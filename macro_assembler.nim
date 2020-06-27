import macros, strutils, sets, hashes

# A compile-time inline assembler

const WordBitWidth* = 64
type Word* = uint64

type
  RM* = enum
    ## Register or Memory operand
    Register    = "r"
    Memory      = "m"
    AnyRegOrMem = "rm"

  Constraint* = enum
    ## GCC extended assembly modifier
    Input               = ""
    Input_Commutative   = "%"
    Input_EarlyClobber  = "&"
    Output_Overwrite    = "="
    Output_EarlyClobber = "=&"
    InputOutput         = "+"

  Operand* = object
    id*: string             # [a0] - ASM id
    rm*: RM
    constraint*: Constraint
    param*: string          # a[0] - C code

  OperandArray* = object
    name*: string           # variable name
    buf: seq[Operand]

  Assembler_x86* = object
    code: string
    operands: HashSet[Operand]
    areFlagsClobbered: bool

func hash(op: Operand): Hash =
  hash(op.id)

func `[]`*(opArray: OperandArray, index: int): Operand =
  opArray.buf[index]

func `[]`*(opArray: var OperandArray, index: int): var Operand =
  opArray.buf[index]

func init*(T: type OperandArray, name: string, len: int, rm: RM, constraint: Constraint): OperandArray =
  result.name = name
  result.buf.setLen(len)
  for i in 0 ..< len:
    result.buf[i] = Operand(
      id: "[" & name & $i & "]",
      rm: rm,
      constraint: constraint,
      param: name & "[" & $i & "]"
    )

func generate*(a: Assembler_x86): NimNode =
  ## Generate the inline assembly code from
  ## the desired instruction

  var
    outOperands: seq[string]
    inOperands: seq[string]
    asmStmt: string

  for op in a.operands.items():
    let decl =
      # [a] "+r" (`a[0]`)
      op.id & " \"" & $op.constraint & $op.rm & "\"" &
      " (`" & op.param & "`)"

    if op.constraint in {Input, Input_Commutative}:
      inOperands.add decl
    else:
      outOperands.add decl

  asmStmt = a.code
  asmStmt.add ": " & outOperands.join(", ") & '\n'
  asmStmt.add ": " & inOperands.join(", ") & '\n'

  if a.areFlagsClobbered:
    asmStmt.add ": \"cc\""
  else:
    asmStmt.add ": "

  result = nnkAsmStmt.newTree(
    newEmptyNode(),
    newLit asmStmt
  )

func codeFragment(a: var Assembler_x86, instr: string, op0, op1: Operand) =
  # Generate a code fragment
  # ⚠️ Warning:
  # The caller should deal with destination/source operand
  # so that it fits GNU Assembly
  if WordBitWidth == 64:
    a.code &= instr & "q %" & op0.id & ", %" & op1.id & '\n'
  else:
    a.code &= instr & "l %" & op0.id & ", %" & op1.id & '\n'

  a.operands.incl op0
  a.operands.incl op1

func codeFragment(a: var Assembler_x86, instr: string, imm: int, op: Operand) =
  # Generate a code fragment
  # ⚠️ Warning:
  # The caller should deal with destination/source operand
  # so that it fits GNU Assembly
  if WordBitWidth == 64:
    a.code &= instr & "q $" & $imm & ", %" & op.id & '\n'
  else:
    a.code &= instr & "l $" & $imm & ", %" & op.id & '\n'
  a.operands.incl op

func add*(a: var Assembler_x86, dst, src: var Operand) =
  # Does: dst <- dst + src
  dst.constraint = InputOutput
  a.codeFragment("add", src, dst)
  a.areFlagsClobbered = true

func adc*(a: var Assembler_x86, dst, src: var Operand) =
  # Does: dst <- dst + src + carry
  dst.constraint = InputOutput
  a.codeFragment("adc", src, dst)
  a.areFlagsClobbered = true

  if dst.rm != Register:
    {.warning: "Using addcarry with a memory destination, this incurs significant performance penalties.".}

func sub*(a: var Assembler_x86, dst, src: var Operand) =
  # Does: dst <- dst - src
  dst.constraint = InputOutput
  a.codeFragment("sub", src, dst)
  a.areFlagsClobbered = true

func sbb*(a: var Assembler_x86, dst, src: var Operand) =
  # Does: dst <- dst - src - borrow
  dst.constraint = InputOutput
  a.codeFragment("sbb", src, dst)
  a.areFlagsClobbered = true

  if dst.rm != Register:
    {.warning: "Using subborrow with a memory destination, this incurs significant performance penalties.".}

func sbb*(a: var Assembler_x86, dst: var Operand, imm: int) =
  # Does: dst <- dst - imm - borrow
  dst.constraint = InputOutput
  a.codeFragment("sbb", imm, dst)
  a.areFlagsClobbered = true

  if dst.rm != Register:
    {.warning: "Using subborrow with a memory destination, this incurs significant performance penalties.".}

func mov*(a: var Assembler_x86, dst, src: var Operand) =
  # Does: dst <- src
  if dst.constraint notin {Output_EarlyClobber, InputOutput}:
    dst.constraint = Output_Overwrite

  a.codeFragment("mov", src, dst)
  # No clobber

func cmovc*(a: var Assembler_x86, dst, src: var Operand) =
  # Does: dst <- src if the carry flag is set
  doAssert dst.rm == Register, "The destination operand must be a register"
  dst.constraint = InputOutput

  a.codeFragment("cmovc", src, dst)
  # No clobber
