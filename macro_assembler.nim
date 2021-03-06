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
    desc*: OperandDesc
    case fromArray: bool
    of true:
      offset: int
    of false:
      discard

  OperandDesc* = ref object
    asmId*: string          # [a] - ASM id
    nimSymbol*: NimNode     # a   - Nim nimSymbol
    rm*: RM
    constraint*: Constraint
    cEmit*: string          # C emit for example a->limbs

  OperandArray* = object
    nimSymbol*: NimNode
    buf: seq[Operand]

  Assembler_x86* = object
    code: string
    operands: HashSet[OperandDesc]
    areFlagsClobbered: bool

func hash(od: OperandDesc): Hash =
  {.noSideEffect.}:
    hash($od.nimSymbol)

func `[]`*(opArray: OperandArray, index: int): Operand =
  opArray.buf[index]

func `[]`*(opArray: var OperandArray, index: int): var Operand =
  opArray.buf[index]

func init*(T: type OperandArray, nimSymbol: NimNode, len: int, rm: RM, constraint: Constraint): OperandArray =
  result.buf.setLen(len)

  # We need to dereference the hidden pointer of var param
  let isHiddenDeref = nimSymbol.kind == nnkHiddenDeref
  let nimSymbol = if isHiddenDeref: nimSymbol[0]
                  else: nimSymbol
  {.noSideEffect.}:
    let symStr = $nimSymbol

  result.nimSymbol = nimSymbol

  if rm != Register:
    let desc = OperandDesc(
                  asmId: "[" & symStr & "]",
                  nimSymbol: nimSymbol,
                  rm: rm,
                  constraint: constraint,
                  cEmit: "*" & symStr # Deref C arrays
                )
    for i in 0 ..< len:
      result.buf[i] = Operand(
        desc: desc,
        fromArray: true,
        offset: i
      )
  else:
    # We can't store an array in register so we create assign individual register
    # per array elements instead
      for i in 0 ..< len:
        result.buf[i] = Operand(
          desc: OperandDesc(
                    asmId: "[" & symStr & $i & "]",
                    nimSymbol: ident(symStr & $i),
                    rm: rm,
                    constraint: constraint,
                    cEmit: symStr & "[" & $i & "]"
                ),
          fromArray: false
        )

func generate*(a: Assembler_x86): NimNode =
  ## Generate the inline assembly code from
  ## the desired instruction

  var
    outOperands: seq[string]
    inOperands: seq[string]
    asmStmt: string

  for odesc in a.operands.items():
    let decl =
      # [a] "+r" (`a[0]`)
      odesc.asmId & " \"" & $odesc.constraint & $odesc.rm & "\"" &
      " (`" & odesc.cEmit & "`)"

    if odesc.constraint in {Input, Input_Commutative}:
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

func getStrOffset(op: Operand): string =
  if not op.fromArray:
    return "%" & op.desc.asmId

  if op.offset == 0:
    return "%" & op.desc.asmId

  if defined(gcc):
    result = $(op.offset * sizeof(Word)) & "+%" & op.desc.asmId
  elif defined(clang):
    # https://lists.llvm.org/pipermail/llvm-dev/2017-August/116202.html
    result = $(op.offset * sizeof(Word)) & "%" & op.desc.asmId
  else:
    error "Unsupported compiler"

func codeFragment(a: var Assembler_x86, instr: string, op0, op1: Operand) =
  # Generate a code fragment
  # ⚠️ Warning:
  # The caller should deal with destination/source operand
  # so that it fits GNU Assembly
  let off0 = op0.getStrOffset()
  let off1 = op1.getStrOffset()

  if WordBitWidth == 64:
    a.code &= instr & "q " & off0 & ", " & off1 & '\n'
  elif WordBitWidth == 32:
    a.code &= instr & "l " & off0 & ", " & off1 & '\n'
  else:
    error "Unsupported bitwidth: " & $WordBitWidth

  a.operands.incl op0.desc
  a.operands.incl op1.desc

func codeFragment(a: var Assembler_x86, instr: string, imm: int, op: Operand) =
  # Generate a code fragment
  # ⚠️ Warning:
  # The caller should deal with destination/source operand
  # so that it fits GNU Assembly
  if WordBitWidth == 64:
    a.code &= instr & "q $" & $imm & ", %" & op.desc.asmId & '\n'
  else:
    a.code &= instr & "l $" & $imm & ", %" & op.desc.asmId & '\n'

  a.operands.incl op.desc

func add*(a: var Assembler_x86, dst, src: Operand) =
  # Does: dst <- dst + src
  doAssert dst.desc.constraint in {Output_EarlyClobber, InputOutput, Output_Overwrite}
  a.codeFragment("add", src, dst)
  a.areFlagsClobbered = true

func adc*(a: var Assembler_x86, dst, src: Operand) =
  # Does: dst <- dst + src + carry
  doAssert dst.desc.constraint in {Output_EarlyClobber, InputOutput, Output_Overwrite}
  a.codeFragment("adc", src, dst)
  a.areFlagsClobbered = true

  if dst.desc.rm != Register:
    {.warning: "Using addcarry with a memory destination, this incurs significant performance penalties.".}

func sub*(a: var Assembler_x86, dst, src: var Operand) =
  # Does: dst <- dst - src
  doAssert dst.desc.constraint in {Output_EarlyClobber, InputOutput, Output_Overwrite}
  a.codeFragment("sub", src, dst)
  a.areFlagsClobbered = true

func sbb*(a: var Assembler_x86, dst, src: var Operand) =
  # Does: dst <- dst - src - borrow
  doAssert dst.desc.constraint in {Output_EarlyClobber, InputOutput, Output_Overwrite}
  a.codeFragment("sbb", src, dst)
  a.areFlagsClobbered = true

  if dst.desc.rm != Register:
    {.warning: "Using subborrow with a memory destination, this incurs significant performance penalties.".}

func sbb*(a: var Assembler_x86, dst: var Operand, imm: int) =
  # Does: dst <- dst - imm - borrow
  doAssert dst.desc.constraint in {Output_EarlyClobber, InputOutput, Output_Overwrite}
  a.codeFragment("sbb", imm, dst)
  a.areFlagsClobbered = true

  if dst.desc.rm != Register:
    {.warning: "Using subborrow with a memory destination, this incurs significant performance penalties.".}

func mov*(a: var Assembler_x86, dst, src: var Operand) =
  # Does: dst <- src
  doAssert dst.desc.constraint in {Output_EarlyClobber, InputOutput, Output_Overwrite}

  a.codeFragment("mov", src, dst)
  # No clobber

func cmovc*(a: var Assembler_x86, dst, src: var Operand) =
  # Does: dst <- src if the carry flag is set
  doAssert dst.desc.rm == Register, "The destination operand must be a register"
  doAssert dst.desc.constraint in {Output_EarlyClobber, InputOutput, Output_Overwrite}

  a.codeFragment("cmovc", src, dst)
  # No clobber
