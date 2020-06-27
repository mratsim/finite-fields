import macros, strutils, sets, hashes

# A compile-time inline assembler

const WordBitWidth = 64
type Word = uint64

type
  RM = enum
    ## Register or Memory operand
    Register    = "r"
    Memory      = "m"
    AnyRegOrMem = "rm"

  Constraint = enum
    ## GCC extended assembly modifier
    Input               = ""
    Input_Commutative   = "%"
    Output_Overwrite    = "="
    Output_EarlyClobber = "&"
    InputOutput         = "+"

  Operand = object
    id: string             # [a0] - ASM id
    rm: RM
    constraint: Constraint
    param: string          # a[0] - C code

  OperandArray = object
    name: string           # variable name
    buf*: seq[Operand]

  Assembler_x86 = object
    code: string
    operands: HashSet[Operand]
    areFlagsClobbered: bool

func hash(op: Operand): Hash =
  hash(op.id)

func `[]`(opArray: OperandArray, index: int): Operand =
  opArray.buf[index]

func `[]`(opArray: var OperandArray, index: int): var Operand =
  opArray.buf[index]

func init(T: type OperandArray, name: string, len: int, rm: RM, constraint: Constraint): OperandArray =
  result.name = name
  result.buf.setLen(len)
  for i in 0 ..< len:
    result.buf[i] = Operand(
      id: "[" & name & $i & "]",
      rm: rm,
      constraint: constraint,
      param: name & "[" & $i & "]"
    )

func generate(a: Assembler_x86): NimNode =
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

func add(a: var Assembler_x86, dst, src: var Operand) =
  # Does: dst <- dst + src
  dst.constraint = InputOutput
  a.codeFragment("add", src, dst)
  a.areFlagsClobbered = true

func adc(a: var Assembler_x86, dst, src: var Operand) =
  # Does: dst <- dst + src + carry
  dst.constraint = InputOutput
  a.codeFragment("adc", src, dst)
  a.areFlagsClobbered = true

  if dst.rm != Register:
    {.warning: "Using addcarry with a memory destination, this incurs significant performance penalties.".}

func sub(a: var Assembler_x86, dst, src: var Operand) =
  # Does: dst <- dst - src
  dst.constraint = InputOutput
  a.codeFragment("sub", src, dst)
  a.areFlagsClobbered = true

func sbb(a: var Assembler_x86, dst, src: var Operand) =
  # Does: dst <- dst - src - carry
  dst.constraint = InputOutput
  a.codeFragment("sbb", src, dst)
  a.areFlagsClobbered = true

  if dst.rm != Register:
    {.warning: "Using subborrow with a memory destination, this incurs significant performance penalties.".}

func cmovc(a: var Assembler_x86, dst, src: var Operand) =
  # Does: dst <- src if the carry flag is set
  doAssert dst.rm == Register, "The destination operand must be a register"
  dst.constraint = InputOutput

  a.codeFragment("cmovc", src, dst)
  # No clobber

# #############################################

func wordsRequired(bits: int): int {.compileTime.} =
  ## Compute the number of limbs required
  ## from the announced bit length
  (bits + 64 - 1) div 64

type
  BigInt[bits: static int] {.byref.} = object
    ## BigInt
    ## Enforce-passing by reference otherwise uint128 are passed by stack
    ## which causes issue with the inline assembly
    limbs: array[bits.wordsRequired, Word]

macro mpAdd[N: static int](a: var array[N, Word], b: array[N, Word]): untyped =
  ## Generate a multiprecision addition
  result = newStmtList()

  var ctx: Assembler_x86
  var
    arrT = init(OperandArray, "t", N, Register, InputOutput)
    arrB = init(OperandArray, $(b[0]), N, AnyRegOrMem, Input)

  for i in 0 ..< N:
    if i == 0:
      ctx.add arrT[0], arrB[0]
    else:
      ctx.adc arrT[i], arrB[i]

  let tmp = ident(arrT.name)
  result.add quote do:
    var `tmp` = `a`
  result.add ctx.generate()
  result.add quote do:
    `a` = `tmp`

func `+=`(a: var BigInt, b: BigInt) {.inline.}=
  mpAdd(a.limbs, b.limbs)

# #############################################
import random

randomize(1234)

proc rand(T: typedesc[BigInt]): T =
  for i in 0 ..< result.limbs.len:
    result.limbs[i] = uint64(rand(high(int)))

proc main() =
  block:
    let a = BigInt[128](limbs: [high(uint64), 0])
    let b = BigInt[128](limbs: [1'u64, 0])

    echo "a:        ", a
    echo "b:        ", b
    echo "------------------------------------------------------"

    var a1 = a
    a1 += b
    echo a1
    echo "======================================================"

  block:
    let a = rand(BigInt[256])
    let b = rand(BigInt[256])

    echo "a:        ", a
    echo "b:        ", b
    echo "------------------------------------------------------"

    var a1 = a
    a1 += b
    echo a1
    echo "======================================================"

  block:
    let a = rand(BigInt[384])
    let b = rand(BigInt[384])

    echo "a:        ", a
    echo "b:        ", b
    echo "------------------------------------------------------"

    var a1 = a
    a1 += b
    echo a1

main()
