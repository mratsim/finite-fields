
import
  macros,
  ./macro_assembler

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
    arrT = init(OperandArray, nimSymbol = ident"t", N, Register, InputOutput)
    arrB = init(OperandArray, nimSymbol = b, N, Memory, Input)
    arrA = init(OperandArray, nimSymbol = a, N, Memory, Output_Overwrite)

  for i in 0 ..< N:
    if i == 0:
      ctx.add arrT[0], arrB[0]
    else:
      ctx.adc arrT[i], arrB[i]
    ctx.mov arrA[i], arrT[i]

  let tmp = ident(arrT.nimSymbol)
  result.add quote do:
    var `tmp` {.exportc, noInit.} = `a`
  result.add ctx.generate()

func `+=`[N: static int](a: var array[N, Word], b: array[N, Word]) {.inline.}=
  # Indirection necessary to avoid bad codegen
  mpAdd(a, b)

func `+=`(a: var BigInt, b: BigInt) {.inline.}=
  a.limbs += b.limbs

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
