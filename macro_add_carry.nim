import macros

func wordsRequired(bits: int): int {.compileTime.} =
  ## Compute the number of limbs required
  ## from the announced bit length
  (bits + 64 - 1) div 64

type
  BigInt[bits: static int] {.byref.} = object
    ## BigInt
    ## Enforce-passing by reference otherwise uint128 are passed by stack
    ## which causes issue with the inline assembly
    limbs: array[bits.wordsRequired, uint64]

macro addCarryGen_u64(a, b: untyped, bits: static int): untyped =
  var asmStmt = (block:
    "      movq %[b], %[tmp]\n" &
    "      addq %[tmp], %[a]\n"
  )

  let maxByteOffset = bits div 8
  const wsize = sizeof(uint64)

  for byteOffset in countup(wsize, maxByteOffset-1, wsize):
    asmStmt.add (block:
      "\n" &
      # movq 8+%[b], %[tmp]
      "      movq " & $byteOffset & "+%[b], %[tmp]\n" &
      # adcq %[tmp], 8+%[a]
      "      adcq %[tmp], " & $byteOffset & "+%[a]\n"
    )

  let tmp = ident("tmp")
  asmStmt.add (block:
    ": [tmp] \"+r\" (`" & $tmp & "`), [a] \"+m\" (`" & $a & "->limbs[0]`)\n" &
    ": [b] \"m\"(`" & $b & "->limbs[0]`)\n" &
    ": \"cc\""
  )

  result = newStmtList()
  result.add quote do:
    var `tmp`{.noinit.}: uint64

  result.add nnkAsmStmt.newTree(
    newEmptyNode(),
    newLit asmStmt
  )

  echo result.toStrLit

func `+=`(a: var BigInt, b: BigInt) =
  addCarryGen_u64(a, b, BigInt.bits)

# #############################################
import random
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
