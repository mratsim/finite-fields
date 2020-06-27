import macros, strutils

# The v1 has issues with the difference in
# access with offset between GCC and Clang

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

  let L = bits.wordsRequired

  result = newStmtList()

  # It is very important that the update destination
  # is in registers for add with carry
  # On Skylake-X (whichIntel has been stuck with for the past 4 years)
  #
  # ADC reg <- reg, is 1 µops fused, 1 µops unfused, Latency 1
  # ADC reg <- mem, is 1 µops fused, 2 µops unfused, Latency 1
  # ADC mem <- reg, is 4 µops fused, 6 µops unfused, Latency 5

  let tmp = ident("tmp")
  result.add quote do:
    var `tmp` = `a`

  var
    asmStmt: string
    outOperands: seq[string]
    inOperands: seq[string]

  for word in 0 ..< L:
    asmStmt.add '\n'
    let tmpW = "[tmp" & $word & "]"
    let bW = "[b" & $word & "]"

    if word == 0:
      asmStmt.add "      addq %" & bW & ", %" & tmpW & "\n"
    else:
      asmStmt.add "      adcq %" & bW & ", %" & tmpW & "\n"

    outOperands.add tmpW & " \"+r\" (`tmp.limbs[" & $word & "]`)"
    inOperands.add bW & " \"m\" (`b->limbs[" & $word & "]`)"

  asmStmt.add ": " & outOperands.join(", ") & '\n'
  asmStmt.add ": " & inOperands.join(", ") & '\n'
  asmStmt.add ": \"cc\"" # Polluted Carry, Overflow, Zero flags (at least)

  result.add nnkAsmStmt.newTree(
    newEmptyNode(),
    newLit asmStmt
  )

  result.add quote do:
    `a` = `tmp`

  # echo result.toStrLit

func `+=`(a: var BigInt, b: BigInt) {.inline.}=
  addCarryGen_u64(a, b, BigInt.bits)

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
