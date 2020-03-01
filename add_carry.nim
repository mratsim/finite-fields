func wordsRequired(bits: int): int {.compileTime.} =
  ## Compute the number of limbs required
  # from the **announced** bit length
  (bits + 64 - 1) div 64

type
  BigInt[bits: static int] = object
    limbs: array[bits.wordsRequired, uint64]

  Carry = cuchar

func addcarry_u64(carryIn: Carry, a, b: uint64, sum: var uint64): Carry {.importc: "_addcarry_u64", header:"<x86intrin.h>", nodecl.}

func `+=`(a: var BigInt, b: BigInt) =
  var carry: Carry
  for i in 0 ..< a.limbs.len:
    carry = addcarry_u64(carry, a.limbs[i], b.limbs[i], a.limbs[i])

func add256(a: var BigInt, b: BigInt) =
  var tmp: uint64

  asm """
    movq %[b], %[tmp]
    addq %[tmp], %[a]

    movq 8+%[b], %[tmp]
    adcq %[tmp], 8+%[a]

    movq 16+%[b], %[tmp]
    adcq %[tmp], 16+%[a]

    movq 24+%[b], %[tmp]
    adcq %[tmp], 24+%[a]
    : [tmp] "+r" (`tmp`), [a] "+m" (`a->limbs[0]`)
    : [b] "m"(`b->limbs[0]`)
    : "cc"
  """

# ######################################################
import random, times, std/monotimes, strformat
import ./timers

proc rand(T: typedesc[BigInt]): T =
  for i in 0 ..< result.limbs.len:
    result.limbs[i] = uint64(rand(high(int)))

proc main() =
  let a = rand(BigInt[256])
  let b = rand(BigInt[256])

  echo "a:        ", a
  echo "b:        ", b
  echo "------------------------------------------------------"

  var a1 = a
  a1 += b
  echo "compiler: ", a1

  var a2 = a
  a2.add256(b)
  echo "assembly: ",a2

main()

echo "\n⚠️ Measurements are approximate and use the CPU nominal clock: Turbo-Boost and overclocking will skew them."
echo "==========================================================================================================\n"

proc report(op, impl: string, start, stop: MonoTime, startClk, stopClk: int64, iters: int) =
  echo &"{op:<15} {impl:<15} {inNanoseconds((stop-start) div iters):>9} ns {(stopClk - startClk) div iters:>9} cycles"


proc bench() =
  const Iters = 1_000_000

  let a = rand(BigInt[256])
  let b = rand(BigInt[256])

  block:
    var a1 = a

    let start = getMonotime()
    let startClk = getTicks()
    for _ in 0 ..< Iters:
      a1 += b
    let stopClk = getTicks()
    let stop = getMonotime()
    report("Addition - 256-bit", "Compiler", start, stop, startClk, stopClk, Iters)

  block:
    var a2 = a

    let start = getMonotime()
    let startClk = getTicks()
    for _ in 0 ..< Iters:
      a2.add256(b)
    let stopClk = getTicks()
    let stop = getMonotime()
    report("Addition - 256-bit", "Assembly", start, stop, startClk, stopClk, Iters)

bench()

# ######################################################
# Codegen (GCC?):
# https://godbolt.org/z/z3pdUz
#
# GNU syntax (result on the right)
#
# pluseq___lAkqysv83DgJrUCC9aFJqPw:
#  mov (%rdi),%rax
#  add (%rsi),%rax
#  setb %dl
#  mov %rax,(%rdi)
#  mov 0x8(%rdi),%rax
#  add $0xff,%dl
#  adc 0x8(%rsi),%rax
#  setb %dl
#  mov %rax,0x8(%rdi)
#  mov 0x10(%rdi),%rax
#  add $0xff,%dl
#  adc 0x10(%rsi),%rax
#  setb %dl
#  mov %rax,0x10(%rdi)
#  mov 0x18(%rsi),%rax
#  add $0xff,%dl
#  adc %rax,0x18(%rdi)
#  retq
#  nopl 0x0(%rax)
#
# Analysis: this is extremely bad
# After the first add, it saves the content of
# the carry flag in %dl register with "setb %dl"
# then store the result, then add the content of %dl to 0xff
# to recreate the carry flag
# then adc
#
# A better ASM would be (a is in rdi and b in rsi)
# pluseq___lAkqysv83DgJrUCC9aFJqPw:
#  mov (%rdi),%rax
#  add %rax, (%rsi)
#  mov 0x8(%rdi),%rax
#  adc %rax, 0x8(%rsi)
#  mov 0x16(%rdi),%rax
#  adc %rax, 0x16(%rsi)
#  mov 0x24(%rsi),%rax
#  adc %rax,0x24(%rdi)
#  retq
#
# Caveat: ADC with a memory destination (instead of register) is much slower
#         on Intel (not AMD) especially before Skylake
# See:
#   - Agner Fog: https://www.agner.org/optimize/instruction_tables.pdf
#   - GMP: https://gmplib.org/~tege/x86-timing.pdf
#   - https://github.com/travisdowns/uarch-bench/wiki/Intel-Performance-Quirks
