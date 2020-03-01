func wordsRequired(bits: int): int {.compileTime.} =
  ## Compute the number of limbs required
  # from the **announced** bit length
  (bits + 64 - 1) div 64

type
  BigInt[bits: static int] = object
    limbs: array[bits.wordsRequired, uint64]

  Carry = cuchar

func addcarry_u64(carryIn: Carry, a, b: uint64, sum: var uint64): Carry {.importc: "_addcarry_u64", header:"<x86intrin.h>", nodecl.}

func add_intrinsics(a: var BigInt, b: BigInt) =
  var carry: Carry
  for i in 0 ..< a.limbs.len:
    carry = addcarry_u64(carry, a.limbs[i], b.limbs[i], a.limbs[i])

func `+=`(a: var BigInt, b: BigInt) {.noinline.}=
  # no-inline needed otherwise the compiler multiplies
  # by the number of iterations in the benchmark
  var carry: bool
  for i in 0 ..< a.limbs.len:
    a.limbs[i] += b.limbs[i] + uint64(carry)
    carry = a.limbs[i] < b.limbs[i]

func add256_asm(a: var BigInt, b: BigInt) =
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
  echo "pure: ", a1

  var a2 = a
  a2.add256_asm(b)
  echo "assembly: ",a2

  var a3 = a
  a3.add_intrinsics(b)
  echo "intrinsics: ",a2

main()

echo "\n⚠️ Measurements are approximate and use the CPU nominal clock: Turbo-Boost and overclocking will skew them."
echo "==========================================================================================================\n"

proc report(op, impl: string, start, stop: MonoTime, startClk, stopClk: int64, iters: int) =
  echo &"{op:<15} {impl:<25} {inNanoseconds((stop-start) div iters):>9} ns {(stopClk - startClk) div iters:>9} cycles"


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
    report("Addition - 256-bit", "Pure Nim", start, stop, startClk, stopClk, Iters)

  block:
    var a2 = a

    let start = getMonotime()
    let startClk = getTicks()
    for _ in 0 ..< Iters:
      a2.add256_asm(b)
    let stopClk = getTicks()
    let stop = getMonotime()
    report("Addition - 256-bit", "Assembly", start, stop, startClk, stopClk, Iters)

  block:
    var a2 = a

    let start = getMonotime()
    let startClk = getTicks()
    for _ in 0 ..< Iters:
      a2.add_intrinsics(b)
    let stopClk = getTicks()
    let stop = getMonotime()
    report("Addition - 256-bit", "Intrinsics", start, stop, startClk, stopClk, Iters)


bench()

# ######################################################
# Codegen (GCC?):
# https://gcc.godbolt.org/z/jaS9kE
#
# GNU syntax (result on the right)
#
# add_intrinsics__lAkqysv83DgJrUCC9aFJqPw_2:
#  mov    (%rdi),%rax
#  add    (%rsi),%rax
#  setb   %dl
#  mov    %rax,(%rdi)
#  mov    0x8(%rdi),%rax
#  add    $0xff,%dl
#  adc    0x8(%rsi),%rax
#  setb   %dl
#  mov    %rax,0x8(%rdi)
#  mov    0x10(%rdi),%rax
#  add    $0xff,%dl
#  adc    0x10(%rsi),%rax
#  setb   %dl
#  mov    %rax,0x10(%rdi)
#  mov    0x18(%rsi),%rax
#  add    $0xff,%dl
#  adc    %rax,0x18(%rdi)
#  retq
#  nopl   0x0(%rax)
#
# Analysis: this is extremely bad
# After the first add, it saves the content of
# the carry flag in %dl register with "setb %dl"
# then store the result, then add the content of %dl to 0xff
# to recreate the carry flag
# then adc
#
# pluseq___n9b4WZZ5kS9bf0NOqjX9cV9bxQ:
#  mov    (%rdi),%rax
#  add    (%rsi),%rax
#  mov    %rax,(%rdi)
#  cmp    (%rsi),%rax
#  mov    0x8(%rsi),%rdx
#  adc    0x8(%rdi),%rdx
#  mov    %rdx,0x8(%rdi)
#  cmp    0x8(%rsi),%rdx
#  mov    0x10(%rsi),%rax
#  adc    0x10(%rdi),%rax
#  mov    %rax,0x10(%rdi)
#  cmp    0x10(%rsi),%rax
#  mov    0x18(%rsi),%rdx
#  adc    %rdx,0x18(%rdi)
#  retq
#  nop
#  nopw   %cs:0x0(%rax,%rax,1)
#
# Analysis: This is better than using the intrinsics but
# we have an extra useless cmp every limbs which means 33% slowdown
# as due to the instruction dependency, the processor cannot use instruction-level parallelism
#
# add256_asm__lAkqysv83DgJrUCC9aFJqPw:
#  xor    %eax,%eax
#  mov    (%rsi),%rax
#  add    %rax,(%rdi)
#  mov    0x8(%rsi),%rax
#  adc    %rax,0x8(%rdi)
#  mov    0x10(%rsi),%rax
#  adc    %rax,0x10(%rdi)
#  mov    0x18(%rsi),%rax
#  adc    %rax,0x18(%rdi)
#  retq
#  nopl   0x0(%rax,%rax,1)
#  nopw   %cs:0x0(%rax,%rax,1)
#
# Analysis: this is the ideal assembly that we would like from an optimizing compiler
#
# Caveat: ADC with a memory destination (instead of register) is much slower
#         on Intel (not AMD) especially before Skylake
# See:
#   - Agner Fog: https://www.agner.org/optimize/instruction_tables.pdf
#   - GMP: https://gmplib.org/~tege/x86-timing.pdf
#   - https://github.com/travisdowns/uarch-bench/wiki/Intel-Performance-Quirks
