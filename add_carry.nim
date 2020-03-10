func wordsRequired(bits: int): int {.compileTime.} =
  ## Compute the number of limbs required
  # from the **announced** bit length
  (bits + 64 - 1) div 64

type
  # Note: a custom bycopy type for limbs is probably
  #       useful for optimization in particular for aliasing.
  BigInt[bits: static int] = object
    limbs: array[bits.wordsRequired, uint64]

  Carry = cuchar

  uint128 {.importc: "unsigned __int128".} = object

  CarryFlag = enum
    cfFalse
    cfTrue

# #######################################################

func addcarry_u64(carryIn: Carry, a, b: uint64, sum: var uint64): Carry {.importc: "_addcarry_u64", header:"<x86intrin.h>", nodecl.}

func addcarry_via128(sum: var uint64, carryOut: var CarryFlag, carryIn: CarryFlag, a, b: uint64) =
  var tmp {.noinit.}: uint128
  {.emit: [tmp, " = (unsigned __int128)", carryIn, " + (unsigned __int128)",a," + (unsigned __int128)",b,";"].}
  {.emit: ["*",sum, " = (NU64)(", tmp, "& (NU64)0xffffffffffffffff);"].}
  {.emit: ["*",carryOut, " = (",CarryFlag,")((", tmp, ">> 64) & 1);"].}

# #######################################################

func add_intrinsics(a: var BigInt, b: BigInt) {.noinline.}=
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

func add_via_u128(a: var BigInt, b: BigInt) {.noinline.}=
  var tmp {.noinit.}: uint128
  {.emit:[tmp, " = (unsigned __int128)0;"].}
  for i in 0 ..< a.limbs.len:
    {.emit:[tmp, " += (unsigned __int128)", a.limbs[i], " + (unsigned __int128)", b.limbs[i], ";"].}
    {.emit:[a.limbs[i], " = (NU64)", tmp, ";"].}
    {.emit:[tmp, " >>= 64;"].}

func add_via_addcarry128(a: var BigInt, b: BigInt) {.noinline.}=
  var carry: CarryFlag
  for i in 0 ..< a.limbs.len:
    addcarry_via128(a.limbs[i], carry, carry, a.limbs[i], b.limbs[i])

func add256_pure(a: var BigInt[256], b: BigInt[256]) {.noinline.}=
  a.limbs[0] += b.limbs[0]
  a.limbs[1] += b.limbs[1] + uint64(a.limbs[0] < b.limbs[0])
  a.limbs[2] += b.limbs[2] + uint64(a.limbs[1] < b.limbs[1])
  a.limbs[3] += b.limbs[3] + uint64(a.limbs[2] < b.limbs[2])

func add256_pure2(a: var BigInt[256], b: BigInt[256]) {.noinline.}=
  a.limbs[0] += b.limbs[0]
  a.limbs[1] += uint64(a.limbs[0] < b.limbs[0])
  a.limbs[1] += b.limbs[1]
  a.limbs[2] += uint64(a.limbs[1] < b.limbs[1])
  a.limbs[2] += b.limbs[2]
  a.limbs[3] += uint64(a.limbs[2] < b.limbs[2])
  a.limbs[3] += b.limbs[3]

func add256_asm(a: var BigInt[256], b: BigInt[256]) {.noinline.}=
  var tmp: uint64

  when defined(gcc):
    asm """
      movq 0+%[b], %[tmp]
      addq %[tmp], 0+%[a]

      movq 8+%[b], %[tmp]
      adcq %[tmp], 8+%[a]

      movq 16+%[b], %[tmp]
      adcq %[tmp], 16+%[a]

      movq 24+%[b], %[tmp]
      adcq %[tmp], 24+%[a]
      : [tmp] "+r" (`tmp`), [a] "=&m" (`a->limbs[0]`)
      : [b] "m"(`b->limbs[0]`)
      : "cc"
    """
  elif defined(clang):
    # https://lists.llvm.org/pipermail/llvm-dev/2017-August/116202.html
    # Remove the 0 from 8+0 when the proc is inline ....
    asm """
      movq 0+0%[b], %[tmp]
      addq %[tmp], 0+0%[a]

      movq 8+0%[b], %[tmp]
      adcq %[tmp], 8+0%[a]

      movq 16+0%[b], %[tmp]
      adcq %[tmp], 16+0%[a]

      movq 24+0%[b], %[tmp]
      adcq %[tmp], 24+0%[a]
      : [tmp] "+r" (`tmp`), [a] "=&m" (`a->limbs[0]`)
      : [b] "m"(`b->limbs[0]`)
      : "cc"
    """
  else:
    {.error: "Unsupported compiler".}

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
  echo "intrinsics: ",a3

  var a4 = a
  a4.add_via_u128(b)
  echo "via u128: ",a4

  var a5 = a
  a5.add256_pure(b)
  echo "unrolled pure Nim: ",a5

  var a6 = a
  a6.add256_pure2(b)
  echo "unrolled pure Nim v2: ",a6

  var a7 = a
  a7.add_via_addcarry128(b)
  echo "addcarry128: ",a7

main()

# warmup
proc warmup*() =
  # Warmup - make sure cpu is on max perf
  let start = cpuTime()
  var foo = 123
  for i in 0 ..< 300_000_000:
    foo += i*i mod 456
    foo = foo mod 789

  # Compiler shouldn't optimize away the results as cpuTime rely on sideeffects
  let stop = cpuTime()
  echo &"Warmup: {stop - start:>4.4f} s, result {foo} (displayed to avoid compiler optimizing warmup away)"

warmup()


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
    var a3 = a

    let start = getMonotime()
    let startClk = getTicks()
    for _ in 0 ..< Iters:
      a3.add_intrinsics(b)
    let stopClk = getTicks()
    let stop = getMonotime()
    report("Addition - 256-bit", "Intrinsics", start, stop, startClk, stopClk, Iters)

  block:
    var a4 = a

    let start = getMonotime()
    let startClk = getTicks()
    for _ in 0 ..< Iters:
      a4.add_via_u128(b)
    let stopClk = getTicks()
    let stop = getMonotime()
    report("Addition - 256-bit", "via uint128", start, stop, startClk, stopClk, Iters)

  block:
    var a5 = a

    let start = getMonotime()
    let startClk = getTicks()
    for _ in 0 ..< Iters:
      a5.add256_pure(b)
    let stopClk = getTicks()
    let stop = getMonotime()
    report("Addition - 256-bit", "unrolled", start, stop, startClk, stopClk, Iters)

  block:
    var a6 = a

    let start = getMonotime()
    let startClk = getTicks()
    for _ in 0 ..< Iters:
      a6.add256_pure2(b)
    let stopClk = getTicks()
    let stop = getMonotime()
    report("Addition - 256-bit", "unrolled v2", start, stop, startClk, stopClk, Iters)

  block:
    var a7 = a

    let start = getMonotime()
    let startClk = getTicks()
    for _ in 0 ..< Iters:
      a7.add_via_addcarry128(b)
    let stopClk = getTicks()
    let stop = getMonotime()
    report("Addition - 256-bit", "add_via_addcarry128", start, stop, startClk, stopClk, Iters)

bench()

# ######################################################
# Codegen (GCC?):
# https://gcc.godbolt.org/z/mFvYA8
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
#
# add_via_u128__lAkqysv83DgJrUCC9aFJqPw_3:
#  mov    (%rsi),%rcx
#  mov    (%rdi),%r8
#  xor    %edx,%edx
#  push   %r12
#  mov    0x8(%rdi),%r9
#  push   %rbx
#  xor    %ebx,%ebx
#  lea    (%rcx,%r8,1),%rax
#  mov    %rax,(%rdi)
#  mov    %rcx,%rax
#  mov    %r8,%rcx
#  add    %rax,%rcx
#  mov    0x8(%rsi),%rax
#  adc    %rdx,%rbx
#  xor    %r10d,%r10d
#  xor    %edx,%edx
#  mov    %rbx,%rcx
#  xor    %ebx,%ebx
#  add    %r9,%rax
#  adc    %r10,%rdx
#  add    %rcx,%rax
#  adc    %rbx,%rdx
#  mov    %rax,0x8(%rdi)
#  mov    0x10(%rsi),%rcx
#  mov    %rdx,%rax
#  xor    %edx,%edx
#  xor    %ebx,%ebx
#  mov    %rax,%r9
#  mov    0x10(%rdi),%rax
#  mov    %rdx,%r10
#  xor    %edx,%edx
#  add    %rcx,%rax
#  adc    %rbx,%rdx
#  add    %r9,%rax
#  mov    0x18(%rdi),%r9
#  mov    %rax,0x10(%rdi)
#  mov    0x18(%rsi),%rcx
#  adc    %r10,%rdx
#  mov    %rdx,%rax
#  pop    %rbx
#  add    %rcx,%r9
#  add    %r9,%rax
#  mov    %rax,0x18(%rdi)
#  pop    %r12
#  retq
#  nopl   0x0(%rax)
#  nopw   %cs:0x0(%rax,%rax,1)
#
# Analysis: no comment ...
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
