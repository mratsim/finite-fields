func wordsRequired(totalBits, bitsPerWords: int): int {.compileTime.} =
  ## Compute the number of limbs required
  # from the **announced** bit length
  (totalBits + bitsPerWords - 1) div bitsPerWords

const ExcessBits = 1

type
  BigIntCarry[bits: static int] = object
    limbs: array[wordsRequired(bits, 64), uint64]

  BigIntExcessBits[bits: static int] = object
    limbs: array[wordsRequired(bits, 64 - ExcessBits), uint64]

  Carry = cuchar

# ###############################################################################

func addcarry_u64(carryIn: Carry, a, b: uint64, sum: var uint64): Carry {.importc: "_addcarry_u64", header:"<x86intrin.h>", nodecl.}

func add_intrinsics(a: var BigIntCarry, b: BigIntCarry) {.noinline.}=
  var carry: Carry
  for i in 0 ..< a.limbs.len:
    carry = addcarry_u64(carry, a.limbs[i], b.limbs[i], a.limbs[i])

# ###############################################################################

template isMsbSet*[T](x: T): T =
  ## Returns the most significant bit of an integer
  const msb_pos = T.sizeof * 8 - 1
  x shr msb_pos

template mask(x: uint64): uint64 =
  x and (high(uint64) shr ExcessBits)

func add_excess(a: var BigIntExcessBits, b: BigIntExcessBits) {.noinline.}=
  ## Addition using excess bits instead of hoping for compiler carry flag
  var excess = 0'u64
  for i in 0 ..< a.limbs.len:
    a.limbs[i] += b.limbs[i] + excess
    excess = a.limbs[i].isMsbSet # This is only valid because we have only one 1 excess bit
    a.limbs[i] = a.limbs[i].mask()

# ###############################################################################
import random, times, std/monotimes, strformat
import ./timers

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

proc rand(T: typedesc): T =
  for i in 0 ..< result.limbs.len:
    result.limbs[i] = uint64(rand(high(int)))

proc main(bitSize: static int) =
  const Iters = 1_000_000
  block:
    let a = rand(BigIntCarry[bitSize])
    let b = rand(BigIntCarry[bitSize])

    block:
      var a1 = a
      let start = getMonotime()
      let startClk = getTicks()
      for _ in 0 ..< Iters:
        a1.add_intrinsics b
      let stopClk = getTicks()
      let stop = getMonotime()
      report("Addition-Carry - " & $bitsize & "-bit", "Pure Nim", start, stop, startClk, stopClk, Iters)

  block:
    let a = rand(BigIntExcessBits[bitSize])
    let b = rand(BigIntExcessBits[bitSize])

    block:
      var a1 = a
      let start = getMonotime()
      let startClk = getTicks()
      for _ in 0 ..< Iters:
        a1.add_excess b
      let stopClk = getTicks()
      let stop = getMonotime()
      report("Addition-Excess - " & $bitsize & "-bit", "Pure Nim", start, stop, startClk, stopClk, Iters)

main(254)
main(381)
