# Constant-time modular arithmetic with carry test
# Compile with Clang, GCC is really bad

func wordsRequired(totalBits, bitsPerWords: int): int {.compileTime.} =
  ## Compute the number of limbs required
  # from the **announced** bit length
  (totalBits + bitsPerWords - 1) div bitsPerWords

const ExcessBits = 13 # 51-bit words

type
  BigIntCarry[bits: static int] = object
    limbs: array[wordsRequired(bits, 64), uint64]

  BigIntExcessBits[bits: static int] = object
    # Note: we implement lazy carry not just lazy reduction
    excess: uint8
    limbs: array[wordsRequired(bits, 64 - ExcessBits), uint64]

  Carry = cuchar
  Borrow = cuchar

# ###############################################################################
# Constant time conditional move

# Note changing the register constraint "r to memory "rm" or any "g"
# leads to slightly higher cycle count

func mux*[T](ctl: T, x, y: T): T {.inline.}=
  ## Multiplexer / selector
  ## Returns x if ctl is true
  ## else returns y
  ## So equivalent to ctl? x: y
  when defined(amd64) or defined(i386):
    when sizeof(T) == 8:
      var muxed = x
      asm """
        testq %[ctl], %[ctl]
        cmovzq %[y], %[muxed]
        : [muxed] "+r" (`muxed`)
        : [ctl] "r" (`ctl`), [y] "r" (`y`)
        : "cc"
      """
      muxed
    elif sizeof(T) == 4:
      var muxed = x
      asm """
        testl %[ctl], %[ctl]
        cmovzl %[y], %[muxed]
        : [muxed] "+r" (`muxed`)
        : [ctl] "r" (`ctl`), [y] "r" (`y`)
        : "cc"
      """
      muxed
    else:
      {.error: "Unsupported word size".}
  else:
    let # Templates duplicate input params code
      x_Mux = x
      y_Mux = y
    y_Mux xor (-T(ctl) and (x_Mux xor y_Mux))

func ccopy*[T](ctl: T, x: var T, y: T) {.inline.}=
  ## Conditional copy
  ## Copy ``y`` into ``x`` if ``ctl`` is true
  when defined(amd64) or defined(i386):
    when sizeof(T) == 8:
      asm """
        testq %[ctl], %[ctl]
        cmovnzq %[y], %[x]
        : [x] "+r" (`*x`)
        : [ctl] "r" (`ctl`), [y] "r" (`y`)
        : "cc"
      """
    elif sizeof(T) == 4:
      asm """
        testl %[ctl], %[ctl]
        cmovnzl %[y], %[x]
        : [x] "+r" (`*x`)
        : [ctl] "r" (`ctl`), [y] "r" (`y`)
        : "cc"
      """
  else:
    x = mux(ctl, y, x)

func copyIfNotNeg[T](x: var T, y: T) {.inline.}=
  ## Return y if the sign flag is set (from a previous substraction)
  ## x left as is if not
  when defined(amd64) or defined(i386):
    when sizeof(T) == 8:
      asm """
        cmovnsq %[y], %[x]
        : [x] "+r" (`*x`)
        : [y] "r" (`y`)
        :
      """
    elif sizeof(T) == 4:
      asm """
        cmovnsl %[y], %[x]
        : [x] "+r" (`*x`)
        : [y] "r" (`y`)
        :
      """
  else:
    {.error: "Unsupported arch".}

# ###############################################################################
# Eager modular addition using full words

func addcarry_u64(carryIn: Carry, a, b: uint64, sum: var uint64): Carry {.importc: "_addcarry_u64", header:"<x86intrin.h>", nodecl.}
func subborrow_u64(borrowIn: Borrow, a, b: uint64, diff: var uint64): Borrow {.importc: "_subborrow_u64", header:"<x86intrin.h>", nodecl.}

func add_intrinsics(a: var BigIntCarry, b: BigIntCarry): Carry =
  for i in 0 ..< a.limbs.len:
    result = addcarry_u64(result, a.limbs[i], b.limbs[i], a.limbs[i])

func sub_intrinsics(a: var BigIntCarry, b: BigIntCarry): Carry =
  for i in 0 ..< a.limbs.len:
    result = subborrow_u64(result, a.limbs[i], b.limbs[i], a.limbs[i])

func GT(a: BigIntCarry, b: BigIntCarry): uint64 =
  # Return true if ``a`` Greater Than ``b``
  # Algo
  # a > b <=> a - b > 0, i.e. a - b does not borrow
  var diff: uint64
  var borrow: Borrow
  for i in 0 ..< a.limbs.len:
    borrow = subborrow_u64(borrow, a.limbs[i], b.limbs[i], diff)

  result = borrow.uint64 xor 1 # boolean not

func conditionalSub(a: var BigIntCarry, b: BigIntCarry, ctl: uint64) =
  var borrow: cuchar
  var diff: uint64
  # Note: the codegen is probably bad due to subborrow relying on the carry flag
  #       and mux/cmov polluting the carry flag by zero-ing it
  #       so it must be saved in register instead and added instead
  #       of an "adc"-chain with just the operands' limbs
  #       and there is no ADOX equivalent for SBB that would only use the OF flag
  for i in 0 ..< a.limbs.len:
    borrow = subborrow_u64(borrow, a.limbs[i], b.limbs[i], diff)
    ctl.ccopy(a.limbs[i], diff)

func addmod(a: var BigIntCarry, b: BigIntCarry, modulus: BigIntCarry) {.noinline.}=
  var overflowed = uint64 a.add_intrinsics(b)
  # It's probably better to fuse a.GT(modulus) and conditionalSub
  overflowed = overflowed or a.GT(modulus)
  a.conditionalSub(modulus, overflowed)

func addmod2(a: var BigIntCarry, b: BigIntCarry, modulus: BigIntCarry) {.noinline.}=
  # ADC to memory is much slower than ADC to registers on old CPU
  # Algorithm
  # a += b
  # tmp = m - a
  var tmp = a
  discard add_intrinsics(tmp, b)
  # TODO we must save the carry flag here, a carry means reduction needed
  a = tmp
  discard sub_intrinsics(tmp, modulus)
  # The previous operation will set the sign flag if
  # a+b - m < 0
  # If the sign flag is not set we have a+b >= m
  # and must reduce, i.e. tmp contains the reduced value
  for i in 0 ..< a.limbs.len:
    a.limbs[i].copyIfNotNeg(tmp.limbs[i])

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

proc report(op: string, bitsize: int, impl: string, start, stop: MonoTime, startClk, stopClk: int64, iters: int) =
  echo &"{op:<30} - {bitsize}-bit {impl:<30} {inNanoseconds((stop-start) div iters):>9} ns {(stopClk - startClk) div iters:>9} cycles"

proc rand(T: typedesc): T =
  for i in 0 ..< result.limbs.len:
    result.limbs[i] = uint64(rand(high(int)))

proc main(bitSize: static int) =
  const Iters = 1_000_000
  block:
    let a = rand(BigIntCarry[bitSize])
    let b = rand(BigIntCarry[bitSize])
    let M = rand(BigIntCarry[bitSize])

    block:
      var a1 = a
      let start = getMonotime()
      let startClk = getTicks()
      for _ in 0 ..< Iters:
        a1.addmod(b, M)
      let stopClk = getTicks()
      let stop = getMonotime()
      report("AddMod-Carry", bitsize, "Pure Nim", start, stop, startClk, stopClk, Iters)

    block:
      var a1 = a
      let start = getMonotime()
      let startClk = getTicks()
      for _ in 0 ..< Iters:
        a1.addmod2(b, M)
      let stopClk = getTicks()
      let stop = getMonotime()
      report("AddMod-Carry v2", bitsize, "Pure Nim", start, stop, startClk, stopClk, Iters)

main(254)
main(381)
