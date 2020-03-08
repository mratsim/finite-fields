# Constant-time modular arithmetic with carry test
# Compile with Clang, GCC is really bad

func wordsRequired(totalBits, bitsPerWords: int): int {.compileTime.} =
  ## Compute the number of limbs required
  # from the **announced** bit length
  (totalBits + bitsPerWords - 1) div bitsPerWords

type
  BigIntCarry[bits: static int] = object
    limbs: array[wordsRequired(bits, 64), uint64]

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

# ###############################################################################
# Primitives

func addcarry_u64(carryIn: Carry, a, b: uint64, sum: var uint64): Carry {.importc: "_addcarry_u64", header:"<x86intrin.h>", nodecl.}
func subborrow_u64(borrowIn: Borrow, a, b: uint64, diff: var uint64): Borrow {.importc: "_subborrow_u64", header:"<x86intrin.h>", nodecl.}

type
  uint128*{.importc: "unsigned __int128".} = object

func muladd1*(hi, lo: var uint64, a, b, c: uint64) {.inline.}=
  ## Extended precision multiplication + addition
  ## This is constant-time on most hardware except some specific one like Cortex M0
  ## (hi, lo) <- a*b + c
  # Note: 0xFFFFFFFF_FFFFFFFF² -> (hi: 0xFFFFFFFFFFFFFFFE, lo: 0x0000000000000001)
  #       so adding any c cannot overflow uint128
  block:
    # Note: since a and b use 63-bit,
    # the result is 126-bit and carrying cannot overflow
    var dblPrec {.noInit.}: uint128
    {.emit:[dblPrec, " = (unsigned __int128)", a," * (unsigned __int128)", b, " + (unsigned __int128)",c,";"].}

    # Don't forget to dereference the var param in C mode
    when defined(cpp):
      {.emit:[hi, " = (NU64)(", dblPrec," >> ", 64'u64, ");"].}
      {.emit:[lo, " = (NU64)", dblPrec,";"].}
    else:
      {.emit:["*",hi, " = (NU64)(", dblPrec," >> ", 64'u64, ");"].}
      {.emit:["*",lo, " = (NU64)", dblPrec,";"].}

func muladd2*(hi, lo: var uint64, a, b, c1, c2: uint64) {.inline.}=
  ## Extended precision multiplication + addition + addition
  ## This is constant-time on most hardware except some specific one like Cortex M0
  ## (hi, lo) <- a*b + c
  # Note: 0xFFFFFFFF_FFFFFFFF² -> (hi: 0xFFFFFFFFFFFFFFFE, lo: 0x0000000000000001)
  #       so adding 0xFFFFFFFFFFFFFFFF leads to (hi: 0xFFFFFFFFFFFFFFFF, lo: 0x0000000000000000)
  #       and we have enough space to add again 0xFFFFFFFFFFFFFFFF without overflowing
  block:
    # Note: since a and b use 63-bit,
    # the result is 126-bit and carrying cannot overflow
    var dblPrec {.noInit.}: uint128
    {.emit:[
      dblPrec, " = (unsigned __int128)", a," * (unsigned __int128)", b,
               " + (unsigned __int128)",c1," + (unsigned __int128)",c2,";"
    ].}

    # Don't forget to dereference the var param in C mode
    when defined(cpp):
      {.emit:[hi, " = (NU64)(", dblPrec," >> ", 64'u64, ");"].}
      {.emit:[lo, " = (NU64)", dblPrec,";"].}
    else:
      {.emit:["*",hi, " = (NU64)(", dblPrec," >> ", 64'u64, ");"].}
      {.emit:["*",lo, " = (NU64)", dblPrec,";"].}

# # ###############################################################################
# # Eager modular addition using full words

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

# ###############################################################################
# Montgomery
import std/bitops

func negInvModWord(M: BigIntCarry): uint64 =
  ## Returns the Montgomery domain magic constant for the input modulus:
  ##
  ##   µ ≡ -1/M[0] (mod Word)
  ##
  ## M[0] is the least significant limb of M
  ## M must be odd and greater than 2.
  ##
  ## Assuming 64-bit words:
  ##
  ## µ ≡ -1/M[0] (mod 2^64)
  # Algorithm:
  # - Cetin Kaya Koc (2017), https://eprint.iacr.org/2017/411
  # - Jean-Guillaume Dumas (2012), https://arxiv.org/pdf/1209.6626v2.pdf
  # - Colin Plumb (1994), http://groups.google.com/groups?selm=1994Apr6.093116.27805%40mnemosyne.cs.du.edu
  # Other sources:
  # - https://crypto.stackexchange.com/questions/47493/how-to-determine-the-multiplicative-inverse-modulo-64-or-other-power-of-two
  # - https://mumble.net/~campbell/2015/01/21/inverse-mod-power-of-two
  # - http://marc-b-reynolds.github.io/math/2017/09/18/ModInverse.html
  let
    M0 = M.limbs[0]
    k = fastLog2(64)

  result = M0                 # Start from an inverse of M0 modulo 2, M0 is odd and it's own inverse
  for _ in 0 ..< k:           # at each iteration we get the inverse mod(2^2k)
    result *= 2 + M0 * result # x' = x(2 + ax) (`+` to avoid negating at the end)

func montyMul_CIOS_nocarry(r: var BigIntCarry, a, b, modulus: BigIntCarry, m0inv: uint64) =
  # https://hackmd.io/@zkteam/modular_multiplication
  var t: BigIntCarry

  for i in 0 ..< t.limbs.len:
    var A: uint64
    muladd1(A, t.limbs[0], a.limbs[0], b.limbs[i], t.limbs[0])
    let m = t.limbs[0] * m0inv
    var carry, lo: uint64
    muladd1(carry, lo, m, modulus.limbs[0], t.limbs[0])
    for j in 1 ..< t.limbs.len:
      muladd2(A, t.limbs[j], a.limbs[j], b.limbs[i], A, t.limbs[j])
      muladd2(carry, t.limbs[j-1], m, modulus.limbs[j], carry, t.limbs[j])

    t.limbs[^1] = carry + A

  # Conditional substraction
  r = t

func montyMul_SOS(r: var BigIntCarry, a, b, modulus: BigIntCarry, m0inv: uint64) =
  var t: array[modulus.limbs.len * 2, uint64]

  for i in 0 ..< modulus.limbs.len:
    var carry: uint64
    for j in 0 ..< modulus.limbs.len:
      muladd2(carry, t[i+j], a.limbs[j], b.limbs[i], t[i+j], carry)
    t[i+modulus.limbs.len] = carry

  for i in 0 ..< modulus.limbs.len:
    var carry: uint64
    let m = t[i] * m0inv
    for j in 0 ..< modulus.limbs.len:
      muladd2(carry, t[i+j], m, modulus.limbs[j], t[i+j], carry)

    var carry2 = addcarry_u64(Carry(0), t[i+modulus.limbs.len], carry, t[i+modulus.limbs.len])
    for k in i+modulus.limbs.len+1 ..< t.len:
      carry2 = addcarry_u64(carry2, t[k], 0, t[k])

  for j in 0 ..< modulus.limbs.len:
    r.limbs[j] = t[j+modulus.limbs.len]

  # Conditional substraction

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

    let m0inv = M.negInvModWord
    let one = block:
      var one: BigIntCarry[bitSize]
      one.limbs[0] = 1
      one

    block:
      var aMonty, bMonty: BigIntCarry[bitSize]
      aMonty.montyMul_CIOS_nocarry(a, one, M, m0inv)
      bMonty.montyMul_CIOS_nocarry(b, one, M, m0inv)

      var r: BigIntCarry[bitSize]
      let start = getMonotime()
      let startClk = getTicks()
      for _ in 0 ..< Iters:
        r.montyMul_CIOS_nocarry(aMonty, bMonty, M, m0inv)
      let stopClk = getTicks()
      let stop = getMonotime()
      report("Montgomery Multiplication - CIOS no carry", bitsize, "Pure Nim", start, stop, startClk, stopClk, Iters)

    block:
      var aMonty, bMonty: BigIntCarry[bitSize]
      aMonty.montyMul_SOS(a, one, M, m0inv)
      bMonty.montyMul_SOS(b, one, M, m0inv)

      var r: BigIntCarry[bitSize]
      let start = getMonotime()
      let startClk = getTicks()
      for _ in 0 ..< Iters:
        r.montyMul_SOS(aMonty, bMonty, M, m0inv)
      let stopClk = getTicks()
      let stop = getMonotime()
      report("Montgomery Multiplication - SOS", bitsize, "Pure Nim", start, stop, startClk, stopClk, Iters)


main(254)
main(381)
