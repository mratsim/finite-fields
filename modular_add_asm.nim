import modular_add_common

func add(a: var BigIntCarry[254], b: BigIntCarry[254]): Carry {.inline.} =
  # This assumes that `a` doesn't aliases
  var tmp: uint64

  asm """
    movq 0+%[b], %[tmp]
    addq %[tmp], 0+%[a]

    movq 8+%[b], %[tmp]
    adcq %[tmp], 8+%[a]

    movq 16+%[b], %[tmp]
    adcq %[tmp], 16+%[a]

    movq 24+%[b], %[tmp]
    adcq %[tmp], 24+%[a]
    : [tmp] "=r" (`tmp`), [a] "+m" (`a->limbs[0]`), "=@ccc"(`result`)
    : [b] "m"(`b->limbs[0]`)
    : "cc"
  """

func add(a: var BigIntCarry[381], b: BigIntCarry[381]): Carry {.inline.} =
  # This assumes that `a` doesn't aliases
  var tmp: uint64

  asm """
    movq 0+%[b], %[tmp]
    addq %[tmp], 0+%[a]

    movq 8+%[b], %[tmp]
    adcq %[tmp], 8+%[a]

    movq 16+%[b], %[tmp]
    adcq %[tmp], 16+%[a]

    movq 24+%[b], %[tmp]
    adcq %[tmp], 24+%[a]

    movq 32+%[b], %[tmp]
    adcq %[tmp], 32+%[a]

    movq 40+%[b], %[tmp]
    adcq %[tmp], 40+%[a]
    : [tmp] "=r" (`tmp`), [a] "+m" (`a->limbs[0]`), "=@ccc"(`result`)
    : [b] "m"(`b->limbs[0]`)
    : "cc"
  """

func sub(a: var BigIntCarry[254], b: BigIntCarry[254]): Borrow {.inline.} =
  # This assumes that `a` doesn't aliases
  var tmp: uint64

  asm """
    movq 0+%[b], %[tmp]
    subq %[tmp], 0+%[a]

    movq 8+%[b], %[tmp]
    sbbq %[tmp], 8+%[a]

    movq 16+%[b], %[tmp]
    sbbq %[tmp], 16+%[a]

    movq 24+%[b], %[tmp]
    sbbq %[tmp], 24+%[a]
    : [tmp] "=r" (`tmp`), [a] "+m" (`a->limbs[0]`), "=@ccc"(`result`)
    : [b] "m"(`b->limbs[0]`)
    : "cc"
  """

func sub(a: var BigIntCarry[381], b: BigIntCarry[381]): Borrow {.inline.} =
  # This assumes that `a` doesn't aliases
  var tmp: uint64

  asm """
    movq 0+%[b], %[tmp]
    subq %[tmp], 0+%[a]

    movq 8+%[b], %[tmp]
    sbbq %[tmp], 8+%[a]

    movq 16+%[b], %[tmp]
    sbbq %[tmp], 16+%[a]

    movq 24+%[b], %[tmp]
    sbbq %[tmp], 24+%[a]

    movq 32+%[b], %[tmp]
    sbbq %[tmp], 32+%[a]

    movq 40+%[b], %[tmp]
    sbbq %[tmp], 40+%[a]
    : [tmp] "=r" (`tmp`), [a] "+m" (`a->limbs[0]`), "=@ccc"(`result`)
    : [b] "m"(`b->limbs[0]`)
    : "cc"
  """

func ccopy(ctl: Carry or Borrow, a: var BigIntCarry[254], b: BigIntCarry[254]) {.inline.}=
  # This relies on CMOV with register -> memory operand being constant-time for crypto
  #
  # CMOV syntax "register <- r/m"
  # is somewhat restrictive, we need to:
  # - load a in a register
  # - cmov b into the register
  # - store the register into a
  # unless `a` is a array stored in register but this
  # requires inlining and is very awkward to implement as a generic ASM
  # as
  # - it's basically solving register allocation
  # - or for-looping over the ASM call
  # - or specifying each array indexes as an input and/or output to the
  #   inline assembly
  var tmp1, tmp2: uint64
  asm """
    testb %[ctl], %[ctl]

    movq 0+%[a], %[tmp1]
    cmovnzq 0+%[b], %[tmp1]
    movq %[tmp1], 0+%[a]

    movq 8+%[a], %[tmp2]
    cmovnzq 8+%[b], %[tmp2]
    movq %[tmp2], 8+%[a]

    movq 16+%[a], %[tmp1]
    cmovnzq 16+%[b], %[tmp1]
    movq %[tmp1], 16+%[a]

    movq 24+%[a], %[tmp2]
    cmovnzq 24+%[b], %[tmp2]
    movq %[tmp2], 24+%[a]

    : [tmp1] "=r" (`tmp1`), [tmp2] "=r" (`tmp2`), [a] "+m" (`a->limbs[0]`)
    : [ctl] "r" (`ctl`), [b] "m"(`b->limbs[0]`)
    : "cc"
  """

func ccopy(ctl: Carry or Borrow, a: var BigIntCarry[381], b: BigIntCarry[381]) =
  # This relies on CMOV with register -> memory operand being constant-time for crypto
  var tmp1, tmp2: uint64
  asm """
    testb %[ctl], %[ctl]

    movq 0+%[a], %[tmp1]
    cmovnzq 0+%[b], %[tmp1]
    movq %[tmp1], 0+%[a]

    movq 8+%[a], %[tmp2]
    cmovnzq 8+%[b], %[tmp2]
    movq %[tmp2], 8+%[a]

    movq 16+%[a], %[tmp1]
    cmovnzq 16+%[b], %[tmp1]
    movq %[tmp1], 16+%[a]

    movq 24+%[a], %[tmp2]
    cmovnzq 24+%[b], %[tmp2]
    movq %[tmp2], 24+%[a]

    movq 32+%[a], %[tmp1]
    cmovnzq 32+%[b], %[tmp1]
    movq %[tmp1], 32+%[a]

    movq 40+%[a], %[tmp2]
    cmovnzq 40+%[b], %[tmp2]
    movq %[tmp2], 40+%[a]

    : [tmp1] "=r" (`tmp1`), [tmp2] "=r" (`tmp2`), [a] "+m" (`a->limbs[0]`)
    : [ctl] "r" (`ctl`), [b] "m"(`b->limbs[0]`)
    : "cc"
  """

func addmod_asm*(a: var BigIntCarry, b: BigIntCarry, modulus: BigIntCarry) {.noinline.}=
  var tmp = a
  let overflow = tmp.add(b)
  a = tmp
  let gtModulus = tmp.sub(modulus).byte xor Carry(1)

  ccopy(overflow or gtModulus, a, tmp)
