import
  macros,
  ./macro_assembler,
  ./modular_add_common

macro genModAdd[N: static int](
        a: var array[N, Word],
        b: array[N, Word],
        modulus: array[N, Word]
      ): untyped =
  ## Generate a multiprecision modular addition
  result = newStmtList()

  var ctx: Assembler_x86
  var
    arrA = init(OperandArray, $(a[0][0]), N, Memory, InputOutput)
    arrB = init(OperandArray, $(b[0]), N, AnyRegOrMem, Input)
    arrM = init(OperandArray, $(modulus[0]), N, AnyRegOrMem, Input)

    arrT = init(OperandArray, "t", N, Register, InputOutput)
    arrTsub = init(OperandArray, "tsub", N, Register, InputOutput)
    overflowed = Operand(
      id: "[overflowed]",
      rm: Register,
      constraint: Output_Overwrite,
      param: "overflowed"
    )

  # Addition
  for i in 0 ..< N:
    if i == 0:
      ctx.add arrT[0], arrB[0]
    else:
      ctx.adc arrT[i], arrB[i]

    # Interleaved copy in a second buffer as well
    ctx.mov arrTsub[i], arrT[i]

  # Test if overflow the buffer, we use sbb instead of setb
  # so that when restoring we can use a single "sbb"
  # instead of "sbb" + "setb"
  ctx.adc overflowed, overflowed

  # Now substract the modulus
  for i in 0 ..< N:
    if i == 0:
      ctx.sub arrTsub[0], arrM[0]
    else:
      ctx.sbb arrTsub[i], arrM[i]

  # If the last sbb underflowed
  # or `overflowed` overflowed
  # set the carry flag
  ctx.sbb overflowed, 0

  # Conditional Mov and
  # and store result
  for i in 0 ..< N:
    ctx.cmovc arrT[i], arrTsub[i]
    ctx.mov arrA[i], arrT[i]

  let t = ident(arrT.name)
  let tsub = ident(arrTsub.name)
  let ov = ident(overflowed.param)
  result.add quote do:
    var `t` = `a`
    var `tsub` {.noInit.}: typeof(`a`)
    var `ov` {.noInit, exportc.}: uint64
  result.add ctx.generate

func addmod_macro*(a: var BigIntCarry, b: BigIntCarry, modulus: BigIntCarry){.inline.} =
  genModAdd(
    a.limbs,
    b.limbs,
    modulus.limbs
  )
