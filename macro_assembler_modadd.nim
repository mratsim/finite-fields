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
    arrA = init(OperandArray, nimSymbol = a, N, Memory, Output_Overwrite)
    arrB = init(OperandArray, nimSymbol = b, N, Memory, Input)
    arrM = init(OperandArray, nimSymbol = modulus, N, Memory, Input)

    arrT = init(OperandArray, nimSymbol = ident"t", N, Register, InputOutput)
    arrTsub = init(OperandArray, nimSymbol = ident"tsub", N, Register, Output_Overwrite)
    overflowed = Operand(
      desc: OperandDesc(
        asmId: "[overflowed]",
        nimSymbol: ident"overflowed",
        rm: Register,
        constraint: Output_Overwrite,
        cEmit: "overflowed"
      )
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

  let t = arrT.nimSymbol
  let tsub = arrTsub.nimSymbol
  let ov = overflowed.desc.nimSymbol
  result.add quote do:
    var `t` = `a`
    var `tsub` {.noInit.}: typeof(`a`)
    var `ov` {.noInit, exportc.}: uint64
  result.add ctx.generate

func addmod_macro[N: static int](a: var array[N, uint64], b, modulus: array[N, uint64]){.inline.} =
  # Indirection to avoid a codegen bug (Nim setting type of a.limbs as BigInt instead of array)
  genModAdd(
    a,
    b,
    modulus
  )


func addmod_macro*(a: var BigIntCarry, b, modulus: BigIntCarry){.inline.} =
  addmod_macro(
    a.limbs,
    b.limbs,
    modulus.limbs
  )
