func wordsRequired(totalBits, bitsPerWords: int): int {.compileTime.} =
  ## Compute the number of limbs required
  # from the **announced** bit length
  (totalBits + bitsPerWords - 1) div bitsPerWords

const ExcessBits = 13 # 51-bit words

type
  BigIntCarry*[bits: static int] = object
    limbs*: array[wordsRequired(bits, 64), uint64]

  BigIntExcessBits*[bits: static int] = object
    # Note: we implement lazy carry not just lazy reduction
    excess*: uint8
    limbs*: array[wordsRequired(bits, 64 - ExcessBits), uint64]

  Carry* = byte
  Borrow* = byte
