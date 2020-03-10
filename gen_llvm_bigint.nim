# Compile with nim c --cc:clang --passC:"-emit-llvm"
# The resulting IR will use i256
# No way to emit i256 add though

type
  Uint256 = object
    t0 {.bitsize:64.}: uint64
    t1 {.bitsize:64.}: uint64
    t2 {.bitsize:64.}: uint64
    t3 {.bitsize:64.}: uint64

proc foo(p: var Uint256) {.noInline.} =
  p.t0 += 1
  p.t1 += 2
  p.t2 += 3
  p.t3 += 4


proc `+=`(a: var Uint256, b: Uint256) {.noinline.} =
  a.t0 += b.t0
  a.t1 += b.t1
  a.t2 += b.t2
  a.t3 += b.t3

import random

proc main() =
  var x: Uint256
  for i in 0 ..< rand(100):
    foo(x)

  for i in 0 ..< 1000:
    x += x

  echo x

main()
