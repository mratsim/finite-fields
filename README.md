# Finite Fields

_This has been implemented in Constantine in PR https://github.com/mratsim/constantine/pull/69_

---------------------------------------------------------

Experimental finite fields primitives (and maybe more)

For now this repo stores experiments to write a fast bigint, crypto and finite fields library (or libraries).
Unfortunately this is an aree where the GCC and Clang are (used to be?) seriously lacking in terms of codegen and intrinsics (but not MSVC and ICC for some reasons).

For example besides using the int128 types as clutches:
- suboptimal support for add with carry and substraction with borrow
- suboptimal support for mul 64x64 -> 128
- suboptimal support for div 128 by 64 (and int128 doesn't really save the day, the codegen is very poor)

In the past, until January 2019, many reports on StackOverflow, GMP own documentation and mersenneforums reported
that the LLVM and GCC codegen was hopeless for carry chains. It may have changed:

- https://gcc.gnu.org/bugzilla/show_bug.cgi?id=67317
- https://bugs.llvm.org/show_bug.cgi?id=24545

## Fallback

Unfortunately big int code is often the bottleneck where it's used and bad code tend to scale, for example multiplication is a n^2 algorithm and exponentiation is worse.

If compiler intrinsics are limiting as a fallback we will need either assembly as a separate .S file or maybe we can use Nim metaprogramming abilities to metaprogram inline assembly statement, for example addition with carry chains.
