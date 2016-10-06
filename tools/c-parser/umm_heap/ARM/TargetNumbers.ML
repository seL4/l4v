(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

structure ImplementationNumbers : IMPLEMENTATION_NUMBERS =
struct

open IntInf

fun exp (n, ex) = if ex = 0 then 1
                  else let
                      val q = ex div 2
                      val r = if ex mod 2 = 1 then n else 1
                      val qex = exp (n, q)
                    in
                      qex * qex * r
                    end

val boolWidth = fromInt 8
val charWidth = 8
val shortWidth = 16
val intWidth = 32
val longWidth = 32
val llongWidth = 64
val ptrWidth : int = 32
val ptr_t = BaseCTypes.Long
val CHAR_BIT : int = 8

fun umax width = exp(2, width) - 1
fun max width = exp(2, width - 1) - 1
fun min width = ~(exp(2, width - 1))

val UCHAR_MAX = umax charWidth
val USHORT_MAX = umax shortWidth
val UINT_MAX = umax intWidth
val ULONG_MAX = umax longWidth
val ULLONG_MAX = umax llongWidth

val SCHAR_MAX = max intWidth
val SHORT_MAX = max shortWidth
val INT_MAX = max intWidth
val LONG_MAX = max longWidth
val LLONG_MAX = max llongWidth

val SCHAR_MIN = min charWidth
val SHORT_MIN = min shortWidth
val INT_MIN = min intWidth
val LONG_MIN = min longWidth
val LLONG_MIN = min llongWidth

val char_signedp = false

val CHAR_MAX = UCHAR_MAX
val CHAR_MIN = IntInf.fromInt 0

open CharLitUtil

val charliteral_conversion = uchar_conv {umax=UCHAR_MAX}

end
