(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

structure BaseCTypes =
struct
  datatype base_inttype = Char | Short | Int | Long | LongLong (* | ITY_Word of int *)
end

signature IMPLEMENTATION_NUMBERS =
sig

  type int = IntInf.int
  val UCHAR_MAX : int
  val USHORT_MAX : int
  val UINT_MAX : int
  val ULONG_MAX : int
  val ULLONG_MAX : int

  val SCHAR_MAX : int
  val CHAR_MAX : int
  val SHORT_MAX : int
  val INT_MAX : int
  val LONG_MAX : int
  val LLONG_MAX : int

  val SCHAR_MIN : int
  val CHAR_MIN : int
  val SHORT_MIN : int
  val INT_MIN : int
  val LONG_MIN : int
  val LLONG_MIN : int

  val char_signedp : bool

  val CHAR_BIT : int
  val boolWidth : int
  val charWidth : int
  val shortWidth : int
  val intWidth : int
  val longWidth : int
  val llongWidth : int
  val ptrWidth : int
  val ptr_t : BaseCTypes.base_inttype

  exception BadChar
  val charliteral_conversion : int -> int

end

signature CHAR_LIT_UTIL =
sig
  exception BadChar
  type int = IntInf.int
  val schar_conv : {umax:int,smin:int,smax:int} -> int -> int
  val uchar_conv : {umax:int} -> int -> int
end

structure CharLitUtil : CHAR_LIT_UTIL =
struct
open IntInf
exception BadChar
fun schar_conv {umax,smin,smax} i = let
  val _ = 0 <= i andalso i <= umax orelse
          raise BadChar
in
  if i > smax then smin + i
  else i
end
fun uchar_conv {umax} i = let
  val _ = 0 <= i andalso i <= umax orelse
          raise BadChar
in
  i
end

end
