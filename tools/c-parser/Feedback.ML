(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

signature FEEDBACK =
sig

  exception WantToExit of string
  val numErrors : int ref
  val errorThreshold : int option ref
  val errorStr : Region.t * string -> unit
  val errorStr' : SourcePos.t * SourcePos.t * string -> unit
  val warnStr' : SourcePos.t * SourcePos.t * string -> unit
  val informStr : int * string -> unit
  val informStr' : int * SourcePos.t * SourcePos.t * string -> unit

  val errorf : (string -> unit) ref
  val warnf : (string -> unit) ref
  val informf : (string -> unit) ref

  val verbosity_level : int ref

  val timestamp : string -> string

end

structure Feedback :> FEEDBACK =
struct

exception WantToExit of string
val isSome = Option.isSome

val numErrors = ref 0
val errorThreshold = ref (SOME 10)

fun default s =  (TextIO.output(TextIO.stdErr, s);
                  TextIO.flushOut TextIO.stdErr)

val errorf = ref default
val warnf = ref default
val informf = ref default

val verbosity_level = ref 1

fun informStr (v,s) = if v <= !verbosity_level then !informf (s ^ "\n") else ()
fun informStr' (v,l,r,s) =
    informStr (v,Region.toString(Region.make {left = l, right = r}) ^ ": " ^ s)

fun errorStr (r, s) = let
in
  !errorf (Region.toString r ^ ": " ^ s ^ "\n");
  numErrors := !numErrors + 1;
  if isSome (!errorThreshold) andalso !numErrors > valOf (!errorThreshold) then
    raise WantToExit "Too many errors - aborted."
  else ()
end

fun errorStr' (l,r,s) = errorStr(Region.make {left = l, right = r}, s)


fun warnStr' (l,_,s) =
    !warnf ("Warning "^SourcePos.toString l^ " " ^ s ^ "\n")

fun timestamp s = Time.fmt 0 (Time.now()) ^ ": " ^ s

end; (* struct *)


