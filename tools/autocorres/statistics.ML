(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(*
 * Gather statistics of terms at various stages in the pipeline.
 *)

signature STATISTICS =
sig
  type measure_fn = Proof.context -> string -> string -> term -> unit;

  val gather: Proof.context -> string -> string -> term -> unit;
  val setup_measure_fn: measure_fn -> unit;

  val dummy_measure_fn : measure_fn;
  val complexity_measure_fn : measure_fn;
end;

structure Statistics : STATISTICS =
struct

type measure_fn = Proof.context -> string -> string -> term -> unit;

(* The null measurement function. *)
fun dummy_measure_fn ctxt phase term_id term = ()

(* Estimate the "lines of specification" of the given term. *)
fun lines_of_spec ctxt term =
let
  fun num_lines [] = 1
    | num_lines (#"\n" :: xs) = 1 + num_lines xs
    | num_lines (_ :: xs) = num_lines xs
in
  Print_Mode.setmp [] (fn () =>
    Syntax.pretty_term ctxt term
    |> Pretty.string_of_margin 80
    |> String.explode
    |> num_lines) ()
end

(* The term-complexity measurement function. *)
fun complexity_measure_fn ctxt phase term_id term =
let
  fun spec_complexity term =
    case term of
        Const (a, _) => 1
      | (a $ b) => spec_complexity a + spec_complexity b
      | Abs (_, _, a) => spec_complexity a + 1
      | _ => 1
in
  writeln ("SC: " ^ phase ^ ": " ^ term_id ^ " "
      ^ (PolyML.makestring (spec_complexity term))
      ^ " "
      ^ "LoS: " ^ (PolyML.makestring (lines_of_spec ctxt term)))
end

(* Preprocess the input term. *)
fun preprocess ctxt t =
  Raw_Simplifier.rewrite_term (Proof_Context.theory_of ctxt)
        @{thms ac_statistics_rewrites} [] t

(* Set it to be the default. *)
val measure_func_ref = (ref dummy_measure_fn : measure_fn ref)

(* Perform a measurement on the given term. *)
fun gather ctxt phase term_id term =
  (!measure_func_ref) ctxt phase term_id (preprocess ctxt term)

(* Setup a custom measure function. *)
fun setup_measure_fn f = (measure_func_ref := f)

end
