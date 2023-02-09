(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

signature THM_EXTRAS =
sig
  datatype adjusted_name =
    FoundName of ((string * int option) * thm)
    | UnknownName of (string * term)
  val adjust_found_thm : adjusted_name -> thm -> adjusted_name
  val fact_ref_to_name : Facts.ref * thm -> adjusted_name
  val adjust_thm_name : Proof.context -> string * int option -> term -> adjusted_name
  val pretty_adjusted_name : Proof.context -> adjusted_name -> Pretty.T
  val pretty_adjusted_fact : Proof.context -> adjusted_name -> Pretty.T
  val pretty_fact : bool -> Proof.context -> adjusted_name -> Pretty.T

  val pretty_thm : bool -> Proof.context -> thm -> Pretty.T
  val pretty_specific_thm : Proof.context -> string -> thm -> Pretty.T
  val pretty_fact_name : Proof.context -> string -> Pretty.T
end

structure ThmExtras: THM_EXTRAS =
struct

datatype adjusted_name =
  FoundName of ((string * int option) * thm)
  | UnknownName of (string * term)

fun adjust_found_thm (FoundName (name, _)) thm = FoundName (name, thm)
  | adjust_found_thm adjusted_name _ = adjusted_name

fun fact_ref_to_name ((Facts.Named ((nm,_), (SOME [Facts.Single i]))),thm) = FoundName ((nm,SOME i),thm)
  | fact_ref_to_name ((Facts.Named ((nm,_), (NONE))),thm) = FoundName ((nm,NONE),thm)
  | fact_ref_to_name (_,thm) = UnknownName ("",Thm.prop_of thm)

(* Parse the index of a theorem name in the form "x_1". *)
fun parse_thm_index name =
  case (String.tokens (fn c => c = #"_") name |> rev) of
      (possible_index::xs) =>
         (case Lexicon.read_nat possible_index of
            SOME n => (space_implode "_" (rev xs), SOME (n - 1))
          | NONE => (name, NONE))
    | _ => (name, NONE)

(*
 * Names stored in proof bodies may have the form "x_1" which can either
 * mean "x(1)" or "x_1". Attempt to determine the correct name for the
 * given theorem. If we can't find the correct theorem, or it is
 * ambiguous, return the original name.
 *)
fun adjust_thm_name ctxt (name,index) term =
let
  val possible_names = case index of NONE => distinct (op =) [(name, NONE), parse_thm_index name]
                                   | SOME i => [(name,SOME i)]

  fun match (n, i) =
  let
    val idx = the_default 0 i
    val thms = Proof_Context.get_fact ctxt (Facts.named n) handle ERROR _ => []
  in
    if idx >= 0 andalso length thms > idx then
      if length thms > 1 then
        SOME ((n, i), nth thms idx)
      else
        SOME ((n,NONE), hd thms)
    else
      NONE
  end
in
  case map_filter match possible_names of
    [x] => FoundName x
    | _ => UnknownName (name, term)
end

fun pretty_adjusted_name ctxt (FoundName ((name, idx), _)) =
    Pretty.block
      [Pretty.mark_str (Facts.markup_extern ctxt (Proof_Context.facts_of ctxt) name),
       case idx of
           SOME n => Pretty.str ("(" ^ string_of_int (n + 1) ^ ")")
         | NONE => Pretty.str ""]
  | pretty_adjusted_name _ (UnknownName (name, _)) =
    Pretty.block [Pretty.str name, Pretty.str "(?)"]

fun pretty_adjusted_fact ctxt (FoundName (_, thm)) =
    Thm.pretty_thm ctxt thm
  | pretty_adjusted_fact ctxt (UnknownName (_, prop)) =
    Syntax.unparse_term ctxt prop

(* Render the given fact, using the given adjusted name. *)
fun pretty_fact only_names ctxt adjusted_name =
      Pretty.block
        (pretty_adjusted_name ctxt adjusted_name ::
          (if only_names then []
          else [Pretty.str ":",Pretty.brk 1, pretty_adjusted_fact ctxt adjusted_name]))

(* Render the given fact. *)
fun pretty_thm only_names ctxt thm =
  let
    val name = Thm.get_name_hint thm
    val adjusted_name = adjust_thm_name ctxt (name, NONE) (Thm.prop_of thm)
  in pretty_fact only_names ctxt adjusted_name
  end

(* Render the given fact, using the given name. The name and fact do not have to match. *)
fun pretty_specific_thm ctxt name thm =
  let val adjusted_name = adjust_thm_name ctxt (name, NONE) (Thm.prop_of thm)
  in pretty_fact false ctxt (adjust_found_thm adjusted_name thm)
  end

(* Render the given name, with markup if it matches a known fact. *)
fun pretty_fact_name ctxt name =
  Pretty.block [Pretty.marks_str (Proof_Context.markup_extern_fact ctxt name)];

end
