(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(*Alternate apply command which displays "used" theorems in refinement step*)

theory Apply_Trace_Cmd
imports Apply_Trace
keywords "apply_trace" :: prf_script
begin

ML{*

structure Filter_Thms = Named_Thms
(
  val name = @{binding no_trace}
  val description = "thms to be ignored from tracing"
)

datatype adjusted_name =
  FoundName of ((string * int option) * thm)
  | UnknownName of (string * term)


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

(* Render the given fact. *)
fun pretty_fact only_names ctxt (FoundName ((name, idx), thm)) =
      Pretty.block
        ([Pretty.mark_str (Facts.markup_extern ctxt (Proof_Context.facts_of ctxt) name),
          case idx of
            SOME n => Pretty.str ("(" ^ string_of_int (n + 1) ^ ")")
          | NONE => Pretty.str ""] @
          (if only_names then []
          else [Pretty.str ":",Pretty.brk 1, Display.pretty_thm ctxt thm]))
  | pretty_fact only_names ctxt (UnknownName (name, prop)) =
      Pretty.block
        [Pretty.str name, Pretty.str "(?) :", Pretty.brk 1,
          Syntax.unparse_term ctxt prop]

fun fact_ref_to_name ((Facts.Named ((nm,_), (SOME [Facts.Single i]))),thm) = FoundName ((nm,SOME i),thm)
    | fact_ref_to_name ((Facts.Named ((nm,_), (NONE))),thm) = FoundName ((nm,NONE),thm)
    | fact_ref_to_name (_,thm) = UnknownName ("",Thm.prop_of thm)

(* Print out the found dependencies. *)
fun print_deps only_names query ctxt thm deps =
let
  (* Remove duplicates. *)
  val deps = sort_distinct (prod_ord (prod_ord string_ord (option_ord int_ord)) Term_Ord.term_ord) deps

  (* Fetch canonical names and theorems. *)
  val deps = map (fn (ident, term) => adjust_thm_name ctxt ident term) deps

  (* Remove "boring" theorems. *)
  val deps = subtract (fn (a, FoundName (_, thm)) => Thm.eq_thm (thm, a)
                          | _ => false) (Filter_Thms.get ctxt) deps

  val deps = case query of SOME (raw_query,pos) => 
    let
      val q = Find_Theorems.read_query (Position.advance_offset 1 pos) raw_query;
      val results = Find_Theorems.find_theorems_cmd ctxt (SOME thm) (SOME 1000000000) false q 
                    |> snd
                    |> map fact_ref_to_name;

      (* Only consider theorems from our query. *)
     
      val deps = inter (fn (FoundName (nmidx,_), FoundName (nmidx',_)) => nmidx = nmidx'
                                    | _ => false) results deps
     in deps end 
     | _ => deps

in
  if only_names then
  Pretty.writeln (
    Pretty.block
      (Pretty.separate "" (map ((pretty_fact only_names) ctxt) deps)))
  else
  (* Pretty-print resulting theorems. *)
  Pretty.writeln (
    Pretty.big_list "used theorems:"
      (map (Pretty.item o single o (pretty_fact only_names) ctxt) deps))

end


val _ =
  Outer_Syntax.command @{command_keyword "apply_trace"} "initial refinement step (unstructured)"
    
  (Args.mode "only_names" -- (Scan.option (Parse.position Parse.cartouche)) --  Method.parse >> 
    (fn ((on,query),text) => Toplevel.proofs (Apply_Trace.apply_results {silent_fail = false} (print_deps on query) text)));

*}

setup {* Filter_Thms.setup *}

lemmas [no_trace] = protectI protectD TrueI Eq_TrueI eq_reflection

(* Test. *)
lemma "(a \<and> b) = (b \<and> a)"
  apply_trace auto
  oops

(* Test. *)
lemma "(a \<and> b) = (b \<and> a)"  
  apply_trace \<open>intro\<close> auto
  oops

(* Local assumptions might mask real facts (or each other). Probably not an issue in practice.*)
lemma
  assumes X: "b = a"
  assumes Y: "b = a"
  shows
  "b = a"
  apply_trace (rule Y)
  oops


end
