(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory AutoLevity_Run
imports AutoLevity_Theory_Report AutoLevity_Test
begin

ML \<open>val theories = Thy_Info.get_names () |> map Thy_Info.get_theory\<close>

ML \<open>\<close> 
ML \<open>
fun get_report thy =
let
  val _ = @{print} ("Reporting on " ^ Context.theory_name thy)
  val k = AutoLevity_Base.get_transactions ();

in
if Symtab.defined k (Context.theory_name thy) then
SOME (AutoLevity_Theory_Report.get_reports_for_thy thy |> 
  AutoLevity_Theory_Report.string_reports_of)
else NONE
end
\<close>
ML \<open>Symtab.lookup (AutoLevity_Base.get_transactions ()) "AutoLevity_Test" |> the
  |> Postab_strict.dest\<close>

ML \<open>AutoLevity_Theory_Report.get_reports_for_thy @}\<close>
declare [[ML_print_depth=1000]]
ML \<open>val undepss = !undeps\<close>
ML \<open>undepss |> rev |> filter 
  (fn (x,_) => x = "ArchInvocationLabels_H.ARM_H.arch_invocation_label.case_1")
  |> map snd |> distinct (op =) \<close>

term CapRights_A.random_aux_rights
ML \<open>val k = get_report @{theory AutoLevity_Test} |> the\<close>

(*
(* Custom run of AutoLevity for seL4 *)

(* Requires up-to-date graph report *)
(* Might be worth just running the report in-place instead of reading in seralized one*)
(*TODO: Warn on revision mismatch?*)


ML {*fun generic_facts_of spec_theories excluded_theories (spec_graph : Spec_Graph.graph_entry Int_Graph.T) (proof_graph : Proof_Graph.proof_entry String_Graph.T) = 
let
  fun in_theory i = member (op =) spec_theories (#theory (Int_Graph.get_node spec_graph i))
  fun is_excluded n = member (op =) excluded_theories (Long_Name.explode n |> hd)

(* The most fine-grained filter for "general" lemmas *)
  fun any_contains n = 
  let
    val e =  String_Graph.get_node proof_graph n
  in
      exists (in_theory) (#contains e)
      orelse (#kind e) = Proof_Count.Crunch
      orelse (#kind e) = Proof_Count.Other
  end


  fun remove_contains n g = if any_contains n then
    fold (String_Graph.del_node) (String_Graph.all_preds g [n] handle String_Graph.UNDEF _ => []) g
  else
    g
 
in
  fold remove_contains (String_Graph.keys proof_graph) proof_graph
  |> String_Graph.dest
  |> map fst
  |> filter_out (fn (n,e) => #lines e = (~1,~1) orelse is_excluded n) end
*}

(*Theories whose constants are considered part of the seL4 spec/proof *)
ML {* val spec_theories = Symtab.dest thy_deps 
  |> map_filter (fn (nm,(f,_)) => 
      if String.isSubstring "~~/../l4v/proof/" f orelse
         String.isSubstring "~~/../l4v/spec/" f orelse
         String.isSubstring "~~/../l4v/tools/c-parser/" f then SOME nm else NONE) 
  |> cons "ProofGraph_Serialize_InfoflowC"
  |> cons "TypHeapLib"
  |> cons "TypHeap"
  |> cons "BCorres_UL"
  |> cons "LemmaBucket_C"
  |> cons "WPC"
*}

(*Theories which are not to be considered for levitation *)
ML {* val excluded_theories = Symtab.dest thy_deps 
  |> map_filter (fn (nm,(f,_)) => 
      if String.isSubstring "~~/../l4v/lib" f orelse
         String.isSubstring "~~/../l4v/spec/cspec" f orelse
         String.isSubstring "~~/../l4v/spec/abstract" f orelse
         String.isSubstring "~~/../l4v/isabelle/" f then SOME nm else NONE) 
  |> cons "EmptyFail"
  |> cons "EmptyFail_H"
  |> cons "CLevityCatch"
*}



ML {* val gen_facts = generic_facts_of spec_theories excluded_theories full_spec proof_spec *}


(*TODO: Some taint analysis to avoid overwriting modified proofs?*)
ML {* 

let 
  val _ = Isabelle_System.bash "rm -r $ISABELLE_HOME/../lib/autolevity_buckets"
  val _ = Isabelle_System.mkdir (Path.explode "~~/../l4v/lib/autolevity_buckets")
  
in
  () end
*}


ML {* val sorted = sort_lemmas (proof_spec,full_spec,thy_deps) (spec_theories) gen_facts
   |> parse_attribs*}

(*Debug flag writes out original thm dependencies after the proof *)
ML {* write_thys true sorted (Path.explode "~~/../l4v/lib/autolevity_buckets/") *}

(*CAREFUL: This line refactors the proof to remove bucketed lemmas *)
(*NOTE: Running this twice in a row will fail for obvious reasons.
  Revert the proof before attempting to run it again*)

ML {* val refactor_proof = true 

val _ = if refactor_proof then clear_thys thy_deps sorted else () *}
*)

end

