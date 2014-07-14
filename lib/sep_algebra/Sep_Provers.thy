(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Sep_Provers
imports Sep_Rotate
begin

(* Constrained lens for sep_erule tactic *)
lemma sep_asm_eq_erule: 
  "(P \<and>* R) s \<Longrightarrow> (\<And>s. T s = (P \<and>* R) s) \<Longrightarrow> (T s \<Longrightarrow> (P' \<and>* R') s)
   \<Longrightarrow> (P' \<and>* R') s" by (clarsimp)

lemma sep_rule:
  "(\<And>s. T s \<Longrightarrow> P s) \<Longrightarrow> (T \<and>* R) s \<Longrightarrow> (P \<and>* R) s" 
    by (erule sep_conj_impl1)

lemma sep_erule: 
  "(T \<and>* R') s  \<Longrightarrow> (\<And>s. T s \<Longrightarrow> P s) \<Longrightarrow> (\<And>s. R' s \<Longrightarrow> R s) \<Longrightarrow>  (P \<and>* R) s"
    by (metis (full_types) sep_conj_impl)

(* Construct analogues to rule/drule etc,  for separation logic *)

ML {* 

 val sep_select     = (resolve_tac  [@{thm sep_eq}])
 val sep_asm_select = (dresolve_tac [@{thm sep_asm_eq}])
 val sep_asm_erule_select = (eresolve_tac [@{thm sep_asm_eq_erule}])


 fun sep_rule_tactic thms  = 
     let val sep_rule = (resolve_tac [@{thm sep_rule}]) in
      sep_apply_tactic sep_rule thms
 end;

 fun sep_drule_tactic thms  =
     let val sep_drule = (dresolve_tac [rotate_prems ~1 @{thm sep_rule}]) in
      sep_apply_tactic sep_drule thms  
 end;

 fun sep_frule_tactic thms  =
     let val sep_frule = (forward_tac [rotate_prems ~1 @{thm sep_rule}]) in
      sep_apply_tactic sep_frule thms  
 end;

 fun sep_erule_tactic thms = 
     let val sep_erule = (eresolve_tac [@{thm sep_erule}]) in
     sep_apply_tactic sep_erule thms
 end;

 fun sep_rule_tac tac ctxt =
     rotator sep_select (tac) ctxt
 fun sep_drule_tac tac ctxt = 
     rotator sep_asm_select tac ctxt
 fun sep_erule_tac tac ctxt = 
     rotator sep_asm_select tac ctxt
 fun sep_erule_concl_tac tac ctxt = 
     rotator sep_select tac ctxt

 fun sep_erule_full_tac tac ctxt =
    let val r = rotator' ctxt
    in 
     tac |> r sep_asm_erule_select |> r sep_select 
   end;
  
  fun sep_erule_full_tac' tac ctxt =
    let val r = rotator' ctxt
    in 
     tac |> r sep_select |> r sep_asm_erule_select
   end;


 fun sep_rule_comb_tac true  thms ctxt  =   (sep_rule_tac  (resolve_tac thms) ctxt) |
     sep_rule_comb_tac false thms ctxt  =   (sep_rule_tac (sep_rule_tactic thms) ctxt)

 fun sep_rule_method bool thms ctxt  = SIMPLE_METHOD'  (sep_rule_comb_tac bool thms ctxt)

 fun sep_drule_comb_tac true  thms ctxt = (sep_drule_tac (dresolve_tac thms) ctxt) |
     sep_drule_comb_tac false thms ctxt = (sep_drule_tac (sep_drule_tactic thms) ctxt) 

 fun sep_drule_method bool thms ctxt = SIMPLE_METHOD' (sep_drule_comb_tac bool thms ctxt) 

 fun sep_frule_method true  thms ctxt = SIMPLE_METHOD' (sep_drule_tac (forward_tac thms) ctxt) |
     sep_frule_method false thms ctxt = SIMPLE_METHOD' (sep_drule_tac (sep_frule_tactic thms) ctxt)

 fun sep_erule_method true  thms ctxt = SIMPLE_METHOD' (sep_erule_tac (eresolve_tac thms) ctxt) |
     sep_erule_method false thms ctxt = SIMPLE_METHOD' (sep_erule_tac (sep_erule_tactic thms) ctxt)

 fun sep_erule_concl_method true  thms ctxt =
                                 SIMPLE_METHOD' (sep_erule_concl_tac (eresolve_tac thms) ctxt) |
     sep_erule_concl_method false thms ctxt =
                                 SIMPLE_METHOD' (sep_erule_concl_tac (sep_erule_tactic thms) ctxt)

fun sep_erule_full_method true thms ctxt =
                                     SIMPLE_METHOD' (sep_erule_full_tac (eresolve_tac thms) ctxt) |
    sep_erule_full_method false thms ctxt =
                                     SIMPLE_METHOD' (sep_erule_full_tac (sep_erule_tactic thms) ctxt)

*}  

method_setup sep_rule = {*
  (Scan.lift (Args.mode "direct")) -- Attrib.thms  >> uncurry sep_rule_method
*}

method_setup sep_drule = {*
  (Scan.lift (Args.mode "direct")) -- Attrib.thms >> uncurry sep_drule_method
*}

method_setup sep_frule = {*
  (Scan.lift (Args.mode "direct")) -- Attrib.thms >> uncurry sep_frule_method
*}

method_setup sep_erule = {*
  (Scan.lift (Args.mode "direct")) -- Attrib.thms >> uncurry sep_erule_method
*}

method_setup sep_erule_concl = {*
  (Scan.lift (Args.mode "direct")) -- Attrib.thms >> uncurry sep_erule_concl_method 
*}

method_setup sep_erule_full = {*
  (Scan.lift (Args.mode "direct")) -- Attrib.thms>> uncurry sep_erule_full_method
*}


end
