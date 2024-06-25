(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Experimental AutoCorres proofs over CRefine: work in progress *)

theory AutoCorresTest
imports Refine_C
begin

section \<open>Simple test case: handleYield\<close>

autocorres
  [
   skip_heap_abs, skip_word_abs, (* for compatibility *)
   scope = handleYield doReplyTransfer,
   scope_depth = 0,
   c_locale = kernel_all_substitute,
   no_c_termination
  ] "../c/build/$L4V_ARCH/kernel_all.c_pp"

context kernel_m begin

text \<open>Export corres_underlying rules for handleYield's callees.\<close>

lemma corres_pre_getCurThread_wrapper:
  assumes cc: "\<And>rv. corres_underlying {(x, y). cstate_relation x y} True True R (P rv) (P' rv)
                        (f rv) (f' (tcb_ptr_to_ctcb_ptr rv))"
  shows   "corres_underlying {(x, y). cstate_relation x y} True True R
                  (\<lambda>s. \<forall>rv. ksCurThread s = rv \<longrightarrow> P rv s)
                  (\<lambda>s. \<forall>rv. ksCurThread_' s = tcb_ptr_to_ctcb_ptr rv \<longrightarrow> P' rv s)
                  (getCurThread >>= f) (gets ksCurThread_' >>= f')"
  (* ugly but works -- corres_symb_exec_l doesn't *)
  using cc
  apply (clarsimp simp: corres_underlying_def getCurThread_def)
  apply monad_eq
  apply (clarsimp simp: cstate_relation_def Let_def)
  done

text \<open>
  Proving handleYield_ccorres via handleYield'.
  The handleYield spec has one less getCurThread, so we need to use the fact
  that tcbSchedDequeue does not modify ksCurThread.
\<close>
local_setup \<open>AutoCorresModifiesProofs.new_modifies_rules "../c/build/$L4V_ARCH/kernel_all.c_pp"\<close>
thm tcbSchedDequeue'_modifies

text \<open>Existing ccorres proof, for reference\<close>
lemma (* handleYield_ccorres: *)
  "ccorres dc xfdc
       (invs' and ct_active')
       UNIV
       []
       (handleYield)
       (Call handleYield_'proc)"
  apply cinit
   apply (rule ccorres_pre_getCurThread)
   apply (ctac add: tcbSchedDequeue_ccorres)
     apply (ctac add: tcbSchedAppend_ccorres)
       apply (ctac add: rescheduleRequired_ccorres)
      apply (wp weak_sch_act_wf_lift_linear tcbSchedAppend_valid_objs')
     apply (vcg exspec= tcbSchedAppend_modifies)
    apply (wp weak_sch_act_wf_lift_linear tcbSchedDequeue_valid_queues)
   apply (vcg exspec= tcbSchedDequeue_modifies)
  apply (clarsimp simp: tcb_at_invs' invs_valid_objs'
                        valid_objs'_maxPriority valid_objs'_maxDomain)
  apply (auto simp: obj_at'_def st_tcb_at'_def ct_in_state'_def)
  done

lemma reorder_gets:
  "(\<And>x. \<lbrace> \<lambda>s. x = f s \<rbrace> g \<lbrace> \<lambda>_ s. x = f s \<rbrace>) \<Longrightarrow>
   (do x \<leftarrow> gets f;
       g;
       h x od) =
   (do g;
       x \<leftarrow> gets f;
       h x od)"
  by (fastforce simp: bind_def' Nondet_VCG.valid_def gets_def get_def return_def)

thm
  (* no arguments, no precondition, dc return *)
  rescheduleRequired_ccorres rescheduleRequired_ccorres[ac]
  (* one argument, simple precondition, dc return *)
  tcbSchedDequeue_ccorres tcbSchedDequeue_ccorres[ac]
  (* multiple arguments, complex precondition, non-dc return *)
  handleFaultReply_ccorres handleFaultReply_ccorres[ac]

text \<open>Now the proof.\<close>
lemma (* handleYield_ccorres: *)
  "ccorres dc xfdc
       (invs' and ct_active')
       UNIV
       []
       (handleYield)
       (Call handleYield_'proc)"
  apply (ac_init)
   apply (simp add: handleYield_def handleYield'_def)
   (* Show that current thread is unmodified.
    * FIXME: proper way to do this? *)
   apply (subst reorder_gets[symmetric, unfolded K_bind_def])
    using tcbSchedDequeue'_modifies apply (fastforce simp: Nondet_VCG.valid_def)
   apply (subst double_gets_drop_regets)
   apply (rule corres_pre_getCurThread_wrapper)
   apply (rule corres_split[OF tcbSchedDequeue_ccorres[ac]])
      apply (rule corres_split[OF tcbSchedAppend_ccorres[ac]])
         apply (rule rescheduleRequired_ccorres[ac])
          apply (solves \<open>wp tcbSchedAppend_valid_objs' weak_sch_act_wf_lift
                            tcbSchedDequeue_valid_queues
                          | simp\<close>)+
    apply (clarsimp simp: invs_valid_objs' tcb_at_invs'
                          valid_objs'_maxPriority valid_objs'_maxDomain)
    by (auto simp: obj_at'_def st_tcb_at'_def ct_in_state'_def)

end


section \<open>Function call testcase: handleFault and handleDoubleFault\<close>

autocorres
  [
   skip_heap_abs, skip_word_abs, (* for compatibility *)
   scope = handleDoubleFault,
   scope_depth = 0,
   c_locale = kernel_all_substitute,
   no_c_termination
  ] "../c/build/$L4V_ARCH/kernel_all.c_pp"

context kernel_m begin
local_setup \<open>AutoCorresModifiesProofs.new_modifies_rules "../c/build/$L4V_ARCH/kernel_all.c_pp"\<close>

text \<open>Extra corres_underlying rules.\<close>

lemma corres_add_noop_rhs2:
  "corres_underlying sr nf nf' r P P' f (do _ \<leftarrow> g; return () od)
      \<Longrightarrow> corres_underlying sr nf nf' r P P' f g"
  by simp

(* Use termination (nf=True) to avoid exs_valid *)
lemma corres_noop2_no_exs:
  assumes x: "\<And>s. P s  \<Longrightarrow> \<lbrace>(=) s\<rbrace> f \<lbrace>\<lambda>r. (=) s\<rbrace> \<and> empty_fail f"
  assumes y: "\<And>s. P' s \<Longrightarrow> \<lbrace>(=) s\<rbrace> g \<lbrace>\<lambda>r. (=) s\<rbrace>"
  assumes z: "nf' \<Longrightarrow> no_fail P f" "no_fail P' g"
  shows      "corres_underlying sr True nf' dc P P' f g"
  apply (clarsimp simp: corres_underlying_def)
  apply (rule conjI)
   apply (drule x, drule y)
   apply (clarsimp simp: Nondet_VCG.valid_def empty_fail_def Ball_def Bex_def)
   apply fast
  apply (insert z)
  apply (clarsimp simp: no_fail_def)
  done

lemma corres_symb_exec_l_no_exs:
  assumes z: "\<And>rv. corres_underlying sr True nf' r (Q rv) P' (x rv) y"
  assumes x: "\<And>s. P s \<Longrightarrow> \<lbrace>(=) s\<rbrace> m \<lbrace>\<lambda>r. (=) s\<rbrace> \<and> empty_fail m"
  assumes y: "\<lbrace>P\<rbrace> m \<lbrace>Q\<rbrace>"
  assumes nf: "nf' \<Longrightarrow> no_fail P m"
  shows      "corres_underlying sr True nf' r P P' (m >>= (\<lambda>rv. x rv)) y"
  apply (rule corres_guard_imp)
    apply (subst gets_bind_ign[symmetric], rule corres_split)
       apply (rule corres_noop2_no_exs)
          apply (erule x)
         apply (rule gets_wp)
        apply (erule nf)
       apply (rule no_fail_gets)
      apply (rule z)
     apply (rule y)
    apply (rule gets_wp)
   apply simp+
  done

text \<open>Existing ccorres proof, for reference\<close>
lemma (* handleDoubleFault_ccorres: *)
  "ccorres dc xfdc (invs' and  tcb_at' tptr and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s) and
        sch_act_not tptr and (\<lambda>s. \<forall>p. tptr \<notin> set (ksReadyQueues s p)))
      (UNIV \<inter> {s. tptr_' s = tcb_ptr_to_ctcb_ptr tptr})
      [] (handleDoubleFault tptr ex1 ex2)
         (Call handleDoubleFault_'proc)"
  apply (cinit lift: tptr_')
   apply (subst ccorres_seq_skip'[symmetric])
   apply (ctac (no_vcg))
    apply (rule ccorres_symb_exec_l)
       apply (rule ccorres_return_Skip)
      apply (wp asUser_inv getRestartPC_inv)+
    apply (rule empty_fail_asUser)
    apply (simp add: getRestartPC_def)
   apply wp
  apply clarsimp
  apply (simp add: ThreadState_Inactive_def)
  apply (fastforce simp: valid_tcb_state'_def)
  done


text \<open>New proof of handleDoubleFault\<close>
lemma (* handleDoubleFault_ccorres: *)
  "ccorres dc xfdc (invs' and tcb_at' tptr and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s) and
        sch_act_not tptr and (\<lambda>s. \<forall>p. tptr \<notin> set (ksReadyQueues s p)))
      (UNIV \<inter> {s. ex1_' s = ex1' \<and> tptr_' s = tcb_ptr_to_ctcb_ptr tptr})
      [] (handleDoubleFault tptr ex1 ex2)
         (Call handleDoubleFault_'proc)"
  apply ac_init
    prefer 3 apply simp
   apply (unfold handleDoubleFault_def handleDoubleFault'_def K_bind_def)
   apply (rule corres_add_noop_rhs2) \<comment> \<open>split out extra haskell code\<close>
   apply (rule corres_split[OF setThreadState_ccorres[ac]])
       apply (rule corres_symb_exec_l_no_exs)
          apply simp
         apply (rule conjI)
          apply (wp asUser_inv getRestartPC_inv)
         apply (wp empty_fail_asUser)
        apply (rule hoare_TrueI)
       apply (wpsimp simp: getRestartPC_def)
      apply simp
     apply (simp add: ThreadState_Inactive_def)
    apply wp
   apply (rule hoare_TrueI)
  by (fastforce simp: valid_tcb_state'_def)

end

autocorres
  [
   skip_heap_abs, skip_word_abs, (* for compatibility *)
   scope = handleFault,
   scope_depth = 0,
   c_locale = kernel_all_substitute,
   no_c_termination
  ] "../c/build/$L4V_ARCH/kernel_all.c_pp"

(* Prove and store modifies rules. *)
context kernel_m begin
local_setup \<open>AutoCorresModifiesProofs.new_modifies_rules "../c/build/$L4V_ARCH/kernel_all.c_pp"\<close>

(* TODO: proof for handleFault' *)
thm handleFault'_def
thm handleFault_ccorres

end




section \<open>Experiment: translating clzl\<close>
text \<open>
  __builtin_clzl is defined using guarded_spec_body,
  which is a bit hard to translate generically.
  This is an experiment to translate clzl manually.
\<close>
context kernel_all_substitute begin

thm kernel_m.clzl_spec clzl_body_def

definition l1_clzl' :: "nat \<Rightarrow> (globals myvars, unit + unit) nondet_monad" where
  "l1_clzl' rec_measure' \<equiv>
     L1_spec ({(s', t). (\<forall>s. s' \<in> \<lbrace>s. \<^bsup>s\<^esup>x \<noteq> 0\<rbrace> \<longrightarrow> t \<in> \<lbrace>\<acute>ret__long = of_nat (word_clz \<^bsup>s\<^esup>x)\<rbrace>) \<and>
                          (\<exists>s. s' \<in> \<lbrace>s. \<^bsup>s\<^esup>x \<noteq> 0\<rbrace>)} \<inter> {(s, t). t may_not_modify_globals s})"

lemma l1_clzl'_corres:
  "L1corres ct \<Gamma> (l1_clzl' rec_measure') (Call clzl_'proc)"
  apply (unfold l1_clzl'_def)
  apply (rule L1corres_Call)
   apply (rule clzl_impl)
  apply (unfold clzl_body_def)
  apply (rule L1corres_guarded_spec)
  done

definition l2_clzl' :: "nat \<Rightarrow> 32 word \<Rightarrow> (globals, unit + 32 signed word) nondet_monad" where
  "l2_clzl' rec_measure' x \<equiv>
     L2_seq (L2_guard (\<lambda>_. x \<noteq> 0))
       (\<lambda>_. L2_gets (\<lambda>_. of_nat (word_clz x)) [''ret''])"

lemma l2_clzl'_corres:
  "L2corres globals ret__long_' (\<lambda>_. ()) (\<lambda>s. x_' s = x) (l2_clzl' rec_measure' x) (l1_clzl' rec_measure')"
  apply (unfold l2_clzl'_def l1_clzl'_def)
  (* TODO: how to automate this? *)
  apply (monad_eq simp: L1_defs L2_defs L2corres_def corresXF_def meq_def)
  apply (subst myvars.splits)
  apply simp
  done

definition clzl' :: "32 word \<Rightarrow> (globals, 32 signed word) nondet_monad" where
  "clzl' x \<equiv> do guard (\<lambda>_. x \<noteq> 0);
                return (of_nat (word_clz x)) od"

lemma clzl'_TScorres:
  "L2_call (l2_clzl' rec_measure' x) = liftE (clzl' x)"
  apply (unfold l2_clzl'_def clzl'_def)
  apply (tactic \<open>simp_tac (@{context} addsimps
      (#lift_rules (the (Monad_Types.get_monad_type "nondet" (Context.Proof @{context})))
       |> Thmtab.dest |> map fst)) 1\<close>)
  done

lemma clzl'_ac_corres: "ac_corres globals ct \<Gamma> ret__long_' (\<lambda>s. x_' s = x) (liftE (clzl' x)) (Call clzl_'proc)"
  apply (rule ac_corres_chain[OF _ _ L2Tcorres_id corresTA_trivial, simplified o_def, simplified])
    apply (rule l1_clzl'_corres)
   apply (rule l2_clzl'_corres)
  apply (rule clzl'_TScorres)
  done
end

text \<open>Add our manual translation of clzl into the AutoCorres function info.\<close>
ML \<open>
fun phasetab_merge_with merge (tab1, tab2) =
  sort_distinct FunctionInfo.phase_ord
      (FunctionInfo.Phasetab.keys tab1 @ FunctionInfo.Phasetab.keys tab2)
  |> map (fn k => (k, case (FunctionInfo.Phasetab.lookup tab1 k, FunctionInfo.Phasetab.lookup tab2 k) of
                          (SOME x1, SOME x2) => merge (x1, x2)
                        | (SOME x1, NONE) => x1
                        | (NONE, SOME x2) => x2
                        (* (NONE, NONE) impossible *)))
  |> FunctionInfo.Phasetab.make;
\<close>
setup \<open>
fn thy =>
let val clzl_cp = {
      name = "clzl",
      invented_body = false,
      is_simpl_wrapper = false,
      callees = Symset.empty,
      rec_callees = Symset.empty,
      phase = FunctionInfo.CP,
      args = [("x", @{typ "32 word"})],
      return_type = @{typ "32 signed word"},
      const = @{term "clzl_'proc"},
      raw_const = @{term "clzl_'proc"},
      definition = @{thm kernel_all_substitute.clzl_body_def},
      mono_thm = NONE,
      corres_thm = @{thm TrueI}
    }: FunctionInfo.function_info;
    val clzl_l1 = clzl_cp
      |> FunctionInfo.function_info_upd_phase FunctionInfo.L1
      |> FunctionInfo.function_info_upd_const @{term "kernel_all_substitute.l1_clzl'"}
      |> FunctionInfo.function_info_upd_definition @{thm kernel_all_substitute.l1_clzl'_def}
      |> FunctionInfo.function_info_upd_corres_thm @{thm "kernel_all_substitute.l1_clzl'_corres"};
    val clzl_l2 = clzl_l1
      |> FunctionInfo.function_info_upd_phase FunctionInfo.L2
      |> FunctionInfo.function_info_upd_const @{term "kernel_all_substitute.l2_clzl'"}
      |> FunctionInfo.function_info_upd_definition @{thm kernel_all_substitute.l2_clzl'_def}
      |> FunctionInfo.function_info_upd_corres_thm @{thm "kernel_all_substitute.l2_clzl'_corres"};
    val clzl_ts = clzl_l2
      |> FunctionInfo.function_info_upd_phase FunctionInfo.TS
      |> FunctionInfo.function_info_upd_const @{term "kernel_all_substitute.clzl'"}
      |> FunctionInfo.function_info_upd_definition @{thm kernel_all_substitute.clzl'_def}
      |> FunctionInfo.function_info_upd_corres_thm @{thm "kernel_all_substitute.clzl'_TScorres"};
    val clzl_info = FunctionInfo.Phasetab.make
          (map (fn info => (#phase info, Symtab.make [("clzl", info)]))
               [clzl_cp, clzl_l1, clzl_l2, clzl_ts]);
    val file = "../c/build/$L4V_ARCH/kernel_all.c_pp";
    val fn_info = the (Symtab.lookup (AutoCorresFunctionInfo.get thy) file);
    val fn_info' = phasetab_merge_with (Symtab.merge (K false)) (fn_info, clzl_info);
in
  thy
  |> AutoCorresFunctionInfo.map (Symtab.update (file, fn_info'))
end
\<close>

text \<open>Now AutoCorres will use our specification in calls to clzl.\<close>
autocorres
  [
   skip_heap_abs, skip_word_abs, (* for compatibility *)
   scope = chooseThread,
   scope_depth = 0,
   c_locale = kernel_all_substitute,
   no_c_termination
  ] "../c/build/$L4V_ARCH/kernel_all.c_pp"

context kernel_m begin
thm clzl'_def
thm chooseThread'_def
end



subsection \<open>Test recursion + call to previously translated (cap_get_capType)\<close>
autocorres
  [
   skip_heap_abs, skip_word_abs, ts_rules = nondet, (* for compatibility *)
   scope = cap_get_capType,
   scope_depth = 0,
   c_locale = kernel_all_substitute
  ] "../c/build/$L4V_ARCH/kernel_all.c_pp"

thm kernel_all_substitute.cap_get_capType'_def
    kernel_all_substitute.cap_get_capType_body_def

autocorres
  [
   skip_heap_abs, skip_word_abs, ts_rules = nondet, (* for compatibility *)
   scope = cteDelete finaliseSlot reduceZombie,
   scope_depth = 0,
   c_locale = kernel_all_substitute
  ] "../c/build/$L4V_ARCH/kernel_all.c_pp"

context kernel_m begin
thm cteDelete'.simps finaliseSlot'.simps reduceZombie'.simps
end

text \<open>Test call to recursive function group\<close>
autocorres
  [
   skip_heap_abs, skip_word_abs, ts_rules = nondet, (* for compatibility *)
   scope = cteRevoke,
   scope_depth = 0,
   c_locale = kernel_all_substitute
  ] "../c/build/$L4V_ARCH/kernel_all.c_pp"

context kernel_m begin
thm cteRevoke'_def
end



subsection \<open>Experiment with proving bitfield specs\<close>

text \<open>
  Here we translate some bitfield functions, then separately prove that
  the translated functions satisfy the bitfield_gen specs.
\<close>
autocorres
  [
   skip_heap_abs, skip_word_abs, ts_rules = nondet, (* for compatibility *)
   scope = cap_capType_equals
     cap_cnode_cap_get_capCNodePtr
     cap_cnode_cap_get_capCNodeGuard
     cap_cnode_cap_get_capCNodeRadix,
   scope_depth = 0,
   c_locale = kernel_all_substitute
  ] "../c/build/$L4V_ARCH/kernel_all.c_pp"

lemma of_bl_from_cond:
  "(if C then 1 else 0) = of_bl [C]"
  by (simp add: word_1_bl)
lemma of_bl_cond:
  "(if C then of_bl [A] else of_bl [B]) = of_bl [if C then A else B]"
  by (rule if_f)

context kernel_m begin
lemma "\<lbrace>\<lambda>_. cap_get_tag cap = scast cap_cnode_cap\<rbrace>
         cap_cnode_cap_get_capCNodePtr' cap
       \<lbrace>\<lambda>r _. r = capCNodePtr_CL (cap_cnode_cap_lift cap)\<rbrace>!"
  apply (unfold cap_cnode_cap_get_capCNodePtr'_def)
  apply wp
  apply (simp add: cap_get_tag_def cap_cnode_cap_lift_def cap_lift_def cap_tag_values
                   shiftr_over_and_dist mask_def)
  done

lemma "\<lbrace>\<lambda>_. cap_get_tag cap = scast cap_cnode_cap\<rbrace>
         cap_cnode_cap_get_capCNodeGuard' cap
       \<lbrace>\<lambda>r _. r = capCNodeGuard_CL (cap_cnode_cap_lift cap)\<rbrace>!"
  apply (unfold cap_cnode_cap_get_capCNodeGuard'_def)
  apply wp
  apply (simp add: cap_get_tag_def cap_cnode_cap_lift_def cap_lift_def cap_tag_values
                   shiftr_over_and_dist mask_def)
  done

lemma "\<lbrace>\<lambda>_. cap_get_tag cap = scast cap_cnode_cap\<rbrace>
         cap_cnode_cap_get_capCNodeRadix' cap
       \<lbrace>\<lambda>r _. r = capCNodeRadix_CL (cap_cnode_cap_lift cap)\<rbrace>!"
  apply (unfold cap_cnode_cap_get_capCNodeRadix'_def)
  apply wp
  apply (simp add: cap_get_tag_def cap_cnode_cap_lift_def cap_lift_def cap_tag_values
                   shiftr_over_and_dist mask_def)
  done

end


subsection \<open>Experiment with transferring bitfield specs\<close>

text \<open>
  For wrapped bitfield functions, the @{term hoarep} triples for them can be transferred
  to @{term valid} triples.
\<close>
context kernel_m begin

thm cap_zombie_cap_get_capZombiePtr_spec
lemma cap_zombie_cap_get_capZombiePtr'_spec:
  "\<lbrace>\<lambda>s. s = s0 \<and> cap_get_tag cap = scast cap_zombie_cap \<and> get_capZombieBits_CL (cap_zombie_cap_lift cap) < 0x1F\<rbrace>
     cap_zombie_cap_get_capZombiePtr' cap
   \<lbrace>\<lambda>r s. s = s0 \<and> r = get_capZombiePtr_CL (cap_zombie_cap_lift cap)\<rbrace>"
  (* setup *)
  apply (rule hoare_weaken_pre)
   apply (rule hoare_strengthen_post)
    (* generic transfer operation *)
    thm autocorres_transfer_spec_no_modifies[OF
          cap_zombie_cap_get_capZombiePtr'_def cap_zombie_cap_get_capZombiePtr_spec]
    apply (rule autocorres_transfer_spec_no_modifies[OF
                  cap_zombie_cap_get_capZombiePtr'_def cap_zombie_cap_get_capZombiePtr_spec _ refl,
                  where cs="undefined\<lparr>globals := s0, cap_' := cap\<rparr>"])
                        (* the standard tactics can't invent a suitable cs automatically *)
      apply (rule cap_zombie_cap_get_capZombiePtr_modifies)
     (* prove sanity conditions on local variables and preconds *)
     apply auto
  done

thm cap_zombie_cap_get_capZombieType_spec
lemma cap_zombie_cap_get_capZombieType'_spec:
  "\<lbrace>\<lambda>s. s = s0 \<and> cap_get_tag cap = scast cap_zombie_cap \<rbrace>
     cap_zombie_cap_get_capZombieType' cap
   \<lbrace>\<lambda>r s. s = s0 \<and> r = capZombieType_CL (cap_zombie_cap_lift cap)\<rbrace>"
  apply (rule hoare_weaken_pre)
   apply (rule hoare_strengthen_post)
    thm autocorres_transfer_spec_no_modifies[OF
          cap_zombie_cap_get_capZombieType'_def cap_zombie_cap_get_capZombieType_spec]
    apply (rule autocorres_transfer_spec_no_modifies[OF
                  cap_zombie_cap_get_capZombieType'_def cap_zombie_cap_get_capZombieType_spec _ refl,
                  where cs="undefined\<lparr>globals := s0, cap_' := cap\<rparr>"])
      apply (rule cap_zombie_cap_get_capZombieType_modifies)
     apply auto
  done

text \<open>There are some extra complications when transferring bitfield update specs\<close>
thm cap_zombie_cap_set_capZombieNumber_spec (* extra quantified var; precond talks about initial state *)
lemma cap_zombie_cap_set_capZombieNumber'_spec:
  "\<lbrace>\<lambda>s. s = s0 \<and> ccap_relation cap' cap \<and> isZombie cap' \<and> capAligned cap' \<and> unat n \<le> zombieCTEs (capZombieType cap')\<rbrace>
     cap_zombie_cap_set_capZombieNumber' cap n
   \<lbrace>\<lambda>r s. s = s0 \<and> ccap_relation (capZombieNumber_update (\<lambda>_. unat n) cap') r\<rbrace>"
  apply (rule hoare_weaken_pre)
   apply (rule hoare_strengthen_post)
    (* All_to_all' drops the extra quantifier. (rule_format would remove both) *)
    thm autocorres_transfer_spec_no_modifies[OF
          cap_zombie_cap_set_capZombieNumber'_def cap_zombie_cap_set_capZombieNumber_spec[THEN All_to_all']]
    apply (rule autocorres_transfer_spec_no_modifies[OF
                  cap_zombie_cap_set_capZombieNumber'_def cap_zombie_cap_set_capZombieNumber_spec[THEN All_to_all'],
                  where cs="undefined\<lparr>globals := s0, cap_' := cap, n_' := n\<rparr>"])
      apply (rule cap_zombie_cap_set_capZombieNumber_modifies)
     (* swap initial state var to allow unification *)
     apply (rule collect_unlift)
    apply auto
  done

thm cap_capType_equals_spec
lemma cap_capType_equals'_spec:
  "\<lbrace>\<lambda>s. s = s0 \<rbrace>
     AC_call_L1 (\<lambda>s. cap_' s = cap \<and> cap_type_tag_' s = cap_type_tag) globals ret__int_'
       (L1_call_simpl check_termination \<Gamma> cap_capType_equals_'proc)
   \<lbrace>\<lambda>r s. s = s0 \<and> r = of_bl [cap_get_tag cap = cap_type_tag]\<rbrace>"
  apply (rule hoare_weaken_pre)
   apply (rule hoare_strengthen_post)
    thm autocorres_transfer_spec_no_modifies[OF reflexive cap_capType_equals_spec]
    apply (rule autocorres_transfer_spec_no_modifies[
                  OF reflexive cap_capType_equals_spec,
                  where cs="undefined\<lparr>globals := s0, cap_' := cap, cap_type_tag_' := cap_type_tag\<rparr>"])
      apply (rule cap_capType_equals_modifies)
     apply auto
  done

(* TODO: any other types of bitfield_gen functions? *)

end



context kernel_m begin
text \<open>Termination proofs for use with @{thm ccorres_to_corres_with_termination}. Currently unused.\<close>

lemma cap_get_capType_terminates:
  "\<Gamma> \<turnstile> Call cap_get_capType_'proc \<down> Normal s"
  apply (tactic \<open>ALLGOALS (terminates_trivial_tac @{context})\<close>;
         fail)
  done

lemma thread_state_get_tcbQueued_terminates:
  "\<Gamma> \<turnstile> Call thread_state_get_tcbQueued_'proc \<down> Normal s"
  apply (tactic \<open>ALLGOALS (terminates_trivial_tac @{context})\<close>;
         fail)
  done

lemma thread_state_ptr_set_tcbQueued_terminates:
  "\<Gamma> \<turnstile> Call thread_state_ptr_set_tcbQueued_'proc \<down> Normal s"
  apply (tactic \<open>ALLGOALS (terminates_trivial_tac @{context})\<close>;
         fail)
  done

lemma ready_queues_index_terminates:
  "\<Gamma> \<turnstile> Call ready_queues_index_'proc \<down> Normal s"
  apply (tactic \<open>ALLGOALS (terminates_trivial_tac @{context})\<close>;
         fail)
  done

lemma prio_to_l1index_terminates:
  "\<Gamma> \<turnstile> Call prio_to_l1index_'proc \<down> Normal s"
  apply (tactic \<open>ALLGOALS (terminates_trivial_tac @{context})\<close>;
         fail)
  done

lemma removeFromBitmap_terminates:
  "\<Gamma> \<turnstile> Call removeFromBitmap_'proc \<down> Normal s"
  apply (tactic \<open>ALLGOALS (terminates_trivial_tac @{context})\<close>;
         rule prio_to_l1index_terminates)
  done

lemma addToBitmap_terminates:
  "\<Gamma> \<turnstile> Call addToBitmap_'proc \<down> Normal s"
  apply (tactic \<open>ALLGOALS (terminates_trivial_tac @{context})\<close>;
         rule prio_to_l1index_terminates)
  done

lemma tcbSchedDequeue_terminates:
   "\<Gamma> \<turnstile> Call tcbSchedDequeue_'proc \<down> Normal s"
  apply (tactic \<open>ALLGOALS (terminates_trivial_tac @{context})\<close>;
         rule thread_state_get_tcbQueued_terminates
              thread_state_ptr_set_tcbQueued_terminates
              ready_queues_index_terminates
              removeFromBitmap_terminates)
  done

lemma tcbSchedAppend_terminates:
   "\<Gamma> \<turnstile> Call tcbSchedAppend_'proc \<down> Normal s"
  apply (tactic \<open>ALLGOALS (terminates_trivial_tac @{context})\<close>;
         rule thread_state_get_tcbQueued_terminates
              thread_state_ptr_set_tcbQueued_terminates
              ready_queues_index_terminates
              addToBitmap_terminates)
  done

lemma tcbSchedEnqueue_terminates:
   "\<Gamma> \<turnstile> Call tcbSchedEnqueue_'proc \<down> Normal s"
  apply (tactic \<open>ALLGOALS (terminates_trivial_tac @{context})\<close>;
         rule thread_state_get_tcbQueued_terminates
              thread_state_ptr_set_tcbQueued_terminates
              ready_queues_index_terminates
              addToBitmap_terminates)
  done

lemma rescheduleRequired_terminates:
   "\<Gamma> \<turnstile> Call rescheduleRequired_'proc \<down> Normal s"
  apply (tactic \<open>ALLGOALS (terminates_trivial_tac @{context})\<close>;
         rule tcbSchedEnqueue_terminates)
  done

end

end
