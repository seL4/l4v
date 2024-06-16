(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

text \<open>
  The InfoFlow theorem needs that caps shared between labels cannot be deleted.
  In order to do that, this file introduces a dummy label, SilcLabel that will
  own all those caps. It then proves all the properties needed about SilcLabel
  doing its job.
\<close>

theory FinalCaps
imports ArchInfoFlow_IF
begin

(* FIXME: arch_split: need to have a label on arch refs*)
fun pasGenAbs :: "'a PAS \<Rightarrow> gen_obj_ref \<Rightarrow> 'a" where
  "pasGenAbs aag (ObjRef ref) = pasObjectAbs aag ref"
| "pasGenAbs aag (IRQRef ref) = pasIRQAbs aag ref"

(*FIXME REPLACE by alternative definition *)
definition cap_points_to_label where
  "cap_points_to_label aag cap l \<equiv>
     (\<forall>x \<in> obj_refs cap. (pasObjectAbs aag x = l)) \<and>
     (\<forall>x \<in> cap_irqs cap. (pasIRQAbs aag x = l))"

(* WARNING: Reply cap will be considered as intra_label even if they are between labels *)
definition intra_label_cap where
  "intra_label_cap aag slot s \<equiv>
     (\<forall>cap. cte_wp_at ((=) cap) slot s
            \<longrightarrow> (cap_points_to_label aag cap (pasObjectAbs aag (fst slot))))"

(*FIXME REPLACE by alternative definition *)
definition slots_holding_overlapping_caps :: "cap \<Rightarrow> ('z::state_ext) state \<Rightarrow> cslot_ptr set" where
  "slots_holding_overlapping_caps cap s \<equiv>
     {cref. \<exists>cap'. fst (get_cap cref s) = {(cap', s)} \<and>
                   (obj_refs cap \<inter> obj_refs cap' \<noteq> {} \<or>
                    cap_irqs cap \<inter> cap_irqs cap' \<noteq> {} \<or>
                    arch_gen_refs cap \<inter> arch_gen_refs cap' \<noteq> {})}"

(* FIXME MOVE *)
abbreviation subject_can_affect :: "'a PAS \<Rightarrow> obj_ref \<Rightarrow> bool" where
  "subject_can_affect aag ptr \<equiv>
     pasObjectAbs aag ptr \<in> subjectAffects (pasPolicy aag) (pasSubject aag)"


abbreviation subject_can_affect_label_directly :: "'a PAS \<Rightarrow> 'a \<Rightarrow> bool" where
  "subject_can_affect_label_directly aag l \<equiv>
     l \<in> subjectAffects (pasPolicy aag) (pasSubject aag)"


text \<open>We introduce a new label. The name 'silc' here stands for 'safe inter-label caps',
  since the domain with this label holds copies of all inter-label caps to ensure that
  any others remain 'safe' by never becoming final caps, which would otherwise introduce
  a potential covert storage channel\<close>
datatype 'a subject_label = OrdinaryLabel 'a | SilcLabel


abbreviation(input) aag_can_read_not_silc where
  "aag_can_read_not_silc aag ptr \<equiv> aag_can_read aag ptr \<and> pasObjectAbs aag ptr \<noteq> SilcLabel"


text\<open>We need to introduce an equivalence on the dummy domain, and add
   it to the state that the current subject can read from (i.e.
   effectively add it to the current subject's domain), to complete
   the proof for is_final_cap. This will necessitate showing that
   the dummy domain's state is never affected, but this should be
   relatively easy. The annoying part is that now we end up proving
   a different property; it will take some finesse to avoid having
   to do a search/replace on @{term reads_respects} \<rightarrow> reads_respects_f\<close>
definition silc_dom_equiv where
  "silc_dom_equiv aag \<equiv> equiv_for (\<lambda>x. pasObjectAbs aag x = SilcLabel) kheap"

text\<open>This is an invariant that ensures that the info leak due to is_final_cap doesn't
   arise. Silc stands for 'safe inter label caps'.
   We include a condition that the contents of SilcLabel wrt the kheap are unchanged from
   some fixed reference state, since we invariably use this fact to reason that the
   invariant is preserved anyway. Including it here saves duplicating essentially identical
   reasoning.\<close>

definition silc_inv :: "'a subject_label PAS \<Rightarrow> det_ext state \<Rightarrow> det_ext state \<Rightarrow> bool" where
  "silc_inv aag st s \<equiv>
     (SilcLabel \<noteq> pasSubject aag) \<and>
     (\<forall>x. pasObjectAbs aag x = SilcLabel \<longrightarrow>  (\<exists>sz. cap_table_at sz x s)) \<and>
     (\<forall>y auth. (y, auth, SilcLabel) \<in> pasPolicy aag \<longrightarrow> y = SilcLabel) \<and>
     (\<forall>slot cap. cte_wp_at ((=) cap) slot s \<and>
                 \<not> intra_label_cap aag slot s
                 \<longrightarrow> (\<exists>lslot. lslot \<in> slots_holding_overlapping_caps cap s \<and>
                              (pasObjectAbs aag (fst lslot) = SilcLabel))) \<and>
     all_children (\<lambda>x. pasObjectAbs aag (fst x) = SilcLabel) (cdt s) \<and>
     silc_dom_equiv aag st s \<and>
     \<comment> \<open>We want the following condition to hold on s as well,
         but stating that here makes proofs more difficult.
         It is shown below in silc_inv_no_transferable'.\<close>
     (\<forall>slot. pasObjectAbs aag (fst slot) = SilcLabel \<and>
             cte_wp_at (\<lambda>cap. cap \<noteq> NullCap \<and> is_transferable_cap cap) slot st
             \<longrightarrow> False)"


(* FIXME MOVE *)
context strengthen_implementation begin

lemma strengthen_cte_wp_at[strg]:
  "(\<And>x. st F (\<longrightarrow>) (P x) (Q x)) \<Longrightarrow> st F (\<longrightarrow>) (cte_wp_at P slot s) (cte_wp_at Q slot s)"
  by (cases F, auto elim:cte_wp_at_weakenE)

end


lemma slots_holding_overlapping_caps_def':
  "slots_holding_overlapping_caps cap s =
   {cref. cte_wp_at (\<lambda>cap'. gen_obj_refs cap \<inter> gen_obj_refs cap' \<noteq> {}) cref s}"
  unfolding slots_holding_overlapping_caps_def cte_wp_at_def gen_obj_refs_def
  by blast

lemma silc_inv_exst[simp]:
  "silc_inv aag st (trans_state f s) = silc_inv aag st s"
  by (auto simp: silc_inv_def silc_dom_equiv_def intra_label_cap_def
                 equiv_for_def slots_holding_overlapping_caps_def)

lemma silc_inv_not_subject:
  "silc_inv aag st s \<Longrightarrow> SilcLabel \<noteq> pasSubject aag"
  unfolding silc_inv_def by force

lemma silc_inv_silc_dom_equiv:
  "silc_inv aag st s \<Longrightarrow> silc_dom_equiv aag st s"
  unfolding silc_inv_def by force

lemma silc_inv_cnode_only:
  "\<lbrakk> silc_inv aag st s; pasObjectAbs aag x = SilcLabel \<rbrakk>
     \<Longrightarrow> \<exists>sz. cap_table_at sz x s"
  unfolding silc_inv_def by force

lemma silc_inv_cnode_onlyE:
  assumes si: "silc_inv aag st s"
  assumes posl: "pasObjectAbs aag x = SilcLabel"
  obtains sz where "cap_table_at sz x s"
  using si posl silc_inv_cnode_only by blast

lemma silc_inv_no_transferable:
  "\<lbrakk> silc_inv aag st s;  pasObjectAbs aag (fst slot) = SilcLabel;
     cte_wp_at (\<lambda>cap. cap \<noteq> NullCap \<and> is_transferable_cap cap) slot st \<rbrakk>
     \<Longrightarrow> False"
  unfolding silc_inv_def by (force simp del: split_paired_All)

lemmas silc_inv_no_transferableD = silc_inv_no_transferable[where slot="(a,b)" for a b,simplified]

lemma cte_wp_at_pspace_specI:
  "\<lbrakk> cte_wp_at P slot s; kheap s (fst slot) = kheap s' (fst slot) \<rbrakk>
     \<Longrightarrow> cte_wp_at P slot s'"
  by (simp add: cte_wp_at_cases)

lemma silc_inv_no_transferable':
  "silc_inv aag st s \<Longrightarrow> pasObjectAbs aag (fst slot) = SilcLabel \<Longrightarrow>
   cte_wp_at (\<lambda>cap. cap \<noteq> NullCap \<and> is_transferable_cap cap) slot s \<Longrightarrow> False"
  apply (frule (1) silc_inv_no_transferable)
   apply (drule silc_inv_silc_dom_equiv)
   apply (simp add:silc_dom_equiv_def)
   apply (drule (1) equiv_forD)
   apply (elim cte_wp_at_pspace_specI)
  by simp+

lemmas silc_inv_no_transferableD' =
  silc_inv_no_transferable'[where slot="(a,b)" for a b, simplified]

lemma (in is_extended') silc_inv[wp]: "I (silc_inv aag st)" by (rule lift_inv,simp)

lemma get_cap_cte_wp_at':
  "(fst (get_cap p s) = {(r,s)}) = cte_wp_at ((=) r) p s"
  by (auto simp: cte_wp_at_def)

lemma silc_invD:
  "\<lbrakk> silc_inv aag st s; cte_wp_at ((=) cap) slot s; \<not> intra_label_cap aag slot s \<rbrakk>
     \<Longrightarrow> (\<exists>lslot. lslot \<in> slots_holding_overlapping_caps cap s \<and>
                 pasObjectAbs aag (fst lslot) = SilcLabel)"
  apply (clarsimp simp: silc_inv_def)
  apply (drule_tac x="fst slot" in spec, drule_tac x="snd slot" in spec, fastforce)
  done

lemma is_final_cap'_def4:
  "is_final_cap' cap s \<equiv> \<exists>a b. slots_holding_overlapping_caps cap s = {(a,b)}"
  by (simp add: is_final_cap'_def slots_holding_overlapping_caps_def gen_obj_refs_Int)


(* I think this property is strong enough to give us a sane
   confidentiality rule for is_final_cap. This is true, so long as
   we include the dummy domain l in what the current subject can
   read *)
(* FIXME DELETE *)
lemma silc_inv:
  "silc_inv aag st s \<Longrightarrow>
     (\<forall>cap slot. cte_wp_at ((=) cap) slot s \<and> is_final_cap' cap s \<longrightarrow>
                 (intra_label_cap aag slot s \<or> (pasObjectAbs aag (fst slot) = SilcLabel)))"
  apply clarsimp
  apply (erule contrapos_np)
  apply (drule (2) silc_invD)
  apply (subgoal_tac "(a,b) \<in> slots_holding_overlapping_caps cap s")
   apply (clarsimp simp: is_final_cap'_def4 cte_wp_at_def)
  apply (auto simp: slots_holding_overlapping_caps_def cte_wp_at_def)
  done

lemma silc_inv_finalD:
  "\<lbrakk> silc_inv aag st s; cte_wp_at ((=) cap) slot s; is_final_cap' cap s \<rbrakk>
     \<Longrightarrow> intra_label_cap aag slot s \<or> (pasObjectAbs aag (fst slot) = SilcLabel)"
  apply clarsimp
  apply (erule contrapos_np)
  apply (drule (2) silc_invD)
  apply (subgoal_tac "slot \<in> slots_holding_overlapping_caps cap s")
   apply (clarsimp simp: is_final_cap'_def4 cte_wp_at_def)
  apply (auto simp: slots_holding_overlapping_caps_def cte_wp_at_def)
  done

lemma silc_inv_finalE:
  assumes hyp: "silc_inv aag st s" "cte_wp_at ((=) cap) slot s" "is_final_cap' cap s"
  obtains "intra_label_cap aag slot s" | "pasObjectAbs aag (fst slot) = SilcLabel"
  using hyp silc_inv_finalD by blast

lemma cte_wp_at_pspace':
  "kheap s (fst p) = kheap s' (fst p) \<Longrightarrow> cte_wp_at P p s = cte_wp_at P p s'"
  apply (rule iffI)
   apply (erule cte_wp_atE)
    apply (auto intro: cte_wp_at_cteI dest: sym)[1]
   apply (auto intro: cte_wp_at_tcbI dest: sym)[1]
  apply (erule cte_wp_atE)
   apply (auto intro: cte_wp_at_cteI dest: sym)[1]
  apply (auto intro: cte_wp_at_tcbI dest: sym)[1]
  done

lemma caps_of_state_pspace':
  assumes x: "kheap s (fst slot) = kheap s' (fst slot)"
  shows "caps_of_state s slot = caps_of_state s' slot"
  by (simp add: caps_of_state_cte_wp_at cte_wp_at_pspace'[OF x])

lemma caps_of_state_intra_label_cap:
  "\<lbrakk> caps_of_state s slot = Some cap; caps_of_state t slot = Some cap; intra_label_cap aag slot s\<rbrakk>
     \<Longrightarrow> intra_label_cap aag slot t"
  by (fastforce simp: intra_label_cap_def cte_wp_at_caps_of_state)

lemma not_is_final_cap_caps_of_stateE:
  assumes hyp: "\<not> is_final_cap' cap s" "caps_of_state s slot = Some cap" "gen_obj_refs cap \<noteq> {}"
  obtains slot' where "slot' \<noteq> slot" "slot' \<in> slots_holding_overlapping_caps cap s"
  using hyp
  apply (simp add: is_final_cap'_def4)
  apply (subgoal_tac "slot \<in> slots_holding_overlapping_caps cap s")
   apply (drule_tac x="fst slot" in spec, drule_tac x="snd slot" in spec)
   apply simp
   apply fastforce
  apply (auto simp: slots_holding_overlapping_caps_def' cte_wp_at_caps_of_state)
  done

lemma is_final_then_nonempty_refs:
  "is_final_cap' cap s \<Longrightarrow> gen_obj_refs cap \<noteq> {}"
  by (auto simp add: is_final_cap'_def)

lemma caps_ref_single_objects:
  "\<lbrakk> x \<in> obj_refs cap; y \<in> obj_refs cap \<rbrakk> \<Longrightarrow> x = y"
  by (cases cap; simp)

lemma caps_ref_single_irqs:
  "\<lbrakk> x \<in> cap_irqs cap; y \<in> cap_irqs cap \<rbrakk> \<Longrightarrow> x = y"
  by (cases cap; simp)

lemma not_is_final_cap[rotated -1]:
  "\<lbrakk> caps_of_state s slot = Some cap; caps_of_state s slot' = Some cap';
     gen_obj_refs cap \<inter> gen_obj_refs cap' \<noteq> {}; slot' \<noteq> slot \<rbrakk>
     \<Longrightarrow> \<not> is_final_cap' cap s"
  apply (rule ccontr)
  apply (clarsimp simp: is_final_cap'_def get_cap_cte_wp_at' cte_wp_at_caps_of_state)
  apply (erule_tac B="{(a,b)}" in equalityE)
  apply (frule_tac c=slot in subsetD; fastforce)
  done


definition reads_equiv_f
where
  "reads_equiv_f aag s s' \<equiv> reads_equiv aag s s' \<and> silc_dom_equiv aag s s'"

abbreviation reads_respects_f
where
  "reads_respects_f aag l P f \<equiv> equiv_valid_inv (reads_equiv_f aag) (affects_equiv aag l) P f"


lemma intra_label_capD:
  "\<lbrakk> intra_label_cap aag slot s; cte_wp_at ((=) cap) slot s \<rbrakk>
     \<Longrightarrow> cap_points_to_label aag cap (pasObjectAbs aag (fst slot))"
  by (auto simp: intra_label_cap_def)

lemma intra_label_capD':
  "\<lbrakk> intra_label_cap aag slot s; caps_of_state s slot = Some cap \<rbrakk>
     \<Longrightarrow> cap_points_to_label aag cap (pasObjectAbs aag (fst slot))"
  by (auto simp: intra_label_cap_def cte_wp_at_caps_of_state)

lemma is_subject_kheap_eq:
  "\<lbrakk> reads_equiv aag s t; is_subject aag ptr \<rbrakk>
     \<Longrightarrow> kheap s ptr = kheap t ptr"
  apply (clarsimp simp: reads_equiv_def2)
  apply (erule states_equiv_forE_kheap)
  apply (blast intro: aag_can_read_self)
  done

lemma aag_can_read_kheap_eq:
  "\<lbrakk> reads_equiv aag s t; aag_can_read aag ptr \<rbrakk>
     \<Longrightarrow> kheap s ptr = kheap t ptr"
  apply (clarsimp simp: reads_equiv_def2)
  apply (erule states_equiv_forE_kheap)
  apply blast
  done

lemma caps_ref_either_an_object_or_irq':
   "ref \<in> cap_irqs cap' \<Longrightarrow>
    (obj_refs cap' = {} \<and> arch_gen_refs cap' = {})"
  apply (case_tac cap', simp_all)
  done


locale FinalCaps_1 =
  fixes aag :: "'a subject_label PAS"
  (* FIXME IF: precludes X64 *)
  assumes FIXME_arch_gen_refs:
    "arch_gen_refs cap = {}"
  and aobj_ref_same_aobject:
    "same_aobject_as cp cp' \<Longrightarrow> aobj_ref cp = aobj_ref cp'"
  and arch_invoke_irq_handler_silc_inv[wp]:
    "arch_invoke_irq_handler hi \<lbrace>silc_inv aag st\<rbrace>"
  and arch_post_cap_deletion_silc_inv[wp]:
    "arch_post_cap_deletion acap \<lbrace>silc_inv aag st\<rbrace>"
  and arch_finalise_cap_silc_inv[wp]:
    "arch_finalise_cap c x \<lbrace>silc_inv aag st\<rbrace>"
  and prepare_thread_delete_silc_inv[wp]:
    "prepare_thread_delete p \<lbrace>silc_inv aag st\<rbrace>"
  and handle_reserved_irq_silc_inv[wp]:
    "handle_reserved_irq irq \<lbrace>silc_inv aag st\<rbrace>"
  and arch_mask_irq_signal_silc_inv[wp]:
    "arch_mask_irq_signal irq \<lbrace>silc_inv aag st\<rbrace>"
  and handle_vm_fault_silc_inv[wp]:
    "handle_vm_fault t vmft \<lbrace>silc_inv aag st\<rbrace>"
  and handle_vm_fault_cur_thread[wp]:
    "\<And>P. handle_vm_fault t vmft \<lbrace>\<lambda>s :: det_state. P (cur_thread s)\<rbrace>"
  and handle_hypervisor_fault_silc_inv[wp]:
    "handle_hypervisor_fault t hvft \<lbrace>silc_inv aag st\<rbrace>"
  and arch_activate_idle_threadt_silc_inv[wp]:
    "arch_activate_idle_thread t \<lbrace>silc_inv aag st\<rbrace>"
  and arch_switch_to_idle_thread_silc_inv[wp]:
    "arch_switch_to_idle_thread \<lbrace>silc_inv aag st\<rbrace>"
  and arch_switch_to_thread_silc_inv[wp]:
    "arch_switch_to_thread t \<lbrace>silc_inv aag st\<rbrace>"
  and init_arch_objects_silc_inv[wp]:
    "init_arch_objects typ ptr num sz refs \<lbrace>silc_inv aag st\<rbrace>"
  and init_arch_objects_cte_wp_at[wp]:
    "\<And>P. init_arch_objects typ ptr num sz refs \<lbrace>\<lambda>s :: det_state. P (cte_wp_at P' slot s)\<rbrace>"
  and finalise_cap_makes_halted:
    "\<lbrace>invs and valid_cap cap and (\<lambda>s. ex = is_final_cap' cap s) and cte_wp_at ((=) cap) slot\<rbrace>
     finalise_cap cap ex
     \<lbrace>\<lambda>rv s :: det_state. \<forall>t \<in> obj_refs (fst rv). halted_if_tcb t s\<rbrace>"
  and arch_post_modify_registers_silc_inv[wp]:
    "arch_post_modify_registers cur t \<lbrace>silc_inv aag st\<rbrace>"
  and arch_derive_cap_silc:
    "\<lbrace>\<lambda>s :: det_state. cap = ArchObjectCap acap \<and>
                       (\<not> cap_points_to_label aag cap l \<longrightarrow> R (slots_holding_overlapping_caps cap s))\<rbrace>
     arch_derive_cap acap
     \<lbrace>\<lambda>cap' s. \<not> cap_points_to_label aag cap' l \<longrightarrow> R (slots_holding_overlapping_caps cap' s)\<rbrace>,-"
begin

lemma cap_points_to_label_def':
  "cap_points_to_label aag cap l = (\<forall>x \<in> gen_obj_refs cap. pasGenAbs aag x = l)"
  unfolding cap_points_to_label_def
  by (simp add: gen_obj_refs_def ball_Un FIXME_arch_gen_refs)

lemma caps_ref_either_an_object_or_irq:
   "ref \<in> obj_refs cap'
    \<Longrightarrow> cap_irqs cap' = {} \<and> arch_gen_refs cap' = {}"
  apply (clarsimp simp: FIXME_arch_gen_refs)
  apply (case_tac cap'; clarsimp)
  done

lemma caps_ref_either_an_object_or_irq'':
   "ref \<in> arch_gen_refs cap'
    \<Longrightarrow> obj_refs cap' = {} \<and> cap_irqs cap' = {}"
  apply (clarsimp simp: FIXME_arch_gen_refs)
  done

lemma arch_gen_refs_no_intersection[simp]:
  "arch_gen_refs c \<inter> arch_gen_refs c' = {}"
  by (cases c; auto simp: FIXME_arch_gen_refs)

lemma is_final_cap'_read_equiv_imp:
  "\<lbrakk> silc_inv aag st s; cte_wp_at ((=) cap) slot s; silc_inv aag st t; cte_wp_at ((=) cap) slot t;
     aag_can_read_not_silc aag (fst slot); reads_equiv aag s t; is_final_cap' cap s \<rbrakk>
     \<Longrightarrow> is_final_cap' cap t"
  unfolding F[symmetric]
  subgoal premises prems
  proof (rule ccontr)
    assume not_final: "\<not> is_final_cap' cap t"
    from prems have ilcs : "intra_label_cap aag slot s"
      by (fastforce elim: silc_inv_finalE[OF _ caps_of_state_cteD, where s = s])
    hence ilct: "intra_label_cap aag slot t"
      using prems caps_of_state_intra_label_cap by blast
    from prems have sdest: "silc_dom_equiv aag s t"
      by (fastforce simp: silc_dom_equiv_def intro: equiv_for_trans
                    dest: silc_inv_silc_dom_equiv elim: equiv_for_sym)

    (* if cap is non final, then there must exists another cap overlapping somewhere *)
    from not_final prems obtain slot' where "slot' \<in> slots_holding_overlapping_caps cap t"
                                        and diff: "slot' \<noteq> slot"
      by (fastforce elim: not_is_final_cap_caps_of_stateE[OF _ _ is_final_then_nonempty_refs])
    then obtain cap' where cap': "caps_of_state t slot' = Some cap'"
                       and cap_overlap_cap': "gen_obj_refs cap \<inter> gen_obj_refs cap' \<noteq> {}"
      by (fastforce simp: slots_holding_overlapping_caps_def' cte_wp_at_caps_of_state)
    note prems = prems not_final cap' cap_overlap_cap' diff
    show False
    proof (cases "aag_can_read aag (fst slot')")
      case True
      (* This case is easy: slot' is in subjectReads domain, so cap' is also in slot' in s.
         Thus cap is not final: Direct contracticion*)
      thus ?thesis using prems
        apply -
        apply (erule(1) not_is_final_cap[THEN notE])
          apply (simp add: caps_of_state_pspace'[OF aag_can_read_kheap_eq])
        by fastforce+
    next
      case False note cant_read = this
      (* slot is in subjectRead, slot' isn't. However they hold overlaping caps. Thus: *)
      hence not_intra : "\<not> intra_label_cap aag slot' t"
        using prems ilct by (fastforce simp: cap_points_to_label_def' dest!: intra_label_capD')
      (* Then, accroding to silc_inv, there is a third cap in SilcLabel overlapping cap and cap'*)
      then obtain lslot where "lslot \<in> slots_holding_overlapping_caps cap' t"
                          and lslot_silc: "pasObjectAbs aag (fst lslot) = SilcLabel"
        using prems silc_invD[simplified F[symmetric]] by blast
      then obtain lcap where lcap_t: "caps_of_state t lslot = Some lcap"
                         and lcap_overlap_cap': "gen_obj_refs cap' \<inter> gen_obj_refs lcap \<noteq> {}"
        by (fastforce simp: slots_holding_overlapping_caps_def' cte_wp_at_caps_of_state)
      (* As lslot is in SilcLabel, kheap do not change between s and t and thus: *)
      have lcap_s: "caps_of_state s lslot = Some lcap"
        using lcap_t prems sdest
        apply (unfold silc_dom_equiv_def)
        apply (drule equiv_forD, rule lslot_silc)
        by (subst caps_of_state_pspace'; assumption)
      (* lcap thus overlaps cap in s but cap was final in s: contradiction *)
      then show ?thesis (* TODO CLEANUP *)
        using prems lslot_silc lcap_overlap_cap' lcap_s
        apply -
        apply (drule gen_obj_refs_distinct_or_equal)+
        apply simp
        apply (erule(1) not_is_final_cap[where slot' = lslot, THEN notE,rotated])
          apply (blast dest:is_final_then_nonempty_refs)
         apply assumption
        apply force
        done
    qed
  qed
  done

lemma is_final_cap'_read_equiv_eq:
  "\<lbrakk> silc_inv aag st s; cte_wp_at ((=) cap) slot s; silc_inv aag st t;
     cte_wp_at ((=) cap) slot t; aag_can_read_not_silc aag (fst slot); reads_equiv aag s t \<rbrakk>
     \<Longrightarrow> is_final_cap' cap s = is_final_cap' cap t"
  apply (rule iffI)
  subgoal by (rule is_final_cap'_read_equiv_imp)
  apply (drule reads_equiv_sym)
  subgoal by (rule is_final_cap'_read_equiv_imp)
  done

lemma is_final_cap_reads_respects:
  "reads_respects_f aag l (silc_inv aag st and (\<lambda>s. cte_wp_at ((=) cap) slot s \<and>
                                                    aag_can_read_not_silc aag (fst slot)))
                          (is_final_cap cap)"
  unfolding is_final_cap_def
  by (clarsimp simp: equiv_valid_def2 equiv_valid_2_def in_monad
                     reads_equiv_f_def is_final_cap'_read_equiv_eq)

end


definition ctes_wp_at
where
  "ctes_wp_at P s \<equiv> {ptr. cte_wp_at P ptr s}"

lemma slots_holding_overlapping_caps_def2:
  "slots_holding_overlapping_caps cap s =
     ctes_wp_at (\<lambda>c. (obj_refs cap \<inter> obj_refs c \<noteq> {}) \<or>
                     (cap_irqs cap \<inter> cap_irqs c \<noteq> {}) \<or>
                     (arch_gen_refs cap \<inter> arch_gen_refs c \<noteq> {})) s"
  by (simp add: slots_holding_overlapping_caps_def ctes_wp_at_def cte_wp_at_def)

lemma intra_label_cap_pres:
  assumes cte: "\<And>P. \<lbrace>\<lambda> s. \<not> cte_wp_at P slot s\<rbrace> f \<lbrace>\<lambda> _ s. \<not> cte_wp_at P slot s\<rbrace>"
  shows "\<lbrace>intra_label_cap aag slot\<rbrace> f \<lbrace>\<lambda>_. intra_label_cap aag slot\<rbrace>"
  apply (clarsimp simp: valid_def intra_label_cap_def)
  apply (drule_tac x=cap in spec)
  apply (case_tac "cte_wp_at ((=) cap) slot s")
   apply blast
  apply (drule_tac use_valid[OF _ cte])
   apply assumption
  apply blast
  done

lemma not_intra_label_cap_pres:
  assumes cte: "\<And>P. \<lbrace>cte_wp_at P slot\<rbrace> f \<lbrace>\<lambda>_. cte_wp_at P slot\<rbrace>"
  shows "\<lbrace>\<lambda>s. \<not> intra_label_cap aag slot s\<rbrace> f \<lbrace>\<lambda>_ s. \<not> intra_label_cap aag slot s\<rbrace>"
  apply (clarsimp simp: valid_def intra_label_cap_def)
  apply (rule_tac x=cap in exI)
  apply (drule_tac use_valid[OF _ cte], assumption)
  apply blast
  done

lemma cte_wp_at_pres_from_kheap':
  assumes l:
    "\<And>ptr P.
     \<lbrace>R and (\<lambda>s. P (kheap s ptr)) and K (pasObjectAbs aag ptr = l)\<rbrace>
     f
     \<lbrace>\<lambda>_ s. P (kheap s ptr)\<rbrace>"
  shows "\<lbrace>(\<lambda>s. Q (cte_wp_at P slot s)) and R and K (pasObjectAbs aag (fst slot) = l)\<rbrace>
         f
         \<lbrace>(\<lambda>_ s. Q (cte_wp_at P slot s))\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: valid_def | intro allI impI ballI)+
  apply (rename_tac x, case_tac x, simp, rename_tac rv s')
  apply (subgoal_tac "\<exists>x. kheap s (fst slot) = x")
   apply (erule exE, rename_tac x)
   apply (drule use_valid)
     apply (rule_tac ptr="fst slot" and P="\<lambda> y. y = x" in l)
    apply simp
   apply (drule trans, erule sym)
   apply (drule_tac P=P in cte_wp_at_pspace')
   apply simp
  apply blast
  done

lemmas cte_wp_at_pres_from_kheap = cte_wp_at_pres_from_kheap'[where R="\<top>", simplified]

lemma hoare_contrapositive:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>; \<not> Q r s'; (r, s') \<in> fst (f s) \<rbrakk> \<Longrightarrow> \<not> P s"
  apply (case_tac "P s")
   apply (blast dest: use_valid)
  apply assumption
  done

lemma allI': "\<forall>x y. P x y \<Longrightarrow> \<forall>y x. P x y"
  by simp

lemma silc_inv_pres:
  assumes l: "\<And>ptr P.
              \<lbrace>silc_inv aag st and (\<lambda>s. P (kheap s ptr)) and K (pasObjectAbs aag ptr = SilcLabel)\<rbrace>
              f
              \<lbrace>\<lambda>_ s. P (kheap s ptr)\<rbrace>"
  assumes c: "\<And>P. \<lbrace>\<lambda>s. P (cdt s)\<rbrace> f \<lbrace>\<lambda>_ s. P (cdt s)\<rbrace>"
  assumes ncte: "\<And>P slot. \<lbrace>\<lambda>s. \<not> cte_wp_at P slot s\<rbrace> f \<lbrace>\<lambda>_ s. \<not> cte_wp_at P slot s\<rbrace>"
  shows "\<lbrace>silc_inv aag st\<rbrace> f \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  apply (clarsimp simp: valid_def silc_inv_def)
  apply (clarsimp simp: slots_holding_overlapping_caps_def2 ctes_wp_at_def)
  apply (rule conjI)
   apply (intro allI impI)
   apply (frule_tac x=x in spec, erule (1) impE)
   apply (erule exE, rename_tac sz, rule_tac x=sz in exI)
   apply (simp add: obj_at_def)
   apply (elim exE conjE, rename_tac ko)
   apply (rule_tac x=ko in exI, simp)
   apply (erule use_valid[OF _ l])
   apply simp
   apply (clarsimp simp: silc_inv_def obj_at_def slots_holding_overlapping_caps_def2 ctes_wp_at_def)
  apply (rule conjI)
   apply clarsimp
   apply (frule_tac x=aa in spec, drule_tac x=ba in spec, drule_tac x=cap in spec)
   apply (subgoal_tac "cte_wp_at ((=) cap) (aa, ba) s \<and> \<not> intra_label_cap aag (aa,ba) s")
    apply (erule (1) impE)
    apply (elim exE conjE)+
    apply (rule_tac x=ab in exI, rule conjI, rule_tac x=bb in exI)
     apply (erule use_valid[OF _ cte_wp_at_pres_from_kheap'[where R="silc_inv aag st"]])
      apply (rule l)
     apply simp
     apply (clarsimp simp: silc_inv_def tcb_at_typ obj_at_def
                           slots_holding_overlapping_caps_def2 ctes_wp_at_def)
    apply assumption
   apply (rule conjI)
    apply (erule (1) hoare_contrapositive[OF ncte, simplified])
   apply (rule hoare_contrapositive[OF intra_label_cap_pres, simplified, OF ncte], assumption+)
  apply (rule conjI)
   apply (erule use_valid[OF _ c])
   apply simp
  apply (simp add: silc_dom_equiv_def)
  apply (rule equiv_forI)
  apply (erule use_valid[OF _ l])
  apply (fastforce simp: silc_inv_def obj_at_def slots_holding_overlapping_caps_def2
                         ctes_wp_at_def silc_dom_equiv_def
                   elim: equiv_forE)
  done


(* if we don't touch any caps or modify any object-types, then
   silc_inv is preserved *)
lemma silc_inv_triv:
  assumes kheap: "\<And>P x. \<lbrace>\<lambda>s. P (kheap s x)\<rbrace> f \<lbrace>\<lambda>_ s. P (kheap s x)\<rbrace>"
  assumes c: "\<And>P. \<lbrace>\<lambda>s. P (cdt s)\<rbrace> f \<lbrace>\<lambda> _ s. P (cdt s)\<rbrace>"
  assumes cte: "\<And>Q P slot. \<lbrace>\<lambda>s. Q (cte_wp_at P slot s)\<rbrace> f \<lbrace>\<lambda>_ s. Q (cte_wp_at P slot s)\<rbrace>"
  assumes typ_at: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  shows "\<lbrace>silc_inv aag st\<rbrace> f \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  apply (clarsimp simp: valid_def silc_inv_def)
  apply (rule conjI)
   apply (intro allI impI)
   apply (erule use_valid)
    apply (rule hoare_vcg_ex_lift)
    apply (rule cap_table_at_lift_valid[OF typ_at])
   apply blast
  apply (rule conjI)
   apply (clarsimp simp: slots_holding_overlapping_caps_def2 ctes_wp_at_def)
   apply (drule_tac x=aa in spec, drule_tac x=ba in spec, drule_tac x=cap in spec)
   apply (subgoal_tac "cte_wp_at ((=) cap) (aa, ba) s \<and> \<not> intra_label_cap aag (aa,ba) s")
    apply (elim exE conjE | simp)+
    apply (rule_tac x=ab in exI, rule conjI, rule_tac x=bb in exI)
     apply (erule (1) use_valid[OF _ cte])
    apply (assumption)
   apply (rule conjI)
    apply (case_tac "cte_wp_at ((=) cap) (aa, ba) s")
     apply assumption
    apply (drule use_valid[OF _ cte[where Q="\<lambda> x. \<not> x"]])
     apply assumption
    apply blast
   apply (case_tac "intra_label_cap aag (aa, ba) s")
    apply (drule_tac use_valid[OF _ intra_label_cap_pres[OF cte]])
     apply assumption
    apply blast
   apply assumption
  apply (simp add: silc_dom_equiv_def)
  apply (rule conjI)
   apply (erule use_valid[OF _ c])
   apply simp
  apply (rule equiv_forI)
  apply (erule use_valid[OF _ kheap])
  apply (fastforce elim: equiv_forE)
  done

lemma set_cap_well_formed_cnode_helper:
  "\<lbrakk> well_formed_cnode_n x xa; xa (snd slot) = Some y \<rbrakk>
     \<Longrightarrow> well_formed_cnode_n x (\<lambda>a. if a = snd slot then Some cap else xa a)"
  apply (simp add: well_formed_cnode_n_def)
  apply (rule equalityI)
   apply (drule equalityD1)
   apply (fastforce dest: subsetD split: if_splits)
  apply (drule equalityD2)
  apply (fastforce dest: subsetD split: if_splits)
  done

lemma set_cap_slots_holding_overlapping_caps_helper:
  "\<lbrakk> x \<in> slots_holding_overlapping_caps cap s; fst x \<noteq> fst slot;
     obj_refs cap = {} \<longrightarrow> cap_irqs cap \<noteq> {};
     ko_at (TCB tcb) (fst slot) s; tcb_cap_cases (snd slot) = Some (getF, setF, blah) \<rbrakk>
     \<Longrightarrow> x \<in> slots_holding_overlapping_caps cap
               (s\<lparr>kheap := (kheap s)(fst slot \<mapsto> TCB (setF (\<lambda>x. capa) tcb))\<rparr>)"
  apply (clarsimp simp: slots_holding_overlapping_caps_def)
  apply (rule_tac x=cap' in exI)
  apply (clarsimp simp: get_cap_cte_wp_at')
  apply (erule (1) upd_other_cte_wp_at)
  done

lemma set_cap_slots_holding_overlapping_caps_other:
  "\<lbrace>\<lambda>s. x \<in> slots_holding_overlapping_caps capa s \<and>
        pasObjectAbs aag (fst x) \<noteq> pasObjectAbs aag (fst slot)\<rbrace>
   set_cap cap slot
   \<lbrace>\<lambda>rv s. x \<in> slots_holding_overlapping_caps capa s\<rbrace>"
  unfolding set_cap_def
  apply (wpsimp wp: set_object_wp get_object_wp)+
  apply (case_tac "obj_refs capa = {} \<and> cap_irqs capa = {}")
   apply (clarsimp simp: slots_holding_overlapping_caps_def)
   apply (fastforce simp: get_cap_def get_object_def bind_def split_def gets_def get_def
                          return_def assert_def assert_opt_def fail_def
                   split: kernel_object.splits if_splits option.splits)
  apply (subgoal_tac "fst x \<noteq> fst slot")
   apply (intro allI impI conjI)
        apply (clarsimp simp: slots_holding_overlapping_caps_def)
        apply (rule_tac x=cap' in exI)
        apply clarsimp
        apply (subst get_cap_cte_wp_at')
        apply (rule upd_other_cte_wp_at)
         apply (simp add: cte_wp_at_def)
        apply assumption
        apply (clarsimp simp: get_cap_caps_of_state)
       apply ((drule set_cap_slots_holding_overlapping_caps_helper[where slot=slot], simp+)+)[5]
  apply clarsimp
  done

lemma set_cap_cte_wp_at_triv:
  "\<lbrace>\<top>\<rbrace> set_cap cap slot \<lbrace>\<lambda>_. cte_wp_at ((=) cap) slot\<rbrace>"
  unfolding set_cap_def
  apply (wpsimp wp: set_object_wp get_object_wp)
  apply (intro impI conjI allI)
       apply (rule cte_wp_at_cteI)
          apply fastforce
         apply clarsimp
         apply (drule set_cap_well_formed_cnode_helper[where slot=slot], simp+)
      apply (fastforce intro: cte_wp_at_tcbI simp: tcb_cap_cases_def)+
  done

lemma set_cap_silc_inv:
  "\<lbrace>(\<lambda>s. \<not> cap_points_to_label aag cap (pasObjectAbs aag (fst slot))
         \<longrightarrow> (\<exists>lslot. lslot \<in> slots_holding_overlapping_caps cap s \<and>
                      pasObjectAbs aag (fst lslot) = SilcLabel)) and
    silc_inv aag st and K (pasObjectAbs aag (fst slot) \<noteq> SilcLabel)\<rbrace>
   set_cap cap slot
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (clarsimp simp: valid_def silc_inv_def)
  apply (intro conjI impI allI)
    apply (erule use_valid)
     apply (rule hoare_vcg_ex_lift)
     apply (rule cap_table_at_lift_valid[OF set_cap_typ_at])
    apply blast
   apply (case_tac "slot = (a,ba)")
    apply (subgoal_tac "cap = capa")
     apply (simp)
     apply (erule impE)
      apply (simp add: intra_label_cap_def)
      apply (elim conjE exE)
      apply (blast dest: cte_wp_at_eqD2)
     apply (elim exE conjE)
     apply (rule_tac x=aa in exI, simp)
     apply (rule_tac x=bb in exI)
     apply (erule use_valid[OF _ set_cap_slots_holding_overlapping_caps_other[where aag=aag]])
     apply fastforce
    apply (rule cte_wp_at_eqD2)
     apply blast
    apply (drule_tac s=slot in sym, simp)
    apply (erule use_valid[OF _ set_cap_cte_wp_at_triv], rule TrueI)
   apply (drule_tac x=a in spec, drule_tac x=ba in spec, drule_tac x= capa in spec)
   apply (erule impE, rule conjI)
     apply (fastforce elim!: hoare_contrapositive[OF set_cap_neg_cte_wp_at_other, simplified])
    apply (rule_tac P="\<lambda> s. intra_label_cap aag (a, ba) s" in hoare_contrapositive)
      apply (rule intra_label_cap_pres)
      apply (erule set_cap_neg_cte_wp_at_other)
     apply (erule conjE, assumption)
    apply assumption
   apply clarsimp
   apply (rule_tac x=aa in exI, simp)
   apply (rule_tac x=bb in exI)
   apply (erule use_valid[OF _ set_cap_slots_holding_overlapping_caps_other[where aag=aag]])
   apply fastforce
   apply (erule use_valid[OF _ set_cap_rvk_cdt_ct_ms(4)],simp)
  apply (simp add: silc_dom_equiv_def)
  apply (rule equiv_forI)
  apply (erule use_valid)
  unfolding set_cap_def
  apply (wp set_object_wp get_object_wp hoare_weak_lift_imp | simp add: split_def | wpc)+
  apply clarsimp
  apply (rule conjI)
   apply fastforce
  apply (fastforce elim: equiv_forE)
  done

lemma slots_holding_overlapping_caps_hold_caps:
  "slot \<in> slots_holding_overlapping_caps cap s \<Longrightarrow> \<exists>cap'. cte_wp_at ((=) cap') slot s"
  by (fastforce simp: slots_holding_overlapping_caps_def get_cap_cte_wp_at')

crunches set_original
  for silc_inv[wp]: "silc_inv aag st"
  (wp: silc_inv_triv wp_del:set_original_wp)

lemma nonempty_refs:
  "\<not> cap_points_to_label aag cap l \<Longrightarrow> obj_refs cap \<noteq> {} \<or> cap_irqs cap \<noteq> {}"
  by (auto simp: cap_points_to_label_def)

lemma set_cdt_silc_inv:
  "\<lbrace>silc_inv aag st and K (all_children (\<lambda>x. pasObjectAbs aag (fst x) = SilcLabel) m)\<rbrace>
   set_cdt m
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  apply (simp add: set_cdt_def)
  apply wp
  apply (simp add: intra_label_cap_def slots_holding_overlapping_caps_def
                   silc_inv_def silc_dom_equiv_def equiv_for_def)
  done

lemma update_cdt_silc_inv:
  "\<lbrace>silc_inv aag st and (\<lambda>s. all_children (\<lambda>x. pasObjectAbs aag (fst x) = SilcLabel) (f (cdt s)))\<rbrace>
   update_cdt f
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  apply (simp add: update_cdt_def)
  apply (wp set_cdt_silc_inv | simp)+
  done

lemma silc_inv_all_children:
  "silc_inv aag st s \<Longrightarrow> all_children (\<lambda>x. pasObjectAbs aag (fst x) = SilcLabel) (cdt s)"
  by (simp add: silc_inv_def)

lemma cap_irqs_max_free_index_update[simp]:
  "cap_irqs (max_free_index_update cap) = cap_irqs cap"
  apply (case_tac cap, simp_all add: free_index_update_def)
  done

lemma cap_points_to_label_max_free_index_update[simp]:
  "cap_points_to_label aag (max_free_index_update cap) l =  cap_points_to_label aag cap l"
  apply (simp add: cap_points_to_label_def)
  done

crunches set_untyped_cap_as_full
  for silc_inv': "silc_inv aag st"
  (wp: set_cap_silc_inv)

lemmas set_untyped_cap_as_full_silc_inv[wp] = set_untyped_cap_as_full_silc_inv'[simplified]

lemma set_untyped_cap_as_full_slots_holding_overlapping_caps_other:
  "\<lbrace>\<lambda>s. x \<in> slots_holding_overlapping_caps capa s \<and>
        pasObjectAbs aag (fst x) \<noteq> pasObjectAbs aag (fst slot)\<rbrace>
   set_untyped_cap_as_full src_cap cap slot
   \<lbrace>\<lambda>_ s. x \<in> slots_holding_overlapping_caps capa s\<rbrace>"
  unfolding set_untyped_cap_as_full_def
  apply (rule hoare_pre)
   apply (wp set_cap_slots_holding_overlapping_caps_other[where aag=aag])
  apply clarsimp
  done

lemma is_derived_overlaps':
  "\<lbrakk> is_derived (cdt s) slot cap cap';
     (obj_refs cap' \<noteq> {} \<or> cap_irqs cap' \<noteq> {}) \<or>
     (obj_refs cap \<noteq> {} \<or> cap_irqs cap \<noteq> {}) \<rbrakk>
     \<Longrightarrow> obj_refs cap \<inter> obj_refs cap' \<noteq> {} \<or>
         cap_irqs cap \<inter> cap_irqs cap' \<noteq> {}"
  apply (simp add: is_derived_def)
  apply (case_tac cap', simp_all add: cap_master_cap_def split: cap.splits)
  apply (fastforce dest: master_arch_cap_obj_refs)
  done

lemma is_derived_overlaps:
  "\<lbrakk> cte_wp_at (is_derived (cdt s) slot cap) slot s;
     obj_refs cap \<noteq> {} \<or> cap_irqs cap \<noteq> {} \<rbrakk>
     \<Longrightarrow> slot \<in> slots_holding_overlapping_caps cap s"
  apply (simp add: slots_holding_overlapping_caps_def get_cap_cte_wp_at')
  apply (drule cte_wp_at_norm)
  apply (erule exE, rename_tac cap')
  apply (rule_tac x=cap' in exI)
  apply (blast dest: is_derived_overlaps')
  done

lemma is_derived_overlaps2:
  "\<lbrakk> cte_wp_at ((=) cap') slot s;
     is_derived (cdt s) slot cap cap';
     obj_refs cap' \<noteq> {} \<or> cap_irqs cap' \<noteq> {} \<rbrakk>
     \<Longrightarrow> slot \<in> slots_holding_overlapping_caps cap' s"
  apply (simp add: slots_holding_overlapping_caps_def get_cap_cte_wp_at')
  apply (blast dest: cte_wp_at_norm is_derived_overlaps')
  done

lemma disj_dup: "A \<and> B \<and> C \<and> C'\<Longrightarrow> A \<and> B \<and> C \<and> A \<and> B \<and> C'"
  by simp


context FinalCaps_1 begin

lemma weak_derived_overlaps':
  "\<lbrakk> weak_derived cap cap'; obj_refs cap \<noteq> {} \<or> cap_irqs cap \<noteq> {} \<rbrakk>
     \<Longrightarrow> obj_refs cap \<inter> obj_refs cap' \<noteq> {} \<or>
         cap_irqs cap \<inter> cap_irqs cap' \<noteq> {}"
  apply (simp add: weak_derived_def)
  apply (erule disjE)
   prefer 2
   apply simp
  apply (simp add: copy_of_def split: if_split_asm add: same_object_as_def split: cap.splits)
       apply ((case_tac cap; simp)+)[5]
  apply (clarsimp simp: aobj_ref_same_aobject)
  done

lemma weak_derived_overlaps:
  "\<lbrakk> cte_wp_at (weak_derived cap) slot s;
     obj_refs cap \<noteq> {} \<or> cap_irqs cap \<noteq> {} \<rbrakk>
     \<Longrightarrow> slot \<in> slots_holding_overlapping_caps cap s"
  apply (simp add: slots_holding_overlapping_caps_def get_cap_cte_wp_at')
  apply (drule cte_wp_at_norm)
  apply (erule exE, rename_tac cap')
  apply (rule_tac x=cap' in exI)
  apply (blast dest: weak_derived_overlaps')
  done

lemma not_cap_points_to_label_transfers_across_overlapping_caps:
  "\<lbrakk> \<not> cap_points_to_label aag cap (pasObjectAbs aag (fst slot));
     slot \<in> slots_holding_overlapping_caps cap s \<rbrakk>
     \<Longrightarrow> \<not> intra_label_cap aag slot s"
  apply (simp add: slots_holding_overlapping_caps_def get_cap_cte_wp_at')
  apply (elim exE conjE, rename_tac cap')
  apply (simp add: intra_label_cap_def)
  apply (rule_tac x=cap' in exI)
  apply (auto simp: cap_points_to_label_def
              dest: caps_ref_single_objects caps_ref_single_irqs caps_ref_either_an_object_or_irq)
  done

lemma overlapping_transfers_across_overlapping_caps:
  "\<lbrakk> slot \<in> slots_holding_overlapping_caps cap s;
     cte_wp_at ((=) cap') slot s;
     lslot \<in> slots_holding_overlapping_caps cap' s \<rbrakk>
     \<Longrightarrow> lslot \<in> slots_holding_overlapping_caps cap s"
  apply (simp add: slots_holding_overlapping_caps_def get_cap_cte_wp_at')
  apply (elim exE conjE)
  apply (drule (1) cte_wp_at_eqD2)+
  apply clarsimp
  apply (rename_tac lcap)
  apply (rule_tac x=lcap in exI)
  apply (auto dest: caps_ref_single_objects caps_ref_single_irqs caps_ref_either_an_object_or_irq)
  done

lemma overlapping_slots_have_labelled_overlapping_caps:
  "\<lbrakk> slot \<in> slots_holding_overlapping_caps cap s; silc_inv aag st s;
     \<not> cap_points_to_label aag cap (pasObjectAbs aag (fst slot)) \<rbrakk>
     \<Longrightarrow> (\<exists>lslot. lslot \<in> slots_holding_overlapping_caps cap s \<and>
                  pasObjectAbs aag (fst lslot) = SilcLabel)"
  apply (drule not_cap_points_to_label_transfers_across_overlapping_caps)
   apply assumption
  apply (frule slots_holding_overlapping_caps_hold_caps)
  apply (erule exE, rename_tac cap')
  apply (drule silc_invD)
    apply assumption
   apply assumption
  apply (blast dest: overlapping_transfers_across_overlapping_caps)
  done

lemma cap_swap_silc_inv:
  "\<lbrace>silc_inv aag st and cte_wp_at (weak_derived cap) slot and
        cte_wp_at (weak_derived cap') slot' and
        K(pasObjectAbs aag (fst slot) = pasObjectAbs aag (fst slot') \<and>
         pasObjectAbs aag (fst slot') \<noteq> SilcLabel)\<rbrace>
      cap_swap cap slot cap' slot'
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  apply (rule hoare_gen_asm)
  unfolding cap_swap_def
  apply (rule hoare_pre)
  apply (wp set_cap_silc_inv hoare_vcg_ex_lift hoare_weak_lift_imp
            set_cap_slots_holding_overlapping_caps_other[where aag=aag] set_cdt_silc_inv
        | simp  split del: if_split)+
  apply (rule conjI)
   apply (rule impI, elim conjE)
   apply (drule weak_derived_overlaps)
    apply (erule nonempty_refs)
   apply (drule overlapping_slots_have_labelled_overlapping_caps)
     apply assumption
    apply simp
   apply fastforce
  apply (rule conjI)
  apply (rule impI, elim conjE)
  apply (drule weak_derived_overlaps, erule nonempty_refs)
  apply (drule overlapping_slots_have_labelled_overlapping_caps)
    apply assumption
   apply simp
  apply fastforce
  apply (elim conjE)
  apply (drule silc_inv_all_children)
  apply simp
  apply (intro impI conjI)
  by (fastforce simp: all_children_def simp del: split_paired_All
     | simp add: all_children_def del: split_paired_All)+ (*slow*)

lemma cap_move_silc_inv:
  "\<lbrace>silc_inv aag st and cte_wp_at (weak_derived cap) slot and
       K(pasObjectAbs aag (fst slot) = pasObjectAbs aag (fst slot') \<and>
         pasObjectAbs aag (fst slot') \<noteq> SilcLabel)\<rbrace>
     cap_move cap slot slot'
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  apply (rule hoare_gen_asm)
  unfolding cap_move_def
  apply (rule hoare_pre)
  apply (wp set_cap_silc_inv hoare_vcg_ex_lift
            set_cap_slots_holding_overlapping_caps_other[where aag=aag]
            set_cdt_silc_inv hoare_weak_lift_imp
        | simp)+
  apply (rule conjI)
   apply (fastforce simp: cap_points_to_label_def)
  apply (rule conjI)
  apply (rule impI, elim conjE)
  apply (drule weak_derived_overlaps)
   apply (erule nonempty_refs)
  apply (drule overlapping_slots_have_labelled_overlapping_caps)
    apply assumption
   apply simp
  apply fastforce
  apply (elim conjE)
  apply (drule silc_inv_all_children)
  apply (fastforce simp: all_children_def simp del: split_paired_All)
  done

lemma slots_holding_overlapping_caps_max_free_index_update[simp]:
  "slots_holding_overlapping_caps (max_free_index_update cap) s =
   slots_holding_overlapping_caps cap s"
  by (simp add: slots_holding_overlapping_caps_def)

lemma cap_insert_silc_inv:
  "\<lbrace>silc_inv aag st and (\<lambda>s. cte_wp_at (is_derived (cdt s) slot cap) slot s) and
    K (pasObjectAbs aag (fst slot) = pasObjectAbs aag (fst slot') \<and>
       pasObjectAbs aag (fst slot') \<noteq> SilcLabel)\<rbrace>
   cap_insert cap slot slot'
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  unfolding cap_insert_def
  (* The order here matters. The first two need to be first. *)
  apply (wp assert_wp hoare_weak_lift_imp_conj set_cap_silc_inv hoare_vcg_ex_lift
            set_untyped_cap_as_full_slots_holding_overlapping_caps_other[where aag=aag]
            get_cap_wp update_cdt_silc_inv | simp | wp (once) hoare_drop_imps)+
  apply clarsimp
  apply (rule disj_dup)
  apply (rule conjI)
   apply (rule impI)
   apply (drule is_derived_overlaps)
    apply (erule nonempty_refs)
   apply (drule overlapping_slots_have_labelled_overlapping_caps)
     apply assumption
    apply simp
   apply fastforce
  apply (rule conjI)
  apply (rule impI)
  apply (drule cte_wp_at_norm)
  apply (elim conjE exE)
  apply (drule (1) cte_wp_at_eqD2)
  apply simp
  apply (drule_tac cap'=capa in is_derived_overlaps2)
    apply assumption
   apply (erule nonempty_refs)
  apply (drule overlapping_slots_have_labelled_overlapping_caps)
    apply assumption
   apply simp
  apply fastforce
  apply (drule silc_inv_all_children)
  apply (rule conjI)
  apply (fastforce simp: all_children_def simp del: split_paired_All)+
  done

end


lemma cte_wp_at_eq:
  assumes a: "\<And>cap. \<lbrace>cte_wp_at ((=) cap) slot\<rbrace> f \<lbrace>\<lambda>_. cte_wp_at ((=) cap) slot\<rbrace>"
  shows "\<lbrace>cte_wp_at P slot\<rbrace> f \<lbrace>\<lambda>_. cte_wp_at P slot\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (drule cte_wp_at_norm)
  apply (elim exE conjE, rename_tac cap)
  apply (drule use_valid)
    apply (rule a)
   apply assumption
  apply (simp add: cte_wp_at_def)
  done

lemma set_simple_ko_silc_inv[wp]:
  "\<lbrace>silc_inv aag st\<rbrace>
   set_simple_ko f ptr ep
   \<lbrace>\<lambda> _. silc_inv aag st\<rbrace>"
  unfolding set_simple_ko_def
  apply (rule silc_inv_pres)
    apply (wpsimp wp: set_object_wp_strong get_object_wp simp: obj_at_def)
    apply (fastforce simp: silc_inv_def obj_at_def is_cap_table_def)
   apply (wpsimp wp: set_object_wp get_object_wp)
  apply (wpsimp wp: set_object_wp_strong get_object_wp simp: obj_at_def)
  apply (case_tac "ptr = fst (a,b)")
   apply (fastforce elim: cte_wp_atE simp: obj_at_def)
  apply (fastforce elim: cte_wp_atE intro: cte_wp_at_cteI cte_wp_at_tcbI)
  done

crunches deleted_irq_handler
  for kheap[wp]: "\<lambda>s. P (kheap s x)"

crunches deleted_irq_handler
  for silc_inv[wp]: "silc_inv aag st"
  (wp: silc_inv_triv)

lemma (in is_extended') not_cte_wp_at[wp]: "I (\<lambda>s. \<not> cte_wp_at P t s)" by (rule lift_inv,simp)

lemma set_thread_state_silc_inv[wp]:
  "\<lbrace>silc_inv aag st\<rbrace>
   set_thread_state tptr ts
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  unfolding set_thread_state_def
  apply (rule silc_inv_pres)
    apply (wp set_object_wp | simp split del: if_split)+
    apply (simp split: kernel_object.splits)
    apply (rule impI | simp)+
    apply (fastforce simp: silc_inv_def dest: get_tcb_SomeD simp: obj_at_def is_cap_table_def)
   apply (wp set_object_wp | simp)+
  apply (case_tac "tptr = fst slot")
   apply (clarsimp split: kernel_object.splits)
   apply (erule notE)
   apply (erule cte_wp_atE)
    apply (fastforce simp: obj_at_def)
   apply (drule get_tcb_SomeD)
   apply (rule cte_wp_at_tcbI)
     apply (simp)
    apply assumption
   apply (fastforce simp: tcb_cap_cases_def split: if_splits)
  apply (fastforce elim: cte_wp_atE intro: cte_wp_at_cteI cte_wp_at_tcbI)
  done

lemma set_bound_notification_silc_inv[wp]:
  "\<lbrace>silc_inv aag st\<rbrace>
   set_bound_notification tptr ntfn
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  unfolding set_bound_notification_def
  apply (rule silc_inv_pres)
    apply (wp set_object_wp|simp split del: if_split)+
    apply (simp split: kernel_object.splits)
    apply (rule impI | simp)+
    apply (fastforce simp: silc_inv_def dest: get_tcb_SomeD simp: obj_at_def is_cap_table_def)
   apply (wp set_object_wp | simp)+
  apply (case_tac "tptr = fst slot")
   apply (clarsimp split: kernel_object.splits)
   apply (erule notE)
   apply (erule cte_wp_atE)
    apply (fastforce simp: obj_at_def)
   apply (drule get_tcb_SomeD)
   apply (rule cte_wp_at_tcbI)
     apply (simp)
    apply assumption
   apply (fastforce simp: tcb_cap_cases_def split: if_splits)
  apply (fastforce elim: cte_wp_atE intro: cte_wp_at_cteI cte_wp_at_tcbI)
  done

crunches fast_finalise, unbind_notification
  for silc_inv[wp]: "silc_inv aag st"
  (ignore: set_object wp: crunch_wps simp: crunch_simps)

lemma slots_holding_overlapping_caps_lift:
  assumes a: "\<And>P Q slot. \<lbrace>\<lambda>s. Q (cte_wp_at P slot s)\<rbrace> f \<lbrace>\<lambda>_ s. Q (cte_wp_at P slot s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. P (slots_holding_overlapping_caps cap s)\<rbrace>
         f
         \<lbrace>\<lambda>_ s. P (slots_holding_overlapping_caps cap s)\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (subgoal_tac "slots_holding_overlapping_caps cap b =
                      slots_holding_overlapping_caps cap s", simp)
  apply (clarsimp simp: slots_holding_overlapping_caps_def2 ctes_wp_at_def)
  apply (rule Collect_cong)
  apply (erule use_valid[OF _ a])
  apply (rule refl)
  done

crunches set_original
  for cte_wp_at'[wp]: "\<lambda>s. Q (cte_wp_at P slot s)"
  (wp_del:set_original_wp)

lemma slots_holding_overlapping_caps_exst_update[simp]:
  "slots_holding_overlapping_caps cap (trans_state f s) =
   slots_holding_overlapping_caps cap s"
  by (simp add: slots_holding_overlapping_caps_def2 ctes_wp_at_def)

crunches set_cdt
  for cte_wp_at'[wp]: "\<lambda>s. Q (cte_wp_at P slot s)"

lemma slots_holding_overlapping_caps_is_original_cap_update[simp]:
  "slots_holding_overlapping_caps cap (s\<lparr>is_original_cap := X\<rparr>) =
   slots_holding_overlapping_caps cap s"
  by (simp add: slots_holding_overlapping_caps_def2 ctes_wp_at_def)

lemma intra_label_cap_is_original_cap[simp]:
  "intra_label_cap aag slot (s\<lparr>is_original_cap := X\<rparr>) = intra_label_cap aag slot s"
  by (simp add: intra_label_cap_def)

lemma silc_inv_is_original_cap[simp]:
  "silc_inv aag st (s\<lparr>is_original_cap := X\<rparr>) = silc_inv aag st s"
  by (simp add: silc_inv_def silc_dom_equiv_def equiv_for_def)

lemma thread_set_silc_inv:
  assumes cap_inv: "\<And>tcb. \<forall>(getF, v) \<in> ran tcb_cap_cases. getF (f tcb) = getF tcb"
  shows "\<lbrace>silc_inv aag st\<rbrace> thread_set f t \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  apply (rule silc_inv_pres)
    apply (subst thread_set_def)
    apply (wp set_object_wp)
    apply (simp split: kernel_object.splits)
    apply (rule impI | simp)+
    apply (fastforce simp: silc_inv_def dest: get_tcb_SomeD simp: obj_at_def is_cap_table_def)
   apply (rule thread_set_Pmdb)
  apply (rule thread_set_cte_wp_at_trivial[OF cap_inv])
  done

lemma thread_set_tcb_fault_update_silc_inv[wp]:
  "\<lbrace>silc_inv aag st\<rbrace>
   thread_set (tcb_fault_update blah) t
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  by (rule thread_set_silc_inv; simp add: tcb_cap_cases_def)

(* FIXME MOVE *)
lemma reply_masters_mdbE:
  assumes rmm: "reply_masters_mdb m cs"
  assumes csr: "cs ptr = Some (ReplyCap t True rights)"
  obtains "m ptr = None"
      and "\<And>ptr'. ptr' \<in> descendants_of ptr m \<Longrightarrow> \<exists>R. cs ptr' = Some(ReplyCap t False R)"
  using rmm csr unfolding reply_masters_mdb_def by force

crunches cancel_signal
  for silc_inv[wp]: "silc_inv aag st"


context FinalCaps_1 begin

lemma empty_slot_silc_inv:
  "\<lbrace>silc_inv aag st and K (pasObjectAbs aag (fst slot) \<noteq> SilcLabel)\<rbrace>
   empty_slot slot free_irq
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  unfolding empty_slot_def post_cap_deletion_def
  apply (wp set_cap_silc_inv hoare_vcg_all_lift hoare_vcg_ex_lift
            slots_holding_overlapping_caps_lift get_cap_wp
            set_cdt_silc_inv dxo_wp_weak hoare_drop_imps
         | wpc | simp del: empty_slot_extended.dxo_eq)+
  apply (clarsimp simp: cap_points_to_label_def)
  apply (drule silc_inv_all_children)
  apply (fastforce simp: all_children_def simp del: split_paired_All)
  done

lemma cap_delete_one_silc_inv:
  "\<lbrace>silc_inv aag st and K (pasObjectAbs aag (fst slot) \<noteq> SilcLabel)\<rbrace>
   cap_delete_one slot
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  unfolding cap_delete_one_def
  by (wpsimp wp: unless_wp empty_slot_silc_inv get_cap_wp)

lemma cap_delete_one_silc_inv_subject:
  "\<lbrace>silc_inv aag st and K (is_subject aag (fst slot))\<rbrace>
   cap_delete_one slot
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  unfolding cap_delete_one_def
  apply (wpsimp wp: unless_wp empty_slot_silc_inv get_cap_wp)
  unfolding silc_inv_def
  by simp

lemma reply_cancel_ipc_silc_inv:
  "\<lbrace>silc_inv aag st and valid_mdb and pas_refined aag and K (is_subject aag t)\<rbrace>
   reply_cancel_ipc t
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  unfolding reply_cancel_ipc_def
  apply (wp cap_delete_one_silc_inv hoare_vcg_if_lift | simp)+
   apply wps
   apply (wp hoare_weak_lift_imp hoare_vcg_all_lift hoare_vcg_ball_lift)
  apply clarsimp
  apply (rename_tac b a)
  apply (frule(1) descendants_of_owned_or_transferable, force, force, elim disjE)
   apply (clarsimp simp add:silc_inv_def)
  apply (case_tac "cdt s (a,b)")
   apply (fastforce dest: descendants_of_NoneD)
  apply (elim is_transferable.cases)
    apply (fastforce dest: mdb_cte_atD valid_mdb_mdb_cte_at simp:  cte_wp_at_caps_of_state)
   apply (fastforce dest: mdb_cte_atD valid_mdb_mdb_cte_at simp:  cte_wp_at_caps_of_state)
  apply (erule(1) silc_inv_no_transferableD')
  apply (force simp add:cte_wp_at_caps_of_state)
  done

lemma cancel_ipc_silc_inv:
  "\<lbrace>silc_inv aag st and valid_mdb and pas_refined aag and K (is_subject aag t)\<rbrace>
   cancel_ipc t
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  unfolding cancel_ipc_def
  apply (wp get_simple_ko_wp reply_cancel_ipc_silc_inv get_thread_state_inv hoare_vcg_all_lift
         | wpc
         | simp (no_asm) add: blocked_cancel_ipc_def get_ep_queue_def get_blocking_object_def
         | wp (once) hoare_drop_imps)+
  apply auto
  done

end


lemma cancel_ipc_indirect_silc_inv:
  "\<lbrace>silc_inv aag st and st_tcb_at receive_blocked t\<rbrace>
    cancel_ipc t
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  unfolding cancel_ipc_def
  apply (rule bind_wp[OF _ gts_sp])
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp: st_tcb_def2 receive_blocked_def)
  apply (simp add: blocked_cancel_ipc_def split: thread_state.splits)
  apply wpsimp
  done

lemma intra_label_cap_machine_state[simp]:
  "intra_label_cap aag slot (s\<lparr>machine_state := X\<rparr>) = intra_label_cap aag slot s"
  by (simp add: intra_label_cap_def)

lemma slots_holding_overlapping_caps_machine_state[simp]:
  "slots_holding_overlapping_caps cap (s\<lparr>machine_state := X\<rparr>) = slots_holding_overlapping_caps cap s"
  by (simp add: slots_holding_overlapping_caps_def2 ctes_wp_at_def)

lemma silc_inv_machine_state[simp]:
  "silc_inv aag st (s\<lparr>machine_state := X\<rparr>) = silc_inv aag st s"
  by (simp add: silc_inv_def silc_dom_equiv_def equiv_for_def)

lemma intra_label_cap_arch_state[simp]:
  "intra_label_cap aag slot (s\<lparr>arch_state := X\<rparr>) = intra_label_cap aag slot s"
  by (simp add: intra_label_cap_def)

lemma slots_holding_overlapping_caps_arch_state[simp]:
  "slots_holding_overlapping_caps cap (s\<lparr>arch_state := X\<rparr>) = slots_holding_overlapping_caps cap s"
  by (simp add: slots_holding_overlapping_caps_def2 ctes_wp_at_def)

lemma silc_inv_arch_state[simp]:
  "silc_inv aag st (s\<lparr>arch_state := X\<rparr>) = silc_inv aag st s"
  by (simp add: silc_inv_def silc_dom_equiv_def equiv_for_def)

(* FIXME MOVE *)
lemma is_subject_not_silc_inv:
  "\<lbrakk>silc_inv aag st s; is_subject aag ptr\<rbrakk> \<Longrightarrow> pasObjectAbs aag ptr \<noteq> SilcLabel"
   using silc_inv_not_subject by fastforce

lemma update_restart_pc_silc_inv[wp]:
  "\<lbrace>silc_inv aag st\<rbrace> update_restart_pc t \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  unfolding update_restart_pc_def
  apply (rule silc_inv_pres)
    apply (simp add: as_user_def)
    apply (wpsimp simp: set_object_wp)
       apply (wp set_object_wp)+
    apply clarsimp+
    apply (fastforce simp: silc_inv_def dest: get_tcb_SomeD simp: obj_at_def is_cap_table_def)
   apply wp+
  done

lemma validE_validE_R':
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>R\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, -"
  apply (rule validE_validE_R)
  apply (erule hoare_strengthen_postE)
  by auto

lemma finalise_cap_ret_subset_cap_irqs:
  "\<lbrace>\<lambda>s. (cap_irqs cap) = X\<rbrace>
   finalise_cap cap blah
   \<lbrace>\<lambda>rv s :: det_state. (cap_irqs (fst rv)) \<subseteq> X\<rbrace>"
  apply (cases cap)
  by (wp arch_finalise_cap_rv | simp add: o_def split del: if_split | simp split: if_split)+

lemma finalise_cap_ret_subset_obj_refs:
  "\<lbrace>\<lambda>s. obj_refs cap = X\<rbrace>
   finalise_cap cap blah
   \<lbrace>\<lambda>rv s :: det_state. (obj_refs (fst rv)) \<subseteq> X\<rbrace>"
  apply (cases cap)
  by (wp arch_finalise_cap_rv | simp add: o_def split del: if_split | simp split: if_split)+

lemma finalise_cap_ret_intra_label_cap:
  "\<lbrace>\<lambda>s. cap_points_to_label aag cap l\<rbrace>
   finalise_cap cap blah
   \<lbrace>\<lambda>rv s :: det_state. cap_points_to_label aag (fst rv) l\<rbrace>"
  apply (clarsimp simp: cap_points_to_label_def valid_def)
  apply (rule conjI)
   apply (erule ball_subset)
   apply (drule use_valid[OF _ finalise_cap_ret_subset_obj_refs])
    apply (rule refl)
   apply simp
  apply (erule ball_subset)
  apply (drule use_valid[OF _ finalise_cap_ret_subset_cap_irqs])
   apply (rule refl)
  by simp

lemma silc_inv_preserves_silc_dom_caps:
  "\<lbrakk> silc_inv aag st s; silc_inv aag st s';
     pasObjectAbs aag (fst lslot) = SilcLabel;
     lslot \<in> FinalCaps.slots_holding_overlapping_caps cap s \<rbrakk>
     \<Longrightarrow> lslot \<in> FinalCaps.slots_holding_overlapping_caps cap s'"
  apply (clarsimp simp: slots_holding_overlapping_caps_def get_cap_cte_wp_at')
  apply (rule_tac x=cap' in exI)
  apply simp
  apply (subst (asm) cte_wp_at_pspace'[where s'=s'])
   apply (fastforce simp: silc_inv_def silc_dom_equiv_def equiv_for_def)
  apply assumption
  done


context FinalCaps_1 begin

lemma finalise_cap_silc_inv:
  "\<lbrace>silc_inv aag st and pspace_aligned and valid_vspace_objs and valid_arch_state
                    and valid_mdb and pas_refined aag and K (pas_cap_cur_auth aag cap)\<rbrace>
   finalise_cap cap final
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  apply (case_tac cap)
             apply (wp cancel_ipc_silc_inv | simp split del: if_split add: suspend_def| clarsimp)+
       apply (fastforce simp: aag_cap_auth_Thread)
      apply (wp | simp split del: if_split | clarsimp split del: if_split)+
      apply (rule hoare_pre)
       apply (wp cap_delete_one_silc_inv
              | simp add: deleting_irq_handler_def
              | strengthen is_subject_not_silc_inv)+
    apply (fastforce simp: aag_cap_auth_def cap_links_irq_def elim: aag_Control_into_owns_irq)
   apply (wp | simp split del: if_split)+
  done

lemma finalise_cap_ret_is_silc:
  "\<lbrace>silc_inv aag st and pspace_aligned and valid_vspace_objs and valid_arch_state and valid_mdb
                    and cte_wp_at ((=) cap) slot and pas_refined aag and K (pas_cap_cur_auth aag cap)\<rbrace>
   finalise_cap cap blah
   \<lbrace>\<lambda>rvb s. \<not> cap_points_to_label aag (fst rvb) (pasObjectAbs aag (fst slot))
            \<longrightarrow> (\<exists>lslot. lslot \<in> slots_holding_overlapping_caps (fst rvb) s \<and>
                         pasObjectAbs aag (fst lslot) = SilcLabel)\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (rename_tac a b s')
  apply (cut_tac aag1=aag and r="(a,b)" and l1="pasObjectAbs aag (fst slot)"
              in hoare_contrapositive[OF finalise_cap_ret_intra_label_cap])
    apply simp
   apply assumption
  apply (frule use_valid[OF _ finalise_cap_silc_inv[where st=st]])
   apply simp
  apply (frule_tac s=s in silc_invD)
    apply assumption
   apply (fastforce simp: intra_label_cap_def)
  apply (simp, elim exE conjE)
  apply (rename_tac la lb)
  apply (rule_tac x=la in exI, simp)
  apply (rule_tac x=lb in exI)
  apply (drule_tac lslot="(la,lb)" in silc_inv_preserves_silc_dom_caps, simp+)
  apply (drule nonempty_refs)+
  apply (erule disjE[where P="obj_refs cap \<noteq> {}"])
   apply (subgoal_tac "cap_irqs cap = {} \<and> cap_irqs a = {}")
    apply (clarsimp simp: slots_holding_overlapping_caps_def get_cap_cte_wp_at')
    apply (rename_tac cap'a)
    apply (rule_tac x=cap'a in exI)
    apply simp
    apply (subgoal_tac "\<exists>x. obj_refs cap = {x} \<and> obj_refs a = {x}")
     apply blast
    apply (erule nonemptyE)
    apply (rename_tac x)
    apply (rule_tac x=x in exI)
    apply (subgoal_tac "obj_refs a \<subseteq> obj_refs cap")
     apply (drule (1) subsetD)
     apply (blast dest: caps_ref_single_objects)
    apply (fastforce dest: use_valid[OF _ finalise_cap_ret_subset_obj_refs])
   apply (fastforce dest: caps_ref_either_an_object_or_irq
                          use_valid[OF _ finalise_cap_ret_subset_cap_irqs])
  apply (subgoal_tac "obj_refs cap = {} \<and> obj_refs a = {}")
   apply (clarsimp simp: slots_holding_overlapping_caps_def get_cap_cte_wp_at')
   apply (rename_tac cap'a)
   apply (rule_tac x=cap'a in exI)
   apply simp
   apply (subgoal_tac "\<exists>x. cap_irqs cap = {x} \<and> cap_irqs a = {x}")
    apply blast
   apply (erule nonemptyE)
   apply (rename_tac x)
   apply (rule_tac x=x in exI)
   apply (subgoal_tac "cap_irqs a \<subseteq> cap_irqs cap")
    apply (drule (1) subsetD)
    apply (blast dest: caps_ref_single_irqs)
   apply (fastforce dest: use_valid[OF _ finalise_cap_ret_subset_cap_irqs])
  apply (fastforce dest: caps_ref_either_an_object_or_irq'
                         use_valid[OF _ finalise_cap_ret_subset_obj_refs])
  done

end


lemma arch_finalise_cap_ret:
  "(rv, s') \<in> fst (arch_finalise_cap arch_cap final (s :: det_state)) \<Longrightarrow> rv = (NullCap, NullCap)"
  apply (erule use_valid)
   apply (wpsimp wp: arch_finalise_cap_rv)+
  done

lemma finalise_cap_ret:
  "(rv, s') \<in> fst (finalise_cap cap final (s :: det_state))
   \<Longrightarrow> case (fst rv) of NullCap \<Rightarrow> True | Zombie ptr bits n \<Rightarrow> True | _ \<Rightarrow> False"
  apply (case_tac cap, simp_all add: return_def)
       apply (fastforce simp: liftM_def when_def bind_def return_def split: if_split_asm)+
  apply (drule arch_finalise_cap_ret)
  apply simp
  done

lemma finalise_cap_ret_is_subject:
  "\<lbrace>K ((is_cnode_cap cap \<or> is_thread_cap cap \<or> is_zombie cap) \<longrightarrow> is_subject aag (obj_ref_of cap))\<rbrace>
   finalise_cap cap is_final
   \<lbrace>\<lambda>rv _ :: det_state. case (fst rv) of Zombie ptr bits n \<Rightarrow> is_subject aag (obj_ref_of (fst rv))
                                                       | _ \<Rightarrow> True\<rbrace>"
  including classic_wp_pre
  apply (case_tac cap, simp_all add: is_zombie_def)
             apply (wp | simp add: comp_def | rule impI | rule conjI)+
  apply (fastforce simp: valid_def dest: arch_finalise_cap_ret)
  done

lemma finalise_cap_ret_is_subject':
  "\<lbrace>K (is_cnode_cap rv \<or> is_thread_cap rv \<or> is_zombie rv \<longrightarrow> is_subject aag (obj_ref_of rv))\<rbrace>
   finalise_cap rv rva
   \<lbrace>\<lambda>rv s :: det_state. (is_zombie (fst rv) \<longrightarrow> is_subject aag (obj_ref_of (fst rv)))\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (drule use_valid[OF _ finalise_cap_ret_is_subject[where aag=aag]])
   apply simp
  apply (case_tac a, simp_all add: is_zombie_def)
  done

lemma get_cap_weak_derived[wp]:
  "\<lbrace>\<top>\<rbrace> get_cap slot \<lbrace>\<lambda>rv s. cte_wp_at (weak_derived rv) slot s\<rbrace>"
  unfolding get_cap_def
  apply (wp get_object_wp | simp add: split_def | wpc)+
  apply safe
   apply (rule cte_wp_at_cteI)
      apply (fastforce simp: obj_at_def)
     apply assumption
    apply assumption
   apply simp
  apply (clarsimp simp: tcb_cnode_map_tcb_cap_cases)
  apply (rule cte_wp_at_tcbI)
    apply (fastforce simp: obj_at_def)
   apply assumption
  apply simp
  done

lemma get_thread_cap_ret_is_subject:
  "\<lbrace>(pas_refined aag) and K (is_subject aag (fst slot))\<rbrace>
   get_cap slot
   \<lbrace>\<lambda>rv s. is_thread_cap rv \<longrightarrow> (is_subject aag (obj_ref_of rv))\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (frule get_cap_det)
  apply (drule_tac f=fst in arg_cong)
  apply (subst (asm) fst_conv)
  apply (drule in_get_cap_cte_wp_at[THEN iffD1])
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (rule caps_of_state_pasObjectAbs_eq)
      apply (blast intro: sym)
     apply (fastforce simp: cap_auth_conferred_def split: cap.split)
    apply assumption+
  apply (case_tac a, simp_all)
  done

lemma get_zombie_ret_is_subject:
  "\<lbrace>pas_refined aag and K (is_subject aag (fst slot))\<rbrace>
   get_cap slot
   \<lbrace>\<lambda>rv s. is_zombie rv \<longrightarrow> (is_subject aag (obj_ref_of rv))\<rbrace>"
  apply (clarsimp simp: valid_def is_zombie_def)
  apply (frule get_cap_det)
  apply (drule_tac f=fst in arg_cong)
  apply (subst (asm) fst_conv)
  apply (drule in_get_cap_cte_wp_at[THEN iffD1])
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (rule caps_of_state_pasObjectAbs_eq)
      apply (blast intro: sym)
     apply (fastforce simp: cap_auth_conferred_def split: cap.split)
    apply assumption+
  apply (case_tac a, simp_all)
  done

lemma ran_caps_of_state_cte_wp_at:
 "(\<forall>cap \<in> ran (caps_of_state s). P cap) \<Longrightarrow> (\<forall>cap. cte_wp_at ((=) cap) slot s \<longrightarrow> P cap)"
  by (fastforce simp: cte_wp_at_caps_of_state)

declare if_weak_cong[cong]

lemma finalise_cap_ret':
  "\<lbrace>\<top>\<rbrace> finalise_cap cap final \<lbrace>\<lambda>rv s :: det_state. (is_zombie (fst rv) \<or> fst rv = NullCap)\<rbrace>"
  by (auto simp: valid_def dest!: finalise_cap_ret split: cap.splits simp: is_zombie_def)

lemma silc_inv_irq_state_independent_A[simp, intro!]:
  "irq_state_independent_A (silc_inv aag st)"
  by (simp add: silc_inv_def irq_state_independent_A_def silc_dom_equiv_def equiv_for_def)


context FinalCaps_1 begin

crunches cap_swap_for_delete
  for silc_inv: "silc_inv aag st"
  (simp: crunch_simps)

lemma rec_del_silc_inv':
  notes drop_spec_valid[wp_split del] drop_spec_validE[wp_split del]
        drop_spec_ev[wp_split del] rec_del.simps[simp del]
  shows
  "s \<turnstile> \<lbrace>silc_inv aag st and einvs and simple_sched_action and valid_rec_del_call call
                        and emptyable (slot_rdcall call) and pas_refined aag
                        and K (case call of
                                 CTEDeleteCall slot _ \<Rightarrow> is_subject aag (fst slot) |
                                 FinaliseSlotCall slot _ \<Rightarrow> is_subject aag (fst slot) |
                                 ReduceZombieCall cap slot _ \<Rightarrow> is_subject aag (fst slot) \<and>
                                                                is_subject aag (obj_ref_of cap))\<rbrace>
       rec_del call
       \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>, \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  proof (induct s rule: rec_del.induct, simp_all only: rec_del_fails hoare_fail_any)
  case (1 slot exposed s) show ?case
    apply (simp add: split_def rec_del.simps)
    apply (rule hoare_pre_spec_validE)
     apply (wp empty_slot_silc_inv drop_spec_validE[OF returnOk_wp] drop_spec_validE[OF liftE_wp]
            | simp)+
     apply (rule_tac Q'="\<lambda>_ s. silc_inv aag st s \<and> is_subject aag (fst slot)"
                 and E="\<lambda>_. silc_inv aag st"
                  in spec_strengthen_postE)
      apply (rule spec_valid_conj_liftE2)
       apply wp
      apply (rule "1.hyps"[simplified])
     apply (simp | fastforce simp: silc_inv_def)+
    done
  next
  case (2 slot exposed s) show ?case
    apply (simp add: rec_del.simps split del: if_split)
    apply (rule hoare_pre_spec_validE)
     apply (wp drop_spec_validE[OF returnOk_wp] drop_spec_validE[OF liftE_wp] set_cap_silc_inv "2.hyps"
            | simp add: split_def split del: if_split)+
          apply (rule drop_spec_validE, (wp preemption_point_inv'| simp)+)[1]
         apply simp
         apply (rule spec_valid_conj_liftE2)
          apply (wp rec_del_ReduceZombie_emptyable preemption_point_inv' rec_del_invs
                    valid_validE_R[OF rec_del_respects(2)[simplified]] "2.hyps"
                    drop_spec_validE[OF liftE_wp] set_cap_silc_inv
                    set_cap_pas_refined replace_cap_invs  final_cap_same_objrefs set_cap_cte_cap_wp_to
                    set_cap_cte_wp_at hoare_weak_lift_imp hoare_vcg_ball_lift
                 | simp add: finalise_cap_not_reply_master_unlifted split del: if_split)+
       (* where the action is *)
       apply (simp cong: conj_cong add: conj_comms)
       apply (rule hoare_strengthen_post)
        apply (rule_tac Q="\<lambda> fin s. pas_refined aag s \<and>
                                    replaceable s slot (fst fin) rv \<and>
                                    cte_wp_at ((=) rv) slot s \<and>
                                    ex_cte_cap_wp_to (appropriate_cte_cap rv) slot s \<and>
                                    (\<forall>t\<in>obj_refs (fst fin). halted_if_tcb t s) \<and>
                                    einvs s \<and>
                                    silc_inv aag st s \<and>
                                    pasSubject aag \<noteq> SilcLabel \<and>
                                    emptyable slot s \<and> s \<turnstile> (fst fin) \<and>
                                    simple_sched_action s \<and>
                                    pas_cap_cur_auth aag (fst fin) \<and>
                                    is_subject aag (fst slot) \<and>
                                    (is_zombie (fst fin) \<or> fst fin = NullCap) \<and>
                                    (is_zombie (fst fin) \<longrightarrow> is_subject aag (obj_ref_of (fst fin))) \<and>
                                    (\<not> cap_points_to_label aag (fst fin) (pasObjectAbs aag (fst slot))
                                     \<longrightarrow> (\<exists>slot. slot \<in> slots_holding_overlapping_caps (fst fin) s
                                               \<and> pasObjectAbs aag (fst slot) = SilcLabel))"
                     in hoare_vcg_conj_lift[OF _ finalise_cap_cases[where slot=slot]])
        prefer 2
        subgoal for cap s'' isfinal s' fin s0
          apply (clarsimp simp: cte_wp_at_caps_of_state simp del:split_paired_Ex split_paired_All)
          apply (elim disjE; clarsimp simp: cte_wp_at_caps_of_state)
          apply (clarsimp simp: is_cap_simps gen_obj_refs_eq replaceable_zombie_not_transferable
                                cap_auth_conferred_def clas_no_asid aag_cap_auth_def
                                pas_refined_all_auth_is_owns cli_no_irqs
                      simp del: split_paired_Ex split_paired_All
                         dest!: appropriate_Zombie[symmetric, THEN trans, symmetric])
          apply (fastforce dest: sym[where s="{_}"])
          done
       apply (wp finalise_cap_pas_refined finalise_cap_silc_inv finalise_cap_auth' finalise_cap_ret'
                 finalise_cap_ret_is_subject' finalise_cap_ret_is_silc[where st=st]
                 finalise_cap_invs[where slot=slot]
                 finalise_cap_replaceable[where sl=slot]
                 finalise_cap_makes_halted[where slot=slot]
                 finalise_cap_auth' hoare_weak_lift_imp)

      apply (wp drop_spec_validE[OF liftE_wp] get_cap_auth_wp[where aag=aag]
             | simp add: is_final_cap_def)+
    apply (clarsimp simp: conj_comms caps_of_state_cteD)
    apply (frule (1) caps_of_state_valid)
    apply (frule if_unsafe_then_capD [OF caps_of_state_cteD]; clarsimp)
    apply (rule conjI, clarsimp simp: silc_inv_def)
    apply (case_tac cap;
           simp add: is_zombie_def aag_cap_auth_CNode aag_cap_auth_Thread aag_cap_auth_Zombie;
           fastforce dest:caps_of_state_valid silc_inv_not_subject)
    done
  next
  case (3 ptr bits n slot s) show ?case
    apply (simp add: rec_del.simps)
    apply (wp drop_spec_validE[OF returnOk_wp] drop_spec_validE[OF liftE_wp]
              cap_swap_for_delete_silc_inv)
    apply (simp add: pred_conj_def)
    apply (rule hoare_pre_spec_validE)
     apply (rule spec_valid_conj_liftE2)
      apply (wp | simp)+
    apply (wp drop_spec_validE[OF assertE_wp])
    apply (fastforce simp: silc_inv_def)
    done
  next
  case (4 ptr bits n slot s) show ?case
    apply (simp add: rec_del.simps)
    apply (wp drop_spec_validE[OF returnOk_wp] drop_spec_validE[OF liftE_wp] set_cap_silc_inv
              drop_spec_validE[OF assertE_wp] get_cap_wp | simp)+
    apply (rule_tac Q'="\<lambda> _. silc_inv aag st and
                    K (pasObjectAbs aag (fst slot) \<noteq> SilcLabel)" in spec_strengthen_postE)
     prefer 2
     apply (clarsimp)
     apply (drule silc_invD)
       apply assumption
      apply (simp add: intra_label_cap_def)
      apply (rule exI)
      apply (rule conjI)
       apply assumption
      apply (fastforce simp: cap_points_to_label_def)
     apply (clarsimp simp: slots_holding_overlapping_caps_def2 ctes_wp_at_def)
    apply (simp add: pred_conj_def)
    apply (rule hoare_pre_spec_validE)
     apply (wp spec_valid_conj_liftE2 "4.hyps")
     apply (simp add: in_monad)
    apply (fastforce simp: silc_inv_def cte_wp_at_caps_of_state zombie_ptr_emptyable)
    done
  qed

schematic_goal rec_del_silc_inv_not_transferable:
  "\<lbrace>?P\<rbrace> rec_del call \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>, \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  apply (rule use_spec)
  apply (rule rec_del_silc_inv')
  done

end


lemma cdt_change_allowed_not_silc:
  "\<lbrakk> valid_objs s; valid_mdb s; pas_refined aag s; silc_inv aag st s; cdt_change_allowed' aag ptr s \<rbrakk>
     \<Longrightarrow> pasObjectAbs aag (fst ptr) \<noteq> SilcLabel"
  (* very manual *)
  apply (frule(3) cca_to_transferable_or_subject)
  apply (frule silc_inv_not_subject)
  apply (elim disjE; simp?)
  apply (intro notI)
  apply (rule silc_inv_no_transferable', assumption, assumption)
  apply (elim cdt_change_allowedE cdt_direct_change_allowed.cases)
   apply (clarsimp simp:rtrancl_eq_or_trancl, elim disjE, solves\<open>clarsimp\<close>)
   apply (clarsimp dest!: tranclD2 parent_ofD)
   apply (drule valid_mdb_mdb_cte_at)
   apply (drule(1) mdb_cte_atD[rotated],clarsimp simp: cte_wp_at_caps_of_state)
  apply (rule silc_inv_cnode_onlyE, assumption, assumption)
  apply (erule tcb_states_of_state_kheapE)
  apply (frule(2) descendant_of_caller_slot[OF _ _ tcb_atI])
  apply clarsimp
  apply (frule(1) parent_of_rtrancl_no_descendant)
  apply (force simp add:is_cap_table obj_at_def)
  done

crunch_ignore (valid) (add: getActiveIRQ)
crunches update_work_units, reset_work_units
  for tcb_domain_map_wellformed[wp]: "tcb_domain_map_wellformed aag"
crunches preemption_point
  for silc_inv[wp]: "silc_inv aag st"
  and pas_refined[wp]: "pas_refined aag"
  (wp: crunch_wps OR_choiceE_weak_wp ignore_del: preemption_point)

lemma thread_set_tcb_registers_caps_merge_default_tcb_silc_inv[wp]:
  "\<lbrace>silc_inv aag st\<rbrace>
   thread_set (tcb_registers_caps_merge default_tcb) word
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  by (rule thread_set_silc_inv; simp add: tcb_cap_cases_def tcb_registers_caps_merge_def)

crunches cancel_badged_sends
  for silc_inv[wp]: "silc_inv aag st"
  (  wp: crunch_wps unless_wp simp: crunch_simps ignore: filterM set_object thread_set
   simp: filterM_mapM)


context FinalCaps_1 begin

lemma rec_del_silc_inv_CTEDelete_transferable':
  "\<lbrace>silc_inv aag st and pas_refined aag and einvs and simple_sched_action and emptyable slot
                    and (\<lambda>s. \<not> exposed \<longrightarrow> ex_cte_cap_wp_to (\<lambda>cp. cap_irqs cp = {}) slot s)
                    and cdt_change_allowed' aag slot\<rbrace>
   rec_del (CTEDeleteCall slot exposed)
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>, \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  apply (cases "is_subject aag (fst slot)")
   apply (wp rec_del_silc_inv_not_transferable)
   apply simp
  apply (subst rec_del.simps[abs_def])
  apply (wp add: hoare_K_bind without_preemption_wp empty_slot_silc_inv hoare_weak_lift_imp wp_transferable
                 rec_del_Finalise_transferable
            del: wp_not_transferable
         | wpc)+
   apply (rule hoare_strengthen_postE,rule rec_del_Finalise_transferable)
    apply force
   apply force
  apply (clarsimp)
  apply (frule(3) cca_to_transferable_or_subject[OF invs_valid_objs invs_mdb])
  apply (frule(4) cdt_change_allowed_not_silc[OF invs_valid_objs invs_mdb])
  by force

lemma cap_delete_silc_inv:
  "\<lbrace>silc_inv aag st and einvs and simple_sched_action and emptyable slot
                    and pas_refined aag and cdt_change_allowed' aag slot\<rbrace>
   cap_delete slot
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  unfolding cap_delete_def
  by (wp rec_del_silc_inv_CTEDelete_transferable' | simp)+

lemma cap_delete_silc_inv_not_transferable:
  "\<lbrace>silc_inv aag st and einvs and simple_sched_action and emptyable slot
                    and pas_refined aag and K (is_subject aag (fst slot))\<rbrace>
   cap_delete slot
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  unfolding cap_delete_def
  by (wp rec_del_silc_inv_not_transferable | simp)+

lemma cap_revoke_silc_inv':
  notes drop_spec_valid[wp_split del] drop_spec_validE[wp_split del]
        drop_spec_ev[wp_split del] rec_del.simps[simp del]
  shows
  "s \<turnstile> \<lbrace>silc_inv aag st and pas_refined aag and einvs
                        and simple_sched_action and K (is_subject aag (fst slot))\<rbrace>
       cap_revoke slot
       \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>, \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  proof(induct rule: cap_revoke.induct[where ?a1.0=s])
  case (1 slot s)
  show ?case
    apply (subst cap_revoke.simps)
    apply (rule hoare_pre_spec_validE)
     apply (wp "1.hyps")
            apply (wp spec_valid_conj_liftE2 | simp)+
             apply (wp drop_spec_validE[OF valid_validE[OF preemption_point_silc_inv]]
                      cap_delete_silc_inv preemption_point_inv' | simp)+
           apply (rule spec_valid_conj_liftE1)
            apply (rule validE_validE_R'[OF valid_validE[OF cap_delete_pas_refined]])
           apply (rule spec_valid_conj_liftE1, (wp | simp)+)
           apply (rule spec_valid_conj_liftE1, (wp | simp)+)
           apply (rule spec_valid_conj_liftE1, (wp | simp)+)
           apply (rule spec_valid_conj_liftE1, (wp | simp)+)
           apply (rule spec_valid_conj_liftE1, (wp | simp)+)
           apply (rule drop_spec_validE[OF valid_validE[OF cap_delete_silc_inv]])
          apply (wp drop_spec_validE[OF assertE_wp] drop_spec_validE[OF without_preemption_wp]
                    get_cap_wp drop_spec_validE[OF returnOk_wp])+
    apply clarsimp
    apply (clarsimp cong: conj_cong simp: conj_comms)
    apply (rule conjI)
     apply (cases "next_revoke_cap slot s")
     apply (force simp: emptyable_def dest!: reply_slot_not_descendant split: if_splits)
    apply (rule all_children_descendants_of[OF cdt_change_allowed_all_children];
           force)
    done
  qed

lemma cap_revoke_silc_inv:
  "\<lbrace>silc_inv aag st and pas_refined aag and einvs
                    and simple_sched_action and K (is_subject aag (fst slot))\<rbrace>
   cap_revoke slot
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>, \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  apply (rule use_spec)
  apply (rule cap_revoke_silc_inv')
  done

lemma finalise_slot_silc_inv:
  "\<lbrace>silc_inv aag st and einvs and pas_refined aag and simple_sched_action
                    and emptyable slot and K (is_subject aag (fst slot))\<rbrace>
   finalise_slot slot blah
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  unfolding finalise_slot_def
  apply (rule validE_valid)
  apply (rule hoare_pre)
   apply (rule rec_del_silc_inv_not_transferable)
  apply simp
  done

lemma invoke_cnode_silc_inv:
  "\<lbrace>silc_inv aag st and einvs and simple_sched_action and pas_refined aag and valid_cnode_inv i
                    and authorised_cnode_inv aag i and is_subject aag \<circ> cur_thread\<rbrace>
   invoke_cnode i
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  unfolding invoke_cnode_def
  apply (case_tac i)
        apply (wp cap_insert_silc_inv | simp)+
        apply (fastforce simp: silc_inv_def authorised_cnode_inv_def)
       apply (wp cap_move_silc_inv | simp)+
       apply (fastforce simp: silc_inv_def authorised_cnode_inv_def)
      apply (wp cap_revoke_silc_inv | simp)+
      apply (fastforce simp: authorised_cnode_inv_def)
     apply (wp cap_delete_silc_inv_not_transferable | simp)+
     apply (force simp: authorised_cnode_inv_def intro: real_cte_emptyable_strg[rule_format])
    apply (rule hoare_pre)
     apply (wp cap_move_silc_inv cap_swap_silc_inv cap_move_cte_wp_at_other
            | simp split del: if_split)+
    apply (fastforce simp: silc_inv_def authorised_cnode_inv_def)
   apply (wp cap_move_silc_inv get_cap_wp | wpc | simp)+
   apply (clarsimp simp: silc_inv_def authorised_cnode_inv_def)
   apply (erule cte_wp_at_weak_derived_ReplyCap)
  apply (wp cancel_badged_sends_silc_inv | simp | wpc | rule hoare_pre)+
  done

end


lemma set_cap_default_cap_silc_inv:
  "\<lbrace>silc_inv aag st and K (is_subject aag (fst slot) \<and> is_subject aag oref)\<rbrace>
   set_cap (default_cap a oref b dev) slot
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  apply (rule hoare_pre)
   apply (rule set_cap_silc_inv)
  apply (auto simp: cap_points_to_label_def
              dest: subsetD[OF obj_refs_default_cap] simp: silc_inv_def)
  done

lemma create_cap_silc_inv:
  "\<lbrace>silc_inv aag st and K (is_subject aag (fst (fst ref)) \<and>
                           is_subject aag (snd ref) \<and>
                           is_subject aag (fst c))\<rbrace>
   create_cap a b c dev ref
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  unfolding create_cap_def
  apply (rule hoare_gen_asm)
  apply (wp set_cap_default_cap_silc_inv set_cdt_silc_inv | simp add: split_def)+
  apply (subgoal_tac "pasObjectAbs aag (fst c) \<noteq> SilcLabel")
   apply (drule silc_inv_all_children)
   apply (simp add: all_children_def del: split_paired_All)
  apply (clarsimp simp: silc_inv_def)
  done

lemma retype_region_silc_inv:
  "\<lbrace>silc_inv aag st and K (range_cover ptr sz (obj_bits_api type o_bits) num_objects \<and>
                           (\<forall>x\<in>{ptr..(ptr && ~~ mask sz) + (2 ^ sz - 1)}. is_subject aag x))\<rbrace>
   retype_region ptr num_objects o_bits type dev
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  apply (rule hoare_gen_asm)+
  apply (simp only: retype_region_def retype_addrs_def
                   foldr_upd_app_if fun_app_def K_bind_def)
  apply (wp modify_wp dxo_wp_weak | simp)+
       apply (simp add: trans_state_update[symmetric] del: trans_state_update)
      apply wp+
  apply (clarsimp simp: not_less)
  apply (clarsimp simp add: silc_inv_def)
  apply (intro conjI impI allI)
    apply (fastforce simp: obj_at_def silc_inv_def
                     dest: retype_addrs_subset_ptr_bits[simplified retype_addrs_def]
                     simp: image_def p_assoc_help power_sub)
   defer
   apply (fastforce simp: silc_dom_equiv_def equiv_for_def silc_inv_def
                    dest: retype_addrs_subset_ptr_bits[simplified retype_addrs_def]
                    simp: image_def p_assoc_help power_sub)
  apply (case_tac "a \<in> (\<lambda>p. ptr_add ptr (p * 2 ^ obj_bits_api type o_bits)) `
                         {0..<num_objects}")
   apply clarsimp
   apply (subgoal_tac "cap = NullCap")
    apply (clarsimp simp: intra_label_cap_def cap_points_to_label_def)
    apply (drule (1) cte_wp_at_eqD2)
    apply fastforce
   apply (erule cte_wp_atE)
    subgoal by (fastforce simp: default_object_def empty_cnode_def
                         split: apiobject_type.splits if_splits)
   subgoal by (clarsimp simp: default_object_def default_tcb_def tcb_cap_cases_def
                       split: apiobject_type.splits if_splits)
  apply (subgoal_tac "cte_wp_at ((=) cap) (a,b) s \<and> \<not> intra_label_cap aag (a,b) s")
   apply (drule_tac x=a in spec, drule_tac x=b in spec, drule_tac x=cap in spec, simp)
   apply (elim exE conjE, rename_tac la lb)
   apply (rule_tac x=la in exI, simp, rule_tac x=lb in exI)
   apply (simp add: slots_holding_overlapping_caps_def2 ctes_wp_at_def)
   apply (subgoal_tac "la \<notin> (\<lambda>p. ptr_add ptr (p * 2 ^ obj_bits_api type o_bits)) `
                          {0..<num_objects}")
    apply (erule_tac t="(la,lb)" in cte_wp_atE)
     apply (rule cte_wp_at_cteI)
        apply fastforce
       apply assumption
      apply assumption
     apply assumption
    apply (rule cte_wp_at_tcbI)
      apply fastforce
     apply assumption
    apply assumption
   subgoal by (fastforce simp: silc_inv_def
                         dest: retype_addrs_subset_ptr_bits[simplified retype_addrs_def]
                         simp: image_def p_assoc_help power_sub)
  apply (rule conjI)
   subgoal by (fastforce elim: cte_wp_atE intro: cte_wp_at_cteI cte_wp_at_tcbI)
  apply (clarsimp simp: intra_label_cap_def cap_points_to_label_def)
  apply (drule (1) cte_wp_at_eqD2)
  apply (rule_tac x=capa in exI)
  apply clarsimp
  by (fastforce elim: cte_wp_atE intro: cte_wp_at_cteI cte_wp_at_tcbI)

lemma slots_holding_overlapping_caps_from_silc_inv:
  assumes a: "\<lbrace>silc_inv aag st and P\<rbrace> f \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  shows "\<lbrace>silc_inv aag st and (\<lambda> s. slot \<in> (slots_holding_overlapping_caps cap s) \<and>
                                pasObjectAbs aag (fst slot) = SilcLabel) and P\<rbrace>
         f
         \<lbrace>\<lambda>_ s. slot \<in> (slots_holding_overlapping_caps cap s)\<rbrace>"
  apply (simp add: valid_def split_def | intro impI allI ballI | elim conjE)+
  apply (simp add: slots_holding_overlapping_caps_def2 ctes_wp_at_def)
  apply (erule subst[rotated], rule cte_wp_at_pspace')
  apply (case_tac x, simp)
  apply (drule use_valid[OF _ a])
   apply simp
  by (fastforce simp: silc_inv_def silc_dom_equiv_def elim: equiv_forE)

lemma detype_silc_inv:
  "\<lbrace>silc_inv aag st and (K (\<forall>p\<in>S. is_subject aag p))\<rbrace>
   modify (detype S)
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  apply (wp modify_wp)
  apply (clarsimp simp: silc_inv_def)
  apply (rule conjI, fastforce)
  apply (rule conjI)
   apply (clarsimp simp: slots_holding_overlapping_caps_def intra_label_cap_def
                         cap_points_to_label_def get_cap_cte_wp_at')
   apply (drule (1) cte_wp_at_eqD2)
   apply clarsimp
   apply (drule_tac x=a in spec, drule_tac x=b in spec, drule_tac x=cap in spec)
   apply simp
   apply (erule impE)
    apply fastforce
   apply (elim exE conjE, rename_tac la lb lcap)
   apply (rule_tac x=la in exI, simp, rule_tac x=lb in exI, rule_tac x=lcap in exI)
   apply simp
   apply fastforce
  apply (clarsimp simp: silc_dom_equiv_def equiv_for_def detype_def)
  done

lemma delete_objects_silc_inv:
  "\<lbrace>silc_inv aag st and K (\<forall>p\<in>ptr_range ptr bits. is_subject aag p)\<rbrace>
   delete_objects ptr bits
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  apply (rule hoare_gen_asm)
  unfolding delete_objects_def
  apply (wp detype_silc_inv |  simp add: ptr_range_def)+
  done

lemma reset_untyped_cap_untyped_cap:
  "\<lbrace>cte_wp_at (\<lambda>cp. is_untyped_cap cp \<and> P True (untyped_range cp)) slot and
    invs and (\<lambda>s. descendants_of slot (cdt s) = {})\<rbrace>
   reset_untyped_cap slot
   \<lbrace>\<lambda>rv. cte_wp_at (\<lambda>cp. P (is_untyped_cap cp) (untyped_range cp)) slot\<rbrace>"
  apply (simp add: reset_untyped_cap_def cong: if_cong)
  apply (rule hoare_pre)
   apply (wp set_cap_cte_wp_at | simp add: unless_def)+
     apply (rule valid_validE,
            rule_tac Q="\<lambda>rv. cte_wp_at (\<lambda>cp. is_untyped_cap cp \<and> is_untyped_cap cap \<and>
                                             untyped_range cp = untyped_range cap \<and>
                                             P True (untyped_range cp)) slot"
                  in hoare_strengthen_post)
     apply (wp mapME_x_inv_wp preemption_point_inv set_cap_cte_wp_at
            | simp add: if_apply_def2
            | clarsimp simp: cte_wp_at_caps_of_state is_cap_simps bits_of_def ptr_range_def[symmetric])+
   apply (wp get_cap_wp)
  apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps ptr_range_def[symmetric])
  apply (frule if_unsafe_then_capD[OF caps_of_state_cteD], clarsimp+)
  apply (drule ex_cte_cap_protects[OF _ _ _ _ order_refl], erule caps_of_state_cteD)
     apply (clarsimp simp: descendants_range_def2 empty_descendants_range_in)
    apply clarsimp+
  done

lemma is_arch_update_overlaps:
  "\<lbrakk> cte_wp_at (\<lambda>c. is_arch_update cap c) slot s; \<not> cap_points_to_label aag cap l \<rbrakk>
     \<Longrightarrow> slot \<in> slots_holding_overlapping_caps cap s"
  apply (clarsimp simp: slots_holding_overlapping_caps_def2 ctes_wp_at_def)
  apply (erule cte_wp_at_weakenE)
  apply (clarsimp simp: is_arch_update_def)
  apply (clarsimp simp: cap_master_cap_def cap_points_to_label_def split: cap.splits)
  apply (fastforce dest: master_arch_cap_obj_refs)
  done

lemma as_user_silc_inv[wp]:
  "as_user t f \<lbrace>silc_inv aag st\<rbrace>"
  unfolding as_user_def
  apply (rule silc_inv_pres)
   apply (wp set_object_wp | simp add: split_def)+
   apply (clarsimp)
   apply (fastforce simp: silc_inv_def dest: get_tcb_SomeD simp: obj_at_def is_cap_table_def)
  apply (wp set_object_wp | simp add: split_def)+
  apply (case_tac "t = fst slot")
   apply (clarsimp split: kernel_object.splits)
   apply (erule notE)
   apply (erule cte_wp_atE)
    apply (fastforce simp: obj_at_def)
   apply (drule get_tcb_SomeD)
   apply (rule cte_wp_at_tcbI)
     apply (simp)
    apply assumption
   apply (fastforce simp: tcb_cap_cases_def split: if_splits)
  apply (fastforce elim: cte_wp_atE intro: cte_wp_at_cteI cte_wp_at_tcbI)
  done

crunches store_word_offs
  for silc_inv[wp]: "silc_inv aag st"

crunches store_word_offs
  for kheap[wp]: "\<lambda> s. P (kheap s x)"

crunches store_word_offs
  for cte_wp_at'[wp]: "\<lambda> s. Q (cte_wp_at P slot s)"
  (wp: crunch_wps simp: crunch_simps)

lemma set_mrs_silc_inv[wp]:
  "set_mrs a b c \<lbrace>silc_inv aag st\<rbrace>"
  unfolding set_mrs_def
  apply (rule silc_inv_pres)
   apply (wp crunch_wps set_object_wp | wpc | simp add: crunch_simps split del: if_split)+
   apply clarsimp
   apply (fastforce simp: silc_inv_def dest: get_tcb_SomeD simp: obj_at_def is_cap_table_def)
  apply (wp crunch_wps set_object_wp | wpc | simp add: crunch_simps split del: if_split)+
  apply (case_tac "a = fst slot")
   apply (clarsimp split: kernel_object.splits cong: conj_cong)
   apply (erule notE)
   apply (erule cte_wp_atE)
    apply (fastforce simp: obj_at_def)
   apply (drule get_tcb_SomeD)
   apply (rule cte_wp_at_tcbI)
     apply simp
    apply assumption
   apply (fastforce simp: tcb_cap_cases_def split: if_splits)
  apply (fastforce elim: cte_wp_atE intro: cte_wp_at_cteI cte_wp_at_tcbI)
  done

crunches update_waiting_ntfn, set_message_info
  for silc_inv[wp]: "silc_inv aag st"

lemma send_signal_silc_inv[wp]:
  "send_signal ntfnptr badge \<lbrace>silc_inv aag st\<rbrace>"
  unfolding send_signal_def
  apply (wp get_simple_ko_wp gts_wp cancel_ipc_indirect_silc_inv | wpc | simp)+
  apply (clarsimp simp: receive_blocked_def pred_tcb_at_def obj_at_def)
  done


context FinalCaps_1 begin

lemma slots_holding_overlapping_caps_eq:
  assumes "obj_refs cap = obj_refs cap'"
  assumes "cap_irqs cap = cap_irqs cap'"
  shows "slots_holding_overlapping_caps cap s = slots_holding_overlapping_caps cap' s"
  using assms by (fastforce simp: slots_holding_overlapping_caps_def)

lemma set_cap_silc_inv_simple:
  "\<lbrace>silc_inv aag st and cte_wp_at (\<lambda>cp. cap_irqs cp = cap_irqs cap \<and>
                                        obj_refs cp = obj_refs cap) slot
                    and K (is_subject aag (fst slot))\<rbrace>
   set_cap cap slot
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  apply (wp set_cap_silc_inv)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (rule conjI; clarsimp)
   apply (drule caps_of_state_cteD)
   apply (frule(1) silc_invD)
    apply (clarsimp simp: intra_label_cap_def)
    apply (rule exI, rule conjI, assumption)
    apply (simp add: cap_points_to_label_def)
   apply (simp add: slots_holding_overlapping_caps_def)
  apply (simp add: silc_inv_def)
  done

lemma reset_untyped_cap_silc_inv:
  "\<lbrace>silc_inv aag st and cte_wp_at is_untyped_cap slot
                    and invs and pas_refined aag
                    and (\<lambda>s. descendants_of slot (cdt s) = {})
                    and K (is_subject aag (fst slot))\<rbrace>
   reset_untyped_cap slot
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: reset_untyped_cap_def cong: if_cong)
  apply (rule validE_valid, rule hoare_pre)
   apply (wp set_cap_silc_inv_simple | simp add: unless_def)+
     apply (rule valid_validE, rule_tac Q="\<lambda>_. cte_wp_at is_untyped_cap slot and
                                               silc_inv aag st" in hoare_strengthen_post)
      apply (rule validE_valid, rule mapME_x_inv_wp, rule hoare_pre)
       apply (wp mapME_x_inv_wp preemption_point_inv set_cap_cte_wp_at
                 set_cap_silc_inv_simple | simp)+
      apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps)
     apply simp
    apply (wp hoare_vcg_const_imp_lift delete_objects_silc_inv get_cap_wp
              set_cap_silc_inv_simple
           | simp add: if_apply_def2)+
  apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps bits_of_def)
  apply (frule(1) cap_auth_caps_of_state)
  apply (clarsimp simp: aag_cap_auth_def aag_has_Control_iff_owns
                        ptr_range_def[symmetric])
  apply (frule if_unsafe_then_capD[OF caps_of_state_cteD], clarsimp+)
  apply (drule ex_cte_cap_protects[OF _ _ _ _ order_refl], erule caps_of_state_cteD)
     apply (clarsimp simp: descendants_range_def2 empty_descendants_range_in)
    apply clarsimp+
  done

lemma invoke_untyped_silc_inv:
  "\<lbrace>silc_inv aag st and invs and pas_refined aag and ct_active
                    and valid_untyped_inv ui and K (authorised_untyped_inv aag ui)\<rbrace>
   invoke_untyped ui
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (rule hoare_pre)
   apply (rule_tac Q="\<lambda>_. silc_inv aag st and
                          cte_wp_at (\<lambda>cp. is_untyped_cap cp
                                          \<longrightarrow> (\<forall>x \<in> untyped_range cp. is_subject aag x))
                                    (case ui of Retype src_slot _ _ _ _ _ _ _ \<Rightarrow> src_slot)"
                in hoare_strengthen_post)
    apply (rule invoke_untyped_Q)
        apply (rule hoare_pre, wp create_cap_silc_inv create_cap_pas_refined)
        apply (clarsimp simp: authorised_untyped_inv_def)
        apply (auto simp: cte_wp_at_caps_of_state)[1]
       apply ((wp | simp)+)[1]
      apply (rule hoare_pre)
       apply (wp retype_region_silc_inv retype_cte_wp_at | simp)+
      apply clarsimp
      apply (strengthen range_cover_le[mk_strg I E])
      apply (clarsimp simp: cte_wp_at_caps_of_state)
      apply (simp add: invs_valid_pspace)
      apply (erule ball_subset)
      apply (simp add: word_and_le2 field_simps)
     apply (rule hoare_pre)
      apply (wp set_cap_silc_inv_simple set_cap_cte_wp_at)
     apply (cases ui, clarsimp simp: cte_wp_at_caps_of_state is_cap_simps
                          split del: if_split cong: if_cong)
     apply (clarsimp simp: authorised_untyped_inv_def)
    apply (wp reset_untyped_cap_silc_inv reset_untyped_cap_untyped_cap)
   apply simp
  apply (cases ui, clarsimp simp: cte_wp_at_caps_of_state authorised_untyped_inv_def)
  apply (frule (1) cap_auth_caps_of_state)
  apply (clarsimp simp: aag_cap_auth_def aag_has_Control_iff_owns)
  done

lemma cap_insert_silc_inv':
  "\<lbrace>silc_inv aag st and K (is_subject aag (fst dest) \<and> is_subject aag (fst src) \<and>
                           cap_points_to_label aag cap (pasSubject aag))\<rbrace>
   cap_insert cap src dest
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  unfolding cap_insert_def
  apply (wp set_cap_silc_inv hoare_vcg_ex_lift
            set_untyped_cap_as_full_slots_holding_overlapping_caps_other[where aag=aag]
            get_cap_wp update_cdt_silc_inv set_cap_caps_of_state2
            set_untyped_cap_as_full_cdt_is_original_cap hoare_weak_lift_imp
         | simp split del: if_split)+
  apply (intro allI impI conjI)
    apply clarsimp
    apply (fastforce dest: silc_invD simp: intra_label_cap_def)
   apply (clarsimp simp: silc_inv_def)
  apply (fastforce dest!: silc_inv_all_children simp: all_children_def simp del: split_paired_All)
  done

end


lemma intra_label_cap_pres':
  assumes cte: "\<And>P. \<lbrace>\<lambda>s. cte_wp_at P slot s \<and> R s\<rbrace> f \<lbrace>\<lambda> _. cte_wp_at P slot\<rbrace>"
  shows "\<lbrace>intra_label_cap aag slot and cte_wp_at Q slot and R\<rbrace>
         f
         \<lbrace>\<lambda>_ s. intra_label_cap aag slot s\<rbrace>"
  apply (clarsimp simp: valid_def intra_label_cap_def)
  apply (drule cte_wp_at_norm)
  apply (elim exE conjE, rename_tac cap')
  apply (subgoal_tac "cap' = cap", blast)
  apply (drule use_valid[OF _ cte], fastforce)
  apply (rule_tac s=b in cte_wp_at_eqD2, auto)
  done

lemma max_free_index_update_intra_label_cap[wp]:
  "\<lbrace>intra_label_cap aag slot and cte_wp_at ((=) cap) slot\<rbrace>
   set_cap (max_free_index_update cap) slot
   \<lbrace>\<lambda>rv s. intra_label_cap aag slot s\<rbrace>"
  unfolding set_cap_def
  apply (wp set_object_wp get_object_wp | wpc| simp add: split_def)+
  apply (clarsimp simp: intra_label_cap_def cap_points_to_label_def)
  apply (fastforce elim: cte_wp_atE)
  done

lemma get_cap_slots_holding_overlapping_caps:
  "\<lbrace>silc_inv aag st\<rbrace>
   get_cap slot
   \<lbrace>\<lambda>cap s. \<not> cap_points_to_label aag cap (pasObjectAbs aag (fst slot))
            \<longrightarrow> (\<exists>a. (\<exists>b. (a, b) \<in> slots_holding_overlapping_caps cap s) \<and>
                     pasObjectAbs aag a = SilcLabel)\<rbrace>"
  apply (wp get_cap_wp)
  apply (fastforce dest: silc_invD simp: intra_label_cap_def)
  done

lemma get_cap_cte_wp_at_triv:
  "\<lbrace>\<top>\<rbrace> get_cap slot \<lbrace>\<lambda>rv s. cte_wp_at ((=) rv) slot s\<rbrace>"
  by (wp get_cap_wp, simp)

lemma get_cap_valid_max_free_index_update:
  "\<lbrace>\<lambda>s. \<exists>cap. cte_wp_at ((=) cap) slot s \<and> valid_cap cap s \<and> is_untyped_cap cap\<rbrace>
   get_cap slot
   \<lbrace>\<lambda>rv s. s \<turnstile> max_free_index_update rv\<rbrace>"
  apply (wp get_cap_wp)
  apply clarsimp
  apply (drule (1) cte_wp_at_eqD2, clarsimp)
  done

lemma get_cap_perform_asid_control_invocation_helper:
  "\<lbrace>\<lambda>s. (\<exists>cap. cte_wp_at ((=) cap) x2 s \<and> valid_cap cap s \<and> is_untyped_cap cap) \<and> R\<rbrace>
   get_cap x2
   \<lbrace>\<lambda>rv s. free_index_of rv \<le> max_free_index (untyped_sz_bits rv) \<and> is_untyped_cap rv \<and>
           max_free_index (untyped_sz_bits rv) \<le> 2 ^ cap_bits rv \<and> R\<rbrace>"
  apply (wp get_cap_wp)
  apply clarsimp
  apply (drule (1) cte_wp_at_eqD2)
  apply (case_tac capa, simp_all add: max_free_index_def free_index_of_def valid_cap_simps)
  done

lemma retype_region_cte_wp_at_other':
  "\<lbrace>cte_wp_at P slot and K ((fst slot) \<notin> set (retype_addrs ptr ty n us))\<rbrace>
   retype_region ptr n us ty dev
   \<lbrace>\<lambda>_. cte_wp_at P slot\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (clarsimp simp: valid_def)
  apply (subst cte_wp_at_pspace')
   prefer 2
   apply assumption
  apply (erule use_valid)
   apply (simp only: retype_region_def retype_addrs_def
                     foldr_upd_app_if fun_app_def K_bind_def)
   apply (wp modify_wp | simp)+
  apply (clarsimp simp: not_less retype_addrs_def)
  done

lemma untyped_caps_are_intra_label:
  "cte_wp_at is_untyped_cap slot s \<Longrightarrow> intra_label_cap aag slot s"
  apply (clarsimp simp: intra_label_cap_def cap_points_to_label_def)
  apply (drule (1) cte_wp_at_eqD2)
  apply (case_tac cap, simp_all)
  done

lemma interrupt_derived_ntfn_cap_identical_refs:
  "\<lbrakk>interrupt_derived cap cap'; is_ntfn_cap cap\<rbrakk> \<Longrightarrow>
   obj_refs cap = obj_refs cap' \<and>
   cap_irqs cap = cap_irqs cap'"
  apply (case_tac cap)
  apply (simp_all add: interrupt_derived_def cap_master_cap_def split: cap.splits)
  done

lemma cap_delete_one_cte_wp_at_other:
  "\<lbrace>cte_wp_at P slot and K (slot \<noteq> irq_slot)\<rbrace>
   cap_delete_one irq_slot
   \<lbrace>\<lambda>rv s. cte_wp_at P slot s\<rbrace>"
  unfolding cap_delete_one_def
  apply (wp unless_wp empty_slot_cte_wp_elsewhere get_cap_wp | simp)+
  done


context FinalCaps_1 begin

lemma cap_insert_silc_inv''':
  "\<lbrace>silc_inv aag st and (\<lambda> s. \<not> cap_points_to_label aag cap (pasObjectAbs aag (fst dest))
                              \<longrightarrow> (\<exists>lslot. lslot \<in> slots_holding_overlapping_caps cap s \<and>
                                           pasObjectAbs aag (fst lslot) = SilcLabel))
                    and K (pasObjectAbs aag (fst src) \<noteq> SilcLabel \<and>
                           pasObjectAbs aag (fst dest) \<noteq> SilcLabel)\<rbrace>
   cap_insert cap src dest
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  unfolding cap_insert_def
  apply (wp set_cap_silc_inv hoare_vcg_ex_lift
            set_untyped_cap_as_full_slots_holding_overlapping_caps_other[where aag=aag]
            get_cap_wp update_cdt_silc_inv set_cap_caps_of_state2
            set_untyped_cap_as_full_cdt_is_original_cap hoare_weak_lift_imp
         | simp split del: if_split)+
  apply (intro impI conjI allI)
    apply clarsimp
    apply (fastforce simp: silc_inv_def)
   apply clarsimp
   apply (drule_tac cap=capa in silc_invD)
     apply assumption
    apply (fastforce simp: intra_label_cap_def)
   apply fastforce
  apply (elim conjE)
  apply (drule silc_inv_all_children)
  apply (simp add: all_children_def del: split_paired_All)
  apply fastforce
  done

(* special case of newer cap_insert_silc_inv''' *)
lemma cap_insert_silc_inv'':
  "\<lbrace>silc_inv aag st and (\<lambda> s. \<not> cap_points_to_label aag cap (pasObjectAbs aag (fst dest))
                              \<longrightarrow> (\<exists>lslot. lslot \<in> slots_holding_overlapping_caps cap s \<and>
                                           pasObjectAbs aag (fst lslot) = SilcLabel))
                    and K (is_subject aag (fst src) \<and> is_subject aag (fst dest))\<rbrace>
   cap_insert cap src dest
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  apply (rule hoare_pre_imp[rotated])
   apply (rule cap_insert_silc_inv''')
  apply clarsimp
  by (metis is_subject_not_silc_inv)

lemma invoke_irq_handler_silc_inv:
  "\<lbrace>silc_inv aag st and pas_refined aag and irq_handler_inv_valid hi
                    and K (authorised_irq_hdl_inv aag hi)\<rbrace>
   invoke_irq_handler hi
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (case_tac hi)
    apply (wp cap_insert_silc_inv'' cap_delete_one_silc_inv_subject cap_delete_one_cte_wp_at_other
              hoare_weak_lift_imp hoare_vcg_ex_lift
              slots_holding_overlapping_caps_from_silc_inv[where aag=aag and st=st]
           | simp add: authorised_irq_hdl_inv_def get_irq_slot_def conj_comms)+
   apply (clarsimp simp: pas_refined_def irq_map_wellformed_aux_def)
   apply (drule cte_wp_at_norm)
   apply (elim exE conjE, rename_tac cap')
   apply (drule_tac cap=cap' in silc_invD)
     apply assumption
    apply (fastforce simp: intra_label_cap_def cap_points_to_label_def
                           interrupt_derived_ntfn_cap_identical_refs)
   apply (fastforce simp: slots_holding_overlapping_caps_def2 ctes_wp_at_def
                          interrupt_derived_ntfn_cap_identical_refs)
  apply (wp cap_delete_one_silc_inv_subject
         | simp add: pas_refined_def irq_map_wellformed_aux_def authorised_irq_hdl_inv_def)+
  done

end


lemma new_irq_handler_caps_are_intra_label:
  "\<lbrakk> cte_wp_at ((=) (IRQControlCap)) slot s; pas_refined aag s; is_subject aag (fst slot) \<rbrakk>
     \<Longrightarrow> cap_points_to_label aag (IRQHandlerCap irq) (pasSubject aag)"
  apply (clarsimp simp: cap_points_to_label_def)
  apply (frule cap_cur_auth_caps_of_state[rotated])
    apply assumption
   apply (simp add: cte_wp_at_caps_of_state)
  apply (clarsimp simp: aag_cap_auth_def cap_links_irq_def)
  apply (blast intro: aag_Control_into_owns_irq)
  done

crunches set_irq_state
  for silc_inv[wp]: "silc_inv aag st"
  (wp: silc_inv_triv)

crunches receive_signal
  for silc_inv[wp]: "silc_inv aag st"

crunches set_extra_badge
  for silc_inv[wp]: "silc_inv aag st"

crunches copy_mrs, set_message_info
  for silc_inv[wp]: "silc_inv aag st"
  (wp: crunch_wps)

crunches do_fault_transfer, complete_signal
  for silc_inv[wp]: "silc_inv aag st"

(* doesn't need sym_refs *)
lemma valid_ep_recv_dequeue':
  "\<lbrakk> ko_at (Endpoint (Structures_A.endpoint.RecvEP (t # ts))) epptr s; valid_objs s \<rbrakk>
     \<Longrightarrow> valid_ep (case ts of [] \<Rightarrow> IdleEP | b # bs \<Rightarrow> RecvEP ts) s"
  unfolding valid_objs_def valid_obj_def valid_ep_def obj_at_def
  apply (drule bspec)
  apply (auto split: list.splits)
  done

(* FIXME MOVE next to get_tcb definition*)
lemma get_tcb_Some:
  "get_tcb t s = Some v \<longleftrightarrow> kheap s t = Some (TCB v)"
  by (simp add: get_tcb_def split: kernel_object.splits option.splits)


context FinalCaps_1 begin

lemma derive_cap_silc:
  "\<lbrace>\<lambda>s :: det_state. \<not> cap_points_to_label aag cap l \<longrightarrow> R (slots_holding_overlapping_caps cap s)\<rbrace>
   derive_cap slot cap
   \<lbrace>\<lambda>cap' s. \<not> cap_points_to_label aag cap' l \<longrightarrow> R (slots_holding_overlapping_caps cap' s)\<rbrace>,-"
  apply (simp add: derive_cap_def)
  apply (wp arch_derive_cap_silc | wpc | simp add: split_def)+
  apply (auto simp: cap_points_to_label_def slots_holding_overlapping_caps_def)
  done

lemma transfer_caps_silc_inv:
  "\<lbrace>silc_inv aag st and valid_objs and valid_mdb and pas_refined aag
                    and (\<lambda>s. (\<forall>x \<in> set caps. s \<turnstile> fst x) \<and>
                             (\<forall>x \<in> set caps. cte_wp_at (\<lambda>cp. fst x \<noteq> NullCap \<longrightarrow> cp = fst x) (snd x) s
                                           \<and> real_cte_at (snd x) s))
                    and K (is_subject aag receiver \<and> (\<forall>cap \<in> set caps. is_subject aag (fst (snd cap))))\<rbrace>
  transfer_caps mi caps endpoint receiver receive_buffer
  \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: transfer_caps_def)
  apply (wpc | wp)+
    apply (rule_tac P = "\<forall>x \<in> set dest_slots. is_subject aag (fst x)" in hoare_gen_asm)
    apply (wpsimp wp: transfer_caps_loop_pres_dest cap_insert_silc_inv)
     apply (fastforce simp: silc_inv_def)
    apply (wp get_receive_slots_authorised hoare_vcg_all_lift hoare_vcg_imp_lift | simp)+
  apply (fastforce elim: cte_wp_at_weakenE)
  done

lemma do_normal_transfer_silc_inv:
  "\<lbrace>silc_inv aag st and pspace_aligned and valid_vspace_objs and valid_arch_state
                    and valid_objs and valid_mdb and pas_refined aag
                    and K (grant \<longrightarrow> is_subject aag sender \<and> is_subject aag receiver)\<rbrace>
   do_normal_transfer sender send_buffer ep badge grant receiver recv_buffer
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  unfolding do_normal_transfer_def
  apply (case_tac grant)
   apply ((wp transfer_caps_silc_inv copy_mrs_cte_wp_at hoare_vcg_ball_lift lec_valid_cap'
              lookup_extra_caps_authorised copy_mrs_pas_refined
           | simp)+)[1]
  apply simp
  apply (wp transfer_caps_empty_inv | simp)+
  done

lemma do_ipc_transfer_silc_inv:
  "\<lbrace>silc_inv aag st and pspace_aligned and valid_vspace_objs and valid_arch_state
                    and valid_objs and valid_mdb and pas_refined aag
                    and K (grant \<longrightarrow> is_subject aag sender \<and> is_subject aag receiver)\<rbrace>
   do_ipc_transfer sender ep badge grant receiver
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  unfolding do_ipc_transfer_def
  apply (wp do_normal_transfer_silc_inv hoare_vcg_all_lift | wpc | wp (once) hoare_drop_imps)+
  apply clarsimp
  done

end


locale FinalCaps_2 = FinalCaps_1 +
  assumes arch_perform_invocation_silc_inv:
    "\<lbrace>silc_inv aag st and invs and valid_arch_inv ai and authorised_arch_inv aag ai\<rbrace>
     arch_perform_invocation ai
     \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  and handle_arch_fault_reply_silc_inv[wp]:
    "handle_arch_fault_reply vmf thread x y \<lbrace>silc_inv aag st\<rbrace>"
  and arch_invoke_irq_control_silc_inv:
    "\<lbrace>silc_inv aag st and pas_refined aag and arch_irq_control_inv_valid arch_irq_cinv
                      and K (arch_authorised_irq_ctl_inv aag arch_irq_cinv)\<rbrace>
     arch_invoke_irq_control arch_irq_cinv
     \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  and invoke_tcb_silc_inv:
    "\<lbrace>silc_inv aag st and einvs and simple_sched_action and pas_refined aag and tcb_inv_wf tinv
                      and K (authorised_tcb_inv aag tinv)\<rbrace>
     invoke_tcb tinv
     \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
begin

lemma invoke_irq_control_silc_inv:
  "\<lbrace>silc_inv aag st and pas_refined aag and irq_control_inv_valid blah and
         K (authorised_irq_ctl_inv aag blah)\<rbrace>
      invoke_irq_control blah
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  unfolding authorised_irq_ctl_inv_def
  apply (case_tac blah)
   apply (rule hoare_gen_asm)
   apply (wp cap_insert_silc_inv'' hoare_vcg_ex_lift slots_holding_overlapping_caps_lift
         | simp add: authorised_irq_ctl_inv_def)+
   apply (fastforce dest: new_irq_handler_caps_are_intra_label)
  apply (simp, rule arch_invoke_irq_control_silc_inv[simplified])
  done

lemma setup_caller_cap_silc_inv:
  "\<lbrace>silc_inv aag st and K (grant \<longrightarrow> is_subject aag sender \<and> is_subject aag receiver)
       and K (pasObjectAbs aag sender \<noteq> SilcLabel \<and> pasObjectAbs aag receiver \<noteq> SilcLabel)\<rbrace>
     setup_caller_cap sender receiver grant
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  unfolding setup_caller_cap_def
  apply (wp cap_insert_silc_inv''' hoare_vcg_imp_lift hoare_vcg_ex_lift
            slots_holding_overlapping_caps_from_silc_inv[where aag=aag and st=st and P="\<top>"]
        | simp)+
  apply (auto simp: cap_points_to_label_def)
  done

lemma send_ipc_silc_inv:
  "\<lbrace>silc_inv aag st and invs and pas_refined aag
       and K (is_subject aag thread \<and> aag_has_auth_to aag SyncSend epptr \<and>
            (can_grant_reply \<longrightarrow> aag_has_auth_to aag Call epptr) \<and>
            (can_grant \<longrightarrow> aag_has_auth_to aag Grant epptr))\<rbrace>
     send_ipc block call badge can_grant can_grant_reply thread epptr
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  unfolding send_ipc_def
  apply (wp setup_caller_cap_silc_inv hoare_weak_lift_imp do_ipc_transfer_silc_inv gts_wp
        | wpc
        | simp add:st_tcb_at_tcb_states_of_state_eq
        | rule conjI impI
        | blast)+
     apply (wp hoare_vcg_all_lift hoare_imp_lift_something get_simple_ko_wp
           | simp add:st_tcb_at_tcb_states_of_state_eq)+
  apply clarsimp
  subgoal for s receiver t
    apply (frule silc_inv_not_subject)
    apply (cases can_grant)
    subgoal (* grant case *)
      apply clarsimp
      apply (rule context_conjI; clarsimp)
      apply (thin_tac "can_grant_reply \<longrightarrow> _")+
      apply (frule(1) tcb_states_of_state_to_auth, simp)
      apply (subgoal_tac "is_subject aag receiver")
       apply (force dest!: ko_atD elim: send_ipc_valid_ep_helper[simplified obj_at_def])
      (* Make the blockedOnReceive state point to epptr *)
      apply (frule(1) sym_ref_endpoint_recvD[OF invs_sym_refs _ head_in_set],
             clarsimp simp: st_tcb_at_tcb_states_of_state_eq)
      apply (frule(2) aag_wellformed_grant_Control_to_recv[OF _ _ pas_refined_wellformed])
      by (simp add: aag_has_Control_iff_owns)
    apply clarsimp
    apply (intro conjI[rotated] impI)
    subgoal (* no grant or grant reply case *)
      by (force elim: send_ipc_valid_ep_helper)
    subgoal (* grant reply case *)
      apply clarsimp
      (* Make the blockedOnReceive state point to epptr *)
      apply (frule(1) sym_ref_endpoint_recvD[OF invs_sym_refs _ head_in_set],
             clarsimp simp: st_tcb_at_tcb_states_of_state_eq)
      apply (frule(1) tcb_states_of_state_to_auth)
      by (auto elim: send_ipc_valid_ep_helper
          simp: aag_has_Control_iff_owns
          dest: tcb_states_of_state_to_auth
          aag_wellformed_grant_Control_to_recv_by_reply[OF _ _ _ pas_refined_wellformed];
          force dest: tcb_states_of_state_kheapD
          simp: obj_at_def is_cap_table
          elim: silc_inv_cnode_onlyE)
    done
  done

lemma receive_ipc_base_silc_inv:
  notes do_nbrecv_failed_transfer_def[simp]
  shows
  "\<lbrace>silc_inv aag st and invs and pas_refined aag and ko_at (Endpoint ep) epptr
       and K (is_subject aag receiver \<and>
           (pasSubject aag, Receive, pasObjectAbs aag epptr) \<in> pasPolicy aag \<and>
            (\<forall>auth \<in> cap_rights_to_auth rights True.
                        (pasSubject aag, auth, pasObjectAbs aag epptr) \<in> pasPolicy aag))\<rbrace>
     receive_ipc_base aag receiver ep epptr rights is_blocking
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  apply (clarsimp simp: thread_get_def get_thread_state_def cong: endpoint.case_cong)
  apply (rule hoare_pre)
   apply (wp setup_caller_cap_silc_inv hoare_weak_lift_imp do_ipc_transfer_silc_inv
         | wpc | simp split del: if_split)+
     apply (wp  hoare_vcg_all_lift hoare_vcg_imp_lift  set_simple_ko_get_tcb
           | wpc | simp split del: if_split)+
  apply (clarsimp)
  apply (frule tcb_states_of_state_to_auth[rotated])
   apply (simp add: tcb_states_of_state_def,blast)
  apply (clarsimp simp: get_tcb_Some)
  apply (frule(2) sym_ref_endpoint_sendD[OF invs_sym_refs _ hd_in_set])
  apply (clarsimp simp:st_tcb_at_tcb_states_of_state dest!:tcb_states_of_state_kheapD)
  apply (frule silc_inv_not_subject)
  by (safe;
       (clarsimp simp: cap_rights_to_auth_def)?;
       (erule(1) receive_ipc_valid_ep_helper
       | (erule(1) silc_inv_cnode_onlyE,simp add: obj_at_def is_cap_table)
       | (drule(2) aag_wellformed_grant_Control_to_send[OF _ _ pas_refined_wellformed],
          (simp add: aag_has_Control_iff_owns | force dest: pas_refined_Control))
       | (drule aag_wellformed_grant_Control_to_send_by_reply[OF _ _ _ pas_refined_wellformed],
          blast, blast, blast, simp add: aag_has_Control_iff_owns)))

lemma receive_ipc_silc_inv:
  "\<lbrace>silc_inv aag st and invs and pas_refined aag and
     K (is_subject aag receiver \<and> pas_cap_cur_auth aag cap \<and>
        AllowRead \<in> cap_rights cap)\<rbrace>
   receive_ipc receiver cap is_blocking
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  unfolding receive_ipc_def
  apply (rule hoare_gen_asm)
  apply (simp del: AllowSend_def split: cap.splits)
  apply clarsimp
  apply (rule bind_wp[OF _ get_simple_ko_sp])
  apply (rule bind_wp[OF _ gbn_sp])
  apply (case_tac ntfnptr, simp_all)
  (* old receive case, not bound *)
   apply (rule hoare_pre, wp receive_ipc_base_silc_inv,
          clarsimp simp: aag_cap_auth_def cap_auth_conferred_def cap_rights_to_auth_def)
  apply (rule bind_wp[OF _ get_simple_ko_sp])
  apply (case_tac "isActive ntfn", simp_all)
  (* new ntfn-binding case *)
   apply (rule hoare_pre, wp, clarsimp)
   (* old receive case, bound ntfn not active *)
  apply (rule hoare_pre, wp receive_ipc_base_silc_inv,
         clarsimp simp: aag_cap_auth_def cap_auth_conferred_def cap_rights_to_auth_def)
  done

lemma send_fault_ipc_silc_inv:
  "\<lbrace>pas_refined aag and invs and is_subject aag \<circ> cur_thread and silc_inv aag st
                    and K (valid_fault fault \<and> is_subject aag thread)\<rbrace>
   send_fault_ipc thread fault
   \<lbrace>\<lambda>rv. silc_inv aag st\<rbrace>"
  apply (rule hoare_gen_asm)+
  unfolding send_fault_ipc_def
  apply (wp send_ipc_silc_inv  thread_set_tcb_fault_set_invs
            thread_set_fault_pas_refined thread_set_refs_trivial thread_set_obj_at_impossible
            hoare_vcg_ex_lift get_cap_wp hoare_vcg_conj_lift hoare_vcg_ex_lift hoare_vcg_all_lift
         | wpc
         | simp add: Let_def split_def lookup_cap_def valid_tcb_fault_update)+
    apply (rule_tac Q'="\<lambda>rv s. silc_inv aag st s \<and> pas_refined aag s
                             \<and> is_subject aag (cur_thread s)
                             \<and> invs s
                             \<and> valid_fault fault
                             \<and> is_subject aag (fst (fst rv))"
                 in hoare_strengthen_postE_R[rotated])
     apply (force dest!: cap_auth_caps_of_state
                   simp: invs_valid_objs invs_sym_refs cte_wp_at_caps_of_state aag_cap_auth_def
                         cap_auth_conferred_def cap_rights_to_auth_def)
   apply (wp get_cap_auth_wp[where aag=aag] lookup_slot_for_thread_authorised
          | simp add: add: lookup_cap_def split_def)+
  done

crunches handle_fault
  for silc_inv[wp]: "silc_inv aag st"

crunches do_reply_transfer
  for silc_inv[wp]: "silc_inv aag st"
  (wp: thread_set_tcb_fault_update_silc_inv crunch_wps  ignore: set_object thread_set)

end


crunches reply_from_kernel
  for silc_inv[wp]: "silc_inv aag st"
  (wp: crunch_wps simp: crunch_simps)

lemma setup_reply_master_silc_inv:
  "\<lbrace>silc_inv aag st and K (is_subject aag thread)\<rbrace>
   setup_reply_master thread
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  unfolding setup_reply_master_def
  apply (wp set_cap_silc_inv hoare_vcg_ex_lift
            slots_holding_overlapping_caps_from_silc_inv[where aag=aag and st=st and P="\<top>"]
            get_cap_wp hoare_weak_lift_imp
         | simp)+
  apply (clarsimp simp: cap_points_to_label_def silc_inv_def)
  done


context FinalCaps_1 begin

crunches restart
  for silc_inv: "silc_inv aag st"
  (wp: crunch_wps simp: crunch_simps)

crunches suspend
  for silc_inv: "silc_inv aag st"

lemma same_object_as_cap_points_to_label:
  "\<lbrakk> same_object_as a cap; \<not> cap_points_to_label aag a (pasSubject aag) \<rbrakk>
     \<Longrightarrow> \<not> cap_points_to_label aag cap (pasSubject aag)"
  apply (simp add: same_object_as_def cap_points_to_label_def split: cap.splits)
      apply (case_tac cap, simp_all)
     apply (case_tac cap, simp_all)
    apply (case_tac cap, simp_all)
   apply (case_tac cap, simp_all)
  apply (fastforce dest: aobj_ref_same_aobject)
  done

lemma same_object_as_slots_holding_overlapping_caps:
  "\<lbrakk> same_object_as a cap; \<not> cap_points_to_label aag a (pasSubject aag) \<rbrakk>
     \<Longrightarrow> slots_holding_overlapping_caps cap s = slots_holding_overlapping_caps a s"
  apply (simp add: same_object_as_def slots_holding_overlapping_caps_def2 ctes_wp_at_def
           split: cap.splits)
       apply (case_tac cap, simp_all)
      apply (case_tac cap, simp_all)
     apply (case_tac cap, simp_all)
    apply (case_tac cap, simp_all)
   apply (case_tac cap, simp_all)
  apply (fastforce dest: aobj_ref_same_aobject)
  done

lemma checked_cap_insert_silc_inv:
  "\<lbrace>silc_inv aag st and K (is_subject aag (fst b) \<and> is_subject aag (fst e))\<rbrace>
   check_cap_at a b (check_cap_at c d (cap_insert a b e))
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  apply (wp cap_insert_silc_inv'' get_cap_wp | simp add: check_cap_at_def)+
  apply clarsimp
  apply (drule_tac cap=cap in silc_invD)
    apply assumption
   apply (clarsimp simp: intra_label_cap_def)
   apply (fastforce dest: same_object_as_cap_points_to_label)
  apply (fastforce dest: same_object_as_slots_holding_overlapping_caps)
  done

end


lemma thread_set_tcb_ipc_buffer_update_silc_inv[wp]:
  "\<lbrace>silc_inv aag st\<rbrace>
   thread_set (tcb_ipc_buffer_update blah) t
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  by (rule thread_set_silc_inv; simp add: tcb_cap_cases_def)

lemma thread_set_tcb_fault_handler_update_silc_inv[wp]:
  "\<lbrace>silc_inv aag st\<rbrace>
   thread_set (tcb_fault_handler_update blah) t
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  by (rule thread_set_silc_inv; simp add: tcb_cap_cases_def)

lemma thread_set_tcb_fault_handler_update_invs:
  "\<lbrace>invs and K (length a = word_bits)\<rbrace>
   thread_set (tcb_fault_handler_update (\<lambda>y. a)) word
   \<lbrace>\<lambda>_ s. invs s\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (wp itr_wps | simp)+
  done

lemma set_mcpriority_silc_inv[wp]:
  "set_mcpriority t mcp \<lbrace>silc_inv aag st\<rbrace>"
  unfolding set_mcpriority_def
  by (rule thread_set_silc_inv; simp add: tcb_cap_cases_def)

crunches bind_notification
  for silc_inv[wp]: "silc_inv aag st"

(* FIXME MOVE to the previous one and replace it: keep things generic please + wps is nice *)
lemma cap_delete_tcb[wp]:
 "cap_delete ptr \<lbrace>\<lambda>s. P (tcb_at t s)\<rbrace>"
  unfolding cap_delete_def tcb_at_typ
  by (simp add: tcb_at_typ | wp rec_del_typ_at)+

lemma st_tcb_at_triv:
  "st_tcb_at (\<lambda>_. P) t s \<longleftrightarrow> P \<and> tcb_at t s"
  by (simp add:tcb_at_st_tcb_at st_tcb_at_tcb_states_of_state) blast

lemma cap_insert_no_tcb_at[wp]:
 "cap_insert cap src dest \<lbrace>\<lambda>s. \<not> tcb_at t s\<rbrace>"
  unfolding tcb_at_st_tcb_at by (wp cap_insert_no_pred_tcb_at)

lemma intra_label_cap_cur_thread[simp]:
  "intra_label_cap aag slot (s\<lparr>cur_thread := X\<rparr>) = intra_label_cap aag slot s"
  by (simp add: intra_label_cap_def)

lemma slots_holding_overlapping_caps_cur_thread[simp]:
  "slots_holding_overlapping_caps cap (s\<lparr>cur_thread := X\<rparr>) = slots_holding_overlapping_caps cap s"
  by (simp add: slots_holding_overlapping_caps_def2 ctes_wp_at_def)

lemma silc_inv_cur_thread[simp]:
  "silc_inv aag st (s\<lparr>cur_thread := X\<rparr>) = silc_inv aag st s"
  by (simp add: silc_inv_def silc_dom_equiv_def equiv_for_def)


context FinalCaps_2 begin

lemma perform_invocation_silc_inv:
  "\<lbrace>silc_inv aag st and valid_invocation iv and authorised_invocation aag iv
                    and einvs and simple_sched_action
                    and pas_refined aag and is_subject aag \<circ> cur_thread\<rbrace>
   perform_invocation block call iv
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  apply (cases iv)
  by (wp invoke_untyped_silc_inv send_ipc_silc_inv
         invoke_tcb_silc_inv invoke_cnode_silc_inv
         invoke_irq_control_silc_inv
         invoke_irq_handler_silc_inv
         arch_perform_invocation_silc_inv
      | simp add: authorised_invocation_def invs_valid_objs
                  invs_mdb invs_sym_refs
                  split_def invoke_domain_def
      | fastforce dest:silc_inv_not_subject)+

lemma handle_invocation_silc_inv:
  "\<lbrace>silc_inv aag st and einvs and simple_sched_action and pas_refined aag
                    and is_subject aag \<circ> cur_thread and ct_active
                    and domain_sep_inv (pasMaySendIrqs aag) st'\<rbrace>
   handle_invocation calling blocking
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  apply (simp add: handle_invocation_def ts_Restart_case_helper split_def
                   liftE_liftM_liftME liftME_def bindE_assoc
              split del: if_split)
  apply (wp syscall_valid perform_invocation_silc_inv set_thread_state_runnable_valid_sched
            set_thread_state_pas_refined decode_invocation_authorised
         | simp split del: if_split)+
       apply (rule_tac E="\<lambda>ft. silc_inv aag st and pas_refined aag and
                               is_subject aag \<circ> cur_thread and invs and
                               (\<lambda>_. valid_fault ft \<and> is_subject aag thread)"
                   and R="Q" and Q=Q for Q in hoare_strengthen_postE)
         apply (wp lookup_extra_caps_authorised lookup_extra_caps_auth | simp)+
     apply (rule_tac E="\<lambda>ft. silc_inv aag st and pas_refined aag and
                             is_subject aag \<circ> cur_thread and invs and
                             (\<lambda>_. valid_fault (CapFault x False ft) \<and> is_subject aag thread)"
                 and R="Q" and Q=Q for Q in hoare_strengthen_postE)
        apply (wp lookup_cap_and_slot_authorised lookup_cap_and_slot_cur_auth | simp)+
  apply (auto intro: st_tcb_ex_cap simp: ct_in_state_def runnable_eq_active)
  done

lemmas handle_send_silc_inv =
  handle_invocation_silc_inv[where calling=False, folded handle_send_def]

lemmas handle_call_silc_inv =
  handle_invocation_silc_inv[where calling=True and blocking=True, folded handle_call_def]

lemma cte_wp_at_caps_of_state':
  "cte_wp_at ((=) c) slot s \<Longrightarrow> caps_of_state s slot = Some c"
  by (simp add: caps_of_state_def cte_wp_at_def)

lemma handle_reply_silc_inv:
  "\<lbrace>silc_inv aag st and invs and pas_refined aag and is_subject aag \<circ> cur_thread\<rbrace>
   handle_reply
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  unfolding handle_reply_def
  apply (wp hoare_vcg_all_lift get_cap_wp | wpc )+
  by (force dest: cap_auth_caps_of_state silc_inv_not_subject
            simp: cte_wp_at_caps_of_state aag_cap_auth_def cap_auth_conferred_def
                  reply_cap_rights_to_auth_def
           intro: aag_Control_into_owns)

crunches delete_caller_cap
  for silc_inv: "silc_inv aag st"

lemma handle_recv_silc_inv:
  "\<lbrace>silc_inv aag st and invs and pas_refined aag and is_subject aag \<circ> cur_thread\<rbrace>
   handle_recv is_blocking
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  apply (simp add: handle_recv_def Let_def lookup_cap_def split_def)
  apply (wp hoare_vcg_all_lift get_simple_ko_wp delete_caller_cap_silc_inv
            receive_ipc_silc_inv lookup_slot_for_thread_authorised
            lookup_slot_for_thread_cap_fault get_cap_auth_wp[where aag=aag]
         | wpc | simp
         | rule_tac Q="\<lambda>rv s. invs s \<and> pas_refined aag s \<and> is_subject aag thread \<and>
                              (pasSubject aag, Receive, pasObjectAbs aag x31) \<in> pasPolicy aag"
                 in hoare_strengthen_post, wp, clarsimp simp: invs_valid_objs invs_sym_refs)+
    apply (rule_tac Q'="\<lambda>r s. silc_inv aag st s \<and> invs s \<and> pas_refined aag s \<and>
                              is_subject aag thread \<and> tcb_at thread s \<and> cur_thread s = thread"
                 in hoare_strengthen_postE_R)
     apply wp
    apply ((clarsimp simp add: invs_valid_objs invs_sym_refs
            | intro impI allI conjI
            | rule cte_wp_valid_cap caps_of_state_cteD
            | fastforce simp: aag_cap_auth_def cap_auth_conferred_def
                              cap_rights_to_auth_def valid_fault_def
                        dest: silc_inv_not_subject)+)[1]
   apply (wp delete_caller_cap_silc_inv | simp add: split_def cong: conj_cong)+
  apply fastforce
  done

lemma handle_interrupt_silc_inv:
  "handle_interrupt irq \<lbrace>silc_inv aag st\<rbrace>"
  unfolding handle_interrupt_def by (wpsimp wp: hoare_drop_imps)

lemma handle_event_silc_inv:
  "\<lbrace>silc_inv aag st and einvs and simple_sched_action and pas_refined aag
                    and domain_sep_inv (pasMaySendIrqs aag) st'
                    and (\<lambda>s. ev \<noteq> Interrupt \<longrightarrow> ct_active s)
                    and (\<lambda>s. ct_active s \<longrightarrow> is_subject aag (cur_thread s))\<rbrace>
   handle_event ev
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  apply (case_tac ev; simp_all)
  by (wpsimp wp: handle_send_silc_inv[where st'=st']
                 handle_call_silc_inv[where st'=st']
                 handle_recv_silc_inv
                 handle_reply_silc_inv
                 handle_interrupt_silc_inv
                 handle_vm_fault_silc_inv hy_inv
                 handle_hypervisor_fault_silc_inv
           simp: invs_valid_objs invs_mdb invs_sym_refs)+

crunches activate_thread
  for silc_inv[wp]: "silc_inv aag st"

crunches schedule
  for silc_inv[wp]: "silc_inv aag st"
  (    wp: OR_choice_weak_wp crunch_wps
   ignore: set_scheduler_action
     simp: crunch_simps)

lemma call_kernel_silc_inv:
  "\<lbrace>silc_inv aag st and einvs and simple_sched_action and pas_refined aag
                    and (\<lambda>s. ev \<noteq> Interrupt \<longrightarrow> ct_active s)
                    and is_subject aag \<circ> cur_thread and domain_sep_inv (pasMaySendIrqs aag) st'\<rbrace>
   call_kernel ev
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  apply (simp add: call_kernel_def)
  apply (wp handle_interrupt_silc_inv handle_event_silc_inv[where st'=st'] | simp)+
  done

end

end
