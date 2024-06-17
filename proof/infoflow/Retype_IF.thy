(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Retype_IF
imports ArchCNode_IF
begin

lemma create_cap_reads_respects:
  "reads_respects aag l (K (is_subject aag (fst (fst slot))))
     (create_cap type bits untyped dev slot)"
  apply (rule gen_asm_ev)
  apply (simp add: create_cap_def split_def bind_assoc[symmetric])
  apply (fold update_cdt_def)
  apply (simp add: bind_assoc create_cap_ext_def)
  apply (wp set_cap_reads_respects set_original_reads_respects
            update_cdt_list_reads_respects update_cdt_reads_respects
         | simp | fastforce simp: equiv_for_def split: option.splits)+
  apply (intro impI conjI allI)
  by (fastforce simp: reads_equiv_def2 equiv_for_def
                elim: states_equiv_forE_is_original_cap states_equiv_forE_cdt
                dest: aag_can_read_self
               split: option.splits)+

lemma gets_any_evrv:
  "equiv_valid_rv_inv I A \<top>\<top> \<top> (gets f)"
  by (clarsimp simp: equiv_valid_2_def in_monad)

lemma select_f_any_evrv:
  "equiv_valid_rv_inv I A \<top>\<top> \<top> (select_f f)"
  by (clarsimp simp: equiv_valid_2_def select_f_def)

lemma select_f_any_ev2:
  "equiv_valid_2 I A A \<top>\<top> \<top> \<top> (select_f f) (select_f f')"
  by (clarsimp simp: equiv_valid_2_def select_f_def)

lemma machine_op_lift_ev':
  "equiv_valid_inv I A
     (K (\<forall>s t x y. (I s t \<longrightarrow> I (s\<lparr>machine_state_rest := x\<rparr>) (t\<lparr>machine_state_rest := y\<rparr>)) \<and>
                   (A s t \<longrightarrow> A (s\<lparr>machine_state_rest := x\<rparr>) (t\<lparr>machine_state_rest := y\<rparr>))))
     (machine_op_lift mop)"
  unfolding machine_op_lift_def comp_def machine_rest_lift_def
  apply (rule gen_asm_ev)
  apply (simp add: equiv_valid_def2)
  apply (rule equiv_valid_rv_bind)
    apply (rule gets_any_evrv)
   apply (rule_tac R'="\<top>\<top>" and Q="\<top>\<top>" and Q'="\<top>\<top>" in equiv_valid_2_bind_pre)
        apply (simp add: split_def)
        apply (rule modify_ev2)
        apply fastforce
       apply (rule select_f_any_ev2)
      apply wpsimp+
  done

lemma equiv_machine_state_machine_state_rest_update:
  "equiv_machine_state P s t
   \<Longrightarrow> equiv_machine_state P (s\<lparr>machine_state_rest := x\<rparr>) (t\<lparr>machine_state_rest := y\<rparr>)"
  by (fastforce intro: equiv_forI elim: equiv_forE)

lemma machine_op_lift_ev:
  "equiv_valid_inv (equiv_machine_state P) (equiv_machine_state Q) \<top> (machine_op_lift mop)"
  apply (rule equiv_valid_guard_imp)
   apply (rule machine_op_lift_ev')
  apply clarsimp
  apply (intro conjI impI)
     apply (drule equiv_machine_state_machine_state_rest_update, fastforce)+
  done

lemma machine_op_lift_irq_state[wp]:
  "machine_op_lift mop \<lbrace>\<lambda>ms. P (irq_state ms)\<rbrace>"
  by (simp add: machine_op_lift_def machine_rest_lift_def | wp | wpc)+

lemma dmo_mol_reads_respects:
  "reads_respects aag l \<top> (do_machine_op (machine_op_lift mop))"
  apply (rule use_spec_ev)
  apply (rule do_machine_op_spec_reads_respects)
   apply (rule equiv_valid_guard_imp[OF machine_op_lift_ev])
   apply simp
  apply wp
  done

lemma dmo_bind_ev:
  "equiv_valid_inv I A P (do_machine_op (a >>= b)) =
   equiv_valid_inv I A P (do_machine_op a >>= (\<lambda>rv. do_machine_op (b rv)))"
  by (fastforce simp: do_machine_op_def gets_def get_def select_f_def modify_def
                      put_def return_def bind_def equiv_valid_def2 equiv_valid_2_def)

lemma dmo_bind_ev':
  "equiv_valid_inv I A P (a >>= (\<lambda>rv. do_machine_op (b rv >>= c rv))) =
   equiv_valid_inv I A P (a >>= (\<lambda>rv. do_machine_op (b rv) >>= (\<lambda>rv'. do_machine_op (c rv rv'))))"
  by (fastforce simp: do_machine_op_def gets_def get_def select_f_def modify_def
                      put_def return_def bind_def equiv_valid_def2 equiv_valid_2_def)

lemma dmo_mapM_ev_pre:
  assumes reads_res: "\<And>x. x \<in> set lst \<Longrightarrow> equiv_valid_inv D A I (do_machine_op (m x))"
  assumes invariant: "\<And>x. x \<in> set lst \<Longrightarrow> do_machine_op (m x) \<lbrace>I\<rbrace>"
  assumes inv_established: "\<And>s. P s \<Longrightarrow> I s"
  shows "equiv_valid_inv D A P (do_machine_op (mapM m lst))"
  using assms
  apply atomize
  apply (rule_tac Q=I in equiv_valid_guard_imp)
   apply (induct lst)
    apply (simp add: mapM_Nil return_ev_pre)
   apply (subst mapM_Cons)
   apply (simp add: dmo_bind_ev dmo_bind_ev')
   apply (rule bind_ev_pre[where P''="I"])
      apply (rule bind_ev[OF return_ev])
       apply fastforce
      apply (rule wp_post_taut)
     apply fastforce+
  done

lemma dmo_mapM_x_ev_pre:
  assumes reads_res: "\<And>x. x \<in> set lst \<Longrightarrow> equiv_valid_inv D A I (do_machine_op (m x))"
  assumes invariant: "\<And>x. x \<in> set lst \<Longrightarrow> do_machine_op (m x) \<lbrace>I\<rbrace>"
  assumes inv_established: "\<And>s. P s \<Longrightarrow> I s"
  shows "equiv_valid_inv D A P (do_machine_op (mapM_x m lst))"
  apply (subst mapM_x_mapM)
  apply (simp add: dmo_bind_ev)
  apply (rule bind_ev_pre[OF return_ev dmo_mapM_ev_pre])
  by (blast intro: reads_res invariant inv_established wp_post_taut)+

lemma dmo_mapM_ev:
  assumes reads_res: "\<And>x. x \<in> set lst \<Longrightarrow> equiv_valid_inv D A I (do_machine_op (m x))"
  assumes invariant: "\<And>x. x \<in> set lst \<Longrightarrow> \<lbrace>I\<rbrace> do_machine_op (m x) \<lbrace>\<lambda>_. I\<rbrace>"
  shows "equiv_valid_inv D A I (do_machine_op (mapM m lst))"
  using assms by (auto intro: dmo_mapM_ev_pre)

lemma dmo_mapM_x_ev:
  assumes reads_res: "\<And>x. x \<in> set lst \<Longrightarrow> equiv_valid_inv D A I (do_machine_op (m x))"
  assumes invariant: "\<And>x. x \<in> set lst \<Longrightarrow> \<lbrace>I\<rbrace> do_machine_op (m x) \<lbrace>\<lambda>_. I\<rbrace>"
  shows "equiv_valid_inv D A I (do_machine_op (mapM_x m lst))"
  using assms by (auto intro: dmo_mapM_x_ev_pre)


locale Retype_IF_1 =
  assumes clearMemory_ev:
    "equiv_valid_inv (equiv_machine_state P) (equiv_machine_state Q) \<top> (clearMemory ptr bits)"
  and freeMemory_ev:
    "equiv_valid_inv (equiv_machine_state P) (equiv_machine_state Q) \<top> (freeMemory ptr bits)"
  and no_irq_freeMemory:
    "no_irq (freeMemory ptr sz)"
  and equiv_asid_detype:
    "equiv_asid asid s s' \<Longrightarrow> equiv_asid asid (detype N s) (detype N s')"
  and clearMemory_irq_state[wp]:
    "\<And>P. clearMemory ptr bits \<lbrace>\<lambda>s. P (irq_state s)\<rbrace>"
  and freeMemory_irq_state[wp]:
    "\<And>P. freeMemory ptr bits \<lbrace>\<lambda>s. P (irq_state s)\<rbrace>"
  and dmo_clearMemory_globals_equiv:
    "do_machine_op (clearMemory ptr (2 ^ bits)) \<lbrace>globals_equiv s\<rbrace>"
  and dmo_freeMemory_globals_equiv:
    "do_machine_op (freeMemory ptr bits) \<lbrace>globals_equiv s\<rbrace>"
  and retype_region_globals_equiv:
    "\<lbrace>globals_equiv s and invs
                      and (\<lambda>s. \<exists>i. cte_wp_at (\<lambda>c. c = UntypedCap dev (p && ~~ mask sz) sz i) slot s \<and>
                                   (i \<le> unat (p && mask sz) \<or> pspace_no_overlap_range_cover p sz s))
                      and K (range_cover p sz (obj_bits_api type o_bits) num \<and> 0 < num)\<rbrace>
     retype_region p num o_bits type dev
     \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
begin

lemma dmo_clearMemory_reads_respects:
  "reads_respects aag l \<top> (do_machine_op (clearMemory ptr bits))"
  apply (rule use_spec_ev)
  apply (rule do_machine_op_spec_reads_respects)
   apply (rule equiv_valid_guard_imp[OF clearMemory_ev], rule TrueI)
  apply wp
  done

lemma dmo_freeMemory_reads_respects:
  "reads_respects aag l \<top> (do_machine_op (freeMemory ptr bits))"
  apply (rule use_spec_ev)
  apply (rule do_machine_op_spec_reads_respects)
   apply (rule equiv_valid_guard_imp[OF freeMemory_ev], rule TrueI)
  apply wp
  done

lemma dmo_clearMemory_reads_respects_g:
  "reads_respects_g aag l \<top> (do_machine_op (clearMemory ptr (2 ^bits)))"
  apply (rule equiv_valid_guard_imp)
   apply (rule reads_respects_g)
    apply (rule dmo_clearMemory_reads_respects)
   apply (rule doesnt_touch_globalsI[where P = \<top>, simplified, OF dmo_clearMemory_globals_equiv])
  apply clarsimp
  done

lemma dmo_freeMemory_reads_respects_g:
  "reads_respects_g aag l (\<lambda> s. is_aligned ptr bits \<and> 2 \<le> bits \<and> bits < word_bits)
                    (do_machine_op (freeMemory ptr bits))"
  apply (rule equiv_valid_guard_imp)
   apply (rule reads_respects_g)
    apply (rule dmo_freeMemory_reads_respects)
   apply (rule doesnt_touch_globalsI[where P = \<top>, simplified, OF dmo_freeMemory_globals_equiv])
  apply clarsimp
  done

end


lemma globals_equiv_cdt_update[simp]:
  "globals_equiv s (s'\<lparr>cdt := x\<rparr>) = globals_equiv s s'"
  by (fastforce simp: globals_equiv_def idle_equiv_def)

lemma globals_equiv_is_original_cap_update[simp]:
  "globals_equiv s (s'\<lparr>is_original_cap := x\<rparr>) = globals_equiv s s'"
  by (fastforce simp: globals_equiv_def idle_equiv_def)

lemma create_cap_globals_equiv:
  "\<lbrace>globals_equiv s and valid_global_objs and valid_arch_state\<rbrace>
   create_cap type bits untyped dev slot
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  apply (simp only: create_cap_def split_def)
  apply (wp set_cap_globals_equiv set_original_globals_equiv set_cdt_globals_equiv
            set_cdt_valid_global_objs dxo_wp_weak set_original_wp | simp)+
  done

abbreviation reads_equiv_valid_g_inv where
"reads_equiv_valid_g_inv A aag P f \<equiv> equiv_valid_inv (reads_equiv_g aag) A P f"

lemma gets_apply_ev':
  "\<forall>s t. I s t \<and> A s t \<and> P s \<and> P t \<longrightarrow> (f s) x = (f t) x
   \<Longrightarrow> equiv_valid I A A P (gets_apply f x)"
  by (clarsimp simp: gets_apply_def get_def bind_def return_def equiv_valid_def2 equiv_valid_2_def)

lemma do_machine_op_globals_equiv:
   "(\<And>s sa. \<lbrakk> P sa; globals_equiv s sa \<rbrakk>
              \<Longrightarrow> \<forall>x\<in>fst (f (machine_state sa)). globals_equiv s (sa\<lparr>machine_state := snd x\<rparr>))
    \<Longrightarrow> \<lbrace>globals_equiv s and P\<rbrace>
        do_machine_op f
        \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding do_machine_op_def
  apply (wp | simp add: split_def)+
  done

lemma ptr_range_memE:
  "\<lbrakk> x \<in> ptr_range ptr bits; \<lbrakk> ptr \<le> x; x \<le> ptr + 2 ^ bits - 1 \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by (clarsimp simp: ptr_range_def)

lemma is_aligned_word_size_bits_upto_enum_step_mem:
  fixes ptr :: obj_ref
  shows "\<lbrakk> is_aligned ptr bits; word_size_bits \<le> bits; bits < word_bits;
           x \<in> set [ptr, ptr + word_size .e. ptr + 2 ^ bits - 1] \<rbrakk>
           \<Longrightarrow> is_aligned x word_size_bits"
  apply (clarsimp simp: word_size_size_bits_word[symmetric])
  apply (subst (asm) upto_enum_step_shift_red; (fastforce simp: word_bits_def)?)
  apply clarsimp
  apply (erule aligned_add_aligned)
   apply (rule is_alignedI)
   apply (simp add: mult.commute)
  apply (simp add: word_bits_conv)
  done

(* TODO: cleanup this beautiful proof *)
lemma ptr_range_subset:
  fixes ptr :: obj_ref
  shows "\<lbrakk> is_aligned ptr bits; word_size_bits \<le> bits; bits < word_bits;
           x \<in> set [ptr , ptr + word_size .e. ptr + 2 ^ bits - 1] \<rbrakk>
           \<Longrightarrow> ptr_range x word_size_bits \<subseteq> ptr_range ptr bits"
  apply (frule is_aligned_word_size_bits_upto_enum_step_mem, assumption+)
  apply (rule subsetI)
  apply (clarsimp simp: word_size_size_bits_word[symmetric])
  apply (subst (asm) upto_enum_step_shift_red; (fastforce simp: word_bits_def)?)
  apply (subst ptr_range_def)
  apply (clarsimp)
  apply (erule ptr_range_memE)
  apply (rule conjI)
   apply (erule order_trans[rotated])
   apply (erule is_aligned_no_wrap')
   apply (rule word_less_power_trans2[where k=word_size_bits, simplified];
         fastforce elim: of_nat_power simp: word_bits_conv word_bits_def)
  apply (erule order_trans)
  apply (clarsimp simp: word_size_size_bits_word)
  apply (subgoal_tac "ptr + of_nat xaa * word_size + word_size - 1 =
                      ptr + ((2 ^ word_size_bits - 1) + of_nat xaa * word_size)")
   apply (subgoal_tac "ptr + 2 ^ bits - 1 = ptr + (2 ^ bits - 1)")
    apply (erule ssubst)+
    apply (rule word_plus_mono_right)
     apply (drule is_aligned_addD1)
      apply (erule (1) is_aligned_weaken)
     prefer 2
     apply (erule is_aligned_no_wrap')
     apply simp
    apply (simp_all add: word_size_size_bits_word)
  apply (drule (1) word_less_power_trans_ofnat[where 'a=machine_word_len], simp add: word_bits_def)
  apply (subst add.commute)
  apply (erule is_aligned_add_less_t2n)
    apply (simp_all add: word_size_size_bits_word)
  using zero_less_word_size gt0_iff_gem1 by blast

lemma do_machine_op_mapM_x:
  assumes ef: "\<And>a. empty_fail (f a)"
  shows "do_machine_op (mapM_x f xs) = mapM_x (\<lambda> x. do_machine_op (f x)) xs"
  apply (induct xs)
   apply (simp add: mapM_x_Nil)
  apply (clarsimp simp: mapM_x_Cons do_machine_op_bind[OF ef empty_fail_mapM_x[OF ef]])
  done

lemma create_cap_reads_respects_g:
  "reads_respects_g aag l
     (K (is_subject aag (fst (fst slot))) and valid_global_objs and valid_arch_state)
     (create_cap type bits untyped dev slot)"
  apply (rule equiv_valid_guard_imp[OF reads_respects_g])
    apply (rule create_cap_reads_respects)
   apply (wp doesnt_touch_globalsI create_cap_globals_equiv | simp)+
  done

lemma retype_region_ext_def2:
  "retype_region_ext a b =
   modify (\<lambda>s. ekheap_update (\<lambda>ekh x. if x \<in> set a then default_ext b (cur_domain s) else ekh x) s)"
  by (simp add: retype_region_ext_def foldr_upd_app_if' gets_def bind_def
                return_def modify_def get_def put_def fun_eq_iff)

lemma retype_region_reads_respects:
  "reads_respects aag l \<top> (retype_region ptr num_objects o_bits type dev)"
  apply (simp only: retype_region_def retype_addrs_def foldr_upd_app_if fun_app_def
                    K_bind_def when_def retype_region_ext_extended.dxo_eq)
  apply (simp only: retype_region_ext_def2)
  apply (simp split del: if_split add: equiv_valid_def2)
  apply (rule_tac W="\<top>\<top>" and Q="\<top>\<top>" in equiv_valid_rv_bind)
    apply (rule equiv_valid_rv_guard_imp[OF if_evrv])
      apply (rule equiv_valid_rv_bind[OF gets_kheap_revrv])
       apply simp
       apply (rule_tac Q="\<lambda>_ s. rv = kheap s" and Q'="\<lambda>_ s. rv' = kheap s" and R'="(=)"
                    in equiv_valid_2_bind_pre)
            apply (rule modify_ev2)
            apply (fastforce elim: reads_equiv_identical_kheap_updates
                                   affects_equiv_identical_kheap_updates
                             simp: identical_kheap_updates_def)
           apply (rule_tac P=\<top> and P'=\<top> in modify_ev2)
           apply (fastforce intro: reads_equiv_identical_ekheap_updates
                                   affects_equiv_identical_ekheap_updates
                             simp: identical_updates_def default_ext_def reads_equiv_def)
          apply (wp | simp)+
     apply (rule return_ev2 | simp | rule impI, rule TrueI)+
  apply (intro impI, wp)
  done

lemma subset_thing:
  "\<lbrakk> a \<le> b; a \<le> a \<rbrakk> \<Longrightarrow> {a} \<subseteq> {a..b}"
  by auto

lemma updates_not_idle:
  "\<lbrakk> idle_equiv st s; \<forall>a \<in> S. a \<noteq> idle_thread s \<rbrakk>
     \<Longrightarrow> idle_equiv st (s\<lparr>kheap := \<lambda>a. if a \<in> S then y else kheap s a\<rparr>)"
  by (fastforce simp: idle_equiv_def tcb_at_def2)

lemma post_retype_invs_valid_arch_stateI:
  "post_retype_invs ty rv s \<Longrightarrow> valid_arch_state s"
  by (clarsimp simp: post_retype_invs_def invs_def valid_state_def split: if_split_asm)

lemma post_retype_invs_pspace_alignedI:
  "post_retype_invs ty rv s \<Longrightarrow> pspace_aligned s"
  by (clarsimp simp: post_retype_invs_def invs_def valid_state_def split: if_split_asm)

lemma detype_def2:
   "detype S (s :: det_state) = s\<lparr>kheap := \<lambda>x. if x \<in> S then None else kheap s x,
                                  ekheap := \<lambda>x. if x \<in> S then None else ekheap s x\<rparr>"
  by (simp add: detype_def detype_ext_def)

lemma cur_thread_detype:
  "cur_thread (detype S s) = cur_thread s"
  by (auto simp: detype_def)

lemma cur_domain_detype:
  "cur_domain (detype S s) = cur_domain s"
  by (auto simp: detype_def detype_ext_def)

lemma sched_act_detype:
  "scheduler_action (detype S s) = scheduler_action s"
  by (auto simp: detype_def detype_ext_def)

lemma wuc_detype:
  "work_units_completed (detype S s) = work_units_completed s"
  by (auto simp: detype_def detype_ext_def)

lemma machine_state_detype:
  "machine_state (detype S s) = machine_state s"
  by (auto simp: detype_def detype_ext_def)


context Retype_IF_1 begin

lemma retype_region_reads_respects_g:
  "reads_respects_g aag l
     ((\<lambda>s. \<exists>idx. cte_wp_at (\<lambda>c. c = UntypedCap dev (ptr && ~~ mask sz) sz idx) slot s \<and>
                 (idx \<le> unat (ptr && mask sz) \<or> pspace_no_overlap_range_cover ptr sz s)) and
      invs and K (range_cover ptr sz (obj_bits_api type o_bits) num_objects \<and> 0 < num_objects))
     (retype_region ptr num_objects o_bits type dev)"
  apply (rule equiv_valid_guard_imp[OF reads_respects_g[OF retype_region_reads_respects]])
   apply (rule doesnt_touch_globalsI)
   apply (rule hoare_weaken_pre[OF retype_region_globals_equiv])
   apply simp
  apply auto
  done

lemma states_equiv_for_detype:
  "states_equiv_for P Q R S s s' \<Longrightarrow> states_equiv_for P Q R S (detype N s) (detype N s')"
  apply (simp add: states_equiv_for_def equiv_for_def equiv_asids_def obj_at_def equiv_asid_detype)
  apply (simp add: detype_def detype_ext_def)
  done

lemma detype_reads_respects:
  "reads_respects aag l \<top> (modify (detype S))"
  apply (clarsimp simp: equiv_valid_def2 equiv_valid_2_def in_monad reads_equiv_def2 affects_equiv_def2)
  apply (simp add: cur_domain_detype cur_thread_detype sched_act_detype wuc_detype machine_state_detype)
  apply (fastforce intro: states_equiv_for_detype)
  done

crunch delete_objects
  for irq_masks[wp]: "\<lambda>s. P (irq_masks (machine_state s))"
  (ignore: do_machine_op wp: dmo_wp no_irq_freeMemory no_irq simp: detype_def)

end


lemma untyped_caps_do_not_overlap_global_refs:
  "\<lbrakk> cte_wp_at ((=) (UntypedCap dev word sz idx)) slot s; valid_global_refs s \<rbrakk>
     \<Longrightarrow> ptr_range word sz \<inter> global_refs s = {}"
  apply (simp add: cte_wp_at_caps_of_state)
  apply (drule (1) valid_global_refsD2)
  apply (fastforce simp: cap_range_def ptr_range_def)
  done

lemma singleton_set_size:
  "{ptr..(ptr::'a::len word) + 2 ^ 0 - 1} = {ptr}"
  by (simp add: field_simps)

lemma cap_range_of_valid_capD:
  "valid_cap cap s \<Longrightarrow> (cap_range cap = {}) \<or> (\<exists>ptr sz. (cap_range cap = ptr_range ptr sz))"
  apply (rule disj_subst)
  apply (cases cap)
  by (clarsimp simp: valid_cap_def valid_untyped_def cap_aligned_def cap_range_def ptr_range_def
      | intro exI | rule singleton_set_size[symmetric] | fastforce)+

lemma set_cap_reads_respects_g:
  "reads_respects_g aag l (valid_global_objs and valid_arch_state
                                             and K (is_subject aag (fst slot))) (set_cap cap slot)"
  apply (rule equiv_valid_guard_imp)
   apply (rule reads_respects_g[OF set_cap_reads_respects])
   apply (wp doesnt_touch_globalsI set_cap_globals_equiv | simp)+
  done

(*FIXME move*)
lemma when_ev:
  "(C \<Longrightarrow> equiv_valid I A A P handle) \<Longrightarrow> equiv_valid I A A (\<lambda>s. C \<longrightarrow> P s) (when C handle)"
  by (wp | auto simp: when_def)+

lemma delete_objects_caps_no_overlap:
  "\<lbrace>invs and ct_active and (\<lambda>s. \<exists>slot idx. cte_wp_at ((=) (UntypedCap dev ptr sz idx)) slot s \<and>
                                           descendants_range_in {ptr..ptr + 2 ^ sz - 1} slot s)\<rbrace>
   delete_objects ptr sz
   \<lbrace>\<lambda>_ s :: det_ext state. caps_no_overlap ptr sz s\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (rule descendants_range_caps_no_overlapI)
    apply (erule use_valid | wp | simp add: descendants_range_def2 | blast)+
   apply (frule untyped_cap_aligned,
         (simp add: invs_valid_objs)+)
   apply (rule conjI, assumption)
   apply (drule (2) untyped_slots_not_in_untyped_range, simp+, rule subset_refl)
   apply simp
  apply (erule use_valid | wp delete_objects_descendants_range_in | simp | blast)+
  done

lemma get_cap_reads_respects_g:
  "reads_respects_g aag l (K (is_subject aag (fst slot))) (get_cap slot)"
  apply (rule equiv_valid_guard_imp)
   apply (rule reads_respects_g[OF get_cap_rev])
   apply (rule doesnt_touch_globalsI)
   apply wp
   apply clarsimp
  apply simp
  done

lemma irq_state_independent_globals_equiv[simp,intro!]:
  "irq_state_independent_A (globals_equiv st)"
  by (clarsimp simp: irq_state_independent_A_def globals_equiv_def idle_equiv_def)

lemma irq_state_independent_A_only_timer_irq_inv[simp]:
  "irq_state_independent_A (only_timer_irq_inv irq st)"
  apply (simp add: only_timer_irq_inv_def)
  apply (rule irq_state_independent_A_conjI)
   apply (simp add: domain_sep_inv_def)
  apply (simp add: irq_state_independent_A_def only_timer_irq_def
                   irq_is_recurring_def is_irq_at_def)
  done

lemma only_timer_irq_inv_work_units_completed[simp]:
  "only_timer_irq_inv irq st (work_units_completed_update f s)
    = only_timer_irq_inv irq st s"
  apply (simp add: only_timer_irq_inv_def)
  apply (simp add: domain_sep_inv_def)
  apply (simp add: irq_state_independent_A_def only_timer_irq_def
                   irq_is_recurring_def is_irq_at_def)
  done

lemma delete_objects_pspace_no_overlap_again:
  "\<lbrace>pspace_aligned and valid_objs and (\<lambda>s. \<exists>slot. cte_wp_at (\<lambda>cp. is_untyped_cap cp \<and>
                                                                  obj_ref_of cp = ptr \<and>
                                                                  bits_of cp = sz) slot s)
                                  and K (S \<subseteq> {ptr .. ptr + 2 ^ sz - 1})\<rbrace>
   delete_objects ptr sz
   \<lbrace>\<lambda>_. pspace_no_overlap S\<rbrace>"
  unfolding delete_objects_def do_machine_op_def
  apply (wp | simp add: split_def detype_machine_state_update_comm)+
  apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps bits_of_def)
  apply (drule caps_of_state_cteD)
  apply (frule cte_wp_at_valid_objs_valid_cap, clarsimp+)
  apply (erule pspace_no_overlap_subset[rotated])
  apply (rule pspace_no_overlap_subset, rule pspace_no_overlap_detype, simp+)
  apply (simp add: valid_cap_simps cap_aligned_def field_simps)
  done

lemma ex_tupleI:
  "P (fst t) (snd t) \<Longrightarrow> \<exists>a b. P a b"
  by blast

lemma equiv_valid_obtain:
  assumes fn_eq: "\<And>s t. I s t \<Longrightarrow> A s t \<Longrightarrow> P s \<Longrightarrow> P t \<Longrightarrow>  fn s = fn t"
  assumes pr: "\<And>x. equiv_valid I A B (P and (\<lambda>s. fn s = x)) f"
  shows "equiv_valid I A B P f"
  apply (clarsimp simp: equiv_valid_def2 equiv_valid_2_def)
  apply (frule(1) fn_eq, simp+)
  apply (cut_tac x="fn s" in pr)
  apply (clarsimp simp: equiv_valid_def2 equiv_valid_2_def)
  apply fastforce
  done

lemma reads_equiv_cte_wp_at:
  "\<lbrakk> reads_equiv aag s s'; is_subject aag (fst slot) \<rbrakk>
     \<Longrightarrow> cte_wp_at P slot s = cte_wp_at P slot s'"
  apply (frule(1) is_subject_kheap_eq)
  apply (simp add: cte_wp_at_cases)
  done

lemma reads_equiv_caps_of_state:
  "\<lbrakk> reads_equiv aag s s'; is_subject aag (fst slot) \<rbrakk>
     \<Longrightarrow> caps_of_state s slot = caps_of_state s' slot"
  apply (frule(1) reads_equiv_cte_wp_at[where P="(=) (the (caps_of_state s slot))"])
  apply (frule(1) reads_equiv_cte_wp_at[where P="\<top>"])
  apply (auto simp: cte_wp_at_caps_of_state)
  done


locale Retype_IF_2 = Retype_IF_1 +
  fixes aag :: "'a subject_label PAS"
  assumes invoke_untyped_reads_respects_g_wcap:
    "reads_respects_g aag l (invs and valid_untyped_inv_wcap ui (Some (UntypedCap dev ptr sz idx))
        and only_timer_irq_inv irq st
        and ct_active and pas_refined aag
        and K (authorised_untyped_inv aag ui)) (invoke_untyped ui)"
begin

lemma invoke_untyped_reads_respects_g:
  "reads_respects_g aag l (invs and valid_untyped_inv ui and only_timer_irq_inv irq st
                                and ct_active and pas_refined aag
                                and K (authorised_untyped_inv aag ui)) (invoke_untyped ui)"
  apply (rule_tac fn="\<lambda>s. caps_of_state s (slot_of_untyped_inv ui)" in equiv_valid_obtain)
   apply (cases ui, clarsimp simp: valid_untyped_inv_wcap reads_equiv_g_def)
   apply (simp add: authorised_untyped_inv_def
                    reads_equiv_caps_of_state)
  apply (case_tac "x \<noteq> None \<and> is_untyped_cap (the x)")
   apply (clarsimp simp: is_cap_simps)
   apply (rule equiv_valid_guard_imp, rule invoke_untyped_reads_respects_g_wcap)
   apply (cases ui, clarsimp simp: cte_wp_at_caps_of_state valid_untyped_inv_wcap)
   apply auto[1]
  apply (rule equiv_valid_guard_imp, rule gen_asm_ev'[where Q=False])
   apply simp
  apply (cases ui, clarsimp simp: valid_untyped_inv_wcap cte_wp_at_caps_of_state)
  done

end

end
