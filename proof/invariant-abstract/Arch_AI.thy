(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Top level architecture related proofs.
*)

theory Arch_AI
imports ArchUntyped_AI ArchFinalise_AI
begin

declare detype_arch_state[simp]

lemma invs_strgs:
  "invs s \<longrightarrow> valid_pspace s"
  "invs s \<longrightarrow> valid_mdb s"
  "invs s \<longrightarrow> valid_objs s"
  "invs s \<longrightarrow> pspace_aligned s"
  by auto


lemma assocs_dom_comp:
  "set (map fst (filter (\<lambda>(x,y). P x \<and> y = None) (assocs f))) = (- dom f \<inter> Collect P)"
  apply (clarsimp simp: in_assocs_is_fun)
  apply (rule set_eqI)
  apply clarsimp
  apply (rule iffI, clarsimp)
  apply (erule conjE)
  apply (drule not_in_domD)
  apply (rule_tac x="(x,None)" in image_eqI)
   apply simp
  apply simp
  done


lemma assocs_empty_dom_comp:
  "(- dom f \<inter> Collect P = {}) = null (filter (\<lambda>(x, y). P x \<and> y = None) (assocs f))"
   apply (subst assocs_dom_comp [symmetric])
   apply (subst empty_set_is_null)
   apply (simp add: null_def)
   done


lemma dom_hd_assocsD:
  fixes P
  defines "filter_assocs f \<equiv> filter (\<lambda>(x,y). P x \<and> y = None) (assocs f)"
  assumes d: "- dom f \<inter> Collect P \<noteq> {}"
  shows "fst (hd (filter_assocs f)) \<notin> dom f \<and> P (fst (hd (filter_assocs f)))"
proof -
  from d  have "\<not>null (filter_assocs f)"
    unfolding filter_assocs_def
    by (simp add: assocs_empty_dom_comp)
  hence "hd (filter_assocs f) \<in> set (filter_assocs f)"
    by (clarsimp simp: null_def neq_Nil_conv)
  thus ?thesis
    unfolding filter_assocs_def
    by (clarsimp simp: in_assocs_is_fun)
qed


lemma ucast_assocs:
  "LENGTH('a) < LENGTH('b) \<Longrightarrow>
   assocs (fn o (ucast :: 'a :: len word \<Rightarrow> 'b :: len word))
     = map (\<lambda>(x, y). (ucast x, y)) (filter (\<lambda>(x, y). x < 2 ^ LENGTH('a)) (assocs fn))"
  apply (simp add: assocs_def enum_word_def split_def filter_map)
  apply (rule map_cong)
   apply (simp add: o_def)
   apply (rule trans [OF _ filter_cong [OF refl]],
          rule sym, rule filter_to_shorter_upto)
    apply simp
   apply (rule iffI)
    apply (subst word_unat_power, rule of_nat_mono_maybe)
     apply simp
    apply assumption
   apply (simp add: word_less_nat_alt word_unat.Abs_inverse unats_def)
  apply clarsimp
  apply (simp add: word_less_nat_alt word_unat.Abs_inverse unats_def)
  apply (simp add: ucast_of_nat_small)
  done


lemma ucast_le_migrate:
  "\<lbrakk> y < 2 ^ size x; size x < size y \<rbrakk> \<Longrightarrow> (ucast x \<le> y) = (x \<le> ucast y)"
  for x :: "'a :: len word" and y :: "'b :: len word"
  apply (simp add: word_le_def ucast_def del: Word.of_int_uint)
  apply (subst word_uint.Abs_inverse)
   apply (simp add: uints_num word_size)
   apply (rule order_less_le_trans, rule uint_lt2p)
   apply simp
  apply (subst word_uint.Abs_inverse)
   apply (simp add: uints_num word_size word_less_alt uint_2p_alt)
  apply simp
  done


lemma obj_at_delete_objects:
  "\<lbrace>\<lambda>s. Q (obj_at (P (interrupt_irq_node s) (arch_state s)) r s) \<and>
        r \<notin> {ptr..ptr + 2 ^ bits - 1}\<rbrace>
   delete_objects ptr bits
   \<lbrace>\<lambda>_ s. Q (obj_at (P (interrupt_irq_node s) (arch_state s)) r s)\<rbrace>"
  apply (simp add: delete_objects_def do_machine_op_def split_def)
  apply wp
  apply (simp add: detype_machine_state_update_comm)
  done


(* FIXME: move *)
crunch arch [wp]: retype_region "\<lambda>s. P (arch_state s)"
  (simp: crunch_simps)

lemma set_free_index_final_cap:
  "\<lbrace>\<lambda>s. P (is_final_cap' False cap s) \<and> cte_wp_at ((=) src_cap) src s\<rbrace>
   set_cap (free_index_update f src_cap) src
   \<lbrace>\<lambda>rv s. P (is_final_cap' False cap s) \<rbrace>"
  apply (simp add:is_final_cap'_def2)
  apply (clarsimp simp:valid_def)
  apply (drule set_cap_caps_of_state_monad)
  apply (erule subst[rotated])
  apply (rule_tac f = P in arg_cong)
  apply (subgoal_tac "\<And>slot. (cte_wp_at (\<lambda>c. gen_obj_refs cap \<inter> gen_obj_refs c \<noteq> {}) slot s
          = cte_wp_at (\<lambda>c. gen_obj_refs cap \<inter> gen_obj_refs c \<noteq> {}) slot b)")
   apply simp
  apply (clarsimp split:cap.splits
         simp:cte_wp_at_caps_of_state free_index_update_def
              gen_obj_refs_def)
  done

lemma set_cap_orth:
  "\<lbrace>\<lambda>s. P s \<and> Q cap' s\<rbrace> set_cap cap src \<lbrace>\<lambda>rv s. Q cap' s\<rbrace> \<Longrightarrow>
   \<lbrace>\<lambda>s. P s \<and> src\<noteq> dest \<and> (cte_wp_at ((=) cap') dest s \<longrightarrow> Q cap' s)\<rbrace>
   set_cap cap src
   \<lbrace>\<lambda>rv s. cte_wp_at ((=) cap') dest s \<longrightarrow> Q cap' s\<rbrace>"
   apply (clarsimp simp:valid_def cte_wp_at_caps_of_state)
   apply (drule_tac x = s in spec)
   apply (frule set_cap_caps_of_state_monad)
   apply clarsimp
   apply (drule(1) bspec)
   apply clarsimp
   done


lemma set_cap_empty_tables[wp]:
  "\<lbrace>\<lambda>s. P (obj_at (empty_table (set (second_level_tables (arch_state s)))) p s)\<rbrace>
     set_cap cap cref
   \<lbrace>\<lambda>rv s. P (obj_at (empty_table (set (second_level_tables (arch_state s)))) p s)\<rbrace>"
  apply (rule hoare_pre)
   apply (rule hoare_use_eq [where f=arch_state, OF set_cap_arch])
   apply (wp set_cap_obj_at_impossible)
  apply (clarsimp simp: empty_table_caps_of)
  done


lemma cte_wp_at_eq_to_op_eq:
  "cte_wp_at (\<lambda>c. c = cap) = cte_wp_at ((=) cap)"
  by (simp add: cte_wp_at_caps_of_state fun_eq_iff)


lemma max_index_upd_caps_overlap_reserved:
  "\<lbrace>\<lambda>s. invs s \<and> S \<subseteq> untyped_range cap \<and>
       descendants_range_in S slot s \<and> cte_wp_at ((=) cap) slot s \<and> is_untyped_cap cap\<rbrace>
  set_cap (max_free_index_update cap) slot
  \<lbrace>\<lambda>rv. caps_overlap_reserved S\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp:is_cap_simps)
  apply (wp set_untyped_cap_caps_overlap_reserved)
  apply (auto simp:cte_wp_at_caps_of_state max_free_index_def)
  done


lemma max_index_upd_invs_simple:
  "\<lbrace>\<lambda>s. descendants_range_in (untyped_range cap) cref s \<and>
         pspace_no_overlap_range_cover (obj_ref_of cap) (cap_bits cap) s \<and>
         invs s \<and> cte_wp_at ((=) cap) cref s \<and>  is_untyped_cap cap\<rbrace>
   set_cap  (max_free_index_update cap) cref \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp:is_cap_simps)
  apply (wp set_untyped_cap_invs_simple)
  apply (auto simp:cte_wp_at_caps_of_state max_free_index_def)
  done


lemma sts_pspace_no_overlap [wp]:
  "\<lbrace>pspace_no_overlap S\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv. pspace_no_overlap S\<rbrace>"
  by (wp pspace_no_overlap_typ_at_lift)


lemma delete_objects_st_tcb_at:
  "\<lbrace>pred_tcb_at proj P t and invs and K (t \<notin> {ptr .. ptr + 2 ^ bits - 1})\<rbrace>
    delete_objects ptr bits
  \<lbrace>\<lambda>y. pred_tcb_at proj P t\<rbrace>"
  by (wp|simp add: delete_objects_def do_machine_op_def split_def)+


end
