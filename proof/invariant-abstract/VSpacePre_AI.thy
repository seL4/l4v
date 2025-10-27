(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
VSpace refinement
*)

theory VSpacePre_AI
imports ArchTcbAcc_AI
begin

arch_requalify_facts
  cap_master_cap_tcb_cap_valid_arch

lemma throw_on_false_wp[wp]:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. (rv \<longrightarrow> Q () s) \<and> (\<not> rv \<longrightarrow> E x s)\<rbrace>
    \<Longrightarrow> \<lbrace>P\<rbrace> throw_on_false x f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  apply (simp add: throw_on_false_def unlessE_def)
  apply wp
   apply simp
  apply simp
  done

crunch_ignore (add: throw_on_false)

definition
  "is_arch_update cap cap' \<equiv> is_arch_cap cap \<and> cap_master_cap cap = cap_master_cap cap'"


lemma dmo_asid_map [wp]:
  "\<lbrace>valid_asid_map\<rbrace> do_machine_op f \<lbrace>\<lambda>_. valid_asid_map\<rbrace>"
  apply (simp add: do_machine_op_def split_def)
  apply wp
  apply simp
  done

crunch do_machine_op
  for caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"

interpretation dmo: non_vspace_non_cap_op "do_machine_op f"
  by (unfold_locales; wp)

declare not_Some_eq_tuple[simp]

lemma pull_out_P:
  "P s \<and> (\<forall>c. caps_of_state s p = Some c \<longrightarrow> Q s c) \<longrightarrow> (\<forall>c. caps_of_state s p = Some c \<longrightarrow> P s \<and> Q s c)"
  by blast

lemma upto_enum_step_subtract:
  "x \<le> z \<Longrightarrow> [x, y .e. z] = (map ((+) x) [0, y - x .e. z - x])"
  by (auto simp add: upto_enum_step_def)

lemma invs_valid_irq_states[elim!]:
  "invs s \<Longrightarrow> valid_irq_states s"
  by(auto simp: invs_def valid_state_def)

(* FIXME: move to Word_Lib *)
lemma uint_ucast:
  "(x :: 'a :: len word) < 2 ^ LENGTH('b) \<Longrightarrow> uint (ucast x :: 'b :: len word) = uint x"
  by (metis Word.of_nat_unat mod_less of_nat_numeral semiring_1_class.of_nat_power unat_less_helper
            unat_ucast)

lemma pd_casting_shifting:
  "size x + n < len_of TYPE('a) \<Longrightarrow>
     ucast (ucast x << n >> n :: ('a :: len) word) = x"
  apply (rule word_eqI)
  apply (simp add: nth_ucast nth_shiftr nth_shiftl word_size)
  done

lemmas aligned_already_mask = is_aligned_andI1

lemma set_upto_enum_step_4:
  "set [0, 4 .e. x :: word32]
       = (\<lambda>x. x << 2) ` {.. x >> 2}"
  by (auto simp: upto_enum_step_def shiftl_t2n shiftr_div_2n_w
                 word_size mult.commute)

lemma set_upto_enum_step_8:
  "set [0, 8 .e. x :: word32]
       = (\<lambda>x. x << 3) ` {.. x >> 3}"
  by (auto simp: upto_enum_step_def shiftl_t2n shiftr_div_2n_w
                 word_size mult.commute)

lemma arch_update_cap_zombies:
  "\<lbrace>\<lambda>s. cte_wp_at (is_arch_update cap) p s \<and> zombies_final s\<rbrace> set_cap cap p \<lbrace>\<lambda>rv s. zombies_final s\<rbrace>"
  apply (simp add: zombies_final_def2 cte_wp_at_caps_of_state del: split_paired_All)
  apply wp
  apply (intro allI impI)
  apply (elim conjE exE)
  apply (simp del: split_paired_All add: is_arch_update_def split: if_split_asm)
    apply (erule_tac x=p in allE)
    apply (erule_tac x=p' in allE)
    apply simp
    apply (frule master_cap_obj_refs)
    apply (drule cap_master_cap_zombie)
    apply clarsimp
   apply (erule_tac x=pa in allE)
   apply (erule_tac x=p in allE)
   apply simp
   apply (frule master_cap_obj_refs)
   apply (drule cap_master_cap_zombie)
   apply clarsimp
  done

lemma arch_update_cap_pspace:
  "\<lbrace>cte_wp_at (is_arch_update cap and
               (\<lambda>c. is_valid_vtable_root c \<longrightarrow> is_valid_vtable_root cap)) p
    and valid_pspace and valid_cap cap\<rbrace>
     set_cap cap p
  \<lbrace>\<lambda>rv. valid_pspace\<rbrace>"
  apply (simp add: valid_pspace_def)
  apply (rule hoare_pre)
   apply (wp set_cap_valid_objs update_cap_iflive arch_update_cap_zombies)
  apply clarsimp
  apply (clarsimp simp: cte_wp_at_caps_of_state is_arch_update_def)
  apply (frule cap_master_cap_zobj_refs)
  apply clarsimp
  apply (drule caps_of_state_cteD)
  apply (drule (1) cte_wp_tcb_cap_valid)
  apply (clarsimp simp: cap_master_cap_tcb_cap_valid_arch)
  done

lemma arch_update_cap_valid_mdb:
  "\<lbrace>cte_wp_at (is_arch_update cap) p and valid_mdb\<rbrace> set_cap cap p \<lbrace>\<lambda>rv. valid_mdb\<rbrace>"
  apply (simp add: valid_mdb_def2 pred_conj_def)
  apply (rule hoare_lift_Pf2 [where f=cdt])
   prefer 2
   apply wp[1]
  apply (rule hoare_lift_Pf2 [where f=is_original_cap])
   prefer 2
   apply wp[1]
  apply (rule hoare_pre)
   apply wp
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (rule conjI)
   apply (clarsimp simp: mdb_cte_at_def is_arch_update_def)
   apply (fastforce simp: is_cap_simps)
  apply (rule conjI)
   apply (clarsimp simp: untyped_mdb_def is_arch_update_def)
   apply (rule conjI)
    apply (fastforce simp: is_cap_simps)
   apply clarsimp
   apply (drule master_cap_obj_refs)
   apply fastforce
  apply (rule conjI)
   apply (erule(1) descendants_inc_minor)
   apply (clarsimp simp:is_arch_update_def)
   apply (frule master_cap_class)
   apply (clarsimp dest!:master_cap_cap_range)
  apply (rule conjI)
   apply (clarsimp simp: untyped_inc_def is_arch_update_def)
  subgoal by (fastforce simp: is_cap_simps)
  apply (rule conjI)
   apply (clarsimp simp: ut_revocable_def)
   apply (clarsimp simp: is_arch_update_def is_cap_simps)
  apply (clarsimp simp: irq_revocable_def is_arch_update_def is_cap_simps simp del: split_paired_All)
  by (erule (2) valid_arch_mdb_same_master_cap[simplified fun_upd_def])


lemma set_cap_arch_obj:
  "\<lbrace>ko_at (ArchObj ao) p and cte_at p'\<rbrace> set_cap cap p' \<lbrace>\<lambda>_. ko_at (ArchObj ao) p\<rbrace>"
  apply (wp set_cap_obj_at_other)
  apply (clarsimp simp: obj_at_def cte_wp_at_cases)
  done

lemma set_mrs_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> set_mrs t buf mrs \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  apply (simp add: set_mrs_def zipWithM_x_mapM split_def
                   store_word_offs_def set_object_def get_object_def
              cong: option.case_cong
              split del: if_split)
  apply (wp hoare_vcg_split_case_option)
    apply (rule mapM_wp [where S=UNIV, simplified])
    apply (wp | simp)+
  apply (clarsimp simp: obj_at_def a_type_def
                  dest!: get_tcb_SomeD)
  done

lemma set_mrs_tcb[wp]:
  "\<lbrace> tcb_at t \<rbrace> set_mrs receiver recv_buf mrs \<lbrace>\<lambda>rv. tcb_at t \<rbrace>"
  by (simp add: tcb_at_typ, wp)


lemma set_mrs_ntfn_at[wp]:
  "\<lbrace> ntfn_at p \<rbrace> set_mrs receiver recv_buf mrs \<lbrace>\<lambda>rv. ntfn_at p \<rbrace>"
  by (simp add: ntfn_at_typ, wp)

end
