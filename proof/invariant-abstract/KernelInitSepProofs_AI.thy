(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory KernelInitSepProofs_AI (* unused and broken, kept here for future reference *)
imports
  KernelInitSep_AI
  CSpaceInv_AI
  "ASpec.KernelInit_A"
begin

lemma propagate_do_kernel_op:
  "do_kernel_op (A >>= B) = ((do_kernel_op A) >>=E (\<lambda>x. do_kernel_op (B x)))"
  by (clarsimp simp: do_kernel_op_def bind_assoc liftE_bindE split_def)
     (fastforce intro!: ext intro: select_bind_eq2 bind_apply_cong
               simp: liftE_def bind_assoc exec_gets exec_modify
                     bind_select_f_bind[symmetric])

text \<open>Lifting rule for wp. Note: apply @{text "hoare_pre"} first.\<close>
lemma do_kernel_op_wp:
  "\<lbrakk> \<And>kis. \<lbrace> \<lambda>s. P kis s \<rbrace> f \<lbrace> \<lambda>rv s. Q rv (kis \<lparr> ki_kernel_state := s \<rparr>) \<rbrace> \<rbrakk>
   \<Longrightarrow>\<lbrace> \<lambda>kis. P kis (ki_kernel_state kis) \<rbrace> do_kernel_op f \<lbrace> Q \<rbrace>,\<lbrace> E \<rbrace>"
  unfolding do_kernel_op_def split_def
  by wp (fastforce elim: use_valid)


section \<open>Deriving Frame Rules for @{term set_cap_local} and
           @{term get_cap_local}\<close>

lemma ki_get_cap:
  "\<lbrace> \<lambda>s. sep_map_cap atyp cptr cap (lift_sep_state s) \<rbrace>
   do_kernel_op (get_cap_local cptr)
   \<lbrace> \<lambda>rv s. sep_map_cap atyp cptr cap (lift_sep_state s) \<and> rv = cap \<rbrace>, \<lbrace> E \<rbrace>"
  apply (rule hoare_pre)
  apply (rule do_kernel_op_wp)
  apply (simp add: get_cap_local_def split_def)
  apply (wp get_object_wp | wpc)+
  apply clarsimp
  apply (cases cptr, clarsimp, drule sep_map_capD, clarsimp simp: obj_at_def)
  apply (clarsimp simp: obj_at_def sep_map_cap_def sep_state_accessors
                        lift_sep_state_def split: option.splits)
  apply (fastforce simp: cap_of_def)
  done

lemma ki_get_cap_frame:
  "\<lbrace> \<lambda>s. (sep_map_cap atyp cptr cap \<and>* P) (lift_sep_state s) \<rbrace>
   do_kernel_op (get_cap_local cptr)
   \<lbrace> \<lambda>rv s. (sep_map_cap atyp cptr cap \<and>* P) (lift_sep_state s)
            \<and> rv = cap \<rbrace>,\<lbrace> E \<rbrace>"
  apply (rule hoare_pre)
  apply (rule do_kernel_op_wp)
   apply (simp add: get_cap_local_def split_def)
   apply (wp get_object_wp | wpc)+
  apply (cases cptr, rename_tac p i)
  apply (clarsimp dest!: sep_map_cap'_ocm_has_capI split: sep_state.splits
                  simp: obj_at_def ocm_has_cap_def lift_sep_state_def
                        sep_state_accessors ko_has_cap_def
                        cap_of_ko_clean_contained_cap)
  apply (fastforce simp: cap_of_def a_base_type_cmp_of_def)
  done

lemma ki_set_obj_under':
  "\<lbrace>\<lambda>s. \<exists>old_cap. (sep_map_cap atyp (p,i) old_cap \<and>* P) (kis_lift kis s)
        \<and> set_ko_cap (the (kheap s p)) i cap = ko
        \<and> a_base_type (the (kheap s p)) = a_base_type ko \<rbrace>
   set_object p ko
   \<lbrace>\<lambda>_ s. (sep_map_cap atyp (p,i) cap \<and>* P) (kis_lift kis s)\<rbrace>"
  unfolding set_object_def
  apply wp
  apply (clarsimp simp: fun_upd_def[symmetric])
  apply (frule sep_map_cap'_ocm_has_capI)
  apply (drule_tac cap=cap in sep_map_cap_update_cap')
  apply (clarsimp simp: sep_update_cap_def lift_sep_state_def
                  split: sep_state.splits)
  apply (erule_tac P="sep_map_cap atyp (p, i) cap \<and>* P" in subst[rotated])
  apply (clarsimp intro!: ext simp: sep_state_accessors ocm_has_cap_def
                  simp: ko_clean_set_ko_cap ko_has_cap_def
                  split: option.splits)
  done

lemma ki_set_cap_frame:
  "\<lbrace> \<lambda>s. ((\<lambda>s. \<exists>old_cap. sep_map_cap atyp cptr old_cap s) \<and>* P)
            (lift_sep_state s) \<rbrace>
   do_kernel_op (set_cap_local cap cptr)
   \<lbrace> \<lambda>_ s. (sep_map_cap atyp cptr cap \<and>* P) (lift_sep_state s) \<rbrace>, \<lbrace> E \<rbrace>"
  apply (cases cptr, rename_tac p i)
  apply (rule hoare_pre)
  apply (rule do_kernel_op_wp)
   apply (simp add: set_cap_local_def split_def)
   apply (wp ki_set_obj_under' get_object_wp | wpc)+
  apply (clarsimp simp: sep_conj_exists)
  apply (frule sep_map_cap'_ocm_has_capI)
  apply (clarsimp simp: sep_state_accessors ocm_has_cap_def
                        lift_sep_state_def obj_at_def
                  split: sep_state.splits)
  apply (rule conjI)
   apply (fastforce simp: set_ko_cap_def intro!: ext)
  apply (auto simp: set_ko_cap_def ko_has_cap_def)
  done

lemma tcb_set_cap_local_via_explosion:
  "\<lbrace> \<lambda>s. (sep_map_ko p (TCB tcb) \<and>* P) (lift_sep_state s)
         \<and> cap_of (TCB tcb) i = Some old_cap
         \<and> valid_cnode_index (TCB tcb) i \<rbrace>
   do_kernel_op (set_cap_local cap (p,i))
   \<lbrace> \<lambda>_ s. (sep_map_ko p (set_ko_cap (TCB tcb) i cap) \<and>* P) (lift_sep_state s) \<rbrace>, \<lbrace> E \<rbrace>"
  unfolding sep_map_ko_def
  apply (rule hoare_gen_asmE'[simplified K_def pred_conj_def])
  apply (clarsimp simp: a_base_type_cmp_of_def)
  apply (rule_tac E=E in hoare_strengthen_postE)
    apply (rule hoare_pre)
     apply (rule ki_set_cap_frame)
    apply (clarsimp simp only: sep_conj_exists)
    apply (rule_tac x=old_cap in exI)
    apply (subst (asm) sep_map_base_subset_explode_eq[where cmps'="{cmp_of (TCB tcb) i}"])
       apply (fastforce simp: insert_commute a_base_type_cmp_of_def
                        intro: singleton_subsetI
                        dest: abt_valid_cnode_index_in_components)+
    apply (clarsimp simp: sep_conj_assoc) \<comment> \<open>flatten\<close>
    apply (sep_rule sep_map_base_sep_map_capI'[where ko="TCB tcb"])
     apply simp+
   apply (clarsimp simp: a_base_type_cmp_of_def split: if_split_asm)
   apply sep_cancel
   apply (sep_select_asm 2)
   apply (drule abt_valid_cnode_index_in_components)
   apply (drule sep_map_base_sep_map_cap_implode)
     apply (fastforce simp: insert_commute a_base_type_cmp_of_def)+
  done

lemma cnode_set_cap_local_via_explosion:
  "\<lbrace> \<lambda>s. (sep_map_ko p (CNode sz cn) \<and>* P) (lift_sep_state s)
         \<and> cap_of (CNode sz cn) i = Some old_cap
         \<and> valid_cnode_index (CNode sz cn) i \<rbrace>
   do_kernel_op (set_cap_local cap (p,i))
   \<lbrace> \<lambda>_ s. (sep_map_ko p (set_ko_cap (CNode sz cn) i cap) \<and>* P) (lift_sep_state s) \<rbrace>, \<lbrace> E \<rbrace>"
  unfolding sep_map_ko_def
  apply (rule hoare_gen_asmE'[simplified K_def pred_conj_def])
   \<comment> \<open>concludes zero-sized cnode case\<close>
   apply (rule_tac E=E in hoare_strengthen_postE)
     apply (rule hoare_pre)
      apply (rule ki_set_cap_frame)
     apply (clarsimp simp only: sep_conj_exists)
     apply (rule_tac x=old_cap in exI)
     apply (subst (asm) sep_map_base_subset_explode_eq[where cmps'="{cmp_of (CNode sz cn) i}"])
       apply (fastforce simp: insert_commute a_base_type_cmp_of_def
                              abt_valid_cnode_index_def insert_same_length_id)
      apply simp
     apply (clarsimp simp: sep_conj_assoc a_base_type_cmp_of_def) \<comment> \<open>flatten\<close>
     apply (sep_rule sep_map_base_sep_map_capI'[where ko="CNode sz cn"])
        apply (simp add: a_base_type_cmp_of_def)+
    apply (clarsimp simp: valid_cnode_index_def)
   apply sep_cancel
   apply (sep_select_asm 2)
   apply (simp split: if_split_asm)
    apply (drule sep_map_cap_sep_map_base[where ko="CNode 0 cn"])
     apply simp
    apply (simp add: bl_length_set_equal)
   apply (drule bl_length_set_equal, simp add: a_base_type_cmp_of_def)
   apply (drule sep_map_base_sep_map_cap_implode)
    apply (fastforce simp: insert_commute a_base_type_cmp_of_def
                            abt_valid_cnode_index_def insert_same_length_id)+
  done

lemma set_cap_local_via_explosion:
  "\<lbrace> \<lambda>s. (sep_map_ko p ko \<and>* P) (lift_sep_state s)
         \<and> cap_of ko i = Some old_cap
         \<and> valid_cnode_index ko i \<rbrace>
   do_kernel_op (set_cap_local cap (p,i))
   \<lbrace> \<lambda>_ s. (sep_map_ko p (set_ko_cap ko i cap) \<and>* P) (lift_sep_state s) \<rbrace>,\<lbrace> E \<rbrace>"
  apply (cases ko, simp_all add: cap_of_def)
   apply (insert cnode_set_cap_local_via_explosion)
   apply (fastforce simp: cap_of_def)
  apply (insert tcb_set_cap_local_via_explosion)
  apply (fastforce simp: cap_of_def)
  done


section \<open>EXPERIMENTAL\<close>

lemma sep_map_ko_tcb_explode:
  "sep_map_ko p (TCB tcb) s
   \<Longrightarrow> (sep_map_base p (TCB tcb) {[]}
        \<and>* sep_map_cap ATCB (p, tcb_cnode_index 0) (tcb_ctable tcb)
        \<and>* sep_map_cap ATCB (p, tcb_cnode_index 1) (tcb_vtable tcb)
        \<and>* sep_map_cap ATCB (p, tcb_cnode_index 2) (tcb_reply tcb)
        \<and>* sep_map_cap ATCB (p, tcb_cnode_index 3) (tcb_caller tcb)
        \<and>* sep_map_cap ATCB (p, tcb_cnode_index 4) (tcb_ipcframe tcb)
       ) s"
  unfolding sep_map_ko_def
  apply clarsimp
  apply (subst (asm) sep_map_base_subset_explode_eq[where cmps'="{[]}"])
       apply (fastforce simp: insert_commute a_base_type_cmp_of_def
                        intro: singleton_subsetI)+
  apply (sep_cancel, clarsimp simp: insert_commute)

  apply (subst (asm) sep_map_base_subset_explode_eq[where cmps'="{tcb_cnode_index 0}"])
       apply (fastforce simp: insert_commute a_base_type_cmp_of_def
                        intro: singleton_subsetI)+
  apply (clarsimp simp: insert_commute)
  apply (drule sep_map_base_sep_map_capI')
   apply (fastforce simp: a_base_type_cmp_of_def cap_of_def tcb_cnode_map_def)+
  apply (clarsimp simp: a_base_type_def)
  apply (sep_cancel)

  apply (subst (asm) sep_map_base_subset_explode_eq[where cmps'="{tcb_cnode_index 1}"])
       apply (fastforce simp: insert_commute a_base_type_cmp_of_def
                        intro: singleton_subsetI)+
  apply (clarsimp simp: insert_commute)
  apply (drule sep_map_base_sep_map_capI')
   apply (fastforce simp: a_base_type_cmp_of_def cap_of_def tcb_cnode_map_def)+
  apply (clarsimp simp: a_base_type_def)
  apply (sep_cancel)

  apply (subst (asm) sep_map_base_subset_explode_eq[where cmps'="{tcb_cnode_index 2}"])
       apply (fastforce simp: insert_commute a_base_type_cmp_of_def
                        intro: singleton_subsetI)+
  apply (clarsimp simp: insert_commute)
  apply (drule sep_map_base_sep_map_capI')
   apply (fastforce simp: a_base_type_cmp_of_def cap_of_def tcb_cnode_map_def)+
  apply (clarsimp simp: a_base_type_def)
  apply (sep_cancel)

  apply (subst (asm) sep_map_base_subset_explode_eq[where cmps'="{tcb_cnode_index 3}"])
       apply (fastforce simp: insert_commute a_base_type_cmp_of_def
                        intro: singleton_subsetI)+
  apply (clarsimp simp: insert_commute)
  apply (drule sep_map_base_sep_map_capI')
   apply (fastforce simp: a_base_type_cmp_of_def cap_of_def tcb_cnode_map_def)+
  apply (clarsimp simp: a_base_type_def)
  apply (sep_cancel)

  apply (drule sep_map_base_sep_map_capI)
   apply (fastforce simp: a_base_type_cmp_of_def cap_of_def tcb_cnode_map_def)+
  done
  (* FIXME: lots of automation opportunities here, assuming this lemma is
            at all useful! *)

text \<open>
  TODO:
  Think on improving notation (arrows etc)

  Relationship between a_base_type and a_type,
    wellformed cnodes and bounded_ko,
    t_obj_bits and obj_bits
\<close>

end
