(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Arch_AC
imports ArchRetype_AC
begin

text\<open>

Setup for arch-specific access control.

\<close>

(* c.f.  auth_ipc_buffers *)
definition ipc_buffer_has_auth :: "'a PAS \<Rightarrow> obj_ref \<Rightarrow> obj_ref option \<Rightarrow> bool" where
   "ipc_buffer_has_auth aag thread \<equiv>
    case_option True (\<lambda>p. is_aligned p msg_align_bits \<and>
                          (\<forall>x \<in> ptr_range p msg_align_bits. abs_has_auth_to aag Write thread x))"

lemma ipc_buffer_has_auth_wordE:
  "\<lbrakk> ipc_buffer_has_auth aag thread (Some buf); p \<in> ptr_range (buf + off) sz;
     is_aligned off sz; sz \<le> msg_align_bits; off < 2 ^ msg_align_bits \<rbrakk>
     \<Longrightarrow> abs_has_auth_to aag Write thread p"
  unfolding ipc_buffer_has_auth_def
  by (fastforce elim: bspec set_mp[OF ptr_range_subset])

lemma is_transferable_ArchCap[simp]:
  "\<not> is_transferable (Some (ArchObjectCap cap))"
  using is_transferable.simps by simp

lemma mapM_set':
  assumes ip: "\<And>x y. \<lbrakk> x \<in> set xs; y \<in> set xs \<rbrakk> \<Longrightarrow> \<lbrace>I x and I y\<rbrace> f x \<lbrace>\<lambda>_. I y\<rbrace>"
  and rl: "\<And>s. (\<forall>x \<in> set xs. I x s) \<Longrightarrow> P s"
  shows "\<lbrace>\<lambda>s. (\<forall>x \<in> set xs. I x s)\<rbrace> mapM f xs \<lbrace>\<lambda>_. P\<rbrace>"
  apply (rule hoare_post_imp[OF rl])
   apply assumption
  apply (rule mapM_set)
    apply (rule hoare_pre)
     apply (rule hoare_vcg_ball_lift)
     apply (erule (1) ip)
    apply clarsimp
   apply (rule hoare_pre)
    apply (rule ip)
     apply assumption
    apply assumption
   apply clarsimp
  apply (rule hoare_pre)
   apply (rule ip)
    apply simp+
  done

lemma mapM_set'':
  assumes ip: "\<And>x y. \<lbrakk> x \<in> set xs; y \<in> set xs \<rbrakk> \<Longrightarrow> \<lbrace>I x and I y and Q\<rbrace> f x \<lbrace>\<lambda>_. I y and Q\<rbrace>"
  and rl: "\<And>s. (\<forall>x \<in> set xs. I x s) \<and> Q s \<Longrightarrow> P s"
  shows "\<lbrace>\<lambda>s. (\<forall>x \<in> set xs. I x s) \<and> Q s\<rbrace> mapM f xs \<lbrace>\<lambda>_. P\<rbrace>"
  apply (rule hoare_post_imp[OF rl])
   apply assumption
  apply (cases "xs = []")
   apply (simp add: mapM_Nil)
  apply (rule hoare_pre)
   apply (rule mapM_set'[where I = "\<lambda>x s. I x s \<and> Q s"])
    apply (rule hoare_pre)
     apply (rule ip[simplified pred_conj_def])
      apply (auto simp: neq_Nil_conv)
  done

lemma as_user_state_vrefs:
  "\<lbrace>pspace_aligned and valid_vspace_objs and valid_arch_state and (\<lambda>s. P (state_vrefs s))\<rbrace>
   as_user t f
   \<lbrace>\<lambda>_ s :: det_ext state. P (state_vrefs s)\<rbrace>"
  apply (simp add: as_user_def)
  apply (wpsimp wp: set_object_wp touch_object_wp')
  apply (clarsimp simp: state_vrefs_tcb_upd obj_at_def is_obj_defs ta_filter_def
                 elim!: rsubst[where P=P, OF _ ext]
                 dest!: get_tcb_SomeD)
  done

lemma as_user_pas_refined[wp]:
  "\<lbrace>pspace_aligned and valid_vspace_objs and valid_arch_state and pas_refined aag\<rbrace>
   as_user t f
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (simp add: pas_refined_def state_objs_to_policy_def)
  apply (rule hoare_pre)
   apply wps
   apply (wp as_user_state_vrefs)
  apply simp
  done

crunches set_message_info
  for pas_refined[wp]: "pas_refined aag"
  and cdt[wp]: "\<lambda>s. P (cdt s)"

crunches do_machine_op
  for thread_st_auth[wp]: "\<lambda>s. P (thread_st_auth s)"
  and state_vrefs[wp]: "\<lambda>s :: 'a :: state_ext state. P (state_vrefs s)"

(* FIXME: More instances of crunch not discovering the right precondition. -robs *)
lemma as_user_integrity_autarch:
  "\<lbrace>integrity aag X st and K (is_subject aag thread)\<rbrace>
   as_user thread info
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  by (wpsimp simp:as_user_def wp:set_object_integrity_autarch touch_object_wp')

lemma set_message_info_integrity_autarch:
  "\<lbrace>integrity aag X st and K (is_subject aag thread)\<rbrace>
   set_message_info thread info
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  by (wpsimp simp:set_message_info_def wp:as_user_integrity_autarch)

crunch integrity_autarch: set_message_info "integrity aag X st"

(* FIXME: move *)
lemma set_mrs_thread_st_auth[wp]:
  "set_mrs thread buf msgs \<lbrace>\<lambda>s. P (thread_st_auth s)\<rbrace>"
  supply if_split[split del]
  apply (simp add: set_mrs_def split_def set_object_def get_object_def)
  apply (wpsimp wp: gets_the_wp get_wp put_wp mapM_x_wp' touch_objects_wp touch_object_wp'
              simp: zipWithM_x_mapM_x split_def store_word_offs_def ta_filter_def obind_def)
  apply (frule get_tcb_SomeD')
  apply (insert get_tcb_True_False)
  apply (rename_tac s ko tcb)
  apply (erule_tac x="TCB ko" in meta_allE)
  apply (erule_tac x=thread in meta_allE)
  apply (erule_tac x=s in meta_allE)
  apply (clarsimp simp: fun_upd_def[symmetric] thread_st_auth_preserved obj_at_def)
  done

lemma set_mrs_thread_bound_ntfns[wp]:
  "set_mrs thread buf msgs \<lbrace>\<lambda>s. P (thread_bound_ntfns s)\<rbrace>"
  supply if_split[split del]
  apply (simp add: set_mrs_def split_def set_object_def get_object_def )
  apply (wpsimp wp: gets_the_wp get_wp put_wp mapM_x_wp' dmo_wp touch_objects_wp touch_object_wp'
              simp: zipWithM_x_mapM_x split_def store_word_offs_def no_irq_storeWord ta_filter_def)
  apply (frule get_tcb_SomeD')
  apply clarsimp
  apply (insert get_tcb_True_False)
  apply (rename_tac s ko tcb)
  apply (erule_tac x="TCB ko" in meta_allE)
  apply (erule_tac x=thread in meta_allE)
  apply (erule_tac x=s in meta_allE)
  apply (clarsimp simp: fun_upd_def[symmetric] thread_bound_ntfns_preserved obj_at_def)
  done

lemma delete_objects_pspace_no_overlap:
  "\<lbrace>pspace_aligned and valid_objs and (\<lambda>s. \<exists>idx. cte_wp_at ((=) (UntypedCap dev ptr sz idx)) slot s)\<rbrace>
   delete_objects ptr sz
   \<lbrace>\<lambda>_. pspace_no_overlap_range_cover ptr sz\<rbrace>"
  unfolding delete_objects_def do_machine_op_def
  apply (wp | simp add: split_def detype_machine_state_update_comm)+
  apply (clarsimp)
  apply (rule pspace_no_overlap_detype)
    apply (auto dest: cte_wp_at_valid_objs_valid_cap)
  done

lemma delete_objects_invs_ex:
  "\<lbrace>invs and ct_active and
    (\<lambda>s. \<exists>slot dev f. cte_wp_at ((=) (UntypedCap dev ptr bits f)) slot s \<and>
                      descendants_range (UntypedCap dev ptr bits f) slot s)\<rbrace>
   delete_objects ptr bits
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (erule use_valid)
   apply wp
  apply auto
  done

lemma is_subject_asid_into_loas:
  "\<lbrakk> is_subject_asid aag asid; pas_refined aag s \<rbrakk>
     \<Longrightarrow> label_owns_asid_slot aag (pasSubject aag) asid"
  unfolding label_owns_asid_slot_def
  by (clarsimp simp: pas_refined_refl)


locale Arch_AC_1 =
  assumes set_mrs_state_vrefs[wp]:
    "\<lbrace>pspace_aligned and valid_vspace_objs and valid_arch_state and (\<lambda>s. P (state_vrefs s))\<rbrace>
     set_mrs thread buf msgs
     \<lbrace>\<lambda>_ s :: det_ext state. P (state_vrefs s)\<rbrace>"
  and mul_add_word_size_lt_msg_align_bits_ofnat:
  "\<lbrakk> p < 2 ^ (msg_align_bits - word_size_bits); k < word_size \<rbrakk>
     \<Longrightarrow> of_nat p * of_nat word_size + k < (2 :: obj_ref) ^ msg_align_bits"
  and zero_less_word_size[simp]:
    "0 < (word_size :: obj_ref)"

context Arch_AC_1 begin

lemmas mul_word_size_lt_msg_align_bits_ofnat =
  mul_add_word_size_lt_msg_align_bits_ofnat[where k=0, simplified]

lemmas ptr_range_off_off_mems =
  ptr_range_add_memI[OF _ mul_word_size_lt_msg_align_bits_ofnat]
  ptr_range_add_memI[OF _ mul_add_word_size_lt_msg_align_bits_ofnat, simplified add.assoc[symmetric]]

lemma dmo_storeWord_respects_Write:
  "\<lbrace>integrity aag X st and K (\<forall>p' \<in> ptr_range p word_size_bits. aag_has_auth_to aag Write p')\<rbrace>
   do_machine_op (storeWord p v)
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (rule hoare_pre)
  apply (wp dmo_wp storeWord_respects)
  apply simp
  done

lemma store_word_offs_integrity_autarch:
  "\<lbrace>\<lambda>s. integrity aag X st s \<and> is_subject aag thread \<and>
        ipc_buffer_has_auth aag thread (Some buf) \<and>
        r < 2 ^ (msg_align_bits - word_size_bits)\<rbrace>
   store_word_offs buf r v
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: store_word_offs_def)
  apply (rule hoare_pre)
   apply (wp dmo_storeWord_respects_Write touch_objects_wp)
  apply clarsimp
  apply (drule (1) ipc_buffer_has_auth_wordE)
     apply (simp add: word_size_word_size_bits is_aligned_mult_triv2)
    apply (simp add: msg_align_bits')
   apply (erule mul_word_size_lt_msg_align_bits_ofnat)
  apply simp
  done

lemma set_mrs_pas_refined[wp]:
  "\<lbrace>pspace_aligned and valid_vspace_objs and valid_arch_state and pas_refined aag\<rbrace>
   set_mrs thread buf msgs
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (simp add: pas_refined_def state_objs_to_policy_def)
  apply (rule hoare_pre)
   apply (wp | wps)+
  apply (clarsimp dest!: auth_graph_map_memD)
  done

lemma copy_mrs_integrity_autarch:
  "\<lbrace>pas_refined aag and integrity aag X st and
    K (is_subject aag receiver \<and> ipc_buffer_has_auth aag receiver rbuf \<and>
       unat n < 2 ^ (msg_align_bits - word_size_bits))\<rbrace>
   copy_mrs sender sbuf receiver rbuf n
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: copy_mrs_def cong: if_cong split del: if_split)
  apply (wpsimp wp: mapM_wp' as_user_integrity_autarch
                    store_word_offs_integrity_autarch[where thread=receiver]
         | fastforce)+
    sorry (* FIXME: broken by touched-addrs -robs
  done
*)

lemma set_mrs_integrity_autarch:
  "\<lbrace>integrity aag X st and K (is_subject aag thread \<and> ipc_buffer_has_auth aag thread buf)\<rbrace>
   set_mrs thread buf msgs
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: set_mrs_def split del: if_split)
  apply (wpsimp wp: gets_the_wp get_wp put_wp mapM_x_wp'
                    store_word_offs_integrity_autarch[where thread=thread]
              simp: split_def zipWithM_x_mapM_x split_del: if_split)+
     apply (clarsimp elim!: in_set_zipE split: if_split_asm)
     apply (rule order_le_less_trans[where y=msg_max_length])
      apply (fastforce simp add: le_eq_less_or_eq)
     apply (simp add: msg_max_length_def msg_align_bits' word_size_bits_def)
    apply simp
    apply (wp set_object_integrity_autarch hoare_drop_imps hoare_vcg_all_lift)+
  apply simp
  done

end

end
