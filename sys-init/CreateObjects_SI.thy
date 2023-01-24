(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory CreateObjects_SI
imports
  "DSpecProofs.Retype_DP"
  ObjectInitialised_SI
  RootTask_SI
  SysInit_SI
begin

(*********************************************************
 * Rewriting the seL4_Untyped_Retype_sep rule to include *
 * that it doesn't delete anything from the CDT.         *
 *********************************************************)

lemma seL4_Untyped_Retype_has_children_wp:
  "\<lbrakk>untyped_cptr < 2 ^ si_cnode_size; ncptr < 2 ^ si_cnode_size\<rbrakk>
   \<Longrightarrow>
  \<lbrace>\<lambda>s. (nt\<noteq> UntypedType \<and> default_object nt (unat ts) minBound = Some obj
    \<and> free_range\<subseteq> tot_free_range) \<and>
    \<guillemotleft>si_tcb_id \<mapsto>f (Tcb tcb)
    \<and>* (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap
    \<and>* (cap_object si_cnode_cap \<mapsto>f CNode (empty_cnode si_cnode_size))
    \<and>* (si_cnode_id, unat untyped_cptr) \<mapsto>c UntypedCap dev obj_range free_range
    \<and>* (si_cnode_id, unat ncptr ) \<mapsto>c NullCap
    \<and>* (\<And>* ptr\<in>tot_free_range. ptr \<mapsto>o Untyped)
    \<and>* (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cnode_cap
    \<and>* (cap_object si_cnode_cap, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap
    \<and>* R\<guillemotright> s \<and>
    (\<not> has_children (si_cnode_id,unat untyped_cptr) (kernel_state s) \<longrightarrow> obj_range = free_range) \<and>
    has_children parent (kernel_state s)\<rbrace>
    seL4_Untyped_Retype untyped_cptr nt ts
                         seL4_CapInitThreadCNode node_index 0 ncptr 1
  \<lbrace>\<lambda>rv s. has_children parent (kernel_state s)\<rbrace>"
  apply (clarsimp simp: has_children_def is_cdt_parent_def)
  apply (subst ex_conj_increase)+
  apply (rule hoare_vcg_ex_lift)+
  apply (rule hoare_chain)
    apply (rule seL4_Untyped_Retype_inc_no_preempt
                [where root_size=si_cnode_size and root_cnode_cap=si_cnode_cap and obj = obj
                    and ncptr = ncptr and free_range = free_range and tot_free_range = tot_free_range
                    and obj_range = obj_range])
   apply ((intro conjI impI | simp
      | clarsimp simp: guard_equal_si_cnode_cap offset_slot_si_cnode_size' )+)
    apply (clarsimp simp: has_children_def is_cdt_parent_def)
   apply fastforce
  apply simp
  done

lemma seL4_Untyped_Retype_list_all_has_children_index_wp:
  "\<lbrakk>untyped_cptr < 2 ^ si_cnode_size; ncptr < 2 ^ si_cnode_size\<rbrakk>
   \<Longrightarrow>
  \<lbrace>\<lambda>s. (nt\<noteq> UntypedType \<and> default_object nt (unat object_size) minBound = Some obj
    \<and> free_range\<subseteq> tot_free_range) \<and>
    \<guillemotleft>si_tcb_id \<mapsto>f (Tcb tcb)
    \<and>* (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap
    \<and>* (cap_object si_cnode_cap \<mapsto>f CNode (empty_cnode si_cnode_size))
    \<and>* (si_cnode_id, unat untyped_cptr) \<mapsto>c UntypedCap dev obj_range free_range
    \<and>* (si_cnode_id, unat ncptr ) \<mapsto>c NullCap
    \<and>* (\<And>* ptr\<in>tot_free_range. ptr \<mapsto>o Untyped)
    \<and>* (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cnode_cap
    \<and>* (cap_object si_cnode_cap, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap
    \<and>* R\<guillemotright> s \<and>
    (\<not> has_children (si_cnode_id,unat untyped_cptr) (kernel_state s) \<longrightarrow> obj_range = free_range) \<and>
    list_all (\<lambda>index. has_children (cnode_id, untyped_slots!index) (kernel_state s)) indices\<rbrace>
     seL4_Untyped_Retype untyped_cptr nt object_size
                         seL4_CapInitThreadCNode node_index 0 ncptr 1
   \<lbrace>\<lambda>rv s. list_all (\<lambda>index. has_children (cnode_id, untyped_slots!index) (kernel_state s)) indices\<rbrace>"
  apply (case_tac "indices=[]", simp_all)
   apply (rule hoare_TrueI)
  apply (clarsimp simp: Ball_set_list_all[symmetric])
  apply (subst Ball_conj_increase, simp)+
  apply (rule hoare_vcg_ball_lift)
  apply (rule hoare_pre)
   apply (rule seL4_Untyped_Retype_has_children_wp[where free_range = free_range
                and obj_range = obj_range and tot_free_range = tot_free_range])
    by auto


lemma seL4_Untyped_Retype_sep_cdt_inc:
  "\<lbrakk>untyped_cptr < 2 ^ si_cnode_size;
    ncptr < 2 ^ si_cnode_size\<rbrakk>
  \<Longrightarrow> \<lbrace>\<lambda>s. (nt\<noteq> UntypedType \<and> default_object nt (unat ts) minBound = Some obj
    \<and> free_range\<subseteq> tot_free_range) \<and>
    \<guillemotleft>si_tcb_id \<mapsto>f (Tcb tcb)
  \<and>* (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap
  \<and>* (cap_object si_cnode_cap \<mapsto>f CNode (empty_cnode si_cnode_size))
  \<and>* (si_cnode_id, unat untyped_cptr) \<mapsto>c UntypedCap dev obj_range free_range
  \<and>* (si_cnode_id, unat ncptr ) \<mapsto>c NullCap
  \<and>* (\<And>* ptr\<in>tot_free_range. ptr \<mapsto>o Untyped)
  \<and>* (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cnode_cap
  \<and>* (cap_object si_cnode_cap, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap
  \<and>* R\<guillemotright> s \<and>
    (\<not> has_children (si_cnode_id,unat untyped_cptr) (kernel_state s) \<longrightarrow> obj_range = free_range) \<and>
    list_all (\<lambda>index. has_children (si_cnode_id, untyped_slots!index) (kernel_state s)) indices\<rbrace>
  seL4_Untyped_Retype untyped_cptr nt ts
                      seL4_CapInitThreadCNode node_index 0
                      ncptr 1
  \<lbrace>\<lambda>r s. (\<not> r \<longrightarrow> (\<exists>oid free_range'. (\<guillemotleft>
     (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap
  \<and>* si_tcb_id \<mapsto>f (Tcb tcb)
  \<and>* (si_cnode_id, unat ncptr) \<mapsto>c (default_cap nt {oid} (unat ts) dev)
  \<and>* oid \<mapsto>o obj
  \<and>* (cap_object si_cnode_cap \<mapsto>f CNode (empty_cnode si_cnode_size))
  \<and>* (\<And>* ptr\<in>tot_free_range - {oid}. ptr \<mapsto>o Untyped)
  \<and>* (si_cnode_id, unat untyped_cptr) \<mapsto>c UntypedCap dev obj_range free_range'
  \<and>* (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cnode_cap
  \<and>* (cap_object si_cnode_cap, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap
  \<and>* R \<guillemotright> s ) \<and> free_range' \<subseteq> free_range - {oid} \<and> oid \<in> free_range)
  \<and> has_children (si_cnode_id,unat untyped_cptr) (kernel_state s))
  \<and> (r \<longrightarrow> (\<guillemotleft>
     (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap
  \<and>* si_tcb_id \<mapsto>f (Tcb tcb)
  \<and>* (cap_object si_cnode_cap \<mapsto>f CNode (empty_cnode si_cnode_size))
  \<and>* (si_cnode_id,unat untyped_cptr) \<mapsto>c UntypedCap dev obj_range free_range
  \<and>* (si_cnode_id, unat ncptr) \<mapsto>c NullCap
  \<and>* (\<And>* ptr\<in>tot_free_range. ptr \<mapsto>o Untyped)
  \<and>* (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cnode_cap
  \<and>* (cap_object si_cnode_cap, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap
  \<and>* R \<guillemotright> s )
  \<and> (\<not>has_children (si_cnode_id,unat untyped_cptr) (kernel_state s) \<longrightarrow> obj_range = free_range)) \<and>
    list_all (\<lambda>index. has_children (si_cnode_id, untyped_slots!index) (kernel_state s)) indices  \<rbrace>"
  apply (rule hoare_chain)
    apply (rule hoare_vcg_conj_lift, rule seL4_Untyped_Retype_sep [where
                root_cnode=si_cnode_id and
                root_cnode_cap=si_cnode_cap and
                root_size=si_cnode_size and
                ucptr_slot="unat untyped_cptr" and
                ncptr=ncptr and
                obj_range=obj_range and
                tot_free_range=tot_free_range and
                free_range=free_range and
                obj=obj and
                P=R], (simp add: offset_slot' guard_equal_si_cnode_cap)+)
     apply (rule seL4_Untyped_Retype_list_all_has_children_index_wp
       [where tcb=tcb and
              cnode_id=si_cnode_id and
              untyped_slots=untyped_slots and
              indices=indices and
              obj_range=obj_range and
              free_range=free_range], simp)
    apply clarsimp
   apply clarsimp
   apply auto
  done

(*****************************************************
 * End of rewriting the seL4_Untyped_Retype_sep rule *
 *****************************************************)

lemma has_children_map_le:
  "\<lbrakk>cdl_cdt s \<subseteq>\<^sub>m cdl_cdt s'; has_children cap_ref s\<rbrakk>
  \<Longrightarrow> has_children cap_ref s'"
  apply (clarsimp simp: has_children_def is_cdt_parent_def)
  apply (rule_tac x=a in exI)
  apply (rule_tac x=b in exI)
  apply (clarsimp simp: map_le_def)
  by (metis domIff option.distinct(1))

lemma retype_untyped_wp:
  "\<lbrakk>default_object type sz minBound = Some new_object;
    available_ids \<subseteq> all_available_ids;
    free_cptr < 2 ^ si_cnode_size;
    untyped_cptr < 2 ^ si_cnode_size;
    sz < 2 ^ word_bits;
    type \<noteq> UntypedType\<rbrakk>
  \<Longrightarrow>
   \<lbrace>\<lambda>s. \<guillemotleft>(si_cnode_id, unat untyped_cptr) \<mapsto>c UntypedCap dev cover_ids available_ids \<and>*
    (\<And>* obj_id \<in> all_available_ids. (obj_id \<mapsto>o Untyped)) \<and>*
    (si_cnode_id, unat free_cptr) \<mapsto>c NullCap \<and>*
     si_tcb_id \<mapsto>f root_tcb \<and>*
    (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
    (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*
     si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
    (si_cnode_id, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap \<and>* R\<guillemotright> s \<and>
   (\<not>has_children (si_cnode_id,unat untyped_cptr) (kernel_state s) \<longrightarrow> cover_ids = available_ids) \<and>
     list_all (\<lambda>index. has_children (si_cnode_id, untyped_slots ! index) (kernel_state s)) indices\<rbrace>
     retype_untyped free_cptr untyped_cptr type sz
   \<lbrace>\<lambda>rv s. (\<not>rv \<longrightarrow> (\<exists>new_id available_ids'.
     new_id \<in> available_ids \<and> available_ids' \<subseteq> available_ids - {new_id} \<and>
    \<guillemotleft>(si_cnode_id, unat untyped_cptr) \<mapsto>c UntypedCap dev cover_ids available_ids' \<and>*
    (\<And>* obj_id \<in> all_available_ids - {new_id}. (obj_id \<mapsto>o Untyped)) \<and>*
     new_id \<mapsto>o new_object \<and>*
    (si_cnode_id, unat free_cptr) \<mapsto>c default_cap type {new_id} sz dev \<and>*
     si_tcb_id \<mapsto>f root_tcb \<and>*
    (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
    (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*
     si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
    (si_cnode_id, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap \<and>* R \<guillemotright> s) \<and>
    has_children (si_cnode_id,unat untyped_cptr) (kernel_state s) \<and>
     list_all (\<lambda>index. has_children (si_cnode_id, untyped_slots ! index) (kernel_state s)) indices) \<and>
   (rv \<longrightarrow>
    \<guillemotleft>(si_cnode_id, unat untyped_cptr) \<mapsto>c UntypedCap dev cover_ids available_ids \<and>*
    (\<And>* obj_id \<in> all_available_ids. (obj_id \<mapsto>o Untyped)) \<and>*
    (si_cnode_id, unat free_cptr) \<mapsto>c NullCap \<and>*
     si_tcb_id \<mapsto>f root_tcb \<and>*
    (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
    (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*
     si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
    (si_cnode_id, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap \<and>* R\<guillemotright> s \<and>
   (\<not>has_children (si_cnode_id,unat untyped_cptr) (kernel_state s) \<longrightarrow> cover_ids = available_ids) \<and>
     list_all (\<lambda>index. has_children (si_cnode_id, untyped_slots ! index) (kernel_state s)) indices)\<rbrace>"
  (* I would like to remove this later by rewriting seL4_Untyped_Retype_sep *)
  apply (subgoal_tac "si_cspace_cap=si_cnode_cap", simp)
   apply (unfold retype_untyped_def)
   apply (rule hoare_chain)
     apply (rule seL4_Untyped_Retype_sep_cdt_inc [where free_range = available_ids and
                                              tot_free_range = all_available_ids and
                                              untyped_slots=untyped_slots and
                                              indices=indices and
                                              obj = new_object and
                                              obj_range=cover_ids and
                                              tcb="obj_tcb root_tcb" and R=R],
           (assumption|simp add: unat_of_nat32 |rule offset_slot' [symmetric] guard_equal_si_cnode_cap)+)
    apply clarsimp
    apply sep_solve
   apply (case_tac r)
    apply clarsimp
    apply sep_solve
   apply clarsimp
   apply (rule_tac x=oid in exI, clarsimp)
   apply (rule_tac x=free_range' in exI, clarsimp)
   apply (clarsimp simp: unat_of_nat32)
   apply sep_solve
  apply (clarsimp simp: si_cspace_cap_def si_cnode_cap_def)
  done

lemma retype_untyped_wp_success:
  "\<lbrakk>default_object type sz minBound= Some new_object;
    available_ids \<subseteq> all_available_ids;
    free_cptr < 2 ^ si_cnode_size;
    untyped_cptr < 2 ^ si_cnode_size;
    sz < 2 ^ word_bits;
    type \<noteq> UntypedType\<rbrakk>
  \<Longrightarrow>
   \<lbrace>\<lambda>s. \<guillemotleft>(si_cnode_id, unat untyped_cptr) \<mapsto>c UntypedCap dev cover_ids available_ids \<and>*
    (\<And>* obj_id \<in> all_available_ids. (obj_id \<mapsto>o Untyped)) \<and>*
    (si_cnode_id, unat free_cptr) \<mapsto>c NullCap \<and>*
     si_tcb_id \<mapsto>f root_tcb \<and>*
    (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
    (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*
     si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
    (si_cnode_id, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap \<and>* R\<guillemotright> s \<and>
    (\<not>has_children (si_cnode_id,unat untyped_cptr) (kernel_state s) \<longrightarrow> cover_ids = available_ids) \<and>
     list_all (\<lambda>index. has_children (si_cnode_id, untyped_slots ! index) (kernel_state s)) indices\<rbrace>
     retype_untyped free_cptr untyped_cptr type sz
   \<lbrace>\<lambda>rv s. \<not>rv \<longrightarrow> (\<exists>new_id available_ids'.
     new_id \<in> available_ids \<and> available_ids' \<subseteq> available_ids - {new_id} \<and>
    \<guillemotleft>(si_cnode_id, unat untyped_cptr) \<mapsto>c UntypedCap dev cover_ids available_ids' \<and>*
    (\<And>* obj_id \<in> all_available_ids - {new_id}. (obj_id \<mapsto>o Untyped)) \<and>*
     new_id \<mapsto>o new_object \<and>*
    (si_cnode_id, unat free_cptr) \<mapsto>c default_cap type {new_id} sz dev \<and>*
     si_tcb_id \<mapsto>f root_tcb \<and>*
    (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
    (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*
     si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
    (si_cnode_id, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap \<and>* R \<guillemotright> s) \<and>
   has_children (si_cnode_id,unat untyped_cptr) (kernel_state s) \<and>
     list_all (\<lambda>index. has_children (si_cnode_id, untyped_slots ! index) (kernel_state s)) indices\<rbrace>"
  by (rule hoare_strengthen_post, rule retype_untyped_wp [where R=R], simp+)

lemma retype_untyped_wp_fail:
  "\<lbrakk>default_object type sz minBound = Some new_object;
    available_ids \<subseteq> all_available_ids;
    free_cptr < 2 ^ si_cnode_size;
    untyped_cptr < 2 ^ si_cnode_size;
    sz < 2 ^ word_bits;
    type \<noteq> UntypedType\<rbrakk>
  \<Longrightarrow>
   \<lbrace>\<lambda>s. \<guillemotleft>(si_cnode_id, unat untyped_cptr) \<mapsto>c UntypedCap dev cover_ids available_ids \<and>*
    (\<And>* obj_id \<in> all_available_ids. (obj_id \<mapsto>o Untyped)) \<and>*
    (si_cnode_id, unat free_cptr) \<mapsto>c NullCap \<and>*
     si_tcb_id \<mapsto>f root_tcb \<and>*
    (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
    (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*
     si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
    (si_cnode_id, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap \<and>* R\<guillemotright> s \<and>
   (\<not>has_children (si_cnode_id,unat untyped_cptr) (kernel_state s) \<longrightarrow> cover_ids = available_ids) \<and>
     list_all (\<lambda>index. has_children (si_cnode_id, untyped_slots ! index) (kernel_state s)) indices\<rbrace>
     retype_untyped free_cptr untyped_cptr type sz
   \<lbrace>\<lambda>rv s. rv \<longrightarrow>
    \<guillemotleft>(si_cnode_id, unat untyped_cptr) \<mapsto>c UntypedCap dev cover_ids available_ids \<and>*
    (\<And>* obj_id \<in> all_available_ids. (obj_id \<mapsto>o Untyped)) \<and>*
    (si_cnode_id, unat free_cptr) \<mapsto>c NullCap \<and>*
     si_tcb_id \<mapsto>f root_tcb \<and>*
    (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
    (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*
     si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
    (si_cnode_id, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap \<and>* R \<guillemotright> s \<and>
   (\<not>has_children (si_cnode_id,unat untyped_cptr) (kernel_state s) \<longrightarrow> cover_ids = available_ids) \<and>
     list_all (\<lambda>index. has_children (si_cnode_id, untyped_slots ! index) (kernel_state s)) indices\<rbrace>"
  by (rule hoare_strengthen_post, rule retype_untyped_wp [where R=R], simp+)

lemma retype_untyped_bij_success:
  "\<lbrakk>well_formed spec; cdl_objects spec obj_id = Some spec_object;
    type = object_type spec_object;
    sz = of_nat (object_size_bits spec_object);
    unat free_cptr = free_slot;
    unat untyped_cptr = untyped_slot;
    used_ids \<inter> available_ids = {};
    free_cptr < 2 ^ si_cnode_size;
    untyped_cptr < 2 ^ si_cnode_size;
    type \<noteq> UntypedType\<rbrakk>
  \<Longrightarrow>
   \<lbrace>\<lambda>s.
     bij_betw_map t used_spec_ids used_ids \<and>
     dom t = used_spec_ids \<and>
     obj_id \<notin> used_spec_ids \<and>
     available_ids \<subseteq> all_available_ids \<and>
    \<guillemotleft>(si_cnode_id, untyped_slot) \<mapsto>c UntypedCap dev cover_ids available_ids \<and>*
    (\<And>* obj_id \<in> all_available_ids. (obj_id \<mapsto>o Untyped)) \<and>*
    (si_cnode_id, free_slot) \<mapsto>c NullCap \<and>*
     si_tcb_id \<mapsto>f root_tcb \<and>*
    (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
    (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*
     si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
    (si_cnode_id, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap \<and>* R\<guillemotright> s \<and>
   (\<not>has_children (si_cnode_id,untyped_slot) (kernel_state s) \<longrightarrow>
         cover_ids = available_ids) \<and>
     si_caps = map_of (zip (take obj_id_index obj_ids) free_cptrs) \<and>
     list_all (\<lambda>index. has_children (si_cnode_id, untyped_slots ! index) (kernel_state s)) indices\<rbrace>
     retype_untyped free_cptr untyped_cptr type sz
   \<lbrace>\<lambda>rv s. \<not>rv \<longrightarrow> (\<exists>new_id available_ids'.
     bij_betw_map (t(obj_id \<mapsto> new_id))
                  (insert obj_id used_spec_ids)
                  (insert new_id used_ids) \<and>
     dom (t(obj_id \<mapsto> new_id)) =  (insert obj_id used_spec_ids) \<and>
     obj_id \<notin> used_spec_ids \<and>
     new_id \<in> available_ids \<and>
     available_ids' \<subseteq> available_ids - {new_id} \<and>
    \<guillemotleft>(si_cnode_id, untyped_slot) \<mapsto>c UntypedCap dev cover_ids available_ids' \<and>*
    (\<And>* obj_id \<in> all_available_ids - {new_id}. (obj_id \<mapsto>o Untyped)) \<and>*
     object_empty spec (t(obj_id \<mapsto> new_id)) obj_id \<and>*
     si_cap_at (t(obj_id \<mapsto> new_id)) (si_caps(obj_id \<mapsto> free_cptr))
                  spec dev obj_id \<and>*
     si_tcb_id \<mapsto>f root_tcb \<and>*
    (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
    (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*
     si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
    (si_cnode_id, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap \<and>* R\<guillemotright> s \<and>
   (\<not>has_children (si_cnode_id,untyped_slot) (kernel_state s) \<longrightarrow>
         cover_ids = available_ids - {new_id})) \<and>
     si_caps = map_of (zip (take obj_id_index obj_ids) free_cptrs) \<and>
     list_all (\<lambda>index. has_children (si_cnode_id, untyped_slots ! index) (kernel_state s)) indices\<rbrace>"
  apply (frule (1) well_formed_object_slots)
  apply (frule (1) well_formed_object_domain)
  apply (frule (1) well_formed_object_size_bits_word_bits)
  apply (subgoal_tac "sz = object_size_bits spec_object")
   apply (subgoal_tac "\<exists>new_object. default_object type (object_size_bits spec_object) minBound =
                                    Some new_object")
    apply (erule exE)
    apply (rule hoare_assume_pre)
    apply (frule offset_slot' [where slot=free_cptr, symmetric])
    apply (frule offset_slot' [where slot=untyped_cptr, symmetric])
    apply (rule hoare_chain, rule retype_untyped_wp_success [where available_ids=available_ids and
                                        all_available_ids=all_available_ids and
                                        cover_ids=cover_ids and R=R],
            (assumption|simp|clarsimp|blast)+)
       apply (metis lt_word_bits_lt_pow well_formed_object_size_bits_word_bits)
      apply assumption
     apply force
    apply clarsimp
    apply (rule_tac x=new_id in exI)
    apply clarsimp
    apply (rule conjI)
     apply (metis IntI bij_betw_map_fun_updI empty_iff non_dom_eval_eq)
    apply (rule_tac x=available_ids' in exI)
    apply (clarsimp simp: object_empty_def object_initialised_general_def sep_conj_exists)
    apply (clarsimp simp: object_default_state_def)
    apply (clarsimp simp: si_cap_at_def)
   apply (clarsimp)
  apply (clarsimp simp: default_object_def split: cdl_object_type.splits)
  apply clarsimp
  done

lemma si_cap_at_update:
  "\<lbrakk>(si_cap_at t si_caps spec dev obj_id) s; obj_id \<noteq> obj_id'\<rbrakk>
  \<Longrightarrow> (si_cap_at t (si_caps(obj_id' \<mapsto> cap_ptr)) spec dev obj_id) s"
  by (clarsimp simp: si_cap_at_def)

lemma map_si_cap_at_update_old:
  "\<lbrakk>distinct obj_ids; obj_id_index < length obj_ids;
    obj_id = obj_ids ! obj_id_index;
   (\<And>* map (si_cap_at t si_caps spec dev) (take obj_id_index obj_ids)) s\<rbrakk>
  \<Longrightarrow> (\<And>* map (si_cap_at t (si_caps(obj_id \<mapsto> cap_ptr)) spec dev)
              (take obj_id_index obj_ids)) s"
  apply (erule sep_list_conj_map_impl [rotated])
  apply (erule si_cap_at_update)
  apply clarsimp
  apply (erule (2) take_nth_distinct)
  done

lemma map_si_cap_at_update': (* Need better tactics. *)
  "\<lbrakk>(\<And>* map (si_cap_at t si_caps spec dev) (take obj_id_index obj_ids) \<and>* R) s;
    distinct obj_ids; obj_id_index < length obj_ids;
    obj_id = obj_ids ! obj_id_index\<rbrakk>
  \<Longrightarrow> (\<And>* map (si_cap_at t (si_caps(obj_id \<mapsto> cap_ptr)) spec dev)
              (take obj_id_index obj_ids) \<and>* R) s"
  by (drule sep_conj_impl, erule map_si_cap_at_update_old, assumption+)


lemma inter_union_empty:
  "\<lbrakk>A \<inter> B = {}; A \<inter> C = {}\<rbrakk>
  \<Longrightarrow> A \<inter> (B \<union> C) = {}"
  by auto


lemma distinct_sets_union_subs:
  "\<lbrakk>C \<subseteq> A; distinct_sets [A,B]\<rbrakk> \<Longrightarrow> A \<union> B - C = A - C \<union> B"
  by (fastforce simp: distinct_sets_def)



lemma cap_objects_remove_free_ids_Union:
  "n < length untyped_caps
  \<Longrightarrow> (\<Union>x\<in>set (untyped_caps [n := remove_free_ids (untyped_caps ! n) new_ids]). cap_objects x)
   = (\<Union>x\<in>set untyped_caps. cap_objects x)"
  apply (erule Union_list_update_id')
  apply simp
  done

lemma all_available_ids_updates:
  "\<lbrakk>distinct_sets (map cap_free_ids untyped_caps);
    all_available_ids = (\<Union>x\<in>set untyped_caps. cap_free_ids x);
    new_ids \<subseteq> cap_free_ids (untyped_caps ! n);
    n < length untyped_caps\<rbrakk>
  \<Longrightarrow> all_available_ids - new_ids =
     (\<Union>x\<in>set (untyped_caps [n := remove_free_ids (untyped_caps ! n) new_ids]). cap_free_ids x)"
  apply clarsimp
  apply (subst upd_conv_take_nth_drop, assumption)
  apply (subst id_take_nth_drop, assumption)
  apply (clarsimp simp: cap_free_ids_remove_free_ids)
  apply (rule distinct_sets_union_subs, assumption)
  apply (subst (asm) id_take_nth_drop, assumption)
  apply clarsimp
  apply (rule inter_union_empty)
   apply (frule distinct_sets_append_Cons_disjoint)
   apply clarsimp
  apply (frule distinct_sets_append2)
  apply clarsimp
  done

lemma untyped_cap_eq:
  "is_untyped_cap cap \<Longrightarrow> UntypedCap (is_device_cap cap) (cap_objects cap) (cap_free_ids cap) = cap"
  by (clarsimp simp: cap_type_def cap_free_ids_def split: cdl_cap.splits)

lemma retype_untyped_loop_inv_pre:
  "\<lbrakk>untyped_index < length untyped_caps;
    obj_id_index < length free_slots;
    length untyped_caps = length untyped_slots;
    list_all is_untyped_cap untyped_caps\<rbrakk> \<Longrightarrow>
   \<guillemotleft>\<And>* map (\<lambda>(slot, cap). (si_cnode_id, slot) \<mapsto>c cap)
             (zip untyped_slots untyped_caps) \<and>*
    \<And>* map (\<lambda>slot. (si_cnode_id, slot) \<mapsto>c NullCap) (drop obj_id_index free_slots) \<and>*
    \<And>* map (object_empty spec t) (take obj_id_index obj_ids) \<and>*
   (\<And>* obj_id\<in>all_available_ids. obj_id \<mapsto>o Untyped) \<and>*
    \<And>* map (si_cap_at t si_caps spec dev) (take obj_id_index obj_ids) \<and>*
     si_tcb_id \<mapsto>f root_tcb \<and>*
    (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
    (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*
     si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
    (si_cnode_id, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap \<and>*
    R\<guillemotright> s \<and>
    list_all
         (\<lambda>index. has_children (si_cnode_id, untyped_slots ! index) (kernel_state s))
         [index\<leftarrow>[0..<length untyped_caps] . \<not> is_full_untyped_cap (untyped_caps ! index)]
 \<Longrightarrow>
  \<guillemotleft>(si_cnode_id, untyped_slots ! untyped_index) \<mapsto>c
        UntypedCap (is_device_cap (untyped_caps ! untyped_index)) (cap_objects (untyped_caps ! untyped_index))
                   (cap_free_ids (untyped_caps ! untyped_index)) \<and>*
   (\<And>* obj_id\<in>all_available_ids. obj_id \<mapsto>o Untyped) \<and>*
    (si_cnode_id, free_slots ! obj_id_index) \<mapsto>c NullCap \<and>*
     si_tcb_id \<mapsto>f root_tcb \<and>*
    (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
    (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*
     si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
    (si_cnode_id, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap \<and>*
    \<And>* map (\<lambda>(slot, cap). (si_cnode_id, slot) \<mapsto>c cap)
             (take untyped_index (zip untyped_slots untyped_caps)) \<and>*
    \<And>* map (\<lambda>(slot, cap). (si_cnode_id, slot) \<mapsto>c cap)
             (drop (Suc untyped_index) (zip untyped_slots untyped_caps)) \<and>*
    \<And>* map (\<lambda>slot. (si_cnode_id, slot) \<mapsto>c NullCap) (drop (Suc obj_id_index) free_slots) \<and>*
    \<And>* map (object_empty spec t) (take obj_id_index obj_ids) \<and>*
    \<And>* map (si_cap_at t si_caps spec dev) (take obj_id_index obj_ids) \<and>*
    R\<guillemotright> s \<and>
    (\<not> has_children (si_cnode_id, untyped_slots ! untyped_index) (kernel_state s) \<longrightarrow>
           cap_objects (untyped_caps ! untyped_index) =
           cap_free_ids (untyped_caps ! untyped_index))"
  apply (subst (asm) id_take_nth_drop [where i=untyped_index and
                     xs="zip untyped_slots untyped_caps"], simp)
  apply (subst (asm) drop_Suc_nth [where xs="free_slots"], assumption)
  apply (subst (asm) sep_conj_map_split [symmetric], simp)
  apply (clarsimp simp: sep_conj_assoc)
  apply (frule list_all_nth, simp)
  apply (clarsimp simp: untyped_cap_eq)
  apply (rule conjI)
   apply sep_solve
  apply (clarsimp simp: Ball_set_list_all[symmetric])
  apply (erule_tac x=untyped_index in allE)
  apply (clarsimp simp: is_full_untyped_cap_simps)
  done
  declare [[blast_depth_limit  = 1000]]

lemma retype_untyped_loop_inv_post:
  "\<lbrakk>untyped_index < length untyped_caps;
    obj_id_index < length obj_ids;
    obj_id = obj_ids ! obj_id_index;
    distinct obj_ids;
    length untyped_caps = length untyped_slots;
    list_all is_untyped_cap untyped_caps;
    distinct_sets (map cap_free_ids untyped_caps);
    new_id \<in> cap_free_ids (untyped_caps ! untyped_index)\<rbrakk> \<Longrightarrow>
   \<guillemotleft>(si_cnode_id, untyped_slots ! untyped_index) \<mapsto>c
        remove_free_ids (untyped_caps ! untyped_index)
                        (cap_free_ids (untyped_caps ! untyped_index) - available_ids') \<and>*
   (\<And>* obj_id\<in>all_available_ids - {new_id}. obj_id \<mapsto>o Untyped) \<and>*
    object_empty spec t obj_id \<and>*
    si_cap_at t
        (si_caps(obj_id \<mapsto> of_nat (free_slots ! obj_id_index)))
        spec dev obj_id \<and>*
    si_tcb_id \<mapsto>f root_tcb \<and>*
   (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
   (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*
    si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
   (si_cnode_id, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap \<and>*
    \<And>* map (\<lambda>(slot, y). (si_cnode_id, slot) \<mapsto>c y)
             (take untyped_index (zip untyped_slots untyped_caps)) \<and>*
    \<And>* map (\<lambda>(slot, y). (si_cnode_id, slot) \<mapsto>c y)
             (drop (Suc untyped_index) (zip untyped_slots untyped_caps)) \<and>*
    \<And>* map (\<lambda>slot. (si_cnode_id, slot) \<mapsto>c NullCap)
             (drop (Suc obj_id_index) free_slots) \<and>*
    \<And>* map (object_empty spec t) (take obj_id_index obj_ids) \<and>*
    \<And>* map (si_cap_at t si_caps spec dev) (take obj_id_index obj_ids) \<and>*
    R\<guillemotright> s
  \<Longrightarrow>
   \<guillemotleft>\<And>* map (\<lambda>(slot, cap). (si_cnode_id, slot) \<mapsto>c cap)
             (zip untyped_slots (untyped_caps[untyped_index :=
              remove_free_ids (untyped_caps ! untyped_index)
                              (cap_free_ids (untyped_caps ! untyped_index) - available_ids')])) \<and>*
    \<And>* map (\<lambda>slot. (si_cnode_id, slot) \<mapsto>c NullCap) (drop (Suc obj_id_index) free_slots) \<and>*
    \<And>* map (object_empty spec t) (take (Suc obj_id_index) obj_ids) \<and>*
   (\<And>* obj_id\<in>all_available_ids - {new_id}. obj_id \<mapsto>o Untyped) \<and>*
    \<And>* map (si_cap_at t
                        (si_caps(obj_id \<mapsto> of_nat (free_slots ! obj_id_index)))
                        spec dev) (take (Suc obj_id_index) obj_ids) \<and>*
    si_tcb_id \<mapsto>f root_tcb \<and>*
   (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
   (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*
    si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
   (si_cnode_id, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap \<and>* R\<guillemotright> s"
  apply (subst upd_conv_take_nth_drop, simp)
  apply (subst sep_conj_zip_take_drop [symmetric], simp+)
  apply (clarsimp simp: sep_conj_assoc)
  apply (subst sep_map_take_Suc, assumption)
  apply (subst sep_map_take_Suc, assumption)
  apply (clarsimp simp: sep_conj_assoc)
  apply (sep_drule  map_si_cap_at_update' [where
     obj_ids = obj_ids and
     obj_id = "obj_ids ! obj_id_index" and
     cap_ptr = "of_nat (free_slots ! obj_id_index)"])
     apply (assumption)+
   apply (rule refl)
  apply (clarsimp simp: remove_free_ids_def)
  apply (fold remove_free_ids_def)
  apply (drule list_all_nth, simp)
  apply sep_solve
  done

lemma sep_map_conj_f_update:
  assumes l:  "i < length xs"
  assumes d:  "distinct xs"
  assumes u:  "\<And>x xs i. xs ! i \<noteq> x \<Longrightarrow> f (t(xs ! i \<mapsto> a')) x = f t x"
shows
  "\<And>* map (f (t(xs ! i \<mapsto> a')) ) (take i xs) = \<And>* map (f t) (take i xs)"
  apply (insert l d)
  apply (rule sym)
  apply (induct xs arbitrary: i)
   apply clarsimp
  apply clarsimp
  apply (case_tac i)
   apply fastforce
  apply clarsimp
  apply (subst u)
   apply (clarsimp)
  apply simp
  done

lemma map_object_empty_update:
  "\<lbrakk>i < length obj_ids; distinct obj_ids\<rbrakk>
  \<Longrightarrow> \<And>* map (object_empty spec (t(obj_ids ! i \<mapsto> obj_id'))) (take i obj_ids)
   = \<And>* map (object_empty spec t) (take i obj_ids)"
  apply (erule (1) sep_map_conj_f_update)
  apply (clarsimp simp: object_empty_def object_initialised_general_def)
  done

lemma map_si_cap_at_update:
  "\<lbrakk>i < length obj_ids; distinct obj_ids\<rbrakk>
  \<Longrightarrow> \<And>* map (si_cap_at (t(obj_ids ! i \<mapsto> obj_id')) si_caps spec dev) (take i obj_ids)
  = \<And>* map (si_cap_at t si_caps spec dev) (take i obj_ids)"
  apply (erule (1) sep_map_conj_f_update)
  apply (clarsimp simp: si_cap_at_def)
  done

lemma nth_map':
 "\<lbrakk>map f xs = ys; i < length xs\<rbrakk> \<Longrightarrow> f (xs ! i) = ys ! i"
  by (metis nth_map)

lemma bij_betw_map_fun_updI2:
  "\<lbrakk>x \<notin> A; y \<notin> B; bij_betw_map f A B\<rbrakk> \<Longrightarrow> \<exists>B'. bij_betw_map (f(x \<mapsto> y)) (insert x A) B'"
  apply (drule (2) bij_betw_map_fun_updI)
  apply fastforce
  done

lemma ran_insert_new:
  "\<lbrakk>a \<notin> dom m; b \<notin> ran m\<rbrakk> \<Longrightarrow> ran (m(a \<mapsto> b)) = insert b (ran m)"
  by auto

lemma remove_free_ids_is_device[simp]:
  "is_untyped_cap a \<Longrightarrow> is_device_cap (remove_free_ids a b) = is_device_cap a"
  by (simp add: remove_free_ids_def split:cdl_cap.splits)

lemma list_all_conj:
  "(list_all P xs \<and> list_all Q xs) = list_all (P and Q) xs"
  by (induct xs) auto

lemmas list_all_conjI = list_all_conj[THEN iffD1,unfolded pred_conj_def,OF conjI]

lemma subset_diff_weaken: "A \<subseteq> B - C \<Longrightarrow> A \<subseteq> B"
  by blast

lemma disjoint_diff: "(A = A - B) = (A \<inter> B = {})"
  by blast

lemma retype_untyped_loop_inv_success:
 "\<lbrakk>well_formed spec;
   distinct obj_ids;
   cdl_objects spec obj_id = Some object;
   obj_id_index < length obj_ids;
   untyped_index < length untyped_slots;
   obj_id_index < length free_slots;
   map of_nat untyped_slots = untyped_cptrs;
   map of_nat free_slots = free_cptrs;
   obj_id = obj_ids ! obj_id_index;
   free_cptr = free_cptrs ! obj_id_index;
   untyped_cptr = untyped_cptrs ! untyped_index;
   type = object_type object;
   object_size = of_nat (object_at_pointer_size_bits spec obj_id)\<rbrakk>
  \<Longrightarrow>
  \<lbrace>\<lambda>s. \<exists>untyped_caps t all_available_ids.
    \<guillemotleft>\<And>* map (\<lambda>(slot, cap). (si_cnode_id, slot) \<mapsto>c cap)
            (zip untyped_slots untyped_caps) \<and>*
     \<And>* map (\<lambda>slot. (si_cnode_id, slot) \<mapsto>c NullCap) (drop obj_id_index free_slots) \<and>*
     \<And>* map (object_empty spec t) (take obj_id_index obj_ids) \<and>*
   (\<And>* obj_id\<in>all_available_ids. obj_id \<mapsto>o Untyped) \<and>*
    \<And>* map (si_cap_at t si_caps spec dev) (take obj_id_index obj_ids) \<and>*

    si_tcb_id \<mapsto>f root_tcb \<and>*
   (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
   (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*
    si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
   (si_cnode_id, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap \<and>* R\<guillemotright> s \<and>
    length untyped_slots = length untyped_caps \<and>
    list_all is_untyped_cap untyped_caps \<and>
    list_all (\<lambda>c. is_device_cap c = dev) untyped_caps \<and>
    list_all well_formed_untyped_cap untyped_caps \<and>
    list_all (\<lambda>n. n < 2 ^ si_cnode_size) untyped_slots \<and>
    list_all (\<lambda>n. n < 2 ^ si_cnode_size) free_slots \<and>
    distinct_sets (map cap_free_ids untyped_caps) \<and>
   (\<Union>x\<in>set untyped_caps. cap_free_ids x) \<subseteq> all_available_ids \<and>
    bij_betw_map t (set (take obj_id_index obj_ids)) (ran t) \<and>
    dom t = set (take obj_id_index obj_ids) \<and>
    ran t \<subseteq> ((\<Union>x\<in>set untyped_caps. cap_objects x) - (\<Union>x\<in>set untyped_caps. cap_free_ids x)) \<and>
   list_all (\<lambda>index. \<not>has_children (si_cnode_id,untyped_slots!index) (kernel_state s) \<longrightarrow>
            is_full_untyped_cap (untyped_caps!index)) [0 ..< length untyped_slots] \<and>
   si_caps = map_of (zip (take obj_id_index obj_ids) free_cptrs)\<rbrace>
     retype_untyped free_cptr untyped_cptr type object_size
  \<lbrace>\<lambda>rv s. \<not>rv \<longrightarrow> (\<exists>untyped_caps t all_available_ids.
    \<guillemotleft>\<And>* map (\<lambda>(slot, cap). (si_cnode_id, slot) \<mapsto>c cap)
            (zip untyped_slots untyped_caps) \<and>*
     \<And>* map (\<lambda>slot. (si_cnode_id, slot) \<mapsto>c NullCap) (drop (Suc obj_id_index) free_slots) \<and>*
     \<And>* map (object_empty spec t)
             (take (Suc obj_id_index) obj_ids) \<and>*
   (\<And>* obj_id\<in>all_available_ids. obj_id \<mapsto>o Untyped) \<and>*
    \<And>* map (si_cap_at t (si_caps(obj_id \<mapsto> free_cptr)) spec dev)
            (take (Suc obj_id_index) obj_ids) \<and>*
    si_tcb_id \<mapsto>f root_tcb \<and>*
   (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
   (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*
    si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
   (si_cnode_id, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap \<and>* R\<guillemotright> s \<and>
    length untyped_slots = length untyped_caps \<and>
    list_all is_untyped_cap untyped_caps \<and>
    list_all (\<lambda>c. is_device_cap c = dev) untyped_caps \<and>
    list_all well_formed_untyped_cap untyped_caps \<and>
    distinct_sets (map cap_free_ids untyped_caps) \<and>
   (\<Union>x\<in>set untyped_caps. cap_free_ids x) \<subseteq> all_available_ids \<and>
    bij_betw_map t (set (take (Suc obj_id_index) obj_ids)) (ran t) \<and>
    dom t = set (take (Suc obj_id_index) obj_ids) \<and>
    ran t \<subseteq> ((\<Union>x\<in>set untyped_caps. cap_objects x) - (\<Union>x\<in>set untyped_caps. cap_free_ids x)) \<and>
    list_all (\<lambda>index. \<not>has_children (si_cnode_id,untyped_slots!index) (kernel_state s) \<longrightarrow>
              is_full_untyped_cap (untyped_caps!index)) [0 ..< length untyped_slots] \<and>
    si_caps = map_of (zip (take obj_id_index obj_ids) free_cptrs))\<rbrace>"
  apply (subst list_all_imp_filter2)+
  apply (rule hoare_ex_pre hoare_ex_pre_conj)+
  apply (rule hoare_grab_asm2)+
  apply (rule hoare_chain)
    apply (rule_tac used_spec_ids = "set (take obj_id_index obj_ids)" and
                    available_ids = "cap_free_ids (untyped_caps ! untyped_index)" and
                    all_available_ids = all_available_ids and
                    used_ids = "ran t" and
                    cover_ids = "cap_objects (untyped_caps ! untyped_index)" and
                    obj_id = "obj_ids ! obj_id_index" and
                    free_slot = "free_slots ! obj_id_index" and
                    untyped_slot = "untyped_slots ! untyped_index" and
                    si_caps = si_caps and
                    spec = spec and
                    spec_object = "the (cdl_objects spec (obj_ids ! obj_id_index))" and
                    R = "\<And>* map (\<lambda>(slot, cap). (si_cnode_id, slot) \<mapsto>c cap)
                                 (take untyped_index (zip untyped_slots untyped_caps)) \<and>*
                         \<And>* map (\<lambda>(slot, cap). (si_cnode_id, slot) \<mapsto>c cap)
                                 (drop (Suc untyped_index)
                                       (zip untyped_slots untyped_caps)) \<and>*
                         \<And>* map (\<lambda>slot. (si_cnode_id, slot) \<mapsto>c NullCap)
                                 (drop (Suc obj_id_index) free_slots) \<and>*
                         \<And>* map (object_empty spec t)
                                 (take obj_id_index obj_ids) \<and>*
                         \<And>* map (si_cap_at t si_caps spec dev)
                                 (take obj_id_index obj_ids) \<and>* R" and
                    indices = "[index\<leftarrow>[0..<length untyped_slots].
                              \<not> is_full_untyped_cap (untyped_caps ! index)]" and
                    untyped_slots = untyped_slots and
                    free_cptrs=free_cptrs and t=t and
                    obj_id_index=obj_id_index and obj_ids=obj_ids
                 in retype_untyped_bij_success,
          (assumption|simp|clarsimp)+)
         apply (drule list_all_nth [where xs=free_slots], simp)
         apply (metis of_nat_less_pow_32 offset_slot_si_cnode_size
                       offset_slot' si_cnode_size_less_than_word_size)
        apply simp
        apply (drule list_all_nth [where xs=untyped_slots], simp)
        apply (metis (mono_tags) le_unat_uoi less_or_eq_imp_le nth_map
                     si_cnode_size_less_than_word_size unat_power_lower32)
       apply force
      apply (drule list_all_nth [where xs=free_slots], simp)
      apply (metis nth_map' of_nat_less_pow_32 si_cnode_size_less_than_word_size)
     apply (drule list_all_nth [where xs=untyped_slots], simp)
     apply (metis nth_map' of_nat_less_pow_32 si_cnode_size_less_than_word_size)
    apply (frule (1) well_formed_object_untyped, simp)
   apply (clarsimp)
   apply (rule conjI)
    apply clarsimp
    apply (erule (2) take_nth_distinct)
   apply (rule conjI)
    apply (metis UN_subset_iff nth_mem)
   apply (rule retype_untyped_loop_inv_pre, simp+)
  apply (clarsimp)
  apply (rule_tac x="untyped_caps[untyped_index :=
         remove_free_ids (untyped_caps ! untyped_index)
                         ((cap_free_ids (untyped_caps ! untyped_index)) - available_ids')]" in exI)
  apply (rule_tac x="t(obj_ids ! obj_id_index \<mapsto> new_id)" in exI)
  apply (rule_tac x="all_available_ids - {new_id}" in exI)
  apply (rule conjI)
   apply (rule retype_untyped_loop_inv_post, simp+)
   apply (subst map_object_empty_update, assumption+)
   apply (subst map_si_cap_at_update, assumption+)
   apply (subst remove_free_ids_simps)
     apply (rule list_all_nth, assumption, assumption)
    apply fast
   apply (drule list_all_nth [where P = "\<lambda>c. is_device_cap c = dev"], simp)
   apply simp
  apply (rule conjI)
   apply (subst length_list_update, rule refl)
  apply (subst (asm) take_insert_nth, assumption)
  apply (subst conj_assoc[symmetric])
  apply (subst list_all_conj)
  apply (rule conjI)
   apply (rule list_all_update,simp)
   apply (rule list_all_conjI,simp+)
  apply (rule conjI)
   apply (erule (1) list_all_update)
   apply (erule well_formed_untyped_cap_remove_free_ids)
  apply (rule conjI)
   apply (erule (1) distinct_sets_map_update)
   apply (subst cap_free_ids_remove_free_ids)
   apply clarsimp
  apply (rule conjI)
   apply (subst all_available_ids_updates [symmetric], (assumption|rule refl|clarsimp)+)
   apply fast
  apply (rule conjI)
   apply (subst ran_insert_new, simp, force)
   apply clarsimp
  apply (rule conjI)
   apply (rule take_insert_nth)
   apply clarsimp
  apply (rule conjI)
   apply (subst all_available_ids_updates [symmetric], (assumption|rule refl)+)
     apply fast
    apply simp
   apply (subst cap_objects_remove_free_ids_Union [where n=untyped_index], assumption)
   apply clarsimp
   apply (drule list_all_nth [where P = well_formed_untyped_cap], simp)
   apply (drule list_all_nth [where P = is_untyped_cap], simp)
   apply (subst (asm) well_formed_untyped_cap_simps, assumption)
   apply (subst (asm) ran_insert_new, simp, force)
   apply (rule conjI)
    apply auto[1]
   apply blast
  apply (clarsimp simp: Ball_set_list_all[symmetric])
  apply (erule_tac x=x in allE)
  apply (case_tac "x=untyped_index", simp_all)
  apply (clarsimp simp: is_full_untyped_cap_simps disjoint_diff)
  done

lemma retype_untyped_bij_fail:
  "\<lbrakk>well_formed spec; cdl_objects spec obj_id = Some spec_object;
    type = object_type spec_object;
    sz = of_nat (object_size_bits spec_object);
    free_cptr < 2 ^ si_cnode_size;
    untyped_cptr < 2 ^ si_cnode_size;
    used_ids \<inter> available_ids = {}\<rbrakk>
  \<Longrightarrow>
   \<lbrace>\<lambda>s.
     bij_betw_map t used_spec_ids used_ids \<and> obj_id \<notin> used_spec_ids \<and>
     available_ids \<subseteq> all_available_ids \<and>
    \<guillemotleft>(si_cnode_id, unat untyped_cptr) \<mapsto>c UntypedCap dev cover_ids available_ids \<and>*
    (\<And>* obj_id \<in> all_available_ids. (obj_id \<mapsto>o Untyped)) \<and>*
    (si_cnode_id, unat free_cptr) \<mapsto>c NullCap \<and>*
     si_tcb_id \<mapsto>f root_tcb \<and>*
    (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
    (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*
     si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
     (si_cnode_id, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap \<and>* R\<guillemotright> s \<and>
   (\<not>has_children (si_cnode_id,unat untyped_cptr) (kernel_state s) \<longrightarrow>
         cover_ids = available_ids) \<and>
   list_all (\<lambda>index. \<not>has_children (si_cnode_id,untyped_slots!index) (kernel_state s) \<longrightarrow>
            is_full_untyped_cap (untyped_caps!index)) [0 ..< length untyped_slots]\<rbrace>
     retype_untyped free_cptr untyped_cptr type sz
   \<lbrace>\<lambda>rv s. rv \<longrightarrow>
     (bij_betw_map t used_spec_ids used_ids \<and> obj_id \<notin> used_spec_ids \<and>
     available_ids \<subseteq> all_available_ids \<and>
    \<guillemotleft>(si_cnode_id, unat untyped_cptr) \<mapsto>c UntypedCap dev cover_ids available_ids \<and>*
    (\<And>* obj_id \<in> all_available_ids. (obj_id \<mapsto>o Untyped)) \<and>*
    (si_cnode_id, unat free_cptr) \<mapsto>c NullCap \<and>*
     si_tcb_id \<mapsto>f root_tcb \<and>*
    (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
    (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*
     si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
    (si_cnode_id, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap \<and>* R\<guillemotright> s \<and>
   (\<not>has_children (si_cnode_id,unat untyped_cptr) (kernel_state s) \<longrightarrow>
         cover_ids = available_ids) \<and>
   list_all (\<lambda>index. \<not>has_children (si_cnode_id,untyped_slots!index) (kernel_state s) \<longrightarrow>
            is_full_untyped_cap (untyped_caps!index)) [0 ..< length untyped_slots])\<rbrace>"
  apply (subgoal_tac "sz = object_size_bits spec_object")
   apply (subgoal_tac "\<exists>new_object. default_object type (object_size_bits spec_object) minBound =
                                    Some new_object")
    apply (erule exE)
    apply (rule hoare_grab_asm)+
    apply (rule hoare_weaken_pre)
      apply simp
      apply (frule offset_slot' [where slot=untyped_cptr, symmetric])
      apply (frule offset_slot' [where slot=free_cptr, symmetric])
    apply (rule hoare_strengthen_post)
    apply (rule retype_untyped_wp_fail
                [where available_ids=available_ids and
                       all_available_ids=all_available_ids  and
                       cover_ids=cover_ids and
                       untyped_slots=untyped_slots and
                       indices = "[index\<leftarrow>[0..<length untyped_slots].
                              \<not> is_full_untyped_cap (untyped_caps ! index)]" and
                       R=R], simp+)
      apply (metis lt_word_bits_lt_pow well_formed_object_size_bits_word_bits)
     apply (frule (1) well_formed_object_untyped, simp)
     apply clarsimp
     apply (subst list_all_imp_filter2, simp)
    apply clarsimp
    apply (subst (asm) list_all_imp_filter2, simp)
   apply (clarsimp simp: default_object_def split: cdl_object_type.splits)
  apply clarsimp
  done

lemma conjI2:
  "\<lbrakk>P \<and> Q; R\<rbrakk> \<Longrightarrow> P \<and> Q \<and> R"
  by fast

lemma retype_untyped_loop_inv_fail:
 "\<lbrakk>well_formed spec;
   distinct obj_ids;
   cdl_objects spec obj_id = Some object;
   obj_id_index < length obj_ids;
   untyped_index < length untyped_slots;
   obj_id_index < length free_slots;
   map of_nat untyped_slots = untyped_cptrs;
   map of_nat free_slots = free_cptrs;
   obj_id = obj_ids ! obj_id_index;
   free_cptr = free_cptrs ! obj_id_index;
   untyped_cptr = untyped_cptrs ! untyped_index;
   type = object_type object;
   object_size = of_nat (object_at_pointer_size_bits spec obj_id)\<rbrakk>
  \<Longrightarrow>
  \<lbrace>\<lambda>s. \<exists>untyped_caps t all_available_ids.
    \<guillemotleft>\<And>* map (\<lambda>(slot, cap). (si_cnode_id, slot) \<mapsto>c cap)
            (zip untyped_slots untyped_caps) \<and>*
     \<And>* map (\<lambda>slot. (si_cnode_id, slot) \<mapsto>c NullCap) (drop obj_id_index free_slots) \<and>*
     \<And>* map (object_empty spec t) (take obj_id_index obj_ids) \<and>*
   (\<And>* obj_id \<in> all_available_ids. obj_id \<mapsto>o Untyped) \<and>*
    \<And>* map (si_cap_at t si_caps spec dev) (take obj_id_index obj_ids) \<and>*
     si_tcb_id \<mapsto>f root_tcb \<and>*
    (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
    (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*
     si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
    (si_cnode_id, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap \<and>* R\<guillemotright> s \<and>
    length untyped_slots = length untyped_caps \<and>
    list_all is_untyped_cap untyped_caps \<and>
    list_all (\<lambda>c. is_device_cap c = dev) untyped_caps \<and>
    list_all well_formed_untyped_cap untyped_caps \<and>
    list_all (\<lambda>n. n < 2 ^ si_cnode_size) untyped_slots \<and>
    list_all (\<lambda>n. n < 2 ^ si_cnode_size) free_slots \<and>
    distinct_sets (map cap_free_ids untyped_caps) \<and>
   (\<Union>x\<in>set untyped_caps. cap_free_ids x) \<subseteq> all_available_ids \<and>
    bij_betw_map t (set (take obj_id_index obj_ids)) (ran t) \<and>
    dom t = set (take obj_id_index obj_ids) \<and>
    ran t \<subseteq> ((\<Union>x\<in>set untyped_caps. cap_objects x) - (\<Union>x\<in>set untyped_caps. cap_free_ids x)) \<and>
   list_all (\<lambda>index. \<not>has_children (si_cnode_id,untyped_slots!index) (kernel_state s) \<longrightarrow>
            is_full_untyped_cap (untyped_caps!index)) [0 ..< length untyped_slots] \<and>
    si_caps = map_of (zip (take obj_id_index obj_ids) free_cptrs)\<rbrace>
     retype_untyped free_cptr untyped_cptr type object_size
  \<lbrace>\<lambda>rv s. rv \<longrightarrow> (\<exists>untyped_caps t all_available_ids.
    \<guillemotleft>\<And>* map (\<lambda>(slot, cap). (si_cnode_id, slot) \<mapsto>c cap)
            (zip untyped_slots untyped_caps) \<and>*
     \<And>* map (\<lambda>slot. (si_cnode_id, slot) \<mapsto>c NullCap) (drop obj_id_index free_slots) \<and>*
     \<And>* map (object_empty spec t)
             (take obj_id_index obj_ids) \<and>*
   (\<And>* obj_id \<in> all_available_ids. obj_id \<mapsto>o Untyped) \<and>*
    \<And>* map (si_cap_at t si_caps spec dev)
            (take obj_id_index obj_ids) \<and>*
     si_tcb_id \<mapsto>f root_tcb \<and>*
    (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
    (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*
     si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
    (si_cnode_id, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap \<and>* R\<guillemotright> s \<and>
    length untyped_slots = length untyped_caps \<and>
    list_all is_untyped_cap untyped_caps \<and>
    list_all (\<lambda>c. is_device_cap c = dev) untyped_caps \<and>
    list_all well_formed_untyped_cap untyped_caps \<and>
    distinct_sets (map cap_free_ids untyped_caps) \<and>
   (\<Union>x\<in>set untyped_caps. cap_free_ids x) \<subseteq> all_available_ids \<and>
    bij_betw_map t (set (take obj_id_index obj_ids)) (ran t) \<and>
    dom t = set (take obj_id_index obj_ids) \<and>
    ran t \<subseteq> ((\<Union>x\<in>set untyped_caps. cap_objects x) - (\<Union>x\<in>set untyped_caps. cap_free_ids x)) \<and>
    list_all (\<lambda>index. \<not>has_children (si_cnode_id,untyped_slots!index) (kernel_state s) \<longrightarrow>
             is_full_untyped_cap (untyped_caps!index)) [0 ..< length untyped_slots] \<and>
    si_caps = map_of (zip (take obj_id_index obj_ids) free_cptrs))\<rbrace>"
  apply (subst list_all_imp_filter2)+
  apply (rule valid_imp_ex)+
  apply (rule hoare_ex_pre hoare_ex_pre_conj)+
  apply (rule hoare_grab_asm2)+
  apply (rule hoare_chain)
    apply (rule_tac used_spec_ids1 = "set (take obj_id_index obj_ids)" and
                    available_ids1 = "cap_free_ids (untyped_caps ! untyped_index)" and
                    all_available_ids1 = all_available_ids and
                    used_ids1 = "ran t" and
                    cover_ids1 = "cap_objects (untyped_caps ! untyped_index)" and
                    free_cptr1 = free_cptr and
                    untyped_cptr1 = untyped_cptr and
                    t1 = t and
                    R1 = "\<And>* map (\<lambda>(slot, cap). (si_cnode_id, slot) \<mapsto>c cap)
                            (take untyped_index (zip untyped_slots untyped_caps)) \<and>*
                         \<And>* map (\<lambda>(slot, cap). (si_cnode_id, slot) \<mapsto>c cap)
                            (drop (Suc untyped_index) (zip untyped_slots untyped_caps)) \<and>*
                         \<And>* map (\<lambda>slot. (si_cnode_id, slot) \<mapsto>c NullCap)
                            (drop (Suc obj_id_index) free_slots) \<and>*
                         \<And>* map (object_empty spec t)
                            (take obj_id_index obj_ids) \<and>*
                         \<And>* map (si_cap_at t si_caps spec dev)
                            (take obj_id_index obj_ids) \<and>* R" and
                    untyped_slots1 = untyped_slots and
                    untyped_caps1 = untyped_caps and
                    P' = "\<lambda>s. si_caps = map_of (zip (take obj_id_index obj_ids)
                                                      free_cptrs)" and
                    Q' = "\<lambda>rv s. si_caps = map_of (zip (take obj_id_index obj_ids)
                                                         free_cptrs)"
                 in hoare_vcg_conj_lift [OF retype_untyped_bij_fail],
                 (assumption|simp|clarsimp)+)
         apply (drule list_all_nth [where xs=free_slots], simp)
         apply (metis of_nat_less_pow_32 si_cnode_size_less_than_word_size)
        apply (drule list_all_nth [where xs=untyped_slots], simp)
        apply (metis nth_map' of_nat_less_pow_32 si_cnode_size_less_than_word_size)
       apply clarsimp
       apply (drule list_all_nth [where xs=free_slots], simp)
       apply (metis (opaque_lifting, no_types) Diff_disjoint Int_commute UN_nth_mem disjoint_subset2)
      apply simp
    apply wp
   apply (clarsimp)
   apply (rule conjI)
    apply (metis take_nth_distinct)
   apply (rule conjI)
    apply force
   apply (subst unat_of_nat32)
    apply (drule list_all_nth [where xs=untyped_slots], simp)
    apply (metis si_cnode_size_less_than_word_size
                 unat_less_word_bits unat_power_lower32)
   apply (subst unat_of_nat32)
    apply (drule list_all_nth [where xs=free_slots], simp)
    apply (metis si_cnode_size_less_than_word_size
                 unat_less_word_bits unat_power_lower32)
    apply (rule conjI2)
     apply (subst unat_of_nat32)
      apply (metis (full_types) list_all_nth si_cnode_size_less_than_word_size unat_less_word_bits unat_power_lower32)
    apply (rule retype_untyped_loop_inv_pre, simp+)
   apply (subst list_all_imp_filter2, simp)
  apply clarsimp
  apply (rule_tac x=untyped_caps in exI)
  apply (rule_tac x=t in exI)
  apply (rule_tac x=all_available_ids in exI)
  apply (rule conjI)
   apply (rule_tac t = "zip untyped_slots untyped_caps" and i1 = untyped_index in ssubst[OF id_take_nth_drop], simp)
   apply (subst drop_Suc_nth [where xs="free_slots"], assumption)
   apply (drule list_all_nth, assumption)+
   apply clarsimp
   apply (subst (asm) unat_of_nat32)
    apply (drule list_all_nth [where xs=untyped_slots], simp)
    apply (metis si_cnode_size_less_than_word_size unat_less_word_bits
                 unat_power_lower32)
   apply (clarsimp simp: untyped_cap_eq sep_conj_assoc)
   apply (subst (asm) unat_of_nat32)
    apply (metis (full_types) si_cnode_size_less_than_word_size unat_less_word_bits unat_power_lower32)
    apply sep_cancel+
  apply (subst (asm) list_all_imp_filter2, simp)
  done

lemma retype_untyped_loop_inv_helper:
 "\<lbrakk>well_formed spec;
   distinct obj_ids;
   cdl_objects spec obj_id = Some object;
   obj_id_index < length obj_ids;
   untyped_index < length untyped_slots;
   obj_id_index < length free_slots;
   map of_nat untyped_slots = untyped_cptrs;
   map of_nat free_slots = free_cptrs;
   obj_id = obj_ids ! obj_id_index;
   free_cptr = free_cptrs ! obj_id_index;
   untyped_cptr = untyped_cptrs ! untyped_index;
   type = object_type object;
   object_size = of_nat (object_at_pointer_size_bits spec obj_id)\<rbrakk>
 \<Longrightarrow>
  \<lbrace>\<lambda>s. \<exists>untyped_caps t all_available_ids.
    \<guillemotleft>\<And>* map (\<lambda>(slot, cap). (si_cnode_id, slot) \<mapsto>c cap)
            (zip untyped_slots untyped_caps) \<and>*
     \<And>* map (\<lambda>slot. (si_cnode_id, slot) \<mapsto>c NullCap) (drop obj_id_index free_slots) \<and>*
     \<And>* map (object_empty spec t) (take obj_id_index obj_ids) \<and>*
   (\<And>* obj_id \<in> all_available_ids. obj_id \<mapsto>o Untyped) \<and>*
    \<And>* map (si_cap_at t si_caps spec dev) (take obj_id_index obj_ids) \<and>*
     si_tcb_id \<mapsto>f root_tcb \<and>*
    (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
    (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*
     si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
    (si_cnode_id, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap \<and>* R\<guillemotright> s \<and>
    length untyped_slots = length untyped_caps \<and>
    list_all is_untyped_cap untyped_caps \<and>
    list_all (\<lambda>c. is_device_cap c = dev) untyped_caps \<and>
    list_all well_formed_untyped_cap untyped_caps \<and>
    list_all (\<lambda>n. n < 2 ^ si_cnode_size) untyped_slots \<and>
    list_all (\<lambda>n. n < 2 ^ si_cnode_size) free_slots \<and>
    distinct_sets (map cap_free_ids untyped_caps) \<and>
   (\<Union>x\<in>set untyped_caps. cap_free_ids x) \<subseteq> all_available_ids \<and>
    bij_betw_map t (set (take obj_id_index obj_ids)) (ran t) \<and>
    dom t = set (take obj_id_index obj_ids) \<and>
    ran t \<subseteq> ((\<Union>x\<in>set untyped_caps. cap_objects x) -
             (\<Union>x\<in>set untyped_caps. cap_free_ids x)) \<and>
    list_all (\<lambda>index. \<not>has_children (si_cnode_id,untyped_slots!index) (kernel_state s) \<longrightarrow>
            is_full_untyped_cap (untyped_caps!index)) [0 ..< length untyped_slots] \<and>
    si_caps = map_of (zip (take obj_id_index obj_ids) free_cptrs)\<rbrace>
     retype_untyped free_cptr untyped_cptr type object_size
  \<lbrace>\<lambda>rv s. (\<exists>untyped_caps t all_available_ids.
    \<guillemotleft>\<And>* map (\<lambda>(slot, cap). (si_cnode_id, slot) \<mapsto>c cap)
            (zip untyped_slots untyped_caps) \<and>*
     \<And>* map (\<lambda>slot. (si_cnode_id, slot) \<mapsto>c NullCap)
             (drop (if rv then obj_id_index else Suc obj_id_index) free_slots) \<and>*
     \<And>* map (object_empty spec t)
             (take (if rv then obj_id_index else Suc obj_id_index) obj_ids) \<and>*
   (\<And>* obj_id \<in> all_available_ids. obj_id \<mapsto>o Untyped) \<and>*
    \<And>* map (si_cap_at t (if rv then si_caps
                   else si_caps(obj_id \<mapsto> free_cptr)) spec dev)
            (take (if rv then obj_id_index else Suc obj_id_index) obj_ids) \<and>*
     si_tcb_id \<mapsto>f root_tcb \<and>*
    (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
    (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*
     si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
    (si_cnode_id, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap \<and>* R\<guillemotright> s \<and>
    length untyped_slots = length untyped_caps \<and>
    list_all is_untyped_cap untyped_caps \<and>
    list_all (\<lambda>c. is_device_cap c = dev) untyped_caps \<and>
    list_all well_formed_untyped_cap untyped_caps \<and>
    distinct_sets (map cap_free_ids untyped_caps) \<and>
   (\<Union>x\<in>set untyped_caps. cap_free_ids x) \<subseteq> all_available_ids \<and>
    bij_betw_map t (set (take (if rv then obj_id_index
                                     else Suc obj_id_index) obj_ids)) (ran t) \<and>
    dom t = set (take (if rv then obj_id_index else Suc obj_id_index) obj_ids) \<and>
    ran t \<subseteq> ((\<Union>x\<in>set untyped_caps. cap_objects x) -
             (\<Union>x\<in>set untyped_caps. cap_free_ids x)) \<and>
    list_all (\<lambda>index. \<not>has_children (si_cnode_id,untyped_slots!index) (kernel_state s) \<longrightarrow>
            is_full_untyped_cap (untyped_caps!index)) [0 ..< length untyped_slots] \<and>
    si_caps = map_of (zip (take obj_id_index obj_ids) free_cptrs))\<rbrace>"
  apply (rule hoare_strengthen_post)
   apply (rule valid_rv_split)
    apply (fact retype_untyped_loop_inv_fail)
   apply (fact retype_untyped_loop_inv_success)
  apply (case_tac r, simp_all)
  done

lemma nth_mem_sub:
  "\<lbrakk>set xs \<subseteq> dom f; n < length xs\<rbrakk> \<Longrightarrow> f (xs ! n) = Some (the (f (xs ! n)))"
  by (metis Some_the nth_mem set_rev_mp)

lemma retype_untyped_loop_inv:
 "\<lbrace>\<lambda>s. \<exists>untyped_caps t all_available_ids.
    \<guillemotleft>\<And>* map (\<lambda>(slot, cap). (si_cnode_id, slot) \<mapsto>c cap)
            (zip untyped_slots untyped_caps) \<and>*
     \<And>* map (\<lambda>slot. (si_cnode_id, slot) \<mapsto>c NullCap) (drop obj_id_index free_slots) \<and>*
     \<And>* map (object_empty spec t) (take obj_id_index obj_ids) \<and>*
   (\<And>* obj_id \<in> all_available_ids. obj_id \<mapsto>o Untyped) \<and>*
    \<And>* map (si_cap_at t si_caps spec dev) (take obj_id_index obj_ids) \<and>*
     si_tcb_id \<mapsto>f root_tcb \<and>*
    (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
    (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*
     si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
    (si_cnode_id, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap \<and>* R\<guillemotright> s \<and>
    well_formed spec \<and>
    set obj_ids \<subseteq> dom (cdl_objects spec) \<and>
    distinct obj_ids \<and>
    obj_id_index < length obj_ids \<and>
    obj_id_index < length free_cptrs \<and>
    untyped_index < length untyped_cptrs \<and>
    length obj_ids \<le> length free_slots \<and>
    object_size = of_nat (object_at_pointer_size_bits spec obj_id) \<and>
    length untyped_slots = length untyped_caps \<and>
    map of_nat untyped_slots = untyped_cptrs \<and>
    map of_nat free_slots = free_cptrs \<and>
    obj_id = obj_ids ! obj_id_index \<and>
    free_cptr = free_cptrs ! obj_id_index \<and>
    untyped_cptr = untyped_cptrs ! untyped_index \<and>
    type = object_type (the (cdl_objects spec obj_id)) \<and>
    list_all is_untyped_cap untyped_caps \<and>
    list_all (\<lambda>c. is_device_cap c = dev) untyped_caps \<and>
    list_all well_formed_untyped_cap untyped_caps \<and>
    list_all (\<lambda>n. n < 2 ^ si_cnode_size) untyped_slots \<and>
    list_all (\<lambda>n. n < 2 ^ si_cnode_size) free_slots \<and>
    distinct_sets (map cap_free_ids untyped_caps) \<and>
   (\<Union>x\<in>set untyped_caps. cap_free_ids x) \<subseteq> all_available_ids \<and>
    bij_betw_map t (set (take obj_id_index obj_ids)) (ran t) \<and>
    dom t = set (take obj_id_index obj_ids) \<and>
    ran t \<subseteq> ((\<Union>x\<in>set untyped_caps. cap_objects x) - (\<Union>x\<in>set untyped_caps. cap_free_ids x)) \<and>
    list_all
       (\<lambda>index. \<not>has_children (si_cnode_id,untyped_slots!index) (kernel_state s) \<longrightarrow>
       is_full_untyped_cap (untyped_caps!index)) [0 ..< length untyped_slots] \<and>
    si_caps = map_of (zip (take obj_id_index obj_ids) free_cptrs)\<rbrace>
     retype_untyped free_cptr untyped_cptr type object_size
  \<lbrace>\<lambda>rv s. (\<exists>untyped_caps t all_available_ids.
    \<guillemotleft>\<And>* map (\<lambda>(slot, cap). (si_cnode_id, slot) \<mapsto>c cap)
            (zip untyped_slots untyped_caps) \<and>*
     \<And>* map (\<lambda>slot. (si_cnode_id, slot) \<mapsto>c NullCap)
             (drop (if rv then obj_id_index else Suc obj_id_index) free_slots) \<and>*
     \<And>* map (object_empty spec t)
             (take (if rv then obj_id_index else Suc obj_id_index) obj_ids) \<and>*
   (\<And>* obj_id \<in> all_available_ids. obj_id \<mapsto>o Untyped) \<and>*
    \<And>* map (si_cap_at t (if rv then si_caps
                   else si_caps(obj_id \<mapsto> free_cptr)) spec dev)
            (take (if rv then obj_id_index else Suc obj_id_index) obj_ids) \<and>*
     si_tcb_id \<mapsto>f root_tcb \<and>*
    (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
    (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*
     si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
    (si_cnode_id, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap \<and>* R\<guillemotright> s \<and>
    obj_id_index < length obj_ids \<and>
    obj_id_index < length free_cptrs \<and>
    untyped_index < length untyped_cptrs \<and>
    length obj_ids \<le> length free_slots \<and>
    length untyped_slots = length untyped_caps \<and>
    list_all is_untyped_cap untyped_caps \<and>
    list_all (\<lambda>c. is_device_cap c = dev) untyped_caps \<and>
    list_all well_formed_untyped_cap untyped_caps \<and>
    distinct_sets (map cap_free_ids untyped_caps) \<and>
   (\<Union>x\<in>set untyped_caps. cap_free_ids x) \<subseteq> all_available_ids \<and>
    bij_betw_map t (set (take (if rv then obj_id_index else Suc obj_id_index) obj_ids)) (ran t) \<and>
    dom t = set (take (if rv then obj_id_index else Suc obj_id_index) obj_ids) \<and>
    ran t \<subseteq> ((\<Union>x\<in>set untyped_caps. cap_objects x) - (\<Union>x\<in>set untyped_caps. cap_free_ids x)) \<and>
    list_all
       (\<lambda>index. \<not>has_children (si_cnode_id,untyped_slots!index) (kernel_state s) \<longrightarrow>
       is_full_untyped_cap (untyped_caps!index)) [0 ..< length untyped_slots] \<and>
    (if rv then si_caps else si_caps(obj_id \<mapsto> free_cptr))
    = map_of (zip (take (if rv then obj_id_index
                               else Suc obj_id_index) obj_ids) free_cptrs))\<rbrace>"
  apply (rule hoare_assume_pre)
  apply (rule hoare_chain)
    apply (rule retype_untyped_loop_inv_helper
           [where object="the (cdl_objects spec obj_id)" and
                  obj_id_index=obj_id_index and obj_id = obj_id and
                  untyped_index=untyped_index and
                  untyped_slots=untyped_slots and
                  obj_ids=obj_ids and
                  free_slots=free_slots and R=R], (assumption|rule refl|clarsimp)+)
              apply (rule nth_mem_sub, assumption+)
             apply (assumption|rule refl|simp|clarsimp)+
   apply (rule_tac x=untyped_capsa in exI)
   apply (rule_tac x=ta in exI)
   apply (rule_tac x=all_available_idsa in exI)
   apply clarsimp
   apply blast
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply blast
  apply clarsimp
  apply (rule_tac x=untyped_capsa in exI)
  apply (rule_tac x=ta in exI)
  apply (rule_tac x=all_available_idsa in exI)
  apply clarsimp
  apply (subst nth_map[symmetric, where f=of_nat], simp)
  apply (rule map_of_zip_take_update, simp+)
  done

lemma if_not:
  "(if \<not>P then a else b) = (if P then b else a)"
  by simp

lemma bij_betw_map_empty [simp]:
  "bij_betw_map Map.empty {} {}"
  apply (clarsimp simp: bij_betw_map_def bij_betw_def)
  done

lemma retype_untypeds_wp_helper:
  "\<lbrakk>well_formed spec; set obj_ids = dom (cdl_objects spec); distinct obj_ids;
    map of_nat untyped_slots = untyped_cptrs;
    map of_nat free_slots = free_cptrs;
    list_all (\<lambda>n. n < 2 ^ si_cnode_size) untyped_slots;
    list_all (\<lambda>n. n < 2 ^ si_cnode_size) free_slots;
    length [obj\<leftarrow>obj_ids. real_object_at obj spec] \<le> length free_cptrs\<rbrakk>
  \<Longrightarrow>
  \<lbrace>\<lambda>s. \<exists>untyped_caps.
   \<guillemotleft>\<And>* map (\<lambda>(slot, cap). (si_cnode_id, slot) \<mapsto>c cap) (zip untyped_slots untyped_caps) \<and>*
    \<And>* map (\<lambda>slot. (si_cnode_id, slot) \<mapsto>c NullCap) free_slots \<and>*
   (\<And>* obj_id\<in>(\<Union>cap\<in>set untyped_caps. cap_free_ids cap). obj_id \<mapsto>o Untyped) \<and>*
    si_tcb_id \<mapsto>f root_tcb \<and>*
   (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
   (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*
    si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
   (si_cnode_id, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap \<and>* R\<guillemotright> s \<and>
   length untyped_slots = length untyped_caps \<and>
   list_all is_full_untyped_cap untyped_caps \<and>
   list_all (\<lambda>c. is_device_cap c = dev) untyped_caps \<and>
   list_all well_formed_untyped_cap untyped_caps \<and>
   distinct_sets (map cap_free_ids untyped_caps)\<rbrace>

     create_objects spec obj_ids untyped_cptrs free_cptrs

   \<lbrace>\<lambda>(si_caps, free_cptrs') s. \<exists>untyped_caps t all_available_ids.
     \<guillemotleft>\<And>* map (\<lambda>(slot, cap). (si_cnode_id, slot) \<mapsto>c cap) (zip untyped_slots untyped_caps) \<and>*
      \<And>* map (\<lambda>slot. (si_cnode_id, slot) \<mapsto>c NullCap) (drop (length [obj\<leftarrow>obj_ids. real_object_at obj spec]) free_slots) \<and>*
      \<And>* map (object_empty spec t) [obj\<leftarrow>obj_ids. real_object_at obj spec] \<and>*
     (\<And>* obj_id \<in> all_available_ids. obj_id \<mapsto>o Untyped) \<and>*
      \<And>* map (si_cap_at t si_caps spec dev) [obj\<leftarrow>obj_ids. real_object_at obj spec] \<and>*
      si_tcb_id \<mapsto>f root_tcb \<and>*
     (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
     (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*
      si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
     (si_cnode_id, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap \<and>* R\<guillemotright> s \<and>
      inj_on t (set [obj\<leftarrow>obj_ids. real_object_at obj spec]) \<and>
      dom t = set [obj\<leftarrow>obj_ids. real_object_at obj spec] \<and>
      ran t \<subseteq> (\<Union>cap\<in>set untyped_caps. cap_objects cap) \<and>
      si_caps = map_of (zip [obj\<leftarrow>obj_ids. real_object_at obj spec] free_cptrs) \<and>
      free_cptrs' = drop (length [obj\<leftarrow>obj_ids. real_object_at obj spec]) free_cptrs\<rbrace>"
  apply (unfold create_objects_def)
  apply (rule hoare_weaken_pre)
   apply (wp|wpc)+
   apply (rule whileLoop_wp [where I="\<lambda>(obj_id_index, untyped_index, si_caps) s.
    \<exists>untyped_caps cover_ids available_ids all_available_ids t.
     \<guillemotleft>\<And>* map (\<lambda>(slot, cap). (si_cnode_id, slot) \<mapsto>c cap) (zip untyped_slots untyped_caps) \<and>*
      \<And>* map (\<lambda>slot. (si_cnode_id, slot) \<mapsto>c NullCap) (drop obj_id_index free_slots) \<and>*
      \<And>* map (object_empty spec t) (take obj_id_index [obj\<leftarrow>obj_ids. real_object_at obj spec]) \<and>*
     (\<And>* obj_id \<in> all_available_ids. obj_id \<mapsto>o Untyped) \<and>*
     \<And>* map (si_cap_at t si_caps spec dev) (take obj_id_index [obj\<leftarrow>obj_ids. real_object_at obj spec]) \<and>*
      si_tcb_id \<mapsto>f root_tcb \<and>*
     (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
     (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*
      si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
     (si_cnode_id, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap \<and>* R\<guillemotright> s \<and>
             obj_id_index  \<le> length [obj\<leftarrow>obj_ids. real_object_at obj spec] \<and>
             obj_id_index  \<le> length free_cptrs \<and>
             untyped_index \<le> length untyped_cptrs \<and>
             length untyped_slots = length untyped_caps \<and>
             list_all is_untyped_cap untyped_caps \<and>
             list_all (\<lambda>c. is_device_cap c = dev) untyped_caps \<and>
             list_all well_formed_untyped_cap untyped_caps \<and>
             distinct_sets (map cap_free_ids untyped_caps) \<and>
            (\<Union>x\<in>set untyped_caps. cap_free_ids x) \<subseteq> all_available_ids \<and>
             bij_betw_map t (set $ take obj_id_index [obj\<leftarrow>obj_ids. real_object_at obj spec]) (ran t) \<and>
             dom t = (set $ take obj_id_index [obj\<leftarrow>obj_ids. real_object_at obj spec]) \<and>
             ran t \<subseteq> ((\<Union>x\<in>set untyped_caps. cap_objects x) -
                      (\<Union>x\<in>set untyped_caps. cap_free_ids x)) \<and>
             list_all (\<lambda>index. \<not>has_children (si_cnode_id,untyped_slots!index)
                                             (kernel_state s) \<longrightarrow>
                                is_full_untyped_cap (untyped_caps!index))
                      [0 ..< length untyped_slots] \<and>
             si_caps = map_of (zip (take obj_id_index [obj\<leftarrow>obj_ids. real_object_at obj spec]) free_cptrs)"])
    apply (rule hoare_weaken_pre)
     apply (wp valid_case_prod)
           apply (simp add: if_not)
           apply (rule hoare_strengthen_post)
            apply (rule_tac spec=spec and obj_id_index=obj_id_index and
                            untyped_index=untyped_index and obj_ids="[obj\<leftarrow>obj_ids. real_object_at obj spec]" and
                            free_slots=free_slots and free_cptrs=free_cptrs and
                            untyped_slots=untyped_slots and
                            untyped_cptrs=untyped_cptrs and
                            si_caps=si_caps and dev = dev and
                            obj_id=obj_id and R=R
                         in retype_untyped_loop_inv)
          apply (erule pre_post_ex)+
          apply (erule exE)+
          apply (rule_tac x=all_available_ids in exI)
          apply (rule_tac x=t in exI)
          apply fastforce
          apply wp+
    apply (clarsimp simp: real_object_at_def)
    apply blast
   apply clarsimp
   apply (rename_tac s untyped_caps all_available_ids t obj_id_index untyped_index)
   apply (drule bij_betw_map_imp_inj_on)
   apply (subgoal_tac "obj_id_index = length [obj\<leftarrow>obj_ids. real_object_at obj spec]")
    apply (clarsimp; drule subset_diff_weaken; blast)
   apply linarith
  apply clarsimp
  apply (rule_tac x=untyped_caps in exI)
  apply (rule_tac x="\<Union>x\<in>set untyped_caps. cap_free_ids x" in exI)
  apply (frule list_allI [where P'="is_untyped_cap"])
   apply (simp add: is_full_untyped_cap_is_untyped_cap)
  apply (clarsimp simp: Ball_set_list_all[symmetric])
  done

lemma comp_tuple:
  "(\<lambda>(a, b). P a b) \<circ> (\<lambda>(a, b). (Q a, R b)) = (\<lambda>(a, b). P (Q a) (R b))"
  by auto

lemma comp_apply:
  "((\<lambda>a. P a) \<circ> Q) = (\<lambda>x. P (Q x))"
  by (fact comp_def)

lemma real_object_at_inter_cdl_objects [simp]:
  "{obj_id. real_object_at obj_id spec} \<inter> dom (cdl_objects spec) = {obj_id. real_object_at obj_id spec}"
  by (auto simp: real_object_at_def)

lemma length_real_object_at_card:
  "\<lbrakk>set obj_ids = dom (cdl_objects spec); distinct obj_ids\<rbrakk>
  \<Longrightarrow> length [obj\<leftarrow>obj_ids . real_object_at obj spec] = card {obj_id. real_object_at obj_id spec}"
  by (clarsimp simp: distinct_length_filter)

(* The \<guillemotleft> \<guillemotright> need to be on the outside here to work with sep_wp. *)
lemma create_objects_sep:
  "\<lbrace>\<guillemotleft>((\<And>* (cptr, cap) \<in> set (zip untyped_cptrs untyped_caps). (si_cnode_id, unat cptr) \<mapsto>c cap) \<and>*
      (\<And>* cptr \<in> set free_cptrs. (si_cnode_id, unat cptr) \<mapsto>c NullCap)  \<and>*
      (\<And>* obj_id\<in>(\<Union>cap\<in>set untyped_caps. cap_free_ids cap). obj_id \<mapsto>o Untyped) \<and>*
       si_objects \<and>* R) and
       K (well_formed spec \<and>
          set obj_ids = dom (cdl_objects spec) \<and>
          distinct obj_ids \<and>
          distinct free_cptrs \<and>
          distinct untyped_cptrs \<and>
          length untyped_cptrs = length untyped_caps \<and>
          list_all is_full_untyped_cap untyped_caps \<and>
          list_all (\<lambda>c. is_device_cap c = dev) untyped_caps \<and>
          list_all well_formed_untyped_cap untyped_caps \<and>
          distinct_sets (map cap_free_ids untyped_caps) \<and>
          card {obj_id. real_object_at obj_id spec} \<le> length free_cptrs \<and>
          list_all (\<lambda>n. n < 2 ^ si_cnode_size) free_cptrs \<and>
          list_all (\<lambda>n. n < 2 ^ si_cnode_size) untyped_cptrs)\<guillemotright> \<rbrace>

  create_objects spec obj_ids untyped_cptrs free_cptrs

\<lbrace>\<lambda>rv s. \<exists>t.
    \<guillemotleft>(objects_empty spec t {obj_id. real_object_at obj_id spec} \<and>*
      si_caps_at t (fst rv) spec dev {obj_id. real_object_at obj_id spec} \<and>*
      si_objects \<and>*
      si_objects_extra_caps' {obj_id. real_object_at obj_id spec} free_cptrs untyped_cptrs \<and>*
      R) and
      K (inj_on t {obj_id. real_object_at obj_id spec} \<and>
         dom t = {obj_id. real_object_at obj_id spec} \<and>
        (map_of (zip [obj\<leftarrow>obj_ids. real_object_at obj spec] free_cptrs),
         drop (card {obj_id. real_object_at obj_id spec}) free_cptrs) = rv)\<guillemotright> s\<rbrace>"
  apply clarsimp
  apply (rule hoare_gen_asm_conj)
  apply (clarsimp simp: si_objects_def si_objects_extra_caps'_def)
  apply (rule hoare_assume_pre)
  apply (rule hoare_chain)
    apply (wp (once) retype_untypeds_wp_helper
      [where R="(si_cnode_id, unat seL4_CapIRQControl) \<mapsto>c IrqControlCap \<and>* si_asid \<and>* R"
         and untyped_slots = "map unat untyped_cptrs" and dev = dev
         and free_slots    = "map unat free_cptrs"],
           (simp|clarsimp)+)
      apply (fastforce simp: list_all_iff unat_less_2_si_cnode_size')
     apply (fastforce simp: list_all_iff unat_less_2_si_cnode_size')
    apply (clarsimp simp: length_real_object_at_card)
   apply (rule_tac x=untyped_caps in exI)
   apply (clarsimp simp: zip_map1 comp_tuple sep_conj_assoc)
   apply (subst comp_apply)+
   apply (subst sep_list_conj_sep_map_set_conj, simp add: distinct_zipI1)
   apply (subst sep_list_conj_sep_map_set_conj, simp add: distinct_zipI1)
   apply sep_cancel+
  apply (clarsimp simp: length_real_object_at_card)
  apply (rule_tac x=t in exI)
  apply (clarsimp simp: sep_conj_exists sep_conj_assoc
                        objects_empty_def si_caps_at_def)
  apply (rule_tac x=untyped_capsa in exI)
  apply (rule_tac x=all_available_ids in exI)
  apply (subst (asm) sep_list_conj_sep_map_set_conj [where xs="[obj\<leftarrow>obj_ids . real_object_at obj spec]"], simp)+
  apply (clarsimp simp: zip_map1 drop_map comp_def split_beta')
  apply (subst (asm) sep_list_conj_sep_map_set_conj, simp add: distinct_zipI1)+
  apply sep_solve
  done

end
