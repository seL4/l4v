(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory KHeap_DP
imports ProofHelpers_DP
begin

lemma has_slots_simps:
  "has_slots (Tcb tcb)"
  "has_slots (CNode cnode)"
  "has_slots (AsidPool ap)"
  "has_slots (PageTable pt)"
  "has_slots (PageDirectory pd)"
  "\<not> has_slots Endpoint"
  "\<not> has_slots Notification"
  "\<not> has_slots (Frame f)"
  "\<not> has_slots Untyped"
  by (simp add: has_slots_def)+

lemma reset_cap_asid_id:
  "reset_cap_asid cap = reset_cap_asid cap'
  \<Longrightarrow> cap = cap'
     \<or> (\<exists>a b c d e f. cap = FrameCap f a b c d e)
     \<or> (\<exists>a b c. cap = PageTableCap a b c)
     \<or> (\<exists>a b c. cap = PageDirectoryCap a b c)"
  by (case_tac cap, (clarsimp simp: reset_cap_asid_def split: cdl_cap.splits)+)

(* Move to Helpers_SD *)
definition is_memory_cap :: "cdl_cap \<Rightarrow> bool"
where
    "is_memory_cap cap \<equiv>
       (case cap of
           FrameCap _ _ _ _ _ _     \<Rightarrow> True
         | PageTableCap _ _ _     \<Rightarrow> True
         | PageDirectoryCap _ _ _ \<Rightarrow> True
         | _                      \<Rightarrow> False)"

lemma reset_cap_asid_memory_cap [simp]:
  "\<not>is_memory_cap cap \<Longrightarrow> reset_cap_asid cap = cap"
  by (clarsimp simp: is_memory_cap_def reset_cap_asid_def
              split: cdl_cap.splits)

lemma is_memory_cap_reset_cap_asid [simp]:
  "is_memory_cap (reset_cap_asid cap) = is_memory_cap cap"
  by (clarsimp simp: is_memory_cap_def reset_cap_asid_def
              split: cdl_cap.splits)

lemmas reset_cap_asid_simps[simp] = reset_cap_asid_def
    [THEN meta_eq_to_obj_eq, THEN fun_cong,split_simps cdl_cap.split]

lemma reset_cap_asid_simps2:
  "reset_cap_asid cap = NullCap \<Longrightarrow> cap = NullCap"
  "reset_cap_asid cap = RunningCap \<Longrightarrow> cap = RunningCap"
  "reset_cap_asid cap = (UntypedCap dev a ra) \<Longrightarrow> cap = UntypedCap dev a ra"
  "reset_cap_asid cap = (EndpointCap b c d) \<Longrightarrow> cap = EndpointCap b c d"
  "reset_cap_asid cap = (NotificationCap e f g) \<Longrightarrow> cap = NotificationCap e f g"
  "reset_cap_asid cap = (ReplyCap h R) \<Longrightarrow> cap = ReplyCap h R"
  "reset_cap_asid cap = (MasterReplyCap i) \<Longrightarrow> cap = MasterReplyCap i"
  "reset_cap_asid cap = (CNodeCap j k l sz) \<Longrightarrow> cap = CNodeCap j k l sz"
  "reset_cap_asid cap = (TcbCap m) \<Longrightarrow> cap = TcbCap m"
  "reset_cap_asid cap = DomainCap \<Longrightarrow> cap = DomainCap"
  "reset_cap_asid cap = RestartCap \<Longrightarrow> cap = RestartCap"
  "reset_cap_asid cap = (PendingSyncSendCap n p q r s rp) \<Longrightarrow> cap = (PendingSyncSendCap n p q r s rp)"
  "reset_cap_asid cap = (PendingSyncRecvCap t isf rp) \<Longrightarrow> cap = (PendingSyncRecvCap t isf rp)"
  "reset_cap_asid cap = (PendingNtfnRecvCap u) \<Longrightarrow> cap = (PendingNtfnRecvCap u)"
  "reset_cap_asid cap = IrqControlCap \<Longrightarrow> cap = IrqControlCap"
  "reset_cap_asid cap = (IrqHandlerCap v) \<Longrightarrow> cap = (IrqHandlerCap v)"
  "reset_cap_asid cap = AsidControlCap \<Longrightarrow> cap = AsidControlCap"
  "reset_cap_asid cap = (AsidPoolCap w x) \<Longrightarrow> cap = (AsidPoolCap w x)"
  "reset_cap_asid cap = (IOPortsCap y z) \<Longrightarrow> cap = (IOPortsCap y z)"
  "reset_cap_asid cap = IOSpaceMasterCap \<Longrightarrow> cap = IOSpaceMasterCap"
  "reset_cap_asid cap = (IOSpaceCap a1) \<Longrightarrow> cap = (IOSpaceCap a1)"
  "reset_cap_asid cap = (IOPageTableCap a2) \<Longrightarrow> cap = (IOPageTableCap a2)"
  "reset_cap_asid cap = (ZombieCap a3) \<Longrightarrow> cap = (ZombieCap a3)"
  "reset_cap_asid cap = (BoundNotificationCap a4) \<Longrightarrow> cap = (BoundNotificationCap a4)"
  "reset_cap_asid cap = (FrameCap dev aa rghts sz rset ma) \<Longrightarrow> \<exists>asid. cap = FrameCap dev aa rghts sz rset asid"
  "reset_cap_asid cap = (PageTableCap aa rights ma) \<Longrightarrow> \<exists>asid. cap = PageTableCap aa rights asid"
  "reset_cap_asid cap = (PageDirectoryCap aa rights as) \<Longrightarrow> \<exists>asid. cap = PageDirectoryCap aa rights asid"
by (clarsimp simp: reset_cap_asid_def split: cdl_cap.splits)+

lemma sep_map_c_any:
  "(p \<mapsto>c cap \<and>* R) s \<Longrightarrow> (p \<mapsto>c - \<and>* R) s"
  by (fastforce simp: sep_any_def sep_conj_exists)

lemma pure_extract:
  "\<lbrakk> <P \<and>* Q> s; pure P \<rbrakk> \<Longrightarrow> <P> s"
  by (fastforce simp: pure_def sep_state_projection_def sep_conj_def)

lemma throw_on_none_rv:
  "\<lbrace>\<lambda>s. case x of Some y \<Rightarrow> P y s | otherwise \<Rightarrow> False\<rbrace> throw_on_none x \<lbrace>P\<rbrace>, \<lbrace>Q\<rbrace>"
  apply (clarsimp simp: throw_on_none_def split: option.splits)
   apply (wp)+
  done

lemma oseq:
  "\<lbrakk> \<lbrace>P\<rbrace> gets_the f \<lbrace>Q\<rbrace>; \<forall>x. \<lbrace>Q x\<rbrace> gets_the $ g x \<lbrace>R\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> gets_the (f |>> g) \<lbrace>R\<rbrace>"
  apply (fastforce simp: gets_def fail_def get_def return_def gets_the_def obind_def valid_def split_def
    Let_def bind_def assert_opt_def split:option.splits)
  done

lemma hoare_ex_all:
     "(\<forall>x. \<lbrace>P x\<rbrace> f \<lbrace>Q\<rbrace>) = \<lbrace>\<lambda>s. \<exists>x. P x s\<rbrace> f \<lbrace>Q\<rbrace>"
  apply (rule iffI)
  apply (fastforce simp: valid_def)+
done


lemma sep_any_All: "\<lbrace><ptr \<mapsto>c - \<and>* R>\<rbrace> f \<lbrace>Q\<rbrace> = (\<forall>x. \<lbrace><ptr \<mapsto>c x \<and>* R>\<rbrace> f \<lbrace>Q\<rbrace>)"
  apply (clarsimp simp: sep_any_def sep_conj_exists hoare_ex_all)
done

(* validE reasoning *)

lemma gets_the_wpE:
  "\<lbrace>\<lambda>s. case (f s) of None \<Rightarrow> True | Some (Inl e) \<Rightarrow> E e s | Some (Inr r) \<Rightarrow> Q r s \<rbrace> gets_the f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  apply (clarsimp simp: validE_def)
  apply (wp)
  apply (clarsimp)
  done

lemma gets_the_invE : "\<lbrace>P\<rbrace> gets_the f \<lbrace>\<lambda>_. P\<rbrace>, -"
  apply (wp)
  apply (clarsimp)
  done

lemma return_rv :"\<lbrace>P r\<rbrace> return (Inr r) \<lbrace>\<lambda>rv s. P rv s\<rbrace>, \<lbrace>\<lambda>_ _. True\<rbrace>"
  by (clarsimp simp: validE_def, wp, simp split: option.splits)

crunches throw_on_none
  for inv[wp]: P

lemma hoare_if_simp:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. (if x then (\<lambda>rv s. Q rv s) else (\<lambda>rv s. Q rv s)) rv s\<rbrace>"
  by (clarsimp)

lemma hoare_if_simpE:
  "\<lbrakk>\<And>x. Q x = R x; \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-\<rbrakk>
  \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. (if x rv s then (\<lambda>s. Q rv s) else (\<lambda>s. R rv s)) s\<rbrace>,-"
  by (clarsimp simp: validE_R_def validE_def split: sum.splits)

lemma hoare_gen_asmEx: "(P \<Longrightarrow> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>) \<Longrightarrow> \<lbrace>P' and K P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  by (fastforce simp: valid_def validE_def)

lemma unless_wp_not: "\<lbrace>\<lambda>s. P s \<and> Q\<rbrace> unless Q f \<lbrace>\<lambda>_. P\<rbrace>"
  by (clarsimp simp: unless_def when_def)

lemma false_e_explode:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>\<lambda>_ _ . False\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>R\<rbrace>"
  by (fastforce simp: validE_def valid_def split: sum.splits)

(* sep rules *)
lemma sep_any_map_c_imp: "(dest \<mapsto>c cap) s \<Longrightarrow> (dest \<mapsto>c -) s"
  by (fastforce simp: sep_any_def)

lemma obj_exists_map_i:
  "<obj_id \<mapsto>o obj \<and>* R> s \<Longrightarrow> \<exists>obj'. (cdl_objects s obj_id = Some obj'
                                       \<and> object_clean obj = object_clean obj')"
  apply (clarsimp simp: sep_map_o_conj)
  apply (case_tac "cdl_objects s obj_id")
   apply (drule_tac x = "(obj_id,Fields)" in fun_cong)
    apply (clarsimp simp: lift_def object_to_sep_state_def object_project_def
      object_at_heap_def sep_state_projection_def
      sep_conj_def Let_unfold)
  apply (rule_tac x = a in exI,simp)
  apply (rule object_eqI)
   apply (drule_tac x = "(obj_id,Fields)" in fun_cong)
   apply (clarsimp simp: lift_def object_to_sep_state_def object_project_def
      object_at_heap_def sep_state_projection_def
      Let_unfold)
  apply (rule ext)
  apply (drule_tac x= "(obj_id,Slot x)" in fun_cong)
  apply (clarsimp simp: lift_def object_to_sep_state_def
      object_project_def sep_state_projection_def
      Let_unfold)
  done

lemma obj_exists_map_f:
  "<obj_id \<mapsto>f obj \<and>* R> s \<Longrightarrow>
  \<exists>obj'. (cdl_objects s obj_id = Some obj' \<and> object_type obj = object_type obj')"
  apply (clarsimp simp: sep_map_f_conj Let_def)
  apply (case_tac "cdl_objects s obj_id")
   apply (clarsimp simp: lift_def object_to_sep_state_def object_project_def
      object_at_heap_def sep_state_projection_def
      sep_conj_def Let_unfold)
  apply (rule_tac x = a in exI,simp)
  apply (clarsimp simp: lift_def object_to_sep_state_def object_project_def
      object_at_heap_def sep_state_projection_def
      Let_unfold)
  apply (drule_tac f = object_type in arg_cong)
  apply simp
  done

lemma object_slots_asid_reset:
  "object_slots (asid_reset obj) = reset_cap_asid \<circ>\<^sub>M (object_slots obj)"
  by (clarsimp simp: object_slots_def asid_reset_def update_slots_def
              split: cdl_object.splits)

lemma reset_cap_asid_idem [simp]:
  "reset_cap_asid (reset_cap_asid cap) = reset_cap_asid cap"
  by (simp add: reset_cap_asid_def split: cdl_cap.splits)

lemma opt_cap_sep_imp:
  "\<lbrakk><p \<mapsto>c cap \<and>* R> s\<rbrakk>
  \<Longrightarrow> \<exists>cap'. opt_cap p s = Some cap' \<and> reset_cap_asid cap' = reset_cap_asid cap"
  apply (clarsimp simp: opt_cap_def sep_map_c_conj Let_def)
  apply (clarsimp simp:  sep_map_c_def lift_def
    split_def
    sep_any_def sep_map_general_def slots_of_def
    sep_state_projection_def object_project_def
    object_slots_object_clean
    Let_unfold split:sep_state.splits option.splits)
done

lemma opt_cap_sep_any_imp:
  "\<lbrakk><dest \<mapsto>c - \<and>* R> s\<rbrakk> \<Longrightarrow> \<exists>cap. opt_cap (dest) s = Some cap"
  apply (clarsimp simp: sep_any_exist
    opt_cap_def sep_map_c_conj Let_def)
  apply (clarsimp simp:  sep_map_c_def lift_def
    split_def object_slots_object_clean
    sep_any_def sep_map_general_def slots_of_def
    sep_state_projection_def object_project_def
    Let_unfold split:sep_state.splits option.splits)
done

lemma sep_f_size_opt_cnode:
  "\<lbrakk>< cap_object cnode_cap \<mapsto>f CNode (empty_cnode r) \<and>* R> s;
    (opt_cnode (cap_object cnode_cap) s) = Some obj \<rbrakk>
  \<Longrightarrow> r = cdl_cnode_size_bits obj"
  apply (clarsimp simp:sep_map_f_conj Let_def)
  apply (case_tac obj)
  apply (auto simp: intent_reset_def empty_cnode_def
    opt_cnode_def update_slots_def sep_state_projection_def
    object_wipe_slots_def
    object_project_def object_clean_def asid_reset_def
    split:cdl_cap.splits cdl_object.splits)
  done


(* concerete wp rules *)


lemma swap_parents_wp:
  "\<lbrace><R>\<rbrace>
   swap_parents src dest
  \<lbrace>\<lambda>_.  <R>\<rbrace>"
  by (wpsimp simp: swap_parents_def lift_def sep_state_projection_def)

lemma insert_cap_orphan_wp:
   "\<lbrace><dest \<mapsto>c - \<and>* R>\<rbrace>
    insert_cap_orphan cap dest
   \<lbrace>\<lambda>_.<dest \<mapsto>c cap \<and>* R>\<rbrace>"
  apply (clarsimp simp: insert_cap_orphan_def)
  apply (wp set_cap_wp)
  apply (clarsimp)
  done

lemma move_cap_wp:
 "\<lbrace><dest \<mapsto>c - \<and>* src \<mapsto>c cap \<and>* R>\<rbrace>
    move_cap cap' src dest
  \<lbrace>\<lambda>_. <dest \<mapsto>c cap'  \<and>* src \<mapsto>c NullCap \<and>* R>\<rbrace>"
  apply (simp add: move_cap_def)
  apply (wp add: swap_parents_wp sep_wp: insert_cap_orphan_wp set_cap_wp)
  apply (sep_solve)
done


lemma swap_cap_wp:
  "\<lbrace><dest \<mapsto>c cap \<and>*  src \<mapsto>c cap' \<and>* R>\<rbrace>
    swap_cap cap' src cap dest
   \<lbrace>\<lambda>_.<dest \<mapsto>c cap' \<and>* src \<mapsto>c cap \<and>* R>\<rbrace>"
  apply (clarsimp simp add: swap_cap_def)
  apply (wp add: swap_parents_wp sep_wand: set_cap_wp)
  apply (sep_solve)
  done

lemma set_parent_wp:
  "\<lbrace><P>\<rbrace>
    set_parent child parent
   \<lbrace>\<lambda>_.<P>\<rbrace>"
  apply (clarsimp simp: set_parent_def sep_state_projection_def)
  apply wp
  apply clarsimp
  done

lemma not_untyped_cap_set_full:
  "\<lbrace>P and K (\<not> is_untyped_cap cap)\<rbrace> set_untyped_cap_as_full src_cap cap src \<lbrace>\<lambda>r. P\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (clarsimp simp:set_untyped_cap_as_full_def)
  done

lemma insert_cap_sibling_wp:
  "\<lbrace><dest \<mapsto>c - \<and>* R> and K (\<not> is_untyped_cap cap)\<rbrace>
    insert_cap_sibling cap src dest
   \<lbrace>\<lambda>_. <dest \<mapsto>c cap \<and>* R>\<rbrace>"
  apply (clarsimp simp: insert_cap_sibling_def)
  apply (wp)
    apply (clarsimp split: option.splits)
    apply (safe)
     apply (wp set_parent_wp set_cap_wp not_untyped_cap_set_full | simp)+
  done

lemma insert_cap_child_wp:
 "\<lbrace><dest \<mapsto>c - \<and>* R> and K (\<not> is_untyped_cap cap)\<rbrace>
    insert_cap_child cap src dest
  \<lbrace>\<lambda>_. <dest \<mapsto>c cap \<and>* R>\<rbrace>"
  apply (clarsimp simp: insert_cap_child_def)
  apply (wp insert_cap_orphan_wp set_parent_wp set_cap_wp not_untyped_cap_set_full | simp)+
done

lemma remove_parent_wp:
  "\<lbrace><P>\<rbrace>
   remove_parent obj
   \<lbrace>\<lambda>_.  <P>\<rbrace>"
   by (wpsimp simp: remove_parent_def lift_def sep_state_projection_def)

lemma get_cap_wp:
  "\<lbrace>P\<rbrace>
    get_cap obj
   \<lbrace>\<lambda>_. P\<rbrace>"
  apply (wp)
  apply (clarsimp simp: opt_cap_def)
done

lemma get_cap_rv:
  "\<lbrace>\<lambda>s. <ptr \<mapsto>c cap \<and>* R> s \<and>
   (\<forall>c. ((reset_cap_asid c = reset_cap_asid cap ) \<longrightarrow> Q c s)) \<rbrace>
    get_cap ptr
   \<lbrace> Q \<rbrace>"
   apply (wp)
   apply (safe)
   apply (clarsimp simp: split_def dest!: opt_cap_sep_imp)
  done

lemma get_cap_rv':
  "\<lbrace>\<lambda>s. <ptr \<mapsto>c cap \<and>* R> s \<and> Q cap s \<and> \<not>is_memory_cap cap\<rbrace>
    get_cap ptr
   \<lbrace>Q\<rbrace>"
  by (wp get_cap_rv, fastforce)

lemma decode_tcb_invocation:
  "\<lbrace>P\<rbrace>decode_tcb_invocation cap cap_ref caps (TcbWriteRegistersIntent resume flags count regs)
  \<lbrace>\<lambda>_. P\<rbrace>"
apply (clarsimp simp: decode_tcb_invocation_def)
apply wp
apply (clarsimp)
done

lemma get_object_wp:
  "\<lbrace>P\<rbrace>
    get_object ptr
   \<lbrace>\<lambda>_. P\<rbrace>"
  apply (wp gets_the_inv)
done

lemma empty_slot_wp:
  "\<lbrace><dest \<mapsto>c - \<and>* R>\<rbrace>
    empty_slot dest
   \<lbrace>\<lambda>_. <dest \<mapsto>c NullCap \<and>* R>\<rbrace>"
  apply (clarsimp simp: empty_slot_def sep_any_def sep_conj_exists)
  apply (subst hoare_ex_all [THEN sym], clarsimp)
  apply (wp set_cap_wp remove_parent_wp get_cap_rv[where R=R])
  apply (rule conjI, assumption)
  apply safe
   apply (clarsimp simp: reset_cap_asid_def split: cdl_cap.splits)
  apply sep_solve
  done

lemma invoke_cnode_insert_wp:
  "\<lbrace><dest \<mapsto>c - \<and>* R> and K (\<not> is_untyped_cap cap)\<rbrace>
     invoke_cnode (InsertCall cap src dest)
   \<lbrace>\<lambda>_. <dest \<mapsto>c cap \<and>* R>\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (clarsimp simp: invoke_cnode_def)
  apply (wp insert_cap_sibling_wp insert_cap_child_wp)
  apply (clarsimp)
  done

lemma invoke_cnode_move_cap:
  "\<lbrace><dest \<mapsto>c - \<and>* src \<mapsto>c cap \<and>* R> \<rbrace> invoke_cnode (MoveCall cap' src dest)
  \<lbrace>\<lambda>_. <dest \<mapsto>c cap' \<and>* src \<mapsto>c NullCap \<and>* R>\<rbrace>,\<lbrace>Q\<rbrace>"
  apply (simp add:validE_def)
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp:invoke_cnode_def liftE_bindE validE_def[symmetric])
  apply (wp move_cap_wp)
  apply simp
  done

lemma invoke_cnode_rotate1_wp:
  "\<lbrace><dest \<mapsto>c cap1 \<and>* src \<mapsto>c cap2 \<and>* R> \<rbrace>
     invoke_cnode (RotateCall cap1 cap2 dest src dest)
   \<lbrace>\<lambda>_. <dest \<mapsto>c cap2 \<and>* src \<mapsto>c cap1 \<and>* R>\<rbrace>"
  apply (clarsimp simp: invoke_cnode_def)
  apply (wp sep_wand: swap_cap_wp)
  apply sep_solve
  done

lemma invoke_cnode_rotate2_wp:
   "(dest) \<noteq> (rnd) \<Longrightarrow>
  \<lbrace><dest \<mapsto>c cap1 \<and>* src \<mapsto>c cap2 \<and>*
    rnd \<mapsto>c - \<and>* R>\<rbrace>
     invoke_cnode (RotateCall cap1 cap2 dest src rnd)
  \<lbrace>\<lambda>_. <dest \<mapsto>c NullCap \<and>* src \<mapsto>c cap1 \<and>*
    rnd \<mapsto>c cap2 \<and>* R>\<rbrace>"
  apply (clarsimp simp: invoke_cnode_def)
  apply (wp sep_wand: move_cap_wp)
  apply sep_solve
  done

lemma get_cnode_wp [wp]:
  "\<lbrace> \<lambda>s. case (cdl_objects s a) of Some (CNode x) \<Rightarrow> P x s | _ \<Rightarrow> False \<rbrace>
     get_cnode a
   \<lbrace> P \<rbrace>"
  apply (clarsimp simp: get_cnode_def)
  apply (wp | wpc)+
  apply (clarsimp split: cdl_object.splits)
  done

lemma resolve_address_bits_wp:
 "\<lbrace> \<lambda>s. P s \<rbrace>
  resolve_address_bits cnode_cap cap_ptr remaining_size
  \<lbrace> \<lambda>_. P \<rbrace>, \<lbrace> \<lambda>_. P \<rbrace>"
  apply (clarsimp simp: gets_the_resolve_cap[symmetric])
  apply (wp)
  apply simp
done

lemma resolve_cap_wp [wp]:
  "\<lbrace> P \<rbrace>
    gets_the (resolve_cap cnode_cap cap_ptr remaining_size)
  \<lbrace> \<lambda>_. P \<rbrace>"
  by (wp gets_the_inv)

lemma lookup_slot_for_cnode_op_wp [wp]:
  "\<lbrace>P\<rbrace>
    lookup_slot_for_cnode_op cnode_cap cap_ptr remaining_size
  \<lbrace>\<lambda>_. P \<rbrace>"
  apply (clarsimp simp: lookup_slot_for_cnode_op_def split_def)
  apply (wp)
   apply (clarsimp simp: fault_to_except_def)
   apply (wp)
   apply (clarsimp simp: gets_the_resolve_cap[symmetric])
   apply (wp gets_the_wpE whenE_wp)+
  apply (clarsimp split: option.splits sum.splits)
done

lemma lookup_slot_for_cnode_op_wpE:
  "\<lbrace>P\<rbrace>
    lookup_slot_for_cnode_op cnode_cap cap_ptr remaining_size
  \<lbrace>\<lambda>_. P \<rbrace>,\<lbrace>\<lambda>_. P \<rbrace>"
  apply (clarsimp simp: lookup_slot_for_cnode_op_def split_def)
  apply (wp)
   apply (clarsimp simp: gets_the_resolve_cap[symmetric])
   apply (clarsimp simp: fault_to_except_def)
   apply (wp gets_the_wpE whenE_wp)+
  apply (clarsimp split: option.splits split: sum.splits)
done

lemma resolve_cap_rv1:
   "\<lbrace>\<lambda>s. Q ((c,slot),0) s \<and> cap_object cnode_cap = c \<and> slot = offset cap_ptr r \<and>
    < c \<mapsto>f CNode (empty_cnode r)  \<and>* (c, slot) \<mapsto>c cap \<and>* R> s \<and>
    one_lvl_lookup cnode_cap remaining_size r\<rbrace>
         gets_the (resolve_cap cnode_cap cap_ptr remaining_size)
  \<lbrace>\<lambda>rv s. Q rv s\<rbrace>,\<lbrace>\<lambda>_ _ . True\<rbrace>"
  apply (wp gets_the_wpE)
  apply (clarsimp simp: one_lvl_lookup_def offset_def)
  apply (clarsimp simp: split_def split: sum.splits option.splits)
  apply (simp add: split_def resolve_cap.simps split: if_split_asm)
  apply (simp add: obind_def split:option.splits)
  apply (drule sep_f_size_opt_cnode)
   apply (simp split: if_split_asm)+
done

lemma resolve_cap_u:
   "\<lbrace>\<lambda>s. Q (((cap_object cnode_cap), offset cap_ptr r), 0) s \<and>
         < user_pointer_at (r,r_s) cnode_cap cap_ptr cap  \<and>* R> s \<rbrace>
         gets_the (resolve_cap cnode_cap cap_ptr r_s)
    \<lbrace>Q\<rbrace>,\<lbrace>\<lambda> _ _.  True\<rbrace>"
  apply (wp gets_the_wpE)
  apply (clarsimp simp:
    user_pointer_at_def Let_unfold one_lvl_lookup_def
    offset_def  split:option.splits sum.splits)
  apply (simp add: split_def resolve_cap.simps split: if_split_asm)
  apply (simp add: obind_def sep_conj_assoc split:option.splits)
  apply (sep_drule (direct) sep_f_size_opt_cnode)
  apply (fastforce split: if_split_asm)+
done

lemma resolve_cap_u_nf:
   "\<lbrace>\<lambda>s. Q (((cap_object cnode_cap), offset cap_ptr r), 0) s \<and>
         < user_pointer_at (r,r_s) cnode_cap cap_ptr cap  \<and>* R> s \<rbrace>
         gets_the (resolve_cap cnode_cap cap_ptr r_s)
    \<lbrace>Q\<rbrace>,\<lbrace>Q'\<rbrace>"
  apply (wp gets_the_wpE)
  apply (clarsimp simp: user_pointer_at_def Let_unfold guard_equal_def one_lvl_lookup_def
                        offset_def sep.mult_assoc)
  apply (clarsimp simp: split_def split: sum.splits option.splits)
  apply (safe)
   apply (simp add: split_def resolve_cap.simps split: if_split_asm)
   apply (simp add: obind_def split:option.splits)
   apply (sep_drule (direct) sep_f_size_opt_cnode)
    apply (fastforce)+
  apply (simp add: split_def resolve_cap.simps split: if_split_asm)
  apply (simp add: obind_def split:option.splits)
   apply (sep_drule (direct) sep_f_size_opt_cnode)
    apply (fastforce split: if_split_asm)+
done

lemma resolve_cap_rv:
 "\<lbrace>\<lambda>s. cap_object cnode_cap = c \<and> slot = offset cap_ptr r \<and>
    < c \<mapsto>f CNode (empty_cnode r) \<and>* (c, slot) \<mapsto>c cap \<and>* R> s \<and>
    one_lvl_lookup cnode_cap remaining_size r\<rbrace>
         gets_the (resolve_cap cnode_cap cap_ptr remaining_size)
  \<lbrace>\<lambda>rv s. (fst rv) = (c,slot) \<and> <
  c \<mapsto>f CNode (empty_cnode r)  \<and>* (c,slot) \<mapsto>c cap \<and>* R> s \<and> (snd rv) = 0\<rbrace>,\<lbrace>\<lambda>_ _ . True\<rbrace>"
  apply (wp resolve_cap_rv1 gets_the_invE)
  apply (clarsimp)
  apply (safe|fastforce)+
done

lemma lookup_slot_for_cnode_op_rv':
    "\<lbrace>\<lambda>s. Q (c,slot) s \<and> cap_object cnode_cap = c \<and> slot = offset cap_ptr r \<and>
    < c \<mapsto>f CNode (empty_cnode r)  \<and>* (c, slot) \<mapsto>c cap \<and>* R> s \<and>
    one_lvl_lookup cnode_cap remaining_size r\<rbrace>
      lookup_slot_for_cnode_op cnode_cap cap_ptr remaining_size
     \<lbrace>\<lambda>rv s. Q rv s\<rbrace>,-"
  apply (clarsimp simp: lookup_slot_for_cnode_op_def gets_the_resolve_cap[symmetric] split_def fault_to_except_def)
  apply (wp resolve_cap_rv1 whenE_wp)
  apply (fastforce)
done

lemma reset_cap_asid_cap_has_object:
  "reset_cap_asid cap = reset_cap_asid cap'
  \<Longrightarrow> cap_has_object cap = cap_has_object cap'"
  apply (frule reset_cap_asid_id)
  apply (safe, (clarsimp simp: reset_cap_asid_def cap_has_object_def
                        split: cdl_cap.splits)+)
  done

lemma cap_object_reset_cap_asid:
  "\<lbrakk>reset_cap_asid cap = reset_cap_asid cap'\<rbrakk> \<Longrightarrow> cap_object cap = cap_object cap'"
  apply (case_tac cap',simp_all add:reset_cap_asid_def split:cdl_cap.split_asm)
  done

lemma cap_type_reset_cap_asid[simp]:
  "cap_type (reset_cap_asid cap) = cap_type cap"
  by (clarsimp simp: reset_cap_asid_def split: cdl_cap.splits)

lemma cap_guard_reset_cap_asid:
  "is_cnode_cap cap \<Longrightarrow> cap_guard (reset_cap_asid cap) = cap_guard cap"
  "is_cnode_cap cap \<Longrightarrow> cap_guard_size (reset_cap_asid cap) = cap_guard_size cap"
  by (case_tac cap,simp_all add:reset_cap_asid_def cap_guard_def)+

lemma lookup_slot_for_cnode_op_rvu':
     "\<lbrace>\<lambda>s. Q ((cap_object cnode_cap), offset cap_ptr r) s \<and> remaining_size \<le> word_bits
         \<and> 0 < remaining_size \<and>
         < \<box> (r, remaining_size): cnode_cap cap_ptr \<mapsto>u cap  \<and>* R> s \<rbrace>
      lookup_slot_for_cnode_op cnode_cap cap_ptr remaining_size
     \<lbrace>Q\<rbrace>,\<lbrace>Q'\<rbrace>"
  apply (clarsimp simp: lookup_slot_for_cnode_op_def gets_the_resolve_cap[symmetric] split_def fault_to_except_def)
  apply (wp resolve_cap_u_nf[where r=r and R=R and cap=cap] whenE_wp)
  apply (clarsimp simp add:user_pointer_at_def Let_def guard_equal_def
    cap_guard_reset_cap_asid one_lvl_lookup_def)
done

lemma lookup_slot_for_cnode_op_rv_2:
  "\<lbrace>\<lambda>s. cap_object cnode_cap = c \<and> slot = offset cap_ptr r \<and>
    < c \<mapsto>f CNode (empty_cnode r)  \<and>* (c, slot) \<mapsto>c cap \<and>* R> s \<and>
    one_lvl_lookup cnode_cap remaining_size r\<rbrace>
      lookup_slot_for_cnode_op cnode_cap cap_ptr remaining_size
  \<lbrace>\<lambda>rv s. rv = (c,slot) \<and> < c \<mapsto>f CNode (empty_cnode r) \<and>* (c,slot) \<mapsto>c cap \<and>* R> s\<rbrace>,-"
  apply (wp lookup_slot_for_cnode_op_rv')
  apply (fastforce)
done


lemma derive_cap_rv:
"\<lbrace>\<lambda>s. case cap of FrameCap dev p r sz b x \<Rightarrow> False | otherwise \<Rightarrow> P s\<rbrace>
     derive_cap slot cap
 \<lbrace>\<lambda>rv s. P s \<and> ( rv = cap \<or> rv = NullCap )\<rbrace>, \<lbrace>\<lambda>_ _. True\<rbrace>"
  apply (clarsimp simp: derive_cap_def returnOk_def split: cdl_cap.splits,safe)
                        apply (wp return_rv whenE_wp | clarsimp simp: ensure_no_children_def)+
done

lemma derive_cap_wp [wp]:
"\<lbrace>P\<rbrace> derive_cap slot cap  \<lbrace>\<lambda>_. P\<rbrace>"
  apply (clarsimp simp: derive_cap_def returnOk_def split: cdl_cap.splits)
  apply (safe)
    apply ((wp whenE_wp)|(clarsimp simp: ensure_no_children_def))+
      done


lemma derive_cap_wpE:
"\<lbrace>P\<rbrace> derive_cap slot cap \<lbrace>\<lambda>_.P\<rbrace>,\<lbrace>\<lambda>_.P\<rbrace>"
  apply (clarsimp simp: derive_cap_def)
  apply (case_tac cap, (wp whenE_wp |
                        simp add: ensure_no_children_def)+)
  done

lemma derive_cap_wp2: "\<lbrace>P\<rbrace> derive_cap slot cap \<lbrace>\<lambda>rv s. if rv = NullCap then True else P s\<rbrace>, -"
  apply (rule hoare_strengthen_postE_R)
   apply (wp (once) derive_cap_wpE)
  apply (clarsimp)
  done

lemma ensure_empty_wpE [wp]: "\<lbrace>P\<rbrace>
     ensure_empty x
     \<lbrace> \<lambda>_. P \<rbrace>,\<lbrace>\<lambda>_. P\<rbrace>"
  apply (clarsimp simp: ensure_empty_def)
  apply (wp liftE_wp unlessE_wp)
  apply (clarsimp)
  done

lemma decode_cnode_copy_wp: "\<lbrace>P\<rbrace>
     decode_cnode_invocation target target_ref caps (CNodeCopyIntent dest_index dest_depth src_index src_depth rights)
     \<lbrace> \<lambda>_. P \<rbrace>,\<lbrace>\<lambda>_. P\<rbrace>"
  apply (clarsimp simp: decode_cnode_invocation_def split_def)
  apply (wp whenE_wp hoare_drop_imps | simp cong: if_cong)+
  done

lemma ensure_empty_wp [wp]: "\<lbrace>P\<rbrace> ensure_empty slot \<lbrace>\<lambda>_. P\<rbrace>"
  by (clarsimp simp: ensure_empty_def,wp unlessE_wp,clarsimp)

lemma ensure_no_children_wp [wp]: "\<lbrace>P\<rbrace> ensure_no_children slot \<lbrace>\<lambda>_. P\<rbrace>"
  apply (clarsimp simp: ensure_no_children_def)
  apply (wp whenE_wp)
  apply (clarsimp)
done

lemma mapu_dest_opt_cap:
  "< \<box> (sz, r): cr ci \<mapsto>u cap \<and>* R> s
  \<Longrightarrow> \<exists>cap'. opt_cap (cap_object cr, offset ci sz) s = Some cap' \<and>
             reset_cap_asid cap' = reset_cap_asid cap"
  apply (clarsimp simp: user_pointer_at_def Let_unfold sep.mult_assoc)
  apply (sep_drule (direct) opt_cap_sep_imp)
  apply (clarsimp)
  done

lemma ensure_empty_no_exception:
  "\<lbrace> < dest_slot \<mapsto>c NullCap \<and>* R> and Q \<rbrace> ensure_empty dest_slot \<lbrace>\<lambda>r. Q \<rbrace>, \<lbrace>Q'\<rbrace>"
  apply (simp add:ensure_empty_def)
  apply (wp unlessE_wp)
  apply (clarsimp dest!:opt_cap_sep_imp reset_cap_asid_simps2)
  done

lemma reset_cap_asid_cap_type:
  "reset_cap_asid cap = reset_cap_asid cap'
  \<Longrightarrow> cap_type cap = cap_type cap'"
  by (clarsimp simp: reset_cap_asid_def split: cdl_cap.splits)

lemma ep_related_cap_update_cap_rights[simp]:
  "ep_related_cap (update_cap_rights rights cap) = ep_related_cap cap"
  "\<lbrakk> is_ep_cap cap \<rbrakk> \<Longrightarrow> cap_badge (update_cap_rights rights cap) = cap_badge cap"
  "\<lbrakk> is_ntfn_cap cap \<rbrakk> \<Longrightarrow> cap_badge (update_cap_rights rights cap) = cap_badge cap"
  by (auto simp:ep_related_cap_def cap_badge_def cap_type_def update_cap_rights_def
          split:cdl_cap.splits)

lemma reset_cap_asid_cap_badge:
  "\<lbrakk>reset_cap_asid cap = reset_cap_asid cap';ep_related_cap cap\<rbrakk>
  \<Longrightarrow> cap_badge cap = cap_badge cap'"
  apply (clarsimp simp: ep_related_cap_def split:cdl_cap.splits)
  by (simp_all add: ep_related_cap_def
    reset_cap_asid_def split:cdl_cap.splits)

lemma reset_cap_asid_ep_related_cap:
  "reset_cap_asid cap = reset_cap_asid cap'
  \<Longrightarrow> ep_related_cap cap = ep_related_cap cap'"
  apply (clarsimp simp: ep_related_cap_def)
  apply (case_tac cap, (case_tac cap', simp_all add: reset_cap_asid_def)+)
  done

lemma reset_cap_asid_ep_cap:
  "reset_cap_asid cap = reset_cap_asid cap'
  \<Longrightarrow> is_ep_cap cap = is_ep_cap cap'"
  apply (case_tac cap; case_tac cap'; simp add: reset_cap_asid_def)
  done

lemma reset_cap_asid_ntfn_cap:
  "reset_cap_asid cap = reset_cap_asid cap'
  \<Longrightarrow> is_ntfn_cap cap = is_ntfn_cap cap'"
  by (case_tac cap; case_tac cap'; simp add: reset_cap_asid_def)

lemma cap_rights_reset_cap_asid:
  "reset_cap_asid cap = reset_cap_asid cap'
 \<Longrightarrow> cap_rights cap = cap_rights cap'"
  apply (clarsimp simp: cap_rights_def reset_cap_asid_def)
  by (case_tac cap; (case_tac cap'; simp))

(* Lemmas about valid_src_cap *)
lemma reset_cap_asid_cnode_cap:
  "\<lbrakk>reset_cap_asid cap' = reset_cap_asid cap ; is_cnode_cap cap\<rbrakk>
  \<Longrightarrow> cap' = cap"
  apply (drule sym)
  apply (drule reset_cap_asid_id)
  apply (clarsimp simp: cap_type_def split: cdl_cap.splits)
  done

lemma valid_src_cap_asid_cong:
  "reset_cap_asid cap' = reset_cap_asid cap
       \<Longrightarrow> valid_src_cap cap' = valid_src_cap cap"
  apply (rule ext)
  apply (clarsimp simp:valid_src_cap_def)
  apply (rule iffI[rotated])
   apply (drule sym)
   apply (clarsimp dest!:reset_cap_asid_cnode_cap)+
  done

lemma derive_cap_invE:
  "\<lbrace>P (derived_cap cap) and Q\<rbrace> derive_cap slot cap \<lbrace>P\<rbrace>, \<lbrace>\<lambda>r. Q\<rbrace>"
  apply (simp add:derive_cap_def)
  apply (rule hoare_pre)
   apply (wp|wpc|simp)+
  apply (auto simp:derived_cap_def)
  done

lemma cap_type_null:
  "cap_has_type cap \<Longrightarrow> cap \<noteq> NullCap"
  "cap_type cap = Some type \<Longrightarrow> cap \<noteq> NullCap"
  by (clarsimp simp: cap_type_def)+

lemma decode_cnode_move_rvu:
  "\<lbrace>\<lambda>s. intent = CNodeMoveIntent dest_index dest_depth src_index src_depth \<and>
        get_index caps 0 = Some (cap ,cap_ref) \<and>
        src_cap \<noteq> NullCap \<and>
        (\<forall>src_cap'. reset_cap_asid src_cap' = reset_cap_asid src_cap \<longrightarrow>
                    Q (MoveCall (src_cap')
                                (cap_object cap, offset src_index sz)
                                (cap_object target, offset dest_index sz')) s) \<and>
        unat src_depth \<le> word_bits \<and> 0 < unat src_depth \<and>
        unat dest_depth \<le> word_bits \<and> 0 < unat dest_depth \<and>
        < \<box> (sz, (unat src_depth)):  cap src_index \<mapsto>u src_cap \<and>*
          \<box> (sz', (unat dest_depth)): target dest_index \<mapsto>u NullCap \<and>* R> s \<rbrace>
      decode_cnode_invocation target target_ref caps intent
     \<lbrace>\<lambda>rv s. Q rv s\<rbrace>, \<lbrace>Q'\<rbrace>"
  apply (unfold validE_def)
  apply (rule hoare_name_pre_state)
  apply (unfold validE_def[symmetric])
  apply (clarsimp simp: decode_cnode_invocation_def split_def split: sum.splits)
  apply wp
     apply (simp add: if_apply_def2)
     apply (rule lookup_slot_for_cnode_op_rvu' [where r=sz and cap=src_cap and
       R="\<box> (sz', (unat dest_depth)): target dest_index \<mapsto>u NullCap \<and>* R"])
    apply simp
    apply (rule ensure_empty_no_exception)
   apply (rule lookup_slot_for_cnode_op_rvu'[where r=sz' and cap=NullCap and
     R="\<box> (sz, (unat src_depth)): cap src_index \<mapsto>u src_cap \<and>* R"])
  apply (simp, wp throw_on_none_rv validE_R_validE)
  apply (clarsimp split: option.splits)
  apply (intro conjI)
    apply (clarsimp simp:user_pointer_at_def Let_def)
    apply (clarsimp simp:sep_conj_assoc)
    apply (sep_solve)
   apply (clarsimp dest!: mapu_dest_opt_cap cap_type_null
                          reset_cap_asid_simps2[OF sym]
                    simp: cap_type_def)
  apply (sep_solve)
  done


crunches  decode_cnode_invocation
  for preserve[wp]: "P"
  (wp: derive_cap_wpE unlessE_wp whenE_wp hoare_drop_imps simp: if_apply_def2 throw_on_none_def)

lemma decode_invocation_wp:
  "\<lbrace>P\<rbrace> decode_invocation (CNodeCap x y z sz) ref caps (CNodeIntent intent) \<lbrace>\<lambda>_. P\<rbrace>, -"
  apply (clarsimp simp: decode_invocation_def)
  apply (wp)
    apply (clarsimp simp: comp_def)
    apply (wpsimp simp: throw_opt_def)+
done

lemma lookup_slot_wp:
  "\<lbrace>P\<rbrace> lookup_slot cnode_ptr ptr \<lbrace>\<lambda>_. P\<rbrace>, \<lbrace>\<lambda>_. P\<rbrace>"
  apply (clarsimp simp: lookup_slot_def)
  apply (clarsimp simp: gets_the_resolve_cap[symmetric] split_def)
  apply (wp get_cap_wp)
  apply (clarsimp)
done

lemma always_empty_wp:
  "\<lbrace><ptr  \<mapsto>c - \<and>* R>\<rbrace>
     always_empty_slot ptr
   \<lbrace>\<lambda>_. < ptr  \<mapsto>c NullCap \<and>* R>\<rbrace>"
  by (clarsimp simp: always_empty_slot_def, wp remove_parent_wp set_cap_wp)

lemma fast_finalise_cap_non_ep_wp:
  "\<lbrace><P> and K (\<not> ep_related_cap cap') \<rbrace> fast_finalise cap' final \<lbrace>\<lambda>y. <P>\<rbrace>"
  by (case_tac cap',simp_all add:ep_related_cap_def)

lemma delete_cap_simple_wp:
 "\<lbrace>\<lambda>s. <ptr  \<mapsto>c cap  \<and>* R> s \<and> \<not> ep_related_cap cap\<rbrace>
    delete_cap_simple ptr
  \<lbrace>\<lambda>_. < ptr  \<mapsto>c NullCap \<and>* R>\<rbrace>"
  apply (clarsimp simp: delete_cap_simple_def is_final_cap_def)
  apply (wp unless_wp always_empty_wp fast_finalise_cap_non_ep_wp)
  apply clarsimp
  apply (frule opt_cap_sep_imp)
  apply (clarsimp, rule conjI)
   apply clarsimp
   apply (metis reset_cap_asid_simps2(1))
  apply clarsimp
  apply (rule conjI)
   apply sep_solve
  apply (metis reset_cap_asid_ep_related_cap)
  done

lemma is_cnode_cap_has_object [simp]:
  "is_cnode_cap cnode_cap \<Longrightarrow> cap_has_object cnode_cap"
  by (clarsimp simp: cap_type_def cap_has_object_def split: cdl_cap.splits)

(* MOVEME *)
lemma K_extract:
  "(K P \<and>* Q) s \<Longrightarrow> P"
  by (auto simp: sep_conj_def)

lemmas K_extract' = K_extract [simplified K_def]

lemma user_pointer_at_cnode_cap':
  "(\<box> (r, word_bits) : cnode_cap cap_ptr \<mapsto>u cap') s
  \<Longrightarrow> is_cnode_cap cnode_cap"
  by (clarsimp simp: user_pointer_at_def Let_unfold)

lemma user_pointer_at_cnode_cap:
  "(\<box> (r, word_bits) : cnode_cap cap_ptr \<mapsto>u cap' \<and>* R) s
  \<Longrightarrow> is_cnode_cap cnode_cap"
  by (drule sep_conj_impl, erule user_pointer_at_cnode_cap', assumption+, erule K_extract')

lemma lookup_slot_rvu:
  "\<lbrace>\<lambda>s. Q (cap_object cnode_cap, offset cap_ptr r) s \<and>
    < (thread,tcb_cspace_slot) \<mapsto>c cnode_cap \<and>*
    \<box> (r, word_bits) : cnode_cap cap_ptr \<mapsto>u cap' \<and>* R> s\<rbrace>
     lookup_slot thread cap_ptr
   \<lbrace>Q\<rbrace>, \<lbrace>Q'\<rbrace> "
  apply (clarsimp simp: lookup_slot_def gets_the_resolve_cap[symmetric] split_def)
  apply (rule bindE_wp)+
    apply (rule returnOk_wp)
   apply (rule resolve_cap_u_nf [where r=r])
  apply (rule hoare_pre, wp)
  apply (clarsimp simp: mapu_dest_opt_cap)
  apply (sep_frule (direct) opt_cap_sep_imp )
  apply (sep_frule (direct) user_pointer_at_cnode_cap)
  apply (clarsimp)
  apply (frule (1) reset_cap_asid_cnode_cap)
  apply fastforce
  done

lemma lookup_cap_rvu :
"\<lbrace>\<lambda>s. (\<forall>c. reset_cap_asid c = reset_cap_asid cap' \<longrightarrow> Q c s) \<and>
    < (thread,tcb_cspace_slot) \<mapsto>c cnode_cap \<and>*
    \<box> (r, word_bits) : cnode_cap cap_ptr \<mapsto>u cap' \<and>* R> s\<rbrace>
     lookup_cap thread cap_ptr
   \<lbrace>Q\<rbrace>, \<lbrace>\<lambda>_ _. False\<rbrace>"
  apply (clarsimp simp: lookup_cap_def)
  using hoare_vcg_prop[wp del]
  apply (wp lookup_slot_rvu [where cnode_cap=cnode_cap] get_cap_rv)
  apply (clarsimp)
  apply safe
    apply (clarsimp simp: user_pointer_at_def sep_conj_assoc Let_unfold)
    apply (sep_solve)
   apply clarsimp
  apply sep_solve
  done

lemma lookup_cap_wp:
  "\<lbrace>P\<rbrace> lookup_cap thread cap_ptr \<lbrace>\<lambda>_. P\<rbrace>, \<lbrace>\<lambda>_ .P \<rbrace> "
  apply (clarsimp simp: lookup_cap_def)
  apply (wp lookup_slot_wp get_cap_wp)
  done


lemma lookup_cap_and_slot_rvu:
  "\<lbrace>\<lambda>s. (\<forall>c. reset_cap_asid c = reset_cap_asid cap' \<longrightarrow>
             Q (c, (cap_object cap, offset cap_ptr r) ) s) \<and>
    < (thread,tcb_cspace_slot) \<mapsto>c cap \<and>*
    \<box> (r, word_bits) : cap cap_ptr \<mapsto>u cap' \<and>* R> s\<rbrace>
     lookup_cap_and_slot thread cap_ptr
   \<lbrace>Q\<rbrace>, \<lbrace>Q'\<rbrace> "
  apply (clarsimp simp: lookup_cap_and_slot_def)
  apply (rule bindE_wp)+
    apply (rule returnOk_wp)
   apply (wp get_cap_rv)
  apply (rule hoare_pre, wp lookup_slot_rvu)
  apply (safe)
    apply (clarsimp simp: user_pointer_at_def Let_unfold sep.mult_assoc)
    apply sep_solve
   apply clarsimp
  apply fastforce
  done


lemma update_cap_data:
  "\<lbrace>\<lambda>s. valid_src_cap cap badge \<and> cap_has_type cap
   \<and> ((is_ep_cap cap \<or> is_ntfn_cap cap) \<longrightarrow> \<not> preserve \<and> cap_badge cap = 0)
   \<and> Q (update_cap_data_det badge cap) s \<rbrace>
  update_cap_data preserve badge cap
  \<lbrace>\<lambda>rv s. Q rv s\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp: Let_def update_cap_data_def update_cap_data_det_def
                        valid_src_cap_def
                        cnode_cap_size_def ep_related_cap_def guard_update_def
                 split: cdl_cap.splits | wp)+
  done

lemma is_exclusive_cap_update_cap_data:
  "safe_for_derive (update_cap_data_det badge cap) = safe_for_derive cap"
  apply (rule iffI)
   apply (simp_all add: safe_for_derive_def update_cap_data_def update_cap_data_det_def)
   apply (case_tac cap, simp_all add: safe_for_derive_def badge_update_def
                               split: if_split_asm)
  apply (case_tac cap, simp_all add: badge_update_def guard_update_def
                                     update_cap_badge_def
                              split: if_split_asm)
  done

lemma cap_object_update_cap_rights:
  "cap_object (update_cap_rights rights src_cap) = cap_object src_cap"
  apply (simp add: cap_object_def update_cap_rights_def
            split: cdl_cap.splits)
  done

lemma derived_cap_update_cap_data_det_NullCap [simp]:
  "(derived_cap (update_cap_data_det badge cap) = NullCap)
 = (derived_cap cap = NullCap)"
  by (clarsimp simp: derived_cap_def update_cap_data_det_def
                     badge_update_def update_cap_badge_def guard_update_def
              split: cdl_cap.splits if_split_asm)

lemma derived_cap_update_cap_rights_NullCap [simp]:
  "(derived_cap (update_cap_rights rights cap) = NullCap)
 = (derived_cap cap = NullCap)"
  by (clarsimp simp: derived_cap_def update_cap_rights_def
              split: cdl_cap.splits if_split_asm)

lemma derived_cap_reset_cap_asid_NullCap:
  "\<lbrakk>reset_cap_asid cap = reset_cap_asid cap'; derived_cap cap = NullCap\<rbrakk>
  \<Longrightarrow> derived_cap cap' = NullCap"
  by (clarsimp simp: derived_cap_def reset_cap_asid_def split: cdl_cap.splits)

lemma derived_cap_update_cap_data_det:
  "derived_cap (update_cap_data_det badge cap) =
   update_cap_data_det badge (derived_cap cap)"
  apply (clarsimp simp: derived_cap_def update_cap_data_det_def)
  apply (case_tac cap, simp_all add: update_cap_data_det_def badge_update_def
                                     derived_cap_def update_cap_badge_def guard_update_def)
  done

lemma cnode_cap_size_upd_cap_rights[simp]:
  "is_cnode_cap src_cap
  \<Longrightarrow> cnode_cap_size (update_cap_rights rights src_cap) = cnode_cap_size src_cap"
  by (simp add: update_cap_rights_def cnode_cap_size_def
         split: cdl_cap.splits)

lemma has_type_default_not_non:
  "cap_type spec_cap = Some type
  \<Longrightarrow> default_cap type ids sz dev \<noteq>  NullCap"
  by (clarsimp simp: default_cap_def cap_type_def
              split: cdl_cap.splits)

lemma ep_related_cap_default_cap:
 "cap_type cap = Some type \<Longrightarrow>
  ep_related_cap (default_cap type ids sz dev) = ep_related_cap cap"
  by (fastforce simp: cap_type_def ep_related_cap_def default_cap_def
               split: cdl_cap.splits cdl_object_type.splits)

lemma cap_has_type_update_rights[simp]:
  "cap_has_type (update_cap_rights rights cap) = cap_has_type cap"
  by (clarsimp simp: cap_type_def update_cap_rights_def
              split: cdl_cap.splits)

lemma cap_has_type_asid_cong:
  "reset_cap_asid cap' = reset_cap_asid src_cap
  \<Longrightarrow> cap_has_type cap' = cap_has_type src_cap"
  by (drule reset_cap_asid_cap_type, simp)

(* FIXME: MOVE *)
fun is_reply_cap
  where "is_reply_cap (ReplyCap _ _) = True"
      | "is_reply_cap _ = False"

lemma ep_related_capI:
  "is_ep_cap cap \<Longrightarrow> ep_related_cap cap"
  "is_ntfn_cap cap \<Longrightarrow> ep_related_cap cap"
  "is_reply_cap cap \<Longrightarrow> ep_related_cap cap"
  by (cases cap; simp add: ep_related_cap_def cap_type_def)+

lemma decode_cnode_mint_rvu:
  "\<lbrace>\<lambda>s. caps \<noteq> [] \<and>
    cap_has_type src_cap \<and> valid_src_cap src_cap badge
    \<and> ((is_ep_cap src_cap \<or> is_ntfn_cap src_cap) \<longrightarrow>
           cap_badge src_cap = 0)
    \<and> (\<forall>src_cap'. (reset_cap_asid src_cap'
       = reset_cap_asid src_cap) \<longrightarrow>
         (let x = update_cap_data_det badge (update_cap_rights (cap_rights src_cap \<inter> rights) src_cap') in
         Q (InsertCall (derived_cap x)
           (cap_object (fst $ the $ get_index caps 0), offset src_index src_sz)
           (cap_object target, offset dest_index dest_sz)) s
    ))
    \<and> unat src_depth \<le> word_bits \<and> 0 < unat src_depth
    \<and> unat dest_depth \<le> word_bits \<and> 0 < unat dest_depth
    \<and> < \<box> (src_sz, (unat src_depth)): (fst (the $ get_index caps 0)) src_index \<mapsto>u src_cap
      \<and>* \<box> (dest_sz, (unat dest_depth)): target dest_index \<mapsto>u NullCap \<and>* R> s \<and> Q' s  \<rbrace>
      decode_cnode_invocation target target_ref caps
      (CNodeMintIntent dest_index dest_depth src_index src_depth rights badge)
     \<lbrace>\<lambda>rv s. Q rv s\<rbrace>, \<lbrace>\<lambda>r. Q'\<rbrace>"
  apply (unfold validE_def)
  apply (rule hoare_name_pre_state)
  apply (unfold validE_def[symmetric])
  apply (clarsimp simp: neq_Nil_conv decode_cnode_invocation_def split_def
                 split: sum.splits)
  apply (wp derive_cap_invE)
       apply (wp update_cap_data)+
     apply (rule validE_validE_R)
     apply (simp add: if_apply_def2)
     apply (rule lookup_slot_for_cnode_op_rvu' [where r=src_sz and cap=src_cap and
       R="\<box> (dest_sz, (unat dest_depth)): target dest_index \<mapsto>u NullCap \<and>* R"])
    apply simp
    apply (rule ensure_empty_no_exception)
   apply (rule_tac R="\<box> (src_sz, (unat src_depth)): a src_index \<mapsto>u src_cap \<and>* R"
     in lookup_slot_for_cnode_op_rvu'[where r=dest_sz and cap=NullCap])
  apply (simp, wp throw_on_none_rv validE_R_validE)
  apply (clarsimp simp:Let_def get_index_def split: option.splits
    cong:cap_rights_reset_cap_asid
         cap_object_reset_cap_asid)
  apply (intro conjI)
    apply (clarsimp simp:user_pointer_at_def Let_def)
    apply (clarsimp simp:sep_conj_assoc)
    apply (sep_erule sep_cancel, assumption)
   apply (clarsimp dest!: mapu_dest_opt_cap
     simp:conj_comms is_exclusive_cap_update_cap_data
     safe_for_derive_not_non valid_src_cap_def)
   apply (intro conjI impI allI)
       apply (metis reset_cap_asid_cap_type)
      apply (frule (1) reset_cap_asid_ep_cap[THEN iffD1])
      apply simp
      apply (metis reset_cap_asid_cap_badge ep_related_capI(1))
     apply (frule (1) reset_cap_asid_ntfn_cap[THEN iffD1])
     apply simp
     apply (metis reset_cap_asid_cap_badge ep_related_capI(2))
    apply (metis option.inject reset_cap_asid_cnode_cap)
   apply (metis cap_rights_reset_cap_asid)
  apply sep_solve
  done

lemma non_cap_cong:
  "reset_cap_asid cap' = reset_cap_asid src_cap
  \<Longrightarrow> (cap' = NullCap) = (src_cap = NullCap)"
  by (rule iffI,simp_all add:reset_cap_asid_def
    split:cdl_cap.splits)

lemma update_cap_data_non:
  "(update_cap_data_det badge cap' = NullCap) = (cap' = NullCap)"
  by (rule iffI,
      simp_all add: update_cap_data_det_def badge_update_def
                    guard_update_def update_cap_badge_def
             split: cdl_cap.splits if_split_asm)

lemma decode_cnode_mutate_rvu:
  "\<lbrace>\<lambda>s. caps \<noteq> []
    \<and> < \<box> (src_sz, (unat src_depth)):  (fst (the $ get_index caps 0)) src_index \<mapsto>u src_cap
    \<and>* \<box> (dest_sz, (unat dest_depth)):  target dest_index \<mapsto>u NullCap \<and>* R> s
    \<and>  valid_src_cap src_cap badge \<and> \<not> ep_related_cap src_cap \<and> cap_has_type src_cap
    \<and> unat src_depth \<le> word_bits \<and> 0 < unat src_depth
    \<and> unat dest_depth \<le> word_bits \<and> 0 < unat dest_depth
    \<and> (\<forall>src_cap'. reset_cap_asid src_cap'
       = reset_cap_asid src_cap
       \<longrightarrow>  Q (MoveCall (update_cap_data_det badge src_cap') (cap_object (fst (the $ get_index caps 0)), offset src_index src_sz)
            (cap_object target, offset dest_index dest_sz)) s)\<rbrace>
    decode_cnode_invocation target target_ref caps
     (CNodeMutateIntent dest_index dest_depth src_index src_depth badge)
   \<lbrace>\<lambda>rv s. Q rv s\<rbrace>, \<lbrace>Q'\<rbrace>"
  apply (unfold validE_def)
  apply (rule hoare_name_pre_state)
  apply (unfold validE_def[symmetric])
  apply clarsimp
  apply (frule cap_type_null)
  apply (clarsimp simp: decode_cnode_invocation_def split_def neq_Nil_conv
    split:sum.splits)
  apply wp
        apply (wp update_cap_data)+
     apply (simp add: if_apply_def2)
     apply (rule lookup_slot_for_cnode_op_rvu' [where r=src_sz and cap=src_cap and
       R="\<box> (dest_sz, (unat dest_depth)): target dest_index \<mapsto>u NullCap \<and>* R"])
    apply simp
    apply (rule ensure_empty_no_exception)
   apply (rule_tac R="\<box> (src_sz, (unat src_depth)): a src_index \<mapsto>u src_cap \<and>* R" in
     lookup_slot_for_cnode_op_rvu'[where r=dest_sz and cap=NullCap])
  apply (simp, wp throw_on_none_rv validE_R_validE)
  apply (clarsimp simp:Let_def get_index_def split: option.splits)
  apply (intro conjI)
    apply (clarsimp simp:user_pointer_at_def Let_def)
    apply (clarsimp simp:sep_conj_assoc)
    apply (sep_solve)
   apply (clarsimp dest!: mapu_dest_opt_cap
     simp: conj_comms update_cap_data_non cong:non_cap_cong)
   apply (subst (asm) reset_cap_asid_ep_related_cap[OF sym], assumption)
   apply (metis reset_cap_asid_cap_type valid_src_cap_asid_cong ep_related_capI(1-2))
  apply sep_solve
  done

lemma do_kernel_op_pull_back:
  "\<lbrace>\<lambda>s. P s\<rbrace> oper \<lbrace>\<lambda>r. Q r\<rbrace> \<Longrightarrow>
   \<lbrace>\<lambda>s. P (kernel_state s)\<rbrace> do_kernel_op oper \<lbrace>\<lambda>r s. Q r (kernel_state s)\<rbrace>"
  apply (simp add:do_kernel_op_def)
    apply (wp|wpc)+
  apply (auto simp:valid_def)
  done

lemma get_thread_sep_wp:
  "\<lbrace>tcb_at' Q thread\<rbrace>
    get_thread thread
   \<lbrace>\<lambda>rv s. Q rv\<rbrace>"
  apply (simp add: get_thread_def | wp | wpc)+
  apply (auto simp: object_at_def)
  done

lemma get_thread_inv:
  "\<lbrace> Q \<rbrace> get_thread thread \<lbrace>\<lambda>t s. Q s\<rbrace>"
  unfolding get_thread_def
  by wpsimp

lemma get_thread_sep_wp_precise:
  "\<lbrace>\<lambda>s. tcb_at' (\<lambda>tcb. Q tcb s) thread s \<rbrace>
    get_thread thread
   \<lbrace>\<lambda>rv. Q rv\<rbrace>"
  apply (simp add:get_thread_def | wp | wpc)+
  apply (auto simp: object_at_def)
  done

(* We are not interested in ep related invocation *)
definition nonep_invocation :: "cdl_invocation \<Rightarrow> bool"
where "nonep_invocation iv \<equiv>  case iv of
       InvokeEndpoint cdl_endpoint_invocation \<Rightarrow> False
     | InvokeNotification cdl_notification_invocation \<Rightarrow> False
     | InvokeReply cdl_reply_invocation \<Rightarrow> False
     | _ \<Rightarrow> True"

lemma has_restart_cap_sep_wp:
  "\<lbrace>\<lambda>s. < (thread,tcb_pending_op_slot) \<mapsto>c cap \<and>* sep_true> s \<and> Q (cap = RestartCap) s\<rbrace>
    has_restart_cap thread
   \<lbrace>\<lambda>rv. Q rv\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp: object_at_def)
  apply (wpsimp simp: object_at_def get_thread_def has_restart_cap_def | intro conjI)+
  apply (clarsimp dest!: opt_cap_sep_imp
                   simp: opt_cap_def slots_of_def)
  apply (clarsimp simp: object_slots_def)
  apply (erule rsubst)
  apply (clarsimp simp: reset_cap_asid_def split: cdl_cap.splits)
  done

lemma lift_do_kernel_op':
  "\<lbrace>\<lambda>s'. P s'\<rbrace> f \<lbrace>\<lambda>_ s'. Q s'\<rbrace> \<Longrightarrow> \<lbrace>\<lambda>s. P (kernel_state s)\<rbrace> do_kernel_op f \<lbrace>\<lambda>_ s. Q (kernel_state s)\<rbrace>"
  apply (simp add: do_kernel_op_def split_def)
  apply wp
  apply (simp add: valid_def split_def)
  done

lemma lift_do_kernel_op:
  "\<lbrace>\<lambda>s. s = s'\<rbrace> f \<lbrace>\<lambda>_ s. s = s'\<rbrace> \<Longrightarrow> \<lbrace>\<lambda>s. (kernel_state s) = s'\<rbrace> do_kernel_op f \<lbrace>\<lambda>_ s. (kernel_state s) = s'\<rbrace>"
  apply (simp add: do_kernel_op_def split_def)
  apply wp
  apply (simp add: valid_def split_def)
  done

lemma switch_to_thread_wp:
  "\<lbrace>\<lambda>s. P (cdl_objects s)\<rbrace>
   switch_to_thread t
   \<lbrace>\<lambda>r s. P (cdl_objects s)\<rbrace>"
  by (wpsimp simp: switch_to_thread_def)

lemma switch_to_thread_current_thread_wp:
  "\<lbrace>\<lambda>s. P t\<rbrace>
   switch_to_thread t
   \<lbrace>\<lambda>r s. P (cdl_current_thread s)\<rbrace>"
  by (wpsimp simp: switch_to_thread_def)

lemma schedule_no_choice_wp:
  "\<lbrace>\<lambda>s.  cdl_current_thread s = Some current_thread \<and> cdl_current_domain s = current_domain \<and> P s \<rbrace>
    schedule
  \<lbrace>\<lambda>r s. cdl_current_thread s = Some current_thread \<and> cdl_current_domain s = current_domain \<longrightarrow>  P s\<rbrace>"
  apply (simp add:schedule_def  switch_to_thread_def change_current_domain_def)
  apply wp
  apply (case_tac s,clarsimp)
  done

end
