(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Ipc_DR
imports CNode_DR
begin

context begin interpretation Arch . (*FIXME: arch_split*)

abbreviation
  "thread_is_running y s \<equiv> st_tcb_at ((=) Structures_A.Running) y s"

lemmas [wp] = abs_typ_at_lifts[OF set_simple_ko_typ_at]

lemma set_object_cur_thread_idle_thread:
  "\<lbrace>\<lambda>s. P (cur_thread s) (idle_thread s)\<rbrace> KHeap_A.set_object word x
         \<lbrace>\<lambda>yb s. P (cur_thread s) (idle_thread s)\<rbrace>"
  by (wpsimp wp: set_object_wp)

lemma set_thread_state_cur_thread_idle_thread:
  "\<lbrace>\<lambda>s. P (cur_thread s) (idle_thread s) \<rbrace> set_thread_state thread x \<lbrace>\<lambda>rv s. P (cur_thread s)  (idle_thread s)\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wp set_object_cur_thread_idle_thread dxo_wp_weak | simp)+
  done

lemma thread_set_cur_thread_idle_thread:
  " \<lbrace>\<lambda>s. P (cur_thread s) (idle_thread s)\<rbrace> thread_set (tcb_fault_update Map.empty) word  \<lbrace>\<lambda>xg s. P (cur_thread s) (idle_thread s)\<rbrace>"
  apply (simp add:thread_set_def)
  apply (wp set_object_cur_thread_idle_thread)
  apply simp
done

lemma as_user_cur_thread_idle_thread:
  "\<lbrace>\<lambda>s. P (cur_thread s) (idle_thread s)\<rbrace> as_user thread x \<lbrace>\<lambda>rv s. P (cur_thread s) (idle_thread s)\<rbrace>"
  by (wpsimp wp: set_object_cur_thread_idle_thread simp: as_user_def split_def)

lemma do_fault_transfer_cur_thread_idle_thread:
  "\<lbrace>\<lambda>s. P (cur_thread s) (idle_thread s)\<rbrace> do_fault_transfer c a e recv_buffer \<lbrace>\<lambda>rv s. P (cur_thread s) (idle_thread s)\<rbrace>"
  apply (simp add:do_fault_transfer_def set_message_info_def)
  apply (wp as_user_cur_thread_idle_thread |wpc|clarsimp)+
  apply (wps | wp transfer_caps_it copy_mrs_it | simp)+
  apply wpc
  apply (wp | simp add:thread_get_def)+
done

lemma do_normal_transfer_cur_thread_idle_thread:
  "\<lbrace>\<lambda>s. P (cur_thread s) (idle_thread s) \<rbrace> Ipc_A.do_normal_transfer a b c d e f g \<lbrace>\<lambda>rv s. P (cur_thread s)  (idle_thread s)\<rbrace>"
  apply (simp add:do_normal_transfer_def set_message_info_def cong: if_cong)
  apply (wp as_user_cur_thread_idle_thread |wpc|clarsimp)+
  apply (wps | wp transfer_caps_it copy_mrs_it)+
  apply clarsimp
done

lemma do_ipc_transfer_cur_thread_idle_thread:
  "\<lbrace>\<lambda>s. P (cur_thread s) (idle_thread s) \<rbrace> Ipc_A.do_ipc_transfer a b c d e \<lbrace>\<lambda>rv s. P (cur_thread s)  (idle_thread s)\<rbrace>"
  apply (simp add:do_ipc_transfer_def)
  apply (wp do_fault_transfer_cur_thread_idle_thread do_normal_transfer_cur_thread_idle_thread|wpc)+
  apply (wp | simp add:thread_get_def)+
done

lemma handle_reply_cur_thread_idle_thread:
  "\<lbrace>\<lambda>s. P (cur_thread s) (idle_thread s)\<rbrace> Syscall_A.handle_reply
            \<lbrace>\<lambda>rv s. P (cur_thread s) (idle_thread s) \<rbrace>"
  apply (simp add:handle_reply_def)
  apply (wp do_ipc_transfer_cur_thread_idle_thread|wpc)+
          apply (clarsimp simp:Ipc_A.do_reply_transfer_def)
          apply (wp set_thread_state_cur_thread_idle_thread dxo_wp_weak
                |wpc|simp add: trans_state_def)+
               apply ((wps|wp cap_delete_one_it)+)[1]
              apply (wp do_ipc_transfer_cur_thread_idle_thread dxo_wp_weak)+
                    apply (clarsimp simp: trans_state_def)
                   apply (case_tac xf)
                   apply (simp | wp set_thread_state_cur_thread_idle_thread
                                    thread_set_cur_thread_idle_thread)+
                 apply ((wps | wp)+)[1]
                apply wp+
             apply ((wps | wp cap_delete_one_it)+)[1]
            apply (rule hoare_drop_imp | rule hoare_conjI | rule hoare_allI | wp)+
    apply simp+
done

declare pbfs_atleast_pageBits [simp]

lemma dcorres_move_guard:
  "dcorres r P P' a c \<Longrightarrow> dcorres r \<top> (P' and (P o transform)) a c"
  apply (rule corres_underlyingI)
   apply (erule (1) corres_underlyingE, simp_all)[1]
   apply (fastforce intro: bexI [rotated])
  apply simp
  done

lemma dcorres_move_guard_back:
  "dcorres r \<top> (P' and (P o transform)) a c \<Longrightarrow> dcorres r P P' a c"
  apply (rule corres_underlyingI)
  apply (erule (1) corres_underlyingE, rule TrueI)
  apply (fastforce intro: bexI [rotated])+
  done

lemma dcorres_move_guard_iff:
  "dcorres r P P' a c = dcorres r \<top> (P' and (P o transform)) a c"
  apply (rule iffI)
   apply (erule dcorres_move_guard)
  apply (erule dcorres_move_guard_back)
  done

lemma transform_cdt_cong:
  "\<lbrakk> cdt s = cdt s'; interrupt_irq_node s = interrupt_irq_node s' \<rbrakk> \<Longrightarrow> transform_cdt s = transform_cdt s'"
  unfolding transform_cdt_def by (simp)

lemma transform_current_thread_cong:
  "\<lbrakk> cur_thread s = cur_thread s'; idle_thread s = idle_thread s' \<rbrakk> \<Longrightarrow> transform_current_thread s = transform_current_thread s'"
  unfolding transform_current_thread_def by (simp)

lemma cap_installed_at_irq_weak_cong:
  "\<lbrakk> w = w'; caps_of_state s = caps_of_state s'; interrupt_irq_node s = interrupt_irq_node s' \<rbrakk> \<Longrightarrow> cap_installed_at_irq w s = cap_installed_at_irq w' s'"
  unfolding cap_installed_at_irq_def by (simp)

lemmas transform_congs = transform_cdt_cong transform_current_thread_cong
                         cap_installed_at_irq_weak_cong caps_of_state_pspace
lemma is_arch_page_capE:
  assumes ispc: "is_arch_page_cap cap"
  and     rl:   "\<And>buf rights sz mapdata dev. \<lbrakk> cap = cap.ArchObjectCap (arch_cap.PageCap dev buf rights sz mapdata)\<rbrakk> \<Longrightarrow> R"
  shows   "R"
  using ispc unfolding is_arch_page_cap_def
  apply (simp split:  cap.splits arch_cap.splits)
  apply (erule rl)
  done

lemma get_ipc_buffer_words_Nil:
  "get_ipc_buffer_words ms tcb [] = []"
  unfolding get_ipc_buffer_words_def
  by (auto simp: mapM_Nil split: cap.splits arch_cap.splits)

lemma det_loadWord:
  "is_aligned x 2 \<Longrightarrow> det (loadWord x)"
  unfolding loadWord_def
  by (simp add: is_aligned_mask)

definition
  "functional f \<equiv> (\<forall>P. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. P\<rbrace>)"

lemma return_functional [simp]:
  "functional (return x)"
  unfolding functional_def by (rule allI, wp)

lemma functional_from_wp:
  "(\<And>P. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. P\<rbrace>) \<Longrightarrow> functional f"
  unfolding functional_def
  by clarsimp

lemma detE:
  "\<lbrakk> det f; \<And>a b. fst (f s) = {(a, b)} \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  unfolding det_def
  apply (drule spec [where x = s])
  apply fastforce
  done

(* might be an equality *)
lemma evalMonad_from_wp:
  "\<lbrakk> \<lbrace>(=) s\<rbrace> f \<lbrace>\<lambda>rv _. P rv\<rbrace>; det f \<rbrakk> \<Longrightarrow> P (the (evalMonad f s))"
  apply (erule detE [where s = s])
  apply (drule use_valid [rotated])
  apply (rule refl)
  apply (erule in_singleton)
  apply (clarsimp simp: evalMonad_def)
  done

lemma evalMonad_bind_functional:
  "\<lbrakk> functional f; det f \<rbrakk> \<Longrightarrow> evalMonad (f >>= g) s = evalMonad (g (the (evalMonad f s))) s "
  unfolding evalMonad_def
  apply (erule detE [where s = s])
  apply (clarsimp simp: bind_def)
  apply (drule in_inv_by_hoareD [OF _ in_singleton, rotated])
   apply (clarsimp simp: functional_def)
  apply simp
  done

lemma mapM_functional:
  assumes fn: "\<And>n. functional (f n)"
  shows   "functional (mapM f ns)"
  apply (rule functional_from_wp)
  apply (wp mapM_wp')
   apply (rule fn [unfolded functional_def, THEN spec])
  apply assumption
  done

lemma evalMonad_mapM_functional:
  assumes fn: "\<And>n. functional (f n)"
  and    det: "\<And>n. n \<in> set ns \<Longrightarrow> det (f n)"
  shows   "the (evalMonad (mapM f ns) s) = map (\<lambda>n. the (evalMonad (f n) s)) ns"
  using det
proof (induct ns)
  case Nil
  thus ?case by (simp add: mapM_Nil)
next
  case (Cons n ns')

  have det': "det (f n)" using Cons.prems by clarsimp

  show ?case
    apply (simp add: mapM_Cons evalMonad_bind_functional [OF fn det'])
    apply (subst evalMonad_bind_functional)
      apply (rule mapM_functional [OF fn])
     apply (rule det_mapM [OF Cons.prems])
      apply assumption
     apply clarsimp
    apply simp
    apply (subst Cons.hyps)
     apply (rule Cons.prems)
     apply simp
    apply simp
    done
qed

lemma loadWord_functional [simp]:
  "functional (loadWord n)"
  unfolding loadWord_def
  apply (rule functional_from_wp)
  apply wp
  apply simp
  done

lemma is_aligned_buffer_offset:
  "\<lbrakk> is_aligned buf (pageBitsForSize sz); is_aligned p msg_align_bits \<rbrakk> \<Longrightarrow>
  is_aligned (buf + (p && mask (pageBitsForSize sz)) + of_nat n * of_nat word_size) 2"
  apply (rule aligned_add_aligned)
     apply (erule aligned_add_aligned)
       apply (erule is_aligned_andI1)
      apply simp
     apply simp
    apply (simp add: word_size_def is_aligned_mult_triv2[where n = 2, simplified]
                     word_bits_conv)
  done

abbreviation
  "ipc_buf_addr buf ptr sz n \<equiv> (buf + (ptr && mask (pageBitsForSize sz)) + of_nat n * of_nat word_size)"

lemma evalMonad_singleton [simp]:
  "evalMonad (\<lambda>s. ({(f s, g s)}, b)) s = Some (f s)"
  unfolding evalMonad_def by simp

lemma mi_length_dest : "of_nat (unat (mi_length rva)) = mi_length rva"
  by (rule word_unat.Rep_inverse)

(* CORRES RULES *)

lemma no_pending_cap_when_active_corres:
  "dcorres (\<lambda>cap rv'. cap = cdl_cap.NullCap) \<top> (st_tcb_at (\<lambda>t. \<not> generates_pending t) thread and not_idle_thread thread and valid_etcbs)
     (KHeap_D.get_cap (thread, tcb_pending_op_slot))
     (return b)"
  apply (simp add:gets_the_def  gets_def  assert_opt_def)
  apply (rule dcorres_absorb_get_l)
  apply (clarsimp simp:st_tcb_at_def obj_at_def)
  apply (frule(1) valid_etcbs_tcb_etcb)
  apply (subst opt_cap_tcb)
     apply (erule get_tcb_rev)
    apply (clarsimp simp: get_etcb_def)
   apply (simp add:not_idle_thread_def)
  apply (clarsimp simp:tcb_pending_op_slot_def tcb_caller_slot_def tcb_cspace_slot_def tcb_ipcbuffer_slot_def
    tcb_replycap_slot_def tcb_vspace_slot_def assert_opt_def)
  apply (clarsimp simp:object_slots_def generates_pending_def infer_tcb_pending_op_def return_def
    split:Structures_A.thread_state.splits)
  done

lemma dummy_finalise_wp[wp]:
  "is_pending_cap obj
         \<Longrightarrow> \<lbrace>(=) s\<rbrace> PageTableUnmap_D.fast_finalise obj (PageTableUnmap_D.is_final_cap' obj s) \<lbrace>\<lambda>x. (=) s\<rbrace>"
  by (clarsimp simp:is_pending_cap_def split:cdl_cap.splits)

lemma cte_at_into_opt_cap:
  "cte_at p s = (\<exists>cap. cte_wp_at ((=) cap) p s
        \<and> (fst p \<noteq> idle_thread s \<and> valid_etcbs s \<longrightarrow> opt_cap (transform_cslot_ptr p) (transform s) = Some (transform_cap cap)))"
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (safe, simp_all)
  apply (clarsimp simp: caps_of_state_transform_opt_cap)
  done

lemma object_slots_has_slots [simp]:
  "object_slots obj p = Some v \<Longrightarrow> has_slots obj"
  unfolding object_slots_def has_slots_def
  by (simp split: cdl_object.splits)

lemma dcorres_when_l:
  assumes tc: "R \<Longrightarrow> dcorres dc \<top> P l r"
  and     fc: "\<not> R \<Longrightarrow> dcorres dc \<top> Q (return ()) r"
  shows "dcorres dc \<top> (\<lambda>s. (R \<longrightarrow> P s) \<and> (\<not> R \<longrightarrow> Q s)) (when R l) r"
  unfolding when_def
  apply (cases R)
   apply simp
   apply (erule tc)
  apply simp
  apply (erule fc)
  done

lemma corres_guard_from_wp_r:
  assumes ac: "corres_underlying sr False False r G G' a c"
  and     rl: "\<lbrace>\<lambda>s. \<not> P s\<rbrace> c \<lbrace>\<lambda>_ _. False\<rbrace>"
  shows "corres_underlying sr False False r G (\<lambda>s. P s \<longrightarrow> G' s) a c"
  apply (rule corres_name_pre)
  apply (case_tac "P s'")
   apply simp
   apply (rule corres_guard_imp)
     apply (rule ac)
    apply simp
   apply simp
  apply (rule corres_underlyingI)
   apply (frule use_valid [OF _ rl])
    apply simp
   apply simp
  apply simp
  done

lemma corres_guard_from_wp_bind_r:
  assumes ac: "corres_underlying sr False False r G G' a (c >>= d)"
  and     rl: "\<lbrace>\<lambda>s. \<not> P s\<rbrace> c \<lbrace>\<lambda>_ _. False\<rbrace>"
  shows "corres_underlying sr False False r G (\<lambda>s. P s \<longrightarrow> G' s) a (c >>= d)"
  apply (rule corres_guard_from_wp_r)
  apply (rule ac)
  apply (wp rl)
  done

lemma thread_set_gwp:
  "dcorres dc P P' a (thread_set f p)
  \<Longrightarrow> dcorres dc P (\<lambda>s. tcb_at p s \<longrightarrow> P' s) a (thread_set f p)"
  unfolding thread_set_def
  apply (erule corres_guard_from_wp_r)
  apply (wp gets_the_wp)
  apply (simp add: tcb_at_def)
  done

lemma sts_gwp:
  "dcorres dc P P' a (set_thread_state p st)
  \<Longrightarrow> dcorres dc P (\<lambda>s. tcb_at p s \<longrightarrow> P' s) a (set_thread_state p st)"
  apply (simp add: set_thread_state_thread_set thread_set_def)
  apply (erule corres_guard_from_wp_r)
  apply (wp gets_the_wp)
  apply (simp add: tcb_at_def)
  done

lemma block_thread_on_send_corres:
  "dcorres dc \<top> (not_idle_thread thread and valid_etcbs)
           (KHeap_D.set_cap (thread, tcb_pending_op_slot)
             (PendingSyncSendCap epptr badge call can_grant can_grant_reply
               False))
           (set_thread_state thread
             (Structures_A.thread_state.BlockedOnSend epptr
               \<lparr>sender_badge = badge, sender_can_grant = can_grant,
                sender_can_grant_reply = can_grant_reply, sender_is_call = call\<rparr>))"
  apply (clarsimp simp:KHeap_D.set_cap_def set_thread_state_def)
  apply (rule dcorres_gets_the, clarsimp)
   apply (rule dcorres_rhs_noop_below_True[OF set_thread_state_ext_dcorres])
   apply (frule(1) valid_etcbs_get_tcb_get_etcb, clarsimp)
   apply (clarsimp simp: obj_at_def not_idle_thread_def opt_object_tcb assert_def
                         transform_tcb_def has_slots_def split: option.splits)
   apply (clarsimp simp:update_slots_def object_slots_def)
   apply (clarsimp simp:set_object_def get_object_def in_monad simpler_modify_def KHeap_D.set_object_def
                        get_def put_def bind_def corres_underlying_def return_def)
   apply (clarsimp simp:transform_def transform_objects_def transform_current_thread_def)
   apply (rule ext)
   apply (clarsimp simp: |rule conjI)+
    apply (fastforce dest!: get_tcb_SomeD get_etcb_SomeD
                      simp: transform_tcb_def infer_tcb_pending_op_def tcb_slot_defs)
   apply (clarsimp simp:restrict_map_def map_add_def)
  apply (clarsimp, frule(1) valid_etcbs_get_tcb_get_etcb)
  apply (fastforce simp:not_idle_thread_def dest!:opt_object_tcb)
  done

lemma block_thread_on_recv_corres:
  "dcorres dc \<top> (not_idle_thread thread and valid_etcbs)
             (KHeap_D.set_cap (thread, tcb_pending_op_slot)
               (PendingSyncRecvCap epptr False can_grant))
             (set_thread_state thread
               (Structures_A.thread_state.BlockedOnReceive epptr \<lparr>receiver_can_grant = can_grant\<rparr>))"
  apply (clarsimp simp:KHeap_D.set_cap_def set_thread_state_def)
  apply (rule dcorres_gets_the, clarsimp)
   apply (rule dcorres_rhs_noop_below_True[OF set_thread_state_ext_dcorres])
   apply (frule(1) valid_etcbs_get_tcb_get_etcb, clarsimp)
   apply (clarsimp simp:not_idle_thread_def opt_object_tcb assert_def
                        transform_tcb_def has_slots_def)
   apply (clarsimp simp:update_slots_def object_slots_def)
   apply (clarsimp simp:set_object_def get_object_def in_monad simpler_modify_def KHeap_D.set_object_def
                        get_def put_def bind_def corres_underlying_def return_def)
   apply (clarsimp simp:transform_def transform_objects_def transform_current_thread_def)
   apply (rule ext)
   apply (clarsimp simp: get_etcb_def|rule conjI)+
    apply (fastforce simp:transform_tcb_def infer_tcb_pending_op_def tcb_slot_defs)
   apply (clarsimp simp:restrict_map_def map_add_def)
  apply (clarsimp, frule(1) valid_etcbs_get_tcb_get_etcb)
  apply (fastforce simp:not_idle_thread_def dest!:opt_object_tcb)
  done

lemma block_thread_on_ntfn_recv_corres:
  "dcorres dc \<top> (not_idle_thread thread and valid_etcbs)
             (KHeap_D.set_cap (thread, tcb_pending_op_slot)
               (PendingNtfnRecvCap w))
             (set_thread_state thread (Structures_A.thread_state.BlockedOnNotification w))"
  apply (clarsimp simp:KHeap_D.set_cap_def set_thread_state_def)
  apply (rule dcorres_gets_the, clarsimp)
   apply (rule dcorres_rhs_noop_below_True[OF set_thread_state_ext_dcorres])
   apply (frule(1) valid_etcbs_get_tcb_get_etcb, clarsimp)
   apply (clarsimp simp:not_idle_thread_def opt_object_tcb assert_def
                        transform_tcb_def has_slots_def)
   apply (clarsimp simp:update_slots_def object_slots_def)
   apply (clarsimp simp:set_object_def get_object_def in_monad simpler_modify_def KHeap_D.set_object_def
                        get_def put_def bind_def corres_underlying_def return_def)
   apply (clarsimp simp:transform_def transform_objects_def transform_current_thread_def)
   apply (rule ext)
   apply (clarsimp simp: get_etcb_def|rule conjI)+
    apply (fastforce simp:transform_tcb_def infer_tcb_pending_op_def tcb_slot_defs)
   apply (clarsimp simp:restrict_map_def map_add_def)
  apply (clarsimp, frule(1) valid_etcbs_get_tcb_get_etcb)
  apply (fastforce simp:not_idle_thread_def dest!:opt_object_tcb)
  done

lemma corres_ignore_ret_lhs: "dcorres rv P P' (do f;g od) f' \<Longrightarrow> dcorres rv P P' (do a\<leftarrow>f;g od) f'"
 by (clarsimp simp:corres_underlying_def)

crunches set_thread_state, set_object
  for not_idle[wp]: "not_idle_thread y :: 'a::state_ext state \<Rightarrow> bool"
  (simp: not_idle_thread_def get_object_def wp: dxo_wp_weak)

lemma set_scheduler_action_dcorres:
  "dcorres dc P P' (return ()) (set_scheduler_action sa)"
  by (clarsimp simp: set_scheduler_action_def modify_def get_def put_def bind_def return_def  corres_underlying_def)


lemma tcb_sched_action_transform_inv: "\<lbrace>\<lambda>ps. transform ps = cs\<rbrace> tcb_sched_action tcb_sched_enqueue t \<lbrace>\<lambda>r s. transform s = cs\<rbrace>"
  apply (clarsimp simp: tcb_sched_action_def)
  apply (wp | simp)+
  done

lemma set_scheduler_action_transform_inv:
  "\<lbrace>\<lambda>ps. transform ps = cs\<rbrace> set_scheduler_action act \<lbrace>\<lambda>r s. transform s = cs\<rbrace>"
  by (wpsimp simp: set_scheduler_action_def)

lemma possible_switch_to_dcorres:
  "dcorres dc P P' (return ()) (possible_switch_to t)"
  apply (clarsimp simp: possible_switch_to_def cong: if_cong)
  apply (rule dcorres_symb_exec_r)+
        apply (rule corres_guard1_imp, rule corres_if_rhs)
          apply (rule tcb_sched_action_dcorres[THEN corres_trivial])
         apply (rule corres_if_rhs)
          apply (rule dcorres_symb_exec_r)+
            apply (rule tcb_sched_action_dcorres[THEN corres_trivial])
           apply (wp set_scheduler_action_transform_inv tcb_sched_action_transform_inv
                 | simp add: reschedule_required_def
                 | wpc
                 | rule set_scheduler_action_dcorres[THEN corres_trivial])+
  done

lemma corres_update_waiting_ntfn_do_notification_transfer:
  "dcorres dc \<top>
    (pspace_aligned and valid_objs and valid_mdb and pspace_distinct and valid_idle and valid_etcbs and
     (st_tcb_at ((=) (Structures_A.thread_state.BlockedOnNotification epptr)) y) and
     valid_ntfn (\<lparr>ntfn_obj = case ys of [] \<Rightarrow> Structures_A.ntfn.IdleNtfn | a # list \<Rightarrow> Structures_A.ntfn.WaitingNtfn ys, ntfn_bound_tcb = bound_tcb\<rparr> ))
          (Endpoint_D.do_notification_transfer y)
          (update_waiting_ntfn epptr (y # ys) bound_tcb badge)"
  apply (simp add: Endpoint_D.do_notification_transfer_def update_waiting_ntfn_def assert_def)
  apply (rule corres_dummy_return_pl)
  apply (rule corres_split_keep_pfx[where r'="dc" and Q="%x. \<top>" and Q'="%x. \<top>"])
     apply (rule corres_guard_imp,rule corres_dummy_set_notification,clarsimp+)
    apply (rule dcorres_expand_pfx)
    apply clarsimp
    apply (frule_tac y = y in  generates_pending_not_idle)
     apply (clarsimp simp:st_tcb_at_def obj_at_def)
     apply (drule_tac t = "tcb_state tcb" in sym)
     apply (simp add:generates_pending_def)
    apply (rule corres_guard_imp)
      apply (rule dcorres_dc_rhs_noop_below_2_True[OF allI[OF possible_switch_to_dcorres]])
      apply (rule corres_split[OF set_thread_state_corres])
        apply (rule set_register_corres)
       apply (wp)+
     apply simp
    apply (frule generates_pending_not_idle[where y = y])
     apply (clarsimp simp: pred_tcb_at_def obj_at_def generates_pending_def)
     apply (drule_tac t = "tcb_state tcb" in sym)
     apply ((clarsimp simp:pred_tcb_at_def obj_at_def not_idle_thread_def split:Structures_A.thread_state.splits)+)[3]
  apply (wp set_simple_ko_aligned set_ep_mdb set_simple_ko_valid_objs sts_typ_ats)
  apply (simp add: not_idle_thread_def a_type_def ntfn_at_def2[symmetric, simplified])
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  apply (drule valid_tcb_objs,erule get_tcb_rev)
  apply (drule_tac t = "tcb_state tcb" in sym)
  apply (clarsimp simp: valid_tcb_def valid_tcb_state_def obj_at_def)
  done

lemma ntfn_waiting_set_spec:
  "\<lbrakk>y\<in> ntfn_waiting_set epptr s\<rbrakk>\<Longrightarrow> st_tcb_at ((=) (Structures_A.thread_state.BlockedOnNotification epptr)) y s"
by (clarsimp simp: ntfn_waiting_set_def st_tcb_at_def obj_at_def)

lemma not_empty_list_not_empty_set:
  "a \<noteq> [] \<Longrightarrow> \<exists>x. x \<in> (set a)"
  apply (case_tac a)
  apply auto
done

lemma set_thread_state_block_on_notification_corres:
    "dcorres dc \<top>
     (not_idle_thread thread and tcb_at thread and valid_etcbs)
     (block_thread_on_ipc thread (PendingNtfnRecvCap w))
     (set_thread_state thread (Structures_A.thread_state.BlockedOnNotification w))"
  apply (simp add: block_thread_on_ipc_def)
  apply (clarsimp simp: KHeap_D.set_cap_def set_thread_state_def)
  apply (rule dcorres_dc_rhs_noop_below_2_True[OF allI[OF set_thread_state_ext_dcorres]])
  apply (rule dcorres_gets_the)
   apply (clarsimp, frule(1) valid_etcbs_get_tcb_get_etcb, clarsimp)
   apply (clarsimp simp: not_idle_thread_def opt_object_tcb assert_def transform_tcb_def has_slots_def)
   apply (clarsimp simp: update_slots_def object_slots_def)
   apply (clarsimp simp: set_object_def get_object_def in_monad simpler_modify_def KHeap_D.set_object_def
                         get_def put_def bind_def corres_underlying_def return_def)
   apply (clarsimp simp: transform_def transform_current_thread_def)
   apply (intro ext conjI)
   apply (case_tac x)
   apply (clarsimp simp: |rule conjI)+
    apply (clarsimp simp: transform_tcb_def transform_objects_def infer_tcb_pending_op_def)
    apply ((fastforce simp: transform_objects_def restrict_map_def map_add_def tcb_at_def
                               transform_tcb_def tcb_slot_defs
                       dest!: get_tcb_SomeD get_etcb_SomeD)+)[2]
  apply (clarsimp, frule(1) valid_etcbs_get_tcb_get_etcb, clarsimp)
  apply (fastforce simp: not_idle_thread_def dest!:opt_object_tcb get_tcb_rev get_etcb_rev)
  done

lemma insert_contr:
  "\<lbrakk>\<forall>x. x \<notin> insert y Q\<rbrakk> \<Longrightarrow> P"
   apply (drule_tac x = y in spec)
   apply (clarsimp simp:insertI1)
done

lemma recv_signal_corres:
  "cap = transform_cap cap' \<Longrightarrow>
  dcorres dc \<top> (invs and not_idle_thread thread and st_tcb_at active thread and valid_etcbs)
             (recv_signal thread cap)
             (receive_signal thread cap' is_blocking)"
  apply (clarsimp simp:receive_signal_def invs_def recv_signal_def corres_free_fail split:cap.splits)
  apply (rename_tac word1 word2 rights)
  apply (rule dcorres_expand_pfx)
  apply (rule_tac Q' = "\<lambda>r. (=) s' and ko_at (kernel_object.Notification r) word1 and valid_ntfn r" in corres_symb_exec_r)
     apply (rule dcorres_expand_pfx)
     apply (clarsimp simp:obj_at_def is_ntfn_def)
     apply (case_tac "ntfn_obj rv"; simp)
       apply (clarsimp simp: ntfn_waiting_set_lift valid_state_def valid_ntfn_abstract_def
                             none_is_waiting_ntfn_def )
       apply (case_tac is_blocking; simp)
        apply (rule corres_guard_imp)
          apply (rule corres_alternate1)
          apply (rule corres_dummy_return_l)
          apply (rule corres_split[OF set_thread_state_block_on_notification_corres])
            apply  (rule corres_dummy_set_notification,simp)
          apply (wp|simp)+
        apply (clarsimp simp:st_tcb_at_def tcb_at_def obj_at_def get_tcb_rev)
       apply (simp add: do_nbrecv_failed_transfer_def)
       apply (rule corres_guard_imp)
         apply (rule corres_alternate2)
         apply (rule corrupt_tcb_intent_as_user_corres)
        apply simp
       apply simp
      (* WaitingNtfn *)
      apply (clarsimp simp: ntfn_waiting_set_lift valid_state_def valid_ntfn_abstract_def
                            none_is_waiting_ntfn_def)
      apply (case_tac is_blocking; simp)
       apply (rule corres_guard_imp)
         apply (rule corres_alternate1)
         apply (rule corres_dummy_return_l)
         apply (rule corres_split[OF set_thread_state_block_on_notification_corres])
           apply  (rule corres_dummy_set_notification,simp)
         apply (wp|simp)+
       apply (clarsimp simp:st_tcb_at_def tcb_at_def obj_at_def get_tcb_rev)
      apply (simp add: do_nbrecv_failed_transfer_def)
      apply (rule corres_guard_imp)
        apply (rule corres_alternate2)
        apply (rule corrupt_tcb_intent_as_user_corres)
       apply simp
      apply simp
     (* Active NTFN *)
     apply (clarsimp simp: ntfn_waiting_set_lift valid_state_def valid_ntfn_abstract_def
                           none_is_waiting_ntfn_def)
     apply (rule corres_alternate2)
     apply (rule corres_guard_imp )
       apply (rule corres_dummy_return_l)
       apply (rule corres_split[OF set_register_corres corres_dummy_set_notification])
        apply (wp |clarsimp)+
     apply (rule_tac Q="\<lambda>r. ko_at (kernel_object.Notification r) word1 and valid_state" in hoare_strengthen_post)
      apply (wp get_simple_ko_ko_at | clarsimp)+
     apply (rule valid_objs_valid_ntfn_simp)
      apply (clarsimp simp:valid_objs_valid_ntfn_simp valid_state_def valid_pspace_def)
     apply (simp add:obj_at_def)
    apply (clarsimp|wp)+
  done

lemma bound_tcb_fold:
  "\<lbrakk>kheap s x = Some (TCB tcb); tcb_bound_notification tcb = Some ntfnptr\<rbrakk> \<Longrightarrow> bound_tcb_at (\<lambda>ntfn. ntfn = Some ntfnptr) x s"
  by (auto simp: pred_tcb_at_def obj_at_def)

lemma receive_blocked_waiting_syncs:
  "\<lbrakk>valid_state s; valid_etcbs s; kheap s ntfnptr = Some (kernel_object.Notification ntfn);
    ntfn_bound_tcb ntfn = Some a; get_tcb a s = Some aa; receive_blocked (tcb_state aa)\<rbrakk>
   \<Longrightarrow> get_waiting_sync_bound_ntfn_threads ntfnptr (transform s) = {a}"
  apply (clarsimp simp: get_waiting_sync_bound_ntfn_threads_def)
  apply (frule get_notification_pick, simp)
  apply (clarsimp simp: valid_ntfn_abstract_def ntfn_bound_set_def get_tcb_def
                 split: Structures_A.kernel_object.splits option.splits)
  apply (rule set_eqI)
  apply clarsimp
  apply (rule iffI)
   apply (clarsimp)
   apply (rule_tac x=aa in exI)
   apply (clarsimp simp: valid_state_def valid_pspace_def)
   apply (frule (3) ntfn_bound_tcb_at[where P="\<lambda>a. a = Some ntfnptr"], simp)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def)
   apply (clarsimp simp: transform_def transform_objects_def restrict_map_def map_add_def
                  split: option.splits)
    apply (subst (asm) handy_if_lemma)+
    apply clarsimp
   apply (case_tac "x \<noteq> idle_thread s")
    apply (clarsimp simp: transform_object_def
                   split: Structures_A.kernel_object.splits ARM_A.arch_kernel_obj.splits
                          option.splits nat.splits)
     apply (frule_tac ptr=x in valid_etcbs_tcb_etcb, simp+)
    apply (clarsimp simp add: transform_tcb_def tcb_pending_op_slot_def
                              tcb_boundntfn_slot_def infer_tcb_bound_notification_def
                       split: option.splits)
    apply (frule_tac tcb="x2a" in  bound_tcb_fold, simp)
    apply (frule (3) bound_tcb_bound_notification_at)
    apply clarsimp
   apply clarsimp
  apply clarsimp
  apply (frule_tac tcb=t in bound_tcb_fold, simp)
  apply (clarsimp simp: valid_state_def valid_pspace_def)
  apply (frule (3) bound_tcb_bound_notification_at)
  apply clarsimp
  apply (drule get_tcb_rev)
  apply (frule (1) valid_etcbs_get_tcb_get_etcb, clarsimp)
  apply (clarsimp simp: transform_def)
  apply (frule (1) transform_objects_tcb)
   apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def)
  apply (clarsimp simp: transform_tcb_def tcb_pending_op_slot_def tcb_boundntfn_slot_def
                        infer_tcb_pending_op_def infer_tcb_bound_notification_def receive_blocked_def
                 split: Structures_A.thread_state.splits)
  done

lemma dcorres_dat:
  "dcorres dc \<top> (valid_etcbs and not_idle_thread a and valid_idle)
           (do_notification_transfer a)
           (do y \<leftarrow> set_thread_state a Structures_A.thread_state.Running;
               y \<leftarrow> as_user a (set_register badge_register badge);
               possible_switch_to a
            od)"
     apply (simp add: Endpoint_D.do_notification_transfer_def)
  apply (rule dcorres_expand_pfx)
  apply clarsimp
  apply (rule corres_guard_imp)
    apply (rule dcorres_dc_rhs_noop_below_2_True[OF allI[OF possible_switch_to_dcorres]])
    apply (rule corres_split[OF set_thread_state_corres])
      apply (rule set_register_corres)
     apply (wp)+
   apply simp
  apply (clarsimp simp: not_idle_thread_def valid_state_def)
  done

lemma not_idle_after_blocked_cancel_ipc:
  "\<lbrace>valid_idle and not_idle_thread obj_id' and valid_objs and st_tcb_at ((=) state) obj_id'\<rbrace>
    blocked_cancel_ipc state obj_id' \<lbrace>\<lambda>y. valid_idle\<rbrace>"
  including no_pre
  apply (simp add:blocked_cancel_ipc_def)
  apply wp
   apply (clarsimp simp:not_idle_thread_def)
   apply (clarsimp simp:get_blocking_object_def)
   apply (case_tac state)
          apply clarsimp+
       apply (clarsimp simp:valid_def return_def st_tcb_at_def valid_objs_def obj_at_def)
       apply (drule_tac x = obj_id' in bspec)
        apply (clarsimp simp:valid_obj_def valid_tcb_def valid_tcb_state_def)+
       apply (drule_tac t = "tcb_state tcb" in sym)
       apply (clarsimp simp:obj_at_def is_ep_def2)
      apply (clarsimp simp:valid_def return_def st_tcb_at_def obj_at_def valid_objs_def)
      apply (drule_tac x = obj_id' in bspec)
       apply (clarsimp simp:valid_obj_def valid_tcb_def valid_tcb_state_def)+
      apply (drule_tac t = "tcb_state tcb" in sym)
      apply (clarsimp simp:obj_at_def is_ep_def2)
     apply (clarsimp)+
  done

lemma valid_idle_set_thread_state:
  "\<lbrace>not_idle_thread xa and valid_idle :: det_state \<Rightarrow> bool\<rbrace> set_thread_state xa Structures_A.thread_state.Restart \<lbrace>\<lambda>xa. valid_idle\<rbrace>"
  apply (simp add: set_thread_state_def not_idle_thread_def)
  apply (simp add: set_object_def get_object_def)
  apply wp
  apply (clarsimp simp: not_idle_thread_def)
  apply (clarsimp simp: obj_at_def dest!:get_tcb_SomeD)
  apply (auto simp: valid_idle_def pred_tcb_at_def obj_at_def)
  done

crunch not_idle_thread[wp]: tcb_sched_action "not_idle_thread a"
  (wp: simp: not_idle_thread_def)

lemma tcb_sched_action_tcb_at_not_idle[wp]:
  "\<lbrace>\<lambda>s. \<forall>x\<in>set list. tcb_at x s \<and> not_idle_thread x s\<rbrace> tcb_sched_action a b
   \<lbrace>\<lambda>x s. \<forall>x\<in>set list. tcb_at x s \<and> not_idle_thread x s\<rbrace>"
  by (wp hoare_Ball_helper)

lemma valid_idle_cancel_all_ipc:
  "\<lbrace>valid_idle and valid_state :: det_state \<Rightarrow> bool\<rbrace> IpcCancel_A.cancel_all_ipc word1 \<lbrace>\<lambda>a. valid_idle\<rbrace>"
  including no_pre
  apply (simp add:cancel_all_ipc_def)
  apply (wp|wpc|simp)+
      apply (rename_tac queue list)
      apply (rule_tac I = "(\<lambda>s. (queue = list) \<and> (\<forall>a\<in> set list. tcb_at a s \<and> not_idle_thread a s))
             and ko_at (kernel_object.Endpoint Structures_A.endpoint.IdleEP) word1  and valid_idle" in mapM_x_inv_wp)
        apply clarsimp
       apply (wp KHeap_DR.tcb_at_set_thread_state_wp)
       apply (rule hoare_conjI)
        apply (rule_tac P="(\<lambda>s. (queue = list) \<and> (\<forall>a\<in> set list. tcb_at a s \<and> not_idle_thread a s))
                  and valid_idle and ko_at (kernel_object.Endpoint Structures_A.endpoint.IdleEP) word1"
               in hoare_vcg_precond_imp)
         apply (wp | clarsimp)+
         apply (rule set_thread_state_ko)
        apply (simp add:is_tcb_def)
       apply (wp valid_idle_set_thread_state)
       apply (clarsimp simp:)+
     apply wp
     apply (rule hoare_vcg_conj_lift)
      apply (rule hoare_Ball_helper)
       apply (wp simple_obj_set_prop_at | clarsimp simp :get_ep_queue_def not_idle_thread_def)+
     apply (rename_tac queue list)
     apply (rule_tac I = "(\<lambda>s. (queue = list) \<and> (\<forall>a\<in> set list. tcb_at a s \<and> not_idle_thread a s))
            and ko_at (kernel_object.Endpoint Structures_A.endpoint.IdleEP) word1  and valid_idle" in mapM_x_inv_wp)
       apply clarsimp
      apply (wp KHeap_DR.tcb_at_set_thread_state_wp)
      apply (rule hoare_conjI)
       apply (rule_tac P="(\<lambda>s. (queue = list) \<and> (\<forall>a\<in> set list. tcb_at a s \<and> not_idle_thread a s))
                       and valid_idle and ko_at (kernel_object.Endpoint Structures_A.endpoint.IdleEP) word1"
              in hoare_vcg_precond_imp)
        apply (rule set_thread_state_ko)
       apply (simp add:is_tcb_def)
      apply (wp valid_idle_set_thread_state)
      apply (clarsimp simp:)+
    apply wp
    apply (rule hoare_vcg_conj_lift)
     apply (rule hoare_Ball_helper)
      apply (wp simple_obj_set_prop_at | clarsimp simp :get_ep_queue_def not_idle_thread_def)+
  apply (rule hoare_strengthen_post[OF get_simple_ko_sp])
  apply (clarsimp  | rule conjI)+
     apply (clarsimp simp:obj_at_def valid_pspace_def valid_state_def)
     apply (drule(1) valid_objs_valid_ep_simp)
     apply (clarsimp simp:is_tcb_def valid_ep_def obj_at_def)
    apply (drule(1) pending_thread_in_send_not_idle)
      apply (simp add:not_idle_thread_def obj_at_def is_ep_def)+
  apply (clarsimp | rule conjI)+
   apply (clarsimp simp:obj_at_def valid_pspace_def valid_state_def)
   apply (drule(1) valid_objs_valid_ep_simp)
   apply (clarsimp simp:is_tcb_def valid_ep_def obj_at_def)
  apply (drule(1) pending_thread_in_recv_not_idle)
    apply (simp add:not_idle_thread_def obj_at_def is_ep_def)+
  done

lemma valid_idle_cancel_all_signals:
  "\<lbrace>valid_idle and valid_state :: det_state \<Rightarrow> bool\<rbrace> IpcCancel_A.cancel_all_signals word1 \<lbrace>\<lambda>a. valid_idle\<rbrace>"
  including no_pre
  apply (simp add:cancel_all_signals_def)
  apply (wp|wpc|simp)+
     apply (rename_tac list)
     apply (rule_tac I = "(\<lambda>s. (\<forall>a\<in> set list. tcb_at a s \<and> not_idle_thread a s))
                    and ko_at (kernel_object.Notification (ntfn_set_obj ntfn Structures_A.ntfn.IdleNtfn)) word1 and valid_idle" in mapM_x_inv_wp)
       apply clarsimp
      apply (wp KHeap_DR.tcb_at_set_thread_state_wp)
      apply (rule hoare_conjI)
       apply (rule_tac P="(\<lambda>s. (\<forall>a\<in> set list. tcb_at a s \<and> not_idle_thread a s))
                and valid_idle and ko_at (kernel_object.Notification (ntfn_set_obj ntfn Structures_A.ntfn.IdleNtfn)) word1"
              in hoare_vcg_precond_imp)
        apply (rule set_thread_state_ko)
       apply (simp add:is_tcb_def)
      apply (wp valid_idle_set_thread_state)+
      apply (clarsimp simp:)+
    apply (rule hoare_vcg_conj_lift)
     apply (rule hoare_Ball_helper)
      apply (wp set_simple_ko_tcb| clarsimp simp : not_idle_thread_def)+
    apply (wp simple_obj_set_prop_at)+
  apply (rule hoare_strengthen_post[OF get_simple_ko_sp])
  apply (clarsimp  | rule conjI)+
    apply (clarsimp simp:obj_at_def valid_pspace_def valid_state_def)
    apply (drule(1) valid_objs_valid_ntfn_simp)
    apply (clarsimp simp:is_tcb_def valid_ntfn_def obj_at_def)
   apply (drule(1) pending_thread_in_wait_not_idle)
      apply (simp add:not_idle_thread_def obj_at_def is_ntfn_def)+
  done

lemma not_idle_after_reply_cancel_ipc:
  "\<lbrace>not_idle_thread obj_id' and invs :: det_state \<Rightarrow> bool \<rbrace> reply_cancel_ipc obj_id'
   \<lbrace>\<lambda>y. valid_idle\<rbrace>"
  apply (simp add:reply_cancel_ipc_def)
  apply wp
       apply (simp add:cap_delete_one_def unless_def)
       apply wp+
          apply (simp add:IpcCancel_A.empty_slot_def)
          apply (wp set_cap_idle select_wp | simp add: if_apply_def2 imp_conjR
            | strengthen imp_consequent[where P="invs s" for s] imp_consequent[where P="valid_idle s" for s])+
   apply (strengthen invs_valid_idle)
   apply (wp thread_set_invs_trivial | simp add: ran_tcb_cap_cases)+
  done

lemma not_idle_thread_cancel_signal:
  "\<lbrace>not_idle_thread obj_id' and valid_idle\<rbrace> cancel_signal obj_id' word \<lbrace>\<lambda>r. valid_idle\<rbrace>"
  including no_pre
  apply (simp add:cancel_signal_def)
  apply (wp valid_idle_set_thread_state|wpc)+
  apply (rule hoare_strengthen_post[OF get_simple_ko_sp])
  apply (clarsimp simp:not_idle_thread_def obj_at_def is_ntfn_def)
  done

lemma cancel_ipc_valid_idle:
  "\<lbrace>valid_idle and not_idle_thread obj_id' and invs :: det_state \<Rightarrow> bool\<rbrace> IpcCancel_A.cancel_ipc obj_id' \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  apply (clarsimp simp: cancel_ipc_def)
  apply (wp not_idle_after_blocked_cancel_ipc not_idle_after_reply_cancel_ipc
            not_idle_thread_cancel_signal | wpc | simp)+
   apply (rule hoare_strengthen_post[where Q="\<lambda>r. st_tcb_at ((=) r) obj_id'
                                                  and not_idle_thread obj_id' and invs"])
    apply (wp gts_sp)
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def not_idle_thread_def | rule conjI)+
  done

lemma send_signal_corres:
  notes if_split [split del]
  shows
  "ep_id = epptr \<Longrightarrow> dcorres dc \<top> (invs and valid_etcbs)
     (Endpoint_D.send_signal ep_id)
     (Ipc_A.send_signal epptr badge)"
  apply (unfold Endpoint_D.send_signal_def Ipc_A.send_signal_def invs_def)
  apply (rule dcorres_expand_pfx)
  apply (clarsimp simp:get_simple_ko_def get_object_def gets_def bind_assoc split: if_split)
  apply (rule dcorres_absorb_get_r)
  apply (clarsimp simp:assert_def corres_free_fail partial_inv_def a_type_def the_equality
                 split:Structures_A.kernel_object.splits if_split)
  apply (rule conjI, clarsimp+)
  apply (rename_tac ntfn_ext)
  apply (case_tac "ntfn_obj ntfn_ext", clarsimp)
    apply (case_tac "ntfn_bound_tcb ntfn_ext", clarsimp)
     \<comment> \<open>Idle, not bound\<close>
     apply (rule corres_alternate1)
     apply (rule dcorres_absorb_get_l)
     apply (clarsimp)
     apply (frule valid_objs_valid_ntfn_simp[rotated])
      apply (simp add:valid_state_def valid_pspace_def)
     apply (simp add:gets_def bind_assoc option_select_def)
     apply (frule get_notification_pick,simp)
     apply (clarsimp simp:ntfn_waiting_set_lift valid_state_def valid_ntfn_abstract_def none_is_waiting_ntfn_def)
     apply (rule corres_guard_imp,rule corres_dummy_set_notification,simp+)[1]
    \<comment> \<open>Idle, bound\<close>
    apply (clarsimp simp: get_thread_state_def thread_get_def gets_the_def gets_def bind_assoc)
    apply (rule dcorres_absorb_get_r)
    apply (clarsimp simp: assert_opt_def corres_free_fail split: Structures_A.kernel_object.splits option.splits)
    apply (case_tac "receive_blocked (tcb_state x2)")
     \<comment> \<open>receive_blocked\<close>
     apply (clarsimp)
     apply (rule corres_alternate2)
     apply (clarsimp simp: send_signal_bound_def gets_def)
     apply (rule dcorres_absorb_get_l)
     apply (clarsimp simp: receive_blocked_waiting_syncs)
     apply (clarsimp simp: IpcCancel_A.cancel_ipc_def get_thread_state_def thread_get_def gets_the_def gets_def bind_assoc)
     apply (rule dcorres_absorb_get_r)
     apply (clarsimp simp: assert_opt_def corres_free_fail split: Structures_A.kernel_object.splits option.splits)
     apply (simp add: receive_blocked_def)
     apply (case_tac "tcb_state x2";clarsimp)
     apply (rule corres_guard_imp)
       apply (simp add: blocked_cancel_ipc_def bind_assoc)
       apply (rule corres_symb_exec_r)
          apply (rule corres_symb_exec_r)
             apply (rule corres_symb_exec_r)
                apply (rule corres_dummy_return_pl)
                apply (rule corres_split[OF corres_dummy_set_sync_ep])
                  apply (simp add: when_def dc_def[symmetric])
                  apply (rule corres_split[OF set_thread_state_corres dcorres_dat])
                   apply (wp cancel_ipc_valid_idle
                        | simp add: not_idle_thread_def invs_def valid_state_def get_blocking_object_def)+
     apply (clarsimp dest!:get_tcb_rev simp:invs_def ep_at_def2[symmetric, simplified])
     apply (frule valid_tcb_if_valid_state[rotated], clarsimp simp: valid_state_def)
     apply (fastforce dest!: get_tcb_SomeD
                       simp: receive_blocked_def valid_idle_def pred_tcb_at_def obj_at_def
                             valid_tcb_def valid_tcb_state_def infer_tcb_pending_op_def
                      split: Structures_A.thread_state.splits)
    apply clarsimp
    apply (rule corres_alternate1)
    apply (rule dcorres_absorb_get_l)
    apply (clarsimp)
    apply (frule valid_objs_valid_ntfn_simp[rotated])
     apply (simp add:valid_state_def valid_pspace_def)
    apply (simp add:gets_def bind_assoc option_select_def)
    apply (frule get_notification_pick,simp)
    apply (clarsimp simp:ntfn_waiting_set_lift valid_state_def valid_ntfn_abstract_def none_is_waiting_ntfn_def)
    apply (rule corres_guard_imp,rule corres_dummy_set_notification,simp+)[1]
   \<comment> \<open>Waiting\<close>
   apply (rule corres_alternate1)
   apply (rule dcorres_absorb_get_l)
   apply (clarsimp)
   apply (frule valid_objs_valid_ntfn_simp[rotated])
    apply (simp add:valid_state_def valid_pspace_def)
   apply (simp add:gets_def bind_assoc option_select_def)
   apply (frule get_notification_pick,simp)
   apply (clarsimp simp:ntfn_waiting_set_lift valid_state_def valid_ntfn_abstract_def split: if_split)
   apply (rule conjI)
    apply (clarsimp simp: dest!:not_empty_list_not_empty_set)
   apply (clarsimp simp:neq_Nil_conv)
   apply (rule corres_guard_imp)
     apply (rule select_pick_corres)
     apply (rule corres_update_waiting_ntfn_do_notification_transfer)
    apply (drule_tac s = "insert y (set ys)" in sym)
    apply (clarsimp simp: image_def)
   apply (drule_tac s = "insert y (set ys)" in sym)
   apply (drule_tac A="ntfn_waiting_set epptr s'" and x = y in eqset_imp_iff)
   apply (clarsimp simp:valid_pspace_def ntfn_waiting_set_def)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def valid_ntfn_def split:list.splits option.splits)
  \<comment> \<open>Active\<close>
  apply (rule corres_alternate1)
  apply (rule dcorres_absorb_get_l)
  apply (clarsimp)
  apply (frule valid_objs_valid_ntfn_simp[rotated])
   apply (simp add:valid_state_def valid_pspace_def)
  apply (clarsimp simp:gets_def bind_assoc option_select_def)
  apply (frule get_notification_pick,simp)
  apply (clarsimp simp:ntfn_waiting_set_lift valid_state_def valid_ntfn_abstract_def none_is_waiting_ntfn_def)
  apply (rule corres_guard_imp,rule corres_dummy_set_notification,simp+)
  done

lemma set_thread_state_block_on_send_corres:
    "dcorres dc \<top>
     (not_idle_thread thread and valid_etcbs)
     (block_thread_on_ipc thread
       (PendingSyncSendCap epptr badge call can_grant can_grant_reply False))
     (set_thread_state thread
       (Structures_A.thread_state.BlockedOnSend epptr
         \<lparr>sender_badge = badge, sender_can_grant = can_grant,
          sender_can_grant_reply = can_grant_reply, sender_is_call = call\<rparr>))"
   by (simp add:block_thread_on_ipc_def,rule block_thread_on_send_corres)

lemma set_thread_state_block_on_receive_corres:
  "dcorres dc \<top> (not_idle_thread thread and valid_etcbs)
      (block_thread_on_ipc thread (PendingSyncRecvCap epptr False can_grant))
      (set_thread_state thread
        (Structures_A.thread_state.BlockedOnReceive epptr \<lparr>receiver_can_grant = can_grant\<rparr>))"
   apply (simp add:block_thread_on_ipc_def)
   apply (rule block_thread_on_recv_corres)
   done

lemma corres_setup_caller_cap:
  "sender \<noteq> receiver \<Longrightarrow> dcorres dc \<top>
  (valid_mdb and valid_idle and not_idle_thread sender and not_idle_thread receiver
   and tcb_at sender and tcb_at receiver
   and st_tcb_at (Not \<circ> halted) sender and valid_objs and valid_etcbs)
           (inject_reply_cap sender receiver can_grant)
           (setup_caller_cap sender receiver can_grant)"
  apply (rule dcorres_expand_pfx)
  apply (rule corres_guard_imp)
    apply (simp add: inject_reply_cap_def setup_caller_cap_def split del: if_split)
    apply (rule corres_split[OF set_thread_state_corres])
      apply (rule reply_cap_insert_corres)
      apply (simp add: not_idle_thread_def)+
    apply (wp set_thread_state_it|simp )+
    apply (rule hoare_vcg_conj_lift)
     apply (clarsimp simp: not_idle_thread_def set_thread_state_def)
     apply wp
      apply (simp add: set_object_def get_object_def)
      apply wp+
   apply simp
  apply (clarsimp simp: not_idle_thread_def tcb_at_def obj_at_def st_tcb_at_def)
  apply (rule conjI|clarsimp simp: is_tcb_def)+
  apply (drule valid_tcb_objs)
   apply (erule get_tcb_rev)
  apply (simp add: valid_tcb_state_def)
  done

lemma seq_alt_when:"(do a \<leftarrow> when c (f \<sqinter> g); h a od) = ((do a\<leftarrow>when c f ; h a od)\<sqinter> (do a\<leftarrow>when c g; h a od))"
  apply (clarsimp simp:when_def)
  apply (subst alternative_bind_distrib)+
  apply (clarsimp simp:alternative_def)
  done

lemma evalMonad_mapM:
  assumes as:"evalMonad (mapM f ls) s = Some v"
  assumes "\<And>l. empty_when_fail (f l)"
  assumes "\<And>P l. weak_det_spec P (f l)"
  assumes wp: "\<And>s l. \<lbrace>(=) s\<rbrace> f l \<lbrace>\<lambda>r. (=) s\<rbrace>"
  shows "v = (map (\<lambda>p. the (evalMonad (f p) s)) ls)"
  using as
  proof (induct ls arbitrary: v)
    case Nil
    thus ?case
      by (clarsimp simp:evalMonad_def mapM_def sequence_def return_def)
 next
    case (Cons l ls)
    show ?case
    using Cons.prems
    apply clarsimp
    apply (clarsimp simp:mapM_Cons)
    apply (subst (asm) evalMonad_compose)
       apply (simp add: Cons assms)+
    apply (clarsimp split:option.splits)
    apply (subst (asm) evalMonad_compose)
       apply (rule empty_when_fail_mapM)
       apply (simp add: Cons assms)+
      apply (rule weak_det_spec_mapM)
      apply (simp add: Cons assms)+
     apply (wp mapM_wp)
       apply (simp add: Cons assms)+
      apply fastforce
     apply simp
    apply (clarsimp split:option.splits)
    apply (simp add: Cons)
    done
  qed

lemma evalMonad_get_extra_cptrs:
  "\<lbrakk>evalMonad (lookup_ipc_buffer False thread) s = Some (Some buf);get_tcb thread s = Some tcb;
    (evalMonad (Ipc_A.get_extra_cptrs (Some buf) (data_to_message_info (arch_tcb_context_get (tcb_arch tcb) msg_info_register))) s) = Some a
    \<rbrakk>
  \<Longrightarrow> a = (map (to_bl) (cdl_intent_extras $ transform_full_intent (machine_state s) thread tcb))"
  including no_pre
  apply (clarsimp simp:get_extra_cptrs_def)
  apply (clarsimp simp:liftM_def)
  apply (subst (asm) evalMonad_compose)
     apply (rule empty_when_fail_mapM)
     apply (simp add:weak_det_spec_load_word_offs empty_when_fail_load_word_offs)
    apply (rule weak_det_spec_mapM)
    apply (simp add:weak_det_spec_load_word_offs)
   apply (wp mapM_wp,fastforce)
  apply (clarsimp split:option.splits)
  apply (rule_tac x = x2 in arg_cong)
  apply (clarsimp simp:transform_full_intent_def Let_def)
  apply (clarsimp simp:get_ipc_buffer_words_def)
  apply (drule lookup_ipc_buffer_SomeB_evalMonad)
  apply (clarsimp simp:cte_wp_at_cases obj_at_def dest!: get_tcb_SomeD)
  apply (drule sym[where t = "tcb_ipcframe tcb"])
  apply clarsimp
  apply (simp add:mapM_load_word_offs_do_machine_op)
  apply (subst (asm) evalMonad_do_machine_op[symmetric])
    apply (rule weak_det_spec_mapM[OF weak_det_spec_loadWord])
   apply (rule empty_when_fail_mapM)
   apply (clarsimp simp:empty_when_fail_loadWord weak_det_spec_loadWord)
  apply (clarsimp simp:get_tcb_message_info_def)
  done

lemma dcorres_symb_exec_r_evalMonad:
  assumes wp:"\<And>sa. \<lbrace>(=) sa\<rbrace> f \<lbrace>\<lambda>r. (=) sa\<rbrace>"
  assumes corres:"\<And>rv. evalMonad f s = Some rv \<Longrightarrow> dcorres r P ((=) s) h (g rv)"
  shows "\<lbrakk> empty_when_fail f; weak_det_spec ((=) s) f \<rbrakk> \<Longrightarrow> dcorres r P ((=) s) h (f>>=g)"
  apply (rule_tac Q'="\<lambda>r. (=) s and K_bind (evalMonad f s = Some r)" in corres_symb_exec_r)
     apply (rule dcorres_expand_pfx)
     using corres
     apply (clarsimp simp:corres_underlying_def)
    apply (wp wp, simp, rule evalMonad_wp)
      apply (simp add:wp)+
  done

lemma dcorres_store_word_offs_spec:
  "\<lbrakk>within_page buf (base + of_nat (x * word_size)) sz\<rbrakk> \<Longrightarrow>
  dcorres dc (\<lambda>_. True) (pspace_aligned and pspace_distinct and valid_objs and ipc_frame_sz_at sz s_id and ipc_frame_ptr_at buf s_id and valid_etcbs)
   (corrupt_frame buf) (store_word_offs base x y)"
  using zip_store_word_corres[where xs = "[x]" and base = base and buf = buf and sz = sz and s_id = s_id and ys = "[y]"]
  apply (clarsimp simp:zipWithM_x_One)
done

lemma dcorres_set_extra_badge:
  "rcv = thread \<Longrightarrow> dcorres dc \<top>
           (valid_idle and valid_objs and pspace_aligned and pspace_distinct and not_idle_thread thread and
            (\<lambda>s. evalMonad (lookup_ipc_buffer in_receive thread) s = Some (Some rcv_buffer) \<and>
                 2 + msg_max_length + n < max_ipc_length) and valid_etcbs)
           (corrupt_ipc_buffer rcv in_receive)
           (set_extra_badge rcv_buffer w n)"
  supply if_cong[cong]
  apply (clarsimp simp:set_extra_badge_def corrupt_ipc_buffer_def)
  apply (rule dcorres_expand_pfx)
  apply clarsimp
  apply (frule lookup_ipc_buffer_SomeB_evalMonad)
  apply clarsimp
  apply (rule corres_guard_imp)
    apply (rule corres_symb_exec_l)
       apply (rule_tac F = "rv = Some b" in corres_gen_asm)
       apply (clarsimp)
       apply (rule dcorres_store_word_offs_spec)
       apply (drule_tac x = "buffer_cptr_index + n" and sz = sz in within_page_ipc_buf)
             apply (simp)+
           apply (simp add:obj_at_def cte_wp_at_cases)
           apply (drule_tac t = "tcb_ipcframe obj" in sym)
           apply (fastforce simp:ipc_frame_wp_at_def obj_at_def)
          apply (simp add:obj_at_def cte_wp_at_cases)
          apply (drule_tac t = "tcb_ipcframe obj" in sym)
          apply (fastforce simp:ipc_frame_wp_at_def obj_at_def)
         apply (simp add:ipc_buffer_wp_at_def obj_at_def)
        apply (clarsimp simp: msg_max_length_def max_ipc_length_unfold buffer_cptr_index_def
                              msg_align_bits)
       apply (simp)
      apply (clarsimp simp:get_ipc_buffer_def gets_the_def exs_valid_def gets_def
                           get_def bind_def return_def assert_opt_def fail_def
                      split:option.splits | rule conjI)+
       apply (subgoal_tac "s = transform s'")
        prefer 2
        apply simp+
       apply (rule exI)
       apply (clarsimp simp: obj_at_def, frule(1) valid_etcbs_tcb_etcb)
       apply (subst opt_cap_tcb)
          apply (rule get_tcb_rev, simp)
         apply (clarsimp simp: get_etcb_def)
        apply (simp add:obj_at_def not_idle_thread_def)+
      apply (simp split:cdl_cap.splits)
     apply (wp cdl_get_ipc_buffer_Some)
           apply (drule lookup_ipc_buffer_SomeB_evalMonad)
           apply (fastforce simp:cte_wp_at_def)
          apply (clarsimp simp:tcb_at_def get_tcb_SomeD obj_at_def not_idle_thread_def)+
  apply (clarsimp simp:cte_wp_at_cases obj_at_def)
  apply (drule_tac t = "tcb_ipcframe obj" in sym)
  apply (fastforce simp:ipc_frame_wp_at_def obj_at_def)
  done

definition
  "dest_of xs \<equiv> case xs of [] \<Rightarrow> None | [r] \<Rightarrow> Some (transform_cslot_ptr r)"

lemma update_cap_rights_cong:
  "\<lbrakk> is_ep_cap cap \<or> is_ntfn_cap cap \<or> is_reply_cap cap \<or> is_arch_page_cap cap \<Longrightarrow> R = R' \<rbrakk> \<Longrightarrow>
  transform_cap (cap_rights_update R' cap) = update_cap_rights R (transform_cap cap)"
  by (clarsimp simp: is_reply_cap_def
                     cap_rights_update_def acap_rights_update_def update_cap_rights_def
               split: cap.splits arch_cap.splits)

lemma transform_cap_rights:
  "is_ep_cap cap \<or> is_ntfn_cap cap \<or> is_reply_cap cap \<or> is_arch_page_cap cap
  \<Longrightarrow> (Structures_A.cap_rights cap) = Types_D.cap_rights (transform_cap cap)"
  by (auto simp: is_cap_simps is_arch_page_cap_def Types_D.cap_rights_def transform_cap_def
           split: arch_cap.splits cap.splits)

definition
  "ipc_buffer rcv rcv_buffer \<equiv> \<lambda>s.
     \<exists>sz. not_idle_thread rcv s \<and> ipc_frame_ptr_at rcv_buffer rcv s \<and>
               ipc_frame_sz_at sz rcv s"

lemma evalMonad_thread_get_eq:
  "evalMonad (thread_get f x) b = (case (get_tcb x b) of None \<Rightarrow> None | Some t \<Rightarrow> Some (f t))"
  apply (simp add:thread_get_def)
  apply (subst evalMonad_compose)
     apply (simp add:empty_when_fail_simps weak_det_spec_simps)+
   apply wp
   apply clarsimp
  apply (clarsimp simp:gets_the_def gets_def get_def bind_def return_def assert_opt_def)
  apply (case_tac "get_tcb x b")
   apply (clarsimp simp:return_def fail_def evalMonad_def split:option.splits)+
  done

lemma evalMonad_lookup_ipc_buffer_wp:
assumes cte_wp:"\<And>P slot. (\<And>c. P c \<Longrightarrow> \<not> is_untyped_cap c)
  \<Longrightarrow> \<lbrace>cte_wp_at (P and (\<noteq>) cap.NullCap) slot\<rbrace> f \<lbrace>\<lambda>r. cte_wp_at P slot\<rbrace>"
assumes tcb_wp:"\<And>buf t. \<lbrace>ipc_buffer_wp_at buf t\<rbrace> f \<lbrace>\<lambda>r. ipc_buffer_wp_at buf t \<rbrace>"
shows "\<lbrace>\<lambda>s. evalMonad (lookup_ipc_buffer in_receive x) s = Some (Some buf)\<rbrace> f \<lbrace>\<lambda>rv s. evalMonad (lookup_ipc_buffer in_receive x) s = Some (Some buf)\<rbrace>"
  apply (simp add:valid_def lookup_ipc_buffer_def)
  apply (subst evalMonad_compose)
     apply (simp add:empty_when_fail_thread_get weak_det_spec_thread_get)+
   apply wp
  apply (clarsimp split:option.split_asm simp:evalMonad_thread_get_eq)
  apply (frule use_valid[OF _ tcb_wp])
   apply (clarsimp dest!:get_tcb_SomeD simp:ipc_buffer_wp_at_def obj_at_def)
   apply (fastforce)
  apply (clarsimp simp:ipc_buffer_wp_at_def obj_at_def dest!:get_tcb_rev)
  apply (subst evalMonad_compose)
     apply (simp add:empty_when_fail_thread_get weak_det_spec_thread_get)+
   apply wp
  apply (subst (asm) evalMonad_compose)
     apply (simp add:empty_when_fail_get_cap weak_det_spec_get_cap)+
   apply wp
  apply (clarsimp simp:evalMonad_get_cap split:option.split_asm cap.split_asm)
  apply (drule caps_of_state_cteD)
  apply (rename_tac arch_cap)
  apply (frule_tac P1 = "(=) (cap.ArchObjectCap arch_cap)" in use_valid[OF _ cte_wp])
    apply (clarsimp simp:is_cap_simps)
   apply (erule cte_wp_at_weakenE)
   apply clarsimp
  apply (clarsimp simp:cte_wp_at_caps_of_state evalMonad_thread_get_eq)
  apply (subst evalMonad_compose)
     apply (simp add:empty_when_fail_get_cap weak_det_spec_get_cap)+
   apply wp
  apply (simp add:evalMonad_get_cap)
  apply (case_tac arch_cap)
      apply simp_all
  apply (clarsimp simp:evalMonad_def return_def split:if_splits)
  done

crunch ipc_buffer_wp_at[wp]: update_cdt "ipc_buffer_wp_at buf t"
  (wp: crunch_wps simp: crunch_simps Retype_A.detype_def set_cdt_def ipc_buffer_wp_at_def ignore:clearMemory)

lemma ipc_buffer_wp_at_exst_update[simp]:
  "ipc_buffer_wp_at buf t (exst_update f s) =
   ipc_buffer_wp_at buf t s"
  by (simp add: ipc_buffer_wp_at_def obj_at_def)

lemma ipc_buffer_wp_set_cap[wp]:
  "\<lbrace>ipc_buffer_wp_at buf t\<rbrace> CSpaceAcc_A.set_cap cap' a \<lbrace>\<lambda>ya. ipc_buffer_wp_at buf t\<rbrace>"
  apply (clarsimp simp: set_cap_def split_def)
  apply (wpsimp wp: set_object_wp get_object_wp)
  apply (rule conjI|clarsimp simp:ipc_buffer_wp_at_def obj_at_def)+
  done

lemma ipc_buffer_wp_at_cap_insert_ext[wp]:
  "\<lbrace>ipc_buffer_wp_at buf t \<rbrace> cap_insert_ext src_parent src_slot dest_slot src_p dest_p \<lbrace>\<lambda>r. ipc_buffer_wp_at buf t\<rbrace>"
  apply (simp only:ipc_buffer_wp_at_def)
  by wp

lemma ipc_buffer_wp_at_cap_insert[wp]:
  "\<lbrace>ipc_buffer_wp_at buf t :: det_state \<Rightarrow> bool \<rbrace> cap_insert cap' (slot_ptr, slot_idx) a \<lbrace>\<lambda>r. ipc_buffer_wp_at buf t\<rbrace>"
  apply (simp add:cap_insert_def set_untyped_cap_as_full_def)
  apply (wp|simp split del:if_split)+
           apply (rule_tac Q = "\<lambda>r. ipc_buffer_wp_at buf t" in hoare_strengthen_post)
            apply wp
           apply (clarsimp simp:ipc_buffer_wp_at_def)
          apply (wp get_cap_inv hoare_drop_imp)+
  apply simp
  done

lemma cap_insert_weak_cte_wp_at_not_null:
assumes "\<And>c. P c \<Longrightarrow> \<not> is_untyped_cap c"
shows "\<lbrace>cte_wp_at (P and (\<noteq>) cap.NullCap) slot :: det_state \<Rightarrow> bool\<rbrace> cap_insert cap' src dest
  \<lbrace>\<lambda>r. cte_wp_at P slot\<rbrace>"
  apply (case_tac "slot = dest")
   apply (clarsimp simp:cap_insert_def)
   apply wp
       apply (rule hoare_pre_cont)
      apply (rule hoare_pre_cont)
     apply (wp get_cap_wp)+
    apply (clarsimp simp:cte_wp_at_caps_of_state)
  apply (wp cap_insert_weak_cte_wp_at2)
   apply (clarsimp simp:assms)
  apply (clarsimp simp:cte_wp_at_caps_of_state)
  done

lemma cap_insert_cte_wp_at_masked_as_full:
  assumes "\<And>c. P c \<Longrightarrow> P (masked_as_full c cap)"
  shows "\<lbrace>\<lambda>s. if slot = dest then P cap else cte_wp_at P slot s\<rbrace>
   cap_insert cap src dest \<lbrace>\<lambda>uu. cte_wp_at P slot\<rbrace>"
  apply (simp add:cap_insert_def set_untyped_cap_as_full_def)
  apply (wp set_cap_cte_wp_at hoare_vcg_if_lift get_cap_wp static_imp_wp dxo_wp_weak
       | simp split del:if_split)+
  apply (intro conjI impI allI |
    clarsimp simp:cte_wp_at_caps_of_state)+
     apply (drule assms)
     apply (clarsimp simp:masked_as_full_def)
    apply (clarsimp simp:cte_wp_at_caps_of_state)
   apply (clarsimp simp:cte_wp_at_caps_of_state)+
  done

lemma is_ep_cap_transform_simp[simp]:
  "Types_D.is_ep_cap (transform_cap cap) = is_ep_cap cap"
  by (simp add:transform_cap_def cap_type_simps
    split:cap.splits arch_cap.splits)

lemma dcorres_transfer_caps_loop:
  "\<lbrakk> dest = dest_of dests;
     caps = map (\<lambda>(cap, slot). (transform_cap cap, transform_cslot_ptr slot)) caps';
     ep = ep' \<rbrakk> \<Longrightarrow>
   dcorres (\<lambda>_ _. True) \<top>
            (valid_idle and valid_objs and pspace_aligned and pspace_distinct and
            valid_mdb and (\<lambda>s. evalMonad (lookup_ipc_buffer True rcv) s = Some (Some rcv_buffer)) and
            not_idle_thread rcv and
            (\<lambda>s. (\<forall>x \<in> set dests. cte_wp_at (\<lambda>cap. cap = cap.NullCap) x s \<and>
                                 real_cte_at x s) \<and>
                 (\<forall>(cap, slot) \<in> set caps'. real_cte_at slot s \<and> valid_cap cap s \<and>
                       cte_wp_at (\<lambda>cp'. (cap \<noteq> cap.NullCap \<longrightarrow> cp'\<noteq>cap \<longrightarrow> cp' = masked_as_full cap cap )) slot s
                 )\<and>
            length dests \<le> 1 \<and>
            2 + msg_max_length + n + length caps' < max_ipc_length) and valid_etcbs)
           (Endpoint_D.transfer_caps_loop ep rcv caps dest)
           (Ipc_A.transfer_caps_loop ep' rcv_buffer n caps' dests mi)"
proof (induct caps' arbitrary: mi n dests dest caps ep ep')
  case Nil thus ?case by clarsimp
next
  case (Cons p caps' mi n dests)
  from Cons.prems
  show ?case
  apply (cases p)
  apply (rename_tac cap slot_ptr slot_idx)
  apply (clarsimp simp: const_on_failure_def split del: if_split)
  apply (case_tac "is_ep_cap cap \<and> ep' = Some (obj_ref_of cap)")
   apply (subgoal_tac "Types_D.is_ep_cap (transform_cap cap) \<and>
                       (\<exists>z. ep' = Some z \<and> z = cap_object (transform_cap cap))")
    prefer 2
    apply (clarsimp simp: is_cap_simps cap_type_simps)
   apply (simp add: catch_liftE_bindE catch_liftE)
   apply (rule corres_guard_imp)
     apply (rule corres_split[where r'=dc])
        apply (rule dcorres_set_extra_badge,simp)
       apply (rule Cons.hyps, rule refl, rule refl, simp)
      apply wp[1]
     apply (simp add: store_word_offs_def set_extra_badge_def
     not_idle_thread_def ipc_frame_wp_at_def
     split_def)
     apply (wp evalMonad_lookup_ipc_buffer_wp)
         apply (erule cte_wp_at_weakenE)
         apply (simp add:ipc_buffer_wp_at_def)+
        apply wp
       apply ((wp hoare_vcg_ex_lift valid_irq_node_typ hoare_vcg_ball_lift)+)[3]
    apply simp
   subgoal by (fastforce simp: not_idle_thread_def ipc_frame_wp_at_def ipc_buffer_def)
  apply (subgoal_tac "\<not>(Types_D.is_ep_cap (transform_cap cap) \<and>
                       (\<exists>z. ep' = Some z \<and> z = cap_object (transform_cap cap)))")
   prefer 2
   apply (clarsimp simp: is_cap_simps cap_type_simps split: cdl_cap.splits)
  apply (simp del: de_Morgan_conj split del: if_split)
  apply (case_tac dests)
   apply (simp add: dest_of_def returnOk_liftE catch_liftE)
  apply (case_tac list)
   prefer 2
   apply simp
  apply (simp (no_asm_simp) add: dest_of_def split del: if_split)
  apply (subst bindE_assoc [symmetric])
  apply (rule corres_guard_imp)
    apply (rule corres_split_catch [where f=dc and E="\<top>\<top>" and E'="\<top>\<top>"]; simp)
      apply (rule corres_splitEE)
         apply (subst alternative_bindE_distrib)
          apply simp
          apply (rule corres_alternate2)
          apply (rule derive_cap_dcorres [where P="\<top>"], simp)
        apply (rule corres_splitEE)
           apply (rule corres_whenE, simp)
            apply (rule dcorres_throw)
           apply (rule TrueI)
          apply (simp add: liftE_bindE)
          apply (rule corres_split)
             apply (rule dcorres_insert_cap_combine [folded alternative_com])
             apply simp
            apply simp
            apply (rule Cons.hyps)
              apply (simp add: dest_of_def)
             apply (rule refl)
            apply (rule refl)
           apply wp[1]
          apply (simp add: split_def not_idle_thread_def)
          apply (wp evalMonad_lookup_ipc_buffer_wp )
            apply (rule hoare_pre)
             apply (rule cap_insert_weak_cte_wp_at_not_null)
             apply clarsimp+
           apply (wp cap_insert_idle valid_irq_node_typ hoare_vcg_ball_lift cap_insert_cte_wp_at)+
       apply (simp add: if_apply_def2)
       apply wp
      apply (simp add: if_apply_def2)
      apply (rule validE_R_validE)
      apply (simp add:conj_comms ball_conj_distrib split del:if_split)
      apply (rule_tac Q' ="\<lambda>cap' s. (cap'\<noteq> cap.NullCap \<longrightarrow>(
       (cte_wp_at (is_derived (cdt s) (slot_ptr, slot_idx) cap') (slot_ptr, slot_idx) s)
       \<and> pspace_aligned s \<and> pspace_distinct s \<and> valid_objs s \<and> valid_idle s
       \<and> valid_mdb s \<and> QM s cap'))" for QM
       in hoare_post_imp_R)
       prefer 2
       apply (subgoal_tac "r\<noteq> cap.NullCap \<longrightarrow> cte_wp_at ((\<noteq>) cap.NullCap) (slot_ptr, slot_idx) s")
        apply (intro impI)
        apply simp
        apply (elim conjE)
        apply (erule conjE)
        apply simp
       apply (clarsimp simp:cte_wp_at_caps_of_state)
      apply (subst imp_conjR)
      apply (rule hoare_vcg_conj_liftE_R)
       apply (rule derive_cap_is_derived)
      apply (rule derive_cap_is_derived_foo)
     apply wp+
   apply (simp split del: if_split)
  apply (clarsimp split del: if_split cong: conj_cong)
  apply (rule conjI)
   apply (clarsimp simp: valid_mdb_def mdb_cte_at_def cte_wp_at_caps_of_state)
   apply fast
  apply (rule conjI)
   apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (rule conjI)
   apply (clarsimp simp: cte_wp_at_caps_of_state)
   apply (case_tac "cap = capa")
    apply (clarsimp simp:cap_master_cap_simps remove_rights_def)+
   apply (clarsimp simp:masked_as_full_def is_cap_simps cap_master_cap_def)
  apply (clarsimp split del: if_split)
  apply (clarsimp simp: cte_wp_at_caps_of_state not_idle_thread_def)
  apply (rule conjI)
   apply (clarsimp simp: not_idle_thread_def valid_idle_def pred_tcb_at_def
                         obj_at_def is_cap_table_def)
  apply (rule conjI)
   apply (clarsimp simp: not_idle_thread_def valid_idle_def pred_tcb_at_def
                         obj_at_def is_cap_table_def)
  apply (rule conjI)
   apply (clarsimp simp: not_idle_thread_def valid_idle_def pred_tcb_at_def
                         obj_at_def is_cap_table_def)
  apply (rule conjI)
   apply (rule rev_mp[OF _ real_cte_tcb_valid])
   apply simp
  apply (rule context_conjI)
   apply (clarsimp split:if_split_asm simp:remove_rights_def)
  apply (intro conjI ballI)
     apply (drule(1) bspec,clarsimp)+
  apply (case_tac "capb = aa")
   apply (clarsimp simp:masked_as_full_def split:if_split_asm)
  by (clarsimp simp:masked_as_full_def free_index_update_def is_cap_simps)
qed

lemma load_cap_transfer_def':
  "load_cap_transfer (buf) = (do
    xs \<leftarrow> mapM (load_word_offs buf) [Suc (Suc (msg_max_length + msg_max_extra_caps))..<5 + (msg_max_length + msg_max_extra_caps)];
    return \<lparr>ct_receive_root = data_to_cptr (head xs), ct_receive_index = data_to_cptr ((head \<circ> tail) xs), ct_receive_depth = ((head\<circ> tail\<circ> tail) xs)\<rparr>
    od)"
  apply (clarsimp simp:load_cap_transfer_def )
  apply (clarsimp simp:captransfer_from_words_def)
  apply (simp add:msg_max_length_def msg_max_extra_caps_def cong: if_weak_cong)
  apply (clarsimp simp:load_word_offs_def mapM_def sequence_def bind_assoc)
  apply (simp add:word_size_def add.commute)
  done

lemma get_ipc_buffer_words_receive_slots:
  "\<lbrakk> tcb_ipcframe obj = cap.ArchObjectCap (arch_cap.PageCap False b rs sz mapdata); valid_cap (tcb_ipcframe obj) s;
    AllowRead \<in> rs;valid_ipc_buffer_cap (tcb_ipcframe obj) (tcb_ipc_buffer obj)\<rbrakk>
  \<Longrightarrow> \<exists>a b c. get_ipc_buffer_words (machine_state s) obj [Suc (Suc (msg_max_length + msg_max_extra_caps))..<5 + (msg_max_length + msg_max_extra_caps)] = [a,b,c]"
  apply (clarsimp simp:valid_ipc_buffer_cap_def get_ipc_buffer_words_def msg_max_length_def msg_max_extra_caps_def Let_def cong:if_weak_cong)
  apply (clarsimp simp:mapM_def sequence_def bind_assoc valid_cap_def cap_aligned_def)
  apply (drule_tac w = b and y = 2 in is_aligned_weaken)
    apply (case_tac sz,simp_all)
  apply (subst evalMonad_compose)
   apply (simp add:empty_when_fail_loadWord weak_det_spec_loadWord)+
   using loadWord_functional[unfolded functional_def,simplified]
     apply fastforce
  apply (simp add:evalMonad_loadWord word_size_def mask_add_aligned)
    apply (subst add.assoc)+
    apply (clarsimp simp: mask_add_aligned)
    apply (drule_tac n1 = "pageBitsForSize sz" and y = 2
      in is_aligned_weaken[OF is_aligned_after_mask])
       apply (case_tac sz,simp_all add:msg_align_bits)
       apply (simp add:mask_add_aligned)
         apply (simp add:word_mod_2p_is_mask[where n = 2,symmetric])
  apply (subst evalMonad_compose)
   apply (simp add:empty_when_fail_loadWord weak_det_spec_loadWord)+
   using loadWord_functional[unfolded functional_def,simplified]
     apply fastforce
  apply (simp add:evalMonad_loadWord word_size_def mask_add_aligned)
       apply (simp add:word_mod_2p_is_mask[where n = 2,symmetric])
  apply (subst evalMonad_compose)
   apply (simp add:empty_when_fail_loadWord weak_det_spec_loadWord)+
   using loadWord_functional[unfolded functional_def,simplified]
     apply fastforce
  apply (simp add:evalMonad_loadWord word_size_def mask_add_aligned)
  apply (simp add:word_mod_2p_is_mask[where n = 2,symmetric])
done

(* FIXME: MOVE *)
lemma dcorres_return:
  "r a b \<Longrightarrow> dcorres (r) (\<lambda>_. True) (\<lambda>_. True) (return a) (return b)"
  by (clarsimp simp:return_def corres_underlying_def)

lemma get_receive_slot_dcorres:
  "dcorres (\<lambda>d d'. d = dest_of d') \<top>
           ((\<lambda>s. evalMonad (lookup_ipc_buffer True t) s = Some buffer) and not_idle_thread t and valid_objs
             and valid_global_refs and valid_irq_node and valid_idle and not_idle_thread t and valid_etcbs)
           (get_receive_slot t)
           (get_receive_slots t (buffer))"
  apply (case_tac buffer)
   apply (simp add:get_receive_slot_def empty_on_failure_def)
   apply (rule dcorres_expand_pfx)
   apply (subst get_thread_def)
   apply (subst gets_the_def)
   apply (simp add:gets_def bind_assoc)
   apply (rule dcorres_absorb_get_l)
   apply (clarsimp simp:not_idle_thread_def)
   apply (frule lookup_ipc_buffer_None_evalMonad)
   apply (clarsimp simp: obj_at_def, frule(1) valid_etcbs_tcb_etcb)
   apply (fold get_etcb_def)
   apply (clarsimp simp:obj_at_def opt_object_tcb transform_tcb_def assert_opt_def
     dest!:get_tcb_rev get_etcb_rev)
   apply (simp add:tcb_slot_pending_ipc_neq[symmetric])
   apply (case_tac "tcb_ipcframe obj")
              apply (simp_all add:dest_of_def tcb_slot_defs)
   apply (rename_tac arch_cap)
   apply (case_tac "arch_cap")
       apply (simp_all add:dest_of_def)
   apply (clarsimp simp:transform_cap_def)
   apply (rename_tac word set vm opt)
   apply (drule_tac x = word in spec)
   apply (drule_tac x = "set" in spec)
   apply (clarsimp simp: cte_wp_at_cases dest!: get_tcb_SomeD spec)
   apply force
  apply (simp add:get_receive_slot_def empty_on_failure_def)
  apply (rule dcorres_expand_pfx)
  apply (subst get_thread_def)
  apply (subst gets_the_def)
  apply (simp add:gets_def bind_assoc)
  apply (rule dcorres_absorb_get_l)
  apply (clarsimp simp:not_idle_thread_def)
  apply (frule lookup_ipc_buffer_SomeB_evalMonad)
  apply (clarsimp simp: obj_at_def, frule(1) valid_etcbs_tcb_etcb)
  apply (fold get_etcb_def)
  apply (clarsimp simp:obj_at_def opt_object_tcb transform_tcb_def assert_opt_def
      dest!:get_tcb_rev get_etcb_rev)
  apply (simp add:tcb_slot_pending_ipc_neq[symmetric])
  apply (clarsimp simp:cte_wp_at_cases dest!:get_tcb_SomeD)
  apply (drule_tac t ="tcb_ipcframe obj" in sym)
  apply (clarsimp simp:transform_full_intent_def Let_def bind_assoc)
  apply (simp add:load_cap_transfer_def' tcb_slots)
  apply (rule_tac Q' = "\<lambda>r s. r = get_ipc_buffer_words (machine_state s'a) obj
               [Suc (Suc (msg_max_length + msg_max_extra_caps))..<5 + (msg_max_length + msg_max_extra_caps)]
    \<and> s = s'a" in corres_symb_exec_r)
     prefer 2
     apply (wp get_ipc_buffer_words)+
      apply (wp mapM_wp)+
      apply fastforce
     apply (clarsimp,intro conjI,(simp add:obj_at_def)+)
    apply (rule dcorres_expand_pfx)
    apply clarsimp
    apply (frule get_tcb_rev,frule valid_tcb_objs,simp)
    apply (clarsimp simp: valid_tcb_def tcb_cap_cases_def is_nondevice_page_cap_simps
                          is_nondevice_page_cap_arch_def
                   split: bool.split_asm)
    apply (drule get_ipc_buffer_words_receive_slots)
       apply (clarsimp dest!:get_tcb_rev,drule valid_tcb_objs,simp)
       apply (clarsimp simp:valid_tcb_def tcb_cap_cases_def)
       apply simp+
     apply (clarsimp dest!:get_tcb_rev,drule valid_tcb_objs,simp)
     apply (clarsimp simp:valid_tcb_def tcb_cap_cases_def)
    apply (clarsimp simp:)
    apply (rule corres_guard_imp[OF corres_split_catch[where f = dc]])
         apply (rule corres_splitEE[where r'="\<lambda>cnode cnode'. cnode = transform_cap cnode'"])
            apply (clarsimp simp:handleE'_def Monads_D.unify_failure_def Exceptions_A.unify_failure_def)
            apply (rule corres_split_bind_case_sum [OF lookup_cap_corres])
                 apply (clarsimp simp: word_size word_bits_def)+
             apply (rule hoareE_TrueI)+
           apply (rule corres_splitEE[where r'="\<lambda>p p'. p = transform_cslot_ptr p'"])
              apply (clarsimp simp:handleE'_def Monads_D.unify_failure_def Exceptions_A.unify_failure_def)
              apply (rule corres_split_bind_case_sum [OF lookup_slot_for_cnode_op_corres])
                     apply (clarsimp simp: word_size)+
               apply (rule hoareE_TrueI[where P=\<top>])+
             apply (simp add:liftE_bindE)
             apply (rule corres_split)
                apply (rule get_cap_corres; simp)
               apply (rule corres_splitEE)
                  apply (rule corres_whenE; simp)
                 apply (rule dcorres_returnOk)
                 apply clarsimp+
                apply (wp|clarsimp)+
            apply (rule hoare_post_imp_R[OF hoare_True_E_R])
            apply (intro impI, simp)
           apply (wp lsfco_not_idle)
          apply clarsimp
          apply (rule hoare_post_impErr[OF hoareE_TrueI TrueI])
          apply simp
         apply (wp lsfco_not_idle | clarsimp)+
     apply (rule conjI; rule TrueI)
    apply (clarsimp simp:not_idle_thread_def)
    apply fastforce
   apply (wp mapM_wp)
    apply fastforce+
  done

lemma dcorres_dummy_corrupt_ipc_buffer:
  "dcorres dc (\<top>) (tcb_at y and valid_idle and not_idle_thread y and valid_etcbs) (corrupt_ipc_buffer y b) (return x)"
  apply (clarsimp simp:corrupt_ipc_buffer_def get_ipc_buffer_def)
  apply (rule dcorres_expand_pfx)
    apply (clarsimp simp:gets_the_def gets_def bind_assoc)
    apply (rule dcorres_absorb_get_l)
    apply (clarsimp simp:tcb_at_def)
    apply (frule(1) valid_etcbs_get_tcb_get_etcb)
    apply (subst opt_cap_tcb)
      apply (simp add:not_idle_thread_def assert_opt_def)+
    apply (case_tac "tcb_ipcframe tcb")
      apply simp_all
      apply (rule corres_guard_imp[OF dummy_corrupt_tcb_intent_corres]
        ,(clarsimp simp:not_idle_thread_def tcb_at_def)+)+
    apply (rename_tac arch_cap etcb)
    apply (case_tac "arch_cap")
      apply simp_all
      apply (rule corres_guard_imp[OF dummy_corrupt_tcb_intent_corres]
        ,(clarsimp simp:not_idle_thread_def tcb_at_def)+)+
    apply (clarsimp simp: | rule conjI)+
      apply (rule corres_guard_imp[OF dcorres_dummy_corrupt_frame],clarsimp+)
    apply (clarsimp | rule conjI)+
      apply (rule corres_guard_imp[OF dcorres_dummy_corrupt_frame],clarsimp+)
  apply (rule corres_guard_imp[OF dummy_corrupt_tcb_intent_corres]
    ,(clarsimp simp:not_idle_thread_def tcb_at_def)+)+
done

lemma transfer_caps_loop_None:
  "dcorres dc \<top>
           (tcb_at rcv and valid_idle and not_idle_thread rcv and valid_etcbs)
           (Endpoint_D.transfer_caps_loop ep rcv caps None)
           (return x)"
  apply (induct caps arbitrary: x)
   apply simp
  apply clarsimp
  apply (rule corres_dummy_return_r)
  apply (rule corres_guard_imp)
    apply (rule corres_split[where r'=dc])
       apply (rule dcorres_dummy_corrupt_ipc_buffer)
      apply assumption
     apply wp+
   apply simp
  apply simp
  done

lemma get_rs_length [wp]:
  "\<lbrace>\<top>\<rbrace> get_receive_slots rcv buffer \<lbrace>\<lambda>slots s. length slots \<le> 1\<rbrace>"
  apply (cases buffer)
   apply (simp del: hoare_True_E_R|wp)+
  done

lemma transfer_caps_dcorres:
  "dcorres dc \<top>
           (tcb_at rcv and valid_idle and not_idle_thread rcv and valid_global_refs and valid_irq_node
            and valid_objs and pspace_aligned
            and pspace_distinct and valid_mdb
            and (\<lambda>s. evalMonad (lookup_ipc_buffer True rcv) s = Some rcv_buffer \<and>
             (\<forall>x\<in>set caps. (\<lambda>(cap, slot).  real_cte_at slot s \<and> valid_cap cap s \<and>
                 cte_wp_at (\<lambda>cp'. (cap \<noteq> cap.NullCap \<longrightarrow> cp'\<noteq>cap \<longrightarrow> cp' = masked_as_full cap cap )) slot s) x)
                 \<and> 2 + msg_max_length + length caps < max_ipc_length) and valid_etcbs)
           (Endpoint_D.transfer_caps ep
              (map (\<lambda>(cap, slot). (transform_cap cap, transform_cslot_ptr slot)) caps)
              sender rcv)
           (Ipc_A.transfer_caps info caps ep rcv rcv_buffer)"
  unfolding Ipc_A.transfer_caps_def Endpoint_D.transfer_caps_def
  apply clarsimp
  apply (cases rcv_buffer)
   apply simp
   apply (rule corres_dummy_return_r)
   apply (rule corres_guard_imp)
     apply (rule corres_split[where r'="\<lambda>r r'. r = None" and P=\<top> and P'=\<top>])
        apply (rule corres_alternate2)
        apply simp
       apply simp
       apply (rule transfer_caps_loop_None)
      apply wp+
    apply simp
   apply simp
  apply (simp del: get_receive_slots.simps)
  apply (rule corres_guard_imp)
    apply (rule corres_split)
       apply (rule corres_alternate1)
       apply (rule get_receive_slot_dcorres)
      apply (unfold dc_def)[1]
      apply (rule dcorres_transfer_caps_loop, auto)[1]
     apply wp[1]
    apply (simp only: ball_conj_distrib)
    apply (wp get_rs_cte_at)
   apply simp
  apply clarsimp
  done

lemma dcorres_lookup_extra_caps:
  "\<lbrakk>evalMonad (lookup_ipc_buffer False thread) s = Some buffer; get_tcb thread s = Some t;
    valid_global_refs s; valid_objs s; valid_irq_node s; valid_idle s; valid_etcbs s;
    not_idle_thread thread s\<rbrakk>
    \<Longrightarrow> dcorres (dc \<oplus> (\<lambda>extra extra'. extra = transform_cap_list extra'))
     \<top> ((=) s)
     (Endpoint_D.lookup_extra_caps thread
                                   (cdl_intent_extras (transform_full_intent (machine_state s) thread t)))
     (Ipc_A.lookup_extra_caps thread buffer (data_to_message_info (arch_tcb_context_get (tcb_arch t) msg_info_register)))"
  apply (clarsimp simp:lookup_extra_caps_def liftE_bindE Endpoint_D.lookup_extra_caps_def)
  apply (rule corres_symb_exec_r)
     apply (rule_tac F = "evalMonad (get_extra_cptrs buffer (data_to_message_info (arch_tcb_context_get (tcb_arch t) msg_info_register))) s = Some rv"
                     in corres_gen_asm2)
     apply (rule corres_mapME[where S = "{(x,y). x = of_bl y \<and> length y = word_bits}"])
           prefer 3
           apply simp
           apply (rule dcorres_lookup_cap_and_slot[simplified])
            apply (clarsimp simp:transform_cap_list_def)+
       apply wp
       apply simp
      apply (case_tac buffer)
       apply clarsimp
       apply (simp add:transform_full_intent_def Let_def)
       apply (rule get_ipc_buffer_words_empty)
        apply (simp add:obj_at_def)
        apply (erule get_tcb_SomeD)
       apply simp
      apply clarify
      apply (subst evalMonad_get_extra_cptrs)
         apply simp+
     apply (case_tac buffer)
      apply clarsimp
     apply clarify
     apply (drule evalMonad_get_extra_cptrs)
       apply (simp del:get_extra_cptrs.simps add: zip_map_eqv[where g = "\<lambda>x. x",simplified])+
     apply (simp add: word_bits_def del:get_extra_cptrs.simps)
    apply (wp evalMonad_wp)
      apply (case_tac buffer)
       apply (simp add:get_extra_cptrs_def empty_when_fail_simps)+
      apply (simp add:liftM_def)
      apply (rule empty_when_fail_compose)
        apply (simp add:empty_when_fail_simps)+
       apply (rule empty_when_fail_mapM)
       apply (simp add:weak_det_spec_load_word_offs empty_when_fail_load_word_offs)
      apply (rule weak_det_spec_mapM)
      apply (simp add:weak_det_spec_load_word_offs)
     apply (case_tac buffer)
      apply (simp add:get_extra_cptrs_def weak_det_spec_simps)+
     apply (simp add:liftM_def)
     apply (rule weak_det_spec_compose)
      apply (simp add:weak_det_spec_simps)
     apply (rule weak_det_spec_mapM)
     apply (simp add:weak_det_spec_load_word_offs)
    apply (clarsimp simp:valid_state_def valid_pspace_def cur_tcb_def)+
   apply (wp|clarsimp)+
  done

lemma dcorres_copy_mrs':
  notes hoare_post_taut[wp] if_cong[cong]
  shows
  "dcorres dc \<top> ((\<lambda>s. evalMonad (lookup_ipc_buffer in_receive recv) s = Some rv)
    and valid_idle and not_idle_thread thread and not_idle_thread recv and tcb_at recv
    and valid_objs and pspace_aligned and pspace_distinct and valid_etcbs)
    (corrupt_ipc_buffer recv in_receive)
    (copy_mrs send rva recv rv (mi_length (data_to_message_info (arch_tcb_context_get (tcb_arch tcb) msg_info_register))))"
  apply (rule dcorres_expand_pfx)
  apply (clarsimp simp:corrupt_ipc_buffer_def)
  apply (case_tac rv)
   apply (rule corres_guard_imp)
     apply (rule corres_symb_exec_l)
        apply (rule_tac F = " rvb = None " in corres_gen_asm)
        apply (clarsimp simp:copy_mrs_def)
        apply (rule corres_dummy_return_l)
        apply (rule corres_split[OF set_registers_corres])
          apply (rule corres_symb_exec_r)+
             apply (rule corres_trivial[OF corres_free_return])
            apply (wp | clarsimp split:option.splits)+
       prefer 2
       apply (wpsimp wp:  hoare_vcg_prop[where P=True] cdl_get_ipc_buffer_None)
      apply (clarsimp simp:get_ipc_buffer_def gets_the_def exs_valid_def gets_def
               get_def bind_def return_def assert_opt_def fail_def split:option.splits | rule conjI)+
      apply (frule(1) tcb_at_is_etcb_at, clarsimp simp: is_etcb_at_def, fold get_etcb_def)
      apply (clarsimp simp:not_idle_thread_def tcb_at_def opt_cap_tcb)+
     apply (simp split:cdl_cap.splits)
    apply clarsimp
   apply simp+
  apply (drule lookup_ipc_buffer_SomeB_evalMonad)
  apply clarsimp
  apply (rule corres_symb_exec_l)
     apply (rule_tac F = "rvb = Some b" in corres_gen_asm)
     apply clarsimp
     apply (rule corres_guard_imp[OF dcorres_copy_mrs])
       apply (simp add:data_to_message_info_valid)+
     apply (clarsimp simp:ipc_frame_wp_at_def obj_at_def cte_wp_at_cases)
     apply (drule_tac t = "tcb_ipcframe obj" in sym)
     apply (clarsimp split:cap.splits simp add:ipc_buffer_wp_at_def obj_at_def)
    apply (clarsimp simp:get_ipc_buffer_def gets_the_def exs_valid_def gets_def
       get_def bind_def return_def assert_opt_def fail_def split:option.splits | rule conjI)+
     apply (clarsimp simp: obj_at_def, frule(1) valid_etcbs_tcb_etcb, fold get_etcb_def)
     apply (subgoal_tac "get_tcb recv s' = Some obj")
      apply (clarsimp simp:not_idle_thread_def tcb_at_def opt_cap_tcb get_tcb_def)+
    apply (simp split:cdl_cap.splits)
   apply (rule hoare_pre, wp hoare_vcg_prop[where P=True]  cdl_get_ipc_buffer_Some)
        apply (fastforce simp:cte_wp_at_def)
       by clarsimp+


lemma opt_cap_valid_etcbs:
  "\<lbrakk>tcb_at ptr s; valid_etcbs s; ptr \<noteq> idle_thread s;
    sl \<in> tcb_abstract_slots \<or> sl = tcb_pending_op_slot\<rbrakk> \<Longrightarrow>
  \<exists>cap. opt_cap (ptr, sl) (transform s) = Some cap"
  apply (clarsimp simp: tcb_at_def)
  apply (frule(1) valid_etcbs_get_tcb_get_etcb)
  apply (clarsimp simp: opt_cap_tcb)
  done

lemma dcorres_set_mrs':
  "dcorres dc \<top> ((\<lambda>s. evalMonad (lookup_ipc_buffer in_receive recv) s = Some rv)
    and valid_idle and not_idle_thread thread and not_idle_thread recv and tcb_at recv
    and valid_objs and pspace_aligned and pspace_distinct and valid_etcbs)
    (corrupt_ipc_buffer recv in_receive)
    (set_mrs recv rv msgs)"
  supply if_cong[cong]
  apply (rule dcorres_expand_pfx)
  apply (clarsimp simp:corrupt_ipc_buffer_def)
    apply (case_tac rv)
      apply (rule corres_symb_exec_l)
        apply (rule_tac F = " rva = None " in corres_gen_asm)
        apply (clarsimp simp:copy_mrs_def)
           apply (rule corres_guard_imp[OF set_mrs_corres_no_recv_buffer])
           apply simp+
      apply (clarsimp simp:get_ipc_buffer_def gets_the_def exs_valid_def gets_def
        get_def bind_def return_def assert_opt_def fail_def split:option.splits | rule conjI)+
      apply (clarsimp simp:not_idle_thread_def)
      apply (rule opt_cap_valid_etcbs, clarsimp+)
    apply (simp split:cdl_cap.splits)
      apply (rule hoare_pre, wp hoare_vcg_prop[where P=True] cdl_get_ipc_buffer_None)
     apply simp+
  apply (drule lookup_ipc_buffer_SomeB_evalMonad)
  apply clarsimp
  apply (rule corres_symb_exec_l)
    apply (rule_tac F = "rva = Some b" in corres_gen_asm)
    apply clarsimp
    apply (rule corrupt_frame_include_self)
    apply (rule corres_guard_imp[OF set_mrs_corres])
      apply (simp add:data_to_message_info_valid)+
    apply (clarsimp simp:ipc_frame_wp_at_def obj_at_def cte_wp_at_cases)
    apply (drule_tac t = "tcb_ipcframe obj" in sym)
    apply (clarsimp split:cap.splits simp add:ipc_buffer_wp_at_def obj_at_def)+
    apply (clarsimp simp:ipc_frame_wp_at_def obj_at_def cte_wp_at_cases)
    apply (drule_tac t = "tcb_ipcframe obj" in sym)
    apply (clarsimp split:cap.splits simp add:ipc_buffer_wp_at_def obj_at_def)+
    apply (clarsimp dest!:get_tcb_rev)
   apply (clarsimp simp:get_ipc_buffer_def gets_the_def exs_valid_def gets_def not_idle_thread_def
      get_def bind_def return_def assert_opt_def fail_def split:option.splits | rule conjI)+
   apply (rule opt_cap_valid_etcbs, clarsimp+)
   apply (simp split:cdl_cap.splits)
     apply wp
     apply (wp cdl_get_ipc_buffer_Some)
      apply (fastforce simp:cte_wp_at_def)
     by clarsimp+

lemma lookup_ipc_buffer_tcb_at:
  "evalMonad (lookup_ipc_buffer in_receive thread) sa = Some a \<Longrightarrow> tcb_at thread sa"
  apply (case_tac a)
    apply clarsimp
    apply (frule lookup_ipc_buffer_None_evalMonad)
    apply (clarsimp simp:tcb_at_def get_tcb_SomeD obj_at_def)+
    apply (frule lookup_ipc_buffer_SomeB_evalMonad)
  apply (clarsimp simp:is_tcb_def obj_at_def)
done

lemma evalMonad_lookup_ipc_buffer_wp':
assumes cte_wp:"\<And>P slot. \<lbrace>cte_wp_at P slot\<rbrace> f \<lbrace>\<lambda>r. cte_wp_at P slot\<rbrace>"
assumes tcb_wp:"\<And>buf t. \<lbrace>ipc_buffer_wp_at buf t\<rbrace> f \<lbrace>\<lambda>r. ipc_buffer_wp_at buf t \<rbrace>"
shows "\<lbrace>\<lambda>s. evalMonad (lookup_ipc_buffer in_receive x) s = Some buf\<rbrace> f \<lbrace>\<lambda>rv s. evalMonad (lookup_ipc_buffer in_receive x) s = Some buf\<rbrace>"
  apply (simp add:valid_def lookup_ipc_buffer_def)
    apply (subst evalMonad_compose)
      apply (simp add:empty_when_fail_thread_get weak_det_spec_thread_get)+
      apply wp
    apply (clarsimp split:option.split_asm simp:evalMonad_thread_get_eq)
    apply (frule use_valid[OF _ tcb_wp])
     apply (clarsimp simp:get_tcb_ko_at ipc_buffer_wp_at_def obj_at_def)
     apply (fastforce)
    apply (clarsimp simp:ipc_buffer_wp_at_def obj_at_def dest!:get_tcb_rev)
    apply (subst evalMonad_compose)
      apply (simp add:empty_when_fail_thread_get weak_det_spec_thread_get)+
      apply wp
    apply (subst (asm) evalMonad_compose)
      apply (simp add:empty_when_fail_get_cap weak_det_spec_get_cap)+
      apply wp
    apply (case_tac buf)
      apply clarsimp
      apply (clarsimp split:option.splits simp:evalMonad_get_cap dest!:caps_of_state_cteD)
      apply (frule use_valid[OF _ cte_wp])
        apply simp
      apply (clarsimp simp:evalMonad_get_cap cte_wp_at_caps_of_state evalMonad_thread_get_eq)
      apply (subst evalMonad_compose)
        apply (simp add:empty_when_fail_get_cap weak_det_spec_get_cap)+
        apply wp
      apply (clarsimp simp:evalMonad_get_cap)
        apply (clarsimp split:cap.splits arch_cap.splits)
        apply (fastforce simp:evalMonad_def return_def)
      apply (clarsimp simp:evalMonad_get_cap split:option.split_asm cap.split_asm)
    apply (drule caps_of_state_cteD)
    apply (rename_tac arch_cap)
    apply (frule_tac P1 = "(=) (cap.ArchObjectCap arch_cap)" in use_valid[OF _ cte_wp])
      apply (erule cte_wp_at_weakenE)
      apply clarsimp
    apply (clarsimp simp:cte_wp_at_caps_of_state evalMonad_thread_get_eq)
    apply (subst evalMonad_compose)
      apply (simp add:empty_when_fail_get_cap weak_det_spec_get_cap)+
      apply wp
    apply (simp add:evalMonad_get_cap)
    apply (case_tac arch_cap)
      apply simp_all
    apply (clarsimp simp:evalMonad_def return_def split:if_splits)
done

lemma ipc_buffer_wp_at_copy_mrs[wp]:
  "\<lbrace>ipc_buffer_wp_at buf t \<rbrace>
     copy_mrs send rva recv rv (mi_length (data_to_message_info (arch_tcb_context_get (tcb_arch obj') msg_info_register)))
   \<lbrace>\<lambda>r. ipc_buffer_wp_at buf t\<rbrace>"
  unfolding copy_mrs_def
  apply (wp|wpc)+
     apply (wp mapM_wp)
       apply (simp add:store_word_offs_def ipc_buffer_wp_at_def)
       apply wp+
      prefer 2
      apply fastforce
     apply (clarsimp simp:ipc_buffer_wp_at_def)
    apply (rule_tac Q="\<lambda>rv. ipc_buffer_wp_at buf t" in hoare_strengthen_post)
     apply (wp mapM_wp)
     apply fastforce
    apply (clarsimp)
   apply wp
  apply assumption
  done

lemma copy_mrs_valid_irq_node:
  "\<lbrace>valid_irq_node\<rbrace> copy_mrs a b c d e
            \<lbrace>\<lambda>rva s. valid_irq_node s\<rbrace>"
  apply (simp add:valid_irq_node_def)
  apply (wpsimp wp: hoare_vcg_all_lift|wps)+
  done

lemma corres_complete_ipc_transfer:
  "ep' = ep
  \<Longrightarrow> dcorres dc \<top>
           (valid_objs and pspace_aligned and valid_global_refs and pspace_distinct and valid_mdb
            and (\<lambda>s. not_idle_thread (cur_thread s) s) and valid_irq_node
            and valid_idle and not_idle_thread recv and not_idle_thread send and valid_etcbs)
           (Endpoint_D.do_ipc_transfer ep' send recv can_grant) \<comment> \<open>FIXME argument order\<close>
           (Ipc_A.do_ipc_transfer send ep badge can_grant recv)"
  apply (clarsimp simp: Endpoint_D.do_ipc_transfer_def Ipc_A.do_ipc_transfer_def)
  apply (rule dcorres_expand_pfx)
  apply (rule dcorres_symb_exec_r_evalMonad)
     apply wp
    apply (clarsimp simp:thread_get_def get_send_slots_def get_thread_def bind_assoc)
    apply (rule dcorres_gets_the)
     apply (clarsimp, frule(1) valid_etcbs_get_tcb_get_etcb)
     apply (clarsimp simp:opt_object_tcb not_idle_thread_def transform_tcb_def split del:if_split)
     apply (case_tac "tcb_fault obj'")
      apply (clarsimp split del:if_split)
      apply (rule dcorres_symb_exec_r_evalMonad,wp)
        apply (simp add:do_normal_transfer_def get_message_info_def select_f_get_register split del:if_split)
        apply (rule dcorres_absorb_gets_the)
        apply (simp add:alternative_bind bind_assoc split del:if_split)
        apply (rule corres_alternate1)
        apply (rule corres_guard_imp)
          apply (rule corres_split)
             apply (rule corres_if, simp)
              apply (rule corres_split_catch)
                 apply clarsimp
                 apply (rule corres_guard_imp[OF dcorres_lookup_extra_caps])
                          apply (clarsimp simp:not_idle_thread_def)+
                 apply assumption
                apply (rule corres_trivial)
                apply (clarsimp simp:transform_cap_list_def)
               apply wp+
             apply (rule corres_trivial)
             apply (clarsimp simp:transform_cap_list_def)
            apply (rule corres_split[OF dcorres_copy_mrs'])
              apply (simp add:get_message_info_def select_f_get_register bind_assoc transform_cap_list_def)
              apply (rule corres_split[OF transfer_caps_dcorres])
                apply (rule corres_corrupt_tcb_intent_dupl)
                apply (rule corres_split[OF set_message_info_corres])
  unfolding K_bind_def
                  apply (rule corrupt_tcb_intent_as_user_corres)
                 apply (wp evalMonad_lookup_ipc_buffer_wp' hoare_vcg_ball_lift copy_mrs_valid_irq_node
                        | simp add:not_idle_thread_def split_def)+
           apply (wp hoare_vcg_ball_lift | clarsimp)+
           apply (rule validE_validE_R)
           apply (rule hoare_vcg_conj_liftE1)
            apply (rule hoare_post_imp_R)
             apply (rule validE_validE_R)
             apply (rule hoare_vcg_conj_liftE1[OF lookup_extra_caps_srcs])
             apply (rule hoare_post_imp_dc2_actual[OF lookup_extra_caps_inv[where P=valid_objs]])
            apply clarsimp
            apply (drule(1) bspec)
            apply (clarsimp simp:cte_wp_at_caps_of_state)
            apply (case_tac "a = cap.NullCap",simp+)
            apply (erule(1) caps_of_state_valid_cap)
           apply (simp add:lookup_extra_caps_def)
           apply (wp mapME_wp mapME_length)
             apply (simp add:validE_def)
             apply (rule hoare_drop_imp)
             apply wp
            apply fastforce
           apply wp
           apply (rule hoare_vcg_conj_lift)
            apply (rule hoare_strengthen_post[OF get_extra_cptrs_length])
            apply (simp add:msg_max_length_def max_ipc_length_unfold msg_max_extra_caps_def)
           apply wp+
         apply fastforce
        apply clarsimp
        apply (rule conjI)
         apply (drule lookup_ipc_buffer_tcb_at)+
         apply (clarsimp dest!:get_tcb_SomeD simp:tcb_at_def not_idle_thread_def)
         apply (rule conjI)
          apply (simp add:data_to_message_info_valid)+
         apply (simp add:msg_max_length_def max_ipc_length_unfold)
        apply (clarsimp simp:not_idle_thread_def tcb_at_def max_ipc_length_unfold msg_max_length_def)+
        apply (drule lookup_ipc_buffer_tcb_at)+
        apply ((clarsimp simp:tcb_at_def empty_when_fail_lookup_ipc_buffer weak_det_spec_lookup_ipc_buffer)+)[3]
     apply (clarsimp simp:alternative_bind bind_assoc do_fault_transfer_def split del: if_split)
     apply (rule corres_alternate2)
     apply (rule corres_guard_imp)
       apply (rule corres_symb_exec_r)
          apply (rule corres_symb_exec_r)
             apply (rule corres_symb_exec_r)
                apply (clarsimp)
                apply (rule corres_split[OF dcorres_set_mrs'])
                  apply (rule corres_corrupt_tcb_intent_dupl)
                  apply (rule corres_split[OF set_message_info_corres])
  unfolding K_bind_def
                    apply (rule corrupt_tcb_intent_as_user_corres)
                   apply (wp|clarsimp simp:not_idle_thread_def)+
            apply wpsimp+
         apply (rule hoare_allI[OF hoare_drop_imp])
         apply (wp|clarsimp)+
     apply (rule conjI,simp)
     apply (clarsimp simp:lookup_ipc_buffer_tcb_at not_idle_thread_def opt_object_tcb
      empty_when_fail_lookup_ipc_buffer weak_det_spec_lookup_ipc_buffer | frule(1) valid_etcbs_get_tcb_get_etcb)+
  done

lemma dcorres_handle_arch_fault_reply:
  "dcorres dc \<top> (tcb_at y and valid_idle and not_idle_thread y and  valid_etcbs)
   (corrupt_tcb_intent y)
   (handle_arch_fault_reply a y mi mrs)"
  apply (cases a)
  apply (clarsimp simp: handle_arch_fault_reply_def)
  apply (rule corres_guard_imp)
    apply (rule corres_corrupt_tcb_intent_return)
   apply assumption
  apply clarsimp
  done


lemma dcorres_handle_fault_reply:
  "dcorres dc \<top> (tcb_at y and valid_idle and not_idle_thread y and  valid_etcbs)
   (corrupt_tcb_intent y)
   (handle_fault_reply a y mi mrs)"
  unfolding arch_get_sanitise_register_info_def
  apply (case_tac a)
     apply (simp_all)
     apply (rule dummy_corrupt_tcb_intent_corres)+
    apply (rule corres_dummy_return_l)
    apply (rule corres_guard_imp)
      apply (rule corres_symb_exec_r)
         apply (rule corres_split[OF corrupt_tcb_intent_as_user_corres corres_trivial[OF corres_free_return]])
          apply (wp|clarsimp simp: arch_get_sanitise_register_info_def)+
   apply (rule corres_dummy_return_l)
   apply (rule corres_guard_imp)
        apply (rule corres_split[OF corrupt_tcb_intent_as_user_corres corres_trivial[OF corres_free_return]])
         apply (wp|clarsimp)+
  apply (rule dcorres_handle_arch_fault_reply)
  done

lemma alternative_distrib2:
  "(do x \<leftarrow> a;  (b x \<sqinter> c x) od) = ((do x\<leftarrow>a; b x od) \<sqinter> (do x\<leftarrow>a; c x od)) "
  apply (simp add:bind_def alternative_def UNION_eq)
  apply (rule ext)+
  apply force
  done

lemma set_cap_overlap:
  "cdl_objects s recv = Some (Tcb tcb)
    \<Longrightarrow> (KHeap_D.set_cap (recv,tcb_pending_op_slot) a >>= K (KHeap_D.set_cap (recv,tcb_pending_op_slot) b)) s
        = (KHeap_D.set_cap (recv,tcb_pending_op_slot) b) s"
  apply (rule monad_state_eqI)
  by (auto simp: KHeap_D.set_cap_def KHeap_D.set_object_def in_monad has_slots_def
                 update_slots_def simpler_modify_def snd_bind valid_def
                 snd_return gets_the_def snd_gets assert_opt_def object_slots_def
           cong: cdl_object.case_cong split: option.splits)

lemma remove_parent_dummy_when_pending_wp:
  "\<lbrakk>mdb_cte_at (swp (cte_wp_at ((\<noteq>)cap.NullCap) ) s) (cdt s); tcb_at y s\<rbrakk>
  \<Longrightarrow>\<lbrace>(=) (transform s)\<rbrace> remove_parent (y, tcb_pending_op_slot) \<lbrace>\<lambda>r. (=) (transform s)\<rbrace>"
  apply (clarsimp simp:remove_parent_def valid_def simpler_modify_def transform_def)
  apply (rule ext)
  apply (clarsimp simp:transform_cdt_def| rule conjI)+
    apply (clarsimp simp: map_lift_over_def transform_cdt_slot_inj_on_mdb_cte_at split:if_splits)
    apply (frule_tac slot'="(aa,bb)" in mdb_cte_at_cte_wp_at')
      apply simp
    apply (drule_tac ad = aa in  invalid_cte_wp_at_pending_slot)
      apply fastforce+
    apply (clarsimp simp: map_lift_over_def transform_cdt_slot_inj_on_mdb_cte_at split:if_splits)
    apply (drule_tac ad = ab in invalid_cte_wp_at_pending_slot)
      apply fastforce+
      apply (erule mdb_cte_at_cte_wp_at')
        apply simp+
    apply (clarsimp simp: map_lift_over_def transform_cdt_slot_inj_on_mdb_cte_at | rule conjI)+
      apply (drule_tac ad = ac in invalid_cte_wp_at_pending_slot)
        apply fastforce+
      apply (erule mdb_cte_at_cte_wp_at)
        apply simp+
    apply clarsimp
      apply (drule_tac ad = aa in invalid_cte_wp_at_pending_slot)
        apply fastforce+
done

lemma dcorres_set_thread_state_Restart:
  "dcorres dc \<top>
           (\<lambda>a. valid_mdb a \<and> not_idle_thread recver a \<and> st_tcb_at idle (idle_thread a) a \<and> valid_etcbs a)
           (do y \<leftarrow> delete_cap_simple (recver, tcb_pending_op_slot);
               KHeap_D.set_cap (recver, tcb_pending_op_slot) RestartCap
            od)
           (set_thread_state recver Structures_A.thread_state.Restart)"
  supply option.case_cong[cong] if_cong[cong]
  apply (rule dcorres_expand_pfx)
  apply (case_tac "\<not> tcb_at recver s'")
   apply (clarsimp simp:set_thread_state_def)
   apply (clarsimp simp:delete_cap_simple_def bind_assoc)
   apply (rule dcorres_gets_the)
    apply (clarsimp simp:tcb_at_def)+
  apply (subgoal_tac "dcorres dc ((=) (transform s')) ((=) s') (KHeap_D.set_cap (recver, 5) RestartCap)
           (KHeap_A.set_object recver (TCB (update_tcb_state Structures_A.thread_state.Restart y)))")
   apply (clarsimp simp:delete_cap_simple_def bind_assoc
                        assert_opt_def set_thread_state_def)
   apply (simp add: bind_assoc[symmetric])
   apply (rule dcorres_rhs_noop_below)
      apply (rule set_thread_state_ext_dcorres)
     apply (simp add: bind_assoc)
     apply (rule dcorres_gets_the)
      apply (simp add:bind_assoc unless_def when_def)
      apply (clarsimp simp:st_tcb_at_def obj_at_def opt_cap_tcb not_idle_thread_def)
      apply (simp add:always_empty_slot_def bind_assoc)
      apply (intro conjI impI)
       apply (rule corres_symb_exec_l)
          apply (rule corres_symb_exec_l)
             apply (rule_tac Q = "\<lambda>rv. (=) (transform s'a)" in corres_symb_exec_l)
                apply (simp add:corres_underlying_def)
                apply (frule(1) valid_etcbs_get_tcb_get_etcb, clarsimp)
                apply (subst set_cap_overlap[unfolded K_def])
                 apply (drule opt_object_tcb, assumption)
                  apply simp
                 apply (simp add:transform_tcb_def)
                apply (frule opt_object_tcb, assumption)
                 apply simp
                apply (clarsimp simp: set_object_def bind_def in_monad gets_the_def simpler_gets_def
                get_def return_def put_def KHeap_D.set_cap_def assert_opt_def transform_tcb_def
                get_object_def
                has_slots_def object_slots_def update_slots_def KHeap_D.set_object_def simpler_modify_def)
                apply (clarsimp simp: transform_def transform_current_thread_def)
                apply (intro conjI ext)
                 apply (frule(1) valid_etcbs_get_tcb_get_etcb, clarsimp simp: get_etcb_def)
                 apply (clarsimp simp:transform_objects_def transform_tcb_def
                  infer_tcb_pending_op_def restrict_map_def map_add_def tcb_slots)
                apply (solves \<open>clarsimp simp: transform_objects_def transform_tcb_def not_idle_thread_def
                                              tcb_slots restrict_map_def map_add_def
                                       dest!: get_tcb_SomeD get_etcb_SomeD\<close>)
               prefer 2
               apply (wp remove_parent_dummy_when_pending_wp)
                apply (clarsimp simp:valid_mdb_def)
               apply (simp add:tcb_at_def)
              apply clarsimp
              apply (wp remove_parent_dummy_when_pending_slot)
                apply (simp add:valid_mdb_def)
               apply (simp add:tcb_at_def get_tcb_def)
              apply simp
             apply clarsimp
            prefer 2
            apply (rule_tac P="x = (PageTableUnmap_D.is_final_cap' obj (transform s'a))" in hoare_gen_asm)
            apply simp
            apply (subst fast_finalise_no_effect)
                apply simp
               apply (simp add: not_idle_thread_def)
              apply (simp add: tcb_at_def)
             apply simp
            apply ((clarsimp simp:tcb_caller_slot_def infer_tcb_pending_op_def cap_counts_def
             tcb_pending_op_slot_def tcb_cspace_slot_def tcb_replycap_slot_def
             tcb_vspace_slot_def PageTableUnmap_D.is_final_cap'_def
             PageTableUnmap_D.is_final_cap_def split:if_split_asm Structures_A.thread_state.splits
            | wp exs_valid_return exs_valid_gets)+)[1]
           apply clarsimp
           apply (subst fast_finalise_no_effect)
               apply simp
              apply (simp add: not_idle_thread_def)
             apply (simp add: tcb_at_def)
            apply simp
           apply (clarsimp simp:tcb_caller_slot_def infer_tcb_pending_op_def cap_counts_def
            tcb_pending_op_slot_def tcb_cspace_slot_def tcb_replycap_slot_def
            tcb_vspace_slot_def PageTableUnmap_D.is_final_cap'_def
            PageTableUnmap_D.is_final_cap_def split:if_split_asm Structures_A.thread_state.splits
           | wp exs_valid_return exs_valid_gets)+
     apply (frule(1) valid_etcbs_get_tcb_get_etcb, clarsimp simp: get_etcb_def)
     apply (subst opt_cap_tcb)
        apply simp
       apply (simp add: get_etcb_def)
      apply (simp add: not_idle_thread_def)
     apply (simp add: tcb_pending_op_slot_def)
    apply ((wp | clarsimp | simp)+)[2]
  apply (frule(1) valid_etcbs_get_tcb_get_etcb, clarsimp simp: get_etcb_def)
  apply (simp add:KHeap_D.set_cap_def set_object_def get_object_def gets_the_def gets_def bind_assoc)
  apply (rule dcorres_absorb_get_l)
  apply (rule dcorres_absorb_get_r)
  apply (rule corres_assert_assume[rotated], clarsimp dest!: get_tcb_SomeD)
  apply (rule corres_assert_assume[rotated], clarsimp dest!: get_tcb_SomeD)
  apply (rule dcorres_absorb_get_r)
  apply (frule opt_object_tcb)
    apply (simp add: get_etcb_def)
   apply (simp add: not_idle_thread_def)
  apply (clarsimp simp: assert_opt_def has_slots_def transform_tcb_def object_slots_def
    update_slots_def tcb_ipcbuffer_slot_def KHeap_D.set_object_def simpler_modify_def)
  apply (clarsimp simp: corres_underlying_def put_def transform_def transform_current_thread_def
    not_idle_thread_def)
  apply (intro ext conjI)
  apply (fastforce simp: transform_objects_def transform_tcb_def restrict_map_def map_add_def
                         assert_def infer_tcb_pending_op_def  not_idle_thread_def tcb_slots)
  done


lemma when_return:
  "when f (return ()) = return ()"
  by (simp add:when_def)

crunch valid_etcbs[wp]: handle_fault_reply valid_etcbs

lemma do_reply_transfer_corres:
  notes wp_post_taut [wp]
  shows
  "slot' = transform_cslot_ptr slot \<Longrightarrow>
   dcorres dc \<top>
     (invs and tcb_at recver and tcb_at sender
      and cte_wp_at (\<lambda>cap. \<exists>R. cap = cap.ReplyCap recver False R) slot
      and (\<lambda>s. not_idle_thread (cur_thread s) s)
      and not_idle_thread recver and not_idle_thread sender and valid_etcbs)
     (Endpoint_D.do_reply_transfer sender recver slot' can_grant)
     (Ipc_A.do_reply_transfer sender recver slot can_grant)"
  apply (clarsimp simp:do_reply_transfer_def Endpoint_D.do_reply_transfer_def)
  apply (clarsimp simp:get_thread_state_def thread_get_def get_thread_fault_def)
  apply (rule dcorres_absorb_gets_the)
  apply (clarsimp simp:assert_def corres_free_fail bind_assoc)
  apply (frule(1) valid_etcbs_get_tcb_get_etcb)
  apply (rule dcorres_gets_the[rotated])
   apply (clarsimp simp:not_idle_thread_def
     opt_object_tcb transform_tcb_def | intro conjI impI)+
   apply (rule corres_guard_imp)
     apply (rule corres_split)
        apply (rule corres_complete_ipc_transfer; simp)
       apply (rule corres_split[OF delete_cap_simple_corres])
         apply (rule corres_split_noop_rhs2[OF set_thread_state_corres
                                               possible_switch_to_dcorres[THEN corres_trivial]])
          apply (wp | clarsimp simp:not_idle_thread_def)+
   apply (clarsimp simp:invs_def valid_state_def valid_pspace_def not_idle_thread_def)
   apply (case_tac slot,clarsimp simp:cte_wp_at_caps_of_state)
   apply (drule valid_idle_has_null_cap)
       apply simp+
  apply (clarsimp simp:bind_assoc)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF delete_cap_simple_corres])
      apply (rule corres_symb_exec_r)
         apply (rule corres_symb_exec_r)
            apply (rule corres_symb_exec_r)
               apply (rule corres_split[OF dcorres_handle_fault_reply])
                 apply (rule corres_split[OF thread_set_fault_corres])
                    apply (simp add: when_return split del: if_split)
                   apply (simp add: dc_def[symmetric] if_distrib[where f = "set_thread_state recver"]
                         split del: if_split)
                   apply (rule corres_split_noop_rhs2)
                      apply (rule corres_if_rhs)
                       apply (rule corres_alternate2)
                       apply (rule set_thread_state_corres)
                      apply (rule corres_alternate1)
                      apply (rule set_thread_state_corres)
                     apply (rule corres_trivial)
                     apply (clarsimp simp: when_def dc_def[symmetric])
                     apply (rule possible_switch_to_dcorres)
                    apply wp+
                  apply simp
                 apply clarsimp+
                 apply (wp wp_post_taut thread_set_no_change_tcb_state
                   hoare_drop_imps thread_set_cur_thread_idle_thread
                   thread_set_valid_idle
                   | simp add:not_idle_thread_def)+
    apply (rule_tac Q = "\<lambda>r s. invs s \<and> not_idle_thread recver s \<and> valid_etcbs s
        \<and> tcb_at recver s "
      in  hoare_strengthen_post)
     apply (clarsimp simp:not_idle_thread_def)
     apply (wp cap_delete_one_reply_st_tcb_at)+
    apply (clarsimp simp:not_idle_thread_def invs_valid_idle st_tcb_at_tcb_at)
   apply (wp |clarsimp)+
  apply (rule conjI)
   apply (case_tac slot)
   apply (clarsimp simp:invs_def not_idle_thread_def valid_state_def)
   apply (clarsimp simp:cte_wp_at_caps_of_state)
   apply (drule valid_idle_has_null_cap)
       apply assumption+
   apply (fastforce simp:valid_state_def)
  apply (rule emptyable_cte_wp_atD)
    apply (fastforce simp:is_master_reply_cap_def invs_def
                          valid_state_def valid_pspace_def valid_idle_def)+
  done

lemma set_endpoint_valid_irq_node[wp]:
  "\<lbrace>valid_irq_node and ep_at w\<rbrace> set_endpoint w ep \<lbrace>\<lambda>rv. valid_irq_node\<rbrace>"
  apply (clarsimp simp:valid_irq_node_def)
  apply wp
   apply (simp add:set_simple_ko_def)
   apply (wp hoare_vcg_all_lift)
      apply (rule_tac Q="\<lambda>s. \<forall>irq. cap_table_at 0 (interrupt_irq_node s irq) s \<and> ep_at w s" in hoare_vcg_precond_imp)
       apply (clarsimp simp: set_object_def get_object_def in_monad get_def put_def bind_def
                             return_def valid_def obj_at_def)
       apply (drule_tac x = irq in spec)
       apply (clarsimp simp: is_cap_table_def is_ep_def)
      apply (simp split: Structures_A.kernel_object.splits)
     apply wp+
   apply (clarsimp simp: get_object_def|wp)+
  done

lemma dcorres_if_rhs:
  assumes G: "G \<Longrightarrow> corres_underlying sr nf nf' rvr P Q a b"
  and nG: "\<not> G \<Longrightarrow> corres_underlying sr nf nf' rvr P Q' a c"
  shows "corres_underlying sr nf nf' rvr P
    (\<lambda>s. (G \<longrightarrow> Q s) \<and> (\<not> G \<longrightarrow> Q' s)) a (if G then b else c)"
  apply (clarsimp)
  apply (safe)
   apply (erule G)
  apply (erule nG)
  done

(* this is ugly and terrible, but pretty much recreates
   the old recv_sync_ipc_corres proof to avoid duplication *)
lemma dcorres_receive_sync:
  "\<lbrakk> ep_at ep s; ko_at (kernel_object.Endpoint rv) ep s; not_idle_thread thread s;
        not_idle_thread (cur_thread s) s; st_tcb_at active thread s; valid_state s;
        valid_etcbs s \<rbrakk> \<Longrightarrow>
    dcorres dc ((=) (transform s)) ((=) s)
        (receive_sync thread ep can_grant)
        (case rv of
            Structures_A.endpoint.IdleEP \<Rightarrow> (case is_blocking of
                True \<Rightarrow> do set_thread_state thread
                              (Structures_A.thread_state.BlockedOnReceive ep
                                  \<lparr>receiver_can_grant = can_grant\<rparr>);
                           set_endpoint ep (Structures_A.endpoint.RecvEP [thread])
                        od
                | False \<Rightarrow> do_nbrecv_failed_transfer thread)
          | Structures_A.endpoint.SendEP q \<Rightarrow>
                do assert (q \<noteq> []);
                   queue \<leftarrow> return $ tl q;
                   sender \<leftarrow> return $ hd q;
                   set_endpoint ep $
                     (case queue of [] \<Rightarrow> Structures_A.endpoint.IdleEP
                         | a # list \<Rightarrow> Structures_A.endpoint.SendEP queue);
                   sender_state \<leftarrow> get_thread_state sender;
                   payload \<leftarrow> case sender_state of
                       Structures_A.thread_state.BlockedOnSend ref x \<Rightarrow> return x | _ \<Rightarrow> fail;
                   Ipc_A.do_ipc_transfer sender (Some ep) (sender_badge payload)
                        (sender_can_grant payload) thread;
                   if sender_is_call payload
                   then if sender_can_grant payload \<or> sender_can_grant_reply payload
                        then setup_caller_cap sender thread can_grant
                        else set_thread_state sender Structures_A.thread_state.Inactive
                   else do set_thread_state sender Structures_A.thread_state.Running;
                           do_extended_op (possible_switch_to sender)
                        od
                od
          | Structures_A.endpoint.RecvEP queue \<Rightarrow> (case is_blocking of
              True \<Rightarrow> do set_thread_state thread
                     (Structures_A.thread_state.BlockedOnReceive ep
                          \<lparr>receiver_can_grant = can_grant\<rparr>);
                      set_endpoint ep (Structures_A.endpoint.RecvEP (queue @ [thread]))
                   od
              | False \<Rightarrow> do_nbrecv_failed_transfer thread))"
  supply if_cong[cong]
  apply (clarsimp simp: receive_sync_def gets_def)
  apply (rule dcorres_absorb_get_l)
  apply (case_tac rv)
    (* IdleEP *)
    apply clarsimp
    apply (frule_tac get_endpoint_pick)
     apply (simp add:obj_at_def)
    apply (subst ep_waiting_set_send_lift)
      apply (simp add:valid_state_def)
     apply simp
    apply (clarsimp simp:valid_ep_abstract_def none_is_sending_ep_def option_select_def)
    apply (case_tac is_blocking; simp)
     apply (rule corres_guard_imp)
       apply (rule corres_alternate1)
       apply (rule corres_dummy_return_l)
       apply (rule corres_guard_imp)
         apply (rule corres_split[OF set_thread_state_block_on_receive_corres corres_dummy_set_sync_ep])
          apply (wp|simp)+
    apply (rule corres_alternate2)
    apply (simp add: do_nbrecv_failed_transfer_def)
    apply (rule corres_guard_imp)
      apply (rule corrupt_tcb_intent_as_user_corres, simp, simp)
    apply (simp add: valid_state_def)
    (* SendEP *)
   apply (frule get_endpoint_pick)
    apply (simp add:obj_at_def)
   apply (subst ep_waiting_set_send_lift)
     apply (simp add:valid_state_def)
    apply simp
   apply (clarsimp simp:option_select_def valid_ep_abstract_def)
   apply (rename_tac list)
   apply (drule_tac s = "set list" in sym)
   apply (rule conjI, clarsimp dest!: not_empty_list_not_empty_set)
   apply (clarsimp simp:neq_Nil_conv, rename_tac t ts)
   apply (rule_tac P1="\<top>" and P'="(=) s" and x1 = t
     in dcorres_absorb_pfx[OF select_pick_corres[OF dcorres_expand_pfx],rotated])
      apply clarsimp
     apply clarsimp
    apply clarsimp
   apply (drule_tac x1 = t in iffD2[OF eqset_imp_iff], simp)
   apply (clarsimp simp:ep_waiting_set_send_def get_thread_def bind_assoc gets_the_def gets_def)
   apply (rename_tac tcb payload)
   apply (rule dcorres_absorb_get_l,clarsimp)
   apply (frule(1) valid_etcbs_tcb_etcb, clarsimp)
   apply (subst opt_object_tcb)
      apply (erule get_tcb_rev)
     apply (fastforce simp: get_etcb_def)
    apply (frule_tac a = t and list = "t # ts" in pending_thread_in_send_not_idle)
       apply ((simp add: valid_state_def insertI obj_at_def not_idle_thread_def)+)[4]
   apply (clarsimp simp: assert_opt_def transform_tcb_def infer_tcb_pending_op_def tcb_slots
              split del: if_split)
   apply (rule dcorres_symb_exec_r)
     apply (rule corres_symb_exec_r)
        apply (rule_tac F="sender_state = tcb_state tcb" in corres_gen_asm2)
        apply (clarsimp dest!: get_tcb_SomeD simp: dc_def[symmetric]
                    split del: if_split split: if_split_asm)
        apply (rule corres_guard_imp)
          apply (rule corres_split[OF corres_complete_ipc_transfer])
             apply simp
            apply (rule dcorres_if_rhs)
             apply (rule dcorres_if_rhs)
              apply (simp add:dc_def[symmetric] when_def)
              apply (rule corres_alternate1)+
              apply (rule corres_setup_caller_cap)
              apply (clarsimp simp:st_tcb_at_def obj_at_def generates_pending_def)
             apply (rule corres_alternate2[OF set_thread_state_corres[unfolded tcb_slots]])
            apply (rule corres_alternate1[OF corres_alternate2])
            apply (rule dcorres_rhs_noop_below_True[OF possible_switch_to_dcorres])
            apply (rule set_thread_state_corres[unfolded tcb_slots])
           apply wp
          apply (wp hoare_drop_imps gts_st_tcb_at | simp add:not_idle_thread_def)+
         apply (rule_tac Q="\<lambda>fault. valid_mdb and valid_objs and pspace_aligned
           and pspace_distinct and not_idle_thread t and not_idle_thread thread
           and valid_idle and valid_irq_node and (\<lambda>s. cur_thread s \<noteq> idle_thread s)
           and tcb_at t and tcb_at thread
           and st_tcb_at (\<lambda>rv. rv = Structures_A.thread_state.BlockedOnSend ep payload) t and valid_etcbs"
         in hoare_strengthen_post[rotated])
          apply (clarsimp simp:not_idle_thread_def)
          apply (clarsimp simp:st_tcb_at_def obj_at_def)
         apply ((wp | clarsimp simp:not_idle_thread_def | wps )+)[1]
        apply (frule_tac a = t and list = "t # ts" in pending_thread_in_send_not_idle)
            apply (clarsimp simp:valid_state_def insertI)+
          apply (simp add:obj_at_def not_idle_thread_def)+
         apply (clarsimp simp:valid_state_def st_tcb_at_def obj_at_def valid_pspace_def)
         apply (drule valid_objs_valid_ep_simp)
          apply (simp add:is_ep_def)
         apply (clarsimp simp:valid_ep_def a_type_def
                     split:Structures_A.endpoint.splits list.splits)
        apply (clarsimp simp:valid_state_def valid_pspace_def a_type_def)+
   apply (rule dcorres_to_wp[where Q=\<top>,simplified])
   apply (rule corres_dummy_set_sync_ep)
  (* RecvEP *)
  apply clarsimp
  apply (frule get_endpoint_pick)
   apply (simp add:obj_at_def)
  apply (subst ep_waiting_set_send_lift)
    apply (simp add:valid_state_def)
   apply simp
  apply (clarsimp simp:valid_ep_abstract_def none_is_sending_ep_def option_select_def)
  apply (case_tac is_blocking; simp)
   apply (rule corres_guard_imp)
     apply (rule corres_alternate1)
     apply (rule corres_dummy_return_l)
     apply (rule corres_guard_imp)
       apply (rule corres_split[OF set_thread_state_block_on_receive_corres corres_dummy_set_sync_ep])
        apply (wp|simp)+
  apply (simp add: do_nbrecv_failed_transfer_def)
  apply (rule corres_alternate2)
  apply (rule corres_guard_imp)
    apply (rule corrupt_tcb_intent_as_user_corres, (simp add: valid_state_def)+)
  done

lemma dcorres_complete_signal:
  "dcorres dc \<top> (valid_idle and not_idle_thread thread and valid_etcbs) (corrupt_tcb_intent thread)
           (complete_signal aa thread)"
  apply (clarsimp simp: complete_signal_def get_simple_ko_def get_object_def gets_def bind_assoc)
  apply (rule dcorres_absorb_get_r)
  apply (clarsimp split: option.splits)
  apply (clarsimp simp: assert_def corres_free_fail partial_inv_def a_type_def
          split: Structures_A.kernel_object.splits Structures_A.ntfn.splits)
  apply (rule corres_guard_imp)
    apply (rule corres_dummy_return_l)
    apply (rule corres_split[OF set_register_corres corres_dummy_set_notification])
     apply (wp | clarsimp)+
  done

lemma recv_sync_ipc_corres:
  "\<lbrakk>epptr = cap_ep_ptr ep_cap; ep_id = epptr;  tcb_id_receiver = thread\<rbrakk>\<Longrightarrow>
    dcorres dc
     \<top>
     (ep_at epptr and not_idle_thread thread and (\<lambda>s. not_idle_thread (cur_thread s) s)
      and st_tcb_at active thread
      and valid_state and valid_etcbs)
     (Endpoint_D.receive_ipc tcb_id_receiver ep_id (Grant \<in> cap_rights ep_cap))
     (Ipc_A.receive_ipc thread ep_cap is_blocking)"
  apply (clarsimp simp:corres_free_fail cap_ep_ptr_def Ipc_A.receive_ipc_def
                 split:cap.splits Structures_A.endpoint.splits)
  apply (rename_tac ep_badge ep_rights)
  apply (rule dcorres_expand_pfx)
  apply (rule_tac Q'="\<lambda>ko. (=) s' and ko_at (kernel_object.Endpoint ko) epptr" in corres_symb_exec_r)
     apply (simp add:Endpoint_D.receive_ipc_def get_bound_notification_def thread_get_def gets_the_def gets_def bind_assoc)
     apply (rule dcorres_absorb_get_r)
     apply (clarsimp simp: assert_opt_def corres_free_fail split: Structures_A.kernel_object.splits option.splits )
     apply safe[1]
     \<comment> \<open>not bound\<close>
      apply (rule corres_alternate2)
      apply (rule dcorres_receive_sync, simp_all)[1]
     apply (simp add: get_simple_ko_def gets_def get_object_def bind_assoc)
     apply (rule dcorres_absorb_get_r)
     apply (frule get_tcb_SomeD)
     apply (clarsimp simp add: valid_state_def valid_pspace_def
                     split: kernel_object.splits if_splits)
     apply (rule valid_objsE, assumption, simp)
     apply (clarsimp simp: valid_obj_def valid_tcb_def valid_bound_ntfn_def)
     apply (clarsimp simp: assert_def corres_free_fail obj_at_def partial_inv_def
                    split: Structures_A.kernel_object.splits)
     apply safe[1]
      apply (rule corres_alternate1)
      apply (rule corres_guard_imp)
        apply (rule dcorres_complete_signal, simp+)
     apply (rule corres_alternate2)
     apply (rule dcorres_receive_sync, simp_all add: obj_at_def valid_state_def valid_pspace_def)[1]
    apply (wp get_simple_ko_ko_at | clarsimp)+
  done

lemma option_select_not_empty:
  "A\<noteq>{} \<Longrightarrow> option_select A = (do a\<leftarrow>select A;return (Some a) od)"
  by (clarsimp simp:option_select_def)

lemma dcorres_splits:
  "\<lbrakk> T a \<Longrightarrow> dcorres r P (Q a) f (g a);
    \<not> T a \<Longrightarrow> dcorres r P (Q' a) f (g a)\<rbrakk>\<Longrightarrow>
    dcorres r P ( (\<lambda>s. (T a) \<longrightarrow> (Q a s)) and (\<lambda>s. (\<not> (T a)) \<longrightarrow> (Q' a s)) ) f (g a)"
  apply (case_tac "T a")
    apply clarsimp+
done

lemma dcorres_alternate_seq1:
  "corres_underlying t nf nf' r P Q (do y \<leftarrow> f; g y od) rh
    \<Longrightarrow> corres_underlying t nf nf' r P Q (do y \<leftarrow> f; g y \<sqinter> h y od) rh"
  apply (simp add:alternative_distrib2)
  apply (erule corres_alternate1)
  done

lemma dcorres_alternate_seq2:
  "corres_underlying t nf nf' r P Q (do y \<leftarrow> f; h y od) rh
    \<Longrightarrow> corres_underlying t nf nf' r P Q (do y \<leftarrow> f; g y \<sqinter> h y od) rh"
  apply (simp add:alternative_distrib2)
  apply (erule corres_alternate2)
  done

lemma dcorres_dummy_set_pending_cap_Restart:
  "dcorres dc \<top> (st_tcb_at ((=) Structures_A.thread_state.Restart) thread and not_idle_thread thread and valid_etcbs)
  (KHeap_D.set_cap (thread, tcb_pending_op_slot) RestartCap) (return ())"
  apply (simp add:KHeap_D.set_cap_def gets_the_def gets_def bind_assoc)
  apply (rule dcorres_absorb_get_l)
  apply (clarsimp simp:st_tcb_at_def obj_at_def dest!:get_tcb_rev)
  apply (frule(1) valid_etcbs_get_tcb_get_etcb, clarsimp)
  apply (frule opt_object_tcb, simp)
   apply (simp add:not_idle_thread_def)
  apply (clarsimp simp:assert_opt_def update_slots_def
    transform_tcb_def has_slots_def object_slots_def)
  apply (simp add:KHeap_D.set_object_def simpler_modify_def)
  apply (clarsimp simp:corres_underlying_def return_def)
  apply (simp add:transform_def)
  apply (rule ext,clarsimp)
  apply (fastforce dest!: get_tcb_SomeD
    simp add: not_idle_thread_def
    transform_objects_def transform_tcb_def
    infer_tcb_pending_op_def runnable_def tcb_slots
    split : Structures_A.thread_state.splits)
  done

crunch pred_tcb[wp]: do_ipc_transfer "pred_tcb_at proj P t"
  (wp: crunch_wps transfer_caps_loop_pres make_fault_message_inv simp: zipWithM_x_mapM)

lemma dcorres_get_thread_state:
  "dcorres (\<lambda>op ts. op = infer_tcb_pending_op t ts)
     \<top>
     (valid_etcbs and tcb_at t and not_idle_thread t)
     (do tcb <- get_thread t; return (the (cdl_tcb_caps tcb tcb_pending_op_slot)) od)
     (get_thread_state t)"
  text \<open>Brute force proof. Trying to reuse @{thm thread_get_corres} doesn't
        seem to work, because it expects to have concrete tcbs\<close>
  apply (simp add: get_thread_state_def)
  apply (monad_eq simp: corres_underlying_def Bex_def
                        get_thread_def
                        thread_get_def get_tcb_def
                   split: option.splits)
  apply (rename_tac s ko tcb)
  apply (case_tac ko; clarsimp)
  text \<open>These two existential vars refer to the same transformed tcb.
        We skip the first one and instantiate the second first\<close>
  apply (rule exI)
  apply (rule conjI)
   apply (rule_tac x="transform_tcb (machine_state s) t tcb (the (get_etcb t s))" in exI)
   apply (monad_eq simp: transform_tcb_def)
   apply (rule conjI)
    apply (fastforce simp: get_etcb_def cdl_objects_tcb not_idle_thread_def
                     dest: valid_etcbs_tcb_etcb)
   apply (rule refl)
  apply (clarsimp simp: infer_tcb_pending_op_def tcb_slot_defs)
  done

lemma send_sync_ipc_corres:
  "\<lbrakk>ep_id = epptr;tcb_id_sender= thread\<rbrakk> \<Longrightarrow>
    dcorres dc
     \<top>
  (not_idle_thread thread and (\<lambda>s. not_idle_thread (cur_thread s) s)
      and st_tcb_at active thread
      and valid_state and valid_etcbs)
     (Endpoint_D.send_ipc block call badge can_grant can_grant_reply tcb_id_sender ep_id)
     (Ipc_A.send_ipc block call badge can_grant can_grant_reply thread epptr)"
  apply (clarsimp simp:gets_def Endpoint_D.send_ipc_def Ipc_A.send_ipc_def
                  split del:if_split)
  apply (rule dcorres_absorb_get_l)
  apply (clarsimp split del:if_split)
  apply (rule_tac Q' = "\<lambda>r. (=) s' and ko_at (kernel_object.Endpoint r) epptr" in corres_symb_exec_r[rotated])
     apply (wp get_simple_ko_ko_at |simp split del:if_split)+
  apply (rule dcorres_expand_pfx)
  apply (clarsimp split del:if_split)
  apply (frule_tac get_endpoint_pick)
   apply (simp add:obj_at_def)
  apply (case_tac rv)
    apply (clarsimp split del:if_split)
    apply (subst ep_waiting_set_recv_lift)
     apply (simp add:valid_state_def)
     apply simp
    apply (clarsimp simp:valid_ep_abstract_def none_is_receiving_ep_def option_select_def)
    apply (rule corres_dummy_return_l)
    apply (rule corres_guard_imp)
      apply (rule corres_split[OF set_thread_state_block_on_send_corres corres_dummy_set_sync_ep])
       apply wp
     apply simp
    apply (wp TrueI |clarsimp simp: split del:if_split)+
(* SendEP *)
   apply (subst ep_waiting_set_recv_lift)
    apply (simp add:valid_state_def)
    apply simp
    apply (clarsimp simp:valid_ep_abstract_def none_is_receiving_ep_def option_select_def)
    apply (rule corres_dummy_return_l)
    apply (rule corres_guard_imp)
      apply (rule corres_split[OF set_thread_state_block_on_send_corres corres_dummy_set_sync_ep])
       apply wp
     apply simp
    apply (wp TrueI|clarsimp simp: split del:if_split)+
(* RecvEP *)
  apply (subst ep_waiting_set_recv_lift,simp add:valid_state_def)
  apply simp
  apply (clarsimp simp:valid_ep_abstract_def split del:if_split)
  apply (subst option_select_not_empty)
   apply (clarsimp simp: dest!: not_empty_list_not_empty_set)
  apply (rename_tac list)
  apply (drule_tac s = "set list" in sym)
  apply (clarsimp simp: bind_assoc neq_Nil_conv split del:if_split)
  apply (rule_tac P1="\<top>" and P'="(=) s'" and x1 = y
         in dcorres_absorb_pfx[OF select_pick_corres[OF dcorres_expand_pfx]])
      defer
      apply (simp+)[3]
  apply (simp split del:if_split)
  apply (drule_tac x1 = y in iffD2[OF eqset_imp_iff], simp)
  apply (clarsimp simp:obj_at_def dc_def[symmetric] split del:if_split)
  apply (subst when_def)+
  apply (rule corres_guard_imp)
    apply (rule dcorres_symb_exec_r)
      apply (simp only: liftM_def)
      apply (rule corres_split[OF dcorres_get_thread_state])
        apply (clarsimp, rename_tac recv_state')
        apply (case_tac recv_state'; simp add: corres_free_fail split del: if_split)
        apply (rule corres_split)
           apply (rule corres_complete_ipc_transfer; simp)
          apply (rule corres_split[OF set_thread_state_corres])
            apply (rule dcorres_rhs_noop_above[OF possible_switch_to_dcorres])
              apply (rule dcorres_if_rhs)
               apply (rule dcorres_if_rhs)
                apply (clarsimp simp only: if_True)
                apply (rule corres_alternate1)+
                apply (rule corres_setup_caller_cap)
                apply (clarsimp simp:ep_waiting_set_recv_def pred_tcb_at_def obj_at_def generates_pending_def)
               apply (rule corres_alternate1[OF corres_alternate2])
               apply (rule set_thread_state_corres)
              apply (rule corres_alternate2)
              apply (rule corres_return_trivial)
             apply wp
            apply (rule_tac Q="\<lambda>r. valid_mdb and valid_idle and valid_objs
                          and not_idle_thread thread and not_idle_thread y and tcb_at thread and tcb_at y
                          and st_tcb_at runnable thread and valid_etcbs"
                          in hoare_strengthen_post[rotated])
             apply (clarsimp simp:pred_tcb_at_def obj_at_def,
                    simp split:Structures_A.thread_state.splits, fastforce)
            apply ((wp sts_st_tcb_at' sts_st_tcb_at_neq |clarsimp simp add:not_idle_thread_def)+)
        apply (wp hoare_vcg_conj_lift)
         apply (rule hoare_disjI1)
         apply (wp do_ipc_transfer_pred_tcb | wpc | simp)+
     apply (clarsimp simp:conj_comms not_idle_thread_def)
     apply (wp | wps)+
    apply (simp add:not_idle_thread_def)
    apply (clarsimp simp:ep_waiting_set_recv_def obj_at_def st_tcb_at_def)+
    apply (frule_tac a = "y" and list = "y # ys" in pending_thread_in_recv_not_idle)
       apply (simp add:valid_state_def)
      apply (fastforce simp:obj_at_def)
     apply (simp add:insertI1 not_idle_thread_def)+
    apply (rule dcorres_to_wp[where Q=\<top> ,simplified])
    apply (rule corres_dummy_set_sync_ep)
   apply simp
  apply (clarsimp simp:valid_state_def not_idle_thread_def
                       valid_pspace_def st_tcb_at_def obj_at_def is_ep_def)
  apply (drule(1) valid_objs_valid_ep_simp)
  apply (clarsimp simp:valid_ep_def tcb_at_def
    valid_idle_def pred_tcb_at_def obj_at_def
    dest!:get_tcb_SomeD
    split:Structures_A.endpoint.splits list.splits)
  apply (clarsimp simp:ep_waiting_set_recv_def runnable_eq_active)
  apply (intro conjI impI)
    apply clarsimp+
  apply fastforce
  done

lemma not_idle_thread_resolve_address_bits:
  "\<lbrace>valid_global_refs and valid_objs and valid_idle and valid_irq_node and ko_at (TCB obj) thread\<rbrace>
    CSpace_A.resolve_address_bits (tcb_ctable obj, blist)
            \<lbrace>\<lambda>rv. not_idle_thread (fst (fst rv))\<rbrace>, \<lbrace>\<lambda>_. \<top>\<rbrace>"
  apply (rule validE_R_validE)
  apply (rule_tac hoare_vcg_precond_impE_R)
   apply (rule validE_validE_R)
   apply (rule_tac Q="\<lambda>r. valid_global_refs and valid_objs and valid_idle and valid_irq_node and ex_cte_cap_to (fst r)"
    in hoare_post_impErr[where E="\<lambda>x y. True"])
     apply (wp rab_cte_cap_to)
    apply clarsimp
    apply (drule ex_cte_cap_to_not_idle, auto simp: not_idle_thread_def)[1]
   apply (rule TrueI)
  apply (clarsimp simp:ex_cte_cap_to_def)
  apply (rule_tac x = thread in exI,rule_tac x = "tcb_cnode_index 0" in exI)
  apply (clarsimp simp:cte_wp_at_cases obj_at_def is_cap_simps)
  done

lemma tcb_fault_update_valid_state[wp]:
  "\<lbrace>invs and (\<lambda>_. valid_fault ft')\<rbrace>
   thread_set (tcb_fault_update (\<lambda>_. Some ft')) thread
   \<lbrace>\<lambda>rv. valid_state\<rbrace>"
  apply (cases "valid_fault ft'"; simp)
  apply (strengthen invs_valid_stateI, wp thread_set_tcb_fault_set_invs)
  done

lemma thread_set_fault_obj_at:
 "\<lbrace>tcb_at thread\<rbrace> thread_set (tcb_fault_update (\<lambda>_. Some ft')) thread
  \<lbrace>\<lambda>rv s. obj_at (\<lambda>ko. \<exists>tcb. ko = TCB tcb \<and> (False \<or> (\<exists>y. tcb_fault tcb = Some y)) = True) thread s\<rbrace>"
  apply (simp add: thread_set_def)
  apply (wpsimp wp: set_object_wp simp: obj_at_def)
  done

lemma thread_set_fault_st_tcb_at:
  "\<lbrace>st_tcb_at P  a\<rbrace> thread_set (tcb_fault_update (\<lambda>_. Some ft')) thread
            \<lbrace>\<lambda>rv. st_tcb_at P a\<rbrace>"
  apply (clarsimp simp: thread_set_def)
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: st_tcb_at_def obj_at_def
                 dest!: get_tcb_SomeD
                 split: if_splits)
  done

lemma tcb_fault_handler_length:
  "\<lbrakk>valid_state s;ko_at (TCB tcb) thread s\<rbrakk>
           \<Longrightarrow> length (tcb_fault_handler tcb) = word_bits"
  apply (clarsimp simp:valid_state_def valid_pspace_def)
  apply (drule valid_tcb_objs)
    apply (simp add:obj_at_def,erule get_tcb_rev)
  apply (simp add:valid_tcb_def word_bits_def)
  done



lemma send_fault_ipc_corres_conj_helper:
  "\<lbrakk> \<lbrace> P \<rbrace> f \<lbrace> \<lambda>_. E \<rbrace>; \<lbrace> P \<rbrace> f \<lbrace> \<lambda>_ s. A s \<and> B s \<and> C s \<and> D s \<rbrace>   \<rbrakk> \<Longrightarrow> \<lbrace> P \<rbrace> f \<lbrace> \<lambda>_ s. A s \<and> B s \<and> C s \<and> D s \<and> E s \<rbrace>"
  apply (subst conj_assoc[symmetric])
  apply (subst conj_assoc[symmetric])
  apply (subst conj_assoc[symmetric])
  apply (rule hoare_conjI[rotated])
  apply (wp | simp)+
  done



lemma set_object_valid_etcbs_2:
  "\<lbrace>\<lambda>s. valid_etcbs_2 a (kheap s) \<and>  kheap s ptr = Some (TCB tcba)\<rbrace> KHeap_A.set_object ptr (TCB tcbb) \<lbrace>\<lambda>rv s. valid_etcbs_2 a (kheap s)\<rbrace>"
  apply (wpsimp wp: set_object_wp)
  apply (fastforce simp: valid_etcbs_def st_tcb_at_def obj_at_def is_etcb_at_def st_tcb_at_kh_def obj_at_kh_def)
  done

lemma valid_etcbs_2_lift:
  assumes a: "\<And>P T t. \<lbrace>\<lambda>s. P (typ_at T t s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T t s)\<rbrace>"
    shows "\<lbrace>\<lambda>s. valid_etcbs_2 ekh (kheap s)\<rbrace> f \<lbrace>\<lambda>rv s. valid_etcbs_2 ekh (kheap s)\<rbrace>"
  apply (simp add: valid_etcbs_def)
  apply (simp add: tcb_at_st_tcb_at[symmetric] tcb_at_typ)
  apply (wp hoare_vcg_all_lift a)
  done

lemma thread_set_valid_etcbs_2:
  "\<lbrace>\<lambda>s. valid_etcbs_2 a (kheap s)\<rbrace> thread_set ref ts \<lbrace>\<lambda>_ s. valid_etcbs_2 a (kheap s) \<rbrace>"
  by (wp hoare_drop_imps valid_etcbs_2_lift | simp add: thread_set_def)+

lemmas [simp] = AllowSend_def AllowRecv_def CanModify_def

lemma send_fault_ipc_corres:
  "did = thread \<Longrightarrow>
   dcorres (dc\<oplus>dc) \<top>
     (not_idle_thread thread and st_tcb_at active thread and valid_irq_node and
      invs and ko_at (TCB tcb) thread and (\<lambda>s. ekheap  s thread = Some etcb) and
      (\<lambda>s. not_idle_thread (cur_thread s) s) and (\<lambda>_. valid_fault ft') and valid_etcbs)
     (Endpoint_D.send_fault_ipc did) (Ipc_A.send_fault_ipc thread ft')"
  apply (simp add:Endpoint_D.send_fault_ipc_def Ipc_A.send_fault_ipc_def)
  apply (rule dcorres_expand_pfx)
  apply (rule corres_guard_imp)
    apply (rule_tac P'="(=) s'" in thread_get_corresE[where tcb' = tcb and etcb'=etcb])
     apply simp_all
   prefer 2
   apply (rule conjI)
    apply (simp add:transform_tcb_def)
   apply (simp add: get_etcb_def)
  apply (rule corres_guard_imp)
    apply (rule_tac R' ="\<lambda>rv s. (\<forall>ref badge rights.
                       rv = cap.EndpointCap ref badge rights \<longrightarrow> (ep_at ref s))
      \<and> not_idle_thread (cur_thread s) s
      \<and> (st_tcb_at active thread s \<and> invs s) \<and> ko_at (TCB tcb) thread s \<and> valid_etcbs s
      \<and> not_idle_thread thread s" and R= "\<lambda>r. \<top>"
      in corres_splitEE[where r'="\<lambda>x y. x = transform_cap y"])
       apply (clarsimp simp: cap_fault_injection)
       apply (rule dcorres_injection_handler_rhs)
       apply (rule lookup_cap_corres)
        apply simp
       apply (simp add: tcb_fault_handler_length[OF invs_valid_stateI])
      apply (simp add: Let_def cap_fault_injection)
      apply (rule dcorres_expand_pfx)
      apply (clarsimp split:cap.splits arch_cap.splits simp:transform_cap_def)
      apply (clarsimp | rule conjI)+
        apply (rule corres_guard_imp)
          apply (rule corres_split[where r'="dc"])
             apply (rule thread_set_fault_corres,simp)
            apply clarsimp
            apply (rule send_sync_ipc_corres)
             apply simp+
          apply (simp add:not_idle_thread_def)
          apply wp
          apply (wps)
          apply (strengthen invs_valid_stateI)
          apply (wp abs_typ_at_lifts[OF thread_set_typ_at]
                    thread_set_fault_obj_at thread_set_fault_st_tcb_at thread_set_valid_etcbs_2
                    thread_set_tcb_fault_set_invs)+
         apply ((simp add: ko_at_tcb_at not_idle_thread_def)+)
       apply (clarsimp simp add: st_tcb_at_def invs_def)
      apply clarsimp
     apply wp+
    apply (rule validE_validE_R)
    apply (rule hoare_validE_conj)
     prefer 2
     apply wp+
     apply (rule hoare_post_imp_R, rule lookup_cap_valid)
     apply (clarsimp simp: valid_cap_simps)
    apply clarsimp+
  apply (intro conjI; clarsimp)
  done

end

end
