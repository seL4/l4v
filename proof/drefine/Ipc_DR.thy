(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory Ipc_DR
imports CNode_DR
begin

declare option.weak_case_cong[cong]

abbreviation
"thread_is_running y s \<equiv> st_tcb_at (op=Structures_A.thread_state.Running) y s"

lemmas [wp] = abs_typ_at_lifts[OF set_async_ep_typ_at]

lemma set_object_cur_thread_idle_thread:
  "\<lbrace>\<lambda>s. P (cur_thread s) (idle_thread s)\<rbrace> KHeap_A.set_object word x
         \<lbrace>\<lambda>yb s. P (cur_thread s) (idle_thread s)\<rbrace>"
  by (fastforce simp:set_object_def valid_def get_def put_def return_def bind_def)

lemma set_thread_state_cur_thread_idle_thread:
  "\<lbrace>\<lambda>s. P (cur_thread s) (idle_thread s) \<rbrace> set_thread_state thread x \<lbrace>\<lambda>rv s. P (cur_thread s)  (idle_thread s)\<rbrace>"
  apply (simp add:set_thread_state_def)
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
  apply (clarsimp simp:as_user_def)
  apply (wp set_object_cur_thread_idle_thread)+
  apply (fastforce simp:set_object_def valid_def get_def put_def return_def bind_def)
  apply (simp add:select_f_def)
  apply (simp add:valid_def)
  apply (auto|wp)+
done


lemma do_fault_transfer_cur_thread_idle_thread:
  "\<lbrace>\<lambda>s. P (cur_thread s) (idle_thread s)\<rbrace> do_fault_transfer c a e recv_buffer \<lbrace>\<lambda>rv s. P (cur_thread s) (idle_thread s)\<rbrace>"
  apply (simp add:do_fault_transfer_def set_message_info_def)
  apply (wp as_user_cur_thread_idle_thread |wpc|clarsimp)+
  apply (wps | wp transfer_caps_it copy_mrs_it | simp)+
  apply wpc
  apply (wp | simp add:thread_get_def)+
done

lemma do_normal_transfer_cur_thread_idle_thread:
  "\<lbrace>\<lambda>s. P (cur_thread s) (idle_thread s) \<rbrace> Ipc_A.do_normal_transfer a b c d e f g h\<lbrace>\<lambda>rv s. P (cur_thread s)  (idle_thread s)\<rbrace>"
  apply (simp add:do_normal_transfer_def set_message_info_def)
  apply (wp as_user_cur_thread_idle_thread |wpc|clarsimp)+
  apply (wps | wp transfer_caps_it copy_mrs_it)+
  apply clarsimp
done

lemma do_ipc_transfer_cur_thread_idle_thread:
  "\<lbrace>\<lambda>s. P (cur_thread s) (idle_thread s) \<rbrace> Ipc_A.do_ipc_transfer a b c d e f\<lbrace>\<lambda>rv s. P (cur_thread s)  (idle_thread s)\<rbrace>"
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
              apply (wp do_ipc_transfer_cur_thread_idle_thread dxo_wp_weak)
                    apply (clarsimp simp: trans_state_def)
                   apply (case_tac xf)
                   apply (simp | wp set_thread_state_cur_thread_idle_thread
                                    thread_set_cur_thread_idle_thread)+
                 apply ((wps | wp handle_fault_reply_it)+)[1]
                apply wp
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
  and     rl:   "\<And>buf rights sz mapdata. \<lbrakk> cap = cap.ArchObjectCap (arch_cap.PageCap buf rights sz mapdata)\<rbrakk> \<Longrightarrow> R"
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
  "\<lbrakk> \<lbrace>op = s\<rbrace> f \<lbrace>\<lambda>rv _. P rv\<rbrace>; det f \<rbrakk> \<Longrightarrow> P (the (evalMonad f s))"
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
         \<Longrightarrow> \<lbrace>op = s\<rbrace> PageTableUnmap_D.fast_finalise obj (PageTableUnmap_D.is_final_cap' obj s) \<lbrace>\<lambda>x. op = s\<rbrace>"
  by (clarsimp simp:is_pending_cap_def split:cdl_cap.splits)

lemma cte_at_into_opt_cap:
  "cte_at p s = (\<exists>cap. cte_wp_at (op = cap) p s
        \<and> (fst p \<noteq> idle_thread s \<and> valid_etcbs s \<longrightarrow> opt_cap (transform_cslot_ptr p) (transform s) = Some (transform_cap cap)))"
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (safe, simp_all)
  apply (clarsimp simp: caps_of_state_transform_opt_cap)
  done


abbreviation
  "meqv \<equiv> monadic_rewrite False True"

lemma monadic_rewrite_exists:
  "(\<And>v. monadic_rewrite F E (Q v) m m') \<Longrightarrow> monadic_rewrite F E ((\<lambda>s. \<forall>v. P v s \<longrightarrow> Q v s) and (\<lambda>s. \<exists>v. P v s)) m m'"
  by (auto simp: monadic_rewrite_def)

lemma monadic_rewrite_gets_the_bind:
  assumes mr: "(\<And>v. monadic_rewrite F E (Q v) (g v) m)"
  shows   "monadic_rewrite F E (\<lambda>s. f s \<noteq> None \<and> Q (the (f s)) s) (gets_the f >>= (\<lambda>x. g x)) m"
  apply (rule monadic_rewrite_imp)
  apply (rule monadic_rewrite_exists [where P = "\<lambda>v s. f s = Some v"])
   apply (subst return_bind [symmetric, where f = "\<lambda>_. m"])
   apply (rule monadic_rewrite_bind)
     apply (rule_tac v = v in monadic_rewrite_gets_the_known_v)
    apply (rule mr)
   apply wp
  apply clarsimp
  done

lemma mr_opt_cap_into_object:
  assumes mr: "\<And>obj. monadic_rewrite F E (Q obj) m m'"
  shows   "monadic_rewrite F E ((\<lambda>s. \<forall>obj. opt_object (fst p) s = Some obj \<and> object_slots obj (snd p) \<noteq> None \<longrightarrow> Q obj s) and (\<lambda>s. opt_cap p s \<noteq> None)) m m'"
  apply (rule monadic_rewrite_imp)
  apply (rule monadic_rewrite_exists [where P = "\<lambda>obj s. opt_object (fst p) s = Some obj \<and> object_slots obj (snd p) \<noteq> None", OF mr])
  apply clarsimp
  apply (rule conjI)
  apply simp
  apply (simp add: opt_cap_def split_def KHeap_D.slots_of_def split: option.splits)
  done

lemma monadic_rewrite_assert2:
  "\<lbrakk> Q \<Longrightarrow> monadic_rewrite F E P (f ()) g \<rbrakk>
      \<Longrightarrow> monadic_rewrite F E ((\<lambda>s. Q \<longrightarrow> P s) and (\<lambda>_. Q)) (assert Q >>= f) g"
  apply (simp add: assert_def split: split_if)
  apply (simp add: monadic_rewrite_def fail_def)
  done

lemma object_slots_has_slots [simp]:
  "object_slots obj p = Some v \<Longrightarrow> has_slots obj"
  unfolding object_slots_def has_slots_def
  by (simp split: cdl_object.splits)

lemma opt_object_cdl_cdt_update [simp]:
  "opt_object p (cdl_cdt_update f s) = opt_object p s"
  unfolding opt_object_def by simp

lemma meqv_sym:
  "meqv P a a' \<Longrightarrow> meqv P a' a"
  unfolding monadic_rewrite_def
  by fastforce

lemma monadic_rewrite_modify_remove_stateful:
  assumes "\<And>v. meqv (P v) m (modify (\<lambda>s. f v s))"
  shows   "meqv (\<lambda>s. P (g s) s) m (modify (\<lambda>s. f (g s) s))"
  using assms unfolding monadic_rewrite_def
  by (clarsimp simp: modify_def put_def get_def bind_def)


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

lemma corres_name_pre:
  "\<lbrakk> \<And>s s'. \<lbrakk> P s; P' s'; (s, s') \<in> sr \<rbrakk>
                 \<Longrightarrow> corres_underlying sr nf r (op = s) (op = s') f g \<rbrakk>
        \<Longrightarrow> corres_underlying sr nf r P P' f g"
  apply (simp add: corres_underlying_def split_def
                   Ball_def)
  apply blast
  done

lemma corres_guard_from_wp_r:
  assumes ac: "corres_underlying sr False r G G' a c"
  and     rl: "\<lbrace>\<lambda>s. \<not> P s\<rbrace> c \<lbrace>\<lambda>_ _. False\<rbrace>"
  shows "corres_underlying sr False r G (\<lambda>s. P s \<longrightarrow> G' s) a c"
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
  assumes ac: "corres_underlying sr False r G G' a (c >>= d)"
  and     rl: "\<lbrace>\<lambda>s. \<not> P s\<rbrace> c \<lbrace>\<lambda>_ _. False\<rbrace>"
  shows "corres_underlying sr False r G (\<lambda>s. P s \<longrightarrow> G' s) a (c >>= d)"
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
             (PendingSyncSendCap epptr badge call can_grant
               False))
           (set_thread_state thread
             (Structures_A.thread_state.BlockedOnSend epptr
               \<lparr>sender_badge = badge, sender_can_grant = can_grant,
                  sender_is_call = call\<rparr>))"
  apply (clarsimp simp:KHeap_D.set_cap_def set_thread_state_def)
  apply (rule dcorres_gets_the, clarsimp)
   apply (rule dcorres_rhs_noop_below_True[OF set_thread_state_ext_dcorres])
   apply (frule(1) valid_etcbs_get_tcb_get_etcb, clarsimp)
   apply (clarsimp simp: obj_at_def not_idle_thread_def opt_object_tcb assert_def
       transform_tcb_def has_slots_def split: option.splits)
   apply (clarsimp simp:update_slots_def object_slots_def)
   apply (clarsimp simp:set_object_def simpler_modify_def KHeap_D.set_object_def
                        get_def put_def bind_def corres_underlying_def return_def)
   apply (clarsimp simp:transform_def transform_objects_def transform_current_thread_def)
   apply (rule ext)
   apply (clarsimp simp: |rule conjI)+
    apply (clarsimp dest!:get_tcb_SomeD get_etcb_SomeD simp:transform_tcb_def infer_tcb_pending_op_def)
   apply (clarsimp simp:restrict_map_def map_add_def)
  apply (clarsimp, frule(1) valid_etcbs_get_tcb_get_etcb)
  apply (fastforce simp:not_idle_thread_def dest!:opt_object_tcb)
  done

lemma block_thread_on_recv_corres:
  "dcorres dc \<top> (not_idle_thread thread and valid_etcbs)
             (KHeap_D.set_cap (thread, tcb_pending_op_slot)
               (PendingSyncRecvCap epptr False))
             (set_thread_state thread (Structures_A.thread_state.BlockedOnReceive epptr x))"
  apply (clarsimp simp:KHeap_D.set_cap_def set_thread_state_def)
  apply (rule dcorres_gets_the, clarsimp)
   apply (rule dcorres_rhs_noop_below_True[OF set_thread_state_ext_dcorres])
   apply (frule(1) valid_etcbs_get_tcb_get_etcb, clarsimp)
   apply (clarsimp simp:not_idle_thread_def opt_object_tcb assert_def
                        transform_tcb_def has_slots_def)
   apply (clarsimp simp:update_slots_def object_slots_def)
   apply (clarsimp simp:set_object_def simpler_modify_def KHeap_D.set_object_def
                        get_def put_def bind_def corres_underlying_def return_def)
   apply (clarsimp simp:transform_def transform_objects_def transform_current_thread_def)
   apply (rule ext)
   apply (clarsimp simp: get_etcb_def|rule conjI)+
    apply (clarsimp simp:transform_tcb_def infer_tcb_pending_op_def)
   apply (clarsimp simp:restrict_map_def map_add_def)
  apply (clarsimp, frule(1) valid_etcbs_get_tcb_get_etcb)
  apply (fastforce simp:not_idle_thread_def dest!:opt_object_tcb)
done

lemma block_thread_on_async_recv_corres:
  "dcorres dc \<top> (not_idle_thread thread and valid_etcbs)
             (KHeap_D.set_cap (thread, tcb_pending_op_slot)
               (PendingAsyncRecvCap w))
             (set_thread_state thread (Structures_A.thread_state.BlockedOnAsyncEvent w))"
  apply (clarsimp simp:KHeap_D.set_cap_def set_thread_state_def)
  apply (rule dcorres_gets_the, clarsimp)
   apply (rule dcorres_rhs_noop_below_True[OF set_thread_state_ext_dcorres])
   apply (frule(1) valid_etcbs_get_tcb_get_etcb, clarsimp)
   apply (clarsimp simp:not_idle_thread_def opt_object_tcb assert_def
                        transform_tcb_def has_slots_def)
   apply (clarsimp simp:update_slots_def object_slots_def)
   apply (clarsimp simp:set_object_def simpler_modify_def KHeap_D.set_object_def
                        get_def put_def bind_def corres_underlying_def return_def)
   apply (clarsimp simp:transform_def transform_objects_def transform_current_thread_def)
   apply (rule ext)
   apply (clarsimp simp: get_etcb_def|rule conjI)+
    apply (clarsimp simp:transform_tcb_def infer_tcb_pending_op_def)
   apply (clarsimp simp:restrict_map_def map_add_def)
  apply (clarsimp, frule(1) valid_etcbs_get_tcb_get_etcb)
  apply (fastforce simp:not_idle_thread_def dest!:opt_object_tcb)
done

lemma corres_ignore_ret_lhs: "dcorres rv P P' (do f;g od) f' \<Longrightarrow> dcorres rv P P' (do a\<leftarrow>f;g od) f'"
 by (clarsimp simp:corres_underlying_def)

lemma dcorres_do_async_transfer:
  "dcorres dc \<top>
    (valid_objs and pspace_aligned and pspace_distinct and valid_idle and tcb_at oid and not_idle_thread oid and valid_etcbs)
    (corrupt_ipc_buffer oid True)  (Ipc_A.do_async_transfer badge msg oid)"
  apply (simp add:do_async_transfer_def)
  apply (clarsimp simp:corrupt_ipc_buffer_def)
  apply (rule dcorres_expand_pfx)
  apply (rule_tac Q' = "\<lambda>r. op = s' and K_bind (evalMonad (lookup_ipc_buffer True oid) s' = Some r)"
      in corres_symb_exec_r)
  apply (rule dcorres_expand_pfx)
  apply (clarsimp)
  apply (frule(1) tcb_at_is_etcb_at)
  apply (case_tac rv)
    apply (rule corres_symb_exec_l)
    apply (rule_tac F="rva = None" in corres_gen_asm)
      apply clarsimp
      apply (rule corres_guard_imp)
        apply (rule corres_corrupt_tcb_intent_dupl)
        apply (rule corres_split[OF _ set_mrs_corres_no_recv_buffer])
          unfolding K_bind_def
          apply (rule corres_corrupt_tcb_intent_dupl)
          apply (rule corres_split[OF _ set_register_corres])
            unfolding K_bind_def
          apply (rule set_message_info_corres)
      apply (wp | clarsimp simp:not_idle_thread_def)+
    apply (simp add:gets_the_def gets_def bind_assoc get_def split_def get_ipc_buffer_def tcb_at_def
      exs_valid_def fail_def return_def bind_def assert_opt_def split:cdl_cap.splits)
    apply (rule_tac x = "(?a,?b)" in bexI)
    apply (rule conjI|fastforce simp:fail_def return_def split:option.splits)+
    apply (clarsimp split:option.splits simp:fail_def | rule conjI)+
      apply (subst opt_cap_tcb)
      apply (simp add:return_def is_etcb_at_def get_etcb_def)+
      apply clarsimp
      apply (drule_tac y = "Some a" in arg_cong[where f  = the])
      apply simp
      apply (wp cdl_get_ipc_buffer_None | simp)+
    apply clarsimp
    apply (drule lookup_ipc_buffer_SomeB_evalMonad)
    apply clarsimp
    apply (rule corres_symb_exec_l)
      apply (rule_tac F = "rv = Some b" in corres_gen_asm)
      apply (clarsimp split:option.splits)
      apply (rule corrupt_frame_include_self'[where y = oid])
        apply (rule corres_guard_imp)
          apply (rule corres_split[OF _ dcorres_set_mrs])
          unfolding K_bind_def
          apply (rule_tac corres_corrupt_tcb_intent_dupl)
              apply (rule corres_split[OF _ set_register_corres])
              unfolding K_bind_def
                apply (rule set_message_info_corres)
              apply (wp|clarsimp simp:not_idle_thread_def)+
      apply (clarsimp simp:cte_wp_at_cases obj_at_def)
      apply (drule sym)
      apply (clarsimp simp:invs_def not_idle_thread_def valid_state_def valid_pspace_def
        ipc_frame_wp_at_def ipc_buffer_wp_at_def obj_at_def)
      apply (clarsimp simp:cte_wp_at_cases obj_at_def)
      apply (drule sym)
      apply (clarsimp simp:ipc_frame_wp_at_def obj_at_def)
    apply (clarsimp simp:get_ipc_buffer_def gets_the_def gets_def get_def fail_def tcb_at_def
      bind_def return_def assert_opt_def exs_valid_def split:option.splits cdl_cap.splits)
    apply (rule exI)
    apply (subst opt_cap_tcb)
      apply (simp add:not_idle_thread_def is_etcb_at_def get_etcb_def)+
    apply (rule cdl_get_ipc_buffer_Some)
      apply fastforce
      apply (simp add:tcb_at_def not_idle_thread_def get_tcb_rev)+
    apply wp
    apply (rule evalMonad_wp)
      apply (simp add:empty_when_fail_lookup_ipc_buffer weak_det_spec_lookup_ipc_buffer)+
    apply (wp|clarsimp)+
  done

crunch not_idle[wp]: set_thread_state "not_idle_thread y"
(simp: not_idle_thread_def wp: dxo_wp_weak)

lemma set_scheduler_action_dcorres:
  "dcorres dc P P' (return ()) (set_scheduler_action sa)"
  by (clarsimp simp: set_scheduler_action_def modify_def get_def put_def bind_def return_def  corres_underlying_def)


lemma tcb_sched_action_transform_inv: "\<lbrace>\<lambda>ps. transform ps = cs\<rbrace> tcb_sched_action tcb_sched_enqueue t \<lbrace>\<lambda>r s. transform s = cs\<rbrace>"
  apply (clarsimp simp: tcb_sched_action_def)
  apply (wp | simp)+
  done

lemma possible_switch_to_dcorres:
  "dcorres dc P P' (return ()) (possible_switch_to t on_same_prio)"
 apply (clarsimp simp: possible_switch_to_def)
  apply (rule dcorres_symb_exec_r)
    apply (rule dcorres_symb_exec_r)
      apply (rule dcorres_symb_exec_r)
        apply (rule dcorres_symb_exec_r)
         apply (rule dcorres_symb_exec_r)
            apply (rule dcorres_symb_exec_r)
              apply (case_tac "rvc = rva", simp_all)
              apply (case_tac "on_same_prio", simp_all)
            apply (rule conjI)
             apply (clarsimp, rule set_scheduler_action_dcorres)
            apply (rule conjI)
            apply (clarsimp, rule dcorres_symb_exec_r)
              apply (case_tac "rve", simp_all)
 
             apply (fold dc_def, rule reschedule_required_dcorres)
            apply (wp hoare_TrueI tcb_sched_action_transform_inv)
            apply (clarsimp, rule dcorres_symb_exec_r)
              apply (case_tac "rve", simp_all)
             apply (fold dc_def, rule reschedule_required_dcorres)
            apply (wp hoare_TrueI tcb_sched_action_transform_inv)
           apply (rule conjI)
           apply (clarsimp, rule set_scheduler_action_dcorres)
           apply (rule conjI)
           apply (clarsimp, rule dcorres_symb_exec_r)
           apply (case_tac "rve", simp_all)
           apply (fold dc_def, rule reschedule_required_dcorres)
           apply (wp hoare_TrueI tcb_sched_action_transform_inv)
           apply (clarsimp, rule dcorres_symb_exec_r)
           apply (case_tac "rve", simp_all)
           apply (fold dc_def, rule reschedule_required_dcorres)
           apply (wp hoare_TrueI tcb_sched_action_transform_inv)
          apply (rule tcb_sched_action_dcorres)
  apply (wp | simp)+
  done

lemma switch_if_required_to_dcorres:
  "dcorres dc P P' (return ()) (switch_if_required_to t)"
  apply (clarsimp simp: switch_if_required_to_def)
  apply (rule possible_switch_to_dcorres)
  done

lemma attempt_switch_to_dcorres: "dcorres dc P P' (return ()) (attempt_switch_to y)"
  apply (clarsimp simp: attempt_switch_to_def)
  apply (rule possible_switch_to_dcorres)
  done

lemma corres_update_waiting_aep_do_async_transfer:
  "dcorres dc \<top>
    (pspace_aligned and valid_objs and valid_mdb and pspace_distinct and valid_idle and valid_etcbs and
     (st_tcb_at (op = (Structures_A.thread_state.BlockedOnAsyncEvent epptr)) y) and
     valid_aep (case ys of [] \<Rightarrow> async_ep.IdleAEP | a # list \<Rightarrow> async_ep.WaitingAEP ys))
          (Endpoint_D.do_async_transfer y)
          (update_waiting_aep epptr (y # ys) badge msg)"
   apply (simp add: Endpoint_D.do_async_transfer_def update_waiting_aep_def assert_def)
   apply (rule corres_dummy_return_pl)
   apply (rule corres_split_keep_pfx[where r'="dc" and Q="%x. \<top>" and Q'="%x. \<top>"])
      apply (rule corres_guard_imp,rule corres_dummy_set_async_ep,clarsimp+)
     apply (rule dcorres_expand_pfx)
    apply clarsimp
    apply (frule_tac y = y in  generates_pending_not_idle)
     apply (clarsimp simp:st_tcb_at_def obj_at_def)
     apply (drule_tac t = "tcb_state tcb" in sym)
     apply (simp add:generates_pending_def)
    apply (rule corres_guard_imp)
      apply (rule dcorres_dc_rhs_noop_below_2_True[OF allI[OF switch_if_required_to_dcorres]])
      apply (rule corres_split[OF _ set_thread_state_corres])
        apply (rule dcorres_do_async_transfer)
       apply (wp hoare_TrueI)
     apply simp
    apply (frule generates_pending_not_idle[where y = y])
     apply (clarsimp simp: st_tcb_at_def obj_at_def generates_pending_def)
     apply (drule_tac t = "tcb_state tcb" in sym)
     apply (clarsimp simp:st_tcb_at_def obj_at_def not_idle_thread_def split:Structures_A.thread_state.splits)+
    apply fastforce
   apply simp
  apply (wp set_aep_aligned set_aep_mdb set_aep_valid_objs sts_typ_ats)
        apply (simp_all add:not_idle_thread_def)+
  apply (clarsimp simp: st_tcb_at_def obj_at_def)
  apply (drule valid_tcb_objs,erule get_tcb_rev)
  apply (drule_tac t = "tcb_state tcb" in sym)
  apply (clarsimp simp:valid_tcb_def valid_tcb_state_def obj_at_def)
  done

lemma aep_waiting_set_spec:
  "\<lbrakk>y\<in> aep_waiting_set epptr s\<rbrakk>\<Longrightarrow> st_tcb_at (op = (Structures_A.thread_state.BlockedOnAsyncEvent epptr)) y s"
by (clarsimp simp: aep_waiting_set_def st_tcb_at_def obj_at_def)


lemma not_empty_list_not_empty_set:
  "a \<noteq> [] \<Longrightarrow> \<exists>x. x \<in> (set a)"
  apply (case_tac a)
  apply auto
done


lemma set_thread_state_block_on_async_recv_corres:
    "dcorres dc \<top>
     (not_idle_thread thread and tcb_at thread and valid_etcbs)
     (block_thread_on_ipc thread (PendingAsyncRecvCap w))
     (set_thread_state thread (Structures_A.thread_state.BlockedOnAsyncEvent w))"
   apply (simp add:block_thread_on_ipc_def)
   apply (clarsimp simp:KHeap_D.set_cap_def set_thread_state_def)
     apply (rule dcorres_dc_rhs_noop_below_2_True[OF allI[OF set_thread_state_ext_dcorres]])
     apply (rule dcorres_gets_the)
     apply (clarsimp, frule(1) valid_etcbs_get_tcb_get_etcb, clarsimp)
     apply (clarsimp simp:not_idle_thread_def opt_object_tcb assert_def
       transform_tcb_def has_slots_def)
     apply (clarsimp simp:update_slots_def object_slots_def)
     apply (clarsimp simp:set_object_def simpler_modify_def KHeap_D.set_object_def
       get_def put_def bind_def corres_underlying_def return_def)
     apply (clarsimp simp:transform_def transform_current_thread_def)
     apply (intro ext conjI)
      apply (case_tac x)
       apply (clarsimp simp: |rule conjI)+
         apply (clarsimp simp:transform_tcb_def transform_objects_def infer_tcb_pending_op_def)
       apply ((clarsimp simp:transform_objects_def restrict_map_def map_add_def tcb_at_def transform_tcb_def
                       dest!:get_tcb_SomeD get_etcb_SomeD)+)[2]
       apply (clarsimp, frule(1) valid_etcbs_get_tcb_get_etcb, clarsimp)
  apply (fastforce simp:not_idle_thread_def dest!:opt_object_tcb get_tcb_rev get_etcb_rev)
  done

lemma insert_contr:
  "\<lbrakk>\<forall>x. x \<notin> insert y Q\<rbrakk> \<Longrightarrow> P"
   apply (drule_tac x = y in spec)
   apply (clarsimp simp:insertI1)
done

lemma recv_async_ipc_corres:
  "cap = transform_cap cap' \<Longrightarrow>
  dcorres dc \<top> (invs and not_idle_thread thread and st_tcb_at active thread and valid_etcbs)
             (recv_async_ipc thread cap)
             (receive_async_ipc thread cap')"
  apply (clarsimp simp:receive_async_ipc_def invs_def recv_async_ipc_def corres_free_fail split:cap.splits)
  apply (rule dcorres_expand_pfx)
  apply (rule_tac Q' = "\<lambda>r. op = s' and ko_at (kernel_object.AsyncEndpoint r) word1 and valid_aep r" in corres_symb_exec_r)
    apply (rule dcorres_expand_pfx)
    apply (clarsimp simp:obj_at_def is_aep_def)
    apply (simp add:gets_def bind_assoc option_select_def)
    apply (rule dcorres_absorb_get_l)
    apply (frule get_async_ep_pick,simp)
    apply (case_tac rv)
      apply (clarsimp simp:aep_waiting_set_lift valid_state_def cap_object_simps
        valid_aep_abstract_def none_is_waiting_aep_def)
      apply (rule corres_guard_imp)
        apply (rule corres_alternate1)
        apply (rule corres_dummy_return_l)
        apply (rule corres_split[OF _ set_thread_state_block_on_async_recv_corres])
      apply  (rule corres_dummy_set_async_ep,simp)
      apply (wp|simp)+
      apply (clarsimp simp:st_tcb_at_def tcb_at_def obj_at_def get_tcb_rev)
(* WaitingAEP *)
      apply (clarsimp simp:aep_waiting_set_lift valid_state_def
        valid_aep_abstract_def none_is_waiting_aep_def cap_object_simps)
      apply (rule conjI)
        apply (clarsimp simp:neq_Nil_conv)
      apply clarsimp
      apply (rule corres_guard_imp)
        apply (rule corres_dummy_return_l)
        apply (rule corres_split[OF _ set_thread_state_block_on_async_recv_corres])
      apply  (rule corres_dummy_set_async_ep,simp+)
      apply (fastforce simp:st_tcb_at_def obj_at_def get_tcb_rev)

(* Active AEP list *)
      apply (clarsimp simp:aep_waiting_set_lift valid_state_def
        valid_aep_abstract_def none_is_waiting_aep_def cap_object_simps)
      apply (rule corres_alternate2)
      apply (rule corres_guard_imp )
      apply (rule corres_dummy_return_l)
        apply (rule corres_split[OF corres_dummy_set_async_ep dcorres_do_async_transfer])
      apply (wp|clarsimp)+
      apply (clarsimp simp:valid_pspace_def st_tcb_at_tcb_at)
      apply wp
      apply (rule_tac Q="\<lambda>r. ko_at (kernel_object.AsyncEndpoint r) word1 and valid_state" in hoare_strengthen_post)
        apply (wp get_aep_ko | clarsimp)+
      apply (rule valid_objs_valid_aep_simp)
        apply (clarsimp simp:valid_objs_valid_aep_simp valid_state_def valid_pspace_def)
        apply (simp add:obj_at_def)
    apply (clarsimp|wp)+
done

lemma send_async_ipc_corres:
  "ep_id = epptr \<Longrightarrow> dcorres dc \<top> (invs and valid_etcbs)
     (Endpoint_D.send_async_ipc ep_id)
     (Ipc_A.send_async_ipc epptr badge msg)"
  apply (unfold Endpoint_D.send_async_ipc_def Ipc_A.send_async_ipc_def invs_def)
  apply (rule dcorres_expand_pfx)
  apply (clarsimp simp:get_async_ep_def get_object_def gets_def bind_assoc)
  apply (rule dcorres_absorb_get_r)
  apply (clarsimp simp:assert_def corres_free_fail split:Structures_A.kernel_object.splits)
  apply (rule dcorres_absorb_get_l)
  apply clarsimp
  apply (frule valid_objs_valid_aep_simp[rotated])
    apply (simp add:valid_state_def valid_pspace_def)
  apply (case_tac async_ep)
      apply (simp add:gets_def bind_assoc option_select_def)
      apply (frule get_async_ep_pick,simp)
      apply (clarsimp simp:aep_waiting_set_lift valid_state_def valid_aep_abstract_def none_is_waiting_aep_def)
      apply (rule corres_guard_imp,rule corres_dummy_set_async_ep,simp+)
(* Waiting AEP list *)
      apply (simp add:gets_def bind_assoc option_select_def)
      apply (frule get_async_ep_pick,simp)
      apply (clarsimp simp:aep_waiting_set_lift valid_state_def valid_aep_abstract_def)
      apply (rule conjI)
        apply (clarsimp simp: dest!:not_empty_list_not_empty_set)
      apply (clarsimp simp:neq_Nil_conv)
      apply (rule corres_guard_imp)
        apply (rule select_pick_corres)
          apply (rule corres_update_waiting_aep_do_async_transfer)
          apply (drule_tac s = "insert y (set ys)" in sym)
          apply (clarsimp simp:image_def)
          apply (drule_tac s = "insert y (set ys)" in sym)
        apply (drule_tac x = y in eqset_imp_iff)
        apply (clarsimp simp:valid_pspace_def aep_waiting_set_def)
      apply (clarsimp simp: st_tcb_at_def obj_at_def valid_aep_def split:list.splits)
(* ActiveAEP *)
    apply (clarsimp simp:gets_def bind_assoc option_select_def)
    apply (frule get_async_ep_pick,simp)
    apply (clarsimp simp:aep_waiting_set_lift valid_state_def valid_aep_abstract_def none_is_waiting_aep_def)
    apply (rule corres_guard_imp,rule corres_dummy_set_async_ep,simp+)
done

lemma set_thread_state_block_on_send_corres:
    "dcorres dc \<top>
     (not_idle_thread thread and valid_etcbs)
     (block_thread_on_ipc thread
       (PendingSyncSendCap epptr badge call can_grant False))
     (set_thread_state thread
       (Structures_A.thread_state.BlockedOnSend epptr
         \<lparr>sender_badge = badge, sender_can_grant = can_grant, sender_is_call = call\<rparr>))"
   by (simp add:block_thread_on_ipc_def,rule block_thread_on_send_corres)

lemma set_thread_state_block_on_receive_corres:
  "dcorres dc \<top> (not_idle_thread thread and valid_etcbs)
      (block_thread_on_ipc thread (PendingSyncRecvCap epptr False))
      (set_thread_state thread (Structures_A.thread_state.BlockedOnReceive epptr x))"
   apply (simp add:block_thread_on_ipc_def)
   apply (rule block_thread_on_recv_corres)
   done

lemma corres_setup_caller_cap:
  "sender \<noteq> receiver \<Longrightarrow> dcorres dc \<top>
  (valid_mdb and valid_idle and not_idle_thread sender and not_idle_thread receiver and tcb_at sender and tcb_at receiver
  and st_tcb_at (Not\<circ> halted) sender and valid_objs and valid_etcbs)
           (inject_reply_cap sender receiver)
           (setup_caller_cap sender receiver)"
  apply (rule dcorres_expand_pfx)
  apply (rule corres_guard_imp)
    apply (simp add: inject_reply_cap_def setup_caller_cap_def)
    apply (rule corres_split[OF _ set_thread_state_corres])
      apply (rule reply_cap_insert_corres)
      apply (simp add:not_idle_thread_def)+
    apply (wp set_thread_state_it|simp )+
    apply (rule hoare_vcg_conj_lift)
     apply (clarsimp simp:not_idle_thread_def set_thread_state_def)
     apply wp
      apply (simp add:set_object_def)
      apply wp
   apply simp
  apply (clarsimp simp:not_idle_thread_def tcb_at_def obj_at_def st_tcb_at_def)
  apply (rule conjI|clarsimp simp:is_tcb_def)+
  apply (drule valid_tcb_objs)
    apply (erule get_tcb_rev)
    apply (simp add:valid_tcb_state_def)
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
  assumes wp: "\<And>s l. \<lbrace>op = s\<rbrace> f l \<lbrace>\<lambda>r. op = s\<rbrace>"
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
      apply (clarsimp split:option.splits)
      apply (simp add: Cons)
    done
  qed

lemma evalMonad_get_extra_cptrs:
  "\<lbrakk>evalMonad (lookup_ipc_buffer False thread) s = Some (Some buf);get_tcb thread s = Some tcb;
    (evalMonad (Ipc_A.get_extra_cptrs (Some buf) (data_to_message_info (tcb_context tcb msg_info_register))) s) = Some a
    \<rbrakk>
  \<Longrightarrow> a = (map (to_bl) (cdl_intent_extras $ transform_full_intent (machine_state s) thread tcb))"
  apply (clarsimp simp:get_extra_cptrs_def)
  apply (clarsimp simp:liftM_def)
  apply (subst (asm) evalMonad_compose)
    apply (rule empty_when_fail_mapM)
    apply (simp add:weak_det_spec_load_word_offs empty_when_fail_load_word_offs)
    apply (rule weak_det_spec_mapM)
    apply (simp add:weak_det_spec_load_word_offs)
    apply (wp mapM_wp,fastforce)
  apply (clarsimp split:option.splits)
  apply (rule_tac x = a in arg_cong)
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
assumes wp:"\<And>sa. \<lbrace>op = sa\<rbrace> f \<lbrace>\<lambda>r. op = sa\<rbrace>"
assumes corres:"\<And>rv. evalMonad f s = Some rv \<Longrightarrow> dcorres r P (op = s) h (g rv)"
shows "\<lbrakk>empty_when_fail f;weak_det_spec (op = s) f\<rbrakk> \<Longrightarrow> dcorres r P (op = s) h (f>>=g)"
  apply (rule_tac Q'="\<lambda>r. op = s and K_bind (evalMonad f s = Some r)" in corres_symb_exec_r)
  apply (rule dcorres_expand_pfx)
  using corres
  apply (clarsimp simp:corres_underlying_def)
    apply fastforce
  apply (wp wp,simp,rule evalMonad_wp)
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
                 2 + msg_max_length + n < unat max_ipc_words) and valid_etcbs)
           (corrupt_ipc_buffer rcv in_receive)
           (set_extra_badge rcv_buffer w n)"
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
        apply (simp add:of_nat_add)+
        apply (simp add:obj_at_def cte_wp_at_cases)
        apply (drule_tac t = "tcb_ipcframe obj" in sym)
        apply (fastforce simp:ipc_frame_wp_at_def obj_at_def)
        apply (simp add:obj_at_def cte_wp_at_cases)
        apply (drule_tac t = "tcb_ipcframe obj" in sym)
        apply (fastforce simp:ipc_frame_wp_at_def obj_at_def)
        apply (simp add:ipc_buffer_wp_at_def obj_at_def)
        apply (clarsimp simp:msg_max_length_def max_ipc_words_def buffer_cptr_index_def
          capTransferDataSize_def msgMaxLength_def msgMaxExtraCaps_def msgExtraCapBits_def msg_align_bits)
        apply (simp add:of_nat_mult)
      apply (clarsimp simp:get_ipc_buffer_def gets_the_def exs_valid_def gets_def
        get_def bind_def return_def assert_opt_def fail_def split:option.splits | rule conjI)+
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
  "\<lbrakk> is_ep_cap cap \<or> is_aep_cap cap \<or> is_arch_page_cap cap \<Longrightarrow> R = R' \<rbrakk> \<Longrightarrow>
  transform_cap (cap_rights_update R' cap) = update_cap_rights R (transform_cap cap)"
  by (clarsimp simp: cap_rights_update_def acap_rights_update_def update_cap_rights_def
               split: cap.splits arch_cap.splits)

lemma transform_cap_rights:
  "is_ep_cap cap \<or> is_aep_cap cap \<or> is_arch_page_cap cap
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
  \<Longrightarrow> \<lbrace>cte_wp_at (P and op\<noteq> cap.NullCap) slot\<rbrace> f \<lbrace>\<lambda>r. cte_wp_at P slot\<rbrace>"
assumes tcb_wp:"\<And>P buf t. \<lbrace>ipc_buffer_wp_at buf t\<rbrace> f \<lbrace>\<lambda>r. ipc_buffer_wp_at buf t \<rbrace>"
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
    apply (frule_tac P1 = "op = (cap.ArchObjectCap arch_cap)" in use_valid[OF _ cte_wp])
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
  by (simp add: ipc_buffer_wp_at_def)

lemma ipc_buffer_wp_set_cap[wp]:
  "\<lbrace>ipc_buffer_wp_at buf t\<rbrace> CSpaceAcc_A.set_cap cap' a \<lbrace>\<lambda>ya. ipc_buffer_wp_at buf t\<rbrace>"
  apply (clarsimp simp:set_cap_def split_def)
  apply (simp add:get_object_def gets_def get_def bind_def return_def assert_def fail_def valid_def)
  apply (clarsimp split:Structures_A.kernel_object.splits simp:return_def set_object_def fail_def get_def put_def bind_def)
  apply (rule conjI|clarsimp simp:ipc_buffer_wp_at_def obj_at_def)+
done

lemma ipc_buffer_wp_at_cap_insert_ext[wp]:
  "\<lbrace>ipc_buffer_wp_at buf t \<rbrace> cap_insert_ext src_parent src_slot dest_slot src_p dest_p \<lbrace>\<lambda>r. ipc_buffer_wp_at buf t\<rbrace>"
  apply (simp only:ipc_buffer_wp_at_def)
  by wp

lemma ipc_buffer_wp_at_cap_insert[wp]:
  "\<lbrace>ipc_buffer_wp_at buf t :: det_state \<Rightarrow> bool \<rbrace> cap_insert cap' (slot_ptr, slot_idx) a \<lbrace>\<lambda>r. ipc_buffer_wp_at buf t\<rbrace>"
  apply (simp add:cap_insert_def set_untyped_cap_as_full_def)
  apply (wp|simp split del:split_if)+
           apply (rule_tac Q = "\<lambda>r. ipc_buffer_wp_at buf t" in hoare_strengthen_post)
            apply wp
           apply (clarsimp simp:ipc_buffer_wp_at_def)
          apply (wp get_cap_inv hoare_drop_imp)
  apply simp
  done

lemma cap_insert_weak_cte_wp_at_not_null:
assumes "\<And>c. P c \<Longrightarrow> \<not> is_untyped_cap c"
shows "\<lbrace>cte_wp_at (P and op \<noteq> cap.NullCap) slot :: det_state \<Rightarrow> bool\<rbrace> cap_insert cap' src dest
  \<lbrace>\<lambda>r. cte_wp_at P slot\<rbrace>"
  apply (case_tac "slot = dest")
   apply (clarsimp simp:cap_insert_def)
   apply wp
       apply (rule hoare_pre_cont)
      apply (rule hoare_pre_cont)
     apply (wp get_cap_wp)
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
       | simp split del:split_if)+
  apply (intro conjI impI allI |
    clarsimp simp:cte_wp_at_caps_of_state)+
     apply (drule assms)
     apply (clarsimp simp:masked_as_full_def)
    apply (clarsimp simp:cte_wp_at_caps_of_state)
   apply (clarsimp simp:cte_wp_at_caps_of_state)+
  done

declare cap_object_simps[simp]

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
            2 + msg_max_length + n + length caps' < unat max_ipc_words) and valid_etcbs)
           (Endpoint_D.transfer_caps_loop ep rcv caps dest)
           (Ipc_A.transfer_caps_loop ep' d rcv_buffer n caps' dests mi)"
proof (induct caps' arbitrary: mi n dests dest caps ep ep')
  case Nil thus ?case by clarsimp
next
  case (Cons p caps' mi n dests)
  from Cons.prems
  show ?case
  apply (cases p)
  apply (rename_tac cap slot_ptr slot_idx)
  apply (clarsimp simp: const_on_failure_def split del: split_if)
  apply (case_tac "is_ep_cap cap \<and> ep' = Some (obj_ref_of cap)")
   apply (subgoal_tac "Types_D.is_ep_cap (transform_cap cap) \<and>
                       (\<exists>z. ep' = Some z \<and> z = cap_object (transform_cap cap))")
    prefer 2
    apply (clarsimp simp: is_cap_simps cap_type_simps)
   apply (simp add: catch_liftE_bindE catch_liftE)
   apply (rule corres_guard_imp)
     apply (rule corres_split [where r'=dc])
        apply (rule Cons.hyps, rule refl, rule refl, simp)
       apply (rule dcorres_set_extra_badge,simp)
      apply wp[1]
     apply (simp add: store_word_offs_def set_extra_badge_def
                      not_idle_thread_def ipc_frame_wp_at_def
                      split_def)
     apply (wp evalMonad_lookup_ipc_buffer_wp)
     apply (erule cte_wp_at_weakenE)
     apply (simp add:ipc_buffer_wp_at_def)+
     apply wp
     apply (wp hoare_vcg_ex_lift valid_irq_node_typ hoare_vcg_ball_lift)[3]
     apply simp
   apply (fastforce simp: not_idle_thread_def ipc_frame_wp_at_def ipc_buffer_def)
  apply (subgoal_tac "\<not>(Types_D.is_ep_cap (transform_cap cap) \<and>
                        (\<exists>z. ep' = Some z \<and> z = cap_object (transform_cap cap)))")
   prefer 2
   apply (clarsimp simp: is_cap_simps cap_type_simps split: cdl_cap.splits)
  apply (simp del: de_Morgan_conj split del: split_if)
  apply (case_tac dests)
   apply (simp add: dest_of_def returnOk_liftE catch_liftE)
  apply (case_tac list)
   prefer 2
   apply simp
  apply (simp (no_asm_simp) add: dest_of_def split del: split_if)
  apply (subst bindE_assoc [symmetric])
  apply (rule corres_guard_imp)
    apply (rule corres_split_catch [where f=dc and E="\<top>\<top>" and E'="\<top>\<top>"])
       apply simp
      apply (rule corres_splitEE)
         prefer 2
         apply (subst alternative_bindE_distrib)
         apply (cases d)
          prefer 2
          apply simp
          apply (rule corres_alternate2)
          apply (rule derive_cap_dcorres [where P="\<top>"], simp)
         apply (rule corres_alternate1)
         apply simp
         apply (rule corres_guard_imp)
           apply (rule derive_cap_dcorres [where P="\<top>"])
           apply (unfold remove_rights_def)[1]
           apply (rule update_cap_rights_cong [symmetric])
           apply (simp add: transform_cap_rights)
          apply assumption
         apply (simp add: swp_def)
        apply (rule corres_splitEE)
           prefer 2
           apply (rule corres_whenE, simp)
            apply (rule dcorres_throw)
           apply (rule TrueI)
          apply (simp add: liftE_bindE)
          apply (rule corres_split)
             prefer 2
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
          apply (wp cap_insert_idle valid_irq_node_typ
                    hoare_vcg_ball_lift cap_insert_cte_wp_at)
          apply (rule validE_validE_R)
        apply (wp whenE_throwError_wp)[1]
       apply wp
      apply (clarsimp)
      apply (rule hoareE_TrueI)
     apply (rule validE_R_validE)
     apply (simp add:conj_ac ball_conj_distrib
          split del:if_splits
          del:split_paired_Ex split_paired_All split_paired_Ball split_paired_Bex
          split_paired_all)
     apply (rule_tac Q' ="\<lambda>cap' s. (cap'\<noteq> cap.NullCap \<longrightarrow>(
          (cte_wp_at (is_derived (cdt s) (slot_ptr, slot_idx) cap') (slot_ptr, slot_idx) s)
          \<and> pspace_aligned s \<and> pspace_distinct s \<and> valid_objs s \<and> valid_idle s
          \<and> valid_mdb s \<and> ?QM s cap'))"
          in hoare_post_imp_R)
        prefer 2
          apply (subgoal_tac "r\<noteq> cap.NullCap \<longrightarrow> cte_wp_at (op \<noteq> cap.NullCap) (slot_ptr, slot_idx) s")
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
      apply wp
      apply (simp split del: split_if)
  apply (clarsimp split del: split_if cong: conj_cong)
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
  apply (clarsimp split del: split_if)
  apply (clarsimp simp: cte_wp_at_caps_of_state not_idle_thread_def)
  apply (rule conjI)
   apply (clarsimp simp: not_idle_thread_def valid_idle_def st_tcb_at_def
                         obj_at_def is_cap_table_def)
  apply (rule conjI)
   apply (clarsimp simp: not_idle_thread_def valid_idle_def st_tcb_at_def
                         obj_at_def is_cap_table_def)
  apply (rule conjI)
   apply (clarsimp simp: not_idle_thread_def valid_idle_def st_tcb_at_def
                         obj_at_def is_cap_table_def)
  apply (rule conjI)
   apply (rule rev_mp[OF _ real_cte_tcb_valid])
   apply simp
  apply (rule context_conjI)
   apply (clarsimp split:split_if_asm simp:remove_rights_def)
  apply (intro conjI ballI)
     apply (drule(1) bspec,clarsimp)+
  apply (case_tac "capb = aa")
   apply (clarsimp simp:masked_as_full_def split:split_if_asm)
  apply (clarsimp simp:masked_as_full_def free_index_update_def is_cap_simps)
  done
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
  apply (simp add:word_size_def add_commute)
done

lemma get_ipc_buffer_words_receive_slots:
  "\<lbrakk> tcb_ipcframe obj = cap.ArchObjectCap (arch_cap.PageCap b rs sz mapdata); valid_cap (tcb_ipcframe obj) s;
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
    apply (subst add_assoc)+
    apply (clarsimp simp: mask_add_aligned)
    apply (drule_tac n1 = "pageBitsForSize sz" and y = 2
      in is_aligned_weaken[OF is_aligned_after_mask])
       apply (case_tac sz,simp_all add:msg_align_bits)
       apply (simp add:mask_add_aligned)
         apply (simp add:word_mod_2p_is_mask[where n = 2,symmetric] word_of_int_hom_syms)
  apply (subst evalMonad_compose)
   apply (simp add:empty_when_fail_loadWord weak_det_spec_loadWord)+
   using loadWord_functional[unfolded functional_def,simplified]
     apply fastforce
  apply (simp add:evalMonad_loadWord word_size_def mask_add_aligned)
       apply (simp add:word_mod_2p_is_mask[where n = 2,symmetric] word_of_int_hom_syms)
  apply (subst evalMonad_compose)
   apply (simp add:empty_when_fail_loadWord weak_det_spec_loadWord)+
   using loadWord_functional[unfolded functional_def,simplified]
     apply fastforce
  apply (simp add:evalMonad_loadWord word_size_def mask_add_aligned)
  apply (simp add:word_mod_2p_is_mask[where n = 2,symmetric] word_of_int_hom_syms)
done

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
          apply (simp_all add:dest_of_def)
        apply (case_tac "arch_cap")
          apply (simp_all add:dest_of_def)
        apply (clarsimp simp:transform_cap_def)
      apply (drule_tac x = word in spec)
      apply (drule_tac x = "set" in spec)
      apply (clarsimp simp:cte_wp_at_cases dest!:get_tcb_SomeD)
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
  apply (simp add:load_cap_transfer_def')
    apply (rule_tac Q' = "\<lambda>r s. r = get_ipc_buffer_words (machine_state s'a) obj
                 [Suc (Suc (msg_max_length + msg_max_extra_caps))..<5 + (msg_max_length + msg_max_extra_caps)]
      \<and> s = s'a" in corres_symb_exec_r)
     prefer 2
     apply (wp get_ipc_buffer_words)
       apply (wp mapM_wp)
     apply fastforce
     apply clarsimp
     apply (clarsimp,intro conjI,(simp add:obj_at_def)+)
    apply (rule dcorres_expand_pfx)
    apply clarsimp
    apply (drule get_ipc_buffer_words_receive_slots)
        apply (clarsimp dest!:get_tcb_rev,drule valid_tcb_objs,simp)
       apply (clarsimp simp:valid_tcb_def tcb_cap_cases_def)
      apply simp+
      apply (clarsimp dest!:get_tcb_rev,drule valid_tcb_objs,simp)
     apply (clarsimp simp:valid_tcb_def tcb_cap_cases_def)
    apply (clarsimp simp:)
    apply (rule corres_guard_imp[OF corres_split_catch[where f = dc]])
         apply (rule corres_trivial[OF dcorres_return])
        apply clarsimp
       apply (rule corres_splitEE[where r'="\<lambda>cnode cnode'. cnode = transform_cap cnode'"])
          apply (rule corres_splitEE[where r'="\<lambda>p p'. p = transform_cslot_ptr p'"])
             apply (simp add:liftE_bindE)
               apply (rule corres_split[OF _ get_cap_corres])
                   apply (rule corres_splitEE[OF _ corres_whenE,where r' = dc])
                       apply (rule dcorres_returnOk)
                      apply clarsimp+
                 apply (wp|clarsimp)+
          apply (clarsimp simp:handleE'_def Monads_D.unify_failure_def Exceptions_A.unify_failure_def)
          apply (rule corres_split_bind_case_sum [OF lookup_slot_for_cnode_op_corres])
              apply (clarsimp simp:word_bl.Rep_inverse word_size)+
           apply (rule hoareE_TrueI[where P=\<top>])+
        apply clarsimp
      apply wp
      apply (rule hoare_post_imp_R[OF hoare_True_E_R])
     apply fastforce
     apply (wp lsfco_not_idle)
    apply (clarsimp simp:handleE'_def Monads_D.unify_failure_def Exceptions_A.unify_failure_def)
         apply (rule corres_split_bind_case_sum [OF lookup_cap_corres])
        apply (clarsimp simp:word_bl.Rep_inverse word_size Types_D.word_bits_def)+
       apply (rule hoareE_TrueI)+
      apply clarsimp
     apply (rule hoare_post_impErr[OF hoareE_TrueI])
    apply fastforce
    apply simp
   apply (wp lsfco_not_idle | clarsimp)+
   apply fastforce
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
    apply (rule corres_split [where r'=dc], assumption)
      apply (rule dcorres_dummy_corrupt_ipc_buffer)
     apply wp
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
                 \<and> 2 + msg_max_length + length caps < unat max_ipc_words) and valid_etcbs)
           (Endpoint_D.transfer_caps ep
              (map (\<lambda>(cap, slot). (transform_cap cap, transform_cslot_ptr slot)) caps)
              sender rcv)
           (Ipc_A.transfer_caps info caps ep rcv rcv_buffer d)"
  unfolding Ipc_A.transfer_caps_def Endpoint_D.transfer_caps_def
  apply clarsimp
  apply (cases rcv_buffer)
   apply simp
   apply (rule corres_dummy_return_r)
   apply (rule corres_guard_imp)
     apply (rule corres_split [where r'="\<lambda>r r'. r = None" and P=\<top> and P'=\<top>])
        prefer 2
        apply (rule corres_alternate2)
        apply simp
       apply simp
       apply (rule transfer_caps_loop_None)
      apply wp
    apply simp
   apply simp
  apply (simp del: get_receive_slots.simps)
  apply (rule corres_guard_imp)
    apply (rule corres_split)
       prefer 2
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
     \<top> (op = s)
     (Endpoint_D.lookup_extra_caps thread
                                   (cdl_intent_extras (transform_full_intent (machine_state s) thread t)))
     (Ipc_A.lookup_extra_caps thread buffer (data_to_message_info (tcb_context t msg_info_register)))"
  apply (clarsimp simp:lookup_extra_caps_def liftE_bindE Endpoint_D.lookup_extra_caps_def)
  apply (rule corres_symb_exec_r)
    apply (rule_tac F = "evalMonad (get_extra_cptrs buffer (data_to_message_info (tcb_context t msg_info_register))) s = Some rv"
      in corres_gen_asm2)
  apply (rule corres_mapME[where S = "{(x,y). x = of_bl y \<and> length y = Types_D.word_bits}"])
    prefer 3
           apply simp
           apply (erule conjE)
           apply (drule_tac t="of_bl y" in sym, simp)
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
      apply (simp del:get_extra_cptrs.simps
        add: zip_map_eqv[where g = "\<lambda>x. x",simplified])+
      apply (simp add: Types_D.word_bits_def del:get_extra_cptrs.simps)
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
  notes hoare_post_taut[wp]
  shows
  "dcorres dc \<top> ((\<lambda>s. evalMonad (lookup_ipc_buffer in_receive recv) s = Some rv)
    and valid_idle and not_idle_thread thread and not_idle_thread recv and tcb_at recv
    and valid_objs and pspace_aligned and pspace_distinct and valid_etcbs)
    (corrupt_ipc_buffer recv in_receive)
    (copy_mrs send rva recv rv (mi_length (data_to_message_info (tcb_context tcb msg_info_register))))"
  apply (rule dcorres_expand_pfx)
  apply (clarsimp simp:corrupt_ipc_buffer_def)
    apply (case_tac rv)
      apply (rule corres_symb_exec_l)
        apply (rule_tac F = " rvb = None " in corres_gen_asm)
        apply (clarsimp simp:copy_mrs_def)
           apply (rule corres_guard_imp)
           apply (rule corres_dummy_return_l)
           apply (rule corres_split[OF _ set_registers_corres])
             apply (rule corres_symb_exec_r)+
          apply (rule corres_trivial[OF corres_free_return])
        apply (wp|clarsimp simp:option.cases split:option.splits)+
      apply (clarsimp simp:get_ipc_buffer_def gets_the_def exs_valid_def gets_def
        get_def bind_def return_def assert_opt_def fail_def split:option.splits | rule conjI)+
      apply (frule(1) tcb_at_is_etcb_at, clarsimp simp: is_etcb_at_def, fold get_etcb_def)
      apply (clarsimp simp:not_idle_thread_def tcb_at_def opt_cap_tcb)+
    apply (simp split:cdl_cap.splits)
      apply (wp cdl_get_ipc_buffer_None)
     apply simp+
     apply (wp cdl_get_ipc_buffer_None)
    apply simp+
  apply (drule lookup_ipc_buffer_SomeB_evalMonad)
  apply clarsimp
  apply (rule corres_symb_exec_l)
    apply (rule_tac F = " rv = Some b" in corres_gen_asm)
    apply (clarsimp simp:option.splits)
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
     apply wp
     apply (wp cdl_get_ipc_buffer_Some)
      apply (fastforce simp:cte_wp_at_def)
     apply clarsimp+
   apply simp+
done


lemma opt_cap_valid_etcbs: "\<lbrakk>tcb_at ptr s; valid_etcbs s; ptr \<noteq> idle_thread s; sl \<in> tcb_abstract_slots \<or> sl = tcb_pending_op_slot\<rbrakk> \<Longrightarrow> \<exists>cap. opt_cap (ptr, sl) (transform s) = Some cap"
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
      apply (wp cdl_get_ipc_buffer_None)
     apply simp+
     apply (wp cdl_get_ipc_buffer_None)
    apply simp+
  apply (drule lookup_ipc_buffer_SomeB_evalMonad)
  apply clarsimp
  apply (rule corres_symb_exec_l)
    apply (rule_tac F = " rv = Some b" in corres_gen_asm)
    apply (clarsimp simp:option.splits)
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
     apply clarsimp+
done

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
    apply (frule_tac P1 = "op = (cap.ArchObjectCap arch_cap)" in use_valid[OF _ cte_wp])
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
  "\<lbrace>ipc_buffer_wp_at buf t \<rbrace> copy_mrs send rva recv rv (mi_length (data_to_message_info (tcb_context obj' msg_info_register)))
            \<lbrace>\<lambda>r. ipc_buffer_wp_at buf t\<rbrace>"
  apply (simp add:copy_mrs_def)
    apply (wp|wpc)+
    apply (wp mapM_wp)
      apply (simp add:store_word_offs_def ipc_buffer_wp_at_def)
      apply wp
     prefer 2
     apply fastforce
    apply (clarsimp simp:ipc_buffer_wp_at_def)
  apply (rule_tac Q="\<lambda>rv. ipc_buffer_wp_at buf t" in hoare_strengthen_post)
    apply (wp mapM_wp)
   apply fastforce
  apply (clarsimp)
done

lemma copy_mrs_valid_irq_node:
  "\<lbrace>valid_irq_node\<rbrace> copy_mrs a b c d e
            \<lbrace>\<lambda>rva s. valid_irq_node s\<rbrace>"
  apply (simp add:valid_irq_node_def)
  apply (wp)
  apply (rule hoare_allI)
  apply (rule hoare_pre)
  apply wps
  apply wp
  apply clarsimp
done

lemma corres_complete_ipc_transfer:
  "ep' = ep
  \<Longrightarrow> dcorres dc \<top>
           (valid_objs and pspace_aligned and valid_global_refs and pspace_distinct and valid_mdb
            and (\<lambda>s. not_idle_thread (cur_thread s) s) and valid_irq_node
            and valid_idle and not_idle_thread recv and not_idle_thread send and valid_etcbs)
           (Endpoint_D.do_ipc_transfer ep' send recv can_grant)
           (Ipc_A.do_ipc_transfer send ep badge can_grant recv diminish)"
  apply (clarsimp simp: Endpoint_D.do_ipc_transfer_def Ipc_A.do_ipc_transfer_def)
  apply (rule dcorres_expand_pfx)
      apply (rule dcorres_symb_exec_r_evalMonad)
     apply wp
     apply (clarsimp simp:thread_get_def get_send_slots_def get_thread_def bind_assoc)
     apply (rule dcorres_gets_the)
      apply (clarsimp, frule(1) valid_etcbs_get_tcb_get_etcb)
      apply (clarsimp simp:opt_object_tcb not_idle_thread_def transform_tcb_def split del:if_splits)
      apply (case_tac "tcb_fault obj'")
        apply (clarsimp split del:if_splits)
        apply (rule dcorres_symb_exec_r_evalMonad,wp)
        apply (simp add:do_normal_transfer_def get_message_info_def select_f_get_register split del:if_splits)
        apply (rule dcorres_absorb_gets_the)
        apply (simp add:alternative_bind bind_assoc split del:if_splits)
        apply (rule corres_alternate1)
          apply (rule corres_guard_imp)
                  apply (rule corres_split[OF _ corres_if[OF _ corres_split_catch]])
                  prefer 4
                  apply clarsimp
                  apply (rule corres_guard_imp[OF dcorres_lookup_extra_caps])
                          apply (clarsimp simp:not_idle_thread_def)+
                 apply assumption
                   apply (rule corres_split[OF _ dcorres_copy_mrs'])
                   apply (simp add:get_message_info_def select_f_get_register bind_assoc transform_cap_list_def)
                     apply (rule corres_split[OF _ transfer_caps_dcorres])
                     apply (rule corres_corrupt_tcb_intent_dupl)
                     apply (rule corres_split[OF _ set_message_info_corres])
                       unfolding K_bind_def
                      apply (rule corrupt_tcb_intent_as_user_corres)
                      apply (wp evalMonad_lookup_ipc_buffer_wp' hoare_vcg_ball_lift copy_mrs_valid_irq_node
                        | simp add:not_idle_thread_def split_def)+
               apply fastforce
              apply (clarsimp simp:transform_cap_list_def)
             apply wp[1]
            apply (rule hoareE_TrueI)
            apply (rule corres_trivial)
           apply (clarsimp simp:transform_cap_list_def)
           apply (wp hoare_vcg_ball_lift | clarsimp)+
           apply (rule validE_validE_R)
            apply (rule hoare_vcg_conj_liftE1)
             apply (rule hoare_post_imp_R)
             apply (rule validE_validE_R)
             apply (rule hoare_vcg_conj_liftE1[OF lookup_extra_caps_srcs])
             apply (rule hoare_post_imp_dc2_actual[OF lookup_extra_caps_valid_objs])
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
            apply (simp add:msg_max_length_def max_ipc_words msg_max_extra_caps_def)
           apply wp
         apply fastforce
       apply clarsimp
       apply (intro conjI|clarsimp simp:obj_at_def dest!:get_tcb_SomeD)+
         apply (rule conjI)
           apply simp+
         apply (drule lookup_ipc_buffer_tcb_at)+
         apply (clarsimp dest!:get_tcb_SomeD simp:tcb_at_def not_idle_thread_def)
         apply (rule conjI)
           apply (simp add:data_to_message_info_valid)+
       apply (simp add:msg_max_length_def max_ipc_words)
     apply (clarsimp simp:not_idle_thread_def tcb_at_def max_ipc_words msg_max_length_def)+
     apply (drule lookup_ipc_buffer_tcb_at)+
     apply ((clarsimp simp:tcb_at_def empty_when_fail_lookup_ipc_buffer weak_det_spec_lookup_ipc_buffer)+)[3]
    apply (clarsimp simp:alternative_bind bind_assoc do_fault_transfer_def split del:if_splits)
    apply (rule corres_alternate2)
      apply (rule corres_guard_imp)
         apply (rule corres_symb_exec_r)
            apply (rule corres_symb_exec_r)
              apply (rule corres_symb_exec_r)
                apply (clarsimp)
                apply (rule corres_split[OF _ dcorres_set_mrs'])
            apply (rule corres_corrupt_tcb_intent_dupl)
            apply (rule corres_split[OF _ set_message_info_corres])
             unfolding K_bind_def
             apply (rule corrupt_tcb_intent_as_user_corres)
           apply (wp|clarsimp simp:not_idle_thread_def)+
          apply (wpc,wp)
         apply (rule hoare_pre)
         apply (wpc,wp)
        apply clarsimp+
       apply (rule hoare_allI[OF hoare_drop_imp])
    apply (wp|clarsimp)+
    apply (rule conjI,simp)
    apply (clarsimp simp:lookup_ipc_buffer_tcb_at not_idle_thread_def opt_object_tcb
      empty_when_fail_lookup_ipc_buffer weak_det_spec_lookup_ipc_buffer | frule(1) valid_etcbs_get_tcb_get_etcb)+
done

lemma dcorres_handle_fault_reply:
  "dcorres dc \<top> (tcb_at y and valid_idle and not_idle_thread y and  valid_etcbs)
   (corrupt_tcb_intent y)
   (handle_fault_reply a y mi mrs)"
  apply (case_tac a)
    apply (simp_all)
    apply (rule dummy_corrupt_tcb_intent_corres)+
    apply (rule corres_dummy_return_l)
    apply (rule corres_guard_imp)
      apply (rule corres_split[OF corres_trivial[OF corres_free_return] corrupt_tcb_intent_as_user_corres])
        apply (wp|clarsimp)+
    apply (rule corres_dummy_return_l)
    apply (rule corres_guard_imp)
      apply (rule corres_split[OF corres_trivial[OF corres_free_return] corrupt_tcb_intent_as_user_corres])
        apply (wp|clarsimp)+
done

lemma alternative_distrib2:
  "(do x \<leftarrow> a;  (b x \<sqinter> c x) od) = ((do x\<leftarrow>a; b x od) \<sqinter> (do x\<leftarrow>a; c x od)) "
  apply (simp add:bind_def alternative_def UNION_eq)
  apply (rule ext)+
  apply force
  done

lemma set_cap_overlap:
  "opt_object recv s = Some (Tcb tcb)
    \<Longrightarrow> (KHeap_D.set_cap (recv,tcb_pending_op_slot) a >>= K (KHeap_D.set_cap (recv,tcb_pending_op_slot) b)) s
    = (KHeap_D.set_cap (recv,tcb_pending_op_slot) b) s"
  apply rule
    apply (clarsimp simp: KHeap_D.set_cap_def in_monad has_slots_def opt_object_def
         KHeap_D.set_object_def update_slots_def object_slots_def )
   apply (clarsimp simp: KHeap_D.set_cap_def in_monad has_slots_def opt_object_def
        KHeap_D.set_object_def update_slots_def object_slots_def )
  apply (fastforce simp: in_monad has_slots_def opt_object_def KHeap_D.set_object_def
        KHeap_D.set_cap_def update_slots_def simpler_modify_def snd_bind
       snd_return gets_the_def snd_gets assert_opt_def object_slots_def
        valid_def cong: cdl_object.case_cong split: option.splits)
  done

lemma remove_parent_dummy_when_pending_wp:
  "\<lbrakk>mdb_cte_at (swp (cte_wp_at (op\<noteq>cap.NullCap) ) s) (cdt s); tcb_at y s\<rbrakk>
  \<Longrightarrow>\<lbrace>op = (transform s)\<rbrace> remove_parent (y, tcb_pending_op_slot) \<lbrace>\<lambda>r. op = (transform s)\<rbrace>"
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

lemma exs_valid_return:
  "\<lbrace>P\<rbrace> return () \<exists>\<lbrace>\<lambda>r. P\<rbrace>"
  by (fastforce simp:return_def exs_valid_def)

lemma exs_valid_gets:
  "\<lbrace>P\<rbrace> gets f \<exists>\<lbrace>\<lambda>r. P\<rbrace>"
  by (fastforce simp:return_def exs_valid_def simpler_gets_def)

lemma dcorres_set_thread_state_Restart:
  "dcorres dc \<top>
           (\<lambda>a. valid_mdb a \<and> not_idle_thread recver a \<and> st_tcb_at idle (idle_thread a) a \<and> valid_etcbs a)
           (do y \<leftarrow> delete_cap_simple (recver, tcb_pending_op_slot);
               KHeap_D.set_cap (recver, tcb_pending_op_slot) RestartCap
            od)
           (set_thread_state recver Structures_A.thread_state.Restart)"
  apply (rule dcorres_expand_pfx)
  apply (case_tac "\<not> tcb_at recver s'")
   apply (clarsimp simp:set_thread_state_def)
   apply (clarsimp simp:delete_cap_simple_def bind_assoc)
   apply (rule dcorres_gets_the)
    apply (clarsimp simp:tcb_at_def)+
  apply (subgoal_tac "dcorres dc (op = (transform s')) (op = s') (KHeap_D.set_cap (recver, 5) RestartCap)
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
             apply (rule_tac Q = "\<lambda>rv. op = (transform s'a)" in corres_symb_exec_l)
                apply (simp add:corres_underlying_def)
                apply (frule(1) valid_etcbs_get_tcb_get_etcb, clarsimp)
                apply (subst set_cap_overlap[unfolded K_def])
                 apply (drule opt_object_tcb, assumption)
                  apply simp
                 apply (simp add:transform_tcb_def)
                apply (frule opt_object_tcb, assumption)
                 apply simp
                apply (simp add:set_object_def bind_def in_monad gets_the_def simpler_gets_def
                get_def return_def put_def KHeap_D.set_cap_def assert_opt_def transform_tcb_def
                has_slots_def object_slots_def update_slots_def KHeap_D.set_object_def simpler_modify_def)
                apply (clarsimp simp:transform_def transform_current_thread_def)
                apply (intro conjI ext)
               apply (frule(1) valid_etcbs_get_tcb_get_etcb, clarsimp simp: get_etcb_def)
                apply (clarsimp simp:transform_objects_def transform_tcb_def
                 infer_tcb_pending_op_def restrict_map_def map_add_def)
               apply (clarsimp simp:restrict_map_def map_add_def dest!:get_tcb_SomeD get_etcb_SomeD)
               prefer 2
               apply (wp remove_parent_dummy_when_pending_wp)
                apply (clarsimp simp:valid_mdb_def)
               apply (simp add:tcb_at_def)
              apply clarsimp
              apply (wp remove_parent_dummy_when_pending_slot)
               apply (simp add:valid_mdb_def)
              apply (simp add:tcb_at_def get_tcb_def)
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
             PageTableUnmap_D.is_final_cap_def split:split_if_asm Structures_A.thread_state.splits
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
            PageTableUnmap_D.is_final_cap_def split:split_if_asm Structures_A.thread_state.splits
           | wp exs_valid_return exs_valid_gets)+
     apply (frule(1) valid_etcbs_get_tcb_get_etcb, clarsimp simp: get_etcb_def)
     apply (subst opt_cap_tcb)
        apply simp
       apply (simp add: get_etcb_def)
      apply (simp add: not_idle_thread_def)
     apply (simp add: tcb_pending_op_slot_def)
    apply ((wp | clarsimp | simp)+)[2]
  apply (frule(1) valid_etcbs_get_tcb_get_etcb, clarsimp simp: get_etcb_def)
  apply (simp add:KHeap_D.set_cap_def set_object_def gets_the_def gets_def bind_assoc)
  apply (rule dcorres_absorb_get_l)
  apply (rule dcorres_absorb_get_r)
  apply (frule opt_object_tcb)
    apply (simp add: get_etcb_def)
   apply (simp add:not_idle_thread_def)
  apply (clarsimp simp:assert_opt_def has_slots_def transform_tcb_def object_slots_def
    update_slots_def tcb_ipcbuffer_slot_def KHeap_D.set_object_def simpler_modify_def)
  apply (clarsimp simp:corres_underlying_def put_def transform_def transform_current_thread_def
    not_idle_thread_def)
  apply (intro ext conjI)
  apply (clarsimp simp:transform_objects_def transform_tcb_def restrict_map_def map_add_def
    infer_tcb_pending_op_def tcb_ipcbuffer_slot_def not_idle_thread_def tcb_pending_op_slot_def)
  done


lemma when_return:
  "when f (return ()) = return ()"
  by (simp add:when_def)

crunch valid_etcbs[wp]: handle_fault_reply valid_etcbs

lemma do_reply_transfer_corres:
  "slot' = transform_cslot_ptr slot \<Longrightarrow>
   dcorres dc \<top>
     (invs and tcb_at recver and tcb_at sender and cte_wp_at (op = (cap.ReplyCap recver False)) slot
      and (\<lambda>s. not_idle_thread (cur_thread s) s)
      and not_idle_thread recver and not_idle_thread sender and valid_etcbs)
     (Endpoint_D.do_reply_transfer sender recver slot')
     (Ipc_A.do_reply_transfer sender recver slot)"
  apply (clarsimp simp:do_reply_transfer_def Endpoint_D.do_reply_transfer_def)
  apply (clarsimp simp:get_thread_state_def thread_get_def get_thread_fault_def)
  apply (rule dcorres_absorb_gets_the)
  apply (clarsimp simp:assert_def corres_free_fail bind_assoc)
  apply (frule(1) valid_etcbs_get_tcb_get_etcb)
  apply (rule dcorres_gets_the[rotated])
   apply (clarsimp simp:not_idle_thread_def
     opt_object_tcb transform_tcb_def | intro conjI impI)+
   apply (rule corres_guard_imp)
     apply (rule corres_split [OF _ corres_complete_ipc_transfer])
        apply (rule corres_split[OF _ delete_cap_simple_corres])
          apply (rule corres_split_noop_rhs2[OF attempt_switch_to_dcorres[THEN corres_trivial]
                                                set_thread_state_corres])
           apply (wp | clarsimp simp:not_idle_thread_def)+
   apply (clarsimp simp:invs_def valid_state_def valid_pspace_def not_idle_thread_def)
   apply (case_tac slot,clarsimp simp:cte_wp_at_caps_of_state)
   apply (drule valid_idle_has_null_cap)
       apply simp+
  apply (clarsimp simp:bind_assoc)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF _ delete_cap_simple_corres])
      apply (rule corres_symb_exec_r)
         apply (rule corres_symb_exec_r)
            apply (rule corres_symb_exec_r)
               apply (rule corres_split[OF _ dcorres_handle_fault_reply])
                 apply (rule corres_split[OF _ thread_set_fault_corres])
                    apply (simp add:when_return split del:if_splits)
                    apply (simp add:dc_def[symmetric] if_distrib[where f = "set_thread_state recver"]
                      split del:if_splits)
                    apply (rule corres_split_noop_rhs2)
                       apply (rule corres_trivial)
                       apply (clarsimp simp: when_def dc_def[symmetric])
                       apply (rule attempt_switch_to_dcorres)
                      apply (rule corres_if_rhs)
                       apply (rule corres_alternate2)
                       apply (rule set_thread_state_corres)
                      apply (rule corres_alternate1)
                      apply (rule set_thread_state_corres)
                     apply wp
                   apply simp
                  apply clarsimp+
                 apply (wp thread_set_no_change_tcb_state
                   hoare_drop_imps thread_set_cur_thread_idle_thread
                   thread_set_valid_idle
                   | simp add:not_idle_thread_def)+
    apply (rule_tac Q = "\<lambda>r s. invs s \<and> not_idle_thread recver s \<and> valid_etcbs s
        \<and> tcb_at recver s "
      in  hoare_strengthen_post)
     apply (clarsimp simp:not_idle_thread_def)
     apply (wp cap_delete_one_reply_st_tcb_at)
    apply (clarsimp simp:not_idle_thread_def invs_valid_idle st_tcb_at_tcb_at)
   apply (wp|clarsimp)+
  apply (rule conjI)
   apply (case_tac slot)
   apply (clarsimp simp:invs_def not_idle_thread_def valid_state_def)
   apply (drule valid_idle_has_null_cap)
       apply assumption+
    apply (fastforce simp:valid_state_def cte_wp_at_caps_of_state)
   apply simp
  apply (rule emptyable_cte_wp_atD)
    apply (simp add:is_master_reply_cap_def invs_def valid_state_def
     valid_pspace_def valid_idle_def)+
done

lemma set_endpoint_valid_irq_node[wp]:
  "\<lbrace>valid_irq_node and ep_at w\<rbrace> set_endpoint w ep \<lbrace>\<lambda>rv. valid_irq_node\<rbrace>"
  apply (clarsimp simp:valid_irq_node_def)
  apply wp
  apply simp_all
  apply (simp add:set_endpoint_def)
    apply wp
  apply (rule hoare_allI)
    apply (rule_tac Q="\<lambda>s. \<forall>irq. cap_table_at 0 (interrupt_irq_node s irq) s \<and> ep_at w s" in hoare_vcg_precond_imp)
      apply (clarsimp simp:set_object_def get_def put_def bind_def return_def valid_def obj_at_def)
      apply (drule_tac x = irq in spec)
      apply (clarsimp simp:is_cap_table_def is_ep_def)
      apply (simp split:Structures_A.kernel_object.splits)
    apply assumption
    apply wp
  apply (clarsimp simp:get_object_def|wp)+
done

lemma dcorres_if_rhs:
  assumes G: "G \<Longrightarrow> corres_underlying sr nf rvr P Q a b"
  and nG: "\<not> G \<Longrightarrow> corres_underlying sr nf rvr P Q' a c"
  shows "corres_underlying sr nf rvr P
    (\<lambda>s. (G \<longrightarrow> Q s) \<and> (\<not> G \<longrightarrow> Q' s)) a (if G then b else c)"
  apply (clarsimp)
  apply (safe)
   apply (erule G)
  apply (erule nG)
  done

lemma recv_sync_ipc_corres:
  "\<lbrakk>epptr = cap_ep_ptr ep_cap; ep_id = epptr;  tcb_id_receiver = thread\<rbrakk>\<Longrightarrow>
    dcorres dc
     \<top>
     (ep_at epptr and not_idle_thread thread and (\<lambda>s. not_idle_thread (cur_thread s) s)
      and st_tcb_at active thread
      and valid_state and valid_etcbs)
     (Endpoint_D.receive_ipc tcb_id_receiver ep_id )
     (Ipc_A.receive_ipc thread ep_cap)
  "
  apply (clarsimp simp:corres_free_fail cap_ep_ptr_def Ipc_A.receive_ipc_def
                 split:cap.splits Structures_A.endpoint.splits)
  apply (rule dcorres_expand_pfx)
  apply (rule_tac Q'="\<lambda>ko. op = s' and ko_at (kernel_object.Endpoint ko) word1" in corres_symb_exec_r)
    apply (simp add:Endpoint_D.receive_ipc_def gets_def)
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
      apply (rule corres_dummy_return_l)
      apply (rule corres_guard_imp)
        apply (rule corres_split[OF corres_dummy_set_sync_ep set_thread_state_block_on_receive_corres])
      apply (wp|clarsimp)+
(* SendEP *)
      apply (frule get_endpoint_pick)
        apply (simp add:obj_at_def)
      apply (subst ep_waiting_set_send_lift)
        apply (simp add:valid_state_def)
        apply simp
      apply (clarsimp simp:option_select_def valid_ep_abstract_def)
      apply (drule_tac s = "set list" in sym)
      apply (rule conjI, clarsimp dest!: not_empty_list_not_empty_set)
      apply (clarsimp simp:neq_Nil_conv)
      apply (rule_tac P1="\<top>" and P'="op = s'a" and x1 = y
        in dcorres_absorb_pfx[OF select_pick_corres[OF dcorres_expand_pfx],rotated])
         apply clarsimp
        apply clarsimp
       apply clarsimp
      apply (drule_tac x1 = y in iffD2[OF eqset_imp_iff], simp)
      apply (clarsimp simp:ep_waiting_set_send_def get_thread_def bind_assoc gets_the_def gets_def)
      apply (rule dcorres_absorb_get_l,clarsimp)
      apply (frule(1) valid_etcbs_tcb_etcb, clarsimp)
      apply (subst opt_object_tcb)
        apply (erule get_tcb_rev)
        apply (fastforce simp: get_etcb_def)
        apply (frule_tac a = y and list = "y # ys" in pending_thread_in_send_not_idle)
          apply ((simp add:valid_state_def insertI obj_at_def not_idle_thread_def )+)[4]
         apply (clarsimp simp:assert_opt_def transform_tcb_def infer_tcb_pending_op_def
           split del:if_splits)
      apply (rule dcorres_symb_exec_r)
        apply (rule corres_symb_exec_r)
           apply (rule_tac F="sender_state = tcb_state t" in corres_gen_asm2)
           apply (clarsimp dest!:get_tcb_SomeD simp:dc_def[symmetric]
             split del:if_splits split:split_if_asm)
           apply (rule corres_guard_imp)
             apply (rule corres_split[OF _ corres_complete_ipc_transfer])
                prefer 2
                apply simp
               apply (rule corres_symb_exec_r)
                  apply (rule dcorres_if_rhs)
                   apply (rule dcorres_if_rhs)
                    apply (simp add:dc_def[symmetric] when_def)
                    apply (rule corres_alternate1)+
                    apply (rule corres_setup_caller_cap)
                    apply (clarsimp simp:st_tcb_at_def obj_at_def generates_pending_def)
                   apply (rule corres_alternate2[OF set_thread_state_corres])
                  apply (rule corres_alternate1[OF corres_alternate2])
                  apply (rule dcorres_rhs_noop_below_True[OF switch_if_required_to_dcorres])
                  apply (rule set_thread_state_corres)
                 apply clarsimp
                 apply (wp hoare_drop_imps)
               apply clarsimp
              apply (wp gts_st_tcb_at | simp add:not_idle_thread_def )+
            apply (rule_tac Q="\<lambda>fault. valid_mdb and valid_objs and pspace_aligned
              and pspace_distinct and not_idle_thread y and not_idle_thread thread
              and valid_idle and valid_irq_node and (\<lambda>s. cur_thread s \<noteq> idle_thread s)
              and tcb_at y and tcb_at thread
              and st_tcb_at (\<lambda>rv. rv = Structures_A.thread_state.BlockedOnSend word1 payload) y and valid_etcbs"
            in hoare_strengthen_post[rotated])
             apply (clarsimp simp:not_idle_thread_def)
             apply (clarsimp simp:st_tcb_at_def obj_at_def)
            apply (frule_tac a = y and list = "y # ys" in pending_thread_in_send_not_idle)
               apply (clarsimp simp:valid_state_def insertI)+
             apply (simp add:obj_at_def not_idle_thread_def)+
            apply (rule hoare_pre)
             apply ((wp | clarsimp simp:not_idle_thread_def | wps )+)[1]
            apply (clarsimp simp:valid_state_def st_tcb_at_def obj_at_def
             valid_pspace_def)
            apply (drule valid_objs_valid_ep_simp)
             apply (simp add:is_ep_def)
            apply (clarsimp simp:valid_ep_def split:Structures_A.endpoint.splits list.splits)
           apply (clarsimp simp:valid_state_def valid_pspace_def)+
       apply (drule valid_objs_valid_ep_simp)
        apply (simp add:is_ep_def)
       apply (clarsimp simp:valid_ep_def split:Structures_A.endpoint.splits list.splits)
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
      apply (rule corres_dummy_return_l)
      apply (rule corres_guard_imp)
        apply (rule corres_split[OF corres_dummy_set_sync_ep set_thread_state_block_on_receive_corres])
      apply (wp|clarsimp)+
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
  "corres_underlying t rl r P Q (do y \<leftarrow> f; g y od) rh
    \<Longrightarrow> corres_underlying t rl r P Q (do y \<leftarrow> f; g y \<sqinter> h y od) rh"
  apply (simp add:alternative_distrib2)
  apply (erule corres_alternate1)
  done

lemma dcorres_alternate_seq2:
  "corres_underlying t rl r P Q (do y \<leftarrow> f; h y od) rh
    \<Longrightarrow> corres_underlying t rl r P Q (do y \<leftarrow> f; g y \<sqinter> h y od) rh"
  apply (simp add:alternative_distrib2)
  apply (erule corres_alternate2)
  done

lemma dcorres_dummy_set_pending_cap_Restart:
  "dcorres dc \<top> (st_tcb_at (op = Structures_A.thread_state.Restart) thread and not_idle_thread thread and valid_etcbs)
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
  apply (clarsimp dest!: get_tcb_SomeD
    simp add:opt_object_def not_idle_thread_def
    transform_objects_def transform_tcb_def
    infer_tcb_pending_op_def runnable_def
    split : Structures_A.thread_state.splits)
  done


crunch valid_etcbs[wp]: attempt_switch_to "valid_etcbs"

lemma send_sync_ipc_corres:
  "\<lbrakk>ep_id = epptr;tcb_id_sender= thread\<rbrakk> \<Longrightarrow>
    dcorres dc
     \<top>
  (not_idle_thread thread and (\<lambda>s. not_idle_thread (cur_thread s) s)
      and st_tcb_at active thread
      and valid_state and valid_etcbs)
     (Endpoint_D.send_ipc block call badge can_grant tcb_id_sender ep_id)
     (Ipc_A.send_ipc block call badge can_grant thread epptr)"
  apply (clarsimp simp:gets_def Endpoint_D.send_ipc_def Ipc_A.send_ipc_def split del:if_splits)
  apply (rule dcorres_absorb_get_l)
  apply (clarsimp split del:if_splits)
  apply (rule_tac Q' = "\<lambda>r. op = s' and ko_at (kernel_object.Endpoint r) epptr" in corres_symb_exec_r[rotated])
     apply (wp|simp split del:if_splits)+
  apply (rule dcorres_expand_pfx)
  apply (clarsimp split del:if_splits)
  apply (frule_tac get_endpoint_pick)
   apply (simp add:obj_at_def)
  apply (case_tac rv)
    apply (clarsimp split del:if_splits)
    apply (subst ep_waiting_set_recv_lift)
     apply (simp add:valid_state_def)
     apply simp
    apply (clarsimp simp:valid_ep_abstract_def none_is_receiving_ep_def option_select_def)
    apply (rule corres_dummy_return_l)
    apply (rule corres_guard_imp)
      apply (rule corres_split[OF corres_dummy_set_sync_ep set_thread_state_block_on_send_corres])
       apply wp
     apply simp
    apply (wp|clarsimp simp: split del:if_splits)+
(* SendEP *)
   apply (subst ep_waiting_set_recv_lift)
    apply (simp add:valid_state_def)
    apply simp
    apply (clarsimp simp:valid_ep_abstract_def none_is_receiving_ep_def option_select_def)
    apply (rule corres_dummy_return_l)
    apply (rule corres_guard_imp)
      apply (rule corres_split[OF corres_dummy_set_sync_ep set_thread_state_block_on_send_corres])
       apply wp
     apply simp
    apply (wp|clarsimp simp: split del:if_splits)+
(* RecvEP *)
  apply (subst ep_waiting_set_recv_lift,simp add:valid_state_def)
  apply simp
  apply (clarsimp simp:valid_ep_abstract_def split del:if_splits)
  apply (subst option_select_not_empty)
   apply (clarsimp simp: dest!: not_empty_list_not_empty_set)
  apply (drule_tac s = "set list" in sym)
  apply (clarsimp simp: bind_assoc neq_Nil_conv)
  apply (rule_tac P1="\<top>" and P'="op = s'a" and x1 = y
         in dcorres_absorb_pfx[OF select_pick_corres[OF dcorres_expand_pfx]])
      defer
      apply simp+
  apply (drule_tac x1 = y in iffD2[OF eqset_imp_iff], simp)
  apply (clarsimp simp:obj_at_def dc_def[symmetric])
  apply (subst when_def)+
  apply (rule corres_guard_imp)
    apply (rule dcorres_symb_exec_r)
      apply (rule corres_symb_exec_r)
         apply (rule corres_symb_exec_r)
                 apply (rule corres_split[OF _ corres_complete_ipc_transfer])
                    apply (rule corres_split[OF _ set_thread_state_corres])
                      apply (rule dcorres_rhs_noop_above[OF attempt_switch_to_dcorres])
                       apply (rule_tac corres_symb_exec_r)
                          apply (rule dcorres_if_rhs)
                           apply (rule dcorres_if_rhs)
                            apply simp
                            apply (rule corres_alternate1)+
                            apply (rule corres_setup_caller_cap)
                            apply (clarsimp simp:ep_waiting_set_recv_def st_tcb_at_def obj_at_def generates_pending_def)
                           apply (rule corres_alternate1[OF corres_alternate2])
                           apply (rule set_thread_state_corres)
                          apply (rule corres_alternate2)
                          apply (rule corres_return_trivial )
                         apply (clarsimp)
                         apply (rule_tac Q="\<lambda>r. valid_mdb and valid_idle and valid_objs
                            and not_idle_thread thread and not_idle_thread y and tcb_at thread and tcb_at y
                            and st_tcb_at runnable thread and valid_etcbs
                           " in hoare_strengthen_post[rotated])
                          apply (clarsimp simp:st_tcb_at_def obj_at_def,
                             simp split:Structures_A.thread_state.splits, fastforce)
                         apply ((wp thread_get_valid_etcbs sts_st_tcb_at' sts_st_tcb_at_neq |clarsimp simp add:not_idle_thread_def)+)
            apply (wp hoare_vcg_conj_lift)
             apply (rule hoare_disjI1)
             apply (wp do_ipc_transfer_st_tcb | wpc | simp)+
          apply (simp add:return_def fail_def valid_def split:Structures_A.thread_state.splits)
         apply (clarsimp simp:conj_ac not_idle_thread_def)+
        apply (rule hoare_drop_imp)
        apply wp
      apply clarsimp
     apply (wp|wps)+
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
    valid_idle_def st_tcb_at_def obj_at_def
    dest!:get_tcb_SomeD
    split:Structures_A.endpoint.splits list.splits)
  apply (clarsimp simp:ep_waiting_set_recv_def runnable_eq_active)
  apply (intro conjI impI)
   apply clarsimp+
  apply fastforce
done

lemma dcorres_injection_handler_rhs:
  "dcorres (dc \<oplus> r) P P' f g
     \<Longrightarrow> dcorres (dc \<oplus> r) P P' f (injection_handler h g)"
  by (rule KHeap_DR.dcorres_injection_handler_rhs)

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
  "\<lbrace>valid_state and (\<lambda>_. valid_fault ft')\<rbrace>
   thread_set (tcb_fault_update (\<lambda>_. Some ft')) thread
   \<lbrace>\<lambda>rv. valid_state\<rbrace>"
  apply (clarsimp simp:valid_state_def pred_conj_def)
  apply (rule hoare_conjI)
   apply (simp add:valid_pspace_def)
   apply (wp thread_set_valid_objs thread_set_iflive_trivial
             thread_set_zombies_trivial
          | simp add:tcb_cap_cases_def)+
        apply (simp add:thread_set_def)
        apply wp
         apply (simp add:set_object_def)
         apply (wp,clarsimp)
        apply (rule delta_sym_refs)
          apply (simp add:state_refs_of_def refs_of_def)+
         apply (case_tac "x = thread")
          apply ((clarsimp dest!:get_tcb_SomeD)+)[2]
        apply (clarsimp simp:state_refs_of_def)
        apply (case_tac "x = thread")
         apply ((clarsimp dest!:get_tcb_SomeD simp: refs_of_def)+)
   apply (clarsimp simp:valid_tcb_def)
   apply (drule_tac bspec, assumption)
   apply (clarsimp simp:tcb_cap_cases_def)
   apply (erule disjE,clarsimp simp:valid_cap_def)+
   apply (clarsimp simp:valid_cap_def)
  apply (wp thread_set_mdb thread_set_valid_ioc_trivial)
    apply (clarsimp simp: tcb_cap_cases_def)
    apply (erule disjE,clarsimp+)+
   apply (wp thread_set_valid_idle_trivial thread_set_valid_ioc_trivial
          | simp add: ran_tcb_cap_cases)+
    apply (wp thread_set_only_idle thread_set_ifunsafe_trivial
              thread_set_arch_state thread_set_valid_reply_caps_trivial
              thread_set_valid_reply_masters_trivial
              thread_set_global_refs_triv
           | clarsimp simp: tcb_cap_cases_def)+
          apply (rule hoare_conjI)
           apply (unfold valid_irq_node_def)
           apply (simp add:thread_set_def)
           apply wp
            apply (simp add:KHeap_A.set_object_def)
            apply wp
           apply (clarsimp simp:obj_at_def)
           apply (drule_tac x = irq in spec)
           apply (clarsimp simp:is_cap_table_def dest!: get_tcb_SomeD)
          apply simp_all
  apply (rule hoare_conjI)
   apply (wp | simp add: thread_set_def set_object_def)+
   apply (clarsimp simp:valid_irq_handlers_def)
   apply (drule_tac x=cap in bspec)
    apply (subst(asm) caps_of_state_after_update)
     apply (clarsimp simp: obj_at_def dest!:get_tcb_SomeD)
     apply (clarsimp simp: tcb_cap_cases_def)
     apply (erule disjE,clarsimp)+
     apply simp+
   apply (clarsimp simp:irq_issued_def)
  apply (wp thread_set_arch_objs thread_set_arch_caps_trivial
            thread_set_valid_globals thread_set_v_ker_map thread_set_eq_ker_map
            thread_set_asid_map thread_set_global_pd_mappings
            thread_set_pspace_in_kernel_window
            thread_set_cap_refs_in_kernel_window
         | simp_all | clarsimp simp:tcb_cap_cases_def)+
done

lemma thread_set_fault_obj_at:
 "\<lbrace>tcb_at thread\<rbrace> thread_set (tcb_fault_update (\<lambda>_. Some ft')) thread
  \<lbrace>\<lambda>rv s. obj_at (\<lambda>ko. \<exists>tcb. ko = TCB tcb \<and> (False \<or> (\<exists>y. tcb_fault tcb = Some y)) = True) thread s\<rbrace>"
  apply (clarsimp simp:thread_set_def)
  apply wp
    apply (simp add:set_object_def)
    apply wp
  apply (clarsimp simp:obj_at_def)
done

lemma thread_set_fault_st_tcb_at:
  "\<lbrace>st_tcb_at P  a\<rbrace> thread_set (tcb_fault_update (\<lambda>_. Some ft')) thread
            \<lbrace>\<lambda>rv. st_tcb_at P a\<rbrace>"
  apply (clarsimp simp:thread_set_def)
  apply wp
    apply (simp add:set_object_def)
    apply wp
    apply (clarsimp simp:st_tcb_at_def obj_at_def dest!:get_tcb_SomeD split:if_splits)
  apply (simp add:get_tcb_def)
done

lemma tcb_fault_handler_length:
  "\<lbrakk>valid_state s;ko_at (TCB tcb) thread s\<rbrakk>
           \<Longrightarrow> length (tcb_fault_handler tcb) = Types_D.word_bits"
  apply (clarsimp simp:valid_state_def valid_pspace_def)
  apply (drule valid_tcb_objs)
    apply (simp add:obj_at_def,erule get_tcb_rev)
  apply (simp add:valid_tcb_def WordSetup.word_bits_def Types_D.word_bits_def)
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
  apply (clarsimp simp: set_object_def)
  apply wp
  apply (auto simp: valid_etcbs_def st_tcb_at_def obj_at_def is_etcb_at_def st_tcb_at_kh_def obj_at_kh_def)
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

lemma send_fault_ipc_corres:
  "did = thread \<Longrightarrow>
   dcorres (dc\<oplus>dc) \<top>
     (not_idle_thread thread and st_tcb_at active thread and valid_irq_node and
      valid_state and ko_at (TCB tcb) thread and (\<lambda>s. ekheap  s thread = Some etcb) and
      (\<lambda>s. not_idle_thread (cur_thread s) s) and (\<lambda>_. valid_fault ft') and valid_etcbs)
     (Endpoint_D.send_fault_ipc did) (Ipc_A.send_fault_ipc thread ft')"
  apply (simp add:Endpoint_D.send_fault_ipc_def Ipc_A.send_fault_ipc_def)
  apply (rule dcorres_expand_pfx)
  apply (rule corres_guard_imp)
    apply (rule_tac P'="op=s'" in thread_get_corresE[where tcb' = tcb and etcb'=etcb])
     apply simp_all
   prefer 2
   apply (rule conjI)
   apply (simp add:transform_tcb_def)
   apply (simp add: get_etcb_def)
  apply (rule corres_guard_imp)
    apply (rule_tac R' ="\<lambda>rv s. (\<forall>ref badge rights.
                       rv = cap.EndpointCap ref badge rights \<longrightarrow> (ep_at ref s))
      \<and> not_idle_thread (cur_thread s) s
      \<and> (st_tcb_at active thread s \<and> valid_state s) \<and> ko_at (TCB tcb) thread s \<and> valid_etcbs s
      \<and> not_idle_thread thread s" and R= "\<lambda>r. \<top>"
      in corres_splitEE[where r'="\<lambda>x y. x = transform_cap y"])
       apply (simp add: Let_def cap_fault_injection)
       apply (rule dcorres_expand_pfx)
       apply (clarsimp split:cap.splits arch_cap.splits simp:transform_cap_def)
       apply (clarsimp | rule conjI)+
         apply (rule corres_guard_imp)
           apply (rule corres_split[where r'="dc"])
              apply clarsimp
              apply (rule send_sync_ipc_corres)
               apply simp+
             apply (rule thread_set_fault_corres,simp)
            apply (wp thread_set_fault_obj_at)
           apply (simp add:not_idle_thread_def)
           apply (wps)
           apply (wp abs_typ_at_lifts[OF thread_set_typ_at]
                     thread_set_fault_obj_at thread_set_fault_st_tcb_at thread_set_valid_etcbs_2)
          apply (simp add: ko_at_tcb_at not_idle_thread_def)+
         apply (clarsimp simp add: st_tcb_at_def)
       apply clarsimp
      apply (clarsimp simp: cap_fault_injection)
      apply (rule dcorres_injection_handler_rhs)
      apply (rule lookup_cap_corres)
       apply simp
      apply (simp add:tcb_fault_handler_length)
     apply wp
    apply (rule validE_validE_R)
    apply (rule hoare_validE_conj)
     prefer 2
     apply wp
    apply (rule hoare_post_impErr[THEN validE_validE_R])
      apply (rule hoare_vcg_precond_impE)
       apply (rule lookup_cap_valid[THEN validE_R_validE])
      apply (clarsimp simp:valid_cap_def valid_state_def valid_pspace_def)+
  done

end
