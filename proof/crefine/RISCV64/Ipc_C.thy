(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Ipc_C
imports
  Finalise_C
  CSpace_All
  SyscallArgs_C
  IsolatedThreadAction
begin

context begin interpretation Arch . (*FIXME: arch-split*)

definition
  "replyFromKernel_success_empty thread \<equiv> do
     VSpace_H.lookupIPCBuffer True thread;
     asUser thread $ setRegister RISCV64_H.badgeRegister 0;
     setMessageInfo thread $ (Types_H.MI 0 0 0 0)
   od"

lemma replyFromKernel_success_empty:
  "replyFromKernel thread (0, []) = replyFromKernel_success_empty thread"
  unfolding replyFromKernel_def replyFromKernel_success_empty_def
  by (simp add: setMRs_Nil submonad_asUser.fn_stateAssert)

crunch copyMRs
  for valid_ipc_buffer_ptr'[wp]: "valid_ipc_buffer_ptr' p"
  (rule: hoare_valid_ipc_buffer_ptr_typ_at' wp: crunch_wps)

lemma threadSet_obj_at'_nontcb:
  "koType TYPE('a::pspace_storable) \<noteq> koType TYPE(Structures_H.tcb) \<Longrightarrow>
   \<lbrace>obj_at' (P :: 'a \<Rightarrow> bool) t'\<rbrace> threadSet f t \<lbrace>\<lambda>rv. obj_at' P t'\<rbrace>"
  apply (simp add: threadSet_def)
  apply (wp obj_at_setObject2 hoare_drop_imps
       | clarsimp simp: updateObject_default_def in_monad)+
  done

lemma setMRs_ntfn_at[wp]:
  "\<lbrace>ko_at' (ntfn :: Structures_H.notification) p\<rbrace>
    setMRs badge val thread
   \<lbrace>\<lambda>_. ko_at' ntfn p\<rbrace>"
  apply (simp add: setMRs_def
                   zipWithM_x_mapM_x split_def storeWordUser_def
                   setThreadState_def asUser_def)
  apply (wp threadSet_obj_at'_nontcb mapM_x_wp hoare_drop_imps
       | simp | rule subset_refl)+
  done

lemma asUser_ntfn_at[wp]:
  "\<lbrace>ko_at' (ntfn :: Structures_H.notification) p\<rbrace>
    asUser tptr f \<lbrace>\<lambda>_. ko_at' ntfn p\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp threadSet_obj_at'_nontcb hoare_drop_imps | simp | rule subset_refl)+
  done

definition
  "lookup_fault_get_lufType luf \<equiv> case luf of
     InvalidRoot \<Rightarrow> 0
   | MissingCapability _ \<Rightarrow> 1
   | DepthMismatch _ _ \<Rightarrow> 2
   | GuardMismatch _ _ _ \<Rightarrow> 3"

definition
  "setMR thread buffer \<equiv> \<lambda>idx value.
   if idx < length msgRegisters
   then do
     asUser thread (setRegister (msgRegisters ! idx) value);
     return (idx + 1)
   od
   else case buffer of None \<Rightarrow> return (length msgRegisters)
     | Some buf \<Rightarrow> do
         storeWordUser (buf + (of_nat (idx + 1) * word_size)) value;
         return (idx + 1)
   od"

lemmas msgMaxLength_unfold
    = msgMaxLength_def[where 'a=nat, unfolded msgLengthBits_def, simplified,
                       unfolded shiftL_nat, simplified]

lemma registers_less_maxlength:
  "length msgRegisters < msgMaxLength"
  by (simp add: msgRegisters_unfold msgMaxLength_unfold)

lemma setMRs_to_setMR':
notes
  wordSize_def' [simp]
shows
  "setMRs thread buffer xs
   = (do
    stateAssert (tcb_at' thread) [];
    ys \<leftarrow> zipWithM (setMR thread buffer) [0 ..< msgMaxLength] xs;
    return (of_nat (min (length xs) (length msgRegisters +
              (case buffer of None \<Rightarrow> 0 | _ \<Rightarrow> Suc (unat (msgMaxLength :: machine_word))
                  - unat ((1 :: machine_word) + of_nat (length msgRegisters))))))
  od)"
  apply (simp add: setMRs_def setMR_def split_def
                   zipWithM_x_mapM_x asUser_mapM_x bind_assoc
                   zipWithM_If_cut)
  apply (simp add: zipWithM_mapM)
  apply (simp add: split_def mapM_liftM_const[unfolded liftM_def]
                   mapM_return mapM_Nil mapM_x_Nil asUser_mapM_x
                   last_append map_replicate_const
            split: option.split split del: if_split)
  apply (simp add: mapM_discarded mapM_x_def split del: if_split)
  apply (intro allI conjI impI bind_cong bind_apply_cong refl
               arg_cong2[where f=sequence_x]
               map_length_cong,
         insert registers_less_maxlength, simp_all)
     apply (clarsimp simp: set_zip)
    apply (clarsimp simp: set_zip)
   apply (simp add: msgRegisters_unfold msgMaxLength_def
                   msgLengthBits_def shiftL_nat)
  apply (clarsimp simp only: set_zip min_less_iff_conj length_zip
                             length_map nth_zip fst_conv nth_map
                             snd_conv upto_enum_word length_drop
                             length_take nth_drop nth_upt)
  apply (subst nth_take)
   apply (simp add: less_diff_conv)
  apply (simp add: word_size word_size_def field_simps)
  done

lemma setMRs_to_setMR:
  "setMRs thread buffer xs
   = (do
    stateAssert (tcb_at' thread) [];
    ys \<leftarrow> zipWithM (setMR thread buffer) [0 ..< msgMaxLength] xs;
    return (of_nat (last (0 # ys)))
  od)"
  apply (simp add: setMRs_to_setMR' zipWithM_mapM split_def mapM_discarded
              del: last.simps)
  apply (subst mapM_last_Cons)
    prefer 3
    apply simp
   apply (simp add: msgMaxLength_unfold)
  apply (simp add: fst_last_zip_upt)
  apply (subgoal_tac "msgMaxLength - Suc 0 \<ge> length msgRegisters
                           \<and> of_nat (length xs - Suc 0) = of_nat (length xs) - (1 :: machine_word)
                           \<and> unat ((1 :: machine_word) + of_nat (length msgRegisters)) = Suc (length msgRegisters)")
   apply (simp add: setMR_def split: option.split)
   apply (intro impI conjI allI)
      apply clarsimp
     apply clarsimp
    apply (clarsimp simp add: msgRegisters_unfold)
    apply (clarsimp simp: linorder_not_less linorder_not_le)
    apply (clarsimp simp: msgRegisters_unfold msgMaxLength_def
                          msgLengthBits_def shiftL_nat)
   apply (clarsimp simp: msgRegisters_unfold msgMaxLength_def
                         msgLengthBits_def shiftL_nat)
  apply (simp add: msgRegisters_unfold msgMaxLength_unfold)
  apply (case_tac xs, simp_all)
  done

lemma asUser_comm:
  assumes neq: "a \<noteq> b"
  assumes efa: "empty_fail fa" and efb: "empty_fail fb"
  shows
  "\<And>ra rb. do
     ra \<leftarrow> asUser a fa;
     rb \<leftarrow> asUser b fb;
     c ra rb
   od = do
     rb \<leftarrow> asUser b fb;
     ra \<leftarrow> asUser a fa;
     c ra rb
   od"
  apply (rule submonad_comm' [OF submonad_asUser submonad_asUser])
      apply (clarsimp simp: neq asUser_replace_def Let_def fun_upd_twist [OF neq])
     apply (clarsimp simp: neq asUser_replace_def Let_def obj_at'_real_def
                           ko_wp_at'_def ps_clear_upd_None ps_clear_upd
                    split: option.split kernel_object.split)
    apply (clarsimp simp: neq[symmetric] asUser_replace_def Let_def
                          obj_at'_real_def ko_wp_at'_def ps_clear_upd_None
                          ps_clear_upd
                   split: option.split kernel_object.split)
   apply (rule efa efb)+
  done

crunch getSanitiseRegisterInfo
  for inv[wp]: P

lemma empty_fail_getSanitiseRegisterInfo[wp, simp]:
  "empty_fail (getSanitiseRegisterInfo t)"
  by (wpsimp simp: getSanitiseRegisterInfo_def wp: RISCV64.empty_fail_archThreadGet)

lemma asUser_getRegister_getSanitiseRegisterInfo_comm:
  "do
     ra \<leftarrow> asUser a (getRegister r);
     rb \<leftarrow> getSanitiseRegisterInfo b;
     c ra rb
   od = do
     rb \<leftarrow> getSanitiseRegisterInfo b;
     ra \<leftarrow> asUser a (getRegister r);
     c ra rb
   od"
  by (rule bind_inv_inv_comm; wpsimp)

lemma asUser_mapMloadWordUser_threadGet_comm:
  "do
     ra \<leftarrow> mapM loadWordUser xs;
     rb \<leftarrow> threadGet fb b;
     c ra rb
   od = do
     rb \<leftarrow> threadGet fb b;
     ra \<leftarrow> mapM loadWordUser xs;
     c ra rb
   od"
  by (rule bind_inv_inv_comm, auto; wp mapM_wp')

lemma asUser_mapMloadWordUser_getSanitiseRegisterInfo_comm:
  "do
     ra \<leftarrow> mapM loadWordUser xs;
     rb \<leftarrow> getSanitiseRegisterInfo b;
     c ra rb
   od = do
     rb \<leftarrow> getSanitiseRegisterInfo b;
     ra \<leftarrow> mapM loadWordUser xs;
     c ra rb
   od"
  by (rule bind_inv_inv_comm, auto; wp mapM_wp')

lemma asUser_loadWordUser_comm:
  "empty_fail m \<Longrightarrow>
   do x \<leftarrow> asUser t m; y \<leftarrow> loadWordUser p; n x y od =
   do y \<leftarrow> loadWordUser p; x \<leftarrow> asUser t m; n x y od"
  apply (rule submonad_comm2 [OF _ loadWordUser_submonad_fn
                                 submonad_asUser, symmetric])
       apply (simp add: submonad_args_def pointerInUserData_def)
      apply (simp add: asUser_replace_def Let_def)
     apply (clarsimp simp: asUser_replace_def Let_def typ_at'_def ko_wp_at'_def
                           ps_clear_upd ps_clear_upd_None pointerInUserData_def
                    split: option.split kernel_object.split)
    apply simp
   apply (simp add: ef_loadWord)
  apply assumption
  done

lemma asUser_storeWordUser_comm:
  "empty_fail m \<Longrightarrow>
   do x \<leftarrow> asUser t m; y \<leftarrow> storeWordUser p v; n x y od =
   do y \<leftarrow> storeWordUser p v; x \<leftarrow> asUser t m; n x y od"
  apply (rule submonad_comm2 [OF _ storeWordUser_submonad_fn
                                 submonad_asUser, symmetric])
       apply (simp add: submonad_args_def pointerInUserData_def)
      apply (simp add: asUser_replace_def Let_def)
     apply (clarsimp simp: asUser_replace_def Let_def typ_at'_def ko_wp_at'_def
                           ps_clear_upd ps_clear_upd_None pointerInUserData_def
                    split: option.split kernel_object.split)
    apply simp
   apply (simp add: ef_storeWord)
  apply assumption
  done

lemma length_syscallMessage:
  "length RISCV64_H.syscallMessage = unat n_syscallMessage"
  apply (simp add: syscallMessage_def RISCV64.syscallMessage_def
                msgRegisters_unfold n_syscallMessage_def)
  apply (simp add: upto_enum_def)
  apply (simp add: fromEnum_def enum_register)
  done

lemma length_timeoutMessage:
  "length RISCV64_H.timeoutMessage = unat n_timeoutMessage"
  by (simp add: timeoutMessage_def RISCV64.timeoutMessage_def msgRegisters_unfold
                n_timeoutMessage_def upto_enum_def fromEnum_def enum_register)

end

context kernel_m begin

(* FIXME move *)
lemma ccap_relation_ep_helpers:
  "\<lbrakk> ccap_relation cap cap'; cap_get_tag cap' = scast cap_endpoint_cap \<rbrakk>
        \<Longrightarrow> capCanSend_CL (cap_endpoint_cap_lift cap') = from_bool (capEPCanSend cap)
          \<and> capCanReceive_CL (cap_endpoint_cap_lift cap') = from_bool (capEPCanReceive cap)
          \<and> capEPPtr_CL (cap_endpoint_cap_lift cap') = capEPPtr cap
          \<and> capEPBadge_CL (cap_endpoint_cap_lift cap') = capEPBadge cap
          \<and> capCanGrant_CL (cap_endpoint_cap_lift cap') = from_bool (capEPCanGrant cap)
          \<and> capCanGrantReply_CL (cap_endpoint_cap_lift cap') = from_bool (capEPCanGrantReply cap)"
  by (clarsimp simp: cap_lift_endpoint_cap cap_to_H_simps
                     cap_endpoint_cap_lift_def word_size
              elim!: ccap_relationE)

(* FIXME move *)
lemma ccap_relation_reply_helpers:
  "\<lbrakk>ccap_relation cap cap'; cap_get_tag cap' = scast cap_reply_cap\<rbrakk>
   \<Longrightarrow> capReplyCanGrant_CL (cap_reply_cap_lift cap') = from_bool (capReplyCanGrant cap)
       \<and> capReplyPtr_CL (cap_reply_cap_lift cap') = capReplyPtr cap"
  by (clarsimp simp: cap_lift_reply_cap cap_to_H_simps cap_reply_cap_lift_def word_size
              elim!: ccap_relationE)

(* FIXME move *)
lemma ccap_relation_sched_context_helpers:
  "\<lbrakk> ccap_relation cap cap'; cap_get_tag cap' = scast cap_sched_context_cap \<rbrakk>
   \<Longrightarrow> capSCPtr_CL (cap_sched_context_cap_lift cap') =  (capSchedContextPtr cap)
       \<and> unat (capSCSizeBits_CL (cap_sched_context_cap_lift cap')) = capSCSize cap"
  by (clarsimp simp: cap_lift_sched_context_cap cap_to_H_simps
                     cap_sched_context_cap_lift_def word_size
              elim!: ccap_relationE)

(*FIXME: arch-split: C kernel names hidden by Haskell names *)
(*FIXME: fupdate simplification issues for 2D arrays *)
abbreviation "syscallMessageC \<equiv>  kernel_all_global_addresses.fault_messages.[unat MessageID_Syscall]"
lemmas syscallMessageC_def = kernel_all_substitute.fault_messages_def
abbreviation "exceptionMessageC \<equiv> kernel_all_substitute.fault_messages.[unat MessageID_Exception]"
lemmas exceptionMessageC_def = kernel_all_substitute.fault_messages_def
abbreviation "timeoutMessageC \<equiv> kernel_all_substitute.fault_messages.[unat MessageID_TimeoutReply]"
lemmas timeoutMessageC_def = kernel_all_substitute.fault_messages_def

lemma syscallMessage_ccorres:
  "n < unat n_syscallMessage
      \<Longrightarrow> register_from_H (RISCV64_H.syscallMessage ! n)
           = index syscallMessageC n"
  apply (simp add: RISCV64_H.syscallMessage_def syscallMessageC_def
                   RISCV64.syscallMessage_def
                   MessageID_Exception_def MessageID_Syscall_def
                   n_syscallMessage_def msgRegisters_unfold)
  apply (simp add: upto_enum_def fromEnum_def enum_register)
  apply (simp add: toEnum_def enum_register)
  apply (clarsimp simp: fupdate_def
              | drule nat_less_cases' | erule disjE)+
  done

lemma timeoutMessage_ccorres:
  "n < unat n_timeoutMessage
   \<Longrightarrow> register_from_H (RISCV64_H.timeoutMessage ! n) = index timeoutMessageC n"
  apply (simp add: RISCV64_H.timeoutMessage_def timeoutMessageC_def RISCV64.timeoutMessage_def
                   MessageID_Exception_def MessageID_TimeoutReply_def
                   n_timeoutMessage_def msgRegisters_unfold)
  apply (simp add: upto_enum_def fromEnum_def enum_register)
  apply (simp add: toEnum_def enum_register)
  apply (clarsimp simp: fupdate_def | drule nat_less_cases' | erule disjE)+
  done

end

context begin interpretation Arch . (*FIXME: arch-split*)

definition
  "handleArchFaultReply' f sender receiver tag \<equiv> do
     label \<leftarrow> return $ msgLabel tag;
     mlen \<leftarrow> return $ msgLength tag;
     case f of
       VMFault _ _ \<Rightarrow> do
         sendBuf \<leftarrow> lookupIPCBuffer False sender;
         stateAssert (tcb_at' sender) [];
         case sendBuf of
           None \<Rightarrow> return ()
         | Some bufferPtr \<Rightarrow> do
             mapM loadWordUser
               (map (\<lambda>i. bufferPtr + PPtr (i * 8))
                    [(scast n_msgRegisters :: machine_word) + 1.e. msgMaxLength]);
             return ()
           od;
         return True
       od
    od"

definition
  "handleFaultReply' f sender receiver \<equiv> do
     tag \<leftarrow> getMessageInfo sender;
     label \<leftarrow> return $ msgLabel tag;
     mlen \<leftarrow> return $ msgLength tag;
     case f of
       CapFault _ _ _ \<Rightarrow> return True
     | ArchFault af \<Rightarrow> handleArchFaultReply' af sender receiver tag
     | UnknownSyscallException _ \<Rightarrow> do
         t \<leftarrow> getSanitiseRegisterInfo receiver;
         regs \<leftarrow> return $ take (unat mlen) syscallMessage;
         zipWithM_x (\<lambda>rs rd. do
           v \<leftarrow> asUser sender $ getRegister rs;
           asUser receiver $ setRegister rd $ sanitiseRegister t rd v
         od) msgRegisters regs;
         sendBuf \<leftarrow> lookupIPCBuffer False sender;
         case sendBuf of
           None \<Rightarrow> return ()
         | Some bufferPtr \<Rightarrow>
             zipWithM_x (\<lambda>i rd. do
               v \<leftarrow> loadWordUser (bufferPtr + PPtr (i * 8));
               asUser receiver $ setRegister rd $ sanitiseRegister t rd v
             od) [(scast n_msgRegisters :: machine_word) + 1.e. scast n_syscallMessage] (drop (unat (scast n_msgRegisters :: machine_word)) regs);
       return (label = 0)
       od
     | UserException _ _ \<Rightarrow> do
         t \<leftarrow> getSanitiseRegisterInfo receiver;
         regs \<leftarrow> return $ take (unat mlen) exceptionMessage;
         zipWithM_x (\<lambda>rs rd. do
           v \<leftarrow> asUser sender $ getRegister rs;
           asUser receiver $ setRegister rd $ sanitiseRegister t rd v
         od) msgRegisters regs;
         return (label = 0)
         od
     | Timeout _ \<Rightarrow> do
         t \<leftarrow> getSanitiseRegisterInfo receiver;
         regs \<leftarrow> return $ take (unat mlen) timeoutMessage;
         zipWithM_x (\<lambda>rs rd. do
           v \<leftarrow> asUser sender $ getRegister rs;
           asUser receiver $ setRegister rd $ sanitiseRegister t rd v
         od) msgRegisters regs;
         sendBuf \<leftarrow> lookupIPCBuffer False sender;
         case sendBuf of
           None \<Rightarrow> return ()
         | Some bufferPtr \<Rightarrow>
             zipWithM_x (\<lambda>i rd. do
               v \<leftarrow> loadWordUser (bufferPtr + PPtr (i * 8));
               asUser receiver $ setRegister rd $ sanitiseRegister t rd v
             od) [(scast n_msgRegisters :: machine_word) + 1.e. scast n_timeoutMessage] (drop (unat (scast n_msgRegisters :: machine_word)) regs);
       return (label = 0)
       od
  od"

lemma loadWordUser_discarded:
  "loadWordUser p >>= (\<lambda>_. n) =
   stateAssert (pointerInUserData p and K (p && mask 3 = 0)) [] >>= (\<lambda>_. n)"
  apply (rule ext)
  apply (clarsimp simp: loadWordUser_def loadWord_def bind_def assert_def
                        stateAssert_def split_def return_def fail_def
                        doMachineOp_def gets_def get_def select_f_def
                        modify_def put_def)
  done

lemma stateAssert_mapM_loadWordUser_comm:
  "do x \<leftarrow> stateAssert P []; y \<leftarrow> mapM loadWordUser ptrs; n od =
   do y \<leftarrow> mapM loadWordUser ptrs; x \<leftarrow> stateAssert P []; n od"
  apply (rule bind_inv_inv_comm)
     apply (wp stateAssert_inv)
    apply (wp mapM_wp_inv)+
  apply simp
  done

lemmas syscallMessage_unfold
  = RISCV64_H.syscallMessage_def
    RISCV64.syscallMessage_def
        [unfolded upto_enum_def, simplified,
         unfolded fromEnum_def enum_register, simplified,
         unfolded toEnum_def enum_register, simplified]

lemmas timeoutMessage_unfold
  = RISCV64_H.timeoutMessage_def
    RISCV64.timeoutMessage_def
        [unfolded upto_enum_def, simplified,
         unfolded fromEnum_def enum_register, simplified,
         unfolded toEnum_def enum_register, simplified]

lemma handleArchFaultReply':
  notes option.case_cong_weak [cong] wordSize_def'[simp]
  shows "(do
    sb \<leftarrow> lookupIPCBuffer False s;
    msg \<leftarrow> getMRs s sb tag;
    handleArchFaultReply f r (msgLabel tag) msg
  od) x' = handleArchFaultReply' f s r tag x'"
  supply  empty_fail_cond[simp]
  apply (unfold handleArchFaultReply'_def getMRs_def msgMaxLength_def
                bit_def msgLengthBits_def msgRegisters_unfold
                fromIntegral_simp1 fromIntegral_simp2
                shiftL_word Let_def)
  apply (simp add: bind_assoc)
  apply (clarsimp simp: mapM_def sequence_def bind_assoc asUser_bind_distrib
                        asUser_return submonad_asUser.fn_stateAssert)
  apply (case_tac f)
    apply (clarsimp simp: handleArchFaultReply_def asUser_getRegister_discarded
                            bind_subst_lift [OF stateAssert_stateAssert]
                            pred_conj_def)
    apply (rule bind_apply_cong [OF refl], rename_tac sb s'')
    apply (rule bind_apply_cong [OF refl], rename_tac rv r'')
    apply (case_tac sb, simp_all add: word_size n_msgRegisters_def)[1]
  done

lemmas lookup_uset_getreg_swap = bind_inv_inv_comm[OF lookupIPCBuffer_inv
                                 user_getreg_inv'
                                 empty_fail_lookupIPCBuffer
                                 empty_fail_asUser[OF empty_fail_getRegister]]

end

lemma mapM_x_zip_take_Cons_append:
  "n = 0 \<longrightarrow> zs = []
  \<Longrightarrow> mapM_x f (zip (x # xs) (take n (y # ys) @ zs))
      = do
        when (n > 0) (f (x, y));
        mapM_x f (zip xs (take (n - 1) ys @ zs))
      od"
  by (cases n, simp_all add: mapM_x_Cons)

lemma threadGet_lookupIPCBuffer_comm:
  "do
     a \<leftarrow> lookupIPCBuffer x y;
     t \<leftarrow> threadGet id r;
     c a t
   od = do
     t \<leftarrow> threadGet id r;
     a \<leftarrow> lookupIPCBuffer x y;
     c a t
  od"
  by (rule bind_inv_inv_comm; wp?; auto)

lemma getSanitiseRegisterInfo_lookupIPCBuffer_comm:
  "do
     a \<leftarrow> lookupIPCBuffer x y;
     t \<leftarrow> getSanitiseRegisterInfo r;
     c a t
   od = do
     t \<leftarrow> getSanitiseRegisterInfo r;
     a \<leftarrow> lookupIPCBuffer x y;
     c a t
  od"
  by (rule bind_inv_inv_comm; wp?; auto)

lemma threadGet_moreMapM_comm:
  "do
     a \<leftarrow>
       case sb of None \<Rightarrow> return []
       | Some bufferPtr \<Rightarrow> return (xs bufferPtr) >>= mapM loadWordUser;
     t \<leftarrow> threadGet id r;
     c a t
   od = do
     t \<leftarrow> threadGet id r;
     a \<leftarrow>
       case sb of None \<Rightarrow> return []
       | Some bufferPtr \<Rightarrow> return (xs bufferPtr) >>= mapM loadWordUser;
     c a t
  od"
  apply (rule bind_inv_inv_comm)
     apply (rule hoare_pre, wpc; (wp mapM_wp')?)
     apply simp
    apply wp
   apply (auto split: option.splits)
  done

lemma getSanitiseRegisterInfo_moreMapM_comm:
  "do
     a \<leftarrow>
       case sb of None \<Rightarrow> return []
       | Some bufferPtr \<Rightarrow> return (xs bufferPtr) >>= mapM loadWordUser;
     t \<leftarrow> getSanitiseRegisterInfo r;
     c a t
   od = do
     t \<leftarrow> getSanitiseRegisterInfo r;
     a \<leftarrow>
       case sb of None \<Rightarrow> return []
       | Some bufferPtr \<Rightarrow> return (xs bufferPtr) >>= mapM loadWordUser;
     c a t
  od"
  apply (rule bind_inv_inv_comm)
     apply (rule hoare_pre, wpc; (wp mapM_wp')?)
     apply simp
    apply wp
   apply (auto split: option.splits)
  done

lemma monadic_rewrite_threadGet_return:
  "monadic_rewrite True False (tcb_at' r) (return x) (do t \<leftarrow> threadGet f r; return x od)"
  apply (wp_pre, monadic_rewrite_symb_exec_r_drop)
   apply (auto intro: monadic_rewrite_refl)
  done

context begin interpretation Arch .

lemma no_fail_getSanitiseRegisterInfo[wp, simp]:
  "no_fail (tcb_at' r) (getSanitiseRegisterInfo r)"
  apply (simp add: getSanitiseRegisterInfo_def)
  by wpsimp

end


lemma monadic_rewrite_getSanitiseRegisterInfo_return:
  "monadic_rewrite True False (tcb_at' r) (return x) (do t \<leftarrow> getSanitiseRegisterInfo r; return x od)"
  apply (wp_pre, monadic_rewrite_symb_exec_r_drop)
   apply (auto intro: monadic_rewrite_refl)
  done

lemma monadic_rewrite_getSanitiseRegisterInfo_drop:
  "monadic_rewrite True False (tcb_at' r) (d) (do t \<leftarrow> getSanitiseRegisterInfo r; d od)"
  apply (wp_pre, monadic_rewrite_symb_exec_r_drop)
   apply (auto intro: monadic_rewrite_refl)
  done

context kernel_m begin interpretation Arch .

lemma threadGet_discarded:
  "(threadGet f t >>= (\<lambda>_. n)) = stateAssert (tcb_at' t) [] >>= (\<lambda>_. n)"
  apply (simp add: threadGet_getObject getObject_get_assert liftM_def bind_assoc stateAssert_def)
  apply (rule ext)
  apply (simp add: bind_def simpler_gets_def get_def)
  done

lemma handleFaultReply':
  notes option.case_cong_weak [cong] wordSize_def'[simp] take_append[simp del] prod.case_cong_weak[cong]
  assumes neq: "s \<noteq> r"
  shows "monadic_rewrite True False (tcb_at' s and tcb_at' r) (do
    tag \<leftarrow> getMessageInfo s;
    sb \<leftarrow> lookupIPCBuffer False s;
    msg \<leftarrow> getMRs s sb tag;
    handleFaultReply f r (msgLabel tag) msg
  od) (handleFaultReply' f s r)"
  supply empty_fail_cond[simp]
  apply (unfold handleFaultReply'_def getMRs_def msgMaxLength_def
                bit_def msgLengthBits_def msgRegisters_unfold
                fromIntegral_simp1 fromIntegral_simp2
                shiftL_word)
  apply (simp add: bind_assoc)
  apply (rule monadic_rewrite_bind_tail)
   apply (clarsimp simp: mapM_def sequence_def bind_assoc asUser_bind_distrib
                         asUser_return submonad_asUser.fn_stateAssert)
   apply (case_tac f, simp_all add: handleFaultReply_def zipWithM_x_mapM_x zip_take)
      (* UserException *)
      apply (clarsimp simp: handleFaultReply_def zipWithM_x_mapM_x
                            zip_Cons RISCV64_H.exceptionMessage_def
                            RISCV64.exceptionMessage_def
                            mapM_x_Cons mapM_x_Nil)
      apply (rule monadic_rewrite_symb_exec_l)
         apply (rule_tac P="tcb_at' s and tcb_at' r" in monadic_rewrite_inst)
         apply (case_tac sb; (case_tac "msgLength tag < scast n_msgRegisters",
                 (erule disjE[OF word_less_cases],
                   ( clarsimp simp: n_msgRegisters_def asUser_bind_distrib
                                    mapM_x_Cons mapM_x_Nil bind_assoc
                                    asUser_mapMloadWordUser_getSanitiseRegisterInfo_comm
                                    asUser_getRegister_getSanitiseRegisterInfo_comm
                                    asUser_getRegister_discarded asUser_mapMloadWordUser_threadGet_comm
                                    asUser_comm[OF neq] asUser_getRegister_threadGet_comm
                                    bind_comm_mapM_comm [OF asUser_loadWordUser_comm, symmetric]
                                    word_le_nat_alt[of 4, simplified linorder_not_less[symmetric, of 4]]
                                    asUser_return submonad_asUser.fn_stateAssert
                   | rule monadic_rewrite_bind_tail monadic_rewrite_refl
                          monadic_rewrite_symb_exec_l[OF _ stateAssert_inv]
                          monadic_rewrite_symb_exec_l[OF _ mapM_x_mapM_valid[OF mapM_x_wp']]
                   | wp)+)+))
        apply wp+
     (* capFault *)
     apply (repeat 5 \<open>rule monadic_rewrite_symb_exec_l\<close>) (* until case sb *)
                    apply (case_tac sb)
                     apply (clarsimp
                           | rule monadic_rewrite_bind_tail monadic_rewrite_refl
                                  monadic_rewrite_symb_exec_l[OF _ mapM_x_mapM_valid[OF mapM_x_wp']]
                           | wp mapM_x_mapM_valid[OF mapM_x_wp'[OF loadWordUser_inv]]
                                empty_fail_loadWordUser)+
    (* UnknownSyscallException *)
    apply (simp add: zip_append2 mapM_x_append asUser_bind_distrib split_def bind_assoc)
    apply (rule monadic_rewrite_guard_imp)
     apply (rule monadic_rewrite_trans[rotated])
      apply (rule monadic_rewrite_do_flip)
      apply (rule monadic_rewrite_bind_tail)
       apply (rule_tac P="inj (case_bool s r)" in monadic_rewrite_gen_asm)
       apply (rule monadic_rewrite_trans[OF _ monadic_rewrite_transverse])
         apply (rule monadic_rewrite_weaken_flags[where F=False and E=True], simp)
         apply (rule isolate_thread_actions_rewrite_bind
                     bool.simps setRegister_simple
                     zipWithM_setRegister_simple
                     thread_actions_isolatable_bind lookupIPCBuffer_isolatable
                     lookupIPCBuffer_isolatable[THEN thread_actions_isolatableD]
                     copy_registers_isolate_general thread_actions_isolatable_return
                     thread_actions_isolatable_return[THEN thread_actions_isolatableD]
               | assumption
               | wp assert_inv)+
       apply (rule monadic_rewrite_isolate_final[where P="\<top>"])
         apply simp+
      apply wp
     (* swap ends *)
     apply (clarsimp simp: handleFaultReply_def zipWithM_x_mapM_x
                            zip_Cons syscallMessage_unfold
                            n_syscallMessage_def
                            upto_enum_word mapM_x_Cons mapM_x_Nil)
     apply (simp add: getSanitiseRegisterInfo_moreMapM_comm asUser_getRegister_getSanitiseRegisterInfo_comm getSanitiseRegisterInfo_lookupIPCBuffer_comm)
     apply (rule monadic_rewrite_bind_tail)
      apply (rule monadic_rewrite_bind_tail [where Q="\<lambda>_. tcb_at' r"])
       apply (case_tac sb)
        apply (case_tac "msgLength tag < scast n_msgRegisters")
         apply (erule disjE[OF word_less_cases],
                  ( clarsimp simp: n_msgRegisters_def asUser_bind_distrib
                                   mapM_x_Cons mapM_x_Nil bind_assoc
                                   asUser_getRegister_discarded
                                   asUser_comm[OF neq] take_zip
                                   word_le_nat_alt[of 4, simplified linorder_not_less[symmetric, of 4]]
                                   asUser_return submonad_asUser.fn_stateAssert
                  | rule monadic_rewrite_bind_tail monadic_rewrite_refl
                         monadic_rewrite_symb_exec_l[OF _ stateAssert_inv]
                  | wp )+)+
       apply (case_tac "msgLength tag < scast n_msgRegisters")
        apply (erule disjE[OF word_less_cases],
                  ( clarsimp simp: n_msgRegisters_def asUser_bind_distrib
                                   mapM_x_Cons mapM_x_Nil bind_assoc
                                   zipWithM_x_Nil
                                   asUser_getRegister_discarded
                                   asUser_comm[OF neq] take_zip
                                   bind_comm_mapM_comm [OF asUser_loadWordUser_comm, symmetric]
                                   asUser_return submonad_asUser.fn_stateAssert
                  | rule monadic_rewrite_bind_tail monadic_rewrite_refl
                         monadic_rewrite_symb_exec_l[OF _ mapM_x_mapM_valid[OF mapM_x_wp']]
                         monadic_rewrite_symb_exec_l[OF _ stateAssert_inv]
                         monadic_rewrite_threadGet_return
                         monadic_rewrite_getSanitiseRegisterInfo_return
                  | wp mapM_wp')+)+
       apply (simp add: n_msgRegisters_def word_le_nat_alt n_syscallMessage_def
                        linorder_not_less syscallMessage_unfold)
       apply (clarsimp | frule neq0_conv[THEN iffD2, THEN not0_implies_Suc,
                                         OF order_less_le_trans, rotated])+
       apply (subgoal_tac "\<forall>n :: machine_word. n \<le> scast n_syscallMessage \<longrightarrow> [n .e. msgMaxLength]
                                 = [n .e. scast n_syscallMessage]
                                     @ [scast n_syscallMessage + 1 .e. msgMaxLength]")
        apply (simp only: upto_enum_word[where y="scast n_syscallMessage :: machine_word"]
                          upto_enum_word[where y="scast n_syscallMessage + 1 :: machine_word"])
        apply (clarsimp simp: bind_assoc asUser_bind_distrib asUser_getRegister_threadGet_comm
                              mapM_x_Cons mapM_x_Nil threadGet_discarded
                              asUser_comm [OF neq] asUser_getRegister_discarded
                              submonad_asUser.fn_stateAssert take_zip
                              bind_subst_lift [OF submonad_asUser.stateAssert_fn]
                              word_less_nat_alt RISCV64_H.sanitiseRegister_def
                              split_def n_msgRegisters_def msgMaxLength_def
                              bind_comm_mapM_comm [OF asUser_loadWordUser_comm, symmetric]
                              word_size msgLengthBits_def n_syscallMessage_def Let_def
                   split del: if_split
                        cong: if_weak_cong register.case_cong)


        apply (rule monadic_rewrite_bind_tail)+
                apply (subst (2) upto_enum_word)
                apply (case_tac "ma < unat n_syscallMessage - 4")

                apply (erule disjE[OF nat_less_cases'],
                       ( clarsimp simp: n_syscallMessage_def bind_assoc asUser_bind_distrib
                                        mapM_x_Cons mapM_x_Nil zipWithM_x_mapM_x mapM_Cons
                                        bind_comm_mapM_comm [OF asUser_loadWordUser_comm, symmetric]
                                        asUser_loadWordUser_comm loadWordUser_discarded asUser_return
                                        zip_take_triv2 msgMaxLength_def
                                        no_fail_stateAssert
                                  cong: if_weak_cong
                       | simp
                       | rule monadic_rewrite_bind_tail
                              monadic_rewrite_refl
                              monadic_rewrite_symb_exec_l[OF _ stateAssert_inv]
                              monadic_rewrite_symb_exec_l[OF _ mapM_x_mapM_valid[OF mapM_x_wp']]
                              monadic_rewrite_threadGet_return
                              monadic_rewrite_getSanitiseRegisterInfo_return
                              monadic_rewrite_getSanitiseRegisterInfo_drop
                       | wp empty_fail_loadWordUser)+)+
      apply (clarsimp simp: upto_enum_word word_le_nat_alt simp del: upt.simps cong: if_weak_cong)
      apply (cut_tac i="unat n" and j="Suc (unat (scast n_syscallMessage :: machine_word))"
                                and k="Suc msgMaxLength" in upt_add_eq_append')
        apply (simp add: n_syscallMessage_def)
       apply (simp add: n_syscallMessage_def msgMaxLength_unfold)
      apply (simp add: n_syscallMessage_def msgMaxLength_def
                       msgLengthBits_def shiftL_nat
                  del: upt.simps upt_rec_numeral)
      apply (simp add: upto_enum_word cong: if_weak_cong)
     apply wp+
     apply (simp add: neq inj_case_bool split: bool.split)
    (* Timeout *)
    apply (simp add: zip_append2 mapM_x_append asUser_bind_distrib split_def bind_assoc)
    apply (rule monadic_rewrite_guard_imp)
     apply (rule monadic_rewrite_trans[rotated])
      apply (rule monadic_rewrite_do_flip)
      apply (rule monadic_rewrite_bind_tail)
       apply (rule_tac P="inj (case_bool s r)" in monadic_rewrite_gen_asm)
       apply (rule monadic_rewrite_trans[OF _ monadic_rewrite_transverse])
         apply (rule monadic_rewrite_weaken_flags[where F=False and E=True], simp)
         apply (rule isolate_thread_actions_rewrite_bind
                     bool.simps setRegister_simple
                     zipWithM_setRegister_simple
                     thread_actions_isolatable_bind lookupIPCBuffer_isolatable
                     lookupIPCBuffer_isolatable[THEN thread_actions_isolatableD]
                     copy_registers_isolate_general thread_actions_isolatable_return
                     thread_actions_isolatable_return[THEN thread_actions_isolatableD]
               | assumption
               | wp assert_inv)+
       apply (rule monadic_rewrite_isolate_final[where P="\<top>"])
         apply simp+
      apply wp
     (* swap ends *)
     apply (clarsimp simp: handleFaultReply_def zipWithM_x_mapM_x
                            zip_Cons timeoutMessage_unfold
                            n_timeoutMessage_def
                            upto_enum_word mapM_x_Cons mapM_x_Nil)
     apply (simp add: getSanitiseRegisterInfo_moreMapM_comm asUser_getRegister_getSanitiseRegisterInfo_comm getSanitiseRegisterInfo_lookupIPCBuffer_comm)
     apply (rule monadic_rewrite_bind_tail)
     apply (rule monadic_rewrite_bind_tail [where Q="\<lambda>_. tcb_at' r"])
      apply (case_tac sb)
       apply (case_tac "msgLength tag < scast n_msgRegisters")
        apply (erule disjE[OF word_less_cases],
                 ( clarsimp simp: n_msgRegisters_def asUser_bind_distrib
                                  mapM_x_Cons mapM_x_Nil bind_assoc
                                  asUser_getRegister_discarded
                                  asUser_comm[OF neq] take_zip
                                  word_le_nat_alt[of 4, simplified linorder_not_less[symmetric, of 4]]
                                  asUser_return submonad_asUser.fn_stateAssert
                 | rule monadic_rewrite_bind_tail monadic_rewrite_refl
                        monadic_rewrite_symb_exec_l[OF _ stateAssert_inv]
                 | wp)+)+
      apply (case_tac "msgLength tag < scast n_msgRegisters")
       apply (erule disjE[OF word_less_cases],
                 ( clarsimp simp: n_msgRegisters_def asUser_bind_distrib
                                  mapM_x_Cons mapM_x_Nil bind_assoc
                                  zipWithM_x_Nil
                                  asUser_getRegister_discarded
                                  asUser_comm[OF neq] take_zip
                                  bind_comm_mapM_comm [OF asUser_loadWordUser_comm, symmetric]
                                  asUser_return submonad_asUser.fn_stateAssert
                 | rule monadic_rewrite_bind_tail monadic_rewrite_refl
                        monadic_rewrite_symb_exec_l[OF _ mapM_x_mapM_valid[OF mapM_x_wp']]
                        monadic_rewrite_symb_exec_l[OF _ stateAssert_inv]
                        monadic_rewrite_threadGet_return
                        monadic_rewrite_getSanitiseRegisterInfo_return
                 | wp mapM_wp')+)+
      apply (simp add: n_msgRegisters_def word_le_nat_alt n_timeoutMessage_def
                       linorder_not_less timeoutMessage_unfold)
      apply (clarsimp | frule neq0_conv[THEN iffD2, THEN not0_implies_Suc,
                                        OF order_less_le_trans, rotated])+
      apply (subgoal_tac "\<forall>n :: machine_word. n \<le> scast n_timeoutMessage \<longrightarrow> [n .e. msgMaxLength]
                                = [n .e. scast n_timeoutMessage]
                                    @ [scast n_timeoutMessage + 1 .e. msgMaxLength]")
       apply (simp only: upto_enum_word[where y="scast n_timeoutMessage :: machine_word"]
                         upto_enum_word[where y="scast n_timeoutMessage + 1 :: machine_word"])
       apply (clarsimp simp: bind_assoc asUser_bind_distrib asUser_getRegister_threadGet_comm
                             mapM_x_Cons mapM_x_Nil threadGet_discarded
                             asUser_comm [OF neq] asUser_getRegister_discarded
                             submonad_asUser.fn_stateAssert take_zip
                             bind_subst_lift [OF submonad_asUser.stateAssert_fn]
                             word_less_nat_alt RISCV64_H.sanitiseRegister_def
                             split_def n_msgRegisters_def msgMaxLength_def
                             bind_comm_mapM_comm [OF asUser_loadWordUser_comm, symmetric]
                             word_size msgLengthBits_def n_timeoutMessage_def Let_def
                  split del: if_split
                       cong: if_weak_cong register.case_cong)


       apply (rule monadic_rewrite_bind_tail)+
               apply (subst (2) upto_enum_word)
               apply (case_tac "ma < unat n_timeoutMessage - 4")
                apply (erule disjE[OF nat_less_cases'],
                       ( clarsimp simp: n_timeoutMessage_def bind_assoc asUser_bind_distrib
                                        mapM_x_Cons mapM_x_Nil zipWithM_x_mapM_x mapM_Cons
                                        bind_comm_mapM_comm [OF asUser_loadWordUser_comm, symmetric]
                                        asUser_loadWordUser_comm loadWordUser_discarded asUser_return
                                        zip_take_triv2 msgMaxLength_def
                                        no_fail_stateAssert
                                  cong: if_weak_cong
                       | simp
                       | rule monadic_rewrite_bind_tail
                              monadic_rewrite_refl
                              monadic_rewrite_symb_exec_l[OF _ stateAssert_inv]
                              monadic_rewrite_symb_exec_l[OF _ mapM_x_mapM_valid[OF mapM_x_wp']]
                              monadic_rewrite_threadGet_return
                              monadic_rewrite_getSanitiseRegisterInfo_return
                              monadic_rewrite_getSanitiseRegisterInfo_drop
                       | wp empty_fail_loadWordUser)+)+ (* FIXME RT: takes ~10 minutes. See whether this can be improved *)
      apply (clarsimp simp: upto_enum_word word_le_nat_alt simp del: upt.simps cong: if_weak_cong)
      apply (cut_tac i="unat n" and j="Suc (unat (scast n_timeoutMessage :: machine_word))"
                                and k="Suc msgMaxLength" in upt_add_eq_append')
        apply (simp add: n_timeoutMessage_def)
       apply (simp add: n_timeoutMessage_def msgMaxLength_unfold)
      apply (simp add: n_timeoutMessage_def msgMaxLength_def
                       msgLengthBits_def shiftL_nat
                  del: upt.simps upt_rec_numeral)
      apply (simp add: upto_enum_word cong: if_weak_cong)
     apply wp+
    (* ArchFault *)
    apply (simp add: neq inj_case_bool split: bool.split)
   apply (rule monadic_rewrite_guard_imp)
    apply (rule monadic_rewrite_is_refl)
    apply (rule ext)
    apply (unfold handleArchFaultReply'[symmetric] getMRs_def msgMaxLength_def
                  bit_def msgLengthBits_def msgRegisters_unfold
                  fromIntegral_simp1 fromIntegral_simp2 shiftL_word)
    apply (clarsimp simp: mapM_def sequence_def bind_assoc asUser_bind_distrib
                          asUser_return submonad_asUser.fn_stateAssert)
   apply wpsimp+
  done

end

context kernel_m
begin

(* FIXME: move *)
lemma ccorres_merge_return:
  "ccorres (r \<circ> f) xf P P' hs H C \<Longrightarrow>
   ccorres r xf P P' hs (do x \<leftarrow> H; return (f x) od) C"
  by (rule ccorres_return_into_rel)

(* FIXME: move *)
lemma ccorres_break:
  assumes r: "\<And>s s'. \<lbrakk> (s,s') \<in> rf_sr; P s; s' \<in> P' \<rbrakk> \<Longrightarrow> r (Inl e) (xf s')"
  assumes xf: "\<And>s. xf (global_exn_var_'_update (\<lambda>_. Break) s) = xf s"
  shows "ccorres r xf P P' (catchbrk_C#hs) (throwError e) break_C"
  apply (simp add: throwError_def cbreak_def)
  apply (clarsimp simp: ccorres_underlying_def return_def split: xstate.splits)
  apply (frule (2) r)
  apply (rule conjI)
   apply clarsimp
   apply (erule exec_handlers.cases, simp_all)[1]
    apply clarsimp
    apply (erule exec_elim_cases, simp_all)[1]
    apply (erule exec_elim_cases, simp_all)[1]
    apply clarsimp
    apply (erule exec_elim_cases, simp_all)[1]
    apply clarsimp
    apply (erule exec_handlers.cases, simp_all)[1]
     apply (clarsimp simp: catchbrk_C_def)
     apply (erule exec_elim_cases, simp_all)[1]
      apply (erule exec_elim_cases, simp_all)[1]
     apply clarsimp
    apply (clarsimp simp: catchbrk_C_def)
    apply (erule exec_elim_cases, simp_all)[1]
     apply clarsimp
     apply (erule exec_elim_cases, simp_all)[1]
     apply (clarsimp simp: unif_rrel_def xf)
    apply clarsimp
   apply clarsimp
   apply (erule exec_elim_cases, simp_all)[1]
   apply (erule exec_elim_cases, simp_all)[1]
   apply (erule exec_elim_cases, simp_all)[1]
  apply (rule conjI, clarsimp)
   apply (erule exec_handlers.cases, simp_all)[1]
    apply clarsimp
    apply ((erule exec_elim_cases, simp_all)[1])+
    apply (clarsimp simp: catchbrk_C_def)
    apply (erule exec_handlers.cases, simp_all)[1]
     apply (auto elim: exec_elim_cases)[3]
  apply (rule conjI, clarsimp)
   apply (erule exec_handlers.cases, simp_all)[1]
    apply clarsimp
    apply ((erule exec_elim_cases, simp_all)[1])+
    apply (clarsimp simp: catchbrk_C_def)
    apply (erule exec_handlers.cases, simp_all)[1]
     apply (auto elim: exec_elim_cases)[3]
  apply clarsimp
  apply (erule exec_handlers.cases, simp_all)[1]
   apply clarsimp
   apply ((erule exec_elim_cases, simp_all)[1])+
   apply (clarsimp simp: catchbrk_C_def)
   apply (erule exec_handlers.cases, simp_all)[1]
   apply (auto elim!: exec_elim_cases)
  done

(* FIXME: move *)
lemma ccorres_break_return:
  assumes r: "\<And>s s'. \<lbrakk> (s,s') \<in> rf_sr; P s; s' \<in> P' \<rbrakk> \<Longrightarrow> r n (xf s')"
  assumes xf: "\<And>s. xf (global_exn_var_'_update (\<lambda>_. Break) s) = xf s"
  shows "ccorres r xf P P' (catchbrk_C#hs) (return n) break_C"
  apply (simp add: throwError_def cbreak_def)
  apply (clarsimp simp: ccorres_underlying_def return_def split: xstate.splits)
  apply (frule (2) r)
  apply (rule conjI)
   apply clarsimp
   apply (erule exec_handlers.cases, simp_all)[1]
    apply clarsimp
    apply (erule exec_elim_cases, simp_all)[1]
    apply (erule exec_elim_cases, simp_all)[1]
    apply clarsimp
    apply (erule exec_elim_cases, simp_all)[1]
    apply clarsimp
    apply (erule exec_handlers.cases, simp_all)[1]
     apply (clarsimp simp: catchbrk_C_def)
     apply (erule exec_elim_cases, simp_all)[1]
      apply (erule exec_elim_cases, simp_all)[1]
     apply clarsimp
    apply (clarsimp simp: catchbrk_C_def)
    apply (erule exec_elim_cases, simp_all)[1]
     apply clarsimp
     apply (erule exec_elim_cases, simp_all)[1]
     apply (clarsimp simp: unif_rrel_def xf)
    apply clarsimp
   apply clarsimp
   apply (erule exec_elim_cases, simp_all)[1]
   apply (erule exec_elim_cases, simp_all)[1]
   apply (erule exec_elim_cases, simp_all)[1]
  apply (rule conjI, clarsimp)
   apply (erule exec_handlers.cases, simp_all)[1]
    apply clarsimp
    apply ((erule exec_elim_cases, simp_all)[1])+
    apply (clarsimp simp: catchbrk_C_def)
    apply (erule exec_handlers.cases, simp_all)[1]
     apply (auto elim: exec_elim_cases)[3]
  apply (rule conjI, clarsimp)
   apply (erule exec_handlers.cases, simp_all)[1]
    apply clarsimp
    apply ((erule exec_elim_cases, simp_all)[1])+
    apply (clarsimp simp: catchbrk_C_def)
    apply (erule exec_handlers.cases, simp_all)[1]
     apply (auto elim: exec_elim_cases)[3]
  apply clarsimp
  apply (erule exec_handlers.cases, simp_all)[1]
   apply clarsimp
   apply ((erule exec_elim_cases, simp_all)[1])+
   apply (clarsimp simp: catchbrk_C_def)
   apply (erule exec_handlers.cases, simp_all)[1]
   apply (auto elim!: exec_elim_cases)
  done

lemma messageInfoFromWord_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s} Call messageInfoFromWord_'proc {t. seL4_MessageInfo_lift (ret__struct_seL4_MessageInfo_C_' t) =
            \<lparr>label_CL = (w_' s >> 12) && 0xFFFFFFFFFFFFF, capsUnwrapped_CL = (w_' s >> 9) && 7,
                 extraCaps_CL = (w_' s >> 7) && 3, length_CL = let v = w_' s && 0x7F in if v > msgMaxLength then msgMaxLength else v\<rparr>}"
  apply vcg
  apply (simp add: seL4_MessageInfo_lift_def Let_def msgMaxLength_def mask_def word_sle_def
                   word_sless_def seL4_MsgMaxLength_def
         split: if_split)
  done

(* FIXME x64: msgLabelBits change *)
lemma messageInfoFromWord_ccorres [corres]:
  "ccorres (\<lambda>r r'. r = message_info_to_H r') ret__struct_seL4_MessageInfo_C_' \<top> {s. w_' s = w} []
           (return (messageInfoFromWord w)) (Call messageInfoFromWord_'proc)"
  apply (rule ccorres_from_spec_modifies [where P = \<top>, simplified])
      apply (rule messageInfoFromWord_spec)
     apply (rule messageInfoFromWord_modifies)
    apply simp
   apply simp
  apply (simp add: return_def messageInfoFromWord_def Let_def message_info_to_H_def
                   msgLengthBits_def Types_H.msgExtraCapBits_def msgMaxExtraCaps_def
                   shiftL_nat msgMaxLength_def msgLabelBits_def)
  done

lemma getMessageInfo_ccorres:
  "ccorres (\<lambda>r r'. r = message_info_to_H r') ret__struct_seL4_MessageInfo_C_'
           (tcb_at' sender) UNIV hs (getMessageInfo sender)
           (\<acute>ret__unsigned_long :== CALL getRegister(tcb_ptr_to_ctcb_ptr sender,scast Kernel_C.msgInfoRegister);;
            \<acute>ret__struct_seL4_MessageInfo_C :== CALL messageInfoFromWord(\<acute>ret__unsigned_long))"
  unfolding getMessageInfo_def
  apply simp
  apply (rule ccorres_guard_imp2)
  apply ctac
  apply ctac
    apply wp
   apply vcg
  apply (frule (1) obj_at_cslift_tcb)
  apply (clarsimp simp: typ_heap_simps RISCV64_H.msgInfoRegister_def RISCV64.msgInfoRegister_def
    Kernel_C.msgInfoRegister_def Kernel_C.a1_def dest!: c_guard_clift)
  done

lemma getMessageInfo_ccorres':
  "ccorres (\<lambda>r r'. r = message_info_to_H r') tag_'
           (tcb_at' sender) UNIV hs (getMessageInfo sender)
           (\<acute>ret__unsigned_long :== CALL getRegister(tcb_ptr_to_ctcb_ptr sender,scast Kernel_C.msgInfoRegister);;
            \<acute>tag :== CALL messageInfoFromWord(\<acute>ret__unsigned_long))"
  unfolding getMessageInfo_def
  apply simp
  apply (rule ccorres_guard_imp2)
  apply ctac
  apply ctac
    apply wp
   apply vcg
  apply (frule (1) obj_at_cslift_tcb)
  apply (clarsimp simp: typ_heap_simps RISCV64_H.msgInfoRegister_def RISCV64.msgInfoRegister_def
    Kernel_C.msgInfoRegister_def Kernel_C.a1_def  dest!: c_guard_clift)
  done

lemma replyFromKernel_success_empty_ccorres [corres]:
  "ccorres dc xfdc \<top> (UNIV \<inter> \<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr thread\<rbrace>) hs
     (replyFromKernel thread (0, []))
     (Call replyFromKernel_success_empty_'proc)"
  apply (subst replyFromKernel_success_empty)
  apply (cinit lift: thread_')
   apply (rule ccorres_symb_exec_l [OF _ _ _ empty_fail_lookupIPCBuffer])
     apply (ctac add: setRegister_ccorres)
       apply (unfold setMessageInfo_def)
       apply csymbr
       apply ctac
         apply (simp only: fun_app_def)
         apply (ctac add: setRegister_ccorres)
        apply wp
       apply vcg
      apply wp
     apply vcg
    apply wp+
  apply (simp add: RISCV64_H.msgInfoRegister_def RISCV64.msgInfoRegister_def
                   Kernel_C.msgInfoRegister_def RISCV64.capRegister_def
                   RISCV64_H.badgeRegister_def RISCV64.badgeRegister_def
                   Kernel_C.badgeRegister_def message_info_to_H_def C_register_defs)
  done

lemma msgRegisters_offset_conv:
  "\<And>offset i. \<lbrakk> offset + i < length RISCV64_H.msgRegisters \<rbrakk> \<Longrightarrow>
   index msgRegistersC (unat ((of_nat offset :: machine_word) + of_nat i)) =
   register_from_H (RISCV64_H.msgRegisters ! (offset + i))"
  apply (simp add: msgRegistersC_def msgRegisters_unfold fupdate_def)
  apply (subst of_nat_add [symmetric])
  apply (case_tac "offset + i", simp_all del: of_nat_add)
  apply (case_tac nat, simp, rename_tac nat, simp)+
  done

lemmas ccorres_pre_stateAssert =
         ccorres_symb_exec_l [OF _ stateAssert_inv stateAssert_wp
                                 empty_fail_stateAssert]

declare setRegister_ccorres[corres]

lemma setMR_ccorres:
  notes if_cong[cong]
  notes unat_of_nat32 = unat_of_nat_eq[where 'a=32, unfolded word_bits_len_of]
  shows
  "ccorres
     (\<lambda>r r'. r = unat (r' && mask msgLengthBits)
             \<and> (offset < length msgRegisters \<longrightarrow> r' = word_of_nat offset + 1))
     ret__unsigned_'
     (valid_pspace' and  case_option \<top> valid_ipc_buffer_ptr' buf
           and (\<lambda>s. offset < msgMaxLength))
     (UNIV \<inter> {s. offset_' s = of_nat offset} \<inter> {s. reg___unsigned_long_' s = v}
             \<inter> {s. receiver_' s = tcb_ptr_to_ctcb_ptr thread}
             \<inter> {s. receiveIPCBuffer_' s = option_to_ptr buf}) []
     (setMR thread buf offset v) (Call setMR_'proc)"
  apply (rule ccorres_gen_asm)
  apply (cinit lift: offset_' reg___unsigned_long_' receiver_' receiveIPCBuffer_')
   apply (rule ccorres_cond2'[where R=\<top>])
     apply (clarsimp simp add: msgRegisters_unfold n_msgRegisters_def Collect_const_mem
                      linorder_not_less word_le_nat_alt unat_of_nat32
                      word_bits_def msgMaxLength_unfold)
     apply arith
    apply wpc
     apply (simp add: option_to_ptr_def option_to_0_def Collect_False
                      ccorres_cond_iffs
                 del: Collect_const)
     apply (rule ccorres_return_C, simp+)[1]
    apply (simp add: option_to_ptr_def option_to_0_def Collect_True
                     ccorres_cond_iffs
                del: Collect_const ptr_add_def')
    apply (rule ccorres_cond_true)
    apply (rule ccorres_split_nothrow_novcg)
        apply (rule ccorres_move_array_assertion_ipc_buffer
               | (rule ccorres_flip_Guard, rule ccorres_move_array_assertion_ipc_buffer))+
        apply (rule storeWordUser_ccorres)
       apply ceqv
      apply (rule ccorres_return_C, simp+)[1]
     apply wp
    apply (clarsimp simp: guard_is_UNIV_def Collect_const_mem)
    apply (simp add: msgLengthBits_def msgMaxLength_def
                     unat_arith_simps less_mask_eq unat_of_nat
                del: Collect_const)
   apply ctac
     apply (rule ccorres_return_C, simp+)[1]
    apply wp
   apply (simp del: Collect_const)
   apply (vcg exspec=setRegister_modifies)
  supply Word.of_int_uint[simp del]
  apply (simp add: Collect_const_mem option_to_0_def
                   unat_gt_0 option_to_ptr_def)
  apply (intro impI conjI allI; simp?)
           apply (clarsimp simp: valid_ipc_buffer_ptr'_def)
           apply (erule aligned_add_aligned)
            apply (simp only: word_size_def is_aligned_mult_triv2[where n=3, simplified])
           apply (simp add: msg_align_bits_def word_size_bits_def)
          apply (simp add: n_msgRegisters_def length_msgRegisters msgLengthBits_def mask_def)
         apply (simp add: unat_of_nat length_msgRegisters n_msgRegisters_def word_le_nat_alt)
        apply (simp add: msg_align_bits word_size_def msgMaxLength_def unat_of_nat
                         length_msgRegisters n_msgRegisters_def uint_nat unat_word_ariths)
       apply (simp add: unat_word_ariths msg_align_bits msgMaxLength_def unat_of_nat)
      apply (simp add: unat_word_ariths msg_align_bits msgMaxLength_def unat_of_nat)
     apply (fastforce simp: valid_ipc_buffer_ptr'_def)
    apply (simp add: unat_of_nat32 word_bits_def msgMaxLength_unfold
                     word_le_nat_alt msgRegisters_ccorres n_msgRegisters_def)
   apply (simp add: unat_of_nat32 msgMaxLength_unfold word_bits_def
                    unat_add_lem[THEN iffD1] less_mask_eq msgLengthBits_def
                    word_less_nat_alt)
  apply (simp add: linorder_not_le n_msgRegisters_def)
  done

lemma setMR_ccorres_dc:
  "ccorres dc xfdc
     (valid_pspace' and  case_option \<top> valid_ipc_buffer_ptr' buf
           and (\<lambda>s. offset < msgMaxLength))
     (UNIV \<inter> {s. offset_' s = of_nat offset} \<inter> {s. reg___unsigned_long_' s = v}
             \<inter> {s. receiver_' s = tcb_ptr_to_ctcb_ptr thread}
             \<inter> {s. receiveIPCBuffer_' s = option_to_ptr buf}) []
     (setMR thread buf offset v) (Call setMR_'proc)"
  by (rule ccorres_rel_imp, rule setMR_ccorres, simp)

end

(* FIXME: move *)
context begin interpretation Arch . (*FIXME: arch-split*)
crunch setMR
  for valid_pspace'[wp]: "valid_pspace'"
crunch setMR
  for valid_ipc_buffer_ptr'[wp]: "valid_ipc_buffer_ptr' p"
end

context kernel_m begin

lemma setMRs_lookup_failure_ccorres:
  notes unat_of_nat32 = unat_of_nat_eq[where 'a=32, unfolded word_bits_len_of]
  shows
  "ccorres (\<lambda>r r'. r \<noteq> [] \<and> last r = unat (r' && mask msgLengthBits))
           ret__unsigned_'
     (valid_pspace'
               and (case buf of None \<Rightarrow> \<top> | Some x \<Rightarrow> valid_ipc_buffer_ptr' x)
               and (\<lambda>_. n + length (msgFromLookupFailure lf) < msgMaxLength))
           (UNIV \<inter> \<lbrace>\<acute>receiver = tcb_ptr_to_ctcb_ptr thread\<rbrace>
                 \<inter> \<lbrace>\<acute>receiveIPCBuffer = option_to_ptr buf\<rbrace>
                 \<inter> \<lbrace>map_option lookup_fault_to_H
                        (lookup_fault_lift \<acute>luf) = Some lf\<rbrace>
                 \<inter> \<lbrace>n = unat \<acute>offset\<rbrace>) hs
    (mapM (\<lambda>(x, y). setMR thread buf x y)
        (zip [n ..< msgMaxLength] (msgFromLookupFailure lf)))
    (Call setMRs_lookup_failure_'proc)"
  apply (rule ccorres_gen_asm)+
  apply (cinit' lift: receiver_' receiveIPCBuffer_' luf_' offset_')
   apply csymbr
   apply (rule_tac P="valid_pspace'
                  and (case buf of None \<Rightarrow> \<top> | Some x \<Rightarrow> valid_ipc_buffer_ptr' x)" and P'=UNIV
                in ccorres_inst)
   apply (clarsimp simp: msgFromLookupFailure_def lookup_fault_lift_def
                         Let_def zip_upt_Cons msgMaxLength_unfold
                         mapM_Cons mapM_Nil bind_assoc
               simp del: Collect_const
                  split: if_split_asm)
      apply (rule ccorres_guard_imp2)
       apply csymbr
       apply csymbr
       apply (ctac add: setMR_ccorres)
         apply csymbr
         apply (ccorres_rewrite)
         apply (simp add: ccorres_cond_iffs)
         apply (rule ccorres_return_C, simp+)[1]
        apply wp
       apply (simp del: Collect_const)
       apply (vcg exspec=setMR_modifies)
      apply (clarsimp simp: msgMaxLength_unfold Collect_const_mem)
      apply (simp add: lookup_fault_tag_defs)
     apply (rule ccorres_guard_imp2)
      apply csymbr
      apply csymbr
      apply (ctac add: setMR_ccorres)
        apply csymbr
        apply (simp add: ccorres_cond_iffs)
        apply (ccorres_rewrite)
        apply (rule ccorres_rhs_assoc)+
        apply csymbr
        apply (ctac add: setMR_ccorres)
          apply (rule ccorres_return_C, simp+)[1]
         apply wp
        apply simp
        apply (vcg exspec=setMR_modifies)
       apply (wp hoare_case_option_wp)
      apply (simp add: Collect_const_mem)
      apply (vcg exspec=setMR_modifies)
     apply (clarsimp simp: msgMaxLength_unfold Collect_const_mem)
     apply (simp add: lookup_fault_missing_capability_lift_def
                      lookup_fault_lift_missing_capability)
     apply (simp add: lookup_fault_tag_defs)
    apply (rule ccorres_guard_imp2)
     apply csymbr
     apply csymbr
     apply (ctac add: setMR_ccorres)
       apply (simp add: ccorres_cond_iffs)
       apply csymbr
       apply (ccorres_rewrite)
       apply (rule ccorres_rhs_assoc)+
       apply csymbr
       apply (ctac add: setMR_ccorres_dc)
         apply csymbr
         apply (ctac add: setMR_ccorres)
           apply (rule ccorres_return_C, simp+)[1]
          apply wp
         apply simp
         apply (vcg exspec=setMR_modifies)
        apply (wp hoare_case_option_wp)
       apply (simp add: Collect_const_mem)
       apply (vcg exspec=setMR_modifies)
      apply (wp hoare_case_option_wp)
     apply (simp add: Collect_const_mem)
     apply (vcg exspec=setMR_modifies)
    apply (clarsimp simp: msgMaxLength_unfold Collect_const_mem)
    apply (simp add: lookup_fault_depth_mismatch_lift_def
                     lookup_fault_lift_depth_mismatch)
    apply (simp add: lookup_fault_tag_defs)
   apply (rule ccorres_guard_imp2)
    apply csymbr
    apply csymbr
    apply (ctac add: setMR_ccorres)
      apply csymbr
      apply (simp add: ccorres_cond_iffs)
      apply (ccorres_rewrite)
      apply (rule ccorres_rhs_assoc)+
      apply csymbr
      apply (ctac add: setMR_ccorres_dc)
        apply csymbr
        apply (ctac add: setMR_ccorres_dc)
          apply csymbr
          apply (ctac add: setMR_ccorres)
            apply (rule ccorres_return_C, simp+)[1]
           apply (wp hoare_case_option_wp
              | (simp add: Collect_const_mem, vcg exspec=setMR_modifies))+
   apply (clarsimp simp: msgMaxLength_unfold Collect_const_mem)
   apply (simp add: lookup_fault_guard_mismatch_lift_def
                    lookup_fault_lift_guard_mismatch)
   apply (simp add: lookup_fault_tag_defs)
  apply simp
  done

lemma setMRs_syscall_error_ccorres:
  "ccorres (\<lambda>r r'. r = r' && mask msgLengthBits) ret__unsigned_long_'
     (valid_pspace'
               and (case buf of None \<Rightarrow> \<top> | Some x \<Rightarrow> valid_ipc_buffer_ptr' x)
               and (\<lambda>_. msg = snd (msgFromSyscallError err)))
           (UNIV \<inter> \<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr thread\<rbrace>
                 \<inter> \<lbrace>\<acute>receiveIPCBuffer = option_to_ptr buf\<rbrace>
                 \<inter> \<lbrace>syscall_error_to_H \<acute>current_syscall_error
                          (lookup_fault_lift \<acute>current_lookup_fault)
                       = Some err\<rbrace>) hs
     (setMRs thread buf msg)
     (Call setMRs_syscall_error_'proc)"
  (is "ccorres ?r ret__unsigned_long_' ?P ?P' hs ?a ?c")
  apply (rule ccorres_gen_asm)
  apply (cinit')
   apply (rule_tac xf' = "\<lambda>s. current_syscall_error_' (globals s)"
                in ccorres_abstract)
    apply (rule ceqv_rules, rule rewrite_xfI,  simp,  rule ceqv_refl)+
    apply (rule ceqv_refl)
   apply (rename_tac err')
   apply (rule_tac xf' = "\<lambda>s. current_lookup_fault_' (globals s)"
                in ccorres_abstract)
    apply (rule ceqv_rules, rule rewrite_xfI,  simp,  rule ceqv_refl)+
    apply (rule ceqv_refl)
   apply (rename_tac luf')
   apply (rule_tac P="Some err = syscall_error_to_H err' (lookup_fault_lift luf')"
                in ccorres_gen_asm2)
   apply (rule_tac A="?P" and A'="?P'" in ccorres_guard_imp2)
    apply (simp add: setMRs_to_setMR del: Collect_const)
    apply (rule ccorres_stateAssert)
    apply (rule ccorres_Cond_rhs[rotated])+
            apply (rule ccorres_inst[where P=\<top> and P'=UNIV])
            apply simp
           apply (rule ccorres_inst[where P=\<top> and P'=UNIV])
           apply (simp add: syscall_error_to_H_def)
          apply (simp_all add: syscall_error_to_H_def msgFromSyscallError_def
                               zipWithM_mapM mapM_Nil mapM_Cons
                               msgMaxLength_unfold zip_upt_Cons bind_assoc)
           apply (ctac add:setMR_ccorres)
             apply (rule ccorres_return_C,simp+)[1]
            apply (wp | (simp add: Collect_const_mem,
              vcg exspec=setMR_modifies exspec=setMRs_lookup_failure_modifies))+
          apply (subgoal_tac "msg = []")
           apply (simp add: zipWithM_mapM mapM_Nil)
           apply (rule ccorres_return_C, simp+)[1]
          apply (simp split: if_split_asm)
         apply (subgoal_tac "err = FailedLookup (to_bool (failedLookupWasSource_C err'))
                                      (lookup_fault_to_H (the (lookup_fault_lift luf')))")
          apply (simp add: zip_upt_Cons mapM_Cons bind_assoc)
          apply (rule ccorres_rhs_assoc)+
          apply (ctac add: setMR_ccorres_dc)
            apply (ctac add: setMRs_lookup_failure_ccorres[unfolded msgMaxLength_unfold])
              apply (rule ccorres_return_C, simp+)[1]
             apply (wp hoare_case_option_wp
                | (simp add: Collect_const_mem,
                          vcg exspec=setMR_modifies exspec=setMRs_lookup_failure_modifies))+
        apply (clarsimp simp: map_option_Some_eq2)
       apply (rule ccorres_return_C, simp+)[1]
      apply (rule ccorres_rhs_assoc
                 | (rule ccorres_inst, ctac add: setMR_ccorres_dc)
                 | (rule ccorres_inst, ctac add: setMR_ccorres)
                 | (rule ccorres_return_C, simp+)[1]
                 | wp hoare_case_option_wp
                 | (simp del: Collect_const, vcg exspec=setMR_modifies)
               )+
   apply (simp add: msgMaxLength_unfold)
   apply (clarsimp split:if_split_asm simp:syscall_error_to_H_def map_option_Some_eq2 ucast_and_mask ucast_nat_def)
   apply (simp add: msgFromLookupFailure_def
                 split: lookup_failure.split
            | simp add: to_bool_def split: if_split)+
  done

lemma lookupIPCBuffer_aligned_option_to_0:
  "\<lbrace>valid_objs'\<rbrace> lookupIPCBuffer b s \<lbrace>\<lambda>rv s. is_aligned (option_to_0 rv) msg_align_bits\<rbrace>"
  apply (rule hoare_strengthen_post, rule lookupIPCBuffer_valid_ipc_buffer)
  apply (simp add: option_to_0_def valid_ipc_buffer_ptr'_def split: option.split_asm)
  done

lemma Cond_if_mem:
   "(Cond (if P then UNIV else {})) = (Cond {s. P})"
   by simp

lemma copyMRs_register_loop_helper:
  fixes n
  defines regs: "regs \<equiv> take (unat n) RISCV64_H.msgRegisters"
  shows
  "\<forall>i. i<length regs \<longrightarrow>
   ccorres dc xfdc \<top> \<lbrace>\<acute>i = of_nat i\<rbrace> hs
     (do v \<leftarrow> asUser sender (getRegister (regs ! i));
         asUser receiver (setRegister (regs ! i) v)
      od)
     (Guard ArrayBounds \<lbrace>\<acute>i < 4\<rbrace>
      (\<acute>ret__unsigned_long :== CALL getRegister(tcb_ptr_to_ctcb_ptr sender,
               ucast (index msgRegistersC (unat \<acute>i))));;
      Guard ArrayBounds \<lbrace>\<acute>i < 4\<rbrace>
      (CALL setRegister(tcb_ptr_to_ctcb_ptr receiver,
               ucast (index msgRegistersC (unat \<acute>i)),
               \<acute>ret__unsigned_long)))"
  apply clarsimp
  apply (rule ccorres_guard_imp)
    apply ctac
      apply ctac
     apply wp
    apply vcg
   apply simp
  apply (clarsimp simp: regs msgRegistersC_def msgRegisters_unfold)
  apply (simp |
         (case_tac i,
          clarsimp simp: fupdate_def index_update index_update2 C_register_defs,
          rename_tac i))+
  done


(* FIXME move *)
lemma copyMRs_ccorres [corres]:
notes
  wordSize_def'[simp]
shows
  "ccorres (\<lambda>r r'. r = r' && mask msgLengthBits) ret__unsigned_long_'
    (valid_pspace' and tcb_at' sender and tcb_at' receiver
        and (case sendBuffer of None \<Rightarrow> \<top> | Some x \<Rightarrow> valid_ipc_buffer_ptr' x)
        and (case recvBuffer of None \<Rightarrow> \<top> | Some x \<Rightarrow> valid_ipc_buffer_ptr' x)
        and K (sendBuffer \<noteq> Some 0) and K (recvBuffer \<noteq> Some 0)
        and K (unat n \<le> msgMaxLength))
    (UNIV \<inter> \<lbrace>\<acute>n = \<acute>n && mask msgLengthBits \<and> \<acute>n = n\<rbrace>
          \<inter> \<lbrace>\<acute>sendBuf = Ptr (option_to_0 sendBuffer)\<rbrace>
          \<inter> \<lbrace>\<acute>recvBuf = Ptr (option_to_0 recvBuffer)\<rbrace>
          \<inter> \<lbrace>\<acute>sender = tcb_ptr_to_ctcb_ptr sender\<rbrace>
          \<inter> \<lbrace>\<acute>receiver = tcb_ptr_to_ctcb_ptr receiver\<rbrace>) []
    (copyMRs sender sendBuffer receiver recvBuffer n)
    (Call copyMRs_'proc)"
  apply (unfold K_def, intro ccorres_gen_asm)
  apply (cinit lift: n_' sendBuf_' recvBuf_' sender_' receiver_'
               simp: whileAnno_def)
   apply (simp only: mapM_discarded)
   apply (rule ccorres_rhs_assoc2)
   apply (rule_tac P = "length (take (unat n) RISCV64_H.msgRegisters) <
                        2 ^ word_bits"
                in ccorres_gen_asm)
   apply (rule ccorres_split_nothrow_novcg)
       apply (rule ccorres_mapM_x_while [OF copyMRs_register_loop_helper[unfolded ucast_id]])
          apply (clarsimp simp: n_msgRegisters_def
                                length_msgRegisters min_def
                         split: if_split)
          apply unat_arith
         apply vcg
         apply simp
        apply wp
       apply assumption
      apply ceqv
     apply (wpc, simp add: option_to_0_def)
      apply (rule ccorres_split_throws, rule ccorres_return_C, simp+)
      apply vcg
     apply (wpc, simp_all add: option_to_0_def)[1]
      apply (rule ccorres_split_throws, rule ccorres_return_C, simp+)
      apply vcg
     apply (subst mapM_only_length)
     apply (rule_tac P="unat n \<le> length RISCV64_H.msgRegisters" in ccorres_cases)
      apply (simp add: upto_enum_def length_msgRegisters n_msgRegisters_def
                       mapM_x_Nil)
      apply (rule ccorres_expand_while_iff_Seq[THEN iffD1])
      apply (rule ccorres_cond_false)
      apply (rule ccorres_return_C, simp+)
     apply (rule ccorres_split_nothrow_novcg)
         apply (rule_tac i="length RISCV64_H.msgRegisters"
               and F="\<lambda>_. valid_ipc_buffer_ptr' (the sendBuffer)
                 and valid_ipc_buffer_ptr' (the recvBuffer)
                 and valid_pspace'"
               in ccorres_mapM_x_while')
             apply clarsimp
             apply (rule ccorres_guard_imp)
               apply (rule ccorres_pre_loadWordUser)
               apply (unfold storeWordUser_def)
               apply (rule ccorres_pre_stateAssert)
               apply (unfold K_bind_def)
               apply (rule ccorres_move_array_assertion_ipc_buffer
                           ccorres_Guard[where S="{s. h_t_valid (htd s) c_guard (ptr s)}" for ptr htd])+
               apply (ctac add: storeWord_ccorres)
              apply (clarsimp simp: word_size valid_ipc_buffer_ptr'_def
                                    msg_align_bits
                                    aligned_add_aligned[OF _ is_aligned_mult_triv2[where n=3, simplified]])
             apply (clarsimp simp: msgRegisters_unfold upto_enum_word word_size
                                   pointerInUserData_h_t_valid pointerInUserData_c_guard
                                   typ_heap_simps'
                split: if_split_asm simp del: upt.simps)
             apply (simp only: unat_arith_simps unat_of_nat msg_align_bits
                               msgMaxLength_def, simp split: if_split)
             apply arith
            apply (simp add: n_msgRegisters_def length_msgRegisters)
           apply (rule allI, rule conseqPre, vcg)
           apply clarsimp
          apply (rule hoare_pre, wpsimp wp: hoare_valid_ipc_buffer_ptr_typ_at')
          apply clarsimp
         apply (simp add: length_msgRegisters n_msgRegisters_def msgMaxLength_def
                          word_bits_def)
        apply ceqv
       apply simp
       apply (rule ccorres_return_C, simp_all)[1]
      apply wp
     apply clarsimp
     apply (clarsimp simp: guard_is_UNIV_def upto_enum_def
                           min_def word_le_nat_alt
                           length_msgRegisters n_msgRegisters_def
                           msgLengthBits_def mask_def
                           linorder_not_le)
    apply simp
    apply (wp mapM_x_wp' hoare_vcg_all_lift hoare_vcg_const_imp_lift | simp)+
   apply (clarsimp simp: guard_is_UNIV_def
                         length_msgRegisters n_msgRegisters_def mask_def
                         Types_H.msgLengthBits_def min_def word_le_nat_alt
                  split: if_split)
   apply unat_arith
  apply (clarsimp simp: length_msgRegisters n_msgRegisters_def
                        msgLengthBits_def min_def word_bits_def)
  apply (auto split: if_split)
  done

lemma getRestartPC_ccorres [corres]:
  "ccorres (=) ret__unsigned_long_' \<top>
     (UNIV \<inter> \<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr thread\<rbrace>) hs
     (asUser thread (getRegister register.FaultIP))
     (Call getRestartPC_'proc)"
  apply (cinit' lift: thread_')
   apply (rule ccorres_trim_return, simp, simp)
   apply ctac
  apply clarsimp
  done

lemma asUser_tcbFault_obj_at:
  "asUser t' m \<lbrace>obj_at' (\<lambda>tcb. P (tcbFault tcb)) t\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp threadGet_wp)
  apply (clarsimp simp: if_cong obj_at_simps)
  done

lemma asUser_atcbContext_obj_at:
  "t \<noteq> t' \<Longrightarrow> asUser t' m \<lbrace>obj_at' (\<lambda>tcb. P ((atcbContextGet o tcbArch) tcb)) t\<rbrace>"
  apply (simp add: asUser_def split_def atcbContextGet_def atcbContextSet_def)
  apply (wp threadGet_wp)
  apply (fastforce simp: obj_at_simps)
  done

lemma asUser_tcbFault_inv:
  "\<lbrace>\<lambda>s. \<exists>t. ko_at' t p' s \<and> tcbFault t = f\<rbrace> asUser p m
   \<lbrace>\<lambda>rv s. \<exists>t. ko_at' t p' s \<and> tcbFault t = f\<rbrace>"
  apply (rule_tac Q'="\<lambda>rv. obj_at' (\<lambda>t. tcbFault t = f) p'"
               in hoare_strengthen_post)
   apply (wp asUser_tcbFault_obj_at)
   apply (clarsimp simp: obj_at'_def)+
  done

lemma setMR_atcbContext_obj_at:
  "t \<noteq> t' \<Longrightarrow>
    \<lbrace>obj_at' (\<lambda>tcb. P ((atcbContextGet o tcbArch) tcb)) t\<rbrace>
      setMR t' b r v
    \<lbrace>\<lambda>rv. obj_at' (\<lambda>tcb. P ((atcbContextGet o tcbArch) tcb)) t\<rbrace>"
  apply (simp add: setMR_def)
  apply (rule hoare_pre)
   apply (wp asUser_atcbContext_obj_at[simplified] | simp | wpc)+
  done

lemma setMR_tcbFault_obj_at:
  "\<lbrace>obj_at' (\<lambda>tcb. P (tcbFault tcb)) t\<rbrace> setMR t' b r v
   \<lbrace>\<lambda>rv. obj_at' (\<lambda>tcb. P (tcbFault tcb)) t\<rbrace>"
  apply (simp add: setMR_def)
  apply (rule hoare_pre)
   apply (wp asUser_tcbFault_obj_at | wpc)+
  apply simp
  done

lemma ccorres_add_getRegister:
  "ccorres rv xf P P' hs (asUser t (getRegister r) >>= (\<lambda>_. a)) c
    \<Longrightarrow> ccorres rv xf (P and tcb_at' t) P' hs a c"
  apply (simp add: asUser_getRegister_discarded)
  apply (simp add: ccorres_underlying_def)
  apply (elim ballEI | clarsimp del: allI)+
  apply (drule mp)
   apply (simp add: stateAssert_def bind_assoc exec_get)
  apply (elim allEI)
  apply (clarsimp simp: in_monad stateAssert_def split: xstate.split_asm)
  apply fastforce
  done

lemma exceptionMessage_ccorres:
  "n < unat n_exceptionMessage
      \<Longrightarrow> register_from_H (RISCV64_H.exceptionMessage ! n)
             = index exceptionMessageC n"
  apply (simp add: exceptionMessageC_def RISCV64_H.exceptionMessage_def
                   RISCV64.exceptionMessage_def MessageID_Exception_def)
  by (simp add: Arrays.update_def n_exceptionMessage_def fcp_beta nth_Cons'
                fupdate_def C_register_defs
         split: if_split) (* long *)

lemma asUser_obj_at_elsewhere:
  "\<lbrace>obj_at' (P :: tcb \<Rightarrow> bool) t' and (\<lambda>_. t \<noteq> t')\<rbrace> asUser t m \<lbrace>\<lambda>rv. obj_at' P t'\<rbrace>"
  apply (rule hoare_gen_asm')
  apply (simp add: asUser_def split_def)
  apply (wp threadGet_wp)
  apply (fastforce simp: obj_at_simps)
  done

lemma exceptionMessage_length_aux :
  "\<And>n. n < length RISCV64_H.exceptionMessage \<Longrightarrow> n < unat n_exceptionMessage"
  by (simp add: RISCV64.exceptionMessage_def RISCV64_H.exceptionMessage_def n_exceptionMessage_def)

lemma copyMRsFault_ccorres_exception:
  "ccorres dc xfdc
           (valid_pspace'
             and obj_at' (\<lambda>tcb. map (user_regs (atcbContext (tcbArch tcb))) exceptionMessage = msg) sender
             and K (length msg = 2)
             and K (recvBuffer \<noteq> Some 0)
             and K (sender \<noteq> receiver))
           (UNIV \<inter> \<lbrace>\<acute>sender = tcb_ptr_to_ctcb_ptr sender\<rbrace>
                 \<inter> \<lbrace>\<acute>receiver = tcb_ptr_to_ctcb_ptr receiver\<rbrace>
                 \<inter> \<lbrace>\<acute>receiveIPCBuffer = Ptr (option_to_0 recvBuffer)\<rbrace>
                 \<inter> \<lbrace> \<acute>length___unsigned_long = 2 \<rbrace>
                 \<inter> \<lbrace> \<acute>id___anonymous_enum = MessageID_Exception \<rbrace>)
           hs
           (mapM_x (\<lambda>(x, y). setMR receiver recvBuffer x y) (zip [0..<120] msg))
           (Call copyMRsFault_'proc)"
  apply (unfold K_def)
  apply (intro ccorres_gen_asm)
  apply (cinit' lift: sender_' receiver_' receiveIPCBuffer_'
                     length___unsigned_long_' id___anonymous_enum_'
                simp: whileAnno_def)
   apply (simp only: mapM_x_append[where xs="take (unat n_msgRegisters) (zip as bs)"
                                         and ys="drop (unat n_msgRegisters) (zip as bs)"
                                         for as bs, simplified] bind_assoc)
   apply (rule ccorres_rhs_assoc2, rule ccorres_split_nothrow_novcg)

       apply (rule_tac F="K $ obj_at' (\<lambda>tcb. map ((user_regs o atcbContext o tcbArch) tcb) RISCV64_H.exceptionMessage = msg) sender"
                     in ccorres_mapM_x_while)
           apply (clarsimp simp: n_msgRegisters_def)
           apply (rule ccorres_guard_imp2)
            apply (rule_tac t=sender and r="RISCV64_H.exceptionMessage ! n"
                            in ccorres_add_getRegister)
            apply (ctac(no_vcg))
             apply (rule_tac P="\<lambda>s. rv = msg ! n" in ccorres_cross_over_guard)
             apply (simp add: setMR_def length_msgRegisters n_msgRegisters_def
                                    liftM_def[symmetric])
             apply ctac
            apply (wp user_getreg_rv)
           apply (clarsimp simp: msgRegisters_ccorres n_msgRegisters_def
                                 syscallMessage_ccorres n_syscallMessage_def
                                 obj_at'_def projectKOs
                                 atcbContextGet_def unat_of_nat64[unfolded word_bits_def])
           apply (clarsimp simp: exceptionMessage_ccorres[simplified,symmetric,OF exceptionMessage_length_aux])
           apply (clarsimp simp: word_of_nat_less MessageID_Exception_def)
          apply (clarsimp simp: n_msgRegisters_def foo)
         apply (rule allI, rule conseqPre, vcg exspec=setRegister_modifies exspec=getRegister_modifies)
         apply simp
        apply (simp add: setMR_def)
        apply (rule hoare_pre)
         apply (wp asUser_obj_at_elsewhere | wpc)+
        apply simp
       apply (simp add: word_bits_def)
      apply ceqv
     apply (rule ccorres_Cond_rhs)
      apply (simp del: Collect_const)
      apply (simp add: n_msgRegisters_def mapM_x_Nil)
      apply (subst ccorres_expand_while_iff[symmetric])
      apply (rule ccorres_cond_false)
      apply (rule ccorres_return_Skip')
     apply (simp add: n_msgRegisters_def mapM_x_Nil)
     apply (rule ccorres_return_Skip')
    apply wp
    apply (simp add: guard_is_UNIV_def)
    apply (clarsimp)
    done

lemma mapM_cong: "\<lbrakk> \<forall>x. elem x xs \<longrightarrow> f x = g x \<rbrakk> \<Longrightarrow> mapM_x f xs =  mapM_x g xs"
  by (induction xs, (simp add: mapM_x_Nil mapM_x_Cons)+)


lemma copyMRsFault_ccorres_syscall:
  "ccorres dc xfdc
           (valid_pspace'
             and obj_at' (\<lambda>tcb. map (user_regs (atcbContext (tcbArch tcb))) syscallMessage = msg) sender
             and (case recvBuffer of Some x \<Rightarrow> valid_ipc_buffer_ptr' x | None \<Rightarrow> \<top>)
             and K (length msg = 10) \<comment> \<open>length RISCV64.syscallMessage\<close>
             and K (recvBuffer \<noteq> Some 0)
             and K (sender \<noteq> receiver))
           (UNIV \<inter> \<lbrace>\<acute>sender = tcb_ptr_to_ctcb_ptr sender\<rbrace>
                 \<inter> \<lbrace>\<acute>receiver = tcb_ptr_to_ctcb_ptr receiver\<rbrace>
                 \<inter> \<lbrace>\<acute>receiveIPCBuffer = Ptr (option_to_0 recvBuffer)\<rbrace>
                 \<inter> \<lbrace>\<acute>length___unsigned_long = 10 \<rbrace> \<comment> \<open>length RISCV64.syscallMessage\<close>
                 \<inter> \<lbrace> \<acute>id___anonymous_enum = MessageID_Syscall \<rbrace>)
           hs
           (mapM_x (\<lambda>(x, y). setMR receiver recvBuffer x y) (zip [0..<120] msg))
           (Call copyMRsFault_'proc)"
proof -
  (* auxiliary lemmas *)
  have option_to_0_imp : "\<lbrakk> option_to_0 recvBuffer= 0 ; recvBuffer \<noteq> Some 0 \<rbrakk> \<Longrightarrow> recvBuffer = None"
    by (simp add: option_to_0_def; cases recvBuffer; simp+)
  have drop_n: "\<And>n m. drop n [0..<m] = [n..<m]"
    by simp
  have less_than_4: "\<And>x y n m. elem (x, y) (zip [n..<120] m) \<Longrightarrow> \<not> x < n "
    by (simp | erule in_set_zipE)+
  have msg_aux: "\<forall>p. elem p (zip [4..<120] (drop 4 msg))
                    \<longrightarrow> (\<lambda>(x1,y1). setMR receiver None x1 y1) p = (\<lambda>_ . return (length msgRegisters)) p"
    by (fastforce simp add: numeral_eqs setMR_def less_than_4 n_msgRegisters_def length_msgRegisters
                            take_bit_Suc
                  simp del: unsigned_numeral)
  have mapM_x_return_gen: "\<And>v w xs. mapM_x (\<lambda>_. return v) xs = return w" (* FIXME mapM_x_return *)
    by (induct_tac xs; simp add: mapM_x_Nil mapM_x_Cons)
  show ?thesis
  including no_pre
  apply (unfold K_def)
  apply (intro ccorres_gen_asm)
  apply (cinit' lift: sender_' receiver_' receiveIPCBuffer_'
                     length___unsigned_long_' id___anonymous_enum_'
                simp: whileAnno_def)
   apply (simp only: mapM_x_append[where xs="take (unat n_msgRegisters) (zip as bs)"
                                         and ys="drop (unat n_msgRegisters) (zip as bs)"
                                         for as bs, simplified] bind_assoc)
   apply (rule ccorres_rhs_assoc2, rule ccorres_split_nothrow_novcg)
       apply (rule_tac F="K $ obj_at' (\<lambda>tcb. map ((user_regs o atcbContext o tcbArch) tcb) RISCV64_H.syscallMessage = msg) sender"
                     in ccorres_mapM_x_while)
           apply (clarsimp simp: n_msgRegisters_def)
           apply (rule ccorres_guard_imp2)
            apply (rule_tac t=sender and r="RISCV64_H.syscallMessage ! n"
                            in ccorres_add_getRegister)
            apply (ctac(no_vcg))
             apply (rule_tac P="\<lambda>s. rv = msg ! n" in ccorres_cross_over_guard)
             apply (simp add: setMR_def length_msgRegisters n_msgRegisters_def
                                    liftM_def[symmetric])
             apply ctac
            apply (wp user_getreg_rv)
           apply (clarsimp simp: msgRegisters_ccorres n_msgRegisters_def
                                 syscallMessage_ccorres n_syscallMessage_def
                                 obj_at'_def projectKOs
                                 atcbContextGet_def unat_of_nat64[unfolded word_bits_def])
           apply (clarsimp simp: word_of_nat_less MessageID_Syscall_def)
          apply (simp add: n_msgRegisters_def)
         apply (rule allI, rule conseqPre, vcg exspec=setRegister_modifies exspec=getRegister_modifies)
         apply simp
        apply (simp add: setMR_def)
        apply (rule hoare_pre)
         apply (wp asUser_obj_at_elsewhere | wpc)+
        apply simp
       apply (simp add: word_bits_def)
      apply ceqv
     apply (rule ccorres_Cond_rhs)
      apply (simp del: Collect_const)
      apply (rule ccorres_rel_imp[where r = dc, simplified])
      apply (rule_tac F="\<lambda>_. obj_at' (\<lambda>tcb. map ((user_regs o atcbContext o tcbArch) tcb) RISCV64_H.syscallMessage = msg)
                                       sender and valid_pspace'
                                       and (case recvBuffer of Some x \<Rightarrow> valid_ipc_buffer_ptr' x | None \<Rightarrow> \<top>)"
                           in ccorres_mapM_x_while'[where i="unat n_msgRegisters"])
          apply (clarsimp simp: setMR_def n_msgRegisters_def length_msgRegisters
                                          option_to_0_def liftM_def[symmetric]
                                   split: option.split_asm)
          apply (rule ccorres_guard_imp2)
          apply (rule_tac t=sender and r="RISCV64_H.syscallMessage ! (n + unat n_msgRegisters)"
                                   in ccorres_add_getRegister)
          apply (ctac(no_vcg))
           apply (rule_tac P="\<lambda>s. rv = msg ! (n + unat n_msgRegisters)"
                           in ccorres_cross_over_guard)
           apply (rule ccorres_move_array_assertion_ipc_buffer
                 | (rule ccorres_flip_Guard, rule ccorres_move_array_assertion_ipc_buffer))+
           apply (simp add: storeWordUser_def)
           apply (rule ccorres_pre_stateAssert)
           apply (ctac add: storeWord_ccorres[unfolded fun_app_def])
          apply (simp add: pred_conj_def)
          apply (wp user_getreg_rv)
         apply (clarsimp simp: n_syscallMessage_def n_msgRegisters_def
                               syscallMessage_ccorres msgRegisters_ccorres
                               unat_add_lem[THEN iffD1] unat_of_nat64
                               word_bits_def word_size_def)
         apply (simp only:field_simps imp_ex imp_conjL)
         apply (clarsimp simp: pointerInUserData_c_guard obj_at'_def
                               pointerInUserData_h_t_valid
                               atcbContextGet_def
                               projectKOs objBits_simps word_less_nat_alt
                               unat_add_lem[THEN iffD1] unat_of_nat)
         apply (clarsimp simp: pointerInUserData_h_t_valid rf_sr_def
                               MessageID_Syscall_def
                               msg_align_bits valid_ipc_buffer_ptr'_def)
         apply (erule aligned_add_aligned)
          apply (rule aligned_add_aligned[where n=3])
            apply (simp add: is_aligned_def)
           apply (rule is_aligned_mult_triv2 [where n=3, simplified])
           apply (simp add: wb_gt_2)+
         apply (simp add: n_msgRegisters_def)
        apply (vcg exspec=getRegister_modifies)
        apply simp
       apply (simp add: setMR_def n_msgRegisters_def length_msgRegisters)
       apply (rule hoare_pre)
        apply (wp hoare_case_option_wp | wpc)+
       apply clarsimp
      apply (simp add: n_msgRegisters_def word_bits_def)
     apply (simp add: n_msgRegisters_def)
     apply (frule (1) option_to_0_imp)
     apply (subst drop_zip)
     apply (subst drop_n)
     apply (clarsimp simp:  n_msgRegisters_def numeral_eqs
                            mapM_cong[OF msg_aux, simplified numeral_eqs])
     apply (subst mapM_x_return_gen[where w2="()"])
     apply (rule ccorres_return_Skip)
    apply (clarsimp)
    apply (rule hoare_impI)
    apply (wp mapM_x_wp_inv setMR_atcbContext_obj_at[simplified atcbContextGet_def, simplified]
              | clarsimp
              | wpc)+
    apply (wp hoare_case_option_wp)
   apply (clarsimp simp: guard_is_UNIV_def n_msgRegisters_def msgLengthBits_def
                         mask_def)+
  done
  qed

lemma Arch_setMRs_fault_ccorres:
  "ccorres (\<lambda>r r'. r = r' && mask msgLengthBits) ret__unsigned_long_'
           (valid_pspace' and obj_at' (\<lambda>tcb. tcbFault tcb = Some ft) sender
                          and K (ft = ArchFault aft)
                          and (case buffer of Some x \<Rightarrow> valid_ipc_buffer_ptr' x | None \<Rightarrow> \<top>)
                          and K (buffer \<noteq> Some 0)
                          and K (sender \<noteq> receiver))
           (UNIV \<inter> \<lbrace>\<acute>sender = tcb_ptr_to_ctcb_ptr sender\<rbrace>
                 \<inter> \<lbrace>\<acute>receiver = tcb_ptr_to_ctcb_ptr receiver\<rbrace>
                 \<inter> \<lbrace>\<acute>faultType = fault_to_fault_tag ft \<rbrace>
                 \<inter> \<lbrace>\<acute>receiveIPCBuffer = Ptr (option_to_0 buffer)\<rbrace>) hs
    (makeArchFaultMessage aft sender >>= (\<lambda>ms. setMRs receiver buffer (snd ms)))
    (Call Arch_setMRs_fault_'proc)"
proof -
  let ?obj_at_ft = "obj_at' (\<lambda>tcb. tcbFault tcb = Some ft) sender"
  note symb_exec_r_fault = ccorres_symb_exec_r_known_rv_UNIV
          [where xf'=ret__unsigned_longlong_' and R="?obj_at_ft" and R'=UNIV]
  show ?thesis
    apply (unfold K_def)
    apply (intro ccorres_gen_asm)
    apply (cinit' lift: sender_' receiver_' faultType_' receiveIPCBuffer_')
     apply (simp only: makeArchFaultMessage_def setMRs_to_setMR
                 del:  Collect_const split del: if_split)
     apply (rule_tac P="ft = ArchFault aft" in ccorres_gen_asm)
     apply wpc
     apply (rename_tac list)
     apply (rule_tac P="zip [Suc (Suc 0) ..< msgMaxLength] list = [(2, hd list), (3, hd (tl list))]"
                     in ccorres_gen_asm)
     apply (simp add: Collect_True Collect_False ccorres_cond_iffs
                      zip_upt_Cons msgMaxLength_unfold
                      zipWithM_mapM mapM_Cons bind_assoc
                      seL4_Fault_tag_defs
                 del: Collect_const)
       apply (rule ccorres_rhs_assoc)+
       apply (ctac(no_vcg) add: getRestartPC_ccorres)
         apply (rule ccorres_stateAssert)
         apply (ctac(no_vcg) add: setMR_ccorres_dc)
       apply (rule ccorres_move_c_guard_tcb)
       apply (rule_tac val="vmFaultAddress aft" in symb_exec_r_fault)
          apply (rule conseqPre, vcg, clarsimp)
          apply (drule(1) obj_at_cslift_tcb)
          apply (clarsimp simp: ctcb_relation_def typ_heap_simps
                                   cfault_rel_def seL4_Fault_lift_def
                                   seL4_Fault_VMFault_lift_def Let_def
                            split: if_split_asm)
        apply ceqv
       apply (ctac(no_vcg) add: setMR_ccorres_dc)
        apply (rule_tac val="hd (vmFaultArchData aft)" in symb_exec_r_fault)
           apply (rule conseqPre, vcg, clarsimp)
           apply (drule(1) obj_at_cslift_tcb)
           apply (clarsimp simp: typ_heap_simps')
           apply (clarsimp simp: ctcb_relation_def
                                     cfault_rel_def seL4_Fault_lift_def
                                     seL4_Fault_VMFault_lift_def Let_def
                              split: if_split_asm)
          apply ceqv
         apply (ctac(no_vcg) add: setMR_ccorres_dc)
          apply (rule_tac val="vmFaultArchData aft ! 1" in symb_exec_r_fault)
              apply (rule conseqPre, vcg, clarsimp)
              apply (drule(1) obj_at_cslift_tcb)
              apply (clarsimp simp: typ_heap_simps')
              apply (clarsimp simp: ctcb_relation_def
                                    cfault_rel_def seL4_Fault_lift_def
                                    seL4_Fault_VMFault_lift_def Let_def
                             split: if_split_asm)
             apply ceqv
            apply (ctac(no_vcg) add: setMR_ccorres)
             apply (simp add: mapM_Nil)
             apply (rule ccorres_return_C, simp+)[1]
            apply wp
           apply (clarsimp simp: option_to_ptr_def)
           apply (subgoal_tac "case list of [a, b] \<Rightarrow> True | _ \<Rightarrow> True")
            apply (simp add: zip_upt_Cons guard_is_UNIVI seL4_VMFault_FSR_def
                             ucast_and_mask ucast_nat_def
                        split: list.split_asm)
           apply (simp split: list.split)
          apply (wp setMR_tcbFault_obj_at asUser_inv[OF getRestartPC_inv]
                       hoare_case_option_wp hoare_weak_lift_imp
                     | simp add: option_to_ptr_def guard_is_UNIVI
                                 seL4_VMFault_PrefetchFault_def
                                 seL4_VMFault_Addr_def
                                 seL4_VMFault_IP_def
                                 msgMaxLength_def
                            del: Collect_const split del: if_split
                     | wp (once) hoare_drop_imp)+

    apply (clarsimp simp: msgMaxLength_def seL4_VMFault_IP_def option_to_ptr_def
                          pageBits_def mask_def Collect_const_mem | rule conjI
         | (drule(1) obj_at_cslift_tcb,
            clarsimp simp: typ_heap_simps ctcb_relation_def,
            fastforce simp: typ_at_to_obj_at_arches elim: obj_at'_weakenE))+
     apply (subgoal_tac "[Suc (Suc 0)..<120] = 2#3#[Suc (Suc (Suc (Suc 0)))..<120]")
      apply (drule(1) obj_at_cslift_tcb)
      apply (clarsimp simp: zip_Cons ctcb_relation_def
        cfault_rel_def seL4_Fault_lift_def
        seL4_Fault_VMFault_lift_def Let_def
        split: if_split_asm)
     apply (subst upt_rec, simp)+
    done
qed

lemma setMR_mode_setTimeArg_ccorres:
  "ccorres (\<lambda>r r'. r = unat (r' && mask msgLengthBits)) ret__unsigned_long_'
     (valid_pspace' and case_option \<top> valid_ipc_buffer_ptr' buf
      and (\<lambda>_. i < msgMaxLength))
     (\<lbrace>\<acute>i = word_of_nat i\<rbrace>
      \<inter> \<lbrace>\<acute>time = v\<rbrace>
      \<inter> \<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr thread\<rbrace>
      \<inter> \<lbrace>\<acute>buffer = option_to_ptr buf\<rbrace>) []
     (setMR thread buf i v) (Call mode_setTimeArg_'proc)"
  apply (rule ccorres_gen_asm)
  apply (cinit' lift:  i_' time_'  thread_' buffer_')
   apply (rule ccorres_add_return2)
   apply (ctac add: setMR_ccorres)
     apply (fastforce intro: ccorres_return_C)
    apply fastforce
   apply (vcg exspec=setMR_modifies)
  apply (clarsimp split: if_splits)
  apply (subst ucast_of_nat_small; clarsimp simp: msgMaxLength_def)
  done

crunch setMR
  for invs'[wp]: invs'
  and valid_objs'[wp]: valid_objs'
  and no_0_obj'[wp]: no_0_obj'
  and tcb_at'[wp]: "tcb_at' tcbPtr"

lemma asUser_tcbSchedContext_inv[wp]:
  "asUser t' m \<lbrace>obj_at' (\<lambda>tcb. P (tcbSchedContext tcb)) t\<rbrace>"
  apply (simp add: asUser_def threadGet_def)
  apply (wpsimp wp: threadSet_obj_at'_strongish)
  apply (clarsimp simp: obj_at'_def split: if_splits)
  done

lemma setMR_tcbSchedContext_inv[wp]:
  "setMR thread buffer a b\<lbrace>obj_at' (\<lambda>tcb. P (tcbSchedContext tcb)) t\<rbrace>"
  unfolding setMR_def
  by wpsimp

crunch setMR, schedContextUpdateConsumed
  for valid_pspace'[wp]: valid_pspace'

crunch schedContextUpdateConsumed
  for obj_at'_tcb[wp]: "obj_at' (P :: tcb \<Rightarrow> bool) tcbPtr"

lemma setMRs_fault_ccorres [corres]:
  "ccorres (\<lambda>r r'. r = r' && mask msgLengthBits) ret__unsigned_long_'
           (valid_pspace' and obj_at' (\<lambda>tcb. tcbFault tcb = Some ft) sender
                          and tcb_at' receiver
                          and (case buffer of Some x \<Rightarrow> valid_ipc_buffer_ptr' x | None \<Rightarrow> \<top>)
                          and K (buffer \<noteq> Some 0)
                          and K (sender \<noteq> receiver))
           (UNIV \<inter> \<lbrace>\<acute>sender = tcb_ptr_to_ctcb_ptr sender\<rbrace>
                 \<inter> \<lbrace>\<acute>receiver = tcb_ptr_to_ctcb_ptr receiver\<rbrace>
                 \<inter> \<lbrace>\<acute>receiveIPCBuffer = Ptr (option_to_0 buffer)\<rbrace>) hs
    (makeFaultMessage ft sender >>= (\<lambda>ms. setMRs receiver buffer (snd ms)))
    (Call setMRs_fault_'proc)"
proof -
  let ?obj_at_ft = "obj_at' (\<lambda>tcb. tcbFault tcb = Some ft) sender"
  note symb_exec_r_fault = ccorres_symb_exec_r_known_rv_UNIV
          [where xf'=ret__unsigned_longlong_' and R="?obj_at_ft" and R'=UNIV]
  note empty_fail_cond[simp]
  show ?thesis
    supply Collect_const[simp del]
    apply (unfold K_def)
    apply (intro ccorres_gen_asm)
    apply (cinit' lift: sender_' receiver_' receiveIPCBuffer_' simp: whileAnno_def)
     apply (simp add: makeFaultMessage_def setMRs_to_setMR)
     apply (rule_tac val="fault_to_fault_tag ft" in symb_exec_r_fault)
        apply (vcg, clarsimp)
        apply (drule(1) obj_at_cslift_tcb)
        apply (clarsimp simp: ctcb_relation_def typ_heap_simps'
                              cfault_rel_def seL4_Fault_lift_def Let_def
                       split: if_split_asm)
           apply (simp add: is_cap_fault_def)
       apply ceqv
      (* UserException *)
      apply wpc
         apply (simp add: bind_assoc seL4_Fault_tag_defs ccorres_cond_iffs
                          Collect_True Collect_False
                          zipWithM_mapM zip_append2 mapM_append)
         apply (rule ccorres_symb_exec_l)
            apply (rule ccorres_stateAssert)
            apply (rule_tac P="length msg = unat n_exceptionMessage"
                       in ccorres_gen_asm)
            apply (simp add: n_exceptionMessage_def msgMaxLength_unfold
                             zip_upt_Cons mapM_Nil mapM_Cons bind_assoc
                             mapM_discarded
                        del: Collect_const upt.simps upt_rec_numeral
                        split del: if_split)
            apply (rule ccorres_rhs_assoc)+
            apply (ctac add: copyMRsFault_ccorres_exception)
              apply (rule ccorres_move_c_guard_tcb)
              apply (rule_tac val="userExceptionNumber ft" in symb_exec_r_fault)
                 apply (vcg, clarsimp)
                 apply (drule(1) obj_at_cslift_tcb)
                 apply (clarsimp simp: ctcb_relation_def typ_heap_simps
                                       cfault_rel_def seL4_Fault_lift_def
                                       seL4_Fault_UserException_lift_def Let_def
                                split: if_split_asm)
                apply ceqv
               apply (ctac add: setMR_ccorres_dc)
                 apply (rule ccorres_move_c_guard_tcb)
                 apply (rule_tac val="userExceptionErrorCode ft" in symb_exec_r_fault)
                    apply (vcg, clarsimp)
                    apply (drule(1) obj_at_cslift_tcb)
                    apply (clarsimp simp: ctcb_relation_def typ_heap_simps
                                          cfault_rel_def seL4_Fault_lift_def
                                          seL4_Fault_UserException_lift_def Let_def
                                   split: if_split_asm)
                   apply ceqv
                  apply (ctac add: setMR_ccorres)
                    apply (rule ccorres_return_C, simp+)[1]
                   apply wp
                  apply (simp del: Collect_const)
                  apply (vcg exspec=setMR_modifies)
                 apply (clarsimp simp: option_to_ptr_def guard_is_UNIVI
                                       ucast_and_mask ucast_nat_def)
                apply (wp setMR_tcbFault_obj_at
                          hoare_case_option_wp)
               apply simp
               apply (vcg exspec=setMR_modifies)
              apply (clarsimp simp: option_to_ptr_def guard_is_UNIVI)
             apply (simp add: split_def)
             apply (wp mapM_x_wp' setMR_tcbFault_obj_at
                       hoare_case_option_wp
                         | simp)+
            apply (vcg exspec=copyMRsFault_modifies exspect=setRegister_modifies)
           apply (wp asUser_inv mapM_wp' getRegister_inv)
          apply simp
          apply (wp asUser_inv mapM_wp' getRegister_inv hoare_drop_imps asUser_const_rv
                    asUser_get_registers[simplified atcbContextGet_def comp_def])
         apply simp
         (* CapFault *)
        apply (simp add: Collect_True Collect_False ccorres_cond_iffs
                         zip_upt_Cons msgMaxLength_unfold
                         zipWithM_mapM mapM_Cons bind_assoc
                    del: Collect_const)
        apply (rule ccorres_rhs_assoc)+
        apply (ctac(no_vcg))
         apply (rule ccorres_stateAssert)
         apply (ctac(no_vcg) add: setMR_ccorres_dc)
          apply (rule_tac val="capFaultAddress ft" in symb_exec_r_fault)
             apply (rule conseqPre, vcg, clarsimp)
             apply (drule(1) obj_at_cslift_tcb)
             apply (clarsimp simp: typ_heap_simps' ctcb_relation_def
                                   cfault_rel_def seL4_Fault_lift_def Let_def
                                   seL4_Fault_CapFault_lift_def
                            split: if_split_asm)
            apply ceqv
           apply (ctac(no_vcg) add: setMR_ccorres_dc)
            apply (rule_tac val="from_bool (capFaultInReceivePhase ft)" in symb_exec_r_fault)
               apply (rule conseqPre, vcg, clarsimp)
               apply (drule(1) obj_at_cslift_tcb)
               apply (clarsimp simp: typ_heap_simps' ctcb_relation_def
                                     cfault_rel_def seL4_Fault_lift_def Let_def
                                     seL4_Fault_CapFault_lift_def
                                     from_bool_to_bool_and_1 word_size
                              split: if_split_asm)
              apply ceqv
             apply (ctac(no_vcg) add: setMR_ccorres_dc)
              apply (rule ccorres_move_c_guard_tcb)
              apply (rule_tac P="obj_at' (\<lambda>tcb. tcbFault tcb = Some ft) sender"
                           in ccorres_cross_over_guard)
              apply (ctac(no_vcg) add: setMRs_lookup_failure_ccorres[unfolded msgMaxLength_unfold])
               apply simp
               apply (rule ccorres_return_C, simp+)[1]
              apply (wp setMR_tcbFault_obj_at hoare_case_option_wp)+
            apply (clarsimp simp: option_to_ptr_def Collect_const_mem guard_is_UNIV_def)
            apply (rule conjI)
             apply (simp add: seL4_CapFault_InRecvPhase_def)
            apply (rule conjI)
             apply (simp add: from_bool_def split: bool.split)
            apply clarsimp
            apply (drule(1) obj_at_cslift_tcb)
            apply (clarsimp simp: typ_heap_simps' ctcb_relation_def
                                  cfault_rel_def seL4_Fault_lift_def Let_def
                                  seL4_Fault_CapFault_lift_def is_cap_fault_def
                                  seL4_CapFault_LookupFailureType_def
                                  ucast_and_mask ucast_nat_def
                           split: if_split_asm)
           apply (wp setMR_tcbFault_obj_at hoare_case_option_wp
                     asUser_inv[OF getRestartPC_inv]
                     | (rule guard_is_UNIVI, clarsimp simp: option_to_ptr_def
                                                            seL4_CapFault_Addr_def))+
      (* UnknownSyscall *)
      apply (rename_tac syscall_number)
      apply (simp add: seL4_Fault_tag_defs Collect_True Collect_False
                       ccorres_cond_iffs zipWithM_mapM mapM_append
                       zip_append2 bind_assoc
                  del: Collect_const)
      apply (rule ccorres_symb_exec_l)
         apply (rule ccorres_stateAssert)
         apply (rule_tac P="length msg = unat n_syscallMessage" in ccorres_gen_asm)
         apply (simp add: msgMaxLength_unfold n_syscallMessage_def zip_upt_Cons
                          mapM_Cons mapM_Nil mapM_discarded
                     del: Collect_const upt_rec_numeral)
         apply (rule ccorres_rhs_assoc)+
         apply (ctac add: copyMRsFault_ccorres_syscall)
           apply (rule ccorres_move_c_guard_tcb)
           apply (rule_tac val="syscall_number" in symb_exec_r_fault)
              apply (vcg, clarsimp)
              apply (drule(1) obj_at_cslift_tcb)
              apply (clarsimp simp: ctcb_relation_def typ_heap_simps'
                                    cfault_rel_def seL4_Fault_lift_def Let_def
                                    seL4_Fault_UnknownSyscall_def
                                    seL4_Fault_UnknownSyscall_lift_def
                              split: if_split_asm)
             apply ceqv
            apply (ctac add: setMR_ccorres)
              apply (rule ccorres_return_C, simp+)[1]
             apply wp
            apply (simp del: Collect_const)
            apply (vcg exspec=setMR_modifies)
           apply (clarsimp simp: option_to_ptr_def guard_is_UNIVI ucast_and_mask ucast_nat_def)
          apply (wp setMR_tcbFault_obj_at mapM_x_wp_inv hoare_case_option_wp
                | clarsimp
                | wpc)+
         apply (vcg exspec=copyMRsFault_modifies)
        apply (wp asUser_inv mapM_wp' getRegister_inv)
       apply simp
       apply (wp asUser_inv mapM_wp' getRegister_inv hoare_drop_imps asUser_const_rv
                 asUser_get_registers[simplified atcbContextGet_def comp_def])
       apply simp
       (* Timeout *)
       apply (rename_tac badge)
       apply (simp add: seL4_Fault_tag_defs Collect_True Collect_False
                        ccorres_cond_iffs zipWithM_mapM bind_assoc)
       apply (rule ccorres_pre_threadGet, rename_tac tcbSc)
       apply (simp add: case_option_If2 if_to_top_of_bind)
       apply (rule ccorres_move_c_guard_tcb)
       apply (rule_tac Q="obj_at' (\<lambda>tcb. tcbSchedContext tcb = tcbSc) sender
                          and valid_objs' and no_0_obj'"
                    in ccorres_cond_both'[where Q'=\<top>])
         apply normalise_obj_at'
         apply (frule (1) obj_at_cslift_tcb)
         apply (frule (1) tcb_ko_at_valid_objs_valid_tcb')
         apply (clarsimp simp: ctcb_relation_def typ_heap_simps valid_tcb'_def)
         apply (case_tac "tcbSchedContext ko"; clarsimp)
        apply (simp add: bind_assoc)
        apply (rule ccorres_rhs_assoc)+
        apply csymbr
        apply (rule ccorres_move_c_guard_tcb)
        apply (ctac (no_vcg) add: schedContext_updateConsumed_ccorres)
         apply (rule ccorres_stateAssert)
         apply (rule ccorres_move_c_guard_tcb)
         apply (rule_tac val=badge in symb_exec_r_fault)
            apply (vcg, clarsimp)
            apply (drule(1) obj_at_cslift_tcb)
            subgoal
              by (clarsimp simp: ctcb_relation_def typ_heap_simps'
                                 cfault_rel_def seL4_Fault_lift_def Let_def
                                 seL4_Fault_Timeout_def seL4_Fault_Timeout_lift_def
                          split: if_split_asm)
           apply ceqv
          apply (simp add: zip_upt_Cons msgMaxLength_unfold mapM_Cons bind_assoc)
          apply (ctac add: setMR_ccorres)
            apply csymbr
            apply (simp add: words_from_time_def zip_upt_Cons mapM_Cons mapM_empty)
            apply (ctac add: setMR_mode_setTimeArg_ccorres[where i="Suc 0"])
              apply (fastforce intro: ccorres_return_C)
             apply wpsimp
            apply (vcg exspec=mode_setTimeArg_modifies)
           apply (wpsimp wp: hoare_case_option_wp)
          apply simp
          apply vcg
         apply (fastforce simp: guard_is_UNIV_def n_msgRegisters_def msgRegisters_def
                                seL4_Timeout_Data_def option_to_ptr_def)
        apply (wpsimp wp: hoare_drop_imp hoare_case_option_wp)
       apply simp
       apply (rule ccorres_stateAssert)
       apply (simp add: zip_upt_Cons msgMaxLength_unfold mapM_Cons mapM_empty)
       apply (rule ccorres_rhs_assoc)+
       apply (rule ccorres_move_c_guard_tcb)
       apply (rule_tac val=badge in symb_exec_r_fault)
          apply (vcg, clarsimp)
          apply (drule(1) obj_at_cslift_tcb)
          subgoal
            by (clarsimp simp: ctcb_relation_def typ_heap_simps'
                               cfault_rel_def seL4_Fault_lift_def Let_def
                               seL4_Fault_Timeout_def seL4_Fault_Timeout_lift_def
                        split: if_split_asm)
         apply ceqv
        apply (ctac add: setMR_ccorres)
          apply (fastforce intro: ccorres_return_C)
         apply wpsimp
        apply (vcg exspec=setMR_modifies)
       apply (clarsimp simp: guard_is_UNIV_def seL4_Timeout_Data_def option_to_ptr_def
                             ucast_and_mask)
      (* ArchFault *)
      apply clarsimp
      apply ccorres_rewrite
      apply (rule ccorres_rhs_assoc)+
      apply (rule ccorres_move_c_guard_tcb)
      apply (rule_tac val="fault_to_fault_tag ft" in symb_exec_r_fault)
        apply (vcg, clarsimp)
        apply (drule(1) obj_at_cslift_tcb)
        apply (clarsimp simp: ctcb_relation_def typ_heap_simps'
                              cfault_rel_def seL4_Fault_lift_def Let_def
                              seL4_Fault_UnknownSyscall_def
                              seL4_Fault_UnknownSyscall_lift_def
                       split: if_split_asm)
       apply ceqv
      apply (rule ccorres_add_return2)
      apply (ctac add: Arch_setMRs_fault_ccorres[simplified setMRs_to_setMR last.simps K_bind_def])
        apply (ctac add: ccorres_return_C)
       apply wpsimp
      apply (vcg exspec=Arch_setMRs_fault_modifies)
      apply (clarsimp simp: guard_is_UNIV_def Collect_const_mem)
      apply (rule fault_to_fault_tag.simps(2)[symmetric])
     (* done *)
     apply clarsimp
     apply (rule guard_is_UNIVI, clarsimp simp: option_to_ptr_def)
     apply (intro conjI impI allI)
      apply (clarsimp simp: seL4_CapFault_IP_def)
     apply (clarsimp simp: ctcb_relation_def typ_heap_simps)
     apply (rename_tac tcb badge ctcb)
     apply (case_tac "tcbSchedContext tcb"; clarsimp)
    apply (fastforce simp: msgMaxLength_unfold length_syscallMessage msgFromLookupFailure_def
                           RISCV64_H.exceptionMessage_def RISCV64.exceptionMessage_def
                           n_exceptionMessage_def n_syscallMessage_def
                           RISCV64.length_msgRegisters seL4_CapFault_IP_def obj_at'_def
                    split: lookup_failure.splits)
    done
qed

definition
  makeArchFaultMessage2 :: "arch_fault \<Rightarrow> machine_word"
where
  "makeArchFaultMessage2 \<equiv>
     \<lambda>aft. case aft of VMFault _ _ \<Rightarrow> 6"

lemma makeFaultMessage2:
  "makeFaultMessage ft thread
    = (do x \<leftarrow> makeFaultMessage ft thread;
       return (case ft of CapFault _ _ _ \<Rightarrow> 1
                   | UnknownSyscallException _ \<Rightarrow> 2
                   | UserException _ _ \<Rightarrow> 3
                   | Timeout _ \<Rightarrow> 5
                   | ArchFault aft \<Rightarrow> makeArchFaultMessage2 aft, snd x) od)"
  apply (cases ft;
         (solves \<open>auto simp: makeFaultMessage_def makeArchFaultMessage2_def makeArchFaultMessage_def
                             bind_assoc
                      split: fault.split arch_fault.split\<close>)?)
  apply (clarsimp simp: makeFaultMessage_def  bind_assoc)
  apply (rule monadic_rewrite_to_eq)
  apply (rule monadic_rewrite_guard_imp)
   apply (rule monadic_rewrite_bind)
     apply (rule monadic_rewrite_refl)
    apply (rule monadic_rewrite_sym)
    apply (rule monadic_rewrite_case_option)
     apply clarsimp
     apply (rule monadic_rewrite_refl)
    apply clarsimp
    apply (rule monadic_rewrite_refl)
   apply wpsimp
  by fastforce

lemma makeFaultMessage_tcb_at'_fault[wp]:
  "makeFaultMessage ft t \<lbrace> obj_at' (\<lambda>a. tcbFault a = Some ft) p\<rbrace>"
  apply (cases ft, simp_all add: makeFaultMessage_def)
      by (wpsimp wp: asUser_inv mapM_wp' det_mapM[where S=UNIV]
                     det_getRestartPC getRestartPC_inv threadGet_wp
               simp: getRegister_def makeArchFaultMessage_def schedContextUpdateConsumed_def
              split: arch_fault.split
          | fastforce simp: obj_at_simps)+

lemma doFaultTransfer_ccorres [corres]:
  "ccorres dc xfdc (valid_pspace' and tcb_at' sender and tcb_at' receiver
                    and (case buffer of Some x \<Rightarrow> valid_ipc_buffer_ptr' x | None \<Rightarrow> \<top>)
                    and K (buffer \<noteq> Some 0) and K (receiver \<noteq> sender))
    (UNIV \<inter> \<lbrace>\<acute>sender = tcb_ptr_to_ctcb_ptr sender\<rbrace>
          \<inter> \<lbrace>\<acute>receiver = tcb_ptr_to_ctcb_ptr receiver\<rbrace>
          \<inter> \<lbrace>\<acute>receiverIPCBuffer = Ptr (option_to_0 buffer)\<rbrace>
          \<inter> \<lbrace>\<acute>badge___unsigned_long = badge\<rbrace>) []
    (doFaultTransfer badge sender receiver buffer)
    (Call doFaultTransfer_'proc)"
  apply (unfold K_def)
  apply (intro ccorres_gen_asm)
  apply (simp add: doFaultTransfer_def)
  apply (subst makeFaultMessage2)
  apply (simp only: makeArchFaultMessage2_def)
  apply (cinit' lift: sender_' receiver_' receiverIPCBuffer_' badge___unsigned_long_')
   apply (rule ccorres_pre_threadGet)
   apply (rename_tac ft)
   apply wpc
    apply (simp del: Collect_const, rule ccorres_fail)
   apply (simp add: split_def bind_assoc del: Collect_const)
   apply (simp only: bind_assoc[symmetric, where m="makeFaultMessage ft t" for ft t])
   apply (ctac(no_vcg) add: setMRs_fault_ccorres)
    apply (rule_tac R="obj_at' (\<lambda>tcb. tcbFault tcb = ft) sender"
              and val="case (the ft) of CapFault _ _ _ \<Rightarrow> 1
                  | ArchFault (VMFault _ _) \<Rightarrow> 6
                  | Timeout _ \<Rightarrow> 5
                  | UnknownSyscallException _ \<Rightarrow> 2
                  | UserException _ _ \<Rightarrow> 3"
              in ccorres_symb_exec_r_known_rv_UNIV
                   [where xf'=ret__unsigned_longlong_' and R'=UNIV])
       apply (rule conseqPre, vcg, clarsimp)
       apply (drule(1) obj_at_cslift_tcb)
       apply (clarsimp simp: typ_heap_simps' ctcb_relation_def
                             cfault_rel_def seL4_Fault_lift_def Let_def
                             seL4_Fault_tag_defs
                      split: if_split_asm)
      apply ceqv
     apply csymbr
     apply (ctac (no_vcg, c_lines 2) add: setMessageInfo_ccorres)
       apply (ctac add: setRegister_ccorres)
      apply wp
     apply (simp add: badgeRegister_def RISCV64.badgeRegister_def RISCV64.capRegister_def
                      Kernel_C.badgeRegister_def "StrictC'_register_defs")
    apply (clarsimp simp: message_info_to_H_def guard_is_UNIVI
                          mask_def msgLengthBits_def
                   split: fault.split arch_fault.split)
   apply (wpsimp simp: setMRs_to_setMR zipWithM_mapM split_def
                   wp: mapM_wp' setMR_tcbFault_obj_at hoare_drop_imps)
  apply (clarsimp simp: obj_at'_def)
  done

lemma ccorres_emptyOnFailure:
  assumes corr_ac: "ccorres (\<lambda>f c. case f of Inl _ \<Rightarrow> r [] c | Inr xs \<Rightarrow> r xs c)
                            xf
                            P P' hs a c"
  shows "ccorres r xf P P' hs (emptyOnFailure a) c" using corr_ac
  apply (simp add: emptyOnFailure_def catch_def const_def bind_def split_def)
  apply (clarsimp simp: ccorres_underlying_def return_def split: xstate.splits sum.splits)
  apply (drule (1) bspec)
  apply (rule conjI, clarsimp)
   apply (erule_tac x=n in allE)
   apply (rename_tac s)
   apply (erule_tac x="Normal s" in allE)
   apply clarsimp
   apply (rule bexI)
    prefer 2
    apply assumption
   apply clarsimp
   apply (rule conjI, clarsimp simp: unif_rrel_def)
   apply (clarsimp simp: unif_rrel_def)
  apply fastforce
  done

lemma unifyFailure_ccorres:
  assumes corr_ac: "ccorres (f \<currency> r) xf P P' hs a c"
  shows "ccorres ((\<lambda>_. dc) \<currency> r) xf P P' hs (unifyFailure a) c"
  using corr_ac
  apply (simp add: unifyFailure_def rethrowFailure_def const_def
                   handleE'_def throwError_def)
  apply (clarsimp simp: ccorres_underlying_def bind_def split_def return_def
                  split: xstate.splits sum.splits)
  apply (drule (1) bspec)
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (erule_tac x=n in allE)
   apply (rename_tac s)
   apply (erule_tac x="Normal s" in allE)
   apply clarsimp
   apply (rule bexI)
    prefer 2
    apply assumption
   apply (clarsimp simp: unif_rrel_def)
   apply fastforce
  apply fastforce
  done

definition
cct_relation:: "cap_transfer \<Rightarrow> cap_transfer_C \<Rightarrow> bool"
where
"cct_relation atc ctc \<equiv>
  case atc of
    (CT croot idx dpt) \<Rightarrow>  ctReceiveRoot_C ctc = croot \<and>
                           ctReceiveIndex_C  ctc= idx \<and>
                           unat (ctReceiveDepth_C ctc) = dpt"

lemma capTransferFromWords_ccorres [corres]:
  "ccorres cct_relation ret__struct_cap_transfer_C_'
           (valid_pspace' and K (is_aligned ptr 3))
           (UNIV \<inter> \<lbrace>array_assertion (Ptr ptr :: machine_word ptr) 3 (hrs_htd \<acute>t_hrs)\<rbrace>
              \<inter> \<lbrace>\<acute>wptr = Ptr ptr\<rbrace>) hs
           (capTransferFromWords ptr)
           (Call capTransferFromWords_'proc)"
  apply (cinit lift: wptr_')
   apply (rule ccorres_pre_loadWordUser)+
   apply (rule_tac P=\<top>
               and P'="{s. array_assertion (Ptr ptr :: machine_word ptr)
                              3 (hrs_htd (t_hrs_' (globals s))) \<and>
                           cslift s (Ptr ptr) = Some rv \<and>
                           cslift s (Ptr (ptr + 8)) = Some rva \<and>
                           cslift s (Ptr (ptr + 16)) = Some rvb}"
                in ccorres_from_vcg_throws)
   apply (rule allI, rule conseqPre, vcg)
   apply (clarsimp simp: typ_heap_simps' ptr_add_assertion_positive
                         array_assertion_shrink_right)
   apply (simp add: return_def)
   apply (simp add: cct_relation_def)
  apply (clarsimp simp: word_size valid_ipc_buffer_ptr'_def wordSize_def')
  apply safe
   apply (erule aligned_add_aligned | simp add: is_aligned_def word_bits_conv)+
  done

lemma array_assertion_shrink_left_add:
  "array_assertion (Ptr ptr :: ('a :: wf_type) ptr) j htd
    \<Longrightarrow> n = of_nat (k * size_of TYPE('a)) \<and> k + i \<le> j \<and> 0 < i
    \<Longrightarrow> array_assertion (Ptr (ptr + n) :: 'a ptr) i htd"
  apply (cases "k = 0")
   apply (simp add: unat_eq_0)
   apply (erule array_assertion_shrink_right, simp)
  apply (drule_tac j=k in array_assertion_shrink_leftD)
   apply simp
  apply simp
  apply (erule array_assertion_shrink_right)
  apply arith
  done

lemma array_assertion_shrink_left_add_div:
  "array_assertion (Ptr ptr :: ('a :: wf_type) ptr) j htd
    \<Longrightarrow> n = of_nat (unat n div size_of TYPE('a)) * of_nat (size_of TYPE('a))
        \<and> i + (unat n div size_of TYPE('a)) \<le> j \<and> 0 < i
    \<Longrightarrow> array_assertion (Ptr (ptr + n) :: 'a ptr) i htd"
  apply (erule_tac k="unat n div size_of TYPE('a)"
    in array_assertion_shrink_left_add)
  apply simp
  done

lemma loadCapTransfer_ccorres [corres]:
  "ccorres  cct_relation ret__struct_cap_transfer_C_'
           (valid_pspace' and valid_ipc_buffer_ptr' buffer)
           (UNIV \<inter> \<lbrace>\<acute>buffer = Ptr buffer\<rbrace>) hs
           (loadCapTransfer buffer)
           (Call loadCapTransfer_'proc)"
  apply (cinit lift: buffer_')
   apply (rule ccorres_Guard_Seq)+
   apply csymbr
   apply (simp add: seL4_MsgLengthBits_def
                    seL4_MsgExtraCapBits_def
                    seL4_MsgMaxLength_def
                    ptr_add_assertion_positive)
   apply (rule ccorres_move_array_assertion_ipc_buffer
               ccorres_rhs_assoc)+
   apply (rule ccorres_add_return2)
   apply (ctac(no_vcg))
    apply (rule ccorres_move_array_assertion_ipc_buffer)
    apply simp
    apply (ctac (no_vcg) add: ccorres_return_C)
   apply (wp capTransferFromWords_inv | simp)+
  apply (clarsimp simp: word_size)
  apply (simp add: seL4_MsgLengthBits_def
                   seL4_MsgExtraCapBits_def
                   seL4_MsgMaxLength_def
                   word_size word_sle_def
                   msgMaxLength_def msgMaxExtraCaps_def
                   msgLengthBits_def msgExtraCapBits_def
                   Collect_const_mem msg_align_bits)
  apply (frule(1) valid_ipc_buffer_ptr_array[where p="Ptr p'" for p', simplified],
    rule order_refl, simp_all add: msg_align_bits)
  apply (clarsimp simp: valid_ipc_buffer_ptr'_def wordSize_def')
  apply (subst array_assertion_shrink_left_add_div, assumption)
   apply (simp add: msgMaxLength_def msgExtraCaps_def msgMaxExtraCaps_def msgExtraCapBits_def
                    shiftL_nat)
  apply simp
  apply (erule aligned_add_aligned, simp_all add: is_aligned_def msg_align_bits_def bit_simps)
  done

lemma loadCapTransfer_ctReceiveDepth:
  "\<lbrace>\<top>\<rbrace> loadCapTransfer buffer \<lbrace>\<lambda>rv s. ctReceiveDepth rv < 2 ^ word_bits\<rbrace>"
  apply (simp add: loadCapTransfer_def capTransferFromWords_def)
  apply wp
    apply (rule_tac Q'="\<lambda>_ _. True" in hoare_post_eq)
     apply simp
     apply (simp only: word_bits_len_of[symmetric])
     apply (subst unat_lt2p, simp)
    apply wpsimp+
  done

lemma getReceiveSlots_ccorres:
  "ccorres (\<lambda>a c. (a = [] \<or> (\<exists>slot. a = [slot])) \<and>
           ((a \<noteq> []) = (c \<noteq> NULL)) \<and> (a\<noteq>[] \<longrightarrow> c = cte_Ptr (hd a) \<and> c \<noteq> NULL))
           ret__ptr_to_struct_cte_C_'
           (valid_ipc_buffer_ptr' buffer and
              valid_pspace'  and
              tcb_at' thread
             and (\<lambda>s. buffer \<noteq> 0))
           (UNIV \<inter> \<lbrace>\<acute>buffer = Ptr buffer\<rbrace> \<inter> \<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr thread\<rbrace>) hs
           (getReceiveSlots thread (Some buffer))
           (Call getReceiveSlots_'proc)"
  apply (rule ccorres_gen_asm)
  apply (cinit lift: buffer_' thread_')
   apply (simp add: split_def)
   apply (ctac (no_vcg))
    apply (rule ccorres_emptyOnFailure)
    apply csymbr
    apply (rule ccorres_split_nothrowE)
         apply (rule unifyFailure_ccorres)
         apply (ctac (no_vcg) add: lookupCap_ccorres')
        apply ceqv
       apply simp
       apply csymbr
       apply (fold lookupTargetSlot_def)
       apply (rule ccorres_split_nothrow_novcgE)
             apply (rule unifyFailure_ccorres)
             apply (ctac (no_vcg) add: lookupTargetSlot_ccorres')
            apply ceqv
           apply (rename_tac slot slot_c)
           apply (simp add: liftE_bindE)
           apply csymbr
           apply (rule_tac P="cte_at' slot and no_0_obj'"
                      in ccorres_from_vcg_throws[where P'=UNIV])
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp: in_monad cte_wp_at_ctes_of Bex_def in_getCTE2)
           apply (rule cmap_relationE1[OF cmap_relation_cte], assumption+)
           apply (clarsimp simp: typ_heap_simps' cap_get_tag_isCap in_monad
                          dest!: ccte_relation_ccap_relation)
           apply (erule cte_at_0'[rotated], simp add: cte_wp_at_ctes_of)
          apply clarsimp
          apply (rule ccorres_split_throws)
           apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp: throwError_def return_def)
          apply (rule conseqPre, vcg, clarsimp)
         apply clarsimp
         apply (wp lsfco_cte_at')
        apply (clarsimp simp: guard_is_UNIV_def)
       apply (clarsimp simp: guard_is_UNIV_def)
       apply (rule UNIV_I)
      apply simp
      apply clarsimp
      apply (rule ccorres_split_throws)
       apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg_throws)
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp: throwError_def return_def)
      apply (rule conseqPre, vcg, clarsimp)
     apply clarsimp
     apply wp
    apply (vcg exspec=lookupCap_modifies)
   apply clarsimp
   apply (wp loadCapTransfer_ctReceiveDepth)
  apply clarsimp
  apply (intro conjI)
    apply fastforce
   apply fastforce
  apply clarsimp
  apply (simp add: cct_relation_def)
  apply (case_tac rv, clarsimp)
  apply (rule UNIV_I)  \<comment> \<open>still a schematic here ...\<close>
  done


lemma setExtraBadge_ccorres:
  "ccorres dc xfdc
           (valid_pspace' and valid_ipc_buffer_ptr' buffer and (\<lambda>_. msg_max_length + 2 + n < unat max_ipc_words))
           (UNIV \<inter> \<lbrace>\<acute>bufferPtr = Ptr buffer\<rbrace> \<inter> \<lbrace>\<acute>badge___unsigned_long = badge\<rbrace> \<inter> \<lbrace>\<acute>i = of_nat n\<rbrace>)
           hs
           (setExtraBadge buffer badge n)
           (Call setExtraBadge_'proc)"
  apply (rule ccorres_gen_asm)
  apply (cinit lift: bufferPtr_' badge___unsigned_long_' i_')
   apply (unfold storeWordUser_def)
   apply (rule ccorres_pre_stateAssert)
   apply (simp only: K_bind_def)
   apply (rule ccorres_move_array_assertion_ipc_buffer
               ccorres_Guard[where F=C_Guard]
               ccorres_Guard[where F=SignedArithmetic]
               )+
   apply (ctac add: storeWord_ccorres)
  apply (clarsimp simp: bufferCPtrOffset_def word_size msgMaxLength_def wordSize_def'
                        seL4_MsgLengthBits_def seL4_MsgMaxLength_def Types_H.msgLengthBits_def
                        field_simps Collect_const_mem)
  apply (subgoal_tac " is_aligned (buffer + (of_nat n * 8 + 0x3D0)) 3")
   apply clarsimp
   prefer 2
   apply (clarsimp simp: valid_ipc_buffer_ptr'_def)
   apply (erule aligned_add_aligned, simp_all add: msg_align_bits)
    apply (rule_tac n=3 in aligned_add_aligned, simp_all add: word_bits_def)
     apply (rule is_aligned_mult_triv2 [where n = 3, simplified])
    apply (simp add: is_aligned_def)
  apply (auto simp: pointerInUserData_c_guard pointerInUserData_h_t_valid
                    msg_align_bits max_ipc_words_def msg_max_length_def
                    capTransferDataSize_def msgMaxLength_def msgMaxExtraCaps_def
                    msgExtraCapBits_def unat_word_ariths unat_of_nat)
  done

(* FIXME: move *)
lemma ccorres_constOnFailure:
  assumes corr_ac: "ccorres (\<lambda>f c. case f of Inl x \<Rightarrow> r n c | Inr n \<Rightarrow> r n c)
                            xf
                            P P' hs a c"
  shows "ccorres r xf P P' hs (constOnFailure n a) c" using corr_ac
  apply (simp add: constOnFailure_def catch_def const_def bind_def split_def)
  apply (clarsimp simp: ccorres_underlying_def return_def split: xstate.splits sum.splits)
  apply (drule (1) bspec)
  apply (rule conjI, clarsimp)
   apply (erule_tac x=na in allE)
   apply (rename_tac s)
   apply (erule_tac x="Normal s" in allE)
   apply clarsimp
   apply (rule bexI)
    prefer 2
    apply assumption
   apply clarsimp
   apply (rule conjI, clarsimp simp: unif_rrel_def)
   apply (clarsimp simp: unif_rrel_def)
  apply fastforce
  done

(* FIXME: move *)
lemma ccorres_case_sum_liftE:
  "ccorres r xf P P' hs H C \<Longrightarrow> ccorres (\<lambda>a c. case_sum (\<lambda>x. r' x c) (\<lambda>y. r y c) a) xf P P' hs (liftE H) C"
  apply (clarsimp simp: ccorres_underlying_def split: xstate.splits)
  apply (drule (1) bspec)
  apply (clarsimp simp: split_def liftE_def bind_def return_def)
  apply (fastforce simp: unif_rrel_def)
  done

(* FIXME: move *)
lemma ccorres_case_bools_rhs:
  assumes P: "ccorres r xf P P' hs a c"
  assumes Q: "ccorres r xf Q Q' hs a c"
  shows "ccorres r xf (P and Q)
                      ({s. s \<in> B \<longrightarrow> s \<in> P'} \<inter> {s. s \<notin> B \<longrightarrow> s \<in> Q'})
                      hs a c" using P Q
  apply (clarsimp simp: ccorres_underlying_def)
  apply (drule (1) bspec)+
  apply clarsimp
  apply (case_tac "b \<in> B", auto)
  done

(* FIXME: move *)
lemma ccorres_return_bind_add:
  "ccorres r xf P P' hs (do z \<leftarrow> return (f x); H z od) C \<Longrightarrow> ccorres r xf P P' hs (H (f x)) C"
  by simp


(* FIXME: move *)
lemma ccorres_if_cond_throws_break:
  fixes e :: 'e
  assumes abs: "\<forall>s s'. (s, s') \<in> sr \<and> Q s \<and> Q' s' \<longrightarrow> P = (s' \<in> P')"
  and     ac: "P \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf R R' (catchbrk_C # hs) a c"
  and     bd: "\<not> P \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf U U' (catchbrk_C # hs) b d"
  and cthrows: "\<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> PT' c {}, UNIV" \<comment> \<open>c always throws\<close>
  shows  "ccorres_underlying sr \<Gamma> r xf arrel axf
          (Q and (\<lambda>s. P \<longrightarrow> R s) and (\<lambda>s. \<not> P \<longrightarrow> U s))
          (Collect Q' \<inter> {s. (s \<in> P' \<longrightarrow> s \<in> R' \<inter> PT') \<and> (s \<notin> P' \<longrightarrow> s \<in> U')})
          (catchbrk_C # hs)
          (if P then a else b) (Cond P' c SKIP ;; d)"
  (is "ccorres_underlying sr \<Gamma> r xf arrel axf ?G ?G' ?hs ?a ?c")
proof (cases P)
  case True

  thus ?thesis
    apply simp
    apply (rule ccorres_guard_imp2)
    apply (rule ccorres_split_throws)
    apply (rule ccorres_cond_true [OF ac [OF True]])
    apply (rule HoarePartial.Cond [where P = "P' \<inter> PT'", OF _ cthrows])
    apply clarsimp
    apply (rule HoarePartial.Skip)
    apply (rule subset_refl)
    apply (clarsimp simp: abs [rule_format, OF conjI])
    done
next
  case False

  thus ?thesis
    apply simp
    apply (rule ccorres_guard_imp2)
    apply (rule ccorres_add_return)
    apply (rule ccorres_split_nothrow)
    apply (rule ccorres_cond_false)
       apply (rule ccorres_return_Skip)
      apply (rule ceqv_refl)
     apply (rule bd [OF False])
    apply wp
   apply simp
   apply (rule Cond_false)
   apply (rule HoarePartial.Skip [OF subset_refl])
   apply (clarsimp simp: abs [rule_format, OF conjI])
   done
qed


(* FIXME: move *)
lemma ccorres_if_cond_throws_break2:
  fixes e :: 'e
  assumes abs: "\<forall>s s'. (s, s') \<in> sr \<and> Q s \<and> Q' s' \<longrightarrow> (\<not> P) = (s' \<in> P')"
  and     ac: "\<not> P \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf R R' (catchbrk_C # hs) a c"
  and     bd: "P \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf U U' (catchbrk_C # hs) b d"
  and cthrows: "\<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> PT' c {}, UNIV" \<comment> \<open>c always throws\<close>
  shows  "ccorres_underlying sr \<Gamma> r xf arrel axf
          (Q and (\<lambda>s. \<not> P \<longrightarrow> R s) and (\<lambda>s. P \<longrightarrow> U s))
          (Collect Q' \<inter> {s. (s \<in> P' \<longrightarrow> s \<in> R' \<inter> PT') \<and> (s \<notin> P' \<longrightarrow> s \<in> U')})
          (catchbrk_C # hs)
          (if P then b else a) (Cond P' c SKIP ;; d)"
  apply (subst if_swap)
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_if_cond_throws_break [OF abs ac bd cthrows])
    apply assumption
   apply simp
  apply clarsimp
  done

declare scast_bit_test[simp]

(* FIXME: move *)
lemma ccorres_split_when_throwError_cond_break:
  fixes e :: 'e
  assumes abs: "\<forall>s s'. (s, s') \<in> sr \<and> Q s \<and> Q' s' \<longrightarrow> P = (s' \<in> P')"
  and     cc: "P \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf ar axf
                        R R' (catchbrk_C # hs) (throwError e) c"
  and     bd: "\<not> P \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf ar axf
                        U U' (catchbrk_C # hs) b d"
  and cthrows: "\<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> PT' c {}, UNIV" \<comment> \<open>c always throws\<close>
  shows  "ccorres_underlying sr \<Gamma> r xf ar axf
          (Q and (\<lambda>s. P \<longrightarrow> R s) and (\<lambda>s. \<not> P \<longrightarrow> U s))
          (Collect Q' \<inter> {s. (s \<in> P' \<longrightarrow> s \<in> R' \<inter> PT') \<and> (s \<notin> P' \<longrightarrow> s \<in> U')})
          (catchbrk_C # hs)
          (whenE P (throwError e) >>=E (\<lambda>_. b)) (Cond P' c SKIP ;; d)"
  apply (subst whenE_bindE_throwError_to_if)
  apply (rule ccorres_if_cond_throws_break [OF abs cc bd cthrows])
   apply assumption
  apply assumption
  done

lemma maskAsFull_isEndpoint[simp]:
  "isEndpointCap a \<Longrightarrow> maskedAsFull a b = a"
   by (clarsimp simp:isCap_simps maskedAsFull_def)

lemma is_derived_capMasterCap:
  "is_derived' m slot cap cap'
         \<Longrightarrow> capMasterCap cap = capMasterCap cap'"
 by (clarsimp simp:is_derived'_def badge_derived'_def)

lemma maskedAsFull_misc:
  "badge_derived' a (maskedAsFull a b)"
  "capASID (maskedAsFull a b) = capASID a"
  "cap_asid_base' (maskedAsFull a b) = cap_asid_base' a"
  "cap_vptr' (maskedAsFull a b) = cap_vptr' a"
  "capMasterCap (maskedAsFull a b) = capMasterCap a"
  by (auto simp:maskedAsFull_def isCap_simps badge_derived'_def
          split:if_split)

lemma maskedAsFull_again:
  "maskedAsFull (maskedAsFull aa aa) r = maskedAsFull aa aa"
  apply (case_tac aa)
  apply (simp_all add:maskedAsFull_def isCap_simps split: if_split)+
  done

lemma ccap_relation_lift:
  "ccap_relation cap cap'
   \<Longrightarrow> (cap_to_H (the (cap_lift cap'))) = cap"
  apply (case_tac "cap_lift cap'")
   apply (auto simp:ccap_relation_def split:option.splits)
  done

lemma ccap_relation_inject:
  "\<lbrakk>ccap_relation acap cap; ccap_relation bcap cap\<rbrakk> \<Longrightarrow> acap = bcap"
  apply (case_tac "cap_lift cap")
   apply (auto simp:ccap_relation_def split:option.splits)
  done

(* FIXME RT: put back in Ipc_R.thy *)
lemma valid_pspace'_splits[elim!]:
  "valid_pspace' s \<Longrightarrow> valid_objs' s"
  "valid_pspace' s \<Longrightarrow> pspace_aligned' s"
  "valid_pspace' s \<Longrightarrow> pspace_canonical' s"
  "valid_pspace' s \<Longrightarrow> pspace_in_kernel_mappings' s"
  "valid_pspace' s \<Longrightarrow> pspace_distinct' s"
  "valid_pspace' s \<Longrightarrow> valid_mdb' s"
  "valid_pspace' s \<Longrightarrow> no_0_obj' s"
  by (simp add: valid_pspace'_def)+

lemma transferCapsLoop_ccorres:
  assumes conds:
    "rcv_buffer \<noteq> 0"
    "ep \<noteq> Some 0"
  defines "check1 \<equiv>
    Guard ShiftError \<lbrace>0 <=s seL4_MsgExtraCapBits\<rbrace>
     (Guard ShiftError \<lbrace>seL4_MsgExtraCapBits <s 0x40\<rbrace>
       (\<acute>ret__int :==
          (if \<acute>i < 2 ^ unat seL4_MsgExtraCapBits - 1 then 1
           else 0)))"
      and "check2 \<equiv> \<lambda>caps.
    IF \<acute>ret__int \<noteq> 0 THEN
      Guard ArrayBounds \<lbrace>\<acute>i < 3\<rbrace> (\<acute>ret__int :==
        (if index (excaprefs_C caps) (unat \<acute>i) \<noteq> cte_Ptr 0 then 1
         else 0))
    FI"
  defines "W \<equiv> \<lambda>ep caps.
           check1;; check2 caps;;
           (While \<lbrace>\<acute>ret__int \<noteq> 0\<rbrace>
             (Guard ArrayBounds \<lbrace>\<acute>i < 3\<rbrace> (\<acute>slot :== index (excaprefs_C caps) (unat \<acute>i));;
              Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t \<acute>slot\<rbrace>
               (\<acute>cap :== h_val (hrs_mem \<acute>t_hrs) (cap_Ptr &(\<acute>slot\<rightarrow>[''cap_C''])));;
              \<acute>ret__unsigned_longlong :== CALL cap_get_capType(\<acute>cap);;
              \<acute>ret__int :== (if \<acute>ret__unsigned_longlong = scast cap_endpoint_cap then 1 else 0);;
              IF \<acute>ret__int \<noteq> 0 THEN
                \<acute>ret__unsigned_longlong :== CALL cap_endpoint_cap_get_capEPPtr(\<acute>cap);;
                \<acute>ret__int :== (if ep_Ptr \<acute>ret__unsigned_longlong = option_to_ptr ep then 1 else 0)
              FI;;
              IF \<acute>ret__int \<noteq> 0 THEN
                \<acute>ret__unsigned_longlong :== CALL cap_endpoint_cap_get_capEPBadge(\<acute>cap);;
                CALL setExtraBadge(Ptr rcv_buffer, ucast \<acute>ret__unsigned_longlong,\<acute>i);;
                \<acute>ret__unsigned_longlong :== CALL seL4_MessageInfo_get_capsUnwrapped(\<acute>info);;
                Guard ShiftError \<lbrace>unat \<acute>i < 31\<rbrace>
                 (\<acute>info :== CALL seL4_MessageInfo_set_capsUnwrapped(\<acute>info,
                  \<acute>ret__unsigned_longlong || scast ((1 :: sword32) << unat \<acute>i)))
              ELSE
                lvar_nondet_init dc_ret_' dc_ret_'_update;;
                IF \<acute>destSlot = cte_Ptr 0 THEN
                  break_C
                FI;;
                \<acute>dc_ret :== CALL deriveCap(\<acute>slot,\<acute>cap);;
                IF deriveCap_ret_C.status_C \<acute>dc_ret \<noteq> scast EXCEPTION_NONE THEN
                  break_C
                FI;;
                \<acute>ret__unsigned_longlong :== CALL cap_get_capType(deriveCap_ret_C.cap_C \<acute>dc_ret);;
                IF \<acute>ret__unsigned_longlong = scast cap_null_cap THEN
                  break_C
                FI;;
                CALL cteInsert(deriveCap_ret_C.cap_C \<acute>dc_ret,\<acute>slot,\<acute>destSlot);;
                \<acute>destSlot :== cte_Ptr 0
              FI;;
              \<acute>i :== \<acute>i + 1;; check1;; check2 caps))"
  defines "precond n mi slots \<equiv> (UNIV \<inter> \<lbrace>\<acute>i = of_nat n\<rbrace>
                 \<inter> \<lbrace>mi = message_info_to_H (\<acute>info)\<rbrace>
                 \<inter> \<lbrace>\<acute>destSlot = (if slots = [] then NULL else cte_Ptr (hd slots))
                                \<and> length slots \<le> 1 \<and> slots \<noteq> [0]\<rbrace>)"
  defines "is_the_ep \<equiv> \<lambda>cap. isEndpointCap cap \<and> ep \<noteq> None \<and> capEPPtr cap = the ep"
  defines "stable_masked \<equiv> \<lambda>scap excap. excap \<noteq> scap \<longrightarrow> excap = maskedAsFull scap scap"
  defines "relative_at  \<equiv> \<lambda>scap slot s. cte_wp_at'
                                 (\<lambda>cte. badge_derived' scap (cteCap cte) \<and>
                                        capASID scap = capASID (cteCap cte) \<and>
                                        cap_asid_base' scap = cap_asid_base' (cteCap cte) \<and>
                                        cap_vptr' scap = cap_vptr' (cteCap cte)) slot s"
  shows "drop n (interpret_excaps caps') = excaps_map caps
            \<and> n \<le> length (interpret_excaps caps')
         \<Longrightarrow> ccorresG rf_sr \<Gamma>
           (\<lambda>r (i, info). r = msgExtraCaps_update (\<lambda>_. i) (message_info_to_H info)
                       \<and> i \<le> 3) (\<lambda>s. (i_' s, info_' s))
           (valid_pspace' and valid_ipc_buffer_ptr' rcv_buffer and
           (\<lambda>s.  (\<forall>x \<in> set caps. s \<turnstile>' fst x
             \<and> cte_wp_at' (\<lambda>cte. slots \<noteq> [] \<or> is_the_ep (cteCap cte)
               \<longrightarrow> (fst x) =  (cteCap cte)) (snd x) s
             \<and> cte_wp_at' (\<lambda>cte. fst x \<noteq> NullCap  \<longrightarrow> stable_masked (fst x) (cteCap cte)) (snd x) s)) and
           (\<lambda>s. \<forall> sl \<in> (set slots). cte_wp_at' (isNullCap o cteCap) sl s) and
           (\<lambda>_. n + length caps \<le> 3 \<and> distinct slots ))
           (precond n mi slots)
           [catchbrk_C]
           (transferCapsToSlots ep rcv_buffer n caps slots mi)
           (W ep caps')"
unfolding W_def check1_def check2_def split_def
proof (rule ccorres_gen_asm, induct caps arbitrary: n slots mi)
  note if_split[split]
  case Nil
  thus ?case
    apply (simp only: transferCapsToSlots.simps)
    apply (rule ccorres_guard_imp2)
     apply (rule ccorres_Guard_Seq ccorres_rhs_assoc)+
     apply (rule ccorres_rhs_assoc2, rule ccorres_symb_exec_r)
       apply (rule ccorres_expand_while_iff [THEN iffD1])
       apply (rule ccorres_cond_false)
       apply (rule_tac P="\<lambda>_. n \<le> 3" and P'="\<lbrace>\<acute>i=of_nat n \<and> mi=message_info_to_H \<acute>info\<rbrace>"
                 in ccorres_from_vcg)
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp: return_def msgExtraCapBits_def word_le_nat_alt unat_of_nat)
      apply vcg
     apply (rule conseqPre, vcg, clarsimp)
     apply (simp add: seL4_MsgExtraCapBits_def)
    apply (clarsimp simp: excaps_map_def seL4_MsgExtraCapBits_def word_sle_def
                          precond_def)
    apply (subst interpret_excaps_test_null; clarsimp simp: unat_of_nat elim!: le_neq_trans)
    done
next
  note if_split[split]
  case (Cons x xs')
  let ?S="\<lbrace>\<acute>i=of_nat n \<and> mi=message_info_to_H \<acute>info\<rbrace>"
  have n3: "n \<le> 3" using Cons.prems by simp
  hence of_nat_n3[intro!]: "of_nat n \<le> (3 :: machine_word)"
    by (simp add: word_le_nat_alt unat_of_nat)
  have drop_n_foo: "\<And>xs n y ys. drop n xs = y # ys
     \<Longrightarrow> \<exists>xs'. length xs' = n \<and> xs = xs' @ (y # ys)"
    apply (frule_tac f=length in arg_cong, simp(no_asm_use))
    apply (cut_tac n=n and xs=xs in append_take_drop_id)
    apply (rule_tac x="take n xs" in exI)
    apply simp
    done

  have ep_cap_not_null: "\<And>cap. isEndpointCap cap \<Longrightarrow> cap \<noteq> NullCap"
    by (clarsimp simp: isCap_simps)

  have is_the_ep_maskedAsFull[simp]:"\<And>a b. is_the_ep (maskedAsFull a b) = is_the_ep a"
    apply (case_tac a)
     apply (simp add:maskedAsFull_def is_the_ep_def isCap_simps)+
    done

  have is_the_ep_fold:
  "(isEndpointCap (fst x) \<and> (\<exists>y. ep = Some y) \<and> capEPPtr (fst x) = the ep)
    = is_the_ep (fst x)"
    by (simp add:is_the_ep_def)

  have relative_fold:
   "\<And>scap slot s. (cte_wp_at'
    (\<lambda>cte. badge_derived' scap (cteCap cte) \<and>
    capASID scap = capASID (cteCap cte) \<and>
    cap_asid_base' scap = cap_asid_base' (cteCap cte) \<and>
    cap_vptr' scap = cap_vptr' (cteCap cte)) slot s) = relative_at scap slot s"
    by (simp add:relative_at_def)

  have stableD:
    "\<And>scap excap. stable_masked scap excap
    \<Longrightarrow> (badge_derived' scap excap \<and>
                 capASID scap = capASID excap \<and>
                 cap_asid_base' scap = cap_asid_base' excap \<and> cap_vptr' scap = cap_vptr' excap)"
    apply (clarsimp simp:stable_masked_def)
    apply (case_tac "excap = scap",simp+)
    apply (simp add:maskedAsFull_misc)
    done

  have stable_eq:
    "\<And>scap excap. \<lbrakk>stable_masked scap excap; isEndpointCap excap\<rbrakk> \<Longrightarrow> scap = excap"
     by (simp add:isCap_simps stable_masked_def maskedAsFull_def split:if_splits)

  have is_the_ep_stable:
    "\<And>a b. \<lbrakk>a \<noteq> NullCap \<longrightarrow> stable_masked a b; \<not> is_the_ep b \<rbrakk> \<Longrightarrow> \<not> is_the_ep a"
    apply (clarsimp simp:stable_masked_def maskedAsFull_def is_the_ep_def isCap_simps split:if_splits)
    apply auto
    done

  have is_the_ep_maskCapRights:
    "\<And>rights cap. is_the_ep (maskCapRights rights cap) = is_the_ep cap"
    apply (case_tac "isEndpointCap cap")
      apply (simp_all add:is_the_ep_def maskCapRights_def)
     apply (clarsimp simp:isCap_simps)
    apply (case_tac cap)
     apply (simp_all add:isCap_simps)
    apply (rename_tac acap)
    apply (case_tac acap)
     apply (clarsimp simp: RISCV64_H.maskCapRights_def isFrameCap_def)+
    done

  have is_the_ep_deriveCap:
  "\<And>slot cap. \<lbrace>\<lambda>s. \<not> (is_the_ep cap)\<rbrace> deriveCap slot cap \<lbrace>\<lambda>rv s. \<not> (is_the_ep rv)\<rbrace>, -"
    apply (case_tac cap)
     apply (simp_all add:deriveCap_def Let_def isCap_simps is_the_ep_def)
      apply (wp,clarsimp)+
      defer
     apply (wp,clarsimp)+
    apply (rename_tac acap)
    apply (case_tac acap)
     apply (simp_all add: RISCV64_H.deriveCap_def Let_def isCap_simps is_the_ep_def)
    apply (wp |clarsimp|rule conjI)+
    done

  have mask_right_eq_null:
    "\<And>r cap. (maskCapRights r cap = NullCap) = (cap = NullCap)"
    apply (case_tac cap)
     apply (simp_all add:maskCapRights_def isCap_simps)
    apply (rename_tac acap)
    apply (case_tac acap)
     apply (simp add: RISCV64_H.maskCapRights_def isFrameCap_def)+
    done

  have scast_2n_eq:
    "n \<le> 2 \<Longrightarrow> SCAST(32 signed \<rightarrow> 64) (1 << n) = (1 << n)"
    apply (case_tac "n=0"; simp)
    apply (case_tac "n=1"; simp)
    by (case_tac "n=2"; simp)

  note if_split[split del]
  note if_cong[cong]
  note extra_sle_sless_unfolds [simp del]
  from Cons.prems
  show ?case
    apply (clarsimp simp: Let_def word_sle_def[where b=5] split_def
                    cong: call_ignore_cong
                simp del: Collect_const)
    apply (rule ccorres_constOnFailure)
    apply (rule ccorres_guard_imp2)
     apply (rule ccorres_symb_exec_r)
       apply (rule ccorres_expand_while_iff [THEN iffD1])
       apply (rule ccorres_cond_true)
       apply (rule ccorres_rhs_assoc)+
       apply (rule_tac xf'=i_' in ccorres_abstract, ceqv)
       apply (rule ccorres_Guard_Seq)
       apply csymbr
       apply (rule ccorres_symb_exec_r)
         apply (rule_tac xf'=cap_' in ccorres_abstract,ceqv)
         apply (rename_tac n' cap')
         apply (rule_tac P="\<exists>acap. ccap_relation acap cap'
                     \<and> (isEndpointCap acap \<longrightarrow> capEPPtr acap \<noteq> 0)" in ccorres_gen_asm2)
         apply csymbr+
         apply (rule ccorres_symb_exec_r)
           apply (rule ccorres_seq_cond_raise[THEN iffD2])
           apply (rule_tac xf'=ret__int_' in ccorres_abstract_known, ceqv)
           apply (rule ccorres_cond2[where R=\<top>])
             apply (clarsimp simp: Collect_const_mem)
             apply (rule sym, rule from_bool_neq_0)

            \<comment> \<open>case where a badge is sent\<close>
            apply (rule ccorres_rhs_assoc)+
            apply csymbr
            apply (simp only: Let_def liftE_bindE withoutFailure_def fun_app_def)
            apply (ctac add: setExtraBadge_ccorres)
              apply (simp only: K_bind_def)
              apply (rule ccorres_case_sum_liftE)
              apply (csymbr, rule ccorres_abstract_cleanup)
              apply (rule ccorres_Guard_Seq)
              apply (csymbr, rule ccorres_abstract_cleanup)
              apply (rule ccorres_symb_exec_r)
                apply (rule ccorres_rhs_assoc2)
                apply (rule Cons.hyps)
                 apply (clarsimp simp: excaps_map_def dest!: drop_n_foo)
                apply simp
               apply vcg
              apply (rule conseqPre, vcg, clarsimp)
             apply (wp hoare_vcg_ball_lift)
            apply (simp split del: if_split)
            apply (vcg exspec=setExtraBadge_modifies)

           \<comment> \<open>case where a cap is sent (or rather a send is attempted)\<close>
           apply (simp add: split_def del: Collect_const
                      cong: call_ignore_cong split del: if_split)
           apply (rule ccorres_rhs_assoc)+
           apply csymbr
           apply wpc
            apply (rule ccorres_cond_true_seq)
            apply (simp add: returnOk_liftE)
            apply (rule ccorres_case_sum_liftE)
            apply (rule ccorres_split_throws)
             apply (rule_tac P=\<top> and P'="?S" in ccorres_break_return)
              apply clarsimp
             apply simp
            apply vcg
           apply (rule ccorres_cond_false_seq)
           apply (simp)

           \<comment> \<open>case not diminish\<close>
           apply (rule ccorres_split_nothrowE)
                apply (rule unifyFailure_ccorres)
                apply (ctac add: deriveCap_ccorres')
               apply ceqv
              apply (simp only: refl not_True_eq_False Collect_False ccorres_seq_simps)
              apply csymbr
              apply (rule_tac Q=\<top> and Q'=\<top> in ccorres_split_when_throwError_cond_break)
                 apply (clarsimp simp: cap_get_tag_isCap Collect_const_mem)
                apply (rule_tac P=\<top> and P'="?S" in ccorres_break)
                 apply clarsimp
                apply simp
               apply (simp(no_asm) add: liftE_bindE split del: if_split)
               apply (ctac add: cteInsert_ccorres)
                 apply (rule ccorres_case_sum_liftE)
                 apply csymbr
                 apply (rule ccorres_symb_exec_r)
                   apply (rule ccorres_rhs_assoc2)
                   apply (rule_tac P="ccorresG rf_sr \<Gamma> r xf Pre Pre' hs a" for r xf Pre Pre' hs a in rsubst)
                    apply (rule Cons.hyps)
                     apply (clarsimp simp: excaps_map_def dest!: drop_n_foo)
                    apply simp
                   apply simp
                  apply vcg
                 apply (rule conseqPre, vcg)
                 apply clarsimp
                apply (rule cteInsert_assume_Null)
                apply simp
                apply (wp cteInsert_valid_pspace hoare_valid_ipc_buffer_ptr_typ_at'
                          hoare_vcg_const_Ball_lift cteInsert_cte_wp_at)
               apply (vcg exspec=cteInsert_modifies)
              apply vcg
             apply (simp)
             apply (rule ccorres_split_throws)
              apply (rule_tac P=\<top> and P'="?S" in ccorres_break)
               apply clarsimp
              apply simp
             apply vcg
            apply wp
            apply (simp cong: conj_cong)
               apply (rule_tac Q' ="\<lambda>rcap s. s \<turnstile>' rcap
                 \<and> (rcap\<noteq> NullCap \<longrightarrow> cte_wp_at' (is_derived' (ctes_of s) (snd x) rcap \<circ> cteCap) (snd x) s)
                 \<and> valid_pspace' s \<and> valid_ipc_buffer_ptr' rcv_buffer s \<and> length slots = 1
                 \<and> \<not> is_the_ep rcap
                 \<and> (\<forall>x\<in>set slots. cte_wp_at' (isNullCap \<circ> cteCap) x s)
                 \<and> (\<forall>x\<in>set xs'. s \<turnstile>' fst x
                    \<and> cte_wp_at' (\<lambda>c. is_the_ep (cteCap c) \<longrightarrow> fst x = cteCap c) (snd x) s
                    \<and> cte_wp_at' (\<lambda>c. fst x \<noteq> NullCap \<longrightarrow> stable_masked (fst x) (cteCap c)) (snd x) s)"
                 in hoare_strengthen_postE_R)
                prefer 2
                 apply (clarsimp simp:cte_wp_at_ctes_of valid_pspace_mdb' valid_pspace'_splits
                   valid_pspace_valid_objs' is_derived_capMasterCap image_def)
                 apply (clarsimp split:if_splits)
                 apply (rule conjI)
                  apply clarsimp+
                 apply (rule conjI)
                  apply (drule(1) bspec)+
                  apply (rule conjI | clarsimp)+
                   apply (clarsimp simp:is_the_ep_def isCap_simps stable_masked_def)
                  apply (drule(1) bspec)+
                  apply (rule conjI | clarsimp)+
                   apply (clarsimp simp:is_the_ep_def stable_masked_def split:if_splits)+
                 apply (case_tac "a = cteCap cteb",clarsimp)
                  apply (simp add:maskedAsFull_def split:if_splits)
                 apply (simp add:maskedAsFull_again)
               apply (wp deriveCap_derived is_the_ep_deriveCap)
            apply (vcg exspec=deriveCap_modifies)

          \<comment> \<open>remaining non ccorres subgoals\<close>
           apply (clarsimp simp: Collect_const_mem if_1_0_0
                     split del: if_split)
           apply (rule_tac Q'="\<lbrace>\<acute>ret__int = from_bool (cap_get_tag cap' = scast cap_endpoint_cap
                                        \<and> ep_Ptr (capEPPtr_CL (cap_endpoint_cap_lift cap')) = option_to_ptr ep)
                  \<and> n' = of_nat n \<and> ((slots \<noteq> [] \<or> isEndpointCap (fst x) \<or> is_the_ep (cap_to_H (the (cap_lift cap'))))
                                       \<longrightarrow> ccap_relation (fst x) cap' )
                  \<and> (isEndpointCap (fst x) \<longrightarrow> capEPPtr (fst x) \<noteq> 0)\<rbrace>
                    \<inter> precond n mi slots"
              in conseqPost[OF _ _ order_refl])
             apply vcg
            apply (rule subsetI)
            apply (clarsimp simp: word_of_nat_less from_bool_0 precond_def
                                cap_get_tag_isCap unat_of_nat)
            apply (rule conjI)
             apply (clarsimp simp: cap_get_tag_EndpointCap cap_get_tag_isCap[symmetric]
                                   ep_cap_not_null)
             apply (clarsimp simp: ccap_relation_def map_option_Some_eq2)
             apply (simp add: message_info_to_H_def word_ao_dist)
             apply (fold shiftl_1)[1]
             apply (subst scast_2n_eq, simp)
             apply (subst and_mask_eq_iff_shiftr_0[THEN iffD2],
                  subst shiftl_shiftr2, simp, simp)
             apply (simp add: seL4_MessageInfo_lift_def word_bw_assocs
                              word_sle_def t2n_mask_eq_if)
            apply (rule conjI)
             apply (clarsimp simp: ccap_rights_relation_def cap_rights_to_H_def
                                   allRights_def excaps_map_def split_def
                            dest!: drop_n_foo interpret_excaps_eq)
            apply (clarsimp simp:from_bool_def split:bool.splits)
             apply (case_tac "isEndpointCap (fst x)")
              apply (clarsimp simp: cap_get_tag_EndpointCap ep_cap_not_null cap_get_tag_isCap[symmetric])
              apply (clarsimp simp: option_to_ptr_def option_to_0_def split:option.splits)
             apply (clarsimp simp: cap_get_tag_EndpointCap ep_cap_not_null cap_get_tag_isCap[symmetric])
             apply (case_tac "ccap_relation (fst x) cap'")
              apply (simp add:ccap_relation_lift)
              apply (drule(1) ccap_relation_inject)
              apply (drule sym[where t = "fst x"])
              apply (clarsimp simp:isCap_simps)
             apply (clarsimp simp: is_the_ep_def ccap_relation_lift isCap_simps)
             apply (clarsimp simp: option_to_ptr_def option_to_0_def split:option.splits)
            apply (clarsimp simp:option_to_ptr_def option_to_0_def)
            apply (case_tac "isEndpointCap (fst x)")
             apply (clarsimp simp: isCap_simps)
             apply (drule_tac acap = acap in ccap_relation_inject)
              apply assumption
             apply clarsimp
             apply (clarsimp simp: ccap_relation_def map_option_Some_eq2 split:option.splits)
             apply (clarsimp simp: cap_endpoint_cap_lift_def option_to_ptr_def
                                option_to_0_def cap_to_H_def Let_def split:cap_CL.splits split:if_splits)
            apply clarsimp
           apply (simp only:badge_derived_mask capASID_mask cap_asid_base_mask'
             cap_vptr_mask' maskCap_valid mask_right_eq_null)
           apply (simp only:is_the_ep_fold relative_fold)
           apply (clarsimp simp:Collect_const_mem if_1_0_0
             split del:if_split)
           apply (rule conseqPre, vcg, clarsimp simp: Collect_const_mem)
          apply (clarsimp simp: if_1_0_0 Collect_const_mem
                              trans[OF eq_commute from_bool_eq_if]
                              from_bool_0
                   split del: if_split simp del: Collect_const)
          apply vcg
         apply (simp only:is_the_ep_fold)
         apply (clarsimp simp:Collect_const_mem if_1_0_0
            split del:if_split)
         apply (rule conseqPre, vcg)
         apply (clarsimp split del: if_split)
        apply (clarsimp split del: if_split
                       simp add: Collect_const[symmetric] precond_def
                       simp del: Collect_const)
        apply (rule HoarePartial.Seq[rotated] HoarePartial.Cond[OF order_refl]
                  HoarePartial.Basic[OF order_refl] HoarePartial.Skip[OF order_refl]
                  HoarePartial.Guard[OF order_refl])+
       apply (simp only:is_the_ep_fold)
       apply (clarsimp simp:Collect_const_mem if_1_0_0
            split del:if_split)
       apply (rule conseqPre, vcg, rule subsetI, clarsimp)
    apply (simp only:is_the_ep_fold)
    apply (clarsimp simp: Collect_const_mem seL4_MsgExtraCapBits_def
                          word_sle_def if_1_0_0 precond_def
                          msg_max_length_def max_ipc_words word_of_nat_less
                          excaps_map_def unat_of_nat valid_pspace'_def
                          cte_wp_at_ctes_of
                   dest!: drop_n_foo interpret_excaps_eq)
    apply (frule(1) ctes_of_valid')
    apply (rule cmap_relationE1[OF cmap_relation_cte], assumption+)
    apply (clarsimp simp: typ_heap_simps' split_def is_the_ep_maskCapRights)
    apply (frule ccte_relation_ccap_relation)
    apply (intro conjI impI)
         apply (intro allI impI)
         apply clarsimp
         apply fastforce
        apply (subgoal_tac "fst x = cteCap cte",simp)
        apply clarsimp
        apply (elim disjE)
         apply (clarsimp simp:ep_cap_not_null stable_masked_def)
        apply (clarsimp dest!:ccap_relation_lift stable_eq simp: cap_get_tag_isCap)
       apply (clarsimp simp:valid_cap_simps' isCap_simps)
       apply (subgoal_tac "slots \<noteq> []")
        apply simp
       apply clarsimp
       apply (elim disjE)
        apply (clarsimp simp:ep_cap_not_null stable_masked_def)
        apply (clarsimp dest!:ccap_relation_lift stable_eq simp: cap_get_tag_isCap)
       apply (clarsimp dest!:ccap_relation_lift simp:cap_get_tag_isCap is_the_ep_def)
      apply (clarsimp simp:valid_cap_simps' isCap_simps)
     apply (intro exI conjI,assumption)
    apply (clarsimp simp: ccap_relation_def map_option_Some_eq2
                            isCap_simps valid_cap_simps')+
    done
qed

lemma cte_wp_at_imp_consequent':
  "cte_wp_at' Q p s \<longrightarrow> cte_wp_at' (\<lambda>cte. P cte \<longrightarrow> Q cte) p s"
  by (clarsimp simp: cte_wp_at_ctes_of)

lemma lookupExtraCaps_srcs2:
  "\<lbrace>\<top>\<rbrace> lookupExtraCaps t buf mi \<lbrace>\<lambda>caps s. \<forall>x \<in> set caps. cte_wp_at'
              (\<lambda>cte. cteCap cte = fst x) (snd x) s\<rbrace>,-"
  apply (simp add: lookupExtraCaps_def lookupCapAndSlot_def
                   split_def lookupSlotForThread_def
                   getSlotCap_def)
  apply (wp mapME_set[where R=\<top>] getCTE_wp'
             | simp add: cte_wp_at_ctes_of
             | wp (once) hoare_drop_imps
             | (rule hoare_strengthen_post [OF hoare_TrueI], rule allI, rule impI, rule TrueI))+
  done

lemma transferCaps_ccorres [corres]:
  notes if_cong[cong]
  notes extra_sle_sless_unfolds[simp del]
  shows
  "ccorres (\<lambda>r r'. r = message_info_to_H r') ret__struct_seL4_MessageInfo_C_'
    (valid_pspace' and tcb_at' receiver
     and (case_option \<top> valid_ipc_buffer_ptr') receiveBuffer
     and (excaps_in_mem caps \<circ> ctes_of)
     and K (length caps \<le> 3)
     and K (ep \<noteq> Some 0)
     and K (receiveBuffer \<noteq> Some 0)
     and K (unat (msgExtraCaps mi) \<le> 3))
    (UNIV \<inter> \<lbrace>interpret_excaps (\<acute>current_extra_caps) = excaps_map caps\<rbrace>
          \<inter> \<lbrace>\<acute>receiver = tcb_ptr_to_ctcb_ptr receiver\<rbrace>
          \<inter> \<lbrace> mi = message_info_to_H \<acute>info\<rbrace>
          \<inter> \<lbrace>\<acute>receiveBuffer = Ptr (option_to_0 receiveBuffer)\<rbrace>
          \<inter> \<lbrace>\<acute>endpoint = option_to_ptr ep\<rbrace>) []
    (transferCaps mi caps ep receiver receiveBuffer)
    (Call transferCaps_'proc)" (is "ccorres _ _ ?P _ _ _ _")
  apply (unfold K_def, intro ccorres_gen_asm)
  apply (cinit lift: current_extra_caps_' receiver_' info_' receiveBuffer_' endpoint_'
    simp: getThreadCSpaceRoot_def locateSlot_conv whileAnno_def)
   apply csymbr+
   apply (rule_tac P="?P" and P'="{s. info_' s = info}" in ccorres_inst)
   apply (cases "receiveBuffer = None")
    apply (clarsimp simp: option_to_0_def getReceiveSlots_def
                simp del: Collect_const)
    apply (rule ccorres_guard_imp2)
     apply (simp (no_asm))
     apply (rule_tac R'=UNIV in ccorres_split_throws [OF ccorres_return_C], simp_all)[1]
     apply vcg
     apply simp
    apply (simp add: message_info_to_H_def word_sless_def word_sle_def)
   apply (cases "caps = []")
    apply (clarsimp simp: interpret_excaps_test_null excaps_map_def
                simp del: Collect_const not_None_eq)
    apply (erule notE, rule ccorres_guard_imp2)
     apply (simp (no_asm))
     apply (rule ccorres_symb_exec_l)
        apply (rule_tac R'=UNIV in ccorres_split_throws [OF ccorres_return_C], simp_all)[1]
        apply vcg
        apply simp
       apply ((wp empty_fail_getReceiveSlots)+)[3]
    apply (simp add: message_info_to_H_def word_sless_def word_sle_def)
   apply (simp add: option_to_0_def ccorres_cond_iffs
                    interpret_excaps_test_null excaps_map_def
               del: Collect_const
               cong: call_ignore_cong)
   apply (elim exE)
   apply (clarsimp simp: Collect_const[symmetric] Collect_False
                         signed_shift_guard_simpler_64
               simp del: Collect_const
                   cong: call_ignore_cong)
   apply (rule ccorres_guard_imp2)
    apply (ctac add: getReceiveSlots_ccorres)
      apply (elim conjE)
      apply (rule ccorres_symb_exec_r)
        apply (rule ccorres_add_return2)
        apply (rule ccorres_split_nothrow_novcg)
            apply (rule ccorres_Catch)
            apply (rule_tac caps=caps and caps'=current_extra_caps in transferCapsLoop_ccorres, simp+)
            apply (simp add: excaps_map_def)
           apply ceqv
          apply csymbr
          apply (rule ccorres_abstract_cleanup)
          apply (rule ccorres_return_C, simp+)[1]
         apply wp
        apply (simp add: guard_is_UNIV_def)
        apply (clarsimp simp: message_info_to_H_def split: if_split)
        apply (erule notE, (rule sym)?, rule less_mask_eq)
        apply (simp add: word_leq_minus_one_le)
       apply (subgoal_tac "rv \<noteq> [0]")
        apply simp
        apply vcg
       apply clarsimp
      apply (rule conseqPre, vcg, clarsimp)
     apply (simp add: o_def pred_conj_def)
     apply (strengthen cte_wp_at_imp_consequent')
     apply wp
    apply (simp only: mem_simps simp_thms split: if_split)
    apply (vcg exspec=getReceiveSlots_modifies)
   apply (clarsimp simp: message_info_to_H_def excaps_in_mem_def
                         slotcap_in_mem_def split_def cte_wp_at_ctes_of
                         word_sless_def word_sle_def)
   apply fastforce
  apply clarsimp
  done

definition
  mi_from_H :: "Types_H.message_info \<Rightarrow> seL4_MessageInfo_CL"
where
 "mi_from_H mi \<equiv>
     \<lparr> label_CL = msgLabel mi,
       capsUnwrapped_CL = msgCapsUnwrapped mi,
       extraCaps_CL = msgExtraCaps mi,
       length_CL = msgLength mi \<rparr>"

lemma ccorres_add_returnOk2:
  "ccorres_underlying rf_sr G r xf arrel axf P P' hs (a >>=E returnOk) c
    \<Longrightarrow> ccorres_underlying rf_sr G r xf arrel axf P P' hs a c"
  by (rule ccorres_add_returnOk)

lemma capFaultOnFailure_ccorres:
  "ccorres (f \<currency> r) xf P P' hs a c
    \<Longrightarrow> ccorres ((\<lambda>x y z. \<exists>w. x = CapFault addr b w \<and> f w y z) \<currency> r)
             xf P P' hs
             (capFaultOnFailure addr b a) c"
  apply (simp add: capFault_injection injection_handler_liftM)
  apply (erule ccorres_rel_imp)
  apply (auto split: sum.split)
  done

definition
 "cfault_rel2 \<equiv> \<lambda>ft exnvar err. exnvar = (scast EXCEPTION_FAULT :: machine_word) \<and>
                   cfault_rel (Some ft) (errfault err) (errlookup_fault err)"

lemma takeWhile_eq:
  "\<lbrakk> \<And>m. \<lbrakk> m < length ys \<rbrakk> \<Longrightarrow> P (xs ! m);
       length ys < length xs \<Longrightarrow> \<not> P (xs ! length ys);
       length ys \<le> length xs;
     \<And>m. m < length ys \<Longrightarrow> xs ! m = ys ! m \<rbrakk>
    \<Longrightarrow> takeWhile P xs = ys"
proof (induct xs arbitrary: n ys)
  case Nil
  thus ?case by simp
next
  case (Cons x xs' ys')
  have P: "\<And>v m. \<lbrakk> (x # xs') ! m = v; m < length ys' \<rbrakk>
                     \<Longrightarrow> P v"
    using Cons.prems by clarsimp
  show ?case using Cons.prems(2-3)
    apply simp
    apply (cases ys')
     apply simp
    apply (subst P[where m1=0])
       apply simp+
    apply (rule conjI)
     apply (cut_tac m1=0 in Cons.prems(4), simp+)
    apply (rule Cons.hyps)
       apply (rule_tac m1="Suc m" in P, simp+)
    apply (cut_tac m1="Suc m" in Cons.prems(4), simp+)
    done
qed

lemma ccorres_sequenceE_while':
  fixes axf :: "globals myvars \<Rightarrow> 'e" shows
  "\<lbrakk>\<And>ys. length ys < length xs \<Longrightarrow>
        ccorres_underlying sr \<Gamma> (inr_rrel (\<lambda>rv rv'. r' (ys @ [rv]) rv')) xf'
                            (inl_rrel arrel) axf
                            (F (length ys)) (Q \<inter> {s. i_' s = of_nat (length ys) \<and> r' ys (xf' s)}) hs
                            (xs ! length ys) body;
    \<And>n. P n = (n < of_nat (length xs));
    \<And>s. s \<in> Q \<Longrightarrow> \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> {s} body (Q \<inter> {t. i_' t = i_' s}),UNIV;
    \<And>n. n < length xs \<Longrightarrow> \<lbrace>F n\<rbrace> xs ! n \<lbrace>\<lambda>_. F (Suc n)\<rbrace>, -;
     length xs < 2 ^ word_bits;
     \<forall>s f. xf' (i_'_update f s) = xf' s
                 \<and> ((i_'_update f s \<in> Q) = (s \<in> Q))
                 \<and> (\<forall>s'. ((s', i_'_update f s) \<in> sr) = ((s', s) \<in> sr)) \<rbrakk>
    \<Longrightarrow> ccorres_underlying sr \<Gamma> (inr_rrel (\<lambda>rv (i', rv'). r' rv rv' \<and> i' = of_nat (length xs)))
                  (\<lambda>s. (i_' s, xf' s)) arrel axf
                  (F 0) (Q \<inter> {s. r' [] (xf' s)}) hs
          (sequenceE xs)
          (Basic (\<lambda>s. i_'_update (\<lambda>_. 0) s) ;;
           While {s. P (i_' s)} (body;;
             Basic (\<lambda>s. i_'_update (\<lambda>_. i_' s + 1) s)))"
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_symb_exec_r)
     apply (rule ccorres_rel_imp2)
       apply (rule ccorres_sequenceE_while_gen'[where i=0, simplified, where xf_update=i_'_update],
              (assumption | simp)+)
         apply (simp add: word_bits_def)
        apply simp+
    apply vcg
   apply (rule conseqPre, vcg)
   apply clarsimp
  apply simp
  done

lemma lookupExtraCaps_ccorres:
  notes if_cong[cong] nat_min_simps [simp del]
  shows
  "ccorres
     ((\<lambda>ft _ err.
                   cfault_rel (Some ft) (errfault err) (errlookup_fault err))
          \<currency> (\<lambda>xs ys. interpret_excaps ys = excaps_map xs))
      (liftxf errstate fst snd
           (\<lambda>s. (ret__unsigned_long_' s, current_extra_caps_' (globals s))))
      (valid_pspace' and tcb_at' thread
             and (case buffer of Some x\<Rightarrow> valid_ipc_buffer_ptr' x | _ \<Rightarrow> \<top>)
             and (\<lambda>s. unat (msgExtraCaps info) <= 3))
      (UNIV \<inter> {s. thread_' s = tcb_ptr_to_ctcb_ptr thread}
            \<inter> {s. bufferPtr_' s = option_to_ptr buffer}
            \<inter> {s. seL4_MessageInfo_lift (info_' s) = mi_from_H info
                  }) []
      (lookupExtraCaps thread buffer info) (Call lookupExtraCaps_'proc)"
proof -
  let ?curr = "\<lambda>s. current_extra_caps_' (globals s)"
  let ?EXCNONE = "{s. ret__unsigned_long_' s = scast EXCEPTION_NONE}"
  let ?interpret = "\<lambda>v n. take n (array_to_list (excaprefs_C v))"
  note empty_fail_cond[simp]
  show ?thesis
  apply (rule ccorres_gen_asm)+
  apply (cinit(no_subst_asm) lift: thread_' bufferPtr_' info_' simp: whileAnno_def)
   apply (clarsimp simp add: getExtraCPtrs_def lookupCapAndSlot_def
                             capFault_bindE
                   simp del: Collect_const)
   apply (simp add: liftE_bindE del: Collect_const)
   apply wpc
   apply (rename_tac word1 word2 word3 word4)
   apply (simp del: Collect_const)
   apply wpc
    apply (simp add: option_to_ptr_def option_to_0_def mapME_Nil)
    apply (rule ccorres_rhs_assoc2, rule ccorres_split_throws)
     apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: returnOk_def return_def)
     apply (simp add: excaps_map_def)
     apply (subst interpret_excaps_test_null[where n=0, simplified, symmetric])
     apply (simp add: word_sle_def word_sless_def)
    apply vcg
   apply (simp add: id_def[symmetric] del: Collect_const)
   apply (rule ccorres_symb_exec_r)
     apply csymbr
     apply csymbr
     apply (rename_tac "lngth")
     apply (unfold mapME_def)[1]
     apply (simp add: mi_from_H_def del: Collect_const)
     apply (rule ccorres_symb_exec_l)
        apply (rule_tac P="length xs = unat word2" in ccorres_gen_asm)
        apply (rule ccorres_rhs_assoc2)
        apply (rule ccorres_add_returnOk2,
               rule ccorres_splitE_novcg)
             apply (rule_tac xf'="?curr"
                       and  r'="\<lambda>xs v. excaps_map xs = ?interpret v (length xs)"
                       and   Q="UNIV"
                       and   F="\<lambda>n s. valid_pspace' s \<and> tcb_at' thread s \<and>
                                      (case buffer of Some x \<Rightarrow> valid_ipc_buffer_ptr' x | _ \<Rightarrow> \<top>) s \<and>
                                       (\<forall>m < length xs. user_word_at (xs ! m)
                                                     (x2 + (of_nat m + (msgMaxLength + 2)) * 8) s)"
                          in ccorres_sequenceE_while')
                  apply (simp add: split_def)
                  apply (rule ccorres_rhs_assoc)+
                  apply (rule ccorres_guard_imp2)
                   apply (rule ccorres_symb_exec_r)
                     apply (rule_tac xf'=cptr_' in ccorres_abstract, ceqv)
                     apply (ctac add: capFaultOnFailure_ccorres
                               [OF lookupSlotForThread_ccorres'])
                        apply (rule_tac P="is_aligned rv 5" in ccorres_gen_asm)
                        apply (simp add: ccorres_cond_iffs liftE_bindE)
                        apply (rule ccorres_symb_exec_l [OF _ _ _ empty_fail_getSlotCap])
                          apply (rule_tac P'="UNIV \<inter> {s. excaps_map ys
                                                         = ?interpret (?curr s) (length ys)}
                                                   \<inter> {s. i_' s = of_nat (length ys)}"
                                     in ccorres_from_vcg[where P=\<top>])
                          apply (rule allI, rule conseqPre, vcg)
                          apply (simp add: returnOk_liftE)
                          apply (clarsimp simp: Bex_def in_monad)
                          apply (clarsimp simp: excaps_map_def array_to_list_def
                                                lookupSlot_raw_rel_def)
                          apply (subgoal_tac "length ys < 3")
                           apply (simp add: take_Suc_conv_app_nth take_map
                                            unat_of_nat64[unfolded word_bits_conv]
                                            word_of_nat_less)
                          apply (simp add: word_less_nat_alt)
                         apply wp+
                       apply (clarsimp simp: ccorres_cond_iffs)
                       apply (rule_tac  P= \<top>
                                and P'="{x. errstate x= lu_ret___struct_lookupSlot_raw_ret_C \<and>
                                            rv' = (xs ! length ys)}"
                                  in ccorres_from_vcg_throws)
                       apply (rule allI, rule conseqPre, vcg)
                       apply (clarsimp simp: throwError_def return_def)
                       apply (frule lookup_failure_rel_fault_lift, assumption)
                       apply (clarsimp simp: cfault_rel2_def)
                       apply (clarsimp simp: cfault_rel_def)
                       apply (simp add: seL4_Fault_CapFault_lift)
                       apply (clarsimp simp: is_cap_fault_def)
                      apply wp
                      apply (rule hoare_strengthen_postE_R, rule lsft_real_cte)
                      apply (clarsimp simp: obj_at'_def projectKOs objBits_simps')
                     apply (vcg exspec=lookupSlot_modifies)
                    apply vcg
                   apply (rule conseqPre, vcg)
                   apply clarsimp
                  apply (clarsimp simp: valid_pspace'_def)
                  apply (drule spec, drule(1) mp)
                  apply (drule(1) user_word_at_cross_over [OF _ _ refl])
                  apply (simp add: field_simps msgMaxLength_def
                                   seL4_MsgLengthBits_def
                                   seL4_MsgMaxLength_def
                                   msgLengthBits_def)
                  apply (subst valid_ipc_buffer_ptr_array, simp+,
                    simp add: msg_align_bits unat_word_ariths unat_of_nat,
                    simp add: msg_align_bits unat_word_ariths unat_of_nat)+
                  apply clarsimp
                 apply simp
                apply (rule conseqPre)
                 apply (vcg exspec=lookupSlot_modifies)
                apply clarsimp
               apply (simp add: split_def)
               apply (rule hoare_pre, wp)
               apply simp
              apply (simp add: word_less_nat_alt word_bits_def)
             apply simp
            apply (rule ceqv_tuple2)
             apply ceqv
            apply ceqv
           apply (simp del: Collect_const)
           apply (rule_tac P'="{s. snd rv'=?curr s}"
                       and P="\<lambda>s. length rv = length xs \<and> (\<forall>x \<in> set rv. snd x \<noteq> 0)"
                    in ccorres_from_vcg_throws)
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp: returnOk_def return_def
                                 seL4_MsgExtraCapBits_def)
           apply (simp add: word_sle_def interpret_excaps_def
                            excaps_map_def)
           apply (rule conjI)
            apply (clarsimp simp: array_to_list_def)
            apply (rule takeWhile_eq, simp_all)[1]
             apply (drule_tac f="\<lambda>xs. xs ! m" in arg_cong)
             apply (clarsimp simp: split_def NULL_ptr_val[symmetric])
           apply (clarsimp simp: array_to_list_def)
           apply (rule takeWhile_eq, simp_all)[1]
            apply (drule_tac f="\<lambda>xs. xs ! m" in arg_cong)
            apply (clarsimp simp: split_def NULL_ptr_val[symmetric])
           apply (simp add: word_less_nat_alt)
          apply simp
         apply (simp add: mapME_def[symmetric] split_def
                          liftE_bindE[symmetric])
         apply (wp mapME_length mapME_set | simp)+
           apply (rule_tac Q'="\<lambda>rv. no_0_obj' and real_cte_at' rv"
                      in hoare_strengthen_postE_R, wp lsft_real_cte)
           apply (clarsimp simp: cte_wp_at_ctes_of)
          apply (wpsimp)+
        apply (clarsimp simp: guard_is_UNIV_def
                       elim!: inl_inrE)
       apply (rule hoare_pre, (wp mapM_wp' | simp)+)
      apply (rule mapM_loadWordUser_user_words_at)
     apply simp
    apply vcg
   apply (rule conseqPre, vcg, clarsimp)
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp add: valid_pspace'_def)
   apply (simp add: upto_enum_step_def
             split: if_split_asm)
   apply (simp add: word_size upto_enum_word field_simps wordSize_def'
               del: upt.simps)
  apply (clarsimp simp: excaps_map_def option_to_ptr_def option_to_0_def
                        valid_ipc_buffer_ptr'_def)
  done
qed

lemma interpret_excaps_empty:
  "(interpret_excaps caps = []) = (index (excaprefs_C caps) 0 = NULL)"
  by (simp add: interpret_excaps_test_null)

lemma getSlotCap_slotcap_in_mem:
  "\<lbrace>\<top>\<rbrace> getSlotCap slot \<lbrace>\<lambda>cap s. slotcap_in_mem cap slot (ctes_of s)\<rbrace>"
  apply (simp add: getSlotCap_def)
  apply (wp getCTE_wp')
  apply (clarsimp simp: cte_wp_at_ctes_of slotcap_in_mem_def)
  done

lemma lookupExtraCaps_excaps_in_mem[wp]:
  "\<lbrace>\<top>\<rbrace> lookupExtraCaps thread buffer info \<lbrace>\<lambda>rv s. excaps_in_mem rv (ctes_of s)\<rbrace>,-"
  apply (simp add: excaps_in_mem_def lookupExtraCaps_def lookupCapAndSlot_def
                   split_def)
  apply (wp mapME_set)
      apply (wpsimp wp: getSlotCap_slotcap_in_mem)+
  done

lemma doNormalTransfer_ccorres [corres]:
  "ccorres dc xfdc
    (valid_pspace' and tcb_at' sender
        and tcb_at' receiver
        and K (endpoint \<noteq> Some 0)
        and (case_option \<top> valid_ipc_buffer_ptr' sendBuffer)
        and (case_option \<top> valid_ipc_buffer_ptr' receiveBuffer))
    (UNIV \<inter> \<lbrace>\<acute>sender = tcb_ptr_to_ctcb_ptr sender\<rbrace>
          \<inter> \<lbrace>\<acute>receiver = tcb_ptr_to_ctcb_ptr receiver\<rbrace>
          \<inter> \<lbrace>\<acute>sendBuffer = Ptr (option_to_0 sendBuffer)\<rbrace>
          \<inter> \<lbrace>\<acute>receiveBuffer = Ptr (option_to_0 receiveBuffer)\<rbrace>
          \<inter> \<lbrace>canGrant = to_bool \<acute>canGrant\<rbrace>
          \<inter> \<lbrace>\<acute>badge___unsigned_long = badge\<rbrace>
          \<inter> \<lbrace>\<acute>endpoint = option_to_ptr endpoint\<rbrace>)  []
    (doNormalTransfer sender sendBuffer endpoint badge canGrant
                      receiver receiveBuffer)
    (Call doNormalTransfer_'proc)"
proof -
  have word_0_le_helper:
    "\<And>i :: sword32. \<lbrakk> i <s (1 << unat (scast seL4_MsgExtraCapBits :: word32)) - 1; 0 <=s i \<rbrakk>
           \<Longrightarrow> 0 <=s i + 1"
    apply (simp add: seL4_MsgExtraCapBits_def word_sle_msb_le
                                 word_sless_msb_less msb_nth)
    apply (clarsimp simp: word_eq_iff)
    apply (drule bang_is_le)
    apply (unat_arith; simp add: take_bit_nat_def)
    done

  show ?thesis
    apply (cinit lift: sender_' receiver_' sendBuffer_' receiveBuffer_'
                       canGrant_' badge___unsigned_long_' endpoint_'
                 cong: call_ignore_cong)
     apply (clarsimp cong: call_ignore_cong)
     apply (ctac(c_lines 2, no_vcg) add: getMessageInfo_ccorres')
       apply (rule_tac xf'="\<lambda>s. current_extra_caps_' (globals s)"
                   and r'="\<lambda>c c'. interpret_excaps c' = excaps_map c"
              in ccorres_split_nothrow_novcg)
           apply (rule ccorres_if_lhs)
            apply (simp add: catch_def to_bool_def ccorres_cond_iffs)
            apply (rule_tac xf'="\<lambda>s. (status_' s, current_extra_caps_' (globals s))"
                        and ef'=fst and vf'=snd and es=errstate
                   in ccorres_split_nothrow_case_sum)
                 apply (rule ccorres_call, rule lookupExtraCaps_ccorres, simp+)
                apply (rule ceqv_tuple2, ceqv, ceqv)
               apply (simp add: ccorres_cond_iffs)
               apply (rule ccorres_return_Skip')
              apply (simp add: ccorres_cond_iffs)
              apply (rule ccorres_from_vcg[where P=\<top> and P'=UNIV])
              apply (rule allI, rule conseqPre, vcg)
              apply (clarsimp simp: return_def excaps_map_def interpret_excaps_empty
                                    word_sless_def word_sle_def)
             apply wp
            apply simp
            apply (vcg exspec=lookupExtraCaps_modifies)
           apply (simp add: to_bool_def ccorres_cond_iffs)
           apply (rule ccorres_return[where R=\<top> and R'=UNIV], vcg)
           apply (clarsimp simp: excaps_map_def interpret_excaps_empty)
          apply ceqv
         apply csymbr
         apply (ctac add: copyMRs_ccorres)
           apply (ctac add: transferCaps_ccorres)
             apply csymbr
             apply (ctac(c_lines 2, no_vcg) add: setMessageInfo_ccorres)
               apply ctac
              apply wp
             apply (clarsimp simp: Kernel_C.badgeRegister_def RISCV64_H.badgeRegister_def
                                   RISCV64.badgeRegister_def a0_def)
            apply wp
           apply (simp add: seL4_MessageInfo_lift_def message_info_to_H_def msgLengthBits_def)
           apply (vcg exspec=transferCaps_modifies)
          apply (wpsimp wp: hoare_case_option_wp)
         apply clarsimp
         apply (vcg exspec=copyMRs_modifies)
        apply (wpsimp wp: lookupExtraCaps_length)
       apply (clarsimp simp: guard_is_UNIV_def Collect_const_mem)
       apply (clarsimp simp: seL4_MessageInfo_lift_def message_info_to_H_def mask_def
                             msgLengthBits_def word_bw_assocs)
      apply (wp getMessageInfo_le3 getMessageInfo_msgLength[unfolded K_def] hoare_weak_lift_imp
                  | simp)+
     apply (auto simp: excaps_in_mem_def valid_ipc_buffer_ptr'_def
                       option_to_0_def option_to_ptr_def
                       seL4_MessageInfo_lift_def mi_from_H_def message_info_to_H_def
                split: option.split)
    done
qed

lemma lookupIPCBuffer_not_Some_0:
  "\<lbrace>\<top>\<rbrace> lookupIPCBuffer r t \<lbrace>\<lambda>rv. K (rv \<noteq> Some 0)\<rbrace>"
  apply (simp add: lookupIPCBuffer_def RISCV64_H.lookupIPCBuffer_def)
  apply (wp hoare_TrueI haskell_assert_wp
    | simp add: Let_def getThreadBufferSlot_def locateSlotTCB_def
    | intro conjI impI | wpc)+
  done

lemma pageBitsForSize_3 [simp]:
  "3 \<le> pageBitsForSize sz"
  by (cases sz, auto simp: bit_simps)

lemma pbfs_msg_align_bits [simp]:
  "msg_align_bits \<le> pageBitsForSize sz"
  by (cases sz, auto simp: msg_align_bits bit_simps)

lemma lookupIPCBuffer_aligned:
  "\<lbrace>valid_objs'\<rbrace> lookupIPCBuffer r t \<lbrace>\<lambda>rv. K (case_option True (\<lambda>x. is_aligned x msg_align_bits) rv)\<rbrace>"
  apply (simp add: lookupIPCBuffer_def RISCV64_H.lookupIPCBuffer_def
                   getThreadBufferSlot_def locateSlot_conv
                   Let_def getSlotCap_def cong: if_cong)
  apply (rule hoare_pre)
  apply (wp getCTE_wp' threadGet_wp | wpc)+
  apply (clarsimp simp: obj_at_simps)
  apply (drule (1) ctes_of_valid)
  apply (prop_tac "valid_tcb' tcb s")
   apply (fastforce intro: tcb_ko_at_valid_objs_valid_tcb' simp: obj_at_simps)
  apply (clarsimp simp: isCap_simps valid_cap'_def capAligned_def valid_obj'_def valid_tcb'_def)
  apply (auto elim: aligned_add_aligned intro: is_aligned_andI1)
  done


lemma isArchPageCap_def2:
  "\<And>cap. isArchFrameCap cap = (isArchObjectCap cap \<and> isFrameCap (capCap cap))"
  by (fastforce simp: isCap_simps)


lemma replyFromKernel_error_ccorres [corres]:
  "ccorres dc xfdc (valid_pspace' and tcb_at' thread)
     (UNIV \<inter> \<lbrace>syscall_error_to_H \<acute>current_syscall_error
                          (lookup_fault_lift \<acute>current_lookup_fault)
                       = Some err\<rbrace>
           \<inter> \<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr thread\<rbrace>) hs
     (replyFromKernel thread (msgFromSyscallError err))
     (Call replyFromKernel_error_'proc)"
  apply (cinit lift: thread_')
   apply clarsimp
   apply wpc
   apply (ctac add: lookupIPCBuffer_ccorres)
     apply simp
     apply ctac
       apply (ctac add: setMRs_syscall_error_ccorres[where err=err])
         apply ((rule ccorres_Guard_Seq)+)?
         apply csymbr
         apply (rule ccorres_abstract_cleanup)
         apply (rule setMessageInfo_ccorres)
        apply wp
       apply (simp add: Collect_const_mem)
       apply (vcg exspec=setMRs_syscall_error_modifies)
      apply (wp hoare_case_option_wp)
     apply (vcg exspec=setRegister_modifies)
    apply simp
    apply (wp lookupIPCBuffer_aligned_option_to_0)
   apply (simp del: Collect_const)
   apply (vcg exspec=lookupIPCBuffer_modifies)
  apply (simp add: msgInfoRegister_def
                   Kernel_C.msgInfoRegister_def C_register_defs
                   RISCV64_H.badgeRegister_def RISCV64.badgeRegister_def
                   Kernel_C.badgeRegister_def RISCV64.capRegister_def
                   message_info_to_H_def valid_pspace_valid_objs')
  apply (clarsimp simp: msgLengthBits_def msgFromSyscallError_def
                        syscall_error_to_H_def syscall_error_type_defs
                        mask_def option_to_ptr_def
                 split: if_split_asm)
  done

lemma fault_to_fault_tag_nonzero:
  "fault_to_fault_tag f \<noteq> 0"
  apply (case_tac f; simp add: seL4_Fault_tag_defs)
  apply (rename_tac af)
  apply (case_tac af; simp add: seL4_Fault_tag_defs)
  done

lemma doIPCTransfer_ccorres[corres]:
  "ccorres dc xfdc
    (valid_pspace' and tcb_at' sender and tcb_at' receiver
     and K (receiver \<noteq> sender \<and> endpoint \<noteq> Some 0))
    (\<lbrace>\<acute>sender = tcb_ptr_to_ctcb_ptr sender\<rbrace>
     \<inter> \<lbrace>\<acute>receiver = tcb_ptr_to_ctcb_ptr receiver\<rbrace>
     \<inter> \<lbrace>canGrant = to_bool \<acute>grant\<rbrace>
     \<inter> \<lbrace>\<acute>badge___unsigned_long = badge\<rbrace>
     \<inter> \<lbrace>\<acute>endpoint = option_to_ptr endpoint\<rbrace>)  []
    (doIPCTransfer sender endpoint badge canGrant receiver)
    (Call doIPCTransfer_'proc)"
  apply (cinit lift: sender_' receiver_' grant_' badge___unsigned_long_' endpoint_')
   apply (rule_tac xf'="ret__ptr_to_unsigned_long_'"
                in ccorres_split_nothrow_call_novcg)
         apply (rule lookupIPCBuffer_ccorres)
        apply simp_all[3]
     apply ceqv
    apply csymbr
    apply (rule ccorres_pre_threadGet)
    apply (rename_tac fault)
    apply (rule ccorres_move_c_guard_tcb)
    apply (rule_tac val="case_option (scast seL4_Fault_NullFault) fault_to_fault_tag fault"
                and xf'=ret__unsigned_longlong_'
                and R="\<lambda>s. \<exists>t. ko_at' t sender s \<and> tcbFault t = fault"
                 in ccorres_symb_exec_r_known_rv_UNIV [where R'=UNIV])
       apply (vcg, clarsimp)
       apply (erule(1) cmap_relation_ko_atE [OF cmap_relation_tcb])
       apply (fastforce simp: ctcb_relation_def typ_heap_simps
                             cfault_rel_def seL4_Fault_lift_def Let_def
                      split: if_split_asm option.split)
      apply ceqv
     apply wpc
      apply (clarsimp simp: seL4_Fault_NullFault_def ccorres_cond_univ_iff)
      apply (rule ccorres_rhs_assoc)
      apply (rule_tac xf'="ret__ptr_to_unsigned_long_'"
                   in ccorres_split_nothrow_call_novcg)
            apply (rule lookupIPCBuffer_ccorres)
           apply simp_all[3]
        apply ceqv
       apply csymbr
       apply ctac
      apply (wp lookupIPCBuffer_not_Some_0 lookupIPCBuffer_aligned)
     apply (clarsimp simp: seL4_Fault_NullFault_def ccorres_cond_iffs
                           fault_to_fault_tag_nonzero)
     apply ctac
    apply (clarsimp simp: guard_is_UNIV_def option_to_ptr_def split: option.splits)
   apply (rule_tac Q'="\<lambda>rv. valid_pspace' and tcb_at' sender
                            and tcb_at' receiver and K (rv \<noteq> Some 0)
                            and (case_option \<top> valid_ipc_buffer_ptr' rv)
                            and K (receiver \<noteq> sender \<and> endpoint \<noteq> Some 0)"
                in hoare_post_imp)
    apply (auto simp: valid_ipc_buffer_ptr'_def option_to_0_def
                   split: option.splits)[1]
   apply (wp lookupIPCBuffer_not_Some_0 lookupIPCBuffer_aligned)
  apply auto
  done

lemma fault_case_absorb_bind:
  "(do x \<leftarrow> f; case_fault (p x) (q x) (r x) (s x) (t x) ft od)
    = case_fault (\<lambda>a b. f >>= (\<lambda>x. p x a b)) (\<lambda>a b c. f >>= (\<lambda>x. q x a b c))
          (\<lambda>a. f >>= (\<lambda>x. r x a)) (\<lambda>a. f >>= (\<lambda>x. s x a)) (\<lambda>a. f >>= (\<lambda>x. t x a)) ft"
  by (simp split: fault.split)

lemma length_exceptionMessage:
  "length RISCV64_H.exceptionMessage = unat n_exceptionMessage"
  by (simp add: RISCV64_H.exceptionMessage_def RISCV64.exceptionMessage_def n_exceptionMessage_def)

lemma Arch_getSanitiseRegisterInfo_ccorres:
  "ccorres ((=) \<circ> from_bool) ret__unsigned_long_'
     (tcb_at' r and no_0_obj' and valid_objs')
     (UNIV \<inter> {s. thread_' s = tcb_ptr_to_ctcb_ptr r}) hs
     (getSanitiseRegisterInfo r)
     (Call Arch_getSanitiseRegisterInfo_'proc)"
  apply (cinit' lift: thread_' simp: getSanitiseRegisterInfo_def)
   apply (rule ccorres_return_C, simp+)
  done

lemma copyMRsFaultReply_ccorres_exception:
  "ccorres dc xfdc
           (valid_pspace' and tcb_at' s and tcb_at' r
                          and obj_at' (\<lambda>t. tcbFault t = Some f) r
                          and K (r \<noteq> s)
                          and K (len \<le> unat n_exceptionMessage))
           (UNIV \<inter> \<lbrace>\<acute>sender = tcb_ptr_to_ctcb_ptr s\<rbrace>
                 \<inter> \<lbrace>\<acute>receiver = tcb_ptr_to_ctcb_ptr r\<rbrace>
                 \<inter> \<lbrace>\<acute>id___anonymous_enum = MessageID_Exception \<rbrace>
                 \<inter> \<lbrace>\<acute>length___unsigned_long = of_nat len \<rbrace>) hs
           (do t \<leftarrow> getSanitiseRegisterInfo r;
               zipWithM_x (\<lambda>rs rd. do v \<leftarrow> asUser s (getRegister rs);
                                        asUser r (setRegister rd (RISCV64_H.sanitiseRegister t rd v))
                                        od)
               RISCV64_H.msgRegisters (take len RISCV64_H.exceptionMessage)
            od)
           (Call copyMRsFaultReply_'proc)"
proof -
  show ?thesis
    apply (unfold K_def, rule ccorres_gen_asm) using [[goals_limit=1]]
    apply (cinit' lift: sender_' receiver_'
                        id___anonymous_enum_'
                        length___unsigned_long_'
                  simp: whileAnno_def)
     apply (ctac(no_vcg) add: Arch_getSanitiseRegisterInfo_ccorres)
     apply (rule ccorres_rhs_assoc2)
     apply (simp add: MessageID_Exception_def)
     apply ccorres_rewrite
     apply (rule ccorres_add_return2)
     apply (rule ccorres_split_nothrow_novcg)
         apply (rule ccorres_zipWithM_x_while)
             apply clarsimp
             apply (intro ccorres_rhs_assoc)
             apply (rule ccorres_symb_exec_r)
               apply ctac
                 apply (rule ccorres_symb_exec_r)
                   apply ctac
                  apply (vcg)
                 apply clarsimp
                 apply (rule conseqPre, vcg)
                 apply (auto simp: sanitiseRegister_def)[1]
                apply wp
               apply clarsimp
               apply vcg
              apply clarsimp
              apply vcg
              apply (rule conjI, simp add: RISCV64_H.exceptionMessage_def
                                           RISCV64.exceptionMessage_def word_of_nat_less)
              apply (simp add: msgRegisters_ccorres n_msgRegisters_def length_msgRegisters
                               RISCV64_H.exceptionMessage_def RISCV64.exceptionMessage_def
                               unat_of_nat exceptionMessage_ccorres[symmetric,simplified MessageID_Exception_def,simplified]
                               n_exceptionMessage_def length_exceptionMessage sanitiseRegister_def Let_def)
               apply (auto simp add: word_less_nat_alt unat_of_nat)[1]
             apply (rule conseqPre, vcg)
             apply (clarsimp simp: word_of_nat_less RISCV64_H.exceptionMessage_def
                                   RISCV64.exceptionMessage_def)
            apply (simp add: min_def length_msgRegisters)
            apply (clarsimp simp: min_def n_exceptionMessage_def
                                  RISCV64_H.exceptionMessage_def
                                  RISCV64.exceptionMessage_def
                                  length_msgRegisters n_msgRegisters_def
                                  message_info_to_H_def word_of_nat_less
                           split: if_split)
            apply (fastforce dest!: le_antisym)
           apply clarsimp
           apply (vcg spec=TrueI)
           apply clarsimp
          apply wp
            apply simp+
         apply (clarsimp simp: RISCV64_H.exceptionMessage_def
                               RISCV64.exceptionMessage_def
                               word_bits_def)
         apply unat_arith
        apply ceqv
       apply (simp add: length_exceptionMessage
                        length_msgRegisters
                        n_exceptionMessage_def
                        msgMaxLength_def
                        n_msgRegisters_def
                        of_nat_less_iff)
       apply ccorres_rewrite
       apply (rule ccorres_return_Skip)
      apply (wp mapM_wp')
     apply clarsimp+
     apply (clarsimp simp: guard_is_UNIV_def message_info_to_H_def
                           Collect_const_mem
                    split: if_split)
   apply wp
  apply (auto)
  done
qed

lemma valid_drop_case: "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. P' rv s\<rbrace> \<rbrakk>
                       \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. case rv of None \<Rightarrow> True | Some x \<Rightarrow> P' rv s\<rbrace>"
   apply (simp only: valid_def Ball_def split: prod.split)
     apply (rule allI impI)+
     apply (case_tac x1)
     apply simp+
  done

lemma copyMRsFaultReply_ccorres_syscall:
  fixes word_size :: "'a::len"
  shows "ccorres dc xfdc
           (valid_pspace' and tcb_at' s
                          and tcb_at' r
                          and obj_at' (\<lambda>t. tcbFault t = Some f) r
                          and K (r \<noteq> s)
                          and K (len \<le> unat n_syscallMessage))
           (UNIV \<inter> \<lbrace>\<acute>sender = tcb_ptr_to_ctcb_ptr s\<rbrace>
                 \<inter> \<lbrace>\<acute>receiver = tcb_ptr_to_ctcb_ptr r\<rbrace>
                 \<inter> \<lbrace>\<acute>id___anonymous_enum = MessageID_Syscall \<rbrace>
                 \<inter> \<lbrace>\<acute>length___unsigned_long = of_nat len \<rbrace>) hs
           (do t \<leftarrow> getSanitiseRegisterInfo r;
               a \<leftarrow> zipWithM_x (\<lambda>rs rd. do v \<leftarrow> asUser s (getRegister rs);
                                           asUser r (setRegister rd (RISCV64_H.sanitiseRegister t rd v))
                                        od)
               RISCV64_H.msgRegisters (take len RISCV64_H.syscallMessage);
               sendBuf \<leftarrow> lookupIPCBuffer False s;
               case sendBuf of None \<Rightarrow> return ()
                            | Some bufferPtr \<Rightarrow>
                                   zipWithM_x (\<lambda>i rd. do v \<leftarrow> loadWordUser (bufferPtr + i * 8);
                                                         asUser r (setRegister rd (RISCV64_H.sanitiseRegister t rd v))
                                                      od)
                                      [scast n_msgRegisters + 1.e.scast n_syscallMessage]
                                      (drop (unat (scast n_msgRegisters :: machine_word))
                                            (take len RISCV64_H.syscallMessage))
                                 od)
           (Call copyMRsFaultReply_'proc)"
  proof -
  let ?obj_at_ft = "obj_at' (\<lambda>tcb. tcbFault tcb = Some f) s"
  note symb_exec_r_fault = ccorres_symb_exec_r_known_rv_UNIV
          [where xf'=ret__unsigned_' and R="?obj_at_ft" and R'=UNIV]
  note empty_fail_cond[simp]
  show ?thesis
    apply (unfold K_def, rule ccorres_gen_asm) using [[goals_limit=1]]
    apply (cinit' lift: sender_' receiver_'
                        id___anonymous_enum_'
                        length___unsigned_long_'
                  simp: whileAnno_def)
     apply (ctac(no_vcg) add: Arch_getSanitiseRegisterInfo_ccorres)
     apply (rule ccorres_rhs_assoc2)
     apply (simp add: MessageID_Syscall_def)
     apply ccorres_rewrite
     apply (rule ccorres_split_nothrow_novcg)
         apply (rule ccorres_zipWithM_x_while)
             apply clarsimp
             apply (intro ccorres_rhs_assoc)
             apply (rule ccorres_symb_exec_r)
               apply ctac
                 apply (rule ccorres_symb_exec_r)
                   apply ctac
                  apply (vcg)
                 apply (rule conseqPre, vcg)
                 apply fastforce
                apply wp
               apply vcg
              apply vcg
              apply (rule conjI, simp add: RISCV64_H.syscallMessage_def
                                           RISCV64.syscallMessage_def word_of_nat_less
                                           unat_of_nat msgRegisters_ccorres n_msgRegisters_def
                                           length_msgRegisters)
              apply (simp add: msgRegisters_ccorres n_msgRegisters_def length_msgRegisters unat_of_nat
                               syscallMessage_ccorres[symmetric,simplified MessageID_Syscall_def,simplified]
                               n_syscallMessage_def length_syscallMessage sanitiseRegister_def)
              apply (auto simp add: word_less_nat_alt unat_of_nat)[1]
             apply (rule conseqPre, vcg)
             apply (clarsimp simp: word_of_nat_less syscallMessage_unfold length_msgRegisters
                                   n_syscallMessage_def n_msgRegisters_def)
            apply (simp add: min_def length_msgRegisters)
            apply (clarsimp simp:   min_def n_syscallMessage_def
                                    length_msgRegisters n_msgRegisters_def
                                    length_syscallMessage
                                    message_info_to_H_def word_of_nat_less
                             split: if_split)
            apply (simp add: word_less_nat_alt unat_of_nat not_le)
           apply clarsimp
           apply (vcg spec=TrueI)
           apply clarsimp
          apply wp
            apply simp+
         apply (clarsimp simp: length_syscallMessage
                               length_msgRegisters
                               n_msgRegisters_def n_syscallMessage_def
                               word_bits_def min_def
                         split: if_split)
        apply ceqv
       apply (rule_tac P'="if 4 < len then _ else _" in ccorres_inst)
       apply (cases "4 < len" ; simp)
        apply (clarsimp simp: unat_ucast_less_no_overflow n_syscallMessage_def
                              length_syscallMessage msgRegisters_unfold
                              word_of_nat_less unat_of_nat unat_less_helper)
        apply ccorres_rewrite
        apply (ctac(no_vcg))
         apply (rename_tac sb sb')
         apply wpc
          apply (simp add: option_to_0_def ccorres_cond_iffs option_to_ptr_def)
          apply (rule ccorres_return_Skip')
            apply (rule_tac P="sb \<noteq> Some 0" in ccorres_gen_asm)
            apply (rule_tac P="case_option True (\<lambda>x. is_aligned x msg_align_bits) sb"
                            in ccorres_gen_asm)
            apply (simp add: option_to_0_def option_to_ptr_def)
            apply (subgoal_tac "sb'\<noteq> NULL") prefer 2
             apply clarsimp
            apply (simp add: ccorres_cond_iffs)
            apply (subst ccorres_seq_skip' [symmetric])
            apply (rule_tac r'="\<lambda>rv rv'. rv' = of_nat (unat  n_msgRegisters) + _" in ccorres_rel_imp)
             apply (drule_tac s="sb" in sym)
             apply (simp only: zipWithM_x_mapM_x)
             apply ccorres_rewrite
             apply (rule_tac F="\<lambda>_. valid_pspace'
                                     and (case sb of None \<Rightarrow> \<top>
                                                   | Some x \<Rightarrow> valid_ipc_buffer_ptr' x)
                                     and tcb_at' r"
                             in ccorres_mapM_x_while')
                 apply clarsimp
                 apply (rule ccorres_guard_imp2)
                  apply (rule ccorres_pre_loadWordUser)
                  apply (intro ccorres_rhs_assoc)
                  apply (rule ccorres_symb_exec_r)
                    apply (rule ccorres_move_array_assertion_ipc_buffer
                                ccorres_Guard_Seq[where S="{s. h_t_valid (htd s) c_guard (ptr s)}" for ptr htd])+
                    apply (rule ccorres_symb_exec_r)
                      apply (rule ccorres_symb_exec_r)
                        apply ctac
                       apply (vcg)
                      apply (rule conseqPre, vcg)
                      apply fastforce
                     apply vcg
                    apply (rule conseqPre, vcg)
                    apply clarsimp
                   apply vcg
                  apply (rule conseqPre, vcg)
                  apply clarsimp
                 apply clarsimp
                 apply (subst aligned_add_aligned, assumption)
                   apply (rule is_aligned_mult_triv2[where n=3, simplified])
                  apply (simp add: msg_align_bits)
                 apply (simp only: n_msgRegisters_def)
                 apply (clarsimp simp: n_syscallMessage_def n_msgRegisters_def
                                       word_unat.Rep_inverse[of "scast _ :: 'a word"]
                                       msgRegisters_ccorres[symmetric]
                                       length_msgRegisters[symmetric]
                                       syscallMessage_ccorres[symmetric]
                                       length_msgRegisters length_syscallMessage
                                       syscallMessage_ccorres[symmetric, simplified MessageID_Syscall_def, simplified]
                                       unat_of_nat64 word_bits_def
                                       MessageID_Syscall_def
                                       min_def message_info_to_H_def
                                       upto_enum_def typ_heap_simps'
                                       unat_add_lem[THEN iffD1] Let_def
                                       msg_align_bits sanitiseRegister_def
                             simp del: upt_rec_numeral cong: if_cong register.case_cong,
                        simp_all add: word_less_nat_alt unat_add_lem[THEN iffD1] unat_of_nat)[1]
                apply (clarsimp simp: n_syscallMessage_def n_msgRegisters_def
                                      msgRegisters_ccorres
                                      syscallMessage_ccorres
                                      length_syscallMessage length_msgRegisters
                                      message_info_to_H_def min_def
                               split: if_split)
                apply (fastforce dest!: le_antisym)
               apply (vcg spec=TrueI)
               apply clarsimp
              apply (simp add: split_def)
              apply (wp hoare_case_option_wp)
              apply (fastforce elim: aligned_add_aligned
                               intro: is_aligned_mult_triv2 [where n=3,simplified]
                               simp: word_bits_def msg_align_bits)
             apply (clarsimp simp: msgRegisters_unfold
                                   n_msgRegisters_def
                                   word_bits_def not_less)
             apply (simp add: n_syscallMessage_def)
            apply simp
        apply (subst option.split[symmetric,where P=id, simplified])
        apply (rule valid_drop_case)
        apply (wp hoare_drop_imps hoare_vcg_all_lift lookupIPCBuffer_aligned[simplified]
                  lookupIPCBuffer_not_Some_0[simplified])
       apply (simp add: length_syscallMessage
                        length_msgRegisters
                        n_syscallMessage_def
                        msgMaxLength_def
                        n_msgRegisters_def
                        of_nat_less_iff)
       apply (rule_tac P'="{s. i_' s = of_nat len}" in ccorres_inst)
       apply ccorres_rewrite
       apply (rule ccorres_guard_imp)
         apply (rule ccorres_symb_exec_l)
            apply (case_tac rva ; clarsimp)
             apply (rule ccorres_return_Skip)+
                apply (wp mapM_x_wp_inv user_getreg_inv'
                       | clarsimp simp: zipWithM_x_mapM_x split: prod.split)+
     apply (cases  "4 < len")
      apply ((fastforce simp: guard_is_UNIV_def
                            msgRegisters_unfold
                            syscallMessage_unfold
                            n_syscallMessage_def
                            n_msgRegisters_def
                       intro: obj_tcb_at')+)[2]
    apply wp
   apply auto
  done
qed

lemma copyMRsFaultReply_ccorres_timeout:
  fixes word_size :: "'a::len"
  shows
  "ccorres dc xfdc
     (valid_pspace' and tcb_at' s and tcb_at' r and obj_at' (\<lambda>t. tcbFault t = Some f) r
      and K (r \<noteq> s) and K (len \<le> unat n_timeoutMessage))
     (\<lbrace>\<acute>sender = tcb_ptr_to_ctcb_ptr s\<rbrace>
      \<inter> \<lbrace>\<acute>receiver = tcb_ptr_to_ctcb_ptr r\<rbrace>
      \<inter> \<lbrace>\<acute>id___anonymous_enum = MessageID_TimeoutReply \<rbrace>
      \<inter> \<lbrace>\<acute>length___unsigned_long = of_nat len \<rbrace>) hs
     (do t \<leftarrow> getSanitiseRegisterInfo r;
         a \<leftarrow> zipWithM_x (\<lambda>rs rd. do v \<leftarrow> asUser s (getRegister rs);
                                    asUser r (setRegister rd (RISCV64_H.sanitiseRegister t rd v))
                                  od)
         RISCV64_H.msgRegisters (take len RISCV64_H.timeoutMessage);
         sendBuf \<leftarrow> lookupIPCBuffer False s;
         case sendBuf of
           None \<Rightarrow> return ()
         | Some bufferPtr \<Rightarrow> zipWithM_x (\<lambda>i rd. do v \<leftarrow> loadWordUser (bufferPtr + i * 8);
                                                   asUser r (setRegister rd (RISCV64_H.sanitiseRegister t rd v))
                                                od)
                                        [scast n_msgRegisters + 1.e.scast n_timeoutMessage]
                                        (drop (unat (scast n_msgRegisters :: machine_word))
                                              (take len RISCV64_H.timeoutMessage))
      od)
     (Call copyMRsFaultReply_'proc)"
proof -
  let ?obj_at_ft = "obj_at' (\<lambda>tcb. tcbFault tcb = Some f) s"
  note symb_exec_r_fault = ccorres_symb_exec_r_known_rv_UNIV
          [where xf'=ret__unsigned_' and R="?obj_at_ft" and R'=UNIV]
  note empty_fail_cond[simp]
  show ?thesis
    apply (unfold K_def, rule ccorres_gen_asm) using [[goals_limit=1]]
    apply (cinit' lift: sender_' receiver_'
                        id___anonymous_enum_'
                        length___unsigned_long_'
                  simp: whileAnno_def)
     apply (ctac(no_vcg) add: Arch_getSanitiseRegisterInfo_ccorres)
     apply (rule ccorres_rhs_assoc2)
     apply (simp add: MessageID_TimeoutReply_def)
     apply ccorres_rewrite
     apply (rule ccorres_split_nothrow_novcg)
         apply (rule ccorres_zipWithM_x_while)
             apply clarsimp
             apply (intro ccorres_rhs_assoc)
             apply (rule ccorres_symb_exec_r)
               apply ctac
                 apply (rule ccorres_symb_exec_r)
                   apply ctac
                  apply (vcg)
                 apply (rule conseqPre, vcg)
                 apply fastforce
                apply wp
               apply vcg
              apply vcg
              apply (rule conjI, simp add: RISCV64_H.timeoutMessage_def
                                           RISCV64.timeoutMessage_def word_of_nat_less
                                           unat_of_nat msgRegisters_ccorres n_msgRegisters_def
                                           length_msgRegisters)
              apply (simp add: msgRegisters_ccorres n_msgRegisters_def length_msgRegisters unat_of_nat
                               timeoutMessage_ccorres[symmetric,simplified MessageID_TimeoutReply_def,simplified]
                               n_syscallMessage_def length_syscallMessage sanitiseRegister_def)
              apply (auto simp add: word_less_nat_alt unat_of_nat)[1]
             apply (rule conseqPre, vcg)
             apply (clarsimp simp: word_of_nat_less syscallMessage_unfold length_msgRegisters
                                   n_syscallMessage_def n_msgRegisters_def)
            apply (simp add: min_def length_msgRegisters)
            apply (clarsimp simp:   min_def n_timeoutMessage_def
                                    length_msgRegisters n_msgRegisters_def
                                    length_timeoutMessage
                                    message_info_to_H_def word_of_nat_less
                             split: if_split)
            apply (simp add: word_less_nat_alt unat_of_nat not_le)
           apply clarsimp
           apply (vcg spec=TrueI)
           apply clarsimp
          apply wp
            apply simp+
         apply (clarsimp simp: length_timeoutMessage
                               length_msgRegisters
                               n_msgRegisters_def n_timeoutMessage_def
                               word_bits_def min_def
                         split: if_split)
        apply ceqv
       apply (rule_tac P'="if 4 < len then _ else _" in ccorres_inst)
       apply (cases "4 < len" ; simp)
        apply (clarsimp simp: unat_ucast_less_no_overflow n_timeoutMessage_def
                              length_timeoutMessage msgRegisters_unfold
                              word_of_nat_less unat_of_nat unat_less_helper)
        apply ccorres_rewrite
        apply (ctac(no_vcg))
         apply (rename_tac sb sb')
         apply wpc
          apply (simp add: option_to_0_def ccorres_cond_iffs option_to_ptr_def)
          apply (rule ccorres_return_Skip')
            apply (rule_tac P="sb \<noteq> Some 0" in ccorres_gen_asm)
            apply (rule_tac P="case_option True (\<lambda>x. is_aligned x msg_align_bits) sb"
                            in ccorres_gen_asm)
            apply (simp add: option_to_0_def option_to_ptr_def)
            apply (subgoal_tac "sb'\<noteq> NULL") prefer 2
             apply clarsimp
            apply (simp add: ccorres_cond_iffs)
            apply (subst ccorres_seq_skip' [symmetric])
            apply (rule_tac r'="\<lambda>rv rv'. rv' = of_nat (unat  n_msgRegisters) + _" in ccorres_rel_imp)
             apply (drule_tac s="sb" in sym)
             apply (simp only: zipWithM_x_mapM_x)
             apply ccorres_rewrite
             apply (rule_tac F="\<lambda>_. valid_pspace'
                                     and (case sb of None \<Rightarrow> \<top>
                                                   | Some x \<Rightarrow> valid_ipc_buffer_ptr' x)
                                     and tcb_at' r"
                             in ccorres_mapM_x_while')
                 apply clarsimp
                 apply (rule ccorres_guard_imp2)
                  apply (rule ccorres_pre_loadWordUser)
                  apply (intro ccorres_rhs_assoc)
                  apply (rule ccorres_symb_exec_r)
                    apply (rule ccorres_move_array_assertion_ipc_buffer
                                ccorres_Guard_Seq[where S="{s. h_t_valid (htd s) c_guard (ptr s)}" for ptr htd])+
                    apply (rule ccorres_symb_exec_r)
                      apply (rule ccorres_symb_exec_r)
                        apply ctac
                       apply (vcg)
                      apply (rule conseqPre, vcg)
                      apply fastforce
                     apply vcg
                    apply (rule conseqPre, vcg)
                    apply clarsimp
                   apply vcg
                  apply (rule conseqPre, vcg)
                  apply clarsimp
                 apply clarsimp
                 apply (subst aligned_add_aligned, assumption)
                   apply (rule is_aligned_mult_triv2[where n=3, simplified])
                  apply (simp add: msg_align_bits)
                 apply (simp only: n_msgRegisters_def)
                 apply (clarsimp simp: n_timeoutMessage_def n_msgRegisters_def
                                       word_unat.Rep_inverse[of "scast _ :: 'a word"]
                                       msgRegisters_ccorres[symmetric]
                                       length_msgRegisters[symmetric]
                                       timeoutMessage_ccorres[symmetric]
                                       length_msgRegisters length_timeoutMessage
                                       timeoutMessage_ccorres[symmetric,
                                                              simplified MessageID_TimeoutReply_def,
                                                              simplified]
                                       unat_of_nat64 word_bits_def
                                       MessageID_TimeoutReply_def
                                       min_def message_info_to_H_def
                                       upto_enum_def typ_heap_simps'
                                       unat_add_lem[THEN iffD1] Let_def
                                       msg_align_bits sanitiseRegister_def
                             simp del: upt_rec_numeral cong: if_cong register.case_cong,
                        simp_all add: word_less_nat_alt unat_add_lem[THEN iffD1] unat_of_nat)[1]
                apply (clarsimp simp: n_timeoutMessage_def n_msgRegisters_def
                                      msgRegisters_ccorres
                                      timeoutMessage_ccorres
                                      length_timeoutMessage length_msgRegisters
                                      message_info_to_H_def min_def
                               split: if_split)
                apply (fastforce dest!: le_antisym)
               apply (vcg spec=TrueI)
               apply clarsimp
              apply (simp add: split_def)
              apply (wp hoare_case_option_wp)
              apply (fastforce elim: aligned_add_aligned
                               intro: is_aligned_mult_triv2 [where n=3,simplified]
                               simp: word_bits_def msg_align_bits)
             apply (clarsimp simp: msgRegisters_unfold
                                   n_msgRegisters_def
                                   word_bits_def not_less)
             apply (simp add: n_syscallMessage_def)
            apply simp
        apply (subst option.split[symmetric,where P=id, simplified])
        apply (rule valid_drop_case)
        apply (wp hoare_drop_imps hoare_vcg_all_lift lookupIPCBuffer_aligned[simplified]
                  lookupIPCBuffer_not_Some_0[simplified])
       apply (simp add: length_timeoutMessage
                        length_msgRegisters
                        n_timeoutMessage_def
                        msgMaxLength_def
                        n_msgRegisters_def
                        of_nat_less_iff)
       apply (rule_tac P'="{s. i_' s = of_nat len}" in ccorres_inst)
       apply ccorres_rewrite
       apply (rule ccorres_guard_imp)
         apply (rule ccorres_symb_exec_l)
            apply (case_tac rva ; clarsimp)
             apply (rule ccorres_return_Skip)+
                apply (wp mapM_x_wp_inv user_getreg_inv'
                       | clarsimp simp: zipWithM_x_mapM_x split: prod.split)+
     apply (cases  "4 < len")
      apply ((fastforce simp: guard_is_UNIV_def
                            msgRegisters_unfold
                            timeoutMessage_unfold
                            n_msgRegisters_def
                       intro: obj_tcb_at')+)[2]
    apply wp
   apply auto
  done
qed

lemma handleArchFaultReply_corres:
  "ccorres (\<lambda>rv rv'. rv = to_bool rv') ret__unsigned_long_'
           (valid_pspace' and tcb_at' sender
                          and tcb_at' receiver
                          and K (f = ArchFault af)
                          and K (sender \<noteq> receiver))
           (UNIV \<inter> \<lbrace> \<acute>faultType = fault_to_fault_tag f \<rbrace>
           \<inter> \<lbrace>\<acute>sender = tcb_ptr_to_ctcb_ptr sender\<rbrace>
           \<inter> \<lbrace>\<acute>receiver = tcb_ptr_to_ctcb_ptr receiver\<rbrace>)
           hs
           (handleArchFaultReply' af sender receiver msg)
           (Call Arch_handleFaultReply_'proc)"
  apply (unfold K_def)
  apply (rule ccorres_gen_asm)+
  apply (cinit lift: faultType_' sender_' receiver_')
   apply (clarsimp simp: bind_assoc seL4_Fault_tag_defs ccorres_cond_iffs Let_def
                   split del: if_split)
   apply (wpc ; clarsimp simp: seL4_Fault_tag_defs ; ccorres_rewrite)
     (* VMFault *)
   apply (rule ccorres_symb_exec_l)
      apply (rule ccorres_stateAssert)
      apply wpc
       apply (clarsimp simp: ccorres_cond_iffs)
       apply (rule ccorres_return_C)
         apply simp+
      apply (rule ccorres_symb_exec_l)
         apply (ctac add: ccorres_return_C)
        apply (wp mapM_wp' empty_fail_loadWordUser | clarsimp)+
  done

(* MOVE *)
lemma monadic_rewrite_ccorres_assemble_nodrop:
  assumes cc: "ccorres_underlying sr G r xf ar axf (P and Q) P' hs f c"
  assumes mr: "monadic_rewrite True False Q g f"
  shows       "ccorres_underlying sr G r xf ar axf (P and Q) P' hs g c"
proof -
  have snd: "\<And>s. \<lbrakk> Q s; \<not> snd (g s) \<rbrakk> \<Longrightarrow> \<not> snd (f s)"
    using mr
    by (simp add: monadic_rewrite_def)

  have fst: "\<And>s v. \<lbrakk> Q s; \<not> snd (g s); v \<in> fst (f s) \<rbrakk> \<Longrightarrow> v \<in> fst (g s)"
    using mr
    by (auto simp add: monadic_rewrite_def)

  show ?thesis
    apply (rule ccorresI')
    apply (erule ccorresE[OF cc], (simp add: snd)+)
    apply clarsimp
    apply (rule rev_bexI[OF fst], assumption+)
    apply simp
    done
qed

lemma handleFaultReply_ccorres [corres]:
  "ccorres (\<lambda>rv rv'. rv = to_bool rv') ret__unsigned_long_'
           (valid_pspace' and obj_at' (\<lambda>t. tcbFault t = Some f) r
                          and (tcb_at' s and tcb_at' r)
                          and K (r \<noteq> s))
           (UNIV  \<inter> \<lbrace>cfault_rel (Some f)
                      (seL4_Fault_lift (h_val (hrs_mem \<acute>t_hrs)
                         (Ptr &(tcb_ptr_to_ctcb_ptr r\<rightarrow>[''tcbFault_C'']))))
                      (lookup_fault_lift (h_val (hrs_mem \<acute>t_hrs)
                         (Ptr &(tcb_ptr_to_ctcb_ptr r\<rightarrow>[''tcbLookupFailure_C'']))))\<rbrace>
                  \<inter> \<lbrace>\<acute>sender = tcb_ptr_to_ctcb_ptr s\<rbrace>
                  \<inter> \<lbrace>\<acute>receiver = tcb_ptr_to_ctcb_ptr r\<rbrace>) hs
           (do
              tag \<leftarrow> getMessageInfo s;
              sb \<leftarrow> lookupIPCBuffer False s;
              msg \<leftarrow> getMRs s sb tag;
              handleFaultReply f r (msgLabel tag) msg
            od) (Call handleFaultReply_'proc)"
  supply if_cong[cong] option.case_cong[cong]
  apply (unfold K_def, rule ccorres_gen_asm)
  apply (rule monadic_rewrite_ccorres_assemble_nodrop[OF _ handleFaultReply',rotated], simp)
  apply (cinit lift: sender_' receiver_' simp: whileAnno_def)
   apply clarsimp
   apply (ctac(c_lines 2) add: getMessageInfo_ccorres')
     apply (rename_tac tag tag')
     apply csymbr
     apply csymbr
     apply csymbr
     apply csymbr
     apply (rule ccorres_move_c_guard_tcb)
     apply (rule ccorres_symb_exec_r)
       apply (rule_tac val="fault_to_fault_tag f"
                   and xf'=ret__unsigned_longlong_'
                   and R="\<lambda>s. \<exists>t. ko_at' t r s \<and> tcbFault t = Some f"
                   and R'="\<lbrace>cfault_rel (Some f) (seL4_Fault_lift \<acute>fault)
                        (lookup_fault_lift (h_val (hrs_mem \<acute>t_hrs)
                           (Ptr &(tcb_ptr_to_ctcb_ptr r\<rightarrow>[''tcbLookupFailure_C'']))))\<rbrace>"
                    in ccorres_symb_exec_r_known_rv)
          apply (rule conseqPre, vcg, clarsimp)
          apply (erule(1) cmap_relation_ko_atE [OF cmap_relation_tcb])
          apply (clarsimp simp: ctcb_relation_def typ_heap_simps
                                cfault_rel_def seL4_Fault_lift_def Let_def
                         split: if_split_asm)
         apply ceqv
        apply (simp add: handleFaultReply_def fault_case_absorb_bind
                    del: Collect_const split del: if_split)
        apply wpc
           (* UserException *)
           apply (rename_tac number code)
           apply (clarsimp simp: bind_assoc seL4_Fault_tag_defs ccorres_cond_iffs
                           split del: if_split)
              apply (subst take_min_len[symmetric,where n="unat (msgLength _)"])
           apply (simp add: bind_assoc[symmetric])
              apply (ctac add: copyMRsFaultReply_ccorres_exception)
                apply (ctac add: ccorres_return_C)
               apply wp
              apply (vcg exspec=copyMRsFaultReply_modifies)
             apply (wpsimp wp: threadGet_wp)+
          (* CapFault *)
          apply (clarsimp simp: bind_assoc seL4_Fault_tag_defs ccorres_cond_iffs
                          split del: if_split)
          apply (ctac add: ccorres_return_C)
         (* UnknowSyscall *)
         apply (rename_tac number)
         apply (clarsimp simp: seL4_Fault_tag_defs ccorres_cond_iffs
                         split del: if_split)
            apply (subst take_min_len[symmetric,where n="unat (msgLength _)"])
            apply (subst take_min_len[symmetric,where n="unat (msgLength _)"])
            apply (fold bind_assoc)
            apply (ctac add: copyMRsFaultReply_ccorres_syscall[simplified bind_assoc[symmetric]])
              apply (ctac add: ccorres_return_C)
             apply wp
            apply (vcg exspec=copyMRsFaultReply_modifies)
           apply (wpsimp wp: threadGet_wp)+
         (* Timeout *)
         apply (clarsimp simp: seL4_Fault_tag_defs ccorres_cond_iffs
                         split del: if_split)
            apply (subst take_min_len[symmetric,where n="unat (msgLength _)"])
            apply (subst take_min_len[symmetric,where n="unat (msgLength _)"])
            apply (fold bind_assoc)
            apply (ctac add: copyMRsFaultReply_ccorres_timeout[simplified bind_assoc[symmetric]])
              apply (ctac add: ccorres_return_C)
             apply wp
            apply (vcg exspec=copyMRsFaultReply_modifies)
           apply (wpsimp wp: threadGet_wp)+
        (* ArchFault *)
        apply (rename_tac arch_fault)
        apply ccorres_rewrite
        apply (rule ccorres_rhs_assoc)
        (* apply (rule_tac P="\<lambda>s. \<exists>t. ko_at' t r s" in ccorres_cross_over_guard) *)
        apply (rule_tac val="fault_to_fault_tag f"
                   and xf'=ret__unsigned_longlong_'
                   and R="\<lambda>s. \<exists>t. ko_at' t r s \<and> tcbFault t = Some f"
                   and R'="\<lbrace>cfault_rel (Some f) (seL4_Fault_lift \<acute>fault)
                        (lookup_fault_lift (h_val (hrs_mem \<acute>t_hrs)
                           (Ptr &(tcb_ptr_to_ctcb_ptr r\<rightarrow>[''tcbLookupFailure_C'']))))\<rbrace>"
                    in ccorres_symb_exec_r_known_rv_UNIV)
           apply (rule conseqPre, vcg, clarsimp)
           apply (erule(1) cmap_relation_ko_atE [OF cmap_relation_tcb])
           apply (clarsimp simp: ctcb_relation_def typ_heap_simps
                                 cfault_rel_def seL4_Fault_lift_def Let_def
                           split: if_split_asm)
          apply ceqv
         apply (rule ccorres_add_return2)
         apply (ctac add: handleArchFaultReply_corres)
           apply (rule ccorres_return_C)
             apply simp+
          apply wp
         apply (vcg exspec=Arch_handleFaultReply_modifies)
        apply (clarsimp simp: guard_is_UNIV_def)
        apply (subst fault_to_fault_tag.simps(2))
        apply (clarsimp split: if_split)
        apply simp+
       (* Done *)
       apply clarsimp
       apply vcg
      apply vcg
     apply clarsimp
     apply vcg_step
     apply (clarsimp simp: n_exceptionMessage_def n_syscallMessage_def n_timeoutMessage_def
                           message_info_to_H_def to_bool_def scast_def
                           length_exceptionMessage length_syscallMessage length_timeoutMessage
                           min_def word_less_nat_alt
                           guard_is_UNIV_def seL4_Faults seL4_Arch_Faults
                       split: if_split)
    apply (simp add: length_exceptionMessage length_syscallMessage length_timeoutMessage)
    apply wp
   apply clarsimp
   apply (vcg exspec=getRegister_modifies)
  apply (clarsimp simp: n_exceptionMessage_def n_syscallMessage_def n_timeoutMessage_def
                        message_info_to_H_def length_exceptionMessage length_syscallMessage
                        length_timeoutMessage min_def word_less_nat_alt obj_at'_def
                 split: if_split)
  apply (fastforce simp: seL4_Faults seL4_Arch_Faults)
  done

context
notes if_cong[cong]
begin
crunch emptySlot, tcbSchedEnqueue, rescheduleRequired
  for tcbFault: "obj_at' (\<lambda>tcb. P (tcbFault tcb)) t"
  (wp: threadSet_obj_at'_strongish crunch_wps
    simp: crunch_simps unless_def)

crunch setThreadState, cancelAllIPC, cancelAllSignals
 for tcbFault: "obj_at' (\<lambda>tcb. P (tcbFault tcb)) t"
  (wp: threadSet_obj_at'_strongish crunch_wps simp: crunch_simps)
end

lemma sbn_tcbFault:
  "\<lbrace>obj_at' (\<lambda>tcb. P (tcbFault tcb)) t\<rbrace>
  setBoundNotification st t'
  \<lbrace>\<lambda>_. obj_at' (\<lambda>tcb. P (tcbFault tcb)) t\<rbrace>"
  apply (simp add: setBoundNotification_def)
  apply (wp threadSet_obj_at' | simp cong: if_cong)+
  done

crunch unbindNotification, unbindMaybeNotification
  for tcbFault: "obj_at' (\<lambda>tcb. P (tcbFault tcb)) t"
  (ignore: threadSet wp: sbn_tcbFault)

lemma transferCapsToSlots_local_slots:
  assumes weak: "\<And>c cap. P (maskedAsFull c cap) = P c"
  shows
  "\<lbrace> cte_wp_at' (\<lambda>cte. P (cteCap cte)) slot and K (slot \<notin> set destSlots) \<rbrace>
    transferCapsToSlots ep rcvBuffer x caps destSlots mi
   \<lbrace>\<lambda>tag'. cte_wp_at' (\<lambda>cte. P (cteCap cte)) slot\<rbrace>"
proof (rule hoare_gen_asm, induct caps arbitrary: x mi destSlots)
  case Nil show ?case by simp
next
  case (Cons cp cps)
  show ?case using Cons.prems
    apply (clarsimp simp: Let_def split del: if_split)
     apply (wp Cons.hyps cteInsert_weak_cte_wp_at2
         | wpc | simp add: weak whenE_def split del: if_split split: prod.splits)+
    done
qed

lemma transferCaps_local_slots:
  assumes weak: "\<And>c cap. P (maskedAsFull c cap) = P c"
  shows "\<lbrace> valid_objs' and (Not o real_cte_at' slot) and cte_wp_at' (\<lambda>cte. P (cteCap cte)) slot \<rbrace>
    transferCaps tag caps ep receiver receiveBuffer
   \<lbrace>\<lambda>tag'. cte_wp_at' (\<lambda>cte. P (cteCap cte)) slot\<rbrace>"
  apply (simp add: transferCaps_def pred_conj_def)
  apply (rule bind_wp_fwd)
   apply (rule hoare_vcg_conj_lift)
    apply (rule get_rs_real_cte_at')
   apply (rule get_recv_slot_inv')
  apply (rule hoare_pre)
   apply (wp transferCapsToSlots_local_slots weak | wpc)+
  apply clarsimp
  done

lemma doNormalTransfer_local_slots:
  assumes weak: "\<And>c cap. P (maskedAsFull c cap) = P c"
  shows "\<lbrace> valid_objs' and (Not o real_cte_at' slot)
        and cte_wp_at' (\<lambda>cte. P (cteCap cte)) slot \<rbrace>
    doNormalTransfer sender sendBuffer ep badge grant receiver receiveBuffer
   \<lbrace>\<lambda>rv. cte_wp_at' (\<lambda>cte. P (cteCap cte)) slot\<rbrace>"
  apply (simp add: doNormalTransfer_def)
  apply (wp transferCaps_local_slots weak copyMRs_typ_at'[where T=CTET, unfolded typ_at_cte]
    | simp)+
  done

lemma doIPCTransfer_local_slots:
  assumes weak: "\<And>c cap. P (maskedAsFull c cap) = P c"
  shows "\<lbrace> valid_objs' and (Not o real_cte_at' slot)
        and cte_wp_at' (\<lambda>cte. P (cteCap cte)) slot and tcb_at' sender\<rbrace>
    doIPCTransfer sender ep badge grant receiver
    \<lbrace> \<lambda>rv. cte_wp_at' (\<lambda>cte. P (cteCap cte)) slot \<rbrace>"
  apply (simp add: doIPCTransfer_def)
  apply (wp doNormalTransfer_local_slots weak threadGet_wp | wpc)+
  apply (fastforce simp: obj_at_simps)
  done

lemma doIPCTransfer_reply_or_replyslot:
  "\<lbrace> cte_wp_at' (\<lambda>cte. isReplyCap (cteCap cte)) slot
      or (valid_objs' and (Not o real_cte_at' slot)
          and  cte_wp_at' (\<lambda>cte. cteCap cte = capability.NullCap \<or> isReplyCap (cteCap cte)) slot)
     and tcb_at' sender\<rbrace>
    doIPCTransfer sender ep badge grant receiver
    \<lbrace> \<lambda>rv. cte_wp_at' (\<lambda>cte. cteCap cte = capability.NullCap \<or> isReplyCap (cteCap cte)) slot\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (case_tac "cte_wp_at' (\<lambda>cte. isReplyCap (cteCap cte)) slot s")
   apply (rule hoare_pre, rule hoare_strengthen_post,
        rule_tac P="isReplyCap" and ptr=slot in doIPCTransfer_non_null_cte_wp_at2')
      apply (clarsimp simp: isCap_simps)
     apply (clarsimp simp: isCap_simps)
    apply (clarsimp simp: cte_wp_at_ctes_of)
   apply simp
  apply (wp doIPCTransfer_local_slots)
   apply (clarsimp simp: maskedAsFull_def cap_get_tag_isCap isCap_simps
                  split: if_split)
  apply simp
  done

crunch handleFaultReply
  for ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"

lemma tcbReadyTime_ccorres:
  "ccorres (=) ret__unsigned_longlong_'
     (tcb_at' tcbPtr and valid_objs' and no_0_obj')
     \<lbrace>\<acute>tcb = tcb_ptr_to_ctcb_ptr tcbPtr\<rbrace> hs
     (gets_the (readTCBReadyTime tcbPtr)) (Call tcbReadyTime_'proc)"
  supply sched_context_C_size[simp del] refill_C_size[simp del]
  unfolding readTCBReadyTime_def readReadyTime_def gets_the_ohaskell_assert
            gets_the_obind threadGet_def[symmetric]
            getRefillHead_def[symmetric]
            Nondet_Reader_Option.gets_the_return return_bind fun_app_def scActive_def[symmetric]
  apply (ccorres_exec_l_pre ccorres_exec_l_pre: threadGet_sp scActive_sp)+
  apply (cinit' lift: tcb_')
   apply (rule ccorres_move_c_guard_tcb)
   apply (rule_tac xf'="\<lambda>s. h_val (hrs_mem (t_hrs_' (globals s))) (ret__ptr_to_struct_refill_C_' s)"
                in ccorres_split_nothrow_call)
          apply (rule refill_head_ccorres)
         apply fastforce
        apply (clarsimp simp: typ_heap_simps)
       apply fastforce
      apply ceqv
     apply (rule ccorres_Guard)
     apply (fastforce intro: ccorres_return_C)
    apply wpsimp
   apply vcg
  apply normalise_obj_at'
  apply (rename_tac scPtr sc)
  apply (frule (1) tcb_ko_at_valid_objs_valid_tcb')
  apply (rule context_conjI)
   apply (frule (1) obj_at_cslift_tcb)
   apply (clarsimp simp: typ_heap_simps ctcb_relation_def)
  apply (clarsimp simp: active_sc_at'_rewrite)
  apply (frule (1) obj_at_cslift_sc)
  apply normalise_obj_at'
  apply (frule (1) sc_ko_at_valid_objs_valid_sc')
  apply (frule rf_sr_refill_buffer_relation)
  apply (frule_tac n="scRefillHead sc" in h_t_valid_refill, fastforce+)
    apply (clarsimp simp: valid_sched_context'_def obj_at'_def)
   apply fastforce
  apply (clarsimp simp: typ_heap_simps csched_context_relation_def sc_ptr_to_crefill_ptr_def
                        h_val_field_from_bytes' crefill_relation_def)
  done

lemma time_after_ccorres:
  "ccorres (\<lambda>rv rv'. rv = to_bool rv') ret__unsigned_long_'
     (\<lambda>s. \<forall>tcbPtr. tcbPtrOpt = Some tcbPtr \<longrightarrow> (tcb_at' tcbPtr s \<and> valid_objs' s \<and> no_0_obj' s))
     (\<lbrace>\<acute>new_time = newTime\<rbrace> \<inter> \<lbrace>\<acute>tcb = option_to_ctcb_ptr tcbPtrOpt\<rbrace>) []
     (gets_the (compareVals newTime tcbPtrOpt readTCBReadyTime (\<le>))) (Call time_after_'proc)"
  (is "ccorres _ _ ?abs _ _ _ _")
  apply (cinit' lift: new_time_' tcb_' simp: compareVals_def gets_the_if_distrib option.case_eq_if)
   apply (subst if_swap)
   apply csymbr
   apply (rule ccorres_cond_seq)
   apply ccorres_rewrite
   apply (rule ccorres_cond_both'[where Q="?abs" and Q'=\<top>])
     apply (fastforce dest: tcb_at_not_NULL simp: option_to_ctcb_ptr_def split: option.splits)
    apply simp
    apply (rule ccorres_rhs_assoc)
    apply (ctac add: tcbReadyTime_ccorres)
      apply csymbr
      apply (rule ccorres_return_C; fastforce)
     apply wpsimp
    apply vcg
   apply (clarsimp simp: gets_the_ogets)
   apply (rule ccorres_return_C; fastforce)
  by (clarsimp simp: option_to_ctcb_ptr_def split: if_splits option.splits)

lemma compareVals_readTCBReadyTime_SomeTrueD:
  "compareVals new_time tcbPtrOpt readTCBReadyTime (\<le>) s = Some True
   \<Longrightarrow> \<exists>tcbPtr. tcbPtrOpt = Some tcbPtr \<and> tcb_at' tcbPtr s"
  unfolding compareVals_def readTCBReadyTime_def
  by (clarsimp dest!: threadRead_SomeD split: if_splits option.splits)

lemma no_ofail_readTCBReadyTime:
  "no_ofail
     (tcb_at' tcbPtr and active_sc_tcb_at' tcbPtr and valid_objs'
      and pspace_aligned' and pspace_distinct' and pspace_bounded')
     (readTCBReadyTime tcbPtr)"
  apply (clarsimp simp: readTCBReadyTime_def)
  apply (wpsimp wp: ovalid_threadRead)
  apply normalise_obj_at'
  apply (frule (1) tcb_ko_at_valid_objs_valid_tcb')
  apply (fastforce intro: pspace_alignedD' pspace_distinctD' pspace_boundedD'
                    simp: opt_pred_def opt_map_def active_sc_at'_def obj_at'_def
                          active_sc_tcb_at'_def
                   split: option.splits)
  done

lemma no_ofail_compareVals:
  "no_ofail (\<lambda>s. \<forall>ptr. ptrOpt = Some ptr \<longrightarrow> (\<exists>val. f ptr s = Some val)) (compareVals val ptrOpt f R)"
  by (clarsimp simp: compareVals_def no_ofail_def obind_def split: if_splits option.splits)

lemma find_time_after_ccorres:
  "ccorres (\<lambda>ptr ptr'. ptr' = option_to_ctcb_ptr ptr) ret__ptr_to_struct_tcb_C_'
     (\<lambda>s. ksReleaseQueue_asrt s \<and> valid_objs' s \<and> no_0_obj' s
          \<and> pspace_aligned' s \<and> pspace_distinct' s \<and> pspace_bounded' s
          \<and> (\<forall>tcbPtr. tcbPtrOpt = Some tcbPtr \<longrightarrow> (tcbInReleaseQueue |< tcbs_of' s) tcbPtr)
          \<and> (\<forall>tcbPtr. (tcbInReleaseQueue |< tcbs_of' s) tcbPtr
                      \<longrightarrow> (tcb_at' tcbPtr s \<and> active_sc_tcb_at' tcbPtr s)))
     (\<lbrace>\<acute>new_time = newTime\<rbrace> \<inter> \<lbrace>\<acute>tcb = option_to_ctcb_ptr tcbPtrOpt\<rbrace>) []
     (findInsertionPoint newTime tcbPtrOpt readTCBReadyTime (\<le>)) (Call find_time_after_'proc)"
  supply sched_context_C_size[simp del] refill_C_size[simp del]
  apply (cinit lift: new_time_' tcb_'
               simp: runReaderT_def whileAnno_def tcbInReleaseQueue_imp_active_sc_tcb_at'_asrt_def)
   apply (rule ccorres_symb_exec_r)
     apply (rule ccorres_add_return2)
     apply (rule ccorres_rhs_assoc2)
     apply (rule ccorres_split_nothrow_novcg)
         apply (rule_tac r=tcbPtrOpt
                     and rrel="\<lambda>ptr ptr'. ptr' = option_to_ctcb_ptr ptr"
                     and xf=after_'
                     and cond_xf=ret__unsigned_long_'
                     and G="\<lambda>r s. ksReleaseQueue_asrt s \<and> valid_objs' s \<and> no_0_obj' s
                                  \<and> pspace_aligned' s \<and> pspace_distinct' s \<and> pspace_bounded' s
                                  \<and> (\<forall>tcbPtr. (tcbInReleaseQueue |< tcbs_of' s) tcbPtr
                                               \<longrightarrow> (tcb_at' tcbPtr s \<and> active_sc_tcb_at' tcbPtr s))
                                  \<and> (\<forall>ptr. r = Some ptr \<longrightarrow> (tcbInReleaseQueue |< tcbs_of' s) ptr)"
                      in ccorres_While'[where P="\<lambda>w. w \<noteq> 0" and G'=UNIV])
              prefer 2
              apply (rule ccorres_guard_imp)
                apply (rule ccorres_rel_imp)
                 apply (fastforce intro: ccorres_call[where xf'="ret__unsigned_long_'",
                                                      OF time_after_ccorres])
                apply (clarsimp simp: to_bool_def)
               apply fastforce
              apply fastforce
             apply (rule stronger_ccorres_guard_imp)
               apply (rule ccorres_pre_getObject_tcb)
               apply (rule ccorres_Guard)
               apply (rule ccorres_return[where R=\<top>])
               apply vcg
               apply clarsimp
               apply (erule CollectD)
              apply fastforce
             apply (clarsimp simp: typ_heap_simps)
             apply (frule compareVals_readTCBReadyTime_SomeTrueD)
             apply (clarsimp simp: typ_heap_simps option_to_ctcb_ptr_def opt_pred_def opt_map_def
                                   obj_at'_def ctcb_relation_def
                            split: option.splits)
            apply (wpsimp wp: no_ofail_compareVals)
            apply (rule_tac m="readTCBReadyTime ptr" in no_ofailD)
             apply (rule no_ofail_readTCBReadyTime)
            apply fastforce
           apply (wpsimp wp: getTCB_wp)
           apply (frule compareVals_readTCBReadyTime_SomeTrueD)
           apply (clarsimp simp: ksReleaseQueue_asrt_def list_queue_relation_def)
           apply (fastforce dest!: heap_ls_next_in_list simp: opt_pred_def opt_map_def obj_at'_def
                            split: option.splits)
          apply (rule conseqPre, vcg)
          apply (fastforce dest: compareVals_readTCBReadyTime_SomeTrueD intro: tcb_at_h_t_valid
                           simp: option_to_ctcb_ptr_def obj_at'_def)
         apply (rule conseqPre, vcg)
         apply (clarsimp simp: option_to_ctcb_ptr_def)
         apply (case_tac r; clarsimp)
         apply (rename_tac tcbPtr)
         apply (drule_tac x=tcbPtr in spec)+
         apply normalise_obj_at'
         apply (rename_tac tcb)
         apply (frule (1) tcb_ko_at_valid_objs_valid_tcb')
         apply (prop_tac "tcbSchedContext tcb \<noteq> None")
          apply (clarsimp simp: obj_at'_def active_sc_tcb_at'_def opt_pred_def opt_map_def
                         split: option.splits)
         apply clarsimp
         apply (rename_tac scPtr)
         apply (prop_tac "sc_at' scPtr s")
          apply (clarsimp simp: valid_tcb'_def valid_bound_sc'_def obj_at'_def split: option.splits)
         apply normalise_obj_at'
         apply (rename_tac sc)
         apply (frule (1) obj_at_cslift_tcb)
         apply (frule (1) obj_at_cslift_sc)
         apply normalise_obj_at'
         apply (frule (1) sc_ko_at_valid_objs_valid_sc')
         apply (frule rf_sr_refill_buffer_relation)
         apply (frule_tac n="scRefillHead sc" and scPtr=scPtr in h_t_valid_refill; fastforce?)
          apply (clarsimp simp: valid_sched_context'_def obj_at'_def in_omonad
                                active_sc_tcb_at'_def)
         apply (rule conjI)
          apply (clarsimp simp: typ_heap_simps)
         apply (rule conjI)
          apply (clarsimp simp: typ_heap_simps ctcb_relation_def)
         apply (rule conjI)
          apply (rule disjI2)
          apply (rule_tac n="length (scRefills sc)" in array_assertion_shrink_right)
           apply (rule sc_at_array_assertion')
             apply fastforce
            apply (clarsimp simp: typ_heap_simps ctcb_relation_def)
            apply (metis ptr_val_def)
           apply (clarsimp simp: valid_sched_context'_def MIN_REFILLS_def)
          apply (clarsimp simp: valid_sched_context'_def typ_heap_simps csched_context_relation_def
                                ctcb_relation_def active_sc_tcb_at'_def opt_pred_def
                                opt_map_def obj_at'_def)
         apply (clarsimp simp: typ_heap_simps csched_context_relation_def ctcb_relation_def
                               sc_ptr_to_crefill_ptr_def)
         apply (metis ptr_val_def)
        apply ceqv
       apply (fastforce intro: ccorres_return_C)
      apply wpsimp
     apply (clarsimp simp: guard_is_UNIV_def)
    apply vcg
   apply (rule conseqPre, vcg)
   apply clarsimp
  apply clarsimp
  done

lemma setReleaseQueue_return_rewrite:
  "monadic_rewrite False True (\<lambda>s. ksReleaseQueue s = queue) (setReleaseQueue queue) (return ())"
  unfolding setReleaseQueue_def
  by (fastforce intro: monadic_rewrite_guard_imp monadic_rewrite_modify_noop)

lemma ccorres_pre_getReleaseQueue:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows
    "ccorres r xf
       (\<lambda>s. \<forall>rv. ksReleaseQueue s = rv \<longrightarrow> P rv s)
       {s'. \<forall>rv s. (s, s') \<in> rf_sr \<and> ksReleaseQueue s = rv \<and> P rv s
                    \<and> ctcb_queue_relation rv (ksReleaseQueue_' (globals s'))
                   \<longrightarrow> s' \<in> P' rv} hs
       (getReleaseQueue >>= (\<lambda>rv. f rv)) c"
  apply (ccorres_exec_l_pre ccorres_exec_l_pre: getReleaseQueue_sp)
  apply (fastforce intro: stronger_ccorres_guard_imp cc
                    dest: rf_sr_ctcb_queue_relation_release_queue)
  done

lemma tcbQueuePrepend_tcb_at'_head[wp]:
  "\<lbrace>tcb_at' t\<rbrace>
   tcbQueuePrepend queue t
   \<lbrace>\<lambda>rv s. \<forall>head. tcbQueueHead rv = Some head \<longrightarrow> tcb_at' head s\<rbrace>"
  unfolding tcbQueuePrepend_def
  by (wpsimp wp: getTCB_wp)

lemma tcbQueuePrepend_tcb_at'_end[wp]:
  "\<lbrace>tcb_at' t\<rbrace>
   tcbQueuePrepend queue t
   \<lbrace>\<lambda>rv s. \<forall>end. tcbQueueEnd rv = Some end \<longrightarrow> tcb_at' end s\<rbrace>"
  unfolding tcbQueuePrepend_def
  apply (wpsimp wp: getTCB_wp hoare_vcg_all_lift)
  apply (fastforce dest: list_queue_relation_tcb_queue_head_end_valid)
  done

lemma tcbQueuePrepend_tcbQueueHead_tcbQueueEnd[wp]:
  "\<lbrace>\<top>\<rbrace>
   tcbQueuePrepend queue t
   \<lbrace>\<lambda>rv s. (\<exists>y. tcbQueueHead rv = Some y) = (\<exists>y. tcbQueueEnd rv = Some y)\<rbrace>"
  unfolding tcbQueuePrepend_def
  apply wpsimp
  apply (fastforce simp: tcbQueueEmpty_def dest: he_ptrs_head_iff_he_ptrs_end)
  done

lemma tcbQueueAppend_tcb_at'_head[wp]:
  "\<lbrace>tcb_at' t\<rbrace>
   tcbQueueAppend queue t
   \<lbrace>\<lambda>rv s. \<forall>head. tcbQueueHead rv = Some head \<longrightarrow> tcb_at' head s\<rbrace>"
  unfolding tcbQueueAppend_def
  apply (wpsimp wp: hoare_vcg_all_lift getTCB_wp)
  apply (fastforce dest: list_queue_relation_tcb_queue_head_end_valid)
  done

lemma tcbQueueAppend_tcb_at'_end[wp]:
  "\<lbrace>tcb_at' t\<rbrace>
   tcbQueueAppend queue t
   \<lbrace>\<lambda>rv s. \<forall>end. tcbQueueEnd rv = Some end \<longrightarrow> tcb_at' end s\<rbrace>"
  unfolding tcbQueueAppend_def
  by (wpsimp wp: hoare_vcg_all_lift getTCB_wp)

lemma tcbQueueAppend_tcbQueueHead_tcbQueueEnd[wp]:
  "\<lbrace>\<top>\<rbrace>
   tcbQueueAppend queue t
   \<lbrace>\<lambda>rv s. (\<exists>y. tcbQueueHead rv = Some y) = (\<exists>y. tcbQueueEnd rv = Some y)\<rbrace>"
  unfolding tcbQueueAppend_def
  apply (wpsimp wp: getTCB_wp hoare_vcg_all_lift)
  apply (clarsimp simp: tcbQueueEmpty_def)
  done

crunch orderedInsert
  for tcb_at'_head'[wp]: "\<lambda>s. \<forall>head. tcbQueueHead queue = Some head \<longrightarrow> tcb_at' head s"
  and tcb_at'_end'[wp]: "\<lambda>s. \<forall>end. tcbQueueEnd queue = Some end \<longrightarrow> tcb_at' end s"
  (wp: crunch_wps)

lemma orderedInsert_tcb_at'_head[wp]:
  "\<lbrace>\<lambda>s. (\<forall>head. tcbQueueHead q = Some head \<longrightarrow> tcb_at' head s) \<and> tcb_at' t s\<rbrace>
   orderedInsert t q f R
   \<lbrace>\<lambda>rv s. \<forall>head. tcbQueueHead rv = Some head \<longrightarrow> tcb_at' head s\<rbrace>"
  unfolding orderedInsert_def
  by (wpsimp wp: hoare_drop_imps)

lemma orderedInsert_tcb_at'_end[wp]:
  "\<lbrace>\<lambda>s. (\<forall>end. tcbQueueEnd q = Some end \<longrightarrow> tcb_at' end s) \<and> tcb_at' t s\<rbrace>
   orderedInsert t q f R
   \<lbrace>\<lambda>rv s. \<forall>end. tcbQueueEnd rv = Some end \<longrightarrow> tcb_at' end s\<rbrace>"
  unfolding orderedInsert_def
  by (wpsimp wp: hoare_drop_imps)

lemma orderedInsert_tcbQueueHead_tcbQueueEnd[wp]:
  "\<lbrace>\<lambda>_. (tcbQueueHead q \<noteq> None) = (tcbQueueEnd q \<noteq> None)\<rbrace>
   orderedInsert t q f R
   \<lbrace>\<lambda>rv s. (\<exists>y. tcbQueueHead rv = Some y) = (\<exists>y. tcbQueueEnd rv = Some y)\<rbrace>"
  unfolding orderedInsert_def
  by (wpsimp wp: hoare_drop_imps)

lemma tcbReleaseEnqueue_ccorres:
  "ccorres dc xfdc
     (no_0_obj' and pspace_aligned' and pspace_distinct' and pspace_bounded')
     \<lbrace>\<acute>tcb = tcb_ptr_to_ctcb_ptr tcbPtr\<rbrace> hs
     (tcbReleaseEnqueue tcbPtr) (Call tcbReleaseEnqueue_'proc)"
  unfolding tcbReleaseEnqueue_def
  apply (ccorres_exec_l_pre ccorres_exec_l_pre: isRunnable_sp get_tcb_sp' getReleaseQueue_sp)+
  apply (rename_tac queue)
  apply (cinit' lift: tcb_' simp: orderedInsert_def)
   apply (rule_tac xf'=queue_'
               and val="tcb_queue_to_tcb_queue_C queue"
               and R="\<lambda>s. ksReleaseQueue s = queue"
                in ccorres_symb_exec_r_known_rv[where R'=UNIV])
      apply (rule conseqPre, vcg)
      apply clarsimp
      apply (frule rf_sr_ctcb_queue_relation_release_queue)
      apply (metis ctcb_queue_relation_def tcb_queue_to_tcb_queue_C_def tcb_queue_C_idupdates(1))
     apply ceqv
    apply (rename_tac aqueue tcb)
    apply (simp add: bind_assoc)
    apply (rule ccorres_stateAssert)
    apply (ctac (no_vcg) add: tcbReadyTime_ccorres)
     apply (clarsimp simp: bind_assoc)
     apply (rule_tac xf'=ret__unsigned_long_'
                 and val="from_bool (tcbQueueEmpty aqueue)"
                 and R="\<lambda>s. \<not> tcbQueueEmpty aqueue \<longrightarrow> tcb_at' (the (tcbQueueHead aqueue)) s
                            \<and> (tcbQueueHead aqueue \<noteq> None \<longleftrightarrow> tcbQueueEnd aqueue \<noteq> None)"
                  in ccorres_symb_exec_r_known_rv[where R'=UNIV])
        apply (rule conseqPre, vcg)
        apply (fastforce dest: tcb_at_not_NULL
                         simp: ctcb_queue_relation_def tcb_queue_to_tcb_queue_C_def
                               option_to_ctcb_ptr_def tcbQueueEmpty_def)
       apply ceqv
      apply csymbr
      apply (rule_tac r'="\<lambda>rv rv'. rv = to_bool rv'" and xf'=ret__int_' in ccorres_split_nothrow)
          apply (rule ccorres_cond[where R=\<top>])
            apply (fastforce simp: tcbQueueEmpty_def)
           apply (rule ccorres_return_Skip')
          apply clarsimp
          apply (rule ccorres_assert2)
          apply (ctac (no_vcg) add: tcbReadyTime_ccorres)
           apply (rule ccorres_return[where R=\<top> and R'=UNIV])
           apply (rule conseqPre, vcg)
           apply (fastforce split: if_splits)
          apply wp
         apply ceqv
        apply (subst bind_assoc[symmetric])
        apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow)
            apply (clarsimp simp: if_to_top_of_bind)
            apply (rule_tac Q="\<lambda>s. \<forall>head. tcbQueueHead aqueue = Some head \<longrightarrow> tcb_at' head s"
                         in ccorres_cond_both'[where Q'=\<top>, simplified])
              apply (clarsimp simp: to_bool_def split: if_splits)
             apply (simp flip: bind_assoc)
             apply (rule ccorres_call_getter_setter_dc[where P'=UNIV])
                apply (rule ccorres_guard_imp[where Q=Q and A=Q for Q, simplified])
                  apply (rule tcb_queue_prepend_ccorres)
                 apply fastforce
                apply (clarsimp simp: ctcb_queue_relation_def)
               apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                                     setReleaseQueue_def modify_def get_def put_def bind_def
                                     carch_state_relation_def cmachine_state_relation_def)
              apply fastforce
             apply wpsimp
            apply (clarsimp simp: bind_assoc)
            apply (rule ccorres_assert2)
            apply (ctac (no_vcg) add: tcbReadyTime_ccorres)
             apply (simp add: if_to_top_of_bind)
             apply (rule_tac Q="\<lambda>s. \<forall>head. tcbQueueHead aqueue = Some head \<longrightarrow> tcb_at' head s"
                          in ccorres_cond_both'[where Q'=\<top>, simplified])
               apply (fastforce split: if_splits)
              apply (rule ccorres_call_getter_setter_dc[where P'=UNIV])
                 apply (rule ccorres_guard_imp)
                   apply (rule tcb_queue_append_ccorres)
                  apply assumption
                 apply (clarsimp simp: ctcb_queue_relation_def)
                apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                                      setReleaseQueue_def modify_def get_def put_def bind_def
                                      carch_state_relation_def cmachine_state_relation_def)
               apply fastforce
              apply wpsimp
             apply wpsimp
             apply (rule ccorres_rhs_assoc)+
             apply csymbr
             apply (clarsimp simp: bind_assoc)
             apply (drule Some_to_the)
             apply clarsimp
             apply (ctac (no_vcg) add: find_time_after_ccorres)
              apply (rule ccorres_assert2)
              apply (rule ccorres_stateAssert)
              apply (rule ccorres_seq_skip'[THEN iffD1])
              apply (ctac (no_vcg) add: tcb_queue_insert_ccorres)
               apply (rule monadic_rewrite_ccorres_assemble)
                apply (rule ccorres_return_Skip)
               apply (rule setReleaseQueue_return_rewrite)
              apply wpsimp
             apply (rule_tac Q'="\<lambda>_ s. tcb_at' tcbPtr s \<and> valid_tcbs' s
                                       \<and> (\<exists>ts. list_queue_relation ts aqueue
                                                 (tcbSchedNexts_of s) (tcbSchedPrevs_of s)
                                       \<and> (\<forall>t \<in> set ts. tcb_at' t s)) \<and> ksReleaseQueue s = aqueue"
                          in hoare_post_imp)
              apply (intro conjI impI allI)
              apply (fastforce dest: heap_ls_unique simp: list_queue_relation_def)
             apply wpsimp+
           apply ceqv
          apply ctac
            apply (rule ccorres_pre_getReleaseQueue)
            apply (rename_tac queue'')
            apply (clarsimp simp: when_def)
            apply (rule_tac Q="\<lambda>s. ksReleaseQueue s = queue''
                                   \<and> (\<forall>head. tcbQueueHead queue'' = Some head \<longrightarrow> tcb_at' head s)
                                   \<and> (\<forall>head. tcbQueueHead aqueue = Some head \<longrightarrow> tcb_at' head s)"
                         in ccorres_cond_both'[where Q'=\<top>])
              apply clarsimp
              apply (frule rf_sr_ctcb_queue_relation_release_queue)
              apply (fastforce dest: tcb_at_not_NULL
                               simp: ctcb_queue_relation_def tcb_queue_to_tcb_queue_C_def
                                     option_to_ctcb_ptr_def
                              split: option.splits)
             apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg)
             apply (rule allI, rule conseqPre, vcg)
             subgoal
               by (clarsimp simp: setReprogramTimer_def rf_sr_def cstate_relation_def Let_def
                                  modify_def gets_def get_def put_def bind_def carch_state_relation_def
                                  cmachine_state_relation_def getReleaseQueue_def)
            apply (rule ccorres_return_Skip)
           apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift')
          apply (vcg exspec=thread_state_ptr_set_tcbInReleaseQueue_modifies)
         apply (wpsimp simp: setReleaseQueue_def)
            apply (rule_tac Q'="\<lambda>_ s. tcb_at' tcbPtr s
                                      \<and> (\<forall>head. tcbQueueHead aqueue = Some head \<longrightarrow> tcb_at' head s)"
                         in hoare_post_imp)
           apply fastforce
          apply wpsimp+
        apply (vcg exspec=tcb_queue_prepend_modifies exspec=tcb_queue_insert_modifies
                   exspec=find_time_after_modifies exspec=tcb_queue_append_modifies
                   exspec=tcbReadyTime_modifies)
        apply wpsimp+
      apply (vcg exspec=tcbReadyTime_modifies)
     apply (vcg exspec=tcb_queue_empty_modifies)
    apply wpsimp
   apply (vcg exspec=tcbReadyTime_modifies)
  apply (clarsimp simp: ksReleaseQueue_asrt_def)
  apply (frule (3) obj_at'_tcbQueueHead_ksReleaseQueue)
  apply (frule (3) obj_at'_tcbQueueEnd_ksReleaseQueue)
  apply (frule he_ptrs_head_iff_he_ptrs_end)
  apply (frule list_queue_relation_Nil)
  apply (clarsimp simp: list_queue_relation_def)
  apply (frule heap_path_head')
  apply clarsimp
  apply (rule conjI)
   subgoal by (auto simp: opt_pred_def opt_map_def obj_at'_def simp: tcbQueueEmpty_def)
  apply (clarsimp simp: ctcb_queue_relation_def tcb_queue_to_tcb_queue_C_def
                        option_to_ctcb_ptr_def tcbQueueEmpty_def
                 split: option.splits)
  done

lemma postpone_ccorres:
  "ccorres dc xfdc
     (no_0_obj' and pspace_aligned' and pspace_distinct' and pspace_bounded')
     \<lbrace>\<acute>sc = Ptr scPtr\<rbrace> []
     (postpone scPtr) (Call postpone_'proc)"
  apply (cinit lift: sc_')
   apply (rule ccorres_stateAssert)
   apply (rule ccorres_pre_getObject_sc)
   apply clarsimp
   apply (rename_tac sc)
   apply (rule ccorres_assert2)
   apply (rule ccorres_move_c_guard_sc)
   apply (rule_tac val="option_to_ctcb_ptr (scTCB sc)"
               and R="ko_at' sc scPtr"
               and R'=UNIV
               and xf'=tcb_'
                in ccorres_symb_exec_r_known_rv)
      apply (rule conseqPre, vcg)
      apply (fastforce dest: obj_at_cslift_sc simp: typ_heap_simps csched_context_relation_def)
     apply ceqv
    apply (ctac (no_vcg) add: tcbSchedDequeue_ccorres)
     apply (ctac (no_vcg) add: tcbReleaseEnqueue_ccorres)
      apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg)
      apply (rule allI, rule conseqPre, vcg)
      apply (clarsimp simp: setReprogramTimer_def rf_sr_def cstate_relation_def Let_def
                            modify_def get_def put_def bind_def carch_state_relation_def
                            cmachine_state_relation_def)
     apply wpsimp
    apply wpsimp
   apply vcg
  apply (rule conjI)
   apply (fastforce dest: sc_ko_at_valid_objs_valid_sc' simp: valid_sched_context'_def)
  apply (clarsimp simp: option_to_ctcb_ptr_def)
  done

lemma ccorres_getCTE_cte_at:
  "ccorresG rf_sr \<Gamma> r xf P P' hs (getCTE p >>= f) c
     \<Longrightarrow> ccorresG rf_sr \<Gamma> r xf (\<lambda>s. cte_at' p s \<longrightarrow> P s) P' hs
            (getCTE p >>= f) c"
  apply (rule ccorres_guard_imp)
    apply (subst gets_bind_ign[where f="cte_at' p", symmetric],
           rule ccorres_symb_exec_l[OF _ _ gets_wp])
      apply (rule_tac b=x in ccorres_case_bools)
       apply assumption
      apply (rule ccorres_getCTE)
      apply (rule ccorres_False[where P'=UNIV])
     apply wp
    apply simp
   apply (clarsimp simp: cte_wp_at_ctes_of)
  apply simp
  done

lemma sendIPC_block_ccorres_helper:
  "ccorres dc xfdc (tcb_at' thread and valid_objs' and pspace_canonical' and
                    ep_at' epptr and
                    (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s) and no_0_obj' and
                    pspace_aligned' and pspace_distinct' and
                    K (bos = ThreadState_BlockedOnSend
                      \<and> epptr' = epptr \<and> badge' = badge
                      \<and> cg = from_bool canGrant \<and> cgr = from_bool canGrantReply
                      \<and> dc' = from_bool do_call) and
                    K (epptr = epptr && ~~ mask 4))
                                 \<comment> \<open>this 4 is coming from thread_state_ptr_set_blockingObject_spec\<close>
                   UNIV hs
           (setThreadState (Structures_H.thread_state.BlockedOnSend
                                epptr badge canGrant canGrantReply do_call) thread)
           (Guard C_Guard
             \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t tcb_ptr_to_ctcb_ptr thread\<rbrace>
             (CALL thread_state_ptr_set_tsType(Ptr
              &(tcb_ptr_to_ctcb_ptr thread\<rightarrow>[''tcbState_C'']),
              scast bos));;
            Guard C_Guard
             \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t tcb_ptr_to_ctcb_ptr thread\<rbrace>
             (CALL thread_state_ptr_set_blockingObject(Ptr
                           &(tcb_ptr_to_ctcb_ptr thread\<rightarrow>[''tcbState_C'']), epptr'));;
            Guard C_Guard
             \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t tcb_ptr_to_ctcb_ptr thread\<rbrace>
             (CALL thread_state_ptr_set_blockingIPCBadge(Ptr
                        &(tcb_ptr_to_ctcb_ptr thread\<rightarrow>[''tcbState_C'']), badge'));;
            Guard C_Guard
             \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t tcb_ptr_to_ctcb_ptr thread\<rbrace>
             (CALL thread_state_ptr_set_blockingIPCCanGrant(Ptr
                           &(tcb_ptr_to_ctcb_ptr thread\<rightarrow>[''tcbState_C'']), cg));;
            Guard C_Guard
             \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t tcb_ptr_to_ctcb_ptr thread\<rbrace>
             (CALL thread_state_ptr_set_blockingIPCCanGrantReply(Ptr
                           &(tcb_ptr_to_ctcb_ptr thread\<rightarrow>[''tcbState_C'']), cgr));;
            Guard C_Guard
             \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t tcb_ptr_to_ctcb_ptr thread\<rbrace>
             (CALL thread_state_ptr_set_blockingIPCIsCall(Ptr
                         &(tcb_ptr_to_ctcb_ptr thread\<rightarrow>[''tcbState_C'']), dc'));;
            CALL scheduleTCB(tcb_ptr_to_ctcb_ptr thread))"
  unfolding K_def setThreadState_def
  apply (intro ccorres_gen_asm)
  apply (rule ccorres_guard_imp)
    apply (rule_tac P="canonical_address epptr" in ccorres_gen_asm)
    apply (rule ccorres_split_nothrow_novcg)
        apply (rule_tac P=\<top> and P'="tcb_at' thread"
                     in threadSet_ccorres_lemma3)
         apply vcg
        apply clarsimp
        apply (frule(1) tcb_at_h_t_valid)
        apply (frule h_t_valid_c_guard)
        apply (clarsimp simp: typ_heap_simps' rf_sr_tcb_update_twice
                        simp flip: canonical_bit_def)
        apply (erule(1) rf_sr_tcb_update_gen,
          (simp add: typ_heap_simps')+)[1]
         apply (simp add: tcb_cte_cases_def cteSizeBits_def)
        apply (simp add: ctcb_relation_def cthread_state_relation_def
                         ThreadState_defs mask_def)
        apply (clarsimp simp: canonical_address_sign_extended sign_extended_iff_sign_extend
                       split: bool.split)
       apply ceqv
      apply clarsimp
      apply (ctac add: scheduleTCB_ccorres)
     apply (wp threadSet_valid_objs')
    apply (clarsimp simp: guard_is_UNIV_def)
   apply (clarsimp simp: valid_tcb'_def tcb_cte_cases_def cteSizeBits_def)
   apply (drule obj_at'_is_canonical, simp, simp)
  apply clarsimp
  done

lemma setThreadStateBlockedOnReply_ccorres:
  "ccorres dc xfdc
     (tcb_at' thread and reply_at' replyPtr and no_0_obj'
      and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s)
      and pspace_aligned' and pspace_distinct' and pspace_canonical')
     (\<lbrace>\<acute>tptr = tcb_ptr_to_ctcb_ptr thread\<rbrace> \<inter> \<lbrace>\<acute>reply = Ptr replyPtr\<rbrace>) hs
     (setThreadState (BlockedOnReply (Some replyPtr)) thread)
     (Call setThreadStateBlockedOnReply_'proc)"
  apply (cinit lift: tptr_' reply_')
   apply (rule ccorres_guard_imp)
     apply (rule_tac P="canonical_address replyPtr" in ccorres_gen_asm)
     apply (rule ccorres_rhs_assoc2)
     apply (rule ccorres_split_nothrow_novcg)
         apply (rule_tac P=\<top> and P'="tcb_at' thread and reply_at' replyPtr"
                      in threadSet_ccorres_lemma3)
          apply vcg
         apply clarsimp
         apply (frule (1) tcb_at_h_t_valid)
         apply (frule h_t_valid_c_guard)
         apply (clarsimp simp: typ_heap_simps' rf_sr_tcb_update_twice simp flip: canonical_bit_def)
         apply (erule (1) rf_sr_tcb_update_gen, fastforce+)
          apply (simp add: tcb_cte_cases_def cteSizeBits_def)
         apply (simp add: ctcb_relation_def cthread_state_relation_def)
         apply (prop_tac "replyPtr = replyPtr && ~~ mask 4")
                                    \<comment> \<open>this 4 is coming from thread_state_ptr_set_replyObject_spec\<close>
          apply (clarsimp intro!: is_aligned_neg_mask_weaken[symmetric]
                            simp: pspace_aligned'_def objBits_simps' obj_at'_def)
         apply (clarsimp simp: canonical_address_sign_extended sign_extended_iff_sign_extend)
        apply ceqv
       apply (ctac add: scheduleTCB_ccorres)
      apply wp
     apply (clarsimp simp: guard_is_UNIV_def)
    apply force
   apply force
  apply (force dest!: obj_at'_is_canonical[where t=replyPtr])
  done

crunch setThreadState
  for tcbSchedContext_obj_at'[wp]: "\<lambda>s. Q (obj_at' (\<lambda>tcb. P (tcbSchedContext tcb)) t' s)"
  (wp: crunch_wps threadSet_obj_at'_no_state simp: crunch_simps)

lemma reply_push_ccorres:
  "ccorres dc xfdc
     (tcb_at' callerPtr and tcb_at' calleePtr and reply_at' replyPtr
      and no_0_obj' and pspace_aligned' and pspace_distinct' and pspace_canonical'
      and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s))
     (\<lbrace>\<acute>tcb_caller = tcb_ptr_to_ctcb_ptr callerPtr\<rbrace>
      \<inter> \<lbrace>\<acute>tcb_callee = tcb_ptr_to_ctcb_ptr calleePtr\<rbrace>
      \<inter> \<lbrace>\<acute>reply = Ptr replyPtr\<rbrace>
      \<inter> \<lbrace>\<acute>canDonate = from_bool canDonate\<rbrace>) hs
     (replyPush callerPtr calleePtr replyPtr canDonate) (Call reply_push_'proc)"
  supply Collect_const[simp del]
  supply if_split[split del]
  apply (cinit lift: tcb_caller_' tcb_callee_' reply_' canDonate_')
  apply (rename_tac canDonate' reply tcb_callee tcb_caller)
   apply (rule ccorres_stateAssert)+
   apply (rule ccorres_pre_getObject_reply)
   apply (rule ccorres_assert)
   apply (rule ccorres_stateAssert)+
   apply (rule ccorres_pre_threadGet)+
         apply (rule_tac xf'=sc_donated_'
                     and val="option_to_ptr scPtrOptDonated"
                     and R="obj_at' (\<lambda>tcb. tcbSchedContext tcb = scPtrOptDonated) callerPtr"
                      in ccorres_symb_exec_r_known_rv[where R'=UNIV])
      apply (rule conseqPre, vcg)
      apply normalise_obj_at'
      apply (frule (1) obj_at_cslift_tcb)
      apply (clarsimp simp: typ_heap_simps' ctcb_relation_def)
     apply ceqv
    apply (rule ccorres_move_c_guard_reply)
    apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow_novcg)
        apply (rule updateReply_ccorres_lemma2[where P=\<top>])
         apply vcg
        apply (frule (1) obj_at_cslift_reply)
        apply (fastforce intro!: rf_sr_reply_update2
                           simp: typ_heap_simps' creply_relation_def option_to_ctcb_ptr_def
                          split: if_splits)
       apply ceqv
      apply (ctac add: setThreadStateBlockedOnReply_ccorres, rename_tac xfdc')
        apply (rule ccorres_rhs_assoc2)
        apply (rule_tac xf'=ret__int_'
                    and val="from_bool ((\<exists>y. scPtrOptDonated = Some y) \<and> scPtrOptCallee = None)"
                    and R="obj_at' (\<lambda>tcb. tcbSchedContext tcb = scPtrOptDonated) callerPtr
                           and obj_at' (\<lambda>tcb. tcbSchedContext tcb = scPtrOptCallee) calleePtr
                           and valid_tcbs' and no_0_obj'"
                     in ccorres_symb_exec_r_known_rv[where R'=UNIV])
           apply (rule conseqPre, vcg)
           apply normalise_obj_at'
           apply (frule (1) obj_at_cslift_tcb[where thread=callerPtr])
           apply (frule (1) ko_at'_valid_tcbs'_valid_tcb'[where ptr=callerPtr])
           apply (frule (1) obj_at_cslift_tcb[where thread=calleePtr])
           apply (frule (1) ko_at'_valid_tcbs'_valid_tcb'[where ptr=calleePtr])
           apply (clarsimp simp: typ_heap_simps from_bool_def split: if_splits bool.splits)
           apply (fastforce simp: valid_tcb'_def ctcb_relation_def)
          apply ceqv
         apply (clarsimp simp: when_def)
         apply (rule ccorres_cond_both'[where Q=\<top> and Q'=\<top>])
           apply fastforce
          apply (clarsimp simp: bindScReply_def bind_assoc)
          apply (rename_tac scPtr)
          apply (rule ccorres_stateAssert)
          apply wpfix
          apply (rule ccorres_pre_getObject_sc, rename_tac sc)
          apply (rule ccorres_rhs_assoc)+
          apply (rule ccorres_move_c_guard_sc)
          apply (rule_tac xf'=old_caller_'
                      and val="option_to_ptr (scReply sc)"
                      and R="ko_at' sc scPtr"
                       in ccorres_symb_exec_r_known_rv[where R'=UNIV])
             apply (rule conseqPre, vcg)
             apply normalise_obj_at'
             apply (frule (1) obj_at_cslift_sc)
             apply (clarsimp simp: csched_context_relation_def typ_heap_simps)
            apply ceqv
           apply (rule ccorres_stateAssert)
           apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow_novcg)
               apply (clarsimp simp: when_def)
               apply (rule_tac Q="valid_sched_context' sc and valid_bound_reply' (scReply sc)
                                  and no_0_obj'"
                            in ccorres_cond_both'[where Q'=\<top>])
                 apply (fastforce simp: option_to_ptr_def option_to_0_def valid_sched_context'_def
                                        valid_bound_obj'_def
                                 split: option.splits)
                apply (rule ccorres_stateAssert)
                apply (rule_tac P'="reply_at' replyPtr and pspace_canonical'"
                             in updateReply_ccorres_lemma3[where P=\<top>])
                 apply vcg
                apply (frule (1) obj_at_cslift_reply)
                apply normalise_obj_at'
                apply (fastforce dest: obj_at'_is_canonical intro!: rf_sr_reply_update2
                                 simp: typ_heap_simps' creply_relation_def
                                       option_to_ptr_def option_to_0_def isHead_def
                                       sign_extend_canonical_address)
               apply (rule ccorres_return_Skip)
              apply ceqv
             apply (rule ccorres_rhs_assoc2)
             apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow_novcg)
                 apply (rule_tac P'="reply_at' replyPtr and pspace_canonical'
                                     and valid_sched_context' sc
                                     and obj_at' (\<lambda>sc'. scReply sc' = scReply sc) scPtr
                                     and valid_bound_reply' (scReply sc)"
                              in updateReply_ccorres_lemma3[where P=\<top>])
                  apply vcg
                 apply (frule (1) obj_at_cslift_reply)
                 apply normalise_obj_at'
                 subgoal
                   by (force dest: obj_at_cslift_reply obj_at'_is_canonical
                           intro!: rf_sr_reply_update2
                             simp: typ_heap_simps' creply_relation_def
                                   option_to_ptr_def option_to_0_def isHead_def
                                   sign_extend_canonical_address valid_sched_context'_def
                            split: if_splits option.splits)
                apply ceqv
               apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow_novcg)
                   apply (rule updateSchedContext_ccorres_lemma2[where P="\<top>"])
                     apply vcg
                    apply fastforce
                   apply (clarsimp simp: typ_heap_simps)
                   apply (rule_tac sc'="scReply_C_update (\<lambda>_. reply_Ptr replyPtr) sc'"
                                in rf_sr_sc_update_no_refill_buffer_update2;
                          fastforce?)
                     apply (clarsimp simp: typ_heap_simps' packed_heap_update_collapse_hrs)
                    apply (clarsimp simp: csched_context_relation_def option_to_ctcb_ptr_def)
                   apply (fastforce intro: refill_buffer_relation_sc_no_refills_update)
                  apply ceqv
                 apply (rule ccorres_rhs_assoc2)
                 apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow_novcg)
                     apply (rule_tac P'="reply_at' replyPtr and pspace_canonical' and sc_at' scPtr"
                                 in updateReply_ccorres_lemma3[where P=\<top>])
                      apply vcg
                     apply (frule (1) obj_at_cslift_reply)
                     apply normalise_obj_at'
                     apply (fastforce dest: obj_at'_is_canonical intro!: rf_sr_reply_update2
                                      simp: typ_heap_simps' creply_relation_def isHead_def
                                            sign_extend_canonical_address)
                    apply ceqv
                   apply (ctac add: schedContext_donate_ccorres)
                  apply wpsimp
                 apply (clarsimp simp: guard_is_UNIV_def)
                apply (wpsimp wp: updateSchedContext_valid_objs')
               apply (clarsimp simp: guard_is_UNIV_def)
              apply wpsimp
             apply (clarsimp simp: guard_is_UNIV_def)
            apply wpsimp
           apply (clarsimp simp: guard_is_UNIV_def)
          apply vcg
         apply (rule ccorres_return_Skip)
        apply vcg
       apply (rule_tac Q'="\<lambda>_ s. tcb_at' calleePtr s \<and> reply_at' replyPtr s
                                 \<and> valid_objs' s \<and> no_0_obj' s
                                 \<and> weak_sch_act_wf (ksSchedulerAction s) s
                                 \<and> pspace_aligned' s \<and> pspace_distinct' s \<and> pspace_canonical' s
                                 \<and> obj_at' (\<lambda>tcb. tcbSchedContext tcb = scPtrOptDonated) callerPtr s
                                 \<and> obj_at' (\<lambda>tcb. tcbSchedContext tcb = scPtrOptCallee) calleePtr s"
                    in hoare_post_imp)
        subgoal
          by (fastforce dest: sc_ko_at_valid_objs_valid_sc'
                        simp: valid_sched_context'_def obj_at'_def valid_obj'_def  valid_reply'_def
                       split: if_splits)
       apply wpsimp
      apply (vcg exspec=setThreadStateBlockedOnReply_modifies)
     apply (wpsimp wp: updateReply_valid_objs')
    apply (clarsimp simp: guard_is_UNIV_def)
   apply vcg
  apply (fastforce simp: valid_reply'_def obj_at'_def)
  done

lemma tcb_queue_C_eq:
  "\<lbrakk>head_C q = head_C q'; end_C q = end_C q'\<rbrakk> \<Longrightarrow> q = q'"
  by (metis tcb_queue_C_idupdates(1))

\<comment> \<open>FIXME RT: move to Lib, or rework proofs where this is used\<close>
lemma bind_assoc_group5':
  "(do x \<leftarrow> a; b x; z \<leftarrow> c x; d x z; v \<leftarrow> e x z; f v od)
   = (do v \<leftarrow> (do x \<leftarrow> a; b x; z \<leftarrow> c x; d x z; e x z od); f v od)"
  by (simp add: bind_assoc)

lemma higher_than_tcb_prio_ccorres:
  "ccorres (\<lambda>rv rv'. rv = to_bool rv') ret__unsigned_long_'
     (\<lambda>s. \<forall>tcbPtr. tcbPtrOpt = Some tcbPtr \<longrightarrow> tcb_at' tcbPtr s)
     (\<lbrace>\<acute>priority = ucast prio\<rbrace> \<inter> \<lbrace>\<acute>tcb = option_to_ctcb_ptr tcbPtrOpt\<rbrace>) []
     (gets_the (compareValsBackwards prio tcbPtrOpt (threadRead tcbPriority) (\<ge>)))
     (Call higher_than_tcb_prio_'proc)"
  (is "ccorres _ _ ?abs _ _ _ _")
  supply Collect_const[simp del]
  apply (cinit' lift: priority_' tcb_' simp: compareValsBackwards_def gets_the_if_distrib)
   apply csymbr
   apply (rule ccorres_cond_seq)
   apply ccorres_rewrite
   apply (rule ccorres_cond_both'[where Q="?abs" and Q'=\<top>])
     apply (fastforce dest: tcb_at_not_NULL simp: option_to_ctcb_ptr_def split: option.splits)
    apply simp
    apply (rule ccorres_symb_exec_l)
       apply (rename_tac tcb_prio)
       apply (rule ccorres_Guard_Seq)
       apply (rule_tac xf'=ret__int_'
                   and val="from_bool (tcb_prio < prio)"
                   and R="obj_at' (\<lambda>tcb. tcbPriority tcb = tcb_prio) (the tcbPtrOpt) "
                    in ccorres_symb_exec_r_known_rv[where R'=UNIV])
          apply (rule conseqPre, vcg)
          apply normalise_obj_at'
          apply (frule (1) obj_at_cslift_tcb)
          apply (clarsimp simp: option_to_ctcb_ptr_def ctcb_relation_def typ_heap_simps
                         split: if_splits)
          apply (intro conjI impI allI)
           apply (force intro: ucast_less_ucast [THEN iffD1, where 'b1=machine_word_len])
          apply (clarsimp simp: from_bool_def split: bool.splits)
          apply (force dest: ucast_less_ucast[THEN iffD2, where 'b1=machine_word_len, rotated])
         apply ceqv
        apply (fastforce intro: ccorres_return_C)
       apply vcg
      apply wpsimp+
   apply (fastforce intro: ccorres_return_C)
  apply clarsimp
  apply (intro conjI impI allI)
    apply (fastforce dest: threadRead_SomeD simp: obj_at'_def)
   apply (fastforce simp: to_bool_def from_bool_def split: bool.splits)
  apply (clarsimp simp: option_to_ctcb_ptr_def split: option.splits)
  apply (frule (1) obj_at_cslift_tcb)
  apply (clarsimp simp: typ_heap_simps)
  done

lemma compareValsBackwards_threadRead_SomeTrueD:
  "compareValsBackwards val tcbPtrOpt (threadRead proj) R s = Some True
   \<Longrightarrow> \<exists>tcbPtr. tcbPtrOpt = Some tcbPtr \<and> tcb_at' tcbPtr s"
  by (clarsimp dest!: threadRead_SomeD simp: compareValsBackwards_def split: if_splits)

lemma no_ofail_compareValsBackwards:
  "no_ofail
     (\<lambda>s. \<forall>ptr. ptrOpt = Some ptr \<longrightarrow> (\<exists>val. f ptr s = Some val))
     (compareValsBackwards val ptrOpt f R)"
  by (clarsimp simp: compareValsBackwards_def no_ofail_def obind_def split: if_splits)

lemma find_tcb_with_higher_prio_ccorres:
  "ccorres (\<lambda>ptr ptr'. ptr' = option_to_ctcb_ptr ptr) ret__ptr_to_struct_tcb_C_'
     (\<lambda>s. (\<exists>ts q. list_queue_relation ts q (tcbSchedNexts_of s) (tcbSchedPrevs_of s)
                  \<and> (\<forall>tcbPtr. tcbPtrOpt = Some tcbPtr \<longrightarrow> tcbPtr \<in> set ts)
                  \<and> (\<forall>t \<in> set ts. tcb_at' t s))
          \<and> sym_heap_sched_pointers s)
     (\<lbrace>\<acute>priority = ucast priority\<rbrace> \<inter> {s'. end_C (queue_' s') = option_to_ctcb_ptr tcbPtrOpt}) []
     (findInsertionPointBackwards priority tcbPtrOpt (threadRead tcbPriority) (\<ge>))
     (Call find_tcb_with_higher_prio_'proc)"
  supply sched_context_C_size[simp del] refill_C_size[simp del]
  apply (cinit lift: priority_' queue_'
               simp: runReaderT_def whileAnno_def)
   apply (rule ccorres_symb_exec_r)
     apply (rule ccorres_add_return2)
     apply (rule ccorres_rhs_assoc2)
     apply (rule ccorres_split_nothrow_novcg)
         apply (rule_tac r=tcbPtrOpt
                     and rrel="\<lambda>ptr ptr'. ptr' = option_to_ctcb_ptr ptr"
                     and xf=tcb_'
                     and cond_xf=ret__unsigned_long_'
                     and G="\<lambda>r s. \<exists>ts q. list_queue_relation
                                           ts q (tcbSchedNexts_of s) (tcbSchedPrevs_of s)
                                  \<and> (\<forall>tcbPtr. r  = Some tcbPtr \<longrightarrow> tcbPtr \<in> set ts)
                                  \<and> (\<forall>t \<in> set ts. tcb_at' t s)
                                  \<and> sym_heap_sched_pointers s"
                      in ccorres_While'[where P="\<lambda>w. w \<noteq> 0" and G'=UNIV])
              apply (rule stronger_ccorres_guard_imp)
                apply (rule ccorres_pre_getObject_tcb)
                apply (rule ccorres_Guard)
                apply (rule ccorres_return[where R=\<top>])
                apply vcg
                apply clarsimp
                apply (erule CollectD)
               apply fastforce
              apply (clarsimp simp: typ_heap_simps)
              apply (frule compareValsBackwards_threadRead_SomeTrueD)
              apply (clarsimp simp: typ_heap_simps option_to_ctcb_ptr_def ctcb_relation_def)
             apply (rule ccorres_guard_imp)
               apply (rule ccorres_rel_imp)
                apply (fastforce intro: ccorres_call[
                                          where xf'="ret__unsigned_long_'",
                                          OF higher_than_tcb_prio_ccorres])
               apply (clarsimp simp: to_bool_def)
              apply fastforce
             apply fastforce
            apply (wpsimp wp: no_ofail_compareValsBackwards)
            apply (rename_tac ptr q)
            apply (rule_tac m="threadRead tcbPriority ptr" in no_ofailD)
             apply wpsimp
            apply fastforce
           apply (wpsimp wp: getTCB_wp)
           apply (rename_tac ts q)
           apply (frule compareValsBackwards_threadRead_SomeTrueD)
           apply (rule_tac x=ts in exI)
           apply (fastforce dest: heap_ls_prev_cases
                            elim: sym_heapD2
                            simp: list_queue_relation_def obj_at'_def opt_map_red prev_queue_head_def)
          apply (rule conseqPre, vcg)
          apply (clarsimp simp: option_to_ctcb_ptr_def)
          apply (frule compareValsBackwards_threadRead_SomeTrueD)
          apply (fastforce dest: obj_at_cslift_tcb simp: typ_heap_simps)
         apply (rule conseqPre, vcg)
         apply (fastforce dest: obj_at_cslift_tcb
                          simp: option_to_ctcb_ptr_def typ_heap_simps split: option.splits)
        apply ceqv
       apply (fastforce intro: ccorres_return_C)
      apply wpsimp
     apply (clarsimp simp: guard_is_UNIV_def)
    apply vcg
   apply clarsimp
   apply (rule conseqPre, vcg)
   apply clarsimp
  apply clarsimp
  done

lemma tcb_queue_insert_after_ccorres:
  "ccorres dc xfdc
     (\<lambda>s. tcb_at' tcbPtr s \<and> tcb_at' beforePtr s \<and> valid_tcbs' s
          \<and> (\<exists>ts q. list_queue_relation ts q (tcbSchedNexts_of s) (tcbSchedPrevs_of s)
                    \<and> beforePtr \<in> set ts \<and> (\<forall>t \<in> set ts. tcb_at' t s)))
     (\<lbrace>\<acute>tcb = tcb_ptr_to_ctcb_ptr tcbPtr\<rbrace> \<inter> \<lbrace>\<acute>before = tcb_ptr_to_ctcb_ptr beforePtr\<rbrace>) hs
     (tcbQueueInsertAfter tcbPtr beforePtr) (Call tcb_queue_insert_after_'proc)"
  apply (cinit' lift: tcb_' before_')
   apply (simp only: tcbQueueInsertAfter_def)
   apply (rule ccorres_pre_getObject_tcb, rename_tac tcb)
   apply (rule ccorres_symb_exec_l, rename_tac afterPtr_opt)
      apply clarsimp
      apply (rule ccorres_assert2)
      apply clarsimp
      apply (rename_tac afterPtr)
      apply (rule ccorres_move_c_guard_tcb)
      apply (rule_tac xf'=after_'
                  and val="tcb_ptr_to_ctcb_ptr afterPtr"
                  and R="ko_at' tcb beforePtr and K (tcbSchedNext tcb = Some afterPtr)"
                   in ccorres_symb_exec_r_known_rv[where R'=UNIV])
         apply (rule conseqPre, vcg)
         apply (fastforce dest: obj_at_cslift_tcb
                          simp: typ_heap_simps ctcb_relation_def option_to_ctcb_ptr_def)
        apply ceqv
       apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow)
           apply (rule ccorres_move_c_guard_tcb)
           apply (rule_tac Q="\<lambda>s tcb. {s'. (s, s') \<in> rf_sr \<and> ko_at' tcb tcbPtr s}"
                        in threadSet_ccorres_lemma3[where P=\<top> and P'=\<top>, simplified])
            apply (rule conseqPre, vcg)
            apply clarsimp
            apply (frule (1) obj_at_cslift_tcb[where thread=tcbPtr])
            apply (fastforce elim!: rf_sr_tcb_update_gen2
                              simp: typ_heap_simps' ctcb_relation_def
                                    option_to_ctcb_ptr_def tcb_cte_cases_def cteSizeBits_def)
           apply fastforce
          apply ceqv
         apply (rule ccorres_split_nothrow[where r'=dc and xf'=xfdc])
             apply (rule ccorres_move_c_guard_tcb)
             apply (rule_tac Q="\<lambda>s tcb. {s'. (s, s') \<in> rf_sr \<and> ko_at' tcb tcbPtr s}"
                          in threadSet_ccorres_lemma3[where P=\<top> and P'=\<top>, simplified])
              apply (rule conseqPre, vcg)
              apply clarsimp
              apply (frule (1) obj_at_cslift_tcb[where thread=tcbPtr])
              apply (fastforce elim!: rf_sr_tcb_update_gen2
                                simp: typ_heap_simps' ctcb_relation_def
                                      option_to_ctcb_ptr_def tcb_cte_cases_def cteSizeBits_def)
             apply fastforce
            apply ceqv
           apply (rule ccorres_split_nothrow[where r'=dc and xf'=xfdc])
               apply (rule ccorres_move_c_guard_tcb)
               apply (rule_tac Q="\<lambda>s tcb. {s'. (s, s') \<in> rf_sr \<and> ko_at' tcb afterPtr s}"
                            in threadSet_ccorres_lemma3[where P=\<top> and P'=\<top>, simplified])
                apply (rule conseqPre, vcg)
                apply clarsimp
                apply (frule (1) obj_at_cslift_tcb)
                apply (fastforce elim!: rf_sr_tcb_update_gen2
                                  simp: typ_heap_simps' ctcb_relation_def option_to_ctcb_ptr_def
                                        tcb_cte_cases_def cteSizeBits_def)
               apply fastforce
              apply ceqv
             apply (rule ccorres_move_c_guard_tcb)
             apply (rule_tac Q="\<lambda>s tcb. {s'. (s, s') \<in> rf_sr \<and> ko_at' tcb beforePtr s}"
                          in threadSet_ccorres_lemma3[where P=\<top> and P'=\<top>])
              apply (rule conseqPre, vcg)
              apply clarsimp
              apply (frule (1) obj_at_cslift_tcb)
              apply (fastforce elim!: rf_sr_tcb_update_gen2
                                simp: typ_heap_simps' ctcb_relation_def option_to_ctcb_ptr_def
                                      tcb_cte_cases_def cteSizeBits_def)
             apply fastforce
            apply wpsimp
           apply vcg
          apply wpsimp
         apply vcg
        apply wpsimp
       apply vcg
      apply clarsimp
      apply vcg
     apply wpsimp
    apply wpsimp
   apply wpsimp
  apply (force dest!: heap_ls_next_in_list simp: list_queue_relation_def obj_at'_def opt_map_red)
  done

lemma tcbAppend_ccorres[corres]:
  "ccorres ctcb_queue_relation ret__struct_tcb_queue_C_'
     (valid_objs' and pspace_canonical' and tcb_at' tcbPtr)
     (\<lbrace>\<acute>tcb = tcb_ptr_to_ctcb_ptr tcbPtr\<rbrace> \<inter> \<lbrace>ctcb_queue_relation q \<acute>queue\<rbrace>) hs
     (tcbAppend tcbPtr q) (Call tcbAppend_'proc)"
  unfolding tcbAppend_def orderedInsert_def
  supply Collect_const[simp del]
  apply (ccorres_exec_l_pre ccorres_exec_l_pre: gets_the_sp)+
  apply (rename_tac val)
  apply (cinit' lift: tcb_' queue_')
   apply (rule ccorres_move_c_guard_tcb)
   apply (rule_tac xf'=priority_'
               and val="ucast val"
               and R="obj_at' (\<lambda>tcb. tcbPriority tcb = val) tcbPtr"
                in ccorres_symb_exec_r_known_rv[where R'=UNIV])
      apply (rule conseqPre, vcg)
      apply clarsimp
      apply (frule (1) obj_at_cslift_tcb)
      apply (clarsimp simp: ctcb_relation_def typ_heap_simps)
     apply ceqv
    apply csymbr
    apply (rule_tac xf'=ret__unsigned_long_'
                and val="from_bool (tcbQueueEmpty q)"
                and R="tcb_queue_head_end_valid q"
                 in ccorres_symb_exec_r_known_rv[where R'=UNIV])
       apply (rule conseqPre, vcg)
       apply (fastforce dest: tcb_at_not_NULL
                        simp: ctcb_queue_relation_def tcb_queue_to_tcb_queue_C_def
                              option_to_ctcb_ptr_def tcbQueueEmpty_def)
      apply ceqv
     apply (rule ccorres_rhs_assoc2)
     apply (rule_tac r'="\<lambda>rv rv'. rv' = from_bool rv"
                 and xf'=ret__int_'
                 and P="obj_at' (\<lambda>tcb. tcbPriority tcb = val) tcbPtr and tcb_queue_head_end_valid q"
                  in ccorres_split_nothrow[where P'=UNIV])
         apply (rule ccorres_guard_imp)
           apply csymbr
           apply (rule ccorres_cond_both'[where Q=\<top> and Q'=\<top>])
             apply fastforce
            apply (rule ccorres_return_Skip')
           apply clarsimp
           apply (rule ccorres_assert)
           apply (rule ccorres_symb_exec_l, rename_tac headVal)
              apply (rule ccorres_move_c_guard_tcb)
              apply (rule_tac R="obj_at' (\<lambda>tcb. tcbPriority tcb = headVal) (the (tcbQueueHead q))"
                           in ccorres_return[where R'=UNIV])
              apply (rule conseqPre, vcg)
              apply (clarsimp simp: ctcb_queue_relation_def tcb_queue_to_tcb_queue_C_def
                                    option_to_ctcb_ptr_def)
              apply (frule (1) obj_at_cslift_tcb)
              apply (clarsimp simp: ctcb_relation_def typ_heap_simps split: if_splits)
              apply (intro conjI impI allI)
                apply (rule order.strict_implies_order)
                apply (force simp: ucast_less_ucast[THEN iffD1, where 'b1=machine_word_len])
               apply force
              apply (clarsimp simp: from_bool_def split: bool.splits)
              apply (rule antisym)
               apply (force simp: ucast_le_ucast[THEN iffD1, where 'b1=machine_word_len])
              apply fastforce
             apply wpsimp
            apply wpsimp
           apply wpsimp
          apply clarsimp
          apply (rule conjI)
           apply (frule threadRead_SomeD)
           apply (clarsimp simp: obj_at'_def)
          apply (clarsimp simp: ctcb_queue_relation_def tcb_queue_to_tcb_queue_C_def
                                tcbQueueEmpty_def)
         apply clarsimp
        apply ceqv
       apply (rule ccorres_cond_seq)
       apply (rule ccorres_cond_both'[where Q=\<top> and Q'=\<top>])
         apply fastforce
        apply (rule ccorres_add_return2)
        apply (ctac (no_vcg) add: tcb_queue_prepend_ccorres)
         apply (fastforce intro: ccorres_return_C)
        apply fastforce
       apply wpsimp
       apply (rule ccorres_assert)
       apply (rule ccorres_symb_exec_l, rename_tac endVal)
          apply (rule ccorres_move_c_guard_tcb)
          apply (rule_tac Q="obj_at' (\<lambda>tcb. tcbPriority tcb = endVal) (the (tcbQueueEnd q))
                             and tcb_queue_head_end_valid q"
                      and C'="{s'. val \<le> endVal}"
                       in ccorres_rewrite_cond_sr_Seq[where Q'=UNIV])
           apply normalise_obj_at'
          apply (rename_tac "end" head_tcb end_tcb)
           apply (frule_tac thread="end" in obj_at_cslift_tcb)
            apply fastforce
           apply clarsimp
           apply (frule ctcb_relation_tcbPriority[symmetric])
           apply (clarsimp simp: typ_heap_simps ctcb_queue_relation_def
                                 tcb_queue_to_tcb_queue_C_def option_to_ctcb_ptr_def)
           apply (fastforce simp: ucast_le_ucast)
          apply (rule ccorres_cond_seq)
          apply (rule ccorres_cond_both'[where Q=\<top> and Q'=\<top>])
            apply fastforce
           apply (rule ccorres_add_return2)
           apply (ctac (no_vcg) add: tcb_queue_append_ccorres)
            apply (fastforce intro: ccorres_return_C)
           apply wpsimp
          apply (rule ccorres_rhs_assoc)+
          apply csymbr
          apply (simp only: bind_assoc_group5')
          apply (rule ccorres_rhs_assoc2)
          apply (rule ccorres_split_nothrow[where r'=dc and xf'=xfdc])
              apply (clarsimp simp del: insertionPoint_asrt_def return_bind K_bind_def del: exE)
              apply (rule monadic_rewrite_ccorres_assemble[rotated])
               apply (rule monadic_rewrite_guard_imp)
                apply (fastforce intro: findInsertionPointBackwards_rewrite)
               apply assumption
              apply (ctac (no_vcg) add: find_tcb_with_higher_prio_ccorres)
               apply (rule ccorres_assert2)
               apply clarsimp
               apply wpfix
               apply (rule ccorres_stateAssert)
               apply (ctac (no_vcg) add: tcb_queue_insert_after_ccorres)
              apply (rule_tac Q'="\<lambda>_ s. tcb_at' tcbPtr s \<and> valid_tcbs' s
                                        \<and> (\<exists>ts. list_queue_relation
                                                  ts q (tcbSchedNexts_of s) (tcbSchedPrevs_of s)
                                        \<and> (\<forall>t \<in> set ts. tcb_at' t s)) "
                           in hoare_post_imp)
               apply (clarsimp simp: list_queue_relation_def)
               apply (drule (1) heap_ls_unique)+
               apply force
              apply wpsimp
             apply ceqv
            apply (fastforce intro: ccorres_return_C)
           apply wp
          apply (vcg exspec=find_tcb_with_higher_prio_modifies
                     exspec=tcb_queue_insert_after_modifies)
         apply wpsimp
        apply wpsimp
       apply wpsimp
      apply wpsimp
     apply vcg
    apply (vcg exspec=tcb_queue_empty_modifies)
   apply vcg
  apply clarsimp
  apply (frule list_queue_relation_tcb_queue_head_end_valid)
   apply fastforce
  apply normalise_obj_at'
  apply (clarsimp simp: ctcb_queue_relation_def tcb_queue_to_tcb_queue_C_def option_to_ctcb_ptr_def)
  apply (intro conjI impI; (solves clarsimp)?)
       apply (fastforce dest: ko_at'_threadRead[where f=tcbPriority])
      apply (rename_tac ts tcb)
      apply (rule_tac x=ts in exI)
      apply clarsimp
      apply (rule conjI)
       apply fastforce
      apply (fastforce simp: list_queue_relation_def queue_end_valid_def)
     apply fastforce
    apply (fastforce dest: heap_path_head ko_at'_threadRead
                     simp: list_queue_relation_def queue_end_valid_def)
   apply normalise_obj_at'
   apply (fastforce dest: ko_at'_threadRead[where f=tcbPriority])
  apply (fastforce dest: ko_at'_threadRead[where f=tcbPriority])
  done

lemma TcbQueue_eq:
  "\<lbrakk>tcbQueueHead q = tcbQueueHead q'; tcbQueueEnd q = tcbQueueEnd q'\<rbrakk> \<Longrightarrow> q = q'"
  by (metis head_end_ptrs.collapse)

lemma tcbEPAppend_ccorres[corres]:
  "ccorres dc xfdc
     (valid_objs' and pspace_canonical' and tcb_at' thread and ep_at' epPtr)
     (\<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr thread\<rbrace> \<inter> \<lbrace>\<acute>epptr = ep_Ptr epPtr\<rbrace>
      \<inter> \<lbrace>cendpoint_state_relation state \<acute>ep_state\<rbrace>) hs
     (tcbEPAppend thread epPtr state) (Call tcbEPAppend_'proc)"
  unfolding tcbEPAppend_def
  apply (ccorres_exec_l_pre ccorres_exec_l_pre: get_ep_sp')+
  apply (cinit' lift: thread_' epptr_' ep_state_')
   apply clarsimp
   apply (rename_tac endpoint ep_state)
   apply (rule_tac xf'=queue_'
               and val="tcb_queue_to_tcb_queue_C (epQueue endpoint)"
               and R="ko_at' endpoint epPtr and valid_objs'"
                in ccorres_symb_exec_r_known_rv[where R'=UNIV])
      apply (rule conseqPre, vcg)
      apply normalise_obj_at'
      apply (frule (1) obj_at_cslift_ep)
      apply (fastforce intro: tcb_queue_C_eq
                        simp: cendpoint_relation_def ctcb_queue_relation_def
                              tcb_queue_to_tcb_queue_C_def typ_heap_simps)
     apply ceqv
    apply (ctac add: tcbAppend_ccorres)
      apply (rename_tac q' new_queue)
      apply (rule ccorres_split_nothrow[where r'=dc and xf'=xfdc])
          apply (rule_tac P'="ep_at' epPtr and pspace_canonical' and tcb_queue_head_end_valid q'"
                      and Q="\<lambda>s endpoint. {s'. (s, s') \<in> rf_sr \<and> ko_at' endpoint epPtr s
                                               \<and> pspace_canonical' s
                                               \<and> tcb_queue_head_end_valid q' s}"
                       in updateEndpoint_ccorres_lemma3[where P=\<top>])
           apply (rule conseqPre, vcg)
           apply clarsimp
           apply (frule (1) obj_at_cslift_ep)
           apply (clarsimp simp: typ_heap_simps')
           apply (simp cong: StateSpace.state.fold_congs globals.fold_congs)
           apply (fastforce intro!: rf_sr_endpoint_update2 tcb_and_not_mask_canonical
                              simp: cendpoint_relation_def Let_def
                                    ctcb_queue_relation_def tcb_queue_to_tcb_queue_C_def
                                    option_to_ctcb_ptr_def packed_heap_update_collapse_hrs
                                    tcbBlockSizeBits_def
                         simp flip: canonical_bit_def)
          apply clarsimp
         apply ceqv
        apply (rule_tac P'="ep_at' epPtr"
                    and Q="\<lambda>s endpoint. {s'. (s, s') \<in> rf_sr \<and> ko_at' endpoint epPtr s}"
                     in updateEndpoint_ccorres_lemma3[where P=\<top>])
         apply (rule conseqPre, vcg)
         apply clarsimp
         apply (frule (1) obj_at_cslift_ep)
         apply (clarsimp simp: typ_heap_simps')
         apply (simp cong: StateSpace.state.fold_congs globals.fold_congs)
         apply (fastforce intro!: rf_sr_endpoint_update2
                            simp: cendpoint_relation_def epstate_to_C_def cendpoint_state_relation_def
                                  endpoint_state_defs mask_def
                           split: epstate.splits)
        apply fastforce
       apply wpsimp
      apply (vcg exspec=ep_ptr_set_queue_modifies)
     apply (wpsimp simp: tcbAppend_def)
    apply (vcg exspec=tcbAppend_modifies)
   apply vcg
  apply (force dest: obj_at_cslift_ep simp: typ_heap_simps ctcb_queue_relation_def)
  done

crunch replyPush, doIPCTransfer, maybeReturnSc
  for weak_sch_act_wf[wp]: "\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s"
  and pspace_canonical'[wp]: pspace_canonical'
  (rule: weak_sch_act_wf_lift simp: crunch_simps wp: crunch_wps)

crunch setThreadState, replyPush, replyUnlink, schedContextDonate, doIPCTransfer
  for tcb_at'_head'[wp]: "\<lambda>s. \<forall>head. tcbQueueHead queue = Some head \<longrightarrow> tcb_at' head s"
  and tcb_at'_end'[wp]: "\<lambda>s. \<forall>end. tcbQueueEnd queue = Some end \<longrightarrow> tcb_at' end s"
  (wp: crunch_wps simp: crunch_simps)

lemma threadGet_exs_valid[wp]:
  "tcb_at' t s \<Longrightarrow> \<lbrace>(=) s\<rbrace> threadGet f t \<exists>\<lbrace>\<lambda>r. (=) s\<rbrace>"
  unfolding threadGet_def liftM_def
  apply (wpsimp wp: exs_getObject)
  apply (fastforce intro: no_ofailD[OF no_ofail_threadRead_tcb_at'])
  done

crunch setCTE
  for tcbSchedContext[wp]: "\<lambda>s. Q (obj_at' (\<lambda>tcb. P (tcbSchedContext tcb)) t s)"
  and tcbFault_Q[wp]: "\<lambda>s. Q (obj_at' (\<lambda>tcb. P (tcbFault tcb)) t s)"
  (wp: setObject_cte_obj_at_tcb')

crunch replyUnlink, doIPCTransfer, tcbEPDequeue
  for obj_at'_tcbSchedContext_Q[wp]: "\<lambda>s. Q (obj_at' (\<lambda>tcb. P (tcbSchedContext tcb)) tcbPtr s)"
  and obj_at'_tcbFault[wp]: "\<lambda>s. Q (obj_at' (\<lambda>tcb. P (tcbFault tcb)) tcbPtr s)"
  (wp: crunch_wps threadSet_obj_at'_no_state simp: crunch_simps ignore: setCTE)

lemma endpoint_ReceiveEPState_split:
  "(case epState ep of ReceiveEPState \<Rightarrow> f | _ \<Rightarrow> g) = (if epState ep = ReceiveEPState then f else g)"
  apply (cases ep; clarsimp)
  apply (rename_tac state queue, case_tac state; clarsimp)
  done

lemma sendIPC_ccorres[corres]:
  "ccorres dc xfdc
     (invs' and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s)
      and st_tcb_at' simple' thread and ep_at' epptr)
     (\<lbrace>\<acute>blocking = from_bool blocking\<rbrace>
      \<inter> \<lbrace>\<acute>do_call = from_bool do_call\<rbrace>
      \<inter> \<lbrace>\<acute>badge___unsigned_long = badge\<rbrace>
      \<inter> \<lbrace>\<acute>canGrant = from_bool canGrant\<rbrace>
      \<inter> \<lbrace>\<acute>canGrantReply = from_bool canGrantReply\<rbrace>
      \<inter> \<lbrace>\<acute>canDonate = from_bool canDonate\<rbrace>
      \<inter> \<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr thread\<rbrace>
      \<inter> \<lbrace>\<acute>epptr = Ptr epptr\<rbrace>) hs
     (sendIPC blocking do_call badge canGrant canGrantReply canDonate thread epptr)
     (Call sendIPC_'proc)"
  apply (cinit' lift: blocking_' do_call_' badge___unsigned_long_' canGrant_' canGrantReply_'
                      canDonate_' thread_' epptr_')
   apply (unfold sendIPC_def)[1]
   apply (subst endpoint_ReceiveEPState_split)
   apply (subst if_swap[where P="epState _ = ReceiveEPState"])
   apply (rule ccorres_stateAssert, clarsimp)
   apply (rule ccorres_stateAssert)+
   apply (rule ccorres_pre_getEndpoint)
   apply (rename_tac ep)
   apply (rule_tac xf'=ret__unsigned_longlong_'
               and val="epstate_to_C (epState ep)"
               and R="ko_at' ep epptr"
                in ccorres_symb_exec_r_known_rv[where R'=UNIV])
      apply vcg
      apply clarsimp
      apply (frule (1) obj_at_cslift_ep)
      apply (clarsimp simp: typ_heap_simps cendpoint_relation_def epstate_to_C_def
                            cendpoint_state_relation_def
                     split: epstate.splits)
     apply ceqv
    apply (rule_tac A="invs' and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s)
                       and st_tcb_at' simple' thread and ko_at' ep epptr and ep_at' epptr"
                 in ccorres_guard_imp2 [where A'=UNIV])
     apply (rule ccorres_cond_both'[where Q=\<top> and Q'=\<top>])
       apply (clarsimp simp: epstate_to_C_def endpoint_state_defs split: epstate.splits)
      apply (rule ccorres_cond[where R=\<top>])
        apply (fastforce split: if_splits)
       \<comment> \<open>the endpoint's state is not Receive.
           Gather all steps related to the update of the thread state, then split them off and
           use the helper lemma\<close>
       apply (intro ccorres_rhs_assoc)
       apply (repeat 6 \<open>rule ccorres_rhs_assoc2\<close>)
       apply (rule ccorres_split_nothrow_novcg, rule sendIPC_block_ccorres_helper)
          apply ceqv
         apply clarsimp
         apply (ctac add: tcbEPAppend_ccorres)
        apply wpsimp
       apply (clarsimp simp: guard_is_UNIV_def epstate_to_C_def cendpoint_state_relation_def)
      apply (rule ccorres_return_Skip)
     \<comment> \<open>ReceiveEPState\<close>
     apply (rule ccorres_cond_true)
     apply (intro ccorres_rhs_assoc)
     apply (csymbr, csymbr)
     apply clarsimp
     apply (rule ccorres_stateAssert)+
     apply (rule ccorres_assert2)+
     apply (rule ccorres_stateAssert)+
     apply (rule ccorres_symb_exec_l3, rename_tac action)
        apply (rule ccorres_assert2)
        apply (rule_tac xf'=queue_'
                    and val="tcb_queue_to_tcb_queue_C (epQueue ep)"
                    and R="ko_at' ep epptr and valid_objs'"
                     in ccorres_symb_exec_r_known_rv[where R'=UNIV])
           apply (rule conseqPre, vcg)
           apply normalise_obj_at'
           apply (frule (1) obj_at_cslift_ep)
           apply (fastforce intro!: tcb_queue_C_eq
                              simp: cendpoint_relation_def typ_heap_simps
                                    ctcb_queue_relation_def tcb_queue_to_tcb_queue_C_def)
          apply ceqv
         apply (rule_tac xf'=dest_'
                     and val="option_to_ctcb_ptr (tcbQueueHead (epQueue ep))"
                     and R="ko_at' ep epptr and valid_objs'"
                      in ccorres_symb_exec_r_known_rv[where R'=UNIV])
            apply (rule conseqPre, vcg)
            apply normalise_obj_at'
            apply (frule (1) obj_at_cslift_ep)
            apply (fastforce simp: tcb_queue_to_tcb_queue_C_def)
           apply ceqv
          apply (ctac add: tcbEPDequeue_ccorres)
            apply (rule ccorres_symb_exec_l3, rename_tac recvState)
               apply (rule ccorres_assert2)
               apply (ctac add: doIPCTransfer_ccorres)
                 apply (rule ccorres_stateAssert)
                 apply (rule ccorres_move_c_guard_tcb)
                 apply (rule_tac xf'=ret__unsigned_longlong_'
                             and val="option_to_0 (replyObject recvState)"
                             and R="st_tcb_at' ((=) recvState) (the (tcbQueueHead (epQueue ep)))
                                    and K (tcbQueueHead (epQueue ep) \<noteq> None)"
                              in ccorres_symb_exec_r_known_rv[where R'=UNIV])
                    apply (rule conseqPre, vcg)
                    apply (clarsimp simp: st_tcb_at'_def split: if_splits)
                    apply normalise_obj_at'
                    apply (frule (1) obj_at_cslift_tcb)
                    apply (fastforce simp: ctcb_relation_def cthread_state_relation_def
                                           isReceive_def typ_heap_simps option_to_ctcb_ptr_def
                                    split: thread_state.splits)
                   apply ceqv
                  apply csymbr
                  apply (rule ccorres_split_nothrow[where r'=dc and xf'=xfdc])
                      apply (simp add: case_option_If2)
                      apply (rule_tac Q="valid_bound_reply' (replyObject recvState) and no_0_obj'"
                                   in ccorres_cond_both'[where Q'="\<top>"])
                        apply (fastforce simp: valid_bound_obj'_def option_to_0_def
                                        split: if_splits option.splits)
                       apply clarsimp
                       apply (drule Some_to_the)
                       apply (fastforce intro: ccorres_call[OF reply_unlink_ccorres])
                      apply (rule ccorres_return_Skip)
                     apply ceqv
                    \<comment> \<open>the following is for scOptDest, the tcbSchedContext of dest, the head of the
                        original queue\<close>
                    apply (rule ccorres_symb_exec_l3, rename_tac scOptDest)
                       apply (rule ccorres_symb_exec_l3, rename_tac fault)
                          apply (rule ccorres_rhs_assoc2)
                          apply (rule ccorres_rhs_assoc2)
                          apply (rule ccorres_split_nothrow[where r'=dc and xf'=xfdc])
                              apply (rule_tac P=do_call in ccorres_cases; clarsimp)
                               apply (rule ccorres_rhs_assoc)+
                               apply csymbr
                               apply ccorres_rewrite
                               apply (rule ccorres_cond_true)
                               apply (rule_tac Q="valid_bound_reply' (replyObject recvState)
                                                  and no_0_obj'"
                                            in ccorres_cond_both'[where Q'=\<top>])
                                 apply (case_tac "replyObject recvState"; clarsimp)
                                 apply (clarsimp simp: valid_bound_reply'_def from_bool_def
                                                split: option.splits bool.splits if_splits)
                                 apply (fastforce dest: ko_at'_not_NULL)
                                apply (ctac add: reply_push_ccorres)
                               apply (ctac add: setThreadState_ccorres)
                              apply (rule ccorres_rhs_assoc)+
                              apply csymbr
                              apply ccorres_rewrite
                              apply (rule ccorres_rhs_assoc)+
                              apply (rule ccorres_move_c_guard_tcb)
                              apply (rule_tac val="case_option (scast seL4_Fault_NullFault)
                                                               fault_to_fault_tag fault"
                                          and xf'=ret__unsigned_longlong_'
                                          and R="\<lambda>s. \<exists>tcb. ko_at' tcb thread s \<and> tcbFault tcb = fault"
                                           in ccorres_symb_exec_r_known_rv[where R'=UNIV])
                                 apply (vcg, clarsimp)
                                 apply (erule (1) cmap_relation_ko_atE[OF cmap_relation_tcb])
                                 subgoal
                                   by (fastforce simp: ctcb_relation_def typ_heap_simps
                                                       cfault_rel_def seL4_Fault_lift_def Let_def
                                                split: if_split_asm option.split)
                                apply ceqv
                               apply (rule_tac xf'=ret__int_'
                                           and val="from_bool (\<exists>f. fault = Some f)"
                                            in ccorres_symb_exec_r_known_rv[where  R=\<top> and R'=UNIV])
                                  apply (rule conseqPre, vcg)
                                  apply (clarsimp split: option.splits fault.splits)
                                  apply (rename_tac fault s', case_tac fault;
                                         clarsimp simp: seL4_Faults)
                                  apply (rename_tac arch_fault, case_tac arch_fault,
                                         clarsimp simp: seL4_Arch_Faults split: if_splits)
                                 apply ceqv
                                apply (rule ccorres_cond_both'[where Q=\<top> and Q'=\<top>])
                                  apply fastforce
                                 apply (rule_tac Q="valid_bound_reply' (replyObject recvState)
                                                    and no_0_obj'"
                                              in ccorres_cond_both'[where Q'=\<top>])
                                   apply (case_tac "replyObject recvState"; clarsimp)
                                   apply (fastforce dest: ko_at'_not_NULL
                                                   split: bool.splits if_splits)
                                  apply (ctac add: reply_push_ccorres)
                                 apply (ctac add: setThreadState_ccorres)
                                apply (rule_tac xf'=ret__int_'
                                            and val="from_bool (canDonate \<and> scOptDest = Nothing)"
                                            and R="\<lambda>s. obj_at' (\<lambda>tcb. tcbSchedContext tcb = scOptDest)
                                                               (the (tcbQueueHead (epQueue ep))) s
                                                       \<and> valid_objs' s \<and> no_0_obj' s
                                                       \<and> tcbQueueHead (epQueue ep) \<noteq> None"
                                             in ccorres_symb_exec_r_known_rv[where R'=UNIV])
                                   apply (rule conseqPre, vcg)
                                   apply normalise_obj_at'
                                   apply (frule (1) tcb_ko_at_valid_objs_valid_tcb')
                                   apply (frule (1) obj_at_cslift_tcb)
                                   apply (rename_tac tcb)
                                   apply (case_tac "tcbSchedContext tcb";
                                          force simp: ctcb_relation_def valid_tcb'_def
                                                      option_to_ctcb_ptr_def option_to_0_def
                                                      typ_heap_simps tcbQueueEmpty_def
                                               split: if_splits option.splits)
                                  apply ceqv
                                 apply (clarsimp simp: when_def)
                                 apply (rule_tac ccorres_cond_both'[where Q=\<top> and Q'=\<top>])
                                   apply (clarsimp split: if_splits)
                                  apply clarsimp
                                  apply (rule ccorres_pre_threadGet, rename_tac scOptSrc)
                                  apply (rule ccorres_assert2)
                                  apply (rule ccorres_move_c_guard_tcb)
                                  apply (ctac add: schedContext_donate_ccorres)
                                 apply (rule ccorres_return_Skip)
                                apply vcg
                               apply vcg
                              apply clarsimp
                              apply (vcg exspec=seL4_Fault_ptr_get_seL4_FaultType_modifies)
                             apply ceqv
                            apply (ctac add: setThreadState_ccorres)
                              apply (clarsimp simp: ifCondRefillUnblockCheck_def)
                              apply (rule ccorres_pre_threadGet)
                              apply (rule ccorres_move_c_guard_tcb)
                              apply (rule_tac xf'=dest_sc_'
                                          and val="option_to_ptr scOpt"
                                          and R="\<lambda>s. obj_at' (\<lambda>tcb. tcbSchedContext tcb = scOpt)
                                                             (the (tcbQueueHead (epQueue ep))) s
                                                     \<and> valid_objs' s \<and> no_0_obj' s
                                                     \<and> tcbQueueHead (epQueue ep) \<noteq> None"
                                           in ccorres_symb_exec_r_known_rv[where R'=UNIV])
                                 apply (rule conseqPre, vcg)
                                 apply normalise_obj_at'
                                 apply (frule (1) tcb_ko_at_valid_objs_valid_tcb')
                                 apply (frule (1) obj_at_cslift_tcb)
                                 apply (clarsimp simp: ctcb_relation_def typ_heap_simps
                                                       option_to_ctcb_ptr_def)
                                apply ceqv
                               apply (clarsimp simp: when_def)
                               apply (simp add: if_to_top_of_bind)
                               apply (rule ccorres_if_lhs)
                                apply (clarsimp simp: bind_assoc, rename_tac scPtr)
                                apply wpfix
                                apply (rule ccorres_pre_getObject_sc, rename_tac sc)
                                apply (rule ccorres_pre_getCurSc, rename_tac cur_sc)
                                apply (rule ccorres_rhs_assoc2)
                                apply (rule ccorres_split_nothrow[where r'=dc and xf'=xfdc])
                                    apply (rule_tac xf'=ret__unsigned_long_'
                                                and val="from_bool (scSporadic sc)"
                                                and R="\<lambda>s. obj_at' (\<lambda>tcb. tcbSchedContext tcb = Some scPtr)
                                                                   (the (tcbQueueHead (epQueue ep))) s
                                                           \<and> ko_at' sc scPtr s \<and> no_0_obj' s
                                                           \<and> tcbQueueHead (epQueue ep) \<noteq> None"
                                                 in ccorres_symb_exec_r_known_rv[where R'=UNIV])
                                       apply (rule conseqPre, vcg)
                                       apply normalise_obj_at'
                                       apply (frule (1) obj_at_cslift_tcb)
                                       apply (frule (1) obj_at_cslift_sc)
                                       apply (clarsimp simp: typ_heap_simps ctcb_relation_def
                                                             csched_context_relation_def to_bool_def
                                                             option_to_ctcb_ptr_def
                                                      split: if_splits)
                                      apply ceqv
                                     apply (rule_tac Q="\<lambda>s. obj_at' (\<lambda>tcb. tcbSchedContext tcb = Some scPtr)
                                                                    (the (tcbQueueHead (epQueue ep))) s
                                                            \<and> ksCurSc s = cur_sc"
                                                  in ccorres_cond_both'[where Q'=\<top>])
                                       apply normalise_obj_at'
                                       apply (frule rf_sr_ksCurSC)
                                       apply clarsimp
                                      apply (ctac add: refill_unblock_check_ccorres)
                                     apply (rule ccorres_return_Skip)
                                    apply (vcg exspec=sc_sporadic_modifies)
                                   apply ceqv
                                  apply (ctac add: possibleSwitchTo_ccorres)
                                 apply wpsimp
                                apply (clarsimp simp: tcbQueueEmpty_def option_to_ctcb_ptr_def)
                                apply (vcg exspec=refill_unblock_check_modifies
                                           exspec=sc_sporadic_modifies)
                               apply clarsimp
                               apply (rule_tac xf'=ret__unsigned_long_'
                                           and val="from_bool False"
                                           and R="\<lambda>s. obj_at' (\<lambda>tcb. tcbSchedContext tcb = None)
                                                              (the (tcbQueueHead (epQueue ep))) s
                                                      \<and> tcbQueueHead (epQueue ep) \<noteq> None"
                                            in ccorres_symb_exec_r_known_rv[where R'=UNIV])
                                  apply (rule conseqPre, vcg)
                                  apply clarsimp
                                 apply ceqv
                                apply (rule ccorres_cond_seq)
                                apply ccorres_rewrite
                                apply (ctac add: possibleSwitchTo_ccorres)
                               apply (clarsimp simp: tcbQueueEmpty_def option_to_ctcb_ptr_def)
                               apply (vcg exspec=sc_sporadic_modifies)
                              apply vcg
                             apply (rule_tac Q'="\<lambda>_ s. tcbQueueHead (epQueue ep) \<noteq> None
                                                       \<and> tcb_at' (the (tcbQueueHead (epQueue ep))) s
                                                       \<and> tcb_queue_head_end_valid (epQueue ep) s
                                                       \<and> valid_objs' s \<and> no_0_obj' s
                                                       \<and> weak_sch_act_wf (ksSchedulerAction s) s
                                                       \<and> ksCurDomain s \<le> maxDomain
                                                       \<and> pspace_aligned' s \<and> pspace_distinct' s
                                                       \<and> pspace_bounded' s"
                                          in hoare_post_imp)
                              apply (clarsimp simp: obj_at'_def)
                             apply wpsimp
                            apply (vcg exspec=setThreadState_modifies)
                           apply (wpsimp wp: threadGet_wp'')
                          apply (vcg exspec=reply_push_modifies
                                     exspec=schedContext_donate_modifies
                                     exspec=setThreadState_modifies)
                         apply wpsimp
                        apply (rule_tac Q'="\<lambda>ft s. tcb_at' thread s
                                                   \<and> tcb_at' (the (tcbQueueHead (epQueue ep))) s
                                                   \<and> obj_at' (\<lambda>tcb. tcbSchedContext tcb = scOptDest)
                                                             (the (tcbQueueHead (epQueue ep))) s
                                                   \<and> obj_at' (\<lambda>tcb. tcbFault tcb = ft) thread s
                                                   \<and> tcb_queue_head_end_valid (epQueue ep) s
                                                   \<and> valid_bound_reply' (replyObject recvState) s
                                                   \<and> valid_objs' s \<and> no_0_obj' s
                                                   \<and> weak_sch_act_wf (ksSchedulerAction s) s
                                                   \<and> ksCurDomain s \<le> maxDomain
                                                   \<and> pspace_aligned' s \<and> pspace_distinct' s
                                                   \<and> pspace_bounded' s \<and> pspace_canonical' s"
                                     in hoare_post_imp)
                         apply normalise_obj_at'
                         subgoal
                           by (fastforce dest!: tcb_ko_at_valid_objs_valid_tcb'
                                          simp: tcbQueueEmpty_def option_to_ctcb_ptr_def
                                                valid_tcb'_def obj_at'_def
                                         split: if_splits)
                        apply (wpsimp wp: threadGet_wp'')
                       apply wpsimp
                      apply wpsimp
                     apply (wpsimp wp: threadGet_wp'')
                    apply wpsimp
                   apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift')
                  apply (vcg exspec=reply_unlink_modifies)
                 apply (vcg exspec=setThreadState_modifies)
                apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift')
               apply (vcg exspec=doIPCTransfer_modifies)
              apply wpsimp
             apply (wpsimp wp: gts_wp')
            apply wpsimp
           apply ((wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift'
                   | strengthen invs_valid_pspace')+)[1]
          apply (vcg exspec=tcbEPDequeue_modifies)
         apply vcg
        apply (vcg exspec=ep_ptr_get_queue_modifies)
       apply wpsimp
      apply wpsimp
     apply wpsimp
    apply clarsimp
    apply (prop_tac "tcb_at' thread s")
     apply fastforce
    apply (prop_tac "epptr = epptr AND NOT (mask 4)")
                                        \<comment> \<open>this 4 is coming from sendIPC_block_ccorres_helper\<close>
     apply (clarsimp simp: obj_at'_def objBits_simps')
    apply (clarsimp simp: option_to_ctcb_ptr_def tcbQueueEmpty_def)
    subgoal
      by (intro conjI impI allI;
          force simp: ctcb_relation_def tcbQueueEmpty_def option_to_ctcb_ptr_def
                      typ_heap_simps option_to_ptr_def option_to_0_def epstate_to_C_def
                      endpoint_state_defs
               split: if_splits option.splits epstate.splits)
   apply (vcg exspec=endpoint_ptr_get_state_modifies)
  apply clarsimp
  done

lemma ctcb_relation_blockingIPCCanGrantReplyD:
  "\<lbrakk>ctcb_relation ko ko'; isSend (tcbState ko)\<rbrakk>
   \<Longrightarrow> blockingIPCCanGrantReply_CL (thread_state_lift (tcbState_C ko'))
       = from_bool (blockingIPCCanGrantReply (tcbState ko))"
  apply (case_tac "tcbState ko" ; clarsimp simp: isReceive_def isSend_def)
  apply (clarsimp simp: ctcb_relation_def cthread_state_relation_def
                        thread_state_lift_def from_bool_to_bool_iff mask_eq1_nochoice)
  done

lemmas ccorres_pre_getBoundNotification = ccorres_pre_threadGet[where f=tcbBoundNotification, folded getBoundNotification_def]

lemma schedContext_resume_ccorres:
  "ccorres dc xfdc
     (no_0_obj' and pspace_aligned' and pspace_distinct' and pspace_bounded') \<lbrace>\<acute>sc = Ptr scPtr\<rbrace> hs
     (schedContextResume scPtr) (Call schedContext_resume_'proc)"
  supply Collect_const[simp del]
  apply (cinit lift: sc_')
   apply (rule ccorres_stateAssert)
   apply (rule ccorres_pre_getObject_sc)
   apply (clarsimp, rename_tac sc)
   apply (rule ccorres_assert2)
   apply (rule_tac xf'=ret__int_'
               and val="from_bool True"
               and R="ko_at' sc scPtr and no_0_obj'"
               and R'=UNIV
                in ccorres_symb_exec_r_known_rv)
      apply (rule conseqPre, vcg, clarsimp)
      apply (frule (1) obj_at_cslift_sc)
      apply (clarsimp split: if_splits)
     apply ceqv
    apply ccorres_rewrite
    apply (rule ccorres_rhs_assoc)
    apply (rule ccorres_move_c_guard_sc)
    apply (ctac add: isSchedulable_ccorres)
      apply csymbr
      apply (clarsimp simp: when_def)
      apply (rule ccorres_cond[where R=\<top>])
        apply (clarsimp simp: to_bool_def)
       apply (rule ccorres_rhs_assoc)+
       apply (ctac add: refill_ready_ccorres)
         apply (clarsimp, rename_tac is_ready)
         apply csymbr
         apply (rule_tac P="to_bool is_ready" in ccorres_cases; clarsimp)
          \<comment> \<open>the scheduling context is ready, so we proceed to check whether it is sufficient\<close>
          apply (rule ccorres_cond_seq)
          apply (rule ccorres_cond_true)
          apply (rule ccorres_rhs_assoc)+
          apply (ctac add: refill_sufficient_ccorres)
            apply csymbr
            apply (rule ccorres_cond[where R=\<top>])
              apply (clarsimp simp: to_bool_def)
             apply (ctac add: postpone_ccorres)
            apply (rule ccorres_return_Skip)
           apply wpsimp
          apply (vcg exspec=refill_sufficient_modifies)
         \<comment> \<open>the scheduling context is not ready, so we do not need to check whether it is sufficient\<close>
         apply (rule ccorres_cond_seq)
         apply (rule ccorres_cond_false)
         apply ccorres_rewrite
         apply (rule ccorres_cond_true)
         apply (rule ccorres_symb_exec_l')
            apply (ctac add: postpone_ccorres)
           apply wpsimp+
       apply (vcg exspec=refill_ready_modifies)
      apply (rule ccorres_return_Skip)
     apply (wpsimp wp: getSchedulable_wp)
    apply (vcg exspec=isSchedulable_modifies)
   apply vcg
  apply (rule conjI)
   apply (fastforce dest: sc_ko_at_valid_objs_valid_sc' simp: valid_sched_context'_def)
  apply (fastforce simp: typ_heap_simps csched_context_relation_def option_to_ctcb_ptr_def
                         to_bool_def)
  done

lemma maybeDonateSchedContext_ccorres:
  "ccorres dc xfdc
     (tcb_at' tcbPtr and invs' and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s))
     (\<lbrace>\<acute>tcb = tcb_ptr_to_ctcb_ptr tcbPtr\<rbrace> \<inter> \<lbrace>\<acute>ntfnPtr = Ptr ntfnPtr\<rbrace>) hs
     (maybeDonateSc tcbPtr ntfnPtr) (Call maybeDonateSchedContext_'proc)"
  supply Collect_const[simp del]
  apply (cinit lift: tcb_' ntfnPtr_')
   apply (rule ccorres_stateAssert)
   apply (rule ccorres_pre_threadGet)
   apply (rule ccorres_move_c_guard_tcb)
   apply (clarsimp simp: when_def)
   apply (rule_tac Q="obj_at' (\<lambda>tcb. scOpt = tcbSchedContext tcb) tcbPtr
                      and valid_objs' and no_0_obj'"
                in ccorres_cond_both'[where Q'=\<top>])
     apply normalise_obj_at'
     apply (rename_tac tcb)
     apply (frule (1) obj_at_cslift_tcb)
     apply (frule (1) tcb_ko_at_valid_objs_valid_tcb')
     apply (case_tac "tcbSchedContext tcb";
            clarsimp simp: ctcb_relation_def typ_heap_simps valid_tcb'_def)
    \<comment> \<open>tcbPtr is not associated with a scheduling context, so we may potentially
       donate to tcbPtr later\<close>
    apply (clarsimp simp: liftM_def)
    apply (rule ccorres_pre_getNotification)
    apply (rename_tac ntfn)
    apply (rule ccorres_rhs_assoc)
    apply (rule ccorres_rhs_assoc)
    apply (rule_tac xf'=sc_'
                and val="option_to_ptr (ntfnSc ntfn)"
                and R="ko_at' ntfn ntfnPtr"
                and R'=UNIV
                 in ccorres_symb_exec_r_known_rv)
       apply (rule conseqPre, vcg)
       apply clarsimp
       apply (erule cmap_relationE1 [OF cmap_relation_ntfn])
        apply (erule ko_at_projectKO_opt)
       apply (clarsimp simp: typ_heap_simps cnotification_relation_def Let_def)
      apply ceqv
     apply csymbr
     apply (simp add: case_option_If2)
     apply (rule ccorres_cond_seq)
     apply (rule_tac Q="ko_at' ntfn ntfnPtr and valid_objs' and no_0_obj'"
                  in ccorres_cond_both'[where Q'=\<top>])
       apply clarsimp
       apply (frule (1) ntfn_ko_at_valid_objs_valid_ntfn')
       apply (clarsimp simp: option_to_ptr_def option_to_0_def valid_ntfn'_def
                      split: option.splits)
      apply (simp add: liftM_def)
      apply (rule ccorres_pre_getObject_sc)
      apply (rule ccorres_move_c_guard_sc)
      apply (rule_tac xf'=ret__int_'
                  and val="from_bool (scTCB rv = None)"
                  and R="ko_at' ntfn ntfnPtr and ko_at' rv (the (ntfnSc ntfn))
                         and valid_objs' and no_0_obj'"
                   in ccorres_symb_exec_r_known_rv[where R'=UNIV])
         apply (rule conseqPre, vcg)
         apply normalise_obj_at'
         apply (frule (1) sc_ko_at_valid_objs_valid_sc')
         apply (frule (1) obj_at_cslift_sc)
         apply (force dest!: tcb_at_not_NULL
                       simp: typ_heap_simps' option_to_ctcb_ptr_def csched_context_relation_def
                             valid_sched_context'_def from_bool_def
                      split: option.splits bool.splits)
        apply ceqv
       apply (rule ccorres_cond_both'[where Q=\<top> and Q'=\<top>])
         apply fastforce
        \<comment> \<open>the scheduling context associated with ntfnPtr is not bound to a TCB, so
            we donate it to tcbPtr\<close>
        apply (ctac add: schedContext_donate_ccorres)
          apply (ctac add: schedContext_resume_ccorres)
         apply clarsimp
         apply (drule Some_to_the)
         apply (wpsimp wp: schedContextDonate_valid_objs')
        apply (vcg exspec=schedContext_donate_modifies)
       apply (rule ccorres_return_Skip)
      apply vcg
     apply ccorres_rewrite
     \<comment> \<open>there is no scheduling context associated with ntfnPtr\<close>
     apply (rule ccorres_cond_false)
     apply (rule ccorres_return_Skip)
    apply vcg
   apply (rule ccorres_return_Skip)
  apply (clarsimp simp: from_bool_def)
  apply (frule invs_valid_objs')
  apply safe
     apply (clarsimp simp: obj_at'_def)
    apply (clarsimp simp: valid_ntfn'_def)
   apply (fastforce dest: obj_at_cslift_ntfn simp: typ_heap_simps)
  apply (clarsimp simp: option_to_ptr_def option_to_0_def split: option.splits)
  done

crunch schedContextResume
  for no_0_obj'[wp]: no_0_obj'
  (simp: crunch_simps wp: crunch_wps)

lemma schedContext_bindTCB_ccorres:
  "ccorres dc xfdc
     (tcb_at' tcbPtr and sc_at' scPtr and no_0_obj'
      and pspace_aligned' and pspace_distinct' and pspace_bounded'
      and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s))
     (\<lbrace>\<acute>tcb = tcb_ptr_to_ctcb_ptr tcbPtr\<rbrace> \<inter> \<lbrace>\<acute>sc = Ptr scPtr\<rbrace>) hs
     (schedContextBindTCB scPtr tcbPtr) (Call schedContext_bindTCB_'proc)"
  supply Collect_const[simp del]
  apply (cinit lift: tcb_' sc_')
   apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow)
       apply (rule ccorres_move_c_guard_tcb)+
       apply (rule_tac Q="\<lambda>s tcb'. {s'. (s, s') \<in> rf_sr \<and> ko_at' tcb' tcbPtr s}"
                    in threadSet_ccorres_lemma3[where P=\<top> and P'=\<top>, simplified])
        apply (rule conseqPre, vcg)
        apply clarsimp
        apply (frule (1) obj_at_cslift_tcb)
        apply (fastforce elim!: rf_sr_tcb_update_gen2
                          simp: typ_heap_simps' ctcb_relation_def option_to_ctcb_ptr_def
                                tcb_cte_cases_def cteSizeBits_def)
       apply clarsimp
      apply ceqv
     apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow)
         apply clarsimp
         apply (rule updateSchedContext_ccorres_lemma2[where P="\<top>"])
           apply vcg
          apply fastforce
         apply (clarsimp simp: typ_heap_simps)
         apply (rule_tac sc'="scTcb_C_update (\<lambda>_. tcb_ptr_to_ctcb_ptr tcbPtr) sc'"
                      in rf_sr_sc_update_no_refill_buffer_update2;
                fastforce?)
           apply (clarsimp simp: typ_heap_simps' packed_heap_update_collapse_hrs)
          apply (clarsimp simp: csched_context_relation_def option_to_ctcb_ptr_def)
         apply (fastforce intro: refill_buffer_relation_sc_no_refills_update)
        apply ceqv
       apply (clarsimp simp: ifCondRefillUnblockCheck_def bind_assoc)
       apply (rule ccorres_pre_getObject_sc, rename_tac sc)
       apply (rule ccorres_pre_getCurSc, rename_tac cur_sc)
       apply (rule ccorres_rhs_assoc2)
       apply (rule_tac val="from_bool (scSporadic sc)"
                   and xf'=ret__int_'
                   and R="ko_at' sc scPtr and no_0_obj'"
                   and R'=UNIV
                    in ccorres_symb_exec_r_known_rv)
          apply (rule conseqPre, vcg)
          apply clarsimp
          apply (frule (1) obj_at_cslift_sc)
          apply (clarsimp simp: typ_heap_simps csched_context_relation_def to_bool_def
                         split: if_splits)
         apply ceqv
        apply (rule ccorres_rhs_assoc2)
        apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow)
            apply (clarsimp simp: when_def)
            apply (rule_tac P="scSporadic sc" in ccorres_cases; clarsimp)
             apply ccorres_rewrite
             apply (rule ccorres_rhs_assoc)+
             apply (rule_tac xf'=ret__unsigned_long_'
                         and val="from_bool (0 < scRefillMax sc)"
                         and R="ko_at' sc scPtr and no_0_obj'"
                         and R'="UNIV"
                          in ccorres_symb_exec_r_known_rv)
                apply (rule conseqPre, vcg, clarsimp)
                apply (frule (1) obj_at_cslift_sc)
                apply (clarsimp simp: typ_heap_simps csched_context_relation_def from_bool_def
                                      word_less_nat_alt
                               split: if_splits bool.splits)
               apply ceqv
              apply simp
              apply csymbr
              apply (simp only: if_1_0_0 simp_thms)
              apply (rule_tac R="\<lambda>s. cur_sc = ksCurSc s" in ccorres_cond)
                apply (fastforce dest: rf_sr_ksCurSC)
               apply (ctac add: refill_unblock_check_ccorres)
              apply (rule ccorres_return_Skip)
             apply (vcg exspec=sc_active_modifies)
            apply ccorres_rewrite
            \<comment> \<open>the scheduling context is not both sporadic and active, so we do not perform
               refill_unblock_check\<close>
            apply (rule ccorres_cond_false)
            apply (rule ccorres_return_Skip)
           apply ceqv
          apply (ctac add: schedContext_resume_ccorres)
            apply (ctac add: isSchedulable_ccorres)
              apply (clarsimp simp: when_def)
              apply (rule ccorres_cond[where R=\<top>])
                apply (fastforce simp: to_bool_def)
               apply (ctac add: tcbSchedEnqueue_ccorres)
                 apply (ctac add: rescheduleRequired_ccorres)
                apply wpsimp
               apply (vcg exspec=tcbSchedEnqueue_modifies)
              apply (rule ccorres_return_Skip)
             apply (wpsimp wp: getSchedulable_wp)
            apply (vcg exspec=isSchedulable_modifies)
           apply (wpsimp wp: hoare_drop_imps)
          apply (vcg exspec=schedContext_resume_modifies)
         apply (wpsimp wp: refillUnblockCheck_invs')
        apply (vcg exspec=refill_unblock_check_modifies exspec=sc_sporadic_modifies
                   exspec=sc_active_modifies)
       apply (vcg exspec=sc_sporadic_modifies)
      apply (rule_tac Q'="\<lambda>_ s. no_0_obj' s
                                \<and> pspace_aligned' s \<and> pspace_distinct' s \<and> pspace_bounded' s
                                \<and> weak_sch_act_wf (ksSchedulerAction s) s \<and> tcb_at' tcbPtr s"
                   in hoare_post_imp)
       apply (fastforce split: if_splits)
      apply (wpsimp wp: updateSchedContext_valid_objs'_stTCB_update_Just[simplified]
                wp_del: updateSchedContext_valid_objs')
     apply vcg
    apply wpsimp
   apply vcg
  apply clarsimp
  done

lemma schedContext_bindNtfn_ccorres:
  "ccorres dc xfdc
     (invs' and sc_at' scPtr and ntfn_at' ntfnPtr)
     (\<lbrace>\<acute>ntfn = Ptr ntfnPtr\<rbrace> \<inter> \<lbrace>\<acute>sc = Ptr scPtr\<rbrace>) hs
     (schedContextBindNtfn scPtr ntfnPtr) (Call schedContext_bindNtfn_'proc)"
  apply (cinit lift: ntfn_' sc_')
   apply (rule ccorres_split_nothrow[where r'=dc and xf'=xfdc])
       apply (rule_tac P'="\<lambda>s. ntfn_at' ntfnPtr s \<and> sc_at' scPtr s \<and> pspace_canonical' s"
                   and Q="\<lambda>s ntfn. {s'. (s, s') \<in> rf_sr \<and> ko_at' ntfn ntfnPtr s \<and> sc_at' scPtr s
                                        \<and> pspace_canonical' s}"
                    in updateNotification_ccorres_lemma3[where P=\<top>])
        apply (rule conseqPre, vcg)
        apply clarsimp
        apply (frule (1) obj_at_cslift_ntfn)
        apply (clarsimp simp: typ_heap_simps')
        apply (simp cong: StateSpace.state.fold_congs globals.fold_congs)
        apply (fastforce intro!: rf_sr_notification_update2
                           dest: obj_at'_is_canonical
                           simp: cnotification_relation_def Let_def sign_extend_canonical_address
                          split: ntfnstate.splits)
       apply clarsimp
      apply ceqv
     apply (rule updateSchedContext_ccorres_lemma2[where P="\<top>"])
       apply vcg
      apply fastforce
     apply (clarsimp simp: typ_heap_simps)
     apply (rule rf_sr_sc_update_no_refill_buffer_update2;
            fastforce?)
       apply (fastforce simp: csched_context_relation_def typ_heap_simps')
      apply (clarsimp simp: csched_context_relation_def)
     apply (fastforce intro: refill_buffer_relation_sc_no_refills_update)
    apply wpsimp
   apply vcg
  apply normalise_obj_at'
  apply (frule (1) obj_at_cslift_ntfn)
  apply (fastforce simp: typ_heap_simps)
  done

crunch maybeDonateSc
  for no_0_obj'[wp]: no_0_obj'
  (simp: crunch_simps wp: crunch_wps)

lemma completeSignal_ccorres:
  "ccorres dc xfdc
     (invs' and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s) and tcb_at' thread)
     (\<lbrace>\<acute>tcb = tcb_ptr_to_ctcb_ptr thread\<rbrace> \<inter> \<lbrace>\<acute>ntfnPtr = Ptr ntfnptr\<rbrace>) hs
     (completeSignal ntfnptr thread) (Call completeSignal_'proc)"
  supply if_split[split del]
  apply (cinit lift: tcb_' ntfnPtr_')
   apply (rule_tac P="invs' and tcb_at' thread" in ccorres_gen_asm_state)
   apply clarsimp
   apply (prop_tac "tcb_ptr_to_ctcb_ptr thread \<noteq> NULL")
    apply (clarsimp simp: invs'_def valid_pspace'_def tcb_ptr_to_ctcb_ptr_def objBits_simps')
    apply (drule sum_to_zero)
    apply (clarsimp simp: obj_at'_def ctcb_offset_defs projectKOs is_aligned_def objBits_simps')
   apply clarsimp
   apply csymbr
   apply simp
   apply (rule ccorres_rhs_assoc)+
   apply (rule ccorres_pre_getNotification, rename_tac ntfn)
   apply (rule_tac xf'=ret__unsigned_longlong_'
               and val="case ntfnState ntfn of
                            IdleNtfnState \<Rightarrow> scast NtfnState_Idle
                          | Waiting \<Rightarrow> scast NtfnState_Waiting
                          | Active \<Rightarrow> scast NtfnState_Active"
               and R="ko_at' ntfn ntfnptr"
                in ccorres_symb_exec_r_known_rv_UNIV[where R'=UNIV])
      apply vcg
      apply clarsimp
      apply (erule (1) cmap_relation_ko_atE[OF cmap_relation_ntfn])
      apply (clarsimp simp: cnotification_relation_def Let_def typ_heap_simps
                     split: Structures_H.ntfnstate.splits)
     apply ceqv
    apply wpc
      \<comment> \<open>IdleNtfn case\<close>
      apply (clarsimp simp: NtfnState_Idle_def NtfnState_Active_def)
      apply csymbr
      apply (rule ccorres_cond_false)
      apply (rule ccorres_fail)
     \<comment> \<open>ActiveNtfn case\<close>
     apply (clarsimp, csymbr, rule ccorres_cond_true)
     apply (rule ccorres_rhs_assoc)+
     apply (rule ccorres_rhs_assoc2)
     apply (rule_tac val="the (ntfnMsgIdentifier ntfn)"
                 and xf'=badge___unsigned_long_'
                 and R="ko_at' ntfn ntfnptr and valid_ntfn' ntfn"
                  in ccorres_symb_exec_r_known_rv_UNIV[where R'=UNIV])
        apply (vcg, clarsimp)
        apply (erule (1) cmap_relation_ko_atE[OF cmap_relation_ntfn])
        apply (clarsimp simp: cnotification_relation_def valid_ntfn'_def Let_def typ_heap_simps)
       apply ceqv
      apply (ctac (no_vcg))
       apply (rule ccorres_split_nothrow[where r'=dc and xf'=xfdc])
       apply (rule_tac P'="invs' and ntfn_at' ntfnptr" in updateNotification_ccorres_lemma3[where P=\<top>])
        apply vcg
        apply clarsimp
       apply (frule (1) obj_at_cslift_ntfn)
       apply (simp cong: StateSpace.state.fold_congs globals.fold_congs)
       apply (force intro!: rf_sr_notification_update2
                      simp: cnotification_relation_def Let_def typ_heap_simps
                            notification_state_defs)
          apply ceqv
         apply (ctac add: maybeDonateSchedContext_ccorres)
           apply (rule ccorres_pre_threadGet, rename_tac scOpt)
           apply (rule ccorres_move_c_guard_tcb)
           apply (rule_tac P="scOpt = None" in ccorres_cases)
            apply (rule_tac xf'=ret__unsigned_long_'
                        and val="from_bool False"
                        and R="obj_at' (\<lambda>tcb. tcbSchedContext tcb = scOpt) thread
                               and valid_objs' and no_0_obj'"
                         in ccorres_symb_exec_r_known_rv[where R'=UNIV])
               apply (rule conseqPre, vcg)
               apply clarsimp
               apply (frule (1) obj_at_cslift_tcb)
               apply normalise_obj_at'
               apply (clarsimp simp: ctcb_relation_def typ_heap_simps)
              apply ceqv
             apply ccorres_rewrite
             apply clarsimp
             apply (rule ccorres_return_Skip)
            apply (vcg exspec=sc_sporadic_modifies)
           apply (clarsimp, rename_tac scPtr)
           apply (wpfix add: option.sel)
           apply (rule ccorres_pre_getObject_sc, rename_tac sc)
           apply (rule_tac xf'=ret__unsigned_long_'
                       and val="from_bool (scSporadic sc)"
                       and R="obj_at' (\<lambda>tcb. tcbSchedContext tcb = Some scPtr) thread
                              and ko_at' sc scPtr and valid_objs' and no_0_obj'"
                        in ccorres_symb_exec_r_known_rv[where R'=UNIV])
              apply (rename_tac abs_state)
              apply (rule conseqPre, vcg)
              apply normalise_obj_at'
              apply (frule (1) obj_at_cslift_tcb)
              apply (frule (1) tcb_ko_at_valid_objs_valid_tcb')
              apply (prop_tac "sc_at' scPtr abs_state")
               apply (clarsimp simp: valid_tcb'_def valid_bound_obj'_def)
              apply (frule (1) obj_at_cslift_sc)
              apply (clarsimp simp: ctcb_relation_def typ_heap_simps csched_context_relation_def
                                    to_bool_def
                             split: if_splits)
             apply ceqv
            apply ccorres_rewrite
            apply (rule_tac P= "scSporadic sc" in ccorres_cases)
             apply (clarsimp simp: from_bool_def)
             apply ccorres_rewrite
             apply (clarsimp simp: liftM_def)
             apply (rule ccorres_pre_getNotification, rename_tac notification)
             apply (rule ccorres_pre_getCurSc, rename_tac cur_sc)
             apply (clarsimp simp: when_def)
             apply (rule ccorres_rhs_assoc)
             apply (rule ccorres_rhs_assoc)
             apply (rule_tac xf'=sc_'
                         and val="option_to_ptr (ntfnSc notification)"
                         and R="ko_at' notification ntfnptr"
                          in ccorres_symb_exec_r_known_rv[where R'=UNIV])
                apply (rule conseqPre, vcg)
                apply clarsimp
                apply (frule (1) obj_at_cslift_ntfn)
                apply (clarsimp simp: typ_heap_simps cnotification_relation_def Let_def)
               apply ceqv
              apply (rule ccorres_move_c_guard_tcb)
              apply (rule_tac xf'=ret__int_'
                          and val="from_bool (Some scPtr = ntfnSc notification)"
                          and R="ko_at' notification ntfnptr
                                 and obj_at' (\<lambda>tcb. tcbSchedContext tcb = Some scPtr) thread
                                 and valid_objs' and no_0_obj'"
                           in ccorres_symb_exec_r_known_rv[where R'=UNIV])
                 apply (rename_tac abs_state)
                 apply (rule conseqPre, vcg)
                 apply clarsimp
                 apply (frule (1) obj_at_cslift_tcb)
                 apply normalise_obj_at'
                 apply (frule (1) tcb_ko_at_valid_objs_valid_tcb')
                 apply (prop_tac "sc_at' scPtr abs_state")
                  apply (clarsimp simp: valid_tcb'_def)
                 apply (clarsimp simp: typ_heap_simps ctcb_relation_def from_bool_def
                                 split: bool.splits)
                 apply (case_tac "ntfnSc notification"; force)
                apply ceqv
               apply (rule ccorres_cond_seq)
               apply (rule_tac P="Some scPtr = ntfnSc notification" in ccorres_cases; clarsimp)
                apply ccorres_rewrite
                apply (rule ccorres_move_c_guard_tcb)
                apply (rule_tac xf'=ret__int_'
                            and val="from_bool (scPtr \<noteq> cur_sc)"
                            and R="\<lambda>s. obj_at' (\<lambda>tcb. tcbSchedContext tcb = Some scPtr) thread s
                                       \<and> ksCurSc s = cur_sc \<and> valid_objs' s \<and> no_0_obj' s"
                             in ccorres_symb_exec_r_known_rv[where R'=UNIV])
                   apply (rule conseqPre, vcg)
                   apply normalise_obj_at'
                   apply (frule (1) obj_at_cslift_tcb)
                   apply (frule rf_sr_ksCurSC)
                   apply (clarsimp simp: ctcb_relation_def typ_heap_simps split: if_splits)
                   apply (case_tac "ntfnSc notification"; fastforce)
                  apply ceqv
                 apply (rule ccorres_cond[where R=\<top>])
                   apply fastforce
                  apply (rule ccorres_move_c_guard_tcb)
                  apply (ctac add: refill_unblock_check_ccorres)
                 apply (rule ccorres_return_Skip)
                apply vcg
               apply ccorres_rewrite
               apply (rule ccorres_cond_false)
               apply (rule ccorres_return_Skip)
              apply vcg
             apply (vcg exspec=notification_ptr_get_ntfnSchedContext_modifies)
            apply ccorres_rewrite
            apply (clarsimp simp: when_def)
            apply (rule ccorres_return_Skip)
           apply (vcg exspec=sc_sporadic_modifies)
          apply (rule_tac Q'="\<lambda>_. valid_objs' and no_0_obj'
                                  and pspace_aligned' and pspace_distinct' and pspace_bounded'
                                  and tcb_at' thread"
                       in hoare_post_imp)
           apply (fastforce simp: obj_at'_def)
          apply wpsimp
         apply (vcg exspec=maybeDonateSchedContext_modifies)
        apply (wpsimp wp: setNotification_invs' getNotification_wp simp: updateNotification_def)
       apply (vcg exspec=notification_ptr_set_state_modifies)
      apply (rule_tac Q'="\<lambda>_ s. invs' s \<and> weak_sch_act_wf (ksSchedulerAction s) s
                                \<and> ko_at' ntfn ntfnptr s \<and> tcb_at' thread s"
                   in hoare_post_imp)
       apply (fastforce dest: ntfn_ko_at_valid_objs_valid_ntfn'
                      intro!: if_live_then_nonz_capE'
                        simp: ko_wp_at'_def obj_at'_def live_ntfn'_def live'_def valid_ntfn'_def)
      apply wpsimp
     apply (clarsimp simp: guard_is_UNIV_def RISCV64_H.badgeRegister_def RISCV64.badgeRegister_def
                           C_register_defs option_to_ptr_def option_to_0_def
                    split: if_splits option.splits)
    \<comment> \<open>WaitingNtfn case\<close>
    apply (clarsimp simp: NtfnState_Active_def NtfnState_Waiting_def)
    apply csymbr
    apply (rule ccorres_cond_false)
    apply (rule ccorres_fail)
   apply (clarsimp simp: guard_is_UNIV_def split: if_splits)
  apply (fastforce dest: ntfn_ko_at_valid_objs_valid_ntfn' simp: notification_state_defs)
  done

lemma doNBRecvFailedTransfer_ccorres[corres]:
  "ccorres dc xfdc
            \<top>
            (UNIV \<inter> {s. thread_' s = tcb_ptr_to_ctcb_ptr thread})
            [] (doNBRecvFailedTransfer thread)
            (Call doNBRecvFailedTransfer_'proc)"
  apply (cinit lift: thread_')
   apply (ctac add: setRegister_ccorres)
  by (clarsimp simp: C_register_defs RISCV64_H.badgeRegister_def
                        RISCV64.badgeRegister_def RISCV64.capRegister_def)

lemma st_tcb_at'_ko_at':
  "st_tcb_at' ((=) st) t s = (\<exists>tcb. tcbState tcb = st \<and> ko_at' tcb t s)"
  unfolding pred_tcb_at'_def
  by (auto dest: obj_at_ko_at' elim: obj_at'_weakenE)

lemma maybeReturnSchedContext_ccorres:
  "ccorres dc xfdc
     (valid_objs' and no_0_obj' and pspace_aligned' and pspace_distinct'
      and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s)
      and ntfn_at' ntfnPtr and tcb_at' tcbPtr)
     (\<lbrace>\<acute>ntfnPtr = Ptr ntfnPtr\<rbrace> \<inter> \<lbrace>\<acute>tcb = tcb_ptr_to_ctcb_ptr tcbPtr\<rbrace>) hs
     (maybeReturnSc ntfnPtr tcbPtr) (Call maybeReturnSchedContext_'proc)"
  supply Collect_const[simp del]
  unfolding maybeReturnSc_def
  apply (ccorres_exec_l_pre unfold: liftM_def nested_bind
                            ccorres_exec_l_pre: get_ntfn_sp' threadGet_sp)+
  apply (rename_tac ntfn tscOpt)
  apply (cinit' lift: ntfnPtr_' tcb_')
   apply (rule ccorres_rhs_assoc2)
   apply (rule_tac xf'=sc_'
               and val="option_to_ptr (ntfnSc ntfn)"
               and R="ko_at' ntfn ntfnPtr"
               and R'=UNIV
                in ccorres_symb_exec_r_known_rv)
      apply (rule conseqPre, vcg)
      apply clarsimp
      apply (frule (1) obj_at_cslift_ntfn)
      apply (clarsimp simp: typ_heap_simps cnotification_relation_def Let_def)
     apply ceqv
    apply clarsimp
    apply csymbr
    apply (rule_tac P="ntfnSc ntfn \<noteq> None" in ccorres_cases)
     \<comment> \<open>ntfnPtr is associated with a scheduling context, so we check to see whether that
        scheduling context is the same as the scheduling context associated with tcbPtr\<close>
     apply (rule ccorres_cond_seq)
     apply (rule ccorres_cond_true)
     apply (rule ccorres_move_c_guard_tcb)
     apply (rule_tac xf'=ret__int_'
                 and val="from_bool (ntfnSc ntfn = tscOpt)"
                 and R="ko_at' ntfn ntfnPtr and obj_at' (\<lambda>tcb. tcbSchedContext tcb = tscOpt) tcbPtr
                        and valid_objs' and no_0_obj'"
                 and R'=UNIV
                  in ccorres_symb_exec_r_known_rv)
        apply (rule conseqPre, vcg)
        apply normalise_obj_at'
        apply (rename_tac scPtr tcb)
        apply (frule (1) obj_at_cslift_tcb)
        apply (frule (1) ntfn_ko_at_valid_objs_valid_ntfn')
        apply (prop_tac "sc_at' scPtr s")
         apply (clarsimp simp: valid_ntfn'_def)
        apply (frule (1) obj_at_cslift_sc)
        apply clarsimp
        apply (frule_tac p=scPtr in ko_at'_not_NULL)
         apply fastforce
        apply (clarsimp simp: ctcb_relation_def typ_heap_simps' from_bool_def
                       split: bool.splits)
        apply (metis option_to_ptr_simps option_to_ptr_not_0)
       apply ceqv
      apply (simp add: when_def)
      apply (rule ccorres_cond[where R=\<top>])
        apply fastforce
       apply (rule ccorres_rhs_assoc)
       apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow)
           apply (rule ccorres_move_c_guard_tcb)+
           apply (rule_tac Q="\<lambda>s tcb. {s'. (s, s') \<in> rf_sr \<and> ko_at' tcb tcbPtr s}"
                        in threadSet_ccorres_lemma3[where P=\<top> and P'=\<top>, simplified])
            apply (rule conseqPre, vcg)
            apply clarsimp
            apply (frule (1) obj_at_cslift_tcb[where thread=tcbPtr])
            subgoal
              by (fastforce elim!: rf_sr_tcb_update_gen2
                             simp: typ_heap_simps' ctcb_relation_def option_to_ctcb_ptr_def
                                   tcb_cte_cases_def cteSizeBits_def)
           apply clarsimp
          apply ceqv
         apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow)
             apply (rule ccorres_move_c_guard_sc)
             apply (rule_tac P=\<top> in updateSchedContext_ccorres_lemma2)
               apply vcg
              apply fastforce
             apply clarsimp
             apply (rule_tac sc'="scTcb_C_update (\<lambda>_. NULL) sc'"
                          in rf_sr_sc_update_no_refill_buffer_update2;
                    fastforce?)
               apply (clarsimp simp: typ_heap_simps')
              apply (clarsimp simp: csched_context_relation_def option_to_ctcb_ptr_def)
             apply (fastforce intro: refill_buffer_relation_sc_no_refills_update)
            apply ceqv
           apply (rule ccorres_pre_getCurThread)
           apply (clarsimp, rename_tac cur_thread scPtr)
           apply (rule_tac Q="\<lambda>s. cur_thread = ksCurThread s" and Q'="\<top>" in ccorres_cond_both')
             apply (fastforce dest: rf_sr_ksCurThread)
            apply (ctac add: rescheduleRequired_ccorres)
           apply (rule ccorres_return_Skip)
          apply clarsimp
          apply (drule Some_to_the)
          apply (wpsimp wp: updateSchedContext_valid_objs' hoare_vcg_imp_lift')
         apply vcg
        apply (wpsimp wp: hoare_drop_imps)
       apply vcg
      apply (rule ccorres_return_Skip)
     apply vcg
    apply ccorres_rewrite
    \<comment> \<open>ntfnPtr is not associated with a scheduling context, so we do nothing\<close>
    apply clarsimp
    apply (rule ccorres_cond_false)
    apply (rule ccorres_return_Skip)
   apply (vcg exspec=notification_ptr_get_ntfnSchedContext_modifies)
  apply normalise_obj_at'
  apply (fastforce dest: ntfn_ko_at_valid_objs_valid_ntfn' simp: valid_ntfn'_def)
  done

lemma receiveIPC_block_ccorres_helper:
  "ccorres dc xfdc
     (tcb_at' thread and valid_objs' and no_0_obj' and pspace_canonical'
      and pspace_aligned' and pspace_distinct' and ep_at' epptr and valid_bound_reply' replyOpt
      and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s)
      and K (epptr = epptr && ~~ mask 4) \<comment> \<open>this 4 is coming from thread_state_ptr_set_tsType_spec\<close>
      and K (isEndpointCap cap \<and> ccap_relation cap cap'))
     \<lbrace>option_to_0 replyOpt = ptr_val \<acute>replyPtr\<rbrace> hs
     (setThreadState (thread_state.BlockedOnReceive epptr False replyOpt) thread)
     (Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t tcb_ptr_to_ctcb_ptr thread\<rbrace>
       (CALL thread_state_ptr_set_tsType(Ptr
        &(tcb_ptr_to_ctcb_ptr thread\<rightarrow>[''tcbState_C'']),
        scast ThreadState_BlockedOnReceive));;
      Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t tcb_ptr_to_ctcb_ptr thread\<rbrace>
       (CALL thread_state_ptr_set_blockingObject(Ptr
                     &(tcb_ptr_to_ctcb_ptr thread\<rightarrow>[''tcbState_C'']),
        epptr));;
      Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t tcb_ptr_to_ctcb_ptr thread\<rbrace>
       (CALL thread_state_ptr_set_replyObject(Ptr
                     &(tcb_ptr_to_ctcb_ptr thread\<rightarrow>[''tcbState_C'']),
        ptr_val \<acute>replyPtr));;
      CALL scheduleTCB(tcb_ptr_to_ctcb_ptr thread))"
  unfolding K_def setThreadState_def
  apply (intro ccorres_gen_asm)
  apply (rule ccorres_guard_imp)
    apply (rule_tac P="canonical_address epptr" in ccorres_gen_asm)
    apply (rule ccorres_split_nothrow_novcg)
        apply (rule_tac P'="tcb_at' thread and valid_bound_reply' replyOpt
                            and pspace_aligned' and pspace_canonical'"
                    and R="\<lbrace>option_to_0 replyOpt = ptr_val \<acute>replyPtr\<rbrace>"
                     in threadSet_ccorres_lemma4[where P=\<top>])
         apply vcg
        apply clarsimp
        apply (frule(1) tcb_at_h_t_valid)
        apply (frule h_t_valid_c_guard)
        apply (clarsimp simp: typ_heap_simps' rf_sr_tcb_update_twice cap_get_tag_isCap
                        simp flip: canonical_bit_def)
        apply (erule(1) rf_sr_tcb_update_gen, (simp add: typ_heap_simps)+)
         apply (simp add: tcb_cte_cases_def cteSizeBits_def)
        apply (simp add: ctcb_relation_def cthread_state_relation_def)
        apply (intro conjI impI allI)
         apply (clarsimp simp: canonical_address_sign_extended sign_extended_iff_sign_extend
                               objBits_simps')
        apply (clarsimp simp: option_to_0_def)
        apply (cases replyOpt; clarsimp)
        apply (prop_tac "ptr_val (replyPtr_' s') = ptr_val (replyPtr_' s') && ~~ mask 4")
                                    \<comment> \<open>this 4 is coming from thread_state_ptr_set_replyObject_spec\<close>
         apply (rule is_aligned_neg_mask_weaken[symmetric])
          apply normalise_obj_at'
          apply (force intro!: ko_at_is_aligned' simp: objBits_simps' obj_at'_def)
         apply linarith
        apply clarsimp
        apply (prop_tac "canonical_address (ptr_val (replyPtr_' s'))")
         apply (fastforce dest!: obj_at'_is_canonical)
        apply (clarsimp simp: canonical_address_sign_extended sign_extended_iff_sign_extend)
       apply ceqv
      apply clarsimp
      apply (ctac add: scheduleTCB_ccorres)
     apply wpsimp
    apply (clarsimp simp: guard_is_UNIV_def)
   apply (clarsimp simp: obj_at'_is_canonical)
  apply clarsimp
  done

lemma ep_SendEPState_split:
  "(case epState ep of SendEPState \<Rightarrow> f | _ \<Rightarrow> g) = (if epState ep = SendEPState then f else g)"
  apply (cases ep; clarsimp)
  by (rename_tac state queue; case_tac state; clarsimp split: if_splits)

lemma receiveIPC_ccorres[corres]:
  "ccorres dc xfdc
     (invs' and sch_act_not thread and valid_cap' cap and valid_cap' replyCap
      and K (isEndpointCap cap))
     (\<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr thread\<rbrace>
      \<inter> \<lbrace>ccap_relation cap \<acute>cap\<rbrace>
      \<inter> \<lbrace>\<acute>isBlocking = from_bool isBlocking\<rbrace>
      \<inter> \<lbrace>ccap_relation replyCap \<acute>replyCap\<rbrace>) hs
     (receiveIPC thread cap isBlocking replyCap)
     (Call receiveIPC_'proc)"
  supply Collect_const[simp del]
  unfolding K_def receiveIPC_def
  apply (subst ep_SendEPState_split)
  apply (subst if_swap[where P="epState _ = _"])
  apply (rule ccorres_gen_asm)
  apply (cinit' lift: thread_' cap_' isBlocking_' replyCap_')
   apply (rename_tac replyCap' isBlocking' cap' thread')
   apply (rule ccorres_stateAssert)+
   apply (rule ccorres_assert2)
   apply (rule ccorres_symb_exec_l3, rename_tac replyOpt)
      apply (rule_tac P="(isReplyCap replyCap \<or> isNullCap replyCap)
                         \<and> (isReplyCap replyCap
                            \<longrightarrow> (cap_get_tag replyCap' = signed cap_reply_cap
                                 \<and> capReplyPtr_CL (cap_reply_cap_lift replyCap')
                                   = capReplyPtr replyCap))
                         \<and> replyOpt
                           = (if isNullCap replyCap then None else Some (capReplyPtr replyCap))"
                   in ccorres_gen_asm)
      apply (rule_tac xf'=ret__unsigned_longlong_'
                  and val="capEPPtr cap"
                   in ccorres_symb_exec_r_known_rv[where R=\<top> and R'=UNIV])
         apply vcg
         apply (clarsimp simp: cap_get_tag_isCap isCap_simps)
         apply (frule cap_get_tag_isCap_unfolded_H_cap)
         apply (simp add: cap_endpoint_cap_lift ccap_relation_def cap_to_H_def)
        apply ceqv
       apply csymbr
       apply csymbr
       apply csymbr
       apply (rule ccorres_split_nothrow[where r'=dc and xf'=xfdc])
           \<comment> \<open>when replyCap is in fact a replyCap, if the reply is linked to a TCB that is not
              thread, call cancelIPC on this TCB\<close>
           apply (clarsimp simp: when_def)
           apply (rule_tac Q="valid_bound_reply'
                                (if replyCap = capability.NullCap
                                 then None else Some (capReplyPtr replyCap))"
                        in ccorres_cond_both'[where Q'=\<top>])
             apply (fastforce dest: cap_get_tag_isCap_unfolded_H_cap
                              simp: cap_tag_defs isCap_simps)
            apply (clarsimp simp: liftM_def)
            apply (rule ccorres_pre_getObject_reply, rename_tac reply)
            apply (rule ccorres_rhs_assoc)+
            apply (rule_tac val="capReplyPtr replyCap"
                        and xf'=ret__unsigned_longlong_'
                         in ccorres_symb_exec_r_known_rv[where R=\<top> and R'=UNIV])
               apply (rule conseqPre, vcg)
               apply clarsimp
              apply ceqv
             apply csymbr
             apply (rule ccorres_move_c_guard_reply)
             apply (rule_tac val="option_to_ctcb_ptr (replyTCB reply)"
                         and xf'=reply_tcb_'
                         and R="ko_at' reply (capReplyPtr replyCap) and tcb_at' thread
                                and valid_objs' and no_0_obj'"
                          in ccorres_symb_exec_r_known_rv[where R'=UNIV])
                apply (rule conseqPre, vcg)
                apply normalise_obj_at'
                apply (frule (1) obj_at_cslift_reply)
                apply (clarsimp simp: creply_relation_def typ_heap_simps)
               apply ceqv
              apply (rule_tac Q="tcb_at' thread and valid_bound_tcb' (replyTCB reply)"
                           in ccorres_cond_both'[where Q'=\<top>])
                apply (fastforce dest: tcb_at_not_NULL
                                 simp: option_to_ctcb_ptr_def split: option.splits)
               apply (ctac add: cancelIPC_ccorres)
              apply (rule ccorres_return_Skip)
             apply vcg
            apply (vcg exspec=cap_reply_cap_get_capReplyPtr_modifies)
           apply (rule ccorres_return_Skip)
          apply ceqv
         apply (rule ccorres_stateAssert)
         apply (rule ccorres_pre_getEndpoint)
         apply (rename_tac ep)
         apply (simp only: ccorres_seq_skip)
         apply (rule ccorres_move_c_guard_tcb)
         apply (clarsimp simp: getBoundNotification_def)
         apply (rule ccorres_pre_threadGet, rename_tac ntfnPtrOpt)
         apply (rule ccorres_symb_exec_l3, rename_tac ntfn)
            apply (rule_tac val="option_to_ptr ntfnPtrOpt"
                        and xf'=ntfnPtr_'
                        and R="obj_at' (\<lambda>tcb. tcbBoundNotification tcb = ntfnPtrOpt) thread
                               and valid_objs' and no_0_obj'"
                         in ccorres_symb_exec_r_known_rv[where R'=UNIV])
               apply (rule conseqPre, vcg)
               apply normalise_obj_at'
               apply (frule (1) obj_at_cslift_tcb)
               apply (clarsimp simp: typ_heap_simps ctcb_relation_def)
              apply ceqv
             apply (rule ccorres_rhs_assoc2)
             apply (rule_tac val="from_bool ((\<exists>y. ntfnPtrOpt = Some y) \<and> ntfnState ntfn = Active)"
                         and xf'=ret__int_'
                         and R="\<lambda>s. (ntfnPtrOpt \<noteq> None \<longrightarrow> ko_at' ntfn (the ntfnPtrOpt) s)
                                    \<and> obj_at' (\<lambda>tcb. tcbBoundNotification tcb = ntfnPtrOpt) thread s
                                    \<and> no_0_obj' s"
                          in ccorres_symb_exec_r_known_rv[where R'=UNIV])
                apply (rule conseqPre, vcg)
                apply normalise_obj_at'
                apply (rename_tac tcb, case_tac "tcbBoundNotification tcb"; clarsimp)
                apply (frule (1) obj_at_cslift_ntfn)
                apply (case_tac "ntfnState ntfn";
                       clarsimp simp: typ_heap_simps ctcb_relation_def valid_tcb'_def
                                      option_to_ptr_def option_to_0_def cnotification_relation_def
                                      notification_state_defs Let_def valid_bound_obj'_def)
               apply ceqv
              apply (rule ccorres_cond_both'[where Q=\<top> and Q'=\<top>])
                apply (simp add: Collect_const_mem)
               \<comment> \<open>thread is bound to an active notification; completeSignal\<close>
               apply (ctac add: completeSignal_ccorres)
              \<comment> \<open>thread is not bound to an active notification\<close>
              apply (rule ccorres_rhs_assoc)
              apply (rule ccorres_split_nothrow[where r'=dc and xf'=xfdc])
                  \<comment> \<open>thread is bound to a notification, and this is a blocking recv\<close>
                  apply (clarsimp simp: when_def)
                  apply (rule_tac Q="\<lambda>s. (ntfnPtrOpt \<noteq> None \<longrightarrow> ko_at' ntfn (the ntfnPtrOpt) s)
                                         \<and> no_0_obj' s"
                               in ccorres_cond_both'[where Q'=\<top>])
                    apply (fastforce simp: option_to_ptr_def option_to_0_def split: option.splits)
                   apply (ctac add: maybeReturnSchedContext_ccorres)
                  apply (rule ccorres_return_Skip)
                 apply ceqv
                apply (rule_tac xf'=ret__unsigned_longlong_'
                            and val="epstate_to_C (epState ep)"
                            and R="ko_at' ep (capEPPtr cap)"
                             in ccorres_symb_exec_r_known_rv[where R'=UNIV])
                   apply vcg
                   apply clarsimp
                   apply (frule (1) obj_at_cslift_ep)
                   apply (clarsimp simp: typ_heap_simps cendpoint_relation_def
                                         epstate_to_C_def cendpoint_state_relation_def)
                  apply ceqv
                 apply clarsimp
                 apply (rule_tac A="invs' and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s)
                                    and st_tcb_at' simple' thread
                                    and valid_cap' cap and valid_cap' replyCap
                                    and ko_at' ep (capEPPtr cap)
                                    and valid_bound_reply'
                                          (if replyCap = capability.NullCap
                                           then None else Some (capReplyPtr replyCap))"
                             and A'="\<lbrace>option_to_0
                                        (if replyCap = capability.NullCap
                                         then None else Some (capReplyPtr replyCap))
                                      = ptr_val \<acute>replyPtr\<rbrace>"
                              in ccorres_guard_imp2)
                  apply clarsimp
                  apply (rule ccorres_cond_both'[where Q=\<top> and Q'=\<top>])
                    apply (case_tac "epState ep"; clarsimp simp: epstate_to_C_def endpoint_state_defs)
                   \<comment> \<open>the endpoint state is not Send; receiveIPCBlocked\<close>
                   apply (clarsimp simp: receiveIPCBlocked_def case_bool_If)
                   apply (rule ccorres_cond_both'[where Q=\<top> and Q'=\<top>])
                     apply fastforce
                   \<comment> \<open>Gather all steps related to the update of the thread state, then split them
                       off and use the helper lemma\<close>
                    apply (intro ccorres_rhs_assoc)
                    apply (rule ccorres_rhs_assoc2)
                    apply (rule ccorres_rhs_assoc2)
                    apply (rule ccorres_rhs_assoc2)
                    apply (rule ccorres_split_nothrow)
                        apply (rule receiveIPC_block_ccorres_helper)
                       apply ceqv
                      apply clarsimp
                      apply (rule ccorres_split_nothrow[where r'=dc and xf'=xfdc])
                          apply (clarsimp simp: when_def)
                          apply (rule_tac Q="\<lambda>s. isReplyCap replyCap
                                                 \<longrightarrow> reply_at' (capReplyPtr replyCap) s
                                                 \<and> no_0_obj' s"
                                      and Q'="\<lambda>s. replyPtr_' s
                                                  = option_to_ptr
                                                      (if isNullCap replyCap
                                                       then None else Some (capReplyPtr replyCap))"
                                       in ccorres_cond_both')
                            apply (clarsimp split: if_splits)
                           apply (rule_tac P'="tcb_at' thread"
                                       and R="\<lbrace>\<acute>replyPtr
                                               = option_to_ptr
                                                   (if isNullCap replyCap
                                                    then None else Some (capReplyPtr replyCap))\<rbrace>"
                                        in updateReply_ccorres_lemma4[where P=\<top>])
                            apply vcg
                           apply (frule (1) obj_at_cslift_reply)
                           apply normalise_obj_at'
                           apply (fastforce dest: obj_at'_is_canonical intro!: rf_sr_reply_update2
                                            simp: typ_heap_simps' creply_relation_def
                                                  sign_extend_canonical_address
                                                  option_to_ctcb_ptr_def
                                           split: if_splits)
                          apply (rule ccorres_return_Skip)
                         apply ceqv
                        apply (ctac add: tcbEPAppend_ccorres)
                       apply (wpsimp wp: updateReply_valid_objs')
                      apply vcg
                     apply (rule_tac Q'="\<lambda>_ s. valid_objs' s \<and> no_0_obj' s \<and> pspace_canonical' s
                                               \<and> valid_cap' cap s \<and> valid_cap' replyCap s
                                               \<and> tcb_at' thread s"
                                  in hoare_post_imp)
                      apply (clarsimp split: if_splits)
                      apply normalise_obj_at'
                      apply (frule (1) tcb_ko_at_valid_objs_valid_tcb')
                     subgoal
                       by (force simp: valid_cap'_def valid_reply'_def
                                       isEndpointCap_def isReplyCap_def
                                split: capability.splits)
                     apply wpsimp
                    apply (vcg exspec=scheduleTCB_modifies)
                   apply (ctac add: doNBRecvFailedTransfer_ccorres)
                  \<comment> \<open>the endpoint state is Send\<close>
                  apply (clarsimp simp: epstate_to_C_def)
                  apply ccorres_rewrite
                  apply (intro ccorres_rhs_assoc)
                  apply (repeat 6 csymbr)
                  apply clarsimp
                  apply (rule ccorres_stateAssert)
                  apply (rule ccorres_assert2)
                  apply (rule_tac xf'=queue_'
                              and val="tcb_queue_to_tcb_queue_C (epQueue ep)"
                              and R="ko_at' ep (capEPPtr cap) and valid_objs'"
                               in ccorres_symb_exec_r_known_rv[where R'=UNIV])
                     apply (rule conseqPre, vcg)
                     apply normalise_obj_at'
                     apply (frule (1) obj_at_cslift_ep)
                     apply (fastforce intro!: tcb_queue_C_eq
                                        simp: cendpoint_relation_def ctcb_queue_relation_def
                                              typ_heap_simps ctcb_queue_relation_def
                                              tcb_queue_to_tcb_queue_C_def)
                    apply ceqv
                   apply (rule_tac xf'=sender_'
                               and val="option_to_ctcb_ptr (tcbQueueHead (epQueue ep))"
                               and R="ko_at' ep (capEPPtr cap) and valid_objs'"
                                in ccorres_symb_exec_r_known_rv[where R'=UNIV])
                      apply (rule conseqPre, vcg)
                      apply normalise_obj_at'
                      apply (frule (1) obj_at_cslift_ep)
                      apply (fastforce simp: tcb_queue_to_tcb_queue_C_def)
                     apply ceqv
                    apply (ctac add: tcbEPDequeue_ccorres)
                      apply (rule ccorres_symb_exec_l3, rename_tac senderState)
                         apply (rule ccorres_assert2)
                         apply (rule ccorres_move_c_guard_tcb)
                         apply (rule ccorres_rhs_assoc2)
                         apply (rule_tac val="blockingIPCBadge senderState"
                                     and xf'=badge___unsigned_long_'
                                     and R="\<lambda>s. \<exists>tcb. ko_at' tcb (the (tcbQueueHead (epQueue ep))) s
                                                      \<and> tcbState tcb = senderState"
                                      in ccorres_symb_exec_r_known_rv[where R'=UNIV])
                            apply (rule conseqPre, vcg)
                            apply normalise_obj_at'
                            apply (frule (1) obj_at_cslift_tcb)
                            apply (clarsimp simp: ctcb_relation_def typ_heap_simps
                                                  cthread_state_relation_def word_size
                                                  isSend_def thread_state_lift_def
                                                  tcbQueueEmpty_def option_to_ctcb_ptr_def
                                           split: Structures_H.thread_state.splits)
                           apply ceqv
                          apply (simp split del: if_split)
                          apply (rule ccorres_move_c_guard_tcb)
                          apply (rule ccorres_rhs_assoc2)
                          apply (rule_tac val="from_bool (blockingIPCCanGrant senderState)"
                                      and xf'=canGrant_'
                                      and R="\<lambda>s. \<exists>tcb. ko_at' tcb  (the (tcbQueueHead (epQueue ep))) s
                                                       \<and> tcbState tcb = senderState"
                                       in ccorres_symb_exec_r_known_rv [where R'=UNIV])
                             apply (rule conseqPre, vcg)
                             apply normalise_obj_at'
                             apply (frule (1) obj_at_cslift_tcb)
                             apply (clarsimp simp: ctcb_relation_def typ_heap_simps
                                                   cthread_state_relation_def word_size
                                                   isSend_def thread_state_lift_def
                                                   tcbQueueEmpty_def option_to_ctcb_ptr_def
                                            split: Structures_H.thread_state.splits)
                            apply ceqv
                           apply (rule ccorres_rhs_assoc2)
                           apply (rule_tac xf'=canGrantReply_'
                                       and val="from_bool (blockingIPCCanGrantReply senderState)"
                                       and R="st_tcb_at' ((=) senderState)
                                                         (the (tcbQueueHead (epQueue ep)))"
                                        in ccorres_symb_exec_r_known_rv[where R'=UNIV])
                              apply (clarsimp, rule conseqPre, vcg)
                              apply (fastforce simp: pred_tcb_at'_def tcb_at_h_t_valid
                                                     typ_heap_simps' tcbQueueEmpty_def
                                                     option_to_ctcb_ptr_def
                                               dest: obj_at_cslift_tcb
                                                     ctcb_relation_blockingIPCCanGrantReplyD)
                             apply ceqv
                            apply (ctac add: doIPCTransfer_ccorres)
                              apply (rule ccorres_move_c_guard_tcb)
                              apply (rule ccorres_rhs_assoc2)
                              apply (rule_tac val="from_bool (blockingIPCIsCall senderState)"
                                          and xf'=do_call_'
                                          and R="\<lambda>s. \<exists>tcb. ko_at' tcb (the (tcbQueueHead (epQueue ep))) s
                                                           \<and> tcbState tcb = senderState"
                                           in ccorres_symb_exec_r_known_rv[where R'=UNIV])
                                 apply (rule conseqPre, vcg)
                                 apply normalise_obj_at'
                                 apply (frule (1) obj_at_cslift_tcb)
                                 apply (clarsimp simp: ctcb_relation_def typ_heap_simps
                                                       cthread_state_relation_def word_size
                                                       isSend_def thread_state_lift_def
                                                       option_to_ctcb_ptr_def tcbQueueEmpty_def
                                                split: Structures_H.thread_state.splits)
                                apply ceqv
                               apply (rule ccorres_pre_threadGet, rename_tac scOpt)
                               apply (rule ccorres_move_c_guard_tcb)
                               apply (rule ccorres_rhs_assoc2)
                               apply (rule ccorres_split_nothrow[where r'=dc and xf'=xfdc])
                                   \<comment> \<open>ifCondRefillUnblockCheck\<close>
                                   apply (clarsimp simp: ifCondRefillUnblockCheck_def when_def)
                                   apply (rule ccorres_if_lhs)
                                   apply (clarsimp simp: bind_assoc, rename_tac scPtr)
                                    apply wpfix
                                    apply (rule ccorres_pre_getObject_sc, rename_tac sc)
                                    apply (rule ccorres_pre_getCurSc, rename_tac cur_sc)
                                    apply (rule_tac xf'=ret__unsigned_long_'
                                                and val="from_bool (scSporadic sc)"
                                                and R="\<lambda>s. obj_at' (\<lambda>tcb. tcbSchedContext tcb = Some scPtr)
                                                                   (the (tcbQueueHead (epQueue ep))) s
                                                           \<and> ko_at' sc scPtr s \<and> no_0_obj' s
                                                           \<and> tcbQueueHead (epQueue ep) \<noteq> None"
                                                 in ccorres_symb_exec_r_known_rv[where R'=UNIV])
                                       apply (rule conseqPre, vcg)
                                       apply normalise_obj_at'
                                       apply (frule (1) obj_at_cslift_tcb)
                                       apply (frule (1) obj_at_cslift_sc)
                                       apply (clarsimp simp: typ_heap_simps ctcb_relation_def
                                                             csched_context_relation_def to_bool_def
                                                             option_to_ctcb_ptr_def
                                                      split: if_splits)
                                      apply ceqv
                                     apply (rule ccorres_cond_both'[where Q=\<top> and Q'=\<top>])
                                       apply fastforce
                                      apply (rule ccorres_move_c_guard_tcb)
                                      apply (rule_tac Q="\<lambda>s. obj_at' (\<lambda>tcb. tcbSchedContext tcb = Some scPtr)
                                                                     (the (tcbQueueHead (epQueue ep))) s
                                                             \<and> ksCurSc s = cur_sc
                                                             \<and> valid_objs' s \<and> no_0_obj' s
                                                             \<and> tcbQueueHead (epQueue ep) \<noteq> None"
                                                   in ccorres_cond_both'[where Q'=\<top>])
                                        apply clarsimp
                                        apply (frule (1) obj_at_cslift_tcb)
                                        apply clarsimp
                                        apply (frule (1) tcb_ko_at_valid_objs_valid_tcb')
                                        apply (frule rf_sr_ksCurSC)
                                        apply (clarsimp simp: option_to_ctcb_ptr_def
                                                              ctcb_relation_def typ_heap_simps
                                                              valid_tcb'_def)
                                        apply (metis ptr_val_def)
                                       apply (rule ccorres_move_c_guard_tcb)
                                       apply (ctac add: refill_unblock_check_ccorres)
                                      apply (rule ccorres_return_Skip)
                                     apply (rule ccorres_return_Skip)
                                    apply (vcg exspec=sc_sporadic_modifies)
                                   apply (rule_tac xf'=ret__unsigned_long_'
                                               and val="from_bool False"
                                               and R="\<lambda>s. obj_at' (\<lambda>tcb. tcbSchedContext tcb = None)
                                                                  (the (tcbQueueHead (epQueue ep))) s
                                                          \<and> tcbQueueHead (epQueue ep) \<noteq> None"
                                                in ccorres_symb_exec_r_known_rv[where R'=UNIV])
                                      apply (rule conseqPre, vcg)
                                      apply normalise_obj_at'
                                      apply (frule (1) obj_at_cslift_tcb)
                                      apply (clarsimp simp: ctcb_relation_def option_to_ctcb_ptr_def
                                                            typ_heap_simps
                                                     split: if_splits)
                                     apply ceqv
                                    apply ccorres_rewrite
                                    apply (rule ccorres_return_Skip)
                                   apply clarsimp
                                   apply (vcg exspec=sc_sporadic_modifies)
                                  apply ceqv
                                 apply (rule ccorres_symb_exec_l3, rename_tac fault)
                                    apply (rule ccorres_rhs_assoc2)
                                    apply (rule_tac val="from_bool (blockingIPCIsCall senderState
                                                                    \<or> (\<exists>ft. fault = Some ft))"
                                                and xf'=ret__int_'
                                                and R="\<lambda>s. \<exists>tcb. ko_at' tcb
                                                                        (the (tcbQueueHead (epQueue ep))) s
                                                                 \<and> tcbFault tcb = fault
                                                           \<and> no_0_obj' s
                                                           \<and> tcbQueueHead (epQueue ep) \<noteq> None"
                                                 in ccorres_symb_exec_r_known_rv[where R'=UNIV])
                                       apply (rule conseqPre, vcg)
                                       apply normalise_obj_at'
                                       apply (frule (1) obj_at_cslift_tcb)
                                       subgoal
                                         by (fastforce simp: ctcb_relation_def typ_heap_simps
                                                             option_to_ctcb_ptr_def cfault_rel_def
                                                             seL4_Fault_lift_def Let_def
                                                      split: if_split_asm option.split)
                                      apply ceqv
                                     apply (rule ccorres_cond_both'[where Q=\<top> and Q'=\<top>])
                                       apply force
                                      \<comment> \<open>is call and there is a fault\<close>
                                      apply (rule_tac Q="\<lambda>s. isReplyCap replyCap
                                                             \<longrightarrow> reply_at' (capReplyPtr replyCap) s
                                                             \<and> no_0_obj' s"
                                                  and Q'="\<lambda>s. replyPtr_' s
                                                              = option_to_ptr
                                                                  (if isNullCap replyCap
                                                                   then None
                                                                   else Some (capReplyPtr replyCap))"
                                                   in ccorres_cond_both')
                                        apply (clarsimp split: if_splits bool.splits)
                                        apply fastforce
                                       apply (rule ccorres_symb_exec_l3, rename_tac senderSc)
                                          apply clarsimp
                                          apply (rule ccorres_rhs_assoc)+
                                          apply (rule ccorres_move_c_guard_tcb)
                                          apply (rule ccorres_rhs_assoc2)
                                          apply (rule ccorres_rhs_assoc2)
                                          apply (rule_tac
                                                       val="from_bool
                                                              ((\<exists>sc_ptr. senderSc = Some sc_ptr)
                                                               \<and> (fault = None
                                                                  \<or> \<not> isTimeoutFault (the fault)))"
                                                   and xf'=canDonate___unsigned_long_'
                                                   and R="\<lambda>s. obj_at' (\<lambda>tcb. tcbSchedContext tcb
                                                                             = senderSc)
                                                                      (the (tcbQueueHead (epQueue ep))) s
                                                              \<and> obj_at' (\<lambda>tcb. tcbFault tcb = fault)
                                                                        (the (tcbQueueHead (epQueue ep))) s
                                                              \<and> valid_objs' s \<and> no_0_obj' s
                                                              \<and> tcbQueueHead (epQueue ep) \<noteq> None"
                                                    in ccorres_symb_exec_r_known_rv[where R'=UNIV])
                                             apply (rule conseqPre, vcg)
                                             apply normalise_obj_at'
                                             apply (frule (1) obj_at_cslift_tcb)
                                             apply (rename_tac tcb)
                                             apply (frule (1) tcb_ko_at_valid_objs_valid_tcb')
                                             apply (clarsimp simp: option_to_ctcb_ptr_def)
                                             apply (intro context_conjI impI allI)
                                               apply (fastforce simp: typ_heap_simps)
                                              apply (case_tac "tcbSchedContext tcb")
                                               apply (fastforce simp: ctcb_relation_def typ_heap_simps)
                                              apply (clarsimp simp: ctcb_relation_def typ_heap_simps
                                                                    from_bool_def isTimeoutFault_def
                                                                    seL4_Faults is_cap_fault_def
                                                                    cfault_rel_def
                                                                    seL4_Fault_lift_def Let_def
                                                             split: if_splits bool.splits)
                                              apply (intro context_conjI impI; clarsimp)
                                             apply (case_tac "tcbSchedContext tcb"; clarsimp)
                                             apply (clarsimp simp: ctcb_relation_def typ_heap_simps
                                                                   valid_tcb'_def)
                                            apply ceqv
                                           apply (ctac add: reply_push_ccorres)
                                          apply vcg
                                         apply wpsimp
                                        apply (wpsimp wp: threadGet_wp)
                                       apply wpsimp
                                      apply (ctac add: setThreadState_ccorres)
                                     apply (ctac add: setThreadState_ccorres)
                                       apply clarsimp
                                       apply (ctac add: possibleSwitchTo_ccorres)
                                      apply wpsimp
                                     apply (vcg exspec=setThreadState_modifies)
                                    apply vcg
                                   apply wpsimp
                                  apply (wpsimp wp: threadGet_wp)
                                 apply wpsimp
                                apply (rule_tac Q'="\<lambda>_ s. tcbQueueHead (epQueue ep) \<noteq> None
                                                          \<and> tcb_at' (the (tcbQueueHead (epQueue ep))) s
                                                          \<and> tcb_at' thread s
                                                          \<and> valid_objs' s \<and> no_0_obj' s
                                                          \<and> pspace_aligned' s \<and> pspace_distinct' s
                                                          \<and> pspace_canonical' s
                                                          \<and> ksCurDomain s \<le> maxDomain
                                                          \<and> weak_sch_act_wf (ksSchedulerAction s) s
                                                          \<and> valid_cap' replyCap s"
                                             in hoare_post_imp)
                                 subgoal
                                   by (cases replyCap;
                                       force simp: valid_cap'_def obj_at'_def isReplyCap_def)
                                apply wpsimp
                               apply (vcg exspec=refill_unblock_check_modifies
                                          exspec=sc_sporadic_modifies
                                          exspec=sc_active_modifies)
                              apply (vcg exspec=thread_state_ptr_get_blockingIPCIsCall_modifies)
                             apply (rule_tac Q'="\<lambda>_ s. tcbQueueHead (epQueue ep) \<noteq> None
                                                       \<and> tcb_at' (the (tcbQueueHead (epQueue ep))) s
                                                       \<and> st_tcb_at' ((=) senderState)
                                                                    (the (tcbQueueHead (epQueue ep))) s
                                                       \<and> tcb_at' thread s
                                                       \<and> valid_objs' s \<and> no_0_obj' s
                                                       \<and> pspace_aligned' s \<and> pspace_distinct' s
                                                       \<and> pspace_bounded' s \<and> pspace_canonical' s
                                                       \<and> ksCurDomain s \<le> maxDomain
                                                       \<and> weak_sch_act_wf (ksSchedulerAction s) s
                                                       \<and> valid_cap' replyCap s"
                                          in hoare_post_imp)
                              apply (clarsimp simp: pred_tcb_at'_def obj_at'_def split: if_split)
                             apply wpsimp
                            apply (vcg exspec=doIPCTransfer_modifies)
                           apply (vcg exspec=thread_state_ptr_get_blockingIPCCanGrantReply_modifies)
                          apply (vcg exspec=thread_state_ptr_get_blockingIPCCanGrant_modifies)
                         apply (vcg exspec=thread_state_ptr_get_blockingIPCBadge_modifies)
                        apply wpsimp
                       apply (wpsimp wp: gts_wp')
                      apply wpsimp
                     apply (rule_tac Q'="\<lambda>_ s. tcbQueueHead (epQueue ep) \<noteq> None
                                               \<and> tcb_at' (the (tcbQueueHead (epQueue ep))) s
                                               \<and> st_tcb_at' simple' thread s
                                               \<and> invs' s \<and> weak_sch_act_wf (ksSchedulerAction s) s
                                               \<and> valid_cap' cap s \<and> isEndpointCap cap
                                               \<and> valid_cap' replyCap s"
                                  in hoare_post_imp)
                      apply clarsimp
                      apply (intro conjI impI allI; fastforce?)
                        apply (clarsimp simp: st_tcb_at'_def obj_at'_def isSend_def)
                        apply (rename_tac tcb, case_tac "tcbState tcb"; clarsimp)
                       apply (cases cap; clarsimp simp: valid_cap'_def isEndpointCap_def)
                      apply (clarsimp simp: st_tcb_at'_def obj_at'_def isSend_def)
                     apply wpsimp
                    apply (vcg exspec=tcbEPDequeue_modifies)
                   apply vcg
                  apply (vcg exspec=ep_ptr_get_queue_modifies)
                 apply clarsimp
                 apply (clarsimp simp: option_to_ctcb_ptr_def ctcb_relation_def typ_heap_simps
                                split: option.splits)
                 apply (prop_tac "isReplyCap replyCap
                                  \<longrightarrow> replyPtr_' s' = reply_Ptr (capReplyPtr replyCap)")
                  apply (clarsimp simp: isReplyCap_def split: if_splits)
                 apply (prop_tac "isReplyCap replyCap
                                  \<longrightarrow> replyPtr_' s'
                                      = option_to_ptr (if replyCap = NullCap
                                                       then None else Some (capReplyPtr replyCap))")
                  apply (clarsimp simp: isReplyCap_def option_to_ptr_def split: if_splits)
                 apply (prop_tac "isNullCap replyCap \<longrightarrow> replyPtr_' s' = NULL")
                  apply (force simp: NULL_ptr_val)
                 apply (clarsimp simp: endpoint_state_defs)
                 apply (cases "isReplyCap replyCap"; clarsimp)
                  apply (intro conjI impI allI;
                         force simp: typ_heap_simps tcbQueueEmpty_def obj_at'_def objBits_simps'
                                     epstate_to_C_def cendpoint_state_relation_def endpoint_state_defs)
                 apply (intro conjI impI allI;
                        force simp: typ_heap_simps tcbQueueEmpty_def obj_at'_def objBits_simps'
                                    epstate_to_C_def cendpoint_state_relation_def endpoint_state_defs)
                apply (vcg exspec=endpoint_ptr_get_state_modifies)
               apply (wpsimp wp: maybeReturnSc_invs')
              apply (vcg exspec=maybeReturnSchedContext_modifies)
             apply (vcg exspec=notification_ptr_get_state_modifies)
            apply (vcg exspec=notification_ptr_get_state_modifies)
           apply (wpsimp wp: gbn_wp')
          apply (wpsimp wp: getNotification_wp)
         apply wpsimp
        apply (rule_tac Q'="\<lambda>_ s. invs' s \<and> weak_sch_act_wf (ksSchedulerAction s) s
                                  \<and> st_tcb_at' simple' thread s
                                  \<and> valid_cap' cap s \<and> valid_cap' replyCap s
                                  \<and> valid_bound_reply'
                                      (if replyCap = capability.NullCap
                                       then None else Some (capReplyPtr replyCap)) s"
                     in hoare_post_imp)
         apply clarsimp
         apply (intro conjI; force simp: obj_at'_def)
        apply (clarsimp simp: when_def)
        apply (wpsimp wp: cancelIPC_st_tcb_at'_different_thread)
       apply (vcg exspec=cancelIPC_modifies)
      apply (vcg exspec=cap_endpoint_cap_get_capEPPtr_modifies)
     apply wpsimp
    apply wpsimp
   apply wpsimp
  apply clarsimp
  apply (prop_tac "isReplyCap replyCap \<longleftrightarrow> cap_get_tag replyCapa = signed cap_reply_cap")
   apply (fastforce dest: cap_get_tag_isCap(10))
  apply (prop_tac "isReplyCap replyCap
                   \<longrightarrow> (cap_get_tag replyCapa = signed cap_reply_cap
                        \<and> capReplyPtr_CL (cap_reply_cap_lift replyCapa)
                           = capReplyPtr replyCap)")
   apply clarsimp
   apply (frule (1) ccap_relation_reply_helpers[where cap=replyCap])
   apply fastforce
  apply (prop_tac "st_tcb_at' active' thread s \<longrightarrow> st_tcb_at' simple' thread s")
   apply (fastforce elim: pred_tcb'_weakenE)
  by (clarsimp simp: isCap_simps option_to_ctcb_ptr_def option_to_0_def option_to_ptr_def
              split: if_splits option.splits,
      fastforce dest: reply_ko_at_valid_objs_valid_reply'[OF _ invs_valid_objs']
                simp: valid_reply'_def valid_cap'_def)

lemma ntfn_set_active_ccorres:
  "ccorres dc xfdc
     (invs' and ntfn_at' ntfnPtr)
     (\<lbrace>\<acute>ntfnPtr = ntfn_Ptr ntfnPtr\<rbrace> \<inter> \<lbrace>\<acute>badge___unsigned_long = badge\<rbrace>) hs
     (ntfnSetActive ntfnPtr badge) (Call ntfn_set_active_'proc)"
  apply (cinit lift: ntfnPtr_' badge___unsigned_long_')
   apply (rule_tac P'="ntfn_at' ntfnPtr"
               and Q="\<lambda>s ntfn. {s'. (s, s') \<in> rf_sr \<and> ko_at' ntfn ntfnPtr s}"
                in updateNotification_ccorres_lemma3[where P=\<top>])
    apply (rule conseqPre, vcg)
    apply clarsimp
    apply (frule (1) obj_at_cslift_ntfn)
    apply (clarsimp simp: typ_heap_simps')
    apply (simp cong: StateSpace.state.fold_congs globals.fold_congs)
    apply (fastforce intro!: rf_sr_notification_update2
                       simp: cnotification_relation_def Let_def
                             notification_state_defs mask_def packed_heap_update_collapse_hrs)
   apply clarsimp
  apply fastforce
  done

lemma sts_runnable:
  "\<lbrace>if t \<noteq> dest then st_tcb_at' runnable' t else st_tcb_at' \<top> t\<rbrace>
  setThreadState Structures_H.thread_state.Running dest
          \<lbrace>\<lambda>rv. st_tcb_at' runnable' t\<rbrace>"
  apply (rule hoare_pre)
  apply (wp sts_st_tcb_at'_cases)
  apply auto
  done

lemma st_tcb'_iff:
  "st_tcb_at' \<top> t = tcb_at' t"
  by (auto simp:st_tcb_at'_def)

crunch maybeDonateSc, tcbNTFNAppend
  for weak_sch_act_wf[wp]: "\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s"
  (simp: crunch_simps wp: crunch_wps)

lemma sendSignal_ccorres[corres]:
  "ccorres dc xfdc
     (invs' and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s))
     (\<lbrace>\<acute>ntfnPtr = Ptr ntfnPtr\<rbrace> \<inter> \<lbrace>\<acute>badge___unsigned_long = badge\<rbrace>) hs
     (sendSignal ntfnPtr badge) (Call sendSignal_'proc)"
  supply Collect_const[simp del]
  unfolding sendSignal_def
  apply (ccorres_exec_l_pre ccorres_exec_l_pre: get_ntfn_sp')+
  apply (rename_tac ntfn)
  apply (cinit' lift: ntfnPtr_' badge___unsigned_long_')
   apply (rule_tac xf'=ret__unsigned_longlong_'
               and val="case ntfnState ntfn of
                            IdleNtfnState \<Rightarrow> scast NtfnState_Idle
                          | Waiting \<Rightarrow> scast NtfnState_Waiting
                          | Active \<Rightarrow> scast NtfnState_Active"
               and R="ko_at' ntfn ntfnPtr"
                in ccorres_symb_exec_r_known_rv_UNIV[where R'=UNIV])
      apply (vcg, clarsimp)
      apply (erule (1) cmap_relation_ko_atE[OF cmap_relation_ntfn])
      apply (clarsimp simp: cnotification_relation_def Let_def typ_heap_simps
                     split: ntfnstate.splits)
     apply ceqv
    apply (rule_tac P="ntfnBoundTCB ntfn \<noteq> None
                       \<longrightarrow> option_to_ctcb_ptr (ntfnBoundTCB ntfn) \<noteq> NULL"
                 in ccorres_gen_asm)
    apply wpc
      \<comment> \<open>IdleNtfnState case\<close>
      apply (rule ccorres_cond_true)
      apply (rule ccorres_rhs_assoc)+
      apply (rule_tac xf'=ret__unsigned_longlong_'
                  and val="ptr_val (option_to_ctcb_ptr (ntfnBoundTCB ntfn))"
                  and R="ko_at' ntfn ntfnPtr"
                   in ccorres_symb_exec_r_known_rv_UNIV[where R'=UNIV])
         apply (rule conseqPre, vcg)
         apply clarsimp
         apply (erule (1) cmap_relation_ko_atE [OF cmap_relation_ntfn])
         apply (clarsimp simp: cnotification_relation_def Let_def typ_heap_simps
                        split: ntfnstate.splits)
        apply ceqv
       apply csymbr
       apply wpc
        apply (simp add: option_to_ctcb_ptr_def split del: if_split)
        apply (rule ccorres_cond_false)
        apply (ctac add: ntfn_set_active_ccorres)
       apply (rename_tac tcbPtr)
       apply (rule ccorres_cond_true)
       apply (rule getThreadState_ccorres_foo, rename_tac thread_state)
       apply (rule ccorres_Guard_Seq)
       apply csymbr
       apply (rule ccorres_abstract_cleanup)
       apply (rule_tac P="(ret__unsigned_longlong = scast ThreadState_BlockedOnReceive)
                          = receiveBlocked thread_state"
                    in ccorres_gen_asm2)
       apply (rule ccorres_cond[where R=\<top>])
         apply (simp add: Collect_const_mem)
        apply (rule ccorres_rhs_assoc)+
        apply simp
        apply (ctac (no_vcg) add: cancelIPC_ccorres)
         apply (ctac (no_vcg) add: setThreadState_ccorres)
          apply (ctac (no_vcg) add: setRegister_ccorres)
           apply (ctac (no_vcg) add: maybeDonateSchedContext_ccorres)
            apply (ctac (no_vcg) add: isSchedulable_ccorres)
             apply (rule ccorres_split_nothrow[where r'=dc and xf'=xfdc])
                 apply (clarsimp simp: when_def)
                 apply (rule ccorres_cond[where R=\<top>])
                   apply (fastforce simp: to_bool_def)
                  apply (ctac (no_vcg) add: possibleSwitchTo_ccorres)
                 apply (rule ccorres_return_Skip)
                apply ceqv
               apply (clarsimp simp: ifCondRefillUnblockCheck_def)
               apply (rule ccorres_pre_threadGet)
               apply (rule ccorres_move_c_guard_tcb)
               apply (clarsimp simp: when_def)
               apply (rule ccorres_if_lhs)
                apply (clarsimp simp: bind_assoc, rename_tac scPtr)
                apply wpfix
                apply (rule ccorres_pre_getObject_sc, rename_tac sc)
                apply (rule ccorres_pre_getCurSc, rename_tac cur_sc)
                apply (rule_tac xf'="ret__unsigned_long_'"
                            and val="from_bool (scSporadic sc)"
                            and R="obj_at' (\<lambda>tcb. tcbSchedContext tcb = Some scPtr) tcbPtr
                                   and ko_at' sc scPtr and no_0_obj'"
                             in ccorres_symb_exec_r_known_rv[where R'=UNIV])
                   apply (rule conseqPre, vcg)
                   apply normalise_obj_at'
                   apply (frule (1) obj_at_cslift_tcb)
                   apply (frule (1) obj_at_cslift_sc)
                   apply (clarsimp simp: typ_heap_simps ctcb_relation_def
                                         csched_context_relation_def to_bool_def
                                         option_to_ctcb_ptr_def
                                  split: if_splits)
                  apply ceqv
                 apply (rule_tac P="scSporadic sc" in ccorres_cases; clarsimp)
                  apply ccorres_rewrite
                  apply (clarsimp simp: option_to_ctcb_ptr_def)
                  apply (rule ccorres_move_c_guard_tcb)
                  apply (rule_tac Q="\<lambda>s. cur_sc = ksCurSc s
                                         \<and> obj_at' (\<lambda>tcb. tcbSchedContext tcb = Some scPtr) tcbPtr s"
                               in ccorres_cond_both'[where Q'=\<top>])
                    apply clarsimp
                    apply (frule (1) obj_at_cslift_tcb)
                    apply (fastforce dest!: rf_sr_ksCurSC simp: typ_heap_simps' ctcb_relation_def)
                   apply (rule ccorres_move_c_guard_tcb)
                   apply (ctac add: refill_unblock_check_ccorres)
                  apply (rule ccorres_return_Skip)
                 apply ccorres_rewrite
                 apply (rule ccorres_return_Skip)
                apply (vcg exspec=sc_sporadic_modifies)
               apply (rule_tac xf'="ret__unsigned_long_'"
                           and val="from_bool False"
                           and R="obj_at' (\<lambda>tcb. tcbSchedContext tcb = None) tcbPtr and no_0_obj'"
                            in ccorres_symb_exec_r_known_rv[where R'=UNIV])
                  apply (rule conseqPre, vcg)
                  apply normalise_obj_at'
                  apply (frule (1) obj_at_cslift_tcb)
                  apply (clarsimp simp: typ_heap_simps ctcb_relation_def option_to_ctcb_ptr_def
                                 split: if_splits)
                 apply ceqv
                apply ccorres_rewrite
                apply (rule ccorres_return_Skip)
               apply (vcg exspec=sc_sporadic_modifies)
              apply (rule_tac Q'="\<lambda>_. invs'" in hoare_post_imp)
               apply (fastforce simp: obj_at'_def)
              apply wpsimp
             apply (vcg exspec=possibleSwitchTo_modifies)
            apply (wpsimp wp: getSchedulable_wp)
           apply (rule_tac Q'="\<lambda>_. invs' and tcb_at' tcbPtr
                                   and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s)"
                        in hoare_post_imp)
            apply fastforce
           apply (wpsimp wp: maybeDonateSc_invs')
          apply wpsimp
         apply (wpsimp wp: setThreadState_Running_invs')
        apply ((wpsimp wp: cancelIPC_receiveBlocked_not_sched_linked[
                             simplified, THEN hoare_conjD1[simplified pred_conj_def]]
                           cancelIPC_receiveBlocked_not_sched_linked[
                             simplified, THEN hoare_conjD2[simplified pred_conj_def]]
                           cancelIPC_st_tcb_at'
                | strengthen invs'_implies)+)[1]
       apply (ctac add: ntfn_set_active_ccorres)
      apply (clarsimp simp: guard_is_UNIV_def option_to_ctcb_ptr_def
                            RISCV64_H.badgeRegister_def C_register_defs
                            RISCV64.badgeRegister_def RISCV64.capRegister_def less_mask_eq)
      apply (case_tac ts;
             simp add: receiveBlocked_def typ_heap_simps cthread_state_relation_def
                       ThreadState_defs;
             fastforce simp: typ_heap_simps ctcb_relation_def)
     \<comment> \<open>Active case\<close>
     apply (rule ccorres_cond_false)
     apply (rule ccorres_cond_false)
     apply (rule ccorres_cond_true)
     apply clarsimp
     apply (rule_tac P'="ko_at' ntfn ntfnPtr and valid_objs'"
                 and Q="\<lambda>s ntfn'. {s'. (s, s') \<in> rf_sr \<and> ko_at' ntfn' ntfnPtr s
                                       \<and> ko_at' ntfn ntfnPtr s \<and> valid_objs' s}"
                  in updateNotification_ccorres_lemma3[where P=\<top>])
      apply (rule conseqPre, vcg)
      apply clarsimp
      apply (frule (1) obj_at_cslift_ntfn)
      apply (frule (1) ntfn_ko_at_valid_objs_valid_ntfn')
      apply (clarsimp simp: typ_heap_simps')
      apply normalise_obj_at'
      apply (simp cong: StateSpace.state.fold_congs globals.fold_congs)
      apply (fastforce intro!: rf_sr_notification_update2
                         simp: cnotification_relation_def Let_def
                               notification_state_defs mask_def packed_heap_update_collapse_hrs
                               word_bw_comms valid_ntfn'_def)
     apply clarsimp
    \<comment> \<open>Waiting case\<close>
    apply (rule ccorres_cond_false)
    apply (rule ccorres_cond_true)
    apply clarsimp
    apply (rule ccorres_assert2)
    apply (rule ccorres_symb_exec_l3)
       apply (rule ccorres_assert2)
       apply (rule ccorres_rhs_assoc)+
       apply csymbr
       apply csymbr
       apply (rule_tac xf'=ntfn_queue_'
                   and val="tcb_queue_to_tcb_queue_C (ntfnQueue ntfn)"
                   and R="ko_at' ntfn ntfnPtr and valid_objs'"
                    in ccorres_symb_exec_r_known_rv[where R'=UNIV])
          apply (rule conseqPre, vcg)
          apply normalise_obj_at'
          apply (frule (1) obj_at_cslift_ntfn)
          apply (fastforce intro!: tcb_queue_C_eq
                             simp: cnotification_relation_def Let_def ctcb_queue_relation_def typ_heap_simps
                                   ctcb_queue_relation_def tcb_queue_to_tcb_queue_C_def)
         apply ceqv
        apply (rule_tac xf'=dest_'
                    and val="option_to_ctcb_ptr (tcbQueueHead (ntfnQueue ntfn))"
                    and R="ko_at' ntfn ntfnPtr and valid_objs'"
                     in ccorres_symb_exec_r_known_rv[where R'=UNIV])
           apply (rule conseqPre, vcg)
           apply normalise_obj_at'
           apply (frule (1) obj_at_cslift_ntfn)
           apply (fastforce simp: tcb_queue_to_tcb_queue_C_def)
          apply ceqv
         apply (ctac add: tcbNTFNDequeue_ccorres)
           apply (ctac (no_vcg))
            apply (ctac (no_vcg))
             apply (ctac (no_vcg) add: maybeDonateSchedContext_ccorres)
              apply (ctac (no_vcg) add: isSchedulable_ccorres)
               apply (rule ccorres_split_nothrow[where r'=dc and xf'=xfdc])
                   apply (clarsimp simp: when_def)
                   apply (rule ccorres_cond[where R=\<top>])
                     apply (fastforce simp: to_bool_def)
                    apply (ctac (no_vcg) add: possibleSwitchTo_ccorres)
                   apply (rule ccorres_return_Skip)
                  apply ceqv
                 apply (clarsimp simp: ifCondRefillUnblockCheck_def)
                 apply (rule ccorres_pre_threadGet)
                 apply (rule ccorres_move_c_guard_tcb)
                 apply (clarsimp simp: when_def)
                 apply (rule ccorres_if_lhs)
                  apply (clarsimp simp: bind_assoc, rename_tac scPtr)
                  apply wpfix
                  apply (rule ccorres_pre_getObject_sc, rename_tac sc)
                  apply (rule ccorres_pre_getCurSc, rename_tac cur_sc)
                  apply (rule_tac xf'="ret__unsigned_long_'"
                              and val="from_bool (scSporadic sc)"
                              and R="obj_at' (\<lambda>tcb. tcbSchedContext tcb = Some scPtr)
                                             (the (tcbQueueHead (ntfnQueue ntfn)))
                                     and ko_at' sc scPtr and valid_objs' and no_0_obj'
                                     and K (tcbQueueHead (ntfnQueue ntfn) \<noteq> None)"
                               in ccorres_symb_exec_r_known_rv[where R'=UNIV])
                     apply (rule conseqPre, vcg)
                     apply normalise_obj_at'
                     apply (frule (1) obj_at_cslift_tcb)
                     apply (frule (1) obj_at_cslift_sc)
                     apply (frule (1) tcb_ko_at_valid_objs_valid_tcb')
                     apply (clarsimp simp: typ_heap_simps ctcb_relation_def
                                           csched_context_relation_def valid_tcb'_def
                                           to_bool_def option_to_ctcb_ptr_def
                                    split: if_splits)
                    apply ceqv
                   apply (rule_tac P="scSporadic sc" in ccorres_cases; clarsimp)
                    apply ccorres_rewrite
                    apply (clarsimp simp: option_to_ctcb_ptr_def)
                    apply (rule ccorres_move_c_guard_tcb)
                    apply (rule_tac Q="\<lambda>s. cur_sc = ksCurSc s
                                           \<and> obj_at' (\<lambda>tcb. tcbSchedContext tcb = Some scPtr)
                                                     (the (tcbQueueHead (ntfnQueue ntfn))) s
                                           \<and> tcbQueueHead (ntfnQueue ntfn) \<noteq> None"
                                 in ccorres_cond_both'[where Q'=\<top>])
                      apply clarsimp
                      apply (frule (1) obj_at_cslift_tcb)
                      apply (fastforce dest!: rf_sr_ksCurSC simp: typ_heap_simps' ctcb_relation_def)
                     apply (rule ccorres_move_c_guard_tcb)
                     apply (ctac (no_vcg) add: refill_unblock_check_ccorres)
                    apply (rule ccorres_return_Skip)
                   apply ccorres_rewrite
                   apply (rule ccorres_return_Skip)
                  apply (vcg exspec=sc_sporadic_modifies)
                 apply (rule_tac xf'="ret__unsigned_long_'"
                             and val="from_bool False"
                             and R="obj_at' (\<lambda>tcb. tcbSchedContext tcb = None)
                                            (the (tcbQueueHead (ntfnQueue ntfn)))
                                    and K (tcbQueueHead (ntfnQueue ntfn) \<noteq> None) and no_0_obj'"
                              in ccorres_symb_exec_r_known_rv[where R'=UNIV])
                    apply (rule conseqPre, vcg)
                    apply normalise_obj_at'
                    apply (frule (1) obj_at_cslift_tcb)
                    apply (clarsimp simp: typ_heap_simps ctcb_relation_def option_to_ctcb_ptr_def)
                   apply ceqv
                  apply ccorres_rewrite
                  apply (rule ccorres_return_Skip)
                 apply (vcg exspec=sc_sporadic_modifies)
                apply (rule_tac Q'="\<lambda>_ s. invs' s \<and> tcbQueueHead (ntfnQueue ntfn) \<noteq> None"
                             in hoare_post_imp)
                 apply (fastforce simp: obj_at'_def)
                apply wpsimp
               apply clarsimp
               apply (vcg exspec=possibleSwitchTo_modifies)
              apply (wpsimp wp: getSchedulable_wp)
             apply (rule_tac Q'="\<lambda>_ s. invs' s \<and> weak_sch_act_wf (ksSchedulerAction s) s
                                       \<and> tcbQueueHead (ntfnQueue ntfn) \<noteq> None
                                       \<and> tcb_at' (the (tcbQueueHead (ntfnQueue ntfn))) s"
                          in hoare_post_imp)
              apply fastforce
             apply (wpsimp wp: maybeDonateSc_invs')
            apply wpsimp
           apply (wpsimp wp: setThreadState_Running_invs')
          apply (wpsimp wp: setNotification_invs')
         apply (vcg exspec=tcbNTFNDequeue_modifies)
        apply vcg
       apply (vcg exspec=ntfn_ptr_get_queue_modifies)
      apply wpsimp
     apply (wpsimp wp: gts_wp')
    apply wpsimp
   apply (clarsimp simp: guard_is_UNIV_def ThreadState_defs mask_def
                         badgeRegister_def C_register_defs RISCV64.badgeRegister_def
                         notification_state_defs option_to_ctcb_ptr_def tcbQueueEmpty_def)
   apply (fastforce simp: typ_heap_simps ctcb_relation_def)
  apply clarsimp
  apply (simp only: conj_assoc[symmetric])
  apply (rule conjI)
   apply (fastforce simp: st_tcb_at'_def obj_at'_def tcbQueueEmpty_def
                          isBlockedOnNtfn_def is_BlockedOnReply_def
                   split: if_splits)
  apply (fastforce dest: ntfn_ko_at_valid_objs_valid_ntfn' tcb_at_not_NULL
                   simp: valid_ntfn'_def option_to_ctcb_ptr_def)
  done

lemma receiveSignal_block_ccorres_helper:
  "ccorres dc xfdc
     (tcb_at' thread and valid_objs' and ntfn_at' ntfnptr and pspace_canonical'
      and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s) and no_0_obj'
      and pspace_aligned' and pspace_distinct' and K (ntfnptr = ntfnptr && ~~ mask 4))
                                 \<comment> \<open>this 4 is coming from thread_state_ptr_set_blockingObject_spec\<close>
     UNIV hs
     (setThreadState (Structures_H.thread_state.BlockedOnNotification ntfnptr) thread)
     (Guard C_Guard {s. s \<Turnstile>\<^sub>c tcb_ptr_to_ctcb_ptr thread}
        (CALL thread_state_ptr_set_tsType(Ptr
                &(tcb_ptr_to_ctcb_ptr thread\<rightarrow>[''tcbState_C'']),
                  scast ThreadState_BlockedOnNotification));;
      Guard C_Guard {s. s \<Turnstile>\<^sub>c tcb_ptr_to_ctcb_ptr thread}
        (CALL thread_state_ptr_set_blockingObject(Ptr
                &(tcb_ptr_to_ctcb_ptr thread\<rightarrow>[''tcbState_C'']),
                  ucast (ptr_val (ntfn_Ptr ntfnptr))));;
      CALL scheduleTCB(tcb_ptr_to_ctcb_ptr thread))"
  unfolding K_def setThreadState_def
  apply (intro ccorres_gen_asm)
  apply (rule ccorres_guard_imp)
    apply (rule_tac P="canonical_address ntfnptr" in ccorres_gen_asm)
    apply (rule ccorres_split_nothrow_novcg)
        apply (rule_tac P'="tcb_at' thread" in threadSet_ccorres_lemma3[where P=\<top>])
         apply vcg
        apply clarsimp
        apply (frule (1) tcb_at_h_t_valid)
        apply (frule h_t_valid_c_guard)
        apply (clarsimp simp: typ_heap_simps' rf_sr_tcb_update_twice)
        apply (erule (1) rf_sr_tcb_update_gen, (simp add: typ_heap_simps')+)
         apply (simp add: tcb_cte_cases_def cteSizeBits_def)
        apply (simp add: ctcb_relation_def cthread_state_relation_def
                         ThreadState_defs mask_def
                   flip: canonical_bit_def)
        apply (clarsimp simp: canonical_address_sign_extended sign_extended_iff_sign_extend
                              objBits_simps')
       apply ceqv
      apply clarsimp
      apply (ctac add: scheduleTCB_ccorres)
     apply (wp hoare_vcg_all_lift threadSet_valid_objs')
    apply (clarsimp simp: guard_is_UNIV_def)
   apply (auto simp: weak_sch_act_wf_def valid_tcb'_def tcb_cte_cases_def
                     obj_at'_is_canonical cteSizeBits_def)
  done

lemma tcbNTFNAppend_ccorres[corres]:
  "ccorres dc xfdc
     (valid_objs' and pspace_canonical' and tcb_at' thread)
     (\<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr thread\<rbrace> \<inter> \<lbrace>\<acute>ntfnPtr = ntfn_Ptr ntfnPtr\<rbrace>) hs
     (tcbNTFNAppend thread ntfnPtr) (Call tcbNTFNAppend_'proc)"
  unfolding tcbNTFNAppend_def
  apply (ccorres_exec_l_pre ccorres_exec_l_pre: get_ntfn_sp')+
  apply (cinit' lift: thread_' ntfnPtr_')
   apply clarsimp
   apply (rename_tac ntfn)
   apply (rule_tac xf'=queue_'
               and val="tcb_queue_to_tcb_queue_C (ntfnQueue ntfn)"
               and R="ko_at' ntfn ntfnPtr and valid_objs'"
                in ccorres_symb_exec_r_known_rv[where R'=UNIV])
      apply (rule conseqPre, vcg)
      apply normalise_obj_at'
      apply (frule (1) obj_at_cslift_ntfn)
      apply (fastforce intro: tcb_queue_C_eq
                        simp: cnotification_relation_def Let_def ctcb_queue_relation_def
                              tcb_queue_to_tcb_queue_C_def typ_heap_simps)
     apply ceqv
    apply (ctac add: tcbAppend_ccorres)
      apply (rename_tac q' new_queue)
            apply (rule_tac P'="\<lambda>s. ntfn_at' ntfnPtr s \<and> pspace_canonical' s
                                    \<and> tcb_queue_head_end_valid q' s"
                        and Q="\<lambda>s endpoint. {s'. (s, s') \<in> rf_sr \<and> ko_at' endpoint ntfnPtr s
                                                 \<and> pspace_canonical' s
                                                 \<and> tcb_queue_head_end_valid q' s}"
                        in updateNotification_ccorres_lemma3[where P=\<top>])
           apply (rule conseqPre, vcg)
           apply clarsimp
           apply (frule (1) obj_at_cslift_ntfn)
           apply (clarsimp simp: typ_heap_simps')
           apply (simp cong: StateSpace.state.fold_congs globals.fold_congs)
           apply (fastforce intro!: rf_sr_notification_update2 tcb_ptr_sign_extend_canonical
                              simp: cnotification_relation_def ctcb_queue_relation_def Let_def
                                    tcb_queue_to_tcb_queue_C_def option_to_ctcb_ptr_def
                                    packed_heap_update_collapse_hrs mask_def
                                    notification_state_defs)
      apply clarsimp
     apply (wpsimp wp: simp: tcbAppend_def)
    apply (vcg exspec=tcbAppend_modifies)
   apply vcg
  apply (force dest: obj_at_cslift_ntfn simp: typ_heap_simps ctcb_queue_relation_def)
  done

lemma ntfn_Active_split:
  "(case ntfnState ntfn of Active \<Rightarrow> f | _ \<Rightarrow> g) = (if ntfnState ntfn = Active then f else g)"
  apply (cases ntfn; clarsimp)
  by (rename_tac state q msg bound_tcb bound_sc, case_tac state; clarsimp)

crunch tcbNTFNAppend
  for ntfn_at'[wp]: "ntfn_at' ntfnPtr"
  (wp: crunch_wps)

crunch maybeDonateSc, asUser
  for sc_at'[wp]: "sc_at' scPtr"
  and ksCurSc[wp]: "\<lambda>s. P (ksCurSc s)"
  and no_0_obj'[wp]: no_0_obj'
  and weak_sch_act_wf[wp]: "\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s"
  (simp: crunch_simps wp:crunch_wps)

lemma receiveSignal_ccorres[corres]:
  "ccorres dc xfdc
     (invs' and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s)
      and valid_cap' cap and st_tcb_at' simple' thread and K (isNotificationCap cap))
     (\<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr thread\<rbrace>
      \<inter> \<lbrace>ccap_relation cap \<acute>cap\<rbrace>
      \<inter> \<lbrace>\<acute>isBlocking = from_bool is_blocking\<rbrace>) hs
     (receiveSignal thread cap is_blocking)
     (Call receiveSignal_'proc)"
  unfolding receiveSignal_def K_bind_def haskell_assert_def return_bind
  supply Collect_const[simp del]
  apply (rule ccorres_grab_asm)
  apply (ccorres_exec_l_pre ccorres_exec_l_pre: isRunnable_sp get_ntfn_sp')+
  apply (cinit' lift: thread_' cap_' isBlocking_')
   apply (subst ntfn_Active_split)
   apply (subst if_swap)
   apply (rule_tac xf'=ret__unsigned_longlong_'
               and val="capNtfnPtr cap"
                in ccorres_symb_exec_r_known_rv[where R=\<top> and R'=UNIV])
      apply vcg
      apply (clarsimp simp: cap_get_tag_isCap isCap_simps)
      apply (frule cap_get_tag_isCap_unfolded_H_cap)
      apply (simp add: cap_notification_cap_lift ccap_relation_def cap_to_H_def)
     apply ceqv
    apply csymbr
    apply (rule_tac xf'=ret__unsigned_longlong_'
                and val="case ntfnState ntfn of
                             IdleNtfnState \<Rightarrow> scast NtfnState_Idle
                           | Waiting \<Rightarrow> scast NtfnState_Waiting
                           | Active \<Rightarrow> scast NtfnState_Active"
                and R="ko_at' ntfn (capNtfnPtr cap)"
                 in ccorres_symb_exec_r_known_rv[where R'=UNIV])
       apply (rule conseqPre, vcg)
       apply normalise_obj_at'
       apply (frule (1) obj_at_cslift_ntfn)
       apply (clarsimp simp: cnotification_relation_def Let_def typ_heap_simps
                      split: ntfnstate.splits)
      apply ceqv
     apply (rule ccorres_cond_both'[where Q=\<top> and Q'=\<top>])
       apply (clarsimp simp: notification_state_defs split: ntfnstate.splits if_splits)
      apply (clarsimp simp: receiveSignalBlocked_def)
      apply (subst case_bool_If)
      apply (rule ccorres_cond_both'[where Q=\<top> and Q'=\<top>])
        apply fastforce
       apply (intro ccorres_rhs_assoc)
       apply (rule ccorres_rhs_assoc2)
       apply (rule ccorres_rhs_assoc2)
       apply (rule ccorres_split_nothrow)
           apply (rule receiveSignal_block_ccorres_helper[simplified])
          apply ceqv
         apply clarsimp
         apply (ctac add: tcbNTFNAppend_ccorres)
           apply (ctac add: maybeReturnSchedContext_ccorres)
          apply wpsimp
         apply (vcg exspec=tcbNTFNAppend_modifies)
        apply wpsimp
       apply clarsimp
       apply (vcg exspec=scheduleTCB_modifies)
      apply (clarsimp simp: guard_is_UNIV_def)
      apply (ctac add: doNBRecvFailedTransfer_ccorres)
     apply (rule ccorres_cond_true)
     apply clarsimp
     apply (intro ccorres_rhs_assoc)
     apply (rule_tac val="the (ntfnMsgIdentifier ntfn)"
                 and xf'=ret__unsigned_longlong_'
                 and R="ko_at' ntfn (capNtfnPtr cap) and K (ntfnMsgIdentifier ntfn \<noteq> None)"
                  in ccorres_symb_exec_r_known_rv[where R'=UNIV])
        apply (vcg, clarsimp)
        apply (frule (1) obj_at_cslift_ntfn)
        apply (clarsimp simp: cnotification_relation_def Let_def typ_heap_simps
                       split: Structures_H.notification.splits)
       apply ceqv
      apply (clarsimp simp: badgeRegister_def Kernel_C.badgeRegister_def)
      apply ctac
        apply (rule ccorres_split_nothrow[where r'=dc and xf'=xfdc])
            apply (rule_tac P'="\<lambda>s. ntfn_at' (capNtfnPtr cap) s "
                        and Q="\<lambda>s ntfn. {s'. (s, s') \<in> rf_sr \<and> ko_at' ntfn (capNtfnPtr cap) s}"
                         in updateNotification_ccorres_lemma3[where P=\<top>])
             apply (rule conseqPre, vcg)
             apply clarsimp
             apply (frule (1) obj_at_cslift_ntfn)
             apply (clarsimp simp: typ_heap_simps')
             apply (simp cong: StateSpace.state.fold_congs globals.fold_congs)
             apply (fastforce intro!: rf_sr_notification_update2 tcb_ptr_sign_extend_canonical
                                simp: cnotification_relation_def Let_def notification_state_defs)
            apply fastforce
           apply ceqv
          apply (ctac add: maybeDonateSchedContext_ccorres)
            apply (rule ccorres_pre_threadGet)
            apply (clarsimp simp: ifCondRefillUnblockCheck_def)
            apply (rule ccorres_move_c_guard_tcb)
            apply (clarsimp simp: when_def)
            apply (rule ccorres_if_lhs)
             apply (clarsimp simp: bind_assoc, rename_tac scPtr)
             apply wpfix
             apply (rule ccorres_pre_getObject_sc, rename_tac sc)
             apply (rule ccorres_pre_getCurSc, rename_tac cur_sc)
             apply (rule ccorres_rhs_assoc2)
             apply (rule_tac xf'=ret__int_'
                         and val="from_bool (scSporadic sc \<and> scPtr \<noteq> cur_sc)"
                         and R="\<lambda>s. obj_at' (\<lambda>tcb. tcbSchedContext tcb = Some scPtr) thread s
                                    \<and> ko_at' sc scPtr s \<and> valid_objs' s \<and> no_0_obj' s
                                    \<and> ksCurSc s = cur_sc"
                          in ccorres_symb_exec_r_known_rv[where R'=UNIV])
                apply (rule conseqPre, vcg)
                apply normalise_obj_at'
                apply (frule (1) obj_at_cslift_tcb)
                apply (frule (1) tcb_ko_at_valid_objs_valid_tcb')
                apply (clarsimp simp: valid_tcb'_def valid_bound_obj'_def)
                apply normalise_obj_at'
                apply (frule (1) obj_at_cslift_sc)
                apply normalise_obj_at'
                apply (frule rf_sr_ksCurSC)
                subgoal
                  by (fastforce simp: typ_heap_simps ctcb_relation_def
                                      csched_context_relation_def to_bool_def
                                      option_to_ctcb_ptr_def from_bool_def
                               split: if_splits bool.splits)
               apply ceqv
              apply (rule ccorres_cond_both'[where Q=\<top> and Q'=\<top>])
                apply fastforce
               apply (ctac add: refill_unblock_check_ccorres)
              apply (rule ccorres_return_Skip)
             apply (vcg exspec=sc_sporadic_modifies)
            apply (rule ccorres_rhs_assoc2)
            apply (rule_tac xf'=ret__int_'
                        and val="from_bool False"
                        and R="obj_at' (\<lambda>tcb. tcbSchedContext tcb = None) thread
                               and valid_objs' and no_0_obj'"
                         in ccorres_symb_exec_r_known_rv[where R'=UNIV])
               apply (rule conseqPre, vcg)
               apply normalise_obj_at'
               apply (frule (1) obj_at_cslift_tcb)
               apply (frule rf_sr_ksCurSC)
               apply (clarsimp simp: ctcb_relation_def typ_heap_simps)
              apply ceqv
             apply ccorres_rewrite
             apply (rule ccorres_return_Skip)
            apply (vcg exspec=sc_sporadic_modifies)
           apply (wpsimp wp: hoare_vcg_all_lift)
           apply (rule_tac Q'="\<lambda>_. no_0_obj' and valid_objs'
                                   and pspace_aligned' and pspace_distinct' and pspace_bounded'"
                        in hoare_post_imp)
            apply (fastforce simp: obj_at'_def)
           apply ((wpsimp | wps)+)[1]
          apply (vcg exspec=maybeDonateSchedContext_modifies)
         apply ((wpsimp wp: setNotification_invs' getNotification_wp simp: updateNotification_def
                 | wps)+)[1]
        apply (vcg exspec=notification_ptr_set_state_modifies)
       apply (rule_tac Q'="\<lambda>_ s. ntfn_at' (capNtfnPtr cap) s \<and> tcb_at' thread s
                                 \<and> invs' s \<and> weak_sch_act_wf (ksSchedulerAction s) s"
                    in hoare_post_imp)
        apply clarsimp
        apply (frule invs_valid_objs')
        apply (frule (1) ntfn_ko_at_valid_objs_valid_ntfn')
        apply (fastforce simp: valid_ntfn'_def)
       apply ((wpsimp wp: hoare_vcg_all_lift | rule hoare_lift_Pf2[where f=ksCurSc])+)[1]
      apply (vcg exspec=setRegister_modifies)
     apply (vcg exspec=notification_ptr_get_ntfnMsgIdentifier_modifies)
    apply (vcg exspec=notification_ptr_get_state_modifies)
   apply wpsimp
   apply (vcg exspec=cap_notification_cap_get_capNtfnPtr_modifies)
  apply clarsimp
  apply (prop_tac "capNtfnPtr cap = capNtfnPtr cap && ~~ mask 4")
   apply (clarsimp simp: obj_at'_def objBits_simps')
  by (intro conjI impI;
      fastforce dest!: ntfn_ko_at_valid_objs_valid_ntfn'[OF _ invs_valid_objs']
                 simp: ctcb_relation_def typ_heap_simps
                       RISCV64.badgeRegister_def RISCV64.capRegister_def C_register_defs
                       valid_ntfn'_def notification_state_defs
                split: ntfnstate.splits)

end
end
