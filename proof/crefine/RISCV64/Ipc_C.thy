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

context begin interpretation Arch . (*FIXME: arch_split*)

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

crunch sch_act_wf: handleFaultReply "\<lambda>s. sch_act_wf (ksSchedulerAction s) s"

crunch valid_ipc_buffer_ptr' [wp]: copyMRs "valid_ipc_buffer_ptr' p"
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

crunch inv[wp]: getSanitiseRegisterInfo P

lemma empty_fail_getSanitiseRegisterInfo[wp, simp]:
  "empty_fail (getSanitiseRegisterInfo t)"
  by (wpsimp simp: getSanitiseRegisterInfo_def wp: ArchMove_C.empty_fail_archThreadGet)

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
  "\<lbrakk> ccap_relation cap cap'; cap_get_tag cap' = scast cap_reply_cap \<rbrakk>
        \<Longrightarrow> capReplyCanGrant_CL (cap_reply_cap_lift cap') = from_bool (capReplyCanGrant cap)
          \<and> capReplyMaster_CL (cap_reply_cap_lift cap') = from_bool (capReplyMaster cap)
          \<and> cap_reply_cap_CL.capTCBPtr_CL (cap_reply_cap_lift cap')
              = ptr_val (tcb_ptr_to_ctcb_ptr (capTCBPtr cap))"
  by (clarsimp simp: cap_lift_reply_cap cap_to_H_simps
                     cap_reply_cap_lift_def word_size
              elim!: ccap_relationE)

(*FIXME: arch_split: C kernel names hidden by Haskell names *)
(*FIXME: fupdate simplification issues for 2D arrays *)
abbreviation "syscallMessageC \<equiv>  kernel_all_global_addresses.fault_messages.[unat MessageID_Syscall]"
lemmas syscallMessageC_def = kernel_all_substitute.fault_messages_def
abbreviation "exceptionMessageC \<equiv> kernel_all_substitute.fault_messages.[unat MessageID_Exception]"
lemmas exceptionMessageC_def = kernel_all_substitute.fault_messages_def

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

end

context begin interpretation Arch . (*FIXME: arch_split*)

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
  apply (simp add: threadGet_def getObject_get_assert liftM_def bind_assoc stateAssert_def)
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
                  | wp asUser_typ_ats)+)+
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
                  | wp asUser_typ_ats mapM_wp')+)+
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
                        | wp asUser_typ_ats empty_fail_loadWordUser)+)+
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
  "ccorres (\<lambda>r r'. r = unat (r' && mask msgLengthBits)) ret__unsigned_'
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
        apply (simp add: msg_align_bits word_size_def msgMaxLength_def unat_of_nat
                         length_msgRegisters n_msgRegisters_def uint_nat unat_word_ariths)
       apply (simp add: unat_word_ariths msg_align_bits msgMaxLength_def
                        word_less_nat_alt unat_of_nat)
      apply (simp add: unat_word_ariths msg_align_bits msgMaxLength_def
                       word_less_nat_alt unat_of_nat)
     apply (clarsimp simp: valid_ipc_buffer_ptr'_def)
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
context begin interpretation Arch . (*FIXME: arch_split*)
crunch valid_pspace'[wp]: setMR "valid_pspace'"
crunch valid_ipc_buffer_ptr'[wp]: setMR "valid_ipc_buffer_ptr' p"
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
  "\<lbrace>obj_at' (\<lambda>tcb. P (tcbFault tcb)) t\<rbrace> asUser t' m
   \<lbrace>\<lambda>rv. obj_at' (\<lambda>tcb. P (tcbFault tcb)) t\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp threadGet_wp)
  apply (simp cong: if_cong)
  done

lemma asUser_atcbContext_obj_at:
  "t \<noteq> t' \<Longrightarrow>
    \<lbrace>obj_at' (\<lambda>tcb. P ((atcbContextGet o tcbArch) tcb)) t\<rbrace>
      asUser t' m
    \<lbrace>\<lambda>rv. obj_at' (\<lambda>tcb. P ((atcbContextGet o tcbArch) tcb)) t\<rbrace>"
  apply (simp add: asUser_def split_def atcbContextGet_def atcbContextSet_def)
  apply (wp threadGet_wp)
  apply simp
  done

lemma asUser_tcbFault_inv:
  "\<lbrace>\<lambda>s. \<exists>t. ko_at' t p' s \<and> tcbFault t = f\<rbrace> asUser p m
   \<lbrace>\<lambda>rv s. \<exists>t. ko_at' t p' s \<and> tcbFault t = f\<rbrace>"
  apply (rule_tac Q="\<lambda>rv. obj_at' (\<lambda>t. tcbFault t = f) p'"
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

(* FIXME move to Corres_C and remove from Tcb_C *)
lemma ccorres_abstract_known:
  "\<lbrakk> \<And>rv' t t'. ceqv \<Gamma> xf' rv' t t' g (g' rv'); ccorres rvr xf P P' hs f (g' val) \<rbrakk>
     \<Longrightarrow> ccorres rvr xf P (P' \<inter> {s. xf' s = val}) hs f g"
  apply (rule ccorres_guard_imp2)
   apply (rule_tac xf'=xf' in ccorres_abstract)
    apply assumption
   apply (rule_tac P="rv' = val" in ccorres_gen_asm2)
   apply simp
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
  apply clarsimp
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
     apply (rule guard_is_UNIVI, clarsimp simp: option_to_ptr_def seL4_CapFault_IP_def)
    apply (clarsimp simp: msgMaxLength_unfold length_syscallMessage msgFromLookupFailure_def
                         RISCV64_H.exceptionMessage_def
                         RISCV64.exceptionMessage_def
                         n_exceptionMessage_def
                         n_syscallMessage_def)
    apply (fastforce elim: obj_tcb_at' split: Fault_H.lookup_failure.splits)
  done
qed


definition
  makeArchFaultMessage2 :: "arch_fault \<Rightarrow> machine_word"
where
  "makeArchFaultMessage2 \<equiv>
     \<lambda>aft. case aft of VMFault _ _ \<Rightarrow> 5"

lemma makeFaultMessage2:
  "makeFaultMessage ft thread
    = (do x \<leftarrow> makeFaultMessage ft thread;
       return (case ft of CapFault _ _ _ \<Rightarrow> 1
                   | UnknownSyscallException _ \<Rightarrow> 2
                   | UserException _ _ \<Rightarrow> 3
                   | ArchFault aft \<Rightarrow> makeArchFaultMessage2 aft, snd x) od)"
  by (cases ft)
     (auto simp: makeFaultMessage_def makeArchFaultMessage2_def makeArchFaultMessage_def bind_assoc
          split: fault.split arch_fault.split)+

lemma makeFaultMessage_tcb_at'_fault[wp]:
  "makeFaultMessage ft t \<lbrace> obj_at' (\<lambda>a. tcbFault a = Some ft) p\<rbrace>"
  apply (cases ft, simp_all add: makeFaultMessage_def)
     apply (wpsimp wp: asUser_inv mapM_wp' det_mapM[where S=UNIV]
                       det_getRestartPC getRestartPC_inv
                 simp: getRegister_def makeArchFaultMessage_def
                 split: arch_fault.split)+
  done

lemma doFaultTransfer_ccorres [corres]:
  "ccorres dc xfdc (valid_pspace' and tcb_at' sender and tcb_at' receiver
                    and (case buffer of Some x \<Rightarrow> valid_ipc_buffer_ptr' x | None \<Rightarrow> \<top>)
                    and K (buffer \<noteq> Some 0) and K (receiver \<noteq> sender))
    (UNIV \<inter> \<lbrace>\<acute>sender = tcb_ptr_to_ctcb_ptr sender\<rbrace>
          \<inter> \<lbrace>\<acute>receiver = tcb_ptr_to_ctcb_ptr receiver\<rbrace>
          \<inter> \<lbrace>\<acute>receiverIPCBuffer = Ptr (option_to_0 buffer)\<rbrace>
          \<inter> \<lbrace>\<acute>badge = badge\<rbrace>) []
    (doFaultTransfer badge sender receiver buffer)
    (Call doFaultTransfer_'proc)"
  apply (unfold K_def)
  apply (intro ccorres_gen_asm)
  apply (simp add: doFaultTransfer_def)
  apply (subst makeFaultMessage2)
  apply (simp only: makeArchFaultMessage2_def)
  apply (cinit' lift: sender_' receiver_' receiverIPCBuffer_' badge_')
   apply (rule ccorres_pre_threadGet)
   apply (rename_tac ft)
   apply wpc
    apply (simp del: Collect_const, rule ccorres_fail)
   apply (simp add: split_def bind_assoc del: Collect_const)
   apply (simp only: bind_assoc[symmetric, where m="makeFaultMessage ft t" for ft t])
   apply (ctac(no_vcg) add: setMRs_fault_ccorres)
    apply (rule_tac R="obj_at' (\<lambda>tcb. tcbFault tcb = ft) sender"
              and val="case (the ft) of CapFault _ _ _ \<Rightarrow> 1
                  | ArchFault (VMFault _ _) \<Rightarrow> 5
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
   apply (wpsimp simp: setMRs_to_setMR zipWithM_mapM split_def wp: mapM_wp' setMR_tcbFault_obj_at)+
   apply assumption
  apply (clarsimp simp: obj_at'_def projectKOs)
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
           (UNIV \<inter> \<lbrace>\<acute>bufferPtr = Ptr buffer\<rbrace> \<inter> \<lbrace>\<acute>badge = badge\<rbrace> \<inter> \<lbrace>\<acute>i = of_nat n\<rbrace>)
           hs
           (setExtraBadge buffer badge n)
           (Call setExtraBadge_'proc)"
  apply (rule ccorres_gen_asm)
  apply (cinit lift: bufferPtr_' badge_' i_')
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
                 in hoare_post_imp_R)
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
    apply (simp add: option_to_ptr_def option_to_0_def)
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
                      apply (rule hoare_post_imp_R, rule lsft_real_cte)
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
                      in hoare_post_imp_R, wp lsft_real_cte)
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
    (valid_pspace' and cur_tcb' and tcb_at' sender
        and tcb_at' receiver
        and K (endpoint \<noteq> Some 0)
        and (case_option \<top> valid_ipc_buffer_ptr' sendBuffer)
        and (case_option \<top> valid_ipc_buffer_ptr' receiveBuffer))
    (UNIV \<inter> \<lbrace>\<acute>sender = tcb_ptr_to_ctcb_ptr sender\<rbrace>
          \<inter> \<lbrace>\<acute>receiver = tcb_ptr_to_ctcb_ptr receiver\<rbrace>
          \<inter> \<lbrace>\<acute>sendBuffer = Ptr (option_to_0 sendBuffer)\<rbrace>
          \<inter> \<lbrace>\<acute>receiveBuffer = Ptr (option_to_0 receiveBuffer)\<rbrace>
          \<inter> \<lbrace>canGrant = to_bool \<acute>canGrant\<rbrace>
          \<inter> \<lbrace>\<acute>badge = badge\<rbrace>
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
                       canGrant_' badge_' endpoint_'
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
  apply (wp hoare_post_taut haskell_assert_wp
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
  apply clarsimp
  apply (drule (1) ctes_of_valid)
  apply (drule (1) ko_at_valid_objs', simp add: projectKOs)
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

lemma doIPCTransfer_ccorres [corres]:
  "ccorres dc xfdc
    (valid_pspace' and cur_tcb' and tcb_at' sender and tcb_at' receiver
                   and K (receiver \<noteq> sender \<and> endpoint \<noteq> Some 0))
    (UNIV \<inter> \<lbrace>\<acute>sender = tcb_ptr_to_ctcb_ptr sender\<rbrace>
          \<inter> \<lbrace>\<acute>receiver = tcb_ptr_to_ctcb_ptr receiver\<rbrace>
          \<inter> \<lbrace>canGrant = to_bool \<acute>grant\<rbrace>
          \<inter> \<lbrace>\<acute>badge = badge\<rbrace>
          \<inter> \<lbrace>\<acute>endpoint = option_to_ptr endpoint\<rbrace>)  []
    (doIPCTransfer sender endpoint badge canGrant receiver)
    (Call doIPCTransfer_'proc)"
  apply (cinit lift: sender_' receiver_' grant_' badge_' endpoint_')
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
   apply (rule_tac Q="\<lambda>rv. valid_pspace' and cur_tcb' and tcb_at' sender
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
  "(do x \<leftarrow> f; case_fault (p x) (q x) (r x) (s x) ft od)
    = case_fault (\<lambda>a b. f >>= (\<lambda>x. p x a b)) (\<lambda>a b c. f >>= (\<lambda>x. q x a b c))
          (\<lambda>a. f >>= (\<lambda>x. r x a)) (\<lambda>a. f >>= (\<lambda>x. s x a)) ft"
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
     apply (clarsimp simp: n_exceptionMessage_def n_syscallMessage_def
                           message_info_to_H_def scast_def
                           length_exceptionMessage length_syscallMessage
                           min_def word_less_nat_alt
                           guard_is_UNIV_def seL4_Faults seL4_Arch_Faults
                       split: if_split)
    apply (simp add: length_exceptionMessage length_syscallMessage)
    apply wp
   apply clarsimp
   apply (vcg exspec=getRegister_modifies)
  apply (clarsimp simp: n_exceptionMessage_def n_syscallMessage_def
                        message_info_to_H_def length_exceptionMessage length_syscallMessage
                        min_def word_less_nat_alt obj_at'_def
                 split: if_split)
  apply (fastforce simp: seL4_Faults seL4_Arch_Faults)
  done

context
notes if_cong[cong]
begin
crunch tcbFault: emptySlot, tcbSchedEnqueue, rescheduleRequired
          "obj_at' (\<lambda>tcb. P (tcbFault tcb)) t"
  (wp: threadSet_obj_at'_strongish crunch_wps
    simp: crunch_simps unless_def)

crunch tcbFault: setThreadState, cancelAllIPC, cancelAllSignals
          "obj_at' (\<lambda>tcb. P (tcbFault tcb)) t"
  (wp: threadSet_obj_at'_strongish crunch_wps)
end

lemma sbn_tcbFault:
  "\<lbrace>obj_at' (\<lambda>tcb. P (tcbFault tcb)) t\<rbrace>
  setBoundNotification st t'
  \<lbrace>\<lambda>_. obj_at' (\<lambda>tcb. P (tcbFault tcb)) t\<rbrace>"
  apply (simp add: setBoundNotification_def)
  apply (wp threadSet_obj_at' | simp cong: if_cong)+
  done

crunch tcbFault: unbindNotification, unbindMaybeNotification "obj_at' (\<lambda>tcb. P (tcbFault tcb)) t"
  (ignore: threadSet wp: sbn_tcbFault)

(* FIXME: move *)
lemma cteDeleteOne_tcbFault:
  "\<lbrace>obj_at' (\<lambda>tcb. P (tcbFault tcb)) t\<rbrace>
  cteDeleteOne slot
  \<lbrace>\<lambda>_. obj_at' (\<lambda>tcb. P (tcbFault tcb)) t\<rbrace>"
  apply (simp add: cteDeleteOne_def unless_when split_def)
  apply (simp add: finaliseCapTrue_standin_def Let_def)
  apply (rule hoare_pre)
  apply (wp emptySlot_tcbFault cancelAllIPC_tcbFault getCTE_wp'
            cancelAllSignals_tcbFault unbindNotification_tcbFault
            isFinalCapability_inv unbindMaybeNotification_tcbFault
            hoare_weak_lift_imp
          | wpc | simp add: Let_def)+
  apply (clarsimp split: if_split)
  done

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
  apply (rule hoare_seq_ext[rotated])
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
        and cte_wp_at' (\<lambda>cte. P (cteCap cte)) slot \<rbrace>
    doIPCTransfer sender ep badge grant receiver
    \<lbrace> \<lambda>rv. cte_wp_at' (\<lambda>cte. P (cteCap cte)) slot \<rbrace>"
  apply (simp add: doIPCTransfer_def)
  apply (wp doNormalTransfer_local_slots weak threadGet_wp | wpc)+
  apply simp
  done

lemma doIPCTransfer_reply_or_replyslot:
  "\<lbrace> cte_wp_at' (\<lambda>cte. isReplyCap (cteCap cte)) slot
      or (valid_objs' and (Not o real_cte_at' slot)
          and  cte_wp_at' (\<lambda>cte. cteCap cte = capability.NullCap \<or> isReplyCap (cteCap cte)) slot)\<rbrace>
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

crunch ksCurDomain[wp]: handleFaultReply "\<lambda>s. P (ksCurDomain s)"

lemma doReplyTransfer_ccorres [corres]:
  "ccorres dc xfdc
    (invs' and st_tcb_at' (Not \<circ> isReply) sender
        and tcb_at' receiver and sch_act_simple and (\<lambda>s. ksCurDomain s \<le> maxDomain)
        and ((Not o real_cte_at' slot) or cte_wp_at' (\<lambda>cte. isReplyCap (cteCap cte)) slot)
        and cte_wp_at' (\<lambda>cte. cteCap cte = capability.NullCap \<or> isReplyCap (cteCap cte))
         slot)
    (UNIV \<inter> \<lbrace>\<acute>sender = tcb_ptr_to_ctcb_ptr sender\<rbrace>
          \<inter> \<lbrace>\<acute>receiver = tcb_ptr_to_ctcb_ptr receiver\<rbrace>
          \<inter> \<lbrace>\<acute>slot = Ptr slot\<rbrace>
          \<inter> \<lbrace>\<acute>grant = from_bool grant\<rbrace>)  hs
    (doReplyTransfer sender receiver slot grant)
    (Call doReplyTransfer_'proc)"
proof -
  have invs_valid_queues_strg: "\<And>s. invs' s \<longrightarrow> valid_queues s"
    by clarsimp
  show ?thesis
  apply (cinit lift: sender_' receiver_' slot_' grant_')
   apply (rule getThreadState_ccorres_foo)
   apply (rule ccorres_assert2)
   apply (simp add: liftM_def getSlotCap_def
               del: Collect_const split del: if_split)
   apply (rule ccorres_pre_getCTE)
   apply (rule ccorres_assert2)
   apply (rule ccorres_pre_getCTE)
   apply (rule ccorres_assert2)
   apply (rule ccorres_pre_threadGet)
   apply (rename_tac fault)
   apply (rule ccorres_move_c_guard_tcb)
   apply (rule_tac val="case_option (scast seL4_Fault_NullFault) fault_to_fault_tag fault"
               and xf'=ret__unsigned_longlong_'
               and R="\<lambda>s. \<exists>t. ko_at' t receiver s \<and> tcbFault t = fault"
                in ccorres_symb_exec_r_known_rv_UNIV [where R'=UNIV])
      apply (vcg, clarsimp)
      apply (erule(1) cmap_relation_ko_atE [OF cmap_relation_tcb])
      apply (fastforce simp: ctcb_relation_def typ_heap_simps
                            cfault_rel_def seL4_Fault_lift_def Let_def
                     split: if_split_asm option.split)
     apply ceqv
    apply csymbr
    apply wpc
     apply (clarsimp simp: ccorres_cond_iffs split del: if_split)
     apply (rule ccorres_rhs_assoc)+
     apply (ctac(no_vcg))
      apply (rule ccorres_symb_exec_r)
        apply (ctac(no_vcg) add: cteDeleteOne_ccorres[where w="scast cap_reply_cap"])
         apply (ctac(no_vcg) add: setThreadState_ccorres)
          apply (ctac(no_vcg) add: possibleSwitchTo_ccorres)
         apply (wpsimp wp: sts_running_valid_queues setThreadState_st_tcb)+
        apply (wp cteDeleteOne_sch_act_wf)
       apply vcg
      apply (rule conseqPre, vcg)
      apply (simp(no_asm_use) add: gs_set_assn_Delete_cstate_relation[unfolded o_def]
                                   subset_iff rf_sr_def)
     apply wp
     apply (simp add: cap_get_tag_isCap)
     apply (strengthen invs_weak_sch_act_wf_strg
                       cte_wp_at_imp_consequent'[where P="\<lambda>ct. Ex (ccap_relation (cteCap ct))" for ct]
                       invs_valid_queues_strg)
     apply (simp add: cap_reply_cap_def)
     apply (wp doIPCTransfer_reply_or_replyslot)
    apply (clarsimp simp: seL4_Fault_NullFault_def ccorres_cond_iffs
                          fault_to_fault_tag_nonzero
               split del: if_split)
    apply (rule ccorres_rhs_assoc)+
    apply (rule ccorres_symb_exec_r)
      apply (ctac (no_vcg) add: cteDeleteOne_ccorres[where w="scast cap_reply_cap"])
       apply (rule_tac A'=UNIV in stronger_ccorres_guard_imp)
         apply (rule ccorres_split_nothrow_novcg [OF ccorres_call,
                                                  OF handleFaultReply_ccorres,
                                                  unfolded bind_assoc,
                                                  where xf'=restart_'])
               apply simp_all[3]
            apply ceqv
           apply csymbr
           apply (rule ccorres_split_nothrow_novcg)
               apply (rule threadSet_ccorres_lemma2[where P=\<top>])
                apply vcg
               apply (clarsimp simp: typ_heap_simps')
               apply (erule(1) rf_sr_tcb_update_no_queue2,
                      (simp add: typ_heap_simps')+, simp_all?)[1]
                apply (rule ball_tcb_cte_casesI, simp+)
               apply (clarsimp simp: ctcb_relation_def
                                     seL4_Fault_lift_NullFault
                                     cfault_rel_def is_cap_fault_def
                                     cthread_state_relation_def)
               apply (case_tac "tcbState tcb", simp_all add: is_cap_fault_def)[1]
              apply ceqv
             apply (rule_tac R=\<top> in ccorres_cond2)
               apply (clarsimp simp: to_bool_def Collect_const_mem)
              apply (ctac (no_vcg))
               apply (simp only: K_bind_def)
               apply (ctac add: possibleSwitchTo_ccorres)
              apply (wp sts_running_valid_queues setThreadState_st_tcb | simp)+
             apply (ctac add: setThreadState_ccorres_valid_queues'_simple)
             apply wp
            apply ((wp threadSet_valid_queues threadSet_sch_act threadSet_valid_queues' hoare_weak_lift_imp
                       threadSet_valid_objs' threadSet_weak_sch_act_wf
                         | simp add: valid_tcb_state'_def)+)[1]
           apply (clarsimp simp: guard_is_UNIV_def ThreadState_defs mask_def option_to_ctcb_ptr_def)

          apply (rule_tac Q="\<lambda>rv. valid_queues and tcb_at' receiver and valid_queues' and
                                valid_objs' and sch_act_simple and (\<lambda>s. ksCurDomain s \<le> maxDomain) and
                                (\<lambda>s. sch_act_wf (ksSchedulerAction s) s)" in hoare_post_imp)
           apply (clarsimp simp: inQ_def weak_sch_act_wf_def)
          apply (wp threadSet_valid_queues threadSet_sch_act handleFaultReply_sch_act_wf)
         apply (clarsimp simp: guard_is_UNIV_def)
        apply assumption
       apply clarsimp
       apply (drule_tac p=receiver in obj_at_ko_at')
       apply clarsimp
       apply (erule(1) cmap_relation_ko_atE [OF cmap_relation_tcb])
       apply (clarsimp simp: ctcb_relation_def typ_heap_simps)
      apply wp
      apply (strengthen vp_invs_strg' invs_valid_queues')
      apply (wp cteDeleteOne_tcbFault cteDeleteOne_sch_act_wf)
     apply vcg
    apply (rule conseqPre, vcg)
    apply (simp(no_asm_use) add: gs_set_assn_Delete_cstate_relation[unfolded o_def]
                                 subset_iff rf_sr_def)
   apply (clarsimp simp: guard_is_UNIV_def option_to_ptr_def option_to_0_def
                         ThreadState_defs mask_def
                         ghost_assertion_data_get_def ghost_assertion_data_set_def
                         cap_tag_defs option_to_ctcb_ptr_def
                  split: option.splits)
  apply (clarsimp simp: pred_tcb_at' invs_valid_objs')
  apply (clarsimp simp: pred_tcb_at'_def obj_at'_def cte_wp_at_ctes_of
                        cap_get_tag_isCap)
  apply fastforce
  done
qed

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

lemma setupCallerCap_ccorres [corres]:
  "ccorres dc xfdc (valid_queues and valid_pspace' and (\<lambda>s. \<forall>d p. sender \<notin> set (ksReadyQueues s (d, p)))
                    and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s) and sch_act_not sender
                    and tcb_at' sender and tcb_at' receiver
                    and tcb_at' sender and tcb_at' receiver)
        (UNIV \<inter> \<lbrace>\<acute>sender = tcb_ptr_to_ctcb_ptr sender\<rbrace>
              \<inter> \<lbrace>\<acute>receiver = tcb_ptr_to_ctcb_ptr receiver\<rbrace>
              \<inter> \<lbrace>\<acute>canGrant = from_bool canGrant\<rbrace>) hs
        (setupCallerCap sender receiver canGrant)
        (Call setupCallerCap_'proc)"
  apply (rule ccorres_gen_asm_state, rule ccorres_gen_asm_state)
  apply (frule_tac p=sender in is_aligned_tcb_ptr_to_ctcb_ptr)
  apply (cinit lift: sender_' receiver_' canGrant_')
   apply (clarsimp simp: word_sle_def
                         tcb_cnode_index_defs[THEN ptr_add_assertion_positive[OF ptr_add_assertion_positive_helper]])
   apply ccorres_remove_UNIV_guard
   apply (ctac(no_vcg))
    apply (rule ccorres_move_array_assertion_tcb_ctes)
    apply (simp only: getThreadReplySlot_def getThreadCallerSlot_def)
    apply (ctac(no_vcg))
      apply (rename_tac replySlot replySlot')
      apply (simp del: Collect_const)
      apply (rule ccorres_getCTE_cte_at)
      apply (rule ccorres_move_c_guard_cte)
      apply (ctac(no_vcg) add:  getSlotCap_h_val_ccorres[unfolded getSlotCap_def fun_app_def,
                                                         folded liftM_def, simplified ccorres_liftM_simp])
        apply (rule ccorres_assert2)+
        apply (simp add: ccorres_seq_skip locateSlot_conv
                         )
        apply (rule ccorres_move_array_assertion_tcb_ctes)
        apply csymbr
        apply (rule ccorres_getSlotCap_cte_at)
        apply (rule ccorres_move_c_guard_cte)
        apply (ctac(no_vcg))
         apply (rule ccorres_assert)
         apply (simp only: ccorres_seq_skip)
         apply csymbr
         apply (ctac add: cteInsert_ccorres)
        apply simp
        apply (wp getSlotCap_cte_wp_at)
       apply (clarsimp simp: ccap_relation_def cap_lift_reply_cap
                             cap_to_H_simps cap_reply_cap_lift_def
                             tcbSlots Kernel_C.tcbCaller_def
                             size_of_def cte_level_bits_def)
        apply (simp add: is_aligned_neg_mask)
       apply (wp getCTE_wp')
      apply (simp add: tcbSlots Kernel_C.tcbCaller_def
                       size_of_def cte_level_bits_def
                       ptr_add_assertion_positive Collect_const_mem
                       tcb_cnode_index_defs)
     apply simp
     apply (rule_tac Q="\<lambda>rv. valid_pspace' and tcb_at' receiver" in hoare_post_imp)
      apply (auto simp: cte_wp_at_ctes_of isCap_simps valid_pspace'_def
                        tcbSlots Kernel_C.tcbCaller_def size_of_def
                        cte_level_bits_def)[1]
      apply (case_tac cte,clarsimp)
      apply (drule ctes_of_valid_cap')
       apply fastforce
      apply (simp add:valid_cap'_def capAligned_def)
     apply (simp add: locateSlot_conv)
     apply wp
    apply (clarsimp simp: ccap_rights_relation_def allRights_def
                          mask_def cap_rights_to_H_def tcbCallerSlot_def
                          Kernel_C.tcbCaller_def)
   apply simp
   apply wp
  apply (clarsimp simp: ThreadState_defs mask_def
                        valid_pspace'_def tcbReplySlot_def
                        valid_tcb_state'_def Collect_const_mem
                        tcb_cnode_index_defs)
  done

lemma sendIPC_dequeue_ccorres_helper:
  "ep_ptr = Ptr ep ==>
  ccorres (\<lambda>rv rv'. rv' = tcb_ptr_to_ctcb_ptr dest) dest___ptr_to_struct_tcb_C_'
           (invs' and st_tcb_at' (\<lambda>st. isBlockedOnReceive st \<and>
                                       blockingObject st = ep) dest
                  and ko_at' (RecvEP (dest#rest)) ep) UNIV hs
           (setEndpoint ep $ case rest of [] \<Rightarrow> Structures_H.IdleEP
                                        | (a#list) \<Rightarrow> Structures_H.RecvEP rest)
        (\<acute>queue :== CALL ep_ptr_get_queue(ep_ptr);;
         \<acute>dest___ptr_to_struct_tcb_C :== head_C \<acute>queue;;
         \<acute>queue :== CALL tcbEPDequeue(\<acute>dest___ptr_to_struct_tcb_C,\<acute>queue);;
         CALL ep_ptr_set_queue(ep_ptr,\<acute>queue);;
         IF head_C \<acute>queue = Ptr 0 THEN
             CALL endpoint_ptr_set_state(ep_ptr,scast EPState_Idle)
         FI)"
  apply (rule ccorres_from_vcg)
  apply (rule allI)
  apply (rule conseqPre, vcg)
  apply (clarsimp split del: if_split)
  apply (frule ep_blocked_in_queueD [OF pred_tcb'_weakenE])
     apply simp
    apply assumption+
  apply (frule (1) ko_at_valid_ep' [OF _ invs_valid_objs'])
  apply (elim conjE)
  apply (frule (1) valid_ep_blockedD)
  apply (elim conjE)
  apply (frule cmap_relation_ep)
  apply (erule (1) cmap_relation_ko_atE)
  apply (intro conjI)
   apply (erule h_t_valid_clift)
  apply (rule impI)
  apply (rule exI)
  apply (rule conjI)
   apply (rule_tac x=\<sigma> in exI)
   apply (intro conjI)
       apply assumption+
    apply (drule (2) ep_to_ep_queue)
    apply (simp add: tcb_queue_relation'_def)
   apply (clarsimp simp: typ_heap_simps cendpoint_relation_def Let_def
                   cong: imp_cong split del: if_split)
  apply (intro conjI impI allI)
      apply (fastforce simp: h_t_valid_clift)
     apply (fastforce simp: h_t_valid_clift)
    apply (fastforce simp: h_t_valid_clift)
   \<comment> \<open>empty case\<close>
   apply clarsimp
   apply (frule null_ep_queue [simplified comp_def] null_ep_queue)
   apply (frule iffD1 [OF tcb_queue_head_empty_iff
                          [OF tcb_queue_relation'_queue_rel]])
     apply (rule ballI, erule bspec)
     apply (erule subsetD [rotated])
     apply (clarsimp simp: cendpoint_relation_def Let_def tcb_queue_relation'_def)
    apply simp
   apply (simp add: setEndpoint_def split_def)
   apply (rule conjI)
    apply (rule bexI [OF _ setObject_eq])
        apply (simp add: rf_sr_def cstate_relation_def Let_def
                         cpspace_relation_def update_ep_map_tos
                         typ_heap_simps')
        apply (elim conjE)
        apply (intro conjI)
             \<comment> \<open>tcb relation\<close>
             apply (erule ctcb_relation_null_queue_ptrs)
             apply (clarsimp simp: comp_def)
            \<comment> \<open>ep relation\<close>
            apply (rule cpspace_relation_ep_update_ep, assumption+)
             apply (simp add: cendpoint_relation_def Let_def EPState_Idle_def
                              tcb_queue_relation'_def)
            apply simp
           \<comment> \<open>ntfn relation\<close>
           apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
           apply simp
           apply (rule cnotification_relation_ep_queue [OF invs_sym'], assumption+)
            apply simp
           apply (erule (1) map_to_ko_atI')
          \<comment> \<open>queue relation\<close>
          apply (rule cready_queues_relation_null_queue_ptrs, assumption+)
          apply (clarsimp simp: comp_def)
         apply (clarsimp simp: carch_state_relation_def packed_heap_update_collapse_hrs)
        apply (simp add: cmachine_state_relation_def)
       apply (simp add: h_t_valid_clift_Some_iff)
      apply (simp add: objBits_simps')
     apply (simp add: objBits_simps)
    apply assumption
   apply (clarsimp simp: cendpoint_relation_def Let_def tcb_queue_relation'_def)
  \<comment> \<open>non-empty case\<close>
  apply clarsimp
  apply (frule null_ep_queue [simplified comp_def] null_ep_queue)
  apply (frule tcb_queue_head_empty_iff [OF tcb_queue_relation'_queue_rel])
   apply (rule ballI, erule bspec)
   apply (erule subsetD [rotated])
   apply (clarsimp simp: cendpoint_relation_def Let_def tcb_queue_relation'_def)
  apply (simp add: setEndpoint_def split_def)
  apply (rule conjI)
   apply (rule bexI [OF _ setObject_eq])
       apply (frule(1) st_tcb_at_h_t_valid)
       apply (simp add: rf_sr_def cstate_relation_def Let_def
                        cpspace_relation_def update_ep_map_tos
                        typ_heap_simps')
       apply (elim conjE)
       apply (intro conjI)
             \<comment> \<open>tcb relation\<close>
            apply (erule ctcb_relation_null_queue_ptrs)
            apply (clarsimp simp: comp_def)
           \<comment> \<open>ep relation\<close>
           apply (rule cpspace_relation_ep_update_ep, assumption+)
            apply (clarsimp simp: cendpoint_relation_def Let_def
                                  isRecvEP_def isSendEP_def
                                  tcb_queue_relation'_def valid_ep'_def
                       simp flip: canonical_bit_def
                           split: endpoint.splits list.splits
                       split del: if_split)
            apply (subgoal_tac "tcb_at' (if x22 = [] then x21 else last x22) \<sigma>")
             apply (erule (1) tcb_and_not_mask_canonical[OF invs_pspace_canonical'])
             apply (simp add: objBits_simps')
            apply (clarsimp split: if_split)
           apply simp
          \<comment> \<open>ntfn relation\<close>
          apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
          apply simp
          apply (rule cnotification_relation_ep_queue [OF invs_sym'], assumption+)
           apply simp
          apply (erule (1) map_to_ko_atI')
         \<comment> \<open>queue relation\<close>
         apply (rule cready_queues_relation_null_queue_ptrs, assumption+)
         apply (clarsimp simp: comp_def)
        apply (clarsimp simp: carch_state_relation_def packed_heap_update_collapse_hrs)
       apply (simp add: cmachine_state_relation_def)
      apply (simp add: h_t_valid_clift_Some_iff)
     apply (simp add: objBits_simps')
    apply (simp add: objBits_simps)
   apply assumption
  apply (clarsimp simp: cendpoint_relation_def Let_def tcb_queue_relation'_def)
  done

(* FIXME: this is the old formulation, the above one does not work as expected *)
lemma rf_sr_tcb_update_twice:
  "h_t_valid (hrs_htd (hrs2 (globals s') (t_hrs_' (gs2 (globals s'))))) c_guard
      (ptr (t_hrs_' (gs2 (globals s'))) (globals s'))
    \<Longrightarrow> ((s, globals_update (\<lambda>gs. t_hrs_'_update (\<lambda>ths.
        hrs_mem_update (heap_update (ptr ths gs :: tcb_C ptr) (v ths gs))
            (hrs_mem_update (heap_update (ptr ths gs) (v' ths gs)) (hrs2 gs ths))) (gs2 gs)) s') \<in> rf_sr)
    = ((s, globals_update (\<lambda>gs. t_hrs_'_update (\<lambda>ths.
        hrs_mem_update (heap_update (ptr ths gs) (v ths gs)) (hrs2 gs ths)) (gs2 gs)) s') \<in> rf_sr)"
  by (simp add: rf_sr_def cstate_relation_def Let_def
                cpspace_relation_def typ_heap_simps'
                carch_state_relation_def cmachine_state_relation_def
                packed_heap_update_collapse_hrs)

lemma sendIPC_block_ccorres_helper:
  "ccorres dc xfdc (tcb_at' thread and valid_queues and valid_objs' and pspace_canonical' and
                    sch_act_not thread and ep_at' epptr and
                    (\<lambda>s. sch_act_wf (ksSchedulerAction s) s \<and>
                         (\<forall>d p. thread \<notin> set (ksReadyQueues s (d, p)))) and
                    K (bos = ThreadState_BlockedOnSend
                      \<and> epptr' = epptr \<and> badge' = badge
                      \<and> cg = from_bool canGrant \<and> cgr = from_bool canGrantReply
                      \<and> dc' = from_bool do_call) and
                    K (epptr = epptr && ~~ mask 4) and
                    K (badge = badge && mask 64))
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
        apply (erule(1) rf_sr_tcb_update_no_queue_gen,
          (simp add: typ_heap_simps')+)[1]
         apply (simp add: tcb_cte_cases_def cteSizeBits_def)
        apply (simp add: ctcb_relation_def cthread_state_relation_def
                         ThreadState_defs mask_def)
        apply (clarsimp simp: canonical_address_sign_extended sign_extended_iff_sign_extend
                       split: bool.split)
       apply ceqv
      apply clarsimp
      apply ctac
     apply (wp threadSet_weak_sch_act_wf_runnable' threadSet_valid_queues
               threadSet_valid_objs')
    apply (clarsimp simp: guard_is_UNIV_def)
   apply (clarsimp simp: sch_act_wf_weak valid_tcb'_def valid_tcb_state'_def
                         tcb_cte_cases_def cteSizeBits_def)
   apply (drule obj_at'_is_canonical, simp, simp)
  apply clarsimp
  done

lemma tcb_queue_relation_last_not_NULL:
  assumes   tq: "tcb_queue_relation getNext getPrev mp queue qprev qhead"
  and valid_ep: "\<forall>t\<in>set queue. tcb_at' t s" "distinct queue"
  and     tcbs: "queue \<noteq> []"
  shows "tcb_ptr_to_ctcb_ptr (last queue) \<noteq> NULL"
proof -
  note last_in_set [where as = queue]

  with tq valid_ep(1) show ?thesis
    by (rule tcb_queue_relation_not_NULL') fact+
qed

lemma tcb_queue_relation_update_end:
  fixes getNext_update :: "(tcb_C ptr \<Rightarrow> tcb_C ptr) \<Rightarrow> tcb_C \<Rightarrow> tcb_C" and
  getPrev_update :: "(tcb_C ptr \<Rightarrow> tcb_C ptr) \<Rightarrow> tcb_C \<Rightarrow> tcb_C"
  assumes qr: "tcb_queue_relation getNext getPrev mp queue qprev qhead"
  and      qe: "qend = (if queue = [] then NULL
                                      else tcb_ptr_to_ctcb_ptr (last queue))"
  and     qe': "qend' \<notin> tcb_ptr_to_ctcb_ptr ` set queue"
  and  cs_tcb: "mp qend' = Some tcb"
  and valid_ep: "\<forall>t\<in>set queue. tcb_at' t s" "distinct queue"
  and     qeN: "qend' \<noteq> NULL"
  and     qpN: "queue = [] \<longrightarrow> qprev = NULL"
  and     fgN: "fg_cons getNext (getNext_update \<circ> (\<lambda>x _. x))"
  and     fgP: "fg_cons getPrev (getPrev_update \<circ> (\<lambda>x _. x))"
  and     npu: "\<And>f t. getNext (getPrev_update f t) = getNext t"
  and     pnu: "\<And>f t. getPrev (getNext_update f t) = getPrev t"
  shows   "tcb_queue_relation getNext getPrev
                 (upd_unless_null qend (getNext_update (\<lambda>_. qend') (the (mp qend)))
                       (mp(qend' := Some (getNext_update (\<lambda>_. NULL) (getPrev_update (\<lambda>_. qend)  tcb)))))
                 (queue @ [ctcb_ptr_to_tcb_ptr qend'])
                 qprev (if qhead = NULL then qend' else qhead)"
  using qr qe qe' cs_tcb valid_ep qeN qpN
proof (induct queue arbitrary: qhead qprev qend)
  case Nil
  thus ?case
    by (clarsimp simp: upd_unless_null_def fg_consD1 [OF fgN]
                       fg_consD1 [OF fgP] pnu npu)
next
  case (Cons tcb' tcbs)
  have not_NULL[simplified]: "tcb_ptr_to_ctcb_ptr (last (tcb'#tcbs)) \<noteq> NULL"
                             "qhead \<noteq> NULL"
    using tcb_queue_relation_next_not_NULL tcb_queue_relation_last_not_NULL
          Cons tcb_at_not_NULL
    by (auto split: if_split)
  thus ?case using Cons.prems
    apply (clarsimp simp: upd_unless_null_def fg_consD1 [OF fgN]
                          fg_consD1 [OF fgP] pnu npu
                   split: if_split)
    apply (rule conjI, clarsimp)
    apply (rule impI)
    apply (subst tcb_queue_relation_cong)
        prefer 5
        apply (erule Cons.hyps [OF _ refl], simp_all add: upd_unless_null_def)
    apply (frule(3) tcb_queue_relation_next_not_NULL, simp)
    done
qed

lemma tcbEPAppend_update:
  assumes sr: "ep_queue_relation' mp queue qhead qend"
  and    qe': "qend' \<notin> tcb_ptr_to_ctcb_ptr ` set queue"
  and  cs_tcb: "mp qend' = Some tcb"
  and valid_ep: "\<forall>t\<in>set queue. tcb_at' t s" "distinct queue"
  and     qeN: "qend' \<noteq> NULL"
  shows "ep_queue_relation'
                   (upd_unless_null qend (tcbEPNext_C_update (\<lambda>_. qend') (the (mp qend)))
                (mp(qend' \<mapsto> tcb\<lparr>tcbEPPrev_C := qend, tcbEPNext_C := NULL\<rparr>)))
            (queue @ [ctcb_ptr_to_tcb_ptr qend'])
            (if qhead = NULL then qend' else qhead) qend'"
  using sr qe' cs_tcb valid_ep qeN
  apply -
  apply (erule tcb_queue_relationE')
  apply (rule tcb_queue_relationI')
   apply (erule(6) tcb_queue_relation_update_end
             [where getNext_update = tcbEPNext_C_update
                and getPrev_update = tcbEPPrev_C_update])
       apply simp_all
  done

lemma tcb_queue_relation_qend_mem':
  "\<lbrakk> tcb_queue_relation' getNext getPrev mp queue qhead qend;
  (\<forall>tcb\<in>set queue. tcb_at' tcb t) \<rbrakk>
  \<Longrightarrow> qend \<noteq> NULL \<longrightarrow> ctcb_ptr_to_tcb_ptr qend \<in> set queue"
  by (clarsimp simp: tcb_queue_head_empty_iff tcb_queue_relation'_def
              split: if_split)

lemma tcb_queue_relation_qend_valid':
  "\<lbrakk> tcb_queue_relation' getNext getPrev (cslift s') queue qhead qend;
  (s, s') \<in> rf_sr; (\<forall>tcb\<in>set queue. tcb_at' tcb s) \<rbrakk>
  \<Longrightarrow> qend \<noteq> NULL \<longrightarrow> s' \<Turnstile>\<^sub>c qend"
  apply (frule (1) tcb_queue_relation_qend_mem')
  apply clarsimp
  apply (drule (3) tcb_queue_memberD [OF tcb_queue_relation'_queue_rel])
  apply (simp add: h_t_valid_clift_Some_iff)
  done

lemma tcbEPAppend_spec:
  "\<forall>s queue. \<Gamma> \<turnstile> \<lbrace>s. \<exists>t. (t, s) \<in> rf_sr
                      \<and> (\<forall>tcb\<in>set queue. tcb_at' tcb t) \<and> distinct queue
                      \<and> tcb_at' (ctcb_ptr_to_tcb_ptr \<acute>tcb) t
                      \<and> (ctcb_ptr_to_tcb_ptr \<acute>tcb \<notin> set queue)
                      \<and> ep_queue_relation' (cslift s) queue
                          (head_C \<acute>queue) (end_C \<acute>queue)\<rbrace>
                  Call tcbEPAppend_'proc
                  {t. head_C (ret__struct_tcb_queue_C_' t) =
                       (if head_C \<^bsup>s\<^esup>queue = tcb_Ptr 0
                           then \<^bsup>s\<^esup>tcb
                           else head_C \<^bsup>s\<^esup>queue)
                   \<and> end_C (ret__struct_tcb_queue_C_' t) = \<^bsup>s\<^esup>tcb
                   \<and> ep_queue_relation' (cslift t)
                       (queue @ [ctcb_ptr_to_tcb_ptr \<^bsup>s\<^esup>tcb])
                       (head_C (ret__struct_tcb_queue_C_' t))
                       (end_C (ret__struct_tcb_queue_C_' t))
                   \<and> (cslift t |` (- tcb_ptr_to_ctcb_ptr ` set
                          ((ctcb_ptr_to_tcb_ptr \<^bsup>s\<^esup>tcb) # queue))) =
                  (cslift s |` (- tcb_ptr_to_ctcb_ptr ` set
                          ((ctcb_ptr_to_tcb_ptr \<^bsup>s\<^esup>tcb) # queue)))
                   \<and> option_map tcb_null_ep_ptrs \<circ> (cslift t) =
                       option_map tcb_null_ep_ptrs \<circ> (cslift s)
                   \<and> cslift_all_but_tcb_C t s  \<and> (hrs_htd \<^bsup>t\<^esup>t_hrs) = (hrs_htd \<^bsup>s\<^esup>t_hrs)
                   \<and> (\<forall>rs. zero_ranges_are_zero rs (\<^bsup>s\<^esup>t_hrs)
                       \<longrightarrow> zero_ranges_are_zero rs (\<^bsup>t\<^esup>t_hrs))}"
  apply (intro allI)
  apply (rule conseqPre, vcg)
  apply clarsimp
  apply (frule obj_at_ko_at')
  apply clarsimp
  apply (frule cmap_relation_tcb)
  apply (drule (1) cmap_relation_ko_atD)
  apply clarsimp
  apply (frule c_guard_clift)
  apply (frule (1) tcb_queue'_head_end_NULL)
  apply (frule (1) tcb_queue_relation_qend_mem')
  apply (frule (2) tcb_queue_relation_qend_valid')
  apply (subgoal_tac "end_C (queue_' x) \<noteq> tcb_' x")
   prefer 2
   apply clarsimp
  apply (frule tcbEPAppend_update)
       apply (erule contrapos_nn, erule tcb_ptr_to_ctcb_ptr_imageD)
      apply assumption+
   apply (drule tcb_at_not_NULL, simp)
  apply (unfold upd_unless_null_def)
  apply (clarsimp split: if_split_asm)
   apply (simp add: typ_heap_simps' clift_heap_update_same)
   apply (rule ext)
   apply (clarsimp simp: typ_heap_simps tcb_null_ep_ptrs_def
                  split: if_split)
  apply (simp add: typ_heap_simps' clift_heap_update_same)
  apply (intro conjI)
    apply (clarsimp simp add: typ_heap_simps h_t_valid_clift_Some_iff)
    apply (erule iffD1 [OF tcb_queue_relation'_cong, OF refl refl refl, rotated -1])
    apply (clarsimp split: if_split)
   apply (rule ext)
   apply (clarsimp dest!: ctcb_ptr_to_tcb_ptr_imageI simp: typ_heap_simps h_t_valid_clift_Some_iff)
  apply (rule ext)
  apply (clarsimp simp: tcb_null_ep_ptrs_def typ_heap_simps h_t_valid_clift_Some_iff
                 split: if_split)
  done

lemma sendIPC_enqueue_ccorres_helper:
  "ccorres dc xfdc (valid_pspace'
                and (\<lambda>s. sym_refs ((state_refs_of' s)(epptr := set queue \<times> {EPSend})))
                and st_tcb_at'  (\<lambda>st. isBlockedOnSend st \<and>
                                      blockingObject st = epptr) thread
                and ko_at' (ep::Structures_H.endpoint) epptr
                and K ((ep = IdleEP \<and> queue = [thread]) \<or>
                       (\<exists>q. ep = SendEP q \<and> thread \<notin> set q \<and>
                            queue = q @ [thread])))
           UNIV hs
           (setEndpoint epptr (Structures_H.endpoint.SendEP queue))
           (\<acute>queue :== CALL ep_ptr_get_queue(ep_Ptr epptr);;
            (\<acute>queue :== CALL tcbEPAppend(tcb_ptr_to_ctcb_ptr thread,\<acute>queue);;
             (CALL endpoint_ptr_set_state(ep_Ptr epptr, scast EPState_Send);;
              CALL ep_ptr_set_queue(ep_Ptr epptr,\<acute>queue))))"
  unfolding K_def
  apply (rule ccorres_gen_asm)
  apply (rule ccorres_from_vcg)
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp split del: if_split)
  apply (frule cmap_relation_ep)
  apply (erule (1) cmap_relation_ko_atE)
  apply (rule conjI)
   apply (erule h_t_valid_clift)
  apply (frule(1) st_tcb_at_h_t_valid)
  apply (frule pred_tcb_at')
  apply (rule impI)
  apply (rule_tac x="init queue" in exI)
  apply (frule(1) ko_at_valid_ep' [OF _ valid_pspace_valid_objs'])
  apply (frule is_aligned_tcb_ptr_to_ctcb_ptr)
  apply (rule conjI)
   apply (rule_tac x=\<sigma> in exI)
   apply (simp add: cendpoint_relation_def Let_def)
   apply (case_tac ep, simp_all add: init_def valid_ep'_def)[1]
  apply (subgoal_tac "sym_refs (state_refs_of' (\<sigma>\<lparr>ksPSpace :=
                          (ksPSpace \<sigma>)(epptr \<mapsto> KOEndpoint (SendEP queue))\<rparr>))")
   prefer 2
   apply (clarsimp simp: state_refs_of'_upd ko_wp_at'_def
                         obj_at'_def projectKOs objBitsKO_def)
  apply (subgoal_tac "ko_at' (SendEP queue) epptr (\<sigma>\<lparr>ksPSpace :=
                          (ksPSpace \<sigma>)(epptr \<mapsto> KOEndpoint (SendEP queue))\<rparr>)")
   prefer 2
   apply (clarsimp simp: obj_at'_def projectKOs objBitsKO_def ps_clear_upd)
  apply (intro conjI impI allI)
     apply (fastforce simp: h_t_valid_clift)
    apply (fastforce simp: h_t_valid_clift)
   apply (fastforce simp: h_t_valid_clift)
  apply (case_tac ep, simp_all add: EPState_Idle_def EPState_Send_def)[1]
   \<comment> \<open>IdleEP case\<close>
   apply clarsimp
   apply (frule null_ep_queue [simplified comp_def] null_ep_queue)
   apply (simp add: setEndpoint_def split_def)
   apply (rule bexI [OF _ setObject_eq])
       apply (simp add: rf_sr_def cstate_relation_def init_def Let_def
                        cpspace_relation_def update_ep_map_tos
                        typ_heap_simps')
       apply (elim conjE)
       apply (intro conjI)
            \<comment> \<open>tcb relation\<close>
            apply (erule ctcb_relation_null_queue_ptrs)
            apply (clarsimp simp: comp_def)
           \<comment> \<open>ep relation\<close>
           apply (rule cpspace_relation_ep_update_ep', assumption+)
            apply (clarsimp simp: cendpoint_relation_def Let_def
                                  mask_def [where n=3] EPState_Send_def)
            apply (clarsimp simp: tcb_queue_relation'_def is_aligned_neg_mask)
            apply (rule conjI, simp add: mask_def)
            subgoal
              apply (clarsimp simp: valid_pspace'_def objBits_simps' simp flip: canonical_bit_def)
              apply (erule (1) tcb_and_not_mask_canonical)
              by (simp (no_asm) add: tcbBlockSizeBits_def)
           apply (simp add: isSendEP_def isRecvEP_def)
          \<comment> \<open>ntfn relation\<close>
          apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
          apply simp
          apply (rule cnotification_relation_ep_queue, assumption+)
            apply (simp add: isSendEP_def isRecvEP_def)
           apply simp
          apply (frule_tac x=p in map_to_ko_atI, clarsimp, clarsimp)
          apply (erule(2) map_to_ko_at_updI')
           apply (simp only:projectKOs injectKO_ep objBits_simps)
           apply clarsimp
          apply (clarsimp simp: obj_at'_def projectKOs)
         \<comment> \<open>queue relation\<close>
         apply (rule cready_queues_relation_null_queue_ptrs, assumption+)
         apply (clarsimp simp: comp_def)
        apply (clarsimp simp: carch_state_relation_def packed_heap_update_collapse_hrs)
       apply (simp add: cmachine_state_relation_def)
      apply (simp add: typ_heap_simps')
     apply (simp add: objBits_simps')
    apply (simp add: objBits_simps)
   apply assumption
  \<comment> \<open>SendEP case\<close>
  apply clarsimp
  apply (frule null_ep_queue [simplified comp_def] null_ep_queue)
  apply (simp add: setEndpoint_def split_def)
  apply (rule bexI [OF _ setObject_eq])
      apply (simp add: rf_sr_def cstate_relation_def Let_def init_def
                       cpspace_relation_def update_ep_map_tos
                       typ_heap_simps')
      apply (elim conjE)
      apply (intro conjI)
           \<comment> \<open>tcb relation\<close>
           apply (erule ctcb_relation_null_queue_ptrs)
           apply (clarsimp simp: comp_def)
          \<comment> \<open>ep relation\<close>
          apply (rule cpspace_relation_ep_update_ep', assumption+)
           apply (clarsimp simp: cendpoint_relation_def Let_def
                                 mask_def [where n=3] EPState_Send_def
                          split: if_split)
           subgoal
             apply (clarsimp simp: tcb_queue_relation'_def is_aligned_neg_mask
                                 valid_ep'_def
                           dest: tcb_queue_relation_next_not_NULL)
             apply (rule conjI, clarsimp)
              apply (rule conjI, fastforce simp: mask_def)
              apply (clarsimp simp: valid_pspace'_def objBits_simps' simp flip: canonical_bit_def)
              apply (erule (1) tcb_and_not_mask_canonical)
              apply (simp (no_asm) add: tcbBlockSizeBits_def)
             apply (clarsimp simp: valid_pspace'_def objBits_simps' simp flip: canonical_bit_def)
             apply (rule conjI, solves \<open>simp (no_asm) add: mask_def\<close>)
             apply (erule (1) tcb_and_not_mask_canonical)
             apply (simp (no_asm) add: tcbBlockSizeBits_def)
             done
          apply (simp add: isSendEP_def isRecvEP_def)
         \<comment> \<open>ntfn relation\<close>
         apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
         apply simp
         apply (rule cnotification_relation_ep_queue, assumption+)
           apply (simp add: isSendEP_def isRecvEP_def)
          apply simp
         apply (frule_tac x=p in map_to_ko_atI, clarsimp, clarsimp)
         apply (erule(2) map_to_ko_at_updI')
          apply (clarsimp simp: objBitsKO_def)
         apply (clarsimp simp: obj_at'_def projectKOs)
        \<comment> \<open>queue relation\<close>
        apply (rule cready_queues_relation_null_queue_ptrs, assumption+)
        apply (clarsimp simp: comp_def)
       apply (clarsimp simp: carch_state_relation_def packed_heap_update_collapse_hrs)
      apply (simp add: cmachine_state_relation_def)
     apply (simp add: h_t_valid_clift_Some_iff)
    apply (simp add: objBits_simps')
   apply (simp add: objBits_simps)
  apply assumption
  done

lemma ctcb_relation_blockingIPCCanGrantD:
  "\<lbrakk> ctcb_relation ko ko' ; isReceive (tcbState ko) \<or> isSend (tcbState ko) \<rbrakk>
   \<Longrightarrow> blockingIPCCanGrant_CL (thread_state_lift (tcbState_C ko'))
      = from_bool (blockingIPCCanGrant (tcbState ko))"
  apply (erule disjE; case_tac "tcbState ko" ; clarsimp simp: isReceive_def isSend_def)
   apply (clarsimp simp: ctcb_relation_def cthread_state_relation_def
                         thread_state_lift_def from_bool_to_bool_iff mask_eq1_nochoice)+
  done

lemma sendIPC_ccorres [corres]:
  "ccorres dc xfdc (invs' and st_tcb_at' simple' thread
                          and sch_act_not thread and ep_at' epptr and
                          (\<lambda>s. \<forall>d p. thread \<notin> set (ksReadyQueues s (d, p))))
     (UNIV \<inter> \<lbrace>\<acute>blocking = from_bool blocking\<rbrace>
           \<inter> \<lbrace>\<acute>do_call = from_bool do_call\<rbrace>
           \<inter> \<lbrace>\<acute>badge = badge\<rbrace>
           \<inter> \<lbrace>\<acute>canGrant = from_bool canGrant\<rbrace>
           \<inter> \<lbrace>\<acute>canGrantReply = from_bool canGrantReply\<rbrace>
           \<inter> \<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr thread\<rbrace>
           \<inter> \<lbrace>\<acute>epptr = Ptr epptr\<rbrace>
           \<inter> \<lbrace>badge && mask 64 = badge\<rbrace>) hs
     (sendIPC blocking do_call badge canGrant canGrantReply thread epptr)
     (Call sendIPC_'proc)"
  unfolding K_def
  apply (rule ccorres_gen_asm2)
  apply (cinit' lift: blocking_' do_call_' badge_' canGrant_' canGrantReply_' thread_' epptr_')
   apply (unfold sendIPC_def)[1]
   apply (rule ccorres_pre_getEndpoint)
   apply (rename_tac ep)
   apply (rule_tac xf'=ret__unsigned_longlong_'
               and val="case ep of IdleEP \<Rightarrow> scast EPState_Idle
                           | RecvEP _ \<Rightarrow> scast EPState_Recv
                           | SendEP _ \<Rightarrow> scast EPState_Send"
               and R="ko_at' ep epptr"
                in ccorres_symb_exec_r_known_rv_UNIV[where R'=UNIV])
      apply (vcg, clarsimp)
      apply (erule cmap_relationE1 [OF cmap_relation_ep])
       apply (erule ko_at_projectKO_opt)
      apply (clarsimp simp: typ_heap_simps cendpoint_relation_def Let_def
                     split: endpoint.split_asm)
     apply ceqv
    apply (rule_tac A="invs' and st_tcb_at' simple' thread
                          and sch_act_not thread and ko_at' ep epptr
                          and ep_at' epptr
                          and (\<lambda>s. \<forall>d p. thread \<notin> set (ksReadyQueues s (d, p)))"
                 in ccorres_guard_imp2 [where A'=UNIV])
     apply wpc
       \<comment> \<open>RecvEP case\<close>
       apply (rule ccorres_cond_false)
       apply (rule ccorres_cond_true)
       apply (intro ccorres_rhs_assoc)
       apply (csymbr, csymbr)
       apply wpc
        apply (simp only: haskell_fail_def)
        apply (rule ccorres_fail)
       apply (rename_tac dest rest)
       apply (rule ccorres_rhs_assoc2)
       apply (rule ccorres_rhs_assoc2)
       apply (rule ccorres_rhs_assoc2)
       apply (rule ccorres_rhs_assoc2)
       apply (rule ccorres_split_nothrow_novcg)
           apply (rule_tac dest=dest in sendIPC_dequeue_ccorres_helper)
           apply simp
          apply ceqv
         apply (rename_tac dest')
         apply (simp only: K_bind_def haskell_assert_def return_bind from_bool_0)

         apply (rule getThreadState_ccorres_foo)
         apply (rename_tac recvState)
         apply (rule ccorres_assert)
         apply (ctac(no_vcg))

          apply (rule ccorres_rhs_assoc2)
          apply (rule_tac xf'=replyCanGrant_' and val="from_bool (blockingIPCCanGrant recvState)"
                   and R="st_tcb_at' ((=) recvState) dest" and R'=UNIV
                   in ccorres_symb_exec_r_known_rv)
             apply (clarsimp, rule conseqPre, vcg)
             apply (fastforce simp: pred_tcb_at'_def tcb_at_h_t_valid typ_heap_simps'
                              dest: obj_at_cslift_tcb ctcb_relation_blockingIPCCanGrantD)
            apply ceqv
           apply (ctac(no_vcg))
            apply (ctac(no_vcg) add: possibleSwitchTo_ccorres)
             apply (clarsimp split del: if_split)
             apply (wpc ; ccorres_rewrite)
              apply (clarsimp simp: disj_imp[symmetric] split del: if_split)
              apply (wpc ; clarsimp)
               apply ccorres_rewrite
               apply (ctac add: setupCallerCap_ccorres)
              apply ccorres_rewrite
              apply (ctac add: setThreadState_ccorres)
             apply (rule ccorres_return_Skip)
            apply (wpsimp wp: hoare_drop_imps hoare_vcg_all_lift possibleSwitchTo_sch_act_not
                              possibleSwitchTo_sch_act_not sts_st_tcb'
                              possibleSwitchTo_ksQ' sts_valid_queues sts_ksQ'
                          simp: valid_tcb_state'_def)+
          apply vcg
         apply (wpsimp wp: doIPCTransfer_sch_act setEndpoint_ksQ hoare_vcg_all_lift
                          set_ep_valid_objs' setEndpoint_valid_mdb'
                | wp (once) hoare_drop_imp
                | strengthen sch_act_wf_weak)+
       apply (fastforce simp: guard_is_UNIV_def ThreadState_defs Collect_const_mem mask_def
                              option_to_ptr_def option_to_0_def
                        split: bool.split_asm)

      \<comment> \<open>IdleEP case\<close>
      apply (rule ccorres_cond_true)
      apply (rule ccorres_cond)
        apply (clarsimp simp: from_bool_def split: bool.split)
       \<comment> \<open>blocking case\<close>
       apply (intro ccorres_rhs_assoc)
       apply csymbr
       apply (simp only:)
       \<comment> \<open>apply (ctac (trace, no_vcg,c_lines 6) add: sendIPC_block_ccorres_helper)\<close>
       apply (rule ccorres_rhs_assoc2)
       apply (rule ccorres_rhs_assoc2)
       apply (rule ccorres_rhs_assoc2)
       apply (rule ccorres_rhs_assoc2)
       apply (rule ccorres_rhs_assoc2)
       apply (rule ccorres_rhs_assoc2)
       apply (rule ccorres_split_nothrow_novcg)
           apply (rule sendIPC_block_ccorres_helper)
          apply ceqv
         apply (simp only: K_bind_def fun_app_def)
         apply (rule_tac ep=IdleEP in sendIPC_enqueue_ccorres_helper)
        apply (simp add: valid_ep'_def)
        apply (wp sts_st_tcb')
       apply (clarsimp simp: obj_at'_def ko_wp_at'_def projectKOs)
       apply (clarsimp simp: guard_is_UNIV_def)
      apply (rule ccorres_return_Skip)
     \<comment> \<open>SendEP case\<close>
     apply (rule ccorres_cond_true)
     apply (rule ccorres_cond)
       apply (clarsimp simp: from_bool_def split: bool.split)
      \<comment> \<open>blocking case\<close>
      apply (intro ccorres_rhs_assoc)
      apply csymbr
      \<comment> \<open>apply (ctac (no_vcg,c_lines 6) add: sendIPC_block_ccorres_helper)\<close>
      apply (rule ccorres_rhs_assoc2)
      apply (rule ccorres_rhs_assoc2)
      apply (rule ccorres_rhs_assoc2)
      apply (rule ccorres_rhs_assoc2)
      apply (rule ccorres_rhs_assoc2)
      apply (rule ccorres_rhs_assoc2)
      apply (rename_tac list)
      apply (rule ccorres_split_nothrow_novcg)
          apply (simp only: )
          apply (rule sendIPC_block_ccorres_helper)
         apply ceqv
        apply (simp only: K_bind_def fun_app_def)
        apply (rule_tac ep="SendEP list" in sendIPC_enqueue_ccorres_helper)
       apply (simp add: valid_ep'_def)
       apply (wp sts_st_tcb')
      apply (clarsimp simp: obj_at'_def ko_wp_at'_def projectKOs)
      apply (clarsimp simp: guard_is_UNIV_def)
     apply (rule ccorres_return_Skip)
    apply (clarsimp simp: EPState_Recv_def EPState_Send_def EPState_Idle_def
                   split: if_split)
    apply (frule(1) ko_at_valid_objs'[OF _ invs_valid_objs'])
     apply (clarsimp simp: projectKO_opt_ep split: kernel_object.split_asm)
    apply (subgoal_tac "epptr \<noteq> thread \<and> bound_tcb_at' (\<lambda>x. tcb_bound_refs' x =
                          state_refs_of' s thread) thread s \<and> (\<forall>r. (thread, r) \<notin>
                            ep_q_refs_of' ep)")
     apply (clarsimp simp: valid_obj'_def valid_ep'_def refs_of'_def
                    split: endpoint.splits)
       apply (frule(1) sym_refs_obj_atD'[OF _ invs_sym'])
       apply (clarsimp simp: st_tcb_at_refs_of_rev' isBlockedOnReceive_def)
       apply (auto split: list.splits elim!: pred_tcb'_weakenE)[1]
      apply (subgoal_tac "state_refs_of' s epptr = {}")
       apply (clarsimp simp: obj_at'_def is_aligned_neg_mask objBitsKO_def
                             projectKOs invs'_def valid_state'_def objBits_simps'
                             st_tcb_at'_def valid_tcb_state'_def ko_wp_at'_def
                             isBlockedOnSend_def projectKO_opt_tcb
                      split: if_split_asm if_split)
       apply (rule conjI, simp, rule impI, clarsimp simp: valid_pspace'_def)
       apply (erule delta_sym_refs)
        apply (clarsimp split: if_split_asm
                        dest!: symreftype_inverse')+
        apply (clarsimp simp: pred_tcb_at'_def obj_at'_def tcb_bound_refs'_def
                              projectKOs eq_sym_conv
                       dest!: symreftype_inverse'
                       split: if_split_asm)
       apply (clarsimp simp: pred_tcb_at'_def obj_at'_def projectKOs
                             tcb_bound_refs'_def eq_sym_conv)
      apply (clarsimp simp: obj_at'_def state_refs_of'_def projectKOs)
     apply (frule(1) sym_refs_obj_atD'[OF _ invs_sym'])
     apply clarsimp
     apply (rule conjI, assumption)
     apply (clarsimp dest!: st_tcb_strg'[rule_format]
                      simp: invs'_def valid_state'_def obj_at'_def objBits_simps'
                            projectKOs valid_tcb_state'_def)
     apply (rule conjI[rotated])
      apply (rule conjI[rotated])
       apply (clarsimp simp: isBlockedOnSend_def ko_wp_at'_def obj_at'_def
                             projectKOs projectKO_opt_tcb objBits_simps')
       apply (fastforce split: if_split_asm
                         elim: delta_sym_refs
                         simp: pred_tcb_at'_def obj_at'_def projectKOs
                               tcb_bound_refs'_def eq_sym_conv symreftype_def)
      apply (clarsimp simp: valid_pspace'_def)
     apply clarsimp
    apply (frule(1) sym_refs_obj_atD'[OF _ invs_sym'])
    apply (frule simple_st_tcb_at_state_refs_ofD')
    apply (case_tac ep, auto simp: st_tcb_at_refs_of_rev' st_tcb_at'_def
                                   obj_at'_def projectKOs)[1]
   apply (clarsimp simp: guard_is_UNIV_def)
  apply (clarsimp simp: guard_is_UNIV_def)
  done

lemma ctcb_relation_blockingIPCCanGrantReplyD:
  "\<lbrakk> ctcb_relation ko ko' ; isSend (tcbState ko) \<rbrakk>
   \<Longrightarrow> blockingIPCCanGrantReply_CL (thread_state_lift (tcbState_C ko'))
      = from_bool (blockingIPCCanGrantReply (tcbState ko))"
  apply ( case_tac "tcbState ko" ; clarsimp simp: isReceive_def isSend_def)
  apply (clarsimp simp: ctcb_relation_def cthread_state_relation_def
                        thread_state_lift_def from_bool_to_bool_iff mask_eq1_nochoice)+
  done

lemma receiveIPC_block_ccorres_helper:
  "ccorres dc xfdc (tcb_at' thread and valid_queues and valid_objs' and pspace_canonical' and
                    sch_act_not thread and ep_at' epptr and
                    (\<lambda>s. sch_act_wf (ksSchedulerAction s) s \<and>
                     (\<forall>d p. thread \<notin> set (ksReadyQueues s (d, p)))) and
                    K (epptr = epptr && ~~ mask 4) and
                    K (isEndpointCap cap \<and> ccap_relation cap cap'))
                   UNIV hs
           (setThreadState (Structures_H.thread_state.BlockedOnReceive
                                epptr (capEPCanGrant cap)) thread)
           (Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t tcb_ptr_to_ctcb_ptr thread\<rbrace>
             (CALL thread_state_ptr_set_tsType(Ptr
              &(tcb_ptr_to_ctcb_ptr thread\<rightarrow>[''tcbState_C'']),
              scast ThreadState_BlockedOnReceive));;
            Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t tcb_ptr_to_ctcb_ptr thread\<rbrace>
             (CALL thread_state_ptr_set_blockingObject(Ptr
                           &(tcb_ptr_to_ctcb_ptr thread\<rightarrow>[''tcbState_C'']),
              ucast (ptr_val (ep_Ptr epptr))));;
           \<acute>ret__unsigned_longlong :== CALL cap_endpoint_cap_get_capCanGrant(cap');;
           (Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t tcb_ptr_to_ctcb_ptr thread\<rbrace>
             (CALL thread_state_ptr_set_blockingIPCCanGrant(Ptr
              &(tcb_ptr_to_ctcb_ptr thread\<rightarrow>[''tcbState_C'']),
              \<acute>ret__unsigned_longlong)));;
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
        apply (clarsimp simp: typ_heap_simps' rf_sr_tcb_update_twice cap_get_tag_isCap
                        simp flip: canonical_bit_def)
        apply (erule(1) rf_sr_tcb_update_no_queue_gen, (simp add: typ_heap_simps)+)
         apply (simp add: tcb_cte_cases_def cteSizeBits_def)
        apply (simp add: ctcb_relation_def cthread_state_relation_def ccap_relation_ep_helpers
                         ThreadState_defs mask_def cap_get_tag_isCap)
        apply (clarsimp simp: canonical_address_sign_extended sign_extended_iff_sign_extend)
       apply ceqv
      apply clarsimp
      apply ctac
     apply (wp threadSet_valid_queues hoare_vcg_all_lift threadSet_valid_objs'
               threadSet_weak_sch_act_wf_runnable')
    apply (clarsimp simp: guard_is_UNIV_def)
   apply (clarsimp simp: sch_act_wf_weak valid_tcb'_def valid_tcb_state'_def
                         tcb_cte_cases_def obj_at'_is_canonical cteSizeBits_def)
  apply clarsimp
  done

lemma receiveIPC_enqueue_ccorres_helper:
  "ccorres dc xfdc (valid_pspace'
                and (\<lambda>s. sym_refs ((state_refs_of' s)(epptr := set queue \<times> {EPRecv})))
                and st_tcb_at'  (\<lambda>st. isBlockedOnReceive st \<and>
                                      blockingObject st = epptr) thread
                and ko_at' (ep::Structures_H.endpoint) epptr
                and K ((ep = IdleEP \<and> queue = [thread]) \<or>
                       (\<exists>q. ep = RecvEP q \<and> thread \<notin> set q \<and>
                            queue = q @ [thread])))
           UNIV hs
           (setEndpoint epptr (Structures_H.endpoint.RecvEP queue))
           (\<acute>queue :== CALL ep_ptr_get_queue(ep_Ptr epptr);;
            (\<acute>queue :== CALL tcbEPAppend(tcb_ptr_to_ctcb_ptr thread,\<acute>queue);;
             (CALL endpoint_ptr_set_state(ep_Ptr epptr, scast EPState_Recv);;
              CALL ep_ptr_set_queue(ep_Ptr epptr,\<acute>queue))))"
  unfolding K_def
  apply (rule ccorres_gen_asm)
  apply (rule ccorres_from_vcg)
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp split del: if_split)
  apply (frule cmap_relation_ep)
  apply (erule (1) cmap_relation_ko_atE)
  apply (rule conjI)
   apply (erule h_t_valid_clift)
  apply (frule(1) st_tcb_at_h_t_valid)
  apply (frule pred_tcb_at')
  apply (rule impI)
  apply (rule_tac x="init queue" in exI)
  apply (frule(1) ko_at_valid_ep' [OF _ valid_pspace_valid_objs'])
  apply (frule is_aligned_tcb_ptr_to_ctcb_ptr)
  apply (rule conjI)
   apply (rule_tac x=\<sigma> in exI)
   apply (simp add: cendpoint_relation_def Let_def)
   apply (case_tac ep, simp_all add: init_def valid_ep'_def)[1]
  apply (subgoal_tac "sym_refs (state_refs_of' (\<sigma>\<lparr>ksPSpace :=
                          (ksPSpace \<sigma>)(epptr \<mapsto> KOEndpoint (RecvEP queue))\<rparr>))")
   prefer 2
   apply (clarsimp simp: state_refs_of'_upd ko_wp_at'_def
                         obj_at'_def projectKOs objBitsKO_def)
  apply (subgoal_tac "ko_at' (RecvEP queue) epptr (\<sigma>\<lparr>ksPSpace :=
                          (ksPSpace \<sigma>)(epptr \<mapsto> KOEndpoint (RecvEP queue))\<rparr>)")
   prefer 2
   apply (clarsimp simp: obj_at'_def projectKOs objBitsKO_def ps_clear_upd)
  apply (intro conjI impI allI)
     apply (fastforce simp: h_t_valid_clift)
    apply (fastforce simp: h_t_valid_clift)
   apply (fastforce simp: h_t_valid_clift)
  apply (case_tac ep, simp_all add: EPState_Idle_def EPState_Recv_def)[1]
   \<comment> \<open>RecvEP case\<close>
   apply clarsimp
   apply (frule null_ep_queue [simplified comp_def] null_ep_queue)
   apply (simp add: setEndpoint_def split_def)
   apply (rule bexI [OF _ setObject_eq])
       apply (simp add: rf_sr_def cstate_relation_def Let_def init_def
                        cpspace_relation_def update_ep_map_tos
                        typ_heap_simps')
       apply (elim conjE)
       apply (intro conjI)
             \<comment> \<open>tcb relation\<close>
            apply (erule ctcb_relation_null_queue_ptrs)
            apply (clarsimp simp: comp_def)
           \<comment> \<open>ep relation\<close>
           apply (rule cpspace_relation_ep_update_ep', assumption+)
            apply (clarsimp simp: cendpoint_relation_def Let_def
                                  mask_def [where n=3] EPState_Recv_def
                           split: if_split)
            subgoal
              apply (clarsimp simp: tcb_queue_relation'_def is_aligned_neg_mask
                                  valid_ep'_def
                            dest: tcb_queue_relation_next_not_NULL)
              apply (rule conjI, clarsimp)
               apply (rule conjI, fastforce simp: mask_def)
               apply (clarsimp simp: valid_pspace'_def objBits_simps' simp flip: canonical_bit_def)
               apply (erule (1) tcb_and_not_mask_canonical)
               apply (simp (no_asm) add: tcbBlockSizeBits_def)
              apply (clarsimp simp: valid_pspace'_def objBits_simps' simp flip: canonical_bit_def)
              apply (rule conjI, solves \<open>simp (no_asm) add: mask_def\<close>)
              apply (erule (1) tcb_and_not_mask_canonical)
              apply (simp (no_asm) add: tcbBlockSizeBits_def)
              done
           apply (simp add: isSendEP_def isRecvEP_def)
          \<comment> \<open>ntfn relation\<close>
          apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
          apply simp
          apply (rule cnotification_relation_ep_queue, assumption+)
            apply (simp add: isSendEP_def isRecvEP_def)
           apply simp
          apply (frule_tac x=p in map_to_ko_atI, clarsimp, clarsimp)
          apply (erule(2) map_to_ko_at_updI')
           apply (clarsimp simp: objBitsKO_def)
          apply (clarsimp simp: obj_at'_def projectKOs)
         \<comment> \<open>queue relation\<close>
         apply (rule cready_queues_relation_null_queue_ptrs, assumption+)
         apply (clarsimp simp: comp_def)
        apply (clarsimp simp: carch_state_relation_def packed_heap_update_collapse_hrs)
       apply (simp add: cmachine_state_relation_def)
      apply (simp add: h_t_valid_clift_Some_iff)
     apply (simp add: objBits_simps')
    apply (simp add: objBits_simps)
   apply assumption
  \<comment> \<open>IdleEP case\<close>
  apply clarsimp
  apply (frule null_ep_queue [simplified comp_def] null_ep_queue)
  apply (simp add: setEndpoint_def split_def)
  apply (rule bexI [OF _ setObject_eq])
      apply (simp add: rf_sr_def cstate_relation_def init_def Let_def
                       cpspace_relation_def update_ep_map_tos
                       typ_heap_simps')
      apply (elim conjE)
      apply (intro conjI)
           \<comment> \<open>tcb relation\<close>
           apply (erule ctcb_relation_null_queue_ptrs)
           apply (clarsimp simp: comp_def)
          \<comment> \<open>ep relation\<close>
          apply (rule cpspace_relation_ep_update_ep', assumption+)
           apply (clarsimp simp: cendpoint_relation_def Let_def
                                 mask_def [where n=3] EPState_Recv_def)
           apply (clarsimp simp: tcb_queue_relation'_def is_aligned_neg_mask
                           simp flip: canonical_bit_def)
           subgoal
             apply (rule conjI, solves\<open>simp (no_asm) add: mask_def\<close>)
             apply (clarsimp simp: valid_pspace'_def)
             apply (erule (1) tcb_and_not_mask_canonical, simp (no_asm) add: tcbBlockSizeBits_def)
             done
          apply (simp add: isSendEP_def isRecvEP_def)
         \<comment> \<open>ntfn relation\<close>
         apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
         apply simp
         apply (rule cnotification_relation_ep_queue, assumption+)
           apply (simp add: isSendEP_def isRecvEP_def)
          apply simp
         apply (frule_tac x=p in map_to_ko_atI, clarsimp, clarsimp)
         apply (erule(2) map_to_ko_at_updI')
          apply (clarsimp simp: objBitsKO_def)
         apply (clarsimp simp: obj_at'_def projectKOs)
        \<comment> \<open>queue relation\<close>
        apply (rule cready_queues_relation_null_queue_ptrs, assumption+)
        apply (clarsimp simp: comp_def)
       apply (clarsimp simp: carch_state_relation_def packed_heap_update_collapse_hrs)
      apply (simp add: cmachine_state_relation_def)
     apply (simp add: typ_heap_simps')
    apply (simp add: objBits_simps')
   apply (simp add: objBits_simps)
  apply assumption
  done

lemma receiveIPC_dequeue_ccorres_helper:
  "ccorres (\<lambda>rv rv'. rv' = tcb_ptr_to_ctcb_ptr sender) sender_'
           (invs' and st_tcb_at' (\<lambda>st. isBlockedOnSend st \<and>
                                       blockingObject st = ep) sender
                  and ko_at' (SendEP (sender#rest)) ep) UNIV hs
           (setEndpoint ep (case rest of [] \<Rightarrow> Structures_H.IdleEP
                                       | (a#list) \<Rightarrow> Structures_H.SendEP rest))
        (\<acute>queue :== CALL ep_ptr_get_queue(Ptr ep);;
         \<acute>sender :== head_C \<acute>queue;;
         \<acute>queue :== CALL tcbEPDequeue(\<acute>sender,\<acute>queue);;
         CALL ep_ptr_set_queue(Ptr ep,\<acute>queue);;
         IF head_C \<acute>queue = Ptr 0 THEN
             CALL endpoint_ptr_set_state(Ptr ep,scast EPState_Idle)
         FI)"
  apply (rule ccorres_from_vcg)
  apply (rule allI)
  apply (rule conseqPre, vcg)
  apply (clarsimp split del: if_split)
  apply (frule ep_blocked_in_queueD [OF pred_tcb'_weakenE])
     apply simp
    apply assumption+
  apply (frule (1) ko_at_valid_ep' [OF _ invs_valid_objs'])
  apply (elim conjE)
  apply (frule (1) valid_ep_blockedD)
  apply (elim conjE)
  apply (frule cmap_relation_ep)
  apply (erule (1) cmap_relation_ko_atE)
  apply (intro conjI)
   apply (erule h_t_valid_clift)
  apply (rule impI)
  apply (rule exI)
  apply (rule conjI)
   apply (rule_tac x=\<sigma> in exI)
   apply (intro conjI)
       apply assumption+
    apply (drule (2) ep_to_ep_queue)
    apply (simp add: tcb_queue_relation'_def)
   apply (clarsimp simp: typ_heap_simps cendpoint_relation_def Let_def
                   cong: imp_cong split del: if_split)
  apply (intro conjI impI allI)
      apply (fastforce simp: h_t_valid_clift)
     apply (fastforce simp: h_t_valid_clift)
    apply (fastforce simp: h_t_valid_clift)
   \<comment> \<open>empty case\<close>
   apply clarsimp
   apply (frule null_ep_queue [simplified comp_def] null_ep_queue)
   apply (frule iffD1 [OF tcb_queue_head_empty_iff
                          [OF tcb_queue_relation'_queue_rel]])
     apply (rule ballI, erule bspec)
     apply (erule subsetD [rotated])
     apply (clarsimp simp: cendpoint_relation_def Let_def tcb_queue_relation'_def)
    apply simp
   apply (simp add: setEndpoint_def split_def)
   apply (rule conjI)
    apply (rule bexI [OF _ setObject_eq])
        apply (simp add: rf_sr_def cstate_relation_def Let_def
                         cpspace_relation_def update_ep_map_tos
                         typ_heap_simps')
        apply (elim conjE)
        apply (intro conjI)
             \<comment> \<open>tcb relation\<close>
             apply (erule ctcb_relation_null_queue_ptrs)
             apply (clarsimp simp: comp_def)
            \<comment> \<open>ep relation\<close>
            apply (rule cpspace_relation_ep_update_ep, assumption+)
             apply (simp add: cendpoint_relation_def Let_def EPState_Idle_def
                              tcb_queue_relation'_def)
            apply simp
           \<comment> \<open>ntfn relation\<close>
           apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
           apply simp
           apply (rule cnotification_relation_ep_queue [OF invs_sym'], assumption+)
           apply simp
          apply (erule (1) map_to_ko_atI')
          \<comment> \<open>queue relation\<close>
          apply (rule cready_queues_relation_null_queue_ptrs, assumption+)
          apply (clarsimp simp: comp_def)
         apply (clarsimp simp: carch_state_relation_def packed_heap_update_collapse_hrs)
        apply (simp add: cmachine_state_relation_def)
       apply (simp add: typ_heap_simps')
      apply (simp add: objBits_simps')
     apply (simp add: objBits_simps)
    apply assumption
   apply (clarsimp simp: cendpoint_relation_def Let_def tcb_queue_relation'_def)
  \<comment> \<open>non-empty case\<close>
  apply clarsimp
  apply (frule null_ep_queue [simplified comp_def] null_ep_queue)
  apply (frule tcb_queue_head_empty_iff [OF tcb_queue_relation'_queue_rel])
   apply (rule ballI, erule bspec)
   apply (erule subsetD [rotated])
   apply (clarsimp simp: cendpoint_relation_def Let_def tcb_queue_relation'_def)
  apply (simp add: setEndpoint_def split_def)
  apply (rule conjI)
   apply (rule bexI [OF _ setObject_eq])
       apply (frule(1) st_tcb_at_h_t_valid)
       apply (simp add: rf_sr_def cstate_relation_def Let_def
                        cpspace_relation_def update_ep_map_tos
                        typ_heap_simps')
       apply (elim conjE)
       apply (intro conjI)
            \<comment> \<open>tcb relation\<close>
            apply (erule ctcb_relation_null_queue_ptrs)
            apply (clarsimp simp: comp_def)
           \<comment> \<open>ep relation\<close>
           apply (rule cpspace_relation_ep_update_ep, assumption+)
            apply (clarsimp simp: cendpoint_relation_def Let_def
                                  isRecvEP_def isSendEP_def
                                  tcb_queue_relation'_def valid_ep'_def
                       simp flip: canonical_bit_def
                           split: endpoint.splits list.splits
                       split del: if_split)
            apply (subgoal_tac "tcb_at' (if x22 = [] then x21 else last x22) \<sigma>")
             apply (erule (1) tcb_and_not_mask_canonical[OF invs_pspace_canonical'])
             apply (clarsimp simp: objBits_simps')
            apply (clarsimp split: if_split)
           apply simp
          \<comment> \<open>ntfn relation\<close>
          apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
          apply simp
          apply (rule cnotification_relation_ep_queue [OF invs_sym'], assumption+)
           apply simp
          apply (erule (1) map_to_ko_atI')
         \<comment> \<open>queue relation\<close>
         apply (rule cready_queues_relation_null_queue_ptrs, assumption+)
         apply (clarsimp simp: comp_def)
        apply (clarsimp simp: carch_state_relation_def packed_heap_update_collapse_hrs)
       apply (simp add: cmachine_state_relation_def)
      apply (simp add: typ_heap_simps')
     apply (simp add: objBits_simps')
    apply (simp add: objBits_simps)
   apply assumption
  apply (clarsimp simp: cendpoint_relation_def Let_def tcb_queue_relation'_def)
  done

lemmas ccorres_pre_getBoundNotification = ccorres_pre_threadGet[where f=tcbBoundNotification, folded getBoundNotification_def]

lemma completeSignal_ccorres:
  notes if_split[split del]
  shows
  "ccorres dc xfdc (invs' and tcb_at' thread)
     (UNIV \<inter> \<lbrace>\<acute>tcb = tcb_ptr_to_ctcb_ptr thread\<rbrace>
           \<inter> \<lbrace>\<acute>ntfnPtr = Ptr ntfnptr\<rbrace>) hs
     (completeSignal ntfnptr thread)
     (Call completeSignal_'proc)"
   apply (cinit lift: tcb_' ntfnPtr_')
   apply (rule_tac P="invs' and tcb_at' thread" in ccorres_gen_asm_state)
   apply clarsimp
   apply (subgoal_tac "tcb_ptr_to_ctcb_ptr thread \<noteq> NULL")
    prefer 2
    apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def
                          tcb_ptr_to_ctcb_ptr_def objBits_simps')
    apply (drule sum_to_zero)
    apply (clarsimp simp: obj_at'_def ctcb_offset_defs projectKOs objBitsKO_def
                          is_aligned_def objBits_simps')
   apply clarsimp
   apply csymbr
   apply simp
   apply (rule ccorres_rhs_assoc)+
   apply (rule ccorres_pre_getNotification, rename_tac ntfn)
   apply (rule_tac xf'=ret__unsigned_longlong_'
                and val="case ntfnObj ntfn of IdleNtfn \<Rightarrow> scast NtfnState_Idle
                                  | WaitingNtfn _ \<Rightarrow> scast NtfnState_Waiting
                                  | ActiveNtfn _ \<Rightarrow> scast NtfnState_Active"
                and R="ko_at' ntfn ntfnptr"
                 in ccorres_symb_exec_r_known_rv_UNIV[where R'=UNIV])
      apply vcg
      apply clarsimp
      apply (erule(1) cmap_relation_ko_atE [OF cmap_relation_ntfn])
      apply (clarsimp simp: cnotification_relation_def Let_def typ_heap_simps
                     split: Structures_H.ntfn.splits)
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
     apply (rename_tac word)
     apply (rule ccorres_rhs_assoc2)
     apply (rule_tac val=word and xf'=badge_' and R="ko_at' ntfn ntfnptr"
                   in ccorres_symb_exec_r_known_rv_UNIV[where R'=UNIV])
        apply (vcg, clarsimp)
        apply (erule(1) cmap_relation_ko_atE[OF cmap_relation_ntfn])
        apply (clarsimp simp: cnotification_relation_def Let_def typ_heap_simps)
       apply ceqv
      apply (ctac(no_vcg))
       apply (rule_tac P="invs' and ko_at' ntfn ntfnptr" and P'=UNIV in ccorres_from_vcg)
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp)
       apply (frule(1) cmap_relation_ko_atD [OF cmap_relation_ntfn])
       apply (clarsimp simp: typ_heap_simps setNotification_def)
       apply (rule bexI [OF _ setObject_eq])
           apply (simp add: rf_sr_def cstate_relation_def Let_def update_ntfn_map_tos
                            cpspace_relation_def typ_heap_simps')
           apply (elim conjE)
           apply (intro conjI)
             apply (rule cpspace_relation_ntfn_update_ntfn, assumption+)
              apply (simp add: cnotification_relation_def Let_def NtfnState_Idle_def mask_def)
             apply simp
            apply (clarsimp simp: carch_state_relation_def)
           apply (simp add: cmachine_state_relation_def)
          apply (simp add: h_t_valid_clift_Some_iff)
         apply (simp add: objBits_simps')
        apply (simp add: objBits_simps)
       apply assumption
      apply wp
     apply (clarsimp simp: guard_is_UNIV_def RISCV64_H.badgeRegister_def
                           RISCV64.badgeRegister_def C_register_defs
                           RISCV64.capRegister_def)
    \<comment> \<open>WaitingNtfn case\<close>
    apply (clarsimp simp: NtfnState_Active_def NtfnState_Waiting_def)
    apply csymbr
    apply (rule ccorres_cond_false)
    apply (rule ccorres_fail)
   apply (clarsimp simp: guard_is_UNIV_def)
  apply (clarsimp)
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

lemma receiveIPC_ccorres [corres]:
  notes option.case_cong_weak [cong]
  shows
  "ccorres dc xfdc (invs' and st_tcb_at' simple' thread and sch_act_not thread
                          and (\<lambda>s. \<forall>d p. thread \<notin> set (ksReadyQueues s (d, p)))
                          and valid_cap' cap and K (isEndpointCap cap))
     (UNIV \<inter> \<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr thread\<rbrace>
           \<inter> \<lbrace>ccap_relation cap \<acute>cap\<rbrace>
           \<inter> \<lbrace>\<acute>isBlocking = from_bool isBlocking\<rbrace>) hs
     (receiveIPC thread cap isBlocking)
     (Call receiveIPC_'proc)"
  unfolding K_def
  apply (rule ccorres_gen_asm)
  apply (cinit lift: thread_' cap_' isBlocking_')
   apply (rule ccorres_pre_getEndpoint)
   apply (rename_tac ep)
   apply (simp only: ccorres_seq_skip)
   apply (rule_tac xf'=ret__unsigned_longlong_'
               and val="capEPPtr cap"
               and R=\<top>
                in ccorres_symb_exec_r_known_rv_UNIV[where R'=UNIV])
      apply vcg
      apply (clarsimp simp: cap_get_tag_isCap isCap_simps)
      apply (frule cap_get_tag_isCap_unfolded_H_cap)
      apply (simp add: cap_endpoint_cap_lift ccap_relation_def cap_to_H_def)
     apply ceqv
    apply csymbr
    apply (rule ccorres_move_c_guard_tcb)
    apply (rule_tac xf'=ntfnPtr_'
                and r'="\<lambda>rv rv'. rv' = option_to_ptr rv \<and> rv \<noteq> Some 0"
                in ccorres_split_nothrow_novcg)
        apply (simp add: getBoundNotification_def)
        apply (rule_tac P="no_0_obj' and valid_objs'" in threadGet_vcg_corres_P)
        apply (rule allI, rule conseqPre, vcg)
        apply clarsimp
        apply (drule obj_at_ko_at', clarsimp)
        apply (drule spec, drule(1) mp, clarsimp)
        apply (clarsimp simp: typ_heap_simps ctcb_relation_def)
        apply (drule(1) ko_at_valid_objs', simp add: projectKOs)
        apply (clarsimp simp: option_to_ptr_def option_to_0_def projectKOs
                              valid_obj'_def valid_tcb'_def)
       apply ceqv
      apply (rename_tac ntfnptr ntfnptr')
      apply (simp del: Collect_const split del: if_split cong: call_ignore_cong)
      apply (rule ccorres_rhs_assoc2)
      apply (rule_tac xf'=ret__int_'
                   and r'="\<lambda>rv rv'. (rv' = 0) = (ntfnptr = None \<or> \<not> isActive rv)"
                    in ccorres_split_nothrow_novcg)
          apply wpc
           apply (rule ccorres_from_vcg[where P=\<top> and P'=UNIV])
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp: option_to_ptr_def option_to_0_def in_monad Bex_def)
          apply (rule ccorres_pre_getNotification[where f=return, simplified])
          apply (rule_tac P="\<lambda>s. ko_at' rv (the ntfnptr) s"
                     in ccorres_from_vcg[where P'=UNIV])
          apply (rule allI, rule conseqPre, vcg)
          apply (clarsimp simp: option_to_ptr_def option_to_0_def in_monad Bex_def)
          apply (erule cmap_relationE1[OF cmap_relation_ntfn])
           apply (erule ko_at_projectKO_opt)
          apply (clarsimp simp: typ_heap_simps cnotification_relation_def Let_def
                                notification_state_defs isActive_def
                         split: Structures_H.ntfn.split_asm Structures_H.notification.splits)
         apply ceqv
        apply (rule ccorres_cond[where R=\<top>])
          apply (simp add: Collect_const_mem)
         apply (ctac add: completeSignal_ccorres)
        apply (rule_tac xf'=ret__unsigned_longlong_'
                    and val="case ep of IdleEP \<Rightarrow> scast EPState_Idle
                            | RecvEP _ \<Rightarrow> scast EPState_Recv
                            | SendEP _ \<Rightarrow> scast EPState_Send"
                    and R="ko_at' ep (capEPPtr cap)"
                    in ccorres_symb_exec_r_known_rv_UNIV[where R'=UNIV])
           apply (vcg, clarsimp)
           apply (erule cmap_relationE1 [OF cmap_relation_ep])
            apply (erule ko_at_projectKO_opt)
           apply (clarsimp simp: typ_heap_simps cendpoint_relation_def Let_def
                          split: endpoint.split_asm)
          apply ceqv
         apply (rule_tac A="invs' and st_tcb_at' simple' thread
                                  and sch_act_not thread
                              and (\<lambda>s. \<forall>d p. thread \<notin> set (ksReadyQueues s (d, p)))
                                  and ko_at' ep (capEPPtr cap)"
                     in ccorres_guard_imp2 [where A'=UNIV])
           apply wpc
            \<comment> \<open>RecvEP case\<close>
            apply (rule ccorres_cond_true)
            apply csymbr
            apply (simp only: case_bool_If from_bool_neq_0)
            apply (rule ccorres_Cond_rhs, simp cong: Collect_cong split del: if_split)
             apply (intro ccorres_rhs_assoc)
             apply (rule ccorres_rhs_assoc2)
             apply (rule ccorres_rhs_assoc2)
             apply (rule ccorres_rhs_assoc2)
             apply (rule ccorres_rhs_assoc2)
             apply (rule ccorres_split_nothrow_novcg)
                 apply (rule receiveIPC_block_ccorres_helper[unfolded ptr_val_def, simplified])
                apply ceqv
               apply simp
               apply (rename_tac list NOo)
               apply (rule_tac ep="RecvEP list" in receiveIPC_enqueue_ccorres_helper[simplified])
              apply (simp add: valid_ep'_def)
              apply (wp sts_st_tcb')
             apply (rename_tac list)
             apply (clarsimp simp: obj_at'_def ko_wp_at'_def projectKOs)
             apply (clarsimp simp: guard_is_UNIV_def)
            apply simp
             apply (ctac add: doNBRecvFailedTransfer_ccorres)
           \<comment> \<open>IdleEP case\<close>
           apply (rule ccorres_cond_true)
           apply csymbr
           apply (simp only: case_bool_If from_bool_neq_0)
           apply (rule ccorres_Cond_rhs, simp cong: Collect_cong split del: if_split)
            apply (intro ccorres_rhs_assoc)
            apply (rule ccorres_rhs_assoc2)
            apply (rule ccorres_rhs_assoc2)
            apply (rule ccorres_rhs_assoc2)
            apply (rule ccorres_rhs_assoc2)
            apply (rule ccorres_split_nothrow_novcg)
                apply (rule receiveIPC_block_ccorres_helper[unfolded ptr_val_def, simplified])
               apply ceqv
              apply simp
              apply (rule_tac ep=IdleEP in receiveIPC_enqueue_ccorres_helper[simplified])
             apply (simp add: valid_ep'_def)
             apply (wp sts_st_tcb')
            apply (clarsimp simp: obj_at'_def ko_wp_at'_def projectKOs)
            apply (clarsimp simp: guard_is_UNIV_def)
           apply simp
            apply (ctac add: doNBRecvFailedTransfer_ccorres)
           \<comment> \<open>SendEP case\<close>
          apply (thin_tac "isBlockinga = from_bool P" for P)
          apply (rule ccorres_cond_false)
          apply (rule ccorres_cond_true)
          apply (intro ccorres_rhs_assoc)
          apply (csymbr, csymbr, csymbr, csymbr, csymbr)
          apply wpc
           apply (simp only: haskell_fail_def)
           apply (rule ccorres_fail)
          apply (rename_tac sender rest)
          apply csymbr
          apply (rule ccorres_rhs_assoc2)
          apply (rule ccorres_rhs_assoc2)
          apply (rule ccorres_rhs_assoc2)
          apply (rule ccorres_rhs_assoc2)
          apply (rule ccorres_split_nothrow_novcg)
              apply simp
              apply (rule_tac sender=sender in receiveIPC_dequeue_ccorres_helper[simplified])
             apply ceqv
            apply (rename_tac sender')
            apply (simp only: K_bind_def haskell_assert_def return_bind)
            apply (rule ccorres_move_c_guard_tcb)
            apply (rule getThreadState_ccorres_foo)
            apply (rename_tac sendState)
            apply (rule ccorres_assert)
            apply (rule ccorres_rhs_assoc2)
            apply (rule_tac val="blockingIPCBadge sendState"
                        and xf'=badge_'
                        and R="\<lambda>s. \<exists>t. ko_at' t sender s \<and> tcbState t = sendState"
                         in ccorres_symb_exec_r_known_rv_UNIV [where R'=UNIV])
               apply (vcg, clarsimp)
               apply (erule(1) cmap_relation_ko_atE [OF cmap_relation_tcb])
               apply (clarsimp simp: ctcb_relation_def typ_heap_simps
                                     cthread_state_relation_def word_size
                                     isSend_def thread_state_lift_def
                              split: Structures_H.thread_state.splits)
              apply ceqv
             apply (simp split del: if_split)
             apply (rule ccorres_move_c_guard_tcb)
             apply (rule ccorres_rhs_assoc2)
             apply (rule_tac val="from_bool (blockingIPCCanGrant sendState)"
                         and xf'=canGrant_'
                         and R="\<lambda>s. \<exists>t. ko_at' t sender s \<and> tcbState t = sendState"
                          in ccorres_symb_exec_r_known_rv_UNIV [where R'=UNIV])
                apply (vcg, clarsimp)
                apply (erule(1) cmap_relation_ko_atE [OF cmap_relation_tcb])
                apply (clarsimp simp: ctcb_relation_def typ_heap_simps
                                      cthread_state_relation_def word_size
                                      isSend_def thread_state_lift_def
                               split: Structures_H.thread_state.splits)
               apply ceqv

              apply (rule ccorres_rhs_assoc2)
              apply (rule_tac xf'=canGrantReply_'
                       and val="from_bool (blockingIPCCanGrantReply sendState)"
                       and R="st_tcb_at' ((=) sendState) sender" and R'=UNIV
                        in ccorres_symb_exec_r_known_rv_UNIV)
                 apply (clarsimp, rule conseqPre, vcg)
                 apply (fastforce simp: pred_tcb_at'_def tcb_at_h_t_valid typ_heap_simps'
                                  dest: obj_at_cslift_tcb ctcb_relation_blockingIPCCanGrantReplyD)
                apply ceqv

               apply (ctac(no_vcg))
                apply (rule ccorres_move_c_guard_tcb)
                apply (rule ccorres_rhs_assoc2)
                apply (rule_tac val="from_bool (blockingIPCIsCall sendState)"
                            and xf'=do_call_'
                            and R="\<lambda>s. \<exists>t. ko_at' t sender s \<and> tcbState t = sendState"
                             in ccorres_symb_exec_r_known_rv_UNIV [where R'=UNIV])
                   apply (vcg, clarsimp)
                   apply (erule(1) cmap_relation_ko_atE [OF cmap_relation_tcb])
                   apply (clarsimp simp: ctcb_relation_def typ_heap_simps
                                         cthread_state_relation_def word_size
                                         isSend_def thread_state_lift_def
                                  split: Structures_H.thread_state.splits)
                  apply ceqv

                 apply (clarsimp simp:  from_bool_0 disj_imp[symmetric] simp del: Collect_const)
                 apply wpc
                  (* blocking ipc call *)
                  apply (clarsimp split del: if_split simp del: Collect_const)
                  apply ccorres_rewrite
                  apply (wpc ; clarsimp ; ccorres_rewrite)
                   apply csymbr
                   apply clarsimp
                   apply ctac
                  apply ctac
                 (* non-blocking ipc call *)
                 apply (clarsimp simp:  from_bool_0 disj_imp[symmetric] simp del: Collect_const)
                 apply ccorres_rewrite
                 apply ctac
                   apply (ctac add: possibleSwitchTo_ccorres)
                  apply (wpsimp wp: sts_st_tcb' sts_valid_queues)
                 apply (vcg exspec=setThreadState_modifies)
                apply (fastforce simp: guard_is_UNIV_def ThreadState_defs mask_def
                                       cap_get_tag_isCap ccap_relation_ep_helpers)
               apply (clarsimp simp: valid_tcb_state'_def)
               apply (rule_tac Q="\<lambda>_. valid_pspace' and valid_queues
                                       and st_tcb_at' ((=) sendState) sender and tcb_at' thread
                                       and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s)
                                       and (\<lambda>s. (\<forall>a b. sender \<notin> set (ksReadyQueues s (a, b))))
                                       and sch_act_not sender and K (thread \<noteq> sender)
                                       and (\<lambda>s. ksCurDomain s \<le> maxDomain)" in hoare_post_imp)
                apply (clarsimp simp: valid_pspace_valid_objs' pred_tcb_at'_def sch_act_wf_weak
                                      obj_at'_def)
               apply (wpsimp simp: guard_is_UNIV_def option_to_ptr_def option_to_0_def conj_ac)+
           apply (rule_tac Q="\<lambda>rv. valid_queues and valid_pspace'
                               and cur_tcb' and tcb_at' sender and tcb_at' thread
                               and sch_act_not sender and K (thread \<noteq> sender)
                               and ep_at' (capEPPtr cap)
                               and (\<lambda>s. ksCurDomain s \<le> maxDomain)
                               and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s \<and>
                                        (\<forall>d p. sender \<notin> set (ksReadyQueues s (d, p))))"
                            in hoare_post_imp)
            subgoal by (auto, auto simp: st_tcb_at'_def obj_at'_def)
           apply (wp hoare_vcg_all_lift set_ep_valid_objs')
          apply (clarsimp simp: guard_is_UNIV_def)
         apply (clarsimp simp: EPState_Recv_def EPState_Send_def EPState_Idle_def)
         apply (frule(1) ko_at_valid_objs' [OF _ invs_valid_objs'])
          apply (clarsimp simp: projectKO_opt_ep split: kernel_object.split_asm)
         apply (subgoal_tac "(capEPPtr cap) \<noteq> thread
                      \<and> state_refs_of' s thread = {r \<in> state_refs_of' s thread. snd r = TCBBound}")
          apply (clarsimp simp: valid_obj'_def valid_ep'_def refs_of'_def
                         split: endpoint.splits)
            apply (rename_tac list)
            apply (subgoal_tac "state_refs_of' s (capEPPtr cap) = (set list) \<times> {EPRecv}
                                \<and> thread \<notin> (set list)")
             subgoal by (fastforce simp: obj_at'_def is_aligned_neg_mask objBitsKO_def
                                         projectKOs invs'_def valid_state'_def st_tcb_at'_def
                                         valid_tcb_state'_def ko_wp_at'_def invs_valid_objs'
                                         isBlockedOnReceive_def projectKO_opt_tcb
                                         objBits_simps'
                                  elim!: delta_sym_refs
                                  split: if_split_asm bool.splits) (*very long*)
            apply (frule(1) sym_refs_obj_atD' [OF _ invs_sym'])
            apply (clarsimp simp: st_tcb_at'_def ko_wp_at'_def obj_at'_def projectKOs
                           split: if_split_asm)
            apply (drule(1) bspec)+
            apply (case_tac "tcbState obj", simp_all add: tcb_bound_refs'_def)[1]
           apply (subgoal_tac "state_refs_of' s (capEPPtr cap) = {}")
            subgoal by (fastforce simp: obj_at'_def is_aligned_neg_mask objBitsKO_def
                                        projectKOs invs'_def valid_state'_def st_tcb_at'_def
                                        valid_tcb_state'_def ko_wp_at'_def invs_valid_objs'
                                        isBlockedOnReceive_def projectKO_opt_tcb objBits_simps'
                                  elim: delta_sym_refs
                                 split: if_split_asm bool.splits) (*very long *)
           apply (clarsimp simp: obj_at'_def state_refs_of'_def projectKOs)
          apply (frule(1) sym_refs_ko_atD' [OF _ invs_sym'])
          apply (frule invs_queues)
          apply clarsimp
          apply (rename_tac list x xa)
          apply (rule_tac P="x\<in>set list" in case_split)
           apply (clarsimp simp:st_tcb_at_refs_of_rev')
           apply (erule_tac x=x and P="\<lambda>x. st_tcb_at' P x s" for P in ballE)
            apply (drule_tac t=x in valid_queues_not_runnable'_not_ksQ)
             apply (clarsimp simp: st_tcb_at'_def obj_at'_def)
            apply (subgoal_tac "sch_act_not x s")
             prefer 2
             apply (frule invs_sch_act_wf')
             apply (clarsimp simp:sch_act_wf_def)
             apply (clarsimp simp: st_tcb_at'_def obj_at'_def)
            apply (clarsimp simp: obj_at'_def st_tcb_at'_def
                                  projectKOs isBlockedOnSend_def
                            split: list.split | rule conjI)+
         apply (clarsimp simp: state_refs_of'_def )
         apply (case_tac "tcbState obj", clarsimp+)[1]
        apply (clarsimp simp: guard_is_UNIV_def)+
       apply (wp getNotification_wp | wpc)+
      apply (clarsimp simp add: guard_is_UNIV_def option_to_ptr_def option_to_0_def
                         split: if_split)
     apply (wp gbn_wp' | simp add: guard_is_UNIV_def)+
  apply (auto simp: isCap_simps valid_cap'_def)
  done

lemma sendSignal_dequeue_ccorres_helper:
  "ccorres (\<lambda>rv rv'. rv' = tcb_ptr_to_ctcb_ptr dest) dest___ptr_to_struct_tcb_C_'
           (invs' and st_tcb_at' ((=) (BlockedOnNotification ntfn)) dest
                  and ko_at' nTFN ntfn
                  and K (ntfnObj nTFN = WaitingNtfn (dest # rest))) UNIV hs
           (setNotification ntfn $ ntfnObj_update (\<lambda>_. case rest of [] \<Rightarrow> Structures_H.ntfn.IdleNtfn
                                        | (a#list) \<Rightarrow> Structures_H.ntfn.WaitingNtfn rest) nTFN)
        (\<acute>ntfn_queue :== CALL ntfn_ptr_get_queue(Ptr ntfn);;
         \<acute>dest___ptr_to_struct_tcb_C :== head_C \<acute>ntfn_queue;;
         \<acute>ntfn_queue :== CALL tcbEPDequeue(\<acute>dest___ptr_to_struct_tcb_C,\<acute>ntfn_queue);;
         CALL ntfn_ptr_set_queue(Ptr ntfn,\<acute>ntfn_queue);;
         IF head_C \<acute>ntfn_queue = Ptr 0 THEN
             CALL notification_ptr_set_state(Ptr ntfn,scast NtfnState_Idle)
         FI)"
  apply (rule ccorres_from_vcg)
  apply (rule allI)
  apply (rule conseqPre, vcg)
  apply (clarsimp split del: if_split)
  apply (frule (2) ntfn_blocked_in_queueD)
  apply (frule (1) ko_at_valid_ntfn' [OF _ invs_valid_objs'])
  apply (elim conjE)
  apply (frule (1) valid_ntfn_isWaitingNtfnD)
  apply (elim conjE)
  apply (frule cmap_relation_ntfn)
  apply (erule (1) cmap_relation_ko_atE)
  apply (intro conjI)
   apply (erule h_t_valid_clift)
  apply (rule impI)
  apply (rule exI)
  apply (rule conjI)
   apply (rule_tac x=\<sigma> in exI)
   apply (intro conjI)
       apply assumption+
    apply clarsimp
    apply (drule ntfn_to_ep_queue, (simp add: isWaitingNtfn_def)+)
    apply (simp add: tcb_queue_relation'_def)
   apply (clarsimp simp: typ_heap_simps cnotification_relation_def Let_def
                   cong: imp_cong split del: if_split)
  apply (intro conjI impI allI)
     apply (fastforce simp: h_t_valid_clift)
    apply (fastforce simp: h_t_valid_clift)
   \<comment> \<open>empty case\<close>
   apply clarsimp
   apply (frule null_ep_queue [simplified comp_def] null_ep_queue)
   apply (frule iffD1 [OF tcb_queue_head_empty_iff
                          [OF tcb_queue_relation'_queue_rel]])
     apply (rule ballI, erule bspec)
     apply (erule subsetD [rotated])
     apply (clarsimp simp: cnotification_relation_def Let_def
                           tcb_queue_relation'_def)
    apply simp
   apply (simp add: setNotification_def split_def)
   apply (rule conjI)
    apply (rule bexI [OF _ setObject_eq])
        apply (simp add: rf_sr_def cstate_relation_def Let_def
                         cpspace_relation_def update_ntfn_map_tos
                         typ_heap_simps')
        apply (elim conjE)
        apply (intro conjI)
             \<comment> \<open>tcb relation\<close>
             apply (erule ctcb_relation_null_queue_ptrs)
             apply (clarsimp simp: comp_def)
            \<comment> \<open>ep relation\<close>
            apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
            apply simp
            apply (rule cendpoint_relation_ntfn_queue [OF invs_sym'], assumption+)
             apply simp+
            apply (erule (1) map_to_ko_atI')
           \<comment> \<open>ntfn relation\<close>
           apply (rule cpspace_relation_ntfn_update_ntfn, assumption+)
            apply (simp add: cnotification_relation_def Let_def NtfnState_Idle_def
                             tcb_queue_relation'_def)
           apply simp
          \<comment> \<open>queue relation\<close>
          apply (rule cready_queues_relation_null_queue_ptrs, assumption+)
          apply (clarsimp simp: comp_def)
         apply (clarsimp simp: carch_state_relation_def packed_heap_update_collapse_hrs)
        apply (simp add: cmachine_state_relation_def)
       apply (simp add: h_t_valid_clift_Some_iff)
      apply (simp add: objBits_simps')
     apply (simp add: objBits_simps)
    apply assumption
   apply (clarsimp simp: cnotification_relation_def Let_def
                         tcb_queue_relation'_def)
  \<comment> \<open>non-empty case\<close>
  apply clarsimp
  apply (frule null_ep_queue [simplified comp_def] null_ep_queue)
  apply (frule tcb_queue_head_empty_iff [OF tcb_queue_relation'_queue_rel])
   apply (rule ballI, erule bspec)
   apply (erule subsetD [rotated])
   apply (clarsimp simp: cnotification_relation_def Let_def
                         tcb_queue_relation'_def)
  apply (simp add: setNotification_def split_def)
  apply (rule conjI)
   apply (rule bexI [OF _ setObject_eq])
       apply (frule(1) st_tcb_at_h_t_valid)
       apply (simp add: rf_sr_def cstate_relation_def Let_def
                        cpspace_relation_def update_ntfn_map_tos
                        typ_heap_simps')
       apply (elim conjE)
       apply (intro conjI)
            \<comment> \<open>tcb relation\<close>
            apply (erule ctcb_relation_null_queue_ptrs)
            apply (clarsimp simp: comp_def)
           \<comment> \<open>ep relation\<close>
           apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
           apply simp
           apply (rule cendpoint_relation_ntfn_queue [OF invs_sym'], assumption+)
            apply simp+
           apply (erule (1) map_to_ko_atI')
          \<comment> \<open>ntfn relation\<close>
          apply (rule cpspace_relation_ntfn_update_ntfn, assumption+)
           apply (clarsimp simp: cnotification_relation_def Let_def
                                 isWaitingNtfn_def
                                 tcb_queue_relation'_def valid_ntfn'_def
                          split: Structures_H.notification.splits list.splits
                      split del: if_split)
           apply (subgoal_tac "tcb_at' (if x22 = [] then x21 else last x22) \<sigma>")
            apply (rule conjI)
             subgoal by (erule (1) tcb_ptr_sign_extend_canonical[OF invs_pspace_canonical'])
            apply (rule context_conjI)
             subgoal by (erule (1) tcb_ptr_sign_extend_canonical[OF invs_pspace_canonical'])
            apply clarsimp
           apply (clarsimp split: if_split)
          apply simp
         \<comment> \<open>queue relation\<close>
         apply (rule cready_queues_relation_null_queue_ptrs, assumption+)
         apply (clarsimp simp: comp_def)
        apply (clarsimp simp: carch_state_relation_def)
       apply (simp add: cmachine_state_relation_def)
      apply (simp add: h_t_valid_clift_Some_iff)
     apply (simp add: objBits_simps')
    apply (simp add: objBits_simps)
   apply assumption
  apply (clarsimp simp: cnotification_relation_def Let_def
                        tcb_queue_relation'_def)
  done

lemma ntfn_set_active_ccorres:
  "ccorres dc xfdc (invs' and ko_at' ntfn ntfnptr
                          and (\<lambda>_. \<not> isWaitingNtfn (ntfnObj ntfn)))
     (UNIV \<inter> {s. ntfnPtr_' s = Ptr ntfnptr} \<inter> {s. badge_' s = badge}) hs
     (setNotification ntfnptr
          (ntfnObj_update (\<lambda>_. Structures_H.ntfn.ActiveNtfn badge) ntfn))
     (Call ntfn_set_active_'proc)"
  apply (rule ccorres_gen_asm)
  apply (cinit lift: ntfnPtr_' badge_')
   apply (simp only: setNotification_def)
   apply (rule_tac P="ko_at' ntfn ntfnptr and invs'"
            in ccorres_from_vcg[where P'=UNIV])
   apply (rule allI, rule conseqPre, vcg)
   apply clarsimp
   apply (rule cmap_relation_ko_atE [OF cmap_relation_ntfn], assumption+)
   apply (clarsimp simp: typ_heap_simps)
   apply (rule bexI[OF _ setObject_eq], simp_all)
    apply (clarsimp simp: typ_heap_simps' rf_sr_def cstate_relation_def Let_def
                          cpspace_relation_def update_ntfn_map_tos
                          carch_state_relation_def packed_heap_update_collapse_hrs
                          cmachine_state_relation_def)
    apply (rule cpspace_relation_ntfn_update_ntfn, assumption+)
     apply (simp add: cnotification_relation_def Let_def NtfnState_Active_def
                      isWaitingNtfn_def mask_def
               split: Structures_H.ntfn.split_asm)
    apply (simp add: objBits_simps')+
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

lemma sendSignal_ccorres [corres]:
  "ccorres dc xfdc (invs')
     (UNIV \<inter> \<lbrace>\<acute>ntfnPtr = Ptr ntfnptr\<rbrace> \<inter> \<lbrace>\<acute>badge = badge\<rbrace>) hs
     (sendSignal ntfnptr badge)
     (Call sendSignal_'proc)"
  apply (cinit lift: ntfnPtr_' badge_')
   apply (rule ccorres_pre_getNotification, rename_tac ntfn)
   apply (rule_tac xf'=ret__unsigned_longlong_'
               and val="case ntfnObj ntfn of IdleNtfn \<Rightarrow> scast NtfnState_Idle
                                 | WaitingNtfn _ \<Rightarrow> scast NtfnState_Waiting
                                 | ActiveNtfn _ \<Rightarrow> scast NtfnState_Active"
               and R="ko_at' ntfn ntfnptr"
                in ccorres_symb_exec_r_known_rv_UNIV[where R'=UNIV])
      apply (vcg, clarsimp)
      apply (erule(1) cmap_relation_ko_atE [OF cmap_relation_ntfn])
      apply (clarsimp simp: cnotification_relation_def Let_def typ_heap_simps
                     split: Structures_H.ntfn.splits)
     apply ceqv
    apply (rule_tac P="ntfnBoundTCB ntfn \<noteq> None \<longrightarrow>
                         option_to_ctcb_ptr (ntfnBoundTCB ntfn) \<noteq> NULL"
                 in ccorres_gen_asm)
    apply wpc
      \<comment> \<open>IdleNtfn case\<close>
      apply (rule ccorres_cond_true)
      apply (rule ccorres_rhs_assoc)+
      apply (rule_tac xf'=ret__unsigned_longlong_'
                 and val="ptr_val (option_to_ctcb_ptr (ntfnBoundTCB ntfn))"
                 and R="ko_at' ntfn ntfnptr"
                 in ccorres_symb_exec_r_known_rv_UNIV[where R'=UNIV])
         apply (rule conseqPre, vcg)
         apply clarsimp
         apply (erule(1) cmap_relation_ko_atE [OF cmap_relation_ntfn])
         apply (clarsimp simp: cnotification_relation_def Let_def typ_heap_simps
                        split: Structures_H.ntfn.splits)
        apply ceqv
       apply csymbr
       apply wpc
        apply (simp add: option_to_ctcb_ptr_def split del: if_split)
        apply (rule ccorres_cond_false)
        apply (ctac add: ntfn_set_active_ccorres)
       apply (rule ccorres_cond_true)
       apply (rule getThreadState_ccorres_foo)
       apply (rule ccorres_Guard_Seq)
       apply csymbr
       apply (rule ccorres_abstract_cleanup)
       apply (rule_tac P="(ret__unsigned_longlong = scast ThreadState_BlockedOnReceive)
                 = receiveBlocked rv" in ccorres_gen_asm2)
       apply (rule ccorres_cond[where R=\<top>])
         apply (simp add: Collect_const_mem)
        apply (rule ccorres_rhs_assoc)+
        apply simp
        apply (ctac(no_vcg) add: cancelIPC_ccorres1[OF cteDeleteOne_ccorres])
         apply (ctac(no_vcg) add: setThreadState_ccorres)
          apply (ctac(no_vcg) add: setRegister_ccorres)
           apply (ctac add: possibleSwitchTo_ccorres)
          apply (wp sts_running_valid_queues sts_st_tcb_at'_cases
                 | simp add: option_to_ctcb_ptr_def split del: if_split)+
        apply (rule_tac Q="\<lambda>_. tcb_at' (the (ntfnBoundTCB ntfn)) and invs'"
                 in hoare_post_imp)
         apply auto[1]
        apply wp
       apply simp
       apply (ctac add: ntfn_set_active_ccorres)
      apply (clarsimp simp: guard_is_UNIV_def option_to_ctcb_ptr_def
                            RISCV64_H.badgeRegister_def C_register_defs
                            RISCV64.badgeRegister_def RISCV64.capRegister_def
                            ThreadState_defs less_mask_eq Collect_const_mem)
      apply (case_tac ts, simp_all add: receiveBlocked_def typ_heap_simps
                       cthread_state_relation_def ThreadState_defs)[1]
      \<comment> \<open>ActiveNtfn case\<close>
     apply (rename_tac old_badge)
     apply (rule ccorres_cond_false)
     apply (rule ccorres_cond_false)
     apply (rule ccorres_cond_true)
     apply (clarsimp simp: setNotification_def)
     apply (rule_tac P="invs' and ko_at' ntfn ntfnptr"
                 and P'=UNIV
                  in ccorres_from_vcg)
     apply (rule allI)
     apply (rule conseqPre, vcg)
     apply clarsimp
     apply (frule(1) cmap_relation_ko_atD [OF cmap_relation_ntfn])
     apply (clarsimp simp: typ_heap_simps)
     apply (rule bexI [OF _ setObject_eq])
         apply (simp add: rf_sr_def cstate_relation_def Let_def
                          cpspace_relation_def update_ntfn_map_tos
                          typ_heap_simps')
         apply (elim conjE)
         apply (intro conjI)
           apply (rule cpspace_relation_ntfn_update_ntfn, assumption+)
            apply (simp add: cnotification_relation_def Let_def
                             NtfnState_Active_def mask_def word_bw_comms)
           apply simp
          apply (clarsimp simp: carch_state_relation_def)
         apply (simp add: cmachine_state_relation_def)
        apply (simp add: h_t_valid_clift_Some_iff)
       apply (simp add: objBits_simps')
      apply (simp add: objBits_simps)
     apply assumption
    \<comment> \<open>WaitingNtfn case\<close>
    apply (rule ccorres_cond_false)
    apply (rule ccorres_cond_true)
    apply wpc
     apply (simp only: haskell_fail_def)
     apply (rule ccorres_fail)
    apply (rename_tac dest rest)
    apply (intro ccorres_rhs_assoc)
    apply (csymbr, csymbr)
    apply (intro ccorres_rhs_assoc2)
    apply (rule ccorres_rhs_assoc)
    apply (rule ccorres_rhs_assoc)
    apply (rule ccorres_split_nothrow_novcg)
        apply (simp only: )
        apply (rule_tac dest=dest in sendSignal_dequeue_ccorres_helper)
       apply ceqv
      apply (simp only: K_bind_def)
      apply (ctac (no_vcg))
       apply simp
       apply (ctac (no_vcg))
        apply (ctac add: possibleSwitchTo_ccorres)
       apply (simp)
       apply (wp weak_sch_act_wf_lift_linear
         setThreadState_oa_queued
         sts_valid_queues tcb_in_cur_domain'_lift)[1]
      apply (wp sts_valid_queues sts_runnable)
     apply (wp setThreadState_st_tcb set_ntfn_valid_objs' | clarsimp)+
    apply (clarsimp simp: guard_is_UNIV_def ThreadState_defs mask_def
                          badgeRegister_def C_register_defs
                          RISCV64.badgeRegister_def RISCV64.capRegister_def)
   apply (clarsimp simp: guard_is_UNIV_def NtfnState_Idle_def
                         NtfnState_Active_def NtfnState_Waiting_def)
  apply clarsimp
  apply (simp only: conj_assoc[symmetric])
  apply (rule conjI)
   apply (frule ko_at_valid_objs', (clarsimp simp: projectKOs)+)
   apply (clarsimp simp: valid_obj'_def)
   apply (auto simp: isWaitingNtfn_def st_tcb_at_refs_of_rev' valid_obj'_def valid_ntfn'_def
               dest!: sym_refs_obj_atD' [OF _ invs_sym']
                elim: pred_tcb'_weakenE
               split: list.splits option.splits)[1]
  apply (clarsimp simp: option_to_ctcb_ptr_def tcb_ptr_to_ctcb_ptr_def
                        ctcb_offset_defs
                 dest!: sum_to_zero)
  apply (frule (1) ko_at_valid_ntfn'[OF _ invs_valid_objs'])
  apply (auto simp: valid_ntfn'_def valid_bound_tcb'_def obj_at'_def projectKOs
                    objBitsKO_def is_aligned_def objBits_simps')
  done

lemma receiveSignal_block_ccorres_helper:
  "ccorres dc xfdc (tcb_at' thread and valid_queues and sch_act_not thread and
                    valid_objs' and ntfn_at' ntfnptr and pspace_canonical' and
                    (\<lambda>s. sch_act_wf (ksSchedulerAction s) s \<and>
                        (\<forall>d p. thread \<notin> set (ksReadyQueues s (d, p)))) and
                    K (ntfnptr = ntfnptr && ~~ mask 4))
                   UNIV hs
           (setThreadState (Structures_H.thread_state.BlockedOnNotification
                                ntfnptr) thread)
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
        apply (rule_tac P=\<top> and P'="tcb_at' thread"
                     in threadSet_ccorres_lemma3)
         apply vcg
        apply clarsimp
        apply (frule(1) tcb_at_h_t_valid)
        apply (frule h_t_valid_c_guard)
        apply (clarsimp simp: typ_heap_simps' rf_sr_tcb_update_twice)
        apply (erule(1) rf_sr_tcb_update_no_queue_gen,
          (simp add: typ_heap_simps')+)
         apply (simp add: tcb_cte_cases_def cteSizeBits_def)
        apply (simp add: ctcb_relation_def cthread_state_relation_def
                         ThreadState_defs mask_def
                    flip: canonical_bit_def)
        apply (clarsimp simp: canonical_address_sign_extended sign_extended_iff_sign_extend)
       apply ceqv
      apply clarsimp
      apply ctac
     apply (wp threadSet_valid_queues hoare_vcg_all_lift threadSet_valid_objs'
               threadSet_weak_sch_act_wf_runnable')
    apply (clarsimp simp: guard_is_UNIV_def)
   apply (auto simp: weak_sch_act_wf_def valid_tcb'_def tcb_cte_cases_def
                     valid_tcb_state'_def obj_at'_is_canonical cteSizeBits_def)
  done

lemma cpspace_relation_ntfn_update_ntfn':
  fixes ntfn :: "Structures_H.notification" and ntfn' :: "Structures_H.notification"
    and ntfnptr :: "machine_word" and s :: "kernel_state"
  defines "qs \<equiv> if isWaitingNtfn (ntfnObj ntfn') then set (ntfnQueue (ntfnObj ntfn')) else {}"
  defines "s' \<equiv> s\<lparr>ksPSpace := (ksPSpace s)(ntfnptr \<mapsto> KONotification ntfn')\<rparr>"
  assumes koat: "ko_at' ntfn ntfnptr s"
  and       vp: "valid_pspace' s"
  and      cp: "cmap_relation (map_to_ntfns (ksPSpace s)) (cslift t) Ptr (cnotification_relation (cslift t))"
  and      srs: "sym_refs (state_refs_of' s')"
  and     rel: "cnotification_relation (cslift t') ntfn' notification"
  and    mpeq: "(cslift t' |` (- (tcb_ptr_to_ctcb_ptr ` qs))) = (cslift t |` (- (tcb_ptr_to_ctcb_ptr ` qs)))"
  shows "cmap_relation (map_to_ntfns ((ksPSpace s)(ntfnptr \<mapsto> KONotification ntfn')))
                       ((cslift t)(Ptr ntfnptr \<mapsto> notification))
                       Ptr
                       (cnotification_relation (cslift t'))"
proof -
  from koat have koat': "ko_at' ntfn' ntfnptr s'"
    by (clarsimp simp: obj_at'_def s'_def objBitsKO_def ps_clear_def projectKOs)

  have ntfns':
    "\<And>x. x \<noteq> ntfnptr \<Longrightarrow> map_to_ntfns (ksPSpace s) x =
                         map_to_ntfns (ksPSpace s') x"
    unfolding s'_def
    by (fastforce intro: ssubst [OF map_comp_update] simp: projectKO_opt_ntfn)

  from koat have map_to_ko_atI'':
    "\<And>x y. \<lbrakk> x \<noteq> ntfnptr; map_to_ntfns (ksPSpace s) x = Some y \<rbrakk> \<Longrightarrow> ko_at' y x s'"
    using vp unfolding s'_def
    by (simp add: map_to_ko_at_updI' injectKO_ntfn objBitsKO_def)

  thus ?thesis using vp srs cp rel mpeq unfolding cmap_relation_def
    apply -
    apply (elim conjE)
    apply (clarsimp elim!: obj_atE' simp: map_comp_update projectKO_opts_defs
                   split: if_split)
    apply (drule (1) bspec [OF _ domI])
    apply simp
    apply (erule(1) cnotification_relation_ntfn_queue [OF _ _ koat'])
      apply (erule(1) map_to_ko_atI'')
     apply (fold qs_def, rule mpeq)
    apply assumption
    done
qed

lemma ntfn_q_refs_of_no_NTFNBound':
  "(x, NTFNBound) \<notin> ntfn_q_refs_of' ntfn"
  by (auto simp: ntfn_q_refs_of'_def split: Structures_H.ntfn.splits)

lemma ntfnBound_state_refs_equivalence:
  "ko_at' ntfn ntfnptr s \<Longrightarrow> {r \<in> state_refs_of' s ntfnptr. snd r = NTFNBound} = ntfn_bound_refs' (ntfnBoundTCB ntfn)"
  by (auto simp: ko_at_state_refs_ofD' set_eq_subset ntfn_q_refs_of_no_NTFNBound' ntfn_bound_refs'_def)


lemma receiveSignal_enqueue_ccorres_helper:
  notes option.case_cong_weak [cong]
  shows
  "ccorres dc xfdc (valid_pspace'
                and (\<lambda>s. sym_refs ((state_refs_of' s)(ntfnptr := set queue \<times> {NTFNSignal} \<union> {r \<in> state_refs_of' s ntfnptr. snd r = NTFNBound})))
                and st_tcb_at'  (\<lambda>st. isBlockedOnNotification st \<and>
                                      waitingOnNotification st = ntfnptr) thread
                and ko_at' (ntfn::Structures_H.notification) ntfnptr
                and K ((ntfnObj ntfn = IdleNtfn \<and> queue = [thread]) \<or>
                       (\<exists>q. ntfnObj ntfn = WaitingNtfn q \<and> thread \<notin> set q \<and>
                            queue = q @ [thread])))
           UNIV hs
           (setNotification ntfnptr $ ntfnObj_update (\<lambda>_. Structures_H.WaitingNtfn queue) ntfn)
           (\<acute>ntfn_queue :== CALL ntfn_ptr_get_queue(ntfn_Ptr ntfnptr);;
            (\<acute>ntfn_queue :== CALL tcbEPAppend(tcb_ptr_to_ctcb_ptr thread,\<acute>ntfn_queue);;
             (CALL notification_ptr_set_state(ntfn_Ptr ntfnptr, scast NtfnState_Waiting);;
              CALL ntfn_ptr_set_queue(ntfn_Ptr ntfnptr,\<acute>ntfn_queue))))"
  unfolding K_def
  apply (rule ccorres_gen_asm)
  apply (rule ccorres_from_vcg)
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp split del: if_split)
  apply (frule cmap_relation_ntfn)
  apply (erule (1) cmap_relation_ko_atE)
  apply (rule conjI)
   apply (erule h_t_valid_clift)
  apply (frule(1) st_tcb_at_h_t_valid)
  apply (frule pred_tcb_at')
  apply (rule impI)
  apply (rule_tac x="init queue" in exI)
  apply (frule(1) ko_at_valid_ntfn' [OF _ valid_pspace_valid_objs'])
  apply (frule is_aligned_tcb_ptr_to_ctcb_ptr)
  apply (rule conjI)
   apply (rule_tac x=\<sigma> in exI)
   apply (simp add: cnotification_relation_def Let_def)
   apply (case_tac "ntfnObj ntfn", simp_all add: init_def valid_ntfn'_def)[1]
  apply (subgoal_tac "sym_refs (state_refs_of' (\<sigma>\<lparr>ksPSpace :=
                               (ksPSpace \<sigma>)(ntfnptr \<mapsto> KONotification (NTFN (WaitingNtfn queue) (ntfnBoundTCB ntfn)))\<rparr>))")
   prefer 2
   apply (clarsimp simp: state_refs_of'_upd ko_wp_at'_def ntfnBound_state_refs_equivalence
                         obj_at'_def projectKOs objBitsKO_def)
  apply (subgoal_tac "ko_at' (NTFN (WaitingNtfn queue) (ntfnBoundTCB ntfn)) ntfnptr (\<sigma>\<lparr>ksPSpace :=
                             (ksPSpace \<sigma>)(ntfnptr \<mapsto> KONotification (NTFN (WaitingNtfn queue) (ntfnBoundTCB ntfn)))\<rparr>)")
   prefer 2
   apply (clarsimp simp: obj_at'_def projectKOs objBitsKO_def ps_clear_upd)
  apply (intro conjI impI allI)
    apply (fastforce simp: h_t_valid_clift)
   apply (fastforce simp: h_t_valid_clift)
  apply (case_tac "ntfnObj ntfn", simp_all add: NtfnState_Idle_def NtfnState_Waiting_def)[1]
   \<comment> \<open>IdleNtfn case\<close>
   apply clarsimp
   apply (frule null_ep_queue [simplified comp_def] null_ep_queue)
   apply (simp add: setNotification_def split_def)
   apply (rule bexI [OF _ setObject_eq])
       apply (simp add: rf_sr_def cstate_relation_def Let_def init_def
                        cpspace_relation_def update_ntfn_map_tos
                        typ_heap_simps')
       apply (elim conjE)
       apply (intro conjI)
            \<comment> \<open>tcb relation\<close>
            apply (erule ctcb_relation_null_queue_ptrs)
            apply (clarsimp simp: comp_def)
           \<comment> \<open>ep relation\<close>
           apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
           apply simp
           apply (rule cendpoint_relation_ntfn_queue, assumption+)
             apply (simp add: isWaitingNtfn_def)
            apply simp
           apply (frule_tac x=p in map_to_ko_atI, clarsimp, clarsimp)
           apply (erule(2) map_to_ko_at_updI')
            apply (clarsimp simp: objBitsKO_def)
           apply (clarsimp simp: obj_at'_def projectKOs)
          \<comment> \<open>ntfn relation\<close>
          apply (rule cpspace_relation_ntfn_update_ntfn', assumption+)
            apply (case_tac "ntfn", simp_all)[1]
           apply (clarsimp simp: cnotification_relation_def Let_def
                                 mask_def [where n=3] NtfnState_Waiting_def)
           subgoal
             apply (clarsimp simp: tcb_queue_relation'_def is_aligned_neg_mask                                valid_ntfn'_def
                                   dest: tcb_queue_relation_next_not_NULL)
             apply (rule conjI, fastforce simp: mask_def)
             apply (rule context_conjI)
              subgoal by (fastforce simp: valid_pspace'_def objBits_simps'
                              intro!: tcb_ptr_sign_extend_canonical
                               dest!: st_tcb_strg'[rule_format])
             by clarsimp
          apply (simp add: isWaitingNtfn_def)
         \<comment> \<open>queue relation\<close>
         apply (rule cready_queues_relation_null_queue_ptrs, assumption+)
         subgoal by (clarsimp simp: comp_def)
        apply (clarsimp simp: carch_state_relation_def packed_heap_update_collapse_hrs)
       apply (simp add: cmachine_state_relation_def)
      apply (simp add: h_t_valid_clift_Some_iff)
     apply (simp add: objBits_simps')
    apply (simp add: objBits_simps)
   apply assumption
  \<comment> \<open>WaitingNtfn case\<close>
  apply clarsimp
  apply (frule null_ep_queue [simplified comp_def] null_ep_queue)
  apply (simp add: setNotification_def split_def)
  apply (rule bexI [OF _ setObject_eq])
      apply (simp add: rf_sr_def cstate_relation_def init_def Let_def
                       cpspace_relation_def update_ntfn_map_tos
                       typ_heap_simps')
      apply (elim conjE)
      apply (intro conjI)
           \<comment> \<open>tcb relation\<close>
           apply (erule ctcb_relation_null_queue_ptrs)
           apply (clarsimp simp: comp_def)
          \<comment> \<open>ep relation\<close>
          apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
          apply simp
          apply (rule cendpoint_relation_ntfn_queue, assumption+)
            apply (simp add: isWaitingNtfn_def)
           apply simp
          apply (frule_tac x=p in map_to_ko_atI, clarsimp, clarsimp)
          apply (erule(2) map_to_ko_at_updI')
           apply (clarsimp simp: objBitsKO_def)
          apply (clarsimp simp: obj_at'_def projectKOs)
         \<comment> \<open>ntfn relation\<close>
         apply (rule cpspace_relation_ntfn_update_ntfn', assumption+)
           apply (case_tac "ntfn", simp_all)[1]
          apply (clarsimp simp: cnotification_relation_def Let_def
                                mask_def [where n=3] NtfnState_Waiting_def
                         split: if_split)
          subgoal for _ _ ko'
            apply (clarsimp simp: tcb_queue_relation'_def is_aligned_neg_mask
                            dest: tcb_queue_relation_next_not_NULL)
            apply (rule conjI, clarsimp)
             apply (rule conjI, fastforce simp: mask_def)
             apply (rule context_conjI)
              subgoal by (fastforce intro!: tcb_ptr_sign_extend_canonical
                                     dest!: st_tcb_strg'[rule_format])
             apply clarsimp
            apply clarsimp
            apply (rule conjI, fastforce simp: mask_def)
            apply (rule conjI)
             subgoal by (fastforce intro!: tcb_ptr_sign_extend_canonical
                                    dest!: st_tcb_strg'[rule_format])
            apply (subgoal_tac "canonical_address (ntfnQueue_head_CL (notification_lift ko'))")
             apply (clarsimp simp: canonical_address_sign_extended sign_extended_iff_sign_extend)
            apply (clarsimp simp: notification_lift_def canonical_address_sign_extended
                                  sign_extended_sign_extend
                            simp flip: canonical_bit_def)
            done
         apply (simp add: isWaitingNtfn_def)
        \<comment> \<open>queue relation\<close>
        apply (rule cready_queues_relation_null_queue_ptrs, assumption+)
        apply (clarsimp simp: comp_def)
       apply (clarsimp simp: carch_state_relation_def packed_heap_update_collapse_hrs)
      apply (simp add: cmachine_state_relation_def)
     apply (simp add: h_t_valid_clift_Some_iff)
    apply (simp add: objBits_simps')
   apply (simp add: objBits_simps)
  apply assumption
  done

lemma receiveSignal_ccorres [corres]:
  "ccorres dc xfdc (invs' and valid_cap' cap and st_tcb_at' simple' thread
                    and sch_act_not thread
                    and (\<lambda>s. \<forall>d p. thread \<notin> set (ksReadyQueues s (d, p)))
                    and K (isNotificationCap cap))
     (UNIV \<inter> \<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr thread\<rbrace>
           \<inter> \<lbrace>ccap_relation cap \<acute>cap\<rbrace>
           \<inter> {s. isBlocking_' s = from_bool is_blocking}) hs
     (receiveSignal thread cap is_blocking)
     (Call receiveSignal_'proc)"
  unfolding K_def
  supply if_cong[cong] option.case_cong[cong]
  apply (rule ccorres_gen_asm)
  apply (cinit lift: thread_' cap_' isBlocking_')
   apply (rule ccorres_pre_getNotification, rename_tac ntfn)
   apply (rule_tac xf'=ret__unsigned_longlong_'
               and val="capNtfnPtr cap"
               and R=\<top>
                in ccorres_symb_exec_r_known_rv_UNIV[where R'=UNIV])
      apply vcg
      apply (clarsimp simp: cap_get_tag_isCap isCap_simps)
      apply (frule cap_get_tag_isCap_unfolded_H_cap)
      apply (simp add: cap_notification_cap_lift ccap_relation_def cap_to_H_def)
     apply ceqv
    apply csymbr
    apply (rule_tac xf'=ret__unsigned_longlong_'
                and val="case ntfnObj ntfn of IdleNtfn \<Rightarrow> scast NtfnState_Idle
                                  | WaitingNtfn _ \<Rightarrow> scast NtfnState_Waiting
                                  | ActiveNtfn _ \<Rightarrow> scast NtfnState_Active"
                and R="ko_at' ntfn (capNtfnPtr cap)"
                 in ccorres_symb_exec_r_known_rv_UNIV[where R'=UNIV])
       apply (vcg, clarsimp)
       apply (erule(1) cmap_relation_ko_atE [OF cmap_relation_ntfn])
       apply (clarsimp simp: cnotification_relation_def Let_def typ_heap_simps
                      split: Structures_H.ntfn.splits)

      apply ceqv
     apply wpc
       \<comment> \<open>IdleNtfn case\<close>
       apply (rule ccorres_cond_true)
       apply csymbr
       apply (simp only: case_bool_If from_bool_neq_0)
       apply (rule ccorres_Cond_rhs, simp cong: Collect_cong)
        apply (intro ccorres_rhs_assoc)
        apply (rule ccorres_rhs_assoc2)
        apply (rule ccorres_rhs_assoc2)
        apply (rule ccorres_split_nothrow_novcg)
            apply (rule receiveSignal_block_ccorres_helper[simplified])
           apply ceqv
          apply (simp only: K_bind_def)
          apply (rule receiveSignal_enqueue_ccorres_helper[simplified])
         apply (simp add: valid_ntfn'_def)
         apply (wp sts_st_tcb')
         apply (rule_tac Q="\<lambda>rv. ko_wp_at' (\<lambda>x. projectKO_opt x = Some ntfn
                               \<and> projectKO_opt x = (None::tcb option))
                                  (capNtfnPtr cap)"
                       in hoare_post_imp)
          apply (clarsimp simp: obj_at'_def ko_wp_at'_def projectKOs)
         apply wp
        apply (clarsimp simp: guard_is_UNIV_def)
       apply simp
       apply (ctac add: doNBRecvFailedTransfer_ccorres)
      \<comment> \<open>ActiveNtfn case\<close>
      apply (rename_tac badge)
      apply (rule ccorres_cond_false)
      apply (rule ccorres_cond_true)
      apply (intro ccorres_rhs_assoc)
      apply (rule_tac val=badge
                  and xf'=ret__unsigned_longlong_'
                  and R="ko_at' ntfn (capNtfnPtr cap)"
                   in ccorres_symb_exec_r_known_rv_UNIV [where R'=UNIV])
         apply (vcg, clarsimp)
         apply (erule(1) cmap_relation_ko_atE [OF cmap_relation_ntfn])
         apply (clarsimp simp: cnotification_relation_def Let_def typ_heap_simps
                        split: Structures_H.notification.splits)
        apply ceqv
       apply (clarsimp simp: badgeRegister_def Kernel_C.badgeRegister_def, ctac(no_vcg))
        apply (rule_tac P="invs' and ko_at' ntfn (capNtfnPtr cap)"
                    and P'=UNIV
                     in ccorres_from_vcg)
        apply (rule allI, rule conseqPre, vcg)
        apply clarsimp
        apply (frule(1) cmap_relation_ko_atD [OF cmap_relation_ntfn])
        apply (clarsimp simp: typ_heap_simps setNotification_def)
        apply (rule bexI [OF _ setObject_eq])
            apply (simp add: rf_sr_def cstate_relation_def Let_def
                             cpspace_relation_def update_ntfn_map_tos
                             typ_heap_simps')
            apply (elim conjE)
            apply (intro conjI)
              apply (rule cpspace_relation_ntfn_update_ntfn, assumption+)
               apply (simp add: cnotification_relation_def Let_def
                                NtfnState_Idle_def mask_def)
              apply simp
             apply (simp add: carch_state_relation_def)
            apply (simp add: cmachine_state_relation_def)
           apply (simp add: h_t_valid_clift_Some_iff)
          apply (simp add: objBits_simps')
         apply (simp add: objBits_simps)
        apply assumption
       apply wp
      apply (clarsimp simp: guard_is_UNIV_def)
      apply (clarsimp simp: RISCV64.badgeRegister_def RISCV64.capRegister_def C_register_defs)
     \<comment> \<open>WaitingNtfn case\<close>
     apply (rename_tac list)
     apply (rule ccorres_cond_true)
     apply csymbr
     apply (simp only: case_bool_If from_bool_neq_0)
     apply (rule ccorres_Cond_rhs, simp cong: Collect_cong)
      apply (intro ccorres_rhs_assoc)
      apply (rule ccorres_rhs_assoc2)
      apply (rule ccorres_rhs_assoc2)
      apply (rule ccorres_split_nothrow_novcg)
          apply (simp only: )
          apply (rule receiveSignal_block_ccorres_helper[simplified])
         apply ceqv
        apply (simp only: K_bind_def)
        apply (rule_tac ntfn="ntfn" in receiveSignal_enqueue_ccorres_helper[simplified])
       apply (simp add: valid_ntfn'_def)
       apply (wp sts_st_tcb')
       apply (rule_tac Q="\<lambda>rv. ko_wp_at' (\<lambda>x. projectKO_opt x = Some ntfn
                             \<and> projectKO_opt x = (None::tcb option))
                                    (capNtfnPtr cap)
                      and K (thread \<notin> set list)"
                       in hoare_post_imp)
        apply (clarsimp simp: obj_at'_def ko_wp_at'_def projectKOs)
       apply wp
      apply (clarsimp simp: guard_is_UNIV_def)
     apply simp
     apply (ctac add: doNBRecvFailedTransfer_ccorres)
    apply (clarsimp simp: guard_is_UNIV_def NtfnState_Active_def
                          NtfnState_Waiting_def NtfnState_Idle_def)
   apply (clarsimp simp: guard_is_UNIV_def)
  apply (clarsimp split: if_split)
  apply (rule conjI)
   apply (clarsimp dest!: st_tcb_strg'[rule_format]
                    simp: isNotificationCap_def valid_cap'_def obj_at'_def projectKOs
                   split: capability.splits split del: if_split)
  apply clarsimp
  apply (frule(1) ko_at_valid_objs' [OF _ invs_valid_objs'])
   apply (clarsimp simp: projectKO_opt_ntfn split: kernel_object.split_asm)
  apply (subgoal_tac "state_refs_of' s thread = {r \<in> state_refs_of' s thread. snd r = TCBBound}")
   apply (clarsimp simp: valid_obj'_def valid_ntfn'_def refs_of'_def
                  split: ntfn.splits)
    apply (subgoal_tac "state_refs_of' s (capNtfnPtr cap) =
                             {r \<in> state_refs_of' s (capNtfnPtr cap). snd r = NTFNBound}")
     subgoal by (fastforce simp: obj_at'_def is_aligned_neg_mask objBits_simps'
                           projectKOs invs'_def valid_state'_def st_tcb_at'_def
                           valid_tcb_state'_def ko_wp_at'_def valid_pspace'_def
                           isBlockedOnNotification_def projectKO_opt_tcb
                     elim: delta_sym_refs
                    split: if_split_asm if_split)
    apply (auto simp: obj_at'_def state_refs_of'_def projectKOs ntfn_bound_refs'_def)[1]
   apply (rename_tac list)
   apply (subgoal_tac "state_refs_of' s (capNtfnPtr cap) = (set list) \<times> {NTFNSignal}
                                       \<union> {r \<in> state_refs_of' s (capNtfnPtr cap). snd r = NTFNBound}
                              \<and> thread \<notin> (set list)")
    subgoal by (fastforce simp: obj_at'_def is_aligned_neg_mask objBits_simps'
                          projectKOs invs'_def valid_state'_def st_tcb_at'_def
                          valid_tcb_state'_def ko_wp_at'_def valid_pspace'_def
                          isBlockedOnNotification_def projectKO_opt_tcb
                    elim: delta_sym_refs
                   split: if_split_asm if_split)
   apply (frule(1) sym_refs_obj_atD' [OF _ invs_sym'])
   apply (rule conjI, clarsimp simp: ko_wp_at'_def dest!: ntfnBound_state_refs_equivalence)
   apply (clarsimp simp: st_tcb_at'_def ko_wp_at'_def obj_at'_def projectKOs
                  split: if_split_asm)
   apply (drule(1) bspec)+
   apply (drule_tac x="(thread, NTFNSignal)" in bspec, clarsimp)
   apply (clarsimp simp: tcb_bound_refs'_def)
   apply (case_tac "tcbState obj", simp_all)[1]
  apply (frule(1) st_tcb_idle' [OF invs_valid_idle'], simp)
  apply (clarsimp simp: st_tcb_at'_def obj_at'_def state_refs_of'_def projectKOs
                 split: if_split_asm)
  apply (case_tac "tcbState obj", clarsimp+)[1]
  done

end
end
