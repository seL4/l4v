(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory Ipc_C
imports Finalise_C CSpace_All
begin

declare option.weak_case_cong[cong]

definition
  "replyFromKernel_success_empty thread \<equiv> do
     VSpace_H.lookupIPCBuffer True thread;
     asUser thread $ setRegister State_H.badgeRegister 0;
     setMessageInfo thread $ (Types_H.MI 0 0 0 0)
   od"

lemma replyFromKernel_success_empty:
  "replyFromKernel thread (0, []) = replyFromKernel_success_empty thread"
  unfolding replyFromKernel_def replyFromKernel_success_empty_def
  by (simp add: setMRs_Nil submonad_asUser.fn_stateAssert)

crunch valid_queues[wp]: handleFaultReply valid_queues

crunch valid_queues'[wp]: handleFaultReply valid_queues'

crunch sch_act_wf: handleFaultReply "\<lambda>s. sch_act_wf (ksSchedulerAction s) s"
  
crunch valid_ipc_buffer_ptr' [wp]: copyMRs "valid_ipc_buffer_ptr' p"
  (lift: hoare_valid_ipc_buffer_ptr_typ_at' wp: crunch_wps)

lemma threadSet_obj_at'_nontcb:
  "koType TYPE('a::pspace_storable) \<noteq> koType TYPE(Structures_H.tcb) \<Longrightarrow>
   \<lbrace>obj_at' (P :: 'a \<Rightarrow> bool) t'\<rbrace> threadSet f t \<lbrace>\<lambda>rv. obj_at' P t'\<rbrace>"
  apply (simp add: threadSet_def)
  apply (wp obj_at_setObject2 hoare_drop_imps
       | clarsimp simp: updateObject_tcb updateObject_default_def in_monad)+
  done

lemma doAsyncTransfer_aep_at[wp]:
  "\<lbrace>ko_at' (aep :: async_endpoint) p\<rbrace>
    doAsyncTransfer badge val thread
   \<lbrace>\<lambda>_. ko_at' aep p\<rbrace>"
  apply (simp add: doAsyncTransfer_def setMessageInfo_def setMRs_def
                   zipWithM_x_mapM_x split_def storeWordUser_def
                   setThreadState_def asUser_def)
  apply (wp threadSet_obj_at'_nontcb mapM_x_wp hoare_drop_imps
       | simp | rule subset_refl)+
  done

lemma doAsyncTransfer_invs'[wp]:
  "\<lbrace>invs' and tcb_at' thread\<rbrace>
   doAsyncTransfer badge val thread \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: doAsyncTransfer_def)
  apply (wp sts_invs_minor' | clarsimp simp: st_tcb_at')+
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

(* FIXME: move! (did get lost, somewhere along the path. *)
declare empty_fail_setRegister[simp]

lemma setMRs_to_setMR':
  "setMRs thread buffer xs
   = (do
    stateAssert (tcb_at' thread) [];
    ys \<leftarrow> zipWithM (setMR thread buffer) [0 ..< msgMaxLength] xs;
    return (of_nat (min (length xs) (length msgRegisters +
              (case buffer of None \<Rightarrow> 0 | _ \<Rightarrow> Suc (unat (msgMaxLength :: word32))
                  - unat ((1 :: word32) + of_nat (length msgRegisters))))))
  od)"
  apply (simp add: setMRs_def setMR_def split_def    
                   zipWithM_x_mapM_x asUser_mapM_x bind_assoc
                   zipWithM_If_cut)
  apply (simp add: zipWithM_mapM)
  apply (simp add: split_def mapM_liftM_const[unfolded liftM_def]
                   mapM_return mapM_Nil mapM_x_Nil asUser_mapM_x
                   zip_is_empty last_append map_replicate_const
            split: option.split split del: split_if)
  apply (simp add: mapM_discarded mapM_x_def split del: split_if) 
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
   apply (simp add: zip_is_empty msgMaxLength_unfold)
  apply (simp add: fst_last_zip_upt)
  apply (subgoal_tac "msgMaxLength - Suc 0 \<ge> length msgRegisters
                           \<and> of_nat (length xs - Suc 0) = of_nat (length xs) - (1 :: word32)
                           \<and> unat ((1 :: word32) + of_nat (length msgRegisters)) = Suc (length msgRegisters)")
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

(* FIXME move the thread_submonad stuff to SubMonad_R and use it for asUser *)
definition
  "thread_fetch \<equiv> \<lambda>ext t s. case (ksPSpace s t) of
      Some (KOTCB tcb) \<Rightarrow> ext tcb
    | None \<Rightarrow> undefined"

definition
  "thread_replace \<equiv> \<lambda>upd t nv s. 
      let obj = case (ksPSpace s t) of
                   Some (KOTCB tcb) \<Rightarrow> Some (KOTCB (upd (\<lambda>_. nv) tcb))
                 | obj \<Rightarrow> obj
      in s \<lparr> ksPSpace := (ksPSpace s) (t := obj) \<rparr>"

lemma thread_submonad_args:
  "\<lbrakk> \<And>f v. ext (upd f v) = f (ext v);
     \<And>f1 f2 v. upd f1 (upd f2 v) = upd (f1 \<circ> f2) v;
     \<And>f v. upd (\<lambda>_. ext v) v = v \<rbrakk> \<Longrightarrow>
   submonad_args (thread_fetch ext t) (thread_replace upd t) (tcb_at' t)"
  apply unfold_locales
     apply (clarsimp simp: thread_fetch_def thread_replace_def
                           Let_def obj_at'_def projectKOs
                    split: kernel_object.split option.split)
    apply (clarsimp simp: thread_replace_def Let_def
                   split: kernel_object.split option.split)
   apply (clarsimp simp: thread_fetch_def thread_replace_def Let_def
                         fun_upd_idem
                  split: kernel_object.splits option.splits)
  apply (clarsimp simp: obj_at'_def thread_replace_def Let_def projectKOs
                 split: kernel_object.splits option.splits)
  apply (case_tac tcb, simp add: objBitsKO_def ps_clear_def)
  done

lemma tcbFault_submonad_args:
  "submonad_args (thread_fetch tcbFault t) (thread_replace tcbFault_update t)
                 (tcb_at' t)"
  apply (rule thread_submonad_args)
    apply (case_tac v, simp)+
  done

lemma threadGet_stateAssert_gets:
  "threadGet ext t = do stateAssert (tcb_at' t) []; gets (thread_fetch ext t) od"
  apply (rule is_stateAssert_gets [OF _ _ empty_fail_threadGet no_fail_threadGet])
    apply (clarsimp simp: threadGet_def liftM_def, wp)[1]
   apply (simp add: threadGet_def liftM_def, wp getObject_tcb_at')
  apply (simp add: threadGet_def liftM_def, wp)
  apply (rule hoare_strengthen_post, wp getObject_obj_at')
     apply (simp add: objBits_def objBitsKO_def)+
  apply (clarsimp simp: obj_at'_def thread_fetch_def projectKOs)
  done

lemma threadGet_tcbFault_submonad_fn:
  "threadGet tcbFault t =
   submonad_fn (thread_fetch tcbFault t) (thread_replace tcbFault_update t)
               (tcb_at' t) get"
  apply (rule ext)
  apply (clarsimp simp: submonad_fn_def bind_assoc split_def)
  apply (subst threadGet_stateAssert_gets, simp)
  apply (rule bind_apply_cong [OF refl])
  apply (clarsimp simp: in_monad bind_def gets_def get_def return_def
                        submonad_args.args(3) [OF tcbFault_submonad_args]
                        select_f_def modify_def put_def)
  done

lemma asUser_threadGet_tcbFault_comm:
  "empty_fail im \<Longrightarrow>
   do y \<leftarrow> asUser t im;
      x \<leftarrow> threadGet tcbFault t';
      n x y
   od =
   do x \<leftarrow> threadGet tcbFault t';
      asUser t im >>= n x
   od"
  apply (rule submonad_comm2 [OF tcbFault_submonad_args
                                 threadGet_tcbFault_submonad_fn 
                                 submonad_asUser, symmetric])
      apply (clarsimp simp: thread_replace_def asUser_replace_def Let_def
                     split: option.split)
      apply (clarsimp simp: fun_upd_idem fun_upd_twist
                     split: kernel_object.split)
      apply (case_tac tcb, simp)
     apply (clarsimp simp: asUser_replace_def Let_def obj_at'_real_def
                           ko_wp_at'_def ps_clear_upd_None ps_clear_upd
                           objBitsKO_def projectKOs
                    split: option.split kernel_object.split)
    apply (clarsimp simp: thread_replace_def Let_def obj_at'_real_def
                          ko_wp_at'_def ps_clear_upd_None
                          ps_clear_upd objBitsKO_def projectKOs
                   split: option.split kernel_object.split)
   apply (simp add: get_def empty_fail_def)
  apply assumption
  done

lemma threadGet_tcbFault_doMachineOp_comm:
  "\<lbrakk> empty_fail m' \<rbrakk> \<Longrightarrow>
   do x \<leftarrow> threadGet tcbFault t; y \<leftarrow> doMachineOp m'; n x y od =
   do y \<leftarrow> doMachineOp m'; x \<leftarrow> threadGet tcbFault t; n x y od"
  apply (rule submonad_comm2 [OF tcbFault_submonad_args
                                 threadGet_tcbFault_submonad_fn
                                 submonad_doMachineOp])
      apply (simp add: thread_replace_def Let_def)
     apply simp
    apply (rule refl)
   apply (simp add: get_def empty_fail_def)
  apply assumption
  done

lemma getObject_tcb_det:
  "(r::tcb,s') \<in> fst (getObject p s) \<Longrightarrow> fst (getObject p s) = {(r,s)} \<and> s' = s"
  apply (clarsimp simp add: getObject_def bind_def get_def gets_def
                            return_def loadObject_default_def split_def)
  apply (clarsimp split: kernel_object.split_asm split_if_asm option.split_asm
                   simp: in_monad typeError_def alignError_def magnitudeCheck_def
                         objBits_def objBitsKO_def projectKOs
                         lookupAround2_def Let_def o_def)
   apply (simp_all add: bind_def return_def assert_opt_def split_def projectKOs
                        alignCheck_def is_aligned_mask[symmetric]
                        unless_def when_def magnitudeCheck_def)
  done

lemma threadGet_again:
  "\<And>rv s s' n. (rv, s') \<in> fst (threadGet ext t s) \<Longrightarrow>
   (threadGet ext t >>= n) s' = n rv s'"
  apply (clarsimp simp add: threadGet_def liftM_def in_monad)
  apply (frule use_valid [OF _ getObject_obj_at'])
     apply (simp add: objBits_def objBitsKO_def)+
  apply (frule getObject_tcb_det)
  apply (clarsimp simp: bind_def split_def)
  apply (insert no_fail_getObject_tcb)
  apply (clarsimp simp: no_fail_def obj_at'_def is_tcb)
  done

lemma asUser_getRegister_discarded:
  "(asUser t (getRegister r)) >>= (\<lambda>_. n) =
   stateAssert (tcb_at' t) [] >>= (\<lambda>_. n)"
  apply (rule ext)
  apply (clarsimp simp: submonad_asUser.fn_is_sm submonad_fn_def
                        submonad_asUser.args assert_def select_f_def
                        gets_def get_def modify_def put_def
                        getRegister_def bind_def split_def
                        return_def fail_def stateAssert_def)
  done

lemma loadWordUser_submonad_fn:
  "loadWordUser p = submonad_fn ksMachineState (ksMachineState_update \<circ> K)
                                (pointerInUserData p) (loadWord p)"
  by (simp add: loadWordUser_def submonad_doMachineOp.fn_is_sm submonad_fn_def)

lemma storeWordUser_submonad_fn:
  "storeWordUser p v = submonad_fn ksMachineState (ksMachineState_update \<circ> K)
                                   (pointerInUserData p) (storeWord p v)"
  by (simp add: storeWordUser_def submonad_doMachineOp.fn_is_sm submonad_fn_def)

lemma threadGet_tcbFault_loadWordUser_comm:
  "do x \<leftarrow> threadGet tcbFault t; y \<leftarrow> loadWordUser p; n x y od =
   do y \<leftarrow> loadWordUser p; x \<leftarrow> threadGet tcbFault t; n x y od"
  apply (rule submonad_comm [OF tcbFault_submonad_args _
                                threadGet_tcbFault_submonad_fn
                                loadWordUser_submonad_fn])
       apply (simp add: submonad_args_def pointerInUserData_def)
      apply (simp add: thread_replace_def Let_def)
     apply simp
    apply (clarsimp simp: thread_replace_def Let_def typ_at'_def ko_wp_at'_def
                          ps_clear_upd ps_clear_upd_None pointerInUserData_def
                   split: option.split kernel_object.split)
   apply (simp add: get_def empty_fail_def)
  apply (simp add: ef_loadWord)
  done

lemma threadGet_tcbFault_storeWordUser_comm:
  "do x \<leftarrow> threadGet tcbFault t; y \<leftarrow> storeWordUser p v; n x y od =
   do y \<leftarrow> storeWordUser p v; x \<leftarrow> threadGet tcbFault t; n x y od"
  apply (rule submonad_comm [OF tcbFault_submonad_args _
                                threadGet_tcbFault_submonad_fn
                                storeWordUser_submonad_fn])
       apply (simp add: submonad_args_def pointerInUserData_def)
      apply (simp add: thread_replace_def Let_def)
     apply simp
    apply (clarsimp simp: thread_replace_def Let_def typ_at'_def ko_wp_at'_def
                          ps_clear_upd ps_clear_upd_None pointerInUserData_def
                   split: option.split kernel_object.split)
   apply (simp add: get_def empty_fail_def)
  apply (simp add: ef_storeWord)
  done

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
  "length State_H.syscallMessage = unat n_syscallMessage"
  apply (simp add: syscallMessage_def ARMMachineTypes.syscallMessage_def
                msgRegisters_unfold n_syscallMessage_def)
  apply (simp add: upto_enum_def)
  apply (simp add: fromEnum_def enum_register)
  done

lemma (in kernel_m) syscallMessage_ccorres:
  "n < unat n_syscallMessage
      \<Longrightarrow> register_from_H (State_H.syscallMessage ! n)
           = index syscallMessage n"
  apply (simp add: State_H.syscallMessage_def syscallMessage_def
                   ARMMachineTypes.syscallMessage_def
                   n_syscallMessage_def msgRegisters_unfold)
  apply (simp add: upto_enum_def fromEnum_def enum_register)
  apply (simp add: toEnum_def enum_register)
  apply (clarsimp simp: fupdate_def
              | drule nat_less_cases' | erule disjE)+
  done

definition
  "handleFaultReply' f sender receiver \<equiv> do
     tag \<leftarrow> getMessageInfo sender;
     label \<leftarrow> return $ msgLabel tag;
     mlen \<leftarrow> return $ msgLength tag;
     case f of
       CapFault _ _ _ \<Rightarrow> do
         sendBuf \<leftarrow> lookupIPCBuffer False sender;
         stateAssert (tcb_at' sender) [];
         case sendBuf of
           None \<Rightarrow> return ()
         | Some bufferPtr \<Rightarrow> do
             mapM loadWordUser
               (map (\<lambda>i. bufferPtr + PPtr (i * 4))
                    [(scast n_msgRegisters :: word32) + 1.e. msgMaxLength]);
             return ()
           od;
         return True
       od
     | VMFault _ _ \<Rightarrow> do
         sendBuf \<leftarrow> lookupIPCBuffer False sender;
         stateAssert (tcb_at' sender) [];
         case sendBuf of
           None \<Rightarrow> return ()
         | Some bufferPtr \<Rightarrow> do
             mapM loadWordUser
               (map (\<lambda>i. bufferPtr + PPtr (i * 4))
                    [(scast n_msgRegisters :: word32) + 1.e. msgMaxLength]);
             return ()
           od;
         return True
       od
     | UnknownSyscallException _ \<Rightarrow> do
         sendBuf \<leftarrow> lookupIPCBuffer False sender;
         regs \<leftarrow> return $ take (unat mlen) syscallMessage;
         stateAssert (tcb_at' sender) [];
         zipWithM_x (\<lambda>rs rd. do
           v \<leftarrow> asUser sender $ getRegister rs;
           asUser receiver $ setRegister rd $ sanitiseRegister rd v
         od) msgRegisters regs;
         stateAssert (tcb_at' receiver) [];
         case sendBuf of
           None \<Rightarrow> return ()
         | Some bufferPtr \<Rightarrow> do
             zipWithM_x (\<lambda>i rd. do
               v \<leftarrow> loadWordUser (bufferPtr + PPtr (i * 4));
               asUser receiver $ setRegister rd $ sanitiseRegister rd v
             od) [(scast n_msgRegisters :: word32) + 1.e. scast n_syscallMessage] (drop (unat (scast n_msgRegisters :: word32)) regs);
             mapM loadWordUser
               (map (\<lambda>i. bufferPtr + PPtr (i * 4))
                    [(scast n_msgRegisters :: word32) + 1 + of_nat (length (drop (unat (scast n_msgRegisters :: word32)) regs)).e.  msgMaxLength]);
             return ()
           od;
         return (label = 0)
       od
     | UserException _ _ \<Rightarrow> do
         sendBuf \<leftarrow> lookupIPCBuffer False sender;
         regs \<leftarrow> return $ take (unat mlen) exceptionMessage;
         stateAssert (tcb_at' sender) [];
         zipWithM_x (\<lambda>rs rd. do
           v \<leftarrow> asUser sender $ getRegister rs;
           asUser receiver $ setRegister rd $ sanitiseRegister rd v
         od) msgRegisters regs;
         stateAssert (tcb_at' receiver) [];
         case sendBuf of
           None \<Rightarrow> return ()
         | Some bufferPtr \<Rightarrow> do
             mapM loadWordUser
               (map (\<lambda>i. bufferPtr + PPtr (i * 4))
                    [(scast n_msgRegisters :: word32) + 1.e. msgMaxLength]);
             return ()
           od;
         return (label = 0)
       od
  od"

lemma loadWordUser_discarded:
  "loadWordUser p >>= (\<lambda>_. n) =
   stateAssert (pointerInUserData p and K (p && mask 2 = 0)) [] >>= (\<lambda>_. n)"
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
    apply (wp mapM_wp_inv)
  apply simp
  done

lemmas syscallMessage_unfold
  = State_H.syscallMessage_def
    ARMMachineTypes.syscallMessage_def
        [unfolded upto_enum_def, simplified,
         unfolded fromEnum_def enum_register, simplified,
         unfolded toEnum_def enum_register, simplified]

lemma handleFaultReply':
  assumes neq: "r \<noteq> s"
  shows "do 
    tag \<leftarrow> getMessageInfo s;
    sb \<leftarrow> lookupIPCBuffer False s;
    msg \<leftarrow> getMRs s sb tag;
    handleFaultReply f r (msgLabel tag) msg
  od = handleFaultReply' f s r"
  apply (rule ext)
  apply (unfold handleFaultReply'_def getMRs_def msgMaxLength_def
                bit_def msgLengthBits_def msgRegisters_unfold
                fromIntegral_simp1 fromIntegral_simp2
                shiftL_word)
  apply (simp add: bind_assoc)
  apply (rule bind_apply_cong [OF refl], rename_tac tag s')
  apply (clarsimp simp: mapM_def sequence_def bind_assoc asUser_bind_distrib
                        asUser_return submonad_asUser.fn_stateAssert)
  apply (case_tac f)
     apply (clarsimp simp: handleFaultReply_def zipWithM_x_mapM_x
                           zip_Cons State_H.exceptionMessage_def
                           ARMMachineTypes.exceptionMessage_def
                           mapM_x_Cons mapM_x_Nil)
     apply (rule bind_apply_cong [OF refl], rename_tac sb s'')
     apply (case_tac sb)
      apply (case_tac "msgLength tag < scast n_msgRegisters")
       apply (fastforce simp: bind_assoc asUser_bind_distrib asUser_return
                             zip_Cons mapM_x_Cons mapM_x_Nil
                             asUser_comm [OF neq] asUser_getRegister_discarded
                             submonad_asUser.fn_stateAssert asUser_return
                             bind_subst_lift [OF submonad_asUser.stateAssert_fn] 
                             State_H.sanitiseRegister_def
                             ARMMachineTypes.sanitiseRegister_def
                             n_msgRegisters_def
                       dest: word_less_cases)
      apply (clarsimp simp: bind_assoc asUser_bind_distrib asUser_return
                            zip_Cons mapM_x_Cons mapM_x_Nil
                            asUser_comm [OF neq] asUser_getRegister_discarded
                            submonad_asUser.fn_stateAssert asUser_return
                            bind_subst_lift [OF submonad_asUser.stateAssert_fn] 
                            word_less_nat_alt State_H.sanitiseRegister_def
                            ARMMachineTypes.sanitiseRegister_def
                            n_msgRegisters_def)
     apply (case_tac "msgLength tag < scast n_msgRegisters")
      apply (fastforce simp: asUser_bind_distrib asUser_return
                            zip_Cons word_le_make_less mapM_x_Cons mapM_x_Nil
                            asUser_comm [OF neq] asUser_getRegister_discarded
                            submonad_asUser.fn_stateAssert asUser_return
                            bind_subst_lift [OF submonad_asUser.stateAssert_fn] 
                            bind_assoc State_H.sanitiseRegister_def
                            ARMMachineTypes.sanitiseRegister_def
                            bind_comm_mapM_comm [OF asUser_loadWordUser_comm]
                            empty_fail_setRegister word_size
                            stateAssert_mapM_loadWordUser_comm
                            n_msgRegisters_def
                      dest: word_less_cases)
     apply (clarsimp simp: asUser_bind_distrib asUser_return
                            zip_Cons word_le_make_less mapM_x_Cons mapM_x_Nil
                            asUser_comm [OF neq] asUser_getRegister_discarded
                            submonad_asUser.fn_stateAssert asUser_return
                            bind_subst_lift [OF submonad_asUser.stateAssert_fn] 
                            bind_assoc State_H.sanitiseRegister_def
                            ARMMachineTypes.sanitiseRegister_def
                            bind_comm_mapM_comm [OF asUser_loadWordUser_comm]
                            empty_fail_setRegister word_size
                            stateAssert_mapM_loadWordUser_comm
                            word_less_nat_alt n_msgRegisters_def)
    apply (clarsimp simp: handleFaultReply_def asUser_getRegister_discarded
                          bind_subst_lift [OF stateAssert_stateAssert]
                          pred_conj_def)
    apply (rule bind_apply_cong [OF refl], rename_tac sb s'')
    apply (case_tac sb, simp_all add: word_size n_msgRegisters_def)[1]
   apply (clarsimp simp: handleFaultReply_def asUser_getRegister_discarded
                         bind_subst_lift [OF stateAssert_stateAssert]
                         pred_conj_def)
   apply (rule bind_apply_cong [OF refl], rename_tac sb s'')
   apply (case_tac sb, simp_all add: word_size n_msgRegisters_def)[1]
  apply (clarsimp simp: handleFaultReply_def zipWithM_x_mapM_x
                        zip_Cons syscallMessage_unfold
                        msgRegisters_unfold upto_enum_word
                        mapM_x_Cons mapM_x_Nil)
  apply (rule bind_apply_cong [OF refl], rename_tac sb s'')
  apply (case_tac sb)
   apply (case_tac "msgLength tag < scast n_msgRegisters")
    apply (fastforce simp: bind_assoc asUser_bind_distrib asUser_return
                          zip_Cons mapM_x_Cons mapM_x_Nil
                          asUser_comm [OF neq] asUser_getRegister_discarded
                          submonad_asUser.fn_stateAssert asUser_return
                          bind_subst_lift [OF submonad_asUser.stateAssert_fn] 
                          State_H.sanitiseRegister_def
                          ARMMachineTypes.sanitiseRegister_def
                          n_msgRegisters_def
                    dest: word_less_cases)
   apply (clarsimp simp: bind_assoc asUser_bind_distrib asUser_return
                         zip_Cons mapM_x_Cons mapM_x_Nil
                         asUser_comm [OF neq] asUser_getRegister_discarded
                         submonad_asUser.fn_stateAssert asUser_return
                         bind_subst_lift [OF submonad_asUser.stateAssert_fn] 
                         word_less_nat_alt State_H.sanitiseRegister_def
                         ARMMachineTypes.sanitiseRegister_def take_Cons
                  split: nat.split)
  apply (case_tac "msgLength tag < scast n_msgRegisters")
   apply (fastforce simp: asUser_bind_distrib asUser_return zipWithM_x_mapM_x
                         zip_Cons word_le_make_less mapM_x_Cons mapM_x_Nil
                         asUser_comm [OF neq] asUser_getRegister_discarded
                         submonad_asUser.fn_stateAssert asUser_return
                         bind_subst_lift [OF submonad_asUser.stateAssert_fn] 
                         bind_assoc State_H.sanitiseRegister_def
                         ARMMachineTypes.sanitiseRegister_def
                         bind_comm_mapM_comm [OF asUser_loadWordUser_comm]
                         empty_fail_setRegister word_size
                         stateAssert_mapM_loadWordUser_comm
                         n_msgRegisters_def
                   dest: word_less_cases)
  apply (simp add: n_msgRegisters_def word_le_nat_alt
                   linorder_not_less)
  apply (clarsimp | frule neq0_conv[THEN iffD2, THEN not0_implies_Suc,
                                    OF order_less_le_trans, rotated])+
  apply (subgoal_tac "\<forall>n :: word32. n \<le> scast n_syscallMessage \<longrightarrow> [n .e. msgMaxLength]
                           = [n .e. scast n_syscallMessage]
                               @ [scast n_syscallMessage + 1 .e. msgMaxLength]")
   apply (simp only: upto_enum_word[where y="scast n_syscallMessage :: word32"]
                     upto_enum_word[where y="scast n_syscallMessage + 1 :: word32"])
   apply (clarsimp simp: bind_assoc asUser_bind_distrib asUser_return
                         mapM_x_Cons mapM_x_Nil
                         asUser_comm [OF neq] asUser_getRegister_discarded
                         submonad_asUser.fn_stateAssert asUser_return
                         bind_subst_lift [OF submonad_asUser.stateAssert_fn] 
                         word_less_nat_alt State_H.sanitiseRegister_def
                         ARMMachineTypes.sanitiseRegister_def
                         n_msgRegisters_def empty_fail_setRegister
                         split_def n_msgRegisters_def msgMaxLength_def
                         word_size msgLengthBits_def n_syscallMessage_def
              split del: split_if cong: if_weak_cong)
   apply (simp add: zipWithM_x_mapM_x mapM_x_Nil
                    stateAssert_mapM_loadWordUser_comm
                    asUser_loadWordUser_comm word_size
                    bind_comm_mapM_comm [OF asUser_loadWordUser_comm]
                    asUser_return submonad_asUser.fn_stateAssert
                    mapM_x_Cons bind_assoc
                    mapM_Cons mapM_Nil asUser_bind_distrib
                    take_Cons
             split: nat.split cong: if_weak_cong)
  apply (clarsimp simp: upto_enum_word word_le_nat_alt simp del: upt.simps)
  apply (cut_tac i="unat n" and j="Suc (unat (scast n_syscallMessage :: word32))"
             and k="Suc msgMaxLength" in upt_add_eq_append')
    apply simp
   apply (simp add: n_syscallMessage_def msgMaxLength_unfold)
  apply (simp add: n_syscallMessage_def msgMaxLength_def
                   msgLengthBits_def shiftL_nat
              del: upt.simps upt_rec_numeral)
  done

context kernel_m
begin

(* FIXME: move *)
lemma ccorres_merge_return:
  "ccorres (\<lambda>a c. r (f a) c) xf P P' hs H C \<Longrightarrow> 
   ccorres r xf P P' hs (do x \<leftarrow> H; return (f x) od) C"  
  apply (clarsimp simp: ccorres_underlying_def split_def bind_def return_def split: xstate.splits)
  apply (fastforce simp: unif_rrel_def)
  done

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
  "\<forall>s. \<Gamma> \<turnstile> {s} Call messageInfoFromWord_'proc {t. message_info_lift (ret__struct_message_info_C_' t) = 
            \<lparr>msgLabel_CL = (w_' s >> 12) && 0xFFFFF, msgCapsUnwrapped_CL = (w_' s >> 9) && 7,
                 msgExtraCaps_CL = (w_' s >> 7) && 3, msgLength_CL = let v = w_' s && 0x7F in if v > msgMaxLength then msgMaxLength else v\<rparr>}"
  apply vcg
  apply (simp add: message_info_lift_def Let_def msgMaxLength_def mask_def word_sle_def
                   word_sless_def seL4_MsgMaxLength_def
         split: split_if)
  done

lemma messageInfoFromWord_ccorres [corres]:
  "ccorres (\<lambda>r r'. r = message_info_to_H r') ret__struct_message_info_C_' \<top> {s. w_' s = w} []
           (return (messageInfoFromWord w)) (Call messageInfoFromWord_'proc)"
  apply (rule ccorres_from_spec_modifies [where P = \<top>, simplified])
      apply (rule messageInfoFromWord_spec)
     apply (rule messageInfoFromWord_modifies)
    apply simp
   apply simp
  apply (simp add: return_def messageInfoFromWord_def Let_def message_info_to_H_def 
    Types_H.msgLengthBits_def Types_H.msgExtraCapBits_def msgMaxExtraCaps_def
    shiftL_nat msgMaxLength_def)
  apply (rule shiftr_mask_eq' [symmetric, where m = 20, simplified mask_def, simplified])
  apply (simp add: word_size)
  done
  
lemma getMessageInfo_ccorres:  
  "ccorres (\<lambda>r r'. r = message_info_to_H r') ret__struct_message_info_C_' 
           (tcb_at' sender) UNIV hs (getMessageInfo sender)
           (\<acute>ret__unsigned_long :== CALL getRegister(tcb_ptr_to_ctcb_ptr sender,scast Kernel_C.msgInfoRegister);;
            \<acute>ret__struct_message_info_C :== CALL messageInfoFromWord(\<acute>ret__unsigned_long))"
  unfolding getMessageInfo_def
  apply simp
  apply (rule ccorres_guard_imp2)
  apply ctac
  apply ctac
    apply wp
   apply vcg
  apply (frule (1) obj_at_cslift_tcb)
  apply (clarsimp simp: typ_heap_simps State_H.msgInfoRegister_def ARMMachineTypes.msgInfoRegister_def
    Kernel_C.msgInfoRegister_def Kernel_C.R1_def dest!: c_guard_clift)
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
  apply (clarsimp simp: typ_heap_simps State_H.msgInfoRegister_def ARMMachineTypes.msgInfoRegister_def
    Kernel_C.msgInfoRegister_def Kernel_C.R1_def dest!: c_guard_clift)
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
    apply wp
  apply (simp add: State_H.msgInfoRegister_def ARMMachineTypes.msgInfoRegister_def
                   Kernel_C.msgInfoRegister_def Kernel_C.R1_def
                   State_H.badgeRegister_def ARMMachineTypes.badgeRegister_def
                   Kernel_C.badgeRegister_def Kernel_C.R0_def
                   message_info_to_H_def)
  done

lemma msgRegisters_offset_conv:
  "\<And>offset i. \<lbrakk> offset + i < length State_H.msgRegisters \<rbrakk> \<Longrightarrow> 
   index msgRegisters (unat ((of_nat offset :: word32) + of_nat i)) =
   register_from_H (State_H.msgRegisters ! (offset + i))"
  apply (simp add: msgRegisters_def msgRegisters_unfold fupdate_def)
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
  shows
  "ccorres (\<lambda>r r'. r = unat (r' && mask msgLengthBits)) ret__unsigned_'
     (valid_pspace' and (\<lambda>_. offset < msgMaxLength
                           \<and> is_aligned (option_to_0 buf) msg_align_bits))
     (UNIV \<inter> {s. offset_' s = of_nat offset} \<inter> {s. reg_' s = v}
             \<inter> {s. receiver_' s = tcb_ptr_to_ctcb_ptr thread}
             \<inter> {s. receiveIPCBuffer_' s = option_to_ptr buf}) []
     (setMR thread buf offset v) (Call setMR_'proc)"
  apply (rule ccorres_gen_asm)
  apply (cinit lift: offset_' reg_' receiver_' receiveIPCBuffer_')
   apply (rule ccorres_cond2'[where R=\<top>])
     apply (simp add: msgRegisters_unfold n_msgRegisters_def Collect_const_mem
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
                del: Collect_const)
    apply (simp add: storeWordUser_def bind_assoc del: Collect_const)
    apply (rule ccorres_pre_stateAssert)
    apply (rule ccorres_cond_true)
    apply (ctac add: storeWord_ccorres[simplified])
      apply (rule ccorres_return_C, simp+)[1]
     apply wp
    apply (simp del: Collect_const)
    apply vcg
   apply ctac
     apply (rule ccorres_return_C, simp+)[1]
    apply wp
   apply (simp del: Collect_const)
   apply (vcg exspec=setRegister_modifies)
  apply (simp add: Collect_const_mem option_to_0_def)
  apply (intro impI conjI allI, simp_all)
           apply (rule aligned_add_aligned[where n=msg_align_bits])
              apply simp
             apply (rule is_aligned_mult_triv2
                         [where n=2, simplified, folded word_size_def])
           apply (simp add: msg_align_bits)
          apply (simp add: msgRegisters_unfold n_msgRegisters_def
                           msgLengthBits_def mask_def)
         apply (simp add: word_size_def)
        apply (clarsimp simp: word_size_def field_simps pointerInUserData_c_guard)
       apply (simp add: unat_of_nat32 msgMaxLength_unfold word_bits_def
                        unat_add_lem[THEN iffD1] less_mask_eq msgLengthBits_def
                        word_less_nat_alt)
      apply (clarsimp simp: word_size_def field_simps pointerInUserData_h_t_valid)
     apply (clarsimp simp: pointerInUserData_def typ_at_to_obj_at_arches
                           mask_out_sub_mask)
     apply (subst(asm) less_mask_eq)
      apply (simp add: word_size_def pageBits_def msgMaxLength_unfold)
      apply (simp add: unat_add_lem[THEN iffD1] word_less_nat_alt
                       unat_mult_lem[THEN iffD1] unat_of_nat32 word_bits_def)
     apply clarsimp
    apply (simp add: unat_of_nat32 word_bits_def msgMaxLength_unfold
                     word_le_nat_alt msgRegisters_ccorres n_msgRegisters_def)
   apply (simp add: unat_of_nat32 msgMaxLength_unfold word_bits_def
                    unat_add_lem[THEN iffD1] less_mask_eq msgLengthBits_def
                    word_less_nat_alt)
  apply (simp add: linorder_not_le n_msgRegisters_def)
  done

lemma setMR_ccorres_dc:
  "ccorres dc xfdc
     (valid_pspace' and (\<lambda>_. offset < msgMaxLength
                           \<and> is_aligned (option_to_0 buf) msg_align_bits))
     (UNIV \<inter> {s. offset_' s = of_nat offset} \<inter> {s. reg_' s = v}
             \<inter> {s. receiver_' s = tcb_ptr_to_ctcb_ptr thread}
             \<inter> {s. receiveIPCBuffer_' s = option_to_ptr buf}) []
     (setMR thread buf offset v) (Call setMR_'proc)"
  by (rule ccorres_rel_imp, rule setMR_ccorres, simp)

(* FIXME: move *)
end

crunch valid_pspace'[wp]: setMR "valid_pspace'"

context kernel_m begin

lemma setMRs_lookup_failure_ccorres:
  "ccorres (\<lambda>r r'. r \<noteq> [] \<and> last r = unat (r' && mask msgLengthBits))
           ret__unsigned_'
     (valid_pspace'
               and (\<lambda>_. is_aligned (option_to_0 buf) msg_align_bits)
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
   apply (rule_tac P="valid_pspace'" and P'=UNIV
                in ccorres_inst)
   apply (clarsimp simp: msgFromLookupFailure_def lookup_fault_lift_def
                         Let_def zip_upt_Cons msgMaxLength_unfold
                         mapM_Cons mapM_Nil bind_assoc
               simp del: Collect_const
                  split: split_if_asm)
      apply (rule ccorres_guard_imp2)
       apply csymbr
       apply (ctac add: setMR_ccorres)
         apply (simp add: ccorres_cond_iffs)
         apply (rule ccorres_return_C, simp+)[1]
        apply wp
       apply (simp del: Collect_const)
       apply (vcg exspec=setMR_modifies)
      apply (clarsimp simp: msgMaxLength_unfold Collect_const_mem)
      apply (simp add: lookup_fault_tag_defs)
     apply (rule ccorres_guard_imp2)
      apply csymbr
      apply (ctac add: setMR_ccorres)
        apply (simp add: ccorres_cond_iffs)
        apply (rule ccorres_rhs_assoc)+
        apply csymbr
        apply (ctac add: setMR_ccorres)
          apply (rule ccorres_return_C, simp+)[1]
         apply wp
        apply simp
        apply (vcg exspec=setMR_modifies)
       apply wp
      apply (simp add: Collect_const_mem)
      apply (vcg exspec=setMR_modifies)
     apply (clarsimp simp: msgMaxLength_unfold Collect_const_mem)
     apply (simp add: lookup_fault_missing_capability_lift_def
                      lookup_fault_lift_missing_capability)
     apply (simp add: lookup_fault_tag_defs)
    apply (rule ccorres_guard_imp2)
     apply csymbr
     apply (ctac add: setMR_ccorres)
       apply (simp add: ccorres_cond_iffs)
       apply (rule ccorres_rhs_assoc)+
       apply csymbr
       apply (ctac add: setMR_ccorres_dc)
         apply csymbr
         apply (ctac add: setMR_ccorres)
           apply (rule ccorres_return_C, simp+)[1]
          apply wp
         apply simp
         apply (vcg exspec=setMR_modifies)
        apply wp
       apply (simp add: Collect_const_mem)
       apply (vcg exspec=setMR_modifies)
      apply wp
     apply (simp add: Collect_const_mem)
     apply (vcg exspec=setMR_modifies)
    apply (clarsimp simp: msgMaxLength_unfold Collect_const_mem)
    apply (simp add: lookup_fault_depth_mismatch_lift_def
                     lookup_fault_lift_depth_mismatch)
    apply (simp add: lookup_fault_tag_defs)
   apply (rule ccorres_guard_imp2)
    apply csymbr
    apply (ctac add: setMR_ccorres)
      apply (simp add: ccorres_cond_iffs)
      apply (rule ccorres_rhs_assoc)+
      apply csymbr
      apply (ctac add: setMR_ccorres_dc)
        apply csymbr
        apply (ctac add: setMR_ccorres_dc)
          apply csymbr
          apply (ctac add: setMR_ccorres)
            apply (rule ccorres_return_C, simp+)[1]
           apply (wp | (simp add: Collect_const_mem, vcg exspec=setMR_modifies))+
   apply (clarsimp simp: msgMaxLength_unfold Collect_const_mem)
   apply (simp add: lookup_fault_guard_mismatch_lift_def
                    lookup_fault_lift_guard_mismatch)
   apply (simp add: lookup_fault_tag_defs)
  apply simp
  done

lemma setMRs_syscall_error_ccorres:
  "ccorres (\<lambda>r r'. r = r' && mask msgLengthBits) ret__unsigned_'
     (valid_pspace'
               and (\<lambda>_. is_aligned (option_to_0 buf) msg_align_bits)
               and (\<lambda>_. msg = snd (msgFromSyscallError err)))
           (UNIV \<inter> \<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr thread\<rbrace>
                 \<inter> \<lbrace>\<acute>receiveIPCBuffer = option_to_ptr buf\<rbrace>
                 \<inter> \<lbrace>syscall_error_to_H \<acute>current_syscall_error
                          (lookup_fault_lift \<acute>current_lookup_fault)
                       = Some err\<rbrace>) hs
     (setMRs thread buf msg)
     (Call setMRs_syscall_error_'proc)"
  (is "ccorres ?r ret__unsigned_' ?P ?P' hs ?a ?c")
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
          apply (simp split: split_if_asm)
         apply (subgoal_tac "err = FailedLookup (to_bool (failedLookupWasSource_C err'))
                                      (lookup_fault_to_H (the (lookup_fault_lift luf')))")
          apply (simp add: zip_upt_Cons mapM_Cons bind_assoc)
          apply (rule ccorres_rhs_assoc)+
          apply (ctac add: setMR_ccorres_dc)
            apply (ctac add: setMRs_lookup_failure_ccorres[unfolded msgMaxLength_unfold])
              apply (rule ccorres_return_C, simp+)[1]
             apply (wp | (simp add: Collect_const_mem,
                          vcg exspec=setMR_modifies exspec=setMRs_lookup_failure_modifies))+
         apply (clarsimp simp: option_map_Some_eq2)
        apply (rule ccorres_return_C, simp+)[1]
       apply (rule ccorres_rhs_assoc
                 | (rule ccorres_inst, ctac add: setMR_ccorres_dc)
                 | (rule ccorres_inst, ctac add: setMR_ccorres)
                 | (rule ccorres_return_C, simp+)[1]
                 | wp
                 | (simp del: Collect_const, vcg exspec=setMR_modifies)
               )+
   apply (simp add: msgMaxLength_unfold if_1_0_0 true_def false_def)
   apply (clarsimp split:split_if_asm simp:syscall_error_to_H_def option_map_Some_eq2)
   apply (simp add: msgFromLookupFailure_def
                 split: lookup_failure.split
            | simp add: to_bool_def split: split_if)+
  done

lemma lookupIPCBuffer_aligned_option_to_0:
  "\<lbrace>valid_objs'\<rbrace> lookupIPCBuffer b s \<lbrace>\<lambda>rv s. is_aligned (option_to_0 rv) msg_align_bits\<rbrace>"
  apply (rule hoare_strengthen_post, rule lookupIPCBuffer_valid_ipc_buffer)
  apply (simp add: option_to_0_def valid_ipc_buffer_ptr'_def split: option.split_asm)
  done

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
         apply (fold dc_def)[1]
         apply (rule setMessageInfo_ccorres)
        apply wp
       apply (simp add: Collect_const_mem)
       apply (vcg exspec=setMRs_syscall_error_modifies)
      apply wp
     apply (vcg exspec=setRegister_modifies)
    apply simp
    apply (wp lookupIPCBuffer_aligned_option_to_0)
   apply (simp del: Collect_const)
   apply (vcg exspec=lookupIPCBuffer_modifies)
  apply (simp add: State_H.msgInfoRegister_def ARMMachineTypes.msgInfoRegister_def
                   Kernel_C.msgInfoRegister_def Kernel_C.R1_def
                   State_H.badgeRegister_def ARMMachineTypes.badgeRegister_def
                   Kernel_C.badgeRegister_def Kernel_C.R0_def
                   message_info_to_H_def valid_pspace_valid_objs')
  apply (clarsimp simp: msgLengthBits_def msgFromSyscallError_def
                        syscall_error_to_H_def syscall_error_type_defs
                        mask_def
                 split: split_if_asm)
  done

lemma copyMRs_register_loop_helper:
  fixes n
  defines regs: "regs \<equiv> take (unat n) State_H.msgRegisters"
  shows
  "\<forall>i. i<length regs \<longrightarrow>
   ccorres dc xfdc \<top> \<lbrace>\<acute>i = of_nat i\<rbrace> hs
     (do v \<leftarrow> asUser sender (getRegister (regs ! i));
         asUser receiver (setRegister (regs ! i) v)
      od)
     (Guard ArrayBounds \<lbrace>\<acute>i < 4\<rbrace>
      (\<acute>ret__unsigned_long :== CALL getRegister(tcb_ptr_to_ctcb_ptr sender,
               ucast (index msgRegisters (unat \<acute>i))));;
      Guard ArrayBounds \<lbrace>\<acute>i < 4\<rbrace>
      (CALL setRegister(tcb_ptr_to_ctcb_ptr receiver,
               ucast (index msgRegisters (unat \<acute>i)),
               \<acute>ret__unsigned_long)))"
  apply clarsimp
  apply (rule ccorres_guard_imp)
    apply ctac
      apply ctac
     apply wp
    apply vcg
   apply simp
  apply (clarsimp simp: regs msgRegisters_def msgRegisters_unfold)
  apply (simp |
         (case_tac i,
          clarsimp simp: fupdate_def index_update index_update2 Kernel_C.R2_def
                         Kernel_C.R3_def Kernel_C.R4_def Kernel_C.R5_def
                         Kernel_C.R6_def Kernel_C.R7_def,
          rename_tac i))+
  done

lemma mab_gt_2 [simp]:
  "2 \<le> msg_align_bits" by (simp add: msg_align_bits)

lemma wb_gt_2:
  "2 < word_bits" by (simp add: word_bits_conv)

lemma copyMRs_buffer_loop_helper:
  fixes n
  defines mrs: "mrs \<equiv> [1 + of_nat (length State_H.msgRegisters).e.n]"
  assumes len: "n \<le> msgMaxLength"
  shows
  "\<forall>i<length mrs.
   ccorres dc xfdc (valid_pspace' and K (is_aligned rb msg_align_bits) and K (is_aligned sb msg_align_bits))
           \<lbrace>\<acute>i = of_nat (length State_H.msgRegisters) + of_nat i\<rbrace> hs
           (do v \<leftarrow> loadWordUser
                       (sb + mrs ! i * of_nat (size (undefined :: word32) div 8));
               storeWordUser
                  (rb + mrs ! i * of_nat (size (undefined :: word32) div 8)) v
            od)
           (Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t (Ptr (rb + (\<acute>i * 4 + 4)) :: word32 ptr)\<rbrace>
             (Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t (Ptr (sb + (\<acute>i * 4 + 4)) :: word32 ptr)\<rbrace>
               (Basic (\<lambda>s. globals_update (t_hrs_'_update (hrs_mem_update
                     (heap_update (Ptr (rb + (i_' s * 4 + 4)) :: word32 ptr)
                       (h_val (hrs_mem (t_hrs_' (globals s)))
                         (Ptr (sb + (i_' s * 4 + 4)) :: word32 ptr))))) s))))"
  apply (intro allI impI)
  apply (rule ccorres_guard_imp)
    apply (rule ccorres_pre_loadWordUser)
    apply (unfold storeWordUser_def)
    apply (rule ccorres_pre_stateAssert)
    apply (unfold K_bind_def)
    apply (ctac add: storeWord_ccorres)
   apply (fastforce elim: aligned_add_aligned
                  intro: is_aligned_mult_triv2 [where n=2, simplified]
                   simp: word_size wb_gt_2)
  apply (clarsimp simp: mrs msgRegisters_unfold upto_enum_word word_size
                        pointerInUserData_h_t_valid pointerInUserData_c_guard
                        typ_heap_simps'
                 split: split_if_asm simp del: upt.simps)
  done

(* FIXME move *)
lemma mapM_only_length:
  "do ys \<leftarrow> mapM f xs;
      g (length ys)
   od =
   do _ \<leftarrow> mapM_x f xs;
      g (length xs)
   od"
  by (subst bind_return_subst [OF mapM_length])
     (rule mapM_discarded)

declare split_if[split]
lemma copyMRs_buffer_loop_ccorres:
  fixes n
  defines i0: "i0 \<equiv> min (of_nat (length State_H.msgRegisters)) n"
  assumes lt: "unat n \<le> msgMaxLength"
  shows
  "ccorres (\<lambda>rv rv'. rv' = n) i_'
      (valid_pspace' and K (is_aligned rb msg_align_bits) and K (is_aligned sb msg_align_bits))
      \<lbrace>\<acute>i = i0\<rbrace> hs
      (mapM_x (\<lambda>i. do v \<leftarrow> loadWordUser
                              (sb + i * of_nat (size (undefined::word32) div 8));
                      storeWordUser
                              (rb + i * of_nat (size (undefined::word32) div 8)) v
                   od)
            [1 + of_nat (length State_H.msgRegisters).e.n])
    (While \<lbrace>\<acute>i < n\<rbrace>
         (Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t (Ptr (rb + (\<acute>i * 4 + 4)) :: word32 ptr)\<rbrace>
             (Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t (Ptr (sb + (\<acute>i * 4 + 4)) :: word32 ptr)\<rbrace>
               (Basic (\<lambda>s. globals_update (t_hrs_'_update (hrs_mem_update
                     (heap_update (Ptr (rb + (i_' s * 4 + 4)) :: word32 ptr)
                       (h_val (hrs_mem (t_hrs_' (globals s)))
                         (Ptr (sb + (i_' s * 4 + 4)) :: word32 ptr))))) s)));;
       \<acute>i :== \<acute>i + 1))"
  using lt
  apply (case_tac "of_nat (length State_H.msgRegisters) \<le> n")
   apply (simp only: i0 min.absorb1)
   apply (rule ccorres_rel_imp)
    apply (rule ccorres_mapM_x_while' [OF copyMRs_buffer_loop_helper])
        apply (clarsimp simp: word_le_nat_alt msgMaxLength_def msgLengthBits_def)
       apply (clarsimp simp: upto_enum_def msgRegisters_unfold)
       apply unat_arith
      apply vcg
      apply simp
     apply wp
       apply simp
    apply (fastforce simp: word_bits_def msgRegisters_unfold upto_enum_def msgMaxLength_def)
   apply (clarsimp simp: upto_enum_def msgRegisters_unfold word_bits_def)
   apply unat_arith
  apply (subgoal_tac "[1 + of_nat (length State_H.msgRegisters).e.n] = []")
   apply (clarsimp simp: mapM_x_Nil i0 min_def)
   apply (subst ccorres_expand_while_iff [symmetric])
   apply (rule ccorres_guard_imp2)
    apply (rule ccorres_cond_false)
    apply (rule ccorres_return_Skip')
   apply simp
  apply (clarsimp simp: upto_enum_def msgRegisters_unfold)
  apply unat_arith
  done

lemma length_upto_enum_cases:
  fixes a :: word32
  shows "length [a .e. b] = (if a \<le> b then Suc (unat b) - unat a else 0)"
  apply (case_tac "a \<le> b")
   apply (clarsimp simp: length_upto_enum)
  apply (clarsimp simp: upto_enum_def)
  apply unat_arith
  done

(* FIXME move *)
lemma copyMRs_ccorres [corres]:
  "ccorres (\<lambda>r r'. r = r' && mask msgLengthBits) ret__unsigned_'
    (valid_pspace' and tcb_at' sender and tcb_at' receiver
        and K (sendBuffer \<noteq> Some 0) and K (recvBuffer \<noteq> Some 0)
        and K (case_option True (\<lambda>x. is_aligned x msg_align_bits) sendBuffer)
        and K (case_option True (\<lambda>x. is_aligned x msg_align_bits) recvBuffer)
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
   apply (rule_tac P = "length (take (unat n) State_H.msgRegisters) <
                        2 ^ word_bits"
                in ccorres_gen_asm)
   apply (rule ccorres_split_nothrow_novcg)
       apply (rule ccorres_mapM_x_while [OF copyMRs_register_loop_helper[unfolded ucast_id]])
          apply (clarsimp simp: n_msgRegisters_def
                                msgRegisters_unfold min_def)
          apply unat_arith
         apply vcg
         apply simp
        apply wp
       apply assumption
      apply ceqv
     apply (rule_tac A="valid_pspace'" in ccorres_guard_imp)
       apply (wpc, simp add: option_to_0_def)
        apply (rule ccorres_split_throws, rule ccorres_return_C, simp+)
        apply vcg
       apply (wpc, simp_all add: option_to_0_def)[1]
        apply (rule ccorres_split_throws, rule ccorres_return_C, simp+)
        apply vcg
       apply (subst mapM_only_length)
       apply (rule ccorres_split_nothrow_novcg)
           apply (rule copyMRs_buffer_loop_ccorres)
           apply (fastforce simp: msgLengthBits_def word_less_nat_alt
                           dest: eq_mask_less)
          apply ceqv
         apply (rule ccorres_return_C, simp_all)[1]
        apply wp
       apply (clarsimp simp: guard_is_UNIV_def upto_enum_def
                             min_def word_le_nat_alt
                             msgRegisters_unfold)
      apply clarsimp
     apply assumption
    apply (wp mapM_x_wp)
    apply (rule subset_refl)
   apply (clarsimp simp: guard_is_UNIV_def
                         msgRegisters_unfold mask_def
                         Types_H.msgLengthBits_def min_def word_le_nat_alt)
   apply unat_arith
  apply (fastforce simp: msgRegisters_unfold
                        msgLengthBits_def min_def word_bits_def)
  done

declare zipWith_Nil2[simp]

declare zipWithM_x_Nil2[simp]

lemma getRestartPC_ccorres [corres]:
  "ccorres (op =) ret__unsigned_long_' \<top>
     (UNIV \<inter> \<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr thread\<rbrace>) hs
     (asUser thread (getRegister register.FaultInstruction))
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

lemma setMR_tcbFault_obj_at:
  "\<lbrace>obj_at' (\<lambda>tcb. P (tcbFault tcb)) t\<rbrace> setMR t' b r v
   \<lbrace>\<lambda>rv. obj_at' (\<lambda>tcb. P (tcbFault tcb)) t\<rbrace>"
  apply (simp add: setMR_def split del: split_if)
  apply (rule hoare_pre)
   apply (wp asUser_tcbFault_obj_at | wpc)+
  apply simp
  done

(* FIXME move *)
lemma from_bool_to_bool_and_1 [simp]:
  assumes r_size: "1 < size r"
  shows "from_bool (to_bool (r && 1)) = r && 1"
proof -
  from r_size have "r && 1 < 2"
    by (simp add: and_mask_less_size [where n=1, unfolded mask_def, simplified])
  thus ?thesis
    by (fastforce simp add: from_bool_def to_bool_def dest: word_less_cases)
qed

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

lemma user_getreg_rv:
  "\<lbrace>obj_at' (\<lambda>tcb. P (tcbContext tcb r)) t\<rbrace> asUser t (getRegister r) \<lbrace>\<lambda>rv s. P rv\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp threadGet_wp)
  apply (clarsimp simp: obj_at'_def projectKOs getRegister_def in_monad)
  done

lemma exceptionMessage_ccorres:
  "n < unat n_exceptionMessage
      \<Longrightarrow> register_from_H (State_H.exceptionMessage ! n)
             = index exceptionMessage n"
  apply (simp add: exceptionMessage_def State_H.exceptionMessage_def
                   ARMMachineTypes.exceptionMessage_def)
  apply (simp add: Arrays.update_def n_exceptionMessage_def fcp_beta nth_Cons'
                   fupdate_def
            split: split_if)
  done

lemma asUser_obj_at_elsewhere:
  "\<lbrace>obj_at' (P :: tcb \<Rightarrow> bool) t' and (\<lambda>_. t \<noteq> t')\<rbrace> asUser t m \<lbrace>\<lambda>rv. obj_at' P t'\<rbrace>"
  apply (rule hoare_gen_asm')
  apply (simp add: asUser_def split_def)
  apply (wp threadGet_wp)
  apply clarsimp
  done

lemma setMRs_fault_ccorres [corres]:
  "ccorres (\<lambda>r r'. r = r' && mask msgLengthBits) ret__unsigned_'
           (valid_pspace' and obj_at' (\<lambda>tcb. tcbFault tcb = Some ft) sender
                          and tcb_at' receiver
                          and K (buffer \<noteq> Some 0)
                          and K (is_aligned (option_to_0 buffer) msg_align_bits)
                          and K (sender \<noteq> receiver))
           (UNIV \<inter> \<lbrace>\<acute>sender = tcb_ptr_to_ctcb_ptr sender\<rbrace>
                 \<inter> \<lbrace>\<acute>receiver = tcb_ptr_to_ctcb_ptr receiver\<rbrace>
                 \<inter> \<lbrace>\<acute>receiveIPCBuffer = Ptr (option_to_0 buffer)\<rbrace>) hs
    (makeFaultMessage ft sender >>= (\<lambda>ms. setMRs receiver buffer (snd ms)))
    (Call setMRs_fault_'proc)"
proof -
  let ?obj_at_ft = "obj_at' (\<lambda>tcb. tcbFault tcb = Some ft) sender"
  note symb_exec_r_fault = ccorres_symb_exec_r_known_rv_UNIV
          [where xf'=ret__unsigned_long_' and R="?obj_at_ft" and R'=UNIV]

  show ?thesis
    apply (unfold K_def)
    apply (intro ccorres_gen_asm)
    apply (cinit' lift: sender_' receiver_' receiveIPCBuffer_' simp: whileAnno_def)
     apply (simp add: makeFaultMessage_def setMRs_to_setMR
                 del: Collect_const split del: split_if)
     apply (rule_tac val="fault_to_fault_tag ft" in symb_exec_r_fault)
        apply (vcg, clarsimp)
        apply (drule(1) obj_at_cslift_tcb)
        apply (clarsimp simp: ctcb_relation_def typ_heap_simps'
                              cfault_rel_def fault_lift_def Let_def
                       split: split_if_asm)
       apply ceqv
      apply wpc
         apply (simp add: bind_assoc fault_tag_defs ccorres_cond_iffs
                          Collect_True Collect_False
                          zipWithM_mapM zip_append2 mapM_append
                     del: Collect_const split del: split_if)
         apply (rule ccorres_symb_exec_l)
            apply (rule ccorres_stateAssert)
            apply (rule_tac P="length msg = unat n_exceptionMessage"
                       in ccorres_gen_asm)
            apply (simp add: n_exceptionMessage_def msgMaxLength_unfold
                             zip_upt_Cons mapM_Nil mapM_Cons bind_assoc
                             mapM_discarded
                        del: Collect_const upt.simps upt_rec_numeral
                           split del: split_if)
            apply (rule ccorres_rhs_assoc)+
            apply csymbr
            apply (simp del: Collect_const split del: split_if)
            apply (rule ccorres_rhs_assoc2, rule ccorres_split_nothrow)
                apply (rule_tac F="K $ obj_at' (\<lambda>tcb. map (tcbContext tcb) State_H.exceptionMessage = msg) sender"
                            in ccorres_mapM_x_while)
                    apply (clarsimp simp: setMR_def msgRegisters_unfold liftM_def[symmetric]
                               split del: split_if)
                    apply (rule ccorres_guard_imp2)
                     apply (rule_tac t=sender and r="State_H.exceptionMessage ! n"
                               in ccorres_add_getRegister)
                     apply ctac
                       apply (rule_tac P="\<lambda>s. rv = msg ! n" in ccorres_cross_over_guard)
                       apply ctac
                      apply (wp user_getreg_rv)
                     apply simp
                     apply (vcg exspec=getRegister_modifies)
                    apply (clarsimp simp: obj_at'_def projectKOs objBits_simps
                                          exceptionMessage_ccorres n_exceptionMessage_def
                                          unat_of_nat32[unfolded word_bits_def])
                    apply (simp add: msgRegisters_ccorres[symmetric] n_msgRegisters_def
                                     msgRegisters_unfold word_of_nat_less)
                   apply simp
                  apply (rule allI, rule conseqPre)
                  apply (vcg exspec=setRegister_modifies exspec=getRegister_modifies)
                  apply clarsimp
                 apply (simp add: setMR_def split del: split_if)
                 apply (rule hoare_pre)
                  apply (wp asUser_obj_at_elsewhere | wpc | simp)+
                apply (simp add: word_bits_def)
               apply ceqv
              apply (rule ccorres_move_c_guard_tcb)
              apply (rule_tac val="userExceptionNumber ft" in symb_exec_r_fault)
                 apply (vcg, clarsimp)
                 apply (drule(1) obj_at_cslift_tcb)
                 apply (clarsimp simp: ctcb_relation_def typ_heap_simps
                                       cfault_rel_def fault_lift_def
                                       fault_user_exception_lift_def Let_def
                                split: split_if_asm)
                apply ceqv
               apply (ctac add: setMR_ccorres_dc)
                 apply (rule ccorres_move_c_guard_tcb)
                 apply (rule_tac val="userExceptionErrorCode ft" in symb_exec_r_fault)
                    apply (vcg, clarsimp)
                    apply (drule(1) obj_at_cslift_tcb)
                    apply (clarsimp simp: ctcb_relation_def typ_heap_simps
                                          cfault_rel_def fault_lift_def
                                          fault_user_exception_lift_def Let_def
                                   split: split_if_asm)
                   apply ceqv
                  apply (ctac add: setMR_ccorres)
                    apply (rule ccorres_return_C, simp+)[1]
                   apply wp
                  apply (simp del: Collect_const)
                  apply (vcg exspec=setMR_modifies)
                 apply (clarsimp simp: option_to_ptr_def guard_is_UNIVI)
                apply (wp setMR_tcbFault_obj_at)
               apply simp
               apply (vcg exspec=setMR_modifies)
              apply (clarsimp simp: option_to_ptr_def guard_is_UNIVI)
             apply (simp add: split_def)
             apply (wp mapM_x_wp' setMR_tcbFault_obj_at
                         | simp)+
            apply (fold whileAnno_def[where I=UNIV and V=undefined])
            apply (vcg exspec=getRegister_modifies exspect=setRegister_modifies)
             apply simp
            apply simp
           apply (wp asUser_inv mapM_wp' getRegister_inv)
          apply simp
          apply (wp asUser_inv mapM_wp' getRegister_inv hoare_drop_imps
                    asUser_get_registers asUser_const_rv)
         apply simp
        apply (rule_tac P="zip [Suc (Suc 0) ..< msgMaxLength] list = [(2, hd list), (3, hd (tl list))]"
                   in ccorres_gen_asm)
        apply (simp add: bind_assoc fault_tag_defs ccorres_cond_iffs
                         Collect_True Collect_False zipWithM_mapM
                         zip_upt_Cons msgMaxLength_unfold
                         mapM_Cons mapM_Nil
                    del: Collect_const)
        apply (rule ccorres_rhs_assoc)+
        apply (ctac(no_vcg))
         apply (rule ccorres_stateAssert)
         apply (ctac(no_vcg) add: setMR_ccorres_dc)
          apply (rule ccorres_move_c_guard_tcb)
          apply (rule_tac val="vmFaultAddress ft" in symb_exec_r_fault)
             apply (rule conseqPre, vcg, clarsimp)
             apply (drule(1) obj_at_cslift_tcb)
             apply (clarsimp simp: ctcb_relation_def typ_heap_simps
                                   cfault_rel_def fault_lift_def
                                   fault_vm_fault_lift_def Let_def
                            split: split_if_asm)
            apply ceqv
           apply (ctac(no_vcg) add: setMR_ccorres_dc)
            apply (rule_tac val="hd (vmFaultArchData ft)" in symb_exec_r_fault)
               apply (rule conseqPre, vcg, clarsimp)
               apply (drule(1) obj_at_cslift_tcb)
               apply (clarsimp simp: typ_heap_simps')
               apply (clarsimp simp: ctcb_relation_def
                                     cfault_rel_def fault_lift_def
                                     fault_vm_fault_lift_def Let_def
                              split: split_if_asm)
              apply ceqv
             apply (ctac(no_vcg) add: setMR_ccorres_dc)
              apply (rule_tac val="vmFaultArchData ft ! 1" in symb_exec_r_fault)
                 apply (rule conseqPre, vcg, clarsimp)
                 apply (drule(1) obj_at_cslift_tcb)
                 apply (clarsimp simp: typ_heap_simps')
                 apply (clarsimp simp: ctcb_relation_def
                                       cfault_rel_def fault_lift_def
                                       fault_vm_fault_lift_def Let_def
                                split: split_if_asm)
                apply ceqv
               apply (ctac(no_vcg) add: setMR_ccorres)
                apply (rule ccorres_return_C, simp+)[1]
               apply wp
              apply (clarsimp simp: option_to_ptr_def)
              apply (subgoal_tac "case list of [a, b] \<Rightarrow> True | _ \<Rightarrow> True")
               apply (simp add: zip_upt_Cons guard_is_UNIVI split: list.split_asm)
              apply (simp split: list.split)
             apply (wp setMR_tcbFault_obj_at asUser_inv[OF getRestartPC_inv] | 
                       simp add: option_to_ptr_def guard_is_UNIVI
                            del: Collect_const split del: split_if)+
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
                                  cfault_rel_def fault_lift_def Let_def
                                  fault_cap_fault_lift_def
                           split: split_if_asm)
           apply ceqv
          apply (ctac(no_vcg) add: setMR_ccorres_dc)
           apply (rule_tac val="from_bool (capFaultInReceivePhase ft)" in symb_exec_r_fault)
              apply (rule conseqPre, vcg, clarsimp)
              apply (drule(1) obj_at_cslift_tcb)
              apply (clarsimp simp: typ_heap_simps' ctcb_relation_def
                                    cfault_rel_def fault_lift_def Let_def
                                    fault_cap_fault_lift_def
                                    from_bool_to_bool_and_1 word_size
                             split: split_if_asm)
             apply ceqv
            apply (ctac(no_vcg) add: setMR_ccorres_dc)
             apply (rule ccorres_move_c_guard_tcb)
             apply (rule_tac P="obj_at' (\<lambda>tcb. tcbFault tcb = Some ft) sender"
                          in ccorres_cross_over_guard)
             apply (ctac(no_vcg) add: setMRs_lookup_failure_ccorres[unfolded msgMaxLength_unfold])
              apply simp
              apply (rule ccorres_return_C, simp+)[1]
             apply (wp setMR_tcbFault_obj_at)
           apply (clarsimp simp: option_to_ptr_def Collect_const_mem guard_is_UNIV_def)
           apply (rule conjI)
            apply (simp add: from_bool_def split: bool.split)
           apply clarsimp
           apply (drule(1) obj_at_cslift_tcb)
           apply (clarsimp simp: typ_heap_simps' ctcb_relation_def
                                 cfault_rel_def fault_lift_def Let_def
                                 fault_cap_fault_lift_def is_cap_fault_def
                          split: split_if_asm)
          apply (wp setMR_tcbFault_obj_at
                    asUser_inv[OF getRestartPC_inv]
                    | (rule guard_is_UNIVI, clarsimp simp: option_to_ptr_def))+
      apply (simp add: fault_tag_defs Collect_True Collect_False
                       ccorres_cond_iffs zipWithM_mapM mapM_append
                       zip_append2 bind_assoc
                  del: Collect_const)
      apply (rule ccorres_symb_exec_l)
         apply (rule ccorres_stateAssert)
         apply (rule_tac P="length msg = unat n_syscallMessage" in ccorres_gen_asm)
         apply (simp add: msgMaxLength_unfold n_syscallMessage_def zip_upt_Cons
                          mapM_Cons mapM_Nil mapM_discarded
                     del: Collect_const upt_rec_numeral)
         apply (simp only: mapM_x_append[where xs="take (unat n_msgRegisters) (zip as bs)"
                                         and ys="drop (unat n_msgRegisters) (zip as bs)"
                                         for as bs, simplified] bind_assoc)
         apply (rule ccorres_rhs_assoc)+
         apply csymbr
         apply (simp del: Collect_const)
         apply (rule ccorres_rhs_assoc2, rule ccorres_split_nothrow_novcg)
             apply (simp only: whileAnno_def)
             apply (rule_tac F="K $ obj_at' (\<lambda>tcb. map (tcbContext tcb) State_H.syscallMessage = msg) sender"
                          in ccorres_mapM_x_while)
                 apply (clarsimp simp: n_msgRegisters_def)
                 apply (rule ccorres_guard_imp2)
                  apply (rule_tac t=sender and r="State_H.syscallMessage ! n"
                            in ccorres_add_getRegister)
                  apply (ctac(no_vcg))
                   apply (rule_tac P="\<lambda>s. rv = msg ! n" in ccorres_cross_over_guard)
                   apply (simp add: setMR_def length_msgRegisters n_msgRegisters_def
                                    liftM_def[symmetric])
                   apply ctac
                  apply (wp user_getreg_rv)
                 apply (clarsimp simp: msgRegisters_ccorres n_msgRegisters_def
                                       syscallMessage_ccorres n_syscallMessage_def
                                       unat_of_nat32[unfolded word_bits_def])
                 apply (clarsimp simp: obj_at'_def projectKOs word_of_nat_less)
                apply (simp add: n_msgRegisters_def)
               apply (rule allI, rule conseqPre, vcg exspec=setRegister_modifies exspec=getRegister_modifies)
               apply simp
              apply (simp add: setMR_def split del: split_if)
              apply (rule hoare_pre)
               apply (wp asUser_obj_at_elsewhere | wpc)+
              apply simp
             apply (simp add: word_bits_def)
            apply ceqv
           apply (rule ccorres_Cond_rhs)
            apply (rule ccorres_rhs_assoc)+
            apply (simp del: Collect_const)
            apply (rule ccorres_split_nothrow_novcg)
                apply (simp only: whileAnno_def)
                apply (rule_tac F="K $ (obj_at' (\<lambda>tcb. map (tcbContext tcb) State_H.syscallMessage = msg)
                                           sender and valid_pspace')"
                           in ccorres_mapM_x_while'[where i="unat n_msgRegisters"])
                    apply (clarsimp simp: setMR_def n_msgRegisters_def length_msgRegisters
                                          option_to_0_def liftM_def[symmetric]
                                   split: option.split_asm)
                    apply (rule ccorres_guard_imp2)
                     apply (rule_tac t=sender and r="State_H.syscallMessage ! (n + unat n_msgRegisters)"
                                  in ccorres_add_getRegister)
                     apply (ctac(no_vcg))
                      apply (rule_tac P="\<lambda>s. rv = msg ! (n + unat n_msgRegisters)"
                                   in ccorres_cross_over_guard)
                      apply (simp add: storeWordUser_def)
                      apply (rule ccorres_pre_stateAssert)
                      apply (ctac add: storeWord_ccorres[unfolded fun_app_def])
                     apply (simp add: pred_conj_def)
                     apply (wp user_getreg_rv)
                    apply (clarsimp simp: n_syscallMessage_def n_msgRegisters_def
                                          syscallMessage_ccorres msgRegisters_ccorres
                                          unat_add_lem[THEN iffD1] unat_of_nat32
                                          word_bits_def word_size_def)
                    apply (simp only:field_simps imp_ex imp_conjL)
                    apply (clarsimp simp: pointerInUserData_c_guard obj_at'_def
                                          pointerInUserData_h_t_valid
                                          projectKOs objBits_simps word_less_nat_alt
                                          unat_add_lem[THEN iffD1] unat_of_nat)
                    apply (clarsimp simp: pointerInUserData_h_t_valid rf_sr_def)
                    apply (erule aligned_add_aligned)
                      apply (rule aligned_add_aligned[where n=2])
                        apply (simp add: is_aligned_def)
                       apply (rule is_aligned_mult_triv2 [where n=2, simplified])
                       apply (simp add: wb_gt_2)+
                   apply (simp add: n_msgRegisters_def)
                  apply (vcg exspec=getRegister_modifies)
                  apply simp
                 apply (simp add: setMR_def n_msgRegisters_def length_msgRegisters)
                 apply (rule hoare_pre)
                  apply (wp | wpc)+
                 apply simp
                apply (simp add: n_msgRegisters_def word_bits_def)
               apply ceqv
              apply (rule_tac val="unknownSyscallNumber ft" in symb_exec_r_fault)
                 apply (rule conseqPre, vcg, clarsimp)
                 apply (drule(1) obj_at_cslift_tcb)
                 apply (clarsimp simp: typ_heap_simps' ctcb_relation_def
                                       cfault_rel_def fault_lift_def Let_def
                                       fault_unknown_syscall_lift_def
                                split: split_if_asm)
                apply ceqv
               apply (simp add: setMR_def msgRegisters_unfold del: Collect_const)
               apply wpc
                apply (rule ccorres_inst[where P=\<top> and P'=UNIV], simp add: option_to_0_def)
               apply (simp add: bind_assoc storeWordUser_def del: Collect_const)
               apply (rule ccorres_pre_stateAssert)
               apply (ctac(no_vcg) add: storeWord_ccorres[unfolded fun_app_def])
                 apply ((rule ccorres_return_C ccorres_Guard | simp)+)[1]
                apply wp
               apply (simp add: msgLengthBits_def mask_def)
              apply (clarsimp simp: guard_is_UNIV_def option_to_0_def n_msgRegisters_def
                                    word_size_def)
              apply (auto simp add: pointerInUserData_c_guard
                                    pointerInUserData_h_t_valid rf_sr_def)[1]
             apply simp
             apply (rule_tac Q="\<lambda>rv. valid_pspace' and ?obj_at_ft" in hoare_post_imp)
              apply (clarsimp simp: word_size_def option_to_0_def)
              apply (erule aligned_add_aligned)
                apply (simp add: is_aligned_def)
                apply simp+
             apply (simp add: split_def)
             apply (wp mapM_x_wp' setMR_tcbFault_obj_at | simp)+
            apply (simp add: guard_is_UNIV_def)
           apply (subgoal_tac "buffer = None")
            apply (simp add: mapM_discarded[symmetric])
            apply (rule_tac P="\<lambda>a. ccorres ?r ?xf ?Pre ?Pre' ?hs (a >>= ?b) ?c" in subst)
             apply (rule mapM_length_cong[OF refl])
             apply (clarsimp simp: setMR_def length_msgRegisters n_msgRegisters_def
                                   set_zip)
             apply (rule refl)
            apply (simp add: mapM_return setMR_def msgRegisters_unfold)
            apply (rule ccorres_return_C, simp+)[1]
           apply (simp add: option_to_0_def split: option.split_asm)
          apply simp
          apply (wp hoare_drop_imps)
          apply (rule mapM_x_wp')
          apply (clarsimp simp: setMR_def split del: split_if)
          apply (rule hoare_pre)
           apply (wp asUser_obj_at_elsewhere | wpc)+
          apply simp
         apply (clarsimp simp: guard_is_UNIV_def n_msgRegisters_def msgLengthBits_def
                               mask_def)
        apply (wp asUser_inv mapM_wp' getRegister_inv)
       apply simp
       apply (wp hoare_drop_imps asUser_get_registers
                 asUser_inv mapM_wp' getRegister_inv
                 asUser_const_rv)
      apply simp
     apply (rule guard_is_UNIVI, clarsimp simp: option_to_ptr_def)
    apply (clarsimp simp: msgMaxLength_unfold length_syscallMessage
                          State_H.exceptionMessage_def
                          ARMMachineTypes.exceptionMessage_def
                          n_exceptionMessage_def)
    apply (drule(1) obj_at_cslift_tcb[where thread=sender])
    apply (clarsimp simp: obj_at'_def projectKOs objBits_simps)
    apply (clarsimp simp: msgFromLookupFailure_def split: lookup_failure.split)
    apply (clarsimp simp: ctcb_relation_def cfault_rel_def fault_lift_def
                          Let_def zip_upt_Cons
                   split: split_if_asm)
    done
qed

lemma makeFaultMessage2:
  "makeFaultMessage ft thread
    = (do x \<leftarrow> makeFaultMessage ft thread;
       return (case ft of CapFault _ _ _ \<Rightarrow> 1
                   | VMFault _ _ \<Rightarrow> 2 | UnknownSyscallException _ \<Rightarrow> 3
                   | UserException _ _ \<Rightarrow> 4, snd x) od)"
  by (simp add: makeFaultMessage_def split: fault.split)

lemma doFaultTransfer_ccorres [corres]:
  "ccorres dc xfdc (valid_pspace' and tcb_at' sender and tcb_at' receiver
                    and K (buffer \<noteq> Some 0) and K (receiver \<noteq> sender)
                    and K (is_aligned (option_to_0 buffer) msg_align_bits))
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
                  | VMFault _ _ \<Rightarrow> 2 | UnknownSyscallException _ \<Rightarrow> 3
                  | UserException _ _ \<Rightarrow> 4"
              in ccorres_symb_exec_r_known_rv_UNIV
                   [where xf'=ret__unsigned_long_' and R'=UNIV])
       apply (rule conseqPre, vcg, clarsimp)
       apply (drule(1) obj_at_cslift_tcb)
       apply (clarsimp simp: typ_heap_simps' ctcb_relation_def
                             cfault_rel_def fault_lift_def Let_def
                             fault_tag_defs
                      split: split_if_asm)
      apply ceqv
     apply csymbr
     apply (ctac (no_vcg, c_lines 2) add: setMessageInfo_ccorres)
       apply (ctac add: setRegister_ccorres[unfolded dc_def])
      apply wp
     apply (simp add: badgeRegister_def ARMMachineTypes.badgeRegister_def
                      Kernel_C.badgeRegister_def "StrictC'_register_defs")
    apply (clarsimp simp: message_info_to_H_def guard_is_UNIVI
                          mask_def msgLengthBits_def
                   split: fault.split)
   apply wp
    apply (simp add: setMRs_to_setMR zipWithM_mapM split_def)
    apply (wp mapM_wp' setMR_tcbFault_obj_at | simp)+
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
  apply (simp add: unifyFailure_def rethrowFailure_def const_def o_def 
                   handleE'_def throwError_def)
  apply (clarsimp simp: ccorres_underlying_def bind_def split_def return_def 
                  split: xstate.splits sum.splits)
  apply (drule (1) bspec)
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (erule_tac x=n in allE)
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
    (CT root idx dpt) \<Rightarrow>  ctReceiveRoot_C ctc = root \<and>
                          ctReceiveIndex_C  ctc= idx \<and>
                          unat (ctReceiveDepth_C ctc) = dpt"


lemma capTransferFromWords_ccorres [corres]:
  "ccorres cct_relation ret__struct_cap_transfer_C_' 
           (valid_pspace' and K (is_aligned ptr 2))
           (UNIV \<inter> \<lbrace>\<acute>wptr = Ptr ptr\<rbrace>) hs
           (capTransferFromWords ptr)
           (Call capTransferFromWords_'proc)"
  apply (cinit lift: wptr_')
   apply (rule ccorres_pre_loadWordUser)+
   apply (rule_tac P=\<top> 
               and P'="{s. cslift s (Ptr ptr) = Some rv \<and> 
                           cslift s (Ptr (ptr + 4)) = Some rva \<and>
                           cslift s (Ptr (ptr + 8)) = Some rvb}"
                in ccorres_from_vcg_throws)
   apply (rule allI, rule conseqPre, vcg)
   apply (clarsimp simp: typ_heap_simps')
   apply (simp add: return_def)
   apply (simp add: cct_relation_def)
  apply (clarsimp simp: word_size valid_ipc_buffer_ptr'_def)
  apply safe
   apply (erule aligned_add_aligned | simp add: is_aligned_def word_bits_conv)+
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
   apply (rule ccorres_add_return2)
   apply (ctac (no_vcg))
    apply (ctac (no_vcg) add: ccorres_return_C)
   apply wp
  apply clarsimp
  apply (simp add: seL4_MsgLengthBits_def 
                   seL4_MsgExtraCapBits_def
                   seL4_MsgMaxLength_def
                   word_size word_sle_def
                   msgMaxLength_def msgMaxExtraCaps_def
                   msgLengthBits_def msgExtraCapBits_def)
 apply (clarsimp simp: valid_ipc_buffer_ptr'_def)
 apply (erule aligned_add_aligned, simp_all add: is_aligned_def)
done



lemma getExtraCPtr_ccorres [corres]:
  "ccorres (op =) ret__unsigned_long_'
           (valid_pspace' and valid_ipc_buffer_ptr' buffer)
           (UNIV \<inter> \<lbrace>\<acute>bufferPtr = Ptr buffer\<rbrace> \<inter> \<lbrace>unat \<acute>i = i\<rbrace>) hs
           (getExtraCPtr buffer i)
           (Call getExtraCPtr_'proc)"
  apply (cinit lift: bufferPtr_' i_')
   apply (rule ccorres_add_return2)
   apply (rule ccorres_pre_loadWordUser)
   apply (rule_tac P=\<top> and
     P'= "{s. cslift s (Ptr (buffer + (8 + msgMaxLength * 4 + ia * 4)))
                 = Some rv}"
     in ccorres_from_vcg_throws)
   apply (rule allI, rule conseqPre, vcg)
   apply (clarsimp simp: return_def seL4_MsgMaxLength_def msgMaxLength_def typ_heap_simps')
  apply (clarsimp simp: bufferCPtrOffset_def word_size msgMaxLength_def
                        seL4_MsgLengthBits_def  Types_H.msgLengthBits_def
                        field_simps)
  apply (clarsimp simp: valid_ipc_buffer_ptr'_def)
  apply (erule aligned_add_aligned, simp_all add: word_bits_def)
   apply (rule_tac n=2 in aligned_add_aligned, simp_all add: word_bits_def)
    apply (rule is_aligned_mult_triv2 [where n = 2, simplified])
   apply (simp add: is_aligned_def)
done


lemma loadCapTransfer_ctReceiveDepth:
  "\<lbrace>\<top>\<rbrace> loadCapTransfer buffer \<lbrace>\<lambda>rv s. ctReceiveDepth rv < 2 ^ word_bits\<rbrace>"
  apply (simp add: loadCapTransfer_def capTransferFromWords_def)
  apply wp
    apply (rule_tac Q'="\<lambda>_ _. True" in hoare_post_eq)
     apply simp
     apply (simp only: word_bits_len_of[symmetric])
     apply (subst unat_lt2p, simp) 
    apply wp
done
(* FIXME: move *)
lemma cte_at_0' [dest!]:
  "\<lbrakk> cte_at' 0 s; no_0_obj' s \<rbrakk> \<Longrightarrow> False"
  apply (clarsimp simp: cte_wp_at_obj_cases')
  apply (auto simp: tcb_cte_cases_def is_aligned_def dest!:tcb_aligned' split: split_if_asm) 
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
  apply (rule UNIV_I)  -- "still a schematic here ..."
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
   apply (unfold K_bind_def)
   apply (ctac add: storeWord_ccorres)
  apply (clarsimp simp: bufferCPtrOffset_def word_size msgMaxLength_def
                        seL4_MsgLengthBits_def seL4_MsgMaxLength_def Types_H.msgLengthBits_def
                        field_simps)
  apply (subgoal_tac " is_aligned (buffer + (of_nat n * 4 + 0x1E8)) 2")
   apply clarsimp
   prefer 2
   apply (clarsimp simp: valid_ipc_buffer_ptr'_def)
   apply (erule aligned_add_aligned, simp_all add: word_bits_def)
    apply (rule_tac n=2 in aligned_add_aligned, simp_all add: word_bits_def)
     apply (rule is_aligned_mult_triv2 [where n = 2, simplified])
    apply (simp add: is_aligned_def)
  apply (auto simp: pointerInUserData_c_guard pointerInUserData_h_t_valid)
done

lemma option_to_0_Some:
  "option_to_0 (Some x) = x"
  by (simp add: option_to_0_def)

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
  and cthrows: "\<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> PT' c {}, UNIV" -- "c always throws"
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
  and cthrows: "\<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> PT' c {}, UNIV" -- "c always throws"
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

(* FIXME : move *)
lemma scast_bit_test [simp]:
    "scast ((1 :: 'a::len signed word) << n) = (1 :: 'a word) << n"
  by (clarsimp simp: word_eq_iff)

(* FIXME: move *)
lemma ccorres_split_when_throwError_cond_break:
  fixes e :: 'e
  assumes abs: "\<forall>s s'. (s, s') \<in> sr \<and> Q s \<and> Q' s' \<longrightarrow> P = (s' \<in> P')"
  and     cc: "P \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf ar axf
                        R R' (catchbrk_C # hs) (throwError e) c"
  and     bd: "\<not> P \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf ar axf
                        U U' (catchbrk_C # hs) b d"
  and cthrows: "\<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> PT' c {}, UNIV" -- "c always throws"
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

lemma maskAsFull_eq_ep:
  "maskedAsFull cap cap =
          EndpointCap a b c d e \<Longrightarrow> cap = EndpointCap a b c d e"
  by (clarsimp simp:maskedAsFull_def isCap_simps split:if_splits)

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
  by (auto simp:maskedAsFull_def isCap_simps badge_derived'_def)

lemma maskedAsFull_again:
  "maskedAsFull (maskedAsFull aa aa) r = maskedAsFull aa aa"
  apply (case_tac aa)
  apply (simp_all add:maskedAsFull_def isCap_simps)+
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

lemma t2n_mask_eq_if:
  "(2 ^ n && mask m) = (if n < m then 2 ^ n else 0)"
  by (rule word_eqI, auto simp add: word_size nth_w2p)

lemma transferCapsLoop_ccorres:
  assumes conds:
    "rcv_buffer \<noteq> 0"
    "ep \<noteq> Some 0"
  defines "check1 \<equiv>
    Guard ShiftError \<lbrace>0 <=s seL4_MsgExtraCapBits\<rbrace>
     (Guard ShiftError \<lbrace>seL4_MsgExtraCapBits <s 0x20\<rbrace>
       (\<acute>ret__int :==
          (if \<acute>i < 2 ^ unat seL4_MsgExtraCapBits - 1 then 1
           else 0)))"
      and "check2 \<equiv> \<lambda>caps.
    IF \<acute>ret__int \<noteq> 0 THEN
      Guard ArrayBounds \<lbrace>\<acute>i < 3\<rbrace> (\<acute>ret__int :==
        (if index (excaprefs_C caps) (unat \<acute>i) \<noteq> cte_Ptr 0 then 1
         else 0))
    FI"
  defines "W \<equiv> \<lambda>ep diminish caps.
           check1;; check2 caps;;
           (While \<lbrace>\<acute>ret__int \<noteq> 0\<rbrace>
             (Guard ArrayBounds \<lbrace>\<acute>i < 3\<rbrace> (\<acute>slot :== index (excaprefs_C caps) (unat \<acute>i));;
              Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t \<acute>slot\<rbrace>
               (\<acute>cap :== h_val (hrs_mem \<acute>t_hrs) (cap_Ptr &(\<acute>slot\<rightarrow>[''cap_C''])));;
              \<acute>ret__unsigned_long :== CALL cap_get_capType(\<acute>cap);;
              \<acute>ret__int :== (if \<acute>ret__unsigned_long = scast cap_endpoint_cap then 1 else 0);;
              IF \<acute>ret__int \<noteq> 0 THEN
                \<acute>ret__unsigned_long :== CALL cap_endpoint_cap_get_capEPPtr(\<acute>cap);;
                \<acute>ret__int :== (if ep_Ptr \<acute>ret__unsigned_long = option_to_ptr ep then 1 else 0)
              FI;;
              IF \<acute>ret__int \<noteq> 0 THEN
                \<acute>ret__unsigned_long :== CALL cap_endpoint_cap_get_capEPBadge(\<acute>cap);;
                CALL setExtraBadge(Ptr rcv_buffer,\<acute>ret__unsigned_long,\<acute>i);;
                \<acute>ret__unsigned_long :== CALL message_info_get_msgCapsUnwrapped(\<acute>info);;
                Guard ShiftError \<lbrace>unat \<acute>i < 31 \<and> 0 <=s (1 :: sword32)\<rbrace>
                 (\<acute>info :== CALL message_info_set_msgCapsUnwrapped(\<acute>info,
                  \<acute>ret__unsigned_long || scast ((1 :: sword32) << unat \<acute>i)))
              ELSE
                lvar_nondet_init dc_ret_' dc_ret_'_update;;
                IF \<acute>destSlot = cte_Ptr 0 THEN
                  break_C
                FI;;
                Cond {_. diminish \<noteq> 0}
                 (\<acute>ret__struct_cap_rights_C :== CALL cap_rights_new(scast true,scast true,scast false);;
                  \<acute>ret__struct_cap_C :== CALL maskCapRights(\<acute>ret__struct_cap_rights_C,\<acute>cap);;
                  \<acute>dc_ret :== CALL deriveCap(\<acute>slot,\<acute>ret__struct_cap_C))
                 (\<acute>dc_ret :== CALL deriveCap(\<acute>slot,\<acute>cap));;
                IF deriveCap_ret_C.status_C \<acute>dc_ret \<noteq> scast EXCEPTION_NONE THEN
                  break_C
                FI;;
                \<acute>ret__unsigned_long :== CALL cap_get_capType(deriveCap_ret_C.cap_C \<acute>dc_ret);;
                IF \<acute>ret__unsigned_long = scast cap_null_cap THEN
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
  defines "stable \<equiv> \<lambda>scap excap. excap \<noteq> scap \<longrightarrow> excap = maskedAsFull scap scap"
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
             \<and> cte_wp_at' (\<lambda>cte. fst x \<noteq> NullCap  \<longrightarrow> stable (fst x) (cteCap cte)) (snd x) s)) and
           (\<lambda>s. \<forall> sl \<in> (set slots). cte_wp_at' (isNullCap o cteCap) sl s) and
           (\<lambda>_. n + length caps \<le> 3 \<and> distinct slots ))
           (precond n mi slots)
           [catchbrk_C]
           (transferCapsToSlots ep (to_bool diminish) rcv_buffer n caps slots mi)
           (W ep diminish caps')"
unfolding W_def check1_def check2_def split_def
proof (rule ccorres_gen_asm, induct caps arbitrary: n slots mi)
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
    apply (subst (asm) interpret_excaps_test_null)
      apply (simp add: unat_of_nat)
     apply (simp add: unat_of_nat)
     apply (erule le_neq_trans, clarsimp)
    apply (simp add: unat_of_nat)
    done
next
  case (Cons x xs')
  let ?S="\<lbrace>\<acute>i=of_nat n \<and> mi=message_info_to_H \<acute>info\<rbrace>"
  have n3: "n \<le> 3" using Cons.prems by simp
  hence of_nat_n3[intro!]: "of_nat n \<le> (3 :: word32)"
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
    "\<And>scap excap. stable scap excap
    \<Longrightarrow> (badge_derived' scap excap \<and>
                 capASID scap = capASID excap \<and>
                 cap_asid_base' scap = cap_asid_base' excap \<and> cap_vptr' scap = cap_vptr' excap)"
    apply (clarsimp simp:stable_def)
    apply (case_tac "excap = scap",simp+)
    apply (simp add:maskedAsFull_misc)
    done

  have stable_eq:
    "\<And>scap excap. \<lbrakk>stable scap excap; isEndpointCap excap\<rbrakk> \<Longrightarrow> scap = excap"
     by (simp add:isCap_simps stable_def maskedAsFull_def split:if_splits)
 
  have is_the_ep_stable:
    "\<And>a b. \<lbrakk>a \<noteq> NullCap \<longrightarrow> stable a b; \<not> is_the_ep b \<rbrakk> \<Longrightarrow> \<not> is_the_ep a"
    apply (clarsimp simp:stable_def maskedAsFull_def is_the_ep_def isCap_simps split:if_splits)
    apply auto
    done

  have is_the_ep_maskCapRights:
    "\<And>rights cap. is_the_ep (maskCapRights rights cap) = is_the_ep cap"
    apply (case_tac "isEndpointCap cap")
      apply (simp_all add:is_the_ep_def maskCapRights_def)
     apply (clarsimp simp:isCap_simps)
    apply (case_tac cap)
     apply (simp_all add:isCap_simps)
    apply (case_tac arch_capability)
     apply (clarsimp simp:ArchRetype_H.maskCapRights_def)+
    done

  have is_the_ep_deriveCap:
  "\<And>slot cap. \<lbrace>\<lambda>s. \<not> (is_the_ep cap)\<rbrace> deriveCap slot cap \<lbrace>\<lambda>rv s. \<not> (is_the_ep rv)\<rbrace>, -"
    apply (case_tac cap)
     apply (simp_all add:deriveCap_def Let_def isCap_simps is_the_ep_def)
      apply (wp,clarsimp)+
      defer
     apply (wp,clarsimp)+
    apply (case_tac arch_capability)
     apply (simp_all add:ArchRetype_H.deriveCap_def Let_def isCap_simps is_the_ep_def)
    apply (wp |clarsimp|rule conjI)+
    done

  have mask_right_eq_null:
    "\<And>r cap. (maskCapRights r cap = NullCap) = (cap = NullCap)"
    apply (case_tac cap)
     apply (simp_all add:maskCapRights_def isCap_simps)
    apply (case_tac arch_capability)
     apply (simp add:ArchRetype_H.maskCapRights_def)+
    done
  note split_if[split del]
  note if_cong[cong]
  from Cons.prems
  show ?case
    apply (clarsimp simp: Let_def word_sle_def[where b=5]
                          split_def
               split del: split_if cong: call_ignore_cong
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

            -- "case where a badge is sent"
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
            apply (simp split del: split_if)
            apply (vcg exspec=setExtraBadge_modifies)

           -- "case where a cap is sent (or rather a send is attempted)"
           apply (simp add: split_def del: Collect_const
                      cong: call_ignore_cong split del: split_if)
           apply (rule ccorres_rhs_assoc)+
           apply csymbr
           apply wpc
            apply (rule ccorres_cond_true_seq)
            apply (simp add: returnOk_liftE split del: split_if)
            apply (rule ccorres_case_sum_liftE)
            apply (rule ccorres_split_throws) 
             apply (rule_tac P=\<top> and P'="?S" in ccorres_break_return)
              apply clarsimp
             apply simp
            apply vcg
           apply (rule ccorres_cond_false_seq)
           apply (simp split del: split_if)
           apply (rule ccorres_Cond_rhs_Seq[unfolded Collect_const])
            -- " case diminish "
            apply (rule ccorres_rhs_assoc)+
            apply csymbr
            apply (rule ccorres_return_bind_add [where f="RetypeDecls_H.maskCapRights (capAllowWrite_update \<bottom> allRights)"])
            apply ctac
              apply (rule_tac P = "rv = maskCapRights (capAllowWrite_update (\<lambda>_. False) allRights) (fst x)"
                in ccorres_gen_asm)
              apply (rule ccorres_split_nothrowE)
                   apply (rule unifyFailure_ccorres)
                   apply (ctac add: deriveCap_ccorres')
                  apply ceqv
                 apply (simp split del: split_if)
                 apply csymbr
                 apply (rule_tac Q=\<top> and Q'=\<top> in ccorres_split_when_throwError_cond_break)
                    apply (clarsimp simp: cap_get_tag_isCap Collect_const_mem)
                   apply (rule_tac P=\<top> and P'="?S" in ccorres_break)
                    apply clarsimp
                   apply simp
                  apply (simp add: liftE_bindE split del: split_if)
                  apply (ctac add: cteInsert_ccorres)
                    apply (rule ccorres_case_sum_liftE)
                    apply csymbr
                    apply (rule ccorres_symb_exec_r)
                      apply (simp add: Collect_const[symmetric] del: Collect_const)
                      apply (rule ccorres_rhs_assoc2)
                      apply (rule_tac P="ccorresG rf_sr \<Gamma> ?r ?xf ?Pre ?Pre' ?hs ?a" in rsubst)
                       apply (rule Cons.hyps)
                        apply (clarsimp simp: excaps_map_def dest!: drop_n_foo)
                       apply clarsimp
                      apply simp
                     apply vcg
                    apply (rule conseqPre, vcg)
                    apply clarsimp
                    apply (rule_tac P="length slots = 1" in hoare_gen_asm)
                   apply (simp)
                   apply (wp cteInsert_valid_pspace hoare_valid_ipc_buffer_ptr_typ_at'
                             hoare_vcg_const_Ball_lift  cteInsert_cte_wp_at)
                     apply (clarsimp)
                  apply (vcg exspec=cteInsert_modifies)
                 apply vcg
                apply (simp split del: split_if)
                apply (rule ccorres_split_throws) 
                 apply (rule_tac P=\<top> and P'="?S" in ccorres_break)
                  apply clarsimp
                 apply simp
                apply vcg
               apply wp
               apply (simp add: to_bool_def cong: conj_cong)
               apply (rule_tac Q' ="\<lambda>rcap s. s \<turnstile>' rcap
                 \<and> (rcap\<noteq> NullCap \<longrightarrow> cte_wp_at' (is_derived' (ctes_of s) (snd x) rcap \<circ> cteCap) (snd x) s)
                 \<and> valid_pspace' s \<and> valid_ipc_buffer_ptr' rcv_buffer s \<and> length slots = 1
                 \<and> \<not> is_the_ep rcap
                 \<and> (\<forall>x\<in>set slots. cte_wp_at' (isNullCap \<circ> cteCap) x s)
                 \<and> (\<forall>x\<in>set xs'. s \<turnstile>' fst x 
                    \<and> cte_wp_at' (\<lambda>c. is_the_ep (cteCap c) \<longrightarrow> fst x = cteCap c) (snd x) s
                    \<and> cte_wp_at' (\<lambda>c. fst x \<noteq> NullCap \<longrightarrow> stable (fst x) (cteCap c)) (snd x) s)"
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
                   apply (clarsimp simp:is_the_ep_def isCap_simps stable_def)
                  apply (drule(1) bspec)+
                  apply (rule conjI | clarsimp)+
                   apply (clarsimp simp:is_the_ep_def stable_def split:if_splits)+
                 apply (case_tac "a = cteCap cteb",clarsimp)
                  apply (simp add:maskedAsFull_def split:if_splits)
                 apply (simp add:maskedAsFull_again)
               apply (wp deriveCap_derived is_the_ep_deriveCap)
              apply (simp split del: split_if)
              apply (vcg exspec=deriveCap_modifies)
             apply wp
            apply (simp split del: split_if)
            apply (vcg exspec= maskCapRights_modifies)
           -- "case not diminish"
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
               apply (simp(no_asm) add: liftE_bindE split del: split_if)
               apply (ctac add: cteInsert_ccorres)
                 apply (rule ccorres_case_sum_liftE)
                 apply csymbr
                 apply (rule ccorres_symb_exec_r)
                   apply (rule ccorres_rhs_assoc2)
                   apply (rule_tac P="ccorresG rf_sr \<Gamma> ?r ?xf ?Pre ?Pre' ?hs ?a" in rsubst)
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
             apply (simp split del: split_if)
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
                    \<and> cte_wp_at' (\<lambda>c. fst x \<noteq> NullCap \<longrightarrow> stable (fst x) (cteCap c)) (snd x) s)"
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
                   apply (clarsimp simp:is_the_ep_def isCap_simps stable_def)
                  apply (drule(1) bspec)+
                  apply (rule conjI | clarsimp)+
                   apply (clarsimp simp:is_the_ep_def stable_def split:if_splits)+
                 apply (case_tac "a = cteCap cteb",clarsimp)
                  apply (simp add:maskedAsFull_def split:if_splits)
                 apply (simp add:maskedAsFull_again)
               apply (wp deriveCap_derived is_the_ep_deriveCap)
            apply (vcg exspec=deriveCap_modifies)

          --"remaining non ccorres subgoals"
           apply (clarsimp simp: Collect_const_mem if_1_0_0
                     split del: split_if)
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
             apply (clarsimp simp: ccap_relation_def option_map_Some_eq2)
             apply (simp add: message_info_to_H_def word_ao_dist)
             apply (fold shiftl_1)[1]
             apply (subst and_mask_eq_iff_shiftr_0[THEN iffD2],
                  subst shiftl_shiftr2, simp, simp)
             apply (simp add: message_info_lift_def word_bw_assocs
                              word_sle_def t2n_mask_eq_if)
             apply (simp add: mask_def)
            apply (rule conjI)
             apply (clarsimp simp: ccap_rights_relation_def cap_rights_to_H_def
                                 false_def true_def to_bool_def allRights_def
                                 excaps_map_def split_def
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
             apply (clarsimp simp: ccap_relation_def option_map_Some_eq2 split:option.splits)
             apply (clarsimp simp: cap_endpoint_cap_lift_def option_to_ptr_def
                                option_to_0_def cap_to_H_def Let_def split:cap_CL.splits split:if_splits)
            apply clarsimp
           apply (simp only:badge_derived_mask capASID_mask cap_asid_base_mask' 
             cap_vptr_mask' maskCap_valid mask_right_eq_null)
           apply (simp only:is_the_ep_fold relative_fold)
           apply (clarsimp simp:Collect_const_mem if_1_0_0
             split del:split_if)
           apply (rule conseqPre, vcg, clarsimp simp: Collect_const_mem)
          apply (clarsimp simp: if_1_0_0 Collect_const_mem
                              trans[OF eq_commute from_bool_eq_if]
                              from_bool_0
                   split del: split_if simp del: Collect_const)
          apply vcg
         apply (simp only:is_the_ep_fold)
         apply (clarsimp simp:Collect_const_mem if_1_0_0
            split del:split_if)
         apply (rule conseqPre, vcg)
         apply (clarsimp split del: split_if)
        apply (clarsimp split del: split_if
                       simp add: Collect_const[symmetric] precond_def true_def false_def
                       simp del: Collect_const)
        apply (rule HoarePartial.Seq[rotated] HoarePartial.Cond[OF order_refl]
                  HoarePartial.Basic[OF order_refl] HoarePartial.Skip[OF order_refl]
                  HoarePartial.Guard[OF order_refl])+
       apply (simp only:is_the_ep_fold)
       apply (clarsimp simp:Collect_const_mem if_1_0_0
            split del:split_if)
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
         apply (clarsimp simp:ep_cap_not_null stable_def)
        apply (clarsimp dest!:ccap_relation_lift stable_eq simp: cap_get_tag_isCap)
       apply (clarsimp simp:valid_cap_simps' isCap_simps)
       apply (subgoal_tac "slots \<noteq> []")
        apply simp
       apply clarsimp
       apply (elim disjE)
        apply (clarsimp simp:ep_cap_not_null stable_def)
        apply (clarsimp dest!:ccap_relation_lift stable_eq simp: cap_get_tag_isCap)
       apply (clarsimp dest!:ccap_relation_lift simp:cap_get_tag_isCap is_the_ep_def)
      apply (clarsimp simp:valid_cap_simps' isCap_simps)
     apply (intro exI conjI,assumption)
    apply (clarsimp simp: ccap_relation_def option_map_Some_eq2
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
             | wp_once hoare_drop_imps
             | (rule hoare_strengthen_post [OF hoare_TrueI], rule allI, rule impI, rule TrueI))+
  done

lemma transferCaps_ccorres [corres]: 
  notes if_cong[cong]
  shows
  "ccorres (\<lambda>r r'. r = message_info_to_H r') ret__struct_message_info_C_'
    (valid_pspace' and tcb_at' receiver
     and (case_option \<top> valid_ipc_buffer_ptr') receiveBuffer
     and (excaps_in_mem caps \<circ> ctes_of)
     and K (length caps \<le> 3)
     and K (ep \<noteq> Some 0)
     and K (receiveBuffer \<noteq> Some 0)
     and K (unat (msgExtraCaps mi) \<le> 3))
    (UNIV \<inter> \<lbrace>interpret_excaps (\<acute>caps) = excaps_map caps\<rbrace>
          \<inter> \<lbrace>\<acute>receiver = tcb_ptr_to_ctcb_ptr receiver\<rbrace>
          \<inter> \<lbrace> mi = message_info_to_H \<acute>info\<rbrace>
          \<inter> \<lbrace>\<acute>receiveBuffer = Ptr (option_to_0 receiveBuffer)\<rbrace>
          \<inter> \<lbrace>\<acute>endpoint = option_to_ptr ep\<rbrace>
          \<inter> \<lbrace>to_bool \<acute>diminish = diminish\<rbrace>) []
    (transferCaps mi caps ep receiver receiveBuffer diminish)
    (Call transferCaps_'proc)" (is "ccorres _ _ ?P _ _ _ _")
  apply (unfold K_def, intro ccorres_gen_asm)
  apply (cinit lift: caps_' receiver_' info_' receiveBuffer_' endpoint_' diminish_'
    simp: getThreadCSpaceRoot_def locateSlot_def whileAnno_def)
   apply csymbr+
   apply (rule_tac P="?P" and P'="{s. info_' s = info}" in ccorres_inst)
   apply (cases "receiveBuffer = None")
    apply (clarsimp simp: option_to_0_def getReceiveSlots_def
                simp del: Collect_const
               split del: split_if)
    apply (rule ccorres_guard_imp2)
     apply (rule ccorres_move_const_guards)+
     apply (simp (no_asm) split del: split_if)
     apply (rule_tac R'=UNIV in ccorres_split_throws [OF ccorres_return_C], simp_all)[1]
     apply vcg
     apply simp
    apply (simp add: message_info_to_H_def word_sless_def word_sle_def)
   apply (cases "caps = []")
    apply (clarsimp simp: interpret_excaps_test_null excaps_map_def
                simp del: Collect_const not_None_eq
               split del: split_if)
    apply (erule notE, rule ccorres_guard_imp2)
     apply (rule ccorres_move_const_guards)+
     apply (simp (no_asm) split del: split_if)
     apply (rule ccorres_symb_exec_l)
        apply (rule_tac R'=UNIV in ccorres_split_throws [OF ccorres_return_C], simp_all)[1]
        apply vcg
        apply simp
       apply (wp empty_fail_getReceiveSlots)[3]
    apply (simp add: message_info_to_H_def word_sless_def word_sle_def)
   apply (simp add: option_to_0_def ccorres_cond_iffs
                    interpret_excaps_test_null excaps_map_def
               del: Collect_const
               cong: call_ignore_cong split del: split_if)
   apply (elim exE)
   apply (clarsimp simp: Collect_const[symmetric] Collect_False
                         signed_shift_guard_simpler_32
               simp del: Collect_const
                   cong: call_ignore_cong split del: split_if)
   apply (rule ccorres_guard_imp2)
    apply (rule ccorres_move_const_guards)+
    apply (simp (no_asm) only: ccorres_seq_cond_empty ccorres_seq_skip)
    apply (ctac add: getReceiveSlots_ccorres)
      apply (elim conjE)
      apply (rule ccorres_symb_exec_r)
        apply (rule ccorres_add_return2)
        apply (rule ccorres_split_nothrow_novcg)
            apply (rule ccorres_Catch)
            apply (rule_tac caps=caps and caps'=capsa in transferCapsLoop_ccorres, simp+)
            apply (simp add: excaps_map_def)
           apply ceqv
          apply csymbr
          apply (rule ccorres_abstract_cleanup)
          apply (rule ccorres_return_C, simp+)[1]
         apply wp
        apply (simp add: guard_is_UNIV_def)
        apply (clarsimp simp: message_info_to_H_def)
        apply (erule notE, (rule sym)?, rule less_mask_eq)
        apply (simp add: minus_one_helper5)
       apply (subgoal_tac "rv \<noteq> [0]")
        apply simp
        apply vcg
       apply clarsimp
      apply (rule conseqPre, vcg, clarsimp)
     apply (simp add: o_def pred_conj_def)
     apply (strengthen cte_wp_at_imp_consequent')
     apply wp
    apply (simp only: mem_simps simp_thms split: split_if)
    apply (vcg exspec=getReceiveSlots_modifies)
   apply (clarsimp simp: message_info_to_H_def excaps_in_mem_def
                         slotcap_in_mem_def split_def cte_wp_at_ctes_of
                         word_sless_def word_sle_def)
   apply fastforce
  apply clarsimp
  done

(* FIXME: move *)
lemma getMessageInfo_le3:
  "\<lbrace>\<top>\<rbrace> getMessageInfo sender \<lbrace>\<lambda>rv s. unat (msgExtraCaps rv) \<le> 3\<rbrace>"
  apply (simp add: getMessageInfo_def)
  apply wp
  apply (rule_tac Q="\<lambda>_. \<top>" in hoare_strengthen_post)
   apply wp
  apply (simp add: messageInfoFromWord_def Let_def msgExtraCapBits_def)
  apply (cut_tac y="r >> Types_H.msgLengthBits" in word_and_le1 [where a=3])
  apply (simp add: word_le_nat_alt)
  done  

lemma getMessageInfo_msgLength:
  "\<lbrace>\<top>\<rbrace> getMessageInfo sender \<lbrace>\<lambda>rv. K (unat (msgLength rv) \<le> msgMaxLength)\<rbrace>"
  apply (simp add: getMessageInfo_def)
  apply wp
  apply (rule_tac Q="\<lambda>_. \<top>" in hoare_strengthen_post)
   apply wp
  apply (simp add: messageInfoFromWord_def Let_def not_less msgMaxLength_def msgLengthBits_def )
  apply (cut_tac y="r" in word_and_le1 [where a="0x7F"])
  apply (simp add: word_le_nat_alt)
  done  

definition
  mi_from_H :: "Types_H.message_info \<Rightarrow> message_info_CL"
where
 "mi_from_H mi \<equiv>
     \<lparr> msgLabel_CL = msgLabel mi,
       msgCapsUnwrapped_CL = msgCapsUnwrapped mi,
       msgExtraCaps_CL = msgExtraCaps mi,
       msgLength_CL = msgLength mi \<rparr>"

lemma ccorres_add_returnOk2:
  "ccorres_underlying rf_sr G r xf arrel axf P P' hs (a >>=E returnOk) c
    \<Longrightarrow> ccorres_underlying rf_sr G r xf arrel axf P P' hs a c"
  by (simp add: bindE_returnOk)

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
 "cfault_rel2 \<equiv> \<lambda>ft exnvar err. exnvar = (scast EXCEPTION_FAULT :: word32) \<and> 
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
  note split_if[split del]
  show ?case using Cons.prems(2-3)
    apply simp
    apply (cases ys')
     apply simp
    apply (subst P[where m=0])
       apply simp+
    apply (rule conjI)
     apply (cut_tac m=0 in Cons.prems(4), simp+)
    apply (rule Cons.hyps)
       apply (rule_tac m="Suc m" in P, simp+)
    apply (cut_tac m="Suc m" in Cons.prems(4), simp+)
    done
qed

lemma lookupExtraCaps_ccorres:
  notes if_cong[cong] min_simps [simp del]
  shows
  "ccorres
     ((\<lambda>ft _ err.
                   cfault_rel (Some ft) (errfault err) (errlookup_fault err))
          \<currency> (\<lambda>xs ys. interpret_excaps ys = excaps_map xs))
      (liftxf errstate fst snd
           (\<lambda>s. (ret__unsigned_long_' s, current_extra_caps_' (globals s))))
      (valid_pspace' and tcb_at' thread and (\<lambda>s. buffer \<noteq> Some 0)
             and (\<lambda>s. unat (msgExtraCaps info) <= 3))
      (UNIV \<inter> {s. thread_' s = tcb_ptr_to_ctcb_ptr thread}
            \<inter> {s. bufferPtr_' s = option_to_ptr buffer}
            \<inter> {s. message_info_lift (info_' s) = mi_from_H info
                  }) []
      (lookupExtraCaps thread buffer info) (Call lookupExtraCaps_'proc)"
proof -
  let ?curr = "\<lambda>s. current_extra_caps_' (globals s)"
  let ?EXCNONE = "{s. ret__unsigned_long_' s = scast EXCEPTION_NONE}"
  let ?interpret = "\<lambda>v n. take n (array_to_list (excaprefs_C v))"
  note split_if[split del]
  show ?thesis
  apply (rule ccorres_gen_asm)+
  apply (cinit(no_subst_asm) lift: thread_' bufferPtr_' info_' simp: whileAnno_def)
   apply (clarsimp simp add: getExtraCPtrs_def lookupCapAndSlot_def
                             capFault_bindE
                   simp del: Collect_const)
   apply (simp add: liftE_bindE del: Collect_const)
   apply wpc
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
     apply (simp add: option_to_ptr_def option_to_0_def Collect_False
                      ccorres_cond_iffs
                 del: Collect_const)
     apply csymbr
     apply (rename_tac "lngth")
     apply (simp add: mi_from_H_def mapME_def del: Collect_const cong: bind_apply_cong)
     apply (rule ccorres_symb_exec_l)
        apply (rule_tac P="length rv = unat word2" in ccorres_gen_asm)
        apply (rule ccorres_rhs_assoc2)
        apply (rule ccorres_add_returnOk2,
               rule ccorres_splitE_novcg)
             apply (rule_tac xf'="?curr"
                       and  r'="\<lambda>xs v. excaps_map xs = ?interpret v (length xs)"
                       and   Q="UNIV"
                       and   F="\<lambda>n s. valid_pspace' s \<and> tcb_at' thread s \<and>
                                       (\<forall>m < length rv. user_word_at (rv ! m)
                                                     (x2 + (of_nat m + (msgMaxLength + 2)) * 4) s)"
                          in ccorres_sequenceE_while)
                  apply (simp add: split_def)
                  apply (rule ccorres_rhs_assoc)+
                  apply (rule ccorres_guard_imp2)
                   apply (rule ccorres_symb_exec_r)
                     apply (rule_tac xf'=cptr_' in ccorres_abstract, ceqv)
                     apply (ctac add: capFaultOnFailure_ccorres
                               [OF lookupSlotForThread_ccorres'])
                        apply (rule_tac P="is_aligned rva 4" in ccorres_gen_asm)
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
                                            unat_of_nat32[unfolded word_bits_conv]
                                            word_of_nat_less)
                          apply (simp add: word_less_nat_alt)
                         apply wp
                       apply (clarsimp simp: ccorres_cond_iffs)
                       apply (rule_tac  P= \<top>
                                and P'="{x. errstate x= lu_ret___struct_lookupSlot_raw_ret_C \<and>
                                            rv' = (rv ! length ys)}"
                                  in ccorres_from_vcg_throws)
                       apply (rule allI, rule conseqPre, vcg)
                       apply (clarsimp simp: throwError_def return_def)
                       apply (frule lookup_failure_rel_fault_lift, assumption)
                       apply (clarsimp simp: cfault_rel2_def)
                       apply (clarsimp simp: cfault_rel_def)
                       apply (simp add: fault_cap_fault_lift)
                       apply (clarsimp simp: is_cap_fault_def to_bool_def false_def)
                      apply wp
                      apply (rule hoare_post_imp_R, rule lsft_real_cte)
                      apply (clarsimp simp: obj_at'_def projectKOs objBits_simps)
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
                   and P="\<lambda>s. length rva = length rv
                               \<and> (\<forall>x \<in> set rva. snd x \<noteq> 0)"
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
            apply (simp add: word_less_nat_alt min.absorb2)
           apply (clarsimp simp: array_to_list_def)
           apply (rule takeWhile_eq, simp_all)[1]
            apply (drule_tac f="\<lambda>xs. xs ! m" in arg_cong)
            apply (clarsimp simp: split_def NULL_ptr_val[symmetric])
           apply (simp add: min.absorb1 word_less_nat_alt)
          apply simp
         apply (simp add: mapME_def[symmetric] split_def
                          liftE_bindE[symmetric])
         apply (wp mapME_length mapME_set | simp)+
           apply (rule_tac Q'="\<lambda>rv. no_0_obj' and real_cte_at' rv"
                      in hoare_post_imp_R, wp lsft_real_cte)
           apply (clarsimp simp: cte_wp_at_ctes_of)
          apply (wp | simp)+
         apply (rule hoare_pre, (wp | simp)+)
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
             split: split_if_asm)
   apply (simp add: word_size upto_enum_word field_simps
               del: upt.simps)
   apply unat_arith
  apply (clarsimp simp: excaps_map_def option_to_ptr_def option_to_0_def) 
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
      apply (wp getSlotCap_slotcap_in_mem | simp)+
    apply (rule hoare_pre, wp, simp)
   apply (simp add:hoare_TrueI)+
  done

lemma doNormalTransfer_ccorres [corres]:
  "ccorres dc xfdc
    (valid_pspace' and cur_tcb' and tcb_at' sender
        and tcb_at' receiver
        and K (sendBuffer \<noteq> Some 0) and K (receiveBuffer \<noteq> Some 0)
        and K (endpoint \<noteq> Some 0)
        and (case_option \<top> valid_ipc_buffer_ptr' sendBuffer)
        and (case_option \<top> valid_ipc_buffer_ptr' receiveBuffer))
    (UNIV \<inter> \<lbrace>\<acute>sender = tcb_ptr_to_ctcb_ptr sender\<rbrace>
          \<inter> \<lbrace>\<acute>receiver = tcb_ptr_to_ctcb_ptr receiver\<rbrace>
          \<inter> \<lbrace>\<acute>sendBuffer = Ptr (option_to_0 sendBuffer)\<rbrace>
          \<inter> \<lbrace>\<acute>receiveBuffer = Ptr (option_to_0 receiveBuffer)\<rbrace>
          \<inter> \<lbrace>canGrant = to_bool \<acute>canGrant\<rbrace>
          \<inter> \<lbrace>\<acute>badge = badge\<rbrace>
          \<inter> \<lbrace>\<acute>endpoint = option_to_ptr endpoint\<rbrace>
          \<inter> \<lbrace>to_bool \<acute>diminish = diminish\<rbrace>)  []
    (doNormalTransfer sender sendBuffer endpoint badge canGrant
                      receiver receiveBuffer diminish)
    (Call doNormalTransfer_'proc)"
proof -
  note split_if[split del]
  have word_0_le_helper:
    "\<And>i :: sword32. \<lbrakk> i <s (1 << unat (scast seL4_MsgExtraCapBits :: word32)) - 1; 0 <=s i \<rbrakk>
           \<Longrightarrow> 0 <=s i + 1"
    apply (simp add: seL4_MsgExtraCapBits_def word_sle_msb_le
                                 word_sless_msb_less msb_nth)
    apply (clarsimp simp: word_eq_iff)
    apply (drule bang_is_le)
    apply unat_arith
    done

  show ?thesis
    apply (cinit lift: sender_' receiver_' sendBuffer_' receiveBuffer_'
                       canGrant_' badge_' endpoint_' diminish_'
                 cong: call_ignore_cong)
     apply (clarsimp cong: call_ignore_cong simp del: dc_simp)
     apply (ctac(c_lines 2, no_vcg) add: getMessageInfo_ccorres')
       apply (rule_tac xf'=caps_' and r'="\<lambda>c c'. interpret_excaps c' = excaps_map c"
                  in ccorres_split_nothrow_novcg)
           apply (rule ccorres_if_lhs)
            apply (simp add: catch_def to_bool_def ccorres_cond_iffs)
            apply (rule ccorres_rhs_assoc)+
            apply (rule_tac xf'="\<lambda>s. (status_' s,
                                current_extra_caps_' (globals s))"
                             and ef'=fst and vf'=snd and es=errstate
                        in ccorres_split_nothrow_case_sum)
                 apply (rule ccorres_call, rule lookupExtraCaps_ccorres, simp+)
                apply (rule ceqv_tuple2, ceqv, ceqv)
               apply (simp add: ccorres_cond_iffs)
               apply (rule ccorres_from_vcg[where P=\<top> and P'=UNIV])
               apply (rule allI, rule conseqPre, vcg)
               apply (clarsimp simp: return_def)
              apply (simp add: ccorres_cond_iffs)
              apply (rule ccorres_from_vcg[where P=\<top> and P'=UNIV])
              apply (rule allI, rule conseqPre, vcg)
              apply (clarsimp simp: return_def excaps_map_def interpret_excaps_empty
                                    word_sless_def word_sle_def)
             apply wp
            apply simp
            apply (vcg exspec=lookupExtraCaps_modifies)
           apply (simp add: to_bool_def ccorres_cond_iffs)
           apply (rule ccorres_from_vcg[where P=\<top> and P'=UNIV])
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp: return_def excaps_map_def interpret_excaps_empty
                                 word_sle_def word_sless_def)
          apply ceqv
         apply csymbr
         apply (ctac(no_vcg) add: copyMRs_ccorres)
          apply (ctac(no_vcg) add: transferCaps_ccorres)
           apply csymbr
           apply (ctac(c_lines 2, no_vcg) add: setMessageInfo_ccorres)             
             apply ctac
            apply wp
           apply (clarsimp simp: Kernel_C.badgeRegister_def State_H.badgeRegister_def
                              ARMMachineTypes.badgeRegister_def Kernel_C.R0_def)
          apply wp
         apply simp
         apply (wp hoare_case_option_wp getMessageInfo_le3
                   getMessageInfo_msgLength lookupExtraCaps_excaps_in_mem
                   lookupExtraCaps_length
                    | simp)+
       apply (clarsimp simp: guard_is_UNIV_def Collect_const_mem)
       apply (clarsimp simp: message_info_lift_def message_info_to_H_def mask_def
                             msgLengthBits_def word_bw_assocs)
      apply (wp getMessageInfo_le3 getMessageInfo_msgLength[unfolded K_def] static_imp_wp
                  | simp)+
     apply (simp add: Collect_const_mem)
    apply (auto simp: excaps_in_mem_def valid_ipc_buffer_ptr'_def
                      option_to_0_def option_to_ptr_def
                      message_info_lift_def mi_from_H_def message_info_to_H_def
               split: option.split)
    done
qed

lemma lookupIPCBuffer_not_Some_0:
  "\<lbrace>\<top>\<rbrace> lookupIPCBuffer r t \<lbrace>\<lambda>rv. K (rv \<noteq> Some 0)\<rbrace>"
  apply (simp add: lookupIPCBuffer_def ArchVSpace_H.lookupIPCBuffer_def)
  apply (wp hoare_post_taut | simp add: Let_def | intro conjI impI)+
  done

lemma pageBitsForSize_2 [simp]:
  "2 \<le> pageBitsForSize sz"
  by (cases sz, auto)

lemma pbfs_msg_align_bits [simp]:
  "msg_align_bits \<le> pageBitsForSize sz"
  by (cases sz, auto simp: msg_align_bits)

lemma lookupIPCBuffer_aligned:
  "\<lbrace>valid_objs'\<rbrace> lookupIPCBuffer r t \<lbrace>\<lambda>rv. K (case_option True (\<lambda>x. is_aligned x msg_align_bits) rv)\<rbrace>"
  apply (simp add: lookupIPCBuffer_def ArchVSpace_H.lookupIPCBuffer_def 
                   getThreadBufferSlot_def locateSlot_def
                   Let_def getSlotCap_def cong: if_cong)
  apply (rule hoare_pre, wp getCTE_wp' threadGet_wp)
  apply clarsimp
  apply (drule (1) ctes_of_valid)
  apply (drule (1) ko_at_valid_objs', simp add: projectKOs)
  apply (clarsimp simp: isCap_simps valid_cap'_def capAligned_def valid_obj'_def valid_tcb'_def)
  apply (auto elim: aligned_add_aligned intro: is_aligned_andI1)
  done

lemma capFVMRights_range:
  "\<And>cap. cap_get_tag cap = scast cap_frame_cap \<Longrightarrow>
   cap_frame_cap_CL.capFVMRights_CL (cap_frame_cap_lift cap) \<le> 3"
  "\<And>cap. cap_get_tag cap = scast cap_small_frame_cap \<Longrightarrow>
   cap_small_frame_cap_CL.capFVMRights_CL (cap_small_frame_cap_lift cap) \<le> 3"
  by (simp add: cap_frame_cap_lift_def cap_small_frame_cap_lift_def
                cap_lift_def cap_tag_defs word_and_le1)+

lemma isArchPageCap_def2:
  "\<And>cap. isArchPageCap cap = (isArchObjectCap cap \<and> isPageCap (capCap cap))"
  by (fastforce simp: isCap_simps)

lemma lookupIPCBuffer_ccorres [corres]:
  "ccorres (\<lambda>rv rv'. rv' = Ptr (option_to_0 rv))
     ret__ptr_to_unsigned_long_' (tcb_at' thread)
     (UNIV \<inter> \<lbrace>recv = to_bool \<acute>isReceiver\<rbrace>
           \<inter> \<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr thread\<rbrace>) hs
     (lookupIPCBuffer recv thread)
     (Call lookupIPCBuffer_'proc)"
  apply (cinit lift: isReceiver_' thread_'
               simp: ArchVSpace_H.lookupIPCBuffer_def)
   apply (rule_tac P="thread = ptr_val (tcb_ptr_to_ctcb_ptr thread) && 0xFFFFFE00"
                in ccorres_gen_asm)
   apply (rule ccorres_move_c_guard_tcb)
   apply (rule ccorres_pre_threadGet)
   apply (rule_tac val=rv
               and xf'="w_bufferPtr_'"
               and R="\<lambda>s. \<exists>t. ko_at' t thread s \<and> tcbIPCBuffer t = rv"
                in ccorres_symb_exec_r_known_rv_UNIV [where R'=UNIV])
      apply (vcg, clarsimp)
      apply (erule(1) cmap_relation_ko_atE [OF cmap_relation_tcb])
      apply (clarsimp simp: ctcb_relation_def typ_heap_simps)
     apply ceqv
    apply (clarsimp simp: word_sle_def
                  intro!: ccorres_Guard_Seq [where S=UNIV, simplified]
                simp del: Collect_const)
    apply (simp add: getThreadBufferSlot_def locateSlot_conv
                del: Collect_const)
    apply (rule ccorres_move_c_guard_cte)
    apply (ctac(no_vcg))
      apply csymbr
      apply csymbr
      apply (rule ccorres_if_lhs)
       apply (clarsimp simp add: cap_get_tag_isCap
                       simp del: Collect_const
                      split del: split_if)
       apply (rule ccorres_Cond_rhs_Seq)
        (* large frame case *)
        apply (intro ccorres_rhs_assoc)
        apply csymbr
        apply (clarsimp split del: split_if)
        apply csymbr
        apply (rule ccorres_cond_false_seq)
        apply (clarsimp simp: Let_def split del: split_if)
        apply csymbr
        apply (rule ccorres_guard_imp[where A=\<top> and A'=UNIV],
               rule ccorres_cond [where R=\<top>])
            apply (clarsimp simp: pageSize_def option_to_0_def isCap_simps
                           split: split_if_asm split del: split_if)
            apply (frule(1) cap_get_tag_isCap_unfolded_H_cap(17))
            apply (frule capFVMRights_range)
            apply (clarsimp simp: ccap_relation_def map_option_case
                           split: option.splits)
            apply (simp add: cap_frame_cap_lift
                             generic_frame_cap_get_capFVMRights_CL_def)
            apply (fastforce simp: cap_to_H_def vmrights_to_H_def to_bool_def
                                  word_le_make_less Kernel_C.VMNoAccess_def
                                  Kernel_C.VMReadWrite_def Kernel_C.VMReadOnly_def
                                  Kernel_C.VMKernelOnly_def
                            dest: word_less_cases)
           apply (intro ccorres_rhs_assoc)
           apply clarsimp
           apply csymbr+
           apply (rule ccorres_Guard)
           apply (intro ccorres_assert)
           apply (ctac add: ccorres_return_C)
          apply (ctac add: ccorres_return_C)
         apply simp
        apply (clarsimp simp: pageSize_def option_to_0_def isCap_simps
                       split: split_if_asm)
        apply (frule(1) cap_get_tag_isCap_unfolded_H_cap(17))
        apply (clarsimp simp: ccap_relation_def map_option_case
                       split: option.splits)
        apply (simp add: cap_frame_cap_lift
                         generic_frame_cap_get_capFSize_CL_def
                         generic_frame_cap_get_capFBasePtr_CL_def)
        apply (clarsimp simp: cap_to_H_def mask_def c_valid_cap_def
                              cl_valid_cap_def Kernel_C.ARMSmallPage_def
                              gen_framesize_to_H_def framesize_to_H_def
                       split: split_if bool.split vmpage_size.split_asm)
       (* small frame case *)
       apply clarsimp
       apply (rule ccorres_cond_false_seq)
       apply (clarsimp simp: Let_def split del: split_if)
       apply csymbr
       apply (rule ccorres_guard_imp[where A=\<top> and A'=UNIV],
              rule ccorres_cond [where R=\<top>])
           apply (clarsimp simp: pageSize_def option_to_0_def isCap_simps
                          split: split_if_asm split del: split_if)
           apply (frule cap_get_tag_isCap_unfolded_H_cap(16), simp)
           apply (frule capFVMRights_range)
           apply (clarsimp simp: ccap_relation_def map_option_case
                          split: option.splits)
           apply (simp add: cap_small_frame_cap_lift
                            generic_frame_cap_get_capFVMRights_CL_def)
           apply (fastforce simp: cap_to_H_def vmrights_to_H_def to_bool_def
                                 word_le_make_less Kernel_C.VMNoAccess_def
                                 Kernel_C.VMReadWrite_def Kernel_C.VMReadOnly_def
                                 Kernel_C.VMKernelOnly_def
                           dest: word_less_cases)
          apply (intro ccorres_rhs_assoc)
          apply clarsimp
          apply csymbr+
          apply (rule ccorres_Guard)
          apply (intro ccorres_assert)
          apply (ctac add: ccorres_return_C)
         apply (ctac add: ccorres_return_C)
        apply simp
       apply (clarsimp simp: pageSize_def option_to_0_def isCap_simps
                      split: split_if_asm)
       apply (frule cap_get_tag_isCap_unfolded_H_cap(16), simp)
       apply (clarsimp simp: ccap_relation_def map_option_case
                      split: option.splits)
       apply (simp add: cap_small_frame_cap_lift
                        generic_frame_cap_get_capFSize_CL_def
                        generic_frame_cap_get_capFBasePtr_CL_def)
       apply (clarsimp simp: cap_to_H_def mask_def c_valid_cap_def
                             cl_valid_cap_def Kernel_C.ARMSmallPage_def
                             gen_framesize_to_H_def framesize_to_H_def
                      split: split_if bool.split vmpage_size.split_asm)
      (* non-frame-cap case *)
      apply (rule ccorres_cond_true_seq, rule ccorres_rhs_assoc)
      apply csymbr
      apply csymbr
      apply (rule ccorres_cond_true_seq)
      apply (clarsimp)
      apply (rule ccorres_split_throws, ctac add: ccorres_return_C)
      apply vcg
     apply (wp hoare_drop_imps)
    apply (clarsimp simp: cap_get_tag_isCap option_to_0_def
                          isArchPageCap_def2)
   apply (clarsimp simp: guard_is_UNIV_def tcbIPCBufferSlot_def tcbBuffer_def
                         cte_level_bits_def size_of_def)
  apply (clarsimp simp: obj_at'_def size_of_def projectKOs tcbBuffer_def
                        objBits_simps)
  apply (auto intro: cte_wp_at_tcbI')
  done

lemma fault_to_fault_tag_nonzero:
  "fault_to_fault_tag f \<noteq> 0"
  by (case_tac f, simp_all add: fault_tag_defs)

lemma doIPCTransfer_ccorres [corres]:
  "ccorres dc xfdc
    (valid_pspace' and cur_tcb' and tcb_at' sender and tcb_at' receiver
                   and K (receiver \<noteq> sender \<and> endpoint \<noteq> Some 0))
    (UNIV \<inter> \<lbrace>\<acute>sender = tcb_ptr_to_ctcb_ptr sender\<rbrace>
          \<inter> \<lbrace>\<acute>receiver = tcb_ptr_to_ctcb_ptr receiver\<rbrace>
          \<inter> \<lbrace>canGrant = to_bool \<acute>grant\<rbrace>
          \<inter> \<lbrace>\<acute>badge = badge\<rbrace>
          \<inter> \<lbrace>\<acute>endpoint = option_to_ptr endpoint\<rbrace>
          \<inter> \<lbrace>to_bool \<acute>diminish = diminish\<rbrace>)  []
    (doIPCTransfer sender endpoint badge canGrant receiver diminish)
    (Call doIPCTransfer_'proc)"
  apply (cinit lift: sender_' receiver_' grant_' badge_' endpoint_' diminish_')
   apply (rule_tac xf'="\<lambda>s. ptr_coerce (receiveBuffer___ptr_to_void_' s)"
                in ccorres_split_nothrow_call_novcg)
         apply (rule lookupIPCBuffer_ccorres)
        apply simp_all[3]
     apply ceqv
    apply (rule ccorres_pre_threadGet)
    apply (rename_tac fault)
    apply (rule ccorres_move_c_guard_tcb)
    apply (rule_tac val="case_option (scast fault_null_fault) fault_to_fault_tag fault"
                and xf'=ret__unsigned_long_'
                and R="\<lambda>s. \<exists>t. ko_at' t sender s \<and> tcbFault t = fault"
                 in ccorres_symb_exec_r_known_rv_UNIV [where R'=UNIV])
       apply (vcg, clarsimp)
       apply (erule(1) cmap_relation_ko_atE [OF cmap_relation_tcb])
       apply (fastforce simp: ctcb_relation_def typ_heap_simps
                             cfault_rel_def fault_lift_def Let_def
                      split: split_if_asm option.split)
      apply ceqv
     apply wpc
      apply (clarsimp simp: fault_null_fault_def ccorres_cond_univ_iff)
      apply (rule_tac xf'="ptr_coerce \<circ> sendBuffer___ptr_to_void_'"
                   in ccorres_split_nothrow_call_novcg)
            apply (rule lookupIPCBuffer_ccorres)
           apply simp_all[3]
        apply ceqv
       apply (fold dc_def)[1]
       apply ctac
      apply (wp lookupIPCBuffer_not_Some_0 lookupIPCBuffer_aligned)
     apply (clarsimp simp: fault_null_fault_def ccorres_cond_iffs
                           fault_to_fault_tag_nonzero)
     apply (fold dc_def)[1]
     apply ctac
    apply (clarsimp simp: guard_is_UNIV_def false_def split: option.splits)
   apply (rule_tac Q="\<lambda>rv. valid_pspace' and cur_tcb' and tcb_at' sender
                       and tcb_at' receiver and K (rv \<noteq> Some 0)
                       and (case_option \<top> valid_ipc_buffer_ptr' rv)
                       and K (receiver \<noteq> sender \<and> endpoint \<noteq> Some 0)"
                in hoare_post_imp)
    apply (auto simp: valid_ipc_buffer_ptr'_def option_to_0_def
                   split: option.splits)[1]
   apply (wp lookupIPCBuffer_not_Some_0 lookupIPCBuffer_aligned)
  apply (auto simp: to_bool_def true_def)
  done

lemma fault_case_absorb_bind:
  "(do x \<leftarrow> f; case_fault (p x) (q x) (r x) (s x) ft od)
    = case_fault (\<lambda>a b. f >>= (\<lambda>x. p x a b)) (\<lambda>a b. f >>= (\<lambda>x. q x a b))
          (\<lambda>a b c. f >>= (\<lambda>x. r x a b c)) (\<lambda>a. f >>= (\<lambda>x. s x a)) ft"
  by (simp split: fault.split)

lemma length_exceptionMessage:
  "length State_H.exceptionMessage = unat n_exceptionMessage"
  by (simp add: State_H.exceptionMessage_def ARMMachineTypes.exceptionMessage_def n_exceptionMessage_def)

lemma handleFaultReply_ccorres [corres]:
  "ccorres (\<lambda>rv rv'. rv = to_bool rv') ret__unsigned_long_'
           (valid_pspace' and tcb_at' s and
            obj_at' (\<lambda>t. tcbFault t = Some f) r and K (r \<noteq> s))
           (UNIV  \<inter> \<lbrace>cfault_rel (Some f)
                      (fault_lift (h_val (hrs_mem \<acute>t_hrs)
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
  apply (unfold K_def, rule ccorres_gen_asm)
  apply (subst handleFaultReply', assumption)
  apply (cinit lift: sender_' receiver_' simp: whileAnno_def)
   apply (clarsimp simp del: dc_simp)
   apply (ctac(c_lines 2) add: getMessageInfo_ccorres')
     apply (rename_tac tag tag')
     apply csymbr
     apply csymbr
     apply (rule ccorres_move_c_guard_tcb)
     apply (rule ccorres_symb_exec_r)
       apply (rule_tac val="fault_to_fault_tag f"
                   and xf'=ret__unsigned_long_'
                   and R="\<lambda>s. \<exists>t. ko_at' t r s \<and> tcbFault t = Some f"
                   and R'="\<lbrace>cfault_rel (Some f) (fault_lift \<acute>fault)
                        (lookup_fault_lift (h_val (hrs_mem \<acute>t_hrs)
                           (Ptr &(tcb_ptr_to_ctcb_ptr r\<rightarrow>[''tcbLookupFailure_C'']))))\<rbrace>"
                    in ccorres_symb_exec_r_known_rv_UNIV)
          apply (rule conseqPre, vcg, clarsimp)
          apply (erule(1) cmap_relation_ko_atE [OF cmap_relation_tcb])
          apply (clarsimp simp: ctcb_relation_def typ_heap_simps
                                cfault_rel_def fault_lift_def Let_def
                         split: split_if_asm)
         apply ceqv
        apply (simp add: handleFaultReply_def fault_case_absorb_bind
                    del: Collect_const split del: split_if)
        apply wpc
           apply (rename_tac number code)
           apply (clarsimp simp: bind_assoc fault_tag_defs ccorres_cond_iffs
                      split del: split_if)
           apply (rule ccorres_rhs_assoc)+
           apply csymbr
           apply csymbr
           apply csymbr
           apply (rule ccorres_symb_exec_l)
              apply (rule ccorres_stateAssert)
              apply (rule ccorres_rhs_assoc2)
              apply (rule ccorres_split_nothrow_novcg)
                  apply (rule ccorres_zipWithM_x_while)
                      apply clarsimp
                      apply (intro ccorres_rhs_assoc)
                      apply (rule ccorres_symb_exec_r)
                        apply ctac
                          apply (rule ccorres_symb_exec_r)
                            apply ctac
                           apply vcg
                          apply (rule conseqPre, vcg)
                          apply fastforce
                         apply wp
                        apply vcg
                       apply vcg
                       apply (rule conjI, simp add: State_H.exceptionMessage_def
                                    ARMMachineTypes.exceptionMessage_def word_of_nat_less)
                       apply (thin_tac "n < unat ?n'")
                       apply (simp add: msgRegisters_ccorres n_msgRegisters_def length_msgRegisters
                                        unat_of_nat exceptionMessage_ccorres[symmetric]
                                        n_exceptionMessage_def length_exceptionMessage)
                       apply (simp add: word_less_nat_alt unat_of_nat)
                      apply (rule conseqPre, vcg)
                      apply (clarsimp simp: word_of_nat_less State_H.exceptionMessage_def
                                            ARMMachineTypes.exceptionMessage_def)
                     apply (clarsimp simp: min_def n_exceptionMessage_def
                                           State_H.exceptionMessage_def
                                           ARMMachineTypes.exceptionMessage_def
                                           msgRegisters_unfold
                                           message_info_to_H_def)
                     apply unat_arith
                    apply (vcg spec=TrueI)
                    apply clarsimp
                   apply wp
                   apply simp
                  apply (clarsimp simp: State_H.exceptionMessage_def
                                        ARMMachineTypes.exceptionMessage_def
                                        word_bits_def)
                  apply unat_arith
                 apply ceqv
                apply (rule ccorres_stateAssert)
                apply wpc
                 apply (simp only: return_bind)
                 apply (ctac add: ccorres_return_C)
                apply (rule ccorres_symb_exec_l)
                   apply (ctac add: ccorres_return_C)
                  apply (wp mapM_wp')
                apply clarsimp+
               apply (wp hoare_drop_imps)
              apply (clarsimp simp: guard_is_UNIV_def message_info_to_H_def)
             apply (wp hoare_drop_imps hoare_vcg_all_lift)
          apply (clarsimp simp: bind_assoc fault_tag_defs ccorres_cond_iffs
                     split del: split_if)
          apply (rule ccorres_symb_exec_l)
             apply (rule ccorres_stateAssert)
             apply wpc
              apply clarsimp
              apply (ctac add: ccorres_return_C)
             apply (rule ccorres_symb_exec_l)
                apply (ctac add: ccorres_return_C)
               apply (wp mapM_wp')
             apply clarsimp+
            apply (wp hoare_drop_imps hoare_vcg_all_lift)
         apply (clarsimp simp: bind_assoc fault_tag_defs ccorres_cond_iffs
                    split del: split_if)
         apply (rule ccorres_symb_exec_l)
            apply (rule ccorres_stateAssert)
            apply wpc
             apply clarsimp
             apply (ctac add: ccorres_return_C)
            apply (rule ccorres_symb_exec_l)
               apply (ctac add: ccorres_return_C)
              apply (wp mapM_wp')
            apply clarsimp+
           apply (wp hoare_drop_imps hoare_vcg_all_lift)
        apply (rename_tac number)
        apply (clarsimp simp: bind_assoc fault_tag_defs ccorres_cond_iffs
                   split del: split_if)
        apply (rule ccorres_rhs_assoc)+
        apply csymbr
        apply csymbr
        apply csymbr
        apply csymbr
        apply (ctac(no_vcg))
         apply (rename_tac sb sb')
         apply (rule ccorres_stateAssert)
         apply (rule ccorres_rhs_assoc2)
         apply (rule ccorres_split_nothrow_novcg)
             apply (rule ccorres_zipWithM_x_while)
                 apply clarsimp
                 apply (intro ccorres_rhs_assoc)
                 apply (rule ccorres_symb_exec_r)
                   apply ctac
                     apply (rule ccorres_symb_exec_r)
                       apply ctac
                      apply vcg
                     apply (rule conseqPre, vcg)
                     apply fastforce
                    apply wp
                   apply vcg
                  apply vcg 
                  apply (simp add: length_syscallMessage length_msgRegisters)
                  apply (simp add: msgRegisters_ccorres syscallMessage_ccorres [symmetric]
                                   n_msgRegisters_def unat_of_nat32 word_bits_def
                                   word_of_nat_less n_syscallMessage_def)
                 apply (rule conseqPre, vcg)
                 apply (clarsimp simp: word_of_nat_less length_msgRegisters
                                       n_msgRegisters_def)
                apply (simp add: length_msgRegisters length_syscallMessage
                                 n_msgRegisters_def n_syscallMessage_def
                                 min_def message_info_to_H_def word_of_nat_less)
                apply unat_arith
               apply (vcg spec=TrueI)
               apply clarsimp
              apply wp
              apply simp
             apply (clarsimp simp: msgRegisters_unfold word_bits_def)
             apply unat_arith
            apply ceqv
           apply (rule ccorres_stateAssert)
           apply (rule ccorres_split_nothrow_novcg)
               apply wpc
                apply (simp add: option_to_0_def ccorres_cond_iffs)
                apply (rule ccorres_return_Skip)
               apply (rule_tac P="sb \<noteq> Some 0" in ccorres_gen_asm)
               apply (rule_tac P="case_option True (\<lambda>x. is_aligned x msg_align_bits) sb"
                            in ccorres_gen_asm)
               apply (simp add: option_to_0_def ccorres_cond_iffs)
               apply (subst ccorres_seq_skip' [symmetric])
               apply (rule ccorres_split_nothrow_novcg)
                   apply (simp only: zipWithM_x_mapM_x)
                   apply (rule ccorres_mapM_x_while')
                       apply clarsimp
                       apply (rule ccorres_guard_imp)
                         apply (rule ccorres_pre_loadWordUser)
                         apply (intro ccorres_rhs_assoc)
                         apply (rule ccorres_symb_exec_r)
                           apply (rule ccorres_Guard_Seq)
                           apply (rule ccorres_symb_exec_r)
                             apply (rule ccorres_symb_exec_r)
                               apply ctac
                              apply vcg
                             apply (rule conseqPre, vcg)
                             apply fastforce
                            apply vcg
                           apply (rule conseqPre, vcg)
                           apply clarsimp
                          apply vcg
                         apply (rule conseqPre, vcg)
                         apply clarsimp
                        apply clarsimp
                        apply assumption
                       apply (clarsimp simp: n_syscallMessage_def n_msgRegisters_def
                                             msgRegisters_ccorres[symmetric]
                                             syscallMessage_ccorres[symmetric]
                                             length_msgRegisters length_syscallMessage
                                             unat_of_nat32 word_bits_def
                                             min_def message_info_to_H_def
                                             upto_enum_def typ_heap_simps'
                                             unat_add_lem[THEN iffD1]
                                      split: split_if_asm
                                   simp del: upt_rec_numeral,
                              simp_all add: word_less_nat_alt unat_add_lem[THEN iffD1] unat_of_nat)[1]
                      apply (clarsimp simp: n_syscallMessage_def n_msgRegisters_def
                                            msgRegisters_ccorres
                                            syscallMessage_ccorres
                                            length_syscallMessage length_msgRegisters
                                            message_info_to_H_def min_def)
                      apply (intro conjI impI, unat_arith+)[1]
                     apply (vcg spec=TrueI)
                     apply clarsimp
                    apply (simp add: split_def)
                    apply wp
                    apply (fastforce elim: aligned_add_aligned
                                   intro: is_aligned_mult_triv2 [where n=2,
                                                                 simplified]
                                    simp: word_bits_def msg_align_bits)
                   apply (clarsimp simp: msgRegisters_unfold word_bits_def)
                   apply (simp add: n_syscallMessage_def)
                  apply ceqv
                 apply (rule ccorres_symb_exec_l)
                    apply (fold dc_def)[1]
                    apply (rule ccorres_return_Skip)
                   apply (wp mapM_wp')
                 apply clarsimp
                apply wp
               apply (clarsimp simp: guard_is_UNIV_def)
              apply ceqv
             apply (ctac add: ccorres_return_C)
            apply wp
           apply (clarsimp simp: guard_is_UNIV_def message_info_to_H_def)
          apply clarsimp
          apply (rule_tac Q="\<lambda>rv. valid_pspace' and K (sb \<noteq> Some 0) and
                                  K (case_option True (\<lambda>x. is_aligned x msg_align_bits) sb)"
                       in hoare_post_imp)
           apply (clarsimp simp: upto_enum_word simp del: upt.simps)
           apply (erule notE, erule aligned_add_aligned)
             apply (simp add: n_msgRegisters_def n_syscallMessage_def
                         del: upt.simps upt_rec_numeral)
             apply (simp add: is_aligned_def)
            apply simp
           apply simp
          apply (simp add: zipWithM_x_mapM_x)
          apply (wp mapM_x_wp | simp add: split_def)+
          apply (rule subset_refl)
         apply (clarsimp simp: guard_is_UNIV_def)
        apply (rule_tac Q="\<lambda>rv. valid_pspace' and K (rv \<noteq> Some 0) and
                                K (case_option True (\<lambda>x. is_aligned x msg_align_bits) rv)"
                     in hoare_post_imp)
         apply clarsimp
        apply (wp lookupIPCBuffer_not_Some_0 lookupIPCBuffer_aligned)
       apply (clarsimp simp: guard_is_UNIV_def to_bool_def true_def false_def)
      apply vcg
     apply (rule conseqPre, vcg)
     apply clarsimp
    apply wp
   apply vcg
  apply (clarsimp simp: obj_at'_def n_msgRegisters_def)
  done

lemma fault_null_fault_ptr_new_ccorres [corres]:
  "ccorres dc xfdc (tcb_at' receiver) UNIV hs
           (threadSet (tcbFault_update empty) receiver)
           (CALL fault_null_fault_ptr_new(Ptr
               &(tcb_ptr_to_ctcb_ptr receiver\<rightarrow>[''tcbFault_C''])))"
  apply (rule ccorres_from_vcg)
  apply (rule allI)
  apply (rule conseqPre, vcg)
  apply clarsimp
  apply (frule(1) obj_at_cslift_tcb)
  apply (rule conjI)
   apply (clarsimp simp: typ_heap_simps)
  apply clarsimp
  apply (rule rev_bexI [OF threadSet_eq], assumption)
  apply clarsimp
  apply (erule(2) rf_sr_tcb_update_no_queue, simp_all add: tcb_cte_cases_def)
  apply (clarsimp simp: ctcb_relation_def cthread_state_relation_def
                        fault_lift_def cfault_rel_def)
  apply (case_tac "tcbState ko", simp_all add: is_cap_fault_def)
  done

(* FIXME: move *)
lemma epCancelAll_sch_act_wf:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>
  epCancelAll ep
  \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: epCancelAll_def)
  apply (rule hoare_TrueI|wp getEndpoint_wp|wpc|simp)+
  apply fastforce?
  done

(* FIXME: move *)
lemma aepCancelAll_sch_act_wf:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>
  aepCancelAll ep
  \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: aepCancelAll_def)
  apply (rule hoare_TrueI|wp getAsyncEP_wp|wpc|simp)+
  apply fastforce?
  done

(* FIXME: move *)
lemma cteDeleteOne_sch_act_wf:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>
  cteDeleteOne slot
  \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: cteDeleteOne_def unless_when split_def)
  apply (simp add: finaliseCapTrue_standin_def Let_def)
  apply (wp isFinalCapability_inv aepCancelAll_sch_act_wf 
            epCancelAll_sch_act_wf getCTE_wp' static_imp_wp
          | simp add: Let_def)+
  done

(* FIXME: move *)
lemma vp_invs_strg': "invs' s \<longrightarrow> valid_pspace' s" by auto

(* FIXME: move *)
lemma setCTE_tcbFault:
  "\<lbrace>obj_at' (\<lambda>tcb. P (tcbFault tcb)) t\<rbrace>
  setCTE slot cte 
  \<lbrace>\<lambda>rv. obj_at' (\<lambda>tcb. P (tcbFault tcb)) t\<rbrace>"
  apply (simp add: setCTE_def)
  apply (rule setObject_cte_obj_at_tcb', simp_all)
  done

(* FIXME: move *)
lemma emptySlot_tcbFault:
  "\<lbrace>obj_at' (\<lambda>tcb. P (tcbFault tcb)) t\<rbrace>
  emptySlot slot irq
  \<lbrace>\<lambda>_. obj_at' (\<lambda>tcb. P (tcbFault tcb)) t\<rbrace>" 
  apply (simp add: emptySlot_def)
  apply (wp setCTE_tcbFault getCTE_wp' hoare_drop_imps
          | wpc
          | simp add: updateMDB_def updateCap_def Let_def
          | rule conjI impI)+
  done

(* FIXME: move *)
lemma tcbSchedEnqueue_tcbFault:
  "\<lbrace>obj_at' (\<lambda>tcb. P (tcbFault tcb)) t\<rbrace>
  tcbSchedEnqueue t'
  \<lbrace>\<lambda>_. obj_at' (\<lambda>tcb. P (tcbFault tcb)) t\<rbrace>"
  apply (simp add: tcbSchedEnqueue_def unless_when)
  apply (wp threadSet_obj_at' hoare_drop_imps threadGet_wp|simp)+
  done

lemma rescheduleRequired_tcbFault:
  "\<lbrace>obj_at' (\<lambda>tcb. P (tcbFault tcb)) t\<rbrace>
     rescheduleRequired
   \<lbrace>\<lambda>_. obj_at' (\<lambda>tcb. P (tcbFault tcb)) t\<rbrace>"
  apply (simp add: rescheduleRequired_def)
  apply (wp tcbSchedEnqueue_tcbFault | wpc)+
  apply simp
  done

(* FIXME: move *)
lemma sts_tcbFault:
  "\<lbrace>obj_at' (\<lambda>tcb. P (tcbFault tcb)) t\<rbrace>
  setThreadState st t'
  \<lbrace>\<lambda>_. obj_at' (\<lambda>tcb. P (tcbFault tcb)) t\<rbrace>"
  apply (simp add: setThreadState_def)
  apply (wp threadSet_obj_at' rescheduleRequired_tcbFault | simp)+
  done

(* FIXME: move *)
lemma setEndpoint_tcb:
  "\<lbrace>obj_at' (\<lambda>tcb::tcb. P tcb) t\<rbrace>
  setEndpoint ep e
  \<lbrace>\<lambda>_. obj_at' P t\<rbrace>"
  apply (simp add: setEndpoint_def)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp: updateObject_default_def in_monad)
  done

(* FIXME: move *)
lemma setAsyncEP_tcb:
  "\<lbrace>obj_at' (\<lambda>tcb::tcb. P tcb) t\<rbrace>
  setAsyncEP aep e
  \<lbrace>\<lambda>_. obj_at' P t\<rbrace>"
  apply (simp add: setAsyncEP_def)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp: updateObject_default_def in_monad)
  done

(* FIXME: move *)
lemma epCancelAll_tcbFault:
  "\<lbrace>obj_at' (\<lambda>tcb. P (tcbFault tcb)) t\<rbrace>
  epCancelAll ep
  \<lbrace>\<lambda>_. obj_at' (\<lambda>tcb. P (tcbFault tcb)) t\<rbrace>"
  apply (simp add: epCancelAll_def)
  apply (rule order_refl |
         wp mapM_x_wp tcbSchedEnqueue_tcbFault sts_tcbFault 
            setEndpoint_tcb getEndpoint_wp rescheduleRequired_tcbFault |
         wpc | simp)+
  done

(* FIXME: move *)
lemma aepCancelAll_tcbFault:
  "\<lbrace>obj_at' (\<lambda>tcb. P (tcbFault tcb)) t\<rbrace>
  aepCancelAll ep
  \<lbrace>\<lambda>_. obj_at' (\<lambda>tcb. P (tcbFault tcb)) t\<rbrace>"
  apply (simp add: aepCancelAll_def)
  apply (rule order_refl |
         wp mapM_x_wp tcbSchedEnqueue_tcbFault sts_tcbFault 
            setAsyncEP_tcb getAsyncEP_wp rescheduleRequired_tcbFault |
         wpc | simp)+
  done

(* FIXME: move *)
lemma cteDeleteOne_tcbFault:
  "\<lbrace>obj_at' (\<lambda>tcb. P (tcbFault tcb)) t\<rbrace>
  cteDeleteOne slot
  \<lbrace>\<lambda>_. obj_at' (\<lambda>tcb. P (tcbFault tcb)) t\<rbrace>"
  apply (simp add: cteDeleteOne_def unless_when split_def)
  apply (simp add: finaliseCapTrue_standin_def Let_def)
  apply (wp emptySlot_tcbFault epCancelAll_tcbFault getCTE_wp'
            aepCancelAll_tcbFault isFinalCapability_inv static_imp_wp    
          | simp add: Let_def)+
  done

lemma doReplyTransfer_ccorres [corres]:
  "ccorres dc xfdc
    (invs' and st_tcb_at' (Not \<circ> isReply) sender and tcb_at' receiver and sch_act_simple)
    (UNIV \<inter> \<lbrace>\<acute>sender = tcb_ptr_to_ctcb_ptr sender\<rbrace>
          \<inter> \<lbrace>\<acute>receiver = tcb_ptr_to_ctcb_ptr receiver\<rbrace>
          \<inter> \<lbrace>\<acute>slot = Ptr slot\<rbrace>)  []
    (doReplyTransfer sender receiver slot)
    (Call doReplyTransfer_'proc)"
proof -
  have invs_valid_queues_strg: "\<And>s. invs' s \<longrightarrow> valid_queues s"
    by clarsimp
  show ?thesis
  apply (cinit lift: sender_' receiver_' slot_')
   apply (rule getThreadState_ccorres_foo)   
   apply (rule ccorres_assert2)
   apply (simp add: liftM_def getSlotCap_def
               del: Collect_const split del: split_if)
   apply (rule ccorres_pre_getCTE)
   apply (rule ccorres_assert2)
   apply (rule ccorres_pre_getCTE)
   apply (rule ccorres_assert2)
   apply (rule ccorres_pre_threadGet)
   apply (rename_tac fault)
   apply (rule ccorres_move_c_guard_tcb)
   apply (rule_tac val="case_option (scast fault_null_fault) fault_to_fault_tag fault"
               and xf'=ret__unsigned_long_'
               and R="\<lambda>s. \<exists>t. ko_at' t receiver s \<and> tcbFault t = fault"
                in ccorres_symb_exec_r_known_rv_UNIV [where R'=UNIV])
      apply (vcg, clarsimp)
      apply (erule(1) cmap_relation_ko_atE [OF cmap_relation_tcb])
      apply (fastforce simp: ctcb_relation_def typ_heap_simps
                            cfault_rel_def fault_lift_def Let_def
                     split: split_if_asm option.split)
     apply ceqv
    apply wpc
     apply (clarsimp simp: ccorres_cond_iffs split del: split_if)
     apply (fold dc_def)[1]
     apply (rule ccorres_rhs_assoc)+
     apply (ctac(no_vcg) add: cteDeleteOne_stronger_ccorres)
      apply (rule ccorres_split_nothrow_novcg)
          apply (rule ccorres_call [where xf'=xfdc])
             apply (rule cteDeleteOne_stronger_ccorres)
	    apply (rule refl)
           apply simp
          apply simp
         apply ceqv
        apply (ctac (no_vcg) add: setThreadState_ccorres)
         apply (rule ccorres_call)
            apply (rule attemptSwitchTo_ccorres)
           apply simp
          apply simp
         apply simp
        apply (wp sts_running_valid_queues setThreadState_st_tcb | simp)+
       apply (wp cteDeleteOne_sch_act_wf)
      apply (simp add: guard_is_UNIV_def ThreadState_Running_def mask_def)
     apply simp
     apply (strengthen invs_weak_sch_act_wf_strg
                       invs_valid_queues_strg)
     apply wp
    apply (clarsimp simp: fault_null_fault_def ccorres_cond_iffs
                          fault_to_fault_tag_nonzero
               split del: split_if)
    apply (rule ccorres_rhs_assoc)+
    apply (fold dc_def)[1]
    apply csymbr
    apply (ctac (no_vcg) add: cteDeleteOne_stronger_ccorres)
     apply (rule_tac A'=UNIV in stronger_ccorres_guard_imp)
       apply (rule ccorres_split_nothrow_novcg [OF ccorres_call,
                                                OF handleFaultReply_ccorres,
                                                unfolded bind_assoc,
                                                where xf'=restart_'])
             apply simp_all[3]
          apply ceqv
         apply (rule ccorres_move_c_guard_tcb)
         apply (rule ccorres_split_nothrow_novcg)
             apply (rule fault_null_fault_ptr_new_ccorres)
            apply ceqv
           apply (rule_tac R=\<top> in ccorres_cond2)
             apply (clarsimp simp: to_bool_def)
            apply (ctac (no_vcg))
             apply (simp only: K_bind_def)
             apply (ctac)
            apply (wp sts_running_valid_queues setThreadState_st_tcb | simp)+
           apply (fold dc_def)[1]
           apply (ctac add: setThreadState_ccorres_valid_queues')
          apply ((wp threadSet_valid_queues threadSet_sch_act threadSet_valid_queues' static_imp_wp
                     threadSet_valid_objs' threadSet_weak_sch_act_wf
                       | simp add: valid_tcb_state'_def)+)[1]
         apply (clarsimp simp: guard_is_UNIV_def ThreadState_Restart_def
                               ThreadState_Inactive_def mask_def to_bool_def)
        apply (rule_tac Q="\<lambda>rv. valid_queues and tcb_at' receiver and valid_queues' and
                              valid_objs' and sch_act_simple and 
                              (\<lambda>s. sch_act_wf (ksSchedulerAction s) s)" in hoare_post_imp)
         apply (fastforce simp: inQ_def weak_sch_act_wf_def)
        apply (wp threadSet_valid_queues threadSet_sch_act handleFaultReply_sch_act_wf) 
       apply (clarsimp simp: guard_is_UNIV_def)
      apply assumption
     apply clarsimp
     apply (drule_tac p=receiver in obj_at_ko_at')
     apply clarsimp
     apply (erule(1) cmap_relation_ko_atE [OF cmap_relation_tcb])
     apply (clarsimp simp: ctcb_relation_def typ_heap_simps)     
    apply wp 
    apply (strengthen vp_invs_strg' impI[OF invs_valid_queues'])
    apply (wp cteDeleteOne_tcbFault cteDeleteOne_sch_act_wf)     
   apply (clarsimp simp: guard_is_UNIV_def to_bool_def true_def     
                         option_to_ptr_def option_to_0_def false_def
                         ThreadState_Running_def mask_def split: option.splits)
  apply (clarsimp simp: st_tcb_at_tcb_at')
  apply (clarsimp simp: st_tcb_at'_def obj_at'_def)
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
              \<inter> \<lbrace>\<acute>receiver = tcb_ptr_to_ctcb_ptr receiver\<rbrace>) hs
        (setupCallerCap sender receiver)
        (Call setupCallerCap_'proc)"
  apply (rule ccorres_gen_asm_state, rule ccorres_gen_asm_state)
  apply (frule_tac p=sender in is_aligned_tcb_ptr_to_ctcb_ptr)
  apply (cinit lift: sender_' receiver_')
   apply (clarsimp simp: word_sle_def, fold dc_def)[1]
   apply (ctac(no_vcg))
    apply (rule ccorres_Guard_Seq)+
    apply (simp only: getThreadReplySlot_def getThreadCallerSlot_def)
    apply (ctac(no_vcg))
      apply (rename_tac replySlot replySlot')
      apply (simp del: Collect_const)
      apply (rule ccorres_getCTE_cte_at)
      apply (rule ccorres_move_c_guard_cte)
      apply (ctac(no_vcg) add:  getSlotCap_h_val_ccorres[unfolded getSlotCap_def fun_app_def,
                                                         folded liftM_def, simplified ccorres_liftM_simp])
        apply (rule ccorres_assert2)+
        apply (simp add: ccorres_seq_skip locateSlot_conv)
        apply (rule ccorres_Guard_Seq)+
        apply csymbr
        apply (rule ccorres_getSlotCap_cte_at)
        apply (rule ccorres_move_c_guard_cte)
        apply (ctac(no_vcg))
         apply (rule ccorres_assert)
         apply (simp only: ccorres_seq_skip dc_def[symmetric])
         apply csymbr
         apply (ctac add: cteInsert_ccorres)
        apply simp
        apply (wp getSlotCap_cte_wp_at)
       apply (clarsimp simp: ccap_relation_def cap_lift_reply_cap
                             cap_to_H_simps cap_reply_cap_lift_def
                             false_def tcbSlots Kernel_C.tcbCaller_def
                             size_of_def cte_level_bits_def)
        apply (simp add: is_aligned_neg_mask)
       apply (wp getCTE_wp')
      apply (simp add: tcbSlots Kernel_C.tcbCaller_def
                       size_of_def cte_level_bits_def)
     apply simp
     apply (rule_tac Q="\<lambda>rv. valid_pspace'" in hoare_post_imp)
      apply (auto simp: cte_wp_at_ctes_of isCap_simps
                        tcbSlots Kernel_C.tcbCaller_def size_of_def 
                        cte_level_bits_def)[1]
      apply (case_tac cte,clarsimp)
      apply (drule ctes_of_valid_cap')
       apply fastforce
      apply (simp add:valid_cap'_def capAligned_def)
     apply (simp add: locateSlot_conv)
     apply wp
    apply (clarsimp simp: ccap_rights_relation_def allRights_def
                          mask_def true_def cap_rights_to_H_def tcbCallerSlot_def
                          Kernel_C.tcbCaller_def)
   apply simp
   apply wp
  apply (clarsimp simp: Kernel_C.ThreadState_BlockedOnReply_def mask_def
                        valid_pspace'_def tcbReplySlot_def Kernel_C.tcbReply_def
                        valid_tcb_state'_def)
  done

lemma sendIPC_dequeue_ccorres_helper:
  "ep_ptr = Ptr ep ==>
  ccorres (\<lambda>rv rv'. rv' = tcb_ptr_to_ctcb_ptr dest) dest_'
           (invs' and st_tcb_at' (\<lambda>st. isBlockedOnReceive st \<and>
                                       blockingIPCEndpoint st = ep) dest
                  and ko_at' (RecvEP (dest#rest)) ep) UNIV hs
           (setEndpoint ep $ case rest of [] \<Rightarrow> Structures_H.IdleEP
                                        | (a#list) \<Rightarrow> Structures_H.RecvEP rest)
        (\<acute>queue :== CALL ep_ptr_get_queue(ep_ptr);;
         \<acute>dest :== head_C \<acute>queue;;
         SKIP;;
         \<acute>queue :== CALL tcbEPDequeue(\<acute>dest,\<acute>queue);;
         CALL ep_ptr_set_queue(ep_ptr,\<acute>queue);;
         IF head_C \<acute>queue = Ptr 0 THEN
             CALL endpoint_ptr_set_state(ep_ptr,scast EPState_Idle)
         FI)"
  apply (rule ccorres_from_vcg)
  apply (rule allI)
  apply (rule conseqPre, vcg)
  apply (clarsimp split del: split_if simp del: comp_def)
  apply (frule ep_blocked_in_queueD [OF st_tcb'_weakenE])
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
              cong: imp_cong split del: split_if simp del: comp_def)
  apply (intro conjI impI allI)
     apply (fastforce simp: h_t_valid_clift)
    apply (fastforce simp: h_t_valid_clift)
   -- "empty case"
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
                         cpspace_relation_def update_ep_map_tos)
        apply (elim conjE)
        apply (intro conjI)
             -- "tcb relation"
             apply (erule ctcb_relation_null_queue_ptrs)
             apply (clarsimp simp: comp_def)
            -- "ep relation"
            apply (rule cpspace_relation_ep_update_ep, assumption+)
             apply (simp add: cendpoint_relation_def Let_def EPState_Idle_def
                              tcb_queue_relation'_def)
            apply simp
           -- "aep relation"
           apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
           apply simp
           apply (rule casync_endpoint_relation_ep_queue [OF invs_sym'], assumption+)
            apply simp
           apply (erule (1) map_to_ko_atI')
          -- "queue relation"
          apply (rule cready_queues_relation_null_queue_ptrs, assumption+)
          apply (clarsimp simp: comp_def)
         apply (simp add: carch_state_relation_def)
        apply (simp add: cmachine_state_relation_def)
       apply (simp add: h_t_valid_clift_Some_iff)
      apply (simp add: objBits_simps)
     apply (simp add: objBits_simps)
    apply assumption
   apply (clarsimp simp: cendpoint_relation_def Let_def tcb_queue_relation'_def)
  -- "non-empty case"
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
                        cpspace_relation_def update_ep_map_tos)
       apply (elim conjE)
       apply (intro conjI)
             -- "tcb relation"
            apply (erule ctcb_relation_null_queue_ptrs)
            apply (clarsimp simp: comp_def)
           -- "ep relation"
           apply (rule cpspace_relation_ep_update_ep, assumption+)
            apply (clarsimp simp: cendpoint_relation_def Let_def
                                  isRecvEP_def isSendEP_def
                                  tcb_queue_relation'_def valid_ep'_def
                           split: endpoint.splits list.splits
                       split del: split_if)
            apply (subgoal_tac "tcb_at' (if x22 = [] then x21 else last x22) \<sigma>")
             apply (clarsimp simp: is_aligned_neg_mask
                            dest!: is_aligned_tcb_ptr_to_ctcb_ptr
                        split del: split_if)
            apply clarsimp
           apply simp
          -- "aep relation"
          apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
          apply simp
          apply (rule casync_endpoint_relation_ep_queue [OF invs_sym'], assumption+)
           apply simp
          apply (erule (1) map_to_ko_atI')
         -- "queue relation"
         apply (rule cready_queues_relation_null_queue_ptrs, assumption+)
         apply (clarsimp simp: comp_def)
        apply (simp add: carch_state_relation_def)
       apply (simp add: cmachine_state_relation_def)
      apply (simp add: h_t_valid_clift_Some_iff)
     apply (simp add: objBits_simps)
    apply (simp add: objBits_simps)
   apply assumption
  apply (clarsimp simp: cendpoint_relation_def Let_def tcb_queue_relation'_def)
  done

lemma sendIPC_block_ccorres_helper:
  "ccorres dc xfdc (tcb_at' thread and valid_queues and valid_objs' and 
                    sch_act_not thread and ep_at' epptr and
                    (\<lambda>s. sch_act_wf (ksSchedulerAction s) s \<and>
                         (\<forall>d p. thread \<notin> set (ksReadyQueues s (d, p)))) and
                    K (bos = ThreadState_BlockedOnSend
                      \<and> epptr' = epptr \<and> badge' = badge
                      \<and> cg = from_bool canGrant \<and> dc' = from_bool do_call) and
                    K (epptr = epptr && ~~ mask 4) and
                    K (badge = badge && mask 28))
                   UNIV hs
           (setThreadState (Structures_H.thread_state.BlockedOnSend
                                epptr badge canGrant do_call) thread)
           (Guard C_Guard
             \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t tcb_ptr_to_ctcb_ptr thread\<rbrace>
             (CALL thread_state_ptr_set_tsType(Ptr
              &(tcb_ptr_to_ctcb_ptr thread\<rightarrow>[''tcbState_C'']),
              scast bos));;
            Guard C_Guard
             \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t tcb_ptr_to_ctcb_ptr thread\<rbrace>
             (CALL thread_state_ptr_set_blockingIPCEndpoint(Ptr
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
             (CALL thread_state_ptr_set_blockingIPCIsCall(Ptr
                         &(tcb_ptr_to_ctcb_ptr thread\<rightarrow>[''tcbState_C'']), dc'));;
            CALL scheduleTCB(tcb_ptr_to_ctcb_ptr thread))"
  unfolding K_def setThreadState_def
  apply (intro ccorres_gen_asm)
  apply (rule ccorres_guard_imp)
    apply (rule ccorres_split_nothrow_novcg)
        apply (rule_tac P=\<top> and P'="tcb_at' thread"
                     in threadSet_ccorres_lemma3)
         apply vcg
        apply clarsimp
        apply (frule(1) tcb_at_h_t_valid)
        apply (frule h_t_valid_c_guard)
        apply (clarsimp simp: typ_heap_simps)
        apply (erule(1) rf_sr_tcb_update_no_queue)
               apply (simp add: typ_heap_simps')+
         apply (simp add: tcb_cte_cases_def)
        apply (simp add: ctcb_relation_def cthread_state_relation_def
                         ThreadState_BlockedOnSend_def mask_def
                         from_bool_def to_bool_def)
        apply (clarsimp split: bool.split)
       apply ceqv
      apply clarsimp
      apply ctac
     apply (wp threadSet_weak_sch_act_wf_runnable' threadSet_valid_queues
               threadSet_valid_objs')
    apply (clarsimp simp: guard_is_UNIV_def)
   apply (clarsimp simp: sch_act_wf_weak valid_tcb'_def valid_tcb_state'_def
                         tcb_cte_cases_def)
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
    by auto
  thus ?case using Cons.prems
    apply (clarsimp simp: upd_unless_null_def fg_consD1 [OF fgN]
                          fg_consD1 [OF fgP] pnu npu)
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
  by (clarsimp simp: tcb_queue_head_empty_iff tcb_queue_relation'_def)

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
                   \<and> cslift_all_but_tcb_C t s  \<and> (hrs_htd \<^bsup>t\<^esup>t_hrs) = (hrs_htd \<^bsup>s\<^esup>t_hrs)}"
  apply (intro allI)
  apply (rule conseqPre, vcg)
  apply (clarsimp split del: split_if)
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
  apply (simp add: typ_heap_simps)
  apply (intro impI conjI allI)
       apply simp
      apply simp
      apply (rule ext)
      apply (clarsimp simp add: typ_heap_simps tcb_null_ep_ptrs_def)
     apply (clarsimp simp add: typ_heap_simps)
    apply (clarsimp simp add: typ_heap_simps h_t_valid_clift_Some_iff)
    apply (erule iffD1 [OF tcb_queue_relation'_cong, OF refl refl refl, rotated -1])
    apply clarsimp
   apply (rule ext)
   apply (clarsimp dest!: ctcb_ptr_to_tcb_ptr_imageI simp add: typ_heap_simps h_t_valid_clift_Some_iff)
  apply (rule ext)
  apply (clarsimp simp add: tcb_null_ep_ptrs_def typ_heap_simps h_t_valid_clift_Some_iff)
  done

(* FIXME: move up to SR_lemmas_C and remove from Retype_C *)
lemma map_to_ko_atI2:
  "\<lbrakk>(projectKO_opt \<circ>\<^sub>m (ksPSpace s)) x = Some v; pspace_aligned' s; pspace_distinct' s\<rbrakk> \<Longrightarrow> ko_at' v x s"
  apply (clarsimp simp: map_comp_Some_iff)
  apply (erule (2) aligned_distinct_obj_atI')
  apply (simp add: project_inject)
  done

lemma map_to_ko_at_updI':
  "\<And>x x' y y' y''.
   \<lbrakk> (projectKO_opt \<circ>\<^sub>m (ksPSpace s)) x = Some y;
     valid_pspace' s; ko_at' y' x' s;
     objBitsKO (injectKO y') = objBitsKO y''; x \<noteq> x' \<rbrakk> \<Longrightarrow>
   ko_at' y x (s\<lparr>ksPSpace := ksPSpace s(x' \<mapsto> y'')\<rparr>)"
  by (fastforce simp: obj_at'_def projectKOs objBitsKO_def ps_clear_upd
               dest: map_to_ko_atI2)

(* FIXME: move *)
lemma state_refs_of'_upd:
  "\<lbrakk> valid_pspace' s; ko_wp_at' (\<lambda>ko. objBitsKO ko = objBitsKO ko') ptr s \<rbrakk> \<Longrightarrow>
   state_refs_of' (s\<lparr>ksPSpace := ksPSpace s(ptr \<mapsto> ko')\<rparr>) =
   (state_refs_of' s)(ptr := refs_of' ko')"
  apply (rule ext)
  apply (clarsimp simp: ps_clear_upd valid_pspace'_def pspace_aligned'_def
                        obj_at'_def ko_wp_at'_def state_refs_of'_def
                 split: option.split)
  done

lemma sendIPC_enqueue_ccorres_helper:
  "ccorres dc xfdc (valid_pspace'
                and (\<lambda>s. sym_refs ((state_refs_of' s)(epptr := set queue \<times> {EPSend})))
                and st_tcb_at'  (\<lambda>st. isBlockedOnSend st \<and>
                                      blockingIPCEndpoint st = epptr) thread
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
  apply (clarsimp split del: split_if simp del: comp_def)
  apply (frule cmap_relation_ep)
  apply (erule (1) cmap_relation_ko_atE)
  apply (rule conjI)
   apply (erule h_t_valid_clift)
  apply (frule(1) st_tcb_at_h_t_valid)
  apply (frule st_tcb_at')
  apply (rule impI)
  apply (rule_tac x="init queue" in exI)
  apply (frule(1) ko_at_valid_ep' [OF _ valid_pspace_valid_objs'])
  apply (frule is_aligned_tcb_ptr_to_ctcb_ptr)
  apply (rule conjI)
   apply (rule_tac x=\<sigma> in exI)
   apply (simp add: cendpoint_relation_def Let_def)
   apply (case_tac ep, simp_all add: init_def valid_ep'_def)[1]
  apply (subgoal_tac "sym_refs (state_refs_of' (\<sigma>\<lparr>ksPSpace :=
                          ksPSpace \<sigma>(epptr \<mapsto> KOEndpoint (SendEP queue))\<rparr>))")
   prefer 2
   apply (clarsimp simp: state_refs_of'_upd ko_wp_at'_def
                         obj_at'_def projectKOs objBitsKO_def)
  apply (subgoal_tac "ko_at' (SendEP queue) epptr (\<sigma>\<lparr>ksPSpace :=
                          ksPSpace \<sigma>(epptr \<mapsto> KOEndpoint (SendEP queue))\<rparr>)")
   prefer 2
   apply (clarsimp simp: obj_at'_def projectKOs objBitsKO_def ps_clear_upd)
  apply (intro conjI impI allI)
    apply (fastforce simp: h_t_valid_clift)
   apply (fastforce simp: h_t_valid_clift)
  apply (case_tac ep, simp_all add: EPState_Idle_def EPState_Send_def)[1]
   -- "IdleEP case"
   apply clarsimp
   apply (frule null_ep_queue [simplified comp_def] null_ep_queue)
   apply (simp add: setEndpoint_def split_def)
   apply (rule bexI [OF _ setObject_eq])
       apply (simp add: rf_sr_def cstate_relation_def init_def Let_def
                        cpspace_relation_def update_ep_map_tos)
       apply (elim conjE)
       apply (intro conjI)
            -- "tcb relation"
            apply (erule ctcb_relation_null_queue_ptrs)
            apply (clarsimp simp: comp_def)
           -- "ep relation"
           apply (rule cpspace_relation_ep_update_ep', assumption+)
            apply (clarsimp simp: cendpoint_relation_def Let_def
                                  mask_def [where n=2] EPState_Send_def)
            apply (clarsimp simp: tcb_queue_relation'_def is_aligned_neg_mask)
           apply (simp add: isSendEP_def isRecvEP_def)
          -- "aep relation"
          apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
          apply simp
          apply (rule casync_endpoint_relation_ep_queue, assumption+)
            apply (simp add: isSendEP_def isRecvEP_def)
           apply simp
          apply (frule_tac x=p in map_to_ko_atI2, clarsimp, clarsimp)
          apply (erule(2) map_to_ko_at_updI')
           apply (simp only:projectKOs injectKO_ep objBits_simps)
           apply clarsimp
          apply (clarsimp simp: obj_at'_def projectKOs)
         -- "queue relation"
         apply (rule cready_queues_relation_null_queue_ptrs, assumption+)
         apply (clarsimp simp: comp_def)
        apply (simp add: carch_state_relation_def)
       apply (simp add: cmachine_state_relation_def)
      apply (simp add: h_t_valid_clift_Some_iff)
     apply (simp add: objBits_simps)
    apply (simp add: objBits_simps)
   apply assumption
  -- "SendEP case"
  apply clarsimp
  apply (frule null_ep_queue [simplified comp_def] null_ep_queue)
  apply (simp add: setEndpoint_def split_def)
  apply (rule bexI [OF _ setObject_eq])
      apply (simp add: rf_sr_def cstate_relation_def Let_def init_def
                       cpspace_relation_def update_ep_map_tos)
      apply (elim conjE)
      apply (intro conjI)
           -- "tcb relation"
           apply (erule ctcb_relation_null_queue_ptrs)
           apply (clarsimp simp: comp_def)
          -- "ep relation"
          apply (rule cpspace_relation_ep_update_ep', assumption+)
           apply (clarsimp simp: cendpoint_relation_def Let_def
                                 mask_def [where n=2] EPState_Send_def)
           apply (fastforce simp: tcb_queue_relation'_def is_aligned_neg_mask
                                 valid_ep'_def
                           dest: tcb_queue_relation_next_not_NULL)
          apply (simp add: isSendEP_def isRecvEP_def)
         -- "aep relation"
         apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
         apply simp
         apply (rule casync_endpoint_relation_ep_queue, assumption+)
           apply (simp add: isSendEP_def isRecvEP_def)
          apply simp
         apply (frule_tac x=p in map_to_ko_atI2, clarsimp, clarsimp)
         apply (erule(2) map_to_ko_at_updI')
          apply (clarsimp simp: objBitsKO_def)
         apply (clarsimp simp: obj_at'_def projectKOs)
        -- "queue relation"
        apply (rule cready_queues_relation_null_queue_ptrs, assumption+)
        apply (clarsimp simp: comp_def)
       apply (simp add: carch_state_relation_def)
      apply (simp add: cmachine_state_relation_def)
     apply (simp add: h_t_valid_clift_Some_iff)
    apply (simp add: objBits_simps)
   apply (simp add: objBits_simps)
  apply assumption
  done

lemmas attemptSwitchTo_sch_act_not
    = possibleSwitchTo_sch_act_not[where b=True, folded attemptSwitchTo_def]

lemma sendIPC_ccorres [corres]:
  "ccorres dc xfdc (invs' and st_tcb_at' simple' thread
                          and sch_act_not thread and ep_at' epptr and
                          (\<lambda>s. \<forall>d p. thread \<notin> set (ksReadyQueues s (d, p))))
     (UNIV \<inter> \<lbrace>\<acute>blocking = from_bool blocking\<rbrace>
           \<inter> \<lbrace>\<acute>do_call = from_bool do_call\<rbrace>
           \<inter> \<lbrace>\<acute>badge = badge\<rbrace>
           \<inter> \<lbrace>\<acute>canGrant = from_bool canGrant\<rbrace>
           \<inter> \<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr thread\<rbrace>
           \<inter> \<lbrace>\<acute>epptr = Ptr epptr\<rbrace>
           \<inter> \<lbrace>badge && mask 28 = badge\<rbrace>) hs
     (sendIPC blocking do_call badge canGrant thread epptr)
     (Call sendIPC_'proc)"
  unfolding K_def
  apply (rule ccorres_gen_asm2)
  apply (cinit' lift: blocking_' do_call_' badge_' canGrant_' thread_' epptr_')
   apply (unfold sendIPC_def)[1]
   apply (rule ccorres_pre_getEndpoint)
   apply (rename_tac ep)
   apply (rule_tac xf'=ret__unsigned_long_'
               and val="case ep of IdleEP \<Rightarrow> scast EPState_Idle
                           | RecvEP _ \<Rightarrow> scast EPState_Recv | SendEP _ \<Rightarrow> scast EPState_Send"
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
                          and (\<lambda>s. \<forall>d p. thread \<notin> set (ksReadyQueues s (d, p)))"
                 in ccorres_guard_imp2 [where A'=UNIV])
     apply wpc
       -- "RecvEP case"
       apply (rule ccorres_cond_false)
       apply (rule ccorres_cond_true)
       apply (intro ccorres_rhs_assoc)
       apply (csymbr, csymbr, csymbr)
       apply wpc
        apply (simp only: haskell_fail_def)
        apply (rule ccorres_fail)
       apply (rename_tac dest rest)
       (* apply (ctac(c_lines 6) add: sendIPC_dequeue_ccorres_helper) *)
       apply (rule ccorres_rhs_assoc2)
       apply (rule ccorres_rhs_assoc2)
       apply (rule ccorres_rhs_assoc2)
       apply (rule ccorres_rhs_assoc2)
       apply (rule ccorres_rhs_assoc2)
       apply (rule ccorres_split_nothrow_novcg)            
           apply (rule_tac dest=dest in sendIPC_dequeue_ccorres_helper)
           apply simp
          apply ceqv
         apply (rename_tac dest')
         apply (simp only: K_bind_def haskell_assert_def return_bind)
         apply (rule ccorres_move_c_guard_tcb)
         apply (rule getThreadState_ccorres_foo)
         apply (rename_tac recvState)
         apply (rule ccorres_assert)
         apply (rule_tac val="from_bool (blockingIPCDiminishCaps recvState)"
                     and xf'=diminish_'
                     and R="\<lambda>s. \<exists>t. ko_at' t dest s \<and> tcbState t = recvState"
                      in ccorres_symb_exec_r_known_rv_UNIV [where R'=UNIV])
            apply (vcg, clarsimp)
            apply (erule(1) cmap_relation_ko_atE [OF cmap_relation_tcb])
            apply (clarsimp simp: ctcb_relation_def typ_heap_simps
                                  cthread_state_relation_def word_size
                                  isReceive_def thread_state_lift_def
                           split: Structures_H.thread_state.splits)
           apply ceqv
          apply (ctac(no_vcg)) 
           apply (ctac(no_vcg))
            apply (ctac(no_vcg))
             apply (rule ccorres_pre_threadGet)
             apply (rename_tac fault)
             apply (clarsimp split del: split_if)
             apply wpc
              apply (clarsimp simp: from_bool_def split del: split_if)
              apply (fold dc_def)[1] 
              apply (rule ccorres_symb_exec_r)
                apply (rule ccorres_cond_true_seq)
                apply (simp only: ccorres_seq_skip)
                apply (rule ccorres_cond_true)
                apply (simp only: case_bool_If Collect_const[symmetric]) 
                apply (rule_tac R=\<top> in ccorres_cond)
                  apply clarsimp
                 apply (ctac add: setupCallerCap_ccorres)
                apply (ctac add: setThreadState_ccorres)
               apply vcg
              apply (rule conseqPre, vcg, clarsimp)
             apply (clarsimp simp: from_bool_def split del: split_if)
             apply (fold dc_def)[1]
             apply (rule ccorres_symb_exec_r)
               apply (rule ccorres_cond_false_seq)
               apply (intro ccorres_rhs_assoc)
               apply (rule ccorres_move_c_guard_tcb [simplified])
               apply (rule_tac val="case_option (scast fault_null_fault)
                                                fault_to_fault_tag fault"
                           and xf'=ret__unsigned_long_'
                           and R="\<lambda>s. \<exists>t. ko_at' t thread s \<and> tcbFault t = fault"
                            in ccorres_symb_exec_r_known_rv_UNIV [where R'=UNIV])
                  apply (rule conseqPre, vcg, clarsimp)
                  apply (erule(1) cmap_relation_ko_atE [OF cmap_relation_tcb])
                  apply (fastforce simp: ctcb_relation_def typ_heap_simps
                                        cfault_rel_def fault_lift_def Let_def
                                 split: split_if_asm option.split)
                 apply ceqv
                apply wpc
                 apply (clarsimp split del: split_if)
                 apply (rule ccorres_symb_exec_r)
                   apply (rule ccorres_cond_false)
                   apply (fold dc_def)[1]
                   apply (rule ccorres_return_Skip)
                  apply vcg
                 apply (rule conseqPre, vcg, clarsimp)
                apply (clarsimp split del: split_if)
                apply (fold dc_def)[1]
                apply (rule ccorres_symb_exec_r)
                  apply (rule ccorres_cond_true)
                  apply (simp only: case_bool_If)
                  apply (rule_tac R=\<top> in ccorres_cond)
                    apply clarsimp
                   apply (ctac add: setupCallerCap_ccorres)
                  apply (ctac add: setThreadState_ccorres)
                 apply vcg
                apply (rule conseqPre, vcg, clarsimp)
               apply (clarsimp simp: fault_to_fault_tag_nonzero fault_null_fault_def
                                     guard_is_UNIV_def ThreadState_Inactive_def)
              apply vcg
             apply (rule conseqPre, vcg, clarsimp)
            apply (rule_tac Q="\<lambda>rv. valid_queues and valid_pspace' and valid_objs'
                                    and sch_act_not thread and tcb_at' thread
                                    and tcb_at' dest and
                                    (\<lambda>s. sch_act_wf (ksSchedulerAction s) s \<and>
                                    (\<forall>d p. thread \<notin> set (ksReadyQueues s (d, p))))"
                         in hoare_post_imp)
             apply (fastforce simp: weak_sch_act_wf_def valid_tcb_state'_def
                              elim: obj_at'_weakenE)
            apply (wp attemptSwitchTo_sch_act_not sts_st_tcb' hoare_vcg_all_lift
                      attemptSwitchTo_ksQ sts_valid_queues sts_ksQ')
          apply (clarsimp simp: valid_tcb_state'_def)
          apply (wp weak_sch_act_wf_lift_linear tcb_in_cur_domain'_lift)
         apply (clarsimp simp: guard_is_UNIV_def ThreadState_Inactive_def
                               ThreadState_Running_def mask_def from_bool_def
                               option_to_ptr_def option_to_0_def
                        split: bool.split_asm)
        apply (rule_tac Q="\<lambda>rv. valid_queues and valid_pspace' and valid_objs'
                            and valid_mdb' and tcb_at' dest and cur_tcb'
                            and tcb_at' thread and K (dest \<noteq> thread)
                            and sch_act_not thread and K (epptr \<noteq> 0)
                            and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s \<and>
                                (\<forall>d p. thread \<notin> set (ksReadyQueues s (d, p))))"
                     in hoare_post_imp)
         apply (clarsimp simp: st_tcb_at'_def obj_at'_def is_tcb weak_sch_act_wf_def)
        apply (wp setEndpoint_ksQ hoare_vcg_all_lift set_ep_valid_objs'
                  setEndpoint_valid_mdb')
       apply (clarsimp simp: guard_is_UNIV_def)
      -- "IdleEP case"
      apply (rule ccorres_cond_true)
      apply (rule ccorres_cond)
        apply (clarsimp simp: from_bool_def split: bool.split)
       -- "blocking case"
       apply (intro ccorres_rhs_assoc)
       apply csymbr
       apply (simp only:)
       -- "apply (ctac (trace, no_vcg,c_lines 6) add: sendIPC_block_ccorres_helper)"
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
        apply (rule_tac Q="\<lambda>rv. ko_wp_at' (\<lambda>x. projectKO_opt x = Some IdleEP
                                    \<and> projectKO_opt x = (None::tcb option)) epptr"
                     in hoare_post_imp)
         apply (clarsimp simp: obj_at'_def ko_wp_at'_def projectKOs)
        apply wp
       apply (clarsimp simp: guard_is_UNIV_def)
      apply (rule ccorres_return_Skip)
     -- "SendEP case"
     apply (rule ccorres_cond_true)
     apply (rule ccorres_cond)
       apply (clarsimp simp: from_bool_def split: bool.split)
      -- "blocking case"
      apply (intro ccorres_rhs_assoc)
      apply csymbr
      -- "apply (ctac (no_vcg,c_lines 6) add: sendIPC_block_ccorres_helper)"
      apply (rule ccorres_rhs_assoc2)
      apply (rule ccorres_rhs_assoc2)
      apply (rule ccorres_rhs_assoc2)
      apply (rule ccorres_rhs_assoc2)
      apply (rule ccorres_rhs_assoc2)
      apply (rule ccorres_split_nothrow_novcg)
          apply (simp only: )
          apply (rule sendIPC_block_ccorres_helper)
         apply ceqv
        apply (simp only: K_bind_def fun_app_def)
        apply (rule_tac ep="SendEP list" in sendIPC_enqueue_ccorres_helper)
       apply (simp add: valid_ep'_def)
       apply (wp sts_st_tcb')
       apply (rule_tac Q="\<lambda>rv. ko_wp_at' (\<lambda>x. projectKO_opt x = Some (SendEP list)
                                   \<and> projectKO_opt x = (None::tcb option)) epptr
                           and K (thread \<notin> set list)"
                    in hoare_post_imp)
        apply (clarsimp simp: obj_at'_def ko_wp_at'_def projectKOs)
       apply wp
      apply (clarsimp simp: guard_is_UNIV_def)
     apply (rule ccorres_return_Skip)
    apply (clarsimp simp: EPState_Recv_def EPState_Send_def EPState_Idle_def)
    apply (frule(1) ko_at_valid_objs' [OF _ invs_valid_objs'])
     apply (clarsimp simp: projectKO_opt_ep split: kernel_object.split_asm)
    apply (subgoal_tac "epptr \<noteq> thread \<and> state_refs_of' s thread = {}
                            \<and> (\<forall>r. (thread, r) \<notin> ep_q_refs_of' ep)")
     apply (clarsimp simp: valid_obj'_def valid_ep'_def refs_of'_def
                    split: endpoint.splits)
       apply (frule(1) sym_refs_obj_atD' [OF _ invs_sym'])
       apply (clarsimp simp: st_tcb_at_refs_of_rev' isBlockedOnReceive_def)
       apply (auto split: list.splits elim!: st_tcb'_weakenE)[1]
      apply (subgoal_tac "state_refs_of' s epptr = {}")
       apply (fastforce simp: obj_at'_def is_aligned_neg_mask objBitsKO_def projectKOs
                             invs'_def valid_state'_def st_tcb_at'_def
                             valid_tcb_state'_def ko_wp_at'_def
                             isBlockedOnSend_def projectKO_opt_tcb
                       elim: delta_sym_refs
                      split: split_if_asm)
      apply (clarsimp simp: obj_at'_def state_refs_of'_def projectKOs)
     apply (frule(1) sym_refs_obj_atD' [OF _ invs_sym'])
     apply clarsimp
     apply (rule conjI, assumption)
     apply (fastforce simp: valid_tcb_state'_def isBlockedOnSend_def
                elim!: delta_sym_refs[OF invs_sym_refs']
                split: split_if_asm
                simp: obj_at'_def projectKOs projectKO_opt_tcb
                       ko_wp_at'_def objBits_simps)[1]
    apply (frule(1) sym_refs_obj_atD' [OF _ invs_sym'])
    apply (frule simple_st_tcb_at_state_refs_ofD')
    apply (case_tac ep, auto simp: st_tcb_at_refs_of_rev'
                  st_tcb_at'_def obj_at'_def projectKOs)[1]
   apply (clarsimp simp: guard_is_UNIV_def)
  apply clarsimp
  done

lemma receiveIPC_block_ccorres_helper:
  "ccorres dc xfdc (tcb_at' thread and valid_queues and valid_objs' and
                    sch_act_not thread and ep_at' epptr and
                    (\<lambda>s. sch_act_wf (ksSchedulerAction s) s \<and>
                     (\<forall>d p. thread \<notin> set (ksReadyQueues s (d, p)))) and
                    K (epptr = epptr && ~~ mask 4) and
                    K (diminish' = from_bool diminish))
                   UNIV hs
           (setThreadState (Structures_H.thread_state.BlockedOnReceive
                                epptr diminish) thread)
           (Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t tcb_ptr_to_ctcb_ptr thread\<rbrace>
             (CALL thread_state_ptr_set_tsType(Ptr
              &(tcb_ptr_to_ctcb_ptr thread\<rightarrow>[''tcbState_C'']),
              scast ThreadState_BlockedOnReceive));;
            Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t tcb_ptr_to_ctcb_ptr thread\<rbrace>
             (CALL thread_state_ptr_set_blockingIPCEndpoint(Ptr
                           &(tcb_ptr_to_ctcb_ptr thread\<rightarrow>[''tcbState_C'']),
              ucast (ptr_val (ep_Ptr epptr))));;
            Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t tcb_ptr_to_ctcb_ptr thread\<rbrace>
             (CALL thread_state_ptr_set_blockingIPCDiminishCaps(Ptr
                           &(tcb_ptr_to_ctcb_ptr thread\<rightarrow>[''tcbState_C'']),
              diminish'));;
            CALL scheduleTCB(tcb_ptr_to_ctcb_ptr thread))"
  unfolding K_def setThreadState_def
  apply (intro ccorres_gen_asm)
  apply (rule ccorres_guard_imp)
    apply (rule ccorres_split_nothrow_novcg)
        apply (rule_tac P=\<top> and P'="tcb_at' thread"
                     in threadSet_ccorres_lemma3)
         apply vcg
        apply clarsimp
        apply (frule(1) tcb_at_h_t_valid)
        apply (frule h_t_valid_c_guard)
        apply (clarsimp simp: typ_heap_simps)
        apply (erule(1) rf_sr_tcb_update_no_queue)
               apply (simp add: typ_heap_simps)+
         apply (simp add: tcb_cte_cases_def)
        apply (simp add: ctcb_relation_def cthread_state_relation_def
                         ThreadState_BlockedOnReceive_def mask_def
                         from_bool_def to_bool_def)
        apply (clarsimp split: bool.split)
       apply ceqv
      apply clarsimp
      apply ctac
     apply (wp threadSet_valid_queues hoare_vcg_all_lift threadSet_valid_objs'
               threadSet_weak_sch_act_wf_runnable')
    apply (clarsimp simp: guard_is_UNIV_def)
   apply (clarsimp simp: sch_act_wf_weak valid_tcb'_def valid_tcb_state'_def
                         tcb_cte_cases_def)
  apply clarsimp
  done 

lemma receiveIPC_enqueue_ccorres_helper:
  "ccorres dc xfdc (valid_pspace'
                and (\<lambda>s. sym_refs ((state_refs_of' s)(epptr := set queue \<times> {EPRecv})))
                and st_tcb_at'  (\<lambda>st. isBlockedOnReceive st \<and>
                                      blockingIPCEndpoint st = epptr) thread
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
  apply (clarsimp split del: split_if simp del: comp_def)
  apply (frule cmap_relation_ep)
  apply (erule (1) cmap_relation_ko_atE)
  apply (rule conjI)
   apply (erule h_t_valid_clift)
  apply (frule(1) st_tcb_at_h_t_valid)
  apply (frule st_tcb_at')
  apply (rule impI)
  apply (rule_tac x="init queue" in exI)
  apply (frule(1) ko_at_valid_ep' [OF _ valid_pspace_valid_objs'])
  apply (frule is_aligned_tcb_ptr_to_ctcb_ptr)
  apply (rule conjI)
   apply (rule_tac x=\<sigma> in exI)
   apply (simp add: cendpoint_relation_def Let_def)
   apply (case_tac ep, simp_all add: init_def valid_ep'_def)[1]
  apply (subgoal_tac "sym_refs (state_refs_of' (\<sigma>\<lparr>ksPSpace :=
                          ksPSpace \<sigma>(epptr \<mapsto> KOEndpoint (RecvEP queue))\<rparr>))")
   prefer 2
   apply (clarsimp simp: state_refs_of'_upd ko_wp_at'_def
                         obj_at'_def projectKOs objBitsKO_def)
  apply (subgoal_tac "ko_at' (RecvEP queue) epptr (\<sigma>\<lparr>ksPSpace :=
                          ksPSpace \<sigma>(epptr \<mapsto> KOEndpoint (RecvEP queue))\<rparr>)")
   prefer 2
   apply (clarsimp simp: obj_at'_def projectKOs objBitsKO_def ps_clear_upd)
  apply (intro conjI impI allI)
    apply (fastforce simp: h_t_valid_clift)
   apply (fastforce simp: h_t_valid_clift)
  apply (case_tac ep, simp_all add: EPState_Idle_def EPState_Recv_def)[1]
   -- "RecvEP case"
   apply clarsimp
   apply (frule null_ep_queue [simplified comp_def] null_ep_queue)
   apply (simp add: setEndpoint_def split_def)
   apply (rule bexI [OF _ setObject_eq])
       apply (simp add: rf_sr_def cstate_relation_def Let_def init_def
                        cpspace_relation_def update_ep_map_tos)
       apply (elim conjE)
       apply (intro conjI)
             -- "tcb relation"
            apply (erule ctcb_relation_null_queue_ptrs)
            apply (clarsimp simp: comp_def)
           -- "ep relation"
           apply (rule cpspace_relation_ep_update_ep', assumption+)
            apply (clarsimp simp: cendpoint_relation_def Let_def
                                  mask_def [where n=2] EPState_Recv_def)
            apply (fastforce simp: tcb_queue_relation'_def is_aligned_neg_mask
                                  valid_ep'_def
                            dest: tcb_queue_relation_next_not_NULL)
           apply (simp add: isSendEP_def isRecvEP_def)
          -- "aep relation"
          apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
          apply simp
          apply (rule casync_endpoint_relation_ep_queue, assumption+)
            apply (simp add: isSendEP_def isRecvEP_def)
           apply simp
          apply (frule_tac x=p in map_to_ko_atI2, clarsimp, clarsimp)
          apply (erule(2) map_to_ko_at_updI')
           apply (clarsimp simp: objBitsKO_def)
          apply (clarsimp simp: obj_at'_def projectKOs)
         -- "queue relation"
         apply (rule cready_queues_relation_null_queue_ptrs, assumption+)
         apply (clarsimp simp: comp_def)
        apply (simp add: carch_state_relation_def)
       apply (simp add: cmachine_state_relation_def)
      apply (simp add: h_t_valid_clift_Some_iff)
     apply (simp add: objBits_simps)
    apply (simp add: objBits_simps)
   apply assumption
  -- "IdleEP case"
  apply clarsimp
  apply (frule null_ep_queue [simplified comp_def] null_ep_queue)
  apply (simp add: setEndpoint_def split_def)
  apply (rule bexI [OF _ setObject_eq])
      apply (simp add: rf_sr_def cstate_relation_def init_def Let_def
                       cpspace_relation_def update_ep_map_tos)
      apply (elim conjE)
      apply (intro conjI)
           -- "tcb relation"
           apply (erule ctcb_relation_null_queue_ptrs)
           apply (clarsimp simp: comp_def)
          -- "ep relation"
          apply (rule cpspace_relation_ep_update_ep', assumption+)
           apply (clarsimp simp: cendpoint_relation_def Let_def
                                 mask_def [where n=2] EPState_Recv_def)
           apply (clarsimp simp: tcb_queue_relation'_def is_aligned_neg_mask)
          apply (simp add: isSendEP_def isRecvEP_def)
         -- "aep relation"
         apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
         apply simp
         apply (rule casync_endpoint_relation_ep_queue, assumption+)
           apply (simp add: isSendEP_def isRecvEP_def)
          apply simp
         apply (frule_tac x=p in map_to_ko_atI2, clarsimp, clarsimp)
         apply (erule(2) map_to_ko_at_updI')
          apply (clarsimp simp: objBitsKO_def)
         apply (clarsimp simp: obj_at'_def projectKOs)
        -- "queue relation"
        apply (rule cready_queues_relation_null_queue_ptrs, assumption+)
        apply (clarsimp simp: comp_def)
       apply (simp add: carch_state_relation_def)
      apply (simp add: cmachine_state_relation_def)
     apply (simp add: h_t_valid_clift_Some_iff)
    apply (simp add: objBits_simps)
   apply (simp add: objBits_simps)
  apply assumption
  done

lemma receiveIPC_dequeue_ccorres_helper:
  "ccorres (\<lambda>rv rv'. rv' = tcb_ptr_to_ctcb_ptr sender) sender_'
           (invs' and st_tcb_at' (\<lambda>st. isBlockedOnSend st \<and>
                                       blockingIPCEndpoint st = ep) sender
                  and ko_at' (SendEP (sender#rest)) ep) UNIV hs
           (setEndpoint ep (case rest of [] \<Rightarrow> Structures_H.IdleEP
                                       | (a#list) \<Rightarrow> Structures_H.SendEP rest))
        (\<acute>queue :== CALL ep_ptr_get_queue(Ptr ep);;
         \<acute>sender :== head_C \<acute>queue;;
         SKIP;;
         \<acute>queue :== CALL tcbEPDequeue(\<acute>sender,\<acute>queue);;
         CALL ep_ptr_set_queue(Ptr ep,\<acute>queue);;
         IF head_C \<acute>queue = Ptr 0 THEN
             CALL endpoint_ptr_set_state(Ptr ep,scast EPState_Idle)
         FI)"
  apply (rule ccorres_from_vcg)
  apply (rule allI)
  apply (rule conseqPre, vcg)
  apply (clarsimp split del: split_if simp del: comp_def)
  apply (frule ep_blocked_in_queueD [OF st_tcb'_weakenE])
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
              cong: imp_cong split del: split_if simp del: comp_def)
  apply (intro conjI impI allI)
     apply (fastforce simp: h_t_valid_clift)
    apply (fastforce simp: h_t_valid_clift)
   -- "empty case"
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
                         cpspace_relation_def update_ep_map_tos)
        apply (elim conjE)
        apply (intro conjI)
             -- "tcb relation"
             apply (erule ctcb_relation_null_queue_ptrs)
             apply (clarsimp simp: comp_def)
            -- "ep relation"
            apply (rule cpspace_relation_ep_update_ep, assumption+)
             apply (simp add: cendpoint_relation_def Let_def EPState_Idle_def
                              tcb_queue_relation'_def)
            apply simp
           -- "aep relation"
           apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
           apply simp
           apply (rule casync_endpoint_relation_ep_queue [OF invs_sym'], assumption+)
           apply simp
          apply (erule (1) map_to_ko_atI')
          -- "queue relation"
          apply (rule cready_queues_relation_null_queue_ptrs, assumption+)
          apply (clarsimp simp: comp_def)
         apply (simp add: carch_state_relation_def)
        apply (simp add: cmachine_state_relation_def)
       apply (simp add: h_t_valid_clift_Some_iff)
      apply (simp add: objBits_simps)
     apply (simp add: objBits_simps)
    apply assumption
   apply (clarsimp simp: cendpoint_relation_def Let_def tcb_queue_relation'_def)
  -- "non-empty case"
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
                        cpspace_relation_def update_ep_map_tos)
       apply (elim conjE)
       apply (intro conjI)
            -- "tcb relation"
            apply (erule ctcb_relation_null_queue_ptrs)
            apply (clarsimp simp: comp_def)
           -- "ep relation"
           apply (rule cpspace_relation_ep_update_ep, assumption+)
            apply (clarsimp simp: cendpoint_relation_def Let_def
                                  isRecvEP_def isSendEP_def
                                  tcb_queue_relation'_def valid_ep'_def
                           split: endpoint.splits list.splits
                       split del: split_if)
            apply (subgoal_tac "tcb_at' (if x22 = [] then x21 else last x22) \<sigma>")
             apply (clarsimp simp: is_aligned_neg_mask
                            dest!: is_aligned_tcb_ptr_to_ctcb_ptr
                        split del: split_if)
            apply clarsimp
           apply simp
          -- "aep relation"
          apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
          apply simp
          apply (rule casync_endpoint_relation_ep_queue [OF invs_sym'], assumption+)
           apply simp
          apply (erule (1) map_to_ko_atI')
         -- "queue relation"
         apply (rule cready_queues_relation_null_queue_ptrs, assumption+)
         apply (clarsimp simp: comp_def)
        apply (simp add: carch_state_relation_def)
       apply (simp add: cmachine_state_relation_def)
      apply (simp add: h_t_valid_clift_Some_iff)
     apply (simp add: objBits_simps)
    apply (simp add: objBits_simps)
   apply assumption
  apply (clarsimp simp: cendpoint_relation_def Let_def tcb_queue_relation'_def)
  done

lemma receiveIPC_ccorres [corres]:
  "ccorres dc xfdc (invs' and st_tcb_at' simple' thread and sch_act_not thread
                          and (\<lambda>s. \<forall>d p. thread \<notin> set (ksReadyQueues s (d, p)))
                          and valid_cap' cap and K (isEndpointCap cap))
     (UNIV \<inter> \<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr thread\<rbrace>
           \<inter> \<lbrace>ccap_relation cap \<acute>cap\<rbrace>) hs
     (receiveIPC thread cap)
     (Call receiveIPC_'proc)"
  unfolding K_def
  apply (rule ccorres_gen_asm)
  apply (cinit lift: thread_' cap_')
   apply (rule ccorres_pre_getEndpoint)
   apply (rename_tac ep)
   apply (simp only: ccorres_seq_skip)
   apply (rule_tac xf'=ret__unsigned_long_'
               and val="capEPPtr cap"
               and R=\<top>
                in ccorres_symb_exec_r_known_rv_UNIV[where R'=UNIV])
      apply vcg
      apply (clarsimp simp: cap_get_tag_isCap isCap_simps)
      apply (frule cap_get_tag_isCap_unfolded_H_cap)
      apply (simp add: cap_endpoint_cap_lift ccap_relation_def cap_to_H_def)
     apply ceqv
    apply csymbr
    apply (rule_tac xf'=ret__unsigned_long_'
                and F="\<lambda>rv. to_bool rv = capEPCanSend cap"
                and R=\<top>
                 in ccorres_symb_exec_r_abstract_UNIV[where R'=UNIV])
       apply vcg
       apply (clarsimp simp: cap_get_tag_isCap isCap_simps)
       apply (frule cap_get_tag_isCap_unfolded_H_cap)
       apply (simp add: cap_endpoint_cap_lift ccap_relation_def cap_to_H_def)
      apply ceqv
     apply (csymbr, rename_tac canSend)
     apply (rule_tac xf'=ret__unsigned_long_'
                 and val="case ep of IdleEP \<Rightarrow> scast EPState_Idle
                             | RecvEP _ \<Rightarrow> scast EPState_Recv | SendEP _ \<Rightarrow> scast EPState_Send"
                 and R="ko_at' ep (capEPPtr cap)"
                  in ccorres_symb_exec_r_known_rv_UNIV[where R'=UNIV])
        apply (vcg, clarsimp)
        apply (erule cmap_relationE1 [OF cmap_relation_ep])
         apply (erule ko_at_projectKO_opt)
        apply (clarsimp simp: typ_heap_simps cendpoint_relation_def Let_def
                       split: endpoint.split_asm)
       apply ceqv
      apply (rule_tac A="invs' and st_tcb_at' simple' thread and sch_act_not thread
                               and (\<lambda>s. \<forall>d p. thread \<notin> set (ksReadyQueues s (d, p)))
                               and ko_at' ep (capEPPtr cap)"
                   in ccorres_guard_imp2 [where A'=UNIV])
       apply wpc
         -- "RecvEP case"
         apply (rule ccorres_cond_true)
         apply (intro ccorres_rhs_assoc)
         apply csymbr
         (* apply (ctac (no_vcg,c_lines 4) add: receiveIPC_block_ccorres_helper) *)
         apply (rule ccorres_rhs_assoc2)
         apply (rule ccorres_rhs_assoc2)
         apply (rule ccorres_rhs_assoc2)
         apply (rule ccorres_split_nothrow_novcg)
             apply (rule receiveIPC_block_ccorres_helper)
            apply ceqv
           apply (rule_tac ep="RecvEP list" in receiveIPC_enqueue_ccorres_helper)
          apply (simp add: valid_ep'_def)
          apply (wp sts_st_tcb')
          apply (rule_tac Q="\<lambda>rv. ko_wp_at' (\<lambda>x. projectKO_opt x = Some (RecvEP list)
                                             \<and> projectKO_opt x = (None::tcb option))
                                            (capEPPtr cap)
                              and K (thread \<notin> set list)"
                       in hoare_post_imp)
           apply (clarsimp simp: obj_at'_def ko_wp_at'_def projectKOs)
          apply wp
         apply (clarsimp simp: guard_is_UNIV_def)
        -- "IdleEP case"
        apply (rule ccorres_cond_true)
        apply (intro ccorres_rhs_assoc)
        apply csymbr
        (* apply (ctac (no_vcg,c_lines 4) add: receiveIPC_block_ccorres_helper) *)
        apply (rule ccorres_rhs_assoc2)
        apply (rule ccorres_rhs_assoc2)
        apply (rule ccorres_rhs_assoc2)
        apply (rule ccorres_split_nothrow_novcg)
            apply (rule receiveIPC_block_ccorres_helper)
           apply ceqv
          apply (rule_tac ep=IdleEP in receiveIPC_enqueue_ccorres_helper)
         apply (simp add: valid_ep'_def)
         apply (wp sts_st_tcb')
         apply (rule_tac Q="\<lambda>rv. ko_wp_at' (\<lambda>x. projectKO_opt x = Some IdleEP
                                            \<and> projectKO_opt x = (None::tcb option))
                                           (capEPPtr cap)"
                      in hoare_post_imp)
          apply (clarsimp simp: obj_at'_def ko_wp_at'_def projectKOs)
         apply wp
        apply (clarsimp simp: guard_is_UNIV_def)
       -- "SendEP case"
       apply (rule ccorres_cond_false)
       apply (rule ccorres_cond_true)
       apply (intro ccorres_rhs_assoc)
       apply (csymbr, csymbr, csymbr, csymbr, csymbr)
       apply wpc
        apply (simp only: haskell_fail_def)
        apply (rule ccorres_fail)
       apply (rename_tac sender rest)
       (* apply (ctac(c_lines 6) add: receiveIPC_dequeue_ccorres_helper) *)
       apply (rule ccorres_rhs_assoc2)
       apply (rule ccorres_rhs_assoc2)
       apply (rule ccorres_rhs_assoc2)
       apply (rule ccorres_rhs_assoc2)
       apply (rule ccorres_rhs_assoc2)
       apply (rule ccorres_split_nothrow_novcg)
           apply (rule_tac sender=sender in receiveIPC_dequeue_ccorres_helper)
          apply ceqv
         apply (rename_tac sender')
         apply (simp only: K_bind_def haskell_assert_def return_bind)
         apply (rule ccorres_move_c_guard_tcb)
         apply (rule getThreadState_ccorres_foo)
         apply (rename_tac sendState)
         apply (rule ccorres_assert)
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
          apply (rule ccorres_move_c_guard_tcb)
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
           apply (ctac(no_vcg))
           apply (rule ccorres_move_c_guard_tcb)
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
             apply (rule ccorres_pre_threadGet)
             apply (rename_tac fault)
             apply (clarsimp split del: split_if)
             apply wpc
              apply (clarsimp simp: from_bool_def split del: split_if)
              apply (fold dc_def)[1]
              apply (rule ccorres_symb_exec_r)
                apply (rule ccorres_cond_true_seq)
                apply (simp only: ccorres_seq_skip)
                apply (rule ccorres_cond_true)
                apply (simp only: case_bool_If)
                apply (rule ccorres_cond)
                  apply (clarsimp simp: to_bool_def)
                 apply ctac
                apply ctac
               apply vcg
              apply (rule conseqPre, vcg)
              apply clarsimp
             apply (clarsimp simp: from_bool_def split del: split_if)
             apply (fold dc_def)[1]
             apply (rule ccorres_symb_exec_r)
               apply (rule ccorres_cond_false_seq)
               apply (intro ccorres_rhs_assoc)
               apply (rule ccorres_move_c_guard_tcb [simplified])
               apply (rule_tac val="case_option (scast fault_null_fault)
                                                fault_to_fault_tag fault"
                           and xf'=ret__unsigned_long_'
                           and R="\<lambda>s. \<exists>t. ko_at' t sender s \<and> tcbFault t = fault"
                            in ccorres_symb_exec_r_known_rv_UNIV [where R'=UNIV])
                  apply (rule conseqPre, vcg, clarsimp)
                  apply (erule(1) cmap_relation_ko_atE [OF cmap_relation_tcb])
                  apply (fastforce simp: ctcb_relation_def typ_heap_simps
                                        cfault_rel_def fault_lift_def Let_def
                                 split: split_if_asm option.split)
                 apply ceqv
                apply wpc
                 apply (clarsimp split del: split_if)
                 apply (fold dc_def)[1]
                 apply (rule ccorres_symb_exec_r)
                   apply (rule ccorres_cond_false)
                   apply (ctac(no_vcg))
                    apply ctac
                   apply (wp sts_st_tcb' sts_valid_queues)
                  apply vcg
                 apply (rule conseqPre, vcg, clarsimp)
                apply (clarsimp split del: split_if)
                apply (fold dc_def)[1]
                apply (rule ccorres_symb_exec_r)
                  apply (rule ccorres_cond_true)
                  apply (simp only: case_bool_If)
                  apply (rule ccorres_cond)
                    apply (clarsimp simp: to_bool_def)
                   apply ctac
                  apply ctac
                 apply vcg
                apply (rule conseqPre, vcg, clarsimp)
               apply (clarsimp simp: fault_to_fault_tag_nonzero fault_null_fault_def
                                     guard_is_UNIV_def ThreadState_Inactive_def
                                     ThreadState_Running_def mask_def)
              apply vcg
             apply (rule conseqPre, vcg, clarsimp)
            apply (clarsimp simp: guard_is_UNIV_def ThreadState_Inactive_def)
           apply (rule_tac Q="\<lambda>rv. valid_queues and valid_pspace' and valid_objs'
                               and st_tcb_at' (op = sendState) sender
                               and tcb_at' thread and sch_act_not sender
                               and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s \<and>
                                    (\<forall>d p. sender \<notin> set (ksReadyQueues s (d, p))))"
                        in hoare_post_imp)
            apply (fastforce simp: sch_act_wf_weak obj_at'_def st_tcb_at'_def
                                   valid_tcb_state'_def)[1]
           apply wp
          apply (clarsimp simp: guard_is_UNIV_def option_to_ptr_def option_to_0_def)
          apply (clarsimp simp add: to_bool_def)
         apply (clarsimp simp: guard_is_UNIV_def)
        apply (rule_tac Q="\<lambda>rv. valid_queues and valid_pspace' and valid_objs'
                            and cur_tcb' and tcb_at' sender and tcb_at' thread
                            and sch_act_not sender and K (thread \<noteq> sender)
                            and ep_at' (capEPPtr cap)
                            and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s \<and>
                                    (\<forall>d p. sender \<notin> set (ksReadyQueues s (d, p))))"
                     in hoare_post_imp)
         apply (auto, auto simp: st_tcb_at'_def obj_at'_def)[1]
        apply (wp hoare_vcg_all_lift set_ep_valid_objs')
       apply (clarsimp simp: guard_is_UNIV_def)
      apply (clarsimp simp: EPState_Recv_def EPState_Send_def EPState_Idle_def)
      apply (frule(1) ko_at_valid_objs' [OF _ invs_valid_objs'])
       apply (clarsimp simp: projectKO_opt_ep split: kernel_object.split_asm)
      apply (subgoal_tac "(capEPPtr cap) \<noteq> thread \<and> state_refs_of' s thread = {}")
       apply (clarsimp simp: valid_obj'_def valid_ep'_def refs_of'_def
                      split: endpoint.splits)
         apply (subgoal_tac "state_refs_of' s (capEPPtr cap) = (set list) \<times> {EPRecv}
                             \<and> thread \<notin> (set list)")
          apply (fastforce simp: obj_at'_def is_aligned_neg_mask objBitsKO_def
                                projectKOs invs'_def valid_state'_def st_tcb_at'_def
                                valid_tcb_state'_def ko_wp_at'_def invs_valid_objs'
                                isBlockedOnReceive_def projectKO_opt_tcb
                                from_bool_def to_bool_def valid_tcb_state'_def
                          elim: delta_sym_refs
                         split: split_if_asm bool.splits)
         apply (frule(1) sym_refs_obj_atD' [OF _ invs_sym'])
         apply (clarsimp simp: st_tcb_at'_def ko_wp_at'_def obj_at'_def projectKOs
                        split: split_if_asm)
         apply (drule(1) bspec)+
         apply (case_tac "tcbState obj", simp_all)[1]
        apply (subgoal_tac "state_refs_of' s (capEPPtr cap) = {}")
         apply (fastforce simp: obj_at'_def is_aligned_neg_mask objBitsKO_def
                               projectKOs invs'_def valid_state'_def st_tcb_at'_def
                               valid_tcb_state'_def ko_wp_at'_def invs_valid_objs'
                               isBlockedOnReceive_def projectKO_opt_tcb
                               from_bool_def to_bool_def valid_tcb_state'_def
                         elim: delta_sym_refs
                        split: split_if_asm bool.splits)
        apply (clarsimp simp: obj_at'_def state_refs_of'_def projectKOs)
       apply (frule(1) sym_refs_ko_atD' [OF _ invs_sym'])
       apply (frule invs_queues)
       apply clarsimp
       apply (rule_tac P="x\<in>set list" in case_split)
        apply (clarsimp simp:st_tcb_at_refs_of_rev')
        apply (erule_tac x=x and P="\<lambda>x. st_tcb_at' ?P x s" in ballE)
         apply (drule_tac t=x in valid_queues_not_runnable'_not_ksQ)
          apply (clarsimp simp: st_tcb_at'_def obj_at'_def o_def)
         apply (subgoal_tac "sch_act_not x s")
          prefer 2
          apply (frule invs_sch_act_wf')
          apply (clarsimp simp:sch_act_wf_def)
          apply (clarsimp simp: st_tcb_at'_def obj_at'_def o_def)
         apply (clarsimp simp: obj_at'_def st_tcb_at'_def
                               projectKOs isBlockedOnSend_def
                         split: list.split | rule conjI)+
      apply (clarsimp simp: state_refs_of'_def )
      apply (case_tac "tcbState obj", clarsimp+)[1]
     apply (clarsimp simp: guard_is_UNIV_def)+
  apply (clarsimp simp: valid_cap'_def isEndpointCap_def
                 split: capability.split_asm)
  done

lemma sendAsyncIPC_dequeue_ccorres_helper:
  "ccorres (\<lambda>rv rv'. rv' = tcb_ptr_to_ctcb_ptr dest) dest_'
           (invs' and st_tcb_at' (op = (BlockedOnAsyncEvent aep)) dest
                  and ko_at' (WaitingAEP (dest#rest)) aep) UNIV hs
           (setAsyncEP aep $ case rest of [] \<Rightarrow> Structures_H.IdleAEP
                                        | (a#list) \<Rightarrow> Structures_H.WaitingAEP rest)
        (\<acute>aep_queue :== CALL aep_ptr_get_queue(Ptr aep);;
         \<acute>dest :== head_C \<acute>aep_queue;;
         SKIP;;
         \<acute>aep_queue :== CALL tcbEPDequeue(\<acute>dest,\<acute>aep_queue);;
         CALL aep_ptr_set_queue(Ptr aep,\<acute>aep_queue);;
         IF head_C \<acute>aep_queue = Ptr 0 THEN
             CALL async_endpoint_ptr_set_state(Ptr aep,scast AEPState_Idle)
         FI)"
  apply (rule ccorres_from_vcg)
  apply (rule allI)
  apply (rule conseqPre, vcg)
  apply (clarsimp split del: split_if simp del: comp_def)
  apply (frule (2) aep_blocked_in_queueD)
  apply (frule (1) ko_at_valid_aep' [OF _ invs_valid_objs'])
  apply (elim conjE)
  apply (frule (1) valid_aep_isWaitingAEPD)
  apply (elim conjE)
  apply (frule cmap_relation_aep)
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
    apply (drule (2) aep_to_ep_queue)
    apply (simp add: tcb_queue_relation'_def)
   apply (clarsimp simp: typ_heap_simps casync_endpoint_relation_def Let_def
              cong: imp_cong split del: split_if simp del: comp_def)
  apply (intro conjI impI allI)
     apply (fastforce simp: h_t_valid_clift)
    apply (fastforce simp: h_t_valid_clift)
   -- "empty case"
   apply clarsimp
   apply (frule null_ep_queue [simplified comp_def] null_ep_queue)
   apply (frule iffD1 [OF tcb_queue_head_empty_iff
                          [OF tcb_queue_relation'_queue_rel]])
     apply (rule ballI, erule bspec)
     apply (erule subsetD [rotated])
     apply (clarsimp simp: casync_endpoint_relation_def Let_def
                           tcb_queue_relation'_def)
    apply simp
   apply (simp add: setAsyncEP_def split_def)
   apply (rule conjI)
    apply (rule bexI [OF _ setObject_eq])
        apply (simp add: rf_sr_def cstate_relation_def Let_def
                         cpspace_relation_def update_aep_map_tos)
        apply (elim conjE)
        apply (intro conjI)
             -- "tcb relation"
             apply (erule ctcb_relation_null_queue_ptrs)
             apply (clarsimp simp: comp_def)
            -- "ep relation"
            apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
            apply simp
            apply (rule cendpoint_relation_aep_queue [OF invs_sym'], assumption+)
             apply simp
            apply (erule (1) map_to_ko_atI')
           -- "aep relation"
           apply (rule cpspace_relation_aep_update_aep, assumption+)
            apply (simp add: casync_endpoint_relation_def Let_def AEPState_Idle_def
                             tcb_queue_relation'_def)
           apply simp
          -- "queue relation"
          apply (rule cready_queues_relation_null_queue_ptrs, assumption+)
          apply (clarsimp simp: comp_def)
         apply (simp add: carch_state_relation_def)
        apply (simp add: cmachine_state_relation_def)
       apply (simp add: h_t_valid_clift_Some_iff)
      apply (simp add: objBits_simps)
     apply (simp add: objBits_simps)
    apply assumption
   apply (clarsimp simp: casync_endpoint_relation_def Let_def
                         tcb_queue_relation'_def)
  -- "non-empty case"
  apply clarsimp
  apply (frule null_ep_queue [simplified comp_def] null_ep_queue)
  apply (frule tcb_queue_head_empty_iff [OF tcb_queue_relation'_queue_rel])
   apply (rule ballI, erule bspec)
   apply (erule subsetD [rotated])
   apply (clarsimp simp: casync_endpoint_relation_def Let_def
                         tcb_queue_relation'_def)
  apply (simp add: setAsyncEP_def split_def)
  apply (rule conjI)
   apply (rule bexI [OF _ setObject_eq])
       apply (frule(1) st_tcb_at_h_t_valid)
       apply (simp add: rf_sr_def cstate_relation_def Let_def
                        cpspace_relation_def update_aep_map_tos)
       apply (elim conjE)
       apply (intro conjI)
            -- "tcb relation"
            apply (erule ctcb_relation_null_queue_ptrs)
            apply (clarsimp simp: comp_def)
           -- "ep relation"
           apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
           apply simp
           apply (rule cendpoint_relation_aep_queue [OF invs_sym'], assumption+)
            apply simp
           apply (erule (1) map_to_ko_atI')
          -- "aep relation"
          apply (rule cpspace_relation_aep_update_aep, assumption+)
           apply (clarsimp simp: casync_endpoint_relation_def Let_def
                                 isWaitingAEP_def
                                 tcb_queue_relation'_def valid_aep'_def
                          split: async_endpoint.splits list.splits
                      split del: split_if)
           apply (subgoal_tac "tcb_at' (if x22 = [] then x21 else last x22) \<sigma>")
            apply (clarsimp simp: is_aligned_neg_mask
                           dest!: is_aligned_tcb_ptr_to_ctcb_ptr
                       split del: split_if)
           apply clarsimp
          apply simp
         -- "queue relation"
         apply (rule cready_queues_relation_null_queue_ptrs, assumption+)
         apply (clarsimp simp: comp_def)
        apply (simp add: carch_state_relation_def)
       apply (simp add: cmachine_state_relation_def)
      apply (simp add: h_t_valid_clift_Some_iff)
     apply (simp add: objBits_simps)
    apply (simp add: objBits_simps)
   apply assumption
  apply (clarsimp simp: casync_endpoint_relation_def Let_def
                        tcb_queue_relation'_def)
  done

lemma doAsyncTransfer_ccorres [corres]:
  "ccorres dc xfdc (tcb_at' thread and valid_queues)
     (UNIV \<inter> \<lbrace>\<acute>badge = badge\<rbrace> \<inter> \<lbrace>\<acute>msgWord = msgWord\<rbrace>
           \<inter> \<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr thread\<rbrace>) hs
     (doAsyncTransfer badge msgWord thread)
     (Call doAsyncTransfer_'proc)"
  apply (cinit lift: badge_' msgWord_' thread_')
   apply (clarsimp simp: setMRs_def zipWithM_x_mapM_x mapM_x_Cons mapM_x_Nil
                         msgRegisters_unfold
                         n_msgRegisters_def word_sless_def word_sle_def
              split del: split_if)
   apply (rule ccorres_symb_exec_l [OF _ lookupIPC_inv lookupIPC_inv
                                         empty_fail_lookupIPCBuffer])
   apply (simp add: ccorres_cond_iffs dc_def[symmetric])
   apply (intro ccorres_rhs_assoc)
   apply (ctac(no_vcg))
    apply csymbr
    apply (ctac(no_vcg))
     apply csymbr
     apply (rule setMessageInfo_ccorres)
    apply wp
  apply (clarsimp simp: ThreadState_Running_def mask_def
                        State_H.badgeRegister_def
                        ARMMachineTypes.badgeRegister_def
                        Kernel_C.badgeRegister_def Kernel_C.R0_def
                        msgRegisters_def fupdate_def message_info_to_H_def)
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

lemma sendAsyncIPC_ccorres [corres]:
  "ccorres dc xfdc invs'
     (UNIV \<inter> \<lbrace>\<acute>aepptr = Ptr aepptr\<rbrace> \<inter> \<lbrace>\<acute>badge = badge\<rbrace> \<inter> \<lbrace>\<acute>val = val\<rbrace>) hs
     (sendAsyncIPC aepptr badge val)
     (Call sendAsyncIPC_'proc)"
  apply (cinit lift: aepptr_' badge_' val_')
   apply (rule ccorres_pre_getAsyncEP, rename_tac aep)
   apply (rule_tac xf'=ret__unsigned_long_'
               and val="case aep of IdleAEP \<Rightarrow> scast AEPState_Idle
                                 | WaitingAEP _ \<Rightarrow> scast AEPState_Waiting
                                 | ActiveAEP _ _ \<Rightarrow> scast AEPState_Active"
               and R="ko_at' aep aepptr"
                in ccorres_symb_exec_r_known_rv_UNIV[where R'=UNIV])
      apply (vcg, clarsimp)
      apply (erule(1) cmap_relation_ko_atE [OF cmap_relation_aep])
      apply (clarsimp simp: casync_endpoint_relation_def Let_def typ_heap_simps
                     split: Structures_H.async_endpoint.splits)
     apply ceqv
    apply wpc
      -- "IdleAEP case"
      apply (rule ccorres_cond_true)
      apply (simp only: setAsyncEP_def)
      apply (rule_tac P="invs' and ko_at' IdleAEP aepptr" and P'=UNIV
                   in ccorres_from_vcg)
      apply (rule allI)
      apply (rule conseqPre, vcg)
      apply clarsimp
      apply (frule(1) cmap_relation_ko_atD [OF cmap_relation_aep])
      apply (clarsimp simp: typ_heap_simps)
      apply (rule bexI [OF _ setObject_eq])
          apply (simp add: rf_sr_def cstate_relation_def Let_def
                           cpspace_relation_def update_aep_map_tos)
          apply (elim conjE)
          apply (intro conjI)
            apply (rule cpspace_relation_aep_update_aep, assumption+)
             apply (simp add: casync_endpoint_relation_def Let_def
                              AEPState_Active_def mask_def)
            apply simp
           apply (simp add: carch_state_relation_def)
          apply (simp add: cmachine_state_relation_def)
         apply (simp add: h_t_valid_clift_Some_iff)
        apply (simp add: objBits_simps)
       apply (simp add: objBits_simps)
      apply assumption
     -- "ActiveAEP case"
     apply (rename_tac old_badge old_val)
     apply (rule ccorres_cond_false)
     apply (rule ccorres_cond_false)
     apply (rule ccorres_cond_true)
     apply (clarsimp simp: setAsyncEP_def)
     apply (rule_tac P="invs' and ko_at' (ActiveAEP old_badge old_val) aepptr"
                 and P'=UNIV
                  in ccorres_from_vcg)
     apply (rule allI)
     apply (rule conseqPre, vcg)
     apply clarsimp
     apply (frule(1) cmap_relation_ko_atD [OF cmap_relation_aep])
     apply (clarsimp simp: typ_heap_simps)
     apply (rule bexI [OF _ setObject_eq])
         apply (simp add: rf_sr_def cstate_relation_def Let_def
                          cpspace_relation_def update_aep_map_tos)
         apply (elim conjE)
         apply (intro conjI)
           apply (rule cpspace_relation_aep_update_aep, assumption+)
            apply (simp add: casync_endpoint_relation_def Let_def
                             AEPState_Active_def mask_def word_bw_comms)
           apply simp
          apply (simp add: carch_state_relation_def)
         apply (simp add: cmachine_state_relation_def)
        apply (simp add: h_t_valid_clift_Some_iff)
       apply (simp add: objBits_simps)
      apply (simp add: objBits_simps)
     apply assumption
    -- "WaitingAEP case"
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
        apply (rule_tac dest=dest in sendAsyncIPC_dequeue_ccorres_helper)
       apply ceqv
      apply (simp only: K_bind_def)
      apply (ctac (no_vcg))
       apply (ctac (no_vcg))
        apply ctac
       apply (simp add: doAsyncTransfer_def)
       apply (wp weak_sch_act_wf_lift_linear
         setThreadState_oa_queued
         sts_valid_queues tcb_in_cur_domain'_lift)[1]
      apply (wp sts_valid_queues sts_runnable)
     apply (wp setThreadState_st_tcb set_aep_valid_objs' | clarsimp)+
    apply (clarsimp simp: guard_is_UNIV_def ThreadState_Running_def mask_def)
   apply (clarsimp simp: guard_is_UNIV_def AEPState_Idle_def
                         AEPState_Active_def AEPState_Waiting_def)
  apply clarsimp
  apply safe
        apply (fastforce simp: st_tcb_at'_def ko_wp_at'_def obj_at'_def projectKOs
                        objBitsKO_def refs_of_rev' invs_valid_objs' valid_aep'_def
                  dest: sym_refs_obj_atD' [OF _ invs_sym'])
     apply (auto simp: valid_aep'_def ko_at_valid_aep' st_tcb'_iff
                split: list.splits
                  dest!:invs_valid_objs' ko_at_valid_aep')
  done

lemma receiveAsyncIPC_block_ccorres_helper:
  "ccorres dc xfdc (tcb_at' thread and valid_queues and sch_act_not thread and
                    valid_objs' and aep_at' aepptr and
                    (\<lambda>s. sch_act_wf (ksSchedulerAction s) s \<and>
                        (\<forall>d p. thread \<notin> set (ksReadyQueues s (d, p)))) and
                    K (aepptr = aepptr && ~~ mask 4))
                   UNIV hs
           (setThreadState (Structures_H.thread_state.BlockedOnAsyncEvent
                                aepptr) thread)
           (Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t tcb_ptr_to_ctcb_ptr thread\<rbrace>
             (CALL thread_state_ptr_set_tsType(Ptr
              &(tcb_ptr_to_ctcb_ptr thread\<rightarrow>[''tcbState_C'']),
              scast ThreadState_BlockedOnAsyncEvent));;
            Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t tcb_ptr_to_ctcb_ptr thread\<rbrace>
             (CALL thread_state_ptr_set_blockingIPCEndpoint(Ptr
                           &(tcb_ptr_to_ctcb_ptr thread\<rightarrow>[''tcbState_C'']),
              ucast (ptr_val (aep_Ptr aepptr))));;
            CALL scheduleTCB(tcb_ptr_to_ctcb_ptr thread))"
  unfolding K_def setThreadState_def
  apply (intro ccorres_gen_asm)
  apply (rule ccorres_guard_imp)
    apply (rule ccorres_split_nothrow_novcg)
        apply (rule_tac P=\<top> and P'="tcb_at' thread"
                     in threadSet_ccorres_lemma3)
         apply vcg
        apply clarsimp
        apply (frule(1) tcb_at_h_t_valid)
        apply (frule h_t_valid_c_guard)
        apply (clarsimp simp: typ_heap_simps)
        apply (erule(1) rf_sr_tcb_update_no_queue)
               apply (simp add: typ_heap_simps)+
         apply (simp add: tcb_cte_cases_def)
        apply (simp add: ctcb_relation_def cthread_state_relation_def
                         ThreadState_BlockedOnAsyncEvent_def mask_def
                         from_bool_def to_bool_def)
       apply ceqv
      apply clarsimp
      apply ctac
     apply (wp threadSet_valid_queues hoare_vcg_all_lift threadSet_valid_objs'
               threadSet_weak_sch_act_wf_runnable')
    apply (clarsimp simp: guard_is_UNIV_def)
   apply (auto simp: weak_sch_act_wf_def valid_tcb'_def tcb_cte_cases_def
                     valid_tcb_state'_def)
  done

lemma cpspace_relation_aep_update_aep':
  fixes aep :: "async_endpoint" and aep' :: "async_endpoint"
    and aepptr :: "word32" and s :: "kernel_state"
  defines "qs \<equiv> if isWaitingAEP aep' then set (aepQueue aep') else {}"
  defines "s' \<equiv> s\<lparr>ksPSpace := ksPSpace s(aepptr \<mapsto> KOAEndpoint aep')\<rparr>"
  assumes koat: "ko_at' aep aepptr s"
  and       vp: "valid_pspace' s"
  and      cp: "cmap_relation (map_to_aeps (ksPSpace s)) (cslift t) Ptr (casync_endpoint_relation (cslift t))"
  and      srs: "sym_refs (state_refs_of' s')"
  and     rel: "casync_endpoint_relation (cslift t') aep' async_endpoint"
  and    mpeq: "(cslift t' |` (- (tcb_ptr_to_ctcb_ptr ` qs))) = (cslift t |` (- (tcb_ptr_to_ctcb_ptr ` qs)))"
  shows "cmap_relation (map_to_aeps (ksPSpace s(aepptr \<mapsto> KOAEndpoint aep')))
           (cslift t(Ptr aepptr \<mapsto> async_endpoint)) Ptr
            (casync_endpoint_relation (cslift t'))"
proof -
  from koat have koat': "ko_at' aep' aepptr s'"
    by (clarsimp simp: obj_at'_def s'_def objBitsKO_def ps_clear_def projectKOs)
  
  have aeps':
    "\<And>x. x \<noteq> aepptr \<Longrightarrow> map_to_aeps (ksPSpace s) x =
                         map_to_aeps (ksPSpace s') x"
    unfolding s'_def
    by (fastforce intro: ssubst [OF map_comp_update] simp: projectKO_opt_aep)

  from koat have map_to_ko_atI'':
    "\<And>x y. \<lbrakk> x \<noteq> aepptr; map_to_aeps (ksPSpace s) x = Some y \<rbrakk> \<Longrightarrow> ko_at' y x s'"
    using vp unfolding s'_def
    by (simp add: map_to_ko_at_updI' injectKO_aep objBitsKO_def)

  thus ?thesis using vp srs cp rel mpeq unfolding cmap_relation_def
    apply -
    apply (elim conjE)
    apply (clarsimp elim!: obj_atE' simp: map_comp_update projectKO_opts_defs)
    apply (drule (1) bspec [OF _ domI])
    apply simp
    apply (erule(1) casync_endpoint_relation_aep_queue [OF _ _ koat'])
      apply (erule(1) map_to_ko_atI'')
     apply (fold qs_def, rule mpeq)
    apply assumption
    done
qed

lemma receiveAsyncIPC_enqueue_ccorres_helper:
  "ccorres dc xfdc (valid_pspace'
                and (\<lambda>s. sym_refs ((state_refs_of' s)(aepptr := set queue \<times> {AEPAsync})))
                and st_tcb_at'  (\<lambda>st. isBlockedOnAsyncEvent st \<and>
                                      waitingOnAsyncEP st = aepptr) thread
                and ko_at' (aep::Structures_H.async_endpoint) aepptr
                and K ((aep = IdleAEP \<and> queue = [thread]) \<or>
                       (\<exists>q. aep = WaitingAEP q \<and> thread \<notin> set q \<and>
                            queue = q @ [thread])))
           UNIV hs
           (setAsyncEP aepptr (Structures_H.WaitingAEP queue))
           (\<acute>aep_queue :== CALL aep_ptr_get_queue(aep_Ptr aepptr);;
            (\<acute>aep_queue :== CALL tcbEPAppend(tcb_ptr_to_ctcb_ptr thread,\<acute>aep_queue);;
             (CALL async_endpoint_ptr_set_state(aep_Ptr aepptr, scast AEPState_Waiting);;
              CALL aep_ptr_set_queue(aep_Ptr aepptr,\<acute>aep_queue))))"
  unfolding K_def
  apply (rule ccorres_gen_asm)
  apply (rule ccorres_from_vcg)
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp split del: split_if simp del: comp_def)
  apply (frule cmap_relation_aep)
  apply (erule (1) cmap_relation_ko_atE)
  apply (rule conjI)
   apply (erule h_t_valid_clift)
  apply (frule(1) st_tcb_at_h_t_valid)
  apply (frule st_tcb_at')
  apply (rule impI)
  apply (rule_tac x="init queue" in exI)
  apply (frule(1) ko_at_valid_aep' [OF _ valid_pspace_valid_objs'])
  apply (frule is_aligned_tcb_ptr_to_ctcb_ptr)
  apply (rule conjI)
   apply (rule_tac x=\<sigma> in exI)
   apply (simp add: casync_endpoint_relation_def Let_def)
   apply (case_tac aep, simp_all add: init_def valid_aep'_def)[1]
  apply (subgoal_tac "sym_refs (state_refs_of' (\<sigma>\<lparr>ksPSpace :=
                          ksPSpace \<sigma>(aepptr \<mapsto> KOAEndpoint (WaitingAEP queue))\<rparr>))")
   prefer 2
   apply (clarsimp simp: state_refs_of'_upd ko_wp_at'_def
                         obj_at'_def projectKOs objBitsKO_def)
  apply (subgoal_tac "ko_at' (WaitingAEP queue) aepptr (\<sigma>\<lparr>ksPSpace :=
                          ksPSpace \<sigma>(aepptr \<mapsto> KOAEndpoint (WaitingAEP queue))\<rparr>)")
   prefer 2
   apply (clarsimp simp: obj_at'_def projectKOs objBitsKO_def ps_clear_upd)
  apply (intro conjI impI allI)
    apply (fastforce simp: h_t_valid_clift)
   apply (fastforce simp: h_t_valid_clift)
  apply (case_tac aep, simp_all add: AEPState_Idle_def AEPState_Waiting_def)[1]
   -- "IdleAEP case"
   apply clarsimp
   apply (frule null_ep_queue [simplified comp_def] null_ep_queue)
   apply (simp add: setAsyncEP_def split_def)
   apply (rule bexI [OF _ setObject_eq])
       apply (simp add: rf_sr_def cstate_relation_def Let_def init_def
                        cpspace_relation_def update_aep_map_tos)
       apply (elim conjE)
       apply (intro conjI)
            -- "tcb relation"
            apply (erule ctcb_relation_null_queue_ptrs)
            apply (clarsimp simp: comp_def)
           -- "ep relation"
           apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
           apply simp
           apply (rule cendpoint_relation_aep_queue, assumption+)
             apply (simp add: isWaitingAEP_def)
            apply simp
           apply (frule_tac x=p in map_to_ko_atI2, clarsimp, clarsimp)
           apply (erule(2) map_to_ko_at_updI')
            apply (clarsimp simp: objBitsKO_def)
           apply (clarsimp simp: obj_at'_def projectKOs)
          -- "aep relation"
          apply (rule cpspace_relation_aep_update_aep', assumption+)
           apply (clarsimp simp: casync_endpoint_relation_def Let_def
                                 mask_def [where n=2] AEPState_Waiting_def)
           apply (fastforce simp: tcb_queue_relation'_def is_aligned_neg_mask
                                 valid_aep'_def
                           dest: tcb_queue_relation_next_not_NULL)
          apply (simp add: isWaitingAEP_def)
         -- "queue relation"
         apply (rule cready_queues_relation_null_queue_ptrs, assumption+)
         apply (clarsimp simp: comp_def)
        apply (simp add: carch_state_relation_def)
       apply (simp add: cmachine_state_relation_def)
      apply (simp add: h_t_valid_clift_Some_iff)
     apply (simp add: objBits_simps)
    apply (simp add: objBits_simps)
   apply assumption
  -- "WaitingAEP case"
  apply clarsimp
  apply (frule null_ep_queue [simplified comp_def] null_ep_queue)
  apply (simp add: setAsyncEP_def split_def)
  apply (rule bexI [OF _ setObject_eq])
      apply (simp add: rf_sr_def cstate_relation_def init_def Let_def
                       cpspace_relation_def update_aep_map_tos)
      apply (elim conjE)
      apply (intro conjI)
           -- "tcb relation"
           apply (erule ctcb_relation_null_queue_ptrs)
           apply (clarsimp simp: comp_def)
          -- "ep relation"
          apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
          apply simp
          apply (rule cendpoint_relation_aep_queue, assumption+)
            apply (simp add: isWaitingAEP_def)
           apply simp
          apply (frule_tac x=p in map_to_ko_atI2, clarsimp, clarsimp)
          apply (erule(2) map_to_ko_at_updI')
           apply (clarsimp simp: objBitsKO_def)
          apply (clarsimp simp: obj_at'_def projectKOs)
         -- "aep relation"
         apply (rule cpspace_relation_aep_update_aep', assumption+)
          apply (clarsimp simp: casync_endpoint_relation_def Let_def
                                mask_def [where n=2] AEPState_Waiting_def)
          apply (fastforce simp: tcb_queue_relation'_def is_aligned_neg_mask)
         apply (simp add: isWaitingAEP_def)
        -- "queue relation"
        apply (rule cready_queues_relation_null_queue_ptrs, assumption+)
        apply (clarsimp simp: comp_def)
       apply (simp add: carch_state_relation_def)
      apply (simp add: cmachine_state_relation_def)
     apply (simp add: h_t_valid_clift_Some_iff)
    apply (simp add: objBits_simps)
   apply (simp add: objBits_simps)
  apply assumption
  done

lemma receiveAsyncIPC_ccorres [corres]:
  "ccorres dc xfdc (invs' and valid_cap' cap and st_tcb_at' simple' thread
                    and sch_act_not thread
                    and (\<lambda>s. \<forall>d p. thread \<notin> set (ksReadyQueues s (d, p)))
                    and K (isAsyncEndpointCap cap))
     (UNIV \<inter> \<lbrace>\<acute>thread = tcb_ptr_to_ctcb_ptr thread\<rbrace>
           \<inter> \<lbrace>ccap_relation cap \<acute>cap\<rbrace>) hs
     (receiveAsyncIPC thread cap)
     (Call receiveAsyncIPC_'proc)"
  unfolding K_def
  apply (rule ccorres_gen_asm)
  apply (cinit lift: thread_' cap_')
   apply (rule ccorres_pre_getAsyncEP, rename_tac aep)
   apply (rule_tac xf'=ret__unsigned_long_'
               and val="capAEPPtr cap"
               and R=\<top>
                in ccorres_symb_exec_r_known_rv_UNIV[where R'=UNIV])
      apply vcg
      apply (clarsimp simp: cap_get_tag_isCap isCap_simps)
      apply (frule cap_get_tag_isCap_unfolded_H_cap)
      apply (simp add: cap_async_endpoint_cap_lift ccap_relation_def cap_to_H_def)
     apply ceqv
    apply csymbr
    apply (rule_tac xf'=ret__unsigned_long_'
                and val="case aep of IdleAEP \<Rightarrow> scast AEPState_Idle
                                  | WaitingAEP _ \<Rightarrow> scast AEPState_Waiting
                                  | ActiveAEP _ _ \<Rightarrow> scast AEPState_Active"
                and R="ko_at' aep (capAEPPtr cap)"
                 in ccorres_symb_exec_r_known_rv_UNIV[where R'=UNIV])
       apply (vcg, clarsimp)
       apply (erule(1) cmap_relation_ko_atE [OF cmap_relation_aep])
       apply (clarsimp simp: casync_endpoint_relation_def Let_def typ_heap_simps
                      split: Structures_H.async_endpoint.splits)
      apply ceqv
     apply wpc
       -- "IdleAEP case"
       apply (rule ccorres_cond_true)
       apply (intro ccorres_rhs_assoc)
       apply csymbr
       (* apply (ctac (no_vcg,c_lines 3) add: receiveAsyncIPC_block_ccorres_helper) *)
       apply (rule ccorres_rhs_assoc2)
       apply (rule ccorres_rhs_assoc2)
       apply (rule ccorres_split_nothrow_novcg)
           apply (simp only: )
           apply (rule receiveAsyncIPC_block_ccorres_helper)
          apply ceqv
         apply (simp only: )
         apply (rule_tac aep=IdleAEP in receiveAsyncIPC_enqueue_ccorres_helper)
        apply (simp add: valid_aep'_def)
        apply (wp sts_st_tcb')
        apply (rule_tac Q="\<lambda>rv. ko_wp_at' (\<lambda>x. projectKO_opt x = Some IdleAEP
                                            \<and> projectKO_opt x = (None::tcb option))
                                          (capAEPPtr cap)"
                     in hoare_post_imp)
         apply (clarsimp simp: obj_at'_def ko_wp_at'_def projectKOs)
        apply wp
       apply (clarsimp simp: guard_is_UNIV_def)
      -- "ActiveAEP case"
      apply (rename_tac badge val)
      apply (rule ccorres_cond_false)
      apply (rule ccorres_cond_true)
      apply (intro ccorres_rhs_assoc)
      apply (rule_tac val=badge
                  and xf'=ret__unsigned_long_'
                  and R="ko_at' aep (capAEPPtr cap)"
                   in ccorres_symb_exec_r_known_rv_UNIV [where R'=UNIV])
         apply (vcg, clarsimp)
         apply (erule(1) cmap_relation_ko_atE [OF cmap_relation_aep])
         apply (clarsimp simp: casync_endpoint_relation_def Let_def typ_heap_simps
                        split: Structures_H.async_endpoint.splits)
        apply ceqv
       apply (rule_tac val=val
                   and xf'=unsigned_long_eret_2_'
                   and R="ko_at' aep (capAEPPtr cap)"
                    in ccorres_symb_exec_r_known_rv_UNIV [where R'=UNIV])
          apply (vcg, clarsimp)
          apply (erule(1) cmap_relation_ko_atE [OF cmap_relation_aep])
          apply (clarsimp simp: casync_endpoint_relation_def Let_def typ_heap_simps
                         split: Structures_H.async_endpoint.splits)
         apply ceqv
        apply (ctac(no_vcg))
         apply (rule_tac P="invs' and ko_at' (ActiveAEP badge val) (capAEPPtr cap)"
                     and P'=UNIV
                      in ccorres_from_vcg)
         apply (rule allI, rule conseqPre, vcg)
         apply clarsimp
         apply (frule(1) cmap_relation_ko_atD [OF cmap_relation_aep])
         apply (clarsimp simp: typ_heap_simps setAsyncEP_def)
         apply (rule bexI [OF _ setObject_eq])
             apply (simp add: rf_sr_def cstate_relation_def Let_def
                              cpspace_relation_def update_aep_map_tos)
             apply (elim conjE)
             apply (intro conjI)
               apply (rule cpspace_relation_aep_update_aep, assumption+)
                apply (simp add: casync_endpoint_relation_def Let_def
                                 AEPState_Idle_def mask_def)
               apply simp
              apply (simp add: carch_state_relation_def)
             apply (simp add: cmachine_state_relation_def)
            apply (simp add: h_t_valid_clift_Some_iff)
           apply (simp add: objBits_simps)
          apply (simp add: objBits_simps)
         apply assumption
        apply wp
       apply (clarsimp simp: guard_is_UNIV_def)
      apply (clarsimp simp: guard_is_UNIV_def)
     -- "WaitingAEP case"
     apply (rule ccorres_cond_true)
     apply (intro ccorres_rhs_assoc)
     apply csymbr
     (* apply (ctac (no_vcg,c_lines 3) add: receiveAsyncIPC_block_ccorres_helper) *)
     apply (rule ccorres_rhs_assoc2)
     apply (rule ccorres_rhs_assoc2)
     apply (rule ccorres_split_nothrow_novcg)
         apply (simp only: )
         apply (rule receiveAsyncIPC_block_ccorres_helper)
        apply ceqv
       apply (simp only: )
       apply (rule_tac aep="WaitingAEP list"
                    in receiveAsyncIPC_enqueue_ccorres_helper)
      apply (simp add: valid_aep'_def)
      apply (wp sts_st_tcb')
      apply (rule_tac Q="\<lambda>rv. ko_wp_at' (\<lambda>x. projectKO_opt x = Some (WaitingAEP list)
                                          \<and> projectKO_opt x = (None::tcb option))
                                        (capAEPPtr cap)
                          and K (thread \<notin> set list)"
                   in hoare_post_imp)
       apply (clarsimp simp: obj_at'_def ko_wp_at'_def projectKOs)
      apply wp
     apply (clarsimp simp: guard_is_UNIV_def)
    apply (clarsimp simp: guard_is_UNIV_def AEPState_Active_def
                          AEPState_Waiting_def AEPState_Idle_def)
   apply (clarsimp simp: guard_is_UNIV_def)
  apply clarsimp
  apply (frule(1) ko_at_valid_objs' [OF _ invs_valid_objs'])
   apply (clarsimp simp: projectKO_opt_aep split: kernel_object.split_asm)
  apply (subgoal_tac "capAEPPtr cap \<noteq> thread \<and> state_refs_of' s thread = {}")
   apply (clarsimp simp: valid_obj'_def valid_aep'_def refs_of'_def
                  split: async_endpoint.splits)
     apply (subgoal_tac "state_refs_of' s (capAEPPtr cap) = {}")
      apply (fastforce simp: obj_at'_def is_aligned_neg_mask objBitsKO_def
                            projectKOs invs'_def valid_state'_def st_tcb_at'_def
                            valid_tcb_state'_def ko_wp_at'_def
                            isBlockedOnAsyncEvent_def projectKO_opt_tcb
                      elim: delta_sym_refs
                     split: split_if_asm)
     apply (clarsimp simp: obj_at'_def state_refs_of'_def projectKOs)
    apply (clarsimp simp: invs'_def valid_state'_def st_tcb_at'
                   elim!: st_tcb'_weakenE)
   apply (subgoal_tac "state_refs_of' s (capAEPPtr cap) = (set list) \<times> {AEPAsync} \<and>
                       thread \<notin> (set list)")
    apply (fastforce simp: obj_at'_def is_aligned_neg_mask objBitsKO_def
                          projectKOs invs'_def valid_state'_def st_tcb_at'_def
                          valid_tcb_state'_def ko_wp_at'_def
                          isBlockedOnAsyncEvent_def projectKO_opt_tcb
                    elim: delta_sym_refs
                   split: split_if_asm)
   apply (frule(1) sym_refs_obj_atD' [OF _ invs_sym'])
   apply (clarsimp simp: st_tcb_at'_def ko_wp_at'_def obj_at'_def projectKOs
                  split: split_if_asm)
   apply (drule(1) bspec)+
   apply (case_tac "tcbState obj", simp_all)[1]
  apply (frule(1) st_tcb_idle' [OF invs_valid_idle'], simp)
  apply (clarsimp simp: st_tcb_at'_def obj_at'_def state_refs_of'_def projectKOs
                 split: split_if_asm)
  apply (case_tac "tcbState obj", clarsimp+)[1]
  done

end
end
