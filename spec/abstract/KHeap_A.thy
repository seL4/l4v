(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Functions to access kernel memory.
*)

chapter \<open>Accessing the Kernel Heap\<close>

theory KHeap_A
imports Exceptions_A
begin

text \<open>This theory gives auxiliary getter and setter methods
for kernel objects.\<close>

section "General Object Access"

definition
  touch_objects :: "obj_ref set \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "touch_objects ptrs \<equiv> do
     kh \<leftarrow> gets kheap;
     assert (\<forall>ptr \<in> ptrs. kh ptr \<noteq> None);
     objs \<leftarrow> return {(ptr, obj) | ptr obj. ptr \<in> ptrs \<and> kh ptr = Some obj};
     ranges \<leftarrow> return $ (\<lambda>(ptr, obj). obj_range ptr obj) ` objs;
     do_machine_op $ addTouchedAddresses $ \<Union> ranges
   od"

definition
  touch_object :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "touch_object ptr \<equiv> touch_objects {ptr}"

lemma touch_object_def2:
  "touch_object ptr = do
     kh \<leftarrow> gets kheap;
     assert (kh ptr \<noteq> None);
     obj \<leftarrow> return $ the $ kh ptr;
     do_machine_op $ addTouchedAddresses (obj_range ptr obj)
   od"
  unfolding touch_object_def touch_objects_def
  apply (simp add: split_def)
  apply (rule bind_cong, rule refl)
  apply (rule fun_cong, rule bind_cong, rule refl)
  apply (clarsimp simp: simpler_gets_def assert_def fail_def split: if_split_asm)
  done

definition
  ta_filter :: "bool \<Rightarrow> machine_word set \<Rightarrow> kernel_object \<Rightarrow> obj_ref \<Rightarrow> kernel_object option" where
  "ta_filter apply ta obj ptr \<equiv> if ~apply \<or> obj_range ptr obj \<subseteq> ta then Some obj else None"

abbreviation f_kheap :: "bool \<Rightarrow> 'z::state_ext state \<Rightarrow> obj_ref \<Rightarrow> kernel_object option" where
  "f_kheap apply s \<equiv> kheap s |>> ta_filter apply (touched_addresses (machine_state s))"

lemma f_kheap_to_kheap[simp]:
  "obind (kheap s) (ta_filter False (touched_addresses (machine_state s))) = kheap s"
  apply(rule ext)
  by (clarsimp simp:ta_filter_def obind_def split:option.splits)

lemma f_kheap_to_kheap'[simp]:
  "(case kheap s a of None \<Rightarrow> None
    | Some kobj \<Rightarrow> ta_filter False (touched_addresses (machine_state s)) kobj a) = kheap s a"
  by (clarsimp simp:ta_filter_def split:option.splits)

lemma f_kheap_to_unfiltered_Some [simplified f_kheap_to_kheap]:
  "f_kheap True s ptr = Some obj \<Longrightarrow> f_kheap False s ptr = Some obj"
  by (clarsimp simp:ta_filter_def obind_def split:if_splits option.splits)

definition
  get_object :: "bool \<Rightarrow> obj_ref \<Rightarrow> (kernel_object,'z::state_ext) s_monad"
where
  "get_object ta_f ptr \<equiv> do
     kh \<leftarrow> gets (f_kheap ta_f);
     assert (kh ptr \<noteq> None);
     return $ the $ kh ptr
   od"

definition
  set_object :: "bool \<Rightarrow> obj_ref \<Rightarrow> kernel_object \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "set_object ta_f ptr obj \<equiv> do
     kobj <- get_object ta_f ptr;
     assert (a_type kobj = a_type obj);
     s \<leftarrow> get;
     put (s\<lparr>kheap := kheap s(ptr \<mapsto> obj)\<rparr>);
     touch_object ptr
   od"

abbreviation
  ms_ta_update  :: "(machine_word set \<Rightarrow> machine_word set) \<Rightarrow>
    'a abstract_state_scheme \<Rightarrow> 'a abstract_state_scheme" where
 "ms_ta_update f \<equiv> \<lambda>s. machine_state_update (machine_state.touched_addresses_update f) s"

lemma simpler_do_machine_op_getTouchedAddresses_def:
  "do_machine_op getTouchedAddresses \<equiv> gets (\<lambda>s. machine_state.touched_addresses $ machine_state s)"
  by (clarsimp simp: bind_def do_machine_op_def getTouchedAddresses_def simpler_gets_def
                        simpler_modify_def select_f_def return_def)

lemma machine_state_update_normalise [simp]:
  "s\<lparr>machine_state := f (machine_state s)\<rparr> = machine_state_update f s"
  by simp

lemma simpler_do_machine_op_addTouchedAddresses_def:
  "do_machine_op (addTouchedAddresses S) \<equiv> modify (ms_ta_update ((\<union>) S))"
  by (clarsimp simp: do_machine_op_def bind_def addTouchedAddresses_def simpler_gets_def
                       simpler_modify_def select_f_def return_def)

section "TCBs"

definition
  get_tcb :: "bool \<Rightarrow> obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> tcb option"
where
  "get_tcb ta_f tcb_ref state \<equiv>
   case f_kheap ta_f state tcb_ref of
      None      \<Rightarrow> None
    | Some kobj \<Rightarrow> (case kobj of
        TCB tcb \<Rightarrow> Some tcb
      | _       \<Rightarrow> None)"

definition
  thread_get :: "(tcb \<Rightarrow> 'a) \<Rightarrow> obj_ref \<Rightarrow> ('a,'z::state_ext) s_monad"
where
  "thread_get f tptr \<equiv> do
     tcb \<leftarrow> gets_the $ get_tcb True tptr;
     return $ f tcb
   od"

definition
  thread_set :: "(tcb \<Rightarrow> tcb) \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "thread_set f tptr \<equiv> do
     touch_object tptr;
     tcb \<leftarrow> gets_the $ get_tcb True tptr;
     set_object True tptr $ TCB $ f tcb
   od"

definition
  arch_thread_get :: "(arch_tcb \<Rightarrow> 'a) \<Rightarrow> obj_ref \<Rightarrow> ('a,'z::state_ext) s_monad"
where
  "arch_thread_get f tptr \<equiv> do
     touch_object tptr;
     tcb \<leftarrow> gets_the $ get_tcb True tptr;
     return $ f (tcb_arch tcb)
   od"

definition
  arch_thread_set :: "(arch_tcb \<Rightarrow> arch_tcb) \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "arch_thread_set f tptr \<equiv> do
     touch_object tptr;
     tcb \<leftarrow> gets_the $ get_tcb True tptr;
     set_object True tptr $ TCB $ tcb \<lparr> tcb_arch := f (tcb_arch tcb) \<rparr>
   od"

definition
  get_thread_state :: "obj_ref \<Rightarrow> (thread_state,'z::state_ext) s_monad"
where
  "get_thread_state ref \<equiv> thread_get tcb_state ref"

definition
  get_bound_notification :: "obj_ref \<Rightarrow> (obj_ref option,'z::state_ext) s_monad"
where
  "get_bound_notification ref \<equiv> thread_get tcb_bound_notification ref"

definition
  set_bound_notification :: "obj_ref \<Rightarrow> obj_ref option \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "set_bound_notification ref ntfn \<equiv> do
     touch_object ref;
     tcb \<leftarrow> gets_the $ get_tcb True ref;
     set_object True ref (TCB (tcb \<lparr> tcb_bound_notification := ntfn \<rparr>))
   od"

definition set_thread_state_ext :: "obj_ref \<Rightarrow> unit det_ext_monad" where
  "set_thread_state_ext t \<equiv> do
     touch_object t;
     ts \<leftarrow> get_thread_state t;
     cur \<leftarrow> gets cur_thread;
     action \<leftarrow> gets scheduler_action;
     when (\<not> (runnable ts) \<and> cur = t \<and> action = resume_cur_thread) (set_scheduler_action choose_new_thread)
   od"

definition
  set_thread_state :: "obj_ref \<Rightarrow> thread_state \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "set_thread_state ref ts \<equiv> do
     touch_object ref;
     tcb \<leftarrow> gets_the $ get_tcb True ref;
     set_object True ref (TCB (tcb \<lparr> tcb_state := ts \<rparr>));
     do_extended_op (set_thread_state_ext ref)
   od"

definition
  set_priority :: "obj_ref \<Rightarrow> priority \<Rightarrow> unit det_ext_monad" where
  "set_priority tptr prio \<equiv> do
     tcb_sched_action tcb_sched_dequeue tptr;
     thread_set_priority tptr prio;
     touch_object tptr;
     ts \<leftarrow> get_thread_state tptr;
     when (runnable ts) $ do
       cur \<leftarrow> gets cur_thread;
       if tptr = cur then reschedule_required else possible_switch_to tptr
     od
   od"

definition
  set_mcpriority :: "obj_ref \<Rightarrow> priority \<Rightarrow> (unit, 'z::state_ext) s_monad"  where
  "set_mcpriority ref mcp \<equiv> thread_set (\<lambda>tcb. tcb\<lparr>tcb_mcpriority:=mcp\<rparr>) ref "


section "simple kernel objects"
(* to be used for abstraction unifying kernel objects other than TCB and CNode *)

definition
  partial_inv :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a option)"
where
  "partial_inv f x = (if \<exists>!y. f y = x then Some (THE y. f y = x) else None)"

lemma proj_inj: "inj f \<Longrightarrow> (partial_inv f ko = Some v) = (f v = ko)"
  by (auto simp: partial_inv_def the_equality injD)

lemma inj_Endpoint: "inj Endpoint" by (auto intro: injI)
lemma inj_Notification: "inj Notification"  by (auto intro: injI)

lemmas proj_inj_ep[simp] = proj_inj[OF inj_Endpoint]
lemma proj_ko_type_ep[simp]: "(\<exists>v. partial_inv Endpoint  ko = Some (v::endpoint)) = (a_type ko = AEndpoint)"
  by (cases ko; auto simp: partial_inv_def a_type_def)

lemmas proj_inj_ntfn[simp] = proj_inj[OF inj_Notification]
lemma proj_ko_type_ntfn[simp]:
  "(\<exists>v. partial_inv Notification  ko = Some (v::notification)) = (a_type ko = ANTFN)"
  by (cases ko; auto simp: partial_inv_def a_type_def)


abbreviation
  "is_simple_type \<equiv> (\<lambda>ob. a_type ob \<in> {AEndpoint, ANTFN})"


definition
  get_simple_ko :: "('a \<Rightarrow> kernel_object) \<Rightarrow> obj_ref \<Rightarrow> ('a,'z::state_ext) s_monad"
where
  "get_simple_ko f ptr \<equiv> do
     kobj \<leftarrow> get_object True ptr;
     assert (is_simple_type kobj);
     (case partial_inv f kobj of Some e \<Rightarrow> return e | _ \<Rightarrow> fail)
   od"


definition
  set_simple_ko :: "('a \<Rightarrow> kernel_object) \<Rightarrow> obj_ref \<Rightarrow> 'a \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "set_simple_ko f ptr ep \<equiv> do
     obj \<leftarrow> get_object True ptr;
     assert (is_simple_type obj);
     assert (partial_inv f obj \<noteq> None);
     set_object True ptr (f ep)
   od"



section \<open>Synchronous and Asyncronous Endpoints\<close>


abbreviation
  get_endpoint :: "obj_ref \<Rightarrow> (endpoint,'z::state_ext) s_monad" where
  "get_endpoint \<equiv> get_simple_ko Endpoint"

abbreviation
  set_endpoint :: "obj_ref \<Rightarrow> endpoint \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "set_endpoint \<equiv> set_simple_ko Endpoint"

abbreviation
  get_notification :: "obj_ref \<Rightarrow> (notification,'z::state_ext) s_monad" where
  "get_notification \<equiv> get_simple_ko Notification"

abbreviation
  set_notification :: "obj_ref \<Rightarrow> notification \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "set_notification \<equiv> set_simple_ko Notification"

abbreviation
  ntfn_set_bound_tcb :: "notification \<Rightarrow> obj_ref option \<Rightarrow> notification" where
  "ntfn_set_bound_tcb ntfn t \<equiv> ntfn \<lparr> ntfn_bound_tcb := t \<rparr>"

abbreviation
  ntfn_set_obj :: "notification \<Rightarrow> ntfn \<Rightarrow> notification" where
  "ntfn_set_obj ntfn a \<equiv> ntfn \<lparr> ntfn_obj := a \<rparr>"


section \<open>IRQ State and Slot\<close>

definition
  get_irq_state :: "irq \<Rightarrow> (irq_state,'z::state_ext) s_monad" where
 "get_irq_state irq \<equiv> gets (\<lambda>s. interrupt_states s irq)"

definition
  set_irq_state :: "irq_state \<Rightarrow> irq \<Rightarrow> (unit,'z::state_ext) s_monad" where
 "set_irq_state state irq \<equiv> do
    modify (\<lambda>s. s \<lparr> interrupt_states := (interrupt_states s) (irq := state)\<rparr>);
    do_machine_op $ maskInterrupt (state = IRQInactive) irq
  od"

definition
  get_irq_slot :: "irq \<Rightarrow> (cslot_ptr,'z::state_ext) s_monad" where
 "get_irq_slot irq \<equiv> gets (\<lambda>st. (interrupt_irq_node st irq, []))"

text \<open>Tests whether an IRQ identifier is in use.\<close>
definition
  is_irq_active :: "irq \<Rightarrow> (bool,'z::state_ext) s_monad" where
 "is_irq_active irq \<equiv> liftM (\<lambda>st. st \<noteq> IRQInactive) $ get_irq_state irq"

section "User Context"

text \<open>
  Changes user context of specified thread by running
  specified user monad.
\<close>
definition
  as_user :: "obj_ref \<Rightarrow> 'a user_monad \<Rightarrow> ('a,'z::state_ext) s_monad"
where
  "as_user tptr f \<equiv> do
    touch_object tptr;
    tcb \<leftarrow> gets_the $ get_tcb True tptr;
    uc \<leftarrow> return $ arch_tcb_context_get (tcb_arch tcb);
    (a, uc') \<leftarrow> select_f $ f uc;
    new_tcb \<leftarrow> return $ tcb \<lparr> tcb_arch := arch_tcb_context_set uc' (tcb_arch tcb)\<rparr>;
    set_object True tptr (TCB new_tcb);
    return a
  od"

text \<open>Raise an exception if a property does not hold.\<close>
definition
throw_on_false :: "'e \<Rightarrow> (bool,'z::state_ext) s_monad \<Rightarrow> ('e + unit,'z::state_ext) s_monad" where
"throw_on_false ex f \<equiv> doE v \<leftarrow> liftE f; unlessE v $ throwError ex odE"

end
