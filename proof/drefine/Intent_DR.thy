(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Intent_DR
imports Corres_D
begin

context begin interpretation Arch . (*FIXME: arch_split*)

definition not_idle_thread:: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
  where
  "not_idle_thread x \<equiv> \<lambda>s. x \<noteq> idle_thread s"

(*Some trivial lemmas rule out irq_node and idle_thread*)

lemma ep_not_idle:
  "\<lbrakk>valid_idle s;obj_at is_ep epptr s\<rbrakk> \<Longrightarrow> not_idle_thread epptr s"
  by (clarsimp simp:valid_idle_def obj_at_def is_cap_table_def pred_tcb_at_def is_ep_def not_idle_thread_def)

lemma ntfn_not_idle:
  "\<lbrakk>valid_idle s;obj_at is_ntfn epptr s\<rbrakk> \<Longrightarrow> not_idle_thread epptr s"
  by (clarsimp simp:valid_idle_def obj_at_def is_cap_table_def pred_tcb_at_def is_ntfn_def not_idle_thread_def)

lemma cte_wp_at_zombie_not_idle:
  "\<lbrakk>cte_wp_at ((=) (cap.Zombie ptr' zbits n)) ptr s; invs s\<rbrakk> \<Longrightarrow> not_idle_thread (fst ptr) s"
  "\<lbrakk>cte_wp_at ((=) (cap.Zombie ptr' zbits n)) ptr s; invs s\<rbrakk> \<Longrightarrow> not_idle_thread ptr' s"
  by (auto dest!: zombie_cap_two_nonidles simp: cte_wp_at_caps_of_state not_idle_thread_def)

lemmas tcb_slots = Types_D.tcb_caller_slot_def Types_D.tcb_cspace_slot_def Types_D.tcb_ipcbuffer_slot_def
  Types_D.tcb_pending_op_slot_def Types_D.tcb_replycap_slot_def Types_D.tcb_vspace_slot_def Types_D.tcb_boundntfn_slot_def

(* FIXME: MOVE *)
lemma tcb_cap_casesE:
  assumes cs: "tcb_cap_cases p = Some (gf, sf, restr)"
  and  rules: "\<lbrakk> p = tcb_cnode_index 0; gf = tcb_ctable; sf = tcb_ctable_update; restr = (\<lambda>_ _. \<top>) \<rbrakk> \<Longrightarrow> R"
              "\<lbrakk> p = tcb_cnode_index 1; gf = tcb_vtable; sf = tcb_vtable_update;
                 restr = (\<lambda>_ _. is_valid_vtable_root or ((=) cap.NullCap)) \<rbrakk> \<Longrightarrow> R"
              "\<lbrakk> p = tcb_cnode_index 2; gf = tcb_reply; sf = tcb_reply_update;
                 restr = (\<lambda>t st c. (is_master_reply_cap c \<and> obj_ref_of c = t
                                        \<and> AllowGrant \<in> cap_rights c)
                                    \<or> (halted st \<and> (c = cap.NullCap))) \<rbrakk> \<Longrightarrow> R"
              "\<lbrakk> p = tcb_cnode_index 3; gf = tcb_caller; sf = tcb_caller_update;
                 restr = (\<lambda>_ st. case st of
                                       Structures_A.BlockedOnReceive e data \<Rightarrow>
                                         ((=) cap.NullCap)
                                     | _ \<Rightarrow> is_reply_cap or ((=) cap.NullCap)) \<rbrakk> \<Longrightarrow> R"
              "\<lbrakk> p = tcb_cnode_index 4; gf = tcb_ipcframe; sf = tcb_ipcframe_update; restr =
                                     (\<lambda>_ _. is_nondevice_page_cap or ((=) cap.NullCap)) \<rbrakk> \<Longrightarrow> R"
  shows "R"
  using cs
  unfolding tcb_cap_cases_def
  apply (simp split: if_split_asm del: One_nat_def)
  apply (erule rules, fastforce+)+
  done

lemma tcb_cnode_index_def2:
  "n < 8 \<Longrightarrow> tcb_cnode_index n = bin_to_bl 3 (int n)"
  unfolding tcb_cnode_index_def to_bl_def
  by (simp add: uint_nat unat_of_nat)

lemma bl_to_bin_tcb_cnode_index:
  "n < 8 \<Longrightarrow> nat (bl_to_bin (tcb_cnode_index n)) = n"
  unfolding tcb_cnode_index_def
  by (simp add: unat_of_nat)

(* LIFT LEMMAS:
   Lift the property from abstract spec to capdl model
 *)

lemma transform_objects_kheap:
  "\<lbrakk> kheap s p = Some ko; p \<noteq> idle_thread s \<rbrakk>
     \<Longrightarrow> transform_objects s p = Some (transform_object (machine_state s) p (ekheap s p) ko)"
  unfolding transform_objects_def
  by (simp)

lemma transform_objects_tcb:
  "\<lbrakk> get_tcb ptr s = Some tcb; get_etcb ptr s = Some etcb; ptr \<noteq> idle_thread s\<rbrakk>
    \<Longrightarrow> transform_objects s ptr = Some (transform_tcb (machine_state s) ptr tcb etcb)"
  by (clarsimp dest!: get_tcb_SomeD simp: get_etcb_def transform_objects_def)

lemma opt_object_tcb:
  "\<lbrakk> get_tcb ptr s = Some tcb; get_etcb ptr s = Some etcb; ptr \<noteq> idle_thread s \<rbrakk> \<Longrightarrow>
  cdl_objects (transform s) ptr = Some (transform_tcb (machine_state s) ptr tcb etcb)"
  by (clarsimp simp: transform_def transform_objects_tcb dest!: get_tcb_SomeD)

abbreviation
  "tcb_abstract_slots \<equiv> {tcb_caller_slot, tcb_cspace_slot, tcb_ipcbuffer_slot, tcb_replycap_slot, tcb_vspace_slot}"

lemma tcb_cap_cases_slot_simps[simp]:
  "tcb_cap_cases (tcb_cnode_index tcb_cspace_slot) = Some (tcb_ctable, tcb_ctable_update, (\<lambda>_ _. \<top>))"
  "tcb_cap_cases (tcb_cnode_index tcb_vspace_slot) =
      Some (tcb_vtable, tcb_vtable_update, (\<lambda>_ _. is_valid_vtable_root or ((=) cap.NullCap)))"
  "tcb_cap_cases (tcb_cnode_index tcb_replycap_slot) =
      Some (tcb_reply, tcb_reply_update,
            (\<lambda>t st c. (is_master_reply_cap c \<and> obj_ref_of c = t \<and> AllowGrant \<in> cap_rights c)
                       \<or> (halted st \<and> (c = cap.NullCap))))"
  "tcb_cap_cases (tcb_cnode_index tcb_caller_slot) =
      Some (tcb_caller, tcb_caller_update,
             (\<lambda>_ st. case st of
               Structures_A.BlockedOnReceive e data \<Rightarrow>
                 ((=) cap.NullCap)
             | _ \<Rightarrow> is_reply_cap or ((=) cap.NullCap)))"
  "tcb_cap_cases (tcb_cnode_index tcb_ipcbuffer_slot) =
      Some (tcb_ipcframe, tcb_ipcframe_update, (\<lambda>_ _. is_nondevice_page_cap or ((=) cap.NullCap)))"
  by (simp add: tcb_slots)+

lemma opt_cap_tcb:
  "\<lbrakk> get_tcb y s = Some tcb; (\<exists>etcb. get_etcb y s = Some etcb); y \<noteq> idle_thread s \<rbrakk> \<Longrightarrow>
  opt_cap (y, sl) (transform s) =
  (if sl \<in> tcb_abstract_slots then (option_map (\<lambda>(getF, _, _). transform_cap (getF tcb)) (tcb_cap_cases (tcb_cnode_index sl)))
  else (if sl = tcb_pending_op_slot then (Some (infer_tcb_pending_op y (tcb_state tcb)))
   else (if sl = tcb_boundntfn_slot then (Some  (infer_tcb_bound_notification (tcb_bound_notification tcb))) else None)))"
  by (fastforce simp add: opt_cap_def KHeap_D.slots_of_def opt_object_tcb object_slots_def transform_tcb_def tcb_slots)

lemma cdl_objects_cnode:
  "\<lbrakk> kheap s' y = Some (CNode sz obj'); valid_idle s' ; sz \<noteq> 0\<rbrakk>
    \<Longrightarrow> cdl_objects (transform s') y =
    Some (cdl_object.CNode \<lparr>cdl_cnode_caps = transform_cnode_contents sz obj', cdl_cnode_size_bits = sz\<rparr>)"
  apply (subgoal_tac "y \<noteq> idle_thread s'")
  apply (auto simp:obj_at_def is_cap_table_def valid_idle_def pred_tcb_at_def
                   transform_def transform_objects_def
             split:nat.split)
  done

lemma cdl_objects_irq_node:
  "\<lbrakk> kheap s' y = Some (CNode 0 obj'); valid_idle s' \<rbrakk>
    \<Longrightarrow> cdl_objects (transform s') y =
    Some (cdl_object.IRQNode \<lparr>cdl_irq_node_caps = transform_cnode_contents 0 obj'\<rparr>)"
  apply (subgoal_tac "y \<noteq> idle_thread s'")
  apply (auto simp:obj_at_def is_cap_table_def valid_idle_def pred_tcb_at_def
         transform_def transform_objects_def)
  done

lemma transform_objects_cnode:
  "\<lbrakk> kheap s' y = Some (CNode sz obj'); valid_idle s'; sz \<noteq> 0\<rbrakk> \<Longrightarrow> transform_objects s' y =
    Some (cdl_object.CNode \<lparr>cdl_cnode_caps = transform_cnode_contents sz obj', cdl_cnode_size_bits = sz\<rparr>)"
  apply (subgoal_tac "y \<noteq> idle_thread s'")
  apply (simp add: transform_objects_def)
  apply (clarsimp simp add: valid_idle_def obj_at_def pred_tcb_at_def split:nat.split)+
  done

lemma transform_objects_irq_node:
  "\<lbrakk> kheap s' y = Some (CNode 0 obj'); valid_idle s'\<rbrakk> \<Longrightarrow> transform_objects s' y =
    Some (cdl_object.IRQNode \<lparr>cdl_irq_node_caps = transform_cnode_contents 0 obj'\<rparr>)"
  apply (subgoal_tac "y \<noteq> idle_thread s'")
  apply (simp add: transform_objects_def)
  apply (clarsimp simp add: valid_idle_def obj_at_def pred_tcb_at_def split:nat.split)+
  done

lemmas lift_simp =
  transform_objects_tcb transform_objects_cnode transform_objects_kheap cdl_objects_cnode
  opt_cap_tcb opt_object_tcb

lemma transform_objects_update_other:
  "\<lbrakk> kh ptr = Some ko; caps_of_object ko = caps_of_object ko'; a_type ko = a_type ko'; ref \<noteq> ptr \<rbrakk>
  \<Longrightarrow> transform_objects (update_kheap (kh(ptr \<mapsto> ko')) s) ref = transform_objects (update_kheap kh s) ref"
  unfolding transform_objects_def
  by (cases ref, simp_all add: restrict_map_def caps_of_state_update_same_caps
                               cap_installed_at_irq_def map_add_def)

lemma caps_of_object_update_state [simp]:
  "(\<lambda>n. map_option (\<lambda>(f, _). f (tcb_state_update stf tcb)) (tcb_cap_cases n)) =
   (\<lambda>n. map_option (\<lambda>(f, _). f tcb) (tcb_cap_cases n))"
  apply (rule ext)
  apply (simp add: tcb_cap_cases_def split: if_split)
  done

lemma caps_of_object_update_boundntfn [simp]:
  "(\<lambda>n. map_option (\<lambda>(f, _). f (tcb_bound_notification_update stf tcb)) (tcb_cap_cases n)) =
   (\<lambda>n. map_option (\<lambda>(f, _). f tcb) (tcb_cap_cases n))"
  apply (rule ext)
  apply (simp add: tcb_cap_cases_def split: if_split)
  done

lemma caps_of_object_update_context [simp]:
  "(\<lambda>n. map_option (\<lambda>(f, _). f (tcb_arch_update (tcb_context_update stf) tcb)) (tcb_cap_cases n)) =
   (\<lambda>n. map_option (\<lambda>(f, _). f tcb) (tcb_cap_cases n))"
  apply (rule ext)
  apply (simp add: tcb_cap_cases_def split: if_split)
  done

definition
  generates_pending :: "Structures_A.thread_state \<Rightarrow> bool"
where
  "generates_pending st \<equiv> case st of
            Structures_A.BlockedOnReceive ptr payload \<Rightarrow> True
          | Structures_A.BlockedOnSend ptr payload \<Rightarrow> True
          | Structures_A.BlockedOnReply \<Rightarrow> True
          | Structures_A.BlockedOnNotification ptr \<Rightarrow> True
          | Structures_A.Restart                 \<Rightarrow> True
          | Structures_A.Running                 \<Rightarrow> True
          | _ \<Rightarrow> False"

lemmas generates_pending_simps [simp]  = generates_pending_def [split_simps Structures_A.thread_state.split]

lemmas infer_tcb_pending_op_simps [simp]  = infer_tcb_pending_op_def [split_simps Structures_A.thread_state.split]

(* Is actually iff *)
lemma not_generates_pending_is_null:
  "\<not> generates_pending st \<Longrightarrow> (infer_tcb_pending_op ptr st = Types_D.NullCap)"
  unfolding generates_pending_def infer_tcb_pending_op_def
  by (simp split: Structures_A.thread_state.splits)

lemma transform_tcb_upd_state_no_pending:
  "\<lbrakk> \<not> generates_pending (tcb_state tcb); \<not> generates_pending (f (tcb_state tcb)) \<rbrakk>
  \<Longrightarrow> transform_tcb ms ptr (tcb_state_update f tcb) etcb = transform_tcb ms ptr tcb etcb"
  unfolding transform_tcb_def
  by (simp add: not_generates_pending_is_null cong: transform_full_intent_cong)

lemmas transform_objects_tcb_state =
  transform_objects_update_kheap_same_caps transform_objects_update_same
  transform_tcb_upd_state_no_pending

lemma transform_objects_dummy_set_original_cap [simp]:
  "transform_objects (b\<lparr>is_original_cap := x\<rparr>) = transform_objects b"
  by (clarsimp simp: cap_installed_at_irq_def transform_objects_def)

lemma transform_objects_dummy_update_cdt [simp]:
  "transform_objects (b\<lparr>cdt := x\<rparr>) = transform_objects b"
  by (clarsimp simp: cap_installed_at_irq_def transform_objects_def)

lemma update_tcb_cxt_eq_dupdate_tcb_intent:
  "\<lbrakk>
    cdl_objects (transform b) y = Some (Tcb t);
    kheap b y = Some (TCB obj);
    \<exists>etcb'. ekheap b y = Some etcb';
    obj' = tcb_arch_update (arch_tcb_context_set cxt) obj;
    not_idle_thread y b;
    intent = transform_full_intent (machine_state (update_kheap ((kheap b)(y\<mapsto>(TCB obj'))) b)) y obj'
   \<rbrakk>
    \<Longrightarrow> dupdate_cdl_object y (Tcb (dupdate_tcb_intent intent t)) (transform b)
    = transform (update_kheap ((kheap b)(y\<mapsto> (TCB obj'))) b)"
  apply (clarsimp simp:transform_def transform_current_thread_def
                       not_idle_thread_def transform_objects_def)
  apply (rule ext, clarsimp)
  apply (rule conjI)
   apply (clarsimp simp:restrict_map_Some_iff)
   apply (clarsimp simp:transform_tcb_def restrict_map_def map_add_def)
  apply (clarsimp simp:transform_tcb_def restrict_map_def map_add_def)
  done

lemma duplicate_corrupt_tcb_intent:
  "do corrupt_tcb_intent epptr; corrupt_tcb_intent epptr od = corrupt_tcb_intent epptr"
  apply (clarsimp simp:bind_def)
  apply (rule ext)
  apply (clarsimp simp:split_def)
  apply (rule prod_eqI)
   apply (rule set_eqI)
   apply clarsimp
   apply (auto simp:corrupt_tcb_intent_def update_thread_def select_def gets_the_def
          return_def fail_def gets_def get_def assert_opt_def bind_def
          put_def modify_def KHeap_D.set_object_def split_def
          split:option.splits cdl_object.splits)[1]
  apply clarsimp
  apply (rule iffI)
   by (auto simp: corrupt_tcb_intent_def update_thread_def select_def gets_the_def
                  return_def fail_def gets_def get_def assert_opt_def bind_def
                  put_def modify_def KHeap_D.set_object_def split_def
           split: option.splits cdl_object.splits)

(* Corrupting a register several times is the same as corrupting it once. *)
lemma corres_corrupt_tcb_intent_dupl:
  "\<lbrakk> dcorres dc P P' (do corrupt_tcb_intent x; corrupt_tcb_intent x od) g \<rbrakk> \<Longrightarrow>
   dcorres dc P P' (corrupt_tcb_intent x) g"
  by (subst duplicate_corrupt_tcb_intent[symmetric], simp)

(*
 * Doing nothing at the abstract level corresponds to corrupting a TCB intent.
 * (In particular, it is the "null" corruption.)
 *)
lemma corres_corrupt_tcb_intent_return:
  "dcorres dc \<top> (tcb_at ptr and not_idle_thread ptr and valid_etcbs) (corrupt_tcb_intent ptr) (return x)"
  supply option.case_cong[cong]
  apply (clarsimp simp: corres_underlying_def return_def corrupt_tcb_intent_def update_thread_def
                        select_def gets_the_def fail_def gets_def get_def assert_opt_def bind_def
                        put_def modify_def KHeap_D.set_object_def)
  apply (clarsimp split: option.splits
                  simp: transform_def tcb_at_def transform_objects_def not_idle_thread_def
                  dest!: get_tcb_SomeD)
   apply (drule(1) valid_etcbs_tcb_etcb)
   apply (clarsimp)
  apply (force simp: transform_def transform_tcb_def transform_objects_def not_idle_thread_def
                     tcb_at_def obj_at_def
               split: cdl_object.splits)
  done

lemma dcorres_set_object_tcb:
  "\<lbrakk> \<exists>etcb'. (transform_tcb (machine_state s') p' tcb' etcb' = Tcb tcb \<and> ekheap s' p' = Some etcb');
     p' \<noteq> idle_thread s'; kheap s' p' \<noteq> None; ekheap s' p' \<noteq> None \<rbrakk> \<Longrightarrow>
  dcorres dc ((=) (transform s')) ((=) s')
           (KHeap_D.set_object p' (Tcb tcb ))
           (KHeap_A.set_object p' (TCB tcb'))"
  apply (clarsimp simp: corres_underlying_def set_object_def get_object_def in_monad)
  apply (clarsimp simp: KHeap_D.set_object_def simpler_modify_def)
  apply (clarsimp simp: transform_def transform_current_thread_def)
  apply (clarsimp simp: transform_objects_def)
  apply (rule ext)
  apply clarsimp
  apply (clarsimp simp: option_map_def restrict_map_def map_add_def)
  done

lemma set_cxt_none_det_intent_corres':
  "\<lbrakk>kheap s' y = Some (TCB obj'); ekheap s' y \<noteq> None;  valid_idle s';not_idle_thread y s'\<rbrakk>
         \<Longrightarrow> dcorres dc ((=) (transform s')) ((=) s')
             (corrupt_tcb_intent y)
             (KHeap_A.set_object y (TCB (tcb_arch_update f obj')))"
  apply (clarsimp simp:bind_assoc corrupt_tcb_intent_def get_thread_def gets_def gets_the_def)
  apply (rule corres_guard_imp)
    apply (rule_tac P="(=)(transform s')" and Q="(=) s'"
       and x="transform_full_intent (machine_state (update_kheap ((kheap s')(y\<mapsto>(TCB (tcb_arch_update f obj')))) s'))
       y (tcb_arch_update f obj')"
       in select_pick_corres)
    apply (clarsimp simp:update_thread_def get_object_def
       gets_the_def gets_def bind_assoc)
    apply (rule dcorres_absorb_get_l)
    apply (subgoal_tac "\<exists>t f. cdl_objects (transform s') y = Some (Tcb t)")
     apply (clarsimp simp:assert_opt_def)
     apply (rule dcorres_set_object_tcb)
       apply (clarsimp simp:transform_tcb_def
         transform_def transform_objects_def not_idle_thread_def)
      apply (clarsimp simp:not_idle_thread_def)
     apply simp
     apply simp
    apply (clarsimp simp:transform_def not_idle_thread_def
      transform_objects_def transform_tcb_def)
   apply clarsimp
  apply clarsimp
done

lemma set_cxt_none_det_intent_corres:
  "\<lbrakk>kheap s' y = Some (TCB obj'); ekheap s' y \<noteq> None;  valid_idle s';not_idle_thread y s'\<rbrakk>
         \<Longrightarrow> dcorres dc ((=) (transform s')) ((=) s')
             (corrupt_tcb_intent y)
             (KHeap_A.set_object y (TCB (tcb_arch_update (arch_tcb_context_set cxt) obj')))"
  by (rule set_cxt_none_det_intent_corres')

lemma set_message_info_corres:
  "dcorres dc \<top> (valid_idle and not_idle_thread y and valid_etcbs) (corrupt_tcb_intent y)
             (set_message_info y m)"
  apply (clarsimp simp:set_message_info_def)
  apply (clarsimp simp:as_user_def setRegister_def)
  apply (rule dcorres_absorb_gets_the)
  apply (clarsimp simp:get_tcb_def split:option.splits Structures_A.kernel_object.splits)
  apply (subst modify_def[unfolded bind_def]|clarsimp simp:get_def put_def)+
  apply (frule_tac ptr=y and tcb=obj' in valid_etcbs_tcb_etcb, clarsimp, clarsimp)
  apply (clarsimp simp:select_f_def bind_def arch_tcb_update_aux3)
  apply (rule corres_guard_imp)
  apply (erule set_cxt_none_det_intent_corres)
   apply (clarsimp simp: valid_def get_tcb_def lift_simp not_idle_thread_def transform_tcb_def
                   split: option.splits Structures_A.kernel_object.splits)+
  done

lemma corrupt_tcb_intent_as_user_corres:
  "dcorres dc \<top> (valid_idle and not_idle_thread y and valid_etcbs)
     (corrupt_tcb_intent y) (as_user y t)"
  apply (clarsimp simp:as_user_def)
  apply (rule dcorres_absorb_gets_the)
  apply (clarsimp simp:get_tcb_def arch_tcb_update_aux3
                  split:option.splits Structures_A.kernel_object.splits)
  apply (rule corres_symb_exec_r)
     apply clarsimp
     apply (rule corres_dummy_return_l)
     apply (rule corres_underlying_split)
        apply (drule(1) valid_etcbs_tcb_etcb)
        apply (rule set_cxt_none_det_intent_corres; simp)
       apply (rule corres_return_trivial)
      apply wpsimp+
  done

lemmas set_register_corres = corrupt_tcb_intent_as_user_corres

lemma dummy_corrupt_tcb_intent_corres:
  "dcorres dc \<top> (tcb_at y and valid_idle and not_idle_thread y and valid_etcbs)
    (corrupt_tcb_intent y) (return a)"
  apply (simp add:corrupt_tcb_intent_def not_idle_thread_def)
  apply (rule dcorres_expand_pfx, clarsimp)
  apply (clarsimp simp:tcb_at_def)
  apply (drule(1) valid_etcbs_get_tcb_get_etcb, clarsimp)
  apply (rule corres_guard_imp)
    apply (rule_tac P="(=)(transform s')" and Q="(=) s'" and
                    x="transform_full_intent (machine_state s') y tcb" in select_pick_corres)
    apply (clarsimp simp:update_thread_def gets_the_def gets_def bind_assoc)
    apply (rule dcorres_absorb_get_l)
    apply (clarsimp simp:opt_object_tcb assert_opt_def transform_tcb_def)
    apply (clarsimp simp:KHeap_D.set_object_def get_def put_def modify_def assert_def bind_def return_def)
    apply (subst corres_singleton)
    apply (clarsimp simp:dc_def)
    apply (clarsimp simp:transform_def)
    apply (rule ext)
    apply (clarsimp simp: restrict_map_Some_iff transform_objects_def
                   split: option.splits dest!:get_tcb_SomeD get_etcb_SomeD)
    apply (clarsimp simp: transform_tcb_def)
   apply (clarsimp simp:transform_def)+
  done

lemma neq_Nil_conv':
  "(a \<noteq> []) =  (\<exists>h x. a = h@[x])"
  by (auto | drule append_butlast_last_id)+

lemma not_idle_thread_as_usr[wp]:
  "\<lbrace>not_idle_thread y\<rbrace> as_user p q \<lbrace>\<lambda>rv. not_idle_thread y\<rbrace>"
  by (simp add:not_idle_thread_def,wp)

lemma set_registers_corres:
  "dcorres dc \<top> (tcb_at y and valid_idle and not_idle_thread y and valid_etcbs)
  (corrupt_tcb_intent y)
  (mapM (%r. do v \<leftarrow> as_user thread (getRegister r);
                as_user y (setRegister r v)
             od) (x)
  )"
  apply (induct_tac "x")
   apply (clarsimp simp:bind_assoc mapM_def sequence_def)
   apply (rule corres_guard_imp)
     apply (rule dummy_corrupt_tcb_intent_corres[unfolded dc_def])
    apply simp+
  apply (clarsimp simp:mapM_def)
  apply (subst duplicate_corrupt_tcb_intent[symmetric])
  apply (clarsimp simp:sequence_def)
  apply (rule_tac Q'="%r. tcb_at y and valid_idle and not_idle_thread y and valid_etcbs"
                  in corres_split_forwards' [where Q="%r. \<top>"])
     apply (rule corres_symb_exec_r)
        apply (rule set_register_corres)
       apply (wp|simp)+
  apply (simp add:bind_assoc dc_def[symmetric])
  apply (rule corres_dummy_return_l)
  apply (rule corres_split_forwards' [where r'="dc" and Q="%x. \<top>" and Q'="%x. \<top>"])
     apply (rule corres_guard_imp)
       apply simp+
  done

lemma set_mrs_corres_no_recv_buffer:
  "dcorres dc \<top> (valid_idle and not_idle_thread y and valid_etcbs)
     (corrupt_tcb_intent y) (set_mrs y None msg)"
  unfolding set_mrs_def
  apply (subst arch_tcb_update_aux3)
  apply simp
  apply (rule dcorres_absorb_gets_the, clarsimp)
  apply (drule(1) valid_etcbs_get_tcb_get_etcb)
  apply (rule corres_dummy_return_l)
  apply (rule corres_split_forwards' [where Q'="%x. \<top>" and Q="%x. \<top>"])
     apply (rule set_cxt_none_det_intent_corres')
        apply (simp add:get_tcb_def get_etcb_def
                  split:option.splits Structures_A.kernel_object.splits
               | wp)+
  done

lemma corrupt_intents_dup: "corrupt_intents f bufp (corrupt_intents g bufp s) = corrupt_intents f bufp s"
  apply (clarsimp simp:corrupt_intents_def)
  apply (cases s)
  apply clarsimp
  apply (rule ext)
  apply (case_tac "cdl_objects x")
   apply (clarsimp simp:map_add_def)+
  apply (clarsimp simp: tcb_ipcframe_id_def split:cdl_object.splits)
  done

lemma corrupt_frame_duplicate: "(do _ \<leftarrow> corrupt_frame bufp; corrupt_frame bufp od) = (corrupt_frame bufp)"
  apply (rule ext)
  apply (clarsimp simp:corrupt_frame_def simpler_modify_def bind_assoc)
  apply (clarsimp simp:bind_def select_def)
  apply (force simp: corrupt_intents_dup)
done

lemma dcorres_dummy_corrupt_frame: "dcorres dc \<top> valid_etcbs
  (corrupt_frame buf) (return a)"
  apply (simp add:corrupt_frame_def)
  apply (rule dcorres_expand_pfx)
  apply (rule corres_guard_imp)
    apply (rule_tac P="(=)(transform s')" and Q="(=) s'"
      and x = "\<lambda>x. transform_full_intent (machine_state s') x (the (get_tcb x s'))"  in select_pick_corres)
    apply (clarsimp simp:get_def put_def modify_def assert_def bind_def return_def)
    apply (subst corres_singleton)
    apply (clarsimp simp:corrupt_intents_def Let_def transform_def transform_objects_def)
    apply (rule ext)
    apply (clarsimp split:option.splits simp:restrict_map_def map_add_def)
    apply (clarsimp simp:map_add_def split:option.splits cdl_object.split_asm if_splits)
    apply (clarsimp simp:transform_object_def split:Structures_A.kernel_object.splits arch_kernel_obj.splits nat.splits)
    apply (drule(1) valid_etcbs_tcb_etcb)
    apply (clarsimp simp:get_tcb_rev get_etcb_rev transform_tcb_def)
   apply (clarsimp split:option.splits simp:map_add_def)+
  done

definition empty_when_fail :: "('s,'a) nondet_monad \<Rightarrow> bool"
where     "empty_when_fail m \<equiv> \<forall>s. snd (m s)\<longrightarrow> fst (m s) = {}"

lemma empty_when_fail_return:
  "empty_when_fail (return x)"
  by (clarsimp simp:return_def empty_when_fail_def)

lemma wp_no_fail_spec:
  "\<lbrakk>empty_when_fail f ; no_fail ((=) s) f \<longrightarrow> \<lbrace>(=) s\<rbrace> f \<lbrace>Q\<rbrace>\<rbrakk>\<Longrightarrow>\<lbrace>(=) s\<rbrace> f \<lbrace>Q\<rbrace>"
  apply (case_tac "no_fail ((=) s) f")
    apply simp
  apply clarsimp
  apply (simp add:no_fail_def valid_def empty_when_fail_def)
done

definition det_spec :: "('s \<Rightarrow> bool) \<Rightarrow> ('s\<Rightarrow>('b\<times>'s) set\<times> bool) \<Rightarrow> bool"
where "det_spec P f \<equiv> \<forall>s. P s \<longrightarrow> (\<exists>r. f s = ({r},False))"

definition weak_det_spec :: "('s \<Rightarrow> bool) \<Rightarrow> ('s\<Rightarrow>('b\<times>'s) set\<times> bool) \<Rightarrow> bool"
where "weak_det_spec P f \<equiv> no_fail P f \<longrightarrow> det_spec P f"

lemma empty_when_fail_compose:
assumes Q:"\<And>r. empty_when_fail (b r)"
assumes P:"empty_when_fail a"
shows "(\<And>P. weak_det_spec P a) \<Longrightarrow> empty_when_fail (a>>=b)"
  apply (clarsimp simp:empty_when_fail_def)
  apply (case_tac "snd (a s)")
    apply (clarsimp simp:bind_def)
    using P
    apply (clarsimp simp:empty_when_fail_def)
  apply (clarsimp simp:bind_def)
  apply (clarsimp simp:weak_det_spec_def no_fail_def)
  apply (drule_tac x = "(=) s" in meta_spec)
  apply (clarsimp simp:det_spec_def)
  using Q
  apply (simp add: empty_when_fail_def)
done

(*
  The following lemma allows use to talking about the return value of a weak_det_spec function in wp
*)

lemma weak_det_spec_ret:
assumes no_fail_det:   "weak_det_spec ((=) s) f"
assumes op_eq: "g s = f s"
shows "\<lbrakk> x = the (evalMonad g s); empty_when_fail f\<rbrakk> \<Longrightarrow> \<lbrace>(=) s\<rbrace> f \<lbrace>\<lambda>r s. r = x\<rbrace>"
  apply (rule wp_no_fail_spec)
    apply clarsimp+
  apply (clarsimp simp:op_eq evalMonad_def weak_det_spec_def  empty_when_fail_def)+
  apply (drule_tac x = s in spec)
    apply (clarsimp simp:|rule conjI)+
    apply (clarsimp simp:valid_def)
  apply (clarsimp)
  using no_fail_det[unfolded weak_det_spec_def]
  apply (clarsimp simp:det_spec_def valid_def)
done

lemma wp_spec:
assumes "P s \<Longrightarrow> \<lbrace>(=) s\<rbrace> f \<lbrace>Q\<rbrace>"
shows "\<lbrace>(=) s and P\<rbrace> f \<lbrace>Q\<rbrace>"
  using assms
  by (clarsimp simp:valid_def)

lemma det_compose:
  "\<lbrakk>det_spec P a;\<And>r. det_spec (Q r) (b r); \<lbrace>P\<rbrace>a\<lbrace>Q\<rbrace>\<rbrakk>\<Longrightarrow> det_spec P (a>>=b)"
  by (fastforce simp: det_spec_def bind_def valid_def)

lemma no_fail_compose_imp:
  "\<lbrakk>no_fail P (a>>= b)\<rbrakk> \<Longrightarrow> no_fail P a \<and> (\<exists>Q. (\<lbrace>P\<rbrace>a\<lbrace>Q\<rbrace> \<and> (\<forall>r. no_fail (Q r) (b r))))"
  apply (clarsimp simp: bind_def no_fail_def)
  apply (rule_tac x = "\<lambda>rv s. \<exists>s'. P s'\<and> (rv,s) \<in> fst (a s')" in exI)
  apply (auto simp:valid_def)
done

lemma mapM_load_word_offs_do_machine_op:
  "mapM (load_word_offs ptr) list
     = do_machine_op (mapM loadWord (map (\<lambda>offs. ptr + of_nat (offs * word_size)) list))"
  apply (subst submonad_mapM[OF submonad_do_machine_op submonad_do_machine_op])
   apply (simp add: loadWord_def empty_fail_cond)
  apply (simp add: load_word_offs_def[abs_def] mapM_map_simp o_def)
  done

lemma det_spec_return:
  "det_spec P (return x)"
  by (clarsimp simp:return_def det_spec_def)

lemma det_spec_get:
  "det_spec P (get)"
  by (clarsimp simp:get_def det_spec_def)

lemma det_spec_put:
  "det_spec P (put t)"
  by (clarsimp simp:put_def det_spec_def)

lemma det_spec_modify:
  "det_spec P (modify f)"
  by (clarsimp simp:simpler_modify_def det_spec_def)

lemma det_spec_gets:
  "det_spec P (gets f)"
  apply (clarsimp simp:gets_def)
  apply (rule det_compose)
  apply (rule det_spec_get)
  apply (rule det_spec_return)
  apply (fastforce simp:get_def valid_def)
done

lemma det_spec_select_f:
  "\<lbrakk>P a; det_spec P f\<rbrakk> \<Longrightarrow> det_spec Q (select_f (f a))"
  by (fastforce simp: select_f_def det_spec_def)

lemma det_imply_weak_det:
  "det_spec P a \<Longrightarrow> weak_det_spec P a"
  by (simp add:weak_det_spec_def)

lemma weak_det_specD:
  "\<lbrakk>weak_det_spec P a;no_fail P a\<rbrakk> \<Longrightarrow> det_spec P a"
  by (clarsimp simp:weak_det_spec_def)

lemma weak_det_spec_mapM:
  assumes single:
    "\<And>r P. weak_det_spec P (g r)"
  shows
    "weak_det_spec Q (mapM g ls)"
    proof (induct ls arbitrary:Q)
      case Nil
      show ?case
        apply (clarsimp simp:mapM_def sequence_def det_spec_return)
        apply (rule det_imply_weak_det[OF det_spec_return])
        done
    next
      case (Cons x xs)
      show ?case
        using Cons.hyps
        apply (clarsimp simp:mapM_Cons weak_det_spec_def)
        apply (drule no_fail_compose_imp)
        apply clarsimp
        apply (rule det_compose)
            apply (rule weak_det_specD)
          apply (simp add: assms)+
        apply (drule_tac x = r in spec)
        apply (drule meta_spec)
        apply (drule no_fail_compose_imp)
        apply clarsimp
            apply (rule det_compose)
          apply fastforce
          apply (rule det_spec_return)
        apply simp
      apply simp
    done
qed

lemma empty_when_fail_mapM:
  "(\<And>P l. weak_det_spec P (x l) \<and> empty_when_fail (x l))
  \<Longrightarrow> empty_when_fail (mapM x ls)"
proof (induct ls)
  case Nil
  show ?case
    by (clarsimp simp:mapM_def sequence_def empty_when_fail_return)
next
  case (Cons x xs)
  show ?case
    apply (clarsimp simp:mapM_Cons)
    apply (rule empty_when_fail_compose)+
        apply (simp add: empty_when_fail_return)
       apply (rule Cons)+
      apply (rule weak_det_spec_mapM)
      apply (simp add: Cons)+
    done
qed

lemma weak_det_spec_compose:
  assumes Q:"\<And>Q r. weak_det_spec (Q r) (b r)"
  assumes P:"\<And>P. weak_det_spec P a"
  shows "\<And>P. weak_det_spec P (a>>=b)"
  apply (clarsimp simp:weak_det_spec_def)
  apply (frule no_fail_compose_imp)
  apply clarsimp
  apply (rule det_compose)
    apply (simp add: P[THEN weak_det_specD])
   apply (drule_tac x = r in spec)
   apply (erule Q[THEN weak_det_specD])
  apply simp
  done

lemma weak_det_spec_select_f:
  "\<lbrakk>\<And>P. weak_det_spec P f\<rbrakk> \<Longrightarrow> weak_det_spec Q (select_f (f a))"
  apply (case_tac "\<forall>s. \<not>Q s")
   apply (simp add:weak_det_spec_def no_fail_def det_spec_def)
  apply (clarsimp simp:weak_det_spec_def)
  apply (rule det_spec_select_f[where P = "(=) a"])
   apply simp
  apply (drule_tac x = "(=) a" in meta_spec)
  apply (clarsimp simp: no_fail_def select_f_def)
  done

lemma weak_det_spec_fail:
  "weak_det_spec P fail"
  by (auto simp: weak_det_spec_def no_fail_def fail_def det_spec_def)

lemma weak_det_spec_assert:
  "weak_det_spec P (assert x)"
  by (auto simp:weak_det_spec_fail assert_def det_imply_weak_det[OF det_spec_return])

lemma weak_det_spec_assert_opt:
  "weak_det_spec P (assert_opt x)"
  by (auto simp: weak_det_spec_fail det_imply_weak_det[OF det_spec_return] assert_opt_def split:option.splits)

lemma weak_det_spec_gets_the:
  "weak_det_spec P (gets_the f)"
  apply (simp add:gets_the_def)
  apply (rule weak_det_spec_compose[OF weak_det_spec_assert_opt det_imply_weak_det[OF det_spec_gets]])
done


lemma weak_det_spec_loadWord:
  "weak_det_spec P (loadWord x)"
  apply (clarsimp simp:loadWord_def)
    apply (rule weak_det_spec_compose)+
      apply (rule det_imply_weak_det[OF det_spec_return])
      apply (rule weak_det_spec_assert)
    apply (rule det_imply_weak_det[OF det_spec_gets])
  done

lemmas weak_det_spec_simps = weak_det_spec_fail weak_det_spec_assert weak_det_spec_assert_opt weak_det_spec_gets_the
                             det_imply_weak_det[OF det_spec_return] det_imply_weak_det[OF det_spec_get]
                             det_imply_weak_det[OF det_spec_gets] det_imply_weak_det[OF det_spec_modify]

lemma weak_det_spec_storeWord:
  "weak_det_spec P (storeWord a b)"
  apply (simp add:storeWord_def)
    apply (rule weak_det_spec_compose)+
    apply (simp_all add:weak_det_spec_simps)
done


lemma weak_det_spec_thread_get:
  "weak_det_spec P (thread_get f x)"
  apply (simp add:thread_get_def)
  apply (rule weak_det_spec_compose)
  apply (clarsimp simp:weak_det_spec_simps)+
done

lemma weak_det_spec_load_word_offs:
  "weak_det_spec P (load_word_offs buf r)"
  apply (clarsimp simp:load_word_offs_def)
  apply (clarsimp simp:do_machine_op_def)
  apply (rule weak_det_spec_compose)+
    apply clarsimp
    apply (rule weak_det_spec_compose)+
      apply (rule det_imply_weak_det[OF det_spec_return])
    apply (rule det_imply_weak_det[OF det_spec_modify])
    apply (rule weak_det_spec_select_f)
    apply (rule weak_det_spec_loadWord)
    apply (rule det_imply_weak_det[OF det_spec_gets])
done

lemma empty_when_fail_fail:
  "empty_when_fail fail"
  by (clarsimp simp:empty_when_fail_def fail_def)

lemma empty_when_fail_get:
  "empty_when_fail get"
  by (clarsimp simp:empty_when_fail_def get_def return_def)

lemma empty_when_fail_gets:
  "empty_when_fail (gets x)"
  by (clarsimp simp:empty_when_fail_def get_def return_def gets_def bind_def)

lemma empty_when_fail_assert:
  "empty_when_fail (assert x)"
  by(clarsimp simp:empty_when_fail_def assert_def fail_def return_def bind_def)

lemma empty_when_fail_assert_opt:
  "empty_when_fail (assert_opt x)"
  by (auto simp:assert_opt_def fail_def return_def empty_when_fail_def split:option.splits)

lemma empty_when_fail_gets_the:
  "empty_when_fail (gets_the f)"
  apply (clarsimp simp:gets_the_def)
  apply (rule empty_when_fail_compose)+
  apply (rule empty_when_fail_assert_opt)
  apply (rule empty_when_fail_gets)+
  apply (rule det_imply_weak_det[OF det_spec_gets])
done

lemma empty_when_fail_modify:
  "empty_when_fail (modify x)"
  by (clarsimp simp:empty_when_fail_def simpler_modify_def)


lemmas empty_when_fail_simps = empty_when_fail_fail empty_when_fail_return empty_when_fail_get empty_when_fail_gets
                               empty_when_fail_gets_the empty_when_fail_assert empty_when_fail_assert_opt empty_when_fail_modify

lemma empty_when_fail_loadWord:
  "empty_when_fail (loadWord x)"
  apply (simp add:loadWord_def)
  apply (rule empty_when_fail_compose[OF _ empty_when_fail_gets])
    apply (rule empty_when_fail_compose[OF empty_when_fail_return])
  apply (simp_all add: weak_det_spec_simps empty_when_fail_simps)+
done

lemma empty_when_fail_storeWord:
  "empty_when_fail (storeWord a b)"
  apply (simp add:storeWord_def)
  apply (rule empty_when_fail_compose)+
  apply (simp_all add:empty_when_fail_simps weak_det_spec_simps)
done

lemma empty_when_fail_select_f:
  "\<lbrakk>empty_when_fail f\<rbrakk> \<Longrightarrow> empty_when_fail (select_f (f a))"
  by (clarsimp simp:empty_when_fail_def select_f_def)

lemma empty_when_fail_thread_get:
  "empty_when_fail (thread_get f x)"
  apply (clarsimp simp:thread_get_def)
  apply (rule empty_when_fail_compose)
  apply (clarsimp simp:empty_when_fail_simps weak_det_spec_simps)+
done

lemma empty_when_fail_load_word_offs:
  "empty_when_fail  (load_word_offs buf r)"
  apply (clarsimp simp:load_word_offs_def)
  apply (clarsimp simp:do_machine_op_def)
  apply (rule empty_when_fail_compose[OF _ empty_when_fail_gets])
    apply (rule empty_when_fail_compose[OF _ empty_when_fail_select_f])
    apply clarsimp
    apply (rule empty_when_fail_compose[OF empty_when_fail_return])
    apply (simp_all add:empty_when_fail_simps weak_det_spec_simps empty_when_fail_loadWord)
    apply (rule weak_det_spec_select_f[OF weak_det_spec_loadWord])
done

lemma empty_when_fail_get_object:
  "empty_when_fail (get_object x)"
  apply (simp add:get_object_def)
  apply (rule empty_when_fail_compose)+
  apply (simp add:empty_when_fail_simps weak_det_spec_simps)+
done

lemma weak_det_spec_get_object:
  "weak_det_spec P (get_object x)"
  apply (simp add:get_object_def)
  apply (rule weak_det_spec_compose)+
  apply (simp add:weak_det_spec_simps)+
done

lemma weak_det_spec_get_cap:
  "weak_det_spec P (get_cap slot)"
  apply (case_tac slot)
  apply (simp add:get_cap_def)
  apply (rule weak_det_spec_compose)+
  apply (simp_all add:weak_det_spec_simps weak_det_spec_get_object)
  apply (case_tac r)
  apply (simp_all add:weak_det_spec_simps weak_det_spec_get_object)
  apply (rule weak_det_spec_compose)
  apply (simp_all add:weak_det_spec_simps weak_det_spec_get_object)
done

lemma empty_when_fail_get_cap:
  "empty_when_fail (get_cap slot)"
  apply (case_tac slot)
  apply (clarsimp simp:get_cap_def)
  apply (rule empty_when_fail_compose)+
  apply (simp_all add:empty_when_fail_simps empty_when_fail_get_object weak_det_spec_get_object)
    apply (case_tac r)
    apply (simp_all add:empty_when_fail_simps empty_when_fail_get_object weak_det_spec_get_object)
    apply (rule empty_when_fail_compose)
    apply (simp_all add:empty_when_fail_simps weak_det_spec_simps empty_when_fail_get_object)
  apply (case_tac r)
    apply (simp_all add:empty_when_fail_simps weak_det_spec_simps empty_when_fail_get_object)
  apply (rule weak_det_spec_compose)
    apply (simp_all add:empty_when_fail_simps weak_det_spec_simps empty_when_fail_get_object)
done

lemma not_emptyI: "a\<noteq>{} \<Longrightarrow>\<exists>x. x\<in> a"
  by auto

lemma evalMonad_do_machine_op:
assumes "weak_det_spec ((=) (machine_state sa)) f"
assumes "empty_when_fail f"
shows "evalMonad (f) (machine_state sa) =
          evalMonad (do_machine_op (f)) sa"
  apply (clarsimp simp:evalMonad_def do_machine_op_def gets_def get_def bind_def return_def simpler_modify_def)
  apply (clarsimp simp:select_f_def | rule conjI)+
    apply (drule not_emptyI)
    apply clarsimp
    apply (rule_tac x = "(a,b)" in bexI)
      apply clarsimp+
    apply (rule arg_cong[where f = "(\<lambda>A. (SOME x. x\<in> A))"])
    apply (rule set_eqI)
    apply (clarsimp simp:image_def)
    apply (rule iffI)
      apply clarsimp
    using assms
    apply (clarsimp simp:empty_when_fail_def weak_det_spec_def no_fail_def)
    apply (drule_tac x = "machine_state sa" in spec)
    apply (clarsimp simp:det_spec_def)
   using assms
   apply (clarsimp simp:empty_when_fail_def weak_det_spec_def no_fail_def)
  apply force
  done

lemma evalMonad_wp:
  "\<lbrakk>empty_when_fail f; weak_det_spec ((=) pres) f\<rbrakk> \<Longrightarrow> \<lbrace>(=) pres \<rbrace>f\<lbrace>\<lambda>rv s. evalMonad f pres = Some rv\<rbrace>"
  apply (clarsimp simp:valid_def weak_det_spec_def no_fail_def empty_when_fail_def)
  apply (drule_tac x = pres in spec)
  apply (clarsimp simp:evalMonad_def notemptyI det_spec_def)
  done



lemma evalMonad_compose:
  "\<lbrakk>empty_when_fail a;weak_det_spec ((=) s) a;\<And>s. \<lbrace>(=) s\<rbrace> a \<lbrace>\<lambda>r. (=) s\<rbrace>\<rbrakk>
    \<Longrightarrow> evalMonad (a>>=b) s = (case (evalMonad a s) of Some r \<Rightarrow> evalMonad (b r) s | _ \<Rightarrow> None)"
  apply (clarsimp simp:evalMonad_def weak_det_spec_def)
  apply (clarsimp simp:no_fail_def det_spec_def empty_when_fail_def)
  apply (drule_tac x = s in spec)+
  apply (case_tac "snd (a s)")
    apply (simp_all)
    apply (fastforce simp:bind_def valid_def)
  apply (clarsimp simp:valid_def)
  apply (drule_tac x = s in meta_spec)
  apply (clarsimp simp:bind_def)
  done

lemma evalMonad_thread_get:
  "evalMonad (thread_get f thread) sa = Some x \<Longrightarrow>  \<exists>tcb. get_tcb thread sa = Some tcb \<and> f tcb = x"
  by (clarsimp simp:thread_get_def evalMonad_def gets_def gets_the_def
    assert_opt_def bind_def get_def return_def get_tcb_def fail_def
    split:option.splits Structures_A.kernel_object.splits)

lemma evalMonad_get_cap:
  "evalMonad (get_cap slot) s = caps_of_state s slot"
  using weak_det_spec_get_cap[where P ="(=) s" and slot = slot]
  using empty_when_fail_get_cap[where slot = slot]
  apply (clarsimp simp:evalMonad_def caps_of_state_def empty_when_fail_def
    weak_det_spec_def no_fail_def det_spec_def)
  apply (drule_tac x = s in spec)
  apply clarsimp
  apply (subgoal_tac "\<lbrace>(=) s\<rbrace>get_cap slot \<lbrace>\<lambda>r. (=) s\<rbrace>")
    apply (clarsimp simp:valid_def)
  apply wp
done

lemma evalMonad_loadWord:
  "evalMonad (loadWord x) ms =
    (if x && mask 2 = 0 then
      Some (word_rcat [underlying_memory ms (x + 3), underlying_memory ms (x + 2), underlying_memory ms (x + 1), underlying_memory ms x])
    else None)"
  by (clarsimp simp: loadWord_def gets_def get_def return_def bind_def assert_def fail_def evalMonad_def)

lemma weak_det_spec_lookup_ipc_buffer:
  "weak_det_spec P (lookup_ipc_buffer a b)"
  apply (simp add:lookup_ipc_buffer_def)
  apply (rule weak_det_spec_compose)+
    apply (simp_all add: empty_when_fail_simps empty_when_fail_get_cap empty_when_fail_thread_get
                         weak_det_spec_simps weak_det_spec_thread_get weak_det_spec_get_cap)
  apply (case_tac ra; simp add:weak_det_spec_simps)
  apply (rename_tac arch_cap)
  apply (case_tac arch_cap; simp add:weak_det_spec_simps)
  done

lemma empty_when_fail_lookup_ipc_buffer:
  "empty_when_fail (lookup_ipc_buffer a b)"
  apply (simp add:lookup_ipc_buffer_def)
  apply (rule empty_when_fail_compose)+
      apply (simp_all add: empty_when_fail_simps empty_when_fail_get_cap empty_when_fail_thread_get
                           weak_det_spec_simps weak_det_spec_thread_get weak_det_spec_get_cap)
  apply (case_tac ra; simp add:empty_when_fail_simps)
  apply (rename_tac arch_cap)
  apply (case_tac arch_cap; simp add:empty_when_fail_simps)
  done

abbreviation
"\<lambda>s. ipc_frame_cte_at thread buf rights sz s \<equiv>
  \<lambda>s. (\<exists>mapdata dev. cte_wp_at ((=) (cap.ArchObjectCap (arch_cap.PageCap dev buf rights sz mapdata))) (thread,tcb_cnode_index 4) s)"

lemma lookup_ipc_buffer_SomeB_evalMonad:
  "evalMonad (lookup_ipc_buffer in_receive thread) sa = Some (Some buf)
    \<Longrightarrow> \<exists>b rs sz obj.  AllowRead \<in>  rs \<and> (\<not> in_receive \<or> (AllowWrite \<in> rs))
    \<and> ipc_frame_cte_at thread b rs sz sa \<and> ko_at (TCB obj) thread sa
    \<and> (buf = b + (tcb_ipc_buffer obj && mask (pageBitsForSize sz)))"
  apply (simp add:lookup_ipc_buffer_def)
  apply (subst (asm) evalMonad_compose)
    apply (clarsimp simp:empty_when_fail_thread_get weak_det_spec_thread_get)+
    apply wp
  apply (clarsimp split:option.splits dest!:evalMonad_thread_get)
  apply (subst (asm) evalMonad_compose)
    apply (clarsimp simp:empty_when_fail_get_cap weak_det_spec_get_cap)+
   apply wp
   apply (clarsimp simp:evalMonad_get_cap split:option.splits)
   apply (clarsimp dest!:caps_of_state_cteD get_tcb_SomeD simp:obj_at_def split:cap.splits arch_cap.splits if_splits)
   apply (clarsimp simp:cte_wp_at_cases)
   apply (fastforce simp: obj_at_def vm_read_only_def vm_read_write_def)
done

lemma lookup_ipc_buffer_None_evalMonad:
  "evalMonad (lookup_ipc_buffer in_receive thread) sa = Some None
    \<Longrightarrow> \<exists>obj. ko_at (TCB obj) thread sa \<and> (\<forall>b rs sz. ipc_frame_cte_at thread b rs sz sa
    \<longrightarrow> ((AllowRead \<notin> rs \<and> \<not> in_receive) \<or>  (in_receive \<and> (AllowWrite \<notin> rs \<or> AllowRead\<notin> rs)))) "
  apply (simp add:lookup_ipc_buffer_def)
  apply (subst (asm) evalMonad_compose)
    apply (clarsimp simp:empty_when_fail_thread_get weak_det_spec_thread_get)+
    apply wp
  apply (clarsimp split:option.splits dest!:evalMonad_thread_get)
  apply (subst (asm) evalMonad_compose)
    apply (clarsimp simp:empty_when_fail_get_cap weak_det_spec_get_cap)+
   apply wp
   apply (clarsimp simp:evalMonad_get_cap split:option.splits)
   apply (clarsimp dest!:caps_of_state_cteD get_tcb_SomeD)
   apply (simp add:obj_at_def cte_wp_at_cases split:cap.splits arch_cap.splits if_splits)
   apply (clarsimp simp:vm_read_only_def vm_read_write_def)
done

lemma cdl_get_ipc_buffer_None:
  "\<lbrakk> valid_etcbs s'; not_idle_thread thread s';
    evalMonad(lookup_ipc_buffer in_receive thread) s' = Some None \<rbrakk> \<Longrightarrow>
  \<lbrace>(=) (transform s')\<rbrace> get_ipc_buffer thread in_receive \<lbrace>\<lambda>r s. r = None\<rbrace>"
  supply if_cong[cong]
  apply (drule lookup_ipc_buffer_None_evalMonad)
  apply (clarsimp simp: valid_def get_ipc_buffer_def gets_the_def gets_def bind_def get_def return_def)
  apply (subst (asm) opt_cap_tcb)
     apply (simp add: obj_at_def get_tcb_rev not_idle_thread_def |
            drule(1) valid_etcbs_tcb_etcb |
            fastforce simp: get_etcb_rev)+
  apply (clarsimp simp: assert_opt_def return_def split: cdl_cap.splits)
  apply (clarsimp simp: transform_cap_def split: cap.splits arch_cap.splits)
  by (auto simp: cte_wp_at_cases split: if_split_asm)

lemma cdl_get_ipc_buffer_Some:
  "\<lbrakk>ipc_frame_cte_at thread b rs sz s';valid_etcbs s';tcb_at thread s';not_idle_thread thread s';AllowRead \<in>  rs \<and> (\<not> in_receive \<or> (AllowWrite \<in> rs))\<rbrakk>  \<Longrightarrow>
  \<lbrace>(=) (transform s')\<rbrace> get_ipc_buffer thread in_receive \<lbrace>\<lambda>r s. r = Some b\<rbrace>"
  apply (clarsimp simp: tcb_at_def not_idle_thread_def)
  apply (drule(1) valid_etcbs_get_tcb_get_etcb)
  apply (clarsimp simp:get_ipc_buffer_def gets_the_def gets_def bind_assoc valid_def)
  apply (clarsimp simp:get_def bind_def assert_opt_def)
  apply (subst (asm) opt_cap_tcb,simp +)
  apply (clarsimp simp:return_def cte_wp_at_cases dest!:get_tcb_SomeD get_etcb_SomeD)
  apply (drule sym)
  apply (clarsimp simp:transform_cap_def return_def split:if_splits)
  done

lemma get_ipc_buffer_words_empty:
  "\<lbrakk>ko_at (TCB obj) thread sa;evalMonad (lookup_ipc_buffer False thread) sa = Some None\<rbrakk> \<Longrightarrow>
  get_ipc_buffer_words (machine_state sa) obj x = []"
  apply (simp add:lookup_ipc_buffer_def)
  apply (subst (asm) evalMonad_compose)
    apply (clarsimp simp:empty_when_fail_thread_get weak_det_spec_thread_get)+
    apply wp
  apply (clarsimp split:option.splits dest!:evalMonad_thread_get)
  apply (subst (asm) evalMonad_compose)
    apply (clarsimp simp:empty_when_fail_get_cap weak_det_spec_get_cap)+
   apply wp
   apply (clarsimp simp:evalMonad_get_cap split:option.splits)
   apply (clarsimp dest!:caps_of_state_cteD get_tcb_SomeD simp:obj_at_def split:cap.splits arch_cap.splits if_splits)
   apply (clarsimp simp:cte_wp_at_cases get_ipc_buffer_words_def dest!:sym[where t = "tcb_ipcframe obj"])+
   apply (clarsimp simp:evalMonad_def split:if_splits)
   apply (clarsimp simp:obj_at_def vm_read_only_def return_def vm_read_write_def)+
   apply (clarsimp simp:cte_wp_at_cases get_ipc_buffer_words_def dest!:sym[where t = "tcb_ipcframe obj"])+
done

lemma get_ipc_buffer_words:
  "\<lbrace>(=) sa and ko_at (TCB obj) thread and K_bind (evalMonad (lookup_ipc_buffer in_receive thread) sa = Some (Some buf))\<rbrace>
    mapM (load_word_offs (buf)) (ls)
   \<lbrace>\<lambda>buf_mrs s. buf_mrs = get_ipc_buffer_words (machine_state sa) obj (ls)\<rbrace>"
  apply (simp add: pred_conj_aci get_ipc_buffer_words_def)
  apply (rule wp_spec)
  apply clarsimp
  apply (drule lookup_ipc_buffer_SomeB_evalMonad)
  apply (clarsimp simp:obj_at_def cte_wp_at_cases)
  apply (drule sym[where t = "tcb_ipcframe obj"])
  apply clarsimp
  apply (rule weak_det_spec_ret)
    apply (rule weak_det_spec_mapM)
    apply (rule weak_det_spec_load_word_offs)
    apply simp
  apply (clarsimp simp: mapM_load_word_offs_do_machine_op mapM_map_simp)
  apply (rule arg_cong[where f = the])
  apply (rule evalMonad_do_machine_op)
  apply (rule weak_det_spec_mapM)
  apply clarsimp
  apply (rule weak_det_spec_loadWord)
  apply (rule empty_when_fail_mapM)
    apply (rule conjI)
    apply (clarsimp simp: weak_det_spec_loadWord empty_when_fail_loadWord)+
  apply (rule empty_when_fail_mapM)
    apply (clarsimp simp:weak_det_spec_load_word_offs empty_when_fail_load_word_offs)
done

lemma get_tcb_mrs_wp:
  "\<lbrace>(=) sa and ko_at (TCB obj) thread and K_bind (evalMonad (lookup_ipc_buffer False thread) sa = Some (op_buf))\<rbrace>
    get_mrs thread (op_buf) (data_to_message_info (arch_tcb_get_registers (tcb_arch obj) msg_info_register))
            \<lbrace>\<lambda>rv s. rv = get_tcb_mrs (machine_state sa) obj\<rbrace>"
  apply (case_tac op_buf)
    apply (clarsimp simp:get_mrs_def thread_get_def gets_the_def)
    apply (wp|wpc)+
    apply (clarsimp simp:get_tcb_mrs_def Let_def)
    apply (clarsimp simp:Suc_leI[OF msg_registers_lt_msg_max_length] split del:if_split)
    apply (clarsimp simp:get_tcb_message_info_def get_ipc_buffer_words_empty)
    apply (clarsimp dest!:get_tcb_SomeD
                    simp:obj_at_def arch_tcb_get_registers_def arch_tcb_context_get_def)
  apply (clarsimp simp:get_mrs_def thread_get_def gets_the_def arch_tcb_get_registers_def
                       arch_tcb_context_get_def)
  apply (clarsimp simp:Suc_leI[OF msg_registers_lt_msg_max_length] split del:if_split)
  apply (wp|wpc)+
  apply (rule_tac P = "tcb = obj" in hoare_gen_asm)
   apply (clarsimp simp: get_tcb_mrs_def Let_def get_tcb_message_info_def Suc_leI[OF msg_registers_lt_msg_max_length]
                   split del:if_split)
    apply (rule_tac Q'="\<lambda>buf_mrs s. buf_mrs =
      (get_ipc_buffer_words (machine_state sa) obj ([Suc (length msg_registers)..<msg_max_length] @ [msg_max_length]))"
      in hoare_strengthen_post)
    apply (rule get_ipc_buffer_words[where thread=thread ])
    apply (simp add: arch_tcb_context_get_def)
  apply wp
  apply (fastforce simp:get_tcb_SomeD obj_at_def)
done


(* Following is the proof of set_mrs *)

declare pbfs_less_wb' [simp]

lemma mab_le_pbfs [simp]:
  "msg_align_bits \<le> pageBitsForSize sz"
  by (cases sz, simp_all add: msg_align_bits)

lemma two_le_pbfs[simp]:
  "2 \<le> pageBitsForSize sz"
  by (cases sz,simp_all)

lemma two_le_msg_align_bits[simp]:
  "2 \<le> msg_align_bits"
  by(simp add:msg_align_bits)

lemma is_aligned_word_size[simp]:
  "is_aligned (of_nat r * of_nat word_size) 2"
  apply (simp add:word_size_def)
  apply (rule is_aligned_mult_triv2[where n = 2,simplified])
done

definition
  ipc_frame_wp_at :: "(word32 \<Rightarrow> rights set \<Rightarrow> vmpage_size \<Rightarrow> (word32 \<times> word32) option \<Rightarrow> bool) \<Rightarrow> obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
  where
  "ipc_frame_wp_at P \<equiv> obj_at (%ko. \<exists>tcb. ko = TCB tcb \<and>
  (case (tcb_ipcframe tcb) of
  cap.ArchObjectCap (arch_cap.PageCap dev ptr rights sz mapdata)  \<Rightarrow> P ptr rights sz mapdata
  | _                                                         \<Rightarrow> False))"

definition
  ipc_buffer_wp_at :: "word32 \<Rightarrow> obj_ref \<Rightarrow>'z::state_ext state \<Rightarrow> bool"
  where
  "ipc_buffer_wp_at w \<equiv> obj_at (%ko. \<exists>tcb. ko = TCB tcb \<and>
  tcb_ipc_buffer tcb = w)"


lemma ipc_frame_wp_at_cte_at:
  "ipc_frame_wp_at P a s\<Longrightarrow> \<exists>buf sz rs. ipc_frame_cte_at a buf sz rs s"
  by (clarsimp simp:ipc_frame_wp_at_def obj_at_def cte_wp_at_cases
    ,simp add: split:cap.splits arch_cap.splits)

abbreviation
  "ipc_frame_ptr_at ptr \<equiv> ipc_frame_wp_at (\<lambda>ptr' _ _ _. ptr = ptr')"

abbreviation
  "ipc_frame_sz_at sz \<equiv> ipc_frame_wp_at (\<lambda>_ _ sz' _. sz = sz')"

definition storeWord_ms :: "word32 \<Rightarrow> word32 \<Rightarrow> machine_state \<Rightarrow> machine_state"
where "storeWord_ms ptr b ms \<equiv>  (underlying_memory_update
   (\<lambda>m. m(ptr := word_rsplit b ! 3, ptr + 1 := word_rsplit b ! 2, ptr + 2 := word_rsplit b ! Suc 0, ptr + 3 := word_rsplit b ! 0))
   ms)"

definition
  is_arch_page_cap :: "cap \<Rightarrow> bool"
where
  "is_arch_page_cap cap = (case cap of
                               cap.ArchObjectCap (arch_cap.PageCap dev buf rights sz mapdata) \<Rightarrow> True
                             | _ \<Rightarrow> False)"

lemmas is_arch_page_cap_simps [simp] = is_arch_page_cap_def [split_simps cap.split arch_cap.split]


lemma get_ipc_frame_words_no_ipc_buffer:
  "\<not> (is_arch_page_cap (tcb_ipcframe tcb)) \<Longrightarrow> get_ipc_buffer_words ms tcb ns = []"
  unfolding get_ipc_buffer_words_def
  by (clarsimp simp: evalMonad_def Let_def return_def
    split:if_splits cap.splits arch_cap.splits)

lemma transform_full_intent_no_ipc_buffer:
    "\<not> (is_arch_page_cap (tcb_ipcframe tcb)) \<Longrightarrow> transform_full_intent ms ptr tcb = transform_full_intent ms' ptr tcb"
  unfolding transform_full_intent_def
  apply (clarsimp simp: evalMonad_def Let_def return_def get_tcb_mrs_def
     split:if_splits cap.splits arch_cap.splits)
  apply (simp add: get_ipc_frame_words_no_ipc_buffer)
done

lemma get_ipc_buffer_words_empty_list[simp]:
  "get_ipc_buffer_words x tcb_type [] = [] "
  by (clarsimp simp:get_ipc_buffer_words_def split:cap.splits arch_cap.splits
    simp:mapM_def sequence_def)


lemma evalMonad_mapM:
  "\<lbrakk>\<forall>r\<in>(set ls). evalMonad (f r) sa = evalMonad (g r) sb;
    \<And>s r. \<lbrace>(=) s\<rbrace> f r\<lbrace>\<lambda>r. (=) s\<rbrace>;
    \<And>s r. \<lbrace>(=) s\<rbrace> g r\<lbrace>\<lambda>r. (=) s\<rbrace>;
    \<And>r. empty_when_fail (f r);
    \<And>r. empty_when_fail (g r);
    \<And>r P. weak_det_spec P (f r);
    \<And>r P. weak_det_spec P (g r)\<rbrakk>
   \<Longrightarrow> evalMonad (mapM f ls) sa = evalMonad (mapM g ls) sb"
proof(induct ls)
  case Nil
  show ?case by (clarsimp simp:mapM_def sequence_def)
next
  case (Cons x ls)
  show ?case
    apply (clarsimp simp:mapM_Cons)
    apply (subst evalMonad_compose)
       apply (simp add:Cons)+
    apply (subst evalMonad_compose)
       apply (simp add:Cons)
       apply (rule empty_when_fail_mapM)
       apply (simp add:Cons)
      apply (rule weak_det_spec_mapM)
      apply (simp add:Cons)
     apply (rule mapM_wp_inv)
     apply (simp add:Cons)
    apply (subst evalMonad_compose)
       apply (simp add:Cons)+
    apply (subst evalMonad_compose)
       apply (rule empty_when_fail_mapM)
       apply (simp add:Cons)
      apply (rule weak_det_spec_mapM)
      apply (simp add:Cons)
     apply (rule mapM_wp_inv)
     apply (simp add:Cons)
    apply (subgoal_tac "evalMonad (mapM f ls) sa = evalMonad (mapM g ls) sb")
     apply (clarsimp split:option.splits)
    apply (rule Cons.hyps)
          apply (simp add:Cons)+
    done
qed

lemma underlying_memory_storeWord:
  "\<lbrakk> is_aligned ptr 2;is_aligned x 2;x \<noteq> ptr;n\<le> 3 \<rbrakk>
    \<Longrightarrow>underlying_memory (storeWord_ms ptr b ms) (x + n) =
            underlying_memory ms (x + n)"
  apply (simp add:storeWord_ms_def)
  using iffD2[OF and_mask_eq_iff_le_mask[where n = 2 and w = n]]
  apply (intro conjI)
  apply (clarsimp simp:is_aligned_mask mask_add_aligned)
    apply (simp add:mask_2pm1)
  apply (clarsimp simp:|rule conjI)+
    apply (case_tac "n=1")
      apply simp
    apply (drule arg_cong[where f = "\<lambda>x. x && mask 2"])
    apply (clarsimp simp:mask_add_aligned)
    using iffD2[OF and_mask_eq_iff_le_mask[where n = 2 and w = n]]
    apply (simp add:mask_2pm1)
  apply (clarsimp simp:|rule conjI)+
    apply (case_tac "n=2")
      apply simp
    apply (drule arg_cong[where f = "\<lambda>x. x && mask 2"])
    apply (clarsimp simp:mask_add_aligned)
    using iffD2[OF and_mask_eq_iff_le_mask[where n = 2 and w = n]]
    apply (simp add:mask_2pm1)
  apply clarsimp
    apply (case_tac "n=3")
      apply simp
    apply (drule arg_cong[where f = "\<lambda>x. x && mask 2"])
    apply (clarsimp simp:mask_add_aligned)
    using iffD2[OF and_mask_eq_iff_le_mask[where n = 2 and w = n]]
    apply (simp add:mask_2pm1)
  done

lemma ipc_frame_ptr_at_frame_at:
  "\<lbrakk>valid_objs s;ipc_frame_ptr_at buf thread s;ipc_frame_sz_at sz thread s\<rbrakk> \<Longrightarrow>ko_at (ArchObj (DataPage False sz)) buf s"
  apply (clarsimp simp:ipc_frame_wp_at_def obj_at_def)
  apply (clarsimp split:cap.splits arch_cap.splits)
  apply (drule valid_tcb_objs)
   apply (erule get_tcb_rev)
  apply (simp add:valid_tcb_def)
  apply (clarsimp simp: valid_ipc_buffer_cap_def tcb_cap_cases_def is_nondevice_page_cap_def
                 split: bool.split_asm)
  apply (clarsimp simp: valid_cap_def obj_at_def a_type_def is_nondevice_page_cap_def)
  by (clarsimp split: Structures_A.kernel_object.splits if_splits arch_kernel_obj.splits)

lemma ipc_buffer_within_frame:
  "\<lbrakk> pspace_aligned s;
     pspace_distinct s;
     ko_at (ArchObj (DataPage dev sz)) buf s;
     ko_at (ArchObj (DataPage dev' sz')) buf' s;
     ptr && ~~ mask (pageBitsForSize sz) = buf;
     ptr' && ~~ mask (pageBitsForSize sz') = buf';
     buf\<noteq>buf'\<rbrakk>
   \<Longrightarrow> ptr \<noteq> ptr'"
  apply (simp add:pspace_aligned_def obj_at_def)
  apply (frule_tac x = buf in bspec)
   apply (simp add:domI obj_at_def)
  apply (drule_tac x = buf' in bspec)
   apply (clarsimp simp:domI obj_at_def)
  apply (unfold pspace_distinct_def)
  apply (drule_tac x = buf in spec)
  apply (drule_tac x = buf' in spec)
  apply (drule_tac x = "ArchObj (DataPage dev sz)" in spec)
  apply (drule_tac x = "ArchObj (DataPage dev' sz')" in spec)
  apply (rule distinct_element)
    apply (rule mp)
     apply (assumption)
    apply simp
   apply (clarsimp simp:is_aligned_def word_and_le2 word_neg_and_le)
  apply (clarsimp simp:word_and_le2 word_neg_and_le)
  done

definition within_page :: "word32 \<Rightarrow> word32 \<Rightarrow> vmpage_size \<Rightarrow> bool"
  where
  "within_page buf ptr sz \<equiv> (ptr && ~~ mask (pageBitsForSize sz) = buf)"

lemma valid_tcb_obj_ipc_align_etc:
  "\<lbrakk>valid_objs s;pspace_aligned s;ipc_frame_ptr_at buf thread s;ipc_frame_sz_at pgsz thread s;
    get_tcb thread s = Some tcb\<rbrakk>
    \<Longrightarrow> is_aligned (tcb_ipc_buffer tcb) msg_align_bits \<and> is_aligned (tcb_ipc_buffer tcb) 2
    \<and> is_aligned buf (pageBitsForSize pgsz) \<and> is_aligned buf 2"
  apply (frule ipc_frame_ptr_at_frame_at)
    apply simp+
  apply (drule(1) valid_tcb_objs)
  apply (clarsimp dest!: get_tcb_SomeD simp:valid_tcb_def valid_ipc_buffer_cap_def
                         ipc_frame_wp_at_def obj_at_def)
  apply (clarsimp split: cap.splits arch_cap.splits bool.split_asm)
  apply (rule conjI)
    apply (rule is_aligned_weaken,simp+)
      apply (simp add:msg_align_bits_def)
  apply (simp add:pspace_aligned_def obj_at_def ipc_frame_wp_at_def)
  apply (drule_tac x = buf in bspec)
    apply (clarsimp simp:)
  apply (clarsimp simp:obj_at_def)
  apply (rule is_aligned_weaken)
    apply simp+
done

lemma mask_neg_mask_cancel:
  "a&& mask n && ~~ mask n = 0 "
 by (simp add:mask_out_sub_mask)

lemma get_ipc_buffer_words_helper:
  "\<lbrakk>valid_objs s;
    get_tcb thread s = Some tcb_type;
    ipc_frame_ptr_at obuf thread s;ipc_frame_sz_at osz thread s;
    ko_at (ArchObj (DataPage dev sz)) buf s;
    is_aligned ptr 2;
    pspace_aligned s; pspace_distinct s;
    within_page buf ptr sz;
    \<forall>x \<in> set xs. within_page obuf (obuf + (tcb_ipc_buffer tcb_type && mask (pageBitsForSize osz)) +of_nat x* of_nat word_size) osz;
    obuf \<noteq> buf\<rbrakk> \<Longrightarrow>
    get_ipc_buffer_words (storeWord_ms ptr b ms) tcb_type xs= get_ipc_buffer_words ms tcb_type xs"
  apply (clarsimp dest!:get_tcb_SomeD simp:get_ipc_buffer_words_def split:cap.splits arch_cap.splits)
  apply (frule ipc_frame_ptr_at_frame_at[where buf = obuf],simp+)
  apply (frule valid_tcb_obj_ipc_align_etc[where buf = obuf],simp+)
   apply (erule get_tcb_rev)
  apply (rule arg_cong[where f = the])
  apply (rule evalMonad_mapM)
        defer
        apply (simp_all add:empty_when_fail_loadWord weak_det_spec_loadWord)
    apply (wp loadWord_inv)+
  apply (clarsimp simp:obj_at_def ipc_frame_wp_at_def)
  apply (drule_tac x = r in bspec,simp)
  apply (clarsimp simp:evalMonad_loadWord get_tcb_SomeD | rule conjI)+
  apply (rule arg_cong[where f = word_rcat])
  apply clarsimp
  apply (clarsimp simp:|rule conjI)
   apply (rule underlying_memory_storeWord)
      apply simp_all
    apply (rule aligned_add_aligned)+
        apply simp+
       apply (rule is_aligned_after_mask)
        apply simp+
   apply (rule ipc_buffer_within_frame[where buf =obuf and buf'=buf])
         apply (simp add:obj_at_def get_tcb_SomeD within_page_def add.assoc)+
  apply (rule conjI)
   apply (subst add.assoc[symmetric])+
   apply (rule underlying_memory_storeWord)
      apply (simp_all)
    apply (rule aligned_add_aligned)+
        apply simp+
       apply (subst is_aligned_after_mask)
        apply simp+
   apply (rule ipc_buffer_within_frame[where buf = obuf and buf' = buf])
         apply (simp add:obj_at_def get_tcb_SomeD within_page_def add.assoc)+
  apply (rule conjI)
   apply (subst add.assoc[symmetric])+
   apply (rule underlying_memory_storeWord)
      apply (simp_all)
    apply (rule aligned_add_aligned)+
        apply simp+
       apply (subst is_aligned_after_mask)
        apply simp+
   apply (rule ipc_buffer_within_frame[where buf = obuf and buf' = buf])
         apply (simp add:obj_at_def get_tcb_SomeD within_page_def add.assoc)+
  apply (subst add.assoc[symmetric])+
  apply (rule underlying_memory_storeWord[where n = 0,simplified])
    apply (simp_all)
   apply (rule aligned_add_aligned)+
       apply simp+
      apply (subst is_aligned_after_mask)
       apply simp+
  apply (rule ipc_buffer_within_frame[where buf = obuf and buf' = buf])
        by ((simp add:obj_at_def get_tcb_SomeD within_page_def add.assoc)+)[7]

lemma get_ipc_buffer_words_separate_frame:
  "\<lbrakk>valid_objs s;
    get_tcb thread s = Some tcb_type;
    ipc_frame_ptr_at obuf thread s;ipc_frame_sz_at osz thread s;
    ipc_frame_ptr_at buf s_id s;ipc_frame_sz_at sz s_id s;
    is_aligned ptr 2;
    pspace_aligned s; pspace_distinct s;
    within_page buf ptr sz;
    \<forall>x \<in> set xs. within_page obuf (obuf + (tcb_ipc_buffer tcb_type && mask (pageBitsForSize osz)) +of_nat x* of_nat word_size) osz;
    obuf \<noteq> buf\<rbrakk> \<Longrightarrow>
    get_ipc_buffer_words (storeWord_ms ptr b ms) tcb_type xs= get_ipc_buffer_words ms tcb_type xs"
  apply (clarsimp dest!:get_tcb_SomeD simp:get_ipc_buffer_words_def split:cap.splits arch_cap.splits)
  apply (frule ipc_frame_ptr_at_frame_at[where buf = buf],simp+)
  apply (frule ipc_frame_ptr_at_frame_at[where buf = obuf],simp+)
  apply (frule valid_tcb_obj_ipc_align_etc[where buf = obuf],simp+)
   apply (erule get_tcb_rev)
  apply (subgoal_tac "\<exists>tcb. get_tcb s_id s = Some tcb")
   prefer 2
   apply (clarsimp simp:ipc_frame_wp_at_def obj_at_def)
   apply (rule exI)
   apply (erule get_tcb_rev)
  apply clarify
  apply (frule valid_tcb_obj_ipc_align_etc[where buf = buf],simp+)
  apply (rule arg_cong[where f = the])
  apply (rule evalMonad_mapM)
        defer
        apply (simp_all add:empty_when_fail_loadWord weak_det_spec_loadWord)
    apply (wp loadWord_inv)+
  apply (clarsimp simp:obj_at_def ipc_frame_wp_at_def)
  apply (drule_tac x = r in bspec,simp)
  apply (clarsimp split:cap.split_asm arch_cap.split_asm)
  apply (clarsimp simp:evalMonad_loadWord get_tcb_SomeD | rule conjI)+
  apply (rule arg_cong[where f = word_rcat])
  apply clarsimp
  apply (clarsimp simp:|rule conjI)
   apply (rule underlying_memory_storeWord)
      apply simp_all
    apply (rule aligned_add_aligned)+
        apply simp+
       apply (rule is_aligned_after_mask)
        apply simp+
   apply (rule ipc_buffer_within_frame[where buf =obuf and buf'=buf])
         apply (simp add:obj_at_def get_tcb_SomeD within_page_def add.assoc)+
  apply (rule conjI)
   apply (subst add.assoc[symmetric])+
   apply (rule underlying_memory_storeWord)
      apply (simp_all)
    apply (rule aligned_add_aligned)+
        apply simp+
       apply (subst is_aligned_after_mask)
        apply simp+
   apply (rule ipc_buffer_within_frame[where buf = obuf and buf' = buf])
         apply (simp add:obj_at_def get_tcb_SomeD within_page_def add.assoc)+
  apply (rule conjI)
   apply (subst add.assoc[symmetric])+
   apply (rule underlying_memory_storeWord)
      apply (simp_all)
    apply (rule aligned_add_aligned)+
        apply simp+
       apply (subst is_aligned_after_mask)
        apply simp+
   apply (rule ipc_buffer_within_frame[where buf = obuf and buf' = buf])
         apply (simp add:obj_at_def get_tcb_SomeD within_page_def add.assoc)+
  apply (subst add.assoc[symmetric])+
  apply (rule underlying_memory_storeWord[where n = 0,simplified])
    apply (simp_all)
   apply (rule aligned_add_aligned)+
       apply simp+
      apply (subst is_aligned_after_mask)
       apply simp+
  apply (rule ipc_buffer_within_frame[where buf = obuf and buf' = buf])
        by ((simp add:obj_at_def get_tcb_SomeD within_page_def add.assoc)+)[7]

lemma mask_inj_if:
  "\<lbrakk>a && mask n = a; b && mask n = b; a && mask n = b && mask n\<rbrakk>\<Longrightarrow> a = b"
  by (rule box_equals)

(* FIXME: move to Word_Lib, generalise *)
lemma bound_preserve_mask:
  "\<lbrakk> is_aligned (x::word32) n; x\<le> mask k; (z::word32)\<le> mask n; n < 32; k < 32; n \<le> k \<rbrakk> \<Longrightarrow>
   x+z \<le> mask k"
  apply (rule order_trans[where y = "(mask k && ~~ mask n) + mask n"])
   apply (rule order_trans[where y = "x + mask n"])
    apply (erule word_plus_mono_right)
    apply (rule is_aligned_no_wrap')
     apply simp
    apply (rule mask_lt_2pn)
    apply (simp add: word_size)
   apply (rule word_plus_mono_left)
    apply (rule order_trans[where y = "x && ~~ mask n"])
     apply (simp add: mask_out_sub_mask is_aligned_mask)
    apply (erule neg_mask_mono_le)
   apply (simp add: mask_out_sub_mask mask_and_mask min_def cong: if_cong)
   apply (rule word_leI)
   apply (clarsimp simp: word_size)
  apply (simp add: mask_out_sub_mask mask_and_mask min_def)
  done

lemma nat_less_le:
  "(a::nat) < b \<Longrightarrow> a \<le> b - 1"
  by auto

lemma within_page_ipc_buf:
  "\<lbrakk>valid_objs s; pspace_aligned s; pspace_distinct s; ipc_frame_ptr_at buf y s; ipc_frame_sz_at sz y s;
                ipc_buffer_wp_at bptr y s; x < 2 ^ (msg_align_bits - 2) \<rbrakk>
      \<Longrightarrow> within_page buf (buf + (bptr && mask (pageBitsForSize sz)) + of_nat x * of_nat word_size) sz"
  apply (clarsimp simp:ipc_buffer_wp_at_def obj_at_def)
  apply (frule valid_tcb_obj_ipc_align_etc,simp+)
   apply (erule get_tcb_rev)
  apply (clarsimp simp: ipc_frame_wp_at_def obj_at_def within_page_def)
  apply (clarsimp split: cap.split_asm arch_cap.split_asm)
  apply (frule valid_tcb_objs, erule get_tcb_rev)
  apply (clarsimp simp: valid_tcb_def valid_ipc_buffer_cap_def)
  apply (subst add.assoc)
  apply (erule is_aligned_add_helper[THEN conjunct2])
  apply (rule iffD1[OF le_mask_iff_lt_2n[where n = "pageBitsForSize sz"],THEN iffD1])
   apply (simp add:word_size)
   apply (case_tac sz,simp_all)
  apply (rule bound_preserve_mask[where n = msg_align_bits])
       apply (rule is_aligned_after_mask)
        apply (simp add:word_and_le1)+
     apply (simp add:msg_align_bits mask_2pm1)
     apply (rule div_le_mult)
      apply (simp add:word_size_def)
      apply (rule word_of_nat_le)
      apply (simp add:word_size_def msg_align_bits)+
   apply (cases sz,auto)
  done

lemma eq_sym_helper: "(A = B)  \<Longrightarrow> (B = A)"
  by auto

lemma store_word_corres_helper:
  "\<lbrakk>pspace_aligned s; pspace_distinct s; valid_objs s; valid_etcbs s; ipc_frame_ptr_at buf s_id s;
    ipc_frame_sz_at sz s_id s; is_aligned ptr 2 ; within_page buf ptr sz\<rbrakk>
            \<Longrightarrow> \<exists>f. corrupt_intents (f) buf (transform s) =
               transform (update_machine (storeWord_ms ptr b (machine_state s)) s)"
  unfolding transform_def corrupt_intents_def
  supply option.case_cong[cong]
  apply (clarsimp simp: transform_current_thread_def transform_objects_def Let_def)
  apply (rule exI)
  apply (rule ext)
  apply (rename_tac thread)
  apply (clarsimp simp: map_add_def split: option.splits simp del: Option.case_map_option)
  apply (rule conjI)
   apply (clarsimp simp:restrict_map_def map_add_def)
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp:restrict_map_def transform_object_def transform_tcb_def
                   split:cdl_object.split_asm Structures_A.kernel_object.split_asm if_split_asm)
            apply (drule(1) valid_etcbs_tcb_etcb,
                   clarsimp simp:restrict_map_def transform_object_def transform_tcb_def
                            split:cdl_object.split_asm Structures_A.kernel_object.split_asm if_split_asm)+
          defer
          apply (drule(1) valid_etcbs_tcb_etcb,
                 clarsimp simp:restrict_map_def transform_object_def transform_tcb_def
                          split:cdl_object.split_asm Structures_A.kernel_object.split_asm if_split_asm)+
   defer
   apply (simp add:tcb_ipcframe_id_def tcb_boundntfn_slot_def tcb_ipcbuffer_slot_def split:if_split_asm)
    apply (simp add:tcb_ipcbuffer_slot_def tcb_pending_op_slot_def)
   apply (frule_tac thread = thread in valid_tcb_objs)
    apply (simp add: get_tcb_rev)
   apply (clarsimp simp:valid_tcb_def tcb_cap_cases_def)
   apply (rename_tac tcb etcb)
   apply (case_tac "\<not> is_arch_page_cap (tcb_ipcframe tcb)")
    apply (simp add:transform_full_intent_no_ipc_buffer)
   apply (clarsimp simp del:upt.simps simp:transform_full_intent_def Let_def get_tcb_mrs_def is_arch_page_cap_def
                   split:cap.split_asm arch_cap.split_asm split del:if_split)
   apply (rename_tac word cap_rights vmpage_size option)
   apply (clarsimp simp:transform_cap_def arch_cap.split_asm simp del:upt.simps)
   apply (frule_tac thread = thread and ptr = ptr and sz = sz
            and ms = "machine_state s" and tcb_type = tcb and b = b and s_id = s_id
            and xs = "[Suc (length msg_registers)..<Suc msg_max_length]"
            in get_ipc_buffer_words_separate_frame)
               apply (erule get_tcb_rev)
              apply ((simp add:ipc_frame_wp_at_def obj_at_def)+)[8]
     apply (clarsimp simp del:upt.simps)
     apply (rule_tac y = thread in within_page_ipc_buf)
           apply (simp add:ipc_frame_wp_at_def obj_at_def ipc_buffer_wp_at_def)+
     apply (simp add:msg_max_length_def msg_align_bits)
    apply simp
   apply (clarsimp simp:transform_cap_def split:cap.splits arch_cap.splits)
   apply (rule conjI)
    apply (frule_tac thread = thread and ptr = ptr and sz = sz and ms = "machine_state s" and
            tcb_type = tcb and b = b and s_id = s_id
            and xs = "[buffer_cptr_index..<buffer_cptr_index + unat (mi_extra_caps (get_tcb_message_info tcb))]"
            in get_ipc_buffer_words_separate_frame)
                apply (erule get_tcb_rev)
               apply ((simp add:ipc_frame_wp_at_def obj_at_def)+)[8]
      apply (clarsimp simp del:upt.simps)
      apply (rule_tac sz = vmpage_size and y = thread in within_page_ipc_buf)
            apply (simp add:ipc_frame_wp_at_def obj_at_def ipc_buffer_wp_at_def)+
      apply (simp add:msg_max_length_def msg_align_bits buffer_cptr_index_def)
      apply (case_tac "get_tcb_message_info tcb")
      apply (clarsimp simp add: get_tcb_message_info_def data_to_message_info_def)
      apply (erule order_less_le_trans)
      apply (simp add: mask_def)
      apply (rule iffD1[OF word_le_nat_alt[where b = "0x6::word32",simplified]])
      apply (rule order_trans)
       apply (rule  word_and_le1[where a = 3])
      apply ((clarsimp simp:ipc_frame_wp_at_def obj_at_def)+)[4]
   apply (frule_tac thread = thread and ptr = ptr and sz = sz and ms = "machine_state s" and
           tcb_type = tcb and b = b and s_id = s_id
           and xs = "[Suc (Suc (msg_max_length + msg_max_extra_caps))..<5 + (msg_max_length + msg_max_extra_caps)]"
           in get_ipc_buffer_words_separate_frame)
              apply (erule get_tcb_rev)
             apply ((simp add:ipc_frame_wp_at_def obj_at_def)+)[8]
     apply (clarsimp simp del:upt.simps)
     apply (rule_tac y = thread and sz = vmpage_size in within_page_ipc_buf)
           apply (simp add:ipc_frame_wp_at_def obj_at_def ipc_buffer_wp_at_def)+
     apply (clarsimp simp:msg_align_bits msg_max_length_def msg_max_extra_caps_def)
    apply simp+
  apply (clarsimp simp: tcb_ipcframe_id_def split: cdl_object.splits option.split_asm cdl_cap.split_asm)
  apply (clarsimp simp: transform_object_def split:Structures_A.kernel_object.split_asm arch_kernel_obj.split_asm nat.splits)
  apply (rename_tac tcb)
  apply (simp add:transform_tcb_def)
  apply (drule sym)
  apply (clarsimp simp:tcb_pending_op_slot_def restrict_map_def tcb_ipcbuffer_slot_def split:if_splits)
  apply (frule(1) valid_etcbs_tcb_etcb[OF _ eq_sym_helper])
  apply clarsimp
  apply (subgoal_tac "(get_tcb thread s) = Some tcb")
   apply (clarsimp dest!:get_tcb_SomeD)
   apply (subgoal_tac "tcb = the (get_tcb thread s)")
    apply (subgoal_tac "etcb = the (get_etcb thread s)")
     apply simp
    apply (simp add: get_etcb_rev)
   apply (simp add:get_tcb_rev)+
  done

lemma select_f_store_word:
  "(select_f (storeWord p w ms)) = (do assert (p && mask 2 = 0);
    return ((),storeWord_ms p w ms) od)"
  apply (clarsimp simp: assert_def select_f_def storeWord_def bind_def fail_def simpler_modify_def
                        storeWord_ms_def return_def)
  done

lemma select_f_get_register:
  "(as_user thread (getRegister register)) =
    (do tcb\<leftarrow>gets_the (get_tcb thread);return (arch_tcb_get_registers (tcb_arch tcb) register) od)"
  apply (simp add: assert_opt_def as_user_def set_object_def get_object_def gets_the_def
                   a_type_def assert_def put_def select_f_def getRegister_def gets_def get_def
                   return_def bind_def)
  apply (rule ext)
  apply (case_tac "get_tcb thread s")
   apply (clarsimp simp: fail_def return_def)+
  apply (clarsimp simp: get_tcb_def arch_tcb_get_registers_def arch_tcb_context_get_def
                  split: option.splits Structures_A.kernel_object.splits)
  done

lemma select_f_evalMonad:
  "\<lbrakk>empty_fail g; empty_when_fail g; \<And>P. weak_det_spec P g; \<And>ms. \<lbrace>(=) ms\<rbrace>g\<lbrace>\<lambda>r. (=) ms\<rbrace>\<rbrakk>
  \<Longrightarrow> (select_f (g ms)) = (case (evalMonad g ms) of Some a \<Rightarrow> return (a,ms) | None \<Rightarrow> fail)"
  apply (rule ext)
  apply (clarsimp simp: return_def select_f_def fail_def empty_fail_def split:option.splits)
  apply (drule_tac x = ms in spec)
    apply (rule conjI)
    apply (clarsimp simp:evalMonad_def valid_def weak_det_spec_def)+
  apply (drule_tac x = "(=) ms" in meta_spec)+
  apply (clarsimp simp:no_fail_def empty_when_fail_def)
  apply (drule_tac x = ms in meta_spec)
  apply (clarsimp simp:det_spec_def)
  apply (drule_tac x = ms in spec)
  apply clarsimp
  done


lemma dcorres_store_word_safe:
  "within_page obuf ptr sz \<Longrightarrow>
   dcorres dc \<top>
    (ko_at (ArchObj (DataPage dev sz)) obuf and (\<lambda>s. \<forall>buf thread. ipc_frame_ptr_at buf thread s \<longrightarrow> buf\<noteq> obuf) and
    valid_objs and pspace_distinct and pspace_aligned and valid_etcbs)
    (return a)
    (do_machine_op (storeWord ptr b))"
  supply option.case_cong[cong]
  apply (rule dcorres_expand_pfx)
  apply (clarsimp simp: do_machine_op_def valid_def get_def gets_def bind_def return_def
                        simpler_modify_def corres_underlying_def)
  apply (clarsimp simp: select_f_store_word assert_def bind_def fail_def return_def
                  split: if_splits)
  apply (clarsimp simp: transform_def transform_current_thread_def)
  apply (rule ext)
  apply (rename_tac thread)
   apply (clarsimp simp:transform_objects_def restrict_map_def option_map_def map_add_def split:option.splits)
   apply (clarsimp simp:transform_object_def split:Structures_A.kernel_object.splits)
   apply (clarsimp simp:transform_tcb_def transform_full_intent_def Let_def)
   apply (clarsimp simp del:upt.simps
                   simp: Let_def get_tcb_mrs_def is_arch_page_cap_def
                   split:cap.split_asm arch_cap.split_asm
                   split del: if_split)
   apply (frule valid_tcb_objs, erule get_tcb_rev)
   apply (clarsimp simp: valid_tcb_def tcb_cap_cases_def valid_ipc_buffer_cap_def
               simp del: upt.simps)
   apply (erule disjE)
    apply (clarsimp simp: is_nondevice_page_cap_def split: cap.split_asm simp del: upt.simps)
    apply (rename_tac tcb arch_cap)
    apply (case_tac arch_cap)
        apply ((simp add:get_ipc_buffer_words_def)+)[2]
      apply (rename_tac word rights vmpage_size option)
      apply (simp add:Suc_leI[OF msg_registers_lt_msg_max_length] del:upt.simps)
      apply (frule_tac thread = thread and ptr = ptr and ms = "machine_state s'"
                   and tcb_type = tcb and b = b
                   and xs = "[Suc (length msg_registers)..<Suc msg_max_length]"
                    in get_ipc_buffer_words_helper)
                apply (erule get_tcb_rev)
               apply ((simp add:ipc_frame_wp_at_def obj_at_def)+)[2]
             apply (simp add:obj_at_def)
            apply (clarsimp simp: is_aligned_mask split: bool.split_asm simp del: upt.simps)+
        apply (rule_tac y = thread in within_page_ipc_buf)
              apply (simp add:ipc_frame_wp_at_def obj_at_def ipc_buffer_wp_at_def)+
        apply (simp add:msg_max_length_def msg_align_bits)
       apply (subgoal_tac "ipc_frame_ptr_at word thread s'")
        apply (drule_tac x = word in spec)
        apply clarsimp
       apply (clarsimp simp:ipc_frame_wp_at_def obj_at_def)

       apply (frule(1) valid_etcbs_tcb_etcb, clarsimp)

      apply (rule conjI)
       apply (frule_tac thread = thread and ptr = ptr and ms = "machine_state s'"
                    and tcb_type = tcb and b = b
                    and xs = "[buffer_cptr_index..<buffer_cptr_index +
                               unat (mi_extra_caps (get_tcb_message_info tcb))]"
                     in get_ipc_buffer_words_helper)
                 apply (erule get_tcb_rev)
                apply ((simp add:ipc_frame_wp_at_def obj_at_def is_aligned_mask)+)[7]
         apply (clarsimp simp del:upt.simps)
         apply (rule_tac sz = vmpage_size and y = thread in within_page_ipc_buf)
               apply (simp add:ipc_frame_wp_at_def obj_at_def ipc_buffer_wp_at_def)+
         apply (simp add:msg_max_length_def msg_align_bits buffer_cptr_index_def)
         apply (case_tac "get_tcb_message_info tcb")
         apply (clarsimp simp add: get_tcb_message_info_def data_to_message_info_def)
         apply (erule order_less_le_trans)
         apply (simp add: mask_def)
         apply (rule iffD1[OF word_le_nat_alt[where b = "0x6::word32",simplified]])
         apply (rule order_trans)
          apply (rule word_and_le1[where a = 3])
         apply simp
        apply (subgoal_tac "ipc_frame_ptr_at word thread s'")
         apply (drule_tac x = word in spec)
         apply clarsimp
        apply (clarsimp simp:ipc_frame_wp_at_def obj_at_def)
       apply simp
      apply (frule_tac thread = thread and ptr = ptr and sz = sz and ms = "machine_state s'"
                   and tcb_type = tcb and b = b
                   and xs = "[Suc (Suc (msg_max_length + msg_max_extra_caps))..<
                              5 + (msg_max_length + msg_max_extra_caps)]"
                    in get_ipc_buffer_words_helper)
                apply (erule get_tcb_rev)
               apply ((simp add:ipc_frame_wp_at_def is_aligned_mask obj_at_def)+)[7]
        apply (clarsimp simp del:upt.simps)
        apply (rule_tac y = thread and sz = vmpage_size in within_page_ipc_buf)
              apply (simp add:ipc_frame_wp_at_def obj_at_def ipc_buffer_wp_at_def)+
        apply (clarsimp simp:msg_align_bits msg_max_length_def msg_max_extra_caps_def)
       apply (subgoal_tac "ipc_frame_ptr_at word thread s'")
        apply (drule_tac x = word in spec)
        apply clarsimp
       apply (clarsimp simp:ipc_frame_wp_at_def obj_at_def)
      apply simp
     apply (clarsimp simp:get_ipc_buffer_words_def)+
  done

lemma store_word_corres:
  "within_page buf ptr sz \<Longrightarrow>
  dcorres dc \<top>
  (pspace_aligned and pspace_distinct and valid_objs and
  (ipc_frame_ptr_at buf s_id) and (ipc_frame_sz_at sz s_id) and valid_etcbs)
  (corrupt_frame buf) (do_machine_op (storeWord ptr b))"
  apply (case_tac "is_aligned ptr 2")
   apply (simp add: corrupt_frame_def)
   apply (simp add: do_machine_op_def gets_def)
   apply (rule dcorres_absorb_get_r)
   apply clarsimp
   apply (drule store_word_corres_helper[where s_id = s_id],simp+)
   apply (simp add:ipc_frame_wp_at_def obj_at_def)+
   apply clarsimp
   apply (rule corres_guard_imp)
     apply (rule_tac Q="(=) s'" and P =\<top> in select_pick_corres)
     apply (simp add: select_f_store_word bind_assoc)
     apply (clarsimp simp:assert_def corres_free_fail)
     apply (rule corres_modify, simp)
     apply (rule sym)
     apply simp+
  apply (clarsimp simp: do_machine_op_def gets_def)
  apply (rule dcorres_absorb_get_r)
  apply (rule corres_guard_imp)
    apply (clarsimp simp:select_f_def fail_def storeWord_def
                         is_aligned_mask assert_def
          |rule conjI)+
    apply (simp add:bind_def simpler_modify_def corres_free_fail[unfolded fail_def])+
  done

lemma store_word_offs_ipc_frame_wp:
  "\<lbrace>ipc_frame_wp_at P s_id\<rbrace> store_word_offs base a aa \<lbrace>\<lambda>rv. ipc_frame_wp_at P s_id\<rbrace>"
  by (wp | simp add: ipc_frame_wp_at_def store_word_offs_def)+

lemma zip_cpy_word_corres:
  "\<forall>x\<in> set xs. within_page buf (base + of_nat(x*word_size)) sz
    \<Longrightarrow> dcorres dc \<top>
   (pspace_aligned and pspace_distinct and valid_objs
    and (ipc_frame_ptr_at buf s_id) and (ipc_frame_sz_at sz s_id) and valid_etcbs)
   (corrupt_frame buf)
   (mapM (\<lambda>x. load_word_offs src_a x >>= store_word_offs base x)
            xs)"
 proof (induct xs)
   case Nil
   show ?case
     apply (rule corres_guard_imp)
     apply (clarsimp simp:mapM_def sequence_def)
     apply (rule dcorres_dummy_corrupt_frame[THEN corres_guard_imp,unfolded dc_def])
   apply simp+
   done
 next
   case (Cons x xs)
   show ?case
     apply (subst corrupt_frame_duplicate[symmetric])
     apply (rule corres_guard_imp)
       apply (clarsimp simp:mapM_Cons)
       apply (rule corres_split)
          apply (rule corres_symb_exec_r)
             apply (simp add: store_word_offs_def bind_assoc[symmetric]
                              state_assert_def[symmetric])
             apply (rule corres_state_assert)
              apply (rule_tac s_id = s_id and sz = sz in store_word_corres)
              using Cons.prems
              apply simp
             using Cons.prems
             apply (clarsimp simp: within_page_def in_user_frame_def)
             apply (thin_tac "Ball S P" for S P)
             apply (rule_tac x=sz in exI)
             apply (frule (2) ipc_frame_ptr_at_frame_at)
             apply (simp add: obj_at_def a_type_simps)
            apply wp+
          apply clarsimp+
         apply (rule corres_dummy_return_l)
         apply (rule corres_split)
            apply (rule Cons.hyps)
            using Cons
            apply clarsimp
           apply (rule corres_free_return[where P = \<top> and P'=\<top> ])
          apply wp+
        apply (wp store_word_offs_ipc_frame_wp)+
     by (fastforce simp:ipc_frame_wp_at_def)+
 qed

lemma zip_store_word_corres:
  "\<forall>x\<in> set xs. within_page buf (base + of_nat (x * word_size)) sz \<Longrightarrow>
   dcorres dc \<top>
   (pspace_aligned and pspace_distinct and valid_objs
    and (ipc_frame_sz_at sz s_id) and (ipc_frame_ptr_at buf s_id) and valid_etcbs)
   (corrupt_frame buf)
   (zipWithM_x (store_word_offs base) xs ys)"
  apply (clarsimp simp:zipWithM_x_mapM_x split del: if_split)
  apply (induct xs arbitrary: ys)
   apply (clarsimp simp: mapM_x_Cons)
   apply (clarsimp simp: mapM_x_Nil)
   apply (rule corres_guard_imp[OF dcorres_dummy_corrupt_frame])
    apply (simp+)[2]
  apply (case_tac ys)
   apply (clarsimp simp: mapM_x_Cons mapM_x_Nil)
   apply (rule corres_guard_imp[OF dcorres_dummy_corrupt_frame])
    apply clarsimp+
  apply (subst mapM_x_Cons)
  apply clarify
  apply (subst corrupt_frame_duplicate[symmetric])
  apply (rule corres_guard_imp)
    apply (rule corres_split[where P="\<top>" and r'="dc"])
       apply (clarsimp simp:store_word_offs_def)
       apply (simp add: store_word_offs_def bind_assoc[symmetric] state_assert_def[symmetric])
       apply (rule corres_state_assert)
        apply (rule_tac s_id = s_id and sz = sz in store_word_corres)
        apply simp
       apply (clarsimp simp: within_page_def in_user_frame_def)
       apply (rule_tac x=sz in exI)
       apply (frule (2) ipc_frame_ptr_at_frame_at)
       apply (simp add: obj_at_def a_type_simps)
      apply clarsimp
      apply (drule allI)
      apply (drule_tac x = list in spec)
      apply simp
     apply (wp store_word_offs_ipc_frame_wp)+
   apply clarsimp+
  done

lemma ex_cte_cap_wp_to_not_idle:
  "\<lbrakk> ex_cte_cap_wp_to P r s; valid_global_refs s; valid_objs s;
             valid_idle s; valid_irq_node  s\<rbrakk>
         \<Longrightarrow> not_idle_thread (fst r) s"
  apply (clarsimp simp:ex_cte_cap_wp_to_def)
  apply (simp add:valid_global_refs_def valid_refs_def not_idle_thread_def)
  apply (drule_tac x = a in spec, drule_tac x = b in spec)
  apply (clarsimp simp:global_refs_def cte_wp_at_cases dest!:get_tcb_SomeD split:if_splits)
  apply (erule disjE)
   apply clarsimp
   apply (case_tac cap)
              apply (clarsimp simp:cap_range_def)+
     apply (rename_tac word)
     apply (clarsimp simp:valid_idle_def valid_irq_node_def)
     apply (drule_tac x = word in spec)
     apply (clarsimp simp:pred_tcb_at_def obj_at_def is_cap_table_def)
    apply (clarsimp simp:cap_range_def)+
  apply (case_tac "get tcb")
             apply clarsimp+
    apply (rename_tac word)
    apply (clarsimp simp:valid_idle_def valid_irq_node_def)
    apply (drule_tac x = word in spec)
    apply (clarsimp simp:st_tcb_at_def pred_tcb_at_def obj_at_def is_cap_table_def)
   apply clarsimp+
  done

lemma pspace_aligned_set_cxt_mrs[wp]:
  "\<lbrace>ko_at (TCB tcb) thread and pspace_aligned\<rbrace>
     KHeap_A.set_object thread (TCB (tcb_arch_update (tcb_context_update f) tcb))
   \<lbrace>\<lambda>rv. pspace_aligned\<rbrace>"
  apply (wp set_object_aligned)
  apply (clarsimp simp:obj_at_def)
  done

lemma pspace_distinct_set_cxt_mrs[wp]:
  "\<lbrace>ko_at (TCB tcb) thread and pspace_distinct\<rbrace>
     KHeap_A.set_object thread (TCB (tcb_arch_update (tcb_context_update f) tcb))
   \<lbrace>\<lambda>rv. pspace_distinct\<rbrace>"
  apply (wp set_object_distinct)
  apply (clarsimp simp:obj_at_def)
  done


lemma valid_objs_set_cxt_mrs[wp]:
  "\<lbrace>ko_at (TCB tcb) thread and valid_objs\<rbrace>
     KHeap_A.set_object thread (TCB (tcb_arch_update (tcb_context_update f) tcb))
   \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (wp set_object_valid_objs)
  apply (clarsimp simp:obj_at_def)
  apply (clarsimp simp:valid_objs_def)
  apply (drule_tac x=thread in bspec)
   apply (clarsimp simp:dom_def)
  apply (clarsimp simp:valid_obj_def valid_tcb_def)
  apply (drule_tac x="(a,aa,b)" in bspec)
   apply simp
  apply (clarsimp simp:tcb_cap_cases_def)
  apply (erule disjE|clarsimp)+
  done

lemma ipc_frame_set_cxt_mrs[wp]:
  "\<lbrace>ko_at (TCB tcb) thread and ipc_frame_wp_at P a\<rbrace>
     KHeap_A.set_object thread (TCB (tcb_arch_update (tcb_context_update f) tcb))
   \<lbrace>\<lambda>rv. ipc_frame_wp_at P a\<rbrace>"
  by (clarsimp simp: KHeap_A.set_object_def get_object_def get_def put_def bind_def valid_def
                       return_def obj_at_def ipc_frame_wp_at_def in_monad)

lemma ipc_buffer_set_cxt_mrs[wp]:
  "\<lbrace>ko_at (TCB tcb) thread and ipc_buffer_wp_at P a\<rbrace>
     KHeap_A.set_object thread (TCB (tcb_arch_update (tcb_context_update f) tcb))
   \<lbrace>\<lambda>rv. ipc_buffer_wp_at P a\<rbrace>"
  by (clarsimp simp: KHeap_A.set_object_def get_object_def get_def put_def bind_def valid_def
                       return_def obj_at_def ipc_buffer_wp_at_def in_monad)

lemmas [wp] =  abs_typ_at_lifts[OF do_machine_op_obj_at]

lemma set_object_valid_etcbs: "\<lbrace>valid_etcbs and (\<lambda>s. kheap s ptr = Some (TCB tcba))\<rbrace>
                KHeap_A.set_object ptr (TCB tcbb)
              \<lbrace>\<lambda>rv. valid_etcbs\<rbrace>"
  apply (clarsimp simp: set_object_def get_object_def)
  apply wp
  apply (auto simp: valid_etcbs_def st_tcb_at_def obj_at_def is_etcb_at_def st_tcb_at_kh_def obj_at_kh_def)
  done

lemma set_mrs_corres:
  "dcorres dc \<top>
   (valid_idle and valid_objs and pspace_aligned and pspace_distinct and not_idle_thread y
     and ipc_frame_ptr_at buf y and ipc_frame_sz_at sz y and ipc_buffer_wp_at bptr y and valid_etcbs)
   (do corrupt_tcb_intent y;corrupt_frame buf od)
   (set_mrs y (Some (buf + (bptr && mask (pageBitsForSize sz)))) b)"
  apply (simp add:set_mrs_def arch_tcb_update_aux3 arch_tcb_set_registers_def del:upt.simps)
  apply (rule dcorres_absorb_gets_the)
  apply (rule corres_guard_imp)
    apply (rule corres_split [where r'=dc])
       apply (clarsimp, drule(1) valid_etcbs_get_tcb_get_etcb)
       apply (rule_tac s'=s' in set_cxt_none_det_intent_corres'; clarsimp)
        apply (clarsimp dest!: get_tcb_SomeD)
       apply (clarsimp dest!: get_etcb_SomeD)
      apply (rule corres_dummy_return_l)
      apply (rule corres_split[where r'=dc and R'="%x. \<top>" and R="%x. \<top>"])
         apply (rule_tac s_id = y and sz = sz in zip_store_word_corres)
         apply (clarsimp simp del:upt.simps)
         apply (rule within_page_ipc_buf)
               apply ((simp add:msg_align_bits msg_max_length_def)+)[7]
        apply (rule corres_free_return)
       apply wp+
    apply (wp set_object_valid_etcbs)
   apply (simp del:upt.simps)
  apply (auto dest!:get_tcb_SomeD simp:obj_at_def ipc_frame_wp_at_def arch_tcb_get_registers_def)
  done

lemma set_registers_ipc_frame_ptr_at[wp]:
  "\<lbrace>ipc_frame_wp_at buf y\<rbrace>as_user thread (setRegister r rv) \<lbrace>%x. ipc_frame_wp_at buf y\<rbrace>"
  apply (clarsimp simp: as_user_def select_f_def
                        arch_tcb_update_aux3 arch_tcb_context_set_def
                        setRegister_def simpler_modify_def)
  apply wp
     apply clarsimp
     apply wp
    apply (clarsimp simp:valid_def)
    apply (assumption)
   apply wp
  apply clarsimp
  done

lemma set_registers_ipc_buffer_ptr_at[wp]:
  "\<lbrace>ipc_buffer_wp_at buf y\<rbrace>as_user thread (setRegister r rv) \<lbrace>%x. ipc_buffer_wp_at buf y\<rbrace>"
  apply (clarsimp simp: as_user_def
                        select_f_def
                        setRegister_def
                        arch_tcb_update_aux3 arch_tcb_context_set_def
                        simpler_modify_def)
  apply wp
    apply clarsimp
    apply wp
   apply (clarsimp simp:valid_def)
   apply (assumption)
  apply wp
  apply clarsimp
  done


lemma copy_mrs_corres:
  "valid_message_info mi \<Longrightarrow>
   dcorres dc \<top> ((valid_idle and valid_objs and pspace_aligned and pspace_distinct and not_idle_thread y
     and ipc_frame_ptr_at buf y and ipc_frame_sz_at sz y and ipc_buffer_wp_at bptr y and valid_etcbs))
    (do corrupt_tcb_intent y;corrupt_frame buf od)
    (copy_mrs thread rv y (Some (buf + (bptr && mask (pageBitsForSize sz))))
               (mi_length mi))"
  supply option.case_cong[cong]
  apply (simp add:copy_mrs_def del:upt.simps)
  apply (rule dcorres_expand_pfx)
  apply (rule corres_guard_imp)
    apply (rule corres_split[where r'="dc"])
       apply (rule set_registers_corres)
      apply (wpc)
       apply (rule corres_dummy_return_l)
       apply (rule corres_split[where r'="dc"])
          apply (rule dcorres_dummy_corrupt_frame)
         apply (rule corres_free_return[where P="\<top>" and P'="\<top>"])
        apply wp
       apply (clarify,simp del:upt.simps )
      apply (rule corres_dummy_return_l)
      apply (rule corres_split[where r'="dc"])
         apply (rule_tac s_id = y and sz = sz in zip_cpy_word_corres)
         apply (clarsimp simp del:upt.simps)
         apply (rule within_page_ipc_buf)
               apply simp+
         apply (clarsimp simp:msg_align_bits valid_message_info_def msg_max_length_def)
         apply (erule less_trans)
         apply (rule le_less_trans[where y =  "Suc (unat (0x78))"])
          apply (rule iffD2[OF Suc_le_mono])
          apply (erule iffD1[OF word_le_nat_alt])
         apply simp
        apply (rule corres_free_return[where P="\<top>" and P'="\<top>"])
       apply wp+
     apply ((clarsimp|wp)+)[1]
    apply (rule mapM_wp_inv)
    apply (case_tac rv)
     apply clarsimp
     apply wp
    apply (clarsimp|rule conjI)+
    apply ((wp|clarsimp)+)[3]
  apply (case_tac rv)
   apply (fastforce simp: ipc_buffer_wp_at_def obj_at_def tcb_at_def)+
  done

lemmas transform_cap_simps [simp] = transform_cap_def [split_simps cap.split arch_cap.split]

lemma corrupt_frame_include_self:
  assumes corres:"dcorres dc \<top> P (do corrupt_tcb_intent y;corrupt_frame buf od) g"
  assumes imp:"\<And>s. P s\<Longrightarrow> ipc_frame_ptr_at buf y s \<and> not_idle_thread y s \<and> valid_etcbs s"
  shows "dcorres dc \<top> P (corrupt_frame buf) g"
  using corres
  supply option.case_cong[cong]
  apply (clarsimp simp:corres_underlying_def)
  apply (frule imp)
  apply (erule allE, erule (1) impE)
  apply (drule_tac x = "(a,ba)" in bspec)
   apply simp+
  apply (clarsimp simp:bind_def)
  apply (rule_tac x = "((),transform ba)" in bexI)
   apply simp
  apply (clarsimp simp:corrupt_tcb_intent_def bind_def)
  apply (clarsimp simp:update_thread_def gets_the_def gets_def get_def bind_def in_monad)
  apply (clarsimp simp:ipc_frame_wp_at_def obj_at_def)
  apply (clarsimp split:cap.splits arch_cap.splits)
  apply (clarsimp simp:select_def KHeap_D.set_object_def simpler_modify_def)
  apply (clarsimp simp:corrupt_frame_def bind_def select_def)
  apply (clarsimp simp:simpler_modify_def corrupt_intents_def)
  apply (drule(1) valid_etcbs_tcb_etcb, clarsimp)
  apply (subst(asm) opt_object_tcb)
     apply (erule get_tcb_rev)
    apply (erule get_etcb_rev)
   apply (simp add:not_idle_thread_def)
  apply (clarsimp simp:transform_tcb_def in_monad set_object_def)
  apply (rule_tac x = x in exI)
  apply (clarsimp simp:transform_def KHeap_D.set_object_def simpler_modify_def)
  apply (case_tac "transform b")
  apply (clarsimp simp:transform_def map_add_def)
  apply (rule ext)
  apply (drule_tac x = xa in fun_cong)
  apply (case_tac xa)
  apply (clarsimp simp:not_idle_thread_def tcb_ipcframe_id_def restrict_map_def transform_objects_def
                  split: if_split)
  apply (clarsimp dest!:get_tcb_rev simp: transform_objects_tcb tcb_ipcbuffer_slot_def
                        tcb_pending_op_slot_def tcb_boundntfn_slot_def)
  apply (clarsimp simp: tcb_ipcbuffer_slot_def tcb_ipcframe_id_def | rule conjI)+
  apply (clarsimp simp:transform_def transform_object_def transform_tcb_def tcb_ipcframe_id_def
        tcb_ipcbuffer_slot_def tcb_pending_op_slot_def tcb_boundntfn_slot_def dest!:get_tcb_SomeD)
  done

lemma corrupt_frame_include_self':
assumes corres:"dcorres dc \<top> P (do corrupt_frame buf; corrupt_tcb_intent y od) g"
assumes imp:"\<And>s. P s\<Longrightarrow> ipc_frame_ptr_at buf y s \<and> not_idle_thread y s \<and> valid_etcbs s"
shows "dcorres dc \<top> P (corrupt_frame buf) g"
  using corres
  apply (clarsimp simp:corres_underlying_def bind_def)
  apply (frule imp)
  apply (erule allE, erule (1) impE)
  apply (drule_tac x = "(a,ba)" in bspec)
   apply simp+
  apply (clarsimp)
  apply (rule_tac x = "((),transform ba)" in bexI)
   apply simp+
  apply (clarsimp simp:corrupt_frame_def select_def bind_def simpler_modify_def)
  apply (clarsimp simp:corrupt_tcb_intent_def update_thread_def
    select_def gets_the_def KHeap_D.set_object_def
    bind_def gets_def get_def return_def assert_opt_def
    fail_def simpler_modify_def split:option.splits)
  apply (rule_tac x = "\<lambda>t. if t = y then T else x t" for T in exI)
  apply (clarsimp simp:corrupt_intents_def transform_def not_idle_thread_def
                       restrict_map_def map_add_def ipc_frame_wp_at_def obj_at_def
                  split:option.split_asm cdl_object.split_asm)
   apply (rule ext)
   apply (clarsimp simp:ipc_frame_wp_at_def obj_at_def tcb_ipcframe_id_def tcb_pending_op_slot_def
                        transform_object_def not_idle_thread_def transform_tcb_def tcb_ipcbuffer_slot_def)
   apply (clarsimp simp: transform_objects_def)
   apply (clarsimp split:cap.splits arch_cap.splits)
   apply (drule(1) valid_etcbs_tcb_etcb)
  by (fastforce simp: transform_tcb_def tcb_ipcframe_id_def tcb_pending_op_slot_def
                      tcb_ipcbuffer_slot_def tcb_boundntfn_slot_def)+

lemma dcorres_set_mrs:
  "dcorres dc \<top>
   (valid_idle and valid_objs and pspace_aligned and pspace_distinct and not_idle_thread y
     and ipc_frame_ptr_at buf y and ipc_frame_sz_at sz y and ipc_buffer_wp_at bptr y and valid_etcbs)
   (corrupt_frame buf)
             (set_mrs y (Some (buf + (bptr && mask (pageBitsForSize sz)))) b)"
  apply (rule corrupt_frame_include_self)
   apply (rule corres_guard_imp[OF set_mrs_corres])
    apply clarsimp+
  done

lemma dcorres_copy_mrs:
  "valid_message_info mi \<Longrightarrow>
   dcorres dc \<top> ((valid_idle and valid_objs and pspace_aligned and pspace_distinct and not_idle_thread y
     and ipc_frame_ptr_at buf y and ipc_frame_sz_at sz y and ipc_buffer_wp_at bptr y and valid_etcbs))
    (corrupt_frame buf)
    (copy_mrs thread rv y (Some (buf + (bptr && mask (pageBitsForSize sz))))
               (mi_length mi))"
  apply (rule corrupt_frame_include_self)
   apply (rule corres_guard_imp[OF copy_mrs_corres])
     apply auto
  done

lemma ipc_frame_ptr_at_sz_at:
  "\<lbrakk>ko_at (ArchObj (DataPage dev sz)) obuf s; valid_objs s;ipc_frame_ptr_at obuf thread s \<rbrakk> \<Longrightarrow> ipc_frame_sz_at sz thread s"
  apply (clarsimp simp:ipc_frame_wp_at_def obj_at_def)
  apply (clarsimp split:cap.splits arch_cap.splits)
  apply (frule valid_tcb_objs)
   apply (erule get_tcb_rev)
  apply (subgoal_tac "valid_cap (tcb_ipcframe tcb) s")
   apply (clarsimp simp: valid_cap_def obj_at_def split: if_splits)
  apply (clarsimp simp: valid_tcb_def tcb_cap_cases_def split: if_splits)
  done

lemma dcorres_store_word_conservative:
  " within_page obuf ptr sz \<Longrightarrow>
    dcorres dc (\<lambda>_. True)
     (ko_at (ArchObj (DataPage dev sz)) obuf and valid_objs and
      pspace_distinct and
      pspace_aligned and valid_etcbs)
     (corrupt_frame obuf) (do_machine_op (storeWord ptr b))"
  apply (rule dcorres_expand_pfx,clarsimp)
  apply (case_tac "\<forall>buf. (\<exists>thread. ipc_frame_ptr_at buf thread s') \<longrightarrow> buf \<noteq> obuf")
   apply (rule corres_dummy_return_pl[where b="()"])
   apply (rule corres_dummy_return_r)
   apply (rule corres_guard_imp)
     apply (rule corres_split[where r'=dc])
        apply (erule dcorres_store_word_safe)
       apply simp
       apply (rule dcorres_dummy_corrupt_frame)
      apply wp+
    apply simp
   apply simp
  apply (clarsimp)
  apply (frule ipc_frame_ptr_at_sz_at,simp+)
  apply (rule corres_guard_imp[OF store_word_corres])
    apply simp+
  done

end

end
