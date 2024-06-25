(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
 * Proofs of the frame rules for leaf functions of the kernel.
 *
 * The frame rule for a function is the rule that shows the
 * function affects only local state.
 *
 *)

theory Frame_SD
imports Separation_SD
begin

(***********************************
 * Frame rules for leaf functions. *
 ***********************************)

lemma dom_object_to_sep_state:
  "dom (object_to_sep_state ptr obj cmp) = {ptr} \<times> cmp"
  apply (clarsimp simp: object_to_sep_state_def split:if_splits)
  apply (auto simp:object_project_def split:if_splits cdl_component_id.splits)
  done

lemma object_to_sep_state_restrict:
  "object_to_sep_state obj_id obj M |` ({obj_id} \<times> m) = object_to_sep_state obj_id obj (M \<inter> m)"
  by (rule ext,
    clarsimp simp:object_to_sep_state_def restrict_map_def
    split:if_splits)

lemma object_to_sep_state_add:
  "\<lbrakk>{obj_id} \<times> m \<inter> dom M = {};b\<in> m\<rbrakk> \<Longrightarrow>
   (object_to_sep_state obj_id obj m ++ M) (obj_id, b)
   = Some (object_project b obj)"
  apply (subgoal_tac "(obj_id, b)\<in> {obj_id} \<times> m")
  apply (drule(1) inter_empty_not_both)
   apply (clarsimp simp:object_to_sep_state_def map_add_def dom_def)
  apply fastforce
  done

lemma singleton_intersect:
  "({x} \<times> UNIV \<inter> A = {}) = (\<forall>y. (x,y) \<notin> A)"
  by blast


lemma set_object_wp:
  "\<lbrace>< (obj_id \<mapsto>o -) \<and>* R>\<rbrace>
   set_object obj_id obj
   \<lbrace>\<lambda>rv. <obj_id \<mapsto>o obj \<and>* R>\<rbrace>"
  apply (clarsimp simp: set_object_def sep_state_projection_def)
  apply wp
  apply (clarsimp simp: sep_conj_def)
  apply (simp add:sep_map_o_def sep_map_general_def)
  apply (rule_tac x = "SepState (object_to_sep_state obj_id obj UNIV) Map.empty" in exI)
  apply (rule_tac x=y in exI)
  apply (clarsimp simp: plus_sep_state_def sep_disj_sep_state_def
    sep_state_disj_def sep_any_def map_disj_def
    sep_map_o_def sep_map_general_def)
  apply (frule disjoint_subset[OF
    dom_map_restrict,rotated,where a1 = "{obj_id} \<times> UNIV"])
  apply (clarsimp simp:dom_object_to_sep_state object_to_sep_state_restrict)
  apply (clarsimp simp:sep_state_add_def)
  apply (rule ext, rename_tac sep_id)
  apply (case_tac sep_id, rename_tac ptr component, clarsimp)
  apply (clarsimp simp:object_to_sep_state_add)
  apply (clarsimp simp:object_to_sep_state_def)
  apply (drule_tac x = "(ptr,component)" in fun_cong)+
  apply (simp add:map_add_def)
  apply (clarsimp split:option.splits)
  done

lemma object_eqI:
  "\<lbrakk>object_wipe_slots obj = object_wipe_slots obj'; object_slots obj = object_slots obj'\<rbrakk>
  \<Longrightarrow> obj = obj'"
  by (simp add: object_slots_def object_wipe_slots_def update_slots_def
                cdl_tcb.splits cdl_cnode.splits
         split: cdl_object.splits)

lemma disjoint_union_diff:
  "a \<inter> b = {} \<Longrightarrow> a \<union> b - a = b"
  by auto

lemma intent_reset_update_slots_single:
  "intent_reset (update_slots ((object_slots obj)(slot \<mapsto> cap)) obj)
  = update_slots ((object_slots (intent_reset obj))(slot \<mapsto> cap)) (intent_reset obj)"
  by simp

lemma object_clean_update_slots_single:
  "object_clean (update_slots ((object_slots obj)(slot \<mapsto> cap)) obj)
  = update_slots ((object_slots (object_clean obj))(slot \<mapsto> reset_cap_asid cap)) (object_clean obj)"
  by (auto simp: object_clean_def intent_reset_def asid_reset_def
                 update_slots_def object_slots_def fun_eq_iff
          split: cdl_object.splits)

lemma ptr_in_obj_to_sep_dom:
  "(ptr,Slot y) \<in> dom (object_to_sep_state ptr obj {Slot y})"
  by (simp add:dom_object_to_sep_state)

lemma sep_any_exist:
  "( sep_any m p \<and>* R ) s = (\<exists>x. ( m p x \<and>* R ) s)"
  by (auto simp:sep_state_projection_def
    sep_any_def sep_conj_def)

lemma sep_map_c_conj:
  "(ptr \<mapsto>c cap \<and>* R) s =
  (let slot = (fst ptr,Slot (snd ptr))
  in (sep_heap s) slot  = Some (CDL_Cap (Some (reset_cap_asid cap))) \<and>
     R (SepState ((sep_heap s)(slot:= None)) (sep_irq_node s)))"
  apply (clarsimp simp:sep_conj_def Let_def plus_sep_state_def sep_state_add_def)
  apply (rule iffI)
   apply (clarsimp simp:sep_map_c_def sep_disj_sep_state_def
     sep_map_general_def sep_state_disj_def map_disj_def)
   apply (subst object_to_sep_state_add)
    apply (simp add:dom_object_to_sep_state singleton_iff)+
   apply (simp add:object_project_def object_slots_object_clean)
   apply (erule arg_cong[where f = R,THEN iffD1,rotated])
   apply (case_tac y)
    apply simp
    apply (rule ext)
    apply (clarsimp simp: dom_def map_add_def object_to_sep_state_def
                   split: if_split_asm option.splits)
  apply (clarsimp simp:sep_map_c_def)
  apply (rule_tac x = "SepState [(fst ptr,Slot (snd ptr))\<mapsto> (CDL_Cap (Some (reset_cap_asid cap)))]
                                Map.empty" in exI)
  apply (rule_tac x = "(SepState ((sep_heap s)((fst ptr,Slot (snd ptr)):= None)))
                                 (sep_irq_node s) " in exI)
  apply (clarsimp simp: sep_map_c_def sep_disj_sep_state_def
                        sep_map_general_def sep_state_disj_def map_disj_def)
  apply (intro conjI)
   apply (case_tac s,simp)
   apply (rule ext)
   apply (clarsimp simp:map_add_def split:option.splits)
  apply (clarsimp simp:object_to_sep_state_def split:if_splits)
  apply (rule_tac x = "CNode \<lparr>cdl_cnode_caps = [slot\<mapsto> cap],
    cdl_cnode_size_bits = of_nat slot\<rparr>" in exI)
  apply (clarsimp simp:object_slots_def)
  apply (rule ext)
  apply (clarsimp simp:object_project_def object_slots_def
    object_clean_def asid_reset_def update_slots_def
    intent_reset_def split:if_splits option.splits)
  done

lemma sep_map_f_conj:
  "(ptr \<mapsto>f obj \<and>* R) s =
  (let slot = (ptr,Fields)
  in (sep_heap s) slot  = Some (CDL_Object (object_wipe_slots (object_clean obj))) \<and>
     R (SepState ((sep_heap s)(slot:= None)) (sep_irq_node s)))"
  apply (clarsimp simp:sep_conj_def Let_def plus_sep_state_def sep_state_add_def)
  apply (rule iffI)
   apply (clarsimp simp:sep_map_f_def sep_disj_sep_state_def
     sep_map_general_def sep_state_disj_def map_disj_def)
   apply (subst object_to_sep_state_add)
    apply (simp add:dom_object_to_sep_state singleton_iff)+
   apply (simp add:object_project_def)
   apply (erule arg_cong[where f = R,THEN iffD1,rotated])
   apply (case_tac y)
   apply simp
   apply (rule ext)
   apply (clarsimp simp:dom_def map_add_def
     object_to_sep_state_def split:if_splits option.splits)
  apply (clarsimp simp:sep_map_c_def)
  apply (rule_tac x = "SepState [(ptr,Fields) \<mapsto> CDL_Object (object_wipe_slots (object_clean obj))]
                                Map.empty" in exI)
  apply (rule_tac x = "SepState ((sep_heap s)((ptr,Fields):= None))
                                (sep_irq_node s)" in exI)
  apply (clarsimp simp:sep_map_f_def sep_disj_sep_state_def
     sep_map_general_def sep_state_disj_def map_disj_def)
  apply (intro conjI)
   apply (case_tac s,simp)
   apply (rule ext)
   apply (clarsimp simp:map_add_def split:option.splits)
  apply (clarsimp simp:object_to_sep_state_def split:if_splits)
  apply (rule ext)
  apply (clarsimp simp:object_project_def split:if_splits)
  done

lemma object_project_slot:
  "object_project (Slot slot) obj =
   CDL_Cap (object_slots (object_clean obj) slot)"
  by (clarsimp simp:object_project_def)

lemma intent_reset_has_slots:
  "intent_reset obj = intent_reset obj' \<Longrightarrow> has_slots obj = has_slots obj'"
  by (clarsimp simp:intent_reset_def  has_slots_def
    split:cdl_object.splits)

lemma asid_reset_has_slots:
  "asid_reset obj = asid_reset obj' \<Longrightarrow>
    has_slots obj = has_slots obj'"
  by (clarsimp simp:asid_reset_def
    has_slots_def update_slots_def
    split:cdl_object.splits)

lemma object_clean_has_slots:
  "object_clean obj = object_clean obj' \<Longrightarrow> has_slots obj = has_slots obj'"
  by (clarsimp simp:object_clean_def2
    dest!: asid_reset_has_slots intent_reset_has_slots)

lemma set_object_slot_wp_helper:
 "\<lbrace>\<lambda>s. <(obj_id, slot) \<mapsto>c - \<and>* R> s \<and> cdl_objects s obj_id = Some obj
  \<and> object_clean obj = object_clean obj'\<rbrace>
  set_object obj_id (update_slots ((object_slots obj') (slot \<mapsto> cap)) obj')
  \<lbrace>\<lambda>rv. <(obj_id, slot) \<mapsto>c cap \<and>* R>\<rbrace>"
  apply (clarsimp simp: set_object_def sep_any_def)
  apply wp
  apply (clarsimp simp: sep_map_c_conj sep_conj_exists Let_def)
  apply (clarsimp simp: lift_def sep_state_projection_def
    sep_conj_def object_project_slot object_slots_object_clean)
  apply (case_tac "has_slots obj")
   apply (frule object_clean_has_slots)
   apply (simp add: object_slots_update_slots[where obj' = obj'])
   apply (erule arg_cong[where f = R,THEN iffD1,rotated])
   apply clarsimp
   apply (rule ext)
   apply (clarsimp split: if_splits option.splits)
   apply (clarsimp simp: object_project_def object_wipe_slots_def
                         object_slots_object_clean object_clean_update_slots_single
                         fun_upd_def[symmetric]
                  split: cdl_component_id.splits if_splits)
  apply (frule object_clean_has_slots)
  apply (clarsimp simp: has_slots_def object_clean_update_slots_single
                 split: option.splits)
  done

lemma set_object_slot_wp:
 "\<lbrace>\<lambda>s. <(obj_id, slot) \<mapsto>c - \<and>* R> s \<and>
       cdl_objects s obj_id = Some obj \<and>
       (\<exists>obj'. object_clean obj = object_clean obj' \<and>
       nobj = (update_slots ((object_slots obj') (slot \<mapsto> cap)) obj'))\<rbrace>
  set_object obj_id nobj
  \<lbrace>\<lambda>rv. <(obj_id, slot) \<mapsto>c cap \<and>* R>\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply clarsimp
  apply (rule hoare_weaken_pre)
   apply (rule set_object_slot_wp_helper)
  apply auto
  done

lemma object_wipe_slots_object_clean:
  "object_wipe_slots (object_clean obj) = object_clean (object_wipe_slots obj)"
  apply (case_tac obj, simp_all add: object_wipe_slots_def object_clean_def
                       intent_reset_def asid_reset_def update_slots_def object_slots_def)
  done

lemma object_wipe_slots_intent_reset:
  "object_wipe_slots (intent_reset obj) = intent_reset (object_wipe_slots obj)"
  by (case_tac obj,simp_all add:object_wipe_slots_def update_slots_def intent_reset_def)

abbreviation
  "tcb_at' P ptr s \<equiv> object_at (\<lambda>obj. \<exists>tcb. obj = Tcb tcb \<and> P tcb) ptr s"

lemma sep_map_f_tcb_at:
  "\<lbrakk><ptr \<mapsto>f tcb \<and>* R> s ; is_tcb tcb\<rbrakk>
  \<Longrightarrow> tcb_at'
  (\<lambda>t. object_clean (object_wipe_slots (Tcb t)) = object_clean (object_wipe_slots tcb))
  ptr s"
  apply (simp add:sep_state_projection_def)
  apply (clarsimp simp:sep_map_f_conj
    object_project_def is_tcb_def
    split:option.splits cdl_object.splits)
  apply (rename_tac cdl_tcb z)
  apply (case_tac z,
         simp_all add: object_wipe_slots_def object_clean_def asid_reset_def
                       update_slots_def intent_reset_def)
  apply (simp add: object_at_def object_slots_def object_wipe_slots_def
                   update_slots_def)
  apply (rename_tac cdl_tcb')
  apply (case_tac cdl_tcb)
  apply (case_tac cdl_tcb')
  apply clarsimp
  done

lemma object_slots_update_slots_empty [simp]:
  "object_slots (update_slots Map.empty object) = Map.empty"
  by (case_tac "has_slots object", simp_all)

lemma set_object_cdl_field_wp:
  assumes slot: "object_slots obj_n = object_slots obj"
  and type: "object_type obj_n = object_type obj"
            "object_type obj_np = object_type obj"
            "object_type obj_p = object_type obj"
  and fields: "object_wipe_slots (object_clean obj_np) = object_wipe_slots (object_clean obj_n)"
  shows
  "\<lbrace>\<lambda>s. <obj_id \<mapsto>f obj_p \<and>* R> s \<and> object_at ((=) obj) obj_id s\<rbrace>
  set_object obj_id obj_n
  \<lbrace>\<lambda>rv. <obj_id \<mapsto>f obj_np \<and>* R>\<rbrace>"
  apply (clarsimp simp: set_object_def)
  apply wp
  apply (clarsimp simp: sep_state_projection_def sep_map_f_conj)
  apply (rule conjI)
   apply (simp add:object_project_def)
   apply (rule object_eqI)
    apply (cut_tac fields)
    apply (simp add:object_wipe_slots_object_clean)
   apply (rule ext)
   apply (simp add:object_wipe_slots_def type)
  apply (erule arg_cong[where f = R, THEN iffD1,rotated])
  apply (clarsimp simp: object_at_def)
  apply (rule ext)
  apply (clarsimp split:if_splits option.splits)
  apply (cut_tac slot)
  apply (rule ccontr)
  apply (clarsimp simp: object_project_def object_slots_object_clean
                 split: cdl_component_id.splits)
  done

lemma set_cap_wp:
  "\<lbrace>\<lambda>s. <ptr \<mapsto>c - \<and>* R> s\<rbrace>
    set_cap ptr cap
   \<lbrace>\<lambda>rv s. <ptr \<mapsto>c cap \<and>* R> s\<rbrace>"
  apply (clarsimp simp: set_cap_def)
  apply (case_tac ptr, rename_tac obj_id slot, clarsimp)
  apply (wp|wpc)+
     apply (rule_tac obj = obj in set_object_slot_wp)
    apply (wp |wpc)+
  apply clarsimp
  apply (clarsimp simp: update_slots_def has_slots_def
                 split: cdl_object.splits)
      apply (rename_tac tcb)
      apply (rule conjI, clarsimp)
       apply (rename_tac intent)
       apply (rule_tac x = "Tcb (tcb\<lparr>cdl_tcb_intent := intent\<rparr>)" in exI)
       apply (clarsimp simp: object_clean_def intent_reset_def asid_reset_def
                             update_slots_def object_slots_def)
      apply clarsimp
      apply (rule_tac x = "Tcb tcb" in exI)
      apply (clarsimp simp: fun_eq_iff)
     apply (fastforce simp: cdl_cnode.splits fun_eq_iff)+
  done

(* General version of setting fields in a TCB.
 * Probably not practical to ever use.
 *)
lemma set_cdl_tcb_field_wp:
  assumes fields_cong:
  "\<And>tcb tcb'. object_clean (object_wipe_slots (Tcb tcb)) = object_clean (object_wipe_slots (Tcb tcb'))
  \<Longrightarrow> object_clean (object_wipe_slots (Tcb (f tcb))) = object_clean (object_wipe_slots (Tcb (f tcb')))"
  assumes slots_simp:
  "\<And>tcb. object_slots (Tcb (f tcb)) = object_slots (Tcb tcb)"
  shows
  "\<lbrace>\<lambda>s. <obj_id \<mapsto>f Tcb tcb \<and>* R> s\<rbrace>
    update_thread obj_id f
   \<lbrace>\<lambda>rv s. <obj_id \<mapsto>f Tcb (f tcb) \<and>* R> s\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp: update_thread_def get_thread_def)
  apply (frule sep_map_f_tcb_at)
   apply simp
  apply (clarsimp simp:object_at_def)
  apply (wp|wpc|simp)+
          apply (rename_tac cdl_tcb)
          apply (rule_tac P =
                 "object_clean (object_wipe_slots (Tcb cdl_tcb)) = object_clean (object_wipe_slots (Tcb tcb))"
                 in hoare_gen_asm)
          apply (rule_tac obj_p = "Tcb tcb" in set_object_cdl_field_wp[OF slots_simp  ])
             apply (simp add:object_type_simps object_wipe_slots_object_clean)+
          apply (drule_tac tcb = cdl_tcb in fields_cong)
          apply simp
         apply wp+
  apply (clarsimp simp: object_at_def)
  done

(* Specialised (and useful) versions of the above rule. *)
lemma set_cdl_tcb_intent_wp:
  "\<lbrace>\<lambda>s. <obj_id \<mapsto>f Tcb tcb \<and>* R> s\<rbrace>
    update_thread obj_id (\<lambda>tcb. tcb\<lparr>cdl_tcb_intent := x\<rparr>)
   \<lbrace>\<lambda>rv s. <obj_id \<mapsto>f Tcb (tcb\<lparr>cdl_tcb_intent := x\<rparr>) \<and>* R> s\<rbrace>"
  apply (rule hoare_weaken_pre)
   apply (wp set_cdl_tcb_field_wp)
    apply (clarsimp simp: object_wipe_slots_def object_clean_def update_slots_def
                          asid_reset_def object_slots_def intent_reset_def)
   apply (clarsimp simp: object_slots_def)
  apply simp
  done

lemma set_cdl_tcb_fault_endpoint_wp:
  "\<lbrace>\<lambda>s. <obj_id \<mapsto>f Tcb tcb \<and>* R> s\<rbrace>
    update_thread obj_id (\<lambda>tcb. tcb\<lparr>cdl_tcb_fault_endpoint := x\<rparr>)
   \<lbrace>\<lambda>rv s. <obj_id \<mapsto>f Tcb (tcb\<lparr>cdl_tcb_fault_endpoint := x\<rparr>) \<and>* R> s\<rbrace>"
  apply (rule hoare_weaken_pre)
   apply (wp set_cdl_tcb_field_wp)
    apply (clarsimp simp: object_wipe_slots_def asid_reset_def update_slots_def
                          object_clean_def object_slots_def intent_reset_def)
    apply (case_tac tcb,case_tac tcb',simp)
   apply (clarsimp simp:object_slots_def)
  apply simp
  done

lemma sep_map_o_conj:
  "(ptr \<mapsto>o obj \<and>* R) s = (( (sep_heap s) |` ({ptr} \<times> UNIV)
  = object_to_sep_state ptr obj UNIV)
  \<and> R (SepState (sep_heap s |` (UNIV - {ptr}\<times>UNIV))
                (sep_irq_node s)))"
  apply (clarsimp simp:sep_conj_def Let_def plus_sep_state_def sep_state_add_def
    sep_map_general_def sep_map_o_def)
  apply (rule iffI)
   apply (clarsimp simp:sep_map_c_def sep_disj_sep_state_def
     sep_map_general_def sep_state_disj_def map_disj_def)
   apply (subst dom_object_to_sep_state[where obj = obj,symmetric])
   apply (subst map_add_restrict_dom_left)
    apply (simp add:map_disj_def)
   apply simp
   apply (erule arg_cong[where f = R,THEN iffD1,rotated])
   apply (case_tac y,clarsimp)
   apply (rule ext)
   apply (clarsimp simp: map_add_restrict
     split:option.splits)
   apply (simp add:dom_object_to_sep_state[where obj = obj,symmetric])
   apply (subst restrict_map_univ_disj_eq)
    apply (fastforce simp:map_disj_def)
   apply simp
  apply (rule_tac x = "SepState (object_to_sep_state ptr obj UNIV) Map.empty" in exI)
  apply (rule_tac x = "SepState (sep_heap s |` (UNIV - {ptr}\<times>UNIV))
                                (sep_irq_node s) " in exI)
  apply (clarsimp simp:sep_map_c_def sep_disj_sep_state_def
     sep_map_general_def sep_state_disj_def map_disj_def)
  apply (clarsimp simp:dom_object_to_sep_state)
  apply (case_tac s,simp)
  apply (rule ext)
  apply (case_tac "x \<in> {ptr}\<times>UNIV")
   apply (drule_tac x = x in fun_cong)
   apply (clarsimp simp:map_add_def restrict_map_def)
  apply (clarsimp simp:map_add_def split:option.splits)
  apply (clarsimp simp:object_to_sep_state_def split:if_splits)
  done

lemma detype_one_wp:
  "\<lbrace><obj_id \<mapsto>o obj \<and>* R>\<rbrace>
    modify (detype {obj_id})
   \<lbrace>\<lambda>_. <obj_id \<mapsto>o Untyped \<and>* R>\<rbrace>"
  apply (clarsimp simp: modify_def detype_def)
  apply wp
  apply (clarsimp simp: sep_state_projection_def sep_map_o_conj)
  apply (rule conjI)
   apply (rule ext)
    apply (clarsimp simp:object_project_def
      restrict_map_def object_to_sep_state_def)
  apply (erule arg_cong[where f = R,THEN iffD1,rotated])
  apply clarsimp
  apply (rule ext)
  apply (clarsimp simp:restrict_map_def split:if_splits)
  done

(* What is the go with create_objects? Is is passed a list of singletons? *)
lemma create_one_wp:
  "\<lbrace><obj_id \<mapsto>o - \<and>* R>\<rbrace>
    Untyped_D.create_objects [{obj_id}] (Some obj)
   \<lbrace>\<lambda>_. <obj_id \<mapsto>o obj \<and>* R>\<rbrace>"
  apply (clarsimp simp: modify_def sep_any_exist create_objects_def)
  apply wp
  apply (clarsimp simp: sep_state_projection_def sep_map_o_conj)
  apply (intro conjI ext)
   apply (drule_tac x = xa in fun_cong)
    apply (clarsimp simp: object_to_sep_state_def)
  apply (erule arg_cong[where f = R,THEN iffD1,rotated])
  apply clarsimp
  apply (rule ext)
  apply (clarsimp simp:restrict_map_def split:if_splits)
  done

end
