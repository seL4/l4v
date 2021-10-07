(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory RWHelper_DP
imports ProofHelpers_DP KHeap_DP
begin

definition eq_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b option) \<Rightarrow> ('a \<Rightarrow> 'b option) \<Rightarrow> bool"
where "eq_on m s s' \<equiv> \<forall>ptr\<in> m. s ptr = s' ptr"

lemma eq_on_subset:
  "\<lbrakk>B \<subseteq> A ; eq_on A s s' \<rbrakk> \<Longrightarrow> eq_on B s s'"
  by (auto simp:eq_on_def)

definition WritingOf :: "(('a \<Rightarrow>'b option) \<Rightarrow> ('a \<Rightarrow> 'b option)) \<Rightarrow> 'a set"
where "WritingOf f \<equiv> UN s:UNIV. {ptr. (f s) ptr \<noteq> s ptr} "

definition IsReadingEstimateOf :: "'a set \<Rightarrow> (('a \<Rightarrow> 'b option) \<Rightarrow> ('a \<Rightarrow> 'b option)) \<Rightarrow> 'a set \<Rightarrow> bool"
  where "IsReadingEstimateOf m f estimate \<equiv> (\<forall>s s'. (eq_on m s s') \<longrightarrow> (eq_on estimate (f s) (f s')))"

definition ReadingEstimateOf :: "(('a \<Rightarrow>'b option) \<Rightarrow> ('a \<Rightarrow> 'b option)) \<Rightarrow> ('a set) \<Rightarrow> ('a set)"
where "ReadingEstimateOf f estimate \<equiv> Inter {m. IsReadingEstimateOf m f estimate }"

abbreviation ReadingOf :: "(('a \<Rightarrow>'b option) \<Rightarrow> ('a \<Rightarrow> 'b option)) \<Rightarrow> 'a set"
where "ReadingOf f \<equiv>  ReadingEstimateOf f (WritingOf f)"

lemma eq_on_trans:
  "\<lbrakk>eq_on a s sa ; eq_on a sa sb\<rbrakk> \<Longrightarrow> eq_on a s sb"
  by (simp add:eq_on_def)

lemma ReadingEstimateOf_inter:
  "\<lbrakk>IsReadingEstimateOf a f r; IsReadingEstimateOf b f r \<rbrakk> \<Longrightarrow> IsReadingEstimateOf (a \<inter> b) f r"
  apply (clarsimp simp:IsReadingEstimateOf_def)
  apply (drule_tac x = s in spec)
  apply (drule_tac x = "(\<lambda>ptr. if ptr\<in>(b - a) then (s' ptr) else (s ptr))" in spec)
  apply (drule_tac x = "(\<lambda>ptr. if ptr\<in>(b - a) then (s' ptr) else (s ptr))" in spec)
  apply (drule_tac x = s' in spec)
  apply (erule impE)
   apply (simp add:eq_on_def)
  apply (erule impE)
   apply (simp add:eq_on_def)
  apply (rule eq_on_trans)
  apply simp+
  done

lemma ReadingEstimateOf_read_subset:
  "\<lbrakk>IsReadingEstimateOf a f w;  a \<subseteq> b\<rbrakk> \<Longrightarrow> IsReadingEstimateOf b f w"
  by (auto simp add:IsReadingEstimateOf_def eq_on_def)

lemma ReadingEstimateOf_write_subset:
  "\<lbrakk>IsReadingEstimateOf a f w;  w' \<subseteq> w\<rbrakk> \<Longrightarrow> IsReadingEstimateOf a f w'"
  by (auto simp add:IsReadingEstimateOf_def eq_on_def)

lemma reading_estimateD:
  "\<lbrakk>IsReadingEstimateOf a f w; eq_on a s s'\<rbrakk> \<Longrightarrow> eq_on w (f s) (f s')"
  by (auto simp:IsReadingEstimateOf_def)

lemma not_writingD:
  "ptr \<notin> WritingOf f \<Longrightarrow> (f s) ptr = s ptr"
  by (auto simp:WritingOf_def)

lemma well_ordered_estimate:
  "WritingOf f \<subseteq> writing_estimate \<Longrightarrow>
    ReadingOf f \<subseteq> ReadingEstimateOf f writing_estimate"
  by (auto simp add:IsReadingEstimateOf_def ReadingEstimateOf_def eq_on_subset)

lemma writing_estimate_pipe:
  "\<lbrakk>WritingOf f \<subseteq> Q; WritingOf g \<subseteq> Q\<rbrakk> \<Longrightarrow> WritingOf (f\<circ>g) \<subseteq> Q"
  apply (subst WritingOf_def)
  apply clarsimp
  apply (rule ccontr)
  apply (drule(1) contra_subsetD)+
  apply (drule_tac s = "g xa" in not_writingD)
  apply (drule_tac s = xa in not_writingD)
  apply simp
  done

lemma reading_writing_estimate:
  "\<lbrakk>eq_on R s s'; IsReadingEstimateOf R g (WritingOf g)\<rbrakk> \<Longrightarrow> eq_on R (g s) (g s')"
  apply (subst eq_on_def)
  apply clarsimp
  apply (case_tac "ptr \<in> WritingOf g")
   apply (clarsimp simp:IsReadingEstimateOf_def)
   apply (elim impE allE)
    apply simp
   apply (clarsimp simp:eq_on_def)
  apply (clarsimp simp:WritingOf_def eq_on_def)
  done

lemma reading_estimate_pipe:
  assumes reg: "IsReadingEstimateOf R g M"
  and ref: " IsReadingEstimateOf R f M"
  and wg: "WritingOf g \<subseteq> M"
  and wf: "WritingOf f \<subseteq> M"
  shows "IsReadingEstimateOf R (f \<circ> g) M"
  apply (clarsimp simp: IsReadingEstimateOf_def)
  apply (cut_tac ReadingEstimateOf_write_subset[OF reg wg])
  apply (drule(1) reading_writing_estimate[rotated])
  apply (erule reading_estimateD[OF ref])
  done

definition
  "IsSepWritingEstimateOf f P proj m \<equiv> \<forall>ptr v.
  \<lbrace>\<lambda>s. (proj s) ptr = v \<and> P s \<and> ptr \<in> (UNIV - m) \<rbrace> f \<lbrace>\<lambda>r s. (proj s) ptr = v \<rbrace>"

definition
  "IsStrongSepWritingEstimateOf f P proj m g \<equiv> \<forall>state.
  \<lbrace>\<lambda>s. (proj s) = state \<and> P s \<rbrace> f
  \<lbrace>\<lambda>r s. (proj s) |` m = (g state) \<and> (proj s) |` (UNIV - m) = state |` (UNIV - m)\<rbrace>"

definition
  "IsSepReadingEstimateOf r f P proj m \<equiv> \<forall>substate. \<exists>g.
  \<lbrace>\<lambda>s. (proj s) |` r = substate \<and> P s  \<rbrace> f \<lbrace>\<lambda>r s. (proj s) |` m = g substate\<rbrace>"

lemma sep_writing_estimateD:
  "\<lbrakk>IsSepWritingEstimateOf f P proj m; (r, s') \<in> fst (f s);P s \<rbrakk>
  \<Longrightarrow> proj s |` (UNIV - m) = proj s' |` (UNIV - m)"
  apply (rule ext)
  apply (clarsimp simp: restrict_map_def
    IsSepWritingEstimateOf_def)
  apply (drule_tac x = x in spec)
  apply (drule_tac x = "proj s x" in spec)
  apply (drule(1) use_valid)
   apply simp+
  done

lemma sep_writing_estimate_imp:
  "\<lbrakk>IsSepWritingEstimateOf f P' proj m; \<And>s. P s \<Longrightarrow> P' s\<rbrakk>
  \<Longrightarrow> IsSepWritingEstimateOf f P proj m"
  apply (clarsimp simp:IsSepWritingEstimateOf_def)
  apply (drule_tac x = ptr in spec)
  apply (drule_tac x = v in spec)
  apply (erule hoare_pre)
  apply clarsimp
  done

lemma sep_strong_writing_estimateD:
  "\<lbrakk>IsStrongSepWritingEstimateOf f P proj m g; (r, s') \<in> fst (f s);P s \<rbrakk>
  \<Longrightarrow> proj s' |` m = g (proj s) \<and> proj s' |` (UNIV - m) = proj s |` (UNIV - m)"
  apply (simp add:
    IsStrongSepWritingEstimateOf_def)
  apply (drule_tac x = "proj s " in spec)
  apply (drule use_valid)
   apply assumption
   apply simp+
  done

lemma intent_reset_twice[simp]:
 "intent_reset (intent_reset z) = intent_reset z"
  apply (case_tac z)
  apply (simp_all add:intent_reset_def)
  done

lemma largest_set:
  "UNIV \<subseteq> cmps \<Longrightarrow> cmps = UNIV"
  by auto

definition "sep_map_predicate p P cmps \<equiv> \<lambda>s. \<exists>obj. (sep_map_general p obj cmps s \<and> P obj)"

definition "sep_heap_dom P m = (\<forall>s. P s \<longrightarrow> dom (sep_heap s) = m)"
definition "sep_irq_node_dom P m = (\<forall>s. P s \<longrightarrow> dom (sep_irq_node s) = m)"

definition "sep_map_spec P s =  (\<forall>s'. P s' \<longrightarrow> s' =  s)"

lemma sep_heap_domD:
  "\<lbrakk>sep_heap_dom P m; P s ; p \<notin> m\<rbrakk>
   \<Longrightarrow> p \<notin> dom (sep_heap s)"
  by (fastforce simp:sep_heap_dom_def)

lemma sep_heap_domD':
  "\<lbrakk>sep_heap_dom P m;P s\<rbrakk>
   \<Longrightarrow> m = dom (sep_heap s)"
  by (fastforce simp:sep_heap_dom_def)

lemma sep_irq_node_domD':
  "\<lbrakk>sep_irq_node_dom P m; P s\<rbrakk>
   \<Longrightarrow> m = dom (sep_irq_node s)"
  by (fastforce simp: sep_irq_node_dom_def)

lemma sep_specD:
  "\<lbrakk>sep_map_spec P s; P s'\<rbrakk> \<Longrightarrow> s = s'"
  by (clarsimp simp: sep_map_spec_def)

lemma sep_heap_dom_sep_map_predicate:
  "m = {ptr}\<times> cmps \<Longrightarrow>
  sep_heap_dom (sep_map_predicate ptr P cmps) m"
  apply (clarsimp simp: sep_map_general_def
    object_to_sep_state_def
    sep_heap_dom_def sep_map_predicate_def
    split:sep_state.splits if_splits)
  apply (rule set_eqI)
  apply (clarsimp simp:dom_def object_project_def split:cdl_component_id.splits)
  done

lemma sep_irq_node_dom_sep_map_predicate:
  "sep_irq_node_dom (sep_map_predicate ptr P cmps) {}"
  apply (clarsimp simp: sep_map_general_def object_to_sep_state_def
    sep_irq_node_dom_def sep_map_predicate_def
    split:sep_state.splits if_split_asm)
  done

lemma sep_map_rewrite_spec:
  "sep_map_general = (\<lambda>p obj cmps.  sep_map_predicate p ((=) obj) cmps)"
  "sep_map_o = (\<lambda>p obj. sep_map_predicate p ((=) obj) UNIV)"
  "sep_map_f = (\<lambda>p obj. sep_map_predicate p ((=) obj) {Fields})"
  "sep_map_c = (\<lambda>p cap. let (ptr,slot) = p in
   sep_map_predicate ptr (\<lambda>obj. object_slots obj = [ slot \<mapsto> cap]) {Slot slot})"
  by (fastforce simp: sep_map_predicate_def sep_any_def sep_map_general_def
                      sep_map_o_def sep_map_f_def sep_map_c_def split_def
               split: sep_state.splits)+

lemma sep_map_rewrite_any:
  "sep_any_map_c = (\<lambda>ptr state.
   sep_map_predicate (fst ptr) (\<lambda>obj. \<exists>cap. object_slots obj = [(snd ptr) \<mapsto> cap]) {Slot (snd ptr)} state)"
  by (fastforce simp: sep_map_predicate_def sep_map_general_def sep_any_def
                      sep_map_o_def sep_map_f_def sep_map_c_def split_def
               split: sep_state.splits)

lemma sep_heap_dom_conj:
  "\<lbrakk>sep_heap_dom P m;sep_heap_dom P' m'\<rbrakk> \<Longrightarrow> sep_heap_dom (P \<and>* P') (m \<union> m')"
  apply (clarsimp simp: sep_heap_dom_def sep_conj_def
                        sep_disj_sep_state_def sep_state_disj_def)
  apply (auto simp: map_disj_def plus_sep_state_def sep_state_add_def)
  done


lemma sep_heap_dom_simps:
  "sep_heap_dom (slot \<mapsto>c -) ({(fst slot,Slot (snd slot))})"
  "sep_heap_dom (slot \<mapsto>c cap) ({(fst slot,Slot (snd slot))})"
  apply (simp add:sep_map_rewrite_any sep_heap_dom_sep_map_predicate)
  apply (simp add:sep_map_rewrite_spec sep_heap_dom_sep_map_predicate split_def)
  done

lemma sep_irq_node_dom_simps:
  "sep_irq_node_dom (slot \<mapsto>c -) {}"
  "sep_irq_node_dom (slot \<mapsto>c cap) {}"
  apply (simp add:sep_map_rewrite_any sep_irq_node_dom_sep_map_predicate)
  apply (simp add:sep_map_rewrite_spec sep_irq_node_dom_sep_map_predicate split_def)
  done

lemma sep_map_spec_conj:
  "\<lbrakk>sep_map_spec P s; sep_map_spec P' s'\<rbrakk>
    \<Longrightarrow> sep_map_spec (P \<and>* P')
                     (SepState (sep_heap s ++ sep_heap s')
                               (sep_irq_node s ++ sep_irq_node s'))"
  by (clarsimp simp: sep_map_spec_def sep_conj_def
                     plus_sep_state_def sep_state_add_def)

lemma sep_spec_simps:
  "sep_map_spec (slot \<mapsto>c cap)
  (SepState [(fst slot,Slot (snd slot)) \<mapsto> (CDL_Cap (Some (reset_cap_asid cap)))]
            Map.empty)"
  apply (clarsimp simp:sep_map_spec_def sep_map_c_def sep_map_general_def)
  apply (case_tac s')
  apply (clarsimp simp:object_to_sep_state_def)
  apply (rule ext)
  apply (clarsimp simp: object_project_def object_slots_object_clean
                 split: if_split_asm)
  done

lemma sep_conj_spec:
  "\<lbrakk> < P \<and>* Q > s\<rbrakk>
   \<Longrightarrow> \<exists>s'. < P \<and>* (=) s' > s"
  by (auto simp:sep_state_projection_def sep_conj_def
    sep_disj_sep_state_def sep_state_disj_def)


lemma sep_conj_spec_value:
  "\<lbrakk> < P \<and>* (=) s' > s; sep_heap_dom P m; p \<notin> m\<rbrakk>
  \<Longrightarrow> (sep_heap s') p = (sep_heap (sep_state_projection s) |` (UNIV - m)) p"
  apply (clarsimp simp:sep_state_projection_def sep_conj_def
    sep_disj_sep_state_def sep_state_disj_def)
  apply (drule(2) sep_heap_domD)
  apply (simp add: plus_sep_state_def sep_state_add_def
            split: sep_state.splits)
  apply (clarsimp simp: map_add_def split:option.splits)
  done


lemma write_estimate_via_sep:
  assumes sep_valid: "\<And>obj Q. \<lbrace>\<lambda>s. < P \<and>* Q > s \<rbrace>
    f \<lbrace>\<lambda>r s. < P' \<and>* Q > s \<rbrace>"
  and sep_heap_dom: "sep_heap_dom P m"
  and sep_heap_dom': "sep_heap_dom P' m"
  shows "IsSepWritingEstimateOf f (\<lambda>s. < P \<and>* Q> s)
    (\<lambda>s.  sep_heap (sep_state_projection s)) m"
  apply (clarsimp simp: valid_def IsSepWritingEstimateOf_def)
  apply (drule sep_conj_spec)
  apply clarsimp
  apply (drule use_valid[OF _ sep_valid])
   apply simp
  apply (drule(1) sep_conj_spec_value[OF _ sep_heap_dom])
  apply (drule(1) sep_conj_spec_value[OF _ sep_heap_dom'])
  apply simp
  done

lemma sep_map_dom_predicate:
  "\<lbrakk>sep_heap_dom P m; sep_irq_node_dom P m';
    <P \<and>* P'> b\<rbrakk>
  \<Longrightarrow> P (SepState (sep_heap (sep_state_projection b) |` m)
                  (sep_irq_node (sep_state_projection b) |` m'))"
  apply (clarsimp simp: sep_state_projection_def sep_conj_def
                        plus_sep_state_def sep_state_add_def)
  apply (drule(1) sep_heap_domD')
  apply (drule(1) sep_irq_node_domD')
  apply simp
  apply (case_tac x,case_tac y)
  apply (clarsimp simp: sep_state_projection_def sep_conj_def
                        sep_disj_sep_state_def sep_state_disj_def)
  apply (simp add: map_add_restrict_dom_left)
  done

lemma strong_write_estimate_via_sep:
  assumes sep_valid: "\<And>obj Q. \<lbrace>\<lambda>s. < P \<and>* Q > s \<rbrace>
    f \<lbrace>\<lambda>r s. < P' \<and>* Q > s \<rbrace>"
  and sep_heap_dom: "sep_heap_dom P m"
  and sep_heap_dom': "sep_heap_dom P' m"
  and sep_irq_node_dom' : "sep_irq_node_dom P' m'"
  and sep_spec: "sep_map_spec P' state"
  shows "IsStrongSepWritingEstimateOf f (\<lambda>s. < P \<and>* Q> s)
    (\<lambda>s.  sep_heap (sep_state_projection s)) m (\<lambda>s. sep_heap state)"
  apply (clarsimp simp: valid_def IsStrongSepWritingEstimateOf_def)
  apply (drule sep_conj_spec)
  apply clarsimp
  apply (drule use_valid[OF _ sep_valid])
   apply simp
  apply (rule conjI)
   apply simp
   apply (drule sep_map_dom_predicate[OF sep_heap_dom' sep_irq_node_dom'])
   apply (drule sep_specD[OF sep_spec])
   apply (case_tac state,simp)
  apply (rule ext,clarsimp simp:restrict_map_def)
  apply (drule sep_conj_spec_value)
    apply (rule sep_heap_dom)
   apply simp
  apply (drule(1) sep_conj_spec_value[OF _ sep_heap_dom'])
  apply simp
  done

lemma map_eqI:
  "\<lbrakk>a |` m = b |` m;a |` (UNIV - m)  = b |` (UNIV - m)\<rbrakk> \<Longrightarrow> a = b"
  apply (rule ext)
  apply (drule_tac x = x in fun_cong)+
  apply (auto simp:restrict_map_def split:if_splits)
  done

lemma using_writing_estimate:
  assumes we: "IsSepWritingEstimateOf f P proj m"
  shows "\<lbrace>\<lambda>s. P s \<and> Q ((proj s) |` (UNIV - m)) \<rbrace> f \<lbrace>\<lambda>r s. Q ((proj s) |` (UNIV - m))\<rbrace>"
  apply (clarsimp simp:valid_def)
  apply (erule arg_cong[where f = Q,THEN iffD1,rotated])
  apply (erule sep_writing_estimateD[OF we])
  apply simp
  done

lemma using_strong_writing_estimate:
  assumes we: "IsStrongSepWritingEstimateOf f P proj m g"
  shows
  "\<lbrace>\<lambda>s. P s \<and> Q ((proj s) |` (UNIV - m) ++ g (proj s))  \<rbrace> f \<lbrace>\<lambda>r s. Q (proj s)\<rbrace>"
  apply (clarsimp simp:valid_def)
  apply (erule arg_cong[where f = Q,THEN iffD1,rotated])
  apply (rule map_eqI[where m = m])
   apply (drule(1) sep_strong_writing_estimateD[OF we,THEN conjunct1,symmetric])
   apply (rule ext)
   apply (clarsimp simp:restrict_map_def
     map_add_def split:option.splits)
  apply (frule(1) sep_strong_writing_estimateD[OF we,THEN conjunct1,symmetric])
  apply (drule(1) sep_strong_writing_estimateD[OF we,THEN conjunct2,symmetric])
  apply (rule ext)
  apply simp
  done

(* Here are some examples that we get valid rules from existing sep_logical rules *)

(* 1.  We need some predicates in the furture to make sure schedule will do the right thing *)

definition "scheduable_cap cap \<equiv> case cap of
  RunningCap \<Rightarrow> True | RestartCap \<Rightarrow> True | _ \<Rightarrow> False"

definition tcb_scheduable :: "cdl_tcb \<Rightarrow> bool"
  where "tcb_scheduable \<equiv> \<lambda>tcb. (cdl_tcb_caps tcb) tcb_pending_op_slot
  = Some RunningCap \<or> (cdl_tcb_caps tcb) tcb_pending_op_slot = Some RestartCap"

abbreviation "tcb_at_heap \<equiv> \<lambda>P ptr heap.
  object_at_heap (\<lambda>obj. \<exists>tcb. obj = Tcb tcb  \<and>  P tcb)  ptr heap"

definition all_scheduable_tcbs :: "(word32 \<Rightarrow> cdl_object option) \<Rightarrow> cdl_object_id set"
where  "all_scheduable_tcbs \<equiv> \<lambda>m. {ptr. tcb_at_heap tcb_scheduable ptr m}"

definition sep_all_scheduable_tcbs :: "(32 word \<times> cdl_component_id \<Rightarrow> cdl_component option) \<Rightarrow> cdl_object_id set"
where "sep_all_scheduable_tcbs m \<equiv> {ptr. \<exists>obj cap. m (ptr,Fields) = Some (CDL_Object obj) \<and> is_tcb obj
  \<and> m (ptr,Slot tcb_pending_op_slot) = Some (CDL_Cap (Some cap)) \<and> scheduable_cap cap}"

lemma is_tcb_obj_type:
  "is_tcb = (\<lambda>x. object_type x = TcbType)"
  by (auto simp:is_tcb_def object_type_def split:cdl_object.splits)

lemma all_scheduable_tcbs_rewrite:
  "all_scheduable_tcbs (cdl_objects s) =
  sep_all_scheduable_tcbs (sep_heap (sep_state_projection s))"
 apply (intro set_eqI iffI)
  apply (clarsimp simp:all_scheduable_tcbs_def sep_state_projection_def
    sep_all_scheduable_tcbs_def object_at_heap_def object_project_def
    is_tcb_obj_type)
  apply (clarsimp simp:object_type_def object_slots_object_clean
    tcb_scheduable_def object_slots_def scheduable_cap_def)
  apply (fastforce simp:object_clean_def asid_reset_def update_slots_def
    reset_cap_asid_def intent_reset_def object_slots_def
    split:if_splits)
 apply (clarsimp simp:all_scheduable_tcbs_def sep_state_projection_def
    sep_all_scheduable_tcbs_def object_at_heap_def object_project_def
    is_tcb_obj_type split:option.splits)
 apply (clarsimp simp:object_type_def tcb_scheduable_def
   scheduable_cap_def object_slots_def object_clean_def asid_reset_def
   update_slots_def intent_reset_def reset_cap_asid_def
   split:cdl_object.splits cdl_cap.splits option.splits)
 done

lemma update_slots_rev:
  "update_slots slots obj = obj' \<Longrightarrow>
  obj = update_slots (object_slots obj) obj'"
  by (clarsimp simp:update_slots_def object_slots_def
    split:cdl_object.splits)

lemma all_scheduable_tcbsD:
  "ptr \<in> all_scheduable_tcbs (cdl_objects s)
  \<Longrightarrow> tcb_at_heap tcb_scheduable ptr (cdl_objects s)"
  by (simp add:all_scheduable_tcbs_def)

lemma all_scheduable_tcbsD':
  "ptr \<notin> all_scheduable_tcbs (cdl_objects s)
  \<Longrightarrow> \<not> tcb_at_heap tcb_scheduable ptr (cdl_objects s)"
  by (simp add:all_scheduable_tcbs_def)

lemma scheduable_cap_reset_cap_asid[simp]:
  "scheduable_cap (reset_cap_asid cap) = scheduable_cap cap"
  by (case_tac cap,simp_all add: reset_cap_asid_def scheduable_cap_def)

lemma set_cap_all_scheduable_tcbs:
  "\<lbrace>\<lambda>s. all_scheduable_tcbs (cdl_objects s) = {cur_thread} \<and> (cap = RunningCap \<or> cap = RestartCap) \<rbrace>
    set_cap (cur_thread,tcb_pending_op_slot) cap
  \<lbrace>\<lambda>rv s. all_scheduable_tcbs (cdl_objects s) = {cur_thread} \<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (cut_tac all_scheduable_tcbsD[where ptr = cur_thread])
   prefer 2
   apply fastforce
  apply (clarsimp simp:all_scheduable_tcbs_rewrite)
  apply (rule hoare_pre)
   apply (rule using_strong_writing_estimate
     [where proj = "(\<lambda>a. sep_heap (sep_state_projection a))"])
   apply (rule strong_write_estimate_via_sep[OF set_cap_wp])
     apply (rule sep_heap_dom_simps sep_irq_node_dom_simps sep_spec_simps)+
  apply (rule conjI)
   apply (clarsimp simp:sep_map_c_conj
     Let_def sep_any_exist all_scheduable_tcbs_rewrite[symmetric]
     dest!:in_singleton)
   apply (clarsimp simp:object_at_heap_def tcb_scheduable_def
     sep_state_projection_def object_project_def)
   apply (rule conjI)
    apply (clarsimp simp:object_slots_def object_clean_def
      update_slots_def intent_reset_def asid_reset_def
      split:option.splits)
    apply fastforce+
  apply (rule subst,assumption)
  apply (drule in_singleton)
  apply (intro set_eqI iffI)
   apply (clarsimp simp: sep_all_scheduable_tcbs_def sep_state_projection_def
                  split: if_split_asm option.splits)
  apply (fastforce simp: sep_all_scheduable_tcbs_def map_add_def
                         sep_state_projection_def scheduable_cap_def
                 split: option.splits)
  done

lemma sep_inv_to_all_scheduable_tcbs:
  assumes sep: "\<And>P. \<lbrace><P>\<rbrace> f \<lbrace>\<lambda>r. <P>\<rbrace>"
  shows "\<lbrace>\<lambda>s. P (all_scheduable_tcbs (cdl_objects s))\<rbrace> f
   \<lbrace>\<lambda>r s. P (all_scheduable_tcbs (cdl_objects s))\<rbrace>"
  apply (clarsimp simp:valid_def all_scheduable_tcbs_rewrite)
  apply (erule use_valid)
   apply (rule hoare_strengthen_post)
    apply (rule sep)
   apply assumption
  apply simp
  done

lemma validE_to_valid:
  assumes validE:"\<And>E. \<lbrace>P\<rbrace>f\<lbrace>\<lambda>r. Q\<rbrace>,\<lbrace>\<lambda>r s. E\<rbrace>"
  shows "\<lbrace>P\<rbrace>f\<lbrace>\<lambda>r. Q\<rbrace>"
  using validE[where E = False]
  apply (clarsimp simp:validE_def valid_def)
  apply (drule_tac spec)
  apply (erule(1) impE)
  apply (drule_tac bspec)
   apply assumption
  apply (auto split:sum.splits)
  done

end
