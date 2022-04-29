(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory CreateObjects_SI
imports
  StaticDerivations_SI
  ObjectInitialised_SI
  RootTask_SI
  SysInit_SI
  Sep_Algebra.Extended_Separation_Algebra
  Sep_Algebra.Sep_Util
  Sep_Algebra.Sep_Fold_Cancel
  Mapped_Separating_Conjunction
  Lib.Guess_ExI
begin

lemma has_children_map_le:
  "\<lbrakk>cdl_cdt s \<subseteq>\<^sub>m cdl_cdt s'; has_children cap_ref s\<rbrakk>
  \<Longrightarrow> has_children cap_ref s'"
  apply (clarsimp simp: has_children_def is_cdt_parent_def)
  apply (rule_tac x=a in exI)
  apply (rule_tac x=b in exI)
  apply (clarsimp simp: map_le_def)
  by (metis domIff option.distinct(1))

lemma retype_untyped_wp_no_children:
  "\<lbrakk>default_object type sz minBound = Some new_object;
    base_ptr \<in> all_available_ids;
    free_cptr < 2 ^ si_cnode_size;
    untyped_cptr < 2 ^ si_cnode_size;
    sz < 2 ^ word_bits;
    type \<noteq> UntypedType;
    base_ptr = Min cover_ids\<rbrakk> \<Longrightarrow>
    \<lbrace>\<lambda>s. \<guillemotleft>(si_cnode_id, unat untyped_cptr) \<mapsto>c UntypedCap dev cover_ids cover_ids \<and>*
      (\<And>* obj_id \<in> all_available_ids. (obj_id \<mapsto>o Untyped)) \<and>*
      (si_cnode_id, unat free_cptr) \<mapsto>c NullCap \<and>*
      si_tcb_id \<mapsto>f root_tcb \<and>*
      (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
      (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*
      si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
      (si_cnode_id, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap \<and>* R\<guillemotright> s \<and>
      \<not>has_children (si_cnode_id,unat untyped_cptr) (kernel_state s)\<rbrace>

    retype_untyped free_cptr untyped_cptr type sz

   \<lbrace>\<lambda>rv s.
    \<guillemotleft>(si_cnode_id, unat untyped_cptr) \<mapsto>c UntypedCap dev cover_ids (update_range cover_ids (base_ptr) (unat (base_ptr + 2 ^ obj_bits_cdl type sz - base_ptr))) \<and>*
    (\<And>* obj_id \<in> all_available_ids - {base_ptr}. (obj_id \<mapsto>o Untyped)) \<and>*
     base_ptr \<mapsto>o new_object \<and>*
    (si_cnode_id, unat free_cptr) \<mapsto>c default_cap type {base_ptr} sz dev \<and>*
     si_tcb_id \<mapsto>f root_tcb \<and>*
    (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
    (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*
     si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
    (si_cnode_id, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap \<and>* R \<guillemotright> s \<and>
    has_children (si_cnode_id,unat untyped_cptr) (kernel_state s)\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (subgoal_tac "si_cspace_cap=si_cnode_cap", simp)
   apply (unfold retype_untyped_def)
   apply (wp)
     apply (clarsimp simp: comp_def, wp)
    apply (rule hoare_chain[OF seL4_Untyped_Retype_sep[where free_range = cover_ids and
                                               tot_free_range = all_available_ids and
                                               root_cnode_cap= si_cnode_cap and
                                               root_size=si_cnode_size and
                                               obj = new_object and
                                               obj_range=cover_ids and
                                               tcb="obj_tcb root_tcb"]])
               apply (fastforce)+
         apply (assumption | simp add: unat_of_nat32 | rule offset_slot' [symmetric] guard_equal_si_cnode_cap)+
    apply (clarsimp)
    apply (clarsimp simp: offset_slot')
    apply (sep_erule_concl refl_imp)+
    apply sep_solve
   apply (clarsimp simp: unat_of_nat32 offset_slot')
   apply (sep_solve)
  apply (clarsimp simp: si_cspace_cap_def si_cnode_cap_def)
  done

lemma retype_untyped_wp_has_children:
  "\<lbrakk>default_object type sz minBound = Some new_object;
    alignUp next_ptr (obj_bits_cdl type sz) \<in> all_available_ids;
    free_cptr < 2 ^ si_cnode_size;
    untyped_cptr < 2 ^ si_cnode_size;
    sz < 2 ^ word_bits;
    type \<noteq> UntypedType;
    available_ids \<noteq> {};
    base_ptr = Min cover_ids;
    next_ptr = Min available_ids\<rbrakk> \<Longrightarrow>
    \<lbrace>\<lambda>s. \<guillemotleft>(si_cnode_id, unat untyped_cptr) \<mapsto>c UntypedCap dev cover_ids available_ids \<and>*
      (\<And>* obj_id \<in> all_available_ids. (obj_id \<mapsto>o Untyped)) \<and>*
      (si_cnode_id, unat free_cptr) \<mapsto>c NullCap \<and>*
      si_tcb_id \<mapsto>f root_tcb \<and>*
      (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
      (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*
      si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
      (si_cnode_id, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap \<and>* R\<guillemotright> s \<and>
      has_children (si_cnode_id,unat untyped_cptr) (kernel_state s)\<rbrace>

     retype_untyped free_cptr untyped_cptr type sz

   \<lbrace>\<lambda>rv s.
    \<guillemotleft>(si_cnode_id, unat untyped_cptr) \<mapsto>c UntypedCap dev cover_ids (update_range cover_ids (base_ptr) (unat (alignUp next_ptr (obj_bits_cdl type sz) + 2 ^ obj_bits_cdl type sz - base_ptr))) \<and>*
    (\<And>* obj_id \<in> all_available_ids - {alignUp next_ptr (obj_bits_cdl type sz)}. (obj_id \<mapsto>o Untyped)) \<and>*
     alignUp next_ptr (obj_bits_cdl type sz) \<mapsto>o new_object \<and>*
    (si_cnode_id, unat free_cptr) \<mapsto>c default_cap type {alignUp next_ptr (obj_bits_cdl type sz)} sz dev \<and>*
     si_tcb_id \<mapsto>f root_tcb \<and>*
    (si_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
    (si_tcb_id, tcb_cspace_slot) \<mapsto>c si_cspace_cap \<and>*
     si_cnode_id \<mapsto>f CNode (empty_cnode si_cnode_size) \<and>*
    (si_cnode_id, unat seL4_CapInitThreadCNode) \<mapsto>c si_cnode_cap \<and>* R \<guillemotright> s \<and>
    has_children (si_cnode_id,unat untyped_cptr) (kernel_state s)\<rbrace>"
  apply (subgoal_tac "si_cspace_cap=si_cnode_cap", simp)
   apply (unfold retype_untyped_def)
   apply (wp)
     apply (clarsimp simp: comp_def, wp)
    apply (rule hoare_chain[OF seL4_Untyped_Retype_sep[where free_range = available_ids and
                                               tot_free_range = all_available_ids and
                                               root_cnode_cap= si_cnode_cap and
                                               root_size=si_cnode_size and
                                               dev=dev and
                                               obj = new_object and
                                               obj_range=cover_ids and
                                               tcb="obj_tcb root_tcb"]])
             apply (fastforce)+
         apply (assumption | simp add: unat_of_nat32 | rule offset_slot' [symmetric] guard_equal_si_cnode_cap)+
    apply (clarsimp)
    apply (clarsimp simp: offset_slot')
    apply (sep_erule_concl refl_imp)+
    apply (clarsimp)
    apply (assumption)
   apply (assumption | simp add: unat_of_nat32 | rule offset_slot' [symmetric] guard_equal_si_cnode_cap)+
   apply (clarsimp, intro conjI impI)
    apply (clarsimp simp: offset_slot')+
    apply (sep_solve)
   apply (clarsimp simp: offset_slot' si_cspace_cap_def si_cnode_cap_def)+
  done

lemma untyped_cap_eq:
  "is_untyped_cap cap \<Longrightarrow> UntypedCap (is_device_cap cap) (cap_objects cap) (cap_free_ids cap) = cap"
  by (clarsimp simp: cap_type_def cap_free_ids_def split: cdl_cap.splits)

lemma create_object_first:
  "cdl_objects spec child = Some child_obj \<Longrightarrow>
   default_object (object_type child_obj) (object_size_bits child_obj) minBound = Some default_child \<Longrightarrow>
   si_caps child = Some free_cptr \<Longrightarrow>
   the (si_caps child) < 2 ^ si_cnode_size \<Longrightarrow>
   parent < 2 ^ si_cnode_size \<Longrightarrow>
   object_type child_obj \<noteq> UntypedType \<Longrightarrow>
   object_size_bits child_obj < 2 ^ word_bits \<Longrightarrow>
   obj_size = (obj_bits_cdl (object_type child_obj) (object_size_bits child_obj)) \<Longrightarrow>
   obj_size < word_size \<Longrightarrow>
   t child = Some (alignUp base_ptr obj_size) \<Longrightarrow>
   cover_ids \<noteq> {} \<Longrightarrow>
   base_ptr = Min cover_ids \<Longrightarrow>
   base_ptr \<le> base_ptr + 2 ^ obj_size \<Longrightarrow>
   is_aligned base_ptr obj_size \<Longrightarrow>
   \<lbrace> \<guillemotleft>si_objects \<and>*
      si_null_cap_at t si_caps spec child \<and>*
      (the (t child)) \<mapsto>o Untyped \<and>*
      (si_cnode_id, unat parent) \<mapsto>c UntypedCap dev cover_ids cover_ids \<and>* R\<guillemotright> \<rbrace>

     create_object spec si_caps parent child

   \<lbrace>\<lambda>_. \<guillemotleft>si_cap_at t si_caps spec dev child \<and>*
          si_objects \<and>* (the (t child)) \<mapsto>o default_child \<and>*
          (si_cnode_id, unat parent) \<mapsto>c UntypedCap dev cover_ids (cover_ids - {..<base_ptr + 2 ^ obj_size}) \<and>* R\<guillemotright> \<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (case_tac "has_children (si_cnode_id, unat parent) (kernel_state s)")
   apply (clarsimp simp: create_object_def assert_opt_def, wp)
    apply (rule hoare_strengthen_post[OF retype_untyped_wp_has_children[where dev=dev and
                                                      new_object=default_child and
                                                      available_ids=cover_ids and
                                                      all_available_ids="{(the (t child))}" and
                                                      cover_ids=cover_ids]])
             apply (fastforce)+
    apply (clarsimp simp: word_size_def alignUp_idem)
    apply (clarsimp simp: si_cap_at_def)
    apply (clarsimp simp: update_range_def si_objects_def)
    apply (sep_flatten)
    apply ((sep_erule_concl refl_imp)+, assumption)
   apply (clarsimp simp: si_objects_def si_null_cap_at_def)
   apply (sep_cancel)+
  apply (clarsimp simp: create_object_def assert_opt_def, wp)
   apply (rule hoare_strengthen_post[OF retype_untyped_wp_no_children[where dev=dev and
                                                      new_object=default_child and
                                                      all_available_ids="{(the (t child))}" and
                                                      cover_ids=cover_ids]])
          apply (fastforce)+
    apply (clarsimp simp: word_size_def alignUp_idem)
   apply (clarsimp simp: si_cap_at_def)
   apply (clarsimp simp:  si_objects_def)
   apply (sep_flatten)
   apply (sep_cancel)+
  apply (clarsimp simp: si_objects_def si_null_cap_at_def)
  apply (sep_cancel)+
  apply (clarsimp simp: alignUp_idem word_size_def)
  apply (clarsimp simp: update_range_def)
  done

lemma create_object_has_children:
  "cdl_objects spec child = Some child_obj \<Longrightarrow>
   default_object (object_type child_obj) (object_size_bits child_obj) minBound = Some default_child \<Longrightarrow>
   si_caps child = Some free_cptr \<Longrightarrow>
   the (si_caps child) < 2 ^ si_cnode_size \<Longrightarrow>
   parent < 2 ^ si_cnode_size \<Longrightarrow>
   object_type child_obj \<noteq> UntypedType \<Longrightarrow>
   object_size_bits child_obj < 2 ^ word_bits \<Longrightarrow>
   obj_size = (obj_bits_cdl (object_type child_obj) (object_size_bits child_obj)) \<Longrightarrow>
   obj_size < word_size \<Longrightarrow>
   t child = Some (alignUp base_ptr obj_size) \<Longrightarrow>
   cover_ids \<noteq> {} \<Longrightarrow>
   available_ids \<noteq> {} \<Longrightarrow>
   base_ptr = Min cover_ids \<Longrightarrow>
   base_ptr \<le> base_ptr + 2 ^ obj_size \<Longrightarrow>
   is_aligned base_ptr obj_size \<Longrightarrow>
   \<lbrace> \<guillemotleft>si_objects \<and>*
      si_null_cap_at t si_caps spec child \<and>*
      (the (t child)) \<mapsto>o Untyped \<and>*
      (si_cnode_id, unat parent) \<mapsto>c UntypedCap dev cover_ids cover_ids \<and>* R\<guillemotright> \<rbrace>

     create_object spec si_caps parent child

   \<lbrace>\<lambda>_ s. has_children (si_cnode_id, unat parent) (kernel_state s) \<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (case_tac "has_children (si_cnode_id, unat parent) (kernel_state s)")
   apply (clarsimp simp: create_object_def assert_opt_def, wp)
    apply (rule hoare_strengthen_post[OF retype_untyped_wp_has_children[where dev=dev and
                                                        new_object=default_child and
                                                        available_ids=cover_ids and
                                                        all_available_ids="{(the (t child))}" and
                                                        cover_ids=cover_ids]])
             apply (fastforce)+
   apply (clarsimp simp: word_size_def alignUp_idem)
   apply (clarsimp simp: update_range_def si_objects_def)
   apply (sep_flatten)
   apply (clarsimp simp: si_objects_def si_null_cap_at_def)
   apply (sep_cancel)+
  apply (clarsimp simp: create_object_def assert_opt_def, wp)
   apply (rule hoare_strengthen_post[OF retype_untyped_wp_no_children[where dev=dev and
                                                       new_object=default_child and
                                                       all_available_ids="{(the (t child))}" and
                                                       cover_ids=cover_ids]])
          apply (fastforce)+
    apply (clarsimp simp: word_size_def alignUp_idem)
   apply (clarsimp simp: si_cap_at_def)
  apply (clarsimp simp:  si_objects_def)
  apply (sep_flatten)
  apply (clarsimp simp: si_objects_def si_null_cap_at_def)
  apply (sep_cancel)+
  done

lemma create_object_rest:
  "cdl_objects spec child = Some child_obj \<Longrightarrow>
   default_object (object_type child_obj) (object_size_bits child_obj) minBound = Some default_child \<Longrightarrow>
   si_caps child = Some free_cptr \<Longrightarrow>
   the (si_caps child) < 2 ^ si_cnode_size \<Longrightarrow>
   parent < 2 ^ si_cnode_size \<Longrightarrow>
   object_type child_obj \<noteq> UntypedType \<Longrightarrow>
   object_size_bits child_obj < 2 ^ word_bits \<Longrightarrow>
   obj_size = (obj_bits_cdl (object_type child_obj) (object_size_bits child_obj)) \<Longrightarrow>
   obj_size < word_size \<Longrightarrow>
   t child = Some (alignUp next_ptr obj_size) \<Longrightarrow>
   cover_ids \<noteq> {} \<Longrightarrow>
   available_ids \<noteq> {} \<Longrightarrow>
   next_ptr = Min available_ids \<Longrightarrow>
   base_ptr = Min cover_ids \<Longrightarrow>
   \<lbrace> \<guillemotleft>si_objects \<and>*
      si_null_cap_at t si_caps spec child \<and>*
      (the (t child)) \<mapsto>o Untyped \<and>*
      (si_cnode_id, unat parent) \<mapsto>c UntypedCap dev cover_ids available_ids \<and>* R\<guillemotright> and
      (\<lambda>s. has_children (si_cnode_id, unat parent) (kernel_state s)) \<rbrace>

     create_object spec si_caps parent child

   \<lbrace>\<lambda>_. \<guillemotleft>si_cap_at t si_caps spec dev child \<and>*
          si_objects \<and>* (the (t child)) \<mapsto>o default_child \<and>*
          (si_cnode_id, unat parent) \<mapsto>c UntypedCap dev cover_ids (update_range cover_ids base_ptr (unat (the (t child) + 2 ^ obj_size - base_ptr))) \<and>* R\<guillemotright> and
          (\<lambda>s. has_children (si_cnode_id, unat parent) (kernel_state s)) \<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp: create_object_def assert_opt_def, wp)
   apply (rule hoare_strengthen_post[OF retype_untyped_wp_has_children[where dev=dev and
                                                       new_object=default_child and
                                                       available_ids=available_ids and
                                                       all_available_ids="{(the (t child))}" and
                                                       cover_ids=cover_ids]])
            apply (fastforce)+
   apply (clarsimp simp: word_size_def alignUp_idem)
   apply (clarsimp simp: si_cap_at_def)
   apply (clarsimp simp: si_objects_def)
   apply (sep_flatten)
   apply (clarsimp simp: si_objects_def si_null_cap_at_def)
   apply (sep_cancel)+
  apply (clarsimp)
  apply (clarsimp simp: si_objects_def si_null_cap_at_def)
  apply (sep_cancel)+
  done

lemma sep_hoare_fold_mapM_x_inv:
  "(\<And>R x. x \<in> set xs \<Longrightarrow> \<lbrace>\<lambda>s. (P x \<and>* R) (sep_lift s) \<and> P' s\<rbrace> f x \<lbrace>\<lambda>_ s. (Q x \<and>* R) (sep_lift s) \<and> P' s\<rbrace>)
    \<Longrightarrow> \<lbrace>\<lambda>s. (sep_fold P Q R xs) (sep_lift s) \<and> P' s \<rbrace> mapM_x f xs \<lbrace>\<lambda>_ s. R (sep_lift s)\<rbrace>"
  apply (clarsimp simp: sep_fold_def)
  apply (induct xs arbitrary: R)
   apply (clarsimp simp: mapM_x_def sequence_x_def)+
   apply wp
   apply (clarsimp)
  apply (simp add: mapM_x_Cons, wp)
    apply assumption+
   apply atomize
   apply (erule allE)
   apply (erule allE)
   apply (erule_tac x=a in allE)
   apply (drule mp)
    apply (clarsimp)
   apply (rule hoare_chain)
     apply assumption+
   apply (clarsimp)
   apply (sep_erule (direct) sep_mp)
  apply clarsimp
  done

lemma si_null_cap_at_cong: "t a = v a \<Longrightarrow> si_null_cap_at t si_caps spec a = si_null_cap_at (\<lambda>x. v x) si_caps spec a"
  apply (clarsimp simp: si_null_cap_at_def)
  done

lemma si_cap_at_cong: "t a = v a \<Longrightarrow> si_cap_at t si_caps spec dev a = si_cap_at (\<lambda>x. v x) si_caps spec dev a"
  apply (clarsimp simp: si_cap_at_def)
  done

lemma [simp]: "x + Map.empty = x" by (rule ext, clarsimp simp: plus_fun_def plus_option_def split: option.splits)

lemma sub_neq_zero_le: "y < (x :: machine_word) \<Longrightarrow> x - y \<noteq> 0"
 by (clarsimp)

lemma Some_the: "x = Some y \<Longrightarrow> the x = y"
 by (clarsimp)

definition "partial (f) (x :: 'a :: zero) = (if x = 0 then \<box> else f x)"

instantiation list :: (type) monoid_add
begin
  definition "zero_list = []"
  definition "plus_list (x :: 'a list) y = x @ y"
instance
 apply (intro_classes;clarsimp simp: zero_list_def plus_list_def)
done
end

lemma [simp]: "partial (P \<circ> f) (x # xs) = (P o f) (x # xs)"
 apply (clarsimp simp: partial_def zero_list_def)
done

lemma [simp]: "partial (P \<circ> f) [] = \<box>"
 apply (clarsimp simp: partial_def zero_list_def)
done







lemma induct_list: "\<lbrakk>P []; \<And>x. P [x];  \<And>x y xs. P (y#xs) \<Longrightarrow> P ([x,y] @ xs)\<rbrakk> \<Longrightarrow> P xs"
 apply (induct xs; clarsimp)
 apply (case_tac xs; clarsimp)
done


lemma sep_fold_simplify_loop: "distinct xs  \<Longrightarrow> (\<And>x y s. y \<in>set xs \<Longrightarrow> previous y xs = Some x \<Longrightarrow> Q x s \<Longrightarrow> P y s) \<Longrightarrow>
       (partial (P o hd) xs \<and>* (sep_fold P' Q' ((partial (Q o last) xs) \<longrightarrow>* R) xs)) s \<Longrightarrow>
       (sep_fold (\<lambda>x. P x \<and>* P' x) (\<lambda>x. Q x \<and>* Q' x) R xs) s "
 apply (induct xs  arbitrary: s R rule: induct_list ; clarsimp simp: sep_fold_def)
 apply (sep_solve)
 apply (sep_cancel)+
 apply (sep_solve)
 apply (sep_cancel)+
 apply (drule_tac x=sc in meta_spec)
 apply (drule_tac x=R in meta_spec)
 apply (atomize)
 apply (erule impE)
 apply (clarsimp)
 apply (intro impI conjI; clarsimp? )
 apply (erule_tac x=xa in allE)
 apply (erule_tac x=y in allE)
 apply (erule_tac x=s in allE)
 apply (clarsimp)
  using not_in_previous' apply fastforce
 apply (erule_tac x=xa in allE)
 apply (erule_tac x=ya in allE)
 apply (erule_tac x=s in allE)
 apply (clarsimp)
  apply presburger
  apply (erule mp)
 apply (sep_mp)
 apply (sep_cancel)+
 apply (clarsimp)
done

definition "default_object_in spec ptr =
  (let obj = (the (cdl_objects spec ptr)) in the (default_object (object_type obj) (object_size_bits obj) minBound))"

lemma default_object_some_default: "cdl_objects spec ptr = Some obj \<Longrightarrow>
       default_object (object_type obj) (object_size_bits obj) minBound = Some (default_object_in spec ptr)"
  apply (clarsimp simp: default_object_in_def)
  by (cases obj; clarsimp simp: default_object_def object_type_def)



lemma the_some_cdl_objects[elim]: "cdl_objects spec ptr = Some obj \<Longrightarrow>  P (the (cdl_objects spec ptr))  = P obj"
  by (clarsimp)

lemma default_object_is_object_empty: "(ptr \<mapsto>o default_object_in spec a) s \<Longrightarrow> cdl_objects spec a = Some obj \<Longrightarrow>
       object_domain obj = minBound \<Longrightarrow> t a = Some ptr \<Longrightarrow>
       (object_empty spec t a) s"
 by (clarsimp simp: object_empty_def object_initialised_general_def object_default_state_def default_object_in_def)

lemma extD1: "P = Q \<Longrightarrow> P x \<Longrightarrow> Q x"
 by (erule subst)






lemma Min_diff_upt: "finite S \<Longrightarrow> v \<in> S \<Longrightarrow> Min (S - {..<v}) =  v"
  apply (rule Min_eqI; clarsimp)
  apply simp
  done

lemma create_children_wp:
  assumes
    increasing_allocations:"list_all (\<lambda>child. previous child children \<noteq> None \<longrightarrow> Min cover_ids < the (allocate (Min cover_ids) spec children child)) children" and
    aligned_no_wrap:"list_all (\<lambda>child.  Min cover_ids \<le> the (aligned_allocations spec (Min cover_ids) children child) + 2 ^ (spec_object_size spec child )) children"
  shows
    "\<forall>x \<in> set children. t x = (aligned_allocations spec (Min cover_ids) children) x \<Longrightarrow>
     cover_ids \<noteq> {} \<Longrightarrow>
     finite cover_ids \<Longrightarrow>
     distinct children \<Longrightarrow>
     \<forall>obj\<in>ran (cdl_objects spec). object_domain obj = minBound \<Longrightarrow>
     list_all (\<lambda>child. the (allocate (Min cover_ids) spec children child) \<in> cover_ids ) children \<Longrightarrow>
     list_all (\<lambda>child. si_caps child \<noteq> None \<and> the (si_caps child) < 2 ^ si_cnode_size) children \<Longrightarrow>
     list_all (\<lambda>child. is_aligned (Min cover_ids) (obj_bits_cdl (object_type (the (cdl_objects spec child))) (object_size_bits (the (cdl_objects spec child))))) children \<Longrightarrow>
     list_all (\<lambda>child. cdl_objects spec child \<noteq> None \<and>
                       object_type (the (cdl_objects spec child)) \<noteq> UntypedType \<and>
                       object_size_bits (the (cdl_objects spec child)) < 2 ^ word_bits \<and>
                       Min cover_ids \<le> (Min cover_ids) + 2 ^ obj_bits_cdl (object_type (the (cdl_objects spec child))) (object_size_bits (the (cdl_objects spec child))) \<and>
                       obj_bits_cdl (object_type (the (cdl_objects spec child))) (object_size_bits (the (cdl_objects spec child))) < word_size) children \<Longrightarrow>
     \<lbrace>\<guillemotleft>(si_null_caps_at t si_caps spec  (set children) \<and>*
       (si_cnode_id, unat parent_cptr) \<mapsto>c UntypedCap dev cover_ids cover_ids \<and>*
       sep_map_set_conj (\<lambda>child. (the (t child)) \<mapsto>o Untyped) (set children) \<and>*
       si_objects \<and>* R )\<guillemotright> and
      K (parent_cptr' = parent_cptr \<and> parent_cptr < 2 ^ si_cnode_size)\<rbrace>
     mapM_x (create_object spec si_caps parent_cptr) children
     \<lbrace>\<lambda>s. \<guillemotleft>(si_caps_at t si_caps spec dev (set children) \<and>*
           (EXS remaining_ids. (si_cnode_id, unat parent_cptr') \<mapsto>c UntypedCap dev cover_ids remaining_ids) \<and>*
           objects_empty spec t (set children) \<and>*
           si_objects \<and>* R )\<guillemotright>\<rbrace>"
  supply Ball_set[symmetric, simp]
  apply (rule hoare_gen_asm)
  apply (case_tac children)
   apply clarsimp
   apply (clarsimp simp: mapM_x_def sequence_x_def, wp, clarsimp simp: si_caps_at_def si_null_caps_at_def objects_empty_def, fastforce)
  apply (simp add: mapM_x_Cons, wp)
    apply (rule sep_hoare_fold_mapM_x_inv[OF create_object_rest[where t="(aligned_allocations spec (Min cover_ids) children)" and base_ptr="Min cover_ids" and cover_ids = cover_ids and
                                                                      available_ids = "cover_ids - {..<the (allocate (Min cover_ids) spec children child )}" and
                                                                      default_child = "default_object_in spec child" and
                                                                      child_obj = "the (cdl_objects spec child)" for list child, simplified sep_wp_simp]])

  using Some_to_the apply fastforce
                apply (fastforce simp: default_object_some_default)
  using Some_to_the apply (fastforce)
              apply fastforce
             apply fastforce
            apply fastforce
           apply fastforce
          apply (rule refl)
         apply fastforce
        apply (elim conjE)
        apply (rule allocate_alignUp)
         apply clarsimp
        apply clarsimp
       apply clarsimp
      apply fastforce
     apply (subst Min_diff_upt; clarsimp?)
    apply clarsimp
   apply clarsimp
   apply (rule hoare_vcg_conj_lift)
    apply (rule create_object_first[where base_ptr ="Min cover_ids" and cover_ids=cover_ids and obj_size = " obj_bits_cdl (object_type obj) (object_size_bits obj)" and
                     default_child = "default_object_in spec child" for obj child, simplified sep_wp_simp, THEN sep_lift_generic])
                 apply fastforce
  using default_object_some_default apply (fastforce)
               apply fastforce
              apply fastforce
             apply fastforce
            apply fastforce
           apply fastforce
          apply (erule the_some_cdl_objects)
         apply clarsimp
        apply fastforce
       apply clarsimp
      apply fastforce
     apply fastforce
    apply fastforce
   apply (rule create_object_has_children[where t="(aligned_allocations spec (Min cover_ids) children)" and
                    base_ptr ="Min cover_ids" and cover_ids=cover_ids])
                 apply fastforce
                apply (erule default_object_some_default)
               apply fastforce
              apply fastforce
             apply fastforce
            apply fastforce
           apply fastforce
          apply fastforce
         apply fastforce
        apply clarsimp
        apply (subst aligned_allocations_hd)
        apply (clarsimp simp: spec_object_size_def)
       apply clarsimp
      apply fastforce
     apply fastforce
    apply fastforce
   apply fastforce
  apply (clarsimp simp: si_null_caps_at_def)
  apply (intro conjI)
   apply (sep_flatten, sep_cancel)
   apply (subst (asm) si_null_cap_at_cong)
    apply (erule trans)
    apply (rule allocate_alignUp; clarsimp)
   apply clarsimp
   apply sep_cancel+
   apply (clarsimp simp: allocate_alignUp, sep_cancel)
   apply clarsimp
   apply sep_cancel
   apply sep_fold_cancel
   apply (rule sep_fold_cong1, rule iffI, sep_select 3, assumption, sep_solve)
   apply (rule sep_fold_cong2, rule iffI, sep_select 3, assumption, sep_solve)
   apply (rule sep_fold_simplify_loop)
     apply clarsimp
    apply (erule_tac subst[where s="set :: machine_word set" for set, rotated])
    apply (subst update_range_simple)
      defer
      defer
      apply clarsimp
      apply (subst allocate_previous)
         apply clarsimp
        apply clarsimp
       apply (erule distinct_previous_const[rotated], clarsimp)
      apply clarsimp
      apply (rule_tac f="\<lambda>x. cover_ids - {..<x}" in arg_cong)
      apply (clarsimp simp: aligned_allocations_def next_allocation_def spec_object_size_def Let_unfold)
      apply (subst mapp_app)
       defer
       apply clarsimp
      apply (case_tac list; simp)
       apply (clarsimp simp: sep_fold_def)
       apply sep_cancel
       apply (clarsimp simp: si_cap_at_def si_caps_at_def allocate_alignUp)
       apply sep_cancel+
       apply (clarsimp simp: aligned_allocations_def)
       apply (rule exI, sep_cancel+)
       apply (clarsimp simp: objects_empty_def)
       apply (erule default_object_is_object_empty)
         apply fastforce
        apply (fastforce simp: ran_def)
       apply (clarsimp simp: mapp_def)
      apply (intro conjI impI; clarsimp)
       apply (clarsimp simp: aligned_allocate_previous allocate_previous next_allocation_def spec_object_size_def)
       apply (subst alignUp_idem, assumption, simp add: word_size_def)
       apply sep_cancel
       apply (clarsimp simp:  sep_fold_def)
       apply sep_flatten
       apply (sep_erule si_null_cap_at_cong[THEN extD1, rotated])
        apply (erule trans)
        apply (clarsimp simp: alignUp_idem word_size_def)
        apply (simp add: aligned_allocate_previous next_allocation_def spec_object_size_def alignUp_idem word_size_def)
       apply (clarsimp simp: alignUp_idem word_size_def)
       apply (simp add: aligned_allocate_previous next_allocation_def spec_object_size_def alignUp_idem word_size_def)
       apply sep_cancel+
       apply (clarsimp simp: si_caps_at_def)
       apply (sep_flatten, sep_erule si_cap_at_cong[THEN extD1, rotated])
        apply (erule trans[symmetric])
        apply (simp add: aligned_allocations_def)
        apply (subst alignUp_idem, assumption, simp add: word_size_def, rule refl)
       apply (sep_erule si_cap_at_cong[THEN extD1, rotated])
        apply (erule trans[symmetric])
        apply (simp add: aligned_allocations_def)
        apply (subst mapp_app; clarsimp)
         apply (clarsimp simp: allocate.simps)
        apply (simp add: allocate.simps aligned_allocate_previous next_allocation_def spec_object_size_def alignUp_idem word_size_def Let_unfold)
       apply (rule exI, sep_cancel+)
       apply (clarsimp simp: objects_empty_def object_empty_def object_initialised_general_def)
       apply (simp add: aligned_allocate_previous next_allocation_def spec_object_size_def alignUp_idem word_size_def Let_unfold default_object_in_def object_default_state_def)
       apply (frule_tac x=ya in bspec)
        apply (fastforce simp: ran_def, clarsimp)
       apply (frule_tac x=yc in bspec)
        apply (fastforce simp: ran_def, clarsimp)
       apply sep_solve
      apply (simp add: allocate_previous spec_object_size_def Let_unfold)
      apply (simp add: next_allocation_def alignUp_idem word_size_def spec_object_size_def Let_unfold)
      apply sep_cancel
      apply (rule sep_map_sep_foldI, clarsimp, sep_flatten)
      apply (simp add: aligned_allocate_previous allocate_previous alignUp_idem word_size_def next_allocation_def spec_object_size_def  Let_unfold)
      apply sep_cancel
      apply (clarsimp simp: sep_list_conj_map_add sep_list_conj_sep_map_set_conj)
      apply (subst sep_map_set_conj_subst[OF arg_cong[where f="\<lambda>p. p \<mapsto>o Untyped"]])
       apply (subst aligned_allocate_previous, simp, simp)
        apply (rule option.collapse)
        apply (meson in_tail_previous not_in_previous)
       apply (rule refl)
      apply (simp only: option.sel)
      apply (subst (asm) sep_map_set_conj_subst[OF arg_cong[where f="\<lambda>p. p \<mapsto>o Untyped"]])
       apply (subst allocate_previous, simp, simp)
        apply (rule option.collapse)
        apply (meson in_tail_previous not_in_previous)
       apply (rule refl)
      apply (simp only: option.sel)
      apply sep_cancel
      apply (clarsimp simp: si_caps_at_def)
      apply (sep_erule si_null_cap_at_cong[THEN extD1, rotated])
       apply (erule trans)
       apply (simp add: aligned_allocations_def aligned_allocate_previous alignUp_idem word_size_def next_allocation_def spec_object_size_def Let_unfold)
       apply (subst mapp_app; clarsimp)
        apply (clarsimp simp: allocate.simps)
       apply (simp add: allocate.simps aligned_allocate_previous next_allocation_def spec_object_size_def alignUp_idem word_size_def Let_unfold)
      apply (sep_erule sep_map_set_conj_subst[THEN extD1, OF si_null_cap_at_cong, rotated ])
       apply (drule (1) bspec, erule trans)
       apply (rule allocate_alignUp[symmetric]; clarsimp?)
      apply sep_cancel+
      apply (sep_erule si_cap_at_cong[THEN extD1, rotated])
       apply (simp add: aligned_allocate_previous alignUp_idem word_size_def next_allocation_def spec_object_size_def Let_unfold)
      apply (sep_erule si_cap_at_cong[THEN extD1, rotated])
       apply (erule trans[symmetric])
       apply (simp add: aligned_allocate_previous alignUp_idem word_size_def next_allocation_def spec_object_size_def Let_unfold)
      apply (sep_erule sep_map_set_conj_subst[THEN extD1, OF si_cap_at_cong, rotated ])
       apply (drule (1) bspec, erule trans[symmetric])
       apply (simp add: aligned_allocate_previous alignUp_idem word_size_def next_allocation_def spec_object_size_def Let_unfold)
       apply (rule allocate_alignUp[symmetric]; clarsimp?)
      apply (rule exI, sep_cancel+)
      apply (clarsimp simp: objects_empty_def)
      apply (sep_erule default_object_is_object_empty)
         apply fastforce
        apply (fastforce simp: ran_def)
       apply (simp add:aligned_allocations_def aligned_allocate_previous alignUp_idem word_size_def next_allocation_def spec_object_size_def Let_unfold)
      apply (sep_erule default_object_is_object_empty)
         apply fastforce
        apply (fastforce simp: ran_def)
       apply (simp add: aligned_allocations_def)
      apply (subst (asm) sep_map_set_conj_subst[OF arg_cong[where f="\<lambda>p. p \<mapsto>o val" for val]])
       apply (rule arg_cong[where f=the and y="t _"])
       apply (drule (1) bspec, rule sym, erule trans, rule allocate_alignUp[symmetric])
        apply clarsimp
       apply clarsimp
      apply (erule sep_map_set_elim, rule refl)
      apply (drule_tac x=x in bspec, assumption, elim conjE exE, erule (1) default_object_is_object_empty)
       apply (fastforce simp: ran_def)
      apply fastforce
     apply sep_cancel
     apply sep_cancel
     apply sep_cancel
     apply (sep_erule si_null_cap_at_cong[THEN extD1, rotated])
      apply assumption
     apply (rule TrueI)
    apply (subst aligned_allocations_def)
    apply clarsimp
    apply (subst mapp_app)
     apply clarsimp
     apply (erule previous_in_allocate; clarsimp)
    apply clarsimp
    apply (subst unat_gt_0)
    apply (rule sub_neq_zero_le)
    apply (subgoal_tac "alignUp (the (allocate (Min cover_ids) spec (a # list) x)) (spec_object_size spec x) +
                2 ^ obj_bits_cdl (object_type (the (cdl_objects spec x))) (object_size_bits (the (cdl_objects spec x))) = next_allocation spec (the (allocate (Min cover_ids) spec (a # list)  x)) x ")
     apply simp
     apply (subst allocate_previous[THEN Some_the, symmetric]; simp?)
       defer
  using distinct_previous_const apply fastforce
      apply (rule_tac x=yb in increasing_allocations[simplified, THEN ballE])
       apply (clarsimp simp: in_tail_previous)
      apply fastforce
     apply (clarsimp simp: next_allocation_def spec_object_size_def Let_unfold)
    apply clarsimp
    apply (rule_tac x=x in aligned_no_wrap[simplified, THEN ballE])
     apply (clarsimp simp: next_allocation_def spec_object_size_def Let_unfold)
    apply (simp add: previous_in_list)
   apply clarsimp
   apply (meson distinct.simps(2) previous_in_allocate)
  apply blast
  done

lemma untyped_cap_helper: "is_device_cap ut =  dev \<Longrightarrow> is_full_untyped_cap ut \<Longrightarrow> UntypedCap dev (available_range ut) (available_range ut) = ut"
  by (clarsimp simp:  is_full_untyped_cap_def dev_of_def split: cdl_cap.splits)

definition derivation_set :: "('a \<times> ('b list)) list \<Rightarrow> ('a \<times> 'b) set"
   where "derivation_set xs = set (List.bind xs (\<lambda>(parent,children). List.bind children (swp (#) [] o Pair parent)))"

lemma distinct_map_snd: "distinct_sets (map (set \<circ> snd) untyped_derivations) \<Longrightarrow> \<forall>(x,y)\<in>set untyped_derivations. \<forall>(a,b)\<in>set untyped_derivations. set b \<inter> set y \<noteq> {} \<longrightarrow> a = x"
  apply (clarsimp)
  apply (induct untyped_derivations; clarsimp simp: comp_def split: prod.splits)
  apply (safe; clarsimp)
  apply (subgoal_tac "x \<in> set b \<inter> (\<Union>x\<in>set untyped_derivations. set (snd x))")
  apply (clarsimp)
  apply fastforce
 apply (subgoal_tac "x \<in> set b \<inter> (\<Union>x\<in>set untyped_derivations. set (snd x))")
  apply (clarsimp)
  apply fastforce
  apply (atomize)
  apply (clarsimp)
  apply (erule_tac x="aaa" in allE)
  apply (erule_tac x="baa" in allE)
  apply (clarsimp)
  apply (fastforce)
done


abbreviation (input) "is \<equiv> (=)"

lemma is_in_rangeD: "(is g \<and>* R) s \<Longrightarrow> v \<in> dom g \<Longrightarrow> s v = g v"
  apply (clarsimp simp: sep_conj_def)
  apply (clarsimp simp: plus_fun_def plus_option_def)
done

lemma is_in_sep_list_conjD: "sep_list_conj (map (\<lambda>x. is (g x)) xs) s \<Longrightarrow>  x \<in> set xs \<Longrightarrow>  v \<in> dom (g x) \<Longrightarrow> s v = (g x v :: 'b option) "
    apply (subst (asm) sep_list_conj_map_remove1, assumption)
    apply (erule (1) is_in_rangeD)
done

definition "disjoint_sets S \<equiv> \<forall>x\<in>S. \<forall>y\<in>S. x \<noteq> y \<longrightarrow> x \<inter> y = {}"


lemma distinct_disjoint: "distinct_sets S \<Longrightarrow> disjoint_sets (set S)"
  apply (induct S; clarsimp simp: disjoint_sets_def)
  by (intro conjI ballI impI; blast)


lemma helper: "distinct_sets (map (set \<circ> snd) untyped_derivations)
         \<Longrightarrow> \<forall>s s'. s \<in> (\<lambda>x. set (snd x)) ` set untyped_derivations \<and> s' \<in> (\<lambda>x. set (snd x)) ` set untyped_derivations \<longrightarrow> s \<noteq> s' \<longrightarrow> s \<inter> s' = {}"
  apply (drule distinct_disjoint)
  apply (clarsimp simp: comp_def)
   apply (clarsimp simp: disjoint_sets_def)
  by (metis snd_conv)

lemma [simp]: "unat x = unat y \<longleftrightarrow> x = y"
  by (metis not_less order_antisym_conv order_refl unat_mono)

lemma zip_map_map: "(zip (map f xs) ys) = map (apfst f) (zip xs ys)"
 apply (induct xs arbitrary: ys ; clarsimp)
 apply (clarsimp simp: apfst_def)
  by (metis id_apply list.map_id0 list.simps(9) map_prod_def zip_map_map)



lemma prod_lift_lambda: "(\<lambda>x. f (case x of (a,b) \<Rightarrow> g a b)) = (\<lambda>(a,b). f (g a b)) "
 by (rule ext, clarsimp)


definition
 on_depleted_untyped_cap where
  "on_depleted_untyped_cap P \<equiv> (\<lambda>cap s. \<exists>cap'. is_untyped_cap cap \<and> is_device_cap cap = is_device_cap cap' \<and> untyped_cap_range cap = untyped_cap_range cap' \<and> P cap' s)"

lemma distinct_fst_snd_distinct: "distinct_sets (map (set o snd) S) \<Longrightarrow>  distinct (map fst S) \<Longrightarrow>  distinct S "
  apply (induct S; clarsimp simp: comp_def)
  apply (subst (asm) Int_commute, simp add: Union_disjoint image_def)
 by (fastforce)

lemma child_in_collection[simp]:
       "(a, b) \<in> set untyped_derivations \<Longrightarrow> child \<in> set b
       \<Longrightarrow> child \<in> set (collect_children untyped_derivations)"
  by (fastforce simp: collect_children_def List.bind_def Bex_def)


lemma the_map_of_elim[simp, elim]: "x \<in> set xs \<Longrightarrow> length xs \<le> length ys \<Longrightarrow> \<forall>x\<in>set ys. P x \<Longrightarrow> P (the (map_of (zip xs ys) x))"
     apply (induct xs arbitrary: ys; clarsimp)
     by (case_tac ys; clarsimp)



lemma distinct_map_comp:" distinct (map g xs) \<Longrightarrow> inj f  \<Longrightarrow> distinct (map (\<lambda>a. f (g a)) xs)"
  by (meson List.distinct_map injD inj_on_def)

lemma distinct_map_comp':" distinct (map g xs) \<Longrightarrow> inj f  \<Longrightarrow> distinct (map (f o g) xs)"
  by (clarsimp simp:  comp_def distinct_map_comp)


lemma map_allocates[simp]: "(parent, children) \<in> set untyped_derivations \<Longrightarrow> child \<in> set children \<Longrightarrow>
                       sep_list_conj (map (\<lambda>(parent, children). is (aligned_allocations spec (f parent)  children)) untyped_derivations) t \<Longrightarrow>
                       t child =  aligned_allocations spec (f parent) children child "
  apply (subst (asm) split_beta')
  apply (drule_tac is_in_sep_list_conjD[where x="(parent,children)" and g="\<lambda>x. (aligned_allocations spec (f (fst x)) (snd x))" and xs=untyped_derivations])
 prefer 3
  apply (erule trans)
  apply (clarsimp)+
  apply (clarsimp simp: aligned_allocations_def mapp_def)
  by (simp add: in_list_allocate)

lemma full_cap_range_available[elim]: "is_full_untyped_cap b \<Longrightarrow> untyped_cap_range b = available_range b"
  by (cases b; clarsimp simp: is_full_untyped_cap_def)


lemma untyped_derivations_inject[simp]: "distinct_sets (map (set o snd) untyped_derivations) \<Longrightarrow> list_all distinct (map snd untyped_derivations) \<Longrightarrow>
    \<forall>x y. x \<in> set untyped_derivations \<longrightarrow> y \<in> set untyped_derivations \<longrightarrow> x \<noteq> y \<longrightarrow> set (snd x) = set (snd y) \<longrightarrow> set (snd x) = {}"
   apply (clarsimp)
   apply (induct untyped_derivations; clarsimp)
   by (metis (no_types, lifting) Int_commute Union_disjoint inf_idem rev_image_eqI set_empty snd_conv)

lemma distinct_inj_on: "distinct (map f S) \<Longrightarrow> inj_on f (set S)"
 apply (induct S; clarsimp)
done

definition "dupl x = (x,x)"

lemma [simp]: "sep_map_set_conj (\<lambda>y. (EXS x. P x y \<and>* Q y)) S = (sep_map_set_conj (\<lambda>y. (EXS x. P x y)) S \<and>* sep_map_set_conj Q S)"
  by (subst sep.prod.cong[OF refl, OF sep_conj_exists1[symmetric]], simp only: sep.prod.distrib)


method arg_checker for t = (match conclusion in "x = _" for x \<Rightarrow> \<open>match (x) in t \<Rightarrow> \<open>fail\<close> \<bar> _ \<Rightarrow> \<open>rule refl\<close> \<close>)

method comp_folder uses comp = ( (subst comp, arg_checker "(\<lambda>a. a)", arg_checker "(\<lambda>a. a)") |  (subst (asm) comp, arg_checker "(\<lambda>a. a)", arg_checker "(\<lambda>a. a)"))

lemma comp_folder: "f = f \<Longrightarrow> g = g \<Longrightarrow> (\<lambda>x. f (g x)) = f o g " by (clarsimp simp: comp_def)

lemma distinct_fstD:
  "distinct (map fst xs) \<Longrightarrow> distinct xs"
  by (induct xs; fastforce simp: image_def)

lemma the_map_of_zip_inR:
  "x \<in> set xs \<Longrightarrow> length xs \<le> length ys \<Longrightarrow> the (map_of (zip xs ys) x) \<in> set ys"
  apply (induct xs arbitrary: ys; clarsimp)
  by (case_tac ys; clarsimp)

definition matching_paddrs where
  "matching_paddrs ut_ids ut_info \<equiv>
    (\<forall>id \<in> set ut_ids. \<exists>desc. desc \<in> set ut_info \<and> bi_ut_paddr desc = id)"

definition valid_untypeds where
  "valid_untypeds ut_ids ut_cptrs ut_info ut_caps \<equiv>
    length ut_ids = length ut_cptrs \<and>
    length ut_cptrs = length ut_info \<and>
    length ut_cptrs = length ut_caps \<and>
    distinct (map bi_ut_paddr ut_info) \<and>
    matching_paddrs ut_ids ut_info \<and>
    distinct ut_cptrs \<and>
    distinct_sets (map cap_free_ids ut_caps) \<and>
    list_all is_full_untyped_cap ut_caps \<and>
    list_all (\<lambda>cap. available_range cap \<noteq> {}) ut_caps \<and>
    list_all well_formed_untyped_cap ut_caps \<and>
    list_all (\<lambda>c. \<not> is_device_cap c) ut_caps"

definition make_untyped_map ::
  "cdl_object_id list \<Rightarrow> cdl_cptr list \<Rightarrow> bi_untyped_desc list \<Rightarrow> cdl_cap list \<Rightarrow>
   cdl_object_id \<Rightarrow> (cdl_cptr \<times> bi_untyped_desc \<times> cdl_cap) option"
  where
  "make_untyped_map untyped_ids untyped_cptrs untyped_info untyped_caps \<equiv> \<lambda>untyped_id.
     if untyped_id \<in> set untyped_ids
     then find (\<lambda>(_, ut_desc, _). bi_ut_paddr ut_desc = untyped_id)
               (zip untyped_cptrs (zip untyped_info untyped_caps))
     else None"

lemma make_untyped_map_Some:
  "\<lbrakk>ut_id \<in> set ids; matching_paddrs ids info; distinct (map bi_ut_paddr info);
    length ids = length cptrs; length cptrs = length info;
    length cptrs = length caps\<rbrakk> \<Longrightarrow>
   \<exists>n. (make_untyped_map ids cptrs info caps ut_id) = Some (cptrs ! n, info ! n, caps ! n) \<and>
       bi_ut_paddr (info ! n) = ut_id \<and> n < length ids"
  apply (clarsimp simp: make_untyped_map_def matching_paddrs_def find_Some_iff
         split_def)
  apply (drule_tac x=ut_id in bspec; clarsimp)
  apply (clarsimp simp: in_set_conv_nth)
  apply (rule_tac x=ia in exI)
  apply clarsimp
  apply (rule_tac x=ia in exI)
  apply clarsimp
  apply (subst (asm) nth_map[where f=bi_ut_paddr, symmetric], clarsimp)+
  apply (subst (asm) nth_eq_iff_index_eq; clarsimp)
  done

lemma make_untyped_map_Some':
  "\<lbrakk>ut_id \<in> set ids; matching_paddrs ids info; distinct (map bi_ut_paddr info);
    length ids = length cptrs; length cptrs = length info;
    length cptrs = length caps\<rbrakk> \<Longrightarrow>
   \<exists>x. (make_untyped_map ids cptrs info caps ut_id) = Some x"
  apply (frule make_untyped_map_Some; assumption?)
  by auto

lemma cap_of_make_untyped_map:
  "\<lbrakk>ut_id \<in> set ids; matching_paddrs ids info; distinct (map bi_ut_paddr info);
    length ids = length cptrs; length cptrs = length info;
    length cptrs = length caps\<rbrakk> \<Longrightarrow>
   cap_of (make_untyped_map ids cptrs info caps ut_id) \<in> set caps"
  apply (frule make_untyped_map_Some; assumption?)
  apply (clarsimp simp: make_untyped_map_def)
  done

lemma cptr_of_make_untyped_map:
  "\<lbrakk>ut_id \<in> set ids; matching_paddrs ids info; distinct (map bi_ut_paddr info);
    length ids = length cptrs; length cptrs = length info;
    length cptrs = length caps\<rbrakk> \<Longrightarrow>
   cptr_of (make_untyped_map ids cptrs info caps ut_id) \<in> set cptrs"
  apply (frule make_untyped_map_Some; assumption?)
  apply (clarsimp simp: make_untyped_map_def)
  done

lemma make_untyped_map_reorder'[OF refl, simplified]:
  "\<lbrakk>sorted_list = map (the \<circ> make_untyped_map ids cptrs info caps) ids;
    matching_paddrs ids info; distinct (map bi_ut_paddr info);
    length ids = length cptrs; length cptrs = length info;
    length cptrs = length caps; distinct ids; distinct cptrs\<rbrakk>
   \<Longrightarrow> make_untyped_map ids (map fst sorted_list) (map (fst \<circ> snd) sorted_list)
                            (map (snd \<circ> snd) sorted_list)
       = make_untyped_map ids cptrs info caps"
  apply (rule ext)
  apply (case_tac "x \<in> set ids")
   prefer 2
   apply (clarsimp simp: make_untyped_map_def)
  apply (frule make_untyped_map_Some; assumption?)
  apply (clarsimp simp: in_set_conv_nth)

  apply (clarsimp simp: make_untyped_map_def o_def)
  apply (subst find_Some_iff)

  apply clarsimp
  apply (rule_tac x=i in exI)
  apply clarsimp
  apply (frule_tac ut_id="ids ! j" and cptrs=cptrs and info=info and caps=caps in make_untyped_map_Some[rotated];
         clarsimp)
  apply (clarsimp simp: make_untyped_map_def distinct_conv_nth)
  done

lemma make_untyped_map_cptr_inj_on:
  "\<lbrakk>matching_paddrs ids info; distinct (map bi_ut_paddr info);
    length ids = length cptrs; length cptrs = length info;
    length cptrs = length caps; distinct cptrs\<rbrakk> \<Longrightarrow>
   inj_on (cptr_of \<circ> make_untyped_map ids cptrs info caps) (set ids)"
  apply (clarsimp simp: inj_on_def)
  apply (frule_tac ut_id="x" and cptrs=cptrs and caps=caps in make_untyped_map_Some[rotated];
       (clarsimp simp: distinct_conv_nth))
  apply (frule_tac ut_id="y" and cptrs=cptrs and caps=caps in make_untyped_map_Some[rotated];
       (clarsimp simp: distinct_conv_nth))
  apply blast
  done

lemma make_untyped_map_list_set[OF refl, simplified]:
  "\<lbrakk>sorted_list = map (the \<circ> make_untyped_map ids cptrs info caps) ids;
    matching_paddrs ids info; distinct (map bi_ut_paddr info);
    length ids = length cptrs; length cptrs = length info;
    length cptrs = length caps; distinct ids; distinct cptrs\<rbrakk> \<Longrightarrow>
   set (zip (map fst sorted_list) (map (snd \<circ> snd) sorted_list))
   = set (zip cptrs caps)"
  apply (rule subset_antisym; clarsimp simp: in_set_zip)
   apply (frule_tac ut_id="ids ! n" and cptrs=cptrs and info=info and caps=caps in make_untyped_map_Some[rotated];
        (clarsimp simp: distinct_conv_nth))
   apply fastforce

  apply (cut_tac make_untyped_map_cptr_inj_on[where ids=ids and cptrs=cptrs and caps=caps];
         fastforce?)
  apply (subst (asm) surjective_iff_injective_gen[where T="set cptrs", symmetric];
         (clarsimp simp: distinct_card cptr_of_make_untyped_map)?)
  apply (drule_tac x="cptrs ! n" in bspec; clarsimp)
  apply (clarsimp simp: in_set_conv_nth)
  apply (frule_tac ut_id="ids ! i" and cptrs=cptrs and info=info and caps=caps in make_untyped_map_Some[rotated];
         (clarsimp simp: distinct_conv_nth))
  apply (rule_tac x=i in exI)
  apply fastforce
  done

lemma make_untyped_map_distinct_fst:
  "\<lbrakk>matching_paddrs ids info; distinct (map bi_ut_paddr info);
    length ids = length cptrs; length cptrs = length info;
    length cptrs = length caps; distinct ids; distinct cptrs\<rbrakk> \<Longrightarrow>
   distinct (map (fst \<circ> (the \<circ> make_untyped_map ids cptrs info caps)) ids)"
  apply (clarsimp simp: distinct_conv_nth)
  apply (frule_tac ut_id="ids ! i" and cptrs=cptrs and info=info and caps=caps in make_untyped_map_Some[rotated];
         (clarsimp simp: distinct_conv_nth))
  apply (frule_tac ut_id="ids ! j" and cptrs=cptrs and info=info and caps=caps in make_untyped_map_Some[rotated];
         (clarsimp simp: distinct_conv_nth))
  apply (case_tac "n=na"; clarsimp)
  done

lemma make_untyped_map_reorder:
  "\<lbrakk>untyped_map = make_untyped_map ids cptrs info caps;
    matching_paddrs ids info; distinct (map bi_ut_paddr info);
    length ids = length cptrs; length cptrs = length info; length cptrs = length caps;
    distinct ids; distinct cptrs\<rbrakk> \<Longrightarrow>
   \<exists>cptrs' info' caps'.
     untyped_map = make_untyped_map ids cptrs' info' caps' \<and>
     set (zip cptrs caps) = set (zip cptrs' caps') \<and> distinct cptrs' \<and>
     length cptrs = length cptrs' \<and> length caps = length caps' \<and>
     (\<forall>i. i < length ids \<longrightarrow> cptr_of (untyped_map (ids ! i)) = cptrs' ! i \<and>
                             cap_of (untyped_map (ids ! i)) = caps' ! i)"
  apply (rule_tac x="(map fst (map (the \<circ> make_untyped_map ids cptrs info caps) ids))" in exI)
  apply (rule_tac x="(map (fst \<circ> snd) (map (the \<circ> make_untyped_map ids cptrs info caps) ids))" in exI)
  apply (rule_tac x="(map (snd \<circ> snd) (map (the \<circ> make_untyped_map ids cptrs info caps) ids))" in exI)
  apply (clarsimp simp: make_untyped_map_reorder' make_untyped_map_list_set
                        make_untyped_map_distinct_fst)
  done

lemma map_nth_length:
  "map (\<lambda>i. f (xs ! i)) [0..<length xs] = map f xs"
  by (auto intro!: map_length_cong simp: in_set_conv_nth)

lemma sep_prod_make_untyped_map_zip[OF refl]:
  "\<lbrakk>untyped_map = make_untyped_map ids cptrs info caps;
    matching_paddrs ids info; distinct (map bi_ut_paddr info);
    length ids = length cptrs; length cptrs = length info; length cptrs = length caps;
    distinct ids; distinct cptrs\<rbrakk>
   \<Longrightarrow> (SETSEPCONJ x:set ids. f (cptr_of (untyped_map x)) (cap_of (untyped_map x))) =
       (SETSEPCONJ x:set (zip cptrs caps). f (fst x) (snd x))"
  apply (cut_tac untyped_map=untyped_map in make_untyped_map_reorder, assumption+)
  apply clarsimp
  apply (clarsimp simp: sep_list_conj_sep_map_set_conj[symmetric] distinct_zipI1)

  apply (subst map_nth_length[symmetric, where xs=ids])
  apply (subst map_nth_length[symmetric, where xs="zip cptrs' caps'" for cptrs' caps'])
  apply clarsimp

  apply (rule map_sep_list_conj_cong)
  apply clarsimp
  done

lemma make_untyped_map_find:
  "\<lbrakk>ut_id \<in> set ut_ids; matching_paddrs ut_ids ut_info; distinct (map bi_ut_paddr ut_info);
    length ut_ids = length ut_cptrs; length ut_cptrs = length ut_info;
    length ut_cptrs = length ut_caps\<rbrakk> \<Longrightarrow>
   cptr_of (make_untyped_map ut_ids ut_cptrs ut_info ut_caps ut_id)
    = the ((find (\<lambda>(_, ut_desc). bi_ut_paddr ut_desc = ut_id)
                ||> fst) (zip ut_cptrs ut_info))"
  apply (frule make_untyped_map_Some'; assumption?)
  apply (clarsimp simp: make_untyped_map_def opt_map_def split: option.splits)
  apply (clarsimp simp: find_Some_iff find_None_iff)+
  apply (rule conjI; clarsimp)
   apply (fastforce simp: simp: set_zip)
  apply (rule arg_cong[where f="nth ut_cptrs"])
  apply (rule ccontr)
  apply (auto simp: neq_iff)
  done

lemma lookup_cptr_wp:
  "\<lbrakk>untyped_map = make_untyped_map untyped_ids (map fst untyped_list)
                                  (map snd untyped_list) untyped_caps;
    length untyped_ids = length untyped_list; length untyped_ids = length untyped_caps;
    matching_paddrs untyped_ids (map snd untyped_list);
    distinct (map bi_ut_paddr (map snd untyped_list));
    untyped_id \<in> set untyped_ids\<rbrakk> \<Longrightarrow>
   \<lbrace>Q (cptr_of (untyped_map untyped_id))\<rbrace>
   lookup_cptr untyped_list untyped_id
   \<lbrace>Q\<rbrace>"
  apply (clarsimp simp: lookup_cptr_def)
  apply wpsimp
  apply (clarsimp simp: make_untyped_map_find zip_map_fst_snd opt_map_def)
  done

declare is_full_untyped_cap_is_untyped_cap[simp]

lemma retype_untypeds_wp_helper:
  defines
    "allocation_map spec untyped_map untyped_derivations \<equiv>
       map (\<lambda>(parent, children). is (aligned_allocations spec ((Min o available_range \<circ> cap_of \<circ> untyped_map) parent) children))
           untyped_derivations"
  shows
    "\<lbrakk>well_formed spec;
      sep_list_conj (allocation_map spec untyped_map untyped_derivations) t;
      map_of (zip_region (collect_children untyped_derivations) free_cptrs) = si_caps;
      map (fst) untyped_list = untyped_slots;
      untyped_map = make_untyped_map (map fst untyped_derivations) (map fst untyped_list)
                                     (map snd untyped_list) untyped_caps;
      \<forall>obj \<in> ran (cdl_objects spec). object_domain obj = minBound;
      length (collect_children untyped_derivations) \<le> length_region free_cptrs;
      list_all
        (\<lambda>x. \<forall>child\<in>set (snd x).
                (\<exists>y. cdl_objects spec child = Some y) \<and>
                object_type (the (cdl_objects spec child)) \<noteq> UntypedType \<and>
                object_size_bits (the (cdl_objects spec child)) < 2 ^ word_bits \<and>
                Min (available_range (cap_of (untyped_map (fst x))))
                \<le> Min (available_range (cap_of (untyped_map (fst x)))) +
                   2 ^ obj_bits_cdl (object_type (the (cdl_objects spec child))) (object_size_bits (the (cdl_objects spec child))) \<and>
                obj_bits_cdl (object_type (the (cdl_objects spec child))) (object_size_bits (the (cdl_objects spec child))) < word_size)
        untyped_derivations;
      list_all (\<lambda>n. n < 2 ^ si_cnode_size) untyped_slots;
      list_all (\<lambda>n. n < 2 ^ si_cnode_size) (list_region free_cptrs);
      list_all (\<lambda>d. list_all
              (\<lambda>child.
                  previous child (snd d) \<noteq> None \<longrightarrow>
                  Min ((available_range \<circ> cap_of \<circ> untyped_map \<circ> fst) d)
                  < the (allocate ((Min o available_range \<circ> cap_of \<circ> untyped_map o fst)  d) spec (snd d) child))
              (snd d)) untyped_derivations;
      list_all (\<lambda>cap. available_range cap \<noteq> {}) untyped_caps;
       list_all (\<lambda>d.
         \<forall>child\<in>set (snd d).
                the (allocate (Min (available_range (cap_of (untyped_map (fst d))))) spec (snd d) child)
                \<in> available_range (cap_of (untyped_map (fst d)))) untyped_derivations;
      list_all (\<lambda>d. let cover_ids = (Min o available_range \<circ> cap_of \<circ> untyped_map  o fst) d in
                    list_all (\<lambda>child. cover_ids
                    \<le> the (aligned_allocations spec cover_ids (snd d) child) + 2 ^ spec_object_size spec child) (snd d))
                untyped_derivations;
      list_all
        (\<lambda>x. \<forall>child\<in>set (snd x).
                is_aligned (Min (available_range (cap_of (untyped_map (fst x)))))
                 (obj_bits_cdl (object_type (the (cdl_objects spec child))) (object_size_bits (the (cdl_objects spec child)))))
        untyped_derivations;
      valid_untypeds (map fst untyped_derivations) (map fst untyped_list)
                     (map snd untyped_list) untyped_caps;
      list_all (\<lambda>c. is_device_cap c = dev) untyped_caps;
      distinct (map fst untyped_derivations); list_all distinct (map snd untyped_derivations);
      valid_slot_region free_cptrs
      \<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s.
    \<guillemotleft>\<And>* map (\<lambda>(slot, cap). (si_cnode_id, unat slot) \<mapsto>c cap) (zip untyped_slots untyped_caps) \<and>*
     si_null_caps_at t si_caps spec (set (collect_children untyped_derivations)) \<and>*
     (\<And>* obj_id\<in>(set (collect_children untyped_derivations)). the (t obj_id) \<mapsto>o Untyped) \<and>*
     si_objects \<and>* R\<guillemotright> s \<and>
    distinct_sets (map (set o snd) untyped_derivations)\<rbrace>
   create_objects spec untyped_list free_cptrs (untyped_derivations :: (machine_word \<times> (machine_word list)) list)
   \<lbrace>\<lambda>(si_caps', free_cptrs') s.
     \<guillemotleft>\<And>* map (\<lambda>(slot, cap). on_depleted_untyped_cap (sep_map_c (si_cnode_id, unat slot)) cap) (zip untyped_slots untyped_caps) \<and>*
      objects_empty spec t (set (collect_children untyped_derivations)) \<and>*
      si_caps_at t si_caps spec dev (set (collect_children untyped_derivations)) \<and>*
      si_objects \<and>* R\<guillemotright> s \<and>
     si_caps = si_caps' \<and>
     free_cptrs' = drop_region (length (collect_children untyped_derivations)) free_cptrs\<rbrace>"
  supply list_all_iff[simp] map_of_zip_is_Some'[symmetric, simp] split_beta'[simp]
  apply (rule hoare_name_pre_state)
  apply (unfold create_objects_def)
  apply (clarsimp simp: valid_untypeds_def)
  apply (rule hoare_weaken_pre)
   apply (wp|wpc)+
   apply (clarsimp split: prod.splits)
   apply (frule (1) distinct_fst_snd_distinct)
   apply (rule sep_hoare_fold_mapM_x, rule bind_wp,
          rule create_children_wp[where dev=dev and t="t" and
                                        cover_ids ="(available_range o cap_of o untyped_map o fst) v" and
                                        parent_cptr'="cptr_of (untyped_map (fst v))"
                                  for v, simplified sep_wp_simp];
          try_solves \<open>simp\<close>)
           apply (simp add: Let_unfold)
           apply (erule (1) bspec)
          apply simp
          apply meson
         apply (clarsimp simp: allocation_map_def)
        apply (simp, erule bspec)
        apply (rule cap_of_make_untyped_map[simplified]; clarsimp)
       apply (fastforce)
      apply (clarsimp)
      apply (rule the_map_of_elim; clarsimp?)
      apply (meson in_set_takeD)
     apply clarsimp+
   apply wpfix
   apply (rule hoare_weaken_pre)
    apply (erule lookup_cptr_wp; clarsimp)
    apply (metis Domain.intros Domain_fst)
   apply clarsimp
   apply (rule conjI)
    apply (subst (asm) ball_simps(9)[symmetric, where f=fst])
    apply (erule bspec)
    apply (subst image_set)
    apply (rule cptr_of_make_untyped_map[simplified]; clarsimp)
    apply (drule_tac f=fst in imageI)
    apply clarsimp
   apply assumption
  apply (frule distinct_fstD)
  apply clarsimp
  apply (sep_fold_cancel)+
  apply (rule sep_map_sep_foldI)
  apply (subgoal_tac "set (collect_children untyped_derivations) = (\<Union>x\<in>set untyped_derivations. set (snd x))")
   apply (clarsimp simp: sep_list_conj_sep_map_set_conj distinct_zipI1 distinct_map_comp[where f=unat] unat_inj distinct_map_comp'  )
   apply (clarsimp simp: si_null_caps_at_def si_caps_at_def objects_empty_def)
   apply (clarsimp simp: sep_map_set_squash[OF untyped_derivations_inject, simplified]  sep_map_set_conj_Union[OF _ helper])
   apply (sep_cancel)+
   apply (comp_folder comp: comp_folder[where g=fst])+
   apply (simp only: sep.prod.reindex[symmetric, where h=fst, OF distinct_inj_on])
   apply (subst sep_prod_make_untyped_map_zip[where ids="map fst untyped_derivations", simplified]; clarsimp)+
   apply (erule (1) sep_conj_impl[OF _ sep_map_set_conj_impl[simplified]]; clarsimp?)
    apply (erule back_subst[OF _ untyped_cap_helper[symmetric]]; fastforce elim!: in_set_zipE)
   apply (sep_cancel)+
   apply (erule sep_map_set_conj_impl)
    apply (clarsimp simp: on_depleted_untyped_cap_def)
    apply (intro context_conjI)
     apply (drule in_set_zip2, rule is_full_untyped_cap_is_untyped_cap, erule (1) bspec)
    apply (guess_exI)
    apply (subgoal_tac"b \<in> set untyped_caps")
     apply (intro conjI; clarsimp)
     apply (drule (1) bspec[where P=is_full_untyped_cap],
                      erule full_cap_range_available, erule in_set_zip2)
   apply (clarsimp)
  apply (clarsimp simp: collect_children_def List.bind_def)
  done

lemma real_object_at_inter_cdl_objects [simp]:
  "{obj_id. real_object_at obj_id spec} \<inter> dom (cdl_objects spec) = {obj_id. real_object_at obj_id spec}"
  by (auto simp: real_object_at_def)

lemma map_of_nat_unat: "map of_nat (map unat xs) = xs"
  by (clarsimp)

lemma create_objects_sep:
  "\<lbrace> \<guillemotleft>\<And>* map  (\<lambda>(slot, cap).  (sep_map_c (si_cnode_id, slot)) cap) (zip untyped_slots untyped_caps) \<and>*
      si_null_caps_at t si_caps spec (set (collect_children untyped_derivations)) \<and>*
      (\<And>* obj_id\<in>(set (collect_children untyped_derivations)). the (t obj_id) \<mapsto>o Untyped) \<and>*
      si_objects \<and>* R\<guillemotright> and
     K (well_formed spec \<and>
        untyped_map = make_untyped_map (map fst untyped_derivations) (map fst untyped_list)
                                       (map snd untyped_list) untyped_caps \<and>
        valid_untypeds (map fst untyped_derivations) (map fst untyped_list)
                       (map snd untyped_list) untyped_caps \<and>
        valid_derivations spec untyped_derivations untyped_map \<and>
        map_of (zip_region (collect_children untyped_derivations) free_cptrs) = si_caps \<and>
        list_all (\<lambda>n. n < 2 ^ si_cnode_size) untyped_slots \<and>
        list_all (\<lambda>n. n < 2 ^ si_cnode_size) (list_region free_cptrs) \<and>
        list_all (\<lambda>c. is_device_cap c = dev) untyped_caps \<and>
        distinct_sets (map cap_free_ids untyped_caps) \<and>
        map (unat \<circ> fst) untyped_list = untyped_slots \<and>
        (\<forall>obj\<in>ran (cdl_objects spec). object_domain obj = minBound) \<and>
        (\<And>* map (\<lambda>(parent, children).
                   (=) (aligned_allocations spec ((Min \<circ> available_range \<circ> cap_of \<circ> untyped_map) parent)
                                            children))
                untyped_derivations) t \<and>
        length (collect_children untyped_derivations) \<le> length_region free_cptrs \<and>
        valid_slot_region free_cptrs) \<rbrace>
   create_objects spec untyped_list free_cptrs (untyped_derivations :: (machine_word \<times> (machine_word list)) list)
   \<lbrace>\<lambda>rv s.
     \<guillemotleft>(K (si_caps = fst rv \<and>
          snd rv = drop_region (length (collect_children untyped_derivations)) free_cptrs) and
      \<And>* map (\<lambda>(slot, cap). on_depleted_untyped_cap (sep_map_c (si_cnode_id, slot)) cap) (zip untyped_slots untyped_caps)) \<and>*
      objects_empty spec t (set (collect_children untyped_derivations)) \<and>*
      si_caps_at t si_caps spec dev (set (collect_children untyped_derivations)) \<and>*
      si_objects  \<and>* R\<guillemotright> s\<rbrace>"
  apply (rule hoare_name_pre_state, clarsimp)
  apply (rule hoare_chain[OF retype_untypeds_wp_helper[where t=t and R=R]])
                       apply (clarsimp)+
                      apply (fastforce)
                     apply (assumption | rule refl)+
                apply (clarsimp simp: valid_derivations_def Let_unfold list_all_iff)
                apply (drule_tac x="(a,b)" in bspec, assumption, clarsimp, drule_tac x=child in  bspec, assumption )
                apply (clarsimp simp: spec_object_size_def)
               apply (fastforce simp: unat_less_2_si_cnode_size list_all_iff)
              apply clarsimp
             apply (clarsimp simp: valid_derivations_def valid_untypeds_def Let_unfold list_all_iff)+
         apply (drule_tac x="(a,b)" in bspec, assumption, clarsimp, drule_tac x=child in  bspec, assumption )
         apply (clarsimp simp: spec_object_size_def)
        apply clarsimp
       apply (clarsimp simp: valid_derivations_def Let_unfold list_all_iff)
       apply (rule refl)
      apply (clarsimp simp: valid_derivations_def Let_unfold list_all_iff)+
   apply (fastforce simp: zip_map_map comp_def apfst_def map_prod_def)+
  done

lemma map_of_zip_not_none: "x \<in> set xs \<Longrightarrow> length xs \<le> length ys \<Longrightarrow> map_of (zip xs ys) x \<noteq> None"
  apply (induct xs; clarsimp)
  apply (case_tac ys; clarsimp)
  by (simp add: map_of_zip_is_Some')


lemma sep_map_set_conj_set_append: "distinct (xs@ys) \<Longrightarrow> sep_map_set_conj P (set (xs @ ys)) = (sep_map_set_conj P (set xs) \<and>* sep_map_set_conj P (set ys))"
 apply (induct xs; clarsimp)
 apply (case_tac ys; clarsimp)
 apply (rule ext; rule iffI; sep_solve)
done

lemma sep_map_set_conj_set_take_drop: "sep_map_set_conj P (set xs) s \<Longrightarrow> distinct xs \<Longrightarrow> (sep_map_set_conj P (set (take n xs)) \<and>*  sep_map_set_conj P (set (drop n xs))) s"
 by (clarsimp simp: append_take_drop_id[where n=n, symmetric] sep_map_set_conj_set_append[symmetric]  )






lemma map2_map_left: "map2 (\<lambda>x. f (g x)) xs ys = map2 f (map g xs) ys"
  apply (induct xs arbitrary:ys ; clarsimp)
  apply (case_tac ys; clarsimp)
  done

lemma filter_notin: "\<not> x \<in> set xs \<Longrightarrow> filter (\<lambda>y. y \<noteq> x) xs = xs"
  by (induct xs; clarsimp)

lemma sep_map_map_of: "\<lbrakk>length xs \<le> length ys; distinct xs; distinct ys\<rbrakk> \<Longrightarrow>
      (SETSEPCONJ x:set xs. f (the (map_of (zip xs ys) x))) = (SETSEPCONJ x:set (take (length xs) ys). f x)"
  apply (induct xs arbitrary:ys; clarsimp)
  apply (case_tac ys; clarsimp)
  apply (subst sep.prod.insert_remove)
   apply (clarsimp)
  apply (clarsimp)
  apply (subst set_minus_filter_out)
  apply (subst filter_notin)
   apply (clarsimp)
   apply (meson in_set_takeD)
  apply (subst sep_map_set_conj_subst[OF arg_cong])
   apply (rule_tac s="the (map_of (zip xs list) x)" in sym)
   apply (clarsimp)
  apply (drule_tac x=list in meta_spec)
  apply (clarsimp)
  done

lemma si_null_cap_at_unfold:
  "\<lbrakk>cap_map obj_id \<noteq> None; the (cap_map obj_id) < 2 ^ si_cnode_size;
    cdl_objects spec obj_id \<noteq> None; t obj_id \<noteq> None\<rbrakk> \<Longrightarrow>
  si_null_cap_at t cap_map spec obj_id = (si_cnode_id, unat (the (cap_map obj_id))) \<mapsto>c NullCap"
  by (rule ext, clarsimp simp: si_null_cap_at_def)

lemma [simp]: "collect_children ((a, b) # xs) = b @ collect_children xs"
  by (clarsimp simp: collect_children_def)

lemma distinct_collection': "distinct_sets (map (set o snd) xs) \<Longrightarrow> list_all distinct (map snd xs) \<Longrightarrow> distinct (collect_children xs)"
  apply (induct xs; clarsimp)
   apply (clarsimp simp: collect_children_def)
  apply (erule disjoint_subset2[rotated])
  apply (simp add: collect_children_def set_list_bind)
  done

lemma distinct_collection[simp]: "valid_derivations spec untyped_derivations untyped_caps \<Longrightarrow> distinct (collect_children untyped_derivations)"
  apply (rule distinct_collection')
   apply (clarsimp simp: valid_derivations_def)
  apply (clarsimp simp: valid_derivations_def Let_unfold)
  apply (simp add: list_all_iff)
  done

lemma is_in_sep_list_conjD': "sep_list_conj (map (\<lambda>x. is (g x)) xs) s \<Longrightarrow> \<exists>x. x \<in> set xs \<and> v \<in> dom (g x) \<Longrightarrow> s v \<noteq> None "
  apply (clarsimp)
  apply (subst (asm) sep_list_conj_map_remove1, assumption)
  apply (drule  is_in_rangeD)
   apply (fastforce simp: dom_def)+
  done

lemma in_collection_in_derivations: "x \<in> set (collect_children untyped_derivations) \<Longrightarrow>
    \<exists>parent family. x\<in> set family \<and> (parent, family) \<in> set untyped_derivations"
  apply (induct untyped_derivations; clarsimp simp: collect_children_def List.bind_def)
  apply blast
  done

lemma create_objects_sep':
  "\<lbrace> \<guillemotleft>\<And>* map  (\<lambda>(slot, cap).  (sep_map_c (si_cnode_id, unat slot)) cap) (zip untyped_slots untyped_caps) \<and>*
      (\<And>* cptr\<in>set_region free_cptrs.
            (si_cnode_id, unat cptr) \<mapsto>c NullCap) \<and>*
      (\<And>* obj_id\<in>(set (collect_children untyped_derivations)). the (t obj_id) \<mapsto>o Untyped) \<and>*
      si_objects \<and>* R\<guillemotright> and
     K (well_formed spec \<and>
        untyped_map = make_untyped_map (map fst untyped_derivations) (map fst untyped_list)
                                       (map snd untyped_list) untyped_caps \<and>
        valid_untypeds (map fst untyped_derivations) (map fst untyped_list)
                       (map snd untyped_list) untyped_caps \<and>
        valid_derivations spec untyped_derivations untyped_map \<and>
        set (collect_children untyped_derivations) \<subseteq> dom (cdl_objects spec) \<and>
        list_all (\<lambda>n. n < 2 ^ si_cnode_size) untyped_slots \<and>
        list_all (\<lambda>n. n < 2 ^ si_cnode_size) (list_region free_cptrs) \<and>
        list_all (\<lambda>c. is_device_cap c = dev) untyped_caps \<and>
        map fst untyped_list = untyped_slots \<and>
        (\<forall>obj\<in>ran (cdl_objects spec). object_domain obj = minBound) \<and>
        (\<And>* map (\<lambda>(parent, children).
                   (=) (aligned_allocations spec ((Min \<circ> available_range \<circ> cap_of \<circ> untyped_map) parent)
                                            children))
                untyped_derivations) t \<and>
        length (collect_children untyped_derivations) \<le> length_region free_cptrs \<and>
        valid_slot_region free_cptrs)\<rbrace>
   create_objects spec untyped_list free_cptrs (untyped_derivations :: (machine_word \<times> (machine_word list)) list)
   \<lbrace>\<lambda>_ s.
     \<guillemotleft>\<And>* map (\<lambda>(slot, cap). on_depleted_untyped_cap (sep_map_c (si_cnode_id, unat slot)) cap) (zip untyped_slots untyped_caps) \<and>*
      objects_empty spec t (set (collect_children untyped_derivations)) \<and>*
      si_caps_at t (map_of (zip_region (collect_children untyped_derivations) free_cptrs)) spec dev (set (collect_children untyped_derivations)) \<and>*
      (\<And>* cptr\<in>set_region (drop_region (length (collect_children untyped_derivations)) free_cptrs).
            (si_cnode_id, unat cptr) \<mapsto>c NullCap) \<and>*
      si_objects  \<and>* R\<guillemotright> s\<rbrace>"
  apply (rule hoare_chain[OF create_objects_sep[where untyped_caps=untyped_caps and
                                                      untyped_slots="(map (unat o fst) untyped_list)" and
                                                      untyped_map=untyped_map]];
         clarsimp simp: pred_conj_def)
   defer
   apply (sep_solve)
  apply (intro conjI)
       defer
       apply (fastforce)
      apply (clarsimp simp: list_all_iff)
  using unat_less_2_si_cnode_size' apply auto[1]
     apply (fastforce)
    apply (fastforce simp: valid_untypeds_def)
   apply (clarsimp simp: valid_untypeds_def, sep_cancel+)
  apply (erule sep_conj_impl)
   apply (subst (asm) map2_map_left[where g=unat])
   apply (clarsimp)
  apply (sep_drule sep_map_set_conj_set_take_drop[where n="length (collect_children untyped_derivations)"])
   apply (clarsimp)
  apply (sep_flatten)
  apply (erule sep_conj_impl)
   defer
   apply (sep_cancel)+
   apply (subst  map2_map_left[where g=unat], clarsimp)
  apply (clarsimp simp: comp_def)
  apply (clarsimp simp: list_all_iff)
  apply (clarsimp simp: si_null_caps_at_def)
  apply (subst sep_map_set_conj_subst[OF si_null_cap_at_unfold])
      apply (simp add: map_of_zip_not_none)
     prefer 4
     apply (subst sep_map_map_of; clarsimp?)
    apply (erule valid_slot_region_less)
    apply (rule set_rev_mp)
     apply (rule the_map_of_zip_inR; clarsimp)
    apply (simp add: set_take_subset)
   defer
   apply (rule_tac is_in_sep_list_conjD'[where xs=untyped_derivations and
                                               g="\<lambda>(parent, children). (aligned_allocations spec
                                                  ((Min o available_range \<circ> cap_of \<circ> untyped_map)
                                                  parent) children)" and
                                               s=t])
    apply (clarsimp)
    apply (simp add: prod_lift_lambda)
   apply (clarsimp)
   apply (frule in_collection_in_derivations, clarsimp)
   apply (rule exI)+
   apply (intro conjI)
    apply (fastforce)
   apply (clarsimp)
   apply (clarsimp simp: aligned_allocations_def)
   apply (rule exI)
   apply (rule mapp_app)
   apply (simp add: in_list_allocate)
  apply (clarsimp simp: dom_def)
  apply (drule (1) set_rev_mp)
  apply (clarsimp)
  done

end
