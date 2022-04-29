(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Retype_DP
imports Invocation_DP
begin

lemma create_objects_mapM_x:
  "create_objects ids (Some obj) = mapM_x (\<lambda>id. create_objects [id] (Some obj)) ids "
  proof (induct ids)
    case Nil
    show ?case
      by (simp add:create_objects_def mapM_x_Nil simpler_modify_def return_def)
  next
    case Cons
    show ?case
      apply (simp add:mapM_x_Cons)
      apply (subst local.Cons[symmetric])
      apply (rule ext)
      apply (case_tac x)
      apply (clarsimp simp:create_objects_def simpler_modify_def bind_def)
      apply (rule ext)
      apply clarsimp
    done
qed

lemma create_objects_mapM_x':
  "ids = map (\<lambda>x. {x}) ids' \<Longrightarrow>
  create_objects ids (Some obj) = mapM_x (\<lambda>id. create_objects [{id}] (Some obj)) ids' "
  apply simp
  proof (induct ids' arbitrary: ids)
    case Nil
    show ?case
      by (simp add:create_objects_def mapM_x_Nil simpler_modify_def return_def)
  next
    case Cons
    show ?case
      apply (simp add:mapM_x_Cons)
      apply (subst local.Cons[symmetric])
       apply simp
      apply (rule ext)
      apply (case_tac x)
      apply (clarsimp simp:create_objects_def simpler_modify_def bind_def)
      apply (rule ext)
      apply clarsimp
    done
qed

lemma pick_rev:
  assumes "target_object_ids = map (\<lambda>x. {x}) ids"
  shows "ids = map (\<lambda>x. pick x) target_object_ids"
  unfolding assms by (induct ids) auto

lemma create_objects_wp:
  notes set_map[simp del]
  shows
  "\<lbrace> K (obj_refs = map (\<lambda>x. {x}) (map pick obj_refs) \<and> distinct (map pick obj_refs) )
  and <(\<And>* ptr\<in>pick ` set obj_refs. ptr \<mapsto>o Untyped) \<and>* P > \<rbrace>
  create_objects obj_refs (Some obj) \<lbrace>\<lambda>r s. <(\<And>* ptr\<in>pick ` set obj_refs. ptr \<mapsto>o obj) \<and>* P > s \<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (subst create_objects_mapM_x'[where ids' = "map pick obj_refs"])
   apply simp
  apply (rule hoare_pre)
   apply (rule hoare_strengthen_post)
    apply (rule cdl.mapM_x_sep')
   apply (rule create_one_wp)
   apply (subst set_map[symmetric])
   apply (subst sep_list_conj_sep_map_set_conj[symmetric])
    apply (simp add:distinct_map)
   apply simp
  apply (clarsimp simp: set_map[symmetric])
  apply (subst(asm) sep_list_conj_sep_map_set_conj[symmetric])
   apply (simp add:distinct_map)
  apply (simp add:set_map)
  apply sep_cancel
  apply (erule sep_list_conj_impl[rotated])
  apply (simp add:list_all2_iff)
  apply (clarsimp simp:zip_map1 zip_map2
    set_zip_same
    Fun.comp_def split_def)
  proof (induct obj_refs)
    case Nil
    show ?case
      using Nil.prems
      by simp
  next
    case Cons
    show ?case
      using Cons.prems
    apply clarsimp
    apply (erule disjE)
     apply (fastforce simp:sep_any_def)
    apply (erule(3) Cons.hyps)
    done
  qed

lemma nonempty_pick_in:
  "a\<noteq>{} \<Longrightarrow> pick a \<in> a"
  by (metis all_not_in_conv someI_ex)

lemma retype_region_wp:
  "\<lbrace> K (default_object target_type target_bits minBound = Some obj
     \<and> target_type \<noteq> UntypedType \<and> distinct (map pick obj_refs)
     \<and> obj_refs = map (\<lambda>x. {x}) (map pick obj_refs)
     \<and> set (map pick obj_refs) \<subseteq> obj_range )
     and (\<lambda>s. cdl_current_domain s = minBound)
     and <(\<And>* ptr\<in>set (map pick obj_refs). ptr \<mapsto>o Untyped) \<and>* P > \<rbrace>
  retype_region target_bits target_type obj_refs
  \<lbrace>\<lambda>r s. <(\<And>* ptr\<in>set (map pick obj_refs). ptr \<mapsto>o obj)
   \<and>* P > s\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (rule hoare_pre)
   apply (clarsimp simp:retype_region_def)
   apply wp
    apply (rule_tac P="current_domain = minBound" in hoare_gen_asm)
    apply (wp create_objects_wp | simp)+
  done

lemma map_zip_first_simp:
  "length x = length y \<Longrightarrow> map (\<lambda>a. g (fst a)) (zip x y) = map g x"
  proof (induct x arbitrary: y)
    case Nil
    show ?case
      by simp
  next
    case Cons
    show ?case
      using local.Cons.prems
      apply (case_tac y)
       apply clarsimp+
      apply (simp add:local.Cons.hyps)
    done
qed

lemma update_range_simple:
  "idx \<noteq> 0 \<Longrightarrow> ptr \<le> ptr + of_nat idx \<Longrightarrow>
      update_range old_range ptr idx = old_range - {..<ptr + of_nat idx}"
  by (clarsimp simp: update_range_def)

lemma update_available_range_wp:
  "\<lbrace> <cap_ref \<mapsto>c - \<and>* P> \<rbrace>
  update_available_range ptr idx cap_ref cap
  \<lbrace>\<lambda>_ . <cap_ref \<mapsto>c set_available_range cap (update_range (untyped_cap_range cap) ptr idx) \<and>* P> \<rbrace>"
  apply (unfold update_available_range_def, simp only: Let_unfold fun_app_def)
  apply (wp sep_wp: set_cap_wp)
  apply (clarsimp simp: pred_conj_def update_range_def)
  apply (intro conjI impI; sep_solve)
  done

lemmas update_available_range_wp' = update_available_range_wp
  [where cap="UntypedCap dev b c" for dev b c, simplified]

lemma reset_cap_asid_untyped_cap_eqD:
  "reset_cap_asid c = UntypedCap dev a b
  \<Longrightarrow> c = UntypedCap dev a b"
  by (simp add:reset_cap_asid_def split:cdl_cap.splits)

lemma dummy_detype_if_untyped:
  "\<lbrakk>finite obj_range ;<(\<And>* ptr\<in>obj_range. ptr \<mapsto>o Untyped) \<and>* P > s\<rbrakk>
  \<Longrightarrow> (detype obj_range s) = s"
  apply (case_tac s,clarsimp simp:detype_def sep_set_conj_def)
  apply (rule ext)
  apply (clarsimp simp:sep_state_projection_def sep_conj_def)
  apply (subst (asm) sep.prod.remove)
   apply simp+
  apply (clarsimp simp:sep_map_o_conj image_def)
  apply (drule_tac f = sep_heap in arg_cong)
  apply (drule_tac x = "(x,Fields)" in fun_cong)+
  apply (case_tac xa,case_tac y)
  apply (clarsimp simp:plus_sep_state_def sep_state_add_def asid_reset_def
    intent_reset_def update_slots_def object_wipe_slots_def sep_disj_sep_state_def
    object_to_sep_state_def object_project_def object_clean_def
    sep_state_disj_def)
  apply (drule map_disj_None_right'[rotated])
   apply simp
  apply (clarsimp simp: map_add_def split:option.splits)
  apply (case_tac z)
    apply (clarsimp simp:plus_sep_state_def sep_state_add_def asid_reset_def
    intent_reset_def update_slots_def object_wipe_slots_def sep_disj_sep_state_def
    object_to_sep_state_def object_project_def object_clean_def
    sep_state_disj_def)+
  done

lemma mapME_x_wp:
  "\<forall>x \<in> set xs. \<lbrace>P\<rbrace> f x \<lbrace>\<lambda>rv. P\<rbrace>,\<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> mapME_x f xs \<lbrace>\<lambda>rv. P\<rbrace>,\<lbrace>E\<rbrace>"
  proof (induct xs)
  case Nil
  show ?case
   apply (simp add: mapME_x_def sequenceE_x_def)
   by wp
  next
  case Cons
  show ?case
   using Cons.prems
   apply (simp add: mapME_x_def sequenceE_x_def)
   apply (fold mapME_x_def sequenceE_x_def)
   including no_pre
   apply wp
    apply (rule Cons.hyps)
    apply fastforce
   apply fastforce
   done
  qed

lemma hoare_whenE_not:
  "\<lbrace>\<lambda>s. R () s \<and> \<not>P\<rbrace> whenE P f \<lbrace>R\<rbrace>, \<lbrace>E\<rbrace>"
  unfolding whenE_def by clarsimp wp

lemma reset_untyped_cap_wp_trivial:
  "\<lbrace><uref \<mapsto>c UntypedCap dev obj_range free_range \<and>* P>
     and (\<lambda>_. obj_range = free_range)\<rbrace>
   reset_untyped_cap uref
   \<lbrace>\<lambda>_. <uref \<mapsto>c UntypedCap dev obj_range free_range \<and>* P>\<rbrace>"
  apply (rule hoare_name_pre_state, clarsimp simp: reset_untyped_cap_def)
  apply (sep_frule (direct) opt_cap_sep_imp, clarsimp dest!: reset_cap_asid_untyped_cap_eqD)
  apply (wp hoare_whenE_not mapME_x_wp)
  apply (clarsimp)
  done

lemma reset_untyped_cap_wp_trivial':
  "\<lbrace><uref \<mapsto>c UntypedCap dev obj_range free_range \<and>* P>
     and (\<lambda>_. obj_range = free_range)\<rbrace> reset_untyped_cap uref
    \<lbrace>\<lambda>_. <uref \<mapsto>c UntypedCap dev obj_range free_range \<and>* P>\<rbrace>, -"
  by (wp reset_untyped_cap_wp_trivial)

lemma reset_untyped_cap_wp_trivial'':
  "\<lbrace><uref \<mapsto>c UntypedCap dev obj_range free_range \<and>* P>
     and (\<lambda>_. obj_range = free_range) and R ()\<rbrace> reset_untyped_cap uref \<lbrace>\<lambda>y. R y\<rbrace>, -"
  unfolding validE_R_def
  apply (rule hoare_name_pre_stateE)
  apply (clarsimp simp: reset_untyped_cap_def)
  apply (sep_frule (direct) opt_cap_sep_imp, clarsimp dest!: reset_cap_asid_untyped_cap_eqD)
  apply (wp hoare_whenE_not mapME_x_wp)
  apply (clarsimp)
  done

crunch reset_untyped_cap
  for cdl_current_domain[wp]: "\<lambda>s. P (cdl_current_domain s)"
  (wp: mapM_x_wp' mapME_x_inv_wp crunch_wps unless_wp
   simp: detype_def crunch_simps)

crunch invoke_untyped
  for cdl_current_domain[wp]: "\<lambda>s. P (cdl_current_domain s)"
  (wp: mapM_x_wp' mapME_x_inv_wp crunch_wps unless_wp
   simp: detype_def crunch_simps validE_E_def)

lemma create_cap_wp:
  "\<lbrace> < ((fst xs) \<mapsto>c cap \<and>* R) >\<rbrace>
   create_cap new_type sz parent_slot dev xs
   \<lbrace>\<lambda>_. < ((fst xs) \<mapsto>c (default_cap new_type (snd xs) sz dev) \<and>* R) > \<rbrace>"
  apply (clarsimp simp: create_cap_def split: prod.split, wp add: set_parent_wp sep_wp: set_cap_wp)
  apply clarsimp
  apply sep_solve
  done

(* FIXME: move to sep-CapDL  *)
lemma sep_lift_generic:
  "\<And>sep_lift.
   (\<And>R. \<lbrace>g (R)\<rbrace> f \<lbrace>\<lambda>x s. (P x \<and>* R) (sep_lift s)\<rbrace>) \<Longrightarrow>
     \<lbrace>g (ALLS x. P x \<longrightarrow>* R x)\<rbrace> f \<lbrace>\<lambda>rv s . R rv (sep_lift s)\<rbrace>"
  apply (rule hoare_chain, assumption)+
   apply (fastforce)
  apply (clarsimp simp: sep_conj_def)
  using sep_add_commute sep_disj_commuteI sep_implD by fastforce

(* FIXME: move to sep-CapDL  *)
lemma sep_lift_generic_E:
  "\<And>sep_lift.
   (\<And>R. \<lbrace>g (R)\<rbrace> f \<lbrace>\<lambda>x s. (P x \<and>* R) (sep_lift s)\<rbrace>, \<lbrace>E\<rbrace>) \<Longrightarrow>
     \<lbrace>g (ALLS x. P x \<longrightarrow>* R x)\<rbrace> f \<lbrace>\<lambda>rv s . R rv (sep_lift s)\<rbrace>, \<lbrace>E\<rbrace>"
  unfolding validE_R_def
  apply (rule hoare_chainE, assumption)+
    apply (fastforce)
   apply (clarsimp simp: sep_conj_def)
  using sep_add_commute sep_disj_commuteI sep_implD apply fastforce
  by (simp)

lemma sep_lift_generic_R:
  "\<And>sep_lift.
   (\<And>R. \<lbrace>g (R)\<rbrace> f \<lbrace>\<lambda>x s. (P x \<and>* R) (sep_lift s)\<rbrace>, -) \<Longrightarrow>
     \<lbrace>g (ALLS x. P x \<longrightarrow>* R x) \<rbrace> f \<lbrace>\<lambda>rv s . R rv (sep_lift s) \<rbrace>, -"
  unfolding validE_R_def
  by (rule sep_lift_generic_E, simp)

lemma distinct_pick: "\<lbrakk>distinct xs;  \<forall>s\<in>set xs. \<exists>v. {v} = s\<rbrakk> \<Longrightarrow> distinct (map pick xs)"
  apply (induct xs; clarsimp?)
  apply (clarsimp simp: Ball_def)
  apply (erule_tac x=aa in allE)
  apply (clarsimp simp: pick_def)
  done

lemma distinct_singleton_union_eq: "\<lbrakk>distinct xs; \<forall>s\<in>set xs. \<exists>v. {v} = s\<rbrakk>
     \<Longrightarrow>  \<Union> (set xs) = pick ` (set xs)"
  by (induct xs; clarsimp)

lemma map_zip_helper: "map (\<lambda>x. f (fst x)) (zip xs ys) = map f (take (length ys) xs)"
  apply (induct xs arbitrary: ys ; clarsimp?)
  apply (case_tac ys; clarsimp)
done

lemma map_zip_helper': "map (\<lambda>x. f (fst x)) (zip xs (map g [0..<length xs])) = map f xs"
  apply (induct xs; clarsimp)
  apply (subst map_zip_helper, clarsimp)
done

lemma [simp]: "fst (case v of (x, y) \<Rightarrow> (f x, g y)) = ((f (fst v))) "
 by (cases v, simp)

lemma [simp]: "snd (case v of (x, y) \<Rightarrow> (f x, g y)) = ((g (snd v))) "
 by (cases v, simp)

lemma [simp]: "(case case v of (x, y) \<Rightarrow> (f x, g y) of (x', y') \<Rightarrow> f' x' y') = ( f' (f (fst v)) (g (snd v)))"
 by (cases v, clarsimp)

lemma invoke_untyped_wp:
  "\<lbrace> K (default_object nt ts minBound = Some obj \<and> nt \<noteq> UntypedType
     \<and> length slots = n  \<and> (generate_range (aligned_ptr) nt sz n) = created_range
     \<and> distinct created_range \<and> base_ptr = Min obj_range \<and> sz = (obj_bits_cdl nt ts) \<and>
     new_idx = unat (aligned_ptr + (of_nat n << sz) - base_ptr)  \<and>
     (\<not> has_kids \<longrightarrow> aligned_ptr = Min (get_range ((\<noteq>) {}) free_range obj_range))
     \<and> (has_kids \<longrightarrow> aligned_ptr = alignUp (Min (get_range ((\<noteq>) {}) free_range obj_range)) sz)
     \<and> (\<not> has_kids \<longrightarrow> free_range = obj_range))
     and (\<lambda>s. cdl_current_domain s = minBound)
     and < \<And>* map (\<lambda>dest_slot. dest_slot \<mapsto>c NullCap) slots
    \<and>*(\<And>* ptr\<in>\<Union> (set created_range). ptr \<mapsto>o Untyped)
    \<and>* uref \<mapsto>c UntypedCap dev obj_range free_range
    \<and>* P > \<rbrace>
  invoke_untyped (Retype uref nt ts slots has_kids n)
  \<lbrace>\<lambda>_ s.
  < \<And>* map (\<lambda>(dest_slot, obj_refs). dest_slot \<mapsto>c (default_cap nt obj_refs ts dev)) (zip slots created_range)
  \<and>* (\<And>* ptr\<in>\<Union> (set created_range). ptr \<mapsto>o obj)
  \<and>* uref \<mapsto>c UntypedCap dev obj_range (update_range obj_range base_ptr new_idx)
  \<and>* P > s \<rbrace>, -"
  apply (simp add: validE_R_def)
  apply (rule hoare_name_pre_stateE)
  apply (clarsimp simp:invoke_untyped_def unless_def)
  apply (rule hoare_pre)
   apply wp
       apply (wp sep_hoare_fold_mapM_x[OF create_cap_wp[where cap=NullCap], simplified])
      apply (wp retype_region_wp[simplified sep_wp_simp, THEN sep_lift_generic])
     apply (wp update_available_range_wp[simplified sep_wp_simp, THEN sep_lift_generic])
    apply wp
   apply wp
   apply (rule reset_untyped_cap_wp_trivial'')
  apply (clarsimp)
  apply (rule conjI, intro impI, clarsimp)
   apply (sep_frule (direct) opt_cap_sep_imp[where p=uref], clarsimp)
   apply (drule reset_cap_asid_untyped_cap_eqD, simp)
   apply (intro conjI)
       apply (fastforce)
      apply (erule distinct_pick)
      apply (clarsimp simp: comp_def generate_range_def)
     apply (clarsimp simp: comp_def generate_range_def)
    apply (fastforce)
   apply (frule distinct_singleton_union_eq)
    apply (clarsimp simp: generate_range_def, clarsimp)
   apply (sep_cancel)+
   apply (rule sep_map_sep_foldI)
   apply (subgoal_tac "(\<And>* map (\<lambda>x. fst x \<mapsto>c NullCap)
            (zip slots (generate_range (alignUp (Min (get_range ((\<noteq>) {}) free_range obj_range)) (obj_bits_cdl nt ts)) nt (obj_bits_cdl nt ts) (length slots))))
             = (\<And>* map (\<lambda>x. x \<mapsto>c NullCap) slots)")
    prefer 2
    apply (rule arg_cong)
    apply (clarsimp simp: generate_range_def)
    apply (subst map_zip_helper', simp)
   apply (clarsimp)
   apply (sep_cancel)+
   apply (clarsimp simp: generate_range_def zip_map2 map_zip_helper comp_def)
  apply (intro impI, clarsimp)
  apply (sep_frule (direct) opt_cap_sep_imp[where p=uref], clarsimp)
  apply (drule reset_cap_asid_untyped_cap_eqD; clarsimp)
  apply (intro conjI)
      apply (sep_solve)
     apply (clarsimp)
    apply (erule distinct_pick)
    apply (clarsimp simp: comp_def generate_range_def)
   apply (clarsimp simp: comp_def pick_def generate_range_def)
  apply (frule  distinct_singleton_union_eq )
   apply (clarsimp simp: generate_range_def, clarsimp)
  apply (sep_cancel)+
  apply (rule sep_map_sep_foldI)+
  apply (clarsimp simp: generate_range_def)
  apply (subst map_zip_helper', sep_cancel+)
  apply (clarsimp simp: generate_range_def zip_map2 map_zip_helper comp_def)
  done

lemma mapME_x_singleton:
  "mapME_x f [a] = (f a >>= return)"
  by (simp add:mapME_x_def sequenceE_x_def)

lemma mapME_singleton:
  "mapME f [a] = (doE x \<leftarrow> f a; returnOk [x] odE)"
  by (simp add:mapME_def sequenceE_def)


lemma decode_untyped_invocation_rvu:
  "\<lbrakk>nt \<noteq> UntypedType\<rbrakk> \<Longrightarrow>
  \<lbrace> (\<lambda>s. Q (InvokeUntyped (Retype ref nt (unat ts)
    [(cap_object cnode_cap, unat node_offset)]
    (has_children ref s) (Suc 0))) s)
  and R and K(is_cnode_cap cnode_cap)\<rbrace>
  decode_invocation (UntypedCap dev tot_range free_range) ref [(cnode_cap,cnode_ref)]
  (UntypedIntent (UntypedRetypeIntent nt ts node_index 0 node_offset 1))
  \<lbrace>\<lambda>r. Q r\<rbrace>, \<lbrace>\<lambda>r. R\<rbrace>"
  apply (simp add:decode_invocation_def
    get_untyped_intent_def throw_opt_def
    get_index_def throw_on_none_def
    decode_untyped_invocation_def mapME_x_singleton)
  apply (rule hoare_pre)
  apply (wp unlessE_wp
    lookup_slot_for_cnode_op_rvu' | wpc | clarsimp)+
  done

lemma set_parent_has_children[wp]:
  "\<lbrace>\<top>\<rbrace> set_parent cref uref \<lbrace>\<lambda>r. has_children uref\<rbrace>"
  apply (clarsimp simp add:set_parent_def simpler_modify_def
    valid_def has_children_def gets_def assert_def bind_def
    get_def return_def fail_def)
  apply (case_tac cref)
  apply (auto simp:is_cdt_parent_def)
  done

lemma create_cap_has_children[wp]:
  "\<lbrace>\<top>\<rbrace> create_cap new_type sz uref slot dev \<lbrace>\<lambda>r. has_children uref\<rbrace>"
  apply (clarsimp simp :create_cap_def split_def)
  apply wpsimp
  done

crunch retype_region, update_available_range
  for cdt[wp]: "\<lambda>s. P (cdl_cdt s)"
  (simp: crunch_simps corrupt_intents_def)

crunch retype_region, update_available_range
  for has_children[wp]: "has_children slot"
  (simp: crunch_simps corrupt_intents_def has_children_def is_cdt_parent_def)

lemma invoke_untyped_one_has_children:
  "uinv = (Retype uref nt ts [slot] has_kids (Suc 0))
  \<Longrightarrow> \<lbrace>K(nt \<noteq> UntypedType)\<rbrace> invoke_untyped uinv \<lbrace>\<lambda>r. has_children uref\<rbrace>,-"
  apply (simp add: invoke_untyped_def)
  apply wp
       apply (rule_tac P = "zip [slot] (generate_range
                (if has_kids then alignUp (Min (get_range ((\<noteq>) {}) (available_range untyped_cap) (untyped_cap_range untyped_cap))) (obj_bits_cdl nt ts)
                 else Min (get_range ((\<noteq>) {}) (available_range untyped_cap) (untyped_cap_range untyped_cap)))
                    nt (obj_bits_cdl nt ts) (Suc 0)) \<noteq> []" in hoare_gen_asm)
       apply (rule hoare_strengthen_post[OF mapM_x_accumulate_checks])
         apply (rule create_cap_has_children)
        apply wp
       apply (clarsimp simp: neq_Nil_conv)
       apply (cases slot, fastforce)
      apply (wpsimp wp: unlessE_wp hoare_drop_imps simp: generate_range_def)+
  done

lemma invoke_untyped_exception:
  "uinv = (Retype uref nt ts [dest_slot] has_kids (Suc 0))
  \<Longrightarrow> \<lbrace>K (\<not> has_kids \<longrightarrow> (obj_range = free_range))
     and < dest_slot \<mapsto>c NullCap \<and>* uref \<mapsto>c UntypedCap dev obj_range free_range
    \<and>* sep_true > \<rbrace>
   invoke_untyped uinv
  -,\<lbrace>\<lambda>r. Q\<rbrace>"
  apply (simp only: invoke_untyped_def validE_E_def)
  apply (rule hoare_name_pre_stateE)
  apply (cases uinv)
  apply clarsimp
  apply (wp unlessE_wp
          | wpc | simp add: reset_untyped_cap_def)+
      apply (rule_tac P = "available_range cap = cap_objects cap" in hoare_gen_asmEx)
      apply (simp add: whenE_def)
     apply wp+
  apply clarsimp
  apply (cut_tac p = "uref" in opt_cap_sep_imp)
   apply sep_solve
  apply (clarsimp dest!: reset_cap_asid_simps2)
  done

lemma invoke_untyped_one_wp:
  fixes "free_range" "obj_range" "nt" "ts"
  defines "aligned_ptr b \<equiv> (if b then alignUp (Min (get_range ((\<noteq>) {}) free_range obj_range)) (obj_bits_cdl nt ts)
                            else Min (get_range ((\<noteq>) {}) free_range obj_range))"
  defines "base_ptr \<equiv> Min obj_range"
  shows
    "uinv = (Retype uref nt ts [dest_slot] has_kids (Suc 0))
  \<Longrightarrow> \<lbrace>K (default_object nt ts minBound = Some obj \<and> nt \<noteq> UntypedType
     \<and> aligned_ptr has_kids \<in> tot_free_range \<and> finite tot_free_range
     \<and> (\<not> has_kids \<longrightarrow> (obj_range = free_range)))
     and (\<lambda>s. cdl_current_domain s = minBound)
     and < dest_slot \<mapsto>c NullCap
    \<and>* (\<And>* ptr\<in>tot_free_range. ptr \<mapsto>o Untyped)
    \<and>* uref \<mapsto>c UntypedCap dev obj_range free_range
    \<and>* P > \<rbrace>
  invoke_untyped uinv
  \<lbrace>\<lambda>_ s.
  < dest_slot \<mapsto>c (default_cap nt {aligned_ptr has_kids} ts dev)
  \<and>* aligned_ptr has_kids \<mapsto>o obj
  \<and>* (\<And>* ptr\<in>tot_free_range - {aligned_ptr has_kids}. ptr \<mapsto>o Untyped)
  \<and>* uref \<mapsto>c UntypedCap dev obj_range (update_range obj_range base_ptr (unat (aligned_ptr has_kids + (1 << obj_bits_cdl nt ts) - base_ptr)))
  \<and>* P > s \<rbrace>, -"
  apply simp
  apply (wp invoke_untyped_wp [where free_range = free_range and obj_range = obj_range and
                                     aligned_ptr="aligned_ptr has_kids" and sz = "obj_bits_cdl nt ts" and
                                     obj = obj and base_ptr = base_ptr,
                                     simplified sep_wp_simp, THEN sep_lift_generic_R])
  apply (clarsimp simp: base_ptr_def)
  apply (rule conjI, simp)
  apply (clarsimp simp: generate_range_def)
  apply (rule conjI, simp)
  apply (rule conjI, clarsimp simp: aligned_ptr_def)+
  apply sep_cancel+
  apply (clarsimp simp: sep.prod.remove aligned_ptr_def base_ptr_def split: if_splits; sep_solve)
  done

lemma mark_tcb_intent_error_has_children[wp]:
  "\<lbrace>\<lambda>s. P (has_children ptr s)\<rbrace>
   mark_tcb_intent_error cur_thread b
   \<lbrace>\<lambda>rv s. P (has_children ptr s)\<rbrace>"
  by (wpsimp simp: has_children_def is_cdt_parent_def mark_tcb_intent_error_def update_thread_def
                   set_object_def)

crunch corrupt_frame, corrupt_tcb_intent, corrupt_ipc_buffer
  for cdt[wp]: "\<lambda>s. P (cdl_cdt s)"
  (simp: crunch_simps corrupt_intents_def)

lemma corrupt_ipc_buffer_has_children[wp]:
  "\<lbrace>\<lambda>s. P (has_children ptr s)\<rbrace>
  corrupt_ipc_buffer cur_thread b
  \<lbrace>\<lambda>rv s. P (has_children ptr s)\<rbrace>"
  by (simp add: has_children_def is_cdt_parent_def | wp)+

lemma update_thread_intent_has_children[wp]:
  "\<lbrace>\<lambda>s. P (has_children ptr s)\<rbrace>
  update_thread cur_thread (cdl_tcb_intent_update f)
  \<lbrace>\<lambda>rv s. P (has_children ptr s)\<rbrace>"
  by (simp add:has_children_def is_cdt_parent_def | wp )+

lemma do_kernel_op_pull_back':
  "\<lbrace>\<lambda>s. P \<lparr>kernel_state = s\<rparr> \<rbrace> oper \<lbrace>\<lambda>r s. Q r \<lparr>kernel_state = s\<rparr>\<rbrace> \<Longrightarrow>
   \<lbrace> P \<rbrace> do_kernel_op oper \<lbrace> Q \<rbrace>"
  apply (wpsimp simp: do_kernel_op_def)
  apply (metis (mono_tags, lifting) unit.exhaust use_valid user_state.surjective
                                    user_state.update_convs(1))
  done

lemma reset_cap_asid_Untyped[simp]:
  "reset_cap_asid c = UntypedCap dev obj_range free_range \<longleftrightarrow>
   c = UntypedCap dev obj_range free_range"
  by (cases c; clarsimp simp: reset_cap_asid_def )

lemma reset_cap_asid_CNode[simp]:
  "is_cnode_cap cnode_cap \<Longrightarrow> reset_cap_asid c = cnode_cap \<longleftrightarrow> c = cnode_cap"
  by (cases cnode_cap; cases c; clarsimp simp: cap_type_def reset_cap_asid_def )

lemma seL4_Untyped_Retype_sep:
  "\<lbrakk> cap_object root_cnode_cap = root_cnode;
     ucptr_slot = offset ucptr root_size;
     is_cnode_cap root_cnode_cap;
     ncptr_slot = offset ncptr root_size;
     unat ncptr_slot_nat = ncptr_slot;
     one_lvl_lookup root_cnode_cap 32 root_size;
     guard_equal root_cnode_cap ucptr 32;
     guard_equal root_cnode_cap croot 32;
     default_object  nt (unat ts) minBound = Some obj;
     aligned_ptr \<in> tot_free_range \<rbrakk> \<Longrightarrow>
   \<lbrace> K (nt \<noteq> UntypedType) and
     \<guillemotleft>root_tcb_id \<mapsto>f (Tcb tcb)
      \<and>* (root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap
      \<and>* (cap_object root_cnode_cap \<mapsto>f CNode (empty_cnode root_size))
      \<and>* (root_cnode, ucptr_slot) \<mapsto>c UntypedCap dev obj_range free_range
      \<and>* (root_cnode, ncptr_slot ) \<mapsto>c NullCap
      \<and>* (\<And>* ptr\<in>tot_free_range. ptr \<mapsto>o Untyped)
      \<and>* (root_tcb_id, tcb_cspace_slot) \<mapsto>c root_cnode_cap
      \<and>* (cap_object root_cnode_cap, offset croot root_size) \<mapsto>c root_cnode_cap
      \<and>* P\<guillemotright>
     and (\<lambda>s. if has_children (root_cnode,ucptr_slot) (kernel_state s)
              then aligned_ptr = alignUp (Min (get_range ((\<noteq>) {}) free_range obj_range))
                                         (obj_bits_cdl nt (unat ts))
              else obj_range = free_range \<and>
                   aligned_ptr = Min (get_range ((\<noteq>) {}) free_range obj_range))\<rbrace>
   seL4_Untyped_Retype ucptr nt ts croot node_index 0 ncptr_slot_nat 1
   \<lbrace>\<lambda>err s.
      (\<not>err \<longrightarrow>
        \<guillemotleft>(root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap
         \<and>* root_tcb_id \<mapsto>f (Tcb tcb)
         \<and>* (root_cnode, ncptr_slot) \<mapsto>c (default_cap nt {aligned_ptr} (unat ts) dev)
         \<and>* aligned_ptr \<mapsto>o obj
         \<and>* (cap_object root_cnode_cap \<mapsto>f CNode (empty_cnode root_size))
         \<and>* (\<And>* ptr\<in>tot_free_range - {aligned_ptr}. ptr \<mapsto>o Untyped)
         \<and>* (root_cnode, ucptr_slot) \<mapsto>c
              UntypedCap dev obj_range
                         (update_range obj_range (Min obj_range)
                                       (unat (aligned_ptr + (of_nat 1 << obj_bits_cdl nt (unat ts))
                                              - Min obj_range)))
         \<and>* (root_tcb_id, tcb_cspace_slot) \<mapsto>c root_cnode_cap
         \<and>* (cap_object root_cnode_cap, offset croot root_size) \<mapsto>c root_cnode_cap
         \<and>* P\<guillemotright> s \<and>
        has_children (root_cnode,ucptr_slot) (kernel_state s))
      \<and>
      (err \<longrightarrow>
        \<guillemotleft>(root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap
         \<and>* root_tcb_id \<mapsto>f (Tcb tcb)
         \<and>* (cap_object root_cnode_cap \<mapsto>f CNode (empty_cnode root_size))
         \<and>* (root_cnode,ucptr_slot) \<mapsto>c UntypedCap dev obj_range free_range
         \<and>* (root_cnode, ncptr_slot) \<mapsto>c NullCap
         \<and>* (\<And>* ptr\<in>tot_free_range. ptr \<mapsto>o Untyped)
         \<and>* (root_tcb_id, tcb_cspace_slot) \<mapsto>c root_cnode_cap
         \<and>* (cap_object root_cnode_cap, offset croot root_size) \<mapsto>c root_cnode_cap
         \<and>* P\<guillemotright> s) \<rbrace>"
  apply (simp add: seL4_Untyped_Retype_def sep_state_projection2_def)
  apply (rule do_kernel_op_pull_back')
  apply clarsimp
  apply (rule hoare_name_pre_state)
  apply (rule hoare_pre)
   apply (rule_tac ?Pd2.0 = "\<lambda>s'. has_children (root_cnode, ucptr_slot) s' =
                                  has_children (root_cnode, ucptr_slot) s \<and> Q s'" for Q
                   in call_kernel_with_intent_allow_error_helper[where check= False and tcb = tcb,
                                                                 simplified, rotated -1])
               apply (elim conjE, assumption)
              apply fastforce
             apply (wp set_cap_wp)
            apply ((wp hoare_vcg_ex_lift set_cap_wp)+)[5]
        apply (rule_tac P = "iv = InvokeUntyped (Retype (root_cnode, ucptr_slot) nt (unat ts)
                                                        [(root_cnode, ncptr_slot)]
                                                        (has_children (cap_object root_cnode_cap,
                                                                       offset ucptr root_size) s)
                                                        1)" in hoare_gen_asmEx)
        apply (simp only: perform_invocation.simps)
        apply (rule hoare_vcg_conj_elimE[where P=P and P'=P for P, simplified, rotated])
         apply wp
         apply (subst conj_assoc[symmetric])
         apply (rule hoare_vcg_conj_liftE_R)
          apply (rule_tac
            invoke_untyped_one_wp
              [where free_range = free_range
                and obj_range = obj_range
                and obj = obj  and dev=dev
                and tot_free_range = tot_free_range and nt=nt and ts="unat ts"
                and uref = "(cap_object root_cnode_cap, offset ucptr root_size)"
                and dest_slot = "(cap_object root_cnode_cap, offset ncptr root_size)", simplified sep_wp_simp, THEN sep_lift_generic_R, simplified])
          apply clarsimp+
          apply (rule_tac s="has_children (cap_object root_cnode_cap, offset ucptr root_size) s" in trans,
                  solves simp, rule refl)
         apply (wp invoke_untyped_one_has_children[where nt=nt and ts="unat ts" and slot="(cap_object root_cnode_cap, offset ncptr root_size)"])
         apply clarsimp+
         apply (rule_tac s="has_children (cap_object root_cnode_cap, offset ucptr root_size) s" in trans,
                 solves simp, rule refl)
        apply (rule hoare_pre)
         apply (rule_tac has_kids = "(has_children (cap_object root_cnode_cap, offset ucptr root_size) s)" in
              invoke_untyped_exception[where dest_slot="(cap_object root_cnode_cap, offset ncptr root_size)" and uref="(cap_object root_cnode_cap, offset ucptr root_size)" and nt=nt and ts="unat ts" and free_range = free_range and obj_range = obj_range])[1]
         apply (clarsimp)
        apply (clarsimp)
        apply (sep_solve)
       apply (wp)
       apply (wp set_cap_wp[simplified sep_wp_simp, THEN sep_lift_generic, simplified])
      apply (rule_tac P =" nt \<noteq> UntypedType
       \<and> c = UntypedCap dev obj_range free_range \<and> cs = [(root_cnode_cap,(root_cnode,offset croot root_size))]" in hoare_gen_asmEx)
      apply (simp only:)
      apply (wp decode_untyped_invocation_rvu)
      apply (clarsimp)
     apply (simp only:lookup_extra_caps_def mapME_singleton)
     apply (rule wp_no_exception_seq)
      apply wp
     apply (wp lookup_cap_and_slot_rvu[where r = root_size and  cap' = "root_cnode_cap"])[1]
    apply (wp lookup_cap_and_slot_rvu[where r = root_size and cap=root_cnode_cap and cap' = "UntypedCap dev obj_range free_range"])[1]
    apply (case_tac "(has_children (cap_object root_cnode_cap, offset ucptr root_size)) s")
     apply (clarsimp)
     apply (intro conjI allI)
          apply (thin_tac "<P \<and>* Q \<and>* (\<lambda>s. True)> s" for P Q s)
          apply (sep_cancel)+
          apply (intro conjI; sep_solve)
         apply (sep_solve)
        apply (fastforce)
       apply (clarsimp simp:user_pointer_at_def Let_def word_bits_def)
       apply (sep_solve)
      apply (clarsimp simp: ep_related_cap_def
                     dest!: reset_cap_asid_simps2 reset_cap_asid_cnode_cap)+
     apply (clarsimp simp:user_pointer_at_def Let_def word_bits_def)
     apply (sep_solve)
    apply (clarsimp simp: ep_related_cap_def user_pointer_at_def Let_def word_bits_def)
    apply (thin_tac "<P \<and>* Q \<and>* (\<lambda>s. True)> s" for P Q s)
    apply (intro conjI)
       apply (sep_cancel)+
       apply (rule conjI)
        apply (sep_solve)+
   apply (clarsimp simp:ep_related_cap_def)+
   apply (wp update_thread_intent_update)
  apply (intro conjI allI impI,simp_all)
    apply (clarsimp simp:ep_related_cap_def)+
    apply sep_solve
   apply (clarsimp, sep_solve)+
  done

(**********************************************************************
 * We need to know the cdt only ever increases when creating objects. *
 *                                                                    *
 * If this is the case, then we can know that UntypedCaps only ever   *
 * become parents, and never lose their children                      *
 **********************************************************************)

crunch schedule
  for cdt_inc[wp]: "\<lambda>s. cdl_cdt s child = parent"
  (wp: crunch_wps simp: crunch_simps)

crunch handle_pending_interrupts
  for cdt_inc[wp]: "\<lambda>s. cdl_cdt s child = parent"
  (wp: simp: crunch_simps)

lemmas gets_the_resolve_cap_sym = gets_the_resolve_cap[symmetric]

lemma unify_failure_cdt_lift:
  "\<lbrace>\<lambda>s. P (cdl_cdt s)\<rbrace> f \<lbrace>\<lambda>r s. P (cdl_cdt s)\<rbrace>
  \<Longrightarrow> \<lbrace>\<lambda>s. P (cdl_cdt s)\<rbrace> unify_failure f \<lbrace>\<lambda>r s. Q r s \<longrightarrow> P (cdl_cdt s)\<rbrace>,
  \<lbrace>\<lambda>r s. Q' r s \<longrightarrow> P (cdl_cdt s)\<rbrace>"
  apply (simp add:unify_failure_def)
  including no_pre
  apply (wp hoare_drop_imps)
  apply (clarsimp simp:validE_def valid_def)
  done

lemma validE_def2:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace> =
  \<lbrace>P\<rbrace> f \<lbrace>\<lambda>v s. (\<forall>e. v = Inl e \<longrightarrow> E e s) \<and> (\<forall>r. v = Inr r \<longrightarrow> Q r s)\<rbrace>"
  apply (clarsimp simp:validE_def valid_def)
  apply (rule iffI)
   apply clarsimp
   apply (drule_tac x = s in spec)
   apply fastforce
  apply clarsimp
  apply (drule_tac x = s in spec)
  apply clarsimp
  apply (drule_tac x = "(a,b)" in bspec)
   apply simp
  apply clarsimp
  apply (case_tac a)
   apply clarsimp+
  done

lemma hoare_drop_impE_R:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. R r s \<longrightarrow> Q s\<rbrace>, -"
  apply (rule validE_validE_R)
  apply (clarsimp simp:validE_def valid_def)
  apply (case_tac a,simp_all)
  apply fastforce
  done

crunch block_thread_on_ipc
  for cdt_inc[wp]: "\<lambda>s. P (cdl_cdt s)"
(wp:hoare_vcg_conj_lift hoare_drop_impE_R
  hoare_drop_imps
  simp:crunch_simps get_thread_def
  ignore:unify_failure)

crunch set_untyped_cap_as_full
  for cdt_inc[wp]: "\<lambda>s. P (cdl_cdt s)"
(wp:hoare_vcg_conj_lift hoare_drop_impE_R
  simp:crunch_simps get_thread_def)

crunch mark_tcb_intent_error
  for cdt_inc[wp]: "\<lambda>s. P (cdl_cdt s)"
(wp:hoare_vcg_conj_lift hoare_drop_impE_R
  simp:crunch_simps)

lemma unify_failure_valid:
  "\<lbrace>\<lambda>s. P s\<rbrace> f \<lbrace>\<lambda>r s. P s\<rbrace>
  \<Longrightarrow> \<lbrace>\<lambda>s. P s\<rbrace> unify_failure f \<lbrace>\<lambda>r s. P s\<rbrace>"
  including no_pre
  apply (simp add:unify_failure_def)
  apply (wp hoare_drop_imps)
  apply (clarsimp simp:validE_def valid_def)
  done

lemma set_parent_other:
  "\<lbrace>\<lambda>s. cdl_cdt s child = Some parent\<rbrace> set_parent dest uref \<lbrace>\<lambda>_ s. cdl_cdt s child = Some parent\<rbrace>"
  apply (simp add:set_parent_def)
  apply wp
  apply auto
  done

lemma invoke_untyped_cdt_inc[wp]:
  "\<lbrace>\<lambda>s. cdl_cdt s child = Some parent \<rbrace>
  invoke_untyped uinv
  \<lbrace>\<lambda>_ s. cdl_cdt s child = Some parent \<rbrace>"
  apply (clarsimp simp:invoke_untyped_def)
  apply (case_tac uinv)
  apply simp
  apply (rule hoare_pre)
  apply (wp unlessE_wp)
      apply (wp mapM_x_wp[OF _ subset_refl])
       apply (simp add:create_cap_def)
        apply (rule hoare_pre)
        apply (wp set_parent_other unless_wp unlessE_wp
               | wpc | simp)+
   apply (simp add: reset_untyped_cap_def validE_def sum.case_eq_if)
   apply (rule_tac Q'="\<lambda>r s. cdl_cdt s child = Some parent" in hoare_post_imp)
    apply simp
   apply (wp whenE_wp mapME_x_inv_wp | simp)+
  apply (clarsimp simp:detype_def)
  done

lemma invoke_untyped_cdt_inc_R[wp]:
  "\<lbrace>\<lambda>s. cdl_cdt s child = Some parent \<rbrace>
  invoke_untyped uinv
  \<lbrace>\<lambda>_ s. cdl_cdt s child = Some parent \<rbrace>, -"
  by wp

lemma object_at_cdl_cdt[simp]:
  "object_at P ptr (s\<lparr>cdl_cdt := a\<rparr>)
   = object_at P ptr s"
  by (simp add: object_at_def)

crunch set_parent
  for tcb_intent[wp]: "\<lambda>s. tcb_at' (\<lambda>tcb. P (cdl_tcb_intent tcb)) ptr s"

lemma throw_on_none_wp:
  "\<lbrace>\<lambda>s. case x of None \<Rightarrow> Q s | Some y \<Rightarrow> P y s\<rbrace> throw_on_none x \<lbrace>P\<rbrace>, \<lbrace>\<lambda>r s. Q s\<rbrace>"
  apply (rule hoare_pre)
   apply (clarsimp simp:throw_on_none_def)
   apply (wp | wpc | simp)+
  apply auto
  done

lemma throw_opt_wp:
  "\<lbrace>\<lambda>s. case x of None \<Rightarrow> Q s | Some y \<Rightarrow> P y s\<rbrace> throw_opt err x \<lbrace>P\<rbrace>, \<lbrace>\<lambda>r s. Q s\<rbrace>"
  apply (rule hoare_pre)
   apply (clarsimp simp:throw_opt_def)
   apply (wp | wpc | simp)+
  apply auto
  done

lemma lookup_cap_rvu':
"\<lbrace>\<lambda>s. (\<forall>c. reset_cap_asid c = reset_cap_asid cap' \<longrightarrow> Q c s) \<and>
    < (thread,tcb_cspace_slot) \<mapsto>c cnode_cap \<and>*
    \<box> (r, word_bits) : cnode_cap cap_ptr \<mapsto>u cap' \<and>* R> s\<rbrace>
     lookup_cap thread cap_ptr
   \<lbrace>Q\<rbrace>, \<lbrace>Q'\<rbrace> "
  apply (clarsimp simp: lookup_cap_def)
  apply (wp lookup_slot_rvu [where cnode_cap=cnode_cap] get_cap_rv)
  apply (clarsimp)
  apply safe
    apply (clarsimp simp: user_pointer_at_def sep_conj_assoc Let_unfold)
    apply (sep_solve)
   apply clarsimp
  apply (sep_solve)
  done

crunch  handle_pending_interrupts
  for cdl_current_thread[wp]: "\<lambda>s. P (cdl_current_thread s)"

crunch  lookup_cap
  for cdl_current_thread[wp]: "\<lambda>s. P (cdl_current_thread s)"
  (wp: hoare_drop_imps)

lemma throw_opt_wp_valid:
  "\<lbrace>P\<rbrace> throw_opt err x \<lbrace>\<lambda>r. P\<rbrace>"
  apply (rule hoare_pre)
   apply (clarsimp simp:throw_opt_def)
   apply (wp | wpc | simp)+
  done

lemma do_notification_transfer_sep_wp:
  "\<lbrace> cdl.lift ((thread, tcb_pending_op_slot) \<mapsto>c - \<and>* P)\<rbrace> do_notification_transfer thread
    \<lbrace>\<lambda>rv. cdl.lift ((thread, tcb_pending_op_slot) \<mapsto>c - \<and>* P)\<rbrace>"
  apply (simp add: do_notification_transfer_def)
  apply (rule hoare_pre)
   apply wp
   apply (rule hoare_post_imp[rotated])
   apply (rule set_cap_wp)
   apply sep_solve
  apply simp
  done

lemma update_thread_no_pending:
  "\<lbrace>no_pending and
    K(\<forall>x. (case cdl_tcb_caps x tcb_pending_op_slot of Some cap \<Rightarrow> \<not> is_pending_cap cap | _ \<Rightarrow> True)\<longrightarrow>
          (case cdl_tcb_caps (t x) tcb_pending_op_slot of Some cap \<Rightarrow> \<not> is_pending_cap cap | _ \<Rightarrow> True))\<rbrace>
    update_thread thread_ptr t \<lbrace>\<lambda>rv. no_pending\<rbrace>"
  unfolding update_thread_def set_object_def
  apply wpsimp
  apply (fastforce simp: opt_cap_def slots_of_def object_slots_def no_pending_def
                   split: if_splits option.splits)
  done

lemma update_thread_tcb_at:
  "\<lbrace>K(\<forall>x. P (t x))\<rbrace>
    update_thread thread_ptr t \<lbrace>\<lambda>rv. tcb_at' P thread_ptr\<rbrace>"
  apply (rule hoare_pre)
  apply (simp add: update_thread_def set_object_def | wp modify_wp | wpc)+
  apply (auto simp: no_pending_def object_at_def)
  done

lemma corrupt_intents_no_pending:
  "no_pending s \<Longrightarrow> no_pending (corrupt_intents a b s)"
  apply (clarsimp simp: no_pending_def corrupt_intents_def opt_cap_def slots_of_def)
  apply (drule_tac x = oid in spec)
  apply (auto split: option.splits cdl_object.splits if_splits
              simp: object_slots_def option.splits)
  done

crunch corrupt_ipc_buffer
  for no_pending[wp]: no_pending
  (wp: crunch_wps update_thread_no_pending corrupt_intents_no_pending)

crunch mark_tcb_intent_error
  for no_pending[wp]: no_pending
  (wp: crunch_wps update_thread_no_pending corrupt_intents_no_pending)

lemma detype_one_wp:
  "<obj_id \<mapsto>o - \<and>* R> s
   \<Longrightarrow> <obj_id \<mapsto>o Untyped \<and>* R> (detype {obj_id} s)"
  apply (clarsimp simp: detype_def sep_any_exist)
  apply (clarsimp simp: sep_state_projection_def sep_map_o_conj sep_any_def)
  apply (rule conjI)
   apply (rule ext)
    apply (clarsimp simp:object_project_def
      restrict_map_def object_to_sep_state_def)
  apply (erule arg_cong[where f = R,THEN iffD1,rotated])
  apply clarsimp
  apply (rule ext)
  apply (clarsimp simp:restrict_map_def split:if_splits)
  done

lemma detype_insert:
  "detype (insert a A) s = detype {a} (detype A s)"
  by (cases s, simp add: detype_def fun_eq_iff)

lemma detype_set_sep_helper:
  "finite S \<Longrightarrow> <(\<And>* x\<in> S. x \<mapsto>o -) \<and>* R> s
   \<Longrightarrow> <(\<And>* x \<in> S. x \<mapsto>o Untyped) \<and>* R> (detype S s)"
proof (induct arbitrary: R rule: finite_induct)
  case empty
  show ?case using empty by (simp add: detype_def)
next
  case (insert a A)
  show ?case using insert.hyps(1-2) insert.prems
    apply (subst detype_insert)
    apply (simp add: )
    apply (subst sep_conj_assoc)
    apply (rule detype_one_wp)
    apply (sep_select 2)
    apply (rule insert.hyps(3))
    apply sep_solve
  done
qed

lemma detype_set_wp:
  "finite S \<Longrightarrow>
   \<lbrace><(\<And>* x\<in> S. x \<mapsto>o -) \<and>* R>\<rbrace>
    modify (detype S)
   \<lbrace>\<lambda>_. <(\<And>* x \<in> S. x \<mapsto>o Untyped) \<and>* R>\<rbrace>"
  apply (clarsimp simp: modify_def)
  apply wp
  apply (rule detype_set_sep_helper)
   apply simp+
  done

lemma invoke_untyped_preempt:
  "finite obj_range \<Longrightarrow>
  \<lbrace>cdl.lift (slot \<mapsto>c UntypedCap dev obj_range free_range \<and>*
         sep_map_set_conj sep_any_map_o obj_range \<and>* Q)\<rbrace>
    invoke_untyped (Retype slot nt (unat ts) dests has_kids n)
   -, \<lbrace>\<lambda>x s. \<exists>free_range. cdl.lift
         (slot \<mapsto>c UntypedCap dev obj_range free_range \<and>*
         sep_map_set_conj sep_any_map_o obj_range \<and>* Q) s\<rbrace>"
  apply (simp add: invoke_untyped_def)
  apply (wp unlessE_wp)
   apply (simp add: reset_untyped_cap_def whenE_liftE | wp whenE_wp)+
      apply (rule_tac P = "\<exists>a. cap = UntypedCap dev obj_range a" in hoare_gen_asmEx)
      apply (rule hoare_strengthen_postE[where E'=E and E=E for E])
        apply (rule mapME_x_inv_wp[where P = P and E = "\<lambda>r. P" for P])
        apply wp
         apply simp
         apply (wp hoare_vcg_ex_lift)
          apply (rule hoare_post_imp[OF _ set_cap_wp])
          apply sep_solve
         apply clarsimp
        apply (rule exI)
        apply sep_solve
       apply simp
      apply simp
    apply wp+
  apply clarsimp
  apply (frule opt_cap_sep_imp)
  apply (clarsimp dest!: reset_cap_asid_untyped_cap_eqD)
  apply (cut_tac S = obj_range in detype_set_wp[unfolded bind_def valid_def simpler_modify_def])
   apply simp
  apply (drule_tac x = s in spec)
  apply (erule impE)
   apply clarsimp
   apply sep_solve
  apply clarsimp
  apply (rule exI)
  apply sep_cancel+
  apply (erule sep_map_set_conj_impl)
   apply sep_solve
  apply simp
  done

lemma set_parent_cdt_parent:
  "\<lbrace>\<lambda>s. cdl_cdt s slot = Some parent\<rbrace> set_parent param_a param_b \<lbrace>\<lambda>_ s. cdl_cdt s slot = Some parent\<rbrace>"
  apply (simp add: set_parent_def)
  apply wp
  apply (clarsimp simp add: )
  done

lemma set_parent_cdl_parent:
   "\<lbrace>\<lambda>s. cdl_cdt s slot = Some parent\<rbrace>
     set_parent slot' parent'
   \<lbrace>\<lambda>_ s. cdl_cdt s slot = Some parent\<rbrace>"
   apply (simp add: set_parent_def)
   apply wp
   apply clarsimp
   done

crunch reset_untyped_cap
  for cdl_parent[wp]: "\<lambda>s. cdl_cdt s slot = Some parent"
   (wp: assert_inv crunch_wps mapME_x_inv_wp
    simp: crunch_simps detype_def)

crunch insert_cap_child, corrupt_ipc_buffer,
          corrupt_tcb_intent, update_thread, derive_cap, insert_cap_sibling
  for cdl_parent[wp]: "\<lambda>s. cdl_cdt s slot = Some parent"
   (wp: crunch_wps set_parent_cdl_parent simp: crunch_simps corrupt_intents_def)

lemma transfer_caps_loop_cdl_parent:
   "\<lbrace>\<lambda>s. cdl_cdt s slot = Some parent\<rbrace>
     transfer_caps_loop ep rcvr caps dest
   \<lbrace>\<lambda>_ s. cdl_cdt s slot = Some parent\<rbrace>"
   apply (induct caps arbitrary: dest; clarsimp split del: if_split)
   apply (rule hoare_pre)
    apply (wp crunch_wps | assumption
      | simp add: crunch_simps split del: if_split)+
   done

lemmas reset_untyped_cap_cdl2[wp] = reset_untyped_cap_cdl_parent[THEN valid_validE_E]

crunch inject_reply_cap
  for cdt_parent: "\<lambda>s. cdl_cdt s slot = Some parent"
  (simp: crunch_simps unless_def wp: crunch_wps)

lemma set_object_no_pending:
  "\<lbrace>no_pending and K(\<forall>cap. object_slots x tcb_pending_op_slot = Some cap \<longrightarrow> \<not> is_pending_cap cap)\<rbrace> set_object a x \<lbrace>\<lambda>rv. no_pending\<rbrace>"
  apply (clarsimp simp: set_object_def simpler_modify_def valid_def no_pending_def)
  apply (drule_tac x=oid in spec)
  apply (fastforce simp: opt_cap_def slots_of_def ran_def
                   split: option.split_asm if_splits)
  done

lemma object_slots_upd_intent[simp]:
  "object_slots (Tcb (x\<lparr>cdl_tcb_intent := intent\<rparr>)) = object_slots (Tcb x)"
  by (clarsimp simp: object_slots_def)

lemma no_pending_cong[cong]:
  "cdl_objects s = cdl_objects b \<Longrightarrow> no_pending s = no_pending b"
  by (clarsimp simp: no_pending_def opt_cap_def slots_of_def)

lemma default_cap_not_pending[simp]:
  "\<not> is_pending_cap (default_cap a b c d)"
  by (simp add: default_cap_def is_pending_cap_def split: cdl_object_type.splits)

lemma set_cap_no_pending[wp]:
  "snd slot = tcb_pending_op_slot \<longrightarrow> \<not> is_pending_cap cap \<Longrightarrow>
  \<lbrace>no_pending\<rbrace> set_cap slot cap \<lbrace>\<lambda>rv s. no_pending s\<rbrace>"
  apply (simp add: set_cap_def)
  apply (cases slot, simp)
  apply (wp set_object_no_pending | wpc | simp add: no_pending_def)+
  apply (drule_tac x = a in spec)
  apply (rule conjI)
    apply (clarsimp simp: tcb_pending_op_slot_def tcb_ipcbuffer_slot_def)
  apply clarsimp
  apply (intro conjI impI allI)
            apply (clarsimp simp: opt_cap_def slots_of_def)+
            apply (case_tac y, (fastforce simp: object_slots_def update_slots_def)+)
           apply (clarsimp simp: opt_cap_def slots_of_def)+
  done

crunch create_cap
  for no_pending[wp]: no_pending

lemma default_object_no_pending_cap:
  "\<lbrakk> default_object b c d = Some x2; object_slots x2 tcb_pending_op_slot = Some cap\<rbrakk>
    \<Longrightarrow> \<not> is_pending_cap cap"
  apply (case_tac b)
  apply (clarsimp simp: default_object_def object_slots_def default_tcb_def is_pending_cap_def
                        empty_cnode_def empty_cap_map_def empty_irq_node_def
                 split: if_split_asm)+
  done

lemma create_objects_no_pending[wp]:
  "\<lbrace>no_pending\<rbrace> create_objects a (default_object b c d) \<lbrace>\<lambda>rv. no_pending\<rbrace>"
  apply (simp add: create_objects_def, wp)
  apply (clarsimp simp: no_pending_def)
  apply (drule_tac x = oid in spec)
  apply (clarsimp simp: opt_cap_def default_object_no_pending_cap slots_of_def
                 split: if_splits option.split_asm)
  done


crunch retype_region
  for no_pending[wp]: "no_pending"
  (wp: crunch_wps ignore: create_objects)

lemma detype_no_pending:
  "no_pending s \<Longrightarrow> no_pending (detype S s)"
  apply (clarsimp simp: detype_def no_pending_def)
  apply (drule_tac x = oid in spec)
  apply (clarsimp simp: opt_cap_def slots_of_def object_slots_def split: if_splits option.splits)
  done

lemma is_pending_cap_set_available_range[simp]:
  "is_pending_cap (set_available_range cap xa) = is_pending_cap cap"
  by (case_tac cap, simp_all add: is_pending_cap_def cap_type_def)

lemma reset_untyped_cap_no_pending[wp]:
  "\<lbrace>no_pending \<rbrace> reset_untyped_cap cref \<lbrace>\<lambda>rv. no_pending\<rbrace>"
  apply (simp add: reset_untyped_cap_def)
  apply (wp whenE_wp)
      apply (rule_tac P = "snd cref = tcb_pending_op_slot \<longrightarrow> \<not> is_pending_cap cap" in hoare_gen_asmEx)
      apply (wp mapME_x_inv_wp | simp)+
  apply (clarsimp simp: detype_no_pending)
  apply (cases cref, clarsimp simp: no_pending_def)
  done

lemma set_cap_opt_cap:
  "\<lbrace>\<lambda>s. P (Some cap)\<rbrace>
  set_cap cref cap
  \<lbrace>\<lambda>rv s. P (opt_cap cref s)\<rbrace>"
  apply (cases cref)
  apply (simp add: set_cap_def gets_the_def gets_def get_def assert_opt_def bind_assoc)
  apply (clarsimp simp: bind_def return_def valid_def split:option.splits)
  apply (clarsimp simp: fail_def assert_def return_def select_def bind_def
                 split: cdl_object.split_asm)
           apply (simp_all add: set_object_def simpler_modify_def opt_cap_def
                                 slots_of_def has_slots_def update_slots_def
                         split: cdl_object.split_asm)+
       apply (clarsimp simp: select_def return_def bind_def
                             object_slots_def update_slots_def
                      split: if_splits)+
  done

lemma set_cap_opt_cap_sep_imp:
  assumes asid:
    "\<And>c c'. reset_cap_asid c = reset_cap_asid c' \<Longrightarrow> P (Some c) = P (Some c')"
  shows
    "\<lbrace>\<lambda>s. cdl.lift (ptr \<mapsto>c c \<and>* cref \<mapsto>c - \<and>* sep_true) s \<and> P (Some c)\<rbrace>
    set_cap cref cap
    \<lbrace>\<lambda>rv s. P (opt_cap ptr s)\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (rule hoare_pre)
   apply (rule hoare_post_imp[OF _ set_cap_wp])
   prefer 2
   apply clarsimp
   apply sep_solve
  apply clarsimp
  apply (sep_select_asm 2)
  apply (drule opt_cap_sep_imp)+
  apply (clarsimp dest!: asid)
  done

lemma set_cap_no_pending_asm_in_pre:
  "\<lbrace>no_pending and K (snd slot = tcb_pending_op_slot \<longrightarrow> \<not> is_pending_cap cap)\<rbrace>
    set_cap slot cap \<lbrace>\<lambda>rv s. no_pending s\<rbrace>"
  by (rule hoare_gen_asm, wp)

lemma reset_untyped_cap_not_pending_cap[wp]:
  "\<lbrace>\<lambda>s. \<not> is_pending_cap (the (opt_cap cref s))\<rbrace>
  reset_untyped_cap cref
  \<lbrace>\<lambda>rv s.  (\<exists>cap. opt_cap cref s = Some cap) \<longrightarrow> \<not> is_pending_cap (the (opt_cap cref s))\<rbrace>"
  apply (simp add: reset_untyped_cap_def)
  apply (wp whenE_wp)
     apply (rule_tac P = " \<not> is_pending_cap cap" in hoare_gen_asmEx)
     apply (wp mapME_x_inv_wp set_cap_opt_cap)+
     apply simp
    apply wp+
  apply (clarsimp simp: detype_no_pending)
  apply (cases cref)
  apply (clarsimp simp: detype_def opt_cap_def slots_of_def object_slots_def
                 split: option.split_asm if_splits)
  done

lemma invoke_untyped_no_pending[wp]:
  "\<lbrace>no_pending and (\<lambda>s. \<not> is_pending_cap (the (opt_cap ref s)))\<rbrace>
  invoke_untyped (Retype ref a b c d e)
  \<lbrace>\<lambda>rv. no_pending\<rbrace>"
  apply (simp add: invoke_untyped_def create_cap_def update_available_range_def)
  apply (wpsimp wp: mapM_x_wp' set_cap_no_pending_asm_in_pre get_cap_wp
                simp: update_available_range_def update_range_def)
   apply (rule_tac Q' = "\<lambda>r s. no_pending s \<and> ((\<exists>y. opt_cap ref s = Some y) \<longrightarrow>
                        \<not> is_pending_cap (the (opt_cap ref s)))" in hoare_strengthen_postE_R)
    apply (wp reset_untyped_cap_no_pending)
   apply auto
  done

lemma is_pending_cap_reset_cap_asid:
  "reset_cap_asid c = reset_cap_asid c'
  \<Longrightarrow> is_pending_cap c = is_pending_cap c'"
  apply (case_tac c')
  apply (clarsimp simp: is_pending_cap_def dest!:reset_cap_asid_simps2)+
  done

lemmas
  is_pending_cap_simps[simp] = is_pending_cap_def[split_simps cdl_cap.split]

lemma map_nonempty_split: "xs \<noteq> [] \<Longrightarrow> map f xs = f (hd xs)# map f (tl xs)"
  by (induct xs; clarsimp)

lemma zip_generate_range_single: "\<lbrakk>type \<noteq> UntypedType; n \<noteq> 0\<rbrakk>
   \<Longrightarrow> zip [x] (generate_range start type sz n) = [(x, {start})]"
  apply (simp add: generate_range_def comp_def)
  apply (case_tac " [0..<n] = []")
   apply (simp add: map_nonempty_split)+
  done

lemma create_cap_touch_wp:
  "\<lbrace>< (fst xs) \<mapsto>c - \<and>* R >\<rbrace>
  create_cap new_type sz parent_slot dev xs
  \<lbrace>\<lambda>_. < (fst xs) \<mapsto>c - \<and>* R >\<rbrace>"
  apply (simp add: create_cap_def)
  apply wpc
   apply (wp set_parent_wp)
     apply (wp sep_wp: set_cap_wp)+
  apply clarsimp
  apply sep_solve
  done

lemma sep_map_list_conjD: "\<lbrakk>(\<And>* map P xs) s; \<And>v s. \<lbrakk>v \<in> set xs; P v s\<rbrakk> \<Longrightarrow> P' v s\<rbrakk>
   \<Longrightarrow> (\<And>* map P' xs) s"
  apply (induction xs arbitrary: s; simp)
  apply (erule sep_conj_impl; simp)
  done

lemma create_objects_touch_wp:
  notes set_map[simp del]
  shows
  "\<lbrace> K (obj_refs = map (\<lambda>x. {x}) (map pick obj_refs) \<and> distinct (map pick obj_refs) \<and> obj \<noteq> None)
     and <(\<And>* ptr\<in>set (map pick obj_refs). ptr \<mapsto>o -) \<and>* P > \<rbrace>
   create_objects obj_refs (obj)
   \<lbrace>\<lambda>r s. <(\<And>* ptr\<in>set (map pick obj_refs). ptr \<mapsto>o -) \<and>* P > s \<rbrace>"
  apply (rule hoare_name_pre_state, clarsimp)
  apply (subst create_objects_mapM_x'[where ids' = "map pick obj_refs"])
   apply simp
  apply (rule hoare_pre)
   apply (rule hoare_strengthen_post)
    apply (rule cdl.mapM_x_sep')
    apply (rule create_one_wp)
   apply (subst sep_list_conj_sep_map_set_conj[symmetric])
    apply (simp add:distinct_map)
   apply simp
   apply (clarsimp simp: set_map[symmetric])
   apply (subst(asm) sep_list_conj_sep_map_set_conj[symmetric])
    apply (simp add:distinct_map)
   apply (simp add:set_map)
   apply sep_cancel
  apply (clarsimp simp: comp_def)
  apply (subst (asm) sep_list_conj_sep_map_set_conj[symmetric])
   apply (clarsimp)
  apply (subst (asm) map_map)
  apply (clarsimp simp: comp_def)
  apply (sep_cancel)+
  apply (erule sep_map_list_conjD)
  apply (sep_solve)
  done

lemma retype_region_touch_wp: "\<lbrace>\<lambda>s. obj_refs = map ((\<lambda>x. {x}) \<circ> pick) obj_refs \<and>
  distinct (map pick obj_refs) \<and> target_type \<noteq> UntypedType \<and> <(\<And>* ptr\<in>set (map pick obj_refs). ptr \<mapsto>o -) \<and>* P> s\<rbrace>
   retype_region target_bits target_type obj_refs
  \<lbrace>\<lambda>r. <(\<And>* ptr\<in>set (map pick obj_refs). ptr \<mapsto>o -) \<and>* P>\<rbrace>"
  apply (clarsimp simp: retype_region_def, wp)
    apply(rule create_objects_touch_wp[simplified, THEN sep_lift_generic, simplified])
   apply (wp)
  apply (clarsimp)
  apply (intro conjI)
   apply (cases target_type; clarsimp simp: default_object_def)
  apply (sep_solve)
  done

lemma update_available_range_touch_wp: "\<lbrace>\<lambda>s. <cap_ref \<mapsto>c - \<and>* P> s\<rbrace>
  update_available_range ptr idx cap_ref cap
  \<lbrace>\<lambda>r s. <cap_ref \<mapsto>c - \<and>* P> s\<rbrace>"
  apply (clarsimp simp: update_available_range_def Let_unfold update_range_def)
  apply (intro conjI impI; wp sep_wp: set_cap_wp, sep_solve)
  done

lemma invoke_untyped_touch_wp:
  "invocation = (Retype uref nt (unat ts) [dest_slot] has_kids (Suc 0)) \<Longrightarrow>
   \<lbrace>\<lambda>s. (\<not> has_kids \<longrightarrow> obj_range = free_range) \<and> nt \<noteq> UntypedType \<and>
    < dest_slot \<mapsto>c NullCap \<and>* uref \<mapsto>c UntypedCap dev obj_range free_range \<and>*
    (if has_kids then (alignUp (Min (get_range ((\<noteq>) {}) free_range obj_range)) (obj_bits_cdl nt (unat ts))) else  (Min (get_range ((\<noteq>) {}) free_range obj_range))) \<mapsto>o - \<and>*  R> s \<rbrace>
    invoke_untyped invocation
   \<lbrace>\<lambda>rv s. <uref \<mapsto>c - \<and>* dest_slot \<mapsto>c - \<and>*
    (if has_kids then (alignUp (Min (get_range ((\<noteq>) {}) free_range obj_range)) (obj_bits_cdl nt (unat ts))) else  (Min (get_range ((\<noteq>) {}) free_range obj_range))) \<mapsto>o - \<and>* R> s\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp:  invoke_untyped_def)
  apply (intro conjI impI; clarsimp)
   apply wp
       apply (subst zip_generate_range_single, clarsimp, clarsimp)
       apply (subst mapM_x_singleton)
       apply (wp sep_wp: create_cap_touch_wp)
      apply (wp retype_region_touch_wp[simplified, THEN sep_lift_generic, simplified])
     apply (wp sep_wp: update_available_range_touch_wp)
    apply (clarsimp)
    apply (rule get_cap_rv[where cap="UntypedCap dev obj_range free_range" and R=sep_true])
   apply (clarsimp)
   apply (intro conjI)
    apply (sep_solve)
   apply (sep_cancel)+
   apply (clarsimp simp: generate_range_def)
   apply (sep_solve)
  apply wp
       apply (subst zip_generate_range_single, clarsimp, clarsimp)
       apply (subst mapM_x_singleton)
       apply (wp sep_wp: create_cap_touch_wp)
      apply (wp retype_region_touch_wp[simplified, THEN sep_lift_generic, simplified])
     apply (wp sep_wp: update_available_range_touch_wp)
    apply (clarsimp)
    apply (rule get_cap_rv[where cap="UntypedCap dev obj_range free_range" and R=sep_true])
   apply (wp reset_untyped_cap_wp_trivial[THEN sep_lift_generic])
  apply (clarsimp, intro conjI impI)
       apply (sep_solve)
      apply (clarsimp)
     apply (sep_solve)
    apply (clarsimp)
   apply (sep_cancel)+
   apply (intro conjI; clarsimp simp: generate_range_def)
   apply (sep_solve)
  apply (clarsimp)
  done

lemma invoke_untyped_touch_wp_R:
  "invocation = (Retype uref nt (unat ts) [dest_slot] has_kids (Suc 0)) \<Longrightarrow>
   \<lbrace>\<lambda>s. (\<not> has_kids \<longrightarrow> obj_range = free_range) \<and> nt \<noteq> UntypedType \<and>
    < dest_slot \<mapsto>c NullCap \<and>* uref \<mapsto>c UntypedCap dev obj_range free_range \<and>*
    (if has_kids then (alignUp (Min (get_range ((\<noteq>) {}) free_range obj_range)) (obj_bits_cdl nt (unat ts))) else  (Min (get_range ((\<noteq>) {}) free_range obj_range))) \<mapsto>o - \<and>*  R> s \<rbrace>
    invoke_untyped invocation
   \<lbrace>\<lambda>rv s. <uref \<mapsto>c - \<and>* dest_slot \<mapsto>c - \<and>*
    (if has_kids then (alignUp (Min (get_range ((\<noteq>) {}) free_range obj_range)) (obj_bits_cdl nt (unat ts))) else  (Min (get_range ((\<noteq>) {}) free_range obj_range))) \<mapsto>o - \<and>* R> s\<rbrace>, -"
  apply (simp only:)
  apply (rule valid_validE_R)
  apply (rule hoare_chain[OF invoke_untyped_touch_wp])
    apply simp
   apply assumption+
  done

abbreviation (input) "retype_with_kids uinv
  \<equiv> (case uinv of (InvokeUntyped (Retype uref nt ts dest has_kids n)) \<Rightarrow> has_kids)"

lemma seL4_Untyped_Retype_inc_no_preempt:
  "\<lbrakk>cap_object root_cnode_cap = root_cnode;
   ucptr_slot = offset ucptr root_size;
   is_cnode_cap root_cnode_cap;
   ncptr_slot = offset ncptr root_size;
   unat ncptr_slot_nat = ncptr_slot;
   one_lvl_lookup root_cnode_cap 32 root_size;
   guard_equal root_cnode_cap ucptr 32;
   guard_equal root_cnode_cap croot 32\<rbrakk>
  \<Longrightarrow> \<lbrace> K (nt\<noteq> UntypedType \<and> default_object  nt (unat ts) minBound = Some obj) and
    \<guillemotleft>root_tcb_id \<mapsto>f (Tcb tcb)
  \<and>* (root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap
  \<and>* (cap_object root_cnode_cap \<mapsto>f CNode (empty_cnode root_size))
  \<and>* (root_cnode, ucptr_slot) \<mapsto>c UntypedCap dev obj_range free_range
  \<and>* (root_cnode, ncptr_slot ) \<mapsto>c NullCap
  \<and>* (\<And>* ptr\<in>tot_free_range. ptr \<mapsto>o Untyped)
  \<and>* (root_tcb_id, tcb_cspace_slot) \<mapsto>c root_cnode_cap
  \<and>* (cap_object root_cnode_cap, offset croot root_size) \<mapsto>c root_cnode_cap
  \<and>* aligned_ptr \<mapsto>o -
  \<and>* P\<guillemotright>
    and (\<lambda>s. if has_children (root_cnode,ucptr_slot) (kernel_state s)
       then  aligned_ptr = alignUp (Min (get_range ((\<noteq>) {}) free_range obj_range)) (obj_bits_cdl nt (unat ts))
       else obj_range = free_range \<and>  aligned_ptr = Min (get_range ((\<noteq>) {}) free_range obj_range ))
    and (\<lambda>s. cdl_cdt (kernel_state s) child = Some parent)
  \<rbrace>
  seL4_Untyped_Retype ucptr nt ts croot node_index 0 ncptr_slot_nat 1
  \<lbrace>\<lambda>rv s. cdl_cdt (kernel_state s) child = Some parent\<rbrace>"
  apply (simp add:seL4_Untyped_Retype_def sep_state_projection2_def)
  apply (rule hoare_name_pre_state)
  apply (rule hoare_pre)
   apply (rule do_kernel_op_pull_back)
   apply (rule_tac ?Pd2.0="\<lambda>s'. has_children (root_cnode,ucptr_slot) ( s') = has_children (root_cnode,ucptr_slot) (kernel_state s) \<and> Q s'" for Q
          in call_kernel_with_intent_allow_error_helper[where check= False and tcb = tcb and Q = Q and Perror = Q for Q,simplified])
               apply fastforce
              apply (wp)+
         apply (rule_tac P = "\<exists>has_kids. iv = InvokeUntyped (Retype (root_cnode,ucptr_slot) nt (unat ts)
               [(root_cnode, ncptr_slot)]
               has_kids 1)"
           in hoare_gen_asmEx)
         apply clarsimp
         apply (rule hoare_vcg_conj_elimE[where P = P and P' = P for P,simplified,rotated])
          apply wp
          apply (rule hoare_strengthen_postE_R[OF hoare_vcg_conj_liftE_R])
            apply (rule valid_validE_R)
            apply (rule invoke_untyped_cdt_inc)
           apply (rule invoke_untyped_touch_wp_R [where
                        uref = "(cap_object root_cnode_cap, offset ucptr root_size)"
                    and dest_slot = "(cap_object root_cnode_cap, offset ncptr root_size)"
                    and free_range = free_range and nt=nt and ts="ts"
                    and obj_range = obj_range, simplified sep_wp_simp, THEN sep_lift_generic_R])
           apply clarsimp
           apply (rule_tac s="retype_with_kids (InvokeUntyped (Retype _ _ _ _ has_kids _))" in trans, simp, rule refl)
          apply clarsimp
          apply (rule conjI)
           apply (sep_erule refl_imp, simp)
          apply fastforce
         apply (rule hoare_pre)
          apply (rule invoke_untyped_exception[where  free_range = free_range and obj_range = obj_range], simp)
         apply (clarsimp)
         apply (sep_solve)
        apply (wp hoare_vcg_conj_lift)
         apply (wp hoare_strengthen_post[OF set_cap_wp])
         apply (sep_schem)
        apply wp[1]
       apply (rule_tac P ="nt \<noteq> UntypedType \<and> c = UntypedCap dev obj_range free_range \<and> cs = [(root_cnode_cap,(root_cnode,offset croot root_size))]"
        in hoare_gen_asmEx)
       apply simp
       apply (rule decode_untyped_invocation_rvu)
       apply simp
      apply (simp add:lookup_extra_caps_def mapME_singleton)
      apply (rule wp_no_exception_seq)
       apply wp[1]
      apply (rule lookup_cap_and_slot_rvu[where r = root_size and  cap' = "root_cnode_cap"])
     apply clarsimp
     apply (rule hoare_weaken_preE)
      apply (rule lookup_cap_and_slot_rvu[where r = root_size and cap' = "UntypedCap dev obj_range free_range"])[1]
     apply (force)
    apply (wp hoare_vcg_ball_lift
              update_thread_intent_update
              hoare_vcg_imp_lift hoare_vcg_ex_lift hoare_vcg_all_lift
              is_cnode_cap_guard_equal update_thread_intent_update)
   apply clarsimp+
   apply (case_tac "has_children (cap_object root_cnode_cap, offset ucptr root_size) sa", clarsimp)
    apply (drule mp, force)
    apply (clarsimp)
    apply (sep_schem)
   apply (drule mp, force)
   apply (clarsimp)
   apply (sep_schem)
  apply (clarsimp)
  apply (intro conjI impI)
         apply (erule conjE)+
         apply clarsimp
         apply (sep_cancel)
         apply (sep_cancel)
         apply (sep_cancel)
         apply (sep_cancel)
         apply (sep_cancel)
         apply (sep_cancel)
         apply (sep_erule refl_imp)
         apply (rule TrueI)
        apply (sep_solve)+
       apply (erule conjE)+
       apply (fastforce)
      apply (subst disj_imp, intro impI conjI)
         apply (clarsimp)
        apply (clarsimp, sep_solve)
       apply (clarsimp)
       apply (clarsimp simp: user_pointer_at_def Let_def ep_related_cap_def
                                       word_bits_def sep_conj_assoc
                                dest!: reset_cap_asid_simps2 reset_cap_asid_cnode_cap | sep_solve)+
  done
end
