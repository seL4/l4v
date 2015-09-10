(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
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

crunch inv[wp]: generate_object_ids P
(wp:crunch_wps select_wp)

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

(* This is not true, need to change the capdl_spec to make the selected list distinct *)
lemma generate_object_ids_rv:
  "\<lbrace>K (target_type \<noteq> UntypedType) \<rbrace>
  generate_object_ids n target_type obj_range
  \<lbrace>\<lambda>r s.  r = map (\<lambda>x. {x}) (map pick r) \<and> length r = n \<and> set (map pick r) \<subseteq> obj_range
  \<and> distinct (map pick r) \<rbrace>"
  apply (clarsimp simp:generate_object_ids_def)
  apply (wp select_wp)
  apply clarsimp
  apply (simp add: distinct_map)
  apply (intro conjI)
   apply (clarsimp simp:Fun.comp_def)
   apply (rule subsetD[rotated,OF nonempty_pick_in])
    apply fastforce
   apply fastforce
  apply (clarsimp simp:Fun.comp_def inj_on_def)
  apply (drule_tac x = xa in bspec)
   apply simp
  apply (frule_tac x = xa in bspec,simp)
  apply (drule_tac x = y in bspec,simp)+
  apply (rule ccontr)
  apply clarsimp
  apply (drule nonempty_pick_in)+
  apply clarsimp
  apply blast
  done

lemma retype_region_wp:
  "\<lbrace> K (default_object target_type target_bits minBound = Some obj
     \<and> target_type \<noteq> UntypedType \<and> distinct (map pick obj_refs)
     \<and> obj_refs = map (\<lambda>x. {x}) (map pick obj_refs)
     \<and> set (map pick obj_refs) \<subseteq> obj_range )
     and (\<lambda>s. cdl_current_domain s = minBound)
     and <(\<And>* ptr\<in>obj_range. ptr \<mapsto>o Untyped) \<and>* P > \<rbrace>
  retype_region target_bits target_type obj_refs
  \<lbrace>\<lambda>r s. <(\<And>* ptr\<in>set (map pick obj_refs). ptr \<mapsto>o obj)
  \<and>* (\<And>* ptr\<in>obj_range - set (map pick obj_refs). ptr \<mapsto>o Untyped) \<and>* P > s\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (rule hoare_pre)
  apply (clarsimp simp:retype_region_def)
   apply wp
    apply (rule_tac P="current_domain = minBound" in hoare_gen_asm)
    apply (wp create_objects_wp | simp)+
  apply (subst sep_conj_assoc[symmetric])
  apply (subst sep.setprod.union_disjoint [symmetric])
   apply simp+
  apply (simp add:Un_absorb1)
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

lemma update_available_range_wp:
  "\<lbrace> (\<lambda>s. cdl_current_domain s = minBound)
     and <uref \<mapsto>c - \<and>* (\<And>* ptr\<in>tot_free_range. ptr \<mapsto>o Untyped) \<and>* P> \<rbrace>
  update_available_range pick_range (map pick new_obj_refs) uref (UntypedCap obj_range free_range)
  \<lbrace>\<lambda>r s. cdl_current_domain s = minBound \<and>
  (\<exists>nfr\<subseteq>pick_range - set (map pick new_obj_refs).
  <(\<And>* ptr\<in>tot_free_range. ptr \<mapsto>o Untyped) \<and>* uref \<mapsto>c UntypedCap obj_range nfr \<and>* P>
  s)\<rbrace>"
  apply wp
   apply (simp add:update_available_range_def)
   apply (wp)
    apply (rule hoare_gen_asm)
    apply (rule hoare_strengthen_post[OF set_cap_wp])
    apply (rule_tac x = new_range in exI)
    apply (intro conjI,assumption+)
    apply (sep_select 2,assumption)
   apply (wp select_wp)
   apply clarsimp+
  done

lemma reset_cap_asid_untyped_cap_eqD:
  "reset_cap_asid c = UntypedCap a b
  \<Longrightarrow> c = UntypedCap a b"
  by (simp add:reset_cap_asid_def split:cdl_cap.splits)

lemma dummy_detype_if_untyped:
  "\<lbrakk>finite obj_range ;<(\<And>* ptr\<in>obj_range. ptr \<mapsto>o Untyped) \<and>* P > s\<rbrakk>
  \<Longrightarrow> (detype obj_range s) = s"
  apply (case_tac s,clarsimp simp:detype_def sep_set_conj_def)
  apply (rule ext)
  apply (clarsimp simp:sep_state_projection_def sep_conj_def)
  apply (subst (asm) sep.setprod.remove)
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

lemma invoke_untyped_wp:
  "\<lbrace> K (default_object nt ts minBound = Some obj \<and> nt \<noteq> UntypedType
     \<and> length slots = n \<and> free_range \<subseteq> tot_free_range
     \<and> (\<not> has_kids \<longrightarrow> free_range = obj_range) \<and> finite tot_free_range)
     and (\<lambda>s. cdl_current_domain s = minBound)
     and < \<And>* map (\<lambda>dest_slot. dest_slot \<mapsto>c NullCap) slots
    \<and>*(\<And>* ptr\<in>tot_free_range. ptr \<mapsto>o Untyped)
    \<and>* uref \<mapsto>c UntypedCap obj_range free_range
    \<and>* P > \<rbrace>
  invoke_untyped (Retype uref nt ts slots has_kids n)
  \<lbrace>\<lambda>_ s. (\<exists>nlist free_range'.
  length nlist = n \<and> distinct nlist \<and> set nlist \<subseteq> free_range
  \<and> free_range' \<subseteq> free_range - (set nlist) \<and>
  < \<And>* map (\<lambda>(dest_slot, obj_refs). dest_slot \<mapsto>c (default_cap nt obj_refs ts)) (zip slots (map (\<lambda>x. {x}) nlist))
  \<and>* (\<And>* ptr\<in>set nlist. ptr \<mapsto>o obj)
  \<and>* (\<And>* ptr\<in>tot_free_range - set nlist. ptr \<mapsto>o Untyped)
  \<and>* uref \<mapsto>c UntypedCap obj_range free_range'
  \<and>* P > s) \<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp:invoke_untyped_def unless_def)
  apply (rule hoare_pre)
   apply wp
        apply (rule hoare_vcg_ex_lift)
        apply (rule_tac P = "new_obj_refs = map (\<lambda>x. {x}) nlist" in hoare_gen_asm)
        apply (simp add:create_cap_def split_def)
        apply (wp hoare_vcg_ex_lift)
        apply (rule cdl.mapM_x_sep')
        apply (wp set_parent_wp set_cap_wp)
        apply fastforce
       apply (rule_tac P = "untyped_cap = UntypedCap obj_range free_range
         \<and> length new_obj_refs = length slots
         \<and> distinct (map pick new_obj_refs)
         \<and> pick ` set new_obj_refs \<subseteq> free_range
         \<and> new_obj_refs = map ((\<lambda>x. {x}) \<circ> pick) new_obj_refs" in hoare_gen_asm)
       apply (wp hoare_vcg_ex_lift)
        apply (rule_tac P = "x = map pick new_obj_refs" in hoare_gen_asm)
        apply simp
        apply (rule_tac
          hoare_strengthen_post[OF retype_region_wp[where obj_range = tot_free_range]])
        apply (simp add:map_zip_first_simp)
        apply (elim conjE)
        apply (sep_select 3,sep_select 3)
        apply assumption
       apply wp
      apply (rule hoare_vcg_conj_lift)
       apply (rule hoare_vcg_ex_lift)
       apply (wp hoare_vcg_conj_lift)
        apply (rule_tac P = "x = map pick new_obj_refs
          \<and> (untyped_cap = UntypedCap obj_range free_range)
          \<and>  distinct (map pick new_obj_refs) \<and>
           new_obj_refs = map ((\<lambda>x. {x}) \<circ> pick) new_obj_refs \<and>
           pick ` set new_obj_refs \<subseteq> tot_free_range" in hoare_gen_asm)
        apply (simp del:set_map split del:split_if)
        apply (rule hoare_strengthen_post[OF update_available_range_wp])
        apply clarsimp
        apply (rule_tac x = nfr in exI)
        apply (rule conjI)
         apply (clarsimp split:if_splits)
        apply (sep_select 3,sep_select 2,simp)
       apply (wp|simp split del:split_if)+
     apply (rule_tac P = "untyped_cap = UntypedCap obj_range free_range"
       in hoare_gen_asm)
     apply (clarsimp simp:conj_comms split del: split_if)
     apply (simp add: conj_assoc[symmetric] del:conj_assoc split del: split_if)+
     apply (rule hoare_vcg_conj_lift)
      apply wp
      apply (rule hoare_strengthen_post[OF generate_object_ids_rv])
      apply (clarsimp simp:Fun.comp_def split:if_splits)
       apply (drule(1) subset_trans[rotated],fastforce)+
     apply wp
  apply (sep_select_asm 3)
  apply (frule opt_cap_sep_imp)
  apply (clarsimp dest!:reset_cap_asid_untyped_cap_eqD)
  apply (rule conjI, clarsimp)
   apply (rule subst[OF dummy_detype_if_untyped[symmetric]])
     apply simp
    apply (subgoal_tac "tot_free_range = obj_range \<union> (tot_free_range - obj_range)")
     apply simp
     apply (subst (asm) sep.setprod.subset_diff)
       apply simp+
     apply (sep_select_asm 2)
     apply (simp add:sep_conj_assoc)
     apply sep_solve
    apply blast
   apply clarsimp+
   apply sep_cancel+
   apply (erule sep_list_conj_impl[rotated])
   apply (rule list_all2I)
    apply (clarsimp simp add: zip_map1 zip_map2 set_zip_same sep_any_map_c_imp)+
  apply sep_cancel+
  apply (erule sep_list_conj_impl[rotated])
  apply (rule list_all2I)
   apply (clarsimp simp add: zip_map1 zip_map2 set_zip_same sep_any_map_c_imp)+
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
  decode_invocation (UntypedCap tot_range free_range) ref [(cnode_cap,cnode_ref)]
  (UntypedIntent (UntypedRetypeIntent nt ts node_index 0 node_offset 1))
  \<lbrace>\<lambda>r. Q r\<rbrace>, \<lbrace>\<lambda>r. R\<rbrace>"
  apply (simp add:decode_invocation_def
    get_untyped_intent_def throw_opt_def
    get_index_def throw_on_none_def
    decode_untyped_invocation_def mapME_x_singleton)
  apply (rule hoare_pre)
  apply (wp alternativeE_wp unlessE_wp
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
  "\<lbrace>\<top>\<rbrace> create_cap new_type sz uref slot \<lbrace>\<lambda>r. has_children uref\<rbrace>"
  apply (clarsimp simp :create_cap_def split_def)
  apply wp
  apply simp
  done

abbreviation (input) "retype_with_kids uinv
  \<equiv> (case uinv of (InvokeUntyped (Retype uref nt ts dest has_kids n)) \<Rightarrow> has_kids)"


crunch cdt[wp]: retype_region "\<lambda>s. P (cdl_cdt s)"
(wp:select_wp simp:crunch_simps corrupt_intents_def)

crunch has_children[wp]: retype_region "has_children slot"
(wp:select_wp simp:crunch_simps corrupt_intents_def simp:has_children_def is_cdt_parent_def)

crunch cdt[wp]: update_available_range "\<lambda>s. P (cdl_cdt s)"
(wp:select_wp simp:crunch_simps corrupt_intents_def)

crunch has_children[wp]: update_available_range "has_children slot"
(wp:select_wp simp:crunch_simps corrupt_intents_def simp:has_children_def is_cdt_parent_def)

lemma invoke_untyped_one_has_children:
  "uinv = (Retype uref nt ts [slot] has_kids (Suc 0))
  \<Longrightarrow> \<lbrace>K(nt \<noteq> UntypedType)\<rbrace> invoke_untyped uinv \<lbrace>\<lambda>r. has_children uref\<rbrace>"
  apply (simp add:invoke_untyped_def)
  apply (wp)
       apply (rule_tac P = "zip [slot] new_obj_refs \<noteq> []" in hoare_gen_asm)
       apply (rule hoare_strengthen_post[OF mapM_x_accumulate_checks])
         apply (rule create_cap_has_children)
        apply wp
       apply simp
      apply (clarsimp simp:neq_Nil_conv)
      apply auto[1]
     apply wp
    apply (rule hoare_strengthen_post[OF generate_object_ids_rv])
     apply (clarsimp simp:zip_is_empty)
    apply wp
  apply simp
  done

lemma invoke_untyped_one_wp:
  "uinv = (Retype uref nt ts [dest_slot] has_kids (Suc 0))
  \<Longrightarrow> \<lbrace>K (default_object nt ts minBound = Some obj \<and> nt \<noteq> UntypedType
     \<and> free_range \<subseteq> tot_free_range
     \<and> (\<not> retype_with_kids (InvokeUntyped uinv) \<longrightarrow> free_range = obj_range) \<and> finite tot_free_range)
     and (\<lambda>s. cdl_current_domain s = minBound)
     and < dest_slot \<mapsto>c NullCap
    \<and>* (\<And>* ptr\<in>tot_free_range. ptr \<mapsto>o Untyped)
    \<and>* uref \<mapsto>c UntypedCap obj_range free_range
    \<and>* P > \<rbrace>
  invoke_untyped uinv
  \<lbrace>\<lambda>_ s. (\<exists>oid free_range'.
  oid \<in> free_range
  \<and> free_range' \<subseteq> free_range - {oid} \<and>
  < dest_slot \<mapsto>c (default_cap nt {oid} ts)
  \<and>* oid \<mapsto>o obj
  \<and>* (\<And>* ptr\<in>tot_free_range - {oid}. ptr \<mapsto>o Untyped)
  \<and>* uref \<mapsto>c UntypedCap obj_range free_range'
  \<and>* P > s) \<rbrace>"
  apply simp
  apply (rule hoare_pre)
   apply (rule hoare_strengthen_post)
    apply (rule invoke_untyped_wp
      [where free_range = free_range and obj_range = obj_range
      and tot_free_range = tot_free_range and obj = obj and P = P])
   apply clarsimp
   apply (case_tac nlist)
    apply simp+
   apply (rule_tac x = "a" in exI)
   apply simp
   apply (rule_tac x = free_range' in exI)
   apply simp
  apply clarsimp
  done

lemma mark_tcb_intent_error_has_children[wp]:
  "\<lbrace>\<lambda>s. P (has_children ptr s)\<rbrace>
  mark_tcb_intent_error cur_thread b
  \<lbrace>\<lambda>rv s. P (has_children ptr s)\<rbrace>"
  apply (simp add:has_children_def is_cdt_parent_def
    mark_tcb_intent_error_def update_thread_def
    set_object_def | wp | wpc)+
  apply fastforce
  done

crunch cdt[wp]: corrupt_frame "\<lambda>s. P (cdl_cdt s)"
(wp:select_wp simp:crunch_simps corrupt_intents_def)

crunch cdt[wp]: corrupt_tcb_intent "\<lambda>s. P (cdl_cdt s)"
(wp:select_wp simp:crunch_simps corrupt_intents_def)

crunch cdt[wp]: corrupt_ipc_buffer "\<lambda>s. P (cdl_cdt s)"
(wp:select_wp simp:crunch_simps corrupt_intents_def)

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

crunch cdt[wp]: set_cap "\<lambda>s. P (cdl_cdt s)"
(wp:select_wp simp:crunch_simps corrupt_intents_def)

crunch has_children[wp]: set_cap "has_children slot"
(wp:select_wp simp:crunch_simps corrupt_intents_def simp:has_children_def is_cdt_parent_def)

crunch cdl_current_domain[wp]: invoke_untyped "\<lambda>s. P (cdl_current_domain s)"
(wp:select_wp mapM_x_wp' crunch_wps hoare_unless_wp
  simp:detype_def crunch_simps)

lemma seL4_Untyped_Retype_sep:
  "\<lbrakk>cap_object root_cnode_cap = root_cnode;
   ucptr_slot = offset ucptr root_size;
   is_cnode_cap root_cnode_cap;
   ncptr_slot = offset ncptr root_size;
   unat ncptr_slot_nat = ncptr_slot;
   one_lvl_lookup root_cnode_cap 32 root_size;
   guard_equal root_cnode_cap ucptr 32;
   guard_equal root_cnode_cap root 32\<rbrakk>
  \<Longrightarrow> \<lbrace> K (nt\<noteq> UntypedType \<and> default_object nt (unat ts) minBound = Some obj
    \<and> free_range\<subseteq> tot_free_range) and
    \<guillemotleft>root_tcb_id \<mapsto>f (Tcb tcb)
  \<and>* (root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap
  \<and>* (cap_object root_cnode_cap \<mapsto>f CNode (empty_cnode root_size))
  \<and>* (root_cnode, ucptr_slot) \<mapsto>c UntypedCap obj_range free_range
  \<and>* (root_cnode, ncptr_slot ) \<mapsto>c NullCap
  \<and>* (\<And>* ptr\<in>tot_free_range. ptr \<mapsto>o Untyped)
  \<and>* (root_tcb_id, tcb_cspace_slot) \<mapsto>c root_cnode_cap
  \<and>* (cap_object root_cnode_cap, offset root root_size) \<mapsto>c root_cnode_cap
  \<and>* P\<guillemotright>
    and (\<lambda>s. \<not> has_children (root_cnode,ucptr_slot) (kernel_state s) \<longrightarrow> obj_range = free_range)
  \<rbrace>
  seL4_Untyped_Retype ucptr nt ts root node_index 0 ncptr_slot_nat 1
  \<lbrace>\<lambda>r s. (\<not> r \<longrightarrow> (\<exists>oid free_range'. (\<guillemotleft>
     (root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap
  \<and>* root_tcb_id \<mapsto>f (Tcb tcb)
  \<and>* (root_cnode, ncptr_slot) \<mapsto>c (default_cap nt {oid} (unat ts))
  \<and>* oid \<mapsto>o obj
  \<and>* (cap_object root_cnode_cap \<mapsto>f CNode (empty_cnode root_size))
  \<and>* (\<And>* ptr\<in>tot_free_range - {oid}. ptr \<mapsto>o Untyped)
  \<and>* (root_cnode, ucptr_slot) \<mapsto>c UntypedCap obj_range free_range'
  \<and>* (root_tcb_id, tcb_cspace_slot) \<mapsto>c root_cnode_cap
  \<and>* (cap_object root_cnode_cap, offset root root_size) \<mapsto>c root_cnode_cap
  \<and>* P \<guillemotright> s ) \<and> free_range' \<subseteq> free_range - {oid} \<and> oid \<in> free_range)
  \<and> has_children (root_cnode,ucptr_slot) (kernel_state s))
  \<and> (r \<longrightarrow> (\<guillemotleft>
     (root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap
  \<and>* root_tcb_id \<mapsto>f (Tcb tcb)
  \<and>* (cap_object root_cnode_cap \<mapsto>f CNode (empty_cnode root_size))
  \<and>* (root_cnode,ucptr_slot) \<mapsto>c UntypedCap obj_range free_range
  \<and>* (root_cnode, ncptr_slot) \<mapsto>c NullCap
  \<and>* (\<And>* ptr\<in>tot_free_range. ptr \<mapsto>o Untyped)
  \<and>* (root_tcb_id, tcb_cspace_slot) \<mapsto>c root_cnode_cap
  \<and>* (cap_object root_cnode_cap, offset root root_size) \<mapsto>c root_cnode_cap
  \<and>* P \<guillemotright> s )
  \<and> (\<not>has_children (root_cnode,ucptr_slot) (kernel_state s) \<longrightarrow> obj_range = free_range))  \<rbrace>"
  apply (simp add:seL4_Untyped_Retype_def sep_state_projection2_def)
  apply (rule hoare_name_pre_state)
  apply (rule hoare_pre)
   apply (rule do_kernel_op_pull_back)
   apply (rule call_kernel_with_intent_allow_error_helper
     [where check= False and tcb = tcb,simplified,rotated -1])
                apply assumption
               apply fastforce
              apply (wp hoare_vcg_ex_lift set_cap_wp)[5]
         apply (rule_tac P = "\<exists>has_kids. iv = InvokeUntyped (Retype (root_cnode,ucptr_slot) nt (unat ts)
               [(root_cnode, ncptr_slot)]
               has_kids 1)"
           in hoare_gen_asmEx)
         apply clarsimp
         apply wp
         apply (rule hoare_strengthen_post[OF hoare_vcg_conj_lift])
          apply (rule invoke_untyped_one_has_children)
          apply fastforce
         apply (rule_tac P = "P1 \<and>* P2" for P1 P2 in
           invoke_untyped_one_wp
             [where free_range = free_range
               and obj_range = obj_range
               and obj = obj
               and tot_free_range = tot_free_range])
          apply fastforce
         apply clarsimp
         apply (rule conjI)
         apply (sep_erule refl_imp, simp)
         apply (rule_tac x = oid in exI)
         apply (rule_tac x = free_range' in exI)
         apply clarsimp
         apply (sep_schem)
        apply (wp hoare_vcg_conj_lift)
         apply (wp hoare_strengthen_post[OF set_cap_wp])
         apply (sep_select 4,assumption)
        apply wp[1]
       apply (rule_tac P =" nt \<noteq> UntypedType
        \<and> c = UntypedCap obj_range free_range \<and> cs = [(root_cnode_cap,(root_cnode,offset root root_size))]"
        in hoare_gen_asmEx)
      apply simp
       apply (rule decode_untyped_invocation_rvu)
       apply simp
      apply (simp add:lookup_extra_caps_def mapME_singleton)
      apply (rule wp_no_exception_seq)
       apply wp[1]
      apply (rule lookup_cap_and_slot_rvu[where r = root_size
       and  cap' = "root_cnode_cap"])
     apply (wp lookup_cap_and_slot_rvu[where r = root_size
       and cap' = "UntypedCap obj_range free_range"])[1]
     apply clarsimp
     apply (intro conjI allI)
      apply (intro impI allI)
      apply (rule conjI)
       apply (intro impI allI)
        apply (clarsimp dest!: reset_cap_asid_simps2 reset_cap_asid_cnode_cap)
        apply (intro conjI,simp_all)[1]
          apply sep_solve
         apply sep_cancel+

      apply (clarsimp simp:user_pointer_at_def Let_def word_bits_def)
      apply (rule conjI)
       apply (thin_tac "<P \<and>* Q \<and>* (\<lambda>s. True)> s" for P Q s)
       apply (clarsimp simp:user_pointer_at_def Let_def word_bits_def)
       apply (sep_solve)
      apply (clarsimp simp: ep_related_cap_def
        dest!: reset_cap_asid_simps2 reset_cap_asid_cnode_cap)+
          apply (thin_tac "<P \<and>* Q \<and>* (\<lambda>s. True)> s" for P Q s)
      apply (sep_cancel)
    apply (clarsimp simp:user_pointer_at_def Let_def
       word_bits_def sep_conj_assoc)
    apply (sep_solve)
    apply (clarsimp simp:user_pointer_at_def Let_def
       word_bits_def sep_conj_assoc)
    apply (rule hoare_pre)
     apply (wp lookup_cap_and_slot_rvu[where r = root_size and
       cap = "root_cnode_cap" and cap' = "UntypedCap obj_range free_range"])
    apply (intro conjI impI allI)
     apply (clarsimp simp: ep_related_cap_def
       dest!: reset_cap_asid_simps2 reset_cap_asid_cnode_cap)
    apply (clarsimp simp:user_pointer_at_def Let_def
      word_bits_def sep_conj_assoc)
    apply (thin_tac "<P \<and>* Q \<and>* sep_true> sa" for P Q)
    apply sep_solve
   apply (wp update_thread_intent_update)
  apply (intro conjI allI impI,simp_all)
     apply (clarsimp simp:ep_related_cap_def)+
    apply sep_solve
   apply clarsimp+
   apply (sep_solve)
  apply clarsimp
  apply (sep_solve)
  done




(**********************************************************************
 * We need to know the cdt only ever increases when creating objects. *
 *                                                                    *
 * If this is the case, then we can know that UntypedCaps only ever   *
 * become parents, and never lose their children                      *
 **********************************************************************)


crunch cdt_inc[wp]: set_cap "\<lambda>s. cdl_cdt s child = parent"
(wp:select_wp simp:crunch_simps)

crunch cdt_inc[wp]: has_restart_cap "\<lambda>s. cdl_cdt s child = parent"
(wp:select_wp simp:crunch_simps)

crunch cdt_inc[wp]: schedule "\<lambda>s. cdl_cdt s child = parent"
(wp:select_wp alternative_wp crunch_wps simp:crunch_simps)

crunch cdt_inc[wp]: handle_pending_interrupts "\<lambda>s. cdl_cdt s child = parent"
(wp:select_wp alternative_wp simp:crunch_simps)

lemmas gets_the_resolve_cap_sym = gets_the_resolve_cap[symmetric]

lemma unify_failure_cdt_lift:
  "\<lbrace>\<lambda>s. P (cdl_cdt s)\<rbrace> f \<lbrace>\<lambda>r s. P (cdl_cdt s)\<rbrace>
  \<Longrightarrow> \<lbrace>\<lambda>s. P (cdl_cdt s)\<rbrace> unify_failure f \<lbrace>\<lambda>r s. Q r s \<longrightarrow> P (cdl_cdt s)\<rbrace>,
  \<lbrace>\<lambda>r s. Q' r s \<longrightarrow> P (cdl_cdt s)\<rbrace>"
  apply (simp add:unify_failure_def)
  apply (wp hoare_drop_imps)
  apply (clarsimp simp:validE_def valid_def)
  apply (case_tac a,fastforce+)
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

crunch cdt_inc[wp]: block_thread_on_ipc "\<lambda>s. P (cdl_cdt s)"
(wp:hoare_vcg_conj_lift hoare_drop_impE_R
  hoare_drop_imps
  simp:crunch_simps get_thread_def
  ignore:unify_failure)

crunch cdt_inc[wp]: set_untyped_cap_as_full "\<lambda>s. P (cdl_cdt s)"
(wp:hoare_vcg_conj_lift hoare_drop_impE_R
  simp:crunch_simps get_thread_def)

crunch cdt_inc[wp]: mark_tcb_intent_error "\<lambda>s. P (cdl_cdt s)"
(wp:hoare_vcg_conj_lift hoare_drop_impE_R
  simp:crunch_simps)

crunch cdt_inv[wp]: set_cap "\<lambda>s. P (cdl_cdt s)"
(wp:hoare_vcg_conj_lift hoare_drop_impE_R
  simp:crunch_simps)

crunch cdt_inc[wp]: handle_pending_interrupts "\<lambda>s. cdl_cdt s child = parent"
(wp:select_wp alternative_wp simp:crunch_simps)

lemma set_parent_other:
  "\<lbrace>\<lambda>s. cdl_cdt s child = Some parent\<rbrace> set_parent dest uref \<lbrace>\<lambda>_ s. cdl_cdt s child = Some parent\<rbrace>"
  apply (simp add:set_parent_def)
  apply wp
  apply auto
  done

lemma invoke_untyped_same_parent:
  "uinv = (Retype uref nt ts dest_slots has_kids n)
  \<Longrightarrow> \<lbrace>\<lambda>s.  cdl_cdt s child = Some parent \<rbrace>
  invoke_untyped uinv
  \<lbrace>\<lambda>_ s. cdl_cdt s child = Some parent \<rbrace>"
  apply (clarsimp simp:invoke_untyped_def)
  apply wp
      apply clarsimp
      apply (wp mapM_x_wp[OF _ subset_refl])
       apply (simp add:create_cap_def)
        apply (rule hoare_pre)
        apply (wp set_parent_other hoare_unless_wp
          |wpc|simp)+
  apply (clarsimp simp:detype_def)
  done

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

lemma seL4_Untyped_Retype_cdt_inc:
  "\<lbrakk>cap_object root_cnode_cap = root_cnode;
   ucptr_slot = offset ucptr root_size;
   is_cnode_cap root_cnode_cap;
   one_lvl_lookup root_cnode_cap 32 root_size;
   guard_equal root_cnode_cap ucptr 32;
   guard_equal root_cnode_cap root 32\<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s.  \<guillemotleft>root_tcb_id \<mapsto>f Tcb tcb \<and>*
  cap_object root_cnode_cap \<mapsto>f CNode (empty_cnode root_size) \<and>*
  (cap_object root_cnode_cap, offset ucptr root_size) \<mapsto>c UntypedCap obj_range free_range \<and>*
  (root_tcb_id, tcb_cspace_slot) \<mapsto>c root_cnode_cap \<and>*
  (cap_object root_cnode_cap, offset root root_size) \<mapsto>c root_cnode_cap \<and>* sep_true\<guillemotright> s
  \<and> cdl_cdt (kernel_state s) child = Some parent\<rbrace>
  seL4_Untyped_Retype ucptr type sz root node_index
    node_depth node_offset node_window
  \<lbrace>\<lambda>rv s. cdl_cdt (kernel_state s) child = Some parent\<rbrace>"
  apply (clarsimp simp: seL4_Untyped_Retype_def)
  apply (rule hoare_pre)
  apply (rule lift_do_kernel_op')
  apply (clarsimp simp: call_kernel_with_intent_def)
  apply wp
    apply (clarsimp simp: call_kernel_def)
    apply (wp hoare_drop_imps |wpc|clarsimp)+
    apply (clarsimp simp: handle_event_def handle_syscall_def handle_invocation_def)
    apply wp
      apply (clarsimp simp: syscall_def)
       apply (rule hoare_vcg_handle_elseE[rotated])
         apply (rule valid_validE)
         apply (rule hoare_pre_cont)
        apply (rule valid_validE)
        apply (rule_tac P = "cdl_intent_op (cdl_tcb_intent xb) \<noteq> None"
          in hoare_gen_asm)
        apply (clarsimp split del:split_if)
        apply wp
        apply (rule hoare_vcg_handle_elseE[rotated])
          apply (wp whenE_inv|simp)+
          apply (rule_tac P = "\<exists>has_kids ref nt ts dests n.
            xc = InvokeUntyped (Retype ref nt (unat ts)
               dests
               has_kids n)"
           in hoare_gen_asmEx)
          apply clarsimp
          apply (rule invoke_untyped_same_parent)
          apply fastforce
       apply wp
       apply (rule_tac P ="fst (a,(aa,b),ba) = UntypedCap obj_range free_range"
        in hoare_gen_asmEx)
       apply (simp add:decode_untyped_invocation_def decode_invocation_def)
       apply (wp throw_on_none_wp alternativeE_wp |wpc | simp)+
               apply (wp mapME_x_inv_wp unlessE_wp hoare_drop_imps
                 throw_on_none_wp | simp)+
        apply (rule hoare_post_impErr
          [rotated 1,where Q = "\<lambda>r s. cdl_cdt s child = Some parent"])
          apply (clarsimp split:option.split)
          apply fastforce
         apply assumption
        apply (wp throw_opt_wp)
       apply (clarsimp split:option.split)
       apply (intro conjI impI,assumption+)
      apply (rule_tac P = "cdl_intent_extras (cdl_tcb_intent xb) = [root]" in hoare_gen_asmEx)
      apply (clarsimp simp:lookup_extra_caps_def mapME_singleton bindE_assoc)
      apply (rule wp_no_exception_seq)
       apply wpc
       apply (rule wp_no_exception_seq)
        apply wp[1]
       apply (wp lookup_cap_and_slot_rvu)[2]
     apply clarsimp
    apply (wp get_thread_sep_wp_precise hoare_drop_imps update_thread_wp)
    apply (rule_tac P = " x = root_tcb_id " in hoare_gen_asm)
    apply simp
    apply (rule_tac Q = "\<lambda>r s. cdl_cdt s child = Some parent \<and>
      (cdl_current_thread s) = Some root_tcb_id \<and>
      tcb_at' (\<lambda>tcb. cdl_tcb_intent tcb = \<lparr>cdl_intent_op =
      Some (UntypedIntent (UntypedRetypeIntent type sz node_index node_depth node_offset node_window)),
      cdl_intent_error = False, cdl_intent_cap = ucptr, cdl_intent_extras = [root],
      cdl_intent_recv_slot = None\<rparr>) root_tcb_id s \<and>
      < root_tcb_id \<mapsto>f (Tcb tcb)
      \<and>* (cap_object root_cnode_cap \<mapsto>f CNode (empty_cnode root_size))
      \<and>* (cap_object root_cnode_cap, offset ucptr root_size) \<mapsto>c UntypedCap obj_range free_range
      \<and>* (root_tcb_id, tcb_cspace_slot) \<mapsto>c root_cnode_cap
      \<and>* (cap_object root_cnode_cap, offset root root_size) \<mapsto>c root_cnode_cap
      \<and>* sep_true> s" in  hoare_strengthen_post)
    apply clarsimp
    apply (wp update_thread_wp update_thread_intent_update)
    apply clarsimp
    apply (frule obj_exists_map_f)
     apply (clarsimp simp:opt_object_def
       object_type_def,simp split:cdl_object.split_asm)
    apply (clarsimp simp:object_at_def)
    apply (intro conjI allI impI)
    prefer 3
        apply (clarsimp simp:user_pointer_at_def Let_def
          word_bits_def sep_conj_assoc)
        apply (intro conjI,simp_all)[1]
        apply sep_solve
     apply (clarsimp simp:reset_cap_asid_untyped_cap_eqD)
    apply (clarsimp simp:user_pointer_at_def Let_def
          word_bits_def sep_conj_assoc)
    apply (intro conjI,simp_all)[1]
    apply sep_solve
   apply clarsimp
   apply wp
  apply (clarsimp simp:sep_state_projection2_def)
  apply (drule obj_exists_map_f)
  apply (clarsimp simp:object_at_def opt_object_def object_type_def)
  apply (fastforce split:cdl_object.split_asm)
  done

end
