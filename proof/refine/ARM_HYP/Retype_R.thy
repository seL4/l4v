(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
   Retype refinement
*)

theory Retype_R
imports VSpace_R
begin

context begin interpretation Arch . (*FIXME: arch_split*)

definition
  APIType_map2 :: "kernel_object + ARM_HYP_H.object_type \<Rightarrow> Structures_A.apiobject_type"
where
 "APIType_map2 ty \<equiv> case ty of
      Inr (APIObjectType ArchTypes_H.Untyped) \<Rightarrow> Structures_A.Untyped
    | Inr (APIObjectType ArchTypes_H.TCBObject) \<Rightarrow> Structures_A.TCBObject
    | Inr (APIObjectType ArchTypes_H.EndpointObject) \<Rightarrow> Structures_A.EndpointObject
    | Inr (APIObjectType ArchTypes_H.NotificationObject) \<Rightarrow> Structures_A.NotificationObject
    | Inr (APIObjectType ArchTypes_H.CapTableObject) \<Rightarrow> Structures_A.CapTableObject
    | Inr PageTableObject \<Rightarrow> ArchObject PageTableObj
    | Inr PageDirectoryObject \<Rightarrow> ArchObject PageDirectoryObj
    | Inr LargePageObject \<Rightarrow> ArchObject LargePageObj
    | Inr SectionObject \<Rightarrow> ArchObject SectionObj
    | Inr SuperSectionObject \<Rightarrow> ArchObject SuperSectionObj
    | Inl (KOArch (KOASIDPool _)) \<Rightarrow> ArchObject ASIDPoolObj
\<comment> \<open>    | Inl (KOArch (KOVCPU _)) \<Rightarrow> ArchObject ARM_A.VCPUObj\<close> \<comment> \<open>inl? inr?\<close>
    | Inr VCPUObject \<Rightarrow> ArchObject ARM_A.VCPUObj \<comment> \<open>inl? inr?\<close>
    | _ \<Rightarrow> ArchObject SmallPageObj"

lemma placeNewObject_def2:
 "placeNewObject ptr val gb = createObjects' ptr 1 (injectKO val) gb"
   apply (clarsimp simp:placeNewObject_def placeNewObject'_def
     createObjects'_def shiftL_nat)
  done

lemma createObjects_ret:
  "\<lbrakk>n < 2^word_bits;n\<noteq> 0\<rbrakk> \<Longrightarrow>
   \<lbrace>\<top>\<rbrace> createObjects y n ko gbits
   \<lbrace>\<lambda>r s. r = map (\<lambda>p. ptr_add y (p * 2 ^ objBitsKO ko * 2 ^ gbits))
                [0..< n]\<rbrace>"
    unfolding createObjects_def createObjects'_def
  apply (simp add: split_def)
  apply (wp|simp cong: if_cong)+
  apply (clarsimp simp: ptr_add_def upto_enum_def o_def
                        unat_sub word_le_nat_alt
                        power_sub[symmetric]
                        objBits_def[symmetric]
              simp del: upt_Suc)
  apply (clarsimp simp: unat_of_nat_minus_1 word_bits_def
                        shiftl_t2n power_add)
  done

lemma objBitsKO_bounded2[simp]:
  "objBitsKO ko < word_bits"
  by (simp add: objBits_simps' word_bits_def vspace_bits_defs vcpu_bits_def archObjSize_def
         split: Structures_H.kernel_object.split arch_kernel_object.split)

definition
  APIType_capBits :: "ARM_HYP_H.object_type \<Rightarrow> nat \<Rightarrow> nat"
where
  "APIType_capBits ty us \<equiv> case ty of
      APIObjectType ArchTypes_H.Untyped \<Rightarrow> us
    | APIObjectType ArchTypes_H.TCBObject \<Rightarrow> objBits (makeObject :: tcb)
    | APIObjectType ArchTypes_H.EndpointObject \<Rightarrow> objBits (makeObject :: endpoint)
    | APIObjectType ArchTypes_H.NotificationObject \<Rightarrow> objBits (makeObject :: Structures_H.notification)
    | APIObjectType ArchTypes_H.CapTableObject \<Rightarrow> objBits (makeObject :: cte) + us
    | SmallPageObject \<Rightarrow> pageBitsForSize ARMSmallPage
    | LargePageObject \<Rightarrow> pageBitsForSize ARMLargePage
    | SectionObject \<Rightarrow> pageBitsForSize ARMSection
    | SuperSectionObject \<Rightarrow> pageBitsForSize ARMSuperSection
    | PageTableObject \<Rightarrow> 12
    | PageDirectoryObject \<Rightarrow> 14
    | VCPUObject \<Rightarrow> vcpu_bits"

definition
  makeObjectKO :: "bool \<Rightarrow> (kernel_object + ARM_HYP_H.object_type) \<rightharpoonup> kernel_object"
where
  "makeObjectKO dev ty \<equiv> case ty of
      Inl KOUserData \<Rightarrow> Some KOUserData
    | Inl (KOArch (KOASIDPool _)) \<Rightarrow> Some (KOArch (KOASIDPool makeObject))
    | Inl (KOArch (KOVCPU _)) \<Rightarrow> Some (KOArch (KOVCPU makeObject)) \<comment> \<open>inl or inr?\<close>
    | Inr VCPUObject \<Rightarrow> Some (KOArch (KOVCPU makeObject)) \<comment> \<open>inl or inr?\<close>
    | Inr (APIObjectType ArchTypes_H.TCBObject) \<Rightarrow> Some (KOTCB makeObject)
    | Inr (APIObjectType ArchTypes_H.EndpointObject) \<Rightarrow> Some (KOEndpoint makeObject)
    | Inr (APIObjectType ArchTypes_H.NotificationObject) \<Rightarrow> Some (KONotification makeObject)
    | Inr (APIObjectType ArchTypes_H.CapTableObject) \<Rightarrow> Some (KOCTE makeObject)
    | Inr PageTableObject \<Rightarrow> Some (KOArch (KOPTE makeObject))
    | Inr PageDirectoryObject \<Rightarrow> Some (KOArch (KOPDE makeObject))
    | Inr SmallPageObject \<Rightarrow> Some (if dev then KOUserDataDevice else KOUserData)
    | Inr LargePageObject \<Rightarrow> Some(if dev then KOUserDataDevice else KOUserData)
    | Inr SectionObject \<Rightarrow> Some (if dev then KOUserDataDevice else KOUserData)
    | Inr SuperSectionObject \<Rightarrow> Some (if dev then KOUserDataDevice else KOUserData)
    | _ \<Rightarrow> None"

text \<open>makeObject etc. lemmas\<close>

lemma NullCap_valid' [iff]: "s \<turnstile>' capability.NullCap"
  unfolding valid_cap'_def by simp

lemma valid_obj_makeObject_cte [simp]:
  "valid_obj' (KOCTE makeObject) s"
  unfolding valid_obj'_def valid_cte'_def
  by (clarsimp simp: makeObject_cte)

lemma valid_obj_makeObject_tcb [simp]:
  "valid_obj' (KOTCB makeObject) s"
  unfolding valid_obj'_def valid_tcb'_def  valid_tcb_state'_def valid_arch_tcb'_def
  by (clarsimp simp: makeObject_tcb makeObject_cte tcb_cte_cases_def minBound_word newArchTCB_def)

lemma valid_obj_makeObject_endpoint [simp]:
  "valid_obj' (KOEndpoint makeObject) s"
  unfolding valid_obj'_def valid_ep'_def
  by (clarsimp simp: makeObject_endpoint)

lemma valid_obj_makeObject_notification [simp]:
  "valid_obj' (KONotification makeObject) s"
  unfolding valid_obj'_def valid_ntfn'_def
  by (clarsimp simp: makeObject_notification)

lemma valid_obj_makeObject_user_data [simp]:
  "valid_obj' (KOUserData) s"
  unfolding valid_obj'_def by simp

lemma valid_obj_makeObject_user_data_device [simp]:
  "valid_obj' (KOUserDataDevice) s"
  unfolding valid_obj'_def by simp

lemma valid_obj_makeObject_pte[simp]:
  "valid_obj' (KOArch (KOPTE makeObject)) s"
  unfolding valid_obj'_def by (simp add: makeObject_pte)

lemma valid_obj_makeObject_pde[simp]:
  "valid_obj' (KOArch (KOPDE makeObject)) s"
  unfolding valid_obj'_def by (simp add: makeObject_pde)

lemma valid_obj_makeObject_asid_pool[simp]:
  "valid_obj' (KOArch (KOASIDPool makeObject)) s"
  unfolding valid_obj'_def
  by (simp add: makeObject_asidpool Let_def ran_def dom_def)

lemma valid_obj_makeObject_vcpu[simp]:
  "valid_obj' (KOArch (KOVCPU makeObject)) s"
  unfolding valid_obj'_def
  by (simp add: makeObject_vcpu makeVCPUObject_def valid_vcpu'_def)

lemmas valid_obj_makeObject_rules =
  valid_obj_makeObject_user_data valid_obj_makeObject_tcb
  valid_obj_makeObject_endpoint valid_obj_makeObject_notification
  valid_obj_makeObject_cte valid_obj_makeObject_pte valid_obj_makeObject_pde
  valid_obj_makeObject_asid_pool valid_obj_makeObject_user_data_device

text \<open>On the abstract side\<close>

text \<open>Lemmas for createNewObjects etc.\<close>

lemma pspace_dom_upd:
  assumes      orth: "set as \<inter> dom ps = {}"
  shows "pspace_dom (foldr (\<lambda>p ps. ps(p \<mapsto> ko)) as ps) =
       pspace_dom ps \<union> (\<Union>x \<in> set as. fst ` obj_relation_cuts ko x)"
  using orth
  apply (subst foldr_upd_app_if)
  apply (rule set_eqI, simp add: pspace_dom_def)
  apply (rule iffI)
   apply (clarsimp split: if_split_asm)
   apply (rule rev_bexI, erule domI)
   apply (fastforce simp: image_def)
  apply (erule disjE)
   apply clarsimp
   apply (rule rev_bexI)
    apply (clarsimp simp: domIff)
    apply (erule exI)
   apply clarsimp
   apply (intro conjI impI)
    apply (drule equals0D, erule notE, erule IntI, erule domI)
   apply (fastforce simp: image_def)
  apply clarsimp
  apply (rule rev_bexI)
   apply (clarsimp simp: domIff)
   apply (erule(1) notE)
  apply clarsimp
  apply (fastforce simp: image_def)
  done

definition
  "new_cap_addrs \<equiv> \<lambda>n ptr ko. map (\<lambda>p. ptr + ((of_nat p :: word32) << (objBitsKO ko)))
                [0 ..< n]"

definition
  null_filter' :: "('a \<rightharpoonup> cte) \<Rightarrow> ('a \<rightharpoonup> cte)"
where
 "null_filter' f \<equiv> \<lambda>x. if f x = Some (CTE NullCap nullMDBNode) then None else f x"

lemma across_null_filter_eq':
  assumes eq: "null_filter' xs = null_filter' ys"
  shows "\<lbrakk> xs x = Some v; ys x = Some v \<Longrightarrow> R;
           \<lbrakk> v = CTE NullCap nullMDBNode; ys x = None \<rbrakk> \<Longrightarrow> R \<rbrakk>
            \<Longrightarrow> R"
  apply (cases "null_filter' xs x")
   apply (subgoal_tac "null_filter' ys x = None")
    apply (simp add: null_filter'_def split: if_split_asm)
   apply (simp add: eq)
  apply (subgoal_tac "null_filter' ys x = Some a")
   apply (simp add: null_filter'_def split: if_split_asm)
  apply (simp add: eq)
  done

lemma null_filter_parent_of'':
  "\<lbrakk> null_filter' xs = null_filter' ys; xs \<turnstile> x \<leadsto> c; c \<noteq> 0 \<rbrakk>
     \<Longrightarrow> ys \<turnstile> x \<leadsto> c"
  apply (clarsimp simp add: mdb_next_unfold)
  apply (drule arg_cong[where f="\<lambda>xs. xs x"])
  apply (simp add: null_filter'_def nullPointer_def split: if_split_asm)
  done

lemma null_filter_parentOf:
  "\<lbrakk> null_filter' xs = null_filter' ys; xs \<turnstile> x parentOf y \<rbrakk>
      \<Longrightarrow> ys \<turnstile> x parentOf y"
  apply (clarsimp simp add: parentOf_def)
  apply (rule across_null_filter_eq'[where x=x], assumption+)
   apply (erule(1) across_null_filter_eq')
    apply clarsimp
   apply simp
  apply simp
  done

lemma null_filter_descendant:
  "\<lbrakk> null_filter' xs = null_filter' ys; xs \<turnstile> x \<rightarrow> y \<rbrakk>
      \<Longrightarrow> ys \<turnstile> x \<rightarrow> y"
  apply (erule subtree.induct)
   apply (rule subtree.direct_parent)
     apply (erule(2) null_filter_parent_of'')
    apply assumption
   apply (erule(1) null_filter_parentOf)
  apply (erule subtree.trans_parent)
    apply (erule(2) null_filter_parent_of'')
   apply assumption
  apply (erule(1) null_filter_parentOf)
  done

lemma null_filter_descendants_of':
  "null_filter' xs = null_filter' ys
    \<Longrightarrow> descendants_of' x xs = descendants_of' x ys"
  apply (simp add: descendants_of'_def)
  apply (rule set_eqI, rule iffI)
   apply simp
   apply (erule(1) null_filter_descendant)
  apply simp
  apply (erule(1) null_filter_descendant[OF sym])
  done

lemma descendants_of_cte_at':
  "\<lbrakk> p \<in> descendants_of x (cdt s); valid_mdb s \<rbrakk>
  \<Longrightarrow> cte_wp_at (\<lambda>c. c \<noteq> cap.NullCap) p s"
  apply (simp add: descendants_of_def)
  apply (drule tranclD2)
  apply (clarsimp simp: cdt_parent_defs valid_mdb_def mdb_cte_at_def
                  simp del: split_paired_All)
  apply (fastforce elim: cte_wp_at_weakenE)
  done


lemma descendants_of_cte_at2':
  "\<lbrakk> p \<in> descendants_of x (cdt s); valid_mdb s \<rbrakk>
  \<Longrightarrow> cte_wp_at (\<lambda>c. c \<noteq> cap.NullCap) x s"
  apply (simp add: descendants_of_def)
  apply (drule tranclD)
  apply (clarsimp simp: cdt_parent_defs valid_mdb_def mdb_cte_at_def
                  simp del: split_paired_All)
  apply (fastforce elim: cte_wp_at_weakenE)
  done

lemma cte_at_next_slot'':
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows "\<lbrakk>valid_list s; valid_mdb s; finite_depth (cdt s)\<rbrakk>
    \<Longrightarrow> next_slot p (cdt_list s) (cdt s) = Some n \<Longrightarrow> cte_wp_at (\<lambda>c. c \<noteq> cap.NullCap) p s"
  apply(simp add: next_slot_def)
  apply(simp split: if_split_asm)
   apply(drule next_childD, simp)
   apply(rule_tac p=n in descendants_of_cte_at2')
    apply(simp add: child_descendant)
   apply(simp)
  apply(subgoal_tac "next_not_child_dom (p, cdt_list s, cdt s)")
   prefer 2
   apply(simp add: next_not_child_termination valid_mdb_def valid_list_def)
  apply(simp split: if_split_asm)
   apply(case_tac "cdt s p")
    apply(simp)
   apply(rule descendants_of_cte_at')
    apply(simp add: descendants_of_def cdt_parent_defs)
    apply(rule r_into_trancl, simp)
   apply(simp)
  apply(drule next_sibD)
  apply(elim exE conjE)
  apply(drule after_in_list_in_list)
  apply(rule descendants_of_cte_at')
   apply(simp add: descendants_of_def cdt_parent_defs)
   apply(rule r_into_trancl, simp)
  apply(simp)
  done


lemma state_relation_null_filterE:
  "\<lbrakk> (s, s') \<in> state_relation; t = kheap_update f (ekheap_update ef s);
     \<exists>f' g' h'.
     t' = s'\<lparr>ksPSpace := f' (ksPSpace s'), gsUserPages := g' (gsUserPages s'),
             gsCNodes := h' (gsCNodes s')\<rparr>;
     null_filter (caps_of_state t) = null_filter (caps_of_state s);
     null_filter' (ctes_of t') = null_filter' (ctes_of s');
     pspace_relation (kheap t) (ksPSpace t');
     ekheap_relation (ekheap t) (ksPSpace t');
     ghost_relation (kheap t) (gsUserPages t') (gsCNodes t'); valid_list s;
     pspace_aligned' s'; pspace_distinct' s'; valid_objs s; valid_mdb s;
     pspace_aligned' t'; pspace_distinct' t';
     mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s) \<rbrakk>
      \<Longrightarrow> (t, t') \<in> state_relation"
  apply (clarsimp simp: state_relation_def)
  apply (intro conjI)
    apply (simp add: cdt_relation_def cte_wp_at_caps_of_state)
    apply (elim allEI)
    apply clarsimp
    apply (erule(1) across_null_filter_eq)
     apply simp
     apply (rule null_filter_descendants_of', simp)
    apply simp
    apply (case_tac "cdt s (a, b)")
     apply (subst mdb_cte_at_no_descendants, assumption)
      apply (simp add: cte_wp_at_caps_of_state swp_def)
     apply (cut_tac s="kheap_update f (ekheap_update ef s)"  and
                    s'="s'\<lparr>ksPSpace := f' (ksPSpace s'),
                           gsUserPages := g' (gsUserPages s'),
                           gsCNodes := h' (gsCNodes s')\<rparr>"
            in pspace_relation_ctes_ofI, simp_all)[1]
      apply (simp add: trans_state_update[symmetric] del: trans_state_update)
      apply (erule caps_of_state_cteD)
     apply (clarsimp simp: descendants_of'_def)
     apply (case_tac cte)
     apply (erule Null_not_subtree[rotated])
     apply simp
    apply (drule(1) mdb_cte_atD)
    apply (clarsimp simp: cte_wp_at_caps_of_state)
   apply(simp add: cdt_list_relation_def cte_wp_at_caps_of_state)
   apply(elim allEI)
   apply(clarsimp)
   apply(case_tac "next_slot (a, b) (cdt_list (s)) (cdt s)")
    apply(simp)
   apply(subgoal_tac "cte_wp_at (\<lambda>c. c \<noteq> cap.NullCap) (a, b) s")
    apply(drule_tac f="\<lambda>cs. cs (a, b)" in arg_cong)
    apply(clarsimp simp: cte_wp_at_caps_of_state)
    apply(clarsimp simp: null_filter_def split: if_split_asm)
    apply(drule_tac f="\<lambda>ctes. ctes (cte_map (a, b))" in arg_cong)
    apply(simp add: null_filter'_def cte_wp_at_ctes_of split: if_split_asm)
    apply(frule pspace_relation_cte_wp_at)
       apply(simp add: cte_wp_at_caps_of_state)
      apply(simp)
     apply(simp)
    apply(simp add: cte_wp_at_ctes_of)
   apply (simp add: mdb_cte_at_def)
   apply(frule finite_depth)
   apply(frule(3) cte_at_next_slot'')
   apply simp
  apply (simp add: revokable_relation_def)
  apply (elim allEI, rule impI, drule(1) mp, elim allEI)
  apply (clarsimp elim!: null_filterE)
  apply (drule(3) pspace_relation_cte_wp_at [OF _ caps_of_state_cteD])
  apply (drule_tac f="\<lambda>ctes. ctes (cte_map (a, b))" in arg_cong)
  apply (clarsimp simp: null_filter'_def cte_wp_at_ctes_of
                 split: if_split_asm)
  done

lemma lookupAround2_pspace_no:
  "is_aligned ptr sz \<Longrightarrow>
   (case fst (lookupAround2 (ptr + 2 ^ sz - 1) ps) of None \<Rightarrow> return ()
             | Some (x, y) \<Rightarrow> haskell_assert (x < fromPPtr ptr) [])
      = assert ({ptr..ptr + 2 ^ sz - 1} \<inter> dom ps = {})"
  apply (simp add: assert_def split: option.split)
  apply safe
    apply (clarsimp simp: lookupAround2_None1)
   apply (clarsimp simp: lookupAround2_char1)
  apply (clarsimp simp: lookupAround2_char1)
  apply (drule_tac a=a in equals0D)
  apply (simp add: linorder_not_less)
  apply fastforce
  done

lemma pspace_no_overlap_disjoint':
  "\<lbrakk>pspace_aligned' s;pspace_no_overlap' x n s\<rbrakk>
   \<Longrightarrow> {x .. (x && ~~ mask n) + 2 ^ n  - 1} \<inter> dom (ksPSpace s) = {}"
  unfolding pspace_no_overlap'_def
  apply (rule disjointI)
  apply (rule ccontr)
  apply clarsimp
  apply (elim allE impE notE)
    apply (simp add:field_simps)+
    apply (erule(2) order_trans[OF _ is_aligned_no_overflow,OF _ pspace_alignedD'])
    apply (erule(1) is_aligned_no_overflow[OF pspace_alignedD'])
  apply (erule order_trans)
  apply (simp add:p_assoc_help)
done

lemma foldr_update_ko_wp_at':
  assumes pv: "pspace_aligned' s" "pspace_distinct' s"
     and pv': "pspace_aligned' (ksPSpace_update (\<lambda>x xa. if xa \<in> set addrs then Some obj else ksPSpace s xa) s)"
              "pspace_distinct' (ksPSpace_update (\<lambda>x xa. if xa \<in> set addrs then Some obj else ksPSpace s xa) s)"
      and al: "\<forall>x \<in> set addrs. is_aligned x (objBitsKO obj)"
   shows
  "ko_wp_at' P p (ksPSpace_update (\<lambda>x xa. if xa \<in> set addrs then Some obj else ksPSpace s xa) s)
         = (if p \<in> set addrs then P obj
                         else ko_wp_at' P p s)"
  (is "ko_wp_at' P p ?s' = ?Q")
  apply (clarsimp simp: ko_wp_at'_def projectKOs al)
  apply (intro conjI impI)
   apply safe[1]
   apply (rule pspace_distinctD' [OF _ pv'(2)])
   apply simp
  apply safe[1]
   apply (simp add: ps_clear_def dom_if_Some)
   apply blast
  apply simp
  apply (rule pspace_distinctD' [OF _ pv'(2)])
  apply simp
  done

lemma foldr_update_obj_at':
  assumes pv: "pspace_aligned' s" "pspace_distinct' s"
     and pv': "pspace_aligned' (ksPSpace_update (\<lambda>x xa. if xa \<in> set addrs then Some obj else ksPSpace s xa) s)"
              "pspace_distinct' (ksPSpace_update (\<lambda>x xa. if xa \<in> set addrs then Some obj else ksPSpace s xa) s)"
      and al: "\<forall>x \<in> set addrs. is_aligned x (objBitsKO obj)"
   shows
  "obj_at' P p (ksPSpace_update (\<lambda>x xa. if xa \<in> set addrs then Some obj else ksPSpace s xa) s)
         = (if p \<in> set addrs then (\<exists>obj'. projectKO_opt obj = Some obj' \<and> P obj')
                         else obj_at' P p s)"
  apply (simp only: obj_at'_real_def)
  apply (rule foldr_update_ko_wp_at' [OF pv pv' al])
  done

lemma makeObjectKO_eq:
  assumes x: "makeObjectKO dev tp = Some v"
  shows
  "(v = KOCTE cte) =
       (tp = Inr (APIObjectType ArchTypes_H.CapTableObject) \<and> cte = makeObject)"
  "(v = KOTCB tcb) =
       (tp = Inr (APIObjectType ArchTypes_H.TCBObject) \<and> tcb = makeObject)"
  using x
  by (simp add: makeObjectKO_def eq_commute
         split: apiobject_type.split_asm sum.split_asm kernel_object.split_asm
                ARM_HYP_H.object_type.split_asm arch_kernel_object.split_asm)+

lemma pspace_no_overlap_base':
  "\<lbrakk>pspace_aligned' s;pspace_no_overlap' x n s; is_aligned x n \<rbrakk> \<Longrightarrow> ksPSpace s x = None"
  apply (drule(1) pspace_no_overlap_disjoint')
  apply (drule equals0D[where a=x])
  apply (rule ccontr, clarsimp)
  apply (erule is_aligned_get_word_bits)
   apply (erule impE)
   apply (frule mask_out_add_aligned[where q = 0,simplified,symmetric])
   apply (fastforce simp add: is_aligned_no_overflow)
  apply clarsimp+
  done

lemma the_ctes_makeObject:
  "fst (the (tcb_cte_cases n)) makeObject
     = (if tcb_cte_cases n = None
           then fst (the None :: (Structures_H.tcb \<Rightarrow> cte) \<times> ((cte \<Rightarrow> cte) \<Rightarrow> Structures_H.tcb \<Rightarrow> Structures_H.tcb))
                     (makeObject :: tcb)
           else makeObject)"
  apply (simp add: makeObject_tcb)
  apply (clarsimp simp: tcb_cte_cases_def)
  done

lemma cte_wp_at_obj_cases_mask:
  "cte_wp_at' P p s =
       (obj_at' P p s \<or>
          (p && mask tcbBlockSizeBits \<in> dom tcb_cte_cases
             \<and> obj_at' (P \<circ> fst (the (tcb_cte_cases (p && mask tcbBlockSizeBits))))
                     (p && ~~ mask tcbBlockSizeBits) s))"
  apply (simp add: cte_wp_at_obj_cases')
  apply (rule arg_cong [where f="\<lambda>x. F \<or> x" for F])
  apply (rule iffI)
   apply (clarsimp simp: obj_at'_def projectKOs objBits_simps)
   apply (frule(1) tcb_cte_cases_aligned_helpers)
   apply fastforce
  apply (clarsimp simp: obj_at'_def projectKOs objBits_simps)
  apply (rule bexI[where x="p && mask tcbBlockSizeBits"])
   apply (clarsimp simp: subtract_mask)
  apply fastforce
  done

lemma ps_clearD:
  "\<lbrakk> ps_clear x n s; ksPSpace s y = Some v; x < y; y \<le> x + 2 ^ n - 1 \<rbrakk> \<Longrightarrow> False"
  apply (clarsimp simp: ps_clear_def)
  apply (drule_tac a=y in equals0D)
  apply (simp add: dom_def)
  apply fastforce
  done

lemma cte_wp_at_retype':
  assumes ko: "makeObjectKO dev tp = Some obj"
      and pv: "pspace_aligned' s" "pspace_distinct' s"
     and pv': "pspace_aligned' (ksPSpace_update (\<lambda>x xa. if xa \<in> set addrs then Some obj else ksPSpace s xa) s)"
              "pspace_distinct' (ksPSpace_update (\<lambda>x xa. if xa \<in> set addrs then Some obj else ksPSpace s xa) s)"
      and al: "\<forall>x \<in> set addrs. is_aligned x (objBitsKO obj)"
      and pn: "\<forall>x \<in> set addrs. ksPSpace s x = None"
   shows
  "cte_wp_at' P p (ksPSpace_update (\<lambda>x xa. if xa \<in> set addrs then Some obj else ksPSpace s xa) s)
      = (if tp = Inr (APIObjectType ArchTypes_H.CapTableObject) \<and> p \<in> set addrs
           \<or> tp = Inr (APIObjectType ArchTypes_H.TCBObject)
                         \<and> (p && ~~ mask tcbBlockSizeBits \<in> set addrs) \<and> (p && mask tcbBlockSizeBits \<in> dom tcb_cte_cases)
              then P (CTE NullCap nullMDBNode)
              else cte_wp_at' P p s)"
  (is "cte_wp_at' P p ?s' = ?Q")
  apply (subgoal_tac "\<forall>p \<in> set addrs. \<forall>(P :: cte \<Rightarrow> bool). \<not> obj_at' P p s")
   apply (subgoal_tac "\<forall>p \<in> set addrs. \<forall>(P :: tcb \<Rightarrow> bool). \<not> obj_at' P p s")
    apply (subgoal_tac "(\<exists>P :: cte \<Rightarrow> bool. obj_at' P p ?s')
                          \<longrightarrow> (\<not> (\<exists>P :: tcb \<Rightarrow> bool. obj_at' P (p && ~~ mask tcbBlockSizeBits) ?s'))")
     apply (simp only: cte_wp_at_obj_cases_mask foldr_update_obj_at'[OF pv pv' al])
     apply (simp    add: projectKOs the_ctes_makeObject
                         makeObjectKO_eq [OF ko]
                         makeObject_cte dom_def
              split del: if_split
                   cong: if_cong)
     apply (insert al ko)
     apply (simp, safe, simp_all)
      apply fastforce
     apply fastforce
    apply (clarsimp elim!: obj_atE' simp: projectKOs objBits_simps)
    apply (drule ps_clearD[where y=p and n=tcbBlockSizeBits])
       apply simp
      apply (rule order_trans_rules(17))
       apply (clarsimp cong: if_cong)
      apply (rule word_and_le2)
     apply (simp add: word_le_mask_out_plus_2sz)
    apply simp
   apply (clarsimp elim!: obj_atE' simp: pn)
  apply (clarsimp elim!: obj_atE' simp: pn)
  done

lemma ctes_of_retype:
  assumes ko: "makeObjectKO dev tp = Some obj"
      and pv: "pspace_aligned' s" "pspace_distinct' s"
     and pv': "pspace_aligned' (ksPSpace_update (\<lambda>x xa. if xa \<in> set addrs then Some obj else ksPSpace s xa) s)"
              "pspace_distinct' (ksPSpace_update (\<lambda>x xa. if xa \<in> set addrs then Some obj else ksPSpace s xa) s)"
      and al: "\<forall>x \<in> set addrs. is_aligned x (objBitsKO obj)"
      and pn: "\<forall>x \<in> set addrs. ksPSpace s x = None"
   shows
  "map_to_ctes (\<lambda> xa. if xa \<in> set addrs then Some obj else ksPSpace s xa)
      = (\<lambda>x. if tp = Inr (APIObjectType ArchTypes_H.CapTableObject) \<and> x \<in> set addrs
              \<or> tp = Inr (APIObjectType ArchTypes_H.TCBObject)
                         \<and> (x && ~~ mask tcbBlockSizeBits \<in> set addrs) \<and> (x && mask tcbBlockSizeBits \<in> dom tcb_cte_cases)
             then Some (CTE NullCap nullMDBNode)
             else map_to_ctes (ksPSpace s) x)"
  (is "map_to_ctes ?ps' = ?map'")
  using cte_wp_at_retype' [where P="(=) cte" for cte, OF ko pv pv' al pn]
        arg_cong [where f=Not, OF cte_wp_at_retype' [OF ko pv pv' al pn, where P="\<top>"]]
  apply (simp(no_asm_use) add: cte_wp_at_ctes_of cong: if_cong)
  apply (rule ext)
  apply (case_tac "map_to_ctes ?ps' x")
   apply (simp(no_asm_simp))
   apply (simp split: if_split_asm)
  apply simp
  done

lemma None_ctes_of_cte_at:
  "(None = ctes_of s x) = (\<not> cte_at' x s)"
  by (fastforce simp add: cte_wp_at_ctes_of)

lemma null_filter_ctes_retype:
  assumes ko: "makeObjectKO dev tp = Some obj"
      and pv: "pspace_aligned' s" "pspace_distinct' s"
     and pv': "pspace_aligned' (ksPSpace_update (\<lambda>x xa. if xa \<in> set addrs then Some obj else ksPSpace s xa) s)"
              "pspace_distinct' (ksPSpace_update (\<lambda>x xa. if xa \<in> set addrs then Some obj else ksPSpace s xa) s)"
      and al: "\<forall>x \<in> set addrs. is_aligned x (objBitsKO obj)"
      and pn: "\<forall>x \<in> set addrs. ksPSpace s x = None"
  shows
  "null_filter' (map_to_ctes (foldr (\<lambda>addr. data_map_insert addr obj) addrs (ksPSpace s)))
    = null_filter' (map_to_ctes (ksPSpace s))"
  apply (subst foldr_upd_app_if[folded data_map_insert_def])
  apply (subst ctes_of_retype[OF ko pv pv' al pn])
  apply (rule ext)
  apply (clarsimp simp: null_filter'_def None_ctes_of_cte_at)
  apply (intro conjI impI notI)
   apply (elim cte_wp_atE' disjE conjE)
    apply (simp_all add: pn)
   apply (cut_tac x="ptr'" and v="if ptr' \<in> set addrs then obj else KOTCB tcb"
                in pspace_distinctD'[OF _ pv'(2)])[1]
    apply simp
   apply (insert ko[symmetric],
          simp add: makeObjectKO_def objBits_simps pn
             split: if_split_asm)[1]
   apply (drule(2) tcb_ctes_clear[where s="ksPSpace_update f s" for f s])
    apply simp
   apply fastforce
  apply (cut_tac x="x && ~~ mask tcbBlockSizeBits" in pspace_distinctD'[OF _ pv'(2)])[1]
   apply simp
  apply (elim cte_wp_atE' disjE conjE)
   apply (insert ko[symmetric], simp add: makeObjectKO_def objBits_simps)
   apply clarsimp
   apply (subst(asm) subtract_mask[symmetric],
          erule_tac v="if x \<in> set addrs then KOTCB makeObject else KOCTE cte"
                in tcb_space_clear)
       apply (simp add: is_aligned_mask word_bw_assocs)
      apply assumption
     apply simp
    apply simp
   apply (simp add: pn)
  apply (clarsimp simp: makeObjectKO_def)
  apply (drule(1) tcb_cte_cases_aligned_helpers)
  apply (clarsimp simp: pn)
  done

lemma new_cap_addrs_aligned:
  "\<lbrakk> is_aligned ptr (objBitsKO ko) \<rbrakk>
    \<Longrightarrow> \<forall>x \<in> set (new_cap_addrs n ptr ko). is_aligned x (objBitsKO ko)"
  apply (clarsimp simp: new_cap_addrs_def)
  apply (erule aligned_add_aligned[OF _ is_aligned_shift])
  apply simp
  done

lemma new_cap_addrs_distinct:
  assumes cover: "range_cover ptr sz (objBitsKO ko) n"
  shows "distinct (new_cap_addrs n ptr ko)"
  unfolding new_cap_addrs_def
  apply (simp add: distinct_map)
  apply (rule comp_inj_on[where f=of_nat, unfolded o_def])
   apply (rule subset_inj_on)
    apply (rule word_unat.Abs_inj_on)
   apply (clarsimp simp only: unats_def atLeastLessThan_iff
                  dest!: less_two_pow_divD)
   apply (insert cover)
   apply (erule less_le_trans)
   apply (insert range_cover.range_cover_n_le[OF cover])
   apply (erule le_trans)
   apply (cases "objBitsKO ko = 0")
    apply (simp add:word_bits_def)
   apply (rule less_imp_le)
    apply (rule power_strict_increasing)
    apply (simp add:word_bits_def)
   apply simp
  apply (rule inj_onI)
  apply clarsimp
  apply (drule arg_cong[where f="\<lambda>x. x >> objBitsKO ko"])
  apply (cases "objBitsKO ko = 0")
   apply simp
  apply (subst(asm) shiftl_shiftr_id, simp add: range_cover_def)
   apply (subst word_unat_power, rule of_nat_mono_maybe)
    apply (rule power_strict_increasing)
     apply (simp add: word_bits_def)
    apply simp
   apply (erule order_less_le_trans)
   apply simp
  apply (subst(asm) shiftl_shiftr_id, simp add: range_cover_def)
   apply (subst word_unat_power, rule of_nat_mono_maybe)
    apply (rule power_strict_increasing)
     apply (simp add: word_bits_def)
    apply simp
   apply (erule order_less_le_trans)
   apply simp
  apply assumption
  done

lemma new_cap_addrs_subset:
  assumes range_cover:"range_cover ptr sz (objBitsKO ko) n"
  shows "set (new_cap_addrs n ptr ko) \<subseteq> {ptr .. ptr_add (ptr && ~~ mask sz) (2 ^ sz - 1)}"
  apply (clarsimp simp add: new_cap_addrs_def shiftl_t2n
                            field_simps
                     dest!: less_two_pow_divD)
  apply (intro conjI)
  apply (insert range_cover)
  apply (rule machine_word_plus_mono_right_split[OF range_cover.range_cover_compare])
    apply assumption
    apply simp
    apply (simp add:range_cover_def word_bits_def)
  apply (clarsimp simp:ptr_add_def)
  apply (subst word_plus_and_or_coroll2[symmetric,where w = "mask sz"])
  apply (subst add.commute)
  apply (subst add.assoc)
  apply (rule word_plus_mono_right)
  apply (drule(1) range_cover.range_cover_compare)
  apply (rule iffD1[OF le_m1_iff_lt,THEN iffD2])
    using range_cover
    apply (simp add: p2_gt_0 range_cover_def word_bits_def)
   apply (rule iffD2[OF word_less_nat_alt])
   apply (rule le_less_trans[OF unat_plus_gt])
   using range_cover
   apply (clarsimp simp: range_cover_def)
  apply (insert range_cover)
  apply (rule is_aligned_no_wrap'[OF is_aligned_neg_mask,OF le_refl ])
   apply (simp add:range_cover_def)+
done

definition
  obj_relation_retype :: "Structures_A.kernel_object \<Rightarrow>
                            Structures_H.kernel_object \<Rightarrow> bool"
where
 "obj_relation_retype ko ko' \<equiv>
   obj_bits ko \<ge> objBitsKO ko'
    \<and> (\<forall>p. fst ` obj_relation_cuts ko p
             = {p + x * 2 ^ (objBitsKO ko') | x. x < 2 ^ (obj_bits ko - objBitsKO ko')}
              \<and> (\<forall>x \<in> obj_relation_cuts ko p. snd x ko ko'))"

lemma obj_relation_retype_cutsD:
  "\<lbrakk> (x, P) \<in> obj_relation_cuts ko p; obj_relation_retype ko ko' \<rbrakk>
      \<Longrightarrow> \<exists>y. x = p + y * 2 ^ (objBitsKO ko') \<and> y < 2 ^ (obj_bits ko - objBitsKO ko')
                 \<and> P ko ko'"
  apply (clarsimp simp: obj_relation_retype_def)
  apply (drule spec[where x=p])
  apply clarsimp
  apply (drule(1) bspec)
  apply (drule arg_cong[where f="\<lambda>S. x \<in> S"])
  apply clarsimp
  apply (fastforce simp: image_def)
  done

lemma APIType_map2_Untyped[simp]:
  "(APIType_map2 tp = Structures_A.Untyped)
        = (tp = Inr (APIObjectType ArchTypes_H.Untyped))"
 by (simp add: APIType_map2_def
         split: sum.split object_type.split kernel_object.split arch_kernel_object.splits
                apiobject_type.split)

lemma obj_relation_retype_leD:
  "\<lbrakk> obj_relation_retype ko ko' \<rbrakk>
      \<Longrightarrow> objBitsKO ko' \<le> obj_bits ko"
  by (simp add: obj_relation_retype_def)

lemma obj_relation_retype_default_leD:
  "\<lbrakk> obj_relation_retype (default_object (APIType_map2 ty) dev us) ko;
       ty \<noteq> Inr (APIObjectType ArchTypes_H.Untyped) \<rbrakk>
      \<Longrightarrow> objBitsKO ko \<le> obj_bits_api (APIType_map2 ty) us"
  by (simp add: obj_relation_retype_def objBits_def obj_bits_dev_irr)

lemma makeObjectKO_Untyped:
  "makeObjectKO dev ty = Some v \<Longrightarrow> ty \<noteq> Inr (APIObjectType ArchTypes_H.Untyped)"
  by (clarsimp simp: makeObjectKO_def)

lemma obj_relation_cuts_trivial:
  "ptr \<in> fst ` obj_relation_cuts x ptr"
  apply (case_tac x)
      apply (rename_tac sz cs)
      apply (clarsimp simp:image_def cte_map_def well_formed_cnode_n_def)
      apply (rule_tac x = "replicate sz False" in exI)
      apply clarsimp+
  apply (rename_tac arch_kernel_obj)
  apply (case_tac arch_kernel_obj)
     apply clarsimp
    apply (simp_all add:image_def pageBits_def)
    apply (rule_tac x = 0 in exI, simp)+
  apply (rule p2_gt_0[THEN iffD2])
  apply (rename_tac vmpage_size)
  apply (case_tac vmpage_size)
     apply (clarsimp simp:pageBitsForSize_def)+
  done

lemma obj_relation_retype_addrs_eq:
  assumes not_unt:"ty \<noteq> Inr (APIObjectType ArchTypes_H.Untyped)"
  assumes  amp: "m = 2^ ((obj_bits_api (APIType_map2 ty) us) - (objBitsKO ko)) * n"
  assumes  orr: "obj_relation_retype (default_object (APIType_map2 ty) dev us) ko"
  shows  "\<lbrakk> range_cover ptr sz (obj_bits_api (APIType_map2 ty) us) n \<rbrakk> \<Longrightarrow>
   (\<Union>x \<in> set (retype_addrs ptr (APIType_map2 ty) n us).
            fst ` obj_relation_cuts (default_object (APIType_map2 ty) dev us) x)
      = set (new_cap_addrs m ptr ko)"
  apply (rule set_eqI, rule iffI)
   apply (clarsimp simp: retype_addrs_def)
  apply (rename_tac p a b)
   apply (drule obj_relation_retype_cutsD[OF _ orr])
   apply (cut_tac obj_relation_retype_default_leD[OF orr not_unt])
   apply (clarsimp simp: new_cap_addrs_def image_def
                  dest!: less_two_pow_divD)
   apply (rule_tac x="p * 2 ^ (obj_bits_api (APIType_map2 ty) us - objBitsKO ko) + unat y"
                 in rev_bexI)
    apply (simp add: amp obj_bits_api_default_object not_unt obj_bits_dev_irr)
    apply (rule less_le_trans[OF nat_add_left_cancel_less[THEN iffD2]])
    apply (erule unat_mono)
      apply (subst unat_power_lower)
      apply (rule le_less_trans[OF diff_le_self])
      apply (clarsimp simp: range_cover_def
        split: Structures_A.apiobject_type.splits)
    apply (simp add:field_simps,subst mult_Suc[symmetric])
    apply (rule mult_le_mono1)
      apply simp
   apply (simp add: ptr_add_def shiftl_t2n field_simps
                    objBits_def[symmetric] word_unat_power[symmetric])
   apply (simp add: power_add[symmetric])
  apply (clarsimp simp: new_cap_addrs_def retype_addrs_def
                 dest!: less_two_pow_divD)
  apply (rename_tac p)
  apply (cut_tac obj_relation_retype_default_leD[OF orr not_unt])
  apply (cut_tac obj_relation_retype_leD[OF orr])
  apply (case_tac "n = 0")
    apply (simp add:amp)
  apply (case_tac "p = 0")
    apply simp
    apply (rule_tac x = 0 in rev_bexI)
    apply simp+
    apply (rule obj_relation_cuts_trivial)
  apply (rule_tac x="p div (2 ^ (obj_bits_api (APIType_map2 ty) us - objBitsKO ko))"
           in rev_bexI)
   apply (simp add:amp)
   apply (rule td_gal_lt[THEN iffD1])
     apply (simp add:field_simps)+
  using orr
  apply (clarsimp simp: obj_relation_retype_def ptr_add_def)
  apply (thin_tac "\<forall>x. P x" for P)
  apply (rule_tac x="of_nat (p mod (2 ^ (obj_bits_api (APIType_map2 ty) us - objBitsKO ko)))" in exI)
  apply (simp only: word_unat_power Abs_fnat_homs shiftl_t2n)
  apply (rule conjI)
   apply (rule arg_cong[where f=of_nat])
   apply (subst mult_div_rearrange)
     apply simp
   apply (subst minus_mod_eq_mult_div[symmetric])
     apply (simp add:diff_mult_distrib2)
  apply (rule of_nat_mono_maybe)
   apply (rule power_strict_increasing)
   apply (rule le_less_trans[OF diff_le_self])
  apply (clarsimp simp: range_cover_def obj_bits_api_default_object obj_bits_dev_irr
                        not_unt word_bits_def)+
done

lemma objBits_le_obj_bits_api:
  "makeObjectKO dev ty = Some ko \<Longrightarrow>
   objBitsKO ko \<le> obj_bits_api (APIType_map2 ty) us"
  apply (case_tac ty)
    apply (auto simp: default_arch_object_def vspace_bits_defs vcpu_bits_def archObjSize_def
                      makeObjectKO_def objBits_simps' APIType_map2_def obj_bits_api_def slot_bits_def
               split: Structures_H.kernel_object.splits arch_kernel_object.splits object_type.splits
                      Structures_H.kernel_object.splits arch_kernel_object.splits apiobject_type.splits)
  done


lemma obj_relation_retype_other_obj:
  "\<lbrakk> is_other_obj_relation_type (a_type ko); other_obj_relation ko ko' \<rbrakk>
      \<Longrightarrow> obj_relation_retype ko ko'"
  apply (simp add: obj_relation_retype_def)
  apply (subgoal_tac "objBitsKO ko' = obj_bits ko")
   apply (clarsimp simp: is_other_obj_relation_type)
  apply (fastforce simp: other_obj_relation_def objBits_simps' archObjSize_def
                  split: Structures_A.kernel_object.split_asm
                         Structures_H.kernel_object.split_asm
                         Structures_H.kernel_object.split
                         arch_kernel_obj.split_asm arch_kernel_object.split)
  done

lemma retype_pspace_relation:
  assumes  sr: "pspace_relation (kheap s) (ksPSpace s')"
      and  vs: "valid_pspace s" "valid_mdb s"
      and vs': "pspace_aligned' s'" "pspace_distinct' s'"
      and  pn: "pspace_no_overlap_range_cover ptr sz s"
      and pn': "pspace_no_overlap' ptr sz s'"
      and  ko: "makeObjectKO dev ty = Some ko"
      and cover: "range_cover ptr sz (obj_bits_api (APIType_map2 ty) us) n"
      and orr: "obj_relation_retype (default_object (APIType_map2 ty) dev us) ko"
      and num_r: "m = 2 ^ (obj_bits_api (APIType_map2 ty) us - objBitsKO ko) * n"
  shows
  "pspace_relation (foldr (\<lambda>p ps. ps(p \<mapsto> default_object (APIType_map2 ty) dev us))
                              (retype_addrs ptr (APIType_map2 ty) n us) (kheap s))
            (foldr (\<lambda>addr. data_map_insert addr ko) (new_cap_addrs m ptr ko) (ksPSpace s'))"
  (is "pspace_relation ?ps ?ps'")
  unfolding pspace_relation_def
proof
  have not_unt: "ty \<noteq> Inr (APIObjectType ArchTypes_H.Untyped)"
     by (rule makeObjectKO_Untyped[OF ko])

  have dom_not_ra:
    "\<forall>x \<in> dom (kheap s). x \<notin> set (retype_addrs ptr (APIType_map2 ty) n us)"
    apply clarsimp
    apply (erule(1) pspace_no_overlapC[OF pn _ _ cover vs(1)])
    done

  hence dom_Int_ra:
    "set (retype_addrs ptr (APIType_map2 ty) n us) \<inter> dom (kheap s) = {}"
    by auto

  note pdom = pspace_dom_upd [OF dom_Int_ra, where ko="default_object (APIType_map2 ty) dev us"]

  have pdom': "dom ?ps' = dom (ksPSpace s') \<union> set (new_cap_addrs m ptr ko)"
    by (clarsimp simp add: foldr_upd_app_if[folded data_map_insert_def]
                           dom_if_Some Un_commute
                split del: if_split)

  note not_unt = makeObjectKO_Untyped [OF ko]

  have "pspace_dom (kheap s) = dom (ksPSpace s')"
    using sr by (simp add: pspace_relation_def)

  thus "pspace_dom ?ps = dom ?ps'"
    apply (simp add: pdom pdom')
    apply (rule arg_cong[where f="\<lambda>T. S \<union> T" for S])
    apply (rule obj_relation_retype_addrs_eq[OF not_unt num_r orr cover])
    done

  have dom_same:
    "\<And>x v. kheap s x = Some v \<Longrightarrow> ?ps x = Some v"
    apply (frule bspec [OF dom_not_ra, OF domI])
    apply (simp add: foldr_upd_app_if)
    done
  have cover':"range_cover ptr sz (objBitsKO ko) m"
    by (rule range_cover_rel[OF cover objBits_le_obj_bits_api[OF ko] num_r])
  have dom_same':
    "\<And>x v. ksPSpace s' x = Some v \<Longrightarrow> ?ps' x = Some v"
    apply (clarsimp simp:foldr_upd_app_if[folded data_map_insert_def])
    apply (drule domI[where m = "ksPSpace s'"])
    apply (drule(1) IntI)
    apply (erule_tac A = "A \<inter> B" for A B in in_emptyE[rotated])
    apply (rule disjoint_subset[OF new_cap_addrs_subset[OF cover']])
    apply (clarsimp simp:ptr_add_def field_simps)
    apply (rule pspace_no_overlap_disjoint'[OF vs'(1) pn'])
  done

  show "\<forall>x \<in> dom ?ps. \<forall>(y, P) \<in> obj_relation_cuts (the (?ps x)) x.
                   P (the (?ps x)) (the (?ps' y))"
    using sr
    apply (clarsimp simp: pspace_relation_def)
    apply (simp add: foldr_upd_app_if split: if_split_asm)
     apply (clarsimp simp: foldr_upd_app_if[folded data_map_insert_def])
     apply (rule conjI)
      apply (drule obj_relation_retype_cutsD [OF _ orr], clarsimp)
     apply (rule impI, erule notE)
     apply (simp add: obj_relation_retype_addrs_eq[OF not_unt num_r orr cover,symmetric])
     apply (erule rev_bexI)
     apply (simp add: image_def)
     apply (erule rev_bexI, simp)
    apply (drule bspec, erule domI)
    apply clarsimp
    apply (drule(1) bspec, simp)
    apply (subgoal_tac "a \<in> pspace_dom (kheap s)")
     apply clarsimp
     apply (frule dom_same', simp)
    apply (simp(no_asm) add: pspace_dom_def)
    apply (rule rev_bexI, erule domI)
    apply (simp add: image_def)
    apply (erule rev_bexI, simp)
    done
qed


(*Clagged from Retype_AC*)
lemma foldr_upd_app_if': "foldr (\<lambda>p ps. ps(p := f p)) as g = (\<lambda>x. if x \<in> set as then (f x) else g x)"
  apply (induct as)
   apply simp
  apply simp
  apply (rule ext)
  apply simp
  done

lemma etcb_rel_makeObject: "etcb_relation default_etcb makeObject"
  apply (simp add: etcb_relation_def default_etcb_def)
  apply (simp add: makeObject_tcb default_priority_def default_domain_def)
  done


lemma ekh_at_tcb_at: "valid_etcbs_2 ekh kh \<Longrightarrow> ekh x = Some y  \<Longrightarrow> \<exists>tcb. kh x = Some (TCB tcb)"
  apply (simp add: valid_etcbs_2_def
                   st_tcb_at_kh_def obj_at_kh_def
                   is_etcb_at'_def obj_at_def)
  apply force
  done

lemma default_etcb_default_domain_futz [simp]:
  "default_etcb\<lparr>tcb_domain := default_domain\<rparr> = default_etcb"
unfolding default_etcb_def by simp

lemma retype_ekheap_relation:
  assumes  sr: "ekheap_relation (ekheap s) (ksPSpace s')"
      and  sr': "pspace_relation (kheap s) (ksPSpace s')"
      and  vs: "valid_pspace s" "valid_mdb s"
      and et: "valid_etcbs s"
      and vs': "pspace_aligned' s'" "pspace_distinct' s'"
      and  pn: "pspace_no_overlap_range_cover ptr sz s"
      and pn': "pspace_no_overlap' ptr sz s'"
      and  ko: "makeObjectKO dev ty = Some ko"
      and cover: "range_cover ptr sz (obj_bits_api (APIType_map2 ty) us) n"
      and orr: "obj_relation_retype (default_object (APIType_map2 ty) dev us) ko"
      and num_r: "m = 2 ^ (obj_bits_api (APIType_map2 ty) us - objBitsKO ko) * n"
  shows
  "ekheap_relation (foldr (\<lambda>p ps. ps(p := default_ext (APIType_map2 ty) default_domain))
                              (retype_addrs ptr (APIType_map2 ty) n us) (ekheap s))
            (foldr (\<lambda>addr. data_map_insert addr ko) (new_cap_addrs m ptr ko) (ksPSpace s'))"
  (is "ekheap_relation ?ps ?ps'")
  proof -
  have not_unt: "ty \<noteq> Inr (APIObjectType ArchTypes_H.Untyped)"
     by (rule makeObjectKO_Untyped[OF ko])
  show ?thesis
    apply (case_tac "ty \<noteq> Inr (APIObjectType apiobject_type.TCBObject)")
     apply (insert ko)
     apply (cut_tac retype_pspace_relation[OF sr' vs vs' pn pn' ko cover orr num_r])
     apply (simp add: foldr_upd_app_if' foldr_upd_app_if[folded data_map_insert_def])
     apply (simp add: obj_relation_retype_addrs_eq[OF not_unt num_r orr cover,symmetric])
     apply (insert sr)
     apply (clarsimp simp add: ekheap_relation_def
                      pspace_relation_def default_ext_def cong: if_cong
                      split: if_split_asm)
      subgoal by (clarsimp simp add: makeObjectKO_def APIType_map2_def cong: if_cong
                              split: sum.splits Structures_H.kernel_object.splits
                                     arch_kernel_object.splits ARM_HYP_H.object_type.splits apiobject_type.splits)

     apply (frule ekh_at_tcb_at[OF et])
     apply (intro impI conjI)
      apply clarsimp
      apply (drule_tac x=a in bspec,force)
      apply (clarsimp simp add: other_obj_relation_def split: if_split_asm)
       apply (case_tac ko,simp_all)
       apply (clarsimp simp add: makeObjectKO_def cong: if_cong split: sum.splits Structures_H.kernel_object.splits
                                 arch_kernel_object.splits ARM_HYP_H.object_type.splits
                                 apiobject_type.splits if_split_asm)
      apply (drule_tac x=xa in bspec,simp)
      subgoal by force
     subgoal by force
    apply (simp add: foldr_upd_app_if' foldr_upd_app_if[folded data_map_insert_def])
    apply (simp add: obj_relation_retype_addrs_eq[OF not_unt num_r orr cover,symmetric])
    apply (clarsimp simp add: APIType_map2_def default_ext_def ekheap_relation_def
           default_object_def makeObjectKO_def etcb_rel_makeObject
           cong: if_cong
           split: if_split_asm)
    apply force
  done
qed

lemma pspace_no_overlapD':
  "\<lbrakk> ksPSpace s x = Some ko; pspace_no_overlap' p bits s \<rbrakk>
       \<Longrightarrow> {x .. x + 2 ^ objBitsKO ko - 1} \<inter> {p .. (p && ~~ mask bits) + 2 ^ bits - 1} = {}"
  apply (simp add:pspace_no_overlap'_def)
  apply (intro impI)
  apply (elim allE impE)
  apply (simp add:field_simps)+
done

lemma new_range_subset:
  assumes
        cover: "range_cover ptr sz (objBitsKO ko) n"
    and addr: "x \<in> set (new_cap_addrs n ptr ko)"
  shows       "{x .. x + 2 ^ (objBitsKO ko) - 1} \<subseteq> {ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1}"
  (is "?lhs \<subseteq> ?rhs")
proof -
  have base_in: "x \<in> {ptr..ptr_add (ptr && ~~ mask sz) (2 ^ sz - 1)}"
    by (rule set_mp[OF new_cap_addrs_subset[OF cover] addr])
  have aligned: "is_aligned x (objBitsKO ko)"
    apply (insert cover)
    apply (clarsimp simp:range_cover_def)
    apply (drule new_cap_addrs_aligned)
    apply (erule bspec[OF _ addr])
  done
  show ?thesis using base_in aligned addr
    apply (intro range_subsetI)
    apply (clarsimp simp:ptr_add_def field_simps)+
    apply (simp add:x_power_minus_1)
    apply (clarsimp simp:new_cap_addrs_def)
   apply (subst word_plus_and_or_coroll2[symmetric,where w = "mask sz"])
   apply (subst add.commute)
  apply (subst add.assoc)
  apply (subst add.assoc)
  apply (rule word_plus_mono_right)
  apply (simp add:mask_2pm1[symmetric])
    apply (rule iffD2[OF shiftr_mask_cmp[where c = "objBitsKO ko"]])
    apply (insert cover)
      apply (simp add:range_cover_def)
    apply (simp add:range_cover_def word_bits_def)
       apply (subst aligned_shift')
      apply (simp add:mask_lt_2pn range_cover_def word_bits_def )
     apply (drule is_aligned_addD1)
      apply (simp add:range_cover_def)
     apply (rule aligned_add_aligned)
       apply (rule aligned_already_mask)
       apply (fastforce simp:range_cover_def)
      apply (simp_all add: range_cover_def)[3]
   apply (subst shiftr_mask2[symmetric])
    apply (simp add:range_cover_def word_bits_def)
   apply (rule le_shiftr)
   apply (subst le_mask_iff_lt_2n[THEN iffD1])
    apply (simp add:range_cover_def word_bits_def)
   apply (clarsimp simp:word_less_nat_alt)
   apply (rule le_less_trans[OF unat_plus_gt])
   apply (frule(1) range_cover.range_cover_compare)
   apply (clarsimp simp:shiftl_t2n mult.commute range_cover_def)
  apply (rule is_aligned_no_wrap'[OF is_aligned_neg_mask])
    apply (rule le_refl)
   apply (simp add:range_cover_def)
  done
qed

lemma retype_aligned_distinct':
  assumes vs': "pspace_aligned' s'" "pspace_distinct' s'"
      and pn': "pspace_no_overlap' ptr sz s'"
      and cover: "range_cover ptr sz (objBitsKO ko) n "
  shows
  "pspace_distinct' (s' \<lparr>ksPSpace := foldr (\<lambda>addr. data_map_insert addr ko)
                                             (new_cap_addrs n ptr ko) (ksPSpace s')\<rparr>)"
  "pspace_aligned' (s' \<lparr>ksPSpace := foldr (\<lambda>addr. data_map_insert addr ko)
                                             (new_cap_addrs n ptr ko) (ksPSpace s')\<rparr>)"
  (is "pspace_aligned' (s'\<lparr>ksPSpace := ?ps\<rparr>)")
proof -
  have al: "is_aligned ptr (objBitsKO ko)"
    using cover
    by (simp add:cover range_cover_def)
  let ?s' = "s'\<lparr>ksPSpace := ?ps\<rparr>"
  note nc_al = bspec [OF new_cap_addrs_aligned [OF al]]
  note nc_al' = nc_al[unfolded objBits_def]

  show pa': "pspace_aligned' ?s'" using vs'(1)
    apply (subst foldr_upd_app_if[folded data_map_insert_def])
    apply (clarsimp simp add: pspace_aligned'_def nc_al'
                       split: if_split_asm)
    apply (drule bspec, erule domI, simp)
    done

  have okov: "objBitsKO ko < word_bits"
    by (simp add: objBits_def)

  have new_range_disjoint:
    "\<And>x. x \<in> set (new_cap_addrs n ptr ko) \<Longrightarrow>
         ({x .. x + 2 ^ (objBitsKO ko) - 1} - {x}) \<inter> set (new_cap_addrs n ptr ko) = {}"
    apply safe
    apply (rule ccontr)
    apply (frule(2) aligned_neq_into_no_overlap [OF _ nc_al nc_al])
    apply (drule_tac a=xa in equals0D)
    apply (clarsimp simp: field_simps is_aligned_no_overflow [OF nc_al])
    done
  note new_range_sub = new_range_subset [OF cover]

  show pd': "pspace_distinct' ?s'" using vs'(2)
    apply (subst foldr_upd_app_if[folded data_map_insert_def])
    apply (simp add: pspace_distinct'_def dom_if_Some ball_Un)
    apply (intro conjI ballI impI)
      apply (simp add: ps_clear_def dom_if_Some Int_Un_distrib
                       objBits_def[symmetric])
      apply (rule conjI)
       apply (erule new_range_disjoint)
      apply (rule disjoint_subset[OF Diff_subset])
      apply (erule disjoint_subset[OF new_range_sub])
      apply (rule pspace_no_overlap_disjoint'[OF vs'(1) pn'])
    apply (clarsimp simp add: ps_clear_def dom_if_Some Int_Un_distrib)
    apply (rule conjI)
      apply (erule new_range_disjoint)
     apply (rule disjoint_subset[OF Diff_subset])
     apply (erule disjoint_subset[OF new_range_sub])
     apply (rule pspace_no_overlap_disjoint'[OF vs'(1) pn'])
    apply (clarsimp simp add: ps_clear_def dom_if_Some Int_Un_distrib)
    apply (subst Int_commute)
    apply (rule disjoint_subset[OF new_cap_addrs_subset,OF cover])
    apply (subst Int_commute)
    apply (simp add:ptr_add_def field_simps)
    apply (rule disjoint_subset[OF Diff_subset])
    apply (erule pspace_no_overlapD' [OF _ pn'])
    done
qed

definition
  update_gs :: "Structures_A.apiobject_type \<Rightarrow> nat \<Rightarrow> word32 set
                \<Rightarrow> 'a kernel_state_scheme \<Rightarrow> 'a kernel_state_scheme"
where
 "update_gs ty us ptrs \<equiv>
  case ty of
    Structures_A.CapTableObject \<Rightarrow> gsCNodes_update
      (\<lambda>cns x. if x \<in> ptrs then Some us else cns x)
  | ArchObject (SmallPageObj) \<Rightarrow> gsUserPages_update
      (\<lambda>ups x. if x \<in> ptrs then Some ARMSmallPage else ups x)
  | ArchObject (LargePageObj) \<Rightarrow> gsUserPages_update
      (\<lambda>ups x. if x \<in> ptrs then Some ARMLargePage else ups x)
  | ArchObject (SectionObj) \<Rightarrow> gsUserPages_update
      (\<lambda>ups x. if x \<in> ptrs then Some ARMSection else ups x)
  | ArchObject (SuperSectionObj) \<Rightarrow> gsUserPages_update
      (\<lambda>ups x. if x \<in> ptrs then Some ARMSuperSection else ups x)
  | _ \<Rightarrow> id"

lemma ksPSpace_update_gs_eq[simp]:
  "ksPSpace (update_gs ty us ptrs s) = ksPSpace s"
  by (simp add: update_gs_def
           split: Structures_A.apiobject_type.splits aobject_type.splits)

end

global_interpretation update_gs: PSpace_update_eq "update_gs ty us ptrs"
  by (simp add: PSpace_update_eq_def)

context begin interpretation Arch . (*FIXME: arch_split*)

lemma update_gs_id:
  "tp \<in> no_gs_types \<Longrightarrow> update_gs tp us addrs = id"
  by (simp add: no_gs_types_def update_gs_def
           split: Structures_A.apiobject_type.splits aobject_type.splits)

lemma update_gs_simps[simp]:
  "update_gs Structures_A.apiobject_type.CapTableObject us ptrs =
   gsCNodes_update (\<lambda>cns x. if x \<in> ptrs then Some us else cns x)"
  "update_gs (ArchObject SmallPageObj) us ptrs =
   gsUserPages_update (\<lambda>ups x. if x \<in> ptrs then Some ARMSmallPage else ups x)"
  "update_gs (ArchObject LargePageObj) us ptrs =
   gsUserPages_update (\<lambda>ups x. if x \<in> ptrs then Some ARMLargePage else ups x)"
  "update_gs (ArchObject SectionObj) us ptrs =
   gsUserPages_update (\<lambda>ups x. if x \<in> ptrs then Some ARMSection else ups x)"
  "update_gs (ArchObject SuperSectionObj) us ptrs =
   gsUserPages_update (\<lambda>ups x. if x \<in> ptrs then Some ARMSuperSection
                               else ups x)"
  by (simp_all add: update_gs_def)

lemma retype_state_relation:
  notes data_map_insert_def[simp del]
  assumes  sr:   "(s, s') \<in> state_relation"
      and  vs:   "valid_pspace s" "valid_mdb s"
      and  et:   "valid_etcbs s" "valid_list s"
      and vs':   "pspace_aligned' s'" "pspace_distinct' s'"
      and  pn:   "pspace_no_overlap_range_cover ptr sz s"
      and pn':   "pspace_no_overlap' ptr sz s'"
      and cover: "range_cover ptr sz (obj_bits_api (APIType_map2 ty) us) n"
      and  ko:   "makeObjectKO dev ty = Some ko"
      and api:   "obj_bits_api (APIType_map2 ty) us \<le> sz"
      and orr:   "obj_relation_retype (default_object (APIType_map2 ty) dev us) ko"
      and num_r: "m = 2 ^ (obj_bits_api (APIType_map2 ty) us - objBitsKO ko) * n"
  shows
  "(ekheap_update
              (\<lambda>_. foldr (\<lambda>p ekh a. if a = p then default_ext (APIType_map2 ty) default_domain else ekh a)
                    (retype_addrs ptr (APIType_map2 ty) n us) (ekheap s))
            s
           \<lparr>kheap :=
              foldr (\<lambda>p. data_map_insert p (default_object (APIType_map2 ty) dev us))
               (retype_addrs ptr (APIType_map2 ty) n us) (kheap s)\<rparr>,
           update_gs (APIType_map2 ty) us (set (retype_addrs ptr (APIType_map2 ty) n us))
            (s'\<lparr>ksPSpace :=
                  foldr (\<lambda>addr. data_map_insert addr ko) (new_cap_addrs m ptr ko)
                   (ksPSpace s')\<rparr>))
          \<in> state_relation"
  (is "(ekheap_update (\<lambda>_. ?eps) s\<lparr>kheap := ?ps\<rparr>, update_gs _ _ _ (s'\<lparr>ksPSpace := ?ps'\<rparr>))
       \<in> state_relation")
  proof (rule state_relation_null_filterE[OF sr refl _ _ _ _ _ _ _ vs'], simp_all add: trans_state_update[symmetric] del: trans_state_update)

  have cover':"range_cover ptr sz (objBitsKO ko) m"
    by (rule range_cover_rel[OF cover objBits_le_obj_bits_api[OF ko] num_r])
  have al':"is_aligned ptr (objBitsKO ko)"
    using cover'
    by (simp add:range_cover_def)
  have sz:"sz < word_bits"
    using cover'
    by (simp add:range_cover_def word_bits_def)
  let ?t = "s\<lparr>kheap := ?ps\<rparr>"
  let ?tp = "APIType_map2 ty"
  let ?al = "retype_addrs ptr ?tp n us"
  let ?t' = "update_gs ?tp us (set ?al) (s'\<lparr>ksPSpace := ?ps'\<rparr>)"

  note pad' = retype_aligned_distinct' [OF vs' pn' cover']
  thus pa': "pspace_aligned' (s'\<lparr>ksPSpace := ?ps'\<rparr>)"
   and pd': "pspace_distinct' (s'\<lparr>ksPSpace := ?ps'\<rparr>)"
    by simp_all

  note pa'' = pa'[simplified foldr_upd_app_if[folded data_map_insert_def]]
  note pd'' = pd'[simplified foldr_upd_app_if[folded data_map_insert_def]]

  note not_unt = makeObjectKO_Untyped [OF ko]
  show "null_filter (caps_of_state ?t) = null_filter (caps_of_state s)"
    apply (rule null_filter_caps_of_state_foldr[folded data_map_insert_def])
     apply (simp add: not_unt)
    apply (rule ballI)
    apply (erule pspace_no_overlapD2 [OF pn _ cover vs(1)])
    done

  have nc_dis: "distinct (new_cap_addrs m ptr ko)"
    by (rule new_cap_addrs_distinct [OF cover'])

  note nc_al = bspec [OF new_cap_addrs_aligned [OF al']]
  note nc_al' = nc_al[unfolded objBits_def]
  show "null_filter' (map_to_ctes ?ps') = null_filter' (ctes_of s')"
    apply (rule null_filter_ctes_retype [OF ko vs' pa'' pd''])
     apply (simp add: nc_al)
    apply clarsimp
    apply (drule subsetD [OF new_cap_addrs_subset [OF cover']])
    apply (insert pspace_no_overlap_disjoint'[OF vs'(1) pn'])
    apply (drule orthD1)
      apply (simp add:ptr_add_def field_simps)
    apply clarsimp
    done

  show "valid_objs s" using vs
    by (clarsimp simp: valid_pspace_def)

  show "valid_mdb s" using vs
    by (clarsimp)

  show "valid_list s" using et
    by (clarsimp)

  show "mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s)" using vs
    by (clarsimp simp: valid_mdb_def)

  have pspr: "pspace_relation (kheap s) (ksPSpace s')"
    using sr by (simp add: state_relation_def)

  thus "pspace_relation ?ps ?ps'"
    by (rule retype_pspace_relation [OF _ vs vs' pn pn' ko cover orr num_r,
        folded data_map_insert_def])

  have "ekheap_relation (ekheap (s)) (ksPSpace s')"
  using sr by (simp add: state_relation_def)

  thus "ekheap_relation ?eps ?ps'"
    by (fold fun_upd_apply) (rule retype_ekheap_relation[OF _ pspr vs et(1) vs' pn pn' ko cover orr num_r])

  have pn2: "\<forall>a\<in>set ?al. kheap s a = None"
    by (rule ccontr) (clarsimp simp: pspace_no_overlapD1[OF pn _ cover vs(1)])

  from sr have gr: "ghost_relation (kheap s) (gsUserPages s') (gsCNodes s')"
    by (rule state_relationE)

  show "ghost_relation ?ps (gsUserPages ?t') (gsCNodes ?t')"
  proof (cases ?tp)
    case Untyped thus ?thesis by (simp add: not_unt)
  next
  note data_map_insert_def[simp]

    case TCBObject
    from pn2
    have [simp]: "ups_of_heap ?ps = ups_of_heap (kheap s)"
      by - (rule ext, induct (?al),
            simp_all add: ups_of_heap_def default_object_def TCBObject)
    from pn2
    have [simp]: "cns_of_heap ?ps = cns_of_heap (kheap s)"
      by - (rule ext, induct (?al),
            simp_all add: cns_of_heap_def default_object_def TCBObject)
   note data_map_insert_def[simp del]
    from gr show ?thesis
      by (simp add: ghost_relation_of_heap, simp add: TCBObject update_gs_def)
  next
    case EndpointObject
    from pn2
    have [simp]: "ups_of_heap ?ps = ups_of_heap (kheap s)"
      by - (rule ext, induct (?al),
            simp_all add: ups_of_heap_def default_object_def data_map_insert_def EndpointObject)
    from pn2
    have [simp]: "cns_of_heap ?ps = cns_of_heap (kheap s)"
      by - (rule ext, induct (?al),
            simp_all add: cns_of_heap_def default_object_def data_map_insert_def EndpointObject)
    from gr show ?thesis
      by (simp add: ghost_relation_of_heap,
          simp add: EndpointObject update_gs_def)
  next
   note data_map_insert_def[simp]
    case NotificationObject
    from pn2
    have [simp]: "ups_of_heap ?ps = ups_of_heap (kheap s)"
      by - (rule ext, induct (?al), simp_all add: ups_of_heap_def
                                      default_object_def NotificationObject)
    from pn2
    have [simp]: "cns_of_heap ?ps = cns_of_heap (kheap s)"
      by - (rule ext, induct (?al), simp_all add: cns_of_heap_def
                                      default_object_def NotificationObject)
   note data_map_insert_def[simp del]
    from gr show ?thesis
      by (simp add: ghost_relation_of_heap,
          simp add: NotificationObject update_gs_def)
  next
    case CapTableObject
    note data_map_insert_def[simp]
    from pn2
    have [simp]: "ups_of_heap ?ps = ups_of_heap (kheap s)"
      by - (rule ext, induct (?al), simp_all add: ups_of_heap_def
                                      default_object_def CapTableObject)
    have [simp]: "cns_of_heap ?ps = (\<lambda>x. if x \<in> set ?al then Some us
                                         else cns_of_heap (kheap s) x)"
      by (rule ext, induct (?al),
          simp_all add: cns_of_heap_def wf_empty_bits wf_unique default_object_def CapTableObject)
    note data_map_insert_def[simp del]
    from gr show ?thesis
      by (simp add: ghost_relation_of_heap,
          simp add: CapTableObject update_gs_def ext)
  next
    case (ArchObject ao)
    from pn2
    have [simp]: "cns_of_heap ?ps = cns_of_heap (kheap s)"
      by - (rule ext, induct (?al), simp_all add: cns_of_heap_def data_map_insert_def
                                      default_object_def ArchObject)
    from pn2 gr show ?thesis
      apply (clarsimp simp add: ghost_relation_of_heap)
      apply (rule conjI[rotated])
       apply (simp add: ArchObject update_gs_def split: aobject_type.splits)
      apply (thin_tac "cns_of_heap h = g" for h g)
      apply (drule sym)
      apply (rule ext)
      apply (induct (?al))
       apply (simp add: update_gs_def ArchObject split: aobject_type.splits)
      apply (simp add: update_gs_def ArchObject default_object_def
                       default_arch_object_def ups_of_heap_def
                       data_map_insert_def
                split: aobject_type.splits)
      done
  qed

  show "\<exists>f' g' h'. ?t' =
          s'\<lparr>ksPSpace := f' (ksPSpace s'), gsUserPages := g' (gsUserPages s'),
             gsCNodes := h' (gsCNodes s')\<rparr>"
    apply (clarsimp simp: update_gs_def
                   split: Structures_A.apiobject_type.splits)
    apply (intro conjI impI)
         apply (subst ex_comm, rule_tac x=id in exI,
                subst ex_comm, rule_tac x=id in exI, fastforce)+
     apply (subst ex_comm, rule_tac x=id in exI)
     apply (subst ex_comm)
     apply (rule_tac x="\<lambda>cns x. if x\<in>set ?al then Some us else cns x" in exI,
            simp)
     apply (rule_tac x="\<lambda>x. foldr (\<lambda>addr. data_map_insert addr ko)
                                  (new_cap_addrs m ptr ko) x" in exI, simp)
    apply clarsimp
    apply (rule_tac x="\<lambda>x. foldr (\<lambda>addr. data_map_insert addr ko)
                                 (new_cap_addrs m ptr ko) x" in exI)
    apply (subst ex_comm, rule_tac x=id in exI)
    apply (simp split: aobject_type.splits)
    apply (intro conjI impI)
          apply (rule_tac x="\<lambda>cns x. if x \<in> set ?al then Some ARMSmallPage
                                     else cns x" in exI, simp)
         apply (rule_tac x="\<lambda>cns x. if x \<in> set ?al then Some ARMLargePage
                                    else cns x" in exI, simp)
        apply (rule_tac x="\<lambda>cns x. if x \<in> set ?al then Some ARMSection
                                   else cns x" in exI, simp)
       apply (rule_tac x="\<lambda>cns x. if x \<in> set ?al then Some ARMSuperSection
                                  else cns x" in exI, simp)
      apply (rule_tac x=id in exI, simp)+
    done
qed

lemma new_cap_addrs_fold':
  "1 \<le> n \<Longrightarrow>
   map (\<lambda>n. ptr + (n << objBitsKO ko)) [0.e.n - 1] =
   new_cap_addrs (unat n) ptr ko"
 by (clarsimp simp:new_cap_addrs_def ptr_add_def upto_enum_red'
           shiftl_t2n power_add field_simps)

lemma objBitsKO_gt_0: "0 < objBitsKO ko"
  apply (case_tac ko)
        apply (simp_all add:objBits_simps' pageBits_def)
  apply (rename_tac arch_kernel_object)
  apply (case_tac arch_kernel_object)
    apply (simp_all add:archObjSize_def vcpu_bits_def vspace_bits_defs)
  done

lemma kheap_ekheap_double_gets:
  "(\<And>rv erv rv'. \<lbrakk>pspace_relation rv rv'; ekheap_relation erv rv'\<rbrakk>
                 \<Longrightarrow> corres r (R rv erv) (R' rv') (b rv erv) (d rv')) \<Longrightarrow>
   corres r (\<lambda>s. R (kheap s) (ekheap s) s) (\<lambda>s. R' (ksPSpace s) s)
          (do x \<leftarrow> gets kheap; xa \<leftarrow> gets ekheap; b x xa od) (gets ksPSpace >>= d)"
  apply (rule corres_symb_exec_l)
     apply (rule corres_guard_imp)
       apply (rule_tac r'= "\<lambda>erv rv'. ekheap_relation erv rv' \<and> pspace_relation x rv'"
               in corres_split)
          apply (subst corres_gets[where P="\<lambda>s. x = kheap s" and P'=\<top>])
          apply clarsimp
          apply (simp add: state_relation_def)
         apply clarsimp
         apply assumption
        apply (wp gets_exs_valid | simp)+
  done

(*

Split out the extended operation that sets the etcb domains.

This allows the existing corres proofs in this file to more-or-less go
through as they stand.

A more principled fix would be to change the abstract spec and
generalise init_arch_objects to initialise other object types.

*)

definition retype_region2_ext :: "obj_ref list \<Rightarrow> Structures_A.apiobject_type \<Rightarrow> unit det_ext_monad" where
  "retype_region2_ext ptrs type \<equiv> modify (\<lambda>s. ekheap_update (foldr (\<lambda>p ekh. (ekh(p := default_ext type default_domain))) ptrs) s)"

crunch all_but_exst[wp]: retype_region2_ext "all_but_exst P"
crunch (empty_fail) empty_fail[wp]: retype_region2_ext

end

interpretation retype_region2_ext_extended: is_extended "retype_region2_ext ptrs type"
  by (unfold_locales; wp)

context begin interpretation Arch . (*FIXME: arch_split*)

definition
 "retype_region2_extra_ext ptrs type \<equiv>
     when (type = Structures_A.TCBObject) (do
       cdom \<leftarrow> gets cur_domain;
       mapM_x (ethread_set (\<lambda>tcb. tcb\<lparr>tcb_domain := cdom\<rparr>)) ptrs
      od)"

crunch all_but_exst[wp]: retype_region2_extra_ext "all_but_exst P" (wp: mapM_x_wp)
crunch (empty_fail) empty_fail[wp]: retype_region2_extra_ext (wp: mapM_x_wp)

end

interpretation retype_region2_extra_ext_extended: is_extended "retype_region2_extra_ext ptrs type"
  by (unfold_locales; wp)

context begin interpretation Arch . (*FIXME: arch_split*)

definition
  retype_region2 :: "obj_ref \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> Structures_A.apiobject_type \<Rightarrow> bool \<Rightarrow> (obj_ref list,'z::state_ext) s_monad"
where
  "retype_region2 ptr numObjects o_bits type dev \<equiv> do
    obj_size \<leftarrow> return $ 2 ^ obj_bits_api type o_bits;
    ptrs \<leftarrow> return $ map (\<lambda>p. ptr_add ptr (p * obj_size)) [0..< numObjects];
    when (type \<noteq> Structures_A.Untyped) (do
      kh \<leftarrow> gets kheap;
      kh' \<leftarrow> return $ foldr (\<lambda>p kh. kh(p \<mapsto> default_object type dev o_bits)) ptrs kh;
      do_extended_op (retype_region2_ext ptrs type);
      modify $ kheap_update (K kh')
    od);
    return $ ptrs
  od"

lemma retype_region_ext_modify_kheap_futz:
  "(retype_region2_extra_ext ptrs type :: (unit, det_ext) s_monad) >>= (\<lambda>_. modify (kheap_update f))
 = (modify (kheap_update f) >>= (\<lambda>_. retype_region2_extra_ext ptrs type))"
  apply (clarsimp simp: retype_region_ext_def retype_region2_ext_def retype_region2_extra_ext_def when_def bind_assoc)
  apply (subst oblivious_modify_swap)
   defer
   apply (simp add: bind_assoc)
  apply (rule oblivious_bind)
  apply simp
  apply (rule oblivious_mapM_x)
  apply (clarsimp simp: ethread_set_def set_eobject_def)
  apply (rule oblivious_bind)
   apply (simp add: gets_the_def)
   apply (rule oblivious_bind)
    apply (clarsimp simp: get_etcb_def)
    apply simp
   apply (simp add: modify_def[symmetric])
done

lemmas retype_region_ext_modify_kheap_futz' =
  fun_cong[OF arg_cong[where f=Nondet_Monad.bind,
           OF retype_region_ext_modify_kheap_futz[symmetric]], simplified bind_assoc]

lemma foldr_upd_app_if_eta_futz:
  "foldr (\<lambda>p ps. ps(p \<mapsto> f p)) as = (\<lambda>g x. if x \<in> set as then Some (f x) else g x)"
apply (rule ext)
apply (rule foldr_upd_app_if)
done

lemma modify_ekheap_update_comp_futz:
  "modify (ekheap_update (f \<circ> g)) = modify (ekheap_update g) >>= (K (modify (ekheap_update f)))"
by (simp add: o_def modify_def bind_def gets_def get_def put_def)

lemma mapM_x_modify_futz:
  assumes "\<forall>ptr\<in>set ptrs. ekheap s ptr \<noteq> None"
  shows "mapM_x (ethread_set F) (rev ptrs) s
       = modify (ekheap_update (foldr (\<lambda>p ekh. ekh(p := Some (F (the (ekh p))))) ptrs)) s" (is "?lhs ptrs s = ?rhs ptrs s")
using assms
proof(induct ptrs arbitrary: s)
  case Nil thus ?case by (simp add: mapM_x_Nil return_def simpler_modify_def)
next
  case (Cons ptr ptrs s)
  have "?rhs (ptr # ptrs) s
      = (do modify (ekheap_update (foldr (\<lambda>p ekh. ekh(p \<mapsto> F (the (ekh p)))) ptrs));
            modify (ekheap_update (\<lambda>ekh. ekh(ptr \<mapsto> F (the (ekh ptr)))))
        od) s"
    by (simp only: foldr_Cons modify_ekheap_update_comp_futz) simp
  also have "... = (do ?lhs ptrs;
                      modify (ekheap_update (\<lambda>ekh. ekh(ptr \<mapsto> F (the (ekh ptr)))))
                    od) s"
    apply (rule monad_eq_split_tail)
     apply simp
    apply (rule Cons.hyps[symmetric])
    using Cons.prems
    apply force
    done
  also have "... = ?lhs (ptr # ptrs) s"
    apply (simp add: mapM_x_append mapM_x_singleton)
    apply (rule monad_eq_split2[OF refl, where
                 P="\<lambda>s. \<forall>ptr\<in>set (ptr # ptrs). ekheap s ptr \<noteq> None"
             and Q="\<lambda>_ s. ekheap s ptr \<noteq> None"])
      apply (simp add: ethread_set_def
                       assert_opt_def get_etcb_def gets_the_def gets_def get_def modify_def put_def set_eobject_def
                       bind_def fail_def return_def split_def
                split: option.splits)
     apply ((wp mapM_x_wp[OF _ subset_refl] | simp add: ethread_set_def set_eobject_def)+)[1]
    using Cons.prems
    apply force
    done
  finally show ?case by (rule sym)
qed

lemma awkward_fold_futz:
  "fold (\<lambda>p ekh. ekh(p \<mapsto> the (ekh p)\<lparr>tcb_domain := cur_domain s\<rparr>)) ptrs ekh
 = (\<lambda>x. if x \<in> set ptrs then Some ((the (ekh x))\<lparr>tcb_domain := cur_domain s\<rparr>) else ekh x)"
by (induct ptrs arbitrary: ekh) (simp_all add: fun_eq_iff)

lemma retype_region2_ext_retype_region_ext_futz:
  "retype_region2_ext ptrs type >>= (\<lambda>_. retype_region2_extra_ext ptrs type)
 = retype_region_ext ptrs type"
proof(cases type)
  case TCBObject
  have complete_futz:
    "\<And>F x. modify (ekheap_update (\<lambda>_. F (cur_domain x) (ekheap x))) x = modify (ekheap_update (\<lambda>ekh. F (cur_domain x) ekh)) x"
    by (simp add: modify_def get_def get_etcb_def put_def bind_def return_def)
  have second_futz:
  "\<And>f G.
   do modify (ekheap_update f);
      cdom \<leftarrow> gets (\<lambda>s. cur_domain s);
      G cdom
   od =
   do cdom \<leftarrow> gets (\<lambda>s. cur_domain s);
      modify (ekheap_update f);
      G cdom
   od"
    by (simp add: bind_def gets_def get_def return_def simpler_modify_def)
  from TCBObject show ?thesis
    apply (clarsimp simp: retype_region_ext_def retype_region2_ext_def retype_region2_extra_ext_def when_def bind_assoc)
    apply (clarsimp simp: exec_gets fun_eq_iff)
    apply (subst complete_futz)
    apply (simp add: second_futz[simplified] exec_gets)
    apply (simp add: default_ext_def exec_modify)
    apply (subst mapM_x_modify_futz[where ptrs="rev ptrs", simplified])
     apply (simp add: foldr_upd_app_if_eta_futz)
    apply (simp add: modify_def exec_get put_def o_def)
    apply (simp add: foldr_upd_app_if_eta_futz foldr_conv_fold awkward_fold_futz)
    apply (simp cong: if_cong)
    done
qed (auto simp: fun_eq_iff retype_region_ext_def retype_region2_ext_def retype_region2_extra_ext_def
                put_def gets_def get_def bind_def return_def mk_ef_def modify_def foldr_upd_app_if' when_def default_ext_def)

lemma retype_region2_ext_retype_region:
  "(retype_region ptr numObjects o_bits type dev :: (obj_ref list, det_ext) s_monad)
 = (do ptrs \<leftarrow> retype_region2 ptr numObjects o_bits type dev;
       retype_region2_extra_ext ptrs type;
       return ptrs
    od)"
apply (clarsimp simp: retype_region_def retype_region2_def when_def bind_assoc)
 apply safe
 defer
 apply (simp add: retype_region2_extra_ext_def)
apply (subst retype_region_ext_modify_kheap_futz'[simplified bind_assoc])
apply (subst retype_region2_ext_retype_region_ext_futz[symmetric])
apply (simp add: bind_assoc)
done

lemma getObject_tcb_gets:
  "getObject addr >>= (\<lambda>x::tcb. gets proj >>= (\<lambda>y. G x y))
 = gets proj >>= (\<lambda>y. getObject addr >>= (\<lambda>x. G x y))"
by (auto simp: exec_gets fun_eq_iff intro: bind_apply_cong dest!: in_inv_by_hoareD[OF getObject_inv_tcb])

lemma setObject_tcb_gets_ksCurDomain:
  "setObject addr (tcb::tcb) >>= (\<lambda>_. gets ksCurDomain >>= G)
 = gets ksCurDomain >>= (\<lambda>x. setObject addr tcb >>= (\<lambda>_. G x))"
apply (clarsimp simp: exec_gets fun_eq_iff)
apply (rule bind_apply_cong)
 apply simp
apply (drule_tac P1="\<lambda>cdom. cdom = ksCurDomain x" in use_valid[OF _ setObject_cd_inv])
apply (simp_all add: exec_gets)
done

lemma curDomain_mapM_x_futz:
  "curDomain >>= (\<lambda>cdom. mapM_x (threadSet (F cdom)) addrs)
 = mapM_x (\<lambda>addr. curDomain >>= (\<lambda>cdom. threadSet (F cdom) addr)) addrs"
proof(induct addrs)
  case Nil thus ?case
    by (simp add: curDomain_def mapM_x_def sequence_x_def bind_def gets_def get_def return_def)
next
  case (Cons addr addrs)
  have H: "\<And>G. do cdom \<leftarrow> curDomain;
                   _ \<leftarrow> threadSet (F cdom) addr;
                   G cdom
                od
              = do cdom \<leftarrow> curDomain;
                   threadSet (F cdom) addr;
                   cdom \<leftarrow> curDomain;
                   G cdom
                od"
    by (simp add: bind_assoc curDomain_def threadSet_def setObject_tcb_gets_ksCurDomain
                  getObject_tcb_gets double_gets_drop_regets)
  from Cons.hyps show ?case
    apply (simp add: mapM_x_def sequence_x_def)
    apply (simp add: bind_assoc foldr_map o_def)
    apply (subst H)
    apply (simp add: mapM_x_def sequence_x_def)
    done
qed

(*

The existing proof continues below.

*)

lemma modify_ekheap_update_ekheap:
  "modify (\<lambda>s. ekheap_update f s) = do s \<leftarrow> gets ekheap; modify (\<lambda>s'. s'\<lparr>ekheap := f s\<rparr>) od"
by (simp add: modify_def gets_def get_def put_def bind_def return_def split_def fun_eq_iff)

lemma corres_retype':
  assumes    not_zero: "n \<noteq> 0"
  and         aligned: "is_aligned ptr (objBitsKO ko + gbits)"
  and    obj_bits_api: "obj_bits_api (APIType_map2 ty) us =
                        objBitsKO ko + gbits"
  and           check: "(sz < obj_bits_api (APIType_map2 ty)  us)
                           = (sz < objBitsKO ko + gbits)"
  and             usv: "APIType_map2 ty = Structures_A.CapTableObject \<Longrightarrow> 0 < us"
  and              ko: "makeObjectKO dev ty = Some ko"
  and             orr: "obj_bits_api (APIType_map2 ty) us \<le> sz \<Longrightarrow>
                        obj_relation_retype
                          (default_object (APIType_map2 ty) dev us) ko"
  and           cover: "range_cover ptr sz (obj_bits_api (APIType_map2 ty) us) n"
  shows "corres (\<lambda>rv rv'. rv' = g rv)
  (\<lambda>s. valid_pspace s \<and> pspace_no_overlap_range_cover ptr sz s
     \<and> valid_mdb s \<and> valid_etcbs s \<and> valid_list s)
  (\<lambda>s. pspace_aligned' s \<and> pspace_distinct' s \<and> pspace_no_overlap' ptr sz s)
  (retype_region2 ptr n us (APIType_map2 ty) dev)
  (do addrs \<leftarrow> createObjects ptr n ko gbits;
      _ \<leftarrow> modify (update_gs (APIType_map2 ty) us (set addrs));
      return (g addrs) od)"
  (is "corres ?r ?P ?P' ?C ?A")
proof -
  note data_map_insert_def[simp del]
  have not_zero':"((of_nat n)::word32) \<noteq> 0"
    by (rule range_cover_not_zero[OF not_zero cover])
  have shiftr_not_zero:" ((of_nat n)::word32) << gbits \<noteq> 0"
    apply (rule range_cover_not_zero_shift[OF not_zero cover])
    apply (simp add:obj_bits_api)
    done
  have unat_of_nat_shift:"unat (((of_nat n)::word32) << gbits) =
                          (n * 2^ gbits)"
    apply (rule range_cover.unat_of_nat_n_shift[OF cover])
    using obj_bits_api
    apply simp
    done
  have unat_of_nat_shift':
    "unat (((of_nat n)::word32) * 2^(gbits + objBitsKO ko)) =
     n * 2^(gbits + objBitsKO ko)"
    apply (subst mult.commute)
    apply (simp add:shiftl_t2n[symmetric])
    apply (rule range_cover.unat_of_nat_n_shift[OF cover])
    using obj_bits_api
    apply simp
    done
  have unat_of_nat_n':
    "unat (((of_nat n)::word32) * 2 ^ (gbits + objBitsKO ko)) \<noteq> 0"
    by (simp add:unat_of_nat_shift' not_zero)
  have bound:"obj_bits_api (APIType_map2 ty) us \<le> sz"
    using cover
    by (simp add:range_cover_def)
  have n_estimate: "n < 2 ^ (word_bits - (objBitsKO ko + gbits))"
    apply (rule le_less_trans)
    apply (rule range_cover.range_cover_n_le(2)[OF cover])
    apply (rule power_strict_increasing)
    apply (simp add:obj_bits_api ko)
    apply (rule diff_less_mono)
    using cover obj_bits_api
    apply (simp_all add:range_cover_def ko word_bits_def)
    done

  have set_retype_addrs_fold:
    "image (\<lambda>n. ptr + 2 ^ obj_bits_api (APIType_map2 ty) us * n)
           {x. x \<le> of_nat n - 1} =
     set (retype_addrs ptr (APIType_map2 ty) n us)"
    apply (clarsimp simp: retype_addrs_def image_def Bex_def ptr_add_def
                          Collect_eq)
    apply (rule iffI)
     apply (clarsimp simp: field_simps word_le_nat_alt)
     apply (rule_tac x="unat x" in exI)
     apply (simp add: unat_sub_if_size range_cover.unat_of_nat_n[OF cover]
                      not_le not_zero
               split: if_split_asm)
    apply (clarsimp simp: field_simps word_le_nat_alt)
    apply (rule_tac x="of_nat x" in exI)
    apply (simp add: unat_sub_if_size range_cover.unat_of_nat_n[OF cover])
    apply (rule nat_le_Suc_less_imp)
    apply (metis le_unat_uoi nat_less_le not_le_imp_less)
    done

  have new_caps_adds_fold:
    "map (\<lambda>n. ptr + 2 ^ objBitsKO ko * n) [0.e.2 ^ gbits * of_nat n - 1] =
     new_cap_addrs (2 ^ gbits * n) ptr ko"
    apply (simp add: new_cap_addrs_def shiftl_t2n)
    apply (subgoal_tac "1 \<le> (2::word32) ^ gbits * of_nat n")
     apply (simp add: upto_enum_red' o_def)
     apply (rule arg_cong2[where f=map, OF refl])
     apply (rule arg_cong2[where f=upt, OF refl])
     apply (metis mult.commute shiftl_t2n unat_of_nat_shift)
    using shiftr_not_zero
    apply (simp add: shiftl_t2n)
    apply (metis word_less_1 word_not_le)
    done

  from aligned
  have al': "is_aligned ptr (obj_bits_api (APIType_map2 ty) us)"
     by (simp add: obj_bits_api ko)
  show ?thesis
  apply (simp add: when_def retype_region2_def createObjects'_def
                   createObjects_def aligned obj_bits_api[symmetric]
                   ko[symmetric] al' shiftl_t2n data_map_insert_def[symmetric]
                   is_aligned_mask[symmetric] split_def unless_def
                   lookupAround2_pspace_no check
        split del: if_split)
  apply (subst retype_addrs_fold)+
  apply (subst if_P)
   using ko
   apply (clarsimp simp: makeObjectKO_def)
  apply (simp add: bind_assoc retype_region2_ext_def)
  apply (rule corres_guard_imp)
    apply (subst modify_ekheap_update_ekheap)
    apply (simp only: bind_assoc)
    apply (rule kheap_ekheap_double_gets)
    apply (rule corres_symb_exec_r)
       apply (simp add: not_less modify_modify bind_assoc[symmetric]
                          obj_bits_api[symmetric] shiftl_t2n upto_enum_red'
                           range_cover.unat_of_nat_n[OF cover])
       apply (rule corres_split_nor[OF _ corres_trivial])
          apply (rename_tac x eps ps)
          apply (rule_tac P="\<lambda>s. x = kheap s \<and> eps = ekheap (s) \<and> ?P s" and
                          P'="\<lambda>s. ps = ksPSpace s \<and> ?P' s" in corres_modify)
          apply (simp add: set_retype_addrs_fold new_caps_adds_fold)
          apply (erule retype_state_relation[OF _ _ _ _ _ _ _ _ _ cover _ _ orr],
                 simp_all add: ko not_zero obj_bits_api
                               bound[simplified obj_bits_api ko])[1]
         apply (clarsimp simp: retype_addrs_fold[symmetric] ptr_add_def upto_enum_red' not_zero'
                               range_cover.unat_of_nat_n[OF cover] word_le_sub1
                         simp del: word_of_nat_eq_0_iff)
         apply (rule_tac f=g in arg_cong)
         apply clarsimp
        apply wp+
      apply (clarsimp split: option.splits)
      apply (intro conjI impI)
       apply (clarsimp|wp)+
     apply (clarsimp split: option.splits)
     apply wpsimp
    apply (clarsimp split: option.splits)
    apply (intro conjI impI)
     apply wp
    apply (clarsimp simp:lookupAround2_char1)
    apply wp
    apply (clarsimp simp: obj_bits_api ko)
    apply (drule(1) pspace_no_overlap_disjoint')
    apply (rule_tac x1 = a in ccontr[OF in_empty_interE])
      apply simp
     apply (clarsimp simp: not_less shiftL_nat)
     apply (erule order_trans)
     apply (subst p_assoc_help)
     apply (subst word_plus_and_or_coroll2[symmetric,where w = "mask sz"])
     apply (subst add.commute)
     apply (subst add.assoc)
     apply (rule word_plus_mono_right)
      using cover
      apply -
      apply (rule iffD2[OF word_le_nat_alt])
      apply (subst word_of_nat_minus)
       using not_zero
       apply simp
      apply (rule le_trans[OF unat_plus_gt])
      apply simp
      apply (subst unat_minus_one)
       apply (subst mult.commute)
       apply (rule word_power_nonzero_32)
         apply (rule of_nat_less_pow_32[OF n_estimate])
         apply (simp add:word_bits_def objBitsKO_gt_0 ko)
        apply (simp add:range_cover_def obj_bits_api ko word_bits_def)
       apply (cut_tac not_zero',clarsimp simp:ko)
      apply(clarsimp simp:field_simps ko)
      apply (subst unat_sub[OF word_1_le_power])
       apply (simp add:range_cover_def)
      apply (subst diff_add_assoc[symmetric])
       apply (cut_tac unat_of_nat_n',simp add:ko)
      apply (clarsimp simp: obj_bits_api ko)
      apply (rule diff_le_mono)
      apply (frule range_cover.range_cover_compare_bound)
      apply (cut_tac obj_bits_api unat_of_nat_shift')
      apply (clarsimp simp:add.commute range_cover_def ko)
     apply (rule is_aligned_no_wrap'[OF is_aligned_neg_mask,OF le_refl ])
     apply (simp add:range_cover_def domI)+
  done
qed

lemma createObjects_corres':
  "\<lbrakk>corres r P P' f (createObjects a b ko d); ko = injectKO val\<rbrakk>
   \<Longrightarrow> corres dc P P' f (createObjects' a b ko d)"
  apply (clarsimp simp:corres_underlying_def createObjects_def return_def)
  apply (rule conjI)
  apply (clarsimp simp:bind_def split_def)
    apply (drule(1) bspec)
    apply (clarsimp simp:image_def)
    apply (drule(1) bspec)
    apply clarsimp
    apply (erule bexI[rotated])
    apply simp
  apply (clarsimp simp:bind_def split_def image_def)
  apply (drule(1) bspec|clarsimp)+
  done

lemmas retype_aligned_distinct'' = retype_aligned_distinct'
       [unfolded foldr_upd_app_if[folded data_map_insert_def]]

lemma retype_ko_wp_at':
  assumes vs: "pspace_aligned' s" "pspace_distinct' s"
     and  pn: "pspace_no_overlap' ptr sz s"
   and cover: "range_cover ptr sz (objBitsKO obj) n"
  shows
  "ko_wp_at' P p (s \<lparr>ksPSpace := foldr (\<lambda>addr. data_map_insert addr obj)
                      (new_cap_addrs n ptr obj) (ksPSpace s)\<rparr>)
     = (if p \<in> set (new_cap_addrs n ptr obj) then P obj
                         else ko_wp_at' P p s)"
  apply (subst foldr_upd_app_if[folded data_map_insert_def])
  apply (rule foldr_update_ko_wp_at' [OF vs])
    apply (simp add: retype_aligned_distinct'' [OF vs pn cover])+
  apply (rule new_cap_addrs_aligned)
  using cover
  apply (simp add:range_cover_def cover)
  done

lemma retype_obj_at':
  assumes vs: "pspace_aligned' s" "pspace_distinct' s"
     and  pn: "pspace_no_overlap' ptr sz s"
     and cover: "range_cover ptr sz (objBitsKO obj) n"
  shows
  "obj_at' P p (s \<lparr>ksPSpace := foldr (\<lambda>addr. data_map_insert addr obj)
                      (new_cap_addrs n ptr obj) (ksPSpace s)\<rparr>)
     = (if p \<in> set (new_cap_addrs n ptr obj) then (\<exists>ko. projectKO_opt obj = Some ko \<and> P ko)
                         else obj_at' P p s)"
  unfolding obj_at'_real_def
  apply (rule retype_ko_wp_at'[OF vs pn cover])
done

lemma retype_obj_at_disj':
  assumes vs: "pspace_aligned' s" "pspace_distinct' s"
     and  pn: "pspace_no_overlap' ptr sz s"
     and cover: "range_cover ptr sz (objBitsKO obj) n"
  shows
  "obj_at' P p (s \<lparr>ksPSpace := foldr (\<lambda>addr. data_map_insert addr obj)
                      (new_cap_addrs n ptr obj) (ksPSpace s)\<rparr>)
     = (obj_at' P p s \<or> p \<in> set (new_cap_addrs n ptr obj)
                         \<and> (\<exists>ko. projectKO_opt obj = Some ko \<and> P ko))"
  apply (simp add: retype_obj_at' [OF vs pn cover])
  apply (safe, simp_all)
  apply (drule subsetD [OF new_cap_addrs_subset [OF cover]])
  apply (insert pspace_no_overlap_disjoint' [OF vs(1) pn ])
  apply (clarsimp simp: obj_at'_def)
  apply (rule_tac x1 = p in ccontr[OF in_empty_interE])
    apply (simp add:ptr_add_def p_assoc_help domI)+
  done

declare word_unat_power[symmetric,simp]

lemma createObjects_ko_at_strg:
  fixes ptr :: word32
  assumes    cover: "range_cover ptr sz ((objBitsKO ko) + gbits) n"
  assumes    not_0: "n\<noteq> 0"
  assumes       pi: "projectKO_opt ko  = Some val"
  shows "\<lbrace>\<lambda>s. pspace_no_overlap' ptr sz s \<and> pspace_aligned' s \<and> pspace_distinct' s\<rbrace>
             createObjects ptr n ko gbits
         \<lbrace>\<lambda>r s. \<forall>x \<in> set r. \<forall>offs < 2 ^ gbits. ko_at' val (x + (offs << objBitsKO ko)) s\<rbrace>"
proof -
  have shiftr_not_zero:" 1 \<le> ((of_nat n)::word32) << gbits"
    using range_cover_not_zero_shift[OF not_0 cover,where gbits = gbits]
    apply -
    apply (simp add:word_le_sub1)
    done
  note unat_of_nat_shiftl = range_cover.unat_of_nat_n_shift[OF cover,where gbits = gbits,simplified]
  note word_of_nat_eq_0_iff[simp del]
  have in_new:"\<And>idx offs. \<lbrakk>idx \<le> of_nat n - 1;offs<2 ^ gbits\<rbrakk>
    \<Longrightarrow> ptr + (idx << objBitsKO ko + gbits) + (offs << objBitsKO ko)
        \<in> set (new_cap_addrs (n * 2 ^ gbits) ptr ko)"
      apply (insert range_cover_not_zero[OF not_0 cover] not_0)
      apply (clarsimp simp:new_cap_addrs_def image_def)
      apply (rule_tac x ="unat (2 ^ gbits * idx + offs)" in bexI)
        apply (subst add.commute)
        apply (simp add:shiftl_shiftl[symmetric])
        apply (simp add:shiftl_t2n distrib_left[symmetric])
      apply simp
      apply (rule unat_less_helper)
      apply (rule less_le_trans)
       apply (erule word_plus_strict_mono_right)
       apply (subst distrib_left[where c = "1 :: 32 word",symmetric,simplified])
       apply (subst mult.commute[where a = "2^gbits"])+
       apply (insert cover)
       apply (rule word_mult_le_iff[THEN iffD2])
         apply (simp add:p2_gt_0)
         apply (clarsimp simp:range_cover_def word_bits_def)
         apply (drule range_cover_rel[where sbit' = "objBitsKO ko "])
           apply simp
          apply simp
         apply (rule less_le_trans)
          apply (rule range_cover.range_cover_le_n_less)
           apply simp
          apply (subst unat_power_lower)
           using cover
           apply (clarsimp simp:range_cover_def)
          apply (simp add:field_simps)
          apply (rule unat_le_helper)
          apply (erule order_trans[OF _ word_sub_1_le])
          apply (simp add:range_cover_not_zero[OF not_0 cover])
         apply (simp add:word_bits_def)
        apply (drule range_cover_rel[where sbit' = "objBitsKO ko "])
          apply simp
         apply simp
        apply (erule less_le_trans[OF range_cover.range_cover_le_n_less(1)])
        apply (subst unat_power_lower)
         using cover
         apply (clarsimp simp:range_cover_def)
        apply (simp add:field_simps)
        apply (rule unat_le_helper[OF inc_le])
        apply (simp add:word_leq_minus_one_le)
       apply (simp add:word_bits_def)
      apply (rule no_plus_overflow_neg)
      apply (rule less_le_trans[where y = "of_nat n"])
       apply unat_arith
      using range_cover.range_cover_n_less[OF cover]
     apply (simp add:word_bits_def)
    apply (subst distrib_left[where c = "1 :: 32 word",symmetric,simplified])
   apply (subst mult.commute)
   apply simp
   apply (rule word_mult_le_iff[THEN iffD2])
       apply (simp add:p2_gt_0)
      apply (simp add:range_cover_def word_bits_def)
     apply (drule range_cover_rel[where sbit' = "objBitsKO ko "])
       apply simp
      apply simp
     apply (rule less_le_trans)
     apply (rule range_cover.range_cover_le_n_less)
       apply simp
     apply (subst unat_power_lower)
       using cover
       apply (clarsimp simp:range_cover_def)
      apply (simp add:field_simps)
     apply (rule unat_le_helper)
    apply unat_arith
   apply (simp add:word_bits_def)
   apply (drule range_cover_rel[where sbit' = "objBitsKO ko "])
       apply simp
      apply simp
     apply (rule less_le_trans)
      apply (erule range_cover.range_cover_le_n_less)
     apply (simp add:range_cover.unat_of_nat_n[OF cover])
    apply (simp add: unat_le_helper)
   apply (simp add:word_bits_def)
  apply unat_arith
  done
  show ?thesis
  apply (simp add: split_def createObjects_def lookupAround2_pspace_no
                   alignError_def unless_def createObjects'_def)
  apply (rule hoare_pre)
   apply (wp|simp add:data_map_insert_def[symmetric]
     cong: if_cong del: fun_upd_apply data_map_insert_def)+
   apply (wpc|wp|clarsimp simp del:fun_upd_apply)+
   apply (subst new_cap_addrs_fold'[OF shiftr_not_zero])+
   apply (subst data_map_insert_def[symmetric])+
   apply (subst retype_obj_at_disj')
     apply (simp add:valid_pspace'_def unat_of_nat_shiftl)+
     apply (rule range_cover_rel[OF cover])
     apply simp+
   apply (subst retype_obj_at_disj')
     apply (simp add:valid_pspace'_def unat_of_nat_shiftl)+
     apply (rule range_cover_rel[OF cover])
     apply simp+
  using range_cover.unat_of_nat_n_shift[OF cover,where gbits = gbits,simplified] pi
  apply (simp add: in_new)
  done
qed

lemma createObjects_ko_at:
  fixes ptr :: word32
  assumes    cover: "range_cover ptr sz ((objBitsKO ko) + gbits) n"
  assumes    not_0: "n\<noteq> 0"
  assumes       pi: "projectKO_opt ko = Some val"
  shows "\<lbrace>\<lambda>s. pspace_no_overlap' ptr sz s \<and> valid_pspace' s\<rbrace>
             createObjects ptr n ko gbits
         \<lbrace>\<lambda>r s. \<forall>x \<in> set r. \<forall>offs < 2 ^ gbits. ko_at' val (x + (offs << objBitsKO ko)) s\<rbrace>"
  by (wp createObjects_ko_at_strg[OF cover not_0 pi],fastforce)

lemma createObjects_obj_at:
  fixes ptr :: word32 and val :: "'a :: pspace_storable"
  assumes  cover:"range_cover ptr sz ((objBitsKO ko) + gbits) n"
  and      not_0:"n \<noteq> 0"
  and       pi: "\<exists>(val::'a). projectKO_opt ko = Some val"
  shows "\<lbrace>\<lambda>s. pspace_no_overlap' ptr sz s \<and> valid_pspace' s\<rbrace>
  createObjects ptr n ko gbits \<lbrace>\<lambda>r s. \<forall>x \<in> set r. \<forall>offs < 2 ^ gbits.
                                     obj_at' (\<lambda>(x::'a). True) (x + (offs << objBitsKO ko)) s\<rbrace>"
  apply (rule exE[OF pi])
  apply (erule_tac val1 = x in
    hoare_post_imp [OF _ createObjects_ko_at [OF cover not_0 ],rotated])
  apply (intro allI ballI impI)
  apply (drule(1) bspec)
  apply (drule spec, drule(1) mp)
  apply (clarsimp elim!: obj_at'_weakenE)
  done

(* until we figure out what we really need of page
   mappings it's just alignment, which, fortunately,
   is trivial *)
lemma createObjects_aligned:
  assumes al: "is_aligned ptr (objBitsKO ko + gbits)"
  and bound :"n < 2 ^ word_bits" "n\<noteq>0"
  and bound':"objBitsKO ko + gbits < word_bits"
  shows "\<lbrace>\<top>\<rbrace> createObjects ptr n ko gbits
         \<lbrace>\<lambda>rv s. \<forall>x \<in> set rv. is_aligned x (objBitsKO ko + gbits)\<rbrace>"
  apply (rule hoare_strengthen_post)
   apply (rule createObjects_ret[OF bound])
  apply (clarsimp dest!: less_two_pow_divD)
  apply (rule is_aligned_ptr_add_helper[OF al])
  apply (simp_all add:bound')
  done

lemma createObjects_aligned2:
  "\<lbrace>\<lambda>s. is_aligned ptr (objBitsKO ko + gbits) \<and> n < 2 ^ word_bits \<and> n \<noteq> 0
      \<and> aln < word_bits
      \<and> aln = objBitsKO ko + gbits\<rbrace>
    createObjects ptr n ko gbits
   \<lbrace>\<lambda>rv s. \<forall>x \<in> set rv. is_aligned x aln\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply simp
  apply (rule hoare_pre, wp createObjects_aligned, simp_all)
  done

lemma range_cover_n_wb:
  "range_cover (ptr :: obj_ref) sz us n \<Longrightarrow> n < 2 ^ word_bits"
  apply (rule order_le_less_trans, erule range_cover.range_cover_n_le(2))
  apply (clarsimp simp: range_cover_def)
  apply (simp add: word_bits_def)
  done

lemma createObjects_nonzero:
  assumes not_0: "n \<noteq> 0"
  assumes  cover:"range_cover ptr sz ((objBitsKO ko) + bits) n"
  shows "\<lbrace>\<lambda>s. ptr \<noteq> 0\<rbrace>
            createObjects ptr n ko bits
         \<lbrace>\<lambda>rv s. \<forall>p \<in> set rv. p \<noteq> 0\<rbrace>"
  apply (insert not_0)
  apply (rule hoare_pre)
   apply (rule hoare_gen_asm [where P = "ptr \<noteq> 0"])
   using cover
   apply (clarsimp simp:range_cover_def)
   apply (erule is_aligned_get_word_bits,simp_all)
  apply (rule hoare_post_imp [OF _ createObjects_ret])
    apply (simp add: ptr_add_def)
    apply (intro allI impI ballI)
    apply (simp add:power_add[symmetric] mult.assoc)
    apply (drule(1) range_cover_no_0[OF _ cover])
    apply (simp add: objBits_def)
   apply (simp add: range_cover_n_wb[OF cover])
  apply simp
  done

lemma objBits_if_dev:
    "objBitsKO (if dev then KOUserDataDevice else KOUserData) = pageBits"
  by (simp add: objBitsKO_def)

lemma cwo_ret:
  assumes  cover:"range_cover ptr sz v n"
  assumes not_0:"n\<noteq> 0"
  shows result: "\<lbrace>pspace_no_overlap' ptr sz and valid_pspace' and K (v = 12 + bs)\<rbrace>
           createObjects ptr n (if dev then KOUserDataDevice else KOUserData) bs
          \<lbrace>\<lambda>rv s. \<forall>x\<in>set rv. \<forall>p<2 ^ (v - pageBits).
                 typ_at' (if dev then UserDataDeviceT else UserDataT) (x + p * 2 ^ pageBits) s\<rbrace>"
proof -
  note create_objs_device = hoare_post_imp [OF _ hoare_conj [OF createObjects_ret
     createObjects_ko_at[where val = UserDataDevice,simplified]]]

  note create_objs_normal = hoare_post_imp [OF _ hoare_conj [OF createObjects_ret
     createObjects_ko_at[where val = UserData,simplified]]]

show ?thesis
  apply (cases dev)
   apply (rule hoare_gen_asm)
   apply (rule hoare_pre)
   apply (rule create_objs_device)
         apply (clarsimp simp add: pageBits_def)
         apply (drule bspec, simp, drule spec, drule(1) mp)
         apply (simp add: typ_at'_def obj_at'_real_def objBits_simps pageBits_def shiftl_t2n field_simps)
         apply (erule ko_wp_at'_weakenE)
         apply (clarsimp simp add: projectKO_opts_defs split: kernel_object.splits)
        apply (rule le_less_trans[OF _ power_strict_increasing])
          apply (rule range_cover.range_cover_n_le(1)[OF cover])
         apply (simp add: word_bits_def pageBits_def not_0)+
     apply (rule range_cover_rel[OF cover])
      apply (simp add: objBitsKO_def pageBits_def not_0)+
     using not_0 apply simp_all
    apply (clarsimp simp add: projectKO_def return_def
      projectKO_opts_defs split: kernel_object.splits)
  apply (rule hoare_gen_asm[unfolded K_def])
  apply (rule hoare_pre)
  apply (rule create_objs_normal)
         apply (clarsimp simp add: pageBits_def)
         apply (drule bspec, simp, drule spec, drule(1) mp)
         apply (simp add: typ_at'_def obj_at'_real_def objBits_simps pageBits_def shiftl_t2n field_simps)
         apply (erule ko_wp_at'_weakenE)
         apply (clarsimp simp add: projectKO_opts_defs split: kernel_object.splits)
        apply (rule le_less_trans[OF _ power_strict_increasing])
          apply (rule range_cover.range_cover_n_le(1)[OF cover])
         apply (simp add: word_bits_def pageBits_def not_0)+
     apply (rule range_cover_rel[OF cover])
      apply (simp add: objBitsKO_def pageBits_def not_0)+
     using not_0 apply simp_all
    apply (clarsimp simp add: projectKO_def return_def
      projectKO_opts_defs split: kernel_object.splits)
  done
qed
lemmas capFreeIndex_update_valid_untyped' =
  capFreeIndex_update_valid_cap'[unfolded valid_cap'_def,simplified,THEN conjunct2,THEN conjunct1]

lemma createNewCaps_valid_cap:
  fixes ptr :: word32
  assumes cover: "range_cover ptr sz (APIType_capBits ty us) n "
  assumes not_0: "n \<noteq> 0"
  assumes ct: "ty = APIObjectType ArchTypes_H.CapTableObject \<Longrightarrow> 0 < us"
              "ty = APIObjectType apiobject_type.Untyped \<Longrightarrow> minUntypedSizeBits \<le> us \<and> us \<le> maxUntypedSizeBits"
  assumes ptr: " ptr \<noteq> 0"
  shows "\<lbrace>\<lambda>s. pspace_no_overlap' ptr sz s \<and> valid_pspace' s\<rbrace>
           createNewCaps ty ptr n us dev
         \<lbrace>\<lambda>r s. (\<forall>cap \<in> set r. s \<turnstile>' cap)\<rbrace>"
proof -
  note blah[simp del] = untyped_range.simps usable_untyped_range.simps atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
  note if_split_def[split del] = if_splits

  show ?thesis
  proof(cases "Types_H.toAPIType ty")
    case None thus ?thesis
      using not_0
      apply (clarsimp simp: createNewCaps_def Arch_createNewCaps_def)
      using cover
      apply (simp add: range_cover_def)
      using cover
      apply (clarsimp simp: ARM_HYP_H.toAPIType_def APIType_capBits_def
                     split: ARM_HYP_H.object_type.splits)
       \<comment> \<open>SmallPageObject\<close>
       apply wp
       apply (simp add: valid_cap'_def capAligned_def n_less_word_bits
                        ball_conj_distrib)
       apply ((wp createObjects_aligned2 createObjects_nonzero[OF not_0 ,simplified]
                 cwo_ret[OF _ not_0]
         | simp add: objBits_if_dev pageBits_def ptr range_cover_n_wb)+)
       apply (simp add:pageBits_def ptr word_bits_def)
      \<comment> \<open>LargePageObject\<close>
      apply wp
      apply (simp add: valid_cap'_def capAligned_def n_less_word_bits
                       ball_conj_distrib)
      apply (wp createObjects_aligned2 createObjects_nonzero[OF not_0 ,simplified]
                cwo_ret[OF _ not_0]
        | simp add: objBits_if_dev pageBits_def ptr range_cover_n_wb)+
      apply (simp add:pageBits_def ptr word_bits_def)

     \<comment> \<open>SectionObject\<close>
     apply wp
     apply (simp add: valid_cap'_def capAligned_def n_less_word_bits
                      ball_conj_distrib)
     apply (wp createObjects_aligned2 createObjects_nonzero[OF not_0 ,simplified]
               cwo_ret[OF _ not_0]
       | simp add: objBits_if_dev vspace_bits_defs ptr range_cover_n_wb)+
     apply (simp add: pageBits_def ptr word_bits_def)

    \<comment> \<open>SuperSectionObject\<close>
    apply wp
    apply (simp add: valid_cap'_def capAligned_def n_less_word_bits
                     ball_conj_distrib)
    apply (wp createObjects_aligned2 createObjects_nonzero[OF not_0 ,simplified]
              cwo_ret[OF _ not_0]
      | simp add: objBits_if_dev pageBits_def ptr range_cover_n_wb)+
    apply (simp add:pageBits_def ptr word_bits_def)

   \<comment> \<open>PageTableObject\<close>
    apply wp
     apply (simp add: valid_cap'_def capAligned_def n_less_word_bits)
     apply (simp only: imp_conv_disj page_table_at'_def
                       typ_at_to_obj_at_arches)
     apply (rule hoare_chain)
       apply (rule hoare_vcg_conj_lift)
        apply (rule createObjects_aligned [OF _ range_cover.range_cover_n_less(1)
            [where 'a=32, unfolded word_bits_len_of, OF cover] not_0])
        apply (simp add:objBits_simps archObjSize_def vspace_bits_defs)+
       apply (simp add:range_cover_def word_bits_def)
       apply (rule createObjects_obj_at[where 'a =pte, OF _  not_0])
         apply (simp add:objBits_simps archObjSize_def vspace_bits_defs)+
       apply (simp add: projectKOs projectKO_opt_pte)
      apply simp
     apply (clarsimp simp: objBits_simps archObjSize_def vspace_bits_defs)
    apply clarsimp
  \<comment> \<open>PageDirectoryObject\<close>
   apply (wp hoare_vcg_const_Ball_lift)
   apply (wp mapM_x_wp' )
   apply (simp add: valid_cap'_def capAligned_def n_less_word_bits)
   apply (simp only: imp_conv_disj page_directory_at'_def
                     typ_at_to_obj_at_arches)
   apply (rule hoare_chain)
     apply (rule hoare_vcg_conj_lift)
      apply (rule createObjects_aligned [OF _ range_cover.range_cover_n_less(1)
          [where 'a=32, unfolded word_bits_len_of, OF cover] not_0])
       apply (simp add:objBits_simps archObjSize_def vspace_bits_defs)+
      apply (simp add:range_cover_def word_bits_def)
     apply (rule createObjects_obj_at [where 'a=pde, OF _  not_0])
      apply (simp add:objBits_simps archObjSize_def vspace_bits_defs)
     apply (simp add: projectKOs projectKO_opt_pde)
    apply simp
   apply (clarsimp simp: objBits_simps archObjSize_def vspace_bits_defs)
  apply simp
  \<comment> \<open>VCPUObject\<close>
  apply (wpsimp wp: hoare_vcg_const_Ball_lift simp: valid_cap'_def capAligned_def n_less_word_bits)+
   apply (simp only: imp_conv_disj typ_at_to_obj_at_arches vcpu_bits_def pageBits_def)
   apply (rule hoare_chain)
     apply (rule hoare_vcg_conj_lift)
      apply (rule createObjects_aligned [OF _ range_cover.range_cover_n_less(1)
           [where 'a=32, unfolded word_bits_len_of, OF cover] not_0])
       apply (simp add:objBits_simps archObjSize_def vcpu_bits_def pageBits_def)+
      apply (simp add:range_cover_def word_bits_def)
     apply (rule createObjects_obj_at [where 'a=vcpu, OF _  not_0])
      apply (simp add:objBits_simps archObjSize_def vcpu_bits_def pageBits_def)
     apply (simp add: projectKOs projectKO_opt_pde)
    apply simp
   apply simp
   apply (clarsimp simp: objBits_simps archObjSize_def vcpu_bits_def pageBits_def)
  apply simp+
  done
  next
    case (Some a) thus ?thesis
    proof(cases a)
      case Untyped with Some cover ct show ?thesis
        apply (clarsimp simp: Arch_createNewCaps_def createNewCaps_def)
        apply (simp_all add: ARM_HYP_H.toAPIType_def fromIntegral_def
                             toInteger_nat fromInteger_nat APIType_capBits_def
                      split: ARM_HYP_H.object_type.splits)
        apply wp
        apply (intro ballI)
        apply (clarsimp simp: image_def upto_enum_red' valid_cap'_def capAligned_def
                       split: capability.splits)
        apply (drule word_leq_minus_one_le[rotated])
       apply (rule range_cover_not_zero[OF not_0 cover])
      apply (intro conjI)
         apply (rule is_aligned_add_multI[OF _ le_refl refl])
           apply (fastforce simp:range_cover_def word_bits_def)+
       apply (clarsimp simp:valid_untyped'_def ko_wp_at'_def obj_range'_def)
       apply (drule(1) pspace_no_overlapD'[rotated])
       apply (frule(1) range_cover_cell_subset)
       apply (erule disjE)
        apply (drule psubset_imp_subset)
        apply (drule(1) disjoint_subset2[rotated])
        apply (drule(1) disjoint_subset)
        apply (drule(1) range_cover_subset_not_empty)
        apply clarsimp+
       apply blast
      apply (drule(1) range_cover_no_0[OF ptr _ unat_less_helper])
      apply simp
      done
    next
      case TCBObject with Some cover ct show ?thesis
        including no_pre
        apply (clarsimp simp: Arch_createNewCaps_def createNewCaps_def)
        apply (simp_all add: ARM_HYP_H.toAPIType_def
                             fromIntegral_def toInteger_nat fromInteger_nat APIType_capBits_def curDomain_def
                      split: ARM_HYP_H.object_type.splits)
        apply (wp mapM_x_wp' hoare_vcg_const_Ball_lift)+
        apply (rule hoare_post_imp)
         prefer 2
         apply (rule createObjects_obj_at [where 'a = "tcb",OF _ not_0])
          using cover
          apply (clarsimp simp: ARM_HYP_H.toAPIType_def APIType_capBits_def objBits_simps
                         split: ARM_HYP_H.object_type.splits)
         apply (simp add: projectKOs)
        apply (clarsimp simp: valid_cap'_def objBits_simps)
        apply (fastforce intro: capAligned_tcbI)
        done
    next
      case EndpointObject with Some cover ct show ?thesis
        including no_pre
        apply (clarsimp simp: Arch_createNewCaps_def createNewCaps_def)
        apply (simp_all add: ARM_HYP_H.toAPIType_def
                             fromIntegral_def toInteger_nat fromInteger_nat APIType_capBits_def
                      split: ARM_HYP_H.object_type.splits)
        apply wp
        apply (rule hoare_post_imp)
         prefer 2
         apply (rule createObjects_obj_at [where 'a=endpoint, OF _ not_0])
          using cover
          apply (clarsimp simp: ARM_HYP_H.toAPIType_def APIType_capBits_def objBits_simps
                         split: ARM_HYP_H.object_type.splits)
         apply (simp add: projectKOs)
        apply (clarsimp simp: valid_cap'_def objBits_simps)
        apply (fastforce intro: capAligned_epI)
        done
    next
      case NotificationObject with Some cover ct show ?thesis
        including no_pre
        apply (clarsimp simp: Arch_createNewCaps_def createNewCaps_def)
        apply (simp_all add: ARM_HYP_H.toAPIType_def
                             fromIntegral_def toInteger_nat fromInteger_nat APIType_capBits_def
                      split: ARM_HYP_H.object_type.splits)
        apply wp
        apply (rule hoare_post_imp)
         prefer 2
         apply (rule createObjects_obj_at [where 'a="notification", OF _ not_0])
          using cover
          apply (clarsimp simp: ARM_HYP_H.toAPIType_def APIType_capBits_def objBits_simps
                         split: ARM_HYP_H.object_type.splits)
         apply (simp add: projectKOs)
        apply (clarsimp simp: valid_cap'_def objBits_simps)
        apply (fastforce intro: capAligned_ntfnI)
        done
    next
      case CapTableObject with Some cover ct show ?thesis
        apply (clarsimp simp: Arch_createNewCaps_def createNewCaps_def)
        apply (simp_all add: ARM_HYP_H.toAPIType_def
                             fromIntegral_def toInteger_nat fromInteger_nat APIType_capBits_def
                      split: ARM_HYP_H.object_type.splits)
        apply wp
         apply (clarsimp simp: ARM_HYP_H.toAPIType_def APIType_capBits_def objBits_simps
                        split: ARM_HYP_H.object_type.split object_type.splits)
         apply (rule hoare_strengthen_post)
           apply (rule hoare_vcg_conj_lift)
           apply (rule createObjects_aligned [OF _ _ not_0 ])
              apply ((clarsimp simp:objBits_simps range_cover_def range_cover.range_cover_n_less[where 'a=32, unfolded word_bits_len_of, OF cover])+)[3]
            apply (simp add: word_bits_def)
           apply (rule hoare_vcg_conj_lift)
            apply (rule createObjects_ret [OF range_cover.range_cover_n_less(1)[where 'a=32, unfolded word_bits_len_of, OF cover] not_0])
           apply (rule createObjects_obj_at [where 'a=cte, OF _ not_0])
            apply (simp add: objBits_simps APIType_capBits_def)
           apply (simp add: projectKOs)
          apply simp
         apply (clarsimp simp: valid_cap'_def capAligned_def objBits_simps
                        dest!: less_two_pow_divD)
         apply (thin_tac "\<forall>x\<in>S. is_aligned (p x) n" for S p n)
         apply (intro conjI)
           apply ((simp add:range_cover_def word_bits_def)+)[2]
         apply (clarsimp simp: power_sub)
         apply (drule bspec, simp)
         apply (drule_tac x = "addr && mask us" in spec)
         apply (drule mp)
          apply simp
          apply (rule and_mask_less')
          apply (simp add: range_cover_def word_bits_def)
         apply (clarsimp simp add: shiftl_t2n)
        apply simp
        done
    qed
  qed
qed


lemma other_objs_default_relation:
  "\<lbrakk> case ty of Structures_A.EndpointObject \<Rightarrow> ko = injectKO (makeObject :: endpoint)
             | Structures_A.NotificationObject \<Rightarrow> ko = injectKO (makeObject :: Structures_H.notification)
             | Structures_A.TCBObject \<Rightarrow> ko = injectKO (makeObject :: tcb)
             | _ \<Rightarrow> False \<rbrakk> \<Longrightarrow>
    obj_relation_retype (default_object ty dev n) ko"
  apply (rule obj_relation_retype_other_obj)
   apply (clarsimp simp: default_object_def
                         is_other_obj_relation_type_def
                  split: Structures_A.apiobject_type.split_asm)
  apply (clarsimp simp: other_obj_relation_def default_object_def
                        ep_relation_def ntfn_relation_def
                        tcb_relation_def default_tcb_def makeObject_tcb
                        makeObject_cte new_context_def newContext_def
                        default_ep_def makeObject_endpoint default_notification_def
                        makeObject_notification default_ntfn_def
                        fault_rel_optionation_def
                        initContext_def
                        arch_tcb_context_get_def atcbContextGet_def
                        default_arch_tcb_def newArchTCB_def
                        arch_tcb_relation_def
                 split: Structures_A.apiobject_type.split_asm)
  done

lemma captable_relation_retype:
  "n < word_bits \<Longrightarrow>
   obj_relation_retype (default_object Structures_A.CapTableObject dev n) (KOCTE makeObject)"
  apply (clarsimp simp: obj_relation_retype_def default_object_def
                        wf_empty_bits objBits_simps'
                        dom_empty_cnode ex_with_length cte_level_bits_def)
  apply (rule conjI)
   defer
   apply (clarsimp simp: cte_relation_def empty_cnode_def makeObject_cte)
  apply (rule set_eqI, rule iffI)
   apply (clarsimp simp: cte_map_def')
   apply (rule_tac x="of_bl y" in exI)
   apply (simp add: of_bl_length[where 'a=32, folded word_bits_def])
  apply (clarsimp simp: image_def cte_map_def')
  apply (rule_tac x="drop (word_bits - n) (to_bl xa)" in exI)
  apply (simp add: of_drop_to_bl word_bits_def word_size)
  apply (simp add: less_mask_eq)
  done

lemma pagetable_relation_retype:
  "obj_relation_retype (default_object (ArchObject PageTableObj) dev n)
                       (KOArch (KOPTE makeObject))"
  apply (simp add: default_object_def default_arch_object_def
                   makeObject_pte obj_relation_retype_def
                   objBits_simps archObjSize_def
                   pte_relation_def)
  apply (clarsimp simp: range_composition[symmetric]
                        shiftl_t2n field_simps)
  apply (subst image_comp [symmetric, where g=ucast, unfolded o_def])
  apply (simp add: ucast_range_less vspace_bits_defs)
  apply (fastforce simp:pte_relation_aligned_def)
  done

lemma pagedirectory_relation_retype:
  "obj_relation_retype (default_object (ArchObject PageDirectoryObj) dev n)
                       (KOArch (KOPDE makeObject))"
  apply (simp add: default_object_def default_arch_object_def
                   makeObject_pde obj_relation_retype_def
                   objBits_simps archObjSize_def
                   pde_relation_def)
  apply (clarsimp simp: range_composition[symmetric]
                        shiftl_t2n field_simps)
  apply (subst image_comp [symmetric, where g=ucast, unfolded o_def])
  apply (simp add: ucast_range_less vspace_bits_defs)
  apply (fastforce simp:pde_relation_aligned_def)
  done

lemmas makeObjectKO_simps = makeObjectKO_def[split_simps ARM_HYP_H.object_type.split
 apiobject_type.split sum.split kernel_object.split ]

lemma corres_retype:
  assumes         not_zero: "n \<noteq> 0"
  and         aligned: "is_aligned ptr (objBitsKO ko + gbits)"
  and    obj_bits_api: "obj_bits_api (APIType_map2 ty) us = objBitsKO ko + gbits"
  and              tp: "APIType_map2 ty \<in> no_gs_types"
  and              ko: "makeObjectKO dev ty = Some ko"
  and             orr: "obj_bits_api (APIType_map2 ty) us \<le> sz \<Longrightarrow>
                        obj_relation_retype (default_object (APIType_map2 ty) dev us) ko"
  and           cover: "range_cover ptr sz (obj_bits_api (APIType_map2 ty) us) n"
  shows "corres (=)
  (\<lambda>s. valid_pspace s \<and> pspace_no_overlap_range_cover ptr sz s
     \<and> valid_mdb s \<and> valid_etcbs s \<and> valid_list s)
  (\<lambda>s. pspace_aligned' s \<and> pspace_distinct' s \<and> pspace_no_overlap' ptr sz s
       \<and> (\<exists>val. ko = injectKO val))
  (retype_region2 ptr n us (APIType_map2 ty) dev) (createObjects ptr n ko gbits)"
  apply (rule corres_guard_imp)
    apply (rule_tac F = "(\<exists>val. ko = injectKO val)" in corres_gen_asm2)
    apply (erule exE)
    apply (rule corres_rel_imp)
    apply (rule corres_retype'[where g=id and ty=ty and sz = sz,OF not_zero aligned _ _ _ ko
           ,simplified update_gs_id[OF tp] modify_id_return,simplified])
        using assms
        apply (simp_all add: objBits_def no_gs_types_def)
  apply auto
  done

lemma init_arch_objects_APIType_map2:
  "init_arch_objects (APIType_map2 (Inr ty)) ptr bits sz refs =
     (case ty of APIObjectType _ \<Rightarrow> return ()
   | _ \<Rightarrow> init_arch_objects (APIType_map2 (Inr ty)) ptr bits sz refs)"
  apply (clarsimp split: ARM_HYP_H.object_type.split)
  apply (simp add: init_arch_objects_def APIType_map2_def
            split: apiobject_type.split)
  done

lemma copyGlobalMappings_corres:
  "corres dc (valid_arch_state and valid_etcbs and pspace_aligned and page_directory_at pd)
             (valid_arch_state' and page_directory_at' pd)
          (copy_global_mappings pd)
          (copyGlobalMappings pd)"
  apply (simp add: copy_global_mappings_def
                   copyGlobalMappings_def
                   objBits_simps archObjSize_def
                   pd_bits_def pdBits_def mapM_x_mapM)
  done

(* FIXME: move *)
lemma copyGlobalMappings_cte_wp_at[wp]:
  "\<lbrace>\<lambda>s. P (cte_wp_at' P' p s)\<rbrace>
     copyGlobalMappings pd
   \<lbrace>\<lambda>rv s. P (cte_wp_at' P' p s)\<rbrace>"
  apply (simp add: copyGlobalMappings_def)
  done

crunch ct[wp]: copyGlobalMappings "\<lambda>s. P (ksCurThread s)"
  (wp: setObject_ksPSpace_only updateObject_default_inv mapM_x_wp')

crunch ksCurDomain[wp]: copyGlobalMappings "\<lambda>s. P (ksCurDomain s)"
  (wp: setObject_ksPSpace_only updateObject_default_inv mapM_x_wp')

lemmas copyGlobalMappings_ctes_of[wp]
    = ctes_of_from_cte_wp_at[where Q="\<top>", simplified,
                             OF copyGlobalMappings_cte_wp_at]

lemmas object_splits =
  apiobject_type.split_asm
  ARM_HYP_H.object_type.split_asm
  sum.split_asm kernel_object.split_asm
  arch_kernel_object.split_asm

lemma ksMachineState_update_gs[simp]:
  "ksMachineState (update_gs tp us addrs s) = ksMachineState s"
  by (simp add: update_gs_def
         split: aobject_type.splits Structures_A.apiobject_type.splits)
lemma update_gs_ksMachineState_update_swap:
  "update_gs tp us addrs (ksMachineState_update f s) =
   ksMachineState_update f (update_gs tp us addrs s)"
  by (simp add: update_gs_def
         split: aobject_type.splits Structures_A.apiobject_type.splits)

declare hoare_in_monad_post[wp del]
declare univ_get_wp[wp del]
declare result_in_set_wp[wp del]

crunch valid_arch_state'[wp]: copyGlobalMappings "valid_arch_state'"
  (wp: crunch_wps)

lemma nullPointer_0_simp[simp]:
  "(nullPointer = 0) = True"
  by (simp add: nullPointer_def)

lemma descendants_of_retype':
  assumes P: "\<And>p. P p \<Longrightarrow> m p = None"
  shows "descendants_of' p (\<lambda>p. if P p then Some makeObject else m p) =
         descendants_of' p m"
  apply (rule set_eqI)
  apply (simp add: descendants_of'_def)
  apply (rule iffI)
   apply (erule subtree.induct)
    apply (rule direct_parent)
      apply (clarsimp simp: mdb_next_unfold makeObject_cte split: if_split_asm)
     apply assumption
    apply (clarsimp simp: parentOf_def makeObject_cte split: if_split_asm)
   apply (erule trans_parent)
     apply (clarsimp simp: mdb_next_unfold makeObject_cte split: if_split_asm)
    apply assumption
   apply (clarsimp simp: parentOf_def makeObject_cte split: if_split_asm)
  apply (erule subtree.induct)
   apply (rule direct_parent)
     apply (clarsimp simp: mdb_next_unfold dest!: P)
    apply assumption
   apply (fastforce simp: parentOf_def dest!: P)
  apply (erule trans_parent)
    apply (clarsimp simp: mdb_next_unfold dest!: P)
   apply assumption
  apply (fastforce simp: parentOf_def dest!: P)
  done

lemma capRange_Null [simp]: "capRange NullCap = {}"
  by (simp add: capRange_def)

end

locale retype_mdb = vmdb +
  fixes P n
  assumes P: "\<And>p. P p \<Longrightarrow> m p = None"
  assumes 0: "\<not>P 0"
  defines "n \<equiv> \<lambda>p. if P p then Some makeObject else m p"
begin
interpretation Arch . (*FIXME: arch_split*)

lemma no_0_n: "no_0 n"
  using no_0 by (simp add: no_0_def n_def 0)

lemma n_next:
  "n \<turnstile> c \<leadsto> c' = (if P c then c' = 0 else m \<turnstile> c \<leadsto> c')"
  by (simp add: mdb_next_unfold n_def makeObject_cte nullPointer_def)

lemma n_prev:
  "n \<turnstile> c \<leftarrow> c' = (if P c' then c = 0 else m \<turnstile> c \<leftarrow> c')"
  by (simp add: mdb_prev_def n_def makeObject_cte nullPointer_def)

lemma dlist_n: "valid_dlist n"
  using dlist no_0 no_0_n
  apply (simp add: valid_dlist_def2)
  apply (clarsimp simp: n_prev n_next)
  apply (rule conjI)
   apply clarsimp
   apply (erule allE, erule (1) impE)
   apply (erule_tac x=c' in allE)
   apply simp
   apply (drule P)
   apply (simp add: mdb_next_unfold)
  apply clarsimp
  apply (erule allE, erule (1) impE)
  apply (erule_tac x=c' in allE)
  apply simp
  apply (drule P)
  apply (simp add: mdb_prev_def)
  done

lemma n_next_trancl:
  "n \<turnstile> c \<leadsto>\<^sup>+ c' \<Longrightarrow> (if P c then c' = 0 else m \<turnstile> c \<leadsto>\<^sup>+ c')"
  apply (insert no_0_n chain)
  apply (erule trancl_induct)
   apply (fastforce simp: n_next)
  apply (simp split: if_split_asm)
   apply (clarsimp simp: mdb_next_unfold)
  apply (simp add: n_next split: if_split_asm)
  apply (simp add: mdb_chain_0_def)
  apply (drule_tac x=c in bspec)
   apply (drule tranclD)
   apply (clarsimp simp: mdb_next_unfold)
  apply assumption
  done

lemma next_not_P:
  "m \<turnstile> c \<leadsto> c' \<Longrightarrow> \<not>P c"
  by (clarsimp simp: mdb_next_unfold dest!: P)

lemma m_next_trancl:
  "m \<turnstile> c \<leadsto>\<^sup>+ c' \<Longrightarrow> n \<turnstile> c \<leadsto>\<^sup>+ c'"
  apply (erule trancl_induct)
   apply (rule r_into_trancl)
   apply (clarsimp simp: n_next)
   apply (drule next_not_P)
   apply simp
  apply (erule trancl_trans)
  apply (rule r_into_trancl)
  apply (clarsimp simp: n_next)
  apply (drule next_not_P)
  apply simp
  done

lemma P_to_0:
  "P c \<Longrightarrow> n \<turnstile> c \<leadsto>\<^sup>+ 0"
  by (rule r_into_trancl) (simp add: n_next)

lemma n_trancl_eq:
  "n \<turnstile> c \<leadsto>\<^sup>+ c' = (if P c then c' = 0 else m \<turnstile> c \<leadsto>\<^sup>+ c')"
  by (auto dest: m_next_trancl n_next_trancl P_to_0)

lemma n_rtrancl_eq:
  "n \<turnstile> c \<leadsto>\<^sup>* c' = (if P c then c' = 0 \<or> c = c' else m \<turnstile> c \<leadsto>\<^sup>* c')"
  by (auto simp: n_trancl_eq rtrancl_eq_or_trancl)

lemma dom_n:
  "dom n = dom m \<union> Collect P"
  by (auto simp add: n_def)

lemma mdb_chain_0_n: "mdb_chain_0 n"
  using chain
  by (auto simp: mdb_chain_0_def dom_n n_trancl_eq)

lemma n_Some_eq:
  "(n p = Some (CTE cap node)) =
  (if P p then cap = NullCap \<and> node = nullMDBNode
          else m p = Some (CTE cap node))"
  by (auto simp: n_def makeObject_cte)

lemma valid_badges_n: "valid_badges n"
proof -
  from valid
  have "valid_badges m" ..
  thus ?thesis
    apply (clarsimp simp: valid_badges_def)
    apply (simp add: n_Some_eq n_next split: if_split_asm)
    apply fastforce
    done
qed

lemma caps_contained_n: "caps_contained' n"
proof -
  from valid
  have "caps_contained' m" ..
  thus ?thesis
    apply (clarsimp simp: caps_contained'_def)
    apply (simp add: n_Some_eq split: if_split_asm)
    apply fastforce
    done
qed

lemma mdb_chunked_n: "mdb_chunked n"
proof -
  from valid
  have "mdb_chunked m" ..
  thus ?thesis
    apply (clarsimp simp: mdb_chunked_def)
    apply (simp add: n_Some_eq split: if_split_asm)
    apply (simp add: n_Some_eq n_trancl_eq n_rtrancl_eq is_chunk_def)
    apply fastforce
    done
qed

lemma descendants [simp]:
  "descendants_of' p n = descendants_of' p m"
  apply (unfold n_def)
  apply (subst descendants_of_retype')
   apply (erule P)
  apply (rule refl)
  done

lemma untyped_mdb_n: "untyped_mdb' n"
proof -
  from valid
  have "untyped_mdb' m" ..
  thus ?thesis
    apply (clarsimp simp: untyped_mdb'_def)
    apply (simp add: n_Some_eq split: if_split_asm)
    done
qed

lemma untyped_inc_n: "untyped_inc' n"
proof -
  from valid
  have "untyped_inc' m" ..
  thus ?thesis
    apply (clarsimp simp: untyped_inc'_def)
    apply (simp add: n_Some_eq split: if_split_asm)
    apply blast
    done
qed

lemma valid_nullcaps_n: "valid_nullcaps n"
proof -
  from valid
  have "valid_nullcaps m" ..
  thus ?thesis
    apply (clarsimp simp: valid_nullcaps_def)
    apply (simp add: n_Some_eq split: if_split_asm)
    done
qed

lemma ut_rev_n: "ut_revocable' n"
proof -
  from valid
  have "ut_revocable' m" ..
  thus ?thesis
    apply (clarsimp simp: ut_revocable'_def)
    apply (simp add: n_Some_eq split: if_split_asm)
    done
qed

lemma class_links_m:
  "class_links m"
  using valid by (simp add: valid_mdb_ctes_def)

lemma next_not_P2:
  "\<lbrakk> m \<turnstile> p \<leadsto> p'; p' \<noteq> nullPointer \<rbrakk> \<Longrightarrow> \<not> P p'"
  using dlist
  apply (clarsimp simp: mdb_next_unfold)
  apply (erule(1) valid_dlistE)
   apply clarsimp
  apply (clarsimp dest!: P)
  done

lemma class_links_n:
  "class_links n"
  using class_links_m
  apply (simp add: class_links_def)
  apply (elim allEI)
  apply clarsimp
  apply (subgoal_tac "p' \<noteq> nullPointer")
   apply (simp add: n_next split: if_split_asm)
   apply (case_tac cte, case_tac cte')
   apply (clarsimp simp add: n_Some_eq split: if_split_asm)
   apply (drule(1) next_not_P2)
   apply simp
  apply (clarsimp simp: no_0_n nullPointer_def)
  done

lemma irq_control_n:
  "irq_control n"
  apply (clarsimp simp add: irq_control_def)
  apply (simp add: n_Some_eq split: if_split_asm)
  apply (frule irq_revocable, rule irq_control)
  apply clarsimp
  apply (erule (1) irq_controlD, rule irq_control)
  done

lemma dist_z_m: "distinct_zombies m"
  using valid by auto

lemma dist_z_n: "distinct_zombies n"
  using dist_z_m
  apply (simp add: n_def distinct_zombies_def
                   distinct_zombie_caps_def
               split del: if_split)
  apply (erule allEI, erule allEI)
  apply (clarsimp split del: if_split)
  apply (clarsimp split: if_split_asm simp: makeObject_cte)
  apply (clarsimp simp: isCap_simps)
  done

lemma reply_masters_rvk_fb_m: "reply_masters_rvk_fb m"
  using valid by auto

lemma reply_masters_rvk_fb_n: "reply_masters_rvk_fb n"
  using reply_masters_rvk_fb_m
  by (simp add: n_def reply_masters_rvk_fb_def
                ball_ran_eq makeObject_cte isCap_simps)

lemma valid_n:
  "valid_mdb_ctes n"
  by (simp add: valid_mdb_ctes_def dlist_n no_0_n mdb_chain_0_n
                valid_badges_n caps_contained_n untyped_mdb_n
                untyped_inc_n mdb_chunked_n valid_nullcaps_n ut_rev_n
                class_links_n irq_control_n dist_z_n
                reply_masters_rvk_fb_n)

end

definition
  caps_no_overlap'' :: "word32 \<Rightarrow> nat \<Rightarrow> kernel_state \<Rightarrow> bool"
where
 "caps_no_overlap'' ptr sz s \<equiv> \<forall>cte \<in> ran (ctes_of s).
               untypedRange (cteCap cte) \<inter> {ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1} \<noteq> {}
               \<longrightarrow> {ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1} \<subseteq> untypedRange (cteCap cte)"

lemma obj_range'_subset:
  "\<lbrakk>range_cover ptr sz (objBitsKO val) n; ptr' \<in> set (new_cap_addrs n ptr val)\<rbrakk>
   \<Longrightarrow> obj_range' ptr' val \<subseteq> {ptr..(ptr && ~~ mask sz) + 2 ^ sz - 1}"
  unfolding obj_range'_def
  by (rule new_range_subset, auto)

lemma obj_range'_subset_strong:
  assumes "range_cover ptr sz (objBitsKO val) n"
      and "ptr' \<in> set (new_cap_addrs n ptr val)"
  shows "obj_range' ptr' val \<subseteq> {ptr..ptr + (of_nat n * 2 ^ objBitsKO val) - 1}"
proof -
  {
    assume cover: "range_cover ptr sz (objBitsKO val) n"
      and  mem_p: "ptr' \<in> set (new_cap_addrs n ptr val)"
      and  not_0: "n\<noteq> 0"
    note n_less = range_cover.range_cover_n_less[OF cover]
    have unat_of_nat_m1: "unat (of_nat n - (1::machine_word)) < n"
      using not_0 n_less by (simp add:unat_of_nat_minus_1)
    have decomp:
      "of_nat n * 2 ^ objBitsKO val =
       of_nat (n - 1) * 2 ^ objBitsKO val + (2 :: machine_word) ^ objBitsKO val"
      apply (simp add:distrib_right[where b = "1 :: machine_word",simplified,symmetric])
      using not_0 n_less
      apply simp
      done
    have "ptr' + 2 ^ objBitsKO val - 1 \<le> ptr + of_nat n * 2 ^ objBitsKO val - 1"
      using cover
      apply (subst decomp)
      apply (simp add:add.assoc[symmetric])
      apply (simp add:p_assoc_help)
      apply (rule order_trans[OF word_plus_mono_left word_plus_mono_right])
         using mem_p not_0
         apply (clarsimp simp:new_cap_addrs_def shiftl_t2n)
         apply (rule word_plus_mono_right)
          apply (subst mult.commute)
          apply (rule word_mult_le_mono1[OF word_of_nat_le])
            using n_less not_0
            apply (simp add:unat_of_nat_minus_1)
           apply (rule p2_gt_0[THEN iffD2])
           apply (simp add:word_bits_def range_cover_def)
          apply (simp only: word_bits_def[symmetric])
          apply (clarsimp simp: unat_of_nat_minus_1[OF n_less(1) not_0])
          apply (rule nat_less_power_trans2
            [OF range_cover.range_cover_le_n_less(2),OF cover, folded word_bits_def])
           apply (simp add:unat_of_nat_m1 less_imp_le)
          apply (simp add:range_cover_def word_bits_def)
         apply (rule machine_word_plus_mono_right_split[where sz = sz])
          using range_cover.range_cover_compare[OF cover,where p = "unat (of_nat n - (1::machine_word))"]
          apply (clarsimp simp:unat_of_nat_m1)
         apply (simp add:range_cover_def word_bits_def)
        apply (rule olen_add_eqv[THEN iffD2])
        apply (subst add.commute[where a = "2^objBitsKO val - 1"])
        apply (subst p_assoc_help[symmetric])
        apply (rule is_aligned_no_overflow)
        apply (clarsimp simp:range_cover_def word_bits_def)
        apply (erule aligned_add_aligned[OF _  is_aligned_mult_triv2]; simp)
       apply simp
      by (meson assms(1) is_aligned_add is_aligned_mult_triv2 is_aligned_no_overflow' range_cover_def)
  }
  with assms show ?thesis
    unfolding obj_range'_def
    apply -
    apply (frule(1) obj_range'_subset)
    apply (simp add: obj_range'_def)
    apply (cases "n = 0"; clarsimp simp:new_cap_addrs_def)
    done
qed

lemma caps_no_overlapD'':
  "\<lbrakk>cte_wp_at' (\<lambda>cap. cteCap cap = c) q s;caps_no_overlap'' ptr sz s\<rbrakk>
   \<Longrightarrow> untypedRange c \<inter> {ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1} \<noteq> {} \<longrightarrow>
       {ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1} \<subseteq> untypedRange c"
  apply (clarsimp simp: cte_wp_at_ctes_of isCap_simps caps_no_overlap''_def
        simp del:atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
        Int_atLeastAtMost atLeastatMost_empty_iff)
  apply (drule_tac x = cte in bspec)
    apply fastforce
  apply (erule(1) impE)
  apply blast
done

context begin interpretation Arch . (*FIXME: arch_split*)
lemma valid_untyped'_helper:
  assumes valid : "valid_cap' c s"
  and  cte_at : "cte_wp_at' (\<lambda>cap. cteCap cap = c) q s"
  and  cover  : "range_cover ptr sz (objBitsKO val) n"
  and  range  : "caps_no_overlap'' ptr sz s"
  and  pres   : "isUntypedCap c \<longrightarrow> usableUntypedRange c \<inter>  {ptr..ptr + of_nat n * 2 ^ objBitsKO val - 1} = {}"
  shows "\<lbrakk>pspace_aligned' s; pspace_distinct' s; pspace_no_overlap' ptr sz s\<rbrakk>
 \<Longrightarrow> valid_cap' c (s\<lparr>ksPSpace := foldr (\<lambda>addr. data_map_insert addr val) (new_cap_addrs n ptr val) (ksPSpace s)\<rparr>)"
  proof -
  note blah[simp del] = atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
        Int_atLeastAtMost atLeastatMost_empty_iff
  assume pn : "pspace_aligned' s" "pspace_distinct' s"
  and   no_overlap: "pspace_no_overlap' ptr sz s"
  show ?thesis
  using pn pres no_overlap valid cover cte_wp_at_ctes_of[THEN iffD1,OF cte_at]
        caps_no_overlapD''[OF cte_at range]
  apply (clarsimp simp:valid_cap'_def retype_ko_wp_at')
  apply (case_tac "cteCap cte"; simp add: valid_cap'_def cte_wp_at_obj_cases'
                                valid_pspace'_def retype_obj_at_disj'
                         split: zombie_type.split_asm)
   apply (rename_tac arch_capability)
   apply (case_tac arch_capability;
          simp add: retype_obj_at_disj' typ_at_to_obj_at_arches
                    page_table_at'_def page_directory_at'_def split del: if_splits)
    apply (fastforce simp: typ_at_to_obj_at_arches retype_obj_at_disj')
                           unfolding valid_untyped'_def
  apply (intro allI)
  apply (rule ccontr)
  apply clarify
  using cover[unfolded range_cover_def]
  apply (clarsimp simp:isCap_simps retype_ko_wp_at' split:if_split_asm)
   apply (thin_tac "\<forall>x. Q x" for Q)
   apply (frule aligned_untypedRange_non_empty)
    apply (simp add:isCap_simps)
   apply (elim disjE)
    apply (frule(1) obj_range'_subset)
    apply (erule impE)
     apply (drule(1) psubset_subset_trans)
     apply (drule Int_absorb1[OF psubset_imp_subset])
     apply (drule aligned_untypedRange_non_empty)
      apply (simp add:isCap_simps)
     apply (simp add:Int_ac)
    apply (drule(1) subset_trans)
    apply blast
   apply (frule(1) obj_range'_subset_strong)
   apply (drule(1) non_disjoing_subset)
   apply blast
  apply (thin_tac "\<forall>x. Q x" for Q)
  apply (frule aligned_untypedRange_non_empty)
   apply (simp add:isCap_simps)
  apply (frule(1) obj_range'_subset)
  apply (drule(1) subset_trans)
   apply (erule impE)
    apply clarsimp
    apply blast
   apply blast
  done
qed

definition caps_overlap_reserved' :: "word32 set \<Rightarrow> kernel_state \<Rightarrow> bool"
where
 "caps_overlap_reserved' S s \<equiv> \<forall>cte \<in> ran (ctes_of s).
  (isUntypedCap (cteCap cte) \<longrightarrow> usableUntypedRange (cteCap cte) \<inter> S = {})"

lemma createObjects_valid_pspace':
  assumes  mko: "makeObjectKO dev ty = Some val"
  and    not_0: "n \<noteq> 0"
  and    cover: "range_cover ptr sz (objBitsKO val + gbits) n"
  shows "\<lbrace>\<lambda>s. pspace_no_overlap' ptr sz s \<and> valid_pspace' s \<and> caps_no_overlap'' ptr sz s
            \<and> caps_overlap_reserved' {ptr .. ptr + of_nat (n * 2^gbits * 2 ^ objBitsKO val ) - 1} s
            \<and> ptr \<noteq> 0\<rbrace>
  createObjects' ptr n val gbits \<lbrace>\<lambda>r. valid_pspace'\<rbrace>"
  apply (cut_tac not_0)
  apply (simp add: split_def createObjects'_def
                   lookupAround2_pspace_no
                   alignError_def unless_def)
  apply (rule hoare_pre)
   apply (wp|simp cong: if_cong del: data_map_insert_def del:fun_upd_apply)+
   apply (wpc|wp)+
   apply (subst new_cap_addrs_fold')
     apply (simp add:unat_1_0 unat_gt_0)
     apply (rule range_cover_not_zero_shift[OF _  cover])
     apply simp+
   apply (subst new_cap_addrs_fold')
     apply (simp add:unat_1_0 unat_gt_0)
     apply (rule range_cover_not_zero_shift[OF _  cover])
     apply simp+
   apply (subst data_map_insert_def[symmetric])+
  apply (rule impI)
  apply (clarsimp simp: new_cap_addrs_fold'
                        valid_pspace'_def linorder_not_less
                        objBits_def[symmetric])
  apply (simp only: imp_disjL[symmetric] imp_conjL[symmetric] imp_ex[symmetric]
                    range_cover.unat_of_nat_n_shift[OF cover,where gbits=gbits,simplified])
proof (intro conjI impI)

  fix s

  assume pn: "pspace_no_overlap' ptr sz s"
     and vo: "valid_objs' s"
     and ad: "pspace_aligned' s" "pspace_distinct' s"
     and pc: "caps_no_overlap'' ptr sz s"
    and mdb: "valid_mdb' s"
    and p_0: "ptr \<noteq> 0"
    and reserved : "caps_overlap_reserved' {ptr..ptr + of_nat n *2 ^ gbits * 2 ^ objBitsKO val - 1} s"
    and no_0_obj': "no_0_obj' s"
  have obj': "objBitsKO val \<le> sz"
    using cover
    by (simp add:range_cover_def)

  let ?s' = "s\<lparr>ksPSpace := foldr (\<lambda>addr. data_map_insert addr val) (new_cap_addrs (n * 2 ^ gbits) ptr val) (ksPSpace s)\<rparr>"

  note cover' = range_cover_rel[where sbit' = "objBitsKO val",OF cover _ refl,simplified]

  note ad' = retype_aligned_distinct'[OF ad pn cover']

  note shift = range_cover.unat_of_nat_n_shift[OF cover,where gbits=gbits,simplified]

  have al: "is_aligned ptr (objBitsKO val)"
    using cover'
    by (simp add:range_cover_def)

  show pspace_aligned: "pspace_aligned' ?s'"
  using ad' range_cover.unat_of_nat_n_shift[OF cover,where gbits=gbits,simplified]
    by (simp add:field_simps)

  show "pspace_distinct' ?s'"
  using ad' shift
    by (simp add:field_simps)

  note obj_at_disj = retype_obj_at_disj' [OF ad pn cover']

  note obj_at_disj' = obj_at_disj [unfolded foldr_upd_app_if[folded data_map_insert_def]]

  have obj_atC: "\<And>P x. x \<in> set (new_cap_addrs (2 ^ gbits * n) ptr val) \<Longrightarrow> \<not> obj_at' P x s"
    apply (clarsimp simp: obj_at'_def)
    apply (drule subsetD [OF new_cap_addrs_subset [OF cover' ]])
    apply (insert pspace_no_overlap_disjoint' [OF ad(1) pn])
    apply (drule domI[where m = "ksPSpace s"])
    apply (drule(1) orthD2)
    apply (clarsimp simp:ptr_add_def p_assoc_help)
    done

  have valid_cap: "\<And>cap q. \<lbrakk> s \<turnstile>' cap; cte_wp_at' (\<lambda>cte. cteCap cte = cap) q s \<rbrakk>
                      \<Longrightarrow> ?s' \<turnstile>' cap"
     apply (rule valid_untyped'_helper[OF _ _ _ pc _ ad pn ])
          apply simp+
        apply (subst mult.commute)
        apply (rule cover')
       using reserved
     apply (clarsimp simp:caps_overlap_reserved'_def cte_wp_at_ctes_of)
     apply (drule_tac x = cte in bspec)
       apply fastforce
     apply simp
   done

  show valid_objs: "valid_objs' ?s'" using vo
    apply (clarsimp simp: valid_objs'_def
                          foldr_upd_app_if[folded data_map_insert_def]
                   elim!: ranE
                   split: if_split_asm)
     apply (insert sym[OF mko])[1]
     apply (clarsimp simp: makeObjectKO_def
                    split: bool.split_asm sum.split_asm
                           ARM_HYP_H.object_type.split_asm
                           apiobject_type.split_asm
                           kernel_object.split_asm
                           arch_kernel_object.split_asm)
    apply (drule bspec, erule ranI)
    apply (subst mult.commute)
    apply (case_tac obj; simp add: valid_obj'_def)
        apply (rename_tac endpoint)
        apply (case_tac endpoint; simp add: valid_ep'_def obj_at_disj')
       apply (rename_tac notification)
       apply (case_tac notification; simp add: valid_ntfn'_def valid_bound_tcb'_def obj_at_disj')
       apply (rename_tac ntfn xa)
       apply (case_tac ntfn, simp_all, (clarsimp simp: obj_at_disj' split:option.splits)+)
      apply (rename_tac tcb)
      apply (case_tac tcb, clarsimp simp add: valid_tcb'_def)
      apply (frule pspace_alignedD' [OF _ ad(1)])
      apply (frule pspace_distinctD' [OF _ ad(2)])
      apply (simp add: objBits_simps)
      apply (subst mult.commute)
      apply (intro conjI ballI)
       apply (clarsimp elim!: ranE)
       apply (rule valid_cap[unfolded foldr_upd_app_if[folded data_map_insert_def]])
        apply (fastforce)
       apply (rule_tac ptr="x + xa" in cte_wp_at_tcbI', assumption+)
        apply fastforce
       apply simp
      apply (rename_tac thread_state mcp priority bool option nat cptr vptr bound user_context)
      apply (case_tac thread_state, simp_all add: valid_tcb_state'_def
                                                  valid_bound_ntfn'_def obj_at_disj'
                                           split: option.splits)[2]
      apply (clarsimp simp add: valid_arch_tcb'_def typ_at_to_obj_at_arches obj_at_disj')
     apply (simp add: valid_cte'_def)
     apply (frule pspace_alignedD' [OF _ ad(1)])
     apply (frule pspace_distinctD' [OF _ ad(2)])
     apply (simp add: objBits_simps')
     apply (subst mult.commute)
     apply (erule valid_cap[unfolded foldr_upd_app_if[folded data_map_insert_def]])
     apply (erule(2) cte_wp_at_cteI'[unfolded cte_level_bits_def])
     apply simp
    apply (rename_tac arch_kernel_object)
    apply (case_tac arch_kernel_object; simp)
      apply (rename_tac asidpool)
      apply (case_tac asidpool, clarsimp simp: page_directory_at'_def
                                               typ_at_to_obj_at_arches
                                               obj_at_disj')
     apply (rename_tac pte)
     apply (case_tac pte; simp add: valid_mapping'_def)
    apply (rename_tac pde)
    apply (case_tac pde; simp add: valid_mapping'_def page_table_at'_def
                                   typ_at_to_obj_at_arches obj_at_disj')
   apply (rename_tac vcpu)
   apply (case_tac "vcpuTCBPtr vcpu";
          clarsimp simp: valid_vcpu'_def typ_at_to_obj_at'[where 'a=tcb, simplified]
                         typ_at_to_obj_at_arches obj_at_disj')
   done
  have not_0: "0 \<notin> set (new_cap_addrs (2 ^ gbits * n) ptr val)"
    using p_0
    apply clarsimp
    apply (drule subsetD [OF new_cap_addrs_subset [OF cover'],rotated])
    apply (clarsimp simp:ptr_add_def)
    done
  show "valid_mdb' ?s'"
    apply (simp add: valid_mdb'_def foldr_upd_app_if[folded data_map_insert_def])
    apply (subst mult.commute)
    apply (subst ctes_of_retype [OF mko ad])
        apply (rule ad'[unfolded foldr_upd_app_if[folded data_map_insert_def]])+
      apply (simp add: objBits_def[symmetric] new_cap_addrs_aligned [OF al])
     apply (rule ballI, drule subsetD [OF new_cap_addrs_subset [OF cover']])
     apply (insert pspace_no_overlap_disjoint' [OF ad(1) pn])
     apply (drule_tac x = x in orthD1)
       apply (simp add:ptr_add_def p_assoc_help)
     apply fastforce
    apply (fold makeObject_cte)
    apply (rule retype_mdb.valid_n)
    apply unfold_locales
      apply (rule mdb[unfolded valid_mdb'_def])
     apply (rule iffD2 [OF None_ctes_of_cte_at[unfolded cte_wp_at_obj_cases'], THEN sym])
     apply (rule notI)
     apply (elim disjE conjE, simp_all add: obj_atC)[1]
       apply (thin_tac "S \<inter> T = {}" for S T)
       apply (clarsimp simp: obj_at'_def projectKOs objBits_simps)
       apply (drule pspace_no_overlapD' [OF _ pn])
       apply (drule subsetD [OF new_cap_addrs_subset[OF cover']])
       apply (frule_tac ptr'=p in mask_in_range)
       apply (drule(1) tcb_cte_cases_aligned_helpers)
       apply (drule_tac x = p in orthD1)
         apply (clarsimp simp:objBits_simps)
       apply (clarsimp simp:ptr_add_def p_assoc_help)
      apply (frule new_range_subset[OF cover'])
      apply (drule bspec [OF new_cap_addrs_aligned[OF al]])
      apply (drule(1) disjoint_subset[rotated])
      apply (drule_tac a=p in equals0D)
      apply (frule_tac ptr'=p in mask_in_range)
      apply (insert sym [OF mko],
             clarsimp simp: objBits_simps makeObjectKO_def obj_at'_def)[1]
     apply (insert sym[OF mko] cover',
            clarsimp simp: obj_at'_def objBits_simps
                           makeObjectKO_def projectKOs)[1]
     apply (drule(1) tcb_cte_cases_aligned_helpers(2))
     apply clarsimp
     apply (drule subsetD [OF new_cap_addrs_subset,rotated])
       apply (simp add:objBits_simps)
     apply (drule orthD1)
       apply (fastforce simp:p_assoc_help ptr_add_def)
     apply fastforce
    apply (simp add: not_0)
    done

  have data_map_ext: "\<And>x y. data_map_insert x y = (\<lambda>m. m (x \<mapsto> y))"
    by (rule ext) simp
  show no_0_obj: "no_0_obj' ?s'"
    using not_0 no_0_obj'
    by (simp add: no_0_obj'_def data_map_ext field_simps foldr_upd_app_other)

qed

lemma createObjects_valid_pspace_untyped':
  assumes  mko: "makeObjectKO dev ty = Some val"
  and    not_0: "n \<noteq> 0"
  and    cover: "range_cover ptr sz (objBitsKO val + gbits) n"
  shows "\<lbrace>\<lambda>s. pspace_no_overlap' ptr sz s \<and> valid_pspace' s \<and> caps_no_overlap'' ptr sz s \<and> ptr \<noteq> 0
            \<and> caps_overlap_reserved' {ptr .. ptr + of_nat (n * 2^gbits * 2 ^ objBitsKO val ) - 1} s \<rbrace>
  createObjects' ptr n val gbits \<lbrace>\<lambda>r. valid_pspace'\<rbrace>"
  apply (wp createObjects_valid_pspace' [OF mko not_0 cover])
  apply simp
  done

crunch valid_objs'[wp]: copyGlobalMappings "valid_objs'"
  (ignore: storePDE wp: crunch_wps)
crunch pspace_aligned'[wp]: copyGlobalMappings "pspace_aligned'"
  (wp: crunch_wps)
crunch pspace_distinct'[wp]: copyGlobalMappings "pspace_distinct'"
  (wp: crunch_wps)

lemmas storePDE_valid_mdb[wp]
    = storePDE_ctes[where P=valid_mdb_ctes, folded valid_mdb'_def]
crunch valid_mdb[wp]: copyGlobalMappings "valid_mdb'"
  (wp: crunch_wps)

crunch no_0_obj' [wp]: copyGlobalMappings no_0_obj'
  (wp: crunch_wps)

lemma copyGlobalMappings_valid_pspace[wp]:
  "\<lbrace>valid_pspace'\<rbrace> copyGlobalMappings pd \<lbrace>\<lambda>rv. valid_pspace'\<rbrace>"
  by (simp add: valid_pspace'_def | wp)+

declare bleeding_obvious [simp]

lemma range_cover_new_cap_addrs_compare:
  assumes not_0: "n \<noteq> 0"
  and     cover: "range_cover ptr sz (objBitsKO val + gbits) n"
  and    ptr_in: "p \<in> set (new_cap_addrs (unat (((of_nat n)::word32) << gbits)) ptr val)"
  shows  "p \<le> ptr + of_nat (shiftL n (objBitsKO val + gbits) - Suc 0)"
proof -
  note unat_of_nat_shift = range_cover.unat_of_nat_n_shift[OF cover,where gbits=gbits,simplified]
  have cover' :"range_cover ptr sz (objBitsKO val) (n*2^gbits)"
    by (rule range_cover_rel[OF cover],simp+)
  have upbound:" unat ((((of_nat n)::word32) * 2 ^ gbits)) * unat ((2::word32) ^ objBitsKO val) < 2 ^ word_bits"
    using range_cover.range_cover_le_n_less[OF cover' le_refl] cover'
    apply -
    apply (drule nat_less_power_trans)
     apply (simp add:range_cover_def)
    apply (fold word_bits_def)
    using unat_of_nat_shift not_0
    apply (simp add:field_simps shiftl_t2n)
    done
  have not_0': "(2::word32) ^ (objBitsKO val + gbits) * of_nat n \<noteq> 0"
    apply (rule range_cover_not_zero_shift[OF not_0,unfolded shiftl_t2n,OF _ le_refl])
    apply (rule range_cover_rel[OF cover]; simp)
    done
  have "gbits < word_bits"
    using cover
    by (simp add:range_cover_def word_bits_def)
  thus ?thesis
    apply -
    apply (insert not_0 cover ptr_in)
    apply (frule range_cover.range_cover_le_n_less[OF _ le_refl])
    apply (fold word_bits_def)
    apply (simp add:shiftL_nat )
    apply (simp add:range_cover.unat_of_nat_n_shift)
    apply (clarsimp simp:new_cap_addrs_def shiftl_t2n)
    apply (rename_tac pa)
    apply (rule word_plus_mono_right)
     apply (rule order_trans)
      apply (subst mult.commute)
      apply (rule word_mult_le_iff[THEN iffD2])
         apply (clarsimp simp:p2_gt_0 range_cover_def word_bits_def)
        apply (drule range_cover_rel[where sbit' = "0"])
          apply (simp+)[2]
        apply (erule less_le_trans[OF range_cover.range_cover_le_n_less(2)])
         apply (clarsimp simp:field_simps power_add)
         apply (rule unat_le_helper)
         apply (rule of_nat_mono_maybe_le[THEN iffD1])
           using range_cover.range_cover_le_n_less[OF cover' le_refl]
           apply (simp_all only:word_bits_def[symmetric])
        apply simp
       apply (drule nat_less_power_trans)
        apply (simp add:range_cover_def word_bits_def)
       apply (rule less_le_trans[OF mult_less_mono1])
         apply (rule unat_mono)
         apply (rule_tac y1= "pa" in  of_nat_mono_maybe'[THEN iffD1,rotated -1])
           apply (assumption)
          apply (simp add:word_bits_def)
         apply (simp add:word_bits_def)
        apply simp
       using unat_of_nat_shift
       apply (simp add:field_simps shiftl_t2n)
      apply simp
     apply (rule word_less_sub_1)
     apply (simp add:power_add field_simps)
     apply (subst mult.assoc[symmetric])
     apply (rule word_mult_less_mono1)
       apply (rule word_of_nat_less)
       using unat_of_nat_shift
       apply (simp add:shiftl_t2n field_simps)
      apply (meson less_exp objBitsKO_bounded2 of_nat_less_pow_32 word_gt_a_gt_0)
     using upbound
     apply (simp add:word_bits_def)
    apply (rule machine_word_plus_mono_right_split[where sz = sz])
     apply (rule less_le_trans[rotated -1])
      apply (rule range_cover.range_cover_compare_bound[OF cover'])
     apply (simp add: unat_minus_one[OF not_0'])
     using range_cover.unat_of_nat_n_shift[OF cover le_refl]
     apply (simp add:shiftl_t2n power_add field_simps)
    apply (simp add:range_cover_def word_bits_def)
    done
qed

lemma createObjects_orig_ko_wp_at2':
  "\<lbrace>\<lambda>s. range_cover ptr sz (objBitsKO val + gbits) n \<and> n \<noteq> 0
      \<and> pspace_aligned' s \<and> pspace_distinct' s
      \<and> P (ko_wp_at' P' p s)
      \<and> (P' val \<longrightarrow> P True)
      \<and> pspace_no_overlap' ptr sz s\<rbrace>
  createObjects' ptr n val gbits \<lbrace>\<lambda>r s. P (ko_wp_at' P' p s)\<rbrace>"
   apply (simp add: createObjects'_def lookupAround2_pspace_no
                    alignError_def unless_def split_def del:fun_upd_apply)
   apply (rule hoare_grab_asm)+
   apply (subst new_cap_addrs_fold')
     apply (drule range_cover_not_zero_shift[rotated])
     apply (rule le_add2)
     apply (simp add:word_le_sub1 del:fun_upd_apply)+
   apply (rule hoare_pre)
    apply (wp|simp cong: if_cong del: data_map_insert_def fun_upd_apply)+
   apply (wpc|wp)+
   apply (clarsimp simp:valid_pspace'_def linorder_not_less simp del:fun_upd_apply)
   apply (subgoal_tac " range_cover ptr sz (objBitsKO val) (unat (of_nat n << gbits))")
    apply (subst data_map_insert_def[symmetric])+
    apply (subst retype_ko_wp_at',simp+)+
    apply clarsimp
   apply (cases "P' val")
    apply simp
   apply clarsimp
   apply (frule(1) subsetD [OF new_cap_addrs_subset])
   apply (drule(1) pspace_no_overlap_disjoint')
   apply (simp add:lookupAround2_None1)
   apply (intro conjI impI allI)
     apply (drule_tac x = p in spec)
     apply (erule impE)
      apply (erule(1) range_cover_new_cap_addrs_compare[rotated])
      apply simp
     apply (fastforce simp: ko_wp_at'_def)
   apply (drule_tac x = p in orthD1)
   apply (clarsimp simp:ptr_add_def p_assoc_help)
   apply (simp add:dom_def)
   apply (fastforce simp:ko_wp_at'_def)
  apply (rule range_cover_rel)
     apply (simp)+
  apply (subst mult.commute)
  apply (erule range_cover.unat_of_nat_n_shift)
  apply simp
  done


lemma createObjects_orig_obj_at2':
  "\<lbrace>\<lambda>s. n \<noteq> 0
      \<and> range_cover ptr sz (objBitsKO val + gbits) n
      \<and> pspace_aligned' s \<and> pspace_distinct' s
      \<and> P (obj_at' P' p s)
      \<and> \<not> (case_option False P' (projectKO_opt val))
      \<and> pspace_no_overlap' ptr sz s\<rbrace>
  createObjects' ptr n val gbits \<lbrace>\<lambda>r s. P (obj_at' P' p s)\<rbrace>"
  unfolding obj_at'_real_def
  by (wp createObjects_orig_ko_wp_at2') auto

lemma createObjects_orig_cte_wp_at2':
  "\<lbrace>\<lambda>s. P (cte_wp_at' P' p s)
      \<and> n \<noteq> 0
      \<and> range_cover ptr sz (objBitsKO val + gbits) n
      \<and> pspace_aligned' s \<and> pspace_distinct' s
      \<and> \<not> (case_option False P' (projectKO_opt val))
      \<and> (\<forall>(getF, setF) \<in> ran tcb_cte_cases.
              \<not> (case_option False (P' \<circ> getF) (projectKO_opt val)))
      \<and> pspace_no_overlap' ptr sz s\<rbrace>
  createObjects' ptr n val gbits \<lbrace>\<lambda>r s. P (cte_wp_at' P' p s)\<rbrace>"
  apply (simp add: cte_wp_at'_obj_at')
  apply (rule handy_prop_divs)
   apply (wp createObjects_orig_obj_at2'[where sz = sz], simp)
  apply (simp add: tcb_cte_cases_def)
  including no_pre
  apply (wp handy_prop_divs createObjects_orig_obj_at2'[where sz = sz]
             | simp add: o_def cong: option.case_cong)+
  done

lemma threadSet_cte_wp_at2'T:
  assumes "\<forall>tcb. \<forall>(getF, setF) \<in> ran tcb_cte_cases. getF (F tcb) = getF tcb"
  shows "\<lbrace>\<lambda>s. P (cte_wp_at' P' p s)\<rbrace> threadSet F t \<lbrace>\<lambda>rv s. P (cte_wp_at' P' p s)\<rbrace>"
  using assms by (rule threadSet_cte_wp_at'T)

lemmas threadSet_cte_wp_at2' =
  threadSet_cte_wp_at2'T [OF all_tcbI, OF ball_tcb_cte_casesI]

lemma createNewCaps_cte_wp_at2:
  "\<lbrace>\<lambda>s. P (cte_wp_at' P' p s) \<and> \<not> P' makeObject
      \<and> n \<noteq> 0
      \<and> range_cover ptr sz (APIType_capBits ty objsz) n
      \<and> pspace_aligned' s \<and> pspace_distinct' s
      \<and> pspace_no_overlap' ptr sz s\<rbrace>
     createNewCaps ty ptr n objsz dev
   \<lbrace>\<lambda>rv s. P (cte_wp_at' P' p s)\<rbrace>"
  including no_pre
  apply (simp add: createNewCaps_def createObjects_def ARM_HYP_H.toAPIType_def
           split del: if_split)
  apply (case_tac ty; simp add: createNewCaps_def createObjects_def Arch_createNewCaps_def
                           split del: if_split cong: if_cong)
        apply (rename_tac apiobject_type)
        apply (case_tac apiobject_type; simp split del: if_split)
            apply (rule hoare_pre, wp, simp add:createObjects_def)
           apply ((wp createObjects_orig_cte_wp_at2'[where sz = sz]
                     mapM_x_wp' threadSet_cte_wp_at2')+
                   | assumption
                   | clarsimp simp: APIType_capBits_def
                                    projectKOs projectKO_opts_defs
                                    makeObject_tcb tcb_cte_cases_def
                                    archObjSize_def vspace_bits_defs
                                    createObjects_def curDomain_def
                                    Let_def objBits_if_dev
                         split del: if_split
                   | simp add: objBits_simps)+
  done

lemma createObjects_orig_obj_at':
  "\<lbrace>\<lambda>s. n \<noteq> 0
      \<and> range_cover ptr sz (objBitsKO val + gbits) n
      \<and> pspace_aligned' s \<and> pspace_distinct' s
      \<and> obj_at' P p s
      \<and> pspace_no_overlap' ptr sz s\<rbrace>
  createObjects' ptr n val gbits \<lbrace>\<lambda>r. obj_at' P p\<rbrace>"
   apply (rule hoare_grab_asm)+
   apply (clarsimp simp: createObjects'_def)
   apply (subst new_cap_addrs_fold')
     apply (simp add:unat_1_0 unat_gt_0)
     apply (rule range_cover_not_zero_shift)
     apply simp+
    apply (wp|simp add:split_def cong: if_cong del: data_map_insert_def fun_upd_apply)+
   apply (simp add: alignError_def del: fun_upd_apply | wpc|wp)+
  apply (clarsimp simp del:fun_upd_apply)
  apply (subst data_map_insert_def[symmetric])+
  apply (subgoal_tac "range_cover ptr sz (objBitsKO val) (unat (of_nat n << gbits))")
  apply (subst retype_obj_at',simp+)+
  apply (intro conjI impI allI)
    apply (clarsimp simp:obj_at'_real_def ko_wp_at'_def)
    apply (frule(1) subsetD [OF new_cap_addrs_subset])
    apply (drule(1) pspace_no_overlap_disjoint')
   apply (simp add:lookupAround2_None1)
     apply (drule_tac x = p in spec)
     apply (erule impE)
      apply (erule(1) range_cover_new_cap_addrs_compare[rotated])
       apply simp
     apply simp
  apply (frule(1) subsetD [OF new_cap_addrs_subset])
  apply (drule(1) pspace_no_overlap_disjoint')
   apply (drule_tac x = p in orthD1)
   apply (clarsimp simp:ptr_add_def p_assoc_help)
   apply (simp add:dom_def obj_at'_real_def ko_wp_at'_def)
  apply (rule range_cover_rel)
     apply (simp)+
  apply (subst mult.commute)
  apply (erule range_cover.unat_of_nat_n_shift)
  apply simp
  done

lemma createObjects_orig_cte_wp_at':
  "\<lbrace>\<lambda>s. range_cover ptr sz (objBitsKO val + gbits) n \<and> n \<noteq> 0
      \<and> pspace_aligned' s \<and> pspace_distinct' s
      \<and> cte_wp_at' P p s
      \<and> pspace_no_overlap' ptr sz s\<rbrace>
  createObjects' ptr n val gbits \<lbrace>\<lambda>r s. cte_wp_at' P p s\<rbrace>"
  apply (simp add: cte_wp_at'_obj_at' tcb_cte_cases_def)
  apply (rule hoare_pre, wp hoare_vcg_disj_lift createObjects_orig_obj_at'[where sz = sz])
  apply clarsimp
  done

lemma createNewCaps_cte_wp_at':
  "\<lbrace>\<lambda>s. cte_wp_at' P p s
      \<and> range_cover ptr sz (APIType_capBits ty us) n \<and> n \<noteq> 0
      \<and> pspace_aligned' s \<and> pspace_distinct' s
      \<and> pspace_no_overlap' ptr sz s\<rbrace>
     createNewCaps ty ptr n us dev
   \<lbrace>\<lambda>rv. cte_wp_at' P p\<rbrace>"
  apply (simp add: createNewCaps_def ARM_HYP_H.toAPIType_def
              split del: if_split)
  apply (case_tac ty; simp add: Arch_createNewCaps_def
                           split del: if_split)
        apply (rename_tac apiobject_type)
        apply (case_tac apiobject_type; simp split del: if_split)
            apply (rule hoare_pre, wp, simp)
           apply (wp createObjects_orig_cte_wp_at'[where sz = sz] mapM_x_wp'
                     threadSet_cte_wp_at'T
                  | clarsimp simp: objBits_simps APIType_capBits_def createObjects_def curDomain_def
                    vspace_bits_defs archObjSize_def
                  | intro conjI impI
                  | force simp: tcb_cte_cases_def)+
  done

lemma createObjects_obj_at_other:
  assumes cover: "range_cover ptr sz (objBitsKO val + gbits) n"
  and     not_0: "n\<noteq> 0"
  shows  "\<lbrace>\<lambda>s. obj_at' P p s \<and> valid_pspace' s \<and> pspace_no_overlap' ptr sz s\<rbrace>
  createObjects ptr n val gbits \<lbrace>\<lambda>_. obj_at' P p\<rbrace>"
  apply (simp add: createObjects_def)
  apply (wp createObjects_orig_obj_at'[where sz = sz])
  using cover not_0
  apply (clarsimp simp: cover not_0 valid_pspace'_def pspace_no_overlap'_def)
  done

lemma valid_cap'_range_no_overlap:
  "\<lbrakk>untypedRange c \<inter> {ptr..(ptr && ~~ mask sz) + 2 ^ sz - 1} = {}; s \<turnstile>' c;
    valid_pspace' s; pspace_no_overlap' ptr sz s;
    range_cover ptr sz (objBitsKO val) n\<rbrakk>
   \<Longrightarrow> s\<lparr>ksPSpace := foldr (\<lambda>addr. data_map_insert addr val)
                           (new_cap_addrs n ptr val) (ksPSpace s)\<rparr> \<turnstile>' c"
  apply (cases c; simp add: valid_cap'_def cte_wp_at_obj_cases' valid_pspace'_def retype_obj_at_disj'
                       split: zombie_type.split_asm
                       del: Int_atLeastAtMost)[1]
  apply (rename_tac arch_capability)
  apply (case_tac arch_capability;
          simp add: retype_obj_at_disj' typ_at_to_obj_at_arches
                    page_table_at'_def page_directory_at'_def)
   apply (fastforce simp: typ_at_to_obj_at_arches retype_obj_at_disj')
  apply (rename_tac word nat1 nat2)
  apply (clarsimp simp:valid_untyped'_def retype_ko_wp_at'
        simp del: atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
        Int_atLeastAtMost atLeastatMost_empty_iff)
  apply (frule aligned_untypedRange_non_empty)
   apply (simp add:isCap_simps)
  apply (intro conjI impI)
   apply (intro allI)
   apply (drule_tac x = ptr' in spec)
   apply (rule ccontr)
   apply (clarsimp simp del: atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
                             Int_atLeastAtMost atLeastatMost_empty_iff)
   apply (erule disjE)
    apply (drule(2) disjoint_subset2 [OF obj_range'_subset])
    apply (drule(1) disjoint_subset2[OF psubset_imp_subset])
    apply (simp add: Int_absorb ptr_add_def p_assoc_help
                del: atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
                     Int_atLeastAtMost atLeastatMost_empty_iff)
   apply (drule(1) obj_range'_subset)
   apply (drule_tac A'=" {word + of_nat nat2..word + 2 ^ nat1 - 1}" in disjoint_subset[rotated])
    apply clarsimp
    apply (rule is_aligned_no_wrap')
     apply (fastforce simp:capAligned_def)
    apply (erule of_nat_less_pow_32)
    apply (simp add:capAligned_def)
   apply (drule(1) disjoint_subset2)
   apply blast
  apply (intro allI)
  apply (drule_tac x = ptr' in spec)
  apply (rule ccontr)
  apply (clarsimp simp del: atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
                            Int_atLeastAtMost atLeastatMost_empty_iff)
  apply (drule(2) disjoint_subset2 [OF obj_range'_subset])
  apply (drule(1) disjoint_subset2)
  apply (simp add: Int_absorb ptr_add_def p_assoc_help
              del: atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
                   Int_atLeastAtMost atLeastatMost_empty_iff)
  done

lemma createObjects_valid_cap':
  "\<lbrace>valid_cap' c and valid_pspace' and pspace_no_overlap' ptr sz and
    K (untypedRange c \<inter> {ptr .. (ptr && ~~ mask sz) + 2^sz - 1} = {} \<and>
      range_cover ptr sz (objBitsKO val + gbits) n \<and> n \<noteq> 0)\<rbrace>
  createObjects' ptr n val gbits
  \<lbrace>\<lambda>_. valid_cap' c\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: createObjects'_def lookupAround2_pspace_no
                    alignError_def unless_def split_def)
  apply (subst new_cap_addrs_fold')
   apply (simp add:unat_1_0 unat_gt_0)
   apply (rule range_cover_not_zero_shift)
     apply fastforce+
  apply (rule hoare_pre)
   apply (wp|simp cong: if_cong del: data_map_insert_def fun_upd_apply)+
     apply (clarsimp simp: linorder_not_less valid_pspace'_def)
  apply (wpc|wp)+
  apply (subst data_map_insert_def[symmetric])+
  apply clarsimp
  apply (subgoal_tac " range_cover ptr sz (objBitsKO val) (unat (of_nat n << gbits))")
   apply (subst range_cover.unat_of_nat_n_shift,simp+)+
   apply (subst (asm) range_cover.unat_of_nat_n_shift,simp+)+
   apply (intro conjI impI allI)
    apply (erule(4) valid_cap'_range_no_overlap)+
  apply (rule range_cover_rel)
    apply (simp)+
  apply (subst mult.commute)
  apply (erule range_cover.unat_of_nat_n_shift)
  apply simp
  done

lemma createObjects_cte_wp_at':
  "\<lbrakk>range_cover ptr sz (objBitsKO val + gbits) n; n \<noteq> 0\<rbrakk>
  \<Longrightarrow>\<lbrace>\<lambda>s. cte_wp_at' P p s \<and> valid_pspace' s \<and> pspace_no_overlap' ptr sz s\<rbrace>
  createObjects' ptr n val gbits
  \<lbrace>\<lambda>_. cte_wp_at' P p\<rbrace>"
  apply (clarsimp simp: valid_def cte_wp_at_obj_cases')
  apply (erule disjE)
   apply (erule use_valid[OF _ ])
    apply (rule createObjects_orig_obj_at')
   apply fastforce
  apply clarsimp
  apply (drule_tac x = na in bspec)
   apply clarsimp
  apply clarsimp
  apply (drule use_valid[OF _ createObjects_orig_obj_at'])
   apply fastforce
  apply simp
  done

lemma createNewCaps_cte_wp_at:
  assumes cover: "range_cover ptr sz (APIType_capBits ty us) n"
  and not_0 : "n \<noteq> 0"
  shows "\<lbrace>\<lambda>s. cte_wp_at' P p s \<and> valid_pspace' s \<and> pspace_no_overlap' ptr sz s\<rbrace>
  createNewCaps ty ptr n us dev
  \<lbrace>\<lambda>_. cte_wp_at' P p\<rbrace>"
  apply (wp createNewCaps_cte_wp_at')
  apply (auto simp: cover not_0)
  done

lemma createObjects_ret2:
  "\<lbrace>(\<lambda>s. P (map (\<lambda>p. ptr_add y (p * 2 ^ (objBitsKO ko + gbits)))
                    [0..<n]))
        and K (n < 2 ^ word_bits \<and> n \<noteq> 0)\<rbrace>
      createObjects y n ko gbits \<lbrace>\<lambda>rv s. P rv\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (rule hoare_chain)
    apply (rule hoare_vcg_conj_lift)
     apply (rule createObjects_ret)
      apply simp+
    apply (rule hoare_vcg_prop)
   defer
   apply (clarsimp simp: power_add mult.commute mult.left_commute | assumption)+
  done

lemma state_refs_ko_wp_at_eq:
  "state_refs_of' s = (\<lambda>x. {r. ko_wp_at' (\<lambda>ko. r \<in> refs_of' ko) x s})"
  apply (rule ext)
  apply (simp add: state_refs_of'_def ko_wp_at'_def
            split: option.split)
  done

lemma state_hyp_refs_ko_wp_at_eq:
  "state_hyp_refs_of' s = (\<lambda>x. {r. ko_wp_at' (\<lambda>ko. r \<in> hyp_refs_of' ko) x s})"
  apply (rule ext)
  apply (simp add: state_hyp_refs_of'_def ko_wp_at'_def
            split: option.split)
  done

lemma createObjects_state_refs_of'':
  "\<lbrace>\<lambda>s. n \<noteq> 0
        \<and> range_cover ptr sz (objBitsKO val + gbits) n
        \<and> P (state_refs_of' s) \<and> refs_of' val = {}
        \<and> pspace_aligned' s \<and> pspace_distinct' s
        \<and> pspace_no_overlap' ptr sz s\<rbrace>
     createObjects' ptr n val gbits
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
   apply (clarsimp simp:valid_def lookupAround2_pspace_no state_refs_ko_wp_at_eq)
   apply (erule ssubst[where P = P,rotated])
   apply (rule ext)
   apply (rule set_eqI)
   apply clarsimp
   apply (intro iffI,rule ccontr)
     apply (drule_tac P1="\<lambda>x. \<not> x" in use_valid[OF _ createObjects_orig_ko_wp_at2'[where sz = sz]])
     apply simp
     apply (intro conjI)
     apply simp+
   apply (drule_tac P1="\<lambda>x. x" in use_valid[OF _ createObjects_orig_ko_wp_at2'[where sz = sz]])
     apply simp+
  done

lemma createObjects_state_hyp_refs_of'':
  "\<lbrace>\<lambda>s. n \<noteq> 0
        \<and> range_cover ptr sz (objBitsKO val + gbits) n
        \<and> P (state_hyp_refs_of' s) \<and> hyp_refs_of' val = {}
        \<and> pspace_aligned' s \<and> pspace_distinct' s
        \<and> pspace_no_overlap' ptr sz s\<rbrace>
     createObjects' ptr n val gbits
   \<lbrace>\<lambda>rv s. P (state_hyp_refs_of' s)\<rbrace>"
   apply (clarsimp simp:valid_def lookupAround2_pspace_no state_hyp_refs_ko_wp_at_eq)
   apply (erule ssubst[where P = P,rotated])
   apply (rule ext)
   apply (rule set_eqI)
   apply clarsimp
   apply (intro iffI,rule ccontr)
     apply (drule_tac P1="\<lambda>x. \<not> x" in use_valid[OF _ createObjects_orig_ko_wp_at2'[where sz = sz]])
     apply simp
     apply (intro conjI)
     apply simp+
   apply (drule_tac P1="\<lambda>x. x" in use_valid[OF _ createObjects_orig_ko_wp_at2'[where sz = sz]])
     apply simp+
  done

crunch state_hyp_refs_of'[wp]: copyGlobalMappings "\<lambda>s. P (state_hyp_refs_of' s)"
  (wp: crunch_wps)

crunch state_refs_of'[wp]: copyGlobalMappings "\<lambda>s. P (state_refs_of' s)"
  (wp: crunch_wps)

lemma createNewCaps_state_refs_of':
  assumes cover: "range_cover ptr sz (APIType_capBits ty us) n"
  and     not_0: "n \<noteq> 0"
  shows
  "\<lbrace>\<lambda>s. valid_pspace' s \<and> pspace_no_overlap' ptr sz s
        \<and> P (state_refs_of' s)\<rbrace>
     createNewCaps ty ptr n us dev
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  unfolding createNewCaps_def
  apply (clarsimp simp: ARM_HYP_H.toAPIType_def
             split del: if_split)
  apply (cases ty; simp add: createNewCaps_def Arch_createNewCaps_def
                        split del: if_split)
        apply (rename_tac apiobject_type)
        apply (case_tac apiobject_type; simp split del: if_split)
            apply (rule hoare_pre, wp, simp)
           apply (insert cover not_0)
           apply(wp mapM_x_wp' createObjects_state_refs_of'' threadSet_state_refs_of'
                    | simp add: not_0 pspace_no_overlap'_def objBitsKO_def APIType_capBits_def
                                valid_pspace'_def makeObject_tcb makeObject_endpoint objBits_def
                                makeObject_notification vspace_bits_defs
                                archObjSize_def createObjects_def curDomain_def
             | intro conjI impI)+
  done

(* FIXME move to KHeap_R *)
lemma  doMachineOp_hyp_bit:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of' s)\<rbrace>
      doMachineOp m
   \<lbrace>\<lambda>rv s. P (state_hyp_refs_of' s)\<rbrace>"
  by (simp add: doMachineOp_def split_def | wp)+

lemma createNewCaps_state_hyp_refs_of':
  assumes cover: "range_cover ptr sz (APIType_capBits ty us) n"
  and     not_0: "n \<noteq> 0"
  shows
  "\<lbrace>\<lambda>s. valid_pspace' s \<and> pspace_no_overlap' ptr sz s
        \<and> P (state_hyp_refs_of' s)\<rbrace>
     createNewCaps ty ptr n us dev
   \<lbrace>\<lambda>rv s. P (state_hyp_refs_of' s)\<rbrace>"
  unfolding createNewCaps_def
  apply (clarsimp simp: ARM_HYP_H.toAPIType_def
             split del: if_split)
  apply (cases ty; simp add: createNewCaps_def Arch_createNewCaps_def
                        split del: if_split)
        apply (rename_tac apiobject_type)
        apply (case_tac apiobject_type; simp split del: if_split)
            apply (rule hoare_pre, wp, simp)
           apply (insert cover not_0)
           apply (wp mapM_x_wp' createObjects_state_hyp_refs_of'' threadSet_state_hyp_refs_of' doMachineOp_hyp_bit
                    | simp add: not_0 pspace_no_overlap'_def objBitsKO_def APIType_capBits_def
                                valid_pspace'_def makeObject_tcb makeObject_vcpu objBits_def
                                vspace_bits_defs newArchTCB_def vcpu_tcb_refs'_def makeVCPUObject_def
                                archObjSize_def createObjects_def curDomain_def
             | intro conjI impI)+
  done

lemma createObjects_iflive':
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s \<and> \<not> live' val
        \<and> n \<noteq> 0
        \<and> range_cover ptr sz (objBitsKO val + gbits) n
        \<and> pspace_aligned' s \<and> pspace_distinct' s
        \<and> pspace_no_overlap' ptr sz s\<rbrace>
     createObjects' ptr n val gbits
   \<lbrace>\<lambda>rv s. if_live_then_nonz_cap' s\<rbrace>"
  apply (rule hoare_pre)
   apply (simp only: if_live_then_nonz_cap'_def
                     ex_nonz_cap_to'_def imp_conv_disj)
   apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift
             hoare_vcg_ex_lift createObjects_orig_ko_wp_at2'
             createObjects_orig_cte_wp_at')
  apply clarsimp
  apply (intro conjI allI impI)
  apply simp_all
  apply (rule ccontr)
  apply clarsimp
  apply (drule(1) if_live_then_nonz_capE')
  apply (fastforce simp: ex_nonz_cap_to'_def)
  done

crunch ksReadyQueues[wp]: copyGlobalMappings "\<lambda>s. P (ksReadyQueues s)"
  (wp: updateObject_default_inv crunch_wps)
crunch ksReadyQueuesL1[wp]: copyGlobalMappings "\<lambda>s. P (ksReadyQueuesL1Bitmap s)"
  (wp: updateObject_default_inv crunch_wps)
crunch ksReadyQueuesL2[wp]: copyGlobalMappings "\<lambda>s. P (ksReadyQueuesL2Bitmap s)"
  (wp: updateObject_default_inv crunch_wps)

crunch valid_idle'[wp]: copyGlobalMappings "valid_idle'"
  (simp: objBits_simps archObjSize_def
     wp: updateObject_default_inv crunch_wps setObject_idle' refl)

crunch iflive'[wp]: copyGlobalMappings "if_live_then_nonz_cap'"
  (wp: crunch_wps)

lemma createNewCaps_iflive'[wp]:
  assumes cover: "range_cover ptr sz (APIType_capBits ty us) n"
  and     not_0: "n \<noteq> 0"
  shows
  "\<lbrace>\<lambda>s. valid_pspace' s \<and> pspace_no_overlap' ptr sz s
        \<and> if_live_then_nonz_cap' s\<rbrace>
     createNewCaps ty ptr n us dev
   \<lbrace>\<lambda>rv s. if_live_then_nonz_cap' s\<rbrace>"
  unfolding createNewCaps_def
  apply (insert cover)
  apply (clarsimp simp: toAPIType_def ARM_HYP_H.toAPIType_def)
  apply (cases ty, simp_all add: createNewCaps_def Arch_createNewCaps_def
                      split del: if_split)
        apply (rename_tac apiobject_type)
        apply (case_tac apiobject_type, simp_all split del: if_split)[1]
            apply (rule hoare_pre, wp, simp)
           apply (wp mapM_x_wp' createObjects_iflive' threadSet_iflive'
                | simp add: not_0 pspace_no_overlap'_def createObjects_def live'_def hyp_live'_def
                            valid_pspace'_def makeObject_tcb makeObject_endpoint
                            makeObject_notification objBitsKO_def newArchTCB_def arch_live'_def
                            APIType_capBits_def objBits_def makeObject_vcpu makeVCPUObject_def
                                 archObjSize_def vspace_bits_defs
                                 curDomain_def split del:if_split
                | simp split: if_split
                | fastforce)+
  done

lemma createObjects_pspace_only:
  "\<lbrakk> \<And>f s. P (ksPSpace_update f s) = P s \<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace> createObjects' ptr n val gbits \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: createObjects_def createObjects'_def unless_def alignError_def
                   split_def lookupAround2_pspace_no)
  apply wpsimp
  done

lemma createObjects'_qs[wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueues s)\<rbrace> createObjects' ptr n val gbits \<lbrace>\<lambda>rv s. P (ksReadyQueues s)\<rbrace>"
  by (rule createObjects_pspace_only, simp)

lemma createObjects'_qsL1[wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueuesL1Bitmap s)\<rbrace> createObjects' ptr n val gbits \<lbrace>\<lambda>rv s. P (ksReadyQueuesL1Bitmap s)\<rbrace>"
  by (rule createObjects_pspace_only, simp)

lemma createObjects'_qsL2[wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueuesL2Bitmap s)\<rbrace> createObjects' ptr n val gbits \<lbrace>\<lambda>rv s. P (ksReadyQueuesL2Bitmap s)\<rbrace>"
  by (rule createObjects_pspace_only, simp)

(* FIXME move these 2 to TcbAcc_R *)
lemma threadSet_qsL1[wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueuesL1Bitmap s)\<rbrace> threadSet f t \<lbrace>\<lambda>rv s. P (ksReadyQueuesL1Bitmap s)\<rbrace>"
  by (simp add: threadSet_def | wp updateObject_default_inv)+

lemma threadSet_qsL2[wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueuesL2Bitmap s)\<rbrace> threadSet f t \<lbrace>\<lambda>rv s. P (ksReadyQueuesL2Bitmap s)\<rbrace>"
  by (simp add: threadSet_def | wp updateObject_default_inv)+

crunches createObjects, createNewCaps
  for qs[wp]: "\<lambda>s. P (ksReadyQueues s)"
  and qsL1[wp]: "\<lambda>s. P (ksReadyQueuesL1Bitmap s)"
  and qsL2[wp]: "\<lambda>s. P (ksReadyQueuesL2Bitmap s)"
  (simp: crunch_simps wp: crunch_wps)

lemma sch_act_wf_lift_asm:
  assumes tcb: "\<And>P t. \<lbrace>st_tcb_at' P t and Q \<rbrace> f \<lbrace>\<lambda>rv. st_tcb_at' P t\<rbrace>"
  assumes tcbDomain: "\<And>P t. \<lbrace>obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t and Q\<rbrace> f \<lbrace>\<lambda>rv. obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t\<rbrace>"
  assumes kCT: "\<And>P. \<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksCurThread s)\<rbrace>"
  assumes kCD: "\<And>P. \<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksCurDomain s)\<rbrace>"
  assumes ksA: "\<And>P. \<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksSchedulerAction s)\<rbrace>"
  shows
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s \<and> Q s\<rbrace>
  f
  \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (frule use_valid [OF _ ksA])
   prefer 2
   apply assumption
  apply (frule_tac P1="(=) (ksCurThread s)" in use_valid [OF _ kCT])
   apply (rule refl)
  apply (frule_tac P1="(=) (ksCurDomain s)" in use_valid [OF _ kCD])
   apply (rule refl)
  apply (case_tac "ksSchedulerAction s")
    apply (simp add: ct_in_state'_def)
    apply (drule use_valid [OF _ tcb])
     apply simp
    apply simp
   apply simp
  apply (clarsimp simp: tcb_in_cur_domain'_def)
  apply (frule use_valid [OF _ tcb], fastforce)
  apply (frule use_valid [OF _ tcbDomain], fastforce)
  apply auto
  done

lemma valid_queues_lift_asm':
  assumes tat: "\<And>d p t. \<lbrace>\<lambda>s. \<not> obj_at' (inQ d p) t s \<and> Q d p s\<rbrace> f \<lbrace>\<lambda>_ s. \<not> obj_at' (inQ d p) t s\<rbrace>"
  and     prq: "\<And>P. \<lbrace>\<lambda>s. P (ksReadyQueues s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksReadyQueues s)\<rbrace>"
  shows   "\<lbrace>\<lambda>s. valid_queues' s \<and> (\<forall>d p. Q d p s)\<rbrace> f \<lbrace>\<lambda>_. valid_queues'\<rbrace>"
  apply (simp only: valid_queues'_def imp_conv_disj)
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift
            tat prq)
  apply simp
  done

lemma createObjects'_ct[wp]:
  "\<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace> createObjects' p n v us \<lbrace>\<lambda>rv s. P (ksCurThread s)\<rbrace>"
  by (rule createObjects_pspace_only, simp)

crunches createObjects, doMachineOp, createNewCaps
  for ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  and ct[wp]: "\<lambda>s. P (ksCurThread s)"
  (ignore: clearMemory simp: unless_def crunch_simps wp: crunch_wps)

lemma copyGlobalMappings_ko_wp_at:
  "\<lbrace>(\<lambda>s. P (ko_wp_at' P' p s)) and K (\<forall>pde_x :: pde. P' (injectKO pde_x) = v)\<rbrace>
     copyGlobalMappings pd
   \<lbrace>\<lambda>rv s. P (ko_wp_at' P' p s)\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: copyGlobalMappings_def storePDE_def)
  done

lemma threadSet_ko_wp_at2':
  "\<lbrace>\<lambda>s. P (ko_wp_at' P' p s) \<and> (\<forall>tcb_x :: tcb. P' (injectKO (F tcb_x)) = P' (injectKO tcb_x))\<rbrace>
     threadSet F ptr
   \<lbrace>\<lambda>_ s. P (ko_wp_at' P' p s)\<rbrace>"
apply (simp add: threadSet_def split del: if_split)
apply (wp setObject_ko_wp_at getObject_tcb_wp | simp add: objBits_simps')+
apply (auto simp: ko_wp_at'_def obj_at'_def projectKOs)
done

lemma threadSet_ko_wp_at2'_futz:
  "\<lbrace>\<lambda>s. P (ko_wp_at' P' p s) \<and> obj_at' Q ptr s
         \<and> (\<forall>tcb_x :: tcb. Q tcb_x \<longrightarrow> P' (injectKO (F tcb_x)) = P' (injectKO tcb_x))\<rbrace>
     threadSet F ptr
   \<lbrace>\<lambda>_ s. P (ko_wp_at' P' p s)\<rbrace>"
apply (simp add: threadSet_def split del: if_split)
apply (wp setObject_ko_wp_at getObject_tcb_wp | simp add: objBits_simps')+
apply (auto simp: ko_wp_at'_def obj_at'_def projectKOs)
done

lemma mapM_x_threadSet_createNewCaps_futz:
  "\<lbrace>\<lambda>s. P (ko_wp_at' P' p s) \<and> (\<forall>addr\<in>set addrs. obj_at' (\<lambda>tcb. \<not>tcbQueued tcb \<and> tcbState tcb = Inactive) addr s)
         \<and> (\<forall>tcb_x :: tcb. tcbQueued (F tcb_x) = tcbQueued tcb_x \<and> tcbState (F tcb_x) = tcbState tcb_x)
         \<and> (\<forall>tcb_x :: tcb. \<not> tcbQueued tcb_x \<and> tcbState tcb_x = Inactive \<longrightarrow> P' (injectKO (F tcb_x)) = P' (injectKO tcb_x))\<rbrace>
     mapM_x (threadSet F) addrs
   \<lbrace>\<lambda>_ s. P (ko_wp_at' P' p s)\<rbrace>" (is "\<lbrace>?PRE\<rbrace> _ \<lbrace>\<lambda>_. ?POST\<rbrace>")
apply (rule mapM_x_inv_wp[where P="?PRE"])
  apply simp
 apply (rule hoare_pre)
  apply (wp hoare_vcg_ball_lift threadSet_ko_wp_at2'[where P="id", simplified]
      | wp (once) threadSet_ko_wp_at2'_futz[where Q="\<lambda>tcb. \<not>tcbQueued tcb \<and> tcbState tcb = Inactive"]
      | simp)+
done

lemma createObjects_makeObject_not_tcbQueued:
  assumes "range_cover ptr sz (objBitsKO tcb) n"
  assumes "n \<noteq> 0" "tcb = injectKO (makeObject::tcb)"
  shows "\<lbrace>\<lambda>s. pspace_no_overlap' ptr sz s \<and> pspace_aligned' s \<and> pspace_distinct' s\<rbrace>
           createObjects ptr n tcb 0
         \<lbrace>\<lambda>rv s. \<forall>addr\<in>set rv. obj_at' (\<lambda>tcb. \<not> tcbQueued tcb \<and> tcbState tcb = Structures_H.thread_state.Inactive) addr s\<rbrace>"
  apply (rule hoare_strengthen_post[OF createObjects_ko_at_strg[where 'a=tcb]])
  using assms
  apply (auto simp: obj_at'_def projectKO_opt_tcb objBitsKO_def
                    objBits_def makeObject_tcb)
  done

lemma createObjects_ko_wp_at2:
  "\<lbrace>\<lambda>s. range_cover ptr sz (objBitsKO ko + gbits) n \<and> n \<noteq> 0
      \<and> pspace_aligned' s \<and> pspace_distinct' s
      \<and> P (ko_wp_at' P' p s)
      \<and> (P' ko \<longrightarrow> P True)
      \<and> pspace_no_overlap' ptr sz s\<rbrace>
    createObjects ptr n ko gbits
   \<lbrace>\<lambda>_ s. P (ko_wp_at' P' p s)\<rbrace>"
apply (simp add: createObjects_def)
apply (wp createObjects_orig_ko_wp_at2')
apply auto
done

crunch ko_wp_at_'_P[wp]: doMachineOp "\<lambda>s. P (ko_wp_at' P' t s)"

lemma createNewCaps_ko_wp_atQ':
  "\<lbrace>(\<lambda>s. P (ko_wp_at' P' p s)
       \<and> range_cover ptr sz (APIType_capBits ty us) n \<and> n \<noteq> 0
       \<and> pspace_aligned' s \<and> pspace_distinct' s
       \<and> pspace_no_overlap' ptr sz s)
       and K (\<forall>pde_x :: pde. P' (injectKO pde_x)
                   \<longrightarrow> (\<forall>pde_y :: pde. P' (injectKO pde_y)))
       and K (\<forall>d (tcb_x :: tcb). \<not>tcbQueued tcb_x \<and> tcbState tcb_x = Inactive
                   \<longrightarrow> P' (injectKO (tcb_x \<lparr> tcbDomain := d \<rparr>)) = P' (injectKO tcb_x))
       and K (\<forall>v. makeObjectKO d (Inr ty) = Some v
                 \<longrightarrow> P' v \<longrightarrow> P True)\<rbrace>
     createNewCaps ty ptr n us d
   \<lbrace>\<lambda>rv s. P (ko_wp_at' P' p s)\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp: createNewCaps_def ARM_HYP_H.toAPIType_def
             split del: if_split)
  apply (cases ty, simp_all add: Arch_createNewCaps_def
                      split del: if_split)
        apply (rename_tac apiobject_type)
        apply (case_tac apiobject_type, simp_all split del: if_split)[1]
            apply (rule hoare_pre, wp, simp)
           apply (wp mapM_x_threadSet_createNewCaps_futz
                     mapM_x_wp'
                     createObjects_obj_at
                     createObjects_ko_wp_at2 createObjects_makeObject_not_tcbQueued
                     copyGlobalMappings_ko_wp_at[where v="\<forall>pde :: pde. P' (injectKO pde)"]
                   | simp add: makeObjectKO_def objBitsKO_def archObjSize_def APIType_capBits_def
                               objBits_def vspace_bits_defs curDomain_def
                            split del: if_split
                   | intro conjI impI | fastforce
                   | split if_split_asm)+
  done


lemmas createNewCaps_ko_wp_at'
    = createNewCaps_ko_wp_atQ'[simplified, unfolded fold_K]

lemmas createNewCaps_obj_at2 =
   createNewCaps_ko_wp_at'
      [where P'="\<lambda>ko. \<exists>obj :: ('a :: pspace_storable).
                   projectKO_opt ko = Some obj \<and> P' obj" for P',
       folded obj_at'_real_def,
       unfolded pred_conj_def, simplified]

lemma createNewCaps_obj_at'':
  "\<lbrace>\<lambda>s. obj_at' (P :: ('a :: pspace_storable) \<Rightarrow> bool) p s
       \<and> range_cover ptr sz (APIType_capBits ty us) n \<and> n \<noteq> 0
       \<and> pspace_aligned' s \<and> pspace_distinct' s
       \<and> pspace_no_overlap' ptr sz s
       \<and> (koType(TYPE('a)) = koType(TYPE(pde))
               \<longrightarrow> (\<forall>x. P x)
                \<and> (\<forall>pde :: pde. \<exists>x :: 'a. injectKO x = injectKO pde))
       \<and> (\<forall>tcb d. \<not>tcbQueued tcb \<and> tcbState tcb = Inactive \<longrightarrow> ((\<exists>obj :: 'a. injectKOS obj = KOTCB (tcb\<lparr>tcbDomain := d\<rparr>) \<and> P obj) \<longleftrightarrow> (\<exists>obj :: 'a. injectKOS obj = KOTCB tcb \<and> P obj)))\<rbrace>
     createNewCaps ty ptr n us d
   \<lbrace>\<lambda>rv s. obj_at' P p s\<rbrace>"
  apply (simp add: obj_at'_real_def)
  apply (wp createNewCaps_ko_wp_at')
  apply clarsimp
  apply (intro conjI impI)
    apply simp+
    apply clarsimp
  apply (clarsimp simp: projectKOs dest!: iffD1 [OF project_koType, OF exI])
  apply (clarsimp simp:project_inject)+
done

lemma createNewCaps_obj_at':
  "\<lbrace>\<lambda>s. obj_at' (P :: ('a :: pspace_storable) \<Rightarrow> bool) p s
       \<and> range_cover ptr sz (APIType_capBits ty us) n \<and> n \<noteq> 0
       \<and> pspace_aligned' s \<and> pspace_distinct' s
       \<and> pspace_no_overlap' ptr sz s
       \<and> koType(TYPE('a)) \<noteq> koType(TYPE(pde))
       \<and> (\<forall>tcb d. \<not>tcbQueued tcb \<and> tcbState tcb = Inactive \<longrightarrow> ((\<exists>obj :: 'a. injectKOS obj = KOTCB (tcb\<lparr>tcbDomain := d\<rparr>) \<and> P obj) \<longleftrightarrow> (\<exists>obj :: 'a. injectKOS obj = KOTCB tcb \<and> P obj)))\<rbrace>
     createNewCaps ty ptr n us d
   \<lbrace>\<lambda>rv s. obj_at' P p s\<rbrace>"
  by (wp createNewCaps_obj_at'', auto)

lemmas createNewCaps_pred_tcb_at'
     = createNewCaps_obj_at'[where P="\<lambda>ko. (Q :: 'a :: type \<Rightarrow> bool) (proj (tcb_to_itcb' ko))" for Q proj,
                             folded pred_tcb_at'_def, simplified]

lemma createNewCaps_cur:
  "\<lbrakk>range_cover ptr sz (APIType_capBits ty us) n ; n \<noteq> 0\<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s. valid_pspace' s \<and>
        pspace_no_overlap' ptr sz s \<and>
        cur_tcb' s\<rbrace>
      createNewCaps ty ptr n us d
   \<lbrace>\<lambda>rv. cur_tcb'\<rbrace>"
  apply (rule hoare_post_imp [where Q="\<lambda>rv s. \<exists>t. ksCurThread s = t \<and> tcb_at' t s"])
   apply (simp add: cur_tcb'_def)
  apply (wp hoare_vcg_ex_lift createNewCaps_obj_at')
  apply (clarsimp simp: pspace_no_overlap'_def cur_tcb'_def valid_pspace'_def)
  apply auto
  done

crunch ksInterrupt[wp]: createNewCaps "\<lambda>s. P (ksInterruptState s)"
  (simp: crunch_simps unless_def
   wp: setObject_ksInterrupt updateObject_default_inv crunch_wps
   ignore: clearMemoryVM)

lemma createNewCaps_ifunsafe':
  "\<lbrace>\<lambda>s. valid_pspace' s \<and>
        pspace_no_overlap' ptr sz s \<and>
        range_cover ptr sz (APIType_capBits ty us) n \<and> n \<noteq> 0 \<and>
        if_unsafe_then_cap' s\<rbrace>
      createNewCaps ty ptr n us d
   \<lbrace>\<lambda>rv s. if_unsafe_then_cap' s\<rbrace>"
  apply (simp only: if_unsafe_then_cap'_def ex_cte_cap_to'_def
                    imp_conv_disj)
  apply (rule hoare_pre)
   apply (rule hoare_use_eq_irq_node' [OF createNewCaps_ksInterrupt])
   apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift
             createNewCaps_cte_wp_at2 hoare_vcg_ex_lift)
  apply (simp add: makeObject_cte pspace_no_overlap'_def
                   valid_pspace'_def)
  apply auto
  done

lemma createObjects_nosch'[wp]:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace>
     createObjects' ptr n val gbits
   \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  by (rule createObjects_pspace_only, simp)

crunches copyGlobalMappings, createObjects, createNewCaps
  for nosch[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  and it[wp]: "\<lambda>s. P (ksIdleThread s)"
  (wp: setObject_ksPSpace_only updateObject_default_inv mapM_x_wp')

lemma createObjects_idle':
  "\<lbrace>valid_idle' and valid_pspace' and pspace_no_overlap' ptr sz
        and (\<lambda>s. \<not> case_option False (\<lambda>cte. ksIdleThread s \<in> capRange (cteCap cte))
                        (projectKO_opt val)
               \<and> (\<forall>(getF, setF) \<in> ran tcb_cte_cases.
                 \<not> case_option False (\<lambda>tcb. ksIdleThread s \<in> capRange (cteCap (getF tcb)))
                        (projectKO_opt val)))
        and K (range_cover ptr sz (objBitsKO val + gbits) n  \<and> n \<noteq> 0)\<rbrace>
  createObjects' ptr n val gbits
  \<lbrace>\<lambda>rv. valid_idle'\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (rule hoare_pre)
   apply (clarsimp simp add: valid_idle'_def pred_tcb_at'_def)
   apply (rule hoare_vcg_conj_lift)
    apply (rule hoare_as_subst [OF createObjects'_it])
    apply (wp createObjects_orig_obj_at'
              createObjects_orig_cte_wp_at2'
              hoare_vcg_all_lift | simp)+
  apply (clarsimp simp: valid_idle'_def projectKOs o_def
                        pred_tcb_at'_def valid_pspace'_def
                  cong: option.case_cong)
  apply auto
  done

lemma createNewCaps_idle'[wp]:
  "\<lbrace>valid_idle' and valid_pspace' and pspace_no_overlap' ptr sz
       and K (range_cover ptr sz (APIType_capBits ty us) n \<and> n \<noteq> 0)\<rbrace>
   createNewCaps ty ptr n us d
   \<lbrace>\<lambda>rv. valid_idle'\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (clarsimp simp: createNewCaps_def ARM_HYP_H.toAPIType_def
             split del: if_split)
  apply (cases ty, simp_all add: Arch_createNewCaps_def
                      split del: if_split)
         apply (rename_tac apiobject_type)
         apply (case_tac apiobject_type, simp_all split del: if_split)[1]
             apply (wp, simp)
           including no_pre
           apply (wp mapM_x_wp'
                     createObjects_idle'
                     threadSet_idle'
                   | simp add: projectKO_opt_tcb projectKO_opt_cte
                               makeObject_cte makeObject_tcb archObjSize_def
                               tcb_cte_cases_def objBitsKO_def APIType_capBits_def
                               vspace_bits_defs objBits_def
                               createObjects_def
                   | intro conjI impI
                   | fastforce simp: curDomain_def)+
  done

crunch ksArch[wp]: createNewCaps "\<lambda>s. P (ksArchState s)"
  (simp: crunch_simps unless_def wp: crunch_wps)
crunch it[wp]: createNewCaps "\<lambda>s. P (ksIdleThread s)"
  (simp: crunch_simps unless_def wp: crunch_wps updateObject_default_inv)
crunch gsMaxObjectSize[wp]: createNewCaps "\<lambda>s. P (gsMaxObjectSize s)"
  (simp: crunch_simps unless_def wp: crunch_wps updateObject_default_inv)

lemma createNewCaps_global_refs':
  "\<lbrace>\<lambda>s. range_cover ptr sz (APIType_capBits ty us) n \<and> n \<noteq> 0
       \<and> pspace_aligned' s \<and> pspace_distinct' s
       \<and> pspace_no_overlap' ptr sz s \<and> valid_global_refs' s
       \<and> 0 < gsMaxObjectSize s\<rbrace>
     createNewCaps ty ptr n us d
   \<lbrace>\<lambda>rv. valid_global_refs'\<rbrace>"
  apply (simp add: valid_global_refs'_def valid_cap_sizes'_def valid_refs'_def)
  apply (rule_tac Q="\<lambda>rv s. \<forall>ptr. \<not> cte_wp_at' (\<lambda>cte. (kernel_data_refs \<inter> capRange (cteCap cte) \<noteq> {}
        \<or> 2 ^ capBits (cteCap cte) > gsMaxObjectSize s)) ptr s \<and> global_refs' s \<subseteq> kernel_data_refs"
                 in hoare_post_imp)
   apply (auto simp: cte_wp_at_ctes_of linorder_not_less elim!: ranE)[1]
  apply (rule hoare_pre)
   apply (simp add: global_refs'_def)
   apply (rule hoare_use_eq [where f=ksArchState, OF createNewCaps_ksArch])
   apply (rule hoare_use_eq [where f=ksIdleThread, OF createNewCaps_it])
   apply (rule hoare_use_eq [where f=irq_node', OF createNewCaps_ksInterrupt])
   apply (rule hoare_use_eq [where f=gsMaxObjectSize], wp)
   apply (wp hoare_vcg_all_lift createNewCaps_cte_wp_at2[where sz=sz])
  apply (clarsimp simp: cte_wp_at_ctes_of global_refs'_def
                        makeObject_cte)
  apply (auto simp: linorder_not_less ball_ran_eq)
  done

lemma koTypeOf_eq_UserDataT:
  "(koTypeOf ko = UserDataT)
        = (ko = KOUserData)"
  by (cases ko, simp_all)

lemma createNewCaps_valid_arch_state:
  "\<lbrace>(\<lambda>s. valid_arch_state' s \<and> valid_pspace' s \<and> pspace_no_overlap' ptr sz s
        \<and> (tp = APIObjectType ArchTypes_H.CapTableObject \<longrightarrow> us > 0))
       and K (range_cover ptr sz (APIType_capBits ty us) n \<and> n \<noteq> 0)\<rbrace>
     createNewCaps ty ptr n us d
   \<lbrace>\<lambda>rv. valid_arch_state'\<rbrace>"
  apply (simp add: valid_arch_state'_def valid_asid_table'_def valid_global_pts'_def
                   page_table_at'_def page_directory_at'_def option_case_all_conv)
   apply (wpsimp wp: hoare_vcg_prop createNewCaps_ko_wp_at' createNewCaps_obj_at''
                     hoare_vcg_all_lift hoare_vcg_imp_lift
          simp: typ_at_to_obj_at_arches o_def is_vcpu'_def)
  apply (fastforce simp: valid_pspace'_def o_def pred_conj_def)
  done

lemma valid_irq_handlers_cte_wp_at_form':
  "valid_irq_handlers' = (\<lambda>s. \<forall>irq. irq_issued' irq s \<or>
                               (\<forall>p. \<not> cte_wp_at' (\<lambda>cte. cteCap cte = IRQHandlerCap irq) p s))"
  by (auto simp: valid_irq_handlers'_def cteCaps_of_def cte_wp_at_ctes_of
                 fun_eq_iff ran_def)

lemma createNewCaps_irq_handlers':
  "\<lbrace>valid_irq_handlers' and pspace_no_overlap' ptr sz
       and pspace_aligned' and pspace_distinct'
       and K (range_cover ptr sz (APIType_capBits ty us) n \<and> n \<noteq> 0)\<rbrace>
     createNewCaps ty ptr n us d
   \<lbrace>\<lambda>rv. valid_irq_handlers'\<rbrace>"
  apply (simp add: valid_irq_handlers_cte_wp_at_form' irq_issued'_def)
   apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift
             createNewCaps_cte_wp_at2)
  apply (clarsimp simp: makeObject_cte)
  apply auto
  done

lemma valid_pde_mappings'_def3:
  "valid_pde_mappings' =
     (\<lambda>s. \<forall>x. \<not> obj_at' (Not \<circ> valid_pde_mapping' (x && mask pdBits)) x s)"
  apply (simp add: valid_pde_mappings'_def)
  apply (rule ext, rule iff_allI)
  apply (auto simp: obj_at'_def projectKOs)
  done

lemma createObjects'_pde_mappings'[wp]:
  "\<lbrace>\<lambda>s. valid_pde_mappings' s \<and> range_cover ptr sz (objBitsKO val + gbits) n  \<and> n \<noteq> 0
            \<and> pspace_aligned' s \<and> pspace_distinct' s
            \<and> pspace_no_overlap' ptr sz s
            \<and> (\<forall>pde. projectKO_opt val = Some pde \<longrightarrow> pde = InvalidPDE)\<rbrace>
       createObjects' ptr n val gbits
   \<lbrace>\<lambda>_. valid_pde_mappings'\<rbrace>"
  apply (simp only: valid_pde_mappings'_def3 all_simps(1)[symmetric])
  apply (rule hoare_vcg_all_lift)
  apply (wp createObjects_orig_obj_at2')
  apply (clarsimp simp: projectKO_opt_pde o_def
                 split: Structures_H.kernel_object.split_asm
                        arch_kernel_object.split_asm)
  apply auto
  done

lemma createObjects_pde_mappings'[wp]:
  "\<lbrace>\<lambda>s. valid_pde_mappings' s \<and> range_cover ptr sz (objBitsKO ko + gbits) n  \<and> n \<noteq> 0
            \<and> pspace_aligned' s \<and> pspace_distinct' s
            \<and> pspace_no_overlap' ptr sz s
            \<and> (\<forall>pde. projectKO_opt ko = Some pde \<longrightarrow> pde = InvalidPDE)\<rbrace>
       createObjects ptr n ko gbits
   \<lbrace>\<lambda>_. valid_pde_mappings'\<rbrace>"
  by (simp add: createObjects_def objBits_def | intro conjI | wp | clarsimp)+

lemma copyGlobalMappings_pde_mappings':
  "\<lbrace>valid_pde_mappings' and K (is_aligned pd pdBits)\<rbrace> copyGlobalMappings pd \<lbrace>\<lambda>rv. valid_pde_mappings'\<rbrace>"
  apply (simp add: copyGlobalMappings_def objBits_simps archObjSize_def)
  apply wpsimp
  done

lemma mapM_x_copyGlobalMappings_pde_mappings':
  "\<lbrace>valid_pde_mappings' and K (\<forall>x \<in> set xs. is_aligned x pdBits)\<rbrace>
      mapM_x copyGlobalMappings xs \<lbrace>\<lambda>rv. valid_pde_mappings'\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (rule hoare_strengthen_post)
   apply (rule mapM_x_wp [OF _ subset_refl])
   apply (wp copyGlobalMappings_pde_mappings' | simp)+
  done

lemma createNewCaps_pde_mappings'[wp]:
  "\<lbrace>\<lambda>s. valid_pde_mappings' s \<and> range_cover ptr sz (APIType_capBits ty us) n \<and> n \<noteq> 0
            \<and> valid_arch_state' s
            \<and> pspace_aligned' s \<and> pspace_distinct' s
            \<and> pspace_no_overlap' ptr sz s\<rbrace>
       createNewCaps ty ptr n us d
   \<lbrace>\<lambda>_. valid_pde_mappings'\<rbrace>"
  apply (simp add: createNewCaps_def Arch_createNewCaps_def Let_def
              split del: if_split cong: option.case_cong
                                        object_type.case_cong)
  apply (rule hoare_pre)
   apply (wp mapM_x_copyGlobalMappings_pde_mappings' | wpc
         | simp split del: if_split)+
    apply (rule_tac P="range_cover ptr sz (APIType_capBits ty us) n \<and> n\<noteq> 0" in hoare_gen_asm)
    apply (rule hoare_strengthen_post)
     apply (rule createObjects_aligned, simp+)
        apply (simp add: objBits_simps vspace_bits_defs archObjSize_def APIType_capBits_def range_cover_def)
       apply (rule range_cover.range_cover_n_less[where 'a=32, folded word_bits_def],fastforce+)
     apply (simp add: objBits_simps vspace_bits_defs archObjSize_def APIType_capBits_def range_cover_def word_bits_def)+
   apply (wp mapM_x_wp[OF _ subset_refl] | wpc | simp add: curDomain_def)+
  apply (clarsimp simp: projectKOs)
  apply (simp add: objBits_simps pdBits_def pageBits_def archObjSize_def APIType_capBits_def)
  apply (case_tac ty; simp)
        apply (rename_tac apiobject_type)
        apply (case_tac apiobject_type)
  apply (auto simp: ARM_HYP_H.toAPIType_def objBits_simps vspace_bits_defs
                    makeObject_pde valid_arch_state'_def page_directory_at'_def)
  done

lemma createObjects'_irq_states' [wp]:
  "\<lbrace>valid_irq_states'\<rbrace> createObjects' a b c d \<lbrace>\<lambda>_. valid_irq_states'\<rbrace>"
  apply (simp add: createObjects'_def split_def)
  apply (wp unless_wp|wpc|simp add: alignError_def)+
  apply fastforce
  done

crunch irq_states' [wp]: createNewCaps valid_irq_states'
  (wp: crunch_wps no_irq no_irq_clearMemory simp: crunch_simps unless_def)

crunch ksMachine[wp]: createObjects "\<lambda>s. P (ksMachineState s)"
  (simp: crunch_simps unless_def)
crunch cur_domain[wp]: createObjects "\<lambda>s. P (ksCurDomain s)"
  (simp: unless_def)

lemma createNewCaps_valid_queues':
  "\<lbrace>valid_queues' and pspace_no_overlap' ptr sz
       and pspace_aligned' and pspace_distinct'
       and K (range_cover ptr sz (APIType_capBits ty us) n \<and> n \<noteq> 0)\<rbrace>
     createNewCaps ty ptr n us d
   \<lbrace>\<lambda>rv. valid_queues'\<rbrace>"
  apply (wp valid_queues_lift_asm' [OF createNewCaps_obj_at2])
  apply (clarsimp simp: projectKOs)
  apply (simp add: makeObjectKO_def
            split: object_type.split_asm
                   apiobject_type.split_asm)
  apply (clarsimp simp: inQ_def)
  apply (auto simp: makeObject_tcb
             split: object_type.splits apiobject_type.splits)
  done

lemma createNewCaps_valid_queues:
  "\<lbrace>valid_queues and pspace_no_overlap' ptr sz
       and pspace_aligned' and pspace_distinct'
       and K (range_cover ptr sz (APIType_capBits ty us) n \<and> n \<noteq> 0)\<rbrace>
     createNewCaps ty ptr n us d
   \<lbrace>\<lambda>rv. valid_queues\<rbrace>"
apply (rule hoare_gen_asm)
apply (wp valid_queues_lift_asm createNewCaps_obj_at2[where sz=sz])
apply (clarsimp simp: projectKO_opts_defs)
apply (simp add: inQ_def)
apply (wp createNewCaps_pred_tcb_at'[where sz=sz] | simp)+
done

lemma mapM_x_threadSet_valid_pspace:
  "\<lbrace>valid_pspace' and K (curdom \<le> maxDomain)\<rbrace>
    mapM_x (threadSet (tcbDomain_update (\<lambda>_. curdom))) addrs \<lbrace>\<lambda>y. valid_pspace'\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (wp mapM_x_wp' threadSet_valid_pspace')
  apply simp_all
  done

lemma createNewCaps_valid_pspace:
  assumes  not_0: "n \<noteq> 0"
  and      cover: "range_cover ptr sz (APIType_capBits ty us) n"
  shows "\<lbrace>\<lambda>s. pspace_no_overlap' ptr sz s \<and> valid_pspace' s
  \<and> caps_no_overlap'' ptr sz s \<and> ptr \<noteq> 0 \<and> caps_overlap_reserved' {ptr..ptr + of_nat n * 2^(APIType_capBits ty us) - 1} s \<and> ksCurDomain s \<le> maxDomain\<rbrace>
  createNewCaps ty ptr n us dev \<lbrace>\<lambda>r. valid_pspace'\<rbrace>"
  unfolding createNewCaps_def Arch_createNewCaps_def
  using valid_obj_makeObject_rules
  apply (clarsimp simp: ARM_HYP_H.toAPIType_def
             split del: if_split cong: option.case_cong)
  apply (cases ty, simp_all split del: if_split)
        apply (rename_tac apiobject_type)
        apply (case_tac apiobject_type, simp_all split del: if_split)
            apply (rule hoare_pre, wp, clarsimp)
           apply (insert cover)
           apply (wp createObjects_valid_pspace_untyped' [OF _ not_0 , where ty="Inr ty" and sz = sz]
                     mapM_x_threadSet_valid_pspace mapM_x_wp'
                 | simp add: makeObjectKO_def archObjSize_def APIType_capBits_def
                             objBits_simps vspace_bits_defs not_0
                             createObjects_def curDomain_def
                 | intro conjI impI
                 | simp add: power_add field_simps)+
  done

lemma copyGlobalMappings_inv[wp]:
  "\<lbrace>\<lambda>s. P (ksMachineState s)\<rbrace>
    copyGlobalMappings newPD
   \<lbrace>\<lambda>_ s. P (ksMachineState s)\<rbrace>"
  by (simp add: copyGlobalMappings_def storePDE_def split_def
      | wp mapM_x_wp_inv setObject_ksMachine updateObject_default_inv)+

lemma doMachineOp_return_foo:
  "doMachineOp (do x\<leftarrow>a;return () od) = (do (doMachineOp a); return () od)"
  apply (clarsimp simp: doMachineOp_def bind_def gets_def
                        get_def return_def select_f_def split_def simpler_modify_def)
  apply (rule ext)+
  apply simp
  apply (rule set_eqI)
  apply clarsimp
  done

lemma doMachineOp_mapM_x_wp:
  assumes empty_fail:"\<And>x. empty_fail (f x)"
  assumes valid: "\<And>z. \<lbrace>P\<rbrace> doMachineOp (f z) \<lbrace>\<lambda>y. P\<rbrace>"
  shows "\<lbrace>P\<rbrace> doMachineOp (mapM_x f xs) \<lbrace>\<lambda>y. P\<rbrace>"
  apply (clarsimp simp: mapM_x_mapM doMachineOp_return_foo)
  apply (subst doMachineOp_mapM)
  apply (wp valid empty_fail mapM_wp' | simp)+
  done


lemma createNewCaps_vms:
  "\<lbrace>pspace_aligned' and pspace_distinct' and pspace_no_overlap' ptr sz and
    K (range_cover ptr sz (APIType_capBits ty us) n \<and> 0 < n) and
    valid_machine_state'\<rbrace>
   createNewCaps ty ptr n us dev
   \<lbrace>\<lambda>archCaps. valid_machine_state'\<rbrace>"
  apply (clarsimp simp: valid_machine_state'_def pointerInDeviceData_def
                        Arch_createNewCaps_def createNewCaps_def pointerInUserData_def
                        typ_at'_def createObjects_def doMachineOp_return_foo
                  split del: if_split)
  apply (rule hoare_pre)
   apply (wpc
         | wp hoare_vcg_const_Ball_lift hoare_vcg_disj_lift
           hoare_vcg_all_lift
           doMachineOp_ko_wp_at' createObjects_orig_ko_wp_at2'[where sz = sz]
           hoare_vcg_all_lift
           doMachineOp_mapM_x_wp dmo_lift' mapM_x_wp' copyGlobalMappings_ko_wp_at threadSet_ko_wp_at2'
         | clarsimp simp: createObjects_def Arch_createNewCaps_def curDomain_def Let_def
               split del: if_split
         | assumption)+
  apply (case_tac ty)
   apply (auto simp: APIType_capBits_def archObjSize_def objBits_simps vspace_bits_defs
                     ARM_HYP_H.toAPIType_def object_type.splits)
  done

lemma createObjects_pspace_domain_valid':
  "\<lbrace>\<lambda>s. range_cover ptr sz (objBitsKO val + gbits) n \<and> n \<noteq> 0
      \<and> {ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1} \<inter> kernel_data_refs = {}
      \<and> pspace_domain_valid s\<rbrace>
       createObjects' ptr n val gbits
   \<lbrace>\<lambda>_. pspace_domain_valid\<rbrace>"
  apply (simp add: createObjects'_def split_def unless_def)
  apply (rule hoare_pre)
   apply (wp | wpc | simp only: alignError_def haskell_assert_def)+
  apply (clarsimp simp: new_cap_addrs_fold' unat_1_0 unat_gt_0
                        range_cover_not_zero_shift
                        caps_overlap_reserved'_def)
  apply (simp add: pspace_domain_valid_def foldr_upd_app_if
                   fun_upd_def[symmetric])
  apply (subgoal_tac " \<forall>x \<in> set (new_cap_addrs (unat (of_nat n << gbits)) ptr
                           val). {x..x + 2 ^ objBitsKO val - 1}
                                \<subseteq> {ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1}")
   apply blast

  apply (rule ballI)
  apply (rule new_range_subset)
   apply (erule range_cover_rel, simp+)
  apply (simp add: range_cover.unat_of_nat_n_shift field_simps)
  done

lemma createObjects_pspace_domain_valid:
  "\<lbrace>\<lambda>s. range_cover ptr sz (objBitsKO val + gbits) n \<and> n \<noteq> 0
      \<and> {ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1} \<inter> kernel_data_refs = {}
      \<and> pspace_domain_valid s\<rbrace>
       createObjects ptr n val gbits
   \<lbrace>\<lambda>_. pspace_domain_valid\<rbrace>"
  apply (simp add: createObjects_def)
  apply (wp createObjects_pspace_domain_valid'[where sz=sz])
  apply (simp add: objBits_def)
  done

crunches copyGlobalMappings, doMachineOp
  for pspace_domain_valid[wp]: "pspace_domain_valid"
  (wp: crunch_wps)

lemma createNewCaps_pspace_domain_valid[wp]:
  "\<lbrace>pspace_domain_valid and K ({ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1}
            \<inter> kernel_data_refs = {}
        \<and> range_cover ptr sz (APIType_capBits ty us) n \<and> 0 < n)\<rbrace>
    createNewCaps ty ptr n us dev
   \<lbrace>\<lambda>rv. pspace_domain_valid\<rbrace>"
  apply (simp add: createNewCaps_def)
  apply (rule hoare_pre)
   apply (wp createObjects_pspace_domain_valid[where sz=sz]
            mapM_x_wp'
        | wpc | simp add: Arch_createNewCaps_def curDomain_def Let_def
                     split del: if_split)+
  apply (simp add: ARM_HYP_H.toAPIType_def
            split: object_type.splits)
  apply (auto simp: objBits_simps APIType_capBits_def
                    archObjSize_def vspace_bits_defs)
  done

crunch cur_domain[wp]: createNewCaps "\<lambda>s. P (ksCurDomain s)"
  (wp: crunch_wps)

(* FIXME: move *)
lemma ct_idle_or_in_cur_domain'_lift_futz:
  assumes a: "\<And>P. \<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace>       f \<lbrace>\<lambda>_ s. P (ksCurDomain s)\<rbrace>"
  assumes b: "\<And>P. \<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksSchedulerAction s)\<rbrace>"
  assumes c: "\<And>P. \<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace>      f \<lbrace>\<lambda>_ s. P (ksIdleThread s)\<rbrace>"
  assumes d: "\<And>P. \<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace>       f \<lbrace>\<lambda>_ s. P (ksCurThread s)\<rbrace>"
  assumes e: "\<And>d t. \<lbrace>\<lambda>s. obj_at' (\<lambda>tcb. tcbState tcb \<noteq> Inactive \<and> d = tcbDomain tcb) t s \<and> Q s\<rbrace>
                            f
                     \<lbrace>\<lambda>_. obj_at' (\<lambda>tcb. tcbState tcb \<noteq> Inactive \<and> d = tcbDomain tcb) t\<rbrace>"
  shows "\<lbrace>ct_idle_or_in_cur_domain' and ct_active' and Q\<rbrace> f \<lbrace>\<lambda>_. ct_idle_or_in_cur_domain'\<rbrace>"
proof -
  from e have e':
    "\<And>d t. \<lbrace>\<lambda>s. obj_at' (\<lambda>tcb. tcbState tcb \<noteq> Inactive \<and> d = tcbDomain tcb) t s \<and> Q s\<rbrace>
              f
            \<lbrace>\<lambda>_. obj_at' (\<lambda>tcb. d = tcbDomain tcb) t\<rbrace>"
    apply (rule hoare_strengthen_post)
    apply (auto simp: obj_at'_def)
    done
  show ?thesis
    apply (simp add: ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)
    apply (rule hoare_pre)
    apply (wps a b c d)
    apply (wp static_imp_wp e' hoare_vcg_disj_lift)
    apply (auto simp: obj_at'_def ct_in_state'_def projectKOs st_tcb_at'_def)
    done
qed

lemma createNewCaps_ct_idle_or_in_cur_domain':
  "\<lbrace>ct_idle_or_in_cur_domain' and pspace_aligned' and pspace_distinct' and pspace_no_overlap' ptr sz and ct_active' and K (range_cover ptr sz (APIType_capBits ty us) n \<and> 0 < n) \<rbrace>
    createNewCaps ty ptr n us dev
   \<lbrace>\<lambda>rv. ct_idle_or_in_cur_domain'\<rbrace>"
apply (wp ct_idle_or_in_cur_domain'_lift_futz createNewCaps_obj_at'[where sz=sz] | simp)+
done

lemma sch_act_wf_lift_asm_futz:
  assumes tcb: "\<And>P t. \<lbrace>st_tcb_at' P t and Q \<rbrace> f \<lbrace>\<lambda>rv. st_tcb_at' P t\<rbrace>"
  assumes tcbDomain: "\<And>P t. \<lbrace>obj_at' (\<lambda>tcb. runnable' (tcbState tcb) \<longrightarrow> P (tcbDomain tcb)) t and Q\<rbrace> f \<lbrace>\<lambda>rv. obj_at' (\<lambda>tcb. runnable' (tcbState tcb) \<longrightarrow> P (tcbDomain tcb)) t\<rbrace>"
  assumes kCT: "\<And>P. \<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksCurThread s)\<rbrace>"
  assumes kCD: "\<And>P. \<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksCurDomain s)\<rbrace>"
  assumes ksA: "\<And>P. \<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksSchedulerAction s)\<rbrace>"
  shows
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s \<and> Q s\<rbrace>
  f
  \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (frule use_valid [OF _ ksA])
   prefer 2
   apply assumption
  apply (frule_tac P1="(=) (ksCurThread s)" in use_valid [OF _ kCT])
   apply (rule refl)
  apply (frule_tac P1="(=) (ksCurDomain s)" in use_valid [OF _ kCD])
   apply (rule refl)
  apply (case_tac "ksSchedulerAction s")
    apply (simp add: ct_in_state'_def)
    apply (drule use_valid [OF _ tcb])
     apply simp
    apply simp
   apply simp
  apply (clarsimp simp: tcb_in_cur_domain'_def)
  apply (frule use_valid [OF _ tcb], fastforce)
  apply simp
  apply (rename_tac word)
  apply (subgoal_tac "(obj_at' (\<lambda>tcb. runnable' (tcbState tcb) \<longrightarrow> ksCurDomain b = tcbDomain tcb) word and Q) s")
   apply (drule use_valid [OF _ tcbDomain], fastforce)
    apply (auto simp: st_tcb_at'_def o_def obj_at'_def ko_wp_at'_def)
  done

lemma createNewCaps_sch_act_wf:
  "\<lbrace>(\<lambda>s. sch_act_wf (ksSchedulerAction s) s) and pspace_aligned' and pspace_distinct' and pspace_no_overlap' ptr sz and K (range_cover ptr sz (APIType_capBits ty us) n \<and> 0 < n)\<rbrace>
     createNewCaps ty ptr n us dev
   \<lbrace>\<lambda>_ s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (wp sch_act_wf_lift_asm_futz
            createNewCaps_pred_tcb_at'[where sz=sz]
            createNewCaps_obj_at'[where sz=sz]
       | simp)+
  done

lemma createObjects'_ksDomSchedule[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace> createObjects' ptr numObjects val gSize \<lbrace>\<lambda>_ s. P (ksDomSchedule s)\<rbrace>"
  apply (simp add: createObjects'_def unless_def alignError_def)
  apply (wp | wpc)+
  apply simp
  done

lemma createObjects'_ksDomScheduleIdx[wp]:
  "\<lbrace>\<lambda>s. P (ksDomScheduleIdx s)\<rbrace> createObjects' ptr numObjects val gSize \<lbrace>\<lambda>_ s. P (ksDomScheduleIdx s)\<rbrace>"
  apply (simp add: createObjects'_def unless_def alignError_def)
  apply (wp | wpc)+
  apply simp
  done

crunch ksDomSchedule[wp]: copyGlobalMappings "\<lambda>s. P (ksDomSchedule s)"
  (wp: setObject_ksPSpace_only updateObject_default_inv mapM_x_wp')

crunch ksDomSchedule[wp]: createNewCaps "\<lambda>s. P (ksDomSchedule s)"
  (wp: mapM_x_wp' simp: crunch_simps)

crunch ksDomScheduleIdx[wp]: createNewCaps "\<lambda>s. P (ksDomScheduleIdx s)"
  (wp: mapM_x_wp' simp: crunch_simps)

lemma createObjects_null_filter':
  "\<lbrace>\<lambda>s. P (null_filter' (ctes_of s)) \<and> makeObjectKO dev ty = Some val \<and>
        range_cover ptr sz (objBitsKO val + gbits) n \<and> n \<noteq> 0 \<and>
        pspace_aligned' s \<and> pspace_distinct' s \<and> pspace_no_overlap' ptr sz s\<rbrace>
   createObjects' ptr n val gbits
   \<lbrace>\<lambda>addrs a. P (null_filter' (ctes_of a))\<rbrace>"
   apply (clarsimp simp: createObjects'_def split_def)
   apply (wp unless_wp|wpc
          | clarsimp simp:haskell_assert_def alignError_def
            split del: if_splits simp del:fun_upd_apply)+
   apply (subst new_cap_addrs_fold')
     apply (simp add:unat_1_0 unat_gt_0)
     apply (rule range_cover_not_zero_shift)
     apply fastforce+
   apply (subst new_cap_addrs_fold')
    apply (simp add:unat_1_0 unat_gt_0)
    apply (rule range_cover_not_zero_shift)
      apply simp
     apply assumption
    apply simp
   apply (subst data_map_insert_def[symmetric])+
   apply (frule(2) retype_aligned_distinct'[where ko = val])
    apply (erule range_cover_rel)
     apply simp+
   apply (frule(2) retype_aligned_distinct'(2)[where ko = val])
    apply (erule range_cover_rel)
     apply simp+
   apply (frule null_filter_ctes_retype
     [where addrs = "(new_cap_addrs (unat (((of_nat n)::word32) << gbits)) ptr val)"])
          apply assumption+
     apply (clarsimp simp:field_simps foldr_upd_app_if[folded data_map_insert_def] shiftl_t2n range_cover.unat_of_nat_shift)+
    apply (rule new_cap_addrs_aligned[THEN bspec])
    apply (erule range_cover.aligned[OF range_cover_rel])
     apply simp+
   apply (clarsimp simp:shiftl_t2n field_simps range_cover.unat_of_nat_shift)
   apply (drule subsetD[OF new_cap_addrs_subset,rotated])
    apply (erule range_cover_rel)
     apply simp
    apply simp
   apply (rule ccontr)
   apply clarify
   apply (frule(1) pspace_no_overlapD')
   apply (erule_tac B = "{x..x+2^objBitsKO y - 1}" in in_empty_interE[rotated])
    apply (drule(1) pspace_alignedD')
    apply (clarsimp)
    apply (erule is_aligned_no_overflow)
    apply (simp del:atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
        Int_atLeastAtMost atLeastatMost_empty_iff add:Int_ac ptr_add_def p_assoc_help)
  apply (simp add:field_simps foldr_upd_app_if[folded data_map_insert_def] shiftl_t2n)
  apply auto
  done

lemma createNewCaps_null_filter':
  "\<lbrace>(\<lambda>s. P (null_filter' (ctes_of s)))
      and pspace_aligned' and pspace_distinct' and pspace_no_overlap' ptr sz
      and K (range_cover ptr sz (APIType_capBits ty us) n \<and> n \<noteq> 0) \<rbrace>
     createNewCaps ty ptr n us dev
   \<lbrace>\<lambda>_ s. P (null_filter' (ctes_of s))\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: createNewCaps_def toAPIType_def
                   Arch_createNewCaps_def
               split del: if_split cong: option.case_cong)
  apply (cases ty, simp_all split del: if_split)
          apply (rename_tac apiobject_type)
          apply (case_tac apiobject_type, simp_all split del: if_split)
              apply (rule hoare_pre, wp,simp)
             apply (simp add: createObjects_def makeObjectKO_def
                              APIType_capBits_def objBits_def
                              archObjSize_def vspace_bits_defs curDomain_def
                              objBits_if_dev
                       split del: if_split
                    | wp createObjects_null_filter'[where ty = "Inr ty" and sz = sz and dev=dev]
                         copyGlobalMappings_ctes_of threadSet_ctes_of mapM_x_wp'
                    | simp add: objBits_simps
                    | fastforce)+
  done

crunch gsUntypedZeroRanges[wp]: createNewCaps "\<lambda>s. P (gsUntypedZeroRanges s)"
  (wp: crunch_wps simp: crunch_simps unless_def)

lemma untyped_ranges_zero_inv_null_filter:
  "untyped_ranges_zero_inv (option_map cteCap o null_filter' ctes)
    = untyped_ranges_zero_inv (option_map cteCap o ctes)"
  apply (simp add: untyped_ranges_zero_inv_def fun_eq_iff null_filter'_def)
  apply clarsimp
  apply (rule_tac f="\<lambda>caps. x = ran caps" for caps in arg_cong)
  apply (clarsimp simp: fun_eq_iff map_comp_def untypedZeroRange_def)
  done

lemma untyped_ranges_zero_inv_null_filter_cteCaps_of:
  "untyped_ranges_zero_inv (cteCaps_of s)
    = untyped_ranges_zero_inv (option_map cteCap o null_filter' (ctes_of s))"
  by (simp add: untyped_ranges_zero_inv_null_filter cteCaps_of_def)

lemma createNewCaps_urz:
  "\<lbrace>untyped_ranges_zero'
      and pspace_aligned' and pspace_distinct' and pspace_no_overlap' ptr sz
      and K (range_cover ptr sz (APIType_capBits ty us) n \<and> n \<noteq> 0) \<rbrace>
   createNewCaps ty ptr n us dev
   \<lbrace>\<lambda>archCaps. untyped_ranges_zero'\<rbrace>"
  apply (simp add: untyped_ranges_zero_inv_null_filter_cteCaps_of)
  apply (rule hoare_pre)
   apply (rule untyped_ranges_zero_lift)
    apply (wp createNewCaps_null_filter')+
  apply (auto simp: o_def)
  done

lemma createNewCaps_invs':
  "\<lbrace>(\<lambda>s. invs' s \<and> ct_active' s \<and> pspace_no_overlap' ptr sz s
        \<and> caps_no_overlap'' ptr sz s \<and> ptr \<noteq> 0
        \<and> {ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1} \<inter> kernel_data_refs = {}
        \<and> caps_overlap_reserved' {ptr..ptr + of_nat n * 2^(APIType_capBits ty us) - 1} s
        \<and> (ty = APIObjectType ArchTypes_H.CapTableObject \<longrightarrow> us > 0)
        \<and> gsMaxObjectSize s > 0)
       and K (range_cover ptr sz (APIType_capBits ty us) n \<and> n \<noteq> 0)\<rbrace>
     createNewCaps ty ptr n us dev
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  (is "\<lbrace>?P and K ?Q\<rbrace> ?f \<lbrace>\<lambda>rv. invs'\<rbrace>")
proof (rule hoare_gen_asm, erule conjE)
  assume cover: "range_cover ptr sz (APIType_capBits ty us) n" and not_0: "n \<noteq> 0"
  have cnc_ct_not_inQ:
    "\<lbrace>ct_not_inQ and valid_pspace' and pspace_no_overlap' ptr sz\<rbrace>
     createNewCaps ty ptr n us dev \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
    unfolding ct_not_inQ_def
    apply (rule_tac Q="\<lambda>s. ksSchedulerAction s = ResumeCurrentThread
                             \<longrightarrow> (obj_at' (Not \<circ> tcbQueued) (ksCurThread s) s
                                  \<and> valid_pspace' s \<and> pspace_no_overlap' ptr sz s)"
                    in hoare_pre_imp, clarsimp)
    apply (rule hoare_convert_imp [OF createNewCaps_nosch])
    apply (rule hoare_weaken_pre)
     apply (wps createNewCaps_ct)
     apply (wp createNewCaps_obj_at')
    using cover not_0
    apply (fastforce simp: valid_pspace'_def)
    done
  show "\<lbrace>?P\<rbrace>
     createNewCaps ty ptr n us dev
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def
                   pointerInUserData_def typ_at'_def)
    apply (rule hoare_pre)
     apply (wp createNewCaps_valid_pspace [OF not_0 cover]
               createNewCaps_state_refs_of' [OF cover not_0 ]
               createNewCaps_state_hyp_refs_of' [OF cover not_0 ]
               createNewCaps_iflive' [OF cover not_0 ]
               irqs_masked_lift
               createNewCaps_ifunsafe'
               createNewCaps_cur [OF cover not_0]
               createNewCaps_global_refs'
               createNewCaps_valid_arch_state
               valid_irq_node_lift_asm [unfolded pred_conj_def, OF _ createNewCaps_obj_at']
               createNewCaps_irq_handlers' createNewCaps_vms
               createNewCaps_valid_queues
               createNewCaps_valid_queues'
               createNewCaps_pred_tcb_at' cnc_ct_not_inQ
               createNewCaps_ct_idle_or_in_cur_domain'
               createNewCaps_sch_act_wf
               createNewCaps_urz[where sz=sz]
           | simp)+
  using not_0
  apply (clarsimp simp: valid_pspace'_def)
  using cover
  apply (intro conjI)
   apply simp_all
  done
qed

lemma createObjects_obj_ranges':
  "\<lbrace>\<lambda>s. (\<forall>x ko. ksPSpace s x = Some ko \<longrightarrow> (obj_range' x ko) \<inter> S = {}) \<and>
        pspace_no_overlap' ptr sz s \<and>
        pspace_aligned' s \<and> pspace_distinct' s \<and>
        S \<inter> {ptr..(ptr &&~~ mask sz) + 2^sz - 1} = {} \<and>
        range_cover ptr sz (objBitsKO val + gbits) n \<and> n \<noteq> 0\<rbrace>
  createObjects' ptr n val gbits
  \<lbrace>\<lambda>r s. (\<forall>x ko. ksPSpace s x = Some ko \<longrightarrow> (obj_range' x ko) \<inter> S = {})\<rbrace>"
  apply (simp add: createObjects'_def lookupAround2_pspace_no
                   alignError_def unless_def split_def del: fun_upd_apply)
  apply (rule hoare_pre)
   apply (wp|simp cong: if_cong del: data_map_insert_def fun_upd_apply)+
  apply (subst new_cap_addrs_fold')
   apply (simp add: unat_1_0 unat_gt_0)
   apply (rule range_cover_not_zero_shift)
     apply fastforce+
  apply (clarsimp simp: foldr_fun_upd_value)
  apply (subgoal_tac "range_cover ptr sz (objBitsKO val) (unat (of_nat n << gbits))")
   apply (erule(1) disjoint_subset[OF obj_range'_subset])
   apply (simp add: Int_commute)
  apply (rule range_cover_rel)
    apply (simp)+
  apply (subst mult.commute)
  apply (erule range_cover.unat_of_nat_n_shift)
  apply simp
  done

lemma createObjects_pred_tcb_at':
  "\<lbrace>pred_tcb_at' proj P t and K (range_cover ptr sz (objBitsKO val + gbits) n \<and> n \<noteq> 0)
     and pspace_aligned' and pspace_distinct' and pspace_no_overlap' ptr sz\<rbrace>
  createObjects ptr n val gbits \<lbrace>\<lambda>rv. pred_tcb_at' proj P t\<rbrace>"
  apply (simp add: pred_tcb_at'_def createObjects_def)
  apply (wp createObjects_orig_obj_at')
  apply auto
  done

lemma createObjects_ex_cte_cap_to [wp]:
  "\<lbrace>\<lambda>s. range_cover ptr sz (objBitsKO val + gbits) n \<and> n \<noteq> 0 \<and> pspace_aligned' s \<and>
        pspace_distinct' s \<and> ex_cte_cap_to' p s \<and> pspace_no_overlap' ptr sz s\<rbrace>
  createObjects ptr n val gbits \<lbrace>\<lambda>r. ex_cte_cap_to' p\<rbrace>"
  apply (simp add: ex_cte_cap_to'_def createObjects_def)
  apply (rule hoare_lift_Pf2 [where f="irq_node'"])
   apply (wp hoare_vcg_ex_lift createObjects_orig_cte_wp_at'[where sz = sz])
   apply simp
  apply wp
  done

lemma createObjects_orig_obj_at3:
  "\<lbrace>\<lambda>s. obj_at' P p s \<and> range_cover ptr sz (objBitsKO val + gbits) n \<and> n \<noteq> 0 \<and>
        pspace_aligned' s \<and>
        pspace_distinct' s \<and> pspace_no_overlap' ptr sz s\<rbrace>
  createObjects ptr n val gbits \<lbrace>\<lambda>r. obj_at' P p\<rbrace>"
  by (wp createObjects_orig_obj_at'[where sz = sz] | simp add: createObjects_def)+

lemma createObjects_sch:
  "\<lbrace>(\<lambda>s. sch_act_wf (ksSchedulerAction s) s) and pspace_aligned' and pspace_distinct' and pspace_no_overlap' ptr sz
      and K (range_cover ptr sz (objBitsKO val + gbits) n \<and> n \<noteq> 0)\<rbrace>
  createObjects ptr n val gbits
  \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (wp sch_act_wf_lift_asm createObjects_pred_tcb_at' createObjects_orig_obj_at3 | force)+
  done

lemma createObjects_queues:
  "\<lbrace>\<lambda>s. valid_queues s \<and>  pspace_aligned' s \<and> pspace_distinct' s \<and>
        pspace_no_overlap' ptr sz s \<and> range_cover ptr sz (objBitsKO val + gbits) n \<and> n \<noteq> 0\<rbrace>
  createObjects ptr n val gbits
  \<lbrace>\<lambda>rv. valid_queues\<rbrace>"
  apply (wp valid_queues_lift_asm [unfolded pred_conj_def, OF createObjects_orig_obj_at3]
            createObjects_pred_tcb_at' [unfolded pred_conj_def])
      apply fastforce
     apply wp+
  apply fastforce
  done

lemma createObjects_queues':
  assumes no_tcb: "\<And>t. projectKO_opt val \<noteq> Some (t::tcb)"
  shows
  "\<lbrace>\<lambda>s. valid_queues' s \<and>  pspace_aligned' s \<and> pspace_distinct' s \<and>
        pspace_no_overlap' ptr sz s \<and> range_cover ptr sz (objBitsKO val + gbits) n \<and> n \<noteq> 0\<rbrace>
  createObjects ptr n val gbits
  \<lbrace>\<lambda>rv. valid_queues'\<rbrace>"
  apply (simp add: createObjects_def)
  apply (wp valid_queues_lift_asm')
    apply (wp createObjects_orig_obj_at2')
    apply clarsimp
    apply assumption
   apply wp
  apply (clarsimp simp: no_tcb split: option.splits)
  apply fastforce
  done

lemma createObjects_no_cte_ifunsafe':
  assumes no_cte: "\<And>c. projectKO_opt val \<noteq> Some (c::cte)"
  assumes no_tcb: "\<And>t. projectKO_opt val \<noteq> Some (t::tcb)"
  shows
  "\<lbrace>\<lambda>s. valid_pspace' s \<and>
       pspace_no_overlap' ptr sz s \<and>
       range_cover ptr sz (objBitsKO val + gbits) n \<and> n \<noteq> 0 \<and>
       if_unsafe_then_cap' s\<rbrace>
      createObjects ptr n val gbits
   \<lbrace>\<lambda>rv s. if_unsafe_then_cap' s\<rbrace>"
  apply (simp only: if_unsafe_then_cap'_def ex_cte_cap_to'_def
                    imp_conv_disj)
  apply (rule hoare_pre)
   apply (rule hoare_use_eq_irq_node' [OF createObjects_ksInterrupt])
   apply (simp add: createObjects_def)
   apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift hoare_vcg_imp_lift
             createObjects_orig_cte_wp_at2' hoare_vcg_ex_lift)
  apply (simp add: valid_pspace'_def disj_imp)
  apply (simp add: split_def no_cte no_tcb split: option.splits)
  apply auto
  done

lemma createObjects_no_cte_valid_global:
  assumes no_cte: "\<And>c. projectKO_opt val \<noteq> Some (c::cte)"
  assumes no_tcb: "\<And>t. projectKO_opt val \<noteq> Some (t::tcb)"
  shows "\<lbrace>\<lambda>s. pspace_aligned' s \<and> pspace_distinct' s \<and>
        pspace_no_overlap' ptr sz s \<and>
        range_cover ptr sz (objBitsKO val + gbits) n \<and> n \<noteq> 0 \<and>
        valid_global_refs' s\<rbrace>
      createObjects ptr n val gbits
   \<lbrace>\<lambda>rv s. valid_global_refs' s\<rbrace>"
  apply (simp add: valid_global_refs'_def valid_cap_sizes'_def valid_refs'_def)
  apply (rule_tac Q="\<lambda>rv s. \<forall>ptr. \<not> cte_wp_at' (\<lambda>cte. (kernel_data_refs \<inter> capRange (cteCap cte) \<noteq> {}
        \<or> 2 ^ capBits (cteCap cte) > gsMaxObjectSize s)) ptr s \<and> global_refs' s \<subseteq> kernel_data_refs"
                 in hoare_post_imp)
   apply (auto simp: cte_wp_at_ctes_of linorder_not_less elim!: ranE)[1]
  apply (rule hoare_pre)
   apply (simp add: global_refs'_def)
   apply (rule hoare_use_eq [where f=ksArchState, OF createObjects_ksArch])
   apply (rule hoare_use_eq [where f=ksIdleThread, OF createObjects_it])
   apply (rule hoare_use_eq [where f=irq_node', OF createObjects_ksInterrupt])
   apply (rule hoare_use_eq [where f=gsMaxObjectSize], wp)
   apply (simp add: createObjects_def)
   apply (wp hoare_vcg_all_lift createObjects_orig_cte_wp_at2')
  apply (simp add: no_cte no_tcb split_def cte_wp_at_ctes_of split: option.splits)
  apply (clarsimp simp: global_refs'_def)
  apply (auto simp: ball_ran_eq linorder_not_less[symmetric])
  done

lemma createObjects'_typ_at:
  "\<lbrace>\<lambda>s. n \<noteq> 0 \<and>
        range_cover ptr sz (objBitsKO val + gbits) n \<and>
        typ_at' T p s \<and>
        pspace_aligned' s \<and> pspace_distinct' s \<and>
        pspace_no_overlap' ptr sz s\<rbrace>
  createObjects' ptr n val gbits \<lbrace>\<lambda>r s. typ_at' T p s\<rbrace>"
  apply (rule hoare_grab_asm)+
  apply (simp add: createObjects'_def lookupAround2_pspace_no
                    alignError_def unless_def split_def typ_at'_def)
   apply (subst new_cap_addrs_fold')
     apply (simp add: unat_1_0 unat_gt_0)
     apply (rule range_cover_not_zero_shift)
     apply simp+
  apply (rule hoare_pre)
    apply (wp|simp cong: if_cong del: data_map_insert_def fun_upd_apply)+
    apply (wpc|wp)+
  apply (subst data_map_insert_def[symmetric])
  apply clarsimp
  apply (subgoal_tac "range_cover ptr sz (objBitsKO val) (unat (of_nat n << gbits))")
    apply (subst data_map_insert_def[symmetric])+
    apply (subst retype_ko_wp_at',simp+)+
    apply clarsimp
   apply (frule(1) subsetD [OF new_cap_addrs_subset])
   apply (drule(1) pspace_no_overlap_disjoint')
   apply (simp add: lookupAround2_None1)
   apply (intro conjI impI allI)
     apply (drule_tac x = p in spec)
     apply (erule impE)
      apply (erule(1) range_cover_new_cap_addrs_compare[rotated])
      apply simp
     apply (fastforce simp: ko_wp_at'_def)
   apply (drule_tac x = p in orthD1)
   apply (clarsimp simp: ptr_add_def p_assoc_help)
   apply (simp add: dom_def)
   apply (fastforce simp: ko_wp_at'_def)
  apply (rule range_cover_rel)
     apply (simp)+
  apply (subst mult.commute)
  apply (erule range_cover.unat_of_nat_n_shift)
  apply simp
  done

lemma createObjects_valid_arch:
  "\<lbrace>\<lambda>s. valid_arch_state' s \<and> pspace_aligned' s \<and> pspace_distinct' s \<and>
        pspace_no_overlap' ptr sz s \<and> range_cover ptr sz (objBitsKO val + gbits) n \<and> n \<noteq> 0 \<rbrace>
      createObjects ptr n val gbits
   \<lbrace>\<lambda>rv s. valid_arch_state' s\<rbrace>"
  apply (simp add: valid_arch_state'_def valid_asid_table'_def page_directory_at'_def
                   valid_global_pts'_def page_table_at'_def createObjects_def)
  apply (wp createObjects'_typ_at hoare_vcg_all_lift createObjects'_typ_at hoare_vcg_imp_lift
            createObjects_orig_ko_wp_at2'
          | clarsimp split: option.splits)+
  apply (simp add: o_def; auto simp: pred_conj_def)+
  done

lemma createObjects_irq_state:
  "\<lbrace>\<lambda>s. pspace_aligned' s \<and> pspace_distinct' s \<and>
        pspace_no_overlap' ptr sz s \<and>
        range_cover ptr sz (objBitsKO val + gbits) n \<and> n \<noteq> 0 \<and>
        valid_irq_node' (irq_node' s) s\<rbrace>
      createObjects ptr n val gbits
   \<lbrace>\<lambda>rv s. valid_irq_node' (irq_node' s) s\<rbrace>"
  apply (wp valid_irq_node_lift_asm [unfolded pred_conj_def, OF _ createObjects_orig_obj_at3])
  apply auto
  done

lemma createObjects_no_cte_irq_handlers:
  assumes no_cte: "\<And>c. projectKO_opt val \<noteq> Some (c::cte)"
  assumes no_tcb: "\<And>t. projectKO_opt val \<noteq> Some (t::tcb)"
  shows
  "\<lbrace>\<lambda>s. pspace_aligned' s \<and> pspace_distinct' s \<and>
        pspace_no_overlap' ptr sz s \<and>
        range_cover ptr sz (objBitsKO val + gbits) n \<and> n \<noteq> 0 \<and>
        valid_irq_handlers' s\<rbrace>
      createObjects ptr n val gbits
   \<lbrace>\<lambda>rv s.  valid_irq_handlers' s\<rbrace>"
  apply (simp add: valid_irq_handlers_cte_wp_at_form' createObjects_def irq_issued'_def)
   apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift
             createObjects_orig_cte_wp_at2')
  apply (clarsimp simp: no_cte no_tcb split_def split: option.splits)
  apply auto
  done

lemma createObjects_cur':
  "\<lbrace>\<lambda>s. pspace_aligned' s \<and> pspace_distinct' s \<and>
        pspace_no_overlap' ptr sz s \<and> range_cover ptr sz (objBitsKO val + gbits) n \<and> n \<noteq> 0 \<and>
        cur_tcb' s\<rbrace>
      createObjects ptr n val gbits
   \<lbrace>\<lambda>rv s. cur_tcb' s\<rbrace>"
  apply (rule hoare_post_imp [where Q="\<lambda>rv s. \<exists>t. ksCurThread s = t \<and> tcb_at' t s"])
   apply (simp add: cur_tcb'_def)
  apply (wp hoare_vcg_ex_lift createObjects_orig_obj_at3)
  apply (clarsimp simp: cur_tcb'_def)
  apply auto
  done

lemma createObjects_vms'[wp]:
  "\<lbrace>(\<lambda>_.  (range_cover ptr sz  (objBitsKO val + gbits) n \<and> 0 < n)) and pspace_aligned' and
     pspace_distinct' and pspace_no_overlap' ptr sz and valid_machine_state'\<rbrace>
      createObjects ptr n val gbits
   \<lbrace>\<lambda>rv. valid_machine_state'\<rbrace>"
  apply (simp add: valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def
                   typ_at'_def)
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift createObjects_orig_ko_wp_at2'
         | simp add: createObjects_def)+
  apply auto
  done

lemma createObjects_ct_idle_or_in_cur_domain':
  "\<lbrace>ct_active' and valid_pspace' and pspace_no_overlap' ptr sz
       and ct_idle_or_in_cur_domain'
       and K (range_cover ptr sz (objBitsKO val + gSize) n \<and> n \<noteq> 0)\<rbrace>
     createObjects ptr n val gSize
   \<lbrace>\<lambda>_. ct_idle_or_in_cur_domain'\<rbrace>"
apply (rule hoare_gen_asm)
apply (wp ct_idle_or_in_cur_domain'_lift_futz createObjects_obj_at_other[where sz=sz])
apply simp_all
done

lemma untyped_zero_ranges_cte_def:
  "untyped_ranges_zero_inv (cteCaps_of s) rs
    = (\<forall>r. (\<exists>p. cte_wp_at' (\<lambda>cte. untypedZeroRange (cteCap cte) = Some r) p s)
        = (r \<in> rs))"
  apply (clarsimp simp: untyped_ranges_zero_inv_def cte_wp_at_ctes_of
                        cteCaps_of_def set_eq_iff ran_def map_comp_Some_iff)
  apply (safe, metis+)
  done

crunch gsUntypedZeroRanges[wp]: createObjects "\<lambda>s. P (gsUntypedZeroRanges s)"
  (simp: unless_def)

lemma createObjects_untyped_ranges_zero':
  assumes moKO: "makeObjectKO dev ty = Some val"
  shows
  "\<lbrace>ct_active' and valid_pspace' and pspace_no_overlap' ptr sz
       and untyped_ranges_zero'
       and K (range_cover ptr sz (objBitsKO val + gSize) n \<and> n \<noteq> 0)\<rbrace>
     createObjects ptr n val gSize
   \<lbrace>\<lambda>_. untyped_ranges_zero'\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: untyped_zero_ranges_cte_def iff_conv_conj_imp
                   createObjects_def)
  apply (simp only: imp_conv_disj not_all not_ex)
  apply (rule hoare_pre)
   apply (wp hoare_vcg_all_lift hoare_vcg_ex_lift hoare_vcg_conj_lift
             hoare_vcg_disj_lift createObjects_orig_cte_wp_at2'[where sz=sz])
  apply (clarsimp simp: valid_pspace'_def)
  apply (cut_tac moKO[symmetric])
  apply (simp add: makeObjectKO_def projectKO_opt_tcb projectKO_opt_cte
                   split: sum.split_asm kernel_object.split_asm
                          arch_kernel_object.split_asm
                          object_type.split_asm apiobject_type.split_asm)
   apply (simp add: makeObject_tcb tcb_cte_cases_def makeObject_cte
                    untypedZeroRange_def)
  apply (simp add: makeObject_cte untypedZeroRange_def)
  done

lemma createObjects_no_cte_invs:
  assumes moKO: "makeObjectKO dev ty = Some val"
  assumes no_cte: "\<And>c. projectKO_opt val \<noteq> Some (c::cte)"
  assumes no_tcb: "\<And>t. projectKO_opt val \<noteq> Some (t::tcb)"
  shows
  "\<lbrace>\<lambda>s. range_cover ptr sz ((objBitsKO val) + gbits) n \<and> n \<noteq> 0 \<and> invs' s \<and> ct_active' s
        \<and> pspace_no_overlap' ptr sz s \<and> ptr \<noteq> 0
        \<and> {ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1} \<inter> kernel_data_refs = {}
        \<and> caps_overlap_reserved' {ptr..ptr + of_nat (n * 2 ^ gbits * 2 ^ objBitsKO val) - 1} s
        \<and> caps_no_overlap'' ptr sz s \<and>
       refs_of' val = {} \<and> hyp_refs_of' val = {} \<and> \<not> live' val
            \<and> (\<forall>pde. projectKO_opt val = Some pde \<longrightarrow> pde = InvalidPDE)\<rbrace>
  createObjects ptr n val gbits
  \<lbrace>\<lambda>rv. invs'\<rbrace>"
proof -
  have co_ct_not_inQ:
    "\<lbrakk>range_cover ptr sz ((objBitsKO val) + gbits) n; n \<noteq> 0\<rbrakk> \<Longrightarrow>
     \<lbrace>\<lambda>s. ct_not_inQ s \<and> pspace_no_overlap' ptr sz s \<and> valid_pspace' s\<rbrace>
      createObjects ptr n val gbits \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
    (is "\<lbrakk> _; _ \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. ct_not_inQ s \<and> ?REST s\<rbrace> _ \<lbrace>_\<rbrace>")
    apply (simp add: ct_not_inQ_def)
    apply (rule_tac Q="\<lambda>s. (ksSchedulerAction s = ResumeCurrentThread) \<longrightarrow>
                             (obj_at' (Not \<circ> tcbQueued) (ksCurThread s) s \<and> ?REST s)"
             in hoare_pre_imp, clarsimp)
    apply (rule hoare_convert_imp [OF createObjects_nosch])
    apply (rule hoare_weaken_pre)
     apply (wps createObjects_ct)
     apply (wp createObjects_obj_at_other)
      apply (simp)+
    done
  show ?thesis
  apply (rule hoare_grab_asm)+
   apply (clarsimp simp: invs'_def valid_state'_def)
   apply wp
   apply (rule hoare_pre)
   apply (rule hoare_vcg_conj_lift)
   apply (simp add: createObjects_def,wp createObjects_valid_pspace_untyped')
   apply (wp assms | simp add: objBits_def)+
   apply (wp createObjects_sch createObjects_queues)
   apply (rule hoare_vcg_conj_lift)
    apply (simp add: createObjects_def)
    apply (wp createObjects_state_refs_of'')
   apply (rule hoare_vcg_conj_lift)
    apply (simp add: createObjects_def)
    apply (wp createObjects_state_hyp_refs_of'')
   apply (rule hoare_vcg_conj_lift)
    apply (simp add: createObjects_def)
    apply (wp createObjects_iflive')
   apply (wp createObjects_no_cte_ifunsafe' irqs_masked_lift
             createObjects_idle' createObjects_no_cte_valid_global
             createObjects_valid_arch createObjects_irq_state
             createObjects_no_cte_irq_handlers createObjects_cur'
             createObjects_queues' [OF no_tcb]
             assms | simp add: objBits_def )+
  apply (rule hoare_vcg_conj_lift)
   apply (simp add: createObjects_def)
   apply (wp createObjects_idle')
   apply (wp createObjects_no_cte_ifunsafe' irqs_masked_lift
             createObjects_idle' createObjects_no_cte_valid_global
             createObjects_valid_arch createObjects_irq_state
             createObjects_no_cte_irq_handlers createObjects_cur'
             createObjects_queues' [OF no_tcb] assms
             createObjects_pspace_domain_valid co_ct_not_inQ
             createObjects_ct_idle_or_in_cur_domain'
             createObjects_untyped_ranges_zero'[OF moKO]
         | simp)+
  apply clarsimp
  apply (simp add: conj_comms)
  apply ((intro conjI; assumption?); simp add: valid_pspace'_def objBits_def)
  apply (fastforce simp add: no_cte no_tcb split_def split: option.splits)
  apply (clarsimp simp: invs'_def no_tcb valid_state'_def no_cte  split: option.splits)
  done
qed

lemma corres_retype_update_gsI:
  assumes not_zero: "n \<noteq> 0"
  and      aligned: "is_aligned ptr (objBitsKO ko + gbits)"
  and obj_bits_api: "obj_bits_api (APIType_map2 ty) us =
                     objBitsKO ko + gbits"
  and        check: "sz < obj_bits_api (APIType_map2 ty) us \<longleftrightarrow>
                     sz < objBitsKO ko + gbits"
  and          usv: "APIType_map2 ty = Structures_A.CapTableObject \<Longrightarrow> 0 < us"
  and           ko: "makeObjectKO dev ty = Some ko"
  and          orr: "obj_bits_api (APIType_map2 ty) us \<le> sz \<Longrightarrow>
                     obj_relation_retype
                       (default_object (APIType_map2 ty) dev us) ko"
  and        cover: "range_cover ptr sz (obj_bits_api (APIType_map2 ty) us) n"
  and            f: "f = update_gs (APIType_map2 ty) us"
  shows "corres (\<lambda>rv rv'. rv' = g rv)
         (\<lambda>s. valid_pspace s \<and> pspace_no_overlap_range_cover ptr sz s
            \<and> valid_mdb s \<and> valid_etcbs s \<and> valid_list s)
         (\<lambda>s. pspace_aligned' s \<and> pspace_distinct' s \<and>
              pspace_no_overlap' ptr sz s)
         (retype_region2 ptr n us (APIType_map2 ty) dev)
         (do addrs \<leftarrow> createObjects ptr n ko gbits;
             _ \<leftarrow> modify (f (set addrs));
             return (g addrs)
          od)"
  using corres_retype' [OF not_zero aligned obj_bits_api check usv ko orr cover]
  by (simp add: f)

lemma gcd_corres: "corres (=) \<top> \<top> (gets cur_domain) curDomain"
  by (simp add: curDomain_def state_relation_def)

lemma retype_region2_extra_ext_mapM_x_corres:
  shows "corres dc
           (valid_etcbs and (\<lambda>s. \<forall>addr\<in>set addrs. tcb_at addr s))
           (\<lambda>s. \<forall>addr\<in>set addrs. tcb_at' addr s)
           (retype_region2_extra_ext addrs Structures_A.apiobject_type.TCBObject)
           (mapM_x (\<lambda>addr. do cdom \<leftarrow> curDomain;
                              threadSet (tcbDomain_update (\<lambda>_. cdom)) addr
                           od)
             addrs)"
  apply (rule corres_guard_imp)
    apply (simp add: retype_region2_extra_ext_def curDomain_mapM_x_futz[symmetric] when_def)
    apply (rule corres_split_eqr[OF gcd_corres])
      apply (rule_tac S="Id \<inter> {(x, y). x \<in> set addrs}"
                  and P="\<lambda>s. (\<forall>t \<in> set addrs. tcb_at t s) \<and> valid_etcbs s"
                  and P'="\<lambda>s. \<forall>t \<in> set addrs. tcb_at' t s"
                   in corres_mapM_x)
          apply simp
          apply (rule corres_guard_imp)
            apply (rule ethread_set_corres, simp_all add: etcb_relation_def non_exst_same_def)[1]
            apply (case_tac tcb')
            apply simp
           apply fastforce
          apply fastforce
         apply (wp hoare_vcg_ball_lift | simp)+
      apply auto[1]
     apply (wp | simp add: curDomain_def)+
  done

lemma retype_region2_extra_ext_trivial:
  "ty \<noteq> APIType_map2 (Inr (APIObjectType apiobject_type.TCBObject))
      \<Longrightarrow> retype_region2_extra_ext ptrs ty = return ()"
by (simp add: retype_region2_extra_ext_def when_def APIType_map2_def)

lemma retype_region2_ext_retype_region_ArchObject_PageDirectoryObj:
  "retype_region ptr n us (APIType_map2 (Inr PageDirectoryObject)) dev =
  (retype_region2 ptr n us (APIType_map2 (Inr PageDirectoryObject)) dev :: obj_ref list det_ext_monad)"
by (simp add: retype_region2_ext_retype_region retype_region2_extra_ext_def when_def APIType_map2_def)

lemma retype_region2_valid_etcbs[wp]:"\<lbrace>valid_etcbs\<rbrace> retype_region2 a b c d dev \<lbrace>\<lambda>_. valid_etcbs\<rbrace>"
  apply (simp add: retype_region2_def)
  apply (simp add: retype_region2_ext_def bind_assoc)
  apply wp
  apply (clarsimp simp del: fun_upd_apply)
  apply (blast intro: valid_etcb_fold_update)
  done

lemma retype_region2_obj_at:
  assumes tytcb: "ty = Structures_A.apiobject_type.TCBObject"
  shows "\<lbrace>\<top>\<rbrace> retype_region2 ptr n us ty dev \<lbrace>\<lambda>rv s. \<forall>x \<in> set rv. tcb_at x s\<rbrace>"
  using tytcb unfolding retype_region2_def
  apply (simp only: return_bind bind_return foldr_upd_app_if fun_app_def K_bind_def)
  apply (wp dxo_wp_weak | simp)+
  apply (auto simp: obj_at_def default_object_def is_tcb_def)
  done

lemma createObjects_tcb_at':
  "\<lbrakk>range_cover ptr sz (objBitsKO (injectKOS (makeObject::tcb))) n; n \<noteq> 0\<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s. pspace_no_overlap' ptr sz s \<and> pspace_aligned' s \<and> pspace_distinct' s\<rbrace>
   createObjects ptr n (KOTCB makeObject) 0 \<lbrace>\<lambda>ptrs s. \<forall>addr\<in>set ptrs. tcb_at' addr s\<rbrace>"
  apply (rule hoare_strengthen_post[OF createObjects_ko_at_strg[where val = "(makeObject :: tcb)"]])
  apply (auto simp: obj_at'_def projectKOs project_inject objBitsKO_def objBits_def makeObject_tcb)
  done

lemma init_arch_objects_APIType_map2_noop:
  "tp \<noteq> Inr PageDirectoryObject
   \<longrightarrow> init_arch_objects (APIType_map2 tp) ptr n m addrs
    = return ()"
  apply (simp add: init_arch_objects_def APIType_map2_def)
  apply (cases tp, simp_all split: kernel_object.split arch_kernel_object.split
    object_type.split apiobject_type.split)
  done

lemma data_page_relation_retype:
  "obj_relation_retype (ArchObj (DataPage False pgsz)) KOUserData"
  "obj_relation_retype (ArchObj (DataPage True pgsz)) KOUserDataDevice"
  apply (simp_all add: obj_relation_retype_def
                   objBits_simps archObjSize_def
                   pbfs_atleast_pageBits)
   apply (clarsimp simp: image_def)+
  done

lemma corres_retype_region_createNewCaps:
  "corres ((\<lambda>r r'. length r = length r' \<and> list_all2 cap_relation r r')
               \<circ> map (\<lambda>ref. default_cap (APIType_map2 (Inr ty)) ref us dev))
            (\<lambda>s. valid_pspace s \<and> valid_mdb s \<and> valid_etcbs s \<and> valid_list s \<and> valid_arch_state s
                   \<and> caps_no_overlap y sz s \<and> pspace_no_overlap_range_cover y sz s
                   \<and> caps_overlap_reserved {y..y + of_nat n * 2 ^ (obj_bits_api (APIType_map2 (Inr ty)) us) - 1} s
                   \<and> (\<exists>slot. cte_wp_at (\<lambda>c. up_aligned_area y sz \<subseteq> cap_range c \<and> cap_is_device c = dev) slot s)
                   \<and> (APIType_map2 (Inr ty) = Structures_A.CapTableObject \<longrightarrow> 0 < us))
            (\<lambda>s. pspace_aligned' s \<and> pspace_distinct' s \<and> pspace_no_overlap' y sz s
                  \<and> valid_pspace' s \<and> valid_arch_state' s
                  \<and> range_cover y sz (obj_bits_api (APIType_map2 (Inr ty)) us) n \<and> n\<noteq> 0)
            (do x \<leftarrow> retype_region y n us (APIType_map2 (Inr ty)) dev :: obj_ref list det_ext_monad;
                init_arch_objects (APIType_map2 (Inr ty)) y n us x;
                return x od)
            (createNewCaps ty y n us dev)"
  apply (rule_tac F="range_cover y sz
                       (obj_bits_api (APIType_map2 (Inr ty)) us) n \<and>
                     n \<noteq> 0 \<and>
                     (APIType_map2 (Inr ty) = Structures_A.CapTableObject
                       \<longrightarrow> 0 < us)"
            in corres_req, simp)
  apply (clarsimp simp add: createNewCaps_def toAPIType_def
                 split del: if_split cong: if_cong)
  apply (subst init_arch_objects_APIType_map2)
  apply (cases ty, simp_all add: Arch_createNewCaps_def
                      split del: if_split)
        apply (rename_tac apiobject_type)
        apply (case_tac apiobject_type, simp_all split del: if_split)
            \<comment> \<open>Untyped\<close>
            apply (simp     add: retype_region_def obj_bits_api_def
                                 APIType_map2_def
                      split del: if_split
                           cong: if_cong)
            apply (subst upto_enum_red')
             apply (drule range_cover_not_zero[rotated])
              apply simp
             apply unat_arith
            apply (clarsimp simp: list_all2_same enum_word_def  range_cover.unat_of_nat_n
                                  list_all2_map1 list_all2_map2
                                  ptr_add_def fromIntegral_def toInteger_nat fromInteger_nat)
            apply (subst unat_of_nat_minus_1)
              apply (rule le_less_trans[OF range_cover.range_cover_n_le(2) power_strict_increasing])
                apply simp
               apply (clarsimp simp: range_cover_def)
               apply (arith+)[4]
           \<comment> \<open>TCB, EP, NTFN\<close>
           defer 10
           apply (simp_all add: retype_region2_ext_retype_region bind_cong[OF curDomain_mapM_x_futz refl, unfolded bind_assoc]
                     split del: if_split)[10] (* not PageDirectoryObject *)
           apply (rule corres_guard_imp)
             apply (rule corres_split_eqr)
                apply (rule corres_retype[where 'a = tcb],
                       simp_all add: obj_bits_api_def objBits_simps' pageBits_def
                                    APIType_map2_def makeObjectKO_def
                                    other_objs_default_relation)[1]
                apply (fastforce simp: range_cover_def)
               apply (rule corres_split_nor)
                  apply (simp add: APIType_map2_def)
                  apply (rule retype_region2_extra_ext_mapM_x_corres)
                 apply (rule corres_trivial, simp)
                 apply (clarsimp simp: list_all2_same list_all2_map1 list_all2_map2
                objBits_simps APIType_map2_def)
                apply wp
               apply wp
              apply ((wp retype_region2_obj_at | simp add: APIType_map2_def)+)[1]
             apply ((wp createObjects_tcb_at'[where sz=sz] | simp add: APIType_map2_def objBits_simps' obj_bits_api_def)+)[1]
            apply simp
           apply simp
          apply (subst retype_region2_extra_ext_trivial)
           apply (simp add: APIType_map2_def)
          apply (simp add: liftM_def[symmetric] split del: if_split)
          apply (rule corres_rel_imp)
           apply (rule corres_guard_imp)
             apply (rule corres_retype[where 'a = endpoint],
                    simp_all add: obj_bits_api_def objBits_simps' pageBits_def
                                  APIType_map2_def makeObjectKO_def
                                  other_objs_default_relation)[1]
             apply (fastforce simp: range_cover_def)
            apply simp
           apply simp
          apply (clarsimp simp: list_all2_same list_all2_map1 list_all2_map2
                                objBits_simps APIType_map2_def)
         apply (subst retype_region2_extra_ext_trivial)
          apply (simp add: APIType_map2_def)
         apply (simp add: liftM_def[symmetric] split del: if_split)
         apply (rule corres_rel_imp)
          apply (rule corres_guard_imp)
            apply (rule corres_retype[where 'a = notification],
                   simp_all add: obj_bits_api_def objBits_simps' pageBits_def
                                 APIType_map2_def makeObjectKO_def
                                 other_objs_default_relation)[1]
            apply (fastforce simp: range_cover_def)
           apply simp
          apply simp
         apply (clarsimp simp: list_all2_same list_all2_map1 list_all2_map2
                               objBits_simps APIType_map2_def)
        \<comment> \<open>CapTable\<close>
        apply (subst retype_region2_extra_ext_trivial)
         apply (simp add: APIType_map2_def)
        apply (subst bind_assoc_return_reverse[of "createObjects y n (KOCTE makeObject) us"])
        apply (subst liftM_def
               [of "map (\<lambda>addr. capability.CNodeCap addr us 0 0)", symmetric])
        apply simp
        apply (rule corres_rel_imp)
         apply (rule corres_guard_imp)
           apply (rule corres_retype_update_gsI,
                 simp_all add: obj_bits_api_def objBits_simps' pageBits_def
                               APIType_map2_def makeObjectKO_def slot_bits_def
                               field_simps ext)[1]
            apply (simp add: range_cover_def)
           apply (rule captable_relation_retype,simp add: range_cover_def word_bits_def)
          apply simp
         apply simp
        apply (clarsimp simp: list_all2_same list_all2_map1 list_all2_map2
                              objBits_simps allRights_def APIType_map2_def
                   split del: if_split)
          \<comment> \<open>SmallPageObject\<close>
       apply (subst retype_region2_extra_ext_trivial)
        apply (simp add: APIType_map2_def)
       apply (simp add: corres_liftM2_simp[unfolded liftM_def] split del: if_split)
       apply (rule corres_rel_imp)
        apply (simp add: init_arch_objects_APIType_map2_noop split del: if_split)
        apply (rule corres_guard_imp)
          apply (rule corres_retype_update_gsI,
                 simp_all add: APIType_map2_def makeObjectKO_def
                     arch_default_cap_def obj_bits_api_def3
                     default_object_def default_arch_object_def pageBits_def
                     ext objBits_simps range_cover.aligned,
                     simp_all add: data_page_relation_retype)[1]
         apply simp+
       apply (simp add: APIType_map2_def arch_default_cap_def vmrights_map_def
                vm_read_write_def list_all2_map1 list_all2_map2 list_all2_same)
         \<comment> \<open>LargePageObject\<close>
      apply (subst retype_region2_extra_ext_trivial)
       apply (simp add: APIType_map2_def)
      apply (simp add: corres_liftM2_simp[unfolded liftM_def] split del: if_split)
      apply (rule corres_rel_imp)
       apply (simp add: init_arch_objects_APIType_map2_noop split del: if_split)
       apply (rule corres_guard_imp)
         apply (rule corres_retype_update_gsI,
                simp_all add: APIType_map2_def makeObjectKO_def
                    arch_default_cap_def obj_bits_api_def3
                    default_object_def default_arch_object_def pageBits_def
                    ext objBits_simps range_cover.aligned,
                    simp_all add: data_page_relation_retype)[1]
        apply simp+
      apply (simp add: APIType_map2_def arch_default_cap_def vmrights_map_def
               vm_read_write_def list_all2_map1 list_all2_map2 list_all2_same)
        \<comment> \<open>SectionObject\<close>
     apply (subst retype_region2_extra_ext_trivial)
      apply (simp add: APIType_map2_def)
     apply (simp add: corres_liftM2_simp[unfolded liftM_def] split del: if_split)
     apply (rule corres_rel_imp)
      apply (simp add: init_arch_objects_APIType_map2_noop split del: if_split)
      apply (rule corres_guard_imp)
        apply (rule corres_retype_update_gsI,
               simp_all add: APIType_map2_def makeObjectKO_def
                   arch_default_cap_def obj_bits_api_def3
                   default_object_def default_arch_object_def pageBits_def
                   ext objBits_simps range_cover.aligned,
                   simp_all add: data_page_relation_retype)[1]
       apply simp+
     apply (simp add: APIType_map2_def arch_default_cap_def vmrights_map_def
              vm_read_write_def list_all2_map1 list_all2_map2 list_all2_same)
    \<comment> \<open>SuperSectionObject\<close>
    apply (subst retype_region2_extra_ext_trivial)
     apply (simp add: APIType_map2_def)
    apply (simp add: corres_liftM2_simp[unfolded liftM_def] split del: if_split)
    apply (rule corres_rel_imp)
     apply (simp add: init_arch_objects_APIType_map2_noop split del: if_split)
     apply (rule corres_guard_imp)
       apply (rule corres_retype_update_gsI,
              simp_all add: APIType_map2_def makeObjectKO_def
                  arch_default_cap_def obj_bits_api_def3
                  default_object_def default_arch_object_def pageBits_def
                  ext objBits_simps range_cover.aligned,
                  simp_all add: data_page_relation_retype)[1]
      apply simp+
    apply (simp add: APIType_map2_def arch_default_cap_def vmrights_map_def
             vm_read_write_def list_all2_map1 list_all2_map2 list_all2_same)
  \<comment> \<open>PageTable\<close>
   apply (subst retype_region2_extra_ext_trivial)
    apply (simp add: APIType_map2_def)
   apply (simp_all add: corres_liftM2_simp[unfolded liftM_def])
   apply (rule corres_guard_imp)
    apply (simp add: init_arch_objects_APIType_map2_noop)
    apply (rule corres_rel_imp)
       apply (rule corres_retype[where 'a =pte],
            simp_all add: APIType_map2_def obj_bits_api_def
                          default_arch_object_def objBits_simps
                          archObjSize_def vspace_bits_defs
                          makeObjectKO_def range_cover.aligned)[1]
     apply (rule pagetable_relation_retype)
    apply (wp | simp)+
    apply (clarsimp simp: list_all2_map1 list_all2_map2 list_all2_same
                          APIType_map2_def arch_default_cap_def)
   apply simp+
   defer
  \<comment> \<open>PageDirectory\<close>
   apply (rule corres_guard_imp)
     apply (rule corres_split_eqr)
        apply (rule corres_retype[where ty = "Inr PageDirectoryObject" and 'a = pde
                     , simplified, folded retype_region2_ext_retype_region_ArchObject_PageDirectoryObj],
               simp_all add: APIType_map2_def obj_bits_api_def
                             default_arch_object_def objBits_simps
                             archObjSize_def vspace_bits_defs
                             makeObjectKO_def)[1]
         apply (simp add: range_cover_def)+
        apply (rule pagedirectory_relation_retype)
       apply (simp add: init_arch_objects_def APIType_map2_def
                        bind_assoc)
       apply (rule corres_split_nor)
          apply (simp add: mapM_x_mapM)
          apply (rule corres_underlying_split[where r' = dc])
             apply (rule_tac Q="\<lambda>xs s. (\<forall>x \<in> set xs. page_directory_at x s)
                                    \<and> valid_arch_state s \<and> pspace_aligned s \<and> valid_etcbs s"
                          and Q'="\<lambda>xs s. (\<forall>x \<in> set xs. page_directory_at' x s) \<and> valid_arch_state' s"
                          in corres_mapM_list_all2[where r'=dc and S="(=)"])
                  apply simp+
                apply (rule corres_guard_imp, rule copyGlobalMappings_corres)
                 apply simp+
               apply (wp hoare_vcg_const_Ball_lift | simp)+
             apply (simp add: list_all2_same)
            apply (rule corres_return[where P =\<top> and P'=\<top>,THEN iffD2])
            apply simp
           apply wp+
         apply (simp add: liftM_def[symmetric] o_def list_all2_map1
                          list_all2_map2 list_all2_same
                          arch_default_cap_def mapM_x_mapM)
         apply (simp add: dc_def[symmetric])
         apply (rule corres_machine_op)
         apply (rule corres_Id)
           apply (simp add: shiftl_t2n shiftL_nat
                            vspace_bits_defs)
          apply simp
         apply (simp add: mapM_discarded[where g = "return ()",simplified,symmetric])
         apply (rule no_fail_pre)
          apply (wp no_fail_mapM|clarsimp)+
      apply (rule hoare_vcg_conj_lift)
       apply (rule hoare_post_imp)
        prefer 2
        apply (rule hoare_vcg_conj_lift)
         apply (rule retype_region_obj_at)
         apply (simp add: APIType_map2_def)
        apply (subst APIType_map2_def, simp)
        apply (rule retype_region_ret)
       apply (clarsimp simp: retype_addrs_def obj_bits_api_def APIType_map2_def
                  default_arch_object_def default_object_def)
       apply (clarsimp simp: obj_at_def a_type_def)
      apply (wp retype_region_valid_arch retype_region_aligned|simp)+
     apply (clarsimp simp: objBits_simps retype_addrs_def obj_bits_api_def
                           APIType_map2_def default_arch_object_def default_object_def)
     apply (rule hoare_vcg_conj_lift)
      apply (rule hoare_post_imp)
       prefer 2
       apply (rule hoare_vcg_conj_lift)
        apply (rule createObjects_ko_at[where sz = sz and 'a = pde])
          apply (simp add: objBits_simps archObjSize_def vspace_bits_defs
                           page_directory_at'_def)+
        apply (simp add: projectKOs)
       apply (rule createObjects_aligned)
          apply (simp add: objBits_simps archObjSize_def vspace_bits_defs
                           page_directory_at'_def)+
          apply (simp add: range_cover_def)
         apply (rule le_less_trans[OF range_cover.range_cover_n_le(2) power_strict_increasing])
           apply simp
          apply (clarsimp simp: range_cover_def word_bits_def)
          apply arith+
       apply (simp add: objBits_simps archObjSize_def vspace_bits_defs
                        page_directory_at'_def)+
       apply (simp add: range_cover_def word_bits_def)
      apply clarsimp
      apply (drule (1) bspec)+
      apply (simp add: objBits_simps retype_addrs_def obj_bits_api_def vspace_bits_defs
                       APIType_map2_def default_arch_object_def default_object_def
                       archObjSize_def)
      apply (clarsimp simp: objBits_simps archObjSize_def vspace_bits_defs
                            page_directory_at'_def)
      apply (drule_tac x = ya in spec)
      apply (clarsimp simp:typ_at'_def obj_at'_real_def)
      apply (erule ko_wp_at'_weakenE)
      apply (clarsimp simp: projectKOs)
     apply (wp createObjects_valid_arch)
    apply (auto simp: objBits_simps retype_addrs_def obj_bits_api_def
                      APIType_map2_def default_arch_object_def default_object_def archObjSize_def
                      vspace_bits_defs fromIntegral_def toInteger_nat fromInteger_nat)[2]
  \<comment> \<open>VCPUObject\<close>
      apply (subst retype_region2_extra_ext_trivial)
       apply (simp add: APIType_map2_def)
      apply (simp add: corres_liftM2_simp[unfolded liftM_def] split del: if_split)
      apply (rule corres_rel_imp)
       apply (simp add: init_arch_objects_APIType_map2_noop split del: if_split)
       apply (rule corres_guard_imp)
            apply (rule corres_retype[where 'a = vcpu],
                   simp_all add: obj_bits_api_def objBits_simps pageBits_def default_arch_object_def
                                 APIType_map2_def makeObjectKO_def archObjSize_def vcpu_bits_def
                                 other_objs_default_relation)[1]
            apply (fastforce simp: range_cover_def)
           apply (simp add: no_gs_types_def)
          apply (auto simp add: obj_relation_retype_def range_cover_def objBitsKO_def arch_kobj_size_def default_object_def
                           archObjSize_def vcpu_bits_def pageBits_def obj_bits_def cte_level_bits_def default_arch_object_def
                           other_obj_relation_def vcpu_relation_def default_vcpu_def makeObject_vcpu
                           makeVCPUObject_def default_gic_vcpu_interface_def vgic_map_def)[1]
         apply simp+
        apply (clarsimp simp: list_all2_same list_all2_map1 list_all2_map2
                              objBits_simps APIType_map2_def arch_default_cap_def)
  done

end
end
