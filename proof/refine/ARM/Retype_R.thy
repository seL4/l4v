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

context begin interpretation Arch . (*FIXME: arch-split*)

definition
  APIType_map2 :: "kernel_object + ARM_H.object_type \<Rightarrow> Structures_A.apiobject_type"
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
  by (simp add: objBits_simps' word_bits_def pageBits_def archObjSize_def pdeBits_def pteBits_def
           split: Structures_H.kernel_object.split arch_kernel_object.split)

definition
  APIType_capBits :: "ARM_H.object_type \<Rightarrow> nat \<Rightarrow> nat"
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
    | PageTableObject \<Rightarrow> 10
    | PageDirectoryObject \<Rightarrow> 14"

definition
  makeObjectKO :: "bool \<Rightarrow> domain \<Rightarrow> (kernel_object + ARM_H.object_type) \<rightharpoonup> kernel_object"
where
  "makeObjectKO dev d ty \<equiv> case ty of
      Inl KOUserData \<Rightarrow> Some KOUserData
    | Inl (KOArch (KOASIDPool _)) \<Rightarrow> Some (KOArch (KOASIDPool makeObject))
    | Inr (APIObjectType ArchTypes_H.TCBObject) \<Rightarrow> Some (KOTCB (tcbDomain_update (\<lambda>_. d) makeObject))
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
  unfolding valid_obj'_def valid_tcb'_def valid_tcb_state'_def
  by (clarsimp simp: makeObject_tcb makeObject_cte tcb_cte_cases_def minBound_word newArchTCB_def
                     cteSizeBits_def valid_arch_tcb'_def)

lemma valid_obj_makeObject_tcb_tcbDomain_update [simp]:
  "d \<le> maxDomain \<Longrightarrow> valid_obj' (KOTCB (tcbDomain_update (\<lambda>_. d) makeObject)) s"
  unfolding valid_obj'_def valid_tcb'_def valid_tcb_state'_def valid_arch_tcb'_def
  by (clarsimp simp: makeObject_tcb makeObject_cte objBits_simps' newArchTCB_def
                     tcb_cte_cases_def maxDomain_def maxPriority_def numPriorities_def minBound_word)

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
  "\<lbrakk> (s, s') \<in> state_relation; t = kheap_update f s;
     \<exists>f' g' h'.
     t' = s'\<lparr>ksPSpace := f' (ksPSpace s'), gsUserPages := g' (gsUserPages s'),
             gsCNodes := h' (gsCNodes s')\<rparr>;
     null_filter (caps_of_state t) = null_filter (caps_of_state s);
     null_filter' (ctes_of t') = null_filter' (ctes_of s');
     pspace_relation (kheap t) (ksPSpace t'); ready_queues_relation t t';
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
     apply (cut_tac s="kheap_update f s"  and
                    s'="s'\<lparr>ksPSpace := f' (ksPSpace s'),
                           gsUserPages := g' (gsUserPages s'),
                           gsCNodes := h' (gsCNodes s')\<rparr>"
            in pspace_relation_ctes_ofI, simp_all)[1]
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
  apply (clarsimp simp: mask_def add_diff_eq)
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
  assumes x: "makeObjectKO dev d tp = Some v"
  shows
  "(v = KOCTE cte) =
       (tp = Inr (APIObjectType ArchTypes_H.CapTableObject) \<and> cte = makeObject)"
  "(v = KOTCB tcb) =
       (tp = Inr (APIObjectType ArchTypes_H.TCBObject) \<and> tcb = (tcbDomain_update (\<lambda>_. d) makeObject))"
  using x
  by (simp add: makeObjectKO_def eq_commute
         split: apiobject_type.split_asm sum.split_asm kernel_object.split_asm
                ARM_H.object_type.split_asm arch_kernel_object.split_asm)+

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
  apply (simp add: dom_def mask_def add_diff_eq)
  apply fastforce
  done

lemma cte_wp_at_retype':
  assumes ko: "makeObjectKO dev d tp = Some obj"
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
     apply (simp    add: projectKOs the_ctes_makeObject makeObjectKO_eq [OF ko] makeObject_cte
              split del: if_split
                   cong: if_cong)
     apply (insert al ko)
     apply simp
     apply (safe; simp)
              apply ((fastforce simp: makeObjectKO_def makeObject_cte makeObject_tcb tcb_cte_cases_def
                               split: if_split_asm)+)[10]
    apply (clarsimp elim!: obj_atE' simp: projectKOs objBits_simps)
    apply (drule ps_clearD[where y=p and n=tcbBlockSizeBits])
       apply simp
      apply (rule order_trans_rules(17))
       apply (clarsimp cong: if_cong)
      apply (rule word_and_le2)
     apply (simp add: word_neg_and_le[simplified field_simps])
    apply simp
   apply (clarsimp elim!: obj_atE' simp: pn)
  apply (clarsimp elim!: obj_atE' simp: pn)
  done

lemma ctes_of_retype:
  assumes ko: "makeObjectKO dev d tp = Some obj"
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
  assumes ko: "makeObjectKO dev d tp = Some obj"
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
          erule_tac v="if x \<in> set addrs then KOTCB (tcbDomain_update (\<lambda>_. d) makeObject)
                                        else KOCTE cte"
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
  "\<lbrakk> obj_relation_retype (default_object (APIType_map2 ty) dev us d) ko;
       ty \<noteq> Inr (APIObjectType ArchTypes_H.Untyped) \<rbrakk>
      \<Longrightarrow> objBitsKO ko \<le> obj_bits_api (APIType_map2 ty) us"
  by (simp add: obj_relation_retype_def objBits_def obj_bits_dev_irr)

lemma makeObjectKO_Untyped:
  "makeObjectKO dev d ty = Some v \<Longrightarrow> ty \<noteq> Inr (APIObjectType ArchTypes_H.Untyped)"
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
  assumes  orr: "obj_relation_retype (default_object (APIType_map2 ty) dev us d) ko"
  shows  "\<lbrakk> range_cover ptr sz (obj_bits_api (APIType_map2 ty) us) n \<rbrakk> \<Longrightarrow>
   (\<Union>x \<in> set (retype_addrs ptr (APIType_map2 ty) n us).
            fst ` obj_relation_cuts (default_object (APIType_map2 ty) dev us d) x)
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
  "makeObjectKO dev d ty = Some ko \<Longrightarrow>
   objBitsKO ko \<le> obj_bits_api (APIType_map2 ty) us"
  apply (case_tac ty)
    apply (auto simp: default_arch_object_def pageBits_def archObjSize_def pteBits_def pdeBits_def
                      makeObjectKO_def objBits_simps' APIType_map2_def obj_bits_api_def slot_bits_def
               split: Structures_H.kernel_object.splits arch_kernel_object.splits object_type.splits
                      Structures_H.kernel_object.splits arch_kernel_object.splits apiobject_type.splits)
  done

lemma obj_relation_retype_other_obj:
  "\<lbrakk> is_other_obj_relation_type (a_type ko); other_obj_relation ko ko' \<rbrakk>
      \<Longrightarrow> obj_relation_retype ko ko'"
  apply (simp add: obj_relation_retype_def)
  apply (subgoal_tac "objBitsKO ko' = obj_bits ko")
   apply (clarsimp simp: is_other_obj_relation_type other_obj_relation_not_aobj)
  apply (fastforce simp: other_obj_relation_def objBits_simps'
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
      and  ko: "makeObjectKO dev d ty = Some ko"
      and cover: "range_cover ptr sz (obj_bits_api (APIType_map2 ty) us) n"
      and orr: "obj_relation_retype (default_object (APIType_map2 ty) dev us d) ko"
      and num_r: "m = 2 ^ (obj_bits_api (APIType_map2 ty) us - objBitsKO ko) * n"
  shows
  "pspace_relation (foldr (\<lambda>p ps. ps(p \<mapsto> default_object (APIType_map2 ty) dev us d))
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

  note pdom = pspace_dom_upd [OF dom_Int_ra, where ko="default_object (APIType_map2 ty) dev us d"]

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

lemma pspace_no_overlapD':
  "\<lbrakk> ksPSpace s x = Some ko; pspace_no_overlap' p bits s \<rbrakk>
       \<Longrightarrow> {x .. x + 2 ^ objBitsKO ko - 1} \<inter> {p .. (p && ~~ mask bits) + 2 ^ bits - 1} = {}"
  by (simp add: pspace_no_overlap'_def mask_def add_diff_eq)

(* FIXME arch-split: AARCH64 uses mask_range here *)
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

(* FIXME arch-split: move, use as alternative when mask_range comes up *)
lemma new_range_subset':
  "\<lbrakk> range_cover ptr sz (objBitsKO ko) n; x \<in> set (new_cap_addrs n ptr ko) \<rbrakk>
   \<Longrightarrow> mask_range x (objBitsKO ko) \<subseteq> {ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1}"
  by (drule (1) new_range_subset)
     (simp add: mask_def add_diff_eq)

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
      apply (simp add: ps_clear_def dom_if_Some Int_Un_distrib mask_def add_diff_eq
                       objBits_def[symmetric])
      apply (rule conjI)
       apply (erule new_range_disjoint)
      apply (rule disjoint_subset[OF Diff_subset])
      apply (erule disjoint_subset[OF new_range_sub])
      apply (rule pspace_no_overlap_disjoint'[OF vs'(1) pn'])
    apply (clarsimp simp add: ps_clear_def dom_if_Some Int_Un_distrib mask_def add_diff_eq)
    apply (rule conjI)
      apply (erule new_range_disjoint)
     apply (rule disjoint_subset[OF Diff_subset])
     apply (erule disjoint_subset[OF new_range_sub])
     apply (rule pspace_no_overlap_disjoint'[OF vs'(1) pn'])
    apply (clarsimp simp add: ps_clear_def dom_if_Some Int_Un_distrib mask_def add_diff_eq)
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

global_interpretation update_gs: pspace_update_eq' "update_gs ty us ptrs"
  by (simp add: pspace_update_eq'_def)

context begin interpretation Arch . (*FIXME: arch-split*)

lemma ksReadyQueues_update_gs[simp]:
  "ksReadyQueues (update_gs tp us addrs s) = ksReadyQueues s"
  by (simp add: update_gs_def
         split: aobject_type.splits Structures_A.apiobject_type.splits)

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

lemma retype_ksPSpace_dom_same:
  fixes x v
  assumes   vs': "pspace_aligned' s'" "pspace_distinct' s'"
  assumes   pn': "pspace_no_overlap' ptr sz s'"
  assumes    ko: "makeObjectKO dev d ty = Some ko"
  assumes cover: "range_cover ptr sz (obj_bits_api (APIType_map2 ty) us) n"
  assumes num_r: "m = 2 ^ (obj_bits_api (APIType_map2 ty) us - objBitsKO ko) * n"
  shows
    "ksPSpace s' x = Some v \<Longrightarrow>
     foldr (\<lambda>addr. data_map_insert addr ko) (new_cap_addrs m ptr ko) (ksPSpace s') x
      = Some v"
proof -
  have cover':"range_cover ptr sz (objBitsKO ko) m"
    by (rule range_cover_rel[OF cover objBits_le_obj_bits_api[OF ko] num_r])
  assume "ksPSpace s' x = Some v"
  thus ?thesis
    apply (clarsimp simp:foldr_upd_app_if[folded data_map_insert_def])
    apply (drule domI[where m = "ksPSpace s'"])
    apply (drule(1) IntI)
    apply (erule_tac A = "A \<inter> B" for A B in in_emptyE[rotated])
    apply (rule disjoint_subset[OF new_cap_addrs_subset[OF cover']])
    apply (clarsimp simp:ptr_add_def field_simps)
    apply (rule pspace_no_overlap_disjoint'[OF vs'(1) pn'])
    done
qed

lemma retype_ksPSpace_None:
  assumes ad: "pspace_aligned' s" "pspace_distinct' s" "pspace_bounded' s"
  assumes pn: "pspace_no_overlap' ptr sz s"
  assumes cover: "range_cover ptr sz (objBitsKO val + gbits) n"
  shows "\<And>x. x \<in> set (new_cap_addrs (2 ^ gbits * n) ptr val) \<Longrightarrow> ksPSpace s x = None"
proof -
  note cover' = range_cover_rel[where sbit' = "objBitsKO val",OF cover _ refl,simplified]
  show "\<And>x. x \<in> set (new_cap_addrs (2 ^ gbits * n) ptr val) \<Longrightarrow> ksPSpace s x = None"
    apply (drule subsetD[OF new_cap_addrs_subset [OF cover' ]])
    apply (insert pspace_no_overlap_disjoint' [OF ad(1) pn])
    apply (fastforce simp: ptr_add_def p_assoc_help)
    done
qed

lemma retype_tcbSchedPrevs_of:
  assumes   vs': "pspace_aligned' s'" "pspace_distinct' s'"
  assumes   pn': "pspace_no_overlap' ptr sz s'"
  assumes    ko: "makeObjectKO dev d ty = Some ko"
  assumes cover: "range_cover ptr sz (obj_bits_api (APIType_map2 ty) us) n"
  assumes num_r: "m = 2 ^ (obj_bits_api (APIType_map2 ty) us - objBitsKO ko) * n"
  shows
    "tcbSchedPrevs_of
       (s'\<lparr>ksPSpace := foldr (\<lambda>addr. data_map_insert addr ko) (new_cap_addrs m ptr ko) (ksPSpace s')\<rparr>)
     = tcbSchedPrevs_of s'"
proof -
  note dom_same' = retype_ksPSpace_dom_same[OF vs' pn' ko cover num_r]
  show ?thesis
    apply (rule ext)
    apply (clarsimp simp: opt_map_def split: option.splits)
    apply (intro impI conjI allI; (drule dom_same'; simp)?)
    apply (clarsimp simp: foldr_upd_app_if[folded data_map_insert_def]
                   split: if_split_asm kernel_object.split_asm)
    using ko
    by (cases ty;
        simp add: makeObjectKO_def makeObject_tcb projectKOs
           split: kernel_object.split_asm arch_kernel_object.split_asm object_type.split_asm
                  apiobject_type.split_asm if_split_asm)
       fastforce+
qed

lemma retype_tcbSchedNexts_of:
  assumes   vs': "pspace_aligned' s'" "pspace_distinct' s'"
  assumes   pn': "pspace_no_overlap' ptr sz s'"
  assumes    ko: "makeObjectKO dev d ty = Some ko"
  assumes cover: "range_cover ptr sz (obj_bits_api (APIType_map2 ty) us) n"
  assumes num_r: "m = 2 ^ (obj_bits_api (APIType_map2 ty) us - objBitsKO ko) * n"
  shows
    "tcbSchedNexts_of
       (s'\<lparr>ksPSpace := foldr (\<lambda>addr. data_map_insert addr ko) (new_cap_addrs m ptr ko) (ksPSpace s')\<rparr>)
     = tcbSchedNexts_of s'"
proof -
  note dom_same' = retype_ksPSpace_dom_same[OF vs' pn' ko cover num_r]
  show ?thesis
    apply (rule ext)
    apply (clarsimp simp: opt_map_def split: option.splits)
    apply (intro impI conjI allI; (drule dom_same'; simp)?)
    apply (clarsimp simp: foldr_upd_app_if[folded data_map_insert_def]
                   split: if_split_asm kernel_object.split_asm)
    using ko
    by (cases ty;
        simp add: makeObjectKO_def makeObject_tcb projectKOs
           split: kernel_object.split_asm arch_kernel_object.split_asm object_type.split_asm
                  apiobject_type.split_asm if_split_asm)
       fastforce+
qed

lemma retype_inQ:
  assumes   vs': "pspace_aligned' s'" "pspace_distinct' s'"
  assumes   pn': "pspace_no_overlap' ptr sz s'"
  assumes    ko: "makeObjectKO dev d ty = Some ko"
  assumes cover: "range_cover ptr sz (obj_bits_api (APIType_map2 ty) us) n"
  assumes num_r: "m = 2 ^ (obj_bits_api (APIType_map2 ty) us - objBitsKO ko) * n"
  shows
    "\<forall>d p.
      inQ d p |< tcbs_of'
       (s'\<lparr>ksPSpace := foldr (\<lambda>addr. data_map_insert addr ko) (new_cap_addrs m ptr ko) (ksPSpace s')\<rparr>)
      = inQ d p |< tcbs_of' s'"
proof -
  note dom_same' = retype_ksPSpace_dom_same[OF vs' pn' ko cover num_r]
  show ?thesis
    apply (intro allI)
    apply (rule ext)
    apply (clarsimp simp: inQ_def opt_pred_def opt_map_def split: option.splits)
    apply (intro impI conjI allI; (drule dom_same'; simp)?)
    apply (clarsimp simp: foldr_upd_app_if[folded data_map_insert_def]
                   split: if_split_asm kernel_object.split_asm)
    using ko
    by (cases ty;
        fastforce simp  add: makeObjectKO_def makeObject_tcb projectKOs
           split: kernel_object.split_asm arch_kernel_object.split_asm object_type.split_asm
                  apiobject_type.split_asm if_split_asm
        | fastforce)+
qed

lemma retype_ready_queues_relation:
  assumes  rlqr: "ready_queues_relation s s'"
  assumes   vs': "pspace_aligned' s'" "pspace_distinct' s'"
  assumes   pn': "pspace_no_overlap' ptr sz s'"
  assumes    ko: "makeObjectKO dev d ty = Some ko"
  assumes cover: "range_cover ptr sz (obj_bits_api (APIType_map2 ty) us) n"
  assumes num_r: "m = 2 ^ (obj_bits_api (APIType_map2 ty) us - objBitsKO ko) * n"
  shows
    "ready_queues_relation
       (s \<lparr>kheap := foldr (\<lambda>p. data_map_insert p (default_object (APIType_map2 ty) dev us d))
                                             (retype_addrs ptr (APIType_map2 ty) n us) (kheap s)\<rparr>)
       (s'\<lparr>ksPSpace := foldr (\<lambda>addr. data_map_insert addr ko) (new_cap_addrs m ptr ko) (ksPSpace s')\<rparr>)"
  using rlqr
  unfolding ready_queues_relation_def Let_def
  by (clarsimp simp: retype_tcbSchedNexts_of[OF vs' pn' ko cover num_r, simplified]
                     retype_tcbSchedPrevs_of[OF vs' pn' ko cover num_r, simplified]
                     retype_inQ[OF vs' pn' ko cover num_r, simplified])

lemma retype_state_relation:
  notes data_map_insert_def[simp del]
  assumes  sr:   "(s, s') \<in> state_relation"
      and  vs:   "valid_pspace s" "valid_mdb s"
      and  et:   "valid_list s"
      and vs':   "pspace_aligned' s'" "pspace_distinct' s'"
      and  pn:   "pspace_no_overlap_range_cover ptr sz s"
      and pn':   "pspace_no_overlap' ptr sz s'"
      and cover: "range_cover ptr sz (obj_bits_api (APIType_map2 ty) us) n"
      and  ko:   "makeObjectKO dev d ty = Some ko"
      and api:   "obj_bits_api (APIType_map2 ty) us \<le> sz"
      and orr:   "obj_relation_retype (default_object (APIType_map2 ty) dev us d) ko"
      and num_r: "m = 2 ^ (obj_bits_api (APIType_map2 ty) us - objBitsKO ko) * n"
  shows
  "(s \<lparr>kheap :=
              foldr (\<lambda>p. data_map_insert p (default_object (APIType_map2 ty) dev us d))
               (retype_addrs ptr (APIType_map2 ty) n us) (kheap s)\<rparr>,
           update_gs (APIType_map2 ty) us (set (retype_addrs ptr (APIType_map2 ty) n us))
            (s'\<lparr>ksPSpace :=
                  foldr (\<lambda>addr. data_map_insert addr ko) (new_cap_addrs m ptr ko)
                   (ksPSpace s')\<rparr>))
          \<in> state_relation"
  (is "(s\<lparr>kheap := ?ps\<rparr>, update_gs _ _ _ (s'\<lparr>ksPSpace := ?ps'\<rparr>))
       \<in> state_relation")
  proof (rule state_relation_null_filterE[OF sr refl _ _ _ _ _ _ _ vs'],
         simp_all add: trans_state_update[symmetric] del: trans_state_update)

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

  have pn2: "\<forall>a\<in>set ?al. kheap s a = None"
    by (rule ccontr) (clarsimp simp: pspace_no_overlapD1[OF pn _ cover vs(1)])

  from sr have gr: "ghost_relation (kheap s) (gsUserPages s') (gsCNodes s')"
    by (rule state_relationE[simplified ghost_relation_wrapper_def]) (* FIXME arch-split *)

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

  have rdyqrel: "ready_queues_relation s s'"
    using sr by (simp add: state_relation_def)

  thus "ready_queues_relation_2 (ready_queues s) (ksReadyQueues s')
                                (?ps' |> tcb_of' |> tcbSchedNext) (?ps' |> tcb_of' |> tcbSchedPrev)
                                (\<lambda>d p. inQ d p |< (?ps' |> tcb_of'))"
    using retype_ready_queues_relation[OF _ vs' pn' ko cover num_r]
    by (clarsimp simp: ready_queues_relation_def Let_def)

qed

lemma new_cap_addrs_fold':
  "1 \<le> n \<Longrightarrow>
   map (\<lambda>n. ptr + (n << objBitsKO ko)) [0.e.n - 1] =
   new_cap_addrs (unat n) ptr ko"
 by (clarsimp simp:new_cap_addrs_def ptr_add_def upto_enum_red'
           shiftl_t2n power_add field_simps)

lemma objBitsKO_gt_0: "0 < objBitsKO ko"
  apply (case_tac ko)
        apply (simp_all add: objBits_simps' pageBits_def)
  apply (rename_tac arch_kernel_object)
  apply (case_tac arch_kernel_object)
    apply (simp_all add:archObjSize_def pageBits_def pteBits_def pdeBits_def)
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

lemma corres_retype':
  assumes    not_zero: "n \<noteq> 0"
  and         aligned: "is_aligned ptr (objBitsKO ko + gbits)"
  and    obj_bits_api: "obj_bits_api (APIType_map2 ty) us = objBitsKO ko + gbits"
  and           check: "(sz < obj_bits_api (APIType_map2 ty) us) = (sz < objBitsKO ko + gbits)"
  and             usv: "APIType_map2 ty = Structures_A.CapTableObject \<Longrightarrow> 0 < us"
  and              ko: "makeObjectKO dev d ty = Some ko"
  and             orr: "obj_bits_api (APIType_map2 ty) us \<le> sz \<Longrightarrow>
                        obj_relation_retype (default_object (APIType_map2 ty) dev us d) ko"
  and           cover: "range_cover ptr sz (obj_bits_api (APIType_map2 ty) us) n"
  shows "corres (\<lambda>rv rv'. rv' = g rv)
                (\<lambda>s. valid_pspace s \<and> pspace_no_overlap_range_cover ptr sz s
                     \<and> valid_mdb s \<and> valid_list s)
                (\<lambda>s. pspace_aligned' s \<and> pspace_distinct' s \<and> pspace_no_overlap' ptr sz s
                      \<and> (ty = Inr (APIObjectType TCBObject) \<longrightarrow> d = ksCurDomain s))
                (retype_region ptr n us (APIType_map2 ty) dev)
                (do addrs \<leftarrow> createObjects ptr n ko gbits;
                    _ \<leftarrow> modify (update_gs (APIType_map2 ty) us (set addrs));
                    return (g addrs)
                 od)"
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
  apply (simp add: when_def retype_region_def createObjects'_def
                   createObjects_def aligned obj_bits_api[symmetric]
                   ko[symmetric] al' shiftl_t2n data_map_insert_def[symmetric]
                   is_aligned_mask[symmetric] split_def unless_def
                   lookupAround2_pspace_no check
        split del: if_split)
  apply (subst retype_addrs_fold)+
  apply (subst if_P)
    using ko
    apply (clarsimp simp: makeObjectKO_def)
   apply (simp add: bind_assoc)
   apply (rule corres_guard_imp)
     apply (rule_tac r'=pspace_relation in corres_underlying_split)
        apply (clarsimp dest!: state_relation_pspace_relation)
       apply (simp add: gets_def)
       apply (rule corres_symb_exec_l[rotated])
          apply (rule exs_valid_get)
         apply (rule get_sp)
        apply (simp add: get_def no_fail_def)
       apply (rule corres_symb_exec_r)
          apply (simp add: not_less modify_modify bind_assoc[symmetric]
                           obj_bits_api[symmetric] shiftl_t2n upto_enum_red'
                           range_cover.unat_of_nat_n[OF cover])
          apply (rule corres_guard_imp)
            apply (rule corres_split_nor[OF _ corres_trivial])
               apply (rename_tac ps ps' sa)
               apply (rule_tac P="\<lambda>s. ps = kheap s \<and> sa = s \<and> ?P s" and
                               P'="\<lambda>s. ps' = ksPSpace s \<and> ?P' s" in corres_modify)
               apply(frule curdomain_relation[THEN sym])
               apply (simp add: set_retype_addrs_fold new_caps_adds_fold)
               apply (drule retype_state_relation[OF _ _ _ _ _ _ _ _ cover _ _ orr],
                      simp_all add: ko not_zero obj_bits_api
                                    bound[simplified obj_bits_api ko])[1]
               apply (cases ty; simp; rename_tac tp; case_tac tp;
                      clarsimp simp: default_object_def APIType_map2_def
                              split: arch_kernel_object.splits apiobject_type.splits)
              apply (clarsimp simp: retype_addrs_fold[symmetric] ptr_add_def upto_enum_red' not_zero'
                                    range_cover.unat_of_nat_n[OF cover] word_le_sub1)
              apply (rule_tac f=g in arg_cong)
              apply clarsimp
             apply wpsimp+
           apply simp+
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
      apply wpsimp+
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
      apply (clarsimp simp: ARM_H.toAPIType_def APIType_capBits_def
                     split: ARM_H.object_type.splits)

       \<comment> \<open>SmallPageObject\<close>
       apply (wp mapM_x_wp' hoare_vcg_op_lift)
        apply (simp add: valid_cap'_def capAligned_def n_less_word_bits
                         ball_conj_distrib)
        apply (wp createObjects_aligned2 createObjects_nonzero[OF not_0 ,simplified]
                 cwo_ret[OF _ not_0]
         | simp add: objBits_if_dev pageBits_def ptr range_cover_n_wb)+
       apply (simp add:pageBits_def ptr word_bits_def)
      \<comment> \<open>LargePageObject\<close>
      apply (wp mapM_x_wp' hoare_vcg_op_lift)
       apply (simp add: valid_cap'_def capAligned_def n_less_word_bits
                        ball_conj_distrib)
       apply (wp createObjects_aligned2 createObjects_nonzero[OF not_0 ,simplified]
                 cwo_ret[OF _ not_0]
         | simp add: objBits_if_dev pageBits_def ptr range_cover_n_wb)+
      apply (simp add:pageBits_def ptr word_bits_def)

     \<comment> \<open>SectionObject\<close>
     apply (wp mapM_x_wp' hoare_vcg_op_lift)
      apply (simp add: valid_cap'_def capAligned_def n_less_word_bits
                       ball_conj_distrib)
      apply (wp createObjects_aligned2 createObjects_nonzero[OF not_0 ,simplified]
                cwo_ret[OF _ not_0]
       | simp add: objBits_if_dev pageBits_def ptr range_cover_n_wb)+
     apply (simp add:pageBits_def ptr word_bits_def)

    \<comment> \<open>SuperSectionObject\<close>
    apply (wp mapM_x_wp' hoare_vcg_op_lift)
     apply (simp add: valid_cap'_def capAligned_def n_less_word_bits
                      ball_conj_distrib)
     apply (wp createObjects_aligned2 createObjects_nonzero[OF not_0 ,simplified]
               cwo_ret[OF _ not_0]
       | simp add: objBits_if_dev pageBits_def ptr range_cover_n_wb)+
    apply (simp add:pageBits_def ptr word_bits_def)

   \<comment> \<open>PageTableObject\<close>
    apply (wp mapM_x_wp' hoare_vcg_op_lift)
     apply (simp add: valid_cap'_def capAligned_def n_less_word_bits)
     apply (simp only: imp_conv_disj page_table_at'_def
                       typ_at_to_obj_at_arches)
     apply (rule hoare_strengthen_post)
      apply (rule hoare_vcg_conj_lift)
       apply (rule createObjects_aligned [OF _ range_cover.range_cover_n_less(1)
           [where 'a=32, unfolded word_bits_len_of, OF cover] not_0])
       apply (simp add:objBits_simps archObjSize_def ptBits_def pageBits_def
                       pdeBits_def pteBits_def)+
      apply (simp add:range_cover_def word_bits_def)
      apply (rule createObjects_obj_at[where 'a =pte, OF _  not_0])
        apply (simp add:objBits_simps archObjSize_def ptBits_def pageBits_def
                        pdeBits_def pteBits_def)+
      apply (simp add: projectKOs projectKO_opt_pte)
     apply simp
    apply (clarsimp simp: objBits_simps archObjSize_def ptBits_def pageBits_def
                          pdeBits_def pteBits_def)
    apply clarsimp
  \<comment> \<open>PageDirectoryObject\<close>
   apply (wp mapM_x_wp' hoare_vcg_op_lift)
   apply (simp add: valid_cap'_def capAligned_def n_less_word_bits)
   apply (simp only: imp_conv_disj page_directory_at'_def
                     typ_at_to_obj_at_arches)
   apply (rule hoare_strengthen_post)
     apply (rule hoare_vcg_conj_lift)
      apply (rule createObjects_aligned [OF _ range_cover.range_cover_n_less(1)
          [where 'a=32, unfolded word_bits_len_of, OF cover] not_0])
       apply (simp add:objBits_simps archObjSize_def ptBits_def pageBits_def pdBits_def
                       pdeBits_def pteBits_def)+
      apply (simp add:range_cover_def word_bits_def)
     apply (rule createObjects_obj_at [where 'a=pde, OF _  not_0])
      apply (simp add:objBits_simps archObjSize_def ptBits_def pageBits_def pdBits_def
                      pdeBits_def pteBits_def)
     apply (simp add: projectKOs projectKO_opt_pde)
    apply simp
   apply (clarsimp simp: objBits_simps archObjSize_def pdBits_def pageBits_def
                         pdeBits_def pteBits_def)
   apply clarsimp
   done
  next
    case (Some a) thus ?thesis
    proof(cases a)
      case Untyped with Some cover ct show ?thesis
        apply (clarsimp simp: Arch_createNewCaps_def createNewCaps_def)
        apply (simp_all add: ARM_H.toAPIType_def fromIntegral_def
                             toInteger_nat fromInteger_nat APIType_capBits_def
                      split: ARM_H.object_type.splits)
        apply wp
        apply (intro ballI)
        apply (clarsimp simp: image_def upto_enum_red' valid_cap'_def capAligned_def
                              canonical_address_def
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
        apply (simp add: mask_def add_diff_eq)
        apply (drule psubset_imp_subset)
        apply (drule(1) disjoint_subset2[rotated])
        apply (drule(1) disjoint_subset)
        apply (drule(1) range_cover_subset_not_empty)
        apply clarsimp+
       apply (simp add: mask_def add_diff_eq)
       apply blast
      apply (drule(1) range_cover_no_0[OF ptr _ unat_less_helper])
      apply simp
      done
    next
      case TCBObject with Some cover ct show ?thesis
        including no_pre
        apply (clarsimp simp: Arch_createNewCaps_def createNewCaps_def)
        apply (simp_all add: ARM_H.toAPIType_def
                             fromIntegral_def toInteger_nat fromInteger_nat APIType_capBits_def curDomain_def
                      split: ARM_H.object_type.splits)
        apply (wp mapM_x_wp' hoare_vcg_const_Ball_lift)+
         apply (rule hoare_post_imp)
          prefer 2
          apply (rule createObjects_obj_at [where 'a = "tcb",OF _ not_0])
           using cover
           apply (clarsimp simp: ARM_H.toAPIType_def APIType_capBits_def objBits_simps
                          split: ARM_H.object_type.splits)
           apply (simp add: projectKOs)+
         apply (clarsimp simp: valid_cap'_def objBits_simps)
         apply (fastforce intro: capAligned_tcbI)
        apply wp
        done
    next
      case EndpointObject with Some cover ct show ?thesis
        including no_pre
        apply (clarsimp simp: Arch_createNewCaps_def createNewCaps_def)
        apply (simp_all add: ARM_H.toAPIType_def
                             fromIntegral_def toInteger_nat fromInteger_nat APIType_capBits_def
                      split: ARM_H.object_type.splits)
        apply wp
        apply (rule hoare_post_imp)
         prefer 2
         apply (rule createObjects_obj_at [where 'a=endpoint, OF _ not_0])
          using cover
          apply (clarsimp simp: ARM_H.toAPIType_def APIType_capBits_def objBits_simps
                         split: ARM_H.object_type.splits)
         apply (simp add: projectKOs)
        apply (clarsimp simp: valid_cap'_def objBits_simps)
        apply (fastforce intro: capAligned_epI)
        done
    next
      case NotificationObject with Some cover ct show ?thesis
        including no_pre
        apply (clarsimp simp: Arch_createNewCaps_def createNewCaps_def)
        apply (simp_all add: ARM_H.toAPIType_def
                             fromIntegral_def toInteger_nat fromInteger_nat APIType_capBits_def
                      split: ARM_H.object_type.splits)
        apply wp
        apply (rule hoare_post_imp)
         prefer 2
         apply (rule createObjects_obj_at [where 'a="notification", OF _ not_0])
          using cover
          apply (clarsimp simp: ARM_H.toAPIType_def APIType_capBits_def objBits_simps
                         split: ARM_H.object_type.splits)
         apply (simp add: projectKOs)
        apply (clarsimp simp: valid_cap'_def objBits_simps)
        apply (fastforce intro: capAligned_ntfnI)
        done
    next
      case CapTableObject with Some cover ct show ?thesis
        apply (clarsimp simp: Arch_createNewCaps_def createNewCaps_def)
        apply (simp_all add: ARM_H.toAPIType_def
                             fromIntegral_def toInteger_nat fromInteger_nat APIType_capBits_def
                      split: ARM_H.object_type.splits)
        apply wp
         apply (clarsimp simp: ARM_H.toAPIType_def APIType_capBits_def objBits_simps
                        split: ARM_H.object_type.split object_type.splits)
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
             | _ \<Rightarrow> False \<rbrakk> \<Longrightarrow>
    obj_relation_retype (default_object ty dev n d) ko"
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

lemma word_to_tcb_flags_0[simp]:
  "word_to_tcb_flags 0 = {}"
  by (clarsimp simp: word_to_tcb_flags_def)

lemma tcb_relation_retype:
  "obj_relation_retype (default_object Structures_A.TCBObject dev n d)
                       (KOTCB (tcbDomain_update (\<lambda>_. d) makeObject))"
  by (clarsimp simp: tcb_relation_cut_def default_object_def obj_relation_retype_def
                     tcb_relation_def default_tcb_def
                     makeObject_tcb makeObject_cte new_context_def newContext_def
                     fault_rel_optionation_def initContext_def default_priority_def
                     default_arch_tcb_def newArchTCB_def arch_tcb_relation_def objBits_simps')

lemma captable_relation_retype:
  "n < word_bits \<Longrightarrow>
   obj_relation_retype (default_object Structures_A.CapTableObject dev n d) (KOCTE makeObject)"
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
  "obj_relation_retype (default_object (ArchObject PageTableObj) dev n d)
                       (KOArch (KOPTE makeObject))"
  apply (simp add: default_object_def default_arch_object_def
                   makeObject_pte obj_relation_retype_def
                   objBits_simps archObjSize_def
                   pte_relation_def)
  apply (clarsimp simp: range_composition[symmetric]
                        shiftl_t2n field_simps)
  apply (subst image_comp [symmetric, where g=ucast, unfolded o_def])
  apply (simp add: ucast_range_less pteBits_def)
  apply (fastforce simp:pte_relation_aligned_def)
  done

lemma pagedirectory_relation_retype:
  "obj_relation_retype (default_object (ArchObject PageDirectoryObj) dev n d)
                       (KOArch (KOPDE makeObject))"
  apply (simp add: default_object_def default_arch_object_def
                   makeObject_pde obj_relation_retype_def
                   objBits_simps archObjSize_def
                   pde_relation_def)
  apply (clarsimp simp: range_composition[symmetric]
                        shiftl_t2n field_simps)
  apply (subst image_comp [symmetric, where g=ucast, unfolded o_def])
  apply (simp add: ucast_range_less pdeBits_def)
  apply (fastforce simp:pde_relation_aligned_def)
  done

lemmas makeObjectKO_simps = makeObjectKO_def[split_simps ARM_H.object_type.split
 apiobject_type.split sum.split kernel_object.split ]

lemma corres_retype:
  assumes    not_zero: "n \<noteq> 0"
  and         aligned: "is_aligned ptr (objBitsKO ko + gbits)"
  and    obj_bits_api: "obj_bits_api (APIType_map2 ty) us = objBitsKO ko + gbits"
  and              tp: "APIType_map2 ty \<in> no_gs_types"
  and              ko: "makeObjectKO dev d ty = Some ko"
  and             orr: "obj_bits_api (APIType_map2 ty) us \<le> sz \<Longrightarrow>
                        obj_relation_retype (default_object (APIType_map2 ty) dev us d) ko"
  and           cover: "range_cover ptr sz (obj_bits_api (APIType_map2 ty) us) n"
  shows "corres (=)
  (\<lambda>s. valid_pspace s \<and> pspace_no_overlap_range_cover ptr sz s
     \<and> valid_mdb s \<and> valid_list s)
  (\<lambda>s. pspace_aligned' s \<and> pspace_distinct' s \<and> pspace_no_overlap' ptr sz s
       \<and> (\<exists>val. ko = injectKO val)
       \<and> (ty = Inr (APIObjectType TCBObject) \<longrightarrow> d = ksCurDomain s))
  (retype_region ptr n us (APIType_map2 ty) dev) (createObjects ptr n ko gbits)"
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
  "init_arch_objects (APIType_map2 (Inr ty)) dev ptr bits sz refs =
     (case ty of APIObjectType _ \<Rightarrow> return ()
   | _ \<Rightarrow> init_arch_objects (APIType_map2 (Inr ty)) dev ptr bits sz refs)"
  apply (clarsimp split: ARM_H.object_type.split)
  apply (simp add: init_arch_objects_def APIType_map2_def
            split: apiobject_type.split)
  done

lemma pde_relation_aligned_eq:
  "\<lbrakk>is_aligned (pd::word32) 6; is_aligned pd' 6\<rbrakk>
   \<Longrightarrow> pde_relation_aligned (pd + x >> 2) xa ya =
       pde_relation_aligned (pd' + x >> 2) xa ya"
  apply (clarsimp simp: pde_relation_aligned_def is_aligned_mask mask_def
                 split: ARM_H.pde.splits)
  apply word_bitwise
  apply auto
  done

lemma copyGlobalMappings_corres:
  "corres dc (valid_arch_state and pspace_aligned and page_directory_at pd)
             (valid_arch_state' and page_directory_at' pd)
          (copy_global_mappings pd)
          (copyGlobalMappings pd)"
  apply (simp add: copy_global_mappings_def
                   copyGlobalMappings_def
                   objBits_simps archObjSize_def
                   pd_bits_def pdBits_def mapM_x_mapM)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr)
       apply (rule corres_trivial, clarsimp simp: state_relation_def arch_state_relation_def)
      apply (rule_tac F ="is_aligned pd 6 \<and> is_aligned global_pd 6" in corres_gen_asm)
      apply (simp add: liftM_def[symmetric])
      apply (rule_tac S="(=)" and r'=dc
                  and Q="\<lambda>xs s. \<forall>x \<in> set xs. pde_at (global_pd + (x << 2)) s
                                             \<and> pde_at (pd + (x << 2)) s \<and> pspace_aligned s"
                  and Q'="\<lambda>xs s. \<forall>x \<in> set xs. pde_at' (global_pd + (x << 2)) s
                                             \<and> pde_at' (pd + (x << 2)) s"
                         in corres_mapM_list_all2, (simp add: pdeBits_def)+)
         apply (rule corres_guard_imp, rule corres_split)
              apply (rule_tac getObject_PDE_corres[OF refl])
             apply (rule storePDE_corres[OF _ refl])
             apply clarsimp
             apply (drule(1) pde_relation_aligned_eq)
             apply fastforce
            apply (wp hoare_vcg_const_Ball_lift | simp)+
      apply (simp add: kernel_base_def ARM.pptrBase_def pptrBase_def list_all2_refl pageBits_def)
     apply wp+
   apply (clarsimp simp: valid_arch_state_def)
   apply (auto elim: page_directory_pde_atI is_aligned_weaken[OF pd_aligned])[1]
  apply (clarsimp simp: valid_arch_state'_def)
  apply (auto simp: le_less_trans elim!: page_directory_pde_atI'[simplified pageBits_def, simplified])
  done

(* FIXME: move *)
lemma copyGlobalMappings_cte_wp_at[wp]:
  "\<lbrace>\<lambda>s. P (cte_wp_at' P' p s)\<rbrace>
     copyGlobalMappings pd
   \<lbrace>\<lambda>rv s. P (cte_wp_at' P' p s)\<rbrace>"
  apply (simp add: copyGlobalMappings_def)
  apply (wp mapM_x_wp')
  done

crunch copyGlobalMappings
  for ct[wp]: "\<lambda>s. P (ksCurThread s)"
  (wp: setObject_ksPSpace_only updateObject_default_inv mapM_x_wp')

crunch copyGlobalMappings
  for ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  (wp: setObject_ksPSpace_only updateObject_default_inv mapM_x_wp')

lemmas copyGlobalMappings_ctes_of[wp]
    = ctes_of_from_cte_wp_at[where Q="\<top>", simplified,
                             OF copyGlobalMappings_cte_wp_at]

lemmas object_splits =
  apiobject_type.split_asm
  ARM_H.object_type.split_asm
  sum.split_asm kernel_object.split_asm
  arch_kernel_object.split_asm

declare hoare_in_monad_post[wp del]
declare univ_get_wp[wp del]

crunch createNewCaps
  for ksArch[wp]: "\<lambda>s. P (ksArchState s)"
  and gsMaxObjectSize[wp]: "\<lambda>s. P (gsMaxObjectSize s)"
  and ksInterrupt[wp]: "\<lambda>s. P (ksInterruptState s)"
  (simp: crunch_simps unless_def wp: crunch_wps updateObject_default_inv setObject_ksInterrupt)

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
interpretation Arch . (*FIXME: arch-split*)

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
  (* FIXME arch-split: this is struggling with the formulation of new_range_subset vs mask_range *)
  apply (drule (1) new_range_subset)
  apply (simp only: shiftl_t2n mult_1_right mask_2pm1 add_diff_eq)
  done

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
    apply (cases "n = 0"; clarsimp simp: new_cap_addrs_def mask_def field_simps)
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

context begin interpretation Arch . (*FIXME: arch-split*)
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
     apply (simp add:Int_ac add_mask_fold)
    apply (drule(1) subset_trans)
    apply (simp only: add_mask_fold)
   apply (frule(1) obj_range'_subset_strong)
   apply (drule(1) non_disjoing_subset)
   apply blast
  apply (thin_tac "\<forall>x. Q x" for Q)
  apply (frule aligned_untypedRange_non_empty)
   apply (simp add:isCap_simps)
  apply (frule(1) obj_range'_subset)
  apply (drule(1) subset_trans)
   apply (erule impE)
    apply (clarsimp simp: add_mask_fold)
    apply blast
   apply (simp only: add_mask_fold)
   apply blast
  done
qed

definition caps_overlap_reserved' :: "word32 set \<Rightarrow> kernel_state \<Rightarrow> bool"
where
 "caps_overlap_reserved' S s \<equiv> \<forall>cte \<in> ran (ctes_of s).
  (isUntypedCap (cteCap cte) \<longrightarrow> usableUntypedRange (cteCap cte) \<inter> S = {})"

lemma createObjects_valid_pspace':
  assumes  mko: "makeObjectKO dev d ty = Some val"
  and    max_d: "ty = Inr (APIObjectType TCBObject) \<longrightarrow> d \<le> maxDomain"
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
     apply (clarsimp simp: makeObjectKO_def max_d
                    split: bool.split_asm sum.split_asm
                           ARM_H.object_type.split_asm
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
      apply (rename_tac thread_state mcp priority bool option nat cptr vptr bound tcbprev tcbnext tcbflags tcbarch)
      apply (case_tac thread_state, simp_all add: valid_tcb_state'_def valid_bound_tcb'_def
                                                  valid_bound_ntfn'_def obj_at_disj' opt_tcb_at'_def
                                                  valid_arch_tcb'_def
                                           split: option.splits)[5]
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

abbreviation
 "injectKOS \<equiv> (injectKO :: ('a :: pspace_storable) \<Rightarrow> kernel_object)"

lemma createObjects_valid_pspace_untyped':
  assumes  mko: "makeObjectKO dev d ty = Some val"
  and    max_d: "ty = Inr (APIObjectType TCBObject) \<longrightarrow> d \<le> maxDomain"
  and    not_0: "n \<noteq> 0"
  and    cover: "range_cover ptr sz (objBitsKO val + gbits) n"
  shows "\<lbrace>\<lambda>s. pspace_no_overlap' ptr sz s \<and> valid_pspace' s \<and> caps_no_overlap'' ptr sz s \<and> ptr \<noteq> 0
            \<and> caps_overlap_reserved' {ptr .. ptr + of_nat (n * 2^gbits * 2 ^ objBitsKO val ) - 1} s \<rbrace>
  createObjects' ptr n val gbits \<lbrace>\<lambda>r. valid_pspace'\<rbrace>"
  apply (wp createObjects_valid_pspace' [OF mko max_d not_0 cover])
  apply simp
  done

lemma getObject_valid_pde'[wp]:
  "\<lbrace>valid_objs'\<rbrace> getObject x \<lbrace>valid_pde'\<rbrace>"
  apply (rule hoare_chain)
    apply (rule hoare_vcg_conj_lift)
     apply (rule getObject_ko_at, simp)
     apply (simp add: objBits_simps archObjSize_def pdeBits_def)
    apply (rule getObject_inv[where P=valid_objs'])
    apply (simp add: loadObject_default_inv)
   apply simp
  apply (clarsimp simp: projectKOs valid_obj'_def dest!: obj_at_valid_objs')
  done

crunch copyGlobalMappings
  for valid_objs'[wp]: "valid_objs'"
  (ignore: storePDE wp: crunch_wps)
crunch copyGlobalMappings
  for pspace_aligned'[wp]: "pspace_aligned'"
  (wp: crunch_wps)
crunch copyGlobalMappings
  for pspace_distinct'[wp]: "pspace_distinct'"
  (wp: crunch_wps)

lemmas storePDE_valid_mdb[wp]
    = storePDE_ctes[where P=valid_mdb_ctes, folded valid_mdb'_def]
crunch copyGlobalMappings
  for valid_mdb[wp]: "valid_mdb'"
  (wp: crunch_wps)

crunch copyGlobalMappings
  for no_0_obj'[wp]: no_0_obj'
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
  apply (simp add: tcb_cte_cases_def tcb_cte_cases_neqs)
  including classic_wp_pre
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
  including classic_wp_pre
  unfolding createNewCaps_def Arch_createNewCaps_def createObjects_def ARM_H.toAPIType_def
  apply (case_tac ty; simp split del: if_split cong: if_cong)
        apply (rename_tac apiobject_type)
        apply (case_tac apiobject_type; simp split del: if_split)
            apply (rule hoare_pre, wp, simp add: createObjects_def)
           apply ((wp createObjects_orig_cte_wp_at2'[where sz = sz] mapM_x_wp')
                   | assumption
                   | clarsimp simp: APIType_capBits_def projectKOs projectKO_opts_defs
                                    makeObject_tcb tcb_cte_cases_def cteSizeBits_def
                                    pageBits_def archObjSize_def ptBits_def pteBits_def
                                    pdBits_def pdeBits_def createObjects_def curDomain_def
                                    objBits_if_dev
                         split del: if_split
                   | simp add: objBits_simps field_simps mult_2_right)+
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
   apply (wpc|wp|simp del: fun_upd_apply data_map_insert_def)+
   apply (simp only: alignError_def, wp)
  apply (subst data_map_insert_def[symmetric])+
  apply clarsimp
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

crunch doMachineOp
  for ko_wp_at'[wp]: "\<lambda>s. P (ko_wp_at' P' p s)"

lemma createObjects_orig_cte_wp_at':
  "\<lbrace>\<lambda>s. range_cover ptr sz (objBitsKO val + gbits) n \<and> n \<noteq> 0
      \<and> pspace_aligned' s \<and> pspace_distinct' s
      \<and> cte_wp_at' P p s
      \<and> pspace_no_overlap' ptr sz s\<rbrace>
  createObjects' ptr n val gbits \<lbrace>\<lambda>r s. cte_wp_at' P p s\<rbrace>"
  apply (simp add: cte_wp_at'_obj_at' tcb_cte_cases_def tcb_cte_cases_neqs)
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
  apply (simp add: createNewCaps_def ARM_H.toAPIType_def
              split del: if_split)
  apply (case_tac ty; simp add: Arch_createNewCaps_def
                           split del: if_split)
        apply (rename_tac apiobject_type)
        apply (case_tac apiobject_type; simp split del: if_split)
            apply (rule hoare_pre, wp, simp)
           apply (wp createObjects_orig_cte_wp_at'[where sz = sz] mapM_x_wp'
                     threadSet_cte_wp_at'T
                  | clarsimp simp: objBits_simps APIType_capBits_def createObjects_def curDomain_def
                    pageBits_def ptBits_def pdBits_def archObjSize_def pteBits_def pdeBits_def
                  | intro conjI impI
                  | force simp: tcb_cte_cases_def tcb_cte_cases_neqs)+
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
    apply (simp add: Int_absorb ptr_add_def p_assoc_help mask_def
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
   apply (simp add: add_mask_fold)
   apply blast
  apply (intro allI)
  apply (drule_tac x = ptr' in spec)
  apply (rule ccontr)
  apply (clarsimp simp del: atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
                            Int_atLeastAtMost atLeastatMost_empty_iff)
  apply (drule(2) disjoint_subset2 [OF obj_range'_subset])
  apply (drule(1) disjoint_subset2)
  apply (simp add: Int_absorb ptr_add_def p_assoc_help mask_def
              del: atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
                   Int_atLeastAtMost atLeastatMost_empty_iff)
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

crunch copyGlobalMappings
  for state_refs_of'[wp]: "\<lambda>s. P (state_refs_of' s)"
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
  apply (clarsimp simp: ARM_H.toAPIType_def
             split del: if_split)
  apply (cases ty; simp add: createNewCaps_def Arch_createNewCaps_def
                        split del: if_split)
        apply (rename_tac apiobject_type)
        apply (case_tac apiobject_type; simp split del: if_split)
            apply (rule hoare_pre, wp, simp)
           apply (insert cover not_0)
           apply (wp mapM_x_wp' createObjects_state_refs_of'' threadSet_state_refs_of'
                    | simp add: not_0 pspace_no_overlap'_def objBitsKO_def APIType_capBits_def
                                valid_pspace'_def makeObject_tcb makeObject_endpoint objBits_def
                                makeObject_notification pageBits_def ptBits_def pdBits_def
                                archObjSize_def createObjects_def curDomain_def
                                pdeBits_def pteBits_def
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

crunch copyGlobalMappings
  for ksReadyQueues[wp]: "\<lambda>s. P (ksReadyQueues s)"
  (wp: updateObject_default_inv crunch_wps)
crunch copyGlobalMappings
  for ksReadyQueuesL1[wp]: "\<lambda>s. P (ksReadyQueuesL1Bitmap s)"
  (wp: updateObject_default_inv crunch_wps)
crunch copyGlobalMappings
  for ksReadyQueuesL2[wp]: "\<lambda>s. P (ksReadyQueuesL2Bitmap s)"
  (wp: updateObject_default_inv crunch_wps)

crunch copyGlobalMappings
  for valid_idle'[wp]: "valid_idle'"
  (simp: objBits_simps archObjSize_def
     wp: updateObject_default_inv crunch_wps setObject_idle' refl)

crunch copyGlobalMappings
  for iflive'[wp]: "if_live_then_nonz_cap'"
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
  apply (clarsimp simp: toAPIType_def ARM_H.toAPIType_def)
  apply (cases ty, simp_all add: createNewCaps_def Arch_createNewCaps_def
                      split del: if_split)
        apply (rename_tac apiobject_type)
        apply (case_tac apiobject_type, simp_all split del: if_split)[1]
            apply (rule hoare_pre, wp, simp)
           apply (wp mapM_x_wp' createObjects_iflive' threadSet_iflive'
                | simp add: not_0 pspace_no_overlap'_def createObjects_def live'_def hyp_live'_def
                                valid_pspace'_def makeObject_tcb makeObject_endpoint
                                 makeObject_notification objBitsKO_def
                                 APIType_capBits_def objBits_def pageBits_def
                                 archObjSize_def ptBits_def pdBits_def
                                 pteBits_def pdeBits_def
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

crunch createObjects, createNewCaps
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

lemma createObjects'_ct[wp]:
  "\<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace> createObjects' p n v us \<lbrace>\<lambda>rv s. P (ksCurThread s)\<rbrace>"
  by (rule createObjects_pspace_only, simp)

crunch createObjects, doMachineOp, createNewCaps
  for ct[wp]: "\<lambda>s. P (ksCurThread s)"
  and ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  (wp: crunch_wps simp: crunch_simps)

lemma copyGlobalMappings_ko_wp_at:
  "\<lbrace>(\<lambda>s. P (ko_wp_at' P' p s)) and K (\<forall>pde_x :: pde. P' (injectKO pde_x) = v)\<rbrace>
     copyGlobalMappings pd
   \<lbrace>\<lambda>rv s. P (ko_wp_at' P' p s)\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: copyGlobalMappings_def storePDE_def)
  apply (wp mapM_x_wp' setObject_ko_wp_at)
      apply simp
     apply (simp add: objBits_simps archObjSize_def)
    apply (simp add: pdeBits_def)
   apply (simp cong: if_cong split del: if_split)
   apply (wp getObject_inv loadObject_default_inv | simp split del: if_split)+
   apply (clarsimp simp: obj_at'_def ko_wp_at'_def projectKOs)
  apply (wp | simp)+
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

lemma createNewCaps_ko_wp_atQ':
  "\<lbrace>(\<lambda>s. P (ko_wp_at' P' p s)
       \<and> range_cover ptr sz (APIType_capBits ty us) n \<and> n \<noteq> 0
       \<and> pspace_aligned' s \<and> pspace_distinct' s
       \<and> pspace_no_overlap' ptr sz s)
       and K (\<forall>pde_x :: pde. P' (injectKO pde_x)
                   \<longrightarrow> (\<forall>pde_y :: pde. P' (injectKO pde_y)))
       and K (\<forall>d (tcb_x :: tcb). \<not>tcbQueued tcb_x \<and> tcbState tcb_x = Inactive
                   \<longrightarrow> P' (injectKO (tcb_x \<lparr> tcbDomain := d \<rparr>)) = P' (injectKO tcb_x))
       and (\<lambda>s. (\<forall>v. makeObjectKO dev (ksCurDomain s) (Inr ty) = Some v \<longrightarrow> P' v \<longrightarrow> P True))\<rbrace>
     createNewCaps ty ptr n us dev
   \<lbrace>\<lambda>rv s. P (ko_wp_at' P' p s)\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp: createNewCaps_def ARM_H.toAPIType_def
             split del: if_split)
  apply (cases ty, simp_all add: Arch_createNewCaps_def
                      split del: if_split)
        apply (rename_tac apiobject_type)
        apply (case_tac apiobject_type, simp_all split del: if_split)[1]
            apply (rule hoare_pre, wp, simp)
           apply ((wp mapM_x_threadSet_createNewCaps_futz
                     mapM_x_wp'
                     createObjects_obj_at
                     createObjects_ko_wp_at2 createObjects_makeObject_not_tcbQueued
                     copyGlobalMappings_ko_wp_at[where v="\<forall>pde :: pde. P' (injectKO pde)"]
                   | simp add: makeObjectKO_def objBitsKO_def archObjSize_def APIType_capBits_def
                               objBits_def pageBits_def pdBits_def ptBits_def curDomain_def
                               pteBits_def pdeBits_def
                          split del: if_split
                   | split if_split_asm[where Q=dev]
                   | intro conjI impI | fastforce)+)
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
  apply (rule hoare_post_imp[where Q'="\<lambda>rv s. \<exists>t. ksCurThread s = t \<and> tcb_at' t s"])
   apply (simp add: cur_tcb'_def)
  apply (wp hoare_vcg_ex_lift createNewCaps_obj_at')
  apply (clarsimp simp: pspace_no_overlap'_def cur_tcb'_def valid_pspace'_def)
  apply auto
  done

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

crunch copyGlobalMappings, createObjects, createNewCaps
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
  apply (clarsimp simp: createNewCaps_def ARM_H.toAPIType_def
             split del: if_split)
  apply (cases ty, simp_all add: Arch_createNewCaps_def
                      split del: if_split)
        apply (rename_tac apiobject_type)
        apply (case_tac apiobject_type, simp_all split del: if_split)[1]
            apply wpsimp
           apply (wpsimp wp: mapM_x_wp' createObjects_idle'
                  | simp add: projectKO_opt_tcb projectKO_opt_cte
                              makeObject_cte makeObject_tcb archObjSize_def
                              tcb_cte_cases_def objBitsKO_def APIType_capBits_def
                              ptBits_def pdBits_def pageBits_def objBits_def
                              createObjects_def pteBits_def pdeBits_def tcb_cte_cases_neqs
                  | intro conjI impI
                  | clarsimp simp: curDomain_def)+
  done

lemma createNewCaps_global_refs':
  "\<lbrace>\<lambda>s. range_cover ptr sz (APIType_capBits ty us) n \<and> n \<noteq> 0
       \<and> pspace_aligned' s \<and> pspace_distinct' s
       \<and> pspace_no_overlap' ptr sz s \<and> valid_global_refs' s
       \<and> 0 < gsMaxObjectSize s\<rbrace>
     createNewCaps ty ptr n us d
   \<lbrace>\<lambda>rv. valid_global_refs'\<rbrace>"
  apply (simp add: valid_global_refs'_def valid_cap_sizes'_def valid_refs'_def)
  apply (rule_tac Q'="\<lambda>rv s. \<forall>ptr. \<not> cte_wp_at' (\<lambda>cte. (kernel_data_refs \<inter> capRange (cteCap cte) \<noteq> {}
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

lemma valid_irq_node_lift_asm:
  assumes x: "\<And>P. \<lbrace>\<lambda>s. P (irq_node' s)\<rbrace> f \<lbrace>\<lambda>rv s. P (irq_node' s)\<rbrace>"
  assumes y: "\<And>p. \<lbrace>real_cte_at' p and Q\<rbrace> f \<lbrace>\<lambda>rv. real_cte_at' p\<rbrace>"
  shows      "\<lbrace>\<lambda>s. valid_irq_node' (irq_node' s) s \<and> Q s\<rbrace> f \<lbrace>\<lambda>rv s. valid_irq_node' (irq_node' s) s\<rbrace>"
  apply (simp add: valid_irq_node'_def)
  apply (rule hoare_pre)
   apply (rule hoare_use_eq_irq_node' [OF x])
   apply (wp hoare_vcg_all_lift y)
  apply simp
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
  apply (clarsimp simp: projectKO_opt_pde o_def valid_pde_mapping'_def
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

lemma getObject_valid_pde_mapping':
  "\<lbrace>valid_pde_mappings' and K (p && mask pdBits = p')\<rbrace> getObject p \<lbrace>\<lambda>pde s. valid_pde_mapping' p' pde\<rbrace>"
  apply (wp getPDE_wp)
  apply (clarsimp simp: valid_pde_mappings'_def)
  done

lemma copyGlobalMappings_pde_mappings':
  "\<lbrace>valid_pde_mappings' and (\<lambda>s. is_aligned (armKSGlobalPD (ksArchState s)) pdBits)
        and K (is_aligned pd pdBits)\<rbrace> copyGlobalMappings pd \<lbrace>\<lambda>rv. valid_pde_mappings'\<rbrace>"
  apply (simp add: copyGlobalMappings_def objBits_simps archObjSize_def)
  apply wp
   apply (rule_tac P="is_aligned globalPD pdBits \<and> is_aligned pd pdBits"
                in hoare_gen_asm)
   apply (rule mapM_x_wp[where S="{x. x < 2 ^ (pdBits - 2)}"])
    apply (wp getObject_valid_pde_mapping' | simp)+
     apply clarsimp
     apply (drule(1) is_aligned_add_helper[OF _ shiftl_less_t2n])
      apply (simp add: pdBits_def pageBits_def pdeBits_def)
     apply (drule(1) is_aligned_add_helper[OF _ shiftl_less_t2n])
      apply (simp add: pdBits_def pageBits_def pdeBits_def)
     apply (simp add: pdeBits_def)
    apply simp
   apply (clarsimp simp: pdBits_def pdeBits_def le_less_trans)
  apply wp
  apply clarsimp
  done

lemma copyGlobalMappings_valid_arch_state'[wp]:
  "\<lbrace>valid_arch_state' and K (is_aligned pd pdBits) \<rbrace> copyGlobalMappings pd \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  by (wp valid_arch_state_lift'_valid_pde_mappings' copyGlobalMappings_pde_mappings')
     (clarsimp simp: valid_arch_state'_def page_directory_at'_def)

lemma mapM_x_copyGlobalMappings_pde_mappings':
  "\<lbrace>valid_pde_mappings' and (\<lambda>s. is_aligned (armKSGlobalPD (ksArchState s)) pdBits)
        and K (\<forall>x \<in> set xs. is_aligned x pdBits)\<rbrace>
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
   apply (wp mapM_x_copyGlobalMappings_pde_mappings'
             mapM_x_wp'[where f="\<lambda>r. doMachineOp (m r)" for m]
         | wpc
         | simp split del: if_split)+
    apply (rule_tac P="range_cover ptr sz (APIType_capBits ty us) n \<and> n\<noteq> 0" in hoare_gen_asm)
    apply (rule hoare_strengthen_post)
     apply (rule createObjects_aligned, simp+)
        apply (simp add: objBits_simps pdBits_def pageBits_def archObjSize_def APIType_capBits_def
                         range_cover_def pdeBits_def)
       apply (rule range_cover.range_cover_n_less[where 'a=32, folded word_bits_def],fastforce+)
     apply (simp add: objBits_simps pdBits_def pageBits_def archObjSize_def APIType_capBits_def range_cover_def word_bits_def
                      pteBits_def pdeBits_def)+
   apply (wp mapM_x_wp[OF _ subset_refl] | wpc | simp add: curDomain_def)+
  apply (clarsimp simp: projectKOs)
  apply (simp add: objBits_simps pdBits_def pageBits_def archObjSize_def APIType_capBits_def)
  apply (case_tac ty; simp)
        apply (rename_tac apiobject_type)
        apply (case_tac apiobject_type)
  apply (auto simp: ARM_H.toAPIType_def objBits_simps ptBits_def pageBits_def pteBits_def pdeBits_def
                    makeObject_pde valid_arch_state'_def pdBits_def page_directory_at'_def)
  done

lemma createNewCaps_valid_arch_state:
  "\<lbrace>(\<lambda>s. valid_arch_state' s \<and> valid_pspace' s \<and> pspace_no_overlap' ptr sz s
        \<and> (tp = APIObjectType ArchTypes_H.CapTableObject \<longrightarrow> us > 0))
       and K (range_cover ptr sz (APIType_capBits ty us) n \<and> n \<noteq> 0)\<rbrace>
     createNewCaps ty ptr n us d
   \<lbrace>\<lambda>rv. valid_arch_state'\<rbrace>"
  unfolding valid_arch_state'_def
  apply (simp add: valid_arch_state'_def
                   valid_asid_table'_def
                   valid_global_pts'_def
                   page_table_at'_def
                   page_directory_at'_def
                   typ_at_to_obj_at_arches)
  apply (rule hoare_pre)
   apply (rule hoare_use_eq [where f=ksArchState, OF createNewCaps_ksArch])
   apply (wp hoare_vcg_const_Ball_lift
             hoare_vcg_prop
             createNewCaps_obj_at''
             createNewCaps_ko_wp_at'
             hoare_vcg_all_lift
             hoare_vcg_const_imp_lift)
  apply (auto simp add: valid_arch_state'_def
                   valid_asid_table'_def
                   valid_global_pts'_def
                   page_table_at'_def
                   page_directory_at'_def
                   typ_at_to_obj_at_arches comp_def)
  done

lemma createObjects'_irq_states' [wp]:
  "\<lbrace>valid_irq_states'\<rbrace> createObjects' a b c d \<lbrace>\<lambda>_. valid_irq_states'\<rbrace>"
  apply (simp add: createObjects'_def split_def)
  apply (wp unless_wp|wpc|simp add: alignError_def)+
  apply fastforce
  done

crunch createNewCaps
  for irq_states'[wp]: valid_irq_states'
  (wp: crunch_wps no_irq no_irq_clearMemory simp: crunch_simps unless_def)

crunch createObjects
  for ksMachine[wp]: "\<lambda>s. P (ksMachineState s)"
  (simp: crunch_simps unless_def)
crunch createObjects
  for cur_domain[wp]: "\<lambda>s. P (ksCurDomain s)"
  (simp: unless_def)

lemma createObjects_valid_bitmaps:
  "createObjects' ptr n val gbits \<lbrace>valid_bitmaps\<rbrace>"
  apply (clarsimp simp: createObjects'_def alignError_def split_def)
  apply (wp case_option_wp[where P="\<lambda>_. P" and P'=P for P, simplified] assert_inv
         | clarsimp simp del: fun_upd_apply)+
  apply (clarsimp simp: valid_bitmaps_def valid_bitmapQ_def bitmapQ_def bitmapQ_no_L2_orphans_def
                        bitmapQ_no_L1_orphans_def)
  done

lemma valid_bitmaps_gsCNodes_update[simp]:
  "valid_bitmaps (gsCNodes_update f s) = valid_bitmaps s"
  by (simp add: valid_bitmaps_def bitmapQ_defs)

lemma valid_bitmaps_gsUserPages_update[simp]:
  "valid_bitmaps (gsUserPages_update f s) = valid_bitmaps s"
  by (simp add: valid_bitmaps_def bitmapQ_defs)

crunch curDomain, copyGlobalMappings
  for valid_bitmaps[wp]: valid_bitmaps
  and sched_pointers[wp]: "\<lambda>s. P (tcbSchedNexts_of s) (tcbSchedPrevs_of s)"
  and valid_sched_pointers[wp]: valid_sched_pointers
  (wp: crunch_wps valid_bitmaps_lift)

lemma createNewCaps_valid_bitmaps:
  "\<lbrace>\<lambda>s. valid_pspace' s \<and> pspace_no_overlap' ptr sz s \<and> valid_bitmaps s\<rbrace>
   createNewCaps ty ptr n us dev
   \<lbrace>\<lambda>_. valid_bitmaps\<rbrace>"
  unfolding createNewCaps_def
  apply (clarsimp simp: ARM_H.toAPIType_def
             split del: if_split)
  apply (cases ty; simp add: createNewCaps_def Arch_createNewCaps_def
                        split del: if_split)
        apply (rename_tac apiobject_type)
        apply (case_tac apiobject_type; simp split del: if_split)
            apply (rule hoare_pre, wp, simp)
           apply (wpsimp wp: createObjects_valid_bitmaps)
           by (wpsimp wp: createObjects_valid_bitmaps[simplified o_def] mapM_x_wp
               | simp add: makeObject_tcb objBits_def createObjects_def
               | intro conjI impI)+

lemma createObjects_sched_queues:
  "\<lbrace>\<lambda>s. n \<noteq> 0
        \<and> range_cover ptr sz (objBitsKO val + gbits) n
        \<and> P (tcbSchedNexts_of s) (tcbSchedPrevs_of s)
        \<and> (case val of KOTCB tcb \<Rightarrow> tcbSchedNext tcb = None \<and> tcbSchedPrev tcb = None
                     | _ \<Rightarrow> True)
        \<and> pspace_aligned' s \<and> pspace_distinct' s
        \<and> pspace_no_overlap' ptr sz s\<rbrace>
   createObjects' ptr n val gbits
   \<lbrace>\<lambda>_ s. P (tcbSchedNexts_of s) (tcbSchedPrevs_of s)\<rbrace>"
  (is "\<lbrace> \<lambda>s. _ \<and> _ \<and> ?Pre s \<rbrace> _ \<lbrace>\<lambda>_. _\<rbrace>")
proof (rule hoare_grab_asm)+
  assume not_0: "\<not> n = 0"
    and cover: "range_cover ptr sz ((objBitsKO val) + gbits) n"
  then show
    "\<lbrace>\<lambda>s. ?Pre s\<rbrace> createObjects' ptr n val gbits \<lbrace>\<lambda>_ s. P (tcbSchedNexts_of s) (tcbSchedPrevs_of s)\<rbrace>"
  proof -
    have shiftr_not_zero:" 1 \<le> ((of_nat n)::machine_word) << gbits"
      using range_cover_not_zero_shift[OF not_0 cover,where gbits = gbits]
      by (simp add:word_le_sub1)
    show ?thesis
      apply (clarsimp simp: createObjects'_def unless_def alignError_def split_def)
      apply (wp | clarsimp simp del: fun_upd_apply)+
      apply (clarsimp simp: shiftL_nat data_map_insert_def[symmetric]
                            new_cap_addrs_fold'[OF shiftr_not_zero]
                  simp del: data_map_insert_def)
      using range_cover.unat_of_nat_n_shift[OF cover, where gbits=gbits, simplified]
      apply (clarsimp simp: foldr_upd_app_if)
      apply (rule_tac a="tcbSchedNexts_of s" and b="tcbSchedPrevs_of s"
                   in rsubst2[rotated, OF sym sym, where P=P])
        apply (rule ext)
        apply (clarsimp simp: opt_map_def)
        apply (frule (3) retype_ksPSpace_None[simplified mult.commute])
          apply (fastforce intro: cover)
         apply fastforce
        apply (clarsimp simp: projectKOs split: kernel_object.splits option.splits)
       apply (rule ext)
       apply (clarsimp simp: opt_map_def)
       apply (frule (3) retype_ksPSpace_None[simplified mult.commute])
         apply (fastforce intro: cover)
        apply fastforce
       apply (clarsimp simp: projectKOs split: kernel_object.splits option.splits)
      apply simp
      done
  qed
qed

crunch doMachineOp
  for sched_projs[wp]: "\<lambda>s. P (tcbSchedNexts_of s) (tcbSchedPrevs_of s)"

lemma createNewCaps_sched_queues:
  assumes cover: "range_cover ptr sz (APIType_capBits ty us) n"
  assumes not_0: "n \<noteq> 0"
  shows
    "\<lbrace>\<lambda>s. valid_pspace' s \<and> pspace_no_overlap' ptr sz s
          \<and> P (tcbSchedNexts_of s) (tcbSchedPrevs_of s)\<rbrace>
     createNewCaps ty ptr n us dev
     \<lbrace>\<lambda>_ s. P (tcbSchedNexts_of s) (tcbSchedPrevs_of s)\<rbrace>"
  unfolding createNewCaps_def
  apply (clarsimp simp: ARM_H.toAPIType_def split del: if_split)
  apply (cases ty; simp add: createNewCaps_def Arch_createNewCaps_def
                        split del: if_split)
        apply (rename_tac apiobject_type)
        apply (case_tac apiobject_type; simp split del: if_split)
            apply (wp, simp)
           apply (insert cover not_0)
           apply (wpsimp wp: mapM_x_wp' createObjects_sched_queues
                       simp: curDomain_def createObjects_def)
           by (wpsimp wp: mapM_x_wp' createObjects_sched_queues[simplified o_def]
                          threadSet_sched_pointers
               | simp add: objBitsKO_def APIType_capBits_def valid_pspace'_def makeObject_tcb
                           objBits_def pageBits_def archObjSize_def createObjects_def
                           pt_bits_def ptBits_def pteBits_def pdBits_def pdeBits_def word_size_bits_def
               | intro conjI impI)+

lemma createObjects_valid_sched_pointers:
  "\<lbrace>\<lambda>s. valid_sched_pointers s
        \<and> (case val of KOTCB tcb \<Rightarrow> tcbSchedNext tcb = None \<and> tcbSchedPrev tcb = None
                     | _ \<Rightarrow> True)\<rbrace>
   createObjects' ptr n val gbits
   \<lbrace>\<lambda>_. valid_sched_pointers\<rbrace>"
  apply (clarsimp simp: createObjects'_def unless_def alignError_def split_def)
  apply (wp case_option_wp[where P="\<lambda>_. P" and P'=P for P, simplified] assert_inv
         | clarsimp simp del: fun_upd_apply)+
  apply (clarsimp simp: valid_sched_pointers_def foldr_upd_app_if opt_pred_def opt_map_def comp_def)
  apply (cases "tcb_of' val"; clarsimp simp: projectKOs)
  done

lemma createNewCaps_valid_sched_pointers:
  "\<lbrace>\<lambda>s. valid_pspace' s \<and> pspace_no_overlap' ptr sz s \<and> valid_sched_pointers s\<rbrace>
   createNewCaps ty ptr n us dev
   \<lbrace>\<lambda>_. valid_sched_pointers\<rbrace>"
  unfolding createNewCaps_def
  apply (clarsimp simp: ARM_H.toAPIType_def
             split del: if_split)
  apply (cases ty; simp add: createNewCaps_def Arch_createNewCaps_def
                        split del: if_split)
        apply (rename_tac apiobject_type)
        apply (case_tac apiobject_type; simp split del: if_split)
            apply (rule hoare_pre, wp, simp)
           apply (wpsimp wp: createObjects_valid_sched_pointers)
           by (wpsimp wp: createObjects_valid_sched_pointers[simplified o_def] mapM_x_wp
                          threadSet_valid_sched_pointers
               | simp add: makeObject_tcb objBits_def createObjects_def
               | intro conjI impI)+

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
  shows
  "\<lbrace>\<lambda>s. pspace_no_overlap' ptr sz s \<and> valid_pspace' s
     \<and> caps_no_overlap'' ptr sz s \<and> ptr \<noteq> 0 \<and> caps_overlap_reserved' {ptr..ptr + of_nat n * 2^(APIType_capBits ty us) - 1} s
     \<and> ksCurDomain s \<le> maxDomain\<rbrace>
   createNewCaps ty ptr n us dev
   \<lbrace>\<lambda>r. valid_pspace'\<rbrace>"
  unfolding createNewCaps_def Arch_createNewCaps_def
  using valid_obj_makeObject_rules
  apply (clarsimp simp: ARM_H.toAPIType_def
             split del: if_split cong: option.case_cong)
  apply (cases ty, simp_all split del: if_split)
        apply (rename_tac apiobject_type)
        apply (case_tac apiobject_type, simp_all split del: if_split)
            apply (rule hoare_pre, wp, clarsimp)
           apply (insert cover)
           (* for TCBObject, we need to know a bit more about tcbDomain *)
           apply (simp add: curDomain_def)
           apply (rule bind_wp[OF _ gets_sp])
           apply (clarsimp simp: createObjects_def)
           apply (rule hoare_assume_pre)
           by (wp createObjects_valid_pspace_untyped' [OF _ _ not_0 , where ty="Inr ty" and sz = sz]
                  mapM_x_threadSet_valid_pspace mapM_x_wp'
               | simp add: makeObjectKO_def APIType_capBits_def
                           objBits_simps pageBits_def pdBits_def ptBits_def not_0
                           createObjects_def curDomain_def
                           pteBits_def pdeBits_def
               | intro conjI impI
               | simp add: power_add field_simps)+

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
                          pteBits_def pdeBits_def
               split del: if_split
         | assumption)+
  apply (case_tac ty)
   apply (auto simp: APIType_capBits_def archObjSize_def objBits_simps pageBits_def ptBits_def
                     pdBits_def ARM_H.toAPIType_def object_type.splits pteBits_def pdeBits_def)
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
  apply (subgoal_tac " \<forall>x \<in> set (new_cap_addrs (unat (of_nat n << gbits)) ptr val).
                         mask_range x (objBitsKO val) \<subseteq> {ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1}")
   apply blast

  apply (rule ballI)
  apply (rule new_range_subset')
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

crunch copyGlobalMappings
  for pspace_domain_valid[wp]: "pspace_domain_valid"
  (wp: crunch_wps)

crunch doMachineOp
  for pspace_domain_valid[wp]: pspace_domain_valid

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
  apply (simp add: ARM_H.toAPIType_def
            split: object_type.splits)
  apply (auto simp: objBits_simps APIType_capBits_def pageBits_def
                    pteBits_def pdeBits_def
                    archObjSize_def ptBits_def pdBits_def)
  done

crunch createNewCaps
  for cur_domain[wp]: "\<lambda>s. P (ksCurDomain s)"
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
    apply (wp hoare_weak_lift_imp e' hoare_vcg_disj_lift)
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

crunch copyGlobalMappings
  for ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
  (wp: setObject_ksPSpace_only updateObject_default_inv mapM_x_wp')

crunch createNewCaps
  for ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
  (wp: mapM_x_wp' simp: crunch_simps)

crunch createNewCaps
  for ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  (wp: mapM_x_wp' simp: crunch_simps)

lemma createObjects_null_filter':
  "\<lbrace>\<lambda>s. P (null_filter' (ctes_of s)) \<and> makeObjectKO dev d ty = Some val \<and>
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
                              APIType_capBits_def objBits_def pageBits_def
                              archObjSize_def ptBits_def pdBits_def curDomain_def
                              objBits_if_dev
                       split del: if_split
                    | wp createObjects_null_filter'[where ty = "Inr ty" and sz = sz and dev=dev]
                         copyGlobalMappings_ctes_of threadSet_ctes_of mapM_x_wp'
                    | simp add: objBits_simps pteBits_def pdeBits_def
                    | fastforce)+
  done

crunch createNewCaps
  for gsUntypedZeroRanges[wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"
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
    apply (rule_tac P'="\<lambda>s. ksSchedulerAction s = ResumeCurrentThread
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
               createNewCaps_iflive' [OF cover not_0 ]
               irqs_masked_lift
               createNewCaps_ifunsafe'
               createNewCaps_cur [OF cover not_0]
               createNewCaps_global_refs'
               createNewCaps_valid_arch_state
               valid_irq_node_lift_asm [unfolded pred_conj_def, OF _ createNewCaps_obj_at']
               createNewCaps_irq_handlers' createNewCaps_vms
               createNewCaps_pred_tcb_at' cnc_ct_not_inQ
               createNewCaps_ct_idle_or_in_cur_domain'
               createNewCaps_sch_act_wf
               createNewCaps_urz[where sz=sz]
               createNewCaps_sched_queues[OF cover not_0]
               createNewCaps_valid_sched_pointers
               createNewCaps_valid_bitmaps
           | simp)+
  using not_0
  apply (clarsimp simp: valid_pspace'_def)
  using cover
  apply (intro conjI)
   apply simp_all
  done
qed

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
  apply (rule_tac Q'="\<lambda>rv s. \<forall>ptr. \<not> cte_wp_at' (\<lambda>cte. (kernel_data_refs \<inter> capRange (cteCap cte) \<noteq> {}
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
        pspace_no_overlap' ptr sz s \<and> range_cover ptr sz (objBitsKO val + gbits) n \<and> n \<noteq> 0 \<and>
        (\<forall>pde. projectKO_opt val = Some pde \<longrightarrow> pde = InvalidPDE) \<rbrace>
      createObjects ptr n val gbits
   \<lbrace>\<lambda>rv s. valid_arch_state' s\<rbrace>"
  apply (simp add: valid_arch_state'_def valid_asid_table'_def
                   page_directory_at'_def valid_global_pts'_def
                   page_table_at'_def)
  apply (rule hoare_pre)
   apply (rule hoare_use_eq [where f=ksArchState, OF createObjects_ksArch])
    apply (simp add: createObjects_def)
    apply (wp createObjects'_typ_at hoare_vcg_all_lift hoare_vcg_const_imp_lift
              hoare_vcg_const_Ball_lift)
  apply (simp add: o_def)
  apply auto
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
  apply (rule hoare_post_imp[where Q'="\<lambda>rv s. \<exists>t. ksCurThread s = t \<and> tcb_at' t s"])
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

crunch createObjects
  for gsUntypedZeroRanges[wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"
  (simp: unless_def)

lemma createObjects_untyped_ranges_zero':
  assumes moKO: "makeObjectKO dev d ty = Some val"
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
   apply (simp add: makeObject_tcb tcb_cte_cases_def tcb_cte_cases_neqs makeObject_cte
                    untypedZeroRange_def)
  apply (simp add: makeObject_cte untypedZeroRange_def)
  done

(* FIXME arch-split: non-hyp arches only *)
lemma sym_refs_empty[simp]:
  "sym_refs (\<lambda>p. {}) = True"
  unfolding sym_refs_def
  by simp

lemma createObjects_no_cte_invs:
  assumes moKO: "makeObjectKO dev d ty = Some val"
  assumes no_cte: "\<And>c. projectKO_opt val \<noteq> Some (c::cte)"
  assumes no_tcb: "\<And>t. projectKO_opt val \<noteq> Some (t::tcb)"
  and     mdom: "ty = Inr (APIObjectType ArchTypes_H.apiobject_type.TCBObject) \<longrightarrow> d \<le> maxDomain"
  shows
  "\<lbrace>\<lambda>s. range_cover ptr sz ((objBitsKO val) + gbits) n \<and> n \<noteq> 0 \<and> invs' s \<and> ct_active' s
        \<and> pspace_no_overlap' ptr sz s \<and> ptr \<noteq> 0
        \<and> {ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1} \<inter> kernel_data_refs = {}
        \<and> caps_overlap_reserved' {ptr..ptr + of_nat (n * 2 ^ gbits * 2 ^ objBitsKO val) - 1} s
        \<and> caps_no_overlap'' ptr sz s \<and>
       refs_of' val = {} \<and> \<not> live' val
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
    apply (rule_tac P'="\<lambda>s. (ksSchedulerAction s = ResumeCurrentThread) \<longrightarrow>
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
   apply (wp createObjects_sch)
   apply (rule hoare_vcg_conj_lift)
    apply (simp add: createObjects_def)
    apply (wp createObjects_state_refs_of'')
   apply (rule hoare_vcg_conj_lift)
    apply (simp add: createObjects_def)
    apply (wp createObjects_iflive')
   apply (wp createObjects_no_cte_ifunsafe' irqs_masked_lift
             createObjects_idle' createObjects_no_cte_valid_global
             createObjects_valid_arch createObjects_irq_state
             createObjects_no_cte_irq_handlers createObjects_cur'
             assms | simp add: objBits_def)+
  apply (rule hoare_vcg_conj_lift)
   apply (simp add: createObjects_def)
   apply (wp createObjects_idle')
   apply (wp createObjects_no_cte_ifunsafe' irqs_masked_lift
             createObjects_idle' createObjects_no_cte_valid_global
             createObjects_valid_arch createObjects_irq_state
             createObjects_no_cte_irq_handlers createObjects_cur'
             assms
             createObjects_pspace_domain_valid co_ct_not_inQ
             createObjects_ct_idle_or_in_cur_domain'
             createObjects_untyped_ranges_zero'[OF moKO]
         | simp)+
  apply (rule hoare_vcg_conj_lift)
   apply (simp add: createObjects_def)
   apply (wpsimp wp: createObjects_sched_queues)
  apply (rule hoare_vcg_conj_lift)
   apply (simp add: createObjects_def)
   apply (wpsimp wp: createObjects_valid_sched_pointers)
  apply (rule hoare_vcg_conj_lift)
   apply (simp add: createObjects_def)
   apply (wpsimp wp: createObjects_valid_bitmaps)
   apply (wp createObjects_no_cte_ifunsafe' irqs_masked_lift
             createObjects_idle' createObjects_no_cte_valid_global
             createObjects_valid_arch createObjects_irq_state
             createObjects_no_cte_irq_handlers createObjects_cur'
             assms
             createObjects_pspace_domain_valid co_ct_not_inQ
             createObjects_ct_idle_or_in_cur_domain'
             createObjects_untyped_ranges_zero'[OF moKO]
         | simp)+
  apply clarsimp
  apply ((intro conjI; assumption?); simp add: valid_pspace'_def objBits_def projectKOs)
     apply (fastforce simp add: no_cte no_tcb split_def split: option.splits)
    apply (fastforce simp: invs'_def no_tcb valid_state'_def no_cte
               split: option.splits kernel_object.splits)
   apply (clarsimp simp: live'_def split: kernel_object.splits)
  apply (clarsimp simp: live'_def split: kernel_object.splits)
  done
qed

lemma corres_retype_update_gsI:
  assumes not_zero: "n \<noteq> 0"
  and      aligned: "is_aligned ptr (objBitsKO ko + gbits)"
  and obj_bits_api: "obj_bits_api (APIType_map2 ty) us = objBitsKO ko + gbits"
  and        check: "sz < obj_bits_api (APIType_map2 ty) us \<longleftrightarrow> sz < objBitsKO ko + gbits"
  and          usv: "APIType_map2 ty = Structures_A.CapTableObject \<Longrightarrow> 0 < us"
  and           ko: "makeObjectKO dev d ty = Some ko"
  and          orr: "obj_bits_api (APIType_map2 ty) us \<le> sz \<Longrightarrow>
                     obj_relation_retype (default_object (APIType_map2 ty) dev us d) ko"
  and        cover: "range_cover ptr sz (obj_bits_api (APIType_map2 ty) us) n"
  and            f: "f = update_gs (APIType_map2 ty) us"
  shows "corres (\<lambda>rv rv'. rv' = g rv)
         (\<lambda>s. valid_pspace s \<and> pspace_no_overlap_range_cover ptr sz s
            \<and> valid_mdb s \<and> valid_list s)
         (\<lambda>s. pspace_aligned' s \<and> pspace_distinct' s \<and>
              pspace_no_overlap' ptr sz s \<and>
              (ty = Inr (APIObjectType TCBObject) \<longrightarrow> d = ksCurDomain s))
         (retype_region ptr n us (APIType_map2 ty) dev)
         (do addrs \<leftarrow> createObjects ptr n ko gbits;
             _ \<leftarrow> modify (f (set addrs));
             return (g addrs)
          od)"
  using corres_retype' [OF not_zero aligned obj_bits_api check usv ko orr cover]
  by (simp add: f)

lemma gcd_corres: "corres (=) \<top> \<top> (gets cur_domain) curDomain"
  by (simp add: curDomain_def state_relation_def)

lemma createObjects_tcb_at':
  "\<lbrakk>range_cover ptr sz (objBitsKO (injectKOS (makeObject::tcb))) n; n \<noteq> 0\<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s. pspace_no_overlap' ptr sz s \<and> pspace_aligned' s \<and> pspace_distinct' s\<rbrace>
   createObjects ptr n (KOTCB makeObject) 0
   \<lbrace>\<lambda>ptrs s. \<forall>addr\<in>set ptrs. tcb_at' addr s\<rbrace>"
  apply (rule hoare_strengthen_post[OF createObjects_ko_at_strg[where val = "(makeObject :: tcb)"]])
  apply (auto simp: obj_at'_def project_inject objBitsKO_def objBits_def makeObject_tcb)
  done

lemma data_page_relation_retype:
  "obj_relation_retype (ArchObj (DataPage False pgsz)) KOUserData"
  "obj_relation_retype (ArchObj (DataPage True pgsz)) KOUserDataDevice"
  apply (simp_all add: obj_relation_retype_def
                   objBits_simps archObjSize_def
                   pbfs_atleast_pageBits)
   apply (clarsimp simp: image_def)+
  done

lemma regroup_createObjects_dmo_userPages:
  "(do
      addrs <- createObjects y n ko sz;
      _ <- modify (\<lambda>ks. ks\<lparr>gsUserPages := g ks addrs\<rparr>);
      _ <- when P (mapM_x (\<lambda>addr. doMachineOp (m addr)) addrs);
      return (f addrs)
    od) = (do
      (addrs, faddrs) <- (do
        addrs <- createObjects y n ko sz;
        _ <- modify (\<lambda>ks. ks\<lparr>gsUserPages := g ks addrs\<rparr>);
        return (addrs, f addrs)
       od);
      _ <- when P (mapM_x (\<lambda>addr. doMachineOp (m addr)) addrs);
      return faddrs
    od)"
  by (simp add: bind_assoc)

lemma corres_retype_region_createNewCaps:
  "corres ((\<lambda>r r'. length r = length r' \<and> list_all2 cap_relation r r')
               \<circ> map (\<lambda>ref. default_cap (APIType_map2 (Inr ty)) ref us dev))
            (\<lambda>s. valid_pspace s \<and> valid_mdb s \<and> valid_list s \<and> valid_arch_state s
                   \<and> caps_no_overlap y sz s \<and> pspace_no_overlap_range_cover y sz s
                   \<and> caps_overlap_reserved {y..y + of_nat n * 2 ^ (obj_bits_api (APIType_map2 (Inr ty)) us) - 1} s
                   \<and> (\<exists>slot. cte_wp_at (\<lambda>c. up_aligned_area y sz \<subseteq> cap_range c \<and> cap_is_device c = dev) slot s)
                   \<and> (APIType_map2 (Inr ty) = Structures_A.CapTableObject \<longrightarrow> 0 < us))
            (\<lambda>s. pspace_aligned' s \<and> pspace_distinct' s \<and> pspace_no_overlap' y sz s
                  \<and> valid_pspace' s \<and> valid_arch_state' s
                  \<and> range_cover y sz (obj_bits_api (APIType_map2 (Inr ty)) us) n \<and> n\<noteq> 0)
            (do x \<leftarrow> retype_region y n us (APIType_map2 (Inr ty)) dev :: obj_ref list det_ext_monad;
                init_arch_objects (APIType_map2 (Inr ty)) dev y n us x;
                return x od)
            (createNewCaps ty y n us dev)"
  apply (rule_tac F="range_cover y sz (obj_bits_api (APIType_map2 (Inr ty)) us) n
                      \<and> n \<noteq> 0 \<and> (APIType_map2 (Inr ty) = Structures_A.CapTableObject \<longrightarrow> 0 < us)"
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
           \<comment> \<open>TCB\<close>
           apply (simp_all add: curDomain_def split del: if_split)
           apply (rule corres_underlying_gets_pre_rhs[rotated])
            apply (rule gets_sp)
           apply (rule corres_guard_imp)
             apply (rule corres_bind_return)
             apply (rule corres_split_eqr)
                apply (rule corres_retype[where 'a = tcb],
                       simp_all add: obj_bits_api_def objBits_simps' pageBits_def
                                     APIType_map2_def makeObjectKO_def)[1]
                 apply (fastforce simp: range_cover_def)
                apply (simp add: tcb_relation_retype)
               apply (rule corres_returnTT, simp)
               apply (clarsimp simp: list_all2_same list_all2_map1 list_all2_map2
                                     objBits_simps APIType_map2_def)
              apply ((wp | simp add: APIType_map2_def)+)[1]
             apply ((wp createObjects_tcb_at'[where sz=sz] | simp add: APIType_map2_def objBits_simps' obj_bits_api_def)+)[1]
            apply simp
           apply simp
         \<comment> \<open>EP, NTFN\<close>
         apply (simp add: liftM_def[symmetric] split del: if_split)
         apply (rule corres_rel_imp)
          apply (rule corres_guard_imp)
            apply (rule corres_retype[where 'a = endpoint],
                   simp_all add: obj_bits_api_def objBits_simps' pageBits_def
                                 APIType_map2_def makeObjectKO_def
                                 other_objs_default_relation)[1]
            apply ((simp add: range_cover_def APIType_map2_def
                              list_all2_same list_all2_map1 list_all2_map2)+)[4]
        apply (simp add: liftM_def[symmetric] split del: if_split)
        apply (rule corres_rel_imp)
         apply (rule corres_guard_imp)
           apply (rule corres_retype[where 'a = notification],
                  simp_all add: obj_bits_api_def objBits_simps' pageBits_def
                                APIType_map2_def makeObjectKO_def
                                other_objs_default_relation)[1]
           apply ((simp add: range_cover_def APIType_map2_def
                             list_all2_same list_all2_map1 list_all2_map2)+)[4]
        \<comment> \<open>CapTable\<close>
        apply (find_goal \<open>match premises in "_ = ArchTypes_H.apiobject_type.CapTableObject" \<Rightarrow> \<open>-\<close>\<close>)
        apply (subst bind_assoc_return_reverse[of "createObjects y n (KOCTE makeObject) us"])
        apply (subst liftM_def[of "map (\<lambda>addr. capability.CNodeCap addr us 0 0)", symmetric])
        apply simp
        apply (rule corres_rel_imp)
         apply (rule corres_guard_imp)
           apply (rule corres_retype_update_gsI,
                  simp_all add: obj_bits_api_def objBits_simps' pageBits_def
                                APIType_map2_def makeObjectKO_def slot_bits_def
                                field_simps ext)[1]
              apply ((clarsimp simp : range_cover_def APIType_map2_def word_bits_def
                                       list_all2_same list_all2_map1 list_all2_map2
                     | rule captable_relation_retype)+)[5]
       \<comment> \<open>SmallPageObject\<close>
       apply (in_case \<open>SmallPageObject\<close>)
       apply (simp add: corres_liftM2_simp[unfolded liftM_def] split del: if_split)
       apply (simp add: init_arch_objects_def split del: if_split)
       apply (subst regroup_createObjects_dmo_userPages)
       apply (rule corres_guard_imp)
         apply (rule corres_split)
            apply (rule corres_retype_update_gsI,
                   simp_all add: APIType_map2_def makeObjectKO_def
                                 arch_default_cap_def obj_bits_api_def3
                                 default_object_def default_arch_object_def pageBits_def
                                 ext objBits_simps range_cover.aligned,
                   simp_all add: data_page_relation_retype)[1]
           apply (simp add: APIType_map2_def vs_apiobj_size_def
                       flip: when_def split del: if_split cong: if_cong)
           apply (rule corres_split)
              apply corres
              apply (rule corres_mapM_x', clarsimp)
                 apply (corres corres: corres_machine_op)
                apply wp+
              apply (rule refl)
             apply (rule corres_returnTT)
             apply (simp add: APIType_map2_def arch_default_cap_def vm_read_write_def vmrights_map_def
                              list_all2_map1 list_all2_map2 list_all2_same)
            apply ((wpsimp split_del: if_split)+)[6]
       \<comment> \<open>LargePageObject\<close>
      apply (in_case \<open>LargePageObject\<close>)
      apply (simp add: corres_liftM2_simp[unfolded liftM_def] split del: if_split)
      apply (simp add: init_arch_objects_def split del: if_split)
      apply (subst regroup_createObjects_dmo_userPages)
      apply (rule corres_guard_imp)
        apply (rule corres_split)
           apply (rule corres_retype_update_gsI,
                  simp_all add: APIType_map2_def makeObjectKO_def
                                arch_default_cap_def obj_bits_api_def3
                                default_object_def default_arch_object_def pageBits_def
                                ext objBits_simps range_cover.aligned,
                  simp_all add: data_page_relation_retype)[1]
          apply (simp add: APIType_map2_def vs_apiobj_size_def
                      flip: when_def split del: if_split cong: if_cong)
          apply (rule corres_split)
             apply corres
             apply (rule corres_mapM_x', clarsimp)
                apply (corres corres: corres_machine_op)
               apply wp+
             apply (rule refl)
            apply (rule corres_returnTT)
            apply (simp add: APIType_map2_def arch_default_cap_def vm_read_write_def vmrights_map_def
                             list_all2_map1 list_all2_map2 list_all2_same)
           apply ((wpsimp split_del: if_split)+)[6]
     \<comment> \<open>SectionObject\<close>
     apply (in_case \<open>SectionObject\<close>)
     apply (simp add: corres_liftM2_simp[unfolded liftM_def] split del: if_split)
     apply (simp add: init_arch_objects_def split del: if_split)
     apply (subst regroup_createObjects_dmo_userPages)
     apply (rule corres_guard_imp)
       apply (rule corres_split)
          apply (rule corres_retype_update_gsI,
                 simp_all add: APIType_map2_def makeObjectKO_def
                               arch_default_cap_def obj_bits_api_def3
                               default_object_def default_arch_object_def pageBits_def
                               ext objBits_simps range_cover.aligned,
                 simp_all add: data_page_relation_retype)[1]
         apply (simp add: APIType_map2_def vs_apiobj_size_def
                     flip: when_def split del: if_split cong: if_cong)
         apply (rule corres_split)
            apply corres
            apply (rule corres_mapM_x', clarsimp)
               apply (corres corres: corres_machine_op)
              apply wp+
            apply (rule refl)
           apply (rule corres_returnTT)
           apply (simp add: APIType_map2_def arch_default_cap_def vm_read_write_def vmrights_map_def
                            list_all2_map1 list_all2_map2 list_all2_same)
          apply ((wpsimp split_del: if_split)+)[6]
    \<comment> \<open>SuperSectionObject\<close>
    apply (in_case \<open>SuperSectionObject\<close>)
    apply (simp add: corres_liftM2_simp[unfolded liftM_def] split del: if_split)
    apply (simp add: init_arch_objects_def split del: if_split)
    apply (subst regroup_createObjects_dmo_userPages)
    apply (rule corres_guard_imp)
      apply (rule corres_split)
         apply (rule corres_retype_update_gsI,
                simp_all add: APIType_map2_def makeObjectKO_def
                              arch_default_cap_def obj_bits_api_def3
                              default_object_def default_arch_object_def pageBits_def
                              ext objBits_simps range_cover.aligned,
                simp_all add: data_page_relation_retype)[1]
        apply (simp add: APIType_map2_def vs_apiobj_size_def
                    flip: when_def split del: if_split cong: if_cong)
        apply (rule corres_split)
           apply corres
           apply (rule corres_mapM_x', clarsimp)
              apply (corres corres: corres_machine_op)
             apply wp+
           apply (rule refl)
          apply (rule corres_returnTT)
          apply (simp add: APIType_map2_def arch_default_cap_def vm_read_write_def vmrights_map_def
                           list_all2_map1 list_all2_map2 list_all2_same)
         apply ((wpsimp split_del: if_split)+)[6]
   \<comment> \<open>PageTableObject\<close>
   apply (in_case \<open>PageTableObject\<close>)
   apply (simp add: corres_liftM2_simp[unfolded liftM_def])
   apply (simp add: init_arch_objects_def bind_assoc split del: if_split)
   apply (rule corres_guard_imp)
     apply (rule corres_split)
        apply (rule corres_retype[where 'a =pte],
               simp_all add: APIType_map2_def obj_bits_api_def
                             default_arch_object_def objBits_simps
                             archObjSize_def ptBits_def pteBits_def
                             makeObjectKO_def range_cover.aligned)[1]
        apply (rule pagetable_relation_retype)
        apply (clarsimp simp: APIType_map2_def vs_apiobj_size_def
                              pt_bits_def ptBits_def pageBits_def pteBits_def)
        apply (rule corres_split)
           apply (rule corres_mapM_x', clarsimp)
              apply (corres corres: corres_machine_op)
             apply wp+
           apply (rule refl)
          apply (rule corres_returnTT)
          apply corres
          apply (clarsimp simp: list_all2_map1 list_all2_map2 list_all2_same
                                APIType_map2_def arch_default_cap_def)
         apply ((wpsimp split_del: if_split)+)[6]
  \<comment> \<open>PageDirectoryObject\<close>
  apply (in_case \<open>PageDirectoryObject\<close>)
  apply (simp add: bind_assoc)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr)
       apply (rule corres_retype[where ty = "Inr PageDirectoryObject" and 'a = pde],
              simp_all add: APIType_map2_def obj_bits_api_def
                            default_arch_object_def objBits_simps
                            pdBits_def pageBits_def
                            pteBits_def pdeBits_def
                            makeObjectKO_def)[1]
        apply (simp add: range_cover_def)+
       apply (rule pagedirectory_relation_retype)
      apply (rename_tac pds)
      apply (simp add: init_arch_objects_def bind_assoc APIType_map2_def
                       vs_apiobj_size_def pdBits_eq
                  split del: if_split)
         apply (rule corres_split)
         apply (rule_tac P="valid_arch_state and pspace_aligned and
                            (\<lambda>s. \<forall>pd \<in> set pds. typ_at (AArch APageDirectory) pd s)" and
                         P'="valid_arch_state' and (\<lambda>s. \<forall>pd \<in> set pds. page_directory_at' pd s)"
                         in corres_mapM_x')
            apply (clarsimp, rule corres_guard_imp, rule copyGlobalMappings_corres; simp)
           apply (wpsimp wp: hoare_vcg_op_lift simp: page_directory_at'_def)+
        apply (rule corres_split, rule corres_mapM_x', rule corres_machine_op)
              apply (clarsimp cong: corres_weak_cong)
              apply (rule corres_underlying_trivial_dc)
              apply wp+
           apply (rule refl)
          apply (rule corres_returnTT)
          apply (simp add: list_all2_map1 list_all2_map2 list_all2_same arch_default_cap_def)
         apply (wpsimp wp: retype_region_valid_arch retype_region_aligned)+
     apply (rule hoare_post_imp)
      prefer 2
      apply (rule hoare_vcg_conj_lift)
       apply (rule retype_region_obj_at)
       apply (simp add: APIType_map2_def)
      apply (simp add: APIType_map2_def)
      apply (rule retype_region_ret)
     apply (clarsimp simp: retype_addrs_def obj_bits_api_def APIType_map2_def
                           default_arch_object_def default_object_def obj_at_def a_type_def)
    apply (wpsimp wp: createObjects_valid_arch)
     apply (rule hoare_post_imp)
      prefer 2
     apply (rule hoare_vcg_conj_lift)
      apply (rule createObjects_ko_at[where sz = sz and 'a = pde])
        apply (simp add: objBits_simps archObjSize_def pdBits_def
                         pteBits_def pdeBits_def APIType_map2_def
                         obj_bits_api_def default_arch_object_def projectKOs
                         pageBits_def page_directory_at'_def)+
     apply (rule createObjects_aligned)
        apply (simp add: objBits_simps archObjSize_def pdBits_def
                      pageBits_def page_directory_at'_def)+
        apply (simp add: range_cover_def pteBits_def pdeBits_def)
       apply (rule le_less_trans[OF range_cover.range_cover_n_le(2) power_strict_increasing])
         apply simp
        apply (clarsimp simp: range_cover_def word_bits_def)
        apply arith+
     apply (simp add: objBits_simps archObjSize_def pdBits_def
                      pageBits_def page_directory_at'_def)+
     apply (simp add: word_bits_def pteBits_def pdeBits_def)
    apply clarsimp
    apply (drule (1) bspec)+
    apply (simp add: objBits_simps retype_addrs_def obj_bits_api_def pdBits_def pageBits_def
                     ptBits_def APIType_map2_def default_arch_object_def default_object_def
                     archObjSize_def)
    apply (clarsimp simp: objBits_simps archObjSize_def pdBits_def
                          pageBits_def page_directory_at'_def
                          pteBits_def pdeBits_def)
    apply (rename_tac offset)
    apply (drule_tac x = offset in spec)
    apply (clarsimp simp:typ_at'_def obj_at'_real_def)
    apply (erule ko_wp_at'_weakenE)
    apply (clarsimp simp: projectKOs)
   apply (auto simp: objBits_simps retype_addrs_def obj_bits_api_def pdBits_def pageBits_def
                     APIType_map2_def default_arch_object_def default_object_def archObjSize_def
                     pteBits_def pdeBits_def ptBits_def
                     pd_bits_def fromIntegral_def toInteger_nat fromInteger_nat
                     makeObject_pde projectKOs)
  done

end
end
