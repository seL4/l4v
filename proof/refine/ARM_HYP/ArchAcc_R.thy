(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
  Lemmas on arch get/set object etc
*)

theory ArchAcc_R
imports SubMonad_R ArchMove_R
begin

context begin

lemma fun_all: "f = f' \<Longrightarrow> (\<forall>s. f s \<longrightarrow> f' s)"
 by simp

lemma distrib_imp:
  "P \<longrightarrow> Q \<and> Q' \<Longrightarrow> ((P \<longrightarrow> Q) \<Longrightarrow> (P \<longrightarrow> Q') \<Longrightarrow> R) \<Longrightarrow> R"
 by simp

method def_to_elim = (drule meta_eq_to_obj_eq, drule fun_all, elim allE, elim distrib_imp)
method simp_to_elim = (drule fun_all, elim allE impE)

end

context Arch begin global_naming ARM_A (*FIXME: arch_split*)

lemma asid_pool_at_ko:
  "asid_pool_at p s \<Longrightarrow> \<exists>pool. ko_at (ArchObj (ARM_A.ASIDPool pool)) p s"
  apply (clarsimp simp: obj_at_def a_type_def)
  apply (case_tac ko, simp_all split: if_split_asm)
  apply (rename_tac arch_kernel_obj)
  apply (case_tac arch_kernel_obj, auto split: if_split_asm)
  done

declare valid_arch_state_def[@def_to_elim, conjuncts]

lemmas valid_arch_state_elims[rule_format, elim!] = conjuncts

lemmas valid_vspace_obj_elims[rule_format, elim!] =
  valid_vspace_obj.simps[@simp_to_elim, @ \<open>(drule bspec)?\<close>]

end

context begin interpretation Arch . (*FIXME: arch_split*)

(*FIXME move *)

lemma pspace_relation_None:
  "\<lbrakk>pspace_relation p p'; p' ptr = None \<rbrakk> \<Longrightarrow> p ptr = None"
  apply (rule not_Some_eq[THEN iffD1, OF allI, OF notI])
  apply (drule(1) pspace_relation_absD)
   apply (case_tac y; clarsimp simp: cte_map_def of_bl_def well_formed_cnode_n_def split: if_splits)
   subgoal for n
    apply (drule spec[of _ ptr])
    apply (drule spec)
    apply clarsimp
    apply (drule spec[of _ "replicate n False"])
    apply (drule mp[OF _ refl])
     apply (drule mp)
    subgoal premises by (induct n; simp)
    apply clarsimp
    done
  subgoal for x
     apply (cases x; clarsimp)
   apply ((drule spec[of _ 0], fastforce)+)[2]
   apply (drule spec[of _ ptr])
   apply (drule spec)
   apply clarsimp
   apply (drule mp[OF _ refl])
   apply (drule spec[of _ 0])
   subgoal for _ sz by (cases sz; simp add: pageBits_def)
   done
  done

lemma no_0_obj'_abstract:
  "(s, s') \<in> state_relation \<Longrightarrow> no_0_obj' s' \<Longrightarrow> kheap s 0 = None"
  by (auto intro: pspace_relation_None simp add: no_0_obj'_def)

declare if_cong[cong]

lemma corres_gets_asid [corres]:
  "corres (\<lambda>a c. a = c o ucast) \<top> \<top> (gets (arm_asid_table \<circ> arch_state)) (gets (armKSASIDTable \<circ> ksArchState))"
  by (simp add: state_relation_def arch_state_relation_def)

lemmas arm_asid_table_related = corres_gets_asid[simplified, rule_format]

lemma asid_low_bits [simp]:
  "asidLowBits = asid_low_bits"
  by (simp add: asid_low_bits_def asidLowBits_def)

lemma getObject_ASIDPool_corres [@lift_corres_args, corres]:
  "corres (\<lambda>p p'. p = inv ASIDPool p' o ucast)
          (asid_pool_at p) (asid_pool_at' p)
          (get_asid_pool p) (getObject p)"
  apply (simp add: getObject_def get_asid_pool_def get_object_def split_def)
  apply (rule corres_no_failI)
   apply (rule no_fail_pre, wp)
   apply (clarsimp simp: typ_at'_def ko_wp_at'_def)
   apply (case_tac ko; simp)
   apply (rename_tac arch_kernel_object)
   apply (case_tac arch_kernel_object, simp_all)[1]
   apply (clarsimp simp: lookupAround2_known1
                         projectKOs)
   apply (clarsimp simp: obj_at'_def projectKOs objBits_simps
                         archObjSize_def)
   apply (erule (1) ps_clear_lookupAround2)
     apply simp
    apply (erule is_aligned_no_overflow)
   apply simp
   apply (clarsimp simp add: objBits_simps archObjSize_def
                      split: option.split)
  apply (clarsimp simp: in_monad loadObject_default_def projectKOs)
  apply (simp add: bind_assoc exec_gets)
  apply (drule asid_pool_at_ko)
  apply (clarsimp simp: obj_at_def)
  apply (simp add: return_def)
  apply (simp add: in_magnitude_check objBits_simps
                   archObjSize_def pageBits_def)
  apply (clarsimp simp: state_relation_def pspace_relation_def)
  apply (drule bspec, blast)
  apply (clarsimp simp: other_obj_relation_def asid_pool_relation_def)
  done

lemma aligned_distinct_obj_atI':
  "\<lbrakk> ksPSpace s x = Some ko; pspace_aligned' s;
      pspace_distinct' s; ko = injectKO v \<rbrakk>
      \<Longrightarrow> ko_at' v x s"
  apply (simp add: obj_at'_def projectKOs project_inject
                   pspace_distinct'_def pspace_aligned'_def)
  apply (drule bspec, erule domI)+
  apply simp
  done

lemmas aligned_distinct_asid_pool_atI'
    = aligned_distinct_obj_atI'[where 'a=asidpool,
                                simplified, OF _ _ _ refl]

lemma aligned_distinct_relation_asid_pool_atI'[elim]:
  "\<lbrakk> asid_pool_at p s; pspace_relation (kheap s) (ksPSpace s');
     pspace_aligned' s'; pspace_distinct' s' \<rbrakk>
        \<Longrightarrow> asid_pool_at' p s'"
  apply (drule asid_pool_at_ko)
  apply (clarsimp simp add: obj_at_def)
  apply (drule(1) pspace_relation_absD)
  apply (clarsimp simp: other_obj_relation_def)
  apply (simp split: Structures_H.kernel_object.split_asm
                     arch_kernel_object.split_asm)
  apply (drule(2) aligned_distinct_asid_pool_atI')
  apply (clarsimp simp: obj_at'_def typ_at'_def ko_wp_at'_def
                        projectKOs)
  done

lemma getObject_ASIDPool_corres':
  "corres (\<lambda>p p'. p = inv ASIDPool p' o ucast)
          (asid_pool_at p) (pspace_aligned' and pspace_distinct')
          (get_asid_pool p) (getObject p)"
  apply (rule stronger_corres_guard_imp,
         rule getObject_ASIDPool_corres)
   apply auto
  done

crunch inv[wp]: headM P
crunch inv[wp]: tailM P

lemma storePDE_cte_wp_at'[wp]:
  "\<lbrace>\<lambda>s. P (cte_wp_at' P' p s)\<rbrace>
     storePDE ptr val
   \<lbrace>\<lambda>rv s. P (cte_wp_at' P' p s)\<rbrace>"
  apply (simp add: storePDE_def)
  apply (wp headM_inv hoare_drop_imps setObject_cte_wp_at2'[where Q="\<top>"])
    apply (clarsimp simp: updateObject_default_def in_monad
                         projectKO_opts_defs projectKOs)
   apply (rule equals0I)
   apply (clarsimp simp: updateObject_default_def in_monad
                         projectKOs projectKO_opts_defs)
  apply simp
  done

lemma storePDE_state_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace>
     storePDE ptr val
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  by (wpsimp wp: headM_inv hoare_drop_imps setObject_state_refs_of_eq
             simp: storePDE_def updateObject_default_def in_monad projectKOs)

lemma storePDE_state_hyp_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of' s)\<rbrace>
     storePDE ptr val
   \<lbrace>\<lambda>rv s. P (state_hyp_refs_of' s)\<rbrace>"
  by (wpsimp wp: headM_inv hoare_drop_imps setObject_state_hyp_refs_of_eq
             simp: storePDE_def updateObject_default_def in_monad projectKOs)

lemma storePTE_cte_wp_at'[wp]:
  "\<lbrace>\<lambda>s. P (cte_wp_at' P' p s)\<rbrace>
     storePTE ptr val
   \<lbrace>\<lambda>rv s. P (cte_wp_at' P' p s)\<rbrace>"
  apply (simp add: storePTE_def)
  apply (wp headM_inv hoare_drop_imps setObject_cte_wp_at2'[where Q="\<top>"])
    apply (clarsimp simp: updateObject_default_def in_monad
                          projectKO_opts_defs projectKOs)
   apply (rule equals0I)
   apply (clarsimp simp: updateObject_default_def in_monad
                         projectKOs projectKO_opts_defs)
  apply simp
  done

lemma storePTE_state_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace>
     storePTE ptr val
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  by (wpsimp wp: headM_inv hoare_drop_imps setObject_state_refs_of_eq
             simp: storePTE_def updateObject_default_def in_monad projectKOs)

lemma storePTE_state_hyp_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of' s)\<rbrace>
     storePTE ptr val
   \<lbrace>\<lambda>rv s. P (state_hyp_refs_of' s)\<rbrace>"
  by (wpsimp wp: headM_inv hoare_drop_imps setObject_state_hyp_refs_of_eq
             simp: storePTE_def updateObject_default_def in_monad projectKOs)

crunch cte_wp_at'[wp]: setIRQState "\<lambda>s. P (cte_wp_at' P' p s)"
crunch inv[wp]: getIRQSlot "P"

lemma setObject_ASIDPool_corres [corres]:
  "a = inv ASIDPool a' o ucast \<Longrightarrow>
  corres dc (asid_pool_at p and valid_etcbs) (asid_pool_at' p)
            (set_asid_pool p a) (setObject p a')"
  apply (simp add: set_asid_pool_def)
  apply (corressimp search: setObject_other_corres[where P="\<lambda>_. True"]
                        wp: get_object_ret get_object_wp)
  apply (simp add: other_obj_relation_def asid_pool_relation_def)
  apply (clarsimp simp: obj_at_simps )
  by (auto simp: obj_at_simps typ_at_to_obj_at_arches
          split: Structures_A.kernel_object.splits if_splits arch_kernel_obj.splits)

lemma setObject_ASIDPool_corres':
  "a = inv ASIDPool a' o ucast \<Longrightarrow>
  corres dc (asid_pool_at p and valid_etcbs) (pspace_aligned' and pspace_distinct')
            (set_asid_pool p a) (setObject p a')"
  apply (rule stronger_corres_guard_imp[OF setObject_ASIDPool_corres])
   apply auto
  done


lemma pde_relation_aligned_simp:
  "pde_relation_aligned (ucast (p && mask pd_bits >> pde_bits)::11 word) pde pde'
       = pde_relation_aligned ((p::word32) >> pde_bits) pde pde'"
  by (clarsimp simp: pde_relation_aligned_def pde_bits_def
              split: ARM_HYP_H.pde.splits if_splits)

lemma getObject_PDE_corres [@lift_corres_args, corres]:
  "corres (pde_relation_aligned (p >> pde_bits)) (pde_at p) (pde_at' p)
     (get_pde p) (getObject p)"
  apply (simp add: getObject_def get_pde_def get_pd_def get_object_def split_def bind_assoc)
  apply (rule corres_no_failI)
   apply (rule no_fail_pre, wp)
   apply (clarsimp simp: ko_wp_at'_def typ_at'_def lookupAround2_known1)
   apply (case_tac ko; simp)
   apply (rename_tac arch_kernel_object)
   apply (case_tac arch_kernel_object; simp add: projectKOs)
   apply (clarsimp simp: objBits_def cong: option.case_cong)
   apply (erule (1) ps_clear_lookupAround2)
     apply simp
    apply (erule is_aligned_no_overflow)
    apply (simp add: objBits_simps archObjSize_def word_bits_def)
   apply simp
  apply (clarsimp simp: in_monad loadObject_default_def projectKOs)
  apply (simp add: bind_assoc exec_gets)
  apply (clarsimp simp: pde_at_def obj_at_def)
  apply (clarsimp simp add: a_type_def return_def
                  split: if_split_asm Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp: typ_at'_def ko_wp_at'_def)
  apply (frule_tac s'=ba in in_magnitude_check, simp add: objBits_simps archObjSize_def vspace_bits_defs)
   apply assumption
  apply (simp add: in_magnitude_check objBits_simps archObjSize_def vspace_bits_defs)
  apply (clarsimp simp: state_relation_def pspace_relation_def)
  apply (drule bspec, blast)
  apply (clarsimp simp: other_obj_relation_def pde_relation_def)
  apply (erule_tac x="(ucast (p && mask pd_bits >> pde_bits))" in allE)
  apply (clarsimp simp: vspace_bits_defs mask_pd_bits_inner_beauty[simplified vspace_bits_defs, simplified])
  apply (clarsimp simp: obj_at_def pde_relation_aligned_simp[simplified vspace_bits_defs, simplified])
  done

lemmas aligned_distinct_pde_atI'
    = aligned_distinct_obj_atI'[where 'a=pde,
                                simplified, OF _ _ _ refl]

lemma aligned_distinct_relation_pde_atI'[elim]:
  "\<lbrakk> pde_at p s; pspace_relation (kheap s) (ksPSpace s');
     pspace_aligned' s'; pspace_distinct' s' \<rbrakk>
        \<Longrightarrow> pde_at' p s'"
  apply (clarsimp simp add: pde_at_def obj_at_def a_type_def)
  apply (simp split: Structures_A.kernel_object.split_asm
                     if_split_asm arch_kernel_obj.split_asm)
  apply (drule(1) pspace_relation_absD)
  apply (clarsimp simp: other_obj_relation_def)
  apply (drule_tac x="ucast ((p && mask pd_bits) >> pde_bits)"
                in spec)
  apply (subst(asm) ucast_ucast_len)
   apply (rule shiftr_less_t2n)
   apply (rule less_le_trans, rule and_mask_less_size)
    apply (simp add: word_size vspace_bits_defs)
   apply (simp add: vspace_bits_defs)
  apply (simp add: shiftr_shiftl1)
  apply (subst(asm) is_aligned_neg_mask_eq[where n=pde_bits])
   apply (erule is_aligned_andI1)
  apply (subst(asm) add.commute,
         subst(asm) word_plus_and_or_coroll2)
  apply (clarsimp simp: pde_relation_def)
  apply (drule(2) aligned_distinct_pde_atI')
  apply (clarsimp simp: obj_at'_def typ_at'_def ko_wp_at'_def
                        projectKOs)
  done

lemma pde_relation_alignedD:
  "\<lbrakk> kheap s (p && ~~ mask pd_bits) = Some (ArchObj (PageDirectory pd));
     pspace_relation (kheap s) (ksPSpace s');
     ksPSpace s' ((p && ~~ mask pd_bits) + (ucast x << pde_bits)) = Some (KOArch (KOPDE pde))\<rbrakk>
     \<Longrightarrow> pde_relation_aligned x (pd x) pde"
  apply (clarsimp simp:pspace_relation_def)
  apply (drule bspec,blast)
  apply (clarsimp simp:pde_relation_def)
  apply (drule_tac x = x in spec)
  apply (clarsimp simp:pde_relation_aligned_def
     split:ARM_HYP_H.pde.splits)
  done


lemma objBits_2n:
  "(1 :: word32) < 2 ^ objBits obj"
  by (simp add: objBits_simps' archObjSize_def vspace_bits_defs vcpu_bits_def
         split: kernel_object.split arch_kernel_object.split)

lemma magnitudeCheck_assert2:
  "\<lbrakk> is_aligned x n; (1 :: word32) < 2 ^ n; ksPSpace s x = Some v \<rbrakk> \<Longrightarrow>
   magnitudeCheck x (snd (lookupAround2 x (ksPSpace (s :: kernel_state)))) n
     = assert (ps_clear x n s)"
  using in_magnitude_check[where x=x and n=n and s=s and s'=s and v="()"]
  by (simp add: magnitudeCheck_assert in_monad)

lemma fst_fail: (* FIXME lib: move up *)
  "fst (fail s) = {}"
  by (simp add: fail_def)

lemma getObject_get_assert:
  assumes deflt: "\<And>a b c d. (loadObject a b c d :: ('a :: pspace_storable) kernel)
                          = loadObject_default a b c d"
  shows
  "(getObject p :: ('a :: pspace_storable) kernel)
   = do v \<leftarrow> gets (obj_at' (\<lambda>x :: 'a. True) p);
        assert v;
        gets (the o projectKO_opt o the o swp fun_app p o ksPSpace)
     od"
  apply (rule ext)
  apply (simp add: exec_get getObject_def split_def exec_gets
                   deflt loadObject_default_def projectKO_def2
                   alignCheck_assert)
  apply (case_tac "ksPSpace x p")
   apply (simp add: obj_at'_def assert_opt_def assert_def
             split: option.split if_split)
  apply (simp add: lookupAround2_known1 assert_opt_def
                   obj_at'_def projectKO_def2
            split: option.split)
  apply (clarsimp simp: fst_fail fst_return conj_comms project_inject
                        objBits_def)
  apply (simp only: assert2[symmetric],
         rule bind_apply_cong[OF refl])
  apply (clarsimp simp: in_monad)
  apply (fold objBits_def)
  apply (simp add: magnitudeCheck_assert2[OF _ objBits_2n])
  apply (rule bind_apply_cong[OF refl])
  apply (clarsimp simp: in_monad return_def simpler_gets_def)
  apply (simp add: iffD2[OF project_inject refl])
  done

lemma ex_in_fail[simp]:
  "(\<exists>x \<in> fst (fail s). P x) = False"
  by (auto simp: in_fail)

definition
  "master_pde_relation \<equiv> \<lambda>pde pde'.
    if isSuperSection pde'
    then pde_relation' pde (pde'\<lparr>pdeFrame := pdeFrame pde' && ~~ mask (pageBitsForSize ARMSuperSection)\<rparr>)
    else pde_relation' pde pde'"

lemmas isLargePage_simps[simp] = isLargePage_def [split_simps pte.split]
lemmas isSuperSection_simps[simp] = isSuperSection_def [split_simps pde.split]

lemma isLargePage_def':
  "isLargePage pte = (\<exists>p a b c. pte = LargePagePTE p a b c)"
  by (cases pte; simp)

lemma isSuperSection_def':
  "isSuperSection pde = (\<exists>p a b c. pde = SuperSectionPDE p a b c)"
  by (cases pde; simp)

lemma master_pde_relation_non_super:
  "\<lbrakk> pde_relation_aligned (p >> pde_bits) pde pde'; \<not>isSuperSection pde' \<rbrakk> \<Longrightarrow> master_pde_relation pde pde'"
  apply (clarsimp simp: pde_relation_aligned_def master_pde_relation_def)
  apply (cases pde'; simp)
  done

lemma getObject_pde_ko_at':
  "(pde::pde, s') \<in> fst (getObject p s) \<Longrightarrow> s' = s \<and> ko_at' pde p s"
  apply (rule context_conjI)
   apply (drule use_valid, rule getObject_inv[where P="(=) s"]; simp add: loadObject_default_inv)
  apply (drule use_valid, rule getObject_ko_at; clarsimp simp: obj_at_simps pde_bits_def)
  done

lemma getObject_pte_ko_at':
  "(pte::pte, s') \<in> fst (getObject p s) \<Longrightarrow> s' = s \<and> ko_at' pte p s"
  apply (rule context_conjI)
   apply (drule use_valid, rule getObject_inv[where P="(=) s"]; simp add: loadObject_default_inv)
  apply (drule use_valid, rule getObject_ko_at; clarsimp simp: obj_at_simps pte_bits_def)
  done

lemma ko_at'_pd:
  "\<lbrakk> ko_at' pde' p s'; (s,s') \<in> state_relation; pde_at p s \<rbrakk> \<Longrightarrow>
    \<exists>pd pde. ko_at (ArchObj (PageDirectory pd)) (p && ~~ mask pd_bits) s \<and> pd (ucast (p && mask pd_bits >> pde_bits)) = pde \<and>
             pde_relation_aligned (p >> pde_bits) pde pde'"
  apply (clarsimp simp: obj_at'_def projectKOs pde_at_def obj_at_def)
  apply (clarsimp simp: state_relation_def pspace_relation_def)
  apply (drule bspec, blast)
  apply (clarsimp simp: other_obj_relation_def pde_relation_def)
  apply (erule_tac x="(ucast (p && mask pd_bits >> pde_bits))" in allE)
  apply (clarsimp simp: vspace_bits_defs mask_pd_bits_inner_beauty[simplified vspace_bits_defs, simplified])
  apply (clarsimp simp: obj_at_def pde_relation_aligned_simp[simplified vspace_bits_defs, simplified])
  done

lemma pde_at_base:
  "pde_at p s \<Longrightarrow> pde_at (p && ~~mask (pde_bits + 4)) s"
  by (simp add: pde_at_def vspace_bits_defs mask_lower_twice2 is_aligned_andI1)

lemma of_nat_8_less_16_le_mask_7_is_aligned_3:
  fixes p :: machine_word
  shows "(\<exists>n. p = of_nat n * 8 \<and> n < 16) \<longleftrightarrow> p \<le> mask 7 \<and> is_aligned p 3"
  apply (rule iffI; clarsimp simp: word_shift_by_3)
   apply (clarsimp simp: is_aligned_mask le_mask_shiftl_le_mask of_nat_le_pow)
  apply (rule_tac x="unat (p >> 3)" in exI)
  apply (clarsimp simp: ucast_nat_def is_aligned_shiftr_shiftl
                intro!: unat_less_helper shiftr_less_t2n[where m=4, simplified])
  apply (clarsimp simp: mask_def elim!: le_less_trans)
  done

lemma superSectionPDEOffsets_nth:
  "n < length superSectionPDEOffsets \<Longrightarrow> superSectionPDEOffsets ! n = of_nat n * 8"
  apply (simp add: superSectionPDEOffsets_def vspace_bits_defs
                   upto_enum_step_def upto_enum_word nth_append
            split: if_split)
  apply clarsimp
  apply (subgoal_tac "n = 15")
   apply simp
  apply arith
  done

lemma length_superSectionPDEOffsets:
  "length superSectionPDEOffsets = 16"
  by (simp add: superSectionPDEOffsets_def vspace_bits_defs upto_enum_step_def)

lemma set_superSectionPDEOffsets:
  "set superSectionPDEOffsets = {of_nat n * 8 |n. n < 16}"
  unfolding set_conv_nth length_superSectionPDEOffsets[symmetric]
  by (rule Collect_cong; rule iffI; clarsimp; frule superSectionPDEOffsets_nth; force)

lemma set_superSectionPDEOffsets':
  "set superSectionPDEOffsets = {p. p \<le> mask 7 \<and> is_aligned p 3}"
  unfolding set_superSectionPDEOffsets
  by (rule Collect_cong, rule of_nat_8_less_16_le_mask_7_is_aligned_3)

lemma in_superSectionPDEOffsets:
  "is_aligned p 3 \<Longrightarrow> \<exists>p' \<in> set superSectionPDEOffsets. (p && ~~ mask 7) + p' = p"
  by (simp add: mask_out_sub_mask set_superSectionPDEOffsets'
                and_mask_eq_iff_le_mask[symmetric] aligned_after_mask)

lemma in_zip_set_snd:
  "\<lbrakk> x \<in> set xs; length ys = length xs \<rbrakk> \<Longrightarrow> \<exists>y. (x,y) \<in> set (zip xs ys)"
  apply (induct xs arbitrary: ys; clarsimp)
  apply (case_tac ys, auto)
  done

lemma in_zip_superSectionPDEOffsets:
  "is_aligned (p::32 word) 3 \<Longrightarrow>
    \<exists>(p',i) \<in> set (zip superSectionPDEOffsets [0.e.15::32 word]). (p && ~~ mask 7) + p' = p \<and> i \<le> 15"
  apply (drule in_superSectionPDEOffsets, clarsimp)
  apply (frule in_zip_set_snd[where ys="[0.e.15::32 word]"])
   apply (simp add: length_superSectionPDEOffsets)
  apply clarsimp
  apply (rule bexI)
   prefer 2
   apply assumption
  apply clarsimp
  apply (drule in_set_zip2)
  apply simp
  done

lemma addPAddr_mask_out:
  "\<lbrakk> x \<le> 15; m = 2^(n-4); is_aligned p n; 4 \<le> n; n < 32 \<rbrakk> \<Longrightarrow> p = addPAddr p (x * m) && ~~ mask n"
  apply (simp add: addPAddr_def fromPAddr_def)
  apply (subst is_aligned_add_or, assumption)
   apply (rule word_less_power_trans2; simp)
   apply unat_arith
  apply (simp add: word_ao_dist)
  apply (subst mask_out_0; simp?)
  apply (rule word_less_power_trans2; simp)
  apply unat_arith
  done

lemma valid_pde_duplicates_at'_pde_obj:
  "\<lbrakk> valid_pde_duplicates_at' (ksPSpace s) (p && ~~ mask (pde_bits + 4)); ko_at' pde' p s;
     pspace_distinct' s \<rbrakk>
  \<Longrightarrow> obj_at' (\<lambda>pde. isSuperSection pde \<and>
                 pde = pde' \<lparr>pdeFrame := pdeFrame pde' && ~~ mask (pageBitsForSize ARMSuperSection)\<rparr>)
              (p && ~~ mask (pde_bits + 4)) s"
  apply (clarsimp simp: obj_at'_def projectKOs valid_pde_duplicates_at'_def vspace_bits_defs)
  apply (drule (1) pspace_distinctD'[where x="p && ~~ mask 7"])
  apply (clarsimp simp: objBits_simps archObjSize_def is_aligned_neg_mask vspace_bits_defs)
  apply (drule in_zip_superSectionPDEOffsets)
  apply (clarsimp simp: vmsz_aligned_def)
  apply (drule (1) bspec)
  apply (clarsimp simp: isSuperSection_def' addPDEOffset_def addPAddr_mask_out)
  done


lemma get_master_pde_corres [@lift_corres_args, corres]:
  "corres master_pde_relation (pde_at p)
     (pde_at' p and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
      pspace_aligned' and pspace_distinct')
     (get_master_pde p) (getObject p)"
  apply (simp add: get_master_pde_def)
  apply (rule corres_no_failI)
   apply (rule no_fail_pre, wp)
   apply clarsimp
  apply (clarsimp simp: in_monad)
  using getObject_PDE_corres [OF refl, of p]
  apply (clarsimp simp: corres_underlying_def)
  apply (drule bspec, assumption, clarsimp)
  apply (drule (1) bspec, clarsimp)
  apply (drule getObject_pde_ko_at', clarsimp)
  apply (rename_tac pde' a b)
  apply (case_tac "isSuperSection pde'")
   apply (drule valid_duplicates'_D)
     apply (clarsimp simp: obj_at'_def projectKOs, assumption)
    apply assumption
   apply (drule (2) valid_pde_duplicates_at'_pde_obj)
   apply (drule obj_at_ko_at')+
   apply clarsimp
   apply (drule pde_at_base)
   apply (drule (2) ko_at'_pd)
   apply clarsimp
   apply (clarsimp simp: get_pde_def and_not_mask_twice get_pd_def bind_assoc get_object_def)
   apply (clarsimp simp: exec_gets pde_at_def obj_at_def vspace_bits_defs mask_lower_twice2)
   apply (clarsimp simp: isSuperSection_def')
   apply (clarsimp simp: pde_relation_aligned_def is_aligned_neg_mask is_aligned_shiftr)
   apply (clarsimp split: ARM_A.pde.splits)
   apply (auto simp: master_pde_relation_def vmsz_aligned'_def return_def vspace_bits_defs)[1]
  apply (clarsimp simp: get_pde_def and_not_mask_twice get_pd_def bind_assoc get_object_def)
  apply (clarsimp simp: exec_gets pde_at_def obj_at_def vspace_bits_defs mask_lower_twice2)
  apply (case_tac "pd (ucast ((p && ~~ mask 7) && mask 14 >> 3))";
           simp add: get_pde_def get_pd_def get_object_def bind_assoc exec_gets vspace_bits_defs,
           simp add: return_def master_pde_relation_non_super vspace_bits_defs)
  apply (subgoal_tac "pde_at (p && ~~mask 7) aa")
   prefer 2
   apply (clarsimp simp: pde_at_def obj_at_def vspace_bits_defs and_not_mask_twice
                         a_type_def is_aligned_andI1)
  apply (frule aligned_distinct_relation_pde_atI')
     apply fastforce
    apply assumption+
  apply (simp add: typ_at_to_obj_at_arches)
  apply (drule obj_at_ko_at')+
  apply clarsimp
  apply (thin_tac "pde_relation_aligned x p p'" for x p p')
  apply (frule (2) ko_at'_pd)
  apply (clarsimp simp: vspace_bits_defs and_not_mask_twice obj_at_def)
  apply (clarsimp simp: pde_relation_aligned_def split: if_split_asm)
  apply (clarsimp simp: obj_at'_def projectKOs objBits_simps archObjSize_def vspace_bits_defs)
  apply (drule (1) valid_duplicates'_D, fastforce)
  apply (clarsimp simp: vspace_bits_defs)
  apply (clarsimp simp: valid_pde_duplicates_at'_def)
  apply (drule in_zip_superSectionPDEOffsets, clarsimp)
  apply (drule (1) bspec, clarsimp simp: addPDEOffset_def)
  done

lemma getObject_PDE_corres':
  "corres (pde_relation_aligned (p >> pde_bits)) (pde_at p)
     (pspace_aligned' and pspace_distinct')
     (get_pde p) (getObject p)"
  apply (rule stronger_corres_guard_imp,
         rule getObject_PDE_corres)
   apply auto[1]
  apply clarsimp
  apply (rule aligned_distinct_relation_pde_atI')
   apply (simp add:state_relation_def)+
  done

lemma get_master_pde_corres':
  "corres master_pde_relation (pde_at p)
     ((\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
      pspace_aligned' and pspace_distinct')
     (get_master_pde p) (getObject p)"
  by (rule stronger_corres_guard_imp, rule get_master_pde_corres) auto

lemma pte_relation_aligned_simp:
  "pte_relation_aligned (ucast (p && mask pt_bits >> pte_bits)::9 word) pde pde' =
   pte_relation_aligned ((p::word32) >> pte_bits) pde pde'"
  by (clarsimp simp: pte_relation_aligned_def pte_bits_def
              split: ARM_HYP_H.pte.splits if_splits)

lemma getObject_PTE_corres [@lift_corres_args, corres]:
  "corres (pte_relation_aligned (p >> pte_bits)) (pte_at p) (pte_at' p)
     (get_pte p) (getObject p)"
  apply (simp add: getObject_def get_pte_def get_pt_def get_object_def split_def bind_assoc)
  apply (rule corres_no_failI)
   apply (rule no_fail_pre, wp)
   apply (clarsimp simp: ko_wp_at'_def typ_at'_def lookupAround2_known1)
   apply (case_tac ko, simp_all)[1]
   apply (rename_tac arch_kernel_object)
   apply (case_tac arch_kernel_object, simp_all add: projectKOs)[1]
   apply (clarsimp simp: objBits_def cong: option.case_cong)
   apply (erule (1) ps_clear_lookupAround2)
     apply simp
    apply (erule is_aligned_no_overflow)
    apply (simp add: objBits_simps archObjSize_def word_bits_def)
   apply simp
  apply (clarsimp simp: in_monad loadObject_default_def projectKOs)
  apply (simp add: bind_assoc exec_gets)
  apply (clarsimp simp: obj_at_def pte_at_def)
  apply (clarsimp simp add: a_type_def return_def
                  split: if_split_asm Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp: typ_at'_def ko_wp_at'_def)
  apply (drule_tac s'=ba in in_magnitude_check)
    apply (simp add: objBits_simps archObjSize_def pte_bits_def, assumption, clarsimp)
  apply (simp add: objBits_simps archObjSize_def)
  apply (clarsimp simp: state_relation_def pspace_relation_def)
  apply (drule bspec, blast)
  apply (clarsimp simp: other_obj_relation_def pte_relation_def)
  apply (erule_tac x="(ucast (p && mask pt_bits >> pte_bits))" in allE)
  apply (clarsimp simp: mask_pt_bits_inner_beauty
                        pte_relation_aligned_simp obj_at_def)
  done

lemma pte_relation_alignedD:
  "\<lbrakk> kheap s (p && ~~ mask pt_bits) = Some (ArchObj (PageTable pt));
     pspace_relation (kheap s) (ksPSpace s');
     ksPSpace s' ((p && ~~ mask pt_bits) + (ucast x << pte_bits)) = Some (KOArch (KOPTE pte))\<rbrakk>
     \<Longrightarrow> pte_relation_aligned x (pt x) pte"
  apply (clarsimp simp:pspace_relation_def)
  apply (drule bspec,blast)
  apply (clarsimp simp:pte_relation_def)
  apply (drule_tac x = x in spec)
  apply clarsimp
  done

lemmas aligned_distinct_pte_atI'
    = aligned_distinct_obj_atI'[where 'a=pte,
                                simplified, OF _ _ _ refl]

lemma aligned_distinct_relation_pte_atI'[elim]:
  "\<lbrakk> pte_at p s; pspace_relation (kheap s) (ksPSpace s');
     pspace_aligned' s'; pspace_distinct' s' \<rbrakk>
        \<Longrightarrow> pte_at' p s'"
  apply (clarsimp simp add: pte_at_def obj_at_def a_type_def)
  apply (simp split: Structures_A.kernel_object.split_asm
                     if_split_asm arch_kernel_obj.split_asm)
  apply (drule(1) pspace_relation_absD)
  apply (clarsimp simp: other_obj_relation_def)
  apply (drule_tac x="ucast ((p && mask pt_bits) >> pte_bits)"
                in spec)
  apply (subst(asm) ucast_ucast_len)
   apply (rule shiftr_less_t2n)
   apply (rule less_le_trans, rule and_mask_less_size)
    apply (simp add: word_size vspace_bits_defs)
   apply (simp add: vspace_bits_defs)
  apply (simp add: shiftr_shiftl1)
  apply (subst(asm) is_aligned_neg_mask_eq[where n=pte_bits])
   apply (erule is_aligned_andI1)
  apply (subst(asm) add.commute,
         subst(asm) word_plus_and_or_coroll2)
  apply (clarsimp simp: pte_relation_def)
  apply (drule(2) aligned_distinct_pte_atI')
  apply (clarsimp simp: obj_at'_def typ_at'_def ko_wp_at'_def
                        projectKOs)
  done

(* FIXME: move *)
lemma no_fail_getPTE [wp]:
  "no_fail (pte_at' p) (getObject p :: pte kernel)"
  apply (simp add: getObject_def split_def)
  apply (rule no_fail_pre)
   apply wp
  apply (clarsimp simp add: obj_at'_def projectKOs objBits_simps typ_at_to_obj_at_arches
                      cong: conj_cong)
  apply (rule ps_clear_lookupAround2, assumption+)
    apply simp
   apply (erule is_aligned_no_overflow)
  apply (clarsimp simp del: lookupAround2_same1)
  done

lemma ko_at'_pt:
  "\<lbrakk> ko_at' pte' p s'; (s,s') \<in> state_relation; pte_at p s \<rbrakk> \<Longrightarrow>
    \<exists>pt pte. ko_at (ArchObj (PageTable pt)) (p && ~~ mask pt_bits) s \<and> pt (ucast (p && mask pt_bits >> pte_bits)) = pte \<and>
             pte_relation_aligned (p >> pte_bits) pte pte'"
  apply (clarsimp simp: obj_at'_def projectKOs pte_at_def obj_at_def)
  apply (clarsimp simp: state_relation_def pspace_relation_def)
  apply (drule bspec, blast)
  apply (clarsimp simp: other_obj_relation_def pde_relation_def)
  apply (erule_tac x="(ucast (p && mask pt_bits >> pte_bits))" in allE)
  apply (clarsimp simp: vspace_bits_defs mask_pt_bits_inner_beauty[simplified vspace_bits_defs, simplified])
  apply (clarsimp simp: pte_relation_def pte_relation_aligned_simp[simplified vspace_bits_defs, simplified])
  done

lemma pte_at_base:
  "pte_at p s \<Longrightarrow> pte_at (p && ~~mask (pte_bits + 4)) s"
  by (simp add: pte_at_def vspace_bits_defs mask_lower_twice2 is_aligned_andI1)

lemma largePagePTEOffsets_nth:
  "n < length largePagePTEOffsets \<Longrightarrow> largePagePTEOffsets ! n = of_nat n * 8"
  apply (simp add: largePagePTEOffsets_def vspace_bits_defs
                   upto_enum_step_def upto_enum_word nth_append
            split: if_split)
  apply clarsimp
  apply (subgoal_tac "n = 15")
   apply simp
  apply arith
  done

lemma length_largePagePTEOffsets:
  "length largePagePTEOffsets = 16"
  by (simp add: largePagePTEOffsets_def vspace_bits_defs upto_enum_step_def)

lemma set_largePagePTEOffsets:
  "set largePagePTEOffsets = {of_nat n * 8 |n. n < 16}"
  unfolding set_conv_nth length_largePagePTEOffsets[symmetric]
  by (rule Collect_cong; rule iffI; clarsimp; frule largePagePTEOffsets_nth; force)

lemma set_largePagePTEOffsets':
  "set largePagePTEOffsets = {p. p \<le> mask 7 \<and> is_aligned p 3}"
  unfolding set_largePagePTEOffsets
  by (rule Collect_cong, rule of_nat_8_less_16_le_mask_7_is_aligned_3)

lemma in_largePagePTEOffsets:
  "is_aligned p 3 \<Longrightarrow> \<exists>p' \<in> set largePagePTEOffsets. (p && ~~ mask 7) + p' = p"
  by (simp add: mask_out_sub_mask set_largePagePTEOffsets'
                and_mask_eq_iff_le_mask[symmetric] aligned_after_mask)

lemma in_zip_largePagePTEOffsets:
  "is_aligned (p::32 word) 3 \<Longrightarrow>
    \<exists>(p',i) \<in> set (zip largePagePTEOffsets [0.e.15::32 word]). (p && ~~ mask 7) + p' = p \<and> i \<le> 15"
  apply (drule in_largePagePTEOffsets, clarsimp)
  apply (frule in_zip_set_snd[where ys="[0.e.15::32 word]"])
   apply (simp add: length_largePagePTEOffsets)
  apply clarsimp
  apply (rule bexI)
   prefer 2
   apply assumption
  apply clarsimp
  apply (drule in_set_zip2)
  apply simp
  done

lemma valid_pte_duplicates_at'_pte_obj:
  "\<lbrakk> valid_pte_duplicates_at' (ksPSpace s) (p && ~~ mask (pte_bits + 4)); ko_at' pte' p s;
     pspace_distinct' s \<rbrakk>
  \<Longrightarrow> obj_at' (\<lambda>pte. isLargePage pte \<and>
                 pte = pte' \<lparr>pteFrame := pteFrame pte' && ~~ mask (pageBitsForSize ARMLargePage)\<rparr>)
              (p && ~~ mask (pte_bits + 4)) s"
  apply (clarsimp simp: obj_at'_def projectKOs valid_pte_duplicates_at'_def vspace_bits_defs)
  apply (drule (1) pspace_distinctD'[where x="p && ~~ mask 7"])
  apply (clarsimp simp: objBits_simps archObjSize_def is_aligned_neg_mask vspace_bits_defs)
  apply (drule in_zip_largePagePTEOffsets)
  apply (clarsimp simp: vmsz_aligned_def)
  apply (drule (1) bspec)
  apply (clarsimp simp: isLargePage_def' addPTEOffset_def addPAddr_mask_out)
  done

definition
  "master_pte_relation \<equiv> \<lambda>pte pte'.
    if isLargePage pte'
    then pte_relation' pte (pte'\<lparr>pteFrame := pteFrame pte' && ~~ mask (pageBitsForSize ARMLargePage)\<rparr>)
    else pte_relation' pte pte'"

lemma master_pte_relation_non_large:
  "\<lbrakk> pte_relation_aligned (p >> pte_bits) pte pte'; \<not>isLargePage pte' \<rbrakk> \<Longrightarrow> master_pte_relation pte pte'"
  apply (clarsimp simp: pte_relation_aligned_def master_pte_relation_def)
  apply (cases pte'; simp)
  done

lemma get_master_pte_corres [corres]:
  "corres master_pte_relation (pte_at p)
     (pte_at' p and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
      pspace_aligned' and pspace_distinct')
     (get_master_pte p) (getObject p)"
  apply (simp add: get_master_pte_def)
  apply (rule corres_no_failI)
   apply (rule no_fail_pre, wp)
   apply clarsimp
  apply (clarsimp simp: in_monad)
  using getObject_PTE_corres [OF refl, of p]
  apply (clarsimp simp: corres_underlying_def)
  apply (drule bspec, assumption, clarsimp)
  apply (drule (1) bspec, clarsimp)
  apply (drule getObject_pte_ko_at', clarsimp)
  apply (rename_tac pte' a b)
  apply (case_tac "isLargePage pte'")
   apply (drule valid_duplicates'_pteD)
     apply (clarsimp simp: obj_at'_def projectKOs, assumption)
    apply assumption
   apply (drule (2) valid_pte_duplicates_at'_pte_obj)
   apply (drule obj_at_ko_at')+
   apply clarsimp
   apply (drule pte_at_base)
   apply (drule (2) ko_at'_pt)
   apply clarsimp
   apply (clarsimp simp: get_pte_def and_not_mask_twice get_pt_def bind_assoc get_object_def)
   apply (clarsimp simp: exec_gets pte_at_def obj_at_def vspace_bits_defs mask_lower_twice2)
   apply (clarsimp simp: isLargePage_def')
   apply (clarsimp simp: pte_relation_aligned_def is_aligned_neg_mask is_aligned_shiftr)
   apply (clarsimp split: ARM_A.pte.splits)
   apply (auto simp: master_pte_relation_def vmsz_aligned'_def return_def vspace_bits_defs)[1]
  apply (clarsimp simp: get_pte_def and_not_mask_twice get_pt_def bind_assoc get_object_def)
  apply (clarsimp simp: exec_gets pte_at_def obj_at_def vspace_bits_defs mask_lower_twice2)
  apply (case_tac "pt (ucast ((p && ~~ mask 7) && mask 12 >> 3))";
           simp add: get_pte_def get_pt_def get_object_def bind_assoc exec_gets vspace_bits_defs,
           simp add: return_def master_pte_relation_non_large vspace_bits_defs)
  apply (subgoal_tac "pte_at (p && ~~mask 7) aa")
   prefer 2
   apply (clarsimp simp: pte_at_def obj_at_def vspace_bits_defs and_not_mask_twice
                         a_type_def is_aligned_andI1)
  apply (frule aligned_distinct_relation_pte_atI')
     apply fastforce
    apply assumption+
  apply (simp add: typ_at_to_obj_at_arches)
  apply (drule obj_at_ko_at')+
  apply clarsimp
  apply (thin_tac "pte_relation_aligned x p p'" for x p p')
  apply (frule (2) ko_at'_pt)
  apply (clarsimp simp: vspace_bits_defs and_not_mask_twice obj_at_def)
  apply (clarsimp simp: pte_relation_aligned_def split: if_split_asm)
  apply (clarsimp simp: obj_at'_def projectKOs objBits_simps archObjSize_def vspace_bits_defs)
  apply (drule (1) valid_duplicates'_D, fastforce)
  apply (clarsimp simp: vspace_bits_defs)
  apply (clarsimp simp: valid_pte_duplicates_at'_def)
  apply (drule in_zip_largePagePTEOffsets, clarsimp)
  apply (drule (1) bspec, clarsimp simp: addPTEOffset_def)
  done

lemma getObject_PTE_corres':
  "corres (pte_relation_aligned (p >> pte_bits)) (pte_at p)
     (pspace_aligned' and pspace_distinct')
     (get_pte p) (getObject p)"
  apply (rule stronger_corres_guard_imp,
         rule getObject_PTE_corres)
   apply auto[1]
  apply clarsimp
  apply (rule aligned_distinct_relation_pte_atI')
   apply (simp add:state_relation_def)+
  done

lemma get_master_pte_corres':
  "corres master_pte_relation (pte_at p)
     ((\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
      pspace_aligned' and pspace_distinct')
     (get_master_pte p) (getObject p)"
  by (rule stronger_corres_guard_imp, rule get_master_pte_corres) auto

lemma setObject_PD_corres [corres]:
  "pde_relation_aligned (p>>pde_bits) pde pde' \<Longrightarrow>
         corres dc  (ko_at (ArchObj (PageDirectory pd)) (p && ~~ mask pd_bits)
                     and pspace_aligned and valid_etcbs)
                    (pde_at' p)
          (set_pd (p && ~~ mask pd_bits) (pd(ucast (p && mask pd_bits >> pde_bits) := pde)))
          (setObject p pde')"
  apply (simp add: set_pd_def set_object_def get_object_def a_type_def bind_assoc)
  apply (rule corres_no_failI)
   apply (rule no_fail_pre, wp)
    apply simp
   apply (clarsimp simp: obj_at'_def ko_wp_at'_def typ_at'_def lookupAround2_known1 projectKOs)
   apply (case_tac ko, simp_all)[1]
   apply (rename_tac arch_kernel_object)
   apply (case_tac arch_kernel_object, simp_all add: projectKOs)[1]
   apply (simp add: objBits_simps archObjSize_def word_bits_def)
  apply (clarsimp simp: setObject_def in_monad split_def updateObject_default_def projectKOs)
  apply (frule_tac s'=s'' in in_magnitude_check)
    apply (simp add: in_magnitude_check objBits_simps archObjSize_def pde_bits_def, assumption)
  apply (clarsimp simp: objBits_simps archObjSize_def pageBits_def)
  apply (clarsimp simp: obj_at_def exec_gets)
  apply (clarsimp simp: set_object_def bind_assoc exec_get)
  apply (clarsimp simp: put_def)
  apply (clarsimp simp: state_relation_def mask_pd_bits_inner_beauty)
  apply (rule conjI)
   apply (clarsimp simp: pspace_relation_def split del: if_split)
   apply (rule conjI)
    apply (subst pspace_dom_update, assumption)
     apply (simp add: a_type_def)
    apply (auto simp: dom_def)[1]
   apply (rule conjI)
    apply (drule bspec, blast)
    apply clarsimp
    apply (drule_tac x = x in spec)
    apply (clarsimp simp: pde_relation_def mask_pd_bits_inner_beauty pde_relation_aligned_simp
                   dest!: more_pd_inner_beauty[simplified pde_bits_def[symmetric]])
   apply (rule ballI)
   apply (drule (1) bspec)
   apply clarsimp
   apply (rule conjI)
    apply (clarsimp simp: pde_relation_def mask_pd_bits_inner_beauty pde_relation_aligned_simp
      dest!: more_pd_inner_beauty[simplified pde_bits_def[symmetric]])
   apply clarsimp
   apply (drule bspec, assumption)
   apply clarsimp
   apply (erule (1) obj_relation_cutsE)
       apply simp
      apply simp
     apply clarsimp
     apply (frule (1) pspace_alignedD)
     apply (drule_tac p=x in pspace_alignedD, assumption)
     apply simp
     apply (drule mask_alignment_ugliness)
        apply (simp add: pd_bits_def pageBits_def)
       apply (simp add: pd_bits_def pageBits_def)
      apply clarsimp
      apply (drule test_bit_size)
      apply (clarsimp simp: word_size pd_bits_def pageBits_def)
      apply arith
     apply (simp split: if_split_asm)
    apply (simp split: if_split_asm)
   apply (simp add: other_obj_relation_def
               split: Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (rule conjI)
   apply (clarsimp simp: ekheap_relation_def pspace_relation_def)
   apply (drule(1) ekheap_kheap_dom)
   apply clarsimp
   apply (drule_tac x=p in bspec, erule domI)
   apply (simp add: other_obj_relation_def
           split: Structures_A.kernel_object.splits)
  apply (rule conjI)
   apply (clarsimp simp add: ghost_relation_def)
   apply (erule_tac x="p && ~~ mask pd_bits" in allE)+
   apply fastforce
  apply (simp add: map_to_ctes_upd_other)
  apply (simp add: fun_upd_def)
  apply (simp add: caps_of_state_after_update obj_at_def swp_cte_at_caps_of)
  done

lemma setObject_PT_corres [corres]:
  "pte_relation_aligned (p >> pte_bits) pte pte' \<Longrightarrow>
         corres dc  (ko_at (ArchObj (PageTable pt)) (p && ~~ mask pt_bits)
                     and pspace_aligned and valid_etcbs)
                    (pte_at' p)
          (set_pt (p && ~~ mask pt_bits) (pt(ucast (p && mask pt_bits >> pte_bits) := pte)))
          (setObject p pte')"
  apply (simp add: set_pt_def set_object_def get_object_def a_type_def bind_assoc)
  apply (rule corres_no_failI)
   apply (rule no_fail_pre, wp)
    apply simp
   apply (clarsimp simp: obj_at'_def ko_wp_at'_def typ_at'_def lookupAround2_known1 projectKOs)
   apply (case_tac ko, simp_all)[1]
   apply (rename_tac arch_kernel_object)
   apply (case_tac arch_kernel_object, simp_all add: projectKOs)[1]
   apply (simp add: objBits_simps archObjSize_def word_bits_def)
  apply (clarsimp simp: setObject_def in_monad split_def updateObject_default_def projectKOs)
  apply (frule_tac s'=s'' in in_magnitude_check ; simp add: in_magnitude_check objBits_simps archObjSize_def pageBits_def)
   apply (simp add: pte_bits_def)
  apply (clarsimp simp: obj_at_def exec_gets)
  apply (clarsimp simp: set_object_def bind_assoc exec_get)
  apply (clarsimp simp: put_def)
  apply (clarsimp simp: state_relation_def mask_pt_bits_inner_beauty)
  apply (rule conjI)
   apply (clarsimp simp: pspace_relation_def split del: if_split)
   apply (rule conjI)
    apply (subst pspace_dom_update, assumption)
     apply (simp add: a_type_def)
    apply (auto simp: dom_def)[1]
   apply (rule conjI)
    apply (drule bspec, blast)
    apply (clarsimp simp: pte_relation_def mask_pt_bits_inner_beauty pte_relation_aligned_simp
                    dest!: more_pt_inner_beauty)
   apply (rule ballI)
   apply (drule (1) bspec)
   apply clarsimp
   apply (rule conjI)
    apply (clarsimp simp: pte_relation_def mask_pt_bits_inner_beauty pte_relation_aligned_simp
      dest!: more_pt_inner_beauty)
   apply clarsimp
   apply (drule bspec, assumption)
   apply clarsimp
   apply (erule (1) obj_relation_cutsE)
       apply simp
      apply clarsimp
      apply (frule (1) pspace_alignedD)
      apply (drule_tac p=x in pspace_alignedD, assumption)
      apply simp
      apply (drule mask_alignment_ugliness)
         apply (simp add: pt_bits_def pageBits_def)
        apply (simp add: pt_bits_def pageBits_def)
       apply clarsimp
       apply (drule test_bit_size)
       apply (clarsimp simp: word_size vspace_bits_defs)
       apply arith
      apply simp
     apply (simp split: if_split_asm)
    apply (simp split: if_split_asm)
   apply (simp add: other_obj_relation_def
               split: Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (rule conjI)
   apply (clarsimp simp: ekheap_relation_def pspace_relation_def)
   apply (drule(1) ekheap_kheap_dom)
   apply clarsimp
   apply (drule_tac x=p in bspec, erule domI)
   apply (simp add: other_obj_relation_def
               split: Structures_A.kernel_object.splits)
  apply (rule conjI)
   apply (clarsimp simp add: ghost_relation_def)
   apply (erule_tac x="p && ~~ mask pt_bits" in allE)+
   apply fastforce
  apply (simp add: map_to_ctes_upd_other)
  apply (simp add: fun_upd_def)
  apply (simp add: caps_of_state_after_update obj_at_def swp_cte_at_caps_of)
  done

lemma wordsFromPDEis2: "\<exists>a b . wordsFromPDE pde = [a , b]"
  by (cases pde ; clarsimp simp: wordsFromPDE_def tailM_def headM_def)

lemma storePDE_corres [corres]:
  "pde_relation_aligned (p >> pde_bits) pde pde' \<Longrightarrow>
  corres dc (pde_at p and pspace_aligned and valid_etcbs) (pde_at' p) (store_pde p pde) (storePDE p pde')"
  apply (simp add: store_pde_def storePDE_def)
  apply (insert wordsFromPDEis2[of pde'])
  apply (clarsimp simp: tailM_def headM_def)
  apply (rule corres_symb_exec_l)
     apply (erule setObject_PD_corres)
    apply (clarsimp simp: exs_valid_def get_pd_def get_object_def exec_gets bind_assoc
                          obj_at_def pde_at_def)
    apply (clarsimp simp: a_type_def return_def
                    split: Structures_A.kernel_object.splits arch_kernel_obj.splits if_split_asm)
   apply wp
   apply clarsimp
  apply (clarsimp simp: get_pd_def obj_at_def no_fail_def pde_at_def
                        get_object_def bind_assoc exec_gets)
  apply (clarsimp simp: a_type_def return_def
                  split: Structures_A.kernel_object.splits arch_kernel_obj.splits if_split_asm)
  done

lemma storePDE_corres':
  "pde_relation_aligned (p >> pde_bits) pde pde' \<Longrightarrow>
  corres dc
     (pde_at p and pspace_aligned and valid_etcbs) (pspace_aligned' and pspace_distinct')
     (store_pde p pde) (storePDE p pde')"
  apply (rule stronger_corres_guard_imp, rule storePDE_corres)
   apply auto
  done

lemma wordsFromPTEis2: "\<exists>a b . wordsFromPTE pte = [a , b]"
  by (cases pte ; clarsimp simp: wordsFromPTE_def tailM_def headM_def)

lemma storePTE_corres [corres]:
  "pte_relation_aligned (p>>pte_bits) pte pte' \<Longrightarrow>
  corres dc (pte_at p and pspace_aligned and valid_etcbs) (pte_at' p) (store_pte p pte) (storePTE p pte')"
  apply (simp add: store_pte_def storePTE_def)
  apply (insert wordsFromPTEis2[of pte'])
  apply (clarsimp simp: tailM_def headM_def)
  apply (rule corres_symb_exec_l)
     apply (erule setObject_PT_corres)
    apply (clarsimp simp: exs_valid_def get_pt_def get_object_def
                          exec_gets bind_assoc obj_at_def pte_at_def)
    apply (clarsimp simp: a_type_def return_def
                    split: Structures_A.kernel_object.splits arch_kernel_obj.splits if_split_asm)
   apply wp
   apply clarsimp
  apply (clarsimp simp: get_pt_def obj_at_def pte_at_def no_fail_def
                        get_object_def bind_assoc exec_gets)
  apply (clarsimp simp: a_type_def return_def
                  split: Structures_A.kernel_object.splits arch_kernel_obj.splits if_split_asm)
  done

lemma storePTE_corres':
  "pte_relation_aligned (p >> pte_bits) pte pte' \<Longrightarrow>
  corres dc (pte_at p and pspace_aligned and valid_etcbs)
            (pspace_aligned' and pspace_distinct')
            (store_pte p pte) (storePTE p pte')"
  apply (rule stronger_corres_guard_imp, rule storePTE_corres)
   apply auto
  done

lemma lookupPDSlot_corres [simp]:
  "lookupPDSlot pd vptr = lookup_pd_slot pd vptr"
  by (simp add: lookupPDSlot_def lookup_pd_slot_def)

defs checkPDAt_def:
  "checkPDAt pd \<equiv> stateAssert (page_directory_at' pd) []"

defs checkPTAt_def:
  "checkPTAt pt \<equiv> stateAssert (page_table_at' pt) []"

lemma pte_relation_must_pte:
  "pte_relation m (ArchObj (PageTable pt)) ko \<Longrightarrow> \<exists>pte. ko = (KOArch (KOPTE pte))"
  apply (case_tac ko)
   apply (simp_all add:pte_relation_def)
  apply clarsimp
  done

lemma pde_relation_must_pde:
  "pde_relation m (ArchObj (PageDirectory pd)) ko \<Longrightarrow> \<exists>pde. ko = (KOArch (KOPDE pde))"
  apply (case_tac ko)
   apply (simp_all add:pde_relation_def)
  apply clarsimp
  done

lemma page_table_at_state_relation:
  "\<lbrakk>page_table_at (ptrFromPAddr ptr) s; pspace_aligned s;
     (s, sa) \<in> state_relation;pspace_distinct' sa\<rbrakk>
  \<Longrightarrow> page_table_at' (ptrFromPAddr ptr) sa"
  apply (clarsimp simp:page_table_at'_def state_relation_def
    obj_at_def)
  apply (clarsimp simp:pspace_relation_def)
  apply (drule bspec)
   apply fastforce
  apply clarsimp
  apply (frule(1) pspace_alignedD)
   apply (simp add:ptrFromPAddr_def vspace_bits_defs)
  apply clarsimp
  apply (drule_tac x = "ucast y" in spec)
  apply (drule sym[where s = "pspace_dom (kheap s)"])
  apply (clarsimp simp:typ_at'_def ko_wp_at'_def)
  apply (subgoal_tac "(ptr + pptrBaseOffset + (y << 3)) \<in> dom (ksPSpace sa)")
   prefer 2
   apply (clarsimp simp: pspace_dom_def)
   apply (rule_tac x = "ptr + pptrBaseOffset" in bexI[where A = "dom (kheap s)"])
    apply (simp add:image_def pte_bits_def)
    apply (rule_tac x = "ucast y" in exI)
    apply (simp add:ucast_ucast_len)
   apply fastforce
  apply (thin_tac "dom a = b" for a b)
  apply (frule(1) pspace_alignedD)
  apply (clarsimp simp:ucast_ucast_len
    split:if_splits)
  apply (drule pte_relation_must_pte)
  apply (drule(1) pspace_distinctD')
  apply (clarsimp simp:objBits_simps archObjSize_def pte_bits_def)
  apply (rule is_aligned_weaken)
   apply (erule aligned_add_aligned)
    apply (rule is_aligned_shiftl_self)
   apply simp
  apply simp
  done

lemma page_directory_at_state_relation:
  "\<lbrakk>page_directory_at ptr s; pspace_aligned s;
     (s, sa) \<in> state_relation;pspace_distinct' sa\<rbrakk>
  \<Longrightarrow> page_directory_at' ptr sa"
  apply (clarsimp simp:page_directory_at'_def state_relation_def obj_at_def)
  apply (clarsimp simp:pspace_relation_def)
  apply (drule bspec)
   apply fastforce
  apply clarsimp
  apply (frule(1) pspace_alignedD)
   apply (simp add: vspace_bits_defs)
  apply clarsimp
  apply (drule_tac x = "ucast y" in spec)
  apply (drule sym[where s = "pspace_dom (kheap s)"])
  apply (clarsimp simp:typ_at'_def ko_wp_at'_def)
  apply (subgoal_tac "(ptr + (y << 3)) \<in> dom (ksPSpace sa)")
   prefer 2
   apply (clarsimp simp: pspace_dom_def)
   apply (rule_tac x = "ptr" in bexI[where A = "dom (kheap s)"])
    apply (simp add: image_def pde_bits_def)
    apply (rule_tac x = "ucast y" in exI)
    apply (simp add:ucast_ucast_len)
   apply fastforce
  apply (thin_tac "dom a = b" for a b)
  apply (frule(1) pspace_alignedD)
  apply (clarsimp simp:ucast_ucast_len split:if_splits)
  apply (drule pde_relation_must_pde)
  apply (drule(1) pspace_distinctD')
  apply (clarsimp simp:objBits_simps archObjSize_def pde_bits_def)
  apply (rule is_aligned_weaken)
   apply (erule aligned_add_aligned)
    apply (rule is_aligned_shiftl_self)
   apply simp
  apply simp
  done

lemma getPDE_wp:
  "\<lbrace>\<lambda>s. \<forall>ko. ko_at' (ko::pde) p s \<longrightarrow> Q ko s\<rbrace> getObject p \<lbrace>Q\<rbrace>"
  by (clarsimp simp: getObject_def split_def loadObject_default_def
                     archObjSize_def in_magnitude_check vspace_bits_defs
                     projectKOs in_monad valid_def obj_at'_def objBits_simps)

lemma getPTE_wp:
  "\<lbrace>\<lambda>s. \<forall>ko. ko_at' (ko::pte) p s \<longrightarrow> Q ko s\<rbrace> getObject p \<lbrace>Q\<rbrace>"
  by (clarsimp simp: getObject_def split_def loadObject_default_def
                     archObjSize_def in_magnitude_check vspace_bits_defs
                     projectKOs in_monad valid_def obj_at'_def objBits_simps)


lemmas get_pde_wp_valid = hoare_add_post'[OF get_pde_valid get_pde_wp]

lemma page_table_at_lift:
  "\<forall>s s'. (s, s') \<in> state_relation \<longrightarrow> (ptrFromPAddr ptr) = ptr' \<longrightarrow>
  (pspace_aligned s \<and> valid_pde (ARM_A.PageTablePDE ptr) s) \<longrightarrow>
  pspace_distinct' s' \<longrightarrow> page_table_at' ptr' s'"
  by (fastforce intro!: page_table_at_state_relation)

lemmas checkPTAt_corres [corresK] =
  corres_stateAssert_implied_frame[OF page_table_at_lift, folded checkPTAt_def]


lemma lookupPTSlot_corres [corres]:
  "corres (lfr \<oplus> (=))
          (pde_at (lookup_pd_slot pd vptr) and pspace_aligned and valid_vspace_objs
          and (\<exists>\<rhd> (lookup_pd_slot pd vptr && ~~ mask pd_bits)) and
          K (is_aligned pd pd_bits \<and> vptr < kernel_base))
          (pspace_aligned' and pspace_distinct')
          (lookup_pt_slot pd vptr) (lookupPTSlot pd vptr)"
  unfolding lookup_pt_slot_def lookupPTSlot_def lookupPTSlotFromPT_def
  apply (corressimp simp: pde_relation_aligned_def lookup_failure_map_def
                      wp: get_pde_wp_valid getPDE_wp)
  by (auto simp: lookup_failure_map_def obj_at_def)

declare in_set_zip_refl[simp]

crunch typ_at' [wp]: storePDE "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps mapM_x_wp' simp: crunch_simps ignore_del: setObject)

crunch typ_at' [wp]: storePTE "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps mapM_x_wp' simp: crunch_simps ignore_del: setObject)

lemmas storePDE_typ_ats[wp] = typ_at_lifts [OF storePDE_typ_at']
lemmas storePTE_typ_ats[wp] = typ_at_lifts [OF storePTE_typ_at']

lemma setObject_asid_typ_at' [wp]:
  "\<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> setObject p' (v::asidpool) \<lbrace>\<lambda>_ s. P (typ_at' T p s)\<rbrace>"
  by (wp setObject_typ_at')

lemmas setObject_asid_typ_ats' [wp] = typ_at_lifts [OF setObject_asid_typ_at']

lemma getObject_pte_inv[wp]:
  "\<lbrace>P\<rbrace> getObject p \<lbrace>\<lambda>rv :: pte. P\<rbrace>"
  by (simp add: getObject_inv loadObject_default_inv)

lemma getObject_pde_inv[wp]:
  "\<lbrace>P\<rbrace> getObject p \<lbrace>\<lambda>rv :: pde. P\<rbrace>"
  by (simp add: getObject_inv loadObject_default_inv)

crunch typ_at'[wp]: copyGlobalMappings "\<lambda>s. P (typ_at' T p s)"
  (wp: mapM_x_wp')

lemmas copyGlobalMappings_typ_ats[wp] = typ_at_lifts [OF copyGlobalMappings_typ_at']

lemma copy_global_mappings_corres [corres]:
  "corres dc (page_directory_at pd and pspace_aligned and valid_arch_state and valid_etcbs)
             (page_directory_at' pd and valid_arch_state')
          (copy_global_mappings pd) (copyGlobalMappings pd)"
  apply (simp add: copy_global_mappings_def copyGlobalMappings_def)
  done

lemma arch_cap_rights_update:
  "acap_relation c c' \<Longrightarrow>
   cap_relation (cap.ArchObjectCap (acap_rights_update (acap_rights c \<inter> msk) c))
                 (Arch.maskCapRights (rights_mask_map msk) c')"
  apply (cases c, simp_all add: ARM_HYP_H.maskCapRights_def
                                acap_rights_update_def Let_def isCap_simps)
  apply (simp add: maskVMRights_def vmrights_map_def rights_mask_map_def
                   validate_vm_rights_def vm_read_write_def vm_read_only_def
                   vm_kernel_only_def )
  done

lemma arch_deriveCap_inv:
  "\<lbrace>P\<rbrace> Arch.deriveCap arch_cap u \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp      add: ARM_HYP_H.deriveCap_def
                  cong: if_cong
             split del: if_split)
  apply (rule hoare_pre, wp undefined_valid)
  apply (cases u, simp_all add: isCap_defs)
  done

lemma arch_deriveCap_valid:
  "\<lbrace>valid_cap' (ArchObjectCap arch_cap)\<rbrace>
     Arch.deriveCap u arch_cap
   \<lbrace>\<lambda>rv. valid_cap' rv\<rbrace>,-"
  apply (simp      add: ARM_HYP_H.deriveCap_def
                  cong: if_cong
             split del: if_split)
  apply (rule hoare_pre, wp undefined_validE_R)
  apply (cases arch_cap, simp_all add: isCap_defs)
  apply (simp add: valid_cap'_def capAligned_def
                   capUntypedPtr_def ARM_HYP_H.capUntypedPtr_def)
  done

lemma arch_deriveCap_corres [corres]:
 "cap_relation (cap.ArchObjectCap c) (ArchObjectCap c') \<Longrightarrow>
  corres (ser \<oplus> (\<lambda>c c'. cap_relation c c'))
         \<top> \<top>
         (arch_derive_cap c)
         (Arch.deriveCap slot c')"
  unfolding arch_derive_cap_def ARM_HYP_H.deriveCap_def Let_def
  apply (cases c, simp_all add: isCap_simps split: option.splits split del: if_split)
      apply (clarify?, rule corres_noopE; wpsimp)+
  done

definition
  "vmattributes_map \<equiv> \<lambda>R. VMAttributes (PageCacheable \<in> R) False (XNever \<in> R)"

definition
  mapping_map :: "ARM_A.pte \<times> word32 list + ARM_A.pde \<times> word32 list \<Rightarrow>
                  ARM_HYP_H.pte \<times> word32 list + ARM_HYP_H.pde \<times> word32 list \<Rightarrow> bool"
where
  "mapping_map \<equiv> pte_relation' \<otimes> (=) \<oplus> pde_relation' \<otimes> (=)"

lemma createMappingEntries_corres [corres]:
  "\<lbrakk> vm_rights' = vmrights_map vm_rights;
     attrib' = vmattributes_map attrib \<rbrakk>
  \<Longrightarrow> corres (ser \<oplus> mapping_map)
          (\<lambda>s. (pgsz = ARMSmallPage \<or> pgsz = ARMLargePage \<longrightarrow> pde_at (lookup_pd_slot pd vptr) s)
           \<and> (is_aligned pd pd_bits \<and> vmsz_aligned vptr pgsz \<and> vptr < kernel_base \<and> vm_rights \<in> valid_vm_rights)
           \<and> valid_vspace_objs s \<and> pspace_aligned s \<and> (\<exists>\<rhd> (lookup_pd_slot pd vptr && ~~ mask pd_bits)) s)
          (pspace_aligned' and pspace_distinct')
          (create_mapping_entries base vptr pgsz vm_rights attrib pd)
          (createMappingEntries base vptr pgsz vm_rights' attrib' pd)"
  unfolding createMappingEntries_def mapping_map_def
  by (cases pgsz; corressimp simp: vmattributes_map_def)

lemma pte_relation'_Invalid_inv [simp]:
  "pte_relation' x ARM_HYP_H.pte.InvalidPTE = (x = ARM_A.pte.InvalidPTE)"
  by (cases x) auto

fun pte_vmsz_aligned' where
  "pte_vmsz_aligned' (LargePagePTE p _ _ _) = vmsz_aligned' p ARMLargePage"
| "pte_vmsz_aligned' (SmallPagePTE p _ _ _) = vmsz_aligned' p ARMSmallPage"
| "pte_vmsz_aligned' _ = True"

fun pde_vmsz_aligned' where
  "pde_vmsz_aligned' (SectionPDE p _ _ _) = vmsz_aligned' p ARMSection"
| "pde_vmsz_aligned' (SuperSectionPDE p _ _ _) = vmsz_aligned' p ARMSuperSection"
| "pde_vmsz_aligned' _ = True"

definition
  "valid_slots' m \<equiv> case m of
    Inl (pte, xs) \<Rightarrow> \<lambda>s. valid_pte' pte s \<and> pte_vmsz_aligned' pte
  | Inr (pde, xs) \<Rightarrow> \<lambda>s. valid_pde' pde s \<and> pde_vmsz_aligned' pde"

lemma createMappingEntries_valid_slots' [wp]:
  "\<lbrace>valid_objs' and
    K (vmsz_aligned' base sz \<and> vmsz_aligned' vptr sz \<and> ptrFromPAddr base \<noteq> 0 \<and> vm_rights \<noteq> VMNoAccess) \<rbrace>
  createMappingEntries base vptr sz vm_rights attrib pd
  \<lbrace>\<lambda>m. valid_slots' m\<rbrace>, -"
  apply (simp add: createMappingEntries_def)
  apply (rule hoare_pre)
   apply (wp|wpc|simp add: valid_slots'_def valid_mapping'_def)+
  apply (simp add: vmsz_aligned'_def)
  apply (auto elim: is_aligned_weaken)
  done

lemmas [corresc_simp] = master_pte_relation_def master_pde_relation_def

lemma ensureSafeMapping_corres [corres]:
  "mapping_map m m' \<Longrightarrow>
  corres (ser \<oplus> dc) (valid_mapping_entries m)
                    (pspace_aligned' and pspace_distinct'
                    and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)))
                    (ensure_safe_mapping m) (ensureSafeMapping m')"
  unfolding mapping_map_def ensureSafeMapping_def
  apply (cases m; cases m'; simp;
         match premises in "(_ \<otimes> (=)) p p'" for p p' \<Rightarrow> \<open>cases "fst p"; cases "fst p'"\<close>; clarsimp)
        by (corressimp corresK: mapME_x_corresK_inv
                            wp: get_master_pte_wp get_master_pde_wp getPTE_wp getPDE_wp;
            auto simp add: valid_mapping_entries_def)+

lemma asidHighBitsOf [simp]:
  "asidHighBitsOf asid = ucast (asid_high_bits_of asid)"
  apply (simp add: asidHighBitsOf_def asid_high_bits_of_def asidHighBits_def)
  apply word_eqI_solve
  done

lemma page_directory_at_lift:
  "corres_inst_eq ptr ptr' \<Longrightarrow> \<forall>s s'. (s, s') \<in> state_relation \<longrightarrow> True \<longrightarrow>
  (pspace_aligned s \<and> page_directory_at ptr s) \<longrightarrow>
  pspace_distinct' s' \<longrightarrow> page_directory_at' ptr' s'"
  by (fastforce simp: corres_inst_eq_def intro!: page_directory_at_state_relation )

lemmas checkPDAt_corres =
  corres_stateAssert_implied_frame[OF page_directory_at_lift, folded checkPDAt_def]

lemma getASID_wp:
  "\<lbrace>\<lambda>s. \<forall>ko. ko_at' (ko::asidpool) p s \<longrightarrow> Q ko s\<rbrace> getObject p \<lbrace>Q\<rbrace>"
  by (clarsimp simp: getObject_def split_def loadObject_default_def
                     archObjSize_def in_magnitude_check pageBits_def
                     projectKOs in_monad valid_def obj_at'_def objBits_simps)

lemma find_pd_for_asid_corres [@lift_corres_args, corres]:
  "corres (lfr \<oplus> (=)) ((\<lambda>s. valid_arch_state s \<or> vspace_at_asid asid pd s)
                           and valid_vspace_objs and pspace_aligned
                           and K (0 < asid \<and> asid \<le> mask asidBits))
                       (pspace_aligned' and pspace_distinct' and no_0_obj')
                       (find_pd_for_asid asid) (findPDForASID asid)"
  apply (simp add: find_pd_for_asid_def findPDForASID_def liftME_def bindE_assoc)
  apply (corressimp simp: liftE_bindE assertE_assert mask_asid_low_bits_ucast_ucast lookup_failure_map_def
                      wp: getPDE_wp getASID_wp
                  search: checkPDAt_corres corres_gets_asid)
  subgoal premises prems for s s'
  apply (intro allI impI conjI)
      subgoal asid_pool_at for x
       apply (insert prems)
       apply (elim conjE disjE)
       apply (fastforce dest: valid_asid_tableD)
       apply (clarsimp simp: vspace_at_asid_def)
       apply (clarsimp simp: vs_asid_refs_def graph_of_def elim!: vs_lookupE)
        apply (erule rtranclE)
        subgoal by simp
       apply (simp add: arm_asid_table_related[simplified o_def])
       apply (clarsimp dest!: vs_lookup1D)
        apply (erule rtranclE)
        apply (clarsimp simp: vs_refs_def graph_of_def obj_at_def a_type_def
                       split: Structures_A.kernel_object.splits
                              arch_kernel_obj.splits)
        apply (clarsimp dest!: vs_lookup1D)
         apply (erule rtranclE)
        apply (fastforce dest!: vs_lookup1D)
        by (clarsimp dest!: vs_lookup1D)
     subgoal pd_at for x pool xa
      apply (insert prems)
       apply (rule valid_vspace_obj_elims)
       apply (rule valid_vspace_objsD)
        apply (rule vs_lookupI)
        apply (rule vs_asid_refsI)
       apply fastforce
      apply (rule rtrancl_refl)
      by (simp add: ranI)+
    apply (insert prems)
    apply (fastforce simp add: asidRange_def mask_2pm1[symmetric])
  subgoal for x by (insert asid_pool_at[of x], auto simp: arm_asid_table_related)
  subgoal for x ko xa
   apply (cases ko; simp)
   apply (frule arm_asid_table_related[where s'=s', simplified o_def])
   apply (cut_tac asid_pool_at[of x, simplified obj_at_def])
     apply clarsimp
     apply (frule pspace_relation_absD, fastforce)
     apply (clarsimp simp: other_obj_relation_def obj_at'_def projectKOs asid_pool_relation_def)
        apply (cut_tac pd_at[of _ _ 0]; assumption?)
        apply (drule(1) no_0_obj'_abstract)
        by (auto simp add: obj_at_def inv_def o_def)
  done
  done

lemma find_pd_for_asid_corres':
  "corres (lfr \<oplus> (=)) (vspace_at_asid asid pd and valid_vspace_objs
                           and pspace_aligned and  K (0 < asid \<and> asid \<le> mask asidBits))
                       (pspace_aligned' and pspace_distinct' and no_0_obj')
                       (find_pd_for_asid asid) (findPDForASID asid)"
  apply (rule corres_guard_imp, rule find_pd_for_asid_corres[OF refl])
   apply fastforce
  apply simp
  done

lemma setObject_arch:
  assumes X: "\<And>p q n ko. \<lbrace>\<lambda>s. P (ksArchState s)\<rbrace> updateObject val p q n ko \<lbrace>\<lambda>rv s. P (ksArchState s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. P (ksArchState s)\<rbrace> setObject t val \<lbrace>\<lambda>rv s. P (ksArchState s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp X | simp)+
  done

lemma setObject_ASID_arch [wp]:
  "\<lbrace>\<lambda>s. P (ksArchState s)\<rbrace> setObject p (v::asidpool) \<lbrace>\<lambda>_ s. P (ksArchState s)\<rbrace>"
  apply (rule setObject_arch)
  apply (simp add: updateObject_default_def)
  apply wp
  apply simp
  done

lemma setObject_PDE_arch [wp]:
  "\<lbrace>\<lambda>s. P (ksArchState s)\<rbrace> setObject p (v::pde) \<lbrace>\<lambda>_ s. P (ksArchState s)\<rbrace>"
  apply (rule setObject_arch)
  apply (simp add: updateObject_default_def)
  apply wp
  apply simp
  done

lemma setObject_PTE_arch [wp]:
  "\<lbrace>\<lambda>s. P (ksArchState s)\<rbrace> setObject p (v::pte) \<lbrace>\<lambda>_ s. P (ksArchState s)\<rbrace>"
  apply (rule setObject_arch)
  apply (simp add: updateObject_default_def)
  apply wp
  apply simp
  done

lemma setObject_ASID_valid_arch [wp]:
  "\<lbrace>valid_arch_state'\<rbrace> setObject p (v::asidpool) \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  apply (rule valid_arch_state_lift'; wp?)
  apply (wpsimp wp: setObject_ko_wp_at simp: objBits_simps archObjSize_def pageBits_def, rule refl, simp)
  apply (clarsimp; rule conjI)
   prefer 2
   apply (clarsimp simp: pred_conj_def)
  apply (clarsimp simp: is_vcpu'_def ko_wp_at'_def obj_at'_def projectKOs)
  done

lemma setObject_PDE_valid_arch [wp]:
  "\<lbrace>valid_arch_state'\<rbrace> setObject p (v::pde) \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  apply (rule valid_arch_state_lift')
  apply (wp setObject_typ_at')+
  apply (wpsimp wp: setObject_ko_wp_at simp: objBits_simps archObjSize_def pageBits_def, rule refl)
   apply (simp add: pde_bits_def)
  apply (clarsimp; rule conjI)
   prefer 2
   apply (clarsimp simp: pred_conj_def)
  apply (clarsimp simp: is_vcpu'_def ko_wp_at'_def obj_at'_def projectKOs)
  done

lemma setObject_PTE_valid_arch [wp]:
  "\<lbrace>valid_arch_state'\<rbrace> setObject p (v::pte) \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  apply (rule valid_arch_state_lift')
  apply (wp setObject_typ_at')+
  apply (wpsimp wp: setObject_ko_wp_at simp: objBits_simps archObjSize_def pageBits_def, rule refl)
   apply (simp add: pte_bits_def)
  apply (clarsimp; rule conjI)
   prefer 2
   apply (clarsimp simp: pred_conj_def)
  apply (clarsimp simp: is_vcpu'_def ko_wp_at'_def obj_at'_def projectKOs)
  done

lemma setObject_ASID_ct [wp]:
  "\<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace> setObject p (e::asidpool) \<lbrace>\<lambda>_ s. P (ksCurThread s)\<rbrace>"
  apply (simp add: setObject_def updateObject_default_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setObject_PDE_ct [wp]:
  "\<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace> setObject p (e::pde) \<lbrace>\<lambda>_ s. P (ksCurThread s)\<rbrace>"
  apply (simp add: setObject_def updateObject_default_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setObject_pte_ct [wp]:
  "\<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace> setObject p (e::pte) \<lbrace>\<lambda>_ s. P (ksCurThread s)\<rbrace>"
  apply (simp add: setObject_def updateObject_default_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setObject_ASID_cur_tcb' [wp]:
  "\<lbrace>\<lambda>s. cur_tcb' s\<rbrace> setObject p (e::asidpool) \<lbrace>\<lambda>_ s. cur_tcb' s\<rbrace>"
  apply (simp add: cur_tcb'_def)
  apply (rule hoare_lift_Pf [where f=ksCurThread])
   apply wp+
  done

lemma setObject_PDE_cur_tcb' [wp]:
  "\<lbrace>\<lambda>s. cur_tcb' s\<rbrace> setObject p (e::pde) \<lbrace>\<lambda>_ s. cur_tcb' s\<rbrace>"
  apply (simp add: cur_tcb'_def)
  apply (rule hoare_lift_Pf [where f=ksCurThread])
   apply wp+
  done

lemma setObject_pte_cur_tcb' [wp]:
  "\<lbrace>\<lambda>s. cur_tcb' s\<rbrace> setObject p (e::pte) \<lbrace>\<lambda>_ s. cur_tcb' s\<rbrace>"
  apply (simp add: cur_tcb'_def)
  apply (rule hoare_lift_Pf [where f=ksCurThread])
   apply wp+
  done

(* FIXME in ArcAcc_AI *)
lemma pde_shifting:  (* ARMHYP >> 20? *)
  "\<lbrakk>is_aligned (vptr::word32) 25; x \<le> 0xF\<rbrakk>
   \<Longrightarrow> x + (vptr >> pageBits + pt_bits - pte_bits) < 0x800"
  apply (rule order_less_le_trans)
   apply (subst upper_bits_unset_is_l2p_32 [where n=11, symmetric])
    apply (clarsimp simp: word_bits_def)
   prefer 2
   apply simp
  apply (clarsimp simp: word_bits_def)
  subgoal premises prems for n'
  proof -
  have H: "(0xF::word32) < 2 ^ 4" by simp
  from prems show ?thesis
    apply (subst (asm) word_plus_and_or_coroll)
     apply (rule word_eqI)
     subgoal for n
       apply (clarsimp simp: word_size nth_shiftr is_aligned_nth vspace_bits_defs)
       apply (spec "21 + n")
       apply (frule test_bit_size[where n="21 + n"])
       apply (simp add: word_size)
       apply (insert H)
       apply (drule (1) order_le_less_trans)
       apply (drule bang_is_le)
       apply (drule_tac z="2 ^ 4" in order_le_less_trans, assumption)
       apply (drule word_power_increasing)
       by simp+
    apply (clarsimp simp: word_size nth_shiftl nth_shiftr is_aligned_nth vspace_bits_defs)
    apply (erule disjE)
     apply (insert H)[1]
     apply (drule (1) order_le_less_trans)
     apply (drule bang_is_le)
     apply (drule order_le_less_trans[where z="2 ^ 4"], assumption)
     apply (drule word_power_increasing; simp)
    apply (spec "21 + n'")
    apply (frule test_bit_size[where n = "21 + n'"])
    by (simp add: word_size)
  qed
done

lemma page_directory_pde_at_lookupI':
  "page_directory_at' pd s \<Longrightarrow> pde_at' (lookup_pd_slot pd vptr) s"
  apply (simp add: lookup_pd_slot_def Let_def vspace_bits_defs)
  apply (drule page_directory_pde_atI'; auto simp: vspace_bits_defs)
  apply (rule vptr_shiftr_le_2p_gen[simplified vspace_bits_defs, simplified])
  done

lemma page_table_pte_at_lookupI':
  "page_table_at' pt s \<Longrightarrow> pte_at' (lookup_pt_slot_no_fail pt vptr) s"
  apply (simp add: lookup_pt_slot_no_fail_def)
  apply (drule page_table_pte_atI'; auto simp: vspace_bits_defs)
  apply (rule vptr_shiftr_le_2pt_gen[simplified vspace_bits_defs, simplified])
  done

lemma storePTE_ctes [wp]:
  "\<lbrace>\<lambda>s. P (ctes_of s)\<rbrace> storePTE p pte \<lbrace>\<lambda>_ s. P (ctes_of s)\<rbrace>"
  apply (rule ctes_of_from_cte_wp_at [where Q=\<top>, simplified])
  apply (rule storePTE_cte_wp_at')
  done

lemma storePDE_ctes [wp]:
  "\<lbrace>\<lambda>s. P (ctes_of s)\<rbrace> storePDE p pte \<lbrace>\<lambda>_ s. P (ctes_of s)\<rbrace>"
  apply (rule ctes_of_from_cte_wp_at [where Q=\<top>, simplified])
  apply (rule storePDE_cte_wp_at')
  done


lemma storePDE_valid_objs [wp]:
  "\<lbrace>valid_objs' and valid_pde' pde\<rbrace> storePDE p pde \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (simp add: storePDE_def doMachineOp_def split_def)
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps|wpc|simp)+
   apply (rule setObject_valid_objs')
   prefer 2
   apply assumption
  apply (clarsimp simp: updateObject_default_def in_monad)
  apply (clarsimp simp: valid_obj'_def)
  done

lemma setObject_ASID_cte_wp_at'[wp]:
  "\<lbrace>\<lambda>s. P (cte_wp_at' P' p s)\<rbrace>
     setObject ptr (asid::asidpool)
   \<lbrace>\<lambda>rv s. P (cte_wp_at' P' p s)\<rbrace>"
  apply (wp setObject_cte_wp_at2'[where Q="\<top>"])
    apply (clarsimp simp: updateObject_default_def in_monad
                          projectKO_opts_defs projectKOs)
   apply (rule equals0I)
   apply (clarsimp simp: updateObject_default_def in_monad
                         projectKOs projectKO_opts_defs)
  apply simp
  done

lemma setObject_ASID_ctes_of'[wp]:
  "\<lbrace>\<lambda>s. P (ctes_of s)\<rbrace>
     setObject ptr (asid::asidpool)
   \<lbrace>\<lambda>rv s. P (ctes_of s)\<rbrace>"
  by (rule ctes_of_from_cte_wp_at [where Q=\<top>, simplified]) wp

lemma clearMemory_vms':
  "valid_machine_state' s \<Longrightarrow>
   \<forall>x\<in>fst (clearMemory ptr bits (ksMachineState s)).
      valid_machine_state' (s\<lparr>ksMachineState := snd x\<rparr>)"
  apply (clarsimp simp: valid_machine_state'_def
                        disj_commute[of "pointerInUserData p s" for p s])
  apply (drule_tac x=p in spec, simp)
  apply (drule_tac P4="\<lambda>m'. underlying_memory m' p = 0"
         in use_valid[where P=P and Q="\<lambda>_. P" for P], simp_all)
  apply (rule clearMemory_um_eq_0)
  done

lemma dmo_clearMemory_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (clearMemory w sz) \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply wp
  apply (clarsimp simp: invs'_def valid_state'_def)
  apply (rule conjI)
   apply (simp add: valid_irq_masks'_def, elim allEI, clarsimp)
   apply (drule use_valid)
     apply (rule no_irq_clearMemory[simplified no_irq_def, rule_format])
    apply simp_all
  apply (drule clearMemory_vms')
  apply fastforce
  done

end
end
