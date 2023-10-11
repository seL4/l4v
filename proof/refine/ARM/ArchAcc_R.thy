(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
  Lemmas on arch get/set object etc
*)

theory ArchAcc_R
imports SubMonad_R
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

lemmas valid_vspace_obj_elims [rule_format, elim!] =
  valid_vspace_obj.simps[@simp_to_elim, @ \<open>(drule bspec)?\<close>]

lemmas Arch_objBits_simps' = pteBits_def pdeBits_def pageBits_def objBits_simps

sublocale setObject_pte: simple_non_tcb_non_sc_non_reply_ko' "setObject :: _ \<Rightarrow> pte \<Rightarrow> _" getObject
  by (unfold_locales,
      simp add: projectKO_opts_defs archObjSize_def Arch_objBits_simps' | wp)+

sublocale setObject_pde: simple_non_tcb_non_sc_non_reply_ko' "setObject :: _ \<Rightarrow> pde \<Rightarrow> _" getObject
  by (unfold_locales,
      simp add: projectKO_opts_defs archObjSize_def Arch_objBits_simps' | wp)+

sublocale setObject_asidpool: simple_non_tcb_non_sc_non_reply_ko' "setObject :: _ \<Rightarrow> asidpool \<Rightarrow> _" getObject
  by (unfold_locales,
      simp add: projectKO_opts_defs archObjSize_def Arch_objBits_simps' | wp)+

sublocale storePDE: simple_non_tcb_non_sc_non_reply_ko' "storePDE" getObject
  by (unfold_locales,
      simp add: storePDE_def projectKO_opts_defs archObjSize_def Arch_objBits_simps' | wp)+

sublocale storePTE: simple_non_tcb_non_sc_non_reply_ko' "storePTE" getObject
  by (unfold_locales,
      simp add: storePTE_def projectKO_opts_defs archObjSize_def Arch_objBits_simps' | wp)+

lemmas storePTE_valid_objs'[wp] =
  storePTE.valid_objs'[simplified valid_obj'_def pred_conj_def, simplified]
lemmas storePTE_valid_pspace'[wp] =
  storePTE.valid_pspace'[simplified valid_obj'_def pred_conj_def, simplified]

lemmas storePDE_valid_objs'[wp] =
  storePDE.valid_objs'[simplified valid_obj'_def pred_conj_def, simplified]
lemmas storePDE_valid_pspace'[wp] =
  storePDE.valid_pspace'[simplified valid_obj'_def pred_conj_def, simplified]

end

context begin interpretation Arch . (*FIXME: arch_split*)

method readObject_arch_obj_at'_method
  =  clarsimp simp: readObject_def obind_def omonad_defs split_def loadObject_default_def obj_at'_def
                    objBits_simps archObjSize_def projectKOs bit_simps' typ_at_to_obj_at_arches
             split: option.splits if_split_asm

lemma readObject_misc_arch_ko_at'[simp, dest!]:
  shows
  readObject_ko_at'_pte: "readObject p s = Some (pte :: pte) \<Longrightarrow> ko_at' pte p s" and
  readObject_ko_at'_pde: "readObject p s = Some (pde :: pde) \<Longrightarrow> ko_at' pde p s" and
  readObject_ko_at'_asidpool: "readObject p s = Some (asidp :: asidpool) \<Longrightarrow> ko_at' asidp p s"
   by readObject_arch_obj_at'_method+


lemma readObject_misc_arch_obj_at'[simp]:
  shows
  readObject_pte_at'[simplified]: "bound (readObject p s ::pte option) \<Longrightarrow> pte_at' p s" and
  readObject_pde_at'[simplified]: "bound (readObject p s ::pde option) \<Longrightarrow> pde_at' p s" and
  readObject_asid_pool_at'[simplified]: "bound (readObject p s ::asidpool option) \<Longrightarrow> asid_pool_at' p s"
   by readObject_arch_obj_at'_method+

method no_ofail_readObject_method =
  clarsimp simp: obj_at'_def readObject_def obind_def omonad_defs split_def projectKO_eq no_ofail_def,
  rule ps_clear_lookupAround2, assumption+, simp,
  blast intro: is_aligned_no_overflow,
  clarsimp simp: bit_simps' project_inject obj_at_simps lookupAround2_known1 split: option.splits

lemma no_ofail_arch_obj_at'_readObject_pte[simp]:
  "no_ofail (obj_at' (P::pte \<Rightarrow> bool) p) (readObject p::pte kernel_r)"
  by no_ofail_readObject_method

lemma no_ofail_arch_obj_at'_readObject_pde[simp]:
  "no_ofail (obj_at' (P::pde \<Rightarrow> bool) p) (readObject p::pde kernel_r)"
  by no_ofail_readObject_method

lemma no_ofail_arch_obj_at'_readObject_asidpool[simp]:
  "no_ofail (obj_at' (P::asidpool \<Rightarrow> bool) p) (readObject p::asidpool kernel_r)"
  by no_ofail_readObject_method

lemma no_ofail_arch_misc_readObject:
  shows
  no_ofail_pte_at'_readObject[simp]: "no_ofail (pte_at' p) (readObject p::pte kernel_r)" and
  no_ofail_pde_at'_readObject[simp]: "no_ofail (pde_at' p) (readObject p::pde kernel_r)" and
  no_ofail_asidpool_at'_readObject[simp]: "no_ofail (asid_pool_at' p) (readObject p::asidpool kernel_r)"
  by (clarsimp simp: typ_at_to_obj_at_arches no_ofail_def
              dest!: no_ofailD[OF no_ofail_arch_obj_at'_readObject_pte]
                     no_ofailD[OF no_ofail_arch_obj_at'_readObject_pde]
                     no_ofailD[OF no_ofail_arch_obj_at'_readObject_asidpool])+

(* aliases for compatibility with master *)

lemmas getPTE_wp = setObject_pte.get_wp
lemmas getPDE_wp = setObject_pde.get_wp
lemmas getASID_wp = setObject_asidpool.getObject_wp

lemmas getObject_pte_inv[wp] = setObject_pte.getObject_inv
lemmas getObject_pde_inv[wp] = setObject_pde.getObject_inv
lemmas getObject_asidpool_inv = setObject_asidpool.getObject_inv

lemmas get_pte_sp' = setObject_pte.getObject_sp'
lemmas get_pde_sp' = setObject_pde.getObject_sp'
lemmas get_asidpool_sp' = setObject_asidpool.getObject_sp'

lemmas setObject_ASID_cteCaps_of[wp] = ctes_of_cteCaps_of_lift [OF setObject_asidpool.ctes_of]
lemmas storePTE_cteCaps_of[wp] = ctes_of_cteCaps_of_lift [OF storePTE.ctes_of]
lemmas storePDE_cteCaps_of[wp] = ctes_of_cteCaps_of_lift [OF storePDE.ctes_of]

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

lemma pte_at_cross:
  "\<lbrakk> pte_at p s; pspace_relation (kheap s) (ksPSpace s'); pspace_aligned s; pspace_distinct s \<rbrakk>
   \<Longrightarrow> pte_at' p s'"
  apply (drule (2) pspace_distinct_cross)
  apply (clarsimp simp: pte_at_def obj_at_def typ_at'_def ko_wp_at'_def)
  apply (prop_tac "p \<in> pspace_dom (kheap s)")
   apply (clarsimp simp: pspace_dom_def)
   apply (rule bexI)
    prefer 2
    apply fastforce
   apply (clarsimp simp: ran_def image_iff)
   apply (rule_tac x="(UCAST(32 \<rightarrow> 8) (p && mask pt_bits >> 2))" in exI)
   apply (simp add: mask_pt_bits_inner_beauty)
  apply (clarsimp simp: pspace_relation_def)
  apply (drule bspec, fastforce)
  apply (clarsimp simp:)
  apply (clarsimp simp: pte_relation_def)
  apply (drule spec[where x="(UCAST(32 \<rightarrow> 8) (p && mask pt_bits >> 2))"])
  apply (clarsimp)
   apply (simp add: mask_pt_bits_inner_beauty)
  apply (clarsimp simp: objBitsKO_def archObjSize_def pteBits_def)
  apply (clarsimp simp: pte_relation_aligned_def)
  apply (frule (1) pspace_distinctD')
  apply (clarsimp simp: objBitsKO_def archObjSize_def pteBits_def word_bits_def)
  done

lemma pde_at_cross:
  "\<lbrakk> pde_at p s; pspace_relation (kheap s) (ksPSpace s'); pspace_aligned s; pspace_distinct s \<rbrakk>
   \<Longrightarrow> pde_at' p s'"
  apply (drule (2) pspace_distinct_cross)
  apply (clarsimp simp: pde_at_def obj_at_def typ_at'_def ko_wp_at'_def)
  apply (prop_tac "p \<in> pspace_dom (kheap s)")
   apply (clarsimp simp: pspace_dom_def)
   apply (rule bexI)
    prefer 2
    apply fastforce
   apply (clarsimp simp: ran_def image_iff)
   apply (rule_tac x="(UCAST(32 \<rightarrow> 12) (p && mask pd_bits >> 2))" in exI)
   apply (simp add: mask_pd_bits_inner_beauty)
  apply (clarsimp simp: pspace_relation_def)
  apply (drule bspec, fastforce)
  apply (clarsimp simp:)
  apply (clarsimp simp: pde_relation_def)
  apply (drule spec[where x="(UCAST(32 \<rightarrow> 12) (p && mask pd_bits >> 2))"])
  apply (clarsimp)
   apply (simp add: mask_pd_bits_inner_beauty)
  apply (clarsimp simp: objBitsKO_def archObjSize_def pdeBits_def)
  apply (clarsimp simp: pde_relation_aligned_def)
  apply (frule (1) pspace_distinctD')
  apply (clarsimp simp: objBitsKO_def archObjSize_def pdeBits_def word_bits_def)
  done

lemma asid_pool_at_cross:
  "\<lbrakk> asid_pool_at p s; pspace_relation (kheap s) (ksPSpace s');
     pspace_aligned s; pspace_distinct s \<rbrakk>
   \<Longrightarrow> asid_pool_at' p s'"
  apply (drule (2) pspace_distinct_cross)
  apply (clarsimp simp: obj_at_def typ_at'_def ko_wp_at'_def)
  apply (prop_tac "p \<in> pspace_dom (kheap s)")
   apply (clarsimp simp: pspace_dom_def)
   apply (rule bexI)
    prefer 2
    apply fastforce
   apply clarsimp
  apply (clarsimp simp: pspace_relation_def)
  apply (drule bspec, fastforce)
  apply (clarsimp simp: other_obj_relation_def split: kernel_object.splits arch_kernel_object.splits)
  apply (clarsimp simp: objBits_simps)
  apply (frule (1) pspace_alignedD)
  apply (rule conjI, simp add: bit_simps archObjSize_def)
  apply (clarsimp simp: pspace_distinct'_def)
  apply (drule bspec, fastforce)
  apply (simp add: objBits_simps archObjSize_def pageBits_def word_bits_def)
  done

lemma pte_relation_must_pte:
  "pte_relation m (ArchObj (PageTable pt)) ko \<Longrightarrow> \<exists>pte. ko = (KOArch (KOPTE pte))"
  apply (case_tac ko)
   apply (simp_all add:pte_relation_def)
  apply clarsimp
  done

lemma is_aligned_pte_offset:
  "is_aligned pt_ptr pt_bits \<Longrightarrow>
   is_aligned (pt_ptr + (i << pt_bits)) pt_bits"
  apply (rule is_aligned_add)
   apply (erule is_aligned_weaken, simp)
  apply (simp add: is_aligned_shiftl)
  done

lemma page_table_at_cross:
  "\<lbrakk> page_table_at p s; pspace_aligned s; pspace_distinct s; pspace_relation (kheap s) (ksPSpace s') \<rbrakk> \<Longrightarrow>
   page_table_at' p s'"
  apply (clarsimp simp: page_table_at'_def)
  apply (rule context_conjI)
   apply (clarsimp simp: obj_at_def)
   apply (frule (1) pspace_alignedD)
   apply (simp add: bit_simps')
  apply clarsimp
  apply (rule pte_at_cross; assumption?)
  apply (clarsimp simp: obj_at_def pte_at_def  is_aligned_pte_offset pt_bits_def pageBits_def)
  apply (intro conjI)
   apply (rule_tac x="ArchObj (PageTable pt)" in exI)
   apply (intro conjI)
    apply (subgoal_tac "p + (y << 2) && ~~ mask 10 = p", simp)
    apply (subst is_aligned_mask_out_add_eq)
     apply (clarsimp simp: obj_at_def pte_at_def  is_aligned_pte_offset ptBits_def pteBits_def)
    apply clarsimp
    defer
    apply (clarsimp simp: a_type_def)
   apply (rule is_aligned_add)
    apply (erule is_aligned_weaken)
    apply (clarsimp simp: ptBits_def)
   apply (clarsimp simp: is_aligned_shift)
  apply (simp add: and_mask_0_iff_le_mask)
  apply (rule le_mask_shiftl_le_mask[where n=8]; simp add: mask_def)
  apply (frule word_less_sub_1, simp)
  done

lemma page_directory_at_cross:
  "\<lbrakk> page_directory_at p s; pspace_aligned s; pspace_distinct s; pspace_relation (kheap s) (ksPSpace s') \<rbrakk> \<Longrightarrow>
   page_directory_at' p s'"
  apply (clarsimp simp: page_directory_at'_def)
  apply (rule context_conjI)
   apply (clarsimp simp: obj_at_def)
   apply (frule (1) pspace_alignedD)
   apply (simp add: bit_simps')
  apply clarsimp
  apply (rule pde_at_cross; assumption?)
  apply (clarsimp simp: obj_at_def pde_at_def  is_aligned_pte_offset pdBits_def pdeBits_def pd_bits_def pageBits_def)
  apply (intro conjI)
   apply (rule_tac x="ArchObj (PageDirectory pd)" in exI)
   apply (intro conjI)
    apply (subgoal_tac "p + (y << 2) && ~~ mask 14 = p", simp)
    apply (subst is_aligned_mask_out_add_eq)
     apply (clarsimp simp: obj_at_def pte_at_def  is_aligned_pte_offset pdBits_def pdeBits_def)
    apply clarsimp
    defer
    apply (clarsimp simp: a_type_def)
   apply (rule is_aligned_add)
    apply (erule is_aligned_weaken)
    apply (clarsimp simp: ptBits_def)
   apply (clarsimp simp: is_aligned_shift)
  apply (simp add: and_mask_0_iff_le_mask)
  apply (rule le_mask_shiftl_le_mask[where n=12]; simp add: mask_def)
  apply (frule word_less_sub_1, simp)
  done

lemma corres_cross_over_asid_pool_at:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> asid_pool_at p s \<and> pspace_distinct s \<and> pspace_aligned s;
     corres r P (Q and asid_pool_at' p) f g \<rbrakk> \<Longrightarrow>
   corres r P Q f g"
  apply (rule corres_cross_over_guard[where Q="Q and asid_pool_at' p"])
   apply (drule meta_spec, drule (1) meta_mp, clarsimp)
   apply (erule asid_pool_at_cross, clarsimp simp: state_relation_def; assumption)
  apply assumption
  done

lemma corres_cross_over_pte_at:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> pte_at p s \<and> pspace_distinct s \<and> pspace_aligned s;
     corres r P (P' and pte_at' p) f g\<rbrakk> \<Longrightarrow>
   corres r P P' f g"
  apply (rule corres_cross_over_guard[where Q="P' and pte_at' p"])
   apply (drule meta_spec, drule (1) meta_mp, clarsimp)
   apply (erule pte_at_cross; assumption?)
   apply (simp add: state_relation_def)
  apply assumption
  done


lemma getObject_ASIDPool_corres [corres]:
  "p = p' \<Longrightarrow> corres (\<lambda>p p'. p = inv ASIDPool p' o ucast)
          (asid_pool_at p) (asid_pool_at' p')
          (get_asid_pool p) (getObject p')"
  apply (simp add: getObject_def get_asid_pool_def get_object_def split_def)
  apply (rule corres_no_failI)
   apply wp
   apply (fastforce simp: typ_at_to_obj_at_arches
                    dest: no_ofailD[OF no_ofail_asidpool_at'_readObject])
  apply (clarsimp simp: in_monad loadObject_default_def projectKOs gets_the_def)
  apply (simp add: bind_assoc exec_gets)
  apply (drule asid_pool_at_ko)
  apply (clarsimp simp: obj_at_def)
  apply (simp add: return_def)
  apply (clarsimp simp: state_relation_def pspace_relation_def)
  apply (drule bspec, blast)
  apply (clarsimp simp: other_obj_relation_def asid_pool_relation_def obj_at'_def projectKOs)
  done

lemma aligned_distinct_relation_asid_pool_atI'[elim]:
  "\<lbrakk> asid_pool_at p s; pspace_relation (kheap s) (ksPSpace s');
     pspace_aligned' s'; pspace_distinct' s'\<rbrakk>
        \<Longrightarrow> asid_pool_at' p s'"
  apply (drule asid_pool_at_ko)
  apply (clarsimp simp add: obj_at_def)
  apply (drule(1) pspace_relation_absD)
  apply (clarsimp simp: other_obj_relation_def)
  apply (simp split: Structures_H.kernel_object.split_asm
                     arch_kernel_object.split_asm)
  apply (drule (2) aligned'_distinct'_ko_at'I[where 'a=asidpool]; fastforce?)
  apply (clarsimp simp: obj_at'_def typ_at'_def ko_wp_at'_def
                        projectKOs)
  done

lemma getObject_ASIDPool_corres':
  "corres (\<lambda>p p'. p = inv ASIDPool p' o ucast)
          (asid_pool_at p) (pspace_aligned' and pspace_distinct')
          (get_asid_pool p) (getObject p)"
  by (corresKsimp search: getObject_ASIDPool_corres) fastforce

lemma setObject_asidpool_replies_of'[wp]:
  "setObject c (asidpool::asidpool) \<lbrace>\<lambda>s. P' (replies_of' s)\<rbrace>"
  by setObject_easy_cases

lemma setObject_pte_replies_of'[wp]:
  "setObject c (pte::pte) \<lbrace>\<lambda>s. P' (replies_of' s)\<rbrace>"
  by setObject_easy_cases

lemma setObject_pde_replies_of'[wp]:
  "setObject c (pde::pde) \<lbrace>\<lambda>s. P' (replies_of' s)\<rbrace>"
  by setObject_easy_cases

crunches storePDE, storePTE
  for replies_of'[wp]: "\<lambda>s. P (replies_of' s)"

crunch cte_wp_at'[wp]: setIRQState "\<lambda>s. P (cte_wp_at' P' p s)"
crunch inv[wp]: getIRQSlot "P"

lemma setObject_ASIDPool_corres [corres]:
  "p = p' \<Longrightarrow> a = inv ASIDPool a' o ucast \<Longrightarrow>
  corres dc (asid_pool_at p) (asid_pool_at' p')
            (set_asid_pool p a) (setObject p' a')"
  apply (simp add: set_asid_pool_def)
  apply (corresKsimp search: setObject_other_corres[where P="\<lambda>_. True"]
                        wp: get_object_ret get_object_wp)
  apply (simp add: other_obj_relation_def asid_pool_relation_def)
  apply (clarsimp simp: obj_at_simps )
  by (auto simp: obj_at_simps typ_at_to_obj_at_arches
          split: Structures_A.kernel_object.splits if_splits arch_kernel_obj.splits)

lemma setObject_ASIDPool_corres':
  "a = inv ASIDPool a' o ucast \<Longrightarrow>
  corres dc (asid_pool_at p) (pspace_aligned' and pspace_distinct')
            (set_asid_pool p a) (setObject p a')"
  apply (rule stronger_corres_guard_imp[OF setObject_ASIDPool_corres])
   apply auto
  done


lemma pde_relation_aligned_simp:
  "pde_relation_aligned (ucast (p && mask pd_bits >> 2)::12 word) pde pde'
       = pde_relation_aligned ((p::word32) >> 2) pde pde'"
  by (clarsimp simp: pde_relation_aligned_def
              split: ARM_H.pde.splits if_splits)

lemma getObject_PDE_corres [corres]:
  "p = p' \<Longrightarrow> corres (pde_relation_aligned (p >> 2)) (pde_at p) (pde_at' p')
     (get_pde p) (getObject p')"
  apply (simp add: getObject_def get_pde_def get_pd_def get_object_def split_def bind_assoc)
  apply (rule corres_no_failI)
  apply wp
   apply (fastforce simp: typ_at_to_obj_at_arches dest: no_ofailD[OF no_ofail_pde_at'_readObject])
   apply simp
  apply (clarsimp simp: in_monad loadObject_default_def projectKOs gets_the_def)
  apply (simp add: bind_assoc exec_gets)
  apply (clarsimp simp: pde_at_def obj_at_def)
  apply (clarsimp simp add: a_type_def return_def
                  split: if_split_asm Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp: obj_at'_def projectKOs)
  apply (simp add: in_magnitude_check objBits_simps archObjSize_def pageBits_def pdeBits_def)
  apply (clarsimp simp: state_relation_def pspace_relation_def)
  apply (drule bspec, blast)
  apply (clarsimp simp: other_obj_relation_def pde_relation_def)
  apply (erule_tac x="(ucast (p && mask pd_bits >> 2))" in allE)
  apply (clarsimp simp: mask_pd_bits_inner_beauty)
  apply (clarsimp simp: obj_at_def pde_relation_aligned_simp)
  done

lemmas aligned_distinct_pde_atI'
    = aligned'_distinct'_ko_at'I[where 'a=pde,
                                simplified, OF _ _ _ _ refl]

lemma aligned_distinct_relation_pde_atI'[elim]:
  "\<lbrakk> pde_at p s; pspace_relation (kheap s) (ksPSpace s');
     pspace_aligned' s'; pspace_distinct' s' \<rbrakk>
        \<Longrightarrow> pde_at' p s'"
  apply (clarsimp simp add: pde_at_def obj_at_def a_type_def)
  apply (simp split: Structures_A.kernel_object.split_asm
                     if_split_asm arch_kernel_obj.split_asm)
  apply (drule(1) pspace_relation_absD)
  apply (clarsimp simp: other_obj_relation_def)
  apply (drule_tac x="ucast ((p && mask pd_bits) >> 2)"
                in spec)
  apply (subst(asm) ucast_ucast_len)
   apply (rule shiftr_less_t2n)
   apply (rule less_le_trans, rule and_mask_less_size)
    apply (simp add: word_size pd_bits_def pageBits_def)
   apply (simp add: pd_bits_def pageBits_def)
  apply (simp add: shiftr_shiftl1)
  apply (subst(asm) is_aligned_neg_mask_eq[where n=2])
   apply (erule is_aligned_andI1)
  apply (subst(asm) add.commute,
         subst(asm) word_plus_and_or_coroll2)
  apply (clarsimp simp: pde_relation_def)
  apply (drule(2) aligned_distinct_pde_atI', simp)
  apply (clarsimp simp: obj_at'_def typ_at'_def ko_wp_at'_def
                        projectKOs)
  done

lemma pde_relation_alignedD:
  "\<lbrakk> kheap s (p && ~~ mask pd_bits) = Some (ArchObj (PageDirectory pd));
     pspace_relation (kheap s) (ksPSpace s');
     ksPSpace s' ((p && ~~ mask pd_bits) + (ucast x << 2)) = Some (KOArch (KOPDE pde))\<rbrakk>
     \<Longrightarrow> pde_relation_aligned x (pd x) pde"
  apply (clarsimp simp:pspace_relation_def)
  apply (drule bspec,blast)
  apply (clarsimp simp:pde_relation_def)
  apply (drule_tac x = x in spec)
  apply (clarsimp simp:pde_relation_aligned_def
     split:ARM_H.pde.splits)
  done

lemma get_master_pde_corres [@lift_corres_args, corres]:
  "corres pde_relation' (pde_at p)
     (pde_at' p and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
      pspace_aligned' and pspace_distinct')
     (get_master_pde p) (getObject p)"
  proof -
    have [simp]: "max pd_bits 6 = pd_bits"
      by (simp add:pd_bits_def pageBits_def)
    have expand: "p && ~~ mask pd_bits = (p && ~~ mask 6) && ~~ mask pd_bits"
      by (simp add: and_not_mask_twice)
    have [simp]: "is_aligned (p && ~~ mask 6 >> 2) 4"
      apply (rule is_aligned_shiftr)
      apply (simp add:is_aligned_neg_mask)
      done
  show ?thesis
    apply (simp add: getObject_def get_pde_def get_pd_def  get_object_def
      split_def bind_assoc pde_relation_aligned_def get_master_pde_def)
    apply (rule corres_no_failI)
     apply wp
   apply (fastforce simp: typ_at_to_obj_at_arches dest: no_ofailD[OF no_ofail_pde_at'_readObject])
    apply (clarsimp simp: in_monad loadObject_default_def gets_the_def
                          projectKOs and_not_mask_twice)
    apply (simp add: bind_assoc exec_gets)
    apply (clarsimp simp: pde_at_def obj_at_def)
    apply (clarsimp split:ARM_A.pde.splits)
    apply (intro conjI impI)
  \<comment> \<open>master_pde = InvaliatePTE\<close>
       apply (clarsimp simp add: a_type_def return_def get_pd_def
                  bind_def get_pde_def get_object_def gets_def get_def
                  split: if_split_asm Structures_A.kernel_object.splits arch_kernel_obj.splits)
       apply (clarsimp simp: obj_at'_def projectKOs)
       apply (clarsimp simp: objBits_simps archObjSize_def pageBits_def pdeBits_def)
       apply (clarsimp simp:state_relation_def)
       apply (frule_tac x = "(ucast (p && mask pd_bits >> 2))"
                     in pde_relation_alignedD)
         apply assumption
        apply (simp add:mask_pd_bits_inner_beauty)
       apply (clarsimp simp: pde_relation_aligned_def gets_the_def exec_gets return_def
                      split: if_splits ARM_H.pde.splits)
       apply (drule_tac p' = "p && ~~ mask 6" in valid_duplicates'_D[rotated])
          apply (simp add:is_aligned_neg_mask is_aligned_weaken[where y = 2])
         apply (clarsimp simp: vs_ptr_align_def and_not_mask_twice)
        apply simp
       apply (frule_tac x = "(ucast ((p && ~~ mask 6) && mask pd_bits >> 2))"
                     in pde_relation_alignedD)
         apply assumption
        apply (simp add:expand)
        apply (subst mask_pd_bits_inner_beauty)
         apply (simp add:is_aligned_neg_mask)
        apply assumption
       apply (clarsimp simp: pde_relation_aligned_def
                  is_aligned_mask[where 'a=32, symmetric])

  \<comment> \<open>master_pde = PageTablePDE\<close>
      apply (clarsimp simp add: a_type_def return_def get_pd_def
        bind_def get_pde_def get_object_def gets_def get_def
        split: if_split_asm Structures_A.kernel_object.splits arch_kernel_obj.splits)
      apply (clarsimp simp: obj_at'_def projectKOs)
      apply (clarsimp simp: objBits_simps archObjSize_def pageBits_def pdeBits_def)
      apply (clarsimp simp:state_relation_def)
      apply (frule_tac x = "(ucast (p && mask pd_bits >> 2))" in pde_relation_alignedD)
        apply assumption
       apply (simp add:mask_pd_bits_inner_beauty)
      apply (clarsimp simp:pde_relation_aligned_def gets_the_def exec_gets return_def
        split:if_splits ARM_H.pde.splits)
      apply (drule_tac p' = "p && ~~ mask 6" in valid_duplicates'_D[rotated])
         apply (simp add:is_aligned_neg_mask is_aligned_weaken[where y = 2])
        apply (clarsimp simp: vs_ptr_align_def)
       apply (simp add:and_not_mask_twice)
      apply (drule_tac x = "(ucast ((p && ~~ mask 6) && mask pd_bits >> 2))" in pde_relation_alignedD)
        apply assumption
       apply (simp add:expand)
       apply (subst mask_pd_bits_inner_beauty)
        apply (simp add:is_aligned_neg_mask)
       apply assumption
      apply (clarsimp simp:pde_relation_aligned_def
         is_aligned_mask[symmetric])
  \<comment> \<open>master_pde = SectionPDE\<close>
     apply (clarsimp simp add: a_type_def return_def get_pd_def
       bind_def get_pde_def get_object_def gets_def get_def
       split: if_split_asm Structures_A.kernel_object.splits arch_kernel_obj.splits)
      apply (clarsimp simp: obj_at'_def projectKOs)
     apply (clarsimp simp: objBits_simps archObjSize_def pageBits_def pdeBits_def)
     apply (clarsimp simp:state_relation_def)
     apply (frule_tac x = "(ucast (p && mask pd_bits >> 2))" in pde_relation_alignedD)
       apply assumption
      apply (simp add:mask_pd_bits_inner_beauty)
     apply (clarsimp simp:pde_relation_aligned_def gets_the_def exec_gets return_def
       split:if_splits ARM_H.pde.splits)
     apply (drule_tac p' = "p && ~~ mask 6" in valid_duplicates'_D[rotated])
        apply (simp add:is_aligned_neg_mask is_aligned_weaken[where y = 2])
       apply (clarsimp simp: vs_ptr_align_def)
      apply (simp add:and_not_mask_twice)
     apply (drule_tac x = "(ucast ((p && ~~ mask 6) && mask pd_bits >> 2))" in pde_relation_alignedD)
       apply assumption
      apply (simp add: expand)
      apply (subst mask_pd_bits_inner_beauty)
       apply (simp add:is_aligned_neg_mask)
      apply assumption
     apply (clarsimp simp:pde_relation_aligned_def
         is_aligned_mask[symmetric])
  \<comment> \<open>master_pde = SuperSectionPDE\<close>
    apply (clarsimp simp add: a_type_def return_def get_pd_def
      bind_def get_pde_def get_object_def gets_def get_def
      split: if_split_asm Structures_A.kernel_object.splits arch_kernel_obj.splits)
    apply (clarsimp simp: obj_at'_def projectKOs)
    apply (clarsimp simp: objBits_simps archObjSize_def pageBits_def pdeBits_def)
    apply (clarsimp simp:state_relation_def)
    apply (drule_tac s = a and s' = b and p = "p && ~~ mask 6"
      in aligned_distinct_relation_pde_atI'[rotated -1])
       apply (clarsimp simp:pde_at_def obj_at_def
         and_not_mask_twice a_type_simps is_aligned_neg_mask)
      apply simp
     apply simp
    apply (clarsimp simp:typ_at'_def ko_wp_at'_def)
    apply (case_tac ko; simp)
    apply (rename_tac arch_kernel_object)
    apply (case_tac arch_kernel_object; simp add: projectKOs)
    apply clarsimp
    apply (frule_tac x = "(ucast ((p && ~~ mask 6 )&& mask pd_bits >> 2))" in pde_relation_alignedD)
      apply assumption
     apply (simp add: expand)
     apply (subst mask_pd_bits_inner_beauty)
      apply (simp add:is_aligned_neg_mask)
     apply assumption
    apply (rename_tac pde)
    apply (case_tac pde)
     apply (simp add: pde_relation_aligned_def
                      is_aligned_mask[where 'a=32, symmetric])+
     apply clarsimp
    apply (drule_tac p = "p && ~~ mask 6" and p' = p  in valid_duplicates'_D)
       apply assumption
      apply simp
     apply (clarsimp simp: vs_ptr_align_def and_not_mask_twice)
    apply simp
    done
  qed

lemma getObject_PDE_corres' :
  "corres (pde_relation_aligned (p >> 2)) (pde_at p)
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
  "corres pde_relation' (pde_at p)
     ((\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
      pspace_aligned' and pspace_distinct')
     (get_master_pde p) (getObject p)"
  apply (rule stronger_corres_guard_imp,
         rule get_master_pde_corres)
   apply auto
  done


lemma pte_relation_aligned_simp:
  "pte_relation_aligned (ucast (p && mask pt_bits >> 2)::word8) pde pde' =
   pte_relation_aligned ((p::word32) >> 2) pde pde'"
  by (clarsimp simp: pte_relation_aligned_def
              split: ARM_H.pte.splits if_splits)

lemma getObject_PTE_corres [corres]:
  "p = p' \<Longrightarrow> corres (pte_relation_aligned (p >> 2)) (pte_at p) (pte_at' p')
     (get_pte p) (getObject p')"
  apply (simp add: getObject_def get_pte_def get_pt_def get_object_def split_def bind_assoc)
  apply (rule corres_no_failI)
  apply wp
   apply (fastforce simp: typ_at_to_obj_at_arches dest: no_ofailD[OF no_ofail_pte_at'_readObject])
   apply simp
  apply (clarsimp simp: in_monad loadObject_default_def projectKOs)
  apply (simp add: bind_assoc exec_gets gets_the_def)
  apply (clarsimp simp: obj_at_def pte_at_def)
  apply (clarsimp simp add: a_type_def return_def
                  split: if_split_asm Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp: obj_at'_def projectKOs)
  apply (simp add: objBits_simps archObjSize_def pageBits_def pteBits_def)
  apply (clarsimp simp: state_relation_def pspace_relation_def)
  apply (drule bspec, blast)
  apply (clarsimp simp: other_obj_relation_def pte_relation_def)
  apply (erule_tac x="(ucast (p && mask pt_bits >> 2))" in allE)
  apply (clarsimp simp: mask_pt_bits_inner_beauty
                        pte_relation_aligned_simp obj_at_def)
  done

lemma pte_relation_alignedD:
  "\<lbrakk> kheap s (p && ~~ mask pt_bits) = Some (ArchObj (PageTable pt));
     pspace_relation (kheap s) (ksPSpace s');
     ksPSpace s' ((p && ~~ mask pt_bits) + (ucast x << 2)) = Some (KOArch (KOPTE pte))\<rbrakk>
     \<Longrightarrow> pte_relation_aligned x (pt x) pte"
  apply (clarsimp simp:pspace_relation_def)
  apply (drule bspec,blast)
  apply (clarsimp simp:pte_relation_def)
  apply (drule_tac x = x in spec)
  apply clarsimp
  done

lemmas aligned_distinct_pte_atI'
    = aligned'_distinct'_ko_at'I[where 'a=pte,
                                simplified, OF _ _ _ _ refl]

lemma aligned_distinct_relation_pte_atI'[elim]:
  "\<lbrakk> pte_at p s; pspace_relation (kheap s) (ksPSpace s');
     pspace_aligned' s'; pspace_distinct' s' \<rbrakk>
        \<Longrightarrow> pte_at' p s'"
  apply (clarsimp simp add: pte_at_def obj_at_def a_type_def)
  apply (simp split: Structures_A.kernel_object.split_asm
                     if_split_asm arch_kernel_obj.split_asm)
  apply (drule(1) pspace_relation_absD)
  apply (clarsimp simp: other_obj_relation_def)
  apply (drule_tac x="ucast ((p && mask pt_bits) >> 2)"
                in spec)
  apply (subst(asm) ucast_ucast_len)
   apply (rule shiftr_less_t2n)
   apply (rule less_le_trans, rule and_mask_less_size)
    apply (simp add: word_size pt_bits_def pageBits_def)
   apply (simp add: pt_bits_def pageBits_def)
  apply (simp add: shiftr_shiftl1)
  apply (subst(asm) is_aligned_neg_mask_eq[where n=2])
   apply (erule is_aligned_andI1)
  apply (subst(asm) add.commute,
         subst(asm) word_plus_and_or_coroll2)
  apply (clarsimp simp: pte_relation_def)
  apply (drule(2) aligned_distinct_pte_atI', simp)
  apply (clarsimp simp: obj_at'_def typ_at'_def ko_wp_at'_def
                        projectKOs)
  done

lemma get_master_pte_corres [@lift_corres_args, corres]:
  "corres pte_relation' (pte_at p)
     (pte_at' p and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
      pspace_aligned' and pspace_distinct')
     (get_master_pte p) (getObject p)"
  proof -
    have [simp]: "max pt_bits 6 = pt_bits"
      by (simp add:pd_bits_def pageBits_def pt_bits_def)
    have expand: "p && ~~ mask pt_bits = (p && ~~ mask 6) && ~~ mask pt_bits"
      by (simp add: and_not_mask_twice)
    have [simp]: "is_aligned (p && ~~ mask 6 >> 2) 4"
      apply (rule is_aligned_shiftr)
      apply (simp add:is_aligned_neg_mask)
      done
  show ?thesis
    apply (simp add: getObject_def get_pte_def get_pt_def  get_object_def
      split_def bind_assoc pte_relation_aligned_def get_master_pte_def)
    apply (rule corres_no_failI)
   apply wp
   apply (fastforce simp: typ_at_to_obj_at_arches dest: no_ofailD[OF no_ofail_pte_at'_readObject])
    apply simp
    apply (clarsimp simp: in_monad loadObject_default_def
      projectKOs and_not_mask_twice gets_the_def)
    apply (simp add: bind_assoc exec_gets)
    apply (clarsimp simp: pte_at_def obj_at_def)
    apply (clarsimp split:ARM_A.pte.splits)
    apply (intro conjI impI)
  \<comment> \<open>master_pde = InvaliatePTE\<close>
      apply (clarsimp simp add: a_type_def return_def get_pt_def
                  bind_def get_pte_def get_object_def gets_def get_def
                  split: if_split_asm Structures_A.kernel_object.splits arch_kernel_obj.splits)
      apply (clarsimp simp: obj_at'_def projectKOs)
      apply (clarsimp simp: objBits_simps archObjSize_def pageBits_def pteBits_def)
      apply (clarsimp simp:state_relation_def)
      apply (frule_tac x = "(ucast (p && mask pt_bits >> 2))" in pte_relation_alignedD)
        apply assumption
       apply (simp add:mask_pt_bits_inner_beauty)
      apply (clarsimp simp:pte_relation_aligned_def gets_the_def exec_gets return_def
        split:if_splits ARM_H.pte.splits)
      apply (drule_tac p' = "p && ~~ mask 6" in valid_duplicates'_D[rotated])
         apply (simp add:is_aligned_weaken[where y = 2] is_aligned_neg_mask)
        apply (clarsimp simp: vs_ptr_align_def)
       apply (simp add:and_not_mask_twice)
      apply (frule_tac x = "(ucast ((p && ~~ mask 6) && mask pt_bits >> 2))" in pte_relation_alignedD)
        apply assumption
       apply (simp add:expand)
       apply (subst mask_pt_bits_inner_beauty)
        apply (simp add:is_aligned_neg_mask)
       apply assumption
      apply (clarsimp simp: pte_relation_aligned_def
                 is_aligned_mask[where 'a=32, symmetric])
  \<comment> \<open>master_pde = LargePagePTE\<close>
     apply (clarsimp simp add: a_type_def return_def get_pt_def
       bind_def get_pte_def get_object_def gets_def get_def
       split: if_split_asm Structures_A.kernel_object.splits arch_kernel_obj.splits)
      apply (clarsimp simp: obj_at'_def projectKOs)
     apply (clarsimp simp: objBits_simps archObjSize_def pageBits_def pteBits_def)
     apply (clarsimp simp:state_relation_def)
     apply (drule_tac s = a and s' = b and p = "p && ~~ mask 6"
      in aligned_distinct_relation_pte_atI'[rotated -1])
        apply (clarsimp simp:pte_at_def obj_at_def
          and_not_mask_twice a_type_simps is_aligned_neg_mask)
       apply simp
      apply simp
     apply (clarsimp simp:typ_at'_def ko_wp_at'_def)
     apply (case_tac ko; simp)
     apply (rename_tac arch_kernel_object)
     apply (case_tac arch_kernel_object, simp_all add: projectKOs)[1]
     apply clarsimp
     apply (frule_tac x = "(ucast ((p && ~~ mask 6 )&& mask pt_bits >> 2))" in pte_relation_alignedD)
       apply assumption
      apply (simp add: expand)
      apply (subst mask_pt_bits_inner_beauty)
       apply (simp add:is_aligned_neg_mask)
      apply assumption
     apply (rename_tac pte)
     apply (case_tac pte)
       apply (simp_all add:pte_relation_aligned_def is_aligned_mask[symmetric])
     apply (drule_tac p = "p && ~~ mask 6" and p' = p  in valid_duplicates'_D)
        apply assumption
       apply simp
      apply (clarsimp simp: vs_ptr_align_def and_not_mask_twice)
     apply (clarsimp simp: if_bool_eq_disj)
  \<comment> \<open>master_pde = SmallPagePTE\<close>
    apply (clarsimp simp add: a_type_def return_def get_pt_def
               bind_def get_pte_def get_object_def gets_def get_def
            split: if_split_asm Structures_A.kernel_object.splits
                   arch_kernel_obj.splits)
      apply (clarsimp simp: obj_at'_def projectKOs)
   apply (clarsimp simp: objBits_simps
                         archObjSize_def pageBits_def pteBits_def)
   apply (clarsimp simp:state_relation_def)
   apply (frule_tac x = "(ucast (p && mask pt_bits >> 2))"
                 in pte_relation_alignedD)
     apply assumption
    apply (simp add:mask_pt_bits_inner_beauty)
   apply (clarsimp simp:pte_relation_aligned_def gets_the_def exec_gets return_def
     split:if_splits ARM_H.pte.splits)
   apply (drule_tac p' = "p && ~~ mask 6" in valid_duplicates'_D[rotated])
      apply (simp add:is_aligned_weaken[where y = 2] is_aligned_neg_mask)
     apply (clarsimp simp: vs_ptr_align_def)
    apply (simp add:and_not_mask_twice)
   apply (drule_tac x = "(ucast ((p && ~~ mask 6) && mask pt_bits >> 2))"
                 in pte_relation_alignedD)
     apply assumption
    apply (simp add: expand)
    apply (subst mask_pt_bits_inner_beauty)
     apply (simp add:is_aligned_neg_mask)
    apply assumption
   apply (clarsimp simp: pte_relation_aligned_def
                         is_aligned_mask[where 'a=32, symmetric])
   done
  qed

lemma getObject_PTE_corres':
  "corres (pte_relation_aligned (p >> 2)) (pte_at p)
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
  "corres pte_relation' (pte_at p)
     ((\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
      pspace_aligned' and pspace_distinct')
     (get_master_pte p) (getObject p)"
  apply (rule stronger_corres_guard_imp,
         rule get_master_pte_corres)
   apply auto
  done

\<comment> \<open>setObject_other_corres unfortunately doesn't work here\<close>
lemma setObject_PD_corres [@lift_corres_args, corres]:
  "pde_relation_aligned (p>>2) pde pde' \<Longrightarrow>
         corres dc  (ko_at (ArchObj (PageDirectory pd)) (p && ~~ mask pd_bits)
                     and pspace_aligned)
                    (pde_at' p)
          (set_pd (p && ~~ mask pd_bits) (pd(ucast (p && mask pd_bits >> 2) := pde)))
          (setObject p pde')"
  apply (simp add: set_pd_def set_object_def get_object_def bind_assoc
                   a_type_def[split_simps kernel_object.split arch_kernel_obj.split])
  apply (rule corres_no_failI)
   apply (rule no_fail_pre, wp)
    apply simp
   apply (clarsimp simp: obj_at'_def ko_wp_at'_def typ_at'_def lookupAround2_known1 projectKOs)
   apply (case_tac ko, simp_all)[1]
   apply (rename_tac arch_kernel_object)
   apply (case_tac arch_kernel_object, simp_all add: projectKOs)[1]
   apply (simp add: objBits_simps archObjSize_def word_bits_def)
  apply (clarsimp simp: setObject_def in_monad split_def updateObject_default_def projectKOs)
  apply (simp add: in_magnitude_check objBits_simps archObjSize_def pageBits_def pdeBits_def)
  apply (clarsimp simp: obj_at_def gets_the_def)
  apply (clarsimp simp: set_object_def bind_assoc exec_get exec_gets)
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
      dest!: more_pd_inner_beauty)
   apply (rule ballI)
   apply (drule (1) bspec)
   apply clarsimp
   apply (rule conjI)
    apply (clarsimp simp: pde_relation_def mask_pd_bits_inner_beauty pde_relation_aligned_simp
      dest!: more_pd_inner_beauty)
   apply clarsimp
   apply (drule bspec, assumption)
   apply clarsimp
   apply (erule (1) obj_relation_cutsE)
         apply (simp+)[4]
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
   apply (fastforce simp: sc_replies_relation_def sc_replies_of_scs_def map_project_def
                          scs_of_kh_def opt_map_def projectKO_opts_defs)
  apply (rule conjI)
   apply (clarsimp simp add: ghost_relation_def)
   apply (erule_tac x="p && ~~ mask pd_bits" in allE)+
   apply fastforce
  apply (simp add: map_to_ctes_upd_other)
  apply (simp add: fun_upd_def)
  apply (simp add: caps_of_state_after_update obj_at_def swp_cte_at_caps_of)
  done


lemma setObject_PT_corres [@lift_corres_args, corres]:
  "pte_relation_aligned (p >> 2) pte pte' \<Longrightarrow>
         corres dc  (ko_at (ArchObj (PageTable pt)) (p && ~~ mask pt_bits)
                     and pspace_aligned)
                    (pte_at' p)
          (set_pt (p && ~~ mask pt_bits) (pt(ucast (p && mask pt_bits >> 2) := pte)))
          (setObject p pte')"
  apply (simp add: set_pt_def set_object_def get_object_def bind_assoc
                   a_type_def[split_simps kernel_object.split arch_kernel_obj.split])
  apply (rule corres_no_failI)
   apply (rule no_fail_pre, wp)
    apply simp
   apply (clarsimp simp: obj_at'_def ko_wp_at'_def typ_at'_def lookupAround2_known1 projectKOs)
   apply (case_tac ko, simp_all)[1]
   apply (rename_tac arch_kernel_object)
   apply (case_tac arch_kernel_object, simp_all add: projectKOs)[1]
   apply (simp add: objBits_simps archObjSize_def word_bits_def)
  apply (clarsimp simp: setObject_def in_monad split_def updateObject_default_def projectKOs)
  apply (simp add: in_magnitude_check objBits_simps archObjSize_def pageBits_def pteBits_def)
  apply (clarsimp simp: obj_at_def gets_the_def)
  apply (clarsimp simp: set_object_def bind_assoc exec_get exec_gets)
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
         apply (simp+)[3]
      apply clarsimp
      apply (frule (1) pspace_alignedD)
      apply (drule_tac p=x in pspace_alignedD, assumption)
      apply simp
      apply (drule mask_alignment_ugliness)
         apply (simp add: pt_bits_def pageBits_def)
        apply (simp add: pt_bits_def pageBits_def)
       apply clarsimp
       apply (drule test_bit_size)
       apply (clarsimp simp: word_size pt_bits_def pageBits_def)
       apply arith
      apply simp
     apply (simp split: if_split_asm)
    apply (simp split: if_split_asm)
   apply (simp add: other_obj_relation_def
               split: Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (rule conjI)
   apply (fastforce simp: sc_replies_relation_def sc_replies_of_scs_def map_project_def
                          scs_of_kh_def opt_map_def projectKO_opts_defs)
  apply (rule conjI)
   apply (clarsimp simp add: ghost_relation_def)
   apply (erule_tac x="p && ~~ mask pt_bits" in allE)+
   apply fastforce
  apply (simp add: map_to_ctes_upd_other)
  apply (simp add: fun_upd_def)
  apply (simp add: caps_of_state_after_update obj_at_def swp_cte_at_caps_of)
  done


lemma storePDE_corres [@lift_corres_args, corres]:
  "pde_relation_aligned (p >> 2) pde pde' \<Longrightarrow>
  corres dc (pde_at p and pspace_aligned) (pde_at' p) (store_pde p pde) (storePDE p pde')"
  apply (simp add: store_pde_def storePDE_def)
  apply (rule corres_symb_exec_l)
     apply (erule setObject_PD_corres[OF _ refl])
    apply (clarsimp simp: exs_valid_def get_pd_def get_object_def exec_gets bind_assoc
                          obj_at_def pde_at_def gets_the_def)
    apply (clarsimp simp: a_type_def return_def
                    split: Structures_A.kernel_object.splits arch_kernel_obj.splits if_split_asm)
   apply wp
   apply clarsimp
  apply (clarsimp simp: get_pd_def obj_at_def no_fail_def pde_at_def
                        get_object_def bind_assoc exec_gets gets_the_def)
  apply (clarsimp simp: a_type_def return_def
                  split: Structures_A.kernel_object.splits arch_kernel_obj.splits if_split_asm)
  done

lemma storePDE_corres':
  "pde_relation_aligned (p >> 2) pde pde' \<Longrightarrow>
  corres dc
     (pde_at p and pspace_aligned) (pspace_aligned' and pspace_distinct')
     (store_pde p pde) (storePDE p pde')"
  apply (rule stronger_corres_guard_imp, rule storePDE_corres)
   apply auto
  done

lemma storePTE_corres [@lift_corres_args, corres]:
  "pte_relation_aligned (p>>2) pte pte' \<Longrightarrow>
  corres dc (pte_at p and pspace_aligned) (pte_at' p) (store_pte p pte) (storePTE p pte')"
  apply (simp add: store_pte_def storePTE_def)
  apply (rule corres_symb_exec_l)
     apply (erule setObject_PT_corres[OF _ refl])
    apply (clarsimp simp: exs_valid_def get_pt_def get_object_def gets_the_def
                          exec_gets bind_assoc obj_at_def pte_at_def)
    apply (clarsimp simp: a_type_def return_def
                    split: Structures_A.kernel_object.splits arch_kernel_obj.splits if_split_asm)
   apply wp
   apply clarsimp
  apply (clarsimp simp: get_pt_def obj_at_def pte_at_def no_fail_def
                        get_object_def bind_assoc exec_gets gets_the_def)
  apply (clarsimp simp: a_type_def return_def
                  split: Structures_A.kernel_object.splits arch_kernel_obj.splits if_split_asm)
  done

lemma storePTE_corres':
  "pte_relation_aligned (p >> 2) pte pte' \<Longrightarrow>
  corres dc (pte_at p and pspace_aligned)
            (pspace_aligned' and pspace_distinct')
            (store_pte p pte) (storePTE p pte')"
  apply (rule stronger_corres_guard_imp, rule storePTE_corres)
   apply auto
  done

lemma lookupPDSlot_corres [simp]:
  "lookupPDSlot pd vptr = lookup_pd_slot pd vptr"
  by (simp add: lookupPDSlot_def lookup_pd_slot_def pageBits_def ptBits_def pdeBits_def)

defs checkPDAt_def:
  "checkPDAt pd \<equiv> stateAssert (page_directory_at' pd) []"

defs checkPTAt_def:
  "checkPTAt pt \<equiv> stateAssert (page_table_at' pt) []"

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
   apply (simp add:ptrFromPAddr_def ptBits_def pageBits_def pteBits_def)
  apply clarsimp
  apply (drule_tac x = "ucast y" in spec)
  apply (drule sym[where s = "pspace_dom (kheap s)"])
  apply (clarsimp simp:typ_at'_def ko_wp_at'_def)
  apply (subgoal_tac "(ptr + pptrBaseOffset + (y << 2)) \<in> dom (ksPSpace sa)")
   prefer 2
   apply (clarsimp simp: pspace_dom_def)
   apply (rule_tac x = "ptr + pptrBaseOffset" in bexI[where A = "dom (kheap s)"])
    apply (simp add:image_def)
    apply (rule_tac x = "ucast y" in exI)
    apply (simp add:ucast_ucast_len)
   apply fastforce
  apply (thin_tac "dom a = b" for a b)
  apply (frule(1) pspace_alignedD)
  apply (clarsimp simp:ucast_ucast_len
    split:if_splits)
  apply (drule pte_relation_must_pte)
  apply (drule(1) pspace_distinctD')
  apply (clarsimp simp:objBits_simps archObjSize_def word_bits_def pteBits_def)
  apply (rule is_aligned_weaken)
   apply (erule aligned_add_aligned)
    apply (rule is_aligned_shiftl_self)
   apply simp+
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
   apply (simp add: pdBits_def pageBits_def pdeBits_def)
  apply clarsimp
  apply (drule_tac x = "ucast y" in spec)
  apply (drule sym[where s = "pspace_dom (kheap s)"])
  apply (clarsimp simp:typ_at'_def ko_wp_at'_def)
  apply (subgoal_tac "(ptr + (y << 2)) \<in> dom (ksPSpace sa)")
   prefer 2
   apply (clarsimp simp: pspace_dom_def)
   apply (rule_tac x = "ptr" in bexI[where A = "dom (kheap s)"])
    apply (simp add: image_def)
    apply (rule_tac x = "ucast y" in exI)
    apply (simp add:ucast_ucast_len)
   apply fastforce
  apply (thin_tac "dom a = b" for a b)
  apply (frule(1) pspace_alignedD)
  apply (clarsimp simp:ucast_ucast_len split:if_splits)
  apply (drule pde_relation_must_pde)
  apply (drule(1) pspace_distinctD')
  apply (clarsimp simp:objBits_simps archObjSize_def word_bits_def pdeBits_def)
  apply (rule is_aligned_weaken)
   apply (erule aligned_add_aligned)
    apply (rule is_aligned_shiftl_self)
   apply simp+
  done

lemmas get_pde_wp_valid = hoare_add_post'[OF get_pde_valid get_pde_wp]

lemma page_table_at_lift:
  "\<forall>s s'. (s, s') \<in> state_relation \<longrightarrow> (ptrFromPAddr ptr) = ptr' \<longrightarrow>
  (pspace_aligned s \<and> valid_pde (ARM_A.PageTablePDE ptr x z) s) \<longrightarrow>
  pspace_distinct' s' \<longrightarrow> page_table_at' ptr' s'"
  by (fastforce intro!: page_table_at_state_relation)

lemmas checkPTAt_corres [corresK] =
  corres_stateAssert_implied_frame[OF page_table_at_lift, folded checkPTAt_def]


lemma lookupPTSlot_corres [@lift_corres_args, corres]:
  "corres (lfr \<oplus> (=))
          (pde_at (lookup_pd_slot pd vptr) and pspace_aligned and valid_vspace_objs
          and (\<exists>\<rhd> (lookup_pd_slot pd vptr && ~~ mask pd_bits)) and
          K (is_aligned pd pd_bits \<and> vptr < kernel_base
          \<and> ucast (lookup_pd_slot pd vptr && mask pd_bits >> 2) \<notin> kernel_mapping_slots))
          (pspace_aligned' and pspace_distinct')
          (lookup_pt_slot pd vptr) (lookupPTSlot pd vptr)"
  unfolding lookup_pt_slot_def lookupPTSlot_def lookupPTSlotFromPT_def
  apply (corresKsimp simp: pde_relation_aligned_def lookup_failure_map_def
                          ptBits_def pdeBits_def pageBits_def pteBits_def mask_def
                      wp: get_pde_wp_valid getPDE_wp)
  by (auto simp: lookup_failure_map_def obj_at_def)

declare in_set_zip_refl[simp]

crunches copyGlobalMappings
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"
  (wp: mapM_x_wp')
end

sublocale Arch < copyGlobalMappings: typ_at_all_props' "copyGlobalMappings newPD"
  by typ_at_props'

context begin interpretation Arch . (*FIXME: arch_split*)

lemma arch_cap_rights_update:
  "acap_relation c c' \<Longrightarrow>
   cap_relation (cap.ArchObjectCap (acap_rights_update (acap_rights c \<inter> msk) c))
                 (Arch.maskCapRights (rights_mask_map msk) c')"
  apply (cases c, simp_all add: ARM_H.maskCapRights_def
                                acap_rights_update_def Let_def isCap_simps)
  apply (simp add: maskVMRights_def vmrights_map_def rights_mask_map_def
                   validate_vm_rights_def vm_read_write_def vm_read_only_def
                   vm_kernel_only_def )
  done

lemma arch_deriveCap_inv:
  "\<lbrace>P\<rbrace> Arch.deriveCap arch_cap u \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp      add: ARM_H.deriveCap_def
                  cong: if_cong
             split del: if_split)
  apply (rule hoare_pre, wp undefined_valid)
  apply (cases u, simp_all add: isCap_defs)
  done

lemma arch_deriveCap_valid:
  "\<lbrace>valid_cap' (ArchObjectCap arch_cap)\<rbrace>
     Arch.deriveCap u arch_cap
   \<lbrace>\<lambda>rv. valid_cap' rv\<rbrace>,-"
  apply (simp      add: ARM_H.deriveCap_def
                  cong: if_cong
             split del: if_split)
  apply (rule hoare_pre, wp undefined_validE_R)
  apply (cases arch_cap, simp_all add: isCap_defs)
  apply (simp add: valid_cap'_def capAligned_def
                   capUntypedPtr_def ARM_H.capUntypedPtr_def)
  done

lemma arch_deriveCap_corres [corres]:
 "cap_relation (cap.ArchObjectCap c) (ArchObjectCap c') \<Longrightarrow>
  corres (ser \<oplus> (\<lambda>c c'. cap_relation c c'))
         \<top> \<top>
         (arch_derive_cap c)
         (Arch.deriveCap slot c')"
  unfolding arch_derive_cap_def ARM_H.deriveCap_def Let_def
  apply (cases c, simp_all add: isCap_simps split: option.splits split del: if_split)
      apply (clarify?, rule corres_noopE; wpsimp)+
  done

definition
  "vmattributes_map \<equiv> \<lambda>R. VMAttributes (PageCacheable \<in> R) (ParityEnabled \<in> R) (XNever \<in> R)"

definition
  mapping_map :: "ARM_A.pte \<times> word32 list + ARM_A.pde \<times> word32 list \<Rightarrow>
                  ARM_H.pte \<times> word32 list + ARM_H.pde \<times> word32 list \<Rightarrow> bool"
where
  "mapping_map \<equiv> pte_relation' \<otimes> (=) \<oplus> pde_relation' \<otimes> (=)"

lemma createMappingEntries_corres [corres]:
  "\<lbrakk> vm_rights' = vmrights_map vm_rights;
     attrib' = vmattributes_map attrib; base = base'; vptr = vptr'; pgsz = pgsz'; pd = pd' \<rbrakk>
  \<Longrightarrow> corres (ser \<oplus> mapping_map)
          (\<lambda>s. (pgsz = ARMSmallPage \<or> pgsz = ARMLargePage \<longrightarrow> pde_at (lookup_pd_slot pd vptr) s)
           \<and> (is_aligned pd pd_bits \<and> vmsz_aligned vptr pgsz \<and> vptr < kernel_base \<and> vm_rights \<in> valid_vm_rights)
           \<and> valid_vspace_objs s \<and> pspace_aligned s \<and> (\<exists>\<rhd> (lookup_pd_slot pd vptr && ~~ mask pd_bits)) s)
          (pspace_aligned' and pspace_distinct')
          (create_mapping_entries base vptr pgsz vm_rights attrib pd)
          (createMappingEntries base' vptr' pgsz' vm_rights' attrib' pd')"
  unfolding createMappingEntries_def mapping_map_def
  by (cases pgsz; corresKsimp simp: vmattributes_map_def less_kernel_base_mapping_slots
                                   largePagePTEOffsets_def
                                   largePagePTE_offsets_def
                                   superSectionPDEOffsets_def
                                   superSectionPDE_offsets_def
                                   pteBits_def pdeBits_def)

lemma pte_relation'_Invalid_inv [simp]:
  "pte_relation' x ARM_H.pte.InvalidPTE = (x = ARM_A.pte.InvalidPTE)"
  by (cases x) auto

definition
  "valid_slots' m \<equiv> case m of
    Inl (pte, xs) \<Rightarrow> \<lambda>s. valid_pte' pte s
  | Inr (pde, xs) \<Rightarrow> \<lambda>s. valid_pde' pde s"

lemma createMappingEntries_valid_slots' [wp]:
  "\<lbrace>valid_objs' and
    K (vmsz_aligned base sz \<and> vmsz_aligned vptr sz \<and> ptrFromPAddr base \<noteq> 0) \<rbrace>
  createMappingEntries base vptr sz vm_rights attrib pd
  \<lbrace>\<lambda>m. valid_slots' m\<rbrace>, -"
  apply (simp add: createMappingEntries_def)
  apply (rule hoare_pre)
   apply (wp|wpc|simp add: valid_slots'_def valid_mapping'_def)+
  apply (simp add: vmsz_aligned_def)
  apply auto
  done

lemma ensureSafeMapping_corres [corres]:
  "mapping_map m m' \<Longrightarrow>
  corres (ser \<oplus> dc) (valid_mapping_entries m)
                    (pspace_aligned' and pspace_distinct'
                    and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)))
                    (ensure_safe_mapping m) (ensureSafeMapping m')"
  unfolding mapping_map_def ensureSafeMapping_def
  apply (cases m; cases m'; simp;
         match premises in "(_ \<otimes> (=)) p p'" for p p' \<Rightarrow> \<open>cases "fst p"; cases "fst p'"\<close>; clarsimp)
        by (corresKsimp corresK: mapME_x_corresK_inv
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

lemma find_pd_for_asid_corres [corres]:
  "asid = asid' \<Longrightarrow> corres (lfr \<oplus> (=)) ((\<lambda>s. valid_arch_state s \<or> vspace_at_asid asid pd s)
                           and valid_vspace_objs and pspace_aligned
                           and K (0 < asid \<and> asid \<le> mask asidBits))
                       (pspace_aligned' and pspace_distinct' and no_0_obj')
                       (find_pd_for_asid asid) (findPDForASID asid')"
  apply (simp add: find_pd_for_asid_def findPDForASID_def liftME_def bindE_assoc)
  apply (corresKsimp simp: liftE_bindE assertE_assert mask_asid_low_bits_ucast_ucast
                          lookup_failure_map_def
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
       apply (simp add: arm_asid_table_related)
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
  subgoal for x ko
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
  apply (rule corres_guard_imp, rule find_pd_for_asid_corres)
   apply fastforce+
  done

lemma setObject_arch:
  assumes X: "\<And>p q n ko. \<lbrace>\<lambda>s. P (ksArchState s)\<rbrace> updateObject val p q n ko \<lbrace>\<lambda>rv s. P (ksArchState s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. P (ksArchState s)\<rbrace> setObject t val \<lbrace>\<lambda>rv s. P (ksArchState s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp X | simp)+
  done

lemma page_directory_pde_at_lookupI':
  "page_directory_at' pd s \<Longrightarrow> pde_at' (lookup_pd_slot pd vptr) s"
  apply (simp add: lookup_pd_slot_def Let_def)
  apply (erule page_directory_pde_atI')
  apply (rule vptr_shiftr_le_2p)
  done

lemma pt_bits_stuff:
  "pt_bits = ptBits"
  "ptBits < word_bits"
  "2 \<le> ptBits"
  by (simp add: pt_bits_def ptBits_def pageBits_def word_bits_def pteBits_def)+

lemma page_table_pte_at_lookupI':
  "page_table_at' pt s \<Longrightarrow> pte_at' (lookup_pt_slot_no_fail pt vptr) s"
  apply (simp add: lookup_pt_slot_no_fail_def)
  apply (erule page_table_pte_atI')
  apply (rule vptr_shiftr_le_2pt[simplified pt_bits_stuff])
  done

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
  apply (clarsimp simp: invs'_def valid_dom_schedule'_def)
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
