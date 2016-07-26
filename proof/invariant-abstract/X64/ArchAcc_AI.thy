(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(*
Lemmas on arch get/set object etc
*)

theory ArchAcc_AI
imports "../SubMonad_AI"
 "../../../lib/Crunch"
begin

  
(*FIXME: Move or remove *)

method spec for x :: "_ :: type" = (erule allE[of _ x])
method bspec for x :: "_ :: type" = (erule ballE[of _ _ x])
method prove for x :: "prop" = (rule revcut_rl[of "PROP x"])

context Arch begin global_naming X64


bundle unfold_objects = 
  obj_at_def[simp]
  kernel_object.splits[split]
  arch_kernel_obj.splits[split]
  
bundle unfold_objects_asm =
  obj_at_def[simp]
  kernel_object.split_asm[split]
  arch_kernel_obj.split_asm[split]  

definition
  "valid_asid asid s \<equiv> x64_asid_map (arch_state s) asid \<noteq> None"


lemma get_asid_pool_wp [wp]:
  "\<lbrace>\<lambda>s. \<forall>pool. ko_at (ArchObj (ASIDPool pool)) p s \<longrightarrow> Q pool s\<rbrace>
  get_asid_pool p
  \<lbrace>Q\<rbrace>"
  apply (simp add: get_asid_pool_def get_object_def)
   apply (wp|wpc)+
  apply (clarsimp simp: obj_at_def)
  done


lemma set_asid_pool_typ_at [wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> set_asid_pool ptr pool \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def get_object_def)
  apply wp
  including unfold_objects
  by clarsimp (simp add: a_type_def)


lemmas set_asid_pool_typ_ats [wp] = abs_typ_at_lifts [OF set_asid_pool_typ_at]

lemma get_pml4_wp [wp]:
  "\<lbrace>\<lambda>s. \<forall>pd. ko_at (ArchObj (PageMapL4 pd)) p s \<longrightarrow> Q pd s\<rbrace> get_pml4 p \<lbrace>Q\<rbrace>"
  apply (simp add: get_pml4_def get_object_def)
  apply (wp|wpc)+
  apply (clarsimp simp: obj_at_def)
  done


lemma get_pml4e_wp:
  "\<lbrace>\<lambda>s. \<forall>pd. ko_at (ArchObj (PageMapL4 pd)) (p && ~~ mask pml4_bits) s \<longrightarrow>
        Q (pd (ucast (p && mask pml4_bits >> word_size_bits))) s\<rbrace>
  get_pml4e p
  \<lbrace>Q\<rbrace>"  
  by (simp add: get_pml4e_def bit_simps) wp


lemma get_pml4e_inv [wp]: "\<lbrace>P\<rbrace> get_pml4e p \<lbrace>\<lambda>_. P\<rbrace>"
  by (wp get_pml4e_wp) simp

lemma get_pdpt_wp [wp]:
  "\<lbrace>\<lambda>s. \<forall>pd. ko_at (ArchObj (PDPointerTable pd)) p s \<longrightarrow> Q pd s\<rbrace> get_pdpt p \<lbrace>Q\<rbrace>"
  apply (simp add: get_pdpt_def get_object_def)
  apply (wp|wpc)+
  apply (clarsimp simp: obj_at_def)
  done


lemma get_pdpte_wp:
  "\<lbrace>\<lambda>s. \<forall>pd. ko_at (ArchObj (PDPointerTable pd)) (p && ~~ mask pdpt_bits) s \<longrightarrow>
        Q (pd (ucast (p && mask pdpt_bits >> word_size_bits))) s\<rbrace>
  get_pdpte p
  \<lbrace>Q\<rbrace>"  
  by (simp add: get_pdpte_def bit_simps) wp


lemma get_pdpte_inv [wp]: "\<lbrace>P\<rbrace> get_pdpte p \<lbrace>\<lambda>_. P\<rbrace>"
  by (wp get_pdpte_wp) simp


lemma get_pd_wp [wp]:
  "\<lbrace>\<lambda>s. \<forall>pd. ko_at (ArchObj (PageDirectory pd)) p s \<longrightarrow> Q pd s\<rbrace> get_pd p \<lbrace>Q\<rbrace>"
  apply (simp add: get_pd_def get_object_def)
  apply (wp|wpc)+
  apply (clarsimp simp: obj_at_def)
  done


lemma get_pde_wp:
  "\<lbrace>\<lambda>s. \<forall>pd. ko_at (ArchObj (PageDirectory pd)) (p && ~~ mask pd_bits) s \<longrightarrow>
        Q (pd (ucast (p && mask pd_bits >> word_size_bits))) s\<rbrace>
  get_pde p
  \<lbrace>Q\<rbrace>"  
  by (simp add: get_pde_def bit_simps) wp


lemma get_pde_inv [wp]: "\<lbrace>P\<rbrace> get_pde p \<lbrace>\<lambda>_. P\<rbrace>"
  by (wp get_pde_wp) simp

bundle pagebits = 
  pd_bits_def[simp] pd_shift_bits_def [simp]
  pt_bits_def[simp] pt_shift_bits_def[simp]
  pdpt_bits_def[simp] pdpt_shift_bits_def[simp]
  pml4_bits_def[simp] pml4_shift_bits_def[simp]
  table_size_def[simp] ptTranslationBits_def[simp]
  pageBits_def[simp] mask_lower_twice[simp]
  word_bool_alg.conj_assoc[symmetric,simp] obj_at_def[simp]
  pde.splits[split] pdpte.splits[split] pml4e.splits[split]
  pte.splits[split]
  
(* FIXME x64:
lemma get_master_pde_wp:
  "\<lbrace>\<lambda>s. \<forall>pd. ko_at (ArchObj (PageDirectory pd)) (p && ~~ mask pd_bits) s
        \<longrightarrow> Q (case (pd (ucast (p && ~~ mask 6 && mask pd_bits >> 2))) of
               SuperSectionPDE x xa xb \<Rightarrow> pd (ucast (p && ~~ mask 6 && mask pd_bits >> 2))
             | _ \<Rightarrow> pd (ucast (p && mask pd_bits >> 2))) s\<rbrace>
   get_master_pde p
   \<lbrace>Q\<rbrace>"
  apply (simp add: get_master_pde_def)
  apply (wp get_pde_wp | wpc)+
  including pagebits
  sorry
*)
 
lemma store_pml4e_typ_at [wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> store_pml4e ptr pde \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  apply (simp add: store_pml4e_def set_pml4_def set_object_def get_object_def)
  apply wp
  apply (clarsimp simp: obj_at_def a_type_def)
  done

lemma store_pdpte_typ_at [wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> store_pdpte ptr pde \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  apply (simp add: store_pdpte_def set_pdpt_def set_object_def get_object_def)
  apply wp
  apply (clarsimp simp: obj_at_def a_type_def)
  done

lemma store_pde_typ_at [wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> store_pde ptr pde \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  apply (simp add: store_pde_def set_pd_def set_object_def get_object_def)
  apply wp
  apply (clarsimp simp: obj_at_def a_type_def)
  done

lemmas store_pml4e_typ_ats [wp] = abs_typ_at_lifts [OF store_pml4e_typ_at]
lemmas store_pdpte_typ_ats [wp] = abs_typ_at_lifts [OF store_pdpte_typ_at]
lemmas store_pde_typ_ats [wp] = abs_typ_at_lifts [OF store_pde_typ_at]


lemma get_pt_wp [wp]:
  "\<lbrace>\<lambda>s. \<forall>pt. ko_at (ArchObj (PageTable pt)) p s \<longrightarrow> Q pt s\<rbrace> get_pt p \<lbrace>Q\<rbrace>"
  apply (simp add: get_pt_def get_object_def)
  apply (wp|wpc)+
  apply (clarsimp simp: obj_at_def)
  done


lemma get_pte_wp:
  "\<lbrace>\<lambda>s. \<forall>pt. ko_at (ArchObj (PageTable pt)) (p && ~~mask pt_bits) s \<longrightarrow>
        Q (pt (ucast (p && mask pt_bits >> word_size_bits))) s\<rbrace>
  get_pte p
  \<lbrace>Q\<rbrace>"
  by (simp add: get_pte_def) wp


lemma get_pte_inv [wp]:
  "\<lbrace>P\<rbrace> get_pte p \<lbrace>\<lambda>_. P\<rbrace>"
  by (wp get_pte_wp) simp

lemma store_pte_typ_at:
    "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> store_pte ptr pte \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  apply (simp add: store_pte_def set_pt_def set_object_def get_object_def)
  apply wp
  apply (clarsimp simp: obj_at_def a_type_def)
  done


lemmas store_pte_typ_ats [wp] = abs_typ_at_lifts [OF store_pte_typ_at]

lemma lookup_pdpt_slot_inv:
  "\<lbrace>P\<rbrace> lookup_pdpt_slot pdpt vptr \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add: lookup_pdpt_slot_def)
  apply (wp get_pml4e_wp | wpc)+
  apply clarsimp
  done

thm lookup_pdpt_slot_inv[THEN valid_validE_R]
  
lemma lookup_pd_slot_inv:
  "\<lbrace>P\<rbrace> lookup_pd_slot pd vptr \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add: lookup_pd_slot_def)
  apply (rule hoare_pre)
  apply (wp get_pdpte_wp lookup_pdpt_slot_inv hoare_vcg_all_lift_R hoare_drop_imps| wpc)+
  apply clarsimp
  done

lemma lookup_pt_slot_inv:
  "\<lbrace>P\<rbrace> lookup_pt_slot pd vptr \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add: lookup_pt_slot_def)
  apply (rule hoare_pre)
  apply (wp get_pde_wp lookup_pd_slot_inv hoare_vcg_all_lift_R hoare_drop_imps| wpc)+
  apply clarsimp
  done

lemma lookup_pdpt_slot_inv_any:
  "\<lbrace>\<lambda>s. \<forall>x. Q x s\<rbrace> lookup_pdpt_slot pd vptr \<lbrace>Q\<rbrace>,-"
  "\<lbrace>E\<rbrace> lookup_pdpt_slot pd vptr -, \<lbrace>\<lambda>ft. E\<rbrace>"
  apply (simp_all add: lookup_pdpt_slot_def)
  apply (wp get_pml4e_wp | simp | wpc)+
  done

lemma lookup_pd_slot_inv_any:
  "\<lbrace>\<lambda>s. \<forall>x. Q x s\<rbrace> lookup_pd_slot pd vptr \<lbrace>Q\<rbrace>,-"
  "\<lbrace>E\<rbrace> lookup_pd_slot pd vptr -, \<lbrace>\<lambda>ft. E\<rbrace>"
  apply (simp_all add: lookup_pd_slot_def)
  by (rule hoare_pre, 
            (wp get_pdpte_wp lookup_pdpt_slot_inv_any 
                hoare_drop_imps hoare_vcg_all_lift 
           | simp | wpc)+)+
  
lemma lookup_pt_slot_inv_any:
  "\<lbrace>\<lambda>s. \<forall>x. Q x s\<rbrace> lookup_pt_slot pd vptr \<lbrace>Q\<rbrace>,-"
  "\<lbrace>E\<rbrace> lookup_pt_slot pd vptr -, \<lbrace>\<lambda>ft. E\<rbrace>"
  apply (simp_all add: lookup_pt_slot_def)
  by (rule hoare_pre, 
            (wp get_pde_wp lookup_pd_slot_inv_any 
                hoare_drop_imps hoare_vcg_all_lift 
           | simp | wpc)+)+

crunch cte_wp_at[wp]: set_irq_state "\<lambda>s. P (cte_wp_at P' p s)"

crunch inv[wp]: get_irq_slot "P"

lemma set_pt_cte_wp_at:
  "\<lbrace>\<lambda>s. P (cte_wp_at P' p s)\<rbrace>
     set_pt ptr val
   \<lbrace>\<lambda>rv s. P (cte_wp_at P' p s)\<rbrace>"
  apply (simp add: set_pt_def set_object_def get_object_def)
  apply wp
  including unfold_objects_asm
  by (clarsimp elim!: rsubst[where P=P]
               simp: cte_wp_at_after_update)

lemma set_pml4_cte_wp_at:
  "\<lbrace>\<lambda>s. P (cte_wp_at P' p s)\<rbrace>
     set_pml4 ptr val
   \<lbrace>\<lambda>rv s. P (cte_wp_at P' p s)\<rbrace>"
  apply (simp add: set_pml4_def set_object_def get_object_def)
  apply wp
  including unfold_objects_asm
  by (clarsimp elim!: rsubst[where P=P]
             simp: cte_wp_at_after_update)
  
lemma set_pdpt_cte_wp_at:
  "\<lbrace>\<lambda>s. P (cte_wp_at P' p s)\<rbrace>
     set_pdpt ptr val
   \<lbrace>\<lambda>rv s. P (cte_wp_at P' p s)\<rbrace>"
  apply (simp add: set_pdpt_def set_object_def get_object_def)
  apply wp
  including unfold_objects_asm
  by (clarsimp elim!: rsubst[where P=P]
             simp: cte_wp_at_after_update)
  
lemma set_pd_cte_wp_at:
  "\<lbrace>\<lambda>s. P (cte_wp_at P' p s)\<rbrace>
     set_pd ptr val
   \<lbrace>\<lambda>rv s. P (cte_wp_at P' p s)\<rbrace>"
  apply (simp add: set_pd_def set_object_def get_object_def)
  apply wp
  including unfold_objects_asm
  by (clarsimp elim!: rsubst[where P=P]
             simp: cte_wp_at_after_update)


lemma set_asid_pool_cte_wp_at:
  "\<lbrace>\<lambda>s. P (cte_wp_at P' p s)\<rbrace>
     set_asid_pool ptr val
   \<lbrace>\<lambda>rv s. P (cte_wp_at P' p s)\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def get_object_def)
  apply wp
  including unfold_objects_asm
  by (clarsimp elim!: rsubst[where P=P]
             simp: cte_wp_at_after_update)

lemma set_pt_pred_tcb_at[wp]:
  "\<lbrace>pred_tcb_at proj P t\<rbrace> set_pt ptr val \<lbrace>\<lambda>_. pred_tcb_at proj P t\<rbrace>"
  apply (simp add: set_pt_def set_object_def)
  apply wp
  apply (rule hoare_strengthen_post [OF get_object_sp])
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  done


lemma set_pd_pred_tcb_at[wp]:
  "\<lbrace>pred_tcb_at proj P t\<rbrace> set_pd ptr val \<lbrace>\<lambda>_. pred_tcb_at proj P t\<rbrace>"
  apply (simp add: set_pd_def set_object_def)
  apply wp
  apply (rule hoare_strengthen_post [OF get_object_sp])
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  done

lemma set_pdpt_pred_tcb_at[wp]:
  "\<lbrace>pred_tcb_at proj P t\<rbrace> set_pdpt ptr val \<lbrace>\<lambda>_. pred_tcb_at proj P t\<rbrace>"
  apply (simp add: set_pdpt_def set_object_def)
  apply wp
  apply (rule hoare_strengthen_post [OF get_object_sp])
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  done
  
lemma set_pml4_pred_tcb_at[wp]:
  "\<lbrace>pred_tcb_at proj P t\<rbrace> set_pml4 ptr val \<lbrace>\<lambda>_. pred_tcb_at proj P t\<rbrace>"
  apply (simp add: set_pml4_def set_object_def)
  apply wp
  apply (rule hoare_strengthen_post [OF get_object_sp])
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  done
  
lemma set_asid_pool_pred_tcb_at[wp]:
  "\<lbrace>pred_tcb_at proj P t\<rbrace> set_asid_pool ptr val \<lbrace>\<lambda>_. pred_tcb_at proj P t\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def)
  apply wp
  apply (rule hoare_strengthen_post [OF get_object_sp])
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  done

lemmas word_simps = 
  word_size word_ops_nth_size nth_ucast nth_shiftr nth_shiftl
  pd_bits_def pageBits_def
  
lemma SucSucSucMinus: "3 \<le> n \<Longrightarrow> Suc (Suc (Suc (n - 3))) = n" by arith

(*FIXME x64:
lemma mask_pd_bits_inner_beauty:
  "is_aligned p 3 \<Longrightarrow>
  (p && ~~ mask pd_shift_bits) + (ucast ((ucast (p && mask pd_shift_bits >> 3))::12 word) << 3) = (p::word64)"
  apply (simp add: is_aligned_nth)
  apply (subst word_plus_and_or_coroll; rule word_eqI)
  subgoal
    by (clarsimp simp: word_simps)
  subgoal for n
    apply (clarsimp simp: word_simps)
    apply (rule iffI, (erule disjE;clarsimp))
    subgoal by (clarsimp simp: SucSucSucMinus)
    apply (spec n)
    apply (clarsimp simp: SucSucMinus)
    by arith
  done
*)

(* FIXME x64:
lemma more_pd_inner_beauty:
  fixes x :: "12 word"
  fixes p :: word32
  assumes x: "x \<noteq> ucast (p && mask pd_bits >> 2)"
  shows "(p && ~~ mask pd_bits) + (ucast x << 2) = p \<Longrightarrow> False"
  apply (subst (asm) word_plus_and_or_coroll)
   apply (clarsimp simp: word_simps bang_eq)
  subgoal for n
    apply (drule test_bit_size)
    apply (clarsimp simp: word_simps)
    by arith
  apply (insert x)
  apply (erule notE)
  apply (rule word_eqI)
  subgoal for n
    apply (clarsimp simp: word_simps bang_eq)
    apply (spec "n+2")
    by (clarsimp simp: word_ops_nth_size word_size)
  done
*)

lemma mask_alignment_ugliness:
  "\<lbrakk> x \<noteq> x + z && ~~ mask m;
     is_aligned (x + z && ~~ mask m) m;
     is_aligned x m;
     \<forall>n \<ge> m. \<not>z !! n\<rbrakk>
  \<Longrightarrow> False"
  apply (erule notE)
  apply (rule word_eqI)
  apply (clarsimp simp: is_aligned_nth word_ops_nth_size word_size pd_bits_def pageBits_def)
  apply (subst word_plus_and_or_coroll)
   apply (rule word_eqI)
   apply (clarsimp simp: word_size)
   
   subgoal for \<dots> na
    apply (spec na)+
    by simp
  by auto

(* FIXME x64:
lemma mask_pt_bits_inner_beauty:
  "is_aligned p 3 \<Longrightarrow>
  (p && ~~ mask pt_shift_bits) + (ucast ((ucast (p && mask pt_shift_bits >> 3))::word8) << 3) = (p::word64)"
  apply (simp add: is_aligned_nth)
  apply (subst word_plus_and_or_coroll; rule word_eqI)
  subgoal by (clarsimp simp: word_simps)
  apply (clarsimp simp: word_simps)
  subgoal for n
   apply (rule iffI)
    apply (erule disjE;clarsimp)
    subgoal by (prove "Suc (Suc (n - 2)) = n") simp+
   apply clarsimp
  apply (rule context_conjI)
   apply (rule leI)
   subgoal by clarsimp
   apply (prove "Suc (Suc (n - 2)) = n") subgoal by arith
   by (simp add: pt_bits_def pageBits_def)
  done
*)

(*FIXME x64:
lemma more_pt_inner_beauty:
  fixes x :: "word8"
  fixes p :: word32
  assumes x: "x \<noteq> ucast (p && mask pt_bits >> 2)"
  shows "(p && ~~ mask pt_bits) + (ucast x << 2) = p \<Longrightarrow> False"
  apply (subst (asm) word_plus_and_or_coroll)
   apply (clarsimp simp: word_size word_ops_nth_size nth_ucast
                         nth_shiftl bang_eq)
   apply (drule test_bit_size)
   apply (clarsimp simp: word_size pt_bits_def pageBits_def)
   apply arith
   apply (rule x[THEN notE])
  apply (rule word_eqI)
  subgoal for n
    apply (clarsimp simp: bang_eq word_simps)
    apply (spec "n+2")
    apply (clarsimp simp: word_ops_nth_size word_size)
    by (clarsimp simp: pt_bits_def pageBits_def)
  done
*)

lemma set_pml4_aligned [wp]:
  "\<lbrace>pspace_aligned\<rbrace> set_pml4 base pd \<lbrace>\<lambda>_. pspace_aligned\<rbrace>"
  apply (simp add: set_pml4_def)
  apply (wp set_object_aligned get_object_wp)
  including unfold_objects_asm
  by (clarsimp simp: a_type_def)

lemma set_pdpt_aligned [wp]:
  "\<lbrace>pspace_aligned\<rbrace> set_pdpt base pd \<lbrace>\<lambda>_. pspace_aligned\<rbrace>"
  apply (simp add: set_pdpt_def)
  apply (wp set_object_aligned get_object_wp)
  including unfold_objects_asm
  by (clarsimp simp: a_type_def)

lemma set_pd_aligned [wp]:
  "\<lbrace>pspace_aligned\<rbrace> set_pd base pd \<lbrace>\<lambda>_. pspace_aligned\<rbrace>"
  apply (simp add: set_pd_def)
  apply (wp set_object_aligned get_object_wp)
  including unfold_objects_asm
  by (clarsimp simp: a_type_def)


crunch aligned [wp]: store_pde pspace_aligned
  (wp: hoare_drop_imps)


lemmas undefined_validE_R = hoare_FalseE_R[where f=undefined]


lemma arch_derive_cap_valid_cap:
  "\<lbrace>valid_cap (cap.ArchObjectCap arch_cap)\<rbrace>
  arch_derive_cap arch_cap
  \<lbrace>valid_cap \<circ> cap.ArchObjectCap\<rbrace>, -"
  apply(simp add: arch_derive_cap_def)
  apply(cases arch_cap, simp_all add: arch_derive_cap_def o_def)
      apply(rule hoare_pre, wpc?, wp,
            clarsimp simp add: cap_aligned_def valid_cap_def split: option.splits)+
  done


lemma arch_derive_cap_inv:
  "\<lbrace>P\<rbrace> arch_derive_cap arch_cap \<lbrace>\<lambda>rv. P\<rbrace>"
  apply(simp add: arch_derive_cap_def, cases arch_cap, simp_all)
      apply(rule hoare_pre, wpc?, wp, simp)+
  done

(* FIXME x64: *)
definition
  "valid_mapping_entries m \<equiv> case m of
    (VMPTE (InvalidPTE), _) \<Rightarrow> \<top>
  | (VMPTE (SmallPagePTE _ _ _), p) \<Rightarrow> pte_at p
  | (VMPDE (InvalidPDE), _) \<Rightarrow> \<top>
  | (VMPDE (PageTablePDE _ _ _), _) \<Rightarrow> \<bottom>
  | (VMPDE (LargePagePDE _ _ _), p) \<Rightarrow> pde_at p
  | (VMPDPTE (InvalidPDPTE), _) \<Rightarrow> \<top>
  | (VMPDPTE (HugePagePDPTE _ _ _), p) \<Rightarrow> pdpte_at p
  | (VMPDPTE (PageDirectoryPDPTE _ _ _), _) \<Rightarrow> \<bottom>"

definition "invalid_pte_at p \<equiv> obj_at (\<lambda>ko. \<exists>pt. ko = (ArchObj (PageTable pt))
  \<and> pt (ucast (p && mask pt_bits) >> word_size_bits) = pte.InvalidPTE) (p && ~~ mask pt_bits)"

definition "invalid_pde_at p \<equiv> obj_at (\<lambda>ko. \<exists>pd. ko = (ArchObj (PageDirectory pd))
  \<and> pd (ucast (p && mask pd_bits) >> word_size_bits) = pde.InvalidPDE) (p && ~~ mask pd_bits)"

definition "invalid_pdpte_at p \<equiv> obj_at (\<lambda>ko. \<exists>pd. ko = (ArchObj (PDPointerTable pd))
  \<and> pd (ucast (p && mask pdpt_bits) >> word_size_bits) = pdpte.InvalidPDPTE) (p && ~~ mask pdpt_bits)"
  
definition "invalid_pml4e_at p \<equiv> obj_at (\<lambda>ko. \<exists>pd. ko = (ArchObj (PageMapL4 pd))
  \<and> pd (ucast (p && mask pml4_bits) >> word_size_bits) = pml4e.InvalidPML4E) (p && ~~ mask pml4_bits)"
  
(* FIXME x64: check
   Note that this doesnt need kernel_mapping_slots shenanigans because
   PML4's don't have pages in them *)
definition
  "valid_slots m \<equiv> case m of
    (VMPTE pte, p) \<Rightarrow>
      \<lambda>s. (\<exists>\<rhd> (p && ~~ mask pt_bits) and pte_at p) s \<and>
          wellformed_pte pte \<and> valid_pte pte s
  | (VMPDE pde, p) \<Rightarrow>
      \<lambda>s. (\<exists>\<rhd> (p && ~~ mask pd_bits) and pde_at p) s \<and>
          wellformed_pde pde \<and> valid_pde pde s
  | (VMPDPTE pdpte, p) \<Rightarrow>
      \<lambda>s. (\<exists>\<rhd> (p && ~~ mask pdpt_bits) and pdpte_at p) s \<and>
          wellformed_pdpte pdpte \<and> valid_pdpte pdpte s"

lemma ucast_mask_asid_low_bits [simp]:
  "ucast ((asid::word64) && mask asid_low_bits) = (ucast asid :: 9 word)"
  apply (rule word_eqI)
  apply (simp add: word_size nth_ucast asid_low_bits_def)
  done


lemma ucast_ucast_asid_high_bits [simp]:
  "ucast (ucast (asid_high_bits_of asid)::word64) = asid_high_bits_of asid"
  apply (rule word_eqI)
  apply (simp add: word_size nth_ucast asid_low_bits_def)
  done


lemma mask_asid_low_bits_ucast_ucast:
  "((asid::word64) && mask asid_low_bits) = ucast (ucast asid :: 9 word)"
  apply (rule word_eqI)
  apply (simp add: word_size nth_ucast asid_low_bits_def)
  done



lemma set_asid_pool_cur [wp]:
  "\<lbrace>\<lambda>s. P (cur_thread s)\<rbrace> set_asid_pool p a \<lbrace>\<lambda>_ s. P (cur_thread s)\<rbrace>"
  unfolding set_asid_pool_def by (wp get_object_wp) simp


lemma set_asid_pool_cur_tcb [wp]:
  "\<lbrace>\<lambda>s. cur_tcb s\<rbrace> set_asid_pool p a \<lbrace>\<lambda>_ s. cur_tcb s\<rbrace>"
  unfolding cur_tcb_def
  by (rule hoare_lift_Pf [where f=cur_thread]) wp


crunch arch [wp]: set_asid_pool "\<lambda>s. P (arch_state s)"
  (wp: get_object_wp)


lemma set_asid_pool_valid_arch [wp]:
  "\<lbrace>valid_arch_state\<rbrace> set_asid_pool p a \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  by (rule valid_arch_state_lift) (wp set_asid_pool_typ_at)


lemma set_asid_pool_valid_objs [wp]:
  "\<lbrace>valid_objs\<rbrace> set_asid_pool p a \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wp set_object_valid_objs get_object_wp)
  including unfold_objects
  by (clarsimp simp: a_type_def valid_obj_def wellformed_arch_obj_def)


lemma pml4_shifting:
  "is_aligned (pm::word64) pml4_bits \<Longrightarrow> pm + (get_pml4_index vptr << word_size_bits) && ~~ mask pml4_bits = pm"
  apply (rule word_eqI)
  apply (subst word_plus_and_or_coroll)
   apply (rule word_eqI)
  subgoal for \<dots> na
   apply (clarsimp simp: table_bits_simps get_pml4_index_def bit_simps)
   by (clarsimp simp: word_size nth_shiftr nth_shiftl is_aligned_nth)
  subgoal for n
    apply (clarsimp simp: bit_simps get_pml4_index_def)
    apply (clarsimp simp: word_size nth_shiftr nth_shiftl is_aligned_nth word_ops_nth_size
                          bit_simps linorder_not_less)
    apply (rule iffI)
     apply clarsimp
     apply (drule test_bit_size)+
     apply (simp add: word_size)
    apply clarsimp
    apply (spec n)
    by simp
  done


lemma pml4_shifting_dual:
  "is_aligned (pm::word64) pml4_bits \<Longrightarrow> 
       pm + (get_pml4_index vptr << word_size_bits) && mask pml4_bits 
           = get_pml4_index vptr << word_size_bits"
  apply (simp add: bit_simps)
  apply (subst word_plus_and_or_coroll)
   apply (rule word_eqI)
   subgoal for n
     by (clarsimp simp: word_size nth_shiftr nth_shiftl is_aligned_nth 
                        bit_simps get_pml4_index_def)
  apply (rule word_eqI)
  apply (clarsimp simp: word_size nth_shiftr nth_shiftl is_aligned_nth word_ops_nth_size
                        bit_simps get_pml4_index_def linorder_not_less)
  apply (rule iffI)
   apply clarsimp
  apply clarsimp
  apply (drule test_bit_size)+
  apply (simp add: word_size)
  done

lemma pml4_shifting_at:
  "\<lbrakk> page_map_l4_at pm s; pspace_aligned s \<rbrakk> \<Longrightarrow>
  pm + (get_pml4_index vptr << word_size_bits) && ~~ mask pml4_bits = pm"
  apply (rule pml4_shifting)
  apply (clarsimp simp: pspace_aligned_def obj_at_def table_bits_simps )
  apply (drule bspec, blast)
  including unfold_objects
  by (clarsimp simp: a_type_def obj_bits.simps bit_simps)


lemma kernel_mapping_slots_empty_pml4eI:
  "\<lbrakk>equal_kernel_mappings s; valid_global_objs s; valid_arch_state s;
    kheap s p = Some (ArchObj (PageMapL4 pm)); x \<in> kernel_mapping_slots\<rbrakk> \<Longrightarrow>
   (\<forall>r. pml4e_ref (pm x) = Some r \<longrightarrow> r \<in> set (x64_global_pdpts (arch_state s)))"
  apply (clarsimp simp: invs_def valid_state_def equal_kernel_mappings_def valid_global_objs_def)
  apply (erule_tac x=p in allE, erule_tac x="x64_global_pml4 (arch_state s)" in allE)
  including unfold_objects
  by (clarsimp simp: empty_table_def valid_arch_state_def a_type_def)


lemma invs_valid_global_pts:
  "invs s \<Longrightarrow> valid_global_pts s"
  by (clarsimp simp: invs_def valid_state_def valid_arch_state_def)

lemma is_aligned_pt:
  "page_table_at pt s \<Longrightarrow> pspace_aligned s
    \<Longrightarrow> is_aligned pt pt_bits"
  apply (clarsimp simp: obj_at_def)
  apply (drule(1) pspace_alignedD)
  apply (simp add: pt_bits_def pageBits_def)
  done

lemma is_aligned_pd:
  "page_directory_at pd s \<Longrightarrow> pspace_aligned s
    \<Longrightarrow> is_aligned pd pd_bits"
  apply (clarsimp simp: obj_at_def)
  apply (drule(1) pspace_alignedD)
  apply (simp add: pd_bits_def)
  done
  
lemma is_aligned_pdpt:
  "pd_pointer_table_at pdpt s \<Longrightarrow> pspace_aligned s
    \<Longrightarrow> is_aligned pdpt pdpt_bits"
  apply (clarsimp simp: obj_at_def)
  apply (drule(1) pspace_alignedD)
  apply (simp add: pdpt_bits_def)
  done
  
lemma is_aligned_global_pt:
  "\<lbrakk>x \<in> set (x64_global_pts (arch_state s)); pspace_aligned s; valid_arch_state s\<rbrakk>
   \<Longrightarrow> is_aligned x pt_bits"
  by (metis valid_arch_state_def valid_global_pts_def
            is_aligned_pt)
  
lemma is_aligned_global_pd:
  "\<lbrakk>x \<in> set (x64_global_pds (arch_state s)); pspace_aligned s; valid_arch_state s\<rbrakk>
   \<Longrightarrow> is_aligned x pd_bits"
  by (metis valid_arch_state_def valid_global_pds_def
            is_aligned_pd)
  
lemma is_aligned_global_pdpt:
  "\<lbrakk>x \<in> set (x64_global_pdpts (arch_state s)); pspace_aligned s; valid_arch_state s\<rbrakk>
   \<Longrightarrow> is_aligned x pdpt_bits"
  by (metis valid_arch_state_def valid_global_pdpts_def
            is_aligned_pdpt)

lemma page_table_pte_at_diffE:
  "\<lbrakk> page_table_at p s; q - p = x << word_size_bits;
    x < 2^(pt_bits - word_size_bits); pspace_aligned s \<rbrakk> \<Longrightarrow> pte_at q s"
  apply (clarsimp simp: diff_eq_eq add.commute)
  including pagebits
  apply (erule page_table_pte_atI; simp add: word_size_bits_def)
  done

lemma lookup_pdpt_slot_pdpte [wp]:
  "\<lbrace>pspace_aligned and valid_arch_objs and valid_arch_state
   and equal_kernel_mappings and valid_global_objs
   and \<exists>\<rhd> pd and page_map_l4_at pd\<rbrace>
  lookup_pdpt_slot pd vptr \<lbrace>pdpte_at\<rbrace>,-"
  apply (simp add: lookup_pdpt_slot_def)
  apply (wp get_pml4e_wp|wpc)+
  apply (clarsimp simp: lookup_pml4_slot_def Let_def)
  apply (simp add: pml4_shifting_at)
  apply (drule (2) valid_arch_objsD)
  apply clarsimp
  apply (bspec "ucast (pd + (get_pml4_index vptr << word_size_bits) && mask pml4_bits >> word_size_bits)")
   apply (clarsimp)
   apply (erule pd_pointer_table_pdpte_atI, simp_all)
   apply (simp add: get_pdpt_index_def bit_simps mask_def)
   apply (rule order_le_less_trans, rule word_and_le1, simp)
  apply (frule kernel_mapping_slots_empty_pml4eI)
    apply (simp add: obj_at_def)+
  apply (clarsimp simp: pml4e_ref_def)
  apply (rule pd_pointer_table_pdpte_atI, simp_all)
   apply (simp add: valid_arch_state_def valid_global_pdpts_def)
  apply (simp add: get_pdpt_index_def bit_simps mask_def)
  apply (rule order_le_less_trans, rule word_and_le1, simp)
  done
  
(* FIXME x64: we want this lemma, but need to figure out
              how to pull vs_refs down to the pd level *)
lemma lookup_pd_slot_pde [wp]:
  "\<lbrace>pspace_aligned and valid_arch_objs and valid_arch_state
   and equal_kernel_mappings and valid_global_objs
   and \<exists>\<rhd> pm and page_map_l4_at pm\<rbrace>
  lookup_pd_slot pm vptr \<lbrace>pde_at\<rbrace>,-"
  apply (simp add: lookup_pd_slot_def)
  apply (rule hoare_pre)
   apply (wp get_pdpte_wp hoare_vcg_all_lift_R lookup_pdpt_slot_inv_any |wpc)+
  apply (clarsimp simp: Let_def)
  (*
  apply (drule (2) valid_arch_objsD)
  apply clarsimp
  apply (bspec "ucast (pm + (vptr >> 20 << 2) && mask pd_bits >> 2)")
   apply clarsimp
   apply (erule page_table_pte_atI, simp_all)
   apply (simp add: pt_bits_def pageBits_def)
   apply (rule order_le_less_trans, rule word_and_le1, simp)
  apply (frule kernel_mapping_slots_empty_pdeI)
    apply (simp add: obj_at_def)+
  apply (clarsimp simp: pde_ref_def)
  apply (rule page_table_pte_atI, simp_all)
   apply (simp add: valid_arch_state_def valid_global_pts_def)
  apply (simp add: pt_bits_def pageBits_def)
  apply (rule order_le_less_trans, rule word_and_le1, simp)
  done*)
  sorry
  
(* FIXME x64: we want this lemma, but need to figure out
              how to pull vs_refs down to the pt level *)
lemma lookup_pt_slot_pte [wp]:
  "\<lbrace>pspace_aligned and valid_arch_objs and valid_arch_state
   and equal_kernel_mappings and valid_global_objs
   and \<exists>\<rhd> pd and page_map_l4_at pd\<rbrace>
  lookup_pt_slot pd vptr \<lbrace>pte_at\<rbrace>,-"
  apply (simp add: lookup_pt_slot_def)
  apply (rule hoare_pre)
   apply (wp get_pde_wp lookup_pd_slot_inv_any hoare_vcg_all_lift_R |wpc)+
  apply (clarsimp simp: lookup_pd_slot_def Let_def)
(*
  apply (simp add: pd_shifting_at)
  apply (drule (2) valid_arch_objsD)
  apply clarsimp
  apply (bspec "ucast (pd + (vptr >> 20 << 2) && mask pd_bits >> 2)")
   apply clarsimp
   apply (erule page_table_pte_atI, simp_all)
   apply (simp add: pt_bits_def pageBits_def)
   apply (rule order_le_less_trans, rule word_and_le1, simp)
  apply (frule kernel_mapping_slots_empty_pdeI)
    apply (simp add: obj_at_def)+
  apply (clarsimp simp: pde_ref_def)
  apply (rule page_table_pte_atI, simp_all)
   apply (simp add: valid_arch_state_def valid_global_pts_def)
  apply (simp add: pt_bits_def pageBits_def)
  apply (rule order_le_less_trans, rule word_and_le1, simp)
  done *)
  sorry

lemma shiftr_w2p:
  "x < len_of TYPE('a) \<Longrightarrow>
  2 ^ x = (2^(len_of TYPE('a) - 1) >> (len_of TYPE('a) - 1 - x) :: 'a :: len word)"
  apply simp
  apply (rule word_eqI)
  apply (auto simp: word_size nth_shiftr nth_w2p)
  done

lemma vptr_shiftr_le_2p:
  "get_pml4_index (vptr :: word64) < 2 ^ ptTranslationBits"
  apply (rule le_less_trans[rotated])
   apply (rule and_mask_less' [where w=max_word])
   apply (simp add: bit_simps)
  apply (rule word_leI)
  apply (simp add: word_size nth_shiftr get_pml4_index_def bit_simps)
  done


lemma page_map_l4_pml4e_at_lookupI:
  "\<lbrakk>page_map_l4_at pm s; pspace_aligned s\<rbrakk> \<Longrightarrow> pml4e_at (lookup_pml4_slot pm vptr) s"
  apply (simp add: lookup_pml4_slot_def Let_def)
  apply (erule (1) page_map_l4_pml4e_atI[rotated 2])
  apply (simp add: bit_simps get_pml4_index_def mask_def)
  apply (rule order_le_less_trans, rule word_and_le1, simp)
  done

lemma pd_pointer_table_pdpte_at_lookupI:
  "\<lbrakk>pd_pointer_table_at pt s; pspace_aligned s\<rbrakk> \<Longrightarrow> pdpte_at (lookup_pdpt_slot_no_fail pt vptr) s"
  apply (simp add: lookup_pdpt_slot_no_fail_def)
  apply (erule (1) pd_pointer_table_pdpte_atI[rotated 2])
  apply (simp add: bit_simps get_pdpt_index_def mask_def)
  apply (rule order_le_less_trans, rule word_and_le1, simp)
  done
  
lemma page_directory_pde_at_lookupI:
  "\<lbrakk>page_directory_at pt s; pspace_aligned s\<rbrakk> \<Longrightarrow> pde_at (lookup_pd_slot_no_fail pt vptr) s"
  apply (simp add: lookup_pd_slot_no_fail_def)
  apply (erule (1) page_directory_pde_atI[rotated 2])
  apply (simp add: bit_simps get_pd_index_def mask_def)
  apply (rule order_le_less_trans, rule word_and_le1, simp)
  done
  
lemma page_table_pte_at_lookupI:
  "\<lbrakk>page_table_at pt s; pspace_aligned s\<rbrakk> \<Longrightarrow> pte_at (lookup_pt_slot_no_fail pt vptr) s"
  apply (simp add: lookup_pt_slot_no_fail_def)
  apply (erule (1) page_table_pte_atI[rotated 2])
    apply (simp add: bit_simps get_pt_index_def mask_def)
  apply (rule order_le_less_trans, rule word_and_le1, simp)
  done


lemma create_mapping_entries_valid [wp]:
  "\<lbrace>pspace_aligned and valid_arch_state and valid_arch_objs
   and equal_kernel_mappings and valid_global_objs
   and \<exists>\<rhd> pm and page_map_l4_at pm\<rbrace>
  create_mapping_entries base vptr sz vm_rights attrib pm
  \<lbrace>\<lambda>m. valid_mapping_entries m\<rbrace>, -"
  apply (cases sz)
    apply (rule hoare_pre)
     apply (wp|simp add: valid_mapping_entries_def)+
   apply (rule hoare_pre)
    apply (wp|simp add: valid_mapping_entries_def)+
  apply (rule hoare_pre)
   apply wp
  apply clarsimp
  done

lemma set_pt_distinct [wp]:
  "\<lbrace>pspace_distinct\<rbrace> set_pt p pt \<lbrace>\<lambda>_. pspace_distinct\<rbrace>"
  apply (simp add: set_pt_def)
  apply (wp set_object_distinct get_object_wp)
  apply (clarsimp simp: obj_at_def a_type_def
                split: kernel_object.splits arch_kernel_obj.splits)
  done


lemma set_pd_distinct [wp]:
  "\<lbrace>pspace_distinct\<rbrace> set_pd p pd \<lbrace>\<lambda>_. pspace_distinct\<rbrace>"
  apply (simp add: set_pd_def)
  apply (wp set_object_distinct get_object_wp)
  apply (clarsimp simp: obj_at_def a_type_def
                  split: kernel_object.splits arch_kernel_obj.splits)
  done

lemma set_pdpt_distinct [wp]:
  "\<lbrace>pspace_distinct\<rbrace> set_pdpt p pd \<lbrace>\<lambda>_. pspace_distinct\<rbrace>"
  apply (simp add: set_pdpt_def)
  apply (wp set_object_distinct get_object_wp)
  apply (clarsimp simp: obj_at_def a_type_def
                  split: kernel_object.splits arch_kernel_obj.splits)
  done

lemma set_pml4_distinct [wp]:
  "\<lbrace>pspace_distinct\<rbrace> set_pml4 p pd \<lbrace>\<lambda>_. pspace_distinct\<rbrace>"
  apply (simp add: set_pml4_def)
  apply (wp set_object_distinct get_object_wp)
  apply (clarsimp simp: obj_at_def a_type_def
                  split: kernel_object.splits arch_kernel_obj.splits)
  done
  
lemma store_pte_valid_objs [wp]:
  "\<lbrace>(%s. wellformed_pte pte) and valid_objs\<rbrace> store_pte p pte \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: store_pte_def set_pt_def get_pt_def bind_assoc set_object_def get_object_def)
  apply (rule hoare_pre)
   apply (wp|wpc)+
  apply (clarsimp simp: valid_objs_def dom_def simp del: fun_upd_apply)
  subgoal for \<dots> ptr _
  apply (rule valid_obj_same_type)
     apply (cases "ptr = p && ~~ mask pt_bits")
      apply (erule allE, erule impE, blast)
      apply (clarsimp simp: valid_obj_def wellformed_arch_obj_def)
     apply clarsimp
     apply fastforce
    apply (erule allE, erule impE, blast)
    apply (clarsimp simp: valid_obj_def wellformed_arch_obj_def)
   apply assumption
  by (simp add: a_type_def)
  done

lemma store_pde_valid_objs [wp]:
  "\<lbrace>(%s. wellformed_pde pde) and valid_objs\<rbrace> store_pde p pde \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: store_pde_def set_pd_def get_pd_def bind_assoc set_object_def get_object_def)
  apply (rule hoare_pre)
   apply (wp|wpc)+
  apply (clarsimp simp: valid_objs_def dom_def simp del: fun_upd_apply)
  subgoal for \<dots> ptr _
  apply (rule valid_obj_same_type)
     apply (cases "ptr = p && ~~ mask pd_bits")
      apply (erule allE, erule impE, blast)
      apply (clarsimp simp: valid_obj_def wellformed_arch_obj_def)
     apply clarsimp
     apply fastforce
    apply (erule allE, erule impE, blast)
    apply (clarsimp simp: valid_obj_def wellformed_arch_obj_def)
   apply assumption
  by (simp add: a_type_def)
  done

lemma store_pdpte_valid_objs [wp]:
  "\<lbrace>(%s. wellformed_pdpte pdpte) and valid_objs\<rbrace> store_pdpte p pdpte \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: store_pdpte_def set_pdpt_def get_pdpt_def bind_assoc set_object_def get_object_def)
  apply (rule hoare_pre)
   apply (wp|wpc)+
  apply (clarsimp simp: valid_objs_def dom_def simp del: fun_upd_apply)
  subgoal for \<dots> ptr _
  apply (rule valid_obj_same_type)
     apply (cases "ptr = p && ~~ mask pdpt_bits")
      apply (erule allE, erule impE, blast)
      apply (clarsimp simp: valid_obj_def wellformed_arch_obj_def)
     apply clarsimp
     apply fastforce
    apply (erule allE, erule impE, blast)
    apply (clarsimp simp: valid_obj_def wellformed_arch_obj_def)
   apply assumption
  by (simp add: a_type_def)
  done
  
lemma set_pt_caps_of_state [wp]:
  "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> set_pt p pt \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  apply (simp add: set_pt_def get_object_def bind_assoc set_object_def)
  apply wp
  apply clarsimp
  apply (subst cte_wp_caps_of_lift)
   prefer 2
   apply assumption
  subgoal for _ y
  by (cases y, auto simp: cte_wp_at_cases)
  done

lemma set_pd_caps_of_state [wp]:
  "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> set_pd p pd \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  apply (simp add: set_pd_def get_object_def bind_assoc set_object_def)
  apply wp
  apply clarsimp
  apply (subst cte_wp_caps_of_lift)
   prefer 2
   apply assumption
  subgoal for _ y
  by (cases y, auto simp: cte_wp_at_cases)
  done

lemma set_pdpt_caps_of_state [wp]:
  "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> set_pdpt p pdpt \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  apply (simp add: set_pdpt_def get_object_def bind_assoc set_object_def)
  apply wp
  apply clarsimp
  apply (subst cte_wp_caps_of_lift)
   prefer 2
   apply assumption
  subgoal for _ y
  by (cases y, auto simp: cte_wp_at_cases)
  done

lemma set_pml4_caps_of_state [wp]:
  "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> set_pml4 p pml4 \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  apply (simp add: set_pml4_def get_object_def bind_assoc set_object_def)
  apply wp
  apply clarsimp
  apply (subst cte_wp_caps_of_lift)
   prefer 2
   apply assumption
  subgoal for _ y
  by (cases y, auto simp: cte_wp_at_cases)
  done
  
lemma store_pte_aligned [wp]:
  "\<lbrace>pspace_aligned\<rbrace> store_pte pt p \<lbrace>\<lambda>_. pspace_aligned\<rbrace>"
  apply (simp add: store_pte_def set_pt_def)
  apply (wp set_object_aligned get_object_wp)
  including unfold_objects
  by (clarsimp simp: a_type_def)
  
lemma store_pdpte_aligned [wp]:
  "\<lbrace>pspace_aligned\<rbrace> store_pdpte pt p \<lbrace>\<lambda>_. pspace_aligned\<rbrace>"
  apply (simp add: store_pdpte_def set_pdpt_def)
  apply (wp set_object_aligned get_object_wp)
  including unfold_objects
  by (clarsimp simp: a_type_def)

lemma store_pml4e_aligned [wp]:
  "\<lbrace>pspace_aligned\<rbrace> store_pml4e pt p \<lbrace>\<lambda>_. pspace_aligned\<rbrace>"
  apply (simp add: store_pml4e_def set_pml4_def)
  apply (wp set_object_aligned get_object_wp)
  including unfold_objects
  by (clarsimp simp: a_type_def)
  
lemma set_asid_pool_aligned [wp]:
  "\<lbrace>pspace_aligned\<rbrace> set_asid_pool p ptr \<lbrace>\<lambda>_. pspace_aligned\<rbrace>"
  apply (simp add: set_asid_pool_def get_object_def)
  apply (wp set_object_aligned|wpc)+
  including unfold_objects
  by (auto simp: a_type_def)

lemma set_asid_pool_distinct [wp]:
  "\<lbrace>pspace_distinct\<rbrace> set_asid_pool p ptr \<lbrace>\<lambda>_. pspace_distinct\<rbrace>"
  apply (simp add: set_asid_pool_def get_object_def)
  apply (wp set_object_distinct|wpc)+
  including unfold_objects
  by (auto simp: a_type_def)

lemma store_pml4e_arch [wp]:
  "\<lbrace>\<lambda>s. P (arch_state s)\<rbrace> store_pml4e p pml4e \<lbrace>\<lambda>_ s. P (arch_state s)\<rbrace>"
  apply (simp add: store_pml4e_def set_pml4_def get_object_def)
  apply (wp|wpc)+
  apply clarsimp
  done
  
lemma store_pdpte_arch [wp]:
  "\<lbrace>\<lambda>s. P (arch_state s)\<rbrace> store_pdpte p pdpte \<lbrace>\<lambda>_ s. P (arch_state s)\<rbrace>"
  apply (simp add: store_pdpte_def set_pdpt_def get_object_def)
  apply (wp|wpc)+
  apply clarsimp
  done
  
lemma store_pde_arch [wp]:
  "\<lbrace>\<lambda>s. P (arch_state s)\<rbrace> store_pde p pde \<lbrace>\<lambda>_ s. P (arch_state s)\<rbrace>"
  apply (simp add: store_pde_def set_pd_def get_object_def)
  apply (wp|wpc)+
  apply clarsimp
  done

lemma store_pte_arch [wp]:
  "\<lbrace>\<lambda>s. P (arch_state s)\<rbrace> store_pte p pte \<lbrace>\<lambda>_ s. P (arch_state s)\<rbrace>"
  apply (simp add: store_pte_def set_pt_def get_object_def)
  apply (wp|wpc)+
  apply clarsimp
  done
  
lemma store_pte_valid_pte [wp]:
  "\<lbrace>valid_pte pt\<rbrace> store_pte p pte \<lbrace>\<lambda>_. valid_pte pt\<rbrace>"
  by (wp valid_pte_lift store_pte_typ_at)

lemma store_pde_valid_pde [wp]:
  "\<lbrace>valid_pde pde\<rbrace> store_pde slot pde' \<lbrace>\<lambda>rv. valid_pde pde\<rbrace>"
  by (wp valid_pde_lift store_pde_typ_at)

lemma store_pdpte_valid_pdpte [wp]:
  "\<lbrace>valid_pdpte pdpte\<rbrace> store_pdpte slot pdpte' \<lbrace>\<lambda>rv. valid_pdpte pdpte\<rbrace>"
  by (wp valid_pdpte_lift store_pdpte_typ_at)

lemma store_pml4e_valid_pml4e [wp]:
  "\<lbrace>valid_pml4e pml4e\<rbrace> store_pml4e slot pml4e' \<lbrace>\<lambda>rv. valid_pml4e pml4e\<rbrace>"
  by (wp valid_pml4e_lift store_pml4e_typ_at)

lemma set_pml4_typ_at [wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> set_pml4 ptr pml4 \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  apply (simp add: set_pml4_def set_object_def get_object_def)
  apply wp
  apply clarsimp
  apply (erule rsubst [where P=P])
  including unfold_objects
  by (clarsimp simp: a_type_def)


lemma set_pml4_valid_objs:
  "\<lbrace>(%s. \<forall>i. wellformed_pml4e (pml4 i)) and valid_objs\<rbrace>
   set_pml4 p pml4
   \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: set_pml4_def)
  apply (wp get_object_wp set_object_valid_objs)
  including unfold_objects
  by (clarsimp simp: valid_obj_def wellformed_arch_obj_def a_type_def)


lemma set_pml4_iflive:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap s\<rbrace>
  set_pml4 p pml4
  \<lbrace>\<lambda>_ s. if_live_then_nonz_cap s\<rbrace>"
  apply (simp add: set_pml4_def)
  apply (wp get_object_wp set_object_iflive)
  including unfold_objects
  by clarsimp


lemma set_pml4_zombies:
  "\<lbrace>\<lambda>s. zombies_final s\<rbrace>
  set_pml4 p pml4
  \<lbrace>\<lambda>_ s. zombies_final s\<rbrace>"
  apply (simp add: set_pml4_def)
  apply (wp get_object_wp set_object_zombies)
  including unfold_objects
  by clarsimp


lemma set_pml4_zombies_state_refs:
  "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>
  set_pml4 p pml4
  \<lbrace>\<lambda>_ s. P (state_refs_of s)\<rbrace>"
  apply (clarsimp simp: set_pml4_def set_object_def)
  apply (wp get_object_wp)
  including unfold_objects
  apply clarsimp
  apply (erule rsubst [where P=P])
  apply (rule ext)
  by (clarsimp simp: state_refs_of_def split: option.splits)


lemma set_pml4_cdt:
  "\<lbrace>\<lambda>s. P (cdt s)\<rbrace>
  set_pml4 p pml4
  \<lbrace>\<lambda>_ s. P (cdt s)\<rbrace>"
  apply (clarsimp simp: set_pml4_def)
  apply (wp get_object_wp)
  apply simp
  done


lemma set_pml4_valid_mdb:
  "\<lbrace>\<lambda>s. valid_mdb s\<rbrace>
  set_pml4 p pml4
  \<lbrace>\<lambda>_ s. valid_mdb s\<rbrace>"
  apply (rule valid_mdb_lift)
    apply (wp set_pml4_cdt)
  apply (clarsimp simp: set_pml4_def)
  apply (wp get_object_wp)
  apply simp
  done


lemma set_pml4_valid_idle:
  "\<lbrace>\<lambda>s. valid_idle s\<rbrace>
  set_pml4 p pml4
  \<lbrace>\<lambda>_ s. valid_idle s\<rbrace>"
  apply (wp valid_idle_lift)
  apply (simp add: set_pml4_def)
  apply (wp get_object_wp)
  apply simp
  done


lemma set_pml4_ifunsafe:
  "\<lbrace>\<lambda>s. if_unsafe_then_cap s\<rbrace>
  set_pml4 p pml4
  \<lbrace>\<lambda>_ s. if_unsafe_then_cap s\<rbrace>"
  apply (simp add: set_pml4_def)
  apply (wp get_object_wp set_object_ifunsafe)
  including unfold_objects
  by clarsimp


lemma set_pml4_reply_caps:
  "\<lbrace>\<lambda>s. valid_reply_caps s\<rbrace>
  set_pml4 p pml4
  \<lbrace>\<lambda>_ s. valid_reply_caps s\<rbrace>"
  by (wp valid_reply_caps_st_cte_lift)


lemma set_pml4_reply_masters:
  "\<lbrace>valid_reply_masters\<rbrace>
   set_pml4 p pml4
   \<lbrace>\<lambda>_. valid_reply_masters\<rbrace>"
  by (wp valid_reply_masters_cte_lift)
  
lemma set_pdpt_typ_at [wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> set_pdpt ptr pdpt \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  apply (simp add: set_pdpt_def set_object_def get_object_def)
  apply wp
  apply clarsimp
  apply (erule rsubst [where P=P])
  including unfold_objects
  by (clarsimp simp: a_type_def)


lemma set_pdpt_valid_objs:
  "\<lbrace>(%s. \<forall>i. wellformed_pdpte (pdpt i)) and valid_objs\<rbrace>
   set_pdpt p pdpt
   \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: set_pdpt_def)
  apply (wp get_object_wp set_object_valid_objs)
  including unfold_objects
  by (clarsimp simp: valid_obj_def wellformed_arch_obj_def a_type_def)


lemma set_pdpt_iflive:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap s\<rbrace>
  set_pdpt p pdpt
  \<lbrace>\<lambda>_ s. if_live_then_nonz_cap s\<rbrace>"
  apply (simp add: set_pdpt_def)
  apply (wp get_object_wp set_object_iflive)
  including unfold_objects
  by clarsimp


lemma set_pdpt_zombies:
  "\<lbrace>\<lambda>s. zombies_final s\<rbrace>
  set_pdpt p pdpt
  \<lbrace>\<lambda>_ s. zombies_final s\<rbrace>"
  apply (simp add: set_pdpt_def)
  apply (wp get_object_wp set_object_zombies)
  including unfold_objects
  by clarsimp


lemma set_pdpt_zombies_state_refs:
  "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>
  set_pdpt p pdpt
  \<lbrace>\<lambda>_ s. P (state_refs_of s)\<rbrace>"
  apply (clarsimp simp: set_pdpt_def set_object_def)
  apply (wp get_object_wp)
  including unfold_objects
  apply clarsimp
  apply (erule rsubst [where P=P])
  apply (rule ext)
  by (clarsimp simp: state_refs_of_def split: option.splits)


lemma set_pdpt_cdt:
  "\<lbrace>\<lambda>s. P (cdt s)\<rbrace>
  set_pdpt p pdpt
  \<lbrace>\<lambda>_ s. P (cdt s)\<rbrace>"
  apply (clarsimp simp: set_pdpt_def)
  apply (wp get_object_wp)
  apply simp
  done


lemma set_pdpt_valid_mdb:
  "\<lbrace>\<lambda>s. valid_mdb s\<rbrace>
  set_pdpt p pdpt
  \<lbrace>\<lambda>_ s. valid_mdb s\<rbrace>"
  apply (rule valid_mdb_lift)
    apply (wp set_pdpt_cdt)
  apply (clarsimp simp: set_pdpt_def)
  apply (wp get_object_wp)
  apply simp
  done


lemma set_pdpt_valid_idle:
  "\<lbrace>\<lambda>s. valid_idle s\<rbrace>
  set_pdpt p pdpt
  \<lbrace>\<lambda>_ s. valid_idle s\<rbrace>"
  apply (wp valid_idle_lift)
  apply (simp add: set_pdpt_def)
  apply (wp get_object_wp)
  apply simp
  done


lemma set_pdpt_ifunsafe:
  "\<lbrace>\<lambda>s. if_unsafe_then_cap s\<rbrace>
  set_pdpt p pdpt
  \<lbrace>\<lambda>_ s. if_unsafe_then_cap s\<rbrace>"
  apply (simp add: set_pdpt_def)
  apply (wp get_object_wp set_object_ifunsafe)
  including unfold_objects
  by clarsimp


lemma set_pdpt_reply_caps:
  "\<lbrace>\<lambda>s. valid_reply_caps s\<rbrace>
  set_pdpt p pdpt
  \<lbrace>\<lambda>_ s. valid_reply_caps s\<rbrace>"
  by (wp valid_reply_caps_st_cte_lift)


lemma set_pdpt_reply_masters:
  "\<lbrace>valid_reply_masters\<rbrace>
   set_pdpt p pdpt
   \<lbrace>\<lambda>_. valid_reply_masters\<rbrace>"
  by (wp valid_reply_masters_cte_lift)
  
lemma set_pd_typ_at [wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> set_pd ptr pd \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  apply (simp add: set_pd_def set_object_def get_object_def)
  apply wp
  apply clarsimp
  apply (erule rsubst [where P=P])
  including unfold_objects
  by (clarsimp simp: a_type_def)


lemma set_pd_valid_objs:
  "\<lbrace>(%s. \<forall>i. wellformed_pde (pd i)) and valid_objs\<rbrace>
   set_pd p pd
   \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: set_pd_def)
  apply (wp get_object_wp set_object_valid_objs)
  including unfold_objects
  by (clarsimp simp: valid_obj_def wellformed_arch_obj_def a_type_def)


lemma set_pd_iflive:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap s\<rbrace>
  set_pd p pd
  \<lbrace>\<lambda>_ s. if_live_then_nonz_cap s\<rbrace>"
  apply (simp add: set_pd_def)
  apply (wp get_object_wp set_object_iflive)
  including unfold_objects
  by clarsimp


lemma set_pd_zombies:
  "\<lbrace>\<lambda>s. zombies_final s\<rbrace>
  set_pd p pd
  \<lbrace>\<lambda>_ s. zombies_final s\<rbrace>"
  apply (simp add: set_pd_def)
  apply (wp get_object_wp set_object_zombies)
  including unfold_objects
  by clarsimp


lemma set_pd_zombies_state_refs:
  "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>
  set_pd p pd
  \<lbrace>\<lambda>_ s. P (state_refs_of s)\<rbrace>"
  apply (clarsimp simp: set_pd_def set_object_def)
  apply (wp get_object_wp)
  including unfold_objects
  apply clarsimp
  apply (erule rsubst [where P=P])
  apply (rule ext)
  by (clarsimp simp: state_refs_of_def split: option.splits)


lemma set_pd_cdt:
  "\<lbrace>\<lambda>s. P (cdt s)\<rbrace>
  set_pd p pd
  \<lbrace>\<lambda>_ s. P (cdt s)\<rbrace>"
  apply (clarsimp simp: set_pd_def)
  apply (wp get_object_wp)
  apply simp
  done


lemma set_pd_valid_mdb:
  "\<lbrace>\<lambda>s. valid_mdb s\<rbrace>
  set_pd p pd
  \<lbrace>\<lambda>_ s. valid_mdb s\<rbrace>"
  apply (rule valid_mdb_lift)
    apply (wp set_pd_cdt)
  apply (clarsimp simp: set_pd_def)
  apply (wp get_object_wp)
  apply simp
  done


lemma set_pd_valid_idle:
  "\<lbrace>\<lambda>s. valid_idle s\<rbrace>
  set_pd p pd
  \<lbrace>\<lambda>_ s. valid_idle s\<rbrace>"
  apply (wp valid_idle_lift)
  apply (simp add: set_pd_def)
  apply (wp get_object_wp)
  apply simp
  done


lemma set_pd_ifunsafe:
  "\<lbrace>\<lambda>s. if_unsafe_then_cap s\<rbrace>
  set_pd p pd
  \<lbrace>\<lambda>_ s. if_unsafe_then_cap s\<rbrace>"
  apply (simp add: set_pd_def)
  apply (wp get_object_wp set_object_ifunsafe)
  including unfold_objects
  by clarsimp


lemma set_pd_reply_caps:
  "\<lbrace>\<lambda>s. valid_reply_caps s\<rbrace>
  set_pd p pd
  \<lbrace>\<lambda>_ s. valid_reply_caps s\<rbrace>"
  by (wp valid_reply_caps_st_cte_lift)


lemma set_pd_reply_masters:
  "\<lbrace>valid_reply_masters\<rbrace>
   set_pd p pd
   \<lbrace>\<lambda>_. valid_reply_masters\<rbrace>"
  by (wp valid_reply_masters_cte_lift)


lemma global_refs_kheap [simp]:
  "global_refs (kheap_update f s) = global_refs s"
  by (simp add: global_refs_def)


crunch global_ref [wp]: set_pd, set_pdpt, set_pml4 "\<lambda>s. P (global_refs s)"
  (wp: crunch_wps)


crunch arch [wp]: set_pd, set_pdpt, set_pml4 "\<lambda>s. P (arch_state s)"
  (wp: crunch_wps)


crunch idle [wp]: set_pd, set_pdpt, set_pml4 "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps)


crunch irq [wp]: set_pd, set_pdpt, set_pml4 "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps)

lemma set_pml4_valid_global:
  "\<lbrace>\<lambda>s. valid_global_refs s\<rbrace>
  set_pml4 p pml4
  \<lbrace>\<lambda>_ s. valid_global_refs s\<rbrace>"
  by (wp valid_global_refs_cte_lift)


lemma set_pml4_valid_arch:
  "\<lbrace>\<lambda>s. valid_arch_state s\<rbrace>
  set_pml4 p pml4
  \<lbrace>\<lambda>_ s. valid_arch_state s\<rbrace>"
  by (wp valid_arch_state_lift)


lemma set_pml4_cur:
  "\<lbrace>\<lambda>s. cur_tcb s\<rbrace>
  set_pml4 p pml4
  \<lbrace>\<lambda>_ s. cur_tcb s\<rbrace>"
  apply (simp add: cur_tcb_def set_pml4_def set_object_def)
  apply (wp get_object_wp)
  apply clarsimp
  apply (clarsimp split: kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp: obj_at_def is_tcb_def)
  done
  
lemma set_pdpt_valid_global:
  "\<lbrace>\<lambda>s. valid_global_refs s\<rbrace>
  set_pdpt p pdpt
  \<lbrace>\<lambda>_ s. valid_global_refs s\<rbrace>"
  by (wp valid_global_refs_cte_lift)


lemma set_pdpt_valid_arch:
  "\<lbrace>\<lambda>s. valid_arch_state s\<rbrace>
  set_pdpt p pdpt
  \<lbrace>\<lambda>_ s. valid_arch_state s\<rbrace>"
  by (wp valid_arch_state_lift)


lemma set_pdpt_cur:
  "\<lbrace>\<lambda>s. cur_tcb s\<rbrace>
  set_pdpt p pdpt
  \<lbrace>\<lambda>_ s. cur_tcb s\<rbrace>"
  apply (simp add: cur_tcb_def set_pdpt_def set_object_def)
  apply (wp get_object_wp)
  apply clarsimp
  apply (clarsimp split: kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp: obj_at_def is_tcb_def)
  done
  
lemma set_pd_valid_global:
  "\<lbrace>\<lambda>s. valid_global_refs s\<rbrace>
  set_pd p pd
  \<lbrace>\<lambda>_ s. valid_global_refs s\<rbrace>"
  by (wp valid_global_refs_cte_lift)


lemma set_pd_valid_arch:
  "\<lbrace>\<lambda>s. valid_arch_state s\<rbrace>
  set_pd p pd
  \<lbrace>\<lambda>_ s. valid_arch_state s\<rbrace>"
  by (wp valid_arch_state_lift)


lemma set_pd_cur:
  "\<lbrace>\<lambda>s. cur_tcb s\<rbrace>
  set_pd p pd
  \<lbrace>\<lambda>_ s. cur_tcb s\<rbrace>"
  apply (simp add: cur_tcb_def set_pd_def set_object_def)
  apply (wp get_object_wp)
  apply clarsimp
  apply (clarsimp split: kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp: obj_at_def is_tcb_def)
  done


crunch interrupt_states[wp]: set_pd, set_pdpt, set_pml4 "\<lambda>s. P (interrupt_states s)"
  (wp: crunch_wps)

lemma set_pml4_arch_objs_unmap:
  "\<lbrace>valid_arch_objs and (\<lambda>s. (\<exists>\<rhd>p) s \<longrightarrow> valid_arch_obj (PageMapL4 pd') s) and
    obj_at (\<lambda>ko. vs_refs (ArchObj (PageMapL4 pd')) \<subseteq> vs_refs ko) p\<rbrace>
  set_pml4 p pd' \<lbrace>\<lambda>_. valid_arch_objs\<rbrace>"
  apply (simp add: set_pml4_def)
  apply (wp set_object_arch_objs get_object_wp)
  including unfold_objects
  by (fastforce simp: a_type_def)

lemma set_pdpt_arch_objs_unmap:
  "\<lbrace>valid_arch_objs and (\<lambda>s. (\<exists>\<rhd>p) s \<longrightarrow> valid_arch_obj (PDPointerTable pdpt') s) and
    obj_at (\<lambda>ko. vs_refs (ArchObj (PDPointerTable pdpt')) \<subseteq> vs_refs ko) p\<rbrace>
  set_pdpt p pdpt' \<lbrace>\<lambda>_. valid_arch_objs\<rbrace>"
  apply (simp add: set_pdpt_def)
  apply (wp set_object_arch_objs get_object_wp)
  including unfold_objects
  by (fastforce simp: a_type_def)  

lemma set_pd_arch_objs_unmap:
  "\<lbrace>valid_arch_objs and (\<lambda>s. (\<exists>\<rhd>p) s \<longrightarrow> valid_arch_obj (PageDirectory pd') s) and
    obj_at (\<lambda>ko. vs_refs (ArchObj (PageDirectory pd')) \<subseteq> vs_refs ko) p\<rbrace>
  set_pd p pd' \<lbrace>\<lambda>_. valid_arch_objs\<rbrace>"
  apply (simp add: set_pd_def)
  apply (wp set_object_arch_objs get_object_wp)
  including unfold_objects
  by (fastforce simp: a_type_def)


declare graph_of_None_update[simp]
declare graph_of_Some_update[simp]


lemma set_pt_typ_at [wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> set_pt ptr pt \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  apply (simp add: set_pt_def set_object_def get_object_def)
  apply wp
  apply clarsimp
  apply (erule rsubst [where P=P])
  including unfold_objects
  by (clarsimp simp: a_type_def)


lemma set_pt_valid_objs:
  "\<lbrace>(%s. \<forall>i. wellformed_pte (pt i)) and valid_objs\<rbrace>
   set_pt p pt
   \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: set_pt_def)
  apply (wp get_object_wp set_object_valid_objs)
  apply (clarsimp split: kernel_object.splits
                         arch_kernel_obj.splits)
  apply (clarsimp simp: valid_obj_def obj_at_def a_type_def
                        wellformed_arch_obj_def)
  done


lemma set_pt_iflive:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap s\<rbrace>
  set_pt p pt
  \<lbrace>\<lambda>_ s. if_live_then_nonz_cap s\<rbrace>"
  apply (simp add: set_pt_def)
  apply (wp get_object_wp set_object_iflive)
  apply (clarsimp split: kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp: obj_at_def)
  done


lemma set_pt_zombies:
  "\<lbrace>\<lambda>s. zombies_final s\<rbrace>
  set_pt p pt
  \<lbrace>\<lambda>_ s. zombies_final s\<rbrace>"
  apply (simp add: set_pt_def)
  apply (wp get_object_wp set_object_zombies)
  apply (clarsimp split: kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp: obj_at_def)
  done


lemma set_pt_zombies_state_refs:
  "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>
  set_pt p pt
  \<lbrace>\<lambda>_ s. P (state_refs_of s)\<rbrace>"
  apply (clarsimp simp: set_pt_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp split: kernel_object.splits arch_kernel_obj.splits)
  apply (erule rsubst [where P=P])
  apply (rule ext)
  apply (clarsimp simp: obj_at_def state_refs_of_def split: option.splits)
  done


lemma set_pt_cdt:
  "\<lbrace>\<lambda>s. P (cdt s)\<rbrace>
  set_pt p pt
  \<lbrace>\<lambda>_ s. P (cdt s)\<rbrace>"
  apply (clarsimp simp: set_pt_def)
  apply (wp get_object_wp)
  apply simp
  done


lemma set_pt_valid_mdb:
  "\<lbrace>\<lambda>s. valid_mdb s\<rbrace>
  set_pt p pt
  \<lbrace>\<lambda>_ s. valid_mdb s\<rbrace>"
  apply (rule valid_mdb_lift)
    apply (wp set_pt_cdt)
  apply (clarsimp simp: set_pt_def)
  apply (wp get_object_wp)
  apply simp
  done


lemma set_pt_valid_idle:
  "\<lbrace>\<lambda>s. valid_idle s\<rbrace>
  set_pt p pt
  \<lbrace>\<lambda>_ s. valid_idle s\<rbrace>"
  apply (wp valid_idle_lift)
  apply (simp add: set_pt_def)
  apply (wp get_object_wp)
  apply simp
  done


lemma set_pt_ifunsafe:
  "\<lbrace>\<lambda>s. if_unsafe_then_cap s\<rbrace>
  set_pt p pt
  \<lbrace>\<lambda>_ s. if_unsafe_then_cap s\<rbrace>"
  apply (simp add: set_pt_def)
  apply (wp get_object_wp set_object_ifunsafe)
  apply (clarsimp split: kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp: obj_at_def)
  done


lemma set_pt_reply_caps:
  "\<lbrace>\<lambda>s. valid_reply_caps s\<rbrace>
  set_pt p pt
  \<lbrace>\<lambda>_ s. valid_reply_caps s\<rbrace>"
  by (wp valid_reply_caps_st_cte_lift)


lemma set_pt_reply_masters:
  "\<lbrace>valid_reply_masters\<rbrace>
   set_pt p pt
   \<lbrace>\<lambda>_. valid_reply_masters\<rbrace>"
  by (wp valid_reply_masters_cte_lift)


crunch global_ref [wp]: set_pt "\<lambda>s. P (global_refs s)"
  (wp: crunch_wps)


crunch arch [wp]: set_pt "\<lambda>s. P (arch_state s)"
  (wp: crunch_wps)


crunch idle [wp]: set_pt "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps)


crunch irq [wp]: set_pt "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps)


lemma set_pt_valid_global:
  "\<lbrace>\<lambda>s. valid_global_refs s\<rbrace>
  set_pt p pt
  \<lbrace>\<lambda>_ s. valid_global_refs s\<rbrace>"
  by (wp valid_global_refs_cte_lift)


lemma set_pt_valid_arch_state[wp]:
  "\<lbrace>\<lambda>s. valid_arch_state s\<rbrace>
  set_pt p pt
  \<lbrace>\<lambda>_ s. valid_arch_state s\<rbrace>"
  by (wp valid_arch_state_lift)


lemma set_pt_cur:
  "\<lbrace>\<lambda>s. cur_tcb s\<rbrace>
  set_pt p pt
  \<lbrace>\<lambda>_ s. cur_tcb s\<rbrace>"
  apply (simp add: cur_tcb_def set_pt_def set_object_def)
  apply (wp get_object_wp)
  apply clarsimp
  apply (clarsimp split: kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp: obj_at_def is_tcb_def)
  done


lemma set_pt_aligned [wp]:
  "\<lbrace>pspace_aligned\<rbrace> set_pt p pt \<lbrace>\<lambda>_. pspace_aligned\<rbrace>"
  apply (simp add: set_pt_def)
  apply (wp get_object_wp set_object_aligned)
  apply (clarsimp simp: a_type_def obj_at_def
                  split: kernel_object.splits arch_kernel_obj.splits)
  done


crunch interrupt_states[wp]: set_pt "\<lambda>s. P (interrupt_states s)"
  (wp: crunch_wps)


lemma set_pt_arch_objs [wp]:
  "\<lbrace>valid_arch_objs and (\<lambda>s. (\<exists>\<rhd>p) s \<longrightarrow> valid_arch_obj (PageTable pt) s)\<rbrace>
  set_pt p pt
  \<lbrace>\<lambda>_. valid_arch_objs\<rbrace>"
  apply (simp add: set_pt_def)
  apply (wp set_object_arch_objs get_object_wp)
  apply (clarsimp simp: obj_at_def)
  apply (rule conjI)
   apply (clarsimp simp: a_type_def
                  split: kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp split: kernel_object.splits arch_kernel_obj.splits)
  apply (simp add: vs_refs_def)
  done

lemma set_pt_vs_lookup [wp]:
  "\<lbrace>\<lambda>s. P (vs_lookup s)\<rbrace> set_pt p pt \<lbrace>\<lambda>x s. P (vs_lookup s)\<rbrace>"
  unfolding set_pt_def set_object_def
  apply (wp get_object_wp)
  apply clarsimp
  apply (erule rsubst [where P=P])
  apply (clarsimp split: kernel_object.splits arch_kernel_obj.splits)
  apply (rule order_antisym)
   apply (rule vs_lookup_sub)
    apply (clarsimp simp: obj_at_def vs_refs_def)
   apply simp
  apply (rule vs_lookup_sub)
   apply (clarsimp simp: obj_at_def vs_refs_def split: split_if_asm)
  apply simp
  done


lemma store_pte_vs_lookup [wp]:
  "\<lbrace>\<lambda>s. P (vs_lookup s)\<rbrace> store_pte x pte \<lbrace>\<lambda>_ s. P (vs_lookup s)\<rbrace>"
  unfolding store_pte_def by wp simp


lemma unique_table_caps_ptD:
  "\<lbrakk> cs p = Some cap; cap_asid cap = None;
     cs p' = Some cap'; is_pt_cap cap; is_pt_cap cap';
     obj_refs cap' = obj_refs cap;
     unique_table_caps cs\<rbrakk>
  \<Longrightarrow> p = p'"
  by (fastforce simp add: unique_table_caps_def)


lemma unique_table_caps_pdD:
  "\<lbrakk> cs p = Some cap; cap_asid cap = None;
     cs p' = Some cap'; is_pd_cap cap; is_pd_cap cap';
     obj_refs cap' = obj_refs cap;
     unique_table_caps cs\<rbrakk>
  \<Longrightarrow> p = p'"
  by (fastforce simp add: unique_table_caps_def)

lemma unique_table_caps_pdptD:
  "\<lbrakk> cs p = Some cap; cap_asid cap = None;
     cs p' = Some cap'; is_pdpt_cap cap; is_pdpt_cap cap';
     obj_refs cap' = obj_refs cap;
     unique_table_caps cs\<rbrakk>
  \<Longrightarrow> p = p'"
  by (fastforce simp add: unique_table_caps_def)

lemma unique_table_caps_pml4D:
  "\<lbrakk> cs p = Some cap; cap_asid cap = None;
     cs p' = Some cap'; is_pml4_cap cap; is_pml4_cap cap';
     obj_refs cap' = obj_refs cap;
     unique_table_caps cs\<rbrakk>
  \<Longrightarrow> p = p'"
  by (fastforce simp add: unique_table_caps_def)

lemma valid_objs_caps:
  "valid_objs s \<Longrightarrow> valid_caps (caps_of_state s) s"
  apply (clarsimp simp: valid_caps_def)
  apply (erule (1) caps_of_state_valid_cap)
  done


lemma simpler_set_pt_def:
  "set_pt p pt =
   (\<lambda>s. if \<exists>pt. kheap s p = Some (ArchObj (PageTable pt)) then
           ({((), s\<lparr>kheap := kheap s(p \<mapsto> ArchObj (PageTable pt))\<rparr>)}, False)
        else ({}, True))"
  by (rule ext) (auto simp: set_pt_def set_object_def get_object_def assert_def
                            put_def get_def simpler_gets_def bind_def
                            return_def fail_def
                     split: kernel_object.splits
                            arch_kernel_obj.splits)


lemma valid_set_ptI:
  "(!!s opt. \<lbrakk>P s; kheap s p = Some (ArchObj (PageTable opt))\<rbrakk>
         \<Longrightarrow> Q () (s\<lparr>kheap := kheap s(p \<mapsto> ArchObj (PageTable pt))\<rparr>))
   \<Longrightarrow> \<lbrace>P\<rbrace> set_pt p pt \<lbrace>Q\<rbrace>"
  by (rule validI) (clarsimp simp: simpler_set_pt_def split: split_if_asm)

lemma set_pt_table_caps [wp]:
  "\<lbrace>valid_table_caps and (\<lambda>s. valid_caps (caps_of_state s) s) and
    (\<lambda>s. ((\<exists>slot. caps_of_state s slot =
                 Some (ArchObjectCap (PageTableCap p None))) \<longrightarrow>
          pt = (\<lambda>x. InvalidPTE)) \<or>
         (\<forall>slot. \<exists>asid. caps_of_state s slot =
             Some (ArchObjectCap (PageTableCap p (Some asid)))))\<rbrace>
   set_pt p pt
   \<lbrace>\<lambda>rv. valid_table_caps\<rbrace>"
  unfolding valid_table_caps_def
  apply (rule valid_set_ptI)
  apply (intro allI impI, simp add: obj_at_def del: HOL.imp_disjL)
  apply (cut_tac s=s and val= "ArchObj (PageTable pt)" and p=p
               in caps_of_state_after_update[folded fun_upd_def])
   apply (simp add: obj_at_def)
  apply (clarsimp simp del: HOL.imp_disjL)
  apply (thin_tac "ALL x. P x" for P)
  apply (case_tac cap, simp_all add: is_pd_cap_def is_pt_cap_def is_pdpt_cap_def is_pml4_cap_def)
  apply (erule disjE)
   apply (simp add: valid_caps_def)
   apply ((drule spec)+, erule impE, assumption)
   apply (rename_tac arch_cap)
   apply (case_tac arch_cap; clarsimp simp: valid_cap_def obj_at_def aa_type_simps)
  apply (erule disjE)
   apply clarsimp
   apply (erule impE, fastforce simp: cap_asid_def split: option.splits)
   apply (erule disjE, simp add: empty_table_def)
   apply (drule_tac x=a in spec, drule_tac x=b in spec)
   apply (clarsimp simp add: cap_asid_def split: option.splits)
  apply (erule disjE)
   apply (simp add: valid_caps_def)
   apply ((drule spec)+, erule impE, assumption)
   apply (rename_tac arch_cap)
   apply (case_tac arch_cap; clarsimp simp: valid_cap_def obj_at_def aa_type_simps)
  apply (simp add: valid_caps_def)
  apply ((drule spec)+, erule impE, assumption)
  apply (rename_tac arch_cap)
  apply (case_tac arch_cap; clarsimp simp: valid_cap_def obj_at_def aa_type_simps)
  done

lemma set_object_caps_of_state:
  "\<lbrace>(\<lambda>s. \<not>(tcb_at p s) \<and> \<not>(\<exists>n. cap_table_at n p s)) and
    K ((\<forall>x y. obj \<noteq> CNode x y) \<and> (\<forall>x. obj \<noteq> TCB x)) and
    (\<lambda>s. P (caps_of_state s))\<rbrace>
   set_object p obj
   \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  apply (clarsimp simp: set_object_def)
  apply wp
  apply clarify
  apply (erule rsubst[where P=P])
  apply (rule ext)
  apply (simp add: caps_of_state_cte_wp_at obj_at_def is_cap_table_def
                   is_tcb_def)
  apply (auto simp: cte_wp_at_cases)
  done


(* FIXME: Move to Invariants_A *)
lemma pte_ref_pagesD:
  "pte_ref_pages (pt y) = Some x \<Longrightarrow>
   (VSRef (ucast y) (Some APageTable), x)
   \<in> vs_refs_pages (ArchObj (PageTable pt))"
  by (auto simp: pte_ref_pages_def vs_refs_pages_def graph_of_def)


(* FIXME x64: *)
lemma set_pt_valid_arch_objs[wp]:
  "valid (\<lambda>s. valid_arch_objs s \<and> ((\<exists>\<rhd> p) s \<longrightarrow> (\<forall>x. valid_pte (pt x) s)))
             (set_pt p pt) (\<lambda>_. valid_arch_objs)"
  apply (rule valid_set_ptI)
  apply (clarsimp simp: valid_arch_objs_def)
  subgoal for s opt pa rs ao
    apply (spec pa)
    apply (prove "(\<exists>\<rhd> pa) s")
     apply (rule exI[where x=rs])
     apply (erule vs_lookupE)
     apply clarsimp
     apply (erule vs_lookupI)
     apply (erule rtrancl.induct, simp)
     subgoal for \<dots> b c
       apply (prove "(b \<rhd>1 c) s")
       apply (thin_tac "_ : rtrancl _")+
       apply (clarsimp simp add: vs_lookup1_def obj_at_def vs_refs_def
                            split: split_if_asm)
       by simp
    apply simp
    apply (spec ao)
    apply (cases "pa = p")
     apply (clarsimp simp: obj_at_def)
     subgoal for _ x
       apply (drule_tac x=x in spec)
       by (cases "pt x"; clarsimp simp: obj_at_def a_type_simps)
    apply (cases ao; simp add: obj_at_def a_type_simps)
      apply clarsimp
      apply (drule bspec, assumption, clarsimp)
     apply clarsimp
     subgoal for "fun" _ x
       apply (spec x)
       by (cases "fun x"; clarsimp simp: obj_at_def a_type_simps)
    apply clarsimp (*
    apply (drule bspec,fastforce)
    subgoal for "fun" x
      by (cases "fun x"; clarsimp simp: obj_at_def a_type_simps)
    done
  done*)
  sorry
  sorry

(* FIXME x64: this needs more vs_refs expansion *)
lemma set_pt_valid_vs_lookup [wp]:
  "\<lbrace>\<lambda>s. valid_vs_lookup s \<and> valid_arch_state s \<and>
        valid_arch_objs s \<and> ((\<exists>\<rhd> p) s \<longrightarrow> (\<forall>x. valid_pte (pt x) s)) \<and>
        (\<forall>ref. (ref \<unrhd> p) s \<longrightarrow>
            (\<forall>x p. pte_ref_pages (pt x) = Some p \<longrightarrow>
                    (\<exists>p' cap. caps_of_state s p' = Some cap \<and>
                         p \<in> obj_refs cap \<and>
                         vs_cap_ref cap =
                         Some (VSRef (ucast x) (Some APageTable) # ref))))\<rbrace>
   set_pt p pt
   \<lbrace>\<lambda>rv. valid_vs_lookup\<rbrace>"
  using set_pt_valid_arch_objs[of p pt] set_pt_valid_arch_state[of p pt]
  apply (clarsimp simp: valid_def simpler_set_pt_def)
  apply (drule_tac x=s in spec)+
  apply (clarsimp simp: valid_vs_lookup_def  split: split_if_asm)
  apply (erule (1) vs_lookup_pagesE_alt)
      apply (clarsimp simp: valid_arch_state_def valid_asid_table_def
                            fun_upd_def)
     apply (drule_tac x=pa in spec)
     apply (drule_tac x="[VSRef (ucast a) None]" in spec)+
     apply simp
     apply (drule vs_lookup_pages_atI)
     apply simp
     apply (subst caps_of_state_after_update, simp add: obj_at_def)
     apply simp
    apply (drule_tac x=pa in spec)
    apply (drule_tac x="[VSRef (ucast b) (Some AASIDPool),
                         VSRef (ucast a) None]" in spec)+
    apply simp
    apply (drule vs_lookup_pages_apI)
      apply (simp split: split_if_asm)
     apply simp+
    apply (subst caps_of_state_after_update, simp add: obj_at_def)
    apply simp
    (*
   apply (drule_tac x=pa in spec)
   apply (drule_tac x="[VSRef (ucast c) (Some APageDirectory),
                        VSRef (ucast b) (Some AASIDPool),
                        VSRef (ucast a) None]" in spec)+
   apply simp
   apply (drule vs_lookup_pages_pdI)
        apply (simp split: split_if_asm)+
   apply (subst caps_of_state_after_update, simp add: obj_at_def)
   apply fastforce
  apply (clarsimp simp: fun_upd_def  split: split_if_asm)
   apply (thin_tac "valid_arch_objs s" for s, thin_tac "valid_arch_state s" for s)
   apply (subst caps_of_state_after_update, simp add: obj_at_def)
   apply (thin_tac "\<forall>p ref. P p ref" for P)
   apply (drule_tac x="[VSRef (ucast c) (Some APageDirectory),
                        VSRef (ucast b) (Some AASIDPool),
                        VSRef (ucast a) None]" in spec)
   apply (thin_tac "valid_pte pte s" for pte s)
   apply (erule impE, fastforce intro: vs_lookup_pdI)
   apply (drule_tac x=d in spec)
   apply (erule impE)
    apply (erule (5) vs_lookup_pdI[THEN vs_lookup_pages_vs_lookupI])
   apply (drule spec, drule spec, erule impE, assumption)
   apply assumption
  apply (thin_tac "valid_arch_objs s" for s, thin_tac "valid_arch_state s" for s)
  apply (subst caps_of_state_after_update, simp add: obj_at_def)
  apply (thin_tac "\<forall>ref. (ref \<unrhd> p) s \<longrightarrow> P ref" for P)
  apply (drule_tac x=pa in spec)
  apply (drule_tac x="[VSRef (ucast d) (Some APageTable),
                       VSRef (ucast c) (Some APageDirectory),
                       VSRef (ucast b) (Some AASIDPool),
                       VSRef (ucast a) None]" in spec)
  apply (thin_tac "(\<exists>\<rhd> p) s \<longrightarrow> P" for P)
  apply (erule impE, fastforce intro: vs_lookup_pages_ptI)
  apply simp
  done *)
  sorry


lemma set_pt_arch_caps [wp]:
  "\<lbrace>valid_arch_caps and valid_arch_state and valid_arch_objs and
    (\<lambda>s. valid_caps (caps_of_state s) s) and
    (\<lambda>s. ((\<exists>slot. caps_of_state s slot =
                 Some (ArchObjectCap (PageTableCap p None))) \<longrightarrow>
          pt = (\<lambda>x. InvalidPTE)) \<or>
         (\<forall>slot. \<exists>asid. caps_of_state s slot =
           Some (ArchObjectCap (PageTableCap p (Some asid))))) and
    (\<lambda>s. ((\<exists>\<rhd> p) s \<longrightarrow> (\<forall>x. valid_pte (pt x) s)) \<and>
         (\<forall>ref. (ref \<unrhd> p) s \<longrightarrow>
            (\<forall>x p. pte_ref_pages (pt x) = Some p \<longrightarrow>
                   (\<exists>p' cap. caps_of_state s p' = Some cap \<and>
                        p \<in> obj_refs cap \<and>
                        vs_cap_ref cap =
                        Some (VSRef (ucast x) (Some APageTable) # ref)))))\<rbrace>
  set_pt p pt \<lbrace>\<lambda>_. valid_arch_caps\<rbrace>"
  unfolding valid_arch_caps_def
  apply (rule hoare_pre)
   apply (wp set_pt_valid_vs_lookup)
  apply clarsimp
  done


lemma valid_global_refsD2:
  "\<lbrakk> caps_of_state s ptr = Some cap; valid_global_refs s \<rbrakk>
      \<Longrightarrow> global_refs s \<inter> cap_range cap = {}"
  by (cases ptr,
      simp add: valid_global_refs_def valid_refs_def
                cte_wp_at_caps_of_state)


lemma valid_global_refsD:
  "\<lbrakk> valid_global_refs s; cte_wp_at (op = cap) ptr s;
         r \<in> global_refs s \<rbrakk>
        \<Longrightarrow> r \<notin> cap_range cap"
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (drule(1) valid_global_refsD2)
  apply fastforce
  done

(* FIXME x64: needs updated valid_global_objs *)
lemma set_pt_global_objs [wp]:
  "\<lbrace>valid_global_objs and valid_arch_state and
    (\<lambda>s. p \<in> set (x64_global_pts (arch_state s)) \<longrightarrow>
         (\<forall>x. aligned_pte (pt x)))\<rbrace>
   set_pt p pt
   \<lbrace>\<lambda>rv. valid_global_objs\<rbrace>"
  apply (rule valid_set_ptI)
  apply (clarsimp simp: valid_global_objs_def valid_arch_state_def
                        valid_ao_at_def obj_at_def)
  sorry


crunch v_ker_map[wp]: set_pt, set_pd, set_pdpt "valid_kernel_mappings"
  (ignore: set_object wp: set_object_v_ker_map crunch_wps)


lemma set_pt_asid_map [wp]:
  "\<lbrace>valid_asid_map\<rbrace> set_pt p pt \<lbrace>\<lambda>_. valid_asid_map\<rbrace>"
  apply (simp add: valid_asid_map_def vspace_at_asid_def)
  apply (rule hoare_lift_Pf2 [where f="arch_state"])
   apply wp
  done


lemma set_pt_only_idle [wp]:
  "\<lbrace>only_idle\<rbrace> set_pt p pt \<lbrace>\<lambda>_. only_idle\<rbrace>"
  by (wp only_idle_lift)


lemma set_pt_equal_mappings [wp]:
  "\<lbrace>equal_kernel_mappings\<rbrace> set_pt p pt \<lbrace>\<lambda>rv. equal_kernel_mappings\<rbrace>"
  by (simp add: set_pt_def | wp set_object_equal_mappings get_object_wp)+


lemma set_pt_valid_global_vspace_mappings:
  "\<lbrace>\<lambda>s. valid_global_vspace_mappings s \<and> valid_global_objs s \<and> p \<notin> global_refs s\<rbrace>
      set_pt p pt
   \<lbrace>\<lambda>rv. valid_global_vspace_mappings\<rbrace>"
  apply (simp add: set_pt_def)
  apply (wp set_object_global_vspace_mappings get_object_wp)
  apply (clarsimp simp: obj_at_def a_type_def
                 split: kernel_object.split_asm
                        arch_kernel_obj.split_asm)
  done


lemma set_pt_kernel_window[wp]:
  "\<lbrace>pspace_in_kernel_window\<rbrace> set_pt p pt \<lbrace>\<lambda>rv. pspace_in_kernel_window\<rbrace>"
  apply (simp add: set_pt_def)
  apply (wp set_object_pspace_in_kernel_window get_object_wp)
  apply (clarsimp simp: obj_at_def a_type_def
                 split: kernel_object.split_asm
                        arch_kernel_obj.split_asm)
  done


lemma set_pt_caps_kernel_window[wp]:
  "\<lbrace>cap_refs_in_kernel_window\<rbrace> set_pt p pt \<lbrace>\<lambda>rv. cap_refs_in_kernel_window\<rbrace>"
  apply (simp add: set_pt_def)
  apply (wp set_object_cap_refs_in_kernel_window get_object_wp)
  apply (clarsimp simp: obj_at_def a_type_def
                 split: kernel_object.split_asm
                        arch_kernel_obj.split_asm)
  done


lemma set_pt_valid_ioc[wp]:
  "\<lbrace>valid_ioc\<rbrace> set_pt p pt \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  apply (simp add: set_pt_def)
  apply (wp set_object_valid_ioc_no_caps get_object_wp)
  by (clarsimp simp: a_type_simps obj_at_def is_tcb is_cap_table
              split: kernel_object.splits arch_kernel_obj.splits)


lemma set_pt_vms[wp]:
  "\<lbrace>valid_machine_state\<rbrace> set_pt p pt \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  apply (simp add: set_pt_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: valid_machine_state_def in_user_frame_def obj_at_def
                 split: kernel_object.splits arch_kernel_obj.splits)
  apply (frule_tac x=pa in spec)
  apply (frule_tac x=p in spec)
  apply (clarsimp simp add: a_type_simps)
  apply (rule_tac x=sz in exI)
  apply (clarsimp simp: a_type_simps)
  done

lemma set_pml4_only_idle [wp]:
  "\<lbrace>only_idle\<rbrace> set_pml4 p pml4 \<lbrace>\<lambda>_. only_idle\<rbrace>"
  by (wp only_idle_lift)



lemma set_pml4_valid_ioc[wp]:
  "\<lbrace>valid_ioc\<rbrace> set_pml4 p pml4 \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  apply (simp add: set_pml4_def)
  apply (wp set_object_valid_ioc_no_caps get_object_wp)
  by (clarsimp simp: a_type_simps obj_at_def is_tcb is_cap_table
              split: kernel_object.splits arch_kernel_obj.splits)

lemma set_pml4_vms[wp]:
  "\<lbrace>valid_machine_state\<rbrace> set_pml4 p pml4 \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  apply (simp add: set_pml4_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: valid_machine_state_def in_user_frame_def obj_at_def
                 split: kernel_object.splits arch_kernel_obj.splits)
  apply (frule_tac x=pa in spec)
  apply (frule_tac x=p in spec)
  apply (clarsimp simp add: a_type_simps)
  apply (rule_tac x=sz in exI)
  apply (clarsimp simp: a_type_simps)
  done
  
lemma set_pdpt_only_idle [wp]:
  "\<lbrace>only_idle\<rbrace> set_pdpt p pdpt \<lbrace>\<lambda>_. only_idle\<rbrace>"
  by (wp only_idle_lift)


lemma set_pdpt_equal_mappings [wp]:
  "\<lbrace>equal_kernel_mappings\<rbrace> set_pdpt p pdpt \<lbrace>\<lambda>rv. equal_kernel_mappings\<rbrace>"
  by (simp add: set_pdpt_def | wp set_object_equal_mappings get_object_wp)+


lemma set_pdpt_valid_global_vspace_mappings:
  "\<lbrace>\<lambda>s. valid_global_vspace_mappings s \<and> valid_global_objs s \<and> p \<notin> global_refs s\<rbrace>
      set_pdpt p pdpt
   \<lbrace>\<lambda>rv. valid_global_vspace_mappings\<rbrace>"
  apply (simp add: set_pdpt_def)
  apply (wp set_object_global_vspace_mappings get_object_wp)
  apply (clarsimp simp: obj_at_def a_type_def
                 split: kernel_object.split_asm
                        arch_kernel_obj.split_asm)
  done


lemma set_pdpt_kernel_window[wp]:
  "\<lbrace>pspace_in_kernel_window\<rbrace> set_pdpt p pdpt \<lbrace>\<lambda>rv. pspace_in_kernel_window\<rbrace>"
  apply (simp add: set_pdpt_def)
  apply (wp set_object_pspace_in_kernel_window get_object_wp)
  apply (clarsimp simp: obj_at_def a_type_def
                 split: kernel_object.split_asm
                        arch_kernel_obj.split_asm)
  done


lemma set_pdpt_caps_kernel_window[wp]:
  "\<lbrace>cap_refs_in_kernel_window\<rbrace> set_pdpt p pdpt \<lbrace>\<lambda>rv. cap_refs_in_kernel_window\<rbrace>"
  apply (simp add: set_pdpt_def)
  apply (wp set_object_cap_refs_in_kernel_window get_object_wp)
  apply (clarsimp simp: obj_at_def a_type_def
                 split: kernel_object.split_asm
                        arch_kernel_obj.split_asm)
  done


lemma set_pdpt_valid_ioc[wp]:
  "\<lbrace>valid_ioc\<rbrace> set_pdpt p pdpt \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  apply (simp add: set_pdpt_def)
  apply (wp set_object_valid_ioc_no_caps get_object_wp)
  by (clarsimp simp: a_type_simps obj_at_def is_tcb is_cap_table
              split: kernel_object.splits arch_kernel_obj.splits)


lemma set_pdpt_vms[wp]:
  "\<lbrace>valid_machine_state\<rbrace> set_pdpt p pdpt \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  apply (simp add: set_pdpt_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: valid_machine_state_def in_user_frame_def obj_at_def
                 split: kernel_object.splits arch_kernel_obj.splits)
  apply (frule_tac x=pa in spec)
  apply (frule_tac x=p in spec)
  apply (clarsimp simp add: a_type_simps)
  apply (rule_tac x=sz in exI)
  apply (clarsimp simp: a_type_simps)
  done
  
lemma set_pd_only_idle [wp]:
  "\<lbrace>only_idle\<rbrace> set_pd p pd \<lbrace>\<lambda>_. only_idle\<rbrace>"
  by (wp only_idle_lift)


lemma set_pd_equal_mappings [wp]:
  "\<lbrace>equal_kernel_mappings\<rbrace> set_pd p pd \<lbrace>\<lambda>rv. equal_kernel_mappings\<rbrace>"
  by (simp add: set_pd_def | wp set_object_equal_mappings get_object_wp)+


lemma set_pd_valid_global_vspace_mappings:
  "\<lbrace>\<lambda>s. valid_global_vspace_mappings s \<and> valid_global_objs s \<and> p \<notin> global_refs s\<rbrace>
      set_pd p pd
   \<lbrace>\<lambda>rv. valid_global_vspace_mappings\<rbrace>"
  apply (simp add: set_pd_def)
  apply (wp set_object_global_vspace_mappings get_object_wp)
  apply (clarsimp simp: obj_at_def a_type_def
                 split: kernel_object.split_asm
                        arch_kernel_obj.split_asm)
  done


lemma set_pd_kernel_window[wp]:
  "\<lbrace>pspace_in_kernel_window\<rbrace> set_pd p pd \<lbrace>\<lambda>rv. pspace_in_kernel_window\<rbrace>"
  apply (simp add: set_pd_def)
  apply (wp set_object_pspace_in_kernel_window get_object_wp)
  apply (clarsimp simp: obj_at_def a_type_def
                 split: kernel_object.split_asm
                        arch_kernel_obj.split_asm)
  done


lemma set_pd_caps_kernel_window[wp]:
  "\<lbrace>cap_refs_in_kernel_window\<rbrace> set_pd p pd \<lbrace>\<lambda>rv. cap_refs_in_kernel_window\<rbrace>"
  apply (simp add: set_pd_def)
  apply (wp set_object_cap_refs_in_kernel_window get_object_wp)
  apply (clarsimp simp: obj_at_def a_type_def
                 split: kernel_object.split_asm
                        arch_kernel_obj.split_asm)
  done


lemma set_pd_valid_ioc[wp]:
  "\<lbrace>valid_ioc\<rbrace> set_pd p pd \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  apply (simp add: set_pd_def)
  apply (wp set_object_valid_ioc_no_caps get_object_wp)
  by (clarsimp simp: a_type_simps obj_at_def is_tcb is_cap_table
              split: kernel_object.splits arch_kernel_obj.splits)


lemma set_pd_vms[wp]:
  "\<lbrace>valid_machine_state\<rbrace> set_pd p pd \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  apply (simp add: set_pd_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: valid_machine_state_def in_user_frame_def obj_at_def
                 split: kernel_object.splits arch_kernel_obj.splits)
  apply (frule_tac x=pa in spec)
  apply (frule_tac x=p in spec)
  apply (clarsimp simp add: a_type_simps)
  apply (rule_tac x=sz in exI)
  apply (clarsimp simp: a_type_simps)
  done
  
crunch valid_irq_states[wp]: set_pt, set_pd, set_pdpt, set_pml4 "valid_irq_states"
  (wp: crunch_wps)

lemma set_pt_invs:
  "\<lbrace>invs and (\<lambda>s. \<forall>i. wellformed_pte (pt i)) and
    (\<lambda>s. (\<exists>\<rhd>p) s \<longrightarrow> valid_arch_obj (PageTable pt) s) and
    (\<lambda>s. \<exists>slot asid. caps_of_state s slot =
         Some (cap.ArchObjectCap (arch_cap.PageTableCap p asid)) \<and>
         (pt = (\<lambda>x. InvalidPTE) \<or> asid \<noteq> None)) and
    (\<lambda>s. \<forall>ref. (ref \<unrhd> p) s \<longrightarrow>
            (\<forall>x p. pte_ref_pages (pt x) = Some p \<longrightarrow>
                    (\<exists>p' cap. caps_of_state s p' = Some cap \<and>
                         p \<in> obj_refs cap \<and>
                         vs_cap_ref cap =
                         Some (VSRef (ucast x) (Some APageTable) # ref))))\<rbrace>
   set_pt p pt
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (rule hoare_pre)
   apply (wp set_pt_valid_objs set_pt_iflive set_pt_zombies
             set_pt_zombies_state_refs set_pt_valid_mdb
             set_pt_valid_idle set_pt_ifunsafe set_pt_reply_caps
             set_pt_valid_arch_state set_pt_valid_global set_pt_cur
             set_pt_reply_masters valid_irq_node_typ
             valid_irq_handlers_lift
             set_pt_valid_global_vspace_mappings)
  apply (clarsimp dest!: valid_objs_caps)
  apply (rule conjI[rotated])
  apply (subgoal_tac "p \<notin> global_refs s", simp add: global_refs_def)
  apply (frule (1) valid_global_refsD2)
  apply (clarsimp simp add: cap_range_def is_pt_cap_def)
  apply (thin_tac "ALL x. P x" for P)+
  apply (clarsimp simp: valid_arch_caps_def unique_table_caps_def)
  apply (drule_tac x=aa in spec, drule_tac x=ba in spec)
  apply (drule_tac x=a in spec, drule_tac x=b in spec)
  apply (clarsimp simp: is_pt_cap_def cap_asid_def)
  done


(* FIXME: move to Invariants_A *)
lemma invs_valid_asid_table [elim!]:
  "invs s \<Longrightarrow> valid_asid_table (x64_asid_table (arch_state s)) s"
  by (simp add: invs_def valid_state_def valid_arch_state_def)


(* FIXME: move to Invariants_A *)
lemma valid_asid_table_ran:
  "valid_asid_table at s \<Longrightarrow> \<forall>p\<in>ran at. asid_pool_at p s"
  by (simp add: invs_def valid_state_def valid_arch_state_def
                valid_asid_table_def)


(* FIXME x64: vs_lookup joy *)
lemma vs_lookup_pages_pt_eq:
  "\<lbrakk>valid_arch_objs s;
    \<forall>p\<in>ran (x64_asid_table (arch_state s)). asid_pool_at p s;
    page_table_at p s\<rbrakk>
   \<Longrightarrow> (ref \<unrhd> p) s = (ref \<rhd> p) s"
   (*
  apply (rule iffI[rotated])
   apply (erule vs_lookup_pages_vs_lookupI)
  apply (erule (2) vs_lookup_pagesE_alt)
     apply (clarsimp simp: obj_at_def)+
   apply (clarsimp simp: obj_at_def pde_ref_pages_def
                  split: pde.splits)
   apply (erule (5) vs_lookup_pdI)
  apply (clarsimp simp: obj_at_def pte_ref_pages_def
                 split: pte.splits)
  done*)
  sorry


lemmas invs_ran_asid_table = invs_valid_asid_table[THEN valid_asid_table_ran]


(* NOTE: we use vs_lookup in the precondition because in this case,
         both are equivalent, but vs_lookup is generally preserved
         by store_pte while vs_lookup_pages might not. *)
lemma store_pte_invs [wp]:
  "\<lbrace>invs and (\<lambda>s. (\<exists>\<rhd>(p && ~~ mask pt_bits)) s \<longrightarrow> valid_pte pte s) and
    (\<lambda>s. wellformed_pte pte) and
    (\<lambda>s. \<exists>slot asid. caps_of_state s slot =
         Some (ArchObjectCap
                 (PageTableCap (p && ~~ mask pt_bits) asid)) \<and>
         (pte = InvalidPTE \<or> asid \<noteq> None)) and
    (\<lambda>s. \<forall>ref. (ref \<rhd> (p && ~~ mask pt_bits)) s \<longrightarrow>
            (\<forall>q. pte_ref_pages pte = Some q \<longrightarrow>
                    (\<exists>p' cap. caps_of_state s p' = Some cap \<and>
                         q \<in> obj_refs cap \<and>
                         vs_cap_ref cap =
                         Some (VSRef (p && mask pt_bits >> word_size_bits)
                                     (Some APageTable) # ref))))\<rbrace>
  store_pte p pte \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: store_pte_def)
  apply (wp dmo_invs set_pt_invs)
  apply clarsimp
  apply (intro conjI)
     apply (drule invs_valid_objs)
     apply (fastforce simp: valid_objs_def dom_def obj_at_def valid_obj_def wellformed_arch_obj_def)
    apply clarsimp
    apply (drule (1) valid_arch_objsD, fastforce)
    apply simp
   apply (thin_tac "All _")
   apply (rule exI)+
   apply (rule conjI, assumption)
   subgoal premises prems for \<dots> asid
   proof (cases asid)
    case (Some a) from this show ?thesis
     by fastforce
    next
    case None from this prems show ?thesis
     apply clarsimp
     apply (rule ext)
     apply clarsimp
     apply (frule invs_pd_caps)
     apply (clarsimp simp add: valid_table_caps_def simp del: HOL.imp_disjL)
     apply (spec "p && ~~ mask pt_bits")
     apply (drule spec)+
     apply (erule impE, assumption)
     by (simp add: is_pt_cap_def cap_asid_def empty_table_def obj_at_def)
  qed
  apply (clarsimp simp: obj_at_def)
  apply (intro impI conjI allI)
   apply (drule (2) vs_lookup_pages_pt_eq[OF invs_arch_objs invs_ran_asid_table,
                                          THEN iffD1, rotated -1])
    apply (clarsimp simp: obj_at_def a_type_simps)
   apply (drule spec, erule impE, assumption)+
   apply (erule exEI)+
   apply clarsimp
   apply (rule sym)
   apply (simp add: word_size_bits_def)
   apply (rule ucast_ucast_len)
   apply (rule shiftr_less_t2n)
   using and_mask_less'[of 12 p]
   apply (simp add: bit_simps)
  subgoal for \<dots> pa
   apply (thin_tac "All _", thin_tac "_ \<longrightarrow> _", thin_tac "_ \<or> _")
   apply (frule invs_valid_vs_lookup)
   apply (simp add: valid_vs_lookup_def)
   apply (spec pa)
   apply (drule spec, erule impE)
    apply (erule vs_lookup_pages_step)
    by (fastforce simp: vs_lookup_pages1_def obj_at_def
                          vs_refs_pages_def graph_of_def image_def) simp
  done


lemma set_asid_pool_iflive [wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap s\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. if_live_then_nonz_cap s\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wp get_object_wp set_object_iflive)
  apply (clarsimp split: kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp: obj_at_def)
  done


lemma set_asid_pool_zombies [wp]:
  "\<lbrace>\<lambda>s. zombies_final s\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. zombies_final s\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wp get_object_wp set_object_zombies)
  apply (clarsimp split: kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp: obj_at_def)
  done


lemma set_asid_pool_zombies_state_refs [wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. P (state_refs_of s)\<rbrace>"
  apply (clarsimp simp: set_asid_pool_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp split: kernel_object.splits arch_kernel_obj.splits)
  apply (erule rsubst [where P=P])
  apply (rule ext)
  apply (clarsimp simp: obj_at_def state_refs_of_def split: option.splits)
  done


lemma set_asid_pool_cdt [wp]:
  "\<lbrace>\<lambda>s. P (cdt s)\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. P (cdt s)\<rbrace>"
  apply (clarsimp simp: set_asid_pool_def)
  apply (wp get_object_wp)
  apply simp
  done


lemma set_asid_pool_caps_of_state [wp]:
  "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  apply (simp add: set_asid_pool_def get_object_def bind_assoc set_object_def)
  apply wp
  apply clarsimp
  apply (subst cte_wp_caps_of_lift)
   prefer 2
   apply assumption
   subgoal for _ y
    by (cases y, auto simp: cte_wp_at_cases)
  done

lemma set_asid_pool_valid_mdb [wp]:
  "\<lbrace>\<lambda>s. valid_mdb s\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. valid_mdb s\<rbrace>"
  apply (rule valid_mdb_lift)
    apply wp
  apply (clarsimp simp: set_asid_pool_def)
  apply (wp get_object_wp)
  apply simp
  done


lemma set_asid_pool_valid_idle [wp]:
  "\<lbrace>\<lambda>s. valid_idle s\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. valid_idle s\<rbrace>"
  apply (wp valid_idle_lift)
  apply (simp add: set_asid_pool_def)
  apply (wp get_object_wp)
  apply simp
  done


lemma set_asid_pool_ifunsafe [wp]:
  "\<lbrace>\<lambda>s. if_unsafe_then_cap s\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. if_unsafe_then_cap s\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wp get_object_wp set_object_ifunsafe)
  apply (clarsimp split: kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp: obj_at_def)
  done


lemma set_asid_pool_reply_caps [wp]:
  "\<lbrace>\<lambda>s. valid_reply_caps s\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. valid_reply_caps s\<rbrace>"
  by (wp valid_reply_caps_st_cte_lift)


lemma set_asid_pool_reply_masters [wp]:
  "\<lbrace>valid_reply_masters\<rbrace>
   set_asid_pool p ap
   \<lbrace>\<lambda>_. valid_reply_masters\<rbrace>"
  by (wp valid_reply_masters_cte_lift)


crunch global_ref [wp]: set_asid_pool "\<lambda>s. P (global_refs s)"
  (wp: crunch_wps)


crunch arch [wp]: set_asid_pool "\<lambda>s. P (arch_state s)"
  (wp: crunch_wps)


crunch idle [wp]: set_asid_pool "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps)


crunch irq [wp]: set_asid_pool "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps)

crunch valid_irq_states[wp]: set_asid_pool "valid_irq_states"
  (wp: crunch_wps)

lemma set_asid_pool_valid_global [wp]:
  "\<lbrace>\<lambda>s. valid_global_refs s\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. valid_global_refs s\<rbrace>"
  by (wp valid_global_refs_cte_lift)


crunch interrupt_states[wp]: set_asid_pool "\<lambda>s. P (interrupt_states s)"
  (wp: crunch_wps)


lemma set_asid_pool_arch_objs_unmap':
  "\<lbrace>valid_arch_objs and (\<lambda>s. (\<exists>\<rhd>p) s \<longrightarrow> valid_arch_obj (ASIDPool ap) s) and
    obj_at (\<lambda>ko. \<exists>ap'. ko = ArchObj (ASIDPool ap') \<and> graph_of ap \<subseteq> graph_of ap') p\<rbrace>
  set_asid_pool p ap \<lbrace>\<lambda>_. valid_arch_objs\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wp get_object_wp set_object_arch_objs)
  apply (clarsimp simp: obj_at_def obj_at_def)
  apply (rule conjI)
   apply (clarsimp simp: a_type_def split: kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp: vs_refs_def)
  apply fastforce
  done


lemma set_asid_pool_arch_objs_unmap:
  "\<lbrace>valid_arch_objs and ko_at (ArchObj (ASIDPool ap)) p\<rbrace>
  set_asid_pool p (ap |` S)  \<lbrace>\<lambda>_. valid_arch_objs\<rbrace>"
  apply (wp set_asid_pool_arch_objs_unmap')
  apply (clarsimp simp: obj_at_def graph_of_restrict_map)
  apply (drule valid_arch_objsD, simp add: obj_at_def, assumption)
  apply simp
  by (auto simp: obj_at_def dest!: ran_restrictD)


lemma set_asid_pool_table_caps [wp]:
  "\<lbrace>valid_table_caps\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>_. valid_table_caps\<rbrace>"
  apply (simp add: valid_table_caps_def)
  apply (rule hoare_lift_Pf2 [where f=caps_of_state];wp?)
  apply (simp add: set_asid_pool_def set_object_def)
  apply (wp get_object_wp)
  by (clarsimp split: kernel_object.splits arch_kernel_obj.splits)
     (fastforce simp: obj_at_def empty_table_def)
  


(* FIXME: Move to Invariants_A *)
lemma vs_lookup_pages_stateI:
  assumes 1: "(ref \<unrhd> p) s"
  assumes ko: "\<And>ko p. ko_at ko p s \<Longrightarrow> obj_at (\<lambda>ko'. vs_refs_pages ko \<subseteq> vs_refs_pages ko') p s'"
  assumes table: "graph_of (x64_asid_table (arch_state s)) \<subseteq> graph_of (x64_asid_table (arch_state s'))"
  shows "(ref \<unrhd> p) s'"
  using 1 vs_lookup_pages_sub [OF ko table] by blast
  
lemma set_asid_pool_vs_lookup_unmap':
  "\<lbrace>valid_vs_lookup and
    obj_at (\<lambda>ko. \<exists>ap'. ko = ArchObj (ASIDPool ap') \<and> graph_of ap \<subseteq> graph_of ap') p\<rbrace>
  set_asid_pool p ap \<lbrace>\<lambda>_. valid_vs_lookup\<rbrace>"
  apply (simp add: valid_vs_lookup_def pred_conj_def)
  apply (rule hoare_lift_Pf2 [where f=caps_of_state];wp?)
  apply (simp add: set_asid_pool_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def simp del: fun_upd_apply del: disjCI
                  split: kernel_object.splits arch_kernel_obj.splits)
  subgoal for \<dots> pa ref
    apply (spec pa)
    apply (spec ref)
    apply (erule impE)
     apply (erule vs_lookup_pages_stateI)
      by (clarsimp simp: obj_at_def vs_refs_pages_def split: split_if_asm)
         fastforce+
  done


lemma set_asid_pool_vs_lookup_unmap:
  "\<lbrace>valid_vs_lookup and ko_at (ArchObj (ASIDPool ap)) p\<rbrace>
  set_asid_pool p (ap |` S) \<lbrace>\<lambda>_. valid_vs_lookup\<rbrace>"
  apply (wp set_asid_pool_vs_lookup_unmap')
  by (clarsimp simp: obj_at_def
                 elim!: subsetD [OF graph_of_restrict_map])


lemma valid_pte_typ_at:
  "(\<And>T p. typ_at (AArch T) p s = typ_at (AArch T) p s') \<Longrightarrow>
   valid_pte pte s = valid_pte pte s'"
  by (case_tac pte, simp+)


lemma valid_pde_typ_at:
  "(\<And>T p. typ_at (AArch T) p s = typ_at (AArch T) p s') \<Longrightarrow>
   valid_pde pde s = valid_pde pde s'"
  by (case_tac pde, simp+)

lemma valid_pdpte_typ_at:
  "(\<And>T p. typ_at (AArch T) p s = typ_at (AArch T) p s') \<Longrightarrow>
   valid_pdpte pdpte s = valid_pdpte pdpte s'"
  by (case_tac pdpte, simp+)
  
lemma valid_pml4e_typ_at:
  "(\<And>T p. typ_at (AArch T) p s = typ_at (AArch T) p s') \<Longrightarrow>
   valid_pml4e pml4e s = valid_pml4e pml4e s'"
  by (case_tac pml4e, simp+)

lemma set_asid_pool_global_objs [wp]:
  "\<lbrace>valid_global_objs and valid_arch_state\<rbrace>
   set_asid_pool p ap
   \<lbrace>\<lambda>_. valid_global_objs\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp del: fun_upd_apply
                  split: kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp: valid_global_objs_def valid_ao_at_def)
  apply (rule conjI)
   apply (clarsimp simp: obj_at_def)
   apply (rule conjI)
    subgoal by (clarsimp simp: valid_arch_state_def obj_at_def a_type_def)
   apply clarsimp
   apply (erule (1) valid_arch_obj_same_type)
   subgoal by (simp add: a_type_def)
  apply (rule conjI)
   subgoal by (clarsimp simp: obj_at_def valid_arch_state_def a_type_def)
  apply (clarsimp simp: obj_at_def)
  apply (drule (1) bspec)
  by clarsimp


crunch v_ker_map[wp]: set_asid_pool "valid_kernel_mappings"
  (ignore: set_object wp: set_object_v_ker_map crunch_wps)


lemma set_asid_pool_restrict_asid_map:
  "\<lbrace>valid_asid_map and ko_at (ArchObj (ASIDPool ap)) p and
    (\<lambda>s. \<forall>asid. asid \<le> mask asid_bits \<longrightarrow> ucast asid \<notin> S \<longrightarrow>
                x64_asid_table (arch_state s) (asid_high_bits_of asid) = Some p \<longrightarrow>
                x64_asid_map (arch_state s) asid = None)\<rbrace>
  set_asid_pool p (ap |` S) \<lbrace>\<lambda>_. valid_asid_map\<rbrace>"
  apply (simp add: set_asid_pool_def valid_asid_map_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp split: kernel_object.splits arch_kernel_obj.splits
                  simp del: fun_upd_apply)
  apply (drule(1) bspec)
  apply (clarsimp simp: vspace_at_asid_def obj_at_def graph_of_def)
  apply (drule subsetD, erule domI)
  apply simp
  apply (drule spec, drule(1) mp)
  apply simp
  apply (erule vs_lookupE)
  apply (rule vs_lookupI, simp)
  apply (clarsimp simp: vs_asid_refs_def graph_of_def)
  apply (drule rtranclD)
  apply (erule disjE, clarsimp)
  apply clarsimp
  apply (drule tranclD)
  apply clarsimp
  apply (rule r_into_rtrancl)
  apply (drule vs_lookup1D)
  apply clarsimp
  apply (subst vs_lookup1_def)
  apply (clarsimp simp: obj_at_def)
  apply (erule rtranclE)
   apply (clarsimp simp: vs_refs_def graph_of_def)
   apply (rule image_eqI[where x="(_, _)"])
    apply (simp add: split_def)
   apply (clarsimp simp: restrict_map_def)
   apply (drule ucast_up_inj, simp)
   apply (simp add: mask_asid_low_bits_ucast_ucast)
   apply (drule ucast_up_inj, simp)
   apply clarsimp
  apply clarsimp
  apply (drule vs_lookup1_trans_is_append)
  apply clarsimp
  apply (drule vs_lookup1D)
  by clarsimp


lemma set_asid_pool_asid_map_unmap:
  "\<lbrace>valid_asid_map and ko_at (ArchObj (ASIDPool ap)) p and
    (\<lambda>s. \<forall>asid. asid \<le> mask asid_bits \<longrightarrow>
                ucast asid = x \<longrightarrow>
                x64_asid_table (arch_state s) (asid_high_bits_of asid) = Some p \<longrightarrow>
                x64_asid_map (arch_state s) asid = None)\<rbrace>
       set_asid_pool p (ap(x := None)) \<lbrace>\<lambda>_. valid_asid_map\<rbrace>"
  using set_asid_pool_restrict_asid_map[where S="- {x}"]
  by (simp add: restrict_map_def fun_upd_def if_flip)


lemma set_asid_pool_arch_objs_unmap_single:
  "\<lbrace>valid_arch_objs and ko_at (ArchObj (ASIDPool ap)) p\<rbrace>
       set_asid_pool p (ap(x := None)) \<lbrace>\<lambda>_. valid_arch_objs\<rbrace>"
  using set_asid_pool_arch_objs_unmap[where S="- {x}"]
  by (simp add: restrict_map_def fun_upd_def if_flip)


lemma set_asid_pool_only_idle [wp]:
  "\<lbrace>only_idle\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>_. only_idle\<rbrace>"
  by (wp only_idle_lift set_asid_pool_typ_at)


lemma set_asid_pool_equal_mappings [wp]:
  "\<lbrace>equal_kernel_mappings\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>rv. equal_kernel_mappings\<rbrace>"
  by (simp add: set_asid_pool_def | wp set_object_equal_mappings get_object_wp)+
  
lemma set_asid_pool_valid_global_vspace_mappings[wp]:
  "\<lbrace>valid_global_vspace_mappings\<rbrace>
      set_asid_pool p ap \<lbrace>\<lambda>rv. valid_global_vspace_mappings\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wp set_object_global_vspace_mappings get_object_wp)
  including unfold_objects
  by (clarsimp simp: a_type_def)


lemma set_asid_pool_kernel_window[wp]:
  "\<lbrace>pspace_in_kernel_window\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>rv. pspace_in_kernel_window\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wp set_object_pspace_in_kernel_window get_object_wp)
  including unfold_objects_asm
  by (clarsimp simp: a_type_def)


lemma set_asid_pool_caps_kernel_window[wp]:
  "\<lbrace>cap_refs_in_kernel_window\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>rv. cap_refs_in_kernel_window\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wp set_object_cap_refs_in_kernel_window get_object_wp)
  including unfold_objects_asm
  by clarsimp


lemma set_asid_pool_valid_ioc[wp]:
  "\<lbrace>valid_ioc\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wp set_object_valid_ioc_no_caps get_object_inv)
  including unfold_objects
  by (clarsimp simp: valid_def get_object_def simpler_gets_def assert_def
          return_def fail_def bind_def
          a_type_simps is_tcb is_cap_table)


lemma set_asid_pool_vms[wp]:
  "\<lbrace>valid_machine_state\<rbrace> set_asid_pool p S \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def)
  apply (wp get_object_wp)
  including unfold_objects
  apply (clarsimp simp: valid_machine_state_def in_user_frame_def)
  subgoal for \<dots> pa
   apply (frule spec[of _ pa])
   apply (frule spec[of _ p])
   apply (clarsimp simp add: a_type_simps)
   subgoal for sz
     apply (rule exI[of _ sz])
     by (clarsimp simp: a_type_simps)
   done
  done


lemma set_asid_pool_invs_restrict:
  "\<lbrace>invs and ko_at (ArchObj (ASIDPool ap)) p and
    (\<lambda>s. \<forall>asid. asid \<le> mask asid_bits \<longrightarrow> ucast asid \<notin> S \<longrightarrow>
                x64_asid_table (arch_state s) (asid_high_bits_of asid) = Some p \<longrightarrow>
                x64_asid_map (arch_state s) asid = None)\<rbrace>
       set_asid_pool p (ap |` S) \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def
                   valid_arch_caps_def)
  apply (rule hoare_pre,
         wp valid_irq_node_typ set_asid_pool_typ_at
            set_asid_pool_arch_objs_unmap  valid_irq_handlers_lift
            set_asid_pool_vs_lookup_unmap set_asid_pool_restrict_asid_map)
  apply simp
  done


lemmas set_asid_pool_cte_wp_at1[wp]
    = hoare_cte_wp_caps_of_state_lift [OF set_asid_pool_caps_of_state]


lemma mdb_cte_at_set_asid_pool[wp]:
  "\<lbrace>\<lambda>s. mdb_cte_at (swp (cte_wp_at (op \<noteq> cap.NullCap)) s) (cdt s)\<rbrace>
   set_asid_pool y pool
   \<lbrace>\<lambda>r s. mdb_cte_at (swp (cte_wp_at (op \<noteq> cap.NullCap)) s) (cdt s)\<rbrace>"
  apply (clarsimp simp:mdb_cte_at_def)
  apply (simp only: imp_conv_disj)
  apply (wp hoare_vcg_disj_lift hoare_vcg_all_lift)
done

lemma set_asid_pool_invs_unmap:
  "\<lbrace>invs and ko_at (ArchObj (ASIDPool ap)) p and
    (\<lambda>s. \<forall>asid. asid \<le> mask asid_bits \<longrightarrow> ucast asid = x \<longrightarrow>
                x64_asid_table (arch_state s) (asid_high_bits_of asid) = Some p \<longrightarrow>
                x64_asid_map (arch_state s) asid = None)\<rbrace>
       set_asid_pool p (ap(x := None)) \<lbrace>\<lambda>_. invs\<rbrace>"
  using set_asid_pool_invs_restrict[where S="- {x}"]
  by (simp add: restrict_map_def fun_upd_def if_flip)


lemma valid_slots_typ_at:
  assumes x: "\<And>T p. \<lbrace>typ_at (AArch T) p\<rbrace> f \<lbrace>\<lambda>rv. typ_at (AArch T) p\<rbrace>"
  assumes y: "\<And>p. \<lbrace>\<exists>\<rhd> p\<rbrace> f \<lbrace>\<lambda>rv. \<exists>\<rhd> p\<rbrace>"
  shows "\<lbrace>valid_slots m\<rbrace> f \<lbrace>\<lambda>rv. valid_slots m\<rbrace>"
  unfolding valid_slots_def
  apply (cases m; clarsimp)
  apply (case_tac a; clarsimp)
  apply (wp x y hoare_vcg_const_Ball_lift valid_pte_lift valid_pde_lift valid_pdpte_lift valid_pml4e_lift
             pte_at_atyp pde_at_atyp pdpte_at_atyp pml4e_at_atyp)
  done


lemma ucast_ucast_id:
  "(len_of TYPE('a)) < (len_of TYPE('b)) \<Longrightarrow> ucast ((ucast (x::('a::len) word))::('b::len) word) = x"
  by (auto intro: ucast_up_ucast_id simp: is_up_def source_size_def target_size_def word_size)


lemma ucast_le_ucast:
  "len_of TYPE('a) \<le> len_of TYPE('b) \<Longrightarrow>
   (ucast x \<le> ((ucast (y :: ('a::len) word)) :: ('b::len) word)) = (x \<le> y)"
  apply (simp add: word_le_nat_alt unat_ucast)
  apply (subst mod_less)
   apply(rule less_le_trans[OF unat_lt2p], simp)
  apply (subst mod_less)
   apply(rule less_le_trans[OF unat_lt2p], simp)
  apply simp
  done
  
definition canonical_address :: "obj_ref \<Rightarrow> bool"
where 
  "canonical_address x \<equiv> ((scast ((ucast x) :: 48 word)) :: 64 word) = x"
  
(* FIXME x64: why dear god *)
lemma test: 
  "canonical_address x = (x \<le> mask 47 \<or> x > ~~ mask 47)"
  sorry
  
  
(* FIXME x64: fuck signed casts and x64 *)
lemma kernel_base_kernel_mapping_slots:
  "\<lbrakk>x < pptr_base; canonical_address x\<rbrakk> \<Longrightarrow> ucast (get_pml4_index x) \<notin> kernel_mapping_slots"
  apply (simp add: kernel_mapping_slots_def pptr_base_def pptrBase_def bit_simps get_pml4_index_def)
  apply (subst ucast_le_ucast[symmetric, where 'a=9 and 'b=64])
   apply simp
  apply (subst ucast_ucast_mask)
  apply (simp add: ucast_def)
  apply (subst word_not_le)
  apply (simp add: mask_def)
  apply (simp add: test mask_def)
  apply (word_bitwise, auto)
  done

(* FIXME x64: review *)
lemma lookup_pdpt_slot_looks_up [wp]:
  "\<lbrace>ref \<rhd> pm and K (is_aligned pm pml4_bits \<and> vptr < pptr_base \<and> canonical_address vptr)
   and valid_arch_state and valid_arch_objs and equal_kernel_mappings
   and pspace_aligned and valid_global_objs\<rbrace>
  lookup_pdpt_slot pm vptr
  \<lbrace>\<lambda>pdpt_slot. (VSRef (get_pml4_index vptr << word_size_bits >> word_size_bits) (Some APageMapL4) # ref) \<rhd> (pdpt_slot && ~~ mask pdpt_bits)\<rbrace>, -"
  apply (simp add: lookup_pdpt_slot_def)
  apply (wp get_pml4e_wp|wpc)+
  apply clarsimp
  apply (rule vs_lookup_step, assumption)
  apply (clarsimp simp: vs_lookup1_def lookup_pml4_slot_def Let_def pml4_shifting pml4_shifting_dual)
  apply (rule exI, rule conjI, assumption)
  subgoal for s _ x
    apply (prove "ptrFromPAddr x + ((get_pdpt_index vptr << word_size_bits)) && ~~ mask pdpt_bits = ptrFromPAddr x")
     apply (prove "is_aligned (ptrFromPAddr x) pdpt_bits")
      apply (drule (2) valid_arch_objsD)
      apply clarsimp
      apply (erule_tac x="ucast (get_pml4_index vptr << word_size_bits >> word_size_bits)" in ballE)
      apply (thin_tac "obj_at P x s" for P x)+
      apply (clarsimp simp: obj_at_def invs_def valid_state_def valid_pspace_def pspace_aligned_def)
      apply (drule bspec, blast)
      apply (clarsimp simp: a_type_def bit_simps
                      split: kernel_object.splits arch_kernel_obj.splits split_if_asm)
      apply (frule kernel_mapping_slots_empty_pml4eI)
        apply ((simp add: obj_at_def)+)[4]
      apply (clarsimp simp: pml4e_ref_def)
      apply (erule is_aligned_global_pdpt)
      apply simp+
     apply (subgoal_tac "get_pdpt_index vptr << word_size_bits < 2 ^ pdpt_bits")
      apply (subst is_aligned_add_or, (simp add: )+)
      apply (subst word_ao_dist)
      apply (subst mask_out_sub_mask [where x="get_pdpt_index vptr << word_size_bits"])
      apply (subst less_mask_eq, simp+)
      apply (subst is_aligned_neg_mask_eq, simp)
      apply (clarsimp simp: valid_arch_state_def valid_global_pdpts_def)
     apply (simp add: get_pdpt_index_def)
     apply (rule shiftl_less_t2n, simp add: bit_simps)
      apply (rule and_mask_less'[where n=ptTranslationBits, unfolded ptTranslationBits_def, simplified])
      apply (simp)
     apply (simp add: bit_simps)
    apply (simp add: bit_simps get_pml4_index_def)
    apply (subst shiftl_shiftr_id)
      apply (simp add: word_bits_def)+
     apply word_bitwise
    apply (subst (asm) shiftl_shiftr_id)
      apply (simp add: word_bits_def)+
     apply word_bitwise
    apply (erule vs_refs_pml4I)
     apply (erule (1) kernel_base_kernel_mapping_slots[unfolded get_pml4_index_def bit_simps, simplified])
    apply (intro allI impI)
    apply (simp add: nth_shiftr)
    done
   done
  
(* FIXME x64: what should this look like, requires recursion down tables 
lemma lookup_pt_slot_looks_up [wp]:
  "\<lbrace>ref \<rhd> pm and K (is_aligned pm pml4_bits \<and> vptr < pptr_base \<and> canonical_address vptr)
   and valid_arch_state and valid_arch_objs and equal_kernel_mappings
   and pspace_aligned and valid_global_objs\<rbrace>
  lookup_pt_slot pm vptr
  \<lbrace>\<lambda>pt_slot. (VSRef (get_pd_index vptr << word_size_bits >> word_size_bits) (Some APageDirectory) # ref) \<rhd> (pt_slot && ~~ mask pt_bits)\<rbrace>, -"
  apply (simp add: lookup_pt_slot_def)
  apply (wp get_pde_wp|wpc)+
  apply clarsimp
  apply (rule vs_lookup_step, assumption)
  apply (clarsimp simp: vs_lookup1_def lookup_pd_slot_def Let_def pd_shifting pd_shifting_dual)
  apply (rule exI, rule conjI, assumption)
  subgoal for s _ x
    apply (prove "ptrFromPAddr x + ((vptr >> 12) && 0xFF << 2) && ~~ mask pt_bits = ptrFromPAddr x")
     apply (prove "is_aligned (ptrFromPAddr x) 10")
      apply (drule (2) valid_arch_objsD)
      apply clarsimp
      apply (erule_tac x="ucast (vptr >> 20 << 2 >> 2)" in ballE)
      apply (thin_tac "obj_at P x s" for P x)+
      apply (clarsimp simp: obj_at_def invs_def valid_state_def valid_pspace_def pspace_aligned_def)
      apply (drule bspec, blast)
      apply (clarsimp simp: a_type_def
                      split: kernel_object.splits arch_kernel_obj.splits split_if_asm)
      apply (frule kernel_mapping_slots_empty_pdeI)
        apply ((simp add: obj_at_def)+)[4]
      apply (clarsimp simp: pde_ref_def)
      apply (erule is_aligned_global_pt[unfolded pt_bits_def pageBits_def, simplified])
      apply simp+
     apply (subgoal_tac "(vptr >> 12) && 0xFF << 2 < 2 ^ 10")
      apply (subst is_aligned_add_or, (simp add: pt_bits_def pageBits_def)+)
      apply (subst word_ao_dist)
      apply (subst mask_out_sub_mask [where x="(vptr >> 12) && 0xFF << 2"])
      apply (subst less_mask_eq, simp+)
      apply (subst is_aligned_neg_mask_eq, simp)
      apply (clarsimp simp: valid_arch_state_def valid_global_pts_def)
     apply (rule shiftl_less_t2n, simp)
      apply (rule and_mask_less'[where n=8, unfolded mask_def, simplified], (simp )+)
    apply (subst shiftl_shiftr_id)
      apply (simp add: word_bits_def)+
     apply word_bitwise
    apply (subst (asm) shiftl_shiftr_id)
      apply (simp add: word_bits_def)+
     apply word_bitwise
    apply (erule vs_refs_pdI)
     apply (erule kernel_base_kernel_mapping_slots)
    apply (intro allI impI)
    apply (simp add: nth_shiftr)
    apply (rule bang_big[simplified])
    by (simp add: word_size)
  done
*)

lemma lookup_pdpt_slot_reachable [wp]:
  "\<lbrace>\<exists>\<rhd> pm and K (is_aligned pm pml4_bits \<and> vptr < pptr_base \<and> canonical_address vptr)
   and valid_arch_state and valid_arch_objs and equal_kernel_mappings
   and pspace_aligned and valid_global_objs\<rbrace>
  lookup_pdpt_slot pm vptr
  \<lbrace>\<lambda>pdpt_slot. \<exists>\<rhd> (pdpt_slot && ~~ mask pdpt_bits)\<rbrace>, -"
  apply (simp add: pred_conj_def ex_simps [symmetric] del: ex_simps)
  apply (rule hoare_vcg_ex_lift_R1)
  apply (rule hoare_pre)
   apply (rule hoare_post_imp_R)
    apply (rule lookup_pdpt_slot_looks_up)
   prefer 2
   apply clarsimp
   apply assumption
  apply fastforce
  done

(* FIXME x64: awaiting review of lookup_pt_slot_looks_up
lemma lookup_pt_slot_reachable [wp]:
  "\<lbrace>\<exists>\<rhd> pd and K (is_aligned pd 14 \<and> vptr < pptr_base \<and> canonical_address vptr)
   and valid_arch_state and valid_arch_objs and equal_kernel_mappings
   and pspace_aligned and valid_global_objs\<rbrace>
  lookup_pt_slot pd vptr
  \<lbrace>\<lambda>pt_slot. \<exists>\<rhd> (pt_slot && ~~ mask pt_bits)\<rbrace>, -"
  apply (simp add: pred_conj_def ex_simps [symmetric] del: ex_simps)
  apply (rule hoare_vcg_ex_lift_R1)
  apply (rule hoare_pre)
   apply (rule hoare_post_imp_R)
    apply (rule lookup_pt_slot_looks_up)
   prefer 2
   apply clarsimp
   apply assumption
  apply fastforce
  done
*)

lemma shiftr_less_t2n3:
  "\<lbrakk>(2 :: 'a word) ^ (n + m) = 0; m < len_of TYPE('a)\<rbrakk>
   \<Longrightarrow> (x :: 'a :: len word) >> n < 2 ^ m"
  apply (rule shiftr_less_t2n')
   apply (simp add: mask_def power_overflow)
  apply simp
  done


lemma shiftr_shiftl_mask_pml4_bits:
  "((get_pml4_index vptr) << word_size_bits) && mask pml4_bits = (get_pml4_index vptr) << word_size_bits"
  apply (rule iffD2 [OF mask_eq_iff_w2p])
   apply (simp add: bit_simps get_pml4_index_def word_size)
  apply (simp add: get_pml4_index_def bit_simps)
  apply (rule shiftl_less_t2n[where m=pml4_bits, unfolded bit_simps, simplified])
   apply (simp)
   apply (rule and_mask_less'[where n=9, simplified])
   apply simp+
  done


lemma triple_shift_fun:
  "get_pml4_index x << word_size_bits >> word_size_bits = get_pml4_index x"
  apply (rule word_eqI)
  apply (simp add: word_size nth_shiftr nth_shiftl get_pml4_index_def bit_simps)
  apply safe
  apply (drule test_bit_size)
  apply (simp add: word_size)
  done


lemma shiftr_20_unat_ucast:
  "unat (ucast (get_pml4_index x :: word64) :: 9word) = unat (get_pml4_index x)"
  unfolding get_pml4_index_def bit_simps
  using vptr_shiftr_le_2p[where vptr=x]
  apply (simp only: unat_ucast)
  apply (rule mod_less)
  apply (rule unat_less_power)
   apply (simp add: word_bits_def)
  apply (simp add: bit_simps get_pml4_index_def)
  done

lemma shiftr_eqD:
  "\<lbrakk> x >> n = y >> n; is_aligned x n; is_aligned y n \<rbrakk> \<Longrightarrow> x = y"
  apply (drule arg_cong[where f="\<lambda>v. v << n"])
  apply (simp add: and_not_mask[symmetric] is_aligned_neg_mask_eq)
  done

lemma mask_out_first_mask_some:
  "\<lbrakk> x && ~~ mask n = y; n \<le> m \<rbrakk> \<Longrightarrow> x && ~~ mask m = y && ~~ mask m"
  apply (rule word_eqI, drule_tac x=na in word_eqD)
  apply (simp add: word_ops_nth_size word_size)
  apply auto
  done


lemma gap_between_aligned:
  "\<lbrakk>a < (b :: ('a ::len word)); is_aligned a n; 
  is_aligned b n;n < len_of TYPE('a) \<rbrakk> \<Longrightarrow> a + (2^ n - 1) < b"
  apply (rule ccontr,simp add:not_less)
  apply (drule le_shiftr[where n = n])
  apply (simp add: aligned_shift')
  apply (case_tac "b >> n = a >> n")
   apply (drule arg_cong[where f = "%x. x<<n"])
  apply (drule le_shiftr')
   apply (clarsimp simp:is_aligned_shiftr_shiftl)
   apply fastforce
  apply (drule(1) le_shiftr')
  apply simp
  done
  

lemma less_kernel_base_mapping_slots:
  "\<lbrakk> vptr < pptr_base; is_aligned pm pml4_bits; canonical_address vptr \<rbrakk>
       \<Longrightarrow> ucast (lookup_pml4_slot pm vptr && mask pml4_bits >> word_size_bits)
                \<notin> kernel_mapping_slots"
  apply (simp add: lookup_pml4_slot_def Let_def)
  apply (subst mask_add_aligned, assumption)
  apply (simp add: shiftr_shiftl_mask_pml4_bits triple_shift_fun)
  apply (erule (1) kernel_base_kernel_mapping_slots)
  done

lemma mask_out_add_aligned:
  assumes al: "is_aligned p n"
  shows "p + (q && ~~ mask n) = (p + q) && ~~ mask n"
  using mask_add_aligned [OF al]
  by (simp add: mask_out_sub_mask)

lemma lookup_pml4_slot_eq:
  "is_aligned pm pml4_bits \<Longrightarrow>
   (lookup_pml4_slot pm vptr && ~~ mask pml4_bits) = pm"
  apply (clarsimp simp: lookup_pml4_slot_def get_pml4_index_def bit_simps)
  apply (erule conjunct2[OF is_aligned_add_helper])
  apply (rule shiftl_less_t2n)
   apply (simp)
   apply (rule and_mask_less'[where n=9, simplified])
   apply simp+
  done

lemma create_mapping_entries_valid_slots [wp]:
  "\<lbrace>valid_arch_state and valid_arch_objs and equal_kernel_mappings
   and pspace_aligned and valid_global_objs
   and \<exists>\<rhd> pm and page_map_l4_at pm and typ_at (AArch (AIntData sz)) (ptrFromPAddr base) and
    K (is_aligned base pageBits \<and> vmsz_aligned vptr sz \<and> vptr < pptr_base \<and>
       canonical_address vptr \<and> vm_rights \<in> valid_vm_rights)\<rbrace>
  create_mapping_entries base vptr sz vm_rights attrib pm
  \<lbrace>\<lambda>m. valid_slots m\<rbrace>, -"
  apply (cases sz)
  apply (rule hoare_pre)
  (*
  apply (wp_trace lookup_pt_slot_inv | simp add: valid_slots_def)+ (* requires lookup_pt_slot_reachable *)
  apply (clarsimp simp: pd_aligned)
    apply (rule hoare_pre)
     apply (wp lookup_pt_slot_inv |simp add: valid_slots_def ball_conj_distrib)+
     apply (wp lookup_pt_slot_non_empty lookup_pt_slot_inv)
    apply (clarsimp simp: pd_aligned vmsz_aligned_def)
   apply (clarsimp simp add: valid_slots_def)
   apply (rule hoare_pre)
    apply wp
   apply (clarsimp simp: valid_slots_def )
   apply (rule conjI)
    apply (simp add: lookup_pd_slot_def Let_def)
    apply (fastforce simp: pd_shifting pd_aligned)
   apply (simp add: page_directory_pde_at_lookupI)
   apply (erule less_kernel_base_mapping_slots)
   apply (simp add: pd_aligned pd_bits)
  apply simp
  apply (rule hoare_pre)
   apply (clarsimp simp add: valid_slots_def)
   apply wp
  apply simp
  apply (elim conjE)
  apply (thin_tac "is_aligned base b" for b)
  apply (subgoal_tac "is_aligned pd 14")
   prefer 2
   apply (clarsimp simp: pd_aligned)
  apply (subst p_0x3C_shift)
   apply (clarsimp simp: lookup_pd_slot_def Let_def)
   apply (erule aligned_add_aligned)
     apply (clarsimp simp: vmsz_aligned_def
                   intro!: is_aligned_shiftl is_aligned_shiftr)
    apply (clarsimp simp: word_bits_def)
   apply clarsimp
  apply (clarsimp simp: upto_enum_step_def word32_shift_by_2)
  apply (clarsimp simp: obj_at_def pde_at_def)
  apply (subgoal_tac "is_aligned pd pd_bits")
   prefer 2
   apply (simp add: pd_bits)
  apply (rule conjI)
   apply (simp add:not_less)
   apply (rule is_aligned_no_wrap'[where sz = 6])
    apply (rule is_aligned_lookup_pd_slot)
     apply (simp add:vmsz_aligned_def)
    apply (erule is_aligned_weaken,simp)
   apply simp
  apply (clarsimp simp: not_less)
  apply (rule conjI)
   apply (simp add: upto_enum_def)
  apply (intro allI impI)
  apply (subst less_kernel_base_mapping_slots_both,assumption+)
   apply (simp add: minus_one_helper5)
  apply (simp add: pd_bits vmsz_aligned_def)
  apply (frule (1) is_aligned_lookup_pd_slot
                   [OF _ is_aligned_weaken[of _ 14 6, simplified]])
  apply (subgoal_tac "(x<<2) + lookup_pd_slot pd vptr && ~~ mask 14 = pd")
  prefer 2
   apply (subst add.commute add.left_commute)
   apply (subst and_not_mask_twice[where n=6 and m=14, simplified, symmetric])
   apply (subst is_aligned_add_helper[THEN conjunct2], simp)
    apply (rule shiftl_less_t2n)
     apply (rule word_less_sub_le[THEN iffD1], simp+)
   apply (erule lookup_pd_slot_eq[simplified pd_bits])
  apply (simp add: a_type_simps)
  apply (subst add.commute)
  apply (fastforce intro!: aligned_add_aligned is_aligned_shiftl_self)
  done
*)
  sorry
  
lemma is_aligned_addrFromPPtr_n:
  "\<lbrakk> is_aligned p n; n \<le> 39 \<rbrakk> \<Longrightarrow> is_aligned (Platform.X64.addrFromPPtr p) n"
  apply (simp add: Platform.X64.addrFromPPtr_def)
  apply (erule aligned_sub_aligned, simp_all)
  apply (simp add: pptrBase_def
                   pageBits_def)
  apply (erule is_aligned_weaken[rotated])
  apply (simp add: is_aligned_def)
  done

lemma is_aligned_addrFromPPtr:
  "is_aligned p pageBits \<Longrightarrow> is_aligned (Platform.X64.addrFromPPtr p) pageBits"
  by (simp add: is_aligned_addrFromPPtr_n pageBits_def)

(* FIXME x64: ARM magic numbers
lemma is_aligned_ptrFromPAddr_n:
  "\<lbrakk>is_aligned x sz; sz\<le> 28\<rbrakk>
  \<Longrightarrow> is_aligned (ptrFromPAddr x) sz"
  apply (simp add:ptrFromPAddr_def physMappingOffset_def
    kernelBase_addr_def physBase_def)
  apply (erule aligned_add_aligned)
   apply (erule is_aligned_weaken[rotated])
   apply (simp add:is_aligned_def)
  apply (simp add:word_bits_def)
  done

lemma is_aligned_ptrFromPAddr:
  "is_aligned p pageBits \<Longrightarrow> is_aligned (ptrFromPAddr p) pageBits"
  by (simp add: is_aligned_ptrFromPAddr_n pageBits_def)
*)

(* FIXME x64: trace down tables? *)
lemma store_pde_lookup_pml4:
  "\<lbrace>\<exists>\<rhd> pm and page_map_l4_at pm and valid_arch_objs
     and (\<lambda>s. valid_asid_table (x64_asid_table (arch_state s)) s)\<rbrace>
  store_pml4e p pml4e \<lbrace>\<lambda>_. \<exists>\<rhd> pm\<rbrace>"
  apply (simp add: store_pml4e_def set_pml4_def set_object_def)
  apply (wp get_object_wp)
  apply clarsimp
  apply (clarsimp split: kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp: obj_at_def)
  apply (erule vs_lookupE)
  apply (clarsimp simp: vs_asid_refs_def graph_of_def)
  apply (drule rtranclD)
  apply (erule disjE)
   apply clarsimp
   apply (rule exI)
   apply (rule vs_lookup_atI)
   apply simp
  apply clarsimp
  apply (frule (1) valid_asid_tableD)
  apply (frule vs_lookup_atI)
  apply (frule (2) stronger_arch_objsD)
  apply (clarsimp simp: obj_at_def a_type_def)
  apply (case_tac ao, simp_all, clarsimp)
  apply (drule tranclD)
  apply clarsimp
  apply (drule rtranclD)
  apply (erule disjE)
   apply clarsimp
   apply (rule_tac x=ref in exI)
   apply (rule vs_lookup_step)
    apply (rule vs_lookup_atI)
    apply simp
   apply (clarsimp simp: vs_lookup1_def)
   apply (clarsimp simp: obj_at_def vs_refs_def graph_of_def)
  apply clarsimp
  apply (drule (1) vs_lookup_step)
  apply (frule (2) stronger_arch_objsD)
  apply clarsimp
  apply (drule vs_lookup1D)
  apply clarsimp
  apply (erule obj_atE)+
  apply (clarsimp simp: vs_refs_def graph_of_def)
  apply (drule bspec, blast)
  apply (erule obj_atE)+
  apply clarsimp
  apply (drule tranclD)
  apply clarsimp
  apply (drule rtranclD)
  apply clarsimp
  apply (drule vs_lookup1D)
  apply clarsimp
  apply (erule obj_atE)+
  apply (clarsimp simp: vs_refs_def graph_of_def)
  apply (erule_tac x=ab in ballE)
   apply (case_tac "pmaa ab", simp_all add: pml4e_ref_def split: split_if_asm)
  apply (erule obj_atE)
  apply clarsimp
  apply (erule disjE)
   apply (clarsimp simp: a_type_def)
  apply clarsimp
  apply (drule tranclD)
  apply clarsimp
  apply (drule vs_lookup1D)
  apply clarsimp
  apply (erule obj_atE)+
  apply (clarsimp simp: vs_refs_def graph_of_def)
  sorry

lemma store_pml4e_arch_objs_unmap:
  "\<lbrace>valid_arch_objs
    and valid_pml4e pml4e
    and K (pml4e_ref pml4e = None)\<rbrace>
  store_pml4e p pml4e \<lbrace>\<lambda>_. valid_arch_objs\<rbrace>"
  apply (simp add: store_pml4e_def)
  apply (wp set_pml4_arch_objs_unmap)
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (drule (1) valid_arch_objsD, fastforce)
   apply simp
  apply (clarsimp simp add: obj_at_def vs_refs_def)
  apply (rule pair_imageI)
  apply (simp add: graph_of_def split: split_if_asm)
  done
  
lemma store_pdpte_arch_objs_unmap:
  "\<lbrace>valid_arch_objs
    and valid_pdpte pdpte
    and K (pdpte_ref pdpte = None)\<rbrace>
  store_pdpte p pdpte \<lbrace>\<lambda>_. valid_arch_objs\<rbrace>"
  apply (simp add: store_pdpte_def)
  apply (wp set_pdpt_arch_objs_unmap)
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (drule (1) valid_arch_objsD, fastforce)
   apply simp
  apply (clarsimp simp add: obj_at_def vs_refs_def)
  apply (rule pair_imageI)
  apply (simp add: graph_of_def split: split_if_asm)
  done
  
lemma store_pde_arch_objs_unmap:
  "\<lbrace>valid_arch_objs
    and valid_pde pde
    and K (pde_ref pde = None)\<rbrace>
  store_pde p pde \<lbrace>\<lambda>_. valid_arch_objs\<rbrace>"
  apply (simp add: store_pde_def)
  apply (wp set_pd_arch_objs_unmap)
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (drule (1) valid_arch_objsD, fastforce)
   apply simp
  apply (clarsimp simp add: obj_at_def vs_refs_def)
  apply (rule pair_imageI)
  apply (simp add: graph_of_def split: split_if_asm)
  done


lemma vs_lookup_arch_update:
  "x64_asid_table (f (arch_state s)) = x64_asid_table (arch_state s) \<Longrightarrow>
  vs_lookup (arch_state_update f s) = vs_lookup s"
  apply (rule order_antisym)
   apply (rule vs_lookup_sub)
    apply (clarsimp simp: obj_at_def)
   apply simp
  apply (rule vs_lookup_sub)
   apply (clarsimp simp: obj_at_def)
  apply simp
  done


lemma vs_lookup_pages_arch_update:
  "x64_asid_table (f (arch_state s)) = x64_asid_table (arch_state s) \<Longrightarrow>
  vs_lookup_pages (arch_state_update f s) = vs_lookup_pages s"
  apply (rule order_antisym)
   apply (rule vs_lookup_pages_sub)
    apply (clarsimp simp: obj_at_def)
   apply simp
  apply (rule vs_lookup_pages_sub)
   apply (clarsimp simp: obj_at_def)
  apply simp
  done


lemma vs_lookup_asid_map [iff]:
  "vs_lookup (s\<lparr>arch_state := x64_asid_map_update f (arch_state s)\<rparr>) = vs_lookup s"
  by (simp add: vs_lookup_arch_update)


lemma vs_lookup_pages_asid_map[iff]:
  "vs_lookup_pages (s\<lparr>arch_state := x64_asid_map_update f (arch_state s)\<rparr>) =
   vs_lookup_pages s"
  by (simp add: vs_lookup_pages_arch_update)

lemma valid_arch_objs_arch_update:
  "x64_asid_table (f (arch_state s)) = x64_asid_table (arch_state s) \<Longrightarrow>
  valid_arch_objs (arch_state_update f s) = valid_arch_objs s"
  apply (rule iffI)
   apply (erule valid_arch_objs_stateI)
     apply (clarsimp simp: obj_at_def)
    apply simp
   apply simp
  apply (erule valid_arch_objs_stateI)
    apply (clarsimp simp: obj_at_def)
   apply simp
  apply simp
  done

lemma store_pte_valid_arch_objs[wp]:
  "\<lbrace>valid_arch_objs and valid_pte pte\<rbrace>
    store_pte p pte
  \<lbrace>\<lambda>_. (valid_arch_objs)\<rbrace>"
  unfolding store_pte_def
  apply wp
  apply clarsimp
  apply (unfold valid_arch_objs_def)
  apply (erule_tac x="p && ~~ mask pt_bits" in allE)
  apply auto
  done

crunch valid_arch [wp]: store_pte valid_arch_state

lemma set_pml4_vs_lookup_unmap:
  "\<lbrace>valid_vs_lookup and
    obj_at (\<lambda>ko. vs_refs_pages (ArchObj (PageMapL4 pml4)) \<subseteq> vs_refs_pages ko) p\<rbrace>
  set_pml4 p pml4
  \<lbrace>\<lambda>_. valid_vs_lookup\<rbrace>"
  apply (simp add: valid_vs_lookup_def pred_conj_def)
  apply (rule hoare_lift_Pf2 [where f=caps_of_state])
   prefer 2
   apply wp
  apply (simp add: set_pml4_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp del: fun_upd_apply del: disjCI
                  split: kernel_object.splits arch_kernel_obj.splits)
  apply (erule allE)+
  apply (erule impE)
   apply (erule vs_lookup_pages_stateI)
    apply (clarsimp simp: obj_at_def split: split_if_asm)
   apply simp
  apply simp
  done

lemma set_pdpt_vs_lookup_unmap:
  "\<lbrace>valid_vs_lookup and
    obj_at (\<lambda>ko. vs_refs_pages (ArchObj (PDPointerTable pdpt)) \<subseteq> vs_refs_pages ko) p\<rbrace>
  set_pdpt p pdpt
  \<lbrace>\<lambda>_. valid_vs_lookup\<rbrace>"
  apply (simp add: valid_vs_lookup_def pred_conj_def)
  apply (rule hoare_lift_Pf2 [where f=caps_of_state])
   prefer 2
   apply wp
  apply (simp add: set_pdpt_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp del: fun_upd_apply del: disjCI
                  split: kernel_object.splits arch_kernel_obj.splits)
  apply (erule allE)+
  apply (erule impE)
   apply (erule vs_lookup_pages_stateI)
    apply (clarsimp simp: obj_at_def split: split_if_asm)
   apply simp
  apply simp
  done

lemma set_pd_vs_lookup_unmap:
  "\<lbrace>valid_vs_lookup and
    obj_at (\<lambda>ko. vs_refs_pages (ArchObj (PageDirectory pd)) \<subseteq> vs_refs_pages ko) p\<rbrace>
  set_pd p pd
  \<lbrace>\<lambda>_. valid_vs_lookup\<rbrace>"
  apply (simp add: valid_vs_lookup_def pred_conj_def)
  apply (rule hoare_lift_Pf2 [where f=caps_of_state])
   prefer 2
   apply wp
  apply (simp add: set_pd_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp del: fun_upd_apply del: disjCI
                  split: kernel_object.splits arch_kernel_obj.splits)
  apply (erule allE)+
  apply (erule impE)
   apply (erule vs_lookup_pages_stateI)
    apply (clarsimp simp: obj_at_def split: split_if_asm)
   apply simp
  apply simp
  done


lemma unique_table_caps_pml4E:
  "\<lbrakk> unique_table_caps cs; cs p = Some cap; cap_asid cap = None;
     cs p' = Some cap'; cap_asid cap' = Some v; is_pml4_cap cap;
     is_pml4_cap cap'; obj_refs cap' = obj_refs cap \<rbrakk>
       \<Longrightarrow> P"
  apply (frule(6) unique_table_caps_pml4D[where cs=cs])
  apply simp
  done
  
lemma unique_table_caps_pdptE:
  "\<lbrakk> unique_table_caps cs; cs p = Some cap; cap_asid cap = None;
     cs p' = Some cap'; cap_asid cap' = Some v; is_pdpt_cap cap;
     is_pdpt_cap cap'; obj_refs cap' = obj_refs cap \<rbrakk>
       \<Longrightarrow> P"
  apply (frule(6) unique_table_caps_pdptD[where cs=cs])
  apply simp
  done
  
lemma unique_table_caps_pdE:
  "\<lbrakk> unique_table_caps cs; cs p = Some cap; cap_asid cap = None;
     cs p' = Some cap'; cap_asid cap' = Some v; is_pd_cap cap;
     is_pd_cap cap'; obj_refs cap' = obj_refs cap \<rbrakk>
       \<Longrightarrow> P"
  apply (frule(6) unique_table_caps_pdD[where cs=cs])
  apply simp
  done

lemmas unique_table_caps_pml4E' = unique_table_caps_pml4E[where cs="arch_caps_of x" for x, simplified]
lemmas unique_table_caps_pdptE' = unique_table_caps_pdptE[where cs="arch_caps_of x" for x, simplified]  
lemmas unique_table_caps_pdE' = unique_table_caps_pdE[where cs="arch_caps_of x" for x, simplified]

lemma set_pml4_table_caps [wp]:
  "\<lbrace>valid_table_caps and (\<lambda>s.
    (obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) p s \<longrightarrow>
     empty_table (set (x64_global_pdpts (arch_state s))) (ArchObj (PageMapL4 pm))) \<or>
    (\<exists>slot cap. caps_of_state s slot = Some cap \<and> is_pml4_cap cap \<and> p \<in> obj_refs cap \<and> cap_asid cap \<noteq> None) \<and>
    valid_caps (caps_of_state s) s \<and>
    unique_table_caps (caps_of_state s))\<rbrace>
  set_pml4 p pm
  \<lbrace>\<lambda>_. valid_table_caps\<rbrace>"
  unfolding valid_table_caps_def
  apply (simp add: pred_conj_def
              del: split_paired_All split_paired_Ex imp_disjL)
  apply (rule hoare_lift_Pf2 [where f=caps_of_state])
   prefer 2
   apply wp
  apply (unfold set_pml4_def set_object_def)
  apply (wp get_object_wp)
  apply (rule allI, intro impI)
  apply (elim exE conjE)
  apply (elim allEI)
  apply (intro impI, simp)
  apply (clarsimp simp: obj_at_def)
  apply (clarsimp split: kernel_object.splits arch_kernel_obj.splits)
  (* yes this is gross *)
  apply (erule disjE, (simp add: valid_caps_def, erule_tac x=a in allE, erule allE, erule allE, erule (1) impE,
           clarsimp simp: is_arch_cap_simps valid_cap_def, clarsimp simp: obj_at_def))+
  apply (erule(6) unique_table_caps_pml4E)
  apply (clarsimp simp: is_arch_cap_simps)
  done


lemma set_pml4_global_objs[wp]:
  "\<lbrace>valid_global_objs and valid_global_refs and
    valid_arch_state and
    (\<lambda>s. (obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) p s
             \<longrightarrow> empty_table (set (x64_global_pdpts (arch_state s)))
                                 (ArchObj (PageMapL4 pm)))
        \<or> (\<exists>slot. cte_wp_at (\<lambda>cap. p \<in> obj_refs cap) slot s))\<rbrace>
  set_pml4 p pm \<lbrace>\<lambda>rv. valid_global_objs\<rbrace>"
  apply (simp add: set_pml4_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp del: fun_upd_apply
                  split: kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp add: valid_global_objs_def valid_ao_at_def
                            cte_wp_at_caps_of_state)
  apply (intro conjI)
    apply (clarsimp simp: obj_at_def
                simp del: valid_arch_obj.simps)
    apply (intro conjI impI)
     apply (clarsimp simp del: valid_arch_obj.simps)
     apply (erule disjE)
      apply (drule(1) empty_table_is_valid)+
      apply (rule valid_arch_obj_same_type, simp+)
      apply (clarsimp simp: a_type_def)
     apply clarsimp
     apply (drule (1) valid_global_refsD2)
     apply (simp add: cap_range_def global_refs_def)
    apply (rule valid_arch_obj_same_type, simp+)
    apply (simp add: a_type_def)
   apply (clarsimp simp: obj_at_def)
   apply (drule (1) valid_global_refsD2)
   apply (simp add: cap_range_def global_refs_def)
  apply clarsimp
  apply (clarsimp simp: obj_at_def
              simp del: valid_arch_obj.simps)
  apply (drule(1) bspec, clarsimp)
  done


lemma eq_ucast_word9[simp]:
  "((ucast (x :: 9 word) :: word64) = ucast y) = (x = y)"
  apply safe
  apply (drule_tac f="ucast :: (word64 \<Rightarrow> 9 word)" in arg_cong)
  apply (simp add: ucast_up_ucast_id is_up_def
                   source_size_def target_size_def word_size)
  done

lemma set_pml4_unmap_mappings:
  "\<lbrace>valid_kernel_mappings and
        obj_at (\<lambda>ko. vs_refs (ArchObj (PageMapL4 pm)) \<subseteq> vs_refs ko) p
    and obj_at (\<lambda>ko. \<exists>pd'. ko = ArchObj (PageMapL4 pd')
                       \<and> (\<forall>x \<in> kernel_mapping_slots. pm x = pd' x)) p\<rbrace>
     set_pml4 p pm
   \<lbrace>\<lambda>rv. valid_kernel_mappings\<rbrace>"
  apply (simp add: set_pml4_def)
  apply (wp set_object_v_ker_map get_object_wp)
  apply (clarsimp simp: obj_at_def
                 split: kernel_object.split_asm
                        arch_kernel_obj.split_asm)
  apply (simp add: vs_refs_def)
  subgoal premises prems for s x r x3
    apply (cases "x \<in> kernel_mapping_slots")
    proof goal_cases
     case False
     with prems show ?thesis
     apply -
     apply (drule subsetD)
      apply (rule image_eqI[rotated])
       apply (rule pml4e_graph_ofI[rotated, rotated])
          apply ((simp;fail)+)[4]
      apply (clarsimp simp: valid_kernel_mappings_def
                      dest!: graph_ofD)
      apply (drule bspec, erule ranI)
      by (simp add: valid_kernel_mappings_if_pm_def)   
    next
     case True 
     with prems show ?thesis
     apply clarsimp
     apply (bspec x)
      apply (clarsimp simp: valid_kernel_mappings_def ran_def valid_kernel_mappings_if_pm_def)
      apply (erule allE[where x="ArchObj (PageMapL4 x3)"])
      apply clarsimp
      apply (erule impE)
        apply (erule exI[where x=p])
       apply (erule allE[where x=x], erule allE[where x=r])
       by clarsimp+
    qed
  done


lemma set_pml4_asid_map [wp]:
  "\<lbrace>valid_asid_map\<rbrace> set_pml4 p pm \<lbrace>\<lambda>_. valid_asid_map\<rbrace>"
  apply (simp add: set_pml4_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp del: fun_upd_apply
                  split: kernel_object.splits
                         arch_kernel_obj.splits)
  apply (clarsimp simp: valid_asid_map_def)
  apply (drule bspec, blast)
  apply (clarsimp simp: vspace_at_asid_def obj_at_def)
  apply (erule vs_lookupE)
  apply (rule vs_lookupI, simp)
  apply (clarsimp simp: vs_asid_refs_def dest!: graph_ofD)
  apply (frule vs_lookup1_trans_is_append)
  apply clarsimp
  apply (drule rtranclD)
  apply clarsimp
  apply (drule tranclD)
  apply clarsimp
  apply (drule vs_lookup1D)
  apply clarsimp
  apply (rule rtrancl_trans)
   apply (rule r_into_rtrancl)
   apply (rule vs_lookup1I)
     apply (clarsimp simp: obj_at_def)
     apply (rule conjI, clarsimp)
      prefer 2
      apply clarsimp
      apply (rule refl)
     apply clarsimp
     apply (clarsimp simp: vs_refs_def)
     apply (drule vs_lookup1_trans_is_append)
     apply clarsimp
    apply assumption
   apply (rule refl)
  apply (frule vs_lookup1_trans_is_append, clarsimp)
  apply (drule rtranclD)
  apply (erule disjE, clarsimp)
  apply clarsimp
  apply (drule tranclD)
  apply clarsimp
  apply (drule vs_lookup1D)
  apply clarsimp
  apply (drule vs_lookup1_trans_is_append, clarsimp)
  done
  
lemma set_pdpt_asid_map [wp]:
  "\<lbrace>valid_asid_map\<rbrace> set_pdpt p pm \<lbrace>\<lambda>_. valid_asid_map\<rbrace>"
  apply (simp add: set_pdpt_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp del: fun_upd_apply
                  split: kernel_object.splits
                         arch_kernel_obj.splits)
  apply (clarsimp simp: valid_asid_map_def)
  apply (drule bspec, blast)
  apply (clarsimp simp: vspace_at_asid_def obj_at_def)
  apply (erule vs_lookupE)
  apply (rule vs_lookupI, simp)
  apply (clarsimp simp: vs_asid_refs_def dest!: graph_ofD)
  apply (frule vs_lookup1_trans_is_append)
  apply clarsimp
  apply (drule rtranclD)
  apply clarsimp
  apply (drule tranclD)
  apply clarsimp
  apply (drule vs_lookup1D)
  apply clarsimp
  apply (rule rtrancl_trans)
   apply (rule r_into_rtrancl)
   apply (rule vs_lookup1I)
     apply (clarsimp simp: obj_at_def)
     apply (rule conjI, clarsimp)
      prefer 2
      apply clarsimp
      apply (rule refl)
     apply clarsimp
     apply (clarsimp simp: vs_refs_def)
     apply (drule vs_lookup1_trans_is_append)
     apply clarsimp
    apply assumption
   apply (rule refl)
  apply (frule vs_lookup1_trans_is_append, clarsimp)
  apply (drule rtranclD)
  apply (erule disjE, clarsimp)
  apply clarsimp
  apply (drule tranclD)
  apply clarsimp
  apply (drule vs_lookup1D)
  apply clarsimp
  apply (drule vs_lookup1_trans_is_append, clarsimp)
  done
  
lemma set_pd_asid_map [wp]:
  "\<lbrace>valid_asid_map\<rbrace> set_pd p pd \<lbrace>\<lambda>_. valid_asid_map\<rbrace>"
  apply (simp add: set_pd_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp del: fun_upd_apply
                  split: kernel_object.splits
                         arch_kernel_obj.splits)
  apply (clarsimp simp: valid_asid_map_def)
  apply (drule bspec, blast)
  apply (clarsimp simp: vspace_at_asid_def obj_at_def)
  apply (erule vs_lookupE)
  apply (rule vs_lookupI, simp)
  apply (clarsimp simp: vs_asid_refs_def dest!: graph_ofD)
  apply (frule vs_lookup1_trans_is_append)
  apply clarsimp
  apply (drule rtranclD)
  apply clarsimp
  apply (drule tranclD)
  apply clarsimp
  apply (drule vs_lookup1D)
  apply clarsimp
  apply (rule rtrancl_trans)
   apply (rule r_into_rtrancl)
   apply (rule vs_lookup1I)
     apply (clarsimp simp: obj_at_def)
     apply (rule conjI, clarsimp)
      prefer 2
      apply clarsimp
      apply (rule refl)
     apply clarsimp
     apply (clarsimp simp: vs_refs_def)
     apply (drule vs_lookup1_trans_is_append)
     apply clarsimp
    apply assumption
   apply (rule refl)
  apply (frule vs_lookup1_trans_is_append, clarsimp)
  apply (drule rtranclD)
  apply (erule disjE, clarsimp)
  apply clarsimp
  apply (drule tranclD)
  apply clarsimp
  apply (drule vs_lookup1D)
  apply clarsimp
  apply (drule vs_lookup1_trans_is_append, clarsimp)
  done

lemma set_pml4_equal_kernel_mappings_triv:
  "\<lbrace>obj_at (\<lambda>ko. \<exists>pm'. ko = (ArchObj (PageMapL4 pm'))
                       \<and> (\<forall>x \<in> kernel_mapping_slots. pm x = pm' x)) p
          and equal_kernel_mappings\<rbrace>
     set_pml4 p pm
   \<lbrace>\<lambda>rv. equal_kernel_mappings\<rbrace>"
  apply (simp add: set_pml4_def)
  apply (wp set_object_equal_mappings get_object_wp)
  apply (clarsimp simp: obj_at_def)
  apply (simp add: equal_kernel_mappings_def obj_at_def)
  done


lemma set_pml4_global_mappings[wp]:
  "\<lbrace>\<lambda>s. valid_global_vspace_mappings s \<and> valid_global_objs s
               \<and> p \<notin> global_refs s\<rbrace>
     set_pml4 p pml4
   \<lbrace>\<lambda>rv. valid_global_vspace_mappings\<rbrace>"
  apply (simp add: set_pml4_def)
  apply (wp set_object_global_vspace_mappings get_object_wp)
  apply simp
  done


lemma set_pml4_kernel_window[wp]:
  "\<lbrace>pspace_in_kernel_window\<rbrace> set_pml4 p pml4 \<lbrace>\<lambda>rv. pspace_in_kernel_window\<rbrace>"
  apply (simp add: set_pml4_def)
  apply (wp set_object_pspace_in_kernel_window get_object_wp)
  apply (clarsimp simp: obj_at_def a_type_def
                 split: kernel_object.split_asm
                        arch_kernel_obj.split_asm)
  done


lemma set_pml4_caps_kernel_window[wp]:
  "\<lbrace>cap_refs_in_kernel_window\<rbrace> set_pml4 p pml4 \<lbrace>\<lambda>rv. cap_refs_in_kernel_window\<rbrace>"
  apply (simp add: set_pml4_def)
  apply (wp set_object_cap_refs_in_kernel_window get_object_wp)
  apply (clarsimp simp: obj_at_def a_type_def
                 split: kernel_object.split_asm
                        arch_kernel_obj.split_asm)
  done

  
(* FIXME: Move to Invariants_A *)
lemma vs_refs_pages_subset: "vs_refs ko \<subseteq> vs_refs_pages ko"
  apply (clarsimp simp: vs_refs_pages_def vs_refs_def graph_of_def 
                 split: kernel_object.splits arch_kernel_obj.splits)
  apply (rule conjI)
   apply (clarsimp split: pde.splits)
  subgoal for "fun" a b
  using
    imageI[where A="{(x, y). pde_ref_pages (fun x) = Some y}"
             and f="(\<lambda>(r, y). (VSRef (ucast r) (Some APageDirectory), y))" and x="(a,b)"]
   apply (clarsimp simp: pde_ref_def pde_ref_pages_def split: if_splits pde.splits)
   done
  apply (rule conjI)
   apply (clarsimp split: pdpte.splits)
  subgoal for "fun" a b
   using
    imageI[where A="{(x, y). pdpte_ref_pages (fun x) = Some y}"
             and f="(\<lambda>(r, y). (VSRef (ucast r) (Some APDPointerTable), y))" and x="(a,b)"]
   apply (clarsimp simp: pdpte_ref_def pdpte_ref_pages_def split: if_splits pdpte.splits)
   done
     apply (clarsimp split: pml4e.splits)
  subgoal for "fun" a b
   using
    imageI[where A="{(x, y). (if x \<in> kernel_mapping_slots then None else pml4e_ref_pages (fun x)) = Some y}"
             and f="(\<lambda>(r, y). (VSRef (ucast r) (Some APageMapL4), y))" and x="(a,b)"]
   apply (clarsimp simp: pml4e_ref_def pml4e_ref_pages_def split: if_splits pml4e.splits)
   done
  done

lemma vs_refs_pages_subset2:
  "\<lbrakk>vs_refs_pages ko \<subseteq> vs_refs_pages ko';
    (\<forall>ao. (ko = ArchObj ao) \<longrightarrow> valid_arch_obj ao s);
    (\<forall>ao'. (ko' = ArchObj ao') \<longrightarrow> valid_arch_obj ao' s)\<rbrakk>
   \<Longrightarrow> vs_refs ko \<subseteq> vs_refs ko'"
  apply clarsimp
  apply (drule (1) subsetD[OF _ subsetD[OF vs_refs_pages_subset]])
  apply (clarsimp simp: vs_refs_def vs_refs_pages_def graph_of_def
                 split: kernel_object.splits arch_kernel_obj.splits if_splits)
  subgoal for pd pd' a b
   using
     imageI[where
       A="{(x, y). pde_ref (pd' x) = Some y}"
       and f="(\<lambda>(r, y). (VSRef (ucast r) (Some APageDirectory), y))" and x="(a,b)"]
    apply (clarsimp simp: pde_ref_def pde_ref_pages_def split: pde.splits)
    apply (drule_tac x=a in spec; simp)
    apply (drule_tac x=a in spec; simp)
    apply (clarsimp simp: obj_at_def a_type_def)
   done  
   subgoal for pdpt pdpt' a b
   using
     imageI[where
       A="{(x, y). pdpte_ref (pdpt' x) = Some y}"
       and f="(\<lambda>(r, y). (VSRef (ucast r) (Some APDPointerTable), y))" and x="(a,b)"]
    apply (clarsimp simp: pdpte_ref_def pdpte_ref_pages_def split: pdpte.splits)
    apply (drule_tac x=a in spec; simp)
    apply (drule_tac x=a in spec; simp)
    apply (clarsimp simp: obj_at_def a_type_def)
   done
   subgoal for pml4 pml4' a b
   using
     imageI[where
       A="{(x, y). (if x \<in> kernel_mapping_slots then None else pml4e_ref (pml4' x)) = Some y}"
       and f="(\<lambda>(r, y). (VSRef (ucast r) (Some APageMapL4), y))" and x="(a,b)"]
    apply (clarsimp simp: pml4e_ref_def pml4e_ref_pages_def split: pml4e.splits)
    done
   done

lemma set_pml4_invs_unmap:
  "\<lbrace>invs and (\<lambda>s. \<forall>i. wellformed_pml4e (pml4 i)) and
    (\<lambda>s. (\<exists>\<rhd>p) s \<longrightarrow> valid_arch_obj (PageMapL4 pml4) s) and
    obj_at (\<lambda>ko. vs_refs_pages (ArchObj (PageMapL4 pml4)) \<subseteq> vs_refs_pages ko) p and
    obj_at (\<lambda>ko. vs_refs (ArchObj (PageMapL4 pml4)) \<subseteq> vs_refs ko) p and
    obj_at (\<lambda>ko. \<exists>pml4'. ko = ArchObj (PageMapL4 pml4')
                       \<and> (\<forall>x \<in> kernel_mapping_slots. pml4 x = pml4' x)) p and
    (\<lambda>s. p \<notin> global_refs s) and
    (\<lambda>s. (obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) p s \<longrightarrow>
     empty_table (set (x64_global_pdpts (arch_state s))) (ArchObj (PageMapL4 pml4))))\<rbrace>
  set_pml4 p pml4
  \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def valid_arch_caps_def)
  apply (rule hoare_pre)
   apply (wp_trace set_pml4_valid_objs set_pml4_iflive set_pml4_zombies
             set_pml4_zombies_state_refs set_pml4_valid_mdb
             set_pml4_valid_idle set_pml4_ifunsafe set_pml4_reply_caps
             set_pml4_valid_arch set_pml4_valid_global set_pml4_cur
             set_pml4_reply_masters valid_irq_node_typ
             set_pml4_arch_objs_unmap set_pml4_vs_lookup_unmap
             valid_irq_handlers_lift
             set_pml4_unmap_mappings set_pml4_equal_kernel_mappings_triv)
  apply (clarsimp simp: cte_wp_at_caps_of_state valid_arch_caps_def
    del: disjCI)
  done


lemma store_pml4e_invs_unmap:
  "\<lbrace>invs and valid_pml4e pml4e and (\<lambda>s. wellformed_pml4e pml4e)
            and K (ucast (p && mask pml4_bits >> word_size_bits) \<notin> kernel_mapping_slots)
            and (\<lambda>s. p && ~~ mask pml4_bits \<notin> global_refs s)
            and K (pml4e = InvalidPML4E)\<rbrace>
  store_pml4e p pml4e \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: store_pml4e_def del: split_paired_Ex)
  apply (wp set_pml4_invs_unmap)
  apply (clarsimp simp del: split_paired_Ex del: exE)
  apply (rule conjI)
   apply clarsimp
   apply (drule (1) valid_arch_objsD, fastforce)
   apply simp
  apply (rule conjI)
   apply (clarsimp intro!: pair_imageI
                   simp: obj_at_def vs_refs_def vs_refs_pages_def map_conv_upd graph_of_def pml4e_ref_def pml4e_ref_pages_def
                   split: split_if_asm)+
  apply (clarsimp simp: empty_table_def)
  apply (cases pml4e, (auto simp: pml4e_ref_def  split:split_if_asm))
  done

lemma store_pml4e_state_refs_of:
  "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace> store_pml4e ptr val \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (simp add: store_pml4e_def set_pml4_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp elim!: rsubst[where P=P] intro!: ext)
  apply (clarsimp simp: state_refs_of_def obj_at_def)
  done
  

lemma store_pdpte_state_refs_of:
  "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace> store_pdpte ptr val \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (simp add: store_pdpte_def set_pdpt_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp elim!: rsubst[where P=P] intro!: ext)
  apply (clarsimp simp: state_refs_of_def obj_at_def)
  done
  
lemma store_pde_state_refs_of:
  "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace> store_pde ptr val \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (simp add: store_pde_def set_pd_def set_object_def)
  apply (wp_trace get_object_wp)
  apply (clarsimp elim!: rsubst[where P=P] intro!: ext)
  apply (clarsimp simp: state_refs_of_def obj_at_def)
  done

lemma store_pte_state_refs_of:
  "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace> store_pte ptr val \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (simp add: store_pte_def set_pt_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp elim!: rsubst[where P=P] intro!: ext)
  apply (clarsimp simp: state_refs_of_def obj_at_def)
  done
  
end

end
