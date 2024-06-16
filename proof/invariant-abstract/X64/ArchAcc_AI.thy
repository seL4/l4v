(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Lemmas on arch get/set object etc
*)

theory ArchAcc_AI
imports
  SubMonad_AI ArchVSpaceLookup_AI "Lib.Crunch_Instances_NonDet"
begin


context Arch begin global_naming X64


bundle unfold_objects =
  obj_at_def[simp]
  kernel_object.splits[split]
  arch_kernel_obj.splits[split]

bundle unfold_objects_asm =
  obj_at_def[simp]
  kernel_object.split_asm[split]
  arch_kernel_obj.split_asm[split]

lemmas set_arch_obj_simps = set_pml4_def set_pt_def set_pdpt_def set_pd_def set_asid_pool_def


(* None generic proofs for get arch objects *)
lemma get_asid_pool_wp [wp]:
  "\<lbrace>\<lambda>s. \<forall>pool. ko_at (ArchObj (ASIDPool pool)) p s \<longrightarrow> Q pool s\<rbrace>
  get_asid_pool p
  \<lbrace>Q\<rbrace>"
  apply (simp add: get_asid_pool_def get_object_def)
   apply (wp|wpc)+
  apply (clarsimp simp: obj_at_def)
  done

lemma get_pml4_wp [wp]:
  "\<lbrace>\<lambda>s. \<forall>pm. ko_at (ArchObj (PageMapL4 pm)) p s \<longrightarrow> Q pm s\<rbrace> get_pml4 p \<lbrace>Q\<rbrace>"
  apply (simp add: get_pml4_def get_object_def)
  apply (wp|wpc)+
  apply (clarsimp simp: obj_at_def)
  done

lemma get_pml4e_wp:
  "\<lbrace>\<lambda>s. \<forall>pm. ko_at (ArchObj (PageMapL4 pm)) (p && ~~ mask pml4_bits) s \<longrightarrow>
        Q (pm (ucast (p && mask pml4_bits >> word_size_bits))) s\<rbrace>
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
  "\<lbrace>\<lambda>s. \<forall>pdpt. ko_at (ArchObj (PDPointerTable pdpt)) (p && ~~ mask pdpt_bits) s \<longrightarrow>
        Q (pdpt (ucast (p && mask pdpt_bits >> word_size_bits))) s\<rbrace>
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

lemma set_asid_pool_typ_at [wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> set_asid_pool ptr pool \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  apply (simp add: set_asid_pool_def get_object_def set_object_def)
  apply wp
  including unfold_objects
  by clarsimp

lemmas set_asid_pool_typ_ats [wp] = abs_typ_at_lifts [OF set_asid_pool_typ_at]

lemma set_asid_pool_vspace_objs_unmap':
  "\<lbrace>valid_vspace_objs and (\<lambda>s. (\<exists>\<rhd>p) s \<longrightarrow> valid_vspace_obj (ASIDPool ap) s) and
    obj_at (\<lambda>ko. \<exists>ap'. ko = ArchObj (ASIDPool ap') \<and> graph_of ap \<subseteq> graph_of ap') p\<rbrace>
  set_asid_pool p ap \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  unfolding set_asid_pool_def including unfold_objects
  apply (wpsimp wp: set_object_vspace_objs get_object_wp)
  apply (fastforce simp: a_type_def vs_refs_def)
  done

lemma set_asid_pool_vspace_objs_unmap:
  "\<lbrace>valid_vspace_objs and ko_at (ArchObj (ASIDPool ap)) p\<rbrace>
    set_asid_pool p (ap |` S)
  \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  apply (wp set_asid_pool_vspace_objs_unmap')
  apply (clarsimp simp: obj_at_def graph_of_restrict_map)
  apply (drule valid_vspace_objsD, simp add: obj_at_def, assumption)
  apply simp
  by (auto simp: obj_at_def dest!: ran_restrictD)

lemma set_asid_pool_iflive [wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap s\<rbrace>
    set_asid_pool p ap
   \<lbrace>\<lambda>_ s. if_live_then_nonz_cap s\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wp set_object_iflive[THEN hoare_set_object_weaken_pre])
  apply (clarsimp simp: a_type_def obj_at_def live_def hyp_live_def
                 split: kernel_object.splits arch_kernel_obj.splits)
  done

lemma set_asid_pool_zombies [wp]:
  "\<lbrace>\<lambda>s. zombies_final s\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. zombies_final s\<rbrace>"
  apply (simp add: set_asid_pool_def)
  including unfold_objects
  apply (wpsimp wp: set_object_zombies[THEN hoare_set_object_weaken_pre] simp: a_type_def)
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
  apply (clarsimp simp: obj_at_def state_refs_of_def a_type_simps split: option.splits)
  done

lemma set_asid_pool_cdt [wp]:
  "\<lbrace>\<lambda>s. P (cdt s)\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. P (cdt s)\<rbrace>"
  unfolding set_asid_pool_def including unfold_objects
  by (wpsimp wp: get_object_wp)

lemma set_asid_pool_caps_of_state [wp]:
  "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  unfolding set_asid_pool_def including unfold_objects
  apply (wpsimp wp: set_object_wp_strong simp: a_type_def)
  apply (subst cte_wp_caps_of_lift)
   prefer 2
   apply assumption
  subgoal for _ _ y apply (cases y, auto simp: cte_wp_at_cases)
    done
  done

lemma set_asid_pool_valid_mdb [wp]:
  "\<lbrace>\<lambda>s. valid_mdb s\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. valid_mdb s\<rbrace>"
  including unfold_objects
  by (wpsimp wp: valid_mdb_lift simp: set_asid_pool_def set_object_def get_object_def)


lemma set_asid_pool_reply_masters [wp]:
  "\<lbrace>valid_reply_masters\<rbrace>
   set_asid_pool p ap
   \<lbrace>\<lambda>_. valid_reply_masters\<rbrace>"
  by (wp valid_reply_masters_cte_lift)

crunches set_asid_pool
  for arch[wp]: "\<lambda>s. P (arch_state s)"
  (wp: crunch_wps)

crunches set_asid_pool
  for idle[wp]: "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps)

crunches set_asid_pool
  for irq[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps)

crunches set_asid_pool
  for valid_irq_states[wp]: "valid_irq_states"
  (wp: crunch_wps)

lemma set_asid_pool_valid_global [wp]:
  "\<lbrace>\<lambda>s. valid_global_refs s\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. valid_global_refs s\<rbrace>"
  by (wp valid_global_refs_cte_lift)

crunches set_asid_pool
  for interrupt_states[wp]: "\<lambda>s. P (interrupt_states s)"
  (wp: crunch_wps)

bundle pagebits =
  pd_bits_def[simp] pd_shift_bits_def [simp]
  pt_bits_def[simp] pt_shift_bits_def[simp]
  pdpt_bits_def[simp] pdpt_shift_bits_def[simp]
  pml4_bits_def[simp] pml4_shift_bits_def[simp]
  table_size_def[simp] ptTranslationBits_def[simp]
  pageBits_def[simp] mask_lower_twice[simp]
  and.assoc[where ?'a = \<open>'a::len word\<close>,symmetric,simp] obj_at_def[simp]
  pde.splits[split] pdpte.splits[split] pml4e.splits[split]
  pte.splits[split]

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

lemma lookup_pdpt_slot_inv:
  "\<lbrace>P\<rbrace> lookup_pdpt_slot pdpt vptr \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add: lookup_pdpt_slot_def)
  apply (wp get_pml4e_wp | wpc)+
  apply clarsimp
  done

lemma lookup_pd_slot_inv:
  "\<lbrace>P\<rbrace> lookup_pd_slot pd vptr \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add: lookup_pd_slot_def)
  apply (rule hoare_pre)
  apply (wp get_pdpte_wp lookup_pdpt_slot_inv hoare_vcg_all_liftE_R hoare_drop_imps| wpc)+
  apply clarsimp
  done

lemma lookup_pt_slot_inv:
  "\<lbrace>P\<rbrace> lookup_pt_slot pd vptr \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add: lookup_pt_slot_def)
  apply (rule hoare_pre)
  apply (wp get_pde_wp lookup_pd_slot_inv hoare_vcg_all_liftE_R hoare_drop_imps| wpc)+
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

crunches set_irq_state
  for cte_wp_at[wp]: "\<lambda>s. P (cte_wp_at P' p s)"

(* Generic lemmas about update arch object  *)

lemma set_object_iflive[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap s\<rbrace>
  set_object ptr (ArchObj aobj)
  \<lbrace>\<lambda>_ s. if_live_then_nonz_cap s\<rbrace>"
  apply (wp set_object_iflive[THEN hoare_set_object_weaken_pre])
  apply (clarsimp simp: a_type_def obj_at_def live_def hyp_live_def
                 split: kernel_object.splits arch_kernel_obj.splits)
  done

(* lemma set_aobject_valid_objs [wp]:
  "\<lbrace>valid_objs and arch_valid_obj obj\<rbrace> set_object ptr (ArchObj obj) \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (wpsimp wp: set_object_valid_objs[THEN hoare_set_object_weaken_pre]
              simp: a_type_def)
  including unfold_objects
  by (clarsimp simp: a_type_def valid_obj_def arch_valid_obj_def) *)

lemma set_aobject_ifunsafe[wp]:
  "\<lbrace>\<lambda>s. if_unsafe_then_cap s\<rbrace>
  set_object ptr (ArchObj obj)
  \<lbrace>\<lambda>_ s. if_unsafe_then_cap s\<rbrace>"
  including unfold_objects
  by (wpsimp wp: set_object_ifunsafe[THEN hoare_set_object_weaken_pre]
           simp: a_type_def)

lemma global_refs_kheap [simp]:
  "global_refs (kheap_update f s) = global_refs s"
  by (simp add: global_refs_def)

crunches set_object
  for global_ref[wp]: "\<lambda>s. P (global_refs s)"
  (wp: crunch_wps)

lemma set_aobj_valid_global[wp]:
  "\<lbrace>\<lambda>s. valid_global_refs s\<rbrace>
  set_object ptr (ArchObj obj)
  \<lbrace>\<lambda>_ s. valid_global_refs s\<rbrace>"
  by (wp valid_global_refs_cte_lift)

lemma set_aobj_valid_kernel_mappings[wp]:
  "\<lbrace>\<lambda>s. valid_kernel_mappings s \<and> valid_kernel_mappings_if_pm (set (second_level_tables (arch_state s))) (ArchObj obj)\<rbrace>
  set_object ptr (ArchObj obj)
  \<lbrace>\<lambda>_ s. valid_kernel_mappings s\<rbrace>"
  apply (wp set_object_v_ker_map[THEN hoare_set_object_weaken_pre])
  apply (clarsimp simp: valid_kernel_mappings_def valid_kernel_mappings_if_pm_def)
  done

lemma valid_vspace_obj_pre:
  "\<lbrakk>kheap s ptr = Some (ArchObj aobj);
   aa_type aobj = aa_type obj; valid_vspace_obj tobj s\<rbrakk>
   \<Longrightarrow> valid_vspace_obj tobj (s\<lparr>kheap := \<lambda>a. if a = ptr then Some (ArchObj obj) else kheap s a\<rparr>)"
  apply (case_tac tobj)
      apply (clarsimp simp: obj_at_def aa_type_def a_type_simps
                     split: arch_kernel_obj.splits if_splits | drule(1) bspec)+
            apply (drule_tac x = x in spec, case_tac "x2 x",
                   (fastforce simp: data_at_def obj_at_def a_type_simps split: pte.splits)+)+
     apply (clarsimp)
     apply (drule_tac x = x in spec, case_tac"x3 x")
       apply ((clarsimp simp: data_at_def obj_at_def a_type_simps aa_type_def
                       split: pte.splits arch_kernel_obj.splits if_splits)+)[3]
    apply (clarsimp)
    apply (drule_tac x = x in spec, case_tac"x4 x")
      apply ((clarsimp simp: data_at_def obj_at_def a_type_simps aa_type_def
                      split: pte.splits arch_kernel_obj.splits if_splits)+)[3]
   apply (clarsimp)
   apply (drule_tac x = x in bspec, simp, case_tac"x5 x")
    apply ((clarsimp simp: data_at_def obj_at_def a_type_simps aa_type_def
                    split: pte.splits arch_kernel_obj.splits if_splits)+)[2]
  apply (clarsimp)
  done

lemma a_type_is_aobj:
 "a_type ko = a_type (ArchObj obj) \<Longrightarrow> \<exists>aobj. ko = ArchObj aobj \<and> aa_type aobj = aa_type obj"
 by (clarsimp simp: a_type_def aa_type_def split: kernel_object.splits if_split_asm)

definition
"valid_global_objs_upd ptr obj ast \<equiv> case obj of
  PageMapL4 pm \<Rightarrow> if ptr = x64_global_pml4 ast then
            empty_table (set (second_level_tables ast)) (ArchObj obj) else True
  | PDPointerTable pdpt \<Rightarrow> if ptr \<in> set (x64_global_pdpts ast) then
                  ((\<forall>x. aligned_pdpte (pdpt x)
                  \<and> (\<forall>r. pdpte_ref (pdpt x) = Some r \<longrightarrow> r \<in> set (x64_global_pds ast)))
                  \<and> valid_global_pdpt pdpt) else True
  | PageDirectory pd \<Rightarrow> if ptr \<in> set (x64_global_pds ast) then
                  (\<forall>x. aligned_pde (pd x) \<and> (\<forall>r. pde_ref (pd x) = Some r \<longrightarrow> r \<in> set (x64_global_pts ast)))
                  else True
  | PageTable pt \<Rightarrow> if ptr \<in> set (x64_global_pts ast) then (\<forall>x. aligned_pte (pt x))
                  else True
  | _ \<Rightarrow> True
  "

lemma aa_type_pml4D:
  "APageMapL4 = aa_type obj \<Longrightarrow> \<exists>pm. obj = PageMapL4 pm"
  by (clarsimp simp: aa_type_def
               split: arch_kernel_obj.splits if_split_asm)

lemma aa_type_PDPTD:
  "APDPointerTable = aa_type obj \<Longrightarrow> \<exists>pdpt. obj = (PDPointerTable pdpt)"
  by (clarsimp simp: aa_type_def
               split: arch_kernel_obj.splits if_split_asm)

lemma aa_type_PTD:
  "APageTable = aa_type obj \<Longrightarrow> \<exists>pt. obj = PageTable pt"
  by (clarsimp simp: aa_type_def
               split: arch_kernel_obj.splits if_split_asm)

lemmas aa_type_eqD = aa_type_pdD[OF sym] aa_type_pml4D aa_type_PDPTD aa_type_PTD

lemma valid_global_pdpts_typD:
  "\<lbrakk>ptr \<in> set (x64_global_pdpts (arch_state s));valid_global_pdpts s\<rbrakk>
  \<Longrightarrow> typ_at (AArch APDPointerTable) ptr s"
  by (fastforce simp: valid_global_pdpts_def)

lemma valid_global_pds_typD:
  "\<lbrakk>p\<in>set (x64_global_pds (arch_state s)); valid_global_pds s\<rbrakk> \<Longrightarrow> typ_at (AArch APageDirectory) p s"
  by (clarsimp simp: valid_global_pds_def)

lemma valid_global_pts_typD:
  "\<lbrakk>p \<in> set (x64_global_pts (arch_state s)); valid_global_pts s\<rbrakk> \<Longrightarrow> typ_at (AArch APageTable) p s"
  by (clarsimp simp: valid_global_pts_def)

lemma a_type_of_ArchObj:
  "a_type (ArchObj ako) = AArch (aa_type ako)"
  by (simp add: a_type_def aa_type_def split: kernel_object.split_asm)

lemma set_object_is_kheap_upd:
  assumes wp: "\<lbrace>preR\<rbrace> set_object ptr (ArchObj aobj) \<lbrace>\<lambda>rv. R \<rbrace>"
  shows "\<lbrakk>preR s; kheap s ptr = Some obj; a_type obj = AArch (aa_type aobj) \<rbrakk> \<Longrightarrow> R (s\<lparr>kheap := \<lambda>x. if x = ptr then Some (ArchObj aobj) else kheap s x\<rparr>)"
  apply (rule use_valid[OF _ wp, where s = s])
    apply (simp add: fun_upd_def set_object_def get_object_def assert_def a_type_simps a_type_of_ArchObj
                     bind_def get_def gets_def return_def put_def fail_def)
  apply simp
  done

lemma set_pt_global_objs [wp]:
  "\<lbrace>valid_global_objs and valid_arch_state
        and (\<lambda>s. valid_global_objs_upd ptr obj (arch_state s))\<rbrace>
    set_object ptr (ArchObj obj)
   \<lbrace>\<lambda>rv. valid_global_objs\<rbrace>"
  apply (clarsimp simp: set_object_def valid_global_objs_def
                        second_level_tables_def)
  apply (wp get_object_wp)
  apply clarsimp
  apply (intro impI allI conjI)
      apply (simp add: valid_vso_at_def)
      apply (clarsimp simp: valid_global_objs_def obj_at_def valid_vspace_obj_pre
                     dest!: a_type_is_aobj)
      apply (clarsimp dest!: a_type_is_aobj aa_type_pml4D
                     simp: valid_arch_state_def aa_type_simps
                           valid_global_objs_upd_def obj_at_def)
      apply (rule set_object_is_kheap_upd[OF valid_pml4e_lift])
         apply (wp | clarsimp | rule conjI | assumption)+
        apply (drule_tac x = x in bspec, simp+)
        apply (simp add: empty_table_def)
       apply simp
      apply (simp add: a_type_simps aa_type_simps)
     apply (clarsimp dest!: a_type_is_aobj aa_type_pml4D
                     simp: valid_arch_state_def aa_type_simps second_level_tables_def
                           valid_global_objs_upd_def obj_at_def)
    apply (fastforce dest: a_type_is_aobj valid_global_pdpts_typD aa_type_PDPTD
                     simp: valid_arch_state_def aa_type_simps
                           valid_global_objs_upd_def obj_at_def)
   apply (fastforce dest: a_type_is_aobj valid_global_pds_typD aa_type_eqD
                    simp: valid_arch_state_def aa_type_simps
                          valid_global_objs_upd_def obj_at_def)
  apply (fastforce dest: a_type_is_aobj aa_type_eqD valid_global_pts_typD
                   simp: valid_arch_state_def aa_type_simps
                         valid_global_objs_upd_def obj_at_def)
  done


(* It is a pity that the following lemmas can not be abstract into a form with set_object *)
lemma store_pte_typ_at:
    "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> store_pte ptr pte \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  apply (simp add: store_pte_def set_pt_def)
  apply wp
  apply (clarsimp simp: obj_at_def a_type_def)
  done

lemmas store_pte_typ_ats [wp] = abs_typ_at_lifts [OF store_pte_typ_at]

lemma mask_table_bits_inner_beauty:
  "is_aligned p 3 \<Longrightarrow>
  (p && ~~ mask table_size) + (ucast ((ucast (p && mask table_size >> word_size_bits))::9 word) << word_size_bits) = (p::word64)"
  by (rule mask_split_aligned;
      simp add: table_size_def ptTranslationBits_def word_size_bits_def)

lemma more_table_bits_inner_beauty:
  fixes x :: "9 word"
  fixes p :: word64
  assumes x: "x \<noteq> ucast (p && mask table_size >> word_size_bits)"
  shows "(p && ~~ mask table_size) + (ucast x << word_size_bits) = p \<Longrightarrow> False"
  by (rule mask_split_aligned_neg[OF _ _ x];
      simp add: table_size_def ptTranslationBits_def word_size_bits_def)

crunches store_pde
  for aligned[wp]: pspace_aligned
  (wp: hoare_drop_imps simp: set_arch_obj_simps)


lemmas undefined_validE_R = hoare_FalseE_R[where f=undefined]


lemma arch_derive_cap_valid_cap:
  "\<lbrace>valid_cap (cap.ArchObjectCap arch_cap)\<rbrace>
  arch_derive_cap arch_cap
  \<lbrace>valid_cap\<rbrace>, -"
  apply(simp add: arch_derive_cap_def)
  apply(cases arch_cap, simp_all add: arch_derive_cap_def o_def)
      apply(rule hoare_pre, wpc?, wp+,
            clarsimp simp add: cap_aligned_def valid_cap_def split: option.splits)+
  done


lemma arch_derive_cap_inv:
  "\<lbrace>P\<rbrace> arch_derive_cap arch_cap \<lbrace>\<lambda>rv. P\<rbrace>"
  apply(simp add: arch_derive_cap_def, cases arch_cap, simp_all)
      apply(rule hoare_pre, wpc?, wp+, simp)+
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

lemma ucast_ucast_asid_high_bits [simp]:
  "ucast (ucast (asid_high_bits_of asid)::word64) = asid_high_bits_of asid"
  by (word_eqI_solve simp: asid_low_bits_def)

lemma ucast_ucast_asid_low_bits [simp]:
  "ucast (ucast (asid_low_bits_of asid)::word64) = asid_low_bits_of asid"
  by (word_eqI_solve simp: asid_low_bits_def)

lemma ucast_mask_asid_low_bits [simp]:
  "ucast ((asid::word64) && mask asid_low_bits) = (ucast asid :: 9 word)"
  by (word_eqI_solve simp: asid_low_bits_def)

lemma mask_asid_low_bits_ucast_ucast:
  "((asid::word64) && mask asid_low_bits) = ucast (ucast asid :: 9 word)"
  by (word_eqI_solve simp: asid_low_bits_def)


context
  fixes m s :: nat and b w :: "'a::len word"
  assumes w_size: "m + s \<le> size w"
      and b_align: "is_aligned b (m + s)"
begin

private lemma aligned_base_split_mask_redundant_right:
  "b + (w && mask m << s) && mask (m + s) >> s = w && mask m"
  using w_size b_align
  apply (subst mask_add_aligned[OF b_align])
  by (auto simp: and_mask is_aligned_shiftl_self is_aligned_shiftr_shiftl
                 shiftl_shiftl shiftr_shiftr word_size)

private lemma aligned_base_split_mask_redundant_left:
  "b + (w && mask m << s) && ~~ mask (m + s) = b"
  by (metis w_size b_align AND_NOT_mask_plus_AND_mask_eq NOT_mask_AND_mask and_mask_shiftl_comm
            is_aligned_neg_mask_eq mask_out_add_aligned)

lemmas aligned_base_split_mask_redundant =
  aligned_base_split_mask_redundant_right
  aligned_base_split_mask_redundant_left

end


context
  fixes vptr :: word64
begin

private lemma vptr_size:
  "ptTranslationBits + word_size_bits \<le> size (vptr >> s)"
  by (auto simp: word_size ptTranslationBits_def word_size_bits_def)

lemma pml4_shifting:
  assumes "is_aligned pm pml4_bits"
  shows
    "pm + (get_pml4_index vptr << word_size_bits) && mask pml4_bits >> word_size_bits = get_pml4_index vptr"
    "pm + (get_pml4_index vptr << word_size_bits) && ~~ mask pml4_bits = pm"
  using assms aligned_base_split_mask_redundant[OF vptr_size]
  by (auto simp: get_pml4_index_def pml4_bits_def table_size_def)

lemma pdpt_shifting:
  assumes "is_aligned pdpt pdpt_bits"
  shows
    "pdpt + (get_pdpt_index vptr << word_size_bits) && mask pdpt_bits >> word_size_bits = get_pdpt_index vptr"
    "pdpt + (get_pdpt_index vptr << word_size_bits) && ~~ mask pdpt_bits = pdpt"
  using assms aligned_base_split_mask_redundant[OF vptr_size]
  by (auto simp: get_pdpt_index_def pdpt_bits_def table_size_def)

lemma pd_shifting:
  assumes "is_aligned pd pd_bits"
  shows
    "pd + (get_pd_index vptr << word_size_bits) && mask pd_bits >> word_size_bits = get_pd_index vptr"
    "pd + (get_pd_index vptr << word_size_bits) && ~~ mask pd_bits = pd"
  using assms aligned_base_split_mask_redundant[OF vptr_size]
  by (auto simp: get_pd_index_def pd_bits_def table_size_def)

lemma pt_shifting:
  assumes "is_aligned pt pt_bits"
  shows
    "pt + (get_pt_index vptr << word_size_bits) && mask pt_bits >> word_size_bits = get_pt_index vptr"
    "pt + (get_pt_index vptr << word_size_bits) && ~~ mask pt_bits = pt"
  using assms aligned_base_split_mask_redundant[OF vptr_size]
  by (auto simp: get_pt_index_def pt_bits_def table_size_def)

end

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

lemma is_aligned_pml4:
  "\<lbrakk> page_map_l4_at pm s; pspace_aligned s \<rbrakk> \<Longrightarrow> is_aligned pm pml4_bits"
  apply (clarsimp simp: pspace_aligned_def obj_at_def)
  apply (drule bspec, blast)
  by (clarsimp simp: bit_simps)

lemmas pt_shifting_at = pt_shifting[OF is_aligned_pt]
lemmas pd_shifting_at = pd_shifting[OF is_aligned_pd]
lemmas pdpt_shifting_at = pdpt_shifting[OF is_aligned_pdpt]
lemmas pml4_shifting_at = pml4_shifting[OF is_aligned_pml4]


lemma kernel_mapping_slots_empty_pml4eI:
  "\<lbrakk>equal_kernel_mappings s; valid_global_objs s; valid_arch_state s;
    kheap s p = Some (ArchObj (PageMapL4 pm)); x \<in> kernel_mapping_slots\<rbrakk> \<Longrightarrow>
   (\<forall>r. pml4e_ref (pm x) = Some r \<longrightarrow> r \<in> set (second_level_tables (arch_state s)))"
  apply (clarsimp simp: invs_def valid_state_def equal_kernel_mappings_def valid_global_objs_def)
  apply (erule_tac x=p in allE, erule_tac x="x64_global_pml4 (arch_state s)" in allE)
  including unfold_objects
  by clarsimp (simp add: empty_table_def valid_arch_state_def a_type_def)


lemma invs_valid_global_pts:
  "invs s \<Longrightarrow> valid_global_pts s"
  by (clarsimp simp: invs_def valid_state_def valid_arch_state_def)

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

lemma data_at_aligned:
  "\<lbrakk> data_at sz p s; pspace_aligned s \<rbrakk> \<Longrightarrow> is_aligned p (pageBitsForSize sz)"
  by (erule pspace_alignedE[where x=p]; fastforce simp: data_at_def obj_at_def)

lemma page_table_pte_at_diffE:
  "\<lbrakk> page_table_at p s; q - p = x << word_size_bits;
    x < 2^(pt_bits - word_size_bits); pspace_aligned s \<rbrakk> \<Longrightarrow> pte_at q s"
  apply (clarsimp simp: diff_eq_eq add.commute)
  including pagebits
  apply (erule page_table_pte_atI; simp add: word_size_bits_def)
  done

lemma canonical_address_range:
  "canonical_address x = (x \<le> mask 47 \<or> ~~ mask 47 \<le> x)"
  by (simp add: canonical_address_def canonical_address_of_def scast_ucast_mask_compare)

lemma canonical_address_of_mask:
  "canonical_address_of x = (if x \<le> mask 47 then ucast x else ucast x || ~~ mask 47)"
  apply (simp add: canonical_address_of_def mask_def)
  by word_bitwise

lemma canonical_address_sign_extended: "canonical_address p = sign_extended 47 p"
  apply (intro iffI;
         simp add: canonical_address_range sign_extended_def
                   le_mask_high_bits neg_mask_le_high_bits word_size)
  apply fastforce
  apply (case_tac "test_bit p 47"; intro disjI1 disjI2 ballI; case_tac "i = 47"; fastforce)
  done

lemmas canonical_address_high_bits
  = canonical_address_sign_extended[THEN iffD1, THEN sign_extended_high_bits]

lemma canonical_address_add:
  assumes "is_aligned p n"
  assumes "f < 2 ^ n"
  assumes "n \<le> 47"
  assumes "canonical_address p"
  shows "canonical_address (p + f)"
  using assms sign_extended_add
  unfolding canonical_address_sign_extended
  by auto

(* Lemmas about looking up entries in vspace tables.
   For each level of table, we prove a single private lemma which tells us
   everything we need to know in order to be able to say something about the
   next level down. These lemmas have post-conditions with several conjuncts,
   which means that the lemmas  may not work well with wp. So we then pull
   each of these lemmas apart to produce several facts which give access to
   the post-condition conjuncts separately. *)

context
  fixes pm vptr :: word64
begin

lemma kernel_base_kernel_mapping_slots:
  assumes "vptr < pptr_base" "canonical_address vptr"
  shows "ucast (get_pml4_index vptr) \<notin> kernel_mapping_slots"
  using assms
  apply (simp add: kernel_mapping_slots_def pptr_base_def pptrBase_def bit_simps get_pml4_index_def)
  apply (subst ucast_le_ucast[symmetric, where 'a=9 and 'b=64];
         simp add: ucast_ucast_mask mask_def canonical_address_range word_not_le)
  apply word_bitwise
  by blast

private lemma vtable_index_mask:
  fixes r :: word64
  shows "(r && mask table_size >> word_size_bits) && mask 9
          = r && mask table_size >> word_size_bits"
  by (simp add: table_size_def ptTranslationBits_def word_size_bits_def
                and_mask_shiftr_comm word_size)

(* We reuse the same pre-condition several times, so we make an abbreviation.
   We also want two versions of the pre-condition: one which requires a specific
   vs_lookup for the PML4, and one which merely requires that some vs_lookup
   exists; so we parameterise over the vs_lookup. *)

private abbreviation (input)
  "pre pm_lookup pm' vptr' \<equiv> pspace_aligned and valid_vspace_objs and valid_arch_state
                      and equal_kernel_mappings and valid_global_objs and pm_lookup
                      and K (is_aligned (pm'::64 word) pml4_bits \<and> vptr' < pptr_base \<and> canonical_address vptr')"

private abbreviation (input)
  "pdpt_ref pm_ref \<equiv> VSRef (get_pml4_index vptr) (Some APageMapL4) # pm_ref "

lemma lookup_pdpt_slot_wp:
  "\<lbrace> \<lambda>s. \<forall>rv. (\<forall>pm_ref. pre (pm_ref \<rhd> pm) pm vptr s \<longrightarrow>
                          pdpte_at rv s
                            \<and> (pdpt_ref pm_ref \<rhd> (rv && ~~ mask pdpt_bits)) s
                            \<and> get_pdpt_index vptr = rv && mask pdpt_bits >> word_size_bits)
              \<longrightarrow> Q rv s \<rbrace>
     lookup_pdpt_slot pm vptr
   \<lbrace> Q \<rbrace>, -"
  apply (clarsimp simp: lookup_pdpt_slot_def)
  apply (wp get_pml4e_wp | wpc)+
  apply (clarsimp, drule spec, erule mp)
  apply (clarsimp simp: lookup_pml4_slot_def pml4_shifting)
  apply (frule (1) kernel_base_kernel_mapping_slots)
  apply (frule (2) valid_vspace_objsD; clarsimp)
  apply (bspec "ucast (get_pml4_index vptr)"; clarsimp)
  apply (rule conjI)
   apply (erule pd_pointer_table_pdpte_atI, simp_all)
   apply (simp add: get_pdpt_index_def bit_simps mask_def)
   apply (rule order_le_less_trans, rule word_and_le1, simp)
  apply (frule vs_lookup_step)
   apply (rule vs_lookup1I[OF _ _ refl], assumption)
   apply (simp add: vs_refs_def)
   apply (rule image_eqI[rotated])
    apply (rule_tac x="ucast (get_pml4_index vptr)" in graph_ofI)
    by (simp add: kernel_base_kernel_mapping_slots pml4e_ref_def get_pml4_index_def pdpt_shifting_at
                  ucast_ucast_mask ptTranslationBits_def)+

private abbreviation (input)
  "pd_ref pm_ref \<equiv> VSRef (get_pdpt_index vptr) (Some APDPointerTable) # pdpt_ref pm_ref"

lemma lookup_pd_slot_wp:
  "\<lbrace> \<lambda>s. \<forall>rv. (\<forall>pm_ref. pre (pm_ref \<rhd> pm) pm vptr s \<longrightarrow>
                          pde_at rv s
                            \<and> (pd_ref pm_ref \<rhd> (rv && ~~ mask pd_bits)) s
                            \<and> get_pd_index vptr = rv && mask pd_bits >> word_size_bits)
              \<longrightarrow> Q rv s \<rbrace>
     lookup_pd_slot pm vptr
   \<lbrace> Q \<rbrace>, -"
  apply (clarsimp simp: lookup_pd_slot_def)
  apply (wp get_pdpte_wp lookup_pdpt_slot_wp | wpc | simp)+
  apply (clarsimp; drule spec; erule mp; clarsimp)
  apply (drule spec; erule (1) impE; clarsimp)
  apply (frule (2) valid_vspace_objsD; clarsimp)
  apply (drule_tac x="ucast (rv && mask pdpt_bits >> word_size_bits)" in spec; clarsimp)
  apply (rule conjI)
   apply (erule page_directory_pde_atI, simp_all)
   apply (simp add: get_pd_index_def bit_simps mask_def)
   apply (rule order_le_less_trans, rule word_and_le1, simp)
  apply (frule vs_lookup_step, rule vs_lookup1I[OF _ _ refl], assumption)
   apply (simp add: vs_refs_def)
   apply (rule image_eqI[rotated])
    apply (rule_tac x="ucast (rv && mask pdpt_bits >> word_size_bits)" in graph_ofI)
    by (simp add: pdpte_ref_def pd_shifting_at ucast_ucast_mask pdpt_bits_def vtable_index_mask)+

private abbreviation (input)
  "pt_ref pm_ref \<equiv> VSRef (get_pd_index vptr) (Some APageDirectory) # pd_ref pm_ref"

lemma lookup_pt_slot_wp:
  "\<lbrace> \<lambda>s. \<forall>rv. (\<forall>pm_ref. pre (pm_ref \<rhd> pm) pm vptr s \<longrightarrow>
                          pte_at rv s
                            \<and> (pt_ref pm_ref \<rhd> (rv && ~~ mask pt_bits)) s
                            \<and> get_pt_index vptr = rv && mask pt_bits >> word_size_bits)
              \<longrightarrow> Q rv s \<rbrace>
     lookup_pt_slot pm vptr
   \<lbrace> Q \<rbrace>, -"
  apply (clarsimp simp: lookup_pt_slot_def)
  apply (wp get_pde_wp lookup_pd_slot_wp | wpc | simp)+
  apply (clarsimp; drule spec; erule mp; clarsimp)
  apply (drule spec; erule (1) impE; clarsimp)
  apply (frule (2) valid_vspace_objsD; clarsimp)
  apply (drule_tac x="ucast (rv && mask pd_bits >> word_size_bits)" in spec; clarsimp)
  apply (rule conjI)
   apply (erule page_table_pte_atI, simp_all)
   apply (simp add: get_pt_index_def bit_simps mask_def)
   apply (rule order_le_less_trans, rule word_and_le1, simp)
  apply (frule vs_lookup_step, rule vs_lookup1I[OF _ _ refl], assumption)
   apply (simp add: vs_refs_def)
   apply (rule image_eqI[rotated])
    apply (rule_tac x="ucast (rv && mask pd_bits >> word_size_bits)" in graph_ofI)
    by (simp add: pde_ref_def pt_shifting_at ucast_ucast_mask pd_bits_def vtable_index_mask)+

(* The following older lemmas are kept for a few existing proofs.
   They are weaker than the above lookup_*_slot_wp rules, and harder to use.
   New proofs should use the lookup_*_slot_wp rules. *)

private lemma lookup_pd_slot_rv:
  "\<And>pm_ref.
    \<lbrace> pre (pm_ref \<rhd> pm) pm vptr \<rbrace>
      lookup_pd_slot pm vptr
    \<lbrace> \<lambda>rv s. pde_at rv s
              \<and> (pd_ref pm_ref \<rhd> (rv && ~~ mask pd_bits)) s
              \<and> (get_pd_index vptr = rv && mask pd_bits >> word_size_bits) \<rbrace>,-"
  by (rule hoare_pre, rule lookup_pd_slot_wp, clarsimp)

private lemma lookup_pdpt_slot_rv:
  "\<And>pm_ref.
    \<lbrace> pre (pm_ref \<rhd> pm) pm vptr \<rbrace>
      lookup_pdpt_slot pm vptr
    \<lbrace> \<lambda>rv s. pdpte_at rv s
              \<and> (pdpt_ref pm_ref \<rhd> (rv && ~~ mask pdpt_bits)) s
              \<and> (get_pdpt_index vptr = rv && mask pdpt_bits >> word_size_bits) \<rbrace>,-"
  by (rule hoare_pre, rule lookup_pdpt_slot_wp, clarsimp)

private lemma lookup_pt_slot_rv:
  "\<And>pm_ref.
    \<lbrace> pre (pm_ref \<rhd> pm) pm vptr \<rbrace>
      lookup_pt_slot pm vptr
    \<lbrace>\<lambda>rv s. pte_at rv s
             \<and> (pt_ref pm_ref \<rhd> (rv && ~~ mask pt_bits)) s
             \<and> (get_pt_index vptr = rv && mask pt_bits >> word_size_bits) \<rbrace>,-"
  by (rule hoare_pre, rule lookup_pt_slot_wp, clarsimp)

(* It's awkward to prove the following more generally, since these are probably only true
   when the vs_lookups are only under conjunctions. *)

private lemma vs_lookup_all_ex_convert_pre:
  assumes "\<And>ref. \<lbrace> pre (ref \<rhd> p) pm vptr \<rbrace> f \<lbrace> R \<rbrace>,-"
  shows "\<lbrace> pre (\<exists>\<rhd> p) pm vptr \<rbrace> f \<lbrace> R \<rbrace>,-"
  using assms by (simp add: validE_R_def validE_def valid_def) blast

private lemma vs_lookup_all_ex_convert_post:
  assumes "\<And>ref. \<lbrace> pre (ref \<rhd> p) pm vptr \<rbrace> f \<lbrace> \<lambda>rv. g ref \<rhd> h rv \<rbrace>,-"
  shows "\<lbrace> pre (\<exists>\<rhd> p) pm vptr \<rbrace> f \<lbrace> \<lambda>rv. \<exists>\<rhd> h rv \<rbrace>,-"
  using assms by (simp add: validE_R_def validE_def valid_def) blast

(* We now break the lookup lemmas apart, to get access to the post-condition conjuncts
   separately. We also provide versions which merely assert the existence of each vs_lookup. *)

private lemmas get_ent_pm = validE_R_post_conjD1
private lemmas get_ent_ex = vs_lookup_all_ex_convert_pre[OF get_ent_pm]
private lemmas get_lookup = validE_R_post_conjD1[OF validE_R_post_conjD2]
private lemmas get_lkp_ex = vs_lookup_all_ex_convert_post[OF get_lookup]

lemmas lookup_pdpt_slot_pdpte_ex     [wp] = get_ent_ex[OF lookup_pdpt_slot_rv]
lemmas lookup_pdpt_slot_vs_lookup    [wp] = get_lookup[OF lookup_pdpt_slot_rv]
lemmas lookup_pdpt_slot_vs_lookup_ex [wp] = get_lkp_ex[OF lookup_pdpt_slot_rv]

lemmas lookup_pd_slot_pde_ex         [wp] = get_ent_ex[OF lookup_pd_slot_rv]
lemmas lookup_pd_slot_vs_lookup      [wp] = get_lookup[OF lookup_pd_slot_rv]
lemmas lookup_pd_slot_vs_lookup_ex   [wp] = get_lkp_ex[OF lookup_pd_slot_rv]

lemmas lookup_pt_slot_pte_ex         [wp] = get_ent_ex[OF lookup_pt_slot_rv]
lemmas lookup_pt_slot_vs_lookup      [wp] = get_lookup[OF lookup_pt_slot_rv]
lemmas lookup_pt_slot_vs_lookup_ex   [wp] = get_lkp_ex[OF lookup_pt_slot_rv]

lemma create_mapping_entries_valid [wp]:
  "\<lbrace> pre (\<exists>\<rhd> pm) pm vptr \<rbrace>
     create_mapping_entries base vptr sz vm_rights attrib pm
   \<lbrace>valid_mapping_entries\<rbrace>,-"
  apply (cases sz)
    apply (rule hoare_pre)
     apply (wpsimp simp: valid_mapping_entries_def)+
  done

end

context begin

method hammer =
  (simp?; erule is_aligned_weaken[rotated]; simp add: is_aligned_def pptrBase_def)

lemma is_aligned_addrFromPPtr_eq: "n \<le> 39 \<Longrightarrow> is_aligned (addrFromPPtr p) n = is_aligned p n"
  apply (simp add: addrFromPPtr_def; rule iffI)
   apply (drule aligned_sub_aligned[where b="-pptrBase"]; hammer)
  apply (erule aligned_sub_aligned; hammer)
  done

lemma is_aligned_ptrFromPAddr_eq: "n \<le> 39 \<Longrightarrow> is_aligned (ptrFromPAddr p) n = is_aligned p n"
  apply (simp add: ptrFromPAddr_def; rule iffI)
   apply (drule aligned_add_aligned[where y="-pptrBase"]; hammer)
  apply (erule aligned_add_aligned; hammer)
  done

end

lemma is_aligned_addrFromPPtr_n:
  "\<lbrakk> is_aligned p n; n \<le> 39 \<rbrakk> \<Longrightarrow> is_aligned (addrFromPPtr p) n"
  by (simp add: is_aligned_addrFromPPtr_eq)

lemma is_aligned_ptrFromPAddr_n:
  "\<lbrakk>is_aligned x sz; sz \<le> 39\<rbrakk> \<Longrightarrow> is_aligned (ptrFromPAddr x) sz"
  by (simp add: is_aligned_ptrFromPAddr_eq)

lemma is_aligned_addrFromPPtr:
  "is_aligned p pageBits \<Longrightarrow> is_aligned (addrFromPPtr p) pageBits"
  by (simp add: is_aligned_addrFromPPtr_n pageBits_def)

lemma is_aligned_ptrFromPAddr:
  "is_aligned p pageBits \<Longrightarrow> is_aligned (ptrFromPAddr p) pageBits"
  by (simp add: is_aligned_ptrFromPAddr_n pageBits_def)

lemma is_aligned_addrFromPPtr_pageBitsForSize:
  "is_aligned (addrFromPPtr p) (pageBitsForSize sz) = is_aligned p (pageBitsForSize sz)"
  by (cases sz; simp add: is_aligned_addrFromPPtr_eq bit_simps)

lemma is_aligned_ptrFromPAddr_pageBitsForSize:
  "is_aligned (ptrFromPAddr p) (pageBitsForSize sz) = is_aligned p (pageBitsForSize sz)"
  by (cases sz; simp add: is_aligned_ptrFromPAddr_eq bit_simps)

lemma data_at_vmsz_aligned:
  "data_at sz (ptrFromPAddr base) s \<Longrightarrow> pspace_aligned s \<Longrightarrow> vmsz_aligned base sz"
  by (cases sz)
     (auto simp: data_at_def obj_at_def vmsz_aligned_def bit_simps
          dest!: pspace_alignedD
          elim!: iffD1[OF is_aligned_ptrFromPAddr_eq, rotated])

lemma create_mapping_entries_valid_slots [wp]:
  "\<lbrace> pspace_aligned and valid_vspace_objs and valid_arch_state and equal_kernel_mappings
        and valid_global_objs and (\<exists>\<rhd> pm) and data_at sz (ptrFromPAddr base)
        and K (is_aligned pm pml4_bits \<and> vptr < pptr_base \<and> canonical_address vptr
                \<and> vm_rights \<in> valid_vm_rights) \<rbrace>
     create_mapping_entries base vptr sz vm_rights attrib pm
   \<lbrace>\<lambda>m. valid_slots m\<rbrace>,-"
  apply (cases sz; simp; rule hoare_pre)
       apply (wp | clarsimp simp: valid_slots_def elim!: data_at_vmsz_aligned
                 | rule lookup_pt_slot_inv_any lookup_pd_slot_inv_any lookup_pdpt_slot_inv_any)+
  done

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
      apply (clarsimp simp: valid_obj_def arch_valid_obj_def)
     apply clarsimp
     apply fastforce
    apply (erule allE, erule impE, blast)
    apply (clarsimp simp: valid_obj_def arch_valid_obj_def)
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
      apply (clarsimp simp: valid_obj_def arch_valid_obj_def)
     apply clarsimp
     apply fastforce
    apply (erule allE, erule impE, blast)
    apply (clarsimp simp: valid_obj_def arch_valid_obj_def)
   apply assumption
  by (simp add: a_type_def)
  done

lemma store_pdpte_valid_objs [wp]:
  "\<lbrace>valid_objs and (%s. wellformed_pdpte pdpte)\<rbrace> store_pdpte p pdpte \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: store_pdpte_def set_pdpt_def get_pdpt_def bind_assoc get_object_def)
  apply (rule hoare_pre)
   apply (wp set_object_valid_objs | wpc)+
  apply (clarsimp simp: valid_objs_def dom_def simp del: fun_upd_apply)
  apply (erule allE, erule impE, blast)
  apply (clarsimp simp: valid_obj_def arch_valid_obj_def)
  done

lemma store_pml4e_arch [wp]:
  "\<lbrace>\<lambda>s. P (arch_state s)\<rbrace> store_pml4e p pml4e \<lbrace>\<lambda>_ s. P (arch_state s)\<rbrace>"
  by (simp add: store_pml4e_def set_arch_obj_simps | wp)+

lemma store_pdpte_arch [wp]:
  "\<lbrace>\<lambda>s. P (arch_state s)\<rbrace> store_pdpte p pdpte \<lbrace>\<lambda>_ s. P (arch_state s)\<rbrace>"
  by (simp add: store_pdpte_def set_arch_obj_simps | wp)+

lemma store_pde_arch [wp]:
  "\<lbrace>\<lambda>s. P (arch_state s)\<rbrace> store_pde p pde \<lbrace>\<lambda>_ s. P (arch_state s)\<rbrace>"
  by (simp add: store_pde_def set_arch_obj_simps | wp)+

lemma store_pte_arch [wp]:
  "\<lbrace>\<lambda>s. P (arch_state s)\<rbrace> store_pte p pte \<lbrace>\<lambda>_ s. P (arch_state s)\<rbrace>"
  apply (simp add: store_pte_def set_arch_obj_simps | wp)+
  done

lemma store_pte_valid_pte [wp]:
  "\<lbrace>valid_pte pt\<rbrace> store_pte p pte \<lbrace>\<lambda>_. valid_pte pt\<rbrace>"
  by (wp valid_pte_lift store_pte_typ_at)

lemma store_pde_valid_pde [wp]:
  "\<lbrace>valid_pde pde\<rbrace> store_pde slot pde' \<lbrace>\<lambda>rv. valid_pde pde\<rbrace>"
  by (wp valid_pde_lift | simp add: store_pde_def set_arch_obj_simps)+

lemma store_pdpte_valid_pdpte [wp]:
  "\<lbrace>valid_pdpte pdpte\<rbrace> store_pdpte slot pdpte' \<lbrace>\<lambda>rv. valid_pdpte pdpte\<rbrace>"
  by (wp valid_pdpte_lift | simp add: store_pdpte_def set_arch_obj_simps)+

lemma store_pml4e_valid_pml4e [wp]:
  "\<lbrace>valid_pml4e pml4e\<rbrace> store_pml4e slot pml4e' \<lbrace>\<lambda>rv. valid_pml4e pml4e\<rbrace>"
  by (wp valid_pml4e_lift | simp add: store_pml4e_def set_arch_obj_simps)+

lemma decrease_predictI:
  assumes decrease: "\<And>A B. A\<subseteq>B \<Longrightarrow> P A \<Longrightarrow> P B"
  shows "\<lbrakk>A \<subseteq> B; P A \<rbrakk> \<Longrightarrow> P B"
  by (auto simp: decrease)

lemma set_aobj_kernel_window[wp]:
  "\<lbrace>pspace_in_kernel_window\<rbrace> set_object p (ArchObj obj) \<lbrace>\<lambda>rv. pspace_in_kernel_window\<rbrace>"
  apply (wp set_object_pspace_in_kernel_window[THEN hoare_set_object_weaken_pre])
  apply (clarsimp simp: obj_at_def a_type_def
                 split: kernel_object.split_asm
                        arch_kernel_obj.split_asm)
  done

lemma set_aobj_valid_global_vspace_mappings[wp]:
  "\<lbrace>\<lambda>s. valid_global_vspace_mappings s \<and> valid_global_objs s \<and> (aa_type obj \<noteq> AASIDPool \<longrightarrow> p \<notin> global_refs s)\<rbrace>
      set_object p (ArchObj obj)
   \<lbrace>\<lambda>rv. valid_global_vspace_mappings\<rbrace>"
  apply (wp set_object_global_vspace_mappings[THEN hoare_set_object_weaken_pre])
  apply (clarsimp simp: obj_at_def a_type_def aa_type_def
                 split: kernel_object.split_asm
                        arch_kernel_obj.split_asm)
  done

lemma set_aobj_valid_ioc[wp]:
  "\<lbrace>valid_ioc\<rbrace> set_object p (ArchObj obj) \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  apply (wp set_object_valid_ioc_no_caps[THEN hoare_set_object_weaken_pre])
  apply (clarsimp simp: a_type_simps obj_at_def is_tcb is_cap_table
                 split: kernel_object.splits arch_kernel_obj.splits)
  done

lemma set_aobj_only_idle [wp]:
  "\<lbrace>only_idle\<rbrace> set_object p (ArchObj aobj) \<lbrace>\<lambda>_. only_idle\<rbrace>"
  by (wp only_idle_lift)

lemma set_aobj_equal_mappings [wp]:
  "\<lbrace>equal_kernel_mappings and
    (\<lambda>s. obj_at (\<lambda>ko. (case aobj of (PageMapL4 pm) \<Rightarrow> (\<exists>pm'. ko = (ArchObj (PageMapL4 pm'))
         \<and> (\<forall>x \<in> kernel_mapping_slots. pm x = pm' x)) | _ \<Rightarrow> True)) p s)
   \<rbrace> set_object p (ArchObj aobj) \<lbrace>\<lambda>rv. equal_kernel_mappings\<rbrace>"
  apply (wp set_object_equal_mappings[THEN hoare_set_object_weaken_pre])
  apply (clarsimp simp: equal_kernel_mappings_def obj_at_def a_type_simps)
  done

lemma set_aobj_respects_device_region[wp]:
  "\<lbrace>pspace_respects_device_region\<rbrace> set_object p (ArchObj aobj) \<lbrace>\<lambda>rv. pspace_respects_device_region\<rbrace>"
  apply (wp set_object_pspace_respects_device_region[THEN hoare_set_object_weaken_pre])
  apply (clarsimp simp: obj_at_def a_type_def
                 split: Structures_A.kernel_object.split_asm
                        arch_kernel_obj.split_asm)
  done

lemma set_aobj_caps_in_kernel_window[wp]:
  "\<lbrace>cap_refs_in_kernel_window\<rbrace> set_object p (ArchObj aobj) \<lbrace>\<lambda>rv. cap_refs_in_kernel_window\<rbrace>"
  apply (wp set_object_cap_refs_in_kernel_window[THEN hoare_set_object_weaken_pre])
  apply (clarsimp simp: obj_at_def a_type_def
                 split: kernel_object.split_asm if_splits
                        arch_kernel_obj.split_asm)
  done

lemma set_aobj_caps_respects_device_region[wp]:
  "\<lbrace>cap_refs_respects_device_region\<rbrace> set_object p (ArchObj aobj) \<lbrace>\<lambda>rv. cap_refs_respects_device_region\<rbrace>"
  apply (wp set_object_cap_refs_respects_device_region[THEN hoare_set_object_weaken_pre])
  apply (clarsimp simp: obj_at_def a_type_def
                 split: Structures_A.kernel_object.split_asm if_splits
                        arch_kernel_obj.split_asm)
  done

lemma valid_machine_stateE:
  assumes vm: "valid_machine_state s"
  assumes e: "\<lbrakk>in_user_frame p s
    \<or> underlying_memory (machine_state s) p = 0 \<rbrakk> \<Longrightarrow> E "
  shows E
  using vm
  apply (clarsimp simp: valid_machine_state_def)
  apply (drule_tac x = p in spec)
  apply (rule e)
  apply auto
  done

lemma in_user_frame_same_type_upd:
  "\<lbrakk>typ_at type p s; type = a_type obj; in_user_frame q s\<rbrakk>
    \<Longrightarrow> in_user_frame q (s\<lparr>kheap := (kheap s)(p \<mapsto> obj)\<rparr>)"
  apply (clarsimp simp: in_user_frame_def obj_at_def)
  apply (rule_tac x=sz in exI)
  apply (auto simp: a_type_simps)
  done

lemma valid_machine_state_heap_updI:
  assumes vm : "valid_machine_state s"
  assumes tyat : "typ_at type p s"
  shows "a_type obj = type \<Longrightarrow> valid_machine_state (s\<lparr>kheap := (kheap s)(p \<mapsto> obj)\<rparr>)"
  apply (clarsimp simp: valid_machine_state_def)
  subgoal for p
   apply (rule valid_machine_stateE[OF vm,where p = p])
   apply (elim disjE,simp_all)
   apply (drule(1) in_user_frame_same_type_upd[OF tyat])
    apply simp+
   done
  done

lemma set_aobj_vms[wp]:
  "\<lbrace>valid_machine_state\<rbrace> set_object p (ArchObj obj) \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  apply (simp add: set_object_def)
  apply (wp get_object_wp)
  apply clarify
  apply (erule valid_machine_state_heap_updI)
   apply (fastforce simp: obj_at_def a_type_def
                   split: kernel_object.splits arch_kernel_obj.splits)+
  done

lemma image_in_rtrancl_image:
  "m `` f \<subseteq> m ^* `` f"
  by auto

definition "set_diff A B \<equiv> A - B \<union> (B - A)"

declare graph_of_None_update[simp]
declare graph_of_Some_update[simp]

lemma set_object_caps_of_state:
  "\<lbrace>(\<lambda>s. \<not>(tcb_at p s) \<and> \<not>(\<exists>n. cap_table_at n p s)) and
    K ((\<forall>x y. obj \<noteq> CNode x y) \<and> (\<forall>x. obj \<noteq> TCB x)) and
    (\<lambda>s. P (caps_of_state s))\<rbrace>
   set_object p obj
   \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  apply (wpsimp wp: set_object_wp)
  apply (erule rsubst[where P=P])
  apply (rule ext)
  apply (simp add: caps_of_state_cte_wp_at obj_at_def is_cap_table_def
                   is_tcb_def)
  apply (auto simp: cte_wp_at_cases)
  done

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


lemma caps_of_slot_test:
  "((\<exists>slot. caps_of_state s slot =
                 Some (ArchObjectCap (PageTableCap p None))) \<longrightarrow>
          pt = (\<lambda>x. InvalidPTE))
   = ((\<exists>slot. caps_of_state s slot =
                 Some (ArchObjectCap (PageTableCap p None))) \<longrightarrow>
          pt = (\<lambda>x. InvalidPTE)) \<or>
         (\<forall>slot. \<exists>asid. caps_of_state s slot =
             Some (ArchObjectCap (PageTableCap p (Some asid))))"
   by clarsimp

definition
"valid_table_caps_aobj cs as obj r \<equiv> \<forall>p cap. cs p = Some cap \<longrightarrow>
              (is_pd_cap cap \<or> is_pt_cap cap \<or> is_pdpt_cap cap \<or> is_pml4_cap cap) \<longrightarrow>
              cap_asid cap = None \<longrightarrow> r \<in> obj_refs cap \<longrightarrow> empty_table (set (second_level_tables as)) obj"

lemma a_type_of_arch:
  "a_type (ArchObj aobj) = AArch (aa_type aobj)"
  by (simp add: a_type_def aa_type_def)

lemma set_objects_caps [wp]:
  "\<lbrace>valid_table_caps and
    (\<lambda>s. typ_at (AArch (aa_type aobj)) p s \<longrightarrow> valid_table_caps_aobj (caps_of_state s) (arch_state s) (ArchObj aobj) p)\<rbrace>
   set_object p (ArchObj aobj)
   \<lbrace>\<lambda>rv. valid_table_caps\<rbrace>"
  apply (clarsimp simp: valid_table_caps_def)
  apply (rule hoare_pre)
  apply (wps set_object_caps_of_state)
  apply (clarsimp simp: set_object_def)
  apply (wp get_object_wp)
  apply clarsimp
  apply (case_tac "r \<noteq> p")
   apply (clarsimp simp: obj_at_def)+
  apply (thin_tac "\<forall>x. P x" for P)
  apply (simp add: a_type_of_arch)
  apply (clarsimp simp: valid_table_caps_aobj_def)
  done

(* FIXME: Move to Invariants_A *)
lemma pte_ref_pagesD:
  "pte_ref_pages (pt y) = Some x \<Longrightarrow>
   (VSRef (ucast y) (Some APageTable), x)
   \<in> vs_refs_pages (ArchObj (PageTable pt))"
  by (auto simp: pte_ref_pages_def vs_refs_pages_def graph_of_def)

lemma vs_ref_lvl_obj_same_type:
  "a_type ko = a_type ko'  \<Longrightarrow> vs_ref_lvl (Some ko) = vs_ref_lvl (Some ko')"
  by (simp add: a_type_def vs_ref_lvl_def vs_ref_lvl_arch_def aa_type_simps
      split: kernel_object.splits if_splits arch_kernel_obj.splits)

lemma valid_vspace_obj_kheap_upd:
  "\<lbrakk>typ_at (a_type (ArchObj obj)) ptr s; valid_vspace_obj ao s\<rbrakk>
   \<Longrightarrow> valid_vspace_obj ao (s\<lparr>kheap := (kheap s)(ptr \<mapsto> ArchObj obj)\<rparr>)"
  apply (cases ao, simp_all)
      apply (fastforce simp: a_type_simps obj_at_def valid_pte_def)+
     apply (clarsimp)
     apply (drule_tac x = x in spec)
     apply (clarsimp simp: a_type_simps obj_at_def)
     apply (rename_tac "fun" x ko)
     apply (case_tac "fun x", simp_all add: data_at_def obj_at_def a_type_simps)[1]
     apply clarsimp+
    apply (drule_tac x = x in spec)
    apply (clarsimp simp: a_type_simps obj_at_def)
    apply (rename_tac "fun" x ko)
    apply (case_tac "fun x", simp_all add: data_at_def obj_at_def a_type_simps)[1]
     apply (clarsimp simp: a_type_simps)+
   apply (drule_tac x = x in spec)
   apply (clarsimp simp: a_type_simps obj_at_def)
   apply (rename_tac "fun" x ko)
   apply (case_tac "fun x", simp_all add: data_at_def obj_at_def a_type_simps)[1]
    apply (clarsimp simp: a_type_simps)+
  apply (drule_tac x = x in bspec, clarsimp)
  apply (clarsimp simp: a_type_simps obj_at_def)
  apply (rename_tac "fun" x ko)
  apply (case_tac "fun x", simp_all add: data_at_def obj_at_def a_type_simps)[1]
  apply (clarsimp simp: a_type_simps)+
  done

lemma set_object_valid_vspace_objs[wp]:
  "\<lbrace> \<lambda>s. valid_vspace_objs s

    \<comment> \<open>Lattice Preserving\<close>
    \<and> (\<forall>nref np nq stepref. ((nref, np) \<in> (vs_lookup1 s)\<^sup>* `` refs_diff vs_lookup1_on_heap_obj obj ptr s
        \<and>  (([], np), [stepref], nq) \<in> vs_lookup1 s)
        \<longrightarrow> vs_ref_lvl (kheap s np) < vs_ref_lvl (kheap s nq))
    \<and> (\<forall>nref np. (nref, np) \<in> refs_diff vs_lookup1_on_heap_obj obj ptr s
        \<longrightarrow> vs_ref_lvl (Some (ArchObj obj)) < vs_ref_lvl (kheap s np))

    \<comment> \<open>New reachable objs are valid\<close>
    \<and> (\<forall>rs. (rs \<rhd> ptr) s \<longrightarrow> valid_vspace_obj obj s)
    \<and> (\<forall>rs p pobj. (ko_at (ArchObj pobj) p s \<and> (rs, p)
        \<in> lookupable_refs (vs_lookup1 s) {ref. (ref \<rhd> ptr) s}
            (refs_diff vs_lookup1_on_heap_obj obj ptr s))
        \<longrightarrow> valid_vspace_obj pobj s)\<rbrace>
    set_object ptr (ArchObj obj)
  \<lbrace> \<lambda>_. valid_vspace_objs \<rbrace>"
  unfolding refs_diff_def
  apply (rule hoare_pre)
   apply (clarsimp simp: set_object_def)
   apply (wp get_object_wp)
  apply (subst valid_vspace_objs_def)
  apply (clarsimp simp: vs_lookup_def del:ImageE)
  apply (drule subsetD[rotated, OF _ wellformed_order_lookup.khupd_graph_subset])
    apply (erule vs_lookup1_wellformed_order)
   apply (rule_tac obj = "Some (ArchObj obj)" in wellformed_order_lookup.khupd_wellformed_order_lookup)
        apply (erule vs_lookup1_wellformed_order)
       apply fastforce
      apply fastforce
     apply (subst vs_ref_lvl_obj_same_type[OF sym])
      apply assumption
     apply (clarsimp simp: obj_at_def)
     apply (erule_tac s = "kheap s ptr" in subst)
     apply (erule wellformed_order_lookup.lookup1_trans_increase[OF vs_lookup1_wellformed_order])
      apply (clarsimp simp: Image_def)
      apply (erule bexI[rotated])
      apply simp
     apply simp
    apply (rule vs_lookup1_wellformed.wellformed_lookup_axioms
                  [where s = "s\<lparr>kheap := (kheap s)(ptr \<mapsto> ArchObj obj)\<rparr>" for s,simplified])
   apply (clarsimp simp: obj_at_def cong:vs_ref_lvl_obj_same_type)
  apply clarsimp
  apply (rule valid_vspace_obj_kheap_upd)
   apply (clarsimp simp: obj_at_def)
  apply (clarsimp dest!:a_type_is_aobj)
  apply (erule disjE)
   apply (drule_tac ao = "if p = ptr then aobj else ao" in valid_vspace_objsD[rotated -1])
     apply (simp add: vs_lookup_def)
    apply (simp add: obj_at_def split: if_split_asm)
   apply (clarsimp split: if_split_asm simp: obj_at_def)
   apply (drule(1) vs_lookupI)
   apply (simp add: vs_lookup_def)
  apply (drule_tac x = rs in spec, drule_tac x = p in spec, drule_tac x = "if p = ptr then aobj else ao" in spec)
  apply (clarsimp simp: obj_at_def split: if_split_asm)
  apply (clarsimp simp: lookupable_refs_def)
  done

(* FIXME: There is already a valid_vs_lookupD, but it does not contains all the information *)
lemma valid_vs_lookup_fullD:
  "\<lbrakk>(ref \<unrhd> p) s; valid_vs_lookup s\<rbrakk>
  \<Longrightarrow> ref \<noteq> [VSRef 0 (Some AASIDPool), VSRef 0 None]
    \<and> (\<exists>slot cap. caps_of_state s slot = Some cap \<and> p \<in> obj_refs cap \<and> vs_cap_ref cap = Some ref)"
  by (simp add: valid_vs_lookup_def)

lemma set_object_valid_vs_lookup[wp]:
  "\<lbrace> \<lambda>s. valid_vspace_objs s \<and> valid_vs_lookup s \<and> valid_asid_table (x64_asid_table (arch_state s)) s

    \<comment> \<open>Lattice Preserving\<close>
    \<and> (\<forall>nref np nq stepref. ((nref, np) \<in> (vs_lookup_pages1 s)\<^sup>* `` refs_diff vs_lookup_pages1_on_heap_obj obj ptr s
        \<and>  (([], np), [stepref], nq) \<in> vs_lookup_pages1 s)
        \<longrightarrow> vs_ref_lvl (kheap s np) < vs_ref_lvl (kheap s nq))
    \<and> (\<forall>nref np. (nref, np) \<in> refs_diff vs_lookup_pages1_on_heap_obj obj ptr s
        \<longrightarrow> vs_ref_lvl (Some (ArchObj obj)) < vs_ref_lvl (kheap s np))

    \<comment> \<open>New reachable objs are valid\<close>
    \<and> (\<forall>rs p pobj. ((rs, p)
        \<in> lookupable_refs (vs_lookup_pages1 s) {ref. (ref \<unrhd> ptr) s}
            (refs_diff vs_lookup_pages1_on_heap_obj obj ptr s))
        \<longrightarrow> rs \<noteq> [VSRef 0 (Some AASIDPool), VSRef 0 None] \<and>
           (\<exists>a b cap. caps_of_state s (a, b) = Some cap \<and> p \<in> obj_refs cap \<and> vs_cap_ref cap = Some rs))\<rbrace>
    set_object ptr (ArchObj obj)
  \<lbrace> \<lambda>_. valid_vs_lookup \<rbrace>"
  unfolding refs_diff_def
  apply (rule hoare_pre)
  apply (clarsimp simp: set_object_def)
  apply (wp get_object_wp)
  apply (subst valid_vs_lookup_def)
  apply (clarsimp simp: vs_lookup_pages_def del:ImageE)
  apply (drule subsetD[rotated, OF _ wellformed_order_lookup.khupd_graph_subset])
     apply (erule(1) vs_lookup_pages1_wellformed_order)
    apply (rule_tac obj = "Some (ArchObj obj)" in wellformed_order_lookup.khupd_wellformed_order_lookup)
        apply (erule(1) vs_lookup_pages1_wellformed_order)
       apply fastforce
      apply fastforce
     apply (subst vs_ref_lvl_obj_same_type[OF sym])
      apply assumption
     apply (clarsimp simp: obj_at_def)
     apply (erule_tac s = "kheap s ptr" in subst)
     apply (erule(1) wellformed_order_lookup.lookup1_trans_increase[OF vs_lookup_pages1_wellformed_order])
     apply (clarsimp simp: Image_def)
     apply (erule bexI[rotated])
      apply simp
     apply simp
    apply (rule vs_lookup_pages1_wellformed.wellformed_lookup_axioms
                  [where s = "s\<lparr>kheap := (kheap s)(ptr \<mapsto> ArchObj obj)\<rparr>" for s, simplified])
   apply (clarsimp simp: obj_at_def cong:vs_ref_lvl_obj_same_type)
  apply (clarsimp simp: fun_upd_def)
  apply (subst caps_of_state_after_update)
   apply (clarsimp simp: obj_at_def dest!:a_type_is_aobj)
  apply (erule disjE)
   apply (drule(1) valid_vs_lookup_fullD[unfolded vs_lookup_pages_def])
   apply simp
  apply (simp add: vs_lookup_pages_def)
  done

lemma set_object_valid_arch_caps[wp]:
  "\<lbrace> \<lambda>s. valid_vspace_objs s \<and> valid_arch_caps s

    \<and> valid_table_caps_aobj (caps_of_state s) (arch_state s) (ArchObj obj) ptr
    \<and> valid_asid_table (x64_asid_table (arch_state s)) s

    \<comment> \<open>Lattice Preserving\<close>
    \<and> (\<forall>nref np nq stepref. ((nref, np) \<in> (vs_lookup_pages1 s)\<^sup>* `` refs_diff vs_lookup_pages1_on_heap_obj obj ptr s
        \<and>  (([], np), [stepref], nq) \<in> vs_lookup_pages1 s)
        \<longrightarrow> vs_ref_lvl (kheap s np) < vs_ref_lvl (kheap s nq))
    \<and> (\<forall>nref np. (nref, np) \<in> refs_diff vs_lookup_pages1_on_heap_obj obj ptr s
        \<longrightarrow> vs_ref_lvl (Some (ArchObj obj)) < vs_ref_lvl (kheap s np))

    \<comment> \<open>New reachable objs are valid\<close>
    \<and> (\<forall>rs p pobj. ((rs, p)
        \<in> lookupable_refs (vs_lookup_pages1 s) {ref. (ref \<unrhd> ptr) s}
            (refs_diff vs_lookup_pages1_on_heap_obj obj ptr s))
        \<longrightarrow> rs \<noteq> [VSRef 0 (Some AASIDPool), VSRef 0 None] \<and>
           (\<exists>a b cap. caps_of_state s (a, b) = Some cap \<and> p \<in> obj_refs cap \<and> vs_cap_ref cap = Some rs))\<rbrace>
    set_object ptr (ArchObj obj)
  \<lbrace> \<lambda>_. valid_arch_caps \<rbrace>"
  by (clarsimp simp: valid_arch_caps_def | wp | fast)+

crunches set_object
  for valid_irq_states[wp]: "valid_irq_states"
  (wp: crunch_wps)

lemma set_object_state_hyp_refs[wp]:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>
    set_object ptr obj
   \<lbrace>\<lambda>_ s. P (state_hyp_refs_of s)\<rbrace>"
  apply (wpsimp simp: set_object_def wp: get_object_wp)
  including unfold_objects
  apply clarsimp
  apply (erule rsubst [where P=P])
  by (auto simp: state_hyp_refs_of_def split: option.splits)

lemma set_object_invs[wp]:
  "\<lbrace> \<lambda>s. invs s \<and> valid_table_caps_aobj (caps_of_state s) (arch_state s) (ArchObj obj) ptr
    \<and> (aa_type obj \<noteq> AASIDPool \<longrightarrow> ptr \<notin> global_refs s)
    \<and> obj_at (\<lambda>ko. case obj of PageMapL4 pm \<Rightarrow> \<exists>pm'. ko = ArchObj (PageMapL4 pm') \<and> (\<forall>x\<in>kernel_mapping_slots. pm x = pm' x) | _ \<Rightarrow> True) ptr s
    \<and> valid_kernel_mappings_if_pm (set (second_level_tables (arch_state s))) (ArchObj obj)
    \<and> valid_global_objs_upd ptr obj (arch_state s)
    \<and> ((\<exists>\<rhd> ptr) s \<longrightarrow> (valid_vspace_obj obj s)) \<and> (arch_valid_obj obj s)

    \<comment> \<open>Lattice Preserving\<close>
    \<and> (\<forall>nref np nq stepref. ((nref, np) \<in> (vs_lookup1 s)\<^sup>* `` refs_diff vs_lookup1_on_heap_obj obj ptr s
    \<and>  (([], np), [stepref], nq) \<in> vs_lookup1 s)
        \<longrightarrow> vs_ref_lvl (kheap s np) < vs_ref_lvl (kheap s nq))
    \<and> (\<forall>nref np. (nref, np) \<in> refs_diff vs_lookup1_on_heap_obj obj ptr s
        \<longrightarrow> vs_ref_lvl (Some (ArchObj obj)) < vs_ref_lvl (kheap s np))
    \<and> (\<forall>nref np nq stepref. ((nref, np) \<in> (vs_lookup_pages1 s)\<^sup>* `` refs_diff vs_lookup_pages1_on_heap_obj obj ptr s
        \<and>  (([], np), [stepref], nq) \<in> vs_lookup_pages1 s)
        \<longrightarrow> vs_ref_lvl (kheap s np) < vs_ref_lvl (kheap s nq))
    \<and> (\<forall>nref np. (nref, np) \<in> refs_diff vs_lookup_pages1_on_heap_obj obj ptr s
        \<longrightarrow> vs_ref_lvl (Some (ArchObj obj)) < vs_ref_lvl (kheap s np))

    \<comment> \<open>New reachable objs are arch valid\<close>

    \<and> (\<forall>rs p pobj. (ko_at (ArchObj pobj) p s \<and> (rs, p)
        \<in> lookupable_refs (vs_lookup1 s) {ref. (ref \<rhd> ptr) s}
            (refs_diff vs_lookup1_on_heap_obj obj ptr s))
        \<longrightarrow> valid_vspace_obj pobj s)
    \<comment> \<open>New reachable objs are vs_lookup valid\<close>
    \<and> (\<forall>rs p pobj. ((rs, p)
        \<in> lookupable_refs (vs_lookup_pages1 s) {ref. (ref \<unrhd> ptr) s}
            (refs_diff vs_lookup_pages1_on_heap_obj obj ptr s))
        \<longrightarrow> rs \<noteq> [VSRef 0 (Some AASIDPool), VSRef 0 None] \<and>
           (\<exists>a b cap. caps_of_state s (a, b) = Some cap \<and> p \<in> obj_refs cap \<and> vs_cap_ref cap = Some rs))\<rbrace>
    set_object ptr (ArchObj obj)
  \<lbrace> \<lambda>_. invs \<rbrace>"
  apply (clarsimp simp: invs_def valid_state_def valid_pspace_def valid_asid_map_def)
  apply (wp valid_irq_node_typ valid_irq_handlers_lift valid_ioports_lift
            set_aobj_valid_global_vspace_mappings set_object_valid_objs)
  apply (clarsimp simp: valid_arch_state_def valid_obj_def)
  done

lemma valid_global_refsD2:
  "\<lbrakk> caps_of_state s ptr = Some cap; valid_global_refs s \<rbrakk>
      \<Longrightarrow> global_refs s \<inter> cap_range cap = {}"
  by (cases ptr,
      simp add: valid_global_refs_def valid_refs_def
                cte_wp_at_caps_of_state)

lemma valid_global_refsD:
  "\<lbrakk> valid_global_refs s; cte_wp_at ((=) cap) ptr s;
         r \<in> global_refs s \<rbrakk>
        \<Longrightarrow> r \<notin> cap_range cap"
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (drule(1) valid_global_refsD2)
  apply fastforce
  done

lemma in_device_frame_same_type_upd:
  "\<lbrakk>typ_at type p s; type = a_type obj ; in_device_frame q s\<rbrakk>
    \<Longrightarrow> in_device_frame q (s\<lparr>kheap := (kheap s)(p \<mapsto> obj)\<rparr>)"
  apply (clarsimp simp: in_device_frame_def obj_at_def)
  apply (rule_tac x=sz in exI)
  apply (auto simp: a_type_simps)
  done

lemma store_word_offs_in_device_frame[wp]:
  "\<lbrace>\<lambda>s. in_device_frame p s\<rbrace> store_word_offs a x w \<lbrace>\<lambda>_ s. in_device_frame p s\<rbrace>"
  unfolding in_device_frame_def
  by (wp hoare_vcg_ex_lift)

lemma as_user_in_device_frame[wp]:
  "\<lbrace>\<lambda>s. in_device_frame p s\<rbrace> as_user t m \<lbrace>\<lambda>_ s. in_device_frame p s\<rbrace>"
  unfolding in_device_frame_def
  by (wp hoare_vcg_ex_lift)

crunches load_word_offs
  for obj_at[wp]: "\<lambda>s. P (obj_at Q p s)"

lemma load_word_offs_in_user_frame[wp]:
  "\<lbrace>\<lambda>s. in_user_frame p s\<rbrace> load_word_offs a x \<lbrace>\<lambda>_ s. in_user_frame p s\<rbrace>"
  unfolding in_user_frame_def
  by (wp hoare_vcg_ex_lift)

(* FIXME: move to Invariants_A *)
lemma invs_valid_asid_table [elim!]:
  "invs s \<Longrightarrow> valid_asid_table (x64_asid_table (arch_state s)) s"
  by (simp add: invs_def valid_state_def valid_arch_state_def)


(* FIXME: move to Invariants_A *)
lemma valid_asid_table_ran:
  "valid_asid_table asid_tbl s \<Longrightarrow> \<forall>p\<in>ran asid_tbl. asid_pool_at p s"
  by (simp add: invs_def valid_state_def valid_arch_state_def
                valid_asid_table_def)


lemma vs_lookup_pages_pt_eq:
  "\<lbrakk>valid_vspace_objs s;
    \<forall>p\<in>ran (x64_asid_table (arch_state s)). asid_pool_at p s;
    page_table_at p s\<rbrakk>
   \<Longrightarrow> (ref \<unrhd> p) s = (ref \<rhd> p) s"
  apply (rule iffI[rotated])
   apply (erule vs_lookup_pages_vs_lookupI)
  apply (erule (2) vs_lookup_pagesE_alt)
  by (auto simp: obj_at_def pml4e_ref_pages_def pdpte_ref_pages_def pde_ref_pages_def
                 pte_ref_pages_def data_at_def
          split: pml4e.splits pdpte.splits pde.splits pte.splits
           elim: vs_lookup_pdI)

lemma valid_vspace_obj_same_type:
  "\<lbrakk>valid_vspace_obj ao s;  kheap s p = Some ko; a_type ko' = a_type ko\<rbrakk>
  \<Longrightarrow> valid_vspace_obj ao (s\<lparr>kheap := (kheap s)(p \<mapsto> ko')\<rparr>)"
    apply (rule hoare_to_pure_kheap_upd[OF valid_vspace_obj_typ])
    by (auto simp: obj_at_def)

lemmas invs_ran_asid_table = invs_valid_asid_table[THEN valid_asid_table_ran]

(* FIXME: Move to Invariants_A *)
lemma vs_lookup_pages_stateI:
  assumes 1: "(ref \<unrhd> p) s"
  assumes ko: "\<And>ko p. ko_at ko p s \<Longrightarrow> obj_at (\<lambda>ko'. vs_refs_pages ko \<subseteq> vs_refs_pages ko') p s'"
  assumes table: "graph_of (x64_asid_table (arch_state s)) \<subseteq> graph_of (x64_asid_table (arch_state s'))"
  shows "(ref \<unrhd> p) s'"
  using 1 vs_lookup_pages_sub [OF ko table] by blast

lemma valid_pte_typ_at:
  "(\<And>T p. typ_at (AArch T) p s = typ_at (AArch T) p s') \<Longrightarrow>
   valid_pte pte s = valid_pte pte s'"
  by (case_tac pte, auto simp add: data_at_def)


lemma valid_pde_typ_at:
  "(\<And>T p. typ_at (AArch T) p s = typ_at (AArch T) p s') \<Longrightarrow>
   valid_pde pde s = valid_pde pde s'"
  by (case_tac pde, auto simp add: data_at_def)

lemma valid_pdpte_typ_at:
  "(\<And>T p. typ_at (AArch T) p s = typ_at (AArch T) p s') \<Longrightarrow>
   valid_pdpte pdpte s = valid_pdpte pdpte s'"
  by (case_tac pdpte, auto simp add: data_at_def)

lemma valid_pml4e_typ_at:
  "(\<And>T p. typ_at (AArch T) p s = typ_at (AArch T) p s') \<Longrightarrow>
   valid_pml4e pml4e s = valid_pml4e pml4e s'"
  by (case_tac pml4e, simp+)

lemmas set_aobj_cte_wp_at1[wp]
    = hoare_cte_wp_caps_of_state_lift [OF set_aobject_caps_of_state]
lemma set_aobj_mdb_cte_at[wp]:
  "\<lbrace>\<lambda>s. mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s)\<rbrace>
   set_object ptr (ArchObj pool)
   \<lbrace>\<lambda>r s. mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s)\<rbrace>"
  apply (rule hoare_pre)
  apply wps
  apply (clarsimp simp: mdb_cte_at_def cte_wp_at_caps_of_state)
  apply wp
  apply (clarsimp simp: mdb_cte_at_def cte_wp_at_caps_of_state)
done

lemma valid_slots_typ_at:
  assumes x: "\<And>T p. \<lbrace>typ_at (AArch T) p\<rbrace> f \<lbrace>\<lambda>rv. typ_at (AArch T) p\<rbrace>"
  assumes y: "\<And>p. \<lbrace>\<exists>\<rhd> p\<rbrace> f \<lbrace>\<lambda>rv. \<exists>\<rhd> p\<rbrace>"
  shows "\<lbrace>valid_slots m\<rbrace> f \<lbrace>\<lambda>rv. valid_slots m\<rbrace>"
  unfolding valid_slots_def
  apply (cases m; clarsimp)
  apply (case_tac a; clarsimp)
  apply (wp x y hoare_vcg_const_Ball_lift valid_pte_lift valid_pde_lift valid_pdpte_lift valid_pml4e_lift
             pte_at_atyp pde_at_atyp pdpte_at_atyp pml4e_at_atyp)+
  done


lemma ucast_ucast_id:
  "(len_of TYPE('a)) < (len_of TYPE('b)) \<Longrightarrow> ucast ((ucast (x::('a::len) word))::('b::len) word) = x"
  by (auto intro: ucast_up_ucast_id simp: is_up_def source_size_def target_size_def word_size)


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
  apply (clarsimp simp: word_size nth_shiftr nth_shiftl get_pml4_index_def bit_simps)
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

lemma mask_out_first_mask_some:
  "\<lbrakk> x && ~~ mask n = y; n \<le> m \<rbrakk> \<Longrightarrow> x && ~~ mask m = y && ~~ mask m"
  apply (rule word_eqI[rule_format], drule_tac x=na in word_eqD)
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

lemma valid_vspace_objs_arch_update:
  "x64_asid_table (f (arch_state s)) = x64_asid_table (arch_state s) \<Longrightarrow>
  valid_vspace_objs (arch_state_update f s) = valid_vspace_objs s"
  apply (rule iffI)
   apply (erule valid_vspace_objs_stateI)
     apply (clarsimp simp: obj_at_def)
    apply simp
   apply simp
  apply (erule valid_vspace_objs_stateI)
    apply (clarsimp simp: obj_at_def)
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

(* FIXME: valid_globals_refsD is used here, so it might be still useful *)

lemma eq_ucast_word9[simp]:
  "((ucast (x :: 9 word) :: word64) = ucast y) = (x = y)"
  apply safe
  apply (drule_tac f="ucast :: (word64 \<Rightarrow> 9 word)" in arg_cong)
  apply (simp add: ucast_up_ucast_id is_up_def
                   source_size_def target_size_def word_size)
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
    (\<forall>ao. (ko = ArchObj ao) \<longrightarrow> valid_vspace_obj ao s);
    (\<forall>ao'. (ko' = ArchObj ao') \<longrightarrow> valid_vspace_obj ao' s)\<rbrakk>
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
    apply (clarsimp simp: data_at_def obj_at_def a_type_def)
   done
   subgoal for pdpt pdpt' a b
   using
     imageI[where
       A="{(x, y). pdpte_ref (pdpt' x) = Some y}"
       and f="(\<lambda>(r, y). (VSRef (ucast r) (Some APDPointerTable), y))" and x="(a,b)"]
    apply (clarsimp simp: pdpte_ref_def pdpte_ref_pages_def split: pdpte.splits)
    apply (drule_tac x=a in spec; simp)
    apply (drule_tac x=a in spec; simp)
    apply (clarsimp simp: data_at_def obj_at_def a_type_def)
   done
   subgoal for pml4 pml4' a b
   using
     imageI[where
       A="{(x, y). (if x \<in> kernel_mapping_slots then None else pml4e_ref (pml4' x)) = Some y}"
       and f="(\<lambda>(r, y). (VSRef (ucast r) (Some APageMapL4), y))" and x="(a,b)"]
    apply (clarsimp simp: pml4e_ref_def pml4e_ref_pages_def split: pml4e.splits)
    done
   done

lemma refs_diff_empty_simps_vslookup1[simp]:
  "kheap s p = Some (ArchObj (PageMapL4 pm)) \<Longrightarrow>
    (refs_diff vs_lookup1_on_heap_obj (PageMapL4 (pm(a := InvalidPML4E))) p s) = {}"
  apply (clarsimp simp: image_def graph_of_def pml4e_ref_def refs_diff_def lookup_refs_def vs_lookup1_on_heap_obj_def vs_refs_def
                 split: if_splits pml4e.splits)
  apply auto
  done

lemma refs_diff_vs_lookup_pages1_slot_upd_pd_simp[simp]:
  "kheap s p = Some (ArchObj (PageDirectory pd)) \<Longrightarrow> refs_diff vs_lookup_pages1_on_heap_obj (PageDirectory (pd(a := pde))) p s
  = (case pde_ref_pages pde of None \<Rightarrow> {} | Some x \<Rightarrow> if pde_ref_pages pde = pde_ref_pages (pd a) then {} else {([VSRef (ucast a) (Some APageDirectory)], x)})"
  apply (clarsimp simp: refs_diff_def vs_lookup_pages1_on_heap_obj_def lookup_refs_def vs_refs_pages_def)
  apply (auto simp: graph_of_def image_def split: if_splits option.splits)
  done

lemma refs_diff_vs_lookup_pages1_slot_upd_pt_simp[simp]:
  "kheap s p = Some (ArchObj (PageTable pt)) \<Longrightarrow> refs_diff vs_lookup_pages1_on_heap_obj (PageTable (pt(a := pte))) p s
  = (case pte_ref_pages pte of None \<Rightarrow> {} | Some x \<Rightarrow> if pte_ref_pages pte = pte_ref_pages (pt a) then {} else {([VSRef (ucast a) (Some APageTable)], x)})"
  apply (clarsimp simp: refs_diff_def vs_lookup_pages1_on_heap_obj_def lookup_refs_def vs_refs_pages_def)
  apply (auto simp: graph_of_def image_def split: if_splits option.splits)
  done

lemma refs_diff_vs_lookup_pages1_slot_upd_pdpt_simp[simp]:
  "kheap s p = Some (ArchObj (PDPointerTable pdpt)) \<Longrightarrow> refs_diff vs_lookup_pages1_on_heap_obj (PDPointerTable (pdpt(a := pdpte))) p s
  = (case pdpte_ref_pages pdpte of None \<Rightarrow> {} | Some x \<Rightarrow> if pdpte_ref_pages pdpte = pdpte_ref_pages (pdpt a) then {} else {([VSRef (ucast a) (Some APDPointerTable)], x)})"
  apply (clarsimp simp: refs_diff_def vs_lookup_pages1_on_heap_obj_def lookup_refs_def vs_refs_pages_def)
  apply (auto simp: graph_of_def image_def split: if_splits option.splits)
  done

lemma refs_diff_vs_lookup_pages1_slot_upd_pml4_simp[simp]:
  "kheap s p = Some (ArchObj (PageMapL4 pml4)) \<Longrightarrow> refs_diff vs_lookup_pages1_on_heap_obj (PageMapL4 (pml4(a := pml4e))) p s
  = (case pml4e_ref_pages pml4e of None \<Rightarrow> {} | Some x \<Rightarrow> if pml4e_ref_pages pml4e = pml4e_ref_pages (pml4 a) \<or> a \<in> kernel_mapping_slots then {} else {([VSRef (ucast a) (Some APageMapL4)], x)})"
  apply (clarsimp simp: refs_diff_def vs_lookup_pages1_on_heap_obj_def lookup_refs_def vs_refs_pages_def)
  apply (auto simp: graph_of_def image_def split: if_splits option.splits)
  done

lemma refs_diff_vs_lookup1_slot_upd_pd_simp[simp]:
  "kheap s p = Some (ArchObj (PageDirectory pd)) \<Longrightarrow> refs_diff vs_lookup1_on_heap_obj (PageDirectory (pd(a := pde))) p s
  = (case pde_ref pde of None \<Rightarrow> {} | Some x \<Rightarrow> if pde_ref pde = pde_ref (pd a) then {} else {([VSRef (ucast a) (Some APageDirectory)], x)})"
  apply (clarsimp simp: refs_diff_def vs_lookup1_on_heap_obj_def lookup_refs_def vs_refs_def)
  apply (auto simp: graph_of_def image_def split: if_splits option.splits)
  done

lemma refs_diff_vs_lookup1_slot_upd_pt_simp[simp]:
  "kheap s p = Some (ArchObj (PageTable pt)) \<Longrightarrow> refs_diff vs_lookup1_on_heap_obj (PageTable (pt(a := pte))) p s
  = {}"
  apply (clarsimp simp: refs_diff_def vs_lookup1_on_heap_obj_def lookup_refs_def vs_refs_def)
  done

lemma refs_diff_vs_lookup1_slot_upd_pdpt_simp[simp]:
  "kheap s p = Some (ArchObj (PDPointerTable pdpt)) \<Longrightarrow> refs_diff vs_lookup1_on_heap_obj (PDPointerTable (pdpt(a := pdpte))) p s
  = (case pdpte_ref pdpte of None \<Rightarrow> {} | Some x \<Rightarrow> if pdpte_ref pdpte = pdpte_ref (pdpt a) then {} else {([VSRef (ucast a) (Some APDPointerTable)], x)})"
  apply (clarsimp simp: refs_diff_def vs_lookup1_on_heap_obj_def lookup_refs_def vs_refs_def)
  apply (auto simp: graph_of_def image_def split: if_splits option.splits)
  done

lemma refs_diff_vs_lookup1_slot_upd_pml4_simp[simp]:
  "kheap s p = Some (ArchObj (PageMapL4 pml4)) \<Longrightarrow> refs_diff vs_lookup1_on_heap_obj (PageMapL4 (pml4(a := pml4e))) p s
  = (case pml4e_ref pml4e of None \<Rightarrow> {} | Some x \<Rightarrow> if pml4e_ref pml4e = pml4e_ref (pml4 a) \<or> a \<in> kernel_mapping_slots then {} else {([VSRef (ucast a) (Some APageMapL4)], x)})"
  apply (clarsimp simp: refs_diff_def vs_lookup1_on_heap_obj_def lookup_refs_def vs_refs_def)
  apply (auto simp: graph_of_def image_def split: if_splits option.splits)
  done

lemma refs_diff_empty_simps_vslookup_pages1[simp]:
  "\<lbrakk>kheap s p = Some (ArchObj (PageDirectory pd));pde_ref_pages pde = None\<rbrakk> \<Longrightarrow>
    (refs_diff vs_lookup_pages1_on_heap_obj (PageDirectory (pd(a := pde))) p s) = {}"
  "\<lbrakk>kheap s p = Some (ArchObj (PageTable pt));pte_ref_pages pte = None\<rbrakk> \<Longrightarrow>
    (refs_diff vs_lookup_pages1_on_heap_obj (PageTable (pt(a := pte))) p s) = {}"
  apply (clarsimp simp: image_def graph_of_def pml4e_ref_pages_def pde_ref_pages_def pde_ref_def
                        refs_diff_def lookup_refs_def vs_lookup_pages1_on_heap_obj_def vs_refs_pages_def
                 split: if_splits pde.splits)
  by auto

lemma empty_table_empty_vs_refs_pages[simp]:
  "empty_table (set (second_level_tables (arch_state s))) ko \<Longrightarrow> vs_refs_pages ko = {}"
  apply (clarsimp simp: empty_table_def split: kernel_object.splits arch_kernel_obj.splits)
     apply (clarsimp simp: vs_refs_pages_def graph_of_def pte_ref_pages_def pde_ref_pages_def
                           pdpte_ref_pages_def pml4e_ref_pages_def)+
  done

lemma empty_table_empty_vs_refs[simp]:
  "empty_table (set (second_level_tables (arch_state s))) ko \<Longrightarrow> vs_refs ko = {}"
  using local.vs_refs_pages_subset
  by (fastforce simp: local.vs_refs_pages_subset)

lemma empty_vs_refs_lookup_refs_refl:
  "\<lbrakk>vs_refs ko = {}; kheap s b = Some ko; ((a, b), tref, p) \<in> (vs_lookup1 s)^*\<rbrakk>
  \<Longrightarrow> b = p \<and> a = tref"
  apply (erule converse_rtranclE)
   apply clarsimp
  apply (clarsimp simp: obj_at_def dest!: vs_lookup1D)
  done

lemmas empty_table_lookup_refs_refl = empty_vs_refs_lookup_refs_refl[OF empty_table_empty_vs_refs]

lemma empty_vs_refs_pages_lookup_refs_pages_refl:
  "\<lbrakk>vs_refs_pages ko = {}; kheap s b = Some ko; ((a, b), tref, p) \<in> (vs_lookup_pages1 s)^*\<rbrakk>
  \<Longrightarrow> b = p \<and> a = tref"
  apply (erule converse_rtranclE)
   apply clarsimp
  apply (clarsimp simp: obj_at_def dest!: vs_lookup_pages1D)
  done

lemmas empty_table_lookup_refs_pages_refl = empty_vs_refs_pages_lookup_refs_pages_refl[OF empty_table_empty_vs_refs_pages]

lemma empty_table_cap_asid_None:
  "\<lbrakk>cte_wp_at (\<lambda>cap. (is_pd_cap cap \<or> is_pt_cap cap \<or> is_pdpt_cap cap \<or> is_pml4_cap cap)
              \<and> cap_asid cap = None \<and> ptr \<in> obj_refs cap) slot s; kheap s ptr = Some ko; invs s\<rbrakk>
  \<Longrightarrow> empty_table (set (second_level_tables (arch_state s))) ko"
  apply (clarsimp simp: valid_table_caps_def cte_wp_at_caps_of_state simp del: split_paired_All dest!: invs_valid_table_caps)
  apply (drule_tac x = ptr in spec)
  apply (drule_tac x = slot in spec)
  apply (clarsimp simp: obj_at_def)
  done

lemma empty_refs_pages_cap_lookup_refs_pages_empty:
  "\<lbrakk>vs_refs_pages ko = {}; ((a,b), tref, p) \<in> (vs_lookup_pages1 s)^+; kheap s b = Some ko\<rbrakk>
  \<Longrightarrow> False"
  apply (erule converse_tranclE)
   apply (clarsimp simp: vs_lookup_pages1_def obj_at_def)+
  done

lemma unmapped_cap_lookup_refs_pages_empty:
  "\<lbrakk>empty_table (set (second_level_tables (arch_state s))) ko; ((a,b), tref, p) \<in> (vs_lookup_pages1 s)^+; kheap s b = Some ko\<rbrakk>
  \<Longrightarrow> False"
  apply (erule(1) empty_refs_pages_cap_lookup_refs_pages_empty[rotated])
  apply simp
  done

lemma empty_refs_cap_lookup_refs_empty:
  "\<lbrakk>vs_refs ko = {}; ((a,b), tref, p) \<in> (vs_lookup1 s)^+; kheap s b = Some ko\<rbrakk>
  \<Longrightarrow> False"
  apply (erule converse_tranclE)
   apply (clarsimp simp: vs_lookup1_def obj_at_def)+
  done

lemma unmapped_cap_lookup_refs_empty:
  "\<lbrakk>empty_table (set (second_level_tables (arch_state s))) ko; ((a,b), tref, p) \<in> (vs_lookup1 s)^+; kheap s b = Some ko\<rbrakk>
  \<Longrightarrow> False"
  apply (erule(1) empty_refs_cap_lookup_refs_empty[rotated])
  apply simp
  done

lemma lookupable_refs_empty[simp]:
  "lookupable_refs a b {} = {}"
  by (simp add: lookupable_refs_def)

lemma invs_valid_kernel_mappings:
  "invs s \<Longrightarrow> valid_kernel_mappings s"
  by (simp add: invs_def valid_state_def)

lemma valid_kernel_mappings_if_pm_pml4e:
  "\<lbrakk>valid_kernel_mappings s; kheap s p = Some (ArchObj (PageMapL4 pm));
    \<forall>r. pml4e_ref pml4e = Some r \<longrightarrow> (r \<in> set (second_level_tables (arch_state s))) = (slot \<in> kernel_mapping_slots)\<rbrakk>
    \<Longrightarrow> valid_kernel_mappings_if_pm (set (second_level_tables (arch_state s)))
                 (ArchObj (PageMapL4 (pm(slot := pml4e))))"
  by (fastforce simp: pml4e_ref_def valid_kernel_mappings_if_pm_def valid_kernel_mappings_def
                      second_level_tables_def
               dest!: bspec split: option.split_asm pml4e.split_asm)

lemma valid_kernel_mappings_if_pm_pte:
  "\<lbrakk>valid_kernel_mappings s; kheap s p = Some (ArchObj (PageTable pt))\<rbrakk>
    \<Longrightarrow> valid_kernel_mappings_if_pm (set (second_level_tables (arch_state s)))
                 (ArchObj (PageTable (pt(slot := pte))))"
  by (fastforce simp: valid_kernel_mappings_if_pm_def valid_kernel_mappings_def pml4e_ref_def
                  dest!: bspec split: option.split_asm pml4e.split_asm)

lemma valid_kernel_mappings_if_pm_pde:
  "\<lbrakk>valid_kernel_mappings s; kheap s p = Some (ArchObj (PageDirectory pd))\<rbrakk>
    \<Longrightarrow> valid_kernel_mappings_if_pm (set (second_level_tables (arch_state s)))
                 (ArchObj (PageDirectory (pd(slot := pde))))"
  by (fastforce simp: valid_kernel_mappings_if_pm_def valid_kernel_mappings_def pml4e_ref_def
                  dest!: bspec split: option.split_asm pml4e.split_asm)

lemma valid_kernel_mappings_if_pm_pdpte:
  "\<lbrakk>valid_kernel_mappings s; kheap s p = Some (ArchObj (PDPointerTable pdpt))\<rbrakk>
    \<Longrightarrow> valid_kernel_mappings_if_pm (set (second_level_tables (arch_state s)))
                 (ArchObj (PDPointerTable (pdpt(slot := pdpte))))"
  by (fastforce simp: valid_kernel_mappings_if_pm_def valid_kernel_mappings_def pml4e_ref_def
                  dest!: bspec split: option.split_asm pml4e.split_asm)

lemma valid_global_objs_upd_invalid_pde:
  "\<lbrakk>valid_global_objs s; kheap s p = Some (ArchObj (PageDirectory pd)); p \<notin> global_refs s\<rbrakk>
    \<Longrightarrow> valid_global_objs_upd p (PageDirectory (pm(slot := pde))) (arch_state s)"
  by (clarsimp simp: valid_global_objs_def valid_global_objs_upd_def obj_at_def valid_ao_at_def
                     empty_table_def global_refs_def)

lemma valid_global_objs_upd_invalid_pte:
  "\<lbrakk>valid_global_objs s; kheap s p = Some (ArchObj (PageTable pt));p \<notin> global_refs s\<rbrakk>
    \<Longrightarrow> valid_global_objs_upd p (PageTable (pt(slot := pte))) (arch_state s)"
  by (clarsimp simp: valid_global_objs_def valid_global_objs_upd_def obj_at_def valid_ao_at_def
                     empty_table_def global_refs_def)

lemma valid_global_objs_upd_invalid_pdpte:
  "\<lbrakk>valid_global_objs s; kheap s p = Some (ArchObj (PDPointerTable pdpt)); p \<notin> global_refs s\<rbrakk>
    \<Longrightarrow> valid_global_objs_upd p (PDPointerTable (pdpt(slot := pdpte))) (arch_state s)"
  by (clarsimp simp: valid_global_objs_def valid_global_objs_upd_def obj_at_def valid_ao_at_def
                     empty_table_def global_refs_def)

lemma valid_global_objs_upd_invalid_pml4e:
  "\<lbrakk>valid_global_objs s; kheap s p = Some (ArchObj (PageMapL4 pm)); pml4e_ref_pages pml4e = None \<or>  p\<notin> global_refs s\<rbrakk>
    \<Longrightarrow> valid_global_objs_upd p (PageMapL4 (pm(slot := pml4e))) (arch_state s)"
  by (clarsimp simp: valid_global_objs_def valid_global_objs_upd_def obj_at_def valid_ao_at_def
                    empty_table_def global_refs_def pml4e_ref_pages_def pml4e_ref_def
             split: pml4e.split_asm)

definition
"valid_table_caps_entry cs as obj r \<equiv> \<forall>p cap. cs p = Some cap \<longrightarrow>
              (is_pd_cap cap \<or> is_pt_cap cap \<or> is_pdpt_cap cap \<or> is_pml4_cap cap) \<longrightarrow>
              cap_asid cap = None \<longrightarrow> r \<in> obj_refs cap \<longrightarrow> empty_table (set (x64_global_pdpts as)) obj"

lemma valid_cap_typ_at:
  "\<lbrakk>is_pd_cap cap; p \<in> obj_refs cap;  s \<turnstile> cap\<rbrakk> \<Longrightarrow> typ_at (AArch APageDirectory) p s"
  "\<lbrakk>is_pt_cap cap; p \<in> obj_refs cap;  s \<turnstile> cap\<rbrakk> \<Longrightarrow> typ_at (AArch APageTable) p s"
  "\<lbrakk>is_pdpt_cap cap; p \<in> obj_refs cap;  s \<turnstile> cap\<rbrakk> \<Longrightarrow> typ_at (AArch APDPointerTable) p s"
  "\<lbrakk>is_pml4_cap cap; p \<in> obj_refs cap;  s \<turnstile> cap\<rbrakk> \<Longrightarrow> typ_at (AArch APageMapL4) p s"
  "\<lbrakk>is_asid_pool_cap cap; p \<in> obj_refs cap;  s \<turnstile> cap\<rbrakk> \<Longrightarrow> typ_at (AArch AASIDPool) p s"
  by (auto simp: is_cap_simps valid_cap_def)

lemma valid_arch_cap_typ_at [elim]:
  "\<And>s p r t sz asid. s \<turnstile> ArchObjectCap (PageCap True p r t sz asid) \<Longrightarrow> typ_at (AArch (ADeviceData sz)) p s"
  "\<And>s p r t sz asid. s \<turnstile> ArchObjectCap (PageCap False p r t sz asid) \<Longrightarrow> typ_at (AArch (AUserData sz)) p s"
  "\<And>s p asid. s \<turnstile> ArchObjectCap (PageTableCap p asid) \<Longrightarrow> typ_at (AArch APageTable) p s"
  "\<And>s p asid. s \<turnstile> ArchObjectCap (PageDirectoryCap p asid) \<Longrightarrow> typ_at (AArch APageDirectory) p s"
  "\<And>s p asid. s \<turnstile> ArchObjectCap (PDPointerTableCap p asid) \<Longrightarrow> typ_at (AArch APDPointerTable) p s"
  "\<And>s p asid. s \<turnstile> ArchObjectCap (PML4Cap p asid) \<Longrightarrow> typ_at (AArch APageMapL4) p s"
  "\<And>s p asid. s \<turnstile> ArchObjectCap (ASIDPoolCap p asid) \<Longrightarrow> typ_at (AArch AASIDPool) p s"
  by (auto simp: valid_cap_def)

lemma is_cap_disjoint[simp]:
  "\<lbrakk>is_pd_cap cap; is_pdpt_cap cap\<rbrakk>\<Longrightarrow> False"
  "\<lbrakk>is_pd_cap cap; is_pml4_cap cap\<rbrakk>\<Longrightarrow> False"
  "\<lbrakk>is_pml4_cap cap; is_pd_cap cap\<rbrakk>\<Longrightarrow> False"
  "\<lbrakk>is_pd_cap cap; is_pt_cap cap\<rbrakk>\<Longrightarrow> False"
  "\<lbrakk>is_pt_cap cap; is_pdpt_cap cap\<rbrakk>\<Longrightarrow> False"
  "\<lbrakk>is_pt_cap cap; is_pml4_cap cap\<rbrakk>\<Longrightarrow> False"
  "\<lbrakk>is_pdpt_cap cap; is_pml4_cap cap\<rbrakk>\<Longrightarrow> False"
  by (auto simp: is_cap_simps)

lemma ref_pages_NoneD[simp]:
  "pde_ref_pages pde = None \<Longrightarrow> pde = InvalidPDE"
  "pte_ref_pages pte = None \<Longrightarrow> pte = InvalidPTE"
  "pdpte_ref_pages pdpte = None \<Longrightarrow> pdpte = InvalidPDPTE"
  "pml4e_ref_pages pml4e = None \<Longrightarrow> pml4e = InvalidPML4E"
  apply (auto simp: pte_ref_pages_def pde_ref_pages_def pdpte_ref_pages_def pml4e_ref_pages_def
             split: pde.split_asm pte.split_asm pdpte.split_asm pml4e.split_asm)
  done

lemma ref_pages_Some:
  "pde_ref pde = Some x \<Longrightarrow> pde_ref_pages pde = Some x"
  "pdpte_ref pdpte = Some x \<Longrightarrow> pdpte_ref_pages pdpte = Some x"
  "pml4e_ref pml4e = Some x \<Longrightarrow> pml4e_ref_pages pml4e = Some x"
  by (auto simp: pdpte_ref_pages_def pdpte_ref_def pde_ref_pages_def pde_ref_def pml4e_ref_def pml4e_ref_pages_def
          split: pde.splits pdpte.splits)

lemma ref_pages_ref_Some:
  "\<lbrakk>pde_ref pde = Some a; pde_ref_pages pde = Some b\<rbrakk> \<Longrightarrow> a = b"
  by (simp add: pde_ref_pages_def pde_ref_def split: pde.splits)

lemma valid_table_caps_aobj_upd_invalid_pde:
  "\<lbrakk>valid_table_caps s; kheap s p = Some (ArchObj (PageDirectory pd));
    pde_ref_pages pde = None \<or> (\<forall>slot cap. caps_of_state s slot = Some cap \<longrightarrow> is_pd_cap cap \<longrightarrow> p \<in> obj_refs cap \<longrightarrow>
         cap_asid cap \<noteq> None); invs s\<rbrakk>
    \<Longrightarrow> valid_table_caps_aobj (caps_of_state s) (arch_state s) (ArchObj (PageDirectory (pd(slot := pde)))) p"
  apply (clarsimp simp: valid_table_caps_def valid_table_caps_aobj_def all_comm
                        empty_table_def pde_ref_def simp del: split_paired_All)
  apply (drule_tac x = cap in spec)
  apply (erule impE)
   apply fastforce
  apply (drule_tac x = p in spec)
  apply (intro impI allI conjI)
         apply (clarsimp simp: obj_at_def dest!: ref_pages_NoneD)
         apply (fastforce simp: ref_pages_NoneD)
    apply (clarsimp simp: obj_at_def dest!: invs_valid_objs caps_of_state_valid | drule(2) valid_cap_typ_at)+
  done

lemma valid_table_caps_aobj_upd_invalid_pte:
  "\<lbrakk>valid_table_caps s; kheap s p = Some (ArchObj (PageTable pt));
    pte_ref_pages pte = None \<or> (\<forall>slot cap. caps_of_state s slot = Some cap \<longrightarrow> is_pt_cap cap \<longrightarrow> p \<in> obj_refs cap \<longrightarrow>
         cap_asid cap \<noteq> None); invs s\<rbrakk>
    \<Longrightarrow> valid_table_caps_aobj (caps_of_state s) (arch_state s) (ArchObj (PageTable (pt(slot := pte)))) p"
  apply (clarsimp simp: valid_table_caps_def valid_table_caps_aobj_def all_comm
                        empty_table_def pde_ref_def simp del: split_paired_All)
  apply (drule_tac x = cap in spec)
  apply (erule impE)
   apply fastforce
  apply (drule_tac x = p in spec)
  apply (intro impI allI conjI)
         apply ((clarsimp simp: obj_at_def dest!: invs_valid_objs caps_of_state_valid | drule(2) valid_cap_typ_at)+)[2]
       apply (fastforce simp: obj_at_def)
      apply (clarsimp simp: obj_at_def dest!: invs_valid_objs caps_of_state_valid | drule(2) valid_cap_typ_at)+
  done

lemma valid_table_caps_aobj_upd_invalid_pdpte:
  "\<lbrakk>valid_table_caps s; kheap s p = Some (ArchObj (PDPointerTable pdpt));
    pdpte_ref_pages pdpte = None \<or> (\<forall>slot cap. caps_of_state s slot = Some cap \<longrightarrow> is_pdpt_cap cap \<longrightarrow> p \<in> obj_refs cap \<longrightarrow>
         cap_asid cap \<noteq> None); invs s\<rbrakk>
    \<Longrightarrow> valid_table_caps_aobj (caps_of_state s) (arch_state s) (ArchObj (PDPointerTable (pdpt(slot := pdpte)))) p"
  apply (clarsimp simp: valid_table_caps_def valid_table_caps_aobj_def all_comm
                        empty_table_def pdpte_ref_def simp del: split_paired_All)
  apply (drule_tac x = cap in spec)
  apply (erule impE)
   apply fastforce
  apply (drule_tac x = p in spec)
  apply (intro impI allI conjI)
      apply ((clarsimp simp: obj_at_def dest!: invs_valid_objs caps_of_state_valid | drule(2) valid_cap_typ_at)+)[4]
         apply (fastforce simp: obj_at_def)
    apply (clarsimp simp: obj_at_def dest!: invs_valid_objs caps_of_state_valid | drule(2) valid_cap_typ_at)+
  done

lemma valid_table_caps_aobj_upd_invalid_pml4e:
  "\<lbrakk>valid_table_caps s; kheap s p = Some (ArchObj (PageMapL4 pml4));
    pml4e_ref_pages pml4e = None \<or> (\<forall>slot cap. caps_of_state s slot = Some cap \<longrightarrow> is_pml4_cap cap \<longrightarrow> p \<in> obj_refs cap \<longrightarrow>
         cap_asid cap \<noteq> None); invs s\<rbrakk>
    \<Longrightarrow> valid_table_caps_aobj (caps_of_state s) (arch_state s) (ArchObj (PageMapL4 (pml4(slot := pml4e)))) p"
  apply (clarsimp simp: valid_table_caps_def valid_table_caps_aobj_def all_comm
                        empty_table_def
                 split: option.splits
              simp del: split_paired_All )
  apply (drule_tac x = cap in spec)
  apply (erule impE)
   apply fastforce
  apply (drule_tac x = p in spec)
  apply (intro impI allI conjI)
      apply ((clarsimp simp: obj_at_def dest!: invs_valid_objs caps_of_state_valid | drule(2) valid_cap_typ_at)+)[12]
         apply (fastforce simp: obj_at_def dest!: ref_pages_Some)
        apply (fastforce simp: obj_at_def dest!: ref_pages_Some)
    apply (clarsimp simp: obj_at_def dest!: invs_valid_objs caps_of_state_valid | drule(2) valid_cap_typ_at)+
  done


lemmas aobj_upd_invalid_slots_simps = valid_kernel_mappings_if_pm_pml4e valid_global_objs_upd_invalid_pml4e
                                      valid_kernel_mappings_if_pm_pdpte valid_kernel_mappings_if_pm_pte
                                      invs_valid_kernel_mappings invs_valid_global_objs
                                      invs_valid_table_caps
                                      valid_kernel_mappings_if_pm_pde
                                      valid_table_caps_aobj_upd_invalid_pde
                                      valid_table_caps_aobj_upd_invalid_pml4e
                                      valid_global_objs_upd_invalid_pde valid_global_objs_upd_invalid_pte
                                      valid_global_objs_upd_invalid_pdpte
                                      valid_table_caps_aobj_upd_invalid_pte



lemmas pde_ref_simps[simp] = pde_ref_def[split_simps pde.split] pde_ref_pages_def[split_simps pde.split]

lemma valid_vspace_obj_from_invs:
  "\<lbrakk>(ref \<rhd> p) s; kheap s p = Some (ArchObj ao); invs s\<rbrakk> \<Longrightarrow> valid_vspace_obj ao s"
  apply (erule valid_vspace_objsD)
   apply (simp add: obj_at_def)
  apply fastforce
  done

lemma valid_obj_from_invs:
  "\<lbrakk>kheap s p = Some (ArchObj ao); invs s\<rbrakk> \<Longrightarrow> arch_valid_obj ao s"
  by (auto simp: valid_obj_def valid_objs_def obj_at_def dom_def dest!:invs_valid_objs)

lemmas vs_ref_lvl_obj_simps[simp] = vs_ref_lvl_def[split_simps kernel_object.split option.split]
lemmas vs_ref_lvl_simps[simp] = vs_ref_lvl_arch_def[split_simps arch_kernel_obj.split aa_type.split option.split]

lemma valid_pde_vs_ref_lvl_simps[simp]:
  "\<lbrakk>valid_pde pde s; pde_ref pde = Some ptr\<rbrakk> \<Longrightarrow> 4 < vs_ref_lvl (kheap s ptr)"
  by (clarsimp simp: valid_pde_def pde_ref_def obj_at_def aa_type_simps split: pde.split_asm)

lemma valid_pml4e_vs_ref_page_lvl_simps[simp]:
  "\<lbrakk>valid_pml4e pml4e s; pml4e_ref_pages pml4e = Some ptr\<rbrakk> \<Longrightarrow> 2 < vs_ref_lvl (kheap s ptr)"
  by (fastforce simp: valid_pml4e_def pml4e_ref_pages_def obj_at_def data_at_def aa_type_simps split: pml4e.split_asm)

lemma valid_pml4e_vs_ref_lvl_simps[simp]:
  "\<lbrakk>valid_pml4e pml4e s; pml4e_ref pml4e = Some ptr\<rbrakk> \<Longrightarrow> 2 < vs_ref_lvl (kheap s ptr)"
  by (clarsimp simp: valid_pml4e_def pml4e_ref_def obj_at_def aa_type_simps split: pml4e.split_asm)

lemma valid_pdpte_vs_ref_page_lvl_simps[simp]:
  "\<lbrakk>valid_pdpte pdpte s; pdpte_ref_pages pdpte = Some ptr\<rbrakk> \<Longrightarrow> 3 < vs_ref_lvl (kheap s ptr)"
  by (fastforce simp: valid_pdpte_def pdpte_ref_pages_def obj_at_def data_at_def aa_type_simps split: pdpte.split_asm)

lemma valid_pdpte_vs_ref_lvl_simps[simp]:
  "\<lbrakk>valid_pdpte pdpte s; pdpte_ref pdpte = Some ptr\<rbrakk> \<Longrightarrow> 3 < vs_ref_lvl (kheap s ptr)"
  by (clarsimp simp: valid_pdpte_def pdpte_ref_def obj_at_def aa_type_simps split: pdpte.split_asm)

lemma valid_pde_vs_ref_page_lvl_simps[simp]:
  "\<lbrakk>valid_pde pde s; pde_ref_pages pde = Some ptr\<rbrakk> \<Longrightarrow> 4 < vs_ref_lvl (kheap s ptr)"
  by (fastforce simp: valid_pde_def pde_ref_pages_def data_at_def obj_at_def aa_type_simps split: pde.split_asm)

lemma valid_pte_vs_ref_page_lvl_simps[simp]:
  "\<lbrakk>valid_pte pte s; pte_ref_pages pte = Some ptr\<rbrakk> \<Longrightarrow> 5 < vs_ref_lvl (kheap s ptr)"
  by (fastforce simp: valid_pte_def pte_ref_pages_def data_at_def obj_at_def aa_type_simps split: pte.split_asm)

lemma valid_pde_ref_obj_at_weakD:
  "\<lbrakk>valid_pde pde s; pde_ref_pages pde = Some ptr \<rbrakk> \<Longrightarrow> obj_at \<top> ptr s"
  by (fastforce simp: valid_pde_def pde_ref_pages_def obj_at_def data_at_def split: pde.splits )

lemma valid_pte_ref_obj_at_empty_vs_refs_pages:
  "\<lbrakk>valid_pte pte s; pte_ref_pages pte = Some ptr\<rbrakk> \<Longrightarrow> obj_at (\<lambda>obj. vs_refs_pages obj = {}) ptr s"
  apply (clarsimp simp: valid_pte_def obj_at_def pte_ref_pages_def data_at_def split: pte.splits)
  apply (elim disjE)
   apply (clarsimp simp: a_type_simps vs_refs_pages_def)+
  done

lemma valid_pte_ref_obj_at_empty_vs_refs:
  "\<lbrakk>valid_pte pte s; pte_ref_pages pte = Some ptr\<rbrakk> \<Longrightarrow> obj_at (\<lambda>obj. vs_refs obj = {}) ptr s"
  apply (clarsimp simp: valid_pte_def obj_at_def pte_ref_pages_def data_at_def split: pte.splits)
  apply (elim disjE)
   apply (clarsimp simp: a_type_simps vs_refs_def)+
  done

lemma store_pte_invs:
  "\<lbrace>invs and (\<lambda>s. valid_pte pte s) and
         (\<lambda>s. \<forall>ptr. pte_ref_pages pte = Some ptr \<longrightarrow> (
            (\<forall>slot cap. caps_of_state s slot = Some cap \<longrightarrow> is_pt_cap cap \<longrightarrow> p && ~~ mask pt_bits \<in> obj_refs cap \<longrightarrow> cap_asid cap \<noteq> None)
          \<and> (\<forall>ref. (ref \<unrhd> (p && ~~ mask pt_bits)) s
                          \<longrightarrow> (\<exists>slot. cte_wp_at (\<lambda>cap. ptr \<in> obj_refs cap \<and> vs_cap_ref cap = Some (VSRef ((p && mask pt_bits >> word_size_bits) && mask ptTranslationBits) (Some APageTable) #ref))
                              slot s))))
    and (\<lambda>s. p && ~~ mask pt_bits \<notin> global_refs s \<and> wellformed_pte pte)\<rbrace>
  store_pte p pte \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: store_pte_def set_arch_obj_simps)
  apply (wp)
  apply (intro impI allI conjI valid_table_caps_aobj_upd_invalid_pte invs_valid_table_caps,
         simp_all add: obj_at_def)
            apply (clarsimp simp: obj_at_def aa_type_simps aobj_upd_invalid_slots_simps ucast_ucast_mask
                           split: if_split_asm option.split_asm
                            dest: valid_vspace_obj_from_invs valid_obj_from_invs
                   | intro valid_table_caps_aobj_upd_invalid_pte)+
        apply (fastforce dest!: valid_vspace_obj_from_invs)
       apply (clarsimp dest!: valid_obj_from_invs)
      apply (clarsimp simp: obj_at_def aa_type_simps aobj_upd_invalid_slots_simps ucast_ucast_mask
                     split: if_split_asm option.split_asm dest:valid_vspace_obj_from_invs valid_obj_from_invs
                   | intro valid_table_caps_aobj_upd_invalid_pte)+
     apply (rule ccontr)
     apply (drule valid_pte_ref_obj_at_empty_vs_refs_pages)
      apply simp
     apply (clarsimp simp: obj_at_def)
     apply (erule(1) empty_refs_pages_cap_lookup_refs_pages_empty[OF _ rtrancl_into_trancl1])
     apply (drule vs_lookup_pages1_wellformed.lookup1_cut, fastforce, fastforce)
    apply (clarsimp simp: aa_type_simps split: option.split_asm if_split_asm)+
   apply (clarsimp split: if_split_asm option.split_asm dest!:ref_pages_Some simp: lookupable_refs_def)
   apply (drule valid_pte_ref_obj_at_empty_vs_refs_pages)
    apply simp
   apply (clarsimp simp: obj_at_def)
   apply (frule(1) empty_vs_refs_pages_lookup_refs_pages_refl)
    apply fastforce
   apply (clarsimp split: if_split_asm option.split_asm dest!:ref_pages_Some simp: lookupable_refs_def)
  apply (clarsimp split: if_split_asm option.split_asm dest!:ref_pages_Some simp: lookupable_refs_def)
  apply (drule valid_pte_ref_obj_at_empty_vs_refs_pages)
   apply simp
  apply (clarsimp simp: obj_at_def)
  apply (frule(1) empty_vs_refs_pages_lookup_refs_pages_refl)
   apply fastforce
  apply clarsimp
  apply (drule(1) empty_vs_refs_pages_lookup_refs_pages_refl)
   apply fastforce
  apply (clarsimp simp: cte_wp_at_caps_of_state ucast_ucast_mask ptTranslationBits_def)
  done

lemma set_asid_pool_valid_idle [wp]:
  "\<lbrace>\<lambda>s. valid_idle s\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. valid_idle s\<rbrace>"
  including unfold_objects
  by (wpsimp wp: valid_idle_lift  simp: set_asid_pool_def)


lemma set_asid_pool_ifunsafe [wp]:
  "\<lbrace>\<lambda>s. if_unsafe_then_cap s\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. if_unsafe_then_cap s\<rbrace>"
  including unfold_objects
  by (wpsimp simp: set_asid_pool_def)

lemma set_asid_pool_pred_tcb_at[wp]:
  "\<lbrace>pred_tcb_at proj P t\<rbrace> set_asid_pool ptr val \<lbrace>\<lambda>_. pred_tcb_at proj P t\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wpsimp wp: get_object_wp simp: pred_tcb_at_def obj_at_def)
  done

lemma set_asid_pool_reply_caps [wp]:
  "\<lbrace>\<lambda>s. valid_reply_caps s\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. valid_reply_caps s\<rbrace>"
  by (wp valid_reply_caps_st_cte_lift)

crunches set_asid_pool
  for global_ref[wp]: "\<lambda>s. P (global_refs s)"
  (wp: crunch_wps)


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
      by (clarsimp simp: obj_at_def vs_refs_pages_def split: if_split_asm)
         fastforce+
  done


lemma set_asid_pool_vs_lookup_unmap:
  "\<lbrace>valid_vs_lookup and ko_at (ArchObj (ASIDPool ap)) p\<rbrace>
  set_asid_pool p (ap |` S) \<lbrace>\<lambda>_. valid_vs_lookup\<rbrace>"
  apply (wp set_asid_pool_vs_lookup_unmap')
  by (clarsimp simp: obj_at_def
                 elim!: subsetD [OF graph_of_restrict_map])

crunches set_asid_pool
  for v_ker_map[wp]: "valid_kernel_mappings"
  (ignore: set_object wp: set_object_v_ker_map crunch_wps)


lemma set_asid_pool_cur [wp]:
  "\<lbrace>\<lambda>s. P (cur_thread s)\<rbrace> set_asid_pool p a \<lbrace>\<lambda>_ s. P (cur_thread s)\<rbrace>"
  unfolding set_asid_pool_def by (wpsimp wp: get_object_wp)


lemma set_asid_pool_cur_tcb [wp]:
  "\<lbrace>\<lambda>s. cur_tcb s\<rbrace> set_asid_pool p a \<lbrace>\<lambda>_ s. cur_tcb s\<rbrace>"
  unfolding cur_tcb_def
  by (rule hoare_lift_Pf [where f=cur_thread]; wp)


lemma set_asid_pool_valid_arch [wp]:
  "\<lbrace>valid_arch_state\<rbrace> set_asid_pool p a \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  by (rule valid_arch_state_lift) (wp set_asid_pool_typ_at)+


lemma set_asid_pool_valid_objs [wp]:
  "\<lbrace>valid_objs\<rbrace> set_asid_pool p a \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wp set_object_valid_objs get_object_wp)
  including unfold_objects
  by (clarsimp simp: a_type_def valid_obj_def arch_valid_obj_def)

lemma set_asid_pool_global_objs [wp]:
  "\<lbrace>valid_global_objs and valid_arch_state\<rbrace>
   set_asid_pool p ap
   \<lbrace>\<lambda>_. valid_global_objs\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp del: fun_upd_apply
                  split: kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp: valid_global_objs_def valid_vso_at_def simp del: fun_upd_apply)
  apply (rule conjI)
   apply (clarsimp simp: obj_at_def)
   apply (rule conjI)
    subgoal by (clarsimp simp: valid_arch_state_def obj_at_def a_type_def)
   apply clarsimp
   apply (erule (1) valid_vspace_obj_same_type[simplified])
   subgoal by (simp add: a_type_def)
  apply (rule conjI)
   subgoal by (clarsimp simp: obj_at_def valid_arch_state_def a_type_def)
  apply (clarsimp simp: obj_at_def)
  by ((rule conjI)?, clarsimp, drule (1) bspec, clarsimp simp: aa_type_simps a_type_simps)+

lemma set_asid_pool_aligned [wp]:
  "\<lbrace>pspace_aligned\<rbrace> set_asid_pool p ptr \<lbrace>\<lambda>_. pspace_aligned\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wpsimp wp: set_object_aligned[THEN hoare_set_object_weaken_pre]
              simp: a_type_def obj_at_def)
  done

lemma set_asid_pool_distinct [wp]:
  "\<lbrace>pspace_distinct\<rbrace> set_asid_pool p ptr \<lbrace>\<lambda>_. pspace_distinct\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wpsimp wp: set_object_distinct[THEN hoare_set_object_weaken_pre]
              simp: a_type_def obj_at_def)+
  done

lemma set_asid_pool_only_idle [wp]:
  "\<lbrace>only_idle\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>_. only_idle\<rbrace>"
  by (wp only_idle_lift set_asid_pool_typ_at)


lemma set_asid_pool_equal_mappings [wp]:
  "\<lbrace>equal_kernel_mappings\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>rv. equal_kernel_mappings\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wpsimp wp: set_object_equal_mappings[THEN hoare_set_object_weaken_pre]
              simp: a_type_def)
  done

lemma set_asid_pool_valid_global_vspace_mappings[wp]:
  "\<lbrace>valid_global_vspace_mappings\<rbrace>
      set_asid_pool p ap \<lbrace>\<lambda>rv. valid_global_vspace_mappings\<rbrace>"
  apply (simp add: set_asid_pool_def)
  including unfold_objects
  apply (wp set_object_global_vspace_mappings[THEN hoare_set_object_weaken_pre])
  apply (clarsimp simp: a_type_def)
  done

lemma set_asid_pool_kernel_window[wp]:
  "\<lbrace>pspace_in_kernel_window\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>rv. pspace_in_kernel_window\<rbrace>"
  apply (simp add: set_asid_pool_def)
  including unfold_objects
  apply (wpsimp wp: set_object_pspace_in_kernel_window[THEN hoare_set_object_weaken_pre]
              simp: a_type_def)
  done

lemma set_asid_pool_pspace_respects_device_region[wp]:
  "\<lbrace>pspace_respects_device_region\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>rv. pspace_respects_device_region\<rbrace>"
  apply (simp add: set_asid_pool_def)
  including unfold_objects
  apply (wpsimp wp: set_object_pspace_respects_device_region[THEN hoare_set_object_weaken_pre]
              simp: a_type_def)
  done

lemma set_asid_pool_caps_kernel_window[wp]:
  "\<lbrace>cap_refs_in_kernel_window\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>rv. cap_refs_in_kernel_window\<rbrace>"
  apply (simp add: set_asid_pool_def)
  including unfold_objects
  apply (wpsimp wp: set_object_cap_refs_in_kernel_window[THEN hoare_set_object_weaken_pre]
              simp: a_type_def)
  done

lemma set_asid_pool_caps_respects_device_region[wp]:
  "\<lbrace>cap_refs_respects_device_region\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>rv. cap_refs_respects_device_region\<rbrace>"
  apply (simp add: set_asid_pool_def)
  including unfold_objects
  apply (wpsimp wp: set_object_cap_refs_respects_device_region[THEN hoare_set_object_weaken_pre]
              simp: a_type_def)
  done

lemma set_asid_pool_valid_ioc[wp]:
  "\<lbrace>valid_ioc\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  apply (simp add: set_asid_pool_def)
  including unfold_objects
  apply (wpsimp wp: set_object_valid_ioc_no_caps[THEN hoare_set_object_weaken_pre]
              simp: a_type_def is_tcb_def is_cap_table_def)
  done

lemma set_asid_pool_vms[wp]:
  "\<lbrace>valid_machine_state\<rbrace> set_asid_pool p S \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wpsimp wp: set_object_wp_strong)
  apply (erule valid_machine_state_heap_updI)
  apply (fastforce simp: a_type_def obj_at_def
                  split: kernel_object.splits arch_kernel_obj.splits)+
  done

lemma set_asid_pool_table_caps [wp]:
  "\<lbrace>valid_table_caps\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>_. valid_table_caps\<rbrace>"
  apply (simp add: valid_table_caps_def)
  apply (rule hoare_lift_Pf2 [where f=caps_of_state];wp?)
  apply (simp add: set_asid_pool_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def a_type_simps
                 split: kernel_object.splits arch_kernel_obj.splits)
  apply (intro conjI impI; (drule spec | drule (1) mp | elim conjE exE)+;
         simp add: empty_table_def)
  done

lemma set_asid_pool_zombies_state_hyp_refs [wp]:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>
    set_asid_pool p ap
   \<lbrace>\<lambda>_ s. P (state_hyp_refs_of s)\<rbrace>"
  by (simp add: set_object_state_hyp_refs set_arch_obj_simps)

lemma set_asid_pool_invs_restrict:
  "\<lbrace>invs and ko_at (ArchObj (ASIDPool ap)) p \<rbrace>
       set_asid_pool p (ap |` S) \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def valid_asid_map_def
                   valid_arch_caps_def del: set_asid_pool_def)
  apply (wp valid_irq_node_typ
            set_asid_pool_vspace_objs_unmap  valid_irq_handlers_lift
            set_asid_pool_vs_lookup_unmap valid_ioports_lift
         | simp del: set_asid_pool_def)+
  done

lemma set_asid_pool_invs_unmap:
  "\<lbrace>invs and ko_at (ArchObj (ASIDPool ap)) p\<rbrace>
       set_asid_pool p (ap(x := None)) \<lbrace>\<lambda>_. invs\<rbrace>"
  using set_asid_pool_invs_restrict[where S="- {x}"]
  by (simp add: restrict_map_def fun_upd_def if_flip)


lemma vs_refs_empty_from_pages_empty:
  "vs_refs_pages a = {} \<Longrightarrow> vs_refs a = {}"
  apply (case_tac a)
   apply (auto simp: vs_refs_pages_def pde_ref_pages_def pdpte_ref_def pdpte_ref_pages_def
                    pde_ref_def graph_of_def vs_refs_def pml4e_ref_pages_def pml4e_ref_def
              split: arch_kernel_obj.splits pde.splits pdpte.splits if_splits)
  done

lemma empty_refs_is_valid:
  "\<lbrakk>vs_refs_pages (ArchObj ao) = {};
    valid_arch_state s\<rbrakk> \<Longrightarrow> valid_vspace_obj ao s"
  apply (case_tac ao)
      apply (simp_all add: vs_refs_pages_def ran_def graph_of_def)
     apply (clarsimp, drule_tac x = x in spec, clarsimp simp: pte_ref_pages_def split: pte.splits)
    apply (clarsimp, drule_tac x = x in spec, clarsimp simp: pde_ref_pages_def split: pde.splits)
   apply (clarsimp, drule_tac x = x in spec, clarsimp simp: pdpte_ref_pages_def split: pdpte.splits)
  apply (clarsimp, drule_tac x = x in spec, clarsimp simp: pml4e_ref_pages_def split: pml4e.splits)
  done

lemma store_pde_invs:
  "\<lbrace>invs and (\<lambda>s. valid_pde pde s) and
         (\<lambda>s. \<forall>ptr. pde_ref_pages pde = Some ptr \<longrightarrow> (
             obj_at (\<lambda>ko. vs_refs_pages ko = {}) ptr s
          \<and> (\<forall>slot cap. caps_of_state s slot = Some cap \<longrightarrow> is_pd_cap cap \<longrightarrow> p && ~~ mask pd_bits \<in> obj_refs cap \<longrightarrow> cap_asid cap \<noteq> None)
          \<and> (\<forall>ref. (ref \<unrhd> (p && ~~ mask pd_bits)) s
                          \<longrightarrow> (\<exists>slot. cte_wp_at (\<lambda>cap. ptr \<in> obj_refs cap \<and> vs_cap_ref cap = Some (VSRef ((p && mask pd_bits >> word_size_bits) && mask ptTranslationBits) (Some APageDirectory) #ref))
                              slot s))))
    and (\<lambda>s. p && ~~ mask pd_bits \<notin> global_refs s \<and> wellformed_pde pde)\<rbrace>
  store_pde p pde \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: store_pde_def set_arch_obj_simps)
  apply (wp)
  apply (intro impI allI conjI valid_table_caps_aobj_upd_invalid_pde invs_valid_table_caps , simp_all add: obj_at_def)
              apply (clarsimp simp: obj_at_def aa_type_simps aobj_upd_invalid_slots_simps ucast_ucast_mask
                             split: if_split_asm option.split_asm dest:valid_vspace_obj_from_invs valid_obj_from_invs
                     | intro valid_table_caps_aobj_upd_invalid_pde)+
          apply (fastforce dest!: valid_vspace_obj_from_invs)
         apply (clarsimp dest!: valid_obj_from_invs)
        apply (clarsimp simp: obj_at_def aa_type_simps aobj_upd_invalid_slots_simps ucast_ucast_mask
                       split: if_split_asm option.split_asm dest:valid_vspace_obj_from_invs valid_obj_from_invs
                     | intro valid_table_caps_aobj_upd_invalid_pde)+
        apply (rule ccontr)
        apply (clarsimp dest!: ref_pages_Some)
        apply (erule(1) empty_refs_cap_lookup_refs_empty[OF vs_refs_empty_from_pages_empty rtrancl_into_trancl1])
         apply (drule vs_lookup1_wellformed.lookup1_cut, fastforce, fastforce)
       apply (clarsimp simp: aa_type_simps split: option.split_asm if_split_asm)+
      apply (rule ccontr)
      apply (erule empty_refs_pages_cap_lookup_refs_pages_empty[OF _ ])
       apply (erule rtrancl_into_trancl1)
       apply (drule vs_lookup_pages1_wellformed.lookup1_cut, fastforce, fastforce)
     apply (clarsimp split: option.split_asm if_split_asm simp: aa_type_simps)
     apply (drule(1) valid_pde_vs_ref_page_lvl_simps, simp)
    apply (clarsimp split: if_split_asm option.split_asm dest!:ref_pages_Some simp: lookupable_refs_def)
    apply (frule(2) empty_vs_refs_lookup_refs_refl[OF vs_refs_empty_from_pages_empty])
    apply clarsimp
    apply (erule empty_refs_is_valid)
     apply fastforce
   apply (clarsimp split: if_split_asm option.split_asm dest!:ref_pages_Some simp: lookupable_refs_def)
   apply (frule(2) empty_vs_refs_pages_lookup_refs_pages_refl)
   apply clarsimp
  apply (clarsimp split: if_split_asm option.split_asm dest!:ref_pages_Some simp: lookupable_refs_def)
  apply (drule(2) empty_vs_refs_pages_lookup_refs_pages_refl)
  apply (clarsimp simp: cte_wp_at_caps_of_state ucast_ucast_mask ptTranslationBits_def)
  done

lemma store_pdpte_invs:
  "\<lbrace>invs and (\<lambda>s. valid_pdpte pdpte s) and
         (\<lambda>s. \<forall>ptr. pdpte_ref_pages pdpte = Some ptr \<longrightarrow> (
             obj_at ((\<lambda>ko. vs_refs_pages ko = {})) ptr s
          \<and> (\<forall>slot cap. caps_of_state s slot = Some cap \<longrightarrow> is_pdpt_cap cap \<longrightarrow> p && ~~ mask pdpt_bits \<in> obj_refs cap \<longrightarrow> cap_asid cap \<noteq> None)
          \<and> (\<forall>ref. (ref \<unrhd> (p && ~~ mask pdpt_bits)) s
                          \<longrightarrow> (\<exists>slot. cte_wp_at (\<lambda>cap. ptr \<in> obj_refs cap \<and> vs_cap_ref cap = Some (VSRef ((p && mask pdpt_bits >> word_size_bits) && mask ptTranslationBits) (Some APDPointerTable) #ref))
                              slot s))))
    and (\<lambda>s. p && ~~ mask pdpt_bits \<notin> global_refs s \<and> wellformed_pdpte pdpte)\<rbrace>
  store_pdpte p pdpte \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: store_pdpte_def set_arch_obj_simps)
  apply (wp)
  apply (intro impI allI conjI valid_table_caps_aobj_upd_invalid_pdpte invs_valid_table_caps , simp_all add: obj_at_def)
              apply (clarsimp simp: obj_at_def aa_type_simps aobj_upd_invalid_slots_simps ucast_ucast_mask
                             split: if_split_asm option.split_asm dest:valid_vspace_obj_from_invs valid_obj_from_invs
                     | intro valid_table_caps_aobj_upd_invalid_pdpte)+
          apply (fastforce dest!: valid_vspace_obj_from_invs)
         apply (clarsimp dest!: valid_obj_from_invs)
        apply (clarsimp simp: obj_at_def aa_type_simps aobj_upd_invalid_slots_simps ucast_ucast_mask
                       split: if_split_asm option.split_asm dest:valid_vspace_obj_from_invs valid_obj_from_invs
                     | intro valid_table_caps_aobj_upd_invalid_pde)+
       apply (rule ccontr)
       apply (clarsimp dest!: ref_pages_Some)
        apply (erule(1) empty_refs_cap_lookup_refs_empty[OF vs_refs_empty_from_pages_empty rtrancl_into_trancl1])
       apply (drule vs_lookup1_wellformed.lookup1_cut, fastforce, fastforce)
      apply (clarsimp simp: aa_type_simps split: option.split_asm if_split_asm)+
     apply (rule ccontr)
     apply (erule empty_refs_pages_cap_lookup_refs_pages_empty[OF _ ])
     apply (erule rtrancl_into_trancl1)
     apply (drule vs_lookup_pages1_wellformed.lookup1_cut, fastforce, fastforce)
    apply (clarsimp split: option.split_asm if_split_asm simp: aa_type_simps)
    apply (drule(1) valid_pdpte_vs_ref_page_lvl_simps, simp)
   apply (clarsimp split: if_split_asm option.split_asm dest!:ref_pages_Some simp: lookupable_refs_def)
   apply (frule(2) empty_vs_refs_lookup_refs_refl[OF vs_refs_empty_from_pages_empty])
   apply clarsimp
   apply (erule empty_refs_is_valid)
    apply fastforce
  apply (clarsimp split: if_split_asm option.split_asm dest!:ref_pages_Some simp: lookupable_refs_def)
  apply (frule(2) empty_vs_refs_pages_lookup_refs_pages_refl)
  apply clarsimp
  apply (clarsimp split: if_split_asm option.split_asm dest!:ref_pages_Some simp: lookupable_refs_def)
  apply (drule(2) empty_vs_refs_pages_lookup_refs_pages_refl)
  apply (clarsimp simp: cte_wp_at_caps_of_state ucast_ucast_mask ptTranslationBits_def)
  done

lemma store_pml4e_invs:
  "\<lbrace>invs and (\<lambda>s. valid_pml4e pml4e s) and
         (\<lambda>s. \<forall>ptr. pml4e_ref_pages pml4e = Some ptr \<longrightarrow> (
            (ptr \<in> set (second_level_tables (arch_state s))) = (ucast (p && mask pml4_bits >> word_size_bits) \<in> kernel_mapping_slots)
          \<and> obj_at (empty_table (set (second_level_tables (arch_state s)))) ptr s
          \<and> (\<forall>slot cap. caps_of_state s slot = Some cap \<longrightarrow> is_pml4_cap cap \<longrightarrow> p && ~~ mask pml4_bits \<in> obj_refs cap \<longrightarrow> cap_asid cap \<noteq> None)
          \<and> (\<forall>ref. (ref \<unrhd> (p && ~~ mask pml4_bits)) s
                          \<longrightarrow> (\<exists>slot. cte_wp_at (\<lambda>cap. ptr \<in> obj_refs cap \<and> vs_cap_ref cap = Some (VSRef ((p && mask pml4_bits >> word_size_bits) && mask ptTranslationBits) (Some APageMapL4) #ref))
                              slot s))))
    and (\<lambda>s. \<forall>pm. ko_at (ArchObj (PageMapL4 pm)) (p && ~~ mask pml4_bits) s
          \<longrightarrow> ucast (p && mask pml4_bits >> word_size_bits) \<in> kernel_mapping_slots \<longrightarrow> pm (ucast (p && mask pml4_bits >> word_size_bits)) = pml4e)
    and (\<lambda>s. p && ~~ mask pml4_bits \<notin> global_refs s \<and> wellformed_pml4e pml4e)\<rbrace>
  store_pml4e p pml4e \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: store_pml4e_def set_arch_obj_simps)
  apply (wp)
  apply (intro impI allI conjI valid_table_caps_aobj_upd_invalid_pml4e invs_valid_table_caps , simp_all add: obj_at_def)
              apply (clarsimp simp: obj_at_def aa_type_simps aobj_upd_invalid_slots_simps ucast_ucast_mask
                             split: if_split_asm option.split_asm dest:valid_vspace_obj_from_invs valid_obj_from_invs
                     | intro valid_table_caps_aobj_upd_invalid_pml4e valid_kernel_mappings_if_pm_pml4e)+
             apply fastforce
            apply (clarsimp dest!: ref_pages_Some)
           apply (clarsimp simp: obj_at_def aa_type_simps aobj_upd_invalid_slots_simps ucast_ucast_mask
                        split: if_split_asm option.split_asm dest:valid_vspace_obj_from_invs valid_obj_from_invs
                     | intro valid_table_caps_aobj_upd_invalid_pde)+
          apply (fastforce dest!: valid_vspace_obj_from_invs)
         apply (clarsimp dest!: valid_obj_from_invs)
        apply (clarsimp simp: obj_at_def aa_type_simps aobj_upd_invalid_slots_simps ucast_ucast_mask
                        split: if_split_asm option.split_asm dest:valid_vspace_obj_from_invs valid_obj_from_invs
                     | intro valid_table_caps_aobj_upd_invalid_pde)+
        apply (rule ccontr)
        apply (clarsimp dest!: ref_pages_Some)
        apply (erule(1) unmapped_cap_lookup_refs_empty[OF _ rtrancl_into_trancl1])
         apply (drule vs_lookup1_wellformed.lookup1_cut, fastforce, fastforce)
       apply (clarsimp simp: aa_type_simps split: option.split_asm if_split_asm)+
      apply (rule ccontr)
      apply (erule unmapped_cap_lookup_refs_pages_empty[OF _ ])
       apply (erule rtrancl_into_trancl1)
       apply (drule vs_lookup_pages1_wellformed.lookup1_cut, fastforce, fastforce)
     apply (clarsimp split: option.split_asm if_split_asm simp: aa_type_simps)
     apply (drule(1) valid_pml4e_vs_ref_page_lvl_simps, simp)
    apply (clarsimp simp: lookupable_refs_def dest!: ref_pages_Some
                   split: if_split_asm option.split_asm)
    apply (frule(2) empty_table_lookup_refs_refl)
    apply clarsimp
    apply (erule empty_table_is_valid)
    apply fastforce
   apply (clarsimp simp: lookupable_refs_def dest!:ref_pages_Some
                  split: if_split_asm option.split_asm)
   apply (frule(2) empty_table_lookup_refs_pages_refl)
   apply clarsimp
  apply (clarsimp simp: lookupable_refs_def dest!:ref_pages_Some
                 split: if_split_asm option.split_asm)
  apply (drule(2) empty_table_lookup_refs_pages_refl)
  apply (clarsimp simp: cte_wp_at_caps_of_state ucast_ucast_mask ptTranslationBits_def)
  done

lemma pspace_respects_device_region_dmo:
  assumes valid_f: "\<And>P. \<lbrace>\<lambda>ms. P (device_state ms)\<rbrace> f \<lbrace>\<lambda>r ms. P (device_state ms)\<rbrace>"
  shows "\<lbrace>pspace_respects_device_region\<rbrace>do_machine_op f\<lbrace>\<lambda>r. pspace_respects_device_region\<rbrace>"
  apply (clarsimp simp: do_machine_op_def gets_def select_f_def simpler_modify_def
                        bind_def valid_def get_def return_def)
  apply (drule use_valid[OF _ valid_f,
                         of _ _ _ "(=) (device_state (machine_state s))" for s,
                         OF _ refl])
  by simp

lemma cap_refs_respects_device_region_dmo:
  assumes valid_f: "\<And>P. \<lbrace>\<lambda>ms. P (device_state ms)\<rbrace> f \<lbrace>\<lambda>r ms. P (device_state ms)\<rbrace>"
  shows "\<lbrace>cap_refs_respects_device_region\<rbrace> do_machine_op f\<lbrace>\<lambda>r. cap_refs_respects_device_region\<rbrace>"
  apply (clarsimp simp: do_machine_op_def gets_def select_f_def simpler_modify_def bind_def
                        valid_def get_def return_def)
  apply (drule use_valid[OF _ valid_f,
                         of _ _ _ "(=) (device_state (machine_state s))" for s,
                         OF _ refl])
  by simp

lemma machine_op_lift_device_state[wp]:
  "\<lbrace>\<lambda>ms. P (device_state ms)\<rbrace> machine_op_lift f \<lbrace>\<lambda>_ ms. P (device_state ms)\<rbrace>"
  by (clarsimp simp: machine_op_lift_def Nondet_VCG.valid_def bind_def
                     machine_rest_lift_def gets_def simpler_modify_def get_def return_def
                     select_def ignore_failure_def select_f_def
              split: if_splits)

lemma as_user_inv:
  assumes x: "\<And>P. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>x. P\<rbrace>"
  shows      "\<lbrace>P\<rbrace> as_user t f \<lbrace>\<lambda>x. P\<rbrace>"
  proof -
  have P: "\<And>a b input. (a, b) \<in> fst (f input) \<Longrightarrow> b = input"
    by (rule use_valid [OF _ x], assumption, rule refl)
  have Q: "\<And>s ps. ps (kheap s) = kheap s \<Longrightarrow> kheap_update ps s = s"
    by simp
  show ?thesis
    apply (simp add: as_user_def gets_the_def assert_opt_def split_def bind_assoc)
    apply (wpsimp wp: set_object_wp)
    apply (clarsimp dest!: P)
    apply (subst Q)
     prefer 2
     apply assumption
    apply (rule ext)
    apply (simp add: get_tcb_def)
    apply (case_tac "kheap s t"; simp)
    apply (case_tac a; simp)
    apply (clarsimp simp: arch_tcb_context_set_def arch_tcb_context_get_def)
    done
qed

crunches getRegister
  for inv[wp]: P
  (simp: getRegister_def)

lemmas user_getreg_inv[wp] = as_user_inv[OF getRegister_inv]

end

end
