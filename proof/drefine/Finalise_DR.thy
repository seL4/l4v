(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Finalise_DR
imports
  KHeap_DR
  "AInvs.VSpaceEntries_AI"
begin

context begin interpretation Arch . (*FIXME: arch-split*)

definition
 "transform_pd_slot_ref x
     = (x && ~~ mask pd_bits,
        unat ((x && mask pd_bits) >> 2))"
definition
 "transform_pt_slot_ref x
     = (x && ~~ mask pt_bits,
        unat ((x && mask pt_bits) >> 2))"

lemma transform_cap_Null [simp]:
  "(transform_cap cap = cdl_cap.NullCap) = (cap = cap.NullCap)"
  apply (cases cap, simp_all)
  apply (rename_tac arch_cap)
  apply (case_tac arch_cap, simp_all)
  done

lemma dcorres_get_irq_slot:
  "dcorres (\<lambda>r r'. r = transform_cslot_ptr r') \<top> \<top> (gets (CSpace_D.get_irq_slot x)) (KHeap_A.get_irq_slot x)"
  apply (simp add:gets_def CSpace_D.get_irq_slot_def KHeap_A.get_irq_slot_def)
  apply (rule dcorres_absorb_get_l)
  apply (rule dcorres_absorb_get_r)
  apply (clarsimp simp: return_def transform_def corres_underlying_def transform_cslot_ptr_def)
done

lemma do_machine_op_wp:
  "\<forall>m. \<lbrace>\<lambda>ms. underlying_memory ms = m\<rbrace> mop \<lbrace>\<lambda>rv ms. underlying_memory ms = m\<rbrace>
    \<Longrightarrow> \<lbrace>\<lambda>ps. transform ps = cs\<rbrace> do_machine_op mop \<lbrace>\<lambda>r ps. transform ps = cs\<rbrace>"
  apply (clarsimp simp:do_machine_op_def gets_def get_def return_def bind_def select_f_def simpler_modify_def)
  apply (clarsimp simp:valid_def)
  apply (drule_tac x = "(machine_state s)" in spec)
  apply (drule_tac x = "(a,b)" in bspec)
    apply simp
  apply clarsimp
  apply (clarsimp simp:transform_def transform_current_thread_def)
  apply (simp add: transform_objects_def2)
  done

lemmas dmo_dwp = do_machine_op_wp [OF allI]

lemma machine_op_lift[wp]:
  "\<lbrace>\<lambda>ms. underlying_memory ms = m\<rbrace> machine_op_lift x \<lbrace>\<lambda>rv ms. underlying_memory ms = m\<rbrace>"
  apply (clarsimp simp:machine_rest_lift_def ignore_failure_def machine_op_lift_def)
  apply (wpsimp simp:simpler_modify_def valid_def)
  done

lemma invalidateLocalTLB_ASID_underlying_memory[wp]:
  "\<lbrace>\<lambda>ms. underlying_memory ms = m\<rbrace> invalidateLocalTLB_ASID a \<lbrace>\<lambda>rv ms. underlying_memory ms = m\<rbrace>"
  apply (clarsimp simp: invalidateLocalTLB_ASID_def, wp)
  done

lemma dsb_underlying_memory[wp]: "\<lbrace>\<lambda>ms. underlying_memory ms = m\<rbrace> dsb \<lbrace>\<lambda>rv ms. underlying_memory ms = m\<rbrace>"
  apply (clarsimp simp: dsb_def, wp)
done

lemma isb_underlying_memory[wp]:
  "\<lbrace>\<lambda>ms. underlying_memory ms = m\<rbrace> isb \<lbrace>\<lambda>rv ms. underlying_memory ms = m\<rbrace>"
  by (clarsimp simp: isb_def, wp)

lemma invalidate_asid_dwp[wp]:
  "\<lbrace>\<lambda>ps. transform ps = cs\<rbrace> invalidate_asid (the (hw_asid_table next_asid)) \<lbrace>\<lambda>x ps. transform ps = cs\<rbrace>"
  apply (clarsimp simp:invalidate_asid_def)
  apply wp
  apply (clarsimp simp:transform_def transform_objects_def2 transform_current_thread_def transform_cdt_def transform_asid_table_def)
  done

lemma invalidate_hw_asid_entry_dwp[wp]:
  "\<lbrace>\<lambda>s. transform s = cs\<rbrace> invalidate_hw_asid_entry next_asid \<lbrace>\<lambda>xb a. transform a = cs\<rbrace>"
  apply (clarsimp simp:invalidate_hw_asid_entry_def)
  apply wp
  apply (clarsimp simp:transform_def transform_objects_def2 transform_current_thread_def transform_cdt_def transform_asid_table_def)
done

lemma write_ttbr0_ptr_dwp[wp]:
  "\<lbrace>\<lambda>ms. underlying_memory ms = m\<rbrace> write_ttbr0_ptr paddr \<lbrace>\<lambda>rv ms. underlying_memory ms = m\<rbrace>"
  by (clarsimp simp: write_ttbr0_ptr_def writeTTBR0_def, wp)

lemma set_hardware_asid_dwp[wp]:
  " \<lbrace>\<lambda>ms. underlying_memory ms = m\<rbrace> setHardwareASID hw_asid \<lbrace>\<lambda>rv ms. underlying_memory ms = m\<rbrace>"
  by (clarsimp simp:setHardwareASID_def,wp)


lemma store_hardware_asid_dwp[wp]:
  "\<lbrace>\<lambda>s. transform s = cs\<rbrace> store_hw_asid a xa \<lbrace>\<lambda>xb a. transform a = cs\<rbrace>"
  apply (clarsimp simp:store_hw_asid_def)
  apply wp
  apply (simp add:find_pd_for_asid_assert_def)
  apply wp
  apply (simp add:find_pd_for_asid_def)
  apply (wp|wpc)+
  apply (clarsimp simp:transform_def transform_objects_def2 transform_current_thread_def transform_cdt_def transform_asid_table_def)
done

lemma  transform_arch_state:
  "\<lbrakk> arm_globals_frame (arch_state a) = arm_globals_frame x;
       arm_asid_table (arch_state a) = arm_asid_table x \<rbrakk>
    \<Longrightarrow> transform (a\<lparr>arch_state := x \<rparr>) = transform a"
  by (clarsimp simp:transform_def transform_objects_def2 transform_cdt_def
    transform_current_thread_def transform_asid_table_def)

lemma find_free_hw_asid_dwp[wp]:
  "\<lbrace>\<lambda>s. transform s = cs\<rbrace> find_free_hw_asid \<lbrace>\<lambda>xa s. transform s = cs\<rbrace>"
  apply (clarsimp simp:find_free_hw_asid_def)
  apply (wp|wpc)+
  apply (clarsimp simp:transform_arch_state)
  apply (wp do_machine_op_wp |clarsimp simp:)+
done

lemma arch_obj_not_idle:
  "\<lbrakk>valid_idle s;kheap s ptr = Some (ArchObj x )\<rbrakk> \<Longrightarrow> not_idle_thread ptr s"
  by (clarsimp simp:not_idle_thread_def valid_idle_def obj_at_def pred_tcb_at_def)

lemma asid_pool_at_rev:
  "\<lbrakk> kheap s a = Some (ArchObj (arch_kernel_obj.ASIDPool fun)) \<rbrakk> \<Longrightarrow> asid_pool_at a s"
  apply (clarsimp simp: obj_at_def valid_idle_def st_tcb_at_def)
  apply (clarsimp simp: a_type_def
                 split: arch_kernel_obj.splits Structures_A.kernel_object.split_asm if_splits)
  done

lemma asid_pool_not_idle:
  "\<lbrakk> valid_idle s; asid_pool_at a s \<rbrakk> \<Longrightarrow> not_idle_thread a s"
  apply (clarsimp simp:obj_at_def valid_idle_def pred_tcb_at_def)
  apply (clarsimp simp: not_idle_thread_def
                 split: if_splits)
  done

lemma opt_object_asid_pool:
  "\<lbrakk> valid_idle s; kheap s a = Some (ArchObj (arch_kernel_obj.ASIDPool fun)) \<rbrakk> \<Longrightarrow>
     cdl_objects (transform s) a = Some (cdl_object.AsidPool \<lparr>cdl_asid_pool_caps = transform_asid_pool_contents fun\<rparr>)"
  apply (frule asid_pool_at_rev)
  apply (frule(1) asid_pool_not_idle)
  apply (clarsimp simp: transform_objects_def transform_def not_idle_thread_def restrict_map_def)
  done

lemma transform_asid_pool_contents_upd:
  "transform_asid_pool_contents (pool(ucast asid := pd)) =
   (transform_asid_pool_contents pool)(snd (transform_asid asid) \<mapsto> transform_asid_pool_entry pd)"
  apply (clarsimp simp:transform_asid_pool_contents_def transform_asid_def)
  apply (rule ext)
  apply (case_tac x)
   apply (clarsimp simp:unat_eq_0 unat_map_def)
  apply (safe | clarsimp)+
  apply (safe | clarsimp simp:unat_map_def)+
  apply (subst (asm) of_nat_Suc[symmetric])
  apply (rule_tac P="Suc nat = unat (ucast asid)" in notE, simp)
  apply (cut_tac x="Suc nat" and y="unat (ucast asid :: 10 word)" in word_unat.Abs_inject[symmetric, where 'a=10])
    apply (simp add:unats_def)+
   apply (rule unat_lt2p[where x="ucast asid :: 10 word", simplified])
  apply simp
  done

lemma dcorres_set_asid_pool:
  "\<lbrakk> pool' = pool (ucast asid := pd); slot = snd (transform_asid asid);
     cap = transform_asid_pool_entry pd \<rbrakk> \<Longrightarrow>
    dcorres dc \<top> (valid_idle and ko_at (ArchObj (arch_kernel_obj.ASIDPool pool)) a)
    (KHeap_D.set_cap (a, slot) cap)
    (set_asid_pool a pool')"
  apply (simp add:KHeap_D.set_cap_def set_asid_pool_def get_object_def gets_the_def
                  gets_def bind_assoc)
  apply (rule dcorres_absorb_get_l)
  apply (clarsimp simp: obj_at_def opt_object_asid_pool assert_opt_def has_slots_def)
  apply (clarsimp simp: KHeap_D.set_object_def simpler_modify_def put_def bind_def
                       corres_underlying_def update_slots_def return_def object_slots_def)
  apply (clarsimp simp: KHeap_A.set_object_def get_object_def in_monad get_def
                        put_def bind_def return_def)
  apply (clarsimp simp: transform_def transform_current_thread_def)
  apply (drule(1) arch_obj_not_idle)
  apply (rule ext)
  apply (clarsimp simp: not_idle_thread_def transform_objects_def restrict_map_def map_add_def)
  apply (rule transform_asid_pool_contents_upd)
  done

lemma dcorres_set_vm_root:
  "dcorres dc \<top> \<top> (return x) (set_vm_root rvd)"
  apply (clarsimp simp: set_vm_root_def set_global_pd_def)
  apply (rule dcorres_symb_exec_r)+
    apply (clarsimp simp:catch_def throwError_def)
    apply (rule corres_dummy_return_r)
    apply (rule dcorres_symb_exec_r[OF corres_free_return[where P=\<top> and P'=\<top>]])+
     apply wp+
      apply wpc
       apply (wp do_machine_op_wp | clarsimp)+
     apply (rule_tac Q'="\<lambda>_ s. transform s = cs" in hoare_post_imp)
      apply simp
     apply (wpsimp wp: whenE_wp do_machine_op_wp [OF allI] hoare_drop_imps find_pd_for_asid_inv
                simp: arm_context_switch_def get_hw_asid_def load_hw_asid_def if_apply_def2)+
  done

lemma invalidateLocalTLB_VAASID_underlying_memory[wp]:
  "\<lbrace>\<lambda>ms. underlying_memory ms = m\<rbrace> invalidateLocalTLB_VAASID word \<lbrace>\<lambda>rv ms. underlying_memory ms = m\<rbrace>"
  by (clarsimp simp: invalidateLocalTLB_VAASID_def, wp)

lemma dcorres_flush_page:
  "dcorres dc \<top> \<top>  (return x) (flush_page aa a b word)"
  supply if_cong[cong]
  apply (rule corres_dummy_return_r)
  apply (rule dcorres_symb_exec_r[OF corres_free_return[where P=\<top> and P'=\<top>]])
   apply wp
  apply (simp add:flush_page_def)
  apply wp
        apply (rule dcorres_to_wp[OF dcorres_set_vm_root])
       apply wp
      apply clarsimp
      apply (wp do_machine_op_wp, clarsimp)
      apply (wp)
     apply (simp add:load_hw_asid_def)
     apply wp
    apply (clarsimp simp:set_vm_root_for_flush_def)
    apply (wp do_machine_op_wp|clarsimp simp:arm_context_switch_def get_hw_asid_def)+
         apply (wpc)
          apply wp+
        apply (rule hoare_conjI,rule hoare_drop_imp)
         apply (wp do_machine_op_wp|clarsimp simp:load_hw_asid_def)+
      apply (wpc|wp)+
     apply (rule_tac Q'="\<lambda>rv s. transform s = cs" in hoare_strengthen_post)
      apply (wp|clarsimp)+
done

lemma page_table_not_idle:
  "\<lbrakk>valid_idle s;page_table_at a s\<rbrakk> \<Longrightarrow> not_idle_thread a s"
  apply (clarsimp simp:obj_at_def valid_idle_def pred_tcb_at_def)
  apply (clarsimp simp: not_idle_thread_def split: if_splits)
  done

lemma page_directory_not_idle:
  "\<lbrakk>valid_idle s;page_directory_at a s\<rbrakk> \<Longrightarrow> not_idle_thread a s"
  apply (clarsimp simp:obj_at_def valid_idle_def pred_tcb_at_def)
  apply (clarsimp simp: not_idle_thread_def split: if_splits)
  done

lemma page_table_at_rev:
  "\<lbrakk>kheap s a = Some (ArchObj (arch_kernel_obj.PageTable fun))\<rbrakk> \<Longrightarrow> page_table_at a s"
  apply (clarsimp simp:obj_at_def valid_idle_def pred_tcb_at_def)
  apply (clarsimp simp:a_type_def split: if_splits)
  done

lemma page_directory_at_rev:
  "\<lbrakk>kheap s a = Some (ArchObj (arch_kernel_obj.PageDirectory fun))\<rbrakk> \<Longrightarrow> page_directory_at a s"
  apply (clarsimp simp:obj_at_def valid_idle_def st_tcb_at_def)
  apply (clarsimp simp:a_type_def split: if_splits)
  done

lemma mask_pd_bits_less:
  "unat ((y::word32) && mask pd_bits >> 2) < 4096"
  apply (clarsimp simp:pd_bits_def pageBits_def simp del: nat_uint_eq)
  apply (unfold unat_def)
  apply (rule iffD2[OF nat_less_eq_zless[where z = 4096,simplified]])
   apply (simp)
  using shiftr_less_t2n'[where m = 12 and x ="(y && mask 14)" and n =2 ,simplified,THEN iffD1[OF word_less_alt]]
  apply (clarsimp simp:mask_twice)
  done

lemma mask_pt_bits_less:
  "unat ((y::word32) && mask pt_bits >> 2) < 256"
  apply (clarsimp simp:pt_bits_def pageBits_def)
  apply (unfold unat_def)
  apply (rule iffD2[OF nat_less_eq_zless[where z = 256,simplified]])
  apply (simp)
  using shiftr_less_t2n'[where m = 8 and x ="(y && mask 10)" and n =2 ,simplified,THEN iffD1[OF word_less_alt]]
  apply (clarsimp simp:mask_twice)
  done

definition pd_pt_relation :: "word32\<Rightarrow>word32\<Rightarrow>word32\<Rightarrow>'z::state_ext state\<Rightarrow>bool"
where "pd_pt_relation pd pt offset s \<equiv>
  \<exists>fun u v ref. ( kheap s pd = Some (ArchObj (arch_kernel_obj.PageDirectory fun))
  \<and> page_table_at pt s \<and> fun (ucast (offset && mask pd_bits >> 2)) = ARM_A.pde.PageTablePDE ref u v
  \<and> pt = ptrFromPAddr ref )"

definition pd_section_relation :: "word32\<Rightarrow>word32\<Rightarrow>word32\<Rightarrow>'z::state_ext state\<Rightarrow>bool"
where "pd_section_relation pd pt offset s \<equiv>
  \<exists>fun u v ref1 ref2. ( kheap s pd = Some (ArchObj (arch_kernel_obj.PageDirectory fun))
  \<and> fun (ucast (offset && mask pd_bits >> 2)) = ARM_A.pde.SectionPDE ref1 u ref2 v
  \<and> pt = ptrFromPAddr ref1 )"

definition pd_super_section_relation :: "word32\<Rightarrow>word32\<Rightarrow>word32\<Rightarrow>'z::state_ext state\<Rightarrow>bool"
where "pd_super_section_relation pd pt offset s \<equiv>
  \<exists>fun u v ref1. ( kheap s pd = Some (ArchObj (arch_kernel_obj.PageDirectory fun))
  \<and> fun (ucast (offset && mask pd_bits >> 2)) = ARM_A.pde.SuperSectionPDE ref1 u v
  \<and> pt = ptrFromPAddr ref1 )"

definition pt_page_relation :: "word32\<Rightarrow>word32\<Rightarrow>word32\<Rightarrow>vmpage_size set\<Rightarrow>'z::state_ext state\<Rightarrow>bool"
where "pt_page_relation pt page offset S s \<equiv>
  \<exists>fun. (kheap s pt = Some (ArchObj (arch_kernel_obj.PageTable fun)))
  \<and> (case fun (ucast (offset && mask pt_bits >> 2)) of
    ARM_A.pte.LargePagePTE ref fun1 fun2 \<Rightarrow>
        page = ptrFromPAddr ref \<and> ARMLargePage \<in> S
  | ARM_A.pte.SmallPagePTE ref fun1 fun2 \<Rightarrow>
        page = ptrFromPAddr ref \<and> ARMSmallPage \<in> S
  | _ \<Rightarrow> False)"

lemma below_kernel_base:
  "ucast (y && mask pd_bits >> 2) \<notin> kernel_mapping_slots
    \<Longrightarrow> kernel_pde_mask f (ucast (y && mask pd_bits >> 2))
    = f (of_nat (unat (y && mask pd_bits >> 2)))"
  by (clarsimp simp:kernel_pde_mask_def kernel_mapping_slots_def )

lemma opt_cap_page_table:
  "\<lbrakk> valid_idle s;pd_pt_relation a pt_id x s;ucast (x && mask pd_bits >> 2) \<notin> kernel_mapping_slots \<rbrakk>
  \<Longrightarrow> \<exists>attr. opt_cap (a, unat (x && mask pd_bits >> 2)) (transform s) = Some (cdl_cap.PageTableCap PT pt_id (Fake attr) None)"
  apply (clarsimp simp :pd_pt_relation_def opt_cap_def transform_def slots_of_def)
  apply (frule page_directory_at_rev)
  apply (frule(1) page_directory_not_idle)
  apply (clarsimp simp: transform_objects_def not_idle_thread_def page_directory_not_idle
                        restrict_map_def object_slots_def)
  apply (clarsimp simp: transform_page_directory_contents_def unat_map_def | rule conjI )+
   apply (clarsimp simp: transform_page_directory_contents_def unat_map_def transform_pde_def below_kernel_base)
  apply (simp add: mask_pd_bits_less )
  done

lemma opt_cap_page:
  "\<lbrakk> valid_idle s; pt_page_relation a pg x S s \<rbrakk>\<Longrightarrow>
   \<exists>attr f sz. opt_cap (a, unat (x && mask pt_bits >> 2)) (transform s) =
                 Some (cdl_cap.FrameCap False pg f sz (Fake attr) None)"
  unfolding pt_page_relation_def transform_def opt_cap_def slots_of_def
  apply clarsimp
  apply (frule transform_objects_kheap)
   apply (fastforce dest!: arch_obj_not_idle simp: not_idle_thread_def)
  apply (fastforce simp: object_slots_def transform_page_table_contents_def unat_map_def
                         transform_pte_def mask_pt_bits_less
                   split: ARM_A.pte.split_asm)
  done

lemma opt_cap_section:
  "\<lbrakk>valid_idle s;pd_section_relation a pg x s \<or> pd_super_section_relation a pg x s;
    ucast (x && mask pd_bits >> 2) \<notin> kernel_mapping_slots\<rbrakk>\<Longrightarrow>
  \<exists>attr f sz. (opt_cap (a, unat (x && mask pd_bits >> 2) ) (transform s))
    = Some (cdl_cap.FrameCap False pg f sz (Fake attr) None)"
  apply (erule disjE)
   apply (clarsimp simp: pd_section_relation_def opt_cap_def transform_def slots_of_def)
   apply (frule page_directory_at_rev)
   apply (frule(1) page_directory_not_idle)
   apply (clarsimp simp: transform_objects_def not_idle_thread_def page_directory_not_idle
                         restrict_map_def object_slots_def)
   apply (clarsimp simp: transform_page_directory_contents_def unat_map_def split:ARM_A.pte.split_asm | rule conjI)+
    apply (clarsimp simp: transform_page_directory_contents_def unat_map_def transform_pde_def below_kernel_base)
   apply (simp add: mask_pd_bits_less)
  apply (clarsimp simp: pd_super_section_relation_def opt_cap_def transform_def slots_of_def)
  apply (frule page_directory_at_rev)
  apply (frule(1) page_directory_not_idle)
  apply (clarsimp simp: transform_objects_def not_idle_thread_def page_directory_not_idle
                        restrict_map_def object_slots_def)
  apply (clarsimp simp: transform_page_directory_contents_def unat_map_def split:ARM_A.pte.split_asm | rule conjI)+
   apply (clarsimp simp: transform_page_directory_contents_def unat_map_def transform_pde_def below_kernel_base)
  apply (simp add: mask_pd_bits_less)
  done

lemma opt_object_page_table:
  "\<lbrakk>valid_idle s; kheap s a = Some (ArchObj (arch_kernel_obj.PageTable fun))\<rbrakk>
  \<Longrightarrow> cdl_objects (transform s) a =
        Some (cdl_object.PageTable PT (transform_page_table_contents fun))"
  apply (frule page_table_at_rev)
  apply (frule(1) page_table_not_idle)
  apply (clarsimp simp: transform_objects_def transform_def not_idle_thread_def restrict_map_def)
  done

lemma opt_object_page_directory:
  "\<lbrakk>valid_idle s; kheap s a = Some (ArchObj (arch_kernel_obj.PageDirectory fun))\<rbrakk>
  \<Longrightarrow> cdl_objects (transform s) a =
        Some (cdl_object.PageTable PD (transform_page_directory_contents fun))"
  apply (frule page_directory_at_rev)
  apply (frule(1) page_directory_not_idle)
  apply (clarsimp simp:transform_objects_def transform_def not_idle_thread_def restrict_map_def)
  done

lemma remove_cdt_pt_slot_exec:
  "\<lbrakk>dcorres dc \<top> Q (g ()) f;
   \<And>s. Q s\<longrightarrow> ( (\<lambda>s. mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s)) and valid_idle and pt_page_relation a pg_id ptr UNIV) s\<rbrakk>
    \<Longrightarrow> dcorres dc P Q
    (remove_parent (a ,aptr) >>= g) f"
  apply (rule corres_dummy_return_pr)
  apply (rule corres_guard_imp)
  apply (rule corres_split[OF dummy_remove_cdt_pt_slot])
    apply (rule_tac F="rv = ()" in corres_gen_asm)
    unfolding K_bind_def
    apply clarsimp
  apply (assumption)
  apply (simp|wp)+
  apply (drule_tac x = s in meta_spec)
  apply (clarsimp simp:pt_page_relation_def dest!:page_table_at_rev)
done

lemma remove_cdt_pd_slot_exec:
  "\<lbrakk>dcorres dc \<top> Q (g ()) f;
   \<And>s. Q s\<longrightarrow> ((\<lambda>s. mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s)) and valid_idle and page_directory_at a) s\<rbrakk>
    \<Longrightarrow> dcorres dc P Q
    (remove_parent (a ,aptr) >>= g) f"
  apply (rule corres_dummy_return_pr)
  apply (rule corres_guard_imp)
  apply (rule corres_split[OF dummy_remove_cdt_pd_slot])
    unfolding K_bind_def
  apply (simp|wp)+
done

lemma dcorres_set_pte_cap:
  "\<lbrakk> (x::word32) = (ptr && mask pt_bits >> 2);pte_cap = transform_pte a_pte\<rbrakk>\<Longrightarrow>
    dcorres dc \<top> (valid_idle and ko_at (ArchObj (arch_kernel_obj.PageTable fun)) a )
    (KHeap_D.set_cap (a, unat (ptr && mask pt_bits >> 2)) pte_cap)
    (KHeap_A.set_object a
      (ArchObj (arch_kernel_obj.PageTable (fun(ucast (ptr && mask pt_bits >> 2) := a_pte)))))"
  apply (simp add: KHeap_D.set_cap_def KHeap_A.set_object_def get_object_def gets_the_def gets_def bind_assoc)
  apply (rule dcorres_absorb_get_r)
  apply (rule dcorres_absorb_get_l)
  apply (clarsimp simp: obj_at_def opt_object_page_table assert_opt_def has_slots_def object_slots_def)
  apply (clarsimp simp: KHeap_D.set_object_def get_object_def in_monad simpler_modify_def put_def bind_def
                        corres_underlying_def update_slots_def return_def object_slots_def)
  apply (rule sym)
  apply (clarsimp simp: transform_def transform_current_thread_def)
  apply (rule ext)
  apply (clarsimp | rule conjI)+
   apply (frule page_table_at_rev)
   apply (frule(1) page_table_not_idle)
   apply (clarsimp simp: transform_objects_def not_idle_thread_def)
   apply (rule ext)
   apply (clarsimp simp: transform_page_table_contents_def transform_pte_def unat_map_def)
   apply (clarsimp simp: mask_pt_bits_less)
   apply (simp only: ucast_nat_def[symmetric])
   apply (drule word_of_nat_inj[rotated -1]; clarsimp simp: mask_pt_bits_less)
  apply (clarsimp simp: transform_objects_def restrict_map_def map_add_def)
  done

lemma dcorres_delete_cap_simple_set_pt:
  "dcorres dc \<top> ((\<lambda>s. mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s))
       and pt_page_relation (ptr && ~~ mask pt_bits) pg_id ptr UNIV
       and valid_idle and ko_at (ArchObj (arch_kernel_obj.PageTable fun)) (ptr && ~~ mask pt_bits))
    (delete_cap_simple (ptr && ~~ mask pt_bits, unat (ptr && mask pt_bits >> 2)))
    (set_pt (ptr && ~~ mask pt_bits) (fun(ucast (ptr && mask pt_bits >> 2) := ARM_A.pte.InvalidPTE)))"
  apply (simp add: delete_cap_simple_def set_pt_def gets_the_def gets_def bind_assoc get_object_def)
  apply (rule dcorres_absorb_get_l)
  apply (clarsimp simp: assert_def corres_free_fail
                 split: Structures_A.kernel_object.split_asm arch_kernel_obj.splits)
  apply (frule opt_cap_page)
    apply simp+
  apply (clarsimp simp: gets_def assert_opt_def ep_related_cap_def)
  apply (clarsimp simp: always_empty_slot_def gets_the_def gets_def bind_assoc)
  apply (rule remove_cdt_pt_slot_exec[where pg_id = pg_id])
   apply (rule corres_guard_imp)
     apply (rule dcorres_set_pte_cap)
      apply (simp add:transform_pte_def)+
  apply clarsimp
  apply simp
  done


lemma transform_page_directory_contents_upd:
  "ucast ((ptr::word32) && mask pd_bits >> 2) \<notin> kernel_mapping_slots
  \<Longrightarrow> (transform_page_directory_contents f)(unat (ptr && mask pd_bits >> 2) \<mapsto> transform_pde a_pde)
   =  transform_page_directory_contents (f(ucast (ptr && mask pd_bits >> 2) := a_pde))"
  apply (rule ext)
  apply (simp (no_asm) add: transform_page_directory_contents_def unat_map_def)
  apply (simp add: below_kernel_base)
  apply (clarsimp simp: mask_pd_bits_less | rule conjI)+
  apply (clarsimp simp: kernel_pde_mask_def kernel_mapping_slots_def)
  apply (simp only: ucast_nat_def[symmetric])
  apply (drule word_of_nat_inj[rotated -1]; clarsimp simp: mask_pt_bits_less)
  apply (rule unat_less_helper)
  apply (subst shiftr_div_2n_w; simp add:word_size)
  apply (rule word_div_mult, simp)
  apply (clarsimp simp: pt_bits_def pd_bits_def pageBits_def)
  apply (rule and_mask_less_size[where n = 14,simplified],simp add:word_size)
  done

lemma dcorres_set_pde_cap:
  "\<lbrakk> (x::word32) = (ptr && mask pd_bits >> 2);pde_cap = transform_pde a_pde; ucast (ptr && mask pd_bits >> 2) \<notin> kernel_mapping_slots\<rbrakk>\<Longrightarrow>
    dcorres dc \<top> (valid_idle and ko_at (ArchObj (arch_kernel_obj.PageDirectory fun)) a )
      (KHeap_D.set_cap (a, unat x) pde_cap)
      (KHeap_A.set_object a (ArchObj
                 (arch_kernel_obj.PageDirectory (fun(ucast x := a_pde)))))"
  apply (simp add: KHeap_D.set_cap_def KHeap_A.set_object_def gets_the_def gets_def bind_assoc)
  apply (rule dcorres_absorb_get_l)
  apply (clarsimp simp: obj_at_def opt_object_page_directory assert_opt_def has_slots_def object_slots_def)
  apply (clarsimp simp: KHeap_D.set_object_def get_object_def in_monad simpler_modify_def put_def
                        bind_def corres_underlying_def update_slots_def object_slots_def return_def)
  apply (clarsimp simp: transform_def transform_current_thread_def)
  apply (rule ext)
  apply (clarsimp | rule conjI)+
   apply (frule page_directory_at_rev)
   apply (frule(1) page_directory_not_idle)
   apply (clarsimp simp: transform_objects_def not_idle_thread_def)
   apply (rule sym)
   apply (erule transform_page_directory_contents_upd)
  apply (clarsimp simp: transform_objects_def restrict_map_def map_add_def)
  done

lemma dcorres_delete_cap_simple_set_pde:
  " ucast (ptr && mask pd_bits >> 2) \<notin> kernel_mapping_slots
    \<Longrightarrow>dcorres dc \<top> ((\<lambda>s. mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s))
    and (pd_pt_relation (ptr && ~~ mask pd_bits) oid ptr
         or pd_section_relation (ptr && ~~ mask pd_bits) oid ptr
         or pd_super_section_relation (ptr && ~~ mask pd_bits) oid ptr)
    and valid_idle and ko_at (ArchObj (arch_kernel_obj.PageDirectory fun)) (ptr && ~~ mask pd_bits))
             (delete_cap_simple (ptr && ~~ mask pd_bits, unat (ptr && mask pd_bits >> 2)))
             (set_pd (ptr && ~~ mask pd_bits) (fun(ucast (ptr && mask pd_bits >> 2) := ARM_A.pde.InvalidPDE)))"
  apply (simp add: delete_cap_simple_def set_pd_def gets_the_def gets_def bind_assoc)
  apply (rule dcorres_absorb_get_l)
  apply (clarsimp simp: assert_def corres_free_fail
                 split: Structures_A.kernel_object.split_asm arch_kernel_obj.splits)
  apply (erule disjE)
   apply (frule opt_cap_page_table, simp+)
   apply (clarsimp simp: gets_def assert_opt_def ep_related_cap_def)
   apply (clarsimp simp: always_empty_slot_def gets_the_def gets_def bind_assoc)
   apply (rule remove_cdt_pd_slot_exec)
    apply (rule corres_guard_imp)
      apply (rule dcorres_set_pde_cap)
        apply (simp add: transform_pte_def)+
       apply (clarsimp simp: pd_pt_relation_def transform_pde_def)+
   apply (rule page_directory_at_rev)
   apply simp
  apply (frule opt_cap_section,simp+)
  apply (clarsimp simp: gets_def assert_opt_def ep_related_cap_def)
  apply (clarsimp simp: always_empty_slot_def gets_the_def gets_def bind_assoc)
  apply (rule remove_cdt_pd_slot_exec)
   apply (rule corres_guard_imp)
     apply (rule dcorres_set_pde_cap)
       apply simp+
      apply (clarsimp simp: pd_pt_relation_def transform_pde_def obj_at_def a_type_def)+
  done

lemma dcorres_lookup_pd_slot:
  "is_aligned pd 14
  \<Longrightarrow> (cdl_lookup_pd_slot pd vptr =  transform_pd_slot_ref (lookup_pd_slot pd vptr))"
  apply (clarsimp simp:cdl_lookup_pd_slot_def
     transform_pd_slot_ref_def lookup_pd_slot_def)
  by (simp add:vaddr_segment_nonsense vaddr_segment_nonsense2)


lemma dcorres_delete_cap_simple_section:
  "dcorres dc \<top> (invs and pd_section_relation (lookup_pd_slot pd v && ~~ mask pd_bits) oid
                    (lookup_pd_slot pd v) and  K (is_aligned pd pd_bits \<and> v < kernel_base))
           (delete_cap_simple (cdl_lookup_pd_slot pd v))
           (store_pde (lookup_pd_slot pd v) ARM_A.pde.InvalidPDE)"
  apply (clarsimp simp: store_pde_def transform_pd_slot_ref_def lookup_pd_slot_def)
  apply (rule corres_gen_asm2)
  apply (subst dcorres_lookup_pd_slot, simp add: pd_bits_def pageBits_def)
  apply (clarsimp simp: transform_pd_slot_ref_def lookup_pd_slot_def)
  apply (rule corres_guard_imp)
    apply (rule corres_symb_exec_r)
       apply (rule dcorres_delete_cap_simple_set_pde[where oid = oid])
       apply (drule(1) less_kernel_base_mapping_slots)
       apply (simp add: lookup_pd_slot_def)
      apply wpsimp+
  apply fastforce
  done

lemma large_frame_range_helper:
  fixes t :: word32
  shows
  "t \<in> set [0 , 4 .e. 0x3C] \<Longrightarrow> t < 0x40"
  apply (clarsimp simp: upto_enum_step_def)
  apply (subgoal_tac "x < 0x10")
    apply (subst mult.commute)
    apply (subst shiftl_t2n[where n =2,simplified,symmetric])
    apply (rule shiftl_less_t2n[where m = 6 and n =2,simplified])
       apply simp+
    apply (rule le_less_trans)
    apply simp+
done

lemma zip_map_eqv:
  "(y, x) \<in> set (zip (map g xs) (map f xs)) = (\<exists>t. (y = g t \<and> x = f t \<and> t \<in> set xs))"
  apply (clarsimp simp:zip_map1 zip_map2)
  apply (rule iffI)
   apply (fastforce simp: in_set_zip)
  apply (clarsimp simp:set_zip_same)
  using imageI[where f ="(\<lambda>(a, b). (a, f b)) \<circ> (\<lambda>(x, y). (g x, y))",simplified]
  apply clarify
  apply (drule_tac x = t in meta_spec)
  apply (drule_tac x = t in meta_spec)
  apply (drule_tac x = "Id \<inter> (set xs) \<times> (set xs) " in meta_spec)
  apply clarsimp
done

lemma page_directory_address_eq:
  fixes ptr :: word32
  shows
  "\<lbrakk>is_aligned ptr 6; t \<in> set [0 , 4 .e. 0x3C]\<rbrakk> \<Longrightarrow> ptr && ~~ mask pd_bits = ptr + t && ~~ mask pd_bits"
  apply (drule large_frame_range_helper)
  using mask_lower_twice[where m = 14 and n = 6 and x= ptr,symmetric]
  apply (clarsimp simp:pd_bits_def pageBits_def)
  using mask_lower_twice[where m = 14 and n = 6 and x= "ptr+t",symmetric]
  apply (clarsimp simp:pd_bits_def pageBits_def)
  apply (subgoal_tac "(ptr && ~~ mask 6)  = (ptr + t && ~~ mask 6)")
    apply simp
  apply (frule is_aligned_neg_mask_eq)
    apply simp
  apply (drule_tac q = t in mask_out_add_aligned)
  apply (subst(asm) less_mask_eq [THEN mask_eq_x_eq_0[THEN iffD1]], erule order_less_le_trans)
  apply clarsimp+
done

lemma page_table_address_eq:
  fixes ptr :: word32
  shows
  "\<lbrakk>is_aligned ptr 6; t \<in> set [0 , 4 .e. 0x3C]\<rbrakk> \<Longrightarrow> ptr && ~~ mask pt_bits = ptr + t && ~~ mask pt_bits"
  apply (drule large_frame_range_helper)
  using mask_lower_twice[where m = 10 and n = 6 and x= ptr,symmetric]
  apply (clarsimp simp:pt_bits_def pageBits_def)
  using mask_lower_twice[where m = 10 and n = 6 and x= "ptr+t",symmetric]
  apply (clarsimp simp:pt_bits_def pageBits_def)
  apply (subgoal_tac "(ptr && ~~ mask 6)  = (ptr + t && ~~ mask 6)")
    apply simp
  apply (frule is_aligned_neg_mask_eq)
    apply simp
  apply (drule_tac q = t in mask_out_add_aligned)
  apply (subst(asm) less_mask_eq [THEN mask_eq_x_eq_0[THEN iffD1]], erule order_less_le_trans)
  apply clarsimp+
done

lemma mapM_Cons_split:
  "xs \<noteq> [] \<Longrightarrow> (mapM f xs) = (do y \<leftarrow> f (hd xs); ys \<leftarrow> mapM f (tl xs); return (y # ys) od)"
  by (clarsimp simp:neq_Nil_conv mapM_Cons)

lemma dcorres_store_invalid_pde_super_section:
  "dcorres dc \<top> (pd_super_section_relation (ptr && ~~ mask pd_bits) pg_id ptr
   and invs
   and K (ucast (ptr && mask pd_bits >> 2) \<notin> kernel_mapping_slots))
  (delete_cap_simple (ptr && ~~ mask pd_bits, unat (ptr && mask pd_bits >> 2)))
  (store_pde ptr ARM_A.pde.InvalidPDE)"
  apply simp
  apply (rule corres_gen_asm2)
  apply (rule corres_guard_imp)
    apply (simp add:store_pde_def)
    apply (rule corres_symb_exec_r)
       apply (rule dcorres_delete_cap_simple_set_pde[where oid = pg_id])
       apply simp
      apply (wp|simp)+
  apply (clarsimp simp: invs_def valid_mdb_def valid_state_def valid_pspace_def)
  done

lemma dcorres_store_invalid_pte:
  "dcorres dc \<top> (pt_page_relation (ptr && ~~ mask pt_bits) pg_id ptr UNIV
   and invs )
  (delete_cap_simple (ptr && ~~ mask pt_bits, unat (ptr && mask pt_bits >> 2)))
  (store_pte ptr ARM_A.pte.InvalidPTE)"
  apply (rule corres_guard_imp)
    apply (simp add:store_pte_def)
    apply (rule corres_symb_exec_r)
       apply (rule dcorres_delete_cap_simple_set_pt[where pg_id = pg_id])
      apply (wp|simp)+
  apply (clarsimp simp: invs_def valid_mdb_def valid_state_def valid_pspace_def)
  done

lemma dcorres_store_pde_non_sense:
  "dcorres dc \<top> (valid_idle and
     (\<lambda>s. \<exists>f. ko_at (ArchObj (arch_kernel_obj.PageDirectory f)) (slot && ~~ mask pd_bits) s
     \<and> (f (ucast (slot && mask pd_bits >> 2)) = pde)))
  (return a) (store_pde slot pde)"
  apply (simp add:store_pde_def)
  apply (simp add:get_pd_def bind_assoc set_object_def get_object_def set_pd_def gets_def)
  apply (rule dcorres_absorb_get_r)
  apply (clarsimp simp add:assert_def corres_free_fail
                  split:Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (rule dcorres_absorb_get_r)
  apply (clarsimp simp:corres_free_fail
                  split:Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (simp add:set_object_def put_def)
  apply (rule dcorres_absorb_get_r)
  apply (simp add:corres_underlying_def return_def transform_def transform_current_thread_def)
  apply (frule page_directory_at_rev)
  apply (drule(1) page_directory_not_idle[rotated])
  apply (rule ext)+
  apply (simp add:transform_objects_def not_idle_thread_def obj_at_def)
  done

lemma dcorres_store_pte_non_sense:
  "dcorres dc \<top> (valid_idle and
     (\<lambda>s. \<exists>f. ko_at (ArchObj (arch_kernel_obj.PageTable f)) (slot && ~~ mask pt_bits) s
      \<and> (f (ucast (slot && mask pt_bits >> 2)) = pte)))
  (return a) (store_pte slot pte)"
  apply (simp add:store_pte_def)
  apply (simp add:get_pt_def bind_assoc set_object_def get_object_def set_pt_def gets_def)
  apply (rule dcorres_absorb_get_r)
  apply (clarsimp simp add:assert_def corres_free_fail
                  split:Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (rule dcorres_absorb_get_r)
  apply (clarsimp simp:corres_free_fail
                  split:Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (simp add:set_object_def put_def)
  apply (rule dcorres_absorb_get_r)
  apply (simp add:corres_underlying_def return_def transform_def transform_current_thread_def)
  apply (frule page_table_at_rev)
  apply (drule(1) page_table_not_idle[rotated])
  apply (rule ext)+
  apply (simp add:transform_objects_def not_idle_thread_def obj_at_def)
  done

lemma store_pde_non_sense_wp:
  "\<lbrace>\<lambda>s. (\<exists>f. ko_at (ArchObj (arch_kernel_obj.PageDirectory f)) (slot && ~~ mask pd_bits) s
    \<and> (\<forall>slot\<in>set xs. f (ucast (slot && mask pd_bits >> 2)) = ARM_A.pde.InvalidPDE)) \<rbrace>
  store_pde x ARM_A.pde.InvalidPDE
   \<lbrace>\<lambda>r s. (\<exists>f. ko_at (ArchObj (arch_kernel_obj.PageDirectory f)) (slot && ~~ mask pd_bits) s
    \<and> (\<forall>slot\<in>set xs. f (ucast (slot && mask pd_bits >> 2)) = ARM_A.pde.InvalidPDE))\<rbrace>"
  apply (simp add:store_pde_def get_object_def get_pde_def set_pd_def set_object_def)
  apply wp
  apply (clarsimp simp:obj_at_def split:Structures_A.kernel_object.splits)
  done

lemma dcorres_store_invalid_pde_tail_super_section:
  "dcorres dc \<top> (valid_idle and
    (\<lambda>s. \<exists>f. ko_at (ArchObj (arch_kernel_obj.PageDirectory f)) (slot && ~~ mask pd_bits) s
    \<and> (\<forall>slot\<in> set slots. f (ucast (slot && mask pd_bits >> 2)) = ARM_A.pde.InvalidPDE))
    and K (\<forall>sl\<in> set slots. sl && ~~ mask pd_bits = slot && ~~ mask pd_bits))
  (return a)
  (mapM (swp store_pde ARM_A.pde.InvalidPDE) slots)"
  proof (induct slots arbitrary:a)
    case Nil
    show ?case
      by (simp add:mapM_Nil)
  next
  case (Cons x xs)
  show ?case
   apply (rule corres_guard_imp)
     apply (simp add:mapM_Cons dc_def[symmetric])
     apply (rule corres_dummy_return_l)
     apply (rule corres_split[OF dcorres_store_pde_non_sense])
       apply (rule corres_dummy_return_l)
       apply (rule corres_split[OF Cons.hyps[unfolded swp_def]])
         apply (rule corres_free_return[where P=\<top> and P'=\<top>])
        apply wp+
     apply simp
     apply (wp store_pde_non_sense_wp)
    apply simp
   apply (clarsimp simp:obj_at_def)
  done
qed

lemma store_pte_non_sense_wp:
  "\<lbrace>\<lambda>s. (\<exists>f. ko_at (ArchObj (arch_kernel_obj.PageTable f)) (slot && ~~ mask pt_bits) s
    \<and> (\<forall>slot\<in>set xs. f (ucast (slot && mask pt_bits >> 2)) = ARM_A.pte.InvalidPTE)) \<rbrace>
  store_pte x ARM_A.pte.InvalidPTE
   \<lbrace>\<lambda>r s. (\<exists>f. ko_at (ArchObj (arch_kernel_obj.PageTable f)) (slot && ~~ mask pt_bits) s
    \<and> (\<forall>slot\<in>set xs. f (ucast (slot && mask pt_bits >> 2)) = ARM_A.pte.InvalidPTE))\<rbrace>"
  apply (simp add:store_pte_def get_object_def get_pte_def set_pt_def set_object_def)
  apply wp
  apply (clarsimp simp:obj_at_def split: Structures_A.kernel_object.splits)
  done

lemma dcorres_store_invalid_pte_tail_large_page:
  "dcorres dc \<top> (valid_idle and
    (\<lambda>s. \<exists>f. ko_at (ArchObj (arch_kernel_obj.PageTable f)) (slot && ~~ mask pt_bits) s
    \<and> (\<forall>slot\<in> set slots. f (ucast (slot && mask pt_bits >> 2)) = ARM_A.pte.InvalidPTE))
    and K (\<forall>sl\<in> set slots. sl && ~~ mask pt_bits = slot && ~~ mask pt_bits))
  (return a)
  (mapM (swp store_pte ARM_A.pte.InvalidPTE) slots)"
  proof (induct slots arbitrary:a)
    case Nil
    show ?case
      by (simp add:mapM_Nil)
  next
  case (Cons x xs)
  show ?case
   apply (rule corres_guard_imp)
     apply (simp add:mapM_Cons dc_def[symmetric])
     apply (rule corres_dummy_return_l)
     apply (rule corres_split[OF dcorres_store_pte_non_sense])
       apply (rule corres_dummy_return_l)
       apply (rule corres_split[OF Cons.hyps[unfolded swp_def]])
         apply (rule corres_free_return[where P=\<top> and P'=\<top>])
        apply wp+
     apply simp
     apply (wp store_pte_non_sense_wp)
    apply simp
   apply (clarsimp simp:obj_at_def)
  done
qed

lemma and_mask_plus:
  "\<lbrakk>is_aligned ptr m; m \<le> n; n < 32; a < 2 ^m\<rbrakk>
   \<Longrightarrow> (ptr::word32) + a && mask n = (ptr && mask n) + a"
  apply (rule mask_eqI[where n = m])
   apply (simp add:mask_twice min_def)
    apply (simp add:is_aligned_add_helper)
    apply (subst is_aligned_add_helper[THEN conjunct1])
      apply (erule is_aligned_after_mask)
     apply simp
    apply simp
   apply simp
  apply (subgoal_tac "(ptr + a && mask n) && ~~ mask m
     = (ptr + a && ~~ mask m ) && mask n")
   apply (simp add:is_aligned_add_helper)
   apply (subst is_aligned_add_helper[THEN conjunct2])
     apply (simp add:is_aligned_after_mask)
    apply simp
   apply simp
  apply (simp add:word_bw_comms word_bw_lcs)
  done

lemma dcorres_unmap_large_section:
  "\<lbrakk>vmsz_aligned v ARMSuperSection; is_aligned ptr 14;
    v < kernel_base \<rbrakk>
  \<Longrightarrow> dcorres dc \<top>
     (invs and valid_pdpt_objs
           and (pd_super_section_relation ((lookup_pd_slot ptr v) && ~~ mask pd_bits)
               pg_id (lookup_pd_slot ptr v)))
     (delete_cap_simple (cdl_lookup_pd_slot ptr v))
     (mapM (swp store_pde ARM_A.pde.InvalidPDE)
           (map (\<lambda>x. x + lookup_pd_slot ptr v) [0 , 4 .e. 0x3C]))"
  supply is_aligned_neg_mask_eq[simp del] is_aligned_neg_mask_weaken[simp del]
  apply (subst mapM_Cons_split)
   apply (simp add:upto_enum_step_def upto_enum_def)
  apply (simp add:store_pte_def PageTableUnmap_D.unmap_page_def)
  apply (rule corres_dummy_return_l)
  apply (simp add: upto_enum_step_def transform_pt_slot_ref_def upto_enum_def hd_map_simp
                   dcorres_lookup_pd_slot)+
  apply (rule corres_guard_imp)
    apply (simp add:transform_pd_slot_ref_def)
    apply (rule corres_dummy_return_l)
    apply (rule corres_split[OF dcorres_store_invalid_pde_super_section[where pg_id = pg_id]])
      apply(rule corres_dummy_return_l)
      apply (rule_tac r'=dc in corres_split)
        apply (rule dcorres_store_invalid_pde_tail_super_section[where slot = ptr])
        apply (rule corres_free_return[where P=\<top> and P'=\<top>])
       apply wp+
    apply (wp store_pde_non_sense_wp)
   apply simp
  apply (simp add: hd_map_simp upto_enum_step_def upto_enum_def drop_map)
  apply (rule conjI)
   apply (rule less_kernel_base_mapping_slots)
    apply (simp add:pd_bits_def pageBits_def)+
  apply (rule conjI, fastforce) \<comment> \<open>valid_idle\<close>
  apply (rule conj_comms[THEN iffD1])
  apply (rule context_conjI)
   apply (clarsimp simp: tl_map)
   apply (clarsimp simp: field_simps)
   apply (subst mask_lower_twice[symmetric,where n = 6])
    apply (simp add:pd_bits_def pageBits_def)
   apply (subst is_aligned_add_helper)
     apply (erule(1) lookup_pd_slot_aligned_6)
    apply (simp add:upto_0_to_n)
    apply (rule word_less_power_trans_ofnat[where k = 2 and m = 6,simplified])
     apply simp
    apply simp
   apply (simp add: lookup_pd_slot_def is_aligned_neg_mask_eq
                    pd_shifting[unfolded pd_bits_def pageBits_def,simplified])
  apply (clarsimp simp:pd_super_section_relation_def obj_at_def)
  apply (simp add: lookup_pd_slot_pd[unfolded pd_bits_def pageBits_def,simplified]
                   is_aligned_neg_mask_eq pd_shifting[unfolded pd_bits_def pageBits_def,simplified])
  apply (rule ballI, drule (1) bspec)
  supply is_aligned_neg_mask2[simp del]
  apply (clarsimp simp: upto_0_to_n tl_map)
  apply (frule (1) lookup_pd_slot_aligned_6[unfolded pd_bits_def pageBits_def,simplified])
  apply (drule(1) valid_pdpt_objs_pdD)
  apply clarsimp
  apply (frule (1) lookup_pd_slot_aligned_6[unfolded pd_bits_def pageBits_def,simplified])
  apply (rename_tac pd rights attr ref s slot)
  apply (drule_tac x = "(ucast (lookup_pd_slot ptr v + of_nat slot * 4 && mask pd_bits >> 2))"
               and y = "ucast (lookup_pd_slot ptr v && mask pd_bits >> 2)"
                in valid_entriesD[rotated])
   apply (rule ccontr)
   apply simp
   apply (drule_tac x="ucast v" for v in arg_cong[where f = "ucast::(12 word\<Rightarrow>word32)"])
   apply (drule_tac x="ucast v" for v in arg_cong[where f = "\<lambda>x. shiftl x 2"])
   apply (subst (asm) ucast_ucast_len)
    apply (rule shiftr_less_t2n)
    apply (rule less_le_trans[OF and_mask_less'])
     apply (simp add:pd_bits_def pageBits_def)
    apply (simp add:pd_bits_def pageBits_def)
   apply (subst (asm) ucast_ucast_len)
    apply (rule shiftr_less_t2n)
    apply (rule less_le_trans[OF and_mask_less'])
     apply (simp add:pd_bits_def pageBits_def)
    apply (simp add:pd_bits_def pageBits_def)
   apply (simp add:shiftr_shiftl1)
   apply (subst (asm) is_aligned_neg_mask_eq[where n = 2])
    apply (erule is_aligned_andI1[OF aligned_add_aligned])
     apply (simp add: shiftl_t2n[symmetric,where n =2, simplified field_simps,simplified]
                      is_aligned_shiftl_self)
    apply simp
   apply (subst (asm) is_aligned_neg_mask_eq[where n = 2])
    apply (erule is_aligned_andI1[OF is_aligned_weaken])
    apply simp
   apply (subst (asm) and_mask_plus)
       apply (erule lookup_pd_slot_aligned_6, simp)
      apply (simp add:pd_bits_def pageBits_def)+
    apply (simp add:shiftl_t2n[symmetric,where n =2,simplified field_simps,simplified])
    apply (rule shiftl_less_t2n[where m = 6,simplified])
     apply (simp add:word_of_nat_less)
    apply simp
   apply simp
   apply (subgoal_tac "0 < (of_nat (slot * 4)::word32)")
    apply simp
   apply (rule le_less_trans[OF _ of_nat_mono_maybe[where y = 0]])
     apply fastforce
    apply simp
   apply fastforce
  apply (rule ccontr)
  apply (erule_tac x = "ucast (lookup_pd_slot ptr v + of_nat slot * 4 && mask pd_bits >> 2)"
                   in in_empty_interE)
   apply (rule non_invalid_in_pde_range)
   apply (simp add: pd_bits_def pageBits_def field_simps)
  apply (simp add: ucast_neg_mask)
  apply (simp add:is_aligned_shiftr)
  apply (rule arg_cong[where f = ucast])
  apply (rule shiftr_eq_neg_mask_eq)
  apply (simp add:shiftr_shiftr shiftr_over_and_dist)
  apply (subst aligned_shift')
     apply (simp add:shiftl_t2n[symmetric,where n =2,simplified field_simps,simplified])
     apply (rule shiftl_less_t2n[where m = 6,simplified])
      apply (simp add:word_of_nat_less)
     apply simp+
  done

lemma pt_page_relation_univ:
  "pt_page_relation a b c {ARMLargePage} s
  \<Longrightarrow> pt_page_relation a b c UNIV s"
  apply (clarsimp simp:pt_page_relation_def)
  apply (clarsimp split: ARM_A.pte.splits)
  done

lemma dcorres_unmap_large_page:
  "is_aligned ptr 6
    \<Longrightarrow> dcorres dc \<top> (invs and valid_pdpt_objs
          and pt_page_relation (ptr && ~~ mask pt_bits) pg_id ptr {ARMLargePage})
     (delete_cap_simple (transform_pt_slot_ref ptr))
     (mapM (swp store_pte ARM_A.pte.InvalidPTE) (map (\<lambda>x. x + ptr) [0 , 4 .e. 0x3C]))"
  supply is_aligned_neg_mask_eq[simp del]
         is_aligned_neg_mask_weaken[simp del]
  apply (subst mapM_Cons_split)
   apply (simp add:upto_enum_step_def upto_enum_def)
  apply (simp add: PageTableUnmap_D.unmap_page_def)
  apply (rule corres_dummy_return_l)
  apply (simp add:upto_enum_step_def transform_pt_slot_ref_def upto_enum_def hd_map_simp)+
  apply (rule corres_guard_imp)
    apply(rule corres_dummy_return_l)
    apply (rule corres_split[OF dcorres_store_invalid_pte[where pg_id = pg_id]])
      apply(rule corres_dummy_return_l)
      apply (rule_tac r'=dc in corres_split)
         apply (rule dcorres_store_invalid_pte_tail_large_page[where slot = ptr])
        apply (rule corres_return_trivial)
       apply wp+
    apply (wp store_pte_non_sense_wp)
   apply simp
  apply (clarsimp simp:unat_def pt_page_relation_univ)
  apply (rule conjI,fastforce)
  apply (rule conj_comms[THEN iffD1])
  apply (rule context_conjI)
   apply (clarsimp simp:tl_map drop_map)
   apply (simp add:field_simps)
   apply (subst mask_lower_twice[symmetric,where n = 6])
    apply (simp add:pt_bits_def pageBits_def)
   apply (subst is_aligned_add_helper)
     apply simp
    apply (simp add:upto_0_to_n)
    apply (rule word_less_power_trans_ofnat[where k = 2 and m = 6,simplified])
     apply simp
    apply simp
   apply simp
  apply (clarsimp simp:pt_page_relation_def obj_at_def)
  apply (drule(1) bspec)
  apply (clarsimp simp:tl_map drop_map upto_0_to_n)
  apply (simp add: field_simps)
  apply (drule(1) valid_pdpt_objs_ptD,clarify)
  apply (drule_tac x = "(ucast (ptr + of_nat x * 4 && mask pt_bits >> 2))"
               and y = "ucast (ptr && mask pt_bits >> 2)"
                in valid_entriesD[rotated])
   apply (rule ccontr)
   apply simp
   apply (drule_tac x="ucast v" for v in arg_cong[where f = "ucast::(word8\<Rightarrow>word32)"])
   apply (drule_tac x="ucast v" for v in arg_cong[where f = "\<lambda>x. shiftl x 2"])
   apply (subst (asm) ucast_ucast_len)
    apply (rule shiftr_less_t2n)
    apply (rule less_le_trans[OF and_mask_less'])
     apply (simp add:pt_bits_def pageBits_def)
    apply (simp add:pt_bits_def pageBits_def)
   apply (subst (asm) ucast_ucast_len)
    apply (rule shiftr_less_t2n)
    apply (rule less_le_trans[OF and_mask_less'])
     apply (simp add:pt_bits_def pageBits_def)
    apply (simp add:pt_bits_def pageBits_def)
   apply (simp add:shiftr_shiftl1)
   apply (subst (asm) is_aligned_neg_mask_eq[where n = 2])
    apply (erule is_aligned_andI1[OF aligned_add_aligned])
     apply (simp add: shiftl_t2n[symmetric, where n=2, simplified field_simps, simplified]
                      is_aligned_shiftl_self)
    apply simp
   apply (subst (asm) is_aligned_neg_mask_eq[where n = 2])
    apply (erule is_aligned_andI1[OF is_aligned_weaken])
    apply simp
   apply (subst (asm) and_mask_plus)
       apply simp
      apply (simp add:pt_bits_def pageBits_def)+
    apply (simp add:shiftl_t2n[symmetric,where n =2,simplified field_simps,simplified])
    apply (rule shiftl_less_t2n[where m = 6,simplified])
     apply (simp add:word_of_nat_less)
    apply simp
   apply simp
   apply (subgoal_tac "0 < (of_nat (x * 4)::word32)")
    apply simp
   apply (rule le_less_trans[OF _ of_nat_mono_maybe[where y = 0]])
     apply fastforce
    apply simp
   apply fastforce
  apply (clarsimp split:if_splits pte.split_asm)
   apply (rule ccontr)
   apply (erule_tac x = "ucast (ptr + of_nat x * 4 && mask pt_bits >> 2)" in in_empty_interE)
    apply (rule non_invalid_in_pte_range)
    apply simp
   apply (simp add: ucast_neg_mask)
   apply (rule arg_cong[where f = ucast])
   apply (rule shiftr_eq_neg_mask_eq)
   apply (simp add:shiftr_shiftr shiftr_over_and_dist)
   apply (subst aligned_shift')
      apply (simp add:shiftl_t2n[symmetric,where n =2,simplified field_simps,simplified])
      apply (rule shiftl_less_t2n[where m = 6,simplified])
       apply (simp add:word_of_nat_less)
      apply (simp+)[4]
  apply (simp add: is_aligned_shiftr)
  done

end

context begin interpretation Arch . (*FIXME: arch-split*)

lemma check_mapping_pptr_pt_relation:
  "\<lbrace>\<lambda>s. vmpage_size \<in> S\<rbrace> check_mapping_pptr w vmpage_size (Inl b)
            \<lbrace>\<lambda>r s. r \<longrightarrow> pt_page_relation (b && ~~ mask pt_bits) w b S s\<rbrace>"
  apply (simp add:check_mapping_pptr_def get_pte_def)
  apply (rule hoare_pre, wp get_pte_wp)
  apply (clarsimp simp: obj_at_def)
  apply (clarsimp simp: pt_page_relation_def)
  apply (simp split: ARM_A.pte.split_asm)
  done

lemma check_mapping_pptr_section_relation:
  "\<lbrace>\<top>\<rbrace> check_mapping_pptr w ARMSection (Inr (lookup_pd_slot rv' b))
   \<lbrace>\<lambda>rv s. rv \<longrightarrow>
    pd_section_relation (lookup_pd_slot rv' b && ~~ mask pd_bits) w (lookup_pd_slot rv' b) s\<rbrace>"
  apply (rule hoare_weaken_pre)
   apply (simp add:check_mapping_pptr_def)
   apply (wp get_pde_wp)
  apply (clarsimp simp: obj_at_def)
  apply (clarsimp simp: pd_section_relation_def pd_super_section_relation_def
                 split: ARM_A.pde.split_asm)
done

lemma check_mapping_pptr_super_section_relation:
  "\<lbrace>\<top>\<rbrace> check_mapping_pptr w ARMSuperSection (Inr (lookup_pd_slot rv' b))
   \<lbrace>\<lambda>rv s. rv \<longrightarrow> pd_super_section_relation (lookup_pd_slot rv' b && ~~ mask pd_bits) w (lookup_pd_slot rv' b) s\<rbrace>"
  apply (rule hoare_weaken_pre)
   apply (simp add:check_mapping_pptr_def)
   apply (wp get_pde_wp)
  apply (clarsimp simp: obj_at_def)
  apply (clarsimp simp: pd_section_relation_def pd_super_section_relation_def
                 split: ARM_A.pde.split_asm)
done

lemma cleanByVA_PoU_underlying_memory[wp]: " \<lbrace>\<lambda>m'. underlying_memory m' = m\<rbrace> cleanByVA_PoU w q \<lbrace>\<lambda>_ m'. underlying_memory m' = m\<rbrace>"
    apply(clarsimp simp: cleanByVA_PoU_def, wp)
done

lemma cdl_asid_table_transform:
  "cdl_asid_table (transform sa) x
  =  unat_map (Some \<circ> transform_asid_table_entry \<circ> arm_asid_table (arch_state sa)) x"
  by (simp add:transform_def transform_asid_table_def)

lemma dcorres_find_pd_for_asid:
  "dcorres ( dc \<oplus> (=)) \<top> valid_idle
    (cdl_find_pd_for_asid (transform_asid a, b))
    (find_pd_for_asid a)"
  apply (simp add:cdl_find_pd_for_asid_def find_pd_for_asid_def transform_asid_def)
  apply (simp add:liftE_bindE assertE_assert)
  apply (rule dcorres_symb_exec_r[where Q' = "\<lambda>r. valid_idle"])
    apply (simp add:gets_def)
    apply (rule dcorres_get)
    apply (clarsimp simp:cdl_asid_table_transform liftE_bindE
      transform_asid_table_entry_def split:option.splits)
    apply (simp add:get_asid_pool_def get_object_def gets_the_def gets_def bind_assoc)
    apply (rule dcorres_get)
    apply (clarsimp simp: obj_at_def opt_object_asid_pool
                          assert_opt_def has_slots_def opt_cap_def slots_of_def assert_def
                          corres_free_fail
                   split: Structures_A.kernel_object.splits arch_kernel_obj.splits)
    apply (clarsimp simp:transform_asid_pool_contents_def
      object_slots_def transform_asid_pool_entry_def split:option.splits)
    apply (rule corres_guard_imp[OF dcorres_returnOk])
    apply (simp|wp)+
  done

lemma unat_pd_bits_less_4096_helper[simp]:
  "\<And>x. unat (x && mask pd_bits >> 2 :: word32) < 4096"
  apply (rule order_less_le_trans[where y="2^12"])
   apply (rule unat_less_power[rotated])
    apply (rule shiftr_less_t2n)
    apply (rule order_less_le_trans, rule and_mask_less')
     apply (simp_all add: pd_bits_def pageBits_def word_bits_conv)
  done

lemma pd_at_cdl_pd_at:
  "\<lbrakk>valid_idle s ; ucast (ptr && mask pd_bits >> 2) \<notin> kernel_mapping_slots;
  kheap s (ptr && ~~ mask pd_bits) = Some (ArchObj (arch_kernel_obj.PageDirectory fun))\<rbrakk>
  \<Longrightarrow> opt_cap (transform_pd_slot_ref ptr) (transform s) =
  Some (transform_pde (fun (of_nat (unat (ptr && mask pd_bits >> 2)))))"
  apply (clarsimp simp:opt_cap_def transform_pd_slot_ref_def transform_def
    slots_of_def transform_objects_def pred_tcb_def2
    valid_idle_def restrict_map_def object_slots_def
    transform_page_directory_contents_def unat_map_def
     dest!:get_tcb_SomeD split:option.splits)
  apply (simp add: below_kernel_base)
  apply (auto simp:transform_page_directory_contents_def unat_map_def)
  done

lemma dcorres_get_pde_helper:
  "ucast (ptr && mask pd_bits >> 2) \<notin> kernel_mapping_slots
  \<Longrightarrow> dcorres (\<lambda>r r'. r = transform_pde r') \<top> valid_idle
  (cdl_get_pde (transform_pd_slot_ref ptr)) (get_pde ptr)"
  apply (simp add:cdl_get_pde_def
    get_pde_def gets_def gets_the_def
    get_pd_def get_object_def bind_assoc)
  apply (rule dcorres_absorb_get_l)
  apply (rule dcorres_absorb_get_r)
  apply (clarsimp simp:assert_def assert_opt_def
    corres_free_fail
    split:Structures_A.kernel_object.splits
    arch_kernel_obj.splits)
  apply (drule(2) pd_at_cdl_pd_at)
  apply (simp add:ucast_nat_def)
  done

lemma dcorres_get_pde:
  "dcorres (\<lambda>r r'. r = transform_pde r') \<top>
  (valid_idle and K (ucast (ptr && mask pd_bits >> 2) \<notin> kernel_mapping_slots))
  (cdl_get_pde (transform_pd_slot_ref ptr)) (get_pde ptr)"
  apply (rule corres_guard_imp[OF corres_gen_asm2])
  apply (rule dcorres_get_pde_helper)
  apply simp+
  done

lemma valid_pde_pt_at:
  "\<lbrakk>valid_pde (ARM_A.pde.PageTablePDE word1 se word2) s \<and> pspace_aligned s\<rbrakk>
  \<Longrightarrow> (ptrFromPAddr word1, unat ((vaddr >> 12) && 0xFF)) =
  transform_pt_slot_ref (ptrFromPAddr word1 + ((vaddr >> 12) && 0xFF << 2))"
  apply (clarsimp simp :transform_pt_slot_ref_def )
  apply (drule(1) pt_aligned)
  apply (simp add:vaddr_segment_nonsense3
    vaddr_segment_nonsense4)
  apply (subst shiftl_shiftr_id)
    apply simp
   apply (rule le_less_trans[OF word_and_le1])
   apply simp
  apply simp
  done

lemma dcorres_lookup_pt_slot:
  "dcorres (dc \<oplus> (\<lambda>r r'. r = transform_pt_slot_ref r')) \<top>
    (valid_vspace_objs and \<exists>\<rhd> (lookup_pd_slot v a && ~~ mask pd_bits) and pspace_aligned
       and valid_idle and K(is_aligned v pd_bits)
       and K (ucast (lookup_pd_slot v a && mask pd_bits >> 2) \<notin> kernel_mapping_slots))
    (cdl_lookup_pt_slot v a)
    (lookup_pt_slot v a)"
  apply (simp add:cdl_lookup_pt_slot_def lookup_pt_slot_def)
  apply (rule corres_guard_imp)
  apply (rule_tac F =" is_aligned v 14" in corres_gen_asm2)
     apply (clarsimp simp:dcorres_lookup_pd_slot)
     apply (rule corres_splitEE[OF corres_liftE_rel_sum[THEN iffD2,OF dcorres_get_pde] ])
      apply (case_tac rv')
         prefer 2
         apply (simp add:transform_pde_def)
         apply (rule corres_returnOk)
         apply (erule valid_pde_pt_at)
        apply (simp add:transform_pde_def)+
       apply (rule hoare_TrueI)
    apply (wp|simp)+
  apply (simp add:pd_bits_def pageBits_def)
  done

lemma find_pd_for_asid_kernel_mapping_help:
  "\<lbrace>pspace_aligned and valid_vspace_objs and K (v<kernel_base) \<rbrace> find_pd_for_asid a
   \<lbrace>\<lambda>rv s. ucast (lookup_pd_slot rv v && mask pd_bits >> 2) \<notin> kernel_mapping_slots \<rbrace>,-"
  apply (rule hoare_gen_asmE)
  apply (rule hoare_strengthen_postE_R)
   apply (rule find_pd_for_asid_aligned_pd_bits)
   apply simp
  apply (rule less_kernel_base_mapping_slots)
  apply simp+
  done

lemma dcorres_might_throw:
  "\<lbrakk>\<And>s. \<lbrace>(=) s\<rbrace> b \<lbrace>\<lambda>r. (=) s\<rbrace>\<rbrakk> \<Longrightarrow> dcorres (dc \<oplus> dc) \<top> \<top> might_throw (throw_on_false a b)"
  apply (simp add: liftE_bindE unlessE_def
    might_throw_def throw_on_false_def split:if_splits)
  apply (rule corres_symb_exec_r)
     apply (clarsimp split:if_splits)
     apply (intro conjI impI)
      apply (rule corres_alternate1)
      apply (simp add:returnOk_def)
     apply (rule corres_alternate2)
     apply simp
    apply (wp hoare_TrueI)
   apply simp
  apply simp
  done

lemma corres_dummy_returnOk_l:
  "dcorres cr P P' (f >>=E returnOk) g \<Longrightarrow> dcorres cr P P' f g"
  by (simp add:liftE_def)

lemma dcorres_unmap_page:
  notes swp_apply[simp del]
  shows "dcorres dc \<top> (invs and valid_pdpt_objs and
                  valid_cap (cap.ArchObjectCap (arch_cap.PageCap dev pg fun vmpage_size (Some (a, v)))))
              (PageTableUnmap_D.unmap_page (transform_asid a,v) pg (pageBitsForSize vmpage_size))
              (ARM_A.unmap_page vmpage_size a v pg)"
  apply (rule dcorres_expand_pfx)
  apply (clarsimp simp:valid_cap_def)
  apply (case_tac vmpage_size)
  \<comment> \<open>ARMSmallPage\<close>
     apply (simp add:ARM_A.unmap_page_def bindE_assoc mapM_x_singleton
       PageTableUnmap_D.unmap_page_def cdl_page_mapping_entries_def)
     apply (rule corres_guard_imp)
       apply (rule_tac P = "\<lambda>x. x = transform s'" and P' = "(=) s'"
                       in corres_split_catch [where f = dc and E = dc and E' =dc])
          apply (rule corres_guard_imp)
            apply (rule_tac corres_splitEE[OF dcorres_find_pd_for_asid,simplified])
              apply (simp_all add: cdl_page_mapping_entries_def liftE_distrib
                                   pageBitsForSize_def bindE_assoc mapM_x_singleton)
          apply (rule corres_splitEE[OF dcorres_lookup_pt_slot])
            apply (rule corres_splitEE)
               apply (rule dcorres_might_throw)
               apply wp
              apply (rule corres_dummy_returnOk_l)
              apply (rule corres_splitEE)
                 apply (simp add:transform_pt_slot_ref_def)
                 apply (rule dcorres_store_invalid_pte[where pg_id = pg])
                apply (simp add:liftE_distrib[symmetric] returnOk_liftE)
                apply (rule dcorres_symb_exec_r)
                  apply (rule dcorres_flush_page)
                 apply (wp do_machine_op_wp | clarsimp)+
            apply (simp add: imp_conjR)
            apply ((wp check_mapping_pptr_pt_relation | wp (once) hoare_drop_imps)+)[1]
           apply (simp | wp lookup_pt_slot_inv)+
        apply (simp add: dc_def
               | wp lookup_pt_slot_inv find_pd_for_asid_kernel_mapping_help
               | rule conjI | clarify)+

   \<comment> \<open>ARMLargePage\<close>
    apply (simp add: ARM_A.unmap_page_def bindE_assoc mapM_x_singleton
                     PageTableUnmap_D.unmap_page_def cdl_page_mapping_entries_def)
    apply (rule corres_guard_imp)
      apply (rule_tac P = "\<lambda>x. x = transform s'" and P' = "(=) s'"
                      in corres_split_catch [where f = dc and E = dc and E' =dc])
         apply (rule corres_guard_imp)
           apply (rule_tac corres_splitEE[OF dcorres_find_pd_for_asid,simplified])
             apply (simp_all add: cdl_page_mapping_entries_def liftE_distrib
                                  pageBitsForSize_def bindE_assoc mapM_x_singleton)
         apply (rule corres_splitEE[OF dcorres_lookup_pt_slot])
           apply (rule corres_splitEE)
              apply (rule dcorres_might_throw)
              apply wp
             apply (rule dcorres_symb_exec_rE)
               apply (rule corres_dummy_returnOk_l)
               apply (rule corres_splitEE)
                  apply simp
                  apply (rename_tac x)
                  apply (rule_tac F = "is_aligned x 6" in corres_gen_asm2)
                  apply (erule dcorres_unmap_large_page[where pg_id = pg])
                 apply (simp add:liftE_distrib[symmetric] returnOk_liftE)
                 apply (rule dcorres_symb_exec_r)
                   apply (rule dcorres_flush_page[unfolded dc_def])
                  apply (wp do_machine_op_wp | clarsimp)+
           apply (simp add: imp_conjR is_aligned_mask)
           apply (rule hoare_vcg_conj_lift)
            apply (wp hoare_drop_imps)[1]
           apply (rule hoare_vcg_conj_lift)
            apply (wp hoare_drop_imps)[1]
           apply (rule hoare_strengthen_post[OF check_mapping_pptr_pt_relation])
           apply fastforce
          apply (simp | wp lookup_pt_slot_inv)+
       apply (simp add: dc_def
              | wp lookup_pt_slot_inv hoare_drop_imps find_pd_for_asid_kernel_mapping_help
              | safe)+

  \<comment> \<open>Section\<close>
   apply (simp add:ARM_A.unmap_page_def bindE_assoc mapM_x_singleton
     PageTableUnmap_D.unmap_page_def cdl_page_mapping_entries_def)
   apply (rule corres_guard_imp)
     apply (rule_tac P = "\<lambda>x. x = transform s'" and P' = "(=) s'"
                     in corres_split_catch [where f = dc and E = dc and E' =dc])
        apply (rule corres_guard_imp)
          apply (rule_tac corres_splitEE[OF dcorres_find_pd_for_asid,simplified])
            apply (simp_all add: cdl_page_mapping_entries_def liftE_distrib
                                 pageBitsForSize_def bindE_assoc mapM_x_singleton)
        apply (rule corres_splitEE)
           apply (rule dcorres_might_throw)
           apply wp
          apply (rule corres_dummy_returnOk_l)
          apply (rule corres_splitEE)
             apply simp
             apply (rule dcorres_delete_cap_simple_section[where oid = pg])
            apply (simp add:liftE_distrib[symmetric] returnOk_liftE)
            apply (rule dcorres_symb_exec_r)
              apply (rule dcorres_flush_page[unfolded dc_def])
             apply (wp do_machine_op_wp | clarsimp)+
        apply (simp add: imp_conjR)
        apply ((wp check_mapping_pptr_section_relation | wp (once) hoare_drop_imps)+)[1]
       apply (simp | wp lookup_pt_slot_inv)+
     apply (simp add: dc_def
            | wp lookup_pt_slot_inv find_pd_for_asid_kernel_mapping_help
            | safe)+

  \<comment> \<open>SuperSection\<close>
  apply (simp add: ARM_A.unmap_page_def bindE_assoc mapM_x_singleton
                   PageTableUnmap_D.unmap_page_def cdl_page_mapping_entries_def)
  apply (rule corres_guard_imp)
    apply (rule_tac P = "\<lambda>x. x = transform s'" and P' = "(=) s'"
                    in corres_split_catch [where f = dc and E = dc and E' =dc])
       apply (rule corres_guard_imp)
         apply (rule_tac corres_splitEE[OF dcorres_find_pd_for_asid,simplified])
           apply (simp_all add: cdl_page_mapping_entries_def liftE_distrib
                                pageBitsForSize_def bindE_assoc mapM_x_singleton)
       apply (rule corres_splitEE)
          apply (rule dcorres_might_throw)
          apply wp
         apply (rule dcorres_symb_exec_rE)
           apply (rule corres_dummy_returnOk_l)
           apply (rule corres_splitEE)
              apply simp
              apply (rule_tac F = "is_aligned pd 14" in corres_gen_asm2)
              apply (erule(2) dcorres_unmap_large_section[where pg_id = pg])
             apply (simp add:liftE_distrib[symmetric] returnOk_liftE)
             apply (rule dcorres_symb_exec_r)
               apply (rule dcorres_flush_page[unfolded dc_def])
              apply (wp do_machine_op_wp | clarsimp)+
       apply (simp add: imp_conjR is_aligned_mask)
       apply (rule hoare_vcg_conj_lift)
        apply (wp hoare_drop_imps)[1]
       apply (rule hoare_vcg_conj_lift)
        apply (wp hoare_drop_imps)[1]
       apply (rule hoare_vcg_conj_lift)
        apply (rule hoare_strengthen_post[OF check_mapping_pptr_super_section_relation])
        apply clarsimp
       apply (simp add:is_aligned_mask[symmetric] dc_def
              | wp lookup_pt_slot_inv hoare_drop_imps find_pd_for_asid_kernel_mapping_help
              | safe)+
  done


lemma asid_table_transform:
  "cdl_asid_table (transform s) slot =
   unat_map (Some \<circ> transform_asid_table_entry \<circ> arm_asid_table (arch_state s)) slot"
  apply (simp add:transform_def transform_asid_table_def transform_asid_table_entry_def)
  done

lemma update_restart_pc_dcorres: "dcorres dc P P' (return ()) (update_restart_pc t)"
  apply (monad_eq simp: update_restart_pc_def as_user_def gets_the_def
                        getRegister_def setRegister_def set_object_def get_object_def
                        corres_underlying_def return_def select_f_def)
  apply (clarsimp simp: get_tcb_def split: option.splits kernel_object.splits)
  apply (clarsimp simp: transform_def transform_objects_def)
  apply (intro impI conjI)
    apply (rule ext)
    apply (clarsimp simp: map_add_def restrict_map_def transform_tcb_def
                          transform_full_intent_def cap_register_def capRegister_def
                          get_tcb_message_info_def msg_info_register_def msgInfoRegister_def
                          get_tcb_mrs_def msgRegisters_A_unfold
                          get_ipc_buffer_words_def transform_current_thread_def
                          ARM.faultRegister_def ARM.nextInstructionRegister_def
                   split: option.splits)+
  done

lemma dcorres_finalise_cap:
  "can_fast_delete (transform_cap cap) \<Longrightarrow>
   dcorres (\<lambda>_ r'. r' = (cap.NullCap, cap.NullCap)) \<top>
     (invs and valid_cap cap and valid_pdpt_objs and cte_wp_at ((=) cap) slot)
     (CSpace_D.finalise_cap (transform_cap cap))
     (CSpace_A.finalise_cap cap final)"
  apply (case_tac cap; simp add: can_fast_delete_def)
  apply (rename_tac arch_cap)
  apply (case_tac arch_cap; simp)
  apply (clarsimp simp: arch_finalise_cap_def transform_mapping_def split: option.splits)
  apply (rule corres_dummy_return_l)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF dcorres_unmap_page])
      apply (rule iffD2[OF corres_return[where P=\<top> and P'=\<top>]])
      apply clarsimp
     apply wpsimp+
  apply simp
  done

lemma set_cdt_modify:
  "set_cdt c = modify (\<lambda>s. s \<lparr> cdt := c \<rparr>)"
  by (simp add: set_cdt_def modify_def)

lemma no_cdt_loop_mloop:
  "no_mloop m \<Longrightarrow> m x \<noteq> Some x"
  apply (rule notI)
  apply (simp add: no_mloop_def cdt_parent_rel_def del: split_paired_All)
  apply (drule_tac x=x in spec)
  apply (erule notE, rule r_into_trancl)
  apply (simp add: is_cdt_parent_def)
  done

lemma set_cdt_list_modify:
  "set_cdt_list c = modify (\<lambda>s. s \<lparr> cdt_list := c \<rparr>)"
  by (simp add: set_cdt_list_def modify_def)

lemma corres_assert_rhs:
  "(F \<Longrightarrow> corres_underlying sr False False r P P' f (g ()))
    \<Longrightarrow> corres_underlying sr False False r P (\<lambda>s. F \<longrightarrow> P' s) f (assert F >>= g)"
  by (cases F, simp_all add: corres_fail)

lemma underlying_memory_irq_state_independent[intro!, simp]:
  "underlying_memory (s\<lparr>irq_state := f (irq_state s)\<rparr>)
   = underlying_memory s"
  by simp

lemma get_ipc_buffer_words_irq_state_independent[intro!, simp]:
  "get_ipc_buffer_words (s\<lparr>irq_state := f (irq_state s)\<rparr>)
   = get_ipc_buffer_words s"
  apply (rule ext, rule ext)
  apply (simp add: get_ipc_buffer_words_def)
  apply (case_tac "tcb_ipcframe x", simp_all)
  apply (clarsimp split: ARM_A.arch_cap.splits)
  apply (rule arg_cong[where f=the])
  apply (rule evalMonad_mapM_cong)
    apply (simp add: evalMonad_def)
    apply safe
      apply ((clarsimp simp: loadWord_def bind_def gets_def get_def return_def in_monad)+)[3]
   apply (rule loadWord_inv)
  apply (rule df_loadWord)
  done

lemma get_tcb_mrs_irq_state_independent[intro!, simp]:
  "get_tcb_mrs (s\<lparr>irq_state := f (irq_state s)\<rparr>)
   = get_tcb_mrs s"
  by (auto simp: get_tcb_mrs_def)

lemma transform_full_intent_irq_state_independent[intro!, simp]:
  "transform_full_intent (s\<lparr>irq_state := f (irq_state s)\<rparr>)
   = transform_full_intent s"
  by (rule ext, rule ext, simp add: transform_full_intent_def)

lemma transform_tcb_irq_state_independent[intro!, simp]:
  "transform_tcb (s\<lparr>irq_state := f (irq_state s)\<rparr>)
   = transform_tcb s"
  by (rule ext, rule ext, simp add: transform_tcb_def)

lemma transform_object_irq_state_independent[intro!, simp]:
  "transform_object (s \<lparr> irq_state := f (irq_state s) \<rparr>)
   = transform_object s"
  by (rule ext, rule ext,
      simp add: transform_object_def
           cong: option.case_cong
           split: Structures_A.kernel_object.splits)

lemma transform_work_units_independent[intro!, simp]:
  "transform (s \<lparr> work_units_completed := f (work_units_completed s) \<rparr>)
   = transform s"
  apply (simp add: transform_def transform_current_thread_def transform_objects_def transform_cdt_def transform_asid_table_def)
  done

lemma transform_work_units_then_irq_state_independent[intro!, simp]:
  "transform (s \<lparr> work_units_completed := g (work_units_completed s) \<rparr>
                \<lparr> machine_state := machine_state s \<lparr> irq_state := f (irq_state (machine_state s)) \<rparr>\<rparr>) =
   transform s"
  apply (simp add: transform_def transform_current_thread_def transform_objects_def transform_cdt_def transform_asid_table_def)
  done

lemma throw_or_return_preemption_corres:
  "dcorres (dc \<oplus> dc) P P'
       (Monads_D.throw \<sqinter> returnOk ())
       preemption_point"
  apply (simp add: preemption_point_def)
  apply (auto simp: preemption_point_def o_def gets_def liftE_def whenE_def getActiveIRQ_def
                    corres_underlying_def select_def bind_def get_def bindE_def select_f_def modify_def
                    alternative_def throwError_def returnOk_def return_def lift_def
                    put_def do_machine_op_def
                    update_work_units_def wrap_ext_bool_det_ext_ext_def work_units_limit_def
                    work_units_limit_reached_def OR_choiceE_def reset_work_units_def mk_ef_def
           split: option.splits kernel_object.splits)
  done

declare rec_del.simps[simp del]

lemma select_pick_corres_asm:
  "\<lbrakk> x \<in> S; corres_underlying sr nf nf' r P Q (f x) g \<rbrakk>
    \<Longrightarrow> corres_underlying sr nf nf' r P Q (select S >>= f) g"
  by (drule select_pick_corres[where x=x and S=S], simp)

lemma invs_valid_idle_strg:
  "invs s \<longrightarrow> valid_idle s"
  by auto

lemma preemption_point_idle_thread[wp]: "\<lbrace> \<lambda>s. P (idle_thread s) \<rbrace> preemption_point \<lbrace> \<lambda>_ s. P (idle_thread s) \<rbrace>"
  apply (simp add: preemption_point_def OR_choiceE_def)
  apply (wpsimp wp: hoare_drop_imps dxo_wp_weak[where P="\<lambda>s. P (idle_thread s)"])
  done

lemma rec_del_idle_thread[wp]:
  "\<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> rec_del args \<lbrace>\<lambda>rv s::'a::state_ext state. P (idle_thread s)\<rbrace>"
  by (wp rec_del_preservation)+

lemma nat_split_conv_to_if:
  "(case n of 0 \<Rightarrow> a | Suc nat' \<Rightarrow> f nat') = (if n = 0 then a else f (n - 1))"
  by (auto split: nat.splits)

end

end
