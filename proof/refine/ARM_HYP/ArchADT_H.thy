(*
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter \<open>Abstract datatype for the executable specification - architecture-specific\<close>

theory ArchADT_H
  imports ADT_H
begin

context Arch begin arch_global_naming

named_theorems ADT_H_assms

definition vm_rights_of :: "vmrights \<Rightarrow> rights set" where
  "vm_rights_of x \<equiv> case x of VMKernelOnly \<Rightarrow> vm_kernel_only
                    | VMReadOnly \<Rightarrow> vm_read_only
                    | VMReadWrite \<Rightarrow> vm_read_write"

lemma vm_rights_of_vmrights_map_id[ADT_H_assms, simp]:
  "rs \<in> valid_vm_rights \<Longrightarrow> vm_rights_of (vmrights_map rs) = rs"
  by (auto simp: vm_rights_of_def vmrights_map_def valid_vm_rights_def
                 vm_read_write_def vm_read_only_def vm_kernel_only_def)

definition
  absPageTable :: "(word32 \<rightharpoonup> Structures_H.kernel_object) \<Rightarrow> obj_ref \<Rightarrow>
                  9 word \<Rightarrow> ARM_HYP_A.pte"
  where
  "absPageTable h a \<equiv> %offs.
   case (h (a + (ucast offs << 3))) of
     Some (KOArch (KOPTE (ARM_HYP_H.InvalidPTE))) \<Rightarrow> ARM_HYP_A.InvalidPTE
   | Some (KOArch (KOPTE (ARM_HYP_H.LargePagePTE p c xn rights))) \<Rightarrow>
       if is_aligned offs 4 then
         ARM_HYP_A.LargePagePTE p
           {x. c & x=PageCacheable | xn & x=XNever}
           (vm_rights_of rights)
       else ARM_HYP_A.InvalidPTE
   | Some (KOArch (KOPTE (ARM_HYP_H.SmallPagePTE p c xn rights))) \<Rightarrow>
       ARM_HYP_A.SmallPagePTE p {x. c & x=PageCacheable |
                                        xn & x=XNever} (vm_rights_of rights)"

definition
  absPageDirectory :: "(word32 \<rightharpoonup> Structures_H.kernel_object) \<Rightarrow> obj_ref \<Rightarrow>
                      11 word \<Rightarrow>  ARM_HYP_A.pde"
  where
  "absPageDirectory h a \<equiv> %offs.
   case (h (a + (ucast offs << 3))) of
     Some (KOArch (KOPDE (ARM_HYP_H.InvalidPDE))) \<Rightarrow> ARM_HYP_A.InvalidPDE
   | Some (KOArch (KOPDE (ARM_HYP_H.PageTablePDE p))) \<Rightarrow>
       ARM_HYP_A.PageTablePDE p
   | Some (KOArch (KOPDE (ARM_HYP_H.SectionPDE p c xn rights))) \<Rightarrow>
       ARM_HYP_A.SectionPDE p {x. c & x=PageCacheable |
                                      xn & x=XNever} (vm_rights_of rights)
   | Some (KOArch (KOPDE (ARM_HYP_H.SuperSectionPDE p c xn rights))) \<Rightarrow>
       if is_aligned offs 4 then
         ARM_HYP_A.SuperSectionPDE p
           {x. c & x=PageCacheable
             | xn & x=XNever}
           (vm_rights_of rights)
       else ARM_HYP_A.InvalidPDE"

definition absVGIC :: "gicvcpuinterface \<Rightarrow> gic_vcpu_interface" where
  "absVGIC v \<equiv> case v of
    VGICInterface hcr vmcr apr lr \<Rightarrow> gic_vcpu_interface.make hcr vmcr apr lr"

lemma absVGIC_eq[simp]:
  "absVGIC (vgic_map vgic) = vgic"
  by (simp add: vgic_map_def absVGIC_def gic_vcpu_interface.make_def)

(* Can't pull the whole heap off at once, start with arch specific stuff.*)
definition
  absHeapArch :: "(word32 \<rightharpoonup> Structures_H.kernel_object) \<Rightarrow> word32
                 \<Rightarrow> arch_kernel_object \<rightharpoonup> arch_kernel_obj"
  where
  "absHeapArch h a \<equiv> %ako.
   (case ako of
     KOASIDPool (ARM_HYP_H.ASIDPool ap) \<Rightarrow>
       Some (ARM_HYP_A.ASIDPool (\<lambda>w. ap (ucast w)))
   | KOPTE _ \<Rightarrow>
       if is_aligned a pt_bits then Some (PageTable (absPageTable h a))
       else None
   | KOPDE _ \<Rightarrow>
       if is_aligned a pd_bits then Some (PageDirectory (absPageDirectory h a))
       else None
   | KOVCPU (VCPUObj tcb vgic regs vppimask) \<Rightarrow>
       Some (VCPU \<lparr> vcpu_tcb    = tcb,
                    vcpu_vgic   = absVGIC vgic,
                    vcpu_regs   = regs,
                    vcpu_vppi_masked = vppimask \<rparr>))"

fun ArchCapabilityMap :: "arch_capability \<Rightarrow> cap" where
  "ArchCapabilityMap (arch_capability.ASIDPoolCap x y) =
     cap.ArchObjectCap (arch_cap.ASIDPoolCap x y)"
| "ArchCapabilityMap (arch_capability.ASIDControlCap) =
     cap.ArchObjectCap (arch_cap.ASIDControlCap)"
| "ArchCapabilityMap (arch_capability.PageCap d word rghts sz data) =
     cap.ArchObjectCap (arch_cap.PageCap d word (vm_rights_of rghts) sz data)"
| "ArchCapabilityMap (arch_capability.PageTableCap word data) =
    cap.ArchObjectCap (arch_cap.PageTableCap word data)"
| "ArchCapabilityMap (arch_capability.PageDirectoryCap word data) =
    cap.ArchObjectCap (arch_cap.PageDirectoryCap word data)"
| "ArchCapabilityMap (arch_capability.VCPUCap v) =
    cap.ArchObjectCap (arch_cap.VCPUCap v)"
| "ArchCapabilityMap (arch_capability.SGISignalCap irq target) =
    cap.ArchObjectCap (arch_cap.SGISignalCap (ucast irq) (ucast target))"

lemma acap_relation_imp_ArchCapabilityMap[ADT_H_assms]:
  "\<lbrakk>wellformed_acap ac; acap_relation ac ac'\<rbrakk> \<Longrightarrow> ArchCapabilityMap ac' = cap.ArchObjectCap ac"
  by (case_tac ac; simp add: wellformed_acap_simps ucast_down_ucast_id is_down)

primrec ArchFaultMap :: "Fault_H.arch_fault \<Rightarrow> ExceptionTypes_A.arch_fault" where
  "ArchFaultMap (ARM_HYP_H.VMFault p m) = ARM_HYP_A.VMFault p m"
| "ArchFaultMap (ARM_HYP_H.VCPUFault w) = ARM_HYP_A.VCPUFault w"
| "ArchFaultMap (ARM_HYP_H.VGICMaintenance m) = ARM_HYP_A.VGICMaintenance m"
| "ArchFaultMap (ARM_HYP_H.VPPIEvent irq) = ARM_HYP_A.VPPIEvent irq"

lemma ArchFaultMap_arch_fault_map[ADT_H_assms]:
  "ArchFaultMap (arch_fault_map f) = f"
  by (cases f; simp add: ArchFaultMap_def arch_fault_map_def)

(* no FPU on this architecture *)
definition ArchTcbMap :: "Structures_H.arch_tcb \<Rightarrow> bool \<Rightarrow> Structures_A.arch_tcb" where
  "ArchTcbMap atcb is_cur_fpu_owner \<equiv>
    \<lparr> tcb_context = atcbContext atcb, tcb_vcpu = atcbVCPUPtr atcb \<rparr>"

lemma arch_tcb_relation_imp_ArchTcbMap:
  "\<lbrakk> arch_tcb_relation atcb atcb' \<rbrakk>
   \<Longrightarrow> ArchTcbMap atcb' is_cur_fpu_owner = atcb"
  by (clarsimp simp: arch_tcb_relation_def ArchTcbMap_def)

definition absArchState ::
  "Arch.kernel_state \<Rightarrow> (obj_ref \<rightharpoonup> arch_kernel_object) \<Rightarrow> arch_state"
  where
  "absArchState s' aobjs' \<equiv>
   case s' of ARMKernelState asid_tbl hwat anext am curvcpu vnumlistregs globalpd kvspace \<Rightarrow>
     \<lparr>arm_asid_table = asid_tbl \<circ> ucast,
      arm_hwasid_table = hwat, arm_next_asid = anext,
      arm_asid_map = am, arm_current_vcpu = curvcpu, arm_gicvcpu_numlistregs = vnumlistregs,
      arm_kernel_vspace = kvspace, arm_us_global_pd = globalpd\<rparr>"

lemma absArchState_correct[ADT_H_assms]:
  "(s,s') \<in> state_relation \<Longrightarrow> absArchState (ksArchState s') (aobjs_of' s') = arch_state s"
  apply (prop_tac "(arch_state s, ksArchState s') \<in> arch_state_relation (aobjs_of' s')")
   apply (simp add: state_relation_def)
  apply (clarsimp simp: arch_state_relation_def absArchState_def
                  split: ARM_HYP_H.kernel_state.splits)
  done

end (* Arch *)

arch_requalify_consts vm_rights_of ArchCapabilityMap ArchFaultMap ArchTcbMap absArchState

interpretation ADT_H?: ADT_H vm_rights_of ArchCapabilityMap ArchFaultMap ArchTcbMap absArchState
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact ADT_H_assms)?)?)
qed

context Arch begin arch_global_naming

named_theorems ADT_H_2_assms

(* Due to DataPage, current FPU owner and gsPPTypes this can't be made generic. In order to
   unify the type across architectures, we use the arch kernel state. *)
definition absHeap ::
  "(machine_word \<rightharpoonup> vmpage_size) \<Rightarrow> (machine_word \<rightharpoonup> nat) \<Rightarrow>
   Arch.kernel_state \<Rightarrow> (machine_word \<rightharpoonup> Structures_H.kernel_object) \<Rightarrow> Structures_A.kheap"
  where
  "absHeap ups cns aks h \<equiv> \<lambda>x.
     case h x of
       Some (KOEndpoint ep) \<Rightarrow> Some (Endpoint (EndpointMap ep))
     | Some (KONotification ntfn) \<Rightarrow> Some (Notification (AEndpointMap ntfn))
     | Some KOKernelData \<Rightarrow> undefined \<comment> \<open>forbidden by pspace_relation\<close>
     | Some KOUserData \<Rightarrow> map_option (ArchObj \<circ> DataPage False) (ups x)
     | Some KOUserDataDevice \<Rightarrow> map_option (ArchObj \<circ> DataPage True) (ups x)
     | Some (KOTCB tcb) \<Rightarrow> Some (TCB (TcbMap tcb False)) \<comment> \<open>no FPU on this arch\<close>
     | Some (KOCTE cte) \<Rightarrow> map_option (\<lambda>sz. absCNode sz h x) (cns x)
     | Some (KOArch ako) \<Rightarrow> map_option ArchObj (absHeapArch h x ako)
     | None \<Rightarrow> None"

lemma unaligned_page_offsets_helper:
  "\<lbrakk>is_aligned y (pageBitsForSize vmpage_size); n\<noteq>0;
    n < 2 ^ (pageBitsForSize vmpage_size - pageBits)\<rbrakk>
   \<Longrightarrow> \<not> is_aligned (y + n * 2 ^ pageBits :: word32) (pageBitsForSize vmpage_size)"
  apply (simp (no_asm_simp) add: is_aligned_mask)
  apply (simp add: mask_add_aligned)
  apply (cut_tac mask_eq_iff_w2p [of "pageBitsForSize vmpage_size" "n * 2 ^ pageBits"])
   prefer 2
   apply (case_tac vmpage_size, simp_all add: pageBits_def word_size)
  apply (cut_tac word_power_nonzero_32[of n pageBits];
         simp add: word_bits_conv pageBits_def)
   prefer 2
   apply (case_tac vmpage_size, simp_all add: pageBits_def word_size)
     apply (frule less_trans[of n _ "0x100000"], simp+)+
  apply clarsimp
  apply (case_tac vmpage_size, simp_all add: pageBits_def)
    apply (frule_tac i=n and k="0x1000" in word_mult_less_mono1, simp+)+
  done

lemma absHeap_correct[ADT_H_2_assms]:
  fixes s' :: kernel_state
  assumes pspace_aligned:  "pspace_aligned s"
  assumes pspace_distinct: "pspace_distinct s"
  assumes valid_objs:      "valid_objs s"
  assumes valid_cur_fpu:   "valid_cur_fpu s"
  assumes pspace_relation: "pspace_relation (kheap s) (ksPSpace s')"
  assumes ghost_relation:  "ghost_relation_wrapper s s'"
  assumes arch_state_relation: "(arch_state s, ksArchState s') \<in> arch_state_relation (aobjs_of' s')"
  shows
    "absHeap (gsUserPages s') (gsCNodes s') (ksArchState s') (ksPSpace s') = kheap s"
proof -
  from ghost_relation
  have gsUserPages:
    "\<And>a sz. (\<exists>dev. kheap s a = Some (ArchObj (DataPage dev sz))) \<longleftrightarrow>
             gsUserPages s' a = Some sz"
   and gsCNodes:
    "\<And>a n. (\<exists>cs. kheap s a = Some (CNode n cs) \<and> well_formed_cnode_n n cs) \<longleftrightarrow>
            gsCNodes s' a = Some n"
    by (fastforce simp add: ghost_relation_def)+

  show "?thesis"
  supply image_cong_simp [cong del]
    apply (rule ext)
    apply (simp add: absHeap_def split: option.splits)
    apply (rule conjI)
    using pspace_relation
     apply (clarsimp simp add: pspace_relation_def pspace_dom_def UNION_eq dom_def Collect_eq)
     apply (erule_tac x=x in allE)
     apply clarsimp
     apply (case_tac "kheap s x", simp)
     apply (erule_tac x=x in allE, clarsimp)
     apply (erule_tac x=x in allE, simp add: Ball_def)
     apply (erule_tac x=x in allE, clarsimp)

     apply (case_tac a)
         apply (simp_all add: other_obj_relation_def
                       split: if_split_asm Structures_H.kernel_object.splits)
      apply (rename_tac sz cs)
      apply (clarsimp simp add: image_def cte_map_def well_formed_cnode_n_def Collect_eq dom_def)
      apply (erule_tac x="replicate sz False" in allE)+
      apply simp
     apply (rename_tac arch_kernel_obj)
     apply (case_tac arch_kernel_obj, simp_all add: image_def)
       apply (erule_tac x=0 in allE, simp)
      apply (erule_tac x=0 in allE, simp)
     apply clarsimp
     apply (erule_tac x=0 in allE, simp add: pageBits_def)
     apply (rename_tac vmpage_size)
     apply (case_tac vmpage_size, simp_all)

    apply clarsimp
    apply (intro conjI impI allI)
           apply (erule pspace_dom_relatedE[OF _ pspace_relation])
           apply clarsimp
           apply (case_tac ko, simp_all add: tcb_relation_cut_def other_obj_relation_def)
             apply (clarsimp simp add: cte_relation_def split: if_split_asm)
            apply (clarsimp simp add: ep_relation_def EndpointMap_def
                               split: Structures_A.endpoint.splits)
           apply (clarsimp simp add: EndpointMap_def
                              split: Structures_A.endpoint.splits)
           apply (rename_tac arch_kernel_obj)
           apply (case_tac arch_kernel_obj, simp_all add: other_obj_relation_def)
             apply (clarsimp simp add: pte_relation_def)
            apply (clarsimp simp add: pde_relation_def)
           apply (clarsimp split: if_split_asm)+

          apply (erule pspace_dom_relatedE[OF _ pspace_relation])
          apply (case_tac ko, simp_all add: tcb_relation_cut_def other_obj_relation_def)
            apply (clarsimp simp add: cte_relation_def split: if_split_asm)
           apply (clarsimp simp add: ntfn_relation_def AEndpointMap_def
                              split: Structures_A.ntfn.splits)
          apply (clarsimp simp add: AEndpointMap_def
                             split: Structures_A.ntfn.splits)
          apply (rename_tac arch_kernel_obj)
          apply (case_tac arch_kernel_obj, simp_all add: other_obj_relation_def)
            apply (clarsimp simp add: pte_relation_def)
           apply (clarsimp simp add: pde_relation_def)
          apply (clarsimp split: if_split_asm)+

         apply (erule pspace_dom_relatedE[OF _ pspace_relation])
         apply (case_tac ko, simp_all add: tcb_relation_cut_def other_obj_relation_def)
          apply (clarsimp simp add: cte_relation_def split: if_split_asm)
         apply (rename_tac arch_kernel_obj)
         apply (case_tac arch_kernel_obj, simp_all add: other_obj_relation_def)
           apply (clarsimp simp add: pte_relation_def)
          apply (clarsimp simp add: pde_relation_def)
         apply (clarsimp split: if_split_asm)+

        apply (erule pspace_dom_relatedE[OF _ pspace_relation])
        apply (case_tac ko, simp_all add: tcb_relation_cut_def other_obj_relation_def)
         apply (clarsimp simp add: cte_relation_def split: if_split_asm)
        apply (rename_tac arch_kernel_obj)
        apply (case_tac arch_kernel_obj, simp_all add: other_obj_relation_def)
          apply (clarsimp simp add: pte_relation_def)
         apply (clarsimp simp add: pde_relation_def)
        apply (rename_tac vmpage_size)
        apply (cut_tac a=y and sz=vmpage_size in gsUserPages, clarsimp split: if_split_asm)
        apply (case_tac "n=0", simp)
        apply (case_tac "kheap s (y + n * 2 ^ pageBits)")
         apply (rule ccontr)
         apply (clarsimp dest!: gsUserPages[symmetric, THEN iffD1] )
    using pspace_aligned
        apply (simp add: pspace_aligned_def dom_def)
        apply (erule_tac x=y in allE)
        apply (case_tac "n=0",(simp split: if_split_asm)+)
        apply (frule (2) unaligned_page_offsets_helper)
        apply (frule_tac y="n*2^pageBits" in pspace_aligned_distinct_None'
                                                [OF pspace_aligned pspace_distinct])
         apply simp
         apply (rule conjI, clarsimp simp add: Word.word_gt_0)
         apply (simp add: is_aligned_mask)
         apply (clarsimp simp add: pageBits_def mask_def)
         apply (case_tac vmpage_size; simp)
           apply ((frule_tac i=n and k="0x1000" in word_mult_less_mono1, simp+)+)[4]
       apply (erule pspace_dom_relatedE[OF _ pspace_relation])
       apply (case_tac ko, simp_all add: tcb_relation_cut_def other_obj_relation_def)
        apply (clarsimp simp add: cte_relation_def split: if_split_asm)
       apply (rename_tac arch_kernel_obj)
       apply (case_tac arch_kernel_obj, simp_all add: other_obj_relation_def)
         apply (clarsimp simp add: pte_relation_def)
        apply (clarsimp simp add: pde_relation_def)
       apply (rename_tac vmpage_size)
       apply (cut_tac a=y and sz=vmpage_size in gsUserPages, clarsimp split: if_split_asm)
       apply (case_tac "n=0", simp)
       apply (case_tac "kheap s (y + n * 2 ^ pageBits)")
        apply (rule ccontr)
        apply (clarsimp dest!: gsUserPages[symmetric, THEN iffD1])
    using pspace_aligned
       apply (simp add: pspace_aligned_def dom_def)
       apply (erule_tac x=y in allE)
       apply (case_tac "n=0",simp+)
       apply (frule (2) unaligned_page_offsets_helper)
       apply (frule_tac y="n*2^pageBits" in pspace_aligned_distinct_None'
                                               [OF pspace_aligned pspace_distinct])
        apply simp
        apply (rule conjI, clarsimp simp add: Word.word_gt_0)
        apply (simp add: is_aligned_mask)
        apply (clarsimp simp add: pageBits_def mask_def)
        apply (case_tac vmpage_size; simp)
          apply ((frule_tac i=n and k="0x1000" in word_mult_less_mono1, simp+)+)[4]
      apply (erule pspace_dom_relatedE[OF _ pspace_relation])
      apply (case_tac ko, simp_all add: tcb_relation_cut_def other_obj_relation_def)
        apply (clarsimp simp add: cte_relation_def split: if_split_asm)
       prefer 2
       apply (rename_tac arch_kernel_obj)
       apply (case_tac arch_kernel_obj, simp_all add: other_obj_relation_def)
         apply (clarsimp simp add: pte_relation_def)
        apply (clarsimp simp add: pde_relation_def)
       apply (clarsimp split: if_split_asm)
      apply (clarsimp simp add: TcbMap_def tcb_relation_def valid_obj_def)
      apply (rename_tac tcb y tcb')
      apply (case_tac tcb)
      apply (case_tac tcb')
      apply (simp add: thread_state_relation_imp_ThStateMap)
      apply (subgoal_tac "map_option FaultMap (tcbFault tcb) = tcb_fault")
       prefer 2
       apply (simp add: fault_rel_optionation_def)
    using valid_objs[simplified valid_objs_def dom_def fun_app_def,simplified]
       apply (erule_tac x=y in allE)
       apply (clarsimp simp: valid_obj_def valid_tcb_def
        split: option.splits)
    using valid_objs[simplified valid_objs_def Ball_def dom_def fun_app_def]
      apply (erule_tac x=y in allE)
      apply (clarsimp simp add: cap_relation_imp_CapabilityMap valid_obj_def
                                valid_tcb_def ran_tcb_cap_cases valid_cap_def2
                                arch_tcb_relation_imp_ArchTcbMap)
     apply (simp add: absCNode_def cte_map_def)
     apply (erule pspace_dom_relatedE[OF _ pspace_relation])
     apply (case_tac ko, simp_all add: tcb_relation_cut_def other_obj_relation_def
                                split: if_split_asm)
      prefer 2
      apply (rename_tac arch_kernel_obj)
      apply (case_tac arch_kernel_obj, simp_all add: other_obj_relation_def)
        apply (clarsimp simp add: pte_relation_def)
       apply (clarsimp simp add: pde_relation_def)
      apply (clarsimp split: if_split_asm)
     apply (simp add: cte_map_def)
     apply (clarsimp simp add: cte_relation_def)
     apply (cut_tac a=y and n=sz in gsCNodes, clarsimp)
    using pspace_aligned[simplified pspace_aligned_def]
     apply (drule_tac x=y in bspec, clarsimp)
     apply (clarsimp simp: shiftl_t2n')
     apply (case_tac "(of_bl ya::word32) * 2^cte_level_bits = 0", simp)
      apply (rule ext)
      apply simp
      apply (rule conjI)
       prefer 2
    using valid_objs[simplified valid_objs_def Ball_def dom_def fun_app_def]
       apply (erule_tac x=y in allE)
       apply (clarsimp simp add: valid_obj_def valid_cs_def valid_cs_size_def
                                 well_formed_cnode_n_def dom_def Collect_eq)
       apply (frule_tac x=ya in spec, simp)
       apply (erule_tac x=bl in allE)
       apply clarsimp+
      apply (frule pspace_relation_absD[OF _ pspace_relation])
      apply (simp add: cte_map_def shiftl_t2n')
      apply (drule_tac x="y + of_bl bl * 2^cte_level_bits" in spec)
      apply clarsimp
      apply (erule_tac x="cte_relation bl" in allE)
      apply (erule impE)
       apply (fastforce simp add: well_formed_cnode_n_def)
      apply clarsimp
      apply (clarsimp simp add: cte_relation_def)
      apply (rule cap_relation_imp_CapabilityMap)
    using valid_objs[simplified valid_objs_def Ball_def dom_def fun_app_def]
       apply (erule_tac x=y in allE)
       apply (clarsimp simp: valid_obj_def valid_cs_def valid_cap_def2 ran_def)
       apply (fastforce simp: cte_level_bits_def cteSizeBits_def)+
     apply (subgoal_tac "kheap s (y + of_bl ya * 2^cte_level_bits) = None")
      prefer 2
    using valid_objs[simplified valid_objs_def Ball_def dom_def fun_app_def]
      apply (erule_tac x=y in allE)
      apply (clarsimp simp add: valid_obj_def valid_cs_def valid_cs_size_def)
      apply (rule pspace_aligned_distinct_None'[OF pspace_aligned pspace_distinct], assumption)
      apply (clarsimp simp: word_neq_0_conv power_add cte_index_repair)
      apply (simp add: well_formed_cnode_n_def dom_def Collect_eq)
      apply (erule_tac x=ya in allE)+
      apply (rule word_mult_less_mono1)
        apply (subgoal_tac "sz = length ya")
         apply simp
         apply (rule of_bl_length, (simp add: word_bits_def)+)[1]
        apply fastforce
       apply (simp add: cte_level_bits_def)
      apply (simp add: word_bits_conv cte_level_bits_def)
      apply (drule_tac a="2::nat" in power_strict_increasing, simp+)
     apply (rule ccontr, clarsimp)
     apply (cut_tac a="y + of_bl ya * 2^cte_level_bits" and n=yc in gsCNodes)
     apply clarsimp

    (* mapping architecture-specific objects *)
    apply clarsimp
    apply (erule pspace_dom_relatedE[OF _ pspace_relation])
    apply (case_tac ko, simp_all add: tcb_relation_cut_def other_obj_relation_def)
     apply (clarsimp simp add: cte_relation_def split: if_split_asm)
    apply (rename_tac arch_kernel_object y ko P arch_kernel_obj)
    apply (case_tac arch_kernel_object, simp_all add: absHeapArch_def split: asidpool.splits)

       apply clarsimp
       apply (case_tac arch_kernel_obj)
           apply (simp add: other_aobj_relation_def asid_pool_relation_def inv_def o_def)
          apply (clarsimp simp add:  pte_relation_def)
         apply (clarsimp simp add:  pde_relation_def)
        apply (clarsimp split: if_split_asm)+
       apply (clarsimp simp: other_aobj_relation_def)
      apply (case_tac arch_kernel_obj)
          apply (simp add: other_aobj_relation_def asid_pool_relation_def inv_def o_def)
    using pspace_aligned[simplified pspace_aligned_def Ball_def dom_def]
         apply (erule_tac x=y in allE)
         apply (clarsimp simp add: pte_relation_def absPageTable_def pt_bits_def pageBits_def)
         apply (rule conjI)
          prefer 2
          apply clarsimp
          apply (rule sym)
          apply (rule pspace_aligned_distinct_None' [OF pspace_aligned pspace_distinct],
                 (simp add: vspace_bits_defs)+)
          apply (cut_tac x=ya and n="2^12" in
                      ucast_less_shiftl3_helper[where 'a=32,simplified word_bits_conv], simp+)
          apply (clarsimp simp add: Word.word_gt_0)
         apply clarsimp
         apply (subgoal_tac "ucast ya << 3 = 0")
          prefer 2
          apply (rule ccontr)
          apply (frule_tac x=y in unaligned_helper, assumption)
           apply (rule ucast_less_shiftl3_helper, simp_all add: vspace_bits_defs)
         apply (rule ext)
         apply (frule pspace_relation_absD[OF _ pspace_relation])
         apply simp
         apply (erule_tac x=offs in allE)
         apply (clarsimp simp add: pte_relation_def)
    using valid_objs[simplified valid_objs_def fun_app_def dom_def, simplified]
         apply (erule_tac x=y in allE)
         apply (clarsimp simp add: valid_obj_def wellformed_pte_def)
         apply (erule_tac x=offs in allE)
         apply (rename_tac pte')
         apply (case_tac pte', simp_all add: pte_relation_aligned_def vspace_bits_defs)[1]
          apply (clarsimp split: ARM_HYP_A.pte.splits)
          apply (rule set_eqI, clarsimp)
          apply (case_tac x, simp_all)[1]
         apply (clarsimp split: ARM_HYP_A.pte.splits)
         apply (rule set_eqI, clarsimp)
         apply (case_tac x, simp_all)[1]
        apply (clarsimp simp add: pde_relation_def)
       apply (clarsimp split: if_split_asm)+
      apply (simp add: other_aobj_relation_def inv_def o_def)
     apply (case_tac arch_kernel_obj)
         apply (simp add: other_aobj_relation_def asid_pool_relation_def inv_def o_def)
        apply (clarsimp simp add:  pte_relation_def)
    using pspace_aligned
       apply (simp add: pspace_aligned_def dom_def)
       apply (erule_tac x=y in allE)
       apply (clarsimp simp add: pde_relation_def absPageDirectory_def vspace_bits_defs)
       apply (rule conjI)
        prefer 2
        apply clarsimp
        apply (rule sym)
        apply (rule pspace_aligned_distinct_None' [OF pspace_aligned pspace_distinct],
               (simp add: vspace_bits_defs)+)
        apply (cut_tac x=ya and n="2^14" in
                  ucast_less_shiftl3_helper[where 'a=32, simplified word_bits_conv], simp+)
        apply (clarsimp simp add: Word.word_gt_0)
       apply clarsimp
       apply (subgoal_tac "ucast ya << 3 = 0")
        prefer 2
        apply (rule ccontr)
        apply (frule_tac x=y in unaligned_helper, assumption)
         apply (rule ucast_less_shiftl3_helper, simp_all)
       apply (rule ext)
       apply (frule pspace_relation_absD[OF _ pspace_relation])
       apply simp
       apply (erule_tac x=offs in allE)
       apply (clarsimp simp add: pde_relation_def)

    using valid_objs[simplified valid_objs_def fun_app_def dom_def,simplified]
       apply (erule_tac x=y in allE)
       apply (clarsimp simp add: valid_obj_def wellformed_pde_def vspace_bits_defs)
       apply (erule_tac x=offs in allE)
       apply (rename_tac pde')
       apply (case_tac pde', simp_all add: pde_relation_aligned_def)[1]
          apply (clarsimp split: ARM_HYP_A.pde.splits)+
        apply (rule set_eqI, clarsimp)
        apply (case_tac x, simp_all)[1]
       apply (clarsimp split: ARM_HYP_A.pde.splits)
       apply (rule set_eqI, clarsimp)
       apply (case_tac x, simp_all)[1]
      apply (clarsimp simp add: pde_relation_def split: if_split_asm)
     apply (clarsimp simp add: other_aobj_relation_def)

    apply clarsimp
    apply (rename_tac arch_kernel_obj vcpu)
    apply (case_tac arch_kernel_obj;
           clarsimp simp: other_aobj_relation_def pte_relation_def pde_relation_def split: if_splits)
    apply (rename_tac vcpu')
    apply (case_tac vcpu')
    apply (clarsimp simp: vcpu_relation_def split: vcpu.splits)
    done
qed

end (* Arch *)

arch_requalify_consts absHeap

interpretation ADT_H_2?: ADT_H_2 vm_rights_of ArchCapabilityMap ArchFaultMap ArchTcbMap absArchState
                                  absHeap
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact ADT_H_2_assms)?)?)
qed

end
