(*
 * Copyright 2014, General Dynamics C4 Systems
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

(* We expect 'a to be one of {pt_index, vs_index} *)
definition absPageTable0 ::
  "(obj_ref \<rightharpoonup> Structures_H.kernel_object) \<Rightarrow> obj_ref \<Rightarrow> 'a::len word \<rightharpoonup> ARM_HYP_A.pte" where
  "absPageTable0 h a \<equiv> \<lambda>offs.
   case h (a + (ucast offs << pte_bits)) of
     Some (KOArch (KOPTE (InvalidPTE))) \<Rightarrow> Some ARM_HYP_A.InvalidPTE
   | Some (KOArch (KOPTE (PagePTE p small global execNever dev rights))) \<Rightarrow>
       Some (ARM_HYP_A.PagePTE p small
                               {x. global \<and> x=Global \<or> \<not>execNever \<and> x = Execute \<or>
                                   dev \<and> x = Device}
                               (vm_rights_of rights))
   | Some (KOArch (KOPTE (PageTablePTE p))) \<Rightarrow>
       if p \<le> mask ppn_len
       then Some (ARM_HYP_A.PageTablePTE (ucast p))
       else None
   | _ \<Rightarrow> None"

definition absPageTable ::
  "(obj_ref \<rightharpoonup> Structures_H.kernel_object) \<Rightarrow> pt_type option \<Rightarrow> obj_ref \<rightharpoonup> pt" where
  "absPageTable h pt_t a \<equiv>
   case pt_t of
     Some NormalPT_T \<Rightarrow>
       if is_aligned a (pt_bits NormalPT_T) \<and> (\<forall>off::pt_index. absPageTable0 h a off \<noteq> None)
       then Some (NormalPT (\<lambda>off. the (absPageTable0 h a off)))
       else None
   | Some VSRootPT_T \<Rightarrow>
       if is_aligned a (pt_bits VSRootPT_T) \<and> (\<forall>off::vs_index. absPageTable0 h a off \<noteq> None)
       then Some (VSRootPT (\<lambda>off. the (absPageTable0 h a off)))
       else None
   | None \<Rightarrow> None"

definition absVGIC :: "gicvcpuinterface \<Rightarrow> gic_vcpu_interface" where
  "absVGIC v \<equiv> case v of
    VGICInterface hcr vmcr apr lr \<Rightarrow> gic_vcpu_interface.make hcr vmcr apr lr"

lemma absVGIC_eq[simp]:
  "absVGIC (vgic_map vgic) = vgic"
  by (simp add: vgic_map_def absVGIC_def gic_vcpu_interface.make_def)

(* Can't pull the whole heap off at once, start with arch specific stuff.*)
definition absHeapArch ::
  "(machine_word \<rightharpoonup> kernel_object) \<Rightarrow> (machine_word \<rightharpoonup> pt_type) \<Rightarrow>
   machine_word \<Rightarrow> arch_kernel_object \<rightharpoonup> arch_kernel_obj" where
  "absHeapArch h pt_types a \<equiv> \<lambda>ako.
     case ako of
       KOASIDPool (ARM_HYP_H.ASIDPool ap) \<Rightarrow>
         Some (ARM_HYP_A.ASIDPool (\<lambda>w. map_option abs_asid_entry (ap (ucast w))))
     | KOPTE _ \<Rightarrow>
         map_option PageTable (absPageTable h (pt_types a) a)
     | KOVCPU (VCPUObj tcb vgic regs vppimask) \<Rightarrow>
       Some (VCPU \<lparr> vcpu_vgic   = absVGIC vgic,
                    vcpu_regs   = regs,
                    vcpu_tcb    = tcb,
                    vcpu_vppi_masked = vppimask \<rparr>)"

definition mdata_map' ::
  "(asid \<times> vspace_ref) option \<Rightarrow> (Machine_A.ARM_HYP_A.asid \<times> vspace_ref) option" where
  "mdata_map' = map_option (\<lambda>(asid, ref). (ucast asid, ref))"

lemma mdata_map'_inv[simp]:
  "mdata_map' (mdata_map m) = m"
  by (cases m; simp add: mdata_map_def mdata_map'_def split_def ucast_down_ucast_id is_down)

fun ArchCapabilityMap :: "arch_capability \<Rightarrow> cap" where
  "ArchCapabilityMap (arch_capability.ASIDPoolCap x y) =
     cap.ArchObjectCap (arch_cap.ASIDPoolCap x (ucast y))"
| "ArchCapabilityMap (arch_capability.ASIDControlCap) =
     cap.ArchObjectCap (arch_cap.ASIDControlCap)"
| "ArchCapabilityMap (arch_capability.FrameCap word rghts sz d data) =
     cap.ArchObjectCap (arch_cap.FrameCap word (vm_rights_of rghts) sz d (mdata_map' data))"
| "ArchCapabilityMap (arch_capability.PageTableCap word pt_t data) =
     cap.ArchObjectCap (arch_cap.PageTableCap word pt_t (mdata_map' data))"
| "ArchCapabilityMap (arch_capability.VCPUCap v) =
     cap.ArchObjectCap (arch_cap.VCPUCap v)"
| "ArchCapabilityMap (arch_capability.SGISignalCap irq target) =
     cap.ArchObjectCap (arch_cap.SGISignalCap (ucast irq) (ucast target))"
| "ArchCapabilityMap (arch_capability.SMCCap smc_badge) =
     cap.ArchObjectCap (arch_cap.SMCCap smc_badge)"

lemma acap_relation_imp_ArchCapabilityMap[ADT_H_assms]:
  "\<lbrakk>wellformed_acap ac; acap_relation ac ac'\<rbrakk> \<Longrightarrow> ArchCapabilityMap ac' = cap.ArchObjectCap ac"
  by (case_tac ac; simp add: wellformed_cap_simps ucast_down_ucast_id is_down)

primrec ArchFaultMap :: "Fault_H.arch_fault \<Rightarrow> ExceptionTypes_A.arch_fault" where
  "ArchFaultMap (ARM_HYP_H.VMFault p m) = ARM_HYP_A.VMFault p m"
| "ArchFaultMap (ARM_HYP_H.VCPUFault w) = ARM_HYP_A.VCPUFault w"
| "ArchFaultMap (ARM_HYP_H.VGICMaintenance m) = ARM_HYP_A.VGICMaintenance m"
| "ArchFaultMap (ARM_HYP_H.VPPIEvent irq) = ARM_HYP_A.VPPIEvent irq"

lemma ArchFaultMap_arch_fault_map[ADT_H_assms]:
  "ArchFaultMap (arch_fault_map f) = f"
  by (cases f; simp add: ArchFaultMap_def arch_fault_map_def)

definition ArchTcbMap :: "Structures_H.arch_tcb \<Rightarrow> bool \<Rightarrow> Structures_A.arch_tcb" where
  "ArchTcbMap atcb is_cur_fpu_owner \<equiv>
    \<lparr> tcb_context = atcbContext atcb, tcb_vcpu = atcbVCPUPtr atcb, tcb_cur_fpu = is_cur_fpu_owner \<rparr>"

lemma arch_tcb_relation_imp_ArchTcbMap:
  "\<lbrakk> arch_tcb_relation atcb atcb'; tcb_cur_fpu atcb = is_cur_fpu_owner\<rbrakk>
   \<Longrightarrow> ArchTcbMap atcb' is_cur_fpu_owner = atcb"
  by (clarsimp simp: arch_tcb_relation_def ArchTcbMap_def)

lemma unaligned_page_offsets_helper:
  "\<lbrakk>is_aligned y (pageBitsForSize vmpage_size); n\<noteq>0;
    n < 2 ^ (pageBitsForSize vmpage_size - pageBits)\<rbrakk>
   \<Longrightarrow> \<not> is_aligned (y + n * 2 ^ pageBits :: machine_word) (pageBitsForSize vmpage_size)"
  apply (simp (no_asm_simp) add: is_aligned_mask)
  apply (simp add: mask_add_aligned)
  apply (cut_tac mask_eq_iff_w2p [of "pageBitsForSize vmpage_size" "n * 2 ^ pageBits"])
   prefer 2
   apply (case_tac vmpage_size, simp_all add: word_size bit_simps)
  apply (cut_tac word_power_nonzero_64[of n pageBits];
         simp add: word_bits_conv pageBits_def)
   prefer 2
   apply (case_tac vmpage_size, simp_all add: bit_simps word_size)
     apply (frule less_trans[of n _ "0x10000000000000"], simp+)+
  apply clarsimp
  apply (case_tac vmpage_size, simp_all add: bit_simps)
    apply (frule_tac i=n and k="0x1000" in word_mult_less_mono1, simp+)+
  done

definition absArchState ::
  "Arch.kernel_state \<Rightarrow> (obj_ref \<rightharpoonup> arch_kernel_object) \<Rightarrow> arch_state"
  where
  "absArchState s' aobjs' \<equiv>
   case s' of
     ARMKernelState asid_tbl kvspace vmid_tab next_vmid global_us_vspace current_vcpu
                    num_list_regs gs_pt_types current_fpu_owner \<Rightarrow>
     \<lparr> arm_asid_table = asid_tbl \<circ> ucast,
       arm_kernel_vspace = kvspace,
       arm_asid_map = armKSASIDMap' s' aobjs',
       arm_vmid_table = map_option ucast \<circ> vmid_tab,
       arm_next_vmid = next_vmid,
       arm_us_global_vspace = global_us_vspace,
       arm_current_vcpu = current_vcpu,
       arm_gicvcpu_numlistregs = num_list_regs,
       arm_current_fpu_owner = current_fpu_owner \<rparr>"

lemma absArchState_correct[ADT_H_assms]:
  "(s,s') \<in> state_relation \<Longrightarrow> absArchState (ksArchState s') (aobjs_of' s') = arch_state s"
  apply (prop_tac "(arch_state s, ksArchState s') \<in> arch_state_relation (aobjs_of' s')")
   apply (simp add: state_relation_def)
  apply (clarsimp simp: arch_state_relation_def absArchState_def
                  split: ARM_HYP_H.kernel_state.splits)
  apply (simp add: o_assoc flip: map_option_comp2)
  apply (simp add: o_def ucast_up_ucast_id is_up map_option.identity)
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
     | Some (KOTCB tcb) \<Rightarrow> Some (TCB (TcbMap tcb (armKSCurFPUOwner aks = Some x)))
     | Some (KOCTE cte) \<Rightarrow> map_option (\<lambda>sz. absCNode sz h x) (cns x)
     | Some (KOArch ako) \<Rightarrow> map_option ArchObj (absHeapArch h (gsPTTypes aks) x ako)
     | None \<Rightarrow> None"

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
   and gsPTs:
    "\<And>a pt_t. (\<exists>pt. kheap s a = Some (ArchObj (PageTable pt)) \<and> pt_t = pt_type pt) \<longleftrightarrow>
               gsPTTypes (ksArchState s') a = Some pt_t"
    by (fastforce simp add: ghost_relation_def)+

  show "?thesis"
    supply image_cong_simp [cong del]
    apply (rule ext)
    apply (simp add: absHeap_def split: option.splits)
    apply (rule conjI)
    using pspace_relation
     apply (clarsimp simp: pspace_relation_def pspace_dom_def UNION_eq dom_def Collect_eq)
     apply (erule_tac x=x in allE)
     apply clarsimp
     apply (case_tac "kheap s x", simp)
     apply (erule_tac x=x in allE, clarsimp)
     apply (erule_tac x=x in allE, simp add: Ball_def)
     apply (erule_tac x=x in allE, clarsimp)
     apply (rename_tac a)
     apply (case_tac a; simp add: other_obj_relation_def
                             split: if_split_asm Structures_H.kernel_object.splits)
      apply (rename_tac sz cs)
      apply (clarsimp simp: image_def cte_map_def well_formed_cnode_n_def Collect_eq dom_def)
      apply (erule_tac x="replicate sz False" in allE)+
      apply simp
     apply (rename_tac arch_kernel_obj)
     apply (case_tac arch_kernel_obj; simp add: image_def)
      apply (erule allE, drule_tac x=0 in bspec, simp, fastforce)
     apply (erule_tac x=0 in allE, simp add: not_less)
     apply (rename_tac vmpage_size)
     apply (case_tac vmpage_size; simp add: bit_simps)

    apply (clarsimp split: kernel_object.splits)
    apply (intro conjI impI allI)
           apply (erule pspace_dom_relatedE[OF _ pspace_relation])
           apply clarsimp
           apply (case_tac ko; simp add: tcb_relation_cut_def other_obj_relation_def)
             apply (clarsimp simp: cte_relation_def split: if_split_asm)
            apply (clarsimp simp: ep_relation_def EndpointMap_def
                            split: Structures_A.endpoint.splits)
           apply (clarsimp simp: EndpointMap_def split: Structures_A.endpoint.splits)
           apply (rename_tac arch_kernel_obj)
           apply (case_tac arch_kernel_obj; simp add: other_obj_relation_def)
            apply (clarsimp simp add: pte_relation_def)
           apply (clarsimp split: if_split_asm)+

          apply (erule pspace_dom_relatedE[OF _ pspace_relation])
          apply (case_tac ko; simp add: tcb_relation_cut_def other_obj_relation_def)
            apply (clarsimp simp: cte_relation_def split: if_split_asm)
           apply (clarsimp simp: ntfn_relation_def AEndpointMap_def
                           split: Structures_A.ntfn.splits)
          apply (clarsimp simp: AEndpointMap_def split: Structures_A.ntfn.splits)
          apply (rename_tac arch_kernel_obj)
          apply (case_tac arch_kernel_obj; simp add: other_obj_relation_def)
           apply (clarsimp simp add: pte_relation_def)
          apply (clarsimp split: if_split_asm)+

         apply (erule pspace_dom_relatedE[OF _ pspace_relation])
         apply (case_tac ko; simp add: tcb_relation_cut_def other_obj_relation_def)
          apply (clarsimp simp: cte_relation_def split: if_split_asm)
         apply (rename_tac arch_kernel_obj)
         apply (case_tac arch_kernel_obj; simp add: other_obj_relation_def)
          apply (clarsimp simp add: pte_relation_def)
         apply (clarsimp split: if_split_asm)+

        apply (erule pspace_dom_relatedE[OF _ pspace_relation])
        apply (case_tac ko, simp_all add: tcb_relation_cut_def other_obj_relation_def)
         apply (clarsimp simp add: cte_relation_def split: if_split_asm)
        apply (rename_tac arch_kernel_obj)
        apply (case_tac arch_kernel_obj, simp_all add: other_obj_relation_def)
         apply (clarsimp simp add: pte_relation_def)
        apply (rename_tac vmpage_size)
        apply (cut_tac a=y and sz=vmpage_size in gsUserPages, clarsimp split: if_split_asm)
        apply (case_tac "n=0", simp)
        apply (case_tac "kheap s (y + n * 2 ^ pageBits)")
         apply (rule ccontr)
         apply (clarsimp simp: shiftl_t2n mult_ac dest!: gsUserPages[symmetric, THEN iffD1] )
    using pspace_aligned
        apply (simp add: pspace_aligned_def dom_def)
        apply (erule_tac x=y in allE)
        apply (case_tac "n=0",(simp split: if_split_asm)+)
        apply (frule (2) unaligned_page_offsets_helper)
        apply (frule_tac y="n*2^pageBits" in pspace_aligned_distinct_None'
                                             [OF pspace_aligned pspace_distinct])
         apply simp
         apply (rule conjI, clarsimp simp add: word_gt_0)
         apply (erule n_less_2p_pageBitsForSize)
        apply (clarsimp simp: shiftl_t2n mult_ac)
       apply (erule pspace_dom_relatedE[OF _ pspace_relation])
       apply (case_tac ko, simp_all add: tcb_relation_cut_def other_obj_relation_def)
        apply (clarsimp simp add: cte_relation_def split: if_split_asm)
       apply (rename_tac arch_kernel_obj)
       apply (case_tac arch_kernel_obj, simp_all add: other_obj_relation_def)
        apply (clarsimp simp add: pte_relation_def)
       apply (rename_tac vmpage_size)
       apply (cut_tac a=y and sz=vmpage_size in gsUserPages, clarsimp split: if_split_asm)
       apply (case_tac "n=0", simp)
       apply (case_tac "kheap s (y + n * 2 ^ pageBits)")
        apply (rule ccontr)
        apply (clarsimp simp: shiftl_t2n mult_ac dest!: gsUserPages[symmetric, THEN iffD1])
       using pspace_aligned
       apply (simp add: pspace_aligned_def dom_def)
       apply (erule_tac x=y in allE)
       apply (case_tac "n=0",simp+)
       apply (frule (2) unaligned_page_offsets_helper)
       apply (frule_tac y="n*2^pageBits" in pspace_aligned_distinct_None'
                                         [OF pspace_aligned pspace_distinct])
        apply simp
        apply (rule conjI, clarsimp simp add: word_gt_0)
        apply (erule n_less_2p_pageBitsForSize)
       apply (clarsimp simp: shiftl_t2n mult_ac)
      (* TCB *)
      apply (erule pspace_dom_relatedE[OF _ pspace_relation])
      apply (case_tac ko, simp_all add: tcb_relation_cut_def other_obj_relation_def)
        apply (clarsimp simp add: cte_relation_def split: if_split_asm)
       prefer 2
       apply (rename_tac arch_kernel_obj)
       apply (case_tac arch_kernel_obj, simp_all add: other_obj_relation_def)
        apply (clarsimp simp add: pte_relation_def)
       apply (clarsimp split: if_split_asm)
      apply (clarsimp simp add: TcbMap_def tcb_relation_def valid_obj_def)
      apply (rename_tac tcb y tcb')
      apply (case_tac tcb)
      apply (case_tac tcb')
      apply (simp add: thread_state_relation_imp_ThStateMap)
      apply (subgoal_tac "map_option FaultMap (tcbFault tcb) = tcb_fault")
       prefer 2
       apply (simp add: fault_rel_optionation_def)
       using valid_objs[simplified valid_objs_def dom_def fun_app_def, simplified]
       apply (erule_tac x=y in allE)
       apply (clarsimp simp: valid_obj_def valid_tcb_def
                       split: option.splits)
      using valid_objs[simplified valid_objs_def Ball_def dom_def fun_app_def]
      apply (erule_tac x=y in allE)
      using arch_state_relation valid_cur_fpu[simplified valid_cur_fpu_def]
      apply (erule_tac x=y in allE)
      apply (clarsimp simp add: cap_relation_imp_CapabilityMap valid_obj_def
                                valid_tcb_def ran_tcb_cap_cases valid_cap_def2
                                arch_tcb_relation_imp_ArchTcbMap arch_state_relation_def
                                is_tcb_cur_fpu_def obj_at_def)
     apply (simp add: absCNode_def cte_map_def)
     apply (erule pspace_dom_relatedE[OF _ pspace_relation])
     apply (case_tac ko, simp_all add: tcb_relation_cut_def other_obj_relation_def
                                split: if_split_asm)
      prefer 2
      apply (rename_tac arch_kernel_obj)
      apply (case_tac arch_kernel_obj, simp_all add: other_obj_relation_def)
       apply (clarsimp simp add: pte_relation_def)
      apply (clarsimp split: if_split_asm)
     apply (simp add: cte_map_def)
     apply (clarsimp simp add: cte_relation_def)
     apply (cut_tac a=y and n=sz in gsCNodes, clarsimp)
    using pspace_aligned[simplified pspace_aligned_def]
     apply (drule_tac x=y in bspec, clarsimp)
     apply clarsimp
     apply (case_tac "(of_bl ya::machine_word) << cte_level_bits = 0", simp)
      apply (rule ext)
      apply simp
      apply (rule conjI)
       prefer 2
    using valid_objs[simplified valid_objs_def Ball_def dom_def
        fun_app_def]
       apply (erule_tac x=y in allE)
       apply (clarsimp simp add: valid_obj_def valid_cs_def valid_cs_size_def
                   well_formed_cnode_n_def dom_def Collect_eq)
       apply (frule_tac x=ya in spec, simp)
       apply (erule_tac x=bl in allE)
       apply clarsimp+
      apply (frule pspace_relation_absD[OF _ pspace_relation])
      apply (simp add: cte_map_def)
      apply (drule_tac x="y + of_bl bl * 2^cte_level_bits" in spec)
      apply (clarsimp simp: shiftl_t2n mult_ac)
      apply (erule_tac x="cte_relation bl" in allE)
      apply (erule impE)
       apply (fastforce simp add: well_formed_cnode_n_def)
      apply clarsimp
      apply (clarsimp simp add: cte_relation_def)
      apply (rule cap_relation_imp_CapabilityMap)
    using valid_objs[simplified valid_objs_def Ball_def dom_def
        fun_app_def]
       apply (erule_tac x=y in allE)
       apply (clarsimp simp: valid_obj_def valid_cs_def valid_cap_def2 ran_def)
       apply (fastforce simp: cte_level_bits_def objBits_defs)+
     apply (subgoal_tac "kheap s (y + of_bl ya * 2^cte_level_bits) = None")
      prefer 2
    using valid_objs[simplified valid_objs_def Ball_def dom_def fun_app_def]
      apply (erule_tac x=y in allE)
      apply (clarsimp simp add: valid_obj_def valid_cs_def valid_cs_size_def)
      apply (rule pspace_aligned_distinct_None'[OF
                  pspace_aligned pspace_distinct], assumption)
      apply (clarsimp simp: word_neq_0_conv power_add cte_index_repair)
      apply (simp add: well_formed_cnode_n_def dom_def Collect_eq shiftl_t2n mult_ac)
      apply (erule_tac x=ya in allE)+
      apply (rule word_mult_less_mono1)
        apply (subgoal_tac "sz = length ya")
         apply simp
         apply (rule of_bl_length, (simp add: word_bits_def)+)[1]
        apply fastforce
       apply (simp add: cte_level_bits_def)
      apply (simp add: word_bits_conv cte_level_bits_def)
      apply (drule_tac a="2::nat" in power_strict_increasing, simp+)
     apply (simp add: shiftl_t2n mult_ac)
     apply (rule ccontr, clarsimp)
     apply (cut_tac a="y + of_bl ya * 2^cte_level_bits" and n=yc in gsCNodes)
     apply clarsimp

    (* mapping architecture-specific objects *)
    apply clarsimp
    apply (erule pspace_dom_relatedE[OF _ pspace_relation])
    apply (case_tac ko, simp_all add: tcb_relation_cut_def other_obj_relation_def)
     apply (clarsimp simp add: cte_relation_def split: if_split_asm)
    apply (rename_tac arch_kernel_object y ko P arch_kernel_obj)
    apply (case_tac arch_kernel_object, simp_all add: absHeapArch_def
                                            split: asidpool.splits)

      apply (in_case "KOASIDPool ?pool")
      apply clarsimp
      apply (case_tac arch_kernel_obj)
         apply (simp add: other_aobj_relation_def asid_pool_relation_def
                          inv_def o_def)
        apply (clarsimp simp add:  pte_relation_def)
       apply (clarsimp simp: other_aobj_relation_def split: if_split_asm)
      apply (simp add: other_aobj_relation_def)

     apply (in_case "KOPTE ?pte")
     apply (case_tac arch_kernel_obj;
            simp add: other_obj_relation_def other_aobj_relation_def asid_pool_relation_def inv_def o_def)
      apply clarsimp
      apply (rename_tac p pte pt idx)
      apply (frule pspace_alignedD, rule pspace_aligned)
      apply (clarsimp simp add: pte_relation_def)
      apply (prop_tac "pt_at (pt_type pt) p s", simp add: obj_at_def)
      apply (drule page_table_at_cross[OF _ pspace_aligned pspace_distinct pspace_relation])
      apply (clarsimp simp: page_table_at'_def typ_at'_def ko_wp_at'_def)
      apply (cut_tac a=p and pt_t="pt_type pt" in gsPTs, clarsimp)
      apply (case_tac "pt_type pt"; clarsimp)
       apply (in_case "VSRootPT_T")
       apply (clarsimp simp: absPageTable_def split del: if_split split: option.splits)
       apply (rule conjI, clarsimp)
        apply (rule sym)
        apply (rule pspace_aligned_distinct_None'[OF pspace_aligned pspace_distinct], assumption)
        apply simp
        apply (case_tac "idx << pte_bits = 0", simp)
        apply (clarsimp simp: word_neq_0_conv)
        apply (rule shiftl_less_t2n)
         apply (simp add: table_size_def le_mask_iff_lt_2n[THEN iffD1])
        apply (simp add: table_size_bounded[unfolded word_bits_def, simplified])
       apply (clarsimp split del: if_split)
       apply (prop_tac "idx << pte_bits = 0")
        apply (rename_tac pt_t')
        apply (cut_tac a="p + (idx << pte_bits)" and pt_t=pt_t' in gsPTs)
        apply clarsimp
        apply (rule ccontr)
        apply (drule_tac y="idx << pte_bits" in pspace_aligned_distinct_None'
                                                [OF pspace_aligned pspace_distinct])
         apply (clarsimp simp: word_neq_0_conv table_size_def)
         apply (rule shiftl_less_t2n, simp)
          apply (erule order_le_less_trans)
          apply (simp add: mask_def bit_simps)
         apply (simp add: bit_simps)
        apply simp
       apply (thin_tac "pte_relation' pte pte'" for pte pte')
       apply (clarsimp simp: pt_bits_def)
       apply (case_tac pt; clarsimp)
       apply (rename_tac vs)
       apply (clarsimp simp: absPageTable0_def)
       apply (rule conjI, clarsimp)
        apply (rule ext, rename_tac offs)
        apply (erule_tac x="ucast offs" in allE, erule impE, rule ucast_leq_mask)
         apply (simp add: bit_simps)
        apply (clarsimp dest!: koTypeOf_pte simp: objBits_simps)
        apply (erule_tac x="ucast offs" in allE)
        apply clarsimp
        apply (rename_tac pte y)
        apply (frule pspace_relation_absD, rule pspace_relation)
        apply clarsimp
        apply (drule_tac x="ucast offs" in bspec)
         apply clarsimp
         apply (rule ucast_leq_mask)
         apply (clarsimp simp: bit_simps)
        apply (clarsimp simp: pte_relation_def ucast_ucast_mask ge_mask_eq vs_index_bits_def)
        apply (erule pspace_valid_objsE, rule valid_objs)
        apply (clarsimp simp: valid_obj_def)
        apply (erule_tac x=offs in allE)
        apply (clarsimp simp: wellformed_pte_def)
        apply (case_tac "vs offs"; clarsimp split: if_split_asm)
         apply (rule set_eqI, simp)
         apply (rename_tac x, case_tac x; simp)
        apply (simp add: ucast_ucast_mask ge_mask_eq)
        apply clarsimp
        apply (erule_tac x="ucast off" in allE)
        apply (erule impE)
         apply (rule ucast_leq_mask)
         apply (clarsimp simp: bit_simps)
        apply (clarsimp dest!: koTypeOf_pte simp: objBits_simps)
        apply (frule pspace_relation_absD, rule pspace_relation)
        apply clarsimp
        apply (drule_tac x="ucast off" in bspec)
         apply clarsimp
         apply (rule ucast_leq_mask)
         apply (clarsimp simp: bit_simps)
        apply (clarsimp simp: pte_relation_def ucast_ucast_mask ge_mask_eq vs_index_bits_def)
        apply (case_tac "vs off"; simp add: ucast_leq_mask ppn_len_val)

      (* NormalPT_T is an exact duplicate of the VSRootPT_T case, but I don't see any good way
         to factor out the commonality *)
      apply (in_case "NormalPT_T")
      apply (clarsimp simp: absPageTable_def split del: if_split split: option.splits)
      apply (rule conjI, clarsimp)
       apply (rule sym)
       apply (rule pspace_aligned_distinct_None'[OF pspace_aligned pspace_distinct], assumption)
       apply simp
       apply (case_tac "idx << pte_bits = 0", simp)
       apply (clarsimp simp: word_neq_0_conv)
       apply (rule shiftl_less_t2n)
        apply (simp add: table_size_def le_mask_iff_lt_2n[THEN iffD1])
       apply (simp add: table_size_bounded[unfolded word_bits_def, simplified])
      apply (clarsimp split del: if_split)
      apply (prop_tac "idx << pte_bits = 0")
       apply (rename_tac pt_t')
       apply (cut_tac a="p + (idx << pte_bits)" and pt_t=pt_t' in gsPTs)
       apply clarsimp
       apply (rule ccontr)
       apply (drule_tac y="idx << pte_bits" in pspace_aligned_distinct_None'
                                               [OF pspace_aligned pspace_distinct])
        apply (clarsimp simp: word_neq_0_conv table_size_def)
        apply (rule shiftl_less_t2n, simp)
         apply (erule order_le_less_trans)
         apply (simp add: mask_def bit_simps)
        apply (simp add: bit_simps)
       apply simp
      apply (thin_tac "pte_relation' pte pte'" for pte pte')
      apply (clarsimp simp: pt_bits_def)
      apply (case_tac pt; clarsimp)
      apply (rename_tac vs)
      apply (clarsimp simp: absPageTable0_def)
      apply (rule conjI, clarsimp)
       apply (rule ext, rename_tac offs)
       apply (erule_tac x="ucast offs" in allE, erule impE, rule ucast_leq_mask)
        apply (simp add: bit_simps)
       apply (clarsimp dest!: koTypeOf_pte simp: objBits_simps)
       apply (erule_tac x="ucast offs" in allE)
       apply clarsimp
       apply (rename_tac pte y)
       apply (frule pspace_relation_absD, rule pspace_relation)
       apply clarsimp
       apply (drule_tac x="ucast offs" in bspec)
        apply clarsimp
        apply (rule ucast_leq_mask)
        apply (clarsimp simp: bit_simps)
       apply (clarsimp simp: pte_relation_def ucast_ucast_mask ge_mask_eq vs_index_bits_def)
       apply (erule pspace_valid_objsE, rule valid_objs)
       apply (clarsimp simp: valid_obj_def)
       apply (erule_tac x=offs in allE)
       apply (clarsimp simp: wellformed_pte_def)
       apply (case_tac "vs offs"; clarsimp split: if_split_asm)
        apply (rule set_eqI, simp)
        apply (rename_tac x, case_tac x; simp)
       apply (simp add: ucast_ucast_mask ge_mask_eq)
      apply clarsimp
      apply (erule_tac x="ucast off" in allE)
      apply (erule impE)
       apply (rule ucast_leq_mask)
       apply (clarsimp simp: bit_simps)
      apply (clarsimp dest!: koTypeOf_pte simp: objBits_simps)
      apply (frule pspace_relation_absD, rule pspace_relation)
      apply clarsimp
      apply (drule_tac x="ucast off" in bspec)
       apply clarsimp
       apply (rule ucast_leq_mask)
       apply (clarsimp simp: bit_simps)
      apply (clarsimp simp: pte_relation_def ucast_ucast_mask ge_mask_eq vs_index_bits_def)
      apply (case_tac "vs off"; simp add: ucast_leq_mask ppn_len_val)

     apply (in_case "DataPage ?p ?sz")
     apply (clarsimp split: if_splits)

    apply (in_case "KOVCPU ?vcpu")
    apply clarsimp
    apply (rename_tac arch_kernel_obj vcpu)
    apply (case_tac arch_kernel_obj;
           clarsimp simp: other_obj_relation_def other_aobj_relation_def pte_relation_def split: if_splits)
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
