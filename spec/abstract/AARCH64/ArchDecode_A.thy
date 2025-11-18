(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Decoding Architecture-specific System Calls"

theory ArchDecode_A
imports
  Interrupt_A
  InvocationLabels_A
  "ExecSpec.InvocationLabels_H"
begin

context Arch begin arch_global_naming (A)

section "Helper definitions"

definition check_vp_alignment :: "vmpage_size \<Rightarrow> machine_word \<Rightarrow> (unit,'z::state_ext) se_monad"
  where
  "check_vp_alignment sz vptr \<equiv>
     unlessE (is_aligned vptr (pageBitsForSize sz)) $ throwError AlignmentError"

definition page_base :: "vspace_ref \<Rightarrow> vmpage_size \<Rightarrow> vspace_ref" where
  "page_base vaddr vmsize \<equiv> vaddr && ~~ mask (pageBitsForSize vmsize)"


section "Architecture-specific Decode Functions"

definition sgi_target_valid :: "machine_word \<Rightarrow> bool" where
  "sgi_target_valid t \<equiv> t \<le> of_nat gicNumTargets - 1"

definition arch_decode_irq_control_invocation ::
  "data \<Rightarrow> data list \<Rightarrow> cslot_ptr \<Rightarrow> cap list \<Rightarrow> (arch_irq_control_invocation,'z::state_ext) se_monad"
  where
  "arch_decode_irq_control_invocation label args src_slot cps \<equiv>
     (if invocation_type label = ArchInvocationLabel ARMIRQIssueIRQHandlerTrigger
      then if length args \<ge> 4 \<and> length cps \<ge> 1
        then let irq_word = args ! 0;
                 trigger = args ! 1;
                 index = args ! 2;
                 depth = args ! 3;
                 cnode = cps ! 0;
                 irq = ucast irq_word
        in doE
          arch_check_irq irq_word;
          irq_active \<leftarrow> liftE $ is_irq_active irq;
          whenE irq_active $ throwError RevokeFirst;
          dest_slot \<leftarrow> lookup_target_slot cnode (data_to_cptr index) (unat depth);
          ensure_empty dest_slot;
          returnOk $ ARMIRQControlInvocation irq dest_slot src_slot (trigger \<noteq> 0)
        odE
        else throwError TruncatedMessage
      else if invocation_type label = ArchInvocationLabel ARMIRQIssueSGISignal
      then if length args \<ge> 4 \<and> length cps \<ge> 1
        then let irq_word = args ! 0;
                 target_word = args ! 1;
                 index = args ! 2;
                 depth = args ! 3;
                 cnode = cps ! 0
        in doE
          range_check irq_word 0 (of_nat numSGIs - 1);
          unlessE (sgi_target_valid target_word) $ throwError $ InvalidArgument 1;
          dest_slot \<leftarrow> lookup_target_slot cnode (data_to_cptr index) (unat depth);
          ensure_empty dest_slot;
          returnOk $ IssueSGISignal (ucast irq_word) (ucast target_word) src_slot dest_slot
        odE
        else throwError TruncatedMessage
      else throwError IllegalOperation)"

definition attribs_from_word :: "machine_word \<Rightarrow> vm_attributes" where
  "attribs_from_word w \<equiv> {attr.  \<not>w!!0 \<and> attr = Device \<or> \<not>w !! 2 \<and> attr = Execute}"

definition make_user_pte :: "paddr \<Rightarrow> vm_attributes \<Rightarrow> vm_rights \<Rightarrow> vmpage_size \<Rightarrow> pte" where
  "make_user_pte addr attr rights vm_size \<equiv>
     PagePTE addr (vm_size = ARMSmallPage) (attr - {Global}) rights"

definition check_vspace_root :: "cap \<Rightarrow> nat \<Rightarrow> (obj_ref \<times> asid, 'z) se_monad" where
  "check_vspace_root cap arg_no \<equiv>
     case cap of
       ArchObjectCap (PageTableCap pt VSRootPT_T (Some (asid, _))) \<Rightarrow> returnOk (pt, asid)
     | _ \<Rightarrow> throwError $ InvalidCapability arg_no"

type_synonym 'z arch_decoder =
  "data \<Rightarrow> data list \<Rightarrow> cslot_ptr \<Rightarrow> arch_cap \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow>
    (arch_invocation,'z) se_monad"

definition decode_fr_inv_map :: "'z::state_ext arch_decoder" where
  "decode_fr_inv_map label args cte cap extra_caps \<equiv> case cap of
     FrameCap p R pgsz dev mapped_address \<Rightarrow>
       if length args > 2 \<and> length extra_caps > 0
       then let
           vaddr = args ! 0;
           rights_mask = args ! 1;
           attr = args ! 2;
           vspace_cap = fst (extra_caps ! 0)
         in doE
           (pt, asid) \<leftarrow> check_vspace_root vspace_cap 1;
           pt' \<leftarrow> lookup_error_on_failure False $ find_vspace_for_asid asid;
           whenE (pt' \<noteq> pt) $ throwError $ InvalidCapability 1;
           check_vp_alignment pgsz vaddr;
           pg_bits \<leftarrow> returnOk $ pageBitsForSize pgsz;
           case mapped_address of
             Some (asid', vaddr') \<Rightarrow> doE
               whenE (asid' \<noteq> asid) $ throwError $ InvalidCapability 1;
               whenE (vaddr' \<noteq> vaddr) $ throwError $ InvalidArgument 0
             odE
           | None \<Rightarrow> doE
               vtop \<leftarrow> returnOk $ vaddr + mask (pageBitsForSize pgsz);
               whenE (vtop > user_vtop) $ throwError $ InvalidArgument 0
             odE;
           (level, slot) \<leftarrow> liftE $ gets_the $ pt_lookup_slot pt vaddr \<circ> ptes_of;
           unlessE (pt_bits_left level = pg_bits) $
             throwError $ FailedLookup False $ MissingCapability $ pt_bits_left level;
           vm_rights \<leftarrow> returnOk $ mask_vm_rights R (data_to_rights rights_mask);
           attribs \<leftarrow> returnOk $ attribs_from_word attr;
           pte \<leftarrow> returnOk $ make_user_pte (addrFromPPtr p) attribs vm_rights pgsz;
           returnOk $ InvokePage $ PageMap (FrameCap p R pgsz dev (Some (asid,vaddr))) cte
                                           (pte,slot,level)
         odE
       else throwError TruncatedMessage
     | _ \<Rightarrow> fail"

definition label_to_flush_type :: "data \<Rightarrow> flush_type" where
  "label_to_flush_type label \<equiv>
     case invocation_type label of
       ArchInvocationLabel ARMVSpaceClean_Data \<Rightarrow> Clean
     | ArchInvocationLabel ARMPageClean_Data \<Rightarrow> Clean
     | ArchInvocationLabel ARMVSpaceInvalidate_Data \<Rightarrow> Invalidate
     | ArchInvocationLabel ARMPageInvalidate_Data \<Rightarrow> Invalidate
     | ArchInvocationLabel ARMVSpaceCleanInvalidate_Data \<Rightarrow> CleanInvalidate
     | ArchInvocationLabel ARMPageCleanInvalidate_Data \<Rightarrow> CleanInvalidate
     | ArchInvocationLabel ARMVSpaceUnify_Instruction \<Rightarrow> Unify
     | ArchInvocationLabel ARMPageUnify_Instruction \<Rightarrow> Unify"

definition decode_fr_inv_flush :: "'z::state_ext arch_decoder" where
  "decode_fr_inv_flush label args cte cap extra_caps \<equiv> case cap of
     FrameCap p R pgsz dev mapped_address \<Rightarrow>
        if length args > 1
        then let
          start = args ! 0;
          end = args ! 1
        in doE
          (asid, vaddr) \<leftarrow> case mapped_address of
                             Some a \<Rightarrow> returnOk a
                           | _ \<Rightarrow> throwError IllegalOperation;
          vspace \<leftarrow> lookup_error_on_failure False $ find_vspace_for_asid asid;
          whenE (end \<le> start) $ throwError $ InvalidArgument 1;
          page_size \<leftarrow> returnOk $ 1 << pageBitsForSize pgsz;
          whenE (start \<ge> page_size \<or> end > page_size) $ throwError $ InvalidArgument 0;
          pstart \<leftarrow> returnOk $ addrFromPPtr p + start;
          \<comment> \<open>flush only inside the kernel window:\<close>
          whenE (pstart < paddrBase \<or> ((end - start) + pstart > paddrTop)) $
            throwError IllegalOperation;
          returnOk $ InvokePage $
            PageFlush (label_to_flush_type label)
                      (vaddr + start) (vaddr + end - 1)
                      pstart vspace asid
        odE
        else throwError TruncatedMessage
   | _ \<Rightarrow> fail"


definition decode_frame_invocation :: "'z::state_ext arch_decoder" where
  "decode_frame_invocation label args cte cap extra_caps \<equiv>
     if invocation_type label = ArchInvocationLabel ARMPageMap
     then decode_fr_inv_map label args cte cap extra_caps
     else if invocation_type label = ArchInvocationLabel ARMPageUnmap
     then returnOk $ InvokePage $ PageUnmap cap cte
     else if invocation_type label = ArchInvocationLabel ARMPageGetAddress
     then returnOk $ InvokePage $ PageGetAddr (acap_obj cap)
     else if isPageFlushLabel (invocation_type label)
     then decode_fr_inv_flush label args cte cap extra_caps
     else throwError IllegalOperation"

definition decode_pt_inv_map :: "'z::state_ext arch_decoder" where
  "decode_pt_inv_map label args cte cap extra_caps \<equiv> case cap of
     PageTableCap p t mapped_address \<Rightarrow>
       if length args > 1 \<and> length extra_caps > 0
       then let
           vaddr = args ! 0;
           attr = args ! 1;
           vspace_cap = fst (extra_caps ! 0)
         in doE
           whenE (mapped_address \<noteq> None) $ throwError $ InvalidCapability 0;
           (pt, asid) \<leftarrow> check_vspace_root vspace_cap 1;
           whenE (user_vtop < vaddr) $ throwError $ InvalidArgument 0;
           pt' \<leftarrow> lookup_error_on_failure False $ find_vspace_for_asid asid;
           whenE (pt' \<noteq> pt) $ throwError $ InvalidCapability 1;
           (level, slot) \<leftarrow> liftE $ gets_the $ pt_lookup_slot pt vaddr \<circ> ptes_of;
           old_pte \<leftarrow> liftE $ get_pte (level_type level) slot;
           whenE (pt_bits_left level = pageBits \<or> old_pte \<noteq> InvalidPTE) $ throwError DeleteFirst;
           pte \<leftarrow> returnOk $ PageTablePTE (ppn_from_pptr p);
           cap' <- returnOk $ PageTableCap p t $ Some (asid, vaddr && ~~mask (pt_bits_left level));
           returnOk $ InvokePageTable $ PageTableMap cap' cte pte slot level
         odE
       else throwError TruncatedMessage
     | _ \<Rightarrow> fail"

definition decode_page_table_invocation :: "'z::state_ext arch_decoder" where
  "decode_page_table_invocation label args cte cap extra_caps \<equiv>
     if invocation_type label = ArchInvocationLabel ARMPageTableMap
     then decode_pt_inv_map label args cte cap extra_caps
     else if invocation_type label = ArchInvocationLabel ARMPageTableUnmap
     then doE
       final \<leftarrow> liftE $ is_final_cap (ArchObjectCap cap);
       unlessE final $ throwError RevokeFirst;
       returnOk $ InvokePageTable $ PageTableUnmap cap cte
     odE
     else throwError IllegalOperation"

definition level_of_vmsize :: "vmpage_size \<Rightarrow> vm_level" where
  "level_of_vmsize vmsz \<equiv>
     case vmsz of
       ARMSmallPage \<Rightarrow> 0
     | ARMLargePage \<Rightarrow> 1
     | ARMHugePage \<Rightarrow> 2"

definition vmsize_of_level :: "vm_level \<Rightarrow> vmpage_size" where
  "vmsize_of_level level \<equiv>
     if level = 0 then ARMSmallPage
     else if level = 1 then ARMLargePage
     else ARMHugePage"

definition lookup_frame :: "obj_ref \<Rightarrow> vspace_ref \<Rightarrow> ptes_of \<Rightarrow> (vmpage_size \<times> paddr) option" where
  "lookup_frame vspace vaddr = do {
     (level, slot) \<leftarrow> pt_lookup_slot vspace vaddr;
     pte \<leftarrow> oapply2 (level_type level) slot;
     oassert (is_PagePTE pte);
     oassert (level \<le> 2);
     oreturn (vmsize_of_level level, pte_base_addr pte)
   }"

definition decode_vs_inv_flush :: "'z::state_ext arch_decoder" where
  "decode_vs_inv_flush label args cte cap extra_caps \<equiv> case cap of
     PageTableCap p VSRootPT_T mapped_address \<Rightarrow>
        if length args > 1
        then let
          start = args ! 0;
          end = args ! 1
        in doE
          whenE (end \<le> start) $ throwError $ InvalidArgument 1;
          whenE (end > pptrUserTop) $ throwError $ IllegalOperation;
          (vspace, asid) \<leftarrow> check_vspace_root (ArchObjectCap cap) 0;
          vspace' \<leftarrow> lookup_error_on_failure False $ find_vspace_for_asid asid;
          whenE (vspace' \<noteq> vspace) $ throwError $ InvalidCapability 0;
          frame_info \<leftarrow> liftE $ gets $ lookup_frame p start \<circ> ptes_of;
          case frame_info of
            None \<Rightarrow> returnOk $ InvokeVSpace VSpaceNothing
          | Some (pgsz, paddr) \<Rightarrow> doE
              bits_left  \<leftarrow> returnOk $ pt_bits_left (level_of_vmsize pgsz);
              base_start \<leftarrow> returnOk $ page_base start pgsz;
              base_end \<leftarrow> returnOk $ page_base (end - 1) pgsz;
              whenE (base_start \<noteq> base_end) $
                throwError $ RangeError start (base_start + mask bits_left);
              pstart \<leftarrow> returnOk $ paddr + (start && mask bits_left);
              returnOk $ InvokeVSpace $
                VSpaceFlush (label_to_flush_type label) start (end - 1) pstart vspace asid
            odE
        odE
        else throwError TruncatedMessage
   | _ \<Rightarrow> fail"

definition decode_vspace_invocation :: "'z::state_ext arch_decoder" where
  "decode_vspace_invocation label args cte cap extra_caps \<equiv>
     if isVSpaceFlushLabel (invocation_type label)
     then decode_vs_inv_flush label args cte cap extra_caps
     else throwError IllegalOperation"

definition decode_asid_control_invocation :: "'z::state_ext arch_decoder" where
  "decode_asid_control_invocation label args cte cap extra_caps \<equiv>
     if invocation_type label = ArchInvocationLabel ARMASIDControlMakePool
     then if length args > 1 \<and> length extra_caps > 1
     then let
         index = args ! 0;
         depth = args ! 1;
         (untyped, parent_slot) = extra_caps ! 0;
         root = fst (extra_caps ! 1)
       in doE
         asid_table \<leftarrow> liftE $ gets asid_table;
         free_set \<leftarrow> returnOk (- dom asid_table);
         whenE (free_set = {}) $ throwError DeleteFirst;
         free \<leftarrow> liftE $ select_ext (\<lambda>_. free_asid_select asid_table) free_set;
         base \<leftarrow> returnOk (ucast free << asid_low_bits);
         (p,n) \<leftarrow> case untyped of
                    UntypedCap False p n _ \<Rightarrow> returnOk (p,n)
                  | _ \<Rightarrow> throwError $ InvalidCapability 1;
         frame \<leftarrow> if n = pageBits then doE
                    ensure_no_children parent_slot;
                    returnOk p
                  odE
                  else throwError $ InvalidCapability 1;
         dest_slot \<leftarrow> lookup_target_slot root (to_bl index) (unat depth);
         ensure_empty dest_slot;
         returnOk $ InvokeASIDControl $ MakePool frame dest_slot parent_slot base
       odE
     else throwError TruncatedMessage
     else throwError IllegalOperation"

definition decode_asid_pool_invocation :: "'z::state_ext arch_decoder" where
  "decode_asid_pool_invocation label args cte cap extra_caps \<equiv>
     if invocation_type label = ArchInvocationLabel ARMASIDPoolAssign
     then if length extra_caps > 0
     then let
         (pt_cap, pt_cap_slot) = extra_caps ! 0;
         p = acap_obj cap;
         base = acap_asid_base cap
       in case pt_cap of
         ArchObjectCap (PageTableCap _ VSRootPT_T None) \<Rightarrow> doE
           asid_table \<leftarrow> liftE $ gets asid_table;
           pool_ptr \<leftarrow> returnOk (asid_table (asid_high_bits_of base));
           whenE (pool_ptr = None) $ throwError $ FailedLookup False InvalidRoot;
           whenE (p \<noteq> the pool_ptr) $ throwError $ InvalidCapability 0;
           pool \<leftarrow> liftE $ get_asid_pool p;
           free_set \<leftarrow> returnOk (- dom pool \<inter> {x. ucast x + base \<noteq> 0});
           whenE (free_set = {}) $ throwError DeleteFirst;
           offset \<leftarrow> liftE $ select_ext (\<lambda>_. free_asid_pool_select pool base) free_set;
           returnOk $ InvokeASIDPool $ Assign (ucast offset + base) p pt_cap_slot
         odE
       | _ \<Rightarrow> throwError $ InvalidCapability 1
     else throwError TruncatedMessage
     else throwError IllegalOperation"

definition decode_sgi_signal_invocation :: "arch_cap \<Rightarrow> (arch_invocation,'z::state_ext) se_monad" where
  "decode_sgi_signal_invocation acap \<equiv>
     case acap of
       SGISignalCap irq target \<Rightarrow> returnOk $ InvokeSGISignal $ SGISignalGenerate irq target
     | _ \<Rightarrow> fail"

definition arch_decode_invocation ::
  "data \<Rightarrow> data list \<Rightarrow> cap_ref \<Rightarrow> cslot_ptr \<Rightarrow> arch_cap \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow>
    (arch_invocation,'z::state_ext) se_monad"
  where
  "arch_decode_invocation label args x_slot cte cap extra_caps \<equiv> case cap of
     PageTableCap _ VSRootPT_T _ \<Rightarrow> decode_vspace_invocation label args cte cap extra_caps
   | PageTableCap _ NormalPT_T _ \<Rightarrow> decode_page_table_invocation label args cte cap extra_caps
   | FrameCap _ _ _ _ _          \<Rightarrow> decode_frame_invocation label args cte cap extra_caps
   | ASIDControlCap              \<Rightarrow> decode_asid_control_invocation label args cte cap extra_caps
   | ASIDPoolCap _ _             \<Rightarrow> decode_asid_pool_invocation label args cte cap extra_caps
   | VCPUCap _                   \<Rightarrow> decode_vcpu_invocation label args cap extra_caps
   | SGISignalCap _ _            \<Rightarrow> decode_sgi_signal_invocation cap"

section "Interface Functions used in Decode"

definition arch_data_to_obj_type :: "nat \<Rightarrow> aobject_type option" where
  "arch_data_to_obj_type n \<equiv>
     if      n = 0 then Some HugePageObj
     else if n = 1 then Some VSpaceObj
     else if n = 2 then Some SmallPageObj
     else if n = 3 then Some LargePageObj
     else if n = 4 then Some PageTableObj
     else if n = 5 then Some VCPUObj
     else None"

end
end
