(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Decoding system calls
*)

chapter "Decoding Architecture-specific System Calls"

theory ArchDecode_A
imports
  Interrupt_A
begin
context Arch begin global_naming ARM_HYP_A

section "Helper definitions"

text \<open>This definition ensures that the given pointer is aligned
to the given page size.\<close>

definition
  check_vp_alignment :: "vmpage_size \<Rightarrow> word32 \<Rightarrow> (unit,'z::state_ext) se_monad" where
  "check_vp_alignment sz vptr \<equiv>
     unlessE (is_aligned vptr (pageBitsForSize sz)) $
       throwError AlignmentError"

text \<open>This definition converts a user-supplied argument into an
invocation label, used to determine the method to invoke.
\<close>

definition
  label_to_flush_type :: "invocation_label \<Rightarrow> flush_type"
where
  "label_to_flush_type label \<equiv> case label of
       ArchInvocationLabel ARMPDClean_Data \<Rightarrow> Clean
     | ArchInvocationLabel ARMPageClean_Data \<Rightarrow> Clean
     | ArchInvocationLabel ARMPDInvalidate_Data \<Rightarrow> Invalidate
     | ArchInvocationLabel ARMPageInvalidate_Data \<Rightarrow> Invalidate
     | ArchInvocationLabel ARMPDCleanInvalidate_Data \<Rightarrow> CleanInvalidate
     | ArchInvocationLabel ARMPageCleanInvalidate_Data \<Rightarrow> CleanInvalidate
     | ArchInvocationLabel ARMPDUnify_Instruction \<Rightarrow> Unify
     | ArchInvocationLabel ARMPageUnify_Instruction \<Rightarrow> Unify"

section "Architecture calls"

text \<open>This definition decodes architecture-specific invocations.
\<close>

definition
  page_base :: "vspace_ref \<Rightarrow> vmpage_size \<Rightarrow> vspace_ref"
where
  "page_base vaddr vmsize \<equiv> vaddr && ~~ mask (pageBitsForSize vmsize)"


(* decode mmu invocations *)

definition
  isIOSpaceFrame :: "arch_cap \<Rightarrow> bool"
  where "isIOSpaceFrame c \<equiv> False"

definition
  decode_mmu_invocation ::
  "data \<Rightarrow> data list \<Rightarrow> cap_ref \<Rightarrow> cslot_ptr \<Rightarrow> arch_cap \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow>
   (arch_invocation,'z::state_ext) se_monad"
where
  "decode_mmu_invocation label args x_slot cte cap extra_caps \<equiv>
case cap of

  PageDirectoryCap _ _ \<Rightarrow>
    if isPDFlushLabel (invocation_type label) then
    if length args > 1
    then let start = args ! 0;
             end = args ! 1
    in doE
            whenE (end \<le> start) $ throwError $ InvalidArgument 1;
            whenE (start \<ge> kernel_base \<or> end > kernel_base) $ throwError IllegalOperation;
            (pd,asid) \<leftarrow> (case cap of
                    PageDirectoryCap pd (Some asid) \<Rightarrow> returnOk (pd,asid)
                  | _ \<Rightarrow> throwError $ InvalidCapability 0);
            pd' \<leftarrow> lookup_error_on_failure False $ find_pd_for_asid asid;
            whenE (pd' \<noteq> pd) $ throwError $ InvalidCapability 0;
            frame_info \<leftarrow> liftE $ resolve_vaddr pd start;
            case frame_info of
                None \<Rightarrow> returnOk $ InvokePageDirectory PageDirectoryNothing
              | Some (frame_size, frame_base) \<Rightarrow>
                    let base_start = page_base start frame_size;
                        base_end = page_base (end - 1) frame_size;
                        offset = start && mask (pageBitsForSize frame_size);
                        pstart = frame_base + offset
                    in doE
                        whenE (base_start \<noteq> base_end) $ throwError $
                            RangeError start (base_start + mask (pageBitsForSize frame_size));
                        returnOk $ InvokePageDirectory $
                            PageDirectoryFlush (label_to_flush_type (invocation_type label))
                            start (end - 1) pstart pd asid
                    odE
    odE
    else throwError TruncatedMessage
    else throwError IllegalOperation

| PageTableCap p mapped_address \<Rightarrow>
    if invocation_type label = ArchInvocationLabel ARMPageTableMap then
    if length args > 1 \<and> length extra_caps > 0
    then let vaddr = args ! 0;
             pd_cap = fst (extra_caps ! 0)
    in doE
            whenE (mapped_address \<noteq> None) $ throwError $ InvalidCapability 0;
            (pd,asid) \<leftarrow> (case pd_cap of
                            ArchObjectCap (PageDirectoryCap pd (Some asid)) \<Rightarrow>
                              returnOk (pd,asid)
                         | _ \<Rightarrow> throwError $ InvalidCapability 1);
            whenE (vaddr \<ge> kernel_base) $ throwError $ InvalidArgument 0;
            pd' \<leftarrow> lookup_error_on_failure False $ find_pd_for_asid asid;
            whenE (pd' \<noteq> pd) $ throwError $ InvalidCapability 1;
            pd_index \<leftarrow> returnOk (shiftr vaddr (pageBits + pt_bits - pte_bits));
            vaddr' \<leftarrow> returnOk (vaddr && ~~ mask (pageBits + pt_bits - pte_bits));
            pd_slot \<leftarrow> returnOk (pd + (pd_index << pde_bits));
            oldpde \<leftarrow> liftE $ get_master_pde pd_slot;
            unlessE (oldpde = InvalidPDE) $ throwError DeleteFirst;
            pde \<leftarrow> returnOk (PageTablePDE (addrFromPPtr p));
            returnOk $ InvokePageTable $
                PageTableMap
                (ArchObjectCap $ PageTableCap p (Some (asid, vaddr')))
                cte pde pd_slot
    odE
    else throwError TruncatedMessage
    else if invocation_type label = ArchInvocationLabel ARMPageTableUnmap
    then doE
            final \<leftarrow> liftE $ is_final_cap (ArchObjectCap cap);
            unlessE final $ throwError RevokeFirst;
            returnOk $ InvokePageTable $ PageTableUnmap (ArchObjectCap cap) cte
    odE
    else throwError IllegalOperation

| PageCap dev p R pgsz mapped_address \<Rightarrow>
    if invocation_type label = ArchInvocationLabel ARMPageMap then
    if length args > 2 \<and> length extra_caps > 0
    then let vaddr = args ! 0;
             rights_mask = args ! 1;
             attr = args ! 2;
             pd_cap = fst (extra_caps ! 0)
        in doE
            (pd,asid) \<leftarrow> (case pd_cap of
                            ArchObjectCap (PageDirectoryCap pd (Some asid)) \<Rightarrow>
                              returnOk (pd,asid)
                         | _ \<Rightarrow> throwError $ InvalidCapability 1);
            case mapped_address of
              Some (asid', vaddr') \<Rightarrow> doE
                whenE (asid' \<noteq> asid) (throwError $ InvalidCapability 1);
                whenE (vaddr' \<noteq> vaddr) (throwError $ InvalidArgument 0)
              odE
            | None \<Rightarrow> doE
                vtop \<leftarrow> returnOk (vaddr + (1 << (pageBitsForSize pgsz)) - 1);
                whenE (vtop \<ge> kernel_base) $ throwError $ InvalidArgument 0
              odE;
            pd' \<leftarrow> lookup_error_on_failure False $ find_pd_for_asid asid;
            whenE (pd' \<noteq> pd) $ throwError $ InvalidCapability 1;
            vm_rights \<leftarrow> returnOk (mask_vm_rights R (data_to_rights rights_mask));
            check_vp_alignment pgsz vaddr;
            entries \<leftarrow> create_mapping_entries (addrFromPPtr p)
                                              vaddr pgsz vm_rights
                                              (attribs_from_word attr) pd;
            ensure_safe_mapping entries;
            returnOk $ InvokePage $ PageMap asid
                (ArchObjectCap $ PageCap dev p R pgsz (Some (asid, vaddr)))
                cte entries
        odE
    else throwError TruncatedMessage
    else if invocation_type label = ArchInvocationLabel ARMPageUnmap
    then  returnOk $ InvokePage $ PageUnmap cap cte
    else if isPageFlushLabel (invocation_type label) then
        if length args > 1
        then let start = args ! 0;
                 end = args ! 1;
                 pstart = start + addrFromPPtr p
        in doE
            (asid, _) \<leftarrow> (case mapped_address of
                Some a \<Rightarrow> returnOk a
              | _ \<Rightarrow> throwError IllegalOperation);
            pd \<leftarrow> lookup_error_on_failure False $ find_pd_for_asid asid;
            whenE (end \<le> start) $ throwError $ InvalidArgument 1;
            page_size \<leftarrow> returnOk $ 1 << pageBitsForSize pgsz;
            whenE (start \<ge> page_size \<or> end > page_size) $ throwError $ InvalidArgument 0;
            whenE (pstart < physBase \<or> ((end - start) + pstart) > paddrTop) $ throwError IllegalOperation;
            returnOk $ InvokePage $ PageFlush
                (label_to_flush_type (invocation_type label)) (start + p) \<comment> \<open>check\<close>
                (end + p - 1) pstart pd asid
    odE
    else throwError TruncatedMessage
    else if invocation_type label = ArchInvocationLabel ARMPageGetAddress
    then returnOk $ InvokePage $ PageGetAddr p
  else  throwError IllegalOperation

| ASIDControlCap \<Rightarrow>
    if invocation_type label = ArchInvocationLabel ARMASIDControlMakePool then
    if length args > 1 \<and> length extra_caps > 1
    then let index = args ! 0;
             depth = args ! 1;
             (untyped, parent_slot) = extra_caps ! 0;
             root = fst (extra_caps ! 1)
         in doE
            asid_table \<leftarrow> liftE $ gets (arm_asid_table \<circ> arch_state);
            free_set \<leftarrow> returnOk (- dom asid_table \<inter> {x. x \<le> (1 << asid_high_bits) - 1});
            whenE (free_set = {}) $ throwError DeleteFirst;
            free \<leftarrow> liftE $ select_ext (\<lambda>_. free_asid_select asid_table) free_set;
            base \<leftarrow> returnOk (ucast free << asid_low_bits);
            (p,n) \<leftarrow> (case untyped of UntypedCap False p n f \<Rightarrow> returnOk (p,n)
                                    | _ \<Rightarrow> throwError $ InvalidCapability 1);
            frame \<leftarrow> (if n = pageBits
                      then doE
                        ensure_no_children parent_slot;
                        returnOk p
                      odE
                      else  throwError $ InvalidCapability 1);
            dest_slot \<leftarrow> lookup_target_slot root (to_bl index) (unat depth);
            ensure_empty dest_slot;
            returnOk $ InvokeASIDControl $ MakePool frame dest_slot parent_slot base
        odE
    else  throwError TruncatedMessage
    else  throwError IllegalOperation

| ASIDPoolCap p base \<Rightarrow>
  if invocation_type label = ArchInvocationLabel ARMASIDPoolAssign then
  if length extra_caps > 0
  then
    let (pd_cap, pd_cap_slot) = extra_caps ! 0
     in case pd_cap of
          ArchObjectCap (PageDirectoryCap _ None) \<Rightarrow> doE
            asid_table \<leftarrow> liftE $ gets (arm_asid_table \<circ> arch_state);
            pool_ptr \<leftarrow> returnOk (asid_table (asid_high_bits_of base));
            whenE (pool_ptr = None) $ throwError $ FailedLookup False InvalidRoot;
            whenE (p \<noteq> the pool_ptr) $ throwError $ InvalidCapability 0;
            pool \<leftarrow> liftE $ get_asid_pool p;
            free_set \<leftarrow> returnOk (- dom pool \<inter> {x. ucast x + base \<noteq> 0});
            whenE (free_set = {}) $ throwError DeleteFirst;
            offset \<leftarrow> liftE $ select_ext (\<lambda>_. free_asid_pool_select pool base) free_set;
            returnOk $ InvokeASIDPool $ Assign (ucast offset + base) p pd_cap_slot
          odE
        | _ \<Rightarrow>  throwError $ InvalidCapability 1
  else  throwError TruncatedMessage
  else  throwError IllegalOperation
| VCPUCap p \<Rightarrow> fail \<comment> \<open>not an MMU invocation\<close>"

(* arch decode invocations *)

definition
  arch_decode_invocation ::
  "data \<Rightarrow> data list \<Rightarrow> cap_ref \<Rightarrow> cslot_ptr \<Rightarrow> arch_cap \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow>
   (arch_invocation,'z::state_ext) se_monad"
where
  "arch_decode_invocation label args x_slot cte cap extra_caps \<equiv> case cap of
 VCPUCap _ \<Rightarrow> decode_vcpu_invocation label args cap extra_caps
\<comment> \<open>arm-hyp: add cases for iommu\<close>
| _ \<Rightarrow> decode_mmu_invocation label args x_slot cte cap extra_caps"

definition
  arch_data_to_obj_type :: "nat \<Rightarrow> aobject_type option" where
 "arch_data_to_obj_type n \<equiv>
  if n = 0 then Some PageDirectoryObj
  else if n = 1 then Some SmallPageObj
  else if n = 2 then Some LargePageObj
  else if n = 3 then Some SectionObj
  else if n = 4 then Some SuperSectionObj
  else if n = 5 then Some PageTableObj
  else if n = 6 then Some VCPUObj
  else None"

definition arch_decode_irq_control_invocation ::
  "data \<Rightarrow> data list \<Rightarrow> cslot_ptr \<Rightarrow> cap list \<Rightarrow> (arch_irq_control_invocation,'z::state_ext) se_monad"
  where
  "arch_decode_irq_control_invocation label args src_slot cps \<equiv>
    (if invocation_type label = ArchInvocationLabel ARMIRQIssueIRQHandler
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

          returnOk $ ArchIRQControlIssue irq dest_slot src_slot (trigger \<noteq> 0)
        odE
      else throwError TruncatedMessage
    else throwError IllegalOperation)"

end

end
