(*
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

definition page_base :: "vspace_ref \<Rightarrow> vmpage_size \<Rightarrow> vspace_ref"
  where
  "page_base vaddr vmsize \<equiv> vaddr && ~~ mask (pageBitsForSize vmsize)"


section "Architecture-specific Decode Functions"

definition
  arch_check_irq :: "data \<Rightarrow> (unit,'z::state_ext) se_monad"
where
  "arch_check_irq irq \<equiv> whenE (irq > ucast maxIRQ \<or> irq = ucast irqInvalid) $
                          throwError (RangeError 1 (ucast maxIRQ))"

definition arch_decode_irq_control_invocation ::
  "data \<Rightarrow> data list \<Rightarrow> cslot_ptr \<Rightarrow> cap list \<Rightarrow> (arch_irq_control_invocation,'z::state_ext) se_monad"
  where
  "arch_decode_irq_control_invocation label args src_slot cps \<equiv>
     (if invocation_type label = ArchInvocationLabel RISCVIRQIssueIRQHandler
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
          returnOk $ RISCVIRQControlInvocation irq dest_slot src_slot (trigger \<noteq> 0)
        odE
      else throwError TruncatedMessage
    else throwError IllegalOperation)"

definition attribs_from_word :: "machine_word \<Rightarrow> vm_attributes"
  where
  "attribs_from_word w \<equiv> if \<not> w!!0 then {Execute} else {}"

definition make_user_pte :: "vspace_ref \<Rightarrow> vm_attributes \<Rightarrow> vm_rights \<Rightarrow> pte"
  where
  "make_user_pte addr attr rights \<equiv>
    if rights = {} \<and> attr = {}
    then InvalidPTE
    else PagePTE (ucast (addr >> pageBits)) (attr \<union> {User}) rights"

definition check_slot :: "obj_ref \<Rightarrow> (pte \<Rightarrow> bool) \<Rightarrow> (unit,'z::state_ext) se_monad"
  where
  "check_slot slot test = doE
     pte \<leftarrow> liftE $ get_pte slot;
     unlessE (test pte) $ throwError DeleteFirst
   odE"

type_synonym 'z arch_decoder =
  "data \<Rightarrow> data list \<Rightarrow> cslot_ptr \<Rightarrow> arch_cap \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow>
    (arch_invocation,'z) se_monad"

definition decode_fr_inv_map :: "'z::state_ext arch_decoder"
  where
  "decode_fr_inv_map label args cte cap extra_caps \<equiv> case cap of
     FrameCap p R pgsz dev mapped_address \<Rightarrow>
       if length args > 2 \<and> length extra_caps > 0
       then let
           vaddr = args ! 0;
           rights_mask = args ! 1;
           attr = args ! 2;
           vspace_cap = fst (extra_caps ! 0)
         in doE
           (pt, asid) \<leftarrow> case vspace_cap of
                           ArchObjectCap (PageTableCap pt (Some (asid, _))) \<Rightarrow> returnOk (pt, asid)
                         | _ \<Rightarrow> throwError $ InvalidCapability 1;
           pt' \<leftarrow> lookup_error_on_failure False $ find_vspace_for_asid asid;
           whenE (pt' \<noteq> pt) $ throwError $ InvalidCapability 1;
           pg_bits \<leftarrow> returnOk $ pageBitsForSize pgsz;
           vtop \<leftarrow> returnOk $ vaddr + mask (pageBitsForSize pgsz);
           whenE (vtop \<ge> user_vtop) $ throwError $ InvalidArgument 0;
           check_vp_alignment pgsz vaddr;
           (level, slot) \<leftarrow> liftE $ gets_the $ pt_lookup_slot pt vaddr \<circ> ptes_of;
           unlessE (pt_bits_left level = pg_bits) $
             throwError $ FailedLookup False $ MissingCapability $ pt_bits_left level;
           case mapped_address of
             Some (asid', vaddr') \<Rightarrow> doE
               whenE (asid' \<noteq> asid) (throwError $ InvalidCapability 1);
               whenE (vaddr' \<noteq> vaddr) (throwError $ InvalidArgument 0);
               check_slot slot (Not \<circ> is_PageTablePTE)
             odE
           | None \<Rightarrow> check_slot slot ((=) InvalidPTE);
           vm_rights \<leftarrow> returnOk $ mask_vm_rights R (data_to_rights rights_mask);
           attribs \<leftarrow> returnOk $ attribs_from_word attr;
           pte \<leftarrow> returnOk $ make_user_pte (addrFromPPtr p) attribs vm_rights;
           returnOk $ InvokePage $ PageMap (FrameCap p R pgsz dev (Some (asid,vaddr))) cte (pte,slot)
         odE
       else throwError TruncatedMessage
     | _ \<Rightarrow> fail"

definition decode_frame_invocation :: "'z::state_ext arch_decoder"
  where
  "decode_frame_invocation label args cte cap extra_caps \<equiv>
     if invocation_type label = ArchInvocationLabel RISCVPageMap
     then decode_fr_inv_map label args cte cap extra_caps
     else if invocation_type label = ArchInvocationLabel RISCVPageUnmap
     then returnOk $ InvokePage $ PageUnmap cap cte
     else if invocation_type label = ArchInvocationLabel RISCVPageGetAddress
     then returnOk $ InvokePage $ PageGetAddr (acap_obj cap)
     else throwError IllegalOperation"

definition decode_pt_inv_map :: "'z::state_ext arch_decoder"
  where
  "decode_pt_inv_map label args cte cap extra_caps \<equiv> case cap of
     PageTableCap p mapped_address \<Rightarrow>
       if length args > 1 \<and> length extra_caps > 0
       then let
           vaddr = args ! 0;
           attr = args ! 1;
           vspace_cap = fst (extra_caps ! 0)
         in doE
           whenE (mapped_address \<noteq> None) $ throwError $ InvalidCapability 0;
           (pt, asid) \<leftarrow> case vspace_cap of
                           ArchObjectCap (PageTableCap pt (Some (asid,_))) \<Rightarrow> returnOk (pt, asid)
                         | _ \<Rightarrow> throwError $ InvalidCapability 1;
           whenE (user_vtop \<le> vaddr) $ throwError $ InvalidArgument 0;
           pt' \<leftarrow> lookup_error_on_failure False $ find_vspace_for_asid asid;
           whenE (pt' \<noteq> pt) $ throwError $ InvalidCapability 1;
           (level, slot) \<leftarrow> liftE $ gets_the $ pt_lookup_slot pt vaddr \<circ> ptes_of;
           old_pte \<leftarrow> liftE $ get_pte slot;
           whenE (pt_bits_left level = pageBits \<or> old_pte \<noteq> InvalidPTE) $ throwError DeleteFirst;
           pte \<leftarrow> returnOk $ PageTablePTE (ucast (addrFromPPtr p >> pageBits)) {};
           cap' <- returnOk $ PageTableCap p $ Some (asid, vaddr && ~~mask (pt_bits_left level));
           returnOk $ InvokePageTable $ PageTableMap cap' cte pte slot
         odE
       else throwError TruncatedMessage
     | _ \<Rightarrow> fail"

definition decode_page_table_invocation :: "'z::state_ext arch_decoder"
  where
  "decode_page_table_invocation label args cte cap extra_caps \<equiv>
     if invocation_type label = ArchInvocationLabel RISCVPageTableMap
     then decode_pt_inv_map label args cte cap extra_caps
     else if invocation_type label = ArchInvocationLabel RISCVPageTableUnmap
     then doE
       final \<leftarrow> liftE $ is_final_cap (ArchObjectCap cap);
       unlessE final $ throwError RevokeFirst;
       case cap of
         PageTableCap pt (Some (asid, _)) \<Rightarrow> doE
             \<comment> \<open>cannot invoke unmap on top level page table\<close>
             pt_opt \<leftarrow> liftE $ gets $ vspace_for_asid asid;
             whenE (pt_opt = Some pt) $ throwError RevokeFirst
           odE
       | _ \<Rightarrow> returnOk ();
       returnOk $ InvokePageTable $ PageTableUnmap cap cte
     odE
     else throwError IllegalOperation"

definition decode_asid_control_invocation :: "'z::state_ext arch_decoder"
  where
  "decode_asid_control_invocation label args cte cap extra_caps \<equiv>
     if invocation_type label = ArchInvocationLabel RISCVASIDControlMakePool
     then if length args > 1 \<and> length extra_caps > 1
     then let
         index = args ! 0;
         depth = args ! 1;
         (untyped, parent_slot) = extra_caps ! 0;
         root = fst (extra_caps ! 1)
       in doE
         asid_table \<leftarrow> liftE $ gets (riscv_asid_table \<circ> arch_state);
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

definition decode_asid_pool_invocation :: "'z::state_ext arch_decoder"
  where
  "decode_asid_pool_invocation label args cte cap extra_caps \<equiv>
     if invocation_type label = ArchInvocationLabel RISCVASIDPoolAssign
     then if length extra_caps > 0
     then let
         (pt_cap, pt_cap_slot) = extra_caps ! 0;
         p = acap_obj cap;
         base = acap_asid_base cap
       in case pt_cap of
         ArchObjectCap (PageTableCap _ None) \<Rightarrow> doE
           asid_table \<leftarrow> liftE $ gets (riscv_asid_table \<circ> arch_state);
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

definition arch_decode_invocation ::
  "data \<Rightarrow> data list \<Rightarrow> cap_ref \<Rightarrow> cslot_ptr \<Rightarrow> arch_cap \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow>
    (arch_invocation,'z::state_ext) se_monad"
  where
  "arch_decode_invocation label args x_slot cte cap extra_caps \<equiv> case cap of
     PageTableCap _ _   \<Rightarrow> decode_page_table_invocation label args cte cap extra_caps
   | FrameCap _ _ _ _ _ \<Rightarrow> decode_frame_invocation label args cte cap extra_caps
   | ASIDControlCap     \<Rightarrow> decode_asid_control_invocation label args cte cap extra_caps
   | ASIDPoolCap _ _    \<Rightarrow> decode_asid_pool_invocation label args cte cap extra_caps"


section "Interface Functions used in Decode"

definition arch_data_to_obj_type :: "nat \<Rightarrow> aobject_type option"
  where
  "arch_data_to_obj_type n \<equiv>
     if      n = 0 then Some HugePageObj
     else if n = 1 then Some SmallPageObj
     else if n = 2 then Some LargePageObj
     else if n = 3 then Some PageTableObj
     else None"

end
end
