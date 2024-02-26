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
  InvocationLabels_A
  "ExecSpec.InvocationLabels_H"
begin

context Arch begin global_naming X64_A

section "Helper definitions"

text \<open>This definition ensures that the given pointer is aligned
to the given page size.\<close>

definition
  check_vp_alignment :: "vmpage_size \<Rightarrow> machine_word \<Rightarrow> (unit,'z::state_ext) se_monad" where
  "check_vp_alignment sz vptr \<equiv>
     unlessE (is_aligned vptr (pageBitsForSize sz)) $
       throwError AlignmentError"

text \<open>This definition converts a user-supplied argument into an
invocation label, used to determine the method to invoke.
\<close>

section "Architecture calls"

text \<open>This definition decodes architecture-specific invocations.
\<close>

definition
  page_base :: "vspace_ref \<Rightarrow> vmpage_size \<Rightarrow> vspace_ref"
where
  "page_base vaddr vmsize \<equiv> vaddr && ~~ mask (pageBitsForSize vmsize)"


(* this needs to be rewritten when arch IRQ handling is redone *)
definition
  arch_decode_irq_control_invocation :: "data \<Rightarrow> data list \<Rightarrow> cslot_ptr \<Rightarrow> cap list
                                     \<Rightarrow> (arch_irq_control_invocation,'z::state_ext) se_monad" where
 "arch_decode_irq_control_invocation label args src_slot cps \<equiv>
  (if invocation_type label = ArchInvocationLabel X64IRQIssueIRQHandlerIOAPIC
    then (if length args \<ge> 7 \<and> length cps \<ge> 1
      then let pre_irq = args ! 6; index = args ! 0; depth = args ! 1;
               cnode = cps ! 0;
               irqv = ucast pre_irq + minUserIRQ;
               ioapic = args ! 2;
               pin = args ! 3;
               level = args ! 4;
               polarity = args ! 5;
               vector = ucast irqv + irqIntOffset
        in doE

        whenE (pre_irq > ucast (maxUserIRQ - minUserIRQ)) $ throwError (RangeError 0 (ucast (maxUserIRQ - minUserIRQ)));
        irq_active \<leftarrow> liftE $ is_irq_active irqv;
        whenE irq_active $ throwError RevokeFirst;
        dest_slot \<leftarrow> lookup_target_slot cnode (data_to_cptr index) (unat depth);
        ensure_empty dest_slot;

        numIOAPICs \<leftarrow> liftE $ gets (x64_num_ioapics \<circ> arch_state);
        ioapic_nirqs \<leftarrow> liftE $ gets (x64_ioapic_nirqs \<circ> arch_state);
        whenE (numIOAPICs = 0) $ throwError IllegalOperation;
        whenE (ioapic > numIOAPICs - 1) $ throwError (RangeError 0 (numIOAPICs-1));
        whenE (pin > ucast (ioapic_nirqs ioapic - 1)) $ throwError (RangeError 0 (ucast (ioapic_nirqs ioapic - 1)));
        whenE (level > 1) $ throwError (RangeError 0 1);
        whenE (polarity > 1) $ throwError (RangeError 0 1);

        returnOk $ IssueIRQHandlerIOAPIC irqv dest_slot src_slot
                     ioapic pin level polarity vector
      odE
    else throwError TruncatedMessage)
  else (if invocation_type label = ArchInvocationLabel X64IRQIssueIRQHandlerMSI
    then (if length args \<ge> 7 \<and> length cps \<ge> 1
      then let pre_irq = args ! 6; index = args ! 0; depth = args ! 1;
               cnode = cps ! 0; irqv = ucast pre_irq + minUserIRQ;
               bus = args ! 2; dev = args ! 3; func = args ! 4; handle = args ! 5
        in doE

        whenE (pre_irq > ucast (maxUserIRQ - minUserIRQ)) $ throwError (RangeError 0 (ucast (maxUserIRQ - minUserIRQ)));
        irq_active \<leftarrow> liftE $ is_irq_active irqv;
        whenE irq_active $ throwError RevokeFirst;

        dest_slot \<leftarrow> lookup_target_slot cnode (data_to_cptr index) (unat depth);
        ensure_empty dest_slot;

       \<comment> \<open>Following should be wrapped in to a function like what c did
          since it is pc99 related, problem is where to put this function\<close>
        whenE (bus > maxPCIBus) $ throwError (RangeError 0 maxPCIBus);
        whenE (dev > maxPCIDev) $ throwError (RangeError 0 maxPCIDev);
        whenE (func > maxPCIFunc) $ throwError (RangeError 0 maxPCIFunc);

        returnOk $ IssueIRQHandlerMSI irqv dest_slot src_slot bus dev func handle
      odE
    else throwError TruncatedMessage)
  else throwError IllegalOperation))"

abbreviation (input)
  args_at_least :: "nat \<Rightarrow> data list \<Rightarrow> (unit,'z::state_ext) se_monad" where
  "args_at_least n args \<equiv>  whenE (n > length args) $ throwError TruncatedMessage"

definition
  ensure_port_operation_allowed :: "arch_cap \<Rightarrow> 32 word \<Rightarrow> nat \<Rightarrow> (unit,'z::state_ext) se_monad"
where
  "ensure_port_operation_allowed cap start_port sz \<equiv> case cap of
    IOPortCap first_allowed last_allowed \<Rightarrow> doE
      end_port \<leftarrow> returnOk $ start_port + of_nat sz - 1;
      assertE (first_allowed \<le> last_allowed);
      assertE (start_port \<le> end_port);
      whenE ((start_port < ucast first_allowed) \<or> (end_port > ucast last_allowed)) $ throwError IllegalOperation
    odE
  | _ \<Rightarrow> fail"

definition
  decode_port_invocation ::
    "data \<Rightarrow> data list \<Rightarrow> arch_cap \<Rightarrow> (arch_invocation,'z::state_ext) se_monad"
where
  "decode_port_invocation label args cap \<equiv> case (invocation_type label) of
    (ArchInvocationLabel X64IOPortIn8) \<Rightarrow> doE
      args_at_least 1 args;
      port \<leftarrow> returnOk $ ucast $ args ! 0;
      ensure_port_operation_allowed cap (ucast port) 1;
      returnOk $ InvokeIOPort $ IOPortInvocation port $ IOPortIn8
    odE
  | (ArchInvocationLabel X64IOPortIn16) \<Rightarrow> doE
      args_at_least 1 args;
      port \<leftarrow> returnOk $ ucast $ args ! 0;
      ensure_port_operation_allowed cap (ucast port) 2;
      returnOk $ InvokeIOPort $ IOPortInvocation port $ IOPortIn16
    odE
  | (ArchInvocationLabel X64IOPortIn32) \<Rightarrow> doE
      args_at_least 1 args;
      port \<leftarrow> returnOk $ ucast $ args ! 0;
      ensure_port_operation_allowed cap (ucast port) 4;
      returnOk $ InvokeIOPort $ IOPortInvocation port $ IOPortIn32
    odE
  | (ArchInvocationLabel X64IOPortOut8) \<Rightarrow> doE
      args_at_least 2 args;
      port \<leftarrow> returnOk $ ucast $ args ! 0;
      ensure_port_operation_allowed cap (ucast port) 1;
      output_data \<leftarrow> returnOk $ ucast $ args ! 1;
      returnOk $ InvokeIOPort $ IOPortInvocation port $ IOPortOut8 output_data
    odE
  | (ArchInvocationLabel X64IOPortOut16) \<Rightarrow> doE
      args_at_least 2 args;
      port \<leftarrow> returnOk $ ucast $ args ! 0;
      ensure_port_operation_allowed cap (ucast port) 2;
      output_data \<leftarrow> returnOk $ ucast $ args ! 1;
      returnOk $ InvokeIOPort $ IOPortInvocation port $ IOPortOut16 output_data
    odE
  | (ArchInvocationLabel X64IOPortOut32) \<Rightarrow> doE
      args_at_least 2 args;
      port \<leftarrow> returnOk $ ucast $ args ! 0;
      ensure_port_operation_allowed cap (ucast port) 4;
      output_data \<leftarrow> returnOk $ ucast $ args ! 1;
      returnOk $ InvokeIOPort $ IOPortInvocation port $ IOPortOut32 output_data
      odE
  | _ \<Rightarrow> throwError IllegalOperation"

definition
  is_ioport_range_free :: "io_port \<Rightarrow> io_port \<Rightarrow> (bool,'z::state_ext) s_monad"
where
  "is_ioport_range_free f l \<equiv> do
     alloc_ports \<leftarrow> gets (x64_allocated_io_ports \<circ> arch_state);
     return $ {f..l} \<inter> (Collect alloc_ports) = {}
  od"

definition
  decode_ioport_control_invocation :: "data \<Rightarrow> data list \<Rightarrow> cslot_ptr \<Rightarrow> arch_cap \<Rightarrow>
                                    cap list \<Rightarrow> (arch_invocation,'z::state_ext) se_monad"
where
  "decode_ioport_control_invocation label args slot cap extra_caps \<equiv>
    if invocation_type label = ArchInvocationLabel X64IOPortControlIssue then
      if length args \<ge> 4 \<and> length extra_caps \<ge> 1 then
        let first_port = ucast (args ! 0); last_port = ucast (args ! 1);
            index = args ! 2; depth = args ! 3; cnode = extra_caps ! 0
        in doE
          whenE (first_port > last_port) $ throwError $ InvalidArgument 1;
          check \<leftarrow> liftE $ is_ioport_range_free first_port last_port;
          whenE (\<not>check) $ throwError RevokeFirst;

          dest_slot \<leftarrow> lookup_target_slot cnode (data_to_cptr index) (unat depth);
          ensure_empty dest_slot;
          returnOk $ InvokeIOPortControl $ IOPortControlInvocation first_port last_port dest_slot slot
        odE
      else throwError TruncatedMessage
    else throwError IllegalOperation"

(*X64STUB*)
definition
  decode_io_unmap_invocation :: "data \<Rightarrow> data list \<Rightarrow> cslot_ptr \<Rightarrow> arch_cap \<Rightarrow>
                            (cap \<times> cslot_ptr) list \<Rightarrow> (arch_invocation,'z::state_ext) se_monad"
where
  "decode_io_unmap_invocation label args cte cap extra_caps \<equiv> undefined"


definition page_cap_set_vmmap_type :: "arch_cap \<Rightarrow> vmmap_type \<Rightarrow> arch_cap"
where "page_cap_set_vmmap_type cap t \<equiv> (case cap of
  PageCap dev p R map_type pgsz mapped_address \<Rightarrow> PageCap dev p R t pgsz mapped_address
  | _ \<Rightarrow> undefined)"

definition
  get_iovm_rights :: "vm_rights \<Rightarrow> vm_rights \<Rightarrow> vm_rights"
where "get_iovm_rights cover base \<equiv>
     (if cover = {AllowRead} then  (if AllowRead \<in> base then {AllowRead} else {}) else
     (if AllowRead \<in> cover then  {AllowRead} \<union> (if AllowWrite \<in> base then {AllowWrite} else {})
     else (if AllowWrite \<in> base then {AllowWrite} else {})))"

(* FIXME x64-vtd:
definition
  pci_request_id_from_cap :: "cap \<Rightarrow> (16 word, 'z::state_ext) s_monad"
  where "pci_request_id_from_cap cap \<equiv>
    case cap of
      ArchObjectCap (IOSpaceCap _ (Some deviceid)) \<Rightarrow> return $ ucast deviceid
    | ArchObjectCap (IOPageTableCap _ _ (Some asid)) \<Rightarrow> return $ fst asid
    | _\<Rightarrow> fail"


definition
  decode_io_pt_invocation :: "data \<Rightarrow> data list \<Rightarrow> cslot_ptr \<Rightarrow> arch_cap \<Rightarrow>
                            (cap \<times> cslot_ptr) list \<Rightarrow> (arch_invocation,'z::state_ext) se_monad"
where
  "decode_io_pt_invocation label args cptr cap extra_caps \<equiv> (case cap of
  IOPageTableCap bptr level mapped_address \<Rightarrow>
    if invocation_type label = ArchInvocationLabel  X64IOPageTableMap
    then
      let paddr = addrFromPPtr bptr;
          ioaddr = args ! 0;
          vmrights = args ! 1;
          iospace_cap = fst (extra_caps ! 0)
      in doE
      whenE (mapped_address \<noteq> None) $ throwError $ InvalidCapability 0;
      (deviceid,domainid) <- (case iospace_cap of
             ArchObjectCap (IOSpaceCap domainid (Some deviceid))
                 \<Rightarrow> returnOk $ (deviceid,domainid)
             | _ \<Rightarrow> throwError $ InvalidCapability 0);
      pci_request_id \<leftarrow> liftE $ pci_request_id_from_cap iospace_cap;
      iocteslot \<leftarrow> liftE $ lookup_io_context_slot pci_request_id;
      iocte \<leftarrow> liftE $ get_iocte iocteslot;
      case iocte of
        VTDCTE did rmrr aw slptr tt False \<Rightarrow> doE
          vtdcte <- returnOk $ VTDCTE did False (x64_num_io_pt_levels - 2)
                                          paddr NotTranslated True;
          cap' <- returnOk $ IOPageTableCap bptr 0 (Some (deviceid, ioaddr));
          returnOk $ InvokeIOPT $ IOPageTableMapContext (ArchObjectCap cap')
            cptr vtdcte iocteslot
        odE
      | VTDCTE did rmrr aw slptr tt True \<Rightarrow> doE
          (slot, level) \<leftarrow> lookup_error_on_failure False $
              lookup_io_pt_slot (ptrFromPAddr slptr) ioaddr;
           level <- returnOk $ x64_num_io_pt_levels - level;
           pte <- liftE $ get_iopte slot;
           cap' <- returnOk $ IOPageTableCap bptr level (Some (deviceid, ioaddr));
           case pte of
             InvalidIOPTE \<Rightarrow> returnOk $ InvokeIOPT $ IOPageTableMap (ArchObjectCap cap')
             cptr (VTDPTE paddr vm_read_write) slot
           | _ \<Rightarrow> throwError $ InvalidCapability 0
        odE
      odE
    else if invocation_type label = ArchInvocationLabel X64IOPageTableUnmap
    then
      returnOk $ InvokeIOPT $ IOPageTableUnmap (ArchObjectCap cap) cptr
    else throwError $ IllegalOperation
  | _ \<Rightarrow> undefined)"

definition
  decode_io_frame_map_invocation :: "data \<Rightarrow> data list \<Rightarrow> cslot_ptr \<Rightarrow> arch_cap \<Rightarrow>
                            (cap \<times> cslot_ptr) list \<Rightarrow> (arch_invocation,'z::state_ext) se_monad"
where
  "decode_io_frame_map_invocation label args cptr cap extra_caps \<equiv> (case cap of
  PageCap p R map_tyhpe pgsz mapped_address \<Rightarrow>
    if invocation_type label = ArchInvocationLabel X64PageMapIO
    then
      let paddr = addrFromPPtr p;
          ioaddr = args ! 0;
          vmrights = args ! 1;
          iospace_cap = fst (extra_caps ! 0);
          vm_right_mask = get_iovm_rights R (data_to_rights vmrights)
      in doE
      whenE (pgsz \<noteq> X64SmallPage) $ throwError $ InvalidCapability 0;
      whenE (mapped_address \<noteq> None) $ throwError $ InvalidCapability 0;
      deviceid \<leftarrow> (case iospace_cap of
                 ArchObjectCap (IOSpaceCap _ (Some deviceid)) \<Rightarrow> returnOk $ ucast deviceid
                 | _ \<Rightarrow> throwError $ InvalidCapability 0);
      pci_request_id \<leftarrow> liftE $ pci_request_id_from_cap iospace_cap;

      iocteslot \<leftarrow> liftE $ lookup_io_context_slot pci_request_id;
      iocte \<leftarrow> liftE $ get_iocte iocteslot;
      (slot, level) \<leftarrow> (case iocte of
                 VTDCTE did rmrr aw slptr tt True \<Rightarrow>
                     lookup_error_on_failure False $ lookup_io_pt_slot (ptrFromPAddr slptr) ioaddr
                 | _ \<Rightarrow> throwError $ FailedLookup False InvalidRoot);
      whenE (level \<noteq> 0) $ throwError $ InvalidCapability 0;
      iopte <- liftE $ get_iopte slot;
      whenE (iopte \<noteq> InvalidIOPTE) $ throwError DeleteFirst;
      vtdpte <- returnOk $ VTDPTE paddr vm_right_mask;
      cap' <- returnOk $ PageCap p R VMIOSpaceMap pgsz (Just (deviceid, ioaddr));
      returnOk $ InvokePage $ PageIOMap (ArchObjectCap cap') cptr vtdpte slot
    odE
    else throwError $ IllegalOperation
  | _ \<Rightarrow> undefined)"


definition
  decode_io_map_invocation :: "data \<Rightarrow> data list \<Rightarrow> cslot_ptr \<Rightarrow> arch_cap \<Rightarrow>
                            (cap \<times> cslot_ptr) list \<Rightarrow> (arch_invocation,'z::state_ext) se_monad"
where
  "decode_io_map_invocation label args cte cap extra_caps \<equiv> undefined"
(*X64STUB*)
*)

definition
decode_page_invocation :: "data \<Rightarrow> data list \<Rightarrow> cslot_ptr \<Rightarrow> arch_cap
                            \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow> (arch_invocation,'z::state_ext) se_monad"
where
  "decode_page_invocation label args cte cap extra_caps \<equiv> (case cap of
  PageCap dev p R map_type pgsz mapped_address \<Rightarrow>
    if invocation_type label = ArchInvocationLabel X64PageMap then
    if length args > 2 \<and> length extra_caps > 0
    then let vaddr = args ! 0;
             rights_mask = args ! 1;
             attr = args ! 2;
             vspace_cap = fst (extra_caps ! 0)
         in doE
             (vspace, asid) \<leftarrow> (case vspace_cap of
                                   ArchObjectCap (PML4Cap pm (Some asid)) \<Rightarrow>
                                         returnOk (pm, asid)
                                 | _ \<Rightarrow> throwError $ InvalidCapability 1);
             case mapped_address of
               Some (asid', vaddr') \<Rightarrow> doE
                 whenE (asid' \<noteq> asid) (throwError $ InvalidCapability 1);
                 whenE (map_type \<noteq> VMVSpaceMap) $ throwError IllegalOperation;
                 whenE (vaddr' \<noteq> vaddr) (throwError $ InvalidArgument 0)
               odE
             | None \<Rightarrow> doE
                 vtop \<leftarrow> returnOk $ vaddr + bit (pageBitsForSize pgsz);
                 whenE (vaddr > user_vtop \<or> vtop > user_vtop) $ throwError $ InvalidArgument 0
               odE;
             vspace' \<leftarrow> lookup_error_on_failure False $ find_vspace_for_asid asid;
             whenE (vspace' \<noteq> vspace) $ throwError $ InvalidCapability 1;
             vm_rights \<leftarrow> returnOk $ mask_vm_rights R $ data_to_rights rights_mask;
             check_vp_alignment pgsz vaddr;
             entries \<leftarrow> create_mapping_entries (addrFromPPtr p) vaddr pgsz vm_rights
                                               (attribs_from_word attr) vspace;
             ensure_safe_mapping entries;
             returnOk $ InvokePage $ PageMap
               (ArchObjectCap $ PageCap dev p R VMVSpaceMap pgsz (Some (asid,vaddr))) cte entries vspace
          odE
    else throwError TruncatedMessage
    else if invocation_type label = ArchInvocationLabel X64PageUnmap then
             \<^cancel>\<open>case map_type of
                 VMIOSpaceMap \<Rightarrow> decode_io_unmap_invocation label args cte cap extra_caps
               | _ \<Rightarrow>\<close> returnOk $ InvokePage $ PageUnmap cap cte
    \<^cancel>\<open>FIXME x64-vtd:
    else if invocation_type label = ArchInvocationLabel X64PageMapIO
    then decode_io_map_invocation label args cte cap extra_caps \<close>
    else if invocation_type label = ArchInvocationLabel X64PageGetAddress
    then returnOk $ InvokePage $ PageGetAddr p
  else throwError IllegalOperation
 | _ \<Rightarrow> fail)"

definition filter_frame_attrs :: "frame_attrs \<Rightarrow> table_attrs"
where
  "filter_frame_attrs attrs \<equiv> {s. \<exists>s' \<in> attrs. s' = PTAttr s}"

definition
  decode_page_table_invocation :: "data \<Rightarrow> data list \<Rightarrow> cslot_ptr \<Rightarrow> arch_cap \<Rightarrow>
                                  (cap \<times> cslot_ptr) list \<Rightarrow> (arch_invocation,'z::state_ext) se_monad"
where
  "decode_page_table_invocation label args cte cap extra_caps \<equiv> (case cap of
    PageTableCap p mapped_address \<Rightarrow>
      if invocation_type label = ArchInvocationLabel X64PageTableMap then
      if length args > 1 \<and> length extra_caps > 0
      then let vaddr = args ! 0;
               attr = args ! 1;
               pml4_cap = fst (extra_caps ! 0)
      in doE
               whenE (mapped_address \<noteq> None) $ throwError $ InvalidCapability 0;
               vaddr' \<leftarrow> returnOk $ vaddr && ~~ mask pd_shift_bits;
               (pml4, asid) \<leftarrow> (case pml4_cap of
                   ArchObjectCap (PML4Cap pml4 (Some asid)) \<Rightarrow> returnOk (pml4, asid)
                   | _ \<Rightarrow> throwError $ InvalidCapability 1);
               whenE (user_vtop < vaddr') $ throwError $ InvalidArgument 0;
               pml4' \<leftarrow> lookup_error_on_failure False $ find_vspace_for_asid asid;
               whenE (pml4' \<noteq> pml4) $ throwError $ InvalidCapability 1;
               pd_slot \<leftarrow> lookup_error_on_failure False $ lookup_pd_slot pml4 vaddr';
               old_pde \<leftarrow> liftE $ get_pde pd_slot;
               unlessE (old_pde = InvalidPDE) $ throwError DeleteFirst;
               pde \<leftarrow> returnOk (PageTablePDE (addrFromPPtr p)
                                  (filter_frame_attrs $ attribs_from_word attr) vm_read_write);
               cap' <- returnOk $ ArchObjectCap $ PageTableCap p $ Some (asid, vaddr');
               returnOk $ InvokePageTable $ PageTableMap cap' cte pde pd_slot pml4
            odE
      else throwError TruncatedMessage
      else if invocation_type label = ArchInvocationLabel X64PageTableUnmap then doE
               final \<leftarrow> liftE $ is_final_cap (ArchObjectCap cap);
               unlessE final $ throwError RevokeFirst;
               returnOk $ InvokePageTable $ PageTableUnmap (ArchObjectCap cap) cte
        odE
      else throwError IllegalOperation
  | _ \<Rightarrow> fail)"

definition
  decode_page_directory_invocation :: "data \<Rightarrow> data list \<Rightarrow> cslot_ptr \<Rightarrow> arch_cap \<Rightarrow>
                                      (cap \<times> cslot_ptr) list \<Rightarrow> (arch_invocation,'z::state_ext) se_monad"
where
  "decode_page_directory_invocation label args cte cap extra_caps \<equiv> (case cap of
    PageDirectoryCap p mapped_address \<Rightarrow>
      if invocation_type label = ArchInvocationLabel X64PageDirectoryMap then
      if length args > 1 \<and> length extra_caps > 0
      then let vaddr = args ! 0;
               attr = args ! 1;
               pml4_cap = fst (extra_caps ! 0)
      in doE
               whenE (mapped_address \<noteq> None) $ throwError $ InvalidCapability 0;
               vaddr' \<leftarrow> returnOk $ vaddr && ~~ mask pdpt_shift_bits;
               (pml4, asid) \<leftarrow> (case pml4_cap of
                       ArchObjectCap (PML4Cap pml4 (Some asid)) \<Rightarrow> returnOk (pml4, asid)
                       | _ \<Rightarrow> throwError $ InvalidCapability 1);
               whenE (user_vtop < vaddr') $ throwError $ InvalidArgument 0;
               pml4' \<leftarrow> lookup_error_on_failure False $ find_vspace_for_asid asid;
               whenE (pml4' \<noteq> pml4) $ throwError $ InvalidCapability 1;
               pdpt_slot \<leftarrow> lookup_error_on_failure False $ lookup_pdpt_slot pml4 vaddr';
               old_pdpte \<leftarrow> liftE $ get_pdpte pdpt_slot;
               unlessE (old_pdpte = InvalidPDPTE) $ throwError DeleteFirst;
               pdpte \<leftarrow> returnOk (PageDirectoryPDPTE (addrFromPPtr p)
                          (filter_frame_attrs $ attribs_from_word attr) vm_read_write);
               cap' <- returnOk $ ArchObjectCap $ PageDirectoryCap p $ Some (asid, vaddr');
               returnOk $ InvokePageDirectory $ PageDirectoryMap cap' cte pdpte pdpt_slot pml4
        odE
      else throwError TruncatedMessage
      else if invocation_type label = ArchInvocationLabel X64PageDirectoryUnmap then doE
               final \<leftarrow> liftE $ is_final_cap (ArchObjectCap cap);
               unlessE final $ throwError RevokeFirst;
               returnOk $ InvokePageDirectory $ PageDirectoryUnmap (ArchObjectCap cap) cte
            odE
      else throwError IllegalOperation
  | _ \<Rightarrow> fail)"

definition
  decode_pdpt_invocation :: "data \<Rightarrow> data list \<Rightarrow> cslot_ptr \<Rightarrow> arch_cap \<Rightarrow>
                                      (cap \<times> cslot_ptr) list \<Rightarrow> (arch_invocation,'z::state_ext) se_monad"
where
  "decode_pdpt_invocation label args cte cap extra_caps \<equiv> (case cap of
    PDPointerTableCap p mapped_address \<Rightarrow>
      if invocation_type label = ArchInvocationLabel X64PDPTMap then
      if length args > 1 \<and> length extra_caps > 0
      then let vaddr = args ! 0;
               attr = args ! 1;
               pml4_cap = fst (extra_caps ! 0)
      in doE
               whenE (mapped_address \<noteq> None) $ throwError $ InvalidCapability 0;
               vaddr' \<leftarrow> returnOk $ vaddr && ~~ mask pml4_shift_bits;
               (pml4 ,asid) \<leftarrow> (case pml4_cap of
                       ArchObjectCap (PML4Cap pml4 (Some asid)) \<Rightarrow> returnOk (pml4, asid)
                       | _ \<Rightarrow> throwError $ InvalidCapability 1);
               whenE (user_vtop < vaddr') $ throwError $ InvalidArgument 0;
               pml4' \<leftarrow> lookup_error_on_failure False $ find_vspace_for_asid (asid);
               whenE (pml4' \<noteq> pml4) $ throwError $ InvalidCapability 1;
               pml_slot \<leftarrow> returnOk $ lookup_pml4_slot pml4 vaddr';
               old_pml4e \<leftarrow> liftE $ get_pml4e pml_slot;
               unlessE (old_pml4e = InvalidPML4E) $ throwError DeleteFirst;
               pml4e \<leftarrow> returnOk (PDPointerTablePML4E (addrFromPPtr p)
                          (filter_frame_attrs $ attribs_from_word attr) vm_read_write);
               cap' <- returnOk $ ArchObjectCap $ PDPointerTableCap p $ Some (asid, vaddr');
               returnOk $ InvokePDPT $ PDPTMap cap' cte pml4e pml_slot pml4
            odE
      else throwError TruncatedMessage
      else if invocation_type label = ArchInvocationLabel X64PDPTUnmap then doE
               final \<leftarrow> liftE $ is_final_cap (ArchObjectCap cap);
               unlessE final $ throwError RevokeFirst;
               returnOk $ InvokePDPT $ PDPTUnmap (ArchObjectCap cap) cte
         odE
      else throwError IllegalOperation
  | _ \<Rightarrow> fail)"

definition
  arch_decode_invocation ::
  "data \<Rightarrow> data list \<Rightarrow> cap_ref \<Rightarrow> cslot_ptr \<Rightarrow> arch_cap \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow>
   (arch_invocation,'z::state_ext) se_monad"
where
  "arch_decode_invocation label args x_slot cte cap extra_caps \<equiv> case cap of
    PDPointerTableCap _ _ \<Rightarrow> decode_pdpt_invocation label args cte cap extra_caps
  | PageDirectoryCap _ _ \<Rightarrow> decode_page_directory_invocation label args cte cap extra_caps
  | PageTableCap _ _ \<Rightarrow> decode_page_table_invocation label args cte cap extra_caps
  | PageCap _ _ _ _ _ _ \<Rightarrow> decode_page_invocation label args cte cap extra_caps
  | ASIDControlCap \<Rightarrow>
      if invocation_type label = ArchInvocationLabel X64ASIDControlMakePool then
      if length args > 1 \<and> length extra_caps > 1
      then let index = args ! 0;
               depth = args ! 1;
               (untyped, parent_slot) = extra_caps ! 0;
               root = fst (extra_caps ! 1)
      in doE
               asid_table \<leftarrow> liftE $ gets (x64_asid_table \<circ> arch_state);
               free_set \<leftarrow> returnOk (- dom asid_table);
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
   else throwError TruncatedMessage
   else throwError IllegalOperation

  | ASIDPoolCap p base \<Rightarrow>
      if invocation_type label = ArchInvocationLabel X64ASIDPoolAssign then
      if length extra_caps > 0
      then let (pd_cap, pd_cap_slot) = extra_caps ! 0 in
            case pd_cap of
               ArchObjectCap (PML4Cap _ None) \<Rightarrow> doE
                  asid_table \<leftarrow> liftE $ gets (x64_asid_table \<circ> arch_state);
                  pool_ptr \<leftarrow> returnOk (asid_table (asid_high_bits_of base));
                  whenE (pool_ptr = None) $ throwError $ FailedLookup False InvalidRoot;
                  whenE (p \<noteq> the pool_ptr) $ throwError $ InvalidCapability 0;
                  pool \<leftarrow> liftE $ get_asid_pool p;
                  free_set \<leftarrow> returnOk (- dom pool \<inter> {x. ucast x + base \<noteq> 0});
                  whenE (free_set = {}) $ throwError DeleteFirst;
                  offset \<leftarrow> liftE $ select_ext (\<lambda>_. free_asid_pool_select pool base) free_set;
                  returnOk $ InvokeASIDPool $ Assign (ucast offset + base) p pd_cap_slot
              odE
            | _ \<Rightarrow> throwError $ InvalidCapability 1
      else throwError TruncatedMessage
      else throwError IllegalOperation

  | IOPortCap f l \<Rightarrow> decode_port_invocation label args (IOPortCap f l)
  | IOPortControlCap \<Rightarrow> decode_ioport_control_invocation label args cte cap (map fst extra_caps)
  | PML4Cap a b \<Rightarrow> throwError IllegalOperation"

definition
  arch_data_to_obj_type :: "nat \<Rightarrow> aobject_type option" where
 "arch_data_to_obj_type n \<equiv>
  if      n = 0 then Some PDPTObj
  else if n = 1 then Some PML4Obj
  else if n = 2 then Some HugePageObj
  else if n = 3 then Some SmallPageObj
  else if n = 4 then Some LargePageObj
  else if n = 5 then Some PageTableObj
  else if n = 6 then Some PageDirectoryObj
  else None"

definition
  arch_check_irq :: "data \<Rightarrow> (unit,'z::state_ext) se_monad"
where
  "arch_check_irq irq \<equiv> throwError IllegalOperation"

end (* context Arch *)

end
