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
Decoding system calls
*)

chapter "Decoding System Calls"

theory Decode_A
imports
  Interrupt_A
  "../../lib/WordLib"
  "../design/InvocationLabels_H"
begin

text {*
  This theory includes definitions describing how user arguments are 
decoded into invocation structures; these structures are then used 
to perform the actual system call (see @{text "perform_invocation"}).  
In addition, these definitions check the validity of these arguments, 
throwing an error if given an invalid request.

  As such, this theory describes the binary interface between the 
user and the kernel, along with the preconditions on each argument.
*}

section "Helper definitions"

text {* This definition ensures that the given pointer is aligned
to the given page size. *}

definition
  check_vp_alignment :: "vmpage_size \<Rightarrow> word32 \<Rightarrow> (unit,'z::state_ext) se_monad" where
  "check_vp_alignment sz vptr \<equiv>
     unlessE (is_aligned vptr (pageBitsForSize sz)) $ 
       throwError AlignmentError"

text {* This definition converts a user-supplied argument into an
invocation label, used to determine the method to invoke. 
*}

definition
  invocation_type :: "data \<Rightarrow> invocation_label"
where
 "invocation_type x \<equiv> if \<exists>(v :: invocation_label). fromEnum v = data_to_nat x
                      then toEnum (data_to_nat x) else InvalidInvocation"

definition
  label_to_flush_type :: "invocation_label \<Rightarrow> flush_type"
where
  "label_to_flush_type label \<equiv> case label of
       ARMPDClean_Data \<Rightarrow> Clean
     | ARMPageClean_Data \<Rightarrow> Clean
     | ARMPDInvalidate_Data \<Rightarrow> Invalidate
     | ARMPageInvalidate_Data \<Rightarrow> Invalidate
     | ARMPDCleanInvalidate_Data \<Rightarrow> CleanInvalidate
     | ARMPageCleanInvalidate_Data \<Rightarrow> CleanInvalidate
     | ARMPDUnify_Instruction \<Rightarrow> Unify
     | ARMPageUnify_Instruction \<Rightarrow> Unify"

section "Architecture calls"

text {* This definition decodes architecture-specific invocations.
*}

definition
  page_base :: "vspace_ref \<Rightarrow> vmpage_size \<Rightarrow> vspace_ref"
where
  "page_base vaddr vmsize \<equiv> vaddr && ~~ mask (pageBitsForSize vmsize)"

definition
  arch_decode_invocation :: 
  "data \<Rightarrow> data list \<Rightarrow> cap_ref \<Rightarrow> cslot_ptr \<Rightarrow> arch_cap \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow> 
   (arch_invocation,'z::state_ext) se_monad"
where
"arch_decode_invocation label args x_slot cte cap extra_caps \<equiv> case cap of

  PageDirectoryCap _ _ \<Rightarrow>
    if isPDFlush (invocation_type label) then
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
    if invocation_type label = ARMPageTableMap then
    if length args > 1 \<and> length extra_caps > 0
    then let vaddr = args ! 0;
             attr = args ! 1;
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
            pd_index \<leftarrow> returnOk (shiftr vaddr 20);
            vaddr' \<leftarrow> returnOk (vaddr && ~~ mask 20);
            pd_slot \<leftarrow> returnOk (pd + (pd_index << 2));
            oldpde \<leftarrow> liftE $ get_master_pde pd_slot;
            unlessE (oldpde = InvalidPDE) $ throwError DeleteFirst;             
            pde \<leftarrow> returnOk (PageTablePDE (addrFromPPtr p)
                               (attribs_from_word attr \<inter> {ParityEnabled}) 0);
            returnOk $ InvokePageTable $ 
                PageTableMap
                (ArchObjectCap $ PageTableCap p (Some (asid, vaddr')))
                cte pde pd_slot
    odE
    else throwError TruncatedMessage
    else if invocation_type label = ARMPageTableUnmap
    then doE
            final \<leftarrow> liftE $ is_final_cap (ArchObjectCap cap);
            unlessE final $ throwError RevokeFirst;
            returnOk $ InvokePageTable $ PageTableUnmap (ArchObjectCap cap) cte
    odE
    else throwError IllegalOperation

| PageCap p R pgsz mapped_address \<Rightarrow>
    if invocation_type label = ARMPageMap then
    if length args > 2 \<and> length extra_caps > 0
    then let vaddr = args ! 0;
             rights_mask = args ! 1;
             attr = args ! 2;
             pd_cap = fst (extra_caps ! 0)
        in doE
            whenE (mapped_address \<noteq> None) $ throwError $ InvalidCapability 0;
            (pd,asid) \<leftarrow> (case pd_cap of 
                            ArchObjectCap (PageDirectoryCap pd (Some asid)) \<Rightarrow> 
                              returnOk (pd,asid)
                         | _ \<Rightarrow> throwError $ InvalidCapability 1);
            pd' \<leftarrow> lookup_error_on_failure False $ find_pd_for_asid asid;
            whenE (pd' \<noteq> pd) $ throwError $ InvalidCapability 1;
            vtop \<leftarrow> returnOk (vaddr + (1 << (pageBitsForSize pgsz)) - 1);
            whenE (vtop \<ge> kernel_base) $ throwError $ InvalidArgument 0;
            vm_rights \<leftarrow> returnOk (mask_vm_rights R (data_to_rights rights_mask));
            check_vp_alignment pgsz vaddr;
            entries \<leftarrow> create_mapping_entries (addrFromPPtr p)
                                              vaddr pgsz vm_rights 
                                              (attribs_from_word attr) pd;
            ensure_safe_mapping entries;
            returnOk $ InvokePage $ PageMap asid
                (ArchObjectCap $ PageCap p R pgsz (Some (asid, vaddr))) 
                cte entries
        odE
    else  throwError TruncatedMessage
    else if invocation_type label = ARMPageRemap then
         if length args > 1 \<and> length extra_caps > 0
         then let rights_mask = args ! 0;
                  attr = args ! 1;
                  pd_cap = fst (extra_caps ! 0)
         in doE
            (pd,asid) \<leftarrow> (case pd_cap of 
                            ArchObjectCap (PageDirectoryCap pd (Some asid)) \<Rightarrow> 
                              returnOk (pd,asid)
                         | _ \<Rightarrow> throwError $ InvalidCapability 1);
            (asid', vaddr) \<leftarrow> (case mapped_address of
                  Some a \<Rightarrow> returnOk a
                | _ \<Rightarrow> throwError $ InvalidCapability 0);
            pd' \<leftarrow> lookup_error_on_failure False $ find_pd_for_asid asid';
            whenE (pd' \<noteq> pd \<or> asid' \<noteq> asid) $ throwError $ InvalidCapability 1;  
            vm_rights \<leftarrow> returnOk (mask_vm_rights R $ data_to_rights rights_mask);
            check_vp_alignment pgsz vaddr;
            entries \<leftarrow> create_mapping_entries (addrFromPPtr p)
                                              vaddr pgsz vm_rights 
                                              (attribs_from_word attr) pd;
            ensure_safe_mapping entries;
            returnOk $ InvokePage $ PageRemap asid' entries
        odE
    else  throwError TruncatedMessage
    else if invocation_type label = ARMPageUnmap
    then  returnOk $ InvokePage $ PageUnmap cap cte
    else if isPageFlush (invocation_type label) then
        if length args > 1
        then let start = args ! 0;
                 end = args ! 1
        in doE
            (asid, vaddr) \<leftarrow> (case mapped_address of
                Some a \<Rightarrow> returnOk a
              | _ \<Rightarrow> throwError IllegalOperation);
            pd \<leftarrow> lookup_error_on_failure False $ find_pd_for_asid asid;
            whenE (end \<le> start) $ throwError $ InvalidArgument 1;
            page_size \<leftarrow> returnOk $ 1 << pageBitsForSize pgsz;
            whenE (start \<ge> page_size \<or> end > page_size) $ throwError $ InvalidArgument 0;
            returnOk $ InvokePage $ PageFlush
                (label_to_flush_type (invocation_type label)) (start + vaddr)
                (end + vaddr - 1) (addrFromPPtr p + start) pd asid
    odE
    else throwError TruncatedMessage
    else if invocation_type label = ARMPageGetAddress
    then returnOk $ InvokePage $ PageGetAddr p
  else  throwError IllegalOperation

| ASIDControlCap \<Rightarrow>
    if invocation_type label = ARMASIDControlMakePool then
    if length args > 1 \<and> length extra_caps > 1
    then let index = args ! 0;
             depth = args ! 1;
             (untyped, parent_slot) = extra_caps ! 0;
             root = fst (extra_caps ! 1)
         in doE
            asid_table \<leftarrow> liftE $ gets (arm_asid_table \<circ> arch_state);
            free_set \<leftarrow> returnOk (- dom asid_table \<inter> {x. x \<le> 2 ^ asid_high_bits - 1});
            whenE (free_set = {}) $ throwError DeleteFirst;
            free \<leftarrow> liftE $ select_ext (\<lambda>_. free_asid_select asid_table) free_set;
            base \<leftarrow> returnOk (ucast free << asid_low_bits);
            (p,n) \<leftarrow> (case untyped of UntypedCap p n f \<Rightarrow> returnOk (p,n) 
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
  if invocation_type label = ARMASIDPoolAssign then
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
            free_set \<leftarrow> returnOk 
                   (- dom pool \<inter> {x. x \<le> 2 ^ asid_low_bits - 1 \<and> ucast x + base \<noteq> 0});
            whenE (free_set = {}) $ throwError DeleteFirst;
            offset \<leftarrow> liftE $ select_ext (\<lambda>_. free_asid_pool_select pool base) free_set;
            returnOk $ InvokeASIDPool $ Assign (ucast offset + base) p pd_cap_slot
          odE
        | _ \<Rightarrow>  throwError $ InvalidCapability 1
  else  throwError TruncatedMessage
  else  throwError IllegalOperation"


text "ARM does not support additional interrupt control operations"
definition
  arch_decode_interrupt_control ::
  "data list \<Rightarrow> cap list \<Rightarrow> (arch_interrupt_control,'z::state_ext) se_monad" where
  "arch_decode_interrupt_control d cs \<equiv> throwError IllegalOperation"

section "CNode"

text {* This definition decodes CNode invocations. *}

definition
  decode_cnode_invocation :: 
  "data \<Rightarrow> data list \<Rightarrow> cap \<Rightarrow> cap list \<Rightarrow> (cnode_invocation,'z::state_ext) se_monad"
where
"decode_cnode_invocation label args cap excaps \<equiv> doE
  unlessE (invocation_type label \<in> set [CNodeRevoke .e. CNodeSaveCaller]) $
    throwError IllegalOperation;
  whenE (length args < 2) (throwError TruncatedMessage);
  index \<leftarrow> returnOk $ data_to_cptr $ args ! 0;
  bits \<leftarrow> returnOk $ data_to_nat $ args ! 1;
  args \<leftarrow> returnOk $ drop 2 args;
  dest_slot \<leftarrow> lookup_target_slot cap index bits;
  if length args \<ge> 2 \<and> length excaps > 0
        \<and> invocation_type label \<in> set [CNodeCopy .e. CNodeMutate] then
  doE
    src_index \<leftarrow> returnOk $ data_to_cptr $ args ! 0;
    src_depth \<leftarrow> returnOk $ data_to_nat $ args ! 1;  
    args \<leftarrow> returnOk $ drop 2 args;
    src_root_cap \<leftarrow> returnOk $ excaps ! 0;
    ensure_empty dest_slot;
    src_slot \<leftarrow> 
         lookup_source_slot src_root_cap src_index src_depth;
    src_cap \<leftarrow> liftE $ get_cap src_slot;
    whenE (src_cap = NullCap) $ 
         throwError $ FailedLookup True $ MissingCapability src_depth;
    (rights, cap_data, is_move) \<leftarrow> case (invocation_type label, args) of
      (CNodeCopy, rightsWord # _) \<Rightarrow> doE
                    rights \<leftarrow> returnOk $ data_to_rights $ rightsWord;
                    returnOk $ (rights, None, False)
                odE
     | (CNodeMint, rightsWord # capData # _) \<Rightarrow> doE
                    rights \<leftarrow> returnOk $ data_to_rights $ rightsWord;
                    returnOk $ (rights, Some capData, False)
                odE
     | (CNodeMove, _) \<Rightarrow> returnOk (all_rights, None, True)
     | (CNodeMutate, capData # _) \<Rightarrow> returnOk (all_rights, Some capData, True)
     | _ \<Rightarrow> throwError TruncatedMessage;
    src_cap \<leftarrow> returnOk $ mask_cap rights src_cap;
    new_cap \<leftarrow> (if is_move then returnOk else derive_cap src_slot) (case cap_data of
                  Some w \<Rightarrow> update_cap_data is_move w src_cap
                | None \<Rightarrow> src_cap);
    whenE (new_cap = NullCap) $ throwError IllegalOperation;
    returnOk $ (if is_move then MoveCall else InsertCall) new_cap src_slot dest_slot
  odE
  else if invocation_type label = CNodeRevoke then returnOk $ RevokeCall dest_slot
  else if invocation_type label = CNodeDelete then returnOk $ DeleteCall dest_slot
  else if invocation_type label = CNodeSaveCaller then doE
    ensure_empty dest_slot;
    returnOk $ SaveCall dest_slot
  odE
  else if invocation_type label = CNodeRecycle then doE
    cap \<leftarrow> liftE $ get_cap dest_slot;
    unlessE (has_recycle_rights cap) $ throwError IllegalOperation;
    returnOk $ RecycleCall dest_slot
  odE
  else if invocation_type label = CNodeRotate \<and> length args > 5
          \<and> length excaps > 1 then
  doE
    pivot_new_data \<leftarrow> returnOk $ args ! 0;  
    pivot_index \<leftarrow> returnOk $ data_to_cptr $ args ! 1; 
    pivot_depth \<leftarrow> returnOk $ data_to_nat $ args ! 2; 
    src_new_data \<leftarrow> returnOk $ args ! 3;
    src_index \<leftarrow> returnOk $ data_to_cptr $ args ! 4; 
    src_depth \<leftarrow> returnOk $ data_to_nat $ args ! 5; 
    pivot_root_cap <- returnOk $ excaps ! 0;
    src_root_cap <- returnOk $ excaps ! 1;
  
    src_slot <- lookup_source_slot src_root_cap src_index src_depth;
    pivot_slot <- lookup_pivot_slot pivot_root_cap pivot_index pivot_depth;

    whenE (pivot_slot = src_slot \<or> pivot_slot = dest_slot) $
      throwError IllegalOperation;

    unlessE (src_slot = dest_slot) $ ensure_empty dest_slot;

    src_cap <- liftE $ get_cap src_slot;
    whenE (src_cap = NullCap) $
      throwError $ FailedLookup True $ MissingCapability src_depth;

    pivot_cap <- liftE $ get_cap pivot_slot;
    whenE (pivot_cap = NullCap) $
      throwError $ FailedLookup False $ MissingCapability pivot_depth;

    new_src_cap \<leftarrow> returnOk $ update_cap_data True src_new_data src_cap;
    new_pivot_cap \<leftarrow> returnOk $ update_cap_data True pivot_new_data pivot_cap;

    whenE (new_src_cap = NullCap) $ throwError IllegalOperation;
    whenE (new_pivot_cap = NullCap) $ throwError IllegalOperation;

    returnOk $ RotateCall new_src_cap new_pivot_cap src_slot pivot_slot dest_slot
  odE
  else
    throwError TruncatedMessage
odE"

section "Threads"

text {* The definitions in this section decode invocations 
on TCBs. 
*}

text {* This definition checks whether the first argument is 
between the second and third. 
*}

definition
  range_check :: "word32 \<Rightarrow> word32 \<Rightarrow> word32 \<Rightarrow> (unit,'z::state_ext) se_monad"
where
  "range_check v min_v max_v \<equiv>
    unlessE (v \<ge> min_v \<and> v \<le> max_v) $
        throwError $ RangeError min_v max_v"

definition
  decode_read_registers :: "data list \<Rightarrow> cap \<Rightarrow> (tcb_invocation,'z::state_ext) se_monad"
where
"decode_read_registers data cap \<equiv> case data of
  flags#n#_ \<Rightarrow> doE
    range_check n 1 $ of_nat (length frameRegisters + length gpRegisters);
    p \<leftarrow> case cap of ThreadCap p \<Rightarrow> returnOk p;
    self \<leftarrow> liftE $ gets cur_thread;
    whenE (p = self) $ throwError IllegalOperation;
    returnOk $ ReadRegisters p (flags !! 0) n ARMNoExtraRegisters
  odE
| _ \<Rightarrow> throwError TruncatedMessage"

definition
  decode_copy_registers :: "data list \<Rightarrow> cap \<Rightarrow> cap list \<Rightarrow> (tcb_invocation,'z::state_ext) se_monad"
where
"decode_copy_registers data cap extra_caps \<equiv> case data of
  flags#_ \<Rightarrow>  doE
    suspend_source \<leftarrow> returnOk (flags !! 0);
    resume_target \<leftarrow> returnOk (flags !! 1);
    transfer_frame \<leftarrow> returnOk (flags !! 2);
    transfer_integer \<leftarrow> returnOk (flags !! 3);
    whenE (extra_caps = []) $ throwError TruncatedMessage;
    src_tcb \<leftarrow> (case extra_caps of 
      ThreadCap p # _ \<Rightarrow> returnOk p 
    | _ \<Rightarrow> throwError $ InvalidCapability 1);
    p \<leftarrow> case cap of ThreadCap p \<Rightarrow> returnOk p;
    returnOk $ CopyRegisters p src_tcb
                             suspend_source resume_target
                             transfer_frame transfer_integer 
                             ARMNoExtraRegisters
  odE
| _ \<Rightarrow>  throwError TruncatedMessage"


definition
  decode_write_registers :: "data list \<Rightarrow> cap \<Rightarrow> (tcb_invocation,'z::state_ext) se_monad"
where
"decode_write_registers data cap \<equiv> case data of
  flags#n#values \<Rightarrow> doE
    whenE (length values < unat n) $ throwError TruncatedMessage;
    p \<leftarrow> case cap of ThreadCap p \<Rightarrow> returnOk p;
    self \<leftarrow> liftE $ gets cur_thread;
    whenE (p = self) $ throwError IllegalOperation;
    returnOk $ WriteRegisters p (flags !! 0)
               (take (unat n) values) ARMNoExtraRegisters
  odE
| _ \<Rightarrow> throwError TruncatedMessage"


definition
  decode_set_priority :: "data list \<Rightarrow> cap \<Rightarrow> cslot_ptr \<Rightarrow> (tcb_invocation,'z::state_ext) se_monad"
where
  "decode_set_priority args cap slot \<equiv> 
     if length args = 0 then throwError TruncatedMessage
     else doE
       cur \<leftarrow> liftE $ gets cur_thread;
       OR_choice (decode_set_priority_error_choice (ucast $ args ! 0) cur)
           (throwError IllegalOperation)
           (returnOk (ThreadControl (obj_ref_of cap) slot None
             (Some (ucast $ args ! 0)) None None None))
     odE"


definition
  decode_set_ipc_buffer :: 
  "data list \<Rightarrow> cap \<Rightarrow> cslot_ptr \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow> (tcb_invocation,'z::state_ext) se_monad"
where
"decode_set_ipc_buffer args cap slot excs \<equiv> doE 
  whenE (length args = 0) $ throwError TruncatedMessage;
  whenE (length excs = 0) $ throwError TruncatedMessage;
  buffer \<leftarrow> returnOk $ data_to_vref $ args ! 0;
  (bcap, bslot) \<leftarrow> returnOk $ excs ! 0;
  newbuf \<leftarrow> if buffer = 0 then returnOk None
           else doE
      buffer_cap \<leftarrow> derive_cap bslot bcap;
      check_valid_ipc_buffer buffer buffer_cap;
      returnOk $ Some (buffer_cap, bslot)
    odE;
  returnOk $ 
    ThreadControl (obj_ref_of cap) slot None None None None (Some (buffer, newbuf))
odE"


definition
  decode_set_space 
  :: "data list \<Rightarrow> cap \<Rightarrow> cslot_ptr \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow> (tcb_invocation,'z::state_ext) se_monad"
where
  "decode_set_space args cap slot excaps \<equiv> doE
   whenE (length args < 3 \<or> length excaps < 2) $ throwError TruncatedMessage;
   fault_ep \<leftarrow> returnOk $ args ! 0;
   croot_data  \<leftarrow> returnOk $ args ! 1;
   vroot_data  \<leftarrow> returnOk $ args ! 2; 
   croot_arg  \<leftarrow> returnOk $ excaps ! 0;
   vroot_arg  \<leftarrow> returnOk $ excaps ! 1;
   can_chg_cr \<leftarrow> liftE $ liftM Not $ slot_cap_long_running_delete
                      $ get_tcb_ctable_ptr $ obj_ref_of cap;
   can_chg_vr \<leftarrow> liftE $ liftM Not $ slot_cap_long_running_delete
                      $ get_tcb_vtable_ptr $ obj_ref_of cap;
   unlessE (can_chg_cr \<and> can_chg_vr) $ throwError IllegalOperation;

   croot_cap  \<leftarrow> returnOk $ fst croot_arg;
   croot_slot \<leftarrow> returnOk $ snd croot_arg;
   croot_cap' \<leftarrow> derive_cap croot_slot $ 
                   (if croot_data = 0 then id else update_cap_data False croot_data) 
                   croot_cap;
   unlessE (is_cnode_cap croot_cap') $ throwError IllegalOperation;
   croot \<leftarrow> returnOk (croot_cap', croot_slot);

   vroot_cap  \<leftarrow> returnOk $ fst vroot_arg;
   vroot_slot \<leftarrow> returnOk $ snd vroot_arg;
   vroot_cap' \<leftarrow> derive_cap vroot_slot $ 
                   (if vroot_data = 0 then id else update_cap_data False vroot_data) 
                   vroot_cap;
   unlessE (is_valid_vtable_root vroot_cap') $ throwError IllegalOperation;
   vroot \<leftarrow> returnOk (vroot_cap', vroot_slot);       
   
   returnOk $ ThreadControl (obj_ref_of cap) slot (Some (to_bl fault_ep)) None 
                            (Some croot) (Some vroot) None
 odE"


definition
  decode_tcb_configure :: 
  "data list \<Rightarrow> cap \<Rightarrow> cslot_ptr \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow> (tcb_invocation,'z::state_ext) se_monad"
where
  "decode_tcb_configure args cap slot extra_caps \<equiv> doE
     whenE (length args < 5) $ throwError TruncatedMessage;
     whenE (length extra_caps < 3) $ throwError TruncatedMessage;
     fault_ep \<leftarrow> returnOk $ args ! 0;
     prio     \<leftarrow> returnOk $ args ! 1;
     croot_data \<leftarrow> returnOk $ args ! 2;
     vroot_data \<leftarrow> returnOk $ args ! 3;
     crootvroot \<leftarrow> returnOk $ take 2 extra_caps;
     buffer_cap \<leftarrow> returnOk $ extra_caps ! 2;
     buffer \<leftarrow> returnOk $ args ! 4;
     set_prio \<leftarrow> decode_set_priority [prio] cap slot;
     set_params \<leftarrow> decode_set_ipc_buffer [buffer] cap slot [buffer_cap];
     set_space \<leftarrow> decode_set_space [fault_ep, croot_data, vroot_data] cap slot crootvroot;
     returnOk $ ThreadControl (obj_ref_of cap) slot (tc_new_fault_ep set_space)
                              (tc_new_priority set_prio)
                              (tc_new_croot set_space) (tc_new_vroot set_space) 
                              (tc_new_buffer set_params)
   odE" 

definition
  decode_bind_aep ::
  "cap \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow> (tcb_invocation,'z::state_ext) se_monad"
where
  "decode_bind_aep cap extra_caps \<equiv> case cap of
    ThreadCap tcb \<Rightarrow> doE
     whenE (length extra_caps = 0) $ throwError TruncatedMessage;
     aEP \<leftarrow> liftE $ get_bound_aep tcb;
     case aEP of
         Some _ \<Rightarrow> throwError IllegalOperation
       | None \<Rightarrow> returnOk ();
     (aepptr, rights) \<leftarrow> case fst (hd extra_caps) of
         AsyncEndpointCap ptr _ r \<Rightarrow> returnOk (ptr, r)
       | _ \<Rightarrow> throwError IllegalOperation;
     aep \<leftarrow> liftE  $ get_async_ep aepptr;
     case (aep_obj aep, aep_bound_tcb aep) of
         (IdleAEP, None) \<Rightarrow> returnOk ()
       | (ActiveAEP _, None) \<Rightarrow> returnOk ()
       | _ \<Rightarrow> throwError IllegalOperation;
     (if AllowRecv \<in> rights
      then returnOk $ AsyncEndpointControl tcb (Some aepptr)
      else throwError IllegalOperation)
   odE
 | _ \<Rightarrow> throwError IllegalOperation"
     
     
definition 
  decode_unbind_aep :: "cap \<Rightarrow> (tcb_invocation,'z::state_ext) se_monad"
where
  "decode_unbind_aep cap \<equiv> case cap of
     ThreadCap tcb \<Rightarrow> doE
       aEP \<leftarrow> liftE $ get_bound_aep tcb;
       case aEP of
           None \<Rightarrow> throwError IllegalOperation
         | Some _ \<Rightarrow> returnOk ();
       returnOk $ AsyncEndpointControl tcb None
    odE
 | _ \<Rightarrow> throwError IllegalOperation"

definition
  decode_tcb_invocation :: 
  "data \<Rightarrow> data list \<Rightarrow> cap \<Rightarrow> cslot_ptr \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow> 
  (tcb_invocation,'z::state_ext) se_monad"
where
 "decode_tcb_invocation label args cap slot excs \<equiv>
  case invocation_type label of
      TCBReadRegisters \<Rightarrow> decode_read_registers args cap
    | TCBWriteRegisters \<Rightarrow> decode_write_registers args cap
    | TCBCopyRegisters \<Rightarrow> decode_copy_registers args cap $ map fst excs
    | TCBSuspend \<Rightarrow> returnOk $ Suspend $ obj_ref_of cap
    | TCBResume \<Rightarrow> returnOk $ Resume $ obj_ref_of cap
    | TCBConfigure \<Rightarrow> decode_tcb_configure args cap slot excs
    | TCBSetPriority \<Rightarrow> decode_set_priority args cap slot 
    | TCBSetIPCBuffer \<Rightarrow> decode_set_ipc_buffer args cap slot excs
    | TCBSetSpace \<Rightarrow> decode_set_space args cap slot excs
    | TCBBindAEP \<Rightarrow> decode_bind_aep cap excs
    | TCBUnbindAEP \<Rightarrow> decode_unbind_aep cap
    | _ \<Rightarrow> throwError IllegalOperation"

definition
  decode_domain_invocation ::
  "data \<Rightarrow> data list \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow>
    ((obj_ref \<times> domain), 'z::state_ext) se_monad"
where
  "decode_domain_invocation label args excs \<equiv> doE
     whenE (invocation_type label \<noteq> DomainSetSet) $ throwError IllegalOperation;
     domain \<leftarrow> (case args of
       x # xs \<Rightarrow> doE
         whenE (unat x \<ge> num_domains) $ throwError $ InvalidArgument 0;
         returnOk (ucast x)
       odE
       | _ \<Rightarrow> throwError TruncatedMessage);
     whenE (length excs = 0) $ throwError TruncatedMessage;
     case (fst (hd excs)) of ThreadCap ptr \<Rightarrow> returnOk $ (ptr, domain)
       | _ \<Rightarrow> throwError $ InvalidArgument 1
   odE"

section "IRQ"

text {* The following two definitions decode system calls for the
interrupt controller and interrupt handlers *}

definition
  decode_irq_control_invocation :: "data \<Rightarrow> data list \<Rightarrow> cslot_ptr \<Rightarrow> cap list
                                     \<Rightarrow> (irq_control_invocation,'z::state_ext) se_monad" where
 "decode_irq_control_invocation label args src_slot cps \<equiv>
  (if invocation_type label = IRQIssueIRQHandler
    then if length args \<ge> 3 \<and> length cps \<ge> 1
      then let x = args ! 0; index = args ! 1; depth = args ! 2;
               cnode = cps ! 0; irqv = ucast x in doE
        whenE (x > ucast maxIRQ) $ 
          throwError (RangeError 0 (ucast maxIRQ));
        irq_active \<leftarrow> liftE $ is_irq_active irqv;
        whenE irq_active $ throwError RevokeFirst;

        dest_slot \<leftarrow> lookup_target_slot
               cnode (data_to_cptr index) (unat depth);
        ensure_empty dest_slot;

        returnOk $ IRQControl irqv dest_slot src_slot
      odE
    else throwError TruncatedMessage
  else if invocation_type label = IRQInterruptControl
    then liftME InterruptControl
         $ arch_decode_interrupt_control args cps
  else throwError IllegalOperation)"

definition
  data_to_bool :: "data \<Rightarrow> bool"
where
  "data_to_bool d \<equiv> d \<noteq> 0" 

definition
  decode_irq_handler_invocation :: "data \<Rightarrow> data list \<Rightarrow> irq \<Rightarrow> (cap \<times> cslot_ptr) list
                                     \<Rightarrow> (irq_handler_invocation,'z::state_ext) se_monad" where
 "decode_irq_handler_invocation label args irq cps \<equiv>
  if invocation_type label = IRQAckIRQ
    then returnOk $ ACKIrq irq
  else if invocation_type label = IRQSetIRQHandler
    then if cps \<noteq> []
      then let (cap, slot) = hd cps in
      if is_aep_cap cap \<and> AllowSend \<in> cap_rights cap
      then returnOk $ SetIRQHandler irq cap slot
      else throwError $ InvalidCapability 0
    else throwError TruncatedMessage
  else if invocation_type label = IRQClearIRQHandler
    then returnOk $ ClearIRQHandler irq
  else if invocation_type label = IRQSetMode
    then if length args \<ge> 2
      then let trig = args ! 0; pol = args ! 1 in 
        returnOk $ SetMode irq (data_to_bool trig) (data_to_bool pol)
      else throwError TruncatedMessage
  else throwError IllegalOperation"

section "Untyped"

text {* The definitions in this section deal with decoding invocations 
of untyped memory capabilities. 
*}

definition
  arch_data_to_obj_type :: "nat \<Rightarrow> aobject_type option" where
 "arch_data_to_obj_type n \<equiv>
  if n = 0 then Some SmallPageObj
  else if n = 1 then Some LargePageObj
  else if n = 2 then Some SectionObj
  else if n = 3 then Some SuperSectionObj
  else if n = 4 then Some PageTableObj
  else if n = 5 then Some PageDirectoryObj
  else None"

definition
  data_to_obj_type :: "data \<Rightarrow> (apiobject_type,'z::state_ext) se_monad" where
  "data_to_obj_type type \<equiv> doE
    n \<leftarrow> returnOk $ data_to_nat type;
    if n = 0 then
      returnOk $ Untyped
    else if n = 1 then
      returnOk $ TCBObject
    else if n = 2 then
      returnOk $ EndpointObject
    else if n = 3 then
      returnOk $ AsyncEndpointObject
    else if n = 4 then
      returnOk $ CapTableObject
    else (case arch_data_to_obj_type (n - 5)
       of Some tp \<Rightarrow> returnOk (ArchObject tp)
        | None \<Rightarrow> throwError (InvalidArgument 0))
  odE"

definition
  get_free_ref :: "obj_ref \<Rightarrow> nat \<Rightarrow> obj_ref" where
  "get_free_ref base free_index \<equiv> base +  (of_nat free_index)"

definition
  get_free_index :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> nat" where
  "get_free_index base free \<equiv> unat $ (free - base)"

definition
  decode_untyped_invocation :: 
  "data \<Rightarrow> data list \<Rightarrow> cslot_ptr \<Rightarrow> cap \<Rightarrow> cap list \<Rightarrow> (untyped_invocation,'z::state_ext) se_monad"
where
"decode_untyped_invocation label args slot cap excaps \<equiv> doE
  unlessE (invocation_type label = UntypedRetype) $ throwError IllegalOperation;
  whenE (length args < 6) $ throwError TruncatedMessage;
  whenE (length excaps = 0) $ throwError TruncatedMessage;
  root_cap \<leftarrow> returnOk $ excaps ! 0;
  new_type \<leftarrow> data_to_obj_type (args!0);

  user_obj_size \<leftarrow> returnOk $ data_to_nat (args!1);
  unlessE (user_obj_size < word_bits - 1)
    $ throwError (RangeError 0 (of_nat word_bits - 2));
  whenE (new_type = CapTableObject \<and> user_obj_size = 0) 
    $ throwError (InvalidArgument 1);
  whenE (new_type = Untyped \<and> user_obj_size < 4) 
    $ throwError (InvalidArgument 1);
  node_index \<leftarrow> returnOk $ data_to_cptr (args!2);
  node_depth \<leftarrow> returnOk $ data_to_nat (args!3);

  node_cap \<leftarrow> if node_depth = 0
        then returnOk root_cap
        else doE
            node_slot \<leftarrow> lookup_target_slot
                root_cap node_index node_depth;
            liftE $ get_cap node_slot
        odE;

  if is_cnode_cap node_cap 
        then  returnOk ()
        else  throwError $ FailedLookup False $ MissingCapability node_depth;

  node_offset \<leftarrow> returnOk $ data_to_nat (args ! 4);
  node_window \<leftarrow> returnOk $ data_to_nat (args ! 5);
  radix_bits \<leftarrow> returnOk $ bits_of node_cap;
  node_size \<leftarrow> returnOk (2 ^ radix_bits);

  whenE (node_offset < 0 \<or> node_offset > node_size - 1) $
    throwError $ RangeError 0 (of_nat (node_size - 1));

  whenE (node_window < 1 \<or> node_window > 256) $ throwError $ RangeError 1 256;

  whenE (node_window < 1 \<or> node_window > node_size - node_offset) $
    throwError $ RangeError 1 (of_nat (node_size - node_offset));

  oref \<leftarrow> returnOk $ obj_ref_of node_cap;
  offsets \<leftarrow> returnOk $ map (nat_to_cref radix_bits) 
                           [node_offset ..< node_offset + node_window];
  slots \<leftarrow> returnOk $ map (\<lambda>cref. (oref, cref)) offsets;

  mapME_x ensure_empty slots;

  free_index \<leftarrow> liftE $ const_on_failure (free_index_of cap) $ (doE
    ensure_no_children slot;
    returnOk 0
  odE);

  free_ref \<leftarrow> returnOk ( get_free_ref (obj_ref_of cap) free_index);
  object_size \<leftarrow> returnOk ( obj_bits_api new_type user_obj_size);
  aligned_free_ref \<leftarrow> returnOk ( alignUp free_ref object_size);
  untyped_free_bytes \<leftarrow> returnOk (obj_size cap - of_nat (free_index));

  max_count \<leftarrow> returnOk ( untyped_free_bytes >> object_size);
  whenE (unat max_count < node_window) $
        throwError $ NotEnoughMemory $ untyped_free_bytes;
  (ptr, block_size) \<leftarrow> case cap of 
                        UntypedCap p n f \<Rightarrow> returnOk (p,n) 
                      | _ \<Rightarrow> fail;
  returnOk $ Retype slot ptr aligned_free_ref new_type user_obj_size slots
odE"

section "Toplevel invocation decode."

text {* This definition is the toplevel decoding definition; it dispatches
to the above definitions, after checking, in some cases, whether the 
invocation is allowed.
*}

definition
  decode_invocation :: 
  "data \<Rightarrow> data list \<Rightarrow> cap_ref \<Rightarrow> cslot_ptr \<Rightarrow> cap \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow> (invocation,'z::state_ext) se_monad"
where
  "decode_invocation label args cap_index slot cap excaps \<equiv> 
  case cap of
    EndpointCap ptr badge rights \<Rightarrow>
      if AllowSend \<in> rights then
        returnOk $ InvokeEndpoint ptr badge (AllowGrant \<in> rights)
      else throwError $ InvalidCapability 0
  | AsyncEndpointCap ptr badge rights \<Rightarrow>
      if AllowSend \<in> rights then
        returnOk $ InvokeAsyncEndpoint ptr badge
      else throwError $ InvalidCapability 0
  | ReplyCap thread False \<Rightarrow>
      returnOk $ InvokeReply thread slot
  | IRQControlCap \<Rightarrow>
      liftME InvokeIRQControl
        $ decode_irq_control_invocation label args slot (map fst excaps)
  | IRQHandlerCap irq \<Rightarrow>
      liftME InvokeIRQHandler
        $ decode_irq_handler_invocation label args irq excaps
  | ThreadCap ptr \<Rightarrow>
      liftME InvokeTCB $ decode_tcb_invocation label args cap slot excaps
  | DomainCap \<Rightarrow>
      liftME (split InvokeDomain) $ decode_domain_invocation label args excaps
  | CNodeCap ptr bits _ \<Rightarrow>
      liftME InvokeCNode $ decode_cnode_invocation label args cap (map fst excaps)
  | UntypedCap ptr sz fi \<Rightarrow>
      liftME InvokeUntyped $ decode_untyped_invocation label args slot cap (map fst excaps)
  | ArchObjectCap arch_cap \<Rightarrow>
      liftME InvokeArchObject $ 
        arch_decode_invocation label args cap_index slot arch_cap excaps
  | _ \<Rightarrow> 
      throwError $ InvalidCapability 0"

end
