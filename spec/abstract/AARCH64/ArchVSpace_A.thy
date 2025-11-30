(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2022, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "AARCH64 VSpace Functions"

theory ArchVSpace_A
imports
  Retype_A
  VCPUAcc_A
begin

context Arch begin arch_global_naming (A)

text \<open>
  Look up a thread's IPC buffer and check that the thread has the authority to read or (in the
  receiver case) write to it.\<close>
definition lookup_ipc_buffer :: "bool \<Rightarrow> obj_ref \<Rightarrow> (obj_ref option,'z::state_ext) s_monad" where
  "lookup_ipc_buffer is_receiver thread \<equiv> do
     buffer_ptr \<leftarrow> thread_get tcb_ipc_buffer thread;
     buffer_frame_slot \<leftarrow> return (thread, tcb_cnode_index 4);
     buffer_cap \<leftarrow> get_cap buffer_frame_slot;
     case buffer_cap of
       ArchObjectCap (FrameCap p R vms False _) \<Rightarrow>
         if vm_read_write \<subseteq> R \<or> vm_read_only \<subseteq> R \<and> \<not>is_receiver
         then return $ Some $ p + (buffer_ptr && mask (pageBitsForSize vms))
         else return None
     | _ \<Rightarrow> return None
   od"

definition pool_for_asid :: "asid \<Rightarrow> 'z::state_ext state \<Rightarrow> obj_ref option" where
  "pool_for_asid asid \<equiv> \<lambda>s. asid_table s (asid_high_bits_of asid)"

definition entry_for_pool :: "obj_ref \<Rightarrow> asid \<Rightarrow> (obj_ref \<rightharpoonup> asid_pool) \<Rightarrow> asid_pool_entry option"
  where
  "entry_for_pool pool_ptr asid \<equiv> do {
     pool \<leftarrow> oapply pool_ptr;
     K $ pool (asid_low_bits_of asid)
   }"

definition vspace_for_pool :: "obj_ref \<Rightarrow> asid \<Rightarrow> (obj_ref \<rightharpoonup> asid_pool) \<Rightarrow> obj_ref option" where
  "vspace_for_pool pool_ptr asid \<equiv> do {
     entry \<leftarrow> entry_for_pool pool_ptr asid;
     oreturn $ ap_vspace entry
   }"

(* this is what asid_map encodes in ARM/ARM_HYP; getASIDPoolEntry in Haskell *)
definition entry_for_asid :: "asid \<Rightarrow> 'z::state_ext state \<Rightarrow> asid_pool_entry option" where
  "entry_for_asid asid = do {
     pool_ptr \<leftarrow> pool_for_asid asid;
     entry_for_pool pool_ptr asid \<circ> asid_pools_of
   }"

(* update an entry in the asid map *)
definition update_asid_pool_entry ::
  "(asid_pool_entry \<rightharpoonup> asid_pool_entry) \<Rightarrow> asid \<Rightarrow> (unit, 'z::state_ext) s_monad" where
  "update_asid_pool_entry f asid \<equiv> do
     pool_ptr \<leftarrow> gets_the $ pool_for_asid asid;
     pool \<leftarrow> get_asid_pool pool_ptr;
     idx \<leftarrow> return $ asid_low_bits_of asid;
     entry \<leftarrow> assert_opt $ pool idx;
     set_asid_pool pool_ptr (pool (idx := f entry))
   od"

definition vspace_for_asid :: "asid \<Rightarrow> 'z::state_ext state \<Rightarrow> obj_ref option" where
  "vspace_for_asid asid = do {
     oassert (0 < asid);
     entry \<leftarrow> entry_for_asid asid;
     oreturn $ ap_vspace entry
   }"

text \<open>Locate the top-level page table associated with a given virtual ASID.\<close>
definition find_vspace_for_asid :: "asid \<Rightarrow> (obj_ref,'z::state_ext) lf_monad" where
  "find_vspace_for_asid asid \<equiv> doE
     vspace_opt \<leftarrow> liftE $ gets $ vspace_for_asid asid;
     throw_opt InvalidRoot vspace_opt
   odE"

definition load_vmid :: "asid \<Rightarrow> (vmid option, 'z::state_ext) s_monad" where
  "load_vmid asid \<equiv> do
     entry \<leftarrow> gets_the $ entry_for_asid asid;
     return $ ap_vmid entry
   od"

text \<open>Associate a VMID with an ASID.\<close>
definition store_vmid :: "asid \<Rightarrow> vmid \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "store_vmid asid hw_asid \<equiv> do
     update_asid_pool_entry (\<lambda>entry. Some $ ASIDPoolVSpace (Some hw_asid) (ap_vspace entry)) asid;
     vmid_table \<leftarrow> gets (arm_vmid_table \<circ> arch_state);
     vmid_table' \<leftarrow> return $ vmid_table (hw_asid \<mapsto> asid);
     modify (\<lambda>s. s \<lparr> arch_state := (arch_state s) \<lparr> arm_vmid_table := vmid_table' \<rparr>\<rparr>)
   od"

text \<open>Clear all TLB mappings associated with this ASID.\<close>
definition invalidate_tlb_by_asid :: "asid \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "invalidate_tlb_by_asid asid \<equiv> do
     maybe_vmid \<leftarrow> load_vmid asid;
     case maybe_vmid of
       None \<Rightarrow> return ()
     | Some vmid \<Rightarrow> do_machine_op $ invalidateTranslationASID (ucast vmid)
   od"

text \<open>Clear all TLB mappings associated with this ASID and virtual address.\<close>
definition invalidate_tlb_by_asid_va :: "asid \<Rightarrow> vspace_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "invalidate_tlb_by_asid_va asid vaddr \<equiv> do
     maybe_vmid \<leftarrow> load_vmid asid;
     case maybe_vmid of
       None \<Rightarrow> return ()
     | Some vmid \<Rightarrow>
         do_machine_op $
           invalidateTranslationSingle $ (ucast vmid << word_bits-asid_bits) || (vaddr >> pageBits)
   od"

text \<open>Remove any mapping from this virtual ASID to a VMID.\<close>
definition invalidate_asid :: "asid \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "invalidate_asid asid \<equiv>
     update_asid_pool_entry (\<lambda>entry. Some $ ASIDPoolVSpace None (ap_vspace entry)) asid"

text \<open>Remove any mapping from this VMID to an ASID.\<close>
definition invalidate_vmid_entry :: "vmid \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "invalidate_vmid_entry vmid \<equiv> do
     vmid_table \<leftarrow> gets (arm_vmid_table \<circ> arch_state);
     vmid_table' \<leftarrow> return (vmid_table (vmid := None));
     modify (\<lambda>s. s \<lparr> arch_state := (arch_state s) \<lparr> arm_vmid_table := vmid_table' \<rparr>\<rparr>)
  od"

text \<open>Remove mappings in either direction involving this ASID.\<close>
definition invalidate_asid_entry :: "asid \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "invalidate_asid_entry asid \<equiv> do
     maybe_vmid \<leftarrow> load_vmid asid;
     when (maybe_vmid \<noteq> None) $ invalidate_vmid_entry (the maybe_vmid);
     invalidate_asid asid
  od"

text \<open>Locate a VMID that is not in use, if necessary by reclaiming one already assigned to an ASID.\<close>
definition find_free_vmid :: "(vmid,'z::state_ext) s_monad" where
  "find_free_vmid \<equiv> do
     vmid_table \<leftarrow> gets (arm_vmid_table \<circ> arch_state);
     next_vmid \<leftarrow> gets (arm_next_vmid \<circ> arch_state);
     maybe_vmid \<leftarrow> return $ find (\<lambda>a. vmid_table a = None)
                                 (take (length [minBound :: vmid .e. maxBound])
                                       ([next_vmid .e. maxBound] @ [minBound .e. next_vmid]));
     case maybe_vmid of
       Some vmid \<Rightarrow> return vmid
     | None \<Rightarrow> do
         invalidate_asid $ the $ vmid_table next_vmid;
         do_machine_op $ invalidateTranslationASID (ucast next_vmid);
         invalidate_vmid_entry next_vmid;
         modify (\<lambda>s. s \<lparr> arch_state := (arch_state s) \<lparr> arm_next_vmid := next_vmid + 1 \<rparr>\<rparr>);
         return next_vmid
       od
   od"

text \<open>Get the VMID associated with an ASID, assigning one if none is already assigned.\<close>
definition get_vmid :: "asid \<Rightarrow> (vmid, 'z::state_ext) s_monad" where
  "get_vmid asid \<equiv> do
     maybe_vmid \<leftarrow> load_vmid asid;
     case maybe_vmid of
       Some vmid \<Rightarrow> return vmid
     | None \<Rightarrow>  do
         new_hw_asid \<leftarrow> find_free_vmid;
         store_vmid asid new_hw_asid;
         return new_hw_asid
       od
   od"

text \<open>
  Format a VM fault message to be passed to a thread's supervisor after it encounters a page fault.\<close>
definition handle_vm_fault :: "obj_ref \<Rightarrow> vmfault_type \<Rightarrow> (unit, 'z::state_ext) f_monad" where
  "handle_vm_fault thread fault \<equiv> case fault of
     ARMDataAbort \<Rightarrow> doE
       addr \<leftarrow> liftE $ do_machine_op getFAR;
       fault \<leftarrow> liftE $ do_machine_op getESR;
       cur_v \<leftarrow> liftE $ gets (arm_current_vcpu \<circ> arch_state);
       addr \<leftarrow> if (\<exists>v. cur_v = Some (v, True)) \<comment> \<open>VCPU active\<close>
              then doE
                  \<comment> \<open>address bits of PAR register after S1 translation\<close>
                  par_el1_mask \<leftarrow> returnOk $ 0xfffffffff000;
                  addr' \<leftarrow> liftE $ do_machine_op $ addressTranslateS1 addr;
                  returnOk $ (addr' && par_el1_mask) || (addr && mask pageBits)
                odE
              else returnOk addr;
       \<comment> \<open>32 is the width of the FSR field in the C VMFault structure\<close>
       throwError $ ArchFault $ VMFault addr [0, fault && mask 32]
     odE
   | ARMPrefetchAbort \<Rightarrow> doE
       pc \<leftarrow> liftE $ as_user thread $ getRestartPC;
       fault \<leftarrow> liftE $ do_machine_op getESR;
       cur_v \<leftarrow> liftE $ gets (arm_current_vcpu \<circ> arch_state);
       pc \<leftarrow> if (\<exists>v. cur_v = Some (v, True)) \<comment> \<open>VCPU active\<close>
            then doE
                \<comment> \<open>address bits of PAR register after S1 translation\<close>
                par_el1_mask \<leftarrow> returnOk $ 0xfffffffff000;
                pc' \<leftarrow> liftE $ do_machine_op $ addressTranslateS1 pc;
                returnOk $ (pc' && par_el1_mask) || (pc && mask pageBits)
              odE
            else returnOk pc;
       \<comment> \<open>32 is the width of the FSR field in the C VMFault structure\<close>
       throwError $ ArchFault $ VMFault pc [1, fault && mask 32]
     odE"


text \<open>Switch to given address space, using VMID associated with provided ASID.\<close>
definition arm_context_switch :: "obj_ref \<Rightarrow> asid \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "arm_context_switch vspace asid = do
     vmid <- get_vmid asid;
     do_machine_op $ setVSpaceRoot (addrFromPPtr vspace) (ucast vmid)
   od"


text \<open>Switch to global user address space, using VMID 0.\<close>
definition set_global_user_vspace :: "(unit,'z::state_ext) s_monad" where
  "set_global_user_vspace = do
     global <- gets (arm_us_global_vspace \<circ> arch_state);
     do_machine_op $ setVSpaceRoot (addrFromKPPtr global) 0
   od"

text \<open>
  Switch into the address space of a given thread or the global address space if none is correctly
  configured.\<close>
definition set_vm_root :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "set_vm_root tcb \<equiv> do
     thread_root_slot \<leftarrow> return (tcb, tcb_cnode_index 1);
     thread_root \<leftarrow> get_cap thread_root_slot;
     (case thread_root of
        ArchObjectCap (PageTableCap pt VSRootPT_T (Some (asid, _))) \<Rightarrow> doE
          pt' \<leftarrow> find_vspace_for_asid asid;
          whenE (pt \<noteq> pt') $ throwError InvalidRoot;
          liftE $ arm_context_switch pt asid
        odE
      | _ \<Rightarrow> throwError InvalidRoot) <catch> (\<lambda>_. set_global_user_vspace)
  od"


definition delete_asid_pool :: "asid \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "delete_asid_pool base ptr \<equiv> do
     assert (asid_low_bits_of base = 0);
     asid_table \<leftarrow> gets asid_table;
     when (asid_table (asid_high_bits_of base) = Some ptr) $ do
       pool \<leftarrow> get_asid_pool ptr;
       mapM (\<lambda>offset. when (pool (ucast offset) \<noteq> None) $ do
                            invalidate_tlb_by_asid $ base + offset;
                            invalidate_asid_entry $ base + offset
                      od) [0  .e.  mask asid_low_bits];
       asid_table' \<leftarrow> return $ asid_table (asid_high_bits_of base:= None);
       modify (\<lambda>s. s \<lparr> arch_state := (arch_state s) \<lparr> arm_asid_table := asid_table' \<rparr>\<rparr>);
       tcb \<leftarrow> gets cur_thread;
       set_vm_root tcb
     od
   od"


definition delete_asid :: "asid \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "delete_asid asid pt \<equiv> do
     pool_ptr_op \<leftarrow> gets (pool_for_asid asid);
     case pool_ptr_op of
       None \<Rightarrow> return ()
     | Some pool_ptr \<Rightarrow> do
         pool \<leftarrow> get_asid_pool pool_ptr;
         when (\<exists>vmid. pool (asid_low_bits_of asid) = Some (ASIDPoolVSpace vmid pt)) $ do
           invalidate_tlb_by_asid asid;
           invalidate_asid_entry asid;
           \<comment> \<open>re-read here, because @{text invalidate_asid_entry} changes the ASID pool:\<close>
           pool \<leftarrow> get_asid_pool pool_ptr;
           pool' \<leftarrow> return $ pool (asid_low_bits_of asid := None);
           set_asid_pool pool_ptr pool';
           tcb \<leftarrow> gets cur_thread;
           set_vm_root tcb
         od
       od
   od"


definition unmap_page_table :: "asid \<Rightarrow> vspace_ref \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "unmap_page_table asid vaddr pt \<equiv> doE
     top_level_pt \<leftarrow> find_vspace_for_asid asid;
     (pt_slot, level) \<leftarrow> pt_lookup_from_level max_pt_level top_level_pt vaddr pt;
     liftE $ store_pte (level_type level) pt_slot InvalidPTE;
     liftE $ do_machine_op $ cleanByVA_PoU pt_slot (addrFromPPtr pt_slot);
     liftE $ invalidate_tlb_by_asid asid
   odE <catch> (K $ return ())"

text \<open>
  Look up an @{text "asid+vspace_ref"} down to the provided level in the page table.
  For level @{term bot_level}, return a pointer to a table at the returned level.
  The level can be higher than @{term bot_level} if the lookup terminates early because
  it hit a page or an invalid entry.\<close>
definition vs_lookup_table ::
  "vm_level \<Rightarrow> asid \<Rightarrow> vspace_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> (vm_level \<times> obj_ref) option" where
  "vs_lookup_table bot_level asid vptr \<equiv> do {
     pool_ptr \<leftarrow> pool_for_asid asid;
     if bot_level = asid_pool_level
     then oreturn (asid_pool_level, pool_ptr)
     else do {
       top_level_pt \<leftarrow> vspace_for_pool pool_ptr asid \<circ> asid_pools_of;
       pt_walk max_pt_level bot_level top_level_pt vptr \<circ> ptes_of
     }
   }"

text \<open>
  Same as @{const vs_lookup_table}, but return a pointer to a slot in a table at the returned level.
  For @{prop "bot_level = asid_pool_level"}, still return the pointer to the ASID pool (not a slot
  inside it, since there are no slot functions for ASID pools).\<close>
definition vs_lookup_slot ::
  "vm_level \<Rightarrow> asid \<Rightarrow> vspace_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> (vm_level \<times> obj_ref) option" where
  "vs_lookup_slot bot_level asid vref \<equiv> do {
     (level', table) \<leftarrow> vs_lookup_table bot_level asid vref;
     if level' = asid_pool_level then
       oreturn (level', table)
     else
       oreturn (level', pt_slot_offset level' table vref)
   }"

text \<open>Unmap a mapped page if the given mapping details are still current.\<close>
definition unmap_page :: "vmpage_size \<Rightarrow> asid \<Rightarrow> vspace_ref \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
  where
  "unmap_page pgsz asid vptr pptr \<equiv> doE
     top_level_pt \<leftarrow> find_vspace_for_asid asid;
     (lev, slot) \<leftarrow> liftE $ gets_the $ pt_lookup_slot top_level_pt vptr \<circ> ptes_of;
     unlessE (pt_bits_left lev = pageBitsForSize pgsz) $ throwError InvalidRoot;
     pte \<leftarrow> liftE $ get_pte lev slot;
     unlessE (is_PagePTE pte \<and> pptr_from_pte pte = pptr) $ throwError InvalidRoot;
     liftE $ store_pte lev slot InvalidPTE;
     liftE $ do_machine_op $ cleanByVA_PoU slot (addrFromPPtr slot);
     liftE $ invalidate_tlb_by_asid_va asid vptr
   odE <catch> (K $ return ())"

text \<open>
  Page table structure capabilities cannot be copied until they have an ASID and location
  assigned. This is because they cannot have multiple current ASIDs and cannot be shared between
  address spaces or virtual locations.\<close>
definition arch_derive_cap :: "arch_cap \<Rightarrow> (cap,'z::state_ext) se_monad" where
  "arch_derive_cap c \<equiv>
     case c of
       PageTableCap _ _ (Some x) \<Rightarrow> returnOk (ArchObjectCap c)
     | PageTableCap _ _ None \<Rightarrow> throwError IllegalOperation
     | FrameCap r R sz dev mp \<Rightarrow> returnOk $ ArchObjectCap (FrameCap r R sz dev None)
     | ASIDControlCap \<Rightarrow> returnOk (ArchObjectCap c)
     | ASIDPoolCap _ _ \<Rightarrow> returnOk (ArchObjectCap c)
     | VCPUCap _ \<Rightarrow> returnOk (ArchObjectCap c)
     | SGISignalCap _ _ \<Rightarrow> returnOk (ArchObjectCap c)"

text \<open>No user-modifiable data is stored in AARCH64-specific capabilities.\<close>
definition arch_update_cap_data :: "bool \<Rightarrow> data \<Rightarrow> arch_cap \<Rightarrow> cap" where
  "arch_update_cap_data preserve data c \<equiv> ArchObjectCap c"


text \<open>Actions that must be taken on finalisation of AARCH64-specific capabilities.\<close>
definition arch_finalise_cap :: "arch_cap \<Rightarrow> bool \<Rightarrow> (cap \<times> cap,'z::state_ext) s_monad" where
  "arch_finalise_cap c x \<equiv> case (c, x) of
     (ASIDPoolCap ptr b, True) \<Rightarrow>  do
       delete_asid_pool b ptr;
       return (NullCap, NullCap)
     od
   | (PageTableCap ptr VSRootPT_T (Some (a, v)), True) \<Rightarrow> do
       delete_asid a ptr;
       return (NullCap, NullCap)
     od
   | (PageTableCap ptr NormalPT_T (Some (a, v)), True) \<Rightarrow> do
       unmap_page_table a v ptr;
       return (NullCap, NullCap)
     od
   | (FrameCap ptr _ sz _ (Some (a, v)), _) \<Rightarrow> do
       unmap_page sz a v ptr;
       return (NullCap, NullCap)
     od
   | (VCPUCap vcpu_ref, True) \<Rightarrow> do
      vcpu_finalise vcpu_ref;
      return (NullCap, NullCap)
     od
   | (SGISignalCap _ _, _) \<Rightarrow>
      return (NullCap, NullCap) \<comment> \<open>nothing to do for @{const SGISignalCap}\<close>
   | _ \<Rightarrow> return (NullCap, NullCap)"


text \<open>
  A thread's virtual address space capability must be to a mapped page table to be valid on
  the AARCH64 architecture.\<close>
definition is_valid_vtable_root :: "cap \<Rightarrow> bool" where
  "is_valid_vtable_root c \<equiv>
     case c of ArchObjectCap (PageTableCap _ VSRootPT_T (Some _)) \<Rightarrow> True | _ \<Rightarrow> False"

text \<open>Make numeric value of @{const msg_align_bits} visible.\<close>
lemmas msg_align_bits = msg_align_bits'[unfolded word_size_bits_def, simplified]

definition check_valid_ipc_buffer :: "vspace_ref \<Rightarrow> cap \<Rightarrow> (unit,'z::state_ext) se_monad" where
  "check_valid_ipc_buffer vptr c \<equiv>
     case c of
       ArchObjectCap (FrameCap _ _ _ False _) \<Rightarrow>
         whenE (\<not> is_aligned vptr msg_align_bits) $ throwError AlignmentError
     | _ \<Rightarrow> throwError IllegalOperation"

text \<open>A pointer is inside a user frame if its top bits point to a @{const DataPage}.\<close>
definition in_user_frame :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
  "in_user_frame p s \<equiv>
     \<exists>sz. kheap s (p && ~~ mask (pageBitsForSize sz)) = Some (ArchObj (DataPage False sz))"

definition prepare_thread_delete :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "prepare_thread_delete thread_ptr \<equiv> do
     t_vcpu \<leftarrow> arch_thread_get tcb_vcpu thread_ptr;
     case t_vcpu of
       Some v \<Rightarrow> dissociate_vcpu_tcb v thread_ptr
     | None \<Rightarrow> return ();
     fpu_release thread_ptr
   od"

end
end
