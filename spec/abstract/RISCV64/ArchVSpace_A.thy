(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "RISCV64 VSpace Functions"

theory ArchVSpace_A
imports Retype_A
begin

context Arch begin arch_global_naming (A)

text \<open>
  Look up a thread's IPC buffer and check that the thread has the authority to read or (in the
  receiver case) write to it.
\<close>
definition lookup_ipc_buffer :: "bool \<Rightarrow> obj_ref \<Rightarrow> (obj_ref option,'z::state_ext) s_monad"
  where
  "lookup_ipc_buffer is_receiver thread \<equiv> do
     buffer_ptr \<leftarrow> thread_get tcb_ipc_buffer thread;
     buffer_frame_slot \<leftarrow> return (thread, tcb_cnode_index 2);
     buffer_cap \<leftarrow> get_cap buffer_frame_slot;
     case buffer_cap of
       ArchObjectCap (FrameCap p R vms False _) \<Rightarrow>
         if vm_read_write \<subseteq> R \<or> vm_read_only \<subseteq> R \<and> \<not>is_receiver
         then return $ Some $ p + (buffer_ptr && mask (pageBitsForSize vms))
         else return None
     | _ \<Rightarrow> return None
   od"

definition pool_for_asid :: "asid \<Rightarrow> 'z::state_ext state \<Rightarrow> obj_ref option"
  where
  "pool_for_asid asid \<equiv> \<lambda>s. riscv_asid_table (arch_state s) (asid_high_bits_of asid)"

definition vspace_for_pool :: "obj_ref \<Rightarrow> asid \<Rightarrow> (obj_ref \<rightharpoonup> asid_pool) \<Rightarrow> obj_ref option"
  where
  "vspace_for_pool pool_ptr asid \<equiv> do {
     pool \<leftarrow> oapply pool_ptr;
     K $ pool (asid_low_bits_of asid)
   }"

definition vspace_for_asid :: "asid \<Rightarrow> 'z::state_ext state \<Rightarrow> obj_ref option"
  where
  "vspace_for_asid asid = do {
     oassert (0 < asid);
     pool_ptr \<leftarrow> pool_for_asid asid;
     vspace_for_pool pool_ptr asid \<circ> asid_pools_of
   }"

text \<open>Locate the top-level page table associated with a given virtual ASID.\<close>
definition find_vspace_for_asid :: "asid \<Rightarrow> (obj_ref,'z::state_ext) lf_monad"
  where
  "find_vspace_for_asid asid \<equiv> doE
    vspace_opt \<leftarrow> liftE $ gets $ vspace_for_asid asid;
    throw_opt InvalidRoot vspace_opt
  odE"

text \<open>
  Format a VM fault message to be passed to a thread's supervisor after it encounters a page fault.
\<close>
definition handle_vm_fault :: "obj_ref \<Rightarrow> vmfault_type \<Rightarrow> (unit,'z::state_ext) f_monad"
  where
  "handle_vm_fault thread fault_type = doE
    addr \<leftarrow> liftE $ do_machine_op read_stval;
    let
      loadf = (\<lambda>a. throwError $ ArchFault $ VMFault a [0, vmFaultTypeFSR RISCVLoadAccessFault]);
      storef = (\<lambda>a. throwError $ ArchFault $ VMFault a [0, vmFaultTypeFSR RISCVStoreAccessFault]);
      instrf = (\<lambda>a. throwError $ ArchFault $ VMFault a [1, vmFaultTypeFSR RISCVInstructionAccessFault])
    in
      case fault_type of
        RISCVLoadPageFault \<Rightarrow> loadf addr
      | RISCVLoadAccessFault \<Rightarrow> loadf addr
      | RISCVStorePageFault \<Rightarrow> storef addr
      | RISCVStoreAccessFault \<Rightarrow> storef addr
      | RISCVInstructionPageFault \<Rightarrow> instrf addr
      | RISCVInstructionAccessFault \<Rightarrow> instrf addr
  odE"

text \<open>
  Switch into the address space of a given thread or the global address space if none is correctly
  configured.
\<close>
definition set_vm_root :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
  where
  "set_vm_root tcb \<equiv> do
    thread_root_slot \<leftarrow> return (tcb, tcb_cnode_index 1);
    thread_root \<leftarrow> get_cap thread_root_slot;
    (case thread_root of
       ArchObjectCap (PageTableCap pt (Some (asid, _))) \<Rightarrow> doE
           pt' \<leftarrow> find_vspace_for_asid asid;
           whenE (pt \<noteq> pt') $ throwError InvalidRoot;
           liftE $ do_machine_op $ setVSpaceRoot (addrFromPPtr pt) (ucast asid)
       odE
     | _ \<Rightarrow> throwError InvalidRoot) <catch>
    (\<lambda>_. do
       global_pt \<leftarrow> gets global_pt;
       do_machine_op $ setVSpaceRoot (addrFromKPPtr global_pt) 0
    od)
  od"


definition delete_asid_pool :: "asid \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
  where
  "delete_asid_pool base ptr \<equiv> do
     assert (asid_low_bits_of base = 0);
     asid_table \<leftarrow> gets (riscv_asid_table \<circ> arch_state);
     when (asid_table (asid_high_bits_of base) = Some ptr) $ do
       pool \<leftarrow> get_asid_pool ptr;
       asid_table' \<leftarrow> return $ asid_table (asid_high_bits_of base:= None);
       modify (\<lambda>s. s \<lparr> arch_state := (arch_state s) \<lparr> riscv_asid_table := asid_table' \<rparr>\<rparr>);
       tcb \<leftarrow> gets cur_thread;
       set_vm_root tcb
     od
   od"


definition delete_asid :: "asid \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
  where
  "delete_asid asid pt \<equiv> do
     asid_table \<leftarrow> gets (riscv_asid_table \<circ> arch_state);
     case asid_table (asid_high_bits_of asid) of
       None \<Rightarrow> return ()
     | Some pool_ptr \<Rightarrow> do
         pool \<leftarrow> get_asid_pool pool_ptr;
         when (pool (asid_low_bits_of asid) = Some pt) $ do
           do_machine_op $ hwASIDFlush (ucast asid);
           pool' \<leftarrow> return $ pool (asid_low_bits_of asid := None);
           set_asid_pool pool_ptr pool';
           tcb \<leftarrow> gets cur_thread;
           set_vm_root tcb
         od
       od
   od"

definition unmap_page_table :: "asid \<Rightarrow> vspace_ref \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
  where
  "unmap_page_table asid vaddr pt \<equiv> doE
     top_level_pt \<leftarrow> find_vspace_for_asid asid;
     pt_slot \<leftarrow> pt_lookup_from_level max_pt_level top_level_pt vaddr pt;
     liftE $ store_pte pt_slot InvalidPTE;
     liftE $ do_machine_op sfence
   odE <catch> (K $ return ())"

text \<open>
  Look up an @{text "asid+vspace_ref"} down to the provided level in the page table.
  For level @{term bot_level}, return a pointer to a table at the returned level.
  The level can be higher than @{term bot_level} if the lookup terminates early because
  it hit a page or an invalid entry.
\<close>
definition vs_lookup_table :: "vm_level \<Rightarrow> asid \<Rightarrow> vspace_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> (vm_level \<times> obj_ref) option"
  where
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
  inside it, since there are no slot functions for ASID pools).
\<close>
definition vs_lookup_slot :: "vm_level \<Rightarrow> asid \<Rightarrow> vspace_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> (vm_level \<times> obj_ref) option"
  where
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
     pte \<leftarrow> liftE $ get_pte slot;
     unlessE (is_PagePTE pte \<and> pptr_from_pte pte = pptr) $ throwError InvalidRoot;
     liftE $ store_pte slot InvalidPTE;
     liftE $ do_machine_op sfence
   odE <catch> (K $ return ())"

text \<open>
  Page table structure capabilities cannot be copied until they have an ASID and location
  assigned. This is because they cannot have multiple current ASIDs and cannot be shared between
  address spaces or virtual locations.
\<close>
definition arch_derive_cap :: "arch_cap \<Rightarrow> (cap,'z::state_ext) se_monad"
  where
  "arch_derive_cap c \<equiv>
     case c of
       PageTableCap _ (Some x) \<Rightarrow> returnOk (ArchObjectCap c)
     | PageTableCap _ None \<Rightarrow> throwError IllegalOperation
     | FrameCap r R sz dev mp \<Rightarrow> returnOk $ ArchObjectCap (FrameCap r R sz dev None)
     | ASIDControlCap \<Rightarrow> returnOk (ArchObjectCap c)
     | ASIDPoolCap _ _ \<Rightarrow> returnOk (ArchObjectCap c)"

text \<open>No user-modifiable data is stored in RISCV64-specific capabilities.\<close>
definition arch_update_cap_data :: "bool \<Rightarrow> data \<Rightarrow> arch_cap \<Rightarrow> cap"
  where
  "arch_update_cap_data preserve data c \<equiv> ArchObjectCap c"


text \<open>Actions that must be taken on finalisation of RISCV64-specific capabilities.\<close>
definition arch_finalise_cap :: "arch_cap \<Rightarrow> bool \<Rightarrow> (cap \<times> cap,'z::state_ext) s_monad"
  where
  "arch_finalise_cap c x \<equiv> case (c, x) of
     (ASIDPoolCap ptr b, True) \<Rightarrow>  do
       delete_asid_pool b ptr;
       return (NullCap, NullCap)
     od
   | (PageTableCap ptr (Some (a, v)), True) \<Rightarrow> do
       doE
         vroot \<leftarrow> find_vspace_for_asid a;
         if vroot = ptr then liftE $ delete_asid a ptr else throwError InvalidRoot
       odE <catch>
       (\<lambda>_. unmap_page_table a v ptr);
       return (NullCap, NullCap)
     od
   | (FrameCap ptr _ sz _ (Some (a, v)), _) \<Rightarrow> do
       unmap_page sz a v ptr;
       return (NullCap, NullCap)
     od
   | _ \<Rightarrow> return (NullCap, NullCap)"


text \<open>
  A thread's virtual address space capability must be to a mapped page table to be valid on
  the RISCV64 architecture.
\<close>
definition is_valid_vtable_root :: "cap \<Rightarrow> bool"
  where
  "is_valid_vtable_root c \<equiv>
     case c of ArchObjectCap (PageTableCap _ (Some _)) \<Rightarrow> True | _ \<Rightarrow> False"

text \<open>Make numeric value of @{const msg_align_bits} visible.\<close>
lemmas msg_align_bits = msg_align_bits'[unfolded word_size_bits_def, simplified]

definition check_valid_ipc_buffer :: "vspace_ref \<Rightarrow> cap \<Rightarrow> (unit,'z::state_ext) se_monad"
  where
  "check_valid_ipc_buffer vptr c \<equiv>
     case c of
       ArchObjectCap (FrameCap _ _ _ False _) \<Rightarrow>
         whenE (\<not> is_aligned vptr msg_align_bits) $ throwError AlignmentError
     | _ \<Rightarrow> throwError IllegalOperation"

text \<open>A pointer is inside a user frame if its top bits point to a @{const DataPage}.\<close>
definition in_user_frame :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
  where
  "in_user_frame p s \<equiv>
     \<exists>sz. kheap s (p && ~~ mask (pageBitsForSize sz)) = Some (ArchObj (DataPage False sz))"

definition prepare_thread_delete :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
  where
  "prepare_thread_delete thread_ptr \<equiv> return ()"

end
end
