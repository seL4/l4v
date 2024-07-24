(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Higher level functions for manipulating virtual address spaces
*)

chapter "x64 VSpace Functions"

theory ArchVSpace_A
imports Retype_A
begin

context Arch begin arch_global_naming (A)
text \<open>
  These attributes are always set to @{const False} when pages are mapped.
\<close>
definition
  "attr_mask = {Global,Dirty,PTAttr Accessed,PTAttr ExecuteDisable}"

definition
  "attr_mask' = attr_mask \<union> {PAT}"

text \<open>Save the set of entries that would be inserted into a page table or
page directory to map various different sizes of frame at a given virtual
address.\<close>
primrec create_mapping_entries ::
  "paddr \<Rightarrow> vspace_ref \<Rightarrow> vmpage_size \<Rightarrow> vm_rights \<Rightarrow> frame_attrs \<Rightarrow> obj_ref \<Rightarrow>
  (vm_page_entry * obj_ref,'z::state_ext) se_monad"
where
  "create_mapping_entries base vptr X64SmallPage vm_rights attrib pd =
  doE
    p \<leftarrow> lookup_error_on_failure False $ lookup_pt_slot pd vptr;
    returnOk $ (VMPTE (SmallPagePTE base (attrib - attr_mask) vm_rights), p)
  odE"

| "create_mapping_entries base vptr X64LargePage vm_rights attrib pdpt =
  doE
    p \<leftarrow> lookup_error_on_failure False $ lookup_pd_slot pdpt vptr;
    returnOk $ (VMPDE (LargePagePDE base (attrib - attr_mask) vm_rights), p)
  odE"

| "create_mapping_entries base vptr X64HugePage vm_rights attrib pml4 =
  doE
    p \<leftarrow> lookup_error_on_failure False $ lookup_pdpt_slot pml4 vptr;
    returnOk $ (VMPDPTE (HugePagePDPTE base (attrib - attr_mask') vm_rights), p)
  odE"


text \<open>This function checks that given entries are either invalid entries (for unmapping)
or replace invalid entries (for mapping).\<close>
fun ensure_safe_mapping ::
  "(vm_page_entry * obj_ref) \<Rightarrow> (unit,'z::state_ext) se_monad"
where
"ensure_safe_mapping (VMPTE InvalidPTE, _) = returnOk ()"
|
"ensure_safe_mapping (VMPDE InvalidPDE, _) = returnOk ()"
|
"ensure_safe_mapping (VMPDPTE InvalidPDPTE, _) = returnOk ()"
|
"ensure_safe_mapping (VMPTE (SmallPagePTE _ _ _), pt_slot) = returnOk ()"
|
"ensure_safe_mapping (VMPDE (LargePagePDE _ _ _), pd_slot) =
    doE
        pde \<leftarrow> liftE $ get_pde pd_slot;
        (case pde of
              InvalidPDE \<Rightarrow> returnOk ()
            | LargePagePDE _ _ _ \<Rightarrow> returnOk ()
            | _ \<Rightarrow> throwError DeleteFirst)
    odE"
|
"ensure_safe_mapping (VMPDPTE (HugePagePDPTE _ _ _), pdpt_slot) =
    doE
        pdpt \<leftarrow> liftE $ get_pdpte pdpt_slot;
        (case pdpt of
              InvalidPDPTE \<Rightarrow> returnOk ()
            | HugePagePDPTE _ _ _ \<Rightarrow> returnOk ()
            | _ \<Rightarrow> throwError DeleteFirst)
    odE"
|
"ensure_safe_mapping (VMPDE (PageTablePDE _ _ _), _) = fail"
|
"ensure_safe_mapping (VMPDPTE (PageDirectoryPDPTE _ _ _), _) = fail"

text \<open>Look up a thread's IPC buffer and check that the thread has the right
authority to read or (in the receiver case) write to it.\<close>
definition
lookup_ipc_buffer :: "bool \<Rightarrow> obj_ref \<Rightarrow> (obj_ref option,'z::state_ext) s_monad" where
"lookup_ipc_buffer is_receiver thread \<equiv> do
    buffer_ptr \<leftarrow> thread_get tcb_ipc_buffer thread;
    buffer_frame_slot \<leftarrow> return (thread, tcb_cnode_index 4);
    buffer_cap \<leftarrow> get_cap buffer_frame_slot;
    (case buffer_cap of
      ArchObjectCap (PageCap _ p R _ vms _) \<Rightarrow>
        if vm_read_write \<subseteq> R \<or> vm_read_only \<subseteq> R \<and> \<not>is_receiver
        then return $ Some $ p + (buffer_ptr && mask (pageBitsForSize vms))
        else return None
    | _ \<Rightarrow> return None)
od"

text \<open>Locate the page directory associated with a given virtual ASID.\<close>
definition
find_vspace_for_asid :: "asid \<Rightarrow> (obj_ref,'z::state_ext) lf_monad" where
"find_vspace_for_asid asid \<equiv> doE
    assertE (asid > 0);
    asid_table \<leftarrow> liftE $ gets (x64_asid_table \<circ> arch_state);
    pool_ptr \<leftarrow> returnOk (asid_table (asid_high_bits_of asid));
    pool \<leftarrow> (case pool_ptr of
               Some ptr \<Rightarrow> liftE $ get_asid_pool ptr
             | None \<Rightarrow> throwError InvalidRoot);
    pml4 \<leftarrow> returnOk (pool (asid_low_bits_of asid));
    (case pml4 of
          Some ptr \<Rightarrow> returnOk ptr
        | None \<Rightarrow> throwError InvalidRoot)
odE"


text \<open>Locate the page directory and check that this process succeeds and
returns a pointer to a real page directory.\<close>
definition
find_vspace_for_asid_assert :: "asid \<Rightarrow> (obj_ref,'z::state_ext) s_monad" where
"find_vspace_for_asid_assert asid \<equiv> do
   pml4 \<leftarrow> find_vspace_for_asid asid <catch> K fail;
   get_pml4 pml4;
   return pml4
 od"

text \<open>Format a VM fault message to be passed to a thread's supervisor after
it encounters a page fault.\<close>
definition
handle_vm_fault :: "obj_ref \<Rightarrow> vmfault_type \<Rightarrow> (unit,'z::state_ext) f_monad"
where
"handle_vm_fault thread fault_type = doE
    addr \<leftarrow> liftE $ do_machine_op getFaultAddress;
    fault \<leftarrow> liftE $ as_user thread $ getRegister ErrorRegister;
    case fault_type of
        X64DataFault \<Rightarrow> throwError $ ArchFault $ VMFault addr [0, fault && mask 5]
      | X64InstructionFault \<Rightarrow> throwError $ ArchFault $ VMFault addr [1, fault && mask 5]
odE"

definition
  get_current_cr3 :: "(cr3, 'z::state_ext) s_monad"
where
  "get_current_cr3 \<equiv> gets (x64_current_cr3 \<circ> arch_state)"

definition
  set_current_cr3 :: "cr3 \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "set_current_cr3 c \<equiv>
     modify (\<lambda>s. s \<lparr>arch_state := (arch_state s) \<lparr>x64_current_cr3 := c\<rparr>\<rparr>)"

definition
  invalidate_page_structure_cache_asid :: "obj_ref \<Rightarrow> asid \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "invalidate_page_structure_cache_asid vspace asid \<equiv>
     do_machine_op $ invalidateLocalPageStructureCacheASID vspace (ucast asid)"

definition
  getCurrentVSpaceRoot :: "(obj_ref, 'z::state_ext) s_monad"
where
  "getCurrentVSpaceRoot \<equiv> do
      cur \<leftarrow> get_current_cr3;
      return $ cr3_base_address cur
   od"

definition
  "cr3_addr_mask \<equiv> mask pml4_shift_bits << asid_bits"

definition
  make_cr3 :: "obj_ref \<Rightarrow> asid \<Rightarrow> cr3"
where
  "make_cr3 vspace asid \<equiv> cr3 (vspace && cr3_addr_mask) asid"

definition
  set_current_vspace_root :: "obj_ref \<Rightarrow> asid \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "set_current_vspace_root vspace asid \<equiv> set_current_cr3 $ make_cr3 vspace asid"

text \<open>Switch into the address space of a given thread or the global address
space if none is correctly configured.\<close>
definition
  set_vm_root :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
"set_vm_root tcb \<equiv> do
    thread_root_slot \<leftarrow> return (tcb, tcb_cnode_index 1);
    thread_root \<leftarrow> get_cap thread_root_slot;
    (case thread_root of
       ArchObjectCap (PML4Cap pml4 (Some asid)) \<Rightarrow> doE
           pml4' \<leftarrow> find_vspace_for_asid asid;
           whenE (pml4 \<noteq> pml4') $ throwError InvalidRoot;
           cur_cr3 \<leftarrow> liftE $ get_current_cr3;
           whenE (cur_cr3 \<noteq> make_cr3 (addrFromPPtr pml4) asid) $
              liftE $ set_current_cr3 $ make_cr3 (addrFromPPtr pml4) asid
       odE
     | _ \<Rightarrow> throwError InvalidRoot) <catch>
    (\<lambda>_. do
       global_pml4 \<leftarrow> gets (x64_global_pml4 \<circ> arch_state);
       set_current_vspace_root (addrFromKPPtr global_pml4) 0
    od)
od"

text \<open>Remove virtual to physical mappings in either direction involving this
virtual ASID.\<close>
definition
hw_asid_invalidate :: "asid \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
"hw_asid_invalidate asid vspace \<equiv>
  do_machine_op $ invalidateASID vspace (ucast asid)"

definition
delete_asid_pool :: "asid \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
"delete_asid_pool base ptr \<equiv> do
  assert (asid_low_bits_of base = 0);
  asid_table \<leftarrow> gets (x64_asid_table \<circ> arch_state);
  when (asid_table (asid_high_bits_of base) = Some ptr) $ do
    pool \<leftarrow> get_asid_pool ptr;
    mapM (\<lambda>offset. (when (pool (ucast offset) \<noteq> None) $
                          hw_asid_invalidate (base + offset) (the (pool (ucast offset)))))
                    [0 .e. (1 << asid_low_bits) - 1];
    asid_table' \<leftarrow> return (asid_table (asid_high_bits_of base:= None));
    modify (\<lambda>s. s \<lparr> arch_state := (arch_state s) \<lparr> x64_asid_table := asid_table' \<rparr>\<rparr>);
    tcb \<leftarrow> gets cur_thread;
    set_vm_root tcb
  od
od"

text \<open>When deleting a page map level 4 from an ASID pool we must deactivate
it.\<close>
definition
delete_asid :: "asid \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
"delete_asid asid pml4 \<equiv> do
  asid_table \<leftarrow> gets (x64_asid_table \<circ> arch_state);
  case asid_table (asid_high_bits_of asid) of
    None \<Rightarrow> return ()
  | Some pool_ptr \<Rightarrow>  do
     pool \<leftarrow> get_asid_pool pool_ptr;
     when (pool (asid_low_bits_of asid) = Some pml4) $ do
                hw_asid_invalidate asid pml4;
                pool' \<leftarrow> return (pool (asid_low_bits_of asid := None));
                set_asid_pool pool_ptr pool';
                tcb \<leftarrow> gets cur_thread;
                set_vm_root tcb
            od
    od
od"

definition
  flush_all :: "obj_ref \<Rightarrow> asid \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "flush_all vspace asid \<equiv> do_machine_op $ invalidateASID vspace (ucast asid)"

abbreviation
  flush_pdpt :: "obj_ref \<Rightarrow> asid \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "flush_pdpt \<equiv> flush_all"

abbreviation
  flush_pd :: "obj_ref \<Rightarrow> asid \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "flush_pd \<equiv> flush_all"

text \<open>Flush mappings associated with a page table.\<close>
definition
flush_table :: "obj_ref \<Rightarrow> vspace_ref \<Rightarrow> obj_ref \<Rightarrow> asid \<Rightarrow> (unit,'z::state_ext) s_monad" where
"flush_table pml4_ref vptr pt_ref asid \<equiv> do
    assert (vptr && mask (ptTranslationBits + pageBits) = 0);
           pt \<leftarrow> get_pt pt_ref;
           forM_x [0 .e. (-1::9 word)] (\<lambda>index. do
             pte \<leftarrow> return $ pt index;
             case pte of
               InvalidPTE \<Rightarrow> return ()
             | _ \<Rightarrow> do_machine_op $ invalidateTranslationSingleASID (vptr + (ucast index << pageBits)) (ucast asid)
           od)
od"


text \<open>Unmap a Page Directory Pointer Table from a PML4.\<close>
definition
unmap_pdpt :: "asid \<Rightarrow> vspace_ref \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
"unmap_pdpt asid vaddr pdpt \<equiv> doE
  vspace \<leftarrow> find_vspace_for_asid asid;
  pm_slot \<leftarrow> returnOk $ lookup_pml4_slot vspace vaddr;
  pml4e \<leftarrow> liftE $ get_pml4e pm_slot;
  case pml4e of
    PDPointerTablePML4E pt' _ _ \<Rightarrow>
      if pt' = addrFromPPtr pdpt then returnOk () else throwError InvalidRoot
    | _ \<Rightarrow> throwError InvalidRoot;
  liftE $ do
    flush_pdpt vspace asid;
    store_pml4e pm_slot InvalidPML4E
  od
odE <catch> (K $ return ())"

text \<open>Unmap a Page Directory from a Page Directory Pointer Table.\<close>
definition
unmap_pd :: "asid \<Rightarrow> vspace_ref \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
"unmap_pd asid vaddr pd \<equiv> doE
  vspace \<leftarrow> find_vspace_for_asid asid;
  pdpt_slot \<leftarrow> lookup_pdpt_slot vspace vaddr;
  pdpte \<leftarrow> liftE $ get_pdpte pdpt_slot;
  case pdpte of
    PageDirectoryPDPTE pd' _ _ \<Rightarrow>
      if pd' = addrFromPPtr pd then returnOk () else throwError InvalidRoot
    | _ \<Rightarrow> throwError InvalidRoot;
  liftE $ do
    flush_pd vspace asid;
    store_pdpte pdpt_slot InvalidPDPTE;
    invalidate_page_structure_cache_asid (addrFromPPtr vspace) asid
  od
odE <catch> (K $ return ())"

text \<open>Unmap a page table from its page directory.\<close>
definition
unmap_page_table :: "asid \<Rightarrow> vspace_ref \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
"unmap_page_table asid vaddr pt \<equiv> doE
    vspace \<leftarrow> find_vspace_for_asid asid;
    pd_slot \<leftarrow> lookup_pd_slot vspace vaddr;
    pde \<leftarrow> liftE $ get_pde pd_slot;
    case pde of
      PageTablePDE addr _ _ \<Rightarrow>
        if addrFromPPtr pt = addr then returnOk () else throwError InvalidRoot
      | _ \<Rightarrow> throwError InvalidRoot;
    liftE $ do
      flush_table vspace vaddr pt asid;
      store_pde pd_slot InvalidPDE;
      invalidate_page_structure_cache_asid (addrFromPPtr vspace) asid
    od
odE <catch> (K $ return ())"

text \<open>Check that a given frame is mapped by a given mapping entry.\<close>
definition
check_mapping_pptr :: "machine_word \<Rightarrow> vm_page_entry \<Rightarrow> bool" where
"check_mapping_pptr pptr entry \<equiv> case entry of
   VMPTE (SmallPagePTE base _ _) \<Rightarrow> base = addrFromPPtr pptr
 | VMPDE (LargePagePDE base _ _) \<Rightarrow> base = addrFromPPtr pptr
 | VMPDPTE (HugePagePDPTE base _ _) \<Rightarrow> base = addrFromPPtr pptr
 | _ \<Rightarrow> False"


text \<open>Unmap a mapped page if the given mapping details are still current.\<close>
definition
unmap_page :: "vmpage_size \<Rightarrow> asid \<Rightarrow> vspace_ref \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
"unmap_page pgsz asid vptr pptr \<equiv> doE
    vspace \<leftarrow> find_vspace_for_asid asid;
    case pgsz of
          X64SmallPage \<Rightarrow> doE
            pt_slot \<leftarrow> lookup_pt_slot vspace vptr;
            pte \<leftarrow> liftE $ get_pte pt_slot;
            unlessE (check_mapping_pptr pptr (VMPTE pte)) $ throwError InvalidRoot;
            liftE $ store_pte pt_slot InvalidPTE
          odE
        | X64LargePage \<Rightarrow> doE
            pd_slot \<leftarrow> lookup_pd_slot vspace vptr;
            pde \<leftarrow> liftE $ get_pde pd_slot;
            unlessE (check_mapping_pptr pptr (VMPDE pde)) $ throwError InvalidRoot;
            liftE $ store_pde pd_slot InvalidPDE
          odE
        | X64HugePage \<Rightarrow> doE
            pdpt_slot \<leftarrow> lookup_pdpt_slot vspace vptr;
            pdpte \<leftarrow> liftE $ get_pdpte pdpt_slot;
            unlessE (check_mapping_pptr pptr (VMPDPTE pdpte)) $ throwError InvalidRoot;
            liftE $ store_pdpte pdpt_slot InvalidPDPTE
          odE;
    liftE $ do_machine_op $ invalidateTranslationSingleASID vptr (ucast asid)
odE <catch> (K $ return ())"


text \<open>Page table structure capabilities cannot be copied until they
have a virtual ASID and location assigned. This is because they
cannot have multiple current virtual ASIDs and cannot be shared
between address spaces or virtual locations.\<close>
definition
  arch_derive_cap :: "arch_cap \<Rightarrow> (cap,'z::state_ext) se_monad"
where
  "arch_derive_cap c \<equiv> case c of
     PageTableCap _ (Some x) \<Rightarrow> returnOk (ArchObjectCap c)
   | PageTableCap _ None \<Rightarrow> throwError IllegalOperation
   | PageDirectoryCap _ (Some x) \<Rightarrow> returnOk (ArchObjectCap c)
   | PageDirectoryCap _ None \<Rightarrow> throwError IllegalOperation
   | PDPointerTableCap _ (Some x) \<Rightarrow> returnOk (ArchObjectCap c)
   | PDPointerTableCap _ None \<Rightarrow> throwError IllegalOperation
   | PML4Cap _ (Some x) \<Rightarrow> returnOk (ArchObjectCap c)
   | PML4Cap _ None \<Rightarrow> throwError IllegalOperation
   | PageCap dev r R mt pgs x \<Rightarrow> returnOk $ ArchObjectCap (PageCap dev r R VMNoMap pgs None)
   | ASIDControlCap \<Rightarrow> returnOk (ArchObjectCap c)
   | ASIDPoolCap _ _ \<Rightarrow> returnOk (ArchObjectCap c)
\<^cancel>\<open>FIXME x64-vtd:
   | IOSpaceCap _ _ \<Rightarrow> returnOk c
   | IOPageTableCap _ _ _ \<Rightarrow> returnOk c\<close>
   | IOPortCap _ _ \<Rightarrow> returnOk (ArchObjectCap c)
   | IOPortControlCap \<Rightarrow> returnOk NullCap"

text \<open>No user-modifiable data is stored in x64-specific capabilities.\<close>
definition
  arch_update_cap_data :: "bool \<Rightarrow> data \<Rightarrow> arch_cap \<Rightarrow> cap"
where
  "arch_update_cap_data preserve data c \<equiv> ArchObjectCap c"


text \<open>Actions that must be taken on finalisation of x64-specific
capabilities.\<close>
definition
  arch_finalise_cap :: "arch_cap \<Rightarrow> bool \<Rightarrow> (cap \<times> cap,'z::state_ext) s_monad"
where
  "arch_finalise_cap c x \<equiv> case (c, x) of
    (ASIDPoolCap ptr b, True) \<Rightarrow>  do
    delete_asid_pool b ptr;
    return (NullCap, NullCap)
    od
  | (PML4Cap ptr (Some a), True) \<Rightarrow> do
    delete_asid a ptr;
    return (NullCap, NullCap)
  od
  | (PDPointerTableCap ptr (Some (a,v)), True) \<Rightarrow> do
    unmap_pdpt a v ptr;
    return (NullCap, NullCap)
  od
  | (PageDirectoryCap ptr (Some (a,v)), True) \<Rightarrow> do
    unmap_pd a v ptr;
    return (NullCap, NullCap)
  od
  | (PageTableCap ptr (Some (a, v)), True) \<Rightarrow> do
    unmap_page_table a v ptr;
    return (NullCap, NullCap)
  od
  | (PageCap _ ptr _ _ s (Some (a, v)), _) \<Rightarrow> do
     unmap_page s a v ptr;
     return (NullCap, NullCap)
  od
  | (IOPortCap f l, True) \<Rightarrow> return (NullCap, (ArchObjectCap (IOPortCap f l)))
  \<comment> \<open>FIXME x64-vtd: IOSpaceCap and IOPageTableCap for @{text arch_finalise_cap}\<close>
  | _ \<Rightarrow> return (NullCap, NullCap)"



text \<open>A thread's virtual address space capability must be to a mapped PML4 (page map level 4)
to be valid on the x64 architecture.\<close>
definition
  is_valid_vtable_root :: "cap \<Rightarrow> bool" where
  "is_valid_vtable_root c \<equiv> \<exists>r a. c = ArchObjectCap (PML4Cap r (Some a))"

definition
check_valid_ipc_buffer :: "vspace_ref \<Rightarrow> cap \<Rightarrow> (unit,'z::state_ext) se_monad" where
"check_valid_ipc_buffer vptr c \<equiv> case c of
  (ArchObjectCap (PageCap False _ _ _ _ _)) \<Rightarrow> doE
    whenE (\<not> is_aligned vptr msg_align_bits) $ throwError AlignmentError;
    returnOk ()
  odE
| _ \<Rightarrow> throwError IllegalOperation"

text \<open>Decode a user argument word describing the kind of VM attributes a
mapping is to have.\<close>
definition
attribs_from_word :: "machine_word \<Rightarrow> frame_attrs" where
"attribs_from_word w \<equiv>
  let V = (if w !!0 then {PTAttr WriteThrough} else {});
      V' = (if w!!1 then insert (PTAttr CacheDisabled) V else V)
  in if w!!2 then insert PAT V' else V'"


text \<open>Update the mapping data saved in a page or page table capability.\<close>
definition
  update_map_data :: "arch_cap \<Rightarrow> (asid \<times> vspace_ref) option \<Rightarrow> vmmap_type option \<Rightarrow> arch_cap" where
  "update_map_data cap m mt \<equiv> case cap of
     PageCap dev p R _ sz _ \<Rightarrow> PageCap dev p R (the mt) sz m
   | PageTableCap p _ \<Rightarrow> PageTableCap p m
   | PageDirectoryCap p _ \<Rightarrow> PageDirectoryCap p m
   | PDPointerTableCap p _ \<Rightarrow> PDPointerTableCap p m"

text \<open>
  A pointer is inside a user frame if its top bits point to a @{text DataPage}.
\<close>
definition
  in_user_frame :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
  "in_user_frame p s \<equiv>
   \<exists>sz. kheap s (p && ~~ mask (pageBitsForSize sz)) =
        Some (ArchObj (DataPage False sz))"

definition
  fpu_thread_delete :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "fpu_thread_delete thread_ptr \<equiv> do
    using_fpu \<leftarrow> do_machine_op (nativeThreadUsingFPU thread_ptr);
    when using_fpu $ do_machine_op (switchFpuOwner 0 0)
  od"

definition
  prepare_thread_delete :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "prepare_thread_delete thread_ptr \<equiv> fpu_thread_delete thread_ptr"

text \<open>Make numeric value of @{const msg_align_bits} visible.\<close>
lemmas msg_align_bits = msg_align_bits'[unfolded word_size_bits_def, simplified]

end
end
