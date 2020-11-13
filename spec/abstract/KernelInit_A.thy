(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory KernelInit_A (* FIXME: unused, out of date *)
imports
  Tcb_A
  ArchVSpace_A
begin

section \<open>Generic stuff\<close>

translations
  (type) "cslot_ptr" <= (type) "word32 \<times> bool list"

type_synonym slot_ptr = "cslot_ptr"
type_synonym slot_region_t = "nat \<times> nat"
type_synonym bi_dev_reg_t = "paddr \<times> word32 \<times> slot_region_t"

text \<open>Select from state S, throw ex if S is empty.\<close>
definition
  "throw_select S ex \<equiv> doE
     whenE (S = {}) (throwError ex);
     liftE (select S)
   odE"


section \<open>Parameters passed in from linker script\<close>

consts
  ki_boot_end :: paddr
  arm_vector_table :: obj_ref
  arm_kernel_stack :: obj_ref
  idle_thread_start :: vspace_ref (* &idle_thread *)

section \<open>Kernel Init State\<close>

text \<open>Ghost state representing the contents of the boot info frame\<close>
record bi_frame_data =
  bi_f_node_id :: word32
  bi_f_num_nodes :: word32
  bi_f_num_iopt_levels :: word32
  bi_f_ipcbuf_vptr :: vspace_ref
  bi_f_null_caps :: slot_region_t
  bi_f_sh_frame_caps :: slot_region_t
  bi_f_ui_frame_caps :: slot_region_t
  bi_f_ui_pt_caps :: slot_region_t
  bi_f_ut_obj_caps :: slot_region_t
  bi_f_ut_obj_paddr_list :: "paddr list"
  bi_f_ut_obj_size_bits_list :: "word8 list"
  bi_f_it_cnode_size_bits :: word8
  bi_f_num_dev_regs :: word32
  bi_f_dev_reg_list :: "bi_dev_reg_t list"

type_synonym (* XXX: natural numbers represent components of kernel objects, for those
              objects that can be subdivided *)
  component = "bool list"

text \<open>
  For kernel initialisation, we need the basic kernel state plus some extra
  information to keep track of, such as free memory.
  At the concrete level, this is managed by region lists.

  The ``available memory'' indicates memory that has been allocated (and thus
  no longer free) but that has no objects in it, as it has not been retyped.
  This is so we can state heap-consuming separation logic predicates which
  assert that ``there's nothing here'', e.g. so-called untyped objects.

  The components map should have the same domain as the abstract heap in the
  kernel state, but indicate which components of the object we have permission
  to access. The purpose is separation logic statements about heaps in which
  objects can be split up, e.g. only one cap in a CNode.
\<close>
record ('z) ki_state =
  ki_kernel_state    :: "'z state"
  ki_free_mem        :: "obj_ref set" (* ndks_boot.freemem representative? *)
  ki_available_mem   :: "obj_ref set" (* ghost state *)
  ki_bootinfo        :: bi_frame_data (* ghost state *)
  ki_components      :: "paddr \<Rightarrow> component set"
  ndks_boot_slot_pos_cur :: nat
  ndks_boot_slot_pos_max :: nat
  ndks_boot_bi_frame :: paddr


section \<open>Kernel init monad\<close>

text \<open>
  The kernel init monad can fail. The actual value of the failure is largely
  irrelevant, just so long as we don't have assertion failures for no reason.
\<close>

datatype ki_failure = InitFailure
type_synonym ('a,'z) ki_monad = "('z ki_state, ki_failure + 'a) nondet_monad"
translations
  (type) "'a ki_monad" <=
    (type) "((ki_failure + 'a) \<times> ki_state \<Rightarrow> bool) \<times> bool"

text \<open>Lift kernel state monad ops to the kernel init monad.\<close>
definition
  do_kernel_op :: "('a,'z::state_ext) s_monad \<Rightarrow> ('a,'z) ki_monad" where
 "do_kernel_op kop \<equiv> liftE $ do
    ms \<leftarrow> gets ki_kernel_state;
    (r, ms') \<leftarrow> select_f (kop ms);
    modify (\<lambda>ks. ks \<lparr> ki_kernel_state := ms' \<rparr>);
    return r
  od"


section \<open>Kernel constants\<close>

definition "MIN_NUM_4K_UNTYPED_OBJ \<equiv> 12 :: nat"
definition "MAX_NUM_FREEMEM_REG \<equiv> 2 :: nat"

text \<open>Fixed cap positions in root CNode (bootinfo.h)\<close>
definition "BI_CAP_NULL         \<equiv>  0 :: nat"
definition "BI_CAP_IT_TCB       \<equiv>  1 :: nat"
definition "BI_CAP_IT_CNODE     \<equiv>  2 :: nat"
definition "BI_CAP_IT_PD        \<equiv>  3 :: nat"
definition "BI_CAP_IRQ_CTRL     \<equiv>  4 :: nat"
definition "BI_CAP_ASID_CTRL    \<equiv>  5 :: nat"
definition "BI_CAP_IT_ASID_POOL \<equiv>  6 :: nat"
definition "BI_CAP_IO_PORT      \<equiv>  7 :: nat"
definition "BI_CAP_IO_SPACE     \<equiv>  8 :: nat"
definition "BI_CAP_BI_FRAME     \<equiv>  9 :: nat"
definition "BI_CAP_IT_IPCBUF    \<equiv> 10 :: nat"
definition "BI_CAP_DYN_START    \<equiv> 11 :: nat"

definition "BI_FRAME_SIZE_BITS \<equiv> pageBits"
definition "ROOT_CNODE_SIZE_BITS \<equiv> 12 :: nat"


section \<open>ARM constants\<close>

definition "PPTR_VECTOR_TABLE \<equiv> 0xffff0000 :: word32"
definition "PPTR_GLOBALS_PAGE \<equiv> 0xffffc000 :: word32"
definition "PPTR_KERNEL_STACK \<equiv> 0xfffff000 :: word32"

definition "IT_ASID     \<equiv> 1 :: asid" (* initial thread ASID *)

definition "WORD_SIZE_BITS \<equiv> 2 :: nat"
definition "ASID_POOL_BITS \<equiv> asid_low_bits :: nat"
definition "ASID_POOL_SIZE_BITS \<equiv> ASID_POOL_BITS + WORD_SIZE_BITS"

definition "CTE_SIZE_BITS \<equiv> 4 :: nat" (* from ARM structures.h *)

text \<open>in abstract, these do not have a direct equivalent\<close>
definition "PD_BITS \<equiv> 12 :: nat"
definition "PT_BITS \<equiv> 8 :: nat"

definition "PDE_SIZE_BITS \<equiv> 2 :: nat"
definition "PTE_SIZE_BITS \<equiv> 2 :: nat"

text \<open>in abstract, these are pd_bits and pt_bits respectively\<close>
definition "PD_SIZE_BITS \<equiv> PD_BITS + PDE_SIZE_BITS"
definition "PT_SIZE_BITS \<equiv> PT_BITS + PTE_SIZE_BITS"


section \<open>Platform constants (iMX31)\<close>

definition "irqInvalid       \<equiv> 255 :: irq"
definition "INTERRUPT_PMU    \<equiv> 23 :: irq"
definition "INTERRUPT_EPIT1  \<equiv> 28 :: irq"
definition "KERNEL_TIMER_IRQ \<equiv> INTERRUPT_EPIT1"

text \<open>Kernel devices for imx31\<close>
definition "EPIT_PADDR \<equiv> 0x53f94000 :: word32"
definition "EPIT_PPTR  \<equiv> 0xfff00000 :: word32"
definition "AVIC_PADDR \<equiv> 0x68000000 :: word32"
definition "AVIC_PPTR  \<equiv> 0xfff01000 :: word32"
definition "L2CC_PADDR \<equiv> 0x30000000 :: word32"
definition "L2CC_PPTR  \<equiv> 0xfff02000 :: word32"
definition "UART_PADDR \<equiv> 0x43f90000 :: word32"
definition "UART_PPTR  \<equiv> 0xfff03000 :: word32"

definition "BASE_OFFSET = pptrBaseOffset"

section \<open>Functions cloned and modified for separation logic to work\<close>

text \<open>
  These shadow the normal functions, but do not force a well-formedness
  check for the cnodes, as wellformed\_cnode\_sz is non-local with respect
  to individual caps, and so get\_cap and set\_cap are also.\<close>

definition
  get_cap_local :: "cslot_ptr \<Rightarrow> (cap,'z::state_ext) s_monad"
where
  "get_cap_local \<equiv> \<lambda>(oref, cref). do
     obj \<leftarrow> get_object oref;
     caps \<leftarrow> case obj of
             CNode sz cnode \<Rightarrow> return cnode
           | TCB tcb     \<Rightarrow> return (tcb_cnode_map tcb)
           | _ \<Rightarrow> fail;
     assert_opt (caps cref)
   od"

definition
  set_cap_local :: "cap \<Rightarrow> cslot_ptr \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "set_cap_local cap \<equiv> \<lambda>(oref, cref). do
     obj \<leftarrow> get_object oref;
     obj' \<leftarrow> case obj of
               CNode sz cn \<Rightarrow> if cref \<in> dom cn
                                then return $ CNode sz $ cn (cref \<mapsto> cap)
                                else fail
             | TCB tcb \<Rightarrow>
                   if cref = tcb_cnode_index 0 then
                       return $ TCB $ tcb \<lparr> tcb_ctable := cap \<rparr>
                   else if cref = tcb_cnode_index 1 then
                       return $ TCB $ tcb \<lparr> tcb_vtable := cap \<rparr>
                   else if cref = tcb_cnode_index 2 then
                       return $ TCB $ tcb \<lparr> tcb_reply := cap \<rparr>
                   else if cref = tcb_cnode_index 3 then
                       return $ TCB $ tcb \<lparr> tcb_caller := cap \<rparr>
                   else if cref = tcb_cnode_index 4 then
                       return $ TCB $ tcb \<lparr> tcb_ipcframe := cap \<rparr>
                   else
                       fail
             | _ \<Rightarrow> fail;
     set_object oref obj'
  od"

definition
  set_untyped_cap_as_full_local :: "cap \<Rightarrow> cap \<Rightarrow> word32 \<times> bool list\<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "set_untyped_cap_as_full_local src_cap new_cap src_slot \<equiv>
   if (is_untyped_cap src_cap \<and> is_untyped_cap new_cap
       \<and> obj_ref_of src_cap = obj_ref_of new_cap \<and> cap_bits_untyped src_cap = cap_bits_untyped new_cap)
       then set_cap_local (max_free_index_update src_cap) src_slot else return ()"

definition
  cap_insert_local :: "cap \<Rightarrow> cslot_ptr \<Rightarrow> cslot_ptr \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "cap_insert_local new_cap src_slot dest_slot \<equiv> do
    src_cap \<leftarrow> get_cap_local src_slot;

    dest_original \<leftarrow> return (if is_ep_cap new_cap then
                                cap_ep_badge new_cap \<noteq> cap_ep_badge src_cap
                             else if is_ntfn_cap new_cap then
                                cap_ep_badge new_cap \<noteq> cap_ep_badge src_cap
                             else if \<exists>irq. new_cap = IRQHandlerCap irq then
                                src_cap = IRQControlCap
                             else is_untyped_cap new_cap);
    old_cap \<leftarrow> get_cap_local dest_slot;
    assert (old_cap = NullCap);
    set_untyped_cap_as_full_local src_cap new_cap src_slot;
    set_cap_local new_cap dest_slot;

    is_original \<leftarrow> gets is_original_cap;
    src_parent \<leftarrow> return $
       should_be_parent_of src_cap (is_original src_slot) new_cap dest_original;
    src_p \<leftarrow> gets (\<lambda>s. cdt s src_slot);
    dest_p \<leftarrow> gets (\<lambda>s. cdt s dest_slot);
    update_cdt (\<lambda>cdt. cdt (dest_slot := if src_parent
                                        then Some src_slot
                                        else cdt src_slot));
    do_extended_op (cap_insert_ext src_parent src_slot dest_slot src_p dest_p);
    set_original dest_slot dest_original
  od"

definition
  "setup_reply_master_local thread \<equiv> do
     old_cap <- get_cap_local (thread, tcb_cnode_index 2);
     when (old_cap = NullCap) $ do
         set_original (thread, tcb_cnode_index 2) True;
         set_cap_local (ReplyCap thread True) (thread, tcb_cnode_index 2)
     od
  od"




section \<open>Kernel init functions\<close>

consts (* TODO: serialise bi_frame_data and write it to the bootinfo frame *)
  sync_bootinfo_frame :: "paddr \<Rightarrow> (unit,'z::state_ext) ki_monad"

definition (* C macro ROUND_DOWN *)
   "round_down w b \<equiv> (w >> b) << b"

definition
  alloc_region :: "nat \<Rightarrow> (obj_ref,'z) ki_monad" where
 "alloc_region bits \<equiv> doE
    free  \<leftarrow> liftE $ gets ki_free_mem;
    ptr   \<leftarrow> throw_select
              {ptr. is_aligned ptr bits \<and> {ptr .. ptr + 2 ^ bits - 1} \<subseteq> free}
              InitFailure;
    liftE $ modify (\<lambda>s. s \<lparr> ki_free_mem :=
                              free - {ptr .. ptr + 2 ^ bits - 1} \<rparr>);

    (* Ghost state update: mark memory as available *)
    avail \<leftarrow> liftE $ gets ki_available_mem;
    liftE $ modify (\<lambda>s. s \<lparr> ki_available_mem :=
                              avail \<union> {ptr .. ptr + 2 ^ bits - 1} \<rparr>);

    returnOk ptr
  odE"

definition
  init_freemem :: "(paddr \<times> paddr) \<Rightarrow> (unit,'z::state_ext) ki_monad" where
  "init_freemem ui_reg \<equiv> doE

     mem_regs \<leftarrow> do_kernel_op $ do_machine_op getMemoryRegions;

     free_addrs \<leftarrow> returnOk $ foldl (\<union>) {}
                             $ map (\<lambda>(start,end). {start..<end}) mem_regs;

     (* subtract userland image addresses from the set of free addresses *)
     free_addrs' \<leftarrow> returnOk $ free_addrs - {fst ui_reg..<(snd ui_reg)};

     (* now pick a subset of those vars, because the C has a limit on the
        number of slots in ndks_boot.freemem[] (MAX_NUM_FREEMEM_REG) which
        isn't represented in the abstract spec *)
     free_addrs_sel \<leftarrow> liftE $ select {s. s \<subseteq> free_addrs'};

     liftE $ modify (\<lambda>s. s \<lparr> ki_free_mem := free_addrs_sel \<rparr>)
   odE"

text \<open>
  The @{text "arm_global_pts"} arch state field means something completely
  different to the armKSGlobalPT in the C code. As such, the abstract spec as
  it stands now must have a list of pts there. Since the kernel init abstract
  spec is based on the actual C, we know there is only one such pt. To prevent
  confusion, this function is meant as the canonical way to get the
  armKSGlobalPT equivalent, whatever it ends up being.

  This means that kernel init assumes the initial state will provide a PT
  there that it can use.\<close>
definition
  get_arm_global_pt :: "(paddr,'z::state_ext) s_monad" where
  "get_arm_global_pt \<equiv> do
     pt \<leftarrow> gets (hd \<circ> arm_global_pts \<circ> arch_state);
     return pt
   od"

definition
  write_slot :: "slot_ptr \<Rightarrow> cap \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "write_slot slot_ptr cap \<equiv> do
     set_cap_local cap slot_ptr;
     set_original slot_ptr True
   od"

definition
  cap_slot_pptr :: "cap \<Rightarrow> nat \<Rightarrow> cslot_ptr" where
  "cap_slot_pptr cap position \<equiv>
     (obj_ref_of cap, nat_to_cref (bits_of cap) position)"
  (* corresponds to C code: SLOT_PTR(pptr_of_cap(cap), position) for cnodes
     but NOT TCBs, for that use something like tcb_cnode_index *)

definition
  provide_cap :: "cap \<Rightarrow> cap \<Rightarrow> (unit,'z::state_ext) ki_monad" where
  "provide_cap root_cnode_cap cap \<equiv> doE
     slot_pos_cur \<leftarrow> liftE $ gets ndks_boot_slot_pos_cur;
     slot_pos_max \<leftarrow> liftE $ gets ndks_boot_slot_pos_max;

     (* Ran out of free slots in root CNode? *)
     whenE (slot_pos_cur \<ge> slot_pos_max) $ throwError InitFailure;

     do_kernel_op $ write_slot (cap_slot_pptr root_cnode_cap slot_pos_cur) cap;

     liftE $ modify (\<lambda>s. s \<lparr> ndks_boot_slot_pos_cur := slot_pos_cur + 1 \<rparr>)
   odE"

definition
  provide_untyped_cap :: "cap \<Rightarrow> paddr \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (unit,'z::state_ext) ki_monad" where
  "provide_untyped_cap root_cnode_cap pptr size_bits slot_pos_before \<equiv> doE

     slot_pos_cur \<leftarrow> liftE $ gets ndks_boot_slot_pos_cur;
     i \<leftarrow> returnOk $ slot_pos_cur - slot_pos_before;

     (* the C code writes to index i, but we append, so crosscheck that...
        this might prove to be overkill, but it's better to remove it during
        corres proof or such *)
     ut_objs \<leftarrow> liftE $ gets (bi_f_ut_obj_paddr_list \<circ> ki_bootinfo);
     assertE (length ut_objs = i);
     ut_objs \<leftarrow> liftE $ gets (bi_f_ut_obj_size_bits_list \<circ> ki_bootinfo);
     assertE (length ut_objs = i);

     (* update ghost bootinfo frame and sync *)
     liftE $ modify (\<lambda>s. s \<lparr> ki_bootinfo := (ki_bootinfo s) \<lparr>
       bi_f_ut_obj_paddr_list :=
         (bi_f_ut_obj_paddr_list $ ki_bootinfo s) @ [pptr],
       bi_f_ut_obj_size_bits_list :=
         (bi_f_ut_obj_size_bits_list $ ki_bootinfo s) @ [of_nat size_bits]
       \<rparr>\<rparr>);
     bi_frame \<leftarrow> liftE $ gets ndks_boot_bi_frame;
     sync_bootinfo_frame bi_frame;

     provide_cap root_cnode_cap $ UntypedCap pptr size_bits 0
   odE"

definition
  init_cpu :: "(unit,'z::state_ext) s_monad" where
  "init_cpu = do
     do_machine_op cleanCache;
     global_pd \<leftarrow> gets (arm_global_pd \<circ> arch_state);
     do_machine_op $ setCurrentPD $ addrFromPPtr global_pd
   od"

definition
  init_plat :: "(unit,'z::state_ext) s_monad" where
  "init_plat \<equiv> do
     do_machine_op initTimer;
     do_machine_op initL2Cache
   od"

definition
  init_irqs :: "cap \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "init_irqs root_cnode_cap \<equiv> do

     mapM (set_irq_state IRQInactive) [0 .e. maxIRQ];
     set_irq_state IRQTimer KERNEL_TIMER_IRQ;

     write_slot (cap_slot_pptr root_cnode_cap BI_CAP_IRQ_CTRL) IRQControlCap
   od"

definition
  arch_configure_idle_thread :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "arch_configure_idle_thread tcb \<equiv> do
     as_user tcb $ set_register CPSR 0x1f;
     as_user tcb $ setNextPC idle_thread_start
   od"

definition
  configure_idle_thread :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "configure_idle_thread tcb \<equiv> do
     arch_configure_idle_thread tcb;
     set_thread_state tcb IdleThreadState
   od"

definition
  create_objects :: "nat \<Rightarrow> nat \<Rightarrow> apiobject_type \<Rightarrow> (paddr,'z::state_ext) ki_monad"
  where
  "create_objects bits ko_bits ko_typ \<equiv> doE
      pptr \<leftarrow> alloc_region bits;
      do_kernel_op $ retype_region pptr (bits div ko_bits) ko_bits ko_typ;

      (* previously available memory now contains object: update ghost state *)
      avail \<leftarrow> liftE $ gets ki_available_mem;
      liftE $ modify (\<lambda>s. s \<lparr> ki_available_mem :=
                                avail - {pptr .. pptr + 2 ^ bits - 1} \<rparr>);
      (* FIXME: update ki_components ghost state !!! *)
      returnOk pptr
   odE"

definition
  create_idle_thread :: "(unit,'z::state_ext) ki_monad" where
  "create_idle_thread \<equiv> doE
     pptr \<leftarrow> create_objects (obj_bits $ TCB undefined)
                           (obj_bits $ TCB undefined) TCBObject;
     do_kernel_op $ do
       modify (\<lambda>s. s \<lparr> idle_thread := pptr \<rparr>);
       configure_idle_thread pptr
     od
   odE"

definition
  create_root_cnode :: "(cap,'z::state_ext) ki_monad" where
  "create_root_cnode \<equiv>
   let sz = (ROOT_CNODE_SIZE_BITS + CTE_SIZE_BITS) in
   doE
     liftE $ modify
               (\<lambda>s. s \<lparr> ndks_boot_slot_pos_max := 2 ^ ROOT_CNODE_SIZE_BITS \<rparr>);

     pptr \<leftarrow> create_objects sz sz CapTableObject;

     let cap = CNodeCap pptr ROOT_CNODE_SIZE_BITS
                             (replicate (32 - ROOT_CNODE_SIZE_BITS) False)
     in (doE
           do_kernel_op $ write_slot (cap_slot_pptr cap BI_CAP_IT_CNODE) cap;
           returnOk cap
         odE)
   odE"

definition
  create_irq_cnode :: "(unit,'z::state_ext) ki_monad" where
  "create_irq_cnode \<equiv> doE
     (* Make a page full of cnodes with one CTE each. At the C level
        this is of course just an array of CTEs taking up the whole page. *)
     pptr \<leftarrow> create_objects pageBits CTE_SIZE_BITS CapTableObject;

     (* Now associate each cnode with an irq *)
     do_kernel_op $ modify
               (\<lambda>s. s \<lparr> interrupt_irq_node :=
                        (\<lambda>irq. pptr + ucast irq * of_nat CTE_SIZE_BITS) \<rparr>)
   odE"

definition
  create_it_frame_cap :: "obj_ref \<Rightarrow> vspace_ref \<Rightarrow> asid option \<Rightarrow> bool \<Rightarrow> (cap,'z::state_ext) ki_monad"
  where
  "create_it_frame_cap pptr vptr asid use_large \<equiv>
   let sz = if use_large then ARMLargePage else ARMSmallPage in
     returnOk $ ArchObjectCap $ PageCap pptr {AllowRead,AllowWrite}
                                        sz (map_option (\<lambda>a. (a, vptr)) asid)"

definition
  create_ipcbuf_frame :: "cap \<Rightarrow> (vspace_ref \<times> vspace_ref)
                          \<Rightarrow> (cap \<times> vspace_ref,'z::state_ext) ki_monad" where
  "create_ipcbuf_frame root_cnode_cap ui_v_reg \<equiv>
   let vptr = snd ui_v_reg (* ui_v_reg.end *)
   in
   doE
     pptr \<leftarrow> alloc_region pageBits;
     do_kernel_op $ do_machine_op $ clearMemory pptr pageBits;

     cap \<leftarrow> create_it_frame_cap pptr vptr (Some IT_ASID) False;

     do_kernel_op $
       write_slot (cap_slot_pptr root_cnode_cap BI_CAP_IT_IPCBUF) cap;

     returnOk (cap, vptr)
   odE"

definition
  create_bi_frame :: "cap \<Rightarrow> (vspace_ref \<times> vspace_ref) \<Rightarrow> vspace_ref \<Rightarrow> word32
                      \<Rightarrow> word32 \<Rightarrow> (vspace_ref,'z::state_ext) ki_monad" where
  "create_bi_frame root_cnode_cap ui_v_reg ipcbuf_vptr node_id num_nodes \<equiv>
   let vptr = ipcbuf_vptr + of_nat (2 ^ pageBits)
   in
   doE
     pptr \<leftarrow> alloc_region BI_FRAME_SIZE_BITS;

     (* update in abstract representation of boot info frame *)
     liftE $ modify (\<lambda>s. s \<lparr> ki_bootinfo := (ki_bootinfo s) \<lparr>
       bi_f_node_id := node_id,
       bi_f_num_nodes := num_nodes,
       bi_f_num_iopt_levels := 0,
       bi_f_ipcbuf_vptr := ipcbuf_vptr,
       bi_f_it_cnode_size_bits := of_nat ROOT_CNODE_SIZE_BITS \<rparr>\<rparr>);

     (* synchronise abstract bootinfo with boot info frame *)
     sync_bootinfo_frame pptr;

     liftE $ modify (\<lambda>s. s \<lparr> ndks_boot_bi_frame := pptr,
                             ndks_boot_slot_pos_cur := BI_CAP_DYN_START \<rparr> );

     cap \<leftarrow> create_it_frame_cap pptr vptr (Some IT_ASID) False;
     do_kernel_op $
       write_slot (cap_slot_pptr root_cnode_cap BI_CAP_BI_FRAME) cap;

     returnOk vptr
   odE"

definition
  create_it_asid_pool :: "cap \<Rightarrow> (cap,'z::state_ext) ki_monad" where
  "create_it_asid_pool root_cnode_cap \<equiv> doE

     (* create ASID pool *)
     ap_pptr \<leftarrow> create_objects ASID_POOL_SIZE_BITS
                              ASID_POOL_SIZE_BITS (ArchObject ASIDPoolObj);

     ap_cap \<leftarrow> returnOk $ ArchObjectCap $
                 ASIDPoolCap ap_pptr (IT_ASID >> asid_low_bits);

     do_kernel_op $ write_slot (cap_slot_pptr root_cnode_cap
                                BI_CAP_IT_ASID_POOL) ap_cap;

     (* create ASID control cap *)
     do_kernel_op $ write_slot (cap_slot_pptr root_cnode_cap BI_CAP_ASID_CTRL)
                               (ArchObjectCap ASIDControlCap);

     returnOk ap_cap
   odE"

definition
  create_frames_of_region :: "cap \<Rightarrow> (paddr \<times> paddr) \<Rightarrow> bool \<Rightarrow> word32
                              \<Rightarrow> (nat \<times> nat,'z::state_ext) ki_monad" where
  "create_frames_of_region root_cnode_cap reg do_map pv_offset \<equiv> doE

     slot_pos_before \<leftarrow> liftE $ gets ndks_boot_slot_pos_cur;

     (swp mapME)
       [(fst reg),(fst reg + of_nat (2 ^ pageBits)) .e. (snd reg - 1)]
       (\<lambda>f. doE
              frame_cap \<leftarrow> (if do_map
                           then create_it_frame_cap f
                                  (f - BASE_OFFSET - pv_offset) (Some IT_ASID) False
                           else create_it_frame_cap f 0 None False);
              provide_cap root_cnode_cap frame_cap
            odE);

     slot_pos_after \<leftarrow> liftE $ gets ndks_boot_slot_pos_cur;

     returnOk (slot_pos_before, slot_pos_after)
   odE"

definition
  write_it_asid_pool :: "cap \<Rightarrow> cap \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "write_it_asid_pool it_ap_cap it_pd_cap \<equiv>
   let ap_ptr = obj_ref_of it_ap_cap;
       pd_ptr = obj_ref_of it_pd_cap;
       asid_idx = ucast (IT_ASID >> asid_low_bits)
   in
   do
     ap \<leftarrow> get_asid_pool ap_ptr;
     ap' \<leftarrow> return (ap (ucast IT_ASID \<mapsto> pd_ptr));
     set_asid_pool ap_ptr ap';

     asid_table \<leftarrow> gets (arm_asid_table \<circ> arch_state);
     asid_table' \<leftarrow> return (asid_table(asid_idx \<mapsto> ap_ptr));
     modify (\<lambda>s. s \<lparr> arch_state :=
                      arch_state s \<lparr> arm_asid_table := asid_table' \<rparr>\<rparr>)

   od"

definition
  map_it_pt_cap :: "cap \<Rightarrow> cap \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "map_it_pt_cap pd_cap pt_cap \<equiv> do

     pd \<leftarrow> return $ obj_ref_of pd_cap; (* C uses specific PD version *)

     (pt,vptr) \<leftarrow> return $ case the_arch_cap pt_cap
                            of PageTableCap ref (Some (_, vref)) \<Rightarrow> (ref,vref);

     slot \<leftarrow> return $ vptr >> pageBitsForSize ARMSection;

     (* C code sets ParityEnable bit, which is apparently to enable ECC *)
     pde \<leftarrow> return $ PageTablePDE (addrFromPPtr pt) {ParityEnabled} 0;

     pd_obj \<leftarrow> get_object pd;
     pd_obj' \<leftarrow> return (case pd_obj
                         of ArchObj (PageDirectory table)
                            \<Rightarrow> ArchObj (PageDirectory $ table(ucast slot := pde)
                       ));
     set_object pd pd_obj'
   od"

definition
  map_it_frame_cap :: "cap \<Rightarrow> cap \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "map_it_frame_cap pd_cap frame_cap \<equiv> do

     pd \<leftarrow> return $ obj_ref_of pd_cap;

     (frame, vptr) \<leftarrow> return $ case the_arch_cap frame_cap
                       of PageCap ref _ _ (Some (_, vptr)) \<Rightarrow> (ref, vptr);

     pd_obj \<leftarrow> get_object pd;
     pde \<leftarrow> return $ case pd_obj
                      of ArchObj (PageDirectory table)
                         \<Rightarrow> table (ucast (vptr >> pageBitsForSize ARMSection));

     pt \<leftarrow> return (case pde of PageTablePDE ref _ _ \<Rightarrow> ptrFromPAddr ref);

     slot \<leftarrow> return $ (vptr && mask (pageBitsForSize ARMSection))
                              >> pageBitsForSize ARMSmallPage;

     pte \<leftarrow> return $ SmallPagePTE (addrFromPPtr frame) {PageCacheable}
                                 vm_read_write;
     pt_obj \<leftarrow> get_object pt;
     pt_obj' \<leftarrow> return (case pt_obj
                         of ArchObj (PageTable table)
                            \<Rightarrow> ArchObj (PageTable $ table(ucast slot := pte)));
     set_object pt pt_obj'
   od"

definition
  write_it_pd_pts :: "cap \<Rightarrow> cap \<Rightarrow> (unit,'z::state_ext) ki_monad" where
  "write_it_pd_pts root_cnode_cap it_pd_cap \<equiv> doE

     do_kernel_op $ copy_global_mappings $ obj_ref_of it_pd_cap;

     (* map PTs into PD *)
     (start, end) \<leftarrow> liftE $ gets (bi_f_ui_pt_caps \<circ> ki_bootinfo);

     do_kernel_op $
       (swp mapM)
          [start..<end]
          (\<lambda>pos. do
                   cap \<leftarrow> get_cap_local $ cap_slot_pptr root_cnode_cap pos;
                   map_it_pt_cap it_pd_cap cap
                 od);

     (* map frames into PTs *)
     (start, end) \<leftarrow> liftE $ gets (bi_f_ui_frame_caps \<circ> ki_bootinfo);

     do_kernel_op (do
       (swp mapM)
          [start..<end]
          (\<lambda>pos. do
                   cap \<leftarrow> get_cap_local $ cap_slot_pptr root_cnode_cap pos;
                   map_it_frame_cap it_pd_cap cap
                 od);

       cap \<leftarrow> get_cap_local $ cap_slot_pptr root_cnode_cap BI_CAP_IT_IPCBUF;
       map_it_frame_cap it_pd_cap cap;
       cap \<leftarrow> get_cap_local $ cap_slot_pptr root_cnode_cap BI_CAP_BI_FRAME;
       map_it_frame_cap it_pd_cap cap
     od)
   odE"

definition
  bi_finalise :: "(unit,'z::state_ext) ki_monad" where
  "bi_finalise \<equiv> doE
     slot_pos_start \<leftarrow> liftE $ gets ndks_boot_slot_pos_cur;
     slot_pos_end \<leftarrow> liftE $ gets ndks_boot_slot_pos_max;
     liftE $ modify (\<lambda>s. s \<lparr> ki_bootinfo := (ki_bootinfo s) \<lparr>
       bi_f_null_caps := (of_nat slot_pos_start, of_nat slot_pos_end) \<rparr>\<rparr>);
     bi_frame \<leftarrow> liftE $ gets ndks_boot_bi_frame;
     sync_bootinfo_frame bi_frame
   odE"

definition
  create_it_pd_pts :: "cap \<Rightarrow> (vspace_ref \<times> vspace_ref) \<Rightarrow> vspace_ref
                       \<Rightarrow> vspace_ref \<Rightarrow> (cap,'z::state_ext) ki_monad" where
  "create_it_pd_pts root_cnode_cap ui_v_reg ipcbuf_vptr bi_frame_vptr \<equiv> doE

     (* create PD obj and cap *)
     pd_pptr \<leftarrow> create_objects PD_SIZE_BITS PD_SIZE_BITS
                              (ArchObject PageDirectoryObj);
     pd_cap \<leftarrow> returnOk $ ArchObjectCap $
                           PageDirectoryCap pd_pptr (Some IT_ASID);
     do_kernel_op $ write_slot (cap_slot_pptr root_cnode_cap BI_CAP_IT_PD)
                               pd_cap;

     (* include IPC buffer and bootinfo frames in the userland image *)
     (ui_v_reg_start, ui_v_reg_end) \<leftarrow>
         returnOk (fst ui_v_reg, bi_frame_vptr + 2 ^ BI_FRAME_SIZE_BITS);

     (* create all PT objs and caps necessary to cover userland image *)
     slot_pos_before \<leftarrow> liftE $ gets ndks_boot_slot_pos_cur;

     start \<leftarrow> returnOk $ round_down ui_v_reg_start (PD_BITS + pageBits);
     next \<leftarrow> returnOk $ start + (2 ^ (PT_BITS + pageBits));

     (swp mapME) [start,next .e. ui_v_reg_end] (\<lambda>pt_vptr. doE

       pt_pptr \<leftarrow> alloc_region PT_SIZE_BITS;
       do_kernel_op $ retype_region pt_pptr 1 PT_SIZE_BITS
                                            (ArchObject PageTableObj);

       provide_cap root_cnode_cap $
         ArchObjectCap $ PageTableCap pt_pptr (Some (IT_ASID, pt_vptr))
     odE);

     slot_pos_after \<leftarrow> liftE $ gets ndks_boot_slot_pos_cur;
     liftE $ modify (\<lambda>s. s \<lparr> ki_bootinfo := (ki_bootinfo s) \<lparr>
       bi_f_ui_pt_caps := (of_nat slot_pos_before, of_nat slot_pos_after) \<rparr>\<rparr>);
     bi_frame \<leftarrow> liftE $ gets ndks_boot_bi_frame;
     sync_bootinfo_frame bi_frame;

     returnOk pd_cap
   odE"

definition
  create_initial_thread :: "cap \<Rightarrow> cap \<Rightarrow> vspace_ref \<Rightarrow> vspace_ref \<Rightarrow> vspace_ref
                            \<Rightarrow> cap \<Rightarrow> (unit,'z::state_ext) ki_monad" where
  "create_initial_thread root_cnode_cap it_pd_cap ui_v_entry bi_frame_vptr
                         ipcbuf_vptr ipcbuf_cap \<equiv>
   let tcb_bits = obj_bits $ TCB undefined
   in
   doE

   (* allocate TCB *)
   tcb_pptr \<leftarrow> create_objects tcb_bits tcb_bits TCBObject;
   (* Arch_initContext should be implicit in retype_region *)

   do_kernel_op $ (do
     cap_insert_local root_cnode_cap (cap_slot_pptr root_cnode_cap BI_CAP_IT_CNODE)
                               (tcb_pptr, tcb_cnode_index 0); (* tcbCTable *)
     cap_insert_local root_cnode_cap (cap_slot_pptr root_cnode_cap BI_CAP_IT_PD)
                               (tcb_pptr, tcb_cnode_index 1); (* tcbVTable *)
     cap_insert_local root_cnode_cap (cap_slot_pptr root_cnode_cap BI_CAP_IT_IPCBUF)
                               (tcb_pptr, tcb_cnode_index 4); (* tcbBuffer *)

     tcb_obj \<leftarrow> get_object tcb_pptr;
     tcb_obj' \<leftarrow> return $
                case tcb_obj
                  of TCB tcb \<Rightarrow> TCB (tcb\<lparr>tcb_ipc_buffer := ipcbuf_vptr\<rparr>);
     set_object tcb_pptr tcb_obj';

     as_user tcb_pptr $ set_register CPSR 0x1f;
     as_user tcb_pptr $ setNextPC ui_v_entry;

     (* TCB priority not in abstract spec *)
     setup_reply_master_local tcb_pptr;
     set_thread_state tcb_pptr Running;
     (* scheduler action not in abstract spec *)
     idle_thread \<leftarrow> gets idle_thread;
     modify (\<lambda>s. s\<lparr> cur_thread := idle_thread \<rparr>);

     switch_to_thread tcb_pptr;

     cap \<leftarrow> return $ ThreadCap tcb_pptr;
     write_slot (cap_slot_pptr root_cnode_cap BI_CAP_IT_TCB) cap
   od)
   odE"

definition
  create_device_frames :: "cap \<Rightarrow> (unit,'z::state_ext) ki_monad" where
  "create_device_frames root_cnode_cap \<equiv> doE
     dev_regs \<leftarrow> do_kernel_op $ do_machine_op getDeviceRegions;

     (swp mapME) dev_regs (\<lambda>(start,end). doE
       (* use 1M frames if possible, else 4K frames *)
       frame_size \<leftarrow>
         returnOk $ if (is_aligned start (pageBitsForSize ARMSection)
                        \<and> is_aligned end (pageBitsForSize ARMSection))
                    then ARMSection
                    else ARMSmallPage;

       slot_pos_before \<leftarrow> liftE $ gets ndks_boot_slot_pos_cur;

       (swp mapME) [start,(start + 2^(pageBitsForSize frame_size))
                       .e. (end - 1)]
         (\<lambda>f. doE
                frame_cap \<leftarrow> create_it_frame_cap f 0 None
                                                (frame_size = ARMSection);
                provide_cap root_cnode_cap frame_cap
              odE);

       slot_pos_after \<leftarrow> liftE $ gets ndks_boot_slot_pos_cur;

       bi_dev_reg \<leftarrow> returnOk (addrFromPPtr start,
                              of_nat (pageBitsForSize frame_size),
                              (slot_pos_before, slot_pos_after));

       liftE $ modify (\<lambda>s. s \<lparr> ki_bootinfo := (ki_bootinfo s) \<lparr>
         bi_f_dev_reg_list := (bi_f_dev_reg_list $
                                 ki_bootinfo s) @ [bi_dev_reg]
         \<rparr>\<rparr>);

       bi_frame \<leftarrow> liftE $ gets ndks_boot_bi_frame;
       sync_bootinfo_frame bi_frame

     odE);

     liftE $ modify (\<lambda>s. s \<lparr> ki_bootinfo := (ki_bootinfo s) \<lparr>
       bi_f_num_dev_regs := of_nat $ length (bi_f_dev_reg_list $
                                               ki_bootinfo s)
       \<rparr>\<rparr>);

     bi_frame \<leftarrow> liftE $ gets ndks_boot_bi_frame;
     sync_bootinfo_frame bi_frame
   odE"

fun (* for (ptr,bits)-style regions which don't straddle the end of memory *)
  no_region_overlap :: "(paddr \<times> nat) \<Rightarrow> (paddr \<times> nat) \<Rightarrow> bool" where
  "no_region_overlap (ptr1,bits1) (ptr2,bits2) =
     ({ptr1 .. ptr1 + 2 ^ bits1 - 1} \<inter> {ptr2 .. ptr2 + 2 ^ bits2 - 1} = {})"

definition
  freemem_regions :: "obj_ref set \<Rightarrow> ((paddr \<times> nat) list,'z::state_ext) s_monad" where
  "freemem_regions free \<equiv> do
     regs \<leftarrow> select {lst. (\<forall>(ptr,bits) \<in> set lst. is_aligned ptr bits \<and>
                                           {ptr .. ptr + 2 ^ bits - 1} \<subseteq> free)
                         \<and> distinct_prop no_region_overlap lst};
     return regs
   od"

definition
  create_untyped_obj :: "cap \<Rightarrow> (paddr \<times> paddr) \<Rightarrow> (unit,'z::state_ext) ki_monad" where
  "create_untyped_obj root_cnode_cap boot_mem_reuse_reg \<equiv> doE

     slot_pos_before \<leftarrow> liftE $ gets ndks_boot_slot_pos_cur;

     (* re-use boot code/data frames *)
     (swp mapME) [fst boot_mem_reuse_reg,(fst boot_mem_reuse_reg + 2^pageBits)
                   .e. (snd boot_mem_reuse_reg - 1)]
                  (\<lambda>i. provide_untyped_cap root_cnode_cap i pageBits
                                           slot_pos_before);

     (* allocate and provide the minimum number of 4K UT objects requested *)
     slot_pos_cur \<leftarrow> liftE $ gets ndks_boot_slot_pos_cur;
     (swp mapME) [(slot_pos_cur - slot_pos_before)..<MIN_NUM_4K_UNTYPED_OBJ]
       (\<lambda>i. doE
              pptr \<leftarrow> alloc_region pageBits;
              provide_untyped_cap root_cnode_cap pptr pageBits slot_pos_before
            odE);

     (* convert remaining freemem into UT objects and provide the caps *)
     (* using non-determinism to the max *)
     freemem \<leftarrow> liftE $ gets ki_free_mem;
     freeregs \<leftarrow> do_kernel_op $ freemem_regions freemem;

     (swp mapME) (take MAX_NUM_FREEMEM_REG freeregs)
       (\<lambda>(start,bits). provide_untyped_cap root_cnode_cap start bits
                                           slot_pos_before);

     slot_pos_after \<leftarrow> liftE $ gets ndks_boot_slot_pos_cur;

     liftE $ modify (\<lambda>s. s \<lparr> ki_bootinfo := (ki_bootinfo s) \<lparr>
       bi_f_ut_obj_caps := (slot_pos_before, slot_pos_after) \<rparr>\<rparr>);

     bi_frame \<leftarrow> liftE $ gets ndks_boot_bi_frame;
     sync_bootinfo_frame bi_frame
   odE"

definition
  map_kernel_frame :: "paddr \<Rightarrow> vspace_ref \<Rightarrow> vm_rights \<Rightarrow> vm_attributes
                       \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "map_kernel_frame paddr vaddr vm_rights attributes \<equiv> do

     idx \<leftarrow> return $ (vaddr && mask (pageBitsForSize ARMSection))
                    >> pageBitsForSize ARMSmallPage;

     global_pt \<leftarrow> get_arm_global_pt;

     pte \<leftarrow> return $ SmallPagePTE paddr attributes vm_rights;

     store_pte (global_pt + (idx << PTE_SIZE_BITS)) pte
   od"


definition (* from plat/imx31/machine/hardware.c *)
  map_kernel_devices :: "(unit,'z::state_ext) s_monad" where
  "map_kernel_devices \<equiv> do
     map_kernel_frame EPIT_PADDR EPIT_PPTR vm_kernel_only
                      {ParityEnabled,PageCacheable};
     map_kernel_frame AVIC_PADDR AVIC_PPTR vm_kernel_only
                      {ParityEnabled,PageCacheable};
     map_kernel_frame L2CC_PADDR L2CC_PPTR vm_kernel_only
                      {ParityEnabled,PageCacheable}
   od"

definition
  map_kernel_window :: "(unit,'z::state_ext) s_monad" where
  "map_kernel_window \<equiv> do

     global_pd \<leftarrow> gets (arm_global_pd \<circ> arch_state);

     (* initial index into the PD, guaranteed to be divisible by 16 *)
     idx \<leftarrow> return $ kernel_base >> pageBitsForSize ARMSection;
     (* first physical address we'll map *)
     phys \<leftarrow> return $ physBase;

     (* map physBase at kernel_base 16M at a time, but not final supersection *)

     iterations \<leftarrow> return ((2^(PD_BITS) - idx) >> 4);

     (swp mapM) [0 .e. iterations - 1] (\<lambda>i. do
         idx' \<leftarrow> return $ idx + i * 16;
         phys' \<leftarrow> return $ phys + i * (2^(pageBitsForSize(ARMSuperSection)));

         pde \<leftarrow> return $ SuperSectionPDE phys' {ParityEnabled,PageCacheable}
                                         vm_kernel_only;

         (* write 16 section entries for this supersection *)
         mapM (\<lambda>offs. store_pde (idx' + offs) pde) [0 .e. 15]
       od);

     (* advance idx and phys to match exit of C loop *)
     idx \<leftarrow> return $ idx + iterations * 16; (* should be 2^PD_BITS - 16 *)
     phys \<leftarrow> return $ phys + iterations * (2^pageBitsForSize(ARMSuperSection));

     (* next 15M mapped using 1M frames *)

     (swp mapM) [0 .e. 14] (\<lambda>i. do
         phys' \<leftarrow> return $ phys + i * (2^(pageBitsForSize(ARMSection)));
         pde \<leftarrow> return $ SectionPDE phys' {ParityEnabled,PageCacheable} 0
                                   vm_kernel_only;
         store_pde (idx + i) pde
       od);

     (* advance idx and phys to match exit of C loop *)
     idx \<leftarrow> return $ idx + 15; (* should be 2^PD_BITS - 1 *)
     phys \<leftarrow> return $ phys + 15 * (2^pageBitsForSize(ARMSection));

     (* now map global PT into last slot in global PD  *)
     global_pt \<leftarrow> get_arm_global_pt;
     pde \<leftarrow> return $ PageTablePDE (addrFromPPtr global_pt) {ParityEnabled} 0;
     store_pde idx pde;

     (* init the PT *)
     retype_region global_pt 1 PT_SIZE_BITS
                   (ArchObject PageTableObj);

     (* map vector table *)
     map_kernel_frame (addrFromPPtr arm_vector_table) PPTR_VECTOR_TABLE
                      vm_kernel_only {ParityEnabled,PageCacheable};

     (* map globals frame *)
     globals_frame \<leftarrow> gets (arm_globals_frame \<circ> arch_state);
     map_kernel_frame (addrFromPPtr globals_frame) PPTR_GLOBALS_PAGE
                      vm_read_only {ParityEnabled,PageCacheable};

     (* map stack frame *)
     map_kernel_frame (addrFromPPtr arm_kernel_stack) PPTR_KERNEL_STACK
                      vm_kernel_only {ParityEnabled,PageCacheable};

     map_kernel_devices
   od"



definition
  paddr_to_pptr_reg :: "(paddr \<times> paddr) \<Rightarrow> (paddr \<times> paddr)" where
  "paddr_to_pptr_reg p_reg \<equiv> (fst p_reg + pptrBaseOffset,
                              snd p_reg + pptrBaseOffset)"

definition
  init_kernel :: "paddr \<Rightarrow> paddr \<Rightarrow> word32 \<Rightarrow> vspace_ref \<Rightarrow> (unit,'z::state_ext) ki_monad" where
  "init_kernel ui_p_reg_start ui_p_reg_end pv_offset v_entry \<equiv>
   let ui_v_reg_start = ui_p_reg_start - pv_offset;
       ui_v_reg_end = ui_p_reg_end - pv_offset;
       ui_v_reg = (ui_v_reg_start, ui_v_reg_end);
       ui_reg = paddr_to_pptr_reg (ui_p_reg_start, ui_p_reg_end)
   in
   doE
     do_kernel_op $ map_kernel_window;
     do_kernel_op $ init_cpu;
     do_kernel_op $ init_plat;
     init_freemem ui_reg;
     root_cnode_cap \<leftarrow> create_root_cnode;
     create_irq_cnode;
     do_kernel_op $ init_irqs root_cnode_cap;
     (* create initial thread's ipc buffer *)
     ipcbuf_ret \<leftarrow> create_ipcbuf_frame root_cnode_cap ui_v_reg;

     bi_frame_vptr \<leftarrow> create_bi_frame root_cnode_cap ui_v_reg
                                     (snd ipcbuf_ret) 0 1;

     (* create userland image frame objs, store info in bootinfo frame *)
     ui_fr_caps \<leftarrow> create_frames_of_region root_cnode_cap ui_reg True pv_offset;
     liftE $ modify (\<lambda>s. s \<lparr> ki_bootinfo := (ki_bootinfo s) \<lparr>
       bi_f_ui_frame_caps := ui_fr_caps \<rparr>\<rparr>);
     bi_frame \<leftarrow> liftE $ gets ndks_boot_bi_frame;
     sync_bootinfo_frame bi_frame;

     (* create/init PDs and PTs for userland image *)
     it_pd_cap \<leftarrow> create_it_pd_pts root_cnode_cap ui_v_reg (snd ipcbuf_ret)
                                   bi_frame_vptr;
     write_it_pd_pts root_cnode_cap it_pd_cap;

     (* create/init initial thread's ASID pool *)
     it_ap_cap \<leftarrow> create_it_asid_pool root_cnode_cap;
     do_kernel_op $ write_it_asid_pool it_ap_cap it_pd_cap;

     create_idle_thread;

     (* create_initial_thread *)
     create_initial_thread root_cnode_cap it_pd_cap v_entry bi_frame_vptr
                           (snd ipcbuf_ret) (fst ipcbuf_ret);

     (* create_untyped_obj (reclaim boot code/data) *)
     create_untyped_obj root_cnode_cap (kernel_base, ki_boot_end);

     (* create_device_frames *)
     create_device_frames root_cnode_cap;

     (* no shared frame caps (ARM = no multikernel) *)
     liftE $ modify (\<lambda>s. s \<lparr> ki_bootinfo := (ki_bootinfo s) \<lparr>
       bi_f_sh_frame_caps := (0,0) \<rparr>\<rparr>);
     bi_frame \<leftarrow> liftE $ gets ndks_boot_bi_frame;
     sync_bootinfo_frame bi_frame;

     bi_finalise;

     do_kernel_op $ do_machine_op cleanCache
   odE
  "

end
