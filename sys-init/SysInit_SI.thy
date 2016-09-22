(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory SysInit_SI
imports
  "../proof/capDL-api/Kernel_DP"
  "../lib/NonDetMonadLemmaBucket"
begin

definition
  parse_bootinfo :: "cdl_bootinfo \<Rightarrow> (cdl_cptr list \<times> cdl_cptr list) u_monad"
where
  "parse_bootinfo bootinfo \<equiv> do
    (untyped_start, untyped_end) \<leftarrow> return $ bi_untypes bootinfo;
    untyped_list \<leftarrow> return [untyped_start .e. (untyped_end - 1)];

    (free_slot_start, free_slot_end) \<leftarrow> return $ bi_free_slots bootinfo;
    free_slots \<leftarrow> return [free_slot_start .e. (free_slot_end - 1)];

    return (untyped_list, free_slots)
  od"

(* Currently, objects are created in any order.
   Later versions could create untypes before their children and use the untyped_covers.
   A refinement will create bigger ones first to remove internal fragmentation. *)
definition
  parse_spec :: "cdl_state \<Rightarrow> cdl_object_id list \<Rightarrow> unit u_monad"
where
  "parse_spec spec obj_ids \<equiv>
     assert (set obj_ids = dom (cdl_objects spec) \<and> distinct obj_ids)"

(* Create a new object in the next free cnode slot using a given untyped.
   Return whether or not the operation fails. *)
definition
  retype_untyped :: "cdl_cptr \<Rightarrow> cdl_cptr \<Rightarrow> cdl_object_type \<Rightarrow> nat \<Rightarrow> bool u_monad"
where
  "retype_untyped free_slot free_untyped type size_bits \<equiv>
    seL4_Untyped_Retype free_untyped type (of_nat size_bits)
                        seL4_CapInitThreadCNode 0 0 free_slot 1"

definition
  inc_when :: "bool \<Rightarrow> nat \<Rightarrow> ('s,nat) nondet_monad"
where
  "inc_when P x \<equiv> return (if P then Suc x else x)"

lemma inc_when_wp [wp]:
  "\<lbrace>Q (if B then Suc x else x)\<rbrace> inc_when B x \<lbrace>Q\<rbrace>"
  by (unfold inc_when_def, wp)

definition
  update_when :: "bool \<Rightarrow> ('a \<Rightarrow> 'b option) \<Rightarrow> 'a \<Rightarrow> 'b
                  \<Rightarrow> ('s,('a \<Rightarrow> 'b option)) nondet_monad"
where
  "update_when P t a b \<equiv> return (if P then t(a \<mapsto> b) else t)"

lemma update_when_wp [wp]:
  "\<lbrace>Q (if B then t(a \<mapsto> b) else t)\<rbrace> update_when B t a b \<lbrace>Q\<rbrace>"
  by (unfold update_when_def, wp)

(* Create the objects in the capDL spec.
   Caps to new objects are stored in the free slots. *)

definition create_objects :: "cdl_state \<Rightarrow> cdl_object_id list
                           \<Rightarrow> cdl_cptr list \<Rightarrow> cdl_cptr list
                           \<Rightarrow> ((cdl_object_id \<Rightarrow> cdl_cptr option) \<times> cdl_cptr list) u_monad"
where
  "create_objects spec obj_ids untyped_cptrs free_cptrs \<equiv> do
    (obj_id_index, untyped_index, si_caps) \<leftarrow> whileLoop (\<lambda>(obj_id_index, untyped_index, si_caps) _.
                     obj_id_index  < length [obj\<leftarrow>obj_ids. real_object_at obj spec] \<and>
                     obj_id_index  < length free_cptrs \<and>
                     untyped_index < length untyped_cptrs)
    (\<lambda>(obj_id_index, untyped_index, si_caps).
     do
        obj_id       \<leftarrow> return $ [obj\<leftarrow>obj_ids. real_object_at obj spec] ! obj_id_index;
        free_cptr    \<leftarrow> return $ free_cptrs ! obj_id_index;
        untyped_cptr \<leftarrow> return $ untyped_cptrs ! untyped_index;

        object      \<leftarrow> get_spec_object spec obj_id;
        object_type \<leftarrow> return $ object_type object;
        object_size \<leftarrow> return $ object_size_bits object;

        fail \<leftarrow> retype_untyped free_cptr untyped_cptr object_type object_size;

        obj_id_index  \<leftarrow> inc_when (\<not> fail) obj_id_index;
        untyped_index \<leftarrow> inc_when    fail  untyped_index;
        si_caps   \<leftarrow> update_when (\<not> fail) si_caps obj_id free_cptr;
        return (obj_id_index, untyped_index, si_caps)
     od) (0, 0, empty);
     assert (untyped_index \<noteq> length untyped_cptrs);
     return (si_caps, drop (length [obj\<leftarrow>obj_ids. real_object_at obj spec]) free_cptrs)
  od"


(* This makes the IRQ handler caps.
 * These caps are then used to set up the IRQs.
 * We need some predicate to say that they are there.
 * irq \<mapsto>c IrqHandlerCap cnode_id?
 *)
definition create_irq_cap :: "cdl_state \<Rightarrow> (cdl_irq \<times> cdl_cptr) \<Rightarrow> unit u_monad"
where
  "create_irq_cap spec \<equiv> \<lambda>(irq, free_cptr). do
    control_cap \<leftarrow> return seL4_CapIRQControl;
    root  \<leftarrow> return seL4_CapInitThreadCNode;
    index \<leftarrow> return $ free_cptr;
    depth \<leftarrow> return (32::word32);

    fail \<leftarrow> seL4_IRQControl_Get control_cap irq root index depth;
    assert (\<not>fail)
  od"

definition create_irq_caps :: "cdl_state \<Rightarrow> cdl_cptr list \<Rightarrow>
                              ((cdl_irq \<Rightarrow> cdl_cptr option) \<times> cdl_cptr list) u_monad"
where
  "create_irq_caps spec free_cptrs \<equiv> do
    irqs \<leftarrow> return $ used_irq_list spec;
    mapM_x (create_irq_cap spec) (zip irqs free_cptrs);
    si_irq_caps \<leftarrow> return $ map_of (zip irqs free_cptrs);
    return (si_irq_caps, drop (length irqs) free_cptrs)
  od"

(* This one installs the caps in the CNodes.
 * It uses seL4 _IRQHandler_SetEndpoint.
 * It turns irq_empty to irq_initialised?
 *)
definition
  init_irq :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_cptr option) \<Rightarrow>
              (cdl_irq \<Rightarrow> cdl_cptr option) \<Rightarrow> cdl_irq \<Rightarrow> unit u_monad"
where
  "init_irq spec orig_caps irq_caps irq \<equiv> do
    irq_handler_cap \<leftarrow> assert_opt $ irq_caps irq;
    irq_slot        \<leftarrow> return $ get_irq_slot irq spec;
    endpoint_cap    \<leftarrow> assert_opt $ opt_cap irq_slot spec;
    endpoint_cptr   \<leftarrow> assert_opt $ orig_caps (cap_object endpoint_cap);

    fail \<leftarrow> seL4_IRQHandler_SetEndpoint irq_handler_cap endpoint_cptr;
    assert (\<not>fail)
  od"

definition
  init_irqs :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_cptr option) \<Rightarrow>
               (cdl_irq \<Rightarrow> cdl_cptr option) \<Rightarrow> unit u_monad"
where
  "init_irqs spec orig_caps irq_caps \<equiv> do
    irqs \<leftarrow> return $ bound_irq_list spec;
    mapM_x (init_irq spec orig_caps irq_caps) irqs
  od"


(* Make a duplicate of a cap in a new free slot. *)
definition duplicate_cap :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_cptr option)
                              \<Rightarrow> (cdl_object_id \<times> cdl_cptr) \<Rightarrow> unit u_monad"
where
  "duplicate_cap spec orig_caps \<equiv> \<lambda>(obj_id, free_slot). do
    rights     \<leftarrow> return $ UNIV;

    dest_root  \<leftarrow> return seL4_CapInitThreadCNode;
    dest_index \<leftarrow> return $ free_slot;
    dest_depth \<leftarrow> return (32::word32);

    src_root   \<leftarrow> return seL4_CapInitThreadCNode;
    src_index  \<leftarrow> assert_opt $ orig_caps obj_id;
    src_depth  \<leftarrow> return (32::word32);

    fail \<leftarrow> seL4_CNode_Copy dest_root dest_index dest_depth
                            src_root src_index src_depth rights;
    assert (\<not>fail)
  od"

(* As CNode caps can be moved, referencing the CNodes can be tricky.
 * Moving capabilities in a particular order would work for all be difficult circular cases,
 * but just keeping a copy of the caps to all of the CNodes and using the copy is much easier.
 *
 * Thread caps are duplicated as the system initialiser needs to have them to start the threads
 * at the end of initialisation.
 *)
definition duplicate_caps :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_cptr option)
                                        \<Rightarrow> cdl_object_id list \<Rightarrow> cdl_cptr list
                                        \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_cptr option) u_monad"
where
  "duplicate_caps spec orig_caps obj_ids free_slots \<equiv> do
    obj_ids' \<leftarrow> return [obj_id \<leftarrow> obj_ids. cnode_at obj_id spec \<or> tcb_at obj_id spec];
    assert (length obj_ids' \<le> length free_slots);
    mapM_x (duplicate_cap spec orig_caps) (zip obj_ids' free_slots);
    return $ map_of $ zip obj_ids' free_slots
  od"

(* Initialise a single tcb (cspace, vspace and fault_ep). *)
definition init_tcb :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_cptr option) \<Rightarrow> cdl_object_id \<Rightarrow> unit u_monad"
where
  "init_tcb spec orig_caps tcb_id \<equiv> do
    cdl_tcb         \<leftarrow> assert_opt $ opt_thread tcb_id spec;
    cdl_cspace_root \<leftarrow> assert_opt $ opt_cap (tcb_id, tcb_cspace_slot) spec;
    cdl_vspace_root \<leftarrow> assert_opt $ opt_cap (tcb_id, tcb_vspace_slot) spec;
    cdl_ipcbuffer   \<leftarrow> assert_opt $ opt_cap (tcb_id, tcb_ipcbuffer_slot) spec;
    ipcbuf_addr     \<leftarrow> return $ tcb_ipc_buffer_address cdl_tcb;
    priority        \<leftarrow> return $ tcb_priority cdl_tcb;

    sel4_tcb         \<leftarrow> assert_opt $ orig_caps tcb_id;
    sel4_cspace_root \<leftarrow> assert_opt $ orig_caps (cap_object cdl_cspace_root);
    sel4_vspace_root \<leftarrow> assert_opt $ orig_caps (cap_object cdl_vspace_root);
    sel4_ipcbuffer   \<leftarrow> assert_opt $ orig_caps (cap_object cdl_ipcbuffer);
    sel4_fault_ep    \<leftarrow> return $ cdl_tcb_fault_endpoint cdl_tcb;

    sel4_cspace_root_data \<leftarrow> return $ guard_as_rawdata cdl_cspace_root;
    sel4_vspace_root_data \<leftarrow> return 0;

    fail \<leftarrow> seL4_TCB_Configure sel4_tcb sel4_fault_ep priority
                                  sel4_cspace_root sel4_cspace_root_data
                                  sel4_vspace_root sel4_vspace_root_data
                                  ipcbuf_addr sel4_ipcbuffer;
    assert (\<not>fail)
  od"

(* Set the registers of a single tcb (cspace, vspace and fault_ep). *)
definition configure_tcb :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_cptr option) \<Rightarrow> cdl_object_id \<Rightarrow> unit u_monad"
where
  "configure_tcb spec orig_caps tcb_id \<equiv> do
    cdl_tcb  \<leftarrow> assert_opt $ opt_thread tcb_id spec;
    sel4_tcb \<leftarrow> assert_opt $ orig_caps tcb_id;
    ip \<leftarrow> return $ tcb_ip cdl_tcb;
    sp \<leftarrow> return $ tcb_sp cdl_tcb;
    regs \<leftarrow> return [ip, sp];
    fail \<leftarrow> seL4_TCB_WriteRegisters sel4_tcb False 0 2 regs;
    assert fail
  od"

(* Initialise all the tcbs (cspace, vspace and fault_ep). *)
definition init_tcbs :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_cptr option) \<Rightarrow> cdl_object_id list \<Rightarrow> unit u_monad"
where
  "init_tcbs spec orig_caps objects \<equiv> do
    tcb_ids \<leftarrow> return [obj \<leftarrow> objects. tcb_at obj spec];
    mapM_x (init_tcb spec orig_caps) tcb_ids;
    mapM_x (configure_tcb spec orig_caps) tcb_ids
  od"



(**************************
 * VSpace Initialisation. *
 **************************)

(* Sets the asid for a page directory from the initialiser's asid pool. *)
definition set_asid :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_cptr option) \<Rightarrow> cdl_object_id
                                                                         \<Rightarrow> unit u_monad"
where
  "set_asid spec orig_caps page_id \<equiv> do
    (* Set asid pool for the page directory. *)
    sel4_asid_pool \<leftarrow> return seL4_CapInitThreadASIDPool;
    sel4_page \<leftarrow> assert_opt $ orig_caps page_id;
    fail \<leftarrow> seL4_ASIDPool_Assign sel4_asid_pool sel4_page;
    assert (\<not>fail)
  od"

(* Set the ASIDs for the page directories. *)
definition init_pd_asids :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_cptr option) \<Rightarrow> cdl_object_id list \<Rightarrow> unit u_monad"
where
  "init_pd_asids spec orig_caps obj_ids \<equiv> do
    pd_ids \<leftarrow> return [obj_id \<leftarrow> obj_ids. pd_at obj_id spec];
    mapM_x (set_asid spec orig_caps) pd_ids
  od"

(* Map the right cap into the slot of a page directory or page table. *)
definition map_page :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_cptr option) \<Rightarrow> cdl_object_id
                             \<Rightarrow> cdl_object_id \<Rightarrow> cdl_right set \<Rightarrow> word32 \<Rightarrow> unit u_monad"
where
  "map_page spec orig_caps page_id pd_id rights vaddr \<equiv> do
    cdl_page  \<leftarrow> assert_opt $ opt_object page_id spec;
    sel4_page \<leftarrow> assert_opt $ orig_caps page_id;
    sel4_pd   \<leftarrow> assert_opt $ orig_caps pd_id;

    vmattribs \<leftarrow> assert_opt $ opt_vmattribs cdl_page;

    if (pt_at page_id spec) then
      seL4_PageTable_Map sel4_page sel4_pd vaddr vmattribs
    else if (frame_at page_id spec) then
      seL4_Page_Map sel4_page sel4_pd vaddr rights vmattribs
    else
      fail;
     return ()
  od"

(* Maps a page directory slot (and all its contents if it's a page table). *)
definition map_page_directory_slot :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_cptr option)
                                    \<Rightarrow> cdl_object_id\<Rightarrow> cdl_cnode_index \<Rightarrow> unit u_monad"
where
  "map_page_directory_slot spec orig_caps pd_id pd_slot \<equiv> do
    page_cap    \<leftarrow> assert_opt $ opt_cap (pd_id, pd_slot) spec;
    page_id     \<leftarrow> return $ cap_object page_cap;

    (* The page table's virtual address is given by the number of slots and how much memory each maps.
       Each page directory slot maps 10+12 bits of memory (by the page table and page respectively). *)
    page_vaddr  \<leftarrow> return $ of_nat pd_slot << (pt_size + small_frame_size);
    page_rights \<leftarrow> return (cap_rights page_cap);

    when (page_cap \<noteq> NullCap)
         (map_page spec orig_caps page_id pd_id page_rights page_vaddr)

  od"

(* Maps a page directory and all its contents. *)
definition map_page_directory :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_cptr option) \<Rightarrow> cdl_object_id
                                                                                   \<Rightarrow> unit u_monad"
where
  "map_page_directory spec orig_caps pd_id \<equiv> do
    pd_slots \<leftarrow> return $ slots_of_list spec pd_id;
    mapM_x (map_page_directory_slot spec orig_caps pd_id) pd_slots
  od"

(* Maps a page directory slot. *)
definition map_page_table_slot :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_cptr option) \<Rightarrow> cdl_object_id
                                      \<Rightarrow> cdl_object_id \<Rightarrow> word32 \<Rightarrow> cdl_cnode_index \<Rightarrow> unit u_monad"
where
  "map_page_table_slot spec orig_caps pd_id pt_id pt_vaddr pt_slot \<equiv> do
    frame_cap  \<leftarrow> assert_opt $ opt_cap (pt_id, pt_slot) spec;
    page       \<leftarrow> return $ cap_object frame_cap;

    (* The page's virtual address is the page table's virtual address,
       plus the relative address of the page in the page table.
       Each page stores 12 bits of memory. *)
    page_vaddr   \<leftarrow> return $ pt_vaddr + (of_nat pt_slot << small_frame_size);
    page_rights  \<leftarrow> return (cap_rights frame_cap);
    when (frame_cap \<noteq> NullCap)
      (map_page spec orig_caps page pd_id page_rights page_vaddr)
  od"

(* Maps a page table's slots. *)
definition map_page_table_slots :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_cptr option) \<Rightarrow> cdl_object_id
                                                                  \<Rightarrow> cdl_cnode_index \<Rightarrow> unit u_monad"
where
  "map_page_table_slots spec orig_caps pd_id pd_slot \<equiv> do
    page_cap    \<leftarrow> assert_opt $ opt_cap (pd_id, pd_slot) spec;
    page        \<leftarrow> return $ cap_object page_cap;
    page_slots  \<leftarrow> return $ slots_of_list spec page;

    (* The page's virtual address is given by the number of slots and how much memory each maps.
       Each page directory slot maps 10+12 bits of memory (by the page table and page respectively). *)
    page_vaddr  \<leftarrow> return $ of_nat pd_slot << (pt_size + small_frame_size);

    when (fake_pt_cap_at (pd_id, pd_slot) spec)
      (mapM_x (map_page_table_slot spec orig_caps pd_id page page_vaddr) page_slots)
  od"

(* Maps a page directory and all its contents. *)
definition map_page_directory_page_tables :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_cptr option) \<Rightarrow> cdl_object_id
                                                                                               \<Rightarrow> unit u_monad"
where
  "map_page_directory_page_tables spec orig_caps pd_id \<equiv> do
    pd_slots \<leftarrow> return $ slots_of_list spec pd_id;
    mapM_x (map_page_table_slots spec orig_caps pd_id) pd_slots
  od"

(* Maps page directories and all their contents. *)
definition init_vspace :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_cptr option) \<Rightarrow> cdl_object_id list \<Rightarrow> unit u_monad"
where
  "init_vspace spec orig_caps obj_ids \<equiv> do
    pd_ids \<leftarrow> return [obj_id \<leftarrow> obj_ids. pd_at obj_id spec];
    mapM_x (map_page_directory spec orig_caps) pd_ids;
    mapM_x (map_page_directory_page_tables spec orig_caps) pd_ids
  od"

(**************************
 * CSpace Initialisation. *
 **************************)

datatype init_cnode_mode = Move | Copy

(* initialises a CNode slot with the desired cap, either moving them or copying it. *)
definition init_cnode_slot :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_cptr option)
                                         \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_cptr option)
                                         \<Rightarrow> (cdl_irq \<Rightarrow> cdl_cptr option)
                                         \<Rightarrow> init_cnode_mode \<Rightarrow> cdl_object_id
                                         \<Rightarrow> cdl_cnode_index \<Rightarrow> bool u_monad"
where
  "init_cnode_slot spec orig_caps dup_caps irq_caps mode cnode_id cnode_slot \<equiv> do
    target_cap     \<leftarrow> assert_opt (opt_cap (cnode_id, cnode_slot) spec);
    target_cap_obj \<leftarrow> return (cap_object target_cap);
    target_cap_irq \<leftarrow> return (cap_irq target_cap);

    target_cap_rights     \<leftarrow> return (cap_rights target_cap);

    (* for endpoint this is the badge, for cnodes, this is the (encoded) guard *)
    target_cap_data \<leftarrow> return (cap_data target_cap);

    is_ep_cap   \<leftarrow> return (ep_related_cap target_cap);
    is_irqhandler_cap \<leftarrow> return (is_irqhandler_cap target_cap);

    (* Any original caps (which includes IRQ Hander caps) are moved, not copied. *)
    move_cap \<leftarrow> return (original_cap_at (cnode_id, cnode_slot) spec);

    dest_obj   \<leftarrow> get_spec_object spec cnode_id;
    dest_size  \<leftarrow> return (object_size_bits dest_obj);

    (* Use a copy of the cap to reference the destination,
        in case the original has already been moved. *)
    dest_root  \<leftarrow> assert_opt (dup_caps cnode_id);
    dest_index \<leftarrow> return (of_nat cnode_slot);
    dest_depth \<leftarrow> return (of_nat dest_size);

    (* Use an original cap to reference the object to copy. *)
    src_root   \<leftarrow> return seL4_CapInitThreadCNode;
    src_index  \<leftarrow> assert_opt (if is_irqhandler_cap
                              then irq_caps target_cap_irq
                              else orig_caps target_cap_obj);
    src_depth  \<leftarrow> return (32::word32);

    (* If it's a NullCap, then there's no need to do anything.
     * If it's a cap that wants to be moved, and we want to move the cap, move (mutate) it.
     * If it's a cap that wants to be copied, and we want to copy it, then copy (mint) it.
     *)
    if (target_cap = NullCap) then
      return True
    else if (mode = Move \<and> move_cap) then (
      if (is_ep_cap \<or> is_irqhandler_cap) then
        (seL4_CNode_Move dest_root dest_index dest_depth src_root src_index src_depth)
      else
        (seL4_CNode_Mutate dest_root dest_index dest_depth src_root src_index src_depth target_cap_data)
    )
    else if (mode = Copy \<and> \<not> move_cap) then
      seL4_CNode_Mint dest_root dest_index dest_depth src_root src_index src_depth target_cap_rights target_cap_data
    else
      return True
  od"

(* Initialises a CNode with it's desired caps, either moving them or copying them. *)
definition init_cnode :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_cptr option)
                                    \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_cptr option)
                                    \<Rightarrow> (cdl_irq \<Rightarrow> cdl_cptr option)
                                    \<Rightarrow> init_cnode_mode \<Rightarrow> cdl_object_id \<Rightarrow> unit u_monad"
where
  "init_cnode spec orig_caps dup_caps irq_caps mode cnode_id \<equiv> do
    cnode_slots \<leftarrow> return $ slots_of_list spec cnode_id;
    mapM_x (init_cnode_slot spec orig_caps dup_caps irq_caps mode cnode_id) cnode_slots
  od"

(* Initialises CNodes with their desired caps in two passes.
   First pass copies caps, the second moves them. *)
definition init_cspace :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_cptr option)
                                     \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_cptr option)
                                     \<Rightarrow> (cdl_irq \<Rightarrow> cdl_cptr option)
                                     \<Rightarrow> cdl_object_id list \<Rightarrow> unit u_monad"
where
  "init_cspace spec orig_caps dup_caps irq_caps obj_ids \<equiv> do
    cnode_ids \<leftarrow> return [obj_id \<leftarrow> obj_ids. cnode_at obj_id spec];
    mapM_x (init_cnode spec orig_caps dup_caps irq_caps Copy) cnode_ids;
    mapM_x (init_cnode spec orig_caps dup_caps irq_caps Move) cnode_ids
  od"

(* Initialise a single tcb (cspace, vspace and fault_ep). *)
definition start_thread :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_cptr option) \<Rightarrow> cdl_object_id \<Rightarrow> unit u_monad"
where
  "start_thread spec dup_caps tcb_id \<equiv> do
    sel4_tcb \<leftarrow> assert_opt $ dup_caps tcb_id;
    fail \<leftarrow> seL4_TCB_Resume sel4_tcb;
    assert fail
  od"

definition start_threads :: "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_cptr option) \<Rightarrow> cdl_object_id list
                                                                                  \<Rightarrow> unit u_monad"
where
  "start_threads spec orig_caps obj_ids \<equiv> do
    tcbs \<leftarrow> return [obj_id \<leftarrow> obj_ids. is_waiting_thread_at obj_id spec];
    mapM_x (start_thread spec orig_caps) tcbs
  od"

definition init_system :: "cdl_state \<Rightarrow> cdl_bootinfo \<Rightarrow> cdl_object_id list \<Rightarrow> unit u_monad"
where
  "init_system spec bootinfo obj_ids \<equiv> do
    (untyped_cptrs, free_cptrs) \<leftarrow> parse_bootinfo bootinfo;

    (orig_caps, free_cptrs) \<leftarrow> create_objects spec obj_ids untyped_cptrs free_cptrs;
    (irq_caps, free_cptrs) \<leftarrow> create_irq_caps spec free_cptrs;
    dup_caps \<leftarrow> duplicate_caps spec orig_caps obj_ids free_cptrs;

    init_irqs     spec orig_caps irq_caps;
    init_pd_asids spec orig_caps obj_ids;
    init_vspace   spec orig_caps obj_ids;
    init_tcbs     spec orig_caps obj_ids;
    init_cspace   spec orig_caps dup_caps irq_caps obj_ids;
    start_threads spec dup_caps obj_ids
  od"

end
