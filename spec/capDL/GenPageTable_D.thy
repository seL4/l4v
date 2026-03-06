(*
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
 * Operations on generic page table objects and frames. The intention is that these operations
 * can be instantiated, or in some cases used directly, to model the behaviour of multiple different
 * seL4 architectures.
 *)

theory GenPageTable_D
imports
  Invocations_D
  CSpace_D
begin

(* FIXME AARCH64: move to nondet_monad *)
(* A monad that may produce anything, including failure. *)
definition chaos :: "('s, 'a) nondet_monad" where
  "chaos \<equiv> \<lambda>s. (UNIV, True)"

section \<open>Decode\<close>

text \<open>
  We model decoding of mapping invocations only, because these are the only ones relevant
  for system initialisation.\<close>

definition cdl_check_vspace_root :: "cdl_cap \<Rightarrow> (cdl_object_id \<times> cdl_asid) option" where
  "cdl_check_vspace_root vspace_cap \<equiv>
     case vspace_cap of
       PageTableCap pt_t pt _ (Some (asid, _)) \<Rightarrow>
         if pt_t = vspace_type then Some (pt, asid) else None
     | _ \<Rightarrow> None"

(* The name is slightly misleading for AARCH32 where the number of bits left also depends on the
   frame size for repeated entries (SuperSection/LargePage). However, when the vptr is aligned
   to the frame size, the returned slot in cdl_pt_slot will still be correct with this shift
   index and represent the first slot of the repeated entry. *)
definition cdl_pt_bits_left :: "nat \<Rightarrow> nat" where
  "cdl_pt_bits_left level \<equiv> fold (+) (map pt_translation_bits [0..<level]) pageBits"

definition cdl_pt_index :: "nat \<Rightarrow> vptr \<Rightarrow> nat" where
  "cdl_pt_index level vptr \<equiv>
     unat ((vptr >> cdl_pt_bits_left level) && mask (pt_translation_bits level))"

definition cdl_pt_slot :: "nat \<Rightarrow> cdl_object_id \<Rightarrow> vptr \<Rightarrow> cdl_cap_ref" where
  "cdl_pt_slot level pt_ptr vptr = (pt_ptr, cdl_pt_index level vptr)"

function cdl_pt_walk ::
  "nat \<Rightarrow> nat \<Rightarrow> cdl_object_id \<Rightarrow> vptr \<Rightarrow> cdl_state \<Rightarrow> (nat \<times> cdl_object_id) option"
  where
  "cdl_pt_walk level bot_level pt_ptr vptr = do {
     if bot_level < level
     then do {
       mapping_cap \<leftarrow> opt_cap (cdl_pt_slot level pt_ptr vptr);
       if is_PageTableCap mapping_cap
         then cdl_pt_walk (level - 1) bot_level (cdl_obj mapping_cap) vptr
         else oreturn (level, pt_ptr)
     }
     else oreturn (level, pt_ptr)
   }"
  by auto

termination cdl_pt_walk
  by (relation "measure fst"; simp)

declare cdl_pt_walk.simps[simp del]

definition cdl_pt_lookup_slot ::
  "cdl_object_id \<Rightarrow> vptr \<Rightarrow> cdl_state \<Rightarrow> (nat \<times> cdl_cap_ref) option"
  where
  "cdl_pt_lookup_slot pt vaddr = do {
     (level, pt_ptr') \<leftarrow> cdl_pt_walk max_pt_level 0 pt vaddr;
     oreturn (level, cdl_pt_slot level pt_ptr' vaddr)
   }"

(* Different architectures have different requirements on which page tables types can be mapped
   into which other ones. The h parameter is the type of the higher level, the l parameter the
   type of the lower level that is being mapped into h. *)
definition check_pt_map_types :: "cdl_pt_type \<Rightarrow> cdl_pt_type \<Rightarrow> bool" where
  "check_pt_map_types h l \<equiv>
     case cdl_ARCH of
       AARCH32 \<Rightarrow> h = PD \<and> l = PT
     | AARCH64 \<Rightarrow> (h = VSROOT \<or> h = PT) \<and> l = PT
     | RISCV32 \<Rightarrow> h = PT \<and> l = PT
     | RISCV64 \<Rightarrow> (h = VSROOT \<or> h = PT) \<and> l = PT
     | IA32    \<Rightarrow> h = PD \<and> l = PT
     | X64     \<Rightarrow> h = PML4 \<and> l = PDPT \<or>
                  h = PDPT \<and> l = PD \<or>
                  h = PD \<and> l = PT"

definition gen_decode_page_table_invocation ::
  "cdl_cap \<Rightarrow> cdl_cap_ref \<Rightarrow> (cdl_cap \<times> cdl_cap_ref) list \<Rightarrow>
   cdl_page_table_intent \<Rightarrow> cdl_page_table_invocation except_monad"
  where
  "gen_decode_page_table_invocation pt_cap target_ref caps intent \<equiv> case intent of
     PageTableMapIntent vaddr attr \<Rightarrow> doE
       whenE (cdl_mapped_addr pt_cap \<noteq> None) throw;
       (vspace_cap, _) \<leftarrow> throw_on_none $ get_index caps 0;
       (vs, asid) \<leftarrow> throw_on_none $ cdl_check_vspace_root vspace_cap;
       unlessE (check_pt_map_types (cdl_cap_pt_type vspace_cap) (cdl_cap_pt_type pt_cap)) throw;
       (level, slot) \<leftarrow> liftE $ gets_the $ cdl_pt_lookup_slot vs vaddr;
       \<comment> \<open>make sure we are not mapping a table into the last level\<close>
       whenE (level = 0) throw;
       new_attribs \<leftarrow> returnOk $ validate_pt_vm_attributes attr;
       p \<leftarrow> returnOk $ cap_object pt_cap;
       pt_t \<leftarrow> returnOk $ cdl_cap_pt_type pt_cap;
       ma \<leftarrow> returnOk $ Some (asid, vaddr && ~~mask (cdl_pt_bits_left level));
       returnOk $ PageTableMap
                    (PageTableCap pt_t p Real ma)
                    (PageTableCap pt_t p (Fake new_attribs) None)
                    target_ref
                    slot
     odE \<sqinter> throw
   \<comment> \<open>Other intents are not needed for system initialisation and not modelled here.\<close>
   | _ \<Rightarrow> select UNIV"

definition gen_decode_page_invocation ::
  "cdl_cap \<Rightarrow> cdl_cap_ref \<Rightarrow> (cdl_cap \<times> cdl_cap_ref) list \<Rightarrow> cdl_page_intent \<Rightarrow>
   cdl_page_invocation except_monad"
  where
  "gen_decode_page_invocation target target_ref caps intent \<equiv> case intent of
     PageMapIntent vaddr rights attr \<Rightarrow> doE
       (vs_cap, _) \<leftarrow> throw_on_none $ get_index caps 0;
       (vs, asid) \<leftarrow> throw_on_none $ cdl_check_vspace_root vs_cap;
       (frame, sz, dev) \<leftarrow> returnOk $ (case target of FrameCap dev p R sz m mp \<Rightarrow> (p, sz, dev));
       (level, slot) \<leftarrow> liftE $ gets_the $ cdl_pt_lookup_slot vs vaddr;
       unlessE (cdl_pt_bits_left level = sz) throw;
       new_rights \<leftarrow> returnOk $ validate_vm_rights $ cap_rights target \<inter> rights;
       new_attribs \<leftarrow> returnOk $ validate_vm_attributes attr (pageForPageBits sz);
       returnOk $ PageMap
                    (FrameCap dev frame (cap_rights target) sz Real (Some (asid, vaddr)))
                    (FrameCap False frame new_rights sz (Fake new_attribs) None)
                    target_ref
                    slot
     odE \<sqinter> throw
   \<comment> \<open>Other intents are not needed for system initialisation and not modelled here.\<close>
   | _ \<Rightarrow> select UNIV"


section \<open>Invoke\<close>

definition gen_invoke_page_table :: "cdl_page_table_invocation \<Rightarrow> unit k_monad" where
  "gen_invoke_page_table params \<equiv> case params of
     PageTableMap real_pt_cap mapping_cap pt_cap_ref target_slot \<Rightarrow> do
       set_cap pt_cap_ref real_pt_cap;            \<comment> \<open>update real PT cap in CSpace\<close>
       insert_cap_orphan mapping_cap target_slot  \<comment> \<open>store mapping cap in page table\<close>
     od
   | _ \<Rightarrow> chaos"

definition gen_invoke_page :: "cdl_page_invocation \<Rightarrow> unit k_monad" where
  "gen_invoke_page params \<equiv> case params of
     PageMap frame_cap pseudo_frame_cap frame_cap_ref pt_slot \<Rightarrow> do
       set_cap frame_cap_ref frame_cap;  \<comment> \<open>update real page cap in CSpace\<close>
       set_cap pt_slot pseudo_frame_cap  \<comment> \<open>store mapping cap in page table\<close>
     od
   | _ \<Rightarrow> chaos"

end
