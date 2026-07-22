(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2022, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Accessing the AARCH64 VSpace"

theory ArchVSpaceAcc_A
imports KHeap_A
begin

context Arch begin arch_global_naming (A)

text \<open>
  This part of the specification is fairly concrete as the machine architecture is visible to
  the user in seL4 and therefore needs to be described. The abstraction compared to the
  implementation is in the data types for kernel objects. The interface which is rich in machine
  details remains the same.
\<close>

section "Encodings"

text \<open>The high bits of a virtual ASID.\<close>
definition asid_high_bits_of :: "asid \<Rightarrow> asid_high_index" where
  "asid_high_bits_of asid \<equiv> ucast (asid >> asid_low_bits)"

text \<open>The low bits of a virtual ASID.\<close>
definition asid_low_bits_of :: "asid \<Rightarrow> asid_low_index" where
  "asid_low_bits_of asid \<equiv> ucast asid"

lemmas asid_bits_of_defs = asid_high_bits_of_def asid_low_bits_of_def

locale_abbrev asid_table :: "'z::state_ext state \<Rightarrow> asid_high_index \<rightharpoonup> obj_ref" where
  "asid_table \<equiv> \<lambda>s. arm_asid_table (arch_state s)"

locale_abbrev asid_map :: "'z::state_ext state \<Rightarrow> asid \<rightharpoonup> vmid" where
  "asid_map \<equiv> \<lambda>s. arm_asid_map (arch_state s)"

section "Kernel Heap Accessors"

(* declared in Arch as workaround for VER-1099 *)
locale_abbrev aobjs_of :: "'z::state_ext state \<Rightarrow> obj_ref \<rightharpoonup> arch_kernel_obj" where
  "aobjs_of \<equiv> \<lambda>s. kheap s |> aobj_of"

text \<open>Manipulate ASID pools, page directories and page tables in the kernel heap.\<close>

locale_abbrev asid_pools_of :: "'z::state_ext state \<Rightarrow> obj_ref \<rightharpoonup> asid_pool" where
  "asid_pools_of \<equiv> \<lambda>s. aobjs_of s |> asid_pool_of"

locale_abbrev get_asid_pool :: "obj_ref \<Rightarrow> (asid_pool, 'z::state_ext) s_monad" where
  "get_asid_pool \<equiv> gets_map asid_pools_of"

definition set_asid_pool :: "obj_ref \<Rightarrow> asid_pool \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "set_asid_pool ptr pool \<equiv> do
     get_asid_pool ptr;
     set_object ptr (ArchObj (ASIDPool pool))
   od"

locale_abbrev pts_of :: "'z::state_ext state \<Rightarrow> obj_ref \<rightharpoonup> pt" where
  "pts_of \<equiv> \<lambda>s. aobjs_of s |> pt_of"

locale_abbrev get_pt :: "obj_ref \<Rightarrow> (pt,'z::state_ext) s_monad" where
  "get_pt \<equiv> gets_map pts_of"

definition set_pt :: "obj_ref \<Rightarrow> pt \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "set_pt ptr pt \<equiv> do
     get_pt ptr;
     set_object ptr (ArchObj (PageTable pt))
   od"

text \<open>The base address of the table a page table entry at p is in (assuming alignment)\<close>
locale_abbrev table_base :: "pt_type \<Rightarrow> obj_ref \<Rightarrow> obj_ref" where
  "table_base pt_t p \<equiv> p && ~~mask (pt_bits pt_t)"

text \<open>The index within the page table that a page table entry at p addresses. We return a
  @{typ machine_word}, which is the slice of the provided address that represents the index in the
  table of the specified table type.\<close>
locale_abbrev table_index :: "pt_type \<Rightarrow> obj_ref \<Rightarrow> machine_word" where
  "table_index pt_t p \<equiv> p && mask (pt_bits pt_t) >> pte_bits"

text \<open>Use an index computed by @{const table_index} and apply it to a page table. Bits higher than
  the table index width will be ignored.\<close>
definition pt_apply :: "pt \<Rightarrow> machine_word \<Rightarrow> pte" where
  "pt_apply pt idx \<equiv> case pt of NormalPT npt \<Rightarrow> npt (ucast idx) | VSRootPT vs \<Rightarrow> vs (ucast idx)"

text \<open>Extract a PTE from the page table of a specific level\<close>
definition level_pte_of :: "pt_type \<Rightarrow> obj_ref \<Rightarrow> (obj_ref \<rightharpoonup> pt) \<rightharpoonup> pte" where
  "level_pte_of pt_t p \<equiv> do {
      oassert (is_aligned p pte_bits);
      pt \<leftarrow> oapply (table_base pt_t p);
      oassert (pt_type pt = pt_t);
      oreturn $ pt_apply pt (table_index pt_t p)
   }"

type_synonym ptes_of = "pt_type \<Rightarrow> obj_ref \<rightharpoonup> pte"

locale_abbrev ptes_of :: "'z::state_ext state \<Rightarrow> ptes_of" where
  "ptes_of s pt_t p \<equiv> level_pte_of pt_t p (pts_of s)"

lemmas ptes_of_def = level_pte_of_def

text \<open>The following function takes a pointer to a PTE in kernel memory and returns the PTE.\<close>
locale_abbrev get_pte :: "pt_type \<Rightarrow> obj_ref \<Rightarrow> (pte,'z::state_ext) s_monad" where
  "get_pte pt_t \<equiv> gets_map (swp ptes_of pt_t)"


text \<open>The update function that corresponds to @{const pt_apply}. Also expects an index computed
  with @{const table_index} for the correct page table type.\<close>
definition pt_upd :: "pt \<Rightarrow> machine_word \<Rightarrow> pte \<Rightarrow> pt" where
  "pt_upd pt idx pte \<equiv> case pt of
                         VSRootPT vs \<Rightarrow> VSRootPT (vs(ucast idx := pte))
                       | NormalPT pt \<Rightarrow> NormalPT (pt(ucast idx := pte))"

definition store_pte :: "pt_type \<Rightarrow> obj_ref \<Rightarrow> pte \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "store_pte pt_t p pte \<equiv> do
     assert (is_aligned p pte_bits);
     base \<leftarrow> return $ table_base pt_t p;
     pt \<leftarrow> get_pt base;
     assert (pt_type pt = pt_t);
     set_pt base (pt_upd pt (table_index pt_t p) pte)
   od"


section "Basic Operations"

(* During pt_walk, we will only call this with level \<le> max_pt_level, but in the invariants we
   also make use of this function for level = asid_pool_level. *)
definition pt_bits_left :: "vm_level \<Rightarrow> nat" where
  "pt_bits_left level =
    (if level = asid_pool_level
     then ptTranslationBits VSRootPT_T + ptTranslationBits NormalPT_T * size max_pt_level
     else ptTranslationBits NormalPT_T * size level)
    + pageBits"

definition pt_index :: "vm_level \<Rightarrow> vspace_ref \<Rightarrow> machine_word" where
  "pt_index level vptr \<equiv>
     (vptr >> pt_bits_left level) && mask (ptTranslationBits level)"


locale_abbrev global_pt :: "'z state \<Rightarrow> obj_ref" where
  "global_pt s \<equiv> arm_us_global_vspace (arch_state s)"


subsection \<open>Walk page tables in software.\<close>

definition pptr_from_pte :: "pte \<Rightarrow> vspace_ref" where
  "pptr_from_pte pte \<equiv> ptrFromPAddr (pte_base_addr pte)"

definition pt_slot_offset :: "vm_level \<Rightarrow> obj_ref \<Rightarrow> vspace_ref \<Rightarrow> obj_ref" where
  "pt_slot_offset level pt_ptr vptr = pt_ptr + (pt_index level vptr << pte_bits)"

text \<open>
  This is the base function for walking a page table structure.
  The walk proceeds from higher-level tables at the provided @{term level} (e.g. 2) to lower
  level tables, down to @{term bot_level} (e.g. 0). It returns a pointer to the page table where
  the walk stopped and the level of that table. The lookup stops when @{term bot_level} or a
  page is reached.
\<close>
fun pt_walk ::
  "vm_level \<Rightarrow> vm_level \<Rightarrow> obj_ref \<Rightarrow> vspace_ref \<Rightarrow> ptes_of \<Rightarrow> (vm_level \<times> obj_ref) option"
  where
  "pt_walk level bot_level pt_ptr vptr = do {
     if bot_level < level
     then do {
       pte \<leftarrow> oapply2 (level_type level) (pt_slot_offset level pt_ptr vptr);
       if is_PageTablePTE pte
         then pt_walk (level - 1) bot_level (pptr_from_pte pte) vptr
         else oreturn (level, pt_ptr)
     }
     else oreturn (level, pt_ptr)
   }"

declare pt_walk.simps[simp del]

text \<open>
  Looking up a slot in a page table structure. The function returns a level and an object
  pointer. The pointer is to a slot in a table at the returned level. If the returned level is 0,
  this slot is either an @{const InvalidPTE} or a @{const PagePTE}. If the returned level is higher
  the slot may also be a @{const PageTablePTE}.
\<close>
definition pt_lookup_slot_from_level ::
  "vm_level \<Rightarrow> vm_level \<Rightarrow> obj_ref \<Rightarrow> vspace_ref \<Rightarrow> ptes_of \<Rightarrow> (vm_level \<times> obj_ref) option" where
  "pt_lookup_slot_from_level level bot_level pt_ptr vptr = do {
     (level', pt_ptr') \<leftarrow> pt_walk level bot_level pt_ptr vptr;
     oreturn (level', pt_slot_offset level' pt_ptr' vptr)
   }"

definition pt_lookup_slot :: "obj_ref \<Rightarrow> vspace_ref \<Rightarrow> ptes_of \<Rightarrow> (vm_level \<times> obj_ref) option" where
  "pt_lookup_slot = pt_lookup_slot_from_level max_pt_level 0"

text \<open>Returns the slot that points to @{text target_pt_ptr}\<close>
fun pt_lookup_from_level ::
  "vm_level \<Rightarrow> obj_ref \<Rightarrow> vspace_ref \<Rightarrow> obj_ref \<Rightarrow> (machine_word \<times> vm_level, 'z::state_ext) lf_monad"
  where
  "pt_lookup_from_level level pt_ptr vptr target_pt_ptr s = (doE
     unlessE (0 < level) $ throwError InvalidRoot;
     slot <- returnOk $ pt_slot_offset level pt_ptr vptr;
     pte <- liftE $ gets_the $ oapply slot o swp ptes_of level;
     unlessE (is_PageTablePTE pte) $ throwError InvalidRoot;
     ptr <- returnOk (pptr_from_pte pte);
     if ptr = target_pt_ptr
       then returnOk (slot, level)
       else pt_lookup_from_level (level - 1) ptr vptr target_pt_ptr
   odE) s"
(* We apply "s" to avoid a type variable warning, and increase in global freeindex counter,
   which we would get without the application *)

declare pt_lookup_from_level.simps[simp del]

(* Recover simp rule without state applied: *)
schematic_goal pt_lookup_from_level_simps:
  "pt_lookup_from_level level pt_ptr vptr target_pt_ptr = ?rhs"
  by (rule ext, rule pt_lookup_from_level.simps)

end
end
