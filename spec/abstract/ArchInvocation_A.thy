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
Arch specific object invocations
*)

header "ARM Object Invocations"

theory ArchInvocation_A
imports Structures_A
begin

text {* These datatypes encode the arguments to the various possible
ARM-specific system calls. Accessors are defined for various fields
for convenience elsewhere. *}

datatype flush_type = Clean | Invalidate | CleanInvalidate | Unify

datatype page_directory_invocation =
    PageDirectoryFlush flush_type vspace_ref vspace_ref word32 obj_ref asid
  | PageDirectoryNothing

primrec
  pd_flush_type :: "page_directory_invocation \<Rightarrow> flush_type"
where
  "pd_flush_type (PageDirectoryFlush typ start end pstart pd asid) = typ"

primrec
  pd_flush_start :: "page_directory_invocation \<Rightarrow> vspace_ref"
where
  "pd_flush_start (PageDirectoryFlush typ start end pstart pd asid) = start"

primrec
  pd_flush_end :: "page_directory_invocation \<Rightarrow> vspace_ref"
where
  "pd_flush_end (PageDirectoryFlush typ start end pstart pd asid) = end"

primrec
  pd_flush_pstart :: "page_directory_invocation \<Rightarrow> word32"
where
  "pd_flush_pstart (PageDirectoryFlush typ start end pstart pd asid) = pstart"

primrec
  pd_flush_pd :: "page_directory_invocation \<Rightarrow> obj_ref"
where
  "pd_flush_pd (PageDirectoryFlush typ start end pstart pd asid) = pd"

primrec
  pd_flush_asid :: "page_directory_invocation \<Rightarrow> asid"
where
  "pd_flush_asid (PageDirectoryFlush typ start end pstart pd asid) = asid"

datatype page_table_invocation = 
    PageTableMap cap cslot_ptr pde obj_ref
  | PageTableUnmap cap cslot_ptr

datatype asid_control_invocation = 
    MakePool obj_ref cslot_ptr cslot_ptr asid

datatype asid_pool_invocation = 
    Assign asid obj_ref cslot_ptr

datatype page_invocation
     = PageMap 
         cap
         cslot_ptr
         "pte \<times> (obj_ref list) + pde \<times> (obj_ref list)"
     | PageRemap 
         "pte \<times> (obj_ref list) + pde \<times> (obj_ref list)"
     | PageUnmap 
         arch_cap
         cslot_ptr
     | PageFlush
         flush_type
         vspace_ref
         vspace_ref
         word32
         obj_ref
         asid

primrec
  page_map_cap :: "page_invocation \<Rightarrow> cap"
where
  "page_map_cap (PageMap c p x) = c"
primrec
  page_map_ct_slot :: "page_invocation \<Rightarrow> cslot_ptr"
where
  "page_map_ct_slot (PageMap c p x) = p"
primrec
  page_map_entries :: "page_invocation \<Rightarrow> pte \<times> (obj_ref list) + pde \<times> (obj_ref list)"
where
  "page_map_entries (PageMap c p x) = x"

primrec
  page_remap_entries :: "page_invocation \<Rightarrow> pte \<times> (obj_ref list) + pde \<times> (obj_ref list)"
where
  "page_remap_entries (PageRemap x) = x"

primrec
  page_unmap_cap :: "page_invocation \<Rightarrow> arch_cap"
where
  "page_unmap_cap (PageUnmap c p) = c"

primrec
  page_unmap_cap_slot :: "page_invocation \<Rightarrow> cslot_ptr"
where
  "page_unmap_cap_slot (PageUnmap c p) = p"

primrec
  page_flush_pd :: "page_invocation \<Rightarrow> obj_ref"
where
  "page_flush_pd (PageFlush typ start end pstart pd asid) = pd"

primrec
  page_flush_asid :: "page_invocation \<Rightarrow> asid"
where
  "page_flush_asid (PageFlush typ start end pstart pd asid) = asid"

primrec
  page_flush_type :: "page_invocation \<Rightarrow> flush_type"
where
  "page_flush_type (PageFlush typ start end pstart pd asid) = typ"

primrec
  page_flush_start :: "page_invocation \<Rightarrow> vspace_ref"
where
  "page_flush_start (PageFlush typ start end pstart pd asid) = start"

primrec
  page_flush_end :: "page_invocation \<Rightarrow> vspace_ref"
where
  "page_flush_end (PageFlush typ start end pstart pd asid) = end"

primrec
  page_flush_pstart :: "page_invocation \<Rightarrow> word32"
where
  "page_flush_pstart (PageFlush typ start end pstart pd asid) = pstart"

datatype arch_invocation
     = InvokePageTable page_table_invocation
     | InvokePageDirectory page_directory_invocation
     | InvokePage page_invocation
     | InvokeASIDControl asid_control_invocation
     | InvokeASIDPool asid_pool_invocation

(* There are no additional interrupt control operations on ARM. *)
typedecl arch_interrupt_control

end
