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

chapter "ARM Object Invocations"

theory ArchInvocation_A
imports "../Structures_A"
begin

context Arch begin global_naming ARM_A

text {* Message infos are encoded to or decoded from a data word. *}
primrec
  message_info_to_data :: "message_info \<Rightarrow> data"
where
  "message_info_to_data (MI ln exc unw mlabel) =
   (let
        extra = exc << 7;
        unwrapped = unw << 9;
        label = mlabel << 12
    in
       label || extra || unwrapped || ln)"

text {* Hard-coded to avoid recursive imports? *}
definition
  data_to_message_info :: "data \<Rightarrow> message_info"
where
  "data_to_message_info w \<equiv>
   MI (let v = w && ((1 << 7) - 1) in if v > 120 then 120 else v) ((w >> 7) && ((1 << 2) - 1))
      ((w >> 9) && ((1 << 3) - 1)) (w >> 12)"


text {* These datatypes encode the arguments to the various possible
ARM-specific system calls. Selectors are defined for various fields
for convenience elsewhere. *}

datatype flush_type = Clean | Invalidate | CleanInvalidate | Unify

datatype page_directory_invocation =
    PageDirectoryFlush (pd_flush_type: flush_type) (pd_flush_start: vspace_ref)
                       (pd_flush_end: vspace_ref) (pd_flush_pstart: word32)
                       (pd_flush_pd: obj_ref) (pd_flush_asid: asid)
  | PageDirectoryNothing

datatype page_table_invocation = 
    PageTableMap cap cslot_ptr pde obj_ref
  | PageTableUnmap cap cslot_ptr

datatype asid_control_invocation = 
    MakePool obj_ref cslot_ptr cslot_ptr asid

datatype asid_pool_invocation = 
    Assign asid obj_ref cslot_ptr

datatype page_invocation
     = PageMap 
         (page_map_asid: asid)
         (page_map_cap: cap)
         (page_map_ct_slot: cslot_ptr)
         (page_map_entries: "pte \<times> (obj_ref list) + pde \<times> (obj_ref list)")
     | PageRemap
         (page_remap_asid: asid)
         (page_remap_entries: "pte \<times> (obj_ref list) + pde \<times> (obj_ref list)")
     | PageUnmap 
         (page_unmap_cap: arch_cap)
         (page_unmap_cap_slot: cslot_ptr)
     | PageFlush
         (page_flush_type: flush_type)
         (page_flush_start: vspace_ref)
         (page_flush_end: vspace_ref)
         (page_flush_pstart: word32)
         (page_flush_pd: obj_ref)
         (page_flush_asid: asid)
     | PageGetAddr
         (page_get_paddr: obj_ref)

datatype arch_invocation
     = InvokePageTable page_table_invocation
     | InvokePageDirectory page_directory_invocation
     | InvokePage page_invocation
     | InvokeASIDControl asid_control_invocation
     | InvokeASIDPool asid_pool_invocation

datatype arch_copy_register_sets =
    ArchDefaultExtraRegisters

-- "There are no additional interrupt control operations on ARM."
typedecl arch_irq_control_invocation

end

end
