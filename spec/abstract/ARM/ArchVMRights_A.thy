(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "ARM-Specific Virtual-Memory Rights"

theory ArchVMRights_A
imports "../CapRights_A" "../../machine/ARM/Setup_Locale"
begin

context Arch begin global_naming ARM_A

text {*
This theory provides architecture-specific definitions and datatypes
for virtual-memory support.
*}

section {* Architecture-specific virtual memory *}

text {* Page access rights. *}

type_synonym vm_rights = cap_rights

definition
  vm_kernel_only :: vm_rights where
  "vm_kernel_only \<equiv> {}" 
definition
  vm_read_only :: vm_rights where
  "vm_read_only \<equiv> {AllowRead}"
definition
  vm_read_write :: vm_rights where
  "vm_read_write \<equiv> {AllowRead,AllowWrite}"

text {*
  Note that only the above combinations of virtual-memory rights are permitted.
  We introduce the following definitions to reflect this fact:
  The predicate @{text valid_vm_rights} holds iff a given set of rights is valid
  (i.e., a permitted combination).
  The function @{text validate_vm_rights} takes an arbitrary set of rights and
  returns the largest permitted subset.
*}
definition
  "valid_vm_rights \<equiv> {vm_read_write, vm_read_only, vm_kernel_only}"
definition
  "validate_vm_rights rs \<equiv>
   (if AllowRead \<in> rs
     then (if AllowWrite \<in> rs then vm_read_write else vm_read_only)
   else vm_kernel_only)"

end

end
