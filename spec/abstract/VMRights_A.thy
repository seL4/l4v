(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Virtual-Memory Rights"

theory VMRights_A
imports CapRights_A
begin

text \<open>
This theory provides architecture-specific definitions and datatypes for virtual-memory support.
\<close>

text \<open>Page access rights.\<close>

type_synonym vm_rights = cap_rights

definition vm_kernel_only :: vm_rights
where
  "vm_kernel_only \<equiv> {}"

definition vm_read_only :: vm_rights
where
  "vm_read_only \<equiv> {AllowRead}"

definition vm_read_write :: vm_rights
where
  "vm_read_write \<equiv> {AllowRead,AllowWrite}"

text \<open>
  Note that only the above combinations of virtual-memory rights are permitted.
  We introduce the following definitions to reflect this fact:
  The predicate @{text valid_vm_rights} holds iff a given set of rights is valid
  (i.e., a permitted combination).
  The function @{text validate_vm_rights} takes an arbitrary set of rights and
  returns the largest permitted subset.
\<close>
definition valid_vm_rights :: "vm_rights set"
where
  "valid_vm_rights \<equiv> {vm_read_write, vm_read_only, vm_kernel_only}"

definition validate_vm_rights :: "vm_rights \<Rightarrow> vm_rights"
where
  "validate_vm_rights rs \<equiv>
     if AllowRead \<in> rs
     then if AllowWrite \<in> rs then vm_read_write else vm_read_only
     else vm_kernel_only"

text \<open>On the abstract level, capability and VM rights share the same type.
  Nevertheless, a simple set intersection might lead to an invalid value like
  @{term "{AllowWrite}"}.  Hence, @{const validate_vm_rights}.\<close>
definition mask_vm_rights :: "vm_rights \<Rightarrow> cap_rights \<Rightarrow> vm_rights"
where
  "mask_vm_rights V R \<equiv> validate_vm_rights (V \<inter> R)"

end
