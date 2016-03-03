(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory VMRights_A
imports
  "./$L4V_ARCH/ArchVMRights_A"

begin

context Arch begin

unqualify_types
  vm_rights

unqualify_consts
  valid_vm_rights :: "vm_rights set"
  validate_vm_rights :: "vm_rights \<Rightarrow> vm_rights"

end

end
