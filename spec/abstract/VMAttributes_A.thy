(*
 * Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Abstract model of VM attributes. *)

theory VMAttributes_A
imports
  ArchVMAttributes_A
begin

arch_requalify_types (A)
  vm_attribute arch_raw_vmattrs

arch_requalify_consts (A)
  attribs_from_word
  attribs_to_word
  validate_vm_attributes
  validate_pt_vm_attributes
  default_vmattrs

arch_requalify_facts (A)
  validate_vm_attributes_def
  validate_pt_vm_attributes_def

end
