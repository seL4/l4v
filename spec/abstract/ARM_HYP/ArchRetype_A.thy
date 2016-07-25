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
Retyping and untyped invocation
*)

chapter "Retyping and Untyped Invocations"

theory ArchRetype_A
imports
  ArchVSpaceAcc_A
  ArchInvocation_A
  VCPU_A
begin

context Arch begin global_naming ARM_A

text {* This is a placeholder function. We may wish to extend the specification
  with explicitly tagging kernel data regions in memory. *}
definition
  reserve_region :: "obj_ref \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "reserve_region ptr byteLength is_kernel \<equiv> return ()"

text {* Create 4096-byte frame objects that can be mapped into memory. These must be
cleared to prevent past contents being revealed. *}

definition
  create_word_objects :: "word32 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "create_word_objects ptr numObjects sz \<equiv>
  do
    byteLength \<leftarrow> return $ numObjects * 2 ^ sz;
    reserve_region ptr byteLength True;
    rst \<leftarrow>  return (map (\<lambda> n. (ptr + (n << sz))) [0  .e.  (of_nat numObjects) - 1]);
    do_machine_op $ mapM_x (\<lambda>x. clearMemory x (2 ^ sz)) rst
 od"

text {* Initialise architecture-specific objects. *}

definition
  init_arch_objects :: "apiobject_type \<Rightarrow> obj_ref \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> obj_ref list \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "init_arch_objects new_type ptr num_objects obj_sz refs \<equiv> case new_type of
    ArchObject SmallPageObj \<Rightarrow> create_word_objects ptr num_objects 12
  | ArchObject LargePageObj \<Rightarrow> create_word_objects ptr num_objects 16
  | ArchObject SectionObj \<Rightarrow> create_word_objects ptr num_objects 20
  | ArchObject SuperSectionObj \<Rightarrow> create_word_objects ptr num_objects 24
  | ArchObject PageTableObj \<Rightarrow>
      do_machine_op $ mapM_x (\<lambda>x. cleanCacheRange_PoU x (x + ((1::word32) << pt_bits) - 1)
                                                      (addrFromPPtr x)) refs
  | ArchObject PageDirectoryObj \<Rightarrow> do
      mapM_x copy_global_mappings refs;
      do_machine_op $ mapM_x (\<lambda>x. cleanCacheRange_PoU x (x + ((1::word32) << pd_bits) - 1)
                                                      (addrFromPPtr x)) refs
    od
  | _ \<Rightarrow> return ()"

definition
  empty_context :: user_context where
  "empty_context \<equiv> \<lambda>_. 0"

definition init_arch_tcb :: arch_tcb where
  "init_arch_tcb \<equiv> \<lparr> tcb_context = empty_context, tcb_vcpu = None \<rparr>"

end

end
