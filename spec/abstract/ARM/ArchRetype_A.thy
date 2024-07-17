(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Retyping and untyped invocation
*)

chapter "Retyping and Untyped Invocations"

theory ArchRetype_A
imports
  ArchVSpaceAcc_A
  ArchInvocation_A
begin

context Arch begin arch_global_naming (A)

text \<open>This is a placeholder function. We may wish to extend the specification
  with explicitly tagging kernel data regions in memory.\<close>
definition
  reserve_region :: "obj_ref \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "reserve_region ptr byteLength is_kernel \<equiv> return ()"

text \<open>Initialise architecture-specific objects.\<close>

definition vs_apiobj_size where
  "vs_apiobj_size ty \<equiv>
     case ty of
       ArchObject SmallPageObj \<Rightarrow> pageBitsForSize ARMSmallPage
     | ArchObject LargePageObj \<Rightarrow> pageBitsForSize ARMLargePage
     | ArchObject SectionObj \<Rightarrow> pageBitsForSize ARMSection
     | ArchObject SuperSectionObj \<Rightarrow> pageBitsForSize ARMSuperSection
     | ArchObject PageTableObj \<Rightarrow> pt_bits
     | ArchObject PageDirectoryObj \<Rightarrow> pd_bits"

definition init_arch_objects ::
  "apiobject_type \<Rightarrow> bool \<Rightarrow> obj_ref \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> obj_ref list \<Rightarrow> (unit,'z::state_ext) s_monad"
  where
  "init_arch_objects new_type is_device ptr num_objects obj_sz refs \<equiv> do
     when (new_type = ArchObject PageDirectoryObj) $ mapM_x copy_global_mappings refs;
     if \<not>is_device \<and>
        new_type \<in> {ArchObject SmallPageObj, ArchObject LargePageObj,
                    ArchObject SectionObj, ArchObject SuperSectionObj}
     then
       mapM_x (\<lambda>ref. do_machine_op $
                       cleanCacheRange_RAM ref (ref + mask (vs_apiobj_size new_type))
                                           (addrFromPPtr ref))
              refs
     else if new_type \<in> {ArchObject PageTableObj, ArchObject PageDirectoryObj}
     then
       mapM_x (\<lambda>ref. do_machine_op $
                       cleanCacheRange_PoU ref (ref + mask (vs_apiobj_size new_type))
                                           (addrFromPPtr ref))
              refs
     else
       return ()
   od"

definition
  empty_context :: user_context where
  "empty_context \<equiv> UserContext (\<lambda>_. 0)"

definition init_arch_tcb :: arch_tcb where
  "init_arch_tcb \<equiv> \<lparr> tcb_context = empty_context \<rparr>"


end

end
