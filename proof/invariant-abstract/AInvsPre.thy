(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory AInvsPre
imports "./$L4V_ARCH/ArchVSpaceEntries_AI" ADT_AI
begin

locale AInvsPre =
  fixes state_ext_type1 :: "('a :: state_ext) itself"
  assumes ptable_rights_imp_frame:
    "\<And> (s :: 'a state) t x y. 
     valid_state s \<Longrightarrow> 
       ptable_rights t s x \<noteq> {} \<Longrightarrow>
       ptable_lift t s x = Some (addrFromPPtr y) \<Longrightarrow>
         in_user_frame y s \<or> in_device_frame y s"

definition
  "kernel_mappings \<equiv> {x. x \<ge> kernel_base}"

end
