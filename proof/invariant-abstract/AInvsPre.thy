(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory AInvsPre
imports ArchVSpaceEntries_AI ADT_AI
begin

locale AInvsPre =
  fixes state_ext_type1 :: "('a :: state_ext) itself"
  assumes ptable_rights_imp_frame:
    "\<And> (s :: 'a state) t x y.
     valid_state s \<Longrightarrow>
       ptable_rights t s x \<noteq> {} \<Longrightarrow>
       ptable_lift t s x = Some (addrFromPPtr y) \<Longrightarrow>
         in_user_frame y s \<or> in_device_frame y s"

end
