(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "ARM-Specific TCB and thread related specifications"

theory ArchKHeap_A
imports "../KHeap_A"
begin

context Arch begin global_naming ARM_A

section "User Context"

text {*
  Changes user context of specified thread by running
  specified user monad.
*}
definition
  as_user :: "obj_ref \<Rightarrow> 'a user_monad \<Rightarrow> ('a,'z::state_ext) s_monad"
where
  "as_user tptr f \<equiv> do
    tcb \<leftarrow> gets_the $ get_tcb tptr;
    uc \<leftarrow> return $ tcb_context (tcb_arch tcb);
    (a, uc') \<leftarrow> select_f $ f uc;
    new_tcb \<leftarrow> return $ tcb \<lparr> tcb_arch := (tcb_arch tcb)\<lparr> tcb_context := uc' \<rparr> \<rparr>;
    set_object tptr (TCB new_tcb);
    return a
  od"

end

end
