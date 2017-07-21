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
Functions for fault handling.
*)

chapter {* arch fault related functions *}

theory ArchFault_A
imports "../Structures_A" "../Tcb_A"
begin

context Arch begin global_naming ARM_HYP_A

fun make_arch_fault_msg :: "arch_fault \<Rightarrow> obj_ref \<Rightarrow> (data \<times> data list,'z::state_ext) s_monad"
where
  "make_arch_fault_msg (VMFault vptr archData) thread = do
     pc \<leftarrow> as_user thread getRestartPC;
     upc \<leftarrow> do_machine_op (addressTranslateS1CPR pc);
     return (5, (upc && ~~ mask pageBits || pc && mask pageBits) # vptr # archData) od"
| "make_arch_fault_msg (VCPUFault hsr) thread = return (7, [hsr])"
| "make_arch_fault_msg (VGICMaintenance archData) thread = do
      msg \<leftarrow> return $ (case archData of None \<Rightarrow> [-1] | Some idx \<Rightarrow> [idx]);
      return (6, msg)
   od"

definition
  handle_arch_fault_reply :: "arch_fault \<Rightarrow> obj_ref \<Rightarrow> data \<Rightarrow> data list \<Rightarrow> (bool,'z::state_ext) s_monad"
where
  "handle_arch_fault_reply af thread x y = return True"


end

end
