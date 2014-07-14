(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(* General lemmas removed from KernelInit *)

theory InitLemmas
imports IncKernelInit
begin

(* Annotation added by Simon Winwood (Thu Jul  1 20:27:09 2010) using taint-mode *)
declare headM_tailM_Cons[simp]

(* Annotation added by Simon Winwood (Thu Jul  1 20:15:55 2010) using taint-mode *)
declare cart_singletons[simp]

declare  less_1_simp[simp]

declare  is_aligned_no_overflow[simp]

lemma dmo_valid_cap'[wp]:
  "\<lbrace>valid_cap' cap\<rbrace> doMachineOp mop \<lbrace>\<lambda>rv. valid_cap' cap\<rbrace>"
  by (simp add: doMachineOp_def split_def | wp select_wp)+

lemma dmo_norq[wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueues s)\<rbrace> doMachineOp mop \<lbrace>\<lambda>rv s. P (ksReadyQueues s)\<rbrace>"
  by (simp add: doMachineOp_def split_def | wp select_wp)+

(* Annotation added by Simon Winwood (Thu Jul  1 20:35:09 2010) using taint-mode *)
declare unless_True[simp]

(* Annotation added by Simon Winwood (Thu Jul  1 20:35:07 2010) using taint-mode *)
declare unless_False[simp]

(* Annotation added by Simon Winwood (Thu Jul  1 20:27:45 2010) using taint-mode *)
declare maybe_fail_bind_fail[simp]

crunch cte_wp_at'[wp]: setPriority "cte_wp_at' P p" (simp: crunch_simps)
crunch irq_node'[wp]: setPriority "\<lambda>s. P (irq_node' s)" (simp: crunch_simps)

end
