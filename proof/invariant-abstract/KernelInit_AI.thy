(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(* Kernel init refinement. Currently axiomatised.
*)

theory KernelInit_AI
imports
  "./$L4V_ARCH/ArchKernelInit_AI"
begin

axiomatization where
  akernel_init_invs: "\<forall>((tc,s),m,e) \<in> Init_A. invs s \<and> ct_running s"

end
