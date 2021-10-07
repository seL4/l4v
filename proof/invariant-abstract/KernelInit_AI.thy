(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Kernel init refinement. Currently axiomatised.
*)

theory KernelInit_AI
imports
  ArchKernelInit_AI
begin

axiomatization where
  akernel_init_invs: "\<forall>((tc,s),m,e) \<in> Init_A. invs s \<and> ct_running s"

end
