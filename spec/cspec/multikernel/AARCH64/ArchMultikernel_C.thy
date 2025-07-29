(*
 * Copyright 2025, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchMultikernel_C
imports Substitute
begin

(* Example definition for how physBase could vary in a multikernel.
   To be generated from config eventually *)
definition ph_base :: "nat \<Rightarrow> 32 word" where
  "ph_base n = 0x80000000 + 0x00010000 * of_nat n"

(* Procedure body that depends on an additional logical parameter *)
definition
  "physBase_of_cpu n \<equiv> TRY
    creturn global_exn_var_'_update ret__unsigned_long_'_update (\<lambda>s. UCAST(32 \<rightarrow> 64) (ph_base n));;
    Guard DontReach {} SKIP
  CATCH SKIP
  END"

locale kernel_all_substitute = kernel_all_substitute0 +
  fixes cpuNum :: nat
begin

(* Override procedure environment from kernel source to get paramteric behaviour *)
definition
  "\<Gamma> \<equiv> \<Gamma>0 (physBase_'proc \<mapsto> physBase_of_cpu cpuNum)"

(* Provide physBase implementation theorem expected by vcg. Other *_impl theorems will be
   generated automatically in Multikernel_C.thy *)
lemma physBase_impl:
  "\<Gamma> physBase_'proc = Some (physBase_of_cpu cpuNum)"
  by (simp add: \<Gamma>_def)

(* vcg and similar tools expect physBase_body_def to unfold to a SIMPL command *)
lemmas physBase_body_def = physBase_of_cpu_def

end

(* Do the same for kernel_all_global_addresses *)
locale kernel_all_multi = kernel_all_global_addresses +
  fixes cpuNum :: nat
begin

definition
  "\<Gamma> \<equiv> \<Gamma>0 (physBase_'proc \<mapsto> physBase_of_cpu cpuNum)"

lemma physBase_impl:
  "\<Gamma> physBase_'proc = Some (physBase_of_cpu cpuNum)"
  by (simp add: \<Gamma>_def)

lemmas physBase_body_def = physBase_of_cpu_def

end

(* Interface to generic proof procedures in Multikernel_C.thy *)
ML \<open>
  val special_proc_name = "physBase"
\<close>

end
