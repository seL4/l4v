(*
 * Copyright 2025, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchMultikernel_C
imports Substitute
begin

(* There is no physBase on x64, but we still want the top-level of \<Gamma> to be a function update.
   The function also must mention cpuNum, otherwise \<Gamma> will not depend on cpuNum outside the
   locale, which means its type would not line up with \<Gamma> in other architectures and generic
   proofs would fail. The following dummy definition is used below to achieve the
   cpuNum-dependent function update. *)
definition
  "addrFromKPPtr_body' n \<equiv> kernel_all_global_addresses.addrFromKPPtr_body"


locale kernel_all_substitute = kernel_all_substitute0 +
  fixes cpuNum :: nat
begin

definition
  "\<Gamma> \<equiv> \<Gamma>0 (addrFromKPPtr_'proc \<mapsto> addrFromKPPtr_body' cpuNum)"

(* Provide implementation theorem expected by vcg. Other *_impl theorems will be
   generated automatically in Multikernel_C.thy *)
lemma addrFromKPPtr_impl:
  "\<Gamma> addrFromKPPtr_'proc = Some addrFromKPPtr_body"
  by (simp add: \<Gamma>_def addrFromKPPtr_body'_def)

end

(* Do the same for kernel_all_global_addresses *)
locale kernel_all_multi = kernel_all_global_addresses +
  fixes cpuNum :: nat
begin

definition
  "\<Gamma> \<equiv> \<Gamma>0 (addrFromKPPtr_'proc \<mapsto> addrFromKPPtr_body' cpuNum)"

lemma addrFromKPPtr_impl:
  "\<Gamma> addrFromKPPtr_'proc = Some addrFromKPPtr_body"
  by (simp add: \<Gamma>_def addrFromKPPtr_body'_def)

end

(* Interface to generic proof procedures in Multikernel_C.thy *)
ML \<open>
  val special_proc_name = "addrFromKPPtr"
\<close>

end
