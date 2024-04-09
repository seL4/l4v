(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* The base theory for generated bitfield proofs about the kernel *)

theory KernelState_C
imports
  "Word_Lib.WordSetup"
  "CLib.BitFieldProofsLib"
  "Substitute"
begin

type_synonym c_ptr_name = int
type_synonym 't c_com = "('t, c_ptr_name, strictc_errortype) com"
type_synonym 't c_body = "('t, c_ptr_name, strictc_errortype) body"
type_synonym 't c_xstate = "('t, strictc_errortype) xstate"

type_synonym cstate = "globals myvars"
type_synonym rf_com = "cstate c_com"

abbreviation
  "cslift (s :: cstate) \<equiv> clift (t_hrs_' (globals s))"

lemma cslift_def: "is_an_abbreviation" by (simp add: is_an_abbreviation_def)

(* Add an abbreviation for the common case of hrs_htd (t_hrs_' (globals s)) \<Turnstile>\<^sub>t p *)
abbreviation
  "c_h_t_valid" :: "cstate \<Rightarrow> 'a::c_type ptr \<Rightarrow> bool"  ("_ \<Turnstile>\<^sub>c _" [99,99] 100)
where
  "s \<Turnstile>\<^sub>c p == hrs_htd (t_hrs_' (globals s)),c_guard \<Turnstile>\<^sub>t p"

(* The HoarePartialDef theorems are used extensively
   (as opposed to their HoareTotalDef counterparts, which aren't used much).
   We can give most their long names, but conseqPre is used over 400 times,
   so for these cases we override the namespaces *)
lemmas conseqPre = HoarePartialDef.conseqPre
lemmas conseqPost = HoarePartialDef.conseqPost

(* Likewise, we'd prefer to get HOL.conj_cong over StateFun.conj_cong *)
lemmas conj_cong = HOL.conj_cong

(* Removes two rules that are too eager for the bitfield proofs. *)
declare bit_shiftr_eq[simp del]
declare shiftl_of_Suc[simp del]

end
