(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory WPSimp
imports
  "WP"
  "WPC"
  "WPFix"
  Eisbach_Tools.Simp_No_Conditional
begin

(* Wrap up the standard usage pattern of wp/wpc/simp into its own command: *)
method wpsimp uses wp wp_del simp simp_del split split_del cong comb comb_del =
  ((determ \<open>wpfix | wp add: wp del: wp_del comb: comb comb del: comb_del | wpc |
            clarsimp_no_cond simp: simp simp del: simp_del split: split split del: split_del cong: cong |
            clarsimp simp: simp simp del: simp_del split: split split del: split_del cong: cong\<close>)+)[1]

end