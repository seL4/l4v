(*
 * Copyright 2019, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory WPSimp
imports
  "WP"
  "WPC"
  "WPFix"
  "../../Simp_No_Conditional"
begin

(* Wrap up the standard usage pattern of wp/wpc/simp into its own command: *)
method wpsimp uses wp wp_del simp simp_del split split_del cong comb comb_del =
  ((determ \<open>wpfix | wp add: wp del: wp_del comb: comb comb del: comb_del | wpc |
            clarsimp_no_cond simp: simp simp del: simp_del split: split split del: split_del cong: cong |
            clarsimp simp: simp simp del: simp_del split: split split del: split_del cong: cong\<close>)+)[1]

end