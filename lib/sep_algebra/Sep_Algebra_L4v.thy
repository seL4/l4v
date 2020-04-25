(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Title: interoperability between separation algebra theories and l4.verified
          theories
   Author: Rafal Kolanski <rafal.kolanski at nicta.com.au>, 2012
*)

theory Sep_Algebra_L4v
imports "Sep_Tactics" "Sep_Fold"
begin

text \<open>
  Remove anything conflicting with @{text "pred_*"} in lib,
  e.g. @{text pred_and} vs @{text pred_conj}\<close>

no_notation pred_and (infixr "and" 35)
no_notation pred_or (infixr "or" 30)
no_notation pred_not ("not _" [40] 40)
no_notation pred_imp (infixr "imp" 25)

end
