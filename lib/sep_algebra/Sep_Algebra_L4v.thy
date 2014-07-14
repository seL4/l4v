(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(* Title: interoperability between separation algebra theories and l4.verified
          theories
   Author: Rafal Kolanski <rafal.kolanski at nicta.com.au>, 2012
*)

theory Sep_Algebra_L4v
imports "Sep_Tactics"
begin

text {*
  Remove anything conflicting with @{text "pred_*"} in lib,
  e.g. @{text pred_and} vs @{text pred_conj} *}

no_notation pred_and (infixr "and" 35)
no_notation pred_or (infixr "or" 30)
no_notation pred_not ("not _" [40] 40)
no_notation pred_imp (infixr "imp" 25)

thm sep_cancel

end
