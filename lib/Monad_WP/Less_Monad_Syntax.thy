(*
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory Less_Monad_Syntax (* use instead of HOL-Library.Monad_Syntax *)
  imports "HOL-Library.Monad_Syntax"
begin

(* remove >> from Monad_Syntax, clashes with word shift *)
no_syntax
  "_thenM" :: "['a, 'b] \<Rightarrow> 'c" (infixr ">>" 54)

(* remove input version of >>= from Monad_Syntax, avoid clash with NonDetMonad *)
no_notation
  Monad_Syntax.bind (infixr ">>=" 54)

(* use ASCII >>= instead of \<bind> *)
notation (output)
  bind_do (infixr ">>=" 54)

(* enable pretty printing for do { .. } syntax globally *)
translations
  "CONST bind_do" <= "CONST bind"

end
