(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory CodeArbitrary imports
  Lib
begin

(* Stop the code generator looking inside arbitrary. If the generator looks
 * inside arbitrary, it finds undefined that is marked code_abort and prevents
 * it making any further progress.
 *)
code_const arbitrary
  (SML "!(raise/ Fail/ \"undefined\")")
  (OCaml "failwith/ \"undefined\"")
  (Haskell "error/ \"undefined\"")

end
