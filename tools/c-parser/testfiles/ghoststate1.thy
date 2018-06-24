(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory ghoststate1
imports "CParser.CTranslation"
begin

external_file "simple_annotated_fn.c"
install_C_file "simple_annotated_fn.c" [ghostty="nat \<Rightarrow> nat"]

(* demonstrates existence of ghost'state global variable of appropriate type *)
term "\<acute>ghost'state :== (\<lambda>x. x + (1::nat))"

end
