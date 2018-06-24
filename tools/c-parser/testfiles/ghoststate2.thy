(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory ghoststate2
imports "CParser.CTranslation"
begin

(*
ML {*
IsarInstall.install_C_file ((((NONE, NONE), NONE), "ghoststate2.c"),
  SOME [(IsarInstall.GhostState, "nat")]) @{theory}
  handle TYPE(msg, tys, tms) =>
    (Pretty.writeln
      (Pretty.block (Pretty.commas (map (Syntax.pretty_term @{context}) tms)));
     @{theory})
*}
*)

external_file "ghoststate2.c"
install_C_file "ghoststate2.c" [ghostty="nat"]

context ghoststate2
begin

thm f_body_def
thm f_modifies

end (* context *)

end (* theory *)
