(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
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
