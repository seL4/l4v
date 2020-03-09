(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver313
  imports "CParser.CTranslation"
begin

ML \<open>Feedback.verbosity_level := 6\<close>

declare [[calculate_modifies_proofs = false ]]

external_file "jiraver313.c"
install_C_file memsafe "jiraver313.c"

ML \<open>
local
open Absyn
val cpp_record =
    {cpp_path = SOME "/usr/bin/cpp", error_detail = 10}
val (decls, _) =
  StrictCParser.parse (IsarInstall.do_cpp cpp_record) 15 []
    (IsarInstall.mk_thy_relative @{theory} "jiraver313.c");
in
val Decl d = hd decls
val VarDecl vd = RegionExtras.node d
end
\<close>

context jiraver313
begin
term foo
term bar
thm f_body_def
thm g_body_def

end

end
