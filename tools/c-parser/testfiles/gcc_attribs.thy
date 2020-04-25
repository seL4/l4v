(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory gcc_attribs
imports "CParser.CTranslation"
begin

external_file "gcc_attribs.c"
install_C_file "gcc_attribs.c"

context gcc_attribs
begin

  thm f_body_def
end

ML \<open>
  val SOME cse = CalculateState.get_csenv @{theory} "gcc_attribs.c"
  val spec1 = Symtab.lookup (ProgramAnalysis.function_specs cse) "myexit"
  val spec2 = Symtab.lookup (ProgramAnalysis.function_specs cse) "myexit2"
\<close>

end
