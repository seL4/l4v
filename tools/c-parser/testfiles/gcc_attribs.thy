(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory gcc_attribs
imports "../CTranslation"
begin

install_C_file "gcc_attribs.c"

context gcc_attribs
begin

  thm f_body_def
end

ML {*
  val SOME cse = CalculateState.get_csenv @{theory} "gcc_attribs.c"
  val spec1 = Symtab.lookup (ProgramAnalysis.function_specs cse) "myexit"
  val spec2 = Symtab.lookup (ProgramAnalysis.function_specs cse) "myexit2"
*}

end
