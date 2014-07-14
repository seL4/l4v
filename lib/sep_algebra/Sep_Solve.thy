(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Sep_Solve
imports Sep_Cancel Sep_MP
begin

thm sep_conj_sep_impl

ML {*
    fun sep_schem ctxt = rotator' ctxt sep_asm_erule_select
     (SOLVED' ( (etac @{thm sep_conj_sep_impl2} THEN'
     (FIRST' [atac, rtac @{thm TrueI}, sep_cancel_tactic' ctxt true] |> REPEAT_ALL_NEW)) ))
    
    fun sep_solve_tactic ctxt  = 
      let val truei = rtac @{thm TrueI}
          fun sep_cancel_rotating i = sep_select_tactic sep_asm_select [1] ctxt i THEN_ELSE
                                    (rotator' ctxt sep_asm_select (FIRST' [atac, truei,  sep_cancel_tactic' ctxt false, etac @{thm sep_conj_sep_impl}] |> REPEAT_ALL_NEW |> SOLVED' ) i, 
                                     SOLVED' (FIRST' [atac, truei,  sep_cancel_tactic' ctxt false, etac @{thm sep_conj_sep_impl}] |> REPEAT_ALL_NEW) i)
          val sep_cancel_tac = (FIRST' [atac, truei,  sep_cancel_tactic' ctxt false, etac  @{thm sep_conj_sep_impl}] |> REPEAT_ALL_NEW)
      in   (DETERM o SOLVED' (FIRST' [atac,truei, sep_cancel_tac])) ORELSE'          
           (SOLVED' (((TRY o CHANGED_PROP o (sep_mp_solver ctxt)) THEN_ALL_NEW  sep_cancel_rotating) )) |> SOLVED'
      end;

   fun sep_solve_method _ ctxt = SIMPLE_METHOD' ( sep_solve_tactic ctxt )
   fun sep_schem_method _ ctxt = SIMPLE_METHOD' ( sep_schem ctxt )

*}

method_setup sep_solve = {*
  sep_cancel_syntax >> sep_solve_method
*}

method_setup sep_schem = {*
  sep_cancel_syntax >> sep_schem_method
*}
 



end
