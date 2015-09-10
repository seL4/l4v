(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory ProofCountTest
imports Main ProofCount
begin


ML {* 
val _ =
  Outer_Syntax.command @{command_keyword "done"} "done proof"
    (Scan.succeed Isar_Cmd.done_proof);
*} 

end
