(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory ProofCountTest
imports Main ProofCount
begin


ML \<open>
val _ =
  Outer_Syntax.command @{command_keyword "done"} "done proof"
    (Scan.succeed Isar_Cmd.done_proof);
\<close>

end
