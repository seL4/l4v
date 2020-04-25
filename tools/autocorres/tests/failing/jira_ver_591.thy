(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Test for Jira issue VER-591. See the C file for more details.
 *)
theory jira_ver_591 imports "AutoCorres.AutoCorres" begin

external_file "jira_ver_591.c"
install_C_file "jira_ver_591.c"

(* This fails *)
autocorres "jira_ver_591.c"

autocorres [keep_going] "jira_ver_591.c"

end
