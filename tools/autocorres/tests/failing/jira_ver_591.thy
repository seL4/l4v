(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(*
 * Test for Jira issue VER-591. See the C file for more details.
 *)
theory jira_ver_591 imports "../../AutoCorres" begin

install_C_file "jira_ver_591.c"

(* This fails *)
autocorres "jira_ver_591.c"

autocorres [keep_going] "jira_ver_591.c"

end
