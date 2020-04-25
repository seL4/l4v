(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver456
  imports "CParser.CTranslation"

begin

external_file "jiraver456.c"
install_C_file "jiraver456.c"

context jiraver456
begin

thm f0_body_def
thm f1_body_def
thm f2_body_def

ML \<open>

fun count c th =
let
  val t = Thm.concl_of th
  fun incifGuard t i = if t = c then i + 1 else i
in
  fold_aterms incifGuard t 0
end
val f = count @{const Div_0};

   (f @{thm f1_body_def} = 1 andalso f @{thm f2_body_def} = 1 andalso f @{thm f0_body_def} = 1)
   orelse
   OS.Process.exit OS.Process.failure
\<close>


end

end
