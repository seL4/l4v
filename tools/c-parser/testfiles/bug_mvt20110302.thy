(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory bug_mvt20110302
imports "CParser.CTranslation"
begin

external_file "bug_mvt20110302.c"
install_C_file "bug_mvt20110302.c"

context bug_mvt20110302
begin

  thm create_ipcbuf_frame_body_def
end

end
