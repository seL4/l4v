(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
