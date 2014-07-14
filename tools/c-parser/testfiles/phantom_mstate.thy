(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory phantom_mstate
imports "../CTranslation"
begin

install_C_file "phantom_mstate.c" [machinety=bool]

context phantom_mstate
begin

  thm machine_proto_body_def
  thm proto2_body_def

  thm f_body_def
  thm g_body_def

  thm f_modifies
  thm g_modifies
  thm machine_proto_modifies
  thm proto2_modifies

  term phantom_machine_state_'
end

end
