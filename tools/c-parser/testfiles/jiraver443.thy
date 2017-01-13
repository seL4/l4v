(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory jiraver443
  imports "../CTranslation"
begin

  declare [[allow_underscore_idents=true]]
  (* 3014 lines, with  78 globals:  works ;
     3498 lines, with  96 globals:  works ;
     3719 lines, with 108 globals:  fails
     3719 lines, (down to _camkes_call_tls_var_to_465_2),
      with following functions removed:
         get__camkes_call_tls_var_to_465
         get_echo_int_4_l_to
                                    fails
  *)
  install_C_file "jiraver443.c"

  context jiraver443
  begin
    thm get__camkes_ret_tls_var_from_244_body_def
    (* observe the UnspecifiedSyntax issue in seL4_Send, if you so desire *)
    thm seL4_Send_body_def
  end

end
