(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory jiraver150
imports "CParser.CTranslation"
begin

external_file "jiraver150.c"

declare [[use_anonymous_local_variables=true]]
  install_C_file "jiraver150.c"

  context jiraver150
  begin

  ML \<open>@{const_name "unsigned_char'local0_'"}\<close>

  thm f_body_def
  thm f2_body_def
  thm g_body_def
  thm h_body_def

  lemma "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>unsigned'local0 :== CALL f(1) \<lbrace> \<acute>unsigned'local0 = 2 \<rbrace>"
  apply vcg
  apply (simp add: scast_id)
  done

  end

end
