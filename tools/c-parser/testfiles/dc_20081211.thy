(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory dc_20081211
imports "CParser.CTranslation"
begin

external_file "dc_20081211.c"
install_C_file "dc_20081211.c"

declare [[show_types]]

context dc_20081211_global_addresses
begin

thm \<Gamma>_def

end

context setHardwareASID_modifies
begin

thm \<Gamma>_def
thm setHardwareASID_modifies

end

context dc_20081211 begin

term "\<Gamma>"
thm setHardwareASID_modifies
thm test_body_def
thm test_modifies


lemma test_modifies:
  "\<forall>s. \<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> {s} Call
  test_'proc {t. t may_only_modify_globals s in [x]}"
  (* fails: apply(vcg spec=modifies)
     perhaps because there already is a test_modifies already in
     scope *)
  oops

end

end
