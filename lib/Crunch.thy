(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Crunch
imports "wp/NonDetMonadVCG"
keywords "crunch" "crunch_ignore" :: thy_decl
begin

ML_file "crunch-cmd.ML"
ML_file "Crunch.ML"

setup {*
  add_crunch_instance "" (CrunchValid.crunch_x, CrunchValid.crunch_ignore_add_del)
*}
setup {*
  add_crunch_instance "valid" (CrunchValid.crunch_x, CrunchValid.crunch_ignore_add_del)
*}
setup {*
  add_crunch_instance "no_fail" (CrunchNoFail.crunch_x, CrunchNoFail.crunch_ignore_add_del)
*}
setup {*
  add_crunch_instance "empty_fail" (CrunchEmptyFail.crunch_x, CrunchEmptyFail.crunch_ignore_add_del)
*}

setup CallCrunch.setup

end
