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
imports
  "Monad_WP/wp/WP"
  Lib
  "ml-helpers/MLUtils"
keywords "crunch" "crunch_ignore" "crunches" :: thy_decl
begin

named_theorems "crunch_def"
named_theorems "crunch_rules"
named_theorems "crunch_param_rules"

ML_file "crunch-cmd.ML"
ML_file "Crunch.ML"

end
