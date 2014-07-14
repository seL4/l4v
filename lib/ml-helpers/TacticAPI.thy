(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory TacticAPI
imports Main
begin

ML_file "tactic_api.ML"

setup {*
  TacticAPI.tactic_antiquotation_setup
*}

end
