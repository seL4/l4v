(*
 * Copyright 2017, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory attributes
  imports "../CTranslation"
begin

install_C_file "attributes.c"

ML \<open>
local
open ProgramAnalysis
in
fun global_details vi = (srcname vi, length (get_vi_attrs vi))

val all_global_details = get_globals #> map global_details
end
\<close>

ML \<open>
val results = CalculateState.get_csenv @{theory} "attributes.c"
  |> the
  |> all_global_details
  |> sort (prod_ord string_ord int_ord)
\<close>

ML \<open>
val _ = if results = [("u",1), ("v", 1)] then ()
        else error "Test case failure"
\<close>

end
