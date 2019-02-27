(*
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory jiraver881

imports "CParser.CTranslation"

begin

external_file "jiraver881.c"
install_C_file "jiraver881.c"

context jiraver881 begin

(* note that x is assigned directly from f(),
   but that compound lvars and y (different notional type) are
   assigned via explicit statements. *)

thm baseline1_body_def
thm baseline2_body_def

thm test1_body_def
thm test2_body_def
thm test3_body_def
thm test4_body_def
thm test5_body_def

(* We expect the call to store the int retvals into ret__int and similar.
   To test this, we pass the updater of the expected variable as the "upd" argument. *)
ML \<open>
fun check_ret func upd =
let val fn_def = Proof_Context.get_thm @{context} (func ^ "_body_def")
in
  assert
    (exists_Const (fn (name, _) => name = upd)
       (term_of_thm fn_def))
    ("assert failed: jiraver881 test for " ^ func ^ " call")
end
\<close>

(* Should always work, since these are trivial assignments *)
ML \<open>
check_ret "baseline1" @{const_name x___int_'_update};
check_ret "baseline2" @{const_name ret__int_'_update};
\<close>

(* Actual tests *)
ML \<open>
check_ret "test1" @{const_name ret__int_'_update};
check_ret "test2" @{const_name ret__int_'_update};
check_ret "test3" @{const_name ret__int_'_update};
check_ret "test4" @{const_name ret__int_'_update};
check_ret "test5" @{const_name ret__int_'_update};
\<close>

end

end
