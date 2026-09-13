(*
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Tests for inline asm staments, with error cases for operand syntax and types
   and positive test cases for supported operand forms. *)

theory asm_errors
imports "CParser.CTranslation"
begin

external_file "asm_errors_signed_output.c"
external_file "asm_errors_narrow_output.c"
external_file "asm_errors_ptr_output.c"
external_file "asm_errors_nonlval_output.c"
external_file "asm_errors_wide_input.c"
external_file "asm_errors_struct_input.c"
external_file "asm_ok.c"

ML \<open>
fun install fname thy = IsarInstall.interactive_install fname thy

fun expect_error fname substr =
  case Exn.capture (install fname) @{theory} of
    Exn.Res _ => error ("expected " ^ fname ^ " to be rejected")
  | Exn.Exn (ERROR msg) =>
      if String.isSubstring substr msg then writeln ("OK (" ^ fname ^ "): " ^ msg)
      else error ("unexpected error for " ^ fname ^ ": " ^ msg)
  | Exn.Exn exn => Exn.reraise exn

val output_msg = "asm output operand"
val input_msg = "asm input operand"
\<close>

ML \<open>
expect_error "asm_errors_signed_output.c" (output_msg ^ " \"=r\"(v) has type int. Only unsigned");
expect_error "asm_errors_narrow_output.c" (output_msg ^ " \"=r\"(v) has type unsigned_short. Its width (16)");
expect_error "asm_errors_ptr_output.c" (output_msg ^ " \"=r\"(p) has type ptr_to_unsigned_long");
expect_error "asm_errors_nonlval_output.c" (output_msg ^ " \"=r\"(...) is not an lvalue");
expect_error "asm_errors_struct_input.c" (input_msg ^ " \"r\"(x) has type struct_s_C, which is not a scalar");
\<close>

(* Test for 32-bit targets only, where unsigned long long is wider than the machine word *)
ML \<open>
if ImplementationNumbers.llongWidth > ImplementationNumbers.ptrWidth
then expect_error "asm_errors_wide_input.c" (input_msg ^ " \"r\"(x) has type unsigned_longlong, which is wider")
else ()
\<close>

(* Check that supported operand forms are accepted *)
install_C_file "asm_ok.c"

context asm_ok
begin
thm good_body_def
end

end
