(*
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Should pass, but produce a warning for an inline asm statement that is
   outside the supported subset for input/output operands. *)

theory asm_warn
imports "CParser.CTranslation"
begin

external_file "asm_warn_two_outputs.c"
install_C_file "asm_warn_two_outputs.c"

context asm_warn_two_outputs
begin
thm two_outputs_body_def
end

end
