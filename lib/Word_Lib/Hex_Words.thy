(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section "Print Words in Hex"

theory Hex_Words
imports
  "HOL-Library.Word"
begin

text \<open>Print words in hex.\<close>

(* mostly clagged from Num.thy *)
typed_print_translation  \<open>
let
  fun dest_num (Const (@{const_syntax Num.Bit0}, _) $ n) = 2 * dest_num n
    | dest_num (Const (@{const_syntax Num.Bit1}, _) $ n) = 2 * dest_num n + 1
    | dest_num (Const (@{const_syntax Num.One}, _)) = 1;

  fun dest_bin_hex_str tm =
  let
    val num = dest_num tm;
    val pre = if num < 10 then "" else "0x"
  in
    pre ^ (Int.fmt StringCvt.HEX num)
  end;

  fun num_tr' sign ctxt T [n] =
    let
      val k = dest_bin_hex_str n;
      val t' = Syntax.const @{syntax_const "_Numeral"} $
        Syntax.free (sign ^ k);
    in
      case T of
        Type (@{type_name fun}, [_, T' as Type("Word.word",_)]) =>
          if not (Config.get ctxt show_types) andalso can Term.dest_Type T'
          then t'
          else Syntax.const @{syntax_const "_constrain"} $ t' $
                            Syntax_Phases.term_of_typ ctxt T'
      | T' => if T' = dummyT then t' else raise Match
    end;
in [(@{const_syntax numeral}, num_tr' "")] end
\<close>

end
