(*
 * Copyright 2021, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Value_Type
imports "HOL-Library.Numeral_Type"
keywords "value_type" :: thy_decl
begin

(*
   Define a type synonym from a term that evaluates to a numeral.

   Examples:

      value_type num_queues = "num_prio * num_domains"
      value_type num_something = "10 * num_domains"
*)

text \<open>See theory @{text "test/Value_Type_Test.thy"} for further example/demo.\<close>

ML \<open>

local

fun get_term_numeral (Const (@{const_name numeral}, Type ("fun", _)) $ n) = SOME n
  | get_term_numeral (Const (@{const_name "Groups.one"}, _))  = SOME @{term "Num.One"}
  | get_term_numeral (Const (@{const_name "Groups.zero"}, _)) = SOME @{term "0"}
  | get_term_numeral _ = NONE

fun typ_of_num (Const (\<^const_name>\<open>Num.Bit0\<close>, _) $ t) = Type (@{type_name "bit0"}, [typ_of_num t])
  | typ_of_num (Const (\<^const_name>\<open>Num.Bit1\<close>, _) $ t) = Type (@{type_name "bit1"}, [typ_of_num t])
  | typ_of_num (Const (\<^const_name>\<open>Num.One\<close>, _))      = Type (@{type_name "num1"}, [])
  | typ_of_num (Const (\<^const_name>\<open>Groups.zero\<close>, _))  = Type (@{type_name "num0"}, [])
  | typ_of_num t = raise TERM ("type_of_num: number expected", [t]);

fun force_nat_numeral (Const (@{const_name numeral}, Type ("fun", [num, _])) $ n) =
      Const (@{const_name numeral}, Type ("fun", [num, @{typ nat}])) $ n
  | force_nat_numeral (Const (@{const_name "Groups.one"}, _))  = @{term "1::nat"}
  | force_nat_numeral (Const (@{const_name "Groups.zero"}, _)) = @{term "0::nat"}
  | force_nat_numeral t = raise TERM ("force_nat_numeral: number expected", [t])

fun make_type binding v lthy =
  let
    val n = case get_term_numeral v of
              SOME n => n
            | NONE => raise TERM ("make_type: numeral expected", [v])
    val typ = typ_of_num n
  in
    lthy |> Typedecl.abbrev (binding, [], Mixfix.NoSyn) typ |> #2
  end

fun make_def binding v lthy =
  let
    val mk_eq = HOLogic.mk_Trueprop o HOLogic.mk_eq
    val def_t = mk_eq (Free (Binding.name_of binding, @{typ nat}), force_nat_numeral v)
  in
    lthy |> Specification.definition NONE [] [] (Binding.empty_atts, def_t) |> #2
  end

in

fun value_type_cmd no_def binding t lthy =
  let
    val t' = Syntax.read_term lthy t
    val v = case get_term_numeral t' of SOME _ => t' | NONE => Value_Command.value lthy t'
  in
    lthy
    |> make_type binding v
    |> (if no_def then I else make_def binding v)
  end

val no_def_option =
  Scan.optional
    (Args.parens (Parse.!!! (Parse.reserved "no_def" >> K true)))
    false;

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>value_type\<close>
    "Declare a type synonym from a term that evaluates to a numeral"
    (no_def_option -- Parse.binding -- (\<^keyword>\<open>=\<close> |-- Parse.term)
      >> (fn ((no_def, n), t) => value_type_cmd no_def n t))

end
\<close>

(*
Potential extension idea for the future:

It may be possible to generalise this command to non-numeral types -- as long as the RHS can
be interpreted as some nat n, we can in theory always define a type with n elements, and instantiate
that type into class finite. Might have to present a goal to the user that RHS evaluates > 0 in nat.

There are a few wrinkles with that, because currently you can use any type on the RHS without
complications. Requiring nat for the RHS term would not be great, because we often have word there.
We could add coercion to nat for word and int, though, that would cover all current use cases.

The benefit of defining a new type instead of a type synonym for a numeral type is that type
checking is now more meaningful and we do get some abstraction over the actual value, which would
help make proofs more generic.
*)


end
