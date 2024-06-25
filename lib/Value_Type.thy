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
   Define a type synonym from a term of type nat or int that evaluates to a (positive) numeral.

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

fun cast_to_nat t = if type_of t = @{typ int} then @{term nat} $ t else t

fun make_type binding v lthy =
  let
    val n = case get_term_numeral v of
              SOME n => n
            | NONE => raise TERM ("make_type: numeral expected", [v])
    val typ = typ_of_num n
  in
    lthy |> Typedecl.abbrev (binding, [], Mixfix.NoSyn) typ |> #2
  end

(* Copied from method eval in HOL.thy: *)
fun eval_tac ctxt =
  let val conv = Code_Runtime.dynamic_holds_conv
  in
    CONVERSION (Conv.params_conv ~1 (Conv.concl_conv ~1 o conv) ctxt) THEN'
    resolve_tac ctxt [TrueI]
  end

(* This produces two theorems: one symbolic _def theorem and one numeric _val theorem.
   The _def theorem is a definition, via Specification.definition.
   The _val theorem is proved from that definition using "eval_tac" via the code generator. *)
fun make_defs binding t v lthy =
  let
    val t = cast_to_nat t
    val mk_eq = HOLogic.mk_Trueprop o HOLogic.mk_eq
    val def_t = mk_eq (Free (Binding.name_of binding, @{typ nat}), t)
    val ((_, (_, def_thm)), lthy') =
          lthy |> Specification.definition NONE [] [] (Binding.empty_atts, def_t)
    val eq_t = mk_eq (t, force_nat_numeral v)
    val eq_thm =
          Goal.prove lthy' [] [] eq_t (fn {context = ctxt, prems = _} => eval_tac ctxt 1)
    val thm = @{thm trans} OF [def_thm, eq_thm]
    val val_binding = Binding.map_name (fn n => n ^ "_val") binding |> Binding.reset_pos
  in
    Local_Theory.note ((val_binding, []), [thm]) lthy' |> #2
  end

in

fun value_type_cmd no_def binding t lthy =
  let
    val t' = Syntax.read_term lthy t
    val v = case get_term_numeral t' of SOME _ => t' | NONE => Value_Command.value lthy t'
  in
    lthy
    |> make_type binding v
    |> (if no_def then I else make_defs binding t' v)
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
Potential extension ideas for the future:

* It may be possible to generalise this command to non-numeral types -- as long as the RHS can
  be interpreted as some nat n, we can in theory always define a type with n elements, and
  instantiate that type into class finite. Might have to present a goal to the user that RHS
  evaluates > 0 in nat.

  The benefit of defining a new type instead of a type synonym for a numeral type is that type
  checking is now more meaningful and we do get some abstraction over the actual value, which would
  help make proofs more generic.

  The disadvantage of a non-numeral type is that it is not equal to the types that come out of the
  C parser.

* We could add more automatic casts from known types to nat (e.g. from word). But it's relatively
  low overhead to provide the cast as a user.
*)

end
