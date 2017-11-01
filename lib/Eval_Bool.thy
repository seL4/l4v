(*
 *
 * Copyright 2017, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory Eval_Bool

imports Try_Methods

begin

text {* The eval_bool method/simproc uses the code generator setup to
reduce terms of boolean type to True or False. Reducing booleans to
True or False is nearly always desirable, and is a fairly good heuristic
for when to make use of definitions/code-equations.

Additional simprocs exist to reduce other types.
*}

ML {*
structure Eval_Simproc = struct

exception Failure

fun mk_constname_tab ts = fold Term.add_const_names ts []
  |> Symtab.make_set

fun is_built_from tab t = case Term.strip_comb t of
    (Const (cn, _), ts) => Symtab.defined tab cn
        andalso forall (is_built_from tab) ts
  | _ => false

fun eval tab ctxt ct = let
    val t = Thm.term_of ct
    val _ = Term.fold_aterms (fn Free _ => raise Failure
      | Var _ => raise Failure | _ => ignore) t ()
    val _ = not (is_built_from tab t) orelse raise Failure
    val ev = the (try (Code_Simp.dynamic_conv ctxt) ct)
  in if is_built_from tab (Thm.term_of (Thm.rhs_of ev))
    then SOME ev else NONE end
  handle Failure => NONE | Option => NONE

val eval_bool = eval (mk_constname_tab [@{term "True"}, @{term "False"}])
val eval_nat = eval (mk_constname_tab [@{term "Suc 0"}, @{term "Suc 1"},
    @{term "Suc 9"}])
val eval_int = eval (mk_constname_tab [@{term "0 :: int"}, @{term "1 :: int"},
    @{term "18 :: int"}, @{term "(-9) :: int"}])

val eval_bool_simproc = Simplifier.make_simproc @{context} "eval_bool"
  { lhss = [@{term "b :: bool"}], proc = K eval_bool }
val eval_nat_simproc = Simplifier.make_simproc @{context} "eval_nat"
  { lhss = [@{term "n :: nat"}], proc = K eval_nat }
val eval_int_simproc = Simplifier.make_simproc @{context} "eval_int"
  { lhss = [@{term "i :: int"}], proc = K eval_int }

end
*}

method_setup eval_bool = \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD'
    (CHANGED o full_simp_tac (clear_simpset ctxt
        addsimprocs [Eval_Simproc.eval_bool_simproc])))\<close>
    "use code generator setup to simplify booleans in goals to True or False"

method_setup eval_int_nat = \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD'
    (CHANGED o full_simp_tac (clear_simpset ctxt
        addsimprocs [Eval_Simproc.eval_nat_simproc, Eval_Simproc.eval_int_simproc])))\<close>
    "use code generator setup to simplify nats and ints in goals to values"

add_try_method eval_bool

text {* Testing. *}
definition
  eval_bool_test_seq :: "int list"
where
  "eval_bool_test_seq = [2, 3, 4, 5, 6, 7, 8]"

lemma
  "eval_bool_test_seq ! 4 = 6 \<and> (3 :: nat) < 4
    \<and> sorted eval_bool_test_seq"
  by eval_bool

text {*
A related gadget for installing constant definitions from locales
as code equations. Useful where locales are being used to "hide"
constants from the global state rather than to do anything tricky
with interpretations.

Installing the global definitions in this way will allow eval_bool
etc to "see through" the hiding and decide questions about these
constants.
*}

ML {*
structure Add_Locale_Code_Defs = struct

fun get_const_defs thy nm = Sign.consts_of thy
  |> Consts.dest |> #constants
  |> map fst
  |> filter (fn s => case Long_Name.explode s of
        [_, nm', _] => nm' = nm | _ => false)
  |> map_filter (try (suffix "_def" #> Global_Theory.get_thm thy))

fun setup nm thy = fold (fn t => Code.add_eqn_global (t, true))
    (get_const_defs thy nm) thy

end
*}

locale eval_bool_test_locale begin

definition
  "x == (12 :: int)"

definition
  "y == (13 :: int)"

definition
  "z = (x * y) + x + y"

end

setup {* Add_Locale_Code_Defs.setup "eval_bool_test_locale" *}

setup {* Add_Locale_Code_Defs.setup "eval_bool_test_locale" *}

lemma "eval_bool_test_locale.z > 150"
  by eval_bool

end
