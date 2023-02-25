(*
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Boolean_Inequalities
  imports Word_EqI
begin

section \<open>All inequalities between binary Boolean operations on @{typ "'a word"}\<close>

text \<open>
  Enumerates all binary functions resulting from Boolean operations on @{typ "'a word"}
  and derives all inequalities of the form @{term "f x y \<le> g x y"} between them.
  We leave out the trivial @{term "0 \<le> g x y"}, @{term "f x y \<le> -1"}, and
  @{term "f x y \<le> f x y"}, because these are already readily available to the simplifier and
  other methods.

  This leaves 36 inequalities. Some of these are subsumed by each other, but we generate
  the full list to avoid too much manual processing.

  All inequalities produced here are in simp normal form.\<close>

context
  includes bit_operations_syntax
begin

(* The following are all 16 binary Boolean operations (on bool):
   all_bool_funs \<equiv> [
     \<lambda>x y. False,
     \<lambda>x y. x \<and> y,
     \<lambda>x y. x \<and> \<not>y,
     \<lambda>x y. x,
     \<lambda>x y. \<not>x \<and> y,
     \<lambda>x y. y,
     \<lambda>x y. x \<noteq> y,
     \<lambda>x y. x \<or> y,
     \<lambda>x y. \<not>(x \<or> y),
     \<lambda>x y. x = y,
     \<lambda>x y. \<not>y,
     \<lambda>x y. x \<or> \<not>y,
     \<lambda>x y. \<not>x,
     \<lambda>x y. \<not>x \<or> y,
     \<lambda>x y. \<not>(x \<and> y),
     \<lambda>x y. True
   ]

  We can define the same for word operations:
*)
definition all_bool_word_funs :: "('a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word) list" where
  "all_bool_word_funs \<equiv> [
     \<lambda>x y. 0,
     \<lambda>x y. x AND y,
     \<lambda>x y. x AND NOT y,
     \<lambda>x y. x,
     \<lambda>x y. NOT x AND y,
     \<lambda>x y. y,
     \<lambda>x y. x XOR y,
     \<lambda>x y. x OR y,
     \<lambda>x y. NOT (x OR y),
     \<lambda>x y. NOT (x XOR y),
     \<lambda>x y. NOT y,
     \<lambda>x y. x OR NOT y,
     \<lambda>x y. NOT x,
     \<lambda>x y. NOT x OR y,
     \<lambda>x y. NOT (x AND y),
     \<lambda>x y. -1
   ]"


text \<open>
  The inequalities on @{typ "'a word"} follow directly from implications on propositional
  Boolean logic, which @{method simp} can solve automatically. This means, we can simply
  enumerate all combinations, reduce from @{typ "'a word"} to @{typ bool}, and attempt to
  solve by @{method simp} to get the complete list.\<close>
local_setup \<open>
let
  (* derived from Numeral.mk_num, but returns a term, not syntax. *)
  fun mk_num n =
    if n > 0 then
      (case Integer.quot_rem n 2 of
        (0, 1) => \<^const>\<open>Num.One\<close>
      | (n, 0) => \<^const>\<open>Num.Bit0\<close> $ mk_num n
      | (n, 1) => \<^const>\<open>Num.Bit1\<close> $ mk_num n)
    else raise Match

  (* derived from Numeral.mk_number, but returns a term, not syntax. *)
  fun mk_number n =
    if n = 0 then \<^term>\<open>0::nat\<close>
    else if n = 1 then \<^term>\<open>1::nat\<close>
    else \<^term>\<open>numeral::num \<Rightarrow> nat\<close> $ mk_num n;

  (* generic form of the goal statement *)
  val goal = @{term "\<lambda>n m. (all_bool_word_funs!n) x y \<le> (all_bool_word_funs!m) x y"}
  (* instance of the goal statement for a pair (i,j) of Boolean functions *)
  fun stmt (i,j) = HOLogic.Trueprop $ (goal $ mk_number i $ mk_number j)

  (* attempt to prove an inequality between functions i and j *)
  fun le_thm ctxt (i,j) = Goal.prove ctxt ["x", "y"] [] (stmt (i,j)) (fn _ =>
    (asm_full_simp_tac (ctxt addsimps [@{thm all_bool_word_funs_def}])
     THEN_ALL_NEW resolve_tac ctxt @{thms word_leI}
     THEN_ALL_NEW asm_full_simp_tac (ctxt addsimps @{thms word_eqI_simps bit_simps})) 1)

  (* generate all combinations for (i,j), collect successful inequality theorems,
     unfold all_bool_word_funs, and put into simp normal form. We leave out 0 (bottom)
     and 15 (top), as well as reflexive thms to remove trivial lemmas from the list.*)
  fun thms ctxt =
    map_product (fn x => fn y => (x,y)) (1 upto 14) (1 upto 14)
    |> filter (fn (x,y) => x <> y)
    |> map_filter (try (le_thm ctxt))
    |> map (Simplifier.simplify ctxt o Local_Defs.unfold ctxt @{thms all_bool_word_funs_def})
in
  fn ctxt =>
    Local_Theory.notes [((Binding.name "word_bool_le_funs", []), [(thms ctxt, [])])] ctxt |> #2
end
\<close>

(* Sanity checks: *)
lemma
  "x AND y \<le> x" for x :: "'a::len word"
  by (rule word_bool_le_funs(1))

lemma
  "NOT x \<le> NOT x OR NOT y" for x :: "'a::len word"
  by (rule word_bool_le_funs(36))

lemma
  "x XOR y \<le> NOT x OR NOT y" for x :: "'a::len word"
  by (rule word_bool_le_funs)

(* Example use when the goal is not in simp normal form: *)
lemma word_xor_le_nand:
  "x XOR y \<le> NOT (x AND y)" for x :: "'a::len word"
  by (simp add: word_bool_le_funs)

end

end