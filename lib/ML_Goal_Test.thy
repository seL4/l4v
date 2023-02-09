(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory ML_Goal_Test
imports
  ML_Goal
  ML_Utils.ML_Utils
begin
experiment begin

\<comment>\<open>
  Basic usage.
\<close>
ML_goal test: \<open>
  [@{term "(P \<longrightarrow> Q) \<and> P \<longrightarrow> Q"}]
\<close>
  apply clarsimp
  done

thm test

\<comment>\<open>
  A goal that we definitely don't want to write out by hand.

  In this case, we're going to show that if x is less than 10,
  we "only" need to consider the cases when x = 0, or x = 1, or...
\<close>
ML_goal big_goal: \<open>
  let
    val var_x = Free ("x", @{typ nat});
    val var_P = Free ("P", @{typ bool});
    val max = 10;

    \<comment>\<open>
      @{ML "HOLogic.mk_nat"} produces nested Suc's, which are pretty
      ugly, so we use this instead.
    \<close>
    val mk_nat = HOLogic.mk_number @{typ nat};

    \<comment>\<open>
      Turns (i: int) into @{term "x = i \<Longrightarrow> P"}.
    \<close>
    fun mk_case i =
        let
          val prem = HOLogic.mk_eq (var_x, mk_nat i) |> HOLogic.mk_Trueprop;
          val conc = var_P |> HOLogic.mk_Trueprop;
        in Logic.mk_implies (prem, conc) end

    val x_cases =
        ListExtras.range 0 max
        |> map mk_case;

    val assm =
        HOLogic.mk_binrel @{const_name "less"}
          (var_x,
          (mk_nat max))
        |> HOLogic.mk_Trueprop;

    val goal =
        Logic.list_implies (assm :: x_cases, var_P |> HOLogic.mk_Trueprop)

  in [goal] end
\<close>
  by force

\<comment>\<open>
  Names are optional.
\<close>
ML_goal \<open>
  [@{term "True"}]
\<close>
  by (rule TrueI)

\<comment>\<open>
  Multiple goals are supported, and result in similar
  "list of fact" lemmas
\<close>
ML_goal multiple_goals: \<open>
  [@{term "(P \<Longrightarrow> Q \<Longrightarrow> P)"}, @{term "(P \<Longrightarrow> Q \<Longrightarrow> Q)"}]
\<close>
  by simp+

thm multiple_goals[OF TrueI]

\<comment>\<open>
  Handles mixes of @{typ bool} and @{typ prop}.
\<close>
ML_goal \<open>
  [@{term "PROP A \<Longrightarrow> PROP A"}, @{term "B \<longrightarrow> B"}]
\<close>
  by simp+

\<comment>\<open>
  Turns out a lemma name can refer to nothing as well!
\<close>
ML_goal nothing: \<open>[]\<close>
  done

thm nothing[OF TrueI]

\<comment>\<open>
  Attributes can be applied, just like normal lemmas.
\<close>
definition magic where "magic = (5 :: nat)"

ML_goal declared_with_an_attribute[folded magic_def, simp]: \<open>
  [@{term "(5 :: nat) = 2 + 3"}]
\<close>
  by simp

lemma uses_our_new_magic_simp_rule:
  "magic = 1 + 4"
  by simp

end

end