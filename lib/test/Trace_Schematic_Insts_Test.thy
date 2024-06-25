(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Trace_Schematic_Insts_Test
imports
  Eisbach_Tools.Trace_Schematic_Insts
begin

text \<open>
  Trace the schematic variables and types that a method instantiates.
  This only works for the variables already in the proof goal; new
  variables introduced by the traced method are not tracked.
\<close>

experiment begin
section \<open>Examples\<close>

text \<open>Schematic variables\<close>
lemma "\<lbrakk> \<forall>x. P x \<rbrakk> \<Longrightarrow> P x"
  apply (drule spec) \<comment> \<open>introduces schematic var "?x"\<close>
  apply (trace_schematic_insts \<open>assumption\<close>)
  done

definition foo :: "'a \<Rightarrow> bool"
  where "foo x = True"

lemma fooI1:
  "foo 0 \<Longrightarrow> foo x"
  by (simp add: foo_def)

lemma fooI2:
  "foo x \<Longrightarrow> foo 0"
  by (simp add: foo_def)

lemma fooI2':
  "foo x \<Longrightarrow> foo (0 :: nat)"
  by (erule fooI2)

text \<open>Schematic type variables\<close>
lemma "foo x \<Longrightarrow> foo y"
  apply (rule fooI1) \<comment> \<open>introduces schematic type "0 :: ?'a"\<close>
  apply (trace_schematic_insts \<open>erule fooI2'\<close>)
  done

text \<open>When backtracking, every recursive invocation is traced\<close>
lemma "\<lbrakk> \<forall>x. Q x \<longrightarrow> R x; \<forall>x. P x \<longrightarrow> Q x; P x; P y \<longrightarrow> R x \<rbrakk> \<Longrightarrow> R x"
  apply (drule spec)
  apply (drule spec)
  text \<open>For more clarity, methods can be named\<close>
  apply (trace_schematic_insts impE1 \<open>erule impE\<close>,
         trace_schematic_insts impE2 \<open>erule impE\<close>,
         (trace_schematic_insts "try assumption" \<open>assumption\<close>)+; fail)
  done

text \<open>Interactive example\<close>
ML \<open>
  fun trace_resolve_tac ctxt =
      Trace_Schematic_Insts.trace_schematic_insts_tac ctxt
        (Trace_Schematic_Insts.default_rule_report ctxt "demo title")
        (fn t => resolve_tac ctxt [t])
\<close>
lemma
  assumes Pf: "\<And>f (x :: nat). Q f \<Longrightarrow> P x \<Longrightarrow> P (f x)"
  assumes Q: "Q ((*) 2)"
  assumes P: "P a"
  shows "\<exists>x. P (x + a + a)"
  apply (tactic \<open>trace_resolve_tac @{context} @{thm exI} 1\<close>)
  apply (trace_schematic_insts \<open>subst add_0\<close>)

  \<comment>\<open>
    This picks *some* instantiation of `f` in @{thm Pf}. The first one is
    @{term "\<lambda>a. a"}, which isn't what we want.
  \<close>
  apply (tactic \<open>trace_resolve_tac @{context} @{thm Pf} 1\<close>)
   \<comment>\<open>
     This picks the *next* instantiation of `f`, in this case @{term "\<lambda>a. a + a"}
     Notice that the reporting callback gets called with the new instantiations!
   \<close>
   back

   apply (tactic \<open>
     Trace_Schematic_Insts.trace_schematic_insts_tac
       @{context}
       (Trace_Schematic_Insts.default_rule_report @{context} "demo title")
       (fn t => EqSubst.eqsubst_tac @{context} [0] [t])
       @{thm mult_2[symmetric]} 1
   \<close>)
   apply (tactic \<open>trace_resolve_tac @{context} @{thm Q} 1\<close>)
  apply (tactic \<open>trace_resolve_tac @{context} @{thm P} 1\<close>)
  done

section \<open>Tests\<close>

ML \<open>
fun trace_schematic_assert ctxt test_name tac expected_vars expected_tvars =
  let
    fun skip_dummy_state tac = fn st =>
        case Thm.prop_of st of
            Const (@{const_name Pure.prop}, _) $
              (Const (@{const_name Pure.term}, _) $ Const (@{const_name Pure.dummy_pattern}, _)) =>
              Seq.succeed st
          | _ => tac st

    fun check insts =
      if expected_vars = #terms insts andalso expected_tvars = #typs insts then () else
        error ("Trace_Schematic_Insts failed test: " ^ test_name)

  in NO_CONTEXT_TACTIC ctxt
        (Trace_Schematic_Insts.trace_schematic_insts (SIMPLE_METHOD tac) check [])
     |> skip_dummy_state
  end
\<close>

text \<open>Schematic variables\<close>
lemma "\<lbrakk> \<forall>x. P x \<rbrakk> \<Longrightarrow> P x"
  apply (drule spec)
  apply (tactic \<open>let
      val alpha = TFree ("'a", @{sort type})
      val expected_vars = [(Var (("x", 0), alpha), Free ("x", alpha))]
      val expected_tvars = []
      in trace_schematic_assert @{context}
            "basic Var test" (assume_tac @{context} 1)
            expected_vars expected_tvars
      end\<close>)
  done

text \<open>Schematic type variables\<close>
lemma "foo x \<Longrightarrow> foo y"
  apply (rule fooI1)
  apply (tactic \<open>let
      val expected_vars = []
      val expected_tvars = [(TVar (("'a", 0), @{sort zero}), @{typ nat})]
      in trace_schematic_assert
            @{context}
            "basic TVar test"
            (eresolve_tac @{context} @{thms fooI2'} 1)
            expected_vars expected_tvars
      end\<close>)
  done


ML \<open>
fun trace_schematic_resolve_tac_assert ctxt test_name thm expected_rule_insts expected_proof_insts =
  let
    fun check rule_insts proof_insts =
        if expected_rule_insts = rule_insts andalso expected_proof_insts = proof_insts
        then ()
        else
          let
            val _ = tracing (@{make_string} (rule_insts, proof_insts))
          in error ("Trace_Schematic_Insts failed test: " ^ test_name) end
    fun tactic thm = resolve_tac ctxt [thm]
  in HEADGOAL (Trace_Schematic_Insts.trace_schematic_insts_tac ctxt check tactic thm)
  end
\<close>

text \<open>Simultaneous rule and goal instantiations\<close>
lemma "\<exists>a. foo (a :: nat)"
  apply (rule exI)
  apply (tactic \<open>
    let
      val a' = TVar (("'a", 0), @{sort type})
      val b' = TVar (("'b", 0), @{sort zero})
      val a'' = TVar (("'a", 2), @{sort type})
      val expected_rule_vars = [
        (Var (("x", 0), a'), Var(("x", 2), a''))
      ]
      val expected_rule_tvars = [
        (a', a''),
        (b', @{typ nat})
      ]
      val expected_goal_vars = [
        (Var (("a", 0), @{typ nat}), @{term "0 :: nat"})
      ]
    in
      trace_schematic_resolve_tac_assert
        @{context}
        "basic rule tracing"
        @{thm fooI2}
        {bounds = [], terms = expected_rule_vars, typs = expected_rule_tvars}
        {bounds = [], terms = expected_goal_vars, typs = []}
    end
  \<close>)
  by (simp add: foo_def)

text \<open>Rule instantiations with bound variables\<close>
lemma "\<And>X. X \<and> Y \<Longrightarrow> Y \<and> X"
  apply (tactic \<open>
    let
      val expected_rule_bounds = [("X", @{typ bool})]
      val expected_rule_vars = [
        (Var (("P", 0), @{typ bool}), @{term "\<lambda>X :: bool. Y :: bool"}),
        (Var (("Q", 0), @{typ bool}), @{term "\<lambda>X :: bool. X :: bool"})
      ]
    in
      trace_schematic_resolve_tac_assert
        @{context}
        "rule tracing with bound variables"
        @{thm conjI}
        {bounds = expected_rule_bounds, terms = expected_rule_vars, typs = []}
        {bounds = [], terms = [], typs = []}
    end
  \<close>)
  by simp+

text \<open>Rule instantiations with function terms\<close>
lemma "\<exists>f. \<forall>x. f x = x"
  apply (intro exI allI)
  apply (rule fun_cong)
  apply (tactic \<open>
    let
      val a' = TVar (("'a", 0), @{sort type})
      \<comment>\<open>
        New lambda abstraction gets an anonymous variable name. Usually rendered as
        @{term "\<lambda>x a. a"}.
      \<close>
      val lambda = Abs ("x", @{typ 'a}, Abs ("", @{typ 'a}, Bound 0))

      val expected_rule_bounds = [("x", @{typ 'a})]
      val expected_rule_vars = [
        (Var (("t", 0), a'), lambda)
      ]
      val expected_rule_typs = [
        (a', @{typ "'a \<Rightarrow> 'a"})
      ]
      val expected_goal_vars = [
        (Var (("f", 2), @{typ "'a \<Rightarrow> 'a \<Rightarrow> 'a"}), lambda)
      ]
    in
      trace_schematic_resolve_tac_assert
        @{context}
        "rule tracing with function term instantiations"
        @{thm refl}
        {bounds = expected_rule_bounds, terms = expected_rule_vars, typs = expected_rule_typs}
        {bounds = [], terms = expected_goal_vars, typs = []}
    end
  \<close>)
  done

end

end