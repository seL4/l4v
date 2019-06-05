(*
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory Trace_Schematic_Insts_Test
imports
  Lib.Trace_Schematic_Insts
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

    fun check var_insts tvar_insts =
      if expected_vars = var_insts andalso expected_tvars = tvar_insts then () else
        error ("Trace_Schematic_Insts failed test: " ^ test_name)

  in Method.NO_CONTEXT_TACTIC ctxt
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

end

end