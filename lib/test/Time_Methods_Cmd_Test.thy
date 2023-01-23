(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Time_Methods_Cmd_Test imports
  Lib.Time_Methods_Cmd
  Eisbach_Tools.Eisbach_Methods
  "HOL-Library.Sublist"
begin

text \<open>
  @{method time_methods} is a utility that runs several methods on the same
  proof goal, printing the running time of each one.

  Usage:

    apply (time_methods [(no_check)] [(skip_fail)]
        [name1:] \<open>method1\<close>
        [name2:] \<open>method2\<close>
        ...)

  Options:

    no_check: Don't check that the outputs of each method match.

    skip_fail: Don't print anything for failed methods.
\<close>

experiment begin
  section \<open>Basic examples\<close>

  lemma
    "A \<Longrightarrow> B \<Longrightarrow> A \<or> B"
    apply (time_methods
            \<open>erule disjI1\<close>
            \<open>erule disjI2\<close>)
    done

  text \<open>Give labels to methods:\<close>
  lemma
    "A \<Longrightarrow> B \<Longrightarrow> A \<or> B"
    apply (time_methods
            label: \<open>erule disjI1\<close>
            "another label": \<open>erule disjI2\<close>)
    done

  text \<open>no_check prevents failing even if the method results differ.\<close>
  lemma
    "A \<Longrightarrow> B \<Longrightarrow> A \<or> B"
    apply (time_methods (no_check)
            \<open>rule disjI1\<close>
            \<open>rule disjI2\<close>)
    apply assumption
    done

  text \<open>
    Fast and slow list reversals.
  \<close>
  lemma list_eval_rev_append:
    "rev xs = rev xs @ []"
    "rev [] @ ys = ys"
    "rev (x # xs) @ ys = rev xs @ (x # ys)"
    by auto

  lemma "rev [0..100] = map ((-) 100) [0..100]"
        "rev [0..200] = map ((-) 200) [0..200]"
    text \<open>evaluate everything but @{term rev}\<close>
    apply (all \<open>match conclusion in "rev x = y" for x y \<Rightarrow>
                  \<open>rule subst[where t = x], simp add: upto.simps\<close>\<close>)
    apply (all \<open>match conclusion in "rev x = y" for x y \<Rightarrow>
                  \<open>rule subst[where t = y], simp add: upto.simps\<close>\<close>)

    text \<open>evaluate @{term rev}\<close>
    apply (time_methods
            naive100: \<open>simp\<close>
            slow100: \<open>simp only: rev.simps append.simps\<close>
            fast100: \<open>subst list_eval_rev_append(1), simp only: list_eval_rev_append(2-3)\<close>
          )
    apply (time_methods
            naive200: \<open>simp\<close>
            slow200: \<open>simp only: rev.simps append.simps\<close>
            fast200: \<open>subst list_eval_rev_append(1), simp only: list_eval_rev_append(2-3)\<close>
          )
    done

  text \<open>
    Fast and slow subsequence testing.
  \<close>
  lemma
    "subseq (map ((*) 2) [1 ..  5]) [1 .. 10]"
    "subseq (map ((*) 2) [1 ..  6]) [1 .. 12]"
    "subseq (map ((*) 2) [1 ..  7]) [1 .. 14]"
    "subseq (map ((*) 2) [1 ..  8]) [1 .. 16]"
    apply (all \<open>match conclusion in "subseq x y" for x y \<Rightarrow>
                  \<open>rule subst[where t = x], simp add: upto.simps,
                   rule subst[where t = y], simp add: upto.simps\<close>\<close>)

    apply (time_methods
      "HOL simp": \<open>simp\<close>

      "l4v simp": \<open>simp cong: if_cong cong del: if_weak_cong\<close>
        \<comment> \<open>exponential time!\<close>
      )+
    done

  text \<open>
    Which method is a better SAT solver?
    Instance 01 from the uf20-91 dataset at http://www.cs.ubc.ca/~hoos/SATLIB/benchm.html
  \<close>
  lemma "\<exists>x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20.
          (~x4 & x18 & ~x19) | (~x3 & ~x18 & x5) | (x5 & x8 & x15) | (x20 & ~x7 & x16) |
          (~x10 & x13 & x7) | (x12 & x9 & ~x17) | (~x17 & ~x19 & ~x5) | (x16 & ~x9 & ~x15) |
          (~x11 & x5 & x14) | (~x18 & x10 & ~x13) | (x3 & ~x11 & ~x12) | (x6 & x17 & x8) |
          (x18 & ~x14 & ~x1) | (x19 & x15 & ~x10) | (~x12 & ~x18 & x19) | (x8 & ~x4 & ~x7) |
          (x8 & x9 & ~x4) | (~x7 & ~x17 & x15) | (~x12 & x7 & x14) | (x10 & x11 & ~x8) |
          (~x2 & x15 & x11) | (~x9 & ~x6 & ~x1) | (x11 & ~x20 & x17) | (~x9 & x15 & ~x13) |
          (~x12 & x7 & x17) | (x18 & x2 & ~x20) | (~x20 & ~x12 & ~x4) | (~x19 & ~x11 & ~x14) |
          (x16 & ~x18 & x4) | (x1 & x17 & x19) | (x13 & ~x15 & ~x10) | (x12 & x14 & x13) |
          (~x12 & x14 & x7) | (x7 & ~x16 & ~x10) | (~x6 & ~x10 & ~x7) | (~x20 & ~x14 & x16) |
          (x19 & ~x17 & ~x11) | (x7 & ~x1 & x20) | (x5 & ~x12 & ~x15) | (x4 & x9 & x13) |
          (~x12 & x11 & x7) | (x5 & ~x19 & x8) | (~x1 & ~x16 & ~x17) | (~x20 & x14 & x15) |
          (~x13 & x4 & ~x10) | (~x14 & ~x7 & ~x10) | (x5 & ~x9 & ~x20) | (~x10 & ~x1 & x19) |
          (x16 & x15 & x1) | (~x16 & ~x3 & x11) | (x15 & x10 & ~x4) | (~x4 & x15 & x3) |
          (x10 & x16 & ~x11) | (x8 & ~x12 & x5) | (~x14 & x6 & ~x12) | (~x1 & ~x6 & ~x11) |
          (x13 & x5 & x1) | (x7 & x2 & ~x12) | (~x1 & x20 & ~x19) | (x2 & x13 & x8) |
          (~x15 & ~x18 & ~x4) | (x11 & ~x14 & ~x9) | (x6 & x15 & x2) | (~x5 & x12 & x15) |
          (x6 & ~x17 & ~x5) | (x13 & ~x5 & x19) | (~x20 & x1 & ~x14) | (~x9 & x17 & ~x15) |
          (x5 & ~x19 & x18) | (x12 & ~x8 & x10) | (x18 & ~x14 & x4) | (~x15 & x9 & ~x13) |
          (~x9 & x5 & x1) | (~x10 & x19 & x14) | (~x20 & ~x9 & ~x4) | (x9 & x2 & ~x19) |
          (x5 & ~x13 & x17) | (~x2 & x10 & x18) | (x18 & ~x3 & ~x11) | (~x7 & x9 & ~x17) |
          (x15 & x6 & x3) | (x2 & ~x3 & x13) | (~x12 & ~x3 & x2) | (x2 & x3 & ~x17) |
          (~x20 & x15 & x16) | (x5 & x17 & x19) | (x20 & x18 & ~x11) | (x9 & ~x1 & x5) |
          (x19 & ~x9 & ~x17) | (~x12 & x2 & ~x17)"
    using [[meson_max_clauses=99]]
    apply (time_methods
              blast: \<open>blast\<close>
              metis: \<open>metis\<close>
              meson: \<open>meson\<close>
              smt:   \<open>smt\<close>
              force: \<open>force\<close>
              fastforce: \<open>fastforce intro: ex_bool_eq[THEN iffD2]\<close>
              fastforce: \<open>fastforce simp: ex_bool_eq\<close>
              presburger: \<open>use ex_bool_eq[simp] in presburger\<close>
          )
    done

  section \<open>Other tests\<close>

  text \<open>Test ML interface\<close>
  lemma "True"
    apply (tactic \<open>
            let val method = SIMPLE_METHOD (simp_tac @{context} 1)
                fun dummy_callback _ _ = ()
            in (fn st => Time_Methods.time_methods false false dummy_callback [(NONE, method)] [] st
                      |> (fn ([timing], st') => (tracing (Timing.message timing); st')))
               |> NO_CONTEXT_TACTIC @{context}
            end\<close>)
    done

  text \<open>Check that we fail when the methods give different results\<close>
  lemma
    "A \<or> B"
    apply (tactic \<open>
      let
        fun skip_dummy_state tac = fn st =>
            case Thm.prop_of st of
                Const ("Pure.prop", _) $ (Const ("Pure.term", _) $ Const ("Pure.dummy_pattern", _)) =>
                  Seq.succeed st
              | _ => tac st;
        val methods = @{thms disjI1 disjI2}
              |> map (fn rule => (NONE, SIMPLE_METHOD (resolve_tac @{context} [rule] 1)))
        fun dummy_callback _ _ = ()
      in (fn st => Time_Methods.time_methods false false dummy_callback methods [] st
                   |> (fn (timing, st') => error "test failed: shouldn't reach here")
                   handle THM _ => Seq.succeed (Seq.Result st)) (* should reach here *)
         |> NO_CONTEXT_TACTIC @{context}
         |> skip_dummy_state
      end\<close>)
    oops

  text \<open>Check that we propagate failures from the input methods\<close>
  lemma "A"
    apply (fails \<open>time_methods \<open>simp\<close>\<close>)
    oops

  text \<open>Check that we skip failing methods when skip_fail set\<close>
  lemma "A \<and> B \<Longrightarrow> A"
    apply (
        ( \<comment> \<open>roughly corresponds to "time_methods (skip_fail) \<open>fail\<close>",
              but errors if it calls the output callback\<close>
          tactic \<open>
            let
              fun timing_callback _ _ = error "test failed: shouldn't reach here"
              val methods = [(NONE, SIMPLE_METHOD no_tac)]
            in
              (fn st =>
                #2 (Time_Methods.time_methods false true timing_callback methods [] st))
              |> NO_CONTEXT_TACTIC @{context}
            end\<close>)
      | time_methods (skip_fail) good_simp: \<open>simp\<close>)
    done
end

end
