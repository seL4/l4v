(*
 *
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory Time_Methods_Cmd imports
  Eisbach_Methods
begin

text \<open>
  Utility that runs several methods on the same proof goal, printing the
  running time of each one.

  Usage:

    apply (time_methods [(no_check)]
        [name1:] \<open>method1\<close>
        [name2:] \<open>method2\<close>
        ...)

  See the examples at the end of this theory.
\<close>

ML {*
*}
method_setup time_methods =
 \<open>
let
  (* Work around Isabelle running every apply method on an empty proof state *)
  fun skip_dummy_state tactic = fn st =>
      case Thm.prop_of st of
          Const ("Pure.prop", _) $ (Const ("Pure.term", _) $ Const ("Pure.dummy_pattern", _)) =>
            Seq.succeed st
        | _ => tactic st;
in
  Scan.lift (Scan.optional (Args.parens (Parse.reserved "no_check") >> K true) false) --
  Scan.repeat1 (Scan.option (Scan.lift (Parse.liberal_name --| Parse.$$$ ":")) -- Method.text_closure) >>
  (fn (no_check, maybe_named_methods) => fn ctxt => fn facts => let
        val named_methods = tag_list 1 maybe_named_methods
                |> map (fn (i, (maybe_name, method)) =>
                        case maybe_name of SOME name => (name, method)
                                         | NONE => ("[method " ^ string_of_int i ^ "]", method))
        fun tac st = let
            fun run name method =
                  Timing.timing (fn () => case method_evaluate method ctxt facts st |> Seq.pull of
                        NONE => (NONE, Seq.empty)
                      | SOME (st', sts') => (SOME st', Seq.cons st' sts')) ()
            val results = named_methods |> map (fn (name, method) =>
                  let val (time, (st', results)) = run name method
                      val _ = warning (name ^ ": " ^ Timing.message time)
                  in {name = name, state = st', results = results} end)
            val canonical_result = hd results
            val other_results = tl results
          in
            if no_check then #results canonical_result else
            case other_results |> filter (fn result =>
                      Option.map Thm.full_prop_of (#state result) <>
                      Option.map Thm.full_prop_of (#state canonical_result)) of
                [] => #results canonical_result
              | (bad::_) => raise THM ("methods \"" ^ #name canonical_result ^
                                       "\" and \"" ^ #name bad ^ "\" have different results",
                                       1, the_list (#state canonical_result) @ the_list (#state bad))
          end
     in SIMPLE_METHOD (skip_dummy_state tac) [] end)
end
\<close>

text \<open>Examples\<close>
experiment begin
  lemma
    "a = b \<Longrightarrow> b = c \<Longrightarrow> a = c"
    apply (time_methods
            \<open>rule back_subst[where P="op= a"], assumption+\<close>
            \<open>rule trans, assumption+\<close>)
    done

  lemma
    "a = b \<Longrightarrow> b = c \<Longrightarrow> a = c"
    apply (time_methods (no_check)
            \<open>rule back_subst[where P="op= a"]\<close>
            \<open>rule trans\<close>)
     text \<open>no_check prevents failing even though the method results differ\<close>
     apply assumption+
    done

  text \<open>
    Fast and slow list reversals
  \<close>
  lemma list_eval_rev_append:
    "rev xs = rev xs @ []"
    "rev [] @ ys = ys"
    "rev (x # xs) @ ys = rev xs @ (x # ys)"
    by auto

  lemma "rev [10..90] = map (op- 100) [10..90]"
        "rev [10..290] = map (op- 300) [10..290]"
    text \<open>evaluate everything but @{term rev}\<close>
    apply (all \<open>match conclusion in "rev x = y" for x y \<Rightarrow>
                  \<open>rule subst[where t = x], simp\<close>\<close>)
    apply (all \<open>match conclusion in "rev x = y" for x y \<Rightarrow>
                  \<open>rule subst[where t = y], simp\<close>\<close>)

    text \<open>evaluate @{term rev}\<close>
    apply (time_methods
            simp: \<open>simp\<close>
            slow: \<open>simp only: rev.simps append.simps\<close>
            fast: \<open>subst list_eval_rev_append(1), simp only: list_eval_rev_append(2-3)\<close>
          )
    apply (time_methods
            simp: \<open>simp\<close>
            slow: \<open>simp only: rev.simps append.simps\<close>
            fast: \<open>subst list_eval_rev_append(1), simp only: list_eval_rev_append(2-3)\<close>
          )
    done


  text \<open>Other tests\<close>

  lemma "A"
    -- "simp should fail and time_methods should propagate the failure"
    apply (fails \<open>time_methods \<open>simp\<close>\<close>)
    oops
end

end
