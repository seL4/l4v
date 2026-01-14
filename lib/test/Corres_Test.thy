(*
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Corres_Test
imports Lib.Corres_Method
begin

(* Test cases and tutorial/docs for Corres_Method *)


section "Setup"

(* Setting up some monads and lemmas to play with later *)
experiment
  fixes sr nf nf'

  fixes f f' :: "('s, nat) nondet_monad"
  assumes f: "corres_underlying sr nf nf' (=) \<top> \<top> f f'"

  fixes Q g g' t
  assumes g: "\<And>x x'::nat. x = t x' \<Longrightarrow> corres_underlying sr nf nf' (=) Q \<top> (g x) (g' x')"
  assumes t: "\<And>x. t x = x"

  fixes P
  assumes Q: "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q\<rbrace>"

  fixes h h'
  assumes h: "corres_underlying sr nf nf' (=) \<top> \<top> h h'"
begin

abbreviation "corres \<equiv> corres_underlying sr nf nf'"


section "Examples"

(* The purpose of the corres method is to make progres on easy corres steps, where things
   "obviously" match up on the concrete and abstract side. You can provide basic terminal
    corres rules like f and g to try. You can provide simp rules to rewrite corres goals
    and to solve side conditions of terminal rules such as the rule for g above. Finally,
    you can provide wp rules to solve or make progress on the final wp goals that a corres
    proof produces. *)
lemma "corres (=) P \<top> (do x \<leftarrow> f; g x od) (do y \<leftarrow> f'; g' y od)"
  by (corres corres: f g wp: Q simp: t)

(* All of these can be declared globally and will be picked up by the method *)
context
  notes [corres] = f g
  notes [wp] = Q
  notes [simp] = t
begin

lemma "corres (=) P \<top> (do x \<leftarrow> f; g x od) (do y \<leftarrow> f'; g' y od)"
  by corres

end

(* During development, the rules needed are often not declared [corres] yet or the right
   simp rules for side conditions etc have yet to be figured out. The following proof
   demonstrates this process. *)
lemma "corres (=) P \<top> (do x \<leftarrow> f; g x od) (do y \<leftarrow> f'; g' y od)"
  (* We begin by invoking "corres" *)
  apply corres
    (* In this case, not much has happened yet, corres has only produced schematic preconditions.
       However, we can see that f and f' are the heads of both sides, and searching with find_theorems
       for a corres rule that mentions those two turns up the rule "f", which we provided to the corres
       method. At this point we can either go back and add it to the previous line, or we
       add a new invocation. The process is very similar to using wpsimp. *)
    apply (corres corres: f)
      (* We see that f has been split off, and we now have a goal for g. Same process as above finds
         the corresponding rule. *)
      apply (corres corres: g)
      (* This solves the corres goal but leaves the side condition of the "g" rule. We can
         now either solve it manually with "apply (simp add: t)" and then continue, or, if it really
         is as simple as a few simp rules, we can tell the corres method to apply it directly *)
      apply (corres simp: t)
     (* We now have only wp goals and the final implication left. *)
     apply (wp Q)
    apply wp
   apply simp
  apply simp
  done

(* Once we have found this proof, we can roll it up, and merge eg. the "simp: t" into the corres
   line before. *)
lemma "corres (=) P \<top> (do x \<leftarrow> f; g x od) (do y \<leftarrow> f'; g' y od)"
  apply corres
    apply (corres corres: f)
      apply (corres corres: g simp: t)
     (* Adding "wp: Q" to the previous line does not help at this stage, because this wp goal
        is produced in the (corres corres: f) line above. We could do
        apply (corres corres: g simp: t wp: Q)+
        above, which *would* solve the rest of the goals, but using + in an uncontrolled way
        is not very stable and therefore not recommended style. *)
     apply (wp Q)
    apply wp
   apply simp
  apply simp
  done

(* Merging the g and f corres lines does enable us to prove the Q wp rule. *)
lemma "corres (=) P \<top> (do x \<leftarrow> f; g x od) (do y \<leftarrow> f'; g' y od)"
  apply corres
    apply (corres corres: f g simp: t wp: Q)
    (* This will still leave the final implication, because we have produced that implication
       outside this subgoal. Merging the two corres invocations above will attempt the final
       implications automatically as well. *)
   apply simp
  apply simp
  done


section "More controlled single-stepping"

(* Sometimes invoking "corres" does too much or too little.
   Too much can occur when the method applies a rule we didn't know is in the [corres] set and
   which leaves us with a strange side condition to solve. Or we may have added an unsafe,
   not-really-terminal rule to [corres] and now we are getting an unprovable goal. Too little
   can occur when the method refuses to split off the head terms even though it looks like a
   terminal corres rule should apply. For these cases, we can take apart some of the internal
   steps like this: *)
lemma "corres (=) P \<top> (do x \<leftarrow> f; g x od) (do y \<leftarrow> f'; g' y od)"
  (* Controlled way to only introduce schematic preconditions and the final implication *)
  apply corres_pre
    (* Invoking "corres" would now fail. Maybe we are convinced that the "f" rule is declared
       [corres] and we want to figure out why it does not apply. Invoking the corres_split method
       will give us the goal the terminal corres rule is tried on: *)
    apply corres_split
       (* Trying out "rule f" does work now -- if it didn't we could debug that and find out why *)
       apply (succeeds \<open>rule f\<close>)
       (* Turns out we forgot to declare it, so we add it manually, and the corres method now
          succeeds on the subgoal *)
       apply (corres corres: f)
      (* For the next goal, we have only g. Maybe we want to debug why corres doesn't solve the
         application of the "g" rule automatically, or where the "x = t x" side condition comes from.
         To do that, we can apply the rule manually: *)
      apply (rule g)
      (* Now it is clear where that side condition comes from, and we can look for rules to solve
         it. *)
      apply (simp add: t)
     apply (wpsimp wp: Q)+
  done


(* Using apply_debug *)
lemma "corres (=) P \<top> (do x \<leftarrow> f; g x od) (do y \<leftarrow> f'; g' y od)"
  (* The corres method declares a "corres" breakpoint tag that can be used with apply_debug to
     step through what it does. This is useful if the method goes too far or applies rules we
     didn't expect. The (trace) option to apply_debug allows us to see which rules were applied. *)
  apply_debug (trace) (tags "corres") (corres corres: f g simp: t wp: Q)
  continue (* guard implication *)
    continue (* application of f *)
      continue (* application of g, including solved side condition for t *)
     continue (* wpsimp+, which happens to solve all remaining goals *)
  finish
  done

lemma "corres (=) P \<top> (do x \<leftarrow> f; g x od) (do y \<leftarrow> f'; g' y od)"
  (* There is also a corres_cleanup breakpoint for further data *)
  apply_debug (trace) (tags "corres", "corres_cleanup") (corres corres: f g simp: t wp: Q)
  continue (* guard implication *)
    continue (* application of f *)
      continue (* application of g, showing side condition *)
  continue (* solve side condition (separate goal) *)
     continue (* wpsimp+, which happens to solve all remaining goals *)
  finish
  done

(* Testing corres_del: and if_split removal *)
lemma "corres (=) P \<top> (do x \<leftarrow> f; g (if X then x else z) od) (do y \<leftarrow> f'; (if X then g' y else g' z) od)"
  supply f[corres] g[corres]
  apply (fails \<open>solves \<open>corres corres_del: g term_simp: t wp: Q\<close>\<close>) (* rule g is not available *)
  apply corres (* "if" has not been split *)
      apply (succeeds \<open>corres simp_split: if_split\<close>) (* adding if_split would make progress *)
      apply (cases X; simp; corres term_simp: t)
      apply (wpsimp wp: Q)+
  done

(* Rewriting corres terms *)
lemma "corres (=) P \<top> (do x \<leftarrow> f; g x od) (do y \<leftarrow> liftM t f'; g' y od)"
  (* In this goal, corres will stop at liftM without finding a rule to apply. Unfolding
     liftM_def exposes the bare f' to the toplevel and lets it apply the existing "f" rule.
     The "t" rewrite happens to solve the now more complex side condition for g.
     Unfolding liftM_def is generally preferred to the liftM corres simp rules, because
     these transform schematic guards in ways that later hinder unification. *)
  by (corres corres: f g simp: liftM_def t wp: Q)

(* Rewriting corres terms more carefully *)
lemma "corres (=) P \<top> (do x \<leftarrow> f; g x od) (do y \<leftarrow> liftM t f'; g' y od)"
  (* "term_simp" tells corres to apply the following simp rules only to the side conditions
     of terminal corres steps, not to the corres terms themselves. Usually those simp rules
     are fairly distinct and side-condition rules don't do anything to the corres terms, so
     it's fine to put them in the "simp:" section, but occasionally we want more control. *)
  by (corres corres: f g simp: liftM_def term_simp: t wp: Q)

(* Dealing with asserts and symbolic execution *)
lemma "corres (=) P \<top> (do s \<leftarrow> get; assert (P s); x \<leftarrow> f; g x od) (do y \<leftarrow> f'; g' y od)"
  (* Here we'd like to do symbolic execution on "get" and then use the unsafe rule
     corres_assert_gen_asm_l for the assert. Often it is good enough to locally
     provide such rules as [corres], but adding corres_symb_exec_l here for instance will
     go too far. It will try to execute all of get, assert, and f: *)
  apply (corres corres: corres_symb_exec_l[where P=P])
  (* unsolvable *)
  oops

lemma "corres (=) P \<top> (do s \<leftarrow> get; assert (P s); x \<leftarrow> f; g x od) (do y \<leftarrow> f'; g' y od)"
  (* We can provide the same rule as a fallback rule. This means it will be tried only when
     no other rule has worked. This lets f and corres_assert_gen_asm_l go first. *)
  by (corres corres: corres_assert_gen_asm_l f g
             fallback: corres_symb_exec_l[where P=P]
             simp: t wp: Q)

lemma "corres (=) P \<top> (do s \<leftarrow> get; assert (P s); x \<leftarrow> f; g x od) (do y \<leftarrow> f'; g' y od)"
  (* For even more control, we can instantiate the rule further: *)
  by (corres corres: corres_assert_gen_asm_l f g
             fallback: corres_symb_exec_l[where P=P and m=get]
             simp: t wp: Q)


section "@{method corres'} and @{method corres_cleanup} parameter methods"

(* First with corres only, no cleanup method: *)
lemma "corres (=) P \<top> (do x \<leftarrow> f; g x; h od) (do y \<leftarrow> f'; g' y; h' od)"
  apply (corres corres: f g)
         (* Imagine we get here, and (simp add: t) wasn't strong enough to solve the side condition.
            Maybe we needed fastforce for it: *)
         apply (fastforce simp: t)
        (* It is absolutely fine to leave this fastforce here, and continue the corres proof *)
        apply (corres corres: h)
       apply (wpsimp wp: Q)+
  done

(* Sometimes that one fastforce is the only thing standing in the way of full automation. Providing
   the fastforce as a cleanup method can help here. *)
lemma "corres (=) P \<top> (do x \<leftarrow> f; g x; h od) (do y \<leftarrow> f'; g' y; h' od)"
  by (corres' \<open>fastforce simp: t\<close> corres: f g h wp: Q)

(* Providing "succeed" will stop at any side condition without solving it. Occasionally useful for
   debugging: *)
lemma "corres (=) P \<top> (do x \<leftarrow> f; g x; h od) (do y \<leftarrow> f'; g' y; h' od)"
  apply (corres' \<open>succeed\<close> corres: f g h term_simp: t)
         (* stops at side condition for g, even though t was available in term_simp *)
         apply (simp add: t)
        apply (corres corres: h)
       apply (wpsimp wp: Q)+
  done

(* Providing something like fastforce can lead to non-termination or slowdown, because the method
   will be tried for any side condition. If there is a distinctive goal pattern that can
   distinguish when the cleanup method should be run, you can use "match" to restrict the method: *)
lemma "corres (=) P \<top> (do x \<leftarrow> f; g x; h od) (do y \<leftarrow> f'; g' y; h' od)"
  by (corres' \<open>match conclusion in "x = t y" for x y \<Rightarrow> \<open>fastforce simp: t\<close>\<close> corres: f g h wp: Q)


section "Form of [@{attribute corres}] rules"

(* The method expects terminal corres rules to instantiate return relation and guards.
   It also expects distinct variables for the abstract and concrete side and tries hard to
   not accidentally mix these by rewriting corres terms with assumptions.

   For instance, it would be tempting to write the "g" rule as follows: *)
lemma g': "corres (=) Q \<top> (g x) (g' x)"
  by (simp add: g t)

(* This will usually not apply in the corres proof, because the goal will tend to have
   the form "corres (=) Q \<top> (g x) (g' y)" with a side condition connecting x and y, and not
   "corres (=) Q \<top> (g x) (g' x)" *)
lemma "corres (=) P \<top> (do x \<leftarrow> f; g x od) (do y \<leftarrow> f'; g' y od)"
  apply (corres corres: f g')
      (* \<And>x y. x = y \<Longrightarrow> corres (=) (?R2 x) (?R'2 y) (g x) (g' y) *)
      apply (fails \<open>rule g'\<close>)
      (* The original "g" rule from the top of this file works, because it has separate x and y *)
      apply (rule g)
      apply (wpsimp wp: Q simp: t)+
  done

(* The corres method refuses to rewrite guards for the same reason.
   Because corres is careful with keeping abstract and concrete variables separate,
   it is usually safe to interleave corres with corres_cases or corres_cases_both *)
lemma "corres (=) P \<top>
              (do x \<leftarrow> case z of None \<Rightarrow> f | Some x' \<Rightarrow> do return x'; f od; g x od)
              (do y \<leftarrow> f'; g' y od)"
  by (corres corres: f g simp: t wp: Q | corres_cases)+

(* It is usually safe to interleave corres with methods that solve their goal, such as
   fastforce, blast, etc.

   It is *not* generally safe to interleave corres with simp or clarsimp. It can occasionally be
   useful to invoke simp or clarsimp manually on corres terms with schematics, but
   generally it is unsafe and should be avoided. Use the "simp:" facility of the corres method
   instead wherever possible, because it provides some protection against common pitfalls.

   Occasionally it is useful to interleave with tactics that work on specific kinds of goals
   only, e.g. a clarsimp on goals that are not corres goals. For this, the predicate methods
   is_corres, is_wp, and is_safe_wp are available. These do not change the proof state, but they
   fail when their predicate does not hold.

   is_corres succeeds on corres goals only
   is_wp succeeds on wp goals only (valid, validE, no_fail)
   is_safe_wp succeeds only on wp goals without a schematic post condition (where wpsimp is not safe)

   Boolean combinations of predicates can be obtained with "," "|" and "fails" for "and", "or", and
   "not".
*)

(* Example of predicate methods *)
lemma "corres (=) P \<top>
              (do x \<leftarrow> case z of None \<Rightarrow> f | Some x' \<Rightarrow> do return x'; f od; g x od)
              (do y \<leftarrow> f'; g' y od)"
  (* Do case distinction and apply the corres method only to the corres goals: *)
  apply (corres_cases; (is_corres, corres corres: f g)?)
         (* Find all safe wp goals and run wpsimp on them *)
         apply (all \<open>(is_safe_wp, wpsimp wp: Q)?\<close>)
     (* Only non-corres and non-wp should remain -- fail if that is not the case *)
     apply (all \<open>fails \<open>is_corres | is_wp\<close>, simp add: t\<close>)
  done

end

end
