(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory TacticTutorial imports
  Main
begin

\<comment> \<open>
  This is a simple lemma with a boring proof. We're going to replicate it in
  ML.
\<close>
lemma my_conj_commute: "(A \<and> B) = (B \<and> A)"
  apply (rule iffI)
   apply (rule conjI)
    apply (erule conjunct2)
   apply (erule conjunct1)
  apply (erule conjE)
  apply (rule conjI)
   apply assumption
  apply assumption
  done

\<comment> \<open>
  The goal of this exercise is *not* for you to have a deep and comprehensive
  understanding of every utility available to you that concerns ML tactic
  internals. The goal is for you to know the basics needed to understand the
  (somewhat sparse) documentation on tactics and how they work, and to not get
  too confused when you see them in the wild.

  However, if you *do* come up with an interesting example that demonstrates a
  principle really well, or you discover a cool and useful trick, feel free to
  add it here!
\<close>

section "Starting a proof"
ML \<open>
  \<comment> \<open>
    To start off a proof for some statement, we use @{ML "Goal.init"}.
  \<close>

  val goal_cterm = @{cterm "Trueprop ((A \<and> B) = (B \<and> A))"};
  val proof_state = Goal.init goal_cterm;

  \<comment> \<open>
    At this point, @{ML proof_state} looks like this:

    Subgoal                 (Protected) goal
    vvvvvvvvvvvvvvvvvvv     vvvvvvvvvvvvvvvvvvvvv
    (A /\ B) = (B /\ A) ==> ((A /\ B) = (B /\ A))

    This says "if you prove the subgoal(s), then you have proven the goal".
    This looks very similar to how theorems are presented; in a theorem, the
    subgoals would be called premises and the goal would be called the
    conclusion.

    In fact, in Isabelle a proof state *is* a special kind of theorem: we start
    off with the uncontroversial claim that our goal implies itself, then
    transform that theorem into one with *no* subgoals.

    In this tutorial, the section "Proof States" outlines the difference
    between a "normal" thm and a proof state, specifically what it means for
    the goal to be "protected".

    This topic is covered in the Isabelle implementation manual, section 4.1
    ("Goals").
  \<close>
\<close>

subsection "What's this Trueprop thing?"
ML \<open>
  \<comment> \<open>
    Isabelle lemmas can only talk about results in @{type prop}, but @{term "x
    = y"} is in @{type bool} (this distinction is what lets Isabelle handle
    different logics generically, like HOL vs FOL vs ZF. This idea is explained
    in more detail in the old Isabelle introduction, chapter 2 ("Formalizing
    logical rules in Isabelle")).
  
    `Trueprop` is a wrapper that does the conversion from a HOL bool to an
    Isabelle prop. However, other things are props by default, and don't need
    the `Trueprop` wrapper.
  \<close>

  val prop_cterm = @{cterm "(A \<Longrightarrow> B) :: prop"};

  val another_prop_cterm = @{cterm "(A \<equiv> B) :: prop"}
\<close>

section "Modifying proof state"
ML \<open>
  \<comment> \<open>
    To recap, our @{ML proof_state} is currently this:
  
    Subgoal                   Goal
    vvvvvvvvvvvvvvvvvvvvv     vvvvvvvvvvvvvvvvvvvvv
    ((A /\ B) = (B /\ A)) ==> ((A /\ B) = (B /\ A))
  
    If you were writing an apply script, you'd use @{method rule} here. The
    equivalent is @{ML resolve_tac}.
  \<close>

  val proof_state =
      proof_state |> resolve_tac @{context} @{thms iffI} 1 |> Seq.hd;

  \<comment> \<open>
    Now our proof state looks like this:

    Subgoal 1               Subgoal 2               Goal
    vvvvvvvvvvvvvvvvvvv     vvvvvvvvvvvvvvvvvvv     vvvvvvvvvvvvvvvvvvvvv
    (A /\ B ==> B /\ A) ==> (B /\ A ==> A /\ B) ==> ((A /\ B) = (B /\ A))

    Our old subgoal is gone, and has been replaced by the subgoals introduced
    by @{thm iffI}.
  \<close>

  \<comment> \<open>
    Let's look at the signature of `resolve_tac`:

    @{ML "resolve_tac: Proof.context -> thm list -> int -> tactic"}

    - The proof context is the same mysterious global state that gets passed
      around all over the place in most Isabelle/ML code.

    - The thm list is the list of facts that `resolve_tac` will try and use to
      change the subgoal (like @{method rule}).

    - The int (`1` in our call) specifies which subgoal to work on. Notice that
      this means we can't use it to modify the final goal.

    The result of `resolve_tac` is a tactic, which is a type alias for
    @{ML_type "thm -> thm Seq.seq"}. A tactic takes a thm (a proof state) and
    produces a lazy list of new thms (new proof states). We get the first such
    new proof state with @{ML "Seq.hd"}

    A tactic can succeed or fail.
    - If it failed, the resulting `seq` will be empty.
    - If it succeeded, the `seq` will have one or more new proof states (for
      example, if we passed more than one thm to `resolve_tac`, we'd get a
      result for each successfully resolved thm).
    For now, we're going to use tactics that will return either zero or one new
    proof states.

    The signature @{ML_type "int -> tactic"} *almost always* means "a tactic
    that can be applied to a specific subgoal", but sometimes the int means
    something else.

    Now that we have two subgoals, we can see what happens if we use a rule on
    something other than the first subgoal.
  \<close>

  val after_rule_on_2nd_subgoal =
      proof_state |> resolve_tac @{context} @{thms conjI} 2 |> Seq.hd;

  \<comment> \<open>
    The proof state @{ML after_rule_on_2nd_subgoal} looks like this:

    Subgoal 1 (old)         Subgoal 2 (new)    Subgoal 3 (new)    Goal
    vvvvvvvvvvvvvvvvvvv     vvvvvvvvvvvvvv     vvvvvvvvvvvvvv     vvvvvvvvvvvvvvvvvvvvv
    (A /\ B ==> B /\ A) ==> (B /\ A ==> A) ==> (B /\ A ==> B) ==> ((A /\ B) = (B /\ A))

    The result isn't very surprising, if you're used to using `rule`.
    `resolve_tac` matched the conclusion of @{thm conjI} against the conclusion
    of the second subgoal of @{ML proof_state}, then asks us to prove the
    premises of @{thm conjI} with the premises of the (original) second
    subgoal.
  \<close>
\<close>

subsection "Subgoals and apply scripts"
\<comment> \<open>
  If we look at the definition of @{method rule}, we see that it uses @{ML
  "HEADGOAL"} and @{ML "Classical.rule_tac"}.
  - `rule_tac` is like `resolve_tac` plus some extra features.
  - `HEADGOAL` turns a tactic that can be applied to a subgoal
    (@{ML_type "int -> tactic"}) into one that only applies to the first
    subgoal.

  In fact, most apply-script methods will only use tactics that modify the
  first subgoal.  @{method tactic} lets us use an ML tactic in an apply script.
  Let's use it to apply a tactic to the second subgoal.
\<close>
lemma "X \<or> Y \<Longrightarrow> A \<and> B"
 apply (erule disjE)
  apply (tactic \<open>resolve_tac @{context} @{thms conjI} 2\<close>)
 oops

subsection "Elimination and assumption"
ML \<open>
  \<comment> \<open>
    The equivalent of @{method erule} is @{ML eresolve_tac}. Let's use it to
    solve subgoal 1, continuing from where we left off with @{ML proof_state}.
  \<close>
  val after_conjI =
      proof_state |> resolve_tac @{context} @{thms conjI} 1 |> Seq.hd;

  val after_conjunct2 =
      after_conjI |> eresolve_tac @{context} @{thms conjunct2} 1 |> Seq.hd;

  \<comment> \<open>
    Notice that, since `eresolve_tac` replaces the matched premise with any
    additional premises of the matched rule, and since `conjunct2` doesn't have
    any such premises, the relevant subgoal has just... disappeared!

    Let's deal with the rest of the subgoals, following the original apply
    script.
  \<close>
  val after_conjunct1 =
      after_conjunct2 |> eresolve_tac @{context} @{thms conjunct1} 1 |> Seq.hd;

  val after_conjE =
      after_conjunct1 |> eresolve_tac @{context} @{thms conjE} 1 |> Seq.hd;

  val after_conjI =
      after_conjE |> resolve_tac @{context} @{thms conjI} 1 |> Seq.hd;

  \<comment> \<open>
    The equivalent of @{method assumption} is @{ML assume_tac}.
  \<close>
  val after_assumptions =
      after_conjI |> assume_tac @{context} 1 |> Seq.hd
                  |> assume_tac @{context} 1 |> Seq.hd;
\<close>

subsection "Finishing off"
ML \<open>
  \<comment> \<open>
    We're done! Our proof state consists of just the original goal, with no
    subgoals.  We can confirm this (and "unwrap" our goal from the special
    protection set up by @{ML Goal.init}):
  \<close>
  val final_thm = Goal.finish @{context} after_assumptions;

  \<comment> \<open>
    Actually, we're not *quite* done. Our theorem has free variables, whereas a
    global fact must not have free variables that don't refer to something in
    the local context. This means we need to convert our free variables into
    bound ones. Thankfully there's a utility for doing that conversion.
  \<close>
  \<comment> \<open>
    TODO: the 'correct' way to do this is using @{ML "Variable.export"}, but
    it's not clear how to actually use that here (what's the "destination"
    context?).
  \<close>
  val final_thm = Thm.forall_intr_frees final_thm;

  \<comment> \<open>
    We can give our new thm a name so we can refer to it.
  \<close>
  val add_thm = Local_Theory.note ((@{binding my_cool_ML_thm}, []), [final_thm]) #> snd;

  \<comment> \<open>
    TODO: these are... magic incantations. What do they do?
  \<close>
  add_thm |> Named_Target.theory_map |> Theory.setup;
\<close>
thm my_cool_ML_thm

section Combinators
ML \<open>
  \<comment> \<open>
    Manually passing around these proof state thms, and fetching the first lazy
    result from a tactic, is very annoying. However, there are utilities for
    composing tactics.

    We're going to construct a subgoal tactic that deals with the subgoal
    @{term "A \<and> B \<Longrightarrow> B \<and> A"}.
  \<close>

  \<comment> \<open>
    Here's one way to get a fact by name without using an antiquotation.
  \<close>
  fun get_thm name =
      Facts.named name |> Proof_Context.get_fact @{context} |> hd;

  val [iffI, conjI, conjunct1, conjunct2] =
      ["iffI", "conjI", "conjunct1", "conjunct2"] |> map get_thm;

  fun resolve thm = resolve_tac @{context} [thm];
  fun eresolve thm = eresolve_tac @{context} [thm];

  val solve_commute_conjunct_goal_tac =
      resolve conjI
      THEN' eresolve conjunct2
      THEN' eresolve conjunct1;

  \<comment> \<open>
    After applying our tactic, we can confirm that the proof state is the same
    as it was after the manual application of these steps (back at
    @{ML after_conjunct1}).
  \<close>
  val result =
      Goal.init goal_cterm
      |> (HEADGOAL (resolve iffI)
         THEN HEADGOAL (solve_commute_conjunct_goal_tac)) |> Seq.hd;

  \<comment> \<open>
    If we want to apply our subgoal tactic to both subgoals at once, we can
    replace `HEADGOAL` with `ALLGOALS`. As expected, this will solve both
    subgoals.
  \<close>
  val result =
      Goal.init goal_cterm
      |> (HEADGOAL (resolve iffI)
         THEN ALLGOALS (solve_commute_conjunct_goal_tac)) |> Seq.hd;
\<close>

section "Tracing tactics"
ML \<open>
  \<comment> \<open>
    The tactic @{ML print_tac} prints all the subgoals when it's invoked, then
    passes the proof state through unchanged. Let's use it to follow what our
    @{ML solve_commute_conjunct_goal_tac} is doing.
  \<close>

  \<comment> \<open>
    `trace` wraps a subgoal-tactic with messages showing the state before and
    after the tactic was applied (and also indicating which subgoal it's
    applied to).  Note that the indicated subgoal might be *removed* in the
    "after" state.
  \<close>
  fun trace msg tac =
      let
        fun msg_before i =
            print_tac @{context} ("(subgoal " ^ Int.toString i ^ ") before " ^ msg);
        val msg_after = K (print_tac @{context} ("after " ^ msg));
      in
        msg_before THEN' tac THEN' msg_after
      end
  val tracing_tac =
      (trace "conjI" (resolve conjI))
      THEN' (trace "conjunct2" (eresolve conjunct2))
      THEN' (trace "conjunct1" (eresolve conjunct1));

  \<comment> \<open>
    The result is very verbose, but also very explicit about what changes and
    when.
  \<close>
  val result =
      Goal.init goal_cterm
      |> (HEADGOAL (resolve iffI)
         THEN ALLGOALS (tracing_tac)) |> Seq.hd;
\<close>

section "Proof States"
ML \<open>
  \<comment> \<open>
    How is @{ML "Goal.init goal_cterm"} different to
    @{ML "Thm.trivial goal_cterm"}?
    
    `Goal.init` "protects" the goal, which prevents most standard tactics from
    changing it (this is good, because otherwise a tactic might suddenly change
    *what you'll finally prove*).

    In this tutorial, the section "Subgoal Restriction" goes through an example
    of using this "protection" feature in a tactic.

    This topic is covered in the Isabelle implementation manual, section 4.1
    ("Goals").
  \<close>

  val bigger_cterm = @{cterm "A \<and> B \<Longrightarrow> B \<and> A"};
  val bigger_goal_thm = Goal.init bigger_cterm;
  val trivial_thm = Thm.trivial bigger_cterm;

  \<comment> \<open>
    `bigger_goal_thm` has one premise (a subgoal) and one conclusion (the
    goal):

    Subgoal                 Goal (protected)
    vvvvvvvvvvvvvvvvvvv     vvvvvvvvvvvvvvvvvvv
    (A /\ B ==> B /\ A) ==> (A /\ B ==> B /\ A)

    Whereas `trivial_thm` has two premises (and hence two "subgoals"):

    Subgoal 1               Subgoal 2  Goal (unprotected)
    vvvvvvvvvvvvvvvvvvv     vvvvvv     vvvvvv
    (A /\ B ==> B /\ A) ==> A /\ B ==> B /\ A

    This means that tactics which specify what subgoal they're going to modify
    can modify a part of the proof state that "should represent" the goal that
    we want to prove.
  \<close>
\<close>

section "Methods and tactics"
ML \<open>
  \<comment> \<open>
    Dummy ML declarations to make the examples in the table work.
  \<close>
  val some_ctxt = @{context};
  val some_thms = [];
\<close>
\<comment> \<open>
  Here is a rough correspondence between methods and their tactic equivalents.
  The first four "basic" tactics are documented in the Isabelle implementation
  manual, section 4.2.1 ("Resolution and assumption tactics").

  Method          | Tactic
  ----------------+-------
  @{method rule}  | @{ML resolve_tac}
  @{method erule} | @{ML eresolve_tac}
  @{method frule} | @{ML forward_tac}
  @{method drule} | @{ML dresolve_tac}
  ----------------+-----------------------------------
  @{method subst} | "subst" ~ @{ML EqSubst.eqsubst_tac}
                  | "subst (asm)" ~ @{ML EqSubst.eqsubst_asm_tac}
  ----------------+--------------------------------------------------------------
  @{method simp}  | "simp" ~ @{ML simp_tac} (only modifies conclusion of subgoal)
                  |        ~ @{ML asm_simp_tac} (can use assumptions of subgoal, e.g. to do
                  |                              proof by contradiction)
                  | "simp only: some_thms" ~
                  |      @{ML "simp_tac (clear_simpset some_ctxt addsimps some_thms)"}
\<close>

section "Method combinators and tactic combinators"
\<comment> \<open>
  These are documented in the Isabelle implementation manual, section 4.3.1
  ("Combining tactics").

  Method combinator | Tactic combinator | Subgoal tactic combinator
  ------------------+-------------------+--------------------------
  (a , b)           | @{ML THEN}        | @{ML THEN'}
  (a | b)           | @{ML ORELSE}      | @{ML ORELSE'}
  (a ; b)           | (none)            | @{ML THEN_ALL_NEW}
  a +               | @{ML REPEAT1}     | (none)
  a ?               | @{ML TRY}         | (none)
  ------------------+-------------------+--------------------
  a [n]             | (see the section on "Subgoal restriction")
\<close>

section "Subgoal restriction"
ML \<open>
  \<comment> \<open>
    How do we stop a method or tactic from modifying certain subgoals?

    The method combinator `[n]` restricts the given method to only modifying
    the first n subgoals.  This works by using the same modification protection
    that @{ML "Goal.init"} uses.

    We usually see `[n]` used with methods that heavily modify proof state in
    ways that are unsafe or hard to predict, such as @{method auto}.

    The tactic combinator @{ML Goal.SELECT_GOAL} turns a general tactic into a
    subgoal-targeted tactic, by restricting which subgoals the tactic can
    modify (side note: there's also a combinator @{ML Goal.PREFER_GOAL} which
    merely moves a specific subgoal to the "front").

    We're going to write a subgoal-targeting version of `auto` *without* using
    `SELECT_GOAL`, to learn how it works. To start, we're going to need to
    understand how to "protect" subgoals. We'll begin with a proof state with
    lots of subgoals for us to play with.
  \<close>
  val cterm = @{cterm "A \<or> B \<or> C \<or> D \<or> E \<Longrightarrow> X"};
  val goal =
      Goal.init cterm
      |> HEADGOAL (REPEAT_ALL_NEW (eresolve_tac @{context} @{thms disjE}))
      |> Seq.hd;

  \<comment> \<open>
    Our proof state has five subgoals:

    Subgoal 1                                               Subgoal 5
    vvvvvvvvv                                               vvvvvvvvv
    (A ==> X) ==> (B ==> X) ==> (C ==> X) ==> (D ==> X) ==> (E ==> X) ==>

    Goal
    vvvvvvvvvvvvvvvvvvvvvvvvvvvvv
    (A \/ B \/ C \/ D \/ E ==> X)

    In the same way that @{ML Goal.init} "protected" the final goal to prevent
    us messing with it, we can use @{ML Goal.restrict} to "protect" some
    subgoals so we can only modify the rest (hence "restricting" us).

    In the abstract, `Goal.restrict i n thm` restricts the proof state to only
    be able to modify subgoals i, i + 1, ..., i + (n - 1) (the n subgoals
    starting at subgoal i). In detail, it accomplishes this by rotating the
    first (i - 1) subgoals to the back of the subgoals list, then "protecting"
    all but the first n subgoals.
  \<close>
  val restricted = goal |> Goal.restrict 2 2;
  \<comment> \<open>
    This proof state only has two subgoals; the others are "protected", and
    can't be modified by most tactics.

    Subgoal 2     Subgoal 3
    vvvvvvvvv     vvvvvvvvv
    (B ==> X) ==> (C ==> X) ==>

    Protected "goal"
    vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv
     Protected     Protected     Protected     Doubly-protected
     subgoal 4     subgoal 5     subgoal 1     actual goal
     vvvvvvvvv     vvvvvvvvv     vvvvvvvvv     vvvvvvvvvvvvvvvvvvvvvvvvvvvvv
    ((D ==> X) ==> (E ==> X) ==> (A ==> X) ==> (A \/ B \/ C \/ D \/ E ==> X))
  \<close>

  \<comment> \<open>
    To restore the previous state, we use @{ML Goal.unrestrict}. In the
    abstract, `Goal.unrestrict i` "undoes" `Goal.restrict i n`. In detail, it
    accomplishes this by first removing a layer of protection from the goal,
    then rotating the last (i - 1) subgoals to the front.
  \<close>
  val unrestricted = restricted |> Goal.unrestrict 2;

  \<comment> \<open>
    Here, we check that the unrestricted restricted goal is the same as the
    original goal.

    This checks that the statements of the two thms are alpha-equivalent.
  \<close>
  @{assert} ((Thm.full_prop_of unrestricted) aconv (Thm.full_prop_of goal));

  \<comment> \<open>
    We're now ready to make a subgoal-targeting version of `auto_tac`.

    This isn't equivalent to the `[n]` notation (if we wanted to apply auto to
    the first i subgoals, instead of the ith subgoal, we'd replace
    `Goal.restrict i 1` with `Goal.restrict 1 i`), but it's arguably more
    useful.
  \<close>
  fun subgoal_auto_tac ctxt i =
      PRIMITIVE (Goal.restrict i 1)
      THEN (auto_tac ctxt)
      THEN PRIMITIVE (Goal.unrestrict i);
\<close>
\<comment> \<open>
  Let's check that it works.
\<close>
lemma "A = B \<and> B = C \<and> C = D \<and> D = E \<and> E = X \<Longrightarrow> A \<or> B \<or> C \<or> D \<or> E \<Longrightarrow> X"
  apply (tactic \<open>HEADGOAL (REPEAT_ALL_NEW (eresolve_tac @{context} @{thms disjE}))\<close>)
      apply (tactic \<open>subgoal_auto_tac @{context} 3\<close>) (* Only removes "C ==> X" case. *)
     apply (tactic \<open>subgoal_auto_tac @{context} 4\<close>) (* Only removes "E ==> X" case. *)
  oops
ML \<open>
  \<comment> \<open>
    For reference, here's the version that uses SELECT_GOAL (the main
    difference is that SELECT_GOAL handles the case where there's only one
    subgoal).
  \<close>
  fun better_subgoal_auto_tac ctxt = Goal.SELECT_GOAL (auto_tac ctxt);
\<close>
lemma "A = B \<and> B = C \<and> C = D \<and> D = E \<and> E = X \<Longrightarrow> A \<or> B \<or> C \<or> D \<or> E \<Longrightarrow> X"
  apply (tactic \<open>HEADGOAL (REPEAT_ALL_NEW (eresolve_tac @{context} @{thms disjE}))\<close>)
      apply (tactic \<open>better_subgoal_auto_tac @{context} 3\<close>) (* Only removes "C ==> X" case. *)
     apply (tactic \<open>better_subgoal_auto_tac @{context} 4\<close>) (* Only removes "E ==> X" case. *)
  oops

end
