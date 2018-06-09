(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(*  Author:     Daniel Matichuk, NICTA/UNSW

    Solve postconditions using wp by decomposing the HOL connectives.
    The default method, wpi, is safe in the sense that it won't do anything that
    couldn't be done with hoare_vcg_imp_lift/hoare_vcg_all_lift.

    The wpi_unsafe method drops antecedents in implications with a heuristic for guessing
    whether or not its actually needed.

    Finally, wpi_dangerous drops any antecedents regardless of whether or not it seems to be
    needed.

    In all cases: antecedents which can be shown to be established iff some precondition holds
    can always be safely lifted. Any consequent that can be solved with a member of the wpi
    named_theorem will (unsafely) drop any remaining unlifted antecedents.

    Formerly "wpu" for "wp-unsafe". Now "wpi" for "wp-implications". Default behaviour
    is to be safe, with two variants to either use heuristics or indiscriminately throw away
    information.

    TODO: Many cases where lifting won't properly occur past disjunctions or
    existentials.


*)

theory WPI
imports
  "../../Eisbach_Methods"
  "../NonDetMonadLemmas"
  "WPEx"
begin

text \<open>The ML version of repeat_new is slightly faster than the Eisbach one.\<close>

method_setup repeat_new =
 \<open>Method.text_closure >> (fn m => fn ctxt => fn facts =>
   let
     fun tac i st' =
       Goal.restrict i 1 st'
       |> method_evaluate m ctxt facts
       |> Seq.map (Goal.unrestrict i)

   in SIMPLE_METHOD (SUBGOAL (fn (_,i) => REPEAT_ALL_NEW tac i) 1) facts end)
\<close>

context begin

text \<open>
      The "atomic" constant tracks our progress in decomposing the postcondition;
      A' and A are the pre and post conditions for all encountered antecedents.
      Formally it shows the fact that f preserves the connection between A and A'
      (which are usually the same).

      B collects antecedents that were lifted over but could not be shown
      to be preserved by our function. Q holds the postcondition and is eventually
      decomposed into an atomic consequent.

      The "trips" constant collects our hoare triples as we solve them.
      \<close>

private definition "atomic f A' A B Q = (\<forall>P. \<lbrace>\<lambda>s. P (A' s)\<rbrace> f \<lbrace>\<lambda>r s. P (A r s)\<rbrace>)"

private definition "trip (Bs :: bool) = Bs"


private lemma
  init: "(atomic f (\<lambda>_. True) (\<lambda>_ _. True) (\<lambda>_ _. True) Q \<Longrightarrow> trip Ts) \<Longrightarrow>
          (trip Ts \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>) \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  by (simp add: atomic_def valid_def)

private lemma
  atomic_conjE1:
  "atomic f A' A B (\<lambda>r s. Q r s \<and> Q' r s) \<Longrightarrow>
    (atomic f A' A B Q \<Longrightarrow> trip Ts) \<Longrightarrow>
    trip Ts "
  by (simp add: atomic_def trip_def)

private lemma
  atomic_conjE2:
  "atomic f A' A B (\<lambda>r s. Q r s \<and> Q' r s) \<Longrightarrow>
    (atomic f A' A B Q' \<Longrightarrow> trip Ts) \<Longrightarrow>
    trip Ts "
  by (simp add: atomic_def trip_def)

private lemma
  atomic_impE_curry:
  "atomic f A' A B (\<lambda>r s. (Q r s \<and> Q' r s) \<longrightarrow> Q'' r s) \<Longrightarrow>
    (atomic f A' A B (\<lambda>r s. Q r s \<longrightarrow> Q' r s \<longrightarrow> Q'' r s) \<Longrightarrow> trip Ts) \<Longrightarrow> trip Ts"
  by (simp add: atomic_def )

private lemma
  atomic_impE_nonpreserved:
  "atomic f A' A B (\<lambda>r s. Q r s \<longrightarrow> Q' r s) \<Longrightarrow>
    (atomic f A' A (\<lambda>r s. Q r s \<and> B r s) Q' \<Longrightarrow> trip Ts) \<Longrightarrow> trip Ts"
  by (simp add: atomic_def )




private lemma bool_function_four_cases:
  "f = Not \<or> f = id \<or> f = (\<lambda>_. True) \<or> f = (\<lambda>_. False)"
  by (auto simp add: fun_eq_iff all_bool_eq)

private lemma
  atomic_impE_preserved:
  "atomic f A' A B (\<lambda>r s. Pres r s \<longrightarrow> Q' r s) \<Longrightarrow>
  (\<And>P. \<lbrace>\<lambda>s. P (Pres' s)\<rbrace> f \<lbrace>\<lambda>r s. P (Pres r s)\<rbrace>) \<Longrightarrow>
  (atomic f (\<lambda>s. A' s \<and> Pres' s) (\<lambda>r s. A r s \<and> Pres r s) B Q' \<Longrightarrow> trip Ts) \<Longrightarrow> trip Ts"
  apply (erule meta_mp)
  apply (clarsimp simp: valid_def atomic_def)
  apply (drule_tac x=P in spec)
  apply (drule_tac x=P in meta_spec)
  apply (drule_tac x=s in spec)+
  apply (cut_tac f=P in bool_function_four_cases)
  by auto

private lemma
  atomic_allE:
  "atomic f A' A B (\<lambda>r s. \<forall>x. Q x r s) \<Longrightarrow>
    (\<And>x. atomic f A' A B (\<lambda>r s. Q x r s) \<Longrightarrow> trip (Ts x)) \<Longrightarrow> trip (\<forall>x. Ts x)"
  by (simp add: atomic_def trip_def)

private lemma
  atomic_exE:
  "atomic f A' A B (\<lambda>r s. \<exists>x. Q x r s) \<Longrightarrow>
    (\<And>x. atomic f A' A B (\<lambda>r s. Q x r s) \<Longrightarrow> trip (Ts x)) \<Longrightarrow> trip (\<exists>x. Ts x)"
  by (simp add: atomic_def trip_def)

private lemma
  atomic_disjE:
  "atomic f A' A B (\<lambda>r s. Q r s \<or> Q' r s) \<Longrightarrow>
   (atomic f A' A B (\<lambda>r s. (\<not> Q r s \<longrightarrow> Q' r s) \<and> (\<not> Q' r s \<longrightarrow> Q r s))
    \<Longrightarrow> trip Ts) \<Longrightarrow> trip Ts"
  by (simp add: atomic_def )

text \<open>Decomposing a static term is a waste of time as we know we can lift it
      out all in one go. Additionally this stops wp_drop_imp from uselessly taking it apart.\<close>


private definition "static Q = (\<lambda>r s. Q)"

private lemma
  atomic_staticE:
  "atomic f A' A B (\<lambda>(_ :: 'a) (_ :: 'b). Q) \<Longrightarrow>
    (atomic f A' A B (static Q :: ('a \<Rightarrow> 'b \<Rightarrow> bool)) \<Longrightarrow> trip Ts) \<Longrightarrow> trip Ts"
  by (simp add: atomic_def)


private lemmas atomic_elims =
   atomic_conjE1 atomic_conjE2 atomic_allE atomic_exE atomic_disjE atomic_impE_curry

text \<open>At the leaves, we try to solve the atomic consequent. We then push our solved preserved
      antecedents back into the final hoare triple.\<close>

private lemma
  atomicE:
  "atomic f A' A B Q \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> trip \<lbrace>\<lambda>s. A' s \<longrightarrow> P s\<rbrace> f \<lbrace>\<lambda>r s. A r s \<longrightarrow> Q r s\<rbrace>"
  by (auto simp add: trip_def atomic_def valid_def;blast)

text \<open>Minor annoyance because everything expects atomicE to produce a goal, but
      we don't need wp if it's static.\<close>

private lemma
  atomicE_static:
  "atomic f A' A B (static Q) \<Longrightarrow> \<lbrace>\<lambda>_. True\<rbrace> f \<lbrace>\<lambda>_ _. True\<rbrace> \<Longrightarrow>
    trip \<lbrace>\<lambda>s. A' s \<longrightarrow> Q\<rbrace> f \<lbrace>\<lambda>r s. A r s \<longrightarrow> Q\<rbrace>"
  by (auto simp add: trip_def atomic_def valid_def;blast)

lemmas atomicEs = atomicE_static atomicE

private lemma
  atomic_drop_trivial:
  "atomic f A' (\<lambda>_ _. True) (\<lambda>_ _. True) Q \<Longrightarrow> R \<Longrightarrow> R"
  by (auto simp add: trip_def)



private lemma trips_True: "trip True" by (simp add: trip_def)


text \<open>We need to push the quantifiers into the hoare triples.
      This is an unfortunate bit of manual work, but anything more than 2 levels
      of nesting is unlikely.\<close>



private lemma trips_push_all1:
  "trip (\<forall>x. \<lbrace>\<lambda>s. Q x s\<rbrace> f \<lbrace>\<lambda>r s. Q' x r s\<rbrace>) \<Longrightarrow>
    trip (\<lbrace>\<lambda>s. \<forall>x. Q x s\<rbrace> f \<lbrace>\<lambda>r s. \<forall>x. Q' x r s\<rbrace>)"
   by (simp add: trip_def valid_def; blast)

private lemma trips_push_all2:
  "trip (\<forall>x y. \<lbrace>\<lambda>s. Q x y s\<rbrace> f \<lbrace>\<lambda>r s. Q' x y r s\<rbrace>) \<Longrightarrow>
    trip (\<lbrace>\<lambda>s. \<forall>x y. Q x y s\<rbrace> f \<lbrace>\<lambda>r s. \<forall>x y. Q' x y r s\<rbrace>)"
   by (simp add: trip_def valid_def; blast)

text \<open>Existentials are hard, and we don't see them often
      as the consequent in the postcondition.
      In the case where the precondition actually needs the existential
      we can't push the outer existential into the precondition. In that case
      we fail to process the triple and it won't be lifted.

      Some more work here to allow the heuristics to drop any added implications
      if they're deemed unecessary.\<close>

private lemma trips_push_ex1:
  "trip (\<exists>x. \<lbrace>\<lambda>s. Q s\<rbrace> f \<lbrace>\<lambda>r s. Q' x r s\<rbrace>) \<Longrightarrow>
    trip (\<lbrace>\<lambda>s. Q s\<rbrace> f \<lbrace>\<lambda>r s. \<exists>x. Q' x r s\<rbrace>)"
   by (simp add: trip_def valid_def,blast)

private lemma trips_push_ex2:
  "trip (\<exists>x y. \<lbrace>\<lambda>s. Q s\<rbrace> f \<lbrace>\<lambda>r s. Q' x y r s\<rbrace>) \<Longrightarrow>
    trip (\<lbrace>\<lambda>s. Q s\<rbrace> f \<lbrace>\<lambda>r s. \<exists>x y. Q' x y r s\<rbrace>)"
   by (simp add: trip_def valid_def; blast)


lemmas trips_pushEs[elim_format] = trips_push_all1 trips_push_all2 trips_push_ex1 trips_push_ex2

private lemma trips_True_drop: "trip True \<Longrightarrow> R \<Longrightarrow> R" by -

private lemma trips_contr_drop: "trip \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_ _. False\<rbrace> \<Longrightarrow> R \<Longrightarrow> R" by -

definition "post_imp A B == A \<longrightarrow> B"

lemma trip_init:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. post_imp True (Q r s)\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  apply (erule hoare_strengthen_post)
  by (simp add: post_imp_def)

lemma trip_drop:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. post_imp (Q' r s) (Q r s)\<rbrace>"
  apply (erule hoare_strengthen_post)
  by (simp add: post_imp_def)

private lemma hoare_add_trip:
  "trip (\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>) \<Longrightarrow>
  \<lbrace>P'\<rbrace> f \<lbrace>\<lambda>r s. post_imp (Q r s \<and> Q' r s) (R r s)\<rbrace> \<Longrightarrow> \<lbrace>\<lambda>s. P s \<and> P' s\<rbrace> f \<lbrace>\<lambda>r s. post_imp (Q' r s) (R r s)\<rbrace>"
  by (auto simp: trip_def valid_def post_imp_def; blast)


lemmas post_imp_cong = imp_cong[simplified post_imp_def[symmetric]]

ML \<open>
  fun has_shared_frees t t' =
  let
    val frees = Term.add_frees t [];
    val frees' = Term.add_frees t' [];
  in
   exists (member (=) frees') frees
  end
\<close>

private method_setup shared_frees =
  \<open>Args.term -- Args.term >>
    (fn (t,t') => (fn _ =>
    SIMPLE_METHOD (fn st =>
    if Method.detect_closure_state st then Seq.empty else
    if has_shared_frees t t' then Seq.single st else Seq.empty )))\<close>

private method uses_arg for C :: "'a \<Rightarrow> 'b \<Rightarrow> bool" =
  determ \<open>(match (C) in "\<lambda>r s. ?discard_r s" (cut) \<Rightarrow> \<open>fail\<close> \<bar> _ \<Rightarrow> \<open>-\<close>)\<close>

text \<open>Here the "test" constant holds information about the logical context of the atomic postcondition
      in the original hoare triple. "f" is the function with its arguments, "C" is all the collected
      premises and "Q" is the atomic postcondition that we want to solve in isolation.

      The method succeeds if the atomic postcondition seems to not depend on its context, i.e.
      it doesn't mention variables in its premises and it is not connected to the functions
      arguments or return value (when its context is).
      \<close>

private lemma trivial_test: "atomic f a b (\<lambda>_ _. True) B \<Longrightarrow> R \<Longrightarrow> R" by -

private method tests =
determ \<open>(match premises in "atomic f _ _ C Q" (cut) for f and C Q :: "'a \<Rightarrow> 'b \<Rightarrow> bool"  \<Rightarrow> \<open>
     fails \<open>
            shared_frees C Q (* consequent shares variables with antecedent *)
          | shared_frees f C, shared_frees f Q (* both consequent and antecedent share variables with function args *)
          | uses_arg C, uses_arg Q (* consequent and antecedent depend on return value *)
          | uses_arg C, shared_frees f Q (* antecedent depends on return value, consequent depends on function args *)
          | shared_frees f C, uses_arg Q (* consequent depends on return value, antecedent depends on function args *)
          \<close>\<close>)\<close>

text \<open>This is the main worker method. It decomposes the postcondition and attempts
      to solve any atomic postconditions that pass our tests. Any successful results
      are stored in "trips", otherwise the resulting
      addition to trips is just "True" and subsequently discarded.\<close>

private method make_goals methods wp_weak wp_strong tests  =
  (repeat_new \<open>erule atomic_staticE | erule atomic_elims |
            (erule atomic_impE_preserved, solves \<open>wp_weak | wp_strong\<close>) |
             erule atomic_impE_nonpreserved\<close>,
      fails \<open>erule atomic_drop_trivial\<close>,
      (solves \<open>erule atomicEs, wp_weak\<close>
      | succeeds \<open>erule trivial_test | tests\<close>,
          determ \<open>erule atomicEs\<close>, solves \<open>wp_strong\<close>))

text \<open>Once all the triples exist we simplify them all in one go to
      find trivial or self-contradictory rules. This avoids invoking the simplifier
      once per postcondition. imp_conjL is used to curry our generated implications.

      If all the postconditions together are contradictory, the simplifier won't use it to strengthen
      the postcondition. As an optimization we simply bail out in that case, rather than
      trying to find the contradicting rules.\<close>

private lemmas simp_dels = all_simps ex_simps

method post_strengthen methods wp_weak wp_strong simp' tests =
  (rule init,
    determ \<open>make_goals \<open>wp_weak\<close> \<open>wp_strong\<close> \<open>tests\<close>,
    (elim trips_pushEs)?,
    rule trip_init\<close>,
    (simp add: imp_conjL del: simp_dels split del: if_split)?,
    determ \<open>(erule trips_True_drop trips_contr_drop hoare_add_trip)\<close>,
    simp',
    rule trip_drop,
    (rule hoare_vcg_prop)?)

text \<open>The "wpi" named theorem is used to avoid the safety heuristics, effectively
      saying that the presence of that postcondition indicates that it should always be lifted.\<close>

named_theorems wpi

private method final_simp =
  (simp del: del: simp_dels split del: if_split cong: post_imp_cong)

text \<open>By default, wpi will only solve an atomic consequent if all its antecedents
      aren't preserved. Therefore "test" is simply "fail". Unpreserved antecedents
      can only be dropped if the consequent is solved by a member of wpi.\<close>

method wpi_once uses add del declares wpi =
  (post_strengthen \<open>wp only: wpi\<close> \<open>wp add: add del: del\<close> \<open>final_simp\<close> \<open>fail\<close>)

method wpi uses add del declares wpi = ((wpi_once add: add del: del)+)[1]


text \<open>A stronger variant handles the case where some antecedents aren't
      preserved. We drop unpreserved antecedents in the case where they
      don't seem to be connected with the consequent.\<close>

method wpi_unsafe uses add del declares wpi =
  (post_strengthen \<open>wp only: wpi\<close> \<open>wp add: add del: del\<close> \<open>final_simp\<close> \<open>tests\<close>)

text \<open>The final variant will apply any rule that solves a consequent.
      Here the wpi set has the same status as the wp set, as we
      aren't using any heuristics at all.\<close>

method wpi_dangerous uses add del declares wpi =
  (post_strengthen \<open>wp add: wpi add del: del\<close> \<open>fail\<close> \<open>final_simp\<close> \<open>fail\<close>)

text \<open>With a slight abuse of the previous work we can capture the "drop" heuristic
      as a separate method. Here we don't concern ourselves with whether or not
      the lifted consequents can be solved, we just do it if it looks safe.

      This has slightly different behaviour to wpi because it backtracks over
      the chosen consequent. This allows us to "find" the right one by putting
      another method after that should solve the result.\<close>

private definition "term x = True"

private lemma
  trips_transport:
  "atomic f A' A B (static Q'') \<Longrightarrow> trip (term (\<lambda>r s. Q''))"
  "atomic f A' A B Q' \<Longrightarrow> trip (term Q')"
  by (simp add: trip_def term_def)+

private definition "post_conj A B \<equiv> A \<and> B"

lemmas post_conj_cong = conj_cong[simplified post_conj_def[symmetric]]

private lemma
  trip_term_quants:
  "trip (\<forall>x. term (Q x)) \<Longrightarrow> trip (term (\<lambda>r s. \<forall>x. Q x r s))"
  "trip (\<forall>x y. term (Q' x y)) \<Longrightarrow> trip (term (\<lambda>r s. \<forall>x y. Q' x y r s))"
  "trip (\<exists>x. term (Q x)) \<Longrightarrow> trip (term (\<lambda>r s. \<exists>x. Q x r s))"
  "trip (\<exists>x y. term (Q' x y)) \<Longrightarrow> trip (term (\<lambda>r s. \<exists>x y. Q' x y r s))"
  by (simp add: trip_def term_def)+


private lemma
  strengthen_trip_term:
  "trip (term Q') \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. post_conj (Q' r s) (Q r s)\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  by (auto simp add: trip_def atomic_def valid_def post_conj_def)

private lemma
  post_conj_drop:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. Q' r s \<and> Q r s\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. post_conj (Q' r s) (Q r s)\<rbrace>"
  by (simp add: post_conj_def)

method wp_drop_imp_internal methods tests =
  (rule init,
   repeat_new \<open>erule atomic_staticE | erule atomic_elims atomic_impE_nonpreserved\<close>,
   fails \<open>erule atomic_drop_trivial\<close>,
   succeeds \<open>erule trivial_test | tests\<close>,
   determ \<open>erule trips_transport\<close>,
   ((drule trip_term_quants)+)?,
   erule strengthen_trip_term,
   simp split del: if_split cong: post_conj_cong,
   rule post_conj_drop)

method wp_drop_imp = wp_drop_imp_internal \<open>tests\<close>

method wp_strong_drop_imp = wp_drop_imp_internal \<open>succeed\<close>

end


notepad begin
  fix P P' P'' P''' and Q Q' Q'' :: "'a \<Rightarrow> bool" and R :: "bool \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool"
      and f :: "'x \<Rightarrow> ('a,'b) nondet_monad" and D D' D'' D''' D'''' y and x :: 'x
  assume    Q[wp]: "\<lbrace>P'\<rbrace> f x \<lbrace>\<lambda>_. Q\<rbrace>" and
            Q'[wp]:"\<lbrace>P''\<rbrace> f x \<lbrace>\<lambda>_. Q'\<rbrace>" and
            C: "\<And>r s.
                (y x \<longrightarrow> D''' y) \<and>
                ((R D r s \<longrightarrow>
                 D \<and> (D'''' \<longrightarrow> y x)) \<and>
                (\<not> R D r s \<longrightarrow> Q'' s))"
  have "\<lbrace>P and P' and P'' and (\<lambda>_. D'' x \<and> D' x)\<rbrace>
          f x
        \<lbrace>\<lambda>r s. D'' x \<and> (R D r s \<longrightarrow> (Q s \<and> Q' s \<and> D \<and> (y x \<longrightarrow> D''' y) \<and> (D''''  \<longrightarrow> y x))) \<and>
                (\<not> R D r s \<longrightarrow> (Q s \<and> Q'' s))\<rbrace>"
  apply wp
  apply (wpi wpi: Q')
  apply (wpi wpi: Q)
  apply (rule hoare_strengthen_post[OF hoare_post_taut[where P=\<top>]])
  apply (simp add: C)
  using C
  apply blast
  using C
  by blast

  fix B
  assume B[wp]: "\<lbrace>\<lambda>s. B x s\<rbrace> f x \<lbrace>\<lambda>r. B x\<rbrace>"

  have "\<lbrace>B x\<rbrace> f x \<lbrace>\<lambda>r s. R D r s \<longrightarrow> B x s\<rbrace>"
  apply (rule hoare_pre)
  apply (wpi wpi: B)
  by simp

  (* wpi_dangerous will apply wp rules without any safety heuristics.
     Recommend using apply_trace to find the rules it applied
     and putting them explicitly into wpi *)

  have "\<lbrace>B x\<rbrace> f x \<lbrace>\<lambda>r s. R D r s \<longrightarrow> B x s\<rbrace>"
  apply (rule hoare_pre)
  apply (wpi_dangerous)
  by simp


  (* wpi avoids heuristics entirely, but can still lift
     over implications if we know how they are established.

     (With the usual exception that anything in the wpi set is
     lifted regardless)

     This is basically a built-in hoare_vcg_const_imp_lift and
     hoare_vcg_imp_lift, but descending into all the conjuncts
     and past quantifiers.*)

  fix C
  assume CC[wp]: "\<lbrace>C\<rbrace> f x \<lbrace>\<lambda>r s. C s\<rbrace>"
  have "\<lbrace>\<lambda>s. D \<longrightarrow> C s\<rbrace> f x \<lbrace>\<lambda>r s. D \<longrightarrow> C s\<rbrace>"
  apply (rule hoare_pre)
  apply wpi
  by simp


  (* We need to know that our precondition is equivalent to the
     antecedent of the post condition. Here it is not sufficient
     to know that CC establishes R D r s, we need to know that
     \<not> CC implies \<not> R D r s in the postcondition. This is wrapped
     up by putting it under a quantified P. *)

  fix C CC
  assume RD[wp]: "\<And>P. \<lbrace>\<lambda>s. P (CC s)\<rbrace> f x \<lbrace>\<lambda>r s. P (R D r s)\<rbrace>" and
         CC[wp]: "\<lbrace>C\<rbrace> f x \<lbrace>\<lambda>r s. C s\<rbrace>"
  have "\<lbrace>\<lambda>s. CC s \<longrightarrow> C s\<rbrace> f x \<lbrace>\<lambda>r s. R D r s \<longrightarrow> C s\<rbrace>"
  apply (rule hoare_pre)
  apply wpi
  by simp

  (* implicit connections are not captured in wpi_unsafe*)

  fix G G'
  assume Failsafe: "\<And>P. P" and
         f_G: "\<And>P :: bool \<Rightarrow> bool. \<lbrace>\<lambda>s. P (G s)\<rbrace> f x \<lbrace>\<lambda>r s. P (G s)\<rbrace>"
  have "\<lbrace>\<lambda>s . (G s \<longrightarrow> \<not> D) \<and> ((\<not>G s) \<longrightarrow> D)\<rbrace> f x \<lbrace>\<lambda>r s. (G s \<longrightarrow> \<not> D) \<and> ((\<not>G s) \<longrightarrow> D)\<rbrace>"
  apply (rule thin_rl[of W W for W])
  apply (rule hoare_pre)
  apply wpi? (* wpi doesn't know how to establish G s, so it (safely) does nothing *)
  apply wpi_unsafe (* the heuristics fail here for wpi_unsafe, backing us into a corner *)
  apply ((rule Failsafe)+)[2]

  apply (rule hoare_pre)
  apply (wpi add: f_G) (* by adding f_G to the wp set, we can safely lift over G *)
  by simp

end

(* wpu can handle lifting under quantifiers as well.
   Note that this case is safe because the antecedent under the
   quantifier is preserved by the function. *)


notepad begin
  fix f and Q P P' :: "int \<Rightarrow> 'a \<Rightarrow> bool" and Q' :: "'a \<Rightarrow> bool" and a

  {
  assume P[wp]: "\<And>PP x. \<lbrace>\<lambda>s. PP (P x s)\<rbrace> f a \<lbrace>\<lambda>r s. PP (P x s)\<rbrace>"
        and Q[wp]: "\<And>x. \<lbrace>\<lambda>s. Q x s\<rbrace> f a \<lbrace>\<lambda>r s. Q x s\<rbrace>"
  have "\<lbrace>\<lambda>s. \<forall>x. P x s \<longrightarrow> Q x s\<rbrace> f a \<lbrace>\<lambda>r s. \<forall>x. P x s \<longrightarrow> Q x s\<rbrace>"
  apply (rule hoare_pre)
  apply wpi
  by simp
  }

  {
  fix Q'' Q'
  assume Q[wp]:"\<And>x. \<lbrace>\<lambda>s. Q x s\<rbrace> f a \<lbrace>\<lambda>r s. Q x s\<rbrace>" and
         Q''[wp]:"\<lbrace>\<lambda>s. Q'' s\<rbrace> f a \<lbrace>\<lambda>r s. Q'' s\<rbrace>"
         and Failsafe: "\<And>P. P"
  have "\<lbrace>\<lambda>s. \<forall>x. P x s \<longrightarrow> Q x s\<rbrace> f a \<lbrace>\<lambda>r s. \<forall>x. P x s \<longrightarrow> (Q'' s \<and> Q x s)\<rbrace>"
  apply (rule thin_rl[of W W for W])
    apply (rule hoare_pre)
    apply wpi? (* wpi fails because P isn't known to be preserved by f *)
    apply wpi_unsafe+ (* wpi_unsafe can lift Q'' out because it doesn't depend on x,
                        but Q is left in place because both it and P depend on x
                        and P isn't preserved by f *)
    apply (wpi wpi: Q) (* we can force it through with the wpi set *)
    apply simp (* now we're stuck because we don't have P *)
    apply (rule Failsafe) (* bail out *)

    apply (rule hoare_pre)
    apply wpi_dangerous+ (* this forces Q through regardless. We lose P again. *)
    apply simp (* again we've lost P *)

    (* This goal is actually not solvable because, in general, f could establish P from nothing *)

    by (rule Failsafe)


  }



  (* Multiple nested universal quantifiers can be safely lifted over. *)

  {
  assume P[wp]: "\<And>PP x. \<lbrace>\<lambda>s. PP (P x s)\<rbrace> f a \<lbrace>\<lambda>r s. PP (P x s)\<rbrace>" and
         P'[wp]: "\<And>PP x. \<lbrace>\<lambda>s. PP (P' x s)\<rbrace> f a \<lbrace>\<lambda>r s. PP (P' x s)\<rbrace>"
         and Q[wp]: "\<lbrace>\<lambda>s. \<forall>x. P' x s \<longrightarrow> Q' s\<rbrace> f a \<lbrace>\<lambda>r s. Q' s\<rbrace>"
  have "\<lbrace>\<lambda>s. Q' s\<rbrace> f a \<lbrace>\<lambda>r s. \<forall>x. P x s \<longrightarrow> (\<forall>y. P' y s \<longrightarrow> Q' s)\<rbrace>"
  apply (rule hoare_pre)
  apply wpi
  by simp
  }

end


end
