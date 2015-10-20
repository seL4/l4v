(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(*  Title:      WPU.thy
    Author:     Daniel Matichuk, NICTA/UNSW
    
    Solve postconditions using wp by decomposing the HOL connectives.
    Can potentially generate preconditions that are too strong by throwing away assumptions.
    Uses heuristics to guess whether or not assumptions are actually necessary for each
    atomic postcondition. These can be overridden by explicitly putting wp rules into the "wpu"
    set or by using wpu_risky.
    
*)

theory WPU
imports "../Eisbach_Methods" NonDetMonadVCG
        
begin

text \<open>The ML version of repeat_new is slightly faster than the Eisbach one.\<close>

method_setup repeat_new =
 \<open>Method_Closure.parse_method >> (fn m => fn ctxt => fn facts =>
   let
     fun tac i st' =
       Goal.restrict i 1 st'
       |> Method_Closure.method_evaluate m ctxt facts
       |> Seq.map (Goal.unrestrict i o snd)

   in SIMPLE_METHOD (SUBGOAL (fn (_,i) => REPEAT_ALL_NEW tac i) 1) facts end)
\<close>

context begin

text \<open>Some dummy constants used to track our progress on decomposing the state.
      We want one goal for each atom in the postcondition, with a schematic postcondition
      for each. This will collect our solved hoare triples.

      We also need to track the new variables introduced through
      decomposing universal or existential quantifiers, so we can re-quantify
      over them in the final hoare triple. Note that existentials are coerced into
      unversals implicitly.

      This is version 2 of the original wpstr from Eisbach_WP, but uses a rule-guided approach
      rather than a recursive match. This is necessary to correctly handle quantifiers,
      as we need to dynamically build a list of new variables at run-time.
      \<close>

private definition "atomic f l B = True"
private definition "test f (A :: 'a) (B :: 'a) = True"

private definition "term x = ()"
private definition "pprem B = True"
private definition "trips (Bs :: bool) = Bs"

private lemma
  init: "(atomic f [] Q \<Longrightarrow> trips Bs) \<Longrightarrow> (trips Bs \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>) \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  by (simp add: atomic_def)

private lemma
  atomic_conjE: 
  "atomic f l (\<lambda>r s. Q r s \<and> Q' r s) \<Longrightarrow> (atomic f l Q \<Longrightarrow> trips A) \<Longrightarrow> (atomic f l Q' \<Longrightarrow> trips B) \<Longrightarrow> trips (A \<and> B)"
  by (simp add: atomic_def trips_def)

private lemma
  atomic_impE: 
  "atomic f l (\<lambda>r s. Q r s \<longrightarrow> Q' r s) \<Longrightarrow> (pprem Q \<Longrightarrow> atomic f l Q' \<Longrightarrow> trips A) \<Longrightarrow> trips A"
  by (simp add: atomic_def pprem_def)

private lemma
  atomic_allE: 
  "atomic f l (\<lambda>r s. \<forall>x. Q x r s) \<Longrightarrow> (\<And>x. atomic f ((term x) # l) (\<lambda>r s. Q x r s) \<Longrightarrow> R) \<Longrightarrow> R"
  by (simp add: atomic_def pprem_def)

private lemma
  atomic_exE: 
  "atomic f l (\<lambda>r s. \<exists>x. Q x r s) \<Longrightarrow> (\<And>x. atomic f ((term x) # l) (\<lambda>r s. Q x r s) \<Longrightarrow> R) \<Longrightarrow> R"
  by (simp add: atomic_def pprem_def)

private lemma
  atomic_disjE: 
  "atomic f l (\<lambda>r s. Q r s \<or> Q' r s) \<Longrightarrow> 
  (pprem (\<lambda>r s. \<not> Q' r s) \<Longrightarrow> atomic f l Q \<Longrightarrow> trips A) \<Longrightarrow> 
  (pprem (\<lambda>r s. \<not> Q r s) \<Longrightarrow> atomic f l Q' \<Longrightarrow> trips B) \<Longrightarrow> 
  trips (A \<and> B)"
  by (simp add: atomic_def pprem_def trips_def)

private lemmas atomic_elims = atomic_conjE atomic_impE atomic_allE atomic_exE atomic_disjE

text \<open>Our generated schematic "trips" won't have access to any introduced variables, so
      we quantify over them as needed to express the postcondition.

      The proper general solution involves generating these on the fly, but this is
      good enough for most cases.\<close>

private lemma
  atomicE: 
  "atomic f l Q \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> trips \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  by (simp add: trips_def)

private lemma
  atomicE_all1: 
  "atomic f [term x] (Q x) \<Longrightarrow> (\<And>x. \<lbrace>P\<rbrace> f \<lbrace>Q x\<rbrace>) \<Longrightarrow> trips (\<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. \<forall>x. Q x r s\<rbrace>)"
  by (simp add: trips_def valid_def, blast)

private lemma
  atomicE_all2: 
  "atomic f [term x, term y] (Q x y) \<Longrightarrow> (\<And>x y. \<lbrace>P\<rbrace> f \<lbrace>Q x y\<rbrace>) \<Longrightarrow> trips (\<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. \<forall>x y. Q x y r s\<rbrace>)"
  by (simp add: trips_def valid_def,blast)

private lemma
  atomicE_all3: 
  "atomic f [term x, term y, term z] (Q x y z) \<Longrightarrow> (\<And>x y z. \<lbrace>P\<rbrace> f \<lbrace>Q x y z\<rbrace>) \<Longrightarrow> 
    trips (\<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. \<forall>x y z. Q x y z r s\<rbrace>)"
  by (simp add: trips_def valid_def,blast)

private lemmas atomicEs = atomicE atomicE_all1 atomicE_all2 atomicE_all3

text \<open>Some helper lemmas for folding up all our prems into one conjunct.\<close>

private definition "pprems A B = True"

private lemma pprem_fold: "pprem A \<Longrightarrow> (pprems A B \<Longrightarrow> R) \<Longrightarrow> R" by (simp add: pprem_def pprems_def)

private lemma pprems: "pprem B \<Longrightarrow> pprems A B \<Longrightarrow> R \<Longrightarrow> R" by -

private lemma pprems_pprem: "pprems A B \<Longrightarrow> (pprem (\<lambda>r s. A r s \<and> B r s) \<Longrightarrow> R) \<Longrightarrow> R" by (simp add: pprem_def pprems_def)

(* \<lbrakk>pprem A; pprem B; pprem C; P\<rbrakk> \<Longrightarrow> R  
   --------------------------------
   \<lbrakk>pprem (\<lambda>r s. A r s \<and> B r s \<and> C r s); P\<rbrakk> \<Longrightarrow> R
*)


private lemma make_test: 
  "pprem A \<Longrightarrow> atomic f l Q \<Longrightarrow> test f A Q"
  by (simp add: test_def)

private lemma make_test_simple: 
  "atomic f l Q \<Longrightarrow> test f (\<lambda>_ _. True) Q"
  by (simp add: test_def)

private lemma trips_True: "trips True" by (simp add: trips_def)


private definition "tripss A B = B"

private lemma trips_conjE: 
  "trips (A \<and> B) \<Longrightarrow> (trips A \<Longrightarrow> trips B \<Longrightarrow> R) \<Longrightarrow> R"
  by (simp add: trips_def)


private lemma trips_True_drop: "trips True \<Longrightarrow> R \<Longrightarrow> R" by -

private lemma trips_contr_drop: "trips \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_ _. False\<rbrace> \<Longrightarrow> R \<Longrightarrow> R" by -

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
  "trips (\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>) \<Longrightarrow>
  \<lbrace>P'\<rbrace> f \<lbrace>\<lambda>r s. post_imp (Q r s \<and> Q' r s) (R r s)\<rbrace> \<Longrightarrow> \<lbrace>\<lambda>s. P s \<and> P' s\<rbrace> f \<lbrace>\<lambda>r s. post_imp (Q' r s) (R r s)\<rbrace>"
  by (auto simp: trips_def valid_def post_imp_def; blast)

private lemma hoare_drop_trip: 
  "trips (\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>) \<Longrightarrow> R \<Longrightarrow> R" 
  by -

lemmas post_imp_cong = imp_cong[simplified post_imp_def[symmetric]]

ML \<open>
  fun has_shared_frees t t' =
  let
    val frees = Term.add_frees t [];
    val frees' = Term.add_frees t' [];
  in
   exists (member (op =) frees') frees
  end
\<close>

private method_setup shared_frees =
  \<open>Args.term -- Args.term >> 
    (fn (t,t') => (fn _ =>
    SIMPLE_METHOD (fn st =>
    if Method_Closure.is_dummy st then Seq.empty else
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

private lemma trivial_test: "test f (\<lambda>_ _. True) B \<Longrightarrow> R \<Longrightarrow> R" by -

private method tests =
  (erule trivial_test 
 | match premises in "test f C Q" (cut) for f and C Q :: "'a \<Rightarrow> 'b \<Rightarrow> bool"  \<Rightarrow> \<open>
     fails \<open>
            shared_frees C Q (* consequent shares variables with antecedent *) 
          | shared_frees f C, shared_frees f Q (* both consequent and antecedent share variables with function args *)
          | uses_arg C, uses_arg Q (* consequent and antecedent depend on return value *)
          | uses_arg C, shared_frees f Q (* antecedent depends on return value, consequent depends on function args *)
          | shared_frees f C, uses_arg Q (* consequent depends on return value, antecedent depends on function args *) 
          \<close>\<close>)

text \<open>This is the main worker method. It decomposes the postcondition and attempts
      to solve any atomic postconditions that pass our tests. Any successful results
      are stored in "trips", otherwise the resulting
      addition to trips is just "True" and subsequently discarded.\<close>

private method make_goals methods wp_weak wp_strong =
  (determ \<open>(repeat_new \<open>erule atomic_elims\<close>)?;
            (((erule pprem_fold, erule (1) pprems, erule pprems_pprem)+)?)\<close>;
      (solves \<open>erule atomicEs, wp_weak\<close>
      | succeeds \<open>(drule (1) make_test | drule make_test_simple), determ \<open>tests\<close>\<close>, 
          determ \<open>erule atomicEs\<close>, solves \<open>wp_strong\<close>
      | rule trips_True))

text \<open>Once all the triples exist we simplify them all in one go to 
      find trivial or self-contradictory rules. This avoids invoking the simplifier
      once per postcondition.

      If all the postconditions together are contradictory, the simplifier won't use it to strengthen
      the postcondition. As an optimization we simply bail out in that case, rather than
      trying to find the contradicting rules.\<close>

method post_strengthen methods wp_weak wp_strong simp' =
  (rule init, 
    determ \<open>make_goals \<open>wp_weak\<close> \<open>wp_strong\<close>,
    (elim trips_conjE)?,
    rule trip_init\<close>,
    (simp split del: split_if)?,
    determ \<open>(erule trips_True_drop trips_contr_drop hoare_add_trip hoare_drop_trip)+\<close>,
    simp',
    rule trip_drop)

text \<open>The "wpu" named theorem is used to avoid the safety heuristics, effectively
      saying that the presence of that postcondition indicates that it should always be lifted.\<close>

named_theorems wpu

text \<open>We obligate the simplifier to make additional progress in the presence of the
      post_imp congruence rule. This enforces that wpu only succeeds when it
      has made some measurable progress, which avoids looping.\<close>

private method final_simp =
  ((simp split del: split_if)?, simp split del: split_if cong: post_imp_cong) 

method wpu uses add del declares wpu = 
  (post_strengthen \<open>wp only: wpu\<close> \<open>wp add: add del: del\<close> \<open>final_simp\<close>)

method wpu_risky uses add del = 
  (post_strengthen \<open>wp add: add del: del\<close> \<open>fail\<close> \<open>final_simp\<close>)

end

notepad begin
  fix P P' P'' P''' and Q Q' Q'' :: "'a \<Rightarrow> bool" and R :: "bool \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool"
      and f :: "'x \<Rightarrow> ('a,'b) nondet_monad" and D D' D'' D''' D'''' y and x :: 'x
  assume    A[wp]: "\<lbrace>P'\<rbrace> f x \<lbrace>\<lambda>_. Q\<rbrace>" and 
            B[wp]:"\<lbrace>P''\<rbrace> f x \<lbrace>\<lambda>_. Q'\<rbrace>" and
            C: "\<And>r s.
                (R D r s \<longrightarrow>
                 D \<and>
                 (y x \<longrightarrow> D''' y) \<and> (D'''' \<longrightarrow> y x)) \<and>
                (\<not> R D r s \<longrightarrow> Q'' s)"
  have "\<lbrace>P and P' and P'' and (\<lambda>_. D'' x \<and> D' x)\<rbrace> 
          f x 
        \<lbrace>\<lambda>r s. D'' x \<and> (R D r s \<longrightarrow> (Q s \<and> Q' s \<and> D \<and> (y x \<longrightarrow> D''' y) \<and> (D''''  \<longrightarrow> y x))) \<and> 
                (\<not> R D r s \<longrightarrow> (Q s \<and> Q'' s))\<rbrace>"
  apply (rule hoare_pre)
  apply wpu
  apply (rule hoare_strengthen_post[OF hoare_post_taut[where P=\<top>]])
  apply (rule C)
  by simp

  fix B
  assume B[wp]: "\<lbrace>\<lambda>s. B x s\<rbrace> f x \<lbrace>\<lambda>r. B x\<rbrace>"

  have "\<lbrace>B x\<rbrace> f x \<lbrace>\<lambda>r s. R D r s \<longrightarrow> B x s\<rbrace>"
  apply (rule hoare_pre)
  apply (wpu wpu: B)
  apply wp
  by simp

  (* wpu_risky will apply wp rules without any safety heuristics.
     Recommend using apply_trace to find the rules it applied
     and putting them explicitly into wpu *)

  have "\<lbrace>B x\<rbrace> f x \<lbrace>\<lambda>r s. R D r s \<longrightarrow> B x s\<rbrace>"
  apply (rule hoare_pre)
  apply (wpu_risky)
  apply wp
  by simp

  (* implicit connections are not captured, thus why wpu is unsafe *)

  fix G G' z
  have "\<lbrace>\<lambda>_. False\<rbrace> f x \<lbrace>\<lambda>r s. (G s \<longrightarrow> \<not> D) \<and> (G' s \<longrightarrow> D)\<rbrace>"
  apply (rule hoare_pre)
  apply wpu? (* we avoid introducting contradictions directly. wpu fails here *)
  apply (rule hoare_vcg_conj_lift)
  apply (wp | wpu)+ (* the contradiction of lifting over G and G' is invisible to us now *)
  apply (rule ccontr)
  by simp

end
  

end