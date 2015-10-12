(*  Title:      Eisbach_WP.thy
    Author:     Daniel Matichuk, NICTA/UNSW
    
    WP-specific Eisbach methods
*)

theory Eisbach_WP
imports "../Eisbach_Methods" NonDetMonadVCG "../Conjuncts" "../Rule_By_Method"
        
begin

text \<open>Strengthening postconditions automatically using wp\<close>

text \<open>TODO: Handle quantifiers in the post condition\<close>

context begin


text \<open>A small wrapper around implication so we can track assumptions we've added.\<close>


definition "strong_post P Q \<equiv> P \<longrightarrow> Q"

lemmas strong_post_cong = imp_cong[simplified strong_post_def[symmetric]]

text \<open>A small utility method which succeeds only when two given terms share free variables.\<close>

ML \<open>
  fun has_shared_frees t t' =
  let
    val frees = Term.add_frees t [];
    val frees' = Term.add_frees t' [];
  in
   exists (member (op =) frees') frees
  end
\<close>

method_setup shared_frees =
  \<open>Args.term -- Args.term >> 
    (fn (t,t') => (fn _ =>
    SIMPLE_METHOD (
      if has_shared_frees t t' then all_tac else no_tac)))\<close>


text \<open>Our counterpart to hoare_add_post.\<close>

lemma hoare_strong_post:
  "\<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> 
  \<lbrace>P''\<rbrace> f \<lbrace>\<lambda>r s. strong_post (Q r s) (H r s)\<rbrace> \<Longrightarrow> \<lbrace>\<lambda>s. P' s \<and> P'' s\<rbrace> f \<lbrace>\<lambda>r s. H r s\<rbrace>"
  by (fastforce simp add: valid_def strong_post_def)

text \<open>Similar for hoare_drop_imps. Note we can repeatedly apply this without clobbering
      the original post condition.\<close>

private lemma drop_strong_post:
  "\<lbrace>P\<rbrace> f \<lbrace>R\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. strong_post (Q r s) (R r s)\<rbrace>"
  apply (erule hoare_strengthen_post)
  by (simp add: strong_post_def)


text \<open>Simple test for if a function uses its first argument. This method will fail if
      handed a post condition which ignores the return value.\<close>

method uses_arg for C :: "'a \<Rightarrow> 'b \<Rightarrow> bool" =
  (match (C) in "\<lambda>r s. ?discard_r s" (cut) \<Rightarrow> \<open>fail\<close> \<bar> _ \<Rightarrow> \<open>-\<close>)

text \<open>Here "f" is the function with its arguments, C is the logical context of the post condition,
      built up as we peel off implications, and Q is the postcondition we are decomposing
      (and assumed to be atomic in the final match case).
      
      We decompose the postcondition, and assume its atomic parts given that we know how to 
      solve them in isolation. wp_weak tries to solve the generated triple regardless, while
      wp_strong is only applied given some safety checks on the logical context.\<close>

method find_context for f :: 'd  and C Q :: "'a \<Rightarrow> 'b \<Rightarrow> bool"  methods wp_weak wp_strong =
  (match (Q) in 
    "\<lambda>r s. Q' r s \<and> Q'' r s" (cut) for Q' Q'' :: "'a \<Rightarrow> 'b \<Rightarrow> bool" \<Rightarrow>
       \<open>find_context f C Q' \<open>wp_weak\<close> \<open>wp_strong\<close> , find_context f C Q'' \<open>wp_weak\<close> \<open>wp_strong\<close> \<close>
  \<bar> "\<lambda>r s. Q' r s \<longrightarrow> Q'' r s" (cut)  for Q' Q'' :: "'a \<Rightarrow> 'b \<Rightarrow> bool" \<Rightarrow>
       \<open>find_context f "\<lambda>r s. C r s \<and> Q' r s" Q'' \<open>wp_weak\<close> \<open>wp_strong\<close> \<close>
  \<bar> "\<lambda>r s. if A r s then Q' r s else Q'' r s" (cut) for A Q' Q'' :: "'a \<Rightarrow> 'b \<Rightarrow> bool" \<Rightarrow>
       \<open>find_context f "\<lambda>r s. C r s \<and> A r s" Q' \<open>wp_weak\<close> \<open>wp_strong\<close> , find_context f "\<lambda>r s. C r s \<and> \<not> A r s"  Q''\<open>wp_weak\<close> \<open>wp_strong\<close>\<close>
  \<bar> "\<lambda>r s. Q' r s \<or> Q'' r s" (cut) for Q' Q'' :: "'a \<Rightarrow> 'b \<Rightarrow> bool" \<Rightarrow>
       \<open>find_context f "\<lambda>r s. C r s \<and> (\<not> Q'' r s)" Q' \<open>wp_weak\<close> \<open>wp_strong\<close> , find_context f "\<lambda>r s. C r s \<and> (\<not> Q' r s)" Q'' \<open>wp_weak\<close> \<open>wp_strong\<close> \<close>
  \<bar> "\<lambda>r. Q' r and Q'' r" (cut)  for Q' Q'' :: "'a \<Rightarrow> 'b \<Rightarrow> bool" \<Rightarrow>
       \<open>find_context f C Q' \<open>wp_weak\<close> \<open>wp_strong\<close> , find_context f C Q'' \<open>wp_weak\<close> \<open>wp_strong\<close>\<close>    
     
       
  \<bar> _ \<Rightarrow> 
  \<open>(rule hoare_strong_post[where Q=Q], (* see if we know how to prove Q *)
   (solves \<open>wp_weak\<close> (* try our more specific solver first (wp only: ...) *)
   |(match (C) in "\<lambda>_ _. True" \<Rightarrow> \<open>succeed\<close> (* optimization: without context lifting is always safe *)
    \<bar> _ \<Rightarrow> \<open>fails \<open>
            shared_frees C Q (* consequent shares variables with antecedent *) 
          | shared_frees f C, shared_frees f Q (* both consequent and antecedent share variables with function args *)
          | uses_arg C, uses_arg Q (* consequent and antecedent depend on return value *)
          | uses_arg C, shared_frees f Q (* antecedent depends on return value, consequent depends on function args *)
          | shared_frees f C, uses_arg Q (* consequent depends on return value, antecedent depends on function args *) 
          \<close>\<close>),  
    solves \<open>wp_strong\<close> (* if we can assume that we don't actually depend on our logical context, try the real solver (wp) *)
    ))?\<close>
   )


text \<open>After matching the conclusion we are now focused and can't affect the schematic precondition.
      To work around this, we replace the precondition with a schematic that we can resolve after
      focusing.\<close>

definition "schematic_equiv P P' \<equiv> (P \<equiv> P')" 

lemma
  hoare_pre_schematic_equiv: 
  "\<lbrace>Q\<rbrace> a \<lbrace>R\<rbrace> \<Longrightarrow> (\<And>s. PROP schematic_equiv (Q s) (P s))\<Longrightarrow> \<lbrace>P\<rbrace> a \<lbrace>R\<rbrace>"
  by (simp add: schematic_equiv_def valid_def)
  

lemma schematic_equivI: "PROP schematic_equiv P P" 
  by (simp add: schematic_equiv_def)
 

text \<open>We focus, schematic-ify the precondition, 
      then we enrich the postcondition. We then simplify it
      (with our own congruence rule) and then drop our enriched postconditions.

      Note that ";" limits us to the first subgoal, so defer_tac only pushes our generated
      subgoal down by 1, leaving us with the original hoare triple after solving it with  
      schematic_equivI.
\<close>


method post_strengthen methods wp_weak wp_strong simp' =
  (match conclusion in "\<lbrace>_\<rbrace> f \<lbrace>Q\<rbrace>" for Q f \<Rightarrow>
    \<open>rule hoare_pre_schematic_equiv, find_context f "\<lambda>_ _. True" Q \<open>wp_weak\<close> \<open>wp_strong\<close>\<close>, 
   defer_tac, rule schematic_equivI,
   simp'; 
    ((rule drop_strong_post)+)
  )

named_theorems wpstr

method wpstr uses add del declares wpstr = 
  (post_strengthen \<open>wp only: wpstr\<close> \<open>wp add: add del: del\<close> \<open>simp split del: split_if cong: strong_post_cong\<close>)

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
  apply wpstr
  apply (rule hoare_strengthen_post[OF hoare_post_taut[where P=\<top>]])
  apply (rule C)
  by simp

  fix B
  assume B[wp]: "\<lbrace>\<lambda>s. B x s\<rbrace> f x \<lbrace>\<lambda>r s. B x s\<rbrace>"

  have "\<lbrace>B x\<rbrace> f x \<lbrace>\<lambda>r s. R D r s \<longrightarrow> B x s\<rbrace>"
  apply (rule hoare_pre)
  apply (wpstr wpstr: B)
  apply wp
  by simp
 

end


text \<open> 
  Methods for manipulating the post conditions of hoare triples as if they
  were proper subgoals. I'm not convinced they are actually that useful anymore,
  as the wpstr method mostly subsumes my intended use for them. 

\<close>
context begin

definition "packed_valid P f si r s \<equiv> P si \<and> (r, s) \<in> fst (f si)"

lemma packed_validE:"(\<And>si r s. packed_valid P f si r s \<Longrightarrow> Q r s) \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  by (clarsimp simp: valid_def packed_valid_def)

lemma packed_validI: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> \<forall>si r s. packed_valid P f si r s \<longrightarrow> Q r s"
  apply (clarsimp simp: valid_def packed_valid_def)
  by auto

definition "packed_validR P f si r s \<equiv> P si \<and> (Inr r, s) \<in> fst (f si)"


lemma packed_validRE:"(\<And>si r s. packed_validR P f si r s \<Longrightarrow> Q r s) \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-"
  apply (clarsimp simp: validE_R_def validE_def valid_def packed_validR_def)
  by (metis sum.case sumE)

lemma packed_validRI: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,- \<Longrightarrow> \<forall>si r s. packed_validR P f si r s \<longrightarrow> Q r s"
  apply (clarsimp simp: valid_def validE_R_def validE_def packed_validR_def)
  by fastforce

lemma trivial_imp: "\<forall>r s. Q r s \<longrightarrow> Q r s" by simp

lemma uncurry2: "\<forall>r s. Q r s \<and> Q' r s \<longrightarrow> Q'' r s \<Longrightarrow> \<forall>r s. Q r s \<longrightarrow> Q' r s \<longrightarrow> Q'' r s"
  by simp

named_theorems hoare_post_imps

lemmas [hoare_post_imps] = hoare_post_imp_R hoare_post_imp[rotated]

method post_asm_raw methods m = 
  (drule hoare_post_imps,
   atomize (full),
   focus_concl 
     \<open>intro impI allI, 
      m, 
      atomize (full),
      ((rule uncurry2)+)?\<close>,
   rule trivial_imp)

method post_asm methods m = 
  (post_asm_raw \<open>(simp only: bipred_conj_def pred_conj_def)?,(elim conjE)?,m\<close>)


named_theorems packed_validEs

lemmas [packed_validEs] = packed_validE packed_validRE

named_theorems packed_validIs

lemmas [packed_validIs] = packed_validI packed_validRI

method post_raw methods m = 
  (focus_concl 
    \<open>rule packed_validEs,
     focus_concl \<open>m,fold_subgoals\<close>, 
     atomize (full),
     rule packed_validI\<close>)

method post_strong methods m_distinct m_all = 
  (post_raw
     \<open>(simp only: pred_conj_def bipred_conj_def)?,
      (intro impI conjI allI)?,
      distinct_subgoals_strong \<open>m_distinct\<close>,
      all \<open>m_all\<close>,
      fold_subgoals\<close>)

method post methods m = post_strong \<open>(assumption | erule mp)+\<close> \<open>m\<close>

end


text \<open>
  Method (meant to be used with @ as an attribute) used for producing multiple facts out of 
  a single hoare triple with a conjunction in its post condition.
\<close>

context begin

private lemma hoare_decompose: 
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. Q r s \<and> Q' r s\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<and> \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>"
  by (fastforce simp add: valid_def pred_conj_def)

private lemma hoare_decomposeE_R: 
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. Q r s \<and> Q' r s\<rbrace>,- \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,- \<and> \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>,-"
  by (fastforce simp add: validE_R_def validE_def valid_def pred_conj_def split: prod.splits sum.splits)

private lemma hoare_decomposeE_E: 
  "\<lbrace>P\<rbrace> f -,\<lbrace>\<lambda>r s. Q r s \<and> Q' r s\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f -,\<lbrace>Q\<rbrace> \<and> \<lbrace>P\<rbrace> f -,\<lbrace>Q'\<rbrace>"
  by (fastforce simp add: validE_E_def validE_def valid_def pred_conj_def split: prod.splits sum.splits)

private lemma hoare_decomposeE:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. E r s \<and> E' r s\<rbrace>,\<lbrace>\<lambda>r s. R r s \<and> R' r s\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>E\<rbrace>,- \<and> \<lbrace>P\<rbrace> f \<lbrace>E'\<rbrace>,- \<and> \<lbrace>P\<rbrace> f -,\<lbrace>R\<rbrace> \<and> \<lbrace>P\<rbrace> f -,\<lbrace>R'\<rbrace>"
  by (fastforce simp add: validE_R_def validE_E_def validE_def valid_def pred_conj_def split: prod.splits sum.splits)

private lemmas hoare_decomposes' = hoare_decompose hoare_decomposeE_R hoare_decomposeE_E hoare_decomposeE

private method add_pred_conj = (subst pred_conj_def[symmetric])
private method add_bipred_conj = (subst bipred_conj_def[symmetric])

private lemmas hoare_decomposes[THEN conjE] = 
  hoare_decomposes' 
  hoare_decomposes'[# \<open>add_pred_conj\<close>]
  hoare_decomposes'[# \<open>add_bipred_conj\<close>]
  hoare_decomposeE[# \<open>add_pred_conj, add_pred_conj\<close>]
  hoare_decomposeE[# \<open>add_bipred_conj, add_pred_conj\<close>]
  hoare_decomposeE[# \<open>add_pred_conj, add_bipred_conj\<close>]
  hoare_decomposeE[# \<open>add_bipred_conj, add_bipred_conj\<close>]

method hoare_decompose = (elim hoare_decomposes)

end


notepad begin
  fix A :: "'a \<Rightarrow> bool" and B C D f
  assume A: "\<And>s. A s = True" and
         B: "\<And>s :: 'a. B s = True" and
         C: "\<And>s :: 'a. C s = True" and
         D: "\<And>s :: 'a. D s = True" and
         f: "f = (return () :: ('a,unit) nondet_monad)"

  have f_valid[@ \<open>hoare_decompose\<close>,conjuncts]: "\<lbrace>A\<rbrace> f \<lbrace>\<lambda>_. B and C and D\<rbrace>"
  apply (simp add: f)
  apply wp
  by (simp add: B C D)

  note f_valid' = conjuncts

  have f_d: "\<lbrace>A\<rbrace> f \<lbrace>\<lambda>_. D\<rbrace>" by (rule f_valid')

  have f_valid_interm: "\<lbrace>A\<rbrace> f \<lbrace>\<lambda>_. B and C and (\<lambda>s. D s \<longrightarrow> B s)\<rbrace>"
  apply (post_strong \<open>simp\<close> \<open>-\<close>)
  apply (wp f_valid')
  by simp
    
  (* All rotations are attempted when strengthening *)

  have f_valid_interm: "\<lbrace>A\<rbrace> f \<lbrace>\<lambda>_. (\<lambda>s. D s \<longrightarrow> B s) and B and C \<rbrace>"
  apply (post_strong \<open>simp\<close> \<open>-\<close>, wp f_valid')
  by simp

end




end