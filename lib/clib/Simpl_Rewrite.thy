(*
 * Copyright 2018, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

text \<open>A simple proof method for rewriting Simpl programs under a predicate which
      is preserved by semantic equivalence.\<close>

theory Simpl_Rewrite
imports
  "Simpl-VCG.Vcg"
  "Lib.Eisbach_Methods"
  "Lib.Apply_Debug"
begin

text \<open>Definitions and lemmas for reasoning about equivalence of Simpl programs.\<close>

named_theorems C_simp
named_theorems C_simp_pre
named_theorems C_simp_simps
named_theorems C_simp_throws

locale simpl_rewrite_base =
  fixes \<Gamma> :: "'p \<Rightarrow> ('s,'p,'f) com option"
begin

text \<open>Semantic equivalence of two Simpl programs.

      Since we quantify over all possible states, this is somewhat stronger than some other
      notions of semantic equivalence. In particular, @{text ceqv} takes particular begin and
      end states as arguments, and is only defined for @{term Normal} begin and end states.\<close>

definition
  "com_eq t c c' \<equiv> t \<longrightarrow> (\<forall>s s'. \<Gamma> \<turnstile> \<langle>c,s\<rangle> \<Rightarrow> s' \<longleftrightarrow> \<Gamma> \<turnstile> \<langle>c',s\<rangle> \<Rightarrow> s')"

text \<open>@{text com_eq} assertions may be guarded. Guards enable simple conditional rewriting.\<close>

lemma com_eq_weaken_guard:
  "com_eq t c c' \<Longrightarrow> (t' \<Longrightarrow> t) \<Longrightarrow> com_eq t' c c'"
  by (simp add: com_eq_def)

lemma com_eq_guard_False:
  "com_eq False c c'"
  by (simp add: com_eq_def)

text \<open>Most @{text com_eq} simplification rules will be unguarded, however.\<close>

abbreviation
  "com_equiv \<equiv> com_eq True"

notation com_equiv (infix "\<sim>" 10)

text \<open>@{term "com_eq"} is an equivalence relation.\<close>

lemma com_eq_refl:
  "c \<sim> c"
  by (auto simp: com_eq_def)

lemma com_eq_sym:
  "c \<sim> c' \<Longrightarrow> c' \<sim> c"
  by (auto simp: com_eq_def)

lemma com_eq_trans:
  "\<lbrakk> c \<sim> c'; c' \<sim> c'' \<rbrakk> \<Longrightarrow> c \<sim> c''"
  by (auto simp add: com_eq_def)

text \<open>Structural decomposition of Simpl programs under @{term "com_eq"}.\<close>

lemma com_eq_Seq:
  "\<lbrakk> c1 \<sim> c1'; c2 \<sim> c2' \<rbrakk> \<Longrightarrow> c1;;c2 \<sim> c1';;c2'"
  unfolding com_eq_def by (auto intro: exec.Seq elim!: exec_elim_cases)

lemma com_eq_Cond:
  "\<lbrakk> c1 \<sim> c1'; c2 \<sim> c2' \<rbrakk> \<Longrightarrow> Cond b c1 c2 \<sim> Cond b c1' c2'"
  unfolding com_eq_def by (auto intro: exec.CondTrue exec.CondFalse elim!: exec_elim_cases)

lemma com_eq_While':
  assumes eq: "c \<sim> c'"
  assumes W: "\<Gamma> \<turnstile> \<langle>While b c,s\<rangle> \<Rightarrow> s'"
  shows "\<Gamma> \<turnstile> \<langle>While b c',s\<rangle> \<Rightarrow> s'"
  using W
  proof (induct "While b c" s s')
    case WhileTrue
    with eq show ?case unfolding com_eq_def by (auto elim: exec.WhileTrue)
  next
    case WhileFalse
    then show ?case by (rule exec.WhileFalse)
  qed auto

lemma com_eq_While:
  "c \<sim> c' \<Longrightarrow> While b c \<sim> While b c'"
  by (subst com_eq_def) (auto intro: com_eq_While' com_eq_While' [OF com_eq_sym])

lemma com_eq_whileAnno:
  "c \<sim> c' \<Longrightarrow> whileAnno b I V c \<sim> whileAnno b I V c'"
  by (clarsimp simp: whileAnno_def elim!: com_eq_While)

lemma com_eq_Guard:
  "c \<sim> c' \<Longrightarrow> Guard f b c \<sim> Guard f b c'"
  by (auto simp: com_eq_def intro: exec.Guard exec.GuardFault elim!: exec_elim_cases)

lemma com_eq_Catch:
  "\<lbrakk> c \<sim> c'; h \<sim> h' \<rbrakk> \<Longrightarrow> Catch c h \<sim> Catch c' h'"
  by (auto simp: com_eq_def intro: exec.CatchMiss exec.CatchMatch elim!: exec_elim_cases)

lemmas com_eq_intros =
  com_eq_Seq com_eq_Cond com_eq_While com_eq_whileAnno com_eq_Guard com_eq_Catch

text \<open>Simpl @{term Seq} is associative under @{term com_eq}.\<close>

lemma com_eq_Seq_assoc_l:
  "c1;;(c2;;c3) \<sim> (c1;;c2);;c3"
  by (clarsimp simp: com_eq_def exec_assoc)

lemma com_eq_Seq_assoc_r:
  "(c1;;c2);;c3 \<sim> c1;;(c2;;c3)"
  by (clarsimp simp: com_eq_def exec_assoc)

text \<open>Under @{term com_eq}, some Simpl elements are right-distributive w.r.t. @{term Seq}.\<close>

lemma com_eq_Cond_distrib_r:
  "Cond b (c1;;c) (c2;;c) \<sim> Cond b c1 c2 ;; c"
  by (auto simp: com_eq_def
          intro: exec.Seq exec.CondTrue exec.CondFalse
          elim!: exec_elim_cases)

lemma com_eq_Guard_distrib_r:
  "Guard f b (c1;;c2) \<sim> Guard f b c1 ;; c2"
  by (auto simp: com_eq_def
          intro: exec.Seq exec.Guard exec.GuardFault
          elim!: exec_elim_cases)

text \<open>Simplification rules should be of the form @{term "com_eq t c c'"}.

      Simplifications added to the @{thm C_simp_pre} set will be performed before
      sub-programs have been simplified. Those added to the @{thm C_simp} set
      will be performed after sub-programs have been simplified.

      Conditional simplification rules will only apply if the guard @{term t} can be
      immediately solved by @{method simp}.\<close>

lemma com_eq_Skip_Seq [C_simp]:
  "Skip;;c \<sim> c"
  apply (clarsimp simp: com_eq_def)
  apply (rule iffI)
   apply (fastforce elim!: exec_elim_cases)
  apply (case_tac s; (simp, (erule exec_elim_cases; simp)?))
  apply (rule exec.Seq, rule exec.Skip, simp)
  done

lemma com_eq_Seq_Skip [C_simp]:
  "c;;Skip \<sim> c"
  apply (clarsimp simp: com_eq_def)
  apply (rule iffI)
   apply (fastforce elim!: exec_elim_cases)
  apply (case_tac s; (simp, (erule exec_elim_cases; simp)?))
  apply (rule exec.Seq, simp)
  apply (case_tac s'; (simp, (erule exec_elim_cases; simp)?))
  apply (rule exec.Skip)
  done

lemma com_eq_Cond_empty [C_simp_pre]:
  "com_eq (b = {}) (Cond b c1 c2) c2"
  by (clarsimp simp: com_eq_def, case_tac s, auto intro: exec.CondFalse elim!: exec_elim_cases)

lemma com_eq_Cond_UNIV [C_simp_pre]:
  "com_eq (b = UNIV) (Cond b c1 c2) c1"
  by (clarsimp simp: com_eq_def, case_tac s, auto intro: exec.CondTrue  elim!: exec_elim_cases)

lemma exec_Cond_cases:
  "\<lbrakk>s \<in> b \<Longrightarrow> \<Gamma>\<turnstile> \<langle>c\<^sub>1,Normal s\<rangle> \<Rightarrow> t; s \<notin> b \<Longrightarrow> \<Gamma>\<turnstile> \<langle>c\<^sub>2,Normal s\<rangle> \<Rightarrow> t\<rbrakk> \<Longrightarrow>
  \<Gamma>\<turnstile> \<langle>Cond b c\<^sub>1 c\<^sub>2,Normal s\<rangle> \<Rightarrow> t"
  by (cases "s \<in> b") (auto intro: exec.CondTrue exec.CondFalse)

lemma com_eq_Cond_both [C_simp]:
  "Cond b c c \<sim> c"
  by (clarsimp simp: com_eq_def, case_tac s, auto intro: exec_Cond_cases elim!: exec_elim_cases)

lemma com_eq_While_empty [C_simp_pre]:
  "com_eq (b = {}) (While b c) Skip"
  by (auto simp: com_eq_def intro: exec.WhileFalse exec.Skip elim!: exec_elim_cases)

lemma com_eq_whileAnno_empty [C_simp_pre]:
  "com_eq (b = {}) (whileAnno b I V c) Skip"
  by (simp add: com_eq_While_empty whileAnno_def)

lemma com_eq_Guard_UNIV [C_simp_pre]:
  "com_eq (b = UNIV) (Guard f b c) c"
  by (clarsimp simp: com_eq_def, case_tac s, auto intro: exec.Guard elim!: exec_elim_cases)

lemma com_eq_Guard_empty [C_simp_pre]:
  "com_eq (c \<noteq> Skip \<and> b = {}) (Guard f b c) (Guard f {} Skip)"
  by (clarsimp simp: com_eq_def, case_tac s, auto intro: exec.GuardFault elim!: exec_elim_cases)

lemma com_eq_Catch_Skip [C_simp]:
  "Catch Skip c \<sim> Skip"
  by (auto simp: com_eq_def intro: exec.CatchMiss exec.Skip elim!: exec_elim_cases)

lemma com_eq_Catch_Throw [C_simp]:
  "Catch Throw c \<sim> c"
  by (clarsimp simp: com_eq_def, case_tac s)
     (auto intro: exec.CatchMatch exec.Throw elim!: exec_elim_cases)

text \<open>An assertion expressing that a Simpl program never finishes normally.\<close>

definition
  "never_continues t c \<equiv> t \<longrightarrow> (\<forall>s s'. \<not> \<Gamma> \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> Normal s')"

text \<open>Commands sequenced after a command that @{term never_continues} may be ignored.\<close>

lemma never_continues_def2:
  "never_continues t c \<equiv> t \<longrightarrow> (\<forall>r. (c;;r) \<sim> c)"
  unfolding atomize_eq never_continues_def com_eq_def
  apply (rule iffI; erule (1) imp_forward; clarsimp)
   apply (rule iffI)
    apply (erule exec_elim_cases; clarsimp)
    apply (match premises in "\<Gamma> \<turnstile> \<langle>c, Normal _\<rangle> \<Rightarrow> s'" for s' \<Rightarrow> \<open>cases s'\<close>;
           clarsimp elim!: exec_elim_cases)
   apply (match premises in "\<Gamma> \<turnstile> \<langle>c, s\<rangle> \<Rightarrow> s'" for s s' \<Rightarrow> \<open>cases s; cases s'\<close>;
          clarsimp elim!: exec_elim_cases exec.Seq)
  by (fastforce dest!: spec[of _ Throw] elim!: exec_elim_cases)

text \<open>Rules for rewriting the arguments of @{term never_continues}.\<close>

lemma never_continues_weaken_guard:
  "never_continues t c \<Longrightarrow> (t' \<Longrightarrow> t) \<Longrightarrow> never_continues t' c"
  by (simp add: never_continues_def)

lemma never_continues_rewrite_com_eq:
  "c \<sim> c' \<Longrightarrow> never_continues t c \<Longrightarrow> never_continues t c'"
  apply (simp add: never_continues_def2)
  apply (elim imp_forward all_forward, assumption)
  apply (rule com_eq_trans, rule com_eq_Seq, erule com_eq_sym, rule com_eq_refl)
  by (erule com_eq_trans[rotated])

text \<open>Rules of the form @{term "never_continues True c"} may be added to @{text C_simp_throws}.\<close>

lemma never_continues_Throw [C_simp_throws]:
  "never_continues True Throw"
  by (auto simp: never_continues_def elim: exec_elim_cases)

lemma While_UNIV_helper:
  "\<Gamma> \<turnstile> \<langle>c',s\<rangle> \<Rightarrow> s'' \<Longrightarrow> c' = While UNIV c \<Longrightarrow> s'' = Normal s' \<Longrightarrow> False"
  by (induct rule: exec.induct) auto

lemma never_continues_While_UNIV [C_simp_throws]:
  "never_continues True (While UNIV c)"
  by (auto simp: never_continues_def elim: While_UNIV_helper)

lemma never_continues_While_True [C_simp_throws]:
  "never_continues True (WHILE True DO c OD)"
  by (simp add: whileAnno_def never_continues_While_UNIV)

lemma never_continues_Guard_False [C_simp_throws]:
  "never_continues True (Guard f {} c)"
  by (auto simp: never_continues_def elim: exec_elim_cases)

text \<open>Structural decomposition of Simpl programs under @{term never_continues}.\<close>

lemma never_continues_Seq1:
  "never_continues t c1 \<Longrightarrow> never_continues t (c1;;c2)"
  apply (clarsimp simp: never_continues_def2)
  apply (frule spec[of _ c2], erule com_eq_trans[rotated, OF com_eq_sym])
  apply (rule com_eq_trans[OF com_eq_Seq_assoc_r])
  by simp

lemma never_continues_Seq2:
  "never_continues t c2 \<Longrightarrow> never_continues t (c1;;c2)"
  apply (clarsimp simp: never_continues_def2)
  apply (rule com_eq_trans[OF com_eq_Seq_assoc_r])
  apply (rule com_eq_Seq[OF com_eq_refl])
  by simp

lemmas never_continues_Seqs =
  never_continues_Seq1 never_continues_Seq2

lemma never_continues_Cond:
  "never_continues t1 c1 \<Longrightarrow> never_continues t2 c2 \<Longrightarrow> never_continues (t1 \<and> t2) (Cond b c1 c2)"
  by (auto simp: never_continues_def elim: exec_elim_cases)

lemma never_continues_Guard:
  "never_continues t c \<Longrightarrow> never_continues t (Guard f b c)"
  by (auto simp: never_continues_def elim: exec_elim_cases)

lemma never_continues_Catch:
  "never_continues tc c \<Longrightarrow> never_continues th h \<Longrightarrow> never_continues (tc \<and> th) (Catch c h)"
  by (auto simp: never_continues_def elim: exec_elim_cases)

text \<open>If all else fails...\<close>

lemma never_continues_False:
  "never_continues False c"
  by (simp add: never_continues_def)

end

text \<open>One layer of context around a Simpl program.

      For example, if the current focus is the first branch of a @{term Cond},
      then the context consists of a constructor @{text CondTC} which indicates
      this is the context, and carries everything but but the focused branch,
      i.e. the condition and the second branch.

      The @{text CondFC} and @{text HandlerC} cases each carry an extra bit of
      information, which indicates whether the left-hand branch @{text never_continues}.
      The assumption here is that we always traverse Simpl programs left-to-right.
      @{text Seq2C} does not require an extra bit, because we never enter the second
      command of a @{term Seq} if the first command @{text never_continues}.\<close>

datatype ('s,'p,'f) com_ctxt
  = Seq1C "('s,'p,'f) com" \<comment> \<open>first command of a @{term Seq}\<close>
  | Seq2C "('s,'p,'f) com" \<comment> \<open>second command of a @{term Seq}\<close>
  | CondTC "'s bexp" "('s,'p,'f) com" \<comment> \<open>first branch of a @{term Cond}\<close>
  | CondFC "'s bexp" "('s,'p,'f) com" bool \<comment> \<open>second branch of a @{term Cond}\<close>
  | WhileC "'s bexp" \<comment> \<open>body of a @{term While}\<close>
  | WhileAnnoC "'s bexp" "'s assn" "('s \<times> 's) assn" \<comment> \<open>body of a @{term whileAnno}\<close>
  | GuardC "'f" "'s bexp" \<comment> \<open>body of a @{term Guard}\<close>
  | TryC "('s,'p,'f) com" \<comment> \<open>body of a @{term Catch}\<close>
  | HandlerC "('s,'p,'f) com" bool \<comment> \<open>handler of a @{term Catch}\<close>

text \<open>Rewrite Simpl programs under a predicate @{term P} which is preserved by @{term com_eq}.\<close>

locale simpl_rewrite = simpl_rewrite_base \<Gamma>
  for \<Gamma> :: "'p \<Rightarrow> ('s,'p,'f) com option" +
  fixes P :: "('s,'p,'f) com \<Rightarrow> bool"
  assumes inv: "\<And>c c'. c \<sim> c' \<Longrightarrow> P c' \<Longrightarrow> P c"
begin

text \<open>Calculate @{term P} for a Simpl program consisting of a sub-program in a nest of contexts.\<close>

fun
  ctxt_P :: "('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com_ctxt list \<Rightarrow> bool"
where
    "ctxt_P c [] = P c"
  | "ctxt_P c (Seq1C c' # cs) = ctxt_P (Seq c c') cs"
  | "ctxt_P c (Seq2C c' # cs) = ctxt_P (Seq c' c) cs"
  | "ctxt_P c (CondTC b c' # cs) = ctxt_P (Cond b c c') cs"
  | "ctxt_P c (CondFC b c' t # cs) = (never_continues t c' \<longrightarrow> ctxt_P (Cond b c' c) cs)"
  | "ctxt_P c (WhileC b # cs) = ctxt_P (While b c) cs"
  | "ctxt_P c (WhileAnnoC b I V # cs) = ctxt_P (whileAnno b I V c) cs"
  | "ctxt_P c (GuardC f b # cs) = ctxt_P (Guard f b c) cs"
  | "ctxt_P c (TryC c' # cs) = ctxt_P (Catch c c') cs"
  | "ctxt_P c (HandlerC c' t # cs) = (never_continues t c' \<longrightarrow> ctxt_P (Catch c' c) cs)"

text \<open>For the current focus, we add a flag @{term t} of type @{typ "bool option"}.
      @{term t} is None until we have finished rewriting sub-programs.
      It is @{term "Some t"} when rewriting has finished for the current focus, and
      the result satisfies @{term "never_continues t"}.\<close>

definition
  "nc_opt t \<equiv> never_continues (case_option False id t)"

definition
  "focus c t cs \<equiv> nc_opt t c \<longrightarrow> ctxt_P c cs"

lemmas focus_defs = focus_def nc_opt_def

lemma nc_opt_None:
  "nc_opt None t"
  by (simp add: nc_opt_def never_continues_False)

text \<open>Rules for beginning and ending the rewriting process.\<close>

lemma enter_focus:
  "focus c None [] \<Longrightarrow> P c"
  by (simp add: focus_defs never_continues_False)

lemma exit_focus:
  "P c \<Longrightarrow> focus c t []"
  by (simp add: focus_defs)

text \<open>Rules for rewriting at the current focus.\<close>

lemma nc_opt_rewrite_com_eq:
  "c \<sim> c' \<Longrightarrow> nc_opt t c \<Longrightarrow> nc_opt t c'"
  by (simp add: nc_opt_def never_continues_rewrite_com_eq)

lemma ctxt_P_rewrite_com_eq:
  "c \<sim> c' \<Longrightarrow> ctxt_P c' cs \<Longrightarrow> ctxt_P c cs"
  proof (induct cs arbitrary: c c')
    case Nil thus ?case by (simp add: inv)
  next
    case (Cons c'' cs) show ?case using Cons.prems(2)
      by (cases c''; clarsimp elim!: Cons.hyps[rotated];
          intro com_eq_intros com_eq_refl Cons.prems(1))
  qed

lemma rewrite_focus:
  "com_eq p c c' \<Longrightarrow> p \<Longrightarrow> focus c' t cs \<Longrightarrow> focus c t cs"
  by (simp add: focus_def nc_opt_rewrite_com_eq ctxt_P_rewrite_com_eq)

text \<open>Rules to set the @{term never_continues} flag for the current focus.\<close>

lemma focus_set_never_continues:
  "never_continues t c \<Longrightarrow> focus c (Some t) cs \<Longrightarrow> focus c None cs"
  by (simp add: focus_defs)

lemma focus_update_never_continues:
  "never_continues t c \<Longrightarrow> focus c (Some (t \<or> t')) cs \<Longrightarrow> focus c (Some t') cs"
  by (cases t; cases t'; simp add: focus_defs)

lemmas focus_never_continues =
  focus_update_never_continues[where t'=True, simplified]
  focus_update_never_continues[where t'=False, simplified]
  focus_set_never_continues

text \<open>Rules for moving the focus down the left spine.\<close>

lemma focus_left:
  "focus c None (Seq1C c' # cs) \<Longrightarrow> focus (Seq c c') None cs"
  "focus c None (CondTC b c' # cs) \<Longrightarrow> focus (Cond b c c') None cs"
  "focus c None (WhileC b # cs) \<Longrightarrow> focus (While b c) None cs"
  "focus c None (WhileAnnoC b I V # cs) \<Longrightarrow> focus (whileAnno b I V c) None cs"
  "focus c None (GuardC f b # cs) \<Longrightarrow> focus (Guard f b c) None cs"
  "focus c None (TryC c' # cs) \<Longrightarrow> focus (Catch c c') None cs"
  by (auto simp: focus_def nc_opt_None)

text \<open>Rules for moving the focus to the right sibling.\<close>

lemma focus_right:
  "focus c' None (Seq2C c # cs) \<Longrightarrow> focus c (Some False) (Seq1C c' # cs)"
  "focus c' None (CondFC b c t # cs) \<Longrightarrow> focus c (Some t) (CondTC b c' # cs)"
  "focus c' None (HandlerC c t # cs) \<Longrightarrow> focus c (Some t) (TryC c' # cs)"
  by (auto simp: focus_defs never_continues_False)

text \<open>Rules for moving the focus up to the parent.\<close>

lemma ctxt_P_Seq1:
  "never_continues True c \<Longrightarrow> ctxt_P c cs \<Longrightarrow> ctxt_P (Seq c c') cs"
  by (auto simp: never_continues_def2 elim: ctxt_P_rewrite_com_eq)

lemma unfocus_simple:
  "focus c (Some True) cs \<Longrightarrow> focus c (Some True) (Seq1C c' # cs)"
  "focus (Seq c' c) (Some t) cs \<Longrightarrow> focus c (Some t) (Seq2C c' # cs)"
  "focus (While b c) (Some False) cs \<Longrightarrow> focus c (Some t) (WhileC b # cs)"
  "focus (whileAnno b I V c) (Some False) cs \<Longrightarrow> focus c (Some t) (WhileAnnoC b I V # cs)"
  "focus (Guard f b c) (Some t) cs \<Longrightarrow> focus c (Some t) (GuardC f b # cs)"
  by (auto simp: focus_defs never_continues_False ctxt_P_Seq1 never_continues_Seq2 never_continues_Guard)

lemma unfocus_complex:
  "focus (Cond b c' c) (Some (t' \<and> t)) cs \<Longrightarrow> focus c (Some t) (CondFC b c' t' # cs)"
  "focus (Catch c' c) (Some (t' \<and> t)) cs \<Longrightarrow> focus c (Some t) (HandlerC c' t' # cs)"
  by (auto simp: focus_defs never_continues_False never_continues_Cond never_continues_Catch)

lemmas unfocus =
  unfocus_complex[where t=True and t'=True, simplified]
  unfocus_complex[where t=False, simplified]
  unfocus_complex[where t'=False, simplified]
  unfocus_simple

text \<open>Methods to automate rewriting.\<close>

method do_rewrite uses ruleset declares C_simp_simps =
  (rule rewrite_focus, rule ruleset,
   #break "simpl_rewrite_rewrite", (simp add: C_simp_simps; fail))+

method rewrite_pre declares C_simp_pre C_simp_simps =
  (do_rewrite ruleset: C_simp_pre)

method rewrite_post declares C_simp C_simp_simps =
  (do_rewrite ruleset: C_simp)

method never_continues declares C_simp_throws =
  (rule focus_never_continues, rule C_simp_throws never_continues_False)

method children methods do_focus declares C_simp C_simp_pre C_simp_simps C_simp_throws =
  (rule focus_left, do_focus, (rule focus_right, do_focus)?, rule unfocus)?

method do_focus declares C_simp C_simp_pre C_simp_simps C_simp_throws =
  (#break "simpl_rewrite_step", rewrite_pre?, children \<open>do_focus\<close>,
   #break "simpl_rewrite_step", rewrite_post?, never_continues)

method simpl_rewrite declares C_simp C_simp_pre C_simp_simps C_simp_throws =
  changed \<open>rule enter_focus, do_focus, rule exit_focus\<close>

text \<open>Tests\<close>

lemma
  assumes c3: "c3 \<sim> c"
  assumes c: "(c;;c) \<sim> c"
  shows "P (c;; Guard f UNIV (IF X THEN c ELSE c FI);; Cond {} Skip (Skip;;c2);; Skip;;
            (IF False THEN Skip ELSE SKIP;; TRY THROW CATCH c3 END FI;; SKIP))"
  apply simpl_rewrite
  apply (match conclusion in "P (c;;c;;c2;;c3)" \<Rightarrow> \<open>-\<close>)
  apply (simpl_rewrite C_simp: c3)
  apply (match conclusion in "P (c;;c;;c2;;c)" \<Rightarrow> \<open>-\<close>)
  apply (simpl_rewrite C_simp: c)
  apply (match conclusion in "P (c;;c2;;c)" \<Rightarrow> \<open>-\<close>)
  apply (fails \<open>simpl_rewrite\<close>)
  oops

text \<open>Test for @{text WHILE} (@{term whileAnno}) case.\<close>

lemma
  "P (WHILE b DO Guard f g c;; IF False THEN c2 FI OD;; SKIP)"
  apply simpl_rewrite
  apply (match conclusion in "P (WHILE b DO Guard f g c OD)" \<Rightarrow> \<open>-\<close>)
  oops

text \<open>Test that simplification works down all branches of the term.\<close>

lemma
  "P (IF b THEN
        (SKIP ;; c) ;; (SKIP ;; IF True THEN SKIP ELSE c FI)
      ELSE
        (SKIP ;; SKIP) ;; (Guard f UNIV c ;; SKIP)
      FI)"
  apply simpl_rewrite
  apply (match conclusion in "P c" \<Rightarrow> \<open>-\<close>)
  oops

text \<open>Test that complex simplification rules work.\<close>

lemma com_eq_Cond_redundant:
  "(IF b THEN c1 ELSE IF b THEN c2 ELSE c3 FI FI) \<sim> (IF b THEN c1 ELSE c3 FI)"
  unfolding com_eq_def
  by (auto intro: exec.CondTrue exec.CondFalse elim!: exec_elim_cases)

lemma
  "P (SKIP ;;
      IF b THEN
        (SKIP ;; c1) ;; (SKIP ;; SKIP)
      ELSE
        IF b THEN
          IF b1 THEN c2 ELSE c2 FI
        ELSE
          WHILE False DO c4 OD ;; (c3 ;; SKIP)
        FI
      FI)"
  apply (simpl_rewrite C_simp: com_eq_Cond_redundant)
  apply (match conclusion in "P (IF b THEN c1 ELSE c3 FI)" \<Rightarrow> \<open>-\<close>)
  oops

text \<open>Test False guard avoids looping.\<close>

lemma
  "P (SKIP ;; Guard f {} (IF b THEN c ELSE c FI) ;; SKIP)"
  apply simpl_rewrite
  apply (match conclusion in "P (Guard f {} SKIP)" \<Rightarrow> \<open>-\<close>)
  oops

text \<open>Test that everything after a deeply nested Throw is discarded.\<close>

lemma
  "P (c0;; (c1;; (c2;; (c3;; (c4;; Throw;; c5);; c6);; c7);; c8);; c9)"
  apply simpl_rewrite
  apply (match conclusion in "P (c0;; (c1;; (c2;; (c3;; (c4;; Throw)))))" \<Rightarrow> \<open>-\<close>)
  oops

text \<open>Test that rewriting can simplify conditions, also using assumptions in the context.\<close>

lemma
  assumes "\<And>s. A s \<Longrightarrow> C s"
  shows "\<forall>s. Q s = (A s \<longrightarrow> B s \<longrightarrow> C s) \<Longrightarrow> P (Cond {s. \<not> Q s} c1 c2)"
  apply (simpl_rewrite C_simp_simps: assms)
  apply (match premises in "\<forall>s. Q s = (A s \<longrightarrow> B s \<longrightarrow> C s)" \<Rightarrow> \<open>match conclusion in "P c2" \<Rightarrow> \<open>-\<close>\<close>)
  oops

end

end
