(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(*
 * A theoretical framework for reasoning about non-interference
 * of monadic programs.
 *)

theory EquivValid
imports Corres_UL
begin

section\<open>State equivalence validity\<close>

text\<open>

A generalised information flow property.

Often, we read in the entire state, but then only examine part of it.
The following property may be used to split up binds whose first part
does this.

@{term "I"} is the state relation that holds invariantly.

@{term "A"} (also) holds between initial states.

@{term "B"} (also) holds between final states.

@{term "P"} holds in the initial state for @{term "f"}.

@{term "P'"} holds in the initial state for @{term "f'"}.

\<close>

definition
  equiv_valid_2 :: "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('s,'b) nondet_monad \<Rightarrow> ('s,'c) nondet_monad \<Rightarrow> bool"
where
  "equiv_valid_2 I A B R P P' f f' \<equiv> \<forall>s t.
       P s \<and> P' t \<and> I s t \<and> A s t
     \<longrightarrow> (\<forall>(rva, s') \<in> fst (f s). \<forall>(rvb, t') \<in> fst (f' t).
          R rva rvb \<and> I s' t' \<and> B s' t')"

lemma equiv_valid_2_bind_general:
  assumes r2: "\<And> rv rv'. R' rv rv' \<Longrightarrow> equiv_valid_2 D B C R (Q rv) (Q' rv') (g rv) (g' rv')"
  assumes r1: "equiv_valid_2 D A B R' P P' f f'"
  assumes hoare: "\<lbrace> S \<rbrace> f \<lbrace> Q \<rbrace>"
  assumes hoare': "\<lbrace> S' \<rbrace> f' \<lbrace> Q' \<rbrace>"
  shows "equiv_valid_2 D A C R (\<lambda> s. P s \<and> S s) (\<lambda> s. P' s \<and> S' s) (f >>= g) (f' >>= g')"
  using assms
  unfolding bind_def equiv_valid_2_def valid_def
  apply fastforce
  done

(* almost all of the time, the second relation doesn't change *)
lemma equiv_valid_2_bind:
  assumes r2: "\<And> rv rv'. R' rv rv' \<Longrightarrow> equiv_valid_2 D A A R (Q rv) (Q' rv') (g rv) (g' rv')"
  assumes r1: "equiv_valid_2 D A A R' P P' f f'"
  assumes hoare: "\<lbrace> S \<rbrace> f \<lbrace> Q \<rbrace>"
  assumes hoare': "\<lbrace> S' \<rbrace> f' \<lbrace> Q' \<rbrace>"
  shows "equiv_valid_2 D A A R (\<lambda> s. P s \<and> S s) (\<lambda> s. P' s \<and> S' s) (f >>= g) (f' >>= g')"
  using assms by (blast intro: equiv_valid_2_bind_general)

lemma equiv_valid_2_guard_imp:
  assumes reads_res: "equiv_valid_2 D A B R Q Q' f f'"
  assumes guard_imp: "\<And> s. P s \<Longrightarrow> Q s"
  assumes guard_imp': "\<And> s. P' s \<Longrightarrow> Q' s"
  shows "equiv_valid_2 D A B R P P' f f'"
  using assms
  by (fastforce simp: equiv_valid_2_def)

lemma equiv_valid_2_bind_pre:
  assumes r2: "\<And> rv rv'. R' rv rv' \<Longrightarrow> equiv_valid_2 D A A R (Q rv) (Q' rv') (g rv) (g' rv')"
  assumes r1: "equiv_valid_2 D A A R' P P' f f'"
  assumes hoare: "\<lbrace> S \<rbrace> f \<lbrace> Q \<rbrace>"
  assumes hoare': "\<lbrace> S' \<rbrace> f' \<lbrace> Q' \<rbrace>"
  assumes guard_imp: "\<And> s. T s \<Longrightarrow> P s \<and> S s"
  assumes guard_imp': "\<And> s. T' s \<Longrightarrow> P' s \<and> S' s"
  shows "equiv_valid_2 D A A R T T' (f >>= g) (f' >>= g')"
  using assms by (blast intro: equiv_valid_2_bind[THEN equiv_valid_2_guard_imp])

lemma return_ev2:
  assumes rel: "\<And> s t. \<lbrakk>P s; P' t; I s t; A s t\<rbrakk> \<Longrightarrow> R a b"
  shows "equiv_valid_2 I A A R P P' (return a) (return b)"
  by(auto simp: equiv_valid_2_def return_def rel)

lemma equiv_valid_2_liftE:
  "equiv_valid_2 D A B R P P' f f' \<Longrightarrow>
   equiv_valid_2 D A B (E \<oplus> R) P P' (liftE f) (liftE f')"
  apply(unfold liftE_def)
  apply(rule equiv_valid_2_guard_imp)
  apply(rule_tac Q="\<top>\<top>" and Q'="\<top>\<top>" and R'=R in equiv_valid_2_bind_general)
       apply(fastforce intro: return_ev2)
      apply assumption
     apply(rule wp_post_taut)+
   by(simp_all)

lemma equiv_valid_2_liftE_bindE_general:
  assumes r2: "\<And> rv rv'. R' rv rv' \<Longrightarrow> equiv_valid_2 D B C R (Q rv) (Q' rv') (g rv) (g' rv')"
  assumes hoare: "\<lbrace> S \<rbrace> f \<lbrace> Q \<rbrace>"
  assumes hoare':  "\<lbrace> S' \<rbrace> f' \<lbrace> Q' \<rbrace>"
  assumes r1: "equiv_valid_2 D A B R' P P' f f'"
  shows "equiv_valid_2 D A C R (P and S) (P' and S') (liftE f >>=E g) (liftE f' >>=E g')"
  apply(unfold bindE_def)
  apply(rule equiv_valid_2_guard_imp)
  apply(rule_tac Q="\<lambda> rv. K (\<forall> v. rv \<noteq> Inl v) and (\<lambda> s. \<forall> v. rv = Inr v \<longrightarrow> Q v s)" and Q'="\<lambda> rv. K (\<forall> v. rv \<noteq> Inl v) and (\<lambda> s. \<forall> v. rv = Inr v \<longrightarrow> Q' v s)" in equiv_valid_2_bind_general)
       prefer 2
       apply(rule_tac E="dc" in equiv_valid_2_liftE)
       apply(rule r1)
      apply(clarsimp simp: lift_def split: sum.split)
      apply(insert r2, fastforce simp: equiv_valid_2_def)[1]
     apply(simp add: liftE_def, wp, fastforce intro!: hoare_strengthen_post[OF hoare])
    apply(simp add: liftE_def, wp, fastforce intro!: hoare_strengthen_post[OF hoare'])
   by(auto)

lemma equiv_valid_2_liftE_bindE:
  assumes r2: "\<And> rv rv'. R' rv rv' \<Longrightarrow> equiv_valid_2 D A A R (Q rv) (Q' rv') (g rv) (g' rv')"
  assumes hoare: "\<lbrace> S \<rbrace> f \<lbrace> Q \<rbrace>"
  assumes hoare':  "\<lbrace> S' \<rbrace> f' \<lbrace> Q' \<rbrace>"
  assumes r1: "equiv_valid_2 D A A R' P P' f f'"
  shows "equiv_valid_2 D A A R (P and S) (P' and S') (liftE f >>=E g) (liftE f' >>=E g')"
  using assms by(blast intro: equiv_valid_2_liftE_bindE_general)

lemma equiv_valid_2_rvrel_imp:
  "\<lbrakk>equiv_valid_2 I A A R P P' f f'; \<And> s t. R s t \<Longrightarrow> R' s t\<rbrakk> \<Longrightarrow>
   equiv_valid_2 I A A R' P P' f f'"
  apply(fastforce simp: equiv_valid_2_def)
  done

subsection\<open>Specialised fixed-state state equivalence validity\<close>

text\<open>

For resolve_address_bits and rec_del: talk about a fixed initial
state. Note we only do this for one of the computations; the other
state can be constrained by how it is related to this one by @{term
"I"} and so forth.

Also captures the typical case where the relation between the return
values is equality and the required preconditions are identical.

wp can cope with this.

\<close>

definition
  spec_equiv_valid :: "'s \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('s,'b) nondet_monad \<Rightarrow> bool"
where
  "spec_equiv_valid st I A B P f \<equiv> equiv_valid_2 I A B (=) (P and ((=) st)) P f f"

abbreviation spec_equiv_valid_inv where
  "spec_equiv_valid_inv st I A P f \<equiv> spec_equiv_valid st I A A P f"

subsection\<open>Specialised state equivalence validity\<close>

text\<open>

Most of the time we deal with the streamlined version.

wp can cope with this too.

\<close>

definition
  equiv_valid :: "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('s,'b) nondet_monad \<Rightarrow> bool"
where
  "equiv_valid I A B P f \<equiv> \<forall>st. spec_equiv_valid st I A B P f"

lemma equiv_valid_def2:
  "equiv_valid I A B P f = equiv_valid_2 I A B (=) P P f f"
  by (simp add: equiv_valid_def spec_equiv_valid_def equiv_valid_2_def)

abbreviation equiv_valid_rv where
  "equiv_valid_rv I A B R P f \<equiv> equiv_valid_2 I A B R P P f f"

(* this is probably way more general than we need for all but a few special cases *)
lemma bind_ev_general:
  assumes reads_res_2: "\<And>rv. equiv_valid I B C (Q rv) (g rv)"
  assumes reads_res_1: "equiv_valid I A B P' f"
  assumes hoare: "\<lbrace> P'' \<rbrace> f \<lbrace> Q \<rbrace>"
  shows "equiv_valid I A C (\<lambda>s. P' s \<and> P'' s) (f >>= g)"
  unfolding equiv_valid_def2
  apply (rule equiv_valid_2_bind_general[where R'="(=)"])
     apply (auto intro: reads_res_1[unfolded equiv_valid_def2] reads_res_2[unfolded equiv_valid_def2])[2]
   apply (rule hoare)
  apply (rule hoare)
  done

lemma bind_ev:
  assumes reads_res_2: "\<And>rv. equiv_valid I A A (Q rv) (g rv)"
  assumes reads_res_1: "equiv_valid I A A P' f"
  assumes hoare: "\<lbrace> P'' \<rbrace> f \<lbrace> Q \<rbrace>"
  shows "equiv_valid I A A (\<lambda>s. P' s \<and> P'' s) (f >>= g)"
  using assms by (blast intro: bind_ev_general)

lemma equiv_valid_guard_imp:
  assumes reads_res: "equiv_valid I A B Q f"
  assumes guard_imp: "\<And> s. P s \<Longrightarrow> Q s"
  shows "equiv_valid I A B P f"
  using assms by (fastforce simp: equiv_valid_def2 equiv_valid_2_def)

lemmas bind_ev_pre = bind_ev[THEN equiv_valid_guard_imp]

lemma gen_asm_ev':
  assumes "Q \<Longrightarrow> equiv_valid D A B P f"
  shows "equiv_valid D A B (P and K Q) f"
  using assms by (fastforce simp: equiv_valid_def2 equiv_valid_2_def)

declare K_def [simp del]

lemmas gen_asm_ev =
  gen_asm_ev'[where P="\<top>", simplified]
  gen_asm_ev'
  gen_asm_ev'[simplified K_def, where P="\<top>", simplified]
  gen_asm_ev'[simplified K_def]

declare K_def [simp]

text \<open>
  This is a further streamlined version that we expect to get the most from
  automating, and for the most part, we shouldn't need to deal with the
  extra generality of the properties above.
\<close>
abbreviation equiv_valid_inv where
  "equiv_valid_inv I A P f \<equiv> equiv_valid I A A P f"

abbreviation equiv_valid_rv_inv where
  "equiv_valid_rv_inv I A R P f \<equiv> equiv_valid_rv I A A R P f"

lemma get_evrv:
  "equiv_valid_rv_inv I A (I And A) \<top> get"
  by(auto simp: equiv_valid_2_def get_def)

lemma equiv_valid_rv_bind_general:
  assumes ev1:
  "equiv_valid_rv I A B W P f"
  assumes ev2:
  "\<And> rv rv'. W rv rv' \<Longrightarrow> equiv_valid_2 I B C R (Q rv) (Q rv') (g rv) (g rv')"
  assumes hoare:
  "\<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>"
  shows "equiv_valid_rv I A C R P (f >>= g)"
  apply(rule equiv_valid_2_guard_imp)
  apply(rule equiv_valid_2_bind_general[OF ev2])
       apply(assumption)
      apply(rule ev1)
     apply(rule hoare)
    apply(rule hoare)
   apply(simp_all)
  done

lemma equiv_valid_rv_bind:
  assumes ev1:
  "equiv_valid_rv_inv I A W P f"
  assumes ev2:
  "\<And> rv rv'. W rv rv' \<Longrightarrow> equiv_valid_2 I A A R (Q rv) (Q rv') (g rv) (g rv')"
  assumes hoare:
  "\<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>"
  shows "equiv_valid_rv_inv I A R P (f >>= g)"
  using assms by(blast intro: equiv_valid_rv_bind_general)

lemma modify_ev2:
  assumes "\<And> s t. \<lbrakk>I s t; A s t; P s; P' t\<rbrakk> \<Longrightarrow> R () () \<and> I (f s) (f' t) \<and> B (f s) (f' t)"
  shows
  "equiv_valid_2 I A B R P P' (modify f) (modify f')"
  apply(clarsimp simp: equiv_valid_2_def in_monad)
  using assms by auto

lemma put_ev2:
  assumes "\<And> s t. \<lbrakk>I s t; A s t; P s; P' t\<rbrakk> \<Longrightarrow> R () () \<and> I x x' \<and> B x x'"
  shows
  "equiv_valid_2 I A B R P P' (put x) (put x')"
  apply(clarsimp simp: equiv_valid_2_def in_monad)
  using assms by auto


lemma get_bind_ev2:
  assumes "\<And> rv rv'. \<lbrakk>I rv rv'; A rv rv'\<rbrakk> \<Longrightarrow> equiv_valid_2 I A B R (P and ((=) rv)) (P' and ((=) rv')) (f rv) (f' rv')"
  shows "equiv_valid_2 I A B R P P' (get >>= f) (get >>= f')"
  apply(rule equiv_valid_2_guard_imp)
  apply(rule_tac R'="I And A" in equiv_valid_2_bind_general)
       apply(rule assms, simp+)
      apply(rule get_evrv)
     apply(wp get_sp)+
   by(auto)


lemma return_ev_pre:
  "equiv_valid_inv I A P (return x)"
  apply (simp add: equiv_valid_def2 return_ev2)
  done

lemmas return_ev = return_ev_pre[where P=\<top>]

lemma fail_ev2_l:
  "equiv_valid_2 I A B R P P' fail f'"
  by(simp add: equiv_valid_2_def fail_def)

lemma fail_ev2_r:
  "equiv_valid_2 I A B R P P' f fail"
  by(simp add: equiv_valid_2_def fail_def)

lemma fail_ev_pre:
  "equiv_valid I A B P fail"
  apply (simp add: equiv_valid_def2 fail_ev2_l)
  done

lemmas fail_ev = fail_ev_pre[where P=\<top>]

lemma assert_ev2:
  "R () () \<Longrightarrow> equiv_valid_2 I A A R P P' (assert a) (assert b)"
  apply(simp add: assert_def fail_ev2_l fail_ev2_r)
  apply(blast intro: return_ev2)
  done

lemma liftE_ev:
  "equiv_valid I A B P f \<Longrightarrow> equiv_valid I A B P (liftE f)"
  unfolding liftE_def
  apply (rule bind_ev_general[THEN equiv_valid_guard_imp, OF return_ev _ wp_post_taut])
  apply fastforce+ (* schematic instantiation *)
  done

lemma if_ev:
  assumes "b \<Longrightarrow> equiv_valid I A B P f"
  assumes "\<not> b \<Longrightarrow> equiv_valid I A B Q g"
  shows "equiv_valid I A B (\<lambda>s. (b \<longrightarrow> P s) \<and> (\<not>b \<longrightarrow> Q s)) (if b then f else g)"
  apply (clarsimp split: if_split)
  using assms by blast

lemmas if_ev_pre = equiv_valid_guard_imp[OF if_ev]

lemma assert_ev_pre:
  "equiv_valid_inv I A P (assert b)"
  apply(simp add: equiv_valid_def2 assert_ev2)
  done

lemmas assert_ev = assert_ev_pre[where P=\<top>]

lemma assert_opt_ev:
  "equiv_valid_inv I A \<top> (assert_opt v)"
  apply (simp add: assert_opt_def return_ev fail_ev
            split: option.split)
  done

lemma assert_opt_ev2:
  assumes "\<And> a a'. \<lbrakk>v = Some a; v' = Some a'\<rbrakk> \<Longrightarrow> R a a'"
  shows "equiv_valid_2 I A A R \<top> \<top> (assert_opt v) (assert_opt v')"
  apply (simp add: assert_opt_def return_ev fail_ev2_l fail_ev2_r
            split: option.split)
  apply(intro allI impI)
  apply(rule return_ev2)
  apply(rule assms, assumption+)
  done

lemma select_f_ev:
  "equiv_valid_inv I A (K (det f)) (select_f (f x))"
  apply (rule gen_asm_ev)
  apply (simp add: select_f_def equiv_valid_def2 equiv_valid_2_def det_set_iff)
  done

lemma gets_evrv:
  "equiv_valid_rv_inv I A R (K (\<forall>s t. I s t \<and> A s t \<longrightarrow> R (f s) (f t))) (gets f)"
  apply (auto simp: equiv_valid_2_def in_monad)
  done

lemma gets_evrv':
  "equiv_valid_rv_inv I A R (\<lambda>s. (\<forall>t. I s t \<and> A s t \<longrightarrow> R (f s) (f t))) (gets f)"
  apply (auto simp: equiv_valid_2_def in_monad)
  done

lemma gets_evrv'':
  "\<forall>s t. I s t \<and> A s t \<and> P s \<and> P t \<longrightarrow> R (f s) (f t) \<Longrightarrow> equiv_valid_rv_inv I A R P (gets f)"
  apply (auto simp: equiv_valid_2_def in_monad)
  done

lemma equiv_valid_rv_guard_imp:
  "\<lbrakk>equiv_valid_rv I A B R P f; \<And> s. Q s \<Longrightarrow> P s\<rbrakk> \<Longrightarrow>
   equiv_valid_rv I A B R Q f"
  apply(simp add: equiv_valid_2_def)
  apply fast
  done

lemma gets_ev:
  shows "equiv_valid_inv I A (\<lambda> s. \<forall> s t. I s t \<and> A s t \<longrightarrow> f s = f t) (gets f)"
  apply (simp add: equiv_valid_def2)
  apply (auto intro: equiv_valid_rv_guard_imp[OF gets_evrv])
  done

lemma gets_ev':
  shows "equiv_valid_inv I A (\<lambda> s. \<forall> t. I s t \<and> A s t \<longrightarrow> f s = f t) (gets f)"
  apply (simp add: equiv_valid_def2)
  apply (auto intro: equiv_valid_rv_guard_imp[OF gets_evrv'])
  done

lemma gets_ev'':
  "\<forall>s t. I s t \<and> A s t \<and> P s \<and> P t \<longrightarrow> f s = f t \<Longrightarrow> equiv_valid_inv I A P (gets f)"
  apply (simp add: equiv_valid_def2)
  apply (auto intro: equiv_valid_rv_guard_imp[OF gets_evrv''])
  done

lemma gets_the_evrv:
  "equiv_valid_rv_inv I A R (K (\<forall>s t. I s t \<and> A s t \<longrightarrow> R (the (f s)) (the (f t)))) (gets_the f)"
  unfolding gets_the_def
  apply (rule equiv_valid_rv_bind)
    apply(rule equiv_valid_rv_guard_imp[OF gets_evrv])
    apply simp
   apply(rule assert_opt_ev2)
   apply simp
  apply wp
  done

lemma gets_the_ev:
  "equiv_valid_inv I A (K (\<forall>s t. I s t \<and> A s t \<longrightarrow> f s = f t)) (gets_the f)"
  unfolding equiv_valid_def2
  apply(rule equiv_valid_rv_guard_imp[OF gets_the_evrv])
  by simp

lemma throwError_ev_pre:
  "equiv_valid_inv I A P (throwError e)"
  by (auto simp: throwError_def return_ev_pre)

lemmas throwError_ev = throwError_ev_pre[where P=\<top>]

lemma returnOk_ev_pre:
  "equiv_valid_inv I A P (returnOk v)"
  by (auto simp: returnOk_def return_ev_pre)

lemmas returnOk_ev = returnOk_ev_pre[where P=\<top>]

(* this seems restrictive, to have the same beginning and ending state relation,
   however, one suspects that bindE is used usually only in code that doesn't
   modify the state, so is probably OK.. We'll see *)
lemma bindE_ev:
  assumes reads_res_2: "\<And> rv. equiv_valid_inv I A (Q rv) (g rv)"
  assumes reads_res_1: "equiv_valid_inv I A P' f"
  assumes hoare: "\<lbrace> P'' \<rbrace> f \<lbrace> Q \<rbrace>,-"
  shows "equiv_valid_inv I A (\<lambda>s. P' s \<and> P'' s) (f >>=E g)"
  unfolding bindE_def
  apply (rule bind_ev)
    prefer 3
    apply(rule hoare[unfolded validE_R_def validE_def])
   apply(simp split: sum.split add: lift_def throwError_ev)
   apply(blast intro!: reads_res_2)
  apply(rule reads_res_1)
  done

lemmas bindE_ev_pre = bindE_ev[THEN equiv_valid_guard_imp]

(* Of course, when we know that progress is always made, we can do better *)
lemma liftE_bindE_ev_general:
  assumes r2: "\<And> val. equiv_valid I B C (Q val) (g val)"
  assumes r1: "equiv_valid I A B P f"
  assumes hoare: "\<lbrace> R \<rbrace> f \<lbrace> Q \<rbrace>"
  shows "equiv_valid I A C (\<lambda> s. P s \<and> R s) (liftE f >>=E g)"
  apply(simp add: bindE_def)
  apply(rule_tac Q="\<lambda> rv. K (\<forall> v. rv \<noteq> Inl v) and (\<lambda> s. \<forall> v. rv = Inr v \<longrightarrow> Q v s)" in bind_ev_general)
    prefer 2
    apply(rule liftE_ev)
    apply(rule r1)
   apply(insert r2, fastforce simp: lift_def split: sum.split simp: equiv_valid_def2 equiv_valid_2_def)[1]
  apply(insert hoare, fastforce simp: valid_def liftE_def return_def bind_def)
  done

lemma liftE_bindE_ev:
  assumes r2: "\<And> val. equiv_valid_inv I A (Q val) (g val)"
  assumes r1: "equiv_valid_inv I A P f"
  assumes hoare: "\<lbrace> R \<rbrace> f \<lbrace> Q \<rbrace>"
  shows "equiv_valid_inv I A (\<lambda> s. P s \<and> R s) (liftE f >>=E g)"
  using assms by (blast intro: liftE_bindE_ev_general)

lemmas liftE_bindE_ev_pre = liftE_bindE_ev[THEN equiv_valid_guard_imp]

lemma liftM_ev:
  assumes reads_res: "equiv_valid I A B P g"
  shows "equiv_valid I A B P (liftM f g)"
  apply (simp add: liftM_def)
  apply (rule bind_ev_general[THEN equiv_valid_guard_imp, OF return_ev reads_res wp_post_taut])
  apply simp
  done

lemma liftME_ev:
  assumes reads_res: "equiv_valid_inv I A P g"
  shows "equiv_valid_inv I A P (liftME f g)"
  apply(simp add: liftME_def)
  apply (rule bindE_ev_pre[OF returnOk_ev reads_res])
  apply (rule hoare_True_E_R)
  apply fast
  done

lemma whenE_ev:
  assumes a: "b \<Longrightarrow> equiv_valid_inv I A P m"
  shows "equiv_valid_inv I A (\<lambda>s. b \<longrightarrow> P s) (whenE b m)"
  unfolding whenE_def by (auto intro: a returnOk_ev_pre)

lemma whenE_throwError_bindE_ev:
  assumes "\<And> rv. \<not> b \<Longrightarrow> equiv_valid_inv I A P (g rv)"
  shows "equiv_valid_inv I A P (whenE b (throwError e) >>=E g)"
  apply (rule_tac Q="\<lambda> rv. P and (\<lambda> s. \<not> b)" in bindE_ev_pre)
     apply (rule gen_asm_ev)
     apply (blast intro: assms)
    apply (rule whenE_ev)
    apply (rule throwError_ev)
   apply (wp whenE_throwError_wp)
  apply simp
  done

(* FIXME: trivially generalised *)
lemma K_bind_ev:
  "equiv_valid I A B P f \<Longrightarrow> equiv_valid I A B P (K_bind f x)"
  by simp

subsection\<open>wp setup\<close>

lemmas splits_ev[wp_split] =
  bind_ev_pre bindE_ev_pre
  bind_ev bindE_ev
  if_ev_pre
  if_ev

lemmas wp_ev[wp] =
  return_ev_pre
  return_ev
  liftE_ev
  fail_ev_pre
  fail_ev
  assert_opt_ev
  assert_ev
  gets_ev
  gets_the_ev
  returnOk_ev_pre
  returnOk_ev
  throwError_ev_pre
  throwError_ev
  liftM_ev
  liftME_ev
  whenE_ev
  K_bind_ev

subsection\<open>crunch setup\<close>

lemmas pre_ev =
  hoare_pre
  equiv_valid_guard_imp

subsection\<open>Tom instantiates wpc\<close>

lemma wpc_helper_equiv_valid:
  "equiv_valid D A B Q f \<Longrightarrow> wpc_helper (P, P') (Q, Q') (equiv_valid D A B P f)"
  using equiv_valid_guard_imp
  apply (simp add: wpc_helper_def)
  apply (blast)
  done

wpc_setup "\<lambda>m. equiv_valid D A B Q m" wpc_helper_equiv_valid

subsection\<open>More hoare-like rules\<close>

lemma mapM_ev_pre:
  assumes reads_res: "\<And> x. x \<in> set lst \<Longrightarrow> equiv_valid_inv D A I (m x)"
  assumes invariant: "\<And> x. x \<in> set lst \<Longrightarrow> \<lbrace> I \<rbrace> m x \<lbrace> \<lambda>_. I \<rbrace>"
  assumes inv_established: "\<And> s. P s \<Longrightarrow> I s"
  shows "equiv_valid_inv D A P (mapM m lst)"
  using assms
  apply(atomize)
  apply(rule_tac Q=I in equiv_valid_guard_imp)
  apply(induct lst)
    apply(simp add: mapM_Nil return_ev_pre)
   apply(subst mapM_Cons)
   apply(rule bind_ev_pre[where P''="I"])
    apply(rule bind_ev[OF return_ev])
    apply fastforce
    apply (rule wp_post_taut)
    apply fastforce+
  done

lemma mapM_x_ev_pre:
  assumes reads_res: "\<And> x. x \<in> set lst \<Longrightarrow> equiv_valid_inv D A I (m x)"
  assumes invariant: "\<And> x. x \<in> set lst \<Longrightarrow> \<lbrace> I \<rbrace> m x \<lbrace> \<lambda>_. I \<rbrace>"
  assumes inv_established: "\<And> s. P s \<Longrightarrow> I s"
  shows "equiv_valid_inv D A P (mapM_x m lst)"
  apply(subst mapM_x_mapM)
  apply(rule bind_ev_pre[OF return_ev mapM_ev_pre])
  apply (blast intro: reads_res invariant inv_established wp_post_taut)+
  done

lemma mapM_ev:
  assumes reads_res: "\<And> x. x \<in> set lst \<Longrightarrow> equiv_valid_inv D A I (m x)"
  assumes invariant: "\<And> x. x \<in> set lst \<Longrightarrow> \<lbrace> I \<rbrace> m x \<lbrace> \<lambda>_. I \<rbrace>"
  shows "equiv_valid_inv D A I (mapM m lst)"
  using assms by (auto intro: mapM_ev_pre)

lemma mapM_x_ev:
  assumes reads_res: "\<And> x. x \<in> set lst \<Longrightarrow> equiv_valid_inv D A I (m x)"
  assumes invariant: "\<And> x. x \<in> set lst \<Longrightarrow> \<lbrace> I \<rbrace> m x \<lbrace> \<lambda>_. I \<rbrace>"
  shows "equiv_valid_inv D A I (mapM_x m lst)"
  using assms by (auto intro: mapM_x_ev_pre)

(* MOVE -- proof clagged from mapM_x_mapM *)
lemma mapME_x_mapME:
  "mapME_x f l = mapME f l >>=E (\<lambda> y. returnOk ())"
  apply (simp add: mapME_x_def sequenceE_x_def mapME_def sequenceE_def)
  apply (induct l, simp_all add: Let_def bindE_assoc)
  done

lemma mapME_ev_pre:
  assumes reads_res: "\<And> x. x \<in> set lst \<Longrightarrow> equiv_valid_inv D A I (m x)"
  assumes invariant: "\<And> x. x \<in> set lst \<Longrightarrow> \<lbrace> I \<rbrace> m x \<lbrace> \<lambda>_. I \<rbrace>,-"
  assumes inv_established: "\<And> s. P s \<Longrightarrow> I s"
  shows "equiv_valid_inv D A P (mapME m lst)"
  using assms
  apply(atomize)
  apply(rule_tac Q=I in equiv_valid_guard_imp)
  apply(induct lst)
    apply(simp add: mapME_Nil returnOk_ev_pre)
   apply(subst mapME_Cons)
   apply wp
   apply fastforce
   apply (rule hoare_True_E_R[where P="\<top>"])
   apply fastforce+
  done

lemma mapME_ev:
  assumes reads_res: "\<And> x. x \<in> set lst \<Longrightarrow> equiv_valid_inv I A P (m x)"
  assumes invariant: "\<And> x. x \<in> set lst \<Longrightarrow> \<lbrace> P \<rbrace> m x \<lbrace> \<lambda>_. P \<rbrace>, -"
  shows "equiv_valid_inv I A P (mapME m lst)"
  using assms by (auto intro: mapME_ev_pre)

lemma mapME_x_ev_pre:
  assumes reads_res: "\<And> x. x \<in> set lst \<Longrightarrow> equiv_valid_inv D A I (m x)"
  assumes invariant: "\<And> x. x \<in> set lst \<Longrightarrow> \<lbrace> I \<rbrace> m x \<lbrace> \<lambda>_. I \<rbrace>,-"
  assumes inv_established: "\<And> s. P s \<Longrightarrow> I s"
  shows "equiv_valid_inv D A P (mapME_x m lst)"
  unfolding mapME_x_mapME
  apply (wp assms mapME_ev_pre | simp)+
  done

lemma mapME_x_ev:
  assumes reads_res: "\<And> x. x \<in> set lst \<Longrightarrow> equiv_valid_inv D A I (m x)"
  assumes invariant: "\<And> x. x \<in> set lst \<Longrightarrow> \<lbrace> I \<rbrace> m x \<lbrace> \<lambda>_. I \<rbrace>, -"
  shows "equiv_valid_inv D A I (mapME_x m lst)"
  using assms by (auto intro: mapME_x_ev_pre)

lemma mapM_ev':
  assumes reads_res: "\<And> x. x \<in> set lst \<Longrightarrow> equiv_valid_inv D A (K (P x)) (m x)"
  shows "equiv_valid_inv D A (K (\<forall>x\<in>set lst. P x)) (mapM m lst)"
  apply(rule mapM_ev)
  apply(rule equiv_valid_guard_imp[OF reads_res], simp+, wp)
  done

lemma mapM_x_ev':
  assumes reads_res: "\<And> x. x \<in> set lst \<Longrightarrow> equiv_valid_inv D A (K (P x)) (m x)"
  shows "equiv_valid_inv D A (K (\<forall>x\<in>set lst. P x)) (mapM_x m lst)"
  apply(rule mapM_x_ev)
  apply(rule equiv_valid_guard_imp[OF reads_res], simp+, wp)
  done

lemma mapME_ev':
  assumes reads_res: "\<And> x. x \<in> set lst \<Longrightarrow> equiv_valid_inv D A (K (P x)) (m x)"
  shows "equiv_valid_inv D A (K (\<forall>x\<in>set lst. P x)) (mapME m lst)"
  apply(rule mapME_ev)
  apply(rule equiv_valid_guard_imp[OF reads_res], simp+, wp)
  done

lemma mapME_x_ev':
  assumes reads_res: "\<And> x. x \<in> set lst \<Longrightarrow> equiv_valid_inv D A (K (P x)) (m x)"
  shows "equiv_valid_inv D A (K (\<forall>x\<in>set lst. P x)) (mapME_x m lst)"
  apply(rule mapME_x_ev)
  apply(rule equiv_valid_guard_imp[OF reads_res], simp+, wp)
  done

subsection\<open>Rules for the specialised validity\<close>

lemma use_spec_ev:
  "(\<And>st. spec_equiv_valid st I A B P f) \<Longrightarrow> equiv_valid I A B P f"
  by (simp add: equiv_valid_def)

lemma drop_spec_ev:
  "equiv_valid I A B P f \<Longrightarrow> spec_equiv_valid st I A B P f"
  by (simp add: equiv_valid_def)

lemma spec_equiv_valid_guard_imp:
  assumes reads_res: "spec_equiv_valid_inv s' I A P' f"
  assumes guard_imp: "\<And> s. P s \<Longrightarrow> P' s"
  shows "spec_equiv_valid_inv s' I A P f"
  using assms
  by (fastforce simp: spec_equiv_valid_def equiv_valid_2_def)

lemma bind_spec_ev:
  assumes reads_res_2: "\<And> rv s''. (rv, s'') \<in> fst (f s') \<Longrightarrow> spec_equiv_valid_inv s'' I A (Q rv) (g rv)"
  assumes reads_res_1: "spec_equiv_valid_inv s' I A P' f"
  assumes hoare: "\<lbrace>P''\<rbrace> f \<lbrace>Q\<rbrace>"
  shows "spec_equiv_valid_inv s' I A (\<lambda>s. P' s \<and> P'' s) (f >>= g)"
  using reads_res_1
  apply (clarsimp simp: spec_equiv_valid_def equiv_valid_2_def valid_def bind_def split_def)
  apply (erule_tac x=t in allE)
  apply clarsimp
  apply (erule_tac x="(a, b)" in ballE)
  apply (erule_tac x="(ab, bb)" in ballE)
  apply clarsimp
  apply (cut_tac rv="ab" and s''="b" in reads_res_2)
   apply assumption
  apply (clarsimp simp: spec_equiv_valid_def equiv_valid_2_def)
  apply(erule_tac x=bb in allE)
  using hoare
  apply (fastforce simp: valid_def)+
  done

lemma bindE_spec_ev:
  assumes reads_res_2: "\<And> rv s''. (Inr rv, s'') \<in> fst (f s') \<Longrightarrow> spec_equiv_valid_inv s'' I A (Q rv) (g rv)"
  assumes reads_res_1: "spec_equiv_valid_inv s' I A P' f"
  assumes hoare: "\<lbrace>P''\<rbrace> f \<lbrace>Q\<rbrace>,-"
  shows "spec_equiv_valid_inv s' I A (\<lambda>s. P' s \<and> P'' s) (f >>=E g)"
  unfolding bindE_def
  apply (rule bind_spec_ev)
    prefer 3
    apply(rule hoare[simplified validE_R_def validE_def])
   apply(simp split: sum.split add: lift_def)
   apply(rule conjI)
    apply(fastforce simp: spec_equiv_valid_def throwError_def return_ev2)
   apply(fastforce simp: reads_res_2)
  apply(rule reads_res_1)
  done

lemma if_spec_ev:
  "\<lbrakk> G \<Longrightarrow> spec_equiv_valid_inv s' I A P f;
     \<not> G \<Longrightarrow> spec_equiv_valid_inv s' I A P' f'
   \<rbrakk>  \<Longrightarrow> spec_equiv_valid_inv s' I A (\<lambda>s. (G \<longrightarrow> P s) \<and> (\<not> G \<longrightarrow> P' s)) (if G then f else f')"
  by (cases G, simp+)

lemmas splits_spec_ev[wp_split] =
  drop_spec_ev
  spec_equiv_valid_guard_imp[OF bind_spec_ev] spec_equiv_valid_guard_imp[OF bindE_spec_ev]
  bind_spec_ev bindE_spec_ev
  spec_equiv_valid_guard_imp[OF if_spec_ev] if_spec_ev

(* Miscellaneous rules. *)

lemma assertE_ev[wp]:
  "equiv_valid_inv I A \<top> (assertE b)"
  unfolding assertE_def
  apply wp
  by simp

lemma equiv_valid_2_bindE:
  assumes g: "\<And>rv rv'. R' rv rv' \<Longrightarrow>
      equiv_valid_2 D A A (E \<oplus> R) (Q rv) (Q' rv') (g rv) (g' rv')"
  assumes h1: "\<lbrace>S\<rbrace> f \<lbrace>Q\<rbrace>,-"
  assumes h2: "\<lbrace>S'\<rbrace> f' \<lbrace>Q'\<rbrace>,-"
  assumes f: "equiv_valid_2 D A A (E \<oplus> R') P P' f f'"
  shows "equiv_valid_2 D A A (E \<oplus> R) (P and S) (P' and S') (f >>=E g) (f' >>=E g')"
  apply(unfold bindE_def)
  apply(rule equiv_valid_2_guard_imp)
    apply(rule_tac R'="E \<oplus> R'" and Q="case_sum \<top>\<top> Q" and Q'="case_sum \<top>\<top> Q'" and S=S and S'=S' in equiv_valid_2_bind)
       apply(clarsimp simp: lift_def split: sum.splits)
       apply(intro impI conjI allI)
          apply(simp add: throwError_def)
          apply(rule return_ev2)
          apply simp
         apply(simp)
        apply(simp)
       apply(fastforce intro: g)
      apply(rule f)
     apply(insert h1, fastforce simp: valid_def validE_R_def validE_def split: sum.splits)[1]
    apply(insert h2, fastforce simp: valid_def validE_R_def validE_def split: sum.splits)[1]
   by auto

lemma rel_sum_comb_equals:
  "((=) \<oplus> (=)) = (=)"
  apply(rule ext)
  apply(rule ext)
  apply(rename_tac a b)
  apply(case_tac a, auto)
  done

definition spec_equiv_valid_2_inv where
  "spec_equiv_valid_2_inv s I A R P P' f f' \<equiv>
      equiv_valid_2 I A A R (P and ((=) s)) P' f f'"

lemma spec_equiv_valid_def2:
  "spec_equiv_valid s I A A P f =
   spec_equiv_valid_2_inv s I A (=) P P f f"
  apply(simp add: spec_equiv_valid_def spec_equiv_valid_2_inv_def)
  done

lemma drop_spec_ev2_inv:
  "equiv_valid_2 I A A R P P' f f' \<Longrightarrow>
   spec_equiv_valid_2_inv s I A R P P' f f'"
  apply(simp add: spec_equiv_valid_2_inv_def)
  apply(erule equiv_valid_2_guard_imp, auto)
  done

lemma spec_equiv_valid_2_inv_guard_imp:
  "\<lbrakk>spec_equiv_valid_2_inv s I A R Q Q' f f'; \<And> s. P s \<Longrightarrow> Q s; \<And> s. P' s \<Longrightarrow> Q' s\<rbrakk> \<Longrightarrow>
    spec_equiv_valid_2_inv s I A R P P' f f'"
  by(auto simp: spec_equiv_valid_2_inv_def equiv_valid_2_def)

lemma bind_spec_ev2:
  assumes reads_res_2: "\<And> rv s' rv'. \<lbrakk>(rv, s') \<in> fst (f s); R' rv rv'\<rbrakk> \<Longrightarrow> spec_equiv_valid_2_inv s' I A R (Q rv) (Q' rv') (g rv) (g' rv')"
  assumes reads_res_1: "spec_equiv_valid_2_inv s I A R' P P' f f'"
  assumes hoare: "\<lbrace>S\<rbrace> f \<lbrace>Q\<rbrace>"
  assumes hoare': "\<lbrace>S'\<rbrace> f' \<lbrace>Q'\<rbrace>"
  shows "spec_equiv_valid_2_inv s I A R (P and S) (P' and S') (f >>= g) (f' >>= g')"
  using reads_res_1
  apply (clarsimp simp: spec_equiv_valid_2_inv_def equiv_valid_2_def bind_def split_def)
  apply (erule_tac x=t in allE)
  apply clarsimp
  apply (drule_tac x="(a, b)" in bspec, assumption)
  apply (drule_tac x="(ab, bb)" in bspec, assumption)
  apply clarsimp
  apply (cut_tac rv="a" and s'="b" in reads_res_2)
    apply assumption
   apply assumption
  apply (clarsimp simp: spec_equiv_valid_2_inv_def equiv_valid_2_def)
  apply(drule_tac x=bb in spec)
  apply clarsimp
  using hoare hoare'
  apply (fastforce simp: valid_def)+
  done

lemma spec_equiv_valid_2_inv_bindE:
  assumes g: "\<And>rv s' rv'. \<lbrakk>(Inr rv, s') \<in> fst (f s); R' rv rv'\<rbrakk> \<Longrightarrow>
      spec_equiv_valid_2_inv s' I A (E \<oplus> R) (Q rv) (Q' rv') (g rv) (g' rv')"
  assumes h1: "\<lbrace>S\<rbrace> f \<lbrace>Q\<rbrace>,-"
  assumes h2: "\<lbrace>S'\<rbrace> f' \<lbrace>Q'\<rbrace>,-"
  assumes f: "spec_equiv_valid_2_inv s I A (E \<oplus> R') P P' f f'"
  shows "spec_equiv_valid_2_inv s I A (E \<oplus> R) (P and S) (P' and S') (f >>=E g) (f' >>=E g')"
  apply(unfold bindE_def)
  apply(rule spec_equiv_valid_2_inv_guard_imp)
    apply(rule_tac R'="E \<oplus> R'" and Q="case_sum \<top>\<top> Q" and Q'="case_sum \<top>\<top> Q'" and S=S and S'=S' in bind_spec_ev2)
       apply(clarsimp simp: lift_def split: sum.splits)
       apply(intro impI conjI allI)
          apply(simp add: throwError_def)
          apply(rule drop_spec_ev2_inv[OF return_ev2])
          apply simp
         apply(simp)
        apply(simp)
       apply(fastforce intro: g)
      apply(rule f)
     apply(insert h1, fastforce simp: valid_def validE_R_def validE_def split: sum.splits)[1]
    apply(insert h2, fastforce simp: valid_def validE_R_def validE_def split: sum.splits)[1]
   by auto

lemma trancl_subset_equivalence:
  "\<lbrakk>(a, b) \<in> r'\<^sup>+; \<forall>x. (a, x)\<in>r'\<^sup>+ \<longrightarrow> Q x; \<forall>x y. Q x \<longrightarrow> ((y, x) \<in> r) = ((y, x) \<in> r')\<rbrakk> \<Longrightarrow> (a, b) \<in> r\<^sup>+"
  apply(induct a b rule: trancl.induct)
   apply(blast)
  apply(simp)
  apply(rule_tac b=b in trancl_into_trancl)
   apply(simp)
  apply(erule_tac x=c in allE)
  apply(subgoal_tac "(a, c) \<in> r'\<^sup>+")
   apply(auto)
   done

lemma equiv_valid_rv_gets_compD:
  "equiv_valid_rv_inv I A R P (gets (f \<circ> g)) \<Longrightarrow>
   equiv_valid_rv_inv I A (\<lambda> rv rv'. R (f rv) (f rv')) P (gets g)"
  apply(clarsimp simp: equiv_valid_2_def gets_def bind_def return_def get_def)
  done


lemma liftE_ev2:
  "equiv_valid_2 I A B R P P' f f' \<Longrightarrow>
   equiv_valid_2 I A B (E \<oplus> R) P P' (liftE f) (liftE f')"
  apply(clarsimp simp: liftE_def equiv_valid_2_def bind_def return_def)
  apply fastforce
  done

lemma whenE_spec_ev2_inv:
  assumes a: "b \<Longrightarrow> spec_equiv_valid_2_inv s I A R P P' m m'"
  assumes r: "\<And> x. R x x"
  shows "spec_equiv_valid_2_inv s I A R P P' (whenE b m) (whenE b m')"
  unfolding whenE_def
  apply (auto intro: a simp: returnOk_def intro!: drop_spec_ev2_inv[OF return_ev2] intro: r)
  done

lemma whenE_spec_ev:
  assumes a: "b \<Longrightarrow> spec_equiv_valid_inv s I A P m"
  shows "spec_equiv_valid_inv s I A P  (whenE b m) "
  unfolding whenE_def
  apply (auto intro: a simp: returnOk_def intro!: drop_spec_ev[OF return_ev_pre])
  done


lemma spec_equiv_valid_2_inv_by_spec_equiv_valid:
  "\<lbrakk>spec_equiv_valid s I A A P f; P' = P; f' = f;
    (\<And> a. R a a)\<rbrakk> \<Longrightarrow>
       spec_equiv_valid_2_inv s I A R P P' f f'"
  apply(clarsimp simp: spec_equiv_valid_def spec_equiv_valid_2_inv_def)
  apply(fastforce simp: equiv_valid_2_def)
  done

lemma mapM_ev'':
  assumes reads_res: "\<And> x. x \<in> set lst \<Longrightarrow> equiv_valid_inv D A (P x) (m x)"
  assumes inv: "\<And> x. x \<in> set lst \<Longrightarrow> \<lbrace> \<lambda>s. \<forall>x\<in>set lst. P x s \<rbrace> m x \<lbrace> \<lambda>_ s. \<forall>x\<in>set lst. P x s \<rbrace>"
  shows "equiv_valid_inv D A (\<lambda> s. \<forall>x\<in>set lst. P x s) (mapM m lst)"
  apply(rule mapM_ev)
  apply(rule equiv_valid_guard_imp[OF reads_res]; simp)
  apply(wpsimp wp: inv)
  done

lemma mapM_x_ev'':
  assumes reads_res: "\<And> x. x \<in> set lst \<Longrightarrow> equiv_valid_inv D A (P x) (m x)"
  assumes inv: "\<And> x. x \<in> set lst \<Longrightarrow> \<lbrace> \<lambda>s. \<forall>x\<in>set lst. P x s \<rbrace> m x \<lbrace> \<lambda>_ s. \<forall>x\<in>set lst. P x s \<rbrace>"
  shows "equiv_valid_inv D A (\<lambda> s. \<forall>x\<in>set lst. P x s) (mapM_x m lst)"
  apply(rule mapM_x_ev)
  apply(rule equiv_valid_guard_imp[OF reads_res]; simp)
  apply(wpsimp wp: inv)
  done

lemma catch_ev[wp]:
  assumes ok:
    "equiv_valid I A A P f"
  assumes err:
    "\<And> e. equiv_valid I A A (E e) (handler e)"
  assumes hoare:
    "\<lbrace> P \<rbrace> f -, \<lbrace> E \<rbrace>"
  shows
  "equiv_valid I A A P (f <catch> handler)"
  apply(simp add: catch_def)
  apply (wp err ok | wpc | simp)+
   apply(insert hoare[simplified validE_E_def validE_def])[1]
   apply(simp split: sum.splits)
  by simp

lemma equiv_valid_rv_trivial:
  assumes inv: "\<And> P. \<lbrace> P \<rbrace> f \<lbrace> \<lambda>_. P \<rbrace>"
  shows "equiv_valid_rv_inv I A \<top>\<top> \<top> f"
  by(auto simp: equiv_valid_2_def dest: state_unchanged[OF inv])

lemma equiv_valid_2_trivial:
  assumes inv: "\<And> P. \<lbrace> P \<rbrace> f \<lbrace> \<lambda>_. P \<rbrace>"
  assumes inv': "\<And> P. \<lbrace> P \<rbrace> f' \<lbrace> \<lambda>_. P \<rbrace>"
  shows "equiv_valid_2 I A A \<top>\<top> \<top> \<top> f f'"
  by(auto simp: equiv_valid_2_def dest: state_unchanged[OF inv] state_unchanged[OF inv'])

lemma gen_asm_ev2_r:
  "\<lbrakk>P' \<Longrightarrow> equiv_valid_2 I A B R P Q f f'\<rbrakk> \<Longrightarrow>
   equiv_valid_2 I A B R P  (Q and (K P')) f f'"
  apply(fastforce simp: equiv_valid_2_def)
  done

lemma gen_asm_ev2_l:
  "\<lbrakk>P \<Longrightarrow> equiv_valid_2 I A B R Q P' f f'\<rbrakk> \<Longrightarrow>
   equiv_valid_2 I A B R (Q and (K P)) P' f f'"
  apply(fastforce simp: equiv_valid_2_def)
  done

lemma gen_asm_ev2_r':
  "\<lbrakk>P' \<Longrightarrow> equiv_valid_2 I A B R P \<top> f f'\<rbrakk> \<Longrightarrow>
   equiv_valid_2 I A B R P (\<lambda>s. P') f f'"
  apply(fastforce simp: equiv_valid_2_def)
  done

lemma gen_asm_ev2_l':
  "\<lbrakk>P \<Longrightarrow> equiv_valid_2 I A B R \<top> P' f f'\<rbrakk> \<Longrightarrow>
   equiv_valid_2 I A B R (\<lambda>s. P) P' f f'"
  apply(fastforce simp: equiv_valid_2_def)
  done

lemma equiv_valid_rv_liftE_bindE:
  assumes ev1:
  "equiv_valid_rv_inv I A W P f"
  assumes ev2:
  "\<And> rv rv'. W rv rv' \<Longrightarrow> equiv_valid_2 I A A R (Q rv) (Q rv') (g rv) (g rv')"
  assumes hoare:
  "\<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>"
  shows "equiv_valid_rv_inv I A R P ((liftE f) >>=E g)"
  apply(unfold bindE_def)
  apply(rule_tac Q="\<lambda> rv. K (\<forall> v. rv \<noteq> Inl v) and (\<lambda> s. \<forall> v. rv = Inr v \<longrightarrow> Q v s)" in equiv_valid_rv_bind)
    apply(rule_tac E="dc" in equiv_valid_2_liftE)
    apply(rule ev1)
   apply(clarsimp simp: lift_def split: sum.split)
   apply(insert ev2, fastforce simp: equiv_valid_2_def)[1]
  apply(insert hoare, clarsimp simp: valid_def liftE_def bind_def return_def split_def)
  done

lemma if_evrv:
  assumes "b \<Longrightarrow> equiv_valid_rv_inv I A R P f"
  assumes "\<not> b \<Longrightarrow> equiv_valid_rv_inv I A R Q g"
  shows "equiv_valid_rv_inv I A R (\<lambda>s. (b \<longrightarrow> P s) \<and> (\<not>b \<longrightarrow> Q s)) (if b then f else g)"
  apply (clarsimp split: if_split)
  using assms by blast

end
