(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(* A theory of guarded monadic bisimulation. *)

theory Bisim_UL
imports
  "Monad_WP/NonDetMonadVCG"
  Corres_UL
  EmptyFailLib
begin

(* This still looks a bit wrong to me, although it is more or less what I want \<emdash> we want to be
   able to move hoare triples across bisimulations, and this allows guards to be left behind, more or less
definition
  "bisim_underlying SR R P P' m m' \<equiv>
    \<forall>s s'. SR s s' \<longrightarrow> (P s \<longrightarrow> (\<forall>(r, t) \<in> fst (m s). \<exists>(r', t') \<in> fst (m' s'). R r r' \<and> SR t t')) \<and>
                       (P' s' \<longrightarrow> (\<forall>(r', t') \<in> fst (m' s'). \<exists>(r, t) \<in> fst (m s). R r r' \<and> SR t t'))"
*)

definition
  bisim_underlying :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> (('c \<times> 'a) set) \<times> bool) \<Rightarrow> ('b \<Rightarrow> (('d \<times> 'b) set) \<times> bool) \<Rightarrow> bool"
where
  "bisim_underlying SR R P P' m m' \<equiv>
    \<forall>s s'. SR s  s' \<and> P s \<and> P' s' \<longrightarrow> ((\<forall>(r, t) \<in> fst (m s). \<exists>(r', t') \<in> fst (m' s'). R r r' \<and> SR t t') \<and>
                                      (\<forall>(r', t') \<in> fst (m' s'). \<exists>(r, t) \<in> fst (m s). R r r' \<and> SR t t'))"

(*
lemma bisim_is_corres_both_ways:
  "bisim_underlying SR R P P' m m' = (corres_underlying SR False R P P' m m' \<and> corres_underlying (converse SR) False (swp R) P' P m' m)"
  unfolding bisim_underlying_def corres_underlying_def
  by (fastforce simp: swp_def Ball_def Bex_def)
*)

lemma bisim_valid:
  assumes ac: "bisim_underlying (=)  (=) P P' a a'"
  and     rl: "\<lbrace>Q\<rbrace> a \<lbrace>S\<rbrace>"
  shows   "\<lbrace>P and P' and Q\<rbrace> a' \<lbrace>S\<rbrace>"
  using ac rl
  unfolding bisim_underlying_def valid_def
  by (fastforce simp: split_def)

lemma bisim_valid2:
  assumes ac: "bisim_underlying (=) (=) P P' a a'"
  and     rl: "\<lbrace>Q\<rbrace> a' \<lbrace>S\<rbrace>"
  shows   "\<lbrace>P and P' and Q\<rbrace> a \<lbrace>S\<rbrace>"
  using ac rl
  unfolding bisim_underlying_def valid_def
  by (fastforce simp: split_def)

lemma bisim_underlyingI [consumes 0, case_names Left Right]:
  assumes r1: "\<And>s s' r t. \<lbrakk>SR s s'; P s; P' s'; (r, t) \<in> fst (m s) \<rbrakk> \<Longrightarrow> \<exists>(r', t') \<in> fst (m' s'). R r r' \<and> SR t t'"
  and     r2: "\<And>s s' r' t'. \<lbrakk>SR s s'; P s; P' s'; (r', t') \<in> fst (m' s') \<rbrakk> \<Longrightarrow> \<exists>(r, t) \<in> fst (m s). R r r' \<and> SR t t'"
  shows   "bisim_underlying SR R P P' m m'"
  unfolding bisim_underlying_def
  by (fastforce dest: r1 r2 simp: split_def)

lemma bisim_underlyingE1:
  assumes bs: "bisim_underlying SR R P P' m m'"
  and     sr: "SR s s'"
  and     ps: "P s" "P' s'"
  and     ms: "(r, t) \<in> fst (m s)"
  and     rl: "\<And>r' t'. \<lbrakk> (r', t') \<in> fst (m' s'); R r r'; SR t t' \<rbrakk> \<Longrightarrow> X"
  shows X
  using bs sr ps ms unfolding bisim_underlying_def
  by (fastforce intro: rl)

lemma bisim_underlyingE2:
  assumes bs: "bisim_underlying SR R P P' m m'"
  and     sr: "SR s s'"
  and     ps: "P s" "P' s'"
  and     ms: "(r', t') \<in> fst (m' s')"
  and     rl: "\<And>r t. \<lbrakk> (r, t) \<in> fst (m s); R r r'; SR t t' \<rbrakk> \<Longrightarrow> X"
  shows X
  using bs sr ps ms unfolding bisim_underlying_def
  by (fastforce intro: rl)

lemma bisim_split:
  assumes ac: "bisim_underlying SR R' P P' a c"
  and     bd: "\<And>r r'. R' r r' \<Longrightarrow> bisim_underlying SR R (Q r) (Q' r') (b r) (d r')"
  and     v1: "\<lbrace>S\<rbrace> a \<lbrace>Q\<rbrace>"
  and     v2: "\<lbrace>S'\<rbrace> c \<lbrace>Q'\<rbrace>"
  shows "bisim_underlying SR R (P and S) (P' and S') (a >>= b) (c >>= d)"
  using ac
  apply -
  apply (rule bisim_underlyingI)
   apply (clarsimp simp: in_monad split_def)
   apply (erule (4) bisim_underlyingE1)
   apply (frule (1) use_valid [OF _ v1])
   apply (frule (1) use_valid [OF _ v2])
   apply (erule (4) bisim_underlyingE1 [OF bd])
   apply (rename_tac r'' t'')
   apply (rule_tac x = "(r'', t'')" in bexI)
    apply clarsimp
   apply (fastforce simp: in_monad)
  apply (clarsimp simp: in_monad split_def)
  apply (erule (4) bisim_underlyingE2)
  apply (frule (1) use_valid [OF _ v1])
  apply (frule (1) use_valid [OF _ v2])
  apply (erule (4) bisim_underlyingE2 [OF bd])
  apply (rename_tac r'' t'')
   apply (rule_tac x = "(r'', t'')" in bexI)
    apply clarsimp
   apply (fastforce simp: in_monad)
  done

abbreviation
  "bisim \<equiv> bisim_underlying (=)"

lemma bisim_refl:
  assumes rrefl: "\<And>r. R r r"
  shows "bisim R P P' m m"
  apply (rule bisim_underlyingI)
   apply (clarsimp simp: split_def)
   apply (erule bexI [rotated])
   apply (simp add: rrefl)
  apply (clarsimp simp: split_def)
  apply (erule bexI [rotated])
  apply (simp add: rrefl)
  done

lemma bisim_guard_imp:
  assumes bs: "bisim_underlying SR R Q Q' m m'"
  and   rls: "\<And>s. P s \<Longrightarrow> Q s" "\<And>s. P' s \<Longrightarrow> Q' s"
  shows "bisim_underlying SR R P P' m m'"
  using bs rls
  by (fastforce intro!: bisim_underlyingI elim: bisim_underlyingE1  bisim_underlyingE2)

lemma bisim_return':
  assumes Rxx: "R x x'"
  shows "bisim_underlying SR R P P' (return x) (return x')"
  apply (rule bisim_underlyingI)
  apply (clarsimp simp: in_monad split_def Bex_def Rxx)
  apply (clarsimp simp: in_monad split_def Bex_def Rxx)
  done

lemmas bisim_return = bisim_return' [where P = \<top> and P' = \<top>]

lemma bisim_split_handle:
  assumes bm: "bisim (f' \<oplus> r) Pn Pn' m m'"
  and     bc: "\<And>x x'. f' x x' \<Longrightarrow> bisim (f \<oplus> r) (Pf x) (Pf' x') (c x) (c' x')"
  and     v1: "\<lbrace>P\<rbrace> m \<lbrace>\<lambda>_ _. True\<rbrace>, \<lbrace>Pf\<rbrace>"
  and     v2: "\<lbrace>P'\<rbrace> m' \<lbrace>\<lambda>_ _. True\<rbrace>, \<lbrace>Pf'\<rbrace>"
  shows "bisim (f \<oplus> r) (Pn and P) (Pn' and P') (m <handle> c) (m' <handle> c')"
  unfolding handleE_def handleE'_def
  apply (rule bisim_split [where Q = "\<lambda>r s. case_sum (\<lambda>l. Pf l s) (\<lambda>_. True) r" and Q' = "\<lambda>r s. case_sum (\<lambda>l. Pf' l s) (\<lambda>_. True) r", OF bm, folded validE_def])
  apply (case_tac ra)
   apply clarsimp
   apply (erule bc)
  apply clarsimp
  apply (rule bisim_return')
  apply simp
  apply (rule v1)
  apply (rule v2)
  done

(* Set up wpc *)
lemma wpc_helper_bisim:
  "bisim_underlying SR r Q Q' f f' \<Longrightarrow> wpc_helper (P, P') (Q, {s. Q' s}) (bisim_underlying SR r P (\<lambda>s. s \<in> P') f f')"
  apply (clarsimp simp: wpc_helper_def)
  apply (erule bisim_guard_imp)
   apply simp
  apply fastforce
  done

wpc_setup "\<lambda>m. bisim_underlying SR r P P' a m" wpc_helper_bisim
wpc_setup "\<lambda>m. bisim_underlying SR r P P' a (m >>= c)" wpc_helper_bisim

lemma bisim_split_refl:
  assumes bs: "\<And>r. bisim R (Q r) (Q' r) (b r) (d r)"
  and    v1: "\<lbrace>S\<rbrace> a \<lbrace>Q\<rbrace>"
  and   v2: "\<lbrace>S'\<rbrace> a \<lbrace>Q'\<rbrace>"
  shows "bisim R S S' (a >>= b) (a >>= d)"
  apply (rule bisim_guard_imp)
  apply (rule bisim_split [OF _ _ v1 v2])
   apply (rule bisim_refl [where P = \<top> and P' = \<top> and R = "(=)", OF refl])
  apply simp
  apply (rule bs)
  apply simp_all
  done

lemma bisim_throwError':
  "f e e' \<Longrightarrow> bisim_underlying SR (f \<oplus> R') P P' (throwError e) (throwError e')"
  apply (rule bisim_underlyingI)
  apply (clarsimp simp: in_monad Bex_def)+
  done

lemmas bisim_throwError = bisim_throwError' [where P = \<top> and P' = \<top>]

lemma bisim_splitE:
  assumes ac: "bisim_underlying SR (f \<oplus> R') P P' a c"
  and     bd: "\<And>r r'. R' r r' \<Longrightarrow> bisim_underlying SR (f \<oplus> R) (Q r) (Q' r') (b r) (d r')"
  and     v1: "\<lbrace>S\<rbrace> a \<lbrace>Q\<rbrace>, -"
  and     v2: "\<lbrace>S'\<rbrace> c \<lbrace>Q'\<rbrace>, -"
  shows "bisim_underlying SR (f \<oplus> R) (P and S) (P' and S') (a >>=E b) (c >>=E d)"
  apply (simp add: bindE_def lift_def[abs_def])
  apply (rule bisim_split [where Q = "\<lambda>r s. case_sum  (\<lambda>_. True) (\<lambda>l. Q l s) r" and Q' = "\<lambda>r s. case_sum  (\<lambda>_. True) (\<lambda>l. Q' l s) r", OF ac, folded validE_def, folded validE_R_def])
  apply (case_tac r')
   apply clarsimp
   apply (erule bisim_throwError')
  apply clarsimp
  apply (erule bd)
  apply (rule v1)
  apply (rule v2)
  done

lemma bisim_split_reflE:
  assumes ab: "\<And>r. bisim (f \<oplus> R) (Q r) (Q' r) (a r) (b r)"
  and     v1: "\<lbrace>S\<rbrace> m \<lbrace>Q\<rbrace>, -"
  and     v2: "\<lbrace>S'\<rbrace> m \<lbrace>Q'\<rbrace>, -"
  and  refls: "\<And>e. f e e" "\<And>r. R r r"
  shows "bisim (f \<oplus> R) S S' (m >>=E a) (m >>=E b)"
  using refls
  apply -
  apply (rule bisim_guard_imp)
  apply (rule bisim_splitE [where R' = "(=)", OF _ _ v1 v2])
  apply (rule bisim_refl)
  apply (case_tac r, simp_all)[1]
  apply simp
  apply (rule ab)
  apply simp+
  done

lemma bisim_split_bind_case_sum:
  "\<lbrakk>bisim_underlying sr (lr \<oplus> rr) P P' a d;
   \<And>rv rv'. lr rv rv' \<Longrightarrow> bisim_underlying sr r (R rv) (R' rv') (b rv) (e rv');
   \<And>rv rv'. rr rv rv' \<Longrightarrow> bisim_underlying sr r (S rv) (S' rv') (c rv) (f rv'); \<lbrace>Q\<rbrace> a \<lbrace>S\<rbrace>, \<lbrace>R\<rbrace>; \<lbrace>Q'\<rbrace> d \<lbrace>S'\<rbrace>, \<lbrace>R'\<rbrace>\<rbrakk>
  \<Longrightarrow> bisim_underlying sr r (P and Q) (P' and Q') (a >>= case_sum b c) (d >>= case_sum e f)"
  apply (erule bisim_split [where Q = "\<lambda>rv s. case_sum (\<lambda>l. R l s) (\<lambda>r. S r s) rv" and Q' = "\<lambda>rv s. case_sum (\<lambda>l. R' l s) (\<lambda>r. S' r s) rv", folded validE_def])
   apply (case_tac r')
    apply clarsimp
   apply clarsimp
  apply assumption+
  done

lemma bisim_liftE [simp]:
  "bisim_underlying SR (f \<oplus> R) P P' (liftE a) (liftE b) = bisim_underlying SR R P P' a b"
  by (fastforce simp: in_monad intro: bisim_underlyingI elim: bisim_underlyingE1  bisim_underlyingE2)

lemma bisim_when:
  assumes bs:  "b \<Longrightarrow> bisim_underlying SR R P P' m m'"
  and     rr: "R () ()"
  shows   "bisim_underlying SR R (\<lambda>s. b \<longrightarrow> P s) (\<lambda>s. b \<longrightarrow> P' s) (when b m) (when b m')"
  using assms
  apply (cases b, simp_all add: when_def)
  apply (erule bisim_return)
  done


(* not really used *)
definition
  "det_on P f \<equiv> \<forall>s. P s \<longrightarrow> (\<exists>r. f s = ({r}, False))"

lemma det_onE:
  "\<lbrakk>det_on P f; P s; \<And>r s'. \<lbrakk> (r, s') \<in> fst (f s); \<not> snd (f s)\<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  unfolding det_on_def by fastforce

lemma bisim_noop_det_on:
  assumes a: "\<And>s. \<lbrace>Pa and (=) s\<rbrace> a \<lbrace>\<lambda>_. (=) s\<rbrace>"
  and     b: "\<And>s. \<lbrace>Pb and (=) s\<rbrace> b \<lbrace>\<lambda>_. (=) s\<rbrace>"
  and    da: "det_on P a"
  and    db: "det_on P' b"
  shows   "bisim_underlying sr dc (Pa and P) (Pb and P') a b"
  using da db
  apply -
  apply (rule bisim_underlyingI)
  apply clarsimp
  apply (erule (1) det_onE)+
  apply (frule use_valid [OF _ a], fastforce)
  apply (frule use_valid [OF _ b], fastforce)
  apply fastforce

  apply clarsimp
  apply (erule (1) det_onE)+
  apply (frule use_valid [OF _ a], fastforce)
  apply (frule use_valid [OF _ b], fastforce)
  apply fastforce
  done

lemma det_on_gets:
  "det_on \<top> (gets f)" unfolding det_on_def
  by (clarsimp simp: gets_def return_def bind_def get_def)

lemma hoare_gen_asmE':
  "(P \<Longrightarrow> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>R\<rbrace>) \<Longrightarrow> \<lbrace>P' and K P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>R\<rbrace>"
  unfolding validE_def
  by (erule hoare_gen_asm)

lemma det_onE':
  "\<lbrakk>det_on P f; P s; \<And>r s'. \<lbrakk> f s = ({(r, s')}, False)\<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  unfolding det_on_def by fastforce

(* ugh *)
lemma det_on_guard_imp [wp_comb]:
  assumes da: "det_on P' a"
  and   "\<And>s. P s \<Longrightarrow> P' s"
  shows "det_on P a"
  using assms unfolding det_on_def by auto

lemma det_on_split [wp_split]:
  assumes da: "det_on Pa a"
  and     db: "\<And>x. det_on (Pb x) (b x)"
  and      v: "\<lbrace>Pb'\<rbrace> a \<lbrace>Pb\<rbrace>"
  shows "det_on (Pa and Pb') (a >>= b)"
  unfolding det_on_def using da
  apply -
  apply clarsimp
  apply (erule (1) det_onE)
  apply (frule (1) use_valid [OF _ v])
  apply (erule det_onE' [OF da])
  apply (erule det_onE' [OF db])
  apply (clarsimp simp: bind_def split_def)
  done

lemma det_det_on:
  "det m \<Longrightarrow> det_on \<top> m"
  unfolding det_def det_on_def by auto

lemma det_on_liftE [wp]:
  "det_on P m \<Longrightarrow> det_on P (liftE m)"
  unfolding liftE_def
  apply (rule det_on_guard_imp)
  apply (erule det_on_split [OF _ det_det_on])
   apply simp
  apply wp
  apply simp
  done

lemma det_on_lift [wp]:
  "(\<And>y. det_on (P y) (m y)) \<Longrightarrow> det_on (case_sum (\<lambda>_. \<top>) P x) (lift m x)"
  unfolding lift_def
  by (auto simp: det_on_def throwError_def return_def split: sum.splits)

lemma det_on_assert_opt [wp]:
  "det_on (\<lambda>_. x \<noteq> None) (assert_opt x)"
  unfolding det_on_def assert_opt_def by (fastforce split: option.splits simp: fail_def return_def)

lemmas dets_to_det_on [wp] = det_det_on [OF det_gets] det_det_on [OF return_det]

(* Set up wpc *)
lemma wpc_helper_det_on:
  "det_on Q f \<Longrightarrow> wpc_helper (P, P') (Q, Q') (det_on P f)"
  apply (clarsimp simp: wpc_helper_def det_on_def)
  done

wpc_setup "\<lambda>m. det_on P m" wpc_helper_det_on
wpc_setup "\<lambda>m. det_on P (m >>= c)" wpc_helper_det_on

lemma bisim_symb_exec_r_det_on:
  assumes z: "\<And>rv. bisim_underlying sr r P (Q' rv) x (y rv)"
  assumes y: "\<lbrace>P'\<rbrace> m \<lbrace>Q'\<rbrace>"
  assumes x: "\<And>s. \<lbrace>Pe and (=) s\<rbrace> m \<lbrace>\<lambda>r. (=) s\<rbrace>"
  assumes nf: "det_on Pd m"
  shows      "bisim_underlying sr r P (P' and Pe and Pd) x (m >>= (\<lambda>rv. y rv))"
  apply (rule bisim_guard_imp)
    apply (subst gets_bind_ign [symmetric], rule bisim_split)
      apply (rule bisim_noop_det_on [OF _ x det_on_gets])
      apply (rule hoare_pre, wp)
      apply fastforce
     apply (rule nf)
    apply (rule z)
   apply (wp y)+
  apply simp+
  done

definition
  not_empty :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b set \<times> bool) \<Rightarrow> bool"
where
  "not_empty P f \<equiv> \<forall>s. P s \<longrightarrow> (fst (f s) \<noteq> {})"

lemma not_emptyE:
  "\<lbrakk> not_empty P f; P s; \<And>r s'. \<lbrakk> (r, s') \<in> fst (f s)\<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  unfolding not_empty_def by fastforce

(* ugh *)
lemma not_empty_guard_imp [wp_comb]:
  assumes da: "not_empty P' a"
  and   "\<And>s. P s \<Longrightarrow> P' s"
  shows "not_empty P a"
  using assms unfolding not_empty_def by auto

lemma not_empty_split [wp_split]:
  assumes da: "not_empty Pa a"
  and     db: "\<And>x. not_empty (Pb x) (b x)"
  and      v: "\<lbrace>Pb'\<rbrace> a \<lbrace>Pb\<rbrace>"
  shows "not_empty (Pa and Pb') (a >>= b)"
  unfolding not_empty_def using da
  apply -
  apply clarsimp
  apply (erule (1) not_emptyE)
  apply (frule (1) use_valid [OF _ v])
  apply (erule not_emptyE [OF da])
  apply (erule not_emptyE [OF db])
  apply (fastforce simp: bind_def split_def)
  done

lemma not_empty_return [wp]:
  "not_empty \<top> (return x)"
  unfolding not_empty_def
  by (simp add: return_def)

lemma not_empty_liftE [wp]:
  assumes ne: "not_empty P m"
  shows "not_empty P (liftE m)"
  unfolding liftE_def
  apply (rule not_empty_guard_imp)
  apply (wp ne)
  apply simp
  done

lemma not_empty_lift [wp]:
  "(\<And>y. not_empty (P y) (m y)) \<Longrightarrow> not_empty (case_sum (\<lambda>_. \<top>) P x) (lift m x)"
  unfolding lift_def
  by (auto simp: not_empty_def throwError_def return_def split: sum.splits)

lemma not_empty_assert_opt [wp]:
  "not_empty (\<lambda>_. x \<noteq> None) (assert_opt x)"
  unfolding not_empty_def assert_opt_def by (fastforce split: option.splits simp: fail_def return_def)

lemma not_empty_gets [wp]:
  "not_empty \<top> (gets f)" unfolding not_empty_def
  by (clarsimp simp: gets_def return_def bind_def get_def)

(* Set up wpc *)
lemma wpc_helper_not_empty:
  "not_empty Q f \<Longrightarrow> wpc_helper (P, P') (Q, Q') (not_empty P f)"
  apply (clarsimp simp: wpc_helper_def not_empty_def)
  done

wpc_setup "\<lambda>m. not_empty P m" wpc_helper_not_empty
wpc_setup "\<lambda>m. not_empty P (m >>= c)" wpc_helper_not_empty

lemma bisim_noop:
  assumes a: "\<And>s. \<lbrace>Pa and (=) s\<rbrace> a \<lbrace>\<lambda>_. (=) s\<rbrace>"
  and     b: "\<And>s. \<lbrace>Pb and (=) s\<rbrace> b \<lbrace>\<lambda>_. (=) s\<rbrace>"
  and    da: "not_empty P a"
  and    db: "not_empty P' b"
  shows   "bisim_underlying sr dc (Pa and P) (Pb and P') a b"
  using da db
  apply -
  apply (rule bisim_underlyingI)
  apply clarsimp
  apply (erule (1) not_emptyE)+
  apply (frule use_valid [OF _ a], fastforce)
  apply (frule use_valid [OF _ b], fastforce)
  apply fastforce

  apply clarsimp
  apply (erule (1) not_emptyE)+
  apply (frule use_valid [OF _ a], fastforce)
  apply (frule use_valid [OF _ b], fastforce)
  apply fastforce
  done

lemma bisim_symb_exec_r:
  assumes  z: "\<And>rv. bisim_underlying sr r P (Q' rv) x (y rv)"
  assumes  y: "\<lbrace>P'\<rbrace> m \<lbrace>Q'\<rbrace>"
  assumes  x: "\<And>s. \<lbrace>Pe and (=) s\<rbrace> m \<lbrace>\<lambda>r. (=) s\<rbrace>"
  assumes ne: "not_empty Pd m"
  shows      "bisim_underlying sr r P (P' and Pe and Pd) x (m >>= (\<lambda>rv. y rv))"
  apply (rule bisim_guard_imp)
    apply (subst gets_bind_ign [symmetric], rule bisim_split)
      apply (rule bisim_noop [OF _ x not_empty_gets])
      apply (rule hoare_pre, wp)
      apply fastforce
     apply (rule ne)
    apply (rule z)
   apply (wp y)+
  apply simp+
  done

lemma bisim_not_empty:
  assumes bs: "bisim r P P' m m'"
  and     ne: "not_empty R m"
  shows   "not_empty (P and P' and R) m'"
  unfolding not_empty_def using bs ne
  apply clarsimp
  apply (erule (1) not_emptyE)
  apply (erule_tac s=s and s'=s in bisim_underlyingE1 [where SR = "(=)"])
      apply simp+
  done

lemma bisim_split_req:
  assumes ac: "bisim (=) P P' a c"
  and     bd: "\<And>r. bisim R (Q r) (Q' r) (b r) (d r)"
  and     v1: "\<lbrace>S\<rbrace> a \<lbrace>\<lambda>r. Q r and Q' r\<rbrace>"
  shows "bisim R (P and S) P' (a >>= b) (c >>= d)"
  using ac
  apply -
  apply (rule bisim_underlyingI)
   apply (clarsimp simp: in_monad split_def)
   apply (erule bisim_underlyingE1)
    apply simp
    apply assumption+
   apply (frule (1) use_valid [OF _ v1])
   apply clarsimp
   apply (rule bisim_underlyingE1 [OF bd])
    apply simp
    apply assumption+
   apply (rename_tac r'' t'')
   apply (rule_tac x = "(r'', t'')" in bexI)
    apply clarsimp
   apply (fastforce simp: in_monad)

   apply (clarsimp simp: in_monad split_def)
   apply (erule bisim_underlyingE2)
    apply simp
    apply assumption+
   apply (frule (1) use_valid [OF _ v1])
   apply clarsimp
   apply (rule bisim_underlyingE2 [OF bd])
    apply simp
    apply assumption+
   apply (rename_tac r'' t'')
   apply (rule_tac x = "(r'', t'')" in bexI)
    apply clarsimp
   apply (fastforce simp: in_monad)
  done

lemma bisim_splitE_req:
  assumes ac: "bisim (f \<oplus> (=)) P P' a c"
  and     bd: "\<And>r. bisim (f \<oplus> R) (Q r) (Q' r) (b r) (d r)"
  and     v1: "\<lbrace>S\<rbrace> a \<lbrace>\<lambda>r. Q r and Q' r\<rbrace>, -"
  shows "bisim (f \<oplus> R) (P and S) P' (a >>=E b) (c >>=E d)"
  using ac
  apply -
  apply (simp add: bindE_def lift_def[abs_def])
  apply (rule bisim_underlyingI)
   apply (clarsimp simp: in_monad split_def)
   apply (erule bisim_underlyingE1)
    apply simp
    apply assumption+
   apply (frule (1) use_valid [OF _ v1 [unfolded validE_R_def validE_def]])
   apply clarsimp
   apply (case_tac x)
    apply (clarsimp simp: in_monad)
    apply (rule_tac x = "(Inl y', t')" in bexI)
    apply fastforce
   apply (fastforce simp: in_monad)
   apply clarsimp
   apply (rule bisim_underlyingE1 [OF bd])
    apply simp
    apply assumption+
   apply (rename_tac r'' t'')
   apply (rule_tac x = "(r'', t'')" in bexI)
    apply clarsimp
   apply (fastforce simp: in_monad)

   apply (clarsimp simp: in_monad split_def)
   apply (erule bisim_underlyingE2)
    apply simp
    apply assumption+
   apply (frule (1) use_valid [OF _ v1 [unfolded validE_R_def validE_def]])
   apply clarsimp
   apply (case_tac r)
    apply (clarsimp simp: in_monad)
    apply (rule_tac x = "(Inl aa, s'')" in bexI)
    apply fastforce
   apply (fastforce simp: in_monad)
   apply clarsimp
   apply (rule bisim_underlyingE2 [OF bd])
    apply simp
    apply assumption+
   apply (rename_tac r'' t'')
   apply (rule_tac x = "(r'', t'')" in bexI)
    apply clarsimp
   apply (fastforce simp: in_monad)
  done

lemma bisim_symb_exec_r_bs:
  assumes bs: "bisim (=) R R' (return ()) m"
  and      z: "\<And>rv. bisim r P P' x (y rv)"
  shows      "bisim r (P and R and P') R' x (m >>= (\<lambda>rv. y rv))"
  apply (rule bisim_guard_imp)
    apply (subst return_bind [symmetric, where f = "\<lambda>(_ :: unit).x"],  rule bisim_split_req)
    apply (rule bs)
     apply (rule z)
     apply wp
   apply simp
  apply simp+
  done

end
