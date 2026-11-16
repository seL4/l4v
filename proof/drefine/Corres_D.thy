(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
 * Corres/Refinement for capDL
 *
 * Instantiates corres_underlying with capDL state translation and types.
 *)

theory Corres_D
imports StateTranslationProofs_DR Lib.Corres_Method
begin

declare dxo_noop[simp]

(* state relation as set, in (simp split_def) normal form *)
abbreviation
dcorres ::
    "('a::type \<Rightarrow> 'b::type \<Rightarrow> bool)
     \<Rightarrow> (cdl_state \<Rightarrow> bool)
       \<Rightarrow> (det_state \<Rightarrow> bool)
         \<Rightarrow> 'a::type k_monad
           \<Rightarrow> (det_state
              \<Rightarrow> ('b::type \<times> det_state) set \<times>
                bool)
             \<Rightarrow> bool"
where
  "dcorres \<equiv> corres_underlying {ss'. transform (snd ss') = fst ss'} False False"

lemma corres_bind_ignore_ret_rhs:
  "corres_underlying sr nf nf' rvr P P' a (do f; g od)
    \<Longrightarrow> corres_underlying sr nf nf' rvr P P' a (do y\<leftarrow> f;g od)"
  by (simp add: bind_def)

lemma corres_free_fail:
  "dcorres c P P' f fail"
  by (fastforce simp: corres_underlying_def bind_def fail_def)

lemma corres_free_return:
  "dcorres dc P P' (return a) (return b)"
  by (clarsimp simp:return_def bind_def corres_underlying_def)

lemma dcorres_chaos:
  "(\<And>rv'. \<exists>rv. r rv rv') \<Longrightarrow> dcorres r P P' chaos m"
  by (rule corres_guard_imp[OF corres_chaos_nf'])
     auto

lemma dcorres_chaos_dc:
  "dcorres dc P P' chaos m"
  by (rule dcorres_chaos)
     simp

lemma dcorres_chaos_dc_dc:
  "dcorres (dc \<oplus> dc) P P' chaos m"
  by (rule dcorres_chaos)
     (case_tac rv'; auto)

lemma dcorres_other_invocation:
  "\<lbrakk> \<And>P. \<lbrace>P\<rbrace> m \<lbrace>\<lambda>_. P\<rbrace>; \<And>y. R OtherInvocation y \<rbrakk> \<Longrightarrow>
   dcorres (dc \<oplus> R) P P' other_invocation m"
  apply (clarsimp simp: corres_underlying_def)
  apply (rename_tac s' rv t')
  apply (drule_tac P="(=) s'" in use_valid, assumption, rule refl)
  apply (case_tac rv; force simp: alternative_def returnOk_def throwError_def return_def)
  done

lemma corres_free_set_object:
  "\<lbrakk> \<forall> s s'. s = transform s' \<and> P s \<and> P' s' \<longrightarrow>
             s = transform ((\<lambda>s. s \<lparr>kheap := (kheap s)(ptr \<mapsto> obj)\<rparr>) s')\<rbrakk> \<Longrightarrow>
  dcorres dc P P' (return a) (set_object ptr obj )"
  by (clarsimp simp: corres_underlying_def put_def return_def modify_def bind_def get_def
                     set_object_def get_object_def in_monad)


(* Some dummy corres *)

lemma corres_dummy_return_l:
  "dcorres c P P' (do x\<leftarrow>f;return x od) g \<Longrightarrow> dcorres c P P' f g"
  by (fastforce simp: corres_underlying_def bind_def return_def)

lemma corres_dummy_return_pl:
  "dcorres c P P' (do return b; f od) g \<Longrightarrow> dcorres c P P' f g"
  by (fastforce simp: corres_underlying_def bind_def return_def)

lemma corres_dummy_return_r:
  "dcorres c P P' f (do x\<leftarrow>g;return x od) \<Longrightarrow> dcorres c P P' f g"
  by (fastforce simp: corres_underlying_def bind_def return_def)

lemma corres_dummy_return_pr:
  "dcorres c P P' f (do return b; g od)  \<Longrightarrow> dcorres c P P' f g"
  by (fastforce simp: corres_underlying_def bind_def return_def)

lemma corres_dummy_returnOk_r:
  "dcorres c P P' f (g >>=E returnOk) \<Longrightarrow> dcorres c P P' f g"
  by simp

lemma corres_dummy_returnOk_pl:
  "dcorres c P P' (returnOk b >>=E (\<lambda>_. f)) g \<Longrightarrow> dcorres c P P' f g"
  by (fastforce simp: corres_underlying_def bindE_def returnOk_def)

lemma dcorres_free_throw:
  assumes "\<And>s. \<lbrace>(=) s\<rbrace> f \<lbrace>\<lambda>r. \<bottom>\<rbrace>, \<lbrace>\<lambda>e. (=) s\<rbrace>"
  shows "dcorres (dc \<oplus> r) P P' Monads_D.throw f"
  using assms
  apply (simp add:corres_underlying_def throwError_def return_def)
  apply (clarsimp simp:validE_def valid_def)
  apply (drule_tac x = b in meta_spec)
  apply (fastforce split: sum.splits)
  done

lemma absorb_imp:"B \<and> A \<Longrightarrow>  (a\<longrightarrow>A) \<and> B "
  by simp


(* This lemma is convienent if you want keep the prefix while split *)

lemma  corres_split_keep_pfx:
  assumes x: "corres_underlying sr nf nf' r' P P' a c"
  assumes y: "\<And>rv rv'. r' rv rv' \<Longrightarrow> corres_underlying sr nf nf' r (P and (Q rv)) (P' and (Q' rv')) (b rv) (d rv')"
  assumes    "\<lbrace>P\<rbrace> a \<lbrace>\<lambda>x. P and (Q x)\<rbrace>" "\<lbrace>P'\<rbrace> c \<lbrace>\<lambda>x. P' and (Q' x)\<rbrace>"
  shows      "corres_underlying sr nf nf' r P P' (a >>= (\<lambda>rv. b rv)) (c >>= (\<lambda>rv'. d rv'))"
  using assms by (rule corres_underlying_split)

(* Following 2 lemmas allows you to get rid of the get function and move the prefix outside *)

lemma dcorres_absorb_pfx:
  assumes "dcorres r (P) (P') (f) (f')"
  shows "\<And> s s'. \<lbrakk>s = transform s'; P s; P' s'\<rbrakk> \<Longrightarrow> dcorres r ((=) s) ((=) s') f f' "
  using assms
by (fastforce simp:corres_underlying_def)

lemma dcorres_expand_pfx:
assumes "\<And> s s'. \<lbrakk>s = transform s'; P s; P' s'\<rbrakk> \<Longrightarrow> dcorres r ((=) s) ((=) s') f f' "
shows "dcorres r P P' f f'"
using assms
by (fastforce simp:corres_underlying_def)

lemma dcorres_absorb_get_l:
  assumes "!!s'. \<lbrakk> P (transform s'); P' s'\<rbrakk> \<Longrightarrow> dcorres rv ((=) (transform s')) ((=) s') (f (transform s')) g"
  shows "dcorres rv P P' (do t\<leftarrow> get; f t od)  g"
  apply (rule corres_symb_exec_l [where Q="%x. P and ((=) x)"])
    apply (rule dcorres_expand_pfx)
    apply clarsimp
    apply (rule assms)
  apply (clarsimp simp: valid_def exs_valid_def get_def)+
  done

lemma dcorres_absorb_get_r:
  assumes "!!s'. \<lbrakk>P (transform s'); P' s'\<rbrakk> \<Longrightarrow> dcorres rv ((=) (transform s')) ((=) s') f (g s')"
  shows "dcorres rv P P' f (do t\<leftarrow> get; g t od)"
  apply (rule corres_symb_exec_r [where Q'="%x. P' and ((=) x)"])
    apply (rule dcorres_expand_pfx)
    apply clarsimp
    apply (rule assms)
  apply (clarsimp simp: valid_def exs_valid_def get_def)+
  done

lemma dcorres_absorb_gets_the:
  assumes A: "\<And>s' obj'. \<lbrakk>P' s';  g' s' = Some obj'; P (transform s')\<rbrakk>
          \<Longrightarrow> dcorres r ((=) (transform s')) ((=) s') (f) (f' obj')"
  shows "dcorres r P P' (f) (do a\<leftarrow> gets_the (g'); f' a od)"
  apply (simp add: gets_the_def gets_def bind_assoc)
  apply (rule dcorres_absorb_get_r)
  apply (clarsimp simp :assert_opt_def split:option.splits)
  apply (clarsimp simp:corres_free_fail)
  apply (rule dcorres_expand_pfx)
  apply (clarsimp simp:assms)
done


lemma dcorres_get:
  assumes A: "\<And>s s'. \<lbrakk>s = transform s';P s; P' s'\<rbrakk>
          \<Longrightarrow> dcorres r ((=) s) ((=) s') (f s) (f' s')"
  shows "dcorres r P P' (do s\<leftarrow>get;f s od) (do s'\<leftarrow> get; f' s' od)"
  apply (rule dcorres_expand_pfx)
  apply (rule_tac r'="\<lambda>r r'. s=r \<and> s'=r'" and Q="%x. (=) s" and Q'="%x. (=) s'" in corres_split_forwards')
    apply (clarsimp simp: corres_underlying_def get_def)
    apply wp+
  apply (drule A)
  apply clarsimp+
done

lemma dcorres_gets_the:
  assumes A: "\<And>s s' obj obj'. \<lbrakk>s = transform s';P s; P' s';  g' s' = Some obj' ;g s = Some obj\<rbrakk>
          \<Longrightarrow> dcorres r ((=) s) ((=) s') (f obj) (f' obj')"
  assumes B: "\<And>s s'. \<lbrakk>s = transform s'; P s; P' s' ; g' s' \<noteq> None\<rbrakk> \<Longrightarrow> g s \<noteq> None"
  shows "dcorres r P P' (do a\<leftarrow>gets_the (g);f a od) (do a\<leftarrow> gets_the (g'); f' a od)"
  apply (simp add:gets_the_def)
  apply (simp add: gets_def)
  apply (subst bind_assoc)+
  apply (rule corres_split_keep_pfx[where r'="\<lambda>s s'. s = transform s'\<and> P s \<and> P' s'"
                                      and Q="\<lambda>x s. x = s" and Q'="\<lambda>x s. x = s "])
     apply (clarsimp simp: corres_underlying_def get_def)
    apply (simp add: assert_opt_def)
    apply (rename_tac x)
    apply (case_tac "g' x = None")
     apply (clarsimp split:option.splits simp:corres_free_fail)
    apply (subgoal_tac "\<exists>obj. g (transform x) \<noteq> None")
     apply (clarsimp split:option.splits)
     apply (rule_tac Q="(=) (transform x)" and Q'="(=) x" in corres_guard_imp)
       apply (simp add: A)+
    using B
    apply (wp|clarsimp)+
  done

(* rules used to get rid of the error branchs of decode proof *)
lemma dcorres_throw:
  "dcorres (dc \<oplus> anyrel) \<top> \<top> (Monads_D.throw) (throwError anyerror)"
  by (clarsimp simp:corres_underlying_def throwError_def return_def)

lemma dcorres_alternative_throw:
  "dcorres (dc \<oplus> anyrel) \<top> \<top> (any \<sqinter> Monads_D.throw) (throwError anyerror)"
  by (rule corres_alternate2[OF dcorres_throw])

lemma dcorres_returnOk:
  "r a b \<Longrightarrow>
  dcorres (dc \<oplus> r) \<top> \<top> (returnOk a) (returnOk b)"
 by (clarsimp simp:corres_underlying_def return_def returnOk_def)

lemma dcorres_return:
  "r a b \<Longrightarrow> dcorres (r) (\<lambda>_. True) (\<lambda>_. True) (return a) (return b)"
  by (clarsimp simp:return_def corres_underlying_def)

lemma split_return_throw_thingy:
  "\<lbrakk> \<And>s. \<lbrace>(=) s\<rbrace> g \<lbrace>\<lambda>rv s'. s' = s \<and> rvP rv\<rbrace>,\<lbrace>\<lambda>ft. (=) s\<rbrace>;
     \<And>rv. rvP rv \<Longrightarrow> corres_underlying sr nf nf' (dc \<oplus> r) P P' (f \<sqinter> throwError e) (h rv);
        nf' \<Longrightarrow> no_fail P' g \<rbrakk>
     \<Longrightarrow> corres_underlying sr nf nf' (dc \<oplus> r) P P'
             (f \<sqinter> throwError e) (g >>=E h)"
  apply (simp add: bindE_def)
  apply (rule corres_guard_imp)
    apply (rule_tac Q'="\<lambda>rv. P' and (\<lambda>_. isRight rv \<longrightarrow> rvP (theRight rv))"
               in corres_symb_exec_r[where P=P and P'=P'], simp_all)
    apply (case_tac rv)
     apply (simp add: lift_def)
     apply (rule corres_alternate2, simp)
    apply (rule corres_gen_asm2)
    apply (simp add: lift_def isRight_def)
   apply (clarsimp simp add: validE_def valid_def)
   apply (erule meta_allE, drule(1) bspec)
   apply (auto simp: isRight_def split: sum.split_asm)[1]
  apply (simp add: validE_def)
  apply (rule hoare_strengthen_post, assumption)
  apply (simp split: sum.split_asm)
  done

lemma case_sum_triv_return:
  "case_sum throwError returnOk = return"
  apply (intro ext)
  apply (simp add: throwError_def returnOk_def return_def
            split: sum.split)
  done

lemma lift_returnOk_bind_triv:
  "g >>= (lift returnOk) = g"
  by (simp add: lift_def case_sum_triv_return cong: bind_cong)

lemma corres_return_throw_thingy:
  "\<lbrakk> \<And>s. \<lbrace>(=) s\<rbrace> g \<lbrace>\<lambda>rv s'. s' = s \<and> Q rv\<rbrace>,\<lbrace>\<lambda>ft. (=) s\<rbrace>;
        nf' \<Longrightarrow> no_fail P' g; \<forall>rv. Q rv \<longrightarrow> r v rv \<rbrakk>
     \<Longrightarrow> corres_underlying sr nf nf' (dc \<oplus> r) P P'
             (returnOk v \<sqinter> throwError e) (g)"
  apply (subst lift_returnOk_bind_triv[where g=g, symmetric])
  apply (fold bindE_def, rule split_return_throw_thingy)
    apply assumption
   apply (rule corres_alternate1)
   apply (clarsimp simp: returnOk_def)
  apply simp
  done

(*
 * We can consider correspondence of a function starting with
 * a conditional "throw" in two parts: when the error occurs
 * and when the error does not occur.
 *)
lemma dcorres_whenE_throwError_abstract:
  "\<lbrakk>cond \<Longrightarrow> dcorres rvrel M M' m (throwError e);
    \<not> cond \<Longrightarrow> dcorres rvrel N N' m m'\<rbrakk> \<Longrightarrow>
   dcorres rvrel (M and N) (M' and N') m (whenE cond (throwError e) >>=E (\<lambda>_. m'))"
  apply (unfold whenE_def)
  apply (case_tac cond)
   apply (clarsimp)
   apply (erule corres_guard_imp, simp+)
  apply (erule corres_guard_imp, simp+)
  done

lemma dcorres_whenE_throwError_abstract':
  "\<lbrakk>cond \<Longrightarrow> dcorres rvrel G G' m (throwError e);
    \<not> cond \<Longrightarrow> dcorres rvrel G G' m m'\<rbrakk> \<Longrightarrow>
   dcorres rvrel G G' m (whenE cond (throwError e) >>=E (\<lambda>_. m'))"
  apply (rule corres_guard_imp)
    apply (rule dcorres_whenE_throwError_abstract, assumption, assumption)
   apply simp
  apply simp
  done

lemma dcorres_symb_exec_r:
  "\<lbrakk>\<And>rv. dcorres r P (Q' rv) h (g rv); \<lbrace>P'\<rbrace> f \<lbrace>\<lambda>r. Q' r\<rbrace>;
    \<And>cs. \<lbrace>\<lambda>ps. transform ps = cs\<rbrace> f \<lbrace>\<lambda>r s. transform s = cs\<rbrace>\<rbrakk>
  \<Longrightarrow> dcorres r P P' h (f>>=g)"
  apply (rule corres_dummy_return_pl)
  apply (rule corres_guard_imp)
    apply (rule corres_split[where R="\<lambda>rv. P" and R'="\<lambda>rv. Q' rv" and r' = dc])
       apply (clarsimp simp:valid_def corres_underlying_def return_def)
      apply simp
     apply wp
    apply simp+
  done

lemma dcorres_symb_exec_r_strong:
  "\<lbrakk>\<And>rv. dcorres r P (Q' rv) h (g rv); \<lbrace>P'\<rbrace> f \<lbrace>\<lambda>r. Q' r\<rbrace>;
    \<And>cs. \<lbrace>\<lambda>ps. P' ps \<and> transform ps = cs\<rbrace> f \<lbrace>\<lambda>r s. transform s = cs\<rbrace>\<rbrakk>
  \<Longrightarrow> dcorres r P P' h (f>>=g)"
  apply (rule corres_dummy_return_pl)
  apply (rule corres_guard_imp)
    apply (rule corres_split[where R="\<lambda>rv. P" and P'=P' and R'="\<lambda>rv. Q' rv" and r' = dc])
       defer
       apply (unfold K_bind_def)
      apply (assumption)
     apply wp
    apply simp+
   apply (clarsimp simp:valid_def corres_underlying_def return_def)
  done

lemma dcorres_to_wp:
  "dcorres dc \<top> Q (return x) g \<Longrightarrow> \<lbrace>\<lambda>s. Q s \<and> transform s = cs\<rbrace>g\<lbrace>\<lambda>r s. transform s = cs\<rbrace>"
  by (fastforce simp:corres_underlying_def valid_def return_def)

lemma wp_to_dcorres:
  "(\<And>cs. \<lbrace>\<lambda>s. Q s \<and> transform s = cs\<rbrace> g \<lbrace>\<lambda>r s. transform s = cs\<rbrace>) \<Longrightarrow>  dcorres dc (\<lambda>_. True) Q (return x) g"
  by (clarsimp simp:corres_underlying_def valid_def return_def)

lemma dcorres_symb_exec_rE:
  "\<lbrakk>\<And>rv. dcorres r P (Q' rv) h (g rv); \<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>; \<And>cs. \<lbrace>\<lambda>ps. transform ps = cs\<rbrace> f \<lbrace>\<lambda>r s. transform s = cs\<rbrace>\<rbrakk>
  \<Longrightarrow> dcorres r P P' h (liftE f >>=E g)"
  apply (simp add: liftE_def lift_def bindE_def)
  apply (erule (1) dcorres_symb_exec_r)
  apply assumption
  done

lemma throw_handle:
  "(Monads_D.throw <handle2> (\<lambda>_. m)) = m"
  by (simp add: handleE'_def throwError_def)

lemma corres_handle2:
  "corres_underlying R False nf' (dc \<oplus> r) P P' m m' \<Longrightarrow>
   corres_underlying R False nf' (dc \<oplus> r) P P' (m <handle2> (\<lambda>x. Monads_D.throw)) m'"
  apply (clarsimp simp: corres_underlying_def)
  apply (rule conjI)
   prefer 2
   apply fastforce
  apply clarsimp
  apply (drule (1) bspec, clarsimp)
  apply (drule (1) bspec, clarsimp)
  apply (clarsimp simp: handleE'_def)
  apply (simp add: bind_def)
  apply (rule bexI)
   prefer 2
   apply assumption
  apply (simp add: return_def throwError_def split: sum.splits)
  apply fastforce
  done

lemma corres_handle2':
  "corres_underlying R False nf' (dc \<oplus> r) P P' m m' \<Longrightarrow>
   corres_underlying R False nf' (dc \<oplus> r) P P' m (m' <handle2> (throwError \<circ> e))"
  apply (clarsimp simp: corres_underlying_def)
  apply (rule conjI)
   prefer 2
   apply (clarsimp simp: handleE'_def bind_def)
   apply (drule (1) bspec, clarsimp)
   apply (drule (1) bspec, clarsimp)
   apply (clarsimp simp: return_def throwError_def split: sum.splits)
  apply clarsimp
  apply (drule (1) bspec, clarsimp)
  apply (clarsimp simp: handleE'_def bind_def)
  apply (drule (1) bspec, clarsimp)
  apply (fastforce simp: return_def throwError_def split: sum.splits)
  done

lemma corres_alternative_throw_splitE:
  assumes a: "corres_underlying R False z (dc \<oplus> r') P P' (f \<sqinter> Monads_D.throw) f'"
  assumes b:  "\<And>x x'. r' x x' \<Longrightarrow> corres_underlying R False z (dc \<oplus> r) (Q x) (Q' x') (g x \<sqinter> Monads_D.throw) (g' x')"
  assumes f: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>\<lambda>_. \<top>\<rbrace>"
  assumes f': "\<lbrace>P'\<rbrace> f' \<lbrace>Q'\<rbrace>, \<lbrace>\<lambda>_. \<top>\<rbrace>"
  assumes f'_eq: "\<And>s. \<lbrace>(=) s\<rbrace> f' \<lbrace>\<lambda>_. (=) s\<rbrace>"
  assumes g'_eq: "\<And>s x. \<lbrace>\<lambda>s'. s' = s \<and> Q' x s'\<rbrace> g' x \<lbrace>\<lambda>_. \<top>\<rbrace>, \<lbrace>\<lambda>_. (=) s\<rbrace>"
  shows "corres_underlying R False z (dc \<oplus> r) P P' ((f >>=E g) \<sqinter> Monads_D.throw) (f' >>=E g')"
  apply (clarsimp simp: bindE_def corres_underlying_def)
  apply (rule conjI)
   prefer 2
   apply (frule (2) corres_underlyingD [OF a])
    apply simp
   apply (clarsimp simp: bind_def split_def lift_def)
   apply (clarsimp simp: throwError_def return_def split: sum.splits)
   apply (drule (1) bspec, clarsimp simp: alternative_def)
   apply (drule b)
   apply (thin_tac "(a,b) \<in> R")
   apply (drule (1) corres_underlyingD)
      apply (drule use_valid, rule f[unfolded validE_def])
       apply assumption
      apply simp
     apply (drule use_valid, rule f'[unfolded validE_def])
      apply assumption
     apply simp
    apply simp
   apply simp
  apply (clarsimp simp: in_bind)
  apply (frule (3) corres_underlyingD2 [OF a])
   apply simp
  apply (clarsimp simp: in_alternative in_throwError)
  apply (erule disjE)
   prefer 2
   apply (clarsimp simp: lift_def in_throwError)
   apply (clarsimp simp: alternative_def throwError_def return_def)
  apply (simp add: lift_def split: sum.splits)
   apply (clarsimp simp: in_throwError)
   apply (rule_tac x="(Inl x',bb)" in bexI)
    apply simp
   apply (clarsimp simp: alternative_def bind_def)
   apply (rule bexI)
    prefer 2
    apply assumption
   apply (simp add: lift_def throwError_def return_def)
  apply clarsimp
  apply (drule b)
  apply (drule_tac s'=s'' in corres_underlyingD2, assumption)
      apply (drule use_valid, rule f[unfolded validE_def])
       apply assumption
      apply simp
     apply (drule use_valid, rule f'[unfolded validE_def])
      apply assumption
     apply simp
    apply assumption
   apply simp
  apply (clarsimp simp: in_alternative in_throwError)
  apply (erule disjE)
   apply (rule bexI, fastforce)
   apply (clarsimp simp: alternative_def)
   apply (simp add: bind_def)
   apply (rule bexI)
    prefer 2
    apply assumption
   apply (clarsimp simp: lift_def)
  apply clarsimp
  apply (frule use_valid, rule f'_eq, rule refl)
  apply clarsimp
  apply (drule use_valid, rule g'_eq[unfolded validE_def])
   apply (rule conjI, rule refl)
   apply (drule use_valid, rule f'[unfolded validE_def], assumption)
   apply simp
  apply (simp add: alternative_def throwError_def return_def)
  done

lemma corres_throw_skip_r:
  assumes c: "corres_underlying R False z (dc \<oplus> r) P P' (f \<sqinter> Monads_D.throw) g'"
  assumes eq: "\<And>s. \<lbrace>(=) s\<rbrace> f' \<lbrace>\<lambda>_. (=) s\<rbrace>"
  assumes nf: "z \<longrightarrow> no_fail P' f'"
  shows "corres_underlying R nf z (dc \<oplus> r) P P' (f \<sqinter> Monads_D.throw) (f' >>=E (\<lambda>_. g'))"
  using c
  apply (clarsimp simp: corres_underlying_def alternative_def bindE_def)
  apply (drule (1) bspec)
  apply (rule conjI)
   apply (clarsimp simp: in_bind)
   apply (frule use_valid, rule eq, rule refl)
   apply clarsimp
   apply (clarsimp simp: lift_def in_throwError split: sum.splits)
    apply (simp add: throwError_def return_def)
   apply (drule (1) bspec, clarsimp)
  apply clarsimp
  apply (clarsimp simp: bind_def)
  apply (erule disjE)
   prefer 2
   apply (insert nf)[1]
   apply (clarsimp simp: no_fail_def)
  apply (clarsimp simp: lift_def throwError_def return_def split: sum.splits)
  apply (frule use_valid, rule eq, rule refl)
  apply clarsimp
  done

lemma dcorres_rhs_noop_below:
  "\<lbrakk> dcorres anyrel Q Q' (return ()) m; dcorres anyrel P P' f g;
     \<lbrace> P \<rbrace> f \<lbrace> \<lambda>_. Q \<rbrace>; \<lbrace> P' \<rbrace> g \<lbrace> \<lambda>_. Q' \<rbrace> \<rbrakk>
   \<Longrightarrow> dcorres anyrel P P' (f :: unit k_monad) (g >>= (\<lambda>_. m))"
  apply (rule corres_add_noop_lhs2)
  apply (rule corres_split_forwards')
  apply (assumption | clarsimp)+
  done

lemma dcorres_rhs_noop_above: "\<lbrakk> dcorres anyrel P P' (return ()) m; dcorres anyrel' Q Q' f g;
              \<lbrace> P \<rbrace> return () \<lbrace> \<lambda>_. Q \<rbrace>; \<lbrace> P' \<rbrace> m \<lbrace> \<lambda>_. Q' \<rbrace> \<rbrakk>
            \<Longrightarrow> dcorres anyrel' P P' f (m >>= (\<lambda>_. g))"
  apply (rule corres_add_noop_lhs)
  apply (rule corres_split_forwards')
  apply (assumption | clarsimp)+
  done

lemmas dcorres_rhs_noop_below_True = dcorres_rhs_noop_below[OF _ _ hoare_TrueI hoare_TrueI]
\<comment> \<open>FIXME: remove\<close>
declare hoare_TrueI[simp]

end
