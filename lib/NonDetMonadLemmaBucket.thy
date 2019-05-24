(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory NonDetMonadLemmaBucket
imports
  "Monad_WP/NonDetMonadVCG"
  "MonadEq"
  "Monad_WP/WhileLoopRulesCompleteness"
  "Word_Lib.Distinct_Prop"
begin
setup \<open>AutoLevity_Base.add_attribute_test "wp" WeakestPre.is_wp_rule\<close>

lemma no_fail_assume_pre:
  "(\<And>s. P s \<Longrightarrow> no_fail P f) \<Longrightarrow> no_fail P f"
  by (simp add: no_fail_def)

lemma no_fail_liftM_eq [simp]:
  "no_fail P (liftM f m) = no_fail P m"
  by (auto simp: liftM_def no_fail_def bind_def return_def)

lemma mapME_Cons:
  "mapME m (x # xs) = (doE y \<leftarrow> m x; ys \<leftarrow> (mapME m xs); returnOk (y # ys) odE)"
  by (simp add: mapME_def sequenceE_def Let_def)


lemma mapME_Nil : "mapME f [] = returnOk []"
  unfolding mapME_def by (simp add: sequenceE_def)

lemma hoare_take_disjunct:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. P' rv s \<and> (False \<or> P'' rv s)\<rbrace>
    \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>P''\<rbrace>"
  by (erule hoare_strengthen_post, simp)

lemma hoare_post_add:
  "\<lbrace>P\<rbrace> S \<lbrace>\<lambda>r s. R r s \<and> Q r s\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> S \<lbrace>Q\<rbrace>"
  by (erule hoare_strengthen_post, simp)

lemma hoare_disjI1:
  "\<lbrace>R\<rbrace> f \<lbrace>P\<rbrace> \<Longrightarrow> \<lbrace>R\<rbrace> f \<lbrace>\<lambda>r s. P r s \<or> Q r s\<rbrace>"
  apply (erule hoare_post_imp [rotated])
  apply simp
  done

lemma hoare_disjI2:
  "\<lbrace>R\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>R\<rbrace> f \<lbrace>\<lambda>r s. P r s \<or> Q r s \<rbrace>"
  by (rule hoare_post_imp [OF _ hoare_disjI1, where P1=Q], auto)

lemma hoare_name_pre_state:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> \<lbrace>(=) s\<rbrace> f \<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  by (clarsimp simp: valid_def)

lemma hoare_name_pre_stateE:
  "\<lbrakk>\<And>s. P s \<Longrightarrow> \<lbrace>(=) s\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  by (clarsimp simp: validE_def2)

lemma valid_prove_more:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>"
  by (erule hoare_strengthen_post, simp)

lemma hoare_vcg_if_lift:
  "\<lbrace>R\<rbrace> f \<lbrace>\<lambda>rv s. (P \<longrightarrow> X rv s) \<and> (\<not>P \<longrightarrow> Y rv s)\<rbrace> \<Longrightarrow>
  \<lbrace>R\<rbrace> f \<lbrace>\<lambda>rv s. if P then X rv s else Y rv s\<rbrace>"

  "\<lbrace>R\<rbrace> f \<lbrace>\<lambda>rv s. (P \<longrightarrow> X rv s) \<and> (\<not>P \<longrightarrow> Y rv s)\<rbrace> \<Longrightarrow>
  \<lbrace>R\<rbrace> f \<lbrace>\<lambda>rv. if P then X rv else Y rv\<rbrace>"
  by (auto simp: valid_def split_def)

lemma hoare_lift_Pf2:
  assumes P: "\<And>x. \<lbrace>Q x\<rbrace> m \<lbrace>\<lambda>_. P x\<rbrace>"
  assumes f: "\<And>P. \<lbrace>\<lambda>s. P (f s)\<rbrace> m \<lbrace>\<lambda>_ s. P (f s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. Q (f s) s\<rbrace> m \<lbrace>\<lambda>_ s. P (f s) s\<rbrace>"
  apply (clarsimp simp add: valid_def)
  apply (frule (1) use_valid [OF _ P], drule (2) use_valid [OF _ f])
  done

lemma hoare_lift_Pf3:
  assumes P: "\<And>x. \<lbrace>Q x\<rbrace> m \<lbrace>P x\<rbrace>"
  assumes f: "\<And>P. \<lbrace>\<lambda>s. P (f s)\<rbrace> m \<lbrace>\<lambda>_ s. P (f s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. Q (f s) s\<rbrace> m \<lbrace>\<lambda>rv s. P (f s) rv s\<rbrace>"
  apply (clarsimp simp add: valid_def)
  apply (frule (1) use_valid [OF _ P], drule (2) use_valid [OF _ f])
  done

lemma no_fail_select_f [wp]:
  "no_fail (\<lambda>s. \<not>snd S) (select_f S)"
  by (simp add: select_f_def no_fail_def)

lemma hoare_lift_Pf:
  assumes P: "\<And>x. \<lbrace>P x\<rbrace> m \<lbrace>\<lambda>_. P x\<rbrace>"
  assumes f: "\<And>P. \<lbrace>\<lambda>s. P (f s)\<rbrace> m \<lbrace>\<lambda>_ s. P (f s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. P (f s) s\<rbrace> m \<lbrace>\<lambda>_ s. P (f s) s\<rbrace>"
  apply (clarsimp simp add: valid_def)
  apply (frule (1) use_valid [OF _ P], drule (2) use_valid [OF _ f])
  done

lemma assert_def2: "assert v = assert_opt (if v then Some () else None)"
  by (cases v, simp_all add: assert_def assert_opt_def)

lemma hoare_if_r_and:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>r. if R r then Q r else Q' r\<rbrace>
  = \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. (R r \<longrightarrow> Q r s) \<and> (\<not>R r \<longrightarrow> Q' r s)\<rbrace>"
  by (fastforce simp: valid_def)


lemma no_fail_liftM [wp]:
  "no_fail P m \<Longrightarrow> no_fail P (liftM f m)"
  by (simp)

lemma no_fail_pre_and:
  "no_fail P f \<Longrightarrow> no_fail (P and Q) f"
  by (erule no_fail_pre) simp

lemma hoare_convert_imp:
  "\<lbrakk> \<lbrace>\<lambda>s. \<not> P s\<rbrace> f \<lbrace>\<lambda>rv s. \<not> Q s\<rbrace>; \<lbrace>R\<rbrace> f \<lbrace>S\<rbrace> \<rbrakk> \<Longrightarrow>
    \<lbrace>\<lambda>s. P s \<longrightarrow> R s\<rbrace> f \<lbrace>\<lambda>rv s. Q s \<longrightarrow> S rv s\<rbrace>"
  apply (simp only: imp_conv_disj)
  apply (erule(1) hoare_vcg_disj_lift)
  done

lemma hoare_vcg_ex_lift_R:
  "\<lbrakk> \<And>v. \<lbrace>P v\<rbrace> f \<lbrace>Q v\<rbrace>,- \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. \<exists>v. P v s\<rbrace> f \<lbrace>\<lambda>rv s. \<exists>v. Q v rv s\<rbrace>,-"
  apply (simp add: validE_R_def validE_def)
  apply (rule hoare_strengthen_post, erule hoare_vcg_ex_lift)
  apply (auto split: sum.split)
  done

lemma hoare_case_option_wpR:
  "\<lbrakk>\<lbrace>P\<rbrace> f None \<lbrace>Q\<rbrace>,-; \<And>x. \<lbrace>P' x\<rbrace> f (Some x) \<lbrace>Q' x\<rbrace>,-\<rbrakk> \<Longrightarrow>
  \<lbrace>case_option P P' v\<rbrace> f v \<lbrace>\<lambda>rv. case v of None \<Rightarrow> Q rv | Some x \<Rightarrow> Q' x rv\<rbrace>,-"
  by (cases v) auto


lemma hoare_vcg_conj_liftE_R:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>P'\<rbrace>,-; \<lbrace>Q\<rbrace> f \<lbrace>Q'\<rbrace>,- \<rbrakk> \<Longrightarrow> \<lbrace>P and Q\<rbrace> f \<lbrace>\<lambda>rv s. P' rv s \<and> Q' rv s\<rbrace>, -"
  apply (simp add: validE_R_def validE_def valid_def split: sum.splits)
  apply blast
  done

lemma zipWithM_x_inv:
  assumes x: "\<And>x y. \<lbrace>P\<rbrace> m x y \<lbrace>\<lambda>rv. P\<rbrace>"
  shows      "length xs = length ys \<Longrightarrow> \<lbrace>P\<rbrace> zipWithM_x m xs ys \<lbrace>\<lambda>rv. P\<rbrace>"
proof (induct xs ys rule: list_induct2)
  case Nil
  show ?case
    by (simp add: zipWithM_x_def sequence_x_def zipWith_def)
next
  case (Cons a as b bs)
  have zipWithM_x_Cons:
    "\<And>m x xs y ys. zipWithM_x m (x # xs) (y # ys)
                 = do m x y; zipWithM_x m xs ys od"
    by (simp add: zipWithM_x_def sequence_x_def zipWith_def)
  have IH: "\<lbrace>P\<rbrace> zipWithM_x m as bs \<lbrace>\<lambda>rv. P\<rbrace>"
    by fact
  show ?case
    by (simp add: zipWithM_x_Cons) (wp IH x)
qed

lemma K_valid[wp]:
  "\<lbrace>K P\<rbrace> f \<lbrace>\<lambda>_. K P\<rbrace>"
  by (simp add: valid_def)

lemma mapME_wp:
  assumes x: "\<And>x. x \<in> S \<Longrightarrow> \<lbrace>P\<rbrace> f x \<lbrace>\<lambda>_. P\<rbrace>, \<lbrace>\<lambda>_. E\<rbrace>"
  shows      "set xs \<subseteq> S \<Longrightarrow> \<lbrace>P\<rbrace> mapME f xs \<lbrace>\<lambda>_. P\<rbrace>, \<lbrace>\<lambda>_. E\<rbrace>"
  apply (induct xs)
   apply (simp add: mapME_def sequenceE_def)
   apply wp
   apply simp
  apply (simp add: mapME_Cons)
  apply (wp x|simp)+
  done

lemmas mapME_wp' = mapME_wp [OF _ subset_refl]

lemma sequence_x_Cons: "\<And>x xs. sequence_x (x # xs) = (x >>= (\<lambda>_. sequence_x xs))"
  by (simp add: sequence_x_def)

lemma mapM_Cons: "mapM m (x # xs) = (do y \<leftarrow> m x; ys \<leftarrow> (mapM m xs); return (y # ys) od)"
  by (simp add: mapM_def sequence_def Let_def)

lemma mapM_simps:
  "mapM m [] = return []"
  "mapM m (x#xs) = do r \<leftarrow> m x; rs \<leftarrow> (mapM m xs); return (r#rs) od"
  by (simp_all add: mapM_def sequence_def)

lemma zipWithM_x_mapM:
 "zipWithM_x f as bs = (mapM (split f) (zip as bs) >>= (\<lambda>_. return ()))"
  apply (simp add: zipWithM_x_def zipWith_def)
  apply (induct ("zip as bs"))
   apply (simp add: sequence_x_def mapM_def sequence_def)
  apply (simp add: sequence_x_Cons mapM_Cons bind_assoc)
  done

(* zipWithM_x and mapM_ *)

lemma mapM_wp:
  assumes x: "\<And>x. x \<in> S \<Longrightarrow> \<lbrace>P\<rbrace> f x \<lbrace>\<lambda>rv. P\<rbrace>"
  shows      "set xs \<subseteq> S \<Longrightarrow> \<lbrace>P\<rbrace> mapM f xs \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (induct xs)
   apply (simp add: mapM_def sequence_def)
  apply (simp add: mapM_Cons)
  apply wp
   apply (rule x, clarsimp)
  apply simp
  done

lemma mapM_x_mapM:
  "mapM_x m l = (mapM m l >>= (\<lambda>x. return ()))"
  apply (simp add: mapM_x_def sequence_x_def mapM_def sequence_def)
  apply (induct l, simp_all add: Let_def bind_assoc)
  done

lemma mapM_x_wp:
  assumes x: "\<And>x. x \<in> S \<Longrightarrow> \<lbrace>P\<rbrace> f x \<lbrace>\<lambda>rv. P\<rbrace>"
  shows      "set xs \<subseteq> S \<Longrightarrow> \<lbrace>P\<rbrace> mapM_x f xs \<lbrace>\<lambda>rv. P\<rbrace>"
  by (subst mapM_x_mapM) (wp mapM_wp x)

lemma mapM_x_Nil:
  "mapM_x f [] = return ()"
  unfolding mapM_x_def sequence_x_def
  by simp

lemma sequence_xappend1:
  "sequence_x (xs @ [x]) = (sequence_x xs >>= (\<lambda>_. x))"
  by (induct xs) (simp add: sequence_x_def, simp add: sequence_x_Cons bind_assoc)

lemma mapM_append_single:
  "mapM_x f (xs @ [y]) = (mapM_x f xs >>= (\<lambda>_. f y))"
  unfolding mapM_x_def
  by (simp add: sequence_xappend1)

lemma mapM_x_Cons:
  "mapM_x m (x # xs) = (do m x; mapM_x m xs od)"
  by (simp add: mapM_x_def sequence_x_def)

lemma mapM_x_inv_wp2:
  assumes post: "\<And>s. \<lbrakk> I s; V [] s \<rbrakk> \<Longrightarrow> Q s"
  and     hr: "\<And>a as. suffix (a # as) xs \<Longrightarrow> \<lbrace>\<lambda>s. I s \<and> V (a # as) s\<rbrace> m a \<lbrace>\<lambda>r s. I s \<and> V as s\<rbrace>"
  shows   "\<lbrace>I and V xs\<rbrace> mapM_x m xs \<lbrace>\<lambda>rv. Q\<rbrace>"
proof (induct xs rule: list_induct_suffix)
  case Nil thus ?case
    apply (simp add: mapM_x_Nil)
    apply wp
    apply (clarsimp intro!: post)
    done
next
  case (Cons x xs)
  thus ?case
    apply (simp add: mapM_x_Cons)
    apply wp
     apply (wp hr)
    apply assumption
    done
qed

lemma zipWithM_x_mapM_x:
  "zipWithM_x f as bs = mapM_x (\<lambda>(x, y). f x y) (zip as bs)"
  apply (subst zipWithM_x_mapM)
  apply (subst mapM_x_mapM)
  apply (rule refl)
  done

lemma zipWithM_x_append1:
  fixes f :: "'b \<Rightarrow> 'c \<Rightarrow> ('a, unit) nondet_monad"
  assumes ls: "length xs = length ys"
  shows "(zipWithM_x f (xs @ [x]) (ys @ [y])) = (zipWithM_x f xs ys >>= (\<lambda>_. f x y))"
  unfolding zipWithM_x_def zipWith_def
  by (subst zip_append [OF ls], simp, rule sequence_xappend1)

lemma zipWithM_x_Cons:
  assumes ls: "length xs = length ys"
  shows "(zipWithM_x f (x # xs) (y # ys)) = (f x y >>=  (\<lambda>_. zipWithM_x f xs ys))"
  unfolding zipWithM_x_def zipWith_def
  by (simp, rule sequence_x_Cons)

lemma mapM_x_inv_wp3:
  fixes m :: "'b \<Rightarrow> ('a, unit) nondet_monad"
  assumes hr: "\<And>a as bs. xs = as @ [a] @ bs \<Longrightarrow>
     \<lbrace>\<lambda>s. I s \<and> V as s\<rbrace> m a \<lbrace>\<lambda>r s. I s \<and> V (as @ [a]) s\<rbrace>"
  shows   "\<lbrace>\<lambda>s. I s \<and> V [] s\<rbrace> mapM_x m xs \<lbrace>\<lambda>rv s. I s \<and> V xs s\<rbrace>"
  using hr
proof (induct xs rule: rev_induct)
  case Nil thus ?case
    apply (simp add: mapM_x_Nil)
    done
next
  case (snoc x xs)
  show ?case
    apply (simp add: mapM_append_single)
    apply (wp snoc.prems)
      apply simp
     apply (rule snoc.hyps [OF snoc.prems])
     apply simp
    apply assumption
    done
qed


lemma mapME_x_map_simp:
  "mapME_x m (map f xs) = mapME_x (m o f) xs"
  by (simp add: mapME_x_def sequenceE_x_def)

lemma mapM_return:
  "mapM (\<lambda>x. return (f x)) xs = return (map f xs)"
  apply (induct xs)
   apply (simp add: mapM_def sequence_def)
  apply (simp add: mapM_Cons)
  done

lemma mapME_x_inv_wp:
  assumes x: "\<And>x. \<lbrace>P\<rbrace> f x \<lbrace>\<lambda>rv. P\<rbrace>,\<lbrace>E\<rbrace>"
  shows      "\<lbrace>P\<rbrace> mapME_x f xs \<lbrace>\<lambda>rv. P\<rbrace>,\<lbrace>E\<rbrace>"
  apply (induct xs)
   apply (simp add: mapME_x_def sequenceE_x_def)
   apply wp
  apply (simp add: mapME_x_def sequenceE_x_def)
  apply (fold mapME_x_def sequenceE_x_def)
  apply wp
   apply (rule x)
  apply assumption
  done

lemma liftM_return [simp]:
  "liftM f (return x) = return (f x)"
  by (simp add: liftM_def)

lemma mapM_x_return :
  "mapM_x (\<lambda>_. return v) xs = return v"
  by (induct xs) (auto simp: mapM_x_Nil mapM_x_Cons)

lemma hoare_imp_eq_substR:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,- \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. rv = x \<longrightarrow> Q x s\<rbrace>,-"
  by (fastforce simp add: valid_def validE_R_def validE_def split: sum.splits)

lemma hoare_split_bind_case_sum:
  assumes x: "\<And>rv. \<lbrace>R rv\<rbrace> g rv \<lbrace>Q\<rbrace>"
             "\<And>rv. \<lbrace>S rv\<rbrace> h rv \<lbrace>Q\<rbrace>"
  assumes y: "\<lbrace>P\<rbrace> f \<lbrace>S\<rbrace>,\<lbrace>R\<rbrace>"
  shows      "\<lbrace>P\<rbrace> f >>= case_sum g h \<lbrace>Q\<rbrace>"
  apply (rule hoare_seq_ext [OF _ y[unfolded validE_def]])
  apply (case_tac x, simp_all add: x)
  done

lemma hoare_split_bind_case_sumE:
  assumes x: "\<And>rv. \<lbrace>R rv\<rbrace> g rv \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
             "\<And>rv. \<lbrace>S rv\<rbrace> h rv \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  assumes y: "\<lbrace>P\<rbrace> f \<lbrace>S\<rbrace>,\<lbrace>R\<rbrace>"
  shows      "\<lbrace>P\<rbrace> f >>= case_sum g h \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  apply (unfold validE_def)
  apply (rule hoare_seq_ext [OF _ y[unfolded validE_def]])
  apply (case_tac x, simp_all add: x [unfolded validE_def])
  done

lemma bind_comm_mapM_comm:
  assumes bind_comm:
    "\<And>n z. do x \<leftarrow> a; y \<leftarrow> b z; (n x y :: ('a, 's) nondet_monad) od =
            do y \<leftarrow> b z; x \<leftarrow> a; n x y od"
  shows "\<And>n'. do x \<leftarrow> a; ys \<leftarrow> mapM b zs; (n' x ys :: ('a, 's) nondet_monad) od =
         do ys \<leftarrow> mapM b zs; x \<leftarrow> a; n' x ys od"
proof (induct zs)
  case Nil
  thus ?case
    by (simp add: mapM_def sequence_def)
  next
  case (Cons z zs')
  thus ?case
    by (clarsimp simp: mapM_Cons bind_assoc bind_comm intro!: bind_cong [OF refl])
qed

lemma liftE_handle :
  "(liftE f <handle> g) = liftE f"
  by (simp add: handleE_def handleE'_def liftE_def)

lemma mapM_empty:
  "mapM f [] = return []"
  unfolding mapM_def
  by (simp add: sequence_def)

lemma mapM_append:
  "mapM f (xs @ ys) =
  (do x \<leftarrow> mapM f xs;
      y \<leftarrow> mapM f ys;
      return (x @ y)
   od)"
proof (induct xs)
  case Nil
  thus ?case by (simp add: mapM_empty)
next
  case (Cons x xs)

  show ?case
    by (simp add: mapM_Cons bind_assoc Cons.hyps)
qed

lemma mapM_x_append:
  "mapM_x f (xs @ ys) =
  (do x \<leftarrow> mapM_x f xs;
      y \<leftarrow> mapM_x f ys;
      return ()
   od)"
  by (simp add: mapM_x_mapM mapM_append bind_assoc)

lemma mapM_singleton:
  "mapM f [x] = (do r \<leftarrow> f x; return [r] od)"
  by (simp add: mapM_def sequence_def)

lemma mapM_x_singleton:
  "mapM_x f [x] = f x"
  by (simp add: mapM_x_mapM mapM_singleton)

lemma return_returnOk:
  "return (Inr x) = returnOk x"
  unfolding returnOk_def by simp

lemma mapME_x_sequenceE:
  "mapME_x f xs \<equiv> doE _ \<leftarrow> sequenceE (map f xs); returnOk () odE"
  apply (induct xs, simp_all add: mapME_x_def sequenceE_def sequenceE_x_def)
  apply (simp add: Let_def bindE_assoc)
  done

lemma sequenceE_Cons:
  "sequenceE (x # xs) = (doE v \<leftarrow> x; vs \<leftarrow> sequenceE xs; returnOk (v # vs) odE)"
  by (simp add: sequenceE_def Let_def)

lemma snd_return [monad_eq]:
  "\<not> snd (return a b)"
  unfolding return_def by simp

lemma snd_throwError [monad_eq]:
  "\<not> snd (throwError e s)"
  unfolding throwError_def by (simp add: snd_return)

lemma snd_lift_Inr  [monad_eq]:
  "snd (lift b (Inr r) t) = snd (b r t)"
  unfolding lift_def by simp

lemma snd_lift_Inl  [monad_eq]:
  "\<not> snd (lift b (Inl r) t)"
  unfolding lift_def by (simp add: snd_throwError)

lemma snd_fail [monad_eq]:
  "snd (fail s)"
  apply (clarsimp simp: fail_def)
  done

lemma not_snd_bindD:
  "\<lbrakk> \<not> snd ((a >>= b) s); (rv, s') \<in> fst (a s) \<rbrakk> \<Longrightarrow> \<not> snd (a s) \<and> \<not> snd (b rv s')"
  by (fastforce simp: bind_def)

lemma whenE_bindE_throwError_to_if:
  "whenE P (throwError e) >>=E (\<lambda>_. b) = (if P then (throwError e) else b)"
  unfolding whenE_def bindE_def
  by (auto simp: NonDetMonad.lift_def throwError_def returnOk_def)

lemma not_snd_bindI1:
  "\<not> snd ((a >>= b) s) \<Longrightarrow> \<not> snd (a s)"
  by (fastforce simp: bind_def)

lemma not_snd_bindI2:
  "\<lbrakk> \<not> snd ((a >>= b) s); (rv, s') \<in> fst (a s) \<rbrakk> \<Longrightarrow> \<not> snd (b rv s')"
  by (fastforce simp: bind_def)

lemma empty_fail_not_snd:
  "\<lbrakk> \<not> snd (m s); empty_fail m \<rbrakk> \<Longrightarrow> \<exists>v. v \<in> fst (m s)"
  by (fastforce simp: empty_fail_def)

lemma mapM_Nil:
  "mapM f [] = return []"
  by (simp add: mapM_def sequence_def)

lemma hoare_vcg_exI:
  "\<lbrace>P\<rbrace> f \<lbrace>Q x\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. \<exists>x. Q x rv s\<rbrace>"
  apply (simp add: valid_def split_def)
  apply blast
  done

lemma hoare_exI_tuple:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>(rv,rv') s. Q x rv rv' s\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>(rv,rv') s. \<exists>x. Q x rv rv' s\<rbrace>"
  by (fastforce simp: valid_def)

lemma hoare_ex_all:
  "(\<forall>x. \<lbrace>P x\<rbrace> f \<lbrace>Q\<rbrace>) = \<lbrace>\<lambda>s. \<exists>x. P x s\<rbrace> f \<lbrace>Q\<rbrace>"
  apply (rule iffI)
   apply (fastforce simp: valid_def)+
  done

lemma empty_fail_bindE:
  "\<lbrakk> empty_fail f; \<And>rv. empty_fail (g rv) \<rbrakk>
       \<Longrightarrow> empty_fail (f >>=E g)"
  apply (simp add: bindE_def)
  apply (erule empty_fail_bind)
  apply (simp add: lift_def throwError_def split: sum.split)
  done

lemma empty_fail_error_bits:
  "empty_fail (returnOk v)"
  "empty_fail (throwError v)"
  "empty_fail (liftE f) = empty_fail f"
  apply (simp_all add: returnOk_def throwError_def)
  apply (rule iffI, simp_all add: liftE_def)
  apply (simp add: empty_fail_def bind_def return_def)
  apply (erule allEI)
  apply clarsimp
  done


lemma mapM_upd:
  assumes "\<And>x rv s s'. (rv,s') \<in> fst (f x s) \<Longrightarrow> x \<in> set xs \<Longrightarrow> (rv, g s') \<in> fst (f x (g s))"
  shows "(rv,s') \<in> fst (mapM f xs s) \<Longrightarrow> (rv, g s') \<in> fst (mapM f xs (g s))"
  using assms
proof (induct xs arbitrary: rv s s')
  case Nil
  thus ?case by (simp add: mapM_Nil return_def)
next
  case (Cons z zs)
  from Cons.prems
  show ?case
    apply (clarsimp simp: mapM_Cons in_monad)
    apply (drule Cons.prems, simp)
    apply (rule exI, erule conjI)
    apply (erule Cons.hyps)
    apply (erule Cons.prems)
    apply simp
    done
qed

definition
  cutMon :: "('s \<Rightarrow> bool) \<Rightarrow> ('s, 'a) nondet_monad \<Rightarrow> ('s, 'a) nondet_monad" where
 "cutMon P f \<equiv> \<lambda>s. if P s then f s else fail s"

lemma cutMon_walk_bind:
  "(cutMon ((=) s) (f >>= g))
     = (cutMon ((=) s) f >>= (\<lambda>rv. cutMon (\<lambda>s'. (rv, s') \<in> fst (f s)) (g rv)))"
  apply (rule ext, simp add: cutMon_def bind_def fail_def)
  apply (auto simp: split_def)
  done

lemma cutMon_walk_bindE:
  "(cutMon ((=) s) (f >>=E g))
     = (cutMon ((=) s) f >>=E (\<lambda>rv. cutMon (\<lambda>s'. (Inr rv, s') \<in> fst (f s)) (g rv)))"
  apply (simp add: bindE_def cutMon_walk_bind)
  apply (rule bind_cong, rule refl)
  apply (simp add: cutMon_def lift_def fail_def
            split: if_split_asm)
  apply (clarsimp split: sum.split)
  done

lemma cutMon_walk_if:
  "cutMon ((=) s) (if P then f else g)
        = (if P then cutMon ((=) s) f else cutMon ((=) s) g)"
  by (simp add: cutMon_def)

lemma cutMon_valid_drop:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> cutMon R f \<lbrace>Q\<rbrace>"
  by (simp add: cutMon_def valid_def fail_def)

lemma cutMon_validE_drop:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> cutMon R f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (simp add: validE_def cutMon_valid_drop)

lemma assertE_assert:
  "assertE F = liftE (assert F)"
  by (clarsimp simp: assertE_def assert_def liftE_def returnOk_def
              split: if_split)

lemma snd_cutMon:
  "snd (cutMon P f s) = (P s \<longrightarrow> snd (f s))"
  by (simp add: cutMon_def fail_def split: if_split)

lemma exec_modify:
  "(modify f >>= g) s = g () (f s)"
  by (simp add: bind_def simpler_modify_def)

lemma no_fail_spec:
  "\<lbrakk> \<And>s. no_fail (((=) s) and P) f \<rbrakk> \<Longrightarrow> no_fail P f"
  by (simp add: no_fail_def)

lemma no_fail_assertE [wp]:
  "no_fail (\<lambda>_. P) (assertE P)"
  by (simp add: assertE_def split: if_split)

lemma no_fail_spec_pre:
  "\<lbrakk> no_fail (((=) s) and P') f; \<And>s. P s \<Longrightarrow> P' s \<rbrakk> \<Longrightarrow> no_fail (((=) s) and P) f"
  by (erule no_fail_pre, simp)

lemma no_fail_whenE [wp]:
  "\<lbrakk> G \<Longrightarrow> no_fail P f \<rbrakk> \<Longrightarrow> no_fail (\<lambda>s. G \<longrightarrow> P s) (whenE G f)"
  by (simp add: whenE_def split: if_split)

lemma no_fail_unlessE [wp]:
  "\<lbrakk> \<not> G \<Longrightarrow> no_fail P f \<rbrakk> \<Longrightarrow> no_fail (\<lambda>s. \<not> G \<longrightarrow> P s) (unlessE G f)"
  by (simp add: unlessE_def split: if_split)

lemma no_fail_throwError [wp]:
  "no_fail \<top> (throwError e)"
  by (simp add: throwError_def)

lemma no_fail_liftE [wp]:
  "no_fail P f \<Longrightarrow> no_fail P (liftE f)"
  unfolding liftE_def by wpsimp

lemma bind_return_eq:
  "(a >>= return) = (b >>= return) \<Longrightarrow> a = b"
  apply (clarsimp simp:bind_def)
  apply (rule ext)
  apply (drule_tac x= x in fun_cong)
  apply (auto simp:return_def split_def)
  done

lemma bindE_bind_linearise:
  "((f >>=E g) >>= h) =
   (f >>= case_sum (h o Inl) (\<lambda>rv. g rv >>= h))"
  apply (simp add: bindE_def bind_assoc)
  apply (rule ext, rule bind_apply_cong, rule refl)
  apply (simp add: lift_def throwError_def split: sum.split)
  done

lemma throwError_bind:
  "(throwError e >>= f) = (f (Inl e))"
  by (simp add: throwError_def)

lemma bind_bindE_assoc:
  "((f >>= g) >>=E h)
    = f >>= (\<lambda>rv. g rv >>=E h)"
  by (simp add: bindE_def bind_assoc)

lemma returnOk_bind:
  "returnOk v >>= f = (f (Inr v))"
  by (simp add: returnOk_def)

lemma liftE_bind:
  "(liftE m >>= m') = (m >>= (\<lambda>rv. m' (Inr rv)))"
  by (simp add: liftE_def)

lemma catch_throwError: "catch (throwError ft) g = g ft"
  by (simp add: catch_def throwError_bind)

lemma select_bind_eq2:
  "\<lbrakk> v = v'; \<And>x. x \<in> fst v \<Longrightarrow> f x s = g x s' \<rbrakk> \<Longrightarrow>
    (select_f v >>= f) s = (select_f v' >>= g) s'"
  by (simp add: select_f_def bind_def split_def
                cart_singleton_image image_image
          cong: image_cong)

lemmas select_bind_eq = select_bind_eq2[OF refl]

lemma select_f_singleton_return:
  "select_f ({v}, False) = return v"
  by (simp add: select_f_def return_def)

lemma select_f_returns:
  "select_f (return v s) = return (v, s)"
  "select_f (get s) = return (s, s)"
  "select_f (gets f s) = return (f s, s)"
  "select_f (modify g s) = return ((), g s)"
  by (simp add: select_f_def return_def get_def
                simpler_gets_def simpler_modify_def)+

lemma select_eq_select_f:
  "select S = select_f (S, False)"
  by (simp add: select_def select_f_def)

lemma select_f_select_f:
  "select_f (select_f v s) = liftM (swp Pair s) (select_f v)"
  apply (rule ext)
  apply (simp add: select_f_def liftM_def swp_def
                   bind_def return_def split_def
                   image_image image_constant_conv)
  apply fastforce
  done

lemma select_f_select:
  "select_f (select S s) = liftM (swp Pair s) (select S)"
  unfolding select_eq_select_f by (rule select_f_select_f)

lemmas select_f_selects = select_f_select_f select_f_select

lemma select_f_asserts:
  "select_f (fail s) = fail"
  "select_f (assert P s) = do assert P; return ((), s) od"
  "select_f (assert_opt v s) = do v' \<leftarrow> assert_opt v; return (v', s) od"
  by (simp add: select_f_def fail_def assert_def return_def bind_def
                assert_opt_def split: if_split option.split)+

lemma liftE_bindE_handle:
  "((liftE f >>=E (\<lambda>x. g x)) <handle> h)
      = f >>= (\<lambda>x. g x <handle> h)"
  by (simp add: liftE_bindE handleE_def handleE'_def
                bind_assoc)

lemma in_returns [monad_eq]:
  "(r, s) \<in> fst (return r s)"
  "(Inr r, s) \<in> fst (returnOk r s)"
  by (simp add: in_monad)+

lemma assertE_sp:
  "\<lbrace>P\<rbrace> assertE Q \<lbrace>\<lambda>rv s. Q \<and> P s\<rbrace>,\<lbrace>E\<rbrace>"
  by (clarsimp simp: assertE_def) wp

lemma catch_liftE:
  "catch (liftE g) h = g"
  by (simp add: catch_def liftE_def)

lemma catch_liftE_bindE:
  "catch (liftE g >>=E (\<lambda>x. f x)) h = g >>= (\<lambda>x. catch (f x) h)"
  by (simp add: liftE_bindE catch_def bind_assoc)

lemma returnOk_catch_bind:
  "catch (returnOk v) h >>= g = g v"
  by (simp add: returnOk_liftE catch_liftE)

lemma alternative_left_readonly_bind:
  "\<lbrakk> \<lbrace>(=) s\<rbrace> f \<lbrace>\<lambda>rv. (=) s\<rbrace>; fst (f s) \<noteq> {} \<rbrakk> \<Longrightarrow>
     alternative (f >>= (\<lambda>x. g x)) h s
       = (f >>= (\<lambda>x. alternative (g x) h)) s"
  apply (subgoal_tac "\<forall>x \<in> fst (f s). snd x = s")
   apply (clarsimp simp: alternative_def bind_def split_def)
   apply fastforce
  apply clarsimp
  apply (drule(1) use_valid, simp_all)
  done

lemma liftE_bindE_assoc:
  "(liftE f >>=E g) >>= h = f >>= (\<lambda>x. g x >>= h)"
  by (simp add: liftE_bindE bind_assoc)

lemma empty_fail_use_cutMon:
  "\<lbrakk> \<And>s. empty_fail (cutMon ((=) s) f) \<rbrakk> \<Longrightarrow> empty_fail f"
  apply (clarsimp simp add: empty_fail_def cutMon_def)
  apply (fastforce split: if_split_asm)
  done

lemma empty_fail_drop_cutMon:
  "empty_fail f \<Longrightarrow> empty_fail (cutMon P f)"
  by (simp add: empty_fail_def fail_def cutMon_def split: if_split)

lemma empty_fail_cutMon:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> empty_fail (cutMon ((=) s) f) \<rbrakk>
    \<Longrightarrow> empty_fail (cutMon P f)"
  apply (clarsimp simp: empty_fail_def cutMon_def fail_def
                 split: if_split)
  apply (fastforce split: if_split_asm)
  done

lemma empty_fail_If:
  "\<lbrakk> P \<Longrightarrow> empty_fail f; \<not> P \<Longrightarrow> empty_fail g \<rbrakk> \<Longrightarrow> empty_fail (if P then f else g)"
  by (simp split: if_split)

lemmas empty_fail_cutMon_intros =
     cutMon_walk_bind[THEN arg_cong[where f=empty_fail], THEN iffD2,
                      OF empty_fail_bind, OF _ empty_fail_cutMon]
     cutMon_walk_bindE[THEN arg_cong[where f=empty_fail], THEN iffD2,
                       OF empty_fail_bindE, OF _ empty_fail_cutMon]
     cutMon_walk_if[THEN arg_cong[where f=empty_fail], THEN iffD2,
                    OF empty_fail_If]

lemma empty_fail_whenEs:
  "empty_fail f \<Longrightarrow> empty_fail (whenE P f)"
  "empty_fail f \<Longrightarrow> empty_fail (unlessE P f)"
  by (auto simp add: whenE_def unlessE_def empty_fail_error_bits split: if_split)

lemma empty_fail_assertE:
  "empty_fail (assertE P)"
  by (simp add: assertE_def empty_fail_error_bits split: if_split)

lemma unlessE_throw_catch_If:
  "catch (unlessE P (throwError e) >>=E f) g
      = (if P then catch (f ()) g else g e)"
  by (simp add: unlessE_def catch_throwError split: if_split)

lemma gets_the_return:
  "(return x = gets_the f) = (\<forall>s. f s = Some x)"
  apply (subst fun_eq_iff)
  apply (simp add: return_def gets_the_def exec_gets
                   assert_opt_def fail_def
            split: option.split)
  apply auto
  done

lemma gets_the_returns[unfolded K_def]:
  "(return x = gets_the f) = (\<forall>s. f s = Some x)"
  "(returnOk x = gets_the g) = (\<forall>s. g s = Some (Inr x))"
  "(throwError x = gets_the h) = (\<forall>s. h s = Some (Inl x))"
  by (simp_all add: returnOk_def throwError_def
                    gets_the_return)

lemma all_rv_choice_fn_eq:
  "\<lbrakk> \<And>rv. \<exists>fn. f rv = g fn \<rbrakk>
    \<Longrightarrow> \<exists>fn. f = (\<lambda>rv. g (fn rv))"
  using all_rv_choice_fn_eq_pred[where f=f and g=g and P=\<top>]
  by (simp add: fun_eq_iff)

lemma cutMon_assert_opt:
  "cutMon P (gets_the f >>= g)
      = gets_the (\<lambda>s. if P s then f s else None) >>= g"
  by (simp add: cutMon_def gets_the_def exec_gets
                bind_assoc fun_eq_iff assert_opt_def
         split: if_split)

lemma gets_the_eq_bind:
  "\<lbrakk> \<exists>fn. f = gets_the (fn o fn');
         \<And>rv. \<exists>fn. g rv
                  = gets_the (fn o fn') \<rbrakk>
     \<Longrightarrow> \<exists>fn. (f >>= g) = gets_the (fn o fn')"
  apply (clarsimp dest!: all_rv_choice_fn_eq)
  apply (rule_tac x="\<lambda>s. case (fn s) of None \<Rightarrow> None | Some v \<Rightarrow> fna v s" in exI)
  apply (simp add: gets_the_def bind_assoc exec_gets
                   assert_opt_def fun_eq_iff
            split: option.split)
  done

lemma gets_the_eq_bindE:
  "\<lbrakk> \<exists>fn. f = gets_the (fn o fn');
         \<And>rv. \<exists>fn. g rv = gets_the (fn o fn') \<rbrakk>
     \<Longrightarrow> \<exists>fn. (f >>=E g) = gets_the (fn o fn')"
  apply (simp add: bindE_def)
  apply (erule gets_the_eq_bind)
  apply (simp add: lift_def gets_the_returns split: sum.split)
  apply fastforce
  done

lemma gets_the_fail:
  "(fail = gets_the f) = (\<forall>s. f s = None)"
  by (simp add: gets_the_def exec_gets assert_opt_def
                fail_def return_def fun_eq_iff
         split: option.split)

lemma gets_the_asserts:
  "(fail = gets_the f) = (\<forall>s. f s = None)"
  "(assert P = gets_the g) = (\<forall>s. g s = (if P then Some () else None))"
  "(assertE P = gets_the h) = (\<forall>s. h s = (if P then Some (Inr ()) else None))"
  by (simp add: assert_def assertE_def
                gets_the_fail gets_the_returns
         split: if_split)+

lemma gets_the_condsE:
  "(\<exists>fn. whenE P f = gets_the (fn o fn'))
            = (P \<longrightarrow> (\<exists>fn. f = gets_the (fn o fn')))"
  "(\<exists>fn. unlessE P g = gets_the (fn o fn'))
            = (\<not> P \<longrightarrow> (\<exists>fn. g = gets_the (fn o fn')))"
  by (simp add: whenE_def unlessE_def gets_the_returns
                ex_const_function
         split: if_split)+

lemma no_fail_gets_the [wp]:
  "no_fail (\<lambda>s. f s \<noteq> None) (gets_the f)"
  apply (simp add: gets_the_def)
  apply (rule no_fail_pre, wp)
  apply simp
  done

lemma gets_the_validE_R_wp:
  "\<lbrace>\<lambda>s. f s \<noteq> None \<and> isRight (the (f s)) \<and> Q (theRight (the (f s))) s\<rbrace>
     gets_the f
   \<lbrace>Q\<rbrace>,-"
  apply (simp add: gets_the_def validE_R_def validE_def)
  apply (wp | wpc | simp add: assert_opt_def)+
  apply (clarsimp split: split: sum.splits)
  done

lemma return_bindE:
  "isRight v \<Longrightarrow> return v >>=E f = f (theRight v)"
  by (clarsimp simp: isRight_def return_returnOk)

lemma assert_opt_If:
  "assert_opt v = If (v = None) fail (return (the v))"
  by (simp_all add: assert_opt_def split: option.split)

lemma if_to_top_of_bind:
  "(bind (If P x y) z) = If P (bind x z) (bind y z)"
  by (simp split: if_split)

lemma if_to_top_of_bindE:
  "(bindE (If P x y) z) = If P (bindE x z) (bindE y z)"
  by (simp split: if_split)

lemma alternative_bind:
  "((a \<sqinter> b) >>= c) = ((a >>= c) \<sqinter> (b >>= c))"
  apply (rule ext, simp add: alternative_def bind_def split_def)
  apply blast
  done

lemma alternative_refl:
  "(a \<sqinter> a) = a"
  by (rule ext, simp add: alternative_def)

lemma alternative_com:
  "(f \<sqinter> g) = (g \<sqinter> f)"
  apply (rule ext)
  apply (auto simp: alternative_def)
  done

lemma liftE_alternative:
  "liftE (a \<sqinter> b) = (liftE a \<sqinter> liftE b)"
  by (simp add: liftE_def alternative_bind)

lemma fst_return:
  "fst (return v s) = {(v, s)}"
  by (simp add: return_def)

(* FIXME: move *)
lemma in_bind_split [monad_eq]:
  "(rv \<in> fst ((f >>= g) s)) =
  (\<exists>rv'. rv' \<in> fst (f s) \<and> rv \<in> fst (g (fst rv') (snd rv')))"
  apply (cases rv)
  apply (fastforce simp add: in_bind)
  done

lemma no_fail_mapM_wp:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> no_fail (P x) (f x)"
  assumes "\<And>x y. \<lbrakk> x \<in> set xs; y \<in> set xs \<rbrakk> \<Longrightarrow> \<lbrace>P x\<rbrace> f y \<lbrace>\<lambda>_. P x\<rbrace>"
  shows "no_fail (\<lambda>s. \<forall>x \<in> set xs. P x s) (mapM f xs)"
  using assms
proof (induct xs)
  case Nil
  thus ?case by (simp add: mapM_empty)
next
  case (Cons z zs)
  show ?case
    apply (clarsimp simp: mapM_Cons)
    apply (wp Cons.prems Cons.hyps hoare_vcg_const_Ball_lift|simp)+
    done
qed

lemma zipWithM_Nil [simp]:
  "zipWithM f xs [] = return []"
  by (simp add: zipWithM_def zipWith_def sequence_def)

lemma zipWithM_One:
  "zipWithM f (x#xs) [a] = (do z \<leftarrow> f x a; return [z] od)"
  by (simp add: zipWithM_def zipWith_def sequence_def)

lemma zipWithM_x_Nil:
  "zipWithM_x f xs [] = return ()"
  by (simp add: zipWithM_x_def zipWith_def sequence_x_def)

lemma zipWithM_x_One:
  "zipWithM_x f (x#xs) [a] = f x a"
  by (simp add: zipWithM_x_def zipWith_def sequence_x_def)

lemma list_case_return:
  "(case xs of [] \<Rightarrow> return v | y # ys \<Rightarrow> return (f y ys))
    = return (case xs of [] \<Rightarrow> v | y # ys \<Rightarrow> f y ys)"
  by (simp split: list.split)

lemma gets_exs_valid:
  "\<lbrace>(=) s\<rbrace> gets f \<exists>\<lbrace>\<lambda>r. (=) s\<rbrace>"
  apply (clarsimp simp: exs_valid_def split_def)
  apply (rule bexI [where x = "(f s, s)"])
   apply simp
  apply (simp add: in_monad)
  done

lemma empty_fail_get:
  "empty_fail get"
  by (simp add: empty_fail_def get_def)

lemma alternative_liftE_returnOk:
  "(liftE m \<sqinter> returnOk v) = liftE (m \<sqinter> return v)"
  by (simp add: liftE_def alternative_def returnOk_def bind_def return_def)

lemma bind_inv_inv_comm_weak:
  "\<lbrakk> \<And>s. \<lbrace>(=) s\<rbrace> f \<lbrace>\<lambda>_. (=) s\<rbrace>; \<And>s. \<lbrace>(=) s\<rbrace> g \<lbrace>\<lambda>_. (=) s\<rbrace>;
     empty_fail f; empty_fail g \<rbrakk> \<Longrightarrow>
   do x \<leftarrow> f; y \<leftarrow> g; n od = do y \<leftarrow> g; x \<leftarrow> f; n od"
  apply (rule ext)
  apply (fastforce simp: bind_def valid_def empty_fail_def split_def image_def)
  done

lemma mapM_last_Cons:
  "\<lbrakk> xs = [] \<Longrightarrow> g v = y;
     xs \<noteq> [] \<Longrightarrow> do x \<leftarrow> f (last xs); return (g x) od
             = do x \<leftarrow> f (last xs); return y od \<rbrakk> \<Longrightarrow>
   do ys \<leftarrow> mapM f xs;
      return (g (last (v # ys))) od
   = do mapM_x f xs;
      return y od"
  apply (cases "xs = []")
   apply (simp add: mapM_x_Nil mapM_Nil)
  apply (simp add: mapM_x_mapM)
  apply (subst append_butlast_last_id[symmetric], assumption,
         subst mapM_append)+
  apply (simp add: bind_assoc mapM_Cons mapM_Nil)
  done

lemma mapM_length_cong:
  "\<lbrakk> length xs = length ys; \<And>x y. (x, y) \<in> set (zip xs ys) \<Longrightarrow> f x = g y \<rbrakk>
      \<Longrightarrow> mapM f xs = mapM g ys"
  by (simp add: mapM_def map_length_cong)

(* FIXME: duplicate *)
lemma zipWithM_mapM:
  "zipWithM f xs ys = mapM (split f) (zip xs ys)"
  by (simp add: zipWithM_def zipWith_def mapM_def)

lemma zipWithM_If_cut:
  "zipWithM (\<lambda>a b. if a < n then f a b else g a b) [0 ..< m] xs
     = do ys \<leftarrow> zipWithM f [0 ..< min n m] xs;
          zs \<leftarrow> zipWithM g [n ..< m] (drop n xs);
          return (ys @ zs) od"
  apply (cases "n < m")
   apply (cut_tac i=0 and j=n and k="m - n" in upt_add_eq_append)
    apply simp
   apply (simp add: min.absorb1 zipWithM_mapM)
   apply (simp add: zip_append1 mapM_append zip_take_triv2 split_def)
   apply (intro bind_cong bind_apply_cong refl mapM_length_cong
                fun_cong[OF mapM_length_cong])
    apply (clarsimp simp: set_zip)
   apply (clarsimp simp: set_zip)
  apply (simp add: min.absorb2 zipWithM_mapM mapM_Nil)
  apply (intro mapM_length_cong refl)
  apply (clarsimp simp: set_zip)
  done

lemma mapM_liftM_const:
  "mapM (\<lambda>x. liftM (\<lambda>y. f x) (g x)) xs
     = liftM (\<lambda>ys. map f xs) (mapM g xs)"
  apply (induct xs)
   apply (simp add: mapM_Nil)
  apply (simp add: mapM_Cons)
  apply (simp add: liftM_def bind_assoc)
  done

lemma empty_failD2:
  "\<lbrakk> empty_fail f; \<not> snd (f s) \<rbrakk> \<Longrightarrow> \<exists>v. v \<in> fst (f s)"
  by (fastforce simp add: empty_fail_def)

lemma empty_failD3:
  "\<lbrakk> empty_fail f; \<not> snd (f s) \<rbrakk> \<Longrightarrow> fst (f s) \<noteq> {}"
  by (drule(1) empty_failD2, clarsimp)

lemma bind_inv_inv_comm:
  "\<lbrakk> \<And>P. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. P\<rbrace>; \<And>P. \<lbrace>P\<rbrace> g \<lbrace>\<lambda>_. P\<rbrace>;
     empty_fail f; empty_fail g \<rbrakk> \<Longrightarrow>
   do x \<leftarrow> f; y \<leftarrow> g; n x y od = do y \<leftarrow> g; x \<leftarrow> f; n x y od"
  apply (rule ext)
  apply (rename_tac s)
  apply (rule_tac s="(do (x, y) \<leftarrow> do x \<leftarrow> f; y \<leftarrow> (\<lambda>_. g s) ; (\<lambda>_. return (x, y) s) od;
                         n x y od) s" in trans)
   apply (simp add: bind_assoc)
   apply (intro bind_apply_cong, simp_all)[1]
    apply (metis in_inv_by_hoareD)
   apply (simp add: return_def bind_def)
   apply (metis in_inv_by_hoareD)
  apply (rule_tac s="(do (x, y) \<leftarrow> do y \<leftarrow> g; x \<leftarrow> (\<lambda>_. f s) ; (\<lambda>_. return (x, y) s) od;
                      n x y od) s" in trans[rotated])
   apply (simp add: bind_assoc)
   apply (intro bind_apply_cong, simp_all)[1]
    apply (metis in_inv_by_hoareD)
   apply (simp add: return_def bind_def)
   apply (metis in_inv_by_hoareD)
  apply (rule bind_apply_cong, simp_all)
  apply (clarsimp simp: bind_def split_def return_def)
  apply (auto | drule(1) empty_failD3)+
  done

lemma throwErrorE_E [wp]:
  "\<lbrace>Q e\<rbrace> throwError e -, \<lbrace>Q\<rbrace>"
  by (simp add: validE_E_def) wp

lemma no_fail_mapM:
  "\<forall>x. no_fail \<top> (f x) \<Longrightarrow> no_fail \<top> (mapM f xs)"
  apply (induct xs)
   apply (simp add: mapM_def sequence_def)
  apply (simp add: mapM_Cons)
  apply (wp|fastforce)+
  done

lemma gets_inv [simp]:
  "\<lbrace> P \<rbrace> gets f \<lbrace> \<lambda>r. P \<rbrace>"
  by (simp add: gets_def, wp)

lemma select_inv:
  "\<lbrace> P \<rbrace> select S \<lbrace> \<lambda>r. P \<rbrace>"
  by (simp add: select_def valid_def)

lemmas return_inv = hoare_return_drop_var

lemma assert_inv: "\<lbrace>P\<rbrace> assert Q \<lbrace>\<lambda>r. P\<rbrace>"
  unfolding assert_def
  by (cases Q) simp+

lemma assert_opt_inv: "\<lbrace>P\<rbrace> assert_opt Q \<lbrace>\<lambda>r. P\<rbrace>"
  unfolding assert_opt_def
  by (cases Q) simp+

lemma let_into_return:
  "(let f = x in m f) = (do f \<leftarrow> return x; m f od)"
  by simp

definition
  injection_handler :: "('a \<Rightarrow> 'b) \<Rightarrow> ('s, 'a + 'c) nondet_monad
                                  \<Rightarrow> ('s, 'b + 'c) nondet_monad"
where
 "injection_handler f m \<equiv> m <handle2> (\<lambda>ft. throwError (f ft))"

lemma injection_wp:
  "\<lbrakk> t = injection_handler f; \<lbrace>P\<rbrace> m \<lbrace>Q\<rbrace>,\<lbrace>\<lambda>ft. E (f ft)\<rbrace> \<rbrakk>
    \<Longrightarrow> \<lbrace>P\<rbrace> t m \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  apply (simp add: injection_handler_def)
  apply (wp|simp)+
  done

lemma injection_wp_E:
  "\<lbrakk> t = injection_handler f; \<lbrace>P\<rbrace> m \<lbrace>Q\<rbrace>,- \<rbrakk>
    \<Longrightarrow> \<lbrace>P\<rbrace> t m \<lbrace>Q\<rbrace>,-"
  by (simp add: validE_R_def injection_wp)

lemma injection_bindE:
  "\<lbrakk> t = injection_handler f; t2 = injection_handler f \<rbrakk>
    \<Longrightarrow> t (x >>=E y) = (t2 x) >>=E (\<lambda>rv. t (y rv))"
  apply (simp add: injection_handler_def)
  apply (simp add: bindE_def handleE'_def bind_assoc)
  apply (rule arg_cong [where f="\<lambda>y. x >>= y"])
  apply (rule ext)
  apply (case_tac x, simp_all add: lift_def throwError_def)
  done

lemma injection_liftE:
  "t = injection_handler f \<Longrightarrow> t (liftE x) = liftE x"
  apply (simp add: injection_handler_def handleE'_def liftE_def)
  done

lemma id_injection:
  "id = injection_handler id"
proof -
  have P: "case_sum throwError (\<lambda>v. return (Inr v)) = return"
    by (auto simp: throwError_def split: sum.splits)
  show ?thesis
    by (auto simp: injection_handler_def handleE'_def P)
qed


lemma case_options_weak_wp:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>; \<And>x. \<lbrace>P'\<rbrace> g x \<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P and P'\<rbrace> case opt of None \<Rightarrow> f | Some x \<Rightarrow> g x \<lbrace>Q\<rbrace>"
  apply (cases opt)
   apply (clarsimp elim!: hoare_weaken_pre)
  apply (rule hoare_weaken_pre [where Q=P'])
   apply simp+
  done

lemma list_cases_weak_wp:
  assumes "\<lbrace>P_A\<rbrace> a \<lbrace>Q\<rbrace>"
  assumes "\<And>x xs. \<lbrace>P_B\<rbrace> b x xs \<lbrace>Q\<rbrace>"
  shows
  "\<lbrace>P_A and P_B\<rbrace>
    case ts of
      [] \<Rightarrow> a
    | x#xs \<Rightarrow> b x xs \<lbrace>Q\<rbrace>"
  apply (cases ts)
  apply (simp, rule hoare_weaken_pre, rule assms, simp)+
  done


lemmas hoare_FalseE_R = hoare_FalseE[where E="\<top>\<top>", folded validE_R_def]

lemma hoare_vcg_if_lift2:
  "\<lbrace>R\<rbrace> f \<lbrace>\<lambda>rv s. (P rv s \<longrightarrow> X rv s) \<and> (\<not> P rv s \<longrightarrow> Y rv s)\<rbrace> \<Longrightarrow>
  \<lbrace>R\<rbrace> f \<lbrace>\<lambda>rv s. if P rv s then X rv s else Y rv s\<rbrace>"

  "\<lbrace>R\<rbrace> f \<lbrace>\<lambda>rv s. (P' rv \<longrightarrow> X rv s) \<and> (\<not> P' rv \<longrightarrow> Y rv s)\<rbrace> \<Longrightarrow>
  \<lbrace>R\<rbrace> f \<lbrace>\<lambda>rv. if P' rv then X rv else Y rv\<rbrace>"
  by (auto simp: valid_def split_def)

lemma hoare_vcg_if_lift_ER: (* Required because of lack of rv in lifting rules *)
  "\<lbrace>R\<rbrace> f \<lbrace>\<lambda>rv s. (P rv s \<longrightarrow> X rv s) \<and> (\<not> P rv s \<longrightarrow> Y rv s)\<rbrace>, - \<Longrightarrow>
  \<lbrace>R\<rbrace> f \<lbrace>\<lambda>rv s. if P rv s then X rv s else Y rv s\<rbrace>, -"

  "\<lbrace>R\<rbrace> f \<lbrace>\<lambda>rv s. (P' rv \<longrightarrow> X rv s) \<and> (\<not> P' rv \<longrightarrow> Y rv s)\<rbrace>, - \<Longrightarrow>
  \<lbrace>R\<rbrace> f \<lbrace>\<lambda>rv. if P' rv then X rv else Y rv\<rbrace>, -"
  by (auto simp: valid_def validE_R_def validE_def split_def)

lemma liftME_return:
  "liftME f (returnOk v) = returnOk (f v)"
  by (simp add: liftME_def)

lemma lifted_if_collapse:
  "(if P then \<top> else f) = (\<lambda>s. \<not>P \<longrightarrow> f s)"
  by auto

lemma undefined_valid: "\<lbrace>\<bottom>\<rbrace> undefined \<lbrace>Q\<rbrace>"
  by (rule hoare_pre_cont)

lemma Inr_in_liftE_simp [monad_eq]:
  "((Inr rv, x) \<in> fst (liftE fn s)) = ((rv, x) \<in> fst (fn s))"
  by (simp add: in_monad)

lemma assertE_wp:
  "\<lbrace>\<lambda>s. F \<longrightarrow> Q () s\<rbrace> assertE F \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  apply (rule hoare_pre)
   apply (unfold assertE_def)
   apply wp
  apply simp
  done

lemma doesn't_grow_proof:
  assumes y: "\<And>s. finite (S s)"
  assumes x: "\<And>x. \<lbrace>\<lambda>s. x \<notin> S s \<and> P s\<rbrace> f \<lbrace>\<lambda>rv s. x \<notin> S s\<rbrace>"
  shows      "\<lbrace>\<lambda>s. card (S s) < n \<and> P s\<rbrace> f \<lbrace>\<lambda>rv s. card (S s) < n\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (subgoal_tac "S b \<subseteq> S s")
   apply (drule card_mono [OF y], simp)
  apply clarsimp
  apply (rule ccontr)
  apply (subgoal_tac "x \<notin> S b", simp)
  apply (erule use_valid [OF _ x])
  apply simp
  done

lemma fold_bindE_into_list_case:
  "(doE v \<leftarrow> f; case_list (g v) (h v) x odE)
      = (case_list (doE v \<leftarrow> f; g v odE) (\<lambda>x xs. doE v \<leftarrow> f; h v x xs odE) x)"
  by (simp split: list.split)

lemma hoare_vcg_propE_R:
  "\<lbrace>\<lambda>s. P\<rbrace> f \<lbrace>\<lambda>rv s. P\<rbrace>, -"
  by (simp add: validE_R_def validE_def valid_def split_def split: sum.split)

lemma set_preserved_proof:
  assumes y: "\<And>x. \<lbrace>\<lambda>s. Q s \<and> x \<in> S s\<rbrace> f \<lbrace>\<lambda>rv s. x \<in> S s\<rbrace>"
  assumes x: "\<And>x. \<lbrace>\<lambda>s. Q s \<and> x \<notin> S s\<rbrace> f \<lbrace>\<lambda>rv s. x \<notin> S s\<rbrace>"
  shows      "\<lbrace>\<lambda>s. Q s \<and> P (S s)\<rbrace> f \<lbrace>\<lambda>rv s. P (S s)\<rbrace>"
  apply (clarsimp simp: valid_def)
  by (metis (mono_tags, lifting) equalityI post_by_hoare subsetI x y)

lemma set_shrink_proof:
  assumes x: "\<And>x. \<lbrace>\<lambda>s. x \<notin> S s\<rbrace> f \<lbrace>\<lambda>rv s. x \<notin> S s\<rbrace>"
  shows
  "\<lbrace>\<lambda>s. \<forall>S'. S' \<subseteq> S s \<longrightarrow> P S'\<rbrace>
     f
   \<lbrace>\<lambda>rv s. P (S s)\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (drule spec, erule mp)
  apply (clarsimp simp: subset_iff)
  apply (rule ccontr)
  apply (drule(1) use_valid [OF _ x])
  apply simp
  done

lemma shrinks_proof:
  assumes y: "\<And>s. finite (S s)"
  assumes x: "\<And>x. \<lbrace>\<lambda>s. x \<notin> S s \<and> P s\<rbrace> f \<lbrace>\<lambda>rv s. x \<notin> S s\<rbrace>"
  assumes z: "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. x \<notin> S s\<rbrace>"
  assumes w: "\<And>s. P s \<Longrightarrow> x \<in> S s"
  shows      "\<lbrace>\<lambda>s. card (S s) \<le> n \<and> P s\<rbrace> f \<lbrace>\<lambda>rv s. card (S s) < n\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (subgoal_tac "S b \<subset> S s")
   apply (drule psubset_card_mono [OF y], simp)
  apply (rule psubsetI)
   apply clarsimp
   apply (rule ccontr)
   apply (subgoal_tac "x \<notin> S b", simp)
   apply (erule use_valid [OF _ x])
   apply simp
  apply (rule not_sym)
  apply (rule set_neqI[where x=x])
   apply (erule w)
  apply (erule(1) use_valid [OF _ z])
  done

lemma unlessE_wp :
  "(\<not>P \<Longrightarrow> \<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace>,\<lbrace>E\<rbrace>) \<Longrightarrow> \<lbrace>if P then R () else Q\<rbrace> unlessE P f \<lbrace>R\<rbrace>,\<lbrace>E\<rbrace>"
  apply (clarsimp simp: unlessE_whenE whenE_def)
  apply wp
  done

lemma use_validE_R:
  "\<lbrakk> (Inr r, s') \<in> fst (f s); \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-; P s \<rbrakk> \<Longrightarrow> Q r s'"
  unfolding validE_R_def validE_def
  by (frule(2) use_valid, simp)

lemma valid_preservation_ex:
  assumes x: "\<And>x P. \<lbrace>\<lambda>s. P (f s x :: 'b)\<rbrace> m \<lbrace>\<lambda>rv s. P (f s x)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. P (f s :: 'a \<Rightarrow> 'b)\<rbrace> m \<lbrace>\<lambda>rv s. P (f s)\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (erule rsubst[where P=P])
  apply (rule ext)
  apply (erule use_valid [OF _ x])
  apply simp
  done

lemmas valid_prove_more' = valid_prove_more[where Q="\<lambda>rv. Q" for Q]

lemma whenE_inv:
  assumes a: "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. P\<rbrace>"
  shows "\<lbrace>P\<rbrace> whenE Q f \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding whenE_def
  apply (cases Q)
   apply simp
   apply (wp a)
  apply simp
  apply wp
  done

lemma whenE_liftE:
  "whenE P (liftE f) = liftE (when P f)"
  by (simp add: whenE_def when_def returnOk_liftE)

lemma whenE_throwError_wp:
  "\<lbrace>\<lambda>s. \<not> P \<longrightarrow> Q s\<rbrace> whenE P (throwError e) \<lbrace>\<lambda>_. Q\<rbrace>, \<lbrace>\<top>\<top>\<rbrace>"
  unfolding whenE_def
  apply (cases P)
   apply simp
   apply wp
  apply simp
  apply wp
  done

lemma whenE_whenE_body:
  "whenE P (throwError f) >>=E (\<lambda>_. whenE Q (throwError f) >>=E r) = whenE (P \<or> Q) (throwError f) >>=E r"
  apply (cases P)
   apply (simp add: whenE_def)
  apply simp
  done

lemma whenE_whenE_same:
  "whenE P (throwError f) >>=E (\<lambda>_. whenE P (throwError g) >>=E r) = whenE P (throwError f) >>=E r"
  apply (cases P)
   apply (simp add: whenE_def)
  apply simp
  done

lemma gets_the_inv: "\<lbrace>P\<rbrace> gets_the V \<lbrace>\<lambda>rv. P\<rbrace>" by wpsimp

lemma select_f_inv:
  "\<lbrace>P\<rbrace> select_f S \<lbrace>\<lambda>_. P\<rbrace>"
  by (simp add: select_f_def valid_def)

lemmas state_unchanged = in_inv_by_hoareD [THEN sym]

lemma validI:
  assumes rl: "\<And>s r s'. \<lbrakk> P s; (r, s') \<in> fst (S s) \<rbrakk> \<Longrightarrow> Q r s'"
  shows "\<lbrace>P\<rbrace> S \<lbrace>Q\<rbrace>"
  unfolding valid_def using rl by safe

lemma opt_return_pres_lift:
  assumes x: "\<And>v. \<lbrace>P\<rbrace> f v \<lbrace>\<lambda>rv. P\<rbrace>"
  shows      "\<lbrace>P\<rbrace> case x of None \<Rightarrow> return () | Some v \<Rightarrow> f v \<lbrace>\<lambda>rv. P\<rbrace>"
  by (rule hoare_pre, (wpcw; wp x), simp)

lemma exec_select_f_singleton:
  "(select_f ({v},False) >>= f) = f v"
  by (simp add: select_f_def bind_def)

lemma mapM_discarded:
  "mapM f xs >>= (\<lambda>ys. g) = mapM_x f xs >>= (\<lambda>_. g)"
  by (simp add: mapM_x_mapM)

lemma valid_return_unit:
  "\<lbrace>P\<rbrace> f >>= (\<lambda>_. return ()) \<lbrace>\<lambda>r. Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r. Q\<rbrace>"
  apply (rule validI)
  apply (fastforce simp: valid_def return_def bind_def split_def)
  done

lemma mapM_x_map:
  "mapM_x f (map g xs) = mapM_x (\<lambda>x. f (g x)) xs"
  by (simp add: mapM_x_def o_def)

lemma maybe_fail_bind_fail:
  "unless P fail >>= (\<lambda>_. fail) = fail"
  "when P fail >>= (\<lambda>_. fail) = fail"
  by (clarsimp simp: bind_def fail_def return_def
                     unless_def when_def)+

lemma unless_False:
  "unless False f = f"
  by (simp add: unless_def when_def)

lemma unless_True:
  "unless True f = return ()"
  by (simp add: unless_def when_def)

lemma filterM_preserved:
  "\<lbrakk> \<And>x. x \<in> set xs \<Longrightarrow> \<lbrace>P\<rbrace> m x \<lbrace>\<lambda>rv. P\<rbrace> \<rbrakk>
      \<Longrightarrow> \<lbrace>P\<rbrace> filterM m xs \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (induct xs)
   apply (wp | simp | erule meta_mp | drule meta_spec)+
  done

lemma filterM_append:
  "filterM f (xs @ ys) = (do
     xs' \<leftarrow> filterM f xs;
     ys' \<leftarrow> filterM f ys;
     return (xs' @ ys')
   od)"
  apply (induct xs)
   apply simp
  apply (simp add: bind_assoc)
  apply (rule ext bind_apply_cong [OF refl])+
  apply simp
  done

lemma filterM_distinct1:
  "\<lbrace>\<top> and K (P \<longrightarrow> distinct xs)\<rbrace> filterM m xs \<lbrace>\<lambda>rv s. (P \<longrightarrow> distinct rv) \<and> set rv \<subseteq> set xs\<rbrace>"
  apply (rule hoare_gen_asm, erule rev_mp)
  apply (rule rev_induct [where xs=xs])
   apply (clarsimp | wp)+
  apply (simp add: filterM_append)
  apply (erule hoare_seq_ext[rotated])
  apply (rule hoare_seq_ext[rotated], rule hoare_vcg_prop)
  apply (wp, clarsimp)
  apply blast
  done

lemma filterM_subset:
  "\<lbrace>\<top>\<rbrace> filterM m xs \<lbrace>\<lambda>rv s. set rv \<subseteq> set xs\<rbrace>"
  by (rule hoare_chain, rule filterM_distinct1[where P=False], simp_all)

lemma filterM_all:
  "\<lbrakk> \<And>x y. \<lbrakk> x \<in> set xs; y \<in> set xs \<rbrakk> \<Longrightarrow> \<lbrace>P y\<rbrace> m x \<lbrace>\<lambda>rv. P y\<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s. \<forall>x \<in> set xs. P x s\<rbrace> filterM m xs \<lbrace>\<lambda>rv s. \<forall>x \<in> set rv. P x s\<rbrace>"
  apply (rule_tac Q="\<lambda>rv s. set rv \<subseteq> set xs \<and> (\<forall>x \<in> set xs. P x s)"
              in hoare_strengthen_post)
   apply (wp filterM_subset hoare_vcg_const_Ball_lift filterM_preserved)
    apply simp+
  apply blast
  done


lemma filterM_distinct:
  "\<lbrace>K (distinct xs)\<rbrace> filterM m xs \<lbrace>\<lambda>rv s. distinct rv\<rbrace>"
  by (rule hoare_chain, rule filterM_distinct1[where P=True], simp_all)

lemma filterM_mapM:
  "filterM f xs = (do
     ys \<leftarrow> mapM (\<lambda>x. do v \<leftarrow> f x; return (x, v) od) xs;
     return (map fst (filter snd ys))
   od)"
  apply (induct xs)
   apply (simp add: mapM_def sequence_def)
  apply (simp add: mapM_Cons bind_assoc)
  apply (rule bind_cong [OF refl] bind_apply_cong[OF refl])+
  apply simp
  done

lemma if_return_closure:
  "(if P then return x else return y)
    = (return (if P then x else y))"
  by simp

lemma select_singleton:
  "select {x} = return x"
  by (fastforce simp add: fun_eq_iff select_def return_def)

lemma static_imp_wp:
  "\<lbrace>Q\<rbrace> m \<lbrace>R\<rbrace> \<Longrightarrow> \<lbrace>\<lambda>s. P \<longrightarrow> Q s\<rbrace> m \<lbrace>\<lambda>rv s. P \<longrightarrow> R rv s\<rbrace>"
  by (cases P, simp_all add: valid_def)

lemma static_imp_conj_wp:
  "\<lbrakk> \<lbrace>Q\<rbrace> m \<lbrace>Q'\<rbrace>; \<lbrace>R\<rbrace> m \<lbrace>R'\<rbrace> \<rbrakk>
    \<Longrightarrow> \<lbrace>\<lambda>s. (P \<longrightarrow> Q s) \<and> R s\<rbrace> m \<lbrace>\<lambda>rv s. (P \<longrightarrow> Q' rv s) \<and> R' rv s\<rbrace>"
  apply (rule hoare_vcg_conj_lift)
   apply (rule static_imp_wp)
   apply assumption+
  done

lemma hoare_eq_P:
  assumes "\<And>P. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. P\<rbrace>"
  shows "\<lbrace>(=) s\<rbrace> f \<lbrace>\<lambda>_. (=) s\<rbrace>"
  by (rule assms)

lemma hoare_validE_R_conj:
  "\<lbrakk>\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, -; \<lbrace>P\<rbrace> f \<lbrace>R\<rbrace>, -\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q And R\<rbrace>, -"
  by (simp add: valid_def validE_def validE_R_def Let_def split_def split: sum.splits)

lemma hoare_vcg_const_imp_lift_R:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,- \<Longrightarrow> \<lbrace>\<lambda>s. F \<longrightarrow> P s\<rbrace> f \<lbrace>\<lambda>rv s. F \<longrightarrow> Q rv s\<rbrace>,-"
  by (cases F, simp_all)

lemmas throwError_validE_R = throwError_wp [where E="\<top>\<top>", folded validE_R_def]

lemma valid_case_option_post_wp:
  "(\<And>x. \<lbrace>P x\<rbrace> f \<lbrace>\<lambda>rv. Q x\<rbrace>) \<Longrightarrow>
    \<lbrace>\<lambda>s. case ep of Some x \<Rightarrow> P x s | _ \<Rightarrow> True\<rbrace>
       f \<lbrace>\<lambda>rv s. case ep of Some x \<Rightarrow> Q x s | _ \<Rightarrow> True\<rbrace>"
  by (cases ep, simp_all add: hoare_vcg_prop)

lemma P_bool_lift:
  assumes t: "\<lbrace>Q\<rbrace> f \<lbrace>\<lambda>r. Q\<rbrace>"
  assumes f: "\<lbrace>\<lambda>s. \<not>Q s\<rbrace> f \<lbrace>\<lambda>r s. \<not>Q s\<rbrace>"
  shows "\<lbrace>\<lambda>s. P (Q s)\<rbrace> f \<lbrace>\<lambda>r s. P (Q s)\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (subgoal_tac "Q b = Q s")
   apply simp
  apply (rule iffI)
   apply (rule classical)
   apply (drule (1) use_valid [OF _ f])
   apply simp
  apply (erule (1) use_valid [OF _ t])
  done

lemma fail_inv :
  "\<lbrace> P \<rbrace> fail \<lbrace> \<lambda>r. P \<rbrace>"
  by wp

lemma gets_sp: "\<lbrace>P\<rbrace> gets f \<lbrace>\<lambda>rv. P and (\<lambda>s. f s = rv)\<rbrace>"
  by (wp, simp)

lemma post_by_hoare2:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>; (r, s') \<in> fst (f s); P s \<rbrakk> \<Longrightarrow> Q r s'"
  by (rule post_by_hoare, assumption+)

lemma hoare_Ball_helper:
  assumes x: "\<And>x. \<lbrace>P x\<rbrace> f \<lbrace>Q x\<rbrace>"
  assumes y: "\<And>P. \<lbrace>\<lambda>s. P (S s)\<rbrace> f \<lbrace>\<lambda>rv s. P (S s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. \<forall>x \<in> S s. P x s\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>x \<in> S s. Q x rv s\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (subgoal_tac "S b = S s")
   apply (erule post_by_hoare2 [OF x])
   apply (clarsimp simp: Ball_def)
  apply (erule_tac P1="\<lambda>x. x = S s" in post_by_hoare2 [OF y])
  apply (rule refl)
  done

lemma hoare_gets_post:
  "\<lbrace> P \<rbrace> gets f \<lbrace> \<lambda>r s. r = f s \<and> P s \<rbrace>"
  by (simp add: valid_def get_def gets_def bind_def return_def)

lemma hoare_return_post:
  "\<lbrace> P \<rbrace> return x \<lbrace> \<lambda>r s. r = x \<and> P s \<rbrace>"
  by (simp add: valid_def return_def)

lemma mapM_wp':
  assumes x: "\<And>x. x \<in> set xs \<Longrightarrow> \<lbrace>P\<rbrace> f x \<lbrace>\<lambda>rv. P\<rbrace>"
  shows "\<lbrace>P\<rbrace> mapM f xs \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (rule mapM_wp)
   apply (erule x)
  apply simp
  done

lemma mapM_set:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> \<lbrace>P\<rbrace> f x \<lbrace>\<lambda>_. P\<rbrace>"
  assumes "\<And>x y. x \<in> set xs \<Longrightarrow> \<lbrace>P\<rbrace> f x \<lbrace>\<lambda>_. Q x\<rbrace>"
  assumes "\<And>x y. \<lbrakk> x \<in> set xs; y \<in> set xs \<rbrakk> \<Longrightarrow> \<lbrace>P and Q y\<rbrace> f x \<lbrace>\<lambda>_. Q y\<rbrace>"
  shows "\<lbrace>P\<rbrace> mapM f xs \<lbrace>\<lambda>_ s. \<forall>x \<in> set xs. Q x s\<rbrace>"
using assms
proof (induct xs)
  case Nil show ?case
    by (simp add: mapM_def sequence_def) wp
next
  case (Cons y ys)
  have PQ_inv: "\<And>x. x \<in> set ys \<Longrightarrow> \<lbrace>P and Q y\<rbrace> f x \<lbrace>\<lambda>_. P and Q y\<rbrace>"
    apply (simp add: pred_conj_def)
    apply (rule hoare_pre)
     apply (wp Cons|simp)+
    done
  show ?case
    apply (simp add: mapM_Cons)
    apply wp
     apply (rule hoare_vcg_conj_lift)
      apply (rule hoare_strengthen_post)
       apply (rule mapM_wp')
       apply (erule PQ_inv)
      apply simp
     apply (wp Cons|simp)+
    done
qed

lemma case_option_fail_return_val:
  "(fst (case_option fail return v s) = {(rv, s')}) = (v = Some rv \<and> s = s')"
  by (cases v, simp_all add: fail_def return_def)

lemma return_expanded_inv:
  "\<lbrace>P\<rbrace> \<lambda>s. ({(x, s)}, False) \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: valid_def)

lemma empty_fail_assert : "empty_fail (assert P)"
  unfolding assert_def by simp

lemma no_fail_mapM':
  assumes rl: "\<And>x. no_fail (\<lambda>_. P x) (f x)"
  shows "no_fail (\<lambda>_. \<forall>x \<in> set xs. P x) (mapM f xs)"
proof (induct xs)
  case Nil thus ?case by (simp add: mapM_def sequence_def)
next
  case (Cons x xs)

  have nf: "no_fail (\<lambda>_. P x) (f x)" by (rule rl)
  have ih: "no_fail (\<lambda>_. \<forall>x \<in> set xs. P x) (mapM f xs)" by (rule Cons)

  show ?case
    apply (simp add: mapM_Cons)
    apply (rule no_fail_pre)
    apply (wp nf ih)
    apply simp
    done
qed

lemma handy_prop_divs:
  assumes x: "\<And>P. \<lbrace>\<lambda>s. P (Q s) \<and> S s\<rbrace> f \<lbrace>\<lambda>rv s. P (Q' rv s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (R s) \<and> S s\<rbrace> f \<lbrace>\<lambda>rv s. P (R' rv s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. P (Q s \<and> R s) \<and> S s\<rbrace> f \<lbrace>\<lambda>rv s. P (Q' rv s \<and> R' rv s)\<rbrace>"
             "\<lbrace>\<lambda>s. P (Q s \<or> R s) \<and> S s\<rbrace> f \<lbrace>\<lambda>rv s. P (Q' rv s \<or> R' rv s)\<rbrace>"
   apply (clarsimp simp: valid_def
                  elim!: rsubst[where P=P])
   apply (rule use_valid [OF _ x(1)], assumption)
   apply (rule use_valid [OF _ x(2)], assumption)
   apply simp
  apply (clarsimp simp: valid_def
                 elim!: rsubst[where P=P])
  apply (rule use_valid [OF _ x(1)], assumption)
  apply (rule use_valid [OF _ x(2)], assumption)
  apply simp
  done

lemma hoare_as_subst:
  "\<lbrakk> \<And>P. \<lbrace>\<lambda>s. P (fn s)\<rbrace> f \<lbrace>\<lambda>rv s. P (fn s)\<rbrace>;
     \<And>v :: 'a. \<lbrace>P v\<rbrace> f \<lbrace>Q v\<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s. P (fn s) s\<rbrace> f \<lbrace>\<lambda>rv s. Q (fn s) rv s\<rbrace>"
  apply (rule_tac Q="\<lambda>rv s. \<exists>v. v = fn s \<and> Q v rv s" in hoare_chain)
    apply (rule hoare_vcg_ex_lift)
    apply (rule hoare_vcg_conj_lift)
     apply assumption+
   apply simp
  apply simp
  done

lemmas hoare_vcg_ball_lift = hoare_vcg_const_Ball_lift

lemma select_singleton_is_return : "select {A} = return A"
  unfolding select_def return_def by (simp add: Sigma_def)

lemma assert_opt_eq_singleton:
  "(assert_opt f s = ({(v, s')},False)) = (s = s' \<and> f = Some v)"
  by (case_tac f, simp_all add: assert_opt_def
              fail_def return_def conj_comms)

lemma hoare_set_preserved:
  assumes x: "\<And>x. \<lbrace>fn' x\<rbrace> m \<lbrace>\<lambda>rv. fn x\<rbrace>"
  shows      "\<lbrace>\<lambda>s. set xs \<subseteq> {x. fn' x s}\<rbrace> m \<lbrace>\<lambda>rv s. set xs \<subseteq> {x. fn x s}\<rbrace>"
  apply (induct xs)
   apply simp
   apply wp
  apply simp
  apply (rule hoare_vcg_conj_lift)
   apply (rule x)
  apply assumption
  done

lemma return_modify:
  "return () = modify id"
  by (simp add: return_def simpler_modify_def)

lemma liftE_liftM_liftME:
  "liftE (liftM f m) = liftME f (liftE m)"
  by (simp add: liftE_liftM liftME_liftM liftM_def)


lemma assert_opt_member:
  "(x, s') \<in> fst (assert_opt y s) = (y = Some x \<and> s' = s)"
  apply (case_tac y, simp_all add: assert_opt_def fail_def return_def)
  apply safe
  done

lemma bind_return_unit:
  "f = (f >>= (\<lambda>x. return ()))"
  by simp

lemma det_mapM:
  assumes x: "\<And>x. x \<in> S \<Longrightarrow> det (f x)"
  shows      "set xs \<subseteq> S \<Longrightarrow> det (mapM f xs)"
  apply (induct xs)
   apply (simp add: mapM_def sequence_def)
  apply (simp add: mapM_Cons x)
  done

lemma det_zipWithM_x:
  assumes x: "\<And>x y. (x, y) \<in> set (zip xs ys) \<Longrightarrow> det (f x y)"
  shows      "det (zipWithM_x f xs ys)"
  apply (simp add: zipWithM_x_mapM)
  apply (rule bind_detI)
   apply (rule det_mapM [where S="set (zip xs ys)"])
    apply (clarsimp simp add: x)
   apply simp
  apply simp
  done

lemma empty_fail_sequence_x :
  assumes "\<And>m. m \<in> set ms \<Longrightarrow> empty_fail m"
  shows "empty_fail (sequence_x ms)" using assms
  by (induct ms) (auto simp: sequence_x_def)

lemma gets_the_member:
  "(x, s') \<in> fst (gets_the f s) = (f s = Some x \<and> s' = s)"
  by (case_tac "f s", simp_all add: gets_the_def
            simpler_gets_def bind_def assert_opt_member)

lemma hoare_ex_wp:
  assumes x: "\<And>x. \<lbrace>P x\<rbrace> f \<lbrace>Q x\<rbrace>"
  shows      "\<lbrace>\<lambda>s. \<exists>x. P x s\<rbrace> f \<lbrace>\<lambda>rv s. \<exists>x. Q x rv s\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (rule exI)
  apply (rule post_by_hoare [OF x])
   apply assumption+
  done

lemma hoare_ex_pre: (* safe, unlike hoare_ex_wp *)
  "(\<And>x. \<lbrace>P x\<rbrace> f \<lbrace>Q\<rbrace>) \<Longrightarrow> \<lbrace>\<lambda>s. \<exists>x. P x s\<rbrace> f \<lbrace>Q\<rbrace>"
  by (fastforce simp: valid_def)

lemma hoare_ex_pre_conj:
  "(\<And>x. \<lbrace>\<lambda>s. P x s \<and> P' s\<rbrace> f \<lbrace>Q\<rbrace>)
  \<Longrightarrow> \<lbrace>\<lambda>s. (\<exists>x. P x s) \<and> P' s\<rbrace> f \<lbrace>Q\<rbrace>"
  by (fastforce simp: valid_def)

lemma hoare_conj_lift_inv:
  "\<lbrakk>\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>; \<lbrace>\<lambda>s. P' s \<and> I s\<rbrace> f \<lbrace>\<lambda>rv. I\<rbrace>;
   \<And>s. P s \<Longrightarrow> P' s\<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s. P s \<and> I s\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> I s\<rbrace>"
   by (fastforce simp: valid_def)

lemma hoare_in_monad_post :
  assumes x: "\<And>P. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>x. P\<rbrace>"
  shows      "\<lbrace>\<top>\<rbrace> f \<lbrace>\<lambda>rv s. (rv, s) \<in> fst (f s)\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (subgoal_tac "s = b", simp)
  apply (simp add: state_unchanged [OF x])
  done

lemma mapM_gets:
  assumes P: "\<And>x. m x = gets (f x)"
  shows      "mapM m xs = gets (\<lambda>s. map (\<lambda>x. f x s) xs)"
proof (induct xs)
  case Nil show ?case
    by (simp add: mapM_def sequence_def gets_def get_def bind_def)
next
  case (Cons y ys) thus ?case
    by (simp add: mapM_Cons P simpler_gets_def return_def bind_def)
qed

lemma mapM_map_simp:
  "mapM m (map f xs) = mapM (m \<circ> f) xs"
  apply (induct xs)
   apply (simp add: mapM_def sequence_def)
  apply (simp add: mapM_Cons)
  done

lemma modify_id_return:
 "modify id = return ()"
  by (simp add: simpler_modify_def return_def)

definition
  oblivious :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a, 'b) nondet_monad \<Rightarrow> bool" where
 "oblivious f m \<equiv> \<forall>s. (\<forall>(rv, s') \<in> fst (m s). (rv, f s') \<in> fst (m (f s)))
                    \<and> (\<forall>(rv, s') \<in> fst (m (f s)). \<exists>s''. (rv, s'') \<in> fst (m s) \<and> s' = f s'')
                    \<and> snd (m (f s)) = snd (m s)"

lemma oblivious_return [simp]:
  "oblivious f (return x)"
  by (simp add: oblivious_def return_def)

lemma oblivious_fail [simp]:
  "oblivious f fail"
  by (simp add: oblivious_def fail_def)

lemma oblivious_assert [simp]:
  "oblivious f (assert x)"
  by (simp add: assert_def)

lemma oblivious_assert_opt [simp]:
  "oblivious f (assert_opt fn)"
  by (simp add: assert_opt_def split: option.splits)

lemma oblivious_bind:
  "\<lbrakk> oblivious f m; \<And>rv. oblivious f (m' rv) \<rbrakk>
      \<Longrightarrow> oblivious f (m >>= m')"
  apply atomize
  apply (simp add: oblivious_def)
  apply (erule allEI)
  apply (intro conjI)
    apply (drule conjunct1)
    apply (clarsimp simp: in_monad)
    apply fastforce
   apply (drule conjunct2, drule conjunct1)
   apply (clarsimp simp: in_monad)
   apply fastforce
  apply (clarsimp simp: bind_def disj_commute)
  apply (rule disj_cong [OF refl])
  apply (rule iffI)
   apply (clarsimp simp: split_def)
   apply fastforce
  apply clarsimp
  apply (drule(1) bspec)
  apply (clarsimp simp: split_def)
  apply (erule (1) my_BallE)
  apply (rule bexI [rotated], assumption)
  apply clarsimp
  done

lemma oblivious_gets [simp]:
  "oblivious f (gets f') = (\<forall>s. f' (f s) = f' s)"
  by (fastforce simp add: oblivious_def simpler_gets_def)

lemma oblivious_liftM:
  "oblivious f m \<Longrightarrow> oblivious f (liftM g m)"
  by (simp add: liftM_def oblivious_bind)

lemma oblivious_modify [simp]:
  "oblivious f (modify f') = (\<forall>s. f' (f s) = f (f' s))"
  apply (simp add: oblivious_def simpler_modify_def)
  apply (rule ball_cong[where A=UNIV, OF refl, simplified])
  apply fastforce
  done

lemma oblivious_modify_swap:
  "\<lbrakk> oblivious f m \<rbrakk>   \<Longrightarrow>
   (modify f >>= (\<lambda>rv. m))
    = (m >>= (\<lambda>rv. modify f))"
  apply (clarsimp simp: bind_def simpler_modify_def)
  apply (rule ext)+
  apply (case_tac "m (f s)", clarsimp)
  apply (simp add: oblivious_def)
  apply (drule_tac x=s in spec)
  apply (rule conjI)
   apply (rule set_eqI)
   apply (rule iffI)
    apply (drule conjunct2, drule conjunct1)
    apply (drule_tac x=x in bspec, simp)
    apply clarsimp
    apply (rule_tac x="((), s'')" in bexI)
     apply simp
    apply simp
   apply (drule conjunct1)
   apply fastforce
  apply (drule conjunct2)+
  apply fastforce
  done

lemma univ_wp:
  "\<lbrace>\<lambda>s. \<forall>(rv, s') \<in> fst (f s). Q rv s'\<rbrace> f \<lbrace>Q\<rbrace>"
  by (simp add: valid_def)

lemma univ_get_wp:
  assumes x: "\<And>P. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. P\<rbrace>"
  shows "\<lbrace>\<lambda>s. \<forall>(rv, s') \<in> fst (f s). s = s' \<longrightarrow> Q rv s'\<rbrace> f \<lbrace>Q\<rbrace>"
  apply (rule hoare_pre_imp [OF _ univ_wp])
  apply clarsimp
  apply (erule my_BallE, assumption, simp)
  apply (subgoal_tac "s = b", simp)
  apply (simp add: state_unchanged [OF x])
  done

lemma result_in_set_wp :
  assumes x: "\<And>P. \<lbrace>P\<rbrace> fn \<lbrace>\<lambda>rv. P\<rbrace>"
  shows      "\<lbrace>\<lambda>s. True\<rbrace> fn \<lbrace>\<lambda>v s'. (v, s') \<in> fst (fn s')\<rbrace>"
  by (rule hoare_pre_imp [OF _ univ_get_wp], simp_all add: x split_def) clarsimp

lemma other_result_in_set_wp:
  assumes x: "\<And>P. \<lbrace>P\<rbrace> fn \<lbrace>\<lambda>rv. P\<rbrace>"
  shows "\<lbrace>\<lambda>s. \<forall>(v, s) \<in> fst (fn s). F v = v\<rbrace> fn \<lbrace>\<lambda>v s'. (F v, s') \<in> fst (fn s')\<rbrace>"
  proof -
  have P: "\<And>v s. (F v = v) \<and> (v, s) \<in> fst (fn s) \<Longrightarrow> (F v, s) \<in> fst (fn s)"
    by simp
  show ?thesis
  apply (rule hoare_post_imp [OF P], assumption)
  apply (rule hoare_pre_imp)
  defer
   apply (rule hoare_vcg_conj_lift)
    apply (rule univ_get_wp [OF x])
   apply (rule result_in_set_wp [OF x])
  apply clarsimp
  apply (erule my_BallE, assumption, simp)
  done
  qed

lemma weak_if_wp:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>; \<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace> \<rbrakk> \<Longrightarrow>
  \<lbrace>P and P'\<rbrace> f \<lbrace>\<lambda>r. if C r then Q r else Q' r\<rbrace>"
  by (auto simp add: valid_def split_def)

lemma zipWithM_x_modify:
  "zipWithM_x (\<lambda>a b. modify (f a b)) as bs
   = modify (\<lambda>s. foldl (\<lambda>s (a, b). f a b s) s (zip as bs))"
  apply (simp add: zipWithM_x_def zipWith_def sequence_x_def)
  apply (induct ("zip as bs"))
   apply (simp add: simpler_modify_def return_def)
  apply (rule ext)
  apply (simp add: simpler_modify_def bind_def split_def)
  done

lemma bindE_split_recursive_asm:
  assumes x: "\<And>x s'. \<lbrakk> (Inr x, s') \<in> fst (f s) \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. B x s \<and> s = s'\<rbrace> g x \<lbrace>C\<rbrace>, \<lbrace>E\<rbrace>"
  shows      "\<lbrace>A\<rbrace> f \<lbrace>B\<rbrace>, \<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>\<lambda>st. A st \<and> st = s\<rbrace> f >>=E g \<lbrace>C\<rbrace>, \<lbrace>E\<rbrace>"
  apply (clarsimp simp: validE_def valid_def bindE_def bind_def lift_def)
  apply (erule allE, erule(1) impE)
  apply (erule(1) my_BallE, simp)
  apply (case_tac a, simp_all add: throwError_def return_def)
  apply (drule x)
  apply (clarsimp simp: validE_def valid_def)
  apply (erule(1) my_BallE, simp)
  done

lemma bind_known_operation_eq:
  "\<lbrakk> no_fail P f; \<lbrace>Q\<rbrace> f \<lbrace>\<lambda>rv s. rv = x \<and> s = t\<rbrace>; P s; Q s; empty_fail f \<rbrakk>
     \<Longrightarrow> (f >>= g) s = g x t"
  apply (drule(1) no_failD)
  apply (subgoal_tac "fst (f s) = {(x, t)}")
   apply (clarsimp simp: bind_def)
  apply (rule not_psubset_eq)
   apply (drule(1) empty_failD2, clarsimp)
   apply fastforce
  apply clarsimp
  apply (drule(1) use_valid, simp+)
  done


lemma gets_the_bind_eq:
  "\<lbrakk> f s = Some x; g x s = h s \<rbrakk>
    \<Longrightarrow> (gets_the f >>= g) s = h s"
  by (simp add: gets_the_def bind_assoc exec_gets assert_opt_def)

lemma hoare_const_imp_R:
  "\<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace>,- \<Longrightarrow> \<lbrace>\<lambda>s. P \<longrightarrow> Q s\<rbrace> f \<lbrace>\<lambda>rv s. P \<longrightarrow> R rv s\<rbrace>,-"
  by (cases P, simp_all)

lemma hoare_vcg_imp_lift_R:
  "\<lbrakk> \<lbrace>P'\<rbrace> f \<lbrace>\<lambda>rv s. \<not> P rv s\<rbrace>, -; \<lbrace>Q'\<rbrace> f \<lbrace>Q\<rbrace>, - \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. P' s \<or> Q' s\<rbrace> f \<lbrace>\<lambda>rv s. P rv s \<longrightarrow> Q rv s\<rbrace>, -"
  by (auto simp add: valid_def validE_R_def validE_def split_def split: sum.splits)

lemma hoare_disj_division:
  "\<lbrakk> P \<or> Q; P \<Longrightarrow> \<lbrace>R\<rbrace> f \<lbrace>S\<rbrace>; Q \<Longrightarrow> \<lbrace>T\<rbrace> f \<lbrace>S\<rbrace> \<rbrakk>
     \<Longrightarrow> \<lbrace>\<lambda>s. (P \<longrightarrow> R s) \<and> (Q \<longrightarrow> T s)\<rbrace> f \<lbrace>S\<rbrace>"
  apply safe
   apply (rule hoare_pre_imp)
    prefer 2
    apply simp
   apply simp
  apply (rule hoare_pre_imp)
   prefer 2
   apply simp
  apply simp
  done

lemma hoare_grab_asm:
  "\<lbrakk> G \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. G \<and> P s\<rbrace> f \<lbrace>Q\<rbrace>"
  by (cases G, simp+)

lemma hoare_grab_asm2:
  "(P' \<Longrightarrow> \<lbrace>\<lambda>s. P s \<and> R s\<rbrace> f \<lbrace>Q\<rbrace>)
  \<Longrightarrow> \<lbrace>\<lambda>s. P s \<and> P' \<and> R s\<rbrace> f \<lbrace>Q\<rbrace>"
  by (fastforce simp: valid_def)

lemma hoare_grab_exs:
  assumes x: "\<And>x. P x \<Longrightarrow> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>"
  shows      "\<lbrace>\<lambda>s. \<exists>x. P x \<and> P' s\<rbrace> f \<lbrace>Q\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (erule(2) use_valid [OF _ x])
  done

lemma hoare_prop_E: "\<lbrace>\<lambda>rv. P\<rbrace> f -,\<lbrace>\<lambda>rv s. P\<rbrace>"
  unfolding validE_E_def
  by (rule hoare_pre, wp, simp)

lemma hoare_vcg_conj_lift_R:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-; \<lbrace>R\<rbrace> f \<lbrace>S\<rbrace>,- \<rbrakk> \<Longrightarrow>
     \<lbrace>\<lambda>s. P s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> S rv s\<rbrace>,-"
  apply (simp add: validE_R_def validE_def)
  apply (drule(1) hoare_vcg_conj_lift)
  apply (erule hoare_strengthen_post)
  apply (clarsimp split: sum.splits)
  done

lemma hoare_walk_assmsE:
  assumes x: "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. P\<rbrace>" and y: "\<And>s. P s \<Longrightarrow> Q s" and z: "\<lbrace>P\<rbrace> g \<lbrace>\<lambda>rv. Q\<rbrace>"
  shows      "\<lbrace>P\<rbrace> doE x \<leftarrow> f; g odE \<lbrace>\<lambda>rv. Q\<rbrace>"
  apply (wp z)
  apply (simp add: validE_def)
  apply (rule hoare_strengthen_post [OF x])
  apply (case_tac r, simp_all add: y)
  done

lemma mapME_set:
  assumes  est: "\<And>x. \<lbrace>R\<rbrace> f x \<lbrace>P\<rbrace>, -"
  and     invp: "\<And>x y. \<lbrace>R and P x\<rbrace> f y \<lbrace>\<lambda>_. P x\<rbrace>, -"
  and     invr: "\<And>x. \<lbrace>R\<rbrace> f x \<lbrace>\<lambda>_. R\<rbrace>, -"
  shows "\<lbrace>R\<rbrace> mapME f xs \<lbrace>\<lambda>rv s. \<forall>x \<in> set rv. P x s\<rbrace>, -"
proof (rule hoare_post_imp_R [where Q' = "\<lambda>rv s. R s \<and> (\<forall>x \<in> set rv. P x s)"], induct xs)
  case Nil
  thus ?case by (simp add: mapME_Nil | wp returnOKE_R_wp)+
next
  case (Cons y ys)

  have minvp: "\<And>x. \<lbrace>R and P x\<rbrace> mapME f ys \<lbrace>\<lambda>_. P x\<rbrace>, -"
    apply (rule hoare_pre)
     apply (rule_tac Q' = "\<lambda>_ s. R s \<and> P x s" in hoare_post_imp_R)
      apply (wp mapME_wp' invr invp)+
      apply simp
     apply simp
    apply simp
    done

  show ?case
    apply (simp add: mapME_Cons)
    apply (wp)
     apply (rule_tac Q' = "\<lambda>xs s. (R s \<and> (\<forall>x \<in> set xs. P x s)) \<and> P x s" in hoare_post_imp_R)
      apply (wp Cons.hyps minvp)
     apply simp
    apply (fold validE_R_def)
    apply simp
    apply (wp invr est)
    apply simp
    done
qed clarsimp

lemma unlessE_throwError_returnOk:
  "(if P then returnOk v else throwError x)
    = (unlessE P (throwError x) >>=E (\<lambda>_. returnOk v))"
  by (cases P, simp_all add: unlessE_def)

lemma weaker_hoare_ifE:
  assumes x: "\<lbrace>P \<rbrace> a \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  assumes y: "\<lbrace>P'\<rbrace> b \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  shows      "\<lbrace>P and P'\<rbrace> if test then a else b \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  apply (rule hoare_vcg_precond_impE)
   apply (wp x y)
  apply simp
  done

lemma wp_split_const_if:
  assumes x: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  assumes y: "\<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>"
  shows "\<lbrace>\<lambda>s. (G \<longrightarrow> P s) \<and> (\<not> G \<longrightarrow> P' s)\<rbrace> f \<lbrace>\<lambda>rv s. (G \<longrightarrow> Q rv s) \<and> (\<not> G \<longrightarrow> Q' rv s)\<rbrace>"
  by (case_tac G, simp_all add: x y)

lemma wp_split_const_if_R:
  assumes x: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-"
  assumes y: "\<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>,-"
  shows "\<lbrace>\<lambda>s. (G \<longrightarrow> P s) \<and> (\<not> G \<longrightarrow> P' s)\<rbrace> f \<lbrace>\<lambda>rv s. (G \<longrightarrow> Q rv s) \<and> (\<not> G \<longrightarrow> Q' rv s)\<rbrace>,-"
  by (case_tac G, simp_all add: x y)

lemma wp_throw_const_imp:
  assumes x: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  shows      "\<lbrace>\<lambda>s. G \<longrightarrow> P s\<rbrace> f \<lbrace>\<lambda>rv s. G \<longrightarrow> Q rv s\<rbrace>"
  by (case_tac G, simp_all add: x hoare_vcg_prop)

lemma wp_throw_const_impE:
  assumes x: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  shows      "\<lbrace>\<lambda>s. G \<longrightarrow> P s\<rbrace> f \<lbrace>\<lambda>rv s. G \<longrightarrow> Q rv s\<rbrace>,\<lbrace>\<lambda>rv s. G \<longrightarrow> E rv s\<rbrace>"
  apply (case_tac G, simp_all add: x)
  apply wp
  done

lemma distinct_tuple_helper:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. distinct (x # xs rv s)\<rbrace> \<Longrightarrow>
   \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. distinct (x # (map fst (zip (xs rv s) (ys rv s))))\<rbrace>"
  apply (erule hoare_strengthen_post)
  apply (erule distinct_prefix)
  apply (simp add: map_fst_zip_prefix)
  done

lemma list_case_throw_validE_R:
  "\<lbrakk> \<And>y ys. xs = y # ys \<Longrightarrow> \<lbrace>P\<rbrace> f y ys \<lbrace>Q\<rbrace>,- \<rbrakk> \<Longrightarrow>
   \<lbrace>P\<rbrace> case xs of [] \<Rightarrow> throwError e | x # xs \<Rightarrow> f x xs \<lbrace>Q\<rbrace>,-"
  apply (case_tac xs, simp_all)
  apply wp
  done

lemma validE_R_sp:
  assumes x: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-"
  assumes y: "\<And>x. \<lbrace>Q x\<rbrace> g x \<lbrace>R\<rbrace>,-"
  shows "\<lbrace>P\<rbrace> f >>=E (\<lambda>x. g x) \<lbrace>R\<rbrace>,-"
  by (rule hoare_pre, wp x y, simp)

lemma valid_set_take_helper:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>x \<in> set (xs rv s). Q x rv s\<rbrace>
    \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>x \<in> set (take (n rv s) (xs rv s)). Q x rv s\<rbrace>"
  apply (erule hoare_strengthen_post)
  apply (clarsimp dest!: in_set_takeD)
  done

lemma whenE_throwError_sp:
  "\<lbrace>P\<rbrace> whenE Q (throwError e) \<lbrace>\<lambda>rv s. \<not> Q \<and> P s\<rbrace>, -"
  apply (simp add: whenE_def validE_R_def)
  apply (intro conjI impI; wp)
  done

lemma no_fail_bindE [wp]:
  "\<lbrakk> no_fail P f; \<And>rv. no_fail (R rv) (g rv); \<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace>,- \<rbrakk>
     \<Longrightarrow> no_fail (P and Q) (f >>=E g)"
  apply (simp add: bindE_def)
  apply (erule no_fail_bind)
   apply (simp add: lift_def)
   apply wpc
    apply (simp add: throwError_def)
    apply wp
   apply assumption
  apply (simp add: validE_R_def validE_def)
  apply (erule hoare_strengthen_post)
  apply clarsimp
  done

lemma empty_fail_mapM_x [simp]:
  "(\<And>x. empty_fail (a x)) \<Longrightarrow> empty_fail (mapM_x a xs)"
  apply (induct_tac xs)
   apply (clarsimp simp: mapM_x_Nil)
  apply (clarsimp simp: mapM_x_Cons)
  done

lemma fst_throwError_returnOk:
  "fst (throwError e s) = {(Inl e, s)}"
  "fst (returnOk v s) = {(Inr v, s)}"
  by (simp add: throwError_def returnOk_def return_def)+

lemma liftE_bind_return_bindE_returnOk:
  "liftE (v >>= (\<lambda>rv. return (f rv)))
     = (liftE v >>=E (\<lambda>rv. returnOk (f rv)))"
  by (simp add: liftE_bindE, simp add: liftE_def returnOk_def)

lemma bind_eqI:
  "g = g' \<Longrightarrow> f >>= g = f >>= g'" by simp

lemma not_snd_bindE_I1:
  "\<not> snd ((a >>=E b) s) \<Longrightarrow> \<not> snd (a s)"
  unfolding bindE_def
  by (erule not_snd_bindI1)

lemma snd_assert [monad_eq]:
  "snd (assert P s) = (\<not> P)"
  apply (clarsimp simp: fail_def return_def assert_def)
  done

lemma not_snd_assert :
  "(\<not> snd (assert P s)) = P"
  by (metis snd_assert)

lemma snd_assert_opt [monad_eq]:
  "snd (assert_opt f s) = (f = None)"
    by (monad_eq simp: assert_opt_def split: option.splits)

declare in_assert_opt [monad_eq]

lemma empty_fail_catch:
  "\<lbrakk> empty_fail f; \<And>x. empty_fail (g x) \<rbrakk> \<Longrightarrow> empty_fail (catch f g)"
  apply (simp add: catch_def)
  apply (erule empty_fail_bind)
  apply (simp split: sum.split)
  done

lemma oblivious_returnOk [simp]:
  "oblivious f (returnOk e)"
  by (simp add: returnOk_def)

lemma oblivious_assertE [simp]:
  "oblivious f (assertE P)"
  by (simp add: assertE_def split: if_split)


lemma oblivious_throwError [simp]:
  "oblivious f (throwError e)"
  by (simp add: throwError_def)

lemma oblivious_bindE:
  "\<lbrakk> oblivious u f; \<And>v. oblivious u (g v) \<rbrakk>
       \<Longrightarrow> oblivious u (f >>=E (\<lambda>v. g v))"
  apply (simp add: bindE_def)
  apply (erule oblivious_bind)
  apply (simp add: lift_def split: sum.split)
  done

lemma oblivious_catch:
  "\<lbrakk> oblivious u f; \<And>v. oblivious u (g v) \<rbrakk>
       \<Longrightarrow> oblivious u (catch f g)"
  apply (simp add: catch_def)
  apply (erule oblivious_bind)
  apply (simp split: sum.split)
  done

lemma oblivious_when [simp]:
  "oblivious f (when P m) = (P \<longrightarrow> oblivious f m)"
  by (simp add: when_def split: if_split)

lemma oblivious_whenE [simp]:
  "oblivious f (whenE P g) = (P \<longrightarrow> oblivious f g)"
  by (simp add: whenE_def split: if_split)

lemma select_f_oblivious [simp]:
  "oblivious f (select_f v)"
  by (simp add: oblivious_def select_f_def)

lemma oblivious_select:
  "oblivious f (select S)"
  by (simp add: oblivious_def select_def)

lemma validE_R_abstract_rv:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>rv'. Q rv' s\<rbrace>,- \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-"
  by (erule hoare_post_imp_R, simp)

lemma validE_cases_valid:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q (Inr rv) s\<rbrace>,\<lbrace>\<lambda>rv s. Q (Inl rv) s\<rbrace>
      \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  apply (simp add: validE_def)
  apply (erule hoare_strengthen_post)
  apply (simp split: sum.split_asm)
  done

lemma valid_isRight_theRight_split:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q True rv s\<rbrace>,\<lbrace>\<lambda>e s. \<forall>v. Q False v s\<rbrace> \<Longrightarrow>
     \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q (isRight rv) (theRight rv) s\<rbrace>"
  apply (simp add: validE_def)
  apply (erule hoare_strengthen_post)
  apply (simp add: isRight_def split: sum.split_asm)
  done

lemma bind_return_subst:
  assumes r: "\<And>r. \<lbrace>\<lambda>s. P x = r\<rbrace> f x \<lbrace>\<lambda>rv s. Q rv = r\<rbrace>"
  shows
  "do a \<leftarrow> f x;
      g (Q a)
   od =
   do _ \<leftarrow> f x;
      g (P x)
   od"
proof -
  have "do a \<leftarrow> f x;
           return (Q a)
        od =
        do _ \<leftarrow> f x;
           return (P x)
        od"
    using r
    apply (subst fun_eq_iff)
    apply (fastforce simp: bind_def valid_def return_def)
    done
  hence "do a \<leftarrow> f x;
            return (Q a)
         od >>= g =
         do _ \<leftarrow> f x;
            return (P x)
         od >>= g"
    by (rule bind_cong, simp)
  thus ?thesis
    by simp
qed

lemma zipWithM_x_Nil2 :
  "zipWithM_x f xs [] = return ()"
  by (simp add: zipWithM_x_mapM mapM_Nil)

lemma assert2:
  "(do v1 \<leftarrow> assert P; v2 \<leftarrow> assert Q; c od)
     = (do v \<leftarrow> assert (P \<and> Q); c od)"
  by (simp add: assert_def split: if_split)

lemma assert_opt_def2:
  "assert_opt v = (do assert (v \<noteq> None); return (the v) od)"
  by (simp add: assert_opt_def split: option.split)

lemma filterM_voodoo:
  "\<forall>ys. P ys (do zs \<leftarrow> filterM m xs; return (ys @ zs) od)
       \<Longrightarrow> P [] (filterM m xs)"
  by (drule spec[where x=Nil], simp)

lemma gets_assert:
  "(do v1 \<leftarrow> assert v; v2 \<leftarrow> gets f; c v1 v2 od)
     = (do v2 \<leftarrow> gets f; v1 \<leftarrow> assert v; c v1 v2 od)"
  by (simp add: simpler_gets_def return_def assert_def fail_def bind_def
         split: if_split)

lemma list_case_return2:
  "(case x of [] \<Rightarrow> return v | y # ys \<Rightarrow> return (f y ys))
        = return (case x of [] \<Rightarrow> v | y # ys \<Rightarrow> f y ys)"
  by (simp split: list.split)

lemma modify_assert:
  "(do v2 \<leftarrow> modify f; v1 \<leftarrow> assert v; c v1 od)
    = (do v1 \<leftarrow> assert v; v2 \<leftarrow> modify f; c v1 od)"
  by (simp add: simpler_modify_def return_def assert_def fail_def bind_def
         split: if_split)

lemma gets_fold_into_modify:
  "do x \<leftarrow> gets f; modify (g x) od = modify (\<lambda>s. g (f s) s)"
  "do x \<leftarrow> gets f; _ \<leftarrow> modify (g x); h od
     = do modify (\<lambda>s. g (f s) s); h od"
  by (simp_all add: fun_eq_iff modify_def bind_assoc exec_gets
                    exec_get exec_put)

lemma bind_assoc2:
  "(do x \<leftarrow> a; _ \<leftarrow> b; c x od) = (do x \<leftarrow> (do x' \<leftarrow> a; _ \<leftarrow> b; return x' od); c x od)"
  by (simp add: bind_assoc)

lemma liftM_pre:
  assumes rl: "\<lbrace>\<lambda>s. \<not> P s \<rbrace> a \<lbrace> \<lambda>_ _. False \<rbrace>"
  shows "\<lbrace>\<lambda>s. \<not> P s \<rbrace> liftM f a \<lbrace> \<lambda>_ _. False \<rbrace>"
  unfolding liftM_def
  apply (rule seq)
  apply (rule rl)
  apply wp
  apply simp
  done

lemma not_snd_bindD':
  "\<lbrakk>\<not> snd ((a >>= b) s); \<not> snd (a s) \<Longrightarrow> (rv, s') \<in> fst (a s)\<rbrakk> \<Longrightarrow> \<not> snd (a s) \<and> \<not> snd (b rv s')"
  apply (frule not_snd_bindI1)
  apply (erule not_snd_bindD)
  apply simp
  done

lemma snd_bind [monad_eq]:
  "snd ((a >>= b) s) = (snd (a s) \<or> (\<exists>r s'. (r, s') \<in> fst (a s) \<and> snd (b r s')))"
  apply (clarsimp simp add: bind_def Bex_def image_def)
  apply (subst surjective_pairing, subst prod.inject, force)
  done

lemma in_lift [monad_eq]:
    "(rv, s') \<in> fst (lift M v s) =
      (case v of Inl x \<Rightarrow> rv = Inl x \<and> s' = s
               | Inr x \<Rightarrow> (rv, s') \<in> fst (M x s))"
  apply (clarsimp simp: lift_def throwError_def return_def split: sum.splits)
  done

lemma snd_lift [monad_eq]:
    "snd (lift M a b) = (\<exists>x. a = Inr x \<and> snd (M x b))"
  apply (clarsimp simp: lift_def throwError_def return_def split: sum.splits)
  done

lemma snd_bindE [monad_eq]:
  "snd ((a >>=E b) s) = (snd (a s) \<or> (\<exists>r s'. (r, s') \<in> fst (a s) \<and> (\<exists>a. r = Inr a \<and> snd (b a s'))))"
  apply (clarsimp simp: bindE_def)
  apply monad_eq
  done

lemma snd_get [monad_eq]:
  shows "(snd (get s)) = False"
  by (simp add: get_def)

lemma snd_gets [monad_eq]:
  shows "(snd (gets f s)) = False"
  by (simp add: gets_def snd_bind snd_get snd_return)

lemma mapME_x_Cons:
  "mapME_x f (x # xs) = (doE f x; mapME_x f xs odE)"
  by (simp add: mapME_x_def sequenceE_x_def)

lemma liftME_map_mapME:
  "liftME (map f) (mapME m xs)
      = mapME (liftME f o m) xs"
  apply (rule sym)
  apply (induct xs)
   apply (simp add: liftME_def mapME_Nil)
  apply (simp add: mapME_Cons liftME_def bindE_assoc)
  done

lemma mapM_upd_inv:
  assumes f: "\<And>x rv. (rv,s) \<in> fst (f x s) \<Longrightarrow> x \<in> set xs \<Longrightarrow> (rv, g s) \<in> fst (f x (g s))"
  assumes inv: "\<And>x. \<lbrace>(=) s\<rbrace> f x \<lbrace>\<lambda>_. (=) s\<rbrace>"
  shows "(rv,s) \<in> fst (mapM f xs s) \<Longrightarrow> (rv, g s) \<in> fst (mapM f xs (g s))"
  using f inv
proof (induct xs arbitrary: rv s)
  case Nil
  thus ?case by (simp add: mapM_Nil return_def)
next
  case (Cons z zs)
  from Cons.prems
  show ?case
    apply (clarsimp simp: mapM_Cons in_monad)
    apply (frule use_valid, assumption, rule refl)
    apply clarsimp
    apply (drule Cons.prems, simp)
    apply (rule exI, erule conjI)
    apply (drule Cons.hyps)
      apply simp
     apply assumption
    apply simp
    done
qed


(* FUXME: duplicate *)
lemma mapM_x_append2:
  "mapM_x f (xs @ ys) = do mapM_x f xs; mapM_x f ys od"
  apply (simp add: mapM_x_def sequence_x_def)
  apply (induct xs)
   apply simp
  apply (simp add: bind_assoc)
  done

lemma mapM_x_split_append:
  "mapM_x f xs = do _ \<leftarrow> mapM_x f (take n xs); mapM_x f (drop n xs) od"
  using mapM_x_append[where f=f and xs="take n xs" and ys="drop n xs"]
  by simp

lemma hoare_gen_asm':
  "(P \<Longrightarrow> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>) \<Longrightarrow> \<lbrace>P' and (\<lambda>_. P)\<rbrace> f \<lbrace>Q\<rbrace>"
  apply (auto intro: hoare_assume_pre)
  done

lemma hoare_gen_asm_conj:
  "(P \<Longrightarrow> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>) \<Longrightarrow> \<lbrace>\<lambda>s. P' s \<and> P\<rbrace> f \<lbrace>Q\<rbrace>"
  by (fastforce simp: valid_def)


lemma hoare_add_K:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>\<lambda>s. P s \<and> I\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> I\<rbrace>"
  by (fastforce simp: valid_def)


lemma valid_rv_lift:
  "\<lbrace>P'\<rbrace> f \<lbrace>\<lambda>rv s. rv \<longrightarrow> Q rv s\<rbrace> \<Longrightarrow> \<lbrace>\<lambda>s. P \<and> P' s\<rbrace> f \<lbrace>\<lambda>rv s. rv \<longrightarrow> P \<and> Q rv s\<rbrace>"
  by (fastforce simp: valid_def)

lemma valid_imp_ex:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. \<exists>x. rv \<longrightarrow> Q rv s x\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. rv \<longrightarrow> (\<exists>x. Q rv s x)\<rbrace>"
  by (fastforce simp: valid_def)

lemma valid_rv_split:
  "\<lbrakk>\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. rv \<longrightarrow> Q s\<rbrace>; \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. \<not>rv \<longrightarrow> Q' s\<rbrace>\<rbrakk>
  \<Longrightarrow>
  \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. if rv then Q s else Q' s\<rbrace>"
  by (fastforce simp: valid_def)

lemma hoare_rv_split:
  "\<lbrakk>\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. rv \<longrightarrow> (Q rv s)\<rbrace>; \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. (\<not>rv) \<longrightarrow> (Q rv s)\<rbrace>\<rbrakk>
  \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (case_tac a, fastforce+)
  done

lemma case_option_find_give_me_a_map:
  "case_option a return (find f xs)
    = liftM theLeft
      (mapME (\<lambda>x. if (f x) then throwError x else returnOk ()) xs
        >>=E (\<lambda>x. assert (\<forall>x \<in> set xs. \<not> f x)
                >>= (\<lambda>_. liftM (Inl :: 'a \<Rightarrow> 'a + unit) a)))"
  apply (induct xs)
   apply simp
   apply (simp add: liftM_def mapME_Nil)
  apply (simp add: mapME_Cons split: if_split)
  apply (clarsimp simp add: throwError_def bindE_def bind_assoc
                            liftM_def)
  apply (rule bind_cong [OF refl])
  apply (simp add: lift_def throwError_def returnOk_def split: sum.split)
  done

lemma if_bind:
  "(if P then (a >>= (\<lambda>_. b)) else return ()) =
  (if P then a else return ()) >>= (\<lambda>_. if P then b else return ())"
  apply (cases P)
   apply simp
  apply simp
  done

lemma in_handleE' [monad_eq]:
    "((rv, s') \<in> fst ((f <handle2> g) s)) =
    ((\<exists>ex. rv = Inr ex \<and> (Inr ex, s') \<in> fst (f s)) \<or>
     (\<exists>rv' s''. (rv, s') \<in> fst (g rv' s'') \<and> (Inl rv', s'') \<in> fst (f s)))"
  apply (clarsimp simp: handleE'_def)
  apply (rule iffI)
   apply (subst (asm) in_bind_split)
   apply (clarsimp simp: return_def split: sum.splits)
   apply (case_tac a)
    apply (erule allE, erule (1) impE)
    apply clarsimp
   apply (erule allE, erule (1) impE)
   apply clarsimp
  apply (subst in_bind_split)
  apply (clarsimp simp: return_def split: sum.splits)
  apply blast
  done

lemma in_handleE [monad_eq]:
  "(a, b) \<in> fst ((A <handle> B) s) =
     ((\<exists>x. a = Inr x \<and> (Inr x, b) \<in> fst (A s))
       \<or> (\<exists>r t. ((Inl r, t) \<in> fst (A s)) \<and> ((a, b) \<in> fst (B r t))))"
  apply (unfold handleE_def)
  apply (monad_eq split: sum.splits)
  apply blast
  done

lemma snd_handleE' [monad_eq]:
    "snd ((A <handle2> B) s) = (snd (A s) \<or> (\<exists>r s'. (r, s')\<in>fst (A s) \<and> (\<exists>a. r = Inl a \<and> snd (B a s'))))"
  apply (clarsimp simp: handleE'_def)
  apply (monad_eq simp: Bex_def split: sum.splits)
  apply (metis sum.sel(1) sum.distinct(1) sumE)
  done

lemma snd_handleE [monad_eq]:
    "snd ((A <handle> B) s) = (snd (A s) \<or> (\<exists>r s'. (r, s')\<in>fst (A s) \<and> (\<exists>a. r = Inl a \<and> snd (B a s'))))"
  apply (unfold handleE_def)
  apply (rule snd_handleE')
  done

declare in_liftE [monad_eq]

lemma snd_liftE [monad_eq]:
    "snd ((liftE x) s) = snd (x s)"
  apply (clarsimp simp: liftE_def snd_bind snd_return)
  done

lemma snd_returnOk [monad_eq]:
    "\<not> snd (returnOk x s)"
  apply (clarsimp simp: returnOk_def return_def)
  done

lemma snd_when [monad_eq]:
  "snd (when P M s) = (P \<and> snd (M s))"
  apply (clarsimp simp: when_def return_def)
  done

lemma bind_liftE_distrib: "(liftE (A >>= (\<lambda>x. B x))) = (liftE A >>=E (\<lambda>x. liftE (\<lambda>s. B x s)))"
  apply (clarsimp simp: liftE_def bindE_def lift_def bind_assoc)
  done

lemma in_condition [monad_eq]:
  "((a, b) \<in> fst (condition C L R s)) = ((C s \<longrightarrow> (a, b) \<in> fst (L s)) \<and> (\<not> C s \<longrightarrow> (a, b) \<in> fst (R s)))"
  by (rule condition_split)

lemma snd_condition [monad_eq]:
  "(snd (condition C L R s)) = ((C s \<longrightarrow> snd (L s)) \<and> (\<not> C s \<longrightarrow> snd (R s)))"
  by (rule condition_split)

lemma condition_apply_cong:
  "\<lbrakk> c s = c' s'; s = s'; \<And>s. c' s \<Longrightarrow> l s = l' s  ; \<And>s. \<not> c' s \<Longrightarrow> r s = r' s  \<rbrakk> \<Longrightarrow>  condition c l r s = condition c' l' r' s'"
  apply (clarsimp split: condition_splits)
  done

lemma condition_cong [cong, fundef_cong]:
  "\<lbrakk> c = c'; \<And>s. c' s \<Longrightarrow> l s = l' s; \<And>s. \<not> c' s \<Longrightarrow> r s = r' s \<rbrakk> \<Longrightarrow> condition c l r = condition c' l' r'"
  apply (rule ext)
  apply (clarsimp split: condition_splits)
  done

(* Alternative definition of no_throw; easier to work with than unfolding validE. *)
lemma no_throw_def': "no_throw P A = (\<forall>s. P s \<longrightarrow> (\<forall>(r, t) \<in> fst (A s). (\<exists>x. r = Inr x)))"
  apply (clarsimp simp: no_throw_def validE_def2 split_def split: sum.splits)
  done

lemma no_throw_returnOk [simp]:
  "no_throw P (returnOk a)"
  apply (clarsimp simp: no_throw_def)
  apply wp
  done

lemma no_throw_liftE [simp]:
  "no_throw P (liftE x)"
  apply (clarsimp simp: liftE_def no_throw_def validE_def)
  apply (wp | simp)+
  done

lemma no_throw_bindE: "\<lbrakk> no_throw A X; \<And>a. no_throw B (Y a); \<lbrace> A \<rbrace> X \<lbrace> \<lambda>_. B \<rbrace>,\<lbrace> \<lambda>_ _. True \<rbrace> \<rbrakk> \<Longrightarrow> no_throw A (X >>=E Y)"
  apply atomize
  apply (clarsimp simp: no_throw_def)
  apply (rule seqE [rotated])
   apply force
  apply (rule  hoare_validE_cases)
   apply simp
  apply simp
  done

lemma no_throw_bindE_simple: "\<lbrakk> no_throw \<top> L; \<And>x. no_throw \<top> (R x) \<rbrakk> \<Longrightarrow> no_throw \<top> (L >>=E R)"
  apply (erule no_throw_bindE)
   apply assumption
  apply wp
  done

lemma no_throw_handleE_simple:
  notes hoare_vcg_prop[wp del]
  shows "\<lbrakk> \<And>x. no_throw \<top> L \<or> no_throw \<top> (R x) \<rbrakk> \<Longrightarrow> no_throw \<top> (L <handle> R)"
  apply (clarsimp simp: no_throw_def)
  apply atomize
  apply clarsimp
  apply (erule disjE)
   apply (wpsimp wp: hoare_vcg_prop[where f="R x" for x])
    apply assumption
   apply simp
  apply (rule handleE_wp)
   apply (erule_tac x=x in allE)
   apply assumption
  apply wp
  done

lemma no_throw_handle2: "\<lbrakk> \<And>a. no_throw Y (B a); \<lbrace> X \<rbrace> A \<lbrace> \<lambda>_ _. True \<rbrace>,\<lbrace> \<lambda>_. Y \<rbrace> \<rbrakk> \<Longrightarrow> no_throw X (A <handle2> B)"
  apply atomize
  apply (clarsimp simp: no_throw_def' handleE'_def bind_def)
  apply (clarsimp simp: validE_def valid_def)
  apply (erule allE, erule (1) impE)
  apply (erule (1) my_BallE)
  apply (clarsimp simp: return_def split: sum.splits)
  apply force
  done

lemma no_throw_handle: "\<lbrakk> \<And>a. no_throw Y (B a); \<lbrace> X \<rbrace> A \<lbrace> \<lambda>_ _. True \<rbrace>,\<lbrace> \<lambda>_. Y \<rbrace> \<rbrakk> \<Longrightarrow> no_throw X (A <handle> B)"
  apply (unfold handleE_def)
  apply (erule (1) no_throw_handle2)
  done

lemma no_throw_fail [simp]: "no_throw P fail"
  apply (clarsimp simp: no_throw_def)
  done

lemma lift_Inr [simp]: "(lift X (Inr r)) = (X r)"
  apply (rule ext)+
  apply (clarsimp simp: lift_def bind_def split_def image_def)
  done

lemma lift_Inl [simp]: "lift C (Inl a) = throwError a"
  apply (clarsimp simp: lift_def throwError_def)
  done

lemma returnOk_def2:  "returnOk a = return (Inr a)"
  apply (clarsimp simp: returnOk_def return_def)
  done

lemma empty_fail_spec [simp]: "empty_fail (state_select F)"
  apply (clarsimp simp: state_select_def empty_fail_def)
  done

declare snd_fail [simp]

lemma empty_fail_select [simp]: "empty_fail (select V) = (V \<noteq> {})"
  apply (clarsimp simp: select_def empty_fail_def)
  done

lemma bind_fail_propagates: "\<lbrakk> empty_fail A \<rbrakk> \<Longrightarrow> A >>= (\<lambda>_. fail) = fail"
  apply (monad_eq simp: empty_fail_def)
  by fastforce

lemma bindE_fail_propagates: "\<lbrakk> no_throw \<top> A; empty_fail A \<rbrakk> \<Longrightarrow> A >>=E (\<lambda>_. fail) = fail"
  apply (rule ext)
  apply (clarsimp simp: empty_fail_def)
  apply (clarsimp simp: no_throw_def validE_def valid_def bind_def
      bindE_def split_def fail_def NonDetMonad.lift_def throwError_def
      split:sum.splits)
  apply fastforce
  done

lemma empty_fail_liftE [simp]:
  "empty_fail (liftE X) = empty_fail X"
  apply (simp add: empty_fail_error_bits)
  done

declare snd_returnOk [simp, monad_eq]

lemma liftE_fail [simp]: "liftE fail = fail"
  apply monad_eq
  done

lemma in_catch [monad_eq]:
  "(r, t) \<in> fst ((M <catch> E) s)
       = ((Inr r, t) \<in> fst (M s)
             \<or> (\<exists>r' s'. ((Inl r', s') \<in> fst (M s)) \<and> (r, t) \<in> fst (E r' s')))"
  apply (rule iffI)
   apply (clarsimp simp: catch_def in_bind in_return split: sum.splits)
   apply (metis sumE)
  apply (clarsimp simp: catch_def in_bind in_return split: sum.splits)
  apply (metis sum.sel(1) sum.distinct(1) sum.inject(2))
  done

lemma snd_catch [monad_eq]:
  "snd ((M <catch> E) s)
       = (snd (M s)
             \<or> (\<exists>r' s'. ((Inl r', s') \<in> fst (M s)) \<and> snd (E r' s')))"
  apply (rule iffI)
   apply (clarsimp simp: catch_def snd_bind snd_return split: sum.splits)
  apply (clarsimp simp: catch_def snd_bind snd_return split: sum.splits)
  apply force
  done

lemma in_get [monad_eq]:
    "(r, s') \<in> fst (get s) = (r = s \<and> s' = s)"
  apply (clarsimp simp: get_def)
  done

lemma returnOk_cong: "\<lbrakk> \<And>s. B a s = B' a s \<rbrakk> \<Longrightarrow> ((returnOk a) >>=E B) = ((returnOk a) >>=E B')"
  apply monad_eq
  done

lemma in_state_assert [monad_eq, simp]:
  "(rv, s') \<in> fst (state_assert P s) = (rv = () \<and> s' = s \<and> P s)"
  apply (monad_eq simp: state_assert_def)
  apply metis
  done

lemma snd_state_assert [monad_eq]:
  "snd (state_assert P s) = (\<not> P s)"
  apply (monad_eq simp: state_assert_def Bex_def)
  done

lemma state_assert_false [simp]: "state_assert (\<lambda>_. False) = fail"
  by monad_eq

lemma no_fail_state_assert [wp]: "no_fail P (state_assert P)"
  by (monad_eq simp: no_fail_def state_assert_def)

lemma no_fail_modify [wp]: "no_fail \<top> (modify M)"
  by (metis non_fail_modify)

lemma combine_validE: "\<lbrakk> \<lbrace> P \<rbrace> x \<lbrace> Q \<rbrace>,\<lbrace> E \<rbrace>;
         \<lbrace> P' \<rbrace> x \<lbrace> Q' \<rbrace>,\<lbrace> E' \<rbrace> \<rbrakk> \<Longrightarrow>
         \<lbrace> P and P' \<rbrace> x \<lbrace> \<lambda>r. (Q r) and (Q' r) \<rbrace>,\<lbrace>\<lambda>r. (E r) and (E' r) \<rbrace>"
  apply (clarsimp simp: validE_def valid_def split: sum.splits)
  apply (erule allE, erule (1) impE)+
  apply (erule (1) my_BallE)+
  apply clarsimp
  done

lemma condition_swap: "(condition C A B) = (condition (\<lambda>s. \<not> C s) B A)"
  apply (rule ext)
  apply (clarsimp split: condition_splits)
  done

lemma condition_fail_rhs: "(condition C X fail) = (state_assert C >>= (\<lambda>_. X))"
  apply (rule ext)
  apply (monad_eq simp: Bex_def)
  done

lemma condition_fail_lhs: "(condition C fail X) = (state_assert (\<lambda>s. \<not> C s) >>= (\<lambda>_. X))"
  apply (metis condition_fail_rhs condition_swap)
  done

lemma condition_bind_fail [simp]:
    "(condition C A B >>= (\<lambda>_. fail)) = condition C (A >>= (\<lambda>_. fail)) (B >>= (\<lambda>_. fail))"
  apply monad_eq
  apply blast
  done

lemma no_throw_Inr:
   "\<lbrakk> x \<in> fst (A s); no_throw P A; P s \<rbrakk> \<Longrightarrow> \<exists>y. fst x = Inr y"
  apply (clarsimp simp: no_throw_def' split: sum.splits)
  apply (erule allE, erule (1) impE, erule (1) my_BallE)
  apply clarsimp
  done

lemma no_throw_handleE': "no_throw \<top> A \<Longrightarrow> (A <handle2> B) = A"
  apply (rule monad_eqI)
    apply monad_eq
    apply (fastforce dest: no_throw_Inr)
   apply monad_eq
   apply (metis (lifting) fst_conv no_throw_Inr)
  apply monad_eq
  apply (fastforce dest: no_throw_Inr)
  done

lemma no_throw_handleE: "no_throw \<top> A \<Longrightarrow> (A <handle> B) = A"
  apply (unfold handleE_def)
  apply (subst no_throw_handleE')
   apply auto
  done

lemma whileLoopE_nothrow:
  "\<lbrakk> \<And>x. no_throw \<top> (B x) \<rbrakk> \<Longrightarrow> no_throw \<top> (whileLoopE C B x)"
  apply atomize
  apply (clarsimp simp: no_throw_def)
  apply (rule validE_whileLoopE [where I="\<lambda>_ _. True"])
    apply simp
   apply (rule validE_weaken)
      apply force
     apply simp
    apply simp
   apply simp
  apply simp
  done

lemma handleE'_nothrow_lhs:
  "\<lbrakk> no_throw \<top> L \<rbrakk> \<Longrightarrow> no_throw \<top> (L <handle2> R)"
  apply (clarsimp simp: no_throw_def)
  apply (rule handleE'_wp [rotated])
   apply assumption
  apply simp
  done

lemma handleE'_nothrow_rhs:
  "\<lbrakk> \<And>x. no_throw \<top> (R x) \<rbrakk> \<Longrightarrow> no_throw \<top> (L <handle2> R)"
  apply atomize
  apply (clarsimp simp: no_throw_def)
  apply (rule handleE'_wp)
   apply (erule allE)
   apply assumption
  apply (rule hoareE_TrueI)
  done

lemma handleE_nothrow_lhs:
  "\<lbrakk> no_throw \<top> L \<rbrakk> \<Longrightarrow> no_throw \<top> (L <handle> R)"
  by (metis handleE'_nothrow_lhs handleE_def)

lemma handleE_nothrow_rhs:
  "\<lbrakk> \<And>x. no_throw \<top> (R x) \<rbrakk> \<Longrightarrow> no_throw \<top> (L <handle> R)"
  by (metis no_throw_handleE_simple)

lemma condition_nothrow: "\<lbrakk> no_throw \<top> L; no_throw \<top> R \<rbrakk> \<Longrightarrow> no_throw \<top> (condition C L R)"
  apply (clarsimp simp: condition_def no_throw_def validE_def2)
  done

lemma empty_fail_guard [simp]: "empty_fail (state_assert G)"
  apply (clarsimp simp: state_assert_def assert_def empty_fail_def get_def return_def bind_def)
  done

lemma simple_bind_fail [simp]:
  "(state_assert X >>= (\<lambda>_. fail)) = fail"
  "(modify M >>= (\<lambda>_. fail)) = fail"
  "(return X >>= (\<lambda>_. fail)) = fail"
  "(gets X >>= (\<lambda>_. fail)) = fail"
  apply (auto intro!: bind_fail_propagates)
  done

lemma valid_case_prod:
  "\<lbrakk> \<And>x y. valid (P x y) (f x y) Q \<rbrakk> \<Longrightarrow> valid (case_prod P v) (case_prod (\<lambda>x y. f x y) v) Q"
  by (simp add: split_def)

lemma validE_case_prod:
  "\<lbrakk> \<And>x y. validE (P x y) (f x y) Q E \<rbrakk> \<Longrightarrow> validE (case_prod P v) (case_prod (\<lambda>x y. f x y) v) Q E"
  by (simp add: split_def)

lemma in_select [monad_eq]:
    "(rv, s') \<in> fst (select S s) = (s' = s \<and> rv \<in> S)"
  apply (clarsimp simp: select_def)
  apply blast
  done

lemma snd_select [monad_eq]:
    "\<not> snd (select S s)"
  by (clarsimp simp: select_def)

lemma bindE_handleE_join:
    "no_throw \<top> A \<Longrightarrow> (A >>=E (\<lambda>x. (B x) <handle> C)) = ((A >>=E B <handle> C))"
  apply (monad_eq simp: Bex_def Ball_def no_throw_def')
  apply blast
  done

lemma snd_put [monad_eq]:
    "\<not> snd (put t s)"
  by (clarsimp simp: put_def)

lemma snd_modify [monad_eq]:
    "\<not> snd (modify t s)"
  by (clarsimp simp: modify_def put_def get_def bind_def)

lemma no_fail_False [simp]:
  "no_fail (\<lambda>_. False) X"
  by (clarsimp simp: no_fail_def)

lemma valid_pre_satisfies_post:
  "\<lbrakk> \<And>s r' s'. P s \<Longrightarrow> Q r' s' \<rbrakk> \<Longrightarrow> \<lbrace> P \<rbrace> m \<lbrace> Q \<rbrace>"
  by (clarsimp simp: valid_def)

lemma validE_pre_satisfies_post:
  "\<lbrakk> \<And>s r' s'. P s \<Longrightarrow> Q r' s'; \<And>s r' s'. P s \<Longrightarrow> R r' s' \<rbrakk> \<Longrightarrow> \<lbrace> P \<rbrace> m \<lbrace> Q \<rbrace>,\<lbrace> R \<rbrace>"
  by (clarsimp simp: validE_def2 split: sum.splits)

lemma snd_gets_the  [monad_eq]:
  "snd (gets_the X s) = (X s = None)"
  by (monad_eq simp: gets_the_def gets_def get_def)

lemma liftE_K_bind: "liftE ((K_bind (\<lambda>s. A s)) x) = K_bind (liftE (\<lambda>s. A s)) x"
  by clarsimp

lemma hoare_assume_preNF:
  "(\<And>s. P s \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>!) \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>!"
  by (metis validNF_alt_def)

lemma bexEI: "\<lbrakk>\<exists>x\<in>S. Q x; \<And>x. \<lbrakk>x \<in> S; Q x\<rbrakk> \<Longrightarrow> P x\<rbrakk> \<Longrightarrow> \<exists>x\<in>S. P x" by blast

lemma monad_eq_split:
  assumes "\<And>r s. Q r s \<Longrightarrow> f r s = f' r s"
          "\<lbrace>P\<rbrace> g \<lbrace>\<lambda>r s. Q r s\<rbrace>"
          "P s"
  shows "(g >>= f) s = (g >>= f') s"
proof -
  have pre: "\<And>rv s'. \<lbrakk>(rv, s') \<in> fst (g s)\<rbrakk> \<Longrightarrow> f rv s' = f' rv s'"
    using assms unfolding valid_def
    by (erule_tac x=s in allE) auto
  show ?thesis
  apply (simp add: bind_def image_def)
  apply (intro conjI)
   apply (rule set_eqI)
   apply (clarsimp simp: Union_eq)
   apply (rule iffI; elim exEI conjE; simp; elim exEI bexEI; clarsimp simp: pre)
  apply (rule iffI; cases "snd (g s)"; simp; elim exEI bexEI; clarsimp simp: pre)
  done
qed

lemma monad_eq_split2:
assumes eq: " g' s = g s"
assumes tail:"\<And>r s. Q r s \<Longrightarrow> f r s = f' r s"
and hoare:   "\<lbrace>P\<rbrace>g\<lbrace>\<lambda>r s. Q r s\<rbrace>" "P s"
shows "(g>>=f) s = (g'>>= f') s"
proof -
have pre: "\<And>aa bb. \<lbrakk>(aa, bb) \<in> fst (g s)\<rbrakk> \<Longrightarrow> Q aa bb"
  using hoare by (auto simp: valid_def)
show ?thesis
  apply (simp add:bind_def eq split_def image_def)
  apply (rule conjI)
   apply (rule set_eqI)
   apply (clarsimp simp:Union_eq)
   apply (metis pre surjective_pairing tail)
  apply (metis pre surjective_pairing tail)
  done
qed

lemma monad_eq_split_tail:
  "\<lbrakk>f = g;a s = b s\<rbrakk> \<Longrightarrow> (a >>= f) s = ((b >>= g) s)"
  by (simp add:bind_def)

lemma double_gets_drop_regets:
  "(do x \<leftarrow> gets f;
       xa \<leftarrow> gets f;
       m xa x
    od) =
   (do xa \<leftarrow> gets f;
       m xa xa
    od)"
  by (simp add: gets_def get_def bind_def return_def)

definition monad_commute where
  "monad_commute P a b \<equiv>
  (\<forall>s. (P s \<longrightarrow> ((do x\<leftarrow>a;y\<leftarrow>b; return (x, y) od) s) = ((do y\<leftarrow>b;x\<leftarrow>a; return (x, y) od) s)))"


lemma monad_eq:
  "a s = b s \<Longrightarrow>  (a >>= g) s = (b >>= g) s"
  by (auto simp:bind_def)

lemma monad_commute_simple:
  "\<lbrakk>monad_commute P a b;P s\<rbrakk> \<Longrightarrow> ((do x\<leftarrow>a;y\<leftarrow>b; g x y od) s) = ((do y\<leftarrow>b;x\<leftarrow>a; g x y od) s)"
  apply (clarsimp simp:monad_commute_def)
  apply (drule spec)
  apply (erule(1) impE)
  apply (drule_tac g = "(\<lambda>t. g (fst t) (snd t))" in monad_eq)
  apply (simp add:bind_assoc)
  done

lemma commute_commute:
  "monad_commute P f h \<Longrightarrow> monad_commute P h f"
  apply (simp (no_asm) add: monad_commute_def)
  apply (clarsimp)
  apply (erule monad_commute_simple[symmetric])
  apply simp
  done

lemma assert_commute: "monad_commute (K G) (assert G) f"
  by (clarsimp simp:assert_def monad_commute_def)

lemma cond_fail_commute: "monad_commute (K (\<not>G)) (when G fail) f"
  by (clarsimp simp:when_def fail_def monad_commute_def)

lemma return_commute: "monad_commute \<top> (return a) f"
  by (clarsimp simp: return_def bind_def monad_commute_def)

lemma monad_commute_guard_imp:
  "\<lbrakk>monad_commute P f h; \<And>s. Q s \<Longrightarrow> P s \<rbrakk> \<Longrightarrow> monad_commute Q f h"
  by (clarsimp simp:monad_commute_def)

lemma monad_commute_split:
  "\<lbrakk>\<And>r. monad_commute (Q r) f (g r); monad_commute P f h;
         \<lbrace>P'\<rbrace> h \<lbrace>\<lambda>r. Q r\<rbrace>\<rbrakk>
   \<Longrightarrow> monad_commute (P and P') f (h>>=g)"
  apply (simp (no_asm) add:monad_commute_def)
   apply (clarsimp simp:bind_assoc)
   apply (subst monad_commute_simple)
    apply simp+
   apply (rule_tac Q = "(\<lambda>x. Q x)" in monad_eq_split)
   apply (subst monad_commute_simple[where a = f])
    apply assumption
    apply simp+
  done

lemma monad_commute_get:
  assumes hf: "\<And>P. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r. P\<rbrace>"
  and hg: "\<And>P. \<lbrace>P\<rbrace> g \<lbrace>\<lambda>r. P\<rbrace>"
  and eptyf: "empty_fail f" "empty_fail g"
  shows "monad_commute \<top> f g"
proof -
  have fsame: "\<And>a b s. (a,b) \<in> fst (f s) \<Longrightarrow> b = s"
    by (drule use_valid[OF _ hf],auto)
  have gsame: "\<And>a b s. (a,b) \<in> fst (g s) \<Longrightarrow> b = s"
    by (drule use_valid[OF _ hg],auto)
  note ef = empty_fail_not_snd[OF _ eptyf(1)]
  note eg = empty_fail_not_snd[OF _ eptyf(2)]
  show ?thesis
  apply (simp add:monad_commute_def)
  apply (clarsimp simp:bind_def split_def return_def)
  apply (intro conjI)
   apply (rule set_eqI)
    apply (rule iffI)
    apply (clarsimp simp:Union_eq dest!: singletonD)
    apply (frule fsame)
    apply clarsimp
    apply (frule gsame)
    apply (metis fst_conv snd_conv)
   apply (clarsimp simp:Union_eq dest!: singletonD)
   apply (frule gsame)
   apply clarsimp
   apply (frule fsame)
   apply clarsimp
   apply (metis fst_conv snd_conv)
  apply (rule iffI)
   apply (erule disjE)
    apply (clarsimp simp:image_def)
    apply (metis fsame)
   apply (clarsimp simp:image_def)
   apply (drule eg)
   apply clarsimp
   apply (rule bexI [rotated], assumption)
   apply (frule gsame)
   apply clarsimp
  apply (erule disjE)
   apply (clarsimp simp:image_def dest!:gsame)
  apply (clarsimp simp:image_def)
  apply (drule ef)
  apply clarsimp
  apply (frule fsame)
  apply (erule bexI[rotated])
  apply simp
  done
qed

lemma mapM_x_commute:
assumes commute:
  "\<And>r. monad_commute (P r) a (b r)"
and   single:
  "\<And>r x. \<lbrace>P r and K (f r \<noteq> f x) and P x\<rbrace> b x \<lbrace>\<lambda>v. P r \<rbrace>"
shows
  "monad_commute (\<lambda>s. (distinct (map f list)) \<and> (\<forall>r\<in> set list. P r s)) a (mapM_x b list)"
  apply (induct list)
   apply (clarsimp simp:mapM_x_Nil return_def bind_def monad_commute_def)
  apply (clarsimp simp:mapM_x_Cons)
  apply (rule monad_commute_guard_imp)
   apply (rule monad_commute_split)
     apply assumption
    apply (rule monad_commute_guard_imp[OF commute])
   apply assumption
   apply (wp hoare_vcg_ball_lift)
   apply (rule single)
  apply (clarsimp simp: image_def)
  apply auto
  done

lemma commute_name_pre_state:
assumes "\<And>s. P s \<Longrightarrow> monad_commute ((=) s) f g"
shows "monad_commute P f g"
  using assms
  by (clarsimp simp:monad_commute_def)

lemma commute_rewrite:
assumes rewrite: "\<And>s. Q s \<Longrightarrow> f s = t s"
  and   hold  : "\<lbrace>P\<rbrace> g \<lbrace>\<lambda>x. Q\<rbrace>"
 shows  "monad_commute R t g \<Longrightarrow> monad_commute (P and Q and R) f g"
   apply (clarsimp simp:monad_commute_def bind_def split_def return_def)
   apply (drule_tac x = s in spec)
   apply (clarsimp simp:rewrite[symmetric])
    apply (intro conjI)
     apply (rule set_eqI)
     apply (rule iffI)
      apply clarsimp
      apply (rule bexI[rotated],assumption)
      apply (subst rewrite)
      apply (rule use_valid[OF _ hold])
     apply simp+
    apply (erule bexI[rotated],simp)
   apply clarsimp
   apply (rule bexI[rotated],assumption)
   apply (subst rewrite[symmetric])
    apply (rule use_valid[OF _ hold])
   apply simp+
   apply (erule bexI[rotated],simp)
  apply (intro iffI)
   apply clarsimp
   apply (rule bexI[rotated],assumption)
   apply simp
   apply (subst rewrite)
    apply (erule(1) use_valid[OF _ hold])
   apply simp
  apply (clarsimp)
  apply (drule bspec,assumption)
  apply clarsimp
  apply (metis rewrite use_valid[OF _ hold])
  done


lemma commute_grab_asm:
  "(F \<Longrightarrow> monad_commute P f g) \<Longrightarrow> (monad_commute (P and (K F)) f g)"
  by (clarsimp simp: monad_commute_def)

end
