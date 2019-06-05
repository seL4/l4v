(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory HaskellLemmaBucket
imports
  HaskellLib_H
  NonDetMonadLemmaBucket
begin

lemma map_bits_to_bl:
  "map ((!!) x) [0..<size x] = reverse (to_bl x)"
  by (simp add: map_bits_rev_to_bl)

lemma not_orList_is_replicate:
  "\<not> orList ls \<Longrightarrow> ls = replicate (length ls) False"
proof (induct ls rule: rev_induct)
  case Nil thus ?case unfolding orList_def by simp
next
  case (snoc l ls)

  from snoc.prems have ol: "\<not> orList ls" and nl: "\<not> l" unfolding orList_def by auto
  have "ls = replicate (length ls) False" by (rule snoc.hyps [OF ol])
  thus ?case
    by (rule ssubst) (simp add: nl replicate_app_Cons_same [where xs = "[]", simplified])
qed

lemma andList_Cons:
  assumes al: "andList $ map P (y # ys)"
  shows   "P y"
  using al unfolding andList_def
  by simp (induct rule: rev_induct, simp+)

lemma andList_mapE:
  assumes al: "andList $ map P xs"
  and     xv: "x \<in> set xs"
  shows   "P x"
  using al xv
proof (induct xs arbitrary: x rule: rev_induct)
  case Nil thus ?case by simp
next
  case (snoc y ys)

  show ?case
  proof (cases "x = y")
    case True
    with snoc.prems show ?thesis by (simp add: andList_def)
  next
    case False
    with snoc.prems show ?thesis
      by (auto simp: andList_def intro!: snoc.hyps)
  qed
qed

lemma andList_to_aligned:
  assumes al: "andList $ map (\<lambda>x. x && mask pageBits = 0) xs"
  and     xv: "x \<in> set xs"
  shows   "is_aligned x pageBits"
proof (subst is_aligned_mask)
  from al show "x && mask pageBits = 0" by (rule andList_mapE) fact
qed

(* minimum/maximum *)

lemma maximum_ge: "x \<in> set b \<Longrightarrow> x \<le> maximum b"
  unfolding maximum_def by (auto intro: Max_ge)

lemma less_minimum_not_in:
  "\<lbrakk> ls \<noteq> []; x < minimum ls \<rbrakk> \<Longrightarrow> x \<notin> set ls"
  unfolding minimum_def by auto

lemma minimum_le_member:
  "\<lbrakk> x \<in> set ls; ls \<noteq> []\<rbrakk> \<Longrightarrow> minimum ls \<le> x"
  unfolding minimum_def
  apply (rule Min_le)
    apply simp
   apply simp
  done

lemma minimum_map_distrib:
  fixes f :: "('a :: linorder) \<Rightarrow> 'a" and ls :: "'a list"
  assumes minf: "\<And>x y. \<lbrakk>x \<in> set ls; y \<in> set ls\<rbrakk> \<Longrightarrow> min (f x) (f y) = f (min x y)"
  and      lsn: "ls \<noteq> []"
  shows "minimum (map f ls) = f (minimum ls)"
  unfolding minimum_def
  apply simp
  apply (rule Min_image_distrib)
    apply (erule (1) minf)
   apply simp
  apply (simp add: lsn)
  done

lemma minimum_enum_upto:
  fixes x :: "'a::len word"
  assumes le: "x \<le> y"
  shows   "minimum [x .e. y] = x"
  unfolding minimum_def using le by (auto intro!: MinI)

lemma break_subsetsD:
  "break f xs = (ys, zs) \<Longrightarrow> set ys \<subseteq> set xs \<and> set zs \<subseteq> set xs"
  apply (induct xs arbitrary: ys zs)
   apply simp
  apply (case_tac "break f xs")
  apply (elim meta_allE, drule(1) meta_mp)
  apply (fastforce simp: split_def split: if_split_asm)
  done

lemma distinct_prop_breakD:
  "\<lbrakk> distinct_prop P xs; break f xs = (ys, zs) \<rbrakk>
    \<Longrightarrow> \<forall>y \<in> set ys. \<forall>z \<in> set zs. P y z"
  apply (induct xs arbitrary: ys zs)
   apply simp
  apply (simp add: split_def split: if_split_asm)
  apply (case_tac "break f xs")
  apply (elim meta_allE, drule(1) meta_mp)
  apply (frule break_subsetsD)
  apply fastforce
  done

lemma stateAssert_wp:
  "\<lbrace>\<lambda>s. P s \<longrightarrow> Q () s\<rbrace> stateAssert P e \<lbrace>Q\<rbrace>"
  by (clarsimp simp: stateAssert_def) wp

lemma haskell_assert_wp:
  "\<lbrace>\<lambda>s. Q \<longrightarrow> P s\<rbrace> haskell_assert Q xs \<lbrace>\<lambda>_. P\<rbrace>"
  by simp wp

lemma init_append_last:
  "xs \<noteq> [] \<Longrightarrow> init xs @ [last xs] = xs"
  apply (induct xs rule: rev_induct)
   apply simp
  apply (simp add: init_def)
  done

lemma init_Snoc[simp]:
  "init (xs @ [x]) = xs"
  by (induct xs) (auto simp: init_def)

lemma init_upto_enum_upt[simp]:
  "init [0.e.n] = [0..<n]"
  by (induct n) (auto simp: init_def)

lemma no_fail_stateAssert:
  "no_fail P (stateAssert P xs)"
  apply (simp add: stateAssert_def)
  apply (rule no_fail_pre, wp no_fail_bind)
  apply simp
  done

lemma empty_fail_stateAssert:
  "empty_fail (stateAssert P s)"
  by (simp add: stateAssert_def assert_def empty_fail_get)

lemma haskell_fail_wp:
  "\<lbrace>\<top>\<rbrace> haskell_fail x \<lbrace>P\<rbrace>"
  by simp

lemma no_fail_haskell_fail [simp, wp]:
  "no_fail \<bottom> (haskell_fail xs)"
  by simp

lemma in_assocs_is_fun:
  "(x \<in> set (assocs f)) = (f (fst x) = snd x)"
  by (cases x) (auto simp add: assocs_def)

lemma fun_is_in_assocs:
  "(f x = y) = ((x,y) \<in> set (assocs f))"
  by (simp add: in_assocs_is_fun)

lemma empty_set_is_null:
  "(set xs = {}) = null xs"
  by (clarsimp simp: null_def)

lemma assert_into_when:
  "(assert P) = (when (\<not> P) (haskell_fail []))"
  by (simp add: assert_def when_def)

lemma const_apply:
  "const x y = x"
  by (simp add: const_def)

lemma const_None_empty:
  "const None = Map.empty"
  by (rule ext, simp add: const_apply)

lemma headM_tailM_Cons:
  "headM (x # xs) = return x"
  "tailM (x # xs) = return xs"
  by (simp add: headM_def tailM_def)+

lemma replicateM_mapM:
  "replicateM n f = mapM (\<lambda>x. f) (replicate n ())"
  by (simp add: replicateM_def mapM_def)

lemma orList_False:
  "(\<not> orList bs) = (set bs \<subseteq> {False})"
  apply (induct bs)
  apply (simp_all add: orList_def foldl_True)
  apply (case_tac a)
  apply (simp_all add: orList_def foldl_True)
  done

lemma Cons_eq_tails:
  "((xs # xxs) = tails ys) = (ys = xs \<and> xxs = tl (tails ys))"
  by (case_tac ys, auto)

lemma findM_on_outcome':
  assumes x: "\<And>x xs. \<lbrace>\<lambda>s. Q None s \<and> x \<in> fn s \<and> set xs \<subseteq> fn s\<rbrace> f x
                     \<lbrace>\<lambda>rv s. (rv \<longrightarrow> Q (Some x) s) \<and> (\<not> rv \<longrightarrow> Q None s \<and> set xs \<subseteq> fn s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. Q None s \<and> set xs \<subseteq> fn s\<rbrace> findM f xs \<lbrace>Q\<rbrace>"
  apply (induct xs)
   apply (simp, wp)
  apply (simp, wp)
   apply (rule x)
  apply simp
  done


lemma findM_on_outcome:
  assumes x: "\<And>x ys. x \<in> set xs \<Longrightarrow> \<lbrace>Q None and I\<rbrace> f x \<lbrace>\<lambda>rv s. (rv \<longrightarrow> Q (Some x) s) \<and> (\<not> rv \<longrightarrow> Q None s \<and> I s)\<rbrace>"
  shows      "\<lbrace>Q None and I\<rbrace> findM f xs \<lbrace>Q\<rbrace>"
  apply (rule hoare_vcg_precond_imp)
   apply (rule findM_on_outcome' [where fn="\<lambda>s. if I s then set xs else {}"])
   apply (case_tac "x \<notin> set xs")
    apply simp
   apply (simp cong: rev_conj_cong)
   apply (case_tac "\<not> set xsa \<subseteq> set xs")
    apply simp
   apply simp
   apply (rule hoare_vcg_precond_imp)
    apply (rule hoare_post_imp [OF _ x])
     apply clarsimp
    apply assumption
   apply simp
  apply simp
  done

lemma in_set_tailsD: "xs \<in> set (tails ys) \<Longrightarrow> set xs \<subseteq> set ys"
  apply (induct ys)
   apply simp
  apply simp
  apply (erule disjE)
   apply simp
  apply simp
  apply blast
  done

lemma notin_set_tails_set:
  "x \<notin> set xs \<Longrightarrow> \<forall>xs' \<in> set (tails xs). \<forall>x' \<in> set xs'. x \<noteq> x'"
  by (fastforce dest!: in_set_tailsD)

lemma set_tails_set: "(set (tails v) \<subseteq> {x. set x \<subseteq> S}) = (set v \<subseteq> S)"
  apply (induct v, simp_all)
  done

lemma filter_assocs_Cons:
  fixes v :: "('a :: len) word" shows
  "\<lbrakk> f (v, g v); \<forall>x < v. \<not> f (x, g x) \<rbrakk> \<Longrightarrow>
     filter f (assocs g) = (v, g v) # tl (filter f (assocs g))"
  apply (simp add: assocs_def)
  apply (cut_tac v=v in enum_word_div)
  apply clarsimp
  apply (subst map_cong [OF _ refl], assumption)+
  apply (simp(no_asm))
  apply simp
  done

lemma snd_stateAssert_after:
  "\<not> snd ((do _ \<leftarrow> f; stateAssert R vs od) s) \<Longrightarrow>
  \<not>snd (f s) \<and> (\<forall>(rv, s') \<in> fst (f s). R s')"
  apply (clarsimp simp: bind_def stateAssert_def get_def assert_def
      return_def fail_def split_def split: if_split_asm)
  done

lemma oblivious_stateAssert [simp]:
  "oblivious f (stateAssert g xs) = (\<forall>s. g (f s) = g s)"
  apply (simp add: oblivious_def stateAssert_def exec_get
                   assert_def return_def fail_def split: if_split)
  apply auto
  done

lemma stateAssert_def2:
  "stateAssert f xs = do v \<leftarrow> gets f; if v then return () else fail od"
  by (simp add: stateAssert_def gets_def assert_def)

lemma findM_is_mapME:
  "(findM f xs >>= g)
   = liftM (\<lambda>_. ())
      (doE ys \<leftarrow> mapME_x (\<lambda>x. do v \<leftarrow> f x;
                             if v then do g (Some x); throwError () od
                             else returnOk () od) xs;
              liftE (g None) odE)"
  apply (induct xs)
   apply (simp add: mapME_x_def sequenceE_x_def liftM_def returnOk_bind)
   apply (simp add: liftE_def)
  apply (simp add: mapME_x_Cons bindE_assoc liftE_bindE[symmetric]
                   liftM_def cong: if_cong)
  apply (simp add: liftE_bindE bind_assoc)
  apply (rule bind_cong[OF refl])
  apply (simp add: bindE_assoc split: if_split)
  apply (simp add: liftE_bindE bind_assoc throwError_bind)
  done

text \<open>Some word equalities can be solved by considering the
problem bitwise.

This is proven for all n < len_of TYPE ('a), which is different to
running word_bitwise and expanding into an explicit list of bits.
\<close>

lemmas word_eqI_solve_simps = word_and_le1 word_or_zero le_word_or2
  shiftL_nat word_FF_is_mask word_1FF_is_mask neg_mask_bang nth_ucast
  linorder_not_less word_size minus_one_norm word_ops_nth_size
  is_aligned_nth nth_w2p nth_shiftl nth_shiftr conj_comms
  less_2p_is_upper_bits_unset

method word_eqI_solve = solves \<open>rule word_eqI;
  clarsimp simp: word_eqI_solve_simps;
  (eval_int_nat; clarsimp simp: word_eqI_solve_simps)?;
  fastforce simp: mask_def
\<close>

add_try_method word_eqI_solve

end
