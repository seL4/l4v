(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Monadic functions over lists: sequence, mapM, filter, etc
   Definitions, equations, Hoare logic and no_fail/empty_fail setup. *)

theory Monad_Lists
  imports
    Monads.NonDetMonadVCG
begin

lemma mapME_Cons:
  "mapME m (x # xs) = (doE y \<leftarrow> m x; ys \<leftarrow> (mapME m xs); returnOk (y # ys) odE)"
  by (simp add: mapME_def sequenceE_def Let_def)

lemma mapME_Nil : "mapME f [] = returnOk []"
  unfolding mapME_def by (simp add: sequenceE_def)

lemmas mapME_simps = mapME_Nil mapME_Cons

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

lemma sequence_x_Cons: "\<And>x xs. sequence_x (x # xs) = (x >>= (\<lambda>_. sequence_x xs))"
  by (simp add: sequence_x_def)

lemma mapM_Cons: "mapM m (x # xs) = (do y \<leftarrow> m x; ys \<leftarrow> (mapM m xs); return (y # ys) od)"
  by (simp add: mapM_def sequence_def Let_def)

lemma mapM_Nil:
  "mapM m [] = return []"
  by (simp add: mapM_def sequence_def)

lemmas mapM_simps = mapM_Nil mapM_Cons

lemma zipWithM_x_mapM:
 "zipWithM_x f as bs = (mapM (case_prod f) (zip as bs) >>= (\<lambda>_. return ()))"
  apply (simp add: zipWithM_x_def zipWith_def)
  apply (induct ("zip as bs"))
   apply (simp add: sequence_x_def mapM_def sequence_def)
  apply (simp add: sequence_x_Cons mapM_Cons bind_assoc)
  done

lemma mapM_x_mapM:
  "mapM_x m l = (mapM m l >>= (\<lambda>x. return ()))"
  apply (simp add: mapM_x_def sequence_x_def mapM_def sequence_def)
  apply (induct l, simp_all add: Let_def bind_assoc)
  done

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

lemma mapME_x_map_simp:
  "mapME_x m (map f xs) = mapME_x (m o f) xs"
  by (simp add: mapME_x_def sequenceE_x_def)

lemma mapM_return:
  "mapM (\<lambda>x. return (f x)) xs = return (map f xs)"
  apply (induct xs)
   apply (simp add: mapM_def sequence_def)
  apply (simp add: mapM_Cons)
  done

lemma liftM_return [simp]:
  "liftM f (return x) = return (f x)"
  by (simp add: liftM_def)

lemma mapM_x_return :
  "mapM_x (\<lambda>_. return v) xs = return v"
  by (induct xs) (auto simp: mapM_x_Nil mapM_x_Cons)

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

lemma mapM_x_append: (* FIXME: remove extra return, fix proofs *)
  "mapM_x f (xs @ ys) =
  (do x \<leftarrow> mapM_x f xs;
      y \<leftarrow> mapM_x f ys;
      return ()
   od)"
  by (simp add: mapM_x_mapM mapM_append bind_assoc)

(* FIXME: duplicate, but mapM_x_append has an extra useless return *)
lemma mapM_x_append2:
  "mapM_x f (xs @ ys) = do mapM_x f xs; mapM_x f ys od"
  apply (simp add: mapM_x_def sequence_x_def)
  apply (induct xs)
   apply simp
  apply (simp add: bind_assoc)
  done

lemma mapM_singleton:
  "mapM f [x] = do r \<leftarrow> f x; return [r] od"
  by (simp add: mapM_def sequence_def)

lemma mapM_x_singleton:
  "mapM_x f [x] = f x"
  by (simp add: mapM_x_mapM mapM_singleton)

lemma mapME_x_sequenceE:
  "mapME_x f xs \<equiv> doE _ \<leftarrow> sequenceE (map f xs); returnOk () odE"
  apply (induct xs, simp_all add: mapME_x_def sequenceE_def sequenceE_x_def)
  apply (simp add: Let_def bindE_assoc)
  done

lemma sequenceE_Cons:
  "sequenceE (x # xs) = (doE v \<leftarrow> x; vs \<leftarrow> sequenceE xs; returnOk (v # vs) odE)"
  by (simp add: sequenceE_def Let_def)

lemma zipWithM_Nil [simp]:
  "zipWithM f xs [] = return []"
  by (simp add: zipWithM_def zipWith_def sequence_def)

lemma zipWithM_One:
  "zipWithM f (x#xs) [a] = (do z \<leftarrow> f x a; return [z] od)"
  by (simp add: zipWithM_def zipWith_def sequence_def)

lemma zipWithM_x_Nil[simp]:
  "zipWithM_x f xs [] = return ()"
  by (simp add: zipWithM_x_def zipWith_def sequence_x_def)

lemma zipWithM_x_One:
  "zipWithM_x f (x#xs) [a] = f x a"
  by (simp add: zipWithM_x_def zipWith_def sequence_x_def)

lemma mapM_last_Cons:
  "\<lbrakk> xs = [] \<Longrightarrow> g v = y;
     xs \<noteq> [] \<Longrightarrow> do x \<leftarrow> f (last xs); return (g x) od
             = do x \<leftarrow> f (last xs); return y od \<rbrakk> \<Longrightarrow>
   do ys \<leftarrow> mapM f xs; return (g (last (v # ys))) od = do mapM_x f xs; return y od"
  apply (cases "xs = []")
   apply (simp add: mapM_x_Nil mapM_Nil)
  apply (simp add: mapM_x_mapM)
  apply (subst append_butlast_last_id[symmetric], assumption,
         subst mapM_append)+
  apply (simp add: bind_assoc mapM_Cons mapM_Nil)
  done

lemma map_length_cong:
  "\<lbrakk> length xs = length ys; \<And>x y. (x, y) \<in> set (zip xs ys) \<Longrightarrow> f x = g y \<rbrakk>
     \<Longrightarrow> map f xs = map g ys"
  apply atomize
  apply (erule rev_mp, erule list_induct2)
   apply auto
  done

lemma mapM_length_cong:
  "\<lbrakk> length xs = length ys; \<And>x y. (x, y) \<in> set (zip xs ys) \<Longrightarrow> f x = g y \<rbrakk>
   \<Longrightarrow> mapM f xs = mapM g ys"
  by (simp add: mapM_def map_length_cong)

(* FIXME: duplicate *)
lemma zipWithM_mapM:
  "zipWithM f xs ys = mapM (case_prod f) (zip xs ys)"
  by (simp add: zipWithM_def zipWith_def mapM_def)

lemma zip_take_triv2:
  "length as \<le> n \<Longrightarrow> zip as (take n bs) = zip as bs"
  apply (induct as arbitrary: n bs; simp)
  apply (case_tac n; simp)
  apply (case_tac bs; simp)
  done

lemma zipWithM_If_cut:
  "zipWithM (\<lambda>a b. if a < n then f a b else g a b) [0 ..< m] xs
     = do ys \<leftarrow> zipWithM f [0 ..< min n m] xs;
          zs \<leftarrow> zipWithM g [n ..< m] (drop n xs);
          return (ys @ zs)
       od"
  apply (cases "n < m")
   apply (cut_tac i=0 and j=n and k="m - n" in upt_add_eq_append)
    apply simp
   apply (simp add: zipWithM_mapM)
   apply (simp add: zip_append1 mapM_append zip_take_triv2 split_def)
   apply (intro bind_cong bind_apply_cong refl mapM_length_cong
                fun_cong[OF mapM_length_cong])
    apply (clarsimp simp: set_zip)
   apply (clarsimp simp: set_zip)
  apply (simp add: zipWithM_mapM mapM_Nil)
  apply (intro mapM_length_cong refl)
  apply (clarsimp simp: set_zip)
  done

lemma mapM_liftM_const:
  "mapM (\<lambda>x. liftM (\<lambda>y. f x) (g x)) xs = liftM (\<lambda>ys. map f xs) (mapM g xs)"
  apply (induct xs)
   apply (simp add: mapM_Nil)
  apply (simp add: mapM_Cons)
  apply (simp add: liftM_def bind_assoc)
  done

lemma mapM_discarded:
  "mapM f xs >>= (\<lambda>ys. g) = mapM_x f xs >>= (\<lambda>_. g)"
  by (simp add: mapM_x_mapM)

lemma mapM_x_map:
  "mapM_x f (map g xs) = mapM_x (\<lambda>x. f (g x)) xs"
  by (simp add: mapM_x_def o_def)

lemma filterM_append:
  "filterM f (xs @ ys) = do
     xs' \<leftarrow> filterM f xs;
     ys' \<leftarrow> filterM f ys;
     return (xs' @ ys')
   od"
  apply (induct xs)
   apply simp
  apply (simp add: bind_assoc)
  apply (rule ext bind_apply_cong [OF refl])+
  apply simp
  done

lemma filterM_mapM:
  "filterM f xs = do
     ys \<leftarrow> mapM (\<lambda>x. do v \<leftarrow> f x; return (x, v) od) xs;
     return (map fst (filter snd ys))
   od"
  apply (induct xs)
   apply (simp add: mapM_def sequence_def)
  apply (simp add: mapM_Cons bind_assoc)
  apply (rule bind_cong [OF refl] bind_apply_cong[OF refl])+
  apply simp
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

lemma filterM_voodoo:
  "\<forall>ys. P ys (do zs \<leftarrow> filterM m xs; return (ys @ zs) od)
       \<Longrightarrow> P [] (filterM m xs)"
  by (drule spec[where x=Nil], simp)

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

lemma mapM_x_split_append:
  "mapM_x f xs = do _ \<leftarrow> mapM_x f (take n xs); mapM_x f (drop n xs) od"
  using mapM_x_append[where f=f and xs="take n xs" and ys="drop n xs"]
  by simp

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

lemma mapM_x_inv_wp3:
  fixes m :: "'b \<Rightarrow> ('a, unit) nondet_monad"
  assumes hr: "\<And>a as bs. xs = as @ [a] @ bs \<Longrightarrow>
     \<lbrace>\<lambda>s. I s \<and> V as s\<rbrace> m a \<lbrace>\<lambda>r s. I s \<and> V (as @ [a]) s\<rbrace>"
  shows   "\<lbrace>\<lambda>s. I s \<and> V [] s\<rbrace> mapM_x m xs \<lbrace>\<lambda>rv s. I s \<and> V xs s\<rbrace>"
  using hr
proof (induct xs rule: rev_induct)
  case Nil thus ?case
    by (simp add: mapM_x_Nil)
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

lemma no_fail_mapM:
  "\<forall>x. no_fail \<top> (f x) \<Longrightarrow> no_fail \<top> (mapM f xs)"
  apply (induct xs)
   apply (simp add: mapM_def sequence_def)
  apply (simp add: mapM_Cons)
  apply (wp|fastforce)+
  done

lemma filterM_preserved:
  "\<lbrakk> \<And>x. x \<in> set xs \<Longrightarrow> \<lbrace>P\<rbrace> m x \<lbrace>\<lambda>rv. P\<rbrace> \<rbrakk>
      \<Longrightarrow> \<lbrace>P\<rbrace> filterM m xs \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (induct xs)
   apply (wp | simp | erule meta_mp | drule meta_spec)+
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

lemma mapM_wp':
  assumes x: "\<And>x. x \<in> set xs \<Longrightarrow> \<lbrace>P\<rbrace> f x \<lbrace>\<lambda>rv. P\<rbrace>"
  shows "\<lbrace>P\<rbrace> mapM f xs \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (rule mapM_wp)
   apply (erule x)
  apply simp
  done

lemma mapM_set:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> \<lbrace>P\<rbrace> f x \<lbrace>\<lambda>_. P\<rbrace>"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> \<lbrace>P\<rbrace> f x \<lbrace>\<lambda>_. Q x\<rbrace>"
  assumes "\<And>x y. \<lbrakk> x \<in> set xs; y \<in> set xs \<rbrakk> \<Longrightarrow> \<lbrace>P and Q y\<rbrace> f x \<lbrace>\<lambda>_. Q y\<rbrace>"
  shows "\<lbrace>P\<rbrace> mapM f xs \<lbrace>\<lambda>_ s. \<forall>x \<in> set xs. Q x s\<rbrace>"
using assms
proof (induct xs)
  case Nil show ?case
    by (simp add: mapM_def sequence_def) wp
next
  case (Cons y ys)
  have PQ_inv: "\<And>x. x \<in> set ys \<Longrightarrow> \<lbrace>P and Q y\<rbrace> f x \<lbrace>\<lambda>_. P and Q y\<rbrace>"
    by (wpsimp wp: Cons)
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

lemma mapM_set_inv:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> \<lbrace>P\<rbrace> f x \<lbrace>\<lambda>_. P\<rbrace>"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> \<lbrace>P\<rbrace> f x \<lbrace>\<lambda>_. Q x\<rbrace>"
  assumes "\<And>x y. \<lbrakk> x \<in> set xs; y \<in> set xs \<rbrakk> \<Longrightarrow> \<lbrace>P and Q y\<rbrace> f x \<lbrace>\<lambda>_. Q y\<rbrace>"
  shows "\<lbrace>P\<rbrace> mapM f xs \<lbrace>\<lambda>_ s. P s \<and> (\<forall>x \<in> set xs. Q x s)\<rbrace>"
  apply (rule hoare_weaken_pre, rule hoare_vcg_conj_lift)
    apply (rule mapM_wp', erule assms)
   apply (rule mapM_set; rule assms; assumption)
  apply simp
  done

lemma mapM_x_wp:
  assumes x: "\<And>x. x \<in> S \<Longrightarrow> \<lbrace>P\<rbrace> f x \<lbrace>\<lambda>rv. P\<rbrace>"
  shows      "set xs \<subseteq> S \<Longrightarrow> \<lbrace>P\<rbrace> mapM_x f xs \<lbrace>\<lambda>rv. P\<rbrace>"
  by (subst mapM_x_mapM) (wp mapM_wp x)

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


lemma empty_fail_mapM_x [simp]:
  "(\<And>x. empty_fail (a x)) \<Longrightarrow> empty_fail (mapM_x a xs)"
  apply (induct_tac xs)
   apply (clarsimp simp: mapM_x_Nil)
  apply (clarsimp simp: mapM_x_Cons)
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

lemma case_option_find_give_me_a_map:
  "case_option a return (find f xs)
    = liftM projl
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

end