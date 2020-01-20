(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory SubMonadLib
imports
  EmptyFailLib
  Corres_UL
begin

locale submonad_args =
  fixes fetch :: "'a \<Rightarrow> 'b"
  fixes replace :: "'b \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes guard :: "'a \<Rightarrow> bool"

  assumes args:
   "\<forall>x s. guard s \<longrightarrow> fetch (replace x s) = x"
   "\<forall>x y s. replace x (replace y s) = replace x s"
   "\<forall>s. replace (fetch s) s = s"

  assumes replace_preserves_guard:
   "\<And>s x. guard (replace x s) = guard s"

definition
  submonad_fn :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow>
                  ('b, 'c) nondet_monad \<Rightarrow> ('a, 'c) nondet_monad"
where
 "submonad_fn fetch replace guard m \<equiv> do
    stateAssert guard [];
    substate \<leftarrow> gets fetch;
    (rv, substate') \<leftarrow> select_f (m substate);
    modify (replace substate');
    return rv
  od"

locale submonad = submonad_args +
  fixes fn :: "('b, 'c) nondet_monad \<Rightarrow> ('a, 'c) nondet_monad"

  assumes fn_is_sm: "fn = submonad_fn fetch replace guard"

lemma (in submonad_args) argsD1:
  "\<And>x s. guard s \<Longrightarrow> fetch (replace x s) = x"
  by (simp add: args)

lemma (in submonad) guarded_sm:
  "\<And>s. guard s \<Longrightarrow>
   fn m s = (do
     substate \<leftarrow> gets fetch;
     (rv, substate') \<leftarrow> select_f (m substate);
     modify (replace substate');
     return rv
   od) s"
  unfolding fn_is_sm submonad_fn_def
  by (simp add: stateAssert_def get_def assert_def bind_def return_def)

lemma modify_modify:
  "modify fn1 >>= (\<lambda>x. modify fn2) = modify (fn2 \<circ> fn1)"
  by (simp add: bind_def modify_def get_def put_def)

lemma select_f_walk:
  assumes m1: "empty_fail m1"
  assumes S: "fst S = {} \<Longrightarrow> snd S"
  shows "(do a \<leftarrow> m1; b \<leftarrow> select_f S; m2 a b od) = (do b \<leftarrow> select_f S; a \<leftarrow> m1; m2 a b od)"
  apply (rule ext)
  apply (rule prod.expand)
  apply (rule conjI)
   apply (simp add: select_f_def bind_def split_def)
   apply fastforce
  apply (simp add: select_f_def bind_def split_def)
  apply (case_tac "fst S = {}")
   apply clarsimp
   apply (case_tac "fst (m1 x) = {}")
    apply (simp add: empty_failD [OF m1] S)
   apply (frule S)
   apply force
  apply safe
     apply clarsimp
     apply force
    apply force
   apply clarsimp
   apply force
  apply clarsimp
  apply (case_tac "fst (m1 x) = {}", simp add: empty_failD [OF m1])
  apply force
  done

lemma stateAssert_stateAssert:
  "(stateAssert g [] >>= (\<lambda>u. stateAssert g' [])) = stateAssert (g and g') []"
  by (simp add: ext stateAssert_def bind_def get_def assert_def fail_def return_def)

lemma modify_stateAssert:
  "\<lbrakk> \<And>s x. g (r x s) = g s \<rbrakk> \<Longrightarrow>
   (modify (r x) >>= (\<lambda>u. stateAssert g []))
            = (stateAssert g [] >>= (\<lambda>u. modify (r x)))"
  by (simp add: ext stateAssert_def bind_def get_def assert_def fail_def
                return_def modify_def put_def)

lemma gets_stateAssert:
  "(gets f >>= (\<lambda>x. stateAssert g' [] >>= (\<lambda>u. m x)))
            = (stateAssert g' [] >>= (\<lambda>u. gets f >>= (\<lambda>x. m x)))"
  by (simp add: ext stateAssert_def bind_def gets_def get_def
                assert_def fail_def return_def)

lemma select_f_stateAssert:
  "empty_fail m \<Longrightarrow>
   (select_f (m a) >>= (\<lambda>x. stateAssert g [] >>= (\<lambda>u. n x))) =
   (stateAssert g [] >>= (\<lambda>u. select_f (m a) >>= (\<lambda>x. n x)))"
  apply (rule ext)
  apply (clarsimp simp: stateAssert_def bind_def select_f_def get_def
                        assert_def return_def fail_def split_def image_image)
  apply (simp only: image_def)
  apply (clarsimp simp: stateAssert_def bind_def select_f_def get_def
                        assert_def return_def fail_def split_def image_image)
  apply (simp only: image_def mem_simps empty_fail_def simp_thms)
  apply fastforce
  done

lemma bind_select_f_bind':
  shows "(select_f (m s) >>= (\<lambda>x. select_f (split n x))) = (select_f ((m >>= n) s))"
  apply (rule ext)
  apply (force simp: select_f_def bind_def split_def)
  done

lemma bind_select_f_bind:
  "(select_f (m1 s) >>= (\<lambda>x. select_f (m2 (fst x) (snd x)))) = (select_f ((m1 >>= m2) s))"
  by (insert bind_select_f_bind' [where m=m1 and n=m2 and s=s],
      simp add: split_def)

lemma select_from_gets: "select_f (gets f s) = return (f s, s)"
  apply (rule ext)
  apply (simp add: select_f_def return_def simpler_gets_def)
  done

lemma select_from_gets':
  "(select_f \<circ> gets f) = (\<lambda>s. return (f s, s))"
  apply (rule ext)
  apply (simp add: o_def select_from_gets)
  done

lemma bind_subst_lift:
  "(f >>= g) = h \<Longrightarrow> (do x \<leftarrow> f; y \<leftarrow> g x; j y od) = (h >>= j)"
  by (simp add: bind_assoc[symmetric])

lemma modify_gets:
  "\<lbrakk> \<And>x s. g (r x s) = g s; \<And>x s. g s \<longrightarrow> f (r x s) = x \<rbrakk>
   \<Longrightarrow> (modify (r x) >>= (\<lambda>u. stateAssert g [] >>= (\<lambda>u'. gets f)))
            = (stateAssert g [] >>= (\<lambda>u'. modify (r x) >>= (\<lambda>u. return x)))"
  by (simp add: ext stateAssert_def assert_def modify_def bind_def get_def
                put_def gets_def return_def fail_def)

lemma (in submonad_args) gets_modify:
  "\<And>s. guard s \<Longrightarrow>
   (do x \<leftarrow> gets fetch; u \<leftarrow> modify (replace x); f x od) s = ((gets fetch) >>= f) s"
  by (clarsimp simp: modify_def gets_def return_def bind_def
                     put_def args get_def
              split: option.split)

lemma submonad_bind:
  "\<lbrakk> submonad f r g m; submonad f r g m'; submonad f r g m'';
     empty_fail a; \<And>x. empty_fail (b x) \<rbrakk> \<Longrightarrow>
   m (a >>= b) = (m' a) >>= (\<lambda>rv. m'' (b rv))"
  apply (subst submonad.fn_is_sm, assumption)+
  apply (clarsimp simp: submonad_def bind_assoc split_def submonad_fn_def)
  apply (subst bind_subst_lift [OF modify_gets, unfolded bind_assoc])
    apply (simp add: submonad_args.args submonad_args.replace_preserves_guard)+
  apply (subst select_f_stateAssert, assumption)
  apply (subst gets_stateAssert)
  apply (subst bind_subst_lift [OF stateAssert_stateAssert])
  apply (clarsimp simp: pred_conj_def)
  apply (clarsimp simp: bind_assoc split_def select_f_walk
                empty_fail_stateAssert empty_failD
                bind_subst_lift[OF modify_modify] submonad_args.args o_def
                bind_subst_lift[OF bind_select_f_bind])
  done

lemma (in submonad) guard_preserved:
  "\<And>s s'. \<lbrakk> (rv, s') \<in> fst (fn m s) \<rbrakk> \<Longrightarrow> guard s'"
  unfolding fn_is_sm submonad_fn_def
  by (clarsimp simp: stateAssert_def gets_def get_def bind_def modify_def put_def
                     return_def select_f_def replace_preserves_guard in_monad)

lemma fst_stateAssertD:
  "\<And>s s' v. (v, s') \<in> fst (stateAssert g [] s) \<Longrightarrow> s' = s \<and> g s"
  by (clarsimp simp: stateAssert_def in_monad)

lemma(in submonad) guarded_gets:
  "\<And>s. guard s \<Longrightarrow> fn (gets f) s = gets (f \<circ> fetch) s"
  apply (simp add: guarded_sm select_from_gets gets_modify)
  apply (simp add: gets_def)
  done

lemma (in submonad) guarded_return:
  "\<And>s. guard s \<Longrightarrow> fn (return x) s = return x s"
  using args guarded_gets
  by (fastforce simp: gets_def bind_def get_def)

lemma (in submonad_args) submonad_fn_gets:
  "submonad_fn fetch replace guard (gets f) =
   (stateAssert guard [] >>= (\<lambda>u. gets (f \<circ> fetch)))"
  apply (simp add: ext select_from_gets submonad_fn_def)
  apply (rule bind_cong [OF refl])
  apply (clarsimp simp: gets_modify dest!: fst_stateAssertD)
  apply (simp add: gets_def)
  done

lemma(in submonad) gets:
  "fn (gets f) = (stateAssert guard [] >>= (\<lambda>u. gets (f \<circ> fetch)))"
  unfolding fn_is_sm submonad_fn_gets
  by (rule refl)

lemma (in submonad) return:
  "fn (return x) = (stateAssert guard [] >>= (\<lambda>u. return x))"
  using args gets
  by (fastforce simp: gets_def bind_def get_def)

lemma (in submonad) mapM_guard_preserved:
  "\<And>s s'. \<lbrakk> guard s; \<exists>rv. (rv, s') \<in> fst (mapM (fn \<circ> m) xs s)\<rbrakk> \<Longrightarrow> guard s'"
proof (induct xs)
  case Nil
  thus ?case
    by (simp add: mapM_def sequence_def return_def)
  next
  case (Cons x xs)
  thus ?case
    apply (clarsimp simp: o_def mapM_Cons return_def bind_def)
    apply (drule guard_preserved)
    apply fastforce
    done
qed

lemma (in submonad) mapM_x_guard_preserved:
  "\<And>s s'. \<lbrakk> guard s; \<exists>rv. (rv, s') \<in> fst (mapM_x (fn \<circ> m) xs s)\<rbrakk> \<Longrightarrow> guard s'"
proof (induct xs)
  case Nil
  thus ?case
    by (simp add: mapM_x_def sequence_x_def return_def)
  next
  case (Cons x xs)
  thus ?case
    apply (clarsimp simp: o_def mapM_x_Cons return_def bind_def)
    apply (drule guard_preserved)
    apply fastforce
    done
qed

lemma (in submonad) stateAssert_fn:
  "stateAssert guard [] >>= (\<lambda>u. fn m) = fn m"
  by (simp add: fn_is_sm submonad_fn_def pred_conj_def
                bind_subst_lift [OF stateAssert_stateAssert])

lemma (in submonad) fn_stateAssert:
  "fn m >>= (\<lambda>x. stateAssert guard [] >>= (\<lambda>u. n x)) = (fn m >>= n)"
  apply (simp add: fn_is_sm submonad_fn_def bind_assoc split_def)
  apply (rule ext)
  apply (rule bind_apply_cong [OF refl])+
  apply (clarsimp simp: stateAssert_def bind_assoc in_monad select_f_def)
  apply (drule iffD2 [OF replace_preserves_guard])
  apply (fastforce simp: bind_def assert_def get_def return_def)
  done

lemma submonad_mapM:
  assumes sm: "submonad f r g sm" and sm': "submonad f r g sm'"
  assumes efm: "\<And>x. empty_fail (m x)"
  shows
  "(sm (mapM m l)) = (stateAssert g [] >>= (\<lambda>u. mapM (sm' \<circ> m) l))"
proof (induct l)
  case Nil
  thus ?case
    by (simp add: mapM_def sequence_def bind_def submonad.return [OF sm])
  next
  case (Cons x xs)
  thus ?case
    using sm sm' efm
    apply (simp add: mapM_Cons)
    apply (simp add: bind_subst_lift [OF submonad.stateAssert_fn])
    apply (simp add: bind_assoc submonad_bind submonad.return)
    apply (subst submonad.fn_stateAssert [OF sm'])
    apply (intro ext bind_apply_cong [OF refl])
    apply (subgoal_tac "g sta")
     apply (clarsimp simp: stateAssert_def bind_def get_def assert_def return_def)
    apply (frule(1) submonad.guard_preserved)
    apply (erule(1) submonad.mapM_guard_preserved, fastforce simp: o_def)
    done
qed

lemma submonad_mapM_x:
  assumes sm: "submonad f r g sm" and sm': "submonad f r g sm'"
  assumes efm: "\<And>x. empty_fail (m x)"
  shows
  "(sm (mapM_x m l)) = (stateAssert g [] >>= (\<lambda>u. mapM_x (sm' \<circ> m) l))"
proof (induct l)
  case Nil
  thus ?case
    by (simp add: mapM_x_def sequence_x_def bind_def submonad.return [OF sm])
  next
  case (Cons x xs)
  thus ?case
    using sm sm' efm
    apply (simp add: mapM_x_Cons)
    apply (simp add: bind_subst_lift [OF submonad.stateAssert_fn])
    apply (simp add: bind_assoc submonad_bind submonad.return)
    apply (subst submonad.fn_stateAssert [OF sm'])
    apply (intro ext bind_apply_cong [OF refl])
    apply (subgoal_tac "g st")
     apply (clarsimp simp: stateAssert_def bind_def get_def assert_def return_def)
    apply (frule(1) submonad.guard_preserved, simp)
    done
qed

lemma corres_select:
  "(\<forall>s' \<in> S'. \<exists>s \<in> S. rvr s s') \<Longrightarrow> corres_underlying sr nf nf' rvr \<top> \<top> (select S) (select S')"
  by (clarsimp simp: select_def corres_underlying_def)

lemma corres_select_f:
  "\<lbrakk> \<forall>s' \<in> fst S'. \<exists>s \<in> fst S. rvr s s'; nf' \<Longrightarrow> \<not> snd S' \<rbrakk>
      \<Longrightarrow> corres_underlying sr nf nf' rvr \<top> \<top> (select_f S) (select_f S')"
  by (clarsimp simp: select_f_def corres_underlying_def)

lemma corres_modify':
  "\<lbrakk> (\<forall>s s'. (s, s') \<in> sr \<longrightarrow> (f s, f' s') \<in> sr); r () () \<rbrakk>
      \<Longrightarrow> corres_underlying sr nf nf' r \<top> \<top> (modify f) (modify f')"
  by (clarsimp simp: modify_def corres_underlying_def bind_def get_def put_def)

(* FIXME: this should only be used for the lemma below *)
lemma corres_select_f_stronger:
  "\<lbrakk> \<forall>s' \<in> fst S'. \<exists>s \<in> fst S. rvr s s'; nf' \<Longrightarrow> \<not> snd S' \<rbrakk>
      \<Longrightarrow> corres_underlying sr nf nf' rvr \<top> \<top> (select_f S) (select_f S')"
  by (clarsimp simp: select_f_def corres_underlying_def)

lemma stateAssert_sp:
  "\<lbrace>P\<rbrace> stateAssert Q l \<lbrace>\<lambda>_. P and Q\<rbrace>"
  by (clarsimp simp: valid_def stateAssert_def in_monad)

lemma corres_submonad:
  "\<lbrakk> submonad f r g fn; submonad f' r' g' fn';
     \<forall>s s'. (s, s') \<in> sr \<and> g s \<and> g' s' \<longrightarrow> (f s, f' s') \<in> ssr;
     \<forall>s s' ss ss'. ((s, s') \<in> sr \<and> (ss, ss') \<in> ssr) \<longrightarrow> (r ss s, r' ss' s') \<in> sr;
     corres_underlying ssr False nf' rvr \<top> \<top> x x'\<rbrakk>
   \<Longrightarrow> corres_underlying sr False nf' rvr g g' (fn x) (fn' x')"
  apply (subst submonad.fn_is_sm, assumption)+
  apply (clarsimp simp: submonad_fn_def)
  apply (rule corres_split' [OF _ _ stateAssert_sp stateAssert_sp])
   apply (fastforce simp: corres_underlying_def stateAssert_def get_def
                         assert_def return_def bind_def)
  apply (rule corres_split' [where r'="\<lambda>x y. (x, y) \<in> ssr",
                             OF _ _ hoare_post_taut hoare_post_taut])
   apply clarsimp
  apply (rule corres_split' [where r'="\<lambda>(x, x') (y, y'). rvr x y \<and> (x', y') \<in> ssr",
                             OF _ _ hoare_post_taut hoare_post_taut])
   defer
   apply clarsimp
   apply (rule corres_split' [where r'=dc, OF _ _ hoare_post_taut hoare_post_taut])
    apply (simp add: corres_modify')
   apply clarsimp
  apply (rule corres_select_f_stronger)
   apply (clarsimp simp: corres_underlying_def)
   apply (drule (1) bspec, clarsimp)
   apply (drule (1) bspec, simp)
   apply blast
  apply (clarsimp simp: corres_underlying_def)
  apply (drule (1) bspec, clarsimp)
  done

lemma stateAssert_top [simp]:
  "stateAssert \<top> l >>= f = f ()"
  by (clarsimp simp add: stateAssert_def get_def bind_def return_def)

lemma stateAssert_A_top [simp]:
  "stateAssert \<top> l = return ()"
  by (simp add: stateAssert_def get_def bind_def return_def)

text \<open>Use of the submonad concept to demonstrate commutativity.\<close>

lemma gets_modify_comm:
  "\<And> s. \<lbrakk> g (f s) = g s \<rbrakk> \<Longrightarrow>
   (do x \<leftarrow> modify f; y \<leftarrow> gets g; m x y od) s =
   (do y \<leftarrow> gets g; x \<leftarrow> modify f; m x y od) s"
  by (simp add: modify_def gets_def get_def bind_def put_def return_def)

lemma bind_subst_lhs_inv:
  "\<And>s. \<lbrakk> \<And>x s'. P s' \<Longrightarrow> (f x >>= g x) s' = h x s'; \<lbrace>P\<rbrace> a \<lbrace>\<lambda>_. P\<rbrace>; P s \<rbrakk> \<Longrightarrow>
   (do x \<leftarrow> a; y \<leftarrow> f x; g x y od) s = (a >>= h) s"
  apply (rule bind_apply_cong [OF refl])
  apply (drule(2) use_valid)
  apply simp
  done

lemma gets_comm:
  "do x \<leftarrow> gets f; y \<leftarrow> gets g; m x y od = do y \<leftarrow> gets g; x \<leftarrow> gets f; m x y od"
  by (simp add: gets_def get_def return_def bind_def)

lemma submonad_comm:
  assumes x1: "submonad_args f r g" and x2: "submonad_args f' r' g'"
  assumes y: "m = submonad_fn f r g im" "m' = submonad_fn f' r' g' im'"
  assumes z: "\<And>s x x'. r x (r' x' s) = r' x' (r x s)"
  assumes gp: "\<And>s x. g (r' x s) = g s" and gp': "\<And>s x. g' (r x s) = g' s"
  assumes efim: "empty_fail im" and efim': "empty_fail im'"
  shows      "(do x \<leftarrow> m; y \<leftarrow> m'; n x y od) = (do y \<leftarrow> m'; x \<leftarrow> m; n x y od)"
proof -
  have P: "\<And>x s. g s \<Longrightarrow> f (r' x s) = f s"
    apply (subgoal_tac "f (r' x (r (f s) s)) = f s")
     apply (simp add: submonad_args.args[OF x1])
    apply (simp add: z[symmetric])
    apply (subst(asm) gp [symmetric])
    apply (fastforce dest: submonad_args.argsD1[OF x1])
    done
  have Q: "\<And>x s. g' s \<Longrightarrow> f' (r x s) = f' s"
    apply (subgoal_tac "f' (r x (r' (f' s) s)) = f' s")
     apply (simp add: submonad_args.args[OF x2])
    apply (simp add: z)
    apply (subst(asm) gp' [symmetric])
    apply (fastforce dest: submonad_args.argsD1[OF x2])
    done
  note empty_failD [OF efim, simp]
  note empty_failD [OF efim', simp]
  show ?thesis
    apply (clarsimp simp: submonad_fn_def y bind_assoc split_def)
    apply (subst bind_subst_lift [OF modify_stateAssert], rule gp gp')+
    apply (simp add: bind_assoc)
    apply (subst select_f_stateAssert, rule efim efim')+
    apply (subst gets_stateAssert bind_subst_lift [OF stateAssert_stateAssert])+
    apply (rule bind_cong)
     apply (simp add: pred_conj_def conj_comms)
    apply (simp add: bind_assoc select_f_walk[symmetric])
    apply (clarsimp dest!: fst_stateAssertD)
    apply (subst bind_assoc[symmetric],
           subst bind_subst_lhs_inv [OF gets_modify_comm],
           erule P Q, wp, simp, simp)+
    apply (simp add: bind_assoc)
    apply (simp add: select_f_walk[symmetric])
    apply (subst gets_comm)
    apply (rule bind_apply_cong [OF refl])+
    apply (subst select_f_walk, simp, simp,
           subst select_f_walk, simp, simp,
           rule bind_apply_cong [OF refl])
    apply (subst select_f_walk, simp, simp, rule bind_apply_cong [OF refl])
    apply (clarsimp simp: simpler_gets_def select_f_def)
    apply (simp add: bind_def get_def put_def modify_def z)
    done
qed

lemma submonad_comm2:
  assumes x1: "submonad_args f r g" and x2: "m = submonad_fn f r g im"
  assumes y: "submonad f' r' g' m'"
  assumes z: "\<And>s x x'. r x (r' x' s) = r' x' (r x s)"
  assumes gp: "\<And>s x. g (r' x s) = g s" and gp': "\<And>s x. g' (r x s) = g' s"
  assumes efim: "empty_fail im" and efim': "empty_fail im'"
  shows      "do x \<leftarrow> m; y \<leftarrow> m' im'; n x y od = do y \<leftarrow> m' im'; x \<leftarrow> m; n x y od"
  apply (rule submonad_comm[where f'=f' and r'=r', OF x1 _ x2 _ z])
       apply (insert y)
       apply (fastforce simp add: submonad_def)
      apply (fastforce dest: submonad.fn_is_sm)
     apply (simp add: efim efim' gp gp')+
  done

lemma submonad_bind_alt:
  assumes x: "submonad_args f r g"
  assumes y: "a = submonad_fn f r g a'" "\<And>rv. b rv = submonad_fn f r g (b' rv)"
  assumes efa: "empty_fail a'" and efb: "\<And>x. empty_fail (b' x)"
  shows      "(a >>= b) = submonad_fn f r g (a' >>= b')"
proof -
  have P: "submonad f r g (submonad_fn f r g)"
    by (simp add: x submonad_def submonad_axioms_def)
  have Q: "b = (\<lambda>rv. submonad_fn f r g (b' rv))"
    by (rule ext) fact+
  show ?thesis
    by (simp add: y Q submonad_bind [OF P P P efa efb])
qed

lemma submonad_singleton:
  "submonad_fn fetch replace \<top> (\<lambda>s. ({(rv s, s' s)}, False))
     = (\<lambda>s. ({(rv (fetch s), replace (s' (fetch s)) s)}, False))"
  apply (rule ext)
  apply (simp add: submonad_fn_def bind_def gets_def
                put_def get_def modify_def return_def
                select_f_def UNION_eq)
  done

lemma gets_submonad:
  "\<lbrakk> submonad_args fetch replace \<top>; \<And>s. f s = f' (fetch s); m = gets f' \<rbrakk>
   \<Longrightarrow> gets f = submonad_fn fetch replace \<top> m"
  apply (drule submonad_args.args(3))
  apply (clarsimp simp add: simpler_gets_def submonad_singleton)
  done

lemma modify_submonad:
  "\<lbrakk> \<And>s. f s = replace (K_record (f' (fetch s))) s; m = modify f' \<rbrakk>
     \<Longrightarrow> modify f = submonad_fn fetch (replace o K_record) \<top> m"
  by (simp add: simpler_modify_def submonad_singleton)

lemma fail_submonad:
  "fail = submonad_fn fetch replace \<top> fail"
  by (simp add: submonad_fn_def simpler_gets_def return_def
                simpler_modify_def select_f_def bind_def fail_def)

lemma return_submonad:
  "submonad_args fetch replace guard \<Longrightarrow>
   return v = submonad_fn fetch replace \<top> (return v)"
  by (simp add: return_def submonad_singleton submonad_args.args)

lemma assert_opt_submonad:
  "submonad_args fetch replace \<top> \<Longrightarrow>
   assert_opt v = submonad_fn fetch replace \<top> (assert_opt v)"
  apply (case_tac v, simp_all add: assert_opt_def)
   apply (rule fail_submonad)
  apply (rule return_submonad)
  apply assumption
  done

lemma is_stateAssert_gets:
  "\<lbrakk> \<forall>s. \<lbrace>(=) s\<rbrace> f \<lbrace>\<lambda>_. (=) s\<rbrace>; \<lbrace>\<top>\<rbrace> f \<lbrace>\<lambda>_. guard\<rbrace>;
     empty_fail f; no_fail guard f; \<lbrace>guard\<rbrace> f \<lbrace>\<lambda>rv s. fetch s = rv\<rbrace> \<rbrakk>
    \<Longrightarrow> f = do stateAssert guard []; gets fetch od"
  apply (rule ext)
  apply (clarsimp simp: bind_def empty_fail_def valid_def no_fail_def
                        stateAssert_def assert_def gets_def get_def
                        return_def fail_def image_def split_def)
  apply (case_tac "f x")
  apply (intro conjI impI)
   apply (drule_tac x=x in spec)+
   apply (subgoal_tac "\<forall>xa\<in>fst (f x). fst xa = fetch x \<and> snd xa = x")
    apply fastforce
   apply clarsimp
  apply (drule_tac x=x in spec)+
  apply fastforce
  done

lemma is_modify:
  "\<And>s. \<lbrakk> \<lbrace>(=) s\<rbrace> f \<lbrace>\<lambda>_. (=) (replace s)\<rbrace>; empty_fail f;
          no_fail guard f; guard s \<rbrakk>
    \<Longrightarrow> f s = modify replace s"
  apply (clarsimp simp: bind_def empty_fail_def valid_def no_fail_def
                        stateAssert_def assert_def modify_def get_def put_def
                        return_def fail_def image_def split_def)
  apply (case_tac "f s")
  apply force
  done

lemma submonad_comm':
  assumes sm1: "submonad f r g m" and sm2: "submonad f' r' g' m'"
  assumes z: "\<And>s x x'. r x (r' x' s) = r' x' (r x s)"
  assumes gp: "\<And>s x. g (r' x s) = g s" and gp': "\<And>s x. g' (r x s) = g' s"
  assumes efim: "empty_fail im" and efim': "empty_fail im'"
  shows      "(do x \<leftarrow> m im; y \<leftarrow> m' im'; n x y od) =
              (do y \<leftarrow> m' im'; x \<leftarrow> m im; n x y od)"
  apply (rule submonad_comm [where f'=f' and r'=r', OF _ _ _ _ z])
         apply (insert sm1 sm2)
         apply (fastforce dest: submonad.fn_is_sm simp: submonad_def)+
     apply (simp add: efim efim' gp gp')+
  done

end
