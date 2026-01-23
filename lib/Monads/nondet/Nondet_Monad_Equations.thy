(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Equations between monads. Conclusions of the form "f = g" where f and g are monads.
   Should not be Hoare triples (those go into a different theory). *)

theory Nondet_Monad_Equations
  imports
    Nondet_Empty_Fail
    Nondet_No_Fail
    Nondet_MonadEq_Lemmas
begin

lemmas assertE_assert = assertE_liftE

lemma assert_def2:
  "assert v = assert_opt (if v then Some () else None)"
  by (cases v; simp add: assert_def assert_opt_def)

lemma return_returnOk:
  "return (Inr x) = returnOk x"
  unfolding returnOk_def by simp

lemma exec_modify:
  "(modify f >>= g) s = g () (f s)"
  by (simp add: bind_def simpler_modify_def)

lemma bind_return_eq:
  "(a >>= return) = (b >>= return) \<Longrightarrow> a = b"
  by clarsimp

lemmas bind_then_eq = arg_cong2[where f=bind, OF _ refl]

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

lemma cart_singleton_image:
  "S \<times> {s} = (\<lambda>v. (v, s)) ` S"
  by auto

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

lemma catch_liftE:
  "catch (liftE g) h = g"
  by (simp add: catch_def liftE_def)

lemma catch_liftE_bindE:
  "catch (liftE g >>=E (\<lambda>x. f x)) h = g >>= (\<lambda>x. catch (f x) h)"
  by (simp add: liftE_bindE catch_def bind_assoc)

lemma returnOk_catch_bind:
  "catch (returnOk v) h >>= g = g v"
  by (simp add: returnOk_liftE catch_liftE)

lemma liftE_bindE_assoc:
  "(liftE f >>=E g) >>= h = f >>= (\<lambda>x. g x >>= h)"
  by (simp add: liftE_bindE bind_assoc)

lemma unlessE_throw_catch_If:
  "catch (unlessE P (throwError e) >>=E f) g
   = (if P then catch (f ()) g else g e)"
  by (simp add: unlessE_def catch_throwError split: if_split)

lemma whenE_bindE_throwError_to_if:
  "whenE P (throwError e) >>=E (\<lambda>_. b) = (if P then (throwError e) else b)"
  unfolding whenE_def bindE_def
  by (auto simp: lift_def throwError_def returnOk_def)

lemma alternative_liftE_returnOk:
  "(liftE m \<sqinter> returnOk v) = liftE (m \<sqinter> return v)"
  by (simp add: liftE_def alternative_def returnOk_def bind_def return_def)

lemma alternative_left_readonly_bind:
  "\<lbrakk> \<lbrace>(=) s\<rbrace> f \<lbrace>\<lambda>rv. (=) s\<rbrace>; fst (f s) \<noteq> {} \<rbrakk>
   \<Longrightarrow> alternative (f >>= (\<lambda>x. g x)) h s
       = (f >>= (\<lambda>x. alternative (g x) h)) s"
  apply (subgoal_tac "\<forall>x \<in> fst (f s). snd x = s")
   apply (clarsimp simp: alternative_def bind_def split_def)
   apply fastforce
  apply clarsimp
  apply (drule(1) use_valid, simp_all)
  done

lemma gets_the_return:
  "(return x = gets_the f) = (\<forall>s. f s = Some x)"
  apply (subst fun_eq_iff)
  apply (simp add: return_def gets_the_def exec_gets
                   assert_opt_def fail_def
            split: option.split)
  apply auto
  done

lemma gets_the_returns:
  "(return x = gets_the f) = (\<forall>s. f s = Some x)"
  "(returnOk x = gets_the g) = (\<forall>s. g s = Some (Inr x))"
  "(throwError x = gets_the h) = (\<forall>s. h s = Some (Inl x))"
  by (simp_all add: returnOk_def throwError_def
                    gets_the_return)

lemma gets_the_eq_bind:
  "\<lbrakk> f = gets_the (fn_f o fn'); \<And>rv. g rv = gets_the (fn_g rv o fn') \<rbrakk>
   \<Longrightarrow> \<exists>fn. (f >>= g) = gets_the (fn o fn')"
  apply clarsimp
  apply (rule exI[where x="\<lambda>s. case (fn_f s) of None \<Rightarrow> None | Some v \<Rightarrow> fn_g v s"])
  apply (simp add: gets_the_def bind_assoc exec_gets
                   assert_opt_def fun_eq_iff
            split: option.split)
  done

lemma gets_the_eq_bindE:
  "\<lbrakk> f = gets_the (fn_f o fn'); \<And>rv. g rv = gets_the (fn_g rv o fn') \<rbrakk>
   \<Longrightarrow> \<exists>fn. (f >>=E g) = gets_the (fn o fn')"
  unfolding bindE_def
  apply (erule gets_the_eq_bind[where fn_g="\<lambda>rv s. case rv of Inl e \<Rightarrow> Some (Inl e) | Inr v \<Rightarrow> fn_g v s"])
  apply (simp add: lift_def gets_the_returns split: sum.split)
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
  by (simp add: assert_def assertE_def gets_the_fail gets_the_returns
         split: if_split)+

lemma ex_const_function:
  "\<exists>f. \<forall>s. f (f' s) = v"
  by force

lemma gets_the_condsE:
  "(\<exists>fn. whenE P f = gets_the (fn o fn'))
   = (P \<longrightarrow> (\<exists>fn. f = gets_the (fn o fn')))"
  "(\<exists>fn. unlessE P g = gets_the (fn o fn'))
   = (\<not> P \<longrightarrow> (\<exists>fn. g = gets_the (fn o fn')))"
  by (simp add: whenE_def unlessE_def gets_the_returns ex_const_function
         split: if_split)+

lemma let_into_return:
  "(let f = x in m f) = (do f \<leftarrow> return x; m f od)"
  by simp

lemma liftME_return:
  "liftME f (returnOk v) = returnOk (f v)"
  by (simp add: liftME_def)

lemma fold_bindE_into_list_case:
  "(doE v \<leftarrow> f; case_list (g v) (h v) x odE)
   = (case_list (doE v \<leftarrow> f; g v odE) (\<lambda>x xs. doE v \<leftarrow> f; h v x xs odE) x)"
  by (simp split: list.split)

lemma whenE_liftE:
  "whenE P (liftE f) = liftE (when P f)"
  by (simp add: whenE_def when_def returnOk_liftE)

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

lemma exec_select_f_singleton:
  "(select_f ({v},False) >>= f) = f v"
  by (simp add: select_f_def bind_def)

lemma maybe_fail_bind_fail:
  "unless P fail >>= (\<lambda>_. fail) = fail"
  "when P fail >>= (\<lambda>_. fail) = fail"
  by (clarsimp simp: bind_def fail_def return_def
                     unless_def when_def)+

lemma select_singleton[simp]:
  "select {x} = return x"
  by (simp add: select_def return_def)

lemma return_modify:
  "return () = modify id"
  by (simp add: return_def simpler_modify_def)

lemma liftE_liftM_liftME:
  "liftE (liftM f m) = liftME f (liftE m)"
  by (simp add: liftE_liftM liftME_liftM liftM_def)

lemma bind_return_unit:
  "f = (f >>= (\<lambda>x. return ()))"
  by simp

lemma modify_id_return:
  "modify id = return ()"
  by (simp add: simpler_modify_def return_def)

lemma liftE_bind_return_bindE_returnOk:
  "liftE (v >>= (\<lambda>rv. return (f rv)))
   = (liftE v >>=E (\<lambda>rv. returnOk (f rv)))"
  by (simp add: liftE_bindE, simp add: liftE_def returnOk_def)

lemma bind_eqI:
  "g = g' \<Longrightarrow> f >>= g = f >>= g'" by simp

lemma unlessE_throwError_returnOk:
  "(if P then returnOk v else throwError x)
   = (unlessE P (throwError x) >>=E (\<lambda>_. returnOk v))"
  by (cases P, simp_all add: unlessE_def)

lemma gets_the_bind_eq:
  "\<lbrakk> f s = Some x; g x s = h s \<rbrakk>
   \<Longrightarrow> (gets_the f >>= g) s = h s"
  by (simp add: gets_the_def bind_assoc exec_gets assert_opt_def)

lemma zipWithM_x_modify:
  "zipWithM_x (\<lambda>a b. modify (f a b)) as bs
   = modify (\<lambda>s. foldl (\<lambda>s (a, b). f a b s) s (zip as bs))"
  apply (simp add: zipWithM_x_def zipWith_def sequence_x_def)
  apply (induct ("zip as bs"))
   apply (simp add: simpler_modify_def return_def)
  apply (rule ext)
  apply (simp add: simpler_modify_def bind_def split_def)
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

lemma assert2:
  "(do v1 \<leftarrow> assert P; v2 \<leftarrow> assert Q; c od)
   = (do v \<leftarrow> assert (P \<and> Q); c od)"
  by (simp add: assert_def split: if_split)

lemma assert_opt_def2:
  "assert_opt v = (do assert (v \<noteq> None); return (the v) od)"
  by (simp add: assert_opt_def split: option.split)

lemma gets_assert:
  "(do v1 \<leftarrow> assert v; v2 \<leftarrow> gets f; c v1 v2 od)
   = (do v2 \<leftarrow> gets f; v1 \<leftarrow> assert v; c v1 v2 od)"
  by (simp add: simpler_gets_def return_def assert_def fail_def bind_def
         split: if_split)

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

lemma gets_return_gets_eq:
  "gets f >>= (\<lambda>g. return (h g)) = gets (\<lambda>s. h (f s))"
  by (simp add: simpler_gets_def bind_def return_def)

lemma gets_prod_comp:
  "gets (case x of (a, b) \<Rightarrow> f a b) = (case x of (a, b) \<Rightarrow> gets (f a b))"
  by (auto simp: split_def)

lemma bind_assoc2:
  "(do x \<leftarrow> a; _ \<leftarrow> b; c x od) = (do x \<leftarrow> (do x' \<leftarrow> a; _ \<leftarrow> b; return x' od); c x od)"
  by (simp add: bind_assoc)

lemma bind_assoc_group3:
  "(do x \<leftarrow> a; y \<leftarrow> b x; z \<leftarrow> c y; f z od) = (do w \<leftarrow> (do x \<leftarrow> a; y \<leftarrow> b x; c y od); f w od)"
  by (simp add: bind_assoc)

lemma bind_assoc_return_reverse:
  "do x \<leftarrow> f;
      _ \<leftarrow> g x;
      h x
   od =
   do x \<leftarrow> do x \<leftarrow> f;
              _ \<leftarrow> g x;
              return x
           od;
      h x
   od"
  by (simp only: bind_assoc return_bind)

lemma if_bind:
  "(if P then (a >>= (\<lambda>_. b)) else return ()) =
   (if P then a else return ()) >>= (\<lambda>_. if P then b else return ())"
  by (cases P; simp)

lemma bind_liftE_distrib: "(liftE (A >>= (\<lambda>x. B x))) = (liftE A >>=E (\<lambda>x. liftE (\<lambda>s. B x s)))"
  by (clarsimp simp: liftE_def bindE_def lift_def bind_assoc)

lemma condition_apply_cong:
  "\<lbrakk> c s = c' s'; s = s'; \<And>s. c' s \<Longrightarrow> l s = l' s  ; \<And>s. \<not> c' s \<Longrightarrow> r s = r' s  \<rbrakk> \<Longrightarrow>  condition c l r s = condition c' l' r' s'"
  by monad_eq

lemma condition_cong [cong, fundef_cong]:
  "\<lbrakk> c = c'; \<And>s. c' s \<Longrightarrow> l s = l' s; \<And>s. \<not> c' s \<Longrightarrow> r s = r' s \<rbrakk> \<Longrightarrow> condition c l r = condition c' l' r'"
  by monad_eq

lemma lift_Inr [simp]: "(lift X (Inr r)) = (X r)"
  by monad_eq

lemma lift_Inl [simp]: "lift C (Inl a) = throwError a"
  by monad_eq

lemma returnOk_def2:  "returnOk a = return (Inr a)"
  by monad_eq

lemma liftE_fail[simp]: "liftE fail = fail"
  by monad_eq

lemma catch_bind_distrib:
  "do _ <- m <catch> h; f od = (doE m; liftE f odE <catch> (\<lambda>x. do h x; f od))"
  by (force simp: catch_def bindE_def bind_assoc liftE_def lift_def bind_def
                  split_def return_def throwError_def
            split: sum.splits)

lemma if_catch_distrib:
  "((if P then f else g) <catch> h) = (if P then f <catch> h else g <catch> h)"
  by (simp split: if_split)

lemma will_throw_and_catch:
  "f = throwError e \<Longrightarrow> (f <catch> (\<lambda>_. g)) = g"
  by (simp add: catch_def throwError_def)

lemma catch_is_if:
  "(doE x <- f; g x odE <catch> h) =
   do
     rv <- f;
     if sum.isl rv then h (projl rv) else g (projr rv) <catch> h
   od"
  apply (simp add: bindE_def catch_def bind_assoc cong: if_cong)
  apply (rule bind_cong, rule refl)
  apply (clarsimp simp: lift_def throwError_def split: sum.splits)
  done

lemma liftE_K_bind: "liftE ((K_bind (\<lambda>s. A s)) x) = K_bind (liftE (\<lambda>s. A s)) x"
  by clarsimp

lemma monad_eq_split:
  assumes "\<And>r s. Q r s \<Longrightarrow> f r s = f' r s"
          "\<lbrace>P\<rbrace> g \<lbrace>\<lambda>r s. Q r s\<rbrace>"
          "P s"
  shows "(g >>= f) s = (g >>= f') s"
proof -
  have pre: "\<And>rv s'. \<lbrakk>(rv, s') \<in> fst (g s)\<rbrakk> \<Longrightarrow> f rv s' = f' rv s'"
    using assms unfolding valid_def apply -
    by (erule allE[where x=s]) auto
  show ?thesis
    by (simp add: bind_def image_def case_prod_unfold pre)
qed

lemma monad_eq_split2:
  assumes eq: " g' s = g s"
  assumes tail:"\<And>r s. Q r s \<Longrightarrow> f r s = f' r s"
  and hoare:   "\<lbrace>P\<rbrace> g \<lbrace>\<lambda>r s. Q r s\<rbrace>" "P s"
  shows "(g >>= f) s = (g' >>= f') s"
proof -
  have pre: "\<And>aa bb. \<lbrakk>(aa, bb) \<in> fst (g s)\<rbrakk> \<Longrightarrow> Q aa bb"
    using hoare by (auto simp: valid_def)
  show ?thesis
    by (simp add:bind_def eq image_def case_prod_unfold pre surjective_pairing tail)
qed

lemma monad_eq_split_tail:
  "\<lbrakk>f = g; a s = b s\<rbrakk> \<Longrightarrow> (a >>= f) s = ((b >>= g) s)"
  by (simp add:bind_def)

lemma double_gets_drop_regets:
  "(do x \<leftarrow> gets f;
       xa \<leftarrow> gets f;
       m xa x
    od) =
   (do xa \<leftarrow> gets f;
       m xa xa
    od)"
  by monad_eq

lemma bind_inv_inv_comm_weak:
  "\<lbrakk> \<And>s. \<lbrace>(=) s\<rbrace> f \<lbrace>\<lambda>_. (=) s\<rbrace>; \<And>s. \<lbrace>(=) s\<rbrace> g \<lbrace>\<lambda>_. (=) s\<rbrace>;
     empty_fail f; empty_fail g \<rbrakk> \<Longrightarrow>
   do x \<leftarrow> f; y \<leftarrow> g; n od = do y \<leftarrow> g; x \<leftarrow> f; n od"
  apply (rule ext)
  apply (fastforce simp: bind_def valid_def empty_fail_def split_def image_def)
  done

lemma state_assert_false[simp]:
  "state_assert (\<lambda>_. False) = fail"
  by monad_eq

lemma condition_fail_rhs:
  "condition C X fail = (state_assert C >>= (\<lambda>_. X))"
  by (monad_eq simp: Bex_def)

lemma condition_swap:
  "condition C A B = condition (\<lambda>s. \<not> C s) B A"
  by monad_eq auto

lemma condition_fail_lhs:
  "condition C fail X = (state_assert (\<lambda>s. \<not> C s) >>= (\<lambda>_. X))"
  by (metis condition_fail_rhs condition_swap)

lemma condition_bind_fail[simp]:
  "(condition C A B >>= (\<lambda>_. fail)) = condition C (A >>= (\<lambda>_. fail)) (B >>= (\<lambda>_. fail))"
  by monad_eq blast

lemma bind_fail_propagates:
  "empty_fail A \<Longrightarrow> A >>= (\<lambda>_. fail) = fail"
  by (monad_eq simp: empty_fail_def) fastforce

lemma simple_bind_fail [simp]:
  "(state_assert X >>= (\<lambda>_. fail)) = fail"
  "(modify M >>= (\<lambda>_. fail)) = fail"
  "(return X >>= (\<lambda>_. fail)) = fail"
  "(gets X >>= (\<lambda>_. fail)) = fail"
  by (auto intro!: bind_fail_propagates)

lemma bind_inv_inv_comm:
  "\<lbrakk> \<And>P. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. P\<rbrace>; \<And>P. \<lbrace>P\<rbrace> g \<lbrace>\<lambda>_. P\<rbrace>;
     empty_fail f; empty_fail g \<rbrakk> \<Longrightarrow>
   do x \<leftarrow> f; y \<leftarrow> g; n x y od = do y \<leftarrow> g; x \<leftarrow> f; n x y od"
  apply (rule ext)
  apply (rule trans[where s="(do (x, y) \<leftarrow> do x \<leftarrow> f; y \<leftarrow> (\<lambda>_. g s) ; (\<lambda>_. return (x, y) s) od;
                                 n x y od) s" for s])
   apply (simp add: bind_assoc)
   apply (intro bind_apply_cong, simp_all)[1]
    apply (metis in_inv_by_hoareD)
   apply (simp add: return_def bind_def)
   apply (metis in_inv_by_hoareD)
  apply (rule trans[where s="(do (x, y) \<leftarrow> do y \<leftarrow> g; x \<leftarrow> (\<lambda>_. f s) ; (\<lambda>_. return (x, y) s) od;
                                 n x y od) s" for s, rotated])
   apply (simp add: bind_assoc)
   apply (intro bind_apply_cong, simp_all)[1]
    apply (metis in_inv_by_hoareD)
   apply (simp add: return_def bind_def)
   apply (metis in_inv_by_hoareD)
  apply (rule bind_apply_cong, simp_all)
  apply (clarsimp simp: bind_def split_def return_def)
  apply (auto | drule(1) empty_failD3)+
  done

lemma bind_known_operation_eq:
  "\<lbrakk> no_fail P f; \<lbrace>Q\<rbrace> f \<lbrace>\<lambda>rv s. rv = x \<and> s = t\<rbrace>; P s; Q s; empty_fail f \<rbrakk>
     \<Longrightarrow> (f >>= g) s = g x t"
  apply (drule(1) no_failD)
  apply (subgoal_tac "fst (f s) = {(x, t)}")
   apply (clarsimp simp: bind_def)
  apply (fastforce simp: valid_def empty_fail_def)
  done

lemma assert_opt_If:
  "assert_opt v = If (v = None) fail (return (the v))"
  by (simp add: assert_opt_def split: option.split)

lemma bind_if_distribL:
  "(do rv \<leftarrow> w;
       if P
       then x rv
       else y rv
    od)
   = (if P
      then w >>= (\<lambda>rv. x rv)
      else w >>= (\<lambda>rv. y rv))"
  by (simp split: if_split)

lemma bind_if_distribR:
  "(bind (If P x y) z) = If P (bind x z) (bind y z)"
  by (simp split: if_split)

(* FIXME: replace uses of if_to_top_of_bind with bind_if_distribR *)
lemmas if_to_top_of_bind = bind_if_distribR

lemmas bind_if_distrib = bind_if_distribL bind_if_distribR

lemma if_to_top_of_bindE:
  "(bindE (If P x y) z) = If P (bindE x z) (bindE y z)"
  by (simp split: if_split)

lemma modify_modify:
  "(do x \<leftarrow> modify f; modify (g x) od) = modify (g () o f)"
  by (simp add: bind_def simpler_modify_def)

lemmas modify_modify_bind =
  arg_cong2[where f=bind, OF modify_modify refl, simplified bind_assoc]

lemma put_then_get[unfolded K_bind_def]:
  "do put s; get od = do put s; return s od"
  by (simp add: put_def bind_def get_def return_def)

lemmas put_then_get_then =
    put_then_get[THEN bind_then_eq, simplified bind_assoc return_bind]

lemma select_empty_bind[simp]:
  "select {} >>= f = select {}"
  by (simp add: select_def bind_def)

end