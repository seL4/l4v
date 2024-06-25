(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Equations between monads. Conclusions of the form "f = g" where f and g are monads.
   Should not be Hoare triples (those go into a different theory). *)

theory Trace_Monad_Equations
  imports
    Trace_Empty_Fail
    Trace_No_Fail
    Trace_No_Trace
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
    apply (auto simp: bind_def valid_def return_def mres_def vimage_def split: tmres.splits;
           fastforce simp: image_def intro: rev_bexI)
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

(*FIXME: the following lemmas were originally solved by monad_eq, which doesn't yet exist for the
         trace monad due to traces making equality more complicated.*)
lemma condition_apply_cong:
  "\<lbrakk> c s = c' s'; s = s'; \<And>s. c' s \<Longrightarrow> l s = l' s  ; \<And>s. \<not> c' s \<Longrightarrow> r s = r' s  \<rbrakk> \<Longrightarrow>  condition c l r s = condition c' l' r' s'"
  by (simp add: condition_def)

lemma condition_cong [cong, fundef_cong]:
  "\<lbrakk> c = c'; \<And>s. c' s \<Longrightarrow> l s = l' s; \<And>s. \<not> c' s \<Longrightarrow> r s = r' s \<rbrakk> \<Longrightarrow> condition c l r = condition c' l' r'"
  by (simp add: condition_def fun_eq_iff)

lemma lift_Inr [simp]: "(lift X (Inr r)) = (X r)"
  by (simp add: lift_def)

lemma lift_Inl [simp]: "lift C (Inl a) = throwError a"
  by (simp add: lift_def)

lemma returnOk_def2:  "returnOk a = return (Inr a)"
  by (simp add: returnOk_def)

lemma liftE_fail[simp]: "liftE fail = fail"
  by (simp add: liftE_def)

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
  have pre: "\<And>rv s'. \<lbrakk>(rv, s') \<in> mres (g s)\<rbrakk> \<Longrightarrow> f rv s' = f' rv s'"
    using assms unfolding valid_def apply -
    by (erule allE[where x=s]) (fastforce simp: mres_def image_def)
  show ?thesis
    by (fastforce intro!: bind_apply_cong simp: pre)
qed

lemma monad_eq_split2:
  assumes eq: " g' s = g s"
  assumes tail:"\<And>r s. Q r s \<Longrightarrow> f r s = f' r s"
  and hoare:   "\<lbrace>P\<rbrace> g \<lbrace>\<lambda>r s. Q r s\<rbrace>" "P s"
  shows "(g >>= f) s = (g' >>= f') s"
  apply (rule trans)
   apply (rule monad_eq_split[OF tail hoare], assumption)
  apply (clarsimp simp: bind_def eq)
  done

lemma monad_eq_split_tail:
  "\<lbrakk>f = g; a s = b s\<rbrakk> \<Longrightarrow> (a >>= f) s = ((b >>= g) s)"
  by (simp add:bind_def)

lemma double_gets_drop_regets:
  "(do x \<leftarrow> gets f;
       y \<leftarrow> gets f;
       m y x
    od) =
   (do x \<leftarrow> gets f;
       m x x
    od)"
  by (simp add: simpler_gets_def bind_def)

lemma state_assert_false[simp]:
  "state_assert (\<lambda>_. False) = fail"
  by (simp add: state_assert_def get_def bind_def)

lemma condition_fail_rhs:
  "condition C X fail = (state_assert C >>= (\<lambda>_. X))"
  by (auto simp: condition_def state_assert_def assert_def fail_def return_def get_def bind_def
                 fun_eq_iff)

lemma condition_swap:
  "condition C A B = condition (\<lambda>s. \<not> C s) B A"
  by (simp add: condition_def fun_eq_iff)

lemma condition_fail_lhs:
  "condition C fail X = (state_assert (\<lambda>s. \<not> C s) >>= (\<lambda>_. X))"
  by (metis condition_fail_rhs condition_swap)

lemma condition_bind_fail[simp]:
  "(condition C A B >>= (\<lambda>_. fail)) = condition C (A >>= (\<lambda>_. fail)) (B >>= (\<lambda>_. fail))"
  by (auto simp: condition_def assert_def fail_def bind_def fun_eq_iff)

lemma bind_fail_propagates:
  "\<lbrakk>no_trace A; empty_fail A\<rbrakk> \<Longrightarrow> A >>= (\<lambda>_. fail) = fail"
  by (fastforce simp: no_trace_def fail_def bind_def case_prod_unfold
               dest!: empty_fail_not_empty split: tmres.splits)

lemma simple_bind_fail [simp]:
  "(state_assert X >>= (\<lambda>_. fail)) = fail"
  "(modify M >>= (\<lambda>_. fail)) = fail"
  "(return X >>= (\<lambda>_. fail)) = fail"
  "(gets X >>= (\<lambda>_. fail)) = fail"
  by (auto intro!: bind_fail_propagates)

lemma bind_inv_inv_comm:
  "\<lbrakk> \<And>P. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. P\<rbrace>; \<And>P. \<lbrace>P\<rbrace> g \<lbrace>\<lambda>_. P\<rbrace>;
     empty_fail f; empty_fail g; no_trace f; no_trace g \<rbrakk> \<Longrightarrow>
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
  apply (rule subset_antisym;
         clarsimp simp: no_trace_def case_prod_unfold
                 split: tmres.splits dest!: empty_fail_not_empty)
       apply ((drule_tac x=x in spec)+, fastforce)+
  done

lemma bind_known_operation_eq:
  "\<lbrakk> no_fail P f; \<lbrace>Q\<rbrace> f \<lbrace>\<lambda>rv s. rv = x \<and> s = t\<rbrace>; P s; Q s; empty_fail f; no_trace f \<rbrakk>
     \<Longrightarrow> (f >>= g) s = g x t"
  apply (drule(1) no_failD)
  apply (subgoal_tac "f s = {([], Result (x, t))}")
   apply (clarsimp simp: bind_def)
  apply (rule subset_antisym;
         clarsimp simp: valid_def empty_fail_def no_trace_def mres_def image_def failed_def)
   apply (metis eq_snd_iff tmres.exhaust)
  apply fastforce
  done

lemma assert_opt_If:
  "assert_opt v = If (v = None) fail (return (the v))"
  by (simp add: assert_opt_def split: option.split)

lemma if_to_top_of_bind:
  "(bind (If P x y) z) = If P (bind x z) (bind y z)"
  by (simp split: if_split)

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


subsection \<open>Alternative @{text env_steps} with repeat\<close>

lemma mapM_Cons:
  "mapM f (x # xs) = do
     y \<leftarrow> f x;
     ys \<leftarrow> mapM f xs;
     return (y # ys)
   od"
  and mapM_Nil:
  "mapM f [] = return []"
  by (simp_all add: mapM_def sequence_def)

lemma mapM_x_Cons:
  "mapM_x f (x # xs) = do
     y \<leftarrow> f x;
     mapM_x f xs
   od"
  and mapM_x_Nil:
  "mapM_x f [] = return ()"
  by (simp_all add: mapM_x_def sequence_x_def)

lemma mapME_Cons:
  "mapME f (x # xs) = doE
     y \<leftarrow> f x;
     ys \<leftarrow> mapME f xs;
     returnOk (y # ys)
   odE"
  and mapME_Nil:
  "mapME f [] = returnOk []"
  by (simp_all add: mapME_def sequenceE_def)

lemma mapME_x_Cons:
  "mapME_x f (x # xs) = doE
     y \<leftarrow> f x;
     mapME_x f xs
   odE"
  and mapME_x_Nil:
  "mapME_x f [] = returnOk ()"
  by (simp_all add: mapME_x_def sequenceE_x_def)

lemma mapM_append:
  "mapM f (xs @ ys) = (do
     fxs \<leftarrow> mapM f xs;
     fys \<leftarrow> mapM f ys;
     return (fxs @ fys)
   od)"
  by (induct xs, simp_all add: mapM_Cons mapM_Nil bind_assoc)

lemma mapM_x_append:
  "mapM_x f (xs @ ys) = (do
     x \<leftarrow> mapM_x f xs;
     mapM_x f ys
   od)"
  by (induct xs, simp_all add: mapM_x_Cons mapM_x_Nil bind_assoc)

lemma mapME_append:
  "mapME f (xs @ ys) = (doE
     fxs \<leftarrow> mapME f xs;
     fys \<leftarrow> mapME f ys;
     returnOk (fxs @ fys)
   odE)"
  by (induct xs, simp_all add: mapME_Cons mapME_Nil bindE_assoc)

lemma mapME_x_append:
  "mapME_x f (xs @ ys) = (doE
     fxs \<leftarrow> mapME_x f xs;
     mapME_x f ys
   odE)"
  by (induct xs, simp_all add: mapME_x_Cons mapME_x_Nil bindE_assoc)

lemma mapM_map:
  "mapM f (map g xs) = mapM (f o g) xs"
  by (induct xs; simp add: mapM_Nil mapM_Cons)

lemma mapM_x_map:
  "mapM_x f (map g xs) = mapM_x (f o g) xs"
  by (induct xs; simp add: mapM_x_Nil mapM_x_Cons)

lemma mapME_map:
  "mapME f (map g xs) = mapME (f o g) xs"
  by (induct xs; simp add: mapME_Nil mapME_Cons)

lemma mapME_x_map:
  "mapME_x f (map g xs) = mapME_x (f o g) xs"
  by (induct xs; simp add: mapME_x_Nil mapME_x_Cons)

primrec repeat_n :: "nat \<Rightarrow> ('s, unit) tmonad \<Rightarrow> ('s, unit) tmonad" where
    "repeat_n 0 f = return ()"
  | "repeat_n (Suc n) f = do f; repeat_n n f od"

lemma repeat_n_mapM_x:
  "repeat_n n f = mapM_x (\<lambda>_. f) (replicate n ())"
  by (induct n, simp_all add: mapM_x_Cons mapM_x_Nil)

definition repeat :: "('s, unit) tmonad \<Rightarrow> ('s, unit) tmonad" where
  "repeat f = do n \<leftarrow> select UNIV; repeat_n n f od"

definition env_step :: "('s,unit) tmonad" where
  "env_step =
   do
     s' \<leftarrow> select UNIV;
     put_trace_elem (Env, s');
     put s'
   od"

abbreviation
  "env_n_steps n \<equiv> repeat_n n env_step"

lemma elem_select_bind:
  "(tr, res) \<in> (do x \<leftarrow> select S; f x od) s
   = (\<exists>x \<in> S. (tr, res) \<in> f x s)"
  by (simp add: bind_def select_def)

lemma select_bind_UN:
  "(do x \<leftarrow> select S; f x od) = (\<lambda>s. \<Union>x \<in> S. f x s)"
  by (rule ext, auto simp: elem_select_bind)

lemma select_early:
  "S \<noteq> {}
   \<Longrightarrow> do x \<leftarrow> f; y \<leftarrow> select S; g x y od
       = do y \<leftarrow> select S; x \<leftarrow> f; g x y od"
  apply (simp add: bind_def select_def Sigma_def)
  apply (rule ext)
  apply (fastforce elim: rev_bexI image_eqI[rotated] split: tmres.split_asm)
  done

lemma repeat_n_choice:
  "S \<noteq> {}
   \<Longrightarrow> repeat_n n (do x \<leftarrow> select S; f x od)
       = (do xs \<leftarrow> select {xs. set xs \<subseteq> S \<and> length xs = n}; mapM_x f xs od)"
  apply (induct n; simp?)
   apply (simp add: select_def bind_def mapM_x_Nil cong: conj_cong)
  apply (simp add: select_early bind_assoc)
  apply (subst select_early)
   apply simp
   apply (auto intro: exI[where x="replicate n xs" for n xs])[1]
  apply (simp(no_asm) add: fun_eq_iff set_eq_iff elem_select_bind)
  apply (simp only: conj_comms[where Q="length xs = n" for xs n])
  apply (simp only: ex_simps[symmetric] conj_assoc length_Suc_conv, simp)
  apply (auto simp: mapM_x_Cons)
  done

lemma repeat_choice:
  "S \<noteq> {}
   \<Longrightarrow> repeat (do x \<leftarrow> select S; f x od)
       = (do xs \<leftarrow> select {xs. set xs \<subseteq> S}; mapM_x f xs od)"
  apply (simp add: repeat_def repeat_n_choice)
  apply (simp(no_asm) add: fun_eq_iff set_eq_iff elem_select_bind)
  done

lemma put_trace_append:
  "put_trace (xs @ ys) = do put_trace ys; put_trace xs od"
  by (induct xs; simp add: bind_assoc)

lemma put_trace_elem_put_comm:
  "do y \<leftarrow> put_trace_elem x; put s od
   = do y \<leftarrow> put s; put_trace_elem x od"
  by (simp add: put_def put_trace_elem_def bind_def insert_commute)

lemma put_trace_put_comm:
  "do y \<leftarrow> put_trace xs; put s od
   = do y \<leftarrow> put s; put_trace xs od"
  apply (rule sym; induct xs; simp)
  apply (simp add: bind_assoc put_trace_elem_put_comm)
  apply (simp add: bind_assoc[symmetric])
  done

lemma mapM_x_comm:
  "(\<forall>x \<in> set xs. do y \<leftarrow> g; f x od = do y \<leftarrow> f x; g od)
   \<Longrightarrow> do y \<leftarrow> g; mapM_x f xs od = do y \<leftarrow> mapM_x f xs; g od"
  apply (induct xs; simp add: mapM_x_Nil mapM_x_Cons)
  apply (simp add: bind_assoc[symmetric], simp add: bind_assoc)
  done

lemma mapM_x_split:
  "(\<forall>x \<in> set xs. \<forall>y \<in> set xs. do z \<leftarrow> g y; f x od = do (z :: unit) \<leftarrow> f x; g y od)
   \<Longrightarrow> mapM_x (\<lambda>x. do z \<leftarrow> f x; g x od) xs = do y \<leftarrow> mapM_x f xs; mapM_x g xs od"
  apply (induct xs; simp add: mapM_x_Nil mapM_x_Cons bind_assoc)
  apply (subst bind_assoc[symmetric], subst mapM_x_comm[where f=f and g="g x" for x])
   apply simp
  apply (simp add: bind_assoc)
  done

lemma mapM_x_put:
  "mapM_x put xs = unless (xs = []) (put (last xs))"
  apply (induct xs rule: rev_induct)
   apply (simp add: mapM_x_Nil unless_def when_def)
  apply (simp add: mapM_x_append mapM_x_Cons mapM_x_Nil)
  apply (simp add: bind_def unless_def when_def put_def return_def)
  done

lemma put_trace_mapM_x:
  "put_trace xs = mapM_x put_trace_elem (rev xs)"
  by (induct xs; simp add: mapM_x_Nil mapM_x_append mapM_x_Cons)

lemma rev_surj:
  "surj rev"
  by (rule surjI[where f=rev], simp)

lemma select_image:
  "select (f ` S) = do x \<leftarrow> select S; return (f x) od"
  by (auto simp add: bind_def select_def return_def Sigma_def)

lemma env_steps_repeat:
  "env_steps = repeat env_step"
  apply (simp add: env_step_def repeat_choice env_steps_def
                   select_early)
  apply (simp add: put_trace_elem_put_comm)
  apply (simp add: mapM_x_split put_trace_elem_put_comm put_trace_put_comm
                   mapM_x_put)
  apply (simp add: put_trace_mapM_x rev_map mapM_x_map o_def)
  apply (subst rev_surj[symmetric], simp add: select_image bind_assoc)
  apply (rule arg_cong2[where f=bind, OF refl ext])
  apply (simp add: bind_def get_def put_def unless_def when_def return_def)
  apply (simp add: last_st_tr_def hd_map hd_rev)
  done

lemma repeat_n_plus:
  "repeat_n (n + m) f = do repeat_n n f; repeat_n m f od"
  by (induct n; simp add: bind_assoc)

lemma repeat_eq_twice[simp]:
  "(do x \<leftarrow> repeat f; repeat f od) = repeat f"
  apply (simp add: repeat_def select_early)
  apply (simp add: bind_assoc repeat_n_plus[symmetric, simplified])
  apply (simp add: bind_def select_def Sigma_def)
  apply (rule ext, fastforce intro: exI[where x=0])
  done

lemmas repeat_eq_twice_then[simp] =
  repeat_eq_twice[THEN bind_then_eq, simplified bind_assoc]

lemmas env_steps_eq_twice[simp] =
  repeat_eq_twice[where f=env_step, folded env_steps_repeat]
lemmas env_steps_eq_twice_then[simp] =
  env_steps_eq_twice[THEN bind_then_eq, simplified bind_assoc]

lemmas mapM_collapse_append =
  mapM_append[symmetric, THEN bind_then_eq, simplified bind_assoc, simplified]

end