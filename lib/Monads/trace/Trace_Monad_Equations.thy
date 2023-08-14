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
    Trace_Lemmas
begin

lemmas bind_then_eq = arg_cong2[where f=bind, OF _ refl]

lemma modify_id:
  "modify id = return ()"
  by (simp add: modify_def get_def bind_def put_def return_def)

lemma modify_modify:
  "(do x \<leftarrow> modify f; modify (g x) od) = modify (g () o f)"
  by (simp add: bind_def simpler_modify_def)

lemmas modify_modify_bind = arg_cong2[where f=bind,
  OF modify_modify refl, simplified bind_assoc]

lemma select_single:
  "select {x} = return x"
  by (simp add: select_def return_def)

lemma put_then_get[unfolded K_bind_def]:
  "do put s; get od = do put s; return s od"
  by (simp add: put_def bind_def get_def return_def)

lemmas put_then_get_then
    = put_then_get[THEN bind_then_eq, simplified bind_assoc return_bind]

lemma select_empty_bind[simp]:
  "select {} >>= f = select {}"
  by (simp add: select_def bind_def)

lemma fail_bind[simp]:
  "fail >>= f = fail"
  by (simp add: bind_def fail_def)


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

lemma mapM_map:
  "mapM f (map g xs) = mapM (f o g) xs"
  by (induct xs; simp add: mapM_Nil mapM_Cons)

lemma mapM_x_map:
  "mapM_x f (map g xs) = mapM_x (f o g) xs"
  by (induct xs; simp add: mapM_x_Nil mapM_x_Cons)

primrec
  repeat_n :: "nat \<Rightarrow> ('s, unit) tmonad \<Rightarrow> ('s, unit) tmonad"
where
    "repeat_n 0 f = return ()"
  | "repeat_n (Suc n) f = do f; repeat_n n f od"

lemma repeat_n_mapM_x:
  "repeat_n n f = mapM_x (\<lambda>_. f) (replicate n ())"
  by (induct n, simp_all add: mapM_x_Cons mapM_x_Nil)

definition
  repeat :: "('s, unit) tmonad \<Rightarrow> ('s, unit) tmonad"
where
  "repeat f = do n \<leftarrow> select UNIV; repeat_n n f od"

definition
  env_step :: "('s,unit) tmonad"
where
  "env_step =
  (do
    s' \<leftarrow> select UNIV;
    put_trace_elem (Env, s');
    put s'
  od)"

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
  by (rule_tac f=rev in surjI, simp)

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

lemmas repeat_eq_twice_then[simp]
    = repeat_eq_twice[THEN bind_then_eq, simplified bind_assoc]

lemmas env_steps_eq_twice[simp]
    = repeat_eq_twice[where f=env_step, folded env_steps_repeat]
lemmas env_steps_eq_twice_then[simp]
    = env_steps_eq_twice[THEN bind_then_eq, simplified bind_assoc]

lemmas mapM_collapse_append = mapM_append[symmetric, THEN bind_then_eq,
    simplified bind_assoc, simplified]

end