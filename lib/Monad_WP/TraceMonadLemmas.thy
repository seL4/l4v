(*
 * Copyright 2017, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)
theory TraceMonadLemmas
imports TraceMonadVCG
begin

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

lemmas bind_then_eq = arg_cong2[where f=bind, OF _ refl]
lemmas repeat_eq_twice_then[simp]
    = repeat_eq_twice[THEN bind_then_eq, simplified bind_assoc]

lemmas env_steps_eq_twice[simp]
    = repeat_eq_twice[where f=env_step, folded env_steps_repeat]
lemmas env_steps_eq_twice_then[simp]
    = env_steps_eq_twice[THEN bind_then_eq, simplified bind_assoc]

lemmas mapM_collapse_append = mapM_append[symmetric, THEN bind_then_eq,
    simplified bind_assoc, simplified]

lemma prefix_closed_mapM[rule_format, wp_split]:
  "(\<forall>x \<in> set xs. prefix_closed (f x)) \<Longrightarrow> prefix_closed (mapM f xs)"
  apply (induct xs)
   apply (simp add: mapM_def sequence_def)
  apply (clarsimp simp: mapM_Cons)
  apply (intro prefix_closed_bind allI; clarsimp)
  done

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

lemmas bind_promote_If
    = if_distrib[where f="\<lambda>f. bind f g" for g]
      if_distrib[where f="\<lambda>g. bind f g" for f]

lemma bind_promote_If2:
  "do x \<leftarrow> f; if P then g x else h x od
    = (if P then bind f g else bind f h)"
  by simp

lemma exec_put_trace[unfolded K_bind_def]:
  "(do put_trace xs; f od) s
    = (\<Union>n \<in> {n. 0 < n \<and> n \<le> length xs}. {(drop n xs, Incomplete)})
        \<union> ((\<lambda>(a, b). (a @ xs, b)) ` f s)"
  apply (simp add: put_trace_eq_drop bind_def)
  apply (safe; (clarsimp split: if_split_asm)?;
      fastforce intro: bexI[where x=0] rev_bexI)
  done

lemma if_fun_lift:
  "(if P then f else g) x = (if P then f x else g x)"
  by simp

lemma UN_If_distrib:
  "(\<Union>x \<in> S. if P x then A x else B x)
    = ((\<Union>x \<in> S \<inter> {x. P x}. A x) \<union> (\<Union>x \<in> S \<inter> {x. \<not> P x}. B x))"
  by (fastforce split: if_split_asm)

lemma Await_redef:
  "Await P = do
    s1 \<leftarrow> select {s. P s};
    env_steps;
    s \<leftarrow> get;
    select (if P s then {()} else {})
  od"
  apply (simp add: Await_def env_steps_def bind_assoc)
  apply (cases "{s. P s} = {}")
   apply (simp add: select_def bind_def get_def)
  apply (rule ext)
  apply (simp add: exec_get select_bind_UN put_then_get_then)
  apply (simp add: bind_promote_If2 if_fun_lift if_distrib[where f=select])
  apply (simp add: exec_put_trace cong: if_cong)
  apply (simp add: put_def bind_def select_def cong: if_cong)
  apply (strengthen equalityI)
  apply clarsimp
  apply (strengthen exI[where x="s # xs" for s xs])
  apply (strengthen exI[where x="Suc n" for n])
  apply simp
  apply blast
  done

lemma bind_apply_cong':
  "f s = f' s
    \<Longrightarrow> (\<forall>rv s'. (rv, s') \<in> mres (f s) \<longrightarrow> g rv s' = g' rv s')
    \<Longrightarrow> bind f g s = bind f' g' s"
  apply (simp add: bind_def)
  apply (rule SUP_cong; simp?)
  apply (clarsimp split: tmres.split)
  apply (drule spec2, drule mp, erule in_mres)
  apply simp
  done

lemmas bind_apply_cong = bind_apply_cong'[rule_format]

lemma select_empty_bind[simp]:
  "select {} >>= f = select {}"
  by (simp add: select_def bind_def)

lemma fail_bind[simp]:
  "fail >>= f = fail"
  by (simp add: bind_def fail_def)

lemma eq_Me_neq_Env:
  "(x = Me) = (x \<noteq> Env)"
  by (cases x; simp)

lemma validI_invariant_imp:
  assumes v: "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
    and P: "\<forall>s0 s. P s0 s \<longrightarrow> I s0"
    and R: "\<forall>s0 s. I s0 \<longrightarrow> R s0 s \<longrightarrow> I s"
    and G: "\<forall>s0 s. I s0 \<longrightarrow> G s0 s \<longrightarrow> I s"
  shows "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>\<lambda>s0 s. I s0 \<and> I s \<and> G s0 s\<rbrace>,\<lbrace>\<lambda>rv s0 s. I s0 \<and> Q rv s0 s\<rbrace>"
proof -
  { fix tr s0 i
  assume r: "rely_cond R s0 tr" and g: "guar_cond G s0 tr"
    and I: "I s0"
  hence imp: "\<forall>(_, s, s') \<in> trace_steps (rev tr) s0. I s \<longrightarrow> I s'"
    apply (clarsimp simp: guar_cond_def rely_cond_def)
    apply (drule(1) bspec)+
    apply (clarsimp simp: eq_Me_neq_Env)
    apply (metis R G)
    done
  hence "i < length tr \<longrightarrow> I (snd (rev tr ! i))"
    using I
    apply (induct i)
     apply (clarsimp simp: neq_Nil_conv[where xs="rev tr" for tr, simplified])
    apply clarsimp
    apply (drule bspec, fastforce simp add: trace_steps_nth)
    apply simp
    done
  }
  note I = this
  show ?thesis
    using v
    apply (clarsimp simp: validI_def rely_def imp_conjL)
    apply (drule spec2, drule(1) mp)+
    apply clarsimp
    apply (frule P[rule_format])
    apply (clarsimp simp: guar_cond_def trace_steps_nth I last_st_tr_def
                          hd_append last_rev[symmetric]
                          last_conv_nth rev_map)
    done
qed

lemma validI_guar_post_conj_lift:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G1\<rbrace>,\<lbrace>Q1\<rbrace>
    \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G2\<rbrace>,\<lbrace>Q2\<rbrace>
    \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>\<lambda>s0 s. G1 s0 s \<and> G2 s0 s\<rbrace>,\<lbrace>\<lambda>rv s0 s. Q1 rv s0 s \<and> Q2 rv s0 s\<rbrace>"
  apply (frule validI_prefix_closed)
  apply (subst validI_def, clarsimp simp: rely_def)
  apply (drule(3) validI_D)+
  apply (auto simp: guar_cond_def)
  done

lemmas modify_prefix_closed[simp] =
  modify_wp[THEN valid_validI_wp[OF no_trace_all(3)], THEN validI_prefix_closed]
lemmas await_prefix_closed[simp] = Await_sync_twp[THEN validI_prefix_closed]

lemma repeat_prefix_closed[intro!]:
  "prefix_closed f \<Longrightarrow> prefix_closed (repeat f)"
  apply (simp add: repeat_def)
  apply (rule prefix_closed_bind; clarsimp)
  apply (rename_tac n)
  apply (induct_tac n; simp)
  apply (auto intro: prefix_closed_bind)
  done

end
