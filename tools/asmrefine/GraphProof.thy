(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory GraphProof
imports TailrecPre GraphLangLemmas "Lib.SplitRule"
begin

declare sep_false_def[symmetric, simp del]

lemma exec_graph_step_Gamma_deterministic:
  assumes stacks: "(stack, stack') \<in> exec_graph_step Gamma"
    "(stack, stack'') \<in> exec_graph_step (adds ++ Gamma)"
  and adds: "\<forall>gf \<in> ran Gamma. \<forall>nn fname inps outps.
        (Call nn fname inps outps) \<in> ran (function_graph gf) \<longrightarrow> fname \<notin> dom adds"
  shows "stack'' = stack'"
proof -
  have adds': "\<And>fname fn fname' fn'. adds fname = Some fn \<Longrightarrow> Gamma fname' = Some fn'
    \<Longrightarrow> \<forall>x nn inps outps. function_graph fn' x \<noteq> Some (Call nn fname inps outps)"
    using adds
    by (metis ranI domI)
  show ?thesis using stacks
    by (auto simp: all_exec_graph_step_cases
            split: graph_function.split_asm dest: adds')
qed

lemmas exec_graph_step_deterministic
    = exec_graph_step_Gamma_deterministic[where adds=Map.empty, simplified]

lemma exec_graph_n_Gamma_deterministic:
  "(stack, stack') \<in> exec_graph_n Gamma n
    \<Longrightarrow> (stack, stack'') \<in> exec_graph_n (adds ++ Gamma) n
    \<Longrightarrow> \<forall>gf \<in> ran Gamma. \<forall>nn fname inps outps.
        (Call nn fname inps outps) \<in> ran (function_graph gf) \<longrightarrow> fname \<notin> dom adds
    \<Longrightarrow> stack'' = stack'"
  using exec_graph_step_Gamma_deterministic
  apply (induct n arbitrary: stack' stack'', simp_all add: exec_graph_n_def)
  apply blast
  done

lemmas exec_graph_n_deterministic
    = exec_graph_n_Gamma_deterministic[where adds=Map.empty, simplified]

lemma step_implies_continuing:
  "(stack, stack') \<in> exec_graph_step Gamma
    \<Longrightarrow> continuing stack"
  by (simp add: exec_graph_step_def continuing_def
         split: list.split_asm prod.split_asm next_node.split_asm)

lemma exec_trace_Gamma_deterministic:
  "trace \<in> exec_trace Gamma f
    \<Longrightarrow> trace' \<in> exec_trace (adds ++ Gamma) f
    \<Longrightarrow> \<forall>gf \<in> ran Gamma. \<forall>nn fname inps outps.
        (Call nn fname inps outps) \<in> ran (function_graph gf) \<longrightarrow> fname \<notin> dom adds
    \<Longrightarrow> trace 0 = trace' 0
    \<Longrightarrow> trace n = trace' n"
  apply (induct n)
   apply simp
  apply (clarsimp simp: exec_trace_def nat_trace_rel_def)
  apply (drule_tac x=n in spec)+
  apply (case_tac "trace' n", clarsimp+)
  apply (case_tac "trace (Suc n)", simp_all)
   apply (auto dest: step_implies_continuing)[1]
  apply (clarsimp simp: step_implies_continuing)
  apply (metis exec_graph_step_Gamma_deterministic)
  done

lemmas exec_trace_deterministic
    = exec_trace_Gamma_deterministic[where adds=Map.empty, simplified]

lemma exec_trace_nat_trace:
  "tr \<in> exec_trace Gamma f \<Longrightarrow> tr \<in> nat_trace_rel continuing (exec_graph_step Gamma)"
  by (clarsimp simp add: exec_trace_def)

abbreviation(input)
  "exec_double_trace Gamma1 f1 Gamma2 f2 trace1 trace2
    \<equiv> (trace1 \<in> exec_trace Gamma1 f1 \<and> trace2 \<in> exec_trace Gamma2 f2)"

definition
  trace_refine :: "bool \<Rightarrow> (state \<Rightarrow> state \<Rightarrow> bool) \<Rightarrow> trace \<Rightarrow> trace \<Rightarrow> bool"
where
  "trace_refine precise rel tr tr' = (case (trace_end tr, trace_end tr') of
      (None, None) \<Rightarrow> True
    | (_, None) \<Rightarrow> \<not> precise
    | (_, Some [(Err, _, _)]) \<Rightarrow> True
    | (Some [(Ret, st, _)], Some [(Ret, st', _)]) \<Rightarrow> rel st st'
    | _ \<Rightarrow> False)"

definition
  "switch_val f x y = (\<lambda>z. if f z then y z else x z)"

definition
  "tuple_switch vs = switch_val id (\<lambda>_. fst vs) (\<lambda>_. snd vs)"

lemma tuple_switch_simps[simp]:
  "tuple_switch vs True = snd vs"
  "tuple_switch vs False = fst vs"
  by (auto simp: tuple_switch_def switch_val_def)

definition
  "function_outputs_st f st = acc_vars (function_outputs f) st"

definition
  trace_refine2 :: "bool \<Rightarrow> graph_function \<times> graph_function
        \<Rightarrow> ((bool \<times> bool \<Rightarrow> variable list) \<Rightarrow> bool) \<Rightarrow> trace \<Rightarrow> trace \<Rightarrow> bool"
where
  "trace_refine2 precise gfs orel tr tr' = trace_refine precise (\<lambda>st st'.
        orel (switch_val fst
            (tuple_switch (acc_vars (function_inputs (fst gfs)) (fst (snd (hd (the (tr 0))))),
                function_outputs_st (fst gfs) st) o snd)
            (tuple_switch (acc_vars (function_inputs (snd gfs)) (fst (snd (hd (the (tr' 0))))),
                function_outputs_st (snd gfs) st') o snd)
            )) tr tr'"

definition
  graph_function_refine :: "bool \<Rightarrow> (string \<Rightarrow> graph_function option) \<Rightarrow> string
      \<Rightarrow> (string \<Rightarrow> graph_function option) \<Rightarrow> string
      \<Rightarrow> ((bool \<Rightarrow> variable list) \<Rightarrow> bool)
      \<Rightarrow> ((bool \<times> bool \<Rightarrow> variable list) \<Rightarrow> bool)
      \<Rightarrow> bool"
where
  "graph_function_refine precise Gamma1 f1 Gamma2 f2 irel orel
    = (\<forall>xs ys tr tr' gf gf'. tr \<in> exec_trace Gamma1 f1 \<and> tr' \<in> exec_trace Gamma2 f2
        \<and> Gamma1 f1 = Some gf \<and> tr 0 = Some [init_state f1 gf xs]
        \<and> Gamma2 f2 = Some gf' \<and> tr' 0 = Some [init_state f2 gf' ys]
        \<and> length xs = length (function_inputs gf) \<and> length ys = length (function_inputs gf')
        \<and> irel (tuple_switch (xs, ys))
        \<longrightarrow> trace_refine precise (\<lambda>st st'. orel (switch_val fst
            (tuple_switch (xs, function_outputs_st gf st) o snd)
            (tuple_switch (ys, function_outputs_st gf' st') o snd)
            )) tr tr')"

lemma graph_function_refine_trace:
  "graph_function_refine prec Gamma1 f1 Gamma2 f2 irel orel
    = (\<forall>tr tr' xs ys gf gf'. exec_double_trace Gamma1 f1 Gamma2 f2 tr tr'
        \<and> tr 0 \<noteq> None \<and> tr' 0 \<noteq> None \<and> Gamma1 f1 = Some gf \<and> Gamma2 f2 = Some gf'
        \<and> the (tr 0) = [init_state f1 gf xs] \<and> the (tr' 0) = [init_state f2 gf' ys]
        \<and> length xs = length (function_inputs gf) \<and> length ys = length (function_inputs gf')
        \<and> irel (tuple_switch (xs, ys))
        \<longrightarrow> trace_refine prec (\<lambda>st st'. orel (switch_val fst
            (tuple_switch (xs, function_outputs_st gf st) o snd)
            (tuple_switch (ys, function_outputs_st gf' st') o snd)
            )) tr tr')"
  apply (clarsimp simp: graph_function_refine_def)
  apply (simp only: ex_simps[symmetric] all_simps[symmetric]
              cong: conj_cong)
  apply auto
  done

definition
  trace_addr :: "trace \<Rightarrow> nat \<Rightarrow> next_node option"
where
  "trace_addr tr n = (case tr n of Some [(nn, _, _)] \<Rightarrow> Some nn | _ \<Rightarrow> None)"

lemma trace_addr_SomeD:
  "trace_addr tr n = Some nn \<Longrightarrow> \<exists>st g. tr n = Some [(nn, st, g)]"
  by (simp add: trace_addr_def split: option.split_asm list.split_asm prod.split_asm)

lemma trace_addr_SomeI:
  "\<exists>x. tr n = Some [(nn, x)] \<Longrightarrow> trace_addr tr n = Some nn"
  by (clarsimp simp add: trace_addr_def)

type_synonym restrs = "nat \<Rightarrow> nat set"

definition
  restrs_condition :: "trace \<Rightarrow> restrs \<Rightarrow> nat \<Rightarrow> bool"
where
  "restrs_condition tr restrs n = (\<forall>m. card {i. i < n \<and> trace_addr tr i = Some (NextNode m)} \<in> restrs m)"

definition
  succ_restrs :: "next_node \<Rightarrow> restrs \<Rightarrow> restrs"
where
  "succ_restrs nn rs = (case nn of NextNode n \<Rightarrow> rs (n := {x. x - 1 \<in> rs n}) | _ \<Rightarrow> rs)"

abbreviation
  "succ_restrs' n \<equiv> succ_restrs (NextNode n)"

definition
  pred_restrs :: "next_node \<Rightarrow> restrs \<Rightarrow> restrs"
where
  "pred_restrs nn rs = (case nn of NextNode n \<Rightarrow> rs (n := {x. Suc x \<in> rs n}) | _ \<Rightarrow> rs)"

abbreviation
  "pred_restrs' n \<equiv> pred_restrs (NextNode n)"

definition
  trace_bottom_addr :: "trace \<Rightarrow> nat \<Rightarrow> next_node option"
where
  "trace_bottom_addr tr n = (case tr n of Some [] \<Rightarrow> None
        | Some xs \<Rightarrow> Some (fst (List.last xs)) | None \<Rightarrow> None)"

definition
  double_trace_imp :: "(trace \<times> trace \<Rightarrow> bool) \<Rightarrow> (trace \<times> trace \<Rightarrow> bool)
    \<Rightarrow> (trace \<times> trace \<Rightarrow> bool)"
where "double_trace_imp P Q = (\<lambda>(tr, tr'). P (tr, tr') \<longrightarrow> Q (tr, tr'))"

type_synonym visit_addr = "bool \<times> next_node \<times> restrs"

definition
  restrs_eventually_condition :: "trace \<Rightarrow> restrs \<Rightarrow> bool"
where
  "restrs_eventually_condition tr restrs = (\<exists>n. tr n \<noteq> None
    \<and> (\<forall>m \<ge> n. restrs_condition tr restrs m))"

definition
  visit :: "trace \<Rightarrow> next_node \<Rightarrow> restrs \<Rightarrow> state option"
where
  "visit tr n restrs = (if \<exists>i. restrs_condition tr restrs i \<and> trace_addr tr i = Some n
    then Some (fst (snd (hd (the (tr (LEAST i. restrs_condition tr restrs i \<and> trace_addr tr i = Some n))))))
    else None)"

definition
  pc :: "next_node \<Rightarrow> restrs \<Rightarrow> trace \<Rightarrow> bool"
where
  "pc n restrs tr = (visit tr n restrs \<noteq> None)"

abbreviation
  "pc' n \<equiv> pc (NextNode n)"

definition
  double_visit :: "visit_addr \<Rightarrow> trace \<times> trace \<Rightarrow> state option"
where
  "double_visit = (\<lambda>(side, nn, restrs) (tr, tr').
    visit (if side then tr' else tr) nn restrs)"

definition
  double_pc :: "visit_addr \<Rightarrow> trace \<times> trace \<Rightarrow> bool"
where
  "double_pc = (\<lambda>(side, nn, restrs) (tr, tr').
    (visit (if side then tr' else tr) nn restrs) \<noteq> None)"

definition
  related_pair :: "visit_addr \<Rightarrow> (state \<Rightarrow> 'a)
    \<Rightarrow> visit_addr \<Rightarrow> (state \<Rightarrow> 'b)
    \<Rightarrow> ('a \<times> 'b \<Rightarrow> bool)
    \<Rightarrow> (trace \<times> trace) \<Rightarrow> bool"
where
  "related_pair v1 expr1 v2 expr2 rel trs
    = rel (expr1 (the (double_visit v1 trs)), expr2 (the (double_visit v2 trs)))"

abbreviation
  "equals v1 expr1 v2 expr2
    \<equiv> related_pair v1 expr1 v2 expr2 (split (=))"

abbreviation
  "equals' n1 restrs1 expr1 n2 restrs2 expr2
    \<equiv> equals (False, NextNode n1, restrs1) expr1 (True, NextNode n2, restrs2) expr2"

definition
  restr_trace_refine :: "bool \<Rightarrow> (string \<Rightarrow> graph_function option) \<Rightarrow> string
      \<Rightarrow> (string \<Rightarrow> graph_function option) \<Rightarrow> string
      \<Rightarrow> restrs \<Rightarrow> restrs
      \<Rightarrow> ((bool \<times> bool \<Rightarrow> variable list) \<Rightarrow> bool) \<Rightarrow> trace \<Rightarrow> trace \<Rightarrow> bool"
where
  "restr_trace_refine precise Gamma1 f1 Gamma2 f2 restrs1 restrs2 orel
    tr tr' = (\<forall>gf gf'. exec_double_trace Gamma1 f1 Gamma2 f2 tr tr'
        \<and> Gamma1 f1 = Some gf \<and> Gamma2 f2 = Some gf'
        \<and> (\<exists>xs. the (tr 0) = [init_state f1 gf xs]
            \<and> length xs = length (function_inputs gf))
        \<and> (\<exists>ys. the (tr' 0) = [init_state f2 gf' ys]
            \<and> length ys = length (function_inputs gf'))
        \<and> restrs_eventually_condition tr restrs1
        \<and> restrs_eventually_condition tr' restrs2
        \<longrightarrow> trace_refine2 precise (gf, gf') orel tr tr')"

definition
  restrs_list :: "(nat \<times> nat list) list \<Rightarrow> restrs"
where
  "restrs_list rs = (\<lambda>i. fold (\<lambda>(n, xs) S.
    if i = n then set xs \<inter> S else S) rs UNIV)"

definition
  fill_in_below :: "nat list \<Rightarrow> nat list"
where
  "fill_in_below xs = [0 ..< fold max (map Suc xs) 0]"

definition
  restrs_visit :: "(nat \<times> nat list) list
    \<Rightarrow> next_node \<Rightarrow> graph_function
    \<Rightarrow> (nat \<times> nat list) list"
where
  "restrs_visit xs nn gf = map (\<lambda>(m, xsf). if (nn, NextNode m) \<in> rtrancl (reachable_step' gf)
    then (m, (fill_in_below xsf)) else (m, xsf)) xs"

definition
  eqs :: "(('a \<times> (variable list \<Rightarrow> variable)) \<times> ('a \<times> (variable list \<Rightarrow> variable))) list
    \<Rightarrow> ('a \<Rightarrow> nat option) \<Rightarrow> ('a \<Rightarrow> variable list) \<Rightarrow> bool"
where
  "eqs xs lens vs = ((\<forall>((laddr, lval), (raddr, rval)) \<in> set xs. lval (vs laddr) = rval (vs raddr))
        \<and> (\<forall>addr. lens addr \<noteq> None \<longrightarrow> length (vs addr) = the (lens addr)))"

definition
  visit_restrs_preds_raw :: "next_node \<Rightarrow> restrs
    \<Rightarrow> (next_node \<times> restrs) list \<Rightarrow> bool"
where
  "visit_restrs_preds_raw nn restrs preds =
    (\<forall>tr i. trace_addr tr i = Some nn \<and> restrs_condition tr restrs i
        \<longrightarrow> (\<forall>j. trace_addr tr j = Some nn \<and> restrs_condition tr restrs j \<longrightarrow> j = i)
            \<and> (\<exists>j nn' restrs'. j < i
                \<and> (nn', restrs') \<in> set preds \<and> trace_addr tr j = Some nn'
                \<and> restrs_condition tr restrs' j))"

definition
  visit_restrs_preds :: "visit_addr \<Rightarrow> visit_addr list \<Rightarrow> bool"
where
  "visit_restrs_preds vis preds = (case vis of (side, nn, restrs)
    \<Rightarrow> (fst ` set preds \<subseteq> {side})
        \<and> visit_restrs_preds_raw nn restrs (map snd preds))"

lemma visit_known:
  "tr i = Some [(nn, st, g)]
    \<Longrightarrow> restrs_condition tr restrs i
    \<Longrightarrow> (\<forall>j < i. trace_addr tr j = Some nn \<longrightarrow> \<not> restrs_condition tr restrs j)
    \<Longrightarrow> visit tr nn restrs = Some st"
  apply (clarsimp simp: visit_def)
   apply (subst Least_equality, blast intro: trace_addr_SomeI)
   apply (blast intro: linorder_not_le[THEN iffD1])
  apply (auto simp: trace_addr_SomeI)
  done

lemma fold_invariant:
  "(\<forall>x \<in> set xs. \<forall> s. g (f x s) = g s) \<Longrightarrow> g s = v \<Longrightarrow> g (fold f xs s) = v"
  by (induct xs arbitrary: s, simp_all)

lemma var_acc_var_upd:
  "var_acc s (var_upd s' v st)
    = (if s = s' then v else var_acc s st)"
  by (cases st, simp add: var_acc_def var_upd_def)

lemma var_acc_save_vals_distinct:
  "distinct xs \<Longrightarrow> length xs = length vs
    \<Longrightarrow> map (\<lambda>i. var_acc i (save_vals xs vs st)) xs = vs"
  apply (induct xs arbitrary: vs st)
   apply simp
  apply (case_tac vs, simp_all add: save_vals_def)
  apply (rule fold_invariant)
   apply (clarsimp simp: var_acc_var_upd elim!: in_set_zipE)
  apply (simp add: var_acc_var_upd)
  done

definition
  wf_graph_function :: "graph_function \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "wf_graph_function f ilen olen = (case f of GraphFunction inputs outputs graph ep
    \<Rightarrow> distinct inputs \<and> distinct outputs \<and> length inputs = ilen \<and> length outputs = olen
        \<and> (\<forall>nn i. (nn, NextNode i) \<in> reachable_step' f \<longrightarrow> i \<in> dom graph)
        \<and> ep \<in> dom graph)"

lemma wf_graph_function_acc_vars_save_vals:
  "\<lbrakk> wf_graph_function f ilen olen; xs = function_inputs f; length vs = ilen \<rbrakk>
    \<Longrightarrow> acc_vars xs (save_vals xs vs st) = vs"
  by (cases f, simp add: acc_vars_def wf_graph_function_def
                         var_acc_save_vals_distinct)

lemma wf_graph_function_length_function_inputs:
  "wf_graph_function f ilen olen \<Longrightarrow> length (function_inputs f) = ilen"
  by (cases f, simp_all add: wf_graph_function_def)

lemma graph_function_refine_trace2:
  "Gamma1 f1 = Some gf \<Longrightarrow> wf_graph_function gf ilen1 olen1
    \<Longrightarrow> Gamma2 f2 = Some gf' \<Longrightarrow> wf_graph_function gf' ilen2 olen2
    \<Longrightarrow> graph_function_refine prec Gamma1 f1 Gamma2 f2 irel orel
    = (\<forall>tr tr'. exec_double_trace Gamma1 f1 Gamma2 f2 tr tr'
        \<and> Gamma1 f1 = Some gf \<and> Gamma2 f2 = Some gf'
        \<and> (\<exists>xs ys. the (tr 0) = [init_state f1 gf xs]
            \<and> length xs = length (function_inputs gf)
            \<and> the (tr' 0) = [init_state f2 gf' ys]
            \<and> length ys = length (function_inputs gf')
            \<and> irel (tuple_switch (xs, ys)))
        \<longrightarrow> trace_refine2 prec (gf, gf') orel tr tr')"
  apply (clarsimp simp: graph_function_refine_trace trace_refine2_def)
  apply (frule wf_graph_function_length_function_inputs[where f=gf])
  apply (frule wf_graph_function_length_function_inputs[where f=gf'])
  apply (simp add: imp_conjL)
  apply (rule arg_cong[where f=All] ext imp_cong[OF refl])+
  apply (clarsimp dest!: exec_trace_init)
  apply (safe, simp_all add: init_state_def wf_graph_function_acc_vars_save_vals)
  done

lemma exec_trace_step_reachable_induct:
  "tr \<in> exec_trace Gamma fn \<Longrightarrow> Gamma fn = Some gf
    \<Longrightarrow> trace_bottom_addr tr (Suc i) = Some addr
    \<Longrightarrow> (\<forall>n. trace_bottom_addr tr i = Some (NextNode n) \<longrightarrow> n \<in> dom (function_graph gf))
        \<longrightarrow> trace_bottom_addr tr i \<noteq> None
        \<and> (trace_bottom_addr tr i = Some addr \<and> trace_addr tr (Suc i) = None
            \<or> trace_addr tr (Suc i) = Some addr
                \<and> (the (trace_bottom_addr tr i), addr) \<in> reachable_step' gf)"
  apply (frule_tac i=i in exec_trace_invariant')
  apply (frule_tac i=i in exec_trace_step_cases)
  apply (simp add: all_exec_graph_step_cases, safe dest!: trace_addr_SomeD,
         simp_all add: trace_bottom_addr_def del: last.simps)
  apply (auto simp: exec_graph_invariant_Cons reachable_step_def
                    get_state_function_call_def
             split: graph_function.split_asm,
         auto split: next_node.splits option.split node.splits if_split_asm
               simp: trace_addr_def neq_Nil_conv)
  done

lemma exec_trace_step_reachable_induct2:
  "tr \<in> exec_trace Gamma fn \<Longrightarrow> Gamma fn = Some gf
    \<Longrightarrow> wf_graph_function gf ilen olen
    \<Longrightarrow> trace_bottom_addr tr (Suc i) = Some addr
    \<Longrightarrow> (\<forall>n. trace_bottom_addr tr i = Some (NextNode n) \<longrightarrow> n \<in> dom (function_graph gf))
        \<and> trace_bottom_addr tr i \<noteq> None
        \<and> (trace_bottom_addr tr i = Some addr \<and> trace_addr tr (Suc i) = None
            \<or> trace_addr tr (Suc i) = Some addr
                \<and> (the (trace_bottom_addr tr i), addr) \<in> reachable_step' gf)"
  apply (induct i arbitrary: addr)
   apply (frule(2) exec_trace_step_reachable_induct)
   apply (clarsimp simp: exec_trace_def trace_bottom_addr_def
                         wf_graph_function_def split: graph_function.split_asm)
  apply (frule(2) exec_trace_step_reachable_induct)
  apply atomize
  apply (case_tac "trace_bottom_addr tr (Suc i)", simp_all)
  apply clarsimp
  apply (frule_tac i=i in exec_trace_step_reachable_induct, simp)
  apply clarsimp
  apply (erule disjE, simp_all)
  apply (simp add: wf_graph_function_def split: graph_function.split_asm)
  apply auto
  done

lemma Collect_less_Suc:
  "{i. i < Suc n \<and> P i} = {i. i < n \<and> P i} \<union> (if P n then {n} else {})"
  by (auto simp: less_Suc_eq)

lemma trace_addr_trace_bottom_addr_eq:
  "trace_addr tr i = Some addr \<Longrightarrow> trace_bottom_addr tr i = Some addr"
  by (clarsimp simp: trace_bottom_addr_def dest!: trace_addr_SomeD)

lemma reachable_trace_induct:
  "tr \<in> exec_trace Gamma fname \<Longrightarrow> Gamma fname = Some f
    \<Longrightarrow> wf_graph_function f ilen olen
    \<Longrightarrow> trace_addr tr i = Some nn
    \<Longrightarrow> i + k \<le> j
    \<Longrightarrow> (\<forall>nn'. trace_bottom_addr tr (i + k) = Some nn'
        \<longrightarrow> (Some nn' \<in> trace_addr tr ` {i .. i + k})
        \<and> (nn, nn') \<in> rtrancl (reachable_step' f \<inter> {(x, y). Some x \<in> trace_addr tr ` {i ..< j}})
        \<and> (k \<noteq> 0 \<and> trace_addr tr (i + k) \<noteq> None
        \<longrightarrow> (nn, nn') \<in> trancl (reachable_step' f \<inter> {(x, y). Some x \<in> trace_addr tr ` {i ..< j}})))"
  apply (induct k)
   apply (clarsimp simp: trace_bottom_addr_def dest!: trace_addr_SomeD)
  apply clarsimp
  apply (frule(3) exec_trace_step_reachable_induct2)
  apply clarsimp
  apply (subgoal_tac "i + k \<in> {i ..< j} \<and> Suc (i + k) \<in> {i .. Suc (i + k)}")
   apply (rule conjI)
    apply (elim disjE conjE)
     apply simp
    apply (blast intro: sym)
   apply (rule conjI)
    apply (elim disjE conjE)
     apply simp
    apply (erule rtrancl_into_rtrancl)
    apply simp
   apply clarify
   apply (elim disjE conjE)
    apply simp
   apply (erule rtrancl_into_trancl1)
   apply simp
  apply simp
  done

lemma reachable_trace:
  "tr \<in> exec_trace Gamma fname \<Longrightarrow> Gamma fname = Some f
    \<Longrightarrow> wf_graph_function f ilen olen
    \<Longrightarrow> trace_addr tr i = Some nn
    \<Longrightarrow> trace_addr tr j = Some nn'
    \<Longrightarrow> i < j
    \<Longrightarrow> (nn, nn') \<in> trancl (reachable_step' f \<inter> {(x, y). Some x \<in> trace_addr tr ` {i ..< j}})"
  apply (frule(3) reachable_trace_induct[where k="j - i" and j=j])
   apply simp
  apply (clarsimp simp: trace_bottom_addr_def dest!: trace_addr_SomeD)
  done

lemma reachable_trace_eq:
  "tr \<in> exec_trace Gamma fname \<Longrightarrow> Gamma fname = Some f
    \<Longrightarrow> wf_graph_function f ilen olen
    \<Longrightarrow> trace_addr tr i = Some nn
    \<Longrightarrow> trace_addr tr j = Some nn'
    \<Longrightarrow> i \<le> j
    \<Longrightarrow> (nn, nn') \<in> rtrancl (reachable_step' f \<inter> {(x, y). Some x \<in> trace_addr tr ` {i ..< j}})"
  apply (cases "i = j", simp_all)
  apply (rule trancl_into_rtrancl)
  apply (fastforce elim: reachable_trace)
  done

lemma restrs_single_visit_neq:
  "tr \<in> exec_trace Gamma fname \<Longrightarrow> Gamma fname = Some f
    \<Longrightarrow> wf_graph_function f ilen olen
    \<Longrightarrow> trace_addr tr i = Some nn
    \<Longrightarrow> restrs_condition tr restrs i
    \<Longrightarrow> trace_addr tr j = Some nn
    \<Longrightarrow> restrs_condition tr restrs j
    \<Longrightarrow> \<forall>x. NextNode x \<in> set cuts \<longrightarrow> (\<exists>y. restrs x \<subseteq> {y})
    \<Longrightarrow> (nn, nn) \<notin> trancl (reachable_step' f \<inter> {(x, y). x \<notin> set cuts})
    \<Longrightarrow> i < j \<Longrightarrow> False"
  apply (frule(5) reachable_trace)
  apply (erule notE, erule trancl_mono)
  apply clarsimp
  apply (case_tac a, simp_all)
    apply (drule spec, drule(1) mp, clarsimp)
    apply (clarsimp simp: restrs_condition_def)
    apply (drule spec, drule(1) subsetD[rotated])+
    apply clarsimp
    apply (frule card_seteq[rotated -1, OF eq_imp_le], simp, clarsimp)[1]
    apply (blast dest: linorder_not_less[THEN iffD2])
   apply (simp add: reachable_step_def)+
  done

lemma restrs_single_visit:
  "tr \<in> exec_trace Gamma fname \<Longrightarrow> Gamma fname = Some f
    \<Longrightarrow> wf_graph_function f ilen olen
    \<Longrightarrow> trace_addr tr i = Some nn
    \<Longrightarrow> restrs_condition tr restrs i
    \<Longrightarrow> trace_addr tr j = Some nn
    \<Longrightarrow> restrs_condition tr restrs j
    \<Longrightarrow> \<forall>x. NextNode x \<in> set cuts \<longrightarrow> (\<exists>y. restrs x \<subseteq> {y})
    \<Longrightarrow> (nn, nn) \<notin> trancl (reachable_step' f \<inter> {(x, y). x \<notin> set cuts})
    \<Longrightarrow> i = j"
  by (metis restrs_single_visit_neq linorder_neq_iff)

lemma restrs_single_visit2:
  "trace_addr tr i = Some nn
    \<Longrightarrow> trace_addr tr j = Some nn
    \<Longrightarrow> tr \<in> exec_trace Gamma fname
    \<Longrightarrow> Gamma fname = Some f
    \<Longrightarrow> wf_graph_function f ilen olen
    \<Longrightarrow> restrs_condition tr restrs i
    \<Longrightarrow> restrs_condition tr restrs j
    \<Longrightarrow> \<forall>x. NextNode x \<in> set cuts \<longrightarrow> (\<exists>y. restrs x \<subseteq> {y})
    \<Longrightarrow> (nn, nn) \<notin> trancl (reachable_step' f \<inter> {(x, y). x \<notin> set cuts})
    \<Longrightarrow> i = j"
  by (metis restrs_single_visit)

lemma not_trancl_converse_step:
  "converse stp `` {y} \<subseteq> S
    \<Longrightarrow> \<forall>z \<in> S. (x, z) \<notin> rtrancl (stp \<inter> constraint)
    \<Longrightarrow> (x, y) \<notin> trancl (stp \<inter> constraint)"
  using tranclD2 by fastforce

lemma reachable_order_mono:
  "(nn, nn') \<in> rtrancl R
    \<Longrightarrow> (\<forall>(nn, nn') \<in> R. order nn \<le> order nn')
    \<Longrightarrow> order nn \<le> (order nn' :: 'a :: linorder)"
  apply (induct rule: rtrancl.induct)
   apply simp
  apply (blast intro: order_trans)
  done

lemma not_reachable_by_order:
  "(\<forall>(nn, nn') \<in> R. order nn \<le> order nn')
    \<Longrightarrow> order nn > (order nn' :: 'a :: linorder)
    \<Longrightarrow> (nn, nn') \<notin> rtrancl R"
  by (metis reachable_order_mono linorder_not_less)

lemma Collect_less_nat:
  "(n :: nat) - 1 = m
    \<Longrightarrow> {i. i < n \<and> P i} = (if n = 0 then {} else {i. i < m \<and> P i} \<union> (if P m then {m} else {}))"
  by (cases n, simp_all add: Collect_less_Suc)

lemma test_restrs_condition:
  "\<lbrakk> graph = [ 1 \<mapsto> Call (NextNode 2) ''foo'' [] [], 2 \<mapsto> Basic (NextNode 3) [], 3 \<mapsto> Basic Ret [] ];
    Gamma ''bar'' = Some (GraphFunction [] [] graph 1);
    tr \<in> exec_trace Gamma ''bar'';
    Gamma ''foo'' = Some (GraphFunction [] [] [ 1 \<mapsto> Basic Ret []] 1) \<rbrakk>
    \<Longrightarrow> restrs_condition tr (restrs_list [(1, [1])]) 5"
  apply (frule exec_trace_init, elim exE conjE)
  apply (frule_tac i=0 in exec_trace_step_cases, clarsimp)
  apply (clarsimp simp: all_exec_graph_step_cases)
  apply (frule_tac i=1 in exec_trace_step_cases, clarsimp)
  apply (clarsimp simp: all_exec_graph_step_cases upd_vars_def save_vals_def init_vars_def)
  apply (frule_tac i=2 in exec_trace_step_cases, clarsimp)
  apply (clarsimp simp: all_exec_graph_step_cases upd_vars_def save_vals_def init_vars_def TWO return_vars_def)
  apply (frule_tac i=3 in exec_trace_step_cases, clarsimp)
  apply (clarsimp simp: all_exec_graph_step_cases upd_vars_def save_vals_def init_vars_def)
  apply (frule_tac i=4 in exec_trace_step_cases, clarsimp)
  apply (clarsimp simp: all_exec_graph_step_cases upd_vars_def save_vals_def init_vars_def)
  apply (frule_tac i=5 in exec_trace_step_cases, clarsimp)
  apply (clarsimp simp: all_exec_graph_step_cases upd_vars_def save_vals_def init_vars_def)

  apply (simp add: restrs_condition_def Collect_less_nat Collect_conv_if trace_addr_def
                   restrs_list_def)
  done

primrec
  first_reached_prop :: "visit_addr list
    \<Rightarrow> (visit_addr \<Rightarrow> (trace \<times> trace) \<Rightarrow> bool)
    \<Rightarrow> (trace \<times> trace) \<Rightarrow> bool"
where
    "first_reached_prop [] p trs = False"
  | "first_reached_prop (v # vs) p trs =
    (if double_pc v trs then p v trs
        else first_reached_prop vs p trs)"

definition
  get_function_call :: "(graph_function \<times> graph_function)
    \<Rightarrow> visit_addr
    \<Rightarrow> (next_node \<times> string \<times> (state \<Rightarrow> variable) list \<times> string list) option"
where
  "get_function_call gfs x = (case x of (side, NextNode n, restrs)
    \<Rightarrow> (case function_graph (tuple_switch gfs side) n of
        Some (Call nn fname inputs outputs) \<Rightarrow> Some (nn, fname, inputs, outputs)
        | _ \<Rightarrow> None) | _ \<Rightarrow> None)"

definition
  func_inputs_match :: "(graph_function \<times> graph_function)
    \<Rightarrow> ((bool \<Rightarrow> variable list) \<Rightarrow> bool)
    \<Rightarrow> visit_addr \<Rightarrow> visit_addr
    \<Rightarrow> (trace \<times> trace) \<Rightarrow> bool"
where
  "func_inputs_match gfs rel vis1 vis2 trs = (case (get_function_call gfs vis1,
        get_function_call gfs vis2) of (Some (_, _, inputs1, _), Some (_, _, inputs2, _))
        \<Rightarrow> rel (\<lambda>x. map (\<lambda>f. f (the (double_visit (tuple_switch (vis1, vis2) x) trs)))
            (tuple_switch (inputs1, inputs2) x))
    | _ \<Rightarrow> False)"

definition
  succ_visit :: "next_node \<Rightarrow> visit_addr \<Rightarrow> visit_addr"
where
  "succ_visit nn vis = (case vis of (side, nn', restrs)
        \<Rightarrow> (side, nn', succ_restrs nn restrs))"

lemma fst_succ_visit[simp]:
  "fst (succ_visit nn v) = fst v"
  by (simp add: succ_visit_def split_def split: next_node.split)

lemma wf_graph_function_init_extract:
  "\<lbrakk> wf_graph_function f ilen olen; tr \<in> exec_trace Gamma fn; Gamma fn = Some f;
        the (tr 0) = [init_state fn f xs];
        \<forall>n. 0 \<in> restrs n; length xs = ilen \<rbrakk> \<Longrightarrow>
    acc_vars (function_inputs f) (the (visit tr (NextNode (entry_point f)) restrs)) = xs"
  apply (cases f)
  apply (frule wf_graph_function_length_function_inputs)
  apply (frule exec_trace_init)
  apply (clarsimp simp: visit_known restrs_condition_def init_state_def
                        wf_graph_function_acc_vars_save_vals)
  done

lemma exec_trace_reachable_step:
  "tr \<in> exec_trace Gamma fn \<Longrightarrow> Gamma fn = Some f
    \<Longrightarrow> trace_addr tr (Suc i) = Some nn'
    \<Longrightarrow> nn' \<noteq> Err
    \<Longrightarrow> \<exists>nn. (nn, nn') \<in> reachable_step' f"
  apply (clarsimp dest!: trace_addr_SomeD)
  apply (frule(1) exec_trace_invariant)
  apply (subgoal_tac "\<forall>stack. tr i = Some stack \<longrightarrow> exec_graph_invariant Gamma fn stack")
   prefer 2
   apply (metis exec_trace_invariant)
  apply (frule_tac i=i in exec_trace_step_cases)
  apply (rule_tac x="the (trace_bottom_addr tr i)" in exI)
  apply (clarsimp simp: all_exec_graph_step_cases)
  apply (safe, simp_all add: reachable_step_def)[1]
  apply (auto simp: exec_graph_invariant_def trace_addr_def
                    get_state_function_call_def trace_bottom_addr_def
             split: graph_function.split_asm next_node.split option.splits node.splits
                    next_node.split)
  done

lemma init_pc:
  "tr \<in> exec_trace Gamma fn \<Longrightarrow> Gamma fn = Some f
    \<Longrightarrow> tr 0 = Some [init_state fn f xs]
    \<Longrightarrow> \<forall>n. 0 \<in> restrs n
    \<Longrightarrow> wf_graph_function f ilen olen
    \<Longrightarrow> pc' (entry_point f) restrs tr"
  apply (clarsimp simp: pc_def visit_def)
  apply (rule_tac x=0 in exI)
  apply (simp add: trace_addr_SomeI init_state_def restrs_condition_def
            split: graph_function.split)
  done

lemma eqs_eq_conj_len_assert:
  "(eqs xs lens vs) = ((eqs xs lens $ vs)
    \<and> (\<forall>addr. lens addr \<noteq> None \<longrightarrow> length (vs addr) = the (lens addr)))"
  by (auto simp: eqs_def)

lemma length_acc_vars[simp]:
  "length (acc_vars vs st) = length vs"
  by (simp add: acc_vars_def)

lemma restrs_eventually_init:
  "tr \<in> exec_trace Gamma fn
    \<Longrightarrow> Gamma fn = Some f
    \<Longrightarrow> converse (reachable_step' f) `` {NextNode (entry_point f)} \<subseteq> set []
    \<Longrightarrow> rs = (restrs_list [(entry_point f, [1])])
    \<Longrightarrow> restrs_eventually_condition tr rs"
  apply (clarsimp simp: restrs_eventually_condition_def)
  apply (rule_tac x=1 in exI)
  apply (rule conjI)
   apply (clarsimp simp: exec_trace_def nat_trace_rel_def)
  apply (clarsimp simp: restrs_condition_def restrs_list_def)
  apply (subst arg_cong[where f=card and y="{0}"], simp_all)
  apply (safe, simp_all)
   apply (case_tac x, simp_all)
   apply (drule(2) exec_trace_reachable_step, simp)
   apply auto[1]
  apply (clarsimp simp: exec_trace_def trace_addr_def)
  done

lemma graph_function_restr_trace_refine:
  assumes wfs: "wf_graph_function f1 il1 ol1" "wf_graph_function f2 il2 ol2"
     and inps: "converse (reachable_step' f1) `` {NextNode (entry_point f1)} \<subseteq> set []"
               "converse (reachable_step' f2) `` {NextNode (entry_point f2)} \<subseteq> set []"
      and gfs: "Gamma1 fn1 = Some f1" "Gamma2 fn2 = Some f2"
  notes wf_facts = wf_graph_function_init_extract
                   wf_graph_function_init_extract
                   wf_graph_function_length_function_inputs
  shows "graph_function_refine prec Gamma1 fn1 Gamma2 fn2
        (eqs ieqs (Some o ils)) orel
    = (\<forall>tr tr'. related_pair (False, NextNode (entry_point f1), restrs_list [])
            (acc_vars (function_inputs f1))
            (True, NextNode (entry_point f2), restrs_list [])
            (acc_vars (function_inputs f2))
            (eqs ieqs (Some o ils) o tuple_switch) (tr, tr')
            \<and> exec_double_trace Gamma1 fn1 Gamma2 fn2 tr tr'
        \<longrightarrow> restr_trace_refine prec Gamma1 fn1 Gamma2 fn2
        (restrs_list [(entry_point f1, [1])]) (restrs_list [(entry_point f2, [1])])
            orel tr tr')"
  using wfs
  apply (simp add: graph_function_refine_trace2 gfs)
  apply (simp add: restr_trace_refine_def gfs
                   restrs_eventually_init
                   restrs_list_def split_def related_pair_def double_visit_def
                   wf_graph_function_init_extract)
  apply (rule arg_cong[where f=All] ext)+
  apply (auto simp: wf_graph_function_init_extract
                    wf_graph_function_length_function_inputs gfs
                    restrs_list_def
              cong: if_cong
             elim!: restrs_eventually_init[where Gamma=Gamma1, OF _ _ inps(1)]
                    restrs_eventually_init[where Gamma=Gamma2, OF _ _ inps(2)];
         metis)
  done

lemma restrs_list_Int:
  "restrs_list rs = (\<lambda>j. \<Inter>(n, xsf) \<in> set rs. (if j = n then set xsf else UNIV))"
  apply (induct rs rule: rev_induct)
   apply (simp add: restrs_list_def)
  apply (clarsimp simp add: restrs_list_def fun_eq_iff)
  done

lemma restrs_list_Int2:
  "restrs_list rs = (\<lambda>j. \<Inter>(_, xsf) \<in> {x \<in> set rs. fst x = j}. set xsf)"
  by (auto simp add: restrs_list_Int fun_eq_iff set_eq_iff)

lemma restrs_list_Cons:
  "restrs_list ((n, xs) # rs) = (\<lambda>j.
    if j = n then set xs \<inter> restrs_list rs j else restrs_list rs j)"
  by (simp add: restrs_list_Int fun_eq_iff)

lemma restrs_eventually_Cons:
  "restrs_eventually_condition tr ((K UNIV) (n := set xs))
    \<Longrightarrow> restrs_eventually_condition tr (restrs_list rs)
    \<Longrightarrow> restrs_eventually_condition tr (restrs_list ((n, xs) # rs))"
  apply (clarsimp simp: restrs_eventually_condition_def)
  apply (rule_tac x="max na naa" in exI)
  apply (simp add: restrs_condition_def restrs_list_Cons split: if_split_asm)
  apply (simp add: max_def)
  done

lemma ex_greatest_nat_le:
  "P j \<Longrightarrow> j \<le> n \<Longrightarrow> \<exists>k \<le> n. (\<forall>i \<in> {Suc k .. n}. \<not> P i) \<and> P k"
  apply (cases "P n")
   apply (rule_tac x=n in exI, simp)
  apply (cut_tac P="\<lambda>j. P (n - j)" and n = "n - j" in ex_least_nat_le, simp+)
  apply (clarify, rule_tac x="n - k" in exI)
  apply clarsimp
  apply (drule_tac x="n - i" in spec, simp)
  done

lemma neq_counting_le:
  assumes neq: "\<forall>i. f i \<noteq> bound"
  assumes mono: "\<forall>i. f (Suc i) \<le> Suc (f i)"
  shows "f 0 < bound \<Longrightarrow> f i < bound"
proof (induct i)
  case 0
  show ?case using 0 by simp
next
  case (Suc n)
  show ?case using neq[rule_format, of n] neq[rule_format, of "Suc n"]
      mono[rule_format, of n] Suc
    by simp
qed

lemma restrs_eventually_upt:
  "\<exists>m. card {i. i < m \<and> trace_addr tr i = Some (NextNode n)} = i \<and> tr m \<noteq> None
    \<Longrightarrow> \<forall>m. card {i. i < m \<and> trace_addr tr i = Some (NextNode n)} \<noteq> j
    \<Longrightarrow> restrs_eventually_condition tr ((\<lambda>_. UNIV) (n := {i ..< j}))"
  apply (clarsimp simp: restrs_eventually_condition_def restrs_condition_def)
  apply (rule exI, rule conjI, erule exI)
  apply (clarsimp simp: Suc_le_eq)
  apply (intro conjI impI allI)
   apply (rule card_mono)
    apply simp
   apply clarsimp
  apply (frule neq_counting_le, simp_all)
   apply (clarsimp simp: Collect_less_Suc)
  apply (drule_tac x=0 in spec, simp)
  done

lemma set_fill_in_below:
  "set (fill_in_below xs) = {k. \<exists>l. l : set xs \<and> k \<le> l}"
  apply (induct xs rule: rev_induct, simp_all add: fill_in_below_def)
  apply (simp add: set_eq_iff less_max_iff_disj less_Suc_eq_le)
  apply auto
  done

lemma restrs_visit_abstract:
  assumes dist: "distinct (map fst rs)"
  shows "restrs_list (restrs_visit rs nn gf)
    = (\<lambda>j. if (nn, NextNode j) \<in> rtrancl (reachable_step' gf)
        then {k. \<exists>l. l \<in> restrs_list rs j \<and> k \<le> l}
        else restrs_list rs j)"
proof -
  have P: "\<And>j. {x \<in> set (restrs_visit rs nn gf). fst x = j}
        = (if (nn, NextNode j) \<in> rtrancl (reachable_step' gf)
            then (\<lambda>(k, xsf). (k, fill_in_below xsf))
                ` {x \<in> set rs. fst x = j}
            else {x \<in> set rs. fst x = j})"
    by (force simp: restrs_visit_def elim: image_eqI[rotated])
  show ?thesis
    apply (rule ext, clarsimp simp: restrs_list_Int2 split_def P)
    apply (cut_tac dist[THEN set_map_of_compr])
    apply (case_tac "\<exists>b. (j, b) \<in> set rs")
     apply (auto simp: set_fill_in_below)
    done
qed

lemma last_upd_stack:
  "List.last (upd_stack nn stf xs)
    = (if length xs = 1 then (nn, stf (fst (snd (hd xs))), snd (snd (hd xs)))
        else List.last xs)"
  by (cases xs, simp_all)

lemma not_reachable_visits_same:
  "tr \<in> exec_trace Gamma fn \<Longrightarrow> Gamma fn = Some gf
    \<Longrightarrow> trace_addr tr i = Some n
    \<Longrightarrow> (n, m) \<notin> rtrancl (reachable_step' gf)
    \<Longrightarrow> wf_graph_function gf ilen olen
    \<Longrightarrow> j > i
    \<Longrightarrow> {k. k < j \<and> trace_addr tr k = Some m} = {k. k < i \<and> trace_addr tr k = Some m}"
  using reachable_trace_eq[THEN subsetD[OF rtrancl_mono, OF Int_lower1]]
  apply (safe, simp_all)
  apply (rule ccontr, clarsimp simp: linorder_not_less)
  done

lemma not_reachable_visits_same_symm:
  "tr \<in> exec_trace Gamma fn \<Longrightarrow> Gamma fn = Some gf
    \<Longrightarrow> trace_addr tr i = Some n
    \<Longrightarrow> trace_addr tr j = Some n
    \<Longrightarrow> (n, m) \<notin> rtrancl (reachable_step' gf)
    \<Longrightarrow> wf_graph_function gf ilen olen
    \<Longrightarrow> {k. k < j \<and> trace_addr tr k = Some m} = {k. k < i \<and> trace_addr tr k = Some m}"
  using linorder_neq_iff[where x=i and y=j] not_reachable_visits_same
  by blast

lemma restrs_eventually_at_visit:
  "restrs_eventually_condition tr (restrs_list rs)
    \<Longrightarrow> trace_addr tr i = Some nn
    \<Longrightarrow> tr \<in> exec_trace Gamma fn \<Longrightarrow> Gamma fn = Some gf
    \<Longrightarrow> distinct (map fst rs)
    \<Longrightarrow> wf_graph_function gf ilen olen
    \<Longrightarrow> restrs_condition tr (restrs_list (restrs_visit rs nn gf)) i"
  apply (clarsimp simp: restrs_eventually_condition_def
                        restrs_condition_def restrs_visit_abstract)
  apply (case_tac "i \<ge> n")
   apply (drule spec, drule(1) mp)
   apply auto[1]
  apply (simp add: linorder_not_le)
  apply (drule spec, drule mp, rule order_refl)
  apply safe
   apply (fastforce intro: card_mono)
  apply (simp add: not_reachable_visits_same[symmetric])
  done

lemma fold_double_trace_imp:
  "fold double_trace_imp hyps hyp trs
    = ((\<forall>h \<in> set hyps. h trs) \<longrightarrow> hyp trs)"
  apply (induct hyps arbitrary: hyp, simp_all)
  apply (auto simp add: double_trace_imp_def)
  done

lemma exec_trace_addr_Suc:
  "tr \<in> exec_trace Gamma f \<Longrightarrow> trace_addr tr n = Some (NextNode m) \<Longrightarrow> tr (Suc n) \<noteq> None"
  apply (drule_tac i=n in exec_trace_step_cases)
  apply (auto dest!: trace_addr_SomeD)
  done

lemma num_visits_equals_j_first:
  "card {i. i < m \<and> trace_addr tr i = Some n} = j
    \<Longrightarrow> j \<noteq> 0
    \<Longrightarrow> \<exists>m'. trace_addr tr m' = Some n \<and> card {i. i < m' \<and> trace_addr tr i = Some n} = j - 1"
  apply (frule_tac P="\<lambda>m. card {i. i < m \<and> trace_addr tr i = Some n} = j" in ex_least_nat_le)
   apply simp
  apply clarify
  apply (rule_tac x="k - 1" in exI)
  apply (case_tac k)
   apply (simp del: Collect_empty_eq)
  apply (simp add: Collect_less_Suc split: if_split_asm)
  done

lemma ex_least_nat:
  "\<exists>n. P n \<Longrightarrow> \<exists>n :: nat. P n \<and> (\<forall>i < n. \<not> P i)"
  apply clarsimp
  apply (case_tac "n = 0")
   apply fastforce
  apply (cut_tac P="\<lambda>i. i \<noteq> 0 \<and> P i" in ex_least_nat_le, auto)
  done

lemma visit_eqs:
  "(visit trace nn restrs = None)
    = (\<forall>i. trace_addr trace i = Some nn \<longrightarrow> \<not> restrs_condition trace restrs i)"
  "(visit trace nn restrs = Some st)
    = (\<exists>i. restrs_condition trace restrs i \<and> trace_addr trace i = Some nn
        \<and> st = fst (snd (hd (the (trace i))))
        \<and> (\<forall>j < i. restrs_condition trace restrs j \<longrightarrow> trace_addr trace j \<noteq> Some nn))"
  apply (simp_all add: visit_def)
   apply auto[1]
  apply (safe elim!: exE[OF ex_least_nat] del: exE, simp_all)
   apply (rule exI, rule conjI, assumption, simp)
   apply (rule arg_cong[OF Least_equality], simp)
   apply (blast intro: linorder_not_le[THEN iffD1])
  apply (rule arg_cong[OF Least_equality], simp)
  apply (blast intro: linorder_not_le[THEN iffD1])
  done

lemmas visit_eqs' = visit_eqs(1) arg_cong[where f=Not, OF visit_eqs(1), simplified]

theorem restr_trace_refine_Restr1:
  "j \<noteq> 0
    \<Longrightarrow> distinct (map fst rs1)
    \<Longrightarrow> wf_graph_function f1 ilen olen \<Longrightarrow> Gamma1 fn1 = Some f1
    \<Longrightarrow> i \<noteq> 0 \<longrightarrow>
        pc' n (restrs_list ((n, [i - 1]) # (restrs_visit rs1 (NextNode n) f1))) tr
    \<Longrightarrow> \<not> pc' n (restrs_list ((n, [j - 1]) # (restrs_visit rs1 (NextNode n) f1))) tr
    \<Longrightarrow> restr_trace_refine prec Gamma1 fn1 Gamma2 fn2 (restrs_list ((n, [i ..< j]) # rs1)) rs2 orel tr tr'
    \<Longrightarrow> restr_trace_refine prec Gamma1 fn1 Gamma2 fn2 (restrs_list rs1) rs2 orel tr tr'"
  apply (clarsimp simp: restr_trace_refine_def)
  apply (subst(asm) restrs_eventually_Cons, simp_all add: K_def)
   prefer 2
   apply auto[1]
  apply (rule restrs_eventually_upt)
   apply (clarsimp simp: fold_double_trace_imp double_trace_imp_def pc_def)
   apply (case_tac "i = 0")
    apply (rule_tac x=0 in exI)
    apply (clarsimp simp: dest!: exec_trace_init)
   apply simp
   apply (clarsimp simp: visit_eqs)
   apply (simp(no_asm_use) add: restrs_list_Cons restrs_condition_def)
   apply (drule_tac x=n in spec)+
   apply simp
   apply (rule_tac x="Suc ia" in exI, simp add: Collect_less_Suc)
   apply (rule exec_trace_addr_Suc[simplified], assumption)
   apply simp
  apply (clarsimp simp: fold_double_trace_imp double_trace_imp_def pc_def)
  apply (thin_tac "0 < i \<longrightarrow> q" for q)
  apply (clarsimp simp: visit_eqs)
  apply (frule num_visits_equals_j_first[OF refl, simplified neq0_conv])
  apply clarsimp
  apply (drule(5) restrs_eventually_at_visit)
  apply (drule_tac x=m' in spec, clarsimp)
  apply (clarsimp simp: restrs_list_Cons restrs_condition_def split: if_split_asm)
  done

theorem restr_trace_refine_Restr2:
  "j \<noteq> 0
    \<Longrightarrow> distinct (map fst rs2)
    \<Longrightarrow> wf_graph_function f2 ilen olen \<Longrightarrow> Gamma2 fn2 = Some f2
    \<Longrightarrow> i \<noteq> 0 \<longrightarrow> pc' n (restrs_list ((n, [i - 1]) # (restrs_visit rs2 (NextNode n) f2))) tr'
    \<Longrightarrow> \<not> pc' n (restrs_list ((n, [j - 1]) # (restrs_visit rs2 (NextNode n) f2))) tr'
    \<Longrightarrow> restr_trace_refine prec Gamma1 fn1 Gamma2 fn2 rs1 (restrs_list ((n, [i ..< j]) # rs2)) orel tr tr'
    \<Longrightarrow> restr_trace_refine prec Gamma1 fn1 Gamma2 fn2 rs1 (restrs_list rs2) orel tr tr'"
  apply (clarsimp simp: restr_trace_refine_def)
  apply (subst(asm) restrs_eventually_Cons, simp_all add: K_def)
   prefer 2
   apply auto[1]
  apply (rule restrs_eventually_upt)
   apply (clarsimp simp: fold_double_trace_imp double_trace_imp_def pc_def)
   apply (case_tac "i = 0")
    apply (rule_tac x=0 in exI)
    apply (clarsimp dest!: exec_trace_init)
   apply simp
   apply (clarsimp simp: visit_eqs restrs_list_Cons restrs_condition_def)
   apply (drule_tac x=n in spec)+
   apply simp
   apply (rule_tac x="Suc ia" in exI, simp add: Collect_less_Suc)
   apply (rule exec_trace_addr_Suc[simplified], assumption)
   apply simp
  apply (clarsimp simp: fold_double_trace_imp double_trace_imp_def pc_def)
  apply (thin_tac "0 < i \<longrightarrow> q" for q)
  apply (clarsimp simp: visit_eqs)
  apply (frule num_visits_equals_j_first[OF refl, simplified neq0_conv])
  apply clarsimp
  apply (drule(5) restrs_eventually_at_visit)
  apply (drule_tac x=m' in spec, clarsimp)
  apply (clarsimp simp: restrs_list_Cons restrs_condition_def split: if_split_asm)
  done

lemma pc_Ret_Err_trace_end:
  "er \<in> {Ret, Err} \<Longrightarrow> pc er restrs tr
    \<Longrightarrow> tr \<in> exec_trace Gamma f
    \<Longrightarrow> \<exists>st g. trace_end tr = Some [(er, st, g)]"
  apply (clarsimp simp: pc_def visit_eqs trace_end_def dest!: trace_addr_SomeD)
  apply (frule_tac i=i in exec_trace_step_cases, simp add: all_exec_graph_step_cases)
  apply (cut_tac tr=tr and n="Suc i" in trace_None_dom_subset)
    apply (auto simp add: exec_trace_def)[2]
  apply (subst Max_eqI[rotated 2], erule domI)
    apply (simp add: finite_subset)
   apply (simp add: subset_iff less_Suc_eq_le)
  apply auto[1]
  done

lemmas pc_Ret_trace_end = pc_Ret_Err_trace_end[where er=Ret, simplified]

lemma exec_trace_end_SomeD:
  "trace_end tr = Some v \<Longrightarrow> tr \<in> exec_trace Gamma f
    \<Longrightarrow> \<exists>n. tr n = Some v \<and> tr (Suc n) = None
        \<and> (\<exists>nn st g. v = [(nn, st, g)] \<and> nn \<in> {Ret, Err})"
  apply (frule exec_trace_nat_trace)
  apply (drule(1) trace_end_SomeD)
  apply clarsimp
  apply (frule_tac i=n in exec_trace_Nil)
  apply (case_tac "fst (hd v)", auto simp add: continuing_def split: list.split_asm)
  done

lemma reachable_from_Ret:
  "((Ret, nn) \<notin> reachable_step' gf)"
  by (simp add: reachable_step_def)

lemma trace_end_visit_Ret:
  "tr n = Some [(Ret, st, g)] \<Longrightarrow> tr (Suc n) = None
    \<Longrightarrow> tr \<in> exec_trace Gamma gf
    \<Longrightarrow> restrs_eventually_condition tr rs
    \<Longrightarrow> visit tr Ret rs = Some st"
  apply (rule visit_known, assumption)
   apply (clarsimp simp: restrs_eventually_condition_def)
   apply (drule spec, erule mp)
   apply (clarsimp simp: exec_trace_def)
   apply (drule(1) trace_None_dom_subset)
   apply auto[1]
  apply (clarsimp dest!: trace_addr_SomeD)
  apply (frule_tac i=j in exec_trace_step_cases, simp add: all_exec_graph_step_cases)
  apply (clarsimp simp: exec_trace_def)
  apply (auto dest!: trace_None_dom_subset)
  done

definition
  "output_rel orel gfs restrs trs =
    orel (\<lambda>(x, y). acc_vars (tuple_switch (function_inputs, function_outputs) y
                (tuple_switch gfs x))
            (the (double_visit (x, tuple_switch (NextNode (entry_point (tuple_switch gfs x)), Ret) y,
                tuple_switch (restrs_list [], tuple_switch restrs x) y) trs)))"

theorem restr_trace_refine_Leaf:
  "wf_graph_function f1 ilen1 olen1 \<Longrightarrow> Gamma1 fn1 = Some f1
    \<Longrightarrow> wf_graph_function f2 ilen2 olen2 \<Longrightarrow> Gamma2 fn2 = Some f2
    \<Longrightarrow> pc Ret rs1 tr \<Longrightarrow> prec \<longrightarrow> pc Ret rs2 tr'
    \<Longrightarrow> output_rel orel (f1, f2) (rs1, rs2) (tr, tr')
    \<Longrightarrow> restr_trace_refine prec Gamma1 fn1 Gamma2 fn2 rs1 rs2 orel tr tr'"
  apply (clarsimp simp only: restr_trace_refine_def)
  apply (clarsimp simp: trace_refine2_def trace_refine_def)
  apply (frule(1) pc_Ret_trace_end)
  apply (case_tac "trace_end tr'")
   apply (clarsimp split: option.split)
   apply (cut_tac tr=tr' in pc_Ret_trace_end, blast, assumption+)
   apply clarsimp
  apply (clarsimp simp: output_rel_def)
  apply (drule(1) exec_trace_end_SomeD)+
  apply (safe del: impCE, simp_all)
  apply (erule rsubst[where P=orel], rule ext)
  apply (clarsimp simp: tuple_switch_def switch_val_def double_visit_def
                        wf_graph_function_init_extract restrs_list_def
                        wf_graph_function_length_function_inputs
                        function_outputs_st_def trace_end_visit_Ret
                        init_state_def wf_graph_function_acc_vars_save_vals)
  done

lemma first_reached_propD:
  "first_reached_prop addrs propn trs
    \<Longrightarrow> \<exists>addr \<in> set addrs. propn addr trs
    \<and> (\<forall>propn. first_reached_prop addrs propn trs = propn addr trs)"
  by (induct addrs, simp_all split: if_split_asm)

lemma double_pc_reds:
  "double_pc (False, nn, restrs) trs = pc nn restrs (fst trs)"
  "double_pc (True, nn, restrs) trs = pc nn restrs (snd trs)"
  by (simp_all add: double_pc_def pc_def split_def)

definition
  merge_opt :: "'a option \<Rightarrow> 'a option \<Rightarrow> 'a option"
where
  "merge_opt opt opt' = case_option opt' Some opt"

lemma merge_opt_simps[simp]:
  "merge_opt (Some x) v = Some x"
  "merge_opt None v = v"
  by (simp_all add: merge_opt_def)

lemma fold_merge_opt_Nones_eq:
  "(\<forall>v \<in> set xs. v = None) \<Longrightarrow> fold merge_opt xs v = v"
  by (induct xs, simp_all)

lemma set_zip_rev:
  "length xs = length ys \<Longrightarrow> set (zip xs ys) = set (zip (rev xs) (rev ys))"
  by (simp add: zip_rev)

lemma exec_trace_non_Call:
  "\<lbrakk> tr \<in> exec_trace Gamma fn; Gamma fn = Some f;
        trace_bottom_addr tr i = Some (NextNode n);
        function_graph f n = Some node;
        case node of Call _ _ _ _ \<Rightarrow> False | _ \<Rightarrow> True
    \<rbrakk> \<Longrightarrow> trace_addr tr i = Some (NextNode n)"
  apply (clarsimp simp: trace_bottom_addr_def split: option.split_asm)
  apply (frule(1) exec_trace_invariant)
  apply (clarsimp simp: exec_graph_invariant_def neq_Nil_conv)
  apply (case_tac "tl (the (tr i))" rule: rev_cases)
   apply (clarsimp simp: trace_addr_SomeI)
  apply (clarsimp simp: get_state_function_call_def split: node.split_asm)
  done

lemma visit_immediate_pred:
  "\<lbrakk> tr \<in> exec_trace Gamma fn; Gamma fn = Some f; wf_graph_function f ilen olen;
        trace_addr tr i = Some nn; nn \<noteq> NextNode (entry_point f);
        converse (reachable_step' f) `` {nn} \<subseteq> S \<rbrakk>
    \<Longrightarrow> \<exists>i' nn'. i = Suc i' \<and> nn' \<in> S \<and> trace_bottom_addr tr i' = Some nn'"
  apply (case_tac i)
   apply (clarsimp dest!: exec_trace_init trace_addr_SomeD)
  apply (rename_tac i')
  apply (frule trace_addr_SomeD, clarsimp)
  apply (frule(1) exec_trace_invariant)
  apply (frule_tac i=i' in exec_trace_step_reachable_induct2, assumption+)
   apply (simp add: trace_bottom_addr_def)
  apply auto
  done



lemma pred_restrs:
  "\<lbrakk> tr \<in> exec_trace Gamma f; trace_bottom_addr tr i = Some nn \<rbrakk>
    \<Longrightarrow> restrs_condition tr restrs (Suc i)
        = restrs_condition tr (if trace_addr tr i = None then restrs
            else pred_restrs nn restrs) i"
  apply (clarsimp simp: restrs_condition_def Collect_less_Suc all_conj_distrib
                        pred_restrs_def
                 split: if_split_asm next_node.split)
  apply (auto simp: trace_addr_trace_bottom_addr_eq)
  done

lemma visit_merge:
  assumes tr: "tr \<in> exec_trace Gamma fn" "Gamma fn = Some f"
      and wf: "wf_graph_function f ilen olen"
      and ns: "nn \<noteq> NextNode (entry_point f)"
        "\<forall>n \<in> set ns. graph n = Some (Basic nn [])"
        "converse (reachable_step graph) `` {nn} \<subseteq> NextNode ` set ns"
     and geq: "function_graph f = graph"
     and cut: "\<forall>x. NextNode x \<in> set cuts \<longrightarrow> (\<exists>y. restrs x \<subseteq> {y})"
              "\<forall>n \<in> set ns. (nn, NextNode n) \<notin> rtrancl
                      (reachable_step graph \<inter> {(x, y). x \<notin> set cuts})"
  shows "visit tr nn restrs = fold merge_opt (map (\<lambda>n. visit tr (NextNode n)
            (pred_restrs' n restrs)) ns) None"
proof -
  note ns = ns[folded geq]
  note cut = cut[folded geq]

  have step_after:
    "\<And>n i. n \<in> set ns \<Longrightarrow> trace_bottom_addr tr i = Some (NextNode n)
        \<Longrightarrow> \<exists>st. tr i = Some [(NextNode n, st, fn)]
            \<and> tr (Suc i) = Some [(nn, st, fn)]
            \<and> trace_addr tr (Suc i) = Some nn
            \<and> restrs_condition tr restrs (Suc i)
                = restrs_condition tr (pred_restrs' n restrs) i"
    apply (drule exec_trace_non_Call[OF tr], (simp add: ns)+)
    apply (frule ns[rule_format], cut_tac tr(2))
    apply (frule trace_addr_SomeD, clarsimp)
    apply (frule exec_trace_invariant[OF tr(1)])
    apply (cut_tac i=i in exec_trace_step_cases[OF tr(1)])
    apply (clarsimp simp: all_exec_graph_step_cases exec_graph_invariant_Cons
                          upd_vars_def save_vals_def)
    apply (simp add: pred_restrs[OF tr(1)] trace_addr_SomeI trace_bottom_addr_def K_def)
    done
  have step_after_single:
    "\<And>n i. n \<in> set ns \<Longrightarrow> trace_bottom_addr tr i = Some (NextNode n)
        \<Longrightarrow> restrs_condition tr restrs (Suc i)
        \<Longrightarrow> (\<forall>n' j. n' \<in> set ns \<longrightarrow> trace_addr tr j = Some (NextNode n')
                \<longrightarrow> restrs_condition tr (pred_restrs' n' restrs) j \<longrightarrow> j = i)"
    apply clarsimp
    apply (frule step_after, erule trace_addr_trace_bottom_addr_eq)
    apply (frule(1) step_after)
    apply clarsimp
    apply (drule(2) restrs_single_visit[OF tr wf _ _ _ _ cut(1)], simp_all)
    apply (rule not_trancl_converse_step, rule ns)
    apply (simp add: cut)
    done
  have visit_after:
    "\<And>n v. n \<in> set ns \<Longrightarrow> visit tr (NextNode n) (pred_restrs' n restrs) = Some v
        \<Longrightarrow> visit tr nn restrs \<noteq> None"
    apply (clarsimp simp: visit_eqs)
    apply (drule_tac i=i in step_after, simp add: trace_addr_trace_bottom_addr_eq)
    apply (rule_tac x="Suc i" in exI)
    apply clarsimp
    done
  show ?thesis
    apply (rule sym, cases "visit tr nn restrs", simp_all)
     apply (rule fold_merge_opt_Nones_eq)
     apply (rule ccontr, clarsimp simp: visit_after)
    apply (clarsimp simp: visit_eqs)
    apply (frule visit_immediate_pred[OF tr wf _ ns(1, 3)])
    apply clarsimp
    apply (frule(1) step_after, clarsimp)
    apply (frule(2) step_after_single)
    apply (drule in_set_conv_decomp_last[THEN iffD1])
    apply clarsimp
    apply (rule trans, rule fold_merge_opt_Nones_eq)
     apply (rule ccontr, clarsimp simp: visit_eqs pc_def ball_Un)
     apply (simp add: trace_addr_SomeI)
    apply (subst visit_known, assumption, simp_all)
    apply clarsimp
    done
qed

lemma visit_merge_restrs:
  assumes tr: "tr \<in> exec_trace Gamma fn" "Gamma fn = Some gf"
     and geq: "function_graph gf = graph"
  assumes indep: "opt \<notin> set (opt2 # opts)"
  assumes reach: "(nn, NextNode addr) \<notin> rtrancl (reachable_step graph)"
         and wf: "wf_graph_function gf ilen olen"
  fixes rs
  defines "rs1 \<equiv> restrs_list ((addr, [opt]) # rs)"
      and "rs2 \<equiv> restrs_list ((addr, opt2 # opts) # rs)"
      and "rs3 \<equiv> restrs_list ((addr, opt # opt2 # opts) # rs)"
  shows
  "visit tr nn rs3
    = merge_opt (visit tr nn rs1) (visit tr nn rs2)"
proof -
  let ?card = "\<lambda>i. card {j. j < i \<and> trace_addr tr j = Some (NextNode addr)}"
  obtain n where vis: "\<forall>i. trace_addr tr i = Some nn \<longrightarrow> ?card i = n"
    apply (case_tac "\<exists>i. trace_addr tr i = Some nn")
     apply clarsimp
     apply (erule_tac x="?card i" in meta_allE)
     apply (erule meta_mp)
     apply clarsimp
     apply (auto dest: not_reachable_visits_same_symm[OF tr _ _ reach[folded geq] wf])
    done
  have indep2: "\<forall>i. restrs_condition tr rs1 i
    \<longrightarrow> \<not> restrs_condition tr rs2 i"
    using indep
    apply (clarsimp, clarsimp simp: restrs_condition_def rs1_def rs2_def restrs_list_Cons)
    apply (drule_tac x=addr in spec)+
    apply (clarsimp simp: restrs_list_def)
    done
  have disj:
    "\<forall>i. restrs_condition tr rs3 i
        = (restrs_condition tr rs1 i \<or> restrs_condition tr rs2 i)"
    apply (clarsimp simp: restrs_condition_def rs1_def rs2_def rs3_def restrs_list_Cons)
    apply blast
    done
  have indep3: "\<forall>j i. trace_addr tr i = Some nn \<longrightarrow> restrs_condition tr rs1 i
    \<longrightarrow> trace_addr tr j = Some nn \<longrightarrow> \<not> restrs_condition tr rs2 j"
    using indep
    apply (clarsimp, clarsimp simp: restrs_condition_def rs1_def rs2_def restrs_list_Cons)
    apply (drule_tac x=addr in spec)+
    apply (clarsimp simp: restrs_list_def vis)
    done
  show ?thesis
    unfolding visit_def
    by (auto simp: disj dest: indep3[rule_format]; metis)
qed

theorem visit_explode_restr:
  assumes gf1: "tr \<in> exec_trace Gamma fn"
    "Gamma fn = Some gf"
    "function_graph gf = graph"
  and gf2: "(nn, NextNode addr) \<notin> (reachable_step graph)\<^sup>*"
    "wf_graph_function gf ilen olen"
  and rs: "restrs_list rs addr = set xs"
    "filter (\<lambda>(addr', xs). addr' \<noteq> addr) rs = rs'"
  and xs: "distinct xs"
  shows "visit tr nn (restrs_list rs) =
        fold (\<lambda>x. merge_opt (visit tr nn (restrs_list ((addr, [x]) # rs')))) xs None"
proof -
  from rs have Q1: "restrs_list rs addr = restrs_list ((addr, rev xs) # rs') addr"
    apply (clarsimp simp: restrs_list_def fun_eq_iff)
    apply (rule fold_invariant[where g="\<lambda>x. x", symmetric], auto)
    done

  { fix addr' from rs(2) have "addr \<noteq> addr'
        \<Longrightarrow> restrs_list rs addr' = restrs_list ((addr, rev xs) # rs') addr'"
    apply clarsimp
    apply hypsubst_thin
    apply (induct rs, simp_all add: restrs_list_Cons)
    apply (clarsimp simp: restrs_list_Cons)
    done
  }
  hence Q: "restrs_list rs = restrs_list ((addr, rev xs) # rs')"
    using Q1
    apply (simp add: fun_eq_iff)
    apply metis
    done

  show "?thesis" using xs unfolding Q
    apply (induct xs rule: rev_induct)
     apply (simp add: restrs_list_Cons visit_def restrs_condition_def)
     apply metis
    apply (case_tac xs rule: rev_cases)
     apply (simp add: merge_opt_def)
    apply (clarsimp simp: visit_merge_restrs[OF gf1 _ gf2])
    done
qed

lemma visit_impossible:
  "tr \<in> exec_trace Gamma fn \<Longrightarrow> Gamma fn = Some gf
    \<Longrightarrow> function_graph gf = graph
    \<Longrightarrow> wf_graph_function gf ilen olen
    \<Longrightarrow> 0 \<notin> restrs n
    \<Longrightarrow> (NextNode n, nn) \<notin> rtrancl (reachable_step graph)
    \<Longrightarrow> visit tr nn restrs = None"
  apply (clarsimp simp: visit_eqs restrs_condition_def)
  apply (rule_tac x=n in exI)
  apply (subst arg_cong[where f=card and y="{}"], simp_all)
  apply clarsimp
  apply (drule(5) reachable_trace)
  apply (drule trancl_mono[OF _ Int_lower1])
  apply (simp add: trancl_into_rtrancl)
  done

lemma visit_inconsistent:
  "restrs i = {} \<Longrightarrow> visit tr nn restrs = None"
  by (auto simp add: visit_def restrs_condition_def)

lemma visit_immediate_pred_step:
  "tr i = Some [(nn, st, fn')]
    \<Longrightarrow> tr \<in> exec_trace Gamma fn \<Longrightarrow> Gamma fn = Some gf
    \<Longrightarrow> wf_graph_function gf ilen olen
    \<Longrightarrow> converse (reachable_step (function_graph gf)) `` {nn} \<subseteq> {NextNode n}
    \<Longrightarrow> nn \<noteq> NextNode (entry_point gf)
    \<Longrightarrow> (case (function_graph gf n) of None \<Rightarrow> False | Some (Call _ _ _ _) \<Rightarrow> False | _ \<Rightarrow> True)
    \<Longrightarrow> \<exists>i' st'. i = Suc i' \<and> fn' = fn \<and> tr i' = Some [(NextNode n, st', fn)]
      \<and> (([(NextNode n, st', fn)], [(nn, st, fn)]) \<in> exec_graph_step Gamma)"
  apply (frule(2) visit_immediate_pred[where i=i], simp_all)
   apply (simp add: trace_addr_def)
  apply (clarsimp split: option.split_asm)
  apply (frule(4) exec_trace_non_Call)
  apply (clarsimp dest!: trace_addr_SomeD)
  apply (frule_tac i=i' in exec_trace_step_cases, clarsimp)
  apply (frule_tac i=i' in exec_trace_invariant')
  apply (frule_tac i=i in exec_trace_invariant')
  apply (clarsimp simp: exec_graph_invariant_def)
  done

lemma visit_Basic:
  "tr \<in> exec_trace Gamma fn \<Longrightarrow> Gamma fn = Some gf
    \<Longrightarrow> function_graph gf = graph
    \<Longrightarrow> wf_graph_function gf ilen olen
    \<Longrightarrow> graph n = Some (Basic nn upds)
    \<Longrightarrow> converse (reachable_step graph) `` {nn} \<subseteq> {NextNode n}
    \<Longrightarrow> nn \<noteq> NextNode (entry_point gf)
    \<Longrightarrow> visit tr nn restrs = option_map (upd_vars upds)
        (visit tr (NextNode n) (pred_restrs' n restrs))"
  apply (cases "visit tr (NextNode n) (pred_restrs' n restrs)", simp_all)
   apply (clarsimp simp: visit_eqs)
   apply (frule(5) visit_immediate_pred)
   apply (clarsimp simp: pred_restrs)
   apply (frule(3) exec_trace_non_Call, simp)
   apply simp
  apply (clarsimp simp: visit_eqs)
  apply (frule trace_addr_SomeD, clarsimp)
  apply (frule_tac i=i in exec_trace_step_cases)
  apply (frule(1) exec_trace_invariant)
  apply (rule_tac x="Suc i" in exI)
  apply (clarsimp simp: all_exec_graph_step_cases exec_graph_invariant_Cons K_def)
  apply (simp add: pred_restrs[unfolded trace_bottom_addr_def] trace_addr_SomeI)
  apply clarsimp
  apply (frule(2) visit_immediate_pred, simp+)
  apply clarsimp
  apply (frule(2) exec_trace_non_Call, simp+)
  apply (clarsimp simp: pred_restrs split: if_split_asm)
  done

definition
  "option_guard guard opt = (case opt of None \<Rightarrow> None | Some v \<Rightarrow> if guard v then Some v else None)"

lemmas option_guard_simps[simp] = option_guard_def[split_simps option.split]

lemma visit_Cond:
  "tr \<in> exec_trace Gamma fn \<Longrightarrow> Gamma fn = Some gf
    \<Longrightarrow> function_graph gf = graph
    \<Longrightarrow> wf_graph_function gf ilen olen
    \<Longrightarrow> graph n = Some (Cond l r cond)
    \<Longrightarrow> converse (reachable_step graph) `` {nn} \<subseteq> {NextNode n}
    \<Longrightarrow> nn \<noteq> NextNode (entry_point gf)
    \<Longrightarrow> \<forall>x. NextNode x \<in> set cuts \<longrightarrow> (\<exists>y. pred_restrs' n restrs x \<subseteq> {y})
    \<Longrightarrow> (l, NextNode n) \<notin> rtrancl (reachable_step graph \<inter> {(x, y). x \<notin> set cuts})
    \<Longrightarrow> (r, NextNode n) \<notin> rtrancl (reachable_step graph \<inter> {(x, y). x \<notin> set cuts})
    \<Longrightarrow> visit tr nn restrs = option_guard (\<lambda>st. (nn = l \<and> cond st) \<or> (nn = r \<and> \<not> cond st))
        (visit tr (NextNode n) (pred_restrs' n restrs))"
  apply (cases "visit tr (NextNode n) (pred_restrs' n restrs)"; simp)
   apply (clarsimp simp: visit_eqs)
   apply (frule(5) visit_immediate_pred)
   apply (clarsimp simp: pred_restrs)
   apply (frule(3) exec_trace_non_Call, simp)
   apply simp
  apply (clarsimp simp: visit_eqs simp del: imp_disjL)
  apply (frule trace_addr_SomeD, clarsimp simp del: imp_disjL)
  apply (frule_tac i=i in exec_trace_step_cases)
  apply (frule(1) exec_trace_invariant)
  apply (clarsimp simp: all_exec_graph_step_cases exec_graph_invariant_Cons
              simp del: imp_disjL)
  apply (intro conjI impI)
    apply (rule_tac x="Suc i" in exI)
    apply (clarsimp simp: pred_restrs trace_bottom_addr_def)
    apply (rule conjI, simp add: trace_addr_def)
    apply clarsimp
    apply (frule(3) visit_immediate_pred, simp, simp)
    apply (clarsimp simp: pred_restrs)
    apply (frule(2) exec_trace_non_Call, simp+)[1]
   apply (rule_tac x="Suc i" in exI)
   apply (clarsimp simp: pred_restrs trace_bottom_addr_def)
   apply (rule conjI, simp add: trace_addr_def)
   apply clarsimp
   apply (frule(3) visit_immediate_pred, simp, simp)
   apply (clarsimp simp: pred_restrs)
   apply (frule(2) exec_trace_non_Call, simp+)[1]
  apply clarsimp
  apply (frule(3) visit_immediate_pred, simp, simp)
  apply (clarsimp simp: pred_restrs)
  apply (frule(2) exec_trace_non_Call, simp+)
  apply (drule(3) restrs_single_visit2, simp+)
   apply (clarsimp simp: reachable_step_def[THEN eqset_imp_iff] dest!: tranclD)
   apply auto[1]
  apply (clarsimp dest!: trace_addr_SomeD split: if_split_asm)
  done

lemma exec_trace_pc_Call:
  "pc' n restrs tr
    \<Longrightarrow> tr \<in> exec_trace Gamma fn \<Longrightarrow> Gamma fn = Some f
    \<Longrightarrow> function_graph f n = Some (node.Call nn fname inps outps)
    \<Longrightarrow> Gamma fname = Some g
    \<Longrightarrow> (\<exists>x. restrs_condition tr restrs x \<and> trace_addr tr x = Some (NextNode n)
        \<and> (trace_drop_n (Suc x) 1 tr \<in> exec_trace Gamma fname)
        \<and> visit tr (NextNode n) restrs = Some (fst (snd (hd (the (tr x))))))"
  apply (clarsimp simp: pc_def visit_eqs elim!: exE[OF ex_least_nat] del: exE)
  apply (rule exI, rule conjI, assumption, simp)
  apply (rule conjI[rotated], blast)
  apply (clarsimp dest!: trace_addr_SomeD)
  apply (frule(1) exec_trace_invariant)
  apply (simp add: exec_graph_invariant_def)
  apply (erule(4) exec_trace_drop_n[simplified])
  done

lemma exec_trace_step:
  "tr \<in> exec_trace Gamma f
    \<Longrightarrow> tr i = Some stack
    \<Longrightarrow> continuing stack
    \<Longrightarrow> \<exists>stack'. tr (Suc i) = Some stack' \<and> (stack, stack') \<in> exec_graph_step Gamma"
  apply (frule_tac i=i in exec_trace_step_cases)
  apply auto
  done

lemma trace_bottom_addr_trace_addr_prev:
  "\<lbrakk> trace_bottom_addr tr i = Some addr; restrs_condition tr restrs i;
        tr \<in> exec_trace Gamma fn; Gamma fn = Some f; wf_graph_function f ilen olen \<rbrakk>
    \<Longrightarrow> \<exists>j. trace_addr tr j = Some addr
        \<and> (i = j \<or> trace_addr tr i = None)
        \<and> (trace_addr tr ` {Suc j .. i} \<subseteq> {None})
        \<and> (trace_bottom_addr tr ` {Suc j .. i} \<subseteq> {Some addr})
        \<and> j \<le> i \<and> restrs_condition tr (if i = j then restrs else pred_restrs addr restrs) j"
  apply (induct i)
   apply (clarsimp dest!: exec_trace_init)
   apply (simp add: trace_addr_def trace_bottom_addr_def)
  apply clarsimp
  apply (case_tac "trace_addr tr (Suc i)")
   defer
   apply (auto simp: trace_addr_trace_bottom_addr_eq)[1]
  apply (subgoal_tac "trace_bottom_addr tr i = Some addr")
   apply (case_tac "trace_addr tr i")
    apply simp
    apply (drule meta_mp)
     apply (simp add: restrs_condition_def Collect_less_Suc)
    apply (clarsimp, clarsimp split: if_split_asm)
    apply (fastforce simp add: atLeastAtMostSuc_conv)
   apply (simp add: trace_addr_trace_bottom_addr_eq pred_restrs)
   apply (rule_tac x=i in exI, simp)
  apply (frule_tac i=i in exec_trace_step_cases)
  apply (elim disjE conjE)
    apply (simp add: trace_bottom_addr_def)
   apply (clarsimp simp: trace_bottom_addr_def)
  apply (clarsimp simp: all_exec_graph_step_cases)
  apply (elim disjE conjE exE, simp_all add: trace_addr_def trace_bottom_addr_def
              split: list.split_asm graph_function.split_asm if_split_asm)
  done

lemma visit_extended_pred:
  "\<lbrakk> trace_addr tr i = Some addr; restrs_condition tr restrs i;
        tr \<in> exec_trace Gamma fn; Gamma fn = Some f; wf_graph_function f ilen olen;
        converse (reachable_step' f) `` {addr} \<subseteq> S;
        addr \<noteq> NextNode (entry_point f) \<rbrakk>
    \<Longrightarrow> \<exists>j nn'. trace_addr tr j = Some nn' \<and> nn' \<in> S
        \<and> j < i
        \<and> (trace_addr tr ` {Suc j ..< i} \<subseteq> {None})
        \<and> (trace_bottom_addr tr ` {Suc j ..< i} \<subseteq> {Some nn'})
        \<and> restrs_condition tr (pred_restrs nn' restrs) j"
  apply (frule(5) visit_immediate_pred)
  apply (clarsimp simp: pred_restrs)
  apply (frule(4) trace_bottom_addr_trace_addr_prev)
  apply clarsimp
  apply (rule_tac x=j in exI, simp)
  apply (clarsimp split: if_split_asm)
  apply (simp add: atLeastLessThanSuc_atLeastAtMost)
  done

lemma if_x_None_eq_Some:
  "((if P then x else None) = Some y) = (P \<and> x = Some y)"
  by simp

lemma subtract_le_nat:
  "((a :: nat) \<le> a - b) = (a = 0 \<or> b = 0)"
  by arith

lemma bottom_addr_only:
  "trace_addr tr i = None \<Longrightarrow> trace_bottom_addr tr i = Some nn
    \<Longrightarrow> \<exists>x x' xs. tr i = Some (x # x' # xs) \<and> nn = fst (last (x' # xs))"
  apply (clarsimp simp: trace_addr_def trace_bottom_addr_def
                 split: option.split_asm list.split_asm)
  apply blast
  done

lemma extended_pred_trace_drop_n:
  "trace_addr tr i = Some (NextNode n)
    \<Longrightarrow> trace_addr tr j = Some nn
    \<Longrightarrow> tr \<in> exec_trace Gamma fn \<Longrightarrow> Gamma fn = Some f
    \<Longrightarrow> wf_graph_function f ilen olen
    \<Longrightarrow> function_graph f n = Some (Call nn fname inputs outputs)
    \<Longrightarrow> Gamma fname = Some f'
    \<Longrightarrow> i < j \<Longrightarrow> nn \<noteq> Err
    \<Longrightarrow> trace_addr tr ` {Suc i ..< j} \<subseteq> {None}
    \<Longrightarrow> trace_bottom_addr tr ` {Suc i ..< j} \<subseteq> {Some (NextNode n)}
    \<Longrightarrow> trace_drop_n (Suc i) 1 tr \<in> exec_trace Gamma fname
        \<and> Suc i < j
        \<and> (\<exists>st g. trace_drop_n (Suc i) 1 tr (j - Suc (Suc i)) = Some [(Ret, st, g)])
        \<and> trace_drop_n (Suc i) 1 tr (j - Suc i) = None"
  apply (clarsimp dest!: trace_addr_SomeD)
  apply (frule_tac i=i in exec_trace_invariant, simp)
  apply (simp add: exec_graph_invariant_Cons)
  apply (frule(3) exec_trace_drop_n, simp+)
  apply (rule context_conjI)
   apply (rule ccontr, simp add: linorder_not_less le_Suc_eq)
   apply (frule_tac i=i in exec_trace_step_cases, simp)
   apply (clarsimp simp: all_exec_graph_step_cases)
  apply (subgoal_tac "Suc (j - 2) = j - 1", simp_all)
  apply (rule context_conjI)
   prefer 2
   apply (clarsimp simp: trace_drop_n_def if_x_None_eq_Some)
   apply (rule_tac x="j - Suc (Suc i)" in exI, simp)
  apply (frule subsetD, rule_tac x="j - 1" and f="trace_addr tr" in imageI, simp)
  apply (frule subsetD, rule_tac x="j - 1" and f="trace_bottom_addr tr" in imageI, simp)
  apply (frule_tac i="j - 1" in exec_trace_step_cases)
  apply clarsimp
  apply (simp add: all_exec_graph_step_cases, safe; (solves \<open>simp add: trace_addr_def\<close>)?)
  apply (simp(no_asm) add: trace_drop_n_def if_x_None_eq_Some)
  apply clarsimp
  apply (cut_tac tr=tr and i="Suc (i + ja)" in bottom_addr_only)
    apply (simp add: image_subset_iff)
   apply (simp add: image_subset_iff)
  apply (cut_tac tr=tr and i="Suc (Suc (i + ja))" in bottom_addr_only)
    apply (simp add: image_subset_iff)
   apply (simp add: image_subset_iff)
  apply (clarsimp simp: continuing_def split: list.split next_node.split)
  apply (case_tac "drop 2 (the (tr (Suc (i + ja))))", simp_all)
  apply (frule_tac i="Suc (i + ja)" in exec_trace_step_cases)
  apply (frule_tac i="Suc (i + ja)" in exec_trace_invariant, simp)
  apply (auto simp: all_exec_graph_step_cases exec_graph_invariant_Cons
             split: graph_function.split_asm)
  done

lemma restrs_condition_no_change:
  "restrs_condition tr restrs i
    \<Longrightarrow> j \<ge> i
    \<Longrightarrow> (\<forall>k \<in> {i ..< j}. trace_addr tr k = None)
    \<Longrightarrow> restrs_condition tr restrs j"
  apply (clarsimp simp: restrs_condition_def)
  apply (rule_tac P="\<lambda>S. card S \<in> SS" for SS in subst[rotated])
   apply (erule spec)
  apply (auto intro: linorder_not_le[THEN iffD1, OF notI])
  done

lemma trace_end_exec_SomeI:
  "tr \<in> exec_trace Gamma fn
    \<Longrightarrow> tr i = Some stk
    \<Longrightarrow> tr (Suc i) = None
    \<Longrightarrow> trace_end tr = Some stk"
  apply (clarsimp simp: trace_end_def exI[where x="Suc i"])
  apply (drule(1) exec_trace_None_dom_subset)
  apply (subst Max_eqI[where x=i], auto elim: finite_subset)
  done

definition
  function_call_trace :: "nat \<Rightarrow> restrs \<Rightarrow> trace \<Rightarrow> trace option"
where
  "function_call_trace n restrs tr
    = (if pc' n restrs tr then Some (trace_drop_n
            (Suc (Least (\<lambda>i. trace_addr tr i = Some (NextNode n) \<and> restrs_condition tr restrs i))) 1 tr)
            else None)"

lemma function_call_trace_eq:
  assumes tr: "tr \<in> exec_trace Gamma fname"
    "Gamma fname = Some f"
    "wf_graph_function f ilen olen"
  and i: "trace_addr tr i = Some (NextNode n)"
    "restrs_condition tr restrs i"
  and cut: "\<forall>x. NextNode x \<in> set cuts \<longrightarrow> (\<exists>y. restrs x \<subseteq> {y})"
    "(NextNode n, NextNode n) \<notin> trancl (reachable_step' f \<inter> {(x, y). x \<notin> set cuts})"
    shows "function_call_trace n restrs tr = Some (trace_drop_n (Suc i) 1 tr)"
proof -

  have P: "\<forall>j < i. trace_addr tr j = Some (NextNode n)
       \<longrightarrow> \<not> restrs_condition tr restrs j"
    using restrs_single_visit[OF tr _ _ i cut]
    by clarsimp

  note eq = Least_equality[where x=i, OF _ ccontr, unfolded linorder_not_le]

  show ?thesis using i
    apply (clarsimp simp: function_call_trace_def pc_def visit_known P
                   dest!: trace_addr_SomeD)
    apply (subst eq, auto simp: i P)
    done
qed

definition function_call_trace_embed :: "state option \<Rightarrow> trace \<Rightarrow> trace option
    \<Rightarrow> (string \<Rightarrow> graph_function option) \<Rightarrow> string \<Rightarrow> (state \<Rightarrow> variable) list \<Rightarrow> bool"
  where "function_call_trace_embed vis tr tr' Gamma f inps
    = (((vis = None) = (tr' = None)) \<and> (\<forall>tr''. tr' = Some tr''
        \<longrightarrow> tr'' \<in> exec_trace Gamma f
            \<and> (trace_end tr'' = None \<longrightarrow> trace_end tr = None)
            \<and> (option_map (fst o hd) (trace_end tr'') = Some Err
                \<longrightarrow> option_map (fst o hd) (trace_end tr) = Some Err)
            \<and> length inps = length (function_inputs (the (Gamma f)))
            \<and> tr'' 0 = Some [init_state f (the (Gamma f)) (map (\<lambda>i. i (the vis)) inps)]))"

lemma exec_trace_Err_propagate:
  "tr \<in> exec_trace Gamma f
    \<Longrightarrow> tr i = Some ((Err, st, fname) # xs)
    \<Longrightarrow> j \<le> length xs \<Longrightarrow> tr (i + j) = Some (upd_stack Err id (drop j ((Err, st, fname) # xs)))"
  apply (induct j arbitrary: xs)
   apply simp
  apply atomize
  apply clarsimp
  apply (cut_tac xs="drop j ((Err, st, fname) # xs)" in neq_Nil_conv)
  apply clarsimp
  apply (frule_tac i="i + j" in exec_trace_step_cases)
  apply (auto simp: exec_graph_step_def drop_eq_Cons Cons_eq_append_conv
                 split: list.split_asm)
  done

lemma trace_end_trace_drop_n_Err:
  "option_map (fst o hd) (trace_end (trace_drop_n i j tr)) = Some Err
    \<Longrightarrow> tr \<in> exec_trace Gamma f
    \<Longrightarrow> trace_drop_n i j tr \<in> exec_trace Gamma f'
    \<Longrightarrow> option_map (fst o hd) (trace_end tr) = Some Err"
  apply clarsimp
  apply (drule(1) exec_trace_end_SomeD)
  apply (clarsimp simp: trace_drop_n_def[THEN fun_cong] if_x_None_eq_Some
                        drop_eq_Cons rev_swap)
  apply (frule(1) exec_trace_Err_propagate[OF _ _ order_refl])
  apply (case_tac "tl (the (tr (n + i)))" rule: rev_cases)
   apply (frule_tac i="n + i" in exec_trace_step_cases)
   apply (clarsimp simp: exec_graph_step_def trace_end_exec_SomeI)
  apply (simp add: rev_swap)
  apply (frule_tac i="n + i + length (the (tr (n + i))) - 2" in exec_trace_step_cases)
  apply (frule_tac i="n + i + length (the (tr (n + i))) - 1" in exec_trace_step_cases)
  apply (clarsimp simp: exec_graph_step_def trace_end_exec_SomeI)
  done

lemma trace_end_Nil:
  "tr \<in> exec_trace Gamma f
    \<Longrightarrow> trace_end tr \<noteq> Some []"
  by (auto dest: exec_trace_end_SomeD simp: exec_trace_Nil)

lemma visit_Call_loop_lemma:
  "(nn, NextNode n) \<notin> rtrancl (reachable_step' f \<inter> S)
    \<Longrightarrow> function_graph f n = Some (Call nn fname inputs outputs)
    \<Longrightarrow> converse (reachable_step' f) `` {nn} \<subseteq> {NextNode n}
    \<Longrightarrow> (nn, nn) \<notin> trancl (reachable_step' f \<inter> S)
        \<and> (NextNode n, NextNode n) \<notin> trancl (reachable_step' f \<inter> S)"
  apply (simp add: not_trancl_converse_step)
  apply (clarsimp simp: reachable_step_def[THEN eqset_imp_iff] dest!: tranclD)
  apply (erule disjE, simp_all)
  apply (erule converse_rtranclE, simp_all add: reachable_step_def)
  done

lemma pred_restrs_list:
  "pred_restrs nn (restrs_list xs)
    = restrs_list (map (\<lambda>(i, ns). (i, if nn = NextNode i
        then map (\<lambda>x. x - 1) (filter ((\<noteq>) 0) ns) else ns)) xs)"
  apply (clarsimp simp: pred_restrs_def split: next_node.split)
  apply (rule sym)
  apply (induct xs; simp, rule ext)
   apply (simp add: restrs_list_def)
  apply (clarsimp simp: restrs_list_Cons split del: if_split cong: if_cong)
  apply (auto intro: image_eqI[rotated])
  done

lemma pred_restrs_cut:
  "(\<exists>y. restrs x \<subseteq> {y}) \<Longrightarrow> (\<exists>y. pred_restrs nn restrs x \<subseteq> {y})"
  apply (clarsimp simp: pred_restrs_def split: next_node.split)
  apply blast
  done

lemma pred_restrs_cut2:
  "\<forall>x. NextNode x \<in> set cuts \<longrightarrow> (\<exists>y. restrs x \<subseteq> {y})
    \<Longrightarrow> \<forall>x. NextNode x \<in> set cuts \<longrightarrow> (\<exists>y. pred_restrs nn restrs x \<subseteq> {y})"
  by (metis pred_restrs_cut)

lemma visit_Call:
  "tr \<in> exec_trace Gamma fn \<Longrightarrow> Gamma fn = Some f
    \<Longrightarrow> wf_graph_function f ilen olen
    \<Longrightarrow> function_graph f n = Some (Call nn fname inputs outputs)
    \<Longrightarrow> Gamma fname = Some f'
    \<Longrightarrow> length inputs = length (function_inputs f')
    \<Longrightarrow> converse (reachable_step' f) `` {nn} \<subseteq> {NextNode n}
    \<Longrightarrow> nn \<noteq> NextNode (entry_point f) \<Longrightarrow> nn \<noteq> Err
    \<Longrightarrow> (nn, NextNode n) \<notin> rtrancl (reachable_step' f \<inter> {(x, y). x \<notin> set cuts})
    \<Longrightarrow> \<forall>x. NextNode x \<in> set cuts \<longrightarrow> (\<exists>y. restrs x \<subseteq> {y})
    \<Longrightarrow> let v = visit tr nn restrs; v' = visit tr (NextNode n) (pred_restrs' n restrs);
            tr' = function_call_trace n (pred_restrs' n restrs) tr
        in function_call_trace_embed v' tr tr' Gamma fname inputs
            \<and> v = option_map (\<lambda>st. return_vars (function_outputs f') outputs
                    (fst (snd (hd (the (trace_end (the tr')))))) st)
            (option_guard (\<lambda>_. tr' \<noteq> None \<and> trace_end (the tr') \<noteq> None
                \<and> fst (hd (the (trace_end (the tr')))) = Ret) v')"
  apply (cases "visit tr (NextNode n) (pred_restrs' n restrs)",
         simp_all split del: if_split)
   apply (clarsimp simp: visit_eqs function_call_trace_embed_def)
   apply (rule context_conjI)
    apply (clarsimp simp: function_call_trace_def pc_def visit_eqs)
   apply clarsimp
   apply (frule(6) visit_extended_pred)
   apply clarsimp
  apply (drule visit_eqs[THEN iffD1])
  apply (drule(2) visit_Call_loop_lemma)
  apply (frule_tac nn="NextNode n" in pred_restrs_cut2)
  apply (clarsimp simp: Let_def split del: if_split)
  apply (frule trace_addr_SomeD, clarsimp split del: if_split)
  apply (frule(1) exec_trace_invariant)
  apply (clarsimp simp: exec_graph_invariant_Cons split del: if_split)
  apply (frule(4) exec_trace_drop_n)
  apply (clarsimp simp: function_call_trace_eq visit_eqs Let_def
              simp del: imp_disjL split del: if_split)
  apply (rule conjI)
   apply (clarsimp simp: function_call_trace_embed_def simp del: map_option_eq_Some)
   apply (rule conjI, blast intro: trace_end_trace_drop_n_None)
   apply (rule conjI, metis trace_end_trace_drop_n_Err)
   apply (clarsimp simp: trace_drop_n_def)
   apply (frule_tac i=i in exec_trace_step_cases)
   apply (clarsimp simp: exec_graph_step_def init_state_def init_vars_def
                  split: graph_function.split_asm dest!: trace_addr_SomeD)
  apply (simp del: imp_disjL)
  apply (rule conjI)
   apply (clarsimp simp: visit_eqs)
   apply (drule(1) exec_trace_end_SomeD, clarsimp)
   apply (frule(4) exec_trace_drop_n_rest[rule_format], simp)
   apply (frule_tac i="Suc i + na" in exec_trace_step_cases)
   apply (clarsimp simp: exec_graph_step_def split: graph_function.split_asm)
   apply (subgoal_tac "restrs_condition tr restrs (Suc (Suc i + na))")
    apply (rule exI, rule conjI, assumption)
    apply (clarsimp simp: trace_addr_SomeI)
    apply (drule(2) restrs_single_visit2[OF trace_addr_SomeI, OF exI], simp+)[1]
   apply (rule_tac i="Suc i" in restrs_condition_no_change)
     apply (simp add: pred_restrs[unfolded trace_bottom_addr_def])
    apply simp
   apply clarsimp
   apply (rule ccontr, clarsimp dest!: trace_addr_SomeD)
   apply (case_tac "trace_drop_n (Suc i) 1 tr (k - Suc i)")
    apply simp
    apply (drule(1) exec_trace_None_dom_subset)+
    apply auto[1]
   apply (frule(2) exec_trace_drop_n_rest[rule_format], fastforce, assumption+)
   apply (clarsimp simp: exec_trace_Nil)
  apply (intro impI allI notI conjI)

  apply (clarsimp simp: visit_eqs)
  apply (rename_tac k)
  apply (frule(6) visit_extended_pred)
  apply clarsimp
  apply (drule(8) restrs_single_visit[rotated 3])
  apply clarsimp
  apply (frule(10) extended_pred_trace_drop_n)
  apply (clarsimp simp: trace_end_exec_SomeI Suc_diff_Suc)
  done

definition
  "double_function_call_trace vis trs = (case vis of (side, NextNode n, restrs)
        \<Rightarrow> function_call_trace n restrs (tuple_switch trs side)
    | _ \<Rightarrow> None)"

lemma double_visit_None:
  "(double_visit vis trs = None) = (\<not> double_pc vis trs)"
  by (simp add: double_pc_def double_visit_def split: prod.split)

lemma restr_trace_refine_Call_single:
  "\<not> fst ccall \<and> (\<exists>nn outps. get_function_call gfs ccall = Some (nn, cfname, cinps, outps))
    \<Longrightarrow> Gamma1 cfname = Some cf \<Longrightarrow> wf_graph_function cf cilen colen
    \<Longrightarrow> fst acall \<and> (\<exists>nn outps. get_function_call gfs acall = Some (nn, afname, ainps, outps))
    \<Longrightarrow> Gamma2 afname = Some af \<Longrightarrow> wf_graph_function af ailen aolen
    \<Longrightarrow> graph_function_refine prec Gamma1 cfname Gamma2 afname irel orel'
    \<Longrightarrow> double_pc ccall (tr, tr') \<longrightarrow> func_inputs_match gfs irel ccall acall (tr, tr')
    \<Longrightarrow> double_pc ccall (tr, tr') \<longrightarrow> double_pc acall (tr, tr')
    \<Longrightarrow> function_call_trace_embed (double_visit ccall (tr, tr')) tr
            (ctr (tr, tr')) Gamma1 cfname cinps
    \<Longrightarrow> function_call_trace_embed (double_visit acall (tr, tr')) tr'
            (ctr' (tr, tr')) Gamma2 afname ainps
    \<Longrightarrow> (double_pc ccall (tr, tr') \<longrightarrow> ctr (tr, tr') \<noteq> None \<and> ctr' (tr, tr') \<noteq> None
                  \<and> trace_end (the (ctr (tr, tr'))) \<noteq> None
                  \<and> trace_refine2 prec (cf, af) orel'
                      (the (ctr (tr, tr'))) (the (ctr' (tr, tr'))))
        \<longrightarrow> restr_trace_refine prec Gamma1 f1 Gamma2 f2 rs1 rs2 orel tr tr'
    \<Longrightarrow> restr_trace_refine prec Gamma1 f1 Gamma2 f2 rs1 rs2 orel tr tr'"
  apply (clarsimp simp: restr_trace_refine_def)
  apply (case_tac "\<not> double_pc ccall (tr, tr')")
   apply (auto simp: double_trace_imp_def)[1]
  apply (clarsimp simp: function_call_trace_embed_def double_trace_imp_def double_visit_None)
  apply (drule(4) graph_function_refine_trace2[THEN iffD1, rotated -1, rule_format])
   apply simp
   apply (rule conjI, assumption)+
   apply simp
   apply (rule exI, rule conjI, rule refl, simp)+
   apply (clarsimp simp: func_inputs_match_def)
   apply (erule rsubst[where P=irel])
   apply (rule ext, simp add: tuple_switch_def switch_val_def)
  apply (case_tac "trace_end (the (ctr (tr, tr')))")
   apply (case_tac "trace_end (the (ctr' (tr, tr')))")
    apply (clarsimp simp: trace_refine2_def trace_refine_def)
   apply (clarsimp simp: trace_refine2_def trace_refine_def)
   apply (clarsimp simp: list.split[where P="Not", THEN consume_Not_eq]
                         next_node.split[where P="Not", THEN consume_Not_eq]
                         trace_end_Nil)
   apply (drule(1) exec_trace_end_SomeD)+
   apply clarsimp
  apply clarsimp
  apply fastforce
  done

definition split_visit_rel
  where "split_visit_rel rel ccall acall j trs
    = (double_pc (ccall j) trs \<and> double_pc (acall j) trs
        \<and> rel j (\<lambda>(x, y). the (double_visit ((tuple_switch (ccall, acall) x)
            (tuple_switch (0, j) y)) trs)))"

lemma not_finite_two:
  "\<not> finite S \<Longrightarrow> \<exists>x y. x \<in> S \<and> y \<in> S \<and> x \<noteq> y"
  apply (case_tac "\<exists>x. x \<in> S")
   apply (rule ccontr, clarsimp)
   apply (erule notE, rule_tac B="{x}" in finite_subset)
    apply auto
  done

definition
  induct_var :: "next_node \<Rightarrow> nat \<Rightarrow> bool"
where
  "induct_var nn n = True"

lemma infinite_subset:
  "\<not> finite S \<Longrightarrow> S \<subseteq> T \<Longrightarrow> \<not> finite T"
  by (metis finite_subset)

lemma restr_trace_refine_Split_orig:
  fixes rs1 rs2 hyps Gamma1 f1 Gamma2 f2
  defines "H trs \<equiv>
          exec_double_trace Gamma1 f1 Gamma2 f2 (fst trs) (snd trs)
        \<and> restrs_eventually_condition (fst trs) (restrs_list rs1)
        \<and> restrs_eventually_condition (snd trs) (restrs_list rs2)"
  assumes Suc: "\<forall>i. double_pc (ccall (Suc i)) (tr, tr') \<longrightarrow> double_pc (ccall i) (tr, tr')"
  and init: "\<forall>i. i < k \<longrightarrow> H (tr, tr')
        \<longrightarrow> double_pc (ccall i) (tr, tr') \<longrightarrow> split_visit_rel rel ccall acall i (tr, tr')"
  and induct: "\<forall>i. H (tr, tr')
        \<longrightarrow> double_pc (ccall (i + k)) (tr, tr')
        \<longrightarrow> (\<forall>j < k. split_visit_rel rel ccall acall (i + j) (tr, tr'))
        \<longrightarrow> split_visit_rel rel ccall acall (i + k) (tr, tr')"
  and distinct: "\<forall>tr i j k. restrs_condition tr (snd (snd (ccall i))) k
        \<longrightarrow> restrs_condition tr (snd (snd (ccall j))) k \<longrightarrow> i = j"
      "\<forall>tr i j k. restrs_condition tr (snd (snd (acall i))) k
        \<longrightarrow> restrs_condition tr (snd (snd (acall j))) k \<longrightarrow> i = j"
  and sides: "\<forall>i. \<not> fst (ccall i) \<and> fst (acall i)"
  and k: "k \<noteq> 0"
  and init_case: "\<not> double_pc (ccall k) (tr, tr')
    \<Longrightarrow> restr_trace_refine prec Gamma1 f1 Gamma2 f2 (restrs_list rs1) (restrs_list rs2)
        orel tr tr'"
  and induct_case: "\<And>i. induct_var (fst (snd (ccall 0))) i
    \<Longrightarrow> induct_var (fst (snd (acall 0))) i
    \<Longrightarrow> \<not> double_pc (ccall (i + k)) (tr, tr')
    \<Longrightarrow> \<forall>j < k. split_visit_rel rel ccall acall (i + j) (tr, tr')
    \<Longrightarrow> restr_trace_refine prec Gamma1 f1 Gamma2 f2 (restrs_list rs1) (restrs_list rs2)
            orel tr tr'"
  shows "restr_trace_refine prec Gamma1 f1 Gamma2 f2 (restrs_list rs1) (restrs_list rs2) orel tr tr'"
proof -
  have pc_ccall_less: "double_pc (ccall n) (tr, tr')
    \<longrightarrow> m \<le> n \<longrightarrow> double_pc (ccall m) (tr, tr')" for n m
    apply (induct_tac n, simp_all)
    apply clarsimp
    apply (frule Suc[rule_format])
    apply (clarsimp simp: linorder_not_le Suc_le_eq[symmetric])
    done

  {fix i assume le[simp]: "i \<ge> k"
    note induct[rule_format, where i="i - k", simplified]
  }
  note induct_minus = this

  {fix j
  have "double_pc (ccall j) (tr, tr') \<and> H (tr, tr')
      \<longrightarrow> split_visit_rel rel ccall acall j (tr, tr')"
    apply (induct j rule: nat_less_induct)
    apply (case_tac "n < k")
     apply (simp add: init)
    apply clarsimp
    apply (rule induct_minus, simp+)
    apply (simp add: field_simps pc_ccall_less)
    done
  }
  note rel_induct = this

  note H_intro = H_def[THEN meta_eq_to_obj_eq, THEN iffD2, OF conjI]

  have Suc_Max: "finite S \<Longrightarrow> Suc (Max S) \<notin> S" for S
    by (auto dest: Max_ge)

  have unreached:
    "finite {n. \<forall>j<k. double_pc (ccall (n + j)) (tr, tr')}
        \<Longrightarrow> x \<in> {n. \<forall>j<k. double_pc (ccall (n + j)) (tr, tr')}
        \<Longrightarrow> \<not> double_pc (ccall (Max {n. \<forall>j<k. double_pc (ccall (n + j)) (tr, tr')} + k)) (tr, tr')"
    for x
    apply (frule Suc_Max)
    apply (frule Max_in, rule notI, clarsimp)
    apply clarsimp
    apply (case_tac k, simp_all)
    apply (auto dest!: less_Suc_eq[THEN iffD1])
    done

  have infinite_helper:
    "tr \<in> exec_trace G f
        \<Longrightarrow> \<forall>i j k. restrs_condition tr (snd (vis i)) k
            \<longrightarrow> restrs_condition tr (snd (vis j)) k \<longrightarrow> i = j
        \<Longrightarrow> \<not> finite {n. pc (fst (vis n)) (snd (vis n)) tr}
        \<Longrightarrow> trace_end tr = None"
    for tr G f and vis :: "'b \<Rightarrow> next_node \<times> (nat \<Rightarrow> nat set)"
    apply (clarsimp simp: trace_end_def)
    apply (drule(1) exec_trace_None_dom_subset)
    apply (drule_tac R="\<lambda>n i. restrs_condition tr (snd (vis n)) i"
           in pigeonhole_infinite_rel)
      apply (erule finite_subset, simp)
     apply (auto simp: pc_def visit_eqs dest!: trace_addr_SomeD)[1]
    apply (auto dest!: not_finite_two)
    done

  have infinite:
    "exec_double_trace Gamma1 f1 Gamma2 f2 tr tr'
        \<Longrightarrow> H (tr, tr')
        \<Longrightarrow> \<not> finite {n. \<forall>j<k. double_pc (ccall (n + j)) (tr, tr')}
        \<Longrightarrow> trace_end tr = None \<and> trace_end tr' = None"
    apply (case_tac "\<exists>n. \<not> double_pc (ccall n) (tr, tr')")
     apply clarsimp
     apply (erule notE, rule_tac k1=n in finite_subset[OF _ finite_lessThan])
     apply clarsimp
     apply (drule_tac x=0 in spec, simp add: k[simplified])
     apply (rule ccontr, simp add: pc_ccall_less)
    apply clarsimp
    apply (rule conjI)
     apply (erule_tac vis="\<lambda>i. snd (ccall i)" in infinite_helper)
      apply (simp add: distinct)
     apply (simp add: double_pc_def[folded pc_def] split_def sides)
    apply (erule_tac vis="\<lambda>i. snd (acall i)" in infinite_helper)
     apply (simp add: distinct)
    apply clarsimp
    apply (drule_tac A="UNIV" in finite_subset[rotated])
     apply clarsimp
     apply (rename_tac n, drule_tac x="n" in spec)
     apply (drule(1) rel_induct[rule_format, OF conjI])
     apply (clarsimp simp: split_visit_rel_def)
     apply (simp add: double_pc_def[folded pc_def] sides split_def)
    apply simp
    done

  show ?thesis
    apply (clarsimp simp: restr_trace_refine_def)
    apply (case_tac "\<not> double_pc (ccall k) (tr, tr')")
     apply (rule init_case[unfolded restr_trace_refine_def, rule_format],
            auto)[1]
    apply (case_tac "finite {n. \<forall>j < k. double_pc (ccall (n + j)) (tr, tr')}")
     apply (frule Max_in)
      apply simp
      apply (rule_tac x="0" in exI)
      apply (simp add: pc_ccall_less)
     apply (rule_tac i="Max {n. \<forall>j < k. double_pc (ccall (n + j)) (tr, tr')}"
         in induct_case[unfolded restr_trace_refine_def, rule_format])
         apply (simp add: induct_var_def)+
       apply (simp add: rel_induct unreached)
      apply (simp add: rel_induct unreached H_intro)
     apply auto[1]
    apply clarsimp
    apply (drule infinite[rotated -1], simp)
     apply (simp add: H_def)
    apply (simp add: trace_refine2_def trace_refine_def)
    done
qed

lemma restrs_condition_unique:
  "restrs_condition tr (restrs_list ((n, [x]) # rs)) k
    \<Longrightarrow> restrs_condition tr (restrs_list ((n, [y]) # rs)) k
    \<Longrightarrow> x = y"
  by (clarsimp simp: restrs_condition_def restrs_list_Cons
              split: if_split_asm)

abbreviation(input)
  "split_restr split_seq restrs i \<equiv> (restrs_list ((fst split_seq,
        [fst (snd split_seq) + i * snd (snd split_seq)]) # restrs))"

abbreviation(input)
  "split_pc split_seq restrs tr i
    \<equiv> pc' (fst split_seq) (split_restr split_seq restrs i) tr"

abbreviation(input)
  "split_visit split_seq restrs i tr
    \<equiv> visit tr (NextNode (fst split_seq)) (split_restr split_seq restrs i)"

definition
  split_visit_rel'
  where "split_visit_rel' rel conc_seq abs_seq restrs trs j
    = (split_pc conc_seq (fst restrs) (fst trs) j \<and> split_pc abs_seq (snd restrs) (snd trs) j
        \<and> rel j (\<lambda>(x, y). the (split_visit (tuple_switch (conc_seq, abs_seq) x)
            (tuple_switch restrs x)
            (tuple_switch (0, j) y) (tuple_switch trs x))))"

lemma split_visit_rel':
  "split_visit_rel rel (\<lambda>i. (False, NextNode (fst cseq), split_restr cseq rs1 i))
    (\<lambda>i. (True, NextNode (fst aseq), split_restr aseq rs2 i)) j trs
    = split_visit_rel' rel cseq aseq (rs1, rs2) trs j"
  apply (simp add: split_visit_rel_def split_visit_rel'_def
                   double_pc_def[folded pc_def] split_def double_visit_def)
  apply (auto elim!: rsubst[where P="rel j", OF _ ext])
  apply (auto simp: tuple_switch_def switch_val_def)
  done

theorem restr_trace_refine_Split:
  assumes Suc: "\<forall>i. split_pc conc_seq rs1 tr (Suc i) \<longrightarrow> split_pc conc_seq rs1 tr i"
  and init: "\<forall>i. i < k \<longrightarrow> split_pc conc_seq rs1 tr i
        \<longrightarrow> split_visit_rel' rel conc_seq abs_seq (rs1, rs2) (tr, tr') i"
  and induct: "\<forall>i. split_pc conc_seq rs1 tr (i + k)
        \<longrightarrow> (\<forall>j < k. split_visit_rel' rel conc_seq abs_seq (rs1, rs2) (tr, tr') (i + j))
        \<longrightarrow> split_visit_rel' rel conc_seq abs_seq (rs1, rs2) (tr, tr') (i + k)"
  and zero: "k \<noteq> 0" "snd (snd conc_seq) \<noteq> 0" "snd (snd abs_seq) \<noteq> 0"
  and init_case: "\<not> split_pc conc_seq rs1 tr k
    \<Longrightarrow> restr_trace_refine prec Gamma1 f1 Gamma2 f2 (restrs_list rs1) (restrs_list rs2)
        orel tr tr'"
  and induct_case: "\<And>i. induct_var (NextNode (fst conc_seq)) i
    \<Longrightarrow> induct_var (NextNode (fst abs_seq)) i
    \<Longrightarrow> \<not> split_pc conc_seq rs1 tr (i + k)
    \<Longrightarrow> \<forall>j < k. split_visit_rel' rel conc_seq abs_seq (rs1, rs2) (tr, tr') (i + j)
    \<Longrightarrow> restr_trace_refine prec Gamma1 f1 Gamma2 f2 (restrs_list rs1) (restrs_list rs2)
            orel tr tr'"
  shows "restr_trace_refine prec Gamma1 f1 Gamma2 f2 (restrs_list rs1) (restrs_list rs2) orel tr tr'"
  apply (rule restr_trace_refine_Split_orig[where
            ccall="\<lambda>i. (False, NextNode (fst conc_seq), split_restr conc_seq rs1 i)"
        and acall="\<lambda>i. (True, NextNode (fst abs_seq), split_restr abs_seq rs2 i)"
        and k=k and rel=rel],
         simp_all add: Suc init induct init_case induct_case zero[simplified]
                       double_pc_def[folded pc_def] split_visit_rel')
   apply (clarsimp, drule(1) restrs_condition_unique)
   apply (simp add: zero)
  apply (clarsimp, drule(1) restrs_condition_unique)
  apply (simp add: zero)
  done

theorem restr_trace_refine_Split':
  "let cpc = split_pc conc_seq rs1 tr;
        rel = split_visit_rel' rel conc_seq abs_seq (rs1, rs2) (tr, tr')
    in (\<forall>i. cpc (Suc i) --> cpc i)
    --> (\<forall>i. i < k --> cpc i --> rel i)
    --> (\<forall>i. cpc (i + k) --> (\<forall>j < k. rel (i + j)) --> rel (i + k))
    --> k \<noteq> 0 --> snd (snd conc_seq) \<noteq> 0 --> snd (snd abs_seq) \<noteq> 0
    --> (~ cpc k --> restr_trace_refine prec Gamma1 f1 Gamma2 f2
        (restrs_list rs1) (restrs_list rs2) orel tr tr')
    --> (\<forall>i. ~ cpc (i + k) --> (\<forall>j < k. rel (i + j))
        --> restr_trace_refine prec Gamma1 f1 Gamma2 f2
            (restrs_list rs1) (restrs_list rs2) orel tr tr')
    --> restr_trace_refine prec Gamma1 f1 Gamma2 f2
        (restrs_list rs1) (restrs_list rs2) orel tr tr'"
  apply (clarsimp simp only: Let_def)
  apply (erule notE, rule restr_trace_refine_Split[where conc_seq=conc_seq and abs_seq=abs_seq
      and k=k and rel=rel], simp_all)
  apply blast
  done

lemma restr_trace_refine_Restr1_offset:
  "induct_var (NextNode n) iv
    \<Longrightarrow> restr_trace_refine prec Gamma1 fn1 Gamma2 fn2 (restrs_list ((n, [iv + 1 ..< iv + j]) # rs1)) rs2 orel tr tr'
    \<Longrightarrow> j \<noteq> 0
    \<Longrightarrow> distinct (map fst rs1)
    \<Longrightarrow> wf_graph_function f1 ilen olen \<Longrightarrow> Gamma1 fn1 = Some f1
    \<Longrightarrow> pc' n (restrs_list ((n, [iv]) # (restrs_visit rs1 (NextNode n) f1))) tr
    \<Longrightarrow> \<not> pc' n (restrs_list ((n, [iv + (j - 1)]) # (restrs_visit rs1 (NextNode n) f1))) tr
    \<Longrightarrow> restr_trace_refine prec Gamma1 fn1 Gamma2 fn2 (restrs_list rs1) rs2 orel tr tr'"
  by (rule restr_trace_refine_Restr1[where i="iv + 1" and j="iv + j"], simp_all)

lemma restr_trace_refine_Restr2_offset:
  "induct_var (NextNode n) iv
    \<Longrightarrow> restr_trace_refine prec Gamma1 fn1 Gamma2 fn2 rs1 (restrs_list ((n, [iv + 1 ..< iv + j]) # rs2)) orel tr tr'
    \<Longrightarrow> j \<noteq> 0
    \<Longrightarrow> distinct (map fst rs2)
    \<Longrightarrow> wf_graph_function f2 ilen olen \<Longrightarrow> Gamma2 fn2 = Some f2
    \<Longrightarrow> pc' n (restrs_list ((n, [iv]) # (restrs_visit rs2 (NextNode n) f2))) tr'
    \<Longrightarrow> \<not> pc' n (restrs_list ((n, [iv + (j - 1)]) # (restrs_visit rs2 (NextNode n) f2))) tr'
    \<Longrightarrow> restr_trace_refine prec Gamma1 fn1 Gamma2 fn2 rs1 (restrs_list rs2) orel tr tr'"
  by (rule restr_trace_refine_Restr2[where i="iv + 1" and j="iv + j"], simp_all)

lemma restr_trace_refine_PCCases1:
  "pc nn rs1 tr
        \<longrightarrow> restr_trace_refine prec Gamma1 fn1 Gamma2 fn2 rs1 rs2 orel tr tr'
    \<Longrightarrow> \<not> pc nn rs1 tr
        \<longrightarrow> restr_trace_refine prec Gamma1 fn1 Gamma2 fn2 rs1 rs2 orel tr tr'
    \<Longrightarrow> restr_trace_refine prec Gamma1 fn1 Gamma2 fn2 rs1 rs2 orel tr tr'"
  by metis

lemma restr_trace_refine_PCCases2:
  "pc nn rs2 tr'
        \<longrightarrow> restr_trace_refine prec Gamma1 fn1 Gamma2 fn2 rs1 rs2 orel tr tr'
    \<Longrightarrow> \<not> pc nn rs2 tr'
        \<longrightarrow> restr_trace_refine prec Gamma1 fn1 Gamma2 fn2 rs1 rs2 orel tr tr'
    \<Longrightarrow> restr_trace_refine prec Gamma1 fn1 Gamma2 fn2 rs1 rs2 orel tr tr'"
  by metis

lemma restr_trace_refine_Err:
  "(\<not> pc Err restrs tr'
        \<longrightarrow> restr_trace_refine prec Gamma1 fn1 Gamma2 fn2 rs1 rs2 orel tr tr')
    \<Longrightarrow> restr_trace_refine prec Gamma1 fn1 Gamma2 fn2 rs1 rs2 orel tr tr'"
  apply (clarsimp simp: restr_trace_refine_def)
  apply (erule impCE)
   apply simp
   apply (clarsimp simp: trace_refine2_def trace_refine_def)
   apply (drule(1) pc_Ret_Err_trace_end[where er=Err, simplified])
   apply clarsimp
   apply (simp split: option.split list.split next_node.split)
  apply auto
  done

definition
  stepwise_graph_refine :: "(string \<Rightarrow> graph_function option)
      \<Rightarrow> (string list \<times> string list)
      \<Rightarrow> (next_node list \<times> next_node list)
      \<Rightarrow> (state list \<times> state list \<Rightarrow> bool)
      \<Rightarrow> ((next_node \<times> state \<times> string) \<times> (next_node \<times> state \<times> string) \<Rightarrow> bool)
      \<Rightarrow> (trace \<times> trace) option
      \<Rightarrow> nat \<Rightarrow> bool"
where
  "stepwise_graph_refine Gamma fnames nns irel orel trs n
    = (\<forall>tr tr' i j. i \<ge> n \<and> j \<ge> n \<and> tr i \<noteq> None \<and> tr' j \<noteq> None
        \<and> (map fst (the (tr i)), map fst (the (tr' j))) = nns
        \<and> (map (snd o snd) (the (tr i)), map (snd o snd) (the (tr' j))) = fnames
        \<and> irel (map (fst o snd) (the (tr i)), map (fst o snd) (the (tr' j)))
        \<and> (trs \<noteq> None \<longrightarrow> trs = Some (tr, tr'))
        \<and> tr \<in> exec_trace Gamma (last (fst fnames)) \<and> tr' \<in> exec_trace Gamma (last (snd fnames))
        \<longrightarrow> (trace_end tr = None) = (trace_end tr' = None)
            \<and> (trace_end tr \<noteq> None \<longrightarrow> orel (hd (the (trace_end tr)), hd (the (trace_end tr')))))"

lemmas stepwise_graph_refineI = stepwise_graph_refine_def[THEN iffD2, rule_format]
lemmas stepwise_graph_refineD = stepwise_graph_refine_def[THEN iffD1, rule_format]

lemma stepwise_graph_refine_Basic:
  "stepwise_graph_refine Gamma (f1 # fns, f2 # fns') (nn # nns, nn' # nns') rel orel otr (Suc N)
    \<Longrightarrow> Gamma f1 = Some gf1 \<Longrightarrow> Gamma f2 = Some gf2
    \<Longrightarrow> function_graph gf1 n = Some (Basic nn upds)
    \<Longrightarrow> function_graph gf2 n' = Some (Basic nn' upds')
    \<Longrightarrow> \<forall>x xs y ys. rel (x # xs, y # ys) \<longrightarrow> rel (upd_vars upds x # xs, upd_vars upds' y # ys)
    \<Longrightarrow> stepwise_graph_refine Gamma (f1 # fns, f2 # fns')
        (NextNode n # nns, NextNode n' # nns') rel orel otr N"
  apply (rule stepwise_graph_refineI)
  apply (erule_tac i="Suc i" and j="Suc j" in stepwise_graph_refineD)
  apply clarsimp
  apply (frule_tac i=i and tr=tr in exec_trace_step_cases)
  apply (frule_tac i=j and tr=tr' in exec_trace_step_cases)
  apply (clarsimp simp: exec_graph_step_def exec_graph_invariant_Cons split: graph_function.split_asm)
  done

lemma stepwise_graph_refine_Cond:
  "stepwise_graph_refine Gamma (f1 # fns, f2 # fns') (l # nns, l' # nns') rel orel otr (Suc N)
    \<Longrightarrow> stepwise_graph_refine Gamma (f1 # fns, f2 # fns') (r # nns, r' # nns') rel orel otr (Suc N)
    \<Longrightarrow> Gamma f1 = Some gf1 \<Longrightarrow> Gamma f2 = Some gf2
    \<Longrightarrow> function_graph gf1 n = Some (Cond l r cond)
    \<Longrightarrow> function_graph gf2 n' = Some (Cond l' r' cond')
    \<Longrightarrow> \<forall>x xs y ys. rel (x # xs, y # ys) \<longrightarrow> cond x = cond' y
    \<Longrightarrow> stepwise_graph_refine Gamma (f1 # fns, f2 # fns')
        (NextNode n # nns, NextNode n' # nns') rel orel otr N"
  apply (rule stepwise_graph_refineI)
  apply (clarsimp simp del: last.simps not_None_eq)
  apply (frule_tac i=i and tr=tr in exec_trace_step_cases)
  apply (frule_tac i=j and tr=tr' in exec_trace_step_cases)
  apply (clarsimp simp: exec_graph_step_def exec_graph_invariant_Cons
                 split: graph_function.split_asm split: if_split_asm
              simp del: last.simps not_None_eq)
     apply (simp_all only: exI all_simps[symmetric] simp_thms)
   apply (erule_tac i="Suc i" and j="Suc j"
     and nns="(l # xs, ys)" for xs ys in stepwise_graph_refineD, simp)
  apply (erule_tac i="Suc i" and j="Suc j"
    and nns="(r # xs, ys)" for xs ys in stepwise_graph_refineD, simp)
  done

lemma stepwise_graph_refine_Call_same:
  "stepwise_graph_refine Gamma (f1 # fns, f2 # fns') (nn # nns, nn' # nns') rel orel otr (Suc N)
    \<Longrightarrow> Gamma f1 = Some gf1 \<Longrightarrow> Gamma f2 = Some gf2
    \<Longrightarrow> function_graph gf1 n = Some (Call nn fname inputs outputs)
    \<Longrightarrow> function_graph gf2 n' = Some (Call nn' fname inputs' outputs')
    \<Longrightarrow> Gamma fname = Some gf3
    \<Longrightarrow> \<forall>x xs y ys. rel (x # xs, y # ys) \<longrightarrow> map (\<lambda>i. i x) inputs = map (\<lambda>i. i y) inputs'
    \<Longrightarrow> \<forall>x xs y ys zs st. rel (x # xs, y # ys)
        \<longrightarrow> rel (return_vars zs outputs st x # xs, return_vars zs outputs' st y # ys)
    \<Longrightarrow> \<forall>sts. fst (fst sts) = Err \<longrightarrow> fst (snd sts) = Err \<longrightarrow> orel sts
    \<Longrightarrow> stepwise_graph_refine Gamma (f1 # fns, f2 # fns')
        (NextNode n # nns, NextNode n' # nns') rel orel otr N"
  apply (rule stepwise_graph_refineI, clarsimp)
  apply (simp only: all_simps[symmetric])
  apply (frule(4) exec_trace_drop_n_Cons[where gf=gf1])
  apply (frule(4) exec_trace_drop_n_Cons[where gf=gf2])
  apply (frule_tac i=i and tr=tr in exec_trace_step_cases)
  apply (frule_tac i=j and tr=tr' in exec_trace_step_cases)
  apply (clarsimp simp: exec_graph_step_def init_vars_def
                 split: graph_function.split_asm)
  apply (subgoal_tac "trace_drop_n (Suc i) (length (the (tr i))) tr
    = trace_drop_n (Suc j) (length (the (tr' j))) tr'")
   apply (frule_tac f=trace_end in arg_cong)
   apply (drule fun_eq_iff[THEN iffD1])
   apply (case_tac "trace_end (trace_drop_n (Suc i) (length (the (tr i))) tr)")
    apply simp
    apply (drule(1) trace_end_trace_drop_n_None, simp)+
    apply simp
   apply clarsimp
   apply (drule(1) exec_trace_end_SomeD)+
   apply clarsimp
   apply (erule disjE)
    apply (frule_tac tr=tr and i=i and k=na in exec_trace_drop_n_rest_Cons[rule_format],
      (simp only: function_graph.simps)+)
    apply (frule_tac tr=tr' and i=j and k=na in exec_trace_drop_n_rest_Cons[rule_format],
      (simp only: function_graph.simps)+)
    apply (frule_tac i="Suc i + na" and tr=tr in exec_trace_step_cases)
    apply (frule_tac i="Suc j + na" and tr=tr' in exec_trace_step_cases)
    apply (clarsimp simp: field_simps exec_graph_step_def)
    apply (drule_tac tr=tr and tr'=tr' and i="i + na + 2" and j="j + na + 2"
      in stepwise_graph_refineD)
     apply (simp add: )
     apply auto[1]
    apply auto[1]
   apply (drule(1) trace_end_trace_drop_n_Err[rotated], simp add: trace_end_exec_SomeI)+
   apply (case_tac "hd (the (trace_end tr))")
   apply (case_tac "hd (the (trace_end tr'))")
   apply clarsimp
  apply (rule ext)
  apply (rule exec_trace_deterministic, simp+)
  apply (simp add: trace_drop_n_def)
  apply (simp only: all_simps[symmetric])
  done

lemma stepwise_graph_refine_nop_left:
  "stepwise_graph_refine Gamma (f1 # fns, fns') (nn # nns, nns') rel orel otr N
    \<Longrightarrow> Gamma f1 = Some gf1
    \<Longrightarrow> function_graph gf1 n = Some (Basic nn [])
    \<Longrightarrow> stepwise_graph_refine Gamma (f1 # fns, fns')
        (NextNode n # nns, nns') rel orel otr N"
  apply (rule stepwise_graph_refineI)
  apply (erule_tac i="Suc i" and j="j" in stepwise_graph_refineD)
  apply clarsimp
  apply (frule_tac i=i and tr=tr in exec_trace_step_cases)
  apply (clarsimp simp: exec_graph_step_def exec_graph_invariant_Cons split: graph_function.split_asm)
  apply (simp add: K_def upd_vars_def save_vals_def)
  done

lemma stepwise_graph_refine_flip:
  "stepwise_graph_refine Gamma (fns', fns) (nns', nns)
        (\<lambda>x. rel (snd x, fst x)) (\<lambda>x. orel (snd x, fst x)) (option_map (\<lambda>x. (snd x, fst x)) otr) N
    = stepwise_graph_refine Gamma (fns, fns') (nns, nns') rel orel otr N"
  apply (intro iffI stepwise_graph_refineI)
   apply (frule_tac i=j and j=i and tr=tr' and tr'=tr in stepwise_graph_refineD)
    apply simp
   apply auto[1]
  apply (frule_tac i=j and j=i and tr=tr' and tr'=tr in stepwise_graph_refineD)
   apply simp
  apply auto[1]
  done

lemma stepwise_graph_refine_nop_right:
  "stepwise_graph_refine Gamma (fns, f2 # fns') (nns, nn' # nns') rel orel otr N
    \<Longrightarrow> Gamma f2 = Some gf2
    \<Longrightarrow> function_graph gf2 n' = Some (Basic nn' [])
    \<Longrightarrow> stepwise_graph_refine Gamma (fns, f2 # fns')
        (nns, NextNode n' # nns') rel orel otr N"
  apply (rule stepwise_graph_refineI)
  apply (erule_tac i="i" and j="Suc j" in stepwise_graph_refineD)
  apply clarsimp
  apply (frule_tac i=j and tr=tr' in exec_trace_step_cases)
  apply (clarsimp simp: exec_graph_step_def exec_graph_invariant_Cons split: graph_function.split_asm)
  apply (simp add: K_def upd_vars_def save_vals_def)
  done

lemma stepwise_graph_refine_inline_left:
  "stepwise_graph_refine Gamma (fname # f1 # fns, f2 # fns')
        (NextNode (entry_point gf3) # NextNode n # nns, nn' # nns')
        rel' orel otr (Suc N)
    \<Longrightarrow> Gamma f1 = Some gf1 \<Longrightarrow> Gamma f2 = Some gf2
    \<Longrightarrow> function_graph gf1 n = Some (Call nn fname inputs outputs)
    \<Longrightarrow> function_graph gf2 n' = Some (Basic nn' upds)
    \<Longrightarrow> Gamma fname = Some gf3
    \<Longrightarrow> \<forall>x xs y ys. rel (x # xs, y # ys)
        \<longrightarrow> rel' (init_vars (function_inputs gf3) inputs x # x # xs, upd_vars upds y # ys)
    \<Longrightarrow> stepwise_graph_refine Gamma (f1 # fns, f2 # fns')
        (NextNode n # nns, NextNode n' # nns') rel orel otr N"
  apply (rule stepwise_graph_refineI)
  apply (erule_tac i="Suc i" and j="Suc j" in stepwise_graph_refineD)
  apply clarsimp
  apply (frule_tac i=i and tr=tr in exec_trace_step_cases)
  apply (frule_tac i=j and tr=tr' in exec_trace_step_cases)
  apply (clarsimp simp: exec_graph_step_def exec_graph_invariant_Cons split: graph_function.split_asm)
  done

lemma stepwise_graph_refine_end_inline_left:
  "stepwise_graph_refine Gamma (f1 # fns, f2 # fns')
        (nn # nns, nn' # nns')
        rel' orel otr (Suc N)
    \<Longrightarrow> Gamma f1 = Some gf1 \<Longrightarrow> Gamma f2 = Some gf2
    \<Longrightarrow> function_graph gf1 n = Some (Call nn fname inputs outputs)
    \<Longrightarrow> function_graph gf2 n' = Some (Basic nn' upds)
    \<Longrightarrow> Gamma fname = Some gf3
    \<Longrightarrow> \<forall>x x' xs y ys. rel (x # x' # xs, y # ys)
        \<longrightarrow> rel' (return_vars (function_outputs gf3) outputs x x' # xs, upd_vars upds y # ys)
    \<Longrightarrow> stepwise_graph_refine Gamma (fname # f1 # fns, f2 # fns')
        (Ret # NextNode n # nns, NextNode n' # nns') rel orel otr N"
  apply (rule stepwise_graph_refineI)
  apply (erule_tac i="Suc i" and j="Suc j" in stepwise_graph_refineD)
  apply clarsimp
  apply (frule_tac i=i and tr=tr in exec_trace_step_cases)
  apply (frule_tac i=j and tr=tr' in exec_trace_step_cases)
  apply (clarsimp simp: exec_graph_step_def exec_graph_invariant_Cons split: graph_function.split_asm)
  done

lemma stepwise_graph_refine_inline_right:
  "stepwise_graph_refine Gamma (f1 # fns, fname # f2 # fns')
        (nn # nns, NextNode (entry_point gf3) # NextNode n' # nns')
        rel' orel otr (Suc N)
    \<Longrightarrow> Gamma f1 = Some gf1 \<Longrightarrow> Gamma f2 = Some gf2
    \<Longrightarrow> function_graph gf1 n = Some (Basic nn upds)
    \<Longrightarrow> function_graph gf2 n' = Some (Call nn' fname inputs outputs)
    \<Longrightarrow> Gamma fname = Some gf3
    \<Longrightarrow> \<forall>x xs y ys. rel (x # xs, y # ys)
        \<longrightarrow> rel' (upd_vars upds x # xs, init_vars (function_inputs gf3) inputs y # y # ys)
    \<Longrightarrow> stepwise_graph_refine Gamma (f1 # fns, f2 # fns')
        (NextNode n # nns, NextNode n' # nns') rel orel otr N"
  apply (rule stepwise_graph_refineI)
  apply (erule_tac i="Suc i" and j="Suc j" in stepwise_graph_refineD)
  apply clarsimp
  apply (frule_tac i=i and tr=tr in exec_trace_step_cases)
  apply (frule_tac i=j and tr=tr' in exec_trace_step_cases)
  apply (clarsimp simp: exec_graph_step_def exec_graph_invariant_Cons split: graph_function.split_asm)
  done

lemma stepwise_graph_refine_end_inline_right:
  "stepwise_graph_refine Gamma (f1 # fns, f2 # fns')
        (nn # nns, nn' # nns')
        rel' orel otr (Suc N)
    \<Longrightarrow> Gamma f1 = Some gf1 \<Longrightarrow> Gamma f2 = Some gf2
    \<Longrightarrow> function_graph gf1 n = Some (Basic nn upds)
    \<Longrightarrow> function_graph gf2 n' = Some (Call nn' fname inputs outputs)
    \<Longrightarrow> Gamma fname = Some gf3
    \<Longrightarrow> \<forall>x xs y y' ys. rel (x # xs, y # y' # ys)
        \<longrightarrow> rel' (upd_vars upds x # xs, return_vars (function_outputs gf3) outputs y y' # ys)
    \<Longrightarrow> stepwise_graph_refine Gamma (f1 # fns, fname # f2 # fns')
        (NextNode n # nns, Ret # NextNode n' # nns') rel orel otr N"
  apply (rule stepwise_graph_refineI)
  apply (erule_tac i="Suc i" and j="Suc j" in stepwise_graph_refineD)
  apply clarsimp
  apply (frule_tac i=i and tr=tr in exec_trace_step_cases)
  apply (frule_tac i=j and tr=tr' in exec_trace_step_cases)
  apply (clarsimp simp: exec_graph_step_def exec_graph_invariant_Cons split: graph_function.split_asm)
  done

lemma stepwise_graph_refine_induct:
  assumes Suc: "\<And>n otr. stepwise_graph_refine Gamma fns nns rel orel otr (Suc n)
        \<Longrightarrow> stepwise_graph_refine Gamma fns nns rel orel otr n"
  shows "stepwise_graph_refine Gamma fns nns rel orel otr n"
proof -
  have induct: "\<And>n m otr. n \<ge> m
        \<Longrightarrow> stepwise_graph_refine Gamma fns nns rel orel otr n
        \<Longrightarrow> stepwise_graph_refine Gamma fns nns rel orel otr m"
    by (erule(1) inc_induct, erule Suc)

  show ?thesis
    apply (rule stepwise_graph_refineI)
    apply (simp add: prod_eq_iff)
    apply (case_tac "\<exists>N. (\<forall>i \<ge> N. tr i = None) \<or> (\<forall>i \<ge> N. tr' i = None)")
     apply clarsimp
      apply (cut_tac n="Suc N" and m="n" and otr="Some (tr, tr')" in induct)
        apply (rule ccontr, auto)[1]
       apply (auto simp add: stepwise_graph_refine_def)[1]
      apply (drule_tac tr=tr and tr'=tr' in stepwise_graph_refineD, (erule conjI)+)
       apply simp
      apply simp
     apply (case_tac "trace_end tr")
      apply (rule ccontr, clarsimp)
      apply (frule(1) exec_trace_end_SomeD, clarsimp)
      apply (frule(1) exec_trace_None_dom_subset)
      apply (drule_tac x="Suc na" in spec)
      apply auto[1]
     apply clarsimp
     apply (frule(1) exec_trace_end_SomeD, clarsimp)
     apply (frule(1) exec_trace_None_dom_subset)
     apply (drule_tac x="Suc na" in spec)
     apply auto[1]
     done
qed

end
