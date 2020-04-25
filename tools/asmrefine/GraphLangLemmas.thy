(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory GraphLangLemmas

imports GraphLang CommonOpsLemmas

begin

definition
  get_state_function_call :: "(string \<Rightarrow> graph_function option)
    \<Rightarrow> (next_node \<times> state \<times> string) \<Rightarrow> string option"
where
  "get_state_function_call Gamma x \<equiv> case x of (NextNode nn, st, fname) \<Rightarrow>
        (case Gamma fname of Some gf \<Rightarrow>
            (case function_graph gf nn of Some (Call _ fname' _ _) \<Rightarrow> Some fname' | _ \<Rightarrow> None)
          | None \<Rightarrow> None)
    | _ \<Rightarrow> None"

definition
  exec_graph_invariant :: "(string \<Rightarrow> graph_function option) \<Rightarrow> string \<Rightarrow> stack \<Rightarrow> bool"
where
  "exec_graph_invariant Gamma gf xs = (xs \<noteq> []
    \<and> (\<forall>frame \<in> set (tl xs). get_state_function_call Gamma frame \<noteq> None)
    \<and> map (Some o snd o snd) xs = map (get_state_function_call Gamma) (tl xs) @ [Some gf])"

lemma exec_graph_invariant_Cons:
  "exec_graph_invariant Gamma fname (x # xs) = (if xs = [] then snd (snd x) = fname
    else (get_state_function_call Gamma (hd xs) = Some (snd (snd x))
        \<and> exec_graph_invariant Gamma fname xs))"
  by (cases xs, auto simp add: exec_graph_invariant_def)

lemma exec_step_invariant:
  "(stack, stack') \<in> exec_graph_step Gamma
    \<Longrightarrow> exec_graph_invariant Gamma gf stack
    \<Longrightarrow> exec_graph_invariant Gamma gf stack'"
  by (auto simp: all_exec_graph_step_cases exec_graph_invariant_Cons
                 get_state_function_call_def
          split: graph_function.split_asm)

lemma exec_trace_invariant':
  "tr \<in> exec_trace Gamma gf
    \<Longrightarrow> (\<forall>stack. tr i = Some stack
        \<longrightarrow> exec_graph_invariant Gamma gf stack)"
  apply (induct i)
   apply (clarsimp simp: exec_trace_def exec_graph_invariant_def)
   apply (clarsimp split: next_node.split_asm list.split_asm)
  apply (clarsimp simp: exec_trace_def nat_trace_rel_def)
  apply (drule_tac x=i in spec, clarsimp)
  apply (auto elim: exec_step_invariant)
  done

lemmas exec_trace_invariant = exec_trace_invariant'[rule_format]

lemma exec_trace_Nil:
  "tr \<in> exec_trace Gamma gf \<Longrightarrow> tr i \<noteq> Some []"
  apply safe
  apply (drule(1) exec_trace_invariant)
  apply (simp add: exec_graph_invariant_def)
  done

lemma exec_trace_step_cases:
  assumes exec: "tr \<in> exec_trace Gamma gf"
  shows "((tr i = None \<and> tr (Suc i) = None))
        \<or> (\<exists>state. tr i = Some [state] \<and> fst state \<in> {Ret, Err} \<and> tr (Suc i) = None)
        \<or> (tr i \<noteq> None \<and> tr (Suc i) \<noteq> None \<and> (the (tr i), the (tr (Suc i))) \<in> exec_graph_step Gamma)"
  using exec exec_trace_Nil[OF exec]
  apply (clarsimp simp: exec_trace_def nat_trace_rel_def continuing_def Ball_def)
  apply (drule_tac x=i in spec)+
  apply (auto split: list.split_asm option.split_asm prod.split_asm next_node.split_asm)[1]
  done

definition
  reachable_step :: "(nat \<Rightarrow> node option) \<Rightarrow> (next_node \<times> next_node) set"
where
  "reachable_step graph = {(s, t). (case s of NextNode i \<Rightarrow>
    (case graph i of None \<Rightarrow> False
        | Some (Cond l r _) \<Rightarrow> (t = l \<or> t = r)
        | Some (Basic c _) \<Rightarrow> t = c
        | Some (Call c _ _ _) \<Rightarrow> t = c \<or> t = Err) | _ \<Rightarrow> False)}"

abbreviation
  "reachable_step' gf \<equiv> reachable_step (function_graph gf)"

lemma exec_trace_None_dom_subset:
  "tr n = None \<Longrightarrow> tr \<in> exec_trace Gamma f
    \<Longrightarrow> dom tr \<subseteq> {..< n}"
  unfolding exec_trace_def
  by (blast elim: CollectE dest: trace_None_dom_subset)

lemma trace_Some_dom_superset:
  "tr \<in> nat_trace_rel c R
    \<Longrightarrow> tr i = Some v
    \<Longrightarrow> {..i} \<subseteq> dom tr"
  apply (clarsimp, rule ccontr, clarsimp)
  apply (drule(1) trace_None_dom_subset)
  apply auto
  done

lemma nat_trace_rel_final:
  "tr \<in> nat_trace_rel c R
    \<Longrightarrow> tr i = Some v
    \<Longrightarrow> \<not> c' v
    \<Longrightarrow> restrict_map tr {.. i} \<in> nat_trace_rel c' R"
  apply (frule(1) trace_Some_dom_superset)
  apply (clarsimp simp: nat_trace_rel_def restrict_map_def Suc_le_eq)
  apply (drule_tac c="Suc n" in subsetD, auto)
  done

lemma trace_None_dom_eq:
  "tr n = None \<Longrightarrow> tr \<in> nat_trace_rel cont R
    \<Longrightarrow> (\<exists>n'. n' \<le> n \<and> dom tr = {..< n'})"
  apply (cases "\<forall>i. tr i = None")
   apply (rule_tac x=0 in exI)
   apply (simp add: fun_eq_iff)
  apply clarsimp
  apply (rule_tac x="Suc (Max (dom tr))" in exI)
  apply (drule(1) nat_trace_Max_dom_None[rotated, simplified, OF exI])
  apply clarsimp
  apply (frule(1) trace_None_dom_subset)
  apply (rule conjI)
   apply auto[1]
  apply (rule equalityI)
   apply (auto simp: less_Suc_eq_le intro!: Max_ge elim: finite_subset)[1]
  apply (clarsimp, rule ccontr, clarsimp simp: less_Suc_eq_le)
  apply (drule(1) trace_None_dom_subset)+
  apply auto
  done

lemma trace_end_eq_Some:
  "tr \<in> nat_trace_rel c R
    \<Longrightarrow> tr i = Some v
    \<Longrightarrow> tr (Suc i) = None
    \<Longrightarrow> trace_end tr = Some v"
  apply (frule(1) trace_Some_dom_superset)
  apply (frule(1) trace_None_dom_eq)
  apply (clarsimp simp: le_Suc_eq lessThan_Suc_atMost[symmetric])
  apply (simp add: trace_end_def)
  apply (subst Max_eqI[where x=i], simp_all)
  apply auto
  done

lemma trace_end_cut:
  "tr \<in> nat_trace_rel c R
    \<Longrightarrow> tr i = Some v
    \<Longrightarrow> trace_end (restrict_map tr {.. i}) = Some v"
  apply (frule(1) trace_Some_dom_superset)
  apply (simp add: trace_end_def Int_absorb1)
  apply (subst Max_eqI[where x=i], simp_all)
  apply (simp add: restrict_map_def)
  apply (metis Suc_n_not_le_n)
  done

definition
  trace_drop_n :: "nat \<Rightarrow> nat \<Rightarrow> trace \<Rightarrow> trace"
where
  "trace_drop_n start n_drop tr = (\<lambda>i. if (\<forall>j < i. tr (start + j) \<noteq> None
        \<and> continuing (rev (drop n_drop (rev (the (tr (start + j)))))))
    then option_map (rev o drop n_drop o rev) (tr (i + start)) else None)"

lemma rev_drop_step:
  "(stack, stack') \<in> exec_graph_step Gamma
    \<Longrightarrow> continuing (rev (drop k (rev stack)))
    \<Longrightarrow> (rev (drop k (rev stack)), rev (drop k (rev stack'))) \<in> exec_graph_step Gamma"
  apply (subgoal_tac "\<exists>xs ys. stack = xs @ ys \<and> k = length ys")
   apply clarsimp
   apply (frule(1) exec_graph_step_stack_extend[THEN iffD1])
   apply clarsimp
  apply (rule_tac x="take (length stack - k) stack" in exI)
  apply (rule_tac x="drop (length stack - k) stack" in exI)
  apply (cases "length (rev (drop k (rev stack)))")
   apply simp
  apply simp
  done

lemma rev_drop_continuing:
  "continuing (rev (drop k (rev stack))) \<Longrightarrow> continuing stack"
  by (simp add: continuing_def split: list.split next_node.split,
      auto simp: drop_Cons split: nat.split_asm)

lemma all_less_Suc_eq:
  "(\<forall>x < Suc i. P x) = (P i \<and> (\<forall>x < i. P x))"
  by (auto simp: less_Suc_eq)

lemma exec_trace_drop_n_Cons:
  assumes tr: "tr \<in> exec_trace Gamma fn" "Gamma fn'' = Some gf"
  shows "tr i = Some ((NextNode n, st, fn'') # xs)
    \<Longrightarrow> function_graph gf n = Some (Call nn fn' inps outps)
    \<Longrightarrow> Gamma fn' = Some gf'
    \<Longrightarrow> trace_drop_n (Suc i) (Suc (length xs)) tr \<in> exec_trace Gamma fn'"
  using tr
  apply (clarsimp simp: exec_trace_def)
  apply (intro conjI)
   apply (simp add: trace_drop_n_def)
   apply (cut_tac exec_trace_step_cases[where i=i, OF tr(1)])
   apply (clarsimp simp: all_exec_graph_step_cases exec_graph_invariant_Cons
                  split: graph_function.split_asm)
  apply (clarsimp simp: nat_trace_rel_def trace_drop_n_def
                        all_less_Suc_eq
             split del: if_split)
  apply (cut_tac i="Suc i + na" in exec_trace_Nil[OF tr(1)])
  apply (drule_tac x="Suc i + na" in spec)+
  apply (clarsimp simp: field_simps)
  apply (safe, simp_all)
  apply (safe intro!: rev_drop_step)
  apply (auto dest!: rev_drop_continuing)
  done

lemma exec_trace_drop_n:
  assumes tr: "tr \<in> exec_trace Gamma fn" "Gamma fn = Some gf"
  shows "tr i = Some [(NextNode n, st, fn'')]
    \<Longrightarrow> function_graph gf n = Some (Call nn fn' inps outps)
    \<Longrightarrow> Gamma fn' = Some gf'
    \<Longrightarrow> trace_drop_n (Suc i) 1 tr \<in> exec_trace Gamma fn'"
  apply (frule exec_trace_invariant[OF tr(1)])
  apply (simp add: exec_graph_invariant_Cons)
  apply (drule(2) exec_trace_drop_n_Cons[OF tr])
  apply simp
  done

lemma exec_trace_drop_n_rest_Cons:
  "tr \<in> exec_trace Gamma fn
    \<Longrightarrow> tr i = Some ((NextNode n, st, fn'') # xs)
    \<Longrightarrow> Gamma fn'' = Some gf
    \<Longrightarrow> function_graph gf n = Some (Call nn fn' inps outps)
    \<Longrightarrow> Gamma fn' = Some gf'
    \<Longrightarrow> (\<forall>stk. trace_drop_n (Suc i) (Suc (length xs)) tr k = Some stk
     \<longrightarrow> tr (Suc i + k) = Some (stk @ (NextNode n, st, fn'') # xs))"
proof (induct k)
  case 0 show ?case using 0
    apply (clarsimp simp: trace_drop_n_def)
    apply (frule_tac i=i in exec_trace_step_cases)
    apply (clarsimp simp: exec_graph_step_def exec_graph_invariant_Cons
                   split: graph_function.split_asm)
    done
next
  case (Suc k)
  have rev_drop_eq: "\<And>xs ys n. length ys = n
    \<Longrightarrow> (xs = rev (drop n (rev xs)) @ ys)
        = (\<exists>zs. xs = zs @ ys)"
    by auto
  show ?case using Suc.prems Suc.hyps
    apply (clarsimp simp: trace_drop_n_def field_simps)
    apply (frule_tac i="Suc k + i" in exec_trace_step_cases)
    apply (clarsimp simp: field_simps all_less_Suc_eq rev_drop_eq)
    apply (clarsimp simp: exec_graph_step_stack_extend)
    done
qed

lemma exec_trace_drop_n_rest:
  "tr \<in> exec_trace Gamma fn \<Longrightarrow> Gamma fn = Some gf
    \<Longrightarrow> tr i = Some [(NextNode n, st, fn'')]
    \<Longrightarrow> function_graph gf n = Some (Call nn fn' inps outps)
    \<Longrightarrow> Gamma fn' = Some gf'
    \<Longrightarrow> (\<forall>stk. trace_drop_n (Suc i) 1 tr k = Some stk
     \<longrightarrow> tr (Suc i + k) = Some (stk @ [(NextNode n, st, fn'')]))"
  apply (frule(1) exec_trace_invariant)
  apply (clarsimp simp: exec_graph_invariant_Cons)
  apply (drule(4) exec_trace_drop_n_rest_Cons)
  apply auto
  done

lemma trace_drop_n_init:
  "tr \<in> exec_trace Gamma fn \<Longrightarrow> Gamma fn = Some f
    \<Longrightarrow> function_graph f n = Some (Call nn fname inputs outputs)
    \<Longrightarrow> Gamma fname = Some f'
    \<Longrightarrow> tr i = Some [(NextNode n, st, fn')]
    \<Longrightarrow> trace_drop_n (Suc i) 1 tr 0 = Some [(NextNode (entry_point f'),
            init_vars (function_inputs f') inputs st, fname)]"
  apply (frule(1) exec_trace_invariant)
  apply (clarsimp simp: exec_graph_invariant_Cons)
  apply (frule_tac i=i in exec_trace_step_cases, clarsimp)
  apply (clarsimp simp: all_exec_graph_step_cases trace_drop_n_def)
  done

lemma exec_trace_init:
  "tr \<in> exec_trace Gamma fn
   \<Longrightarrow> \<exists>st gf. Gamma fn = Some gf \<and> tr 0 = Some [(NextNode (entry_point gf), st, fn)]"
  by (clarsimp simp: exec_trace_def)

lemma dom_Max_None:
  "tr \<in> exec_trace Gamma f \<Longrightarrow> (tr (Max (dom tr)) \<noteq> None)"
  apply (rule notI)
  apply (frule(1) exec_trace_None_dom_subset)
  apply (cases "dom tr = {}")
   apply (clarsimp dest!: exec_trace_init)
  apply (drule Max_in[rotated])
   apply (simp add: finite_subset)
  apply clarsimp
  done

lemma trace_end_trace_drop_n_None:
  "trace_end (trace_drop_n i j tr) = None \<Longrightarrow> tr \<in> exec_trace Gamma f
    \<Longrightarrow> trace_drop_n i j tr \<in> exec_trace Gamma f'
    \<Longrightarrow> trace_end tr = None"
  apply (clarsimp simp: trace_end_def dom_Max_None split: if_split_asm)
  apply (rule ccontr, simp)
  apply (drule(1) exec_trace_None_dom_subset)
  apply (drule_tac x="n + i + 1" in spec)
  apply (clarsimp simp: trace_drop_n_def split: if_split_asm)
  apply auto[1]
  done

lemma trace_end_trace_drop_n_Some:
  "trace_end (trace_drop_n (Suc i) (Suc 0) tr) = Some [(Ret, st', dontcare)]
    \<Longrightarrow> tr \<in> exec_trace Gamma fn \<Longrightarrow> Gamma fn = Some f
    \<Longrightarrow> function_graph f n = Some (Call nn fname inputs outputs)
    \<Longrightarrow> Gamma fname = Some f'
    \<Longrightarrow> tr i = Some [(NextNode n, st, fn')]
    \<Longrightarrow> \<exists>j. tr (Suc i + j) = Some [(nn, return_vars (function_outputs f') outputs st' st, fn)]
"
  apply (frule(4) exec_trace_drop_n)
  apply (drule trace_end_SomeD, fastforce simp add: exec_trace_def)
  apply clarsimp
  apply (frule(4) exec_trace_drop_n_rest, simp, drule spec, drule(1) mp)
  apply simp
  apply (frule(1) exec_trace_invariant[where stack="[a, b]" for a b])
  apply (clarsimp simp: exec_graph_invariant_Cons get_state_function_call_def)
  apply (frule_tac i="Suc i + na" in exec_trace_step_cases, clarsimp)
  apply (clarsimp simp: all_exec_graph_step_cases)
  apply (metis add_Suc_right)
  done

end
