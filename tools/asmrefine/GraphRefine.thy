(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory GraphRefine

imports
  TailrecPre
  GraphLangLemmas
  Lib.Lib
  "CParser.LemmaBucket_C"
  ExtraSpecs
begin

type_synonym ('s, 'x, 'e) c_trace = "nat \<Rightarrow> (('s, 'x, 'e) com \<times> ('s, 'e) xstate) option"

definition
  c_trace :: "('x \<Rightarrow> ('s, 'x, 'e) com option) \<Rightarrow> ('s, 'x, 'e) c_trace set"
where
  "c_trace Gamma = nat_trace_rel (Not o final) {(cfg, cfg'). step Gamma cfg cfg'}"

definition
  "exec_final_step cfg = (case cfg of (Throw, Normal xs) \<Rightarrow> Abrupt xs | _ \<Rightarrow> snd cfg)"

lemma exec_via_trace:
  "Gamma \<turnstile> \<langle>com, Normal s\<rangle> \<Rightarrow> xs
    = (\<exists>tr \<in> c_trace Gamma. tr 0 = Some (com, Normal s)
        \<and> option_map exec_final_step (trace_end tr) = Some xs)"
proof -
  have dom_If: "\<And>n f. dom (\<lambda>i. if i \<le> n then Some (f i) else None) = {..n}"
    by (auto split: if_split_asm)
  have end_If: "\<And>n f. trace_end (\<lambda>i. if i \<le> n then Some (f i) else None) = Some (f n)"
    apply (simp add: trace_end_def dom_If)
    apply (subst Max_eqI, simp+)
    apply (rule_tac x="Suc n" in exI, simp)
    done
  show ?thesis unfolding c_trace_def
    apply safe
     apply (clarsimp simp: relpowp_fun_conv dest!: exec_impl_steps rtranclp_imp_relpowp)
     apply (rule_tac x="\<lambda>i. if i \<le> n then Some (f i) else None" in bexI)
      apply (simp add: end_If exec_final_step_def split: xstate.split_asm)
     apply (simp add: nat_trace_rel_def)
     apply (clarsimp simp: linorder_not_le less_Suc_eq)
     apply (simp add: final_def split: xstate.split_asm)
    apply (drule(1) trace_end_SomeD)
    apply clarsimp
    apply (subgoal_tac "rtranclp (step Gamma) (the (tr 0)) (the (tr n))")
     apply (clarsimp simp: final_def)
     apply (auto simp: exec_final_step_def dest: steps_Skip_impl_exec steps_Throw_impl_exec)[1]
    apply (simp add: rtranclp_power relpowp_fun_conv)
    apply (rule_tac x=n in exI)
    apply (rule_tac x="the o tr" in exI)
    apply (frule(1) trace_None_dom_eq)
    apply (clarsimp simp: nat_trace_rel_def)
    apply (subgoal_tac "i \<in> dom tr \<and> Suc i \<in> dom tr")
     apply clarify
     apply metis
    apply (drule(1) eqset_imp_iff[THEN iffD1, rotated, OF domI])+
    apply simp
    done
qed

abbreviation
  "extend_rel \<equiv> {((i :: nat, tr), (j, tr')).
    j > i \<and> restrict_map tr {.. i} = restrict_map tr' {.. i}}"

definition
  "suffix_tuple_closure_inter Ss
    = (\<Inter>S \<in> Ss. {(y, tr). \<exists>k. (y, restrict_map tr {.. k}) \<in> S})"

lemma suffix_tuple_closure_prefixI:
  "(y, restrict_map tr {.. (k :: nat)}) \<in> suffix_tuple_closure_inter Ss
    \<Longrightarrow> (y, tr) \<in> suffix_tuple_closure_inter Ss"
  by (auto simp add: suffix_tuple_closure_inter_def)

definition
  trace_end_match :: "(state \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's set
        \<Rightarrow> stack option
        \<Rightarrow> ((('s, 'x, 'e) com \<times> ('s, 'e) xstate) option)
        \<Rightarrow> bool"
where
  "trace_end_match out_eqs I e e' = ((\<exists>ft. e' = Some (com.Skip, Fault ft))
    \<or> ((e = None) \<and> (e' = None))
    \<or> (\<exists>sst' gst' gf'. e = Some [(Ret, gst', gf')]
        \<and> e' = Some (com.Skip, Normal sst')
        \<and> out_eqs gst' sst' \<and> sst' \<in> I))"

definition
  simpl_to_graph :: "('x \<Rightarrow> ('s, 'x, 'e) com option)
        \<Rightarrow> (string \<Rightarrow> graph_function option) \<Rightarrow> string
        \<Rightarrow> next_node \<Rightarrow> ('s, 'x, 'e) com
        \<Rightarrow> nat \<Rightarrow> (trace \<times> ('s, 'x, 'e) c_trace) set list
        \<Rightarrow> 's set \<Rightarrow> 's set \<Rightarrow> (state \<Rightarrow> 's \<Rightarrow> bool)
        \<Rightarrow> (state \<Rightarrow> 's \<Rightarrow> bool)
        \<Rightarrow> bool"
where
  "simpl_to_graph SGamma GGamma gf nn com n traces P I inp_eqs out_eqs
    = (\<forall>tr gst sst n' gf' tr' n''. tr n' = Some [(nn, gst, gf')] \<and> sst \<in> P \<and> sst \<in> I
        \<and> inp_eqs gst sst \<and> n' \<ge> n \<and> n'' \<ge> n
        \<and> tr \<in> exec_trace GGamma gf
        \<and> (tr, restrict_map tr' {.. n''}) \<in> suffix_tuple_closure_inter (set traces)
                \<and> tr' \<in> nat_trace_rel (\<lambda>x. False) {(cfg, cfg'). step SGamma cfg cfg'}
                \<and> tr' n'' = Some (com, Normal sst)
        \<longrightarrow> (\<exists>tr''. tr'' \<in> c_trace SGamma \<and> restrict_map tr'' {.. n''} = restrict_map tr' {.. n''}
                \<and> trace_end_match out_eqs I (trace_end tr) (trace_end tr'')))"

lemma simpl_to_graph_ge_subset:
  "simpl_to_graph SGamma GGamma gf nn com n traces' P I inp_eqs out_eqs
    \<Longrightarrow> n' \<ge> n \<and> set traces' \<subseteq> set traces
    \<Longrightarrow> simpl_to_graph SGamma GGamma gf nn com n' traces P I inp_eqs out_eqs"
  apply (simp add: simpl_to_graph_def suffix_tuple_closure_inter_def Ball_def)
  apply (erule mp[rotated], intro all_mono ex_mono imp_mono conj_mono imp_refl,
      simp_all)
  apply blast
  done

lemmas simpl_to_graphI = simpl_to_graph_def[THEN iffD2, rule_format]
lemmas simpl_to_graphD = simpl_to_graph_def[THEN iffD1, rule_format]

lemma nat_trace_rel_split:
  "tr n = Some v
    \<Longrightarrow> tr' (Suc n) = Some v'
    \<Longrightarrow> (v, v') \<in> R
    \<Longrightarrow> tr \<in> nat_trace_rel cont' R
    \<Longrightarrow> (\<lambda>i. tr' (Suc n + i)) \<in> nat_trace_rel cont R
    \<Longrightarrow> (\<lambda>i. if i \<le> n then tr i else tr' i) \<in> nat_trace_rel cont R"
  apply (frule(1) trace_Some_dom_superset)
  apply (clarsimp simp: nat_trace_rel_def, safe)
  apply (simp_all add: linorder_not_le less_Suc_eq_le subset_iff domIff)
    apply (drule_tac x="na - Suc n" in spec | clarsimp)+
  done

lemma nat_trace_rel_to_relpow:
  "trace \<in> nat_trace_rel cont R
    \<Longrightarrow> trace i = Some x
    \<Longrightarrow> trace (i + j) = Some y
    \<Longrightarrow> (x, y) \<in> R ^^ j"
  apply (induct j arbitrary: y)
   apply simp
  apply atomize
  apply (clarsimp simp: nat_trace_rel_def)
  apply (drule_tac x="i + j" in spec, clarsimp)
  apply auto
  done

lemma exec_graph_trace_must_take_steps:
  "trace \<in> exec_trace \<Gamma> fn
    \<Longrightarrow> trace i = Some [(nn, st, fn)]
    \<Longrightarrow> (exec_graph_step \<Gamma> ^^ j) `` {[(nn, st, fn)]} \<subseteq> {[(nn', st', fn)]}
    \<Longrightarrow> \<forall>k < j. \<forall>st'. ([(nn, st, fn)], st') \<in> exec_graph_step \<Gamma> ^^ k
        \<longrightarrow> continuing st'
    \<Longrightarrow> trace (i + j) = Some [(nn', st', fn)]"
  apply (case_tac "trace (i + j)")
   apply (clarsimp simp add: exec_trace_def)
   apply (drule(1) trace_None_dom_eq)
   apply clarsimp
   apply (drule sym[where s="dom trace"])
   apply (frule_tac x=i in eqset_imp_iff)
   apply (frule_tac x="n' - 1" in eqset_imp_iff)
   apply (frule_tac x="n'" in eqset_imp_iff)
   apply (simp(no_asm_use), clarsimp simp: domIff)
   apply (frule_tac i="n' - 1" in trace_end_eq_Some, simp+)
   apply (drule(1) trace_end_SomeD, clarsimp)
   apply (drule_tac x="n' - 1 - i" in spec, simp)
   apply (drule_tac i=i and j="n' - 1 - i" in nat_trace_rel_to_relpow, simp+)
  apply (clarsimp simp add: exec_trace_def)
  apply (drule_tac i=i and j=j in nat_trace_rel_to_relpow, simp+)
  apply auto
  done

lemma c_trace_may_extend:
  "trace \<in> nat_trace_rel (\<lambda>x. False) {(x, y). \<Gamma> \<turnstile> x \<rightarrow> y}
    \<Longrightarrow> trace i = Some (com, Normal st)
    \<Longrightarrow> ((step \<Gamma>) ^^ j) (com, Normal st) (com', xst')
    \<Longrightarrow> (y, restrict_map trace {..i}) \<in> suffix_tuple_closure_inter Ss
    \<Longrightarrow> \<exists>trace'. trace' \<in> nat_trace_rel (\<lambda>x. False) {(x, y). \<Gamma> \<turnstile> x \<rightarrow> y}
      \<and> trace' (i + j) = Some (com', xst')
      \<and> restrict_map trace' {.. i} = restrict_map trace {.. i}
      \<and> (y, restrict_map trace' {.. i + j}) \<in> suffix_tuple_closure_inter Ss"
  apply (cases "j = 0")
   apply fastforce
  apply (clarsimp simp: relpowp_fun_conv)
  apply (rule_tac x="\<lambda>k. if k \<le> i then trace k else
               if k \<le> i + j then Some (f (k - i))
               else None"
         in exI)
  apply (intro conjI)
     apply (erule nat_trace_rel_split, simp, simp_all)
     apply (drule_tac x=0 in spec, simp)
    apply (simp add: nat_trace_rel_def)
   apply (simp add: restrict_map_def cong: if_cong)
  apply (rule_tac k=i in suffix_tuple_closure_prefixI)
  apply (simp add: restrict_map_def cong: if_cong)
  done

lemma c_trace_may_extend_steps:
  "trace \<in> nat_trace_rel (\<lambda>x. False) {(x, y). \<Gamma> \<turnstile> x \<rightarrow> y}
    \<Longrightarrow> trace i = Some (com, Normal st)
    \<Longrightarrow> \<Gamma> \<turnstile> (com, Normal st) \<rightarrow>\<^sup>* (com', xst')
    \<Longrightarrow> (y, restrict_map trace {..i}) \<in> suffix_tuple_closure_inter Ss
    \<Longrightarrow> \<exists>j trace'. trace' \<in> nat_trace_rel (\<lambda>x. False) {(x, y). \<Gamma> \<turnstile> x \<rightarrow> y}
      \<and> trace' (i + j) = Some (com', xst')
      \<and> restrict_map trace' {.. i} = restrict_map trace {.. i}
      \<and> (y, restrict_map trace' {.. i + j}) \<in> suffix_tuple_closure_inter Ss"
  apply (clarsimp simp: rtranclp_power)
  apply (blast intro: c_trace_may_extend)
  done

lemma restrict_map_prefix_eq: "(restrict_map tr {..n} = restrict_map tr' {..n})
    = (\<forall>i \<le> n. tr i = tr' i)"
  by (auto simp add: fun_eq_iff restrict_map_def)

lemma restrict_map_eq_mono:
  "i \<le> j \<Longrightarrow> restrict_map tr {..j} = restrict_map tr' {..j}
    \<Longrightarrow> restrict_map tr {.. (i :: 'a :: linorder)} = restrict_map tr' {..i}"
  unfolding restrict_map_prefix_eq
  by clarsimp

lemma simpl_to_graph_step_general:
  "(\<And>sst gst. sst \<in> P \<Longrightarrow> sst \<in> I \<Longrightarrow> inp_eqs gst sst
        \<Longrightarrow> \<exists>sst' gst'. ((step SGamma) ^^ j) (com, Normal sst) (com', Normal sst')
            \<and> (exec_graph_step GGamma ^^ i) `` {[(nn, gst, gf)]} \<subseteq> {[(nn', gst', gf)]}
            \<and> (\<forall>k < i. \<forall>st'. ([(nn, gst, gf)], st') \<in> exec_graph_step GGamma ^^ k
                \<longrightarrow> continuing st')
            \<and> sst' \<in> P' \<and> sst' \<in> I \<and> inp_eqs' gst' sst')
    \<Longrightarrow> simpl_to_graph SGamma GGamma gf nn' com' (n + min i j) traces P' I inp_eqs' out_eqs
    \<Longrightarrow> simpl_to_graph SGamma GGamma gf nn com n traces P I inp_eqs out_eqs"
  apply (clarsimp intro!: simpl_to_graphI)
  apply (erule_tac x=sst in meta_allE)
  apply (erule_tac x=gst in meta_allE)
  apply clarsimp
  apply (frule(1) exec_trace_invariant)
  apply (clarsimp simp: exec_graph_invariant_Cons)
  apply (frule(2) exec_graph_trace_must_take_steps)
   apply simp
  apply (frule(3) c_trace_may_extend)
  apply clarsimp
  apply (drule_tac n''="n'' + j" in simpl_to_graphD,
      (rule conjI | assumption | simp)+)
  apply (metis restrict_map_eq_mono[OF le_add1[where m=j]])
  done

lemma simpl_to_graph_step:
  "(\<And>sst gst. sst \<in> P \<Longrightarrow> sst \<in> I \<Longrightarrow> inp_eqs gst sst
        \<Longrightarrow> \<exists>sst' gst'. (step SGamma) (com, Normal sst) (com', Normal sst')
            \<and> exec_graph_step GGamma `` {[(NextNode m, gst, gf)]} \<subseteq> {[(nn', gst', gf)]}
            \<and> sst' \<in> P' \<and> sst' \<in> I \<and> inp_eqs' gst' sst')
    \<Longrightarrow> simpl_to_graph SGamma GGamma gf nn' com' (Suc n) traces P' I inp_eqs' out_eqs
    \<Longrightarrow> simpl_to_graph SGamma GGamma gf (NextNode m) com n traces P I inp_eqs out_eqs"
  apply (rule simpl_to_graph_step_general[rotated, where i=1 and j=1])
    apply simp+
  apply (simp add: eq_OO)
  done

lemma simpl_to_graph_step_R:
  "(\<And>sst gst. sst \<in> P \<Longrightarrow> sst \<in> I \<Longrightarrow> inp_eqs gst sst
        \<Longrightarrow> \<exists>sst'. (step SGamma) (com, Normal sst) (com', Normal sst')
            \<and> sst' \<in> P' \<and> sst' \<in> I \<and> inp_eqs' gst sst')
    \<Longrightarrow> simpl_to_graph SGamma GGamma gf nn com' n traces P' I inp_eqs' out_eqs
    \<Longrightarrow> simpl_to_graph SGamma GGamma gf nn com n traces P I inp_eqs out_eqs"
  apply (rule simpl_to_graph_step_general[rotated, where i=0 and j=1])
    apply simp+
  apply (simp add: eq_OO)
  done

lemma simpl_to_graph_step_R_unchanged:
  "(\<And>sst gst. sst \<in> P \<Longrightarrow> sst \<in> I \<Longrightarrow> inp_eqs gst sst
        \<Longrightarrow> (step SGamma) (com, Normal sst) (com', Normal sst))
    \<Longrightarrow> simpl_to_graph SGamma GGamma gf nn com' n traces P I inp_eqs out_eqs
    \<Longrightarrow> simpl_to_graph SGamma GGamma gf nn com n traces P I inp_eqs out_eqs"
  apply (erule simpl_to_graph_step_R[rotated])
  apply blast
  done

lemma simpl_to_graph_steps_Fault1:
  "\<forall>s \<in> P \<inter> I. \<exists>com'. SGamma \<turnstile> (com, Normal s) \<rightarrow>\<^sup>* (com', Fault F)
    \<Longrightarrow> simpl_to_graph SGamma GGamma gf nn com n Q P I eqs out_eqs"
  apply (clarsimp simp: simpl_to_graph_def)
  apply (drule_tac x=sst in bspec, clarsimp+)
  apply (cut_tac \<Gamma>=SGamma and c="com'" and f=F in steps_Fault)
  apply (frule_tac c_trace_may_extend_steps, assumption)
    apply (erule(1) rtranclp_trans)
   apply assumption
  apply (clarsimp simp: c_trace_def)
  apply (rule exI, rule context_conjI)
   apply (erule(1) nat_trace_rel_final, fastforce simp: final_def)
  apply (simp add: trace_end_cut trace_end_match_def)
  done

lemma extensible_traces_to_infinite_trace:
  assumes step: "\<forall>x \<in> S. (trace x, trace (f x)) \<in> extend_rel
          \<and> f x \<in> S \<and> m x < m (f x)"
    and x: "x \<in> S"
  shows "\<exists>tr. \<forall>i :: nat. \<exists>y \<in> S. \<exists>j. m y > i \<and> fst (trace y) > i
    \<and> (trace y, (j, tr)) \<in> extend_rel"
proof -

  let ?f = "\<lambda>i. (f ^^ i) x"

  have f_induct: "\<And>i. m (?f i) \<ge> i \<and> fst (trace (?f i)) \<ge> i \<and> ?f i \<in> S"
    apply (induct_tac i)
     apply (simp add: x)
    apply (auto dest: step[rule_format])
    done

  have f_eq: "\<forall>i j k. i \<le> fst (trace (?f j)) \<longrightarrow> j \<le> k
     \<longrightarrow> fst (trace (?f j)) \<le> fst (trace (?f k)) \<and> snd (trace (?f k)) i = snd (trace (?f j)) i"
    apply (intro allI, induct_tac k)
     apply simp
    apply clarsimp
    apply (cut_tac i=n in f_induct[rule_format], clarsimp)
    apply (frule_tac step[rule_format])
    apply (clarsimp simp: fun_eq_iff restrict_map_def linorder_not_le split_def
                   split: if_split_asm)
    apply (drule_tac x=i in spec)
    apply (auto simp: le_Suc_eq)
    done

  have f_norm:
    "\<forall>i j. j \<le> fst (trace (?f i)) \<longrightarrow> snd (trace (?f i)) j = snd (trace (?f j)) j"
    apply clarsimp
    apply (cut_tac i=j and j="min i j" and k="max i j" in f_eq[rule_format])
      apply (simp add: min_def linorder_not_le f_induct)
     apply simp
    apply (simp add: min_def max_def split: if_split_asm)
    done

  show "?thesis"
    apply (rule_tac x="\<lambda>i. snd (trace (?f i)) i" in exI)
    apply (clarsimp simp: split_def)
    apply (rule_tac x="?f (Suc i)" in bexI)
     apply (cut_tac i="Suc i" in f_induct)
     apply (clarsimp simp: fun_eq_iff restrict_map_def f_norm
                 simp del: funpow.simps)
     apply (metis lessI)
    apply (simp add: f_induct del: funpow.simps)
    done
qed

lemma extensible_traces_to_infinite_trace_choice:
  assumes step: "\<forall>x \<in> S. \<exists>y. (trace x, trace y) \<in> extend_rel
          \<and> y \<in> S \<and> m x < m y"
    and x: "x \<in> S"
  shows "\<exists>tr. \<forall>i :: nat. \<exists>y \<in> S. \<exists>j. m y > i \<and> fst (trace y) > i
    \<and> (trace y, (j, tr)) \<in> extend_rel"
proof -

  let ?P = "\<lambda>i x. m x \<ge> i \<and> fst (trace x) \<ge> i \<and> x \<in> S"
  let ?Q = "\<lambda>x y. m y > m x \<and> (trace x, trace y) \<in> extend_rel"

  have induct:
    "\<And>x n. ?P n x \<Longrightarrow> \<exists>y. ?P (Suc n) y \<and> ?Q x y"
    apply clarsimp
    apply (frule step[THEN bspec])
    apply clarsimp
    apply (rule_tac x=y in exI)
    apply simp
    done

  obtain f where f: "\<forall>n. ?P n (f n) \<and> ?Q (f n) (f (Suc n))"
    using x dependent_nat_choice[where P="?P" and Q="\<lambda>_. ?Q"]
    by (simp only: induct, auto)

  have f_induct: "\<And>i. m (f i) \<ge> i \<and> fst (trace (f i)) \<ge> i \<and> f i \<in> S"
    apply (cut_tac n=i in f[rule_format], simp)
    done

  have f_eq: "\<forall>i j k. i \<le> fst (trace (f j)) \<longrightarrow> j \<le> k
     \<longrightarrow> fst (trace (f j)) \<le> fst (trace (f k)) \<and> snd (trace (f k)) i = snd (trace (f j)) i"
    apply (intro allI, induct_tac k)
     apply simp
    apply clarsimp
    apply (cut_tac i=n in f_induct[rule_format], clarsimp)
    apply (cut_tac n=n in f[rule_format], simp)
    apply (clarsimp simp: fun_eq_iff restrict_map_def linorder_not_le split_def
                   split: if_split_asm)
    apply (drule_tac x=i in spec)
    apply (auto simp: le_Suc_eq)
    done

  have f_norm:
    "\<forall>i j. j \<le> fst (trace (f i)) \<longrightarrow> snd (trace (f i)) j = snd (trace (f j)) j"
    apply clarsimp
    apply (cut_tac i=j and j="min i j" and k="max i j" in f_eq[rule_format])
      apply (simp add: min_def linorder_not_le f_induct)
     apply simp
    apply (simp add: min_def max_def split: if_split_asm)
    done

  show "?thesis"
    apply (rule_tac x="\<lambda>i. snd (trace (f i)) i" in exI)
    apply (clarsimp simp: split_def)
    apply (rule_tac x="f (Suc i)" in bexI)
     apply (cut_tac i="Suc i" in f_induct)
     apply (clarsimp simp: fun_eq_iff restrict_map_def f_norm
                 simp del: funpow.simps)
     apply (metis lessI)
    apply (simp add: f_induct del: funpow.simps)
    done
qed

lemma trace_end_None_ge_seq:
  "tr \<in> nat_trace_rel c R
    \<Longrightarrow> \<forall>i. \<exists>j \<ge> i. tr j \<noteq> None
    \<Longrightarrow> trace_end tr = None"
  apply (clarsimp simp: trace_end_def)
  apply (drule_tac x=n in spec)
  apply (drule(1) trace_None_dom_subset)
  apply auto
  done

lemma restrict_map_eq_Some_le:
  "(restrict_map tr {..n} = restrict_map tr' {..m})
    \<Longrightarrow> tr' (m :: nat) = Some v
    \<Longrightarrow> n \<ge> m \<and> (\<forall>k \<le> m. restrict_map tr {..k} = restrict_map tr' {..k})"
  apply (frule_tac x=m in fun_cong, simp(no_asm_use) add: restrict_map_def)
  apply (simp split: if_split_asm)
  apply (auto simp: fun_eq_iff split: if_split_asm)
  done

lemma trace_prefixes_to_trace:
  assumes i: "\<forall>i. \<exists>j tr k. j \<ge> i \<and> tr j \<noteq> None
        \<and> ((j, tr), (k, tr')) \<in> extend_rel \<and> tr \<in> nat_trace_rel c R"
  shows "trace_end tr' = None \<and> tr' \<in> nat_trace_rel c' R"
proof (intro conjI)
  have weak: "tr' \<in> nat_trace_rel (\<lambda>x. False) R"
    apply (clarsimp simp: nat_trace_rel_def)
    apply (cut_tac i="Suc n" in i[rule_format])
    apply (clarsimp simp: nat_trace_rel_def)
    apply (drule_tac x=n in spec, clarsimp)
    apply (clarsimp simp: restrict_map_prefix_eq)
    done

  have inf: "\<forall>i. tr' i \<noteq> None"
    apply (intro allI notI)
    apply (cut_tac i=i in i[rule_format])
    apply (clarsimp simp: restrict_map_prefix_eq)
    apply (drule trace_None_dom_subset[OF _ weak])
    apply auto
    done

  thus "trace_end tr' = None"
    by (simp only: trace_end_def, simp)

  show "tr' \<in> nat_trace_rel c' R" using weak
    by (simp only: nat_trace_rel_def inf mem_Collect_eq, simp)
qed

lemma suffix_tuple_closure_inter_insert:
  "(x, tr) \<in> suffix_tuple_closure_inter (insert S Ss)
    = ((\<exists>k. (x, restrict_map tr {..k}) \<in> S) \<and> (x, tr) \<in> suffix_tuple_closure_inter Ss)"
  by (simp add: suffix_tuple_closure_inter_def)

lemma simpl_to_graph_induct_proof:
  assumes Suc: "\<And>S' n'. n' \<ge> n
    \<Longrightarrow> simpl_to_graph SGamma GGamma gf nn com (Suc n') (S' # S) P I inp_eqs out_eqs
    \<Longrightarrow> simpl_to_graph SGamma GGamma gf nn com n' (S' # S) P I inp_eqs out_eqs"
  shows "simpl_to_graph SGamma GGamma gf nn com n (({tr} \<times> UNIV) # S) P I inp_eqs out_eqs"
proof -
  obtain M where M_def:
    "M = (\<lambda>n1 tr1. {(n', n'', tr'). tr' \<in> nat_trace_rel (\<lambda>x. False) {(x, y). SGamma\<turnstile> x \<rightarrow> y}
        \<and> (\<exists>sst gst gf'. tr' n'' = Some (com, Normal sst) \<and> tr n' = Some [(nn, gst, gf')]
            \<and> inp_eqs gst sst \<and> sst \<in> P \<and> sst \<in> I
            \<and> (tr, restrict_map tr' {..n''}) \<in> suffix_tuple_closure_inter (set S)
            \<and> restrict_map tr' {..n1} = restrict_map tr1 {..n1}
            \<and> n' \<ge> n \<and> n'' \<ge> n \<and> n'' \<ge> n1)})"
    by auto

  have induct_ge: "\<And>S' m n'. m \<ge> n \<longrightarrow> simpl_to_graph SGamma GGamma gf nn com m (S' # S) P I inp_eqs out_eqs
    \<Longrightarrow> m \<ge> n'
    \<Longrightarrow> n' \<ge> n \<longrightarrow> simpl_to_graph SGamma GGamma gf nn com n' (S' # S) P I inp_eqs out_eqs"
    apply (erule(1) inc_induct)
    apply clarsimp
    apply (erule(1) Suc)
    done

  hence ge: "\<And>S' m n'. simpl_to_graph SGamma GGamma gf nn com m (S' # S) P I inp_eqs out_eqs
    \<Longrightarrow> m \<ge> n' \<Longrightarrow> n' \<ge> n
    \<Longrightarrow> simpl_to_graph SGamma GGamma gf nn com n' (S' # S) P I inp_eqs out_eqs"
    by auto

  have terminating_case: "\<And>i j orig_tr' n1 tr1. (i, j, orig_tr') \<in> M n1 tr1
      \<Longrightarrow> tr \<in> exec_trace GGamma gf
      \<Longrightarrow> \<forall>v' \<in> M n1 tr1. fst v' > i \<longrightarrow> ((j, orig_tr'), snd v') \<notin> extend_rel
      \<Longrightarrow> \<exists>tr'. tr' \<in> c_trace SGamma
            \<and> restrict_map tr' {..j} = restrict_map orig_tr' {..j}
            \<and> trace_end_match out_eqs I (trace_end tr) (trace_end tr')"
    apply (cut_tac n'="min i j" and m="Suc (max i j)"
            and S'="{tr} \<times> {restrict_map orig_tr' {..j}}" in ge)
       apply (clarsimp simp: M_def simpl_to_graph_def suffix_tuple_closure_inter_insert)
       apply (erule_tac x=n' in allE, erule_tac x=n'' in allE, erule_tac x=tr' in allE)
       apply (simp add: Suc_le_eq)
       apply (drule(1) restrict_map_eq_Some_le)
       apply simp
      apply simp
     apply (clarsimp simp: M_def)
    apply (clarsimp simp: M_def)
    apply (erule_tac n''=j and tr'=orig_tr' in simpl_to_graphD,
      (rule conjI | assumption | simp)+)
     apply (simp add: suffix_tuple_closure_inter_insert)
     apply (metis min.idem)
    apply simp
    done

  have infinite_case:
    "\<And>v' n1 tr1. \<forall>v \<in> M n1 tr1. \<exists>v' \<in> M n1 tr1. fst v' > fst v \<and> (snd v, snd v') \<in> extend_rel
        \<Longrightarrow> tr \<in> exec_trace GGamma gf
        \<Longrightarrow> v' \<in> M n1 tr1
        \<Longrightarrow> \<exists>tr'. trace_end tr = None
            \<and> restrict_map tr' {.. n1} = restrict_map tr1 {.. n1}
            \<and> trace_end tr' = None
            \<and> tr' \<in> c_trace SGamma"
    apply (drule extensible_traces_to_infinite_trace_choice[where
          trace=snd and m=fst, rotated])
     apply (rule ballI, drule(1) bspec)
     apply fastforce
    apply (erule exE, rename_tac tr')
    apply (rule_tac x=tr' in exI)
    apply (rule conjI)
     apply (rule trace_end_None_ge_seq)
      apply (auto simp add: exec_trace_def)[1]
     apply clarsimp
     apply (drule_tac x=i in spec)
     apply (clarsimp simp: M_def)
     apply (blast intro: less_imp_le)
    apply (clarsimp simp: c_trace_def)
    apply (rule conjI)
     apply (drule_tac x=0 in spec)
     apply (clarsimp simp: M_def)
     apply (drule_tac i=n1 in restrict_map_eq_mono[rotated], assumption)+
     apply simp
    apply (rule trace_prefixes_to_trace)
    apply clarsimp
    apply (drule_tac x=i in spec)
    apply (clarsimp simp: M_def)
    apply (blast intro: less_imp_le)
    done

  show ?thesis
    apply (clarsimp simp: simpl_to_graph_def suffix_tuple_closure_inter_insert)
    apply (case_tac "(\<forall>v \<in> M n'' tr'. \<exists>v' \<in> M n'' tr'. fst v' > fst v \<and> (snd v, snd v') \<in> extend_rel)")
     apply (drule(1) infinite_case)
      apply (fastforce simp add: M_def)
     apply (fastforce simp: trace_end_match_def)
    apply clarsimp
    apply (frule(1) terminating_case, simp)
    apply (clarify, rename_tac soln_tr', rule_tac x=soln_tr' in exI)
    apply (clarsimp simp: M_def)
    apply (drule_tac i=n'' in restrict_map_eq_mono[rotated], assumption)+
    apply simp
    done
qed

lemma simpl_to_graph_induct:
  assumes Suc: "\<And>S' k. simpl_to_graph SGamma GGamma gf nn com (Suc n + k) (S' # S) P I inp_eqs out_eqs
    \<Longrightarrow> simpl_to_graph SGamma GGamma gf nn com (n + k) (S' # S) P I inp_eqs out_eqs"
  shows "simpl_to_graph SGamma GGamma gf nn com n S P I inp_eqs out_eqs"
  apply (rule simpl_to_graphI)
  apply (cut_tac tr=tr and n=n and S=S in simpl_to_graph_induct_proof)
   apply (cut_tac S'=S' and k="n'a - n" in Suc)
    apply simp+
  apply (erule simpl_to_graphD)
  apply (simp add: suffix_tuple_closure_inter_insert)
  apply blast
  done

definition
  "eq_impl addr eqs eqs2 S = (\<forall>gst sst. eqs gst sst \<longrightarrow> sst \<in> S \<longrightarrow> eqs2 gst sst)"

lemma eq_implD:
  "\<lbrakk> eq_impl addr eqs eqs2 S; eqs gst sst; sst \<in> S \<rbrakk>
        \<Longrightarrow> eqs2 gst sst"
  by (simp add: eq_impl_def)

lemma simpl_to_graph_cases:
  "simpl_to_graph SGamma GGamma gf nn com n traces (P \<inter> S) I inp_eqs out_eqs
    \<Longrightarrow> simpl_to_graph SGamma GGamma gf nn com n traces (P \<inter> - S) I inp_eqs out_eqs
    \<Longrightarrow> simpl_to_graph SGamma GGamma gf nn com n traces P I inp_eqs out_eqs"
  apply (rule simpl_to_graphI)
  apply (case_tac "sst \<in> S")
   apply (clarsimp simp only: simpl_to_graph_def[where P="P \<inter> S"] Compl_iff Int_iff)
  apply (clarsimp simp only: simpl_to_graph_def[where P="P \<inter> - S"] Compl_iff Int_iff)
  done

lemma exec_graph_step_image_node:
  "GGamma f = Some gf \<Longrightarrow> function_graph gf n = Some node
    \<Longrightarrow> exec_graph_step GGamma `` {[(NextNode n, gst, f)]}
      = exec_node GGamma gst node [(NextNode n, gst, f)]"
  by (cases gf, simp add: exec_graph_step_def)

definition
  "add_cont com conts
    = foldl (\<lambda>c d. case d of Inl d' \<Rightarrow> c ;; d' | Inr d' \<Rightarrow> com.Catch c d') com conts"

lemma add_cont_Cons:
  "add_cont c (Inl d # cont) = add_cont (c ;; d) cont"
  "add_cont c (Inr d # cont) = add_cont (com.Catch c d) cont"
  by (simp_all add: add_cont_def)

lemma add_cont_Nil:
  "add_cont c [] = c"
  by (simp add: add_cont_def)

lemma add_cont_step:
  "SGamma \<turnstile> (com, s) \<rightarrow> (com', s')
    \<Longrightarrow> SGamma \<turnstile> (add_cont com con, s) \<rightarrow> (add_cont com' con, s')"
  apply (induct con rule: rev_induct)
   apply (simp add: add_cont_def)
  apply (simp add: add_cont_def step.intros split: sum.split)
  done

lemma simpl_to_graph_Cond:
  "\<lbrakk> nn = NextNode m; GGamma gf = Some gfc; function_graph gfc m = Some (Cond l r cond);
        eq_impl nn eqs (\<lambda>gst sst. l \<noteq> r \<longrightarrow> cond gst = (sst \<in> C)) (P \<inter> I);
        eq_impl nn eqs eqs2 (P \<inter> I \<inter> C);
        simpl_to_graph SGamma GGamma gf l (add_cont c con) (Suc n) Q (P \<inter> C) I eqs2 out_eqs;
        eq_impl nn eqs eqs3 (P \<inter> I \<inter> (- C));
        simpl_to_graph SGamma GGamma gf r (add_cont d con) (Suc n) Q (P \<inter> - C) I eqs3 out_eqs \<rbrakk>
    \<Longrightarrow> simpl_to_graph SGamma GGamma gf nn (add_cont (com.Cond C c d) con) n Q P I eqs out_eqs"
  apply clarsimp
  apply (rule_tac S=C in simpl_to_graph_cases)
   apply (erule_tac nn'=l in simpl_to_graph_step[rotated])
   apply (simp add: exec_graph_step_image_node)
   apply (fastforce dest: eq_implD intro: step.intros add_cont_step)[1]
  apply (erule_tac nn'=r in simpl_to_graph_step[rotated])
  apply (simp add: exec_graph_step_image_node)
  apply (fastforce dest: eq_implD intro: step.intros add_cont_step)[1]
  done

lemma simpl_to_graph_weaken[rotated]:
  assumes eqs: "\<forall>gst sst. eqs gst sst \<and> sst \<in> P \<and> sst \<in> I
            \<longrightarrow> eqs2 gst sst \<and> sst \<in> Q"
  shows "simpl_to_graph SGamma GGamma gf nn com n tS Q I eqs2 out_eqs
    \<Longrightarrow> simpl_to_graph SGamma GGamma gf nn com n tS P I eqs out_eqs"
  using eqs
  apply (clarsimp simp add: simpl_to_graph_def)
  apply blast
  done

lemma simpl_to_graph_weaken_eq_impl:
  "eq_impl nn eqs eqs2 (I \<inter> P)
    \<Longrightarrow> simpl_to_graph SGamma GGamma gf nn com n tS P I eqs2 out_eqs
    \<Longrightarrow> simpl_to_graph SGamma GGamma gf nn com n tS P I eqs out_eqs"
  apply (erule simpl_to_graph_weaken)
  apply (simp add: eq_impl_def)
  done

lemma simpl_to_graph_While_lemma:
  assumes ps: "GGamma f = Some gf" "nn = NextNode m" "function_graph gf m = Some (Cond l r cond)"
        "eq_impl nn eqs (\<lambda>gst sst. cond gst = (sst \<in> C)) (I \<inter> P)"
  assumes loop: "\<And>k S. \<lbrakk> simpl_to_graph SGamma GGamma f nn (add_cont (com.While C c) con) (Suc (n + k)) (S # tS) P I eqs out_eqs \<rbrakk>
        \<Longrightarrow> simpl_to_graph SGamma GGamma f l (add_cont (c ;; com.While C c) con) (Suc (n + k)) (S # tS) (P \<inter> C) I eqs out_eqs"
  assumes exitloop: "simpl_to_graph SGamma GGamma f r (add_cont com.Skip con) (Suc n) tS (P \<inter> (- C)) I eqs out_eqs"
  shows "simpl_to_graph SGamma GGamma f nn (add_cont (com.While C c) con) n tS P I eqs out_eqs"
  apply (rule simpl_to_graph_induct)
  apply (simp add: ps)
  apply (rule_tac S=C in simpl_to_graph_cases)
   apply (rule simpl_to_graph_step[rotated])
    apply (rule loop)
    apply (simp add: ps)
   apply (frule eq_implD[OF ps(4)], simp+)
   apply (simp add: exec_graph_step_image_node ps)
   apply (blast intro: step.intros add_cont_step)
  apply (rule simpl_to_graph_step[rotated])
   apply (rule simpl_to_graph_ge_subset)
    apply (rule exitloop)
   apply fastforce
  apply (frule eq_implD[OF ps(4)], simp+)
  apply (simp add: exec_graph_step_image_node ps)
  apply (blast intro: step.intros add_cont_step)
  done

lemma simpl_to_graph_While_inst:
  assumes ps: "nn = NextNode m" "GGamma f = Some gf" "function_graph gf m = Some (Cond l r cond)"
        "eq_impl nn eqs (\<lambda>gst sst. cond gst = (sst \<in> C)) (I \<inter> G)"
   and ss_eq: "eq_impl nn eqs eqs2 (I \<inter> G \<inter> C)"
      and ss: "\<And>k S. \<lbrakk> simpl_to_graph SGamma GGamma f nn (add_cont (com.While C c) con) (Suc (n + k)) (S # tS) G I eqs out_eqs \<rbrakk>
        \<Longrightarrow> simpl_to_graph SGamma GGamma f l (add_cont (c ;; com.While C c) con) (Suc (n + k)) (S # tS) (G \<inter> C) I eqs2 out_eqs"
   and ex_eq: "eq_impl nn eqs eqs3 (I \<inter> G \<inter> - C)"
      and ex: "simpl_to_graph SGamma GGamma f r (add_cont com.Skip con) (Suc n) tS (G \<inter> (- C)) I eqs3 out_eqs"
   and in_eq: "eq_impl nn eqs (\<lambda>gst sst. sst \<in> G) (I \<inter> G')"
  shows "simpl_to_graph SGamma GGamma f nn (add_cont (com.While C c) con) n tS G' I eqs out_eqs"
  apply (rule simpl_to_graph_weaken)
   apply (rule simpl_to_graph_While_lemma[where P=G], (rule ps)+)
    apply (rule simpl_to_graph_weaken, erule ss)
    apply (clarsimp simp: ss_eq[THEN eq_implD])
   apply (rule simpl_to_graph_weaken, rule ex)
   apply (clarsimp simp: ex_eq[THEN eq_implD])
  apply (clarsimp simp: in_eq[THEN eq_implD])
  done

lemma use_simpl_to_graph_While_assum:
  "\<lbrakk> simpl_to_graph SGamma GGamma f nn com n tS P I eqs out_eqs;
    n \<le> n' \<and> set tS \<subseteq> set tS';
    eq_impl nn eqs (\<lambda>gst sst. sst \<in> P) (Q \<inter> I) \<rbrakk>
    \<Longrightarrow> simpl_to_graph SGamma GGamma f nn com n' tS' Q I eqs out_eqs"
  apply (erule simpl_to_graph_ge_subset[rotated])
  apply (erule simpl_to_graph_weaken)
  apply (auto simp add: eq_impl_def)
  done

lemma simpl_to_graph_Skip_immediate:
  "simpl_to_graph SGamma GGamma f nn (add_cont c con) n tS P I eqs out_eqs
    \<Longrightarrow> simpl_to_graph SGamma GGamma f nn (add_cont com.Skip (Inl c # con)) n tS P I eqs out_eqs"
  "simpl_to_graph SGamma GGamma f nn (add_cont com.Skip con) n tS P I eqs out_eqs
    \<Longrightarrow> simpl_to_graph SGamma GGamma f nn (add_cont com.Skip (Inr c # con)) n tS P I eqs out_eqs"
  apply (safe elim!: simpl_to_graph_step_R_unchanged[rotated])
   apply (auto simp: add_cont_Cons intro: add_cont_step step.intros)
  done

lemmas simpl_to_graph_Skip
    = simpl_to_graph_Skip_immediate[OF simpl_to_graph_weaken_eq_impl]

lemma simpl_to_graph_Throw_immediate:
  "simpl_to_graph SGamma GGamma f nn (add_cont com.Throw con) n tS P I eqs out_eqs
    \<Longrightarrow> simpl_to_graph SGamma GGamma f nn (add_cont com.Throw (Inl c # con)) n tS P I eqs out_eqs"
  "simpl_to_graph SGamma GGamma f nn (add_cont c con) n tS P I eqs out_eqs
    \<Longrightarrow> simpl_to_graph SGamma GGamma f nn (add_cont com.Throw (Inr c # con)) n tS P I eqs out_eqs"
  apply (safe elim!: simpl_to_graph_step_R_unchanged[rotated])
   apply (auto simp: add_cont_Cons intro: add_cont_step step.intros)
  done

lemmas simpl_to_graph_Throw
    = simpl_to_graph_Throw_immediate[OF simpl_to_graph_weaken_eq_impl]

lemma simpl_to_graph_Seq:
  "simpl_to_graph SGamma GGamma f nn (add_cont (c ;; d) con) n tS P I eqs out_eqs
    = simpl_to_graph SGamma GGamma f nn (add_cont c (Inl d # con)) n tS P I eqs out_eqs"
  by (simp add: add_cont_Cons)

lemma simpl_to_graph_Catch:
  "simpl_to_graph SGamma GGamma f nn (add_cont (com.Catch c d) con) n tS P I eqs out_eqs
    = simpl_to_graph SGamma GGamma f nn (add_cont c (Inr d # con)) n tS P I eqs out_eqs"
  by (simp add: add_cont_Cons)

lemma no_next_step: "eq_impl nn' eqs (\<lambda>gst' sst'.
        ((exec_graph_step GGamma) ^^ 0) `` {[(nn, gst', fn)]} \<subseteq> {[(nn, gst', fn)]}
        \<and> (\<forall>k < (0 :: nat). \<forall>st'. ([(nn, gst', fn)], st') \<in> exec_graph_step GGamma ^^ k
        \<longrightarrow> continuing st')) P"
  by (simp add: eq_impl_def)

lemma basic_next_step: "GGamma fn = Some gf \<Longrightarrow> function_graph gf m = Some (Basic nn' upds)
    \<Longrightarrow> eq_impl nn'' eqs (\<lambda>gst' sst'.
        ((exec_graph_step GGamma) ^^ 1) `` {[(NextNode m, gst', fn)]} \<subseteq> {[(nn', upd_vars upds gst', fn)]}
        \<and> (\<forall>k < 1. \<forall>st'. ([(NextNode m, gst', fn)], st') \<in> exec_graph_step GGamma ^^ k
        \<longrightarrow> continuing st')) P"
  apply (clarsimp simp: eq_impl_def simp del: imp_disjL)
  apply (clarsimp simp: exec_graph_step_def K_def split: graph_function.split_asm)
  done

lemma simpl_to_graph_Basic_next_step:
  assumes next_step: "eq_impl nn eqs (\<lambda>gst' sst'.
        ((exec_graph_step GGamma) ^^ steps) `` {[(nn, gst', fn)]} \<subseteq> {[(nn', f gst', fn)]}
        \<and> (\<forall>k < steps. \<forall>st'. ([(nn, gst', fn)], st') \<in> exec_graph_step GGamma ^^ k
        \<longrightarrow> continuing st')) (P \<inter> I)"
  shows
  "\<lbrakk> eq_impl nn eqs (\<lambda>gst sst. eqs2 (f gst) (f' sst) \<and> f' sst \<in> I \<and> f' sst \<in> Q) (P \<inter> I);
        simpl_to_graph SGamma GGamma fn nn' (add_cont com.Skip con) (n + min steps 1) tS Q I eqs2 out_eqs \<rbrakk>
    \<Longrightarrow> simpl_to_graph SGamma GGamma fn nn (add_cont (com.Basic f') con) n tS P I eqs out_eqs"
  apply (rule simpl_to_graph_step_general[where j=1 and i=steps, rotated -1])
   apply simp
  apply (frule eq_implD[OF next_step], simp)
  apply (simp add: eq_OO)
  apply (rule exI, rule conjI, blast intro: add_cont_step step.intros)
  apply (auto dest: eq_implD)
  done

lemmas simpl_to_graph_Basic_triv'
    = simpl_to_graph_Basic_next_step[OF no_next_step]

lemmas simpl_to_graph_Basic_triv = simpl_to_graph_Basic_triv'[where f'="\<lambda>x. x" and Q=UNIV]

lemmas simpl_to_graph_Basic
    = simpl_to_graph_Basic_next_step[OF basic_next_step, where Q=UNIV]

definition
  "upd_range upd_fun v = range (upd_fun (\<lambda>_. v))"

lemma simpl_to_graph_cbreak:
  "eq_impl nn eqs (\<lambda>gst sst. eqs2 gst (exn_upd (\<lambda>_. Break) sst) \<and> exn_upd (\<lambda>_. Break) sst \<in> I) (P \<inter> I)
    \<Longrightarrow> simpl_to_graph SGamma GGamma f nn
        (add_cont com.Throw con) n tS (upd_range exn_upd Break) I eqs2 out_eqs
    \<Longrightarrow> simpl_to_graph SGamma GGamma f nn
        (add_cont (cbreak exn_upd) con) n tS P I eqs out_eqs"
  apply (simp add: cbreak_def simpl_to_graph_Seq)
  apply (rule_tac simpl_to_graph_Basic_triv'[rotated])
   apply (rule simpl_to_graph_Skip_immediate)
   apply simp
  apply (simp add: upd_range_def)
  done

lemma simpl_to_graph_ccatchbrk_Break:
  "\<forall>f s. exn_var (exn_upd f s) = f (exn_var s)
    \<Longrightarrow> eq_impl nn eqs eqs2 (upd_range exn_upd Break \<inter> I)
    \<Longrightarrow> simpl_to_graph SGamma GGamma f nn
        (add_cont com.Skip con) n tS (upd_range exn_upd Break) I eqs2 out_eqs
    \<Longrightarrow> simpl_to_graph SGamma GGamma f nn
        (add_cont (ccatchbrk exn_var) con) n tS (upd_range exn_upd Break) I eqs out_eqs"
  apply (simp add: ccatchbrk_def)
  apply (rule simpl_to_graph_step_R_unchanged)
   apply (simp add: upd_range_def)
   apply (blast intro: add_cont_step step.intros)
  apply (erule simpl_to_graph_weaken, simp add: eq_impl_def)
  done

lemma simpl_to_graph_ccatchbrk_Return:
  "\<forall>f s. exn_var (exn_upd f s) = f (exn_var s)
    \<Longrightarrow> eq_impl nn eqs eqs2 (upd_range exn_upd Return \<inter> I)
    \<Longrightarrow> simpl_to_graph SGamma GGamma f nn
        (add_cont com.Throw con) n tS (upd_range exn_upd Return) I eqs2 out_eqs
    \<Longrightarrow> simpl_to_graph SGamma GGamma f nn
        (add_cont (ccatchbrk exn_var) con) n tS (upd_range exn_upd Return) I eqs out_eqs"
  apply (simp add: ccatchbrk_def)
  apply (rule simpl_to_graph_step_R_unchanged)
   apply (simp add: upd_range_def)
   apply (rule add_cont_step step.CondFalse)+
   apply clarsimp
  apply (erule simpl_to_graph_weaken, simp add: eq_impl_def)
  done

lemma simpl_to_graph_creturn_void:
  "eq_impl nn eqs (\<lambda>gst sst. eqs2 gst (exn_upd (\<lambda>_. Return) sst) \<and> exn_upd (\<lambda>_. Return) sst \<in> I) (P \<inter> I)
    \<Longrightarrow> simpl_to_graph SGamma GGamma f nn
        (add_cont com.Throw con) n tS (upd_range exn_upd Return) I eqs2 out_eqs
    \<Longrightarrow> simpl_to_graph SGamma GGamma f nn
        (add_cont (creturn_void exn_upd) con) n tS P I eqs out_eqs"
  apply (simp add: creturn_void_def simpl_to_graph_Seq)
  apply (rule_tac simpl_to_graph_Basic_triv'[rotated])
   apply (rule simpl_to_graph_Skip_immediate)
   apply simp
  apply (simp add: upd_range_def)
  done

lemma rtranclp_respects_fun:
  assumes respects: "\<And>x y. R x y \<Longrightarrow> R (f x) (f y)"
  shows "R\<^sup>*\<^sup>* x y \<Longrightarrow> R\<^sup>*\<^sup>* (f x) (f y)"
  apply (induct rule: rtranclp.induct)
   apply (fastforce intro: respects elim: rtranclp_trans)+
  done

lemma add_cont_steps:
  "\<Gamma> \<turnstile> (com, xs) \<rightarrow>\<^sup>* (com', xs')
    \<Longrightarrow> \<Gamma> \<turnstile> (add_cont com con, xs) \<rightarrow>\<^sup>* (add_cont com' con, xs')"
  apply (drule_tac f="\<lambda>(a, b). (add_cont a con, b)" in rtranclp_respects_fun[rotated])
   apply clarsimp
   apply (erule add_cont_step)
  apply simp
  done

lemma simpl_to_graph_steps_Fault:
  "\<forall>s \<in> P \<inter> I. \<exists>com'. SGamma \<turnstile> (com, Normal s) \<rightarrow>\<^sup>* (com', Fault F)
    \<Longrightarrow> simpl_to_graph SGamma GGamma gf nn (add_cont com con) n Q P I eqs out_eqs"
  apply (clarsimp intro!: simpl_to_graph_steps_Fault1)
  apply (drule_tac x=s in bspec, clarsimp+)
  apply (rule exI)
  apply (erule add_cont_steps)
  done

lemma simpl_to_graph_Guard:
  "\<lbrakk> nn = NextNode m; eq_impl nn eqs eqs2 (P \<inter> I \<inter> G);
        simpl_to_graph SGamma GGamma gf nn (add_cont c con) n Q (G \<inter> P) I eqs2 out_eqs \<rbrakk>
    \<Longrightarrow> simpl_to_graph SGamma GGamma gf nn (add_cont (com.Guard F G c) con) n Q P I eqs out_eqs"
  apply clarsimp
  apply (rule_tac S=G in simpl_to_graph_cases)
   apply (rule simpl_to_graph_step_R_unchanged[rotated])
    apply (erule simpl_to_graph_weaken)
    apply (simp add: eq_impl_def)
   apply (rule add_cont_step)
   apply (blast intro: step.Guard)
  apply (rule simpl_to_graph_steps_Fault)
  apply (blast intro: step.GuardFault)
  done

lemma simpl_to_graph_done:
  "\<lbrakk> eq_impl nn eqs out_eqs (P \<inter> I) \<rbrakk>
    \<Longrightarrow> simpl_to_graph SGamma GGamma gf Ret (add_cont com.Skip []) n Q P I eqs out_eqs"
  apply (clarsimp simp: c_trace_def add_cont_Nil intro!: simpl_to_graphI)
  apply (frule_tac i=n' in exec_trace_step_cases)
  apply (rule exI, rule context_conjI)
   apply (erule(1) nat_trace_rel_final, simp add: final_def)
  apply (clarsimp simp: trace_end_cut exec_graph_step_def)
  apply (clarsimp simp: exec_trace_def trace_end_eq_Some
                        eq_impl_def trace_end_match_def)
  done

lemma eq_impl_refl:
  "eq_impl nn eqs eqs P"
  by (simp add: eq_impl_def)

lemmas simpl_to_graph_done2 = simpl_to_graph_done[OF eq_impl_refl]
lemmas simpl_to_graph_creturn_void2 = simpl_to_graph_creturn_void[where nn=Ret, OF eq_impl_refl]

lemma simpl_to_graph_noop_Basic:
  "\<lbrakk> GGamma gf = Some gfc; function_graph gfc m = Some (node.Basic nn upds);
        eq_impl nn eqs (\<lambda>gst sst. eqs2 (upd_vars upds gst) sst) (P \<inter> I);
        simpl_to_graph SGamma GGamma gf nn c n Q P I eqs2 out_eqs \<rbrakk>
    \<Longrightarrow> simpl_to_graph SGamma GGamma gf (NextNode m) c n Q P I eqs out_eqs"
  apply (rule simpl_to_graph_step_general[where i=1 and j=0, rotated])
    apply simp+
  apply (simp add: exec_graph_step_image_node eq_impl_def K_def)
  done

lemma simpl_to_graph_noop:
  "\<lbrakk> GGamma gf = Some gfc; function_graph gfc m = Some (node.Basic nn []);
        simpl_to_graph SGamma GGamma gf nn c n Q P I eqs2 out_eqs;
        eq_impl nn eqs eqs2 (P \<inter> I) \<rbrakk>
    \<Longrightarrow> simpl_to_graph SGamma GGamma gf (NextNode m) c n Q P I eqs out_eqs"
  apply (erule(1) simpl_to_graph_noop_Basic, simp_all)
  apply (simp add: upd_vars_def save_vals_def eq_impl_def)
  done

lemmas simpl_to_graph_nearly_done
    = simpl_to_graph_noop[where c="add_cont com.Skip []"]

lemma eq_impl_triv: "eq_impl nn eqs eqs S"
  by (simp add: eq_impl_def)

lemmas simpl_to_graph_noop_same_eqs
    = simpl_to_graph_noop[OF _ _ _ eq_impl_triv]

definition
  exec_trace_inputs :: "graph_function \<Rightarrow> trace \<Rightarrow> variable list"
where
  "exec_trace_inputs gfun tr = (case tr 0 of Some [(nn, gst, _)]
    => acc_vars (function_inputs gfun) gst)"

definition
  graph_fun_refines
where
  "graph_fun_refines SGamma GGamma I inputs proc outputs fname
    = (\<exists>gf. GGamma fname = Some gf \<and> length (function_inputs gf) = length inputs
        \<and> length (function_outputs gf) = length outputs
        \<and> distinct (function_inputs gf)
        \<and> (\<forall>tr \<in> exec_trace GGamma fname.
            \<forall>s. map (\<lambda>i. i s) inputs = exec_trace_inputs gf tr \<and> s \<in> I
                \<longrightarrow> ((\<exists>ft. SGamma \<turnstile> \<langle>com.Call proc, Normal s\<rangle> \<Rightarrow> Fault ft)
                    \<or> (trace_end tr = None \<and> \<not> terminates SGamma (com.Call proc) (Normal s))
                    \<or> (\<exists>gst sst. SGamma \<turnstile> \<langle>com.Call proc, Normal s\<rangle> \<Rightarrow> Normal sst
                        \<and> trace_end tr = Some [(Ret, gst, fname)]
                        \<and> sst \<in> I \<and> map (\<lambda>j. j sst) outputs
                            = acc_vars (function_outputs gf) gst))))"

lemma var_acc_var_upd:
  "var_acc nm (var_upd nm' v st) = (if nm = nm' then v else var_acc nm st)"
  by (cases st, simp add: var_acc_def var_upd_def)

lemma var_acc_var_upd_same[simp]:
  "var_acc nm (var_upd nm v st) = v"
  by (simp add: var_acc_var_upd)

lemma var_acc_var_upd_diff:
  "nm \<noteq> nm' \<Longrightarrow> var_acc nm (var_upd nm' v st) = var_acc nm st"
  by (simp add: var_acc_var_upd)

lemma fetch_returned:
  "\<lbrakk> distinct vs; length vs = length xs \<rbrakk>
    \<Longrightarrow> acc_vars vs (save_vals vs xs st) = xs"
  apply (induct vs arbitrary: xs st)
   apply (simp add: acc_vars_def)
  apply (case_tac xs, simp_all add: save_vals_def acc_vars_def)
  apply (rule_tac P="\<lambda>st. var_acc a st = b" and Q="\<lambda>x. x \<in> set xs" for a b xs
            in fold_invariant, simp)
   apply simp
  apply (clarsimp simp: var_acc_var_upd set_zip)
  done

lemma c_trace_nontermination:
  "tr \<in> c_trace \<Gamma>
    \<Longrightarrow> trace_end tr = None
    \<Longrightarrow> tr 0 = Some (com, st)
    \<Longrightarrow> \<not> terminates \<Gamma> com st"
  apply (frule trace_end_NoneD, simp add: c_trace_def)
  apply (erule disjE)
   apply (clarsimp simp: c_trace_def nat_trace_rel_def)+
  apply (drule terminates_impl_no_infinite_trans_computation)
  apply auto
  done

lemma trace_end_Ret_Err:
  "trace \<in> exec_trace Gamma fname
    \<Longrightarrow> trace_end trace = Some v
    \<Longrightarrow> \<exists>gst er. v = [(er, gst, fname)] \<and> er \<in> {Ret, Err}"
  apply (frule trace_end_SomeD)
   apply (clarsimp simp: exec_trace_def, assumption)
  apply clarsimp
  apply (frule(1) exec_trace_invariant)
  apply (auto simp: continuing_def exec_graph_invariant_Cons
             split: list.split_asm next_node.split_asm,
         auto simp: exec_graph_invariant_def)
  done

lemma graph_fun_refines_from_simpl_to_graph_with_refine:
  "\<lbrakk> SGamma proc = Some com; GGamma fname = Some gf;
    simple_simpl_refines SGamma com' com;
    \<And>Q. simpl_to_graph SGamma GGamma fname (NextNode (entry_point gf)) (add_cont com' []) 0
        [Q] UNIV I eqs
        (\<lambda>s s'. map (\<lambda>i. var_acc i s) (function_outputs gf) = map (\<lambda>i. i s') outs);
        eq_impl (NextNode (entry_point gf))
          (\<lambda>gst sst. map (\<lambda>i. var_acc i gst) (function_inputs gf) = map (\<lambda>i. i sst) ins)
          eqs I;
        distinct (function_inputs gf); length ins = length (function_inputs gf);
        length outs = length (function_outputs gf) \<rbrakk>
    \<Longrightarrow> graph_fun_refines SGamma GGamma I ins proc outs fname"
  apply (clarsimp simp: graph_fun_refines_def)
  apply (frule exec_trace_def[THEN eqset_imp_iff, THEN iffD1])
  apply clarsimp
  apply (erule_tac x="UNIV \<times> {[0 \<mapsto> (com', Normal s)]}" in meta_allE)
  apply (drule_tac tr=tr and tr'="[0 \<mapsto> (com', Normal s)]"
          and n'=0 and n''=0 and sst=s in simpl_to_graphD)
   apply (rule conjI, assumption)
   apply (simp add: suffix_tuple_closure_inter_def exec_trace_def)
   apply (rule conjI)
    apply (erule eq_implD)
     apply (simp add: fetch_returned exec_trace_inputs_def acc_vars_def)
    apply simp
   apply (simp add: add_cont_Nil nat_trace_rel_def)
  apply (clarsimp simp: trace_end_match_def dest!: fun_cong[where x=0])
  apply (subgoal_tac "\<forall>st. trace_end tr'' = Some st
    \<longrightarrow> SGamma \<turnstile> \<langle>com.Call proc,Normal s\<rangle> \<Rightarrow> exec_final_step st")
   apply (elim disjE exE conjE)
     apply (clarsimp simp: exec_final_step_def)
    apply clarsimp
    apply (drule step_preserves_termination[rotated])
     apply (erule step.Call)
    apply (drule simple_simpl_refines_no_fault_terminatesD)
     apply (blast intro: exec.Call)
    apply (simp add: c_trace_nontermination simple_simpl_refines_def)
   apply (frule(1) trace_end_Ret_Err)
   apply (clarsimp simp: exec_final_step_def acc_vars_def)
   apply metis
  apply clarsimp
  apply (rule exec.Call, assumption)
  apply (erule simple_simpl_refines_no_fault_execD[rotated])
   apply (blast intro: exec.Call)
  apply (simp add: exec_via_trace)
  apply metis
  done

lemmas graph_fun_refines_from_simpl_to_graph
    = graph_fun_refines_from_simpl_to_graph_with_refine[OF _ _ simple_simpl_refines_refl]

lemma simpl_to_graph_name_simpl_state:
  "(\<And>sst. sst \<in> P \<Longrightarrow> simpl_to_graph SGamma GGamma gf nn com n traces {sst} I inp_eqs out_eqs)
    \<Longrightarrow> simpl_to_graph SGamma GGamma gf nn com n traces P I inp_eqs out_eqs"
  by (simp add: simpl_to_graph_def, blast)

lemma trace_drop_n_init:
  "tr \<in> exec_trace Gamma fn \<Longrightarrow> Gamma fn = Some gf
    \<Longrightarrow> function_graph gf n = Some (Call nn fn' inps outps)
    \<Longrightarrow> Gamma fn' = Some gf'
    \<Longrightarrow> tr i = Some [(NextNode n, st, fn'')]
    \<Longrightarrow> trace_drop_n (Suc i) (Suc 0) tr 0
        = Some [(NextNode (entry_point gf'), init_vars (function_inputs gf') inps st, fn')]"
  apply (frule(1) exec_trace_invariant)
  apply (simp add: exec_graph_invariant_Cons)
  apply (frule_tac tr=tr and i=i in exec_trace_step_cases)
  apply (clarsimp simp: exec_graph_step_def split: graph_function.split_asm)
  apply (simp add: trace_drop_n_def)
  done

lemma trace_drop_n_end:
  "tr \<in> exec_trace Gamma fn \<Longrightarrow> Gamma fn = Some gf
    \<Longrightarrow> function_graph gf n = Some (Call nn fn' inps outps)
    \<Longrightarrow> Gamma fn' = Some gf'
    \<Longrightarrow> tr i = Some [(NextNode n, st, fn'')]
    \<Longrightarrow> trace_drop_n (Suc i) (Suc 0) tr \<in> exec_trace Gamma fn'
    \<Longrightarrow> trace_end (trace_drop_n (Suc i) (Suc 0) tr) = Some [(Ret, st', fn''')]
    \<Longrightarrow> \<exists>j \<ge> 2. tr (i + j) = Some [(nn, return_vars (function_outputs gf') outps st' st, fn)]"
  apply (frule trace_end_SomeD, (auto simp: exec_trace_def)[1])
  apply clarsimp
  apply (rename_tac j')
  apply (drule(4) exec_trace_drop_n_rest[rotated 2, rule_format], simp)
  apply (frule_tac i="Suc (i + j')" in exec_trace_step_cases)
  apply (frule(1) exec_trace_invariant)
  apply (clarsimp simp: exec_graph_step_def exec_graph_invariant_def
                 split: graph_function.split_asm)
  apply (rule_tac x="Suc (Suc j')" in exI, simp)
  done

lemma nontermination_to_c_trace:
  "tr \<in> nat_trace_rel F {(cfg, cfg'). \<Gamma> \<turnstile> cfg \<rightarrow> cfg'}
    \<Longrightarrow> tr i = Some (add_cont com con, st)
    \<Longrightarrow> \<not> terminates \<Gamma> com st
    \<Longrightarrow> \<exists>tr'. tr' \<in> c_trace \<Gamma> \<and> restrict_map tr' {..i} = restrict_map tr {..i}
      \<and> trace_end tr' = None"
  apply (clarsimp simp: terminates_iff_no_infinite_computation inf_def)
  apply (rule_tac x="\<lambda>j. if j \<le> i then tr j else case f (j - i) of
      (com', st') \<Rightarrow> Some (add_cont com' con, st')" in exI)
  apply (rule conjI)
   apply (simp add: c_trace_def)
   apply (rule nat_trace_rel_split, assumption, simp_all)
     apply (simp add: split_def)
    apply (rule add_cont_step)
    apply (drule spec[where x=0])
    apply simp
   apply (clarsimp simp: nat_trace_rel_def split_def)
   apply (rule add_cont_step, simp)
  apply (frule(1) trace_Some_dom_superset)
  apply (rule conjI)
   apply (simp add: restrict_map_def fun_eq_iff)
  apply (simp only: trace_end_def)
  apply (rule if_not_P)
  apply (simp add: trace_end_def split_def subset_iff domIff)
  done

lemma simpl_to_graph_call_next_step:
  assumes graph: "nn = NextNode m" "GGamma p = Some gfc"
      "function_graph gfc m = Some (node.Call nn' p' args rets)"
  assumes next_step: "eq_impl nn eqs_inner (\<lambda>gst' sst'.
        ((exec_graph_step GGamma) ^^ steps) `` {[(nn', gst', p)]} \<subseteq> {[(nn'', f gst', p)]}
        \<and> (\<forall>k < steps. \<forall>st'. ([(nn', gst', p)], st') \<in> exec_graph_step GGamma ^^ k
        \<longrightarrow> continuing st')) I"
  and rel: "graph_fun_refines SGamma GGamma I inputs proc outputs p'"
  and modifies: "(\<forall>\<sigma>. SGamma \<turnstile>\<^bsub>/UNIV\<^esub> {\<sigma>} com.Call proc (Q \<sigma>)) \<or> (Q = (\<lambda>_. UNIV))"
  and init: "eq_impl nn eqs (\<lambda>gst sst. initf sst \<in> I
            \<and> map (\<lambda>i. i gst) args = map (\<lambda>i. i (initf sst)) inputs) (I \<inter> P)"
  and ret: "eq_impl nn eqs (\<lambda>gst sst. (\<forall>sst' vs. map (\<lambda>i. i sst') outputs = vs
                  \<and> sst' \<in> I \<and> sst' \<in> Q (initf sst)
        \<longrightarrow> eqs2 (f (save_vals rets vs gst))
                (f' sst sst' (ret sst sst')) \<and> f' sst sst' (ret sst sst') \<in> I
            \<and> eqs_inner (save_vals rets vs gst) (f' sst sst' (ret sst sst')))) I"
  and cont: "simpl_to_graph SGamma GGamma p nn'' (add_cont com.Skip con) n tS UNIV I eqs2 out_eqs"
  shows "simpl_to_graph SGamma GGamma p nn
        (add_cont (call initf proc ret (\<lambda>x y. com.Basic (f' x y))) con)
        n tS P I eqs out_eqs"
  apply (rule simpl_to_graph_name_simpl_state)
  apply (clarsimp simp: call_def block_def graph)
  apply (rule_tac i=0 and j=3 and P'="{initf sst}"
        and inp_eqs'="\<lambda>gst _. eqs gst sst \<and> sst \<in> I" in simpl_to_graph_step_general)
   apply (simp add: init[THEN eq_implD] numeral_3_eq_3 eq_OO)
   apply (rule conjI[OF _ refl])
   apply (intro relcomppI)
     apply (rule add_cont_step, rule step.DynCom)
    apply (simp add: add_cont_Cons[symmetric])
    apply (rule add_cont_step, rule step.Basic)
   apply (simp add: add_cont_Cons(1), rule add_cont_step, rule step.SeqSkip)
  apply simp
  apply (clarsimp intro!: simpl_to_graphI)
  apply (frule init[THEN eq_implD], simp+)
  apply (cut_tac rel, clarsimp simp: graph_fun_refines_def)
  apply (frule exec_trace_drop_n, (rule graph | assumption)+)
  apply (drule(1) bspec)
  apply (drule_tac x="initf sst" in spec)
  apply (clarsimp simp: exec_trace_inputs_def graph)
  apply (subst(asm) trace_drop_n_init, (assumption | rule graph)+)
  apply (clarsimp simp: init_vars_def fetch_returned)
  apply (elim disjE exE conjE)
    apply (frule(1) c_trace_may_extend_steps)
      apply (rule rtranclp_trans)
       apply (rule add_cont_steps)
       apply (erule exec_impl_steps_Fault)
      apply (rule steps_Fault)
     apply assumption
    apply (clarsimp simp: c_trace_def)
    apply (rule exI, rule context_conjI)
     apply (erule(1) nat_trace_rel_final, fastforce simp: final_def)
    apply (simp add: trace_end_cut trace_end_match_def)
   apply (frule(2) trace_end_trace_drop_n_None)
   apply (frule(2) nontermination_to_c_trace)
   apply (auto simp: trace_end_match_def)[1]
  apply (frule trace_drop_n_end, (assumption | rule graph)+)
  apply (frule(1) c_trace_may_extend_steps)
    apply (rule rtranclp_trans)
     apply (rule add_cont_steps)
     apply (erule exec_impl_steps_Normal)
    apply (simp add: add_cont_Cons)
    apply (rule add_cont_steps)
    apply (rule exec_impl_steps_Normal)
    apply (rule exec.CatchMiss exec.Seq exec.Skip exec.DynCom exec.Basic | simp)+
  apply clarsimp
  apply (frule ret[THEN eq_implD], simp, clarsimp)
  apply (drule_tac x=ssta in spec, drule mp, rule conjI, assumption)
   apply (rule disjE[OF modifies])
    apply (drule spec, drule cvalidD[OF hoare_sound], simp+)
     apply clarsimp
    apply auto[1]
   apply simp
  apply clarsimp
  apply (frule next_step[THEN eq_implD], simp)
  apply (clarsimp simp: return_vars_def)
  apply (frule(3) exec_graph_trace_must_take_steps)
  apply (cut_tac tr=tr and tr'=trace' and n''="n'' + ja"
      and sst="f' a b c" for a b c in simpl_to_graphD[OF cont])
   apply auto[1]
  apply (metis restrict_map_eq_mono[OF le_add1])
  done

lemmas simpl_to_graph_call_triv
    = simpl_to_graph_call_next_step[where f'="\<lambda>x y s. s",
        where eqs_inner="\<lambda>_ _. True", OF _ _ _ no_next_step]

lemmas simpl_to_graph_call
    = simpl_to_graph_call_next_step[OF _ _ _ basic_next_step,
        where eqs_inner="\<lambda>_ _. True"]

lemma known_guard_then_basic_next_step:
  "GGamma fn = Some gf \<Longrightarrow> function_graph gf m = Some (node.Cond (NextNode m') Err C)
    \<Longrightarrow> GGamma fn = Some gf \<Longrightarrow> function_graph gf m' = Some (node.Basic nn'' upds)
    \<Longrightarrow> eq_impl nn (\<lambda>gst' sst'. C gst') (\<lambda>gst' sst'.
        ((exec_graph_step GGamma) ^^ 2) `` {[(NextNode m, gst', fn)]} \<subseteq> {[(nn'', upd_vars upds gst', fn)]}
        \<and> (\<forall>k < 2. \<forall>st'. ([(NextNode m, gst', fn)], st') \<in> exec_graph_step GGamma ^^ k
        \<longrightarrow> continuing st')) I"
  apply (clarsimp simp: eq_impl_def)
  apply (drule_tac n=m and gst=gst and GGamma=GGamma
    in exec_graph_step_image_node[rotated], simp)
  apply (drule_tac n=m' and gst=gst and GGamma=GGamma
    in exec_graph_step_image_node[rotated], simp)
  apply (simp add: numeral_2_eq_2 relcomp_Image less_Suc_eq K_def)
  apply (simp add: set_eq_iff)
  done

lemmas simpl_to_graph_call_known_guard
    = simpl_to_graph_call_next_step[OF _ _ _ known_guard_then_basic_next_step]

lemma simpl_to_graph_lvar_nondet_init:
  assumes stg: "simpl_to_graph SGamma GGamma fname nn (add_cont com.Skip con) n traces UNIV I eqs2 out_eqs"
      and eqs: "eq_impl nn eqs (\<lambda>gst sst. \<forall>f. eqs2 gst (updf f sst) \<and> updf f sst \<in> I) (P \<inter> I)"
  shows "simpl_to_graph SGamma GGamma fname nn
        (add_cont (lvar_nondet_init accf updf) con) n traces P I eqs out_eqs"
  apply (rule simpl_to_graph_step_R[OF _ stg])
  apply (simp add: lvar_nondet_init_def)
  apply (drule eq_implD[OF eqs], simp)
  apply (rule exI, rule conjI, rule add_cont_step)
   apply (rule step.Spec)
   apply simp
   apply (rule_tac x=undefined in exI, simp)
  apply simp
  done

lemmas load_word_defs = load_word32_def load_word64_def
lemmas store_word_defs = store_word32_def store_word64_def

lemma c_guard_ptr_val_gt_0:
  "c_guard (p :: ('a :: mem_type) ptr) \<Longrightarrow> ptr_val p > 0"
  apply (simp only: word_neq_0_conv[symmetric], rule notI)
  apply (cases p, simp)
  done

lemma h_val_word8:
  "h_val hp p = load_word8 (ptr_val p) hp"
  by (simp add: h_val_def load_word8_def from_bytes_def typ_info_word
                word_rcat_bl)

lemma h_val_word32:
  "h_val hp p = load_word32 (ptr_val p) hp"
  by (simp add: h_val_def load_word32_def from_bytes_def typ_info_word)

lemma h_val_word64:
  "h_val hp p = load_word64 (ptr_val p) hp"
  by (simp add: h_val_def load_word64_def from_bytes_def typ_info_word)

lemma h_val_ptr:
  "h_val hp (p :: ('a :: c_type) ptr ptr) = Ptr (load_machine_word (ptr_val p) hp)"
  by (simp add: h_val_def load_word_defs from_bytes_def typ_info_ptr word_size_def)

(* FIXME: should this go into Word.word_ubin near norm_Rep? *)
lemma bintrunc_len_eq_signed:
  "bintrunc LENGTH('a) (uint (x :: 'a :: len signed word)) = uint x"
  by (metis (full_types) len_signed word_of_int_uint word_ubin.eq_norm)

lemma uint_word_of_int_uint_signed_unsigned:
  "uint (word_of_int (uint (x :: 'a :: len signed word)) :: 'a word) = uint x"
  by (metis len_signed uint_word_of_int_eq word_uint.Rep_inverse)

(*FIXME: move to lib *)
lemma is_up_is_down_remove_sign[simp]:
  "is_up (UCAST('a :: len signed \<rightarrow> 'a))"
  "is_down (UCAST('a signed \<rightarrow> 'a))"
  unfolding is_up_def is_down_def source_size target_size by simp_all

(*FIXME: move to lib *)
lemma to_bytes_remove_sign:
  "to_bytes (w :: 'a :: len8 signed word) = to_bytes (UCAST('a signed \<rightarrow> 'a) w)"
  by (simp add: to_bytes_def typ_info_word word_rsplit_def uint_up_ucast)

(*FIXME: move to lib *)
lemma size_of_remove_sign:
  "size_of TYPE('a :: len8 signed word) = size_of TYPE('a word)"
  by (simp add: size_of_def typ_info_word)

(*FIXME: move to lib *)
lemma heap_update_remove_sign:
  "heap_update p (w :: 'a :: len8 signed word) hp =
    heap_update (PTR_COERCE('a signed word \<rightarrow> 'a word) p) (ucast w) hp"
  by (simp add: heap_update_def to_bytes_remove_sign size_of_remove_sign)

lemma heap_update_word8:
  "heap_update p (w :: 8 word) hp = store_word8 (ptr_val p) w hp"
  by (simp add: heap_update_def to_bytes_def typ_info_word store_word8_def word_rsplit_same)

lemma heap_update_sword8:
  "heap_update p (w :: 8 signed word) hp = store_word8 (ptr_val p) (ucast w) hp"
  by (simp add: heap_update_def store_word8_def to_bytes_remove_sign to_bytes_word8)

lemma heap_update_word32:
  "heap_update p w hp = store_word32 (ptr_val p) w hp"
  by (simp add: heap_update_def to_bytes_def typ_info_word store_word32_def)

lemma heap_update_sword32:
  "heap_update p (w :: 32 signed word) hp = store_word32 (ptr_val p) (ucast w) hp"
  by (simp add: heap_update_remove_sign heap_update_word32)

lemma heap_update_word64:
  "heap_update p w hp = store_word64 (ptr_val p) w hp"
  by (simp add: heap_update_def to_bytes_def typ_info_word store_word64_def)

lemma heap_update_sword64:
  "heap_update p (w :: 64 signed word) hp = store_word64 (ptr_val p) (ucast w) hp"
  by (simp add: heap_update_remove_sign heap_update_word64)

lemma heap_update_ptr:
  "heap_update (p :: ('a :: c_type) ptr ptr) p' hp = store_machine_word (ptr_val p) (ptr_val p') hp"
  by (simp add: heap_update_def to_bytes_def typ_info_ptr store_word_defs)

lemma from_bytes_ucast_isom[OF refl refl]:
  "x = from_bytes xs \<Longrightarrow> y = from_bytes xs
    \<Longrightarrow> size x = size y
    \<Longrightarrow> size x = length xs * 8
    \<Longrightarrow> ucast x = y"
  apply (clarsimp simp: word_size from_bytes_def typ_info_word)
  apply (rule word_eqI)
  apply (simp add: nth_ucast word_size test_bit_rcat[OF refl refl])
  done

lemma h_val_sword8:
  "(h_val hp p :: 8 signed word) = ucast (h_val hp (ptr_coerce p) :: 8 word)"
  by (simp add: h_val_def from_bytes_ucast_isom word_size)

lemma h_val_sword32:
  "(h_val hp p :: 32 signed word) = ucast (h_val hp (ptr_coerce p) :: 32 word)"
  by (simp add: h_val_def from_bytes_ucast_isom word_size)

lemma h_val_sword64:
  "(h_val hp p :: 64 signed word) = ucast (h_val hp (ptr_coerce p) :: 64 word)"
  by (simp add: h_val_def from_bytes_ucast_isom word_size)

lemma to_bytes_ucast_isom[OF refl]:
  "y = ucast x
    \<Longrightarrow> size x = size y
    \<Longrightarrow> 8 dvd size x
    \<Longrightarrow> to_bytes y = to_bytes x"
  apply (rule ext)
  apply (clarsimp simp: word_size to_bytes_def typ_info_word)
  apply (rule nth_equalityI)
   apply (simp add: word_size length_word_rsplit_exp_size')
  apply (clarsimp simp: dvd_def)
  apply (rule word_eqI)
  apply (simp add: test_bit_rsplit_alt length_word_rsplit_exp_size' word_size
                   nth_ucast)
  apply auto
  done

lemma to_bytes_sword:
  "to_bytes (w :: ('a :: len8) signed word)
    = to_bytes (ucast w :: 'a word)"
  by (simp add: to_bytes_ucast_isom word_size len8_dv8)

lemma heap_list_update_word8:
  "heap_update_list addr (to_bytes w (heap_list hp' 1 addr')) hp
    = store_word8 addr w hp"
  "heap_update_list addr (to_bytes w [hp' addr']) hp
    = store_word8 addr w hp"
  by (simp_all add: to_bytes_def store_word8_def typ_info_word word_rsplit_same)

lemma heap_list_update_word32:
  "heap_update_list addr (to_bytes w (heap_list hp' 4 addr')) hp
    = store_word32 addr w hp"
  by (simp add: to_bytes_def store_word32_def typ_info_word)

lemma heap_list_update_word64:
  "heap_update_list addr (to_bytes w (heap_list hp' 8 addr')) hp
    = store_word64 addr w hp"
  by (simp add: to_bytes_def store_word64_def typ_info_word)

lemma heap_list_update_ptr:
  "heap_update_list addr (to_bytes p (heap_list hp' word_size addr')) hp
    = store_machine_word addr (ptr_val (p :: ('a :: c_type) ptr)) hp"
  by (simp add: to_bytes_def store_word_defs typ_info_ptr)

lemma field_lvalue_offset_eq:
  "field_lookup (typ_info_t TYPE('a :: c_type)) f 0 = Some v
        \<Longrightarrow> field_lvalue (ptr :: 'a ptr) f = ptr_val ptr + of_nat (snd v)"
  apply (cases v, simp, drule field_lookup_offset_eq)
  apply (simp add: field_lvalue_def)
  done

lemmas h_val_word_simps =
  h_val_word8 h_val_sword8
  h_val_word32 h_val_sword32
  h_val_word64 h_val_sword64
  h_val_ptr

lemmas heap_update_word_simps =
  heap_update_word8 heap_update_sword8
  heap_update_word32 heap_update_sword32
  heap_update_word64 heap_update_sword64
  heap_update_ptr

lemmas heap_list_update_word_simps =
  heap_list_update_word8
  heap_list_update_word32
  heap_list_update_word64
  heap_list_update_ptr[unfolded word_size_def]

lemma image_fst_cart_UNIV_subset:
  "S \<subseteq> (fst ` S) \<times> UNIV"
  by (auto elim: image_eqI[rotated])

lemma simpl_to_graph_Err_cond:
  "\<lbrakk> nn = NextNode m; GGamma fname = Some gf;
      function_graph gf m = Some (node.Cond l Err Check);
      eq_impl nn eqs (\<lambda>gst sst. Check gst) (P \<inter> I);
      eq_impl nn eqs eqs2 (P \<inter> I);
      simpl_to_graph SGamma GGamma fname l com n traces P I eqs2 out_eqs \<rbrakk>
    \<Longrightarrow> simpl_to_graph SGamma GGamma fname nn com n traces P I eqs out_eqs"
  apply (rule_tac i=1 and j=0 in simpl_to_graph_step_general[rotated -1])
    apply simp
   apply (simp add: exec_graph_step_image_node)
   apply (auto dest: eq_implD)
  done

lemma simpl_to_graph_impossible:
  "eq_impl nn eqs (\<lambda>_ _. False) (P \<inter> I)
    \<Longrightarrow> simpl_to_graph SGamma GGamma fname nn com n traces P I eqs out_eqs"
  apply (rule simpl_to_graphI, clarsimp)
  apply (drule(1) eq_implD, simp+)
  done

definition[simp]: "VarMachineWord = arch_machine_word_constructor VarWord32 VarWord64"

definition
  "asm_args_to_list enc xs m_ms
    = map VarMachineWord xs @ [VarMem (fst m_ms), VarMS (enc (snd m_ms))]"

definition
  "asm_rets_to_list ret enc v mem_vs
    = (if ret then [VarMachineWord v] else []) @ [VarMem (fst mem_vs), VarMS (enc (snd mem_vs))]"

definition
  asm_fun_refines
where
  "asm_fun_refines specname ret enc len GGamma fname
    = (\<exists>gf. GGamma fname = Some gf
        \<and> distinct (function_inputs gf)
        \<and> length (function_inputs gf) = len
        \<and> (\<forall>tr \<in> exec_trace GGamma fname. \<forall>inp_vs inp_mem_ms.
                exec_trace_inputs gf tr = asm_args_to_list enc inp_vs inp_mem_ms
                \<longrightarrow> (\<exists>r gst.
                          r \<in> asm_semantics specname inp_vs inp_mem_ms
                        \<and> trace_end tr = Some [(Ret, gst, fname)]
                        \<and> acc_vars (function_outputs gf) gst = split (asm_rets_to_list ret enc) r)))"

lemma asm_args_to_list_inj:
  "(asm_args_to_list enc vs mem_ms = asm_args_to_list enc vs' mem_ms')
    = (vs = vs' \<and> fst mem_ms = fst mem_ms' \<and> enc (snd mem_ms) = enc (snd mem_ms'))"
  apply (simp add: asm_args_to_list_def)
  apply (subst inj_map_eq_map)
   apply (rule inj_onI, simp)
  apply simp
  done

lemma simpl_to_graph_call_asm_fun:
  assumes graph: "nn = NextNode m" "GGamma p = Some gfc"
      "function_graph gfc m = Some (node.Call nn' p' args rets)"
  and rel: "asm_fun_refines specname ret enc len GGamma p'"
  and init: "eq_impl nn eqs (\<lambda>gst sst. sst \<in> I
            \<and> map (\<lambda>i. i gst) args = asm_args_to_list enc (asm_args sst)
                (asm_fetch (globals sst))
            \<and> length args = len) (I \<inter> P)"
  and ret: "eq_impl nn eqs (\<lambda>gst sst. (\<forall>m' v' (ms' :: 'a).
            gdata (asm_store gdata (m', ms') (globals sst)) = gdata (globals sst)
            \<and> (v', (m', ms')) \<in> asm_semantics specname (asm_args sst) (asm_fetch (globals sst))
            \<longrightarrow> eqs2 (save_vals rets (asm_rets_to_list ret enc v' (m', ms')) gst)
                 (asm_ret v' (globals_update (asm_store gdata (m', ms')) sst))
                \<and> asm_ret v' (globals_update (asm_store gdata (m', ms')) sst) \<in> I)) I"
  and cont: "simpl_to_graph SGamma GGamma p nn' (add_cont com.Skip con) n tS UNIV I eqs2 out_eqs"
  shows "simpl_to_graph SGamma GGamma p nn
        (add_cont (Spec (asm_spec (ti :: 'a itself) gdata vol specname asm_ret asm_args)) con)
        n tS P I eqs out_eqs"
  apply (rule simpl_to_graph_name_simpl_state)
  apply (clarsimp simp: graph intro!: simpl_to_graphI)
  apply (frule init[THEN eq_implD], simp+)
  apply (cut_tac rel, clarsimp simp: asm_fun_refines_def)
  apply (frule exec_trace_drop_n, (rule graph | assumption)+)
  apply (drule(1) bspec)
  apply (clarsimp simp: exec_trace_inputs_def graph)
  apply (subst(asm) trace_drop_n_init, (assumption | rule graph)+)
  apply (clarsimp simp: init_vars_def)
  apply (subst(asm) fetch_returned, simp_all)
   apply (drule arg_cong[where f=length])+
   apply simp
  apply (simp add: asm_args_to_list_inj)
  apply (drule spec, drule mp, rule refl)
  apply clarsimp
  apply (frule trace_drop_n_end, (assumption | rule graph)+)
  apply clarsimp
  apply (frule(1) c_trace_may_extend_steps)
    apply (rule add_cont_steps)
    apply (rule exec_impl_steps_Normal)
    apply (rule exec.Spec)
    apply (simp add: asm_spec_def)
    apply (erule rev_bexI)
    apply simp
   apply simp
  apply clarsimp
  apply (frule ret[THEN eq_implD], simp)
  apply (cut_tac tr=tr and tr'=trace' and n''="n'' + ja"
      and sst="asm_ret a b" for a b in simpl_to_graphD[OF cont])
   apply (auto simp: return_vars_def asm_store_eq)[1]
  apply (metis restrict_map_eq_mono[OF le_add1])
  done

lemma take_1_drop:
  "n < length xs \<Longrightarrow> take (Suc 0) (drop n xs) = [xs ! n]"
  apply (cases "drop n xs")
   apply simp
  apply (clarsimp dest!: nth_via_drop)
  done

lemma ptr_safe_field:
  "\<lbrakk> ptr_safe (p :: ('a :: mem_type) ptr) d; field_ti TYPE('a) f = Some t;
        export_uinfo t = typ_uinfo_t TYPE('b) \<rbrakk>
    \<Longrightarrow> ptr_safe (Ptr &(p\<rightarrow>f) :: ('b :: mem_type) ptr) d"
  apply (clarsimp simp: field_ti_def split: option.split_asm)
  apply (erule(2) ptr_safe_mono)
  done

lemma heap_update_list_If1:
  "length xs \<le> addr_card
   \<Longrightarrow> heap_update_list p xs hp
     = (\<lambda>x. if unat (x - p) < length xs then xs ! unat (x - p) else hp x)"
  apply (subst coerce_heap_update_to_heap_updates[where chunk = 1, OF _ refl])
   apply simp
  apply (rule ext)
  apply (subst foldl_cong[OF refl refl])
   apply (clarsimp simp: take_1_drop)
   apply (rule refl)
  apply (induct xs rule: rev_induct)
   apply simp
  apply (simp split del: if_split)
  apply (subst foldl_cong[OF refl refl])
   apply (clarsimp simp: nth_append)
   apply (rule refl)
  apply (simp add: nth_append split del: if_split cong: if_cong)
  apply (auto simp: addr_card linorder_not_less less_Suc_eq take_bit_nat_eq_self unat_of_nat
              dest: word_unat.Rep_inverse')
  done

lemma heap_update_list_If2:
  "length xs \<le> addr_card
   \<Longrightarrow> heap_update_list p xs hp
     = (\<lambda>x. if x \<in> {p ..+ length xs} then xs ! unat (x - p) else hp x)"
  apply (simp add: heap_update_list_If1)
  apply (rule ext, simp add: intvl_def)
  apply clarsimp
  apply (erule notE, erule order_le_less_trans[rotated])
  apply (simp add: unat_of_nat)
  done

lemma word_sless_to_less:
  "\<lbrakk> 0 <=s x; 0 <=s y \<rbrakk> \<Longrightarrow> (x <s y) = (x < y)"
  apply (simp add: word_sless_alt word_sle_def word_less_def)
  apply (simp add: sint_eq_uint word_msb_sint)
  done

lemma word_sle_to_le:
  "\<lbrakk> 0 <=s x; 0 <=s y \<rbrakk> \<Longrightarrow> (x <=s y) = (x <= y)"
  apply (simp add: word_sle_def word_le_def)
  apply (simp add: sint_eq_uint word_msb_sint)
  done

ML \<open>

structure SimplToGraphProof = struct

fun mk_ptr_val_app p =
    Const (@{const_name ptr_val}, fastype_of p --> @{typ machine_word}) $ p

fun mk_arr_idx arr i = let
    val arrT = fastype_of arr
    val elT = case arrT of Type (@{type_name "array"}, [elT, _])
        => elT | _ => raise TYPE ("mk_arr_idx", [arrT], [arr])
  in Const (@{const_name "Arrays.index"}, arrT --> @{typ nat} --> elT)
    $ arr $ i
  end

val gammaT_to_stateT = strip_type #> snd
        #> dest_Type #> snd #> the_single
        #> dest_Type #> snd #> hd

fun mk_simpl_acc ctxt sT nm = let
    val sst = Free ("sst", sT)
    val symbol_table = Free ("symbol_table", @{typ "string => machine_word"})

    val [globals, globals_swap, t_hrs, t_hrs_update, globals_list, pms, pms_encode] =
        map (Syntax.read_term ctxt) [
          "globals :: globals myvars \<Rightarrow> _",
          "globals_swap :: (globals \<Rightarrow> _) \<Rightarrow> _",
          "t_hrs_' :: globals \<Rightarrow> _",
          "t_hrs_'_update :: _ \<Rightarrow> globals \<Rightarrow> globals",
          "globals_list",
          "phantom_machine_state_' :: globals \<Rightarrow> _",
          "encode_machine_state"
        ];

    val globals_sst = globals $ sst
    val _ = type_of globals_sst (* does type checking *)

    val globals_swap = globals_swap $ t_hrs $ t_hrs_update $ symbol_table $ globals_list

    fun do_pms_encode t = case pms_encode of Const _ => pms_encode $ t
      | _ => raise TERM ("mk_simpl_acc: requires `encode_machine_state :: machine_state => unit \<times> nat'", [t])

    val ghost_assns_fetch = Syntax.read_term ctxt "ghost_assns_from_globals"
    fun get_ghost_assns_fetch () = case head_of ghost_assns_fetch of Const _ => ghost_assns_fetch
      | _ => raise TERM ("mk_simpl_acc: requires `ghost_assns_from_globals :: globals => ghost_assertions", [])

    fun mk_sst_acc "Mem" = @{term hrs_mem} $ (t_hrs $ (globals_swap $ globals_sst))
      | mk_sst_acc "HTD" = @{term hrs_htd} $ (t_hrs $ globals_sst)
      | mk_sst_acc "PMS" = do_pms_encode (pms $ globals_sst)
      | mk_sst_acc "GhostAssertions" = get_ghost_assns_fetch () $ globals_sst
      | mk_sst_acc nm = if String.isPrefix "rv#space#" nm
              then mk_sst_acc (unprefix "rv#space#" nm)
              else if String.isSuffix "#v" nm
              then Syntax.read_term ctxt
                  (suffix "_'" (unsuffix "#v" nm) ^ " :: globals myvars => _") $ sst
              else let
                  val (head, tail) = Library.space_explode "." nm
                      |> Library.split_last |> apfst (Library.space_implode ".")
                  val acc = mk_sst_acc head
                  val typ_nm = fastype_of acc |> dest_Type |> fst
                  val acc2 = if typ_nm = "Arrays.array"
                    then mk_arr_idx acc (HOLogic.mk_number @{typ nat}
                        (ParseGraph.parse_int tail))
                    else Proof_Context.read_const {proper = true, strict = true}
                        ctxt (typ_nm ^ "." ^ tail) $ acc
                in acc2 end
    fun mk_sst_acc2 nm = let
        val acc = mk_sst_acc nm
        val T = fastype_of acc |> dest_Type |> fst
      in if T = @{type_name ptr} then mk_ptr_val_app acc else acc end
  in Term.lambda sst (ParseGraph.mk_var_term (mk_sst_acc2 nm)) end

fun foldr1_default _ v [] = v
  | foldr1_default f _ xs = foldr1 f xs

datatype hints = Hints of { deps: (string * term) list Inttab.table,
    hint_tactics: (Proof.context -> int -> tactic) Inttab.table,
    err_conds: Inttab.set }

fun mk_graph_eqs Gamma (Hints hints) nm n = let
    val vs = case (Inttab.lookup (#deps hints) n) of
      SOME vs => vs
    | NONE => raise TERM ("mk_graph_eqs: " ^ nm ^ " " ^ string_of_int n, [])
    val sT = gammaT_to_stateT (fastype_of Gamma)
    val sst = Free ("sst", sT)

    val gst = @{term "gst :: GraphLang.state"}

    fun mk_eq (nm, acc) = HOLogic.mk_eq (@{term var_acc} $ HOLogic.mk_string nm $ gst,
        betapply (acc, sst))
    val eqs = map mk_eq vs
  in Term.lambda gst (Term.lambda sst
        (foldr1_default HOLogic.mk_conj @{term True} eqs)) end

fun with_cache cache termfun tracer t = case Termtab.lookup (! cache) t
    of SOME v => v
    | NONE => let val v = termfun t
    in tracer t v; cache := Termtab.insert (K false) (t, v) (! cache); v end

fun dest_nat (@{term Suc} $ n) = dest_nat n + 1
  | dest_nat (@{term "0 :: nat"}) = 0
  | dest_nat n = HOLogic.dest_number n |> snd

fun simpl_to_graph_skel hints nm (Const (@{const_name simpl_to_graph}, T)
                $ SG $ GG $ gfname $ (@{term NextNode} $ nn) $ com
                $ _ $ trS $ P $ I $ _ $ out_eqs)
    = Const (@{const_name simpl_to_graph}, T)
        $ SG $ GG $ gfname $ (@{term NextNode} $ nn) $ com
        $ @{term "n :: nat"} $ Free ("trS", fastype_of trS)
        $ P $ I $ mk_graph_eqs SG hints nm (dest_nat nn) $ out_eqs
  | simpl_to_graph_skel _ _ t = raise TERM ("simpl_to_graph_skel", [t])

fun simpl_to_graph_nn (Const (@{const_name simpl_to_graph}, _)
                $ _ $ _ $ _ $ (@{term NextNode} $ nn) $ _
                $ _ $ _ $ _ $ _ $ _ $ _)
    = dest_nat nn
  | simpl_to_graph_nn t = raise TERM ("simpl_to_graph_nn", [t])

fun SUBGOAL tfun i t = Tactical.SUBGOAL tfun i t
  handle TYPE (s, tps, ts) => raise TYPE ("SUBGOAL " ^ s,
    tps, [Thm.cprem_of t i |> Thm.term_of] @ ts)

val standard_GG = @{term "GG :: string \<Rightarrow> graph_function option"}

fun graph_gamma_tac ctxt = SUBGOAL (fn (t, i) => let
    val (lhs, _) = HOLogic.dest_Trueprop (Logic.strip_assums_concl
        (Envir.beta_eta_contract t)) |> HOLogic.dest_eq
    val _ = (head_of lhs = standard_GG andalso length (snd (strip_comb lhs)) = 1)
      orelse raise TERM ("GG lhs", [])
    val nm = the_single (snd (strip_comb lhs)) |> HOLogic.dest_string
        |> Long_Name.base_name
    val gfun = Syntax.read_term ctxt (nm ^ "_graph_fun")
    val gfun_def = Proof_Context.get_thm ctxt (nm ^ "_graph_fun_def")
    val _ = dest_Const (head_of gfun)
    val GG_assum = HOLogic.mk_eq
            (lhs, @{term "Some :: graph_function \<Rightarrow> _"} $ gfun)
        |> HOLogic.mk_Trueprop |> Thm.cterm_of ctxt |> Thm.assume
        |> simplify (put_simpset HOL_basic_ss ctxt addsimps [gfun_def])
  in resolve0_tac [GG_assum] i end
    handle TERM (s, ts) => raise TERM ("graph_gamma_tac: " ^ s, t :: ts))

fun inst_graph_node_tac ctxt =
  simp_tac (put_simpset HOL_basic_ss ctxt addsimps @{thms function_graph.simps})
  THEN' SUBGOAL (fn (t, i) => case
    HOLogic.dest_Trueprop (Logic.strip_assums_concl
        (Envir.beta_eta_contract t))
  of @{term "(=) :: node option \<Rightarrow> _"} $ (f $ n) $ _ => (let
    val g = head_of f |> dest_Const |> fst
    val n' = dest_nat n
    val thm = Proof_Context.get_thm ctxt
        (Long_Name.base_name g ^ "_" ^ Int.toString n')
    val thm = if n = @{term "Suc 0"}
        then simplify (put_simpset HOL_basic_ss ctxt addsimps @{thms One_nat_def}) thm
        else thm
  in resolve0_tac [thm] i end handle TERM (s, ts) => raise TERM ("inst_graph_node_tac: " ^ s, t :: ts))
  | t => raise TERM ("inst_graph_node_tac", [t]))

fun inst_graph_tac ctxt = graph_gamma_tac ctxt THEN' inst_graph_node_tac ctxt

fun mk_graph_refines (funs : ParseGraph.funs) ctxt s = let
    val proc = Syntax.read_term ctxt
        (Long_Name.base_name s ^ "_'proc")
    val gamma = Syntax.read_term ctxt "\<Gamma>"
    val invs = Syntax.read_term ctxt "simpl_invariant"
    val _ = case head_of invs of Const _ => ()
      | _ => raise TERM ("mk_graph_refines: requires simpl_invariant constant", [])
    val sT = fastype_of gamma |> gammaT_to_stateT
    val (xs, ys, _) = Symtab.lookup funs s |> the
    val inputs = map (mk_simpl_acc ctxt sT) xs
        |> HOLogic.mk_list (sT --> @{typ variable})
    val outputs = map (mk_simpl_acc ctxt sT) ys
        |> HOLogic.mk_list (sT --> @{typ variable})
  in HOLogic.mk_Trueprop (Const (@{const_name graph_fun_refines}, [fastype_of gamma,
      @{typ "string \<Rightarrow> graph_function option"}, fastype_of invs,
      fastype_of inputs, fastype_of proc, fastype_of outputs,
      @{typ string}] ---> @{typ bool})
    $ gamma $ standard_GG $ invs $ inputs $ proc $ outputs
    $ HOLogic.mk_string s)
  end

fun asm_spec_name_to_fn_name _ specname = let
    val name = space_implode "_" (space_explode " " specname)
  in "asm_instruction'" ^ name end

fun mk_asm_refines (funs : ParseGraph.funs) ctxt specname = let
    val s = asm_spec_name_to_fn_name true specname
    val (xs, ys, _) = Symtab.lookup funs s |> the
    val enc = Syntax.read_term ctxt "encode_machine_state"
    val _ = case enc of Const _ => ()
      | _ => raise TERM ("mk_simpl_acc: requires `encode_machine_state :: machine_state => unit \<times> nat'", [])
  in HOLogic.mk_Trueprop (Const (@{const_name asm_fun_refines},
        [@{typ string}, @{typ bool}, fastype_of enc, @{typ nat},
            fastype_of standard_GG, @{typ string}] ---> @{typ bool})
    $ HOLogic.mk_string specname
    $ (if (length ys > 2) then @{term True} else @{term False})
    $ enc
    $ HOLogic.mk_number @{typ nat} (length xs)
    $ standard_GG $ HOLogic.mk_string s)
  end

fun apply_graph_refines_ex_tac funs ctxt = SUBGOAL (fn (t, i) => case
    (Logic.strip_assums_concl (Envir.beta_eta_contract t)) of
    @{term Trueprop} $ (Const (@{const_name graph_fun_refines}, _)
        $ _ $ _ $ _ $ _ $ _ $ _ $ s)
        => (resolve0_tac [Thm.assume (Thm.cterm_of ctxt
            (mk_graph_refines funs ctxt (HOLogic.dest_string s)))] i)
        | _ => raise TERM ("apply_graph_refines_ex_tac", [t]))

fun apply_asm_refines_ex_tac funs ctxt = SUBGOAL (fn (t, i) => case
    (Logic.strip_assums_concl (Envir.beta_eta_contract t)) of
    @{term Trueprop} $ (Const (@{const_name asm_fun_refines}, _)
        $ specname $ _ $ _ $ _ $ _ $ _)
        => (resolve0_tac [Thm.assume (Thm.cterm_of ctxt
            (mk_asm_refines funs ctxt (HOLogic.dest_string specname)))] i)
        | _ => raise TERM ("apply_graph_refines_ex_tac", [t]))

fun apply_impl_thm ctxt = SUBGOAL (fn (t, i) => case
        Logic.strip_assums_concl (Envir.beta_eta_contract t)
    of @{term Trueprop} $ (Const (@{const_name HOL.eq}, _)
        $ (_ $ Const (s, _)) $ (Const (@{const_name Some}, _) $ _))
    => resolve0_tac [Proof_Context.get_thm ctxt
        (suffix "_impl" (unsuffix "_'proc" (Long_Name.base_name s)))] i
  | _ => no_tac)

fun get_Call_args (Const (@{const_name com.Call}, _) $ x) = [x]
  | get_Call_args (f $ x) = get_Call_args f @ get_Call_args x
  | get_Call_args (Abs (_, _, t)) = get_Call_args t
  | get_Call_args _ = []

fun apply_modifies_thm ctxt = SUBGOAL (fn (t, i) => case
        get_Call_args (Envir.beta_eta_contract t)
    of [Const (s, _)] => let
        val s = unsuffix "_'proc" (Long_Name.base_name s)
        val thms = (@{thm disjI1}, Proof_Context.get_thm ctxt (s ^ "_modifies"))
            handle ERROR _ => (@{thm disjI2}, @{thm refl})
      in resolve0_tac [fst thms] i THEN resolve0_tac [snd thms] i end
    | _ => no_tac)

fun is_safe_eq_impl (p as (@{term Trueprop}
        $ (Const (@{const_name "eq_impl"}, _) $ _ $ _ $ _ $ _)))
    = not (exists_subterm (fn Var _ => true | Free ("n", _) => true
                        | _ => false) p)
  | is_safe_eq_impl _ = false

fun eq_impl_assume_tac ctxt = DETERM o SUBGOAL (fn (t, i) => let
    val p = Logic.strip_assums_concl (Envir.beta_eta_contract t)
  in if is_safe_eq_impl p
    then resolve0_tac [Thm.assume (Thm.cterm_of ctxt p)] i
    else no_tac
  end)

fun is_pglobal_valid_conjs (Const (@{const_name conj}, _) $ p $ q)
    = is_pglobal_valid_conjs p andalso is_pglobal_valid_conjs q
  | is_pglobal_valid_conjs (Const (@{const_name "pglobal_valid"}, _) $ _ $ _ $ _)
    = true
  | is_pglobal_valid_conjs _ = false

fun simpl_ss ctxt = put_simpset HOL_basic_ss ctxt
    addsimps @{thms switch.simps fst_conv snd_conv
        length_Cons singletonI triv_forall_equality
        simpl_to_graph_Seq simpl_to_graph_Catch
}

val immediates = @{thms
    simpl_to_graph_Skip_immediate simpl_to_graph_Throw_immediate}

fun except_tac ctxt msg = SUBGOAL (fn (t, _) => let
  in warning msg; Syntax.pretty_term ctxt t |> Pretty.writeln;
    raise TERM (msg, [t]) end)

fun apply_hint_thm ctxt (Hints hints) = SUBGOAL (fn (t, i) => let
    val nn = Logic.strip_assums_concl t |> Envir.beta_eta_contract
        |> HOLogic.dest_Trueprop |> simpl_to_graph_nn
  in case Inttab.lookup (#hint_tactics hints) nn
    of SOME tac => tac ctxt i
      | NONE => no_tac end
    handle TERM _ => no_tac)

fun check_err_cond_tac (Hints hints) = SUBGOAL (fn (t, _) => let
    val nn = Logic.strip_assums_concl t |> Envir.beta_eta_contract
        |> HOLogic.dest_Trueprop |> simpl_to_graph_nn
  in case Inttab.lookup (#err_conds hints) nn
    of SOME () => all_tac
      | NONE => no_tac end
    handle TERM _ => no_tac)

fun apply_simpl_to_graph_tac funs hints ctxt =
        simp_tac (simpl_ss ctxt
            addsimps @{thms One_nat_def whileAnno_def
                creturn_def[folded creturn_void_def]})
    THEN' DETERM o (FIRST' [
        apply_hint_thm ctxt hints,
        resolve0_tac [@{thm simpl_to_graph_Basic_triv}],
        resolve_tac ctxt @{thms simpl_to_graph_lvar_nondet_init
            simpl_to_graph_Skip
            simpl_to_graph_Throw
            simpl_to_graph_cbreak
            simpl_to_graph_creturn_void},
        resolve_tac ctxt @{thms
                simpl_to_graph_ccatchbrk_Break
                simpl_to_graph_ccatchbrk_Return}
            THEN' (simp_tac ctxt
                THEN_ALL_NEW except_tac ctxt
                    "apply_simpl_to_graph_tac: exn eq unsolved"),
        resolve0_tac [@{thm simpl_to_graph_Guard[OF refl]}],
        check_err_cond_tac hints
            THEN' resolve0_tac [@{thm simpl_to_graph_Err_cond[OF refl]}]
            THEN' inst_graph_tac ctxt,
        resolve0_tac [@{thm simpl_to_graph_Cond[OF refl]}]
            THEN' inst_graph_tac ctxt,
        resolve0_tac [@{thm simpl_to_graph_Basic}]
            THEN' inst_graph_tac ctxt,
        resolve0_tac [@{thm simpl_to_graph_call_triv[OF refl]}]
            THEN' inst_graph_tac ctxt
            THEN' apply_graph_refines_ex_tac funs ctxt
            THEN' apply_modifies_thm ctxt,
        resolve0_tac [@{thm simpl_to_graph_call[OF refl]}]
            THEN' inst_graph_tac ctxt
            THEN' inst_graph_tac ctxt
            THEN' apply_graph_refines_ex_tac funs ctxt
            THEN' apply_modifies_thm ctxt,
        resolve0_tac [@{thm simpl_to_graph_call_known_guard[OF refl]}]
            THEN' inst_graph_tac ctxt
            THEN' inst_graph_tac ctxt
            THEN' inst_graph_tac ctxt
            THEN' apply_graph_refines_ex_tac funs ctxt
            THEN' apply_modifies_thm ctxt,
        resolve0_tac [@{thm simpl_to_graph_call_asm_fun[OF refl]}]
            THEN' inst_graph_tac ctxt
            THEN' apply_asm_refines_ex_tac funs ctxt,
        resolve0_tac [@{thm simpl_to_graph_nearly_done}]
            THEN' inst_graph_tac ctxt
    ] THEN_ALL_NEW (TRY o REPEAT_ALL_NEW
        (resolve_tac ctxt immediates)))

fun trace_cache _ (SOME thm) = tracing
  ("Adding thm to cache with " ^ string_of_int (Thm.nprems_of thm) ^ " prems.")
  | trace_cache _ NONE = tracing "Adding NONE to cache."

fun simpl_to_graph_cache_tac funs hints cache nm ctxt =
        simp_tac (simpl_ss ctxt)
    THEN_ALL_NEW DETERM o FIRST' [
        SUBGOAL (fn (t, i) => (case
        with_cache cache (mk_simpl_to_graph_thm funs hints cache nm ctxt) (K (K ()))
            (simpl_to_graph_skel hints nm (HOLogic.dest_Trueprop
                (Logic.strip_assums_concl (Envir.beta_eta_contract t)))) of
            SOME thm => resolve0_tac [thm] i | _ => no_tac)
            handle TERM _ => no_tac),
        resolve_tac ctxt @{thms simpl_to_graph_done2
            simpl_to_graph_Skip_immediate[where nn=Ret]
            simpl_to_graph_Throw_immediate[where nn=Ret]
            simpl_to_graph_creturn_void2},
        eq_impl_assume_tac ctxt
    ]

and mk_simpl_to_graph_thm funs hints cache nm ctxt tm = let
    val ct = Thm.cterm_of ctxt (HOLogic.mk_Trueprop tm)
  in Thm.trivial ct
    |> (apply_simpl_to_graph_tac funs hints ctxt
        THEN_ALL_NEW (TRY o simpl_to_graph_cache_tac funs hints cache nm ctxt)
        THEN_ALL_NEW (TRY o eq_impl_assume_tac ctxt)) 1
    |> Seq.hd
    |> Drule.generalize (Names.empty, Names.make_set ["n", "trS"])
    |> SOME
  end handle TERM (s, _) => (tracing ("mk_simpl_to_graph_thm: " ^ s); NONE)
    | Empty => (tracing "mk_simpl_to_graph_thm: raised Empty on:";
          tracing (Syntax.pretty_term ctxt tm |> Pretty.string_of);
          NONE)
    | Option => NONE

fun dest_next_node (@{term NextNode} $ n)
    = dest_nat n
  | dest_next_node @{term Ret} = ~1
  | dest_next_node @{term Err} = ~2
  | dest_next_node t = raise TERM ("dest_next_node", [t])

fun get_while (Const (@{const_name simpl_to_graph}, _)
                $ _ $ _ $ _ $ nn
                $ (Const (@{const_name add_cont}, _) $ (Const (@{const_name While}, _) $ C $ c) $ _)
                $ _ $ _ $ _ $ _ $ _ $ _)
    = (dest_next_node nn, C, c)
  | get_while t = raise TERM ("get_while", [t])

fun check_while_assums t = let
    val hyps = Logic.strip_assums_hyp t
        |> filter (fn (@{term Trueprop} $ (@{term "All :: (nat => _) => _"} $ _))
                => true | _ => false)
  in length hyps < 2 orelse raise TERM ("check_while_assums: too many", []);
    () end

fun get_while_body_guard C c = case c of
    Const (@{const_name com.Seq}, _) $ _ $ last => let
    val setT = fastype_of C
    fun mk_int (x, y) = Const (fst (dest_Const @{term "(Int)"}),
        setT --> setT --> setT) $ x $ y
    fun build_guard (Const (@{const_name Guard}, _) $ _ $ G
        $ Const (@{const_name com.Skip}, _))
      = G
      | build_guard (Const (@{const_name Guard}, _) $ _ $ G $ c)
      = mk_int (G, build_guard c)
      | build_guard _ = error ""
    val G = case try build_guard last of SOME G => G
      | NONE => Const (fst (dest_Const @{term "UNIV"}), setT)
  in G end
  | _ => Const (fst (dest_Const @{term "UNIV"}), fastype_of C)

fun simpl_to_graph_While_tac hints nm ctxt =
    simp_tac (simpl_ss ctxt)
  THEN' SUBGOAL (fn (t, i) => let
    val t = HOLogic.dest_Trueprop (Logic.strip_assums_concl
        (Envir.beta_eta_contract t))
    val (_, Cond, body) = get_while t
    val gd = get_while_body_guard Cond body
    val skel = simpl_to_graph_skel hints nm t
    val ct = Thm.cterm_of ctxt (HOLogic.mk_Trueprop skel)
    val rl_inst = infer_instantiate ctxt [(("G",0), Thm.cterm_of ctxt gd)]
        @{thm simpl_to_graph_While_inst}
  in
    resolve_tac ctxt [Thm.trivial ct |> Drule.generalize (Names.empty, Names.make_set ["n", "trS"])] i
        THEN resolve_tac ctxt [rl_inst] i
        THEN resolve_tac ctxt @{thms refl} i
        THEN inst_graph_tac ctxt i
  end handle TERM _ => no_tac)

fun trace_fail_tac ctxt s = SUBGOAL (fn (t, _) =>
  (Syntax.pretty_term ctxt t |> Pretty.string_of
    |> prefix ("Tactic " ^ s ^ " failed on: ") |> tracing;
    no_tac))

fun trace_fail_tac2 _ = K no_tac

fun simpl_to_graph_tac funs hints nm ctxt = let
    val cache = ref (Termtab.empty)
  in REPEAT_ALL_NEW (DETERM o (full_simp_tac (simpl_ss ctxt) THEN_ALL_NEW
    SUBGOAL (fn (t, i) => fn thm =>
      ((simpl_to_graph_cache_tac funs hints cache nm ctxt
    ORELSE' (eresolve0_tac [@{thm use_simpl_to_graph_While_assum}]
        THEN' simp_tac ctxt)
    ORELSE' simpl_to_graph_While_tac hints nm ctxt
    ORELSE' trace_fail_tac ctxt "simpl_to_graph_tac") i thm
        handle Empty => (tracing "simpl_to_graph_tac: raised Empty on:";
          tracing (Syntax.pretty_term ctxt t |> Pretty.string_of);
          Seq.empty)))
    ))
  end

fun get_conts (@{term node.Basic} $ nn $ _) = [nn]
  | get_conts (@{term node.Cond} $ l $ _ $ Abs (_, _, @{term True})) = [l]
  | get_conts (@{term node.Cond} $ _ $ r $ Abs (_, _, @{term False})) = [r]
  | get_conts (@{term node.Cond} $ l $ r $ _) = [l, r]
  | get_conts (@{term node.Call} $ nn $ _ $ _ $ _) = [nn]
  | get_conts n = raise TERM ("get_conts", [n])

fun get_rvals (Abs (_, _, t)) = let
    fun inner (Const _ $ (s as (@{term "(#) :: char \<Rightarrow> _"} $ _ $ _)) $ Bound 0)
      = [HOLogic.dest_string s]
      | inner (f $ x) = inner f @ inner x
      | inner (Const _) = []
      | inner (Free ("symbol_table", _)) = []
      | inner t = raise TERM ("get_rvals", [t])
  in inner t end
  | get_rvals t = raise TERM ("get_rvals", [t])

fun flip f x y = f y x

fun get_lvals_rvals (@{term node.Basic} $ _ $ upds) = let
    val (lvs, rvs) = HOLogic.dest_list upds |> map_split HOLogic.dest_prod
  in (map HOLogic.dest_string lvs, maps get_rvals rvs) end
  | get_lvals_rvals (@{term node.Cond} $ _ $ _ $ cond) = ([], get_rvals cond)
  | get_lvals_rvals (@{term node.Call} $ _ $ _ $ args $ rets)
    = (HOLogic.dest_list rets |> map HOLogic.dest_string,
      HOLogic.dest_list args |> maps get_rvals)
  | get_lvals_rvals n = raise TERM ("get_conts", [n])

fun get_var_deps nodes ep outputs = let
    fun forward tab (point :: points) = if point < 0
      then forward tab points
      else let
        val node = Inttab.lookup nodes point |> the
        val conts = map dest_next_node (get_conts node)
        val upds = filter_out (Inttab.lookup_list tab #>
          flip (Ord_List.member int_ord) point) conts
        val tab = fold (fn c => Inttab.map_default (c, [])
          (Ord_List.insert int_ord point)) conts tab
      in forward tab (upds @ points) end
      | forward tab [] = tab
    val preds = forward (Inttab.make [(ep, [])]) [ep]
    fun backward tab (point :: points) = let
        val node = Inttab.lookup nodes point |> the
        val conts = map dest_next_node (get_conts node)
        val (lvs, rvs) = get_lvals_rvals node
          |> apply2 (Ord_List.make string_ord)
        val cont_vars = maps (Inttab.lookup_list tab) conts
          |> Ord_List.make string_ord
        val vars = Ord_List.merge string_ord (rvs,
            Ord_List.subtract string_ord lvs cont_vars)
        val prev_vars = Inttab.lookup tab point
        val tab = Inttab.update (point, vars) tab
        val upds = if prev_vars <> SOME vars
            then Inttab.lookup_list preds point else []
      in backward tab (upds @ points) end
      | backward tab [] = tab
    val deps = backward (Inttab.make [(~1, outputs), (~2, [])])
      (maps (Inttab.lookup_list preds) [~1, ~2])
  in (preds, deps) end

fun get_loop_var_upd_nodes nodes =
    nodes
    |> filter (snd #> (fn (@{term Basic} $ _ $ _) => true | _ => false))
    |> filter (snd #> get_lvals_rvals #> fst
        #> (fn xs => not (null xs) andalso forall (String.isSuffix "#count") xs))
    |> map fst

fun get_err_conds nodes =
    nodes
    |> filter (snd #> (fn (@{term Cond} $ _ $ @{term Err} $ _) => true | _ => false))
    |> map fst

fun mk_hints (funs : ParseGraph.funs) ctxt nm = case Symtab.lookup funs nm of
    NONE => raise TERM ("mk_var_deps_hints: miss " ^ nm, [])
  | SOME (_, _, NONE) => Hints {deps = Inttab.empty, hint_tactics = Inttab.empty,
        err_conds = Inttab.empty}
  | SOME (_, outputs, SOME (ep, nodes, _)) => let
    val sT = Syntax.read_typ ctxt "globals myvars"
    val deps = snd (get_var_deps (Inttab.make nodes) ep outputs)
        |> Inttab.map (K (filter_out (fn s => String.isSuffix "#count" s)
            #> map (fn s => (s, mk_simpl_acc ctxt sT s))))
    val no_deps_nodes = map fst nodes
        |> filter_out (Inttab.defined deps)
    val all_deps = Inttab.join (fn _ => error "mk_hints")
        (deps, Inttab.make (map (rpair []) no_deps_nodes))
    val no_deps_tacs = no_deps_nodes
        |> map (rpair (K (resolve0_tac [@{thm simpl_to_graph_impossible}])))
    val loop_tacs = get_loop_var_upd_nodes nodes
        |> map (rpair (fn ctxt => resolve0_tac [@{thm simpl_to_graph_noop_Basic}]
            THEN' inst_graph_tac ctxt))
    val all_tacs = Inttab.make (no_deps_tacs @ loop_tacs)
    val ec = get_err_conds nodes |> Inttab.make_set
  in Hints {deps = all_deps,
    hint_tactics = all_tacs,
    err_conds = ec} end

fun init_graph_refines_proof funs nm ctxt = let
    val body_ref_thm = Get_Body_Refines.get ctxt (Long_Name.base_name nm)
    val ct = mk_graph_refines funs ctxt nm |> Thm.cterm_of ctxt
  in Thm.trivial ct
    |> (resolve_tac ctxt [@{thm graph_fun_refines_from_simpl_to_graph_with_refine}] 1
        THEN apply_impl_thm ctxt 1
        THEN graph_gamma_tac ctxt 1
        THEN resolve_tac ctxt [body_ref_thm] 1
        THEN ALLGOALS (simp_tac (put_simpset HOL_basic_ss ctxt
            addsimps @{thms entry_point.simps function_inputs.simps
                            function_outputs.simps list.simps}))
        THEN TRY ((resolve_tac ctxt [@{thm simpl_to_graph_noop_same_eqs}]
            THEN' inst_graph_tac ctxt) 1)
    )
    |> Seq.hd
  end

val thin_While_assums_rule =
    @{thm thin_rl[where V="simpl_to_graph SG GG f nn (add_cont (com.While C c) con) n tS P I e e2"]}
        |> Drule.generalize (Names.empty, Names.make_set ["SG", "GG", "f", "nn", "C", "c", "con", "n", "tS", "P", "I", "e", "e2"])

fun eq_impl_unassume_tac t = let
    val hyps = t |> Thm.chyps_of
        |> filter (Thm.term_of #> is_safe_eq_impl)
  in (* tracing ("Restoring " ^ string_of_int (length hyps) ^ " hyps.") ; *)
    fold Thm.implies_intr hyps t |> Seq.single end

fun simpl_to_graph_upto_subgoals funs hints nm ctxt =
    init_graph_refines_proof funs nm ctxt
    |> (simpl_to_graph_tac funs hints nm ctxt 1
        THEN ALLGOALS (TRY o REPEAT_ALL_NEW (eresolve0_tac [thin_While_assums_rule]))
        THEN eq_impl_unassume_tac
    ) |> Seq.hd

end

\<close>

ML \<open>
fun define_graph_fun_short funs s =
  Local_Theory.begin_nested
  #> snd
  #> ParseGraph.define_graph_fun funs (Long_Name.base_name s ^ "_graph")
                                 (Binding.name (Long_Name.base_name s ^ "_graph_fun")) s
  #> Local_Theory.end_nested
\<close>

end

