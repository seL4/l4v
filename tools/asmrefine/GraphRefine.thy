(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory GraphRefine

imports TailrecPre GraphLangLemmas "../../lib/LemmaBucket_C"

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
    by (auto split: split_if_asm)
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
     apply blast
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

lemma exec_graph_trace_must_take_steps:
  "trace \<in> exec_trace \<Gamma> fn
    \<Longrightarrow> trace i = Some [(nn, st, fn)]
    \<Longrightarrow> (exec_graph_step \<Gamma> ^^ j) `` {[(nn, st, fn)]} \<subseteq> {[(nn', st', fn)]}
    \<Longrightarrow> j < 2 \<and> (j = 0 \<or> nn \<notin> {Ret, Err})
    \<Longrightarrow> trace (i + j) = Some [(nn', st', fn)]"
  apply (cases j)
   apply simp
  apply (case_tac nat, simp_all)
  apply (frule_tac i=i in exec_trace_step_cases)
  apply clarsimp
  apply (drule subsetD, erule ImageI, simp)
  apply simp
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
            \<and> sst' \<in> P' \<and> sst' \<in> I \<and> inp_eqs' gst' sst')
    \<Longrightarrow> (i < 2 \<and> (i = 0 \<or> nn \<notin> {Ret, Err}))
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
                   split: split_if_asm)
    apply (drule_tac x=i in spec)
    apply (auto simp: le_Suc_eq)
    done

  have f_norm:
    "\<forall>i j. j \<le> fst (trace (?f i)) \<longrightarrow> snd (trace (?f i)) j = snd (trace (?f j)) j"
    apply clarsimp
    apply (cut_tac i=j and j="min i j" and k="max i j" in f_eq[rule_format])
      apply (simp add: min_def linorder_not_le f_induct)
     apply simp
    apply (simp add: min_def max_def split: split_if_asm)
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
  apply (simp split: split_if_asm)
  apply (auto simp: fun_eq_iff split: split_if_asm)
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

  { fix S' Q'
    note bchoice[where Q="\<lambda>x y. y \<in> S' \<and> Q' x y", folded Bex_def]
  } note bbchoice = this

  have infinite_case:
    "\<And>v' n1 tr1. \<forall>v \<in> M n1 tr1. \<exists>v' \<in> M n1 tr1. fst v' > fst v \<and> (snd v, snd v') \<in> extend_rel
        \<Longrightarrow> tr \<in> exec_trace GGamma gf
        \<Longrightarrow> v' \<in> M n1 tr1
        \<Longrightarrow> \<exists>tr'. trace_end tr = None
            \<and> restrict_map tr' {.. n1} = restrict_map tr1 {.. n1}
            \<and> trace_end tr' = None
            \<and> tr' \<in> c_trace SGamma"
    apply (drule bbchoice)
    apply (elim exE)
    apply (frule_tac trace=snd and m=fst and f=f
          in extensible_traces_to_infinite_trace[rotated])
     apply simp
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
   apply blast
  apply (clarsimp simp only: simpl_to_graph_def[where P="P \<inter> - S"] Compl_iff Int_iff)
  apply blast
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
        simpl_to_graph SGamma GGamma gf l (add_cont c con) (Suc n) Q P I eqs2 out_eqs;
        eq_impl nn eqs eqs2 (P \<inter> I \<inter> C);
        simpl_to_graph SGamma GGamma gf r (add_cont d con) (Suc n) Q P I eqs3 out_eqs;
        eq_impl nn eqs eqs3 (P \<inter> I \<inter> (- C)) \<rbrakk>
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

lemma simpl_to_graph_While_UNIV:
  assumes ps: "GGamma f = Some gf" "nn = NextNode m" "function_graph gf m = Some (Cond l r cond)"
        "eq_impl nn eqs (\<lambda>gst sst. cond gst = (sst \<in> C)) I"
  assumes ss: "\<And>k S. \<lbrakk> simpl_to_graph SGamma GGamma f nn (add_cont (com.While C c) con) (Suc (n + k)) (S # tS) UNIV I eqs out_eqs \<rbrakk>
        \<Longrightarrow> simpl_to_graph SGamma GGamma f l (add_cont (c ;; com.While C c) con) (Suc (n + k)) (S # tS) C I eqs2 out_eqs"
   and ss_eq: "eq_impl nn eqs eqs2 (I \<inter> C)"
  assumes ex: "simpl_to_graph SGamma GGamma f r (add_cont com.Skip con) (Suc n) tS (- C) I eqs3 out_eqs"
   and ex_eq: "eq_impl nn eqs eqs3 (I \<inter> - C)"
  shows "simpl_to_graph SGamma GGamma f nn (add_cont (com.While C c) con) n tS P I eqs out_eqs"
  apply (rule simpl_to_graph_weaken)
   apply (rule simpl_to_graph_While_lemma[where P=UNIV], (rule ps)+)
     apply (simp, rule ps)
    apply simp
    apply (rule simpl_to_graph_weaken, erule ss)
    apply (clarsimp simp: ss_eq[THEN eq_implD])
   apply (rule simpl_to_graph_weaken, rule ex)
   apply (clarsimp simp: ex_eq[THEN eq_implD])
  apply simp
  done

lemma simpl_to_graph_While_Guard:
  fixes c' F G
  defines "c == c' ;; com.Guard F G com.Skip"
  assumes ps: "GGamma f = Some gf" "nn = NextNode m" "function_graph gf m = Some (Cond l r cond)"
        "eq_impl nn eqs (\<lambda>gst sst. cond gst = (sst \<in> C)) (I \<inter> G)"
  assumes ss: "\<And>k S. \<lbrakk> simpl_to_graph SGamma GGamma f nn (add_cont (com.While C c) con) (Suc (n + k)) (S # tS) G I eqs out_eqs \<rbrakk>
        \<Longrightarrow> simpl_to_graph SGamma GGamma f l (add_cont (c ;; com.While C c) con) (Suc (n + k)) (S # tS) (G \<inter> C) I eqs2 out_eqs"
   and ss_eq: "eq_impl nn eqs eqs2 (I \<inter> G \<inter> C)"
  assumes ex: "simpl_to_graph SGamma GGamma f r (add_cont com.Skip con) (Suc n) tS (G \<inter> (- C)) I eqs3 out_eqs"
   and ex_eq: "eq_impl nn eqs eqs3 (I \<inter> G \<inter> - C)"
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

lemma no_next_step: "\<forall>gst'.
        ((exec_graph_step GGamma) ^^ 0) `` {[(nn, gst', fn)]} \<subseteq> {[(nn, gst', fn)]}
        \<and> 0 < (2 :: nat) \<and> (0 = (0 :: nat) \<or> nn \<notin> {Ret, Err})"
  by simp

lemma basic_next_step: "GGamma fn = Some gf \<Longrightarrow> function_graph gf m = Some (Basic nn' upds)
    \<Longrightarrow> \<forall>gst'.
        ((exec_graph_step GGamma) ^^ 1) `` {[(NextNode m, gst', fn)]} \<subseteq> {[(nn', upd_vars upds gst', fn)]}
        \<and> (1 :: nat) < 2 \<and> ((1 :: nat) = 0 \<or> NextNode m \<notin> {Ret, Err})"
  apply (clarsimp simp del: imp_disjL)
  apply (clarsimp simp: exec_graph_step_def K_def split: graph_function.split_asm)
  done

lemma simpl_to_graph_Basic_next_step:
  assumes next_step: "\<forall>gst'.
        ((exec_graph_step GGamma) ^^ steps) `` {[(nn, gst', fn)]} \<subseteq> {[(nn', f gst', fn)]}
        \<and> steps < 2 \<and> (steps = 0 \<or> nn \<notin> {Ret, Err})"
  shows
  "\<lbrakk> eq_impl nn eqs (\<lambda>gst sst. eqs2 (f gst) (f' sst) \<and> f' sst \<in> I \<and> f' sst \<in> Q) (P \<inter> I);
        simpl_to_graph SGamma GGamma fn nn' (add_cont com.Skip con) (n + min steps 1) tS Q I eqs2 out_eqs \<rbrakk>
    \<Longrightarrow> simpl_to_graph SGamma GGamma fn nn (add_cont (com.Basic f') con) n tS P I eqs out_eqs"
  apply (rule simpl_to_graph_step_general[where j=1 and i=steps, rotated -1])
    apply simp
   apply (simp add: eq_OO)
   apply (rule exI, rule conjI, blast intro: add_cont_step step.intros)
   apply (rule exI, rule conjI, rule next_step[rule_format, THEN conjunct1])
   apply (drule(1) eq_implD, simp+)
  apply (simp add: next_step[simplified])
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
  "eq_impl nn eqs eqs2 (upd_range exn_upd Break \<inter> I)
    \<Longrightarrow> simpl_to_graph SGamma GGamma f nn
        (add_cont com.Skip con) n tS (upd_range exn_upd Break) I eqs2 out_eqs
    \<Longrightarrow> \<forall>f s. exn_var (exn_upd f s) = f (exn_var s)
    \<Longrightarrow> simpl_to_graph SGamma GGamma f nn
        (add_cont (ccatchbrk exn_var) con) n tS (upd_range exn_upd Break) I eqs out_eqs"
  apply (simp add: ccatchbrk_def)
  apply (rule simpl_to_graph_step_R_unchanged)
   apply (simp add: upd_range_def)
   apply (blast intro: add_cont_step step.intros)
  apply (erule simpl_to_graph_weaken, simp add: eq_impl_def)
  done

lemma simpl_to_graph_ccatchbrk_Return:
  "eq_impl nn eqs eqs2 (upd_range exn_upd Return \<inter> I)
    \<Longrightarrow> simpl_to_graph SGamma GGamma f nn
        (add_cont com.Throw con) n tS (upd_range exn_upd Return) I eqs2 out_eqs
    \<Longrightarrow> \<forall>f s. exn_var (exn_upd f s) = f (exn_var s)
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
  "\<lbrakk> nn = NextNode m; GGamma gf = Some gfc; function_graph gfc m = Some (Cond l Err cond);
        eq_impl nn eqs (\<lambda>gst sst. sst \<in> G \<longrightarrow> cond gst) (I \<inter> P);
        simpl_to_graph SGamma GGamma gf l (add_cont c con) (Suc n) Q (G \<inter> P) I eqs2 out_eqs;
        eq_impl nn eqs eqs2 (P \<inter> I \<inter> G) \<rbrakk>
    \<Longrightarrow> simpl_to_graph SGamma GGamma gf nn (add_cont (com.Guard F G c) con) n Q P I eqs out_eqs"
  apply clarsimp
  apply (rule_tac S=G in simpl_to_graph_cases)
   apply (erule_tac nn'=l in simpl_to_graph_step[rotated])
   apply (simp add: exec_graph_step_image_node)
   apply (fastforce dest: eq_implD intro: step.intros add_cont_step)[1]
  apply (rule simpl_to_graph_steps_Fault)
  apply (blast intro: step.GuardFault)
  done

lemma simpl_to_graph_double_Guard:
  "simpl_to_graph SGamma GGamma gf nn (add_cont (com.Guard F' G' c) con) n Q (P \<inter> G) I eqs2 out_eqs
    \<Longrightarrow> eq_impl nn eqs eqs2 (I \<inter> P \<inter> G)
    \<Longrightarrow> simpl_to_graph SGamma GGamma gf nn (add_cont (com.Guard F G (com.Guard F' G' c)) con) n Q P I eqs out_eqs"
  apply (rule_tac S=G in simpl_to_graph_cases)
   apply (rule simpl_to_graph_step_R_unchanged[rotated])
    apply (erule simpl_to_graph_weaken_eq_impl[rotated])
    apply (simp add: Int_ac)
   apply (rule add_cont_step)
   apply (rule step.Guard, simp)
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

lemma simpl_to_graph_done2:
  "simpl_to_graph SGamma GGamma gf Ret (add_cont com.Skip []) n Q P I eqs eqs"
  by (auto intro: simpl_to_graph_done simp: eq_impl_def)

lemma simpl_to_graph_noop:
  "\<lbrakk> GGamma gf = Some gfc; function_graph gfc m = Some (node.Basic nn []);
        simpl_to_graph SGamma GGamma gf nn c n Q P I eqs2 out_eqs;
        eq_impl nn eqs eqs2 (P \<inter> I) \<rbrakk>
    \<Longrightarrow> simpl_to_graph SGamma GGamma gf (NextNode m) c n Q P I eqs out_eqs"
  apply (rule simpl_to_graph_step_general[where i=1 and j=0, rotated])
    apply simp+
  apply (simp add: exec_graph_step_image_node upd_vars_def save_vals_def K_def
                   eq_impl_def)
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
  apply (rule_tac P="\<lambda>st. var_acc ?a st = ?b" and Q="\<lambda>x. x \<in> set ?xs"
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

lemma graph_fun_refines_from_simpl_to_graph:
  "\<lbrakk> SGamma proc = Some com; GGamma fname = Some gf;
    \<And>Q. simpl_to_graph SGamma GGamma fname (NextNode (entry_point gf)) (add_cont com []) 0
        [Q] UNIV I eqs
        (\<lambda>s s'. map (\<lambda>i. var_acc i s) (function_outputs gf) = map (\<lambda>i. i s') outs);
        \<forall>gst sst. map (\<lambda>i. var_acc i gst) (function_inputs gf) = map (\<lambda>i. i sst) ins
            \<longrightarrow> eqs gst sst;
        distinct (function_inputs gf); length ins = length (function_inputs gf);
        length outs = length (function_outputs gf) \<rbrakk>
    \<Longrightarrow> graph_fun_refines SGamma GGamma I ins proc outs fname"
  apply (clarsimp simp: graph_fun_refines_def)
  apply (frule exec_trace_def[THEN eqset_imp_iff, THEN iffD1])
  apply clarsimp
  apply (erule_tac x="UNIV \<times> {[0 \<mapsto> (com, Normal s)]}" in meta_allE)
  apply (drule_tac tr=tr and tr'="[0 \<mapsto> (com, Normal s)]"
          and n'=0 and n''=0 and sst=s in simpl_to_graphD)
   apply (rule conjI, assumption)
   apply (simp add: suffix_tuple_closure_inter_def exec_trace_def)
   apply (rule conjI)
    apply (erule allE, erule allE, erule mp)
    apply (simp add: fetch_returned exec_trace_inputs_def acc_vars_def)
   apply (simp add: add_cont_Nil nat_trace_rel_def)
  apply (clarsimp simp: trace_end_match_def dest!: fun_cong[where x=0])
  apply (subgoal_tac "\<forall>st. trace_end tr'' = Some st
    \<longrightarrow> SGamma \<turnstile> \<langle>com.Call proc,Normal s\<rangle> \<Rightarrow> exec_final_step st")
   apply (elim disjE exE conjE)
     apply (clarsimp simp: exec_final_step_def)
    apply clarsimp
    apply (drule step_preserves_termination[rotated])
     apply (erule step.Call)
    apply (simp add: c_trace_nontermination)
   apply (frule(1) trace_end_Ret_Err)
   apply (clarsimp simp: exec_final_step_def acc_vars_def)
   apply metis
  apply clarsimp
  apply (erule exec.Call)
  apply (simp add: exec_via_trace)
  apply metis
  done

lemma simpl_to_graph_call_noreturn:
  "(\<exists>ft. \<forall>s xs. (SGamma \<turnstile> \<langle>com.Call p, Normal s\<rangle> \<Rightarrow> xs)
            = (xs = Fault ft))
    \<Longrightarrow> simpl_to_graph SGamma GGamma gf nn
        (add_cont (call initf p ret (\<lambda>x y. com.Basic (f x y))) con)
        n Q P I eqs out_eqs"
  apply (clarsimp simp: call_def block_def)
  apply (rule simpl_to_graph_steps_Fault)
  apply clarsimp
  apply (rule exI)
  apply (rule exec_impl_steps_Fault)
  apply (rule exec.DynCom exec.Seq exec.CatchMiss exec.Basic)+
    apply blast
   apply simp
  apply (rule exec.FaultProp)
  done

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
  assumes next_step: "\<forall>gst'.
        ((exec_graph_step GGamma) ^^ steps) `` {[(nn', gst', p)]} \<subseteq> {[(nn'', f gst', p)]}
        \<and> steps < 2 \<and> (steps = 0 \<or> nn' \<notin> {Ret, Err})"
  and rel: "graph_fun_refines SGamma GGamma I inputs proc outputs p'"
  and modifies: "\<forall>\<sigma>. SGamma \<turnstile>\<^bsub>/UNIV\<^esub> {\<sigma>} com.Call proc (Q \<sigma>)"
  and init: "eq_impl nn eqs (\<lambda>gst sst. initf sst \<in> I
            \<and> map (\<lambda>i. i gst) args = map (\<lambda>i. i (initf sst)) inputs) (I \<inter> P)"
  and ret: "eq_impl nn eqs (\<lambda>gst sst. \<forall>sst' vs. map (\<lambda>i. i sst') outputs = vs
                  \<and> sst' \<in> I \<and> sst' \<in> Q (initf sst)
        \<longrightarrow> eqs2 (f (save_vals rets vs gst))
                (f' sst sst' (ret sst sst')) \<and> f' sst sst' (ret sst sst') \<in> I) I"
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
  apply simp
  apply (clarsimp intro!: simpl_to_graphI)
  apply (frule init[THEN eq_implD], simp+)
  apply (cut_tac rel, clarsimp simp: graph_fun_refines_def)
  apply (frule exec_trace_drop_n, (rule graph | assumption)+)
  apply (drule(1) bspec)
  apply (drule_tac x="initf sst" in spec)
  apply (clarsimp simp: exec_trace_inputs_def graph)
  apply (subst(asm) trace_drop_n_init, (assumption | rule graph)+)
  apply (clarsimp simp: init_vars_def fetch_returned len)
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
  apply (frule(1) exec_graph_trace_must_take_steps[OF
      _ _ next_step[rule_format, THEN conjunct1]])
   apply (simp only: next_step, simp)
  apply (cut_tac tr=tr and tr'=trace'
      and sst="f' ?a ?b ?c" in simpl_to_graphD[OF cont])
   apply (rule conjI, assumption)
   apply simp
   apply (drule ret[THEN eq_implD], simp)
   apply (simp only: conj_assoc[symmetric], rule conjI[rotated], assumption)
   apply (simp add: return_vars_def conj_ac)
   apply (frule cvalidD[OF hoare_sound, OF modifies[THEN spec], rotated],
     simp, clarsimp, simp)
   apply clarsimp
   apply auto[1]
  apply (metis restrict_map_eq_mono[OF le_add1])
  done

lemmas simpl_to_graph_call_triv
    = simpl_to_graph_call_next_step[where f'="\<lambda>x y s. s", OF _ _ _ no_next_step]

lemmas simpl_to_graph_call
    = simpl_to_graph_call_next_step[OF _ _ _ basic_next_step]

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

lemma c_guard_ptr_val_gt_0:
  "c_guard (p :: ('a :: mem_type) ptr) \<Longrightarrow> ptr_val p > 0"
  apply (simp only: word_neq_0_conv[symmetric], rule notI)
  apply (cases p, simp add: c_guard_NULL_simp)
  done

lemma h_val_ptr:
  "h_val hp (p :: ('a :: c_type) ptr ptr) = Ptr (load_word32 (ptr_val p) hp)"
  by (simp add: h_val_def load_word32_def from_bytes_def typ_info_ptr)

lemma heap_update_ptr:
  "heap_update (p :: ('a :: c_type) ptr ptr) p' hp = store_word32 (ptr_val p) (ptr_val p') hp"
  by (simp add: heap_update_def to_bytes_def typ_info_ptr store_word32_def)

lemma h_val_word32:
  "h_val hp p = load_word32 (ptr_val p) hp"
  by (simp add: h_val_def load_word32_def from_bytes_def typ_info_word)

lemma heap_update_word32:
  "heap_update p w hp = store_word32 (ptr_val p) w hp"
  by (simp add: heap_update_def to_bytes_def typ_info_word store_word32_def)

lemma heap_list_update_word32:
  "heap_update_list addr (to_bytes w (heap_list hp' 4 addr')) hp
    = store_word32 addr w hp"
  by (simp add: to_bytes_def store_word32_def typ_info_word)

lemma heap_list_update_ptr:
  "heap_update_list addr (to_bytes p (heap_list hp' 4 addr')) hp
    = store_word32 addr (ptr_val (p :: ('a :: c_type) ptr)) hp"
  by (simp add: to_bytes_def store_word32_def typ_info_ptr)

lemma field_lvalue_offset_eq:
  "field_lookup (typ_info_t TYPE('a :: c_type)) f 0 = Some v
        \<Longrightarrow> field_lvalue (ptr :: 'a ptr) f = ptr_val ptr + of_nat (snd v)"
  apply (cases v, simp, drule field_lookup_offset_eq)
  apply (simp add: field_lvalue_def)
  done

lemma image_fst_cart_UNIV_subset:
  "S \<subseteq> (fst ` S) \<times> UNIV"
  by (auto elim: image_eqI[rotated])

lemma simpl_to_graph_known_extra_check:
  "\<lbrakk> nn = NextNode m; GGamma fname = Some gf;
      function_graph gf m = Some (node.Cond l Err Check);
      \<And>s. Check s \<longrightarrow> True;
      eq_impl nn eqs (\<lambda>gst sst. Check gst) (P \<inter> I);
      eq_impl nn eqs eqs2 (P \<inter> I);
      simpl_to_graph SGamma GGamma fname l com n traces P I eqs2 out_eqs \<rbrakk>
    \<Longrightarrow> simpl_to_graph SGamma GGamma fname nn com n traces P I eqs out_eqs"
  apply (rule_tac i=1 and j=0 in simpl_to_graph_step_general[rotated -1])
    apply simp
   apply (simp add: exec_graph_step_image_node)
   apply (auto dest: eq_implD)
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
  apply (simp split del: split_if)
  apply (subst foldl_cong[OF refl refl])
   apply (clarsimp simp: nth_append)
   apply (rule refl)
  apply (simp add: nth_append split del: split_if cong: if_cong)
  apply (auto simp: unat_of_nat addr_card linorder_not_less less_Suc_eq
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

lemma intvl_empty2:
  "({p ..+ n} = {}) = (n = 0)"
  by (auto simp add: intvl_def)

lemma heap_list_update_commute:
  "{p ..+ length xs} \<inter> {q ..+ length ys} = {}
      \<Longrightarrow> heap_update_list p xs (heap_update_list q ys hp)
        = heap_update_list q ys (heap_update_list p xs hp)"
  apply (cases "length xs \<le> addr_card")
   apply (cases "length ys \<le> addr_card")
    apply (simp add: heap_update_list_If2)
    apply (rule ext, simp)
    apply blast
   apply (simp_all add: addr_card intvl_overflow intvl_empty2)
  done

lemma is_aligned_intvl_disjoint:
  "\<lbrakk> p \<noteq> p'; is_aligned p n; is_aligned p' n \<rbrakk>
    \<Longrightarrow> {p ..+ 2 ^ n} \<inter> {p' ..+ 2 ^ n} = {}"
  apply (drule(2) aligned_neq_into_no_overlap)
  apply (drule upto_intvl_eq)+
  apply (simp add: field_simps del: Int_atLeastAtMost)
  done

lemma store_store_word32_commute:
  "\<lbrakk> p \<noteq> p'; is_aligned p 2; is_aligned p' 2 \<rbrakk>
    \<Longrightarrow> store_word32 p w (store_word32 p' w' hp)
      = store_word32 p' w' (store_word32 p w hp)"
  apply (clarsimp simp: store_word32_def)
  apply (rule heap_list_update_commute)
  apply (drule(2) is_aligned_intvl_disjoint)
  apply (simp add: length_word_rsplit_even_size[OF refl] word_size
              del: Int_atLeastAtMost)
  done

lemma store_store_word32_commute_offset:
  assumes prems: "(p - p') = n" "n && 3 = 0" "n \<noteq> 0"
  shows "store_word32 p w (store_word32 p' w' hp)
      = store_word32 p' w' (store_word32 p w hp)"
  using prems
  apply (clarsimp simp: store_word32_def)
  apply (rule heap_list_update_commute)
  apply (rule intvl_disj_offset[where x="- p'", THEN iffD1])
  apply (simp add: length_word_rsplit_even_size[OF refl] word_size
              del: Int_atLeastAtMost)
  apply (rule is_aligned_intvl_disjoint[where n=2, simplified])
    apply (simp add: field_simps word_neq_0_conv[symmetric] del: word_neq_0_conv)
   apply (simp add: field_simps is_aligned_mask mask_def)
  apply simp
  done

lemma c_guard_to_word_ineq:
  "c_guard (p :: ('a :: mem_type) ptr)
     = (ptr_val p && mask (align_td (typ_info_t TYPE('a))) = 0
        \<and> ptr_val p \<noteq> 0 \<and> ptr_val p \<le> (- of_nat (size_of TYPE('a))))"
  using max_size[where 'a='a]
  apply (simp add: c_guard_def ptr_aligned_def align_of_def
                   is_aligned_def[symmetric] is_aligned_mask
                   c_null_guard_def intvl_def addr_card_def
                   card_word)
  apply safe
    apply (drule_tac x=0 in spec, simp)
   apply (rule ccontr)
   apply (drule_tac x="unat (- ptr_val p)" in spec)
   apply simp
   apply (simp add: Aligned.unat_minus word_le_nat_alt
             split: split_if_asm)
    apply (drule of_nat_inverse, simp+)
    apply (cut_tac 'a='a in sz_nzero, simp)
   apply (simp add: word_size unat_of_nat linorder_not_le
                    linorder_not_less)
   apply (cut_tac x="ptr_val p" in unat_lt2p, simp)
  apply (simp add: word_neq_0_conv[symmetric] del: word_neq_0_conv)
  apply (subgoal_tac "ptr_val p = (- (of_nat k))")
   apply simp
   apply (simp add: word_le_nat_alt Aligned.unat_minus split: split_if_asm)
    apply (drule of_nat_inverse, simp+)
    apply (cut_tac 'a='a in sz_nzero, simp)
   apply (simp add: word_size unat_of_nat)
  apply (simp add: sign_simps[symmetric])
  done

lemma word_sless_to_less:
  "\<lbrakk> 0 <=s x; 0 <=s y \<rbrakk> \<Longrightarrow> (x <s y) = (x < y)"
  apply (simp add: word_sless_alt word_sle_def word_less_def)
  apply (simp add: sint_eq_uint word_msb_sint)
  done

lemma unat_ucast_less_helper:
  "ucast x < (of_nat n :: word32) \<Longrightarrow> unat (x :: word8) < n"
  apply (drule unat_less_helper)
  apply (simp add: unat_ucast_8_32)
  done

lemma store_load_word32:
  "store_word32 p (load_word32 p m) m = m"
  apply (simp add: store_word32_def load_word32_def)
  apply (rule heap_update_list_id[where n=4])
  apply (simp add: word_rsplit_rcat_size word_size)
  done

lemma word32_lt_bounds_reduce:
  "\<lbrakk> n \<noteq> 0; (i \<noteq> (n - 1)) \<rbrakk> \<Longrightarrow> (i < (n :: word32)) = (i < (n - 1))"
  apply (rule sym, rule trans, rule less_le)
  apply simp
  apply (simp add: word_le_def word_less_def uint_sub_if')
  done

lemma length_Cons: "length (x # xs) = Suc (length xs)"
  by simp

ML {*

structure UseHints = struct

fun parse_compile_hints fname = let
    val f = TextIO.openIn fname
    val parse_int = ParseGraph.parse_int
    fun get () = case TextIO.inputLine f
      of NONE => []
      | SOME s => unsuffix "\n" s :: get ()
    fun group hs (["Hints", s] :: sss)
      = (s, hs) :: group [] sss
      | group hs (ss :: sss) = group (ss :: hs) sss
      | group _ [] = []
    val groups = group [] (rev (map (Library.space_explode " ") (get ())))
    fun proc_var_deps [] = []
      | proc_var_deps (nm :: ss) = let
        val (typ, ss) = ParseGraph.parse_typ ss
      in ((nm, typ) :: proc_var_deps ss) end
    fun proc ("VarDeps" :: n :: ss)
      = ((parse_int n, proc_var_deps ss))
      | proc ss = error (String.concat ("parse_compile_hints: " :: ss))
    fun proc_group hs = let
        val vds = map proc hs
      in Inttab.make vds end
  in Symtab.make (map (apsnd proc_group) groups) end

fun mk_ptr_val_app p =
    Const (@{const_name ptr_val}, fastype_of p --> @{typ word32}) $ p

val globals_swap = ref (fn (x : term) => x)

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
    val globals_sst = Syntax.read_term ctxt "globals :: globals myvars \<Rightarrow> _"
        $ sst
    val _ = type_of globals_sst (* does type checkig *)

    val t_hrs = Syntax.read_term ctxt "t_hrs_' :: globals \<Rightarrow> _"
    val pms = Syntax.read_term ctxt "phantom_machine_state_' :: globals \<Rightarrow> _"
    val pms_encode = Syntax.read_term ctxt "encode_machine_state"
    fun do_pms_encode t = case pms_encode of Const _ => pms_encode $ t
      | _ => raise TERM ("mk_simpl_acc: requires `encode_machine_state :: machine_state => unit \<times> nat'", [t])

    fun mk_sst_acc "Mem" = @{term hrs_mem} $ (t_hrs $ ((! globals_swap) globals_sst))
      | mk_sst_acc "HTD" = @{term hrs_htd} $ (t_hrs $ globals_sst)
      | mk_sst_acc "PMS" = do_pms_encode (pms $ globals_sst)
      | mk_sst_acc nm = if String.isPrefix "rv#space#" nm
              then mk_sst_acc (unprefix "rv#space#" nm)
              else if String.isSuffix "_'" nm
              then Syntax.read_term ctxt (nm ^ " :: globals myvars => _") $ sst
              else let
                  val (head, tail) = Library.space_explode "." nm
                      |> Library.split_last |> apfst (Library.space_implode ".")
                  val acc = mk_sst_acc head
                  val typ_nm = fastype_of acc |> dest_Type |> fst
                  val acc2 = if typ_nm = "Arrays.array"
                    then mk_arr_idx acc (HOLogic.mk_number @{typ nat}
                        (ParseGraph.parse_int tail))
                    else Proof_Context.read_const_proper
                        ctxt true (typ_nm ^ "." ^ tail) $ acc
                in acc2 end
    fun mk_sst_acc2 nm = let
        val acc = mk_sst_acc nm
        val T = fastype_of acc |> dest_Type |> fst
      in if T = @{type_name ptr} then mk_ptr_val_app acc else acc end
  in Term.lambda sst (ParseGraph.mk_var_typ (mk_sst_acc2 nm)) end

fun foldr1_default _ v [] = v
  | foldr1_default f _ xs = foldr1 f xs

fun mk_graph_eqs Gamma deps nm n = let
    val vs = case (Inttab.lookup deps n) of
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
    tps, [cprem_of t i |> term_of] @ ts)

val standard_GG = @{term "GG :: string \<Rightarrow> graph_function option"}

fun graph_gamma_tac ctxt = SUBGOAL (fn (t, i) => let
    val (lhs, _) = HOLogic.dest_Trueprop (Logic.strip_assums_concl
        (Envir.beta_eta_contract t)) |> HOLogic.dest_eq
    val thy = Proof_Context.theory_of ctxt
    val _ = (head_of lhs = standard_GG andalso length (snd (strip_comb lhs)) = 1)
      orelse raise TERM ("GG lhs", [])
    val nm = the_single (snd (strip_comb lhs)) |> HOLogic.dest_string
        |> Long_Name.base_name
    val gfun = Syntax.read_term ctxt (nm ^ "_graph_fun")
    val gfun_def = Proof_Context.get_thm ctxt (nm ^ "_graph_fun_def")
    val _ = dest_Const (head_of gfun)
    val GG_assum = HOLogic.mk_eq
            (lhs, @{term "Some :: graph_function \<Rightarrow> _"} $ gfun)
        |> HOLogic.mk_Trueprop |> cterm_of thy |> Thm.assume
        |> simplify (put_simpset HOL_basic_ss ctxt addsimps [gfun_def])
  in rtac GG_assum i end
    handle TERM (s, ts) => raise TERM ("graph_gamma_tac: " ^ s, t :: ts))

fun inst_graph_node_tac ctxt =
  simp_tac (put_simpset HOL_basic_ss ctxt addsimps @{thms function_graph.simps})
  THEN' SUBGOAL (fn (t, i) => case
    HOLogic.dest_Trueprop (Logic.strip_assums_concl
        (Envir.beta_eta_contract t))
  of @{term "op = :: node option \<Rightarrow> _"} $ (f $ n) $ _ => (let
    val g = head_of f |> dest_Const |> fst
    val n = dest_nat n
    val thm = Proof_Context.get_thm ctxt
        (Long_Name.base_name g ^ "_" ^ Int.toString n)
  in rtac thm i end handle TERM (s, ts) => raise TERM ("inst_graph_node_tac: " ^ s, t :: ts))
  | t => raise TERM ("inst_graph_node_tac", [t]))

fun inst_graph_tac ctxt = graph_gamma_tac ctxt THEN' inst_graph_node_tac ctxt

fun mk_graph_refines (funs : ParseGraph.funs) ctxt s = let
    val proc = Syntax.read_term ctxt
        (Long_Name.base_name s ^ "_'proc")
    val gamma = Syntax.read_term ctxt "\<Gamma>"
    val invs = Syntax.read_term ctxt "simpl_invariant"
    val _ = case invs of Const _ => ()
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

fun apply_graph_refines_ex_tac funs ctxt = SUBGOAL (fn (t, i) => case
    (Logic.strip_assums_concl (Envir.beta_eta_contract t)) of
    @{term Trueprop} $ (Const (@{const_name graph_fun_refines}, _)
        $ _ $ _ $ _ $ _ $ _ $ _ $ s)
        => (rtac (Thm.assume (cterm_of (Proof_Context.theory_of ctxt)
            (mk_graph_refines funs ctxt (HOLogic.dest_string s)))) i)
        | _ => raise TERM ("apply_graph_refines_ex_tac", [t]))

fun apply_impl_thm ctxt = SUBGOAL (fn (t, i) => case
        Logic.strip_assums_concl (Envir.beta_eta_contract t)
    of @{term Trueprop} $ (Const (@{const_name HOL.eq}, _)
        $ (_ $ Const (s, _)) $ (Const (@{const_name Some}, _) $ _))
    => rtac (Proof_Context.get_thm ctxt
        (suffix "_impl" (unsuffix "_'proc" (Long_Name.base_name s)))) i
  | _ => no_tac)

fun get_Call_args (Const (@{const_name com.Call}, _) $ x) = [x]
  | get_Call_args (f $ x) = get_Call_args f @ get_Call_args x
  | get_Call_args (Abs (_, _, t)) = get_Call_args t
  | get_Call_args _ = []

fun apply_modifies_thm ctxt = SUBGOAL (fn (t, i) => case
        get_Call_args (Envir.beta_eta_contract t)
    of [Const (s, _)] => let
        val s = unsuffix "_'proc" (Long_Name.base_name s)
        val thm = Proof_Context.get_thm ctxt (s ^ "_modifies")
      in rtac thm i end
    | _ => no_tac)

fun is_safe_eq_impl (p as (@{term Trueprop}
        $ (Const (@{const_name "eq_impl"}, _) $ _ $ _ $ _ $ _)))
    = not (exists_subterm (fn Var _ => true | Free ("n", _) => true
                        | _ => false) p)
  | is_safe_eq_impl _ = false

fun eq_impl_assume_tac ctxt = DETERM o SUBGOAL (fn (t, i) => let
    val p = Logic.strip_assums_concl (Envir.beta_eta_contract t)
  in if is_safe_eq_impl p
    then rtac (Thm.assume (cterm_of (Proof_Context.theory_of ctxt) p)) i
    else no_tac
  end)

fun is_pglobal_valid_conjs (Const (@{const_name conj}, _) $ p $ q)
    = is_pglobal_valid_conjs p andalso is_pglobal_valid_conjs q
  | is_pglobal_valid_conjs (Const (@{const_name "pglobal_valid"}, _) $ _ $ _ $ _)
    = true
  | is_pglobal_valid_conjs _ = false

fun check_is_pglobal_valid ctxt = SUBGOAL (fn (t, i) =>
    (if is_pglobal_valid_conjs (Logic.strip_assums_concl (Envir.beta_eta_contract t)
        |> HOLogic.dest_Trueprop |> HOLogic.dest_imp |> fst)
    then simp_tac (put_simpset HOL_ss ctxt) i else no_tac)
        )

fun simpl_ss ctxt = put_simpset HOL_basic_ss ctxt
    addsimps @{thms switch.simps fst_conv snd_conv
        length_Cons singletonI triv_forall_equality
        simpl_to_graph_Seq simpl_to_graph_Catch
}

val immediates = @{thms
    simpl_to_graph_Skip_immediate simpl_to_graph_Throw_immediate}

fun apply_simpl_to_graph_tac funs noreturns ctxt nm =
        simp_tac (simpl_ss ctxt
            addsimps @{thms One_nat_def whileAnno_def
                creturn_def[folded creturn_void_def]})
    THEN' DETERM o (FIRST' [
        rtac @{thm simpl_to_graph_Basic_triv},
        resolve_tac @{thms simpl_to_graph_lvar_nondet_init
            simpl_to_graph_Skip
            simpl_to_graph_Throw
            simpl_to_graph_cbreak
            simpl_to_graph_creturn_void
            simpl_to_graph_ccatchbrk_Break
            simpl_to_graph_ccatchbrk_Return},
        rtac @{thm simpl_to_graph_known_extra_check[OF refl]}
            THEN' inst_graph_tac ctxt
            THEN' check_is_pglobal_valid ctxt,
        rtac @{thm simpl_to_graph_double_Guard},
        rtac @{thm simpl_to_graph_Guard[OF refl]}
            THEN' inst_graph_tac ctxt,
        rtac @{thm simpl_to_graph_Cond[OF refl]}
            THEN' inst_graph_tac ctxt,
        rtac @{thm simpl_to_graph_Basic}
            THEN' inst_graph_tac ctxt,
        rtac @{thm simpl_to_graph_call_noreturn}
            THEN' resolve_tac noreturns,
        rtac @{thm simpl_to_graph_call_triv[OF refl]}
            THEN' inst_graph_tac ctxt
            THEN' apply_graph_refines_ex_tac funs ctxt
            THEN' apply_modifies_thm ctxt,
        rtac @{thm simpl_to_graph_call[OF refl]}
            THEN' inst_graph_tac ctxt
            THEN' inst_graph_tac ctxt
            THEN' apply_graph_refines_ex_tac funs ctxt
            THEN' apply_modifies_thm ctxt,
        rtac @{thm simpl_to_graph_nearly_done}
            THEN' inst_graph_tac ctxt
    ] THEN_ALL_NEW (TRY o REPEAT_ALL_NEW
        (resolve_tac immediates)))

fun trace_cache _ (SOME thm) = tracing
  ("Adding thm to cache with " ^ string_of_int (nprems_of thm) ^ " prems.")
  | trace_cache _ NONE = tracing "Adding NONE to cache."

fun simpl_to_graph_cache_tac funs noreturns hints cache nm ctxt =
        simp_tac (simpl_ss ctxt)
    THEN_ALL_NEW DETERM o FIRST' [
        SUBGOAL (fn (t, i) => (case
        with_cache cache (mk_simpl_to_graph_thm funs noreturns hints cache nm ctxt) (K (K ()))
            (simpl_to_graph_skel hints nm (HOLogic.dest_Trueprop
                (Logic.strip_assums_concl (Envir.beta_eta_contract t)))) of
            SOME thm => rtac thm i | _ => no_tac)
            handle TERM _ => no_tac),
        rtac @{thm simpl_to_graph_done2},
        eq_impl_assume_tac ctxt
    ]

and mk_simpl_to_graph_thm funs noreturns hints cache nm ctxt tm = let
    val thy = Proof_Context.theory_of ctxt
    val ct = cterm_of thy (HOLogic.mk_Trueprop tm)
  in Thm.trivial ct
    |> (apply_simpl_to_graph_tac funs noreturns ctxt nm
        THEN_ALL_NEW (TRY o simpl_to_graph_cache_tac funs noreturns hints cache nm ctxt)
        THEN_ALL_NEW (TRY o eq_impl_assume_tac ctxt)) 1
    |> Seq.hd
    |> Drule.generalize ([], ["n", "trS"])
    |> SOME
  end handle TERM (s, _) => (tracing ("mk_simpl_to_graph_thm: " ^ s); NONE)
    | Empty => (tracing "mk_simpl_to_graph_thm: raised Empty on:";
          tracing (Syntax.pretty_term ctxt tm |> Pretty.string_of);
          NONE)
    | Option => NONE

fun get_while (Const (@{const_name simpl_to_graph}, _)
                $ _ $ _ $ _ $ _
                $ (Const (@{const_name add_cont}, _) $ (Const (@{const_name While}, _) $ C $ c) $ _)
                $ _ $ _ $ _ $ _ $ _ $ _)
    = (C, c)
  | get_while t = raise TERM ("get_while", [t])

fun check_while_assums t = let
    val hyps = Logic.strip_assums_hyp t
        |> filter (fn (@{term Trueprop} $ (@{term "All :: (nat => _) => _"} $ _))
                => true | _ => false)
  in length hyps < 2 orelse raise TERM ("check_while_assums: too many", []);
    () end

fun simpl_to_graph_While_tac hints nm ctxt =
    simp_tac (simpl_ss ctxt)
  THEN' SUBGOAL (fn (t, i) => let
    val t = HOLogic.dest_Trueprop (Logic.strip_assums_concl
        (Envir.beta_eta_contract t))
    val _ = get_while t
    val skel = simpl_to_graph_skel hints nm t
    val thy = Proof_Context.theory_of ctxt
    val ct = cterm_of thy (HOLogic.mk_Trueprop skel)
  in
    rtac (Thm.trivial ct |> Drule.generalize ([], ["n"])) i
        THEN resolve_tac @{thms simpl_to_graph_While_Guard[OF refl]
                simpl_to_graph_While_UNIV[OF refl]} i
        THEN inst_graph_tac ctxt i
  end handle TERM _ => no_tac)

fun trace_fail_tac ctxt = SUBGOAL (fn (t, i) =>
  (Syntax.pretty_term ctxt t |> Pretty.string_of
    |> prefix "Tactic failed on: " |> tracing;
    no_tac))

fun trace_fail_tac2 ctxt = K no_tac

fun simpl_to_graph_tac funs noreturns hints nm ctxt = let
    val cache = ref (Termtab.empty)
  in REPEAT_ALL_NEW (DETERM o (full_simp_tac (simpl_ss ctxt) THEN'
    SUBGOAL (fn (t, i) => fn thm =>
      ((simpl_to_graph_cache_tac funs noreturns hints cache nm ctxt
    ORELSE' etac @{thm use_simpl_to_graph_While_assum}
    ORELSE' simpl_to_graph_While_tac hints nm ctxt
    ORELSE' trace_fail_tac ctxt) i thm
        handle Empty => (tracing "simpl_to_graph_tac: raised Empty on:";
          tracing (Syntax.pretty_term ctxt t |> Pretty.string_of);
          Seq.empty)))
    ))
  end

fun dest_next_node (@{term NextNode} $ n)
    = dest_nat n
  | dest_next_node @{term Ret} = ~1
  | dest_next_node @{term Err} = ~2
  | dest_next_node t = raise TERM ("dest_next_node", [t])

fun get_conts (@{term node.Basic} $ nn $ _) = [nn]
  | get_conts (@{term node.Cond} $ l $ r $ _) = [l, r]
  | get_conts (@{term node.Call} $ nn $ _ $ _ $ _) = [nn]
  | get_conts n = raise TERM ("get_conts", [n])

fun get_rvals (Abs (_, _, t)) = let
    fun inner (Const _ $ (s as (@{term "op # :: char \<Rightarrow> _"} $ _ $ _)) $ Bound 0)
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
        val cont_vars = maps (Inttab.lookup_list tab) conts
          |> Ord_List.make string_ord
        val vars = Ord_List.merge string_ord (rvs,
            Ord_List.subtract string_ord lvs cont_vars)
        val prev_vars = Inttab.lookup_list tab point
        val tab = Inttab.update (point, vars) tab
        val upds = if prev_vars <> vars
            then Inttab.lookup_list preds point else []
      in backward tab (upds @ points) end
      | backward tab [] = tab
    val deps = backward (Inttab.make [(~1, outputs), (~2, [])])
      (maps (Inttab.lookup_list preds) [~1, ~2])
  in (preds, deps) end

fun mk_var_deps_hints (funs : ParseGraph.funs) ctxt sT nm = case Symtab.lookup funs nm of
    NONE => raise TERM ("mk_var_deps_hints: miss " ^ nm, [])
  | SOME (_, _, NONE) => Inttab.empty
  | SOME (_, outputs, SOME (ep, nodes, _)) => let
  in snd (get_var_deps (Inttab.make nodes) ep outputs)
    |> Inttab.map (fn _ => map (fn s => (s, mk_simpl_acc ctxt sT s))) end

end

*}

ML {*
fun define_graph_fun_short funs s
    = ParseGraph.define_graph_fun funs (Long_Name.base_name s ^ "_graph")
        (Binding.name (Long_Name.base_name s ^ "_graph_fun")) s
        #> Local_Theory.restore
*}

ML {*
open UseHints

fun enum_simps ctxt = let
    val csenv = CalculateState.get_csenv
        (Proof_Context.theory_of ctxt) "c/kernel_all.c_pp" |> the
    val Absyn.CE ecenv = ProgramAnalysis.cse2ecenv csenv;
  in
    #enumenv ecenv |> Symtab.dest
       |> map (Proof_Context.get_thm ctxt o suffix "_def" o fst)
  end

(*
val global_data_mems = @{thms kernel_all_global_addresses.global_data_mems[
       unfolded global_data_defs]}

val const_global_simps = global_data_mems
    RL [@{thm const_globals_in_memory_h_val_swap}]

val pglobal_valids = (global_data_mems RL
    @{thms ptr_inverse_safe_htd_safe_global_data[OF globals_list_distinct]
            ptr_inverse_safe_htd_safe_const_global_data[OF globals_list_distinct]})
  |> map (full_simplify (HOL_basic_ss addsimps @{thms symbols_in_table_simps
                    pglobal_valid_fold c_guard_to_word_ineq}))
  |> map (full_simplify (@{simpset} addsimps @{thms align_td_array' mask_def}))

val globals_swap_rewrites2
    = @{thms globals_list_distinct} RL globals_swap_rewrites
*)

val thin_While_assums_rule =
    @{thm thin_rl[where V="simpl_to_graph SG GG f nn (add_cont (com.While C c) con) n tS P I e e2"]}
        |> Drule.generalize ([], ["SG", "GG", "f", "nn", "C", "c", "con", "n", "tS", "P", "I", "e", "e2"])

fun init_graph_refines_proof funs nm ctxt = let
    val thy = Proof_Context.theory_of ctxt
    val body_thm = Proof_Context.get_thm ctxt
            (Long_Name.base_name nm ^ "_body_def")
    val ct = mk_graph_refines funs ctxt nm |> cterm_of thy
  in Thm.trivial ct
    |> (rtac @{thm graph_fun_refines_from_simpl_to_graph} 1
        THEN apply_impl_thm ctxt 1
        THEN graph_gamma_tac ctxt 1
        THEN ALLGOALS (simp_tac (put_simpset HOL_basic_ss ctxt addsimps [body_thm]
            addsimps @{thms entry_point.simps function_inputs.simps
                            function_outputs.simps map.simps list.simps}))
        THEN TRY ((rtac @{thm simpl_to_graph_noop_same_eqs}
            THEN' inst_graph_tac ctxt) 1)
    )
    |> Seq.hd
  end

fun eq_impl_unassume_tac t = let
    val hyps = t |> Thm.crep_thm |> #hyps
        |> filter (term_of #> is_safe_eq_impl)
  in (* tracing ("Restoring " ^ string_of_int (length hyps) ^ " hyps.") ; *)
    fold Thm.implies_intr hyps t |> Seq.single end

fun full_simpl_to_graph_tac funs noreturns hints nm ctxt =
    UseHints.simpl_to_graph_tac funs noreturns hints nm ctxt 1
    THEN ALLGOALS (TRY o REPEAT_ALL_NEW (etac thin_While_assums_rule))
    THEN eq_impl_unassume_tac

fun safe_goal_tac ctxt =
  REPEAT_ALL_NEW (DETERM o CHANGED o safe_steps_tac ctxt)

fun graph_refine_proof_tacs ctxt = [
        asm_simp_tac ((put_simpset HOL_basic_ss ctxt) addsimps @{thms
              signed_arith_ineq_checks_to_eq_word32
              signed_arith_eq_checks_to_ord
              signed_mult_eq_checks32_to_64}),
        asm_simp_tac (ctxt addsimps @{thms eq_impl_def
                       var_word32_def var_word8_def var_mem_def
                       var_htd_def var_acc_var_upd
                       pvalid_def var_ms_def init_vars_def
                       return_vars_def upd_vars_def save_vals_def
                       mem_upd_def mem_acc_def hrs_mem_update}),
(*        simp_tac ((put_simpset HOL_basic_ss ctxt) addsimps @{thms forall_swap_madness}), *)
(*        simp_tac (ctxt addsimps @{thms
                       globals_update_globals_swap_twice globals_swap_twice
                       hrs_htd_globals_swap mex_def meq_def}), *)
        TRY o safe_goal_tac ctxt,
        asm_full_simp_tac (ctxt addsimps @{thms
(*                       h_t_valid_disjoint_globals_swap 
                       ptr_safe_disjoint_globals_swap 
                       h_t_valid_field hrs_mem_update 
                       disjoint_h_val_globals_swap[OF global_acc_valid _ image_fst_cart_UNIV_subset]
                       disjoint_heap_update_globals_swap[OF global_acc_valid _ image_fst_cart_UNIV_subset]
                       globals_swap_hrs_htd_update[OF global_acc_valid globals_list_valid]
                       all_htd_updates_def globals_swap_ghost_state
                       globals_update_globals_swap_twice
                       globals_swap_twice hrs_htd_globals_swap hrs_htd_update
                       inj_eq[OF bij_is_inj[OF globals_swap_bij]]
*)
                       unat_less_helper word32_lt_bounds_reduce
                       palign_valid_def pweak_valid_def}
         (*       addsimps globals_swap_rewrites2
                addsimps const_global_simps
                addsimps pglobal_valids *) ),
(*        TRY o REPEAT_ALL_NEW
            (etac @{thm const_globals_in_memory_heap_update_subset[rotated]}
                ORELSE' (rtac @{thm const_globals_in_memory_heap_update[
                       OF _ globals_list_distinct, rotated -1]}
                    THEN' atac)
                ORELSE' (resolve_tac @{thms h_t_valid_field[rotated] ptr_safe_field[rotated]}
                    THEN' simp_tac @{simpset})),
*)
        asm_full_simp_tac (ctxt addsimps @{thms
                       mem_upd_def hrs_mem_update heap_update_ptr
                       heap_update_word32 h_val_ptr h_val_word32
                       field_lvalue_offset_eq NULL_ptr_val
                       (* field_h_val_rewrites *) heap_access_Array_element
                       heap_update_Array_element'[OF refl]
                       scast_id ucast_id word32_sint_1
                       unat_less_helper word_of_int_hom_syms
                       unat_ucast_less_helper ucast_nat_def
                       word_sless_to_less word_sle_def[THEN iffD2]
                       word32_lt_bounds_reduce
                       CTypesDefs.ptr_add_def ptr_val_inj[symmetric]
                       (* heap_update_words_of_upd_eq  words_of_simps *)
                       store_store_word32_commute_offset
                       store_load_word32
                       h_t_valid_ptr_safe typ_uinfo_t_def
                       (* symbols_in_table_simps *)
                       fupdate_def
                    }
                addsimps (enum_simps ctxt)
                addsimprocs [Word_Bitwise_Tac.expand_upt_simproc]
                delsimps @{thms ptr_val_inj}),
         asm_full_simp_tac (put_simpset HOL_ss ctxt addsimps @{thms word_neq_0_conv[symmetric]}),
         asm_full_simp_tac (ctxt addsimps @{thms
                        typ_uinfo_t_def c_guard_to_word_ineq bvshl_def
                        bvlshr_def bvashr_def bv_clz_def scast_def mask_def
                        word_sle_def[THEN iffD2] word_sless_alt[THEN iffD2]
                        store_load_word32
                    })
]

fun mk_graph_refines_proof funs noreturns hints s ctxt
    = init_graph_refines_proof funs s ctxt
        |> full_simpl_to_graph_tac funs noreturns hints s ctxt
        |> Seq.hd
        |> EVERY (map ALLGOALS (graph_refine_proof_tacs ctxt))
        |> Seq.hd
*}

end

