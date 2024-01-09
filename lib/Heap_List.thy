(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Singly-linked lists on heaps or projections from heaps, as predicate and as recursive function.
   Loosely after ~~/src/HOL/Hoare/Pointer_Examples.thy *)

theory Heap_List
imports Main "HOL-Library.Prefix_Order" ListLibLemmas
begin

(* Given a heap projection that returns the next-pointer for an object at address x,
   given a start pointer x, and an end pointer y, determine if the given list
   is the path of addresses visited when following the next-pointers from x to y *)
primrec heap_path :: "('a \<rightharpoonup> 'a) \<Rightarrow> 'a option \<Rightarrow> 'a list \<Rightarrow> 'a option \<Rightarrow> bool" where
  "heap_path hp x [] y     = (x = y)"
| "heap_path hp x (a#as) y = (x = Some a \<and> heap_path hp (hp a) as y)"

(* When a path ends in None, it is a singly-linked list *)
abbreviation heap_ls :: "('a \<rightharpoonup> 'a) \<Rightarrow> 'a option \<Rightarrow> 'a list \<Rightarrow> bool" where
  "heap_ls hp x xs \<equiv> heap_path hp x xs None"

(* Walk a linked list of next pointers, recording which it visited.
   Terminates artificially at loops, and otherwise because the address domain is finite *)
function heap_walk :: "('a::finite \<rightharpoonup> 'a) \<Rightarrow> 'a option \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "heap_walk hp None xs = xs"
| "heap_walk hp (Some x) xs = (if x \<in> set xs then xs else heap_walk hp (hp x) (xs@[x]))"
  by pat_completeness auto

lemma card_set_UNIV:
  fixes xs :: "'a::finite list"
  assumes "x \<notin> set xs"
  shows "card (set xs) < card(UNIV::'a set)"
proof -
  have "finite (UNIV::'a set)" by simp
  moreover
  from assms have "set xs \<subset> UNIV" by blast
  ultimately
  show ?thesis by (rule psubset_card_mono)
qed

termination heap_walk
  by (relation "measure (\<lambda>(_, _, xs). card(UNIV :: 'a set) - card (set xs))";
      simp add: card_set_UNIV diff_less_mono2)

lemma heap_path_append[simp]:
  "heap_path hp start (xs @ ys) end = (\<exists>x. heap_path hp start xs x \<and> heap_path hp x ys end)"
  by (induct xs arbitrary: start; simp)

lemma heap_path_None[simp]:
  "heap_path hp None xs end = (xs = [] \<and> end = None)"
  by (cases xs, auto)

lemma heap_ls_unique:
  "\<lbrakk> heap_ls hp x xs; heap_ls hp x ys \<rbrakk> \<Longrightarrow> xs = ys"
  by (induct xs arbitrary: ys x; simp) (case_tac ys; clarsimp)

lemma heap_ls_hd_not_in_tl:
  "heap_ls hp (hp x) xs \<Longrightarrow> x \<notin> set xs"
proof
  assume "x \<in> set xs"
  then obtain ys zs where xs: "xs = ys @ x # zs"  by (auto simp: in_set_conv_decomp)
  moreover assume "heap_ls hp (hp x) xs"
  moreover from this xs have "heap_ls hp (hp x) zs" by clarsimp
  ultimately show False by (fastforce dest: heap_ls_unique)
qed

lemma heap_ls_distinct:
  "heap_ls hp x xs \<Longrightarrow> distinct xs"
  by (induct xs arbitrary: x; clarsimp simp: heap_ls_hd_not_in_tl)

lemma heap_ls_is_walk':
  "\<lbrakk> heap_ls hp x xs; set xs \<inter> set ys = {} \<rbrakk> \<Longrightarrow> heap_walk hp x ys = ys @ xs"
  by (frule heap_ls_distinct) (induct xs arbitrary: x ys; clarsimp)

lemma heap_ls_is_walk:
  "heap_ls hp x xs \<Longrightarrow> heap_walk hp x [] = xs"
  using heap_ls_is_walk' by fastforce

lemma heap_path_end_unique:
  "heap_path hp x xs y \<Longrightarrow> heap_path hp x xs y' \<Longrightarrow> y = y'"
  by (induct xs arbitrary: x; clarsimp)

lemma heap_path_head:
  "heap_path hp x xs y \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> x = Some (hd xs)"
  by (induct xs arbitrary: x; clarsimp)

lemma heap_path_non_nil_lookup_next:
  "heap_path hp x (xs@z#ys) y \<Longrightarrow> hp z = (case ys of [] \<Rightarrow> y | _ \<Rightarrow> Some (hd ys))"
  by (cases ys; fastforce)

lemma heap_path_prefix:
  "heap_path hp st ls ed \<Longrightarrow> \<forall>xs\<le>ls. heap_path hp st xs (if xs = [] then st else hp (last xs))"
  apply clarsimp
  apply (erule Prefix_Order.prefixE)
  by (metis append_butlast_last_id heap_path_append heap_path_non_nil_lookup_next list.case(1))

lemma heap_path_butlast:
  "heap_path hp st ls ed \<Longrightarrow> ls \<noteq> [] \<Longrightarrow> heap_path hp st (butlast ls) (Some (last ls))"
  by (induct ls rule: rev_induct; simp)

lemma in_list_decompose_takeWhile:
  "x \<in> set xs \<Longrightarrow>
   xs = (takeWhile ((\<noteq>) x) xs) @ x # (drop (length (takeWhile ((\<noteq>) x) xs) + 1) xs)"
  by (induct xs arbitrary: x; clarsimp)

lemma takeWhile_neq_hd_eq_Nil[simp]:
  "takeWhile ((\<noteq>) (hd xs)) xs = Nil"
  by (metis (full_types) hd_Cons_tl takeWhile.simps(1) takeWhile.simps(2))

lemma heap_not_in_dom[simp]:
  "ptr \<notin> dom hp \<Longrightarrow> hp(ptr := None) = hp"
  by (auto simp: dom_def)

lemma heap_path_takeWhile_lookup_next:
  "\<lbrakk> heap_path hp st rs ed; r \<in> set rs \<rbrakk>
   \<Longrightarrow> heap_path hp st (takeWhile ((\<noteq>) r) rs) (Some r)"
  apply (drule heap_path_prefix)
  apply (subgoal_tac "takeWhile ((\<noteq>) r) rs @ [r] \<le> rs", fastforce)
  by (fastforce dest!: in_list_decompose_takeWhile intro: Prefix_Order.prefixI)

lemma heap_path_heap_upd_not_in:
  "\<lbrakk>heap_path hp st rs ed; r \<notin> set rs\<rbrakk> \<Longrightarrow> heap_path (hp(r:= x)) st rs ed"
  by (induct rs arbitrary: st; clarsimp)

lemma heap_path_last_update:
  "\<lbrakk>heap_path hp st xs end; xs \<noteq> []; distinct xs\<rbrakk> \<Longrightarrow> heap_path (hp(last xs := new)) st xs new"
  by (induct xs arbitrary: st rule: rev_induct; simp add: heap_path_heap_upd_not_in)

lemma heap_walk_lb:
  "heap_walk hp x xs \<ge> xs"
  apply (induct xs rule: heap_walk.induct; clarsimp)
  by (metis Prefix_Order.prefixE Prefix_Order.prefixI append_assoc)

lemma heal_walk_Some_nonempty':
  "heap_walk hp (Some x) [] > []"
  by (fastforce intro: heap_walk_lb less_le_trans[where y="[x]"])

lemma heal_walk_Some_nonempty:
  "heap_walk hp (Some x) [] \<noteq> []"
  by (metis less_list_def heal_walk_Some_nonempty')

lemma heap_walk_Nil_None:
  "heap_walk hp st [] = [] \<Longrightarrow> st = None"
   by (case_tac st; simp only: heal_walk_Some_nonempty)

lemma heap_path_last_end:
  "heap_path hp st xs end \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> hp (last xs) = end"
  by (induct xs rule: rev_induct; clarsimp)

lemmas heap_ls_last_None = heap_path_last_end[where ?end=None]

(* sym_heap *)

definition sym_heap where
  "sym_heap hp hp' \<equiv> \<forall>p p'. hp p = Some p' \<longleftrightarrow> hp' p' = Some p"

lemma sym_heapD1:
  "sym_heap hp hp' \<Longrightarrow> hp p = Some p' \<Longrightarrow> hp' p' = Some p"
  by (clarsimp simp: sym_heap_def)

lemma sym_heapD2:
  "sym_heap hp hp' \<Longrightarrow> hp' p' = Some p \<Longrightarrow> hp p = Some p'"
  by (clarsimp simp: sym_heap_def)

lemma sym_heap_symmetric:
  "sym_heap hp hp' \<longleftrightarrow> sym_heap hp' hp"
  unfolding sym_heap_def by blast

lemma sym_heap_None:
  "\<lbrakk>sym_heap hp hp'; hp p = None\<rbrakk> \<Longrightarrow> \<forall>p'. hp' p' \<noteq> Some p" unfolding sym_heap_def by force

lemma sym_heap_path_reverse:
  "sym_heap hp hp' \<Longrightarrow>
      heap_path hp (Some p) (p#ps) (Some p')
          \<longleftrightarrow> heap_path hp' (Some p') (p'#(rev ps)) (Some p)"
  unfolding sym_heap_def by (induct ps arbitrary: p p' rule: rev_induct; force)

lemma sym_heap_ls_rev_Cons:
  "\<lbrakk>sym_heap hp hp'; heap_ls hp (Some p) (p#ps)\<rbrakk>
  \<Longrightarrow> heap_path hp' (Some (last (p#ps))) (rev ps) (Some p)"
  supply rev.simps[simp del]
  apply (induct ps arbitrary: p rule: rev_induct; simp add: rev.simps)
  by (auto dest!: sym_heap_path_reverse[THEN iffD1])

lemma sym_heap_ls_rev:
  "\<lbrakk>sym_heap hp hp'; heap_ls hp (Some p) ps\<rbrakk>
  \<Longrightarrow> heap_path hp' (Some (last ps)) (butlast (rev ps)) (Some p)
      \<and> hp (last ps) = None"
  apply (induct ps arbitrary: p rule: rev_induct, simp)
  apply (frule heap_path_head; clarsimp)
  by (auto dest!: sym_heap_path_reverse[THEN iffD1])

lemma heap_path_sym_heap_non_nil_lookup_prev:
  "\<lbrakk>heap_ls hp x (xs @ z # ys); sym_heap hp hp'; xs \<noteq> []\<rbrakk> \<Longrightarrow> hp' z = (Some (last xs))"
  supply heap_path_append[simp del]
  apply (cut_tac xs="butlast xs" and z="last xs" and ys="z # ys"
              in heap_path_non_nil_lookup_next[where hp=hp and x=x and y=None])
   apply (frule append_butlast_last_id)
   apply (metis append_eq_Cons_conv append_eq_append_conv2)
  apply (fastforce dest: sym_heapD1)
  done

(* more on heap_path : next/prev in path *)

lemma heap_path_extend:
  "heap_path hp st (ls @ [p]) (hp p) \<longleftrightarrow> heap_path hp st ls (Some p)"
  by (induct ls rule: rev_induct; simp)

lemma heap_path_prefix_heap_ls:
  "\<lbrakk>heap_ls hp st xs; heap_path hp st ys ed\<rbrakk> \<Longrightarrow> ys \<le> xs"
  apply (induct xs arbitrary: ys st, simp)
  apply (case_tac ys; clarsimp)
  done

lemma distinct_decompose2:
  "\<lbrakk>distinct xs; xs = ys @ x # y # zs\<rbrakk>
   \<Longrightarrow> x \<noteq> y \<and> x \<notin> set ys \<and> y \<notin> set ys \<and> x \<notin> set zs \<and> y \<notin> set zs"
  by (simp add: in_set_conv_decomp)

lemma heap_path_distinct_next_cases: (* the other direction needs sym_heap *)
  "\<lbrakk>heap_path hp st xs ed; distinct xs; p \<in> set xs; hp p = Some np\<rbrakk>
  \<Longrightarrow> ed = Some p \<or> ed = Some np \<or> np \<in> set xs"
  apply (cases ed; simp)
   apply (frule in_list_decompose_takeWhile)
   apply (subgoal_tac "heap_ls hp st (takeWhile ((\<noteq>) p) xs @ p # drop (length (takeWhile ((\<noteq>) p) xs) + 1) xs)")
   apply (drule heap_path_non_nil_lookup_next)
   apply (case_tac "drop (length (takeWhile ((\<noteq>) p) xs) + 1) xs"; simp)
   apply (metis in_set_dropD list.set_intros(1))
  apply simp
  apply (frule in_list_decompose_takeWhile)
  apply (subgoal_tac "heap_path hp st (takeWhile ((\<noteq>) p) xs @ p # drop (length (takeWhile ((\<noteq>) p) xs) + 1) xs) ed")
  apply (frule heap_path_non_nil_lookup_next)
  apply (case_tac "drop (length (takeWhile ((\<noteq>) p) xs) + 1) xs", simp)
  apply (simp split: if_split_asm)
  apply (drule (1) distinct_decompose2)
  apply clarsimp
  by (metis in_set_dropD list.set_intros(1)) simp

lemma heap_ls_next_in_list:
  "\<lbrakk>heap_ls hp st xs; p \<in> set xs; hp p = Some np\<rbrakk>
  \<Longrightarrow> np \<in> set xs"
   apply (subgoal_tac "distinct xs")
   by (fastforce dest!: heap_path_distinct_next_cases) (erule heap_ls_distinct)

lemma heap_path_distinct_sym_prev_cases:
  "\<lbrakk>heap_path hp st xs ed; distinct xs; np \<in> set xs; hp p = Some np; sym_heap hp hp'\<rbrakk>
  \<Longrightarrow> st = Some np \<or> p \<in> set xs"
  apply (cases st; simp)
  apply (rename_tac stp)
  apply (case_tac "stp = np"; simp)
  apply (cases xs; simp del: heap_path.simps)
  apply (frule heap_path_head, simp)
  apply (cases ed, clarsimp)
   apply (frule sym_heap_ls_rev_Cons, fastforce)
   apply (drule heap_path_distinct_next_cases[where hp=hp']; simp add: sym_heap_def)
   apply simp
  apply (simp del: heap_path.simps)
  apply (frule (1) sym_heap_path_reverse[where hp'=hp', THEN iffD1])
  apply simp
  apply (frule heap_path_distinct_next_cases[where hp=hp']; simp add: sym_heap_def)
  apply fastforce
  done

lemma heap_ls_prev_cases:
  "\<lbrakk>heap_ls hp st xs; np \<in> set xs; hp p = Some np; sym_heap hp hp'\<rbrakk>
  \<Longrightarrow> st = Some np \<or> p \<in> set xs"
   apply (subgoal_tac "distinct xs")
   by (fastforce dest!: heap_path_distinct_sym_prev_cases) (erule heap_ls_distinct)

lemma heap_ls_prev_not_in:
  "\<lbrakk>heap_ls hp st xs; np \<notin> set xs; hp p = Some np\<rbrakk>
  \<Longrightarrow> p \<notin> set xs"
  by (meson heap_ls_next_in_list)

lemma heap_path_distinct_prev_not_in:
  "\<lbrakk>heap_path hp st xs ed; distinct xs; np \<notin> set xs; hp p = Some np; ed \<noteq> Some np; ed \<noteq> Some p\<rbrakk>
  \<Longrightarrow> p \<notin> set xs"
  using heap_path_distinct_next_cases
  by fastforce

lemma heap_path_distinct_next_not_in:
  "\<lbrakk>heap_path hp st xs ed; distinct xs; p \<notin> set xs; hp p = Some np;
    sym_heap hp hp'; st \<noteq> Some np\<rbrakk>
  \<Longrightarrow> np \<notin> set xs"
  by (fastforce dest!: heap_path_distinct_sym_prev_cases[simplified])

lemma heap_ls_next_not_in:
  "\<lbrakk>heap_ls hp st xs; p \<notin> set xs; hp p = Some np; sym_heap hp hp'; st \<noteq> Some np\<rbrakk>
  \<Longrightarrow> np \<notin> set xs"
  by (fastforce dest!: heap_ls_prev_cases[simplified])

(* more on heap_path *)

lemma heap_ls_next_takeWhile_append:
  "\<lbrakk>heap_ls hp st xs; p \<in> set xs; hp p = Some np\<rbrakk>
  \<Longrightarrow> takeWhile ((\<noteq>) np) xs = (takeWhile ((\<noteq>) p) xs) @ [p]"
  apply (frule heap_ls_distinct)
  apply (frule in_list_decompose_takeWhile)
  apply (subgoal_tac "heap_ls hp st (takeWhile ((\<noteq>) p) xs @ p # drop (length (takeWhile ((\<noteq>) p) xs) + 1) xs)")
   prefer 2 apply simp
  apply (drule heap_path_non_nil_lookup_next)
  apply (case_tac "drop (length (takeWhile ((\<noteq>) p) xs) + 1) xs"; simp)
  apply (subgoal_tac "np \<in> set xs")
   prefer 2 apply (erule (2) heap_ls_next_in_list)
  apply (frule in_list_decompose_takeWhile[where x=np])
  apply (drule (1) distinct_inj_middle[where x=np and xa="takeWhile ((\<noteq>) np) xs" and ya="takeWhile ((\<noteq>) p) xs @ [p]"])
   apply simp+
  done

(* RT FIXME: Move *)
lemma takeWhile_neq_notin_same:
  "x \<notin> set xs \<Longrightarrow> takeWhile ((\<noteq>) x) xs = xs"
  using takeWhile_eq_all_conv by blast

lemma heap_path_extend_takeWhile:
  "\<lbrakk>heap_ls hp st xs; heap_path hp st (takeWhile ((\<noteq>) p) xs) (Some p); hp p = Some np\<rbrakk>
  \<Longrightarrow> heap_path hp st (takeWhile ((\<noteq>) np) xs) (Some np)"
  apply (case_tac "p \<in> set xs")
  apply (subst heap_ls_next_takeWhile_append[where p=p and np=np and hp=hp]; simp)
  apply (drule takeWhile_neq_notin_same, simp)
  apply (drule (1) heap_path_end_unique, simp)
  done

lemma heap_ls_next_takeWhile_append_sym:
  "\<lbrakk>heap_ls hp st xs; np \<in> set xs; st \<noteq> Some np; hp p = Some np; sym_heap hp hp'\<rbrakk>
  \<Longrightarrow>takeWhile ((\<noteq>) np) xs = (takeWhile ((\<noteq>) p) xs) @ [p]"
  apply (frule (3) heap_ls_prev_cases, simp)
  apply (fastforce elim!: heap_ls_next_takeWhile_append)
  done

lemma heap_path_curtail_takeWhile:
  "\<lbrakk>heap_ls hp st xs; heap_path hp st (takeWhile ((\<noteq>) np) xs) (Some np);
    st \<noteq> Some np; hp p = Some np; sym_heap hp hp'\<rbrakk>
  \<Longrightarrow> heap_path hp st (takeWhile ((\<noteq>) p) xs) (Some p)"
  apply (case_tac "np \<in> set xs")
   apply (drule (4) heap_ls_next_takeWhile_append_sym)
   apply simp
  apply (drule takeWhile_neq_notin_same, simp)
  apply (drule (1) heap_path_end_unique, simp)
  done

(* more on heap_path : end *)


\<comment> \<open>Lemmas relating an update to the list to an update to the heap\<close>

lemma heap_ls_prepend:
  "\<lbrakk>heap_ls hp st xs; new \<notin> set xs; xs \<noteq> []\<rbrakk>
   \<Longrightarrow> heap_ls (hp(new := Some (hd xs))) (Some new) (new # xs)"
  apply simp
  apply (erule heap_path_heap_upd_not_in[rotated])
  apply (frule (1) heap_path_head)
  apply fastforce
  done

lemma heap_ls_append:
  "\<lbrakk>heap_ls hp st xs; xs \<noteq> []; new \<notin> set xs\<rbrakk>
   \<Longrightarrow> heap_ls (hp(last xs := Some new, new := None)) st (xs @ [new])"
  apply (frule heap_ls_distinct)
  apply simp
  apply (rule heap_path_heap_upd_not_in)
   apply (fastforce simp: heap_path_last_update)
  apply assumption
  done

lemma heap_ls_list_insert_before:
  "\<lbrakk>heap_ls hp st (xs @ ys); new \<notin> set (xs @ ys); xs \<noteq> []; ys \<noteq> []\<rbrakk>
   \<Longrightarrow> heap_ls (hp(last xs := Some new, new := Some (hd ys))) st
               (list_insert_before (xs @ ys) (hd ys) new)"
  apply (frule heap_ls_distinct)
  apply (subst list_insert_before_distinct; fastforce?)
  apply simp
  apply (rule conjI)
   \<comment> \<open>the path until new\<close>
   apply (fastforce intro: heap_path_heap_upd_not_in heap_path_last_update)
  \<comment> \<open>the path from hd ys\<close>
  apply (metis disjoint_iff_not_equal heap_path_head heap_path_heap_upd_not_in last_in_set)
  done

lemma heap_ls_remove_singleton:
  "heap_ls hp st [x] \<Longrightarrow> heap_ls (hp(x := None)) None []"
  by simp

lemma heap_ls_remove_head_not_singleton:
  "\<lbrakk>heap_ls hp st xs; tl xs \<noteq> []\<rbrakk>
   \<Longrightarrow> heap_ls (hp(hd xs := None)) (Some (hd (tl xs))) (tl xs)"
  apply (frule heap_ls_distinct)
  apply (cases xs; simp)
  apply clarsimp
  apply (frule heap_path_head)
   apply fastforce
  apply (fastforce elim!: heap_path_heap_upd_not_in)
  done

lemma heap_ls_remove_last_not_singleton:
  "\<lbrakk>heap_ls hp st xs; butlast xs \<noteq> []\<rbrakk>
   \<Longrightarrow> heap_ls (hp((last (butlast xs)) := None)) st (butlast xs)"
  apply (frule heap_ls_distinct)
  apply (frule distinct_butlast)
  apply (fastforce dest: heap_path_last_update heap_path_butlast)
  done

lemma heap_ls_remove_middle:
  "\<lbrakk>heap_ls hp st (xs @ a # ys); xs \<noteq> []; ys \<noteq> []\<rbrakk>
   \<Longrightarrow> heap_ls (hp(last xs := Some (hd ys), a := None)) st (xs @ ys)"
  apply (frule heap_ls_distinct)
  apply simp
  apply (rule_tac x="Some (hd ys)" in exI)
  apply (rule conjI)
   apply (fastforce intro: heap_path_heap_upd_not_in heap_path_last_update)
  apply (rule heap_path_heap_upd_not_in)
   apply (rule heap_path_heap_upd_not_in)
    using heap_path_head apply fastforce
   apply force
  apply fastforce
  done

end