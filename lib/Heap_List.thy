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

lemma heap_path_not_Nil:
  "heap_ls hp (Some st) ls \<Longrightarrow> ls \<noteq> []"
  by fastforce

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

lemma heap_path_head':
  "heap_path hp st xs y \<Longrightarrow> xs \<noteq> [] \<longrightarrow> st = Some (hd xs)"
  by (induct xs arbitrary: st; clarsimp)

lemmas heap_path_head = heap_path_head'[rule_format]

lemma heap_path_non_nil_lookup_next:
  "heap_path hp x (xs@z#ys) y \<Longrightarrow> hp z = (case ys of [] \<Rightarrow> y | _ \<Rightarrow> Some (hd ys))"
  by (cases ys; fastforce)

lemma heap_ls_next_of_hd:
  "\<lbrakk>a = hd ls; heap_ls hp st ls; Suc 0 < length ls\<rbrakk> \<Longrightarrow> hp a = Some (hd (tl ls))"
  apply (cut_tac hp=hp and xs="[]" and z=a and ys="tl ls" in heap_path_non_nil_lookup_next)
   apply (prop_tac "ls \<noteq> []", fastforce)
   apply fastforce
  apply (cases "tl ls"; clarsimp)
  apply (cases ls; clarsimp)
  done

lemma heap_path_prefix:
  "heap_path hp st ls ed \<Longrightarrow> \<forall>xs\<le>ls. heap_path hp st xs (if xs = [] then st else hp (last xs))"
  apply clarsimp
  apply (erule Prefix_Order.prefixE)
  by (metis append_butlast_last_id heap_path_append heap_path_non_nil_lookup_next list.case(1))

lemma heap_ls_suffix:
  "\<lbrakk> heap_ls hp (Some t) xs; heap_ls hp x ys; t \<in> set ys \<rbrakk> \<Longrightarrow> suffix xs ys"
  apply (drule_tac xs1=ys in in_set_conv_decomp_first[THEN iffD1])
  apply clarsimp
  apply (rename_tac pfx zs)
  apply (prop_tac "xs = t # zs")
   apply (simp add: heap_ls_unique)
  apply (clarsimp simp: suffix_def)
  done

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

lemma heap_path_heap_upd_not_in_strong:
  "\<lbrakk>heap_path hp st rs ed; \<forall>t \<in> set rs. hp' t = hp t\<rbrakk> \<Longrightarrow> heap_path hp' st rs ed"
  by (induct rs arbitrary: st; clarsimp)

lemma heap_path_heap_upd_not_in:
  "\<lbrakk>heap_path hp st rs ed; r \<notin> set rs\<rbrakk> \<Longrightarrow> heap_path (hp(r:= x)) st rs ed"
  by (fastforce elim: heap_path_heap_upd_not_in_strong)

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

lemmas heap_ls_cong = rsubst3[where P=heap_ls]

(* sym_heap *)

definition sym_heap where
  "sym_heap hp hp' \<equiv> \<forall>p p'. hp p = Some p' \<longleftrightarrow> hp' p' = Some p"

lemmas sym_heap_cong = rsubst2[where P=sym_heap]

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

lemma sym_heap_remove_only:
  "\<lbrakk>sym_heap hp hp'; hp' y = Some x\<rbrakk> \<Longrightarrow> sym_heap (hp(x := None)) (hp'(y := None))"
  apply (clarsimp simp: sym_heap_def)
  apply (metis option.inject)
  done

lemma sym_heap_remove_only':
  "\<lbrakk>sym_heap hp hp'; hp y = Some x\<rbrakk> \<Longrightarrow> sym_heap (hp(y := None)) (hp'(x := None))"
  apply (clarsimp simp: sym_heap_def)
  apply (metis option.inject)
  done

lemma sym_heap_remove_middle_from_chain:
  "\<lbrakk>sym_heap hp hp'; before \<noteq> middle; middle \<noteq> after;
    hp before = Some middle; hp middle = Some after\<rbrakk>
   \<Longrightarrow> sym_heap (hp(before := Some after, middle := None))
                (hp'(after := Some before, middle := None))"
  apply (clarsimp simp: sym_heap_def)
  apply (metis option.simps(1))
  done

lemma sym_heap_connect:
  "\<lbrakk>sym_heap hp hp'; hp a = None; hp' b = None \<rbrakk> \<Longrightarrow> sym_heap (hp(a \<mapsto> b)) (hp'(b \<mapsto> a))"
  by (force simp: sym_heap_def)

lemma sym_heap_insert_into_middle_of_chain:
  "\<lbrakk>sym_heap hp hp'; hp before = Some after; hp middle = None; hp' middle = None\<rbrakk>
   \<Longrightarrow> sym_heap (hp(before \<mapsto> middle, middle \<mapsto> after)) (hp'(after \<mapsto> middle, middle \<mapsto> before))"
  apply (clarsimp simp: sym_heap_def)
  apply (metis option.simps)
  done

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
  "\<lbrakk>heap_path hp x (xs @ z # ys) ed; sym_heap hp hp'; xs \<noteq> []\<rbrakk> \<Longrightarrow> hp' z = (Some (last xs))"
  apply (cut_tac xs="butlast xs" and z="last xs" and ys="z # ys"
              in heap_path_non_nil_lookup_next[where hp=hp and x=x and y=ed])
   apply (frule append_butlast_last_id)
   apply (metis Cons_eq_append_conv append.assoc)
  apply (fastforce dest: sym_heapD1)
  done

lemma heap_path_prev_of_last:
  "\<lbrakk>heap_path hp st ls ed; sym_heap hp hp'; Suc 0 < length ls\<rbrakk>
   \<Longrightarrow> hp' (last ls) = Some (last (butlast ls))"
  apply (cut_tac hp=hp and xs="butlast ls" and z="last ls" and ys="[]"
              in heap_path_sym_heap_non_nil_lookup_prev)
     apply (prop_tac "ls \<noteq> []", fastforce)
     apply fastforce
    apply fastforce
   apply (fastforce intro!: length_gt_1_imp_butlast_nonempty)
  apply assumption
  done

lemma ptr_in_middle_prev_next:
  "\<lbrakk>heap_ls hp st (xs @ ptr # ys); xs \<noteq> []; ys \<noteq> []; sym_heap hp hp'\<rbrakk>
   \<Longrightarrow> hp' ptr = Some (last xs) \<and> hp ptr = Some (hd ys)"
  apply (rule conjI)
   apply (fastforce dest: heap_path_sym_heap_non_nil_lookup_prev)
  apply (cut_tac hp=hp in heap_path_non_nil_lookup_next)
   apply fastforce
  apply (cases ys; clarsimp)
  done

lemma heap_ls_no_loops:
  "\<lbrakk>heap_ls hp st xs; p \<in> set xs\<rbrakk> \<Longrightarrow> hp p \<noteq> Some p"
  apply (frule heap_ls_distinct)
  apply (fastforce dest: split_list heap_path_non_nil_lookup_next split: list.splits)
  done

lemma heap_ls_prev_no_loops:
  "\<lbrakk>heap_ls hp st xs; p \<in> set xs; sym_heap hp hp'\<rbrakk> \<Longrightarrow> hp' p \<noteq> Some p"
  by (fastforce dest: heap_ls_no_loops sym_heapD2)

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

lemma sym_heap_prev_None_is_start:
  "\<lbrakk>heap_ls hp st xs; sym_heap hp hp'; p \<in> set xs; hp' p = None\<rbrakk>
   \<Longrightarrow> Some p = st"
  using split_list_last heap_path_sym_heap_non_nil_lookup_prev
  by fastforce

lemma not_last_next_not_None:
  "\<lbrakk>heap_ls hp st xs; p \<in> set xs; p \<noteq> last xs\<rbrakk> \<Longrightarrow> hp p \<noteq> None"
  by (fastforce intro: heap_path_head dest: split_list)

lemma not_head_prev_not_None:
  "\<lbrakk>heap_ls hp st xs; p \<in> set xs; p \<noteq> hd xs; sym_heap hp hp'\<rbrakk>
   \<Longrightarrow> hp' p \<noteq> None"
  using sym_heap_prev_None_is_start heap_path_head
  by fastforce

lemma heap_ls_neighbour_in_set:
  "\<lbrakk>heap_ls hp st xs; sym_heap hp hp'; st \<noteq> None \<longrightarrow> hp' (the st) = None; p \<in> set xs\<rbrakk>
   \<Longrightarrow> \<forall>nbr. (hp p = Some nbr \<longrightarrow> nbr \<in> set xs) \<and> (hp' p = Some nbr \<longrightarrow> nbr \<in> set xs)"
  apply (intro conjI impI allI)
   apply (erule (2) heap_ls_next_in_list)
  apply (fastforce dest: heap_ls_prev_cases[where np=p] sym_heapD2)
  done

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


section \<open>
  Definitions and lemmas for relating an Isabelle list to a pointer data structure that implements
  a doubly-linked list with a separate head/end structure. This implementation is used as a queue
  on seL4/master, but no longer represents an actual queue on seL4/MCS. Because of the former, many
  of the names in the C and Haskell implementation refer to "queue" for this heap structure.\<close>

datatype 'a head_end_ptrs =
  HeadEndPtrs (he_ptrs_head : "'a option") (he_ptrs_end : "'a option")

primrec he_ptrs_head_update :: "('a option \<Rightarrow> 'a option) \<Rightarrow> 'a head_end_ptrs \<Rightarrow> 'a head_end_ptrs" where
  "he_ptrs_head_update f (HeadEndPtrs h e) = HeadEndPtrs (f h) e"

primrec he_ptrs_end_update :: "('a option \<Rightarrow> 'a option) \<Rightarrow> 'a head_end_ptrs \<Rightarrow> 'a head_end_ptrs" where
  "he_ptrs_end_update f (HeadEndPtrs h e) = HeadEndPtrs h (f e)"

lemma he_ptrs_head_he_ptrs_head_update[simp]:
  "he_ptrs_head (he_ptrs_head_update f v) = f (he_ptrs_head v)"
  by (cases v) simp

lemma he_ptrs_head_he_ptrs_end_update[simp]:
  "he_ptrs_head (he_ptrs_end_update f v) = he_ptrs_head v"
  by (cases v) simp

lemma he_ptrs_end_he_ptrs_head_update[simp]:
  "he_ptrs_end (he_ptrs_head_update f v) = he_ptrs_end v"
  by (cases v) simp

lemma he_ptrs_end_tcbQueueEnd_update[simp]:
  "he_ptrs_end (he_ptrs_end_update f v) = f (he_ptrs_end v)"
  by (cases v) simp

definition emptyHeadEndPtrs :: "'a head_end_ptrs" where
  "emptyHeadEndPtrs \<equiv> HeadEndPtrs None None"

definition headEndPtrsEmpty :: "'a head_end_ptrs => bool" where
  "headEndPtrsEmpty q \<equiv> he_ptrs_head q = None"

definition queue_end_valid :: "'a list \<Rightarrow> 'a head_end_ptrs \<Rightarrow> bool" where
  "queue_end_valid ts q \<equiv>
     (ts = [] \<longrightarrow> he_ptrs_end q = None) \<and> (ts \<noteq> [] \<longrightarrow> he_ptrs_end q = Some (last ts))"

definition prev_queue_head :: "'a head_end_ptrs \<Rightarrow> ('a \<rightharpoonup> 'a) \<Rightarrow> bool" where
  "prev_queue_head q prevs \<equiv> \<forall>head. he_ptrs_head q = Some head \<longrightarrow> prevs head = None"

lemma prev_queue_head_heap_upd:
  "\<lbrakk>prev_queue_head q prevs; Some r \<noteq> he_ptrs_head q\<rbrakk> \<Longrightarrow> prev_queue_head q (prevs(r := x))"
  by (clarsimp simp: prev_queue_head_def)

definition list_queue_relation ::
  "'a list \<Rightarrow> 'a head_end_ptrs \<Rightarrow> ('a \<rightharpoonup> 'a) \<Rightarrow> ('a \<rightharpoonup> 'a) \<Rightarrow> bool"
  where
  "list_queue_relation ts q nexts prevs \<equiv>
     heap_ls nexts (he_ptrs_head q) ts \<and> queue_end_valid ts q \<and> prev_queue_head q prevs"

lemmas list_queue_relation_cong = rsubst4[where P=list_queue_relation]

lemma list_queue_relation_Nil:
  "list_queue_relation ts q nexts prevs \<Longrightarrow> ts = [] \<longleftrightarrow> headEndPtrsEmpty q"
  by (fastforce dest: heap_path_head simp: headEndPtrsEmpty_def list_queue_relation_def)

lemma list_queue_relation_Nil_emptyQueue[simp]:
  "list_queue_relation [] emptyHeadEndPtrs hp hp'"
  by (clarsimp simp: list_queue_relation_def queue_end_valid_def prev_queue_head_def
                     emptyHeadEndPtrs_def)

lemma he_ptrs_head_iff_he_ptrs_end:
  "list_queue_relation ts q nexts prevs
   \<Longrightarrow> (\<exists>head. he_ptrs_head q = Some head) \<longleftrightarrow> (\<exists>end. he_ptrs_end q = Some end)"
  apply (clarsimp simp: list_queue_relation_def queue_end_valid_def)
  using heap_path_None
  apply fastforce
  done

lemma list_queue_relation_neighbour_in_set:
  "\<lbrakk>list_queue_relation ls q hp hp'; sym_heap hp hp'; p \<in> set ls\<rbrakk>
   \<Longrightarrow> \<forall>nbr. (hp p = Some nbr \<longrightarrow> nbr \<in> set ls) \<and> (hp' p = Some nbr \<longrightarrow> nbr \<in> set ls)"
  apply (rule heap_ls_neighbour_in_set)
     apply (fastforce simp: list_queue_relation_def)
    apply fastforce
   apply (clarsimp simp: list_queue_relation_def prev_queue_head_def)
  apply fastforce
  done


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