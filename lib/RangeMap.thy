(*
 * Copyright 2019, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory RangeMap
imports
  FastMap
  FP_Eval
  "ml-helpers/MkTermAntiquote"
begin

text \<open>
  Efficient rules and tactics for working with range maps.
  A range map partitions the key space into sorted disjoint ranges.
  This is useful for, e.g. representing program heaps, allowing one to quickly
  look up which object covers any given address.

  Features:
    \<^item> Define a binary lookup tree for any lookup table (requires linorder keys)
    \<^item> Conversion between lookup trees and lists
    \<^item> Pre-computation of lookup results and domain/range sets

  See RangeMap_Tests for examples.
\<close>

section \<open>Preliminaries: generalised lookup lists\<close>

definition lookup_upd :: "('k \<Rightarrow> 'l \<Rightarrow> bool) \<Rightarrow> ('l \<Rightarrow> 'k \<times> 'v) \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> ('l \<Rightarrow> 'k \<times> 'v)"
  where
  "lookup_upd eq f k v \<equiv> \<lambda>x. if eq k x then (k, v) else f x"

fun lookup_map_of :: "('k \<Rightarrow> 'l \<Rightarrow> bool) \<Rightarrow> ('k \<times> 'v) list \<Rightarrow> ('l \<Rightarrow> ('k \<times> 'v) option)"
  where
    "lookup_map_of eq [] = Map.empty"
  | "lookup_map_of eq ((k, v)#kvs) = (\<lambda>x. if eq k x then Some (k, v) else lookup_map_of eq kvs x)"

lemma map_of_to_lookup_map_of:
  "map_of kvs = map_option snd o lookup_map_of (=) kvs"
  by (induct kvs; auto)

lemma lookup_map_of_Some:
  "lookup_map_of eq kvs k = Some (k', v') \<Longrightarrow> (k', v') \<in> set kvs \<and> eq k' k"
  by (induct kvs; fastforce split: if_splits)

lemma lookup_map_of_None:
  "lookup_map_of eq kvs k = None \<Longrightarrow> \<forall>(k', v') \<in> set kvs. \<not> eq k' k"
  by (induct kvs; fastforce split: if_splits)


subsection \<open>Distinct ordered pairs of list elements\<close>

fun list_pairwise :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
  where
  "list_pairwise P [] = True"
| "list_pairwise P (x#xs) = ((\<forall>y \<in> set xs. P x y) \<and> list_pairwise P xs)"

lemma list_pairwise_as_indices:
  "list_pairwise P xs = (\<forall>i j. i < j \<and> j < length xs \<longrightarrow> P (xs ! i) (xs ! j))"
  apply (induct xs)
   apply simp
  apply (rule iffI)
   apply clarsimp
   apply (case_tac "i = 0")
    apply simp
   apply simp
   apply (drule_tac x="i - 1" in spec, drule_tac x="j - 1" in spec)
   apply simp
   apply linarith
  apply simp
  apply (rule conjI)
   apply clarsimp
   apply (subst (asm) in_set_conv_nth, erule exE)
   apply (rename_tac j)
   apply (drule_tac x="0" in spec, drule_tac x="j + 1" in spec)
   apply simp
  apply clarsimp
  apply (drule_tac x="i + 1" in spec, drule_tac x="j + 1" in spec)
  apply simp
  done

lemma list_pairwise_snoc:
  "list_pairwise P (xs @ [x]) = ((\<forall>y \<in> set xs. P y x) \<and> list_pairwise P xs)"
  by (induct xs; auto)

lemma list_pairwise_append:
  "list_pairwise P (xs @ ys) =
   (list_pairwise P xs \<and> list_pairwise P ys \<and> (\<forall>x \<in> set xs. \<forall>y \<in> set ys. P x y))"
  by (induct xs; auto)

lemma index_rev_rev_eq:
  fixes i :: nat and n :: nat
  shows "i < n \<Longrightarrow> n - (n - i - 1) - 1 = i"
  by simp

lemma list_pairwise_rev:
  "list_pairwise P (rev xs) = list_pairwise (swp P) xs"
  apply (simp add: list_pairwise_as_indices swp_def)
  apply (case_tac "xs = []")
   apply simp
  apply (rule iffI)
   apply (intro allI impI)
   apply (drule_tac x="length xs - j - 1" in spec, drule_tac x="length xs - i - 1" in spec)
   apply (clarsimp simp: rev_nth)
  apply (clarsimp simp: rev_nth)
  done

lemma list_pairwise_imp:
  "\<lbrakk> \<And>i j. \<lbrakk> i < j; P (xs ! i) (xs ! j) \<rbrakk> \<Longrightarrow> Q (xs ! i) (xs ! j) \<rbrakk> \<Longrightarrow>
   list_pairwise P xs \<Longrightarrow> list_pairwise Q xs"
  by (simp add: list_pairwise_as_indices)

lemma list_pairwise_imp_weak:
  "\<lbrakk> \<And>x y. \<lbrakk> x \<in> set xs; y \<in> set xs; P x y \<rbrakk> \<Longrightarrow> Q x y \<rbrakk> \<Longrightarrow>
   list_pairwise P xs \<Longrightarrow> list_pairwise Q xs"
  by (simp add: list_pairwise_as_indices)

lemma list_pairwise_commute:
  "symp P \<Longrightarrow> list_pairwise P (xs @ ys) = list_pairwise P (ys @ xs)"
  by (fastforce simp: list_pairwise_append symp_def)


subsection \<open>Predicate for disjoint keys\<close>

definition lookup_map_disjoint_keys :: "('k \<Rightarrow> 'x \<Rightarrow> bool) \<Rightarrow> ('k \<times> 'v) list \<Rightarrow> bool"
  where
  "lookup_map_disjoint_keys eq =
     list_pairwise (\<lambda>(k, _) (k', _). disjnt (Collect (eq k)) (Collect (eq k')))"

lemma ran_lookup_map_of:
  "ran (lookup_map_of eq []) = {}"
  "ran (lookup_map_of eq ((k, v)#kvs)) =
     (if Collect (eq k) \<noteq> {} then {(k, v)} else {})
     \<union> ran (lookup_map_of eq kvs |` Collect (not (eq k)))"
  by (auto simp: ran_def restrict_map_def pred_neg_def)

lemma ran_lookup_map_of_disjoint:
  "ran (lookup_map_of eq []) = {}"
  "\<forall>(k', v') \<in> set kvs. \<forall>x. eq k x \<longrightarrow> \<not>eq k' x
   \<Longrightarrow> ran (lookup_map_of eq ((k, v)#kvs)) =
         (if Collect (eq k) \<noteq> {} then {(k, v)} else {})
         \<union> ran (lookup_map_of eq kvs)"
  apply simp

  apply (subst ran_lookup_map_of)
  apply (clarsimp simp: restrict_map_def pred_neg_def)
  apply (rule arg_cong[where f="insert _"])
  apply (force simp: ran_def dest: lookup_map_of_Some)
  done


locale RangeMap begin

section \<open>Range maps as lookup lists\<close>

text \<open>
  Helper for proofs and some automation. This predicate is normally not
  visible to end users.

  Note that we use [start, end) ranges. This fits well with 0-based
  memory addressing semantics, but such ranges cannot cover the
  maximum key value (if there is one).
\<close>
fun in_range :: "('k::linorder \<times> 'k) \<Rightarrow> 'k \<Rightarrow> bool"
  where
  "in_range (start, end) k = (start \<le> k \<and> k < end)"

declare in_range.simps[simp del]
declare in_range.simps[THEN iffD1, dest]

lemma Collect_in_range_atLeastLessThan[simp]:
  "Collect (in_range r) = {fst r ..< snd r}"
  by (cases r; fastforce simp: in_range.simps ord_class.atLeastLessThan_iff)

definition "range_map_of \<equiv> lookup_map_of in_range"

lemmas range_map_of_Some' =
  lookup_map_of_Some[where eq=in_range, folded range_map_of_def]
lemmas range_map_of_Some =
  range_map_of_Some'[where k'="(start', end')" for start' end', simplified in_range.simps]

lemma range_map_of_SomeD:
  "range_map_of kvs k = Some ((start, end), v) \<Longrightarrow>
   ((start, end), v) \<in> set kvs \<and> start \<le> k \<and> k < end"
  by (fastforce simp: in_range.simps dest: range_map_of_Some')

subsection \<open>Disjoint and monotonic key ranges\<close>

definition disjoint_key_ranges :: "(('k::linorder \<times> 'k) \<times> 'v) list \<Rightarrow> bool"
  where
  "disjoint_key_ranges = lookup_map_disjoint_keys in_range"

fun monotonic_key_ranges :: "(('k::linorder \<times> 'k) \<times> 'v) list \<Rightarrow> bool"
  where
    "monotonic_key_ranges (((start, end), _) # ((start', end'), v') # kvs) =
       (start \<le> end \<and> end \<le> start' \<and> monotonic_key_ranges (((start', end'), v') # kvs))"
  | "monotonic_key_ranges [((start, end), _)] = (start \<le> end)"
  | "monotonic_key_ranges [] = True"

lemma monotonic_key_ranges_alt_def:
  "monotonic_key_ranges kvs =
     (list_all (\<lambda>((start, end), _). start \<le> end) kvs
      \<and> list_pairwise (\<lambda>((start, end), _) ((start', end'), _). end \<le> start') kvs)"
  apply (induct kvs rule: monotonic_key_ranges.induct)
    apply auto
  done

lemma monotonic_key_ranges_disjoint:
  "monotonic_key_ranges kvs \<Longrightarrow> disjoint_key_ranges kvs"
  apply (simp add: monotonic_key_ranges_alt_def
                   disjoint_key_ranges_def lookup_map_disjoint_keys_def disjnt_def)
  apply (induct kvs; fastforce)
  done


section \<open>Search trees for ranges\<close>

text \<open>
  Binary search tree. This is largely an implementation detail, so we
  choose the structure to make automation easier (e.g. separate fields
  for the keys and value).

  We could reuse HOL.Tree instead, but the proofs would need changing.

  NB: this is not the same as "range trees" in the data structures
      literature, but just ordinary search trees.
\<close>
datatype ('k, 'v) RangeTree =
    Leaf
  | Node 'k 'k 'v "('k, 'v) RangeTree" "('k, 'v) RangeTree"

primrec lookup_range_tree :: "('k::linorder, 'v) RangeTree \<Rightarrow> 'k \<Rightarrow> (('k \<times> 'k) \<times> 'v) option"
  where
    "lookup_range_tree Leaf x = None"
  | "lookup_range_tree (Node start end v l r) x =
       (if start \<le> x \<and> x < end then Some ((start, end), v)
        else if x < start then lookup_range_tree l x
        else lookup_range_tree r x)"

text \<open>
  Predicate for well-formed search trees.
  This states that the ranges are disjoint and appear in ascending order,
  and all ranges have correctly ordered key pairs.
  It also returns the lowest and highest keys in the tree (or None for empty trees).
\<close>
primrec lookup_range_tree_valid ::
        "('k::linorder, 'v) RangeTree \<Rightarrow> bool \<times> ('k \<times> 'k) option"
  where
    "lookup_range_tree_valid Leaf = (True, None)"
  | "lookup_range_tree_valid (Node start end v lt rt) =
       (let (lt_valid, lt_range) = lookup_range_tree_valid lt;
            (rt_valid, rt_range) = lookup_range_tree_valid rt;
            lt_low = (case lt_range of None \<Rightarrow> start | Some (low, high) \<Rightarrow> low);
            rt_high = (case rt_range of None \<Rightarrow> end | Some (low, high) \<Rightarrow> high)
        in (lt_valid \<and> rt_valid \<and> start \<le> end \<and>
            (case lt_range of None \<Rightarrow> True | Some (low, high) \<Rightarrow> high \<le> start) \<and>
            (case rt_range of None \<Rightarrow> True | Some (low, high) \<Rightarrow> end \<le> low),
            Some (lt_low, rt_high)))"

lemma lookup_range_tree_valid_empty:
  "lookup_range_tree_valid tree = (True, None) \<Longrightarrow> tree = Leaf"
  apply (induct tree)
   apply simp
  apply (fastforce split: prod.splits option.splits if_splits)
  done

lemma lookup_range_tree_valid_range:
  "lookup_range_tree_valid tree = (True, Some (low, high)) \<Longrightarrow> low \<le> high"
  apply (induct tree arbitrary: low high)
   apply simp
  apply (fastforce split: prod.splits option.splits if_splits)
  done

lemma lookup_range_tree_valid_in_range:
  "lookup_range_tree_valid tree = (True, Some (low, high)) \<Longrightarrow>
   lookup_range_tree tree k = Some ((start, end), v) \<Longrightarrow>
   in_range (start, end) k \<and> low \<le> start \<and> end \<le> high"
  apply (induct tree arbitrary: k v low high)
   apply simp
  apply (fastforce simp: in_range.simps
                   split: prod.splits option.splits if_split_asm
                   dest: lookup_range_tree_valid_empty lookup_range_tree_valid_range)
  done

lemma lookup_range_tree_valid_in_range_None:
  "lookup_range_tree_valid tree = (True, Some (low, high)) \<Longrightarrow>
   \<not> in_range (low, high) k \<Longrightarrow>
   lookup_range_tree tree k = None"
  apply (erule contrapos_np)
  apply (fastforce simp: in_range.simps dest: lookup_range_tree_valid_in_range)
  done

text \<open>
  Flatten a lookup tree into an assoc-list.
  As long as the tree is well-formed, both forms are equivalent.
\<close>
primrec lookup_range_tree_to_list :: "('k, 'v) RangeTree \<Rightarrow> (('k \<times> 'k) \<times> 'v) list"
  where
    "lookup_range_tree_to_list Leaf = []"
  | "lookup_range_tree_to_list (Node start end v lt rt) =
        lookup_range_tree_to_list lt @ [((start, end), v)] @ lookup_range_tree_to_list rt"

lemma lookup_range_tree_to_list_range:
  "lookup_range_tree_valid tree = (True, Some (low, high)) \<Longrightarrow>
   ((start, end), v) \<in> set (lookup_range_tree_to_list tree) \<Longrightarrow>
   low \<le> start \<and> start \<le> end \<and> end \<le> high"
  apply (induct tree arbitrary: start "end" v low high)
   apply simp
  apply (fastforce split: prod.splits option.splits if_split_asm
                   dest: lookup_range_tree_valid_empty lookup_range_tree_valid_range)
  done

lemma monotonic_ranges_each_valid:
  "monotonic_key_ranges xs \<Longrightarrow> ((start, end), v) \<in> set xs \<Longrightarrow> start \<le> end"
  by (fastforce simp: monotonic_key_ranges_alt_def list_all_iff)

lemma lookup_range_tree_list_monotonic:
  "fst (lookup_range_tree_valid tree) \<Longrightarrow>
   monotonic_key_ranges (lookup_range_tree_to_list tree)"
  apply (induct tree)
   apply simp
  apply (clarsimp simp: monotonic_key_ranges_alt_def list_pairwise_append
                  split: prod.splits option.splits)
     apply (fastforce dest: lookup_range_tree_valid_empty lookup_range_tree_to_list_range)+
  done

lemma lookup_map_of_append_to_map_add:
  "lookup_map_of eq (xs @ ys) = lookup_map_of eq ys ++ lookup_map_of eq xs"
  unfolding map_add_def
  apply (induct xs)
   apply simp
  apply (rule ext)
  apply (clarsimp split: option.splits)
  done

lemma lookup_map_of_append_cong:
  "\<lbrakk> lookup_map_of eq xs = lookup_map_of eq xs';
     lookup_map_of eq ys = lookup_map_of eq ys'
   \<rbrakk> \<Longrightarrow> lookup_map_of eq (xs @ ys) = lookup_map_of eq (xs' @ ys')"
  by (simp add: lookup_map_of_append_to_map_add)

lemma lookup_map_of_append1_commute:
  "lookup_map_disjoint_keys eq (xs @ [y]) \<Longrightarrow>
   lookup_map_of eq (xs @ [y]) = lookup_map_of eq ([y] @ xs)"
  apply (induct xs arbitrary: y)
   apply simp
  apply (rule ext)
  apply clarify
  apply (simp add: disjnt_def lookup_map_disjoint_keys_def flip: Collect_conj_eq)
  done

lemma Cons_to_append:
  "x # xs = [x] @ xs"
  by simp

lemma lookup_map_of_append_commute:
  "lookup_map_disjoint_keys eq (xs @ ys) \<Longrightarrow>
   lookup_map_of eq (xs @ ys) = lookup_map_of eq (ys @ xs)"
  (* FIXME: cleanup... *)
  apply (induct xs arbitrary: ys)
   apply simp
  apply (subst Cons_to_append, subst append_assoc)
  apply (subst lookup_map_of_append1_commute[symmetric])
   apply (simp only: lookup_map_disjoint_keys_def)
   apply (subst list_pairwise_commute)
    apply (fastforce intro: sympI disjnt_sym)
   apply simp
  apply (rule_tac t="lookup_map_of eq (ys @ a # xs)" and s="lookup_map_of eq ((ys @ [a]) @ xs)" in subst)
   apply simp
  apply (subst append_assoc, drule meta_spec, erule meta_mp)
  apply simp
  apply (subst (asm) Cons_to_append, subst append_assoc[symmetric])
  apply (simp only: lookup_map_disjoint_keys_def)
  apply (subst list_pairwise_commute)
   apply (fastforce intro: sympI disjnt_sym)
  apply simp
  done

lemma map_add_alt_cond:
  "\<lbrakk>\<And>x. g x \<noteq> None \<Longrightarrow> \<not> cond x; \<And>x. f x \<noteq> None \<Longrightarrow> cond x\<rbrakk> \<Longrightarrow>
   f ++ g = (\<lambda>x. if cond x then f x else g x)"
  by (fastforce simp: map_add_def split: option.splits)

lemma map_add_alt_cond':
  "\<lbrakk>\<And>x. f x \<noteq> None \<Longrightarrow> \<not> cond x; \<And>x. g x \<noteq> None \<Longrightarrow> cond x\<rbrakk> \<Longrightarrow>
   f ++ g = (\<lambda>x. if cond x then g x else f x)"
  by (fastforce simp: map_add_def split: option.splits)


lemma fst_lookup_range_tree_validD:
  "fst (lookup_range_tree_valid (Node start end v l r)) \<Longrightarrow>
   fst (lookup_range_tree_valid l) \<and> fst (lookup_range_tree_valid r)"
  by (simp split: option.splits prod.splits)

lemma lookup_range_tree_Some:
  "lookup_range_tree tree k = Some ((start, end), v) \<Longrightarrow>
   fst (lookup_range_tree_valid tree) \<Longrightarrow>
   in_range (start, end) k
   \<and> (\<exists>low high. lookup_range_tree_valid tree = (True, Some (low, high))
                  \<and> low \<le> start \<and> end \<le> high)"
  apply (cases "lookup_range_tree_valid tree")
  apply clarsimp
  apply (rename_tac r, case_tac r)
   apply (fastforce dest: lookup_range_tree_valid_empty)
  apply (fastforce dest: lookup_range_tree_valid_in_range)
  done

text \<open>Conversion between RangeTrees and lookup lists\<close>

theorem lookup_range_tree_to_list_of:
  fixes tree :: "('a::linorder, 'b) RangeTree"
  shows "fst (lookup_range_tree_valid tree) \<Longrightarrow>
         lookup_range_tree tree = range_map_of (lookup_range_tree_to_list tree)"
unfolding range_map_of_def
proof (induct tree)
  case Leaf
    show ?case
      by (fastforce simp: range_map_of_def)
  next case (Node start "end" v treeL treeR)
    have valid_children:
      "fst (lookup_range_tree_valid treeL)"
      "fst (lookup_range_tree_valid treeR)"
      using Node.prems fst_lookup_range_tree_validD by auto

    have eq_children:
      "lookup_range_tree treeL = lookup_map_of in_range (lookup_range_tree_to_list treeL)"
      "lookup_range_tree treeR = lookup_map_of in_range (lookup_range_tree_to_list treeR)"
      using Node.hyps valid_children by auto

    have treeL1_disjoint:
      "lookup_map_disjoint_keys in_range (lookup_range_tree_to_list treeL @ [((start, end), v)])"
      using Node.prems
      by (fastforce dest!: lookup_range_tree_list_monotonic monotonic_key_ranges_disjoint
                    simp: disjoint_key_ranges_def lookup_map_disjoint_keys_def list_pairwise_append)

    {
      fix x :: 'a
      have lookup_list_reorder:
        "lookup_map_of in_range (lookup_range_tree_to_list (Node start end v treeL treeR)) x
         = lookup_map_of in_range
                         ([((start, end), v)]
                           @ lookup_range_tree_to_list treeL
                           @ lookup_range_tree_to_list treeR) x"
        using lookup_range_tree_to_list.simps append_assoc
              lookup_map_of_append_commute[OF treeL1_disjoint]
              lookup_map_of_append_cong[OF _ refl]
        by metis

      have branch_eq_lookup_append[symmetric]:
        "lookup_map_of in_range (lookup_range_tree_to_list treeL @ lookup_range_tree_to_list treeR) x
         = (if x < start then lookup_map_of in_range (lookup_range_tree_to_list treeL) x
                         else lookup_map_of in_range (lookup_range_tree_to_list treeR) x)"
        apply (simp only: lookup_map_of_append_to_map_add flip: eq_children)
        apply (rule map_add_alt_cond'[THEN fun_cong])
         using Node.prems
         apply (fastforce dest: lookup_range_tree_Some split: prod.splits)+
        done

      have case_ext:
        "lookup_range_tree (Node start end v treeL treeR) x
         = lookup_map_of in_range (lookup_range_tree_to_list (Node start end v treeL treeR)) x"
        apply (simp only: lookup_range_tree.simps
                          lookup_list_reorder eq_children branch_eq_lookup_append
                    flip: in_range.simps)
        by (simp only: lookup_map_of.simps append.simps)
    }
    then show ?case by auto
qed

(* Top-level rule for converting to lookup list. *)
lemma lookup_range_tree_to_list_of_gen:
  "\<lbrakk> fst (lookup_range_tree_valid tree);
     lookup_range_tree_to_list tree = binds
   \<rbrakk> \<Longrightarrow> lookup_range_tree tree = range_map_of binds
         \<and> monotonic_key_ranges binds"
  using lookup_range_tree_to_list_of
  apply (fastforce dest: lookup_range_tree_list_monotonic)
  done


subsection \<open>Domain and range\<close>

lemma dom_range_map_of:
  "dom (range_map_of xs) =
     Union (set (map (Collect o in_range o fst) xs))"
  by (induct xs; fastforce simp: range_map_of_def in_range.simps)

lemma Collect_in_range_rewrite:
  "Collect o in_range o fst = (\<lambda>((start, end), v). {start ..< end})"
  by (fastforce simp: in_range.simps)

lemma ran_add_if:
  "\<lbrakk> \<forall>x. P x \<longrightarrow> z x = None \<rbrakk>
   \<Longrightarrow> ran (\<lambda>x. if P x then y x else z x) = ran (y |` Collect P) \<union> ran z"
  by (auto simp: ran_def restrict_map_def)

text \<open>
  Key ranges are often contiguous. We can generate a more compact domain spec
  that takes this into account. We define a function, combine_contiguous_ranges,
  then evaluate it over the input keys.
\<close>
lemma atLeastLessThan_union_contiguous:
  "\<lbrakk>(l::'a::linorder) \<le> m; m \<le> u\<rbrakk> \<Longrightarrow> {l..<m} \<union> {m..<u} = {l..<u}"
  "\<lbrakk>(l::'a::linorder) \<le> m; m \<le> u\<rbrakk> \<Longrightarrow> ({l..<m} \<union> {m..<u}) \<union> x = {l..<u} \<union> x"
  "\<lbrakk>(l::'a::linorder) \<le> m; m \<le> u\<rbrakk> \<Longrightarrow> {l..<m} \<union> ({m..<u} \<union> x) = {l..<u} \<union> x"
  by (auto simp: ivl_disj_un)

(* This is the one we want to evaluate *)
fun combine_contiguous_ranges :: "('a::linorder \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list"
  where
    "combine_contiguous_ranges ((start, end) # (start', end') # xs) =
       (if end = start' then combine_contiguous_ranges ((start, end') # xs) else
          (start, end) # combine_contiguous_ranges ((start', end') # xs))"
  | "combine_contiguous_ranges xs = xs"

(* This one seems to be easier to verify *)
fun combine_contiguous_ranges_rev :: "('a::linorder \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list"
  where
    "combine_contiguous_ranges_rev ((start, end) # xs) =
       (case combine_contiguous_ranges_rev xs of
            (start', end') # xs' \<Rightarrow> if end = start' then (start, end') # xs' else
                                      (start, end) # (start', end') # xs'
          | [] \<Rightarrow> [(start, end)])"
  | "combine_contiguous_ranges_rev [] = []"

lemma combine_contiguous_ranges_both:
  "combine_contiguous_ranges xs = combine_contiguous_ranges_rev xs"
  apply (induct xs rule: length_induct)
  apply (case_tac xs)
   apply clarsimp
  apply (rename_tac xs')
  apply (case_tac xs')
   apply clarsimp
  apply (clarsimp split: list.splits)
  done

lemma combine_contiguous_ranges_rev_head_helper:
  "\<lbrakk> combine_contiguous_ranges_rev ks = ((start', end') # ks_tl');
     monotonic_key_ranges kvs; ks = map fst kvs; ks = (start, end) # ks_tl
   \<rbrakk> \<Longrightarrow>
   start = start' \<and> end \<le> end'"
  (* FIXME: cleanup *)
  apply (induct kvs arbitrary: ks start "end" start' end' ks_tl ks_tl'
                rule: monotonic_key_ranges.induct)
    apply (clarsimp simp del: combine_contiguous_ranges_rev.simps)
    apply (drule_tac x="(start', end') # map fst kvs" in meta_spec)
    apply (drule_tac x="start'" in meta_spec)
    apply (drule_tac x="end'" in meta_spec)
    apply (clarsimp simp del: combine_contiguous_ranges_rev.simps)
    apply (simp only: combine_contiguous_ranges_rev.simps(1)[where xs = "_#_"])
    apply (fastforce dest: monotonic_ranges_each_valid split: list.splits if_splits)
   apply auto
  done

lemma combine_contiguous_ranges_rev_correct:
  "monotonic_key_ranges xs \<Longrightarrow>
   Union (set (map (Collect o in_range o fst) xs))
    = Union (set (map (Collect o in_range) (combine_contiguous_ranges_rev (map fst xs))))"
  (* FIXME: cleanup *)
  apply (induct xs rule: monotonic_key_ranges.induct)
    subgoal
      supply combine_contiguous_ranges_rev.simps[simp del]
      apply (clarsimp simp: combine_contiguous_ranges_rev.simps(1)[where xs="_#_"]
                      split: list.splits)
      apply (drule(1) combine_contiguous_ranges_rev_head_helper)
        apply simp
       apply (rule refl)
      apply (fastforce dest: atLeastLessThan_union_contiguous monotonic_ranges_each_valid)
      done
   apply auto
  done

lemmas combine_contiguous_ranges_correct =
  combine_contiguous_ranges_rev_correct[folded combine_contiguous_ranges_both]

text \<open>
  @{const ran} is simpler. Every entry that can be a lookup result
  (i.e. its key range is nonempty) is part of the range.
\<close>

lemma ran_range_map_of:
  "\<lbrakk> monotonic_key_ranges xs \<rbrakk> \<Longrightarrow>
   ran (range_map_of xs) = set (filter (\<lambda>((start, end), v). start < end) xs)"
  apply (induct xs)
   apply (fastforce simp: range_map_of_def)
  apply (clarsimp simp: range_map_of_def monotonic_key_ranges_alt_def list_all_iff)
  apply (subst ran_add_if)
   apply (subst not_in_domIff[where f="lookup_map_of _ _"])
   apply (subst dom_range_map_of[unfolded range_map_of_def])
   apply (fastforce simp: disjnt_def in_range.simps)
  apply (clarsimp simp: ran_def restrict_map_def in_range.simps)
  apply (drule sym)
  by auto


subsection \<open>Generating lookup rules\<close>

lemma lookup_map_of_single:
  "\<lbrakk> lookup_map_disjoint_keys eq binds;
     (k, v) \<in> set binds; eq k x \<rbrakk>
   \<Longrightarrow> lookup_map_of eq binds x = Some (k, v)"
  by (induct binds;
      fastforce simp: lookup_map_disjoint_keys_def disjnt_def)

lemma range_map_of_single':
  "\<lbrakk> disjoint_key_ranges binds;
     ((start, end), v) \<in> set binds; in_range (start, end) k \<rbrakk>
   \<Longrightarrow> range_map_of binds k = Some ((start, end), v)"
  unfolding range_map_of_def disjoint_key_ranges_def
  by (fastforce intro: lookup_map_of_single)

lemmas range_map_of_single = range_map_of_single'[unfolded in_range.simps, OF _ _ conjI]

lemma range_map_of_lookups__gen_all':
  "\<lbrakk> m = range_map_of binds; disjoint_key_ranges binds \<rbrakk> \<Longrightarrow>
   list_all (\<lambda>((start, end), v). \<forall>k. in_range (start, end) k = (m k = Some ((start, end), v))) binds"
  by (fastforce simp: list_all_iff intro: range_map_of_single' dest: range_map_of_Some')

lemmas range_map_of_lookups__gen_all =
  range_map_of_lookups__gen_all'
    [OF _ monotonic_key_ranges_disjoint, simplified in_range.simps]

text \<open>
  We also generate equations for the useful special case of
  looking up the start key of each range.
\<close>

lemma range_map_of_start:
  "\<lbrakk> disjoint_key_ranges binds; ((start, end), v) \<in> set binds; start < end \<rbrakk>
   \<Longrightarrow> range_map_of binds start = Some ((start, end), v)"
  by (fastforce simp: in_range.simps intro: range_map_of_single)

lemma range_map_of_start_lookups__gen_all':
  "\<lbrakk> m = range_map_of binds; disjoint_key_ranges binds \<rbrakk> \<Longrightarrow>
   list_all (\<lambda>((start, end), v). start < end \<longrightarrow> m start = Some ((start, end), v)) binds"
  by (fastforce simp: list_all_iff intro: range_map_of_start)

lemmas range_map_of_start_lookups__gen_all =
  range_map_of_start_lookups__gen_all'[OF _ monotonic_key_ranges_disjoint]

lemmas list_all_dest = FastMap.list_all_dest


subsection \<open>Setup for automation\<close>

definition quote :: "'a \<Rightarrow> 'a"
  where unquote: "quote x \<equiv> x"
lemma hold_quote:
  "quote x = quote x" by simp

text \<open>Like @{thm spec} without eta expansion\<close>
lemma spec_FO:
  "All P \<Longrightarrow> P x" by simp
ML_val \<open>@{assert} (not (Thm.eq_thm_prop (@{thm spec}, @{thm spec_FO})))\<close>

text \<open>
  Install tree lookup simp rules that don't depend on
  @{thm if_cong}/@{thm if_weak_cong} being set up correctly.
\<close>
lemma lookup_range_tree_simps':
  "lookup_range_tree Leaf x = None"
  "\<lbrakk> start \<le> x; x < end \<rbrakk> \<Longrightarrow>
     lookup_range_tree (Node start end v l r) x = Some ((start, end), v)"
  "\<lbrakk> x < start \<rbrakk> \<Longrightarrow>
     lookup_range_tree (Node start end v l r) x = lookup_range_tree l x"
  "\<lbrakk> start \<le> end; end \<le> x \<rbrakk> \<Longrightarrow>
     lookup_range_tree (Node start end v l r) x = lookup_range_tree r x"
  by auto

end

declare RangeMap.lookup_range_tree_simps'[simp]

ML \<open>
structure RangeMap = struct

val $$ = uncurry Thm.apply;
infix 9 $$;

(* Like "OF", but first order, and resolving thms must not have extra prems *)
fun FO_OF (thm, []) = thm
  | FO_OF (thm, res::ress) = let
      val (prem1, _) = Thm.dest_implies (Thm.cprop_of thm);
      val inst = Thm.first_order_match (prem1, Thm.cprop_of res);
      val thm' = Thm.instantiate inst thm;
      in FO_OF (Thm.implies_elim thm' res, ress) end;
infix 0 FO_OF;

(* Applies conversion to a whole thm *)
fun conv_prop conv thm =
  let val next = conv (Thm.cprop_of thm);
  in if Thm.is_reflexive next then thm else Thm.equal_elim next thm end;

(* Like HOLogic.mk_list but for cterms *)
fun mk_list ctxt T = let
  val Nil = Const (@{const_name Nil}, HOLogic.listT T)
            |> Thm.cterm_of ctxt;
  val Cons = Const (@{const_name Cons}, T --> HOLogic.listT T --> HOLogic.listT T)
             |> Thm.cterm_of ctxt;
  in fn xs => fold_rev (fn x => fn xs => Cons $$ x $$ xs) xs Nil end;

(* Build RangeTree cterm *)
fun build_range_tree ctxt kT vT = let
  val treeT = Type (@{type_name RangeMap.RangeTree}, [kT, vT]);
  val leaf = Const (@{const_name RangeMap.Leaf}, treeT) |> Thm.cterm_of ctxt;
  val node = Const (@{const_name RangeMap.Node}, kT-->kT-->vT-->treeT-->treeT-->treeT)
             |> Thm.cterm_of ctxt;
  fun build [] = leaf
    | build kvs = let
          val (kvs1, ((ks, ke), v) :: kvs2) = chop (length kvs div 2) kvs;
          in node $$ ks $$ ke $$ v $$ build kvs1 $$ build kvs2
          end;
  in build end;

(* Build lookup list cterm *)
fun build_lookup_list ctxt kT vT = let
  val key_rangeT = HOLogic.mk_prodT (kT, kT);
  val key_Pair = Const (@{const_name Pair}, kT --> kT --> key_rangeT)
                 |> Thm.cterm_of ctxt;
  val elemT = HOLogic.mk_prodT (key_rangeT, vT);
  val elem_Pair = Const (@{const_name Pair}, key_rangeT --> vT --> elemT)
                  |> Thm.cterm_of ctxt;
  fun elem ((ks, ke), v) = elem_Pair $$ (key_Pair $$ ks $$ ke) $$ v;
  in mk_list ctxt elemT o map elem end;

(* Quote all keys and values to prevent unwanted rewriting *)
fun quote_elems ctxt kT vT =
  let fun quote T = Const (@{const_name RangeMap.quote}, T-->T) |> Thm.cterm_of ctxt;
  in map (fn ((ks, ke), v) => ((quote kT $$ ks, quote kT $$ ke), quote vT $$ v)) end;

(* Check whether conversion is valid and its result lies in a given list *)
fun is_conv_to terms (src, conv) =
      Thm.term_of (Thm.lhs_of conv) aconv Thm.term_of src andalso
      exists (fn term => Thm.term_of (Thm.rhs_of conv) aconv term) terms;

(* Checking generated lookup rules *)
fun check_generated_thms desc templates thms =
      if length thms <> length templates then
        raise THM ("RangeMap internal error: generated " ^ string_of_int (length thms) ^
                   " thms for " ^ desc ^ ", but expected " ^ string_of_int (length templates),
                   0, thms)
      else case filter (fn (thm, template) => not (Thm.prop_of thm aconv template))
                       (thms ~~ templates) of
               [] => ()
             | bads => raise THM ("RangeMap internal error: wrong format for " ^ desc,
                                  0, map fst bads);

(* Common FP_Eval configuration. We use hold_quote everywhere to avoid
   descending into user input terms *)
fun fp_eval_conv' ctxt rules congs =
  FP_Eval.eval_conv ctxt (FP_Eval.make_rules rules (congs @ @{thms RangeMap.hold_quote}));

fun unquote_conv ctxt = FP_Eval.eval_conv ctxt (FP_Eval.make_rules @{thms RangeMap.unquote} []);
val unquote_thm = Conv.fconv_rule o unquote_conv;

(* Helper for targeted beta reduction *)
fun beta_conversion_thm conv_where =
      conv_prop (conv_where (Thm.beta_conversion false));

(* Pre-compute key comparison results.
   This allows us to report errors early and avoid cluttering
   other proofs with the user-supplied key ordering semantics. *)
fun compare_keys ctxt kT solver elems =
  let val but_last = split_last #> fst;
      val elem_pairs = if null elems then [] else but_last elems ~~ tl elems;
      val cmpT = kT --> kT --> @{typ bool};
      val eqT = Thm.cterm_of ctxt (Const (@{const_name HOL.eq}, cmpT));
      val lessT = Thm.cterm_of ctxt (Const (@{const_name less}, cmpT));
      val less_eqT = Thm.cterm_of ctxt (Const (@{const_name less_eq}, cmpT));

      (* Monotonicity: required to be True always *)
      val monotonic_cmps =
              map (fn ((ks, ke), _) => less_eqT $$ ks $$ ke) elems
            @ map (fn (((_, ke), _), ((ks', _), _)) => less_eqT $$ ke $$ ks') elem_pairs;

      val monotonic_results = map solver monotonic_cmps;
      val _ = case filter (not o is_conv_to [@{term True}])
                          (monotonic_cmps ~~ monotonic_results) of
                  [] => ()
                | ((_, bad)::_) =>
                    raise THM ("RangeMap: failed to solve key constraint", 0, [bad]);

      (* Determine whether ranges are adjacent.
         Allowed to be False, used for generating compact domain thm. *)
      val adj_eq_cmps =
            map (fn (((_, ke), _), ((ks', _), _)) => eqT $$ ke $$ ks') elem_pairs;

      val adj_eq_results = map solver adj_eq_cmps;
      val _ = case filter (not o is_conv_to [@{term True}, @{term False}])
                          (adj_eq_cmps ~~ adj_eq_results) of
                  [] => ()
                | ((_, bad)::_) =>
                    raise THM ("RangeMap: failed to solve key constraint", 0, [bad]);

      (* Determine whether each key range is nonempty.
         Allowed to be False, used for generating range thm. *)
      val nonempty_cmps =
              map (fn ((ks, ke), _) => lessT $$ ks $$ ke) elems;

      val nonempty_results = map solver nonempty_cmps;
      val _ = case filter (not o is_conv_to [@{term True}, @{term False}])
                          (nonempty_cmps ~~ nonempty_results) of
                  [] => ()
                | ((_, bad)::_) =>
                    raise THM ("RangeMap: failed to solve key range emptyiness", 0, [bad]);

  in (monotonic_results, adj_eq_results, nonempty_results) end;

(*** Generate various theorems and conversions ***)

fun gen__lookup_range_tree_valid ctxt tree_const tree_def key_cmps =
  let val prop =
        @{mk_term "Trueprop (fst (RangeMap.lookup_range_tree_valid ?tree))" (tree)} tree_const
        |> Thm.cterm_of ctxt;
      val rules = FP_Eval.make_rules
                    (@{thms RangeMap.lookup_range_tree_valid.simps
                            simp_thms prod.sel prod.case option.case Let_def if_True if_False}
                     @ [tree_def] @ key_cmps)
                    @{thms if_weak_cong FP_Eval.let_weak_cong' option.case_cong_weak
                           RangeMap.hold_quote};
  in Goal.init prop
     |> (FP_Eval.eval_tac ctxt rules 1
         THEN resolve_tac ctxt @{thms TrueI} 1)
     |> Seq.hd
     |> Goal.finish ctxt
  end;

fun gen__lookup_range_tree_to_list ctxt tree_const tree_def list_const list_def =
  let val prop =
        @{mk_term "Trueprop (RangeMap.lookup_range_tree_to_list ?tree = ?list)" (tree, list)}
          (tree_const, list_const)
        |> Thm.cterm_of ctxt;
      val rules = FP_Eval.make_rules
                    (@{thms RangeMap.lookup_range_tree_to_list.simps append.simps}
                     @ [list_def, tree_def])
                    @{thms RangeMap.hold_quote};
  in Goal.init prop
     |> (FP_Eval.eval_tac ctxt rules 1
         THEN resolve_tac ctxt @{thms refl} 1)
     |> Seq.hd
     |> Goal.finish ctxt
  end;

fun gen__range_lookups ctxt tree_list_lookup_eq_thm list_def list_monotonic_thm =
  (@{thm RangeMap.range_map_of_lookups__gen_all}
      FO_OF [tree_list_lookup_eq_thm, list_monotonic_thm])
  |> Conv.fconv_rule (fp_eval_conv' ctxt
                        (@{thms RangeMap.list_all_dest prod.case} @ [list_def]) [])
  |> HOLogic.conj_elims ctxt
  |> map (fn t => (@{thm RangeMap.spec_FO} FO_OF [t])
                  |> beta_conversion_thm Conv.arg_conv (* beta reduce result of spec thm *))
  |> map (Conv.fconv_rule (fp_eval_conv' ctxt @{thms RangeMap.in_range.simps} []));

fun expected__range_lookups tree_const elems =
  elems
  |> map (fn ((ks, ke), v) =>
            @{mk_term "Trueprop ((?s \<le> ?x \<and> ?x < ?e)
                                 = (RangeMap.lookup_range_tree ?tree ?x = Some ((?s, ?e), ?v)))"
                       (tree, s, e, v)}
              (tree_const, Thm.term_of ks, Thm.term_of ke, Thm.term_of v));

fun gen__start_lookups ctxt
      tree_list_lookup_eq_thm list_def list_monotonic_thm key_range_nonempty_thms =
  (@{thm RangeMap.range_map_of_start_lookups__gen_all}
      FO_OF [tree_list_lookup_eq_thm, list_monotonic_thm])
  |> Conv.fconv_rule (fp_eval_conv' ctxt
                        (@{thms RangeMap.list_all_dest prod.case simp_thms}
                         @ [list_def] @ key_range_nonempty_thms)
                        [])
  |> HOLogic.conj_elims ctxt;

fun expected__start_lookups tree_const elems key_range_nonempty_thms =
  elems ~~ key_range_nonempty_thms
  |> filter (fn (_, cmp) => Thm.term_of (Thm.rhs_of cmp) = @{term True})
  |> map fst
  |> map (fn ((ks, ke), v) =>
            @{mk_term "Trueprop (RangeMap.lookup_range_tree ?tree ?s = Some ((?s, ?e), ?v))"
                       (tree, s, e, v)}
              (tree_const, Thm.term_of ks, Thm.term_of ke, Thm.term_of v));

fun gen__domain_thm ctxt tree_const tree_list_lookup_eq_thm =
  @{mk_term "dom (RangeMap.lookup_range_tree ?tree)" (tree)} tree_const
  |> Thm.cterm_of ctxt
  |> fp_eval_conv' ctxt ([tree_list_lookup_eq_thm] @ @{thms RangeMap.dom_range_map_of}) [];

fun gen__compact_domain_thm ctxt domain_thm list_def list_monotonic_thm key_adj_equal_thms =
  domain_thm
  |> Conv.fconv_rule
      ((* First, invoke @{const RangeMap.combine_contiguous_ranges} *)
       (fp_eval_conv' ctxt
          [(@{thm RangeMap.combine_contiguous_ranges_correct} FO_OF [list_monotonic_thm])] [])
       then_conv
       (* Now evaluate combine_contiguous_ranges. We can't expand the
          lookup list definition before using "combine_contiguous_ranges_correct",
          so this is split into a subsequent eval step. *)
       (fp_eval_conv' ctxt
                ([list_def]
                 @ @{thms RangeMap.combine_contiguous_ranges.simps prod.case list.map prod.sel
                          rel_simps simp_thms if_True if_False
                          RangeMap.Collect_in_range_atLeastLessThan o_apply}
                 @ key_adj_equal_thms)
                @{thms if_weak_cong})
      );

fun gen__range_thm ctxt
      tree_const tree_list_lookup_eq_thm list_def list_monotonic_thm key_range_nonempty_thms =
  @{mk_term "ran (RangeMap.lookup_range_tree ?tree)" (tree)} tree_const
  |> Thm.cterm_of ctxt
  |> (fp_eval_conv' ctxt
            ([tree_list_lookup_eq_thm]
             @ [@{thm RangeMap.ran_range_map_of} FO_OF [list_monotonic_thm]])
            []
      then_conv
      fp_eval_conv' ctxt
            ([list_def] @ key_range_nonempty_thms
             @ @{thms filter.simps prod.case simp_thms if_True if_False})
            @{thms if_weak_cong prod.case_cong_weak}
      (* if range turns out to contain all elements, collapse back into list *)
      then_conv
      fp_eval_conv' ctxt [Thm.symmetric list_def] []
     );

(*** User interface ***)

(* Choosing names for the const and its theorems. The constant will be named with
   map_name; Local_Theory.define may also add extra names (e.g. <map_name>_def) *)
type name_opts = {
    tree_const: binding,
    tree_def: binding,
    list_const: binding,
    list_def: binding,
    tree_valid_thm: binding,
    tree_to_list_thm: binding,
    tree_list_lookup_eq_thm: binding,
    list_monotonic_thm: binding,
    range_lookup_thms: binding,
    start_lookup_thms: binding,
    domain_thm: binding,
    compact_domain_thm: binding,
    range_thm: binding
};

fun name_opts_default (base_name: string): name_opts =
  let val qual = Binding.qualify_name true (Binding.name base_name);
  in {
    tree_const = qual "tree",
    tree_def = Thm.def_binding (qual "tree"),
    list_const = qual "list",
    list_def = Thm.def_binding (qual "list"),
    tree_valid_thm = qual "tree_valid",
    tree_to_list_thm = qual "tree_to_list",
    tree_list_lookup_eq_thm = qual "tree_list_lookup_eq",
    list_monotonic_thm = qual "list_monotonic",
    range_lookup_thms = qual "lookups",
    start_lookup_thms = qual "start_lookups",
    domain_thm = qual "domain",
    compact_domain_thm = qual "domain_compact",
    range_thm = qual "range"
  } end;

(* Top level *)
fun define_map
      (name_opts: name_opts)
      (elems: ((cterm * cterm) * cterm) list)
      (kT: typ)
      (vT: typ)
      (key_cmp_solver: conv)
      ctxt =
  let
    fun msg x = "RangeMap: " ^ Binding.print (#tree_const name_opts) ^ ": " ^ x;
    val tracing_msg = tracing o msg;

    (* check input types *)
    val _ = elems
            |> app (fn ((ks, ke), v) =>
                  if Thm.typ_of_cterm ks <> kT
                  then raise TYPE (msg "key has wrong type", [kT], [Thm.term_of ks])
                  else if Thm.typ_of_cterm ke <> kT
                  then raise TYPE (msg "key has wrong type", [kT], [Thm.term_of ke])
                  else if Thm.typ_of_cterm v <> vT
                  then raise TYPE (msg "value has wrong type", [vT], [Thm.term_of v])
                  else ());

    (* quote all input keys and values *)
    val quoted_elems = quote_elems ctxt kT vT elems;
    (* unquote when computing key comparisons *)
    val quoted_key_cmp_solver = unquote_conv ctxt then_conv key_cmp_solver;

    (* less verbose "notes"; also unquotes user input *)
    fun notes ctxt thmss =
          Local_Theory.notes
            (map (fn (bind, thms) => ((bind, []), [(map (unquote_thm ctxt) thms, [])])) thmss) ctxt
          |> snd;

    val _ = tracing_msg "evaluating key comparisons";
    val start = Timing.start ();
    val (key_mono_thms, key_adj_eq_thms, key_range_nonempty_thms) =
           compare_keys ctxt kT quoted_key_cmp_solver quoted_elems;
    val _ = tracing_msg ("done: " ^ Timing.message (Timing.result start));

    val _ = tracing_msg "defining tree";
    val start = Timing.start ();
    val quoted_tree = build_range_tree ctxt kT vT quoted_elems;
    val unquote_tree_eqn = unquote_conv ctxt quoted_tree;
    val unquoted_tree = Thm.rhs_of unquote_tree_eqn;
    val ((tree_const, (_, tree_def)), ctxt) =
          ctxt |> Local_Theory.define
              ((#tree_const name_opts, NoSyn),
               ((#tree_def name_opts, []), Thm.term_of unquoted_tree));
    val quoted_tree_def = Thm.transitive tree_def (Thm.symmetric unquote_tree_eqn);
    val _ = tracing_msg ("done: " ^ Timing.message (Timing.result start));

    val _ = tracing_msg "defining lookup list";
    val start = Timing.start ();
    val quoted_list = build_lookup_list ctxt kT vT quoted_elems;
    val unquote_list_eqn = unquote_conv ctxt quoted_list;
    val unquoted_list = Thm.rhs_of unquote_list_eqn;
    val ((list_const, (_, list_def)), ctxt) =
          ctxt |> Local_Theory.define
              ((#list_const name_opts, NoSyn),
               ((#list_def name_opts, []), Thm.term_of unquoted_list));
    val quoted_list_def = Thm.transitive list_def (Thm.symmetric unquote_list_eqn);
    val _ = tracing_msg ("done: " ^ Timing.message (Timing.result start));

    val _ = tracing_msg "proving tree validity";
    val start = Timing.start ();
    val tree_valid_thm =
          gen__lookup_range_tree_valid ctxt tree_const quoted_tree_def key_mono_thms;
    val ctxt = notes ctxt
          [(#tree_valid_thm name_opts, [tree_valid_thm])];
    val _ = tracing_msg ("done: " ^ Timing.message (Timing.result start));

    val _ = tracing_msg "proving tree and list correspondence";
    val start = Timing.start ();
    val tree_to_list_thm =
          gen__lookup_range_tree_to_list ctxt
                tree_const quoted_tree_def
                list_const quoted_list_def;
    val list_properties =
          @{thm RangeMap.lookup_range_tree_to_list_of_gen}
            FO_OF [tree_valid_thm, tree_to_list_thm];
    val [tree_list_lookup_eq_thm, list_monotonic_thm] =
          HOLogic.conj_elims ctxt list_properties;
    val ctxt = notes ctxt
          [(#tree_to_list_thm name_opts, [tree_to_list_thm]),
           (#tree_list_lookup_eq_thm name_opts, [tree_list_lookup_eq_thm]),
           (#list_monotonic_thm name_opts, [list_monotonic_thm])];
    val _ = tracing_msg ("done: " ^ Timing.message (Timing.result start));

    val _ = tracing_msg "generating lookup rules";
    val start = Timing.start ();
    val tree_range_lookups =
          if null elems then [] else
          gen__range_lookups ctxt tree_list_lookup_eq_thm quoted_list_def list_monotonic_thm
          |> tap (check_generated_thms "range lookup rule"
                    (expected__range_lookups tree_const quoted_elems));
    val tree_start_lookups =
          if null elems then [] else
          gen__start_lookups ctxt
              tree_list_lookup_eq_thm quoted_list_def list_monotonic_thm key_range_nonempty_thms
          |> tap (check_generated_thms "start lookup rule"
                    (expected__start_lookups tree_const quoted_elems key_range_nonempty_thms));
    val ctxt = notes ctxt
          [(#range_lookup_thms name_opts, tree_range_lookups),
           (#start_lookup_thms name_opts, tree_start_lookups)];
    val _ = tracing_msg ("done: " ^ Timing.message (Timing.result start));

    val _ = tracing_msg "calculating domain and range";
    val domain_thm = gen__domain_thm ctxt tree_const tree_list_lookup_eq_thm;
    val compact_domain_thm =
          gen__compact_domain_thm ctxt
              domain_thm quoted_list_def list_monotonic_thm key_adj_eq_thms;
    val domain_thm' = (* remove internal "in_range" *)
          domain_thm
          |> Conv.fconv_rule (fp_eval_conv' ctxt @{thms RangeMap.Collect_in_range_rewrite} []);
    val range_thm =
          gen__range_thm ctxt tree_const
              tree_list_lookup_eq_thm quoted_list_def list_monotonic_thm key_range_nonempty_thms;
    val ctxt = notes ctxt
          [(#domain_thm name_opts, [domain_thm']),
           (#compact_domain_thm name_opts, [compact_domain_thm]),
           (#range_thm name_opts, [range_thm])];
    val _ = tracing_msg ("done: " ^ Timing.message (Timing.result start));
  in ctxt end;

end;
\<close>

end