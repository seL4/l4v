(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory ListLibLemmas
imports List_Lib LemmaBucket
begin

(* This theory contains various list results that
are used in proofs related to the abstract cdt_list.*)

(* Sorting a list given a partial ordering, where
        elements are only necessarily comparable if
        relation R holds between them. *)
locale partial_sort =
  fixes less :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"

  assumes all_comp: "\<And>x y. R x y \<Longrightarrow> (less x y \<or> less y x)"

  (*This is only necessary to guarantee the uniqueness of
    sorted lists. *)
  assumes antisym: "\<And>x y. R x y \<Longrightarrow> less x y \<and> less y x \<Longrightarrow> x = y"

  assumes trans: "\<And>x y z. less x y \<Longrightarrow>  less y z \<Longrightarrow> less x z"

begin

primrec pinsort :: " 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
   "pinsort x [] = [x]" |
   "pinsort x (y#ys) = (if (less x y) then (x#y#ys) else y#(pinsort x ys))"

inductive psorted :: "'a list \<Rightarrow> bool" where
  Nil [iff]: "psorted []"
| Cons: "\<forall>y\<in>set xs. less x y \<Longrightarrow> psorted xs \<Longrightarrow> psorted (x # xs)"

definition R_set where
"R_set S \<equiv> \<forall>x y. x \<in> S \<longrightarrow> y \<in> S \<longrightarrow> R x y"

abbreviation R_list where
"R_list xs \<equiv> R_set (set xs)"

definition psort :: "'a list \<Rightarrow> 'a list" where
"psort xs = foldr pinsort xs []"

end

context partial_sort begin

lemma psorted_Cons: "psorted (x#xs) = (psorted xs & (\<forall> y \<in> set xs. less x y))"
  apply (rule iffI)
  apply (erule psorted.cases,simp)
   apply clarsimp
  apply (rule psorted.Cons,clarsimp+)
  done

lemma psorted_distinct_set_unique:
assumes "psorted xs" "distinct xs" "psorted ys" "distinct ys" "set xs = set ys"
        "R_list xs"
shows "xs = ys"
proof -
  from assms have 1: "length xs = length ys" by (auto dest!: distinct_card)
  from assms show ?thesis
  proof(induct rule:list_induct2[OF 1])
    case 1 show ?case by simp
  next
    case 2 thus ?case
    by (simp add: psorted_Cons R_set_def)
         (metis Diff_insert_absorb antisym insertE insert_iff)
  qed
qed


lemma pinsort_set: "set (pinsort a xs) = insert a (set xs)"
  apply (induct xs)
  apply simp
  apply simp
  apply blast
  done

lemma all_comp': "R x y \<Longrightarrow> \<not>less x y \<Longrightarrow> less y x"
  apply (cut_tac x=x and y=y in all_comp,simp+)
  done

lemma pinsort_sorted: "R_set (insert a (set xs)) \<Longrightarrow> psorted xs \<Longrightarrow> psorted (pinsort a xs)"
  apply (induct xs arbitrary: a)
  apply (simp add: psorted_Cons)
  apply (simp add: psorted_Cons)
  apply clarsimp
  apply (simp add: pinsort_set)
  apply (intro impI conjI)
    apply (intro ballI)
    apply (drule_tac x=x in bspec)
     apply simp
    apply (frule(1) trans)
    apply simp
   apply (simp add: R_set_def)
  apply (rule all_comp')
   apply (simp add: R_set_def)
  apply simp
  done

lemma psort_set: "set (psort xs) = set xs"
  apply (simp add: psort_def)
  apply (induct xs)
   apply simp
  apply (simp add: pinsort_set)
  done

lemma psort_psorted: "R_list xs \<Longrightarrow> psorted (psort xs)"
  apply (simp add: psort_def)
  apply (induct xs)
   apply simp
  apply simp
  apply (cut_tac xs =xs in psort_set)
  apply (simp add: psort_def)
  apply (rule pinsort_sorted)
   apply simp
  apply (simp add: R_set_def)
  done


lemma insort_length: "length (pinsort a xs) = Suc (length xs)"
  apply (induct xs)
  apply simp
  apply simp
  done

lemma psort_length: "length (psort xs) = length xs"
  apply (simp add: psort_def)
  apply (induct xs)
   apply simp
  apply simp
  apply (simp add: insort_length)
  done

lemma pinsort_distinct: "\<lbrakk>a \<notin> set xs; distinct xs\<rbrakk>
       \<Longrightarrow> distinct (pinsort a xs)"
  apply (induct xs)
  apply simp
  apply (clarsimp simp add: pinsort_set)
  done

lemma psort_distinct: "distinct xs \<Longrightarrow> distinct (psort xs)"
  apply (simp add: psort_def)
  apply (induct xs)
   apply simp
  apply simp
  apply (rule pinsort_distinct)
   apply (fold psort_def)
   apply (simp add: psort_set)+
  done


lemma in_can_split: "y \<in> set list \<Longrightarrow> \<exists>ys xs. list = xs @ (y # ys)"
  apply (induct list)
   apply simp
  apply clarsimp
  apply (elim disjE)
   apply simp
   apply force
  apply simp
  apply (elim exE)
  apply simp
  apply (rule_tac x=ys in exI)
  apply force
  done

lemma lsorted_sorted:
assumes lsorted: "\<And>x y xs ys . list = xs @ (x # y # ys) \<Longrightarrow> less x y"
shows "psorted list"
  apply (insert lsorted)
  apply atomize
  apply simp
  apply (induct list)
   apply simp
  apply (simp add: psorted_Cons)
  apply (rule context_conjI)
   apply (erule meta_mp)
   apply clarsimp
   apply (drule_tac x="a#xs" in spec)
   apply (drule_tac x=x in spec)
   apply (drule_tac x=y in spec)
   apply (erule mp)
   apply force
  apply (intro ballI)
  apply clarsimp
  apply (drule in_can_split)
  apply (elim exE)
  apply (drule_tac x="[]" in spec)
  apply simp
  apply (case_tac xs)
   apply simp
  apply (clarsimp simp add: psorted_Cons)
  apply (blast intro: trans)
  done


lemma psorted_set: "finite A \<Longrightarrow> R_set A \<Longrightarrow> \<exists>!xs. set xs = A \<and> psorted xs \<and> distinct xs"
  apply (drule finite_distinct_list)
  apply clarify
  apply (rule_tac a="psort xs" in ex1I)
   apply (auto simp: psorted_distinct_set_unique psort_set psort_psorted psort_distinct)
done

end


text \<open>These list operations roughly correspond to cdt
        operations.\<close>

lemma after_can_split: "after_in_list list x = Some y \<Longrightarrow> \<exists>ys xs. list = xs @ (x # y # ys)"
  apply (induct list x rule: after_in_list.induct)
  apply simp+
  apply (simp split: if_split_asm)
   apply force
  apply (elim exE)
  apply simp
  apply (rule_tac x="ys" in exI)
  apply simp
  done

lemma distinct_inj_middle: "distinct list \<Longrightarrow> list = (xa @ x # xb) \<Longrightarrow> list = (ya @ x # yb) \<Longrightarrow> xa = ya \<and> xb = yb"
  apply (induct list arbitrary: xa ya)
  apply simp
  apply clarsimp
  apply (case_tac "xa")
   apply simp
   apply (case_tac "ya")
    apply simp
   apply clarsimp
  apply clarsimp
  apply (case_tac "ya")
   apply (simp (no_asm_simp))
   apply simp
  apply clarsimp
  done


lemma after_can_split_distinct:
  "distinct list \<Longrightarrow> after_in_list list x = Some y \<Longrightarrow> \<exists>!ys. \<exists>!xs. list = xs @ (x # y # ys)"
  apply (frule after_can_split)
  apply (elim exE)
  apply (rule ex1I)
   apply (rule ex1I)
    apply assumption
   apply simp
  apply (elim ex1E)
  apply (thin_tac "\<forall>x. P x" for P)
  apply (frule_tac yb="y#ysa" in distinct_inj_middle,assumption+)
  apply simp
  done


lemma after_ignore_head: "x \<notin> set list \<Longrightarrow> after_in_list (list @ list') x = after_in_list list' x"
  apply (induct list x rule: after_in_list.induct)
  apply simp
   apply simp
   apply (case_tac list',simp+)
  done


lemma after_distinct_one_sibling: "distinct list \<Longrightarrow> list = xs @ x # y # ys \<Longrightarrow> after_in_list list x = Some y"
  apply (induct xs)
  apply simp
  apply simp
  apply clarsimp
  apply (subgoal_tac "after_in_list ((a # xs) @ (x # y # ys)) x = after_in_list (x # y # ys) x")
   apply simp
  apply (rule after_ignore_head)
  apply simp
  done


lemma (in partial_sort) after_order_sorted:
assumes after_order: "\<And>x y. after_in_list list x = Some y \<Longrightarrow> less x y"
assumes distinct: "distinct list"
shows "psorted list"
  apply (rule lsorted_sorted)
  apply (rule after_order)
  apply (erule after_distinct_one_sibling[OF distinct])
  done

lemma hd_not_after_in_list:
  "\<lbrakk>distinct xs; x \<notin> set xs\<rbrakk> \<Longrightarrow> after_in_list (x # xs) a \<noteq> Some x"
  apply (induct xs a rule: after_in_list.induct)
    apply simp+
  apply fastforce
  done

lemma after_in_list_inj:
  "\<lbrakk>distinct list; after_in_list list a = Some x; after_in_list list b = Some x\<rbrakk>
    \<Longrightarrow> a = b"
  apply(induct list)
   apply(simp)
  apply(simp)
  apply(case_tac "a=aa")
   apply(case_tac list, simp)
   apply(simp add: hd_not_after_in_list split: if_split_asm)
  apply(case_tac list, simp)
  apply(simp add: hd_not_after_in_list split: if_split_asm)
  done

lemma list_replace_ignore:"a \<notin> set list \<Longrightarrow> list_replace list a b = list"
  apply (simp add: list_replace_def)
  apply (induct list,clarsimp+)
  done

lemma list_replace_empty[simp]: "list_replace [] a b = []"
  by (simp add: list_replace_def)

lemma list_replace_empty2[simp]:
  "(list_replace list a b = []) = (list = [])"
  by (simp add: list_replace_def)

lemma after_in_list_list_replace: "\<lbrakk>p \<noteq> dest; p \<noteq> src;
         after_in_list list p = Some src\<rbrakk>
        \<Longrightarrow> after_in_list (list_replace list src dest) p = Some dest"
  apply (simp add: list_replace_def)
  apply (induct list)
   apply simp+
  apply (case_tac list)
   apply simp+
  apply (intro conjI impI,simp+)
  done

lemma replace_list_preserve_after: "dest \<notin> set list \<Longrightarrow> distinct list \<Longrightarrow>  after_in_list (list_replace list src dest) dest = after_in_list list src"
  apply (simp add: list_replace_def)
  apply (induct list src rule: after_in_list.induct)
    apply (simp+)
  apply fastforce
  done

lemma replace_list_preserve_after': "\<lbrakk>p \<noteq> dest; p \<noteq> src;
         after_in_list list p \<noteq> Some src\<rbrakk>
        \<Longrightarrow> after_in_list (list_replace list src dest) p = after_in_list list p"
  apply (simp add: list_replace_def)
  apply (induct list p rule: after_in_list.induct)
    apply (simp+)
  apply fastforce
  done

lemma distinct_after_in_list_not_self:
  "distinct list \<Longrightarrow> after_in_list list src \<noteq> Some src"
  apply (induct list,simp+)
  apply (case_tac list,clarsimp+)
  done

lemma set_list_insert_after:
  "set (list_insert_after list a b) = set list \<union> (if a \<in> set list then {b} else {})"
  apply(induct list)
   apply(simp)
  apply(simp)
  done

lemma distinct_list_insert_after:
  "\<lbrakk>distinct list; b \<notin> set list \<or> a \<notin> set list\<rbrakk> \<Longrightarrow> distinct (list_insert_after list a b)"
  apply(induct list)
   apply(simp)
  apply(fastforce simp: set_list_insert_after)
  done

lemma list_insert_after_after:
  "\<lbrakk>distinct list; b \<notin> set list; a \<in> set list\<rbrakk>
    \<Longrightarrow> after_in_list (list_insert_after list a b) p
    = (if p = a then Some b else if p = b then after_in_list list a else after_in_list list p)"
  apply(induct list p rule: after_in_list.induct)
    apply (simp split: if_split_asm)+
  apply fastforce
  done

lemma list_remove_removed:
  "set (list_remove list x) = (set list) - {x}"
  apply (induct list,simp+)
  apply blast
  done


lemma remove_distinct_helper: "\<lbrakk>distinct (list_remove list x); a \<noteq> x; a \<notin> set list;
        distinct list\<rbrakk>
       \<Longrightarrow> a \<notin> set (list_remove list x)"
  apply (induct list)
   apply (simp split: if_split_asm)+
  done


lemma list_remove_distinct:
  "distinct list \<Longrightarrow>  distinct (list_remove list x)"
  apply (induct list)
  apply (simp add: remove_distinct_helper split: if_split_asm)+
  done

lemma list_remove_none: "x \<notin> set list \<Longrightarrow> list_remove list x = list"
  apply (induct list)
  apply clarsimp+
  done

lemma replace_distinct: "x \<notin> set list \<Longrightarrow> distinct list \<Longrightarrow> distinct (list_replace list y x)"
  apply (induct list)
  apply (simp add: list_replace_def)+
  apply blast
  done

lemma set_list_replace_list:
  "\<lbrakk>distinct list; slot \<in> set list; slot \<notin> set list'\<rbrakk>
    \<Longrightarrow> set (list_replace_list list slot list') = set list \<union> set list' - {slot}"
  apply (induct list)
  apply auto
  done

lemma after_in_list_in_list:
  "after_in_list list a = Some b \<Longrightarrow> b \<in> set list"
  apply(induct list a arbitrary: b rule: after_in_list.induct)
  apply (simp split: if_split_asm)+
  done

lemma list_replace_empty_after_empty:
  "\<lbrakk>after_in_list list p = Some slot; distinct list\<rbrakk>
    \<Longrightarrow> after_in_list (list_replace_list list slot []) p = after_in_list list slot"
  apply(induct list slot rule: after_in_list.induct)
  apply (simp split: if_split_asm)+
   apply (case_tac xs,simp+)
  apply (case_tac xs,simp+)
  apply (auto dest!: after_in_list_in_list)
  done

lemma list_replace_after_fst_list:
  "\<lbrakk>after_in_list list p = Some slot; distinct list\<rbrakk>
    \<Longrightarrow> after_in_list (list_replace_list list slot (x # xs)) p = Some x"
  apply(induct list p rule: after_in_list.induct)
  apply (simp split: if_split_asm)+
  apply (drule after_in_list_in_list)+
  apply force
  done

lemma after_in_list_append_notin_hd:
  "p \<notin> set list' \<Longrightarrow> after_in_list (list' @ list) p = after_in_list list p"
  apply(induct list', simp, simp)
  apply(case_tac list', simp)
   apply(case_tac list, simp+)
   done

lemma after_in_list_append_last_hd:
  "\<lbrakk>p \<in> set list'; after_in_list list' p = None\<rbrakk>
    \<Longrightarrow> after_in_list (list' @ x # xs) p = Some x"
  apply(induct list' p rule: after_in_list.induct)
    apply(simp)
   apply(simp)
  apply(simp split: if_split_asm)
  done

lemma after_in_list_append_in_hd:
  "after_in_list list p = Some a \<Longrightarrow> after_in_list (list @ list') p = Some a"
  apply(induct list p rule: after_in_list.induct)
    apply(simp split: if_split_asm)+
    done

lemma after_in_list_in_list': "after_in_list list a = Some y \<Longrightarrow> a \<in> set list"
  apply (induct list a rule: after_in_list.induct)
  apply simp+
  apply force
  done

lemma list_replace_after_None_notin_new:
  "\<lbrakk>after_in_list list p = None; p \<notin> set list'\<rbrakk>
    \<Longrightarrow> after_in_list (list_replace_list list slot list') p = None"
  apply(induct list)
   apply(simp)
  apply(simp)
  apply(intro conjI impI)
   apply(simp)
   apply(case_tac list, simp)
    apply(induct list')
     apply(simp)
    apply(simp)
    apply(case_tac list', simp, simp)
   apply(simp split: if_split_asm)
    apply(simp add: after_in_list_append_notin_hd)
   apply(simp add: after_in_list_append_notin_hd)
  apply(case_tac "list_replace_list list slot list'")
   apply(simp)
  apply(simp)
  apply(case_tac list, simp, simp split: if_split_asm)
  done

lemma list_replace_after_notin_new:
  "\<lbrakk>after_in_list list p = Some a; a \<noteq> slot; p \<notin> set list'; p \<noteq> slot\<rbrakk>
    \<Longrightarrow> after_in_list (list_replace_list list slot list') p = Some a"
  apply(induct list)
   apply(simp)
  apply(simp)
  apply(intro conjI impI)
   apply(simp add: after_in_list_append_notin_hd)
   apply(case_tac list, simp, simp)
  apply(case_tac list, simp, simp split: if_split_asm)
  apply(insert after_in_list_append_notin_hd)
  apply(atomize)
  apply(erule_tac x=p in allE, erule_tac x="[aa]" in allE, erule_tac x="list' @ lista" in allE)
  apply(simp)
  done

lemma list_replace_after_None_notin_old:
  "\<lbrakk>after_in_list list' p = None; p \<in> set list'; p \<notin> set list\<rbrakk>
    \<Longrightarrow> after_in_list (list_replace_list list slot list') p = after_in_list list slot"
  apply(induct list)
   apply(simp)
  apply(simp)
  apply(intro conjI impI)
   apply(simp)
   apply(case_tac list)
    apply(simp)
   apply(simp add: after_in_list_append_last_hd)
  apply(case_tac "list_replace_list list slot list'")
   apply(simp)
   apply(case_tac list, simp, simp)
  apply(simp)
  apply(case_tac list, simp, simp)
  done

lemma list_replace_after_notin_old:
  "\<lbrakk>after_in_list list' p = Some a; p \<notin> set list; slot \<in> set list\<rbrakk>
    \<Longrightarrow> after_in_list (list_replace_list list slot list') p = Some a"
  apply(induct list)
   apply(simp)
  apply(simp)
  apply(intro conjI impI)
   apply(simp add: after_in_list_append_in_hd)
  apply(simp)
  apply(case_tac "list_replace_list list slot list'")
   apply(simp)
  apply(simp)
  done


lemma list_replace_set: "x \<in> set list \<Longrightarrow> set (list_replace list x y) = insert y (set (list) - {x})"
  apply (induct list)
  apply (simp add: list_replace_def)+
  apply (intro impI conjI)
  apply blast+
  done

lemma list_swap_both: "x \<in> set list \<Longrightarrow> y \<in> set list \<Longrightarrow> set (list_swap list x y) = set (list)"
  apply (induct list)
  apply (simp add: list_swap_def)+
  apply (intro impI conjI)
  apply blast+
  done

lemma list_swap_self[simp]: "list_swap list x x = list"
  apply (simp add: list_swap_def)
  done

lemma map_ignore: "x \<notin> set list \<Longrightarrow> (map (\<lambda>xa. if xa = x then y else xa)
             list) = list"
  apply (induct list)
  apply simp+
  apply blast
  done

lemma map_ignore2: "y \<notin> set list \<Longrightarrow> (map (\<lambda>xa. if xa = x then y else if xa = y then x else xa)
             list) = (map (\<lambda>xa. if xa = x then y else xa) list)"
  apply (simp add: map_ignore)
  done

lemma map_ignore2': "y \<notin> set list \<Longrightarrow> (map (\<lambda>xa. if xa = y then x else if xa = x then y else xa)
             list) = (map (\<lambda>xa. if xa = x then y else xa) list)"
  apply (simp add: map_ignore)
  apply force
  done

lemma swap_distinct_helper: "\<lbrakk>x \<in> set list; y \<noteq> x; y \<notin> set list; distinct list\<rbrakk>
       \<Longrightarrow> distinct (map (\<lambda>xa. if xa = x then y else xa) list)"
  apply (induct list)
  apply (simp add: map_ignore | elim conjE | intro impI conjI | blast)+
  done

lemma swap_distinct: "x \<in> set list \<Longrightarrow> y \<in> set list \<Longrightarrow> distinct list \<Longrightarrow> distinct (list_swap list x y)"
  apply (induct list)
  apply (simp add: list_swap_def)+
  apply (intro impI conjI,simp_all)
  apply (simp add: map_ignore2 map_ignore2' swap_distinct_helper | elim conjE | force)+
  done


lemma list_swap_none: "x \<notin> set list \<Longrightarrow> y \<notin> set list \<Longrightarrow> list_swap list x y = list"
  apply (induct list)
  apply (simp add: list_swap_def)+
  apply blast
  done

lemma list_swap_one: "x \<in> set list \<Longrightarrow> y \<notin> set list \<Longrightarrow> set (list_swap list x y) = insert y (set (list)) - {x}"
  apply (induct list)
  apply (simp add: list_swap_def)+
  apply (intro impI conjI)
  apply blast+
  done

lemma list_swap_one': "x \<notin> set list \<Longrightarrow> y \<in> set list \<Longrightarrow> set (list_swap list x y) = insert x (set (list)) - {y}"
  apply (induct list)
  apply (simp add: list_swap_def)+
  apply (intro impI conjI)
  apply blast+
  done


lemma in_swapped_list: "y \<in> set list \<Longrightarrow> x \<in> set (list_swap list x y)"
  apply (case_tac "x \<in> set list")
   apply (simp add: list_swap_both)
  apply (simp add: list_swap_one')
  apply (intro notI,simp)
  done

lemma list_swap_empty : "(list_swap list x y = []) = (list = [])"
  by(simp add: list_swap_def)

lemma distinct_after_in_list_antisym:
  "distinct list \<Longrightarrow> after_in_list list a = Some b \<Longrightarrow> after_in_list list b \<noteq> Some a"
  apply (induct list b arbitrary: a rule: after_in_list.induct)
    apply simp+
  apply (case_tac xs)
   apply (clarsimp split: if_split_asm | intro impI conjI)+
  done


lemma after_in_listD: "after_in_list list x = Some y \<Longrightarrow> \<exists>xs ys. list = xs @ (x # y # ys) \<and> x \<notin> set xs"
  apply (induct list x arbitrary: a rule: after_in_list.induct)
    apply (simp split: if_split_asm | elim exE | force)+
  apply (rule_tac x="x # xsa" in exI)
  apply simp
  done

lemma list_swap_symmetric: "list_swap list a b = list_swap list b a"
  apply (simp add: list_swap_def)
  done

lemma list_swap_preserve_after:
  "\<lbrakk>desta \<notin> set list; distinct list\<rbrakk>
\<Longrightarrow> after_in_list (list_swap list srca desta) desta =
   after_in_list list srca"
  apply (induct list desta rule: after_in_list.induct)
  apply (simp add: list_swap_def)+
  apply force
  done

lemma list_swap_preserve_after':
 "\<lbrakk>p \<noteq> desta; p \<noteq> srca; after_in_list list p = Some srca\<rbrakk>
\<Longrightarrow> after_in_list (list_swap list srca desta) p = Some desta"
  apply (induct list p rule: after_in_list.induct)
  apply (simp add: list_swap_def)+
  apply force
  done

lemma list_swap_does_swap:
       "\<lbrakk>distinct list; after_in_list list desta = Some srca\<rbrakk>
       \<Longrightarrow> after_in_list (list_swap list srca desta) srca = Some desta"
  apply (induct list srca rule: after_in_list.induct)
    apply (simp add: list_swap_def)+
  apply (elim conjE)
  apply (intro impI conjI,simp_all)
   apply (frule after_in_list_in_list,simp)+
  done

lemma list_swap_does_swap':
  "distinct list \<Longrightarrow> after_in_list list srca = Some desta \<Longrightarrow>
                after_in_list (list_swap list srca desta) srca =
          after_in_list list desta"
  apply (induct list srca rule: after_in_list.induct)
    apply (simp add: list_swap_def)+
  apply (elim conjE)
  apply (intro impI conjI,simp_all)
   apply (case_tac xs)
    apply (clarsimp+)[2]
  apply (case_tac xs)
   apply clarsimp+
done

lemmas list_swap_preserve_after'' = list_swap_preserve_after'[simplified list_swap_symmetric]

lemma list_swap_preserve_Some_other:
 "\<lbrakk>z \<noteq> desta; z \<noteq> srca; after_in_list list srca = Some z\<rbrakk>
\<Longrightarrow> after_in_list (list_swap list srca desta) desta = Some z"
  apply (induct list srca rule: after_in_list.induct)
  apply (simp add: list_swap_def)+
  apply force
  done


lemmas list_swap_preserve_Some_other' = list_swap_preserve_Some_other[simplified list_swap_symmetric]

lemma list_swap_preserve_None:
 "\<lbrakk>after_in_list list srca = None\<rbrakk>
\<Longrightarrow> after_in_list (list_swap list desta srca) desta = None"
  apply (induct list srca rule: after_in_list.induct)
  apply (simp add: list_swap_def)+
  apply force
  done

lemma list_swap_preserve_None':
 "\<lbrakk>after_in_list list srca = None\<rbrakk>
\<Longrightarrow> after_in_list (list_swap list srca desta) desta = None"
  apply (subst list_swap_symmetric)
  apply (erule list_swap_preserve_None)
  done

lemma list_swap_preserve_after_None:
 "\<lbrakk>p \<noteq> desta; p \<noteq> srca; after_in_list list p = None\<rbrakk>
\<Longrightarrow> after_in_list (list_swap list srca desta) p = None"
  apply (induct list p rule: after_in_list.induct)
  apply (simp add: list_swap_def)+
  apply force
  done

lemma list_swap_preserve_Some_other_distinct:
 "\<lbrakk>distinct list; z \<noteq> desta; after_in_list list srca = Some z\<rbrakk>
\<Longrightarrow> after_in_list (list_swap list srca desta) desta = Some z"
  apply (rule list_swap_preserve_Some_other)
  apply simp+
   apply (rule notI)
   apply simp
   apply (frule distinct_after_in_list_not_self[where src=srca])
   apply simp+
  done

lemma list_swap_preserve_separate:
 "\<lbrakk>p \<noteq> desta; p \<noteq> srca; z \<noteq> desta; z \<noteq> srca; after_in_list list p = Some z\<rbrakk>
\<Longrightarrow> after_in_list (list_swap list srca desta) p = Some z"
  apply (induct list p rule: after_in_list.induct)
  apply (simp add: list_swap_def split: if_split_asm)+
  apply (intro impI conjI)
   apply simp+
  done

fun after_in_list_list where
  "after_in_list_list [] a = []" |
  "after_in_list_list (x # xs) a = (if a = x then xs else after_in_list_list xs a)"

lemma after_in_list_list_in_list:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows "y \<in> set (after_in_list_list list x) \<Longrightarrow> y \<in> set list"
  apply(induct list arbitrary:x y)
  apply(simp)
  apply(case_tac "x=a", simp+)
done

lemma range_nat_relation_induct:
"\<lbrakk> m = Suc (n + k) ; m < cap ; \<forall>n. Suc n < cap \<longrightarrow> P n (Suc n );
   \<forall>i j k. i < cap \<and> j < cap \<and> k < cap \<longrightarrow> P i j \<longrightarrow> P j k \<longrightarrow> P i k \<rbrakk> \<Longrightarrow>  P n m"
  apply (clarify)
  apply (thin_tac "m = t" for t)
  apply (induct k)
   apply (drule_tac x = "n" in spec)
   apply (erule impE, simp, simp)
  apply (frule_tac x = "Suc (n + k)" in spec)
  apply (erule impE)
   apply (simp only: add_Suc_right)
  apply (rotate_tac 3, frule_tac x = n in spec)
  apply (rotate_tac -1, drule_tac x = "Suc (n + k)" in spec)
  apply (rotate_tac -1, drule_tac x = "Suc (n + Suc k) " in spec)
  apply (erule impE)
   apply (intro conjI)
     apply (rule_tac y = "Suc (n + Suc k)" in less_trans)
      apply (rule less_SucI)
      apply (simp only: add_Suc_right)+
done

lemma indexed_trancl_as_set_helper : "\<lbrakk>p < q; q < length list; list ! p = a; list ! q = b;
        q = Suc (p + k); Suc n < length list\<rbrakk>
       \<Longrightarrow> (a, b) \<in> {(i, j). \<exists>p. Suc p <length list \<and> list ! p = i \<and> list ! Suc p = j}\<^sup>+"
  apply (induct k arbitrary: p q a b)
   apply (rule r_into_trancl,simp, rule_tac x = p in exI, simp)
  apply (atomize)
  apply (erule_tac x = p in allE, erule_tac x = "Suc (p + k)" in allE, erule_tac x = "a" in allE, erule_tac x = "list ! Suc (p + k)" in allE)
  apply (elim impE)
        apply (simp)+
  apply (rule_tac b = "list ! Suc (p + k)" in trancl_into_trancl)
   apply (simp)+
  apply (rule_tac x = "Suc (p + k)" in exI, simp)
  done

lemma indexed_trancl_as_set: "distinct list \<Longrightarrow> {(i, j). \<exists> p q. p < q \<and> q < length list \<and> list ! p = i \<and> list ! q = j }
      = {(i, j). \<exists> p. Suc p < length list \<and> list ! p = i \<and> list ! Suc p = j }\<^sup>+"
  apply (rule equalityI)
    apply (rule subsetI)
    apply (case_tac x, simp)
    apply (elim exE conjE)
    apply (frule less_imp_Suc_add)
    apply (erule exE)
    apply (rule_tac cap = "length list" and m = q and n = p and k = k in range_nat_relation_induct)
      apply (simp)
      apply (simp)
      apply (rule allI, rule impI)
      apply (rule_tac p = p and q = q and k = k and n = n in indexed_trancl_as_set_helper)
        apply (simp)+
  apply (rule subsetI)
    apply (case_tac x, simp)
    apply (erule trancl_induct)
      apply (simp, elim exE conjE)
      apply (rule_tac x = p in exI, rule_tac x = "Suc p" in exI, simp)
      apply (simp)
      apply (rotate_tac 4, erule exE, rule_tac x = p in exI)
      apply (erule exE, rule_tac x = "Suc pa" in exI)
      apply (intro conjI)
        defer
        apply (simp)
        apply (erule exE, simp)
        apply (simp)
        apply (erule exE)
        apply (subgoal_tac "pa = q")
          apply (simp)
          apply (frule_tac xs = list and i = pa and j = q in nth_eq_iff_index_eq)
            apply (simp)+
done

lemma indexed_trancl_irrefl: "distinct list \<Longrightarrow> (x,x) \<notin> {(i, j). \<exists> p. Suc p < length list \<and> list ! p = i \<and> list ! Suc p = j }\<^sup>+"
 apply (frule indexed_trancl_as_set [THEN sym])
 apply (simp)
 apply (intro allI impI notI)
 apply (frule_tac xs = list and i = p and j = q in nth_eq_iff_index_eq)
 apply (simp+)
done

lemma after_in_list_trancl_indexed_trancl: "distinct list \<Longrightarrow> {(p, q). after_in_list list p = Some q}\<^sup>+ = {(i, j). \<exists> p. Suc p < length list \<and> list ! p = i \<and> list ! Suc p = j }\<^sup>+"
  apply (rule_tac f = "\<lambda> x. x\<^sup>+" in  arg_cong)
  apply (intro equalityI subsetI)

  apply (case_tac x, simp)
  apply (induct list)
   apply (simp)
   apply (case_tac "a = aa")
     apply (rule_tac x = 0 in exI, case_tac list, simp, simp)
     apply (case_tac list, simp, simp)
     apply (atomize, drule_tac x = x in spec, drule_tac x = aa in spec, drule_tac x = b in spec, simp)
     apply (erule exE, rule_tac x = "Suc p" in exI, simp)

  apply (case_tac x, simp)
  apply (induct list)
    apply (simp)
    apply (case_tac "a = aa")
      apply (erule exE)
      apply (subgoal_tac "p = 0")
        apply (case_tac list, simp, simp)
        apply (subgoal_tac "distinct (aa # list)")
          apply (frule_tac i = 0 and j = p and xs = "aa # list" in nth_eq_iff_index_eq)
          apply (simp, simp, simp, simp)
    apply (atomize, drule_tac x = x in spec, drule_tac x = aa in spec, drule_tac x = b in spec, simp)
    apply (drule mp)
      apply (erule exE)
      apply (case_tac p, simp, simp)
      apply (rule_tac x = nat in exI, simp)
   apply (case_tac list, simp, simp)
done

lemma distinct_after_in_list_not_self_trancl:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows "distinct list \<Longrightarrow> (x, x) \<notin> {(p, q). after_in_list list p = Some q}\<^sup>+"
  by (simp add: after_in_list_trancl_indexed_trancl indexed_trancl_irrefl)

lemma distinct_after_in_list_in_list_trancl:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows "\<lbrakk>distinct list; (x, y) \<in> {(p, q). after_in_list list q = Some p}\<^sup>+\<rbrakk> \<Longrightarrow> x \<in> set list"
  by(erule tranclE2, (drule CollectD, simp, drule after_in_list_in_list, simp)+)


lemma after_in_list_trancl_prepend:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows "\<lbrakk>distinct (y # list); x \<in> set list\<rbrakk> \<Longrightarrow> (y, x) \<in> {(n, p). after_in_list (y # list) n = Some p}\<^sup>+"
  apply(induct list arbitrary:x y)
    apply(simp)
    apply(case_tac "x=a")
      apply(rule r_into_trancl)
      apply(simp)
      apply(drule set_ConsD)
      apply(elim disjE)
        apply(simp)
        apply(atomize)
        apply(drule_tac x=x in spec)
        apply(drule_tac x=y in spec)
        apply(drule_tac mp)
          apply(simp)
        apply(drule_tac mp)
          apply(simp)
        apply(erule trancl_induct)
          apply(drule CollectD, simp)
          apply(rule_tac b = a in trancl_into_trancl2)
            apply(simp)
          apply(rule r_into_trancl)
          apply(rule_tac a = "(a,ya)" in CollectI)
          apply(clarsimp)
          apply(case_tac list)
            apply(simp)
            apply(simp)
          apply(case_tac "ya=a")
            apply(drule CollectD)
            apply(simp del:after_in_list.simps)
            apply(drule after_in_list_in_list')
            apply(simp)
            apply(rule_tac b=ya in trancl_into_trancl)
              apply(simp)
              apply(drule CollectD)
              apply(rule CollectI)
              apply(case_tac "ya=y")
                apply(frule_tac x=y in distinct_after_in_list_not_self_trancl)
                apply(simp)
                apply(case_tac list)
                  apply(simp)
                  apply(simp)
done

lemma after_in_list_append_not_hd:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows "a \<noteq> x \<Longrightarrow> after_in_list (a # list) x = after_in_list list x"
by (case_tac list, simp, simp)

lemma trancl_Collect_rev:
  "(a, b) \<in> {(x, y). P x y}\<^sup>+ \<Longrightarrow> (b, a) \<in> {(x, y). P y x}\<^sup>+"
  apply(induct rule: trancl_induct)
   apply(fastforce intro: trancl_into_trancl2)+
   done


lemma prepend_after_in_list_distinct : "distinct (a # list) \<Longrightarrow> {(next, p). after_in_list (a # list) p = Some next}\<^sup>+ =
       {(next, p). after_in_list (list) p = Some next}\<^sup>+ \<union>
       set list \<times> {a} "
  apply (rule equalityI)
   (* \<subseteq> direction *)
   apply (rule subsetI, case_tac x)
   apply (simp)
   apply (erule trancl_induct)
     (* base case *)
    apply (drule CollectD, simp)
    apply (case_tac list, simp)
    apply (simp split:if_split_asm)
    apply (rule r_into_trancl)
    apply (rule CollectI, simp)
    (* Inductive case *)
   apply (drule CollectD, simp)
   apply (erule disjE)
    apply (case_tac "a \<noteq> z")
     apply (rule disjI1)
     apply (rule_tac b =y in trancl_into_trancl)
      apply (simp, case_tac list, simp, simp)

    apply (simp)
    apply (rule disjI2)
    apply (erule conjE)
    apply (frule_tac x = aa and y = y in distinct_after_in_list_in_list_trancl)
     apply (simp)
    apply (simp)
   apply (subgoal_tac "after_in_list (a # list) z \<noteq> Some a", simp)
   apply (rule_tac hd_not_after_in_list, simp, simp)
(* \<supseteq> direction *)
  apply (rule subsetI)
  apply (case_tac x)
  apply (simp)
  apply (erule disjE)
    (* transitive case *)
   apply (erule tranclE2)
    apply (drule CollectD, simp)
    apply (subgoal_tac "b \<noteq> a")
     apply (rule r_into_trancl)
     apply (rule CollectI, simp)
     apply (case_tac list, simp, simp)
    apply (frule after_in_list_in_list')
    apply (erule conjE)
    apply (blast)
   apply (rule_tac y = c in trancl_trans)
    apply (subgoal_tac "c \<noteq> a")
     apply (case_tac list, simp, simp)
     apply (case_tac "aaa = aa")
      apply (rule r_into_trancl)
      apply (rule CollectI, simp)

     apply (rule r_into_trancl)
     apply (rule CollectI, simp)
    apply (erule CollectE, simp)
    apply (frule after_in_list_in_list')
    apply (erule conjE, blast)
   apply (erule trancl_induct)
    apply (simp)
    apply (rule r_into_trancl, simp)
    apply (subgoal_tac "y \<noteq> a")
     apply (case_tac list, simp, simp)
    apply (rotate_tac 3)
    apply (frule after_in_list_in_list')
    apply (erule conjE, blast)
   apply (rule_tac b = y in trancl_into_trancl, simp)
   apply (rule CollectI, simp)
   apply (subgoal_tac "a \<noteq> z")
    apply (case_tac list, simp, simp)
   apply (rotate_tac 3)
   apply (frule after_in_list_in_list')
   apply (blast)
(* not so transitive case *)
  apply (subgoal_tac "distinct (a # list)")
   apply (frule_tac x = aa in after_in_list_trancl_prepend, simp, simp)
   apply (rule trancl_Collect_rev, simp)
  apply (simp)
done

lemma after_in_list_in_cons:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows "\<lbrakk>after_in_list (x # xs) y = Some z; distinct (x # xs); y \<in> set xs\<rbrakk> \<Longrightarrow> z \<in> set xs"
  apply(case_tac "y=x")
  apply(simp)
  apply(simp add:after_in_list_append_not_hd after_in_list_in_list)
done

lemma after_in_list_list_set:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows "distinct list \<Longrightarrow>
         set (after_in_list_list list x)
         = {a. (a, x) \<in> {(next, p). after_in_list list p = Some next}\<^sup>+}"
  apply(intro equalityI)
  (* \<subseteq> *)
   apply(induct list arbitrary:x)
    apply(simp)
   apply(atomize)
   apply(simp)
   apply(rule conjI, rule impI, rule subsetI)
    apply(rule_tac a = xa in CollectI)
    apply(rule trancl_Collect_rev)
    apply(rule after_in_list_trancl_prepend)
     apply(simp)
    apply(simp)
   apply(clarify)
   apply(drule_tac x=x in spec)
   apply(drule_tac B="{a. (a, x) \<in> {(next, p). after_in_list list p = Some next}\<^sup>+}" in set_rev_mp)
    apply(simp)
   apply(drule CollectD)
   apply(simp add:prepend_after_in_list_distinct)
 (* \<supseteq> *)
  apply(clarsimp)
  apply(drule trancl_Collect_rev)
  apply(erule trancl_induct)
    (* base *)
   apply(simp)
   apply(induct list arbitrary:x)
    apply(simp)
   apply(case_tac "a=x")
    apply(frule_tac src=x in distinct_after_in_list_not_self)
    apply(simp)
    apply(drule after_in_list_in_list)
    apply(simp)+
   apply(drule_tac list=list in after_in_list_append_not_hd)
   apply(simp)
   (* inductive *)
  apply(simp)
  apply(drule trancl_Collect_rev)
  apply(induct list arbitrary: x)
   apply(simp)
  apply(case_tac "a\<noteq>x")
  (* a\<noteq>x *)
   apply(atomize, drule_tac x=y in spec, drule_tac x=z in spec, drule_tac x=x in spec)
   apply(simp add:prepend_after_in_list_distinct)
   apply(case_tac "a=y")
    apply(simp add:after_in_list_list_in_list)
   apply(simp add:after_in_list_append_not_hd)
   (* a=x *)
  apply(frule after_in_list_in_cons, simp+)
done

lemma list_eq_after_in_list':
  "\<lbrakk> distinct xs; p = xs ! i; i < length xs \<rbrakk>
    \<Longrightarrow> \<exists>list. xs = list @ p # after_in_list_list xs p"
   apply (induct xs arbitrary: i)
     apply (simp)
  apply (atomize)
  apply (case_tac i)
   apply (simp)
  apply (drule_tac x = nat in spec, simp)
  apply (erule exE, rule impI, rule_tac x = "a # list" in exI)
  apply (simp)
done

lemma after_in_list_last_None:
  "distinct list \<Longrightarrow> after_in_list list (last list) = None"
  apply(induct list)
   apply(simp)
  apply(case_tac list)
   apply(simp)
  apply(fastforce split: if_split_asm)
  done

lemma after_in_list_None_last:
  "\<lbrakk>after_in_list list x = None; x \<in> set list\<rbrakk> \<Longrightarrow> x = last list"
  by (induct list x rule: after_in_list.induct,(simp split: if_split_asm)+)

end
