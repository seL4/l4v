(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory DataStructures
imports "~~/src/HOL/Main"
begin

(*
 * Proofs on abstract data structures that should be applicable
 * to concrete C proofs.
 *)


(*
 * Singly-linked list definitions and lemmas adapted from:
 *
 *   "Proving Pointer Programs in Higher-Order Logic"
 *   Farhad Mehta, Tobias Nipkow
 *)

locale linked_list =
  (* Fetch next pointer from object. *)
  fixes list_next :: "'a \<Rightarrow> 'p"
  (* Null pointer. *)
  and NULL :: "'p"

context linked_list begin

primrec
  list :: "('p \<Rightarrow> 'a option) \<Rightarrow> 'p list \<Rightarrow> 'p \<Rightarrow> bool"
where
  "list s [] i = (i = NULL)"
| "list s (x#xs) i =
    (i = x \<and> x \<noteq> NULL \<and> (\<exists>a. s x = Some a \<and>  list s xs (list_next a)))"



definition
  is_list :: "('p \<Rightarrow> 'a option) \<Rightarrow> 'p \<Rightarrow> bool"
where
  "is_list s p \<equiv> \<exists>xs. list s xs p"

definition
  the_list :: "('p \<Rightarrow> 'a option) \<Rightarrow> 'p \<Rightarrow> 'p list"
where
  "the_list s p \<equiv> (THE xs. list s xs p)"

lemma list_empty [simp]: "list s xs NULL = (xs = [])"
  by (case_tac "xs", auto)

lemma is_list_empty [simp]: "is_list s NULL"
  by (clarsimp simp: is_list_def)

lemma the_list_empty [simp]: "the_list s NULL = []"
  by (clarsimp simp: the_list_def)

lemma list_unique: "\<lbrakk> list s xs p; list s ys p \<rbrakk> \<Longrightarrow> xs = ys"
  apply (induct xs arbitrary: ys p)
   apply simp
  apply (case_tac ys, auto)
  done

lemma list_ptr_unique: "\<lbrakk> list s xs p; list s xs p' \<rbrakk> \<Longrightarrow> p = p'"
  by (metis linked_list.list.simps(1) linked_list.list.simps(2) neq_Nil_conv)

lemma list_non_NULL:
  "p \<noteq> NULL \<Longrightarrow>
    list s xs p = (\<exists>ys. xs= p#ys \<and> (\<exists>a. s p = Some a \<and> list s ys (list_next a)))"
  by (case_tac xs, auto)

lemma is_list_non_NULL:
  "p \<noteq> NULL \<Longrightarrow>
    is_list s p = (\<exists>a. s p = Some a \<and> is_list s (list_next a))"
  apply (clarsimp simp: is_list_def list_non_NULL)
  apply force
  done

lemma the_list_non_NULL:
  "\<lbrakk> p \<noteq> NULL; is_list s p \<rbrakk> \<Longrightarrow>
    the_list s p = (p # (the_list s (list_next (the (s p)))))"
  apply (clarsimp simp: the_list_def is_list_def list_non_NULL)
  apply (rule the_equality)
   apply (clarsimp simp: list_unique)
   apply (metis (lifting) list_unique the_equality)
  apply clarsimp
  apply (metis (lifting) list_unique the_equality)
  done

lemma list_is_list: "list s xs p \<Longrightarrow> is_list s p"
  apply (clarsimp simp: is_list_def)
  apply force
  done

lemma list_the_list: "list s xs p \<Longrightarrow> the_list s p = xs"
  apply (clarsimp simp: the_list_def)
  apply (metis (lifting) list_unique the_equality)
  done

lemma the_list_empty' [simp]:
    "is_list s p \<Longrightarrow> (the_list s p = []) = (p = NULL)"
  by (metis is_list_def list_empty list_ptr_unique list_the_list)

lemma list_last_is_NULL:
    "\<lbrakk> is_list s p; the_list s p = l; p \<noteq> NULL \<rbrakk> \<Longrightarrow> list_next (the (s (last l))) = NULL"
  apply (induct l arbitrary: p)
   apply clarsimp
  apply (metis is_list_non_NULL last_ConsL last_ConsR linked_list.the_list_non_NULL option.sel the_list_empty' list.sel(3))
  done

lemma list_in_Some:
  "\<lbrakk> list s xs p; x \<in> set xs \<rbrakk> \<Longrightarrow> \<exists>a. s x = Some a"
  apply (induct xs arbitrary: p, auto)
  done

lemma list_mem: "\<lbrakk> list s xs p; p \<noteq> NULL \<rbrakk> \<Longrightarrow> p \<in> set xs"
  by (case_tac xs, auto)

lemma list_ign [iff]: "\<lbrakk> x \<notin> set xs \<rbrakk> \<Longrightarrow> list (s(x := v)) xs p = list s xs p"
  apply (induct xs arbitrary: p)
   apply clarsimp
  apply atomize
  apply clarsimp
  done

lemma list_ign_ext' [intro, iff]:
    "\<lbrakk> \<forall>x \<in> set xs. (\<exists>a. s x = Some a) = (\<exists>a. s' x = Some a) \<and> (list_next (the (s x)) = list_next (the (s' x)))  \<rbrakk> \<Longrightarrow> list s xs p = list s' xs p"
  apply (induct xs arbitrary: p, auto)
  done

lemma list_ign_ext [iff?]: "\<lbrakk> \<forall>x \<in> set xs. s x = s' x \<rbrakk> \<Longrightarrow> list s xs p = list s' xs p"
  apply force
  done

lemma list_append_Ex:
  "list s (xs@ys) p \<Longrightarrow> (\<exists>q. list s ys q)"
  apply (induct xs arbitrary: ys p)
   apply force
  apply force
  done

lemma list_head_not_in_list: "\<lbrakk> list s xs (list_next a); s p = Some a \<rbrakk> \<Longrightarrow> p \<notin> set xs"
  apply (rule ccontr)
  apply clarsimp
  apply (frule split_list)
  apply clarsimp
  apply (frule list_append_Ex)
  apply clarsimp
  apply (drule (1) list_unique)
  apply clarsimp
  done

lemma list_distinct: "list s xs x \<Longrightarrow> distinct xs"
  apply (induct xs arbitrary: x)
   apply clarsimp
  apply clarsimp
  apply (drule (1) list_head_not_in_list)
  apply clarsimp
  done

lemma list_next: "\<lbrakk> list s xs x; s x = Some a; x \<noteq> NULL \<rbrakk> \<Longrightarrow> list s (tl xs) (list_next a)"
  apply (case_tac xs)
   apply clarsimp
  apply clarsimp
  done

primrec
  path :: "('p \<Rightarrow> 'a option) \<Rightarrow> 'p \<Rightarrow> 'p list \<Rightarrow> 'p \<Rightarrow> bool"
where
  "path s x [] y = (x = y)"
| "path s x (a#as) y = (x \<noteq> NULL \<and> x = a \<and> (\<exists>v. s x = Some v \<and> path s (list_next v) as y))"

lemma path_null [simp]: "path s NULL as x = (as = [] \<and> x = NULL)"
  by (case_tac as, auto)

lemma path_no_null [simp]: "\<lbrakk> path s a xs b \<rbrakk> \<Longrightarrow> NULL \<notin> set xs"
  apply (induct xs arbitrary: a)
   apply clarsimp
  apply clarsimp
  done

lemma path_next:
  "\<lbrakk> x \<noteq> NULL \<rbrakk> \<Longrightarrow> path s x as y = ((as = [] \<and> x = y)
    \<or> (\<exists>bs. as = x # bs \<and> (\<exists>a. s x = Some a \<and> path s (list_next a) bs y)))"
  apply (case_tac as, auto)
  done

lemma path_null_list: "path s a xs NULL = list s xs a"
  apply (induct xs arbitrary: a, auto)
  done

lemma path_ign [iff]: "u \<notin> set as \<Longrightarrow> path (s(u := v)) x as y = path s x as y"
  by (induct as arbitrary: x y, auto)

lemma path_split [simp]: "path s x (as @ bs) z = (\<exists>y. path s x as y \<and> path s y bs z)"
  apply (induct as arbitrary: x, auto)
  done

lemma list_split [simp]: "list s (as @ bs) x = (\<exists>y. path s x as y \<and> list s bs y)"
  by (induct as arbitrary: x, auto)

end

(*
 * Doubly-linked list, with NULL pointers.
 *)
locale dbl_linked_list =
  linked_list +
  constrains list_next :: "'a \<Rightarrow> 'p" and NULL :: "'p"
  (* Fetch prev pointer from object. *)
  fixes list_prev :: "'a \<Rightarrow> 'p"

context dbl_linked_list begin

primrec
  dbl_list_tail :: "('p \<Rightarrow> 'a option) \<Rightarrow> 'p \<Rightarrow> 'p list \<Rightarrow> 'p \<Rightarrow> bool"
where
  "dbl_list_tail s p [] h = (h = NULL)"
| "dbl_list_tail s p (x#xs) h =
    (h = x \<and> x \<noteq> NULL \<and> (\<exists>a. s x = Some a \<and> list_prev a = p \<and> dbl_list_tail s x xs (list_next a)))"

abbreviation
  dbl_list :: "('p \<Rightarrow> 'a option) \<Rightarrow> 'p list \<Rightarrow> 'p \<Rightarrow> bool"
where
  "dbl_list s l h \<equiv> dbl_list_tail s NULL l h"

lemma dbl_list_null_empty [simp]: "dbl_list_tail s p [] NULL"
  by simp

lemma dbl_list_empty [simp]: "dbl_list_tail s p xs NULL = (xs = [])"
  by (case_tac xs, auto)

lemma dbl_list_single: "\<lbrakk> s x = Some y; list_prev y = NULL; list_next y = NULL; x \<noteq> NULL \<rbrakk> \<Longrightarrow> dbl_list s [x] x"
  by simp

lemma dbl_list_tail_non_NULL:
  "h \<noteq> NULL \<Longrightarrow>
    dbl_list_tail s p xs h =
      (\<exists>ys. xs= h#ys \<and> (\<exists>a. s h = Some a \<and> list_prev a = p \<and> dbl_list_tail s h ys (list_next a)))"
  apply (case_tac xs, auto)
  done

lemma dbl_list_tail_in_Some:
  "\<lbrakk> dbl_list_tail s p xs h; x \<in> set xs \<rbrakk> \<Longrightarrow> \<exists>a. s x = Some a"
  apply (induct xs arbitrary: p h, auto)
  done

lemma dbl_list_tail_mem: "\<lbrakk> dbl_list_tail s p xs h; h \<noteq> NULL \<rbrakk> \<Longrightarrow> h \<in> set xs"
  by (case_tac xs, auto)

lemma dbl_list_ign [iff]: "\<lbrakk> x \<notin> set xs \<rbrakk> \<Longrightarrow> dbl_list_tail (s(x := v)) p xs h = dbl_list_tail s p xs h"
  apply (induct xs arbitrary: p h)
   apply clarsimp
  apply atomize
  apply clarsimp
  done

lemma dbl_list_ign_ext' [intro, iff]:
    "\<lbrakk> \<forall>x \<in> set xs.
        (\<exists>a. s x = Some a) = (\<exists>a. s' x = Some a)
        \<and> (list_next (the (s x)) = list_next (the (s' x)))
        \<and> (list_prev (the (s x)) = list_prev (the (s' x))) \<rbrakk> \<Longrightarrow>
     dbl_list_tail s p xs h = dbl_list_tail s' p xs h"
  apply (induct xs arbitrary: p h, auto)
  done

lemma dbl_list_ign_ext [iff?]: "\<lbrakk> \<forall>x \<in> set xs. s x = s' x \<rbrakk> \<Longrightarrow> dbl_list_tail s p xs h = dbl_list_tail s' p xs h"
  apply force
  done

lemma dbl_list_unique: "\<lbrakk> dbl_list_tail s p xs h; dbl_list_tail s p' ys h \<rbrakk> \<Longrightarrow> xs = ys"
  apply (induct xs arbitrary: ys p p' h)
   apply simp
  apply (case_tac ys, auto)
  done

lemma dbl_list_append_Ex:
  "dbl_list_tail s p (xs@ys) h \<Longrightarrow> (\<exists>q. dbl_list_tail s (last (p#xs)) ys q)"
  apply (induct xs arbitrary: ys p h)
   apply force
  apply force
  done

lemma dbl_list_head_not_in_list: "\<lbrakk> dbl_list_tail s p xs (list_next a); s h = Some a \<rbrakk> \<Longrightarrow> h \<notin> set xs"
  apply (rule ccontr)
  apply clarsimp
  apply (frule split_list)
  apply clarsimp
  apply (frule dbl_list_append_Ex)
  apply clarsimp
  apply (drule (1) dbl_list_unique)
  apply clarsimp
  done

lemma dbl_list_distinct: "dbl_list_tail s p xs x \<Longrightarrow> distinct xs"
  apply (induct xs arbitrary: x p)
   apply clarsimp
  apply clarsimp
  apply (drule (1) dbl_list_head_not_in_list)
  apply clarsimp
  done

lemma dbl_list_next: "\<lbrakk> dbl_list_tail s p xs x; s x = Some a; x \<noteq> NULL \<rbrakk> \<Longrightarrow> dbl_list_tail s x (tl xs) (list_next a)"
  apply (case_tac xs)
   apply clarsimp
  apply clarsimp
  done

end

(*
 * Circular-linked list, with a head node.
 *)
locale circ_linked_list =
  (* Fetch next pointer from object. *)
  fixes list_next :: "'a \<Rightarrow> 'p"
  (* Fetch previous pointer from object. *)
  fixes list_prev :: "'a \<Rightarrow> 'p"

context circ_linked_list begin

fun
  circ_list_tail :: "('p \<Rightarrow> 'a option) \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p list \<Rightarrow> 'p \<Rightarrow> bool"
where
  "circ_list_tail s head prev [] current = (current = head)"
| "circ_list_tail s head prev (x#xs) current =
        (current = x \<and> current \<noteq> head \<and>
          (\<exists>a. s x = Some a \<and> list_prev a = prev
            \<and> circ_list_tail s head x xs (list_next a)))"

lemma circ_list_defn_test: "
  \<lbrakk> s head = Some headNode;
    s n1 = Some node1;
    s n2 = Some node2;
    list_next headNode = n1; list_next node1 = n2; list_next node2 = head;
    list_prev headNode = n2; list_prev node1 = head; list_prev node2 = n1;
    n1 \<noteq> head; n2 \<noteq> head \<rbrakk> \<Longrightarrow>
   circ_list_tail s head head [n1, n2] n1"
  apply clarsimp
  done

definition
  circ_list :: "('p \<Rightarrow> 'a option) \<Rightarrow> 'p \<Rightarrow> 'p list \<Rightarrow> bool"
where
  "circ_list s head l \<equiv> (\<exists>a. s head = Some a \<and> (list_prev a = (last (head # l))) \<and> (circ_list_tail s head head l (list_next a)))"

lemma circ_list_tail_empty [simp]: "circ_list_tail s head p xs head = (xs = [])"
  apply (case_tac xs)
   apply clarsimp
  apply clarsimp
  done

lemma circ_list_empty: "\<lbrakk> s head = Some a; list_next a = head; list_prev a = head \<rbrakk> \<Longrightarrow> circ_list s head []"
  apply (clarsimp simp: circ_list_def)
  done

lemma circ_list_single: "\<lbrakk>
    x \<noteq> head;
    s x = Some a; list_next a = head; list_prev a = head;
    s head = Some b; list_next b = x; list_prev b = x
  \<rbrakk> \<Longrightarrow> circ_list s head [x]"
  apply (clarsimp simp: circ_list_def)
  done

lemma circ_list_tail_in_Some:
  "\<lbrakk> circ_list_tail s head p xs h; x \<in> set xs \<rbrakk> \<Longrightarrow> \<exists>a. s x = Some a"
  apply (induct xs arbitrary: p h, auto)
  done

lemma circ_list_tail_ign [iff]: "\<lbrakk> x \<notin> set xs \<rbrakk> \<Longrightarrow> circ_list_tail (s(x := v)) head p xs h = circ_list_tail s head p xs h"
  apply (induct xs arbitrary: p h)
   apply clarsimp
  apply clarsimp
  done

lemma circ_list_ign [iff]: "\<lbrakk> x \<notin> set xs; x \<noteq> head \<rbrakk> \<Longrightarrow> circ_list (s(x := v)) head xs = circ_list s head xs"
  apply (clarsimp simp: circ_list_def)
  done

lemmas circ_list_tail_ign' [iff] = circ_list_tail_ign [unfolded fun_upd_def]
lemmas circ_list_ign' [iff] = circ_list_ign [unfolded fun_upd_def]

lemma circ_list_tail_ign_ext' [intro?, iff?]:
    "\<lbrakk> \<forall>x \<in> set xs.
        (\<exists>a. s x = Some a) = (\<exists>a. s' x = Some a)
        \<and> (list_next (the (s x)) = list_next (the (s' x)))
        \<and> (list_prev (the (s x)) = list_prev (the (s' x))) \<rbrakk> \<Longrightarrow>
     circ_list_tail s head p xs h = circ_list_tail s' head p xs h"
  apply (induct xs arbitrary: p h, auto)
  done

lemma circ_list_ign_ext' [intro?, iff?]:
    "\<lbrakk> \<forall>x \<in> set xs.
        (\<exists>a. s x = Some a) = (\<exists>a. s' x = Some a)
        \<and> (list_next (the (s x)) = list_next (the (s' x)))
        \<and> (list_prev (the (s x)) = list_prev (the (s' x)));
       (\<exists>a. s head = Some a) = (\<exists>a. s' head = Some a);
       (list_next (the (s head)) = list_next (the (s' head)));
       (list_prev (the (s head)) = list_prev (the (s' head))) \<rbrakk> \<Longrightarrow>
     circ_list s head xs = circ_list s' head xs"
  apply (clarsimp simp: circ_list_def)
  apply (case_tac xs)
   apply force
  apply (clarsimp, safe, auto iff: circ_list_tail_ign_ext')
  done

lemma circ_list_tail_ign_ext [iff?]: "\<lbrakk> \<forall>x \<in> set xs. s x = s' x \<rbrakk> \<Longrightarrow> circ_list_tail s head p xs h = circ_list_tail s' head p xs h"
  apply (force iff: circ_list_tail_ign_ext')
  done

lemma circ_list_ign_ext [iff?]: "\<lbrakk> \<forall>x \<in> set xs. s x = s' x; s head = s' head \<rbrakk> \<Longrightarrow> circ_list s head xs = circ_list s' head xs"
  apply (force iff: circ_list_ign_ext')
  done

lemma circ_list_tail_unique: "\<lbrakk> circ_list_tail s head p xs h; circ_list_tail s head p' ys h \<rbrakk> \<Longrightarrow> xs = ys"
  apply (induct xs arbitrary: ys p p' h)
   apply clarsimp
  apply (case_tac ys, auto)
  done

lemma circ_list_unique: "\<lbrakk> circ_list s h xs; circ_list s h ys \<rbrakk> \<Longrightarrow> xs = ys"
  apply (clarsimp simp: circ_list_def)
  apply (erule (1) circ_list_tail_unique)
  done

lemma circ_list_tail_append_Ex:
  "circ_list_tail s head p (xs@ys) h \<Longrightarrow> (\<exists>q. circ_list_tail s head (last (p#xs)) ys q)"
  apply (induct xs arbitrary: ys p h)
   apply force
  apply force
  done

lemma circ_list_tail_head_not_in_list: "\<lbrakk> circ_list_tail s head p xs (list_next a); s h = Some a \<rbrakk> \<Longrightarrow> h \<notin> set xs"
  apply (rule ccontr)
  apply clarsimp
  apply (frule split_list)
  apply clarsimp
  apply (frule circ_list_tail_append_Ex)
  apply clarsimp
  apply (drule (1) circ_list_tail_unique)
  apply clarsimp
  done

lemma circ_list_head_not_in_list: "\<lbrakk> circ_list s head xs \<rbrakk> \<Longrightarrow> head \<notin> set xs"
  apply (clarsimp simp: circ_list_def)
  apply (drule (1) circ_list_tail_head_not_in_list)
  apply simp
  done

lemma circ_list_tail_distinct: "circ_list_tail s head p xs x \<Longrightarrow> distinct xs"
  apply (induct xs arbitrary: x p)
   apply clarsimp
  apply clarsimp
  apply (drule (1) circ_list_tail_head_not_in_list)
  apply clarsimp
  done

lemma circ_list_distinct: "circ_list s head xs \<Longrightarrow> distinct xs"
  by (metis circ_list_def circ_list_tail_distinct)

lemma circ_list_tail_prev':
  "\<lbrakk> circ_list_tail s h p a x; n \<in> set a; s n = Some m; list_prev m \<noteq> p \<rbrakk> \<Longrightarrow> list_prev m \<in> set a"
  apply (induct a arbitrary: p x)
   apply clarsimp
  apply force
  done

lemma circ_list_tail_prev:
  "\<lbrakk> circ_list_tail s h p a x; n \<in> set a; s n = Some m; list_prev m \<notin> set a \<rbrakk> \<Longrightarrow> list_prev m = p"
  apply (induct a arbitrary: p x)
   apply clarsimp
  apply force
  done

lemma circ_list_tail_h_not_in_list:
  "\<lbrakk> circ_list_tail s h p a x \<rbrakk> \<Longrightarrow> h \<notin> set a"
  by (induct a arbitrary: p x, auto)

lemma circ_list_tail_cong:
  "\<lbrakk> \<And>i. \<lbrakk> i \<in> set a; i \<noteq> h \<rbrakk> \<Longrightarrow> s i = s' i; h = h'; p = p'; a = a'; x = x' \<rbrakk>
     \<Longrightarrow> circ_list_tail s h p a x = circ_list_tail s' h' p' a' x'"
  apply clarsimp
  apply (case_tac "h' \<in> set a'")
   apply (metis circ_list_tail_h_not_in_list)
  apply (rule circ_list_tail_ign_ext')
  apply clarsimp
  apply metis
  done

end


end
