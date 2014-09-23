(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory ListRev
imports "../../AutoCorres"
begin

install_C_file "list_rev.c"

autocorres [heap_abs_syntax] "list_rev.c"

primrec
  list :: "lifted_globals \<Rightarrow> node_C ptr \<Rightarrow> node_C ptr list \<Rightarrow> bool"
where
  "list s p [] = (p = NULL)"
| "list s p (x#xs) = (
       p = x \<and> p \<noteq> NULL \<and> is_valid_node_C s p \<and> list s (s[p]\<rightarrow>next) xs)"

lemma list_empty [simp]:
  "list s NULL xs = (xs = [])"
  by (induct xs) auto

lemma list_in [simp]:
  "\<lbrakk> list s p xs; p \<noteq> NULL \<rbrakk> \<Longrightarrow> p \<in> set xs"
  by (induct xs) auto

lemma list_non_NULL:
  "\<lbrakk> p \<noteq> NULL \<rbrakk> \<Longrightarrow>
    list s p xs = (\<exists>ys. xs = p # ys \<and> is_valid_node_C s p \<and> list s (s[p]\<rightarrow>next) ys)"
  by (cases xs) auto

lemma list_unique:
  "list s p xs \<Longrightarrow> list s p ys \<Longrightarrow> xs = ys"
  by (induct xs arbitrary: p ys) (auto simp add: list_non_NULL)

lemma list_append_Ex:
  "list s p (xs @ ys) \<Longrightarrow> (\<exists>q. list s q ys)"
  by (induct xs arbitrary: p) auto

lemma list_distinct [simp]:
  "list s p xs \<Longrightarrow> distinct xs"
  apply (induct xs arbitrary: p)
   apply simp
  apply (clarsimp dest!: split_list)
  apply (frule list_append_Ex)
  apply (auto dest: list_unique)
  done

lemma list_heap_update_ignore [simp]:
  "q \<notin> set xs \<Longrightarrow> list (s[q\<rightarrow>next := v]) p xs = list s p xs"
  apply (induct xs arbitrary: p)
   apply clarsimp
  apply (clarsimp simp: fun_upd_def)
  done

definition
  the_list :: "lifted_globals \<Rightarrow> node_C ptr \<Rightarrow> node_C ptr list"
where
  "the_list s p = (THE xs. list s p xs)"

lemma the_list_val [simp]: "list s p xs \<Longrightarrow> the_list s p = xs"
  apply (clarsimp simp: the_list_def)
  apply (metis (lifting) list_unique the_equality)
  done

lemma [simp]:
   "\<lbrakk> q \<notin> set xs; list s p xs \<rbrakk> \<Longrightarrow> the_list s[q\<rightarrow>next := v] p = the_list s p"
  apply (subgoal_tac "list s[q\<rightarrow>next := v] p xs")
   apply (metis the_list_val)
  apply clarsimp
  done

definition "reverse_inv xs list' rev' s =
                 (\<exists>ys zs. list s list' ys
                    \<and> list s rev' zs
                    \<and> rev xs = rev ys @ zs
                    \<and> distinct (rev xs))"

lemma (in list_rev) reverse_correct:
  "\<lbrace> \<lambda>s. list s p xs \<rbrace>
     reverse' p
   \<lbrace> \<lambda>rv s. list s rv (rev xs) \<rbrace>!"
  apply (clarsimp simp: reverse'_def)
  apply (subst whileLoop_add_inv [where
        I="\<lambda>(list', rev') s. reverse_inv xs list' rev' s"
        and M="\<lambda>((list', rev'), s). length (the_list s list')",
        unfolded reverse_inv_def])
  apply wp
    apply (clarsimp simp del: distinct_rev)
    apply (case_tac ys, fastforce)
    apply (clarsimp simp del: distinct_rev)
    apply (rule_tac x=lista in exI)
    apply (simp add: fun_upd_def)
   apply (clarsimp simp del: distinct_rev)
  apply simp
  done

end
