(*
 * @TAG(OTHER_BSD)
 *)
(*
 * Copyright (C) 2002 Tobias Nipkow (TUM)
 * Copyright (C) 2013--2014 Japheth Lim (NICTA)
 * Copyright (C) 2013--2014 David Greenaway (NICTA)
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * * Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * * Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * * Neither the name of the University of Cambridge or the Technische
 * Universitaet Muenchen nor the names of their contributors may be used
 * to endorse or promote products derived from this software without
 * specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *)

theory CList imports
  "../../AutoCorres"
begin

install_C_file "list.c"
autocorres "list.c"

context list begin

thm reverse'_def
thm revappend'_def

section "The heap"

subsection "Paths in the heap"

definition node_next where "node_next s p = next_C (heap_node_C s p)"
definition node_exists where "node_exists s p = (p \<noteq> NULL \<and> is_valid_node_C s p)"

definition node_next_upd where
  "node_next_upd s p q = heap_node_C_update (\<lambda>old. old(p := next_C_update (\<lambda>_. q) (old p))) s"

lemma "p \<noteq> x \<Longrightarrow> heap_node_C (node_next_upd s x q) p = heap_node_C s p"
by (simp add: node_next_def node_next_upd_def fun_upd_apply)
lemma [simp]: "node_next (node_next_upd s p q) p = q"
by (simp add: node_next_def node_next_upd_def fun_upd_apply)
lemma [simp]: "p \<noteq> x \<Longrightarrow> node_next (node_next_upd s x q) p = node_next s p"
by (simp add: node_next_def node_next_upd_def fun_upd_apply)
lemma "node_next_upd (node_next_upd s p a) p b = node_next_upd s p b"
by (simp add: node_next_def node_next_upd_def fun_upd_apply)
lemma [simp]: "node_exists (node_next_upd s q x) p = node_exists s p"
by (simp add: node_exists_def node_next_upd_def fun_upd_apply)
lemma "p \<noteq> q \<Longrightarrow> node_next (node_next_upd s q x) p = node_next s p"
by (simp add: node_next_def node_next_upd_def fun_upd_apply)

primrec Path :: "lifted_globals \<Rightarrow> node_C ptr \<Rightarrow> node_C ptr list \<Rightarrow> node_C ptr \<Rightarrow> bool" where
  "Path s x [] y \<longleftrightarrow> x = y"
| "Path s x (a#as) y \<longleftrightarrow> node_exists s x \<and> x = a \<and> Path s (node_next s x) as y"

lemma [iff]: "Path s NULL xs y = (xs = [] \<and> y = NULL)"
by (case_tac xs, fastforce, fastforce simp: node_exists_def)

lemma [simp]: "node_exists s a \<Longrightarrow> Path s a as z =
(as = [] \<and> a = z   \<or>   (\<exists>bs. as = a # bs \<and> Path s (node_next s a) bs z))"
by (case_tac as, fastforce, fastforce simp: node_exists_def)

lemma [simp]: "\<And>x. Path s x (as@bs) z =
(\<exists>y. Path s x as y \<and> Path s y bs z)"
by (induct as, simp+)

lemma Path_upd[simp]:
"\<And>x. u \<notin> set as \<Longrightarrow>
Path (node_next_upd s u v) x as y = Path s x as y"
apply (induct as, simp)
apply (simp add: node_exists_def node_next_def node_next_upd_def fun_upd_apply)
done

lemma Path_snoc:
"\<lbrakk> node_exists s a; Path (node_next_upd s a q) p as a \<rbrakk> \<Longrightarrow> Path (node_next_upd s a q) p (as @ [a]) q"
by simp


subsection "Non-repeating paths"

definition distPath ::
  "lifted_globals \<Rightarrow> node_C ptr \<Rightarrow> node_C ptr list \<Rightarrow> node_C ptr \<Rightarrow> bool"
  where "distPath s x as y \<longleftrightarrow> Path s x as y \<and> distinct as"

text{* The term @{term "distPath s x as y"} expresses the fact that a
non-repeating path @{term as} connects location @{term x} to location
@{term y} over the heap @{term s}. In the case where @{text "x = y"},
and there is a cycle from @{term x} to itself, @{term as} can
be both @{term "[]"} and the non-repeating list of nodes in the
cycle. *}

lemma neq_dP: "p \<noteq> q \<Longrightarrow> Path s p Ps q \<Longrightarrow> distinct Ps \<Longrightarrow>
 \<exists> a Qs. p = a & Ps = a#Qs & a \<notin> set Qs"
by (case_tac Ps, auto)


lemma neq_dP_disp: "\<lbrakk> p \<noteq> q; distPath s p Ps q \<rbrakk> \<Longrightarrow>
 \<exists> a Qs. p = a \<and> Ps = a#Qs \<and> a \<notin> set Qs"
apply (simp only:distPath_def)
by (case_tac Ps, auto)


subsection "Lists on the heap"

subsubsection "Relational abstraction"

definition List :: "lifted_globals \<Rightarrow> node_C ptr \<Rightarrow> node_C ptr list \<Rightarrow> bool"
  where "List s x as = Path s x as NULL"

lemma [simp]: "List s x [] = (x = NULL)"
by(simp add:List_def)

lemma List_case [simp]: "List s x (a#as) = (x = a \<and> node_exists s a \<and> List s (node_next s a) as)"
by(auto simp:List_def)

lemma [simp]: "List s NULL as = (as = [])"
by(case_tac as, simp_all add: node_exists_def)

lemma List_Ref[simp]: "node_exists s a \<Longrightarrow> List s a as = (\<exists>bs. as = a#bs \<and> List s (node_next s a) bs)"
by(case_tac as, simp_all add: node_exists_def, fast)

theorem notin_List_update[simp]:
 "\<And>x. \<lbrakk> node_exists s a; a \<notin> set as \<rbrakk> \<Longrightarrow> List (node_next_upd s a y) x as = List s x as"
apply(induct as)
apply simp
apply(clarsimp simp add:fun_upd_apply)
done

lemma List_unique: "\<And>x bs. List s x as \<Longrightarrow> List s x bs \<Longrightarrow> as = bs"
by(induct as, simp, clarsimp)

lemma List_unique1: "List s p as \<Longrightarrow> \<exists>!as. List s p as"
by(blast intro:List_unique)

lemma List_app: "\<And>x. List s x (as@bs) = (\<exists>y. Path s x as y \<and> List s y bs)"
by(induct as, simp, auto)

lemma List_hd_not_in_tl[simp]: "List s (node_next s a) as \<Longrightarrow> a \<notin> set as"
apply(clarsimp simp add:in_set_conv_decomp)
apply(frule List_app[THEN iffD1])
apply(fastforce dest: List_unique)
done

lemma List_distinct[simp]: "\<And>x. List s x as \<Longrightarrow> distinct as"
apply(induct as, simp)
apply(fastforce dest:List_hd_not_in_tl)
done

lemma Path_is_List:
  "\<lbrakk>node_exists s a; Path s b Ps a; a \<notin> set Ps\<rbrakk> \<Longrightarrow> List (node_next_upd s a NULL) b (Ps @ [a])"
apply (induct Ps arbitrary: b)
apply (auto simp: node_exists_def node_next_upd_def node_next_def fun_upd_apply)
done



subsection "Functional abstraction"

definition islist :: "lifted_globals \<Rightarrow> node_C ptr \<Rightarrow> bool"
  where "islist s p \<longleftrightarrow> (\<exists>as. List s p as)"

definition list :: "lifted_globals \<Rightarrow> node_C ptr \<Rightarrow> node_C ptr list"
  where "list s p = (SOME as. List s p as)"

lemma List_conv_islist_list: "List s p as = (islist s p \<and> as = list s p)"
apply(simp add:islist_def list_def)
apply(rule iffI)
apply(rule conjI)
apply blast
apply(subst some1_equality)
  apply(erule List_unique1)
 apply assumption
apply(rule refl)
apply simp
apply(rule someI_ex)
apply fast
done

lemma [simp]: "islist s NULL"
by(simp add:islist_def)

lemma [simp]: "node_exists s a \<Longrightarrow> islist s a = islist s (node_next s a)"
by(simp add:islist_def)

lemma [simp]: "\<lbrakk> node_exists s a; islist s a \<rbrakk> \<Longrightarrow> islist s (node_next s a)"
apply (clarsimp simp: islist_def)
done

lemma [simp]: "list s NULL = []"
by(simp add:list_def)

lemma list_Ref_conv[simp]:
 "\<lbrakk> node_exists s a; islist s (node_next s a) \<rbrakk> \<Longrightarrow> list s a = a # list s (node_next s a)"
apply(insert List_Ref[of s])
apply(metis List_conv_islist_list)
done

lemma [simp]: "\<lbrakk> node_exists s a; islist s (node_next s a) \<rbrakk> \<Longrightarrow> a \<notin> set(list s (node_next s a))"
apply(insert List_hd_not_in_tl[of s])
apply(metis List_conv_islist_list)
done

lemma list_upd_conv[simp]:
 "islist s p \<Longrightarrow> y \<notin> set(list s p) \<Longrightarrow> list (node_next_upd s y q) p = list s p"
  apply (clarsimp simp: islist_def node_next_upd_def)
  by (metis (mono_tags) list.List_def list.List_unique list.Path_upd list.list_def list.node_next_upd_def some_eq_ex)

lemma islist_upd[simp]:
 "islist s p \<Longrightarrow> y \<notin> set(list s p) \<Longrightarrow> islist (node_next_upd s y q) p"
  apply (clarsimp simp: islist_def node_next_upd_def)
  by (metis (mono_tags) list.List_def list.List_unique list.Path_upd list.list_def list.node_next_upd_def some_eq_ex)


subsection "List reversal"

subsubsection "Program representation"
text {* This is AutoCorres's representation of revappend. *}
thm revappend'_def

text {* The heap operations are a bit too low level,
        so let's lift them using our heap accessors. *}
schematic_goal revappend'_abstract: "revappend' p q = ?new_definition"
  apply (subst revappend'_def)
  unfolding node_next_def[symmetric]
            node_next_upd_def[symmetric]
            modify_def
  apply (rule refl)
  done


text {* node_exists is a prerequisite for most of our abstraction rules.
        But we cannot extract this prerequisite from the program text because it is
        implied by our Hoare preconditions (below) which are not a part of the program
        text. Here we arrange for Isabelle's tactics to infer it when needed. *}

(* FIXME: figure out why we need to take this out of the simpset for
          the loop termination subgoals. *)
lemma node_exists_imp_valid[simp]: "node_exists s b \<Longrightarrow> is_valid_node_C s b"
  by (simp add: node_exists_def)

lemma List_node_exists [dest!]: "\<lbrakk> p \<noteq> NULL; List s p as \<rbrakk> \<Longrightarrow> node_exists s p"
by (case_tac as, auto simp: node_exists_def)

lemma islist_node_exists [simp]: "\<lbrakk> p \<noteq> NULL; islist s p \<rbrakk> \<Longrightarrow> node_exists s p"
  apply (clarsimp simp: islist_def)
  apply (rename_tac a, case_tac a, simp_all add: node_exists_def)
  done



subsubsection "Verification with relational abstraction"
text {* Almost automatic proof using the relational abstraction.
        (The termination proof uses functional abstraction.) *}

lemma
"\<lbrace> \<lambda>s. List s p Ps \<and> List s q Qs \<and> set Ps \<inter> set Qs = {} \<rbrace>
   revappend' p q
 \<lbrace> \<lambda>r s. List s r (rev Ps @ Qs) \<rbrace>!"
  txt {* We verify the abstracted version of the program. *}
  unfolding revappend'_abstract

  txt {* Add the loop invariant and measure. *}
  apply (subst whileLoop_add_inv
    [where I = "\<lambda>(dest', list') s.
                 \<exists>ps qs. List s list' ps \<and> List s dest' qs \<and> set ps \<inter> set qs = {} \<and>
                         rev ps @ qs = rev Ps @ Qs"
       and M = " (\<lambda>((_, list'), s). length (list s list'))"])
  apply (wp validNF_whileLoop_inv_measure_twosteps)

  txt {* Loop invariant. *}
    apply (fastforce intro: notin_List_update[THEN iffD2])

  txt {* Loop measure. *}
    apply wp
    apply (fastforce simp: List_conv_islist_list simp del: node_exists_imp_valid)

  txt {* Loop entrance and exit. *}
   apply fastforce+
  done



subsubsection "Verification with functional abstraction"
text {* Fully automatic proof using the functional abstraction. *}
lemma
"\<lbrace> \<lambda>s. islist s p \<and> islist s q \<and> Ps = list s p \<and> Qs = list s q \<and> set Ps \<inter> set Qs = {} \<rbrace>
   revappend' p q
 \<lbrace> \<lambda>r s. islist s r \<and> list s r = rev Ps @ Qs \<rbrace>!"
  unfolding revappend'_abstract

  apply (subst whileLoop_add_inv
    [where I = "\<lambda>(q, p) s. islist s p \<and> islist s q \<and>
                           set(list s p) \<inter> set(list s q) = {} \<and>
                           rev(list s p) @ (list s q) = rev Ps @ Qs"
       and M = "(\<lambda>((q, p), s). length (list s p))"])
  apply (wp validNF_whileLoop_inv_measure_twosteps)

  txt {* Loop invariant. *}
     apply clarsimp

  txt {* Loop measure. *}
    apply wp
    apply (clarsimp simp del: node_exists_imp_valid)

  txt {* Loop entrance and exit. *}
   apply clarsimp+
  done

text {* Provide the node_exists condition manually. *}
lemma
"\<lbrace> \<lambda>s. islist s p \<and> islist s q \<and> Ps = list s p \<and> Qs = list s q \<and> set Ps \<inter> set Qs = {} \<rbrace>
   revappend' p q
 \<lbrace> \<lambda>r s. islist s r \<and> list s r = rev Ps @ Qs \<rbrace>!"
  unfolding revappend'_abstract

  apply (subst whileLoop_add_inv
    [where I = "\<lambda>(q, p) s. islist s p \<and> islist s q \<and>
                           set(list s p) \<inter> set(list s q) = {} \<and>
                           rev(list s p) @ (list s q) = rev Ps @ Qs"
       and M = "(\<lambda>((q, p), s). length (list s p))"])
  apply (wp validNF_whileLoop_inv_measure_twosteps)
     apply (clarsimp simp del: islist_node_exists)
     apply (frule islist_node_exists, assumption)
     apply (clarsimp simp del: islist_node_exists)

    apply wp
    apply (clarsimp simp del: node_exists_imp_valid)

   apply clarsimp+
  done

end (* context list *)

end
