(*
 * @TAG(OTHER_BSD)
 *)
(*
 * Copyright (C) 2003 Farhad Mehta (TUM)
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

(*
 * This file contains a proof of a C implementation of the Schorr-Waite
 * graph marking algorithm.
 *
 * The original proof was carried out by Farhad Mehta, and is
 * distributed as part of Isabelle 2013-2.
 *
 * The proof minimally modified to hook up to the output of AutoCorres
 * by Japheth Lim and David Greenaway. Japheth Lim additionally modified
 * the proof to show fault-avoidence and termination.
 *)
theory SchorrWaite imports
  "~~/src/HOL/Library/Product_Lexorder"
  "../../AutoCorres"
begin

declare fun_upd_apply[simp del]

install_C_file "schorr_waite.c"
autocorres [heap_abs_syntax] "schorr_waite.c"

(* AutoCorres doesn't successfully recognize all boolean variables yet,
   so this saves us some typing *)
abbreviation Cbool where "Cbool b \<equiv> if b then 1 else 0"

declare fun_upd_apply [simp]

(*** Base List definitions ***)

section "The heap"

subsection "Paths in the heap"

primrec Path :: "('p ptr \<Rightarrow> 'p ptr) \<Rightarrow> 'p ptr \<Rightarrow> 'p ptr list \<Rightarrow> 'p ptr \<Rightarrow> bool" where
  "Path s x [] y = (x = y)"
| "Path s x (a#as) y = (x \<noteq> NULL \<and> x = a \<and> Path s (s x) as y)"

lemma [iff]: "Path h NULL xs y = (xs = [] \<and> y = NULL)"
apply(case_tac xs)
apply fastforce
apply fastforce
done

lemma [simp]: "a \<noteq> NULL \<Longrightarrow> Path h a as z =
 (as = [] \<and> z = a \<or>  (\<exists>bs. as = a#bs \<and> Path h (h a) bs z))"
apply(case_tac as)
apply fastforce
apply fastforce
done

lemma [simp]: "\<And>x. Path f x (as@bs) z = (\<exists>y. Path f x as y \<and> Path f y bs z)"
by(induct as, simp+)

lemma Path_upd[simp]:
 "\<And>x. u \<notin> set as \<Longrightarrow> Path (f(u := v)) x as y = Path f x as y"
by(induct as, simp, simp add:eq_sym_conv)

lemma Path_snoc:
 "a \<noteq> NULL \<Longrightarrow> Path (f(a := q)) p as a \<Longrightarrow> Path (f(a := q)) p (as @ [a]) q"
by simp


subsection "Lists on the heap"

subsubsection "Relational abstraction"

definition List :: "('a ptr \<Rightarrow> 'a ptr) \<Rightarrow> 'a ptr \<Rightarrow> 'a ptr list \<Rightarrow> bool"
  where "List h x as = Path h x as NULL"

lemma [simp]: "List h x [] = (x = NULL)"
by(simp add:List_def)

lemma [simp]: "List h x (a#as) = (x \<noteq> NULL \<and> x = a \<and> List h (h x) as)"
by(simp add:List_def)

lemma [simp]: "List h NULL as = (as = [])"
by(case_tac as, simp_all)

lemma List_Ref[simp]: "a \<noteq> NULL \<Longrightarrow> List h a as = (\<exists>bs. as = a#bs \<and> List h (h a) bs)"
by(case_tac as, simp_all, fast)

theorem notin_List_update[simp]:
 "\<And>x. a \<notin> set as \<Longrightarrow> List (h(a := y)) x as = List h x as"
apply(induct as)
apply simp
apply(clarsimp simp add:fun_upd_apply)
done

lemma List_unique: "\<And>x bs. List h x as \<Longrightarrow> List h x bs \<Longrightarrow> as = bs"
by(induct as, simp, clarsimp)

lemma List_unique1: "List h p as \<Longrightarrow> \<exists>!as. List h p as"
by(blast intro:List_unique)

lemma List_app: "\<And>x. List h x (as@bs) = (\<exists>y. Path h x as y \<and> List h y bs)"
by(induct as, simp, clarsimp)

lemma List_hd_not_in_tl[simp]: "List h (h a) as \<Longrightarrow> a \<notin> set as"
apply (clarsimp simp add:in_set_conv_decomp)
apply(frule List_app[THEN iffD1])
apply(fastforce dest: List_unique)
done

lemma List_distinct[simp]: "\<And>x. List h x as \<Longrightarrow> distinct as"
apply(induct as, simp)
apply(fastforce dest:List_hd_not_in_tl)
done

lemma Path_is_List:
  "\<lbrakk> Path h b Ps a; a \<notin> set Ps; a \<noteq> NULL \<rbrakk> \<Longrightarrow> List (h(a := NULL)) b (Ps @ [a])"
apply (induct Ps arbitrary: b)
apply (auto simp add:fun_upd_apply)
done

lemma List_eq_select [elim]: "\<lbrakk> List s p xs; \<forall>x \<in> set xs. s x = t x \<rbrakk> \<Longrightarrow> List t p xs"
by (induct xs arbitrary: p) auto

(*** Main Proof ***)

section {* Machinery for the Schorr-Waite proof*}

definition
  -- "Relations induced by a mapping"
  rel :: "('a ptr \<Rightarrow> 'a ptr) \<Rightarrow> ('a ptr \<times> 'a ptr) set"
  where "rel m = {(x,y). m x = y \<and> y \<noteq> NULL}"

definition
  relS :: "('a ptr \<Rightarrow> 'a ptr) set \<Rightarrow> ('a ptr \<times> 'a ptr) set"
  where "relS M = (\<Union> m \<in> M. rel m)"

definition
  addrs :: "'a ptr set \<Rightarrow> 'a ptr set"
  where "addrs P = {a \<in> P. a \<noteq> NULL}"

definition
  reachable :: "('a ptr \<times> 'a ptr) set \<Rightarrow> 'a ptr set \<Rightarrow> 'a ptr set"
  where "reachable r P = (r\<^sup>* `` addrs P)"

lemmas rel_defs = relS_def rel_def

text {* Rewrite rules for relations induced by a mapping*}

lemma self_reachable: "b \<in> B \<Longrightarrow> b \<in> R\<^sup>* `` B"
apply blast
done

lemma oneStep_reachable: "b \<in> R``B \<Longrightarrow> b \<in> R\<^sup>* `` B"
apply blast
done

lemma still_reachable: "\<lbrakk>B\<subseteq>Ra\<^sup>*``A; \<forall> (x,y) \<in> Rb-Ra. y\<in> (Ra\<^sup>*``A)\<rbrakk> \<Longrightarrow> Rb\<^sup>* `` B \<subseteq> Ra\<^sup>* `` A "
apply (clarsimp simp only:Image_iff)
apply (erule rtrancl_induct)
 apply blast
apply (subgoal_tac "(y, z) \<in> Ra\<union>(Rb-Ra)")
 apply (erule UnE)
 apply (auto intro:rtrancl_into_rtrancl)
apply blast
done

lemma still_reachable_eq: "\<lbrakk> A\<subseteq>Rb\<^sup>*``B; B\<subseteq>Ra\<^sup>*``A; \<forall> (x,y) \<in> Ra-Rb. y \<in>(Rb\<^sup>*``B); \<forall> (x,y) \<in> Rb-Ra. y\<in> (Ra\<^sup>*``A)\<rbrakk> \<Longrightarrow> Ra\<^sup>*``A =  Rb\<^sup>*``B "
apply (rule equalityI)
 apply (erule still_reachable ,assumption)+
done

lemma reachable_null: "reachable mS {NULL} = {}"
apply (simp add: reachable_def addrs_def)
done

lemma reachable_empty: "reachable mS {} = {}"
apply (simp add: reachable_def addrs_def)
done

lemma reachable_union: "(reachable mS aS \<union> reachable mS bS) = reachable mS (aS \<union> bS)"
apply (simp add: reachable_def rel_defs addrs_def)
apply blast
done

lemma reachable_union_sym: "reachable r (insert a aS) = (r\<^sup>* `` addrs {a}) \<union> reachable r aS"
apply (simp add: reachable_def rel_defs addrs_def)
apply blast
done

lemma rel_upd1: "(a,b) \<notin> rel (r(q:=t)) \<Longrightarrow> (a,b) \<in> rel r \<Longrightarrow> a=q"
apply (rule classical)
apply (simp add:rel_defs fun_upd_apply)
done

lemma rel_upd2: "(a,b)  \<notin> rel r \<Longrightarrow> (a,b) \<in> rel (r(q:=t)) \<Longrightarrow> a=q"
apply (rule classical)
apply (simp add:rel_defs fun_upd_apply)
done

definition
  -- "Restriction of a relation"
  restr ::"('a ptr \<times> 'a ptr) set \<Rightarrow> ('a ptr \<Rightarrow> bool) \<Rightarrow> ('a ptr \<times> 'a ptr) set"       ("(_/ | _)" [50, 51] 50)
  where "restr r m = {(x,y). (x,y) \<in> r \<and> \<not> m x}"

text {* Rewrite rules for the restriction of a relation *}

lemma restr_identity[simp]:
 " (\<forall>x. \<not> m x) \<Longrightarrow> (R |m) = R"
by (auto simp add:restr_def)

lemma restr_rtrancl[simp]: " \<lbrakk>m l\<rbrakk> \<Longrightarrow> (R | m)\<^sup>* `` {l} = {l}"
by (auto simp add:restr_def elim:converse_rtranclE)

lemma [simp]: " \<lbrakk>m l\<rbrakk> \<Longrightarrow> (l,x) \<in> (R | m)\<^sup>* = (l=x)"
by (auto simp add:restr_def elim:converse_rtranclE)

lemma restr_upd: "((rel (r (q := t)))|(m(q := True))) = ((rel (r))|(m(q := True))) "
apply (auto simp:restr_def rel_def fun_upd_apply)
done

lemma restr_un: "((r \<union> s)|m) = (r|m) \<union> (s|m)"
  by (auto simp add:restr_def)

lemma rel_upd3: "(a, b) \<notin> (r|(m(q := t))) \<Longrightarrow> (a,b) \<in> (r|m) \<Longrightarrow> a = q "
apply (rule classical)
apply (simp add:restr_def fun_upd_apply)
done

definition
  -- "A short form for the stack mapping function for List"
  S :: "('a ptr \<Rightarrow> bool) \<Rightarrow> ('a ptr \<Rightarrow> 'a ptr) \<Rightarrow> ('a ptr \<Rightarrow> 'a ptr) \<Rightarrow> ('a ptr \<Rightarrow> 'a ptr)"
  where "S c l r = (\<lambda>x. if c x then r x else l x)"

text {* Rewrite rules for Lists using S as their mapping *}

lemma [rule_format,simp]:
 "\<forall>p. a \<notin> set stack \<longrightarrow> List (S c l r) p stack = List (S (c(a:=x)) (l(a:=y)) (r(a:=z))) p stack"
apply(induct_tac stack)
 apply(simp add:fun_upd_apply S_def)+
done

lemma [rule_format,simp]:
 "\<forall>p. a \<notin> set stack \<longrightarrow> List (S c l (r(a:=z))) p stack = List (S c l r) p stack"
apply(induct_tac stack)
 apply(simp add:fun_upd_apply S_def)+
done

lemma [rule_format,simp]:
 "\<forall>p. a \<notin> set stack \<longrightarrow> List (S c (l(a:=z)) r) p stack = List (S c l r) p stack"
apply(induct_tac stack)
 apply(simp add:fun_upd_apply S_def)+
done

lemma [rule_format,simp]:
 "\<forall>p. a \<notin> set stack \<longrightarrow> List (S (c(a:=z)) l r) p stack = List (S c l r) p stack"
apply(induct_tac stack)
 apply(simp add:fun_upd_apply S_def)+
done

primrec
  --"Recursive definition of what is means for a the graph/stack structure to be reconstructible"
  stkOk :: "('a ptr \<Rightarrow> bool) \<Rightarrow> ('a ptr \<Rightarrow> 'a ptr) \<Rightarrow> ('a ptr \<Rightarrow> 'a ptr) \<Rightarrow> ('a ptr \<Rightarrow> 'a ptr) \<Rightarrow> ('a ptr \<Rightarrow> 'a ptr) \<Rightarrow> 'a ptr \<Rightarrow>'a ptr list \<Rightarrow>  bool"
where
  stkOk_nil:  "stkOk c l r iL iR t [] = True"
| stkOk_cons:
    "stkOk c l r iL iR t (p#stk) = (stkOk c l r iL iR p stk \<and>
      iL p = (if c p then l p else t) \<and>
      iR p = (if c p then t else r p) \<and>
      p \<noteq> NULL)"

text {* Rewrite rules for stkOk *}

lemma [simp]: "\<And>t. \<lbrakk> x \<notin> set xs; x \<noteq> t \<rbrakk> \<Longrightarrow>
  stkOk (c(x := f)) l r iL iR t xs = stkOk c l r iL iR t xs"
apply (induct xs)
 apply (auto simp:eq_sym_conv)
done

lemma [simp]: "\<And>t. \<lbrakk> x \<notin> set xs; x\<noteq>t \<rbrakk> \<Longrightarrow>
 stkOk c (l(x := g)) r iL iR t xs = stkOk c l r iL iR t xs"
apply (induct xs)
 apply (auto simp:eq_sym_conv)
done

lemma [simp]: "\<And>t. \<lbrakk> x \<notin> set xs; x\<noteq>t \<rbrakk> \<Longrightarrow>
 stkOk c l (r(x := g)) iL iR t xs = stkOk c l r iL iR t xs"
apply (induct xs)
 apply (auto simp:eq_sym_conv)
done

lemma stkOk_r_rewrite [simp]: "\<And>x. x \<notin> set xs \<Longrightarrow>
  stkOk c l (r(x := g)) iL iR x xs = stkOk c l r iL iR x xs"
apply (induct xs)
 apply (auto simp:eq_sym_conv)
done

lemma [simp]: "\<And>x. x \<notin> set xs \<Longrightarrow>
 stkOk c (l(x := g)) r iL iR x xs = stkOk c l r iL iR x xs"
apply (induct xs)
 apply (auto simp:eq_sym_conv)
done

lemma [simp]: "\<And>x. x \<notin> set xs \<Longrightarrow>
 stkOk (c(x := g)) l r iL iR x xs = stkOk c l r iL iR x xs"
apply (induct xs)
 apply (auto simp:eq_sym_conv)
done

lemma stkOk_eq_select[elim]:
"\<lbrakk> stkOk s a b c d p xs; \<forall>x \<in> set xs. s x = t x \<rbrakk> \<Longrightarrow> stkOk t a b c d p xs"
by (induct xs arbitrary: p) auto

definition measure :: "('a \<Rightarrow> ('n :: wellorder)) \<Rightarrow> ('a \<times> 'a) set"
where
  "measure r \<equiv> {(s', s). r s' < r s}"

lemma in_measure[simp, code_unfold]: "((x,y) : measure f) = (f x < f y)"
  by (simp add:measure_def)

lemma wf_measure [iff]: "wf (measure f)"
apply (unfold measure_def)
by (metis wf_wellorder_measure)

context schorr_waite begin

abbreviation schorr_waite'_inv where
  "schorr_waite'_inv s s0 R p t cond stack \<equiv>
     (*i1*) List (S (\<lambda>x. s[x]\<rightarrow>c \<noteq> 0) (\<lambda>x. s[x]\<rightarrow>l) (\<lambda>x. s[x]\<rightarrow>r)) p stack \<and>
     (*i2*) (\<forall>x \<in> set stack. s[x]\<rightarrow>m \<noteq> 0) \<and>
     (*i3*) R = reachable (relS {\<lambda>x. s[x]\<rightarrow>l, \<lambda>x. s[x]\<rightarrow>r}) {t, p} \<and>
     (*i4*) (\<forall>x. x \<in> R \<and> s[x]\<rightarrow>m = 0 \<longrightarrow>
                   x \<in> reachable (restr (relS {\<lambda>x. s[x]\<rightarrow>l, \<lambda>x. s[x]\<rightarrow>r}) (\<lambda>x. s[x]\<rightarrow>m \<noteq> 0))
                                 ({t} \<union> set (map (\<lambda>x. s[x]\<rightarrow>r) stack))) \<and>
     (*i5*) (\<forall>x. s[x]\<rightarrow>m \<noteq> 0 \<longrightarrow> x \<in> R) \<and>
     (*i6*) (\<forall>x. x \<notin> set stack \<longrightarrow> s[x]\<rightarrow>r = s0[x]\<rightarrow>r \<and> s[x]\<rightarrow>l = s0[x]\<rightarrow>l) \<and>
     (*i7*) (stkOk (\<lambda>x. s[x]\<rightarrow>c \<noteq> 0) (\<lambda>x. s[x]\<rightarrow>l) (\<lambda>x. s[x]\<rightarrow>r) (\<lambda>x. s0[x]\<rightarrow>l) (\<lambda>x. s0[x]\<rightarrow>r) t stack) \<and>
     (*i8*) (\<forall>x. x \<in> R \<longrightarrow> is_valid_node_C s x) \<and>
     (*i9*) cond = Cbool (p = NULL \<longrightarrow> (t \<noteq> NULL \<and> s[t]\<rightarrow>m = 0))"

abbreviation schorr_waite'_measure where
  "schorr_waite'_measure s s0 R p t cond \<equiv>
     let stack = (THE stack. schorr_waite'_inv s s0 R p t cond stack)
     in (card {x \<in> R. s[x]\<rightarrow>m = 0}, card {x \<in> set stack. s[x]\<rightarrow>c = 0}, length stack)"

schematic_goal schorr_waite'_prove_def:
  "schorr_waite' root_ptr \<equiv> ?A root_ptr (s0 :: lifted_globals) (R :: node_C ptr set)"
  apply (subst schorr_waite'_def[abs_def])
  apply (subst whileLoop_add_inv
           [where I = "\<lambda>(p, cond, t) s. \<exists>stack. schorr_waite'_inv s s0 R p t cond stack"
              and M = "(\<lambda>((p, cond, t), s). schorr_waite'_measure s s0 R p t cond)"])
  apply (rule reflexive)
  done

(* Helper for the termination proof. *)
lemma the_equality': "\<And>P a. \<lbrakk>P a; \<And>x. \<lbrakk> P a; P x \<rbrakk> \<Longrightarrow> x = a\<rbrakk> \<Longrightarrow> (THE x. P x) = a"
  by blast

(* Hypothetical "wp_all" tactic *)
ML {*
fun wp_all_tac ctxt = let fun f n thm =
      if n > Thm.nprems_of thm then Seq.single thm else
        let val thms = WeakestPre.apply_rules_tac_n false
                         ctxt [] (Unsynchronized.ref []) n thm
                       |> Seq.list_of
        in if null thms then f (n+1) thm else f n (hd thms) end
     in f 0 end
*}

(*** Main Proof ***)

declare fun_upd_apply[simp del] fun_upd_same[simp] fun_upd_other[simp]
declare validNF_whileLoop_inv_measure_twosteps [wp]

section{*The Schorr-Waite algorithm*}

theorem SchorrWaiteAlgorithm:
"\<lbrace>\<lambda>s. R = reachable (relS {\<lambda>x. s[x]\<rightarrow>l, \<lambda>x. s[x]\<rightarrow>r}) {root_ptr} \<and>
      (\<forall>x. s[x]\<rightarrow>m = 0) \<and> s0 = s \<and> (\<forall>x\<in>R. is_valid_node_C s x)
      (* \<and> finite R (* unnecessary because ptr \<approx> word32 *) *) \<rbrace>
  schorr_waite' root_ptr
 \<lbrace>\<lambda>r s. \<forall>x. (x \<in> R) = (s[x]\<rightarrow>m \<noteq> 0) \<and> s[x]\<rightarrow>l = s0[x]\<rightarrow>l \<and> s[x]\<rightarrow>r = s0[x]\<rightarrow>r\<rbrace>!"
unfolding schorr_waite'_prove_def[of root_ptr R s0]

txt {* wp currently generates many tuples for the whileLoop state,
       we simplify them with the second simp rule. *}
proof (tactic "wp_all_tac @{context}",
    simp_all (no_asm_use) only: split_tupled_all split_conv)
  let "\<lbrace> ?Pre root_ptr \<rbrace> _ \<lbrace> ?Post \<rbrace>!" = ?thesis
  fix p :: "node_C ptr" and t :: "node_C ptr" and
      s :: "lifted_globals" and cond :: "int"
  let "?cond p t s" = "p = NULL \<longrightarrow> t \<noteq> NULL \<and> s[t]\<rightarrow>m = 0"
  let "?inv p t cond s" = "\<exists>stack. schorr_waite'_inv s s0 R p t cond stack"
  let "?measure p t cond s" = "schorr_waite'_measure s s0 R p t cond"

  let "\<exists>stack. ?Inv p t cond s stack" = "?inv p t cond s"

  {
    fix s
    assume "?Pre root_ptr s"
    thus "\<forall>x. ?inv NULL root_ptr (Cbool (root_ptr \<noteq> NULL \<and> s[root_ptr]\<rightarrow>m = 0)) s \<and>
              (root_ptr \<noteq> NULL \<longrightarrow> is_valid_node_C s root_ptr)"
      by (auto simp: reachable_def addrs_def)
  next

    fix x s p t cond
    assume a: "?inv p t cond s" and b: "\<not> cond \<noteq> 0"
    then obtain stack where inv: "?Inv p t cond s stack" by blast
    from a b have pNull: "p = NULL" and tDisj: "t=NULL \<or> (t\<noteq>NULL \<and> s[t]\<rightarrow>m \<noteq> 0)" by auto
    let "?I1 \<and> _ \<and> _ \<and> ?I4 \<and> ?I5 \<and> ?I6 \<and> _ \<and> _ \<and> _"  =  "?Inv p t cond s stack"
    from inv have i1: "?I1" and i4: "?I4" and i5: "?I5" and i6: "?I6" by simp+
    from pNull i1 have stackEmpty: "stack = []" by simp
    from tDisj i4 have RisMarked[rule_format]: "\<forall>x. x \<in> R \<longrightarrow> s[x]\<rightarrow>m \<noteq> 0" using inv by(auto simp: reachable_def addrs_def stackEmpty)
    from i5 i6 show "(x \<in> R) = (s[x]\<rightarrow>m \<noteq> 0) \<and> s[x]\<rightarrow>l = s0[x]\<rightarrow>l \<and> s[x]\<rightarrow>r = s0[x]\<rightarrow>r" by(auto simp: stackEmpty fun_eq_iff RisMarked)
  next

  {
    fix s p t cond stack_tl
    assume stackInv: "?Inv p t cond s (p # stack_tl)"
       and whileB: "cond \<noteq> 0" (is "?whileB")
       and ifB1: "t = NULL \<or> s[t]\<rightarrow>m \<noteq> 0" (is "?ifB1") and ifB2: "s[p]\<rightarrow>c \<noteq> 0" (is "?ifB2")
    let "?I1 \<and> ?I2 \<and> ?I3 \<and> ?I4 \<and> ?I5 \<and> ?I6 \<and> ?I7 \<and> ?I8 \<and> ?I9" = "?Inv p t cond s (p # stack_tl)"
    from stackInv have i1: "?I1" and i2: "?I2" and i3: "?I3" and i4: "?I4"
                   and i5: "?I5" and i6: "?I6" and i7: "?I7" and i8: "?I8"
                   and cond: "?I9" by simp+
    have stackDist: "distinct (p # stack_tl)" using i1 by (rule List_distinct)
      from whileB and ifB1 and cond have pNotNULL [iff]: "p \<noteq> NULL" by simp
    with i2 have m_p: "s[p]\<rightarrow>m \<noteq> 0" by auto
    from stackDist have p_notin_stack_tl: "p \<notin> set stack_tl" by simp
    let "?pop_s" = "s[p\<rightarrow>r := t]"
    have "?Inv (s[p]\<rightarrow>r) p (Cbool (?cond (s[p]\<rightarrow>r) p ?pop_s)) ?pop_s stack_tl"
          (is "?poI1\<and> ?poI2\<and> ?poI3\<and> ?poI4\<and> ?poI5\<and> ?poI6\<and> ?poI7\<and> ?poI8\<and> ?poI9")
    proof -
        -- {*List property is maintained:*}
      from i1 p_notin_stack_tl ifB2
        have poI1: "List (S (\<lambda>x. ?pop_s[x]\<rightarrow>c \<noteq> 0) (\<lambda>x. ?pop_s[x]\<rightarrow>l) (\<lambda>x. ?pop_s[x]\<rightarrow>r)) (s[p]\<rightarrow>r) stack_tl"
        by(simp, simp add: S_def)

      moreover
        -- {*Everything on the stack is marked:*}
      from i2 have poI2: "\<forall> x \<in> set stack_tl. s[x]\<rightarrow>m \<noteq> 0" by simp
      moreover

        -- {*Everything is still reachable:*}
      let "(R = reachable ?Ra ?A)" = "?I3"
        let "?Rb" = "relS {\<lambda>x. ?pop_s[x]\<rightarrow>l, \<lambda>x. ?pop_s[x]\<rightarrow>r}"
      let "?B" = "{p, s[p]\<rightarrow>r}"
        -- {*Our goal is @{text"R = reachable ?Rb ?B"}.*}
      have "?Ra\<^sup>* `` addrs ?A = ?Rb\<^sup>* `` addrs ?B" (is "?L = ?R")
      proof
        show "?L \<subseteq> ?R"
        proof (rule still_reachable)
          show "addrs ?A \<subseteq> ?Rb\<^sup>* `` addrs ?B"
              by(fastforce simp:addrs_def relS_def rel_def
                         intro:oneStep_reachable Image_iff[THEN iffD2])
          show "\<forall>(x,y) \<in> ?Ra-?Rb. y \<in> (?Rb\<^sup>* `` addrs ?B)"
            by (clarsimp simp:relS_def)
               (fastforce simp add:rel_def Image_iff addrs_def dest:rel_upd1)
        qed
        show "?R \<subseteq> ?L"
        proof (rule still_reachable)
            show "addrs ?B \<subseteq> ?Ra\<^sup>* `` addrs ?A"
              by (fastforce simp: addrs_def rel_defs
                          intro: oneStep_reachable Image_iff[THEN iffD2])
        next
          show "\<forall>(x, y)\<in>?Rb-?Ra. y\<in>(?Ra\<^sup>*``addrs ?A)"
            by (clarsimp simp:relS_def)
                 (fastforce simp add:rel_def Image_iff addrs_def dest:rel_upd2)
        qed
      qed
        with i3 have poI3: "R = reachable ?Rb ?B"  by (simp add:reachable_def)
      moreover

        -- "If it is reachable and not marked, it is still reachable using..."
      let "\<forall>x. x \<in> R \<and> s[x]\<rightarrow>m = 0 \<longrightarrow> x \<in> reachable ?Ra ?A"  =  ?I4
        let "?Rb" = "restr (relS {\<lambda>x. ?pop_s[x]\<rightarrow>l, \<lambda>x. ?pop_s[x]\<rightarrow>r}) (\<lambda>x. ?pop_s[x]\<rightarrow>m \<noteq> 0)"
        let "?B" = "{p} \<union> set (map (\<lambda>x. ?pop_s[x]\<rightarrow>r) stack_tl)"
        -- {*Our goal is @{text"\<forall>x. x \<in> R \<and> \<not> m x \<longrightarrow> x \<in> reachable ?Rb ?B"}.*}
      let ?T = "{t, s[p]\<rightarrow>r}"

      have "?Ra\<^sup>* `` addrs ?A \<subseteq> ?Rb\<^sup>* `` (addrs ?B \<union> addrs ?T)"
      proof (rule still_reachable)
          have rewrite: "\<forall>x\<in>set stack_tl. ?pop_s[x]\<rightarrow>r = s[x]\<rightarrow>r"
          by (auto simp add:p_notin_stack_tl intro:fun_upd_other)
        show "addrs ?A \<subseteq> ?Rb\<^sup>* `` (addrs ?B \<union> addrs ?T)"
            by (fastforce cong:map_cong simp:addrs_def rewrite fun_upd_apply intro:self_reachable)
        show "\<forall>(x, y)\<in>?Ra-?Rb. y\<in>(?Rb\<^sup>*``(addrs ?B \<union> addrs ?T))"
          by (clarsimp simp:restr_def relS_def)
              (fastforce simp add:rel_def Image_iff addrs_def dest:rel_upd1)
      qed
          -- "We now bring a term from the right to the left of the subset relation."
      hence subset: "?Ra\<^sup>* `` addrs ?A - ?Rb\<^sup>* `` addrs ?T \<subseteq> ?Rb\<^sup>* `` addrs ?B"
        by blast
        have poI4: "\<forall>x. x \<in> R \<and> ?pop_s[x]\<rightarrow>m = 0 \<longrightarrow> x \<in> reachable ?Rb ?B"
      proof (rule allI, rule impI)
        fix x
          assume a: "x \<in> R \<and> ?pop_s[x]\<rightarrow>m = 0"
          -- {*First, a disjunction on @{term "s[p]\<rightarrow>r"} used later in the proof*}
        have pDisj:"s[p]\<rightarrow>r = NULL \<or> (s[p]\<rightarrow>r \<noteq> NULL \<and> s[(s[p]\<rightarrow>r)]\<rightarrow>m \<noteq> 0)" using poI1 poI2
          by (case_tac stack_tl, auto simp: List_def)
            -- {*@{term x} belongs to the left hand side of @{thm[source] subset}:*}
        have incl: "x \<in> ?Ra\<^sup>*``addrs ?A" using  a i4 by (simp only:reachable_def, clarsimp)
          have excl: "x \<notin> ?Rb\<^sup>*`` addrs ?T" using pDisj ifB1 a by (auto simp add:addrs_def)
          -- {*And therefore also belongs to the right hand side of @{thm[source]subset},*}
          -- {*which corresponds to our goal.*}
        from incl excl subset  show "x \<in> reachable ?Rb ?B" by (auto simp add:reachable_def)
      qed
      moreover

        -- "If it is marked, then it is reachable"
        from i5 have poI5: "\<forall>x. ?pop_s[x]\<rightarrow>m \<noteq> 0 \<longrightarrow> x \<in> R" by simp
      moreover

        -- {*If it is not on the stack, then its @{term l} and @{term r} fields are unchanged*}
      from i7 i6 ifB2
        have poI6: "\<forall>x. x \<notin> set stack_tl \<longrightarrow> ?pop_s[x]\<rightarrow>r = s0[x]\<rightarrow>r \<and> ?pop_s[x]\<rightarrow>l = s0[x]\<rightarrow>l"
        by(auto simp: fun_upd_apply)

      moreover

        -- {*If it is on the stack, then its @{term l} and @{term r} fields can be reconstructed*}
        from p_notin_stack_tl i7 have poI7: "stkOk (\<lambda>x. ?pop_s[x]\<rightarrow>c \<noteq> 0) (\<lambda>x. ?pop_s[x]\<rightarrow>l) (\<lambda>x. ?pop_s[x]\<rightarrow>r) (\<lambda>x. s0[x]\<rightarrow>l) (\<lambda>x. s0[x]\<rightarrow>r) p stack_tl"
          by clarsimp
      moreover

        from i8 have poI8: "\<forall>x. x \<in> R \<longrightarrow> is_valid_node_C ?pop_s x"
        by simp

        ultimately show "?thesis" by simp
    qed
  }
  note popStack = this

    -- "Proofs of the Swing and Push arm follow."
    -- "Since they are in principle simmilar to the Pop arm proof,"
    -- "we show fewer comments and use frequent pattern matching."
  {
      -- "Swing arm"
    fix s p t cond stack
    assume stackInv: "?Inv p t cond s stack"
      and whileB: "cond \<noteq> 0" (is "?whileB")
      and ifB1: "t = NULL \<or> s[t]\<rightarrow>m \<noteq> 0" (is "?ifB1") and nifB2: "\<not> s[p]\<rightarrow>c \<noteq> 0" (is "\<not> ?ifB2")
    let "?I1 \<and> ?I2 \<and> ?I3 \<and> ?I4 \<and> ?I5 \<and> ?I6 \<and> ?I7 \<and> ?I8 \<and> ?I9" = "?Inv p t cond s stack"
    from stackInv have i1: "?I1" and i2: "?I2" and i3: "?I3" and i4: "?I4"
      and i5: "?I5" and i6: "?I6" and i7: "?I7" and i8: "?I8"
      and cond: "?I9" by simp+
    have stackDist: "distinct (stack)" using i1 by (rule List_distinct)
      from whileB and ifB1 and cond have pNotNULL [iff]: "p \<noteq> NULL" by simp
    with i1 obtain stack_tl where stack_eq: "stack = p # stack_tl"
      by (case_tac stack) (auto simp: List_def)
    with i2 have m_p: "s[p]\<rightarrow>m \<noteq> 0" by auto
    from stack_eq stackDist have p_notin_stack_tl: "p \<notin> set stack_tl" by simp

    let "?sw_s"  = "((s[p\<rightarrow>r := s[p]\<rightarrow>l])[p\<rightarrow>l := t])[p\<rightarrow>c := 1]"
    have "?Inv p (s[p]\<rightarrow>r) (Cbool (?cond p (s[p]\<rightarrow>r) ?sw_s)) ?sw_s stack"
      (is "?swI1\<and>?swI2\<and>?swI3\<and>?swI4\<and>?swI5\<and>?swI6\<and>?swI7\<and>?swI8\<and>?swI9")
    proof -

        -- {*List property is maintained:*}
      from i1 p_notin_stack_tl nifB2
      have swI1: "?swI1"
          by (simp add: stack_eq, auto simp: S_def fun_upd_apply)
      moreover

        -- {*Everything on the stack is marked:*}
      from i2
        have swI2: "?swI2" by simp
      moreover

        -- {*Everything is still reachable:*}
      let "R = reachable ?Ra ?A" = "?I3"
      let "R = reachable ?Rb ?B" = "?swI3"
      have "?Ra\<^sup>* `` addrs ?A = ?Rb\<^sup>* `` addrs ?B"
      proof (rule still_reachable_eq)
          show "addrs ?A \<subseteq> ?Rb\<^sup>* `` addrs ?B"
            by(fastforce simp:addrs_def rel_defs intro:oneStep_reachable Image_iff[THEN iffD2])
      next
          show "addrs ?B \<subseteq> ?Ra\<^sup>* `` addrs ?A"
            by(fastforce simp:addrs_def rel_defs intro:oneStep_reachable Image_iff[THEN iffD2])
      next
        show "\<forall>(x, y)\<in>?Ra-?Rb. y\<in>(?Rb\<^sup>*``addrs ?B)"
            by (clarsimp simp:relS_def) (fastforce simp add:rel_def Image_iff addrs_def fun_upd_apply dest:rel_upd1)
      next
        show "\<forall>(x, y)\<in>?Rb-?Ra. y\<in>(?Ra\<^sup>*``addrs ?A)"
            by (clarsimp simp:relS_def) (fastforce simp add:rel_def Image_iff addrs_def fun_upd_apply dest:rel_upd2)
      qed
      with i3
        have swI3: "?swI3" by (simp add:reachable_def)
      moreover

        -- "If it is reachable and not marked, it is still reachable using..."
      let "\<forall>x. x \<in> R \<and> s[x]\<rightarrow>m = 0 \<longrightarrow> x \<in> reachable ?Ra ?A" = ?I4
      let "\<forall>x. x \<in> R \<and> _[x]\<rightarrow>m = 0 \<longrightarrow> x \<in> reachable ?Rb ?B" = ?swI4
      let ?T = "{t}"
      have "?Ra\<^sup>*``addrs ?A \<subseteq> ?Rb\<^sup>*``(addrs ?B \<union> addrs ?T)"
      proof (rule still_reachable)
          have rewrite: "(\<forall>x\<in>set stack_tl. ?sw_s[x]\<rightarrow>r = s[x]\<rightarrow>r)"
            by (auto simp add:p_notin_stack_tl intro:fun_upd_other)
        show "addrs ?A \<subseteq> ?Rb\<^sup>* `` (addrs ?B \<union> addrs ?T)"
            by (fastforce cong:map_cong simp:stack_eq addrs_def rewrite fun_upd_apply intro:self_reachable)
      next
        show "\<forall>(x, y)\<in>?Ra-?Rb. y\<in>(?Rb\<^sup>*``(addrs ?B \<union> addrs ?T))"
            by (clarsimp simp:relS_def restr_def) (fastforce simp add:rel_def Image_iff addrs_def fun_upd_apply dest:rel_upd1)
      qed
      then have subset: "?Ra\<^sup>*``addrs ?A - ?Rb\<^sup>*``addrs ?T \<subseteq> ?Rb\<^sup>*``addrs ?B"
        by blast
      have ?swI4
      proof (rule allI, rule impI)
        fix x
        assume a: "x \<in> R \<and> ?sw_s[x]\<rightarrow>m = 0"
        with i4 stack_eq  have inc: "x \<in> ?Ra\<^sup>*``addrs ?A"
            by (simp only:reachable_def, clarsimp)
        with ifB1 a
        have exc: "x \<notin> ?Rb\<^sup>*`` addrs ?T"
            by (auto simp add:addrs_def)
        from inc exc subset  show "x \<in> reachable ?Rb ?B"
          by (auto simp add:reachable_def)
      qed
      moreover

        -- "If it is marked, then it is reachable"
      from i5
        have "?swI5" by simp
      moreover

        -- {*If it is not on the stack, then its @{term l} and @{term r} fields are unchanged*}
      from i6 stack_eq
      have "?swI6"
          by clarsimp
      moreover

        -- {*If it is on the stack, then its @{term l} and @{term r} fields can be reconstructed*}
      from stackDist i7 nifB2
      have "?swI7"
          by (simp add: stack_eq) (auto simp: fun_upd_apply)
      moreover

      from i8
      have "?swI8"
        by simp
        ultimately show ?thesis by simp
    qed
  }
  note swStack = this

  {
      -- "Push arm"
    fix s p t cond stack
    assume stackInv: "?Inv p t cond s stack"
      and whileB: "cond \<noteq> 0" (is "?whileB")
      and nifB1: "\<not> (t = NULL \<or> s[t]\<rightarrow>m \<noteq> 0)" (is "\<not> ?ifB1")
    let "?I1 \<and> ?I2 \<and> ?I3 \<and> ?I4 \<and> ?I5 \<and> ?I6 \<and> ?I7 \<and> ?I8 \<and> ?I9" = "?Inv p t cond s stack"
    from stackInv have i1: "?I1" and i2: "?I2" and i3: "?I3" and i4: "?I4"
      and i5: "?I5" and i6: "?I6" and i7: "?I7" and i8: "?I8"
      and cond: "?I9" by simp+
    have stackDist: "distinct (stack)" using i1 by (rule List_distinct)
      from whileB and nifB1 and cond have tNotNULL [iff]: "t \<noteq> NULL" by simp
    with i1 obtain new_stack where new_stack_eq: "new_stack = t # stack" by clarsimp
    from tNotNULL nifB1 cond have n_m_t: "s[t]\<rightarrow>m = 0" by clarsimp
    with i2 have t_notin_stack: "t \<notin> set stack" by blast

    let "?pu_s"  = "((s[t\<rightarrow>l := p])[t\<rightarrow>m := 1])[t\<rightarrow>c := 0]"
    have "?Inv t (s[t]\<rightarrow>l) (Cbool (?cond t (s[t]\<rightarrow>l) ?pu_s)) ?pu_s new_stack"
      (is "?puI1\<and>?puI2\<and>?puI3\<and>?puI4\<and>?puI5\<and>?puI6\<and>?puI7\<and>?puI8\<and>?puI9")
    proof -
        -- {*List property is maintained:*}
      from i1 t_notin_stack new_stack_eq
      have puI1: "?puI1"
          by (simp add: new_stack_eq del: fun_upd_apply) (auto simp:S_def fun_upd_apply)
      moreover

        -- {*Everything on the stack is marked:*}
      from i2
      have puI2: "?puI2"
        by (simp add:new_stack_eq fun_upd_apply)
      moreover

          -- {*Everything is still reachable:*}
      let "R = reachable ?Ra ?A" = "?I3"
      let "R = reachable ?Rb ?B" = "?puI3"
      have "?Ra\<^sup>* `` addrs ?A = ?Rb\<^sup>* `` addrs ?B"
      proof (rule still_reachable_eq)
          show "addrs ?A \<subseteq> ?Rb\<^sup>* `` addrs ?B"
            by(fastforce simp:addrs_def rel_defs intro:oneStep_reachable Image_iff[THEN iffD2])
      next
          show "addrs ?B \<subseteq> ?Ra\<^sup>* `` addrs ?A"
            by(fastforce simp:addrs_def rel_defs intro:oneStep_reachable Image_iff[THEN iffD2])
      next
        show "\<forall>(x, y)\<in>?Ra-?Rb. y\<in>(?Rb\<^sup>*``addrs ?B)"
            by (clarsimp simp:relS_def) (fastforce simp add:rel_def Image_iff addrs_def dest:rel_upd1)
      next
        show "\<forall>(x, y)\<in>?Rb-?Ra. y\<in>(?Ra\<^sup>*``addrs ?A)"
            by (clarsimp simp:relS_def) (fastforce simp add:rel_def Image_iff addrs_def fun_upd_apply dest:rel_upd2)
      qed
      with i3
      have puI3: "?puI3" by (simp add:reachable_def addrs_def)
      moreover

        -- "If it is reachable and not marked, it is still reachable using..."
      let "\<forall>x. x \<in> R \<and> s[x]\<rightarrow>m = 0 \<longrightarrow> x \<in> reachable ?Ra ?A" = ?I4
      let "\<forall>x. x \<in> R \<and> _[x]\<rightarrow>m = 0 \<longrightarrow> x \<in> reachable ?Rb ?B" = ?puI4
      let ?T = "{t}"
      have "?Ra\<^sup>*``addrs ?A \<subseteq> ?Rb\<^sup>*``(addrs ?B \<union> addrs ?T)"
      proof (rule still_reachable)
        show "addrs ?A \<subseteq> ?Rb\<^sup>* `` (addrs ?B \<union> addrs ?T)"
            by (fastforce simp:new_stack_eq addrs_def intro:self_reachable)
      next
        show "\<forall>(x, y)\<in>?Ra-?Rb. y\<in>(?Rb\<^sup>*``(addrs ?B \<union> addrs ?T))"
            by (clarsimp simp:relS_def new_stack_eq restr_un restr_upd)
               (auto simp add:rel_def Image_iff restr_def addrs_def fun_upd_apply dest:rel_upd3)
      qed
      then have subset: "?Ra\<^sup>*``addrs ?A - ?Rb\<^sup>*``addrs ?T \<subseteq> ?Rb\<^sup>*``addrs ?B"
        by blast
      have ?puI4
      proof (rule allI, rule impI)
        fix x
        assume a: "x \<in> R \<and> ?pu_s[x]\<rightarrow>m = 0"
        have xDisj: "x = t \<or> x \<noteq> t" by simp
        with i4 a have inc: "x \<in> ?Ra\<^sup>*``addrs ?A"
            by (fastforce simp: addrs_def reachable_def intro:self_reachable)
        have exc: "x \<notin> ?Rb\<^sup>*`` addrs ?T"
          using xDisj a n_m_t
            by (clarsimp simp add:addrs_def)
        from inc exc subset  show "x \<in> reachable ?Rb ?B"
            by (auto simp add:reachable_def)
      qed
      moreover

        -- "If it is marked, then it is reachable"
        from i5
      have "?puI5"
          by (auto simp:addrs_def i3 reachable_def fun_upd_apply intro:self_reachable)
      moreover

        -- {*If it is not on the stack, then its @{term l} and @{term r} fields are unchanged*}
      from i6
      have "?puI6"
          by (simp add:new_stack_eq)
      moreover

        -- {*If it is on the stack, then its @{term l} and @{term r} fields can be reconstructed*}
      from stackDist i6 t_notin_stack i7
        have "?puI7" by (simp add: new_stack_eq) (auto simp: fun_upd_apply)
      moreover

      from i8
      have "?puI8"
        by simp

        ultimately show ?thesis by auto
    qed
    (* replace new_stack because it has been locally obtained *)
    hence "?Inv t (s[t]\<rightarrow>l) (Cbool (?cond t (s[t]\<rightarrow>l) ?pu_s)) ?pu_s (t # stack)"
      by (fastforce simp: new_stack_eq)
  }
  note puStack = this

  txt {* Loop invariant and correctness *}
  {
    fix s p t cond
    assume loopInv: "?inv p t cond s \<and> cond \<noteq> 0" (is "_ \<and> ?whileB")
    then have exStack: "?inv p t cond s" and whileB: "?whileB" by simp+
    from loopInv obtain stack where stackInv: "?Inv p t cond s stack" by blast

    from stackInv have stackDist: "distinct (stack)" by (auto simp: List_distinct)
    from stackInv have tValid: "t \<noteq> NULL \<longrightarrow> is_valid_node_C s t"
                   and pValid: "p \<noteq> NULL \<longrightarrow> is_valid_node_C s p"
      by (auto simp: reachable_def addrs_def)

    let "?pop_s" = "s[p\<rightarrow>r := t]"
    let "?sw_s"  = "((s[p\<rightarrow>r := s[p]\<rightarrow>l])[p\<rightarrow>l := t])[p\<rightarrow>c := 1]"
    let "?pu_s"  = "((s[t\<rightarrow>l := p])[t\<rightarrow>m := 1])[t\<rightarrow>c := 0]"

    show "(if t = NULL \<or> s[t]\<rightarrow>m \<noteq> 0
           then (if s[p]\<rightarrow>c \<noteq> 0
                 then ?inv (s[p]\<rightarrow>r) p (Cbool (?cond (s[p]\<rightarrow>r) p ?pop_s)) ?pop_s \<and>
                      (s[p]\<rightarrow>r = NULL \<longrightarrow> p \<noteq> NULL \<longrightarrow> is_valid_node_C ?pop_s p)
                 else ?inv p (s[p]\<rightarrow>r) (Cbool (?cond p (s[p]\<rightarrow>r) ?sw_s)) ?sw_s \<and>
                      (p = NULL \<longrightarrow> s[p]\<rightarrow>r \<noteq> NULL \<longrightarrow> is_valid_node_C ?sw_s (s[p]\<rightarrow>r))) \<and>
                is_valid_node_C s p
           else (?inv t (s[t]\<rightarrow>l) (Cbool (?cond t (s[t]\<rightarrow>l) ?pu_s)) ?pu_s \<and>
                 (t = NULL \<longrightarrow> s[t]\<rightarrow>l \<noteq> NULL \<longrightarrow> is_valid_node_C ?pu_s (s[t]\<rightarrow>l))) \<and>
                is_valid_node_C s t) \<and>
          (t \<noteq> NULL \<longrightarrow> is_valid_node_C s t)"
         (is "(if ?ifB1 then (if ?ifB2 then ?popInv else ?swInv) \<and> _ else ?puInv) \<and> _")
    proof -
      {
        have "t \<noteq> NULL \<longrightarrow> is_valid_node_C s t"
          using stackInv whileB by (auto simp: reachable_def addrs_def)
      }
      note tValid = this

      moreover
      {
        assume ifB1: "?ifB1" and ifB2: "?ifB2"
        then obtain stack_tl where stack_eq: "stack = p # stack_tl"
          using stackInv whileB by (case_tac stack) (auto simp: List_def)
        have pNotNULL: "p \<noteq> NULL" using whileB ifB1 stackInv by simp
        have pValid: "is_valid_node_C ?pop_s p"
          using pNotNULL stackInv by (auto simp: reachable_def addrs_def)

        have "?popInv"
          using popStack[OF stackInv[unfolded stack_eq] whileB ifB1 ifB2] pValid
          by blast
      }

      moreover
      {
        assume ifB1: "?ifB1" and nifB2: "\<not> ?ifB2"
        have pNotNULL: "p \<noteq> NULL" using whileB ifB1 stackInv by simp
        have prValid: "s[p]\<rightarrow>r \<noteq> NULL \<longrightarrow> is_valid_node_C ?sw_s (s[p]\<rightarrow>r)"
        proof -
          have "s[p]\<rightarrow>r \<noteq> NULL \<longrightarrow> s[p]\<rightarrow>r \<in> R"
            using stackInv by (auto simp: pNotNULL reachable_def rel_defs addrs_def)
          then show ?thesis using stackInv by auto
        qed

        have "?swInv"
          using swStack[OF stackInv whileB ifB1 nifB2] prValid by blast
      }

      moreover
      {
        assume nifB1: "\<not> ?ifB1"
        have tNotNULL: "t \<noteq> NULL" using whileB nifB1 stackInv by simp
        have tlValid: "s[t]\<rightarrow>l \<noteq> NULL \<longrightarrow> is_valid_node_C ?pu_s (s[t]\<rightarrow>l)"
        proof -
          have "s[t]\<rightarrow>l \<noteq> NULL \<longrightarrow> s[t]\<rightarrow>l \<in> R"
            using stackInv tNotNULL by (auto simp: reachable_def rel_defs addrs_def)
          then show ?thesis using stackInv by auto
        qed

        have "?puInv"
          using puStack[OF stackInv whileB nifB1] tValid tNotNULL tlValid by blast
      }

      moreover
      {
        assume "?ifB1"
        then have "is_valid_node_C s p"
          using whileB stackInv by (auto simp: reachable_def addrs_def)
      }

      ultimately show "?thesis" by presburger
    qed
  }

  txt {* Loop termination *}
  {
    fix p t cond m1 m2 m3 s
    assume loopInv: "?inv p t cond s \<and> cond \<noteq> 0
                        \<and> schorr_waite'_measure s s0 R p t cond = (m1, m2, m3)"
    (is "_ \<and> _ \<and> ?prevMeasure")
    then have exStack: "\<exists>stack. ?Inv p t cond s stack"
     and whileB: "cond \<noteq> 0" (is "?whileB")
     and measure: "?prevMeasure" by blast+

    from exStack obtain stack where stackInv: "?Inv p t cond s stack" by blast
    from stackInv have stackDist: "distinct stack" by auto
    have theStack: "\<And>p t cond s stack. ?Inv p t cond s stack \<Longrightarrow>
                       (THE stack. ?Inv p t cond s stack) = stack"
      by (auto simp: the_equality List_unique)

    have measure': "(m1, m2, m3) = (card {x \<in> R. s[x]\<rightarrow>m = 0}, card {x \<in> set stack. s[x]\<rightarrow>c = 0}, length stack)"
      using theStack[OF stackInv] measure by auto

    let "?pop_s" = "s[p\<rightarrow>r := t]"
    let "?sw_s"  = "((s[p\<rightarrow>r := s[p]\<rightarrow>l])[p\<rightarrow>l := t])[p\<rightarrow>c := 1]"
    let "?pu_s"  = "((s[t\<rightarrow>l := p])[t\<rightarrow>m := 1])[t\<rightarrow>c := 0]"

    let "?decreasing p t s" = "schorr_waite'_measure s s0 R p t
                                   (Cbool (?cond p t s) :: int)
                            < (m1, m2, m3)"

    have weird_mp: "\<And>a b. (a \<and> (a \<longrightarrow> b)) = (a \<and> b)" by blast

    show "(t \<noteq> NULL \<longrightarrow> is_valid_node_C s t) \<longrightarrow>
          (if t = NULL \<or> s[t]\<rightarrow>m \<noteq> 0
           then is_valid_node_C s p \<longrightarrow>
                (if s[p]\<rightarrow>c \<noteq> 0
                 then (s[p]\<rightarrow>r = NULL \<longrightarrow> p \<noteq> NULL \<longrightarrow> is_valid_node_C ?pop_s p) \<longrightarrow>
                        ?decreasing (s[p]\<rightarrow>r) p ?pop_s
                 else (p = NULL \<longrightarrow> s[p]\<rightarrow>r \<noteq> NULL \<longrightarrow> is_valid_node_C ?sw_s (s[p]\<rightarrow>r)) \<longrightarrow>
                        ?decreasing p (s[p]\<rightarrow>r) ?sw_s)
           else is_valid_node_C s t \<longrightarrow>
                 (t = NULL \<longrightarrow> s[t]\<rightarrow>l \<noteq> NULL \<longrightarrow> is_valid_node_C ?pu_s (s[t]\<rightarrow>l)) \<longrightarrow>
                  ?decreasing t (s[t]\<rightarrow>l) ?pu_s)"
         (is "_ \<longrightarrow> (if ?ifB1
                    then _ \<longrightarrow> (if ?ifB2 then _ \<longrightarrow> ?popMeasure else ?swMeasure)
                    else _ \<longrightarrow> ?puMeasure)")
    proof -
      {
        assume ifB1: "?ifB1" and ifB2: "?ifB2"
        then have pNotNULL: "p \<noteq> NULL" using stackInv whileB by simp
        from stackInv pNotNULL obtain stack_tl where stack_eq: "stack = p # stack_tl"
          by (case_tac stack, auto simp: List_def)
        have stack_tlDist: "distinct stack_tl" using stackDist stack_eq by simp
        have conv: "\<And>P xs. distinct xs \<Longrightarrow> card {x \<in> set xs. P x} = length [x\<leftarrow>xs. P x]"
          by (subst set_filter[symmetric])
             (metis distinct_card distinct_filter)

        have stackC_mono: "card {x \<in> set stack_tl. s[x]\<rightarrow>c = 0} \<le> card {x \<in> set stack. s[x]\<rightarrow>c = 0}"
          by (simp add: conv[OF stackDist] conv[OF stack_tlDist])
             (simp add: stack_eq)
        have "?popMeasure"
          using theStack[OF popStack[OF stackInv[unfolded stack_eq] whileB ifB1 ifB2]] stackC_mono
          by (simp add: pNotNULL stack_eq prod_less_def measure')
      }

      moreover
      {
        assume ifB1: "?ifB1" and nifB2: "\<not> ?ifB2"
        then have pNotNULL: "p \<noteq> NULL" using stackInv whileB by simp
        from stackInv pNotNULL obtain stack_tl where stack_eq: "stack = p # stack_tl"
          by (case_tac stack, auto simp: List_def)
        from stack_eq stackDist have p_notin_stack_tl: "p \<notin> set stack_tl" by simp

        have notin_filter: "\<And>xs a P. a \<notin> set xs \<Longrightarrow> filter P xs = filter (\<lambda>x. x \<noteq> a \<and> P x) xs"
        proof -
          fix xs a P
          show "a \<notin> set xs \<Longrightarrow> ?thesis xs a P" by (induct xs) auto
        qed
          have decrease: "card {x \<in> set stack. ?sw_s[x]\<rightarrow>c = 0} < card {x \<in> set stack. s[x]\<rightarrow>c = 0}"
        proof -
            have conv: "\<And>P. card {x \<in> set stack. P x} = length [x\<leftarrow>stack. P x]"
            by (subst set_filter[symmetric])
               (metis stackDist distinct_card distinct_filter)

          show ?thesis
            unfolding conv
              by (simp add: stack_eq nifB2 weird_mp fun_upd_apply
                          notin_filter[OF p_notin_stack_tl, symmetric])
        qed

          hence "?swMeasure"
          using theStack[OF swStack[OF stackInv[unfolded stack_eq] whileB ifB1 nifB2]]
            by (simp add: stack_eq[symmetric] prod_less_def measure')
      }

      moreover
      {
        assume nifB1: "\<not>?ifB1"
        from nifB1 whileB stackInv have tNotNULL: "t \<noteq> NULL" by clarsimp
        from stackInv obtain new_stack where new_stack_eq: "new_stack = t # stack" by clarsimp
        from tNotNULL nifB1 stackInv have n_m_t: "s[t]\<rightarrow>m = 0" by clarsimp
        with stackInv have t_notin_stack: "t \<notin> set stack" by blast
        let "?puI1\<and>?puI2\<and>?puI3\<and>?puI4\<and>?puI5\<and>?puI6\<and>?puI7\<and>?puI8\<and>?puI9" =
              "?Inv t (s[t]\<rightarrow>l) t_cond ?pu_s new_stack"

        have set_filter_remove: "\<And>s a P. a \<in> s \<Longrightarrow> {x. x \<noteq> a \<and> x \<in> s \<and> P x} = {x\<in>s. P x} - {a}"
          by blast

          have decrease: "card {x \<in> R. ?pu_s[x]\<rightarrow>m = 0} < card {x \<in> R. s[x]\<rightarrow>m = 0}"
        proof -
          have new_stackDist: "distinct new_stack"
            by (simp add: new_stack_eq t_notin_stack stackDist)
          have t_reachable: "t \<in> R" using stackInv tNotNULL
            by (auto simp: reachable_def addrs_def)

            have new_m: "{x \<in> R. ?pu_s[x]\<rightarrow>m = 0} = {x \<in> R. s[x]\<rightarrow>m = 0} - {t}"
              by (auto simp: set_filter_remove fun_upd_apply)

          show ?thesis
            by (subst new_m card.remove[of "{x\<in>R. s[x]\<rightarrow>m = 0}" t])+
               (auto simp: t_reachable n_m_t)
        qed

        have "?puMeasure"
            using theStack[OF puStack[OF stackInv whileB nifB1]] decrease
            by (simp add: measure' prod_less_def)
      }

      ultimately show ?thesis by presburger
    qed
    }
  }
qed

end

end
