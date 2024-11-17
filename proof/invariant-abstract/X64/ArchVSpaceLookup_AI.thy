(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchVSpaceLookup_AI
imports
  SubMonad_AI
  "Lib.Crunch_Instances_NonDet"
begin

definition
  "lookup_walk cs m ref p \<equiv> {(r, q). \<exists>h. ref = h @ r \<and> (r, q) \<in> cs\<^sup>* `` m \<and> (([], q),h, p) \<in> cs\<^sup>*}"

definition
  "trans_depends kh cs f \<equiv> \<forall>q h p. (([],q),h,p) \<in> cs = (\<exists>obj. obj = kh q \<and> f obj p h)"

definition
  "lookup_leaf ptr cs =  {(ref,p). (([],ptr),ref, p) \<in> cs^*}"

definition
lookup_refs ::"'c \<Rightarrow> ('c \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> ('a list \<times> 'b) set"
where "lookup_refs obj f \<equiv> {(h,p). f obj p h}"

definition
lookupable_refs :: "(('a list \<times> 'b) \<times> 'a list \<times> 'b) set \<Rightarrow> 'a list set \<Rightarrow> ('a list \<times> 'b) set \<Rightarrow> ('a list \<times> 'b) set"
where  "lookupable_refs cs refs m \<equiv> {(ref, p). \<exists>tref href. href\<in>refs \<and> ref=tref@href \<and> (tref,p)\<in>cs^* `` m}"

definition
  "reachable vset \<equiv> (\<lambda>(ref, p). p) ` vset"

locale wellformed_lookup =
  fixes cs :: "(('c list \<times> 'a) \<times> 'c list \<times> 'a) set" and kh and f
  assumes trans_depends: "trans_depends kh cs f"
  assumes lookup1_is_append:
      "((r , q), rs, p) \<in> cs \<Longrightarrow> \<exists>ref. rs = ref # r"
  assumes lookup1_append:
      "((ra @ b, q), r @ b, p) \<in> cs \<Longrightarrow> ((ra, q), r, p) \<in> cs"
  assumes lookup1_cut:
      "((ra, q), r, p) \<in> cs \<Longrightarrow> ((ra @ b, q), r @ b, p) \<in> cs"
  assumes graph_inject:
      "\<And>p q obj ref. \<lbrakk>f obj p ref; f obj q ref\<rbrakk> \<Longrightarrow> p = q"
  assumes graph_single_step:
      "\<And>p obj ref. \<lbrakk>f obj p ref\<rbrakk> \<Longrightarrow> \<exists>r. ref = [r]"

context wellformed_lookup
begin

lemma lookup_refs_lookup1:
  "lookup_refs (kh ptr) f = {(h,p). (([],ptr),h,p) \<in> cs}"
  apply (insert  trans_depends)
  apply (clarsimp simp: trans_depends_def lookup_refs_def)
  done

lemma lookupable_refs_reach_self:
  "(rs, ptr) \<in> lookupable_refs cs {ref. (ref, ptr) \<in> cs\<^sup>* `` rset} refs
  \<Longrightarrow> \<exists>rs'. (rs', ptr) \<in> cs^* `` rset"
  apply (clarsimp simp: lookupable_refs_def Image_def)
  apply fastforce
  done

lemma lookup1_append_singleton:
  "((a, b), ref # a, q) \<in> cs \<Longrightarrow> (([], b), [ref], q) \<in> cs"
  apply (rule lookup1_append)
  apply fastforce
  done

lemma lookup1_cut_singleton:
  "(([], b), [ref], q) \<in> cs \<Longrightarrow> ((a, b), ref # a, q) \<in> cs "
  apply (drule lookup1_cut)
  apply fastforce
  done

lemma trans_dependsD:
  "(([],p), ref, q ) \<in> cs \<Longrightarrow> f (kh p) q ref"
  apply (insert trans_depends)
  apply (simp add: trans_depends_def)
  done

lemma trans_depends_eq:
  "(([],q),h,p) \<in> cs = f (kh q) p h"
  apply (insert trans_depends)
  apply (clarsimp simp: trans_depends_def)
  done

lemma lookup_empty_refl:
  "((a, p), [], q) \<in> cs\<^sup>* \<Longrightarrow> a = [] \<and> p = q"
  apply (erule rtranclE)
   apply simp
  apply (case_tac y)
  apply (clarsimp dest!: lookup1_is_append)
  done

lemma lookup_empty_refl_eq[simp]:
  "((a, p), [], q) \<in> cs\<^sup>* \<longleftrightarrow> a = [] \<and> p = q"
  using lookup_empty_refl by auto

lemma lookup1_same_leaf:
  "\<lbrakk>(a, refs, p) \<in> cs; (a, refs, q) \<in> cs\<rbrakk> \<Longrightarrow> p = q"
  apply (case_tac a)
  apply clarsimp
  apply (frule lookup1_is_append)
  apply clarsimp
  apply (drule lookup1_append_singleton)
  apply (drule lookup1_append_singleton)
  apply (clarsimp dest!: trans_dependsD)
  apply (drule graph_inject)
  apply simp+
  done

lemma lookup_ref_step:
  "((ref, ptr), ref', p) \<in> cs\<^sup>* \<Longrightarrow> \<exists>r. ref' = r @ ref"
  proof (induct "length ref'" arbitrary: ref' ref ptr p)
  case 0
    assume xs: "0 = length ref'"
      and  "((ref, ptr), ref', p) \<in> cs\<^sup>*"
  thus ?case
    apply simp
    done
  next
  case Suc
  show ?case
    apply (cut_tac Suc.prems Suc.hyps(2))
    apply (erule rtranclE)
     apply fastforce
    apply (case_tac y)
    apply (case_tac ref')
     apply clarsimp
    apply simp
    apply (drule Suc.hyps(1)[rotated])
     apply (clarsimp dest!: lookup1_is_append )+
    done
  qed

lemma lookup_trancl_append_1: (* This is true because the lengh of the lookup is always increased by 1 *)
  "((ra @ [b], q), r @ [b], p) \<in> cs\<^sup>*
  \<Longrightarrow> ((ra, q), r, p) \<in> cs\<^sup>*"
  proof (induct "length r - length ra" arbitrary: ra r q p)
  case 0
    assume "0 = length r - length ra"
    and "((ra @ [b], q), r @ [b], p) \<in> cs\<^sup>*"
  thus ?case
    apply simp
    apply (erule rtranclE)
     apply simp
    apply (case_tac y)
    apply simp
    apply (frule lookup_ref_step)
    apply (clarsimp dest!: lookup1_is_append)
    done
  next
  case Suc
  show ?case
    apply (insert Suc.prems Suc.hyps(2))
    apply (erule rtranclE)
     apply simp
    apply (case_tac y)
    apply clarsimp
    apply (frule lookup_ref_step)
    apply clarsimp
    apply (drule Suc.hyps(1)[where r = "a @ b" for a b, rotated,simplified])
     apply (clarsimp dest!: lookup1_is_append)
    apply (drule lookup1_append[where ra = "a @ b" for a b, simplified])
    apply (erule rtrancl.intros)
    apply simp
    done
  qed


lemma lookup_trancl_append:
  "((ra @ ref, b), r @ ref, p) \<in> cs^* \<Longrightarrow> ((ra, b), r, p) \<in> cs^*"
  proof (induct "length ref" arbitrary: ref ra r b p)
  case 0
  assume "((ra @ ref, b), r @ ref, p) \<in> cs ^*"
     and " 0 = length ref"
  thus ?case
    by simp
  next
  case Suc
  have t: "\<And>a b c. a @ b # c = (a @ [b]) @ c"
    by auto
  show ?case
    apply (insert Suc.prems Suc.hyps(2))
    apply (case_tac ref)
     apply clarsimp+
    apply (subst(asm) t)
    apply (subst(asm) t[where a = r])
    apply (frule(1) Suc.hyps(1)[rotated])
    apply (drule lookup_trancl_append_1)
    apply fastforce
    done
  qed

lemma lookup_leaf_from_lookup:
  assumes neq: "ref' \<noteq> ref"
  shows "\<lbrakk>((ref, p), ref', q) \<in> cs\<^sup>* \<rbrakk>
  \<Longrightarrow> \<exists>r ptr. ref' = r @ ref \<and> (([],p),[last r],ptr) \<in> cs \<and> (r,q) \<in> lookup_leaf p cs"
  apply (frule lookup_ref_step)
  apply clarsimp
  apply (erule converse_rtranclE)
   apply (insert neq)
   apply clarsimp
  apply (case_tac y)
  apply (rule conjI)
   apply clarsimp
   apply (rename_tac r mref ptr)
   apply (rule_tac x = ptr in exI)
   subgoal ex
    apply (clarsimp dest!: lookup_ref_step)
    apply (rule_tac ra = "[]" and b = ref in lookup1_append)
    apply (frule lookup1_is_append)
    apply clarsimp
    done
  apply (clarsimp simp: lookup_leaf_def)
  apply (rule converse_rtrancl_into_rtrancl)
  apply (rule ex)
      apply simp+
  apply (rule_tac ref = ref in lookup_trancl_append)
  apply (frule lookup_ref_step)
  apply (clarsimp dest!: lookup1_is_append)
  done

lemma lookupE:
  assumes rcl: "((ref, p), ref', q) \<in> cs\<^sup>*"
  assumes eq: "\<lbrakk>ref' = ref; p = q\<rbrakk> \<Longrightarrow> P ref' ref p q cs"
  and neq: "\<And>r ptr. \<lbrakk>ref' \<noteq> ref; ref' = r @ ref;  (([],p),[last r],ptr) \<in> cs; (r,q) \<in> lookup_leaf p cs\<rbrakk> \<Longrightarrow> P ref' ref p q cs"
  shows "P ref' ref p q cs"
  apply (insert rcl)
  apply (case_tac "ref' = ref")
   apply (rule eq)
    apply simp
   apply (erule rtranclE)
    apply simp
   apply (clarsimp dest!: lookup1_is_append lookup_ref_step)
  apply (frule(1) lookup_leaf_from_lookup)
  apply (elim disjE conjE exE)
  apply (rule neq)
   apply simp+
  done

lemma lookup_forwardE:
  assumes rcl: "(([], p), ref, q) \<in> cs\<^sup>*"
  assumes eq: "\<lbrakk>ref = []; p = q\<rbrakk> \<Longrightarrow> P ref p q cs"
  and neq1: "\<And>r. \<lbrakk>ref = [r]; (([], p), [r], q) \<in> cs\<rbrakk> \<Longrightarrow> P ref p q cs"
  and neq: "\<And>r ptr ref'. \<lbrakk>ref \<noteq> []; ref = r @ [ref'];  (([],p),[ref'],ptr) \<in> cs; (([], ptr), r, q) \<in> cs\<^sup>*\<rbrakk> \<Longrightarrow> P ref p q cs"
  shows "P ref p q cs"
  apply (insert rcl)
  apply (erule converse_rtranclE)
   apply (rule eq)
    apply (simp add: eq)
   apply simp
  apply clarsimp
  apply (frule lookup_ref_step)
  apply (frule lookup1_is_append)
  apply (elim exE)+
  apply (case_tac r)
   apply (rule neq1)
    apply simp
   apply clarsimp
   apply (erule rtranclE, simp)
   apply (clarsimp dest!: lookup1_is_append)
  apply clarsimp
  apply (drule lookup_trancl_append[where ra = "[]" and r = "h # g" for h g,simplified])
  apply (drule neq[rotated 2])
    apply simp+
  done

lemma lookup_rtrancl_stepD:
  "(([],p), [r], q) \<in> cs^* \<Longrightarrow> (([],p),[r],q) \<in> cs"
  apply (erule rtranclE)
  apply simp
  apply clarsimp
  apply (frule lookup_ref_step)
  apply clarsimp
  apply (erule rtranclE)
   apply simp
  apply (clarsimp dest!: lookup_ref_step lookup1_is_append)
  done

lemma lookup_rtrancl_stepsD:
  "(([], p), r @ [ref'], q) \<in> cs\<^sup>* \<Longrightarrow> \<exists>ptr. (([],p),[ref'],ptr) \<in> cs \<and> (([], ptr), r, q) \<in> cs\<^sup>*"
  apply (erule lookup_forwardE)
  apply clarsimp+
  apply force+
  done

lemma lookup_trancl_cut_1:
  (* This is true because the lengh of the lookup is always increased by 1 *)
  "((ra, q), r, p) \<in> cs\<^sup>* \<Longrightarrow> ((ra @ [b], q), r @ [b], p) \<in> cs\<^sup>*"
    proof (induct "length r - length ra" arbitrary: ra r q p)
  case 0
    assume " 0 = length r - length ra"
    and "((ra , q), r , p) \<in> cs\<^sup>*"
  thus ?case
    apply simp
    apply (frule lookup_ref_step)
    apply clarsimp
    apply (erule rtranclE)
     apply simp
    apply (case_tac y)
    apply simp
    apply (frule lookup_ref_step)
    apply (clarsimp dest!: lookup1_is_append)
    done
  next
  case Suc
  show ?case
    apply (insert Suc.prems Suc.hyps(2))
    apply (erule rtranclE)
     apply simp
    apply (case_tac y)
    apply clarsimp
    apply (frule lookup_ref_step)
    apply clarsimp
    apply (drule Suc.hyps(1)[where r = "a @ b" for a b, rotated,simplified])
     apply (clarsimp dest!: lookup1_is_append)
    apply (erule rtrancl.intros)
    apply (frule lookup1_cut)
    apply simp
    done
  qed

lemma lookup_trancl_cut:
  "((ra, b), r, p) \<in> cs\<^sup>* \<Longrightarrow> ((ra @ ref, b), r @ ref, p) \<in> cs\<^sup>*"
  proof (induct "length ref" arbitrary: ref ra r b p)
  case 0
  assume "((ra, b), r, p) \<in> cs\<^sup>*"
     and " 0 = length ref"
  thus ?case
    by simp
  next
  case Suc
  have t: "\<And>a b c. a @ b # c = (a @ [b]) @ c"
    by auto
  show ?case
    apply (insert Suc.prems Suc.hyps(2))
    apply (case_tac ref rule: rev_cases)
     apply clarsimp+
    apply (frule(1) Suc.hyps(1)[rotated])
    apply (drule lookup_trancl_cut_1)
        apply (drule lookup_trancl_cut_1)
    apply fastforce
    done
  qed

lemma empty_lookup_walk:
  "lookup_walk cs m [] p = {ptr. ptr \<in> m \<and> fst ptr = [] \<and> snd ptr = p }"
  by (fastforce simp: lookup_walk_def)

lemma lookup_walk_stepI1:
  "\<lbrakk>p \<in> lookup_walk cs m ref ptr; (([], ptr), [q], ptr') \<in> cs\<rbrakk> \<Longrightarrow> p \<in> lookup_walk cs m (q # ref) ptr'"
  apply (clarsimp simp: lookup_walk_def)
  apply (rule conjI, fastforce)
  apply (erule rtrancl_into_rtrancl)
  apply (erule lookup1_cut[where ra = "[]" and r = "[q]", simplified])
  done

lemma lookup_walk_stepsI1:
  "\<lbrakk>p \<in> lookup_walk cs m ref ptr; (([], ptr), refs, ptr') \<in> cs^*\<rbrakk> \<Longrightarrow> p \<in> lookup_walk cs m (refs @ ref) ptr'"
  apply (clarsimp simp: lookup_walk_def)
  apply (rule conjI, fastforce)
  apply (erule rtrancl_trans)
  apply (erule lookup_trancl_cut[where ra = "[]" and r = "refs", simplified])
  done

lemma lookup_walk_stepI2:
  "\<lbrakk>(ref, ptr) \<in> lookup_walk cs m ref ptr; (([], ptr), [q], ptr') \<in> cs\<rbrakk>
  \<Longrightarrow> (q#ref,ptr') \<in> lookup_walk cs m (q # ref) ptr'"
  apply (clarsimp simp: lookup_walk_def Image_def)
  apply (erule bexI[rotated])
  apply (erule rtrancl_into_rtrancl)
  apply (drule lookup1_cut)
  apply fastforce
  done

lemma lookup_walk_step_hdD:
  "(refs, p) \<in> lookup_walk cs m refs p \<Longrightarrow> (refs, p)\<in> m \<or> (\<exists>y. (tl refs,y) \<in> lookup_walk cs m (tl refs) y \<and> (([],y), [hd refs], p) \<in> cs)"
  apply (clarsimp simp: lookup_walk_def del: disjCI)
  apply (erule rtranclE)
   apply simp
  apply (rule disjI2)
  apply (case_tac y, clarsimp)
  apply (frule lookup1_is_append)
  apply clarsimp
  apply (intro conjI exI)
   apply fastforce
  apply (erule lookup1_append_singleton)
  done

lemma lookup_walk_stepD:
  "p \<in> lookup_walk cs m (ref # refs) q
  \<Longrightarrow> p = (ref # refs, q)
      \<or> (\<exists>ptr r. r @ (fst p) = refs \<and> p \<in> lookup_walk cs m refs ptr \<and> (([],ptr),[ref], q) \<in> cs)"
  apply (clarsimp simp: lookup_walk_def del: disjCI)
  apply (erule rtranclE)
   apply clarsimp
  apply (case_tac ya, clarsimp del: disjCI)
  apply (frule lookup1_is_append)
  apply (clarsimp del: disjCI)
  apply (rule conjI)
   apply force
  apply (intro exI conjI)
   apply force
  apply (erule lookup1_append_singleton)
  done

lemma reachable_walk:
  "(ref, p) \<in> (cs^* `` m) \<Longrightarrow> (ref, p) \<in> lookup_walk cs m ref p"
  by (clarsimp simp: lookup_walk_def)

lemma lookup_trans_eq:
  "((refs, b), refs, p) \<in> cs\<^sup>* \<Longrightarrow> b = p"
  by (erule lookup_trancl_append[where ra = "[]" and r = "[]" , simplified])

lemma lookup1_same_parent:
  "\<lbrakk>(a, refs, p) \<in> cs; (b, refs, q) \<in> cs\<rbrakk> \<Longrightarrow> fst a = fst b"
  apply (insert trans_depends)
  apply (case_tac a,case_tac b)
  apply (clarsimp dest!: lookup1_is_append)
  done

lemma lookupable_is_unique:
 "\<lbrakk>(sref, refs, p) \<in> cs^*; (sref, refs, q) \<in> cs^* \<rbrakk>
 \<Longrightarrow> p = q"
  proof (induct "length refs - length (fst sref)" arbitrary: p q sref refs)
  case 0
  thus ?case
    apply (insert "local.0.prems" "local.0.hyps")
    apply (cases sref, simp)
    apply (case_tac "fst sref = refs")
     apply (clarsimp dest!: lookup_trans_eq)
    apply clarsimp
    apply (drule lookup_leaf_from_lookup[rotated])
     apply simp
    apply clarsimp
    done
  next
  case Suc
  show ?case
    apply (insert Suc.prems Suc.hyps(2))
    apply (erule rtranclE, simp)
    apply (erule rtranclE, simp)
    apply (frule_tac a = y and b = ya in lookup1_same_parent)
     apply simp
    apply (case_tac y, clarsimp)
    apply (drule(1) Suc.hyps(1)[rotated])
     apply (fastforce dest!: lookup1_is_append)
   apply clarsimp
   apply (erule(1) lookup1_same_leaf)
   done
  qed

lemma lookup_walk_reduce:
  "(ref, ptr) \<in> lookup_walk cs m refs q
  \<Longrightarrow> (ref, ptr) \<in> lookup_walk cs m ref ptr"
  by (clarsimp simp: lookup_walk_def)

lemma lookup_walk_trivial:
  "a \<in> lookup_walk cs m ref ptr
  \<Longrightarrow> (ref, ptr) \<in> lookup_walk cs m ref ptr"
  apply (clarsimp simp: lookup_walk_def Image_def)
  apply (erule bexI[rotated])
  apply (erule rtrancl_trans)
  apply clarsimp
  apply (drule_tac ref = x in lookup_trancl_cut)
  apply clarsimp
  done

lemma lookup_walk_imp_reachable:
  "p \<in> lookup_walk cs m r ptr \<Longrightarrow> (r, ptr) \<in> cs^* `` m"
  apply (clarsimp simp: lookup_walk_def Image_def)
  apply (erule bexI[rotated])
  apply (erule rtrancl_trans)
  apply (erule lookup_trancl_cut[where ra = "[]", simplified])
  done

lemma lookup_trancl_walk:
  "(([], pa), ref, rptr) \<in> cs\<^sup>* \<Longrightarrow> (ref, rptr) \<in> lookup_walk cs {([],pa)} ref rptr"
  by (clarsimp simp: lookup_walk_def)

lemma lookup1_eq_ref:
  "(ref, ptr) \<in> lookup_walk cs m ref p \<Longrightarrow> p = ptr"
  by (clarsimp simp: lookup_walk_def)

lemma lookup_walk_decomp:
  "(a, ptr) \<in> lookup_walk cs rset r rptr \<Longrightarrow>
  \<exists>h. r = h @ a \<and> (h,rptr) \<in> lookup_walk cs ({([], ptr)}) h rptr"
  apply (clarsimp simp: lookup_walk_def)
  done

lemma lookup_walk_decomp_more:
  "(h @ [b],rptr) \<in> lookup_walk cs ({([], ptr)}) (h @ [b]) rptr \<Longrightarrow>
    \<exists>p. (([], ptr), [b], p) \<in> cs \<and> (([], p), h, rptr) \<in> cs\<^sup>*"
  apply (clarsimp simp: lookup_walk_def)
  apply (erule converse_rtranclE)
   apply clarsimp
  apply clarsimp
  apply (frule lookup1_is_append)
  apply clarsimp
  apply (frule lookup_ref_step)
  apply (intro exI conjI)
   apply force
  apply (rule lookup_trancl_append)
  apply force
  done

lemma lookupable_refs_set:
  shows "lookupable_refs cs refs (lookup_refs a f)
    \<subseteq> lookupable_refs cs refs (lookup_refs a f - lookup_refs b f) \<union> lookupable_refs cs refs (lookup_refs b f)"
  apply (fastforce simp: lookupable_refs_def Image_def)
  done

lemma in_lookupable_refsI:
  "\<lbrakk>(ref, ptr) \<in> cs\<^sup>* `` rset; f obj b a ; ((a, b), refs, rptr) \<in> cs\<^sup>*\<rbrakk> \<Longrightarrow>
  (refs @ ref, rptr) \<in> lookupable_refs cs {ref. (ref, ptr) \<in> cs\<^sup>* `` rset} (lookup_refs obj f)"
  apply (clarsimp simp: lookupable_refs_def Image_def)
  apply (intro exI conjI)
    apply fastforce
   apply fastforce
  apply (clarsimp simp: lookup_refs_def)
  apply fastforce
  done

(* The main result for this locale *)
theorem khupd_graph_subset:
  assumes wlcs: "wellformed_lookup cs' (kh(ptr := obj)) f"
  shows "(refs, p) \<in> cs'^* `` rset \<Longrightarrow> \<exists>sref. (sref, p) \<in> cs^* `` rset \<union> lookupable_refs cs
      {ref. (ref, ptr) \<in> cs^* `` rset} (lookup_refs obj f)"
  proof (induct "length refs" arbitrary: refs p)
   case 0
   note "0.prems" "0.hyps"
   thus ?case
    apply clarsimp
    apply (erule rtranclE, fastforce)
    apply (clarsimp dest!: wellformed_lookup.lookup1_is_append[OF wlcs])
    done
   next
   case Suc
   thus ?case
    apply (insert Suc.hyps(2) Suc.prems)
    apply (clarsimp del: disjCI)
    apply (erule rtranclE)
     apply fastforce
    apply (case_tac y, clarsimp del: disjCI)
    apply (rename_tac ref mptr)
    apply (frule  wellformed_lookup.lookup1_is_append[OF wlcs])
    apply (clarsimp del: disjCI)
    apply (drule Suc.hyps(1))
     apply (fastforce simp: Image_def)
    apply clarsimp
    apply (case_tac "mptr = ptr")
     apply (elim disjE)
      apply (rule_tac x = "refa # sref" in exI)
      apply (rule disjI2)
      apply (clarsimp simp: lookupable_refs_def lookup_refs_def)
      apply (drule wellformed_lookup.lookup1_append_singleton[OF wlcs])
      apply (clarsimp dest!:wellformed_lookup.trans_dependsD[OF wlcs])
      apply ((rule exI | rule conjI | force)+)[1]
     apply clarsimp
     apply (clarsimp simp: lookupable_refs_def)
     apply (intro disjI2 exI conjI | force)+
      apply (drule wellformed_lookup.lookup1_append_singleton[OF wlcs])
      apply (clarsimp dest!:wellformed_lookup.trans_dependsD[OF wlcs])
      apply (fastforce simp: Image_def lookup_refs_def)
    apply (clarsimp simp: Image_def)
    apply (drule wellformed_lookup.lookup1_append_singleton[OF wlcs])
    apply (clarsimp dest!:wellformed_lookup.trans_dependsD[OF wlcs])
    apply (rule exI)
    apply (elim disjE)
     apply (rule disjI1)
     apply (clarsimp simp: Image_def trans_depends_eq[symmetric])
     apply ((intro conjI bexI
              | simp add: obj_at_def
              | erule lookup1_cut_singleton
              | erule rtrancl_into_rtrancl)+)[1]
    apply (rule disjI2)
    apply (clarsimp simp: lookupable_refs_def Image_def trans_depends_eq[symmetric])
    apply (intro conjI exI)
      apply (rule_tac x = "(aa,ba)" in bexI)
       apply simp+
    apply (clarsimp simp: lookup_refs_def)
    apply ((intro conjI exI bexI
              | simp add: obj_at_def
              | erule lookup1_cut_singleton
              | erule rtrancl_into_rtrancl)+)[1]
    done
   qed
end

lemma lookup_bound_estimate:
  assumes wlcs: "wellformed_lookup cs kh f"
  and   wlcs': "wellformed_lookup cs' kh' f"
  and bound: "\<And>p. lookup_refs (kh' p) f \<subseteq> lookup_refs (kh p) f"
  shows "(refs, p) \<in> cs'^* `` rset \<Longrightarrow> (refs, p) \<in> cs^* `` rset"
  apply (clarsimp simp: Image_def)
  apply (erule_tac x = "(a,b)" in bexI[rotated])
  apply (induct refs arbitrary: p)
   apply (erule rtranclE)
   apply (clarsimp dest!: wellformed_lookup.lookup1_is_append[OF wlcs'])+
  apply (erule rtranclE)
   apply simp
  apply (rule_tac b = y in rtrancl_into_rtrancl)
   apply (clarsimp dest!: wellformed_lookup.lookup1_is_append[OF wlcs'])
  apply (case_tac y,clarsimp)
  apply (frule wellformed_lookup.lookup_ref_step[OF wlcs'])
  apply clarsimp
  apply (frule wellformed_lookup.lookup1_is_append[OF wlcs'])
  apply clarsimp
  apply (rule  wellformed_lookup.lookup1_cut[OF wlcs,where ra = "[]" and r = "[a]" for a,simplified])
  apply (drule wellformed_lookup.lookup1_append[OF wlcs', where ra = "[]" and r = "[a]" for a, simplified])
  apply (simp add: wellformed_lookup.trans_depends_eq[OF wlcs] wellformed_lookup.trans_depends_eq[OF wlcs'])
  apply (insert bound)
  apply (clarsimp simp: lookup_refs_def)
  apply fastforce
  done

lemma trans_depends_vs_walk:
  assumes wlcs: "wellformed_lookup cs kh f"
    and   wlcs': "wellformed_lookup cs' kh' f"
    and stick: "\<And>r q. (r, q) \<in> lookup_walk cs m ref p \<Longrightarrow> kh' q = kh q"
  shows "lookup_walk cs m ref p \<subseteq> lookup_walk cs' m ref p"
  apply (subgoal_tac "\<forall>r q. (r, q) \<in> lookup_walk cs m ref p \<longrightarrow> kh' q = kh q")
  prefer 2
    apply (clarsimp simp: stick)
  proof (induct ref arbitrary: p)
  case Nil
  show ?case
    by (simp add: wellformed_lookup.empty_lookup_walk[OF wlcs]
                  wellformed_lookup.empty_lookup_walk[OF wlcs'])
  next
  case Cons
  show ?case
    apply clarsimp
    apply (frule wellformed_lookup.lookup_walk_stepD[OF wlcs])
    apply (elim disjE)
     apply clarsimp
     apply (drule wellformed_lookup.lookup_walk_step_hdD[OF wlcs])
     apply (erule disjE)
      apply (fastforce simp: lookup_walk_def Image_def)
     apply clarsimp
     apply (rule wellformed_lookup.lookup_walk_stepI2[OF wlcs'])
      apply (erule subsetD[OF Cons.hyps, rotated])
      apply clarsimp
      apply (drule(1) wellformed_lookup.lookup_walk_stepI1[OF wlcs])
      apply (insert Cons.prems, fastforce)
     apply (drule(1) wellformed_lookup.lookup_walk_stepI1[OF wlcs])
     apply (clarsimp simp: wellformed_lookup.trans_depends_eq[OF wlcs] wellformed_lookup.trans_depends_eq[OF wlcs'])
    apply (elim exE conjE)
    apply (rule wellformed_lookup.lookup_walk_stepI1[OF wlcs'])
     apply (erule subsetD[OF Cons.hyps,rotated])
     apply clarsimp
      apply (drule(1) wellformed_lookup.lookup_walk_stepI1[OF wlcs])
      apply (insert Cons.prems, fastforce)
    apply clarsimp
    apply (drule_tac ptr = ptr in wellformed_lookup.lookup_walk_trivial[OF wlcs])
    apply (drule(1) wellformed_lookup.lookup_walk_stepI1[OF wlcs])
    apply (clarsimp simp: wellformed_lookup.trans_depends_eq[OF wlcs] wellformed_lookup.trans_depends_eq[OF wlcs'])
    done
  qed


locale wellformed_order_lookup = wellformed_lookup +
  fixes ev :: "'b\<Rightarrow>nat" and rset
  assumes lookup1_increase: "\<And>p q r ref. \<lbrakk>(ref,p) \<in> cs^* `` rset; (([],p),[r],q) \<in> cs \<rbrakk> \<Longrightarrow> ev (kh p) < ev (kh q)"

context wellformed_order_lookup
begin
lemma lookup1_increaseD:
  "\<lbrakk>(ref,p) \<in> cs^* `` rset; (([],p),[r],q) \<in> cs\<rbrakk> \<Longrightarrow> ev (kh p) < ev (kh q)"
  apply (insert lookup1_increase)
  apply (fastforce)
  done

lemma lookup_walk_distinct_strong:
  "(ref, ptr) \<in> lookup_walk cs rset (r @ ref) q \<Longrightarrow> (ev (kh ptr)) < (ev (kh q)) \<or> r = []"
  proof (induct "length r" arbitrary: ref ptr q r)
  case 0
  show ?case
    apply (insert "local.0")
    by clarsimp
  next
  case Suc
  show ?case
    apply (insert Suc.prems Suc.hyps(2))
    apply (case_tac r, simp)
    apply clarsimp
    apply (drule lookup_walk_stepD)
    apply (elim disjE, clarsimp)
    apply clarsimp
    apply (frule Suc.hyps(1)[rotated])
     apply fastforce
    apply (elim disjE)
     apply (frule lookup_walk_imp_reachable)
     apply (drule(1) lookup1_increaseD)
     apply clarsimp
    apply (frule lookup_walk_imp_reachable)
    apply (drule(1) lookup1_increaseD)
    apply (clarsimp dest!:lookup1_eq_ref)
    done
  qed

lemma lookup1_trans_increase:
  "\<lbrakk>(ref,p) \<in> cs^* `` rset; ((a,p),b,q) \<in> cs^+ \<rbrakk> \<Longrightarrow> ev (kh p) < ev (kh q)"
  apply (drule reachable_walk)
  apply (frule lookup_ref_step[OF trancl_into_rtrancl])
  apply clarsimp
  apply (drule lookup_walk_stepsI1)
   apply (rule lookup_trancl_append)
   apply force
  apply (drule lookup_walk_distinct_strong)
  apply clarsimp
  apply (erule tranclE)
   apply (clarsimp dest!: lookup1_is_append lookup_ref_step trancl_into_rtrancl)+
  done

lemma lookup_walk_unique:
  "(ref', ptr) \<in> lookup_walk cs rset ref ptr \<Longrightarrow> ref = ref'"
  proof (induct "length ref" arbitrary: ref ptr ref')
  case 0
  show ?case
    apply (insert "local.0")
    by (clarsimp simp:empty_lookup_walk)
  next
  case Suc
  show ?case
    apply (insert Suc.prems Suc.hyps(2))
    apply (case_tac ref)
     apply simp
    apply clarsimp
    apply (drule lookup_walk_stepD)
    apply (elim disjE, clarsimp)
    apply clarsimp
    apply (frule lookup_walk_distinct_strong)
    apply (frule lookup_walk_imp_reachable)
    apply (drule(1) lookup1_increaseD)
    apply (clarsimp dest!: lookup1_eq_ref)
    done
  qed

lemma lookup_walk_unique_from_root:
  "\<lbrakk>(([], ptr), b, ptr) \<in> cs^*; (ref,ptr) \<in> cs^* `` rset\<rbrakk> \<Longrightarrow> b = []"
  apply (subgoal_tac "b @ ref = ref")
   apply simp
  apply (rule lookup_walk_unique)
  apply (simp add: lookup_walk_def)
  done

lemma  lookup_walk_kh_upd:
  "\<lbrakk>wellformed_order_lookup cs' (kh(ptr := obj)) f ev rset; (q, ptr) \<in> lookup_walk cs rset q ptr \<rbrakk>
    \<Longrightarrow> (q, ptr) \<in> lookup_walk cs' rset q ptr"
  apply (case_tac q)
   apply (clarsimp simp: empty_lookup_walk)
   apply (fastforce simp: lookup_walk_def Image_def)
  apply clarsimp
  apply (frule lookup_walk_step_hdD)
   apply (elim disjE)
   apply (fastforce simp: lookup_walk_def Image_def)
  apply (clarsimp simp: Image_def)
  apply (cut_tac m = rset and ref = list and p = y
          in trans_depends_vs_walk[OF local.wellformed_lookup_axioms])
    apply (erule wellformed_order_lookup.axioms)
   apply clarsimp
   apply (drule_tac p = "(r, ptr)" in lookup_walk_stepI1[rotated])
    apply simp
   apply (clarsimp dest!: lookup_walk_unique)
   apply (drule lookup_walk_decomp)
   apply simp
  apply (rule wellformed_lookup.lookup_walk_stepI2)
    apply (erule wellformed_order_lookup.axioms)
   apply fastforce
  apply (subst wellformed_lookup.trans_depends_eq)
   apply (erule wellformed_order_lookup.axioms)
  apply (subgoal_tac "y \<noteq> ptr")
   apply (simp add: trans_depends_eq)
  apply clarsimp
   apply (drule_tac p = "(list, ptr)" in lookup_walk_stepI1[rotated])
   apply simp
  apply (clarsimp dest!: lookup_walk_unique)
  done

lemma lookup_walk_path_distinct:
  "h \<noteq> [] \<Longrightarrow> (q, ptr) \<in> lookup_walk cs rset (h @ q) rptr \<Longrightarrow> ptr \<noteq> rptr"
  apply (rule ccontr)
  apply clarsimp
  apply (drule lookup_walk_unique)
  apply simp
  done

(*
   This lemma should not be used out side of this locale.
   Please use kpupd_wellformed_order_lookup instead.
*)
lemma khupd_wellform_order_lookup_pref:
  assumes wlos: "wellformed_order_lookup cs' (kh(ptr := obj)) f ev rset"
  shows "cs'^* `` rset \<subseteq> cs^* `` rset \<union> lookupable_refs cs
      {ref. (ref, ptr) \<in> cs^* `` rset} (lookup_refs obj f)"
  proof -
  have wlcs: "wellformed_lookup cs' (kh(ptr := obj)) f"
   by (intro wellformed_order_lookup.axioms[OF wlos])
  have kh_upd_dummy[simp]:
     "(kh(ptr := obj, ptr := kh ptr)) = kh"
  by auto
  have l: "\<And>ys y q.  ys @ y # q = (ys @ [y]) @ q"
  by auto
  show ?thesis
  apply (rule subsetI)
  apply (clarsimp del: disjCI)
  apply (rename_tac r rptr ref p)
  apply (erule rtranclE)
   apply (fastforce simp: wellformed_lookup.empty_lookup_walk[OF wlcs] Image_def)
  apply (insert wlcs)
  apply (drule wellformed_lookup.reachable_walk)
   apply (simp add: Image_def)
   apply fastforce
  apply (case_tac "\<exists>q. (q, ptr) \<in> lookup_walk cs' rset r rptr")
   apply (clarsimp del: disjCI)
   apply (frule_tac ptr = ptr in wellformed_lookup.lookup_walk_reduce[OF wlcs])
   apply (drule_tac obj = "kh ptr" and ptr = ptr and cs' = cs in wellformed_order_lookup.lookup_walk_kh_upd[rotated -1,OF _ wlos])
    apply simp
    apply (rule wellformed_order_lookup_axioms)
   apply (frule_tac rptr = rptr in wellformed_lookup.lookup_walk_decomp[OF wlcs])
   apply (clarsimp del: disjCI)
   apply (rule_tac xs = h in rev_cases)
    apply (clarsimp simp: wellformed_lookup.empty_lookup_walk[OF wlcs])
    apply (simp add: lookup_walk_def)
   apply (rule disjI2)
   apply clarsimp
   apply (drule wellformed_lookup.lookup_walk_decomp_more[OF wlcs])
   apply clarsimp
   apply (drule wellformed_lookup.lookup_trancl_walk[OF wlcs])
   apply (drule_tac ref = q in wellformed_lookup.lookup_walk_reduce[OF wlcs])
   apply (drule_tac c="(ys, rptr)" in subsetD[OF trans_depends_vs_walk,rotated -1])
      apply (rule wlcs)
     apply (rule local.wellformed_lookup_axioms)
    apply clarsimp
    apply (drule_tac ref = r in wellformed_lookup.lookup_walk_reduce[OF wlcs])
    apply (frule_tac ptr = ptr in wellformed_order_lookup.lookup_walk_unique_from_root
                 [OF wlos _ wellformed_lookup.lookup_walk_imp_reachable[OF wlcs],rotated])
     apply (erule converse_rtrancl_into_rtrancl)
     apply (drule wellformed_lookup.lookup_walk_imp_reachable[OF wlcs])+
     apply (clarsimp simp: Image_def)
     apply (rule wellformed_lookup.lookup_trancl_cut[OF wlcs, where ra = "[]",simplified])
     apply simp
    apply simp
   apply (subst l)
   apply (rule in_lookupable_refsI)
     apply (clarsimp dest!: lookup_walk_imp_reachable)
    apply (drule wellformed_lookup.trans_dependsD[OF wlcs])
    apply simp
   apply (rule lookup_trancl_cut[where ra ="[]",simplified])
   apply (clarsimp dest!: lookup_walk_imp_reachable)
   apply simp
  apply (cut_tac m = rset and ref=r and p = rptr
          in trans_depends_vs_walk[OF wlcs local.wellformed_lookup_axioms])
   apply clarsimp
  apply (drule subsetD)
   apply (rule wellformed_lookup.reachable_walk[OF wlcs])
   apply (clarsimp simp: Image_def)
   apply (erule bexI[rotated])
   apply (erule(1) rtrancl_into_rtrancl)
  apply (simp add: lookup_walk_imp_reachable)
  done
  qed

lemma lookupable_refs_reachable:
  "lookupable_refs cs {ref. (ref, ptr) \<in> cs\<^sup>* `` rset} (lookup_refs (kh ptr) f)
   \<subseteq> cs\<^sup>* `` rset"
   apply (clarsimp simp: lookupable_refs_def Image_def lookup_refs_lookup1)
   apply (erule bexI[rotated])
   apply (erule rtrancl_trans)
   apply (frule lookup1_is_append)
   apply clarsimp
   apply (erule converse_rtrancl_into_rtrancl[OF lookup1_cut_singleton])
   apply (drule lookup_trancl_cut)
   apply force
   done

lemma khupd_wellformed_order_lookup_private:
  assumes well_order:
    "\<And>nref np stepref nq sref. \<lbrakk>(nref,np) \<in> cs^* `` (lookup_refs obj f); (([],np),[stepref],nq) \<in> cs; (sref, ptr)\<in> cs^* `` rset\<rbrakk>
    \<Longrightarrow> ev (kh np) < ev (kh nq)"
  and well_order_as_parent:
    "\<And>nref np sref. \<lbrakk>(nref,np) \<in> lookup_refs obj f; (sref, ptr)\<in> cs^* `` rset\<rbrakk> \<Longrightarrow> ev (obj) < ev (kh np)"
  and well_order_as_leaf:
    "\<And>p r sref. \<lbrakk>((r, p), sref, ptr) \<in> cs^+ ;(r, p) \<in> cs^* `` rset\<rbrakk> \<Longrightarrow> ev (kh p) < ev (obj)"
  and wlcs: "wellformed_lookup cs' (kh(ptr := obj)) f"
  shows "ev (kh ptr) \<le> ev obj \<Longrightarrow> wellformed_order_lookup cs' (kh(ptr := obj)) f ev rset"
  apply (intro wellformed_order_lookup.intro[OF wlcs])
  apply (intro wellformed_order_lookup_axioms.intro)
  apply (drule khupd_graph_subset[OF wlcs])
  apply (clarsimp simp: wellformed_lookup.trans_depends_eq[OF wlcs])
  apply (elim disjE)
   apply (clarsimp split: if_splits)
    apply (cut_tac nref = "[r]" and np = q in well_order_as_parent)
      apply (clarsimp simp: Image_def lookup_refs_def)
     apply (fastforce simp: Image_def)
    apply clarsimp
   apply (clarsimp simp: trans_depends_eq[symmetric])
   apply (intro conjI impI)
    apply (rule well_order_as_leaf[rotated])
     apply (fastforce simp: Image_def)
    apply (rule r_into_trancl')
    apply (rule lookup1_cut_singleton)
    apply force
   apply (rule lookup1_increase)
    apply (clarsimp simp: Image_def)
    apply (erule bexI[rotated])
    apply simp
   apply simp
  apply (clarsimp simp: lookupable_refs_def split: if_splits)
   apply (cut_tac nref = "[r]" and np = q in well_order_as_parent)
     apply (clarsimp simp: Image_def lookup_refs_def)
    apply (fastforce simp: Image_def)
   apply clarsimp
  apply (clarsimp simp: trans_depends_eq[symmetric])
  apply (intro conjI impI)
   apply clarsimp
   apply (frule well_order_as_parent)
    apply fastforce
   apply (drule well_order[rotated])
     apply fastforce+
  apply (frule well_order[rotated])
    apply (fastforce)+
  done

lemma khupd_wellformed_order_lookup:
  assumes well_order:
    "\<And>nref np stepref nq sref. \<lbrakk>(nref,np) \<in> cs^* `` (lookup_refs obj f - lookup_refs (kh ptr) f); (([],np),[stepref],nq) \<in> cs; (sref, ptr)\<in> cs^* `` rset\<rbrakk>
    \<Longrightarrow> ev (kh np) < ev (kh nq)"
  and well_order_as_parent:
    "\<And>nref np sref. \<lbrakk>(nref,np) \<in> (lookup_refs obj f - lookup_refs (kh ptr) f); (sref, ptr)\<in> cs^* `` rset\<rbrakk> \<Longrightarrow> ev (obj) < ev (kh np)"
  and well_order_as_leaf:
    "\<And>p r sref. \<lbrakk>((r, p), sref, ptr) \<in> cs^+ ;(r, p) \<in> cs^* `` rset\<rbrakk> \<Longrightarrow> ev (kh p) < ev (obj)"
  and wlcs: "wellformed_lookup cs' (kh(ptr := obj)) f"
  shows "ev (kh ptr) = ev obj \<Longrightarrow> wellformed_order_lookup cs' (kh(ptr := obj)) f ev rset"
  apply (rule khupd_wellformed_order_lookup_private[OF _ _ well_order_as_leaf wlcs])
       apply clarsimp
       apply (case_tac "(a,b) \<in> lookup_refs (kh ptr) f")
        apply (rule lookup1_increaseD)
         apply (clarsimp simp: Image_def)
         apply (erule bexI[rotated])
         apply (erule rtrancl_trans)
         apply (rule converse_rtrancl_into_rtrancl)
          apply (simp add: lookup_refs_lookup1)
          apply (drule_tac b = sref in lookup1_cut[where q = ptr])
          apply fastforce
         apply (erule lookup_trancl_cut)
        apply simp
       apply (rule well_order, fastforce+)
     apply clarsimp
     apply (case_tac "(nref,np) \<in> lookup_refs (kh ptr) f")
      apply (clarsimp simp: Image_def lookup_refs_lookup1)
      apply (frule lookup1_is_append)
      apply clarsimp
      apply (erule subst)
       apply (rule lookup1_trans_increase)
       apply (clarsimp simp: Image_def)
       apply (erule bexI[rotated])
        apply (simp add: lookup_refs_lookup1)+
       apply fastforce
      apply (rule well_order_as_parent,fastforce+)
   done

(* The main result for this locale *)
theorem khupd_graph_subset:
  assumes wlos: "wellformed_order_lookup cs' (kh(ptr := obj)) f ev rset"
  shows "cs'^* `` rset \<subseteq> cs^* `` rset \<union> lookupable_refs cs
      {ref. (ref, ptr) \<in> cs^* `` rset} (lookup_refs obj f - lookup_refs (kh ptr) f)"
  proof -
  have set_plus_mono: "\<And>a b c d. \<lbrakk>a \<subseteq> b \<union> c; c \<subseteq> d\<rbrakk> \<Longrightarrow> a \<subseteq> b \<union> d"
    by auto
  show ?thesis
    apply (insert khupd_wellform_order_lookup_pref[OF wlos])
    apply (drule set_plus_mono)
     apply (rule_tac b = "kh ptr" in lookupable_refs_set)
    apply (cut_tac ptr = ptr in lookupable_refs_reachable)
    apply fastforce
    done
  qed
end

context Arch begin arch_global_naming

locale_abbrev "vs_lookup_leaf ptr s \<equiv> lookup_leaf ptr (vs_lookup1 s)"

primrec vsref_of :: "vs_ref \<Rightarrow> word64"
where
  "vsref_of (VSRef x _ ) = x"

definition
  vs_ref_lvl_arch :: "arch_kernel_obj \<Rightarrow> nat"
where
  "vs_ref_lvl_arch atype \<equiv> case aa_type atype of
      AASIDPool \<Rightarrow> 1
    | APageMapL4 \<Rightarrow> 2
    | APDPointerTable \<Rightarrow> 3
    | APageDirectory \<Rightarrow> 4
    | APageTable \<Rightarrow> 5
    | _ \<Rightarrow> 6"

definition
  "vs_ref_lvl obj_opt \<equiv> case_option 7 (arch_obj_fun_lift vs_ref_lvl_arch 7) obj_opt"

lemma vs_ref_lvl_arch_obj [simp]:
  "vs_ref_lvl (Some (ArchObj aobj)) = vs_ref_lvl_arch aobj"
  by (simp add: vs_ref_lvl_def)

lemma vs_ref_lvl_arch_simps [simp]:
  "vs_ref_lvl_arch (ASIDPool ap) = 1"
  "vs_ref_lvl_arch (PageMapL4 pm) = 2"
  "vs_ref_lvl_arch (PDPointerTable pdpt) = 3"
  "vs_ref_lvl_arch (PageDirectory pd) = 4"
  "vs_ref_lvl_arch (PageTable pt) = 5"
  "vs_ref_lvl_arch (DataPage dev sz) = 6"
  by (auto simp: vs_ref_lvl_arch_def aa_type_def)

definition
  "vs_lookup1_on_heap_obj \<equiv> \<lambda>obj q h. (\<exists>ko. obj = Some ko \<and> (\<exists>r. h = [r] \<and> (r, q) \<in> vs_refs ko))"

definition
  "vs_lookup_pages1_on_heap_obj \<equiv> \<lambda>obj q h. (\<exists>ko. obj = Some ko \<and> (\<exists>r. h = [r] \<and> (r, q) \<in> vs_refs_pages ko))"

sublocale vs_lookup1_wellformed:
  wellformed_lookup "vs_lookup1 s" "kheap s" vs_lookup1_on_heap_obj
  apply unfold_locales
       apply (clarsimp simp: trans_depends_def vs_lookup1_def obj_at_def vs_lookup1_on_heap_obj_def)+
   apply (clarsimp simp: vs_refs_def up_ucast_inj_eq graph_of_def
                  split: kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp: vs_lookup1_on_heap_obj_def)
  done

lemmas vs_lookup1_is_wellformed_lookup
  = vs_lookup1_wellformed.wellformed_lookup_axioms

sublocale vs_lookup_pages1_wellformed:
  wellformed_lookup "vs_lookup_pages1 s" "kheap s" vs_lookup_pages1_on_heap_obj
  apply unfold_locales
       apply (clarsimp simp: trans_depends_def vs_lookup_pages1_def obj_at_def vs_lookup_pages1_on_heap_obj_def)+
   apply (clarsimp simp: vs_refs_pages_def up_ucast_inj_eq graph_of_def
                  split: kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp: vs_lookup_pages1_on_heap_obj_def)
  done

lemmas vs_lookup_pages1_is_wellformed_lookup
  = vs_lookup_pages1_wellformed.wellformed_lookup_axioms

lemma vs_refs_pages_vs_ref_lvl:
  "\<lbrakk> ko_at (ArchObj aobj) p s; (r, q) \<in> vs_refs_pages (ArchObj aobj); valid_vspace_obj aobj s \<rbrakk>
     \<Longrightarrow> vs_ref_lvl (kheap s p) < vs_ref_lvl (kheap s q)"
  apply (cases aobj;
         clarsimp simp: vs_refs_pages_def graph_of_def ball_ran_eq obj_at_def
                        pte_ref_pages_def pde_ref_pages_def pdpte_ref_pages_def pml4e_ref_pages_def
                 split: if_splits pte.splits pde.splits pdpte.splits pml4e.splits;
         match premises in H [thin]: "\<forall>i. P (t i)" and J: "t i = v" for P t i v \<Rightarrow>
                              \<open>insert spec[where x=i, OF H]\<close>
                         \<bar> H [thin]: "\<forall>i \<in> S. P (t i)" and J: "t i = v" for P S t i v \<Rightarrow>
                              \<open>insert bspec[where x=i, OF H]\<close>)
  by (auto simp: obj_at_def data_at_def)

lemmas vs_refs_vs_ref_lvl = vs_refs_pages_vs_ref_lvl[OF _ vs_refs_vs_refs_pages]

lemma vs_lookup1_wellformed_order:
  "valid_vspace_objs s
    \<Longrightarrow> wellformed_order_lookup (vs_lookup1 s) (kheap s) vs_lookup1_on_heap_obj
                                vs_ref_lvl (vs_asid_refs (x64_asid_table (arch_state s)))"
  apply (intro wellformed_order_lookup.intro vs_lookup1_wellformed.wellformed_lookup_axioms
               wellformed_order_lookup_axioms.intro)
  apply (simp only: vs_lookup_def2[symmetric])
  apply (clarsimp simp add: vs_lookup1_def)
  apply (case_tac ko; (clarsimp simp: vs_refs_def; fail)?; rename_tac ako; clarsimp)
  apply (frule (2) valid_vspace_objsD)
  apply (case_tac ako; clarsimp simp: vs_refs_def)
     apply (drule (1) graph_of_in_ranD; clarsimp simp: obj_at_def)
    apply (match premises in "(i,_) \<in> graph_of _" for i \<Rightarrow>
            \<open>match premises in H[thin]: "\<forall>i. P i" for P \<Rightarrow> \<open>insert spec[where x=i, OF H]\<close>
                             \<bar> H[thin]: "\<forall>i\<in>_. P i" for P \<Rightarrow> \<open>insert bspec[where x=i, OF H]\<close>\<close>;
           fastforce simp: graph_of_def obj_at_def
                           pde_ref_def pdpte_ref_def pml4e_ref_def
                    split: pde.splits pdpte.splits pml4e.splits if_splits)+
  done

lemma vs_lookup_pages1_wellformed_order:
  "\<lbrakk> valid_vspace_objs s; valid_asid_table (x64_asid_table (arch_state s)) s \<rbrakk>
    \<Longrightarrow> wellformed_order_lookup (vs_lookup_pages1 s) (kheap s) vs_lookup_pages1_on_heap_obj
                                vs_ref_lvl (vs_asid_refs (x64_asid_table (arch_state s)))"
  apply (intro wellformed_order_lookup.intro vs_lookup_pages1_wellformed.wellformed_lookup_axioms
               wellformed_order_lookup_axioms.intro)
  apply (simp only: vs_lookup_pages_def2[symmetric])
  apply (clarsimp simp add: vs_lookup_pages1_def)
  apply (case_tac ko; (clarsimp simp: vs_refs_pages_def; fail)?; rename_tac ako; clarsimp)
  apply (frule (3) valid_vspace_objsD')
  apply (case_tac ako; clarsimp simp: vs_refs_pages_def)
      apply (drule (1) graph_of_in_ranD; clarsimp simp: obj_at_def)
     apply (match premises in "(x,y) \<in> graph_of f" for f x y \<Rightarrow>
             \<open>match premises in H[thin]: "\<forall>i. P i" for P \<Rightarrow> \<open>insert spec[where x=x, OF H]\<close>
                              \<bar> H[thin]: "\<forall>i\<in>_. P i" for P \<Rightarrow> \<open>insert bspec[where x=x, OF H]\<close>\<close>;
            fastforce simp: graph_of_def obj_at_def data_at_def
                            pte_ref_pages_def pde_ref_pages_def pdpte_ref_pages_def pml4e_ref_pages_def
                     split: pte.splits pde.splits pdpte.splits pml4e.splits if_splits)+
  done

definition
  refs_diff :: "(kernel_object option \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> bool)
                  \<Rightarrow> arch_kernel_obj \<Rightarrow> 64 word \<Rightarrow> 'c abstract_state_scheme \<Rightarrow> ('a list \<times> 'b) set"
where
  "refs_diff lf obj ptr s = (lookup_refs (Some (ArchObj obj)) lf - lookup_refs (kheap s ptr) lf)"

end

end
