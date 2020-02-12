(*
 *
 * Copyright 2017, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)
theory Strengthen_Demo

imports "Strengthen"

begin

text \<open>Here's a complicated predicate transformer. You don't need
to understand this, it just makes it easy to set up some complicated
example goals below.\<close>
definition
  "predt f g h P x y = (\<exists>x'. (\<exists>y' \<in> f y. x' \<in> g y' ` h y) \<and> P x x')"

text \<open>Strengthen performs the same kinds of steps as
intro/elim rules, but it can perform them within complex
conclusions. Here's an example where we replace Q with P
(strengthening the goal) deep within some quantifiers.\<close>

lemma predt_double_mono:
  assumes PQ: "\<And>x y. P x y \<longrightarrow> Q x y"
  assumes P: "predt f g h (predt f g h' P) x y"
  shows "predt f g h (predt f g h' Q) x y"
  using P
  apply (simp add: predt_def)
  apply (strengthen PQ)
  apply assumption
  done

text \<open>Here's a more conventional monotonicity proof.
Once the clarsimp has finished, the goal becomes a bit
difficult to prove. Let's use some fancy strengthen
features to address this. The rest of this demo will
explain what the attribute and fancy features are doing,
and thus how this proof works.\<close>

lemma predt_double_mono2:
  assumes PQ: "\<And>x y. P x y \<longrightarrow> Q x y"
  assumes P: "predt f g h (predt f g' h P) x y"
  shows "predt f g h (predt f g' h Q) x y"
  using P
  apply (clarsimp simp: predt_def)
  apply (strengthen bexI[mk_strg I _ A])
  apply (strengthen image_eqI[mk_strg I _ A])
  apply simp
  apply (strengthen bexI[mk_strg I _ O], assumption)
  apply (strengthen image_eqI[mk_strg I _ E])
  apply simp
  apply (simp add: PQ)
  done

text \<open>The @{attribute mk_strg} controls the way that
strengthen applies a rule. By default, strengthen will
use a rule as an introduction rule, trying to replace
the rule's conclusion with its premises.

Once the @{attribute mk_strg} attribute has applied, the
rule is formatted showing how strengthen will try to
transform components of a goal. The syntax of the
second theorem is reversed, showing that strengthen will
attempt to replace instances of the subset predicate
with instances of the proper subset predicate.
\<close>
thm psubset_imp_subset psubset_imp_subset[mk_strg]

text \<open>Rules can have any number of premises, or none,
and still be used as strengthen rules.\<close>
thm subset_UNIV subset_UNIV[mk_strg]
    equalityI equalityI[mk_strg]

text \<open>Rules which would introduce schematics are
adjusted by @{attribute mk_strg} to introduce quantifiers
instead. The argument I to mk_strg prevents this step.
\<close>
thm subsetD subsetD[mk_strg I] subsetD[mk_strg]

text \<open>The first argument to mk_strg controls the way
the rule will be applied.
  I: use rule in introduction style, matching its conclusion.
  D: use rule in destruction (forward) style, matching its first premise.
  I': like I, replace new schematics with existential quantifiers.
  D': like D, replace new schematics with universal quantifiers.

The default is I'.
\<close>
thm subsetD subsetD[mk_strg I] subsetD[mk_strg I']
  subsetD[mk_strg D] subsetD[mk_strg D']

text \<open>Note that I and D rules will be applicable at different
sites.\<close>
lemma
  assumes PQ: "P \<Longrightarrow> Q"
  shows "{x. Suc 0 < x \<and> P} \<subseteq> {x. Suc 0 < x \<and> Q}"
  (* adjust Q into P on rhs *)
  apply (strengthen PQ[mk_strg I])
  (* adjust P into Q on lhs *)
  apply (strengthen PQ[mk_strg D])
  (* oops, overdid it *)
  oops

text \<open>Subsequent arguments to mk_strg capture premises for
special treatment. The 'A' argument (synonym 'E') specifies that
a premise should be solved by assumption. Our fancy proof above
used a strengthen rule bexI[mk_strg I _ A], which tells strengthen
to do approximately the same thing as
\<open>apply (rule bexI) prefer 2 apply assumption\<close>

This is a useful way to apply a rule, picking the premise which
will cause unknowns to be instantiated correctly.
\<close>
thm eq_mem_trans eq_mem_trans[mk_strg I _ _] eq_mem_trans[mk_strg I A _]
    eq_mem_trans[mk_strg I _ A] eq_mem_trans[mk_strg I A A]

text \<open>The 'O' argument ("obligation") picks out premises of
a rule for immediate attention as new subgoals.

The step
\<open>apply (strengthen bexI[mk_strg I _ O], assumption)\<close>
in our proof above had the same effect as strengthening with
@{thm bexI[mk_strg I _ A]}.

This option suits special cases where a particular premise is best
handled by a specialised method.
\<close>
thm eq_mem_trans eq_mem_trans[mk_strg I _ _] eq_mem_trans[mk_strg I O _]
    eq_mem_trans[mk_strg I _ O] eq_mem_trans[mk_strg I O O]

end
