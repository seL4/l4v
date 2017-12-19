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

text {* Here's a complicated predicate transformer, which
sets up some quantifiers for our examples. *}
definition
  "predt f g h P x y = (\<exists>x'. (\<exists>y' \<in> f y. x' \<in> g y' ` h y) \<and> P x x')"

text {* Here's strengthen proving a monotonicity
property. We replace Q with P deep within the conclusion. *}

lemma predt_double_mono:
  assumes PQ: "P \<le> Q"
  assumes P: "predt f g h (predt f g h' P) x y"
  shows "predt f g h (predt f g h' Q) x y"
  using P
  apply (simp add: predt_def)
  apply (strengthen predicate2D[OF PQ])
  apply assumption
  done

text {* Here's a more conventional monotonicity proof,
which uses more strengthen features. At each strengthen
step our the goal is an existential quantifier which would
be unpleasant to instantiate by hand. Instead, we want to
use rule @{thm bexI} or @{thm image_eqI}, matching the
set-membership premise against one of our assumptions. *}

lemma predt_double_mono2:
  assumes PQ: "P \<le> Q"
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
  apply (rule predicate2D[OF PQ])
  apply simp
  done

text {* The @{attribute mk_strg} controls the way that
strengthen applies a rule. By default, strengthen will
use a rule as an introduction rule, trying to replace
the rule's conclusion with its premises.
*}
thm psubset_imp_subset psubset_imp_subset[mk_strg]

text {* This applies to rules with any number of premises,
including no premises. *}
thm subset_UNIV subset_UNIV[mk_strg]
    equalityI equalityI[mk_strg]

text {* Rules which would introduce schematics are
also adjusted to introduce quantifiers instead.
The argument I to mk_strg prevents this step.
*}
thm subsetD subsetD[mk_strg I] subsetD[mk_strg]

text {* The first argument to mk_strg controls the way
the rule will be applied.
  I: use rule in introduction style, matching its conclusion.
  D: use rule in destruction (forward) style, matching its first premise.
  I': like I, replace new schematics with existential quantifiers.
  D': like D, replace new schematics with universal quantifiers.

The default is I'.
*}
thm subsetD subsetD[mk_strg I] subsetD[mk_strg I']
  subsetD[mk_strg D] subsetD[mk_strg D']

text {* Note that I and D rules will be applicable at different
sites. *}
lemma
  assumes PQ: "P \<Longrightarrow> Q"
  shows "{x. Suc 0 < x \<and> P} \<subseteq> {x. Suc 0 < x \<and> Q}"
  (* adjust Q into P on rhs *)
  apply (strengthen PQ[mk_strg I])
  (* adjust P into Q on lhs *)
  apply (strengthen PQ[mk_strg D])
  (* oops, overdid it *)
  oops

text {* Subsequent arguments to mk_strg capture premises for
special treatment. The 'A' argument (synonym 'E') specifies that
a premise should be solved by assumption. The bexI[mk_strg I _ E]
rule in our proof above has approximately the same effect as
\<open>apply (rule bexI) prefer 2 apply assumption\<close>

This is a useful way to apply a rule, picking the premise which
will cause unknowns to be instantiated correctly.
*}
thm eq_mem_trans eq_mem_trans[mk_strg I _ _] eq_mem_trans[mk_strg I A _]
    eq_mem_trans[mk_strg I _ A] eq_mem_trans[mk_strg I A A]

text {* The 'O' argument ("obligation") picks out premises of
a rule for immediate attention as new subgoals.

The step
\<open>apply (strengthen bexI[mk_strg I _ O], assumption)\<close>
in our proof above had the same effect as strengthening with
@{thm bexI[mk_strg I _ A]}.

This option suits special cases where a particular premise is best
handled by a specialised method.
*}
thm eq_mem_trans eq_mem_trans[mk_strg I _ _] eq_mem_trans[mk_strg I O _]
    eq_mem_trans[mk_strg I _ O] eq_mem_trans[mk_strg I O O]

end
