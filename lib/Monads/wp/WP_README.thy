(*
 * Copyright 2024, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
*)

theory WP_README
  imports
    Nondet_More_VCG
begin

\<comment> \<open>The 'WP' tool and friends\<close>

text\<open>
The monad framework comes with a collection of tools which
together perform the role of a VCG (verification condition generator).

The usual strategy for proving a Hoare triple is via backward propagation from
the postcondition. The initial step is to replace the current precondition with
an Isabelle schematic variable using a precondition weakening rule such as
@{thm hoare_pre}. This schematic variable is progressively instantiated by applying
weakest precondition rules as introduction rules. The implication between the
assumed and generated preconditions must be solved by some other means.

This approach requires a large family of weakest precondition rules, including
one for each monadic combinator and operation, and further rules for
user-defined monadic operations. The @{method wp} tool automates the storage and use of
this collection of rules. Weakest precondition rules are marked with the 'wp'
attribute and are then automatically applied.

The 'wp' tool also handles the construction of variations of 'wp' rules
via combinator rules. If the postcondition being proved is a conjunction and a
weakest precondition rule is available for the first conjunct, progress can be
made by first applying the @{thm hoare_vcg_conj_lift} combinator rule and then the
rule of interest. The 'wp_comb' attribute given to such rules in
@{theory Monads.Nondet_VCG} specifies that they should be used in this way.

The 'wp' tool's semantics are defined entirely by these sets of rules.
Selection from a set of rules ('wp' and 'wp_split') or combinators ('wp_comb')
occurs in last-to-first order, i.e. always preferring to apply the theorem most
recently added to a set.
First, each 'wp' rule is attempted in the following order:
- on its own, as an introduction rule
- prefixed by a 'wp_comb' rule (i.e. 'rule wp_comb_rule, rule wp_rule').
If no 'wp' rule can be applied, rules from the 'wp_split' set are attempted
(on their own as introduction rules, without 'wp_comb' prefixes).

Note that rules may be supplied which are not the actual weakest precondition.
This may cause the tool to produce unhelpfully weak conclusions. The
@{thm hoare_vcg_prop} rule supplied in @{theory Monads.Nondet_VCG} is unsafe in this manner.
It is convenient that postconditions which ignore the results of the operation can
be handled immediately (especially when used with the combinator rules), however
information from assertions in the program may be discarded.

Rules declared 'wp' do not have to match an unspecified postcondition. It was
useful in the L4.verified project to instead prove a collection of rules about
a given program function, one for each conjunct appearing in postconditions. To
reduce the number of such conjuncts, it was useful to consider only simp-normal
postconditions. The 'wp' tool does not itself invoke the simplifier in any way,
but can be alternated with the simplifier e.g. 'apply (wp | simp)+'.

The principle caveat of the 'wp' approach is the use of an Isabelle schematic
variable. Care must be taken to ensure that a distinct schematic variable is
available to be instantiated with the precondition for each problem. This means
that case spliting cannot be done via Isabelle's normal mechanisms. Isabelle's
'safe' tools, such as 'safe' and 'clarsimp', also tend to create problems by
implicitly doing case splits on meta-quantified tuples in a way that blocks
unification.

The @{method wpc} tool synthesises the needed case split rules for datatype case
statements in the function bodies in the Hoare triples.

There are several cases where unification of the schematic preconditions can cause
problems. The @{method wpfix} tool handles four of the most common of these cases.
See @{theory Monads.WPFix} and @{theory Monads.Datatype_Schematic} for more details.

A further caveat is that the 'wp' and 'wp_comb' rulesets provided are not
necessarily ideal. Updating these rulesets would create difficult maintenance
problems, and thus they are largely left as first defined. One issue that has
not been addressed is the implicit precondition weakening done by combinator
rules @{thm hoare_post_comb_imp_conj} and @{thm hoare_weaken_pre}. In hindsight it
would be better if @{thm hoare_pre} were always applied manually, or if the 'wp'
tool itself could decide when they ought be applied. Note that such weakening
rules were not supplied for the error hoare triples/quadruple, which postdate
this realisation.

The 'wp' rule set may become quite large. The 'wp' tool uses a resolution net
to accelerate rule lookup. Matching is done only on the function body within
the Hoare triple. The 'wp_trip' rule set contains rewrites which convert
various hoare triples and other judgements into a standard form. It is assumed
that no combinator rules change the function body within the Hoare triple.

The 'wp' tool may be extended to new triples or other judgements by supplying
an appropriate set of rules. A 'wp_trip' rule may be provided to accelerate
rule lookup.

The `wp` tool can also be traced, either by invoking it with `wp (trace)` or by
setting the config value `wp_trace` to `true`. This will list the rules used by `wp`,
in the order that they were applied. It is occasionally helpful to see the specific
instantiations of the rules used, to see how their preconditions were unified. This
can be done by setting `wp_trace_instantiation` to `true`.

For ease of use, @{method wpsimp} is available and wraps up the standard usage pattern
of '(wpfix|wp|wpc|clarsimp)+'.\<close>

end
