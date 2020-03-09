#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

Readme for the 'WP' tool and friends

The nondeterministic monad framework comes with a collection of tools which
together perform the role of a VCG (verification condition generator).

The usual strategy for proving a Hoare triple is via backward propagation from
the postcondition. The initial step is to replace the current precondition with
an Isabelle schematic variable using a precondition weakening rule such as
'hoare_pre'. This schematic variable is progressively instantiated by applying
weakest precondition rules as introduction rules. The implication between the
assumed and generated preconditions must be solved by some other means.

This approach requires a large family of weakest precondition rules, including
one for each monadic combinator and operation, and further rules for
user-defined monadic operations. The 'wp' tool automates the storage and use of
this collection of rules. Weakest precondition rules are marked with the 'wp'
attribute and will be automatically applied.

The 'wp' tool also also handles the construction of variations of 'wp' rules
via combinator rules. If the postcondition being proved is a conjunction and a
weakest precondition rule is available for the first conjunct, progress can be
made by first applying the 'hoare_vcg_conj_lift' combinator rule and then the
rule of interest. The 'wp_comb' attribute given to such rules in
NonDetMonadVCG.thy specifies that they should be used in this way.

The 'wp' tool's semantics are defined entirely by these sets of rules. It
always either applies a 'wp' rule as an introduction rule, or applies a
'wp_comb' rule first and then a 'wp' rule. If multiple choices are available,
the one with the most recently added 'wp' rule is preferred. Application alone
is preferred to application with a combinator, and combinators are also
selected last-first. There is also a 'wp_split' rule set which are not combined
with combinators and which are applied only if no 'wp' rules can be applied.

Note that rules may be supplied which are not the actual weakest precondition.
This may cause the tool to produce unhelpfully weak conclusions. Perhaps the
tool should actually be named 'p'.  The 'hoare_vcg_prop' rule supplied in
NonDetMonadVCG.thy is unsafe in this manner. It is convenient that
postconditions which ignore the results of the operation can be handled
immediately (especially when used with the combinator rules), however
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

The 'wpc' tool synthesises the needed case split rules for datatype case
statements in the function bodies in the Hoare triples.

A further caveat is that the 'wp' and 'wp_comb' rulesets provided are not
necessarily ideal. Updating these rulesets would create difficult maintenance
problems, and thus they are largely left as first defined. One issue that has
not been addressed is the implicit precondition weakening done by combinator
rules 'hoare_post_comb_imp_conj' and 'hoare_vcg_precond_imp'. In hindsight it
would be better if 'hoare_pre' were always applied manually, or if the 'wp'
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


