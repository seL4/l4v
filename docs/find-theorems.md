<!--
     Copyright 2021, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Using find_theorems effectively

This command is for searching for theorems. If you are looking for a
constant/function instead, look at [find_consts](find-consts.md).

There is an introduction to the `find_theorems` command in the
[Isabelle/HOL tutorial](https://isabelle.in.tum.de/documentation.html).
Here we cover some additional material and useful patterns.

`find_theorems` can be written in the theory as a diagnostic command, or
accessed from the jEdit Query panel. Sometimes it is useful to create a
"New Floating Instance" of the panel to view theorems while you work.

As a reminder, the basic search criteria are:

| syntax | matches |
| ------------------- | ------------
| `"pattern"`       | only theorems that match this pattern
| `name: "string"`    | only theorems whose names contain this string
| `simp: "pattern"` | equations that can rewrite this pattern
| `intro`, `elim`, `dest`, `solves` | theorems that are intro/elim/dest rules for the current proof goal, or solve the goal
| `- <criterion>`   | only theorems that do **not** match the criterion

## Patterns

`find_theorems` attempts to match your pattern(s) in theorems. Usually,
using dummy terms (underscores) is enough. Sometimes it pays to be more
creative.

### Match the conclusion of a theorem

The query

    "if _ then _ else _"

returns many kinds of theorems. If we are only interested in theorems
with this exact conclusion, write

    "_ ⟹ if _ then _ else _"

You can also use the same trick to match assumptions:

    "if _ then _ else _ ⟹ _"

Be aware that these won't match theorems with no assumptions!
Alternatively, write a pattern of type prop, so that it matches only
assumptions and conclusions:

    "Trueprop (if _ then _ else _)"

### Finding theorems for a type

Suppose we want to find nat division rules:

    "_ div _"

That wasn't very effective. Use type annotations to narrow the search:

    "_ div _ :: nat"

Using dummy types to find word division rules:

    "_ div _ :: _ word"

### Don't be too specific

Terms and types can be too specific and prevent useful results from
being returned. In the previous example, generic division rules are not
returned by the queries with type constraints. We can search for generic
rules separately:

    name:ring_div_class "_ div _"

This fetches theorems proved in the locales `ring_div_class` and
`semiring_div_class`.

In the previous example, we deliberately added the type constraint. More
often, the cause is a subterm of the pattern that is too concrete. For
example,

    "my_const + _ = _ + my_const"

is unlikely to return any results. When this happens, try again with a
more general query that replaces `my_const`.

### Using schematics

Schematic variables can appear multiple times --- use this to your
advantage. Suppose we wanted a commutativity rule for `my_const + _`
(previous section):

    "_ + _ = _ + _"

But we get many irrelevant results. Instead, use named schematics:

    "?x + ?y = ?y + ?x"

Note that schematics in multiple patterns are matched independently, even if
they have the same name, so this technique becomes less effective.

### Names

Many theorems are organised into theories and locales. When you have a pattern
that's too general and it's not clear how to refine it, names can be used as
"thematic" search criteria.

Find simp rules for bytes:

    name:"simp" "_ :: 8 word"

Find induction rules in the List theory:

    name:"List." name:induct

Note the "." after "List". Adding or removing dots can have a great
effect on some queries, e.g. find simp rules not defined by the datatype
package:

    name:"simp" -name:".simp" "_ :: 8 word"

One problem with our List query is that not all induction rules are
contained in List. Instead, we can search for a conclusion that is
common to list induction rules:

    name:induct "_ ⟹ _ (_ :: _ list)"

Indeed, we see that other theories also have list induction rules.

The `name` search criterion is often useful with negation. For instance

    name:induct "_ ⟹ _ (_ :: _ list)" -name: "List."

will remove everything from the `List` theory from the previous search.

Finally, a note on the pattern `"_ (_ :: _ list)"` that we used to
match the conclusion. `find_theorems` requires every dummy term or
schematic to match something in the theorem, which is different from how
unification of schematics usually behaves (e.g. in `apply rule`). We
exploit this to match only theorems whose conclusions talk about a list.
