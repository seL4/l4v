<!--
     Copyright 2021, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

# De-duplicating proofs

## Why should I avoid duplication?

Duplication is a natural part of the development process, for both
proofs and code. It's never obvious which parts of a specification or
proof will need to be generalised until you have started working on them
seriously. It is important, however, to notice when you should take your
hand off of "Ctrl-C" and "Ctrl-V" and think about what language
features you can use to reduce duplication. This is important for a
number of reasons:

- **Your proofs usually check faster**

  This is not always the case, but our proofs already take a very long time to
  check. Very often by avoiding duplicating lemma statements or doing redundant
  reasoning you are going to speed everything up and make everyone much happier.

- **You save on initial development time**

  Copy-pasting proof text may be a quick fix to get a particular lemma
  proven faster, but you are nearly always hurting yourself in the long
  run. Proving is never a straight-line process, your definitions always
  change and your lemmas always need to be rephrased. It might be time
  to do some de-duplication when you find yourself doing the long trudge
  through all your theories again, making minor adjustments to your 17
  suspiciously similar helper lemmas.

- **You save on proof maintenance time**

  Our proofs do not live in a vacuum: both the kernel code and Isabelle
  itself are constantly changing. Every time a change occurs the proofs
  break in various strange and exciting ways. If your particular
  copy-pasted proof block is the one that breaks during an update, you
  are potentially doubling the effort required to fix it. If the
  maintainer doesn't notice the duplication, he will likely see both
  proofs in isolation and spend the same amount of time on each to fix
  them.

To seasoned software developers this list may seem a bit obvious.
Indeed, designing modular and re-usable code is a requirement for
creating any large piece of software. So why do we see it so much in
formal proofs? One can argue that the development tools are simply not
there yet. As a result of this, refactoring proofs is a painstaking
process, where even moving one lemma can take hours due to needing to
re-check the entire proof. However, there is less of a pressing need to
refactor, because we don't need to convince ourselves or anyone else
that the proof is correct. Once Isabelle gives it the green light, we
technically don't care about the gruesome details of its inner
workings. As a result of this, proof authors often have an attitude of
"just get it done, we'll fix it later". However, once the proof is
finished, we find ourselves unmotivated to fix it because we **know**
it's correct.

There are obviously limits to how much duplication can be reasonably
avoided. Taken to the extreme, too much de-duplication can result in
proofs which devolve into abstract nonsense. This document aims to
provide a brief introduction to Isabelle features and tools that can be
used to avoid proof duplication.

> The first time you do something you just do it. The second time you do
> something similar, you wince at the duplication, but you do the
> duplicate thing anyway. The third time you do something similar, you
> refactor.
>
> *-Martin Fowler, Refactoring: Improving the Design of Existing Code*

## Techniques for avoiding duplication

### Rule attributes

Rule attributes are used to transform facts in-place. The syntax
is `fact[attribute1 args,attribute2 args]`, where `args` may itself
contain facts with applied attributes. The comma chains the attributes
together, applying one after the other. Any Isabelle tool which takes a
fact as a parameter can also take a more general *fact expression* (a
fact with applied attributes). Here is a list of commonly used rule
attributes:

|  **Attribute**      |  **Description**    |  **Examples**        |
| ------------------- | ------------------- | -------------------- |
| `fact[OF A1 ... An]` | Resolves facts A1 through An with the first n assumptions of fact | `conjI[OF TrueI] :: ?Q ⟹ True ∧ ?Q` <br/> `conjI[OF _ TrueI] :: ?P ⟹ ?P ∧ True`
| `fact[THEN A]`     |  Resolves fact with the first assumption of `A` | `TrueI[THEN conjI] :: ?Q ⟹ True ∧ ?Q`|
| `fact[of x1 ...  xn]`  | Specialises the first n schematics of fact with the given terms. | `conjI[of False] :: ⟦False; ?Q⟧ ⟹ False ∧ ?Q` <br /> `conjI[of _ False] :: ⟦?P; False⟧ ⟹ ?P ∧ False`
| `fact[where A=x and B=y for z]` | Specialises the schematics `A` and `B` in fact to `x` and `y`  respectively, abstracting over `z`| `conjI[where P=False] :: ⟦False; ?Q⟧ ⟹ False ∧ ?Q` <br /> `conjI[where P="R ⟶ E" for R E] :: ⟦?R1 ⟶ ?E1; ?Q⟧ ⟹ (?R1 ⟶ ?E1) ∧ ?Q`
| `fact[simplified As]`   | Simplifies fact with the simplifier, using the given facts `As`. If no facts are given, the default simpset is used. Otherwise **only** `As` is used for simplification   | `‹[a,b] = [c,d]›[simplified] :: a = c ∧ b = d` <br /> `‹[a,b] = [c,d]›[simplified ‹a = c›] :: [c, b] = [c, d]`

The most common use of rule attributes is to do ad-hoc specialisation
during proofs (i.e. `allE[where x=y]`). However they can also be used to
transform lemmas to avoid needing to re-phrase them.

### Simple Example: Decomposing conjuncts

Assume we prove some general hoare triple showing multiple postconditions.

```isabelle
lemma f_AB: "⦃P⦄ f ⦃λ_. A and B⦄"
...
done
```

Suppose we want to turn this into two hoare triples, showing each postcondition
separately. We could write this explicitly as two separate lemmas.

```isabelle
lemma f_A: "⦃P⦄ f ⦃λ_. A⦄"
  apply (rule hoare_strengthen_post)
   apply (rule f_AB)
  by auto

lemma f_B: "⦃P⦄ f ⦃λ_. B⦄"
  apply (rule hoare_strengthen_post)
   apply (rule f_AB)
  by auto
```

Or we could simply transform the original lemma using rule attributes.

```isabelle
thm hoare_conjD1 -- "⦃?P⦄ ?f ⦃λrv. ?Q rv and ?R rv⦄ ⟹ ⦃?P⦄ ?f ⦃?Q⦄"
thm hoare_conjD2 -- "⦃?P⦄ ?f ⦃λrv. ?Q rv and ?R rv⦄ ⟹ ⦃?P⦄ ?f ⦃?R⦄"

lemmas f_A = f_AB[THEN hoare_conjD1] -- "⦃P⦄ f ⦃λ_. A⦄"
lemmas f_B = f_AB[THEN hoare_conjD2] -- "⦃P⦄ f ⦃λ_. B⦄"
```

The advantage of this form is that it does not depend on the phrasing of
the initial lemma. If the precondition `P` is strengthened to `P` and `P'`,
then this change will be propagated automatically to `f_A` and `f_B` without
having to rephrase them both.

### Advanced usage - the simplified attribute

By combining the primitive attributes with `simplified`, we have the
ability to write much more general lemmas and convert them into
specialised forms. A common use-case is to replace parameters with some
identity, so that the simplifier can remove them entirely.

```isabelle
lemma f_invs_and_ct:
  "⦃λs. invs s ∧ Q (cur_thread s)⦄ f ⦃λr s. invs s ∧ Q (cur_thread s)⦄"
  ...

lemmas invs_True = f_invs_and_ct[where Q="λ_. True"] -- "⦃λs. invs s ∧ True⦄ f ⦃λr s. invs s ∧ True⦄"

lemmas invs = invs_True[simplified] -- "⦃invs⦄ f ⦃λr. invs⦄"
```

In this example, the default simplification rule transforms `A ∧ True`
into `A` in both the precondition and postcondition. The resulting rule
can now be applied by `wp`.

Of course there are limits to this approach. Once a fact expression
begins to look like:

```isabelle
lemmas ultimate_fact = my_fact[OF my_other_fact[where x="Baz y" for y], simplified,
                               OF _ _ _ _ my_final_fact[of "¬final_form",simplified],
                               simplified]
```

It might be time to just write another lemma.

## Rules for avoiding duplicate subgoals

There are a number of reasons why precisely the same subgoal might arise
in a given proof. Before copy-pasting the proof script you used to solve
it the first time, or even writing a lemma to solve it in general, it
might be worth investigating **why** you are seeing the same subgoal
multiple times.

### Redundant Conjuncts

Often automated proof methods produce several copies of the same
conjunct. Instead of introducing these naively (with `intro`, `safe` or
`auto`), try invoking `simp cong: conj_cong` to remove redundant conjuncts.

```isabelle
lemma
  assumes AB: "A ∧ B"
  shows "A ∧ B ∧ A"
  apply (simp cong: conj_cong) -- "reduces the goal to "A ∧ B""
  by (rule AB)
```

### Over-generalised rules

A general rule can often have several assumptions that all resolve to
the same thing when applied in a particular situation. Consider writing
a specialised version of the lemma, or transforming it with *rule
attributes*, to avoid producing duplicate subgoals.

```isabelle
lemma my_bipredI: "X ⟹ Y ⟹ my_bipred X Y" by (simp add: my_bipred_def)

lemma
  assumes X: X
  shows "my_bipred X X"
  apply (rule my_bipredI)
   apply (rule X)
  apply (rule X) -- "redundant"
  done

lemma my_bipred_sameI: "X ⟹ my_bipred X X" by (rule my_bipredI) -- "specialised"

lemma
  assumes X: X
  shows "my_bipred X X"
  apply (rule my_bipred_sameI)
  apply (rule X)
  done
```

### Dependent Conjuncts

Given the subgoal `A ∧ B` the standard introduction rule will require
proving `A` then `B`. If the proof of `B` depends on `A`, however, you will
redundantly need to re-prove it. The alternate introduction
rule `context_conjI` allows you to assume `A` while proving `B`.

```isabelle
lemma
  assumes A: "X ⟹ A"
  assumes B: "A ⟹ B"
  shows "X ⟹ A ∧ B"
  apply (rule context_conjI)
   apply (erule A)
  apply (erule B) -- "A is assumed"
  done
```

## Lifting Rules and Locales

In our Hoare logic proofs we have a lot of invariants which only discuss
an isolated part of the state, and functions which similarly only modify
a small part of the state. Usually *crunch* can trivially show that a
given invariant is preserved by a function if they depend on different
fields of the *state* record. Often, however, both depend on the `kheap`
(kernel heap) and thus their independence is not as obvious. If you have
a function that only involves TCBs and a collection of invariants that
only discuss page tables, it might be worth writing a *lifting lemma* to
prove an abstract property that would show that your given invariants
are preserved by your function.

## Tips for using locales

For tips on using locales in conjunction with the Arch locale, see
the [Architecture Split][] page.

[Architecture Split]: arch-split.md

### Type variables

It is possible to quantify over types used in a locale definition, but
only at the top level of the locale. That is, any type variable that
arises in the locale definition (i.e. *fixes* and *assumes* parts)
is *arbitrary but fixed* in the locale context. In particular, it is not
possible to have a type variable in a locale assumption, and then use
that assumption in the locale context with a particular instantiation
for the type variable. This means that lemmas in the locale context must
be provable for the *arbitrary but fixed* type. If you have something
that is only provable for a particular instantiation of the type
variable, make a derived locale as in the example below.

Whenever you have a type variable in a locale, make it explicit, to
ensure it has a predictable name. A *fixes* clause is typically the
clearest place to do this. Use a descriptive name, to make it easier to
search for, and to distinguish it from automatically generated type
variable names like `'a` and `'b`.

It may or may not be useful to fix the type variable using
the `itself` type constructor, as in the example below. The main
requirement is that you mention the type variable explicitly somewhere
in a `fixes` clause.

```isabelle
(* Always mention the type variable explicitly in a fixes clause.
   Here we reify the type variable using "itself". *)

locale foo =
  fixes my_type_var_reified :: "'my_type_var itself"

(* If you want to use a locale assumption at a particular instantiation,
   you'll need to do that in a derived locale which explicitly performs
   that instantiation.
   Here we instantiate "'my_type_var" with "'my_list_elt list".
   There are two parts to this:
   - First instantiate the parameter of the base locale in the locale
     expression, using some new variable name.
   - Then abstract over that same variable name, in a "for" clause,
     explicitly giving the instantiated type. This type can contain
     new type variables. *)

locale foo_derived = foo my_type_var_instantiated
  for my_type_var_instantiated :: "'my_list_element list itself"
```
