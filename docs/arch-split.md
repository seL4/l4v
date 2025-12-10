<!--
     Copyright 2024, Proofcraft Pty Ltd
     Copyright 2021, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Architecture Split

Initially, the seL4 functional correctness proof existed for only one
architecture and platform. When porting to other architectures, we realised
that copying everything and fixing up the copy is not a good approach, since a
significant proportion of the specifications and proofs are very similar. By
splitting the specs and proofs into *generic* and *arch-specific* parts, a
large amount of work duplication can be avoided. The Haskell spec was already
written in a way that keeps the generic and architecture-specific definitions
and types separated. The first arch-split was conducted during the abstract
invariant (AInvs) proof for 32-bit ARM_HYP.

We use (perhaps abuse) the Isabelle locale mechanism, together with some custom
commands, to place architecture-specific definitions and proofs in namespaces,
to make it harder to unfold architecture-specific definitions by accident. We
also have a collection of hacks to keep existing proofs checking while we
continue to work towards the ultimate goal of proofs on multiple architectures.

So far, the `ASpec` and `AInvs` sessions have been arch-split, with some work
already done on the executable design spec (`ExecSpec`).


## L4V_ARCH

When running a session, the `L4V_ARCH` environment variable is used to specify
the target architecture; this affects which seL4 kernel configuration gets
used, where Isabelle images are stored, as well as the arch-split infrastructure
via parametrised theory imports.

By using `$L4V_ARCH` in the theory imports section, we can include
the appropriate architecture-specific theories for the currently selected
architecture. For example:

- `l4v/spec/abstract/CSpace_A.thy`

```isabelle
theory CSpace_A
imports
  "./$L4V_ARCH/ArchVSpace_A"
  IpcCancel_A
  "./$L4V_ARCH/ArchCSpace_A"
```

For the `ARM` architecture, we make subdirectories named `ARM` for
architecture-specific theories, and set `L4V_ARCH=ARM` in the environment before
starting Isabelle.

Theories often come in pairs of a generic theory and an associated
architecture-specific theory. Since theory base names must be unique, regardless
of their fully qualified names, we adopt the convention that
architecture-specific theory names are prefixed with "Arch". We don't prefix
with `ARM` or `X64`, because generic theories must be able to import
architecture-specific theories without naming a particular architecture.


## The Arch locale

We use a locale named `Arch` as a container for architecture-specific
definitions and lemmas, defined as follows:

- `l4v/spec/machine/Setup_Locale.thy`

```isabelle
theory Setup_Locale
imports "../../lib/Qualify" "../../lib/Requalify" "../../lib/Extend_Locale"
begin
(*
   We use a locale for namespacing architecture-specific definitions.
   The global_naming command changes the underlying naming of the locale. The intention is that
   we liberally put everything into the "ARM" namespace, and then carefully unqualify (put into global namespace)
   or requalify (change qualifier to "Arch" instead of "ARM") in order to refer to entities in
   generic proofs.
*)
locale Arch
end
```

All architecture-specific definitions should be placed in the Arch locale, with
an appropriate `global_naming` scheme (see below).

If you're not familiar with locales, you should read the [locale tutorial]. The
`Arch` locale has no parameters and no assumptions, since we are merely using it
as a namespace, but it still important to understand the various ways of
interpreting this locale, how it interacts with various other locales in the
proofs, as well as our custom name-spacing commands.

The locale is named "Arch" on every architectures, rather than "ARM" or "X64",
because the generic theories need to be able to selectively refer to types,
constants and facts from architecture-specific theories, without naming a
particular architecture. The mechanisms for doing this are described below.

[locale tutorial]: https://isabelle.in.tum.de/doc/locales.pdf


## Workaround for non-split theories

For many sessions, the proofs remain duplicated between architectures.

As a temporary measure, we wrap existing proofs in an anonymous context block,
in which we interpret the Arch locale. For example:

```isabelle
theory Retype_R
imports VSpace_R
begin

context begin interpretation Arch . (*FIXME: arch-split*)

lemma placeNewObject_def2:
 "placeNewObject ptr val gb = createObjects' ptr 1 (injectKO val) gb"
   apply (clarsimp simp:placeNewObject_def placeNewObject'_def
     createObjects'_def shiftL_nat)
  done

(* ... *)
end
end
```

The `FIXME` indicates that this is a temporary workaround, and that
architecture-specific proofs still need to be separated out before this part of
the proof can be adapted to another architecture.

There are issues with some commands that do not work inside anonymous context
blocks, most notably locale declarations, and locale context blocks. In these
cases, we exit the anonymous context block before entering the locale context,
and then interpret the Arch locale inside the locale context block (if
necessary).


## Global naming

The Arch locale must have the same name on every architecture. However, there
are two classes of architecture-specific types, constants and facts, i.e. those
that:
* only exist internal to a specific architecture (e.g. Arm-only machine op)
* exist on all architectures, but have architecture-specific definitions
  (e.g. a constant that gets the value of some register in thread context,
   but *not* its definition)

We want to be able to *refer* to the latter in generic theories, while
acknowledging that they have architecture-specific definitions and proofs. We
want to prevent, however, inadvertent references to types, constants and facts
which are only internal to a particular architecture (e.g. definitions of
constants).

To help achieve this hiding, we provide the custom commands **global_naming**
and **arch_global_naming**, which modify the way qualified names are generated.
The primary use of these commands is in architecture-specific theories, to
ensure that by default, types, constants and lemmas are given an
architecture-specific qualified name, even though they are part of the Arch
locale.

- `l4v/proof/invariant-abstract/ARM/ArchADT_AI.thy`

```isabelle
theory ArchADT_AI
imports "../Invariants_AI" (* ... *)
begin

(* All ARM-specific definitions and lemmas should be placed in the Arch context,
   with the "ARM" global_naming scheme. *)

context Arch begin global_naming ARM
definition "get_pd_of_thread ≡ ..."
end

(* the more convenient and preferred way to achieve the above when L4V_ARCH=ARM
   is to use arch_global_naming, spiritually equivalent to `global_naming $L4V_ARCH` *)
context Arch begin arch_global_naming
(* ... *)
end

(* Back in the global context, we can't refer to these names without naming a particular architecture! *)
term get_pd_of_thread         (* Free variable *)
term Arch.get_pd_of_thread    (* Free variable *)
term ARM.get_pd_of_thread     (* Accessible; qualifier clearly indicates that this is ARM-specific. *)
thm  ARM.get_pd_of_thread_def (* Also accessible. *)

(* ... *)
end
```

In the above example, we are in an `ARM`-specific theory in the abstract
invariants. We enter the `Arch` locale (`context Arch begin ... end`), and
immediately set the `global_naming` scheme for this context block to `ARM`.
Constants and lemmas in this context block are given their usual unqualified
local names in the `Arch` locale, but their global names are qualified as "ARM",
rather than "Arch". This means that outside the `Arch` context, we cannot refer
to these constants and lemmas without explicitly naming a particular
architecture. If we saw such a reference in a generic theory, we would
immediately recognise that something was wrong.

The convention is that in architecture-specific theories, we initially
give *all* types, constants and lemmas the architecture-specific
`arch_global_naming` scheme. Then, in generic theories, we use
*requalification* to selectively extract just those types, constants and
facts which are expected to exist on all architectures.


## Requalify

We provide three custom commands for giving existing names new bindings
in the global namespace: **requalify_types**, **requalify_consts**,
**requalify_facts**, for types, constants and facts respectively. The
new name is based on the context in which the requalification command is
executed. As with `global_naming`, we provide `L4V_ARCH`-aware versions of
these commands: **arch_requalify_types**, **arch_requalify_consts** and
**arch_requalify_types**.

To understand how these commands function, see `lib/test/Requalify_Test.thy`.

We use requalification in various ways, depending on the situation.

The most basic use is to take a name from the Arch context and make it
available in the global context without qualification. This should be
done for any type, constant or fact:

1. which is expected to exist on all architectures, even though it is defined or
   proved differently on different architectures,

2. which is needed in architecture-generic definitions or proofs,

3. whose unqualified name does not clash with some other architecture-generic
   type, constant or fact, so that the unqualified name unambiguously denotes
   the architecture-specific concept for the current architecture.

Note: the `[arch_]requalify_*` commands will warn when the unqualified name is
already available in the global context (see: Dealing with name clashes). To
suppress this warning, pass `(aliasing)` as the first parameter.


### Requalifying in practice

Let's use the generic theory `l4v/proof/invariant-abstract/ADT_AI.thy` as an
example:

```isabelle
theory ADT_AI
imports
  "./$L4V_ARCH/ArchADT_AI"
begin

term empty_context (* Free variable. *)
```

The constant `empty_context` is not visible in the theory scope, as it was
defined inside the Arch locale, likely with `arch_global_naming`, thus visible
as (for example) `ARM.empty_context`. We want to make this constant available
to generic proofs. The obvious way to do this is:

```isabelle
requalify_consts ARM.empty_context (* avoid: can only be done in Arch theories *)
```

Unfortunately, on another platforms such as RISCV64, the constant will have a
different qualified name. We can instead appeal to `L4V_ARCH` again, since we
already rely on it to select the correct theories for the current architecture:

```isabelle
arch_requalify_consts empty_context (* preferred *)

(* The requalified constant is now available unqualified in the global context. *)
term empty_context

(* However, its definition is not. *)
thm empty_context_def (* ERROR *)
```

In some cases, consts/types/facts may be thrown into the `Arch` context without
further qualification. In such cases, normal requalification may be used:

```isabelle
requalify_consts Arch.empty_context (* standard locale version, likely due to missing global_naming *)
```


### Requalifying inside "Arch" theories

While requalifying inside `Arch*` theories is possible, as seen above, it
requires duplicating the requalify command(s) on every architecture, and so
should be avoided. However, it is not always possible to conveniently do so,
particularly when defining constants inside `Arch`, then having to use those
constants to instantiate locales, before heading back into the `Arch` context.


### Requalifying via interpretation (slow)

Using `arch_requalify_*` commands still implicitly appeals to the name of the
architecture while in a generic theory. This has the advantage of being fast and
thus is preferred, but we describe the old interpretation method here for
reference (for dealing with older theories or older repository versions).

We can do this in a generic theory:

- `l4v/proof/invariant-abstract/ADT_AI.thy`

```isabelle
theory ADT_AI
imports
  "./$L4V_ARCH/ArchADT_AI"
begin

term empty_context (* Free variable. *)

context begin interpretation Arch .
term empty_context (* This was previously defined in the Arch locale. *)
requalify_consts empty_context
end

(* The requalified constant is now available unqualified in the global context. *)
term empty_context

(* However, its definition is not. *)
thm empty_context_def (* ERROR *)

(* ... *)
end
```

In the above example, we enter an anonymous context block (`context begin ...
end`). Because this is not a named context, the effect of `requalify_consts` is
to requalify the given names into the global context, such that they become
accessible as unqualified names.

But we must first get hold of an existing name. We cannot use a qualified name,
because the name was presumably defined with `global_naming ARM` or similar, and
we cannot refer to `ARM` in a generic theory (because the generic theory also
has to work for `X64` and `RISCV64` etc). However, we can temporarily interpret
the Arch locale (`interpretation Arch .`) making *everything* in the Arch locale
available unqualified until the end of the context block. Indeed, in this case,
the only purpose of the anonymous context block is to limit the scope of this
`interpretation`.

Note: It is critical to the success of arch-split that we *never* interpret the
Arch locale, *except* inside an appropriate context block.

In a generic theory, we typically only interpret the Arch locale to keep
existing proofs checking until we find time to factor out the
architecture-dependent parts. The `.` in `context begin interpretation Arch .`
in the middle of AInvs takes 7.5s, so repeated use of this technique should be
avoided when possible.



### Requalifying into the Arch locale

The `requalify` commands support a target parameter, e.g.

```isabelle
requalify_facts (in Arch) user_mem_dom_cong
```

Which prevents exporting the name into the global theory context, exporting it
under `Arch.` instead:

```isabelle
thm user_mem_dom_cong      (* ERROR *)
thm ARM.user_mem_dom_cong  (* ok *)
thm Arch.user_mem_dom_cong (* ok *)
```

Generally, we want to avoid unprefixed names in the Arch locale, preferring to
use a `global_naming` to generate a prefix instead. However, when the generic
and arch-specific short names are identical, this functionality allows giving
an architecture-specific constant/type/fact a generic name while not mixing it
with generic namespace (see also "Dealing with name clashes", as this affects
lookup order inside interpretations).

One can target any locale in this fashion, although the usefulness to arch-split
is then decreased, since short names might not be visible past a naming prefix:

```isabelle
requalify_facts (in Some_Locale) ARM.user_mem_dom_cong

thm user_mem_dom_cong             (* ERROR *)
thm ARM.user_mem_dom_cong         (* ok *)
thm Some_Locale.user_mem_dom_cong (* ok *)
```


### Dealing with name clashes

Things are a bit more complicated when a generic theory needs to refer to an
architecture-specific entity when there already exists an architecture-generic
entity with the same unqualified name. That is, points 1 and 2 above hold, but
3 does not. This happens frequently in the Haskell spec, where a generic
definition may refer to the corresponding architecture-specific definition. In
this case, we would like the unqualified name to refer to the generic concept,
and we would like to refer to the architecture-specific concept with an "Arch"
qualifier. To do this, we requalify the name into the Arch context:

- `l4v/spec/design/Retype_H.thy`

```isabelle
theory Retype_H
imports
  RetypeDecls_H
begin

term deriveCap (* Outside the Arch context, this is the arch-generic deriveCap function. *)
thm deriveCap_def (* Similarly, this is the arch-generic deriveCap definition. *)

context Arch begin

(* Here, the global_naming scheme is "Arch" by default. *)

term deriveCap               (* In the Arch context, this is the deriveCap function for arch caps. *)
term RetypeDecls_H.deriveCap (* This is the arch-generic deriveCap function. *)

thm deriveCap_def            (* In the Arch context, this is the deriveCap definition for arch caps. *)
thm Retype_H.deriveCap_def   (* This is the arch-generic deriveCap definition. *)

(* The following makes Arch.deriveCap refer to the architecture-specific constant. *)
requalify_consts deriveCap   (* Warning: Name "deriveCap" already exists in theory context *)
requalify_facts deriveCap_def (* Warning: Name "deriveCap_def" already exists in theory context *)

(* Unfortunately, the above also means that in a context in which Arch is interpreted,
  `deriveCap` unqualified would refer to the arch-specific constant, which may break existing proofs.
   The following incantation ensures that `deriveCap` unqualified refers to the arch-generic constant,
   even when the Arch locale is interpreted. *)

context begin global_naming global
requalify_consts (aliasing) RetypeDecls_H.deriveCap
requalify_facts (aliasing) Retype_H.deriveCap_def
end

end

(* Now, in the global context... *)
term deriveCap        (* arch-generic *)
term global.deriveCap (* arch-generic alternative *)
term Arch.deriveCap   (* arch-specific *)
thm deriveCap_def     (* arch-generic *)

(* Also when we interpret the Arch locale... *)
context begin interpretation Arch .
term deriveCap        (* arch-generic *)
term global.deriveCap (* arch-generic alternative *)
term Arch.deriveCap   (* arch-specific *)
thm deriveCap_def     (* arch-generic *)
end

(* Even when we re-enter the Arch locale... *)
context Arch begin
term deriveCap        (* arch-generic *)
term global.deriveCap (* arch-generic alternative *)
term Arch.deriveCap   (* arch-specific *)
thm deriveCap_def     (* arch-generic *)
end

(* For facts, there is an additional caveat: named_theorems perturbs fact name ordering: *)
context Arch begin
thm deriveCap_def     (* arch-generic, as expected *)
named_theorems Some_assms
thm deriveCap_def     (* arch-specific, until the end of the context block! *)
end

(* ... *)
end
```

In this case, we perform the requalification in the Arch context (`context Arch
begin ... end`). Contrast this with the previous case, where we entered an
anonymous context block, and interpreted the Arch locale.

There is a complication due to the way names from locales are bound into the
current context during interpretation. Without further intervention, an
interpretation of the Arch locale rebinds an unqualified name into the current
context, based on the last binding of that name within the locale. The result is
that the unqualified name now refers to same thing as the Arch-qualified name.
This is generally *not* what we want.

To fix this, we add a second requalification of the arch-generic constant
(obtained by a full theory-qualified reference). Since this is the last binding
of that name in the locale, it is used for rebinding the unqualified name during
interpretation. To avoid *also* overriding the binding of the Arch-qualified
name, we use a `global_naming` scheme *other than Arch* for this second
requalification, choosing `global` as our convention. A side effect is that the
arch-generic thing can be found with *either* an unqualified name or a
`global`-qualified name, whereas the arch-specific thing can only be found with
an `Arch`-qualified name.

As shown above, for facts, `named_theorems` causes a reordering of fact names,
meaning that the default name becomes arch-specific in an `Arch` locale or
interpretation. For this reason, when dealing with fact names which have been
disambiguated with a `global./Arch.` prefix, we strongly suggest qualifying
both fact names when unfolding them inside of an Arch locale or interpretation:

```isabelle
context Arch begin
(* ... *)
  apply (simp add: global.deriveCap_def Arch.deriveCap_def)
(* ... *)
end
```

Note: In a generic theory, we typically *only* enter the Arch context
to requalify names with the "Arch" qualifier.


### Name clashes between abstract and Haskell specs (i.e. `ARM_A` vs `ARM_H`)

In addition to name clashes between architecture-generic and
architecture-specific concepts, there are also many names in common between the
abstract and Haskell specs. Previously, these were disambiguated in the
refinement proofs by fully qualified references including theory names. For
architecture-specific things, the introduction of the Arch locale
(with `global_naming`) changed the required fully-qualified names, so many
proofs were broken. For example, `ArchRetype_H.updateCapData_def` became
`ArchRetype_H.ARM.updateCapData_def`.

Fixing this required search-and-replace, but rather than entrench the fragility
of theory-qualified references, we introduced different `global_naming` schemes
for abstract and Haskell specs: `ARM_A` for abstract specs, and `ARM_H` for
Haskell specs. We use `ARM` everywhere else. This means that the arch-specific
references only require either an `ARM_A` or `ARM_H` qualifier. No theory
qualifier is required, and the result is more robust to theory reorganisation.

Requalification of consts/types/facts from these prefixes should be done as
follows:

```isabelle
arch_requalify_const some_const (* requalifies ARM.some_const *)
arch_requalify_const (A) some_const (* requalifies ARM_A.some_const *)
arch_requalify_const (H) some_const (* requalifies ARM_H.some_const *)
```

In the future, when we are properly splitting the refinement proofs, we may
want to extend this approach by introducing `Arch_A` and `Arch_H`
`global_naming` schemes to disambiguate overloaded requalified names.


### Name clashes with the C spec

There were also some clashes between Haskell and C specs. For names generated in
`Kernel_C.thy`, we simply added a `Kernel_C.` qualifier. For names generated in
Substitute.thy, we used hand-crafted abbreviations, for example:

- `l4v/proof/crefine/Ipc_C.thy`

```isabelle
abbreviation "syscallMessageC ≡ kernel_all_substitute.syscallMessage"
lemmas syscallMessageC_def = kernel_all_substitute.syscallMessage_def
```

## Managing intra-theory dependencies


### Three-theory split (deprecated)

Note: this is no longer the expected convention except for older files. See
`Theory-specific architecture-generic locales` for new convention.

Initial work on splitting invariant definitions and proofs found that
within many theory files, there were both:

- architecture-specific definitions and proofs that depended on
  architecture-generic definitions and proofs, and

- vice-versa.

Since we use theory imports to separate architecture-specific concepts
from generic concepts, we found it was often necessary to split an
existing theory `Foo_AI` into *three* theories:

- `FooPre_AI` makes generic definitions that are needed for
  architecture-specific definitions.

- `$L4V_ARCH/ArchFoo_AI` imports `FooPre_AI`, and makes
  architecture-specific definitions and proofs in the `Arch` locale.

- `Foo_AI` imports `ArchFoo_AI`, and makes generic definitions and proofs
  that refer to architecture-specific constants and facts.

In some cases, `FooPre_AI` was not necessary, and it was sufficient to
have `Foo_AI` import `ArchFoo_AI`.

We see no reason to redo that previous work, so the above still
describes the current state of the abstract spec and some of the
invariants.


### Theory-specific architecture-generic locales

For further updates, however, we have developed a new pattern which we
hope will eliminate the need for more "Pre" theories, and only require
the addition of Arch theories for each existing theory.

In this pattern, an existing theory `Foo_AI` is split into two theories:

- `Foo_AI` retains the architecture-generic parts, using locales `Foo_AI*`
   where necessary to *assume* the existence of the appropriate
   architecture-specific parts.
   Note: if only one locale is needed, it is named `Foo_AI` by convention,
   otherwise naming proceeds: `Foo_AI_1`, `Foo_AI_2`, etc.

- `$L4V_ARCH/ArchFoo_AI` imports `Foo_AI`, makes architecture-specific
  definitions and proofs in the `Arch` locale, and then interprets the
  `Foo_AI*` locales globally.

After the `Foo_AI*` locales are interpreted, we never speak of them again.

Here is an example with a single locale:

- `l4v/proof/invariant-abstract/Retype_AI.thy`

```isabelle
theory Retype_AI
imports VSpace_AI
begin

(* Declare a theory-specific locale, which we use to assume the existence
   of architecture-specific details.

   We have access to the clearMemoryVM constant, since
   it was previously requalified into the global context,
   but its definition is architecture-specific.
   Here, we assume a property that we need to continue
   making architecture-generic statements.
   Previously, this was a lemma that unfolded
   architecture-specific details. *)

locale Retype_AI =
  assumes clearMemoryVM_return[simp]:
    "clearMemoryVM a b = return ()"

(* ... *)

(* This lemma makes use of the assumption of the Retype_AI locale,
   so we prove it in the Retype_AI context. *)

lemma (in Retype_AI) swp_clearMemoryVM [simp]:
  "swp clearMemoryVM x = (λ_. return ())"
  by (rule ext, simp)

(* ... *)

context Retype_AI

(* we can do proofs using the assumptions of Retype_AI here, as an alternative
   to multiple (in Retype_AI) lemmas *)

end

(* ... *)

end
```

- `l4v/proof/invariant-abstract/ARM/ArchRetype_AI.thy`

```isabelle
theory ArchRetype_AI
imports "../Retype_AI"
begin

context Arch begin global_naming ARM

(* We declare a collection of lemmas, initially empty,
   to which we'll add lemmas which will be needed to discharge
   the assumptions of the Retype_AI locale. *)

named_theorems Retype_AI_assms

(* We prove a lemma which matches an assumption of the Retype_AI locale,
   making use of an arch-specific definition.
   We declare the lemma as a memory of the Retype_AI_assms collection. *)

lemma clearMemoryVM_return[simp, Retype_AI_assms]:
  "clearMemoryVM a b = return ()"
  by (simp add: clearMemoryVM_def)

end

(* Having proved the Retype_AI locale assumptions, we can make a global
   interpretation of that locale, which has the effect of making all
   the lemmas proved from those assumptions available in the global context.
   The proof incantation is designed to give useful error messages if
   some locale assumptions have not been satisfied. For each theory,
   the same proof should be used, substituting only the names of the
   locale and the named_theorems collection. *)

global_interpretation Retype_AI?: Retype_AI
proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; fact Retype_AI_assms)?)
qed

(* ... *)

end
```

Note: `global_interpretation Retype_AI?` exports all names into the global
context, but they are also accessible with a `Retype_AI.` prefix, which is
useful to know in case of name collision.


### Need for multiple theory-specific architecture-generic locales

In the previous section, we mentioned "locales" (plural), with the ideal case
being a single locale. The reason we need this is due to chains of lemmas that
look like this:
* using AA (arch-specific) prove GB (generic)
* using GB (generic) prove AC (arch-specific)
* using AC (arch-specific) prove GD (generic)

If we wanted to split this theory as in the single-locale example, we would end
up with multiple theories, divided only by the arbitrariness of the dependency
graph. Instead, we can employ multiple locales as follows.

In the generic theory (e.g. `Foo_AI`) we do:

```isabelle
locale Foo_AI_1 =
  assumes AA: (* ... *) "XXX"

lemma (in Foo_AI_1) GB: "XXX"
  by (* using AA *)

locale Foo_AI2 = Foo_AI_1 +
  assumes AC: (* ... *) "XXX"

lemma (in Foo_AI_2) GD: "XXX"
  by (* using AC *)
```

This allows instantiation of the locales in stages in the arch-specific theory
(e.g. `ArchFoo_AI`):

```isabelle

context Arch begin global_naming ARM

lemma AA[Foo_AI_assms]: "XXX"
  by (* ... *)

end

interpretation Foo_AI_1?: Foo_AI_1
proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; fact Foo_AI_assms)?)
qed

(* now we get access to GB in the global context *)

context Arch begin global_naming ARM

lemma AC[Foo_AI_assms]: "XXX"
  by (* using GB *)

end

interpretation Foo_AI_2?: Foo_AI_2
proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; fact Foo_AI_assms)?)
qed

(* now we get access to GD in the global context *)
```

While strictly speaking, there is no requirement that `Foo_AI_2` includes
`Foo_AI_1`, in practice we always do so, since we want everything that got
proved to be instantly available in case it's needed in the proof chain. This
generates limited duplication: a fact from `Foo_AI_1` will be duplicated in
`Foo_AI_2`, but not in `Foo_AI_3+`.


### Temporarily proving a fact in the Arch locale

The concept of "generic consequences of architecture-specific properties" shows
up in a few places. Normally, as outlined above, we prefer either exporting
enough facts to prove the property in the generic context or requiring the
property as a locale assumption. However, sometimes we end up in a situation
where the same proof will work on all architectures and spelling it out with
locale assumptions is inconvenient. For example (from `Invariants_AI`):

```isabelle
(* generic consequence of architecture-specific details *)
lemma (in Arch) valid_arch_cap_pspaceI:
  "⟦ valid_arch_cap acap s; kheap s = kheap s' ⟧ ⟹ valid_arch_cap acap s'"
  unfolding valid_arch_cap_def
  by (auto intro: obj_at_pspaceI split: arch_cap.split)

requalify_facts Arch.valid_arch_cap_pspaceI
```

In this case, no matter what the architecture, the `valid_arch_cap` function
will only ever look at the heap, so this proof will always work.

There are some considerations when using this strategy:

1. We use the Arch locale without `global_naming`, as its performance is better
   than entering the Arch locale and proving the lemma there. This means its
   qualified name will be `Arch.valid_arch_cap_pspaceI`, but this is acceptable
   since:
2. The lemma is immediately requalified into the generic context, so we never
   really want to use its qualified name again.
3. This technique is rarely used, *use sparingly*!


## Qualifying non-locale-compatible commands

Generally speaking, architecture-specific definitions and lemmas should
be put inside the `Arch` locale, with an appropriate `global_naming` scheme.

However, there are some commands that don't work in locales, for
example records. To work around this, we have a pair of custom commands:
`qualify` and `end_qualify`. Surrounding definitions with these commands has
the effect of adding the qualifier to the names of those definitions.

```isabelle
context ARM begin

typedecl my_type

end

qualify ARM

record foo = baz :: ARM.my_type -- "Qualifier still needed"

end_qualify

typ foo -- Error
term baz_update -- Free
thm foo.cases -- Error

typ ARM.foo
thm ARM.foo.cases
term ARM.baz_update

context ARM begin

typ foo
term baz_update
thm foo.cases

end
```

Some caveats:

- This only affects names. It does not do the usual context-hiding for simp (and
    other) declarations. There may be some post-hoc cleanup needed for removing
    these from the global theory in order to avoid inadvertently breaking
    abstraction.

- Interpreting the `Arch` locale won't bring unqualified versions of these names
    into the local scope.

In short: use sparingly and avoid when possible.


## HOWTO

For splitting new parts of the proof, this is roughly the workflow we follow:

Initially, we just want to populate Arch-specific theories with:

- types and constants whose definitions are clearly architecture-specific, for
  example if they refer to details of the page table structure;

- lemmas which we do not expect to be present on all architectures, in
  particular, those whose statements refer to architecture-specific constants;

- lemmas which are likely to exist on all architectures, but whose proofs
  probably can't be abstracted away from architecture-specific details.

Later, we can more work on actually creating abstractions that will
allow us to share more proofs across architectures, but for now this
means that we'll leave behind FIXMEs in generic theories for lemmas we
suspect can be abstracted, but currently have proofs that unfold
architecture-specific details.

The workflow:

- Pick a theory to work on. Co-ordinate with others if there are multiple people
  working on the split.

- Assuming you're starting for ARM, which has the most proofs: If there is no
  ARM-specific theory corresponding to this theory, create it in the ARM
  subdirectory, prefixing the name of the theory with "Arch".

  - The Arch theory should import the generic theory, and any theories which
    previously imported the generic theory should now import this Arch theory.

  - Fill out the template of the Arch theory, as per the section "Managing
    intra-theory dependencies" above.

- Look in the generic theory for a block of the form
  `context Arch begin (* FIXME: arch-split *) ... end`.

  - These indicate things that we've previously classified as belonging in an
    arch-specific theory.

  - Move the contents of that block to the Arch theory, within a
    block of the form `context Arch begin global_naming ARM ...
    end`.

- Look for subsequent breakage in the generic theory.

  - If this is in a subsequent Arch block (`context Arch begin (* FIXME:
    arch-split *) ... end`), just move that block.

  - Otherwise, if it's not obvious what to do, have a conversation with someone.
    We'll add more tips here as the process becomes clearer.


## Handling existing locales

Existing locales may need to be split up into architecture-generic and
architecture-specific variants. We can do this by making a second locale
which extends both the original locale and the Arch locale.

```isabelle
(* Before *)
locale my_locale = fixes x
begin
lemma non_arch_lemma: "Generic_statement"
lemma arch_lemma: "ARM_specific_statement"
end
(* After *)
locale my_locale = fixes x
locale Arch_my_locale = my_locale + Arch
```

To interpret these locales, we can just do a regular `interpretation`
for the arch-independent one. The arch-specific one, however, needs to
be interpreted **inside** the `Arch` locale. Contrary to intuition, this
is done using the `sublocale` command, not `interpretation`. This is
because the results of an `interpretation` are thrown away when the
locale context is exited.

```isabelle
theory Arch_Theory
context Arch_my_locale begin
lemma arch_lemma: "ARM_specific_statement"
end
end

theory Generic_Theory
context my_locale begin
lemma non_arch_lemma: "Generic_statement"
end
end
```

Often we want to lift some results out of our arch-specific locale into our
generic one (like an `unqualify`). This can be done using `interpretation`. Note
that because the effect of interpretation is temporary, we won't accidentally
pollute the global namespace with all of our architecture-specific content.

```isabelle
context Arch_my_locale begin

lemma quasi_arch_lemma[iff]: ....

end

context my_locale begin

interpretation Arch_my_locale by unfold_locales -- "Always by unfold_locales because they share the same base locale"

lemmas quasi_arch_lemma[iff] = quasi_arch_lemma -- "Similar to unqualify_facts, but keeps the result local to my_locale. Note that the attribute must be re-declared here (but will erroneously give a warning)"

end

interpretation my_locale "some_function" by unfold_locales ...

thm quasi_arch_lemma -- "Exported result"

thm arch_lemma -- "Error, still private"
```


## Breaking abstraction

It is important to note that this the namespacing convention is very much a
"soft" abstraction. At any point a proof author is free to open (or interpret)
the `Arch` locale and start writing architecture-specific proofs. This
intentionally allows proof authors to focus on one architecture at a time, and
not always have to think about the general case. However the expectation is that
this is eventually cleaned up so that the proofs for **all** architectures will
check.

To break into an arch-specific proof in the middle of a lemma, you can use the
following method:

```isabelle
subgoal proof - interpret Arch .

shows ?thesis \<Arch proof here\>

qed
```

This allows a proof author to write an arch-specific proof inside a generic
lemma. Note that the proof should check with all architectures otherwise this
doesn't really work.
