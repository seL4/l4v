<!--
     Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Naming Conventions

This file collects naming conventions for the specifications and proofs in this
repository.

Not all of these are followed consistently yet, but over time everything in the
repository should converge towards these. All new material should follow the
conventions below. If you touch old material that is not compliant, you are
encouraged to bring it into compliance.

This file is not comprehensive and currently mostly focuses on the seL4
invariant and refinement proofs. Feel encouraged to raise pull requests to add
conventions as observed in other parts of the proofs or generally to update or
correct material in here!


## General

* in general, the [Isabelle naming conventions][1] apply
* names should be descriptive of the content. Do not use `foo_5`.
* small definitions and lemmas can have short mathematical (single or
  two-letter) parameter or variable names, such as `x` and `y`, but if either
  the definition becomes longer, the number of parameters larger, or consistency
  with other definitions requires it, parameter names should have longer names
  that indicate their purpose.
* for short names the following conventions apply:
  * generic (type `'a`) variables are `x`, `y`, `z`, etc. Example: `x <= x`.
  * natural numbers are `n`, `m`, `i`, etc. Example: `n < Suc n`
  * names for functions are `f`, `g`, `h`, etc.
  * names for lists end in `s`, e.g. `xs`, `ys`. The `s` stands for "sequence" and
    expresses plural. Example: `map f (xs @ ys) = map f xs @ map f ys`
  * names for sets are generally `A`, `S`, i.e. single letter and upper case, unless
    a longer name makes more sense.
  * prefer `x'` over `x2` if you need a name multiple times (`x2` under some
    circumstances will be transformed into `?x2.0` which is harder to work with),
    but don't overuse `'`, i.e. `x'''` is not a good name.

[1]: https://web.archive.org/web/20220810201813/https://isabelle.systems/conventions/naming.html


## Directories

* directories are lower-case-hyphenated
* directory names should correspond at least loosely to session names where
  appropriate
* directories that contain sessions with architecture-generic and -specific
  parts have subdirectories `ARM`, `X64`, `RISCV64`, etc
* `spec` and `proof` refer to specs and proofs about the seL4 kernel
  specifically. New material about seL4 itself should go here.
* `lib` and `tools` are for more general material.
* `sys-init` and `camkes` are user-level proofs about programs on top of seL4.


## Theories

* theory names are in Snake_Case and start with a capital letter. There are
  still many older CamelCase names around. They should disappear over time.

* **postfix:** theory names in `l4v` usually carry a short postfix that indicate
  to which session they belong. This is necessary because the session name in
  current Isabelle is not part of the theory name, and Isabelle will reject
  `Session_A.T` and `Session_B.T` as duplicate theory `T`.

  Examples of postfixes:

  * `T_A` for theories in the abstract specification
  * `T_H` for theories in the design (Haskell) specification
  * `T_AI` for theories in abstract invariants
  * `T_R` for theories in the Refine session
  * `T_C` for theories in the CRefine session

* **prefix**: architecture dependent theories are prefixed with `Arch`.
  **Example:** `ArchDetype_AI` in `proof/invariant-abstract/ARM`


## Constants

* constant names in the abstract spec follow usual Isabelle conventions and are
  `underscore_case` unless they are datatype constructors, which are
  `CamelCase`

* constant names in Haskell and the design specification use Haskell conventions
  (violate Isabelle conventions) and are `CamelCase`.

* property names in abstract invariants are `underscore_case`. Example: `invs`
  and `valid_objs`.

* property names in design spec invariants are also `underscore_case`, but are
  marked with `'` when they could conflict with abstract invariant names.
  Example `invs'` and `valid_objs'`.


## Theorems

### Hoare triples

#### General Hoare triple conventions

* `function_wp` indicates a weakest precondition triple about `function` with a
  generic postcondition and the real weakest precondition that ensures the
  postcondition. Usually safe to declare `[wp]`.

* `function_inv` indicates invariance, e.g. along the lines of
  `⦃P⦄ function ⦃λ_. P⦄`. Usually **not** safe for `[wp]`. Do not confuse with
  `function_invs`, which is an instance of the pattern below for the property
  `invs`.

* `function_prop` indicates a triple with a reasonably weak precondition for a
  postcondition `prop`. Doesn't have to be the weakest, just the weak enough to
  be useful. Often safe for `[wp]`, use discretion.
  Example:
  `⦃valid_objs and valid_ep ep⦄ set_endpoint p ep ⦃λ_. valid_objs⦄`

* `prop_lift` indicates a lifting lemma for proving a property about (usually)
  an arbitrary `f` by showing simpler properties about `f`.

* states are called `s` and `t` within Hoare triples.

* states names `s'` and `t'` should be avoided within Hoare triples. They would
  stand for result states of an operation outside Hoare triples or "concrete"
  states in a correspondence proof.

* return values are called `rv` by default, but can have a more indicative name
  if useful. Avoid other generic names such as `a` or `x`.

* return values that are ignored should use the dummy pattern `_`.
  Example: `⦃P⦄ function ⦃λ_. P⦄`.

* function variables are called `f`, `g`, or `m` (for "monad")

* property variables are called `P`, `Q`, `R`, `P'`, `Q'`. This means, in Hoare
  triples, `P` tends to be a precondition, `Q` a postcondition. If there is only
  one property variable, it should be called `P` so it is easy to guess the name
  for instantiations. Example: `return_wp: ⦃P v⦄ return v ⦃P⦄` (even though P is
  a postcondition here).


#### Specific property names

Some common property and function names are abbreviated in `invariant-abstract`
and similar large sessions. Abbreviations are faster to type, but can get
confusing. If in doubt, write out the name of the property instead of
introducing a new abbreviation. It's easier to find.

Some examples are:

* `typ_at` for `λs. P (typ_at T s)`


#### Function name abbreviations

* `sts` for `set_thread_state`
* `sts'` for `setThreadState`
* there are many more, please raise pull requests to make this a more comprehensive list


### Corres rules

Corres rules (from "correspondence") are used in refinement proofs to show
correspondence between an abstract and a concrete function or operator.

There are two refinement/correspondence frameworks in `l4v`, one for proofs
between monadic functions, and one for proofs between monadic functions and C
(or Simpl functions, to be precise). The former are called `corres`, the latter
`ccorres`. Both frameworks have `corres_underlying` / `ccorres_underlying`
definition that is instantiated to a `corres` / `ccorres` predicate by
abbreviation.

* General lemmas about `corres_underlying` that are directly used in program
  proofs are called `_corres` despite their more general nature. Exceptions are
  lemmas that are only used to build up the library internally, but are not used
  for program proofs.

* `corres_op` is for "built-in" operators and functions of the state monad such
  as `return`, `get`, `bind`, `when`, etc. Examples are `corres_get`,
  `corres_return`.

* `function_corres` is for correspondence proofs between an abstract and a
  concrete function. Often these functions have the same name, the abstract in
  `underscore_style` the concrete in `CamelCase`. The lemma should use the
  concrete name for function (this is currently too random and should converge
  more).

* same as for Hoare triples, the function name can be abbreviated (see above).

