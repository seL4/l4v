<!--
     Copyright 2024, Proofcraft Pty Ltd

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

# VCG debugging techniques for CRefine

## Unprovable goals and `False` in the post condition

When using `vcg`, situations arise where schematic instantiation to `False` can
happen due to unification failure -- mostly during simplification. This is
usually hard to find because `False` itself does not necessarily show up, for
example you may get something like this:

```isabelle
   ∀cte cap.
      ccap_relation (cteCap cte) cap ⟶
      cap_get_tag cap ≠ signed cap_vspace_cap ∧ ...
```

Which is obviously not provable, because we don't have any information about
`cap` to work with. What it should have generated is something like:

```isabelle
   ∀cte cap.
       ccap_relation (cteCap cte) cap ⟶
       (∀t. cap_get_tag cap = signed cap_vspace_cap ⟶ ...)
```

This means that some conjunct in the `...` above got resolved to `False`, which
got simplified to the unsolvable goal.

The way to track down these issues is to go over the `vcg` steps to see which
ones introduced the unexpected result. However, with large goals this is very
difficult to work with. What else can help?

First, try removing `(P ⟶ False) = (¬ P)` from the simpset, so we can look for
`False` in the goals:

```isabelle
  supply simp_thms(19)[simp del]
```

Second, if you do have identified a suspicious `vcg` invocation that could
result in a bad instantiation, try the following instead of only `vcg`:

```isabelle
  apply (rule conseqPre, vcg, rule subset_refl)
```

For a "good" goal, this sequence will succeed and leave a goal to prove which
has no schematic variables in the assumptions (ideally also not in the
conclusion, but those should be harmless for this purpose). If this sequence
fails, then there most likely is a problem with the parameters of the schematic
precondition the goal is allowed to depend on, e.g. you have `?P x` in the
precondition, but `vcg` is generating a goal that depends on add additional
parameter `y`.

This can happen when new parameters are introduced by `exE`, `clarsimp`, case
distinctions, or other tactics. For instance you might have `x = Some y` in the
assumptions and `?P (Some y)` as the schematic precondition, but the `vcg` needs
`?P y`. Unification is generally not smart enough to figure out that `P (the
(Some y))` would be a solution. The following strategies may help:

* try using the tactic `wpfix`. It can sometimes resolve the problem by
  replacing `?P` with a new `?P` that is allowed to depend on more parameters.

* go back to the place where the schematic `?P` is introduced and introduce the
  parameter before the schematic, so `?P` can depend on the parameter. This could
  happen for instance by using a better case distinction rule that manages
  schematics, or by performing the relevant `exE`, `clarsimp` etc before the
  schematic is introduced (not always possible).

* go back to the place where the parameter `y` is introduced and prevent it from
  being introduced. E.g. instead of using `clarsimp` to generate `x = Some y`
  and using `y`, be careful to keep the form `∃y. x = Some y` in your
  assumptions (or prevent it from even occurring when possible, e.g. by blocking
  a `x ≠ None` rewrite or using `Lib.not_None`). Then use `the x` instead to
  access the content of `x`. This is not necessarily nice, but should always be
  available in principle.

* it is sometimes possible to use `wpc` in `ccorres` goals to produce sub goals
  that provide access to the correct set of parameters (e.g. a `None` case and
  `Some y` case, where `y` is fine to access). This can also be used when one of
  the cases is impossible by showing a contradiction for that branch.

In summary, beware not only of `simp`, which might instantiate schematics, but
also of otherwise safe tactics like `clarsimp` and `exE` when working with `vcg`
goals that still have schematic variables.

## VCG takes very long

Sometimes the `vcg` invocation takes very long for simple goals. There are two
potential reasons for this.

* `vcg` might be expanding the state record into its many constituents. While
  this is a good tactic for the `vcg` for making progress in smaller state
  spaces, the C state in `l4v` is too large for this, and even printing the goal
  state will take a long time in expanded form with hundreds of state variables.

  To avoid this, use `conseqPre` before you apply `vcg` so that there is no
  concrete state the `vcg` can split on. You can resolve the generated
  implication immediately with `subset_refl`, so the full form is the same
  as for avoiding instantiation to `False`:

  ```isabelle
  apply (rule conseqPre, vgc, rule subset_refl)
  ```

* `vcg` might be trying to inline multiple function definitions and the goal is
  then not actually as small as it looked. When this happens the `vcg` prints
  info messages about this unfolding. Prove specification lemmas for the
  functions instead to avoid unfolding.

If you do get a legitimate goal that is very large, you can try to at least
speed up printing at the cost of not expanding syntax and syntax translations:

* Use `supply [[goals_limit = 1]]` if you have more than one goal
* Use the `Quick print` option in jEdit to turn off translations
* Turn off some of the Hoare package's funky syntax translations using

  ```isabelle
  ML {* HoareSyntax.use_call_tr' := false *}
  ```
