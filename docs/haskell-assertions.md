<!--
     Copyright 2021, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

# The role of assertions in Haskell

This is a snapshot of a monologue by @mbrcknl about assertions and monadic failure generally, and more specifically about how we can use assertions in Haskell to transport information from abstract invariants to proofs of Haskell-to-C refinement.

> :mag: **tl;dr**
> * assertions (assert) in Haskell give you:
>   * free assumptions in wp
>   * proof obligations in `corres` in `Refine`
>   * free assumptions in `ccorres` in `CRefine`
> * you can use them to transport information (properties, invariants) from `AInvs` down to Haskell and C:
>   * if you assert `P'` in Haskell
>   * and can derive `[| (s,s') : state_relation; P s |] ==> P' s'`
>   * and can derive `P` in/from AInvs
>   * then you get `P'` for free in wp proofs in Haskell, can prove it from the abstract side in `corres`, and get to assume it in `ccorres` for C

First, let's talk about failure in `corres_underlying`. There are two settings, `nf` and `nf'` which control how `corres_underlying` treats the failure flag on each side of the correspondence.

Concerning `nf`:
* If `nf` is `True`, then we get to assume that the failure flag is not set on the abstract side.
* If `nf` is False, `corres_underlying` doesn't care about the failure flag on the abstract side.

Concerning `nf'`:
* If `nf'` is `True`, then we have to prove that the failure flag is not set on the concrete side.
* If `nf'` is `False`, then `corres_underlying` doesn't care about the failure flag on the concrete side.

For `corres`, we take the strongest combination `(False, True)`. So we don't get to assume that the failure flag is not set on the abstract side, but we have to prove that the failure flag is not set on the concrete side.

Now, you might have heard that during `Refine`, we have to prove any assertions we made in the abstract spec. And you would hope so, since we got to assume them during `AInvs`. But how does that fit with the above, if corres doesn't care about the failure flag on the abstract side?

The thing is, there are two aspects to failure. Remember the type of `nondet_monad: 's => ('a x 's) set x bool`. The `bool` is the failure flag, and that's all that's relevant to the `nf` and `nf'` settings above. There's also a set of results, and if that set is empty, that's the other way that failure manifests.

Why do we have two ways of expressing failure? That's to do with nondeterminism. It's possible to have one branch of the nondeterministic computation fail and another succeed, such that the overall computation still produces a non-empty set of results. But we usually want to know that *no branch failed*, and that's the role of the failure flag.

Of course, we also want to know there is some kind of relationship between the failure flag and the emptiness/non-emptiness of the set of result. So we have a bunch of `empty_fail` proofs about that: `empty_fail` says that if the failure flag is set, then the set of results is empty.

So, now we can look again at `corres_underlying`, and we can see that for `corres`, `nf'` is `True`, so we have to prove that the concrete side does not set the failure flag, and therefore produces a result (assuming `empty_fail` on the concrete side).

The *forall* part of `corres_underlying` then requires that there is a result on the abstract side. Again, assuming `empty_fail` on the abstract side, the failure flag must not be set on the abstract side.

So, even though `nf` is `False` for `corres`, we effectively have to prove that the failure flag is not set on the abstract side, thanks to `empty_fail`.

With all that background, we can now see how assertions relate to `corres`. In `corres`, we have to prove non-failure on both abstract and concrete. Since failed assertions produce a failure, we have to prove that asserts are satisfied on both sides.

Now we can think about why we might want to write assertions.

In `AInvs`, the `valid` predicate we use doesn't insist on getting a result. This effectively means we can assume assertions are satisfied in proofs of invariant Hoare triples. So in `AInvs`, we can use `assert` to defer a proof obligation. Sometimes this allows us to write simpler Hoare triples, since we can elide a precondition if an `assert` gives us the information we need. Simpler Hoare triples can mean simpler proofs elsewhere. So that can be useful, but it can also be dangerous.

In `Refine`, assertions just add to the proof obligations, so that's not particularly useful *for the purpose of getting `Refine` done*. I guess if you really want to know that something is true at a particular point in Haskell, you could use an assertion for that.

But Haskell assertions can be very useful (often essential) in `CRefine`, so to see that, we should move down a level.

Looking at `ccorres_underlying`, there are no toggles like in `corres_underlying`. In `ccorres`, we always get to assume that the abstract side (i.e. Haskell) doesn't have the failure flag set. And it's fine to assume that here, since we proved it during Refine.

So, when proving `ccorres` between a pair of Haskell and C functions, an `assert` in the Haskell allows us to assume that `assert` is satisfied, in much the same way as we do in `AInvs`.

Why is this so useful? Sometimes in `ccorres`, we need information out of an invariant. We don't prove any invariants at the C level, because that would just be too painful. In the past, we have proved lots of invariants at the Haskell level, and with the Haskell-to-C state relation, that's often enough.

But proving invariants at the Haskell level that are equivalent to existing invariants on the abstract spec is a duplication of work, so we're trying to get out of that business.

What we can do instead, when we need some information in `CRefine`, is to add an assertion to Haskell. As far as `CRefine` is concerned, we're just conjuring out of thin air, like we do in `AInvs`. If we do this everywhere we need a particular bit of information in `CRefine`, then we can avoid writing a Haskell invariant for that bit of information.

Of course, we don't get anything for free. When we add an assertion to Haskell, we need to go back to `Refine` to do the work of proving that assertion. But in `Refine`, we have access to invariants proved on the abstract spec, so we often still get to avoid proving invariants on the Haskell level.

In summary, assertions in Haskell can allow us to transport information from `AInvs` to `CRefine`.

We still sometimes need to prove invariants at the Haskell level. This happens when the Haskell spec contains some information that's not present in the abstract spec. For example, Haskell contains a flag in the TCB that indicates whether a thread is in the run queue. We'll need to show that this flag is consistent with the actual queue contents before we can show that a Haskell function that looks at that flag is a refinement of an abstract function that checks whether the thread is in the release queue.

You might wonder whether the same thing happens at the C level. And yes it would, if the C contained information not present in the Haskell spec. We avoid that, by making sure that the Haskell spec has all the information in the C.
