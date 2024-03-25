<!--
     Copyright 2022, UNSW (ABN 57 195 873 197)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Notes on C refinement proof in practice

Notes/Issues on the refinement from Haskell to C (or how to use Simon's magic framework).

## The big picture

The correspondence lemma between the Haskell level and the C level, for a given operation 'op', has the following statement:


```
ccorres r xf P P' hs (op arguments) (Call op_'proc)

```
where

* `r ::` `α` `⇒` `ß`  `⇒` `bool` is the relation between the return values
* `xf :: state` `⇒` `ß` projects the return value from the (concrete) state
* `P` is the precondition on the Haskell side
* `P'` is the precondition on the C side
* `hs` is the handler stack
* `op` is the definition of the operation on the Haskell side
* `op_'proc` is the definition of the operation on the C side

This statement can be visualised as follow:


```
(P s1) holds      s1 -------------->  (s2,  v )
                  /\                   /\   /\
                   |                    |    |
                   | rf_sr        rf_sr |    | r
                   |                    |    |
                   |                    |    |
                  \/    op_'proc       \/   \/
(s1':P') holds    s1' --------------> (s2', xf(s2'))

```
(where rf\_sr is the state relation. Actually `ccorres == ccorresG Gamma rf_sr`)

## The general proof architecture

The proof will roughly look like:


```
cinit	                  *
   ctac/csymbr...         +
     ctac/csymbr...       +
       ctac/csymbr...     +
         ...
        wp                x
       vcg                x
      wp                  x
     vcg                  x
    wp                    x
   vcg                    x
  <proof of last big subgoal>

```
The `*` line is the proof initialisation.

The + lines are the proof of ccorres subgoal.

The `x` lines are the hoare triple proofs (both from Haskell and C).

The final line is where we prove that the conjunction of all the preconditions accumulated along the proof is implied by the original precondition of the lemma.

## Proof Initialisation

The first step is to unfold the function bodies and to generalise the preconditions by applying:


```
apply (cinit)

```
or


```
apply (cinit lift: arg1_' arg2_'...)

```
(see Simon's note for more detail)

in order to obtain two subgoals:


```
1. ccorres r xf (?Q ...) (?Q' ...) hs
	   (do
              y0 ← f0 x0;
              y1 ← f1 x1;
              ...
            od)
           (y0':== f0' x0';;
            y1':== f1' x1';;
            ...)
2. ⟦ (s, s') : rf_sr; P s; s' : P' ⟧ ⟹ ?Q s  ∧  s' : ?Q'

```
The generalisation of the preconditions follows the idea that the proof will be done on schematic preconditions that will be instantiated all along the proof. And at the end we'll prove that the final instantiation of the preconditions is implied by the original ones in the lemma statement. The underlying theorem that is used for generalising the preconditions is:


```
ccorres_guard_imp2
```
There is also the theorem


```
ccorres_guard_imp
```
that generates three subgoals (2 separate additional subgoals, one for the Haskell precondition and one for the C precondition)

The `cinit` tactic is an abbreviation for (roughly):


```
unfolding op_def                             -- "unfolds the Haskell function body"
  apply (rule ccorres_Call)                    -- "replaces the C side by a schematic function body,
                                                   with a new subgoal for the definition of the schematic being the C function body"
   apply (rule op_impl [unfolded op_body_def]) -- "finds the C function body"
  apply (rule ccorres_rhs_assoc)+              -- "re-associates the sequence of C instructions (to be able to consider the 1st one)"
  apply (simp del: return_bind Int_UNIV_left)  -- "simplification, but keeping the returns and the (UNIV inter ...)"
  apply (cinitlift arg1_' arg2_' ...)          -- "lifts variables out of C precondition"
  apply (rule ccorres_guard_imp2)              -- "generalises the precondition (replaces by schematic and additional subgoal)"

```
It is worth knowing the sequence that `cinit` abbreviates in case `cinit` does not work ;‑)

### If it doesn't work

* The simplifier may be messing you up, especially if there are `if _ then _ else` statements in the haskell side of the refinement. Try adding:


  ```
  lemma foo:
     notes if_split [split del]
     shows "ccorres ..."
   apply cinit
   ...

  ```
  which will take `split_if` out of the split simp set for the rule.

## Working on the ccorres subgoal

The general idea is to use the tactic `ctac` to replace the current 'ccorres subgoal' (subgoal 1 above) by:


```
1. ccorres r xf (?Q0 ...) (?Q0' ...) hs
	   (do y1 ← f1 x1; ... od)
           (y1':== f1' x1';; ...)
2. {?Q} y0 ← f0 x0 {?Q0}
3. Γ ⊢ (?Q') y0':== f0' x0'(?Q0')

```
In other words, we roughly have the first instruction in the Haskell sequence that corresponds to the first one in the C sequence. And we (hopefully) already have a ccorres lemma stating that they correspond. So we use `ctac`, possibly giving the ccorres lemma to use:


```
apply (ctac add: ccorres_i0)

```
This can be visualised as follows (we only show the preconditions that hold):


```
_
           i0            i1               in
P  ⟹ ?Q ------>  ?Q0 ------> ?Q1  ... ------> ?Qn
       |            |           |                |
       |   i0'      |    i1'    |         in'    |
P' ⟹ ?Q'------> ?Q0' ------> ?Q1' ... ------> ?Qn'

```
So the first phase after initialisation is to apply `ctac` to all pairs of instructions, in order to generate all the Hoare triple subgoals on schematic pre and postconditions, that will be linked as shown in the above diagram. The second phase (proving the Hoare triples) will start 'by the end': instantiating the ?Qn and ?Qn' until the ?Q and ?Q' (see next section). The last step will finally prove the implication (`P ⟹ ?Q` and `P' ⟹ ?Q'`)

But unfortunately, the Haskell side and the C side are not always such ideally linked by exact pair-wise instructions matching.
These are some things that may happen and some hints do deal with it:

* if there is an instruction in C that does not appear in Haskell (typically `y:==CALL op(args)`) then


  ```
  apply csymbr

  ```
  should symbolically execute the C side only. If it does not work (it happens ;‑) ) then we can apply the underlying lemma by hand:


  ```
  apply (rule ccorres_symb_exec_r)

  ```
  but it generates 2 additional subgoals (the Hoare triple of the C side and preservation of the state relation). If this takes too large or too small a step because of the associativity of the C representation, you can manipulate this by applying `ccorres_rhs_assoc` or `ccorres_lhs_assoc` beforehand.


* if there is an Haskell instruction that does not appear in C (typically `cte <- getCTE slot`) then


  ```
  apply (rule ccorres_symb_exec_l)

  ```
  (with similarly 2 additional subgoals, one for the Haskell Hoare triple and one for the existence of a resulting state). Like the C side, if this takes too large or small steps due to associativity, you can manipulate the representation with `bind_assoc` or `bind_assoc2` beforehand.


* Finally if `ctac` does not work (e.g. no exact matching with the ccorres lemma of the first instruction), we can split by hand by using:


  ```
  apply (rule ccorres_split_nothrow)

  ```
  which generates 5 subgoals: the 3 that `ctac` usually generated (the corres proof of the rest of the sequence, the Haskell Hoare triple and the C Hoare triple) plus the corres proof of the first instruction and a 'ceqv' subgoal, proved by `ceqv` tactic (see Simon's notes). If you're in a more specific case, you can apply one of the variants like `ccorres_split_nothrow_call_novcg` which can sometimes generate nicer subgoals.



  Remark: before applying `ccorres_split_nothrow`, we generally have to apply `ccorres_guard_imp2` to generalise the preconditions (because `ccorres_split_nothrow` expects intersections of preconditions, which might not be the case of the goal where `ccorres_split_nothrow` is applied)

## Proving the Hoare triple

Mostly, this phase is just a sequence of application of `wp` and `vcg` tactics.

However here are some tips for when things go wrong:

* if `vcg` is expanding all the state, see the [VCG debugging guide](vcg-debugging.md#vcg-takes-very-long).

* sometimes the precondition generated by `vcg` contains `False` somewhere or leaves an unprovable
  goal (we figure it out while trying to prove the 'last big subgoal') so a modification before
  `vcg` is needed. See the [VCG debugging
  guide](vcg-debugging.md#unprovable-goals-and-false-in-the-post-condition) for these cases.

## Proving the 'last big subgoal'

This 'last big subgoal' is where we prove that the `P` and `P'` appearing in the lemma statement imply the `?Q` and `?Q'` that have, at that point, been instantiated to a big conjunction of all the preconditions computed to fulfil the Hoare triple for each instruction of the program.

The first thing that may happen here is that you end up needing to prove `False` or get an
unprovable goal from the C `vcg`. See the [VCG debugging guide](vcg-debugging.md) for more
information.

Another problem is to deal with sometimes 40 goals after expansion of this last goal, and usually very similar goals. So this idea is to 'generate' the more useful premises as possible before expanding (by `subgoal_tac` or `frule`).

In this context, a trick that helped me is that if some subgoals depend on an equality (e.g. one subgoal being `a = b ⟶ P`), then try to formulate the lemma you want to use as frule (before expansion) as


```isabelle
⟦ bla ⟧ ⟹ a = b ⟶ P
```

instead of

```isabelle
⟦ bla; a = b ⟧ ⟹ P
```

(because if not you will need first to expand and then to do `impI` and then to apply the lemma, whereas in the first case, you can do frule before expansion and hopefully even have the subgoal proved automatically).

## Some other hints

* if you can't find a lemma of name N or a definition of name N, look for N\_underlying ;‑)
* each time you write yourself a term containing Ptr (in a statement or using `subgoal_tac`), you have to constrain the type (if not strange things happen, such as `apply assumption` not working on `a ⟹ a`) The type should be explicit. Example:


  ```
  ((Ptr &(Ptr POINTER :: cte_C ptr ->[''cteMDBNode_C''])) ::mdb_node_C ptr)

  ```




* if `csymbr` does not work, verify that the association is correct or use `ccorres_rhs_assoc` before.
* Sometimes `ctac` does not apply because of const being unfolded; try


  ```
  apply (ctac add: rule [unfolded const_def])
  ```




* if the `vcg` takes too long, see the [VCG debugging guide](vcg-debugging.md)
  for strategies.





## VCGs and No-VCGs

A number of the rules and tactics have a VCG and a no-VCG variant. For instance, `apply (ctac(no_vcg))` and `rule ccorres_split_nothrow_novcg` compared to `rule ccorres_split_nothrow`.

The ccorres rules are all designed so there should be as little to prove as possible on the C side. Most ccorres rules only assume UNIV or a property about local arguments. Local arguments will mostly be bound by ceqv, and information about them available globally. So it may be possible to prove the C assumptions on the spot and skip the VCG work of passing them backwards. This is when the no-VCG variants can be used.

If a proof attempt ends with an attempted "guard\_is\_UNIV" proof when the guard doesn't seem to be provable, or if the final big goal requires a proof of some non-trivial property for all states (possibly quantifying over the variable "t"), then you probably used a no-VCG variant when you shouldn't have.

-----

OK, the hard part. The real reason the no-VCG variants exist is because the VCG sometimes generates over-strong assumptions. Here's why. Norbert's Simpl language and VCG are designed for a verification approach in which one true Hoare triple is proven for every function. If a lemma exists with the name f\_spec, the VCG will attempt to use it as a specification for the function f, ignoring f's actual definition. If that spec rule has a precondition, e.g. the pointer validity precondition in the spec rules for the \_ptr\_ variants of the bitfield functions, that precondition must be established. Even if we're proving the weak version of the Hoare triple where we can assume rather than prove the pointer guards.

Yuck.

So, something to look out for. Running the VCG over a function whose spec has preconditions may create work for you that you don't really need. Also watch out for the VCG inlining functions when you didn't need that either. One solution is to use the no-VCG rule variants, but it can be tricky to ensure this is safe. The most involved and effective option is the `apply (vcg exspec=getSyscallArg_modifies)` form you will see in the proofs. These "extra spec" (exspec) rules override the usual spec rules, and the modifies rules produced by the parser are ideal for this purpose since they have no precondition. But you have to be careful to override all the spec rules that were used.

## Basics

### Extraction functions

The main reason for most of this machinery is to get the result out of a C function. Unlike Haskell where the result is separate to the state, the C result is just stored in a variable. This variable is that function's *extraction function* (usually denoted xf).

A general method that applies to most of the tactics is lifting replacing a xf (i.e., something like `cPtr_' s`) with a HOL variable. The actual rewriting is done through the term `ceqv`, the rules for which are in seL4-api/crefine/Corres\_UL\_C.thy.

Procedure invocation involves transferring the result from the function's return variable into the local variable. For example, in the code


```
foo :== CALL bar(a, b, c)

```
`bar` might place its result in variable `ret__unsigned_long`. The last thing the call does is


```
foo :== ret__unsigned_long

```
This becomes an issue when we are lifting the xf — we want to lift `foo` in this case, but corres lemmas about `bar` results will talk about `ret__unsigned_long`. The tactics examine the C portion of the current goal and figure out the current xf (in this case `foo`) and instantiate the required rule at this variable — otherwise this instantiation would need to be by hand.

### Records

A further annoyance is field updates to structs. The C code


```
foo.bar = x

```
will be translated to


```
Basic (%s. foo_update (%_. bar_update (%_. x) (foo s)))

```
The rules need both functions and are different than for the non-record case — they do not generate a new HOL variable (usually the `(foo s)` above will have been replaced — if it has not been, it is lifted). Instead, they will replace `foo` after the statement by `(bar_update (%_.x) old_value)`

## Tactics

There are a number of tactics which basically take care of some of the annoying steps required by the way the C verification works. They are set up in seL4-api/crefine/Corres\_C.thy and implemented in seL4-api/crefine/ctac-method.ML.

### Arguments and Options

Tactics which take options take them in parentheses before any theorem arguments, e.g.


```
apply (ctac (no_vcg, trace) add: foo_ccorres simp: blah_simp)

```

### Debugging

Most tactics (all the important ones, see below) take tracing arguments (in parentheses) which control the tracing behaviour. Tracing output is prefixed by the depth, which can be used with
[[simp-outline.el|simp-outline.el]] — have a look at the outline-mode docs for usage.

The tactic `ctac_print_xf` will print some information about what `ctac` and friends think is the current xf.



### ceqv

`ceqv` solves goals of the form `ceqv G xf v t t' c ?C` which essentially means replace `xf s` by `v` in `c` to get `?C`. ceqv rules typically rely on `xpres xf v G c`, which states that the statements in c preserve the value at xf (where xf is a field in the state).

The details of how `ceqv` works are somewhat gruesome (see `ctac-method.ML`), although the following probably needs to be known by users:

* `ceqv` will try to replace as many occurrences as it can. Typically this means that occurrences will be replaced up until xpres fails. This will occur if the variable under consideration is updated. In the tactic, rule `Seq_ceqv` will fail, then `Seq_weak_ceqv`, which looks at the LHS of a Seq only, will be tried.
* While will fail if the variable is updated in the body.

#### Usage

Options are 'trace' and 'trace\_ceqv' (both of which turn on tracing)


```
apply (ceqv (trace))

```



### cinitlift

This tactic lifts variables out of the concrete guard. The guard should be


```
G ∧ {s. P1 (xf1 s)} ∧ {s. P2 (xf2 s)} ∧ ... ∧ {s. Pn (xfn s)}

```
The arguments are the variables to be lifted, in left to right order. Note that the tactic works from right to left, so


```
apply (cinitlift xf3 ... xfn)
```
will work, while


```
apply (cinitlift xf1 xf2 xf3)
```
will not (assuming n > 3).

This tactic is superseded by `cinit`, but may be useful if you want to do some things by hand. The tactic applies the rule `ccorres_tmp_lift11` and then `ccorres_tmp_init_lift12`

#### Usage

At least 1 argument is required.


```
apply (cinitlift xf1 xf2 ... xfn)

```


### cinit and cinit'

The tactic `cinit` does the boilerplate required at the start of at corres proof. The following two pieces of code do more or less the same thing:


```
apply (cinit lift: destSlot_' srcSlot_' newCap_' simp del: return_bind)

```
and


```
apply (unfold cteInsert_def)
  apply (rule ccorres_Call)
  apply (rule cteInsert_impl [unfolded cteInsert_body_def])
  apply (rule ccorres_rhs_assoc)+
  apply (simp del: return_bind Int_UNIV_left)
  apply (cinitlift destSlot_' srcSlot_' newCap_')
  apply (erule ssubst)+
  apply (rule ccorres_guard_imp2)

```
`cinit'` is identical to `cinit` except that it doesn't unfold the abstract side.

#### Usage

The lift must come before any other arguments. All arguments are optional.


```
apply (cinit lift: xf1 xf2 ... xfn simp (add?|del|only): ... cong (add?|del|only): ...)

```
Options are:

* no\_subst\_asm | subst\_asm\_vars | subst\_asm: don't substitute, substitute only var = ..., substitute everything (default)
* ignore\_call | no\_ignore\_call: whether to simplify inside call arguments or ignore (default)
* trace\_all | trace\_ceqv: tracing



### ctac

`ctac` is the main tactic for proving corres lemmas. It splits the goal (if required) and tries to apply any rule that has been declared `[corres]` or any that is passed in via the `add` annotation. It tries to instantiate the xf; in the case where it cannot and the term is a function call, it will use `xfdc` — you may see HOL variables called xfdc as consequence (this should be fixed at some point).

#### Usage

All arguments are optional. There are 2 sets of arguments: option controlling how ctac works, and attributes controlling rules used. The options are parenthesised (like `simp`) and come before any other options. Multiple options are separated by commas. For example:


```
apply (ctac (no_simp, trace) pre: ccorres_getCTE)

```
Options are:

* no\_simp: Leave any assumptions of the matched corres rule (i.e., that which matches the LHS of the bind and Seq)
* use\_simp: Simplify the assumptions of the matched corres rule.
* no\_vcg: Don't generate vcg goals — only really useful if the hoare triple would have a trivial post-condition. In the case of a CALL, this means the post-condition refers only to local variables, in other cases, the post-condition must be equal to `UNIV` (and there is a goal stating this). At the moment the record cases may not always work (see treatment of oldv in the record\_novcg lemmas)
* c\_lines <n>: assumes that <n> lines of C correspond to the first line of Haskell. What `ctac` effectively does is to apply rule `ccorres_rhs_assoc2` for (<n> - 1) times.
* trace: trace everything
* trace\_ceqv: trace ceqv

Note that tracing options stack — (trace, trace\_ceqv) == (trace)

Attributes are (any order is permissible):

* add | del | only: add/remove/use only the given rules for solving corres goals. These rules can have assumptions which must be solvable by simp. Rules can also be added via the corres attribute
* pre (add? | del | only): add/remove/use only the given rules for pre-processing corres goals. pre rules must have only one premise which is corres. Rules can also be added via the corres\_pre attribute
* simp (add? | del | only): as for simp
* cong (add? | del | only): as for simp
