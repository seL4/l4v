(*
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Nondet_README
  imports
    Nondet_More_VCG
    Nondet_Det
    Nondet_No_Throw
    Nondet_Monad_Equations
    WP_README
begin

\<comment> \<open>Nondeterministic State Monad with Failure\<close>

text \<open>
The type of the nondeterministic monad, @{typ "('s, 'a) nondet_monad"}, can be found in
@{theory Monads.Nondet_Monad}, along with definitions of fundamental monad primitives and
Haskell-like do-syntax.

The basic type of the nondeterministic state monad with failure is very similar to the
normal state monad. Instead of a pair consisting of result and new state, we return a set
of these pairs coupled with a failure flag. Each element in the set is a potential result
of the computation. The flag is @{const True} if there is an execution path in the
computation that may have failed. Conversely, if the flag is @{const False}, none of the
computations resulting in the returned set can have failed.

The following lemmas are basic examples of those primitives and that syntax.\<close>

lemma "do x \<leftarrow> return 1;
          return (2::nat);
          return x
       od =
       return 1 >>=
       (\<lambda>x. return (2::nat) >>=
            K_bind (return x))"
  by (rule refl)

lemma "do x \<leftarrow> return 1;
          return 2;
          return x
       od = return 1"
  by simp

text \<open>
We also provide a variant of the nondeterministic monad extended with exceptional return
values. This is available by using the type @{typ "('s, 'e + 'a) nondet_monad"}, with
primitives and syntax existing for it as well\<close>

lemma "doE x \<leftarrow> returnOk 1;
           returnOk (2::nat);
           returnOk x
       odE =
       returnOk 1 >>=E
       (\<lambda>x. returnOk (2::nat) >>=E
            K_bind (returnOk x))"
  by (rule refl)

text \<open>
A Hoare logic for partial correctness for the nondeterministic state monad and the
exception monad is introduced in @{theory Monads.Nondet_VCG}. This comes along with a
family of lemmas and tools which together perform the role of a VCG (verification
condition generator).

The Hoare logic is defined by the @{const valid} predicate, which is a triple of
precondition, monadic function, and postcondition. A version is also provided for the
exception monad, in the form of @{const validE}. Instead of one postcondition it has two:
one for normal and one for exceptional results.

@{theory Monads.Nondet_VCG} also proves a collection of rules about @{const valid}, in
particular lifting rules for the common operators and weakest precondition rules for the
monadic primitives. The @{method wp} tool automates the storage and use of this
collection of rules. For more details about @{method wp} see @{theory Monads.WP_README}.

The following is an example of one of these operator lifting rules and an example of a
relatively trivial Hoare triple being solved by @{method wp}.\<close>

lemma hoare_vcg_if_split:
  "\<lbrakk>P \<Longrightarrow> \<lbrace>Q\<rbrace> f \<lbrace>S\<rbrace>; \<not>P \<Longrightarrow> \<lbrace>R\<rbrace> g \<lbrace>S\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s. (P \<longrightarrow> Q s) \<and> (\<not>P \<longrightarrow> R s)\<rbrace> if P then f else g \<lbrace>S\<rbrace>"
  by simp

lemma
  "\<lbrace>\<lambda>s. odd (value s)\<rbrace>
   do
     x <- gets value;
     return (3 * x)
   od
   \<lbrace>\<lambda>rv s. odd rv\<rbrace>"
  by wpsimp

text \<open>
Lemmas directly about the monad primitives can be found in @{theory Monads.Nondet_Lemmas}
and @{theory Monads.Nondet_Monad_Equations}. Many of these lemmas use @{method monad_eq},
which is a tactic for solving monadic equalities.\<close>

lemma
  "(do x \<leftarrow> gets f;
       xa \<leftarrow> gets f;
       m xa x
    od) =
   (do xa \<leftarrow> gets f;
       m xa xa
    od)"
  by monad_eq

lemma
  "snd (gets_the X s) = (X s = None)"
  by (monad_eq simp: gets_the_def gets_def get_def)

text \<open>
While working with the monad primitives you sometimes end up needing to reason directly
on the states, with goals containing terms in the form of @{term "(v, s') \<in> fst (m s)"}.
Lemmas for handling these goals exist in @{theory Monads.Nondet_In_Monad}, with
@{thm in_monad} being particularly useful.\<close>

lemma
  "(r, s) \<in> fst (return r s)"
  by (simp add: in_monad)

text \<open>
There are additional properties of nondeterministic monadic functions that are often
useful. These include:
  @{const no_fail} - a monad does not fail when starting in a state that satisfies a
    given precondition.
  @{const empty_fail} - if a monad returns an empty set of results then it must also have
    the failure flag set.
  @{const no_throw} - an exception monad does not throw an exception when starting in a
    state that satisfies a given precondition.
  @{const det} - a monad is deterministic and returns exactly one non-failing state.\<close>

text \<open>
Variants of the basic validity definition are sometimes useful when working with the
nondeterministic monad.
  @{const validNF} - a total correctness extension combining @{const valid} and
    @{const no_fail}.
  @{const exs_valid} - a dual to @{const valid} showing that after a monad executes there
    exists at least one state that satisfies a given condition.\<close>

end
