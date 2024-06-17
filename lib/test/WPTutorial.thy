(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory WPTutorial
imports "Refine.Bits_R"
begin

text \<open>
This is a tutorial on the use of the various Hoare mechanisms developed
for the L4.verified project. We import Bits_R above, which is a compromise
between the twin goals of getting the Hoare setup from L4.verified and not
importing existing properties. It's probably best to work from a prebuilt
Refine Isabelle image which includes Bits_R.
\<close>

text \<open>The point of our apparatus is to prove Hoare triples. These are a
triple of a precondition, function, and postcondition. In our state-monadic
world, the precondition is a function of the state, and the postcondition
is a function of the return value and the state. In example 1 below,
the precondition doesn't impose any restriction on the state, and the
postcondition only requires that the return value be the obvious one.\<close>

text \<open>The weakest precondition tool, wp, attempts to construct the
weakest precondition for a given postcondition. Use wp (with the command
"apply wp") to solve example 1\<close>

lemma example_1:
  "\<lbrace>\<lambda>s. True\<rbrace> return 1 \<lbrace>\<lambda>rv s. rv = 1\<rbrace>"
  apply wp
  apply simp
  done

text \<open>The wp tool works in reverse order (from postcondition to weakest
precondition, rather than from precondition to strongest postcondition).
It stops when it encounters a postcondition/function pair it doesn't
know any rules for. Try example 2 below, noting where wp gets stuck.

The wp method already knows how to handle most monadic operations
(liftE, catch, assert, when, if-then-else, etc) but there are some
exceptions. One is the split operator, which hides behind Isabelle syntax
that looks like (\<lambda>(x, y). blah), {(x, y). blah}, (\<forall>(x, y) \<in> S. blah).
Solve the problem by unfolding it with (simp add: split_def).

The intermediate precondition seen when wp stops is a schematic variable.
The wp tool uses Isabelle's underlying unification mechanism to set the
precondition as it goes. This usually works well, but there are some
problems, especially with tuples. Note the strange behaviour if we use
clarsimp instead of (simp add: split_def) to deal with the split constant.
The root cause of this strange behaviour is that the unification mechanism
does not know how to construct a ?P such that "?P (a, b) = a". This is
annoying, since it means that clarsimp/clarify/safe must frequently be
avoided.
\<close>

lemma example_2:
  "\<lbrace>\<lambda>s. s = [(True, False), (False, True)]\<rbrace> do
     v \<leftarrow> gets length;
     (x, y) \<leftarrow> gets hd;
     return x
   od \<lbrace>\<lambda>rv s. rv\<rbrace>"
  apply wp
     apply (simp add: split_def)
     apply wp+
  apply simp
  done

text \<open>
An additional annoyance to the clarsimp/tuple issue described above is
the splitter. The wp tool is designed to work on a hoare triple with a
schematic precondition. Note how the simplifier splits the problem
in two because it contains an if constant. Delete the split
rule from the simpset with (simp split del: if_split) to avoid this
issue and see where wp gets stuck.

We still need to deal with the if constant. In this (somewhat contrived)
example we can give the simplifier the rule if_apply_def2 to make
progress.

Note that wp can deal with a function it knows nothing about if
the postcondition is constant in the return value and state.
\<close>

lemma example_3:
  "\<lbrace>\<lambda>s. s = [False, True]\<rbrace> do
     x \<leftarrow> gets hd;
     possible_state_change_that_isnt_defined;
     y \<leftarrow> gets (if x then \<bottom> else \<top>);
     return $ y \<and> \<not> x
   od \<lbrace>\<lambda>rv s. rv\<rbrace>"
  apply wp
    apply (simp add: if_apply_def2 split del: if_split)
    apply wp+
  apply simp
  done

text \<open>Let's make this more interesting by introducing some functions
from the abstract specification. The set_endpoint function (an abbreviation
for the function set_simple_ko) is used to set the contents of an endpoint
object somewhere in the kernel object heap (kheap). The cap derivation
tree (cdt) lives in an entirely different field of the state to the kheap,
so this fact about it should be unchanged by the endpoint update.
Solve example 4 - you'll have to unfold enough definitions that wp knows
what to do.\<close>

lemma example_4:
  "\<lbrace>\<lambda>s. cdt s (42, [True, False]) = None\<rbrace>
      set_endpoint ptr Structures_A.IdleEP
   \<lbrace>\<lambda>rv s. cdt s (42, [True, False]) = None\<rbrace>"
  apply (simp add: set_simple_ko_def set_object_def get_object_def)
  apply wp
  apply clarsimp
  done

text \<open>
Example 4 proved that a property about the cdt was preserved from
before set_endpoint to after. This preservation property is true for
any property that just talks about the cdt. Example 5 rephrases
example 4 in this style. Get used to this style of Hoare triple,
it is very common in our proofs.
\<close>

lemma example_5:
  "\<lbrace>\<lambda>s. P (cdt s)\<rbrace>
      set_endpoint ptr Structures_A.IdleEP
   \<lbrace>\<lambda>rv s. P (cdt s)\<rbrace>"
  apply (simp add: set_simple_ko_def set_object_def get_object_def)
  apply wp
  apply clarsimp
  done

text \<open>
The set_cap function from the abstract specification is not much different
to set_endpoint. However, caps can live within CSpace objects or within
TCBs, and the set_cap function handles this issue with a case division.

The wp tool doesn't know anything about how to deal with case statements.
In addition to the tricks we've learned already, use the wpc tool to break
up the case statement into components so that wp can deal with it to solve
example 6.
\<close>

lemma example_6:
  "\<lbrace>\<lambda>s. P (cdt s)\<rbrace>
     set_cap cap ptr
   \<lbrace>\<lambda>rv s. P (cdt s)\<rbrace>"
  apply (simp add: set_cap_def split_def set_object_def
                   get_object_def)
  apply (wp | wpc)+
  apply simp
  done

text \<open>
The wp method can be given additional arguments which are theorems to use
as summaries. Solve example 7 by supplying example 6 as a rule to
use with (wp example_6).
\<close>

lemma example_7:
  "\<lbrace>\<lambda>s. cdt s ptr' = None\<rbrace> do
     set_cap cap.NullCap ptr;
     v \<leftarrow> gets (\<lambda>s. cdt s ptr);
     assert (v = None);
     set_cap cap.NullCap ptr';
     set_cap cap.IRQControlCap ptr';
     return True
   od \<lbrace>\<lambda>rv s. cdt s ptr = None \<and> cdt s ptr' = None\<rbrace>"
  apply (wp example_6)
  apply simp
  done

text \<open>
There isn't a good reason not to use example_6 whenever possible, so we can
declare example_6 a member of the wp rule set by changing its proof site to
"lemma example_6[wp]:", by doing "declare example_6[wp]", or by putting it
in a group of lemmas declared wp with "lemmas foo[wp] = example_6".
Pick one of those options and remove the manual reference to example_6 from
the proof of example_7.
\<close>

text \<open>
These preservation Hoare triples are often easy to prove and apply, so much
of the effort is in typing them all out. To speed this up we have the crunch
tool. Let's prove that setup_reply_master and set_endpoint don't change
another field of the state, machine_state. I've typed out the required
crunch command below. Let's explain the bits. The naming scheme
"machine_state_preserved:" sets a common suffix for all the lemmas
proved. Just like with lemma names, we could add the theorems to the wp set
with "machine_state_preserved[wp]:". What follows is a list of functions.
The crunch tool also descends through the call graph of functions, so it
proves a rule about set_cap because setup_reply_master calls it. The last
argument is the term to appear in the precondition and postcondition.

The final, optional bit of the crunch syntax is a group of modifiers, which
go between the parentheses inserted below. The crunch command doesn't
currently work. We need to provide some additional simp and wp rules
with syntax like (simp: some rules wp: some rules). If you look at the way
crunch failed, you'll spot which simp rule we need to add to make some
progress.

But not much more progress. To get through set_endpoint, we need to deal
with a slightly complex postcondition to get_object, one which incorporates
an assertion about its return value. We can solve this problem by simply
throwing the extra assumption away - supplying the wp rule hoare_drop_imps
does this. There are standard sets of simp and wp rules which are frequently
helpful to crunch, crunch_simps and crunch_wps, which contain the rules we
added here.

Finally, this proof needs to simplify the predicates underneath an
@{text "if"}, which uses a congruence rule. The crunch command doesn't provide
syntax for this and more rarely used simp and wp modifiers. We can still supply
the necessary rules by putting the crunch command in a context block that declares
those rules.
\<close>

context
notes if_cong[cong]
begin

crunch
  setup_reply_master, set_simple_ko
  for machine_state_preserved: "\<lambda>s. P (machine_state s)"
  (simp: split_def wp: crunch_wps)

end

end
