(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Crunch_Test_Trace
imports
  Lib.Crunch_Instances_Trace
  Crunch_Test_Qualified_Trace
  Lib.Defs
begin

text \<open>Test cases for crunch\<close>

definition
  "crunch_foo1 (x :: nat) \<equiv> do
    modify ((+) x);
    modify ((+) x)
  od"

definition
  "crunch_foo2 \<equiv> do
    crunch_foo1 12;
    crunch_foo1 13
  od"

crunch_ignore (add: crunch_foo1)

crunches crunch_foo2
  for gt: "\<lambda>x. x > y"
  (ignore: modify bind ignore_del: crunch_foo1)

crunch_ignore (del: crunch_foo1)

definition
  "crunch_always_true (x :: nat) \<equiv> \<lambda>y :: nat. True"

lemma crunch_foo1_at_2:
  "True \<Longrightarrow> \<lbrace>crunch_always_true 3 and crunch_always_true 2\<rbrace>
      crunch_foo1 x \<lbrace>\<lambda>rv. crunch_always_true 2 and K True\<rbrace>"
  by (simp add: crunch_always_true_def, wp)

lemma crunch_foo1_at_3[wp]:
  "\<lbrace>crunch_always_true 3\<rbrace> crunch_foo1 x \<lbrace>\<lambda>rv. crunch_always_true 3\<rbrace>"
  by (simp add: crunch_always_true_def, wp)

lemma no_fail_crunch_foo1:
  "True \<Longrightarrow> no_fail (crunch_always_true 2 and crunch_always_true 3) (crunch_foo1 x)"
  apply (simp add:crunch_always_true_def crunch_foo1_def)
  apply (rule no_fail_pre)
   apply (wp, simp)
  done

crunches crunch_foo2
  for (no_fail) no_fail
  (ignore: modify bind wp: crunch_foo1_at_2[simplified])

crunches crunch_foo2
  for (valid) at_2: "crunch_always_true 2"
  (ignore: modify bind wp: crunch_foo1_at_2[simplified])

fun crunch_foo3 :: "nat => nat => 'a => (nat,unit) tmonad" where
  "crunch_foo3 0 x _ = crunch_foo1 x"
| "crunch_foo3 (Suc n) x y = crunch_foo3 n x y"

crunches crunch_foo3
  for gt2: "\<lambda>x. x > y"
  (ignore: modify bind)

class foo_class =
  fixes stuff :: 'a
begin

fun crunch_foo4 :: "nat => nat => 'a => (nat,unit) tmonad" where
  "crunch_foo4 0 x _ = crunch_foo1 x"
| "crunch_foo4 (Suc n) x y = crunch_foo4 n x y"

definition
  "crunch_foo5 x (y::'a) \<equiv> crunch_foo1 x"

end

lemma crunch_foo4_alt:
  "crunch_foo4 n x y \<equiv> crunch_foo1 x"
  apply (induct n)
   apply simp+
  done

crunches crunch_foo4
  for gt3: "\<lambda>x. x > y"
  (ignore: modify bind)

crunches crunch_foo4
  for (no_fail) no_fail2
  (rule: crunch_foo4_alt ignore: modify bind)

crunches crunch_foo4
  for gt3': "\<lambda>x. x > y"
  (rule: crunch_foo4_alt ignore: modify bind)

crunches crunch_foo5
  for gt4: "\<lambda>x. x > y"
  (ignore: modify bind)

(* Test cases for crunch in locales *)

definition
  "crunch_foo6 \<equiv> return () >>= (\<lambda>_. return ())"

locale test_locale =
fixes fixed_return_unit :: "(unit, unit) tmonad"

begin

definition
  "crunch_foo7 \<equiv> return () >>= (\<lambda>_. return ())"

(* crunch works on a global constant within a locale *)
crunches crunch_foo6
  for test[wp]: P
(ignore: bind)

(* crunch works on a locale constant *)
crunches crunch_foo7
  for test[wp]: P
(ignore: bind)

definition
  "crunch_foo8 \<equiv> fixed_return_unit >>= (\<lambda>_. fixed_return_unit)"

definition
  "crunch_foo9 (x :: nat) \<equiv> do
    modify ((+) x);
    modify ((+) x)
  od"

crunches crunch_foo9
  for test: "\<lambda>x. x > y" (ignore: bind)

definition
  "crunch_foo10 (x :: nat) \<equiv> do
    modify ((+) x);
    modify ((+) x)
  od"

(*crunch_def attribute overrides definition lookup *)

lemma crunch_foo10_def2[crunch_def]:
  "crunch_foo10 = crunch_foo9"
  unfolding crunch_foo10_def[abs_def] crunch_foo9_def[abs_def]
  by simp

crunches crunch_foo10
  for test[wp]: "\<lambda>x. x > y"

(* crunch_ignore works within a locale *)
crunch_ignore (add: bind)

crunches crunch_foo9
  for test': "\<lambda>x. x > y"

end

interpretation test_locale "return ()" .

(* interpretation promotes the wp attribute from the locale *)
lemma "\<lbrace>Q\<rbrace> crunch_foo7 \<lbrace>\<lambda>_. Q\<rbrace>" by wp

(* crunch still works on an interpreted locale constant *)
crunches crunch_foo7
  for test2: P
  (wp_del: crunch_foo7_test)

locale test_sublocale

sublocale test_sublocale < test_locale "return ()" .

context test_sublocale begin

(* crunch works on a locale constant with a fixed locale parameter *)
crunches crunch_foo8
  for test[wp]: P

end

(* check that qualified names are handled properly. *)

consts foo_const :: "(unit, unit) tmonad"
defs foo_const_def: "foo_const \<equiv> Crunch_Test_Qualified_Trace.foo_const"

crunches foo_const
  for test: P

(* check that the grid-style crunch is working *)

crunches crunch_foo3, crunch_foo4, crunch_foo5
  for silly: "\<lambda>s. True \<noteq> False"
  and (no_fail) nf
  (ignore: modify bind rule: crunch_foo4_alt wp_del: hoare_vcg_prop)

end
