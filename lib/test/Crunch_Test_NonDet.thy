(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Crunch_Test_NonDet
imports
  Lib.Crunch_Instances_NonDet
  Crunch_Test_Qualified_NonDet
  Lib.GenericLib
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

crunch_ignore (valid, empty_fail, no_fail) (add: NonDetMonad.bind)

crunch (empty_fail) empty_fail: crunch_foo2

crunch_ignore (add: crunch_foo1)

crunch gt: crunch_foo2 "\<lambda>x. x > y"
  (ignore_del: crunch_foo1)

crunch_ignore (del: crunch_foo1)

definition
  "crunch_always_true (x :: nat) \<equiv> \<lambda>_. True"

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

crunch (no_fail) no_fail: crunch_foo2
  (wp: crunch_foo1_at_2[simplified])

crunch (valid) at_2: crunch_foo2 "crunch_always_true 2"
  (wp: crunch_foo1_at_2[simplified])

fun crunch_foo3 :: "nat => nat => 'a => (nat,unit) nondet_monad" where
  "crunch_foo3 0 x _ = crunch_foo1 x"
| "crunch_foo3 (Suc n) x y = crunch_foo3 n x y"

crunch gt2: crunch_foo3 "\<lambda>x. x > y"

crunch (empty_fail) empty_fail2: crunch_foo3

(* check that simp rules can be used to solve a goal without crunching *)
crunch (empty_fail) empty_fail: crunch_foo3
  (ignore: crunch_foo1 simp: crunch_foo3_empty_fail2)

class foo_class =
  fixes stuff :: 'a
begin

fun crunch_foo4 :: "nat => nat => 'a => (nat,unit) nondet_monad" where
  "crunch_foo4 0 x _ s = crunch_foo1 x s"
| "crunch_foo4 (Suc n) x y s = crunch_foo4 n x y s"

definition
  "crunch_foo5 x (y::'a) \<equiv> crunch_foo1 x"

end

lemma crunch_foo4_alt:
  "crunch_foo4 n x y \<equiv> crunch_foo1 x"
  apply (induct n)
   apply (simp add: fun_eq_iff)+
  done

(* prove rules about crunch_foo4 with and without the alternative definition *)
crunch gt3: crunch_foo4 "\<lambda>x. x > y"

crunch (no_fail) no_fail2: crunch_foo4
  (rule: crunch_foo4_alt)

crunch gt3': crunch_foo4 "\<lambda>x. x > y"
  (rule: crunch_foo4_alt)

crunch gt4: crunch_foo5 "\<lambda>x. x > y"

(* Test cases for crunch in locales *)

definition
  "crunch_foo6 \<equiv> return () >>= (\<lambda>_. return ())"

crunch_ignore (del: bind)

locale test_locale =
fixes fixed_return_unit :: "(unit, unit) nondet_monad"

begin

definition
  "crunch_foo7 \<equiv> return () >>= (\<lambda>_. return ())"

(* crunch works on a global constant within a locale *)
crunch test[wp]: crunch_foo6 P
(ignore: bind)

(* crunch works on a locale constant *)
crunch test[wp]: crunch_foo7 P
(ignore: bind)

definition
  "crunch_foo8 \<equiv> fixed_return_unit >>= (\<lambda>_. fixed_return_unit)"

definition
  "crunch_foo9 (x :: nat) \<equiv> do
    modify ((+) x);
    modify ((+) x)
  od"

crunch test: crunch_foo9 "\<lambda>x. x > y" (ignore: bind)

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

crunch test[wp]: crunch_foo10 "\<lambda>x. x > y"

(* crunch_ignore works within a locale *)
crunch_ignore (add: bind)

crunch test': crunch_foo9 "\<lambda>x. x > y"

end

interpretation test_locale "return ()" .

(* interpretation promotes the wp attribute from the locale *)
lemma "\<lbrace>Q\<rbrace> crunch_foo7 \<lbrace>\<lambda>_. Q\<rbrace>" by wp

(* crunch still works on an interpreted locale constant *)
crunch test2: crunch_foo7 P
  (wp_del: crunch_foo7_test)

locale test_sublocale

sublocale test_sublocale < test_locale "return ()" .

context test_sublocale begin

(* crunch works on a locale constant with a fixed locale parameter *)
crunch test[wp]: crunch_foo8 P

end

(* check that qualified names are handled properly. *)

consts foo_const :: "(unit, unit) nondet_monad"
defs foo_const_def: "foo_const \<equiv> Crunch_Test_Qualified_NonDet.foo_const"

crunch test: foo_const P

(* check that the grid-style crunch is working *)

crunches crunch_foo3, crunch_foo4, crunch_foo5
  for silly: "\<lambda>s. True \<noteq> False"
  and (no_fail) nf
  and (empty_fail) ef
  (rule: crunch_foo4_alt wp_del: hoare_vcg_prop)

(* check that crunch can use wps to lift sub-predicates
   (and also that top-level constants can be ignored) *)
consts crunch_foo11 :: "(nat, unit) nondet_monad"
consts Q :: "bool \<Rightarrow> nat \<Rightarrow> bool"
consts R :: "nat \<Rightarrow> bool"
axiomatization
  where test1: "\<lbrace>Q x\<rbrace> crunch_foo11 \<lbrace>\<lambda>_. Q x\<rbrace>"
  and test2: "\<lbrace>\<lambda>s. P (R s)\<rbrace> crunch_foo11 \<lbrace>\<lambda>_ s. P (R s)\<rbrace>"

crunch test3: crunch_foo11 "\<lambda>s. Q (R s) s"
  (wp: test1 wps: test2 ignore: crunch_foo11)

(* check that crunch can handle functions lifted between different state spaces *)
record 'a state =
  state' :: nat
  ext :: 'a

definition do_nat_op :: "(nat, unit) nondet_monad \<Rightarrow> ('a state,unit) nondet_monad" where
  "do_nat_op f \<equiv>
     do
       s \<leftarrow> get;
       (_,s') \<leftarrow> select_f (mk_ef (f (state' s)));
       modify (\<lambda>state. state\<lparr>state' := s'\<rparr>)
     od"

lemma do_nat_op_ef:
  "empty_fail f \<Longrightarrow> empty_fail (do_nat_op f)"
  unfolding do_nat_op_def
  apply (wpsimp wp: empty_fail_bind empty_fail_get empty_fail_select_f
              simp: mk_ef_def)
  done

lemma nf_do_nat_op:
  "no_fail P f \<Longrightarrow> empty_fail f \<Longrightarrow> no_fail (P \<circ> state') (do_nat_op f)"
  unfolding do_nat_op_def
  apply wpsimp
  apply (fastforce simp: mk_ef_def no_fail_def empty_fail_def)
  done

definition
  "crunch_foo12_nat (x :: nat) = modify ((+) x)"

consts wrap_ext_op :: "(nat state, unit) nondet_monad \<Rightarrow> ('a state,unit) nondet_monad"
consts unwrap_ext :: "'a state \<Rightarrow> nat state"

definition do_extended_op :: "(nat state, unit) nondet_monad \<Rightarrow> ('a state,unit) nondet_monad" where
  "do_extended_op eop \<equiv> do
                         ex \<leftarrow> get;
                         (_,es') \<leftarrow> select_f (mk_ef ((wrap_ext_op eop) ex));
                         modify (\<lambda>state. state\<lparr>ext := (ext es')\<rparr>)
                        od"

axiomatization
  where do_extended_op_ef[wp]: "empty_fail f \<Longrightarrow> empty_fail (do_extended_op f)"
  and nf_do_extended_op[wp]: "no_fail P f \<Longrightarrow> empty_fail f \<Longrightarrow> no_fail (P \<circ> unwrap_ext) (do_extended_op f)"

definition
  "crunch_foo12_ext (x :: nat) = modify (ext_update ((+) x))"

definition
  "crunch_foo12 x \<equiv>
     do
       do_extended_op (crunch_foo12_ext x);
       do_nat_op (crunch_foo12_nat x)
     od"

crunches crunch_foo12
  for (empty_fail) ef[wp]
  and (no_fail) nf
  (wp: empty_fail_bind)

(* check that other side conditions can still be collected when mixed with lifted functions*)
definition crunch_foo13_pre :: "('a state,unit) nondet_monad" where
  "crunch_foo13_pre \<equiv> return ()"

axiomatization
  where nf_crunch_foo13_pre[wp]: "no_fail (crunch_always_true 0) crunch_foo13_pre"

definition
  "crunch_foo13 x \<equiv>
     do
       crunch_foo13_pre;
       do_extended_op (crunch_foo12_ext x);
       do_nat_op (crunch_foo12_nat x)
     od"

crunches crunch_foo13
  for (no_fail) nf

end
