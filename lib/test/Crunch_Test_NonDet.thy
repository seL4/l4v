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

definition crunch_foo1 :: "nat \<Rightarrow> (unit, nat, unit) nondet_monad" where
  "crunch_foo1 x \<equiv> do
    modify (map_state ((+) x));
    modify (map_state ((+) x))
  od"

definition crunch_foo2 :: "(unit, nat, unit) nondet_monad" where
  "crunch_foo2 \<equiv> do
    crunch_foo1 12;
    crunch_foo1 13
  od"

crunch_ignore (valid, empty_fail, no_fail) (add: Nondet_Monad.bind)

crunch crunch_foo2
  for (empty_fail) empty_fail

crunch_ignore (add: crunch_foo1)

crunch crunch_foo2
  for gt: "\<lambda>x. mstate x > y"
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

crunch crunch_foo2
  for (no_fail) no_fail
  (wp: crunch_foo1_at_2[simplified])

crunch crunch_foo2
  for (valid) at_2: "crunch_always_true 2"
  (wp: crunch_foo1_at_2[simplified])

fun crunch_foo3 :: "nat => nat => 'a => (unit, nat, unit) nondet_monad" where
  "crunch_foo3 0 x _ = crunch_foo1 x"
| "crunch_foo3 (Suc n) x y = crunch_foo3 n x y"

crunch crunch_foo3
  for gt2: "\<lambda>x. mstate x > y"

crunch crunch_foo3
  for (empty_fail) empty_fail2

(* check that simp rules can be used to solve a goal without crunching *)
crunch crunch_foo3
  for (empty_fail) empty_fail
  (ignore: crunch_foo1 simp: crunch_foo3_empty_fail2)

class foo_class =
  fixes stuff :: 'a
begin

fun crunch_foo4 :: "nat => nat => 'a => (unit, nat, unit) nondet_monad" where
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
crunch crunch_foo4
  for gt3: "\<lambda>x. mstate x > y"

crunch crunch_foo4
  for (no_fail) no_fail2
  (rule: crunch_foo4_alt)

crunch crunch_foo4
  for gt3': "\<lambda>x. mstate x > y"
  (rule: crunch_foo4_alt)

crunch crunch_foo5
  for gt4: "\<lambda>x. mstate x > y"

(* Test cases for crunch in locales *)

definition
  "crunch_foo6 \<equiv> return () >>= (\<lambda>_. return ())"

crunch_ignore (del: bind)

locale test_locale =
fixes fixed_return_unit :: "(unit, unit, unit) nondet_monad"

begin

definition
  "crunch_foo7 \<equiv> return () >>= (\<lambda>_. return ())"

(* crunch works on a global constant within a locale *)
crunch crunch_foo6
  for test[wp]: P
(ignore: bind)

(* crunch works on a locale constant *)
crunch crunch_foo7
  for test[wp]: P
(ignore: bind)

definition
  "crunch_foo8 \<equiv> fixed_return_unit >>= (\<lambda>_. fixed_return_unit)"

definition
  "crunch_foo9 (x :: nat) \<equiv> do
    modify (map_state ((+) x));
    modify (map_state ((+) x))
  od"

crunch crunch_foo9
  for test: "\<lambda>x. mstate x > y" (ignore: bind)

definition
  "crunch_foo10 (x :: nat) \<equiv> do
    modify (map_state ((+) x));
    modify (map_state ((+) x))
  od"

(*crunch_def attribute overrides definition lookup *)

lemma crunch_foo10_def2[crunch_def]:
  "crunch_foo10 = crunch_foo9"
  unfolding crunch_foo10_def[abs_def] crunch_foo9_def[abs_def]
  by simp

crunch crunch_foo10
  for test[wp]: "\<lambda>x. mstate x > y"

(* crunch_ignore works within a locale *)
crunch_ignore (add: bind)

crunch crunch_foo9
  for test': "\<lambda>x. mstate x > y"

end

interpretation test_locale "return ()" .

(* interpretation promotes the wp attribute from the locale *)
lemma "\<lbrace>Q\<rbrace> crunch_foo7 \<lbrace>\<lambda>_. Q\<rbrace>" by wp

(* crunch still works on an interpreted locale constant *)
crunch crunch_foo7
  for test2: P
  (wp_del: crunch_foo7_test)

locale test_sublocale

sublocale test_sublocale < test_locale "return ()" .

context test_sublocale begin

(* crunch works on a locale constant with a fixed locale parameter *)
crunch crunch_foo8
  for test[wp]: P

end

(* check that qualified names are handled properly. *)

consts foo_const :: "(unit, unit, unit) nondet_monad"
defs foo_const_def: "foo_const \<equiv> Crunch_Test_Qualified_NonDet.foo_const"

crunch foo_const
  for test: P

(* check that the grid-style crunch is working *)

crunch crunch_foo3, crunch_foo4, crunch_foo5
  for silly: "\<lambda>s. True \<noteq> False"
  and (no_fail) nf
  and (empty_fail) ef
  (rule: crunch_foo4_alt wp_del: hoare_vcg_prop)

(* check that crunch can use wps to lift sub-predicates
   (and also that top-level constants can be ignored) *)
consts crunch_foo11 :: "(unit, nat, unit) nondet_monad"
consts Q :: "bool \<Rightarrow> (unit, nat) monad_state \<Rightarrow> bool"
consts R :: "(unit, nat) monad_state \<Rightarrow> bool"
axiomatization
  where test1: "\<lbrace>Q x\<rbrace> crunch_foo11 \<lbrace>\<lambda>_. Q x\<rbrace>"
  and test2: "\<lbrace>\<lambda>s. P (R s)\<rbrace> crunch_foo11 \<lbrace>\<lambda>_ s. P (R s)\<rbrace>"

crunch crunch_foo11
  for test3: "\<lambda>s. Q (R s) s"
  (wp: test1 wps: test2 ignore: crunch_foo11)

(* check that crunch can handle functions lifted between different state spaces *)
record 'a state = "unit monad_state_record" +
  state' :: nat
  ext :: 'a

type_synonym 'a state_x = "('a, unit) state_ext"

definition do_nat_op :: "(unit, nat, unit) nondet_monad \<Rightarrow> (unit, 'a state_x, unit) nondet_monad" where
  "do_nat_op f \<equiv>
     do
       s \<leftarrow> get;
       (_, s') \<leftarrow> select_f (mk_ef (f (monad_state () (state' s))));
       modify (\<lambda>state. state\<lparr>state' := s'\<rparr>)
     od"

lemma do_nat_op_ef:
  "empty_fail f \<Longrightarrow> empty_fail (do_nat_op f)"
  unfolding do_nat_op_def
  apply (wpsimp wp: empty_fail_bind empty_fail_get empty_fail_select_f
              simp: mk_ef_def)
  done

lemma nf_do_nat_op:
  "no_fail P f \<Longrightarrow> empty_fail f \<Longrightarrow> no_fail (P \<circ> monad_state () \<circ> state') (do_nat_op f)"
  unfolding do_nat_op_def
  apply wpsimp
  apply (fastforce simp: mk_ef_def no_fail_def empty_fail_def)
  done

definition
  "crunch_foo12_nat (x :: nat) = modify (map_state ((+) x))"

consts wrap_ext_op :: "(unit, nat state_x, unit) nondet_monad \<Rightarrow> (unit, 'a state_x, unit) nondet_monad"
consts unwrap_ext :: "'a state \<Rightarrow> nat state"

definition do_extended_op :: "(unit, nat state_x, unit) nondet_monad \<Rightarrow> (unit, 'a state_x, unit) nondet_monad" where
  "do_extended_op eop \<equiv> do
                         ex \<leftarrow> get;
                         (_,es') \<leftarrow> select_f (mk_ef ((wrap_ext_op eop) ex));
                         modify (\<lambda>state. state\<lparr>ext := (ext (monad_state () es'))\<rparr>)
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

crunch crunch_foo12
  for (empty_fail) ef[wp]
  and (no_fail) nf
  (wp: empty_fail_bind)

(* check that other side conditions can still be collected when mixed with lifted functions*)
definition crunch_foo13_pre :: "(unit, 'a state_x, unit) nondet_monad" where
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

crunch crunch_foo13
  for (no_fail) nf

end
