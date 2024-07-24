(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)


theory MachineMonad
imports MachineTypes
begin

arch_requalify_types
  machine_state
  machine_state_rest

arch_requalify_consts
  underlying_memory
  underlying_memory_update
  device_state
  device_state_update
  irq_masks
  machine_state_rest
  machine_state_rest_update

text \<open>
  The machine monad is used for operations on the state defined above.
\<close>
type_synonym 'a machine_monad = "(machine_state, 'a) nondet_monad"

translations
  (type) "'c machine_monad" <= (type) "machine_state \<Rightarrow> ('c \<times> machine_state) set \<times> bool"

type_synonym 'a machine_rest_monad = "(machine_state_rest, 'a) nondet_monad"

definition
  machine_rest_lift :: "'a machine_rest_monad \<Rightarrow> 'a machine_monad"
where
  "machine_rest_lift f \<equiv> do
    mr \<leftarrow> gets machine_state_rest;
    (r, mr') \<leftarrow> select_f (f mr);
    modify (\<lambda>s. s \<lparr> machine_state_rest := mr' \<rparr>);
    return r
  od"


definition
  ignore_failure :: "('s,unit) nondet_monad \<Rightarrow> ('s,unit) nondet_monad"
  where
  "ignore_failure f \<equiv>
  \<lambda>s. if fst (f s) = {} then ({((),s)},False) else (fst (f s), False)"

text \<open>The wrapper doesn't do anything for usual operations:\<close>
lemma failure_consistent:
  "\<lbrakk> empty_fail f; no_fail \<top> f \<rbrakk> \<Longrightarrow> ignore_failure f = f"
  apply (simp add: ignore_failure_def empty_fail_def no_fail_def)
  apply (rule ext)
  apply (auto intro: prod_eqI)
  done

text \<open>And it has the desired properties\<close>
lemma ef_ignore_failure [simp]:
  "empty_fail (ignore_failure f)"
  by (simp add: empty_fail_def ignore_failure_def)

lemma no_fail_ignore_failure [simp, intro!]:
  "no_fail \<top> (ignore_failure f)"
  by (simp add: no_fail_def ignore_failure_def)


lemma ef_machine_rest_lift [simp, intro!]:
  "empty_fail f \<Longrightarrow> empty_fail (machine_rest_lift f)"
  apply (clarsimp simp: empty_fail_def machine_rest_lift_def simpler_gets_def
                        select_f_def bind_def simpler_modify_def return_def)
  apply force
  done

lemma no_fail_machine_state_rest [intro!]:
  "no_fail P f \<Longrightarrow> no_fail (P o machine_state_rest) (machine_rest_lift f)"
  apply (simp add: no_fail_def machine_rest_lift_def simpler_gets_def
                        select_f_def bind_def simpler_modify_def return_def)
  apply force
  done

lemma no_fail_machine_state_rest_T [simp, intro!]:
  "no_fail \<top> f \<Longrightarrow> no_fail \<top> (machine_rest_lift f)"
  apply (drule no_fail_machine_state_rest)
  apply (simp add: o_def)
  done

definition
  "machine_op_lift \<equiv> machine_rest_lift o ignore_failure"


end
