(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(* 
Monad instantiations, handling of faults, errors, and interrupts.
*)

chapter "Basic Kernel and Exception Monads"

theory Exceptions_A
imports Deterministic_A
begin

text {* This theory contains abbreviations for the monadic types used
in the specification and a number of lifting functions between them. *}

text {* The basic kernel monad without faults, interrupts, or errors. *}
type_synonym ('a,'z) s_monad = "('z state, 'a) nondet_monad"

text {* The fault monad: may throw a @{text fault} exception which
will usually be reported to the current thread's fault handler. *}
type_synonym ('a,'z) f_monad = "(fault + 'a,'z) s_monad"

term "a::(unit,'a) s_monad"

text {* The error monad: may throw a @{text syscall_error} exception
which will usually be reported to the current thread as system call 
result. *}
type_synonym ('a,'z) se_monad = "(syscall_error + 'a,'z) s_monad"

text {* The lookup failure monad: may throw a @{text lookup_failure}
exception. Depending on context it may either be reported directly to
the current thread or to its fault handler.
*}
type_synonym ('a,'z) lf_monad = "(lookup_failure + 'a,'z) s_monad"

text {* The preemption monad. May throw an interrupt exception. *}
type_synonym ('a,'z) p_monad = "(interrupt + 'a,'z) s_monad"


text {*
  Printing abbreviations for the above types.
*}
translations 
  (type) "'a s_monad" <= (type) "state \<Rightarrow> (('a \<times> state) \<Rightarrow> bool) \<times> bool"
  (type) "'a f_monad" <= (type) "(fault + 'a) s_monad"
  (type) "'a se_monad" <= (type) "(syscall_error + 'a) s_monad"
  (type) "'a lf_monad" <= (type) "(lookup_failure + 'a) s_monad"
  (type) "'a p_monad" <=(type) "(interrupt + 'a) s_monad"

text {* Perform non-preemptible operations within preemptible blocks. *}
definition
  without_preemption :: "('a,'z::state_ext) s_monad \<Rightarrow> ('a,'z::state_ext) p_monad" 
where without_preemption_def[simp]:
 "without_preemption \<equiv> liftE"

text {* Allow preemption at this point. *}
definition
  preemption_point :: "(unit,'z::state_ext) p_monad" where
 "preemption_point \<equiv> doE liftE $ do_extended_op update_work_units;
                         OR_choiceE (work_units_limit_reached)
                           (doE liftE $ do_extended_op reset_work_units;
                                irq_opt \<leftarrow> liftE $ do_machine_op (getActiveIRQ True);
                                case_option (returnOk ()) (throwError \<circ> Interrupted) irq_opt
                           odE) (returnOk ())
                     odE"

text {* Lift one kind of exception monad into another by converting the error
into various other kinds of error or return value. *}
definition
  cap_fault_on_failure :: "obj_ref \<Rightarrow> bool \<Rightarrow> ('a,'z::state_ext) lf_monad \<Rightarrow> ('a,'z::state_ext) f_monad" where
 "cap_fault_on_failure cptr rp m \<equiv> handleE' m (throwError \<circ> CapFault cptr rp)"

definition
  lookup_error_on_failure ::  "bool \<Rightarrow> ('a,'z::state_ext) lf_monad \<Rightarrow> ('a,'z::state_ext) se_monad" where
 "lookup_error_on_failure s m \<equiv> handleE' m (throwError \<circ> FailedLookup s)"

definition
  null_cap_on_failure :: "(cap,'z::state_ext) lf_monad \<Rightarrow> (cap,'z::state_ext) s_monad" where
 "null_cap_on_failure \<equiv> liftM (case_sum (\<lambda>x. NullCap) id)"

definition
  unify_failure :: "('f + 'a,'z::state_ext) s_monad \<Rightarrow> (unit + 'a,'z::state_ext) s_monad" where
 "unify_failure m \<equiv> handleE' m (\<lambda>x. throwError ())"

definition
  empty_on_failure :: "('f + 'a list,'z::state_ext) s_monad \<Rightarrow> ('a list,'z::state_ext) s_monad" where
 "empty_on_failure m \<equiv> m <catch> (\<lambda>x. return [])"

definition
  const_on_failure :: "'a \<Rightarrow> ('f + 'a,'z::state_ext) s_monad \<Rightarrow> ('a,'z::state_ext) s_monad" where
 "const_on_failure c m \<equiv> m <catch> (\<lambda>x. return c)"

text {* Checks whether first argument is between second and third (inclusive). *}

definition
  range_check :: "machine_word \<Rightarrow> machine_word \<Rightarrow> machine_word \<Rightarrow> (unit,'z::state_ext) se_monad"
where
  "range_check v min_v max_v \<equiv>
    unlessE (v \<ge> min_v \<and> v \<le> max_v) $ throwError $ RangeError min_v max_v"

end
