(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory CLanguage
imports "CProof"
begin

definition
  creturn :: "((c_exntype \<Rightarrow> c_exntype) \<Rightarrow> ('c, 'd) state_scheme \<Rightarrow> ('c, 'd) state_scheme)
      \<Rightarrow> (('a \<Rightarrow> 'a) \<Rightarrow> ('c, 'd) state_scheme \<Rightarrow> ('c, 'd) state_scheme)
      \<Rightarrow> (('c, 'd) state_scheme \<Rightarrow> 'a) \<Rightarrow> (('c, 'd) state_scheme,'p,'f) com"
where
  "creturn rtu xfu v \<equiv> (Basic (\<lambda>s. xfu (\<lambda>_. v s) s);; (Basic (rtu (\<lambda>_. Return));; THROW))"

definition
  creturn_void :: "((c_exntype \<Rightarrow> c_exntype) \<Rightarrow> ('c, 'd) state_scheme
      \<Rightarrow> ('c, 'd) state_scheme) \<Rightarrow> (('c, 'd) state_scheme,'p,'f) com"
where
  "creturn_void rtu \<equiv> (Basic (rtu (\<lambda>_. Return));; THROW)"

definition
  cbreak :: "((c_exntype \<Rightarrow> c_exntype) \<Rightarrow> ('c, 'd) state_scheme
      \<Rightarrow> ('c, 'd) state_scheme) \<Rightarrow> (('c, 'd) state_scheme,'p,'f) com"
where
  "cbreak rtu \<equiv> (Basic (rtu (\<lambda>_. Break));; THROW)"

definition
  ccatchbrk :: "( ('c, 'd) state_scheme \<Rightarrow> c_exntype) \<Rightarrow> (('c, 'd) state_scheme,'p,'f) com"
where
  "ccatchbrk rt \<equiv> Cond {s. rt s = Break} SKIP THROW"

definition
  cchaos :: "('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a,'c,'d) com"
where
  "cchaos upd \<equiv> Spec { (s0,s) . \<exists>v. s = upd v s0 }"

definition
  "guarded_spec_body F R = Guard F (fst ` R) (Spec R)"

text \<open>
  Uninterpreted function for expressing the semantics of external functions. Used for
  DONT_TRANSLATE functions that have a MODIFIES annotation. @{text extern_semantics} takes
  the function name, the function arguments as a tuple, and the global state, and returns
  a set of pairs with result and a new global state. Generally, each function will use different
  type instances for @{text 'a} and @{text 'r}. The function can be defined or constrained
  later if desired.\<close>
consts extern_semantics :: "string \<Rightarrow> 'a \<Rightarrow> 'g \<Rightarrow> ('r \<times> 'g) set"

text \<open>
  The full body of such an external function. @{text M} is the relation that comes out of the
  MODIFIES annotation. @{text X} is @{const extern_semantics} applied to a specific function call.
  The body is written to never be empty, so the @{const Spec} semantics cannot be @{const Stuck} and
  modifies proofs can remain automatic and always prove @{text M}.
  Usual use cases should have @{term "X \<subseteq> M"}.\<close>
definition extern_spec_body :: "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<times> 's) set \<Rightarrow> ('s,'p,'f) com" where
  "extern_spec_body M X \<equiv>
     Spec {(s,t). M s t \<and> ((s,t) \<in> X \<or> (\<forall>t'. M s t' \<longrightarrow> (s,t') \<notin> X))}"

end
