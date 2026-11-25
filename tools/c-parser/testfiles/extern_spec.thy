(*
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory extern_spec
imports "CParser.CTranslation"
begin

(* Toy machine state *)
type_synonym regs = "32 word \<Rightarrow> 32 word"

external_file "extern_spec.c"
install_C_file "extern_spec.c" [machinety=regs]


section \<open>Generated bodies\<close>

context extern_spec
begin

(* extern_spec/extern_semantics bodies *)
lemma
  "read_reg_body \<equiv>
     extern_spec_body
       (\<lambda>s t. t may_not_modify_globals s)
       {(s, t). (ret__unsigned_' t, globals t) \<in> extern_semantics ''read_reg'' (r_' s) (globals s)}"
  by (fact read_reg_body_def)

lemma
  "write_reg_body \<equiv>
     extern_spec_body
       (\<lambda>s t. t may_only_modify_globals s in [phantom_machine_state])
       {(s, t). ((), globals t) \<in> extern_semantics ''write_reg'' (r_' s, v_' s) (globals s)}"
  by (fact write_reg_body_def)

lemma
  "update_x_body \<equiv>
     extern_spec_body
       (\<lambda>s t. t may_only_modify_globals s in [x])
       {(s, t). (ret__int_' t, globals t) \<in> extern_semantics ''update_x'' (a_' s) (globals s)}"
  by (fact update_x_body_def)

lemma
  "tick_body \<equiv>
     extern_spec_body
       (\<lambda>s t. t may_only_modify_globals s in [phantom_machine_state])
       {(s, t). ((), globals t) \<in> extern_semantics ''tick'' () (globals s)}"
  by (fact tick_body_def)

(* Modifies theorems of external functions and their callers are as always *)
thm read_reg_modifies
thm write_reg_modifies
thm update_x_modifies
thm tick_modifies
thm swap_reg_modifies
thm bump_modifies

(* Has FNSPEC, therefore no extern_spec_body *)
thm magic_body_def

end


section \<open>Reasoning from @{text MODIFIES} only\<close>

context extern_spec
begin

(* By default we know nothing about extern_semantics, so the default vcg rule only uses the
   MODIFIES annotation *)
lemma update_x_y:
  "\<Gamma> \<turnstile> \<lbrace>\<acute>y = n\<rbrace> \<acute>ret__int :== PROC update_x(\<acute>a) \<lbrace>\<acute>y = n\<rbrace>"
  apply vcg
  apply (fastforce simp: meq_def mex_def)
  done

lemma bump_y:
  "\<Gamma> \<turnstile> \<lbrace>\<acute>a = n\<rbrace> \<acute>ret__int :== PROC bump(\<acute>a) \<lbrace>\<acute>y = n\<rbrace>"
  apply vcg
  apply (fastforce simp: meq_def mex_def)
  done

end


section \<open>Reasoning with assumptions about the semantics\<close>

(* Since extern_semantics is uninterpreted, we can make further assumptions: *)
locale extern_spec_sem = extern_spec +
  (* reads state *)
  assumes read_reg_sem:
    "\<And>r (g::globals). extern_semantics ''read_reg'' r g = {(phantom_machine_state_' g r, g)}"
  (* changes state *)
  assumes write_reg_sem:
    "\<And>r v (g::globals).
       extern_semantics ''write_reg'' (r, v) g =
         {((), g\<lparr>phantom_machine_state_' := (phantom_machine_state_' g)(r := v)\<rparr>)}"
  (* usable only under additional assumption like a \<noteq> 0 *)
  assumes update_x_sem:
    "\<And>a (g::globals). a \<noteq> 0 \<Longrightarrow> extern_semantics ''update_x'' a g = {(x_' g, g\<lparr>x_' := a\<rparr>)}"
begin

(* Proving the spec rule requires us to reason about enabledness so that we can make use of more
   than just the MODIFIES part *)
lemma read_reg_spec:
  "\<forall>\<sigma>. \<Gamma> \<turnstile> {\<sigma>}
           \<acute>ret__unsigned :== PROC read_reg(\<acute>r)
           \<lbrace>\<acute>ret__unsigned = \<^bsup>\<sigma>\<^esup>phantom_machine_state \<^bsup>\<sigma>\<^esup>r\<rbrace>"
  apply (rule allI)
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (rule extern_spec_body_enabled_wp)
  apply (clarsimp simp: read_reg_sem meq_def)
  apply (rule_tac x="\<sigma>\<lparr>ret__unsigned_' := phantom_machine_state_' (globals \<sigma>) (r_' \<sigma>)\<rparr>" in exI)
  apply simp
  done

lemma write_reg_spec:
  "\<forall>\<sigma>. \<Gamma> \<turnstile> {\<sigma>}
           PROC write_reg(\<acute>r, \<acute>v)
           \<lbrace>\<acute>phantom_machine_state = (\<^bsup>\<sigma>\<^esup>phantom_machine_state)(\<^bsup>\<sigma>\<^esup>r := \<^bsup>\<sigma>\<^esup>v)\<rbrace>"
  supply [[simproc add: ex_sel_eq]]
  apply (rule allI)
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (rule extern_spec_body_enabled_wp)
  apply (simp add: write_reg_sem meq_def mex_def fun_upd_def cong: rev_conj_cong)
  apply fastforce
  done

(* Now available automatically *)
lemma swap_reg_spec:
  "\<Gamma> \<turnstile> \<lbrace>\<acute>phantom_machine_state = regs \<and> \<acute>r = reg \<and> \<acute>v = val\<rbrace>
       \<acute>ret__unsigned :== PROC swap_reg(\<acute>r, \<acute>v)
       \<lbrace>\<acute>ret__unsigned = regs reg \<and> \<acute>phantom_machine_state = regs(reg := val)\<rbrace>"
  by vcg (fastforce simp: meq_def mex_def)

(* Explicit reasoning about enabledness with an extra assumption *)
lemma update_x_enabled:
  "a_' (s::globals myvars) \<noteq> 0 \<Longrightarrow>
   \<exists>t::globals myvars.
     t may_only_modify_globals s in [x] \<and>
     (ret__int_' t, globals t) \<in> extern_semantics ''update_x'' (a_' s) (globals s)"
  apply (rule_tac x="s\<lparr>ret__int_' := x_' (globals s), globals := (globals s)\<lparr>x_' := a_' s\<rparr>\<rparr>" in exI)
  apply (simp add: update_x_sem meq_def mex_def)
  apply (rule exI, rule refl)
  done

lemma update_x_spec:
  "\<forall>\<sigma>. \<Gamma> \<turnstile> {\<sigma>}
           \<acute>ret__int :== PROC update_x(\<acute>a)
           \<lbrace>\<^bsup>\<sigma>\<^esup>a \<noteq> 0 \<longrightarrow> \<acute>ret__int = \<^bsup>\<sigma>\<^esup>x \<and> \<acute>x = \<^bsup>\<sigma>\<^esup>a\<rbrace>"
  apply (rule allI)
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (rule extern_spec_body_wp)
  apply (clarsimp simp del: word_neq_0_conv)
  apply (rule conjI)
   apply (fastforce simp: update_x_sem simp del: word_neq_0_conv dest: update_x_enabled)
  apply (rule_tac x=\<sigma> in exI)
  apply (simp add: meq_def mex_def)
  apply (rule_tac x="x_' (globals \<sigma>)" in exI)
  apply simp
  done

(* Uses "update_x" which has a spec rule now, and "tick" which has only MODIFIES *)
lemma bump_spec:
  "\<Gamma> \<turnstile> \<lbrace>\<acute>a = n \<and> n \<noteq> 0 \<and> \<acute>x = m\<rbrace> \<acute>ret__int :== PROC bump(\<acute>a) \<lbrace>\<acute>ret__int = m \<and> \<acute>x = n \<and> \<acute>y = n\<rbrace>"
  by vcg (fastforce simp: meq_def mex_def)

end


section \<open>Using a definition instead of assumptions\<close>

(* We can provide an explicit definition for extern_semantics. Since it uses different type
   instances for different functions, we need overloading. *)
overloading
  extern_semantics_read_reg \<equiv>
    "extern_semantics :: string \<Rightarrow> 32 word \<Rightarrow> globals \<Rightarrow> (32 word \<times> globals) set"
  extern_semantics_write_reg \<equiv>
    "extern_semantics :: string \<Rightarrow> 32 word \<times> 32 word \<Rightarrow> globals \<Rightarrow> (unit \<times> globals) set"
  extern_semantics_update_x \<equiv>
    "extern_semantics :: string \<Rightarrow> 32 signed word \<Rightarrow> globals \<Rightarrow> (32 signed word \<times> globals) set"
begin

(* reads state *)
definition extern_semantics_read_reg ::
  "string \<Rightarrow> 32 word \<Rightarrow> globals \<Rightarrow> (32 word \<times> globals) set" where
  "extern_semantics_read_reg name r g \<equiv>
     if name = ''read_reg'' then {(phantom_machine_state_' g r, g)} else UNIV"

(* changes state *)
definition extern_semantics_write_reg ::
  "string \<Rightarrow> 32 word \<times> 32 word \<Rightarrow> globals \<Rightarrow> (unit \<times> globals) set" where
  "extern_semantics_write_reg name args g \<equiv>
     if name = ''write_reg''
     then case args of
            (r, v) \<Rightarrow> {((), g\<lparr>phantom_machine_state_' := (phantom_machine_state_' g)(r := v)\<rparr>)}
     else UNIV"

(* constrained for a \<noteq> 0 *)
definition extern_semantics_update_x ::
  "string \<Rightarrow> 32 signed word \<Rightarrow> globals \<Rightarrow> (32 signed word \<times> globals) set" where
  "extern_semantics_update_x name a g \<equiv>
     if name = ''update_x'' \<and> a \<noteq> 0 then {(x_' g, g\<lparr>x_' := a\<rparr>)} else UNIV"

end

(* The definitions satisfy the assumptions of extern_spec_sem, so everything proved there is now
   available in extern_spec without further assumptions. *)
sublocale extern_spec \<subseteq> extern_spec_sem
  by unfold_locales
     (auto simp: extern_semantics_read_reg_def extern_semantics_write_reg_def
                 extern_semantics_update_x_def)

context extern_spec
begin

thm read_reg_spec write_reg_spec update_x_spec
thm swap_reg_spec bump_spec

end


end
