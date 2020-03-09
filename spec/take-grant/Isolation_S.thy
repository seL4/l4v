(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Isolation_S
imports Islands_S
begin

definition
  set_flow :: "state \<Rightarrow> (entity_id set \<times> entity_id set) set" where
  "set_flow s \<equiv> {(X,Y). \<exists>x \<in> X. \<exists>y \<in> Y.
                        (read_cap x \<in>cap caps_of s y \<or>
                        write_cap y \<in>cap caps_of s x)}"

lemma set_flow_def2:
  "(X, Y) \<in> set_flow s = (\<exists>x \<in> X. \<exists>y \<in> Y.
                        (read_cap x \<in>cap caps_of s y \<or>
                        write_cap y \<in>cap caps_of s x))"
  by (simp add: set_flow_def)

definition
  flow :: "state \<Rightarrow> (entity_id \<times> entity_id) set" where
  "flow s \<equiv>  {(x,y). (island s x, island s y) \<in> set_flow s}"

lemma flow_def2:
  "(x, y) \<in> flow s = ((island s x, island s y) \<in> set_flow s)"
  by (simp add: flow_def)


abbreviation
  in_flow :: "state \<Rightarrow> entity_id \<Rightarrow> entity_id \<Rightarrow> bool" ("_ \<turnstile> _ \<leadsto> _" [60,0,60] 61)
where
  "s \<turnstile> x \<leadsto> y \<equiv> (x,y) \<in> flow s"

definition
  flow_trans :: "state \<Rightarrow> (entity_id \<times> entity_id) set" ("flow\<^sup>*") where
  "flow_trans s \<equiv> (flow s)\<^sup>*"

abbreviation
  in_flow_trans :: "state \<Rightarrow> entity_id \<Rightarrow> entity_id \<Rightarrow> bool" ("_ \<turnstile> _ \<leadsto>* _" [60,0,60] 61)
where
  "s \<turnstile> x \<leadsto>* y == (x,y) \<in> flow_trans s"

notation (latex output)
  in_flow_trans ("_ \<turnstile> _ \<leadsto>\<^sup>* _" [60,0,60] 61)

translations
  "\<not> (s \<turnstile> x \<leadsto> y)" <= "(x,y) \<notin> CONST flow s"
  "\<not> (s \<turnstile> x \<leadsto>* y)" <= "(x,y) \<notin> CONST flow_trans s"


(* Proof *)
lemma rights_extra_rights_read_cap [simp]:
  "rights (extra_rights (read_cap e)) = {Read}"
  by (simp add: rights_extra_rights)

lemma rights_extra_rights_write_cap [simp]:
  "rights (extra_rights (write_cap e)) = {Write}"
  by (simp add: rights_extra_rights)

lemma flow_trans_refl [simp]:
  "s \<turnstile> x \<leadsto>* x"
  by (metis flow_trans_def rtrancl.rtrancl_refl)

lemma flow_connected_step:
  "\<lbrakk>s' \<turnstile> x \<leadsto>* y; s' \<in> step cmd s\<rbrakk> \<Longrightarrow>
    s \<turnstile> x \<leadsto>* y"
  apply (erule rtrancl_induct [where r="flow s'",
                              simplified flow_trans_def[symmetric]])
   apply simp
  apply (subgoal_tac "s \<turnstile> y \<leadsto> z")
   apply (fastforce simp: flow_trans_def rtrancl.rtrancl_into_rtrancl)
  apply (clarsimp simp: flow_def island_def set_flow_def)
  apply (frule_tac x=y in tgs_connected_preserved_step, simp)
  apply (frule_tac x=z in tgs_connected_preserved_step, simp)
  apply (clarsimp simp: cap_in_caps_def)
  apply (erule disjE)
   apply clarsimp
   apply (drule (1) caps_of_op)
   apply (clarsimp simp: cap_in_caps_def)
   apply (metis (no_types) tgs_connected_trans subsetD)
  apply clarsimp
  apply (drule (1) caps_of_op)
  apply (clarsimp simp: cap_in_caps_def)
  apply (metis (no_types) tgs_connected_trans subsetD)
  done

lemma flow_connected [rule_format]:
  "\<forall>s'.  s' \<in> execute cmds s \<longrightarrow>
    s' \<turnstile> x \<leadsto>* y \<longrightarrow>
    s \<turnstile> x \<leadsto>* y"
  apply (induct_tac cmds, simp)
  apply clarsimp
  apply (drule (1) flow_connected_step)
  apply auto
  done

lemma information_flow:
  "\<lbrakk>s' \<in> execute cmds s;
  \<not> s \<turnstile> x \<leadsto>* y\<rbrakk> \<Longrightarrow>
  \<not> s' \<turnstile> x \<leadsto>* y"
  by (auto simp: flow_connected)

end
