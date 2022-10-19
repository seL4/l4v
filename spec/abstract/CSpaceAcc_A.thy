(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Accessor functions for capability spaces.
*)

chapter "Accessing CSpace"

theory CSpaceAcc_A
imports KHeap_A
begin

text \<open>
This theory contains basic definitions for manipulating capabilities and
CDTs.
\<close>

section \<open>Capability access\<close>

text \<open>
 Recall that a capability may reside in either a CNode, or inside a TCB;
the following definitions allow the kernel model to retrieve and update
capabilities in a uniform fashion.\<close>
definition
  get_cap :: "bool \<Rightarrow> cslot_ptr \<Rightarrow> (cap,'z::state_ext) s_monad"
where
  "get_cap ta_f \<equiv> \<lambda>(oref, cref). do
     obj \<leftarrow> get_object ta_f oref;
     caps \<leftarrow> case obj of
             CNode sz cnode \<Rightarrow> do
                                assert (well_formed_cnode_n sz cnode);
                                return cnode
                              od
           | TCB tcb     \<Rightarrow> return (tcb_cnode_map tcb)
           | _ \<Rightarrow> fail;
     assert_opt (caps cref)
   od"

definition
  set_cap :: "cap \<Rightarrow> cslot_ptr \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "set_cap cap \<equiv> \<lambda>(oref, cref). do
     obj \<leftarrow> get_object True oref;
     obj' \<leftarrow> case obj of
               CNode sz cn \<Rightarrow> if cref \<in> dom cn \<and> well_formed_cnode_n sz cn
                                then return $ CNode sz $ cn (cref \<mapsto> cap)
                                else fail
             | TCB tcb \<Rightarrow>
                   if cref = tcb_cnode_index 0 then
                       return $ TCB $ tcb \<lparr> tcb_ctable := cap \<rparr>
                   else if cref = tcb_cnode_index 1 then
                       return $ TCB $ tcb \<lparr> tcb_vtable := cap \<rparr>
                   else if cref = tcb_cnode_index 2 then
                       return $ TCB $ tcb \<lparr> tcb_reply := cap \<rparr>
                   else if cref = tcb_cnode_index 3 then
                       return $ TCB $ tcb \<lparr> tcb_caller := cap \<rparr>
                   else if cref = tcb_cnode_index 4 then
                       return $ TCB $ tcb \<lparr> tcb_ipcframe := cap \<rparr>
                   else
                       fail
             | _ \<Rightarrow> fail;
     set_object True oref obj'
  od"

text \<open>Ensure a capability slot is empty.\<close>
definition
  ensure_empty :: "cslot_ptr \<Rightarrow> (unit,'z::state_ext) se_monad"
where
  "ensure_empty slot \<equiv> doE
    liftE $ touch_object (fst slot);
    cap \<leftarrow> liftE $ get_cap True slot;
    whenE (cap \<noteq> NullCap) (throwError DeleteFirst)
  odE"

section \<open>Accessing the capability derivation tree\<close>

text \<open>Set the capability derivation tree.\<close>
definition
  set_cdt :: "cdt \<Rightarrow> (unit,'z::state_ext) s_monad"
  where
  "set_cdt t \<equiv> do
    s \<leftarrow> get;
    put $ s\<lparr> cdt := t \<rparr>
  od"

text \<open>Update the capability derivation tree.\<close>
definition
  update_cdt :: "(cdt \<Rightarrow> cdt) \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "update_cdt f \<equiv> do
     t \<leftarrow> gets cdt;
     set_cdt (f t)
  od"

text \<open>Set the original flag for a given cap slot.\<close>
definition
  set_original :: "cslot_ptr \<Rightarrow> bool \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "set_original slot v \<equiv> do
     r \<leftarrow> gets is_original_cap;
     modify (\<lambda>s. s \<lparr> is_original_cap := r (slot := v) \<rparr>)
  od"

text \<open>Definitions and syntax for predicates on capability derivation.\<close>
definition
  is_cdt_parent :: "cdt \<Rightarrow> cslot_ptr \<Rightarrow> cslot_ptr \<Rightarrow> bool" where
  "is_cdt_parent t p c \<equiv> t c = Some p"

definition
  cdt_parent_rel :: "cdt \<Rightarrow> (cslot_ptr \<times> cslot_ptr) set" where
  "cdt_parent_rel t \<equiv> {(p,c). is_cdt_parent t p c}"

abbreviation
  parent_of :: "cdt \<Rightarrow> cslot_ptr \<Rightarrow> cslot_ptr \<Rightarrow> bool"
  ("_ \<turnstile> _ cdt'_parent'_of _" [60,0,60] 61)
where
  "t \<turnstile> p cdt_parent_of c \<equiv> (p,c) \<in> cdt_parent_rel t"

abbreviation
  parent_of_trancl :: "cdt \<Rightarrow> cslot_ptr \<Rightarrow> cslot_ptr \<Rightarrow> bool"
  ("_ \<turnstile> _ cdt'_parent'_of\<^sup>+ _" [60,0,60] 61)
where
  "t \<turnstile> x cdt_parent_of\<^sup>+ y \<equiv> (x, y) \<in> (cdt_parent_rel t)\<^sup>+"

abbreviation
  parent_of_rtrancl :: "cdt \<Rightarrow> cslot_ptr \<Rightarrow> cslot_ptr \<Rightarrow> bool"
  ("_ \<turnstile> _ cdt'_parent'_of\<^sup>* _" [60,0,60] 61)
where
  "t \<turnstile> x cdt_parent_of\<^sup>* y \<equiv> (x, y) \<in> (cdt_parent_rel t)\<^sup>*"


notation
  parent_of ("_ \<Turnstile> _ \<leadsto> _" [60,0,60] 60)
and
  parent_of_trancl ("_ \<Turnstile> _ \<rightarrow> _" [60,0,60] 60)
and
  parent_of_rtrancl ("_ \<Turnstile> _ \<rightarrow>* _" [60,0,60] 60)

text \<open>The set of descendants of a particular slot in the CDT.\<close>
definition
  descendants_of :: "cslot_ptr \<Rightarrow> cdt \<Rightarrow> cslot_ptr set" where
  "descendants_of p t \<equiv> {q. (p,q) \<in> (cdt_parent_rel t)\<^sup>+}"

end
