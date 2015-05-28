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
Accessor functions for capability spaces.
*)

chapter "Accessing CSpace"

theory CSpaceAcc_A
imports KHeap_A
begin

text {* 
This theory contains basic definitions for manipulating capabilities and
CDTs.
*}

section {* Capability access *}

text {*
 Recall that a capability may reside in either a CNode, or inside a TCB; 
the following definitions allow the kernel model to retrieve and update
capabilities in a uniform fashion.*}
definition
  get_cap :: "cslot_ptr \<Rightarrow> (cap,'z::state_ext) s_monad"
where
  "get_cap \<equiv> \<lambda>(oref, cref). do
     obj \<leftarrow> get_object oref;
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
     obj \<leftarrow> get_object oref;
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
     set_object oref obj'
  od"

text {* Ensure a capability slot is empty. *}
definition
  ensure_empty :: "cslot_ptr \<Rightarrow> (unit,'z::state_ext) se_monad"
where
  "ensure_empty slot \<equiv> doE
    cap \<leftarrow> liftE $ get_cap slot;
    whenE (cap \<noteq> NullCap) (throwError DeleteFirst)
  odE"

section {* Accessing the capability derivation tree *}

text {* Set the capability derivation tree. *}
definition
  set_cdt :: "cdt \<Rightarrow> (unit,'z::state_ext) s_monad"
  where
  "set_cdt t \<equiv> do 
    s \<leftarrow> get; 
    put $ s\<lparr> cdt := t \<rparr> 
  od"

text {* Update the capability derivation tree. *}
definition
  update_cdt :: "(cdt \<Rightarrow> cdt) \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "update_cdt f \<equiv> do 
     t \<leftarrow> gets cdt;
     set_cdt (f t)
  od"

text {* Set the original flag for a given cap slot. *}
definition
  set_original :: "cslot_ptr \<Rightarrow> bool \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "set_original slot v \<equiv> do 
     r \<leftarrow> gets is_original_cap;
     modify (\<lambda>s. s \<lparr> is_original_cap := r (slot := v) \<rparr>)
  od"

text {* Definitions and syntax for predicates on capability derivation. *}
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

text {* The set of descendants of a particular slot in the CDT. *}
definition
  descendants_of :: "cslot_ptr \<Rightarrow> cdt \<Rightarrow> cslot_ptr set" where
  "descendants_of p t \<equiv> {q. (p,q) \<in> (cdt_parent_rel t)\<^sup>+}"

end
