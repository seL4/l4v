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
Functions to access kernel memory.
*)

chapter {* VCPU *}

theory VCPU_A
imports "../Structures_A"
begin


section "VCPU"

text {* This definition decodes VCPU invocations. *}
(*
definition
  decode_vcpu_invocation ::
  "data \<Rightarrow> data list \<Rightarrow> cap \<Rightarrow> cap list \<Rightarrow> (cnode_invocation,'z::state_ext) se_monad"
where
"decode_cnode_invocation label args cap excaps \<equiv> doE
  unlessE (invocation_type label \<in> set [CNodeRevoke .e. CNodeSaveCaller]) $
    throwError IllegalOperation;
decode_vcpu_
*)


end