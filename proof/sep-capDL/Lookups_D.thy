(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Lookups_D
imports
  "DSpec.Syscall_D"
  "Monads.Nondet_Reader_Option"
begin

type_synonym 'a lookup = "cdl_state \<Rightarrow> 'a option"

definition
  opt_cnode :: "cdl_object_id \<Rightarrow> cdl_cnode lookup"
where
  "opt_cnode p \<equiv> DO
      t \<leftarrow> \<lambda>s. cdl_objects s p;
      case t of
        CNode cnode \<Rightarrow> oreturn cnode
      | _ \<Rightarrow> ofail
   OD"

function resolve_cap ::
  "cdl_cap \<Rightarrow> cdl_cptr \<Rightarrow> nat \<Rightarrow> (cdl_fault_error + cdl_cap_ref \<times> nat) lookup"
where
  "resolve_cap cnode_cap cap_ptr remaining_size =
  (if is_cnode_cap cnode_cap
  then DO
    \<comment> \<open>Fetch the next level CNode.\<close>
    cnode \<leftarrow> opt_cnode $ cap_object cnode_cap;
    radix_size \<leftarrow> oreturn $ cdl_cnode_size_bits cnode;
    guard_size \<leftarrow> oreturn $ cap_guard_size cnode_cap;
    cap_guard  \<leftarrow> oreturn $ cap_guard cnode_cap;
    level_size \<leftarrow> oreturn (radix_size + guard_size);
    oassert (level_size \<noteq> 0);

    \<comment> \<open>Ensure the guard matches up.\<close>
    guard \<leftarrow> oreturn $ (cap_ptr >> (remaining_size-guard_size)) && (mask guard_size);
    if \<not>(guard_size \<le> remaining_size \<and> guard = cap_guard) \<or>
       level_size > remaining_size
    then othrow FaultError
    else DO
      \<comment> \<open>Find the next slot.\<close>
      offset \<leftarrow> oreturn $ (cap_ptr >> (remaining_size-level_size)) && (mask radix_size);
      slot \<leftarrow> oreturn (cap_object cnode_cap, unat offset);
      size_left \<leftarrow> oreturn (remaining_size - level_size);
      if size_left = 0 then
        oreturnOk (slot, 0)
      else DO
        next_cap \<leftarrow> opt_cap slot;
        if is_cnode_cap next_cap then
          resolve_cap next_cap cap_ptr size_left
        else
          oreturnOk (slot, size_left)
      OD
    OD
  OD
  else othrow FaultError)"
  by auto

termination
  by (relation "measure (\<lambda>(a,b,c). c)") auto

declare resolve_cap.simps [simp del]

declare resolve_address_bits.simps [simp del]

lemma throwError_FaultError [simp]:
  "throwError FaultError = throw"
  apply (cases "undefined::cdl_fault_error")
  apply simp
  done

lemma gets_the_get_cnode:
  "gets_the (opt_cnode r) = get_cnode r"
  apply (simp add: get_cnode_def opt_cnode_def)
  apply (rule bind_cong, rule refl)
  apply (clarsimp split: cdl_object.splits)
  done

lemma gets_the_resolve_cap:
  "gets_the (resolve_cap cnode_cap cap_ptr remaining_size) =
   resolve_address_bits cnode_cap cap_ptr remaining_size"
  apply (induct cnode_cap cap_ptr remaining_size rule: resolve_cap.induct [simplified])
  apply (subst resolve_cap.simps)
  apply (subst resolve_address_bits.simps)
  apply (clarsimp simp: unlessE_def liftE_bindE assertE_liftE gets_the_get_cnode)
  apply (rule bind_cong, rule refl)
  apply (rule bind_apply_cong, rule refl)
  apply (clarsimp simp: liftE_bindE)
  apply (rule bind_apply_cong, rule refl)
  apply (clarsimp simp: in_monad gets_the_get_cnode [symmetric])
  done

end
