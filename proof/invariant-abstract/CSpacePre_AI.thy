(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
CSpace invariants preamble
*)

theory CSpacePre_AI
imports ArchCSpaceInv_AI
begin

context begin interpretation Arch .
requalify_consts
  cap_asid
  is_simple_cap_arch
  is_derived_arch
  safe_parent_for_arch
  cap_asid_base
  cap_vptr
end

lemma fun_upd_Some:
  "ms p = Some k \<Longrightarrow> (ms(a \<mapsto> b)) p = Some (if a = p then b else k)"
  by auto


lemma fun_upd_Some_rev:
  "\<lbrakk>ms a = Some k; (ms(a \<mapsto> b)) p = Some cap\<rbrakk>
   \<Longrightarrow> ms p = Some (if a = p then k else cap)"
  by auto

lemma P_bool_lift':
  "\<lbrakk>\<lbrace>Q and Q'\<rbrace> f \<lbrace>\<lambda>r. Q\<rbrace>; \<lbrace>(\<lambda>s. \<not> Q s) and Q'\<rbrace> f \<lbrace>\<lambda>r s. \<not> Q s\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s. P (Q s) \<and> Q' s\<rbrace> f \<lbrace>\<lambda>r s. P (Q s)\<rbrace>"
  apply (clarsimp simp:valid_def)
  apply (elim allE)
  apply (case_tac "Q s")
    apply fastforce+
  done

lemma free_index_update_simps[simp]:
  "free_index_update g (cap.UntypedCap dev ref sz f) = cap.UntypedCap dev ref sz (g f)"
   by (simp add:free_index_update_def)

(* FIXME: MOVE*)
lemma is_cap_free_index_update[simp]:
  "is_zombie (src_cap\<lparr>free_index := f \<rparr>) = is_zombie src_cap"
  "is_cnode_cap (src_cap\<lparr>free_index := f \<rparr>) = is_cnode_cap src_cap"
  "is_thread_cap (src_cap\<lparr>free_index := f \<rparr>) = is_thread_cap src_cap"
  "is_domain_cap (src_cap\<lparr>free_index := f \<rparr>) = is_domain_cap src_cap"
  "is_ep_cap (src_cap\<lparr>free_index := f \<rparr>) = is_ep_cap src_cap"
  "is_untyped_cap (src_cap\<lparr>free_index := f \<rparr>) = is_untyped_cap src_cap"
  "is_arch_cap (src_cap\<lparr>free_index := f \<rparr>) = is_arch_cap src_cap"
  "is_ntfn_cap (src_cap\<lparr>free_index := f \<rparr>) = is_ntfn_cap src_cap"
  "is_sched_context_cap (src_cap\<lparr>free_index := f \<rparr>) = is_sched_context_cap src_cap"
  "is_reply_cap (src_cap\<lparr>free_index := f \<rparr>) = is_reply_cap src_cap"
  by (simp add:is_cap_simps free_index_update_def split:cap.splits)+


lemma masked_as_full_simps[simp]:
  "masked_as_full (cap.EndpointCap r badge a) cap = (cap.EndpointCap r badge a)"
  "masked_as_full (cap.Zombie r bits n) cap = (cap.Zombie r bits n)"
  "masked_as_full (cap.ArchObjectCap x) cap = (cap.ArchObjectCap x)"
  "masked_as_full (cap.CNodeCap r n g) cap = (cap.CNodeCap r n g)"
  "masked_as_full (cap.SchedContextCap r m) cap = (cap.SchedContextCap r m)"
  "masked_as_full (cap.ReplyCap r) cap = (cap.ReplyCap r)"
  "masked_as_full cap.NullCap cap = cap.NullCap"
  "masked_as_full cap.DomainCap cap = cap.DomainCap"
  "masked_as_full (cap.ThreadCap r) cap = cap.ThreadCap r"
  "masked_as_full cap (cap.EndpointCap r badge a) = cap"
  "masked_as_full cap (cap.Zombie r bits n) = cap"
  "masked_as_full cap (cap.ArchObjectCap x) = cap"
  "masked_as_full cap (cap.CNodeCap r n g) = cap"
  "masked_as_full cap (cap.SchedContextCap r m) = cap"
  "masked_as_full cap (cap.ReplyCap r) = cap"
  "masked_as_full cap cap.NullCap = cap"
  "masked_as_full cap cap.DomainCap = cap"
  "masked_as_full cap (cap.ThreadCap r) = cap"
  by (simp add:masked_as_full_def)+

lemma masked_as_full_test_function_stuff[simp]:
  "gen_obj_refs (masked_as_full a cap) = gen_obj_refs a"
  "cap_asid (masked_as_full a cap ) = cap_asid a"
  "obj_refs (masked_as_full a cap ) = obj_refs a"
  "is_zombie (masked_as_full a cap ) = is_zombie a"
  "is_cnode_cap (masked_as_full a cap ) = is_cnode_cap a"
  "is_thread_cap (masked_as_full a cap ) = is_thread_cap a"
  "is_domain_cap (masked_as_full a cap ) = is_domain_cap a"
  "is_ep_cap (masked_as_full a cap ) = is_ep_cap a"
  "is_untyped_cap (masked_as_full a cap ) = is_untyped_cap a"
  "is_arch_cap (masked_as_full a cap ) = is_arch_cap a"
  "is_zombie (masked_as_full a cap ) = is_zombie a"
  "is_ntfn_cap (masked_as_full a cap ) = is_ntfn_cap a"
  "is_sched_context_cap (masked_as_full a cap ) = is_sched_context_cap a"
  "is_reply_cap (masked_as_full a cap ) = is_reply_cap a"
  by (auto simp:masked_as_full_def)

lemma set_untyped_cap_as_full_cte_wp_at_neg:
  "\<lbrace>\<lambda>s. (dest \<noteq> src \<and> \<not> (cte_wp_at P dest s) \<or>
         dest = src \<and> \<not> cte_wp_at (\<lambda>a. P (masked_as_full a cap)) src s) \<and>
        cte_wp_at ((=) src_cap) src s\<rbrace>
   set_untyped_cap_as_full src_cap cap src
   \<lbrace>\<lambda>ya s. \<not> cte_wp_at P dest s\<rbrace>"
  apply (clarsimp simp:set_untyped_cap_as_full_def | rule conjI |wp set_cap_cte_wp_at_neg)+
    apply (clarsimp simp:cte_wp_at_caps_of_state masked_as_full_def)+
  apply wp
  apply clarsimp
done

lemma set_untyped_cap_as_full_is_final_cap'_neg:
  "\<lbrace>\<lambda>s. \<not> is_final_cap' cap' s \<and> cte_wp_at ((=) src_cap) src s\<rbrace>
   set_untyped_cap_as_full src_cap cap src
   \<lbrace>\<lambda>rv s. \<not> is_final_cap' cap' s\<rbrace>"
  apply (rule hoare_pre)
  apply (simp add:is_final_cap'_def2)
     apply (wp hoare_vcg_all_lift hoare_vcg_ex_lift)
       apply (rule_tac Q = "cte_wp_at Q slot"
         and Q'="cte_wp_at ((=) src_cap) src" for Q slot in P_bool_lift' )
       apply (wp set_untyped_cap_as_full_cte_wp_at)
       apply clarsimp
     apply (wp set_untyped_cap_as_full_cte_wp_at_neg)
     apply (clarsimp simp:cte_wp_at_caps_of_state masked_as_full_def)
   apply (clarsimp simp:is_final_cap'_def2)
  done

lemma set_cap_def2:
  "set_cap cap = (\<lambda>(oref, cref). do
     obj \<leftarrow> get_object oref;
     obj' \<leftarrow> (case (obj, tcb_cap_cases cref) of
     (CNode sz cs, _) \<Rightarrow> if cref \<in> dom cs \<and> well_formed_cnode_n sz cs
         then return $ CNode sz $ cs(cref \<mapsto> cap)
         else fail
   | (TCB tcb, Some (getF, setF, restr)) \<Rightarrow> return $ TCB (setF (\<lambda>x. cap) tcb)
   | _ \<Rightarrow> fail);
     set_object oref obj'
   od)"
  apply (rule ext, simp add: set_cap_def split_def)
  apply (intro bind_cong bind_apply_cong refl)
  apply (simp split: Structures_A.kernel_object.split)
  apply (simp add: tcb_cap_cases_def)
  done

lemmas cap_insert_typ_ats [wp] = abs_typ_at_lifts [OF cap_insert_typ_at]

definition
  "is_simple_cap cap \<equiv>
    cap \<noteq> cap.NullCap \<and> cap \<noteq> cap.IRQControlCap \<and> \<not>is_untyped_cap cap \<and>
    \<not>is_sched_context_cap cap \<and> \<not>is_reply_cap cap \<and>
    \<not>is_ep_cap cap \<and> \<not>is_ntfn_cap cap \<and>
    \<not>is_thread_cap cap \<and> \<not>is_cnode_cap cap \<and> \<not>is_zombie cap \<and>
    is_simple_cap_arch cap"

definition
  "safe_parent_for m p cap parent \<equiv>
   cap_is_device cap = cap_is_device parent \<and>
   same_region_as parent cap \<and>
   ((\<exists>irq. cap = cap.IRQHandlerCap irq) \<and> parent = cap.IRQControlCap \<or>
    is_untyped_cap parent \<and> descendants_of p m = {} \<or> safe_parent_for_arch cap parent)"

definition
  capBadge_ordering :: "bool \<Rightarrow> (badge option \<times> badge option) set"
where
 "capBadge_ordering firstBadged \<equiv>
    (if firstBadged then {(None, None)} else Id) \<union> ({None, Some 0} \<times> range Some)"

(* True if cap' is derived from cap. *)
definition
  is_derived :: "cdt \<Rightarrow> cslot_ptr \<Rightarrow> cap \<Rightarrow> cap \<Rightarrow> bool"
where
  "is_derived m p cap' cap \<equiv>
  cap' \<noteq> cap.NullCap \<and>
  \<not> is_zombie cap \<and>
  cap' \<noteq> cap.IRQControlCap \<and>
  (if is_untyped_cap cap
  then
    cap_master_cap cap = cap_master_cap cap' \<and> descendants_of p m = {}
  else
    (cap_master_cap cap = cap_master_cap cap') \<and>
    (cap_badge cap, cap_badge cap') \<in> capBadge_ordering False) \<and>
    is_derived_arch cap' cap" (* RT: FIXME : reply_cap can be drived in rt?*)



(* FIXME: remove copy_of and use cap_master_cap with weak_derived directly *)
definition
  copy_of :: "cap \<Rightarrow> cap \<Rightarrow> bool"
where
  "copy_of cap' cap \<equiv>
     if (is_untyped_cap cap)
     then cap = cap'
     else same_object_as cap cap' \<and>
          is_reply_cap cap = is_reply_cap cap'"

(* cap' can be the result of a modification from cap made by the user
   using Copy, Mint, Move, Mutate,... Actually, that relation should be symmetric*)
definition
  "weak_derived cap cap' \<equiv>
  (copy_of cap cap' \<and>
   cap_asid cap = cap_asid cap' \<and>
   cap_asid_base cap = cap_asid_base cap' \<and>
   cap_vptr cap = cap_vptr cap') \<or>
   cap' = cap"


end
