(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory SR_lemmas_C
imports
  StateRelation_C
  "Refine.Invariants_H"
begin

context begin interpretation Arch . (*FIXME: arch-split*)

section "vm rights"

lemma vmRightsToBits_bounded:
  "vmRightsToBits rights < 4"
  by (cases rights; clarsimp simp: vmRightsToBits_def)

lemma vmRightsToBits_not_0:
  "vmRightsToBits rights \<noteq> 0"
  by (cases rights; clarsimp simp: vmRightsToBits_def)

lemma vmRightsToBits_vmrights_to_H:
  "\<lbrakk> rights < 4; rights \<noteq> 0 \<rbrakk> \<Longrightarrow> vmRightsToBits (vmrights_to_H rights) = rights"
  apply (clarsimp simp add: vmrights_to_H_def vm_rights_defs vmRightsToBits_def split: if_splits)
  apply (drule word_less_cases, erule disjE, simp, simp)+
  done

section "ctes"

subsection "capabilities"

lemma cteMDBNode_cte_to_H [simp]:
  "cteMDBNode (cte_to_H cte) = mdb_node_to_H (cteMDBNode_CL cte)"
  unfolding cte_to_H_def
  by simp

lemma cteMDBNode_CL_lift [simp]:
  "cte_lift cte' = Some ctel \<Longrightarrow>
  mdb_node_lift (cteMDBNode_C cte') = cteMDBNode_CL ctel"
  unfolding cte_lift_def
  by (fastforce split: option.splits)

lemma cteCap_cte_to_H [simp]:
  "cteCap (cte_to_H cte) = cap_to_H (cap_CL cte)"
  unfolding cte_to_H_def
  by simp

lemma cap_CL_lift [simp]:
  "cte_lift cte' = Some ctel \<Longrightarrow> cap_lift (cte_C.cap_C cte') = Some (cap_CL ctel)"
  unfolding cte_lift_def
  by (fastforce split: option.splits)

lemma cteCap_update_cte_to_H [simp]:
  "\<lbrakk> cte_lift cte' = Some z; cap_lift cap' = Some capl\<rbrakk>
  \<Longrightarrow> map_option cte_to_H (cte_lift (cte_C.cap_C_update (\<lambda>_. cap') cte')) =
  Some (cteCap_update (\<lambda>_. cap_to_H capl) (cte_to_H z))"
  unfolding cte_lift_def
  by (clarsimp simp: cte_to_H_def split: option.splits)

lemma cteMDBNode_C_update_lift [simp]:
  "cte_lift cte' = Some ctel \<Longrightarrow>
  (cte_lift (cteMDBNode_C_update (\<lambda>_. m) cte') = Some x)
  = (cteMDBNode_CL_update (\<lambda>_. mdb_node_lift m) ctel = x)"
  unfolding cte_lift_def
  by (fastforce split: option.splits)

lemma ccap_relationE:
  "\<lbrakk>ccap_relation c v; \<And>vl. \<lbrakk> cap_lift v = Some vl; c = cap_to_H vl; c_valid_cap v\<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  unfolding ccap_relation_def map_option_case
  apply clarsimp
  apply (drule sym)
  apply (clarsimp split: option.splits)
  done

definition
  "frameSize cap \<equiv> case cap of ArchObjectCap (FrameCap _ _ sz _ _) \<Rightarrow> sz"

definition
  "isArchCap_tag (n :: machine_word) \<equiv> n mod 2 = 1"

lemma isArchCap_tag_def2:
  "isArchCap_tag n \<equiv> n && 1 = 1"
  by (simp add: isArchCap_tag_def word_mod_2p_is_mask[where n=1, simplified] mask_def)

lemma cap_get_tag_isCap0:
  assumes cr: "ccap_relation cap cap'"
  shows "(cap_get_tag cap' = scast cap_thread_cap) = isThreadCap cap
  \<and> (cap_get_tag cap' = scast cap_null_cap) = (cap = NullCap)
  \<and> (cap_get_tag cap' = scast cap_notification_cap) = isNotificationCap cap
  \<and> (cap_get_tag cap' = scast cap_endpoint_cap) = isEndpointCap cap
  \<and> (cap_get_tag cap' = scast cap_irq_handler_cap) = isIRQHandlerCap cap
  \<and> (cap_get_tag cap' = scast cap_irq_control_cap) = isIRQControlCap cap
  \<and> (cap_get_tag cap' = scast cap_sched_control_cap) = isSchedControlCap cap
  \<and> (cap_get_tag cap' = scast cap_sched_context_cap) = isSchedContextCap cap
  \<and> (cap_get_tag cap' = scast cap_zombie_cap) = isZombie cap
  \<and> (cap_get_tag cap' = scast cap_reply_cap) = isReplyCap cap
  \<and> (cap_get_tag cap' = scast cap_untyped_cap) = isUntypedCap cap
  \<and> (cap_get_tag cap' = scast cap_cnode_cap) = isCNodeCap cap
  \<and> isArchCap_tag (cap_get_tag cap') = isArchCap \<top> cap
  \<and> (cap_get_tag cap' = scast cap_frame_cap) = (isArchFrameCap cap)
  \<and> (cap_get_tag cap' = scast cap_domain_cap) = isDomainCap cap"
  using cr
  apply -
  apply (erule ccap_relationE)
  apply (simp add: cap_to_H_def cap_lift_def Let_def isArchCap_tag_def2 isArchCap_def)
  by (clarsimp simp: isCap_simps cap_tag_defs word_le_nat_alt Let_def
              split: if_split_asm) \<comment> \<open>takes a while\<close>



lemma cap_get_tag_isCap:
  assumes cr: "ccap_relation cap cap'"
  shows "(cap_get_tag cap' = scast cap_thread_cap) = (isThreadCap cap)"
  and "(cap_get_tag cap' = scast cap_null_cap) = (cap = NullCap)"
  and "(cap_get_tag cap' = scast cap_notification_cap) = (isNotificationCap cap)"
  and "(cap_get_tag cap' = scast cap_endpoint_cap) = (isEndpointCap cap)"
  and "(cap_get_tag cap' = scast cap_irq_handler_cap) = (isIRQHandlerCap cap)"
  and "(cap_get_tag cap' = scast cap_irq_control_cap) = (isIRQControlCap cap)"
  and "(cap_get_tag cap' = scast cap_sched_control_cap) = isSchedControlCap cap"
  and "(cap_get_tag cap' = scast cap_sched_context_cap) = isSchedContextCap cap"
  and "(cap_get_tag cap' = scast cap_zombie_cap) = (isZombie cap)"
  and "(cap_get_tag cap' = scast cap_reply_cap) = isReplyCap cap"
  and "(cap_get_tag cap' = scast cap_untyped_cap) = (isUntypedCap cap)"
  and "(cap_get_tag cap' = scast cap_cnode_cap) = (isCNodeCap cap)"
  and "isArchCap_tag (cap_get_tag cap') = isArchCap \<top> cap"
  and "(cap_get_tag cap' = scast cap_frame_cap) = (isArchFrameCap cap)"
  and "(cap_get_tag cap' = scast cap_domain_cap) = isDomainCap cap"
  using cap_get_tag_isCap0 [OF cr] by auto

lemma cap_get_tag_NullCap:
  assumes cr: "ccap_relation cap cap'"
  shows "(cap_get_tag cap' = scast cap_null_cap) = (cap = NullCap)"
  using cr
  apply -
  apply (rule iffI)
   apply (clarsimp simp add: cap_lifts cap_get_tag_isCap cap_to_H_def)
  apply (simp add: cap_get_tag_isCap isCap_simps)
  done

lemma cap_get_tag_ThreadCap:
  assumes cr: "ccap_relation cap cap'"
  shows "(cap_get_tag cap' = scast cap_thread_cap) =
  (cap = ThreadCap (ctcb_ptr_to_tcb_ptr (Ptr (cap_thread_cap_CL.capTCBPtr_CL (cap_thread_cap_lift cap')))))"
  using cr
  apply -
  apply (rule iffI)
   apply (erule ccap_relationE)
   apply (clarsimp simp add: cap_lifts cap_to_H_def)
  apply (simp add: cap_get_tag_isCap isCap_simps)
  done

lemma cap_get_tag_NotificationCap:
  assumes cr: "ccap_relation cap cap'"
  shows "(cap_get_tag cap' = scast cap_notification_cap) =
  (cap = NotificationCap
         (capNtfnPtr_CL (cap_notification_cap_lift cap'))
         (capNtfnBadge_CL (cap_notification_cap_lift cap'))
         (to_bool (capNtfnCanSend_CL (cap_notification_cap_lift cap')))
         (to_bool (capNtfnCanReceive_CL (cap_notification_cap_lift cap'))))"
  using cr
  apply -
  apply (rule iffI)
   apply (erule ccap_relationE)
   apply (clarsimp simp add: cap_lifts cap_to_H_def)
  apply (simp add: cap_get_tag_isCap isCap_simps)
  done

lemma cap_get_tag_EndpointCap:
  assumes cr: "ccap_relation cap cap'"
  shows "(cap_get_tag cap' = scast cap_endpoint_cap) =
  (cap = EndpointCap (capEPPtr_CL (cap_endpoint_cap_lift cap'))
        (capEPBadge_CL (cap_endpoint_cap_lift cap'))
        (to_bool (capCanSend_CL (cap_endpoint_cap_lift cap')))
        (to_bool (capCanReceive_CL (cap_endpoint_cap_lift cap')))
        (to_bool (capCanGrant_CL (cap_endpoint_cap_lift cap')))
        (to_bool (capCanGrantReply_CL (cap_endpoint_cap_lift cap'))))"
  using cr
  apply -
  apply (rule iffI)
   apply (erule ccap_relationE)
   apply (clarsimp simp add: cap_lifts cap_to_H_def)
  apply (simp add: cap_get_tag_isCap isCap_simps)
  done

lemma cap_get_tag_CNodeCap:
  assumes cr: "ccap_relation cap cap'"
  shows "(cap_get_tag cap' = scast cap_cnode_cap) =
  (cap = capability.CNodeCap (capCNodePtr_CL (cap_cnode_cap_lift cap'))
          (unat (capCNodeRadix_CL (cap_cnode_cap_lift cap')))
          (capCNodeGuard_CL (cap_cnode_cap_lift cap'))
          (unat (capCNodeGuardSize_CL (cap_cnode_cap_lift cap'))))"
  using cr
  apply -
  apply (rule iffI)
   apply (erule ccap_relationE)
   apply (clarsimp simp add: cap_lifts cap_to_H_def Let_def)
  apply (simp add: cap_get_tag_isCap isCap_simps Let_def)
  done

lemma cap_get_tag_IRQHandlerCap:
  assumes cr: "ccap_relation cap cap'"
  shows "(cap_get_tag cap' = scast cap_irq_handler_cap) =
  (cap = capability.IRQHandlerCap (ucast (capIRQ_CL (cap_irq_handler_cap_lift cap'))))"
  using cr
  apply -
  apply (rule iffI)
   apply (erule ccap_relationE)
   apply (clarsimp simp add: cap_lifts cap_to_H_def)
  apply (simp add: cap_get_tag_isCap isCap_simps)
  done

lemma cap_get_tag_SchedControlCap:
  assumes cr: "ccap_relation cap cap'"
  shows "(cap_get_tag cap' = scast cap_sched_control_cap) = (cap = capability.SchedControlCap)"
  using cr
  apply -
  apply (rule iffI)
   apply (erule ccap_relationE)
   apply (clarsimp simp add: cap_lifts cap_to_H_def Let_def)
  apply (simp add: cap_get_tag_isCap isCap_simps Let_def)
  done

lemma cap_get_tag_SchedContextCap:
  assumes cr: "ccap_relation cap cap'"
  shows "(cap_get_tag cap' = scast cap_sched_context_cap) =
   (cap = capability.SchedContextCap (ucast (capSCPtr_CL (cap_sched_context_cap_lift cap')))
                                     (unat (capSCSizeBits_CL (cap_sched_context_cap_lift cap'))))"
  using cr
  apply -
  apply (rule iffI)
   apply (erule ccap_relationE)
   apply (clarsimp simp add: cap_lifts cap_to_H_def Let_def)
  apply (simp add: cap_get_tag_isCap isCap_simps Let_def)
  done

lemma cap_get_tag_IRQControlCap:
  assumes cr: "ccap_relation cap cap'"
  shows "(cap_get_tag cap' = scast cap_irq_control_cap) =
  (cap = capability.IRQControlCap)"
  using cr
  apply -
  apply (rule iffI)
   apply (clarsimp simp add: cap_lifts cap_get_tag_isCap isCap_simps cap_to_H_def)
  apply (simp add: cap_get_tag_isCap isCap_simps)
  done

lemma cap_get_tag_ReplyCap:
   assumes cr: "ccap_relation cap cap'"
   shows "(cap_get_tag cap' = scast cap_reply_cap) =
   (cap =
       ReplyCap (capReplyPtr_CL (cap_reply_cap_lift cap'))
                (to_bool (capReplyCanGrant_CL (cap_reply_cap_lift cap'))))"
   using cr
   apply -
   apply (rule iffI)
    apply (erule ccap_relationE)
    apply (clarsimp simp add: cap_lifts cap_to_H_def)
   apply (simp add: cap_get_tag_isCap isCap_simps)
   done

lemma cap_get_tag_ZombieCap:
  assumes cr: "ccap_relation cap cap'"
  shows "(cap_get_tag cap' = scast cap_zombie_cap) =
  (cap =
   (if isZombieTCB_C (capZombieType_CL (cap_zombie_cap_lift cap'))
     then capability.Zombie (capZombieID_CL (cap_zombie_cap_lift cap') && ~~ mask 5) ZombieTCB
           (unat (capZombieID_CL (cap_zombie_cap_lift cap') && mask 5))
     else let radix = unat (capZombieType_CL (cap_zombie_cap_lift cap'))
          in capability.Zombie (capZombieID_CL (cap_zombie_cap_lift cap') && ~~ mask (radix + 1))
              (ZombieCNode radix)
              (unat (capZombieID_CL (cap_zombie_cap_lift cap') && mask (radix + 1)))))"
  using cr
  apply -
  apply (rule iffI)
   apply (erule ccap_relationE)
   apply (clarsimp simp add: cap_lifts cap_to_H_def)
  apply (simp add: cap_get_tag_isCap isCap_simps Let_def
            split: if_split_asm)
  done

lemma cap_get_tag_UntypedCap:
  assumes cr: "ccap_relation cap cap'"
  shows "(cap_get_tag cap' = scast cap_untyped_cap) =
  (cap = UntypedCap (to_bool (capIsDevice_CL (cap_untyped_cap_lift cap')))
                    (capPtr_CL (cap_untyped_cap_lift cap'))
                    (unat (capBlockSize_CL (cap_untyped_cap_lift cap')))
                    (unat (capFreeIndex_CL (cap_untyped_cap_lift cap') << 4)))"
  using cr
  apply -
  apply (rule iffI)
   apply (erule ccap_relationE)
   apply (clarsimp simp add: cap_lifts cap_to_H_def)
  apply (simp add: cap_get_tag_isCap isCap_simps)
  done

lemma cap_get_tag_DomainCap:
  assumes cr: "ccap_relation cap cap'"
  shows "(cap_get_tag cap' = scast cap_domain_cap) = (cap = DomainCap)"
  using cr
  apply -
  apply (rule iffI)
   apply (clarsimp simp add: cap_lifts cap_get_tag_isCap cap_to_H_def)
  apply (simp add: cap_get_tag_isCap isCap_simps)
  done

lemmas cap_get_tag_to_H_iffs =
     cap_get_tag_NullCap
     cap_get_tag_ThreadCap
     cap_get_tag_NotificationCap
     cap_get_tag_EndpointCap
     cap_get_tag_CNodeCap
     cap_get_tag_IRQHandlerCap
     cap_get_tag_IRQControlCap
     cap_get_tag_ReplyCap
     cap_get_tag_SchedControlCap
     cap_get_tag_SchedContextCap
     cap_get_tag_ZombieCap
     cap_get_tag_UntypedCap
     cap_get_tag_DomainCap

lemmas cap_get_tag_to_H = cap_get_tag_to_H_iffs [THEN iffD1]

subsection "mdb"

lemma cmdbnode_relation_mdb_node_to_H [simp]:
  "cte_lift cte' = Some y
  \<Longrightarrow> cmdbnode_relation (mdb_node_to_H (cteMDBNode_CL y)) (cteMDBNode_C cte')"
  unfolding cmdbnode_relation_def mdb_node_to_H_def mdb_node_lift_def cte_lift_def
  by (fastforce split: option.splits)

definition
  tcb_no_ctes_proj ::
  "tcb \<Rightarrow> Structures_H.thread_state \<times> vptr \<times> arch_tcb \<times> bool \<times> bool \<times> priority \<times> priority \<times>
          domain \<times> fault option \<times> machine_word option \<times> machine_word option \<times>
          machine_word option \<times> machine_word option \<times> machine_word option"
  where
  "tcb_no_ctes_proj t \<equiv> (tcbState t, tcbIPCBuffer t, tcbArch t, tcbQueued t, tcbInReleaseQueue t,
                          tcbMCP t, tcbPriority t, tcbDomain t, tcbFault t, tcbBoundNotification t,
                          tcbSchedContext t, tcbYieldTo t, tcbSchedNext t, tcbSchedPrev t)"

lemma tcb_cte_cases_proj_eq [simp]:
  "tcb_cte_cases p = Some (getF, setF) \<Longrightarrow>
  tcb_no_ctes_proj tcb = tcb_no_ctes_proj (setF f tcb)"
  unfolding tcb_no_ctes_proj_def tcb_cte_cases_def
  by (auto split: if_split_asm)

(* NOTE: 5 = cte_level_bits *)
lemma map_to_ctes_upd_cte':
  "\<lbrakk> ksPSpace s p = Some (KOCTE cte'); is_aligned p cte_level_bits; ps_clear p cte_level_bits s \<rbrakk>
  \<Longrightarrow> map_to_ctes ((ksPSpace s)(p |-> KOCTE cte)) = (map_to_ctes (ksPSpace s))(p |-> cte)"
  apply (erule (1) map_to_ctes_upd_cte)
  apply (simp add: field_simps ps_clear_def3 cte_level_bits_def mask_def)
  done

lemma map_to_ctes_upd_tcb':
  "[| ksPSpace s p = Some (KOTCB tcb'); is_aligned p tcbBlockSizeBits;
   ps_clear p tcbBlockSizeBits s |]
==> map_to_ctes ((ksPSpace s)(p |-> KOTCB tcb)) =
    (%x. if EX getF setF.
               tcb_cte_cases (x - p) = Some (getF, setF) &
               getF tcb ~= getF tcb'
         then case tcb_cte_cases (x - p) of
              Some (getF, setF) => Some (getF tcb)
         else ctes_of s x)"
  apply (erule (1) map_to_ctes_upd_tcb)
  apply (simp add: field_simps ps_clear_def3 mask_def objBits_defs)
  done


lemma tcb_cte_cases_inv [simp]:
  "tcb_cte_cases p = Some (getF, setF) \<Longrightarrow> getF (setF (\<lambda>_. v) tcb) = v"
  unfolding tcb_cte_cases_def
  by (simp split: if_split_asm)

declare insert_dom [simp]

lemma in_alignCheck':
  "(z \<in> fst (alignCheck x n s)) = (snd z = s \<and> is_aligned x n)"
  by (cases z, simp)

lemma fst_alignCheck_empty [simp]:
   "(fst (alignCheck x n s) = {}) = (\<not> is_aligned x n)"
  apply (subst all_not_in_conv [symmetric])
  apply (clarsimp simp: in_alignCheck')
  done

lemma fst_setCTE0:
  notes option.case_cong_weak [cong]
  assumes ct: "cte_at' dest s"
  shows   "\<exists>(v, s') \<in> fst (setCTE dest cte s).
           (s' = s \<lparr> ksPSpace := ksPSpace s' \<rparr>)
           \<and> (dom (ksPSpace s) = dom (ksPSpace s'))
           \<and> (\<forall>x \<in> dom (ksPSpace s).
                case (the (ksPSpace s x)) of
                      KOCTE _ \<Rightarrow> (\<exists>cte. ksPSpace s' x = Some (KOCTE cte))
                    | KOTCB t \<Rightarrow> (\<exists>t'. ksPSpace s' x = Some (KOTCB t') \<and> tcb_no_ctes_proj t = tcb_no_ctes_proj t')
                    | _       \<Rightarrow> ksPSpace s' x = ksPSpace s x)"
  using ct
  apply -
  apply (clarsimp simp: setCTE_def setObject_def
    bind_def return_def assert_opt_def gets_def split_beta get_def
    modify_def put_def)
  apply (erule cte_wp_atE')
   apply (rule ps_clear_lookupAround2, assumption+)
     apply simp
    apply (erule is_aligned_no_overflow)
   apply (simp (no_asm_simp) del: fun_upd_apply cong: option.case_cong)
   apply (simp add: return_def updateObject_cte
     bind_def assert_opt_def gets_def split_beta get_def
     modify_def put_def unless_def when_def
     objBits_simps
     cong: bex_cong)
   apply (rule bexI [where x = "((), s)"])
    apply (frule_tac s' = s in in_magnitude_check [where v = "()"])
      apply (simp add: cte_level_bits_def)
     apply assumption
    apply (simp add: objBits_defs cte_level_bits_def)
    apply (erule bexI [rotated])
    apply (simp  cong: if_cong)
    apply rule
    apply (simp split: kernel_object.splits)
    apply (fastforce simp: tcb_no_ctes_proj_def)
   apply (simp add: cte_level_bits_def objBits_defs)
  (* clag *)
  apply (rule ps_clear_lookupAround2, assumption+)
    apply (erule (1) tcb_cte_cases_in_range1)
   apply (erule (1) tcb_cte_cases_in_range2)
  apply (simp add: return_def del: fun_upd_apply cong: bex_cong option.case_cong)
  apply (subst updateObject_cte_tcb)
   apply assumption
  apply (simp add: bind_def split_beta in_alignCheck' objBits_simps magnitudeCheck_def
            split: option.splits kernel_object.splits)
   apply (clarsimp simp: read_magnitudeCheck_def return_def)
  apply (fastforce simp: gets_the_def gets_def return_def get_def bind_def)
  done

(* duplicates *)

declare pspace_distinctD' [intro?]

lemma ctes_of_ksI [intro?]:
  fixes s :: "kernel_state"
  assumes ks: "ksPSpace s x = Some (KOCTE cte)"
  and     pa: "pspace_aligned' s"
  and     pd: "pspace_distinct' s"
  shows   "ctes_of s x = Some cte"
proof (rule ctes_of_eq_cte_wp_at')
  from ks show "cte_wp_at' ((=) cte) x s"
  proof (rule cte_wp_at_cteI' [OF _ _ _ refl])
    from ks pa have "is_aligned x (objBitsKO (KOCTE cte))" using pspace_alignedD' by fastforce
    thus "is_aligned x cte_level_bits"
      unfolding cte_level_bits_def by (simp add: objBits_simps')

    from ks pd have "ps_clear x (objBitsKO (KOCTE cte)) s" ..
    thus "ps_clear x cte_level_bits s"
      unfolding cte_level_bits_def by (simp add: objBits_simps')
  qed
qed


lemma fst_setCTE:
  assumes ct: "cte_at' dest s"
  and     rl: "\<And>s'. \<lbrakk> ((), s') \<in> fst (setCTE dest cte s);
           (s' = s \<lparr> ksPSpace := ksPSpace s' \<rparr>);
           (ctes_of s' = (ctes_of s)(dest \<mapsto> cte));
           (map_to_eps (ksPSpace s) = map_to_eps (ksPSpace s'));
           (map_to_ntfns (ksPSpace s) = map_to_ntfns (ksPSpace s'));
           (map_to_scs (ksPSpace s) = map_to_scs (ksPSpace s'));
           (map_to_replies (ksPSpace s) = map_to_replies (ksPSpace s'));
           (map_to_ptes (ksPSpace s) = map_to_ptes (ksPSpace s'));
           (map_to_asidpools (ksPSpace s) = map_to_asidpools (ksPSpace s'));
           (map_to_user_data (ksPSpace s) = map_to_user_data (ksPSpace s'));
           (map_to_user_data_device (ksPSpace s) = map_to_user_data_device (ksPSpace s'));
           (map_option tcb_no_ctes_proj \<circ> map_to_tcbs (ksPSpace s)
              = map_option tcb_no_ctes_proj \<circ> map_to_tcbs (ksPSpace s'));
           \<forall>T p. typ_at' T p s = typ_at' T p s'\<rbrakk> \<Longrightarrow> P"
  shows   "P"
proof -
  from fst_setCTE0 [where cte = cte, OF ct]
  obtain s' where
    "((), s')\<in>fst (setCTE dest cte s)"
    "s' = s\<lparr>ksPSpace := ksPSpace s'\<rparr>"
    "dom (ksPSpace s) = dom (ksPSpace s')"
    "(\<forall>p \<in> dom (ksPSpace s').
       case the (ksPSpace s p) of
         KOTCB t \<Rightarrow> \<exists>t'. ksPSpace s' p = Some (KOTCB t') \<and> tcb_no_ctes_proj t = tcb_no_ctes_proj t'
       | KOCTE _ \<Rightarrow> \<exists>cte. ksPSpace s' p = Some (KOCTE cte)
       | _ \<Rightarrow> ksPSpace s' p = ksPSpace s p)"
    by clarsimp
  note thms = this

  have ceq: "ctes_of s' = (ctes_of s)(dest \<mapsto> cte)"
    by (rule use_valid [OF thms(1) setCTE_ctes_of_wp]) simp

  show ?thesis
  proof (rule rl)
    show "map_to_eps (ksPSpace s) = map_to_eps (ksPSpace s')"
    proof (rule map_comp_eqI)
      fix x
      assume xin: "x \<in> dom (ksPSpace s')"
      then obtain ko where ko: "ksPSpace s x = Some ko" by (clarsimp simp: thms(3)[symmetric])
      moreover from xin obtain ko' where ko': "ksPSpace s' x = Some ko'" by clarsimp
      ultimately have "(projectKO_opt ko' :: endpoint option) = projectKO_opt ko" using xin thms(4) ceq
        by - (drule (1) bspec, cases ko, auto simp: projectKO_opt_ep)
      thus "(projectKO_opt (the (ksPSpace s' x)) :: endpoint option) = projectKO_opt (the (ksPSpace s x))"  using ko ko'
        by simp
    qed fact

    (* clag \<dots> *)
    show "map_to_ntfns (ksPSpace s) = map_to_ntfns (ksPSpace s')"
    proof (rule map_comp_eqI)
      fix x
      assume xin: "x \<in> dom (ksPSpace s')"
      then obtain ko where ko: "ksPSpace s x = Some ko" by (clarsimp simp: thms(3)[symmetric])
      moreover from xin obtain ko' where ko': "ksPSpace s' x = Some ko'" by clarsimp
      ultimately have "(projectKO_opt ko' :: Structures_H.notification option) = projectKO_opt ko" using xin thms(4) ceq
        by - (drule (1) bspec, cases ko, auto simp: projectKO_opt_ntfn)
      thus "(projectKO_opt (the (ksPSpace s' x)) :: Structures_H.notification option) = projectKO_opt (the (ksPSpace s x))" using ko ko'
        by simp
    qed fact

    (* clag \<dots> *)
    show "map_to_scs (ksPSpace s) = map_to_scs (ksPSpace s')"
    proof (rule map_comp_eqI)
      fix x
      assume xin: "x \<in> dom (ksPSpace s')"
      then obtain ko where ko: "ksPSpace s x = Some ko" by (clarsimp simp: thms(3)[symmetric])
      moreover from xin obtain ko' where ko': "ksPSpace s' x = Some ko'" by clarsimp
      ultimately have "(projectKO_opt ko' :: Structures_H.sched_context option) = projectKO_opt ko" using xin thms(4) ceq
        by - (drule (1) bspec, cases ko, auto simp: projectKO_opt_sc)
      thus "(projectKO_opt (the (ksPSpace s' x)) :: Structures_H.sched_context option) = projectKO_opt (the (ksPSpace s x))" using ko ko'
        by simp
    qed fact

    (* clag \<dots> *)
    show "map_to_replies (ksPSpace s) = map_to_replies (ksPSpace s')"
    proof (rule map_comp_eqI)
      fix x
      assume xin: "x \<in> dom (ksPSpace s')"
      then obtain ko where ko: "ksPSpace s x = Some ko" by (clarsimp simp: thms(3)[symmetric])
      moreover from xin obtain ko' where ko': "ksPSpace s' x = Some ko'" by clarsimp
      ultimately have "(projectKO_opt ko' :: Structures_H.reply option) = projectKO_opt ko" using xin thms(4) ceq
        by - (drule (1) bspec, cases ko, auto simp: projectKO_opt_reply)
      thus "(projectKO_opt (the (ksPSpace s' x)) :: Structures_H.reply option) = projectKO_opt (the (ksPSpace s x))" using ko ko'
        by simp
    qed fact

    show "map_to_ptes (ksPSpace s) = map_to_ptes (ksPSpace s')"
    proof (rule map_comp_eqI)
      fix x
      assume xin: "x \<in> dom (ksPSpace s')"
      then obtain ko where ko: "ksPSpace s x = Some ko" by (clarsimp simp: thms(3)[symmetric])
      moreover from xin obtain ko' where ko': "ksPSpace s' x = Some ko'" by clarsimp
      ultimately have "(projectKO_opt ko' :: pte option) = projectKO_opt ko" using xin thms(4) ceq
        by - (drule (1) bspec, cases ko, auto simp: projectKO_opt_pte)
      thus "(projectKO_opt (the (ksPSpace s' x)) :: pte option) = projectKO_opt (the (ksPSpace s x))" using ko ko'
        by simp
    qed fact

    show "map_to_asidpools (ksPSpace s) = map_to_asidpools (ksPSpace s')"
    proof (rule map_comp_eqI)
      fix x
      assume xin: "x \<in> dom (ksPSpace s')"
      then obtain ko where ko: "ksPSpace s x = Some ko" by (clarsimp simp: thms(3)[symmetric])
      moreover from xin obtain ko' where ko': "ksPSpace s' x = Some ko'" by clarsimp
      ultimately have "(projectKO_opt ko' :: asidpool option) = projectKO_opt ko" using xin thms(4) ceq
        by - (drule (1) bspec, cases ko, auto simp: projectKO_opt_asidpool)
      thus "(projectKO_opt (the (ksPSpace s' x)) :: asidpool option) = projectKO_opt (the (ksPSpace s x))" using ko ko'
        by simp
    qed fact

    show "map_to_user_data (ksPSpace s) = map_to_user_data (ksPSpace s')"
    proof (rule map_comp_eqI)
      fix x
      assume xin: "x \<in> dom (ksPSpace s')"
      then obtain ko where ko: "ksPSpace s x = Some ko" by (clarsimp simp: thms(3)[symmetric])
      moreover from xin obtain ko' where ko': "ksPSpace s' x = Some ko'" by clarsimp
      ultimately have "(projectKO_opt ko' :: user_data option) = projectKO_opt ko" using xin thms(4) ceq
        by - (drule (1) bspec, cases ko, auto simp: projectKO_opt_user_data)
      thus "(projectKO_opt (the (ksPSpace s' x)) :: user_data option) = projectKO_opt (the (ksPSpace s x))" using ko ko'
        by simp
    qed fact

    show "map_to_user_data_device (ksPSpace s) = map_to_user_data_device (ksPSpace s')"
    proof (rule map_comp_eqI)
      fix x
      assume xin: "x \<in> dom (ksPSpace s')"
      then obtain ko where ko: "ksPSpace s x = Some ko" by (clarsimp simp: thms(3)[symmetric])
      moreover from xin obtain ko' where ko': "ksPSpace s' x = Some ko'" by clarsimp
      ultimately have "(projectKO_opt ko' :: user_data_device option) = projectKO_opt ko" using xin thms(4) ceq
             by - (drule (1) bspec, cases ko, auto simp: projectKO_opt_user_data_device)
      thus "(projectKO_opt (the (ksPSpace s' x)) :: user_data_device option) = projectKO_opt (the (ksPSpace s x))" using ko ko'
             by simp
    qed fact


    note sta = setCTE_typ_at'[where P="\<lambda>x. x = y" for y]
    show typ_at: "\<forall>T p. typ_at' T p s = typ_at' T p s'"
      using use_valid[OF _ sta, OF thms(1), OF refl]
      by auto

    show "map_option tcb_no_ctes_proj \<circ> map_to_tcbs (ksPSpace s) =
      map_option tcb_no_ctes_proj \<circ> map_to_tcbs (ksPSpace s')"
    proof (rule ext)
      fix x

      have dm: "dom (map_to_tcbs (ksPSpace s)) = dom (map_to_tcbs (ksPSpace s'))"
        using thms(3) thms(4)
        apply -
        apply (rule set_eqI)
        apply rule
        apply (frule map_comp_subset_domD)
        apply simp
        apply (drule (1) bspec)
        apply (clarsimp simp: projectKOs dom_map_comp)
        apply (frule map_comp_subset_domD)
        apply (drule (1) bspec)
        apply (auto simp: dom_map_comp projectKOs split: kernel_object.splits)
        apply fastforce
        done

      {
        assume "x \<in> dom (map_to_tcbs (ksPSpace s))"
        hence "map_option tcb_no_ctes_proj (map_to_tcbs (ksPSpace s) x)
          = map_option tcb_no_ctes_proj (map_to_tcbs (ksPSpace s') x)"
          using thms(3) thms(4)
          apply -
          apply (frule map_comp_subset_domD)
          apply simp
          apply (drule (1) bspec)
          apply (clarsimp simp: dom_map_comp projectKOs projectKO_opt_tcb)
          apply (case_tac y)
          apply simp_all
          apply clarsimp
          done
      } moreover
      {
        assume "x \<notin> dom (map_to_tcbs (ksPSpace s))"
        hence "map_option tcb_no_ctes_proj (map_to_tcbs (ksPSpace s) x)
          = map_option tcb_no_ctes_proj (map_to_tcbs (ksPSpace s') x)"
          apply -
          apply (frule subst [OF dm])
          apply (simp add: dom_def)
          done
      } ultimately show "(map_option tcb_no_ctes_proj \<circ> (map_to_tcbs (ksPSpace s))) x
          = (map_option tcb_no_ctes_proj \<circ> (map_to_tcbs (ksPSpace s'))) x"
          by auto
    qed
  qed fact+
qed

lemma cor_map_relI:
  assumes dm: "dom am = dom am'"
  and     rl: "\<And>x y y' z. \<lbrakk> am x = Some y; am' x = Some y';
  rel y z \<rbrakk> \<Longrightarrow> rel y' z"
  shows "cmap_relation am cm sz rel \<Longrightarrow> cmap_relation am' cm sz rel"
  unfolding cmap_relation_def
  apply -
  apply clarsimp
  apply rule
   apply (simp add: dm)
  apply rule
  apply (frule_tac P = "\<lambda>s. x \<in> s" in ssubst [OF dm])
  apply (drule (1) bspec)
  apply (erule domD [where m = am, THEN exE])
  apply (rule rl, assumption+)
   apply (clarsimp simp add: dom_def)
  apply simp
  done

lemma setCTE_tcb_case:
  assumes om: "map_option tcb_no_ctes_proj \<circ> map_to_tcbs (ksPSpace s) =
  map_option tcb_no_ctes_proj \<circ> map_to_tcbs (ksPSpace s')"
  and    rel: "cmap_relation (map_to_tcbs (ksPSpace s)) (clift (t_hrs_' (globals x))) tcb_ptr_to_ctcb_ptr ctcb_relation"
  shows "cmap_relation (map_to_tcbs (ksPSpace s')) (clift (t_hrs_' (globals x))) tcb_ptr_to_ctcb_ptr ctcb_relation"
  using om
proof (rule cor_map_relI [OF map_option_eq_dom_eq])
  fix x tcb tcb' z
  assume y: "map_to_tcbs (ksPSpace s) x = Some tcb"
    and y': "map_to_tcbs (ksPSpace s') x = Some tcb'" and rel: "ctcb_relation tcb z"

  hence "tcb_no_ctes_proj tcb = tcb_no_ctes_proj tcb'" using om
    apply -
    apply (drule fun_cong [where x = x])
    apply simp
    done

  thus "ctcb_relation tcb' z" using rel
    unfolding tcb_no_ctes_proj_def ctcb_relation_def cfault_rel_def option_to_ptr_def option_to_0_def
    by auto
qed fact+

lemma lifth_update:
  "clift (t_hrs_' s) ptr = clift (t_hrs_' s') ptr
  \<Longrightarrow> lifth ptr s = lifth ptr s'"
  unfolding lifth_def
  by simp

lemma getCTE_exs_valid:
  "cte_at' dest s \<Longrightarrow> \<lbrace>(=) s\<rbrace> getCTE dest \<exists>\<lbrace>\<lambda>r. (=) s\<rbrace>"
  unfolding exs_valid_def getCTE_def cte_wp_at'_def
  by clarsimp

lemma cmap_domE1:
  "\<lbrakk> f ` dom am = dom cm; am x = Some v; \<And>v'. cm (f x) = Some v' \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (drule equalityD1)
  apply (drule subsetD)
   apply (erule imageI [OF domI])
  apply (clarsimp simp: dom_def)
  done

lemma cmap_domE2:
  "\<lbrakk> f ` dom am = dom cm; cm x = Some v'; \<And>x' v. \<lbrakk> x = f x'; am x' = Some v \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (drule equalityD2)
  apply (drule subsetD)
  apply (erule domI)
  apply (clarsimp simp: dom_def)
  done

lemma cmap_relationE1:
  "\<lbrakk> cmap_relation am cm f rel; am x = Some y;
  \<And>y'. \<lbrakk>am x = Some y; rel y y'; cm (f x) = Some y'\<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  unfolding cmap_relation_def
  apply clarsimp
  apply (erule (1) cmap_domE1)
  apply (drule (1) bspec [OF _ domI])
  apply clarsimp
  done

lemma cmap_relationE2:
  "\<lbrakk> cmap_relation am cm f rel; cm x = Some y';
  \<And>x' y. \<lbrakk>x = f x'; rel y y'; am x' = Some y\<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  unfolding cmap_relation_def
  apply clarsimp
  apply (erule (1) cmap_domE2)
  apply (drule (1) bspec [OF _ domI])
  apply clarsimp
  done

lemma cmap_relationI:
  assumes doms:  "f ` dom am = dom cm"
  and     rel:   "\<And>x v v'. \<lbrakk>am x = Some v; cm (f x) = Some v' \<rbrakk> \<Longrightarrow> rel v v'"
  shows "cmap_relation am cm f rel"
  unfolding cmap_relation_def using doms
proof (rule conjI)
  show "\<forall>x\<in>dom am. rel (the (am x)) (the (cm (f x)))"
  proof
    fix x
    assume "x \<in> dom am"
    then obtain v where "am x = Some v" ..
    moreover with doms obtain v' where "cm (f x) = Some v'" by (rule cmap_domE1)
    ultimately show "rel (the (am x)) (the (cm (f x)))"
      by (simp add: rel)
  qed
qed

lemma cmap_relation_relI:
  assumes "cmap_relation am cm f rel"
  and     "am x = Some v"
  and     "cm (f x) = Some v'"
  shows "rel v v'"
  using assms
  by (fastforce elim!: cmap_relationE1)

lemma cspace_cte_relationE:
  "\<lbrakk> cmap_relation am cm Ptr ccte_relation; am x = Some y;
  \<And>z k'. \<lbrakk>cm (Ptr x) = Some k'; cte_lift k' = Some z; cte_to_H z = y; c_valid_cte k' \<rbrakk> \<Longrightarrow> P
  \<rbrakk> \<Longrightarrow> P"
  apply (erule (1) cmap_relationE1)
  apply (clarsimp simp: ccte_relation_def map_option_Some_eq2)
  done

lemma cmdbnode_relationE:
  "\<lbrakk>cmdbnode_relation m v; m = mdb_node_to_H (mdb_node_lift v) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  unfolding cmdbnode_relation_def
  apply (drule sym)
  apply clarsimp
  done

(* Used when the rel changes as well *)
lemma cmap_relation_upd_relI:
  fixes am :: "machine_word \<rightharpoonup> 'a" and cm :: "'b typ_heap"
  assumes cr: "cmap_relation am cm f rel"
  and   cof: "am dest = Some v"
  and   cl:  "cm (f dest) = Some v'"
  and   cc:  "rel' nv nv'"
  and   rel: "\<And>x ov ov'. \<lbrakk> x \<noteq> dest; am x = Some ov; cm (f x) = Some ov'; rel ov ov' \<rbrakk> \<Longrightarrow> rel' ov ov'"
  and   inj: "inj f"
  shows "cmap_relation (am(dest \<mapsto> nv)) (cm(f dest \<mapsto> nv')) f rel'"
  using assms
  apply -
  apply (rule cmap_relationE1, assumption+)
  apply clarsimp
  apply (rule cmap_relationI)
  apply (simp add: cmap_relation_def)
  apply (case_tac "x = dest")
   apply simp
  apply (simp add: inj_eq split: if_split_asm)
  apply (erule (2) rel)
  apply (erule (2) cmap_relation_relI)
  done

lemma cmap_relation_updI:
  fixes am :: "machine_word \<rightharpoonup> 'a" and cm :: "'b typ_heap"
  assumes cr: "cmap_relation am cm f rel"
  and   cof: "am dest = Some v"
  and   cl:  "cm (f dest) = Some v'"
  and   cc:  "rel nv nv'"
  and   inj: "inj f"
  shows "cmap_relation (am(dest \<mapsto> nv)) (cm(f dest \<mapsto> nv')) f rel"
  using cr cof cl cc
  apply (rule cmap_relation_upd_relI)
   apply simp
  apply fact
  done

declare inj_Ptr[simp]

(* Ugh *)
lemma cpspace_cte_relation_upd_capI:
  assumes cr: "cmap_relation (map_to_ctes am) (clift cm) Ptr ccte_relation"
  and   cof: "map_to_ctes am dest = Some cte"
  and   cl:  "clift cm (Ptr dest) = Some cte'"
  and   cc:  "ccap_relation capl cap"
  shows "cmap_relation ((map_to_ctes am)(dest \<mapsto>  (cteCap_update (\<lambda>_. capl) cte)))
  ((clift cm)(Ptr dest \<mapsto> cte_C.cap_C_update (\<lambda>_. cap) cte')) Ptr ccte_relation"
  using cr cof cl cc
  apply -
  apply (frule (2) cmap_relation_relI)
  apply (erule (2) cmap_relation_updI)
   apply (clarsimp elim!: ccap_relationE simp: map_comp_Some_iff ccte_relation_def)
    apply (subst (asm) map_option_Some_eq2)
    apply clarsimp
    apply (simp add: c_valid_cte_def cl_valid_cte_def)
  apply simp
done

lemma cte_to_H_mdb_node_update [simp]:
  "cte_to_H (cteMDBNode_CL_update (\<lambda>_. m) cte) =
  cteMDBNode_update (\<lambda>_. mdb_node_to_H  m) (cte_to_H cte)"
  unfolding cte_to_H_def
  by simp

lemma cspace_cte_relation_upd_mdbI:
  assumes cr: "cmap_relation (map_to_ctes am) (clift cm) Ptr ccte_relation"
  and   cof: "map_to_ctes am dest = Some cte"
  and   cl:  "clift cm (Ptr dest) = Some cte'"
  and   cc:  "cmdbnode_relation mdbl m"
  shows "cmap_relation ((map_to_ctes am)(dest \<mapsto> cteMDBNode_update (\<lambda>_. mdbl) cte))
  ((clift cm)(Ptr dest \<mapsto> cte_C.cteMDBNode_C_update (\<lambda>_. m) cte')) Ptr ccte_relation"
  using cr cof cl cc
  apply -
  apply (frule (2) cmap_relation_relI)
  apply (erule (2) cmap_relation_updI)
   apply (clarsimp elim!: cmdbnode_relationE
           simp: map_comp_Some_iff ccte_relation_def c_valid_cte_def cl_valid_cte_def map_option_Some_eq2)
  apply simp
done

lemma mdb_node_to_H_mdbPrev_update[simp]:
  "mdb_node_to_H (mdbPrev_CL_update (\<lambda>_. x) m)
  = mdbPrev_update (\<lambda>_. x) (mdb_node_to_H m)"
  unfolding mdb_node_to_H_def by simp

lemma mdb_node_to_H_mdbNext_update[simp]:
  "mdb_node_to_H (mdbNext_CL_update (\<lambda>_. x) m)
  = mdbNext_update (\<lambda>_. x) (mdb_node_to_H m)"
  unfolding mdb_node_to_H_def by simp

lemma mdb_node_to_H_mdbRevocable_update[simp]:
  "mdb_node_to_H (mdbRevocable_CL_update (\<lambda>_. x) m)
  = mdbRevocable_update (\<lambda>_. to_bool x) (mdb_node_to_H m)"
  unfolding mdb_node_to_H_def by simp

lemma mdb_node_to_H_mdbFirstBadged_update[simp]:
  "mdb_node_to_H (mdbFirstBadged_CL_update (\<lambda>_. x) m)
  = mdbFirstBadged_update (\<lambda>_. to_bool x) (mdb_node_to_H m)"
  unfolding mdb_node_to_H_def by simp

declare to_bool_from_bool [simp]

lemma mdbNext_to_H [simp]:
  "mdbNext (mdb_node_to_H n) = mdbNext_CL n"
  unfolding mdb_node_to_H_def
  by simp

lemma mdbPrev_to_H [simp]:
  "mdbPrev (mdb_node_to_H n) = mdbPrev_CL n"
  unfolding mdb_node_to_H_def
  by simp

lemmas ctes_of_not_0 [simp] = valid_mdbD3' [of s, rotated] for s

(* For getting rid of the generated guards -- will probably break with c_guard*)
lemma cte_bits_le_3 [simp]: "3 \<le> cte_level_bits"
  by (simp add: objBits_defs cte_level_bits_def)

lemma cte_bits_le_tcb_bits: "cte_level_bits \<le> tcbBlockSizeBits"
  by (simp add: cte_level_bits_def objBits_defs)

lemma ctes_of_aligned_bits:
  assumes pa: "pspace_aligned' s"
  and    cof: "ctes_of s p = Some cte"
  and   bits: "bits \<le> cte_level_bits"
  shows  "is_aligned p bits"
proof -
  from cof have "cte_wp_at' ((=) cte) p s"
    by (simp add: cte_wp_at_ctes_of)
  thus ?thesis
    apply -
    apply (rule is_aligned_weaken[OF _ bits])
    apply (erule cte_wp_atE')
     apply assumption
    apply (simp add: tcb_cte_cases_def field_simps cteSizeBits_def split: if_split_asm)
        apply (fastforce elim: aligned_add_aligned[OF _ _ cte_bits_le_tcb_bits]
                         simp: is_aligned_def cte_level_bits_def)+
    apply (erule is_aligned_weaken[OF _  cte_bits_le_tcb_bits])
    done
qed

lemma mdbNext_not_zero_eq:
  "cmdbnode_relation n n' \<Longrightarrow> \<forall>s s'. (s, s') \<in> rf_sr \<comment> \<open>ja \<and> (is_aligned (mdbNext n) 3)\<close>
  \<longrightarrow> (mdbNext n \<noteq> 0) = (s' \<in> {_. mdbNext_CL (mdb_node_lift n') \<noteq> 0})"
  by (fastforce elim: cmdbnode_relationE)

lemma mdbPrev_not_zero_eq:
  "cmdbnode_relation n n' \<Longrightarrow> \<forall>s s'. (s, s') \<in> rf_sr \<comment> \<open>ja\<and> (is_aligned (mdbPrev n) 3)\<close>
  \<longrightarrow> (mdbPrev n \<noteq> 0) = (s' \<in> {_. mdbPrev_CL (mdb_node_lift n') \<noteq> 0})"
  by (fastforce elim: cmdbnode_relationE)

abbreviation
  "nullCapPointers cte \<equiv> cteCap cte = NullCap \<and> mdbNext (cteMDBNode cte) = nullPointer \<and> mdbPrev (cteMDBNode cte) = nullPointer"

lemma nullCapPointers_def:
  "is_an_abbreviation" unfolding is_an_abbreviation_def by simp

lemma valid_mdb_ctes_of_next:
  "\<lbrakk> valid_mdb' s; ctes_of s p = Some cte; mdbNext (cteMDBNode cte) \<noteq> 0 \<rbrakk> \<Longrightarrow> cte_at' (mdbNext (cteMDBNode cte)) s"
  unfolding valid_mdb'_def valid_mdb_ctes_def
  apply (erule conjE)
  apply (erule (2) valid_dlistE)
  apply (simp add: cte_wp_at_ctes_of)
  done

lemma valid_mdb_ctes_of_prev:
  "\<lbrakk> valid_mdb' s; ctes_of s p = Some cte; mdbPrev (cteMDBNode cte) \<noteq> 0 \<rbrakk> \<Longrightarrow> cte_at' (mdbPrev (cteMDBNode cte)) s"
  unfolding valid_mdb'_def valid_mdb_ctes_def
  apply (erule conjE)
  apply (erule (2) valid_dlistE)
  apply (simp add: cte_wp_at_ctes_of)
  done

end

context kernel
begin

lemma cmap_relation_tcb [intro]:
  "(s, s') \<in> rf_sr \<Longrightarrow> cpspace_tcb_relation (ksPSpace s) (t_hrs_' (globals s'))"
  unfolding rf_sr_def state_relation_def cstate_relation_def cpspace_relation_def
  by (simp add: Let_def)

lemma cmap_relation_ep [intro]:
  "(s, s') \<in> rf_sr \<Longrightarrow> cpspace_ep_relation (ksPSpace s) (t_hrs_' (globals s'))"
  unfolding rf_sr_def state_relation_def cstate_relation_def cpspace_relation_def
  by (simp add: Let_def)

lemma cmap_relation_ntfn [intro]:
  "(s, s') \<in> rf_sr \<Longrightarrow> cpspace_ntfn_relation (ksPSpace s) (t_hrs_' (globals s'))"
  unfolding rf_sr_def state_relation_def cstate_relation_def cpspace_relation_def
  by (simp add: Let_def)

lemma cmap_relation_sched_context [intro]:
  "(s, s') \<in> rf_sr \<Longrightarrow> cpspace_sched_context_relation (ksPSpace s) (t_hrs_' (globals s'))"
  unfolding rf_sr_def state_relation_def cstate_relation_def cpspace_relation_def
  by (simp add: Let_def)

lemma cmap_relation_reply [intro]:
  "(s, s') \<in> rf_sr \<Longrightarrow> cpspace_reply_relation (ksPSpace s) (t_hrs_' (globals s'))"
  unfolding rf_sr_def state_relation_def cstate_relation_def cpspace_relation_def
  by (simp add: Let_def)

lemma cmap_relation_cte [intro]:
  "(s, s') \<in> rf_sr \<Longrightarrow> cpspace_cte_relation (ksPSpace s) (t_hrs_' (globals s'))"
  unfolding rf_sr_def state_relation_def cstate_relation_def cpspace_relation_def
  by (simp add: Let_def)

lemma rf_sr_cpspace_asidpool_relation:
  "(s, s') \<in> rf_sr
    \<Longrightarrow> cpspace_asidpool_relation (ksPSpace s) (t_hrs_' (globals s'))"
  by (clarsimp simp: rf_sr_def cstate_relation_def
                     cpspace_relation_def Let_def)

lemma rf_sr_cpte_relation:
  "(s, s') \<in> rf_sr \<Longrightarrow> cmap_relation (map_to_ptes (ksPSpace s))
                         (cslift s') pte_Ptr cpte_relation"
  by (clarsimp simp: rf_sr_def cstate_relation_def
                     Let_def cpspace_relation_def)

lemma rf_sr_cte_relation:
  "\<lbrakk> (s, s') \<in> rf_sr; ctes_of s src = Some cte; cslift s' (Ptr src) = Some cte' \<rbrakk> \<Longrightarrow> ccte_relation cte cte'"
  apply (drule cmap_relation_cte)
  apply (erule (2) cmap_relation_relI)
  done

lemma ccte_relation_ccap_relation:
  "ccte_relation cte cte' \<Longrightarrow> ccap_relation (cteCap cte) (cte_C.cap_C cte')"
  unfolding ccte_relation_def ccap_relation_def c_valid_cte_def cl_valid_cte_def c_valid_cap_def cl_valid_cap_def
  by (clarsimp simp: map_option_Some_eq2 if_bool_eq_conj)

lemma ccte_relation_cmdbnode_relation:
  "ccte_relation cte cte' \<Longrightarrow> cmdbnode_relation (cteMDBNode cte) (cte_C.cteMDBNode_C cte')"
  unfolding ccte_relation_def ccap_relation_def
  by (clarsimp simp: map_option_Some_eq2)

lemma rf_sr_ctes_of_clift:
  assumes sr: "(s, s') \<in> rf_sr"
  and    cof: "ctes_of s p = Some cte"
  shows "\<exists>cte'. cslift s' (Ptr p) = Some cte' \<and> cte_lift cte' \<noteq> None \<and> cte = cte_to_H (the (cte_lift cte'))
         \<and> c_valid_cte cte'"
proof -
  from sr have "cpspace_cte_relation (ksPSpace s) (t_hrs_' (globals s'))" ..
  thus ?thesis using cof
    apply (rule cspace_cte_relationE)
    apply clarsimp
    done
qed

lemma c_valid_cte_eq:
 "c_valid_cte c = case_option True cl_valid_cte (cte_lift c)"
 apply (clarsimp simp: c_valid_cte_def cl_valid_cte_def c_valid_cap_def  split: option.splits)
 apply (unfold cte_lift_def)
 apply simp
done

lemma rf_sr_ctes_of_cliftE:
  assumes cof: "ctes_of s p = Some cte"
  assumes sr: "(s, s') \<in> rf_sr"
  and     rl: "\<And>cte' ctel'. \<lbrakk>ctes_of s p = Some (cte_to_H ctel');
                        cslift s' (Ptr p) = Some cte';
                        cte_lift cte' = Some ctel';
                        cte = cte_to_H ctel' ;
                        cl_valid_cte ctel'\<rbrakk> \<Longrightarrow> R"
  shows "R"
  using sr cof
  apply -
  apply (frule (1) rf_sr_ctes_of_clift)
  apply (elim conjE exE)
  apply (rule rl)
      apply simp
     apply assumption
    apply clarsimp
   apply clarsimp
  apply (clarsimp simp: c_valid_cte_eq)
  done

lemma cstate_relation_only_t_hrs:
  "\<lbrakk> t_hrs_' s = t_hrs_' t;
  ksReadyQueues_' s = ksReadyQueues_' t;
  ksReadyQueuesL1Bitmap_' s = ksReadyQueuesL1Bitmap_' t;
  ksReadyQueuesL2Bitmap_' s = ksReadyQueuesL2Bitmap_' t;
  ksSchedulerAction_' s = ksSchedulerAction_' t;
  ksCurThread_' s = ksCurThread_' t;
  ksCurTime_' s = ksCurTime_' t;
  ksCurSC_' s = ksCurSC_' t;
  ksIdleThread_' s = ksIdleThread_' t;
  ksIdleSC_' s = ksIdleSC_' t;
  ksWorkUnitsCompleted_' s = ksWorkUnitsCompleted_' t;
  intStateIRQTable_' s = intStateIRQTable_' t;
  riscvKSASIDTable_' s = riscvKSASIDTable_' t;
  phantom_machine_state_' s = phantom_machine_state_' t;
  ghost'state_' s = ghost'state_' t;
  ksDomScheduleIdx_' s = ksDomScheduleIdx_' t;
  ksCurDomain_' s = ksCurDomain_' t;
  ksDomainTime_' s = ksDomainTime_' t;
  ksConsumed_' s = ksConsumed_' t;
  ksReleaseQueue_' s = ksReleaseQueue_' t;
  ksReprogram_' s = ksReprogram_' t
  \<rbrakk>
  \<Longrightarrow> cstate_relation a s = cstate_relation a t"
  unfolding cstate_relation_def
  by (clarsimp simp add: Let_def carch_state_relation_def cmachine_state_relation_def)

lemma rf_sr_upd:
  assumes
    "(t_hrs_' (globals x)) = (t_hrs_' (globals y))"
    "(ksReadyQueues_' (globals x)) = (ksReadyQueues_' (globals y))"
    "(ksReadyQueuesL1Bitmap_' (globals x)) = (ksReadyQueuesL1Bitmap_' (globals y))"
    "(ksReadyQueuesL2Bitmap_' (globals x)) = (ksReadyQueuesL2Bitmap_' (globals y))"
    "(ksSchedulerAction_' (globals x)) = (ksSchedulerAction_' (globals y))"
    "(ksCurThread_' (globals x)) = (ksCurThread_' (globals y))"
    "(ksCurTime_' (globals x)) = (ksCurTime_' (globals y))"
    "(ksCurSC_' (globals x)) = (ksCurSC_' (globals y))"
    "(ksIdleThread_' (globals x)) = (ksIdleThread_' (globals y))"
    "(ksIdleSC_' (globals x)) = (ksIdleSC_' (globals y))"
    "(ksWorkUnitsCompleted_' (globals x)) = (ksWorkUnitsCompleted_' (globals y))"
    "intStateIRQTable_'(globals x) = intStateIRQTable_' (globals y)"
    "riscvKSASIDTable_' (globals x) = riscvKSASIDTable_' (globals y)"
    "phantom_machine_state_' (globals x) = phantom_machine_state_' (globals y)"
    "ghost'state_' (globals x) = ghost'state_' (globals y)"
    "ksDomScheduleIdx_' (globals x) = ksDomScheduleIdx_' (globals y)"
    "ksCurDomain_' (globals x) = ksCurDomain_' (globals y)"
    "ksDomainTime_' (globals x) = ksDomainTime_' (globals y)"
    "ksConsumed_' (globals x) = ksConsumed_' (globals y)"
    "ksReleaseQueue_' (globals x) = ksReleaseQueue_' (globals y)"
    "ksReprogram_' (globals x) = ksReprogram_' (globals y)"
  shows "((a, x) \<in> rf_sr) = ((a, y) \<in> rf_sr)"
  unfolding rf_sr_def using assms
  by simp (rule cstate_relation_only_t_hrs, auto)

lemma rf_sr_upd_safe[simp]:
  assumes rl: "(t_hrs_' (globals (g y))) = (t_hrs_' (globals y))"
  and     rq: "(ksReadyQueues_' (globals (g y))) = (ksReadyQueues_' (globals y))"
  and     rqL1: "(ksReadyQueuesL1Bitmap_' (globals (g y))) = (ksReadyQueuesL1Bitmap_' (globals y))"
  and     rqL2: "(ksReadyQueuesL2Bitmap_' (globals (g y))) = (ksReadyQueuesL2Bitmap_' (globals y))"
  and     sa: "(ksSchedulerAction_' (globals (g y))) = (ksSchedulerAction_' (globals y))"
  and     ct: "(ksCurThread_' (globals (g y))) = (ksCurThread_' (globals y))"
  and  ctime: "(ksCurTime_' (globals (g y))) = (ksCurTime_' (globals y))"
  and    csc: "(ksCurSC_' (globals (g y))) = (ksCurSC_' (globals y))"
  and     it: "(ksIdleThread_' (globals (g y))) = (ksIdleThread_' (globals y))"
  and    isc: "(ksIdleSC_' (globals (g y))) = (ksIdleSC_' (globals y))"
  and     ist: "intStateIRQTable_'(globals (g y)) = intStateIRQTable_' (globals y)"
  and     dsi: "ksDomScheduleIdx_' (globals (g y)) = ksDomScheduleIdx_' (globals y)"
  and     cdom: "ksCurDomain_' (globals (g y)) = ksCurDomain_' (globals y)"
  and     dt: "ksDomainTime_' (globals (g y)) = ksDomainTime_' (globals y)"
  and   cons: "ksConsumed_' (globals (g y)) = ksConsumed_' (globals y)"
  and arch:
    "riscvKSASIDTable_' (globals (g y)) = riscvKSASIDTable_' (globals y)"
    "phantom_machine_state_' (globals (g y)) = phantom_machine_state_' (globals y)"
  and    gs: "ghost'state_' (globals (g y)) = ghost'state_' (globals y)"
  and     wu:  "(ksWorkUnitsCompleted_' (globals (g y))) = (ksWorkUnitsCompleted_' (globals y))"
  and  rlq: "(ksReleaseQueue_' (globals (g y))) = (ksReleaseQueue_' (globals y))"
  and reprog: "(ksReprogram_' (globals (g y))) = (ksReprogram_' (globals y))"
  shows "((a, (g y)) \<in> rf_sr) = ((a, y) \<in> rf_sr)"
  using rl rq rqL1 rqL2 sa ct ctime csc it isc ist arch wu gs dsi cdom dt cons rlq reprog
  by - (rule rf_sr_upd)

(* More of a well-formed lemma, but \<dots> *)
lemma valid_mdb_cslift_next:
  assumes vmdb: "valid_mdb' s"
  and       sr: "(s, s') \<in> rf_sr"
  and      cof: "ctes_of s p = Some cte"
  and       nz: "mdbNext (cteMDBNode cte) \<noteq> 0"
  shows "cslift s' (Ptr (mdbNext (cteMDBNode cte)) :: cte_C ptr) \<noteq> None"
proof -
  from vmdb cof nz obtain cten where
    "ctes_of s (mdbNext (cteMDBNode cte)) = Some cten"
    by (auto simp: cte_wp_at_ctes_of dest!: valid_mdb_ctes_of_next)

  with sr show ?thesis
    apply -
    apply (drule (1) rf_sr_ctes_of_clift)
    apply clarsimp
    done
qed

lemma valid_mdb_cslift_prev:
  assumes vmdb: "valid_mdb' s"
  and       sr: "(s, s') \<in> rf_sr"
  and      cof: "ctes_of s p = Some cte"
  and       nz: "mdbPrev (cteMDBNode cte) \<noteq> 0"
  shows "cslift s' (Ptr (mdbPrev (cteMDBNode cte)) :: cte_C ptr) \<noteq> None"
proof -
  from vmdb cof nz obtain cten where
    "ctes_of s (mdbPrev (cteMDBNode cte)) = Some cten"
    by (auto simp: cte_wp_at_ctes_of dest!: valid_mdb_ctes_of_prev)

  with sr show ?thesis
    apply -
    apply (drule (1) rf_sr_ctes_of_clift)
    apply clarsimp
    done
qed

lemma rf_sr_cte_at_valid:
  "\<lbrakk> cte_wp_at' P (ptr_val p) s; (s,s') \<in> rf_sr \<rbrakk> \<Longrightarrow> s' \<Turnstile>\<^sub>c (p :: cte_C ptr)"
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (drule (1) rf_sr_ctes_of_clift)
  apply (clarsimp simp add: typ_heap_simps)
  done

lemma rf_sr_cte_at_validD:
  "\<lbrakk> cte_wp_at' P p s; (s,s') \<in> rf_sr \<rbrakk> \<Longrightarrow> s' \<Turnstile>\<^sub>c (Ptr p :: cte_C ptr)"
  by (simp add: rf_sr_cte_at_valid)

(* MOVE *)
lemma ccap_relation_NullCap_iff:
  "(ccap_relation NullCap cap') = (cap_get_tag cap' = scast cap_null_cap)"
  unfolding ccap_relation_def
  by (clarsimp simp: map_option_Some_eq2 c_valid_cap_def cl_valid_cap_def
                     cap_to_H_def cap_lift_def Let_def cap_tag_defs
              split: if_split)

(* MOVE *)
lemma ntfn_blocked_in_queueD:
  "\<lbrakk> st_tcb_at' ((=) (Structures_H.thread_state.BlockedOnNotification ntfn)) thread \<sigma>;
     ko_at' ntfn' ntfn \<sigma>; invs' \<sigma> ; sym_refs (state_refs_of' \<sigma>)\<rbrakk>
   \<Longrightarrow> thread \<in> set (ntfnQueue (ntfnObj ntfn')) \<and> isWaitingNtfn (ntfnObj ntfn')"
  apply (drule sym_refs_st_tcb_atD')
   apply clarsimp
  apply (clarsimp simp: obj_at'_def ko_wp_at'_def
                        refs_of_rev'[where ko = "KONotification ntfn'", simplified])
  apply (cases "ntfnObj ntfn'")
    apply (simp_all add: isWaitingNtfn_def)
    done

(* MOVE *)
lemma valid_ntfn_isWaitingNtfnD:
  "\<lbrakk> valid_ntfn' ntfn s; isWaitingNtfn (ntfnObj ntfn) \<rbrakk>
  \<Longrightarrow> ntfnQueue (ntfnObj ntfn) \<noteq> [] \<and> (\<forall>t\<in>set (ntfnQueue (ntfnObj ntfn)). tcb_at' t s)"
  unfolding valid_ntfn'_def isWaitingNtfn_def
  by (clarsimp split: Structures_H.notification.splits ntfn.splits)

lemma cmap_relation_ko_atD:
  fixes ko :: "'a :: pspace_storable" and  mp :: "word32 \<rightharpoonup> 'a"
  assumes ps: "cmap_relation (projectKO_opt \<circ>\<^sub>m (ksPSpace s)) (cslift s') f rel"
  and     ko: "ko_at' ko ptr s"
  shows   "\<exists>ko'. cslift s' (f ptr) = Some ko' \<and> rel ko ko'"
  using ps ko unfolding cmap_relation_def
  apply clarsimp
  apply (drule bspec [where x = "ptr"])
   apply (clarsimp simp: obj_at'_def projectKOs)
  apply (clarsimp simp: obj_at'_def projectKOs)
  apply (drule equalityD1)
  apply (drule subsetD [where c = "f ptr"])
   apply (rule imageI)
   apply clarsimp
  apply clarsimp
  done

lemma cmap_relation_ko_atE:
  fixes ko :: "'a :: pspace_storable" and  mp :: "word32 \<rightharpoonup> 'a"
  assumes ps: "cmap_relation (projectKO_opt \<circ>\<^sub>m (ksPSpace s)) (cslift s') f rel"
  and     ko: "ko_at' ko ptr s"
  and     rl: "\<And>ko'. \<lbrakk>cslift s' (f ptr) = Some ko'; rel ko ko'\<rbrakk> \<Longrightarrow> P"
  shows   P
  using ps ko
  apply -
  apply (drule (1) cmap_relation_ko_atD)
  apply (clarsimp)
  apply (erule (1) rl)
  done

lemma ntfn_to_ep_queue:
  assumes ko: "ko_at' ntfn' ntfn s"
  and     waiting: "isWaitingNtfn (ntfnObj ntfn')"
  and     rf: "(s, s') \<in> rf_sr"
  shows "ep_queue_relation' (cslift s') (ntfnQueue (ntfnObj ntfn'))
              (Ptr (ntfnQueue_head_CL
                     (notification_lift (the (cslift s' (Ptr ntfn))))))
              (Ptr (ntfnQueue_tail_CL
                     (notification_lift (the (cslift s' (Ptr ntfn))))))"
proof -
  from rf have
    "cmap_relation (map_to_ntfns (ksPSpace s)) (cslift s') Ptr (cnotification_relation (cslift s'))"
    by (rule cmap_relation_ntfn)

  thus ?thesis using ko waiting
    apply -
    apply (erule (1) cmap_relation_ko_atE)
    apply (clarsimp simp: cnotification_relation_def Let_def isWaitingNtfn_def
                   split: Structures_H.notification.splits ntfn.splits)
    done
qed

lemma map_to_tcbs_from_tcb_at:
  "tcb_at' thread s \<Longrightarrow> map_to_tcbs (ksPSpace s) thread \<noteq> None"
  unfolding obj_at'_def
  by clarsimp

lemma map_to_scs_from_sc_at:
  "sc_at' thread s \<Longrightarrow> map_to_scs (ksPSpace s) thread \<noteq> None"
  unfolding obj_at'_def
  by clarsimp

lemma map_to_replies_from_reply_at:
  "reply_at' replyPtr s \<Longrightarrow> map_to_replies (ksPSpace s) replyPtr \<noteq> None"
  unfolding obj_at'_def
  by clarsimp

(* FIXME RT: generalise to other kernel object types *)
lemma dom_eq:
  "\<exists>ko. ko_at' (ko :: sched_context) p s \<Longrightarrow>
   dom (map_to_scs ((ksPSpace s)(p \<mapsto> KOSchedContext ko))) = dom (map_to_scs (ksPSpace s))"
  apply (clarsimp simp: dom_def map_comp_def)
  by (fastforce simp: obj_at'_def split: if_splits kernel_object.splits)

lemma tcb_at_h_t_valid:
  "\<lbrakk> tcb_at' thread s; (s, s') \<in> rf_sr \<rbrakk> \<Longrightarrow> s' \<Turnstile>\<^sub>c tcb_ptr_to_ctcb_ptr thread"
  apply (drule cmap_relation_tcb)
  apply (drule map_to_tcbs_from_tcb_at)
  apply (clarsimp simp add: cmap_relation_def)
  apply (drule (1) bspec [OF _ domI])
  apply (clarsimp simp add: dom_def tcb_ptr_to_ctcb_ptr_def image_def)
  apply (drule equalityD1)
  apply (drule subsetD)
   apply simp
   apply (rule exI [where x = thread])
   apply simp
  apply (clarsimp simp: typ_heap_simps)
  done

lemma st_tcb_at_h_t_valid:
  "\<lbrakk> st_tcb_at' P thread s; (s, s') \<in> rf_sr \<rbrakk> \<Longrightarrow> s' \<Turnstile>\<^sub>c tcb_ptr_to_ctcb_ptr thread"
  apply (drule pred_tcb_at')
  apply (erule (1) tcb_at_h_t_valid)
  done

lemma sc_at_h_t_valid:
  "\<lbrakk> sc_at' scPtr s; (s, s') \<in> rf_sr \<rbrakk> \<Longrightarrow> s' \<Turnstile>\<^sub>c PTR(sched_context_C) scPtr"
  apply (drule cmap_relation_sched_context)
  apply (drule map_to_scs_from_sc_at)
  apply (clarsimp simp add: cmap_relation_def)
  apply (drule (1) bspec [OF _ domI])
  apply (clarsimp simp add: dom_def tcb_ptr_to_ctcb_ptr_def image_def)
  apply (drule equalityD1)
  apply (drule subsetD)
   apply simp
   apply (rule exI [where x = scPtr])
   apply simp
  apply (clarsimp simp: typ_heap_simps)
  done

lemma reply_at_h_t_valid:
  "\<lbrakk> reply_at' replyPtr s; (s, s') \<in> rf_sr \<rbrakk> \<Longrightarrow> s' \<Turnstile>\<^sub>c reply_Ptr replyPtr"
  apply (drule cmap_relation_reply)
  apply (drule map_to_replies_from_reply_at)
  apply (clarsimp simp add: cmap_relation_def)
  apply (drule (1) bspec [OF _ domI])
  apply (clarsimp simp add: dom_def image_def)
  apply (drule equalityD1)
  apply (drule subsetD)
   apply simp
   apply (rule exI [where x = replyPtr])
   apply simp
  apply (clarsimp simp: typ_heap_simps)
  done

(* MOVE *)
lemma exs_getObject:
  assumes x: "\<And>q n ko. loadObject p q n ko =
                (loadObject_default p q n ko :: 'a :: pspace_storable kernel_r)"
  and objat: "obj_at' (P :: ('a::pspace_storable \<Rightarrow> bool)) p s"
  shows      "\<lbrace>(=) s\<rbrace> getObject p \<exists>\<lbrace>\<lambda>r :: 'a :: pspace_storable. (=) s\<rbrace>"
  using objat unfolding exs_valid_def obj_at'_def
  apply clarsimp
  apply (rule_tac x = "(the (projectKO_opt ko), s)" in bexI)
   apply (clarsimp simp: split_def)
  apply (simp split: option.splits)
  apply (clarsimp simp: loadObject_default_def getObject_def in_monad return_def lookupAround2_char1
                        split_def x objBits_def[symmetric] project_inject
                        readObject_def ogets_def oassert_opt_def
                 split: option.splits)
  by (fastforce simp: word_le_less_eq)

lemma setObject_modify_variable_size:
  fixes v :: "'a :: pspace_storable" shows
  "\<lbrakk>obj_at' (P :: 'a \<Rightarrow> bool) p s; updateObject v = updateObject_default v;
    (1 :: machine_word) < 2 ^ objBits v; obj_at' (\<lambda>obj. objBits v = objBits obj) p s\<rbrakk>
   \<Longrightarrow> setObject p v s = modify (ksPSpace_update (\<lambda>ps. ps (p \<mapsto> injectKO v))) s"
  apply (clarsimp simp: setObject_def split_def exec_gets obj_at'_def lookupAround2_known1
                        assert_opt_def updateObject_default_def bind_assoc)
  apply (simp add: projectKO_def alignCheck_assert)
  apply (simp add: project_inject objBits_def)
  apply (clarsimp simp only: koTypeOf_injectKO)
  apply (frule in_magnitude_check[where s'=s])
    apply blast
   apply fastforce
  apply (simp add: magnitudeCheck_assert in_monad bind_def gets_def oassert_opt_def
                   get_def return_def)
  apply (simp add: simpler_modify_def)
  done

lemma setObject_modify:
  fixes v :: "'a :: pspace_storable" shows
  "\<lbrakk>obj_at' (P :: 'a \<Rightarrow> bool) p s; updateObject v = updateObject_default v;
    (1 :: machine_word) < 2 ^ objBits v; \<And>ko. P ko \<Longrightarrow> objBits ko = objBits v \<rbrakk>
   \<Longrightarrow> setObject p v s = modify (ksPSpace_update (\<lambda>ps. ps (p \<mapsto> injectKO v))) s"
  apply (rule setObject_modify_variable_size)
     apply fastforce
    apply fastforce
  apply fastforce
  unfolding obj_at'_def
  by fastforce

lemma getObject_return:
  fixes v :: "'a :: pspace_storable" shows
  "\<lbrakk> \<And>q n ko. loadObject p q n ko =
                (loadObject_default p q n ko :: 'a :: pspace_storable kernel_r);
     ko_at' v p s; (1 :: machine_word) < 2 ^ objBits v \<rbrakk> \<Longrightarrow>
   getObject p s = return v s"
  apply (clarsimp simp: getObject_def readObject_def omonad_defs split_def gets_the_def gets_def
                        get_def bind_def return_def assert_opt_def fail_def obj_at'_def
                        lookupAround2_known1 loadObject_default_def in_omonad
                 split: option.splits)
  by (fastforce simp add: project_inject objBits_def)

lemmas getObject_return_tcb
    = getObject_return[OF meta_eq_to_obj_eq, OF loadObject_tcb,
                       unfolded objBits_simps, simplified]

lemmas setObject_modify_tcb
    = setObject_modify[OF _ meta_eq_to_obj_eq, OF _ updateObject_tcb,
                       unfolded objBits_simps, simplified]

lemma setObject_eq_variable_size:
  fixes v :: "'a :: pspace_storable" shows
  "\<lbrakk>obj_at' (P :: 'a \<Rightarrow> bool) p s; updateObject v = updateObject_default v;
   (1 :: machine_word) < 2 ^ objBits v; obj_at' (\<lambda>obj. objBits v = objBits obj) p s\<rbrakk>
   \<Longrightarrow> ((), s\<lparr> ksPSpace := (ksPSpace s)(p \<mapsto> injectKO v)\<rparr>) \<in> fst (setObject p v s)"
  apply (frule (3) setObject_modify_variable_size)
  by (clarsimp simp: modify_def get_def bind_def put_def)

lemma setObject_eq:
  fixes ko :: "'a :: pspace_storable"
  assumes x: "\<And>(val :: 'a) old ptr ptr' next. updateObject val old ptr ptr' next =
                (updateObject_default val old ptr ptr' next :: kernel_object kernel)"
  assumes P: "\<And>v::'a::pspace_storable. (1 :: machine_word) < 2 ^ (objBits v)"
  and     ob: "\<And>(v :: 'a) (v' :: 'a). objBits v = objBits v'"
  and objat: "obj_at' (P :: ('a::pspace_storable \<Rightarrow> bool)) p s"
  shows  "((), s\<lparr> ksPSpace := (ksPSpace s)(p \<mapsto> injectKO ko)\<rparr>) \<in> fst (setObject p ko s)"
  apply (rule setObject_eq_variable_size)
     apply (fastforce intro: objat)
    apply (fastforce intro: x)
   apply (fastforce intro: P)
  apply (insert ob objat)
  unfolding obj_at'_def
  by fastforce

lemma getObject_eq:
  fixes ko :: "'a :: pspace_storable"
  assumes x: "\<And>q n ko. loadObject p q n ko =
                (loadObject_default p q n ko :: 'a :: pspace_storable kernel_r)"
  and objat: "ko_at' ko p s"
  shows      "(ko, s) \<in> fst (getObject p s)"
  using objat unfolding exs_valid_def obj_at'_def
  apply clarsimp
  apply (clarsimp simp: loadObject_default_def getObject_def in_monad return_def lookupAround2_char1
                        split_def x objBits_def[symmetric] project_inject
                        readObject_def ogets_def oassert_opt_def
                 split: option.splits)
  by (fastforce simp: word_le_less_eq)

lemma threadSet_eq:
  "ko_at' tcb thread s \<Longrightarrow>
  ((), s\<lparr> ksPSpace := (ksPSpace s)(thread \<mapsto> injectKO (f tcb))\<rparr>) \<in> fst (threadSet f thread s)"
  unfolding threadSet_def
  apply (clarsimp simp add: in_monad)
  apply (rule exI)
  apply (rule exI)
  apply (rule conjI)
   apply (rule getObject_eq)
    apply simp
   apply (simp add: objBits_simps')
  apply (frule setObject_eq_variable_size)
     apply simp
    apply (clarsimp simp: objBits_simps')
   apply (clarsimp simp: obj_at_simps)
   apply (rule_tac x=tcb in exI)
   apply simp
  apply simp
  done

definition
  "tcb_null_ep_ptrs a \<equiv> a \<lparr> tcbEPNext_C := NULL, tcbEPPrev_C := NULL \<rparr>"

definition
  "tcb_null_sched_ptrs a \<equiv> a \<lparr> tcbSchedNext_C := NULL, tcbSchedPrev_C := NULL \<rparr>"

definition
  "tcb_null_queue_ptrs a \<equiv> a \<lparr> tcbSchedNext_C := NULL, tcbSchedPrev_C := NULL, tcbEPNext_C := NULL, tcbEPPrev_C := NULL\<rparr>"

lemma null_sched_queue:
  "map_option tcb_null_sched_ptrs \<circ> mp = map_option tcb_null_sched_ptrs \<circ> mp'
  \<Longrightarrow> map_option tcb_null_queue_ptrs \<circ> mp = map_option tcb_null_queue_ptrs \<circ> mp'"
  apply (rule ext)
  apply (erule_tac x = x in map_option_comp_eqE)
   apply simp
  apply (clarsimp simp: tcb_null_queue_ptrs_def tcb_null_sched_ptrs_def)
  done

lemma null_ep_queue:
  "map_option tcb_null_ep_ptrs \<circ> mp = map_option tcb_null_ep_ptrs \<circ> mp'
  \<Longrightarrow> map_option tcb_null_queue_ptrs \<circ> mp = map_option tcb_null_queue_ptrs \<circ> mp'"
  apply (rule ext)
  apply (erule_tac x = x in map_option_comp_eqE)
   apply simp
  apply (case_tac v, case_tac v')
  apply (clarsimp simp: tcb_null_queue_ptrs_def tcb_null_ep_ptrs_def)
  done

lemma null_sched_epD:
  assumes om: "map_option tcb_null_sched_ptrs \<circ> mp = map_option tcb_null_sched_ptrs \<circ> mp'"
  shows "map_option tcbEPNext_C \<circ> mp = map_option tcbEPNext_C \<circ> mp' \<and>
         map_option tcbEPPrev_C \<circ> mp = map_option tcbEPPrev_C \<circ> mp'"
  using om
  apply -
  apply (rule conjI)
   apply (rule ext)
   apply (erule_tac x = x in map_option_comp_eqE )
    apply simp
   apply (case_tac v, case_tac v')
   apply (clarsimp simp: tcb_null_sched_ptrs_def)
  apply (rule ext)
  apply (erule_tac x = x in map_option_comp_eqE )
   apply simp
  apply (case_tac v, case_tac v')
  apply (clarsimp simp: tcb_null_sched_ptrs_def)
  done

lemma null_ep_schedD:
  assumes om: "map_option tcb_null_ep_ptrs \<circ> mp = map_option tcb_null_ep_ptrs \<circ> mp'"
  shows "map_option tcbSchedNext_C \<circ> mp = map_option tcbSchedNext_C \<circ> mp' \<and>
         map_option tcbSchedPrev_C \<circ> mp = map_option tcbSchedPrev_C \<circ> mp'"
  using om
  apply -
  apply (rule conjI)
   apply (rule ext)
   apply (erule_tac x = x in map_option_comp_eqE )
    apply simp
   apply (case_tac v, case_tac v')
   apply (clarsimp simp: tcb_null_ep_ptrs_def)
  apply (rule ext)
  apply (erule_tac x = x in map_option_comp_eqE )
   apply simp
  apply (case_tac v, case_tac v')
  apply (clarsimp simp: tcb_null_ep_ptrs_def)
  done

lemma cmap_relation_cong:
  assumes adom: "dom am = dom am'"
  and     cdom: "dom cm = dom cm'"
  and   rel: "\<And>p a a' b b'.
  \<lbrakk> am p = Some a; am' p = Some a'; cm (f p) = Some b; cm' (f p) = Some b' \<rbrakk> \<Longrightarrow> rel a b = rel' a' b'"
  shows "cmap_relation am cm f rel = cmap_relation am' cm' f rel'"
  unfolding cmap_relation_def
  apply (clarsimp simp: adom cdom)
  apply (rule iffI)
   apply simp
   apply (erule conjE)
   apply (drule equalityD1)
   apply (rule ballI)
   apply (drule (1) bspec)
   apply (erule iffD1 [OF rel, rotated -1])
      apply (rule Some_the, erule ssubst [OF adom])
     apply (erule Some_the)
    apply (rule Some_the [where f = cm])
    apply (drule subsetD)
     apply (erule imageI)
    apply (simp add: cdom)
   apply (rule Some_the [where f = cm'])
   apply (erule subsetD)
   apply (erule imageI)
  \<comment> \<open>clag\<close>
   apply simp
   apply (erule conjE)
   apply (drule equalityD1)
   apply (rule ballI)
   apply (drule (1) bspec)
   apply (erule iffD2 [OF rel, rotated -1])
      apply (rule Some_the, erule ssubst [OF adom])
     apply (erule Some_the)
    apply (rule Some_the [where f = cm])
    apply (drule subsetD)
     apply (erule imageI)
    apply (simp add: cdom)
   apply (rule Some_the [where f = cm'])
   apply (erule subsetD)
   apply (erule imageI)
   done

lemma ctcb_relation_null_ep_ptrs:
  assumes rel: "cmap_relation mp mp' tcb_ptr_to_ctcb_ptr ctcb_relation"
  and same: "map_option tcb_null_ep_ptrs \<circ> mp'' = map_option tcb_null_ep_ptrs \<circ> mp'"
  shows "cmap_relation mp mp'' tcb_ptr_to_ctcb_ptr ctcb_relation"
  using rel
  apply (rule iffD1 [OF cmap_relation_cong, OF _ map_option_eq_dom_eq, rotated -1])
    apply simp
   apply (rule same [symmetric])
  apply (drule compD [OF same])
  apply (case_tac b, case_tac b')
  apply (simp add: ctcb_relation_def tcb_null_ep_ptrs_def)
  done

lemma map_to_ctes_upd_tcb_no_ctes:
  "\<lbrakk>ko_at' tcb thread s ; \<forall>x\<in>ran tcb_cte_cases. (\<lambda>(getF, setF). getF tcb' = getF tcb) x \<rbrakk>
  \<Longrightarrow> map_to_ctes ((ksPSpace s)(thread \<mapsto> KOTCB tcb')) = map_to_ctes (ksPSpace s)"
  apply (erule obj_atE')
  apply (simp add: projectKOs objBits_simps)
  apply (subst map_to_ctes_upd_tcb')
     apply assumption+
  apply (rule ext)
  apply (clarsimp split: if_split)
  apply (drule (1) bspec [OF _ ranI])
  apply simp
  done

lemma update_ntfn_map_tos:
  fixes P :: "Structures_H.notification \<Rightarrow> bool"
  assumes at: "obj_at' P p s"
  shows   "map_to_eps ((ksPSpace s)(p \<mapsto> KONotification ko)) = map_to_eps (ksPSpace s)"
  and     "map_to_scs ((ksPSpace s)(p \<mapsto> KONotification ko)) = map_to_scs (ksPSpace s)"
  and     "map_to_replies ((ksPSpace s)(p \<mapsto> KONotification ko)) = map_to_replies (ksPSpace s)"
  and     "map_to_tcbs ((ksPSpace s)(p \<mapsto> KONotification ko)) = map_to_tcbs (ksPSpace s)"
  and     "map_to_ctes ((ksPSpace s)(p \<mapsto> KONotification ko)) = map_to_ctes (ksPSpace s)"
  and     "map_to_ptes ((ksPSpace s)(p \<mapsto> KONotification ko)) = map_to_ptes (ksPSpace s)"
  and     "map_to_asidpools ((ksPSpace s)(p \<mapsto> KONotification ko)) = map_to_asidpools (ksPSpace s)"
  and     "map_to_user_data ((ksPSpace s)(p \<mapsto> KONotification ko)) = map_to_user_data (ksPSpace s)"
  and     "map_to_user_data_device ((ksPSpace s)(p \<mapsto> KONotification ko)) = map_to_user_data_device (ksPSpace s)"
  using at
  by (auto elim!: obj_atE' intro!: map_to_ctes_upd_other map_comp_eqI
    simp: projectKOs projectKO_opts_defs split: kernel_object.splits if_split_asm)+

lemma update_ep_map_tos:
  fixes P :: "endpoint \<Rightarrow> bool"
  assumes at: "obj_at' P p s"
  shows   "map_to_ntfns ((ksPSpace s)(p \<mapsto> KOEndpoint ko)) = map_to_ntfns (ksPSpace s)"
  and     "map_to_scs ((ksPSpace s)(p \<mapsto> KOEndpoint ko)) = map_to_scs (ksPSpace s)"
  and     "map_to_replies ((ksPSpace s)(p \<mapsto> KOEndpoint ko)) = map_to_replies (ksPSpace s)"
  and     "map_to_tcbs ((ksPSpace s)(p \<mapsto> KOEndpoint ko)) = map_to_tcbs (ksPSpace s)"
  and     "map_to_ctes ((ksPSpace s)(p \<mapsto> KOEndpoint ko)) = map_to_ctes (ksPSpace s)"
  and     "map_to_ptes ((ksPSpace s)(p \<mapsto> KOEndpoint ko)) = map_to_ptes (ksPSpace s)"
  and     "map_to_asidpools ((ksPSpace s)(p \<mapsto> KOEndpoint ko)) = map_to_asidpools (ksPSpace s)"
  and     "map_to_user_data ((ksPSpace s)(p \<mapsto> KOEndpoint ko)) = map_to_user_data (ksPSpace s)"
  and     "map_to_user_data_device ((ksPSpace s)(p \<mapsto> KOEndpoint ko)) = map_to_user_data_device (ksPSpace s)"
  using at
  by (auto elim!: obj_atE' intro!: map_to_ctes_upd_other map_comp_eqI
    simp: projectKOs projectKO_opts_defs split: kernel_object.splits if_split_asm)+

lemma update_tcb_map_tos:
  fixes P :: "tcb \<Rightarrow> bool"
  assumes at: "obj_at' P p s"
  shows   "map_to_eps ((ksPSpace s)(p \<mapsto> KOTCB ko)) = map_to_eps (ksPSpace s)"
  and     "map_to_ntfns ((ksPSpace s)(p \<mapsto> KOTCB ko)) = map_to_ntfns (ksPSpace s)"
  and     "map_to_scs ((ksPSpace s)(p \<mapsto> KOTCB ko)) = map_to_scs (ksPSpace s)"
  and     "map_to_replies ((ksPSpace s)(p \<mapsto> KOTCB ko)) = map_to_replies (ksPSpace s)"
  and     "map_to_ptes ((ksPSpace s)(p \<mapsto> KOTCB ko)) = map_to_ptes (ksPSpace s)"
  and     "map_to_asidpools ((ksPSpace s)(p \<mapsto> KOTCB ko)) = map_to_asidpools (ksPSpace s)"
  and     "map_to_user_data ((ksPSpace s)(p \<mapsto> KOTCB ko)) = map_to_user_data (ksPSpace s)"
  and     "map_to_user_data_device ((ksPSpace s)(p \<mapsto> KOTCB ko)) = map_to_user_data_device (ksPSpace s)"
  using at
  by (auto elim!: obj_atE' intro!: map_to_ctes_upd_other map_comp_eqI
    simp: projectKOs projectKO_opts_defs split: kernel_object.splits if_split_asm)+

lemma update_scs_map_tos:
  fixes P :: "sched_context \<Rightarrow> bool"
  assumes at: "obj_at' P p s"
  shows   "map_to_eps ((ksPSpace s)(p \<mapsto> KOSchedContext ko)) = map_to_eps (ksPSpace s)"
  and     "map_to_ntfns ((ksPSpace s)(p \<mapsto> KOSchedContext ko)) = map_to_ntfns (ksPSpace s)"
  and     "map_to_tcbs ((ksPSpace s)(p \<mapsto> KOSchedContext ko)) = map_to_tcbs (ksPSpace s)"
  and     "map_to_ctes ((ksPSpace s)(p \<mapsto> KOSchedContext ko)) = map_to_ctes (ksPSpace s)"
  and     "map_to_replies ((ksPSpace s)(p \<mapsto> KOSchedContext ko)) = map_to_replies (ksPSpace s)"
  and     "map_to_ptes ((ksPSpace s)(p \<mapsto> KOSchedContext ko)) = map_to_ptes (ksPSpace s)"
  and     "map_to_asidpools ((ksPSpace s)(p \<mapsto> KOSchedContext ko)) = map_to_asidpools (ksPSpace s)"
  and     "map_to_user_data ((ksPSpace s)(p \<mapsto> KOSchedContext ko)) = map_to_user_data (ksPSpace s)"
  and     "map_to_user_data_device ((ksPSpace s)(p \<mapsto> KOSchedContext ko)) = map_to_user_data_device (ksPSpace s)"
  using at
  by (auto elim!: obj_atE' intro!: map_to_ctes_upd_other map_comp_eqI
    simp: projectKOs projectKO_opts_defs split: kernel_object.splits if_split_asm)+

lemma update_replies_map_tos:
  fixes P :: "reply \<Rightarrow> bool"
  assumes at: "obj_at' P p s"
  shows   "map_to_eps ((ksPSpace s)(p \<mapsto> KOReply ko)) = map_to_eps (ksPSpace s)"
  and     "map_to_ntfns ((ksPSpace s)(p \<mapsto> KOReply ko)) = map_to_ntfns (ksPSpace s)"
  and     "map_to_tcbs ((ksPSpace s)(p \<mapsto> KOReply ko)) = map_to_tcbs (ksPSpace s)"
  and     "map_to_scs ((ksPSpace s)(p \<mapsto> KOReply ko)) = map_to_scs (ksPSpace s)"
  and     "map_to_ctes ((ksPSpace s)(p \<mapsto> KOReply ko)) = map_to_ctes (ksPSpace s)"
  and     "map_to_ptes ((ksPSpace s)(p \<mapsto> KOReply ko)) = map_to_ptes (ksPSpace s)"
  and     "map_to_asidpools ((ksPSpace s)(p \<mapsto> KOReply ko)) = map_to_asidpools (ksPSpace s)"
  and     "map_to_user_data ((ksPSpace s)(p \<mapsto> KOReply ko)) = map_to_user_data (ksPSpace s)"
  and     "map_to_user_data_device ((ksPSpace s)(p \<mapsto> KOReply ko)) = map_to_user_data_device (ksPSpace s)"
  using at
  by (auto elim!: obj_atE' intro!: map_to_ctes_upd_other map_comp_eqI
            simp: projectKOs projectKO_opts_defs split: kernel_object.splits if_split_asm)+

lemma update_asidpool_map_tos:
  fixes P :: "asidpool \<Rightarrow> bool"
  assumes at: "obj_at' P p s"
  shows   "map_to_ntfns ((ksPSpace s)(p \<mapsto> KOArch (KOASIDPool ap))) = map_to_ntfns (ksPSpace s)"
  and     "map_to_scs ((ksPSpace s)(p \<mapsto> KOArch (KOASIDPool ap))) = map_to_scs (ksPSpace s)"
  and     "map_to_replies ((ksPSpace s)(p \<mapsto> KOArch (KOASIDPool ap))) = map_to_replies (ksPSpace s)"
  and     "map_to_tcbs ((ksPSpace s)(p \<mapsto> KOArch (KOASIDPool ap))) = map_to_tcbs (ksPSpace s)"
  and     "map_to_ctes ((ksPSpace s)(p \<mapsto> KOArch (KOASIDPool ap))) = map_to_ctes (ksPSpace s)"
  and     "map_to_ptes ((ksPSpace s)(p \<mapsto> KOArch (KOASIDPool ap))) = map_to_ptes (ksPSpace s)"
  and     "map_to_eps  ((ksPSpace s)(p \<mapsto> KOArch (KOASIDPool ap))) = map_to_eps (ksPSpace s)"
  and     "map_to_user_data ((ksPSpace s)(p \<mapsto> KOArch (KOASIDPool ap))) = map_to_user_data (ksPSpace s)"
  and     "map_to_user_data_device ((ksPSpace s)(p \<mapsto> KOArch (KOASIDPool ap))) = map_to_user_data_device (ksPSpace s)"
  using at
  by (auto elim!: obj_atE' intro!: map_to_ctes_upd_other map_comp_eqI
      simp: projectKOs projectKO_opts_defs
     split: if_split if_split_asm Structures_H.kernel_object.split_asm
            arch_kernel_object.split_asm)

lemma update_asidpool_map_to_asidpools:
  "map_to_asidpools ((ksPSpace s)(p \<mapsto> KOArch (KOASIDPool ap)))
             = (map_to_asidpools (ksPSpace s))(p \<mapsto> ap)"
  by (rule ext, clarsimp simp: projectKOs map_comp_def split: if_split)

lemma update_pte_map_to_ptes:
  "map_to_ptes ((ksPSpace s)(p \<mapsto> KOArch (KOPTE pte)))
             = (map_to_ptes (ksPSpace s))(p \<mapsto> pte)"
  by (rule ext, clarsimp simp: projectKOs map_comp_def split: if_split)

lemma update_pte_map_tos:
  fixes P :: "pte \<Rightarrow> bool"
  assumes at: "obj_at' P p s"
  shows   "map_to_ntfns ((ksPSpace s)(p \<mapsto> (KOArch (KOPTE pte)))) = map_to_ntfns (ksPSpace s)"
  and     "map_to_tcbs ((ksPSpace s)(p \<mapsto> (KOArch (KOPTE pte)))) = map_to_tcbs (ksPSpace s)"
  and     "map_to_ctes ((ksPSpace s)(p \<mapsto> (KOArch (KOPTE pte)))) = map_to_ctes (ksPSpace s)"
  and     "map_to_eps  ((ksPSpace s)(p \<mapsto> (KOArch (KOPTE pte)))) = map_to_eps (ksPSpace s)"
  and     "map_to_scs  ((ksPSpace s)(p \<mapsto> (KOArch (KOPTE pte)))) = map_to_scs (ksPSpace s)"
  and     "map_to_replies  ((ksPSpace s)(p \<mapsto> (KOArch (KOPTE pte)))) = map_to_replies (ksPSpace s)"
  and     "map_to_asidpools ((ksPSpace s)(p \<mapsto> (KOArch (KOPTE pte)))) = map_to_asidpools (ksPSpace s)"
  and     "map_to_user_data ((ksPSpace s)(p \<mapsto> (KOArch (KOPTE pte)))) = map_to_user_data (ksPSpace s)"
  and     "map_to_user_data_device ((ksPSpace s)(p \<mapsto> (KOArch (KOPTE pte)))) = map_to_user_data_device (ksPSpace s)"
  using at
  by (auto elim!: obj_atE' intro!: map_comp_eqI map_to_ctes_upd_other
           split: if_split_asm if_split
            simp: projectKOs,
       auto simp: projectKO_opts_defs)

lemma heap_to_page_data_cong [cong]:
  "\<lbrakk> map_to_user_data ks = map_to_user_data ks'; bhp = bhp' \<rbrakk>
  \<Longrightarrow> heap_to_user_data ks bhp = heap_to_user_data ks' bhp'"
  unfolding heap_to_user_data_def by simp

lemma heap_to_device_data_cong [cong]:
  "\<lbrakk> map_to_user_data_device ks = map_to_user_data_device ks'; bhp = bhp' \<rbrakk>
  \<Longrightarrow> heap_to_device_data ks bhp = heap_to_device_data ks' bhp'"
  unfolding heap_to_device_data_def by simp

lemma map_leD:
  "\<lbrakk> map_le m m'; m x = Some y \<rbrakk> \<Longrightarrow> m' x = Some y"
  by (simp add: map_le_def dom_def)

lemma region_is_bytes_disjoint:
  assumes cleared: "region_is_bytes' p n (hrs_htd hrs)"
    and not_byte: "typ_uinfo_t TYPE('a :: wf_type) \<noteq> typ_uinfo_t TYPE(word8)"
  shows "hrs_htd hrs \<Turnstile>\<^sub>t (p' :: 'a ptr)
    \<Longrightarrow> {p ..+ n} \<inter> {ptr_val p' ..+ size_of TYPE('a)} = {}"
  apply (clarsimp simp: h_t_valid_def valid_footprint_def Let_def)
  apply (clarsimp simp: set_eq_iff dest!: intvlD[where p="ptr_val p'"])
  apply (drule_tac x="of_nat k" in spec, clarsimp simp: size_of_def)
  apply (cut_tac m=k in typ_slice_t_self[where td="typ_uinfo_t TYPE('a)"])
  apply (clarsimp simp: in_set_conv_nth)
  apply (drule_tac x=i in map_leD, simp)
  apply (simp add: cleared[unfolded region_is_bytes'_def] not_byte size_of_def)
  done

lemma region_actually_is_bytes:
  "region_actually_is_bytes' ptr len htd
    \<Longrightarrow> region_is_bytes' ptr len htd"
  by (simp add: region_is_bytes'_def region_actually_is_bytes'_def
         split: if_split)

lemma zero_ranges_are_zero_update[simp]:
  "h_t_valid (hrs_htd hrs) c_guard (ptr :: 'a ptr)
    \<Longrightarrow> typ_uinfo_t TYPE('a :: wf_type) \<noteq> typ_uinfo_t TYPE(word8)
    \<Longrightarrow> zero_ranges_are_zero rs (hrs_mem_update (heap_update ptr v) hrs)
        = zero_ranges_are_zero rs hrs"
  apply (clarsimp simp: zero_ranges_are_zero_def hrs_mem_update
        intro!: ball_cong[OF refl] conj_cong[OF refl])
  apply (drule region_actually_is_bytes)
  apply (drule(2) region_is_bytes_disjoint)
  apply (simp add: heap_update_def heap_list_update_disjoint_same Int_commute)
  done

lemma inj_tcb_ptr_to_ctcb_ptr [simp]:
  "inj tcb_ptr_to_ctcb_ptr"
  apply (rule injI)
  apply (simp add: tcb_ptr_to_ctcb_ptr_def)
  done

lemmas tcb_ptr_to_ctcb_ptr_eq [simp] = inj_eq [OF inj_tcb_ptr_to_ctcb_ptr]

lemma obj_at_cslift_tcb:
  fixes P :: "tcb \<Rightarrow> bool"
  shows "\<lbrakk>obj_at' P thread s; (s, s') \<in> rf_sr\<rbrakk> \<Longrightarrow>
  \<exists>ko ko'. ko_at' ko thread s \<and> P ko \<and>
        cslift s' (tcb_ptr_to_ctcb_ptr thread) = Some ko' \<and>
        ctcb_relation ko ko'"
  apply (frule obj_at_ko_at')
  apply clarsimp
  apply (frule cmap_relation_tcb)
  apply (drule (1) cmap_relation_ko_atD)
  apply fastforce
  done

lemma obj_at_cslift_sc:
  fixes P :: "sched_context \<Rightarrow> bool"
  shows "\<lbrakk>obj_at' P sc s; (s, s') \<in> rf_sr\<rbrakk> \<Longrightarrow>
  \<exists>ko ko'. ko_at' ko sc s \<and> P ko \<and>
        cslift s' (Ptr sc) = Some ko' \<and>
        csched_context_relation ko ko'"
  apply (frule obj_at_ko_at')
  apply clarsimp
  apply (frule cmap_relation_sched_context)
  apply (drule (1) cmap_relation_ko_atD)
  apply fastforce
  done

lemma obj_at_cslift_reply:
  fixes P :: "reply \<Rightarrow> bool"
  shows "\<lbrakk>obj_at' P replyPtr s; (s, s') \<in> rf_sr\<rbrakk>
         \<Longrightarrow> \<exists>ko ko'. ko_at' ko replyPtr s \<and> P ko \<and> cslift s' (Ptr replyPtr) = Some ko'
                      \<and> creply_relation ko ko'"
  apply (frule obj_at_ko_at')
  apply clarsimp
  apply (frule cmap_relation_reply)
  apply (drule (1) cmap_relation_ko_atD)
  apply fastforce
  done

fun
  thread_state_to_tsType :: "thread_state \<Rightarrow> machine_word"
where
  "thread_state_to_tsType (Structures_H.Running) = scast ThreadState_Running"
  | "thread_state_to_tsType (Structures_H.Restart) = scast ThreadState_Restart"
  | "thread_state_to_tsType (Structures_H.Inactive) = scast ThreadState_Inactive"
  | "thread_state_to_tsType (Structures_H.IdleThreadState) = scast ThreadState_IdleThreadState"
  | "thread_state_to_tsType (Structures_H.BlockedOnReply oref) = scast ThreadState_BlockedOnReply"
  | "thread_state_to_tsType (Structures_H.BlockedOnReceive oref cg ro) = scast ThreadState_BlockedOnReceive"
  | "thread_state_to_tsType (Structures_H.BlockedOnSend oref badge cg cgr isc) = scast ThreadState_BlockedOnSend"
  | "thread_state_to_tsType (Structures_H.BlockedOnNotification oref) = scast ThreadState_BlockedOnNotification"

lemma ctcb_relation_thread_state_to_tsType:
  "ctcb_relation tcb ctcb \<Longrightarrow> tsType_CL (thread_state_lift (tcbState_C ctcb)) = thread_state_to_tsType (tcbState tcb)"
  unfolding ctcb_relation_def cthread_state_relation_def
  by (cases "(tcbState tcb)", simp_all)


lemma tcb_ptr_to_tcb_ptr [simp]:
  "tcb_ptr_to_ctcb_ptr (ctcb_ptr_to_tcb_ptr x) = x"
  unfolding tcb_ptr_to_ctcb_ptr_def ctcb_ptr_to_tcb_ptr_def
  by simp

lemma ctcb_ptr_to_ctcb_ptr [simp]:
  "ctcb_ptr_to_tcb_ptr (tcb_ptr_to_ctcb_ptr x) = x"
  unfolding ctcb_ptr_to_tcb_ptr_def tcb_ptr_to_ctcb_ptr_def
  by simp

declare ucast_id [simp]

definition
  cap_rights_from_word_canon :: "machine_word \<Rightarrow> seL4_CapRights_CL"
  where
  "cap_rights_from_word_canon wd \<equiv>
    \<lparr> capAllowGrantReply_CL = from_bool (wd !! 3),
      capAllowGrant_CL = from_bool (wd !! 2),
      capAllowRead_CL = from_bool (wd !! 1),
      capAllowWrite_CL = from_bool (wd !! 0)\<rparr>"

definition
  cap_rights_from_word :: "machine_word \<Rightarrow> seL4_CapRights_CL"
  where
  "cap_rights_from_word wd \<equiv> SOME cr.
   to_bool (capAllowGrantReply_CL cr) = wd !! 3 \<and>
   to_bool (capAllowGrant_CL cr) = wd !! 2 \<and>
   to_bool (capAllowRead_CL cr) = wd !! 1 \<and>
   to_bool (capAllowWrite_CL cr) = wd !! 0"

lemma cap_rights_to_H_from_word [simp]:
  "cap_rights_to_H (cap_rights_from_word wd) = rightsFromWord wd"
  unfolding cap_rights_from_word_def rightsFromWord_def
  apply (rule someI2_ex)
   apply (rule exI [where x = "cap_rights_from_word_canon wd"])
   apply (simp add: cap_rights_from_word_canon_def)
  apply (simp add: cap_rights_to_H_def)
  done

lemma cmap_relation_updI2:
  fixes am :: "machine_word \<rightharpoonup> 'a" and cm :: "'b typ_heap"
  assumes cr: "cmap_relation am cm f rel"
  and   cof: "am dest = None"
  and   cc:  "rel nv nv'"
  and   inj: "inj f"
  shows "cmap_relation (am(dest \<mapsto> nv)) (cm(f dest \<mapsto> nv')) f rel"
  using cr cof cc inj
  by (clarsimp simp add: cmap_relation_def inj_eq split: if_split)

lemma rf_sr_heap_user_data_relation:
  "(s, s') \<in> rf_sr \<Longrightarrow> cmap_relation
      (heap_to_user_data (ksPSpace s) (underlying_memory (ksMachineState s)))
      (cslift s') Ptr cuser_user_data_relation"
  by (clarsimp simp: user_word_at_def rf_sr_def
                     cstate_relation_def Let_def
                     cpspace_relation_def)

lemma rf_sr_heap_device_data_relation:
  "(s, s') \<in> rf_sr \<Longrightarrow> cmap_relation
      (heap_to_device_data (ksPSpace s) (underlying_memory (ksMachineState s)))
      (cslift s') Ptr cuser_user_data_device_relation"
  by (clarsimp simp: user_word_at_def rf_sr_def
                     cstate_relation_def Let_def
                     cpspace_relation_def)

lemma user_word_at_cross_over:
  "\<lbrakk> user_word_at x p s; (s, s') \<in> rf_sr; p' = Ptr p \<rbrakk>
   \<Longrightarrow> c_guard p' \<and> hrs_htd (t_hrs_' (globals s')) \<Turnstile>\<^sub>t p'
         \<and> h_val (hrs_mem (t_hrs_' (globals s'))) p' = x"
  apply (drule rf_sr_heap_user_data_relation)
  apply (erule cmap_relationE1)
   apply (clarsimp simp: heap_to_user_data_def Let_def
                         user_word_at_def pointerInUserData_def
                         typ_at_to_obj_at'[where 'a=user_data, simplified])
   apply (drule obj_at_ko_at', clarsimp)
   apply (rule conjI, rule exI, erule ko_at_projectKO_opt)
   apply (rule refl)
  apply (thin_tac "heap_to_user_data a b c = d" for a b c d)
  apply (cut_tac x=p and w="~~ mask pageBits" in word_plus_and_or_coroll2)
  apply (rule conjI)
   apply (clarsimp simp: user_word_at_def pointerInUserData_def)
   apply (simp add: c_guard_def c_null_guard_def ptr_aligned_def)
   apply (drule lift_t_g)
   apply (clarsimp simp: )
   apply (simp add: align_of_def size_of_def)
   apply (fold is_aligned_def[where n=3, simplified], simp)
   apply (erule contra_subsetD[rotated])
   apply (rule order_trans[rotated])
    apply (rule_tac x="p && mask pageBits" and y=8 in intvl_sub_offset)
    apply (cut_tac y=p and a="mask pageBits && (~~ mask 3)" in word_and_le1)
    apply (subst(asm) word_bw_assocs[symmetric], subst(asm) is_aligned_neg_mask_eq,
           erule is_aligned_andI1)
    apply (simp add: word_le_nat_alt mask_def pageBits_def)
   apply simp
  apply (clarsimp simp: cuser_user_data_relation_def user_word_at_def)
  apply (frule_tac f="[''words_C'']" in h_t_valid_field[OF h_t_valid_clift],
         simp+)
  apply (drule_tac n="uint (p && mask pageBits >> 3)" in h_t_valid_Array_element)
    apply simp
   apply (simp add: shiftr_over_and_dist mask_def pageBits_def uint_and)
   apply (insert int_and_leR [where a="uint (p >> 3)" and b=511], clarsimp)[1]
  apply (simp add: field_lvalue_def
            field_lookup_offset_eq[OF trans, OF _ arg_cong[where f=Some, symmetric], OF _ prod.collapse]
            word_shift_by_3 shiftr_shiftl1 is_aligned_andI1)
  apply (drule_tac x="ucast (p >> 3)" in spec)
  apply (simp add: byte_to_word_heap_def Let_def ucast_ucast_mask)
  apply (fold shiftl_t2n[where n=3, simplified, simplified mult.commute mult.left_commute])
  apply (simp add: aligned_shiftr_mask_shiftl pageBits_def)
  apply (rule trans[rotated], rule_tac hp="hrs_mem (t_hrs_' (globals s'))"
                                   and x="Ptr &(Ptr (p && ~~ mask 12) \<rightarrow> [''words_C''])"
                                    in access_in_array)
     apply (rule trans)
      apply (erule typ_heap_simps)
       apply simp+
    apply (rule order_less_le_trans, rule unat_lt2p)
    apply simp
   apply (fastforce simp add: typ_info_word)
  apply simp
  apply (rule_tac f="h_val hp" for hp in arg_cong)
  apply simp
  apply (simp add: field_lvalue_def)
  apply (simp add: ucast_nat_def ucast_ucast_mask)
  apply (fold shiftl_t2n[where n=3, simplified, simplified mult.commute mult.left_commute])
  apply (simp add: aligned_shiftr_mask_shiftl)
  done

lemma memory_cross_over:
  "\<lbrakk>(\<sigma>, s) \<in> rf_sr; pspace_aligned' \<sigma>; pspace_distinct' \<sigma>;
    pointerInUserData ptr \<sigma>\<rbrakk>
   \<Longrightarrow> fst (t_hrs_' (globals s)) ptr = underlying_memory (ksMachineState \<sigma>) ptr"
  apply (subgoal_tac " c_guard (Ptr (ptr && ~~ mask 3)::machine_word ptr) \<and>
    s \<Turnstile>\<^sub>c (Ptr (ptr && ~~ mask 3)::machine_word ptr) \<and> h_val (hrs_mem (t_hrs_' (globals s))) (Ptr (ptr && ~~ mask 3)) = x" for x)
  prefer 2
   apply (drule_tac p="ptr && ~~ mask 3" in user_word_at_cross_over[rotated])
     apply simp
    apply (simp add: user_word_at_def Aligned.is_aligned_neg_mask
                     pointerInUserData_def pageBits_def mask_lower_twice)
    apply assumption
  apply (clarsimp simp: h_val_def from_bytes_def typ_info_word)
  apply (drule_tac f="word_rsplit :: machine_word \<Rightarrow> word8 list" in arg_cong)
  apply (simp add: word_rsplit_rcat_size word_size)
  apply (drule_tac f="\<lambda>xs. xs ! unat (ptr && mask 3)" in arg_cong)
  apply (simp add: heap_list_nth unat_mask_3_less_8
                   word_plus_and_or_coroll2 add.commute
                   hrs_mem_def)
  apply (cut_tac p=ptr in unat_mask_3_less_8)
  apply (subgoal_tac "(ptr && ~~ mask 3) + (ptr && mask 3) = ptr")
   apply (subgoal_tac "!n x. n < 8 \<longrightarrow> (unat (x::machine_word) = n) = (x = of_nat n)")
    apply (clarsimp simp: eval_nat_numeral)
    apply (fastforce simp: add.commute elim!: less_SucE)
   apply (clarsimp simp: unat64_eq_of_nat word_bits_def)
  apply (simp add: add.commute word_plus_and_or_coroll2)
  done

lemma cap_get_tag_isCap_ArchObject0:
  assumes cr: "ccap_relation (capability.ArchObjectCap cap) cap'"
  shows "(cap_get_tag cap' = scast cap_asid_control_cap) = isASIDControlCap cap
  \<and> (cap_get_tag cap' = scast cap_asid_pool_cap) = isASIDPoolCap cap
  \<and> (cap_get_tag cap' = scast cap_page_table_cap) = isPageTableCap cap
  \<and> (cap_get_tag cap' = scast cap_frame_cap) = (isFrameCap cap)"
  using cr
  apply -
  apply (erule ccap_relationE)
  apply (simp add: cap_to_H_def cap_lift_def Let_def isArchCap_def)
  by (clarsimp simp: isCap_simps cap_tag_defs word_le_nat_alt Let_def split: if_split_asm) \<comment> \<open>takes a while\<close>

lemma cap_get_tag_isCap_ArchObject:
  assumes cr: "ccap_relation (capability.ArchObjectCap cap) cap'"
  shows "(cap_get_tag cap' = scast cap_asid_control_cap) = isASIDControlCap cap"
  and "(cap_get_tag cap' = scast cap_asid_pool_cap) = isASIDPoolCap cap"
  and "(cap_get_tag cap' = scast cap_page_table_cap) = isPageTableCap cap"
  and "(cap_get_tag cap' = scast cap_frame_cap) = (isFrameCap cap)"
  using cap_get_tag_isCap_ArchObject0 [OF cr] by auto

lemma cap_get_tag_isCap_unfolded_H_cap:
  shows "ccap_relation (capability.ThreadCap v0) cap' \<Longrightarrow> (cap_get_tag cap' = scast cap_thread_cap)"
  and "ccap_relation (capability.NullCap) cap' \<Longrightarrow> (cap_get_tag cap' = scast cap_null_cap)"
  and "ccap_relation (capability.NotificationCap v4 v5 v6 v7) cap' \<Longrightarrow> (cap_get_tag cap' = scast cap_notification_cap) "
  and "ccap_relation (capability.EndpointCap v8 v9 v10 v10b v11 v12) cap' \<Longrightarrow> (cap_get_tag cap' = scast cap_endpoint_cap)"
  and "ccap_relation (capability.IRQHandlerCap v13) cap' \<Longrightarrow> (cap_get_tag cap' = scast cap_irq_handler_cap)"
  and "ccap_relation (capability.IRQControlCap) cap' \<Longrightarrow> (cap_get_tag cap' = scast cap_irq_control_cap)"
  and "ccap_relation (capability.Zombie v14 v15 v16) cap' \<Longrightarrow> (cap_get_tag cap' = scast cap_zombie_cap)"
  and "ccap_relation (capability.ReplyCap v17 v18) cap' \<Longrightarrow> (cap_get_tag cap' = scast cap_reply_cap)"
  and "ccap_relation (capability.UntypedCap v100 v19 v20 v20b) cap' \<Longrightarrow> (cap_get_tag cap' = scast cap_untyped_cap)"
  and "ccap_relation (capability.CNodeCap v21 v22 v23 v24) cap' \<Longrightarrow> (cap_get_tag cap' = scast cap_cnode_cap)"
  and "ccap_relation (capability.DomainCap) cap' \<Longrightarrow> (cap_get_tag cap' = scast cap_domain_cap)"
  and "ccap_relation (capability.SchedContextCap v25 v26) cap' \<Longrightarrow> (cap_get_tag cap' = scast cap_sched_context_cap)"
  and "ccap_relation (capability.SchedControlCap) cap' \<Longrightarrow> (cap_get_tag cap' = scast cap_sched_control_cap)"

  and "ccap_relation (capability.ArchObjectCap arch_capability.ASIDControlCap) cap' \<Longrightarrow> (cap_get_tag cap' = scast cap_asid_control_cap)"
  and "ccap_relation (capability.ArchObjectCap (arch_capability.ASIDPoolCap v28 v29)) cap' \<Longrightarrow> (cap_get_tag cap' = scast cap_asid_pool_cap)"
  and "ccap_relation (capability.ArchObjectCap (arch_capability.PageTableCap v30 v31)) cap' \<Longrightarrow> (cap_get_tag cap' = scast cap_page_table_cap)"
  and "ccap_relation (capability.ArchObjectCap (arch_capability.FrameCap v101 v44 v45 v46 v47)) cap'  \<Longrightarrow> (cap_get_tag cap' = scast cap_frame_cap)"
  apply (simp add: cap_get_tag_isCap cap_get_tag_isCap_ArchObject isCap_simps)
  apply (frule cap_get_tag_isCap(2), simp)
  apply (simp add: cap_get_tag_isCap cap_get_tag_isCap_ArchObject isCap_simps)+
  done

lemma cap_get_tag_isCap_ArchObject2_worker:
  "\<lbrakk> \<And>cap''. ccap_relation (ArchObjectCap cap'') cap' \<Longrightarrow> (cap_get_tag cap' = n) = P cap'';
                ccap_relation cap cap'; isArchCap_tag n \<rbrakk>
        \<Longrightarrow> (cap_get_tag cap' = n)
              = (isArchObjectCap cap \<and> P (capCap cap))"
  apply (rule iffI)
   apply (clarsimp simp: cap_get_tag_isCap isCap_simps)
  apply (clarsimp simp: isCap_simps)
  done

lemma cap_get_tag_isCap_ArchObject2:
  assumes cr: "ccap_relation cap cap'"
  shows "(cap_get_tag cap' = scast cap_asid_control_cap)
           = (isArchObjectCap cap \<and> isASIDControlCap (capCap cap))"
  and   "(cap_get_tag cap' = scast cap_asid_pool_cap)
           = (isArchObjectCap cap \<and> isASIDPoolCap (capCap cap))"
  and   "(cap_get_tag cap' = scast cap_page_table_cap)
           = (isArchObjectCap cap \<and> isPageTableCap (capCap cap))"
  and   "(cap_get_tag cap' = scast cap_frame_cap)
           = (isArchObjectCap cap \<and> isFrameCap (capCap cap))"
  by (rule cap_get_tag_isCap_ArchObject2_worker [OF _ cr],
      simp add: cap_get_tag_isCap_ArchObject,
      simp add: isArchCap_tag_def2 cap_tag_defs)+

schematic_goal cap_frame_cap_lift_def':
  "cap_get_tag cap = SCAST(32 signed \<rightarrow> 64) cap_frame_cap
    \<Longrightarrow> cap_frame_cap_lift cap =
         \<lparr>capFMappedASID_CL = ?mapped_asid,
          capFBasePtr_CL = ?base_ptr,
          capFSize_CL = ?frame_size,
          capFVMRights_CL = ?vm_rights,
          capFIsDevice_CL = ?is_device,
          capFMappedAddress_CL = ?mapped_address\<rparr>"
  by (simp add: cap_frame_cap_lift_def cap_lift_def cap_tag_defs)

lemmas ccap_rel_cap_get_tag_cases_generic =
  cap_get_tag_isCap_unfolded_H_cap(1-13)
    [OF back_subst[of "\<lambda>cap. ccap_relation cap cap'" for cap']]

lemmas ccap_rel_cap_get_tag_cases_arch =
  cap_get_tag_isCap_unfolded_H_cap(14-17)
    [OF back_subst[of "\<lambda>cap. ccap_relation (ArchObjectCap cap) cap'" for cap'],
     OF back_subst[of "\<lambda>cap. ccap_relation cap cap'" for cap']]

lemmas ccap_rel_cap_get_tag_cases_arch' =
  ccap_rel_cap_get_tag_cases_arch[OF _ refl]

lemmas cap_lift_defs =
       cap_untyped_cap_lift_def
       cap_endpoint_cap_lift_def
       cap_notification_cap_lift_def
       cap_reply_cap_lift_def
       cap_sched_context_cap_lift_def
       cap_sched_control_cap_lift_def
       cap_cnode_cap_lift_def
       cap_thread_cap_lift_def
       cap_irq_handler_cap_lift_def
       cap_zombie_cap_lift_def
       cap_frame_cap_lift_def
       cap_page_table_cap_lift_def
       cap_asid_pool_cap_lift_def

lemma cap_lift_Some_CapD:
  "\<And>c'. cap_lift c = Some (Cap_untyped_cap c') \<Longrightarrow> cap_get_tag c = SCAST(32 signed \<rightarrow> 64) cap_untyped_cap"
  "\<And>c'. cap_lift c = Some (Cap_endpoint_cap c') \<Longrightarrow> cap_get_tag c = SCAST(32 signed \<rightarrow> 64) cap_endpoint_cap"
  "\<And>c'. cap_lift c = Some (Cap_notification_cap c') \<Longrightarrow> cap_get_tag c = SCAST(32 signed \<rightarrow> 64) cap_notification_cap"
  "\<And>c'. cap_lift c = Some (Cap_reply_cap c') \<Longrightarrow> cap_get_tag c = SCAST(32 signed \<rightarrow> 64) cap_reply_cap"
  "\<And>c'. cap_lift c = Some (Cap_sched_context_cap c') \<Longrightarrow> cap_get_tag c = SCAST(32 signed \<rightarrow> 64) cap_sched_context_cap"
  "\<And>c'. cap_lift c = Some (Cap_sched_control_cap c') \<Longrightarrow> cap_get_tag c = SCAST(32 signed \<rightarrow> 64) cap_sched_control_cap"
  "\<And>c'. cap_lift c = Some (Cap_cnode_cap c') \<Longrightarrow> cap_get_tag c = SCAST(32 signed \<rightarrow> 64) cap_cnode_cap"
  "\<And>c'. cap_lift c = Some (Cap_thread_cap c') \<Longrightarrow> cap_get_tag c = SCAST(32 signed \<rightarrow> 64) cap_thread_cap"
  "\<And>c'. cap_lift c = Some (Cap_irq_handler_cap c') \<Longrightarrow> cap_get_tag c = SCAST(32 signed \<rightarrow> 64) cap_irq_handler_cap"
  "\<And>c'. cap_lift c = Some (Cap_zombie_cap c') \<Longrightarrow> cap_get_tag c = SCAST(32 signed \<rightarrow> 64) cap_zombie_cap"
  "\<And>c'. cap_lift c = Some (Cap_frame_cap c') \<Longrightarrow> cap_get_tag c = SCAST(32 signed \<rightarrow> 64) cap_frame_cap"
  "\<And>c'. cap_lift c = Some (Cap_page_table_cap c') \<Longrightarrow> cap_get_tag c = SCAST(32 signed \<rightarrow> 64) cap_page_table_cap"
  "\<And>c'. cap_lift c = Some (Cap_asid_pool_cap c') \<Longrightarrow> cap_get_tag c = SCAST(32 signed \<rightarrow> 64) cap_asid_pool_cap"
  by (auto simp: cap_lifts cap_lift_defs)

lemma rf_sr_riscvKSGlobalPT:
  "(s, s') \<in> rf_sr \<Longrightarrow> riscvKSGlobalPT (ksArchState s) = ptr_val riscvKSGlobalPT_Ptr"
  by (clarsimp simp: rf_sr_def cstate_relation_def Let_def carch_state_relation_def
                     carch_globals_riscvKSGlobalPT)

lemma ghost_assertion_size_logic':
  "unat (sz :: machine_word) \<le> gsMaxObjectSize s
    \<Longrightarrow> cstate_relation s gs
    \<Longrightarrow> gs_get_assn cap_get_capSizeBits_'proc (ghost'state_' gs) = 0 \<or>
            sz \<le> gs_get_assn cap_get_capSizeBits_'proc (ghost'state_' gs)"
  by (clarsimp simp: rf_sr_def cstate_relation_def Let_def ghost_size_rel_def
                     linorder_not_le word_less_nat_alt)

lemma ghost_assertion_size_logic:
  "unat (sz :: machine_word) \<le> gsMaxObjectSize s
    \<Longrightarrow> (s, \<sigma>) \<in> rf_sr
    \<Longrightarrow> gs_get_assn cap_get_capSizeBits_'proc (ghost'state_' (globals \<sigma>)) = 0 \<or>
            sz \<le> gs_get_assn cap_get_capSizeBits_'proc (ghost'state_' (globals \<sigma>))"
  by (clarsimp simp: rf_sr_def ghost_assertion_size_logic')

lemma gs_set_assn_Delete_cstate_relation:
  "cstate_relation s (ghost'state_'_update (gs_set_assn cteDeleteOne_'proc v) gs)
    = cstate_relation s gs"
  apply (cases "ghost'state_' gs")
  by (auto simp: rf_sr_def cstate_relation_def Let_def carch_state_relation_def
                 cmachine_state_relation_def ghost_assertion_data_set_def
                 ghost_size_rel_def ghost_assertion_data_get_def
                 cteDeleteOne_'proc_def cap_get_capSizeBits_'proc_def refill_buffer_relation_def)

lemma ptr_val_tcb_ptr_mask:
  "obj_at' (P :: tcb \<Rightarrow> bool) thread s
      \<Longrightarrow> ptr_val (tcb_ptr_to_ctcb_ptr thread) && (~~ mask tcbBlockSizeBits)
                  = thread"
  apply (clarsimp simp: obj_at'_def tcb_ptr_to_ctcb_ptr_def)
  apply (simp add: is_aligned_add_helper ctcb_offset_defs objBits_simps')
  done

lemmas ptr_val_tcb_ptr_mask'[simp]
    = ptr_val_tcb_ptr_mask[unfolded mask_def tcbBlockSizeBits_def, simplified]

lemma typ_uinfo_t_diff_from_typ_name:
  "typ_name (typ_info_t TYPE ('a :: c_type)) \<noteq> typ_name (typ_info_t TYPE('b :: c_type))
    \<Longrightarrow> typ_uinfo_t (aty :: 'a itself) \<noteq> typ_uinfo_t (bty :: 'b itself)"
  by (clarsimp simp: typ_uinfo_t_def td_diff_from_typ_name)

declare ptr_add_assertion'[simp] typ_uinfo_t_diff_from_typ_name[simp]

lemma clift_array_assertion_imp:
  "clift hrs (p :: (('a :: wf_type)['b :: finite]) ptr) = Some v
    \<Longrightarrow> htd = hrs_htd hrs
    \<Longrightarrow> n \<noteq> 0
    \<Longrightarrow> \<exists>i. p' = ptr_add (ptr_coerce p) (int i)
        \<and> i + n \<le> CARD('b)
    \<Longrightarrow> array_assertion (p' :: 'a ptr) n htd"
  apply clarsimp
  apply (drule h_t_valid_clift)
  apply (drule array_ptr_valid_array_assertionD)
  apply (drule_tac j=i in array_assertion_shrink_leftD, simp)
  apply (erule array_assertion_shrink_right)
  apply simp
  done

lemma page_table_at_carray_map_relation:
  "\<lbrakk> page_table_at' pt s; cpspace_pte_array_relation (ksPSpace s) hp \<rbrakk>
    \<Longrightarrow> clift hp (pt_Ptr pt) \<noteq> None"
  apply (clarsimp simp: carray_map_relation_def h_t_valid_clift_Some_iff)
  apply (drule spec, erule iffD1)
  apply (clarsimp simp: page_table_at'_def objBits_simps)
  apply (drule_tac x="ucast (p' && mask ptBits >> pte_bits)" in spec)
  apply (clarsimp simp: shiftr_shiftl1 mask_pt_bits_inner_beauty)
  apply (clarsimp simp: typ_at_to_obj_at_arches
                 dest!: obj_at_ko_at' ko_at_projectKO_opt)
  done

lemma page_table_at_rf_sr:
   "\<lbrakk> page_table_at' pd s; (s, s') \<in> rf_sr \<rbrakk>
    \<Longrightarrow> cslift s' (Ptr pd :: (pte_C[512]) ptr) \<noteq> None"
  by (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                     cpspace_relation_def page_table_at_carray_map_relation)

lemma gsUntypedZeroRanges_rf_sr:
  "\<lbrakk> (start, end) \<in> gsUntypedZeroRanges s; (s, s') \<in> rf_sr \<rbrakk>
    \<Longrightarrow> region_actually_is_zero_bytes start (unat ((end + 1) - start)) s'"
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                        zero_ranges_are_zero_def)
  apply (drule(1) bspec)
  apply clarsimp
  done

lemma ctes_of_untyped_zero_rf_sr:
  "\<lbrakk> ctes_of s p = Some cte; (s, s') \<in> rf_sr;
      untyped_ranges_zero' s;
      untypedZeroRange (cteCap cte) = Some (start, end) \<rbrakk>
    \<Longrightarrow> region_actually_is_zero_bytes start (unat ((end + 1) - start)) s'"
  apply (erule gsUntypedZeroRanges_rf_sr[rotated])
  apply (clarsimp simp: untyped_ranges_zero_inv_def)
  apply (rule_tac a=p in ranI)
  apply (simp add: map_comp_def cteCaps_of_def)
  done

lemma heap_list_is_zero_mono:
  "heap_list_is_zero hmem p n \<Longrightarrow> n' \<le> n
    \<Longrightarrow> heap_list_is_zero hmem p n'"
  apply (induct n arbitrary: n' p)
   apply simp
  apply clarsimp
  apply (case_tac n', simp_all)
  done

lemma heap_list_h_eq_better:
  "\<And>p. \<lbrakk> x \<in> {p..+q}; heap_list h q p = heap_list h' q p \<rbrakk>
      \<Longrightarrow> h x = h' x"
proof (induct q)
  case 0 thus ?case by simp
next
  case (Suc n) thus ?case by (force dest: intvl_neq_start)
qed

lemma heap_list_is_zero_mono2:
  "heap_list_is_zero hmem p n
    \<Longrightarrow> {p' ..+ n'} \<le> {p ..+ n}
    \<Longrightarrow> heap_list_is_zero hmem p' n'"
  using heap_list_h_eq2[where h'="\<lambda>_. 0"]
      heap_list_h_eq_better[where h'="\<lambda>_. 0"]
  apply (simp(no_asm_use) add: heap_list_rpbs)
  apply blast
  done

lemma invs_urz[elim!]:
  "invs' s \<Longrightarrow> untyped_ranges_zero' s"
  by (clarsimp simp: invs'_def)

lemma arch_fault_tag_not_fault_tag_simps [simp]:
  "(arch_fault_to_fault_tag arch_fault = scast seL4_Fault_CapFault) = False"
  "(arch_fault_to_fault_tag arch_fault = scast seL4_Fault_UserException) = False"
  "(arch_fault_to_fault_tag arch_fault = scast seL4_Fault_UnknownSyscall) = False"
  "(arch_fault_to_fault_tag arch_fault = scast seL4_Fault_Timeout) = False"
  by (cases arch_fault ; simp add: seL4_Faults seL4_Arch_Faults)+

lemma capTCBPtr_eq:
  "\<lbrakk> ccap_relation cap cap'; isThreadCap cap \<rbrakk>
     \<Longrightarrow> cap_thread_cap_CL.capTCBPtr_CL (cap_thread_cap_lift cap')
           = ptr_val (tcb_ptr_to_ctcb_ptr (capTCBPtr cap))"
  apply (simp add: cap_get_tag_isCap[symmetric])
  apply (drule(1) cap_get_tag_to_H)
  apply clarsimp
  done

lemma rf_sr_ctcb_queue_relation:
  "\<lbrakk> (s, s') \<in> rf_sr; d \<le> maxDomain; p \<le> maxPriority \<rbrakk>
  \<Longrightarrow> ctcb_queue_relation (ksReadyQueues s (d, p))
                          (index (ksReadyQueues_' (globals s')) (cready_queues_index_to_C d p))"
  unfolding rf_sr_def cstate_relation_def cready_queues_relation_def
  apply (clarsimp simp: Let_def seL4_MinPrio_def minDom_def maxDom_to_H maxPrio_to_H)
  done

lemma rf_sr_ctcb_queue_relation_release_queue:
  "(s, s') \<in> rf_sr \<Longrightarrow> ctcb_queue_relation (ksReleaseQueue s) (ksReleaseQueue_' (globals s'))"
  unfolding rf_sr_def cstate_relation_def cready_queues_relation_def
  by (clarsimp simp: Let_def seL4_MinPrio_def minDom_def maxDom_to_H maxPrio_to_H)

lemma rf_sr_sched_action_relation:
  "(s, s') \<in> rf_sr
   \<Longrightarrow> cscheduler_action_relation (ksSchedulerAction s) (ksSchedulerAction_' (globals s'))"
  by (clarsimp simp: rf_sr_def cstate_relation_def Let_def)

lemma rf_sr_refill_buffer_relation[intro]:
  "(s, s') \<in> rf_sr \<Longrightarrow>
   refill_buffer_relation (ksPSpace s) (t_hrs_' (globals s')) (ghost'state_' (globals s'))"
  by (clarsimp simp: rf_sr_def cstate_relation_def Let_def)

lemma canonical_address_tcb_ptr:
  "\<lbrakk>canonical_address t; is_aligned t tcbBlockSizeBits\<rbrakk> \<Longrightarrow>
     canonical_address (ptr_val (tcb_ptr_to_ctcb_ptr t))"
  apply (clarsimp simp: tcb_ptr_to_ctcb_ptr_def)
  apply (erule canonical_address_add)
    apply (clarsimp simp: objBits_simps' ctcb_offset_defs canonical_bit_def)+
  done

lemma canonical_address_ctcb_ptr:
  assumes "canonical_address (ctcb_ptr_to_tcb_ptr t)" "is_aligned (ctcb_ptr_to_tcb_ptr t) tcbBlockSizeBits"
  shows "canonical_address (ptr_val t)"
proof -
  from assms(2)[unfolded ctcb_ptr_to_tcb_ptr_def]
  have "canonical_address ((ptr_val t - ctcb_offset) + ctcb_offset)"
    apply (rule canonical_address_add; simp add: objBits_simps' ctcb_offset_defs canonical_bit_def)
    using assms(1)
    by (simp add: ctcb_ptr_to_tcb_ptr_def ctcb_offset_defs)
  thus ?thesis by simp
qed

lemma tcb_and_not_mask_canonical:
  "\<lbrakk>pspace_canonical' s; tcb_at' t s; n < tcbBlockSizeBits\<rbrakk> \<Longrightarrow>
    tcb_Ptr (sign_extend canonical_bit (ptr_val (tcb_ptr_to_ctcb_ptr t) && ~~ mask n)) =
        tcb_ptr_to_ctcb_ptr t"
  apply (frule (1) obj_at'_is_canonical)
  apply (drule canonical_address_tcb_ptr)
   apply (clarsimp simp: obj_at'_def objBits_simps' split: if_splits)
  apply (clarsimp simp: canonical_address_sign_extended sign_extended_iff_sign_extend)
  apply (subgoal_tac "ptr_val (tcb_ptr_to_ctcb_ptr t) && ~~ mask n = ptr_val (tcb_ptr_to_ctcb_ptr t)")
   prefer 2
   apply (simp add: tcb_ptr_to_ctcb_ptr_def ctcb_offset_defs)
   apply (rule is_aligned_neg_mask_eq)
   apply (clarsimp simp: obj_at'_def objBits_simps')
   apply (rule is_aligned_add)
    apply (erule is_aligned_weaken, simp)
   apply (rule is_aligned_weaken[where x="tcbBlockSizeBits - 1"])
    apply (simp add: is_aligned_def objBits_simps')
   apply (simp add: objBits_simps')
  apply simp
  done

lemmas tcb_ptr_sign_extend_canonical =
      tcb_and_not_mask_canonical[where n=0, simplified mask_def objBits_simps', simplified]

(* FIXME: move up to TypHeap? *)
lemma lift_t_Some_iff:
  "lift_t g hrs p = Some v \<longleftrightarrow> hrs_htd hrs, g \<Turnstile>\<^sub>t p \<and> h_val (hrs_mem hrs) p = v"
  unfolding hrs_htd_def hrs_mem_def by (cases hrs) (auto simp: lift_t_if)

context
  fixes p :: "'a::mem_type ptr"
  fixes q :: "'b::c_type ptr"
  fixes d g\<^sub>p g\<^sub>q
  assumes val_p: "d,g\<^sub>p \<Turnstile>\<^sub>t p"
  assumes val_q: "d,g\<^sub>q \<Turnstile>\<^sub>t q"
  assumes disj: "typ_uinfo_t TYPE('a) \<bottom>\<^sub>t typ_uinfo_t TYPE('b)"
begin

lemma h_val_heap_same_typ_disj:
  "h_val (heap_update p v h) q = h_val h q"
  using disj by (auto intro: h_val_heap_same[OF val_p val_q]
                       simp: tag_disj_def sub_typ_proper_def field_of_t_def typ_tag_lt_def
                             field_of_def typ_tag_le_def)

lemma h_val_heap_same_hrs_mem_update_typ_disj:
  "h_val (hrs_mem (hrs_mem_update (heap_update p v) s)) q = h_val (hrs_mem s) q"
  by (simp add: hrs_mem_update h_val_heap_same_typ_disj)

end

lemmas h_t_valid_nested_fields =
  h_t_valid_field[OF h_t_valid_field[OF h_t_valid_field]]
  h_t_valid_field[OF h_t_valid_field]
  h_t_valid_field

lemmas h_t_valid_fields_clift =
  h_t_valid_nested_fields[OF h_t_valid_clift]
  h_t_valid_clift

lemma numDomains_sge_1_simp:
  "1 <s Kernel_C.numDomains \<longleftrightarrow> Suc 0 < Kernel_Config.numDomains"
  apply (simp add: word_sless_alt sint_numDomains_to_H)
  done

lemma unat_scast_numDomains:
  "unat (SCAST(32 signed \<rightarrow> machine_word_len) Kernel_C.numDomains) = unat Kernel_C.numDomains"
  by (simp add: scast_eq sint_numDomains_to_H unat_numDomains_to_H numDomains_machine_word_safe)

(* link up Kernel_Config loaded from the seL4 build system with physBase in C code *)
lemma physBase_spec:
  "\<forall>s. \<Gamma>\<turnstile> {s} Call physBase_'proc {t. ret__unsigned_long_' t = Kernel_Config.physBase }"
  apply (rule allI, rule conseqPre, vcg)
  apply (simp add: Kernel_Config.physBase_def)
  done

(* Sanity check for hard coded sizeof_sched_context_t *)
lemma sizeof_sched_context_t_eq:
  "sizeof_sched_context_t = size_of TYPE(sched_context_C)"
  by (simp add: sizeof_sched_context_t_def word_size_def)

lemma refill_buffer_relation_pte_update:
  "\<lbrakk>ko_at' (v :: pte) (ptr_val (f x)) \<sigma>; cslift x (f x) = Some y';
    refill_buffer_relation (ksPSpace \<sigma>) (t_hrs_' (globals x)) (ghost'state_' (globals x))\<rbrakk>
   \<Longrightarrow> refill_buffer_relation ((ksPSpace \<sigma>)(ptr_val (f x) \<mapsto> KOArch (KOPTE ko)))
                              (hrs_mem_update (heap_update (f x) (ko' :: pte_C)) (t_hrs_' (globals x)))
                              (ghost'state_' (globals x))"
  by (fastforce simp: typ_heap_simps update_pte_map_tos  refill_buffer_relation_def Let_def)

lemma rf_sr_sc_update_no_refill_buffer_update:
  "\<lbrakk>(s, s') \<in> rf_sr; ko_at' (old_sc :: sched_context) scPtr s;
    t_hrs_' (globals t) = hrs_mem_update (heap_update (PTR(sched_context_C) scPtr) sc')
                                         (t_hrs_' (globals s'));
    csched_context_relation sc sc';
    refill_buffer_relation ((ksPSpace s)(scPtr \<mapsto> KOSchedContext sc))
                           (hrs_mem_update (heap_update (PTR(sched_context_C) scPtr) sc')
                                           (t_hrs_' (globals s')))
                           (ghost'state_' (globals s'))\<rbrakk>
   \<Longrightarrow> (s\<lparr>ksPSpace := (ksPSpace s)(scPtr \<mapsto> KOSchedContext sc)\<rparr>,
        t'\<lparr>globals := globals s'\<lparr>t_hrs_' := t_hrs_' (globals t)\<rparr>\<rparr>) \<in> rf_sr"
  unfolding rf_sr_def state_relation_def cstate_relation_def cpspace_relation_def
  apply (clarsimp simp: Let_def update_scs_map_tos)
  apply (frule_tac ptr=scPtr in cmap_relation_ko_atD[rotated])
  apply fastforce
  apply (erule obj_atE')
  apply clarsimp
  apply (clarsimp simp: map_comp_update projectKO_opt_sc typ_heap_simps')
  apply (intro conjI)
    subgoal by (clarsimp simp: cmap_relation_def split: if_splits)
   subgoal by (clarsimp simp: carch_state_relation_def typ_heap_simps')
  by (simp add: cmachine_state_relation_def)

lemma rf_sr_obj_update_helper:
  "(s, s'\<lparr> globals := globals s' \<lparr> t_hrs_' := t_hrs_' (globals (undefined
              \<lparr> globals := (undefined \<lparr> t_hrs_' := f (globals s') (t_hrs_' (globals s')) \<rparr>)\<rparr>))\<rparr>\<rparr>) \<in> rf_sr
          \<Longrightarrow> (s, globals_update (\<lambda>v. t_hrs_'_update (f v) v) s') \<in> rf_sr"
  by (simp cong: StateSpace.state.fold_congs globals.fold_congs)

lemmas rf_sr_sc_update_no_refill_buffer_update2 =
  rf_sr_obj_update_helper[OF rf_sr_sc_update_no_refill_buffer_update, simplified]

(* FIXME RT: move higher up? *)
lemma cheap_dom_eq:
 "\<exists>old_ko :: 'a :: c_type. cslift s' (Ptr ptr) = Some old_ko
  \<Longrightarrow> dom (lift_t c_guard (hrs_mem_update (heap_update (Ptr ptr) (f (ko :: 'a)))
                          (t_hrs_' (globals s'))))
      = dom (lift_t c_guard (t_hrs_' (globals s')))"
  apply (subst set_eq_subset)
  by (intro conjI; (clarsimp, metis h_t_valid_clift_Some_iff hrs_htd_mem_update))

lemma refill_buffer_relation_sc_no_refills_update:
  "\<lbrakk>refill_buffer_relation (ksPSpace s) (t_hrs_' (globals s')) (ghost'state_' (globals s'));
    ko_at' sc scPtr s; scSize (g sc) = scSize sc; scRefills (g sc) = scRefills sc;
    cslift s' (Ptr scPtr) = Some (old_sc' :: sched_context_C)\<rbrakk>
   \<Longrightarrow> refill_buffer_relation
         ((ksPSpace s)(scPtr \<mapsto> KOSchedContext (g sc)))
         (hrs_mem_update (heap_update (PTR(sched_context_C) scPtr) (f sc')) (t_hrs_' (globals s')))
         (ghost'state_' (globals s'))"
  apply (simp (no_asm_simp) only: refill_buffer_relation_def Let_def)
  apply (intro context_conjI)
      apply (drule refill_buffer_relation_cvariable_array_map_relation)
      apply (clarsimp simp: cvariable_array_map_relation_def)
      apply (case_tac "p \<noteq> scPtr")
       apply (clarsimp simp: map_comp_def)
      apply (drule_tac x=scPtr in spec)
      apply (clarsimp simp: map_comp_def split: option.splits)
       apply (clarsimp simp: obj_at_simps)
      apply (fastforce simp: obj_at_simps)
     apply (drule refill_buffer_relation_refill_to_sc)
     apply (subst cheap_dom_eq)
      apply fastforce
     apply (subst dom_eq)
      apply (clarsimp simp: obj_at_simps)
     apply (fastforce simp: obj_at'_def map_comp_def split: if_splits)
    apply (drule refill_buffer_relation_crefill_relation)
    apply (clarsimp simp: Let_def)
    apply (case_tac "p \<noteq> scPtr")
     apply (clarsimp simp: map_comp_def typ_heap_simps)
    apply (clarsimp simp: obj_at'_def dyn_array_list_rel_pointwise typ_heap_simps)
   apply (drule refill_buffer_relation_gs_dom)
   apply (subst dom_eq; force)
  apply (frule refill_buffer_relation_size_eq)
  apply (clarsimp simp: obj_at'_def map_comp_def split: option.splits if_splits)
  done

lemma refillSizeBytes_sizeof:
  "refillSizeBytes = size_of TYPE(refill_C)"
  by (simp add: refillSizeBytes_def)

(* FIXME RT: move to Refine *)
lemma ko_at_is_aligned'[intro?]:
  "ko_at' ko p s \<Longrightarrow> is_aligned p (objBits ko)"
  apply (erule obj_atE')
  apply (simp add: objBits_def project_inject)
  done

(* FIXME RT: move to StateRelation.thy in Refine *)
lemma scRefills_sc_size_rel:
  "valid_sched_context' sc s \<Longrightarrow>
   schedContextStructSize + length (scRefills sc) * refillSizeBytes
   \<le> 2 ^ (objBits sc)"
  supply refill_C_size[simp del] sched_context_C_size[simp del]
  apply (clarsimp simp: objBits_simps valid_sched_context'_def add_ac)
  apply (rule refillAbsoluteMax'_leq)
  apply (rule_tac y="2 ^ minSchedContextBits" in order_trans)
   apply (rule schedContextStructSize_minSchedContextBits)
  apply fastforce
  done

lemma c_guard_refill:
  "\<lbrakk>is_aligned scPtr sz; sz < word_bits;
    schedContextStructSize + len * refillSizeBytes \<le> 2 ^ sz;
    minSchedContextBits \<le> sz; n < len; scPtr \<noteq> 0\<rbrakk>
   \<Longrightarrow> c_guard (sc_ptr_to_crefill_ptr scPtr +\<^sub>p int n)"
  supply refill_C_size[simp del] refillSizeBytes_sizeof[symmetric, simp add]
  apply (clarsimp simp: sc_ptr_to_crefill_ptr_def2)
  apply (rule_tac n="4" and m="3" in is_aligned_c_guard)
      apply clarsimp
      apply (rule is_aligned_add)
       apply (rule is_aligned_add)
        apply (rule_tac x=sz in is_aligned_weaken)
         apply simp
        apply (clarsimp simp: objBits_simps minSchedContextBits_def sc_size_bounds_def)
       apply (clarsimp simp: is_aligned_def schedContextStructSize_sizeof)
      apply (rule_tac k="word_of_nat n" in is_alignedI)
      apply (simp add: refillSizeBytes_def refill_C_size)
     apply (simp add: add_ac)
     apply (rule_tac n=sz in aligned_offset_non_zero)
       apply (clarsimp simp: obj_at_simps)
      apply (subst Abs_fnat_hom_mult)
      apply (subst word_of_nat_plus[symmetric])
      apply (rule word_of_nat_less)
      apply (subst unat_power_lower64')
       apply (clarsimp simp: obj_at'_def objBits_simps word_bits_def)
      apply (clarsimp simp: objBits_simps word_bits_def refillSizeBytes_def)
     apply fastforce
    apply (simp add: add.assoc)
    apply (clarsimp simp: align_of_def)
   apply (insert refill_C_size)
   apply force
  apply linarith
  done

lemma h_t_valid_refill:
  "\<lbrakk>refill_buffer_relation (ksPSpace s) (t_hrs_' (globals s')) gs;
    ko_at' sc scPtr s; valid_sched_context' sc s; valid_sched_context_size' sc;
    n < length (scRefills sc); scPtr \<noteq> 0\<rbrakk>
   \<Longrightarrow> s' \<Turnstile>\<^sub>c (sc_ptr_to_crefill_ptr scPtr +\<^sub>p int n)"
  supply refill_C_size[simp del] refillSizeBytes_sizeof[symmetric, simp add]
  apply (rule h_t_array_valid_field)
    apply (frule refill_buffer_relation_cvariable_array_map_relation)
    apply (clarsimp simp: Let_def cvariable_array_map_relation_def)
    apply (fastforce intro: ko_at_projectKO_opt)
   apply simp
  apply (rule c_guard_refill[where len="length (scRefills sc)"])
       apply (fastforce simp: obj_at'_def)
      apply (fastforce simp: obj_at'_def)
     apply (frule scRefills_sc_size_rel)
     apply (clarsimp simp: objBits_simps word_bits_def refillSizeBytes_def)
    apply (clarsimp simp: valid_sched_context_size'_def sc_size_bounds_def objBits_simps)
   by assumption

lemma refill_buffer_within_sc_size:
  "\<lbrakk>ksPSpace s p = Some (KOSchedContext sc); valid_sched_context' sc s; pspace_bounded' s\<rbrakk>
   \<Longrightarrow> {ptr_val (sc_ptr_to_crefill_ptr p)..+length (scRefills sc) * size_of TYPE(refill_C)}
       \<subseteq> {p..+2 ^ objBits sc}"
  supply refill_C_size[simp del]
  apply (insert scRefills_sc_size_rel[where sc=sc and s=s])
  apply (simp add: sc_ptr_to_crefill_ptr_def2)
  apply (rule intvl_sub_offset)
  apply (subst unat_of_nat_eq)
   apply (rule_tac y="2 ^ objBitsKO (KOSchedContext sc)" in le_less_trans)
    apply (simp flip: refillSizeBytes_sizeof
                 add: refillSizeBytes_def)
    apply (fastforce simp: objBits_simps)
   apply (drule pspace_boundedD'[rotated])
    apply fastforce
   apply (fastforce simp: word_bits_def
                   intro: power_strict_increasing_iff[THEN iffD2])
  apply (simp flip: refillSizeBytes_sizeof)
  done

lemma refill_within_sc_size:
  "\<lbrakk>ksPSpace s p = Some (KOSchedContext sc); valid_sched_context' sc s; pspace_bounded' s;
    n < length (scRefills sc)\<rbrakk>
   \<Longrightarrow> {(ptr_val (sc_ptr_to_crefill_ptr p +\<^sub>p int n))..+size_of TYPE(refill_C)}
       \<subseteq> {p..+2 ^ objBits sc}"
  supply refill_C_size[simp del]
  apply (drule pspace_boundedD'[rotated])
    apply fastforce
  apply (insert scRefills_sc_size_rel[where sc=sc and s=s])
  apply (simp add: sc_ptr_to_crefill_ptr_def2)
  apply (simp only: Abs_fnat_hom_mult add.assoc
              flip: word_of_nat_plus)
  apply (drule sym)
  apply (erule subst)
  apply (rule intvl_sub_offset)
  apply (subst unat_of_nat_eq)
   apply (rule_tac y="2 ^ objBitsKO (KOSchedContext sc)" in le_less_trans)
    apply (simp flip: refillSizeBytes_sizeof
                 add: refillSizeBytes_def)
    apply (fastforce simp: objBits_simps)
   apply (fastforce simp: word_bits_def
                   intro: power_strict_increasing_iff[THEN iffD2])
  apply (simp flip: refillSizeBytes_sizeof
               add: objBits_simps refillSizeBytes_def)
  done

lemma sc_from_refill:
  "\<lbrakk>clift hp (x :: refill_C ptr) = Some refill; refill_buffer_relation (ksPSpace s) hp gs;
    pspace_aligned' s; pspace_distinct' s; pspace_bounded' s; valid_objs' s\<rbrakk>
   \<Longrightarrow> \<exists>p sc n. ko_at' sc p s
                \<and> {ptr_val x..+size_of TYPE(refill_C)} \<subseteq> {p..+2 ^ objBits sc}
                \<and> ptr_val x \<in> {p..+2 ^ objBits sc}
                \<and> n < length (scRefills sc)
                \<and> x = sc_ptr_to_crefill_ptr p +\<^sub>p int n"
  supply refill_C_size[simp del]
  apply (frule refill_buffer_relation_refill_to_sc)
  apply (clarsimp simp: Let_def)
  apply (prop_tac "x \<in> dom (clift hp)")
   apply fastforce
  apply (drule (1) set_rev_mp)
  apply clarsimp
  apply (rename_tac p n sc)
  apply (rule_tac x=p in exI)
  apply (rule_tac x=sc in exI)
  apply (intro context_conjI; fastforce?)
   apply (fastforce intro: map_to_ko_atI)
  apply (clarsimp simp: map_comp_def split: option.splits)
  apply (frule (1) sc_ko_at_valid_objs_valid_sc')
  apply (frule refill_within_sc_size, fastforce+)
  done

lemma sc_at_array_assertion':
  "\<lbrakk>refill_buffer_relation (ksPSpace s) (t_hrs_' (globals s')) (ghost'state_' (globals s'));
    ko_at' sc scPtr s; 0 < length (scRefills sc)\<rbrakk>
   \<Longrightarrow> array_assertion
        (PTR(refill_C)
          (scPtr +
           UCAST(32 \<rightarrow> 64) (word_of_nat (size_of TYPE(sched_context_C)))))
        (length (scRefills sc)) (hrs_htd (t_hrs_' (globals s')))"
  supply sched_context_C_size[simp del]
  apply (drule refill_buffer_relation_cvariable_array_map_relation)
  apply (rule h_t_array_valid_array_assertion)
   apply (clarsimp simp: cvariable_array_map_relation_def)
   apply (drule obj_at_ko_at', clarsimp)
   apply (drule_tac x=scPtr in spec)
   apply (drule_tac x=sc in spec)
   apply (elim impE)
    apply (erule ko_at_projectKO_opt)
   apply (clarsimp simp: sc_ptr_to_crefill_ptr_def)
  apply assumption
  done

lemma obj_range'_intvl:
  "is_aligned ptr (objBitsKO obj) \<Longrightarrow> obj_range' ptr obj = {ptr..+2 ^ objBitsKO obj}"
  apply (clarsimp simp: obj_range'_def)
  apply (frule upto_intvl_eq[symmetric])
  apply (clarsimp simp: mask_def p_assoc_help)
  done

lemma sc_ptr_to_crefill_ptr_inj:
  "\<lbrakk>ksPSpace s scPtr = Some (KOSchedContext sc); valid_sched_context' sc s;
    valid_sched_context_size' sc; n < length (scRefills sc); m < length (scRefills sc)\<rbrakk>
   \<Longrightarrow> (sc_ptr_to_crefill_ptr scPtr +\<^sub>p int n = sc_ptr_to_crefill_ptr scPtr +\<^sub>p int m)
       = (n = m)"
  supply len_bit0[simp del] refill_C_size[simp del]
         word_bits_len_of[simp add]
  apply (intro iffI; simp?)
  apply (frule (1) length_scRefills_bounded)
  apply (clarsimp simp: sc_ptr_to_crefill_ptr_def)
  apply (drule word_unat_eq_iff[THEN iffD1])
  apply (subst (asm) unat_mult_lem[THEN iffD1])
   apply (subst unat_of_nat_eq)
    apply (simp add: refillSizeBytes_def)
   apply (subst unat_of_nat_eq)
    apply (clarsimp simp: refill_C_size refillSizeBytes_def)
   apply (simp add: refillSizeBytes_sizeof)
   apply (rule_tac y="size_of TYPE(refill_C) * length (scRefills sc)" in le_less_trans)
    apply fastforce
   apply fastforce
  apply (subst (asm) unat_mult_lem[THEN iffD1])
   apply (subst (asm) unat_of_nat_eq
          | subst unat_of_nat_eq
          | clarsimp simp: refill_C_size refillSizeBytes_def)+
  done

lemma rf_sr_refill_update:
  "\<lbrakk>(s, s') \<in> rf_sr; ko_at' (old_sc :: sched_context) scPtr s;
    valid_objs' s; no_0_obj' s; pspace_aligned' s; pspace_distinct' s; pspace_bounded' s;
    n < length (scRefills old_sc);
    sc = scRefills_update (\<lambda>ls. updateAt n ls f) old_sc;
    cslift s' (sched_context_Ptr scPtr) = Some sc';
    t_hrs_' (globals t) =
    hrs_mem_update (heap_update (sc_ptr_to_crefill_ptr scPtr +\<^sub>p int n) refill')
                   (t_hrs_' (globals s'));
    csched_context_relation sc sc';
    refill = f (scRefills old_sc ! n); crefill_relation refill refill'\<rbrakk>
   \<Longrightarrow> (s\<lparr>ksPSpace := (ksPSpace s)(scPtr \<mapsto> KOSchedContext sc)\<rparr>,
        t'\<lparr>globals := globals s'\<lparr>t_hrs_' := t_hrs_' (globals t)\<rparr>\<rparr>) \<in> rf_sr"
  supply sched_context_C_size[simp del] refill_C_size[simp del]

  apply (frule_tac k=old_sc in sc_ko_at_valid_objs_valid_sc', assumption)
  apply (frule rf_sr_refill_buffer_relation)
  apply (frule_tac sc=old_sc and scPtr=scPtr and n=n in h_t_valid_refill; fastforce?)

  unfolding rf_sr_def state_relation_def cstate_relation_def cpspace_relation_def
  apply (clarsimp simp: Let_def update_scs_map_tos)
  apply (frule_tac ptr=scPtr in cmap_relation_ko_atD[rotated])
   apply fastforce
  apply (erule obj_atE')
  apply clarsimp
  apply (clarsimp simp: map_comp_update projectKO_opt_sc typ_heap_simps')
  apply (intro conjI)
     subgoal by (clarsimp simp: cmap_relation_def split: if_splits)

    subgoal \<comment> \<open>refill_buffer_relation\<close>
      apply (prop_tac "length (scRefills sc) = length (scRefills old_sc)", simp)
      apply (prop_tac "scRefills old_sc \<noteq> []")
       apply (clarsimp simp: valid_sched_context'_def)

      apply (simp (no_asm) add: refill_buffer_relation_def Let_def)

      apply (rule conjI)
       apply (drule refill_buffer_relation_cvariable_array_map_relation)
       apply (clarsimp simp: cvariable_array_map_relation_def map_comp_def
                      split: if_splits)

      apply (rule conjI)
       apply (drule refill_buffer_relation_refill_to_sc)
       apply (subst dom_lift_t_heap_update)
       apply (subst dom_eq)
        subgoal by (fastforce simp: obj_at'_def)
       apply (clarsimp simp only: Let_def subset_eq)
       apply (rename_tac refillPtr refill'')
       apply (drule_tac x=refillPtr in bspec, blast)
       apply clarsimp
       apply (rename_tac scPtr' n' sc'')
       apply (rule_tac x=scPtr' in bexI)
        subgoal by (clarsimp simp: map_comp_def split: option.splits if_splits)
       apply blast

      apply (rule conjI)
       apply (drule refill_buffer_relation_crefill_relation)
       apply (clarsimp simp: Let_def)
       apply (rename_tac p sc'')
       apply (case_tac "p \<noteq> scPtr")
        apply (clarsimp simp: map_comp_def split: option.splits if_splits)
        apply (drule_tac x=p in spec)
        apply (drule_tac x="KOSchedContext sc''" in spec)
        apply (clarsimp simp: Let_def dyn_array_list_rel_pointwise typ_heap_simps split: if_splits)
        apply (rename_tac n')
        apply (drule_tac x=n' in spec)
        apply (elim impE)
         apply assumption
        apply (elim exE)
        apply (frule_tac scPtr=p in ksPSpace_valid_sched_context')
         apply fastforce
        apply (elim conjE)
        apply (frule_tac p=p and  n=n' and sc=sc'' in refill_within_sc_size; assumption?)
        apply (frule_tac p=scPtr and n=n and sc=old_sc in refill_within_sc_size; assumption?)
        apply (frule_tac a=scPtr and b=p in obj_range'_disjoint; assumption?)
         apply fastforce
        apply (rule FalseE)
        apply (rule_tac A="obj_range' scPtr (KOSchedContext old_sc)"
                    and B="obj_range' p (KOSchedContext sc'')"
                    and x="ptr_val (sc_ptr_to_crefill_ptr scPtr +\<^sub>p int n)"
                     in in_empty_interE)
          apply (simp only: obj_range'_def)
         apply (frule_tac x=scPtr in pspace_alignedD', fastforce)
         apply (frule obj_range'_intvl)
         subgoal by (fastforce simp: objBits_simps)
        apply (frule_tac x=p in pspace_alignedD', fastforce)
        apply (frule_tac ptr=p in obj_range'_intvl)
        subgoal by (fastforce simp: objBits_simps)
       apply (drule_tac x=scPtr in spec)
       apply (clarsimp simp: dyn_array_list_rel_pointwise)
       apply (rename_tac n')
       apply (frule_tac i=n' and j=n and f=f and xs="scRefills old_sc" in updateAt_index;
              assumption?)
       apply (case_tac "n=n'")
        apply (clarsimp simp: typ_heap_simps')
       apply (drule_tac x=n' in spec)
       apply (clarsimp simp: typ_heap_simps' split: if_splits)
       apply (intro conjI impI)
        apply (frule_tac scPtr=scPtr and n=n and m=n' in sc_ptr_to_crefill_ptr_inj;
               assumption?)
        apply fastforce
       apply (subst updateAt_index; assumption?)
       apply (clarsimp split: if_splits)

      apply (rule conjI)
       apply (drule refill_buffer_relation_gs_dom)
       apply (subst dom_eq)
        subgoal by (fastforce simp: obj_at'_def)
       apply (clarsimp simp: Let_def)

      apply (drule refill_buffer_relation_size_eq)
      by (clarsimp simp: map_comp_def split: if_splits)

   subgoal by (clarsimp simp: carch_state_relation_def typ_heap_simps')
  by (simp add: cmachine_state_relation_def)

lemmas rf_sr_refill_update2 =
  rf_sr_obj_update_helper[OF rf_sr_refill_update, simplified]

lemma ret__ptr_to_struct_refill_C_'_update_rf_sr_helper:
  "((s, globals_update f (ret__ptr_to_struct_refill_C_'_update g s')) \<in> rf_sr) =
   ((s, globals_update f s') \<in> rf_sr)"
  by (clarsimp simp: rf_sr_def)

lemma crefill_relationD:
  "\<lbrakk>refill_buffer_relation (ksPSpace s) (t_hrs_' (globals s')) gs; ko_at' sc scPtr s; valid_objs' s;
    n < length (scRefills sc)\<rbrakk>
   \<Longrightarrow> crefill_relation
        (scRefills sc ! n)
        (h_val (hrs_mem (t_hrs_' (globals s'))) (sc_ptr_to_crefill_ptr scPtr +\<^sub>p int n))"
  apply (frule refill_buffer_relation_crefill_relation)
  apply (clarsimp simp: Let_def)
  apply (drule_tac x=scPtr in spec)
  apply (drule_tac x=sc in spec)
  apply (elim impE)
   apply (frule (1) ko_at_projectKO_opt)
  apply (frule (1) sc_ko_at_valid_objs_valid_sc')
  apply (clarsimp simp: dyn_array_list_rel_pointwise)
  apply (fastforce simp: typ_heap_simps)
  done

end
end
