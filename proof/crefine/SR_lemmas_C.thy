(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory SR_lemmas_C
imports
  StateRelation_C
  "../refine/Invariants_H"
begin

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
  \<Longrightarrow> option_map cte_to_H (cte_lift (cte_C.cap_C_update (\<lambda>_. cap') cte')) =
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
  "pageSize cap \<equiv> case cap of ArchObjectCap (PageCap _ _ sz _) \<Rightarrow> sz"

definition
  "isArchCap_tag (n :: 32 word) \<equiv> n mod 2 = 1"

lemma isArchCap_tag_def2:
  "isArchCap_tag n \<equiv> n && 1 = 1"
  by (simp add: isArchCap_tag_def word_mod_2p_is_mask[where n=1, simplified] mask_def)

lemma framesize_to_H_not_Small [simp]:
  "framesize_to_H w \<noteq> ARMSmallPage"
  by (simp add: framesize_to_H_def)

lemma cap_get_tag_isCap0:
  assumes cr: "ccap_relation cap cap'"
  shows "(cap_get_tag cap' = scast cap_thread_cap) = isThreadCap cap
  \<and> (cap_get_tag cap' = scast cap_null_cap) = (cap = NullCap)
  \<and> (cap_get_tag cap' = scast cap_async_endpoint_cap) = isAsyncEndpointCap cap
  \<and> (cap_get_tag cap' = scast cap_endpoint_cap) = isEndpointCap cap
  \<and> (cap_get_tag cap' = scast cap_irq_handler_cap) = isIRQHandlerCap cap
  \<and> (cap_get_tag cap' = scast cap_irq_control_cap) = isIRQControlCap cap
  \<and> (cap_get_tag cap' = scast cap_zombie_cap) = isZombie cap
  \<and> (cap_get_tag cap' = scast cap_reply_cap) = isReplyCap cap
  \<and> (cap_get_tag cap' = scast cap_untyped_cap) = isUntypedCap cap
  \<and> (cap_get_tag cap' = scast cap_cnode_cap) = isCNodeCap cap
  \<and> isArchCap_tag (cap_get_tag cap') = isArchCap \<top> cap
  \<and> (cap_get_tag cap' = scast cap_small_frame_cap) = (isArchPageCap cap \<and> pageSize cap = ARMSmallPage)
  \<and> (cap_get_tag cap' = scast cap_frame_cap) = (isArchPageCap cap \<and> pageSize cap \<noteq> ARMSmallPage)
  \<and> (cap_get_tag cap' = scast cap_domain_cap) = isDomainCap cap"
  using cr
  apply -
  apply (erule ccap_relationE)
  apply (simp add: cap_to_H_def cap_lift_def Let_def isArchCap_tag_def2 isArchCap_def)
  apply (clarsimp simp: isCap_simps cap_tag_defs word_le_nat_alt pageSize_def Let_def
                 split: split_if_asm) -- "takes a while"
  done


lemma cap_get_tag_isCap:
  assumes cr: "ccap_relation cap cap'"
  shows "(cap_get_tag cap' = scast cap_thread_cap) = (isThreadCap cap)"
  and "(cap_get_tag cap' = scast cap_null_cap) = (cap = NullCap)"
  and "(cap_get_tag cap' = scast cap_async_endpoint_cap) = (isAsyncEndpointCap cap)"
  and "(cap_get_tag cap' = scast cap_endpoint_cap) = (isEndpointCap cap)"
  and "(cap_get_tag cap' = scast cap_irq_handler_cap) = (isIRQHandlerCap cap)"
  and "(cap_get_tag cap' = scast cap_irq_control_cap) = (isIRQControlCap cap)"
  and "(cap_get_tag cap' = scast cap_zombie_cap) = (isZombie cap)"
  and "(cap_get_tag cap' = scast cap_reply_cap) = isReplyCap cap"
  and "(cap_get_tag cap' = scast cap_untyped_cap) = (isUntypedCap cap)"
  and "(cap_get_tag cap' = scast cap_cnode_cap) = (isCNodeCap cap)"  
  and "isArchCap_tag (cap_get_tag cap') = isArchCap \<top> cap"
  and "(cap_get_tag cap' = scast cap_small_frame_cap) = (isArchPageCap cap \<and> pageSize cap = ARMSmallPage)"
  and "(cap_get_tag cap' = scast cap_frame_cap) = (isArchPageCap cap \<and> pageSize cap \<noteq> ARMSmallPage)"
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

lemma cap_get_tag_AsyncEndpointCap:
  assumes cr: "ccap_relation cap cap'"
  shows "(cap_get_tag cap' = scast cap_async_endpoint_cap) = 
  (cap = AsyncEndpointCap
         (capAEPPtr_CL (cap_async_endpoint_cap_lift cap'))
         (capAEPBadge_CL (cap_async_endpoint_cap_lift cap'))
         (to_bool (capAEPCanSend_CL (cap_async_endpoint_cap_lift cap')))
         (to_bool (capAEPCanReceive_CL (cap_async_endpoint_cap_lift cap'))))"
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
        (to_bool (capCanGrant_CL (cap_endpoint_cap_lift cap'))))"
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
            split: split_if_asm)
  done



lemma cap_get_tag_ReplyCap:
  assumes cr: "ccap_relation cap cap'"
  shows "(cap_get_tag cap' = scast cap_reply_cap) = 
  (cap = 
      ReplyCap (ctcb_ptr_to_tcb_ptr (Ptr (cap_reply_cap_CL.capTCBPtr_CL (cap_reply_cap_lift cap'))))
               (to_bool (capReplyMaster_CL (cap_reply_cap_lift cap'))))"
  using cr
  apply -
  apply (rule iffI)   
   apply (erule ccap_relationE)
   apply (clarsimp simp add: cap_lifts cap_to_H_def)
  apply (simp add: cap_get_tag_isCap isCap_simps)
  done

lemma cap_get_tag_UntypedCap:
  assumes cr: "ccap_relation cap cap'"
  shows "(cap_get_tag cap' = scast cap_untyped_cap) = 
  (cap = UntypedCap (capPtr_CL (cap_untyped_cap_lift cap'))
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
     cap_get_tag_AsyncEndpointCap
     cap_get_tag_EndpointCap
     cap_get_tag_CNodeCap
     cap_get_tag_IRQHandlerCap
     cap_get_tag_IRQControlCap
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

(* MOVE --- here down doesn't really belong here, maybe in a haskell specific file?*)
lemma tcb_cte_cases_in_range1:
  assumes tc:"tcb_cte_cases (y - x) = Some v"
  and     al: "is_aligned x 9"
  shows   "x \<le> y"
proof -
  from tc obtain q where yq: "y = x + q" and qv: "q < 2 ^ 9"
    unfolding tcb_cte_cases_def
    by (simp add: diff_eq_eq split: split_if_asm)
   
  have "x \<le> x + 2 ^ 9 - 1" using al
    by (rule is_aligned_no_overflow)
    
  hence "x \<le> x + q" using qv
    apply simp
    apply unat_arith
    apply simp
    done
    
  thus ?thesis using yq by simp
qed

lemma tcb_cte_cases_in_range2:
  assumes tc: "tcb_cte_cases (y - x) = Some v"
  and     al: "is_aligned x 9"
  shows   "y \<le> x + 2 ^ 9 - 1"
proof -
  from tc obtain q where yq: "y = x + q" and qv: "q \<le> 2 ^ 9 - 1"
    unfolding tcb_cte_cases_def
    by (simp add: diff_eq_eq split: split_if_asm)
   
  have "x + q \<le> x + (2 ^ 9 - 1)" using qv
    apply (rule word_plus_mono_right)
    apply (rule is_aligned_no_overflow' [OF al])
    done

  thus ?thesis using yq by (simp add: field_simps)
qed
  
lemmas tcbSlots = 
  tcbCTableSlot_def tcbVTableSlot_def
  tcbReplySlot_def tcbCallerSlot_def tcbIPCBufferSlot_def

lemma updateObject_cte_tcb:
  assumes tc: "tcb_cte_cases (ptr - ptr') = Some (accF, updF)"
  shows   "updateObject ctea (KOTCB tcb) ptr ptr' next =
   (do alignCheck ptr' (objBits tcb);
        magnitudeCheck ptr' next (objBits tcb);
        return (KOTCB (updF (\<lambda>_. ctea) tcb))
    od)"
  using tc unfolding tcb_cte_cases_def
  apply -
  apply (clarsimp simp add: updateObject_cte Let_def 
    tcb_cte_cases_def objBits_simps tcbSlots shiftl_t2n
    split: split_if_asm cong: if_cong)
  done

definition
  tcb_no_ctes_proj :: "tcb \<Rightarrow> Structures_H.thread_state \<times> word32 \<times> word32 \<times> (ARMMachineTypes.register \<Rightarrow> word32) \<times> bool \<times> word8 \<times> word8 \<times> nat \<times> fault option"
  where
  "tcb_no_ctes_proj t \<equiv> (tcbState t, tcbFaultHandler t, tcbIPCBuffer t, tcbContext t, tcbQueued t,
                            tcbPriority t, tcbDomain t, tcbTimeSlice t, tcbFault t)"

lemma tcb_cte_cases_proj_eq [simp]:
  "tcb_cte_cases p = Some (getF, setF) \<Longrightarrow> 
  tcb_no_ctes_proj tcb = tcb_no_ctes_proj (setF f tcb)"
  unfolding tcb_no_ctes_proj_def tcb_cte_cases_def
  by (auto split: split_if_asm)

lemma map_to_ctes_upd_cte':
  "\<lbrakk> ksPSpace s p = Some (KOCTE cte'); is_aligned p 4; ps_clear p 4 s \<rbrakk>
  \<Longrightarrow> map_to_ctes (ksPSpace s(p |-> KOCTE cte)) = (map_to_ctes (ksPSpace s))(p |-> cte)"
  apply (erule (1) map_to_ctes_upd_cte)
  apply (simp add: field_simps ps_clear_def3)
  done

lemma map_to_ctes_upd_tcb':  
  "[| ksPSpace s p = Some (KOTCB tcb'); is_aligned p 9;
   ps_clear p 9 s |]
==> map_to_ctes (ksPSpace s(p |-> KOTCB tcb)) =
    (%x. if EX getF setF.
               tcb_cte_cases (x - p) = Some (getF, setF) &
               getF tcb ~= getF tcb'
         then case tcb_cte_cases (x - p) of
              Some (getF, setF) => Some (getF tcb)
         else ctes_of s x)"
  apply (erule (1) map_to_ctes_upd_tcb)
  apply (simp add: field_simps ps_clear_def3)
  done


lemma tcb_cte_cases_inv [simp]:
  "tcb_cte_cases p = Some (getF, setF) \<Longrightarrow> getF (setF (\<lambda>_. v) tcb) = v"
  unfolding tcb_cte_cases_def
  by (simp split: split_if_asm)
  
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
     cte_level_bits_def objBits_simps
     cong: bex_cong)
   apply (rule bexI [where x = "((), s)"])
    apply (frule_tac s' = s in in_magnitude_check [where v = "()"])
      apply simp
     apply assumption
    apply simp
    apply (erule bexI [rotated])
    apply (simp  cong: if_cong)
    apply rule
    apply (simp split: kernel_object.splits)
    apply (fastforce simp: tcb_no_ctes_proj_def)
   apply (simp add: in_alignCheck)
  (* clag *)
  apply (rule ps_clear_lookupAround2, assumption+)
    apply (erule (1) tcb_cte_cases_in_range1)
   apply (erule (1) tcb_cte_cases_in_range2)
  apply (simp add: return_def del: fun_upd_apply cong: bex_cong option.case_cong)
  apply (subst updateObject_cte_tcb)
   apply assumption
  apply (simp add: bind_def return_def assert_opt_def gets_def split_beta get_def when_def
    modify_def put_def unless_def when_def in_alignCheck')
  apply (simp add: objBits_simps)
  apply (simp add: magnitudeCheck_def return_def split: option.splits
    cong: bex_cong if_cong)
   apply (simp split: kernel_object.splits)
   apply (fastforce simp: tcb_no_ctes_proj_def)
  apply (simp add: magnitudeCheck_def when_def return_def fail_def 
    linorder_not_less
    split: option.splits
    cong: bex_cong if_cong)
  apply rule
  apply (simp split: kernel_object.splits)
  apply (fastforce simp: tcb_no_ctes_proj_def)
  done


(* duplicates *)
lemma pspace_alignedD' [intro?]:
  assumes  lu: "ksPSpace s x = Some v"
  and      al: "pspace_aligned' s"
  shows   "is_aligned x (objBitsKO v)"
  using al lu unfolding pspace_aligned'_def
  apply -
  apply (drule (1) bspec [OF _ domI])
  apply simp
  done

declare pspace_distinctD' [intro?]

lemma ctes_of_ksI [intro?]:
  fixes s :: "kernel_state"
  assumes ks: "ksPSpace s x = Some (KOCTE cte)"
  and     pa: "pspace_aligned' s"  (* yuck *)
  and     pd: "pspace_distinct' s"
  shows   "ctes_of s x = Some cte"
proof (rule ctes_of_eq_cte_wp_at')
  from ks show "cte_wp_at' (op = cte) x s"
  proof (rule cte_wp_at_cteI' [OF _ _ _ refl])
    from ks pa have "is_aligned x (objBitsKO (KOCTE cte))" ..
    thus "is_aligned x cte_level_bits" 
      unfolding cte_level_bits_def by (simp add: objBits_simps)
    
    from ks pd have "ps_clear x (objBitsKO (KOCTE cte)) s" ..
    thus "ps_clear x cte_level_bits s"  
      unfolding cte_level_bits_def by (simp add: objBits_simps)
  qed
qed


lemma fst_setCTE:
  assumes ct: "cte_at' dest s"
  and     rl: "\<And>s'. \<lbrakk> ((), s') \<in> fst (setCTE dest cte s);
           (s' = s \<lparr> ksPSpace := ksPSpace s' \<rparr>);
           (ctes_of s' = ctes_of s(dest \<mapsto> cte));
           (map_to_eps (ksPSpace s) = map_to_eps (ksPSpace s'));
           (map_to_aeps (ksPSpace s) = map_to_aeps (ksPSpace s'));
           (map_to_pdes (ksPSpace s) = map_to_pdes (ksPSpace s'));
           (map_to_ptes (ksPSpace s) = map_to_ptes (ksPSpace s'));
           (map_to_asidpools (ksPSpace s) = map_to_asidpools (ksPSpace s'));
           (map_to_user_data (ksPSpace s) = map_to_user_data (ksPSpace s'));
           (option_map tcb_no_ctes_proj \<circ> map_to_tcbs (ksPSpace s) 
              = option_map tcb_no_ctes_proj \<circ> map_to_tcbs (ksPSpace s')) \<rbrakk> \<Longrightarrow> P"
  shows   "P"
proof -
  (* Unpack the existential and bind x, theorems in this.  Yuck *)
  from fst_setCTE0 [where cte = cte, OF ct] guess s' by clarsimp
  note thms = this
  
  from thms have ceq: "ctes_of s' = ctes_of s(dest \<mapsto> cte)"
    apply -    
    apply (erule use_valid [OF _ setCTE_ctes_of_wp])
    apply simp
    done
  
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
    show "map_to_aeps (ksPSpace s) = map_to_aeps (ksPSpace s')"
    proof (rule map_comp_eqI)
      fix x
      assume xin: "x \<in> dom (ksPSpace s')"
      then obtain ko where ko: "ksPSpace s x = Some ko" by (clarsimp simp: thms(3)[symmetric])
      moreover from xin obtain ko' where ko': "ksPSpace s' x = Some ko'" by clarsimp
      ultimately have "(projectKO_opt ko' :: async_endpoint option) = projectKO_opt ko" using xin thms(4) ceq
	      by - (drule (1) bspec, cases ko, auto simp: projectKO_opt_aep)
      thus "(projectKO_opt (the (ksPSpace s' x)) :: async_endpoint option) = projectKO_opt (the (ksPSpace s x))" using ko ko' 
	      by simp
    qed fact

    show "map_to_pdes (ksPSpace s) = map_to_pdes (ksPSpace s')"
    proof (rule map_comp_eqI)
      fix x
      assume xin: "x \<in> dom (ksPSpace s')"
      then obtain ko where ko: "ksPSpace s x = Some ko" by (clarsimp simp: thms(3)[symmetric])
      moreover from xin obtain ko' where ko': "ksPSpace s' x = Some ko'" by clarsimp
      ultimately have "(projectKO_opt ko' :: pde option) = projectKO_opt ko" using xin thms(4) ceq
	      by - (drule (1) bspec, cases ko, auto simp: projectKO_opt_pde)
      thus "(projectKO_opt (the (ksPSpace s' x)) :: pde option) = projectKO_opt (the (ksPSpace s x))" using ko ko' 
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
        
    show "option_map tcb_no_ctes_proj \<circ> map_to_tcbs (ksPSpace s) =
      option_map tcb_no_ctes_proj \<circ> map_to_tcbs (ksPSpace s')"
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
	hence "option_map tcb_no_ctes_proj (map_to_tcbs (ksPSpace s) x)
	  = option_map tcb_no_ctes_proj (map_to_tcbs (ksPSpace s') x)"
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
	hence "option_map tcb_no_ctes_proj (map_to_tcbs (ksPSpace s) x)
	  = option_map tcb_no_ctes_proj (map_to_tcbs (ksPSpace s') x)"
	  apply -
	  apply (frule subst [OF dm])
	  apply (simp add: dom_def)
	  done
      } ultimately show "(option_map tcb_no_ctes_proj \<circ> (map_to_tcbs (ksPSpace s))) x
	  = (option_map tcb_no_ctes_proj \<circ> (map_to_tcbs (ksPSpace s'))) x"
	by auto
    qed
  qed fact+
qed

lemma ctes_of_cte_at:
  "ctes_of s p = Some x \<Longrightarrow> cte_at' p s"
  by (simp add: cte_wp_at_ctes_of)

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
  assumes om: "option_map tcb_no_ctes_proj \<circ> map_to_tcbs (ksPSpace s) =
  option_map tcb_no_ctes_proj \<circ> map_to_tcbs (ksPSpace s')"
  and    rel: "cmap_relation (map_to_tcbs (ksPSpace s)) (clift (t_hrs_' (globals x))) tcb_ptr_to_ctcb_ptr ctcb_relation"
  shows "cmap_relation (map_to_tcbs (ksPSpace s')) (clift (t_hrs_' (globals x))) tcb_ptr_to_ctcb_ptr ctcb_relation"
  using om
proof (rule cor_map_relI [OF option_map_eq_dom_eq])
  fix x tcb tcb' z
  assume y: "map_to_tcbs (ksPSpace s) x = Some tcb"
    and y': "map_to_tcbs (ksPSpace s') x = Some tcb'" and rel: "ctcb_relation tcb z"
    
  hence "tcb_no_ctes_proj tcb = tcb_no_ctes_proj tcb'" using om
    apply -    
    apply (simp add: o_def)
    apply (drule fun_cong [where x = x])
    apply simp
    done
  
  thus "ctcb_relation tcb' z" using rel
    unfolding tcb_no_ctes_proj_def ctcb_relation_def cfault_rel_def
    by auto
qed fact+

lemma lifth_update:
  "clift (t_hrs_' s) ptr = clift (t_hrs_' s') ptr
  \<Longrightarrow> lifth ptr s = lifth ptr s'"
  unfolding lifth_def
  by simp
  
lemma getCTE_exs_valid:
  "cte_at' dest s \<Longrightarrow> \<lbrace>op = s\<rbrace> getCTE dest \<exists>\<lbrace>\<lambda>r. op = s\<rbrace>"
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
  apply (clarsimp elim: imageE simp: dom_def)
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
  apply (clarsimp simp: ccte_relation_def option_map_Some_eq2) 
  done

lemma cmdbnode_relationE:
  "\<lbrakk>cmdbnode_relation m v; m = mdb_node_to_H (mdb_node_lift v) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  unfolding cmdbnode_relation_def
  apply (drule sym)
  apply clarsimp
  done

(* Used when the rel changes as well *)
lemma cmap_relation_upd_relI:
  fixes am :: "word32 \<rightharpoonup> 'a" and cm :: "'b typ_heap"
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
  apply (simp add: inj_eq split: split_if_asm)
  apply (erule (2) rel)
  apply (erule (2) cmap_relation_relI)
  done

lemma cmap_relation_updI:
  fixes am :: "word32 \<rightharpoonup> 'a" and cm :: "'b typ_heap"
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
    apply (subst (asm) option_map_Some_eq2)
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
           simp: map_comp_Some_iff ccte_relation_def c_valid_cte_def cl_valid_cte_def option_map_Some_eq2)
  apply simp
done

(* FIXME: move, generic *)
lemma aligned_neg_mask [simp]:
  "is_aligned x n \<Longrightarrow> x && ~~ mask n = x"
  apply (erule is_aligned_get_word_bits)
   apply (rule iffD2 [OF mask_in_range])
    apply assumption
   apply simp
  apply (simp add: power_overflow NOT_mask)
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

declare word_neq_0_conv [simp del]

lemma ctes_of_not_0 [simp]:
  assumes vm: "valid_mdb' s"
  and    cof: "ctes_of s p = Some cte"
  shows  "p \<noteq> 0"
proof -
  from vm have "no_0 (ctes_of s)" 
    unfolding valid_mdb'_def by auto
  thus ?thesis using cof 
    by auto
qed


(* For getting rid of the generated guards -- will probably break with c_guard*)
lemma ctes_of_aligned_3 [simp]:
  assumes pa: "pspace_aligned' s"
  and    cof: "ctes_of s p = Some cte"
  shows  "is_aligned p 3"
proof -
  from cof have "cte_wp_at' (op = cte) p s"
    by (simp add: cte_wp_at_ctes_of)
  thus ?thesis
    apply (rule cte_wp_atE')
    apply (simp add: cte_level_bits_def is_aligned_weaken)
  apply (simp add: tcb_cte_cases_def field_simps split: split_if_asm )
      apply ((erule aligned_add_aligned, simp_all add: is_aligned_def word_bits_conv)[1])+
  apply (simp add: is_aligned_weaken)
  done
qed

lemma mdbNext_not_zero_eq:
  "cmdbnode_relation n n' \<Longrightarrow> \<forall>s s'. (s, s') \<in> rf_sr (*ja \<and> (is_aligned (mdbNext n) 3)*)
  \<longrightarrow> (mdbNext n \<noteq> 0) = (s' \<in> {_. mdbNext_CL (mdb_node_lift n') \<noteq> 0})"
  apply clarsimp 
  apply (erule cmdbnode_relationE)
  apply (fastforce simp: mdbNext_to_H)
  done

lemma mdbPrev_not_zero_eq:
  "cmdbnode_relation n n' \<Longrightarrow> \<forall>s s'. (s, s') \<in> rf_sr (*ja\<and> (is_aligned (mdbPrev n) 3)*)
  \<longrightarrow> (mdbPrev n \<noteq> 0) = (s' \<in> {_. mdbPrev_CL (mdb_node_lift n') \<noteq> 0})"
  apply clarsimp 
  apply (erule cmdbnode_relationE)
  apply (unfold mdb_node_to_H_def)
  apply (fastforce)
  done

declare is_aligned_0 [simp]
      
abbreviation
  "nullCapPointers cte \<equiv> cteCap cte = NullCap \<and> mdbNext (cteMDBNode cte) = nullPointer \<and> mdbPrev (cteMDBNode cte) = nullPointer"

lemma nullCapPointers_def:
  "is_an_abbreviation" unfolding is_an_abbreviation_def by simp

lemma valid_mdb_ctes_of_next:
  "\<lbrakk> valid_mdb' s; ctes_of s p = Some cte; mdbNext (cteMDBNode cte) \<noteq> 0 \<rbrakk> \<Longrightarrow> cte_at' (mdbNext (cteMDBNode cte)) s"
  unfolding valid_mdb'_def valid_mdb_ctes_def
  apply clarsimp
  apply (erule (2) valid_dlistE)
  apply (simp add: cte_wp_at_ctes_of)
  done

lemma valid_mdb_ctes_of_prev:
  "\<lbrakk> valid_mdb' s; ctes_of s p = Some cte; mdbPrev (cteMDBNode cte) \<noteq> 0 \<rbrakk> \<Longrightarrow> cte_at' (mdbPrev (cteMDBNode cte)) s"
  unfolding valid_mdb'_def valid_mdb_ctes_def
  apply clarsimp
  apply (erule (2) valid_dlistE)
  apply (simp add: cte_wp_at_ctes_of)
  done

context kernel
begin

definition
  rf_sr :: "(KernelStateData_H.kernel_state \<times> cstate) set"
  where
  "rf_sr \<equiv> {(s, s'). cstate_relation s (globals s')}"

lemma cmap_relation_tcb [intro]:
  "(s, s') \<in> rf_sr \<Longrightarrow> cpspace_tcb_relation (ksPSpace s) (t_hrs_' (globals s'))"
  unfolding rf_sr_def state_relation_def cstate_relation_def cpspace_relation_def
  by (simp add: Let_def)

lemma cmap_relation_ep [intro]:
  "(s, s') \<in> rf_sr \<Longrightarrow> cpspace_ep_relation (ksPSpace s) (t_hrs_' (globals s'))"
  unfolding rf_sr_def state_relation_def cstate_relation_def cpspace_relation_def
  by (simp add: Let_def)

lemma cmap_relation_aep [intro]:
  "(s, s') \<in> rf_sr \<Longrightarrow> cpspace_aep_relation (ksPSpace s) (t_hrs_' (globals s'))"
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
lemma rf_sr_cpde_relation:
  "(s, s') \<in> rf_sr \<Longrightarrow> cmap_relation (map_to_pdes (ksPSpace s))
                         (cslift s') pde_Ptr cpde_relation"
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
  by (clarsimp simp: option_map_Some_eq2 if_bool_eq_conj)

lemma ccte_relation_cmdbnode_relation:
  "ccte_relation cte cte' \<Longrightarrow> cmdbnode_relation (cteMDBNode cte) (cte_C.cteMDBNode_C cte')"
  unfolding ccte_relation_def ccap_relation_def
  by (clarsimp simp: option_map_Some_eq2)

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
  ksSchedulerAction_' s = ksSchedulerAction_' t; 
  ksCurThread_' s = ksCurThread_' t;
  ksIdleThread_' s = ksIdleThread_' t;
  ksWorkUnitsCompleted_' s = ksWorkUnitsCompleted_' t;
  intStateIRQNode_' s = intStateIRQNode_' t;
  intStateIRQTable_' s = intStateIRQTable_' t; 
  armKSHWASIDTable_' s = armKSHWASIDTable_' t;
  armKSASIDTable_' s = armKSASIDTable_' t;
  armKSNextASID_' s = armKSNextASID_' t;
  phantom_machine_state_' s = phantom_machine_state_' t;
  ghost'state_' s = ghost'state_' t;
  ksDomScheduleIdx_' s = ksDomScheduleIdx_' t;
  ksCurDomain_' s = ksCurDomain_' t;
  ksDomainTime_' s = ksDomainTime_' t
  \<rbrakk> 
  \<Longrightarrow> cstate_relation a s = cstate_relation a t"
  unfolding cstate_relation_def
  by (clarsimp simp add: Let_def carch_state_relation_def cmachine_state_relation_def)

lemma rf_sr_upd:
  assumes 
    "(t_hrs_' (globals x)) = (t_hrs_' (globals y))"
    "(ksReadyQueues_' (globals x)) = (ksReadyQueues_' (globals y))"  
    "(ksSchedulerAction_' (globals x)) = (ksSchedulerAction_' (globals y))"
    "(ksCurThread_' (globals x)) = (ksCurThread_' (globals y))"  
    "(ksIdleThread_' (globals x)) = (ksIdleThread_' (globals y))"
    "(ksWorkUnitsCompleted_' (globals x)) = (ksWorkUnitsCompleted_' (globals y))"
    "intStateIRQNode_'(globals x) = intStateIRQNode_' (globals y)"
    "intStateIRQTable_'(globals x) = intStateIRQTable_' (globals y)"
    "armKSHWASIDTable_' (globals x) = armKSHWASIDTable_' (globals y)"
    "armKSASIDTable_' (globals x) = armKSASIDTable_' (globals y)"
    "armKSNextASID_' (globals x) = armKSNextASID_' (globals y)"
    "phantom_machine_state_' (globals x) = phantom_machine_state_' (globals y)"
    "ghost'state_' (globals x) = ghost'state_' (globals y)"
    "ksDomScheduleIdx_' (globals x) = ksDomScheduleIdx_' (globals y)"
    "ksCurDomain_' (globals x) = ksCurDomain_' (globals y)"
    "ksDomainTime_' (globals x) = ksDomainTime_' (globals y)"
  shows "((a, x) \<in> rf_sr) = ((a, y) \<in> rf_sr)"
  unfolding rf_sr_def using assms
  by simp (rule cstate_relation_only_t_hrs, auto)

lemma rf_sr_upd_safe[simp]:
  assumes rl: "(t_hrs_' (globals (g y))) = (t_hrs_' (globals y))"
  and     rq: "(ksReadyQueues_' (globals (g y))) = (ksReadyQueues_' (globals y))"  
  and     sa: "(ksSchedulerAction_' (globals (g y))) = (ksSchedulerAction_' (globals y))"
  and     ct: "(ksCurThread_' (globals (g y))) = (ksCurThread_' (globals y))"  
  and     it: "(ksIdleThread_' (globals (g y))) = (ksIdleThread_' (globals y))"
  and     isn: "intStateIRQNode_'(globals (g y)) = intStateIRQNode_' (globals y)"
  and     ist: "intStateIRQTable_'(globals (g y)) = intStateIRQTable_' (globals y)"
  and     dsi: "ksDomScheduleIdx_' (globals (g y)) = ksDomScheduleIdx_' (globals y)"
  and     cdom: "ksCurDomain_' (globals (g y)) = ksCurDomain_' (globals y)"
  and     dt: "ksDomainTime_' (globals (g y)) = ksDomainTime_' (globals y)"
  and arch:
    "armKSHWASIDTable_' (globals (g y)) = armKSHWASIDTable_' (globals y)"
    "armKSASIDTable_' (globals (g y)) = armKSASIDTable_' (globals y)"
    "armKSNextASID_' (globals (g y)) = armKSNextASID_' (globals y)"
    "phantom_machine_state_' (globals (g y)) = phantom_machine_state_' (globals y)"
  and    gs: "ghost'state_' (globals (g y)) = ghost'state_' (globals y)"
  and     wu:  "(ksWorkUnitsCompleted_' (globals (g y))) = (ksWorkUnitsCompleted_' (globals y))"
  shows "((a, (g y)) \<in> rf_sr) = ((a, y) \<in> rf_sr)"
  using rl rq sa ct it isn ist arch wu gs dsi cdom dt by - (rule rf_sr_upd)

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
  apply (clarsimp simp: option_map_Some_eq2 c_valid_cap_def cl_valid_cap_def 
            cap_to_H_def cap_lift_def Let_def cap_tag_defs split: split_if)
  done

(* MOVE *)
lemma ko_at_valid_aep':
  "\<lbrakk> ko_at' aep p s; valid_objs' s \<rbrakk> \<Longrightarrow> valid_aep' aep s"
  apply (erule obj_atE')
  apply (erule (1) valid_objsE')
   apply (simp add: projectKOs valid_obj'_def)
   done
    
(* MOVE *)
lemma aep_blocked_in_queueD:
  "\<lbrakk> st_tcb_at' (op = (Structures_H.thread_state.BlockedOnAsyncEvent aep)) thread \<sigma>; ko_at' aep' aep \<sigma>; invs' \<sigma> \<rbrakk> 
   \<Longrightarrow> thread \<in> set (aepQueue aep') \<and> isWaitingAEP aep'"
  apply (drule sym_refs_st_tcb_atD')
   apply clarsimp
  apply (clarsimp simp: refs_of_rev' obj_at'_def ko_wp_at'_def projectKOs)
  apply (cases aep')
    apply (simp_all add: isWaitingAEP_def)
    done

(* MOVE *)  
lemma valid_aep_isWaitingAEPD:
  "\<lbrakk> valid_aep' aep s; isWaitingAEP aep \<rbrakk> \<Longrightarrow> (aepQueue aep) \<noteq> [] \<and> (\<forall>t\<in>set (aepQueue aep). tcb_at' t s) \<and> distinct (aepQueue aep)"
  unfolding valid_aep'_def isWaitingAEP_def
  by (clarsimp split: async_endpoint.splits)

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
  
lemma aep_to_ep_queue:
  assumes ko: "ko_at' aep' aep s"
  and     waiting: "isWaitingAEP aep'"
  and     rf: "(s, s') \<in> rf_sr"
  shows "ep_queue_relation' (cslift s') (aepQueue aep')
              (Ptr (aepQueue_head_CL
                     (async_endpoint_lift (the (cslift s' (Ptr aep))))))
              (Ptr (aepQueue_tail_CL
                     (async_endpoint_lift (the (cslift s' (Ptr aep))))))"
proof -
  from rf have
    "cmap_relation (map_to_aeps (ksPSpace s)) (cslift s') Ptr (casync_endpoint_relation (cslift s'))"
    by (rule cmap_relation_aep)
  
  thus ?thesis using ko waiting
    apply -
    apply (erule (1) cmap_relation_ko_atE)
    apply (clarsimp simp: casync_endpoint_relation_def Let_def isWaitingAEP_def split: async_endpoint.splits)
    done
qed

lemma map_to_tcbs_from_tcb_at:
  "tcb_at' thread s \<Longrightarrow> map_to_tcbs (ksPSpace s) thread \<noteq> None"
  unfolding obj_at'_def 
  by (clarsimp simp: projectKOs)

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
  apply (drule st_tcb_at_tcb_at')
  apply (erule (1) tcb_at_h_t_valid)
  done


(* MOVE *)
lemma exs_getObject:
  assumes x: "\<And>q n ko. loadObject p q n ko =
                (loadObject_default p q n ko :: ('a :: pspace_storable) kernel)"
  assumes P: "\<And>(v::'a::pspace_storable). (1 :: word32) < 2 ^ (objBits v)"
  and objat: "obj_at' (P :: ('a::pspace_storable \<Rightarrow> bool)) p s"
  shows      "\<lbrace>op = s\<rbrace> getObject p \<exists>\<lbrace>\<lambda>r :: ('a :: pspace_storable). op = s\<rbrace>"
  using objat unfolding exs_valid_def obj_at'_def
  apply clarsimp
  apply (rule_tac x = "(the (projectKO_opt ko), s)" in bexI)
   apply (clarsimp simp: split_def)
  apply (simp add: projectKO_def fail_def split: option.splits)
  apply (clarsimp simp: loadObject_default_def getObject_def in_monad return_def lookupAround2_char1
                        split_def x P lookupAround2_char1 projectKOs    
                        objBits_def[symmetric] in_magnitude_check project_inject)
  done


lemma setObject_eq:
  fixes ko :: "('a :: pspace_storable)"
  assumes x: "\<And>(val :: 'a) old ptr ptr' next. updateObject val old ptr ptr' next =
                (updateObject_default val old ptr ptr' next :: kernel_object kernel)"
  assumes P: "\<And>(v::'a::pspace_storable). (1 :: word32) < 2 ^ (objBits v)"
  and     ob: "\<And>(v :: 'a) (v' :: 'a). objBits v = objBits v'"
  and objat: "obj_at' (P :: ('a::pspace_storable \<Rightarrow> bool)) p s"  
  shows  "((), s\<lparr> ksPSpace := (ksPSpace s)(p \<mapsto> injectKO ko)\<rparr>) \<in> fst (setObject p ko s)"
  using objat unfolding setObject_def obj_at'_def
  apply (clarsimp simp: updateObject_default_def in_monad return_def lookupAround2_char1
                        split_def x P lookupAround2_char1 projectKOs 
                        objBits_def[symmetric] in_magnitude_check project_inject)
  apply (frule ssubst [OF ob, where P = "is_aligned p" and v1 = ko])  
  apply (simp add: P in_magnitude_check)
  apply (rule conjI)
   apply (rule_tac x = obj in exI)
   apply simp
  apply (erule ssubst [OF ob])
  done

lemma getObject_eq:
  fixes ko :: "'a :: pspace_storable"
  assumes x: "\<And>q n ko. loadObject p q n ko =
                (loadObject_default p q n ko :: 'a kernel)"
  assumes P: "\<And>(v::'a). (1 :: word32) < 2 ^ (objBits v)"
  and objat: "ko_at' ko p s"
  shows      "(ko, s) \<in> fst (getObject p s)"
  using objat unfolding exs_valid_def obj_at'_def
  apply clarsimp
  apply (simp add: projectKO_def fail_def split: option.splits)
  apply (clarsimp simp: loadObject_default_def getObject_def in_monad return_def lookupAround2_char1
                        split_def x P lookupAround2_char2 projectKOs    
                        objBits_def[symmetric] in_magnitude_check project_inject)
  done

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
    apply (simp add: objBits_simps)
   apply assumption
  apply (drule setObject_eq [rotated -1])
     apply simp
    apply (simp add: objBits_simps)
   apply (simp add: objBits_simps)
  apply simp
  done

definition
  "tcb_null_ep_ptrs a \<equiv> a \<lparr> tcbEPNext_C := NULL, tcbEPPrev_C := NULL \<rparr>"

definition
  "tcb_null_sched_ptrs a \<equiv> a \<lparr> tcbSchedNext_C := NULL, tcbSchedPrev_C := NULL \<rparr>"

definition
  "tcb_null_queue_ptrs a \<equiv> a \<lparr> tcbSchedNext_C := NULL, tcbSchedPrev_C := NULL, tcbEPNext_C := NULL, tcbEPPrev_C := NULL\<rparr>"

lemma null_sched_queue:
  "option_map tcb_null_sched_ptrs \<circ> mp = option_map tcb_null_sched_ptrs \<circ> mp'
  \<Longrightarrow> option_map tcb_null_queue_ptrs \<circ> mp = option_map tcb_null_queue_ptrs \<circ> mp'"
  apply (rule ext)  
  apply (erule_tac x = x in option_map_comp_eqE)
   apply simp
  apply (clarsimp simp: tcb_null_queue_ptrs_def tcb_null_sched_ptrs_def)
  done
  
lemma null_ep_queue:
  "option_map tcb_null_ep_ptrs \<circ> mp = option_map tcb_null_ep_ptrs \<circ> mp'
  \<Longrightarrow> option_map tcb_null_queue_ptrs \<circ> mp = option_map tcb_null_queue_ptrs \<circ> mp'"
  apply (rule ext)  
  apply (erule_tac x = x in option_map_comp_eqE)
   apply simp
  apply (case_tac v, case_tac v')
  apply (clarsimp simp: tcb_null_queue_ptrs_def tcb_null_ep_ptrs_def)
  done

lemma null_sched_epD:
  assumes om: "option_map tcb_null_sched_ptrs \<circ> mp = option_map tcb_null_sched_ptrs \<circ> mp'"
  shows "option_map tcbEPNext_C \<circ> mp = option_map tcbEPNext_C \<circ> mp' \<and>
         option_map tcbEPPrev_C \<circ> mp = option_map tcbEPPrev_C \<circ> mp'"
  using om
  apply -
  apply (rule conjI)
   apply (rule ext)  
   apply (erule_tac x = x in option_map_comp_eqE )
    apply simp
   apply (case_tac v, case_tac v')
   apply (clarsimp simp: tcb_null_sched_ptrs_def)
  apply (rule ext)  
  apply (erule_tac x = x in option_map_comp_eqE )
   apply simp
  apply (case_tac v, case_tac v')
  apply (clarsimp simp: tcb_null_sched_ptrs_def)  
  done

lemma null_ep_schedD:
  assumes om: "option_map tcb_null_ep_ptrs \<circ> mp = option_map tcb_null_ep_ptrs \<circ> mp'"
  shows "option_map tcbSchedNext_C \<circ> mp = option_map tcbSchedNext_C \<circ> mp' \<and>
         option_map tcbSchedPrev_C \<circ> mp = option_map tcbSchedPrev_C \<circ> mp'"
  using om
  apply -
  apply (rule conjI)
   apply (rule ext)  
   apply (erule_tac x = x in option_map_comp_eqE )
    apply simp
   apply (case_tac v, case_tac v')
   apply (clarsimp simp: tcb_null_ep_ptrs_def)
  apply (rule ext)  
  apply (erule_tac x = x in option_map_comp_eqE )
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
  -- "clag"
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

lemma ctcb_relation_null_queue_ptrs:
  assumes rel: "cmap_relation mp mp' tcb_ptr_to_ctcb_ptr ctcb_relation"
  and same: "option_map tcb_null_queue_ptrs \<circ> mp'' = option_map tcb_null_queue_ptrs \<circ> mp'"
  shows "cmap_relation mp mp'' tcb_ptr_to_ctcb_ptr ctcb_relation"
  using rel 
  apply (rule iffD1 [OF cmap_relation_cong, OF _ option_map_eq_dom_eq, rotated -1])
    apply simp
   apply (rule same [symmetric])
  apply (drule compD [OF same])
  apply (case_tac b, case_tac b')
  apply (simp add: ctcb_relation_def tcb_null_queue_ptrs_def)
  done

lemma map_to_ko_atI':
  "\<lbrakk>(projectKO_opt \<circ>\<^sub>m (ksPSpace s)) x = Some v; invs' s\<rbrakk> \<Longrightarrow> ko_at' v x s"
  apply (clarsimp simp: map_comp_Some_iff)
  apply (erule aligned_distinct_obj_atI')
    apply clarsimp
   apply clarsimp
  apply (simp add: project_inject)
  done

(* Levity: added (20090419 09:44:27) *)
declare aepQueue_head_mask_4 [simp]

lemma aepQueue_tail_mask_4 [simp]:
  "aepQueue_tail_CL (async_endpoint_lift ko') && ~~ mask 4 = aepQueue_tail_CL (async_endpoint_lift ko')"
  unfolding async_endpoint_lift_def
  by (clarsimp simp: mask_def word_bw_assocs)

lemma map_to_ctes_upd_tcb_no_ctes:
  "\<lbrakk>ko_at' tcb thread s ; \<forall>x\<in>ran tcb_cte_cases. (\<lambda>(getF, setF). getF tcb' = getF tcb) x \<rbrakk>
  \<Longrightarrow> map_to_ctes (ksPSpace s(thread \<mapsto> KOTCB tcb')) = map_to_ctes (ksPSpace s)"
  apply (erule obj_atE')
  apply (simp add: projectKOs objBits_simps)  
  apply (subst map_to_ctes_upd_tcb')
     apply assumption+
  apply (rule ext)
  apply (clarsimp split: split_if)
  apply (drule (1) bspec [OF _ ranI])
  apply simp
  done

lemma update_aep_map_tos:
  fixes P :: "async_endpoint \<Rightarrow> bool"
  assumes at: "obj_at' P p s"
  shows   "map_to_eps (ksPSpace s(p \<mapsto> KOAEndpoint ko)) = map_to_eps (ksPSpace s)"
  and     "map_to_tcbs (ksPSpace s(p \<mapsto> KOAEndpoint ko)) = map_to_tcbs (ksPSpace s)"
  and     "map_to_ctes (ksPSpace s(p \<mapsto> KOAEndpoint ko)) = map_to_ctes (ksPSpace s)"
  and     "map_to_pdes (ksPSpace s(p \<mapsto> KOAEndpoint ko)) = map_to_pdes (ksPSpace s)"
  and     "map_to_ptes (ksPSpace s(p \<mapsto> KOAEndpoint ko)) = map_to_ptes (ksPSpace s)"
  and     "map_to_asidpools (ksPSpace s(p \<mapsto> KOAEndpoint ko)) = map_to_asidpools (ksPSpace s)"
  and     "map_to_user_data (ksPSpace s(p \<mapsto> KOAEndpoint ko)) = map_to_user_data (ksPSpace s)"
  using at
  by (auto elim!: obj_atE' intro!: map_to_ctes_upd_other map_comp_eqI
    simp: projectKOs projectKO_opts_defs split: kernel_object.splits split_if_asm)+

lemma update_ep_map_tos:
  fixes P :: "endpoint \<Rightarrow> bool"
  assumes at: "obj_at' P p s"
  shows   "map_to_aeps (ksPSpace s(p \<mapsto> KOEndpoint ko)) = map_to_aeps (ksPSpace s)"
  and     "map_to_tcbs (ksPSpace s(p \<mapsto> KOEndpoint ko)) = map_to_tcbs (ksPSpace s)"
  and     "map_to_ctes (ksPSpace s(p \<mapsto> KOEndpoint ko)) = map_to_ctes (ksPSpace s)"
  and     "map_to_pdes (ksPSpace s(p \<mapsto> KOEndpoint ko)) = map_to_pdes (ksPSpace s)"
  and     "map_to_ptes (ksPSpace s(p \<mapsto> KOEndpoint ko)) = map_to_ptes (ksPSpace s)"
  and     "map_to_asidpools (ksPSpace s(p \<mapsto> KOEndpoint ko)) = map_to_asidpools (ksPSpace s)"
  and     "map_to_user_data (ksPSpace s(p \<mapsto> KOEndpoint ko)) = map_to_user_data (ksPSpace s)"
  using at
  by (auto elim!: obj_atE' intro!: map_to_ctes_upd_other map_comp_eqI
    simp: projectKOs projectKO_opts_defs split: kernel_object.splits split_if_asm)+

lemma update_tcb_map_tos:
  fixes P :: "tcb \<Rightarrow> bool"
  assumes at: "obj_at' P p s"
  shows   "map_to_eps (ksPSpace s(p \<mapsto> KOTCB ko)) = map_to_eps (ksPSpace s)"
  and     "map_to_aeps (ksPSpace s(p \<mapsto> KOTCB ko)) = map_to_aeps (ksPSpace s)"
  and     "map_to_pdes (ksPSpace s(p \<mapsto> KOTCB ko)) = map_to_pdes (ksPSpace s)"
  and     "map_to_ptes (ksPSpace s(p \<mapsto> KOTCB ko)) = map_to_ptes (ksPSpace s)"
  and     "map_to_asidpools (ksPSpace s(p \<mapsto> KOTCB ko)) = map_to_asidpools (ksPSpace s)"
  and     "map_to_user_data (ksPSpace s(p \<mapsto> KOTCB ko)) = map_to_user_data (ksPSpace s)"
  using at
  by (auto elim!: obj_atE' intro!: map_to_ctes_upd_other map_comp_eqI
    simp: projectKOs projectKO_opts_defs split: kernel_object.splits split_if_asm)+

lemma update_asidpool_map_tos:
  fixes P :: "asidpool \<Rightarrow> bool"
  assumes at: "obj_at' P p s"
  shows   "map_to_aeps (ksPSpace s(p \<mapsto> KOArch (KOASIDPool ap))) = map_to_aeps (ksPSpace s)"
  and     "map_to_tcbs (ksPSpace s(p \<mapsto> KOArch (KOASIDPool ap))) = map_to_tcbs (ksPSpace s)"
  and     "map_to_ctes (ksPSpace s(p \<mapsto> KOArch (KOASIDPool ap))) = map_to_ctes (ksPSpace s)"
  and     "map_to_pdes (ksPSpace s(p \<mapsto> KOArch (KOASIDPool ap))) = map_to_pdes (ksPSpace s)"
  and     "map_to_ptes (ksPSpace s(p \<mapsto> KOArch (KOASIDPool ap))) = map_to_ptes (ksPSpace s)"
  and     "map_to_eps  (ksPSpace s(p \<mapsto> KOArch (KOASIDPool ap))) = map_to_eps (ksPSpace s)"
  and     "map_to_user_data (ksPSpace s(p \<mapsto> KOArch (KOASIDPool ap))) = map_to_user_data (ksPSpace s)"
  using at
  by (auto elim!: obj_atE' intro!: map_to_ctes_upd_other map_comp_eqI
      simp: projectKOs projectKO_opts_defs
     split: split_if split_if_asm Structures_H.kernel_object.split_asm
            arch_kernel_object.split_asm)

lemma update_asidpool_map_to_asidpools:
  "map_to_asidpools (ksPSpace s(p \<mapsto> KOArch (KOASIDPool ap)))
             = (map_to_asidpools (ksPSpace s))(p \<mapsto> ap)"
  by (rule ext, clarsimp simp: projectKOs map_comp_def split: split_if)

lemma update_pte_map_to_ptes:
  "map_to_ptes (ksPSpace s(p \<mapsto> KOArch (KOPTE pte)))
             = (map_to_ptes (ksPSpace s))(p \<mapsto> pte)"
  by (rule ext, clarsimp simp: projectKOs map_comp_def split: split_if)

lemma update_pte_map_tos:
  fixes P :: "pte \<Rightarrow> bool"
  assumes at: "obj_at' P p s"
  shows   "map_to_aeps (ksPSpace s(p \<mapsto> (KOArch (KOPTE pte)))) = map_to_aeps (ksPSpace s)"
  and     "map_to_tcbs (ksPSpace s(p \<mapsto> (KOArch (KOPTE pte)))) = map_to_tcbs (ksPSpace s)"
  and     "map_to_ctes (ksPSpace s(p \<mapsto> (KOArch (KOPTE pte)))) = map_to_ctes (ksPSpace s)"
  and     "map_to_pdes (ksPSpace s(p \<mapsto> (KOArch (KOPTE pte)))) = map_to_pdes (ksPSpace s)"
  and     "map_to_eps  (ksPSpace s(p \<mapsto> (KOArch (KOPTE pte)))) = map_to_eps (ksPSpace s)"
  and     "map_to_asidpools (ksPSpace s(p \<mapsto> (KOArch (KOPTE pte)))) = map_to_asidpools (ksPSpace s)"
  and     "map_to_user_data (ksPSpace s(p \<mapsto> (KOArch (KOPTE pte)))) = map_to_user_data (ksPSpace s)"
  using at
  by (auto elim!: obj_atE' intro!: map_comp_eqI map_to_ctes_upd_other
           split: split_if_asm split_if
            simp: projectKOs,
       auto simp: projectKO_opts_defs)

lemma update_pde_map_to_pdes:
  "map_to_pdes (ksPSpace s(p \<mapsto> KOArch (KOPDE pde)))
             = (map_to_pdes (ksPSpace s))(p \<mapsto> pde)"
  by (rule ext, clarsimp simp: projectKOs map_comp_def split: split_if)

lemma update_pde_map_tos:
  fixes P :: "pde \<Rightarrow> bool"
  assumes at: "obj_at' P p s"
  shows   "map_to_aeps (ksPSpace s(p \<mapsto> (KOArch (KOPDE pde)))) = map_to_aeps (ksPSpace s)"
  and     "map_to_tcbs (ksPSpace s(p \<mapsto> (KOArch (KOPDE pde)))) = map_to_tcbs (ksPSpace s)"
  and     "map_to_ctes (ksPSpace s(p \<mapsto> (KOArch (KOPDE pde)))) = map_to_ctes (ksPSpace s)"
  and     "map_to_ptes (ksPSpace s(p \<mapsto> (KOArch (KOPDE pde)))) = map_to_ptes (ksPSpace s)"
  and     "map_to_eps  (ksPSpace s(p \<mapsto> (KOArch (KOPDE pde)))) = map_to_eps (ksPSpace s)"
  and     "map_to_asidpools (ksPSpace s(p \<mapsto> (KOArch (KOPDE pde)))) = map_to_asidpools (ksPSpace s)"
  and     "map_to_user_data (ksPSpace s(p \<mapsto> (KOArch (KOPDE pde)))) = map_to_user_data (ksPSpace s)"
  using at
  by (auto elim!: obj_atE' intro!: map_comp_eqI map_to_ctes_upd_other
           split: split_if_asm split_if
            simp: projectKOs,
       auto simp: projectKO_opts_defs)


lemma heap_to_page_data_cong [cong]:
  "\<lbrakk> map_to_user_data ks = map_to_user_data ks'; bhp = bhp' \<rbrakk>
  \<Longrightarrow> heap_to_page_data ks bhp = heap_to_page_data ks' bhp'"
  unfolding heap_to_page_data_def by simp

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

fun
  thread_state_to_tsType :: "thread_state \<Rightarrow> word32"
where
  "thread_state_to_tsType (Structures_H.Running) = scast ThreadState_Running"
  | "thread_state_to_tsType (Structures_H.Restart) = scast ThreadState_Restart"
  | "thread_state_to_tsType (Structures_H.Inactive) = scast ThreadState_Inactive"
  | "thread_state_to_tsType (Structures_H.IdleThreadState) = scast ThreadState_IdleThreadState"
  | "thread_state_to_tsType (Structures_H.BlockedOnReply) = scast ThreadState_BlockedOnReply"
  | "thread_state_to_tsType (Structures_H.BlockedOnReceive oref dimin) = scast ThreadState_BlockedOnReceive"
  | "thread_state_to_tsType (Structures_H.BlockedOnSend oref badge cg isc) = scast ThreadState_BlockedOnSend"
  | "thread_state_to_tsType (Structures_H.BlockedOnAsyncEvent oref) = scast ThreadState_BlockedOnAsyncEvent"


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
  cap_rights_from_word_canon :: "word32 \<Rightarrow> cap_rights_CL"
  where
  "cap_rights_from_word_canon wd \<equiv> 
    \<lparr> capAllowGrant_CL = from_bool (wd !! 2),
      capAllowRead_CL = from_bool (wd !! 1),
      capAllowWrite_CL = from_bool (wd !! 0)\<rparr>"

definition 
  cap_rights_from_word :: "word32 \<Rightarrow> cap_rights_CL"
  where
  "cap_rights_from_word wd \<equiv> SOME cr. 
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

lemma small_frame_cap_is_mapped_alt:
  "cap_get_tag cp = scast cap_small_frame_cap \<Longrightarrow>
   (cap_small_frame_cap_CL.capFMappedASIDHigh_CL (cap_small_frame_cap_lift cp) = 0
       \<and> cap_small_frame_cap_CL.capFMappedASIDLow_CL (cap_small_frame_cap_lift cp) = 0)
    = ((cap_small_frame_cap_CL.capFMappedASIDHigh_CL (cap_small_frame_cap_lift cp)
              << asidLowBits)
         + cap_small_frame_cap_CL.capFMappedASIDLow_CL (cap_small_frame_cap_lift cp)
              = 0)"
  apply (simp add: cap_lift_small_frame_cap cap_small_frame_cap_lift_def)
  apply (subst word_plus_and_or_coroll)
   apply (rule word_eqI)
   apply (clarsimp simp: word_ops_nth_size nth_shiftl asid_low_bits_def)
  apply (simp add: word_or_zero)
  apply safe
   apply simp
  apply (rule word_eqI)
  apply (drule_tac x="n + asid_low_bits" in word_eqD)+
  apply (clarsimp simp add: word_ops_nth_size asid_low_bits_def nth_shiftl nth_shiftr)
  done

lemma frame_cap_is_mapped_alt:
  "cap_get_tag cp = scast cap_frame_cap \<Longrightarrow>
   (cap_frame_cap_CL.capFMappedASIDHigh_CL (cap_frame_cap_lift cp) = 0
       \<and> cap_frame_cap_CL.capFMappedASIDLow_CL (cap_frame_cap_lift cp) = 0)
    = ((cap_frame_cap_CL.capFMappedASIDHigh_CL (cap_frame_cap_lift cp)
              << asidLowBits)
         + cap_frame_cap_CL.capFMappedASIDLow_CL (cap_frame_cap_lift cp)
              = 0)"
  apply (simp add: cap_lift_frame_cap cap_frame_cap_lift_def)
  apply (subst word_plus_and_or_coroll)
   apply (rule word_eqI)
   apply (clarsimp simp: word_ops_nth_size nth_shiftl asid_low_bits_def)
  apply (simp add: word_or_zero)
  apply safe
   apply simp
  apply (rule word_eqI)
  apply (drule_tac x="n + asid_low_bits" in word_eqD)+
  apply (clarsimp simp add: word_ops_nth_size asid_low_bits_def nth_shiftl nth_shiftr)
  done

lemma cmap_relation_updI2:
  fixes am :: "word32 \<rightharpoonup> 'a" and cm :: "'b typ_heap"
  assumes cr: "cmap_relation am cm f rel"
  and   cof: "am dest = None"
  and   cc:  "rel nv nv'"
  and   inj: "inj f"
  shows "cmap_relation (am(dest \<mapsto> nv)) (cm(f dest \<mapsto> nv')) f rel"
  using cr cof cc inj
  by (clarsimp simp add: cmap_relation_def inj_eq split: split_if)

definition
  user_word_at :: "word32 \<Rightarrow> word32 \<Rightarrow> kernel_state \<Rightarrow> bool"
where
 "user_word_at x p \<equiv> \<lambda>s. is_aligned p 2
       \<and> pointerInUserData p s
       \<and> x = word_rcat (map (underlying_memory (ksMachineState s))
                                [p + 3, p + 2, p + 1, p])"

lemma rf_sr_heap_relation:
  "(s, s') \<in> rf_sr \<Longrightarrow> cmap_relation
      (heap_to_page_data (ksPSpace s) (underlying_memory (ksMachineState s)))
      (cslift s') Ptr cuser_data_relation"
  by (clarsimp simp: user_word_at_def rf_sr_def
                     cstate_relation_def Let_def
                     cpspace_relation_def)

lemma ko_at_projectKO_opt:
  "ko_at' ko p s \<Longrightarrow> (projectKO_opt \<circ>\<^sub>m ksPSpace s) p = Some ko"
  by (clarsimp elim!: obj_atE' simp: projectKOs)

lemma int_and_leR:
  "0 \<le> b \<Longrightarrow> a AND b \<le> (b :: int)"
  by (clarsimp simp: int_and_le bin_sign_def split: split_if_asm)

lemma int_and_leL:
  "0 \<le> a \<Longrightarrow> a AND b \<le> (a :: int)"
  by (metis int_and_leR int_and_comm)

lemma user_word_at_cross_over:
  "\<lbrakk> user_word_at x p s; (s, s') \<in> rf_sr; p' = Ptr p \<rbrakk>
   \<Longrightarrow> c_guard p' \<and> hrs_htd (t_hrs_' (globals s')) \<Turnstile>\<^sub>t p'
         \<and> h_val (hrs_mem (t_hrs_' (globals s'))) p' = x"
  apply (drule rf_sr_heap_relation)
  apply (erule cmap_relationE1)
   apply (clarsimp simp: heap_to_page_data_def Let_def
                         user_word_at_def pointerInUserData_def
                         typ_at_to_obj_at'[where 'a=user_data, simplified])
   apply (drule obj_at_ko_at', clarsimp)
   apply (rule conjI, rule exI, erule ko_at_projectKO_opt)
   apply (rule refl)
  apply (thin_tac "heap_to_page_data a b c = d" for a b c d)
  apply (cut_tac x=p and w="~~ mask pageBits" in word_plus_and_or_coroll2)
  apply (rule conjI)
   apply (clarsimp simp: user_word_at_def pointerInUserData_def)
   apply (simp add: c_guard_def c_null_guard_def ptr_aligned_def)
   apply (drule lift_t_g)
   apply (clarsimp simp: )
   apply (simp add: align_of_def size_of_def)
   apply (fold is_aligned_def[where n=2, simplified], simp)
   apply (erule contra_subsetD[rotated])
   apply (rule order_trans[rotated])
    apply (rule_tac x="p && mask pageBits" and y=4 in intvl_sub_offset)
    apply (cut_tac y=p and a="mask pageBits && (~~ mask 2)" in word_and_le1)
    apply (subst(asm) word_bw_assocs[symmetric], subst(asm) aligned_neg_mask,
           erule is_aligned_andI1)
    apply (simp add: word_le_nat_alt mask_def pageBits_def)
   apply simp
  apply (clarsimp simp: cuser_data_relation_def user_word_at_def)
  apply (frule_tac f="[''words_C'']" in h_t_valid_field[OF h_t_valid_clift],
         simp+)
  apply (drule_tac n="uint (p && mask pageBits >> 2)" in h_t_valid_Array_element)
    apply simp
   apply (simp add: shiftr_over_and_dist mask_def pageBits_def uint_and)
   apply (insert int_and_leR [where a="uint (p >> 2)" and b=1023], clarsimp)[1]
  apply (simp add: field_lvalue_def
            field_lookup_offset_eq[OF trans, OF _ arg_cong[where f=Some, symmetric], OF _ pair_collapse]
            word32_shift_by_2 shiftr_shiftl1 is_aligned_andI1)
  apply (drule_tac x="ucast (p >> 2)" in spec)
  apply (simp add: byte_to_word_heap_def Let_def ucast_ucast_mask)
  apply (fold shiftl_t2n[where n=2, simplified, simplified mult.commute mult.left_commute])
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
  apply (fold shiftl_t2n[where n=2, simplified, simplified mult.commute mult.left_commute])
  apply (simp add: aligned_shiftr_mask_shiftl)
  done

(* FIXME: move to GenericLib *)
lemmas unat32_eq_of_nat = unat_eq_of_nat[where 'a=32, folded word_bits_def]

lemma user_memory_cross_over:
  "\<lbrakk>(\<sigma>, s) \<in> rf_sr; pspace_aligned' \<sigma>; pspace_distinct' \<sigma>;
    pointerInUserData ptr \<sigma>\<rbrakk>
   \<Longrightarrow> fst (t_hrs_' (globals s)) ptr = underlying_memory (ksMachineState \<sigma>) ptr"
  apply (drule_tac p="ptr && ~~ mask 2" in user_word_at_cross_over[rotated])
    apply simp
   apply (simp add: user_word_at_def Aligned.is_aligned_neg_mask
                    pointerInUserData_def pageBits_def mask_lower_twice)
  apply (clarsimp simp: h_val_def from_bytes_def typ_info_word)
  apply (drule_tac f="word_rsplit :: word32 \<Rightarrow> word8 list" in arg_cong)
  apply (simp add: word_rsplit_rcat_size word_size)
  apply (drule_tac f="\<lambda>xs. xs ! unat (ptr && mask 2)" in arg_cong)
  apply (simp add: heap_list_nth unat_mask_2_less_4
                   word_plus_and_or_coroll2 add.commute
                   hrs_mem_def)
  apply (cut_tac p=ptr in unat_mask_2_less_4)
  apply (subgoal_tac "(ptr && ~~ mask 2) + (ptr && mask 2) = ptr")
   apply (subgoal_tac "!n x. n < 4 \<longrightarrow> (unat (x\<Colon>word32) = n) = (x = of_nat n)")
    apply (auto simp add: eval_nat_numeral unat_eq_0 add.commute
                elim!: less_SucE)[1]
    apply (clarsimp simp add: unat32_eq_of_nat word_bits_def)
  apply (simp add: add.commute word_plus_and_or_coroll2)
  done

lemma cap_get_tag_isCap_ArchObject0:
  assumes cr: "ccap_relation (capability.ArchObjectCap cap) cap'"
  shows "(cap_get_tag cap' = scast cap_asid_control_cap) = isASIDControlCap cap
  \<and> (cap_get_tag cap' = scast cap_asid_pool_cap) = isASIDPoolCap cap
  \<and> (cap_get_tag cap' = scast cap_page_table_cap) = isPageTableCap cap
  \<and> (cap_get_tag cap' = scast cap_page_directory_cap) = isPageDirectoryCap cap
  \<and> (cap_get_tag cap' = scast cap_small_frame_cap) = (isPageCap cap \<and> capVPSize cap = ARMSmallPage)
  \<and> (cap_get_tag cap' = scast cap_frame_cap) = (isPageCap cap \<and> capVPSize cap \<noteq> ARMSmallPage)"
  using cr
  apply -
  apply (erule ccap_relationE)
  apply (simp add: cap_to_H_def cap_lift_def Let_def isArchCap_def)
  apply (clarsimp simp: isCap_simps cap_tag_defs word_le_nat_alt pageSize_def Let_def split: split_if_asm) -- "takes a while"
  done

lemma cap_get_tag_isCap_ArchObject:
  assumes cr: "ccap_relation (capability.ArchObjectCap cap) cap'"
  shows "(cap_get_tag cap' = scast cap_asid_control_cap) = isASIDControlCap cap"
  and "(cap_get_tag cap' = scast cap_asid_pool_cap) = isASIDPoolCap cap"
  and "(cap_get_tag cap' = scast cap_page_table_cap) = isPageTableCap cap"
  and "(cap_get_tag cap' = scast cap_page_directory_cap) = isPageDirectoryCap cap"
  and "(cap_get_tag cap' = scast cap_small_frame_cap) = (isPageCap cap \<and> capVPSize cap = ARMSmallPage)"
  and "(cap_get_tag cap' = scast cap_frame_cap) = (isPageCap cap \<and> capVPSize cap \<noteq> ARMSmallPage)"
  using cap_get_tag_isCap_ArchObject0 [OF cr] by auto


lemma cap_get_tag_isCap_unfolded_H_cap:
  shows "ccap_relation (capability.ThreadCap v0) cap' \<Longrightarrow> (cap_get_tag cap' = scast cap_thread_cap)"
  and "ccap_relation (capability.NullCap) cap' \<Longrightarrow> (cap_get_tag cap' = scast cap_null_cap)"
  and "ccap_relation (capability.AsyncEndpointCap v4 v5 v6 v7) cap' \<Longrightarrow> (cap_get_tag cap' = scast cap_async_endpoint_cap) "
  and "ccap_relation (capability.EndpointCap v8 v9 v10 v11 v12) cap' \<Longrightarrow> (cap_get_tag cap' = scast cap_endpoint_cap)"
  and "ccap_relation (capability.IRQHandlerCap v13) cap' \<Longrightarrow> (cap_get_tag cap' = scast cap_irq_handler_cap)"
  and "ccap_relation (capability.IRQControlCap) cap' \<Longrightarrow> (cap_get_tag cap' = scast cap_irq_control_cap)"
  and "ccap_relation (capability.Zombie v14 v15 v16) cap' \<Longrightarrow> (cap_get_tag cap' = scast cap_zombie_cap)"
  and "ccap_relation (capability.ReplyCap v17 v18) cap' \<Longrightarrow> (cap_get_tag cap' = scast cap_reply_cap)"
  and "ccap_relation (capability.UntypedCap v19 v20 v20b) cap' \<Longrightarrow> (cap_get_tag cap' = scast cap_untyped_cap)"
  and "ccap_relation (capability.CNodeCap v21 v22 v23 v24) cap' \<Longrightarrow> (cap_get_tag cap' = scast cap_cnode_cap)"  
  and "ccap_relation (capability.DomainCap) cap' \<Longrightarrow> (cap_get_tag cap' = scast cap_domain_cap)"

  and "ccap_relation (capability.ArchObjectCap arch_capability.ASIDControlCap) cap' \<Longrightarrow> (cap_get_tag cap' = scast cap_asid_control_cap)"  
  and "ccap_relation (capability.ArchObjectCap (arch_capability.ASIDPoolCap v28 v29)) cap' \<Longrightarrow> (cap_get_tag cap' = scast cap_asid_pool_cap)"  
  and "ccap_relation (capability.ArchObjectCap (arch_capability.PageTableCap v30 v31)) cap' \<Longrightarrow> (cap_get_tag cap' = scast cap_page_table_cap)"   
  and "ccap_relation (capability.ArchObjectCap (arch_capability.PageDirectoryCap v32 v33)) cap' \<Longrightarrow> (cap_get_tag cap' = scast cap_page_directory_cap)"   

  and "\<lbrakk>ccap_relation (capability.ArchObjectCap (arch_capability.PageCap v34 v35 v36 v37)) cap'; v36=ARMSmallPage\<rbrakk>  \<Longrightarrow> (cap_get_tag cap' = scast cap_small_frame_cap)"   
  and "\<lbrakk>ccap_relation (capability.ArchObjectCap (arch_capability.PageCap v38 v39 v40 v41)) cap'; v40\<noteq>ARMSmallPage\<rbrakk>  \<Longrightarrow> (cap_get_tag cap' = scast cap_frame_cap)"   
  and "ccap_relation (capability.ArchObjectCap (arch_capability.PageDirectoryCap v42 v43)) cap' \<Longrightarrow> (cap_get_tag cap' = scast cap_page_directory_cap)"   
  and "ccap_relation (capability.ArchObjectCap (arch_capability.PageDirectoryCap v44 v45)) cap' \<Longrightarrow> (cap_get_tag cap' = scast cap_page_directory_cap)"
  apply (simp add: cap_get_tag_isCap cap_get_tag_isCap_ArchObject isCap_simps)
  apply (frule cap_get_tag_isCap(2), simp) 
  apply (simp add: cap_get_tag_isCap cap_get_tag_isCap_ArchObject isCap_simps pageSize_def)+
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
  shows "(cap_get_tag cap' = scast cap_page_directory_cap)
           = (isArchObjectCap cap \<and> isPageDirectoryCap (capCap cap))"
  and   "(cap_get_tag cap' = scast cap_asid_pool_cap)
           = (isArchObjectCap cap \<and> isASIDPoolCap (capCap cap))"
  and   "(cap_get_tag cap' = scast cap_page_table_cap)
           = (isArchObjectCap cap \<and> isPageTableCap (capCap cap))"
  and   "(cap_get_tag cap' = scast cap_page_directory_cap)
           = (isArchObjectCap cap \<and> isPageDirectoryCap (capCap cap))"
  and   "(cap_get_tag cap' = scast cap_small_frame_cap)
           = (isArchObjectCap cap \<and> isPageCap (capCap cap) \<and> capVPSize (capCap cap) = ARMSmallPage)"
  and   "(cap_get_tag cap' = scast cap_frame_cap)
           = (isArchObjectCap cap \<and> isPageCap (capCap cap) \<and> capVPSize (capCap cap) \<noteq> ARMSmallPage)"
  by (rule cap_get_tag_isCap_ArchObject2_worker [OF _ cr],
      simp add: cap_get_tag_isCap_ArchObject,
      simp add: isArchCap_tag_def2 cap_tag_defs)+

lemma rf_sr_armKSGlobalPD:
  "(s, s') \<in> rf_sr
   \<Longrightarrow> armKSGlobalPD (ksArchState s)
         = symbol_table ''armKSGlobalPD''"
  by (clarsimp simp: rf_sr_def cstate_relation_def Let_def carch_state_relation_def carch_globals_def)

lemma ghost_assertion_size_logic':
  "unat (sz :: word32) \<le> gsMaxObjectSize s
    \<Longrightarrow> cstate_relation s gs
    \<Longrightarrow> gs_get_assn cap_get_capSizeBits_'proc (ghost'state_' gs) = 0 \<or>
            sz \<le> gs_get_assn cap_get_capSizeBits_'proc (ghost'state_' gs)"
  by (clarsimp simp: rf_sr_def cstate_relation_def Let_def ghost_size_rel_def
                     linorder_not_le word_less_nat_alt)

lemma ghost_assertion_size_logic:
  "unat (sz :: word32) \<le> gsMaxObjectSize s
    \<Longrightarrow> (s, \<sigma>) \<in> rf_sr
    \<Longrightarrow> gs_get_assn cap_get_capSizeBits_'proc (ghost'state_' (globals \<sigma>)) = 0 \<or>
            sz \<le> gs_get_assn cap_get_capSizeBits_'proc (ghost'state_' (globals \<sigma>))"
  by (clarsimp simp: rf_sr_def ghost_assertion_size_logic')

lemma gs_set_assn_Delete_cstate_relation:
  "cstate_relation s (ghost'state_'_update (gs_set_assn cteDeleteOne_'proc v) gs)
    = cstate_relation s gs"
  apply (cases "ghost'state_' gs")
  apply (auto simp: rf_sr_def cstate_relation_def Let_def carch_state_relation_def
                    cmachine_state_relation_def ghost_assertion_data_set_def
                    ghost_size_rel_def ghost_assertion_data_get_def
                    cteDeleteOne_'proc_def cap_get_capSizeBits_'proc_def)
  done

end
end

