(*
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Architecture-specific results about CNode Invocations, particularly the recursive revoke and
   delete operations *)

theory ArchCNodeInv_R
imports CNodeInv_R
begin

context Arch begin arch_global_naming

named_theorems CNodeInv_R_assms

definition arch_finalise_prop_stuff :: "(kernel_state \<Rightarrow> bool) \<Rightarrow> bool" where
  "arch_finalise_prop_stuff P = True"

lemma arch_finalise_prop_stuff_top[CNodeInv_R_assms, simp]:
  "arch_finalise_prop_stuff \<top>"
  by (simp add: arch_finalise_prop_stuff_def)

lemma acap_relation_arch_update_cap_data_NullCap[CNodeInv_R_assms]:
  "acap_relation acap acap' \<Longrightarrow>
   (arch_update_cap_data P x acap = cap.NullCap) = (Arch.updateCapData P x acap' = NullCap)"
  unfolding arch_update_cap_data_def ARM_H.updateCapData_def
  by (cases acap; simp)

lemma cnode_guard_size_bits_wordRadix[CNodeInv_R_assms]:
  "cnode_guard_size_bits = wordRadix"
  by (simp add: wordRadix_def)

lemma cteRightsBits_cnode_padding_bits[CNodeInv_R_assms]:
  "cteRightsBits = cnode_padding_bits"
  by (simp add: cteRightsBits_def)

(* FIXME arch-split: valid_cnode_capI in CNodeInv_AI exposes the value of word_bits, replace with this *)
lemma valid_cnode_capI'[CNodeInv_R_assms]:
  "\<lbrakk>cap_table_at n w s; valid_objs s; pspace_aligned s; 0 < n; length g \<le> word_bits\<rbrakk>
   \<Longrightarrow> s \<turnstile> cap.CNodeCap w n g"
  by (simp add: word_bits_def valid_cnode_capI)

lemma arch_capBadge_updateCapData_True[CNodeInv_R_assms]:
  "Arch.updateCapData True x acap \<noteq> NullCap \<Longrightarrow>
   capBadge (Arch.updateCapData True x acap) = arch_capBadge acap"
  unfolding ARM_H.updateCapData_def
  by (cases acap; simp)

crunch prepareThreadDelete
  for ctes_of[CNodeInv_R_assms, wp]: "\<lambda>s. P (ctes_of s)"

crunch prepareThreadDelete
  for not_recursive_ctes[CNodeInv_R_assms]: "\<lambda>s. P (not_recursive_ctes s)"
  (simp: prepareThreadDelete_def not_recursive_ctes_def cteCaps_of_def)

lemma in_preempt'[CNodeInv_R_assms]:
  "(Inr rv, s') \<in> fst (preemptionPoint s) \<Longrightarrow>
   \<exists>f g. s' = ksWorkUnitsCompleted_update f
                (s \<lparr> ksMachineState := ksMachineState s \<lparr> irq_state := g (irq_state (ksMachineState s)) \<rparr>\<rparr>)"
  apply (simp add: preemptionPoint_def alternative_def in_monad
                   getActiveIRQ_def doMachineOp_def split_def
                   select_f_def select_def getWorkUnits_def setWorkUnits_def
                   modifyWorkUnits_def return_def returnOk_def
              split: option.splits if_splits)
   apply (erule disjE)
     apply (cases "workUnitsLimit \<le> ksWorkUnitsCompleted s + 1", drule (1) mp,
            rule exI[where x="\<lambda>x. 0"], rule exI[where x=Suc], force,
            rule exI[where x="\<lambda>x. x + 1"], rule exI[where x=id], force)+
  apply (rule exI[where x="\<lambda>x. x + 1"], rule exI[where x=id], force)
  done

lemma sameRegionAs_eq_child:
  "\<lbrakk> sameRegionAs cap c; weak_derived' c c' \<rbrakk>
   \<Longrightarrow> sameRegionAs cap c'"
  by (clarsimp simp: weak_derived'_def sameRegionAs_def2 isCap_simps)

lemma sameRegionAs_eq_parent:
  "\<lbrakk> sameRegionAs c cap; weak_derived' c c' \<rbrakk>
   \<Longrightarrow> sameRegionAs c' cap"
  by (clarsimp simp: weak_derived'_def sameRegionAs_def2 isCap_simps)

lemma sameRegion_ep[CNodeInv_R_assms]:
  "\<lbrakk> sameRegionAs cap cap'; isEndpointCap cap \<rbrakk> \<Longrightarrow> isEndpointCap cap'"
  by (auto simp: gen_isCap_simps sameRegionAs_def3 isArchFrameCap_non_arch)

lemma sameRegion_ntfn[CNodeInv_R_assms]:
  "\<lbrakk> sameRegionAs cap cap'; isNotificationCap cap \<rbrakk> \<Longrightarrow> isNotificationCap cap'"
  by (auto simp: gen_isCap_simps sameRegionAs_def3 isArchFrameCap_non_arch)

lemma sameRegionAs_Zombie[CNodeInv_R_assms, simp]:
  "\<not> sameRegionAs (Zombie p zb n) cap"
  by (simp add: sameRegionAs_def3 isCap_simps)

lemma isFinal_notUntyped_capRange_disjoint[CNodeInv_R_assms]:
  "\<lbrakk> isFinal cap sl (cteCaps_of s); cteCaps_of s sl' = Some cap';
     sl \<noteq> sl'; capUntypedPtr cap = capUntypedPtr cap'; capBits cap = capBits cap';
     isThreadCap cap \<or> isCNodeCap cap; s \<turnstile>' cap;
     \<not> isUntypedCap cap'; \<not> isArchFrameCap cap'; \<not> isZombie cap';
     capClass cap' = PhysicalClass; valid_objs' s \<rbrakk>
   \<Longrightarrow> P"
  apply (clarsimp simp add: isFinal_def)
  apply (drule_tac x=sl' in spec)
  apply (clarsimp simp: cteCaps_of_def)
  apply (drule(1) ctes_of_valid')
  apply (elim disjE isCapDs[elim_format])
   apply (clarsimp simp: valid_cap'_def valid_arch_cap'_def vspace_table_at'_defs
                         obj_at'_def typ_at'_def ko_wp_at'_def
                  split: capability.split_asm zombie_type.split_asm
                         arch_capability.split_asm option.split_asm
                  dest!: spec[where x=0],
          (clarsimp simp: sameObjectAs_def3 isCap_simps)?)+
  done

lemma ztc_sameRegion[CNodeInv_R_assms]:
  "\<lbrakk> isCNodeCap cap \<or> isThreadCap cap \<or> isZombie cap \<rbrakk>
   \<Longrightarrow> sameRegionAs cap cap' = sameObjectAs cap cap'"
  apply (subgoal_tac "\<not> isUntypedCap cap \<and> \<not> isArchFrameCap cap
                      \<and> \<not> isIRQControlCap cap")
   apply (simp add: sameRegionAs_def3 sameObjectAs_def3)
   apply (auto simp: isCap_simps)
  done

lemma mdb_chunked_update_final[CNodeInv_R_assms]:
  assumes chunked: "mdb_chunked m"
         and slot: "m slot = Some (CTE cap node)"
         and Fin1: "\<And>x cte. m x = Some cte \<Longrightarrow> x \<noteq> slot
                        \<Longrightarrow> \<not> sameRegionAs cap (cteCap cte)"
         and Fin2: "\<And>x cte. m x = Some cte \<Longrightarrow> x \<noteq> slot
                        \<Longrightarrow> \<not> sameRegionAs cap' (cteCap cte)"
         and Fin3: "\<And>x cte. m x = Some cte \<Longrightarrow> x \<noteq> slot
                        \<Longrightarrow> sameRegionAs (cteCap cte) cap
                        \<Longrightarrow> isUntypedCap (cteCap cte)"
         and Fin4: "\<And>x cte. m x = Some cte \<Longrightarrow> x \<noteq> slot
                        \<Longrightarrow> sameRegionAs (cteCap cte) cap'
                        \<Longrightarrow> isUntypedCap (cteCap cte)"
         and capR: "capRange cap = capRange cap'"
  shows            "mdb_chunked (m (slot \<mapsto> CTE cap' node))"
           (is "mdb_chunked ?m'")
proof -
  note trancl[simp] = trancl_cap_upd [where m=m, OF slot]
  note rtrancl[simp] = rtrancl_cap_upd [where m=m, OF slot]

  have sameRegionAs:
    "\<And>x cte. \<lbrakk> m x = Some cte; x \<noteq> slot; sameRegionAs (cteCap cte) cap' \<rbrakk>
              \<Longrightarrow> sameRegionAs (cteCap cte) cap"
    apply (frule(2) Fin4)
    apply (clarsimp simp: sameRegionAs_def3 capR)
    apply (clarsimp simp: isCap_simps)
    done

  have is_chunk:
    "\<And>x cap n p p'. \<lbrakk> is_chunk m cap p p'; m x = Some (CTE cap n); x \<noteq> slot \<rbrakk> \<Longrightarrow>
                        is_chunk ?m' cap p p'"
    apply (simp add: is_chunk_def split del: if_split)
    apply (erule allEI)
    apply (clarsimp simp: slot)
    apply (frule(1) Fin3, simp)
    apply (clarsimp simp: sameRegionAs_def3 capR)
    apply (clarsimp simp: isCap_simps)
    done

  have not_chunk: "\<And>p. \<lbrakk> m \<turnstile> slot \<leadsto>\<^sup>+ p; p \<noteq> slot \<rbrakk> \<Longrightarrow> \<not> is_chunk m cap slot p"
    apply (simp add: is_chunk_def)
    apply (rule_tac x=p in exI)
    apply clarsimp
    apply (frule(1) Fin1)
    apply simp
    done

  show ?thesis using chunked
    apply (simp add: mdb_chunked_def split del: if_split)
    apply (erule allEI, erule allEI)
    apply (clarsimp split del: if_split)
    apply (clarsimp simp: slot split: if_split_asm)
      apply (frule(1) Fin2[OF _ not_sym], simp)
     apply (frule(1) sameRegionAs, clarsimp+)
     apply (simp add: not_chunk is_chunk)
    apply (simp add: is_chunk)
    done
qed

lemma sameRegionAs_ThreadCap_eq[CNodeInv_R_assms]:
  "sameRegionAs (ThreadCap p) (ThreadCap p') = (p = p')"
  by (simp add: sameRegionAs_def2 isCap_simps)

lemma sameRegionAs_IRQHandlerCap_eq[CNodeInv_R_assms]:
  "sameRegionAs (IRQHandlerCap irq) (IRQHandlerCap irq') = (irq = irq')"
  by (simp add: sameRegionAs_def2 isCap_simps)

lemma sameRegionAs_CNodeCap_eq[CNodeInv_R_assms]:
  "sameRegionAs (CNodeCap p b g gs) (CNodeCap p' b' g' gs') = (p = p' \<and> b = b')"
  by (simp add: sameRegionAs_def2 isCap_simps)

lemma ztc_untyped_helper[CNodeInv_R_assms]:
  "\<lbrakk> isCNodeCap cap' \<or> isThreadCap cap' \<or> isZombie cap'; sameRegionAs cap cap' \<rbrakk>
   \<Longrightarrow> isUntypedCap cap \<or> sameRegionAs cap' cap"
  apply (erule sameRegionAsE)
      apply (clarsimp simp: ztc_sameRegion sameObjectAs_def3)
      apply (drule_tac F="\<lambda>cap. (isNullCap cap, isZombie cap,
                                 isUntypedCap cap, isArchFrameCap cap,
                                 capRange cap)" in  master_eqE,
              simp add: gen_isCap_Master capRange_Master del: isNullCap)+
      apply (auto simp: gen_isCap_Master capRange_Master isCap_simps)[1]
     apply simp
    apply (clarsimp simp: isCap_simps)+
  done

lemma valid_arch_badges_PhysicalClass[CNodeInv_R_assms]:
  "\<lbrakk> valid_arch_badges cap'' cap' node'; capClass cap'' = PhysicalClass; capClass cap = PhysicalClass \<rbrakk>
   \<Longrightarrow> valid_arch_badges cap cap' node'"
  by (auto simp: valid_arch_badges_def isCap_simps)

lemma isFinal_Zombie[CNodeInv_R_assms]:
  "isFinal (Zombie p' b n) p cs"
  by (simp add: isFinal_def sameObjectAs_def2 gen_isCap_simps)

crunch Arch.postCapDeletion
  for no_cte_prop[wp]: "no_cte_prop P"

(* interface, above crunch does not result in same lemma on all architectures *)
lemma arch_postCapDeletion_no_cte_prop[CNodeInv_R_assms]:
  "\<lbrace>no_cte_prop P and K (arch_finalise_prop_stuff P)\<rbrace>
   Arch.postCapDeletion t
   \<lbrace>\<lambda>_. no_cte_prop P\<rbrace>"
  by wpsimp

lemma post_cap_delete_pre'_IRQHandlerCap[CNodeInv_R_assms]:
  "post_cap_delete_pre' (IRQHandlerCap irq) sl cs
   = (arch_valid_irq irq \<and> (\<forall>sl'. sl \<noteq> sl' \<longrightarrow> cs sl' \<noteq> Some (IRQHandlerCap irq)))"
  by (simp add: post_cap_delete_pre'_def)

lemma final_post_cap_delete_pre'_ArchObjectCap[CNodeInv_R_assms]:
  "\<lbrakk> isFinal (ArchObjectCap acap) sl (cteCaps_of s); arch_cap_has_cleanup' acap;
     valid_arch_cap' acap s\<rbrakk>
   \<Longrightarrow> post_cap_delete_pre' (ArchObjectCap acap) sl (cteCaps_of s)"
  by (clarsimp simp add: post_cap_delete_pre'_def arch_cap_has_cleanup'_def isCap_simps)

crunch Arch_finaliseCap, prepareThreadDelete
  for st_tcb_at'[CNodeInv_R_assms, wp]: "st_tcb_at' P t"
  (simp: crunch_simps
   wp: crunch_wps getObject_inv loadObject_default_inv
   rule: ARM_H.finaliseCap_def)

lemmas setObject_ASID_cteCaps_of[wp] = cteCaps_of_ctes_of_lift [OF setObject_ASID_ctes_of']
lemmas storePTE_cteCaps_of[wp] = cteCaps_of_ctes_of_lift [OF storePTE_ctes]
lemmas storePDE_cteCaps_of[wp] = cteCaps_of_ctes_of_lift [OF storePDE_ctes]

lemma archThreadSet_rvk_prog':
  "archThreadSet f p \<lbrace>\<lambda>s. revoke_progress_ord m (\<lambda>x. map_option capToRPO (cteCaps_of s x))\<rbrace>"
  by (wpsimp simp: cteCaps_of_def)

crunch prepareThreadDelete, Arch_finaliseCap
  for rvk_prog'[CNodeInv_R_assms]:
        "\<lambda>s. revoke_progress_ord m (\<lambda>x. option_map capToRPO (cteCaps_of s x))"
  (wp: crunch_wps emptySlot_rvk_prog' threadSet_ctesCaps_of
       getObject_inv loadObject_default_inv
   simp: crunch_simps unless_def o_def setBoundNotification_def
   ignore: setCTE threadSet
   rule: ARM_H.finaliseCap_def)

lemma cap_relation_trans[CNodeInv_R_assms]:
  "\<lbrakk> cap_relation cap cap'; cap_relation cap cap'' \<rbrakk>
   \<Longrightarrow> cap' = cap''"
  by (clarsimp split: cap_relation_split_asm arch_cap.split_asm)

crunch Arch_finaliseCap, prepareThreadDelete
  for irq_states'[CNodeInv_R_assms, wp]: valid_irq_states'
  (wp: crunch_wps unless_wp getASID_wp no_irq
       no_irq_invalidateLocalTLB_ASID no_irq_setHardwareASID
       no_irq_set_current_pd no_irq_invalidateLocalTLB_VAASID
       no_irq_cleanByVA_PoU
   simp: crunch_simps armv_contextSwitch_HWASID_def o_def setCurrentPD_to_abs
   rule: ARM_H.finaliseCap_def)

end (* Arch *)

locale Arch_mdb_swap = mdb_swap + Arch
begin

lemma isSGI_src:
  "isArchSGISignalCap scap = isArchSGISignalCap src_cap"
  using src_derived
  by (fastforce simp: isCap_simps weak_derived'_def)

lemma isSGI_dest:
  "isArchSGISignalCap dcap = isArchSGISignalCap dest_cap"
  using dest_derived
  by (fastforce simp: isCap_simps weak_derived'_def)

lemma SGI_dcap_neq:
  "isArchSGISignalCap dest_cap \<Longrightarrow> (cap \<noteq> dcap) = (cap \<noteq> dest_cap)"
  using dest_derived
  by (auto simp: weak_derived'_def isCap_simps)

lemma SGI_dcap_neq_cap:
  "isArchSGISignalCap cap \<Longrightarrow> (dcap \<noteq> cap) = (dest_cap \<noteq> cap)"
  using dest_derived
  by (auto simp: weak_derived'_def isCap_simps)

lemma SGI_scap_neq:
  "isArchSGISignalCap src_cap \<Longrightarrow> (cap \<noteq> scap) = (cap \<noteq> src_cap)"
  using src_derived
  by (auto simp: weak_derived'_def isCap_simps)

lemma SGI_scap_neq_cap:
  "isArchSGISignalCap cap \<Longrightarrow> (scap \<noteq> cap) = (src_cap \<noteq> cap)"
  using src_derived
  by (auto simp: weak_derived'_def isCap_simps)

(* export to generic below *)

lemma mdb_chunked_arch_assms_scap[simp]:
  "mdb_chunked_arch_assms scap =  mdb_chunked_arch_assms src_cap"
  by (simp add: mdb_chunked_arch_assms_def isSGI_src)

lemma mdb_chunked_arch_assms_dcap[simp]:
  "mdb_chunked_arch_assms dcap =  mdb_chunked_arch_assms dest_cap"
  by (simp add: mdb_chunked_arch_assms_def isSGI_dest)

lemma valid_arch_badges_src[simp]:
  "valid_arch_badges scap c node = valid_arch_badges src_cap c node"
  by (simp add: valid_arch_badges_def SGI_scap_neq_cap)

lemma valid_arch_badges_dest[simp]:
  "valid_arch_badges c dcap node = valid_arch_badges c dest_cap node"
  by (simp add: valid_arch_badges_def isSGI_dest SGI_dcap_neq)

lemma valid_arch_badges_dest'[simp]:
  "valid_arch_badges dcap c node = valid_arch_badges dest_cap c node"
  by (simp add: valid_arch_badges_def  SGI_dcap_neq_cap)

lemma valid_arch_badges_src'[simp]:
  "valid_arch_badges c scap node = valid_arch_badges c src_cap node"
  by (simp add: valid_arch_badges_def isSGI_src SGI_scap_neq)

end (* Arch_mdb_swap *)

context Arch_mdb_move begin

lemma sameRegionAs_parent_eq: (* FIXME arch-split: consolidate in CSpace_R *)
  "sameRegionAs cap cap' = sameRegionAs cap src_cap"
  using parency unfolding weak_derived'_def
  by (simp add: sameRegionAs_def2)

lemma sameRegion_cap'_src[simp]:
  "sameRegionAs cap' c = sameRegionAs src_cap c"
  using parency unfolding weak_derived'_def
  apply (case_tac "isReplyCap src_cap"; clarsimp)
   apply (clarsimp simp: capMasterCap_def arch_capMasterCap_def
                   split: capability.splits arch_capability.splits;
          fastforce simp: sameRegionAs_def ARM_H.sameRegionAs_def isCap_simps split: if_split_asm)+
  done

lemma mdb_chunked_arch_assms_src[simp]:
  "mdb_chunked_arch_assms cap' = mdb_chunked_arch_assms src_cap"
  by (simp add: mdb_chunked_arch_assms_def)

lemma valid_badges':
  "valid_badges m'"
proof -
  from parency
  have SGI_src_cap: "isArchSGISignalCap src_cap \<Longrightarrow> cap' = src_cap"
    unfolding weak_derived'_def
    by (clarsimp simp: isCap_simps)

  from valid
  have "valid_badges m" ..
  thus "valid_badges m'" using src dest parency
    apply (clarsimp simp: valid_badges_def2 valid_arch_badges_def)
    apply (drule m'_badged)+
    apply (drule m'_next)
    apply (clarsimp simp add: weak_derived'_def split: if_split_asm)
      apply (erule_tac x=src in allE, erule_tac x=p' in allE,
             erule allE, erule impE, erule exI)
      apply (clarsimp simp: SGI_src_cap)
     apply (erule_tac x=p in allE, erule_tac x=src in allE,
            erule allE, erule impE, erule exI)
     apply clarsimp
     apply (clarsimp simp: isCap_simps)
    apply blast
    done
qed

end (* Arch_mdb_move *)

context mdb_swap begin

(* FIXME arch-split: there's overlap here with CNodeInv_R *)
lemmas arch_assms =
  ARM.sameRegionAs_eq_child
  ARM.sameRegionAs_eq_parent
  ARM.sameRegion_ep
  ARM.sameRegion_ntfn

lemmas gen_arch_assms =
  Arch_mdb_swap.mdb_chunked_arch_assms_scap
  Arch_mdb_swap.mdb_chunked_arch_assms_dcap
  Arch_mdb_swap.valid_arch_badges_src
  Arch_mdb_swap.valid_arch_badges_dest
  Arch_mdb_swap.valid_arch_badges_src'
  Arch_mdb_swap.valid_arch_badges_dest'

(* extract arch-dependent assumptions of mdb_swap_gen proved in Arch_mdb_swap
   (faster than interpreting Arch) *)
lemmas gen_assms = gen_arch_assms[unfolded Arch_mdb_swap_def, OF mdb_swap_axioms]

sublocale mdb_swap_gen_CNodeInv_R
  by (unfold_locales)
     (fact arch_assms gen_assms)+

(* re-bind names *)
lemmas cteSwap_valid_mdb_helper = cteSwap_valid_mdb_helper

end (* mdb_swap *)

context mdb_move begin

lemmas gen_arch_assms =
  Arch_mdb_move.sameRegion_cap'_src
  Arch_mdb_move.mdb_chunked_arch_assms_src
  Arch_mdb_move.sameRegionAs_parent_eq
  Arch_mdb_move.valid_badges'

(* extract arch-dependent assumptions of mdb_move_gen proved in Arch_mdb_move
   (faster than interpreting Arch) *)
lemmas gen_assms = gen_arch_assms[unfolded Arch_mdb_move_def, OF mdb_move_axioms]

sublocale mdb_move_gen_CNodeInv_R
  by (unfold_locales)
     (fact gen_assms)+

(* re-bind names *)
lemmas cteMove_valid_mdb_helper = cteMove_valid_mdb_helper

end (* mdb_move *)

context Arch begin arch_global_naming

lemmas [CNodeInv_R_assms] =
  mdb_swap.cteSwap_valid_mdb_helper
  mdb_move.cteMove_valid_mdb_helper

end (* Arch *)

arch_requalify_consts arch_finalise_prop_stuff

interpretation CNodeInv_R?: CNodeInv_R arch_finalise_prop_stuff
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact CNodeInv_R_assms)?)?)
qed

context Arch begin arch_global_naming

sublocale cteDelete: typ_at_props' "cteDelete slot exposed"
  by typ_at_props'

sublocale reduceZombie: typ_at_props' "reduceZombie cap slot x"
  by typ_at_props'

sublocale finaliseSlot: typ_at_props' "finaliseSlot ptr exposed"
  by typ_at_props'

sublocale invokeCNode: typ_at_props' "invokeCNode i"
  by typ_at_props'

sublocale cteMove: typ_at_props' "cteMove cap src dest"
  by typ_at_props'

end  (* Arch *)

end
