(*
 * Copyright 2019, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

(*
   RISCV64 VSpace refinement
*)

theory VSpace_R
imports TcbAcc_R
begin
context Arch begin global_naming RISCV64 (*FIXME: arch_split*)

lemmas store_pte_typ_ats[wp] = store_pte_typ_ats abs_atyp_at_lifts[OF store_pte_typ_at]

end

context begin interpretation Arch . (*FIXME: arch_split*)

crunch_ignore (add: throw_on_false)

definition
  "vspace_at_asid' vs asid \<equiv> \<lambda>s. \<exists>ap pool.
             riscvKSASIDTable (ksArchState s) (ucast (asid_high_bits_of (ucast asid))) = Some ap \<and>
             ko_at' (ASIDPool pool) ap s \<and> pool (ucast (asid_low_bits_of (ucast asid))) = Some vs \<and>
             page_table_at' vs s"

lemma findVSpaceForASID_vs_at_wp:
  "\<lbrace>\<lambda>s. \<forall>pm. asid \<noteq> 0 \<and> asid_wf asid \<and> vspace_at_asid' pm asid s \<longrightarrow> P pm s\<rbrace>
    findVSpaceForASID asid
   \<lbrace>P\<rbrace>,-"
  apply (simp add: findVSpaceForASID_def assertE_def checkPTAt_def
                   asidRange_def mask_2pm1[symmetric]
                   le_mask_asidBits_asid_wf
             cong: option.case_cong split del: if_split)
  apply (wpsimp wp: getASID_wp)
  apply (erule allE; erule mp; clarsimp simp: vspace_at_asid'_def page_table_at'_def)
  apply (case_tac ko; simp)
  apply (subst (asm) inv_f_f, rule inj_onI, simp)
  apply (rule conjI, fastforce)
  apply (simp add: asid_low_bits_of_def ucast_ucast_a is_down ucast_ucast_mask asid_low_bits_def)
  by fastforce

lemma findVSpaceForASIDAssert_vs_at_wp:
  "\<lbrace>(\<lambda>s. \<forall>pd. vspace_at_asid' pd asid  s \<longrightarrow> P pd s)\<rbrace>
       findVSpaceForASIDAssert asid \<lbrace>P\<rbrace>"
  apply (simp add: findVSpaceForASIDAssert_def const_def
                   checkPTAt_def)
  apply (rule hoare_pre, wp findVSpaceForASID_vs_at_wp)
  apply simp
  done

crunch inv[wp]: findVSpaceForASIDAssert "P"
  (simp: const_def crunch_simps wp: loadObject_default_inv crunch_wps)

lemma asidBits_asid_bits[simp]:
  "asidBits = asid_bits"
  by (simp add: bit_simps' asid_bits_def asidBits_def)

lemma no_fail_read_sbadaddr[intro!,simp]:
  "no_fail \<top> read_sbadaddr"
  sorry

lemma hv_corres:
  "corres (fr \<oplus> dc) (tcb_at thread) (tcb_at' thread)
          (handle_vm_fault thread fault) (handleVMFault thread fault)"
  apply (simp add: RISCV64_H.handleVMFault_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqrE)
       apply (cases fault; simp)
      apply simp
      apply (rule corres_machine_op[where r="(=)"])
      apply (rule corres_Id, rule refl, simp)
      apply (rule no_fail_read_sbadaddr)
     apply wpsimp+
  done

lemma set_vm_root_corres [corres]:
  assumes "t' = t"
  shows "corres dc (tcb_at t and valid_arch_state and valid_objs
                      and unique_table_refs and valid_vs_lookup
                      and valid_global_objs and pspace_aligned and pspace_distinct
                      and valid_vspace_objs)
                   (no_0_obj')
                   (set_vm_root t) (setVMRoot t')"
(* FIXME RISCV: derive: "pspace_aligned' and pspace_distinct' and valid_arch_state' and tcb_at' t'" *)
sorry (* FIXME RISCV
proof -
  have P: "corres dc \<top> \<top>
        (do global_pml4 \<leftarrow> gets (x64_global_pml4 \<circ> arch_state);
            set_current_vspace_root (RISCV64.addrFromKPPtr global_pml4) 0
         od)
        (do globalPML4 \<leftarrow> gets (x64KSSKIMPML4 \<circ> ksArchState);
            RISCV64_H.setCurrentUserVSpaceRoot (addrFromKPPtr globalPML4) 0
         od)"
    apply (simp add: RISCV64_H.setCurrentUserVSpaceRoot_def set_current_vspace_root_def
                     make_cr3_def makeCR3_def)
    apply (rule corres_guard_imp)
      apply (rule corres_split_eqr)
         apply (rule set_current_cr3_corres,
                simp add: cr3_relation_def cr3_addr_mask_def addrFromKPPtr_def bit_simps)
        apply (subst corres_gets)
        apply (clarsimp simp: state_relation_def arch_state_relation_def)
       apply (wp | simp)+
    done
  have Q: "\<And>P P'. corres dc P P'
        (throwError ExceptionTypes_A.lookup_failure.InvalidRoot <catch>
         (\<lambda>_ . do global_pml4 \<leftarrow> gets (x64_global_pml4 \<circ> arch_state);
                  set_current_vspace_root (RISCV64.addrFromKPPtr global_pml4) 0
               od))
        (throwError Fault_H.lookup_failure.InvalidRoot <catch>
         (\<lambda>_ . do globalPML4 \<leftarrow> gets (x64KSSKIMPML4 \<circ> ksArchState);
                  setCurrentUserVSpaceRoot (addrFromKPPtr globalPML4) 0
               od))"
    apply (rule corres_guard_imp)
      apply (rule corres_split_catch [where f=lfr])
         apply (simp, rule P)
        apply (subst corres_throwError, simp add: lookup_failure_map_def)
       apply (wp | simp)+
    done
  show ?thesis
    unfolding set_vm_root_def setVMRoot_def getThreadVSpaceRoot_def locateSlot_conv
              catchFailure_def withoutFailure_def throw_def
              make_cr3_def makeCR3_def
    apply (rule corres_guard_imp)
      apply (rule corres_split' [where r'="(=) \<circ> cte_map"])
         apply (simp add: tcbVTableSlot_def cte_map_def objBits_def cte_level_bits_def
                          objBitsKO_def tcb_cnode_index_def to_bl_1 assms)
        apply (rule_tac R="\<lambda>thread_root. valid_arch_state and
                                         valid_vspace_objs and valid_vs_lookup and
                                         unique_table_refs o caps_of_state and
                                         valid_global_objs and valid_objs and
                                         pspace_aligned and pspace_distinct and
                                         cte_wp_at ((=) thread_root) thread_root_slot"
                    and R'="\<lambda>thread_root. pspace_aligned' and pspace_distinct' and no_0_obj'"
                 in corres_split [OF _ getSlotCap_corres])
           apply (case_tac rv; simp add: isCap_simps Q[simplified])
           apply (rename_tac arch_cap)
           apply (case_tac arch_cap; simp add: isCap_simps Q[simplified])
           apply (rename_tac pm_ptr pm_mapped)
           apply (case_tac pm_mapped; simp add: Q[simplified])
           apply (clarsimp simp: cap_asid_def)
           apply (rule corres_guard_imp)
             apply (rule corres_split_catch [where f=lfr, OF P _ wp_post_tautE wp_post_tautE])
             apply (rule corres_split_eqrE [OF _ find_vspace_for_asid_corres[OF refl]])
               apply (rule whenE_throwError_corres; simp add: lookup_failure_map_def)
               apply (simp only: liftE_bindE)
               apply (rule corres_split'[OF get_current_cr3_corres])
                 apply (rule corres_whenE[OF _ _ dc_simp])
                  apply (case_tac cur_cr3; case_tac curCR3; clarsimp simp: cr3_relation_def cr3_addr_mask_def)
                 apply (rule iffD2[OF corres_liftE_rel_sum, OF set_current_cr3_corres])
                 apply (simp add: cr3_relation_def cr3_addr_mask_def)
                apply wp
               apply wpsimp
              apply simp
              apply wp
             apply simp
             apply wp
            apply clarsimp
            apply (frule (1) cte_wp_at_valid_objs_valid_cap)
            apply (clarsimp simp: valid_cap_def mask_def word_neq_0_conv asid_wf_def asid_bits_def)
            apply (fastforce simp: valid_cap_def mask_def word_neq_0_conv)
           apply simp
          apply wpsimp
         apply (wpsimp wp: get_cap_wp)
        apply wp
       apply wp
      apply wp
    using tcb_at_cte_at_1 by auto
qed *)


lemma get_asid_pool_corres_inv':
  assumes "p' = p"
  shows "corres (\<lambda>p. (\<lambda>p'. p = p' o ucast) \<circ> inv ASIDPool)
                (asid_pool_at p and pspace_aligned and pspace_distinct) \<top>
                (get_asid_pool p) (getObject p')"
  apply (rule corres_rel_imp)
   apply (rule get_asid_pool_corres[OF assms])
  apply simp
  done

lemma dMo_no_0_obj'[wp]:
  "doMachineOp f \<lbrace>no_0_obj'\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply wp
  by (simp add: no_0_obj'_def)

lemma dMo_riscvKSASIDTable_inv[wp]:
  "doMachineOp f \<lbrace>\<lambda>s. P (riscvKSASIDTable (ksArchState s))\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply wp
  by (clarsimp)

lemma dMo_valid_arch_state'[wp]:
  "\<lbrace>\<lambda>s. P (valid_arch_state' s)\<rbrace> doMachineOp f \<lbrace>\<lambda>_ s. P (valid_arch_state' s)\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply wp
  by (clarsimp)

crunch no_0_obj'[wp]: deleteASID "no_0_obj'"
  (simp: crunch_simps wp: crunch_wps getObject_inv loadObject_default_inv)

lemma delete_asid_corres [corres]:
  assumes "asid' = ucast asid" "pm' = pm"
  shows "corres dc
          (invs and K (asid \<noteq> 0)) no_0_obj'
          (delete_asid asid pm) (deleteASID asid' pm')"
(* FIXME RISCV: derive
          (pspace_aligned' and pspace_distinct' and no_0_obj'
              and valid_arch_state' and cur_tcb')
*)
sorry (* FIXME RISCV
  using assms
  apply (simp add: delete_asid_def deleteASID_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split [OF _ corres_gets_asid])
      apply (case_tac "asid_table (asid_high_bits_of asid)", simp)
      apply clarsimp
      apply (rule_tac P="\<lambda>s. asid_high_bits_of asid \<in> dom (asidTable o ucast) \<longrightarrow>
                             asid_pool_at (the ((asidTable o ucast) (asid_high_bits_of asid))) s" and
                      P'="pspace_aligned' and pspace_distinct'" and
                      Q="invs and valid_etcbs and K (asid_wf asid \<and> asid \<noteq> 0) and
                         (\<lambda>s. x64_asid_table (arch_state s) = asidTable \<circ> ucast)" in
                      corres_split)
         prefer 2
         apply (simp add: dom_def)
         apply (rule get_asid_pool_corres_inv'[OF refl])
        apply (rule corres_when, simp add: mask_asid_low_bits_ucast_ucast asid_low_bits_of_def)
        apply (rule corres_split [OF _ hw_asid_invalidate_corres[where pm=pm]])
            apply (rule_tac P="asid_pool_at (the (asidTable (ucast (asid_high_bits_of asid))))
                               and valid_etcbs"
                        and P'="pspace_aligned' and pspace_distinct'"
                         in corres_split)
               prefer 2
               apply (simp del: fun_upd_apply)
               apply (rule set_asid_pool_corres')
               apply (simp add: inv_def mask_asid_low_bits_ucast_ucast)
               apply (rule ext)
               apply (clarsimp simp: o_def)
              apply (rule corres_split [OF _ gct_corres])
                apply simp
                apply (rule set_vm_root_corres[OF refl])
               apply wp+
             apply (thin_tac "x = f o g" for x f g)
             apply (simp del: fun_upd_apply)
             apply (fold cur_tcb_def)
           apply (wp set_asid_pool_vs_lookup_unmap'
                     set_asid_pool_vspace_objs_unmap_single)+
          apply simp
            apply (fold cur_tcb'_def)
          apply (wp | clarsimp simp: o_def)+
       apply (subgoal_tac "vspace_at_asid asid pm s")
        apply (auto simp: obj_at_def a_type_def graph_of_def
                   split: if_split_asm)[1]
       apply (simp add: vspace_at_asid_def)
       apply (rule vs_lookupI)
        apply (simp add: vs_asid_refs_def)
        apply (rule image_eqI[OF refl])
        apply (erule graph_ofI)
       apply (rule r_into_rtrancl)
       apply simp
       apply (erule vs_lookup1I [OF _ _ refl])
       apply (simp add: vs_refs_def)
       apply (rule image_eqI[rotated], erule graph_ofI)
       apply (simp add: mask_asid_low_bits_ucast_ucast)
      apply wp
      apply (simp add: o_def)
      apply (wp getASID_wp)
      apply clarsimp
      apply assumption
     apply wp+
   apply clarsimp
   apply (clarsimp simp: valid_arch_state_def valid_asid_table_def
                  dest!: invs_arch_state)
   apply blast
  apply (clarsimp simp: valid_arch_state'_def valid_asid_table'_def)
  done *)

lemma valid_arch_state_unmap_strg':
  "valid_arch_state' s \<longrightarrow>
   valid_arch_state' (s\<lparr>ksArchState :=
                        riscvKSASIDTable_update (\<lambda>_. (riscvKSASIDTable (ksArchState s))(ptr := None))
                         (ksArchState s)\<rparr>)"
  apply (simp add: valid_arch_state'_def valid_asid_table'_def)
  apply (auto simp: ran_def split: if_split_asm)
  done

lemma delete_asid_pool_corres:
  assumes "base' = ucast base" "ptr' = ptr"
  shows "corres dc (invs and K (is_aligned base asid_low_bits) and asid_pool_at ptr)
                   (no_0_obj')
                   (delete_asid_pool base ptr) (deleteASIDPool base' ptr)"
(* FIXME RISCV: derive (pspace_aligned' and pspace_distinct' and no_0_obj'
                        and valid_arch_state' and cur_tcb') *)
sorry (* FIXME RISCV
  using assms
  apply (simp add: delete_asid_pool_def deleteASIDPool_def)
  apply (rule corres_assume_pre, simp add: is_aligned_asid_low_bits_of_zero cong: corres_weak_cong)
  apply (thin_tac P for P)+
  apply (rule corres_guard_imp)
    apply (rule corres_split [OF _ corres_gets_asid])
      apply (rule corres_when)
       apply simp
      apply (simp add: liftM_def)
      apply (rule corres_split [OF _ get_asid_pool_corres'[OF refl]])
        apply (rule corres_split)
           prefer 2
           apply (rule corres_mapM [where r=dc and r'=dc], simp, simp)
               prefer 5
               apply (rule order_refl)
              apply (rule_tac P="invs and ko_at (ArchObj (arch_kernel_obj.ASIDPool pool)) ptr
                                      and [VSRef (ucast (asid_high_bits_of base)) None] \<rhd> ptr
                                      and K (is_aligned base asid_low_bits)"
                          and P'="pspace_aligned' and pspace_distinct' and no_0_obj'"
                       in corres_guard_imp)
                apply (rule corres_when)
                 apply (clarsimp simp: ucast_ucast_low_bits)
                apply (simp add: ucast_ucast_low_bits)
                apply (rule_tac pm="the (inv ASIDPool x xa)"
                         in hw_asid_invalidate_corres[OF refl refl])
               apply simp
              apply simp
             apply clarsimp
             apply ((wp|clarsimp simp: o_def)+)[3]
          apply (rule corres_split)
             prefer 2
             apply (rule corres_modify [where P=\<top> and P'=\<top>])
             apply (simp add: state_relation_def arch_state_relation_def)
             apply (rule ext)
             apply clarsimp
             apply (erule notE)
             apply (rule word_eqI[rule_format])
             apply (drule_tac x1="ucast xa" in bang_eq [THEN iffD1])
             apply (erule_tac x=n in allE)
             apply (simp add: word_size nth_ucast)
            apply (rule corres_split)
               prefer 2
               apply (rule gct_corres)
              apply (simp only:)
              apply (rule set_vm_root_corres[OF refl])
             apply wp+
         apply (rule_tac R="\<lambda>_ s. rv = x64_asid_table (arch_state s)"
                  in hoare_post_add)
         apply (drule sym, simp only: )
         apply (drule sym, simp only: )
         apply (thin_tac "P" for P)+
         apply (simp only: pred_conj_def cong: conj_cong)
         apply simp
         apply (fold cur_tcb_def)
         apply (strengthen valid_arch_state_unmap_strg
                           valid_vspace_objs_unmap_strg
                           valid_vs_lookup_unmap_strg)
         apply (wp mapM_wp')+
         apply simp
        apply (rule_tac R="\<lambda>_ s. rv' = x64KSASIDTable (ksArchState s)"
                 in hoare_post_add)
        apply (simp only: pred_conj_def cong: conj_cong)
        apply simp
        apply (strengthen valid_arch_state_unmap_strg')
        apply (fold cur_tcb'_def)
        apply (wp mapM_wp')+
        apply (clarsimp simp: cur_tcb'_def)
       apply (simp add: o_def pred_conj_def)
       apply wp
      apply (wp getASID_wp)+
   apply (clarsimp simp: conj_comms)
   apply (auto simp: vs_lookup_def intro: vs_asid_refsI)[1]
  apply clarsimp
  done
*)

crunch typ_at' [wp]: setVMRoot "\<lambda>s. P (typ_at' T p s)"
  (simp: crunch_simps)

lemmas setVMRoot_typ_ats [wp] = typ_at_lifts [OF setVMRoot_typ_at']

(* FIXME: move to Lib *)
lemma get_mapM_x_lower:
  fixes P :: "'a option \<Rightarrow> 's \<Rightarrow> bool"
  fixes f :: "('s,'a) nondet_monad"
  fixes g :: "'a \<Rightarrow> 'b \<Rightarrow> ('s,'c) nondet_monad"
  \<comment> \<open>@{term g} preserves the state that @{term f} cares about\<close>
  assumes g: "\<And>x y. \<lbrace> P (Some x) \<rbrace> g x y \<lbrace> \<lambda>_. P (Some x) \<rbrace>"
  \<comment> \<open>@{term P} specifies whether @{term f} either fails or returns a deterministic result\<close>
  assumes f: "\<And>opt_x s. P opt_x s \<Longrightarrow> f s = case_option ({},True) (\<lambda>x. ({(x,s)},False)) opt_x"
  \<comment> \<open>Every state determines P, and therefore the behaviour of @{term f}\<close>
  assumes x: "\<And>s. \<exists> opt_x. P opt_x s"
  \<comment> \<open>If @{term f} may fail, ensure there is at least one @{term f}\<close>
  assumes y: "\<exists>s. P None s \<Longrightarrow> ys \<noteq> []"
  shows "do x \<leftarrow> f; mapM_x (g x) ys od = mapM_x (\<lambda>y. do x \<leftarrow> f; g x y od) ys"
  proof -
    have f_rv: "\<lbrace>\<top>\<rbrace> f \<lbrace>\<lambda>r. P (Some r)\<rbrace>"
      using x f
      apply (clarsimp simp: valid_def)
      apply (drule_tac x=s in meta_spec; clarsimp)
      apply (case_tac opt_x; simp)
      done
    { fix y and h :: "'a \<Rightarrow> ('s,'d) nondet_monad"
      have "do x \<leftarrow> f; _ \<leftarrow> g x y; h x od
              = do x \<leftarrow> f; _ \<leftarrow> g x y; x \<leftarrow> f; h x od"
        apply (rule ext)
        apply (subst monad_eq_split[where g="do x \<leftarrow> f; g x y; return x od"
                                      and P="\<top>" and Q="\<lambda>r. P (Some r)"
                                      and f="h" and f'="\<lambda>_. f >>= h",
                                    simplified bind_assoc, simplified])
        apply (wpsimp wp: g f_rv simp: f return_def bind_def)+
        done
    } note f_redundant = this
    show ?thesis
    proof (cases "\<exists>s. P None s")
      case True show ?thesis
        apply (cases ys; simp add: True y mapM_x_Cons bind_assoc)
        subgoal for y ys
          apply (thin_tac _)
          apply (induct ys arbitrary: y; simp add: mapM_x_Nil mapM_x_Cons bind_assoc)
          apply (subst f_redundant; simp)
          done
        done
    next
      case False
      show ?thesis using False
        apply (induct ys; simp add: mapM_x_Nil mapM_x_Cons bind_assoc)
         apply (rule ext)
         subgoal for s
           by (insert x[of s]; drule spec[of _ s]; clarsimp; case_tac opt_x;
               clarsimp simp: bind_def return_def f)
        apply (subst f_redundant; simp)
        done
    qed
  qed

lemma get_pt_mapM_x_lower:
  assumes g: "\<And>P pt x. \<lbrace> \<lambda>s. P (kheap s pt_ptr) \<rbrace> g pt x \<lbrace> \<lambda>_ s. P (kheap s pt_ptr) \<rbrace>"
  assumes y: "ys \<noteq> []"
  notes [simp] = gets_map_def get_object_def gets_def get_def bind_def return_def
                 assert_opt_def fail_def opt_map_def
  shows "do pt \<leftarrow> get_pt pt_ptr; mapM_x (g pt) ys od
          = mapM_x (\<lambda>y. get_pt pt_ptr >>= (\<lambda>pt. g pt y)) ys"
  apply (rule get_mapM_x_lower
                [where P="\<lambda>opt_pt s. case kheap s pt_ptr of
                                       Some (ArchObj (PageTable pt)) \<Rightarrow> opt_pt = Some pt
                                     | _ \<Rightarrow> opt_pt = None",
                 OF _ _ _ y])
    apply (wp g)
   apply (case_tac "kheap s pt_ptr"; simp; rename_tac ko; case_tac ko; simp;
          rename_tac ako; case_tac ako; simp)+
  done

lemma get_pte_corres'':
  assumes "p' = p"
  shows "corres pte_relation' (pte_at p and pspace_aligned and pspace_distinct) \<top>
                              (get_pte p) (getObject p')"
  using assms get_pte_corres by simp

(* FIXME: move to Lib *)
lemma zip_map_rel:
  assumes "(x,y) \<in> set (zip xs ys)" "map f xs = map g ys"
  shows "f x = g y"
  using assms by (induct xs arbitrary: x y ys; cases ys) auto

(* FIXME RISCV
crunch aligned'[wp]: unmapPageTable "pspace_aligned'"
  (ignore: getObject simp: crunch_simps
       wp: crunch_wps getObject_inv loadObject_default_inv)
crunch distinct'[wp]: unmapPageTable "pspace_distinct'"
  (ignore: getObject simp: crunch_simps
       wp: crunch_wps getObject_inv loadObject_default_inv)
*)

crunch no_0_obj'[wp]: storePTE no_0_obj'

crunch valid_arch'[wp]: storePTE valid_arch_state'
(ignore: setObject)

crunch cur_tcb'[wp]: storePTE cur_tcb'
(ignore: setObject)

(* FIXME RISCV
crunch inv[wp]: lookupPTSlot "P"
  (wp: loadObject_default_inv)
*)

lemma unmap_page_table_corres:
  assumes "asid' = ucast asid" "vptr' = vptr" "pt' = pt"
  notes liftE_get_pte_corres = get_pte_corres[THEN corres_liftE_rel_sum[THEN iffD2]]
  shows "corres dc
          (invs and pt_at pt and K (0 < asid \<and> vptr \<in> user_region))
          no_0_obj'
          (unmap_page_table asid vptr pt)
          (unmapPageTable asid' vptr' pt')"
  (* FIXME RISCV: had before (valid_arch_state' and pspace_aligned' and pspace_distinct'
                               and no_0_obj' and cur_tcb' and valid_objs') *)
  sorry (*
  apply (clarsimp simp: assms unmap_page_table_def unmapPageTable_def ignoreFailure_def const_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_catch[where E="\<top>\<top>" and E'="\<top>\<top>"], simp)
      apply (rule corres_split_eqrE[OF _ find_vspace_for_asid_corres[OF refl]])
        apply (rule corres_split_eqrE[OF _ lookup_pd_slot_corres])
          apply (rule corres_splitEE[OF _ liftE_get_pde_corres])
            apply (rule corres_splitEE[where r'=dc])
               prefer 2
               apply (case_tac "\<exists>addr x xa. pde = RISCV64_A.PageTablePDE addr x xa";
                      fastforce intro!: corres_returnOkTT
                                simp: lookup_failure_map_def pde_relation_def
                                split: RISCV64_A.pde.splits)
              apply simp
              apply (rule corres_split[OF _ flush_table_corres[OF refl refl refl refl]])
                apply (rule corres_split[OF _ store_pde_corres'])
                   apply (rule invalidatePageStructureCacheASID_corres)
                  apply simp
                 apply ((wpsimp wp: hoare_if get_pde_wp getPDE_wp)+)[8]
         apply ((wpsimp wp: lookup_pd_slot_wp hoare_vcg_all_lift_R | wp_once hoare_drop_imps)+)[2]
       apply ((wp find_vspace_for_asid_wp)+)[4]
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def valid_arch_caps_def
                         word_neq_0_conv[symmetric])
   apply (frule (3) find_vspace_for_asid_eq_helper; fastforce simp: vspace_at_asid_def)
  apply simp
  done *)

(* FIXME RISCV
crunch aligned' [wp]: unmapPage pspace_aligned'
  (wp: crunch_wps simp: crunch_simps ignore: getObject)

crunch distinct' [wp]: unmapPage pspace_distinct'
  (wp: crunch_wps simp: crunch_simps ignore: getObject)
*)

lemma corres_split_strengthen_ftE:
  "\<lbrakk> corres (ftr \<oplus> r') P P' f j;
      \<And>rv rv'. r' rv rv' \<Longrightarrow> corres (ftr' \<oplus> r) (R rv) (R' rv') (g rv) (k rv');
      \<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace>,-; \<lbrace>Q'\<rbrace> j \<lbrace>R'\<rbrace>,- \<rbrakk>
    \<Longrightarrow> corres (dc \<oplus> r) (P and Q) (P' and Q') (f >>=E (\<lambda>rv. g rv)) (j >>=E (\<lambda>rv'. k rv'))"
  apply (rule_tac r'=r' in corres_splitEE)
     apply (rule corres_rel_imp, assumption)
     apply (case_tac x, auto)[1]
    apply (erule corres_rel_imp)
    apply (case_tac x, auto)[1]
   apply (simp add: validE_R_def)+
  done

thm unmap_page_def

lemma check_mapping_corres:
  "pte_relation' pte pte' \<Longrightarrow> corres (dc \<oplus> dc) \<top> \<top>
      (unlessE (is_PagePTE pte \<and> pptr_from_pte pte = pptr) $ throwError ExceptionTypes_A.InvalidRoot)
      (checkMappingPPtr pptr pte')"
  apply (simp add: liftE_bindE checkMappingPPtr_def)
  sorry (* FIXME RISCV
  apply (cases m, simp_all add: liftE_bindE)
    apply (clarsimp simp: page_entry_map_def)
    apply (case_tac x1; auto simp: unlessE_def corres_returnOk)
   apply (clarsimp simp: page_entry_map_def)
   apply (case_tac x2; auto simp: unlessE_def corres_returnOk)
  apply (clarsimp simp: page_entry_map_def)
  apply (case_tac x3; auto simp: unlessE_def corres_returnOk)
  done *)

crunch inv[wp]: checkMappingPPtr "P"
  (wp: crunch_wps loadObject_default_inv simp: crunch_simps)

lemmas liftE_get_pte_corres = get_pte_corres[THEN corres_liftE_rel_sum[THEN iffD2]]

lemma unmap_page_corres:
  assumes "sz' = sz" "asid' = ucast asid" "vptr' = vptr" "pptr' = pptr"
  shows "corres dc (invs and K (valid_unmap sz (asid,vptr) \<and> vptr \<in> user_region))
                   (no_0_obj')
                   (unmap_page sz asid vptr pptr)
                   (unmapPage sz' asid' vptr' pptr')"
  (* FIXME RISCV: was (valid_objs' and valid_arch_state' and pspace_aligned' and
                     pspace_distinct' and no_0_obj' and cur_tcb') *)
  sorry (* FIXME RISCV
  apply (clarsimp simp: assms unmap_page_def unmapPage_def ignoreFailure_def const_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_catch[where E="\<top>\<top>" and E'="\<top>\<top>"], simp)
      apply (rule corres_split_strengthen_ftE[where ftr'=dc])
         apply (rule find_vspace_for_asid_corres[OF refl])
        apply (rule corres_splitEE)
           apply (clarsimp simp: ucast_id)
           apply (rule corres_machine_op, rule corres_Id, rule refl, simp)
           apply (rule no_fail_invalidateTranslationSingleASID)
          apply (rule_tac F = "vptr < pptr_base" in corres_gen_asm)
          apply (rule_tac P="\<exists>\<rhd> vspace and page_map_l4_at vspace and vspace_at_asid asid vspace
                             and (\<exists>\<rhd> vspace)
                             and valid_arch_state and valid_vspace_objs
                             and equal_kernel_mappings
                             and pspace_aligned and valid_global_objs and valid_etcbs and
                             K (valid_unmap sz (asid,vptr) \<and> canonical_address vptr )" and
                          P'="pspace_aligned' and pspace_distinct'" in corres_inst)
          apply clarsimp
          apply (rename_tac vspace)
          apply (cases sz, simp_all)[1]
             apply (rule corres_guard_imp)
               apply (rule_tac F = "vptr < pptr_base" in corres_gen_asm)
               apply (rule corres_split_strengthen_ftE[OF lookup_pt_slot_corres])
                 apply simp
                 apply (rule corres_splitEE[OF _ liftE_get_pte_corres])
                   apply simp
                   apply (rule corres_split_norE[OF _ check_mapping_corres, where r=dc, simplified])
                   apply simp
                   apply (rule store_pte_corres')
                   apply (((wpsimp  wp: hoare_vcg_all_lift_R get_pte_wp getPTE_wp lookup_pt_slot_wp
                                  simp: page_entry_map_def unlessE_def is_aligned_pml4 if_apply_def2
                             split_del: if_split
                              simp_del: dc_simp)+
                           | wp_once hoare_drop_imps)+)[10]
         apply (rule corres_guard_imp)
           apply (rule corres_split_strengthen_ftE[OF lookup_pd_slot_corres])
             apply (simp del: dc_simp)
             apply (rule corres_splitEE[OF _ liftE_get_pde_corres])
               apply (rule corres_split_norE[OF _ check_mapping_corres, where r=dc, simplified])
                  apply simp
                  apply (rule store_pde_corres')
                  apply (((wpsimp  wp: hoare_vcg_all_lift_R get_pde_wp getPDE_wp lookup_pd_slot_wp
                                 simp: page_entry_map_def unlessE_def is_aligned_pml4 if_apply_def2
                            split_del: if_split
                             simp_del: dc_simp)+
                         | wp_once hoare_drop_imps)+)[10]
        apply (rule corres_guard_imp)
          apply (rule corres_split_strengthen_ftE[OF lookup_pdpt_slot_corres])
            apply (simp del: dc_simp)
            apply (rule corres_splitEE[OF _ liftE_get_pdpte_corres])
              apply (rule corres_split_norE[OF _ check_mapping_corres, where r=dc, simplified])
                 apply simp
                 apply (rule store_pdpte_corres')
                 apply (((wpsimp  wp: hoare_vcg_all_lift_R get_pdpte_wp getPDPTE_wp
                                      lookup_pdpt_slot_wp
                                simp: page_entry_map_def unlessE_def is_aligned_pml4 if_apply_def2
                           split_del: if_split
                            simp_del: dc_simp)+
                         | wp_once hoare_drop_imps)+)
   apply (rule conjI[OF disjI1], clarsimp)
   apply (clarsimp simp: invs_vspace_objs invs_psp_aligned valid_unmap_def invs_arch_state
                         invs_equal_kernel_mappings)
  apply (clarsimp)
  done *)

definition
  "mapping_map \<equiv> \<lambda>(pte, r) (pte', r'). pte_relation' pte pte' \<and> r' = r"

definition
  "page_invocation_map pgi pgi' \<equiv> case pgi of
    RISCV64_A.PageMap c slot m \<Rightarrow>
      \<exists>c' m'. pgi' = PageMap c' (cte_map slot) m' \<and>
              cap_relation (Structures_A.ArchObjectCap c) c' \<and>
              mapping_map m m'
  | RISCV64_A.PageRemap m \<Rightarrow>
      \<exists>m'. pgi' = PageRemap m' \<and> mapping_map m m'
  | RISCV64_A.PageUnmap c ptr \<Rightarrow>
      \<exists>c'. pgi' = PageUnmap c' (cte_map ptr) \<and>
      acap_relation c c'
  | RISCV64_A.PageGetAddr ptr \<Rightarrow>
      pgi' = PageGetAddr ptr"

definition
  "valid_page_inv' pgi \<equiv> \<lambda>s. True"
(* FIXME RISCV: let's see how far we get with assertions
  case pgi of
    PageMap cap ptr m vs \<Rightarrow>
      cte_wp_at' (is_arch_update' cap) ptr and valid_slots' m and valid_cap' cap
      and K (page_entry_map_corres m)
  | PageRemap m asid vs \<Rightarrow> valid_slots' m and K (page_entry_map_corres m)
  | PageUnmap cap ptr \<Rightarrow>
      \<lambda>s. \<exists>r mt R sz d m. cap = PageCap r R mt sz d m \<and>
          cte_wp_at' (is_arch_update' (ArchObjectCap cap)) ptr s \<and>
          s \<turnstile>' (ArchObjectCap cap)
  | PageGetAddr ptr \<Rightarrow> \<top>" *)

(* FIXME RISCV:
crunch ctes [wp]: unmapPage "\<lambda>s. P (ctes_of s)"
  (wp: crunch_wps simp: crunch_simps ignore: getObject)
*)

(*
lemma updateCap_valid_slots'[wp]: FIXME RISCV
  "\<lbrace>valid_slots' x2\<rbrace> updateCap cte cte' \<lbrace>\<lambda>_ s. valid_slots' x2 s \<rbrace>"
  apply (case_tac x2, case_tac a)
    by (wpsimp simp: valid_slots'_def wp: hoare_vcg_ball_lift)+
*)

lemma message_info_to_data_eqv:
  "wordFromMessageInfo (message_info_map mi) = message_info_to_data mi"
  apply (cases mi)
  apply (simp add: wordFromMessageInfo_def msgLengthBits_def msgExtraCapBits_def msgMaxExtraCaps_def shiftL_nat)
  done

lemma message_info_from_data_eqv:
  "message_info_map (data_to_message_info rv) = messageInfoFromWord rv"
  using shiftr_mask_eq[where 'a=64 and n=12]
  by (auto simp: data_to_message_info_def messageInfoFromWord_def Let_def not_less
                 msgLengthBits_def msgExtraCapBits_def msgMaxExtraCaps_def mask_def
                 shiftL_nat msgMaxLength_def msgLabelBits_def)

lemma set_mi_corres:
 "mi' = message_info_map mi \<Longrightarrow>
  corres dc (tcb_at t and pspace_aligned and pspace_distinct) \<top>
            (set_message_info t mi) (setMessageInfo t mi')"
  sorry (* FIXME RISCV: derive tcb_at'
  apply (simp add: setMessageInfo_def set_message_info_def)
  apply (subgoal_tac "wordFromMessageInfo (message_info_map mi) =
                      message_info_to_data mi")
   apply (simp add: user_setreg_corres msg_info_register_def
                    msgInfoRegister_def)
  apply (simp add: message_info_to_data_eqv)
  done *)


lemma set_mi_invs'[wp]: "\<lbrace>invs' and tcb_at' t\<rbrace> setMessageInfo t a \<lbrace>\<lambda>x. invs'\<rbrace>"
  by (simp add: setMessageInfo_def) wp

lemma set_mi_tcb' [wp]:
  "\<lbrace> tcb_at' t \<rbrace> setMessageInfo receiver msg \<lbrace>\<lambda>rv. tcb_at' t\<rbrace>"
  by (simp add: setMessageInfo_def) wp


lemma setMRs_typ_at':
  "\<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> setMRs receiver recv_buf mrs \<lbrace>\<lambda>rv s. P (typ_at' T p s)\<rbrace>"
  by (simp add: setMRs_def zipWithM_x_mapM split_def, wp crunch_wps)

lemmas setMRs_typ_at_lifts[wp] = typ_at_lifts [OF setMRs_typ_at']

lemma set_mrs_invs'[wp]:
  "\<lbrace> invs' and tcb_at' receiver \<rbrace> setMRs receiver recv_buf mrs \<lbrace>\<lambda>rv. invs' \<rbrace>"
  apply (simp add: setMRs_def)
  apply (wp dmo_invs' no_irq_mapM no_irq_storeWord crunch_wps|
         simp add: zipWithM_x_mapM split_def)+
  done

lemma perform_page_corres:
  assumes "page_invocation_map pgi pgi'"
  notes mapping_map_simps = mapping_map_def
  shows "corres dc (invs and valid_page_inv pgi) \<top>
                   (perform_page_invocation pgi) (performPageInvocation pgi')"
(* FIXME RISCV: was (invs' and valid_page_inv' pgi') *)
sorry (* FIXME RISCV
proof -
  have pull_out_P:
    "\<And>P s Q c p. P s \<and> (\<forall>c. caps_of_state s p = Some c \<longrightarrow> Q s c) \<longrightarrow> (\<forall>c. caps_of_state s p = Some c \<longrightarrow> P s \<and> Q s c)"
   by blast
  show ?thesis
  using assms
  apply (cases pgi)
       apply (rename_tac cap prod entry vspace)
       apply (clarsimp simp: perform_page_invocation_def performPageInvocation_def
                             page_invocation_map_def)
       apply (rule corres_guard_imp)
         apply (rule_tac R="\<lambda>_. invs and (valid_page_map_inv cap (a,b) (aa,ba) vspace) and valid_etcbs and (\<lambda>s. caps_of_state s (a,b) = Some cap)"
           and R'="\<lambda>_. invs' and valid_slots' (ab,bb) and pspace_aligned'
           and pspace_distinct' and K (page_entry_map_corres (ab,bb))" in corres_split)
            prefer 2
            apply (erule updateCap_same_master)
           apply (simp, rule corres_gen_asm2)
           apply (case_tac aa)
             apply clarsimp
             apply (frule (1) mapping_map_pte, clarsimp)
             apply (clarsimp simp: mapping_map_simps valid_slots'_def valid_slots_def valid_page_inv_def neq_Nil_conv valid_page_map_inv_def)
            apply (rule corres_name_pre)
           apply (clarsimp simp:mapM_Cons bind_assoc split del: if_split)
           apply (rule corres_guard_imp)
             apply (rule corres_split[OF _ store_pte_corres'])
                apply (rule corres_split[where r'="(=)"])
                   apply simp
                   apply (rule invalidatePageStructureCacheASID_corres)
                  apply (case_tac cap; clarsimp simp add: is_pg_cap_def)
                  apply (case_tac m; clarsimp)
                  apply (rule corres_fail[where P=\<top> and P'=\<top>])
                  apply (simp add: same_refs_def)
                 apply (wpsimp simp: invs_psp_aligned)+
          apply (frule (1) mapping_map_pde, clarsimp)
          apply (clarsimp simp: mapping_map_simps valid_slots'_def valid_slots_def valid_page_inv_def neq_Nil_conv valid_page_map_inv_def)
          apply (rule corres_name_pre)
          apply (clarsimp simp:mapM_Cons bind_assoc split del: if_split)
          apply (rule corres_guard_imp)
            apply (rule corres_split[OF _ store_pde_corres'])
               apply (rule corres_split[where r'="(=)"])
                  apply simp
                  apply (rule invalidatePageStructureCacheASID_corres)
                 apply (case_tac cap; clarsimp simp add: is_pg_cap_def)
                 apply (case_tac m; clarsimp)
                 apply (rule corres_fail[where P=\<top> and P'=\<top>])
                 apply (simp add: same_refs_def)
                apply (wpsimp simp: invs_psp_aligned)+
         apply (frule (1) mapping_map_pdpte, clarsimp)
         apply (clarsimp simp: mapping_map_simps valid_slots'_def valid_slots_def valid_page_inv_def neq_Nil_conv valid_page_map_inv_def)
         apply (rule corres_name_pre)
         apply (clarsimp simp:mapM_Cons bind_assoc split del: if_split)
         apply (rule corres_guard_imp)
                apply (rule corres_split[OF _ store_pdpte_corres'])
              apply (rule corres_split[where r'="(=)"])
                 apply simp
                 apply (rule invalidatePageStructureCacheASID_corres)
                apply (case_tac cap; clarsimp simp add: is_pg_cap_def)
                apply (case_tac m; clarsimp)
                apply (rule corres_fail[where P=\<top> and P'=\<top>])
                apply (simp add: same_refs_def)
               apply (wpsimp simp: invs_psp_aligned)+
        apply (wp_trace arch_update_cap_invs_map set_cap_valid_page_map_inv)
       apply (wp arch_update_updateCap_invs)
      apply (clarsimp simp: invs_valid_objs invs_psp_aligned invs_distinct valid_page_inv_def cte_wp_at_caps_of_state is_arch_update_def is_cap_simps)
     apply (simp add: cap_master_cap_def split: cap.splits arch_cap.splits)
     apply (auto simp: cte_wp_at_ctes_of valid_page_inv'_def)[1]
       \<comment> \<open>PageRemap\<close>
      apply (rename_tac asid vspace)
      apply (clarsimp simp: perform_page_invocation_def performPageInvocation_def
      page_invocation_map_def)
    apply (rule corres_name_pre)
    apply (clarsimp simp: mapM_Cons mapM_x_mapM bind_assoc valid_slots_def valid_page_inv_def
                          neq_Nil_conv valid_page_inv'_def split del: if_split)
    apply (case_tac a; simp)
      apply (frule (1) mapping_map_pte, clarsimp)
      apply (clarsimp simp: mapping_map_simps)
      apply (rule corres_guard_imp)
        apply (rule corres_split[OF _ store_pte_corres'])
           apply (rule invalidatePageStructureCacheASID_corres)
          apply (wpsimp simp: invs_pspace_aligned')+
     apply (frule (1) mapping_map_pde, clarsimp)
     apply (clarsimp simp: mapping_map_simps)
     apply (rule corres_guard_imp)
       apply (rule corres_split[OF _ store_pde_corres'])
          apply (rule invalidatePageStructureCacheASID_corres)
         apply (wpsimp simp: invs_pspace_aligned')+
    apply (frule (1) mapping_map_pdpte, clarsimp)
    apply (clarsimp simp: mapping_map_simps)
    apply (rule corres_guard_imp)
      apply (rule corres_split[OF _ store_pdpte_corres'])
         apply (rule invalidatePageStructureCacheASID_corres)
        apply (wpsimp simp: invs_pspace_aligned')+
     \<comment> \<open>PageUnmap\<close>
   apply (clarsimp simp: performPageInvocation_def perform_page_invocation_def
                         page_invocation_map_def)
   apply (rule corres_assume_pre)
   apply (clarsimp simp: valid_page_inv_def valid_page_inv'_def isCap_simps is_page_cap_def cong: option.case_cong prod.case_cong)
   apply (case_tac m)
    apply (simp add: split_def)+
    apply (case_tac maptyp; simp)
     apply (rule corres_fail, clarsimp simp: valid_cap_def)
   apply (simp add: perform_page_invocation_unmap_def performPageInvocationUnmap_def split_def)
    apply (rule corres_guard_imp)
     apply (rule corres_split)
        prefer 2
        apply (rule unmap_page_corres[OF refl refl refl refl])
       apply (rule corres_split [where r'=acap_relation])
          prefer 2
          apply simp
          apply (rule corres_rel_imp)
           apply (rule get_cap_corres_all_rights_P[where P=is_arch_cap], rule refl)
          apply (clarsimp simp: is_cap_simps)
         apply (rule_tac F="is_page_cap cap" in corres_gen_asm)
         apply (rule updateCap_same_master)
         apply (clarsimp simp: is_page_cap_def update_map_data_def)
        apply (wp get_cap_wp getSlotCap_wp)+
      apply (simp add: cte_wp_at_caps_of_state)
      apply (strengthen pull_out_P)+
      apply wp
     apply (simp add: cte_wp_at_ctes_of)
     apply wp
    apply (clarsimp simp: valid_unmap_def cte_wp_at_caps_of_state)
    apply (clarsimp simp: is_arch_diminished_def is_cap_simps split: cap.splits arch_cap.splits)
    apply (drule (2) diminished_is_update')+
    apply (clarsimp simp: cap_rights_update_def is_page_cap_def cap_master_cap_simps update_map_data_def acap_rights_update_def)
    apply (clarsimp simp add: wellformed_mapdata_def valid_cap_def mask_def)
    apply auto[1]
   apply (auto simp: cte_wp_at_ctes_of)[1]
    \<comment> \<open>PageGetAddr\<close>
  apply (clarsimp simp: perform_page_invocation_def performPageInvocation_def page_invocation_map_def fromPAddr_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF _ gct_corres])
      apply simp
      apply (rule corres_split[OF set_mi_corres set_mrs_corres])
         apply (simp add: message_info_map_def)
        apply clarsimp
       apply (wp)+
   apply (clarsimp simp: tcb_at_invs)
  apply (clarsimp simp: tcb_at_invs')
  done
qed *)

definition
  "page_table_invocation_map pti pti' \<equiv> True"
(* FIXME RISCV: use assertions?
case pti of
     RISCV64_A.PageTableMap cap ptr pde pd_slot vspace \<Rightarrow>
    \<exists>cap' pde'. pti' = PageTableMap cap' (cte_map ptr) pde' pd_slot vspace \<and>
                cap_relation cap cap' \<and>
                pde_relation' pde pde'
   | RISCV64_A.PageTableUnmap cap ptr \<Rightarrow>
    \<exists>cap'. pti' = PageTableUnmap cap' (cte_map ptr) \<and>
           cap_relation cap (ArchObjectCap cap')"
*)

definition
  "valid_pti' pti \<equiv> \<top>" (* FIXME RISCV: use assertions?
   case pti of
     PageTableMap cap slot pde pdeSlot vspace \<Rightarrow>
     cte_wp_at' (is_arch_update' cap) slot and
     valid_cap' cap and
     valid_pde' pde and K (case cap of ArchObjectCap (PageTableCap _ (Some (asid, vs))) \<Rightarrow> True | _ \<Rightarrow> False)
   | PageTableUnmap cap slot \<Rightarrow> cte_wp_at' (is_arch_update' (ArchObjectCap cap)) slot
                                 and valid_cap' (ArchObjectCap cap)
                                 and K (isPageTableCap cap)"
*)

lemma clear_page_table_corres:
  "corres dc (pspace_aligned and pspace_distinct and pt_at p)
             \<top>
    (mapM_x (swp store_pte RISCV64_A.InvalidPTE)
       [p , p + 8 .e. p + 2 ^ ptBits - 1])
    (mapM_x (swp storePTE RISCV64_H.InvalidPTE)
       [p , p + 8 .e. p + 2 ^ ptBits - 1])"
  apply (rule_tac F="is_aligned p ptBits" in corres_req)
   apply (clarsimp simp: obj_at_def a_type_def)
   apply (clarsimp split: Structures_A.kernel_object.split_asm if_split_asm
                          arch_kernel_obj.split_asm)
   apply (drule(1) pspace_alignedD)
   apply (simp add: bit_simps)
  apply (simp add: upto_enum_step_subtract[where x=p and y="p + 8"]
                   is_aligned_no_overflow bit_simps
                   upto_enum_step_red[where us=3, simplified]
                   mapM_x_mapM liftM_def[symmetric])
  apply (rule corres_guard_imp,
         rule_tac r'=dc and S="(=)"
               and Q="\<lambda>xs s. \<forall>x \<in> set xs. pte_at x s \<and> pspace_aligned s \<and> pspace_distinct s"
               and Q'="\<lambda>_. \<top>"
                in corres_mapM_list_all2, simp_all)
      apply (rule corres_guard_imp, rule store_pte_corres)
        apply (simp add:pte_relation_def)+
     apply (wp hoare_vcg_const_Ball_lift | simp)+
   apply (simp add: list_all2_refl)
  apply (clarsimp simp: upto_enum_step_def)
  apply (erule page_table_pte_atI[simplified shiftl_t2n mult.commute bit_simps, simplified])
   apply (simp add: bit_simps word_less_nat_alt word_le_nat_alt unat_of_nat)
  apply simp
  done

(* FIXME RISCV:
crunch typ_at'[wp]: unmapPageTable "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps hoare_vcg_all_lift_R ignore: getObject)

lemmas unmapPageTable_typ_ats[wp] = typ_at_lifts[OF unmapPageTable_typ_at']
*)


lemma perform_page_table_corres:
  "page_table_invocation_map pti pti' \<Longrightarrow>
   corres dc
          (invs and valid_pti pti) \<top>
          (perform_page_table_invocation pti)
          (performPageTableInvocation pti')"
  (is "?mp \<Longrightarrow> corres dc ?P ?P' ?f ?g")
  (* FIXME RISCV: was (invs' and valid_pti' pti') *)
  sorry (* FIXME RISCV
  apply (simp add: perform_page_table_invocation_def performPageTableInvocation_def)
  apply (cases pti)
   apply (rename_tac cap slot pde pd_slot vspace)
   apply (clarsimp simp: page_table_invocation_map_def)
   apply (rule corres_name_pre)
   apply (clarsimp simp: valid_pti_def valid_pti'_def split: capability.split_asm arch_capability.split_asm)
   apply (rule corres_guard_imp)
     apply (rule corres_split [OF _ updateCap_same_master])
        prefer 2
        apply assumption
       apply (rule corres_split [OF _ store_pde_corres'])
          apply (rule corres_split[where r'="(=)" and P="\<top>" and P'="\<top>"])
             apply simp
             apply (rule invalidatePageStructureCacheASID_corres)
            apply (case_tac cap; clarsimp simp add: is_pt_cap_def)
            apply (case_tac asid; clarsimp)
           apply (wpsimp wp: set_cap_typ_at)+
    apply (clarsimp simp: invs_valid_objs invs_psp_aligned invs_distinct is_arch_update_def
                          cte_wp_at_caps_of_state )
    apply (clarsimp simp: is_cap_simps cap_master_cap_simps
                   dest!: cap_master_cap_eqDs)
   apply (clarsimp simp: cte_wp_at_ctes_of valid_pti'_def)
   apply auto[1]
  apply (clarsimp simp: split:RISCV64_H.pde.split)
  apply (rename_tac cap a b)
  apply (clarsimp simp: page_table_invocation_map_def)
  apply (rule_tac F="is_pt_cap cap" in corres_req)
   apply (clarsimp simp: valid_pti_def)
  apply (clarsimp simp: is_pt_cap_def split_def
                        bit_simps objBits_simps archObjSize_def
                  cong: option.case_cong)
  apply (simp add: case_option_If2 getSlotCap_def split del: if_split)
  apply (rule corres_guard_imp)
    apply (rule corres_split_nor)
       apply (simp add: liftM_def)
       apply (rule corres_split [OF _ get_cap_corres])
         apply (rule_tac F="is_pt_cap x" in corres_gen_asm)
         apply (rule updateCap_same_master)
         apply (clarsimp simp: is_pt_cap_def update_map_data_def)
        apply (wp get_cap_wp)+
      apply (rule corres_if[OF refl])
       apply (rule corres_split [OF _ unmap_page_table_corres[OF refl refl refl]])
         apply (rule clear_page_table_corres[simplified bit_simps bitSimps, simplified])
        apply wp+
      apply (rule corres_trivial, simp)
     apply (simp add: cte_wp_at_caps_of_state pred_conj_def
           split del: if_split)
     apply (rule hoare_lift_Pf2[where f=caps_of_state])
      apply ((wp hoare_vcg_all_lift hoare_vcg_const_imp_lift
                mapM_x_wp' | simp split del: if_split)+)
   apply (clarsimp simp: valid_pti_def cte_wp_at_caps_of_state
                         is_arch_diminished_def
                         cap_master_cap_simps
                         update_map_data_def is_cap_simps
                         cap_rights_update_def acap_rights_update_def
                  dest!: cap_master_cap_eqDs)
   apply (frule (2) diminished_is_update')
   apply (auto simp: valid_cap_def mask_def cap_master_cap_def
                     cap_rights_update_def acap_rights_update_def
                     wellformed_mapdata_def
              split: option.split_asm)[1]
   apply (auto simp: valid_pti'_def cte_wp_at_ctes_of bit_simps)
  done *)

definition
  "asid_pool_invocation_map ap \<equiv> case ap of
  asid_pool_invocation.Assign asid p slot \<Rightarrow> Assign (ucast asid) p (cte_map slot)"

definition
  "valid_apinv' ap \<equiv> \<top>" (* FIXME RISCV: use assertions?
    case ap of Assign asid p slot \<Rightarrow>
      asid_pool_at' p and cte_wp_at' (isArchCap isPageTableCap o cteCap) slot and K
      (0 < asid \<and> asid_wf asid)" *)

lemma pap_corres:
  assumes "ap' = asid_pool_invocation_map ap"
  shows "corres dc (valid_objs and pspace_aligned and pspace_distinct and valid_apinv ap) \<top>
                   (perform_asid_pool_invocation ap)
                   (performASIDPoolInvocation ap')"
(* FIXME RISCV: was (pspace_aligned' and pspace_distinct' and valid_apinv' ap') *)
sorry (* FIXME RISCV
  proof -
    { fix rv p asid asid'
      assume "rv = cap.ArchObjectCap (arch_cap.PageTableCap p asid)"
      hence "(case rv of cap.ArchObjectCap (arch_cap.PageTableCap p asid)
                 \<Rightarrow> cap.ArchObjectCap (arch_cap.PageTableCap p asid'))
               = cap.ArchObjectCap (arch_cap.PageTableCap p asid')"
      by simp
    } note helper = this
    show ?thesis
      using assms
      apply (clarsimp simp: perform_asid_pool_invocation_def performASIDPoolInvocation_def)
      apply (cases ap, simp add: asid_pool_invocation_map_def)
      apply (rename_tac word1 word2 prod)
      apply (rule corres_guard_imp)
        apply (rule corres_split[OF _ getSlotCap_corres[OF refl] get_cap_wp getSlotCap_wp])
        apply (rule_tac F="\<exists>p asid. rv = Structures_A.ArchObjectCap (RISCV64_A.PageTableCap p asid)"
                 in corres_gen_asm; elim exE)
        apply (simp cong: corres_weak_cong)
        apply (rule subst[OF helper], assumption)
        apply (rule corres_split[OF _ updateCap_same_master])
           unfolding store_asid_pool_entry_def
           apply (rule corres_split[where r'="\<lambda>pool pool'. pool = pool' \<circ> ucast"])
              prefer 2
              apply (simp cong: corres_weak_cong)
              apply (rule corres_rel_imp)
               apply (rule get_asid_pool_corres'[OF refl])
              apply simp
             apply (simp only: return_bind cong: corres_weak_cong)
             apply (rule set_asid_pool_corres')
             apply (rule ext; clarsimp simp: inv_def mask_asid_low_bits_ucast_ucast)
            apply (wp getASID_wp)+
          apply simp
         apply (wpsimp wp: set_cap_typ_at hoare_drop_imps)
        apply (wpsimp wp: hoare_drop_imps)
       by (auto simp: valid_apinv_def cte_wp_at_def is_pml4_cap_def
                      is_cap_simps cap_master_cap_def obj_at_def a_type_simps
                      valid_apinv'_def cte_wp_at'_def)
  qed
*)

crunch obj_at[wp]: setVMRoot "\<lambda>s. P (obj_at' P' t s)"
  (simp: crunch_simps)

crunches doMachineOp
  for arch[wp]: "\<lambda>s. P (ksArchState s)"
  and irq_node'[wp]: "\<lambda>s. P (irq_node' s)"
  and gsMaxObjectSize[wp]: "\<lambda>s. P (gsMaxObjectSize s)"
  and ksInterruptState[wp]: "\<lambda>s. P (ksInterruptState s)"

lemma setVMRoot_invs [wp]:
  "\<lbrace>invs'\<rbrace> setVMRoot p \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: setVMRoot_def getThreadVSpaceRoot_def)
  apply (wp hoare_whenE_wp findVSpaceForASID_vs_at_wp
         | wpcw
         | clarsimp simp: if_apply_def2)+
  sorry (* FIXME RISCV *)

lemma setVMRoot_invs_no_cicd':
  "\<lbrace>invs_no_cicd'\<rbrace> setVMRoot p \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
  apply (simp add: setVMRoot_def getThreadVSpaceRoot_def)
  apply (wp hoare_whenE_wp findVSpaceForASID_vs_at_wp
         | wpcw
         | clarsimp simp: if_apply_def2)+
  sorry (* FIXME RISCV *)

crunch nosch [wp]: setVMRoot "\<lambda>s. P (ksSchedulerAction s)"
  (wp: crunch_wps getObject_inv simp: crunch_simps
       loadObject_default_def ignore: getObject)

crunch it' [wp]: deleteASIDPool "\<lambda>s. P (ksIdleThread s)"
  (simp: crunch_simps loadObject_default_def wp: getObject_inv mapM_wp'
   ignore: getObject)

(* FIXME RISCV:
crunch it' [wp]: lookupPTSlot "\<lambda>s. P (ksIdleThread s)"
  (simp: crunch_simps loadObject_default_def wp: getObject_inv
   ignore: getObject)
*)

crunch it' [wp]: storePTE "\<lambda>s. P (ksIdleThread s)"
  (simp: crunch_simps updateObject_default_def wp: setObject_idle'
   ignore: setObject)

crunch it' [wp]: deleteASID "\<lambda>s. P (ksIdleThread s)"
  (simp: crunch_simps loadObject_default_def updateObject_default_def
   wp: getObject_inv
   ignore: getObject setObject)

(* FIXME RISCV
crunch typ_at' [wp]: performPageTableInvocation "\<lambda>s. P (typ_at' T p s)"
  (ignore: getObject wp: crunch_wps)

crunch typ_at' [wp]: performPageInvocation "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps simp: crunch_simps ignore: getObject)
*)

lemma performASIDPoolInvocation_typ_at' [wp]:
  "\<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> performASIDPoolInvocation api \<lbrace>\<lambda>_ s. P (typ_at' T p s)\<rbrace>"
  by (wpsimp simp: performASIDPoolInvocation_def
               wp: getASID_wp hoare_vcg_imp_lift[where P'=\<bottom>, simplified])

(* FIXME RISCV:
lemmas performPageTableInvocation_typ_ats' [wp] =
  typ_at_lifts [OF performPageTableInvocation_typ_at']

lemmas performPageInvocation_typ_ats' [wp] =
  typ_at_lifts [OF performPageInvocation_typ_at']

lemmas performASIDPoolInvocation_typ_ats' [wp] =
  typ_at_lifts [OF performASIDPoolInvocation_typ_at']
*)

lemma storePTE_pred_tcb_at' [wp]:
  "\<lbrace>pred_tcb_at' proj P t\<rbrace> storePTE p pte \<lbrace>\<lambda>_. pred_tcb_at' proj P t\<rbrace>"
  apply (simp add: storePTE_def pred_tcb_at'_def)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp add: updateObject_default_def in_monad)
  done

lemma dmo_ct[wp]:
  "\<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace> doMachineOp m \<lbrace>\<lambda>rv s. P (ksCurThread s)\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply wp
  apply clarsimp
  done

lemma storePTE_valid_mdb [wp]:
  "\<lbrace>valid_mdb'\<rbrace> storePTE p pte \<lbrace>\<lambda>rv. valid_mdb'\<rbrace>"
  by (simp add: valid_mdb'_def) wp

crunch nosch [wp]: storePTE "\<lambda>s. P (ksSchedulerAction s)"
  (simp: updateObject_default_def)

crunch ksQ [wp]: storePTE "\<lambda>s. P (ksReadyQueues s)"
  (simp: updateObject_default_def ignore: setObject)

lemma storePTE_inQ[wp]:
  "\<lbrace>\<lambda>s. P (obj_at' (inQ d p) t s)\<rbrace> storePTE ptr pte \<lbrace>\<lambda>rv s. P (obj_at' (inQ d p) t s)\<rbrace>"
  apply (simp add: obj_at'_real_def storePTE_def)
  apply (wp setObject_ko_wp_at | simp add: objBits_simps)+
  apply (clarsimp simp: obj_at'_def ko_wp_at'_def)
  done

crunch norqL1[wp]: storePTE "\<lambda>s. P (ksReadyQueuesL1Bitmap s)"
  (simp: updateObject_default_def ignore: setObject)

crunch norqL2[wp]: storePTE "\<lambda>s. P (ksReadyQueuesL2Bitmap s)"
  (simp: updateObject_default_def ignore: setObject)

lemma storePTE_valid_queues' [wp]:
  "\<lbrace>valid_queues'\<rbrace> storePTE p pte \<lbrace>\<lambda>_. valid_queues'\<rbrace>"
  by (wp valid_queues_lift')

lemma storePTE_iflive [wp]:
  "\<lbrace>if_live_then_nonz_cap'\<rbrace> storePTE p pte \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: storePTE_def)
  apply (rule hoare_pre)
   apply (rule setObject_iflive' [where P=\<top>], simp)
      apply (simp add: objBits_simps)
     apply (auto simp: updateObject_default_def in_monad)
  done

lemma setObject_pte_ksInt [wp]:
  "\<lbrace>\<lambda>s. P (ksInterruptState s)\<rbrace> setObject p (pte::pte) \<lbrace>\<lambda>_. \<lambda>s. P (ksInterruptState s)\<rbrace>"
  by (wp setObject_ksInterrupt updateObject_default_inv|simp)+

crunch ksInterruptState [wp]: storePTE "\<lambda>s. P (ksInterruptState s)"
  (ignore: setObject)

lemma storePTE_ifunsafe [wp]:
  "\<lbrace>if_unsafe_then_cap'\<rbrace> storePTE p pte \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  apply (simp add: storePTE_def)
  apply (rule hoare_pre)
   apply (rule setObject_ifunsafe' [where P=\<top>], simp)
     apply (auto simp: updateObject_default_def in_monad)[2]
   apply wp
  apply simp
  done

lemma storePTE_idle [wp]:
  "\<lbrace>valid_idle'\<rbrace> storePTE p pte \<lbrace>\<lambda>rv. valid_idle'\<rbrace>"
  unfolding valid_idle'_def
  by (rule hoare_lift_Pf [where f="ksIdleThread"]; wp)

crunch arch' [wp]: storePTE "\<lambda>s. P (ksArchState s)"
  (ignore: setObject)

crunch cur' [wp]: storePTE "\<lambda>s. P (ksCurThread s)"
  (ignore: setObject)

lemma storePTE_irq_states' [wp]:
  "\<lbrace>valid_irq_states'\<rbrace> storePTE pte p \<lbrace>\<lambda>_. valid_irq_states'\<rbrace>"
  apply (simp add: storePTE_def)
  apply (wpsimp wp: valid_irq_states_lift' dmo_lift' no_irq_storeWord setObject_ksMachine
                    updateObject_default_inv)
  done

lemma storePTE_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> storePTE p pte \<lbrace>\<lambda>_. valid_machine_state'\<rbrace>"
  apply (simp add: storePTE_def valid_machine_state'_def pointerInUserData_def
                   pointerInDeviceData_def)
  apply (wp setObject_typ_at_inv setObject_ksMachine updateObject_default_inv
            hoare_vcg_all_lift hoare_vcg_disj_lift | simp)+
  done

crunch pspace_domain_valid[wp]: storePTE "pspace_domain_valid"

lemma storePTE_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace> storePTE p pte \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  apply (rule ct_not_inQ_lift [OF storePTE_nosch])
  apply (simp add: storePTE_def)
  apply (wp_pre, wps)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp: updateObject_default_def in_monad)+
  done

lemma setObject_pte_cur_domain[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> setObject t (v::pte) \<lbrace>\<lambda>rv s. P (ksCurDomain s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setObject_pte_ksDomSchedule[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace> setObject t (v::pte) \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma storePTE_cur_domain[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> storePTE p pte \<lbrace>\<lambda>rv s. P (ksCurDomain s)\<rbrace>"
  by (simp add: storePTE_def) wp

lemma storePTE_ksDomSchedule[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace> storePTE p pte \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
  by (simp add: storePTE_def) wp

lemma storePTE_tcb_obj_at'[wp]:
  "\<lbrace>obj_at' (P::tcb \<Rightarrow> bool) t\<rbrace> storePTE p pte \<lbrace>\<lambda>_. obj_at' P t\<rbrace>"
  apply (simp add: storePTE_def)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp add: updateObject_default_def in_monad)
  done

lemma storePTE_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t\<rbrace> storePTE p pte \<lbrace>\<lambda>_. tcb_in_cur_domain' t\<rbrace>"
  by (wp tcb_in_cur_domain'_lift)

lemma storePTE_ct_idle_or_in_cur_domain'[wp]:
  "\<lbrace>ct_idle_or_in_cur_domain'\<rbrace> storePTE p pte \<lbrace>\<lambda>_. ct_idle_or_in_cur_domain'\<rbrace>"
  by (wp ct_idle_or_in_cur_domain'_lift hoare_vcg_disj_lift)

lemma setObject_pte_ksDomScheduleIdx [wp]:
  "\<lbrace>\<lambda>s. P (ksDomScheduleIdx s)\<rbrace> setObject p (pte::pte) \<lbrace>\<lambda>_. \<lambda>s. P (ksDomScheduleIdx s)\<rbrace>"
  by (wp updateObject_default_inv|simp add:setObject_def | wpc)+

crunch ksDomScheduleIdx[wp]: storePTE "\<lambda>s. P (ksDomScheduleIdx s)"
  (ignore: getObject setObject)

crunch gsMaxObjectSize[wp]: storePTE "\<lambda>s. P (gsMaxObjectSize s)"
  (ignore: getObject setObject wp: setObject_ksPSpace_only updateObject_default_inv)

crunch gsUntypedZeroRanges[wp]: storePTE "\<lambda>s. P (gsUntypedZeroRanges s)"
  (ignore: getObject setObject wp: setObject_ksPSpace_only updateObject_default_inv)

crunch pspace_canonical'[wp]: storePTE "pspace_canonical'"
  (ignore: getObject setObject)

crunch pspace_in_kernel_mappings'[wp]: storePTE "pspace_in_kernel_mappings'"
  (ignore: getObject setObject)

lemma storePTE_invs[wp]:
  "\<lbrace>invs' and valid_pte' pte\<rbrace>
      storePTE p pte
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
  apply (rule hoare_pre)
   apply (wp sch_act_wf_lift valid_global_refs_lift'
             irqs_masked_lift
             valid_arch_state_lift' valid_irq_node_lift
             cur_tcb_lift valid_irq_handlers_lift''
             untyped_ranges_zero_lift
           | simp add: cteCaps_of_def o_def)+
  sorry (* FIXME RISCV
  apply clarsimp
  done *)

lemma storePTE_valid_queues [wp]:
  "\<lbrace>Invariants_H.valid_queues\<rbrace> storePTE p pte \<lbrace>\<lambda>_. Invariants_H.valid_queues\<rbrace>"
  by (wp valid_queues_lift | simp add: pred_tcb_at'_def)+

lemma storePTE_valid_objs[wp]:
  "storePTE p pte \<lbrace>valid_objs'\<rbrace>"
  apply (simp add: storePTE_def doMachineOp_def split_def)
  apply (rule hoare_pre, rule setObject_valid_objs'[where P=\<top>])
   prefer 2
   apply simp
  apply (clarsimp simp: updateObject_default_def in_monad  valid_obj'_def)
  done

lemma setASIDPool_valid_objs [wp]:
  "setObject p (ap::asidpool) \<lbrace>valid_objs'\<rbrace>"
  apply (wp setObject_valid_objs'[where P=\<top>])
   apply (clarsimp simp: updateObject_default_def in_monad valid_obj'_def)
  apply simp
  done

lemma setASIDPool_valid_mdb [wp]:
  "\<lbrace>valid_mdb'\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv. valid_mdb'\<rbrace>"
  by (simp add: valid_mdb'_def) wp

lemma setASIDPool_nosch [wp]:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  by (wp setObject_nosch updateObject_default_inv|simp)+

lemma setASIDPool_ksQ [wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueues s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv s. P (ksReadyQueues s)\<rbrace>"
  by (wp setObject_qs updateObject_default_inv|simp)+

lemma setASIDPool_inQ[wp]:
  "\<lbrace>\<lambda>s. P (obj_at' (inQ d p) t s)\<rbrace>
     setObject ptr (ap::asidpool)
   \<lbrace>\<lambda>rv s. P (obj_at' (inQ d p) t s)\<rbrace>"
  apply (simp add: obj_at'_real_def)
  apply (wpsimp wp: setObject_ko_wp_at simp: objBits_simps)
    apply (simp add: pageBits_def)
   apply simp
  apply (clarsimp simp: obj_at'_def ko_wp_at'_def)
  done

lemma setASIDPool_qsL1 [wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueuesL1Bitmap s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv s. P (ksReadyQueuesL1Bitmap s)\<rbrace>"
  by (wp setObject_qs updateObject_default_inv|simp)+

lemma setASIDPool_qsL2 [wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueuesL2Bitmap s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv s. P (ksReadyQueuesL2Bitmap s)\<rbrace>"
  by (wp setObject_qs updateObject_default_inv|simp)+

lemma setASIDPool_tcb_obj_at'[wp]:
  "\<lbrace>obj_at' (P::tcb \<Rightarrow> bool) t\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. obj_at' P t\<rbrace>"
  apply (rule obj_at_setObject2)
  apply (clarsimp simp add: updateObject_default_def in_monad)
  done

lemma setASIDPool_valid_queues [wp]:
  "\<lbrace>Invariants_H.valid_queues\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. Invariants_H.valid_queues\<rbrace>"
  by (wp valid_queues_lift | simp add: pred_tcb_at'_def)+

lemma setASIDPool_valid_queues' [wp]:
  "\<lbrace>valid_queues'\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. valid_queues'\<rbrace>"
  by (wp valid_queues_lift')

lemma setASIDPool_state_refs' [wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  apply (clarsimp simp: setObject_def valid_def in_monad split_def
                        updateObject_default_def objBits_simps
                        in_magnitude_check state_refs_of'_def ps_clear_upd'
                 elim!: rsubst[where P=P] intro!: ext
             split del: if_split cong: option.case_cong if_cong)
  apply (simp split: option.split)
  done

lemma setASIDPool_iflive [wp]:
  "\<lbrace>if_live_then_nonz_cap'\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (rule hoare_pre)
   apply (rule setObject_iflive' [where P=\<top>], simp)
      apply (simp add: objBits_simps)
     apply (auto simp: updateObject_default_def in_monad pageBits_def)
  done

lemma setASIDPool_ksInt [wp]:
  "\<lbrace>\<lambda>s. P (ksInterruptState s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. \<lambda>s. P (ksInterruptState s)\<rbrace>"
  by (wp setObject_ksInterrupt updateObject_default_inv|simp)+

lemma setASIDPool_ifunsafe [wp]:
  "\<lbrace>if_unsafe_then_cap'\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  apply (rule hoare_pre)
   apply (rule setObject_ifunsafe' [where P=\<top>], simp)
     apply (auto simp: updateObject_default_def in_monad)[2]
   apply wp
  apply simp
  done

lemma setASIDPool_it' [wp]:
  "\<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. \<lambda>s. P (ksIdleThread s)\<rbrace>"
  by (wp setObject_it updateObject_default_inv|simp)+

lemma setASIDPool_pred_tcb_at' [wp]:
  "\<lbrace>pred_tcb_at' proj P t\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. pred_tcb_at' proj P t\<rbrace>"
  apply (simp add: pred_tcb_at'_def)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp add: updateObject_default_def in_monad)
  done

lemma setASIDPool_idle [wp]:
  "\<lbrace>valid_idle'\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv. valid_idle'\<rbrace>"
  unfolding valid_idle'_def
  by (rule hoare_lift_Pf [where f="ksIdleThread"]; wp)

lemma setASIDPool_irq_states' [wp]:
  "\<lbrace>valid_irq_states'\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. valid_irq_states'\<rbrace>"
  apply (rule hoare_pre)
   apply (rule hoare_use_eq [where f=ksInterruptState, OF setObject_ksInterrupt])
    apply (simp, rule updateObject_default_inv)
   apply (rule hoare_use_eq [where f=ksMachineState, OF setObject_ksMachine])
    apply (simp, rule updateObject_default_inv)
   apply wp
  apply assumption
  done


lemma setASIDPool_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. valid_machine_state'\<rbrace>"
  apply (simp add: valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def)
  apply (wp setObject_typ_at_inv setObject_ksMachine updateObject_default_inv
            hoare_vcg_all_lift hoare_vcg_disj_lift | simp)+
  done

lemma setASIDPool_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  apply (rule ct_not_inQ_lift [OF setObject_nosch])
   apply (simp add: updateObject_default_def | wp)+
  apply (rule hoare_weaken_pre)
   apply (wps setObject_ASID_ct)
  apply (rule obj_at_setObject2)
   apply (clarsimp simp: updateObject_default_def in_monad)+
  done

lemma setObject_asidpool_cur'[wp]:
  "\<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv s. P (ksCurThread s)\<rbrace>"
  apply (simp add: setObject_def)
  apply (wp | wpc | simp add: updateObject_default_def)+
  done

lemma setObject_asidpool_cur_domain[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv s. P (ksCurDomain s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setObject_asidpool_ksDomSchedule[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setObject_tcb_obj_at'[wp]:
  "\<lbrace>obj_at' (P::tcb \<Rightarrow> bool) t\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. obj_at' P t\<rbrace>"
  apply (rule obj_at_setObject2)
  apply (clarsimp simp add: updateObject_default_def in_monad)
  done

lemma setObject_asidpool_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. tcb_in_cur_domain' t\<rbrace>"
  by (wp tcb_in_cur_domain'_lift)

lemma setObject_asidpool_ct_idle_or_in_cur_domain'[wp]:
  "\<lbrace>ct_idle_or_in_cur_domain'\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. ct_idle_or_in_cur_domain'\<rbrace>"
  apply (rule ct_idle_or_in_cur_domain'_lift)
      apply (wp hoare_vcg_disj_lift)+
  done

lemma setObject_ap_ksDomScheduleIdx [wp]:
  "\<lbrace>\<lambda>s. P (ksDomScheduleIdx s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. \<lambda>s. P (ksDomScheduleIdx s)\<rbrace>"
  by (wp updateObject_default_inv|simp add:setObject_def | wpc)+

lemma setASIDPool_invs [wp]:
  "setObject p (ap::asidpool) \<lbrace>invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
  apply (wp sch_act_wf_lift valid_global_refs_lift' irqs_masked_lift
            valid_arch_state_lift' valid_irq_node_lift
            cur_tcb_lift valid_irq_handlers_lift''
            untyped_ranges_zero_lift
            updateObject_default_inv
          | simp add: cteCaps_of_def
          | rule setObject_ksPSpace_only)+
  apply (clarsimp simp:  o_def)
  done

(* FIXME RISCV
crunch cte_wp_at'[wp]: unmapPageTable "\<lambda>s. P (cte_wp_at' P' p s)"
  (wp: crunch_wps simp: crunch_simps ignore: getObject setObject)
*)

lemmas storePTE_Invalid_invs = storePTE_invs[where pte=InvalidPTE, simplified]

(* FIXME RISCV: crunch
crunch invs'[wp]: unmapPageTable "invs'"
  (ignore: getObject setObject doMachineOp
       wp: storePTE_Invalid_invs mapM_wp' crunch_wps
     simp: crunch_simps)
*)

lemma perform_pti_invs [wp]:
  "\<lbrace>invs' and valid_pti' pti\<rbrace> performPageTableInvocation pti \<lbrace>\<lambda>_. invs'\<rbrace>"
  sorry (* FIXME RISCV: will need assertions
  apply (clarsimp simp: performPageTableInvocation_def getSlotCap_def
                 split: page_table_invocation.splits)
  apply (intro conjI allI impI)
   apply (rule hoare_pre)
    apply (wp arch_update_updateCap_invs getCTE_wp
              hoare_vcg_ex_lift  mapM_x_wp'
                | wpc | simp add: o_def
                | (simp only: imp_conv_disj, rule hoare_vcg_disj_lift))+
   apply (clarsimp simp: valid_pti'_def cte_wp_at_ctes_of
                         is_arch_update'_def isCap_simps valid_cap'_def
                         capAligned_def)
  apply (rule hoare_pre)
   apply (wpsimp wp: arch_update_updateCap_invs hoare_vcg_all_lift hoare_vcg_ex_lift
             | wp_once hoare_drop_imps)+
  apply (clarsimp simp: cte_wp_at_ctes_of valid_pti'_def)
  done *)

(* FIXME RISCV: crunch
crunch cte_wp_at': unmapPage "\<lambda>s. P (cte_wp_at' P' p s)"
  (wp: crunch_wps simp: crunch_simps ignore: getObject)

lemmas unmapPage_typ_ats [wp] = typ_at_lifts [OF unmapPage_typ_at']

crunch inv: lookupPTSlot P
  (wp: crunch_wps simp: crunch_simps ignore: getObject)
*)

lemma unmapPage_invs' [wp]:
  "\<lbrace>invs'\<rbrace> unmapPage sz asid vptr pptr \<lbrace>\<lambda>_. invs'\<rbrace>"
  sorry (* FIXME RISCV
  apply (simp add: unmapPage_def)
  apply (rule hoare_pre)
   apply (wp lookupPTSlot_inv
             hoare_vcg_const_imp_lift
         |wpc
         |simp)+
  done *)

lemma perform_page_invs [wp]:
  notes no_irq[wp]
  shows "\<lbrace>invs' and valid_page_inv' pt\<rbrace> performPageInvocation pt \<lbrace>\<lambda>_. invs'\<rbrace>"
  sorry (* FIXME RISCV: likely to need assertions
  apply (simp add: performPageInvocation_def)
  apply (cases pt)
     apply clarsimp
     apply ((wpsimp wp: hoare_vcg_all_lift hoare_vcg_ex_lift hoare_vcg_const_imp_lift
                       arch_update_updateCap_invs unmapPage_cte_wp_at' getSlotCap_wp
                  simp: valid_page_inv'_def valid_slots'_def is_arch_update'_def
                 split: vmpage_entry.splits
             | (auto simp: is_arch_update'_def)[1])+)[3]
  apply (wp arch_update_updateCap_invs unmapPage_cte_wp_at' getSlotCap_wp
         | wpc
         | clarsimp simp: performPageInvocationUnmap_def)+
   apply (rename_tac acap word a b)
   apply (rule_tac Q="\<lambda>_. invs' and cte_wp_at' (\<lambda>cte. \<exists>r R mt sz d m. cteCap cte =
                                       ArchObjectCap (PageCap r R mt sz d m)) word"
               in hoare_strengthen_post)
    apply (wp unmapPage_cte_wp_at')
   apply (clarsimp simp: cte_wp_at_ctes_of)
   apply (case_tac cte)
   apply clarsimp
   apply (frule ctes_of_valid_cap')
    apply (auto simp: valid_page_inv'_def valid_slots'_def cte_wp_at_ctes_of)[1]
   apply (simp add: is_arch_update'_def isCap_simps)
   apply (simp add: valid_cap'_def capAligned_def)
  apply (clarsimp simp: cte_wp_at_ctes_of valid_page_inv'_def)
  apply (simp add: is_arch_update'_def isCap_simps)
  apply (case_tac cte)
  apply clarsimp+
  done *)

lemma setObject_cte_obj_at_ap':
  shows
  "\<lbrace>\<lambda>s. P' (obj_at' (P :: asidpool \<Rightarrow> bool) p s)\<rbrace>
  setObject c (cte::cte)
  \<lbrace>\<lambda>_ s. P' (obj_at' P p s)\<rbrace>"
  apply (clarsimp simp: setObject_def in_monad split_def
                        valid_def lookupAround2_char1
                        obj_at'_def ps_clear_upd'
             split del: if_split)
  apply (clarsimp elim!: rsubst[where P=P'])
  apply (clarsimp simp: updateObject_cte in_monad objBits_simps
                        tcbCTableSlot_def tcbVTableSlot_def
                        typeError_def
                 split: if_split_asm
                        Structures_H.kernel_object.split_asm)
  done

lemma updateCap_ko_at_ap_inv'[wp]:
  "\<lbrace>\<lambda>s. P (ko_at' (ko::asidpool) p s )\<rbrace> updateCap a b \<lbrace>\<lambda>rv s. P ( ko_at' ko p s)\<rbrace>"
  by (wpsimp simp: updateCap_def setCTE_def wp: setObject_cte_obj_at_ap')

lemma perform_aci_invs [wp]:
  "\<lbrace>invs' and valid_apinv' api\<rbrace> performASIDPoolInvocation api \<lbrace>\<lambda>_. invs'\<rbrace>"
  sorry (* FIXME RISCV: likely to need assertions
  apply (clarsimp simp: performASIDPoolInvocation_def split: asidpool_invocation.splits)
  apply (wp arch_update_updateCap_invs getASID_wp getSlotCap_wp hoare_vcg_all_lift
            hoare_vcg_imp_lift
          | simp add: o_def)+
  apply (clarsimp simp: valid_apinv'_def cte_wp_at_ctes_of)
  apply (case_tac cte)
  apply (clarsimp split: if_splits)
  apply (drule ctes_of_valid_cap', fastforce)
  apply (clarsimp simp: isPML4Cap'_def valid_cap'_def capAligned_def is_arch_update'_def isCap_simps)
  apply (drule ko_at_valid_objs', fastforce, clarsimp simp: projectKOs)
  apply (clarsimp simp: valid_obj'_def ran_def mask_asid_low_bits_ucast_ucast
                 split: if_split_asm)
  apply (case_tac x, clarsimp simp: inv_def)
  apply (clarsimp simp: page_map_l4_at'_def, drule_tac x=0 in spec)
  apply (auto simp: bit_simps asid_bits_defs asid_bits_of_defs ucast_ucast_mask mask_def word_and_le1)
  done *)

lemma diminished_valid':
  "diminished' cap cap' \<Longrightarrow> valid_cap' cap = valid_cap' cap'"
  by (rule ext) (clarsimp simp add: diminished'_def)

end

lemma cteCaps_of_ctes_of_lift:
  "(\<And>P. \<lbrace>\<lambda>s. P (ctes_of s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ctes_of s)\<rbrace>) \<Longrightarrow> \<lbrace>\<lambda>s. P (cteCaps_of s) \<rbrace> f \<lbrace>\<lambda>_ s. P (cteCaps_of s)\<rbrace>"
  unfolding cteCaps_of_def .

end
