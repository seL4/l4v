(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory UserOp_IF
imports Syscall_IF "../access-control/ADT_AC"
begin

definition ptable_lift_s where
  "ptable_lift_s s \<equiv>  ptable_lift (cur_thread s) s"

definition ptable_rights_s where
  "ptable_rights_s s \<equiv>  ptable_rights (cur_thread s) s"

definition get_pt_xn :: "(obj_ref \<rightharpoonup> arch_kernel_obj) \<Rightarrow> obj_ref \<Rightarrow> word32 \<rightharpoonup> bool" where
  "get_pt_xn ahp pt_ref vptr \<equiv>
   case get_pt_entry ahp pt_ref vptr of
     Some (ARM_Structs_A.SmallPagePTE base atts _) \<Rightarrow> Some (XNever \<in> atts)
   | Some (ARM_Structs_A.LargePagePTE base atts _) \<Rightarrow> Some (XNever \<in> atts)
   | _ \<Rightarrow> None"

definition  get_page_xn :: "(obj_ref \<rightharpoonup> arch_kernel_obj) \<Rightarrow> obj_ref \<Rightarrow> word32 \<rightharpoonup> bool" where
  "get_page_xn ahp pd_ref vptr \<equiv>
   case get_pd_entry ahp pd_ref vptr of
     Some (ARM_Structs_A.PageTablePDE p _ _) \<Rightarrow>
       get_pt_xn ahp (Platform.ptrFromPAddr p) vptr
   | Some (ARM_Structs_A.SectionPDE base atts _ _) \<Rightarrow> Some (XNever \<in> atts)
   | Some (ARM_Structs_A.SuperSectionPDE base atts _) \<Rightarrow> Some (XNever \<in> atts)
   | _ \<Rightarrow> None"

definition
  ptable_xn :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> word32 \<Rightarrow> bool" where
 "ptable_xn tcb s \<equiv> \<lambda>addr.
  option_case False (\<lambda>x. x)
     (get_page_xn (\<lambda>obj. get_arch_obj (kheap s obj))
        (get_pd_of_thread (kheap s) (arch_state s) tcb) addr)"

definition ptable_xn_s where
  "ptable_xn_s s \<equiv>  ptable_xn (cur_thread s) s"

definition getExMonitor :: "exclusive_monitors machine_monad" where
  "getExMonitor \<equiv> gets exclusive_state"

definition setExMonitor :: "exclusive_monitors \<Rightarrow> unit machine_monad" where
  "setExMonitor es \<equiv> modify (\<lambda>ms. ms\<lparr>exclusive_state := es\<rparr>)"

definition do_user_op_if where
  "do_user_op_if uop tc =
   do pr \<leftarrow> gets ptable_rights_s;
      pxn \<leftarrow> gets ptable_xn_s;
      pl \<leftarrow> gets (\<lambda>s. restrict_map (ptable_lift_s s) {x. pr x \<noteq> {}});
      t \<leftarrow> gets cur_thread;
      um \<leftarrow> gets (\<lambda>s. restrict_map (user_mem s \<circ> ptrFromPAddr)
                             {y. EX x. pl x = Some y \<and> AllowRead \<in> pr x});
      es \<leftarrow> do_machine_op getExMonitor;
      u \<leftarrow> return (uop t pl pr pxn (tc, um, es));
      assert (u \<noteq> {});
      (e,(tc',um',es')) \<leftarrow> select u;
      do_machine_op (user_memory_update
        (restrict_map um' {y. EX x. pl x = Some y \<and> AllowWrite : pr x} \<circ>
         addrFromPPtr));
      do_machine_op (setExMonitor es');
      return (e,tc')
   od"

(* Assumptions:
 * User is deterministic based on an address being mapped with no rights or not mapped at all.
 * We implicitly assume that if you have any rights you must have at least read rights.
*)

lemma dmo_user_memory_update_reads_respects_g:
   "reads_respects_g aag l \<top> (do_machine_op (user_memory_update um))"
   apply(clarsimp simp: equiv_valid_def2 equiv_valid_2_def)
   apply(clarsimp simp: do_machine_op_def user_memory_update_def gets_def select_f_def
                        get_def bind_def in_monad)
   apply(clarsimp simp: reads_equiv_g_def globals_equiv_def split: option.splits)
   apply(subgoal_tac "reads_respects aag l \<top> (do_machine_op (user_memory_update um))")
    apply(fastforce simp: equiv_valid_def2 equiv_valid_2_def in_monad
                    do_machine_op_def user_memory_update_def select_f_def
                    idle_equiv_def)
   apply(rule use_spec_ev)
   apply (simp add: user_memory_update_def)
   apply(rule do_machine_op_spec_reads_respects)
    apply(simp add: equiv_valid_def2)
    apply(rule modify_ev2)
    apply(fastforce intro: equiv_forI elim: equiv_forE split: option.splits)
   apply (wp | simp)+
   done

lemma requiv_get_pd_of_thread_eq:
  "\<lbrakk> reads_equiv aag s s'; pas_refined aag s; is_subject aag (cur_thread s);
     pd_ref \<noteq> arm_global_pd (arch_state s);
     pd_ref' \<noteq> arm_global_pd (arch_state s');
     get_pd_of_thread (kheap s) (arch_state s) (cur_thread s) = pd_ref;
     get_pd_of_thread (kheap s') (arch_state s') (cur_thread s') = pd_ref' \<rbrakk>
   \<Longrightarrow> pd_ref = pd_ref'"
  apply (erule reads_equivE)
  apply (erule equiv_forE)
  apply (subgoal_tac "aag_can_read aag (cur_thread s)")
   apply (clarsimp simp: get_pd_of_thread_eq)
  apply (simp add: reads_lrefl)
  done

lemma requiv_get_pt_entry_eq:
  "\<lbrakk> reads_equiv aag s s'; is_subject aag pt \<rbrakk>
   \<Longrightarrow> get_pt_entry (\<lambda>obj. get_arch_obj (kheap s obj)) pt x
       = get_pt_entry (\<lambda>obj. get_arch_obj (kheap s' obj)) pt x"
  apply (erule reads_equivE)
  apply (erule equiv_forE)
  apply (subgoal_tac "aag_can_read aag pt")
   apply (simp add: get_pt_entry_def split: option.splits)
  apply (simp add: reads_lrefl)
  done

lemma requiv_get_pt_info_eq:
  "\<lbrakk> reads_equiv aag s s'; pas_refined aag s; is_subject aag pt \<rbrakk>
   \<Longrightarrow> get_pt_info (\<lambda>obj. get_arch_obj (kheap s obj)) pt x
       = get_pt_info (\<lambda>obj. get_arch_obj (kheap s' obj)) pt x"
  apply (simp add: get_pt_info_def)
  apply (subst requiv_get_pt_entry_eq, simp+)
  done

lemma requiv_get_pd_entry_eq:
  "\<lbrakk> reads_equiv aag s s'; is_subject aag pd \<rbrakk>
   \<Longrightarrow> get_pd_entry (\<lambda>obj. get_arch_obj (kheap s obj)) pd x
       = get_pd_entry (\<lambda>obj. get_arch_obj (kheap s' obj)) pd x"
  apply (erule reads_equivE)
  apply (erule equiv_forE)
  apply (subgoal_tac "aag_can_read aag pd")
   apply (simp add: get_pd_entry_def split: option.splits)
  apply (simp add: reads_lrefl)
  done

lemma requiv_get_page_info_eq:
  "\<lbrakk> reads_equiv aag s s'; pas_refined aag s; is_subject aag pd;
     x \<notin> kernel_mappings \<rbrakk>
   \<Longrightarrow> get_page_info (\<lambda>obj. get_arch_obj (kheap s obj)) pd x
       = get_page_info (\<lambda>obj. get_arch_obj (kheap s' obj)) pd x"
  apply (simp add: get_page_info_def)
  apply (subst requiv_get_pd_entry_eq[symmetric], simp+)
  apply (clarsimp split: option.splits pde.splits)
  apply (frule pt_in_pd_same_agent, fastforce+)
  apply (rule requiv_get_pt_info_eq, simp+)
  done

lemma requiv_pd_of_thread_global_pd:
  "\<lbrakk> reads_equiv aag s s'; is_subject aag (cur_thread s); invs s; pas_refined aag s;
     get_pd_of_thread (kheap s) (arch_state s) (cur_thread s) = arm_global_pd (arch_state s) \<rbrakk>
   \<Longrightarrow> get_pd_of_thread (kheap s') (arch_state s') (cur_thread s') = arm_global_pd (arch_state s')"
  apply (erule reads_equivE)
  apply (erule equiv_forE)
  apply (subgoal_tac "aag_can_read aag (cur_thread s)")
   prefer 2
   apply (simp add: reads_lrefl)
  apply (clarsimp simp: get_pd_of_thread_def2
                  split: option.splits kernel_object.splits cap.splits arch_cap.splits)
  apply (subgoal_tac "aag_can_read_asid aag aa")
   apply (subgoal_tac "s \<turnstile> ArchObjectCap (PageDirectoryCap word (Some aa))")
    apply (clarsimp simp: equiv_asids_def equiv_asid_def valid_cap_def)
    apply (drule_tac x=aa in spec)
    apply (clarsimp simp: word_gt_0 typ_at_eq_kheap_obj)
    apply (drule invs_valid_global_refs)
    apply (drule_tac ptr="((cur_thread s), tcb_cnode_index 1)" in valid_global_refsD2[rotated])
     apply (subst caps_of_state_tcb_cap_cases)
       apply (simp add: get_tcb_def)
      apply (simp add: dom_tcb_cap_cases[simplified])
     apply simp
    apply (simp add: cap_range_def global_refs_def)

   apply (cut_tac s=s and t="cur_thread s" and tcb=tcb_ext in objs_valid_tcb_vtable)
     apply (fastforce simp: invs_valid_objs get_tcb_def)+
  apply (subgoal_tac "(pasObjectAbs aag (cur_thread s), Control, pasASIDAbs aag aa)
                          \<in> state_asids_to_policy aag s")
   apply (frule pas_refined_Control_into_is_subject_asid)
    apply (fastforce simp: pas_refined_def)
   apply simp
  apply (cut_tac aag=aag and ptr="(cur_thread s, tcb_cnode_index 1)" in sata_asid)
    prefer 3
    apply simp
   apply (subst caps_of_state_tcb_cap_cases)
     apply (simp add: get_tcb_def)
    apply (simp add: dom_tcb_cap_cases[simplified])+
  done

lemma requiv_ptable_rights_eq:
  "\<lbrakk> reads_equiv aag s s'; pas_refined aag s; pas_refined aag s';
     is_subject aag (cur_thread s); invs s; invs s' \<rbrakk>
   \<Longrightarrow> ptable_rights_s s = ptable_rights_s s'"
  apply (simp add: ptable_rights_s_def)
  apply (rule ext)
  apply (case_tac "x \<in> kernel_mappings")
   apply (clarsimp simp: ptable_rights_def split: option.splits)
   apply (intro conjI)
    apply clarsimp
    apply (frule some_get_page_info_kmapsD)
       apply (fastforce simp: invs_valid_global_pd_mappings invs_equal_kernel_mappings
                              vspace_cap_rights_to_auth_def)+
   apply clarsimp
   apply (frule some_get_page_info_kmapsD)
      apply (fastforce simp: invs_valid_global_pd_mappings invs_equal_kernel_mappings
                             vspace_cap_rights_to_auth_def)+
   apply clarsimp
   apply (frule_tac r=ba in some_get_page_info_kmapsD)
      apply (fastforce simp: invs_valid_global_pd_mappings invs_equal_kernel_mappings
                             vspace_cap_rights_to_auth_def)+

  apply (case_tac "get_pd_of_thread (kheap s) (arch_state s) (cur_thread s)
                 = arm_global_pd (arch_state s)")
   apply (frule requiv_pd_of_thread_global_pd)
       apply fastforce+
   apply (clarsimp simp: ptable_rights_def split: option.splits)
   apply (intro conjI)
    apply clarsimp
    apply (frule get_page_info_gpd_kmaps[rotated, rotated])
      apply (fastforce simp: invs_valid_global_objs invs_arch_state)+
   apply clarsimp
   apply (intro conjI)
    apply clarsimp
    apply (frule get_page_info_gpd_kmaps[rotated, rotated])
      apply (fastforce simp: invs_valid_global_objs invs_arch_state)+
   apply clarsimp
   apply (frule get_page_info_gpd_kmaps[rotated, rotated])
     apply (fastforce simp: invs_valid_global_objs invs_arch_state)+

  apply (case_tac "get_pd_of_thread (kheap s') (arch_state s') (cur_thread s')
                 = arm_global_pd (arch_state s')")
  apply (drule reads_equiv_sym)
  apply (frule requiv_pd_of_thread_global_pd)
       apply (fastforce simp: reads_equiv_def)+

  apply (simp add: ptable_rights_def)
  apply (frule requiv_get_pd_of_thread_eq)
        apply fastforce+
  apply (frule pd_of_thread_same_agent, simp+)
  apply (subst requiv_get_page_info_eq, simp+)
  done

lemma requiv_ptable_lift_eq:
  "\<lbrakk> reads_equiv aag s s'; pas_refined aag s; pas_refined aag s'; invs s;
     invs s'; is_subject aag (cur_thread s); ptable_rights_s s x \<noteq> {} \<rbrakk>
   \<Longrightarrow> ptable_lift_s s x = ptable_lift_s s' x"
  apply (simp add: ptable_lift_s_def ptable_rights_s_def)
  apply (case_tac "x \<in> kernel_mappings")
   apply (clarsimp simp: ptable_lift_def split: option.splits)
   apply (intro conjI)
    apply clarsimp
    apply (frule some_get_page_info_kmapsD)
       apply (fastforce simp: invs_valid_global_pd_mappings invs_equal_kernel_mappings
                              vspace_cap_rights_to_auth_def ptable_rights_def)+
   apply clarsimp
   apply (frule some_get_page_info_kmapsD)
      apply (fastforce simp: invs_valid_global_pd_mappings invs_equal_kernel_mappings
                             vspace_cap_rights_to_auth_def ptable_rights_def)+

  apply (case_tac "get_pd_of_thread (kheap s) (arch_state s) (cur_thread s)
                 = arm_global_pd (arch_state s)")
   apply (frule requiv_pd_of_thread_global_pd)
       apply fastforce+
   apply (clarsimp simp: ptable_lift_def split: option.splits)
   apply (intro conjI)
    apply clarsimp
    apply (frule get_page_info_gpd_kmaps[rotated, rotated])
      apply (fastforce simp: invs_valid_global_objs invs_arch_state)+
   apply clarsimp
   apply (intro conjI)
    apply (frule get_page_info_gpd_kmaps[rotated, rotated])
      apply (fastforce simp: invs_valid_global_objs invs_arch_state)+
   apply clarsimp
   apply (frule get_page_info_gpd_kmaps[rotated, rotated])
     apply (fastforce simp: invs_valid_global_objs invs_arch_state)+

  apply (case_tac "get_pd_of_thread (kheap s') (arch_state s') (cur_thread s')
                 = arm_global_pd (arch_state s')")
  apply (drule reads_equiv_sym)
  apply (frule requiv_pd_of_thread_global_pd)
       apply (fastforce simp: reads_equiv_def)+

  apply (simp add: ptable_lift_def)
  apply (frule requiv_get_pd_of_thread_eq, simp+)
  apply (frule pd_of_thread_same_agent, simp+)
  apply (subst requiv_get_page_info_eq, simp+)
  done

lemma requiv_get_pt_xn_eq:
  "\<lbrakk> reads_equiv aag s s'; pas_refined aag s; is_subject aag pt \<rbrakk>
   \<Longrightarrow> get_pt_xn (\<lambda>obj. get_arch_obj (kheap s obj)) pt x
       = get_pt_xn (\<lambda>obj. get_arch_obj (kheap s' obj)) pt x"
  apply (simp add: get_pt_xn_def)
  apply (subst requiv_get_pt_entry_eq, simp+)
  done

lemma requiv_get_page_xn_eq:
  "\<lbrakk> reads_equiv aag s s'; pas_refined aag s; is_subject aag pd;
     x \<notin> kernel_mappings \<rbrakk>
   \<Longrightarrow> get_page_xn (\<lambda>obj. get_arch_obj (kheap s obj)) pd x
       = get_page_xn (\<lambda>obj. get_arch_obj (kheap s' obj)) pd x"
  apply (simp add: get_page_xn_def)
  apply (subst requiv_get_pd_entry_eq[symmetric], simp+)
  apply (clarsimp split: option.splits pde.splits)
  apply (frule pt_in_pd_same_agent, fastforce+)
  apply (rule requiv_get_pt_xn_eq, simp+)
  done

lemma some_get_page_xn_kmapsD:
  "\<lbrakk>get_page_xn (\<lambda>obj. get_arch_obj (kheap s obj)) pd_ref p = Some xn;
    p \<in> kernel_mappings; valid_global_pd_mappings s; equal_kernel_mappings s\<rbrakk>
   \<Longrightarrow> \<not> xn"
  apply (clarsimp simp: get_page_xn_def get_pd_entry_def get_arch_obj_def
                        kernel_mappings_slots_eq
                 split: option.splits Structures_A.kernel_object.splits
                        arch_kernel_obj.splits)
  apply (erule valid_global_pd_mappingsE)
  apply (clarsimp simp: equal_kernel_mappings_def obj_at_def)
  apply (drule_tac x=pd_ref in spec,
         drule_tac x="arm_global_pd (arch_state s)" in spec, simp)
  apply (drule bspec, assumption)
  apply (clarsimp simp: valid_pd_kernel_mappings_def pde_mapping_bits_def)
  apply (drule_tac x="ucast (p >> 20)" in spec)
  apply (clarsimp simp: get_page_xn_def get_pd_entry_def get_arch_obj_def
                        get_pt_xn_def get_pt_entry_def
                        kernel_mappings_slots_eq
                 split: option.splits Structures_A.kernel_object.splits
                        arch_kernel_obj.splits
                        ARM_Structs_A.pde.splits ARM_Structs_A.pte.splits)
     apply (simp add: valid_pde_kernel_mappings_def obj_at_def
                      valid_pt_kernel_mappings_def)
     apply (drule_tac x="ucast ((p >> 12) && mask 8)" in spec)
     apply (clarsimp simp: valid_pte_kernel_mappings_def)
    apply (simp add: valid_pde_kernel_mappings_def obj_at_def
                     valid_pt_kernel_mappings_def)
    apply (drule_tac x="ucast ((p >> 12) && mask 8)" in spec)
    apply (clarsimp simp: valid_pte_kernel_mappings_def)
   apply (simp add: valid_pde_kernel_mappings_def)
  apply (simp add: valid_pde_kernel_mappings_def)
  done

lemma get_pt_xn_some_get_pt_info:
  "get_pt_xn ahp pd_ref vptr = Some xn \<Longrightarrow>
    \<exists>base sz rights. get_pt_info ahp pd_ref vptr = Some (base, sz, rights)"
  by (simp add: get_pt_xn_def get_pt_info_def split: option.splits pte.splits)

lemma get_page_xn_some_get_page_info:
  "get_page_xn ahp pd_ref vptr = Some xn \<Longrightarrow>
    \<exists>base sz rights. get_page_info ahp pd_ref vptr = Some (base, sz, rights)"
  apply (simp add: get_page_xn_def get_page_info_def split: option.splits pde.splits)
  apply (drule get_pt_xn_some_get_pt_info)
  apply simp
  done

lemma requiv_ptable_xn_eq:
  "\<lbrakk> reads_equiv aag s s'; pas_refined aag s; pas_refined aag s';
     is_subject aag (cur_thread s); invs s; invs s' \<rbrakk>
   \<Longrightarrow> ptable_xn_s s = ptable_xn_s s'"
  apply (simp add: ptable_xn_s_def)
  apply (rule ext)
  apply (case_tac "x \<in> kernel_mappings")
   apply (clarsimp simp: ptable_xn_def split: option.splits)
   apply (intro conjI)
    apply clarsimp
    apply (frule some_get_page_xn_kmapsD)
       apply (fastforce simp: invs_valid_global_pd_mappings invs_equal_kernel_mappings)+
   apply clarsimp
   apply (frule some_get_page_xn_kmapsD)
      apply (fastforce simp: invs_valid_global_pd_mappings invs_equal_kernel_mappings)+
   apply clarsimp
   apply (frule_tac xn=True in some_get_page_xn_kmapsD)
      apply (fastforce simp: invs_valid_global_pd_mappings invs_equal_kernel_mappings)+

  apply (case_tac "get_pd_of_thread (kheap s) (arch_state s) (cur_thread s)
                 = arm_global_pd (arch_state s)")
   apply (frule requiv_pd_of_thread_global_pd)
       apply fastforce+
   apply (clarsimp simp: ptable_xn_def split: option.splits)
   apply (intro conjI)
    apply clarsimp
    apply (drule get_page_xn_some_get_page_info)
    apply clarsimp
    apply (frule get_page_info_gpd_kmaps[rotated, rotated])
      apply (fastforce simp: invs_valid_global_objs invs_arch_state)+
   apply clarsimp
   apply (intro conjI)
    apply clarsimp
    apply (drule get_page_xn_some_get_page_info)
    apply clarsimp
    apply (frule get_page_info_gpd_kmaps[rotated, rotated])
      apply (fastforce simp: invs_valid_global_objs invs_arch_state)+
   apply clarsimp
   apply (drule get_page_xn_some_get_page_info)
   apply clarsimp
   apply (frule get_page_info_gpd_kmaps[rotated, rotated])
     apply (fastforce simp: invs_valid_global_objs invs_arch_state)+

  apply (case_tac "get_pd_of_thread (kheap s') (arch_state s') (cur_thread s')
                 = arm_global_pd (arch_state s')")
  apply (drule reads_equiv_sym)
  apply (frule requiv_pd_of_thread_global_pd)
       apply (fastforce simp: reads_equiv_def)+

  apply (simp add: ptable_xn_def)
  apply (frule requiv_get_pd_of_thread_eq)
        apply fastforce+
  apply (frule pd_of_thread_same_agent, simp+)
  apply (subst requiv_get_page_xn_eq, simp+)
  done

lemma requiv_user_mem_eq:
  "\<lbrakk> reads_equiv aag s s'; globals_equiv s s'; invs s;
     invs s'; is_subject aag (cur_thread s); AllowRead \<in> ptable_rights_s s x;
     ptable_lift_s s x = Some y; pas_refined aag s; pas_refined aag s' \<rbrakk>
   \<Longrightarrow> user_mem s (ptrFromPAddr y) = user_mem s' (ptrFromPAddr y)"
  apply (simp add: user_mem_def)
  apply (subgoal_tac "in_user_frame (ptrFromPAddr y) s")
   apply (subgoal_tac "in_user_frame (ptrFromPAddr y) s'")
    apply clarsimp
    apply (rule_tac P="(ptrFromPAddr y) \<in> range_of_arm_globals_frame s" in case_split)
     apply (clarsimp simp: globals_equiv_def)
    apply (subgoal_tac "aag_can_read aag (ptrFromPAddr y)")
     apply (erule reads_equivE)
     apply (erule_tac f="underlying_memory" in equiv_forE)
     apply simp
    apply (frule_tac auth=Read in user_op_access)
        apply (fastforce simp: ptable_lift_s_def ptable_rights_s_def
                               vspace_cap_rights_to_auth_def)+
    apply (rule reads_read)
    apply simp
   apply (frule requiv_ptable_rights_eq, fastforce+)
   apply (frule requiv_ptable_lift_eq, fastforce+)
   apply (rule ptable_rights_imp_user_frame)
     apply (fastforce simp: invs_valid_stateI ptable_rights_s_def ptable_lift_s_def)+
  apply (rule ptable_rights_imp_user_frame)
    apply (fastforce simp: invs_valid_stateI ptable_rights_s_def ptable_lift_s_def)+
  done

lemma gets_ev''':
  "equiv_valid_inv I A (\<lambda>s. P s \<and> (\<forall> t. I s t \<and> A s t \<and> P t \<longrightarrow> f s = f t)) (gets f)"
  apply (simp add: equiv_valid_def2)
  apply (auto simp: equiv_valid_2_def in_monad)
  done

lemma spec_equiv_valid_add_asm:
  "((P st) \<Longrightarrow> spec_equiv_valid_inv st I A P f) \<Longrightarrow> spec_equiv_valid_inv st I A P f"
  apply(clarsimp simp: spec_equiv_valid_def equiv_valid_2_def)
  done

lemma spec_equiv_valid_add_rel:
  "\<lbrakk>spec_equiv_valid_inv st I A (P and I st) f; \<And>s. I s s\<rbrakk> \<Longrightarrow> spec_equiv_valid_inv st I A P f"
  apply (clarsimp simp: spec_equiv_valid_def equiv_valid_2_def)
  done

lemma spec_equiv_valid_add_rel':
  "\<lbrakk>spec_equiv_valid_inv st I A (P and A st) f; \<And>s. A s s\<rbrakk> \<Longrightarrow> spec_equiv_valid_inv st I A P f"
  apply (clarsimp simp: spec_equiv_valid_def equiv_valid_2_def)
  done

lemma reads_equiv_g_refl:
  "reads_equiv_g aag s s"
  apply (rule reads_equiv_gI)
   apply (rule reads_equiv_refl)
  apply (rule globals_equiv_refl)
  done

definition context_matches_state where
  "context_matches_state pl pr pxn um es s \<equiv>
      pl = ptable_lift_s s |` {x. pr x \<noteq> {}} \<and>
      pr = ptable_rights_s s \<and>
      pxn = ptable_xn_s s \<and>
      um = (user_mem s \<circ> ptrFromPAddr) |` {y. \<exists>x. pl x = Some y \<and> AllowRead \<in> pr x} \<and>
      es = exclusive_state (machine_state s)"

(* FIXME - move - duplicated in Schedule_IF *)
lemma dmo_ev:
  "(\<And>s s'. equiv_valid (\<lambda>ms ms'. I (s\<lparr>machine_state := ms\<rparr>) (s'\<lparr>machine_state := ms'\<rparr>))
                   (\<lambda>ms ms'. A (s\<lparr>machine_state := ms\<rparr>) (s'\<lparr>machine_state := ms'\<rparr>))
                   (\<lambda>ms ms'. B (s\<lparr>machine_state := ms\<rparr>) (s'\<lparr>machine_state := ms'\<rparr>))
          (K (P s \<and> P s')) f)
    \<Longrightarrow> equiv_valid I A B P (do_machine_op f)"
  apply (clarsimp simp: do_machine_op_def bind_def equiv_valid_def2 equiv_valid_2_def gets_def get_def select_f_def modify_def put_def return_def split_def)
  apply atomize
  apply (erule_tac x=s in allE)
  apply (erule_tac x=t in allE)
  apply simp
  apply (erule_tac x="machine_state s" in allE)
  apply (erule_tac x="machine_state t" in allE)
  apply fastforce
  done

(* FIXME - move - duplicated in Schedule_IF *)
lemma ev_modify: "(\<And> s t. \<lbrakk>P s; P t; A s t; I s t\<rbrakk> \<Longrightarrow> (I (f s) (f t)) \<and> (B (f s) (f t))) \<Longrightarrow> equiv_valid I A B P (modify f)"
  apply (clarsimp simp add: equiv_valid_def2 equiv_valid_2_def simpler_modify_def)
  done

lemma dmo_setExMonitor_reads_respects_g:
  "reads_respects_g aag l \<top> (do_machine_op (setExMonitor es))"
  apply (simp add: setExMonitor_def)
  apply (wp dmo_ev ev_modify)
  apply (clarsimp simp: reads_equiv_g_def)
  apply (clarsimp simp: reads_equiv_def affects_equiv_def states_equiv_for_def equiv_for_def equiv_asids_def equiv_asid_def globals_equiv_def idle_equiv_def)
  done

lemma dmo_getExMonitor_reads_respects_g:
  "reads_respects_g aag l (\<lambda>s. cur_thread s \<noteq> idle_thread s) (do_machine_op getExMonitor)"
  apply (simp add: getExMonitor_def)
  apply (wp dmo_ev gets_ev'')
  apply (clarsimp simp: reads_equiv_g_def globals_equiv_def)
  done

lemma getExMonitor_wp[wp]:
  "\<lbrace>\<lambda>ms. P (exclusive_state ms) ms\<rbrace> getExMonitor \<lbrace>P\<rbrace>"
  by (simp add: getExMonitor_def | wp)+

lemma do_user_op_reads_respects_g:
  notes split_paired_All[simp del]
  shows "( \<forall>pl pr pxn tc um es s. P tc s \<and> context_matches_state pl pr pxn um es s \<longrightarrow> (\<exists>x. uop (cur_thread s) pl pr pxn (tc, um, es) = {x}))
   \<Longrightarrow> reads_respects_g aag l (pas_refined aag and invs and is_subject aag \<circ> cur_thread and (\<lambda>s. cur_thread s \<noteq> idle_thread s) and P tc) (do_user_op_if uop tc)"
  apply (simp add: do_user_op_if_def)
  apply (rule use_spec_ev)
  apply (rule spec_equiv_valid_add_asm)
  apply (rule spec_equiv_valid_add_rel[OF _ reads_equiv_g_refl])
  apply (rule spec_equiv_valid_add_rel'[OF _ affects_equiv_refl])
  apply (rule spec_equiv_valid_guard_imp)
   apply (wp dmo_user_memory_update_reads_respects_g dmo_setExMonitor_reads_respects_g | wpc)+
                  apply (erule_tac x = rvb in allE)
                  apply (erule_tac x = "rv" in allE)
                  apply (erule_tac x = "rva" in allE)
                  apply (erule_tac x = "tc" in allE)
                  apply (erule_tac x = "rvd" in allE)
                  apply (erule_tac x = "rve" in allE)
                  apply (erule_tac x = st in allE)
                  apply (rule_tac Q="P tc st \<and> context_matches_state rvb rv rva rvd rve st" in gen_asm_ev(2))
                  apply clarsimp
                  apply (wp add: select_wp select_ev dmo_getExMonitor_reads_respects_g del: gets_ev
                        | rule_tac P="pas_refined aag and invs" in gets_ev''' | simp)+
  apply (simp add: reads_equiv_g_def, intro context_conjI allI impI, safe)
        apply (simp add: requiv_ptable_rights_eq)
       apply (simp add: requiv_ptable_xn_eq)
      apply (subst expand_restrict_map_eq)
      apply (clarsimp simp: requiv_ptable_lift_eq)
     apply (simp add: requiv_cur_thread_eq)
    apply (subst expand_restrict_map_eq)
    apply (clarsimp simp: restrict_map_def requiv_user_mem_eq)
   apply (simp add: context_matches_state_def comp_def)
  apply (erule_tac x=st in allE)+
  apply (simp add: context_matches_state_def reads_equiv_sym globals_equiv_sym affects_equiv_sym comp_def)
  apply (simp add: globals_equiv_def)
  done

end
