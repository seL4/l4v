(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory KHeap_R
imports
  "AInvs.ArchDetSchedSchedule_AI"
  Machine_R
begin

lemma lookupAround2_known1:
  "m x = Some y \<Longrightarrow> fst (lookupAround2 x m) = Some (x, y)"
  by (fastforce simp: lookupAround2_char1)

context begin interpretation Arch . (*FIXME: arch_split*)

lemma obj_at_getObject:
  assumes R:
  "\<And>a b n ko s obj::'a::pspace_storable.
  \<lbrakk> (a, b) \<in> fst (loadObject t t n ko s); projectKO_opt ko = Some obj \<rbrakk> \<Longrightarrow> a = obj"
  shows "\<lbrace>obj_at' P t\<rbrace> getObject t \<lbrace>\<lambda>(rv::'a::pspace_storable) s. P rv\<rbrace>"
  by (auto simp: getObject_def obj_at'_def in_monad valid_def
                 split_def projectKOs lookupAround2_known1
           dest: R)

declare projectKO_inv [wp]

lemma loadObject_default_inv:
  "\<lbrace>P\<rbrace> loadObject_default addr addr' next obj \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: loadObject_default_def magnitudeCheck_def alignCheck_def unless_def alignError_def
      | wp hoare_vcg_split_case_option hoare_drop_imps hoare_vcg_all_lift)+

lemma getObject_inv:
  assumes x: "\<And>p q n ko. \<lbrace>P\<rbrace> loadObject p q n ko \<lbrace>\<lambda>(rv :: 'a :: pspace_storable). P\<rbrace>"
  shows      "\<lbrace>P\<rbrace> getObject p \<lbrace>\<lambda>(rv :: 'a :: pspace_storable). P\<rbrace>"
  by (simp add: getObject_def split_def | wp x)+

lemma getObject_inv_tcb [wp]: "\<lbrace>P\<rbrace> getObject l \<lbrace>\<lambda>(rv :: Structures_H.tcb). P\<rbrace>"
  apply (rule getObject_inv)
  apply simp
  apply (rule loadObject_default_inv)
  done

lemma no_fail_loadObject_default [wp]:
  "no_fail (\<lambda>s. \<exists>obj. projectKO_opt ko = Some (obj::'a) \<and>
                      is_aligned p (objBits obj) \<and> q = p
                      \<and> case_option True (\<lambda>x. 2 ^ (objBits obj) \<le> x - p) n)
           (loadObject_default p q n ko :: ('a::pre_storable) kernel)"
  apply (simp add: loadObject_default_def split_def projectKO_def
                   alignCheck_def alignError_def magnitudeCheck_def
                   unless_def)
  apply (rule no_fail_pre)
   apply (wp case_option_wp)
  apply (clarsimp simp: is_aligned_mask)
  apply (clarsimp split: option.split_asm)
  apply (clarsimp simp: is_aligned_mask[symmetric])
  apply simp
  done

lemma no_fail_getObject_tcb [wp]:
  "no_fail (tcb_at' t) (getObject t :: tcb kernel)"
  apply (simp add: getObject_def split_def)
  apply (rule no_fail_pre)
   apply wp
  apply (clarsimp simp add: obj_at'_def projectKOs objBits_simps'
                      cong: conj_cong)
  apply (rule ps_clear_lookupAround2, assumption+)
    apply simp
   apply (simp add: field_simps)
   apply (erule is_aligned_no_wrap')
   apply simp
  apply (fastforce split: option.split_asm simp: objBits_simps' archObjSize_def)
  done

lemma typ_at_to_obj_at':
  "typ_at' (koType (TYPE ('a :: pspace_storable))) p s
     = obj_at' (\<top> :: 'a \<Rightarrow> bool) p s"
  by (simp add: typ_at'_def obj_at'_real_def project_koType[symmetric])

lemmas typ_at_to_obj_at_arches
  = typ_at_to_obj_at'[where 'a=pte, simplified]
    typ_at_to_obj_at' [where 'a=pde, simplified]
    typ_at_to_obj_at'[where 'a=asidpool, simplified]
    typ_at_to_obj_at'[where 'a=user_data, simplified]
    typ_at_to_obj_at'[where 'a=user_data_device, simplified]

lemmas page_table_at_obj_at'
  = page_table_at'_def[unfolded typ_at_to_obj_at_arches]


lemma corres_get_tcb [corres]:
  "corres (tcb_relation \<circ> the) (tcb_at t) (tcb_at' t) (gets (get_tcb t)) (getObject t)"
  apply (rule corres_no_failI)
   apply wp
  apply (clarsimp simp add: gets_def get_def return_def bind_def get_tcb_def)
  apply (frule in_inv_by_hoareD [OF getObject_inv_tcb])
  apply (clarsimp simp add: obj_at_def is_tcb obj_at'_def projectKO_def
                            projectKO_opt_tcb split_def
                            getObject_def loadObject_default_def in_monad)
  apply (case_tac koa)
   apply (simp_all add: fail_def return_def)
  apply (case_tac bb)
   apply (simp_all add: fail_def return_def)
  apply (clarsimp simp add: state_relation_def pspace_relation_def)
  apply (drule bspec)
   apply clarsimp
   apply blast
  apply (clarsimp simp add: other_obj_relation_def
                            lookupAround2_known1)
  done

lemma lookupAround2_same1[simp]:
  "(fst (lookupAround2 x s) = Some (x, y)) = (s x = Some y)"
  apply (rule iffI)
   apply (simp add: lookupAround2_char1)
  apply (simp add: lookupAround2_known1)
  done

lemma getObject_tcb_at':
  "\<lbrace> \<top> \<rbrace> getObject t \<lbrace>\<lambda>r::tcb. tcb_at' t\<rbrace>"
  by (clarsimp simp: valid_def getObject_def in_monad
                     loadObject_default_def obj_at'_def projectKOs split_def
                     in_magnitude_check objBits_simps')

text \<open>updateObject_cte lemmas\<close>

lemma koType_objBitsKO:
  "koTypeOf k = koTypeOf k' \<Longrightarrow> objBitsKO k = objBitsKO k'"
  by (auto simp: objBitsKO_def archObjSize_def
          split: Structures_H.kernel_object.splits
                 ARM_H.arch_kernel_object.splits)

lemma updateObject_objBitsKO:
    "(ko', t') \<in> fst (updateObject (val :: 'a :: pspace_storable) ko p q n t)
         \<Longrightarrow> objBitsKO ko' = objBitsKO ko"
  apply (drule updateObject_type)
  apply (erule koType_objBitsKO)
  done

lemmas tcbSlot_defs = tcbCTableSlot_def tcbVTableSlot_def tcbIPCBufferSlot_def
                      tcbFaultHandlerSlot_def tcbTimeoutHandlerSlot_def

lemma updateObject_cte_is_tcb_or_cte:
  fixes cte :: cte and ptr :: word32
  shows "\<lbrakk> fst (lookupAround2 p (ksPSpace s)) = Some (q, ko);
           snd (lookupAround2 p (ksPSpace s)) = n;
           (ko', s') \<in> fst (updateObject cte ko p q n s) \<rbrakk> \<Longrightarrow>
  (\<exists>tcb getF setF. ko = KOTCB tcb \<and> s' = s \<and> tcb_cte_cases (p - q) = Some (getF, setF)
    \<and> ko' = KOTCB (setF (\<lambda>x. cte) tcb) \<and> is_aligned q tcbBlockSizeBits \<and> ps_clear q tcbBlockSizeBits s) \<or>
  (\<exists>cte'. ko = KOCTE cte' \<and> ko' = KOCTE cte \<and> s' = s
        \<and> p = q \<and> is_aligned p cte_level_bits \<and> ps_clear p cte_level_bits s)"
  apply (clarsimp simp: updateObject_cte typeError_def alignError_def
               tcbVTableSlot_def tcbCTableSlot_def to_bl_1 rev_take objBits_simps'
               in_monad map_bits_to_bl cte_level_bits_def in_magnitude_check field_simps
               lookupAround2_char1
         split: kernel_object.splits)
  apply (subst(asm) in_magnitude_check3, simp+)
   apply (simp add: in_monad tcbSlot_defs
             split: if_split_asm)
  apply (simp add: in_monad tcbSlot_defs
            split: if_split_asm)
  done

declare plus_1_less[simp]

lemma ps_clear_domE[elim?]:
  "\<lbrakk> ps_clear x n s; dom (ksPSpace s) = dom (ksPSpace s') \<rbrakk> \<Longrightarrow> ps_clear x n s'"
  by (simp add: ps_clear_def)

lemma ps_clear_upd':
  "ksPSpace s y = Some v \<Longrightarrow>
    ps_clear x n (ksPSpace_update (\<lambda>a. ksPSpace s(y \<mapsto> v')) s') = ps_clear x n s"
  by (rule iffI | clarsimp elim!: ps_clear_domE | fastforce)+

lemmas ps_clear_updE'[elim] = iffD2[OF ps_clear_upd', rotated]

lemma updateObject_default_result:
  "(x, s'') \<in> fst (updateObject_default e ko p q n s) \<Longrightarrow> x = injectKO e"
  by (clarsimp simp add: updateObject_default_def in_monad)

lemma obj_at_setObject1:
  assumes R: "\<And>(v::'a::pspace_storable) p q n ko s x s''.
                (x, s'') \<in> fst (updateObject v ko p q n s) \<Longrightarrow> x = injectKO v"
  assumes Q: "\<And>(v::'a::pspace_storable) (v'::'a). objBits v = objBits v'"
  shows
  "\<lbrace> obj_at' (\<lambda>x::'a::pspace_storable. True) t \<rbrace>
   setObject p (v::'a::pspace_storable)
  \<lbrace> \<lambda>rv. obj_at' (\<lambda>x::'a::pspace_storable. True) t \<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (rule hoare_seq_ext [OF _ hoare_gets_post])
  apply (clarsimp simp: valid_def in_monad obj_at'_def
                        projectKOs lookupAround2_char1
                        project_inject
                 dest!: R)
  apply (subgoal_tac "objBitsKO (injectKO v) = objBitsKO (injectKO obj)")
   apply (intro conjI impI, simp_all)
      apply fastforce+
  apply (fold objBits_def)
  apply (rule Q)
  done

lemma obj_at_setObject2:
  fixes v :: "'a::pspace_storable"
  fixes P :: "'b::pspace_storable \<Rightarrow> bool"
  assumes R: "\<And>ko s' (v :: 'a) oko x y n s. (ko, s') \<in> fst (updateObject v oko x y n s)
                                  \<Longrightarrow> koTypeOf ko \<noteq> koType TYPE('b)"
  shows
  "\<lbrace> obj_at' P t \<rbrace>
   setObject p (v::'a)
  \<lbrace> \<lambda>rv. obj_at' P t \<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (rule hoare_seq_ext [OF _ hoare_gets_post])
  apply (clarsimp simp: valid_def in_monad)
  apply (frule updateObject_type)
  apply (drule R)
  apply (clarsimp simp: obj_at'_def projectKOs)
  apply (rule conjI)
   apply (clarsimp simp: lookupAround2_char1)
   apply (drule iffD1 [OF project_koType, OF exI])
   apply simp
  apply (clarsimp simp: ps_clear_upd' lookupAround2_char1)
  done

lemmas objBits_type = koType_objBitsKO

lemma setObject_typ_at_inv:
  "\<lbrace>typ_at' T p'\<rbrace> setObject p v \<lbrace>\<lambda>r. typ_at' T p'\<rbrace>"
  apply (clarsimp simp: setObject_def split_def)
  apply (clarsimp simp: valid_def typ_at'_def ko_wp_at'_def in_monad
                        lookupAround2_char1 ps_clear_upd')
  apply (drule updateObject_type)
  apply clarsimp
  apply (drule objBits_type)
  apply (simp add: ps_clear_upd')
  done

lemma setObject_typ_at_not:
  "\<lbrace>\<lambda>s. \<not> (typ_at' T p' s)\<rbrace> setObject p v \<lbrace>\<lambda>r s. \<not> (typ_at' T p' s)\<rbrace>"
  apply (clarsimp simp: setObject_def valid_def in_monad split_def)
  apply (erule notE)
  apply (clarsimp simp: typ_at'_def ko_wp_at'_def lookupAround2_char1
                 split: if_split_asm)
   apply (drule updateObject_type)
   apply clarsimp
   apply (drule objBits_type)
   apply (clarsimp elim!: ps_clear_domE)
   apply fastforce
  apply (clarsimp elim!: ps_clear_domE)
  apply fastforce
  done

lemma setObject_typ_at'[wp]:
  "\<lbrace>\<lambda>s. P (typ_at' T p' s)\<rbrace> setObject p v \<lbrace>\<lambda>r s. P (typ_at' T p' s)\<rbrace>"
  by (blast intro: P_bool_lift setObject_typ_at_inv setObject_typ_at_not)

lemmas setObject_typ_ats [wp] = typ_at_lifts [OF setObject_typ_at']

lemma setObject_cte_wp_at2':
  assumes x: "\<And>x n tcb s t. \<lbrakk> t \<in> fst (updateObject v (KOTCB tcb) ptr x n s); Q s;
                               lookupAround2 ptr (ksPSpace s) = (Some (x, KOTCB tcb), n) \<rbrakk>
                  \<Longrightarrow> \<exists>tcb'. t = (KOTCB tcb', s) \<and> (\<forall>(getF, setF) \<in> ran tcb_cte_cases. getF tcb' = getF tcb)"
  assumes y: "\<And>x n cte s. fst (updateObject v (KOCTE cte) ptr x n s) = {}"
  shows      "\<lbrace>\<lambda>s. P' (cte_wp_at' P p s) \<and> Q s\<rbrace> setObject ptr v \<lbrace>\<lambda>rv s. P' (cte_wp_at' P p s)\<rbrace>"
  apply (clarsimp simp add: setObject_def valid_def in_monad split_def)
  apply (simp add: cte_wp_at_cases' split del: if_split)
  apply (erule rsubst[where P=P'])
  apply (rule iffI)
   apply (erule disjEI)
    apply (clarsimp simp: ps_clear_upd' lookupAround2_char1 y)
   apply (erule exEI [where 'a=word32])
   apply (clarsimp simp: ps_clear_upd' lookupAround2_char1)
   apply (drule(1) x)
    apply (clarsimp simp: lookupAround2_char1 prod_eqI)
   apply (fastforce dest: bspec [OF _ ranI])
  apply (erule disjEI)
   apply (clarsimp simp: ps_clear_upd' lookupAround2_char1
                  split: if_split_asm)
   apply (frule updateObject_type)
   apply (case_tac ba, simp_all add: y)[1]
  apply (erule exEI)
  apply (clarsimp simp: ps_clear_upd' lookupAround2_char1
                 split: if_split_asm)
  apply (frule updateObject_type)
  apply (case_tac ba, simp_all)
  apply (drule(1) x)
   apply (clarsimp simp: prod_eqI lookupAround2_char1)
  apply (fastforce dest: bspec [OF _ ranI])
  done

lemma setObject_cte_wp_at':
  assumes x: "\<And>x n tcb s t. \<lbrakk> t \<in> fst (updateObject v (KOTCB tcb) ptr x n s); Q s;
                               lookupAround2 ptr (ksPSpace s) = (Some (x, KOTCB tcb), n) \<rbrakk>
                  \<Longrightarrow> \<exists>tcb'. t = (KOTCB tcb', s) \<and> (\<forall>(getF, setF) \<in> ran tcb_cte_cases. getF tcb' = getF tcb)"
  assumes y: "\<And>x n cte s. fst (updateObject v (KOCTE cte) ptr x n s) = {}"
  shows      "\<lbrace>cte_wp_at' P p and Q\<rbrace> setObject ptr v \<lbrace>\<lambda>rv. cte_wp_at' P p\<rbrace>"
  unfolding pred_conj_def
  by (rule setObject_cte_wp_at2'[OF x y], assumption+)

lemma setObject_ep_pre:
  assumes "\<lbrace>P and ep_at' p\<rbrace> setObject p (e::endpoint) \<lbrace>Q\<rbrace>"
  shows "\<lbrace>P\<rbrace> setObject p (e::endpoint) \<lbrace>Q\<rbrace>" using assms
  apply (clarsimp simp: valid_def setObject_def in_monad
                        split_def updateObject_default_def
                        projectKOs in_magnitude_check objBits_simps')
  apply (drule spec, drule mp, erule conjI)
   apply (simp add: obj_at'_def projectKOs objBits_simps')
  apply (simp add: split_paired_Ball)
  apply (drule spec, erule mp)
  apply (clarsimp simp: in_monad projectKOs in_magnitude_check)
  done

lemma setObject_ntfn_pre:
  assumes "\<lbrace>P and ntfn_at' p\<rbrace> setObject p (e::Structures_H.notification) \<lbrace>Q\<rbrace>"
  shows "\<lbrace>P\<rbrace> setObject p (e::Structures_H.notification) \<lbrace>Q\<rbrace>" using assms
  apply (clarsimp simp: valid_def setObject_def in_monad
                        split_def updateObject_default_def
                        projectKOs in_magnitude_check objBits_simps')
  apply (drule spec, drule mp, erule conjI)
   apply (simp add: obj_at'_def projectKOs objBits_simps')
  apply (simp add: split_paired_Ball)
  apply (drule spec, erule mp)
  apply (clarsimp simp: in_monad projectKOs in_magnitude_check)
  done

lemma setObject_tcb_pre:
  assumes "\<lbrace>P and tcb_at' p\<rbrace> setObject p (t::tcb) \<lbrace>Q\<rbrace>"
  shows "\<lbrace>P\<rbrace> setObject p (t::tcb) \<lbrace>Q\<rbrace>" using assms
  apply (clarsimp simp: valid_def setObject_def in_monad
                        split_def updateObject_default_def
                        projectKOs in_magnitude_check objBits_simps')
  apply (drule spec, drule mp, erule conjI)
   apply (simp add: obj_at'_def projectKOs objBits_simps')
  apply (simp add: split_paired_Ball)
  apply (drule spec, erule mp)
  apply (clarsimp simp: in_monad projectKOs in_magnitude_check)
  done

lemma setObject_reply_pre:
  assumes "\<lbrace>P and reply_at' p\<rbrace> setObject p (t::reply) \<lbrace>Q\<rbrace>"
  shows "\<lbrace>P\<rbrace> setObject p (t::reply) \<lbrace>Q\<rbrace>" using assms
  apply (clarsimp simp: valid_def setObject_def in_monad
                        split_def updateObject_default_def
                        projectKOs in_magnitude_check objBits_simps')
  apply (drule spec, drule mp, erule conjI)
   apply (simp add: obj_at'_def projectKOs objBits_simps')
  apply (simp add: split_paired_Ball)
  apply (drule spec, erule mp)
  apply (clarsimp simp: in_monad projectKOs in_magnitude_check)
  done

lemma setObject_sched_context_pre:
  assumes "\<lbrace>P and sc_at' p\<rbrace> setObject p (t::sched_context) \<lbrace>Q\<rbrace>"
  shows "\<lbrace>P\<rbrace> setObject p (t::sched_context) \<lbrace>Q\<rbrace>" using assms
  apply (clarsimp simp: valid_def setObject_def in_monad
                        split_def updateObject_default_def
                        projectKOs in_magnitude_check objBits_simps')
  apply (drule spec, drule mp, erule conjI)
   apply (simp add: obj_at'_def projectKOs objBits_simps')
  apply (simp add: split_paired_Ball)
  apply (drule spec, erule mp)
  apply (clarsimp simp: in_monad projectKOs in_magnitude_check)
  done

lemma obj_at_setObject3:
  fixes Q::"'a::pspace_storable \<Rightarrow> bool"
  fixes P::"'a::pspace_storable \<Rightarrow> bool"
  assumes R: "\<And>ko s x y n. (updateObject v ko p y n s)
                   = (updateObject_default v ko p y n s)"
  assumes P: "\<And>(v::'a::pspace_storable). (1 :: word32) < 2 ^ (objBits v)"
  shows "\<lbrace>(\<lambda>s. P v)\<rbrace> setObject p v \<lbrace>\<lambda>rv. obj_at' P p\<rbrace>"
  apply (clarsimp simp add: valid_def in_monad obj_at'_def
                            setObject_def split_def projectKOs
                            project_inject objBits_def[symmetric]
                            R updateObject_default_def
                            in_magnitude_check P ps_clear_upd')
  apply fastforce
  done

lemma setObject_tcb_strongest:
  "\<lbrace>\<lambda>s. if t = t' then P tcb else obj_at' P t' s\<rbrace>
  setObject t (tcb :: tcb)
  \<lbrace>\<lambda>rv. obj_at' P t'\<rbrace>"
  apply (cases "t = t'")
   apply simp
   apply (rule hoare_weaken_pre)
    apply (rule obj_at_setObject3)
     apply simp
    apply (simp add: objBits_simps')
   apply simp
  apply (simp add: setObject_def split_def)
  apply (clarsimp simp: valid_def obj_at'_def split_def in_monad
                        updateObject_default_def projectKOs
                        ps_clear_upd')
  done

method setObject_replies_of =
  clarsimp simp: setObject_def in_monad split_def valid_def,
  erule rsubst[where P=P'], rule ext,
  clarsimp simp: updateObject_default_def in_monad opt_map_def projectKO_opts_defs projectKO_eq2
         split: Structures_H.kernel_object.split_asm

lemma setObject_endpoint_replies_of'[wp]:
  "setObject c (endpoint::endpoint) \<lbrace>\<lambda>s. P' (replies_of' s)\<rbrace>"
  by setObject_replies_of

lemma setObject_notification_replies_of'[wp]:
  "setObject c (notification::notification) \<lbrace>\<lambda>s. P' (replies_of' s)\<rbrace>"
  by setObject_replies_of

lemma setObject_tcb_replies_of'[wp]:
  "setObject c (tcb::tcb) \<lbrace>\<lambda>s. P' (replies_of' s)\<rbrace>"
  by setObject_replies_of

lemma setObject_sched_context_replies_of'[wp]:
  "setObject c (sched_context::sched_context) \<lbrace>\<lambda>s. P' (replies_of' s)\<rbrace>"
  by setObject_replies_of

lemma setObject_cte_replies_of'[wp]:
  "setObject c (cte::cte) \<lbrace>\<lambda>s. P' (replies_of' s)\<rbrace>"
  apply (clarsimp simp: setObject_def in_monad split_def valid_def lookupAround2_char1)
  apply (erule rsubst[where P=P'], rule ext)
  apply (clarsimp simp: updateObject_cte in_monad
                        typeError_def opt_map_def projectKO_opts_defs
                 split: if_split_asm
                        Structures_H.kernel_object.split_asm)
  done

(* Warning: This may not be a weakest precondition. *)
lemma setObject_reply_replies_of'[wp]:
  "\<lbrace>\<lambda>s. P' ((replies_of' s)(c \<mapsto> reply))\<rbrace>
  setObject c (reply::reply)
  \<lbrace>\<lambda>_ s. P' (replies_of' s)\<rbrace>"
  apply (clarsimp simp: setObject_def in_monad split_def
                        valid_def lookupAround2_char1)
  apply (clarsimp simp: updateObject_default_def in_monad
                        typeError_def opt_map_def projectKO_opts_defs
                 split: if_split_asm
                        Structures_H.kernel_object.split_asm)
  done

crunches setNotification, setEndpoint, setSchedContext
  for replies_of'[wp]: "\<lambda>s. P (replies_of' s)"

lemma getObject_obj_at':
  assumes x: "\<And>q n ko. loadObject p q n ko =
                (loadObject_default p q n ko :: ('a :: pspace_storable) kernel)"
  assumes P: "\<And>(v::'a::pspace_storable). (1 :: word32) < 2 ^ (objBits v)"
  shows      "\<lbrace> \<top> \<rbrace> getObject p \<lbrace>\<lambda>r::'a::pspace_storable. obj_at' ((=) r) p\<rbrace>"
  by (clarsimp simp: valid_def getObject_def in_monad
                     loadObject_default_def obj_at'_def projectKOs
                     split_def in_magnitude_check lookupAround2_char1
                     x P project_inject objBits_def[symmetric])

lemma getObject_valid_obj:
  assumes x: "\<And>p q n ko. loadObject p q n ko =
                (loadObject_default p q n ko :: ('a :: pspace_storable) kernel)"
  assumes P: "\<And>(v::'a::pspace_storable). (1 :: word32) < 2 ^ (objBits v)"
  shows "\<lbrace> valid_objs' \<rbrace> getObject p \<lbrace>\<lambda>rv::'a::pspace_storable. valid_obj' (injectKO rv) \<rbrace>"
  apply (rule hoare_chain)
    apply (rule hoare_vcg_conj_lift)
     apply (rule getObject_obj_at' [OF x P])
    apply (rule getObject_inv)
    apply (subst x)
    apply (rule loadObject_default_inv)
   apply (clarsimp, assumption)
  apply clarsimp
  apply (drule(1) obj_at_valid_objs')
  apply (clarsimp simp: project_inject)
  done

declare fail_inv[simp]

lemma typeError_inv [wp]:
  "\<lbrace>P\<rbrace> typeError x y \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: typeError_def|wp)+

lemma getObject_cte_inv [wp]: "\<lbrace>P\<rbrace> (getObject addr :: cte kernel) \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: getObject_def loadObject_cte split_def)
  apply (clarsimp simp: valid_def in_monad)
  apply (clarsimp simp: typeError_def in_monad magnitudeCheck_def
                 split: kernel_object.split_asm if_split_asm option.split_asm)
  done

lemma getObject_ko_at:
  assumes x: "\<And>q n ko. loadObject p q n ko =
                (loadObject_default p q n ko :: ('a :: pspace_storable) kernel)"
  assumes P: "\<And>(v::'a::pspace_storable). (1 :: word32) < 2 ^ (objBits v)"
  shows      "\<lbrace> \<top> \<rbrace> getObject p \<lbrace>\<lambda>r::'a::pspace_storable. ko_at' r p\<rbrace>"
  by (subst eq_commute, rule getObject_obj_at' [OF x P])

lemma getObject_ko_at_tcb [wp]:
  "\<lbrace>\<top>\<rbrace> getObject p \<lbrace>\<lambda>rv::tcb. ko_at' rv p\<rbrace>"
  by (rule getObject_ko_at | simp add: objBits_simps')+

lemma OMG_getObject_tcb:
  "\<lbrace>obj_at' P t\<rbrace> getObject t \<lbrace>\<lambda>(tcb :: tcb) s. P tcb\<rbrace>"
  apply (rule obj_at_getObject)
  apply (clarsimp simp: loadObject_default_def in_monad projectKOs)
  done

lemma setObject_nosch:
  assumes x: "\<And>p q n ko. \<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> updateObject val p q n ko \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> setObject t val \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp x | simp)+
  done

lemma getObject_ep_inv: "\<lbrace>P\<rbrace> getObject addr :: endpoint kernel \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (rule getObject_inv)
  apply (simp add: loadObject_default_inv)
  done

lemma getObject_ntfn_inv:
  "\<lbrace>P\<rbrace> getObject addr :: Structures_H.notification kernel \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (rule getObject_inv)
  apply (simp add: loadObject_default_inv)
  done

lemma getObject_sc_inv: "\<lbrace>P\<rbrace> (getObject addr :: sched_context kernel) \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (rule getObject_inv)
  apply (simp add: loadObject_default_inv)
  done

lemma getObject_reply_inv: "\<lbrace>P\<rbrace> (getObject addr :: reply kernel) \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (rule getObject_inv)
  apply (simp add: loadObject_default_inv)
  done

lemma get_ep_inv'[wp]: "\<lbrace>P\<rbrace> getEndpoint ep \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: getEndpoint_def getObject_ep_inv)

lemma get_ntfn_inv'[wp]: "\<lbrace>P\<rbrace> getNotification ntfn \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: getNotification_def getObject_ntfn_inv)

lemma get_sc_inv': "\<lbrace>P\<rbrace> getSchedContext sc \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: getSchedContext_def getObject_sc_inv)

lemma get_reply_inv': "\<lbrace>P\<rbrace> getReply p \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: getReply_def getObject_reply_inv)

lemma get_ep_sp':
  "\<lbrace>P\<rbrace> getEndpoint r \<lbrace>\<lambda>t. P and ko_at' t r\<rbrace>"
  by (clarsimp simp: getEndpoint_def getObject_def loadObject_default_def
                     projectKOs in_monad valid_def obj_at'_def objBits_simps'
                     in_magnitude_check split_def)

lemma getEndpoint_wp:
  "\<lbrace>\<lambda>s. \<forall>ep. ko_at' ep e s \<longrightarrow> P ep s\<rbrace> getEndpoint e \<lbrace>P\<rbrace>"
  by (rule hoare_strengthen_post, rule get_ep_sp') simp

lemma get_ntfn_sp':
  "\<lbrace>P\<rbrace> getNotification r \<lbrace>\<lambda>t. P and ko_at' t r\<rbrace>"
  by (clarsimp simp: getNotification_def getObject_def loadObject_default_def
                     projectKOs in_monad valid_def obj_at'_def objBits_simps'
                     in_magnitude_check split_def)

lemma getNotification_wp:
  "\<lbrace>\<lambda>s. \<forall>ntfn. ko_at' ntfn e s \<longrightarrow> P ntfn s\<rbrace> getNotification e \<lbrace>P\<rbrace>"
  by (rule hoare_strengthen_post, rule get_ntfn_sp') simp

lemma get_sc_sp':
  "\<lbrace>P\<rbrace> getSchedContext p \<lbrace>\<lambda>t. P and ko_at' t p\<rbrace>"
  by (clarsimp simp: getSchedContext_def getObject_def loadObject_default_def
                     projectKOs in_monad valid_def obj_at'_def objBits_simps'
                     in_magnitude_check split_def)

lemma getSchedContext_wp[wp]:
  "\<lbrace>\<lambda>s. \<forall>ko. ko_at' ko p s \<longrightarrow> P ko s\<rbrace> getSchedContext p \<lbrace>P\<rbrace>"
  by (rule hoare_strengthen_post, rule get_sc_sp') simp

lemma get_reply_sp':
  "\<lbrace>P\<rbrace> getReply p \<lbrace>\<lambda>t. P and ko_at' t p\<rbrace>"
  by (clarsimp simp: getReply_def getObject_def loadObject_default_def
                     projectKOs in_monad valid_def obj_at'_def objBits_simps'
                     in_magnitude_check split_def)

lemma getReply_wp[wp]:
  "\<lbrace>\<lambda>s. \<forall>ko. ko_at' ko p s \<longrightarrow> P ko s\<rbrace> getReply p \<lbrace>P\<rbrace>"
  by (rule hoare_strengthen_post, rule get_reply_sp') simp

context
begin

private method getObject_valid_obj =
  rule hoare_chain,
  rule getObject_valid_obj; clarsimp simp: objBits_simps' valid_obj'_def

lemma get_ep'_valid_ep[wp]:
  "\<lbrace> invs' and ep_at' ep \<rbrace> getEndpoint ep \<lbrace> valid_ep' \<rbrace>"
  unfolding getEndpoint_def by getObject_valid_obj

lemma get_ntfn'_valid_ntfn[wp]:
  "\<lbrace> invs' and ntfn_at' ep \<rbrace> getNotification ep \<lbrace> valid_ntfn' \<rbrace>"
  unfolding getNotification_def by getObject_valid_obj

lemma get_sc_valid_sc'[wp]:
  "\<lbrace> invs' and sc_at' sc \<rbrace> getSchedContext sc \<lbrace> valid_sched_context' \<rbrace>"
  unfolding getSchedContext_def by getObject_valid_obj

lemma get_reply_valid_reply'[wp]:
  "\<lbrace> invs' and sc_at' sc \<rbrace> getReply sc \<lbrace> valid_reply' \<rbrace>"
  unfolding getReply_def by getObject_valid_obj

end

lemma get_ep_ko':
  "\<lbrace>\<top>\<rbrace> getEndpoint ep \<lbrace>\<lambda>rv. ko_at' rv ep\<rbrace>"
  unfolding getEndpoint_def
  by (rule getObject_ko_at; simp add: objBits_simps')

lemma get_ntfn_ko':
  "\<lbrace>\<top>\<rbrace> getNotification ntfn \<lbrace>\<lambda>rv. ko_at' rv ntfn\<rbrace>"
  unfolding getNotification_def
  by (rule getObject_ko_at; simp add: objBits_simps')

lemma get_sc_ko':
  "\<lbrace>\<top>\<rbrace> getSchedContext sc_ptr \<lbrace>\<lambda>sc. ko_at' sc sc_ptr\<rbrace>"
  unfolding getSchedContext_def
  by (rule getObject_ko_at; simp add: objBits_simps')

lemma get_reply_ko':
  "\<lbrace>\<top>\<rbrace> getReply reply_ptr \<lbrace>\<lambda>reply. ko_at' reply reply_ptr\<rbrace>"
  unfolding getReply_def
  by (rule getObject_ko_at; simp add: objBits_simps')

context
begin

private method unfold_setObject_inmonad =
  (clarsimp simp: setObject_def split_def valid_def in_monad projectKOs
                  objBits_def[symmetric] lookupAround2_char1 ps_clear_upd'
            split: if_split_asm
            dest!: updateObject_objBitsKO;
    fastforce dest: bspec[OF _ domI])

lemma setObject_distinct[wp]:
  "setObject p val \<lbrace>pspace_distinct'\<rbrace>"
  unfolding pspace_distinct'_def by unfold_setObject_inmonad

lemma setObject_aligned[wp]:
  "setObject p val \<lbrace>pspace_aligned'\<rbrace>"
  unfolding pspace_aligned'_def by unfold_setObject_inmonad

end

lemma pspace_dom_update:
  "\<lbrakk> ps ptr = Some x; a_type x = a_type v \<rbrakk> \<Longrightarrow> pspace_dom (ps(ptr \<mapsto> v)) = pspace_dom ps"
  apply (simp add: pspace_dom_def dom_fun_upd2 del: dom_fun_upd)
  apply (rule SUP_cong [OF refl])
  apply clarsimp
  apply (simp add: obj_relation_cuts_def3)
  done

lemmas ps_clear_def3 = ps_clear_def2 [OF order_less_imp_le [OF aligned_less_plus_1]]


declare diff_neg_mask[simp del]

lemma cte_wp_at_ctes_of:
  "cte_wp_at' P p s = (\<exists>cte. ctes_of s p = Some cte \<and> P cte)"
  apply (simp add: cte_wp_at_cases' map_to_ctes_def Let_def
                   cte_level_bits_def objBits_simps'
          split del: if_split)
  apply (safe del: disjCI)
    apply (clarsimp simp: ps_clear_def3 field_simps)
   apply (clarsimp simp: ps_clear_def3 field_simps
              split del: if_split)
   apply (frule is_aligned_sub_helper)
    apply (clarsimp simp: tcb_cte_cases_def split: if_split_asm)
   apply (case_tac "n = 0")
    apply (clarsimp simp: field_simps)
   apply (subgoal_tac "ksPSpace s p = None")
    apply clarsimp
    apply (clarsimp simp: field_simps)
   apply (elim conjE)
   apply (subst(asm) mask_in_range, assumption)
   apply (drule arg_cong[where f="\<lambda>S. p \<in> S"])
   apply (simp add: dom_def field_simps)
   apply (erule mp)
   apply (rule ccontr, simp add: linorder_not_le)
   apply (drule word_le_minus_one_leq)
   apply clarsimp
   apply (simp add: field_simps)
  apply (clarsimp split: if_split_asm del: disjCI)
   apply (simp add: ps_clear_def3 field_simps)
  apply (rule disjI2, rule exI[where x="(p - (p && ~~ mask 9))"])
  apply (clarsimp simp: ps_clear_def3[where na=9] is_aligned_mask
                        word_bw_assocs field_simps)
  done

lemma tcb_cte_cases_small:
  "\<lbrakk> tcb_cte_cases v = Some (getF, setF) \<rbrakk>
      \<Longrightarrow> v < 2 ^ tcbBlockSizeBits"
  by (simp add: tcb_cte_cases_def objBits_defs split: if_split_asm)

lemmas tcb_cte_cases_aligned_helpers =
    is_aligned_add_helper [OF _ tcb_cte_cases_small]
    is_aligned_sub_helper [OF _ tcb_cte_cases_small]

lemma ctes_of_from_cte_wp_at:
  assumes x: "\<And>P P' p. \<lbrace>\<lambda>s. P (cte_wp_at' P' p s) \<and> Q s\<rbrace> f \<lbrace>\<lambda>r s. P (cte_wp_at' P' p s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. P (ctes_of s) \<and> Q s\<rbrace> f \<lbrace>\<lambda>rv s. P (ctes_of s)\<rbrace>"
  apply (clarsimp simp: valid_def
                 elim!: rsubst[where P=P]
                intro!: ext)
  apply (case_tac "ctes_of s x", simp_all)
   apply (drule_tac P1=Not and P'1="\<top>" and p1=x in use_valid [OF _ x],
           simp_all add: cte_wp_at_ctes_of)
  apply (drule_tac P1=id and P'1="(=) aa" and p1=x in use_valid [OF _ x],
          simp_all add: cte_wp_at_ctes_of)
  done

lemmas setObject_ctes_of = ctes_of_from_cte_wp_at [OF setObject_cte_wp_at2']

lemma map_to_ctes_upd_cte:
  "\<lbrakk> s p = Some (KOCTE cte'); is_aligned p cte_level_bits;
     {p + 1..p + mask cte_level_bits} \<inter> dom s = {} \<rbrakk> \<Longrightarrow>
     map_to_ctes (s (p \<mapsto> (KOCTE cte))) = ((map_to_ctes s) (p \<mapsto> cte))"
  apply (rule ext)
  apply (simp    add: map_to_ctes_def Let_def dom_fun_upd2
           split del: if_split del: dom_fun_upd)
  apply (case_tac "x = p")
   apply (simp add: objBits_simps' cte_level_bits_def mask_def field_simps)
  apply (case_tac "(x && ~~ mask (objBitsKO (KOTCB undefined))) = p")
   apply clarsimp
  apply (simp del: dom_fun_upd split del: if_split cong: if_cong
              add: dom_fun_upd2 field_simps objBits_simps)
  done

declare overflow_plus_one_self[simp]

lemma map_to_ctes_upd_tcb:
  "\<lbrakk> s p = Some (KOTCB tcb'); is_aligned p tcbBlockSizeBits;
     {p + 1..p + mask tcbBlockSizeBits} \<inter> dom s = {} \<rbrakk> \<Longrightarrow>
     map_to_ctes (s (p \<mapsto> (KOTCB tcb))) =
      (\<lambda>x. if \<exists>getF setF. tcb_cte_cases (x - p) = Some (getF, setF)
                  \<and> getF tcb \<noteq> getF tcb'
           then (case tcb_cte_cases (x - p) of Some (getF, setF) \<Rightarrow> Some (getF tcb))
           else map_to_ctes s x)"
  supply
    is_aligned_neg_mask_eq[simp del]
    is_aligned_neg_mask_weaken[simp del]
  apply (subgoal_tac "p && ~~ (mask tcbBlockSizeBits) = p")
   apply (rule ext)
   apply (simp    add: map_to_ctes_def Let_def dom_fun_upd2
            split del: if_split del: dom_fun_upd
                 cong: option.case_cong if_cong)
   apply (case_tac "x = p")
    apply (simp add: objBits_simps' field_simps map_to_ctes_def mask_def)
   apply (case_tac "x && ~~ mask (objBitsKO (KOTCB undefined)) = p")
    apply (case_tac "tcb_cte_cases (x - p)")
     apply (simp split del: if_split cong: if_cong option.case_cong)
    apply (subgoal_tac "s x = None")
     apply (simp add: field_simps objBits_simps' split del: if_split
                cong: if_cong option.case_cong)
     apply (clarsimp simp: mask_def)
    apply (subst(asm) mask_in_range[where bits="objBitsKO v" for v])
     apply (simp add: objBitsKO_def)
    apply (drule_tac a=x in equals0D)
    apply (simp add: dom_def objBits_simps' mask_def field_simps)
    apply (erule mp)
    apply (rule ccontr, simp add: linorder_not_le)
    apply (drule word_le_minus_one_leq, simp)
   apply (case_tac "tcb_cte_cases (x - p)")
    apply (simp split del: if_split cong: if_cong option.case_cong)
   apply (rule FalseE)
   apply (subst(asm) mask_in_range[where bits="objBitsKO v" for v])
    apply (simp add: objBitsKO_def)
   apply (subgoal_tac "x - p < 2 ^ tcbBlockSizeBits")
    apply (frule word_le_minus_one_leq)
    apply (frule(1) is_aligned_no_wrap')
    apply (drule word_plus_mono_right[where x=p])
     apply (simp only: field_simps)
     apply (erule is_aligned_no_overflow)
    apply (simp add: objBits_simps field_simps)
   apply (clarsimp simp: tcb_cte_cases_def objBits_simps' field_simps
                  split: if_split_asm)
  apply (subst mask_in_range, assumption)
  apply (simp only: atLeastAtMost_iff order_refl simp_thms)
  apply (erule is_aligned_no_overflow)
  done

lemma map_to_ctes_upd_other:
  "\<lbrakk> s p = Some ko; case ko of KOTCB tcb \<Rightarrow> False | KOCTE cte \<Rightarrow> False | _ \<Rightarrow> True;
     case ko' of KOTCB tcb \<Rightarrow> False | KOCTE cte \<Rightarrow> False | _ \<Rightarrow> True \<rbrakk> \<Longrightarrow>
     map_to_ctes (s (p \<mapsto> ko')) = (map_to_ctes s)"
  apply (rule ext)
  apply (simp    add: map_to_ctes_def Let_def dom_fun_upd2
           split del: if_split del: dom_fun_upd
                cong: if_cong)
  apply (rule if_cong)
    apply clarsimp
    apply fastforce
   apply clarsimp
  apply (rule if_cong)
    apply clarsimp
    apply fastforce
   apply clarsimp
  apply (rule refl)
  done

lemma ctes_of_eq_cte_wp_at':
  "cte_wp_at' ((=) cte) x s \<Longrightarrow> ctes_of s x = Some cte"
  by (simp add: cte_wp_at_ctes_of)

lemma tcb_cte_cases_change:
  "tcb_cte_cases x = Some (getF, setF) \<Longrightarrow>
   (\<exists>getF. (\<exists>setF. tcb_cte_cases y = Some (getF, setF)) \<and> getF (setF f tcb) \<noteq> getF tcb)
     = (x = y \<and> f (getF tcb) \<noteq> getF tcb)"
  apply (rule iffI)
   apply (clarsimp simp: tcb_cte_cases_def split: if_split_asm)
  apply (clarsimp simp: tcb_cte_cases_def split: if_split_asm)
  done

lemma cte_level_bits_nonzero [simp]: "0 < cte_level_bits"
  by (simp add: cte_level_bits_def)

lemma ctes_of_setObject_cte:
  "\<lbrace>\<lambda>s. P ((ctes_of s) (p \<mapsto> cte))\<rbrace> setObject p (cte :: cte) \<lbrace>\<lambda>rv s. P (ctes_of s)\<rbrace>"
  apply (clarsimp simp: setObject_def split_def valid_def in_monad)
  apply (drule(1) updateObject_cte_is_tcb_or_cte[OF _ refl, rotated])
  apply (elim exE conjE disjE rsubst[where P=P])
   apply (clarsimp simp: lookupAround2_char1)
   apply (subst map_to_ctes_upd_tcb; assumption?)
    apply (clarsimp simp: mask_def objBits_defs field_simps ps_clear_def3)
   apply (clarsimp simp: tcb_cte_cases_change)
   apply (rule ext, clarsimp)
   apply (intro conjI impI)
    apply (clarsimp simp: tcb_cte_cases_def split: if_split_asm)
   apply (drule(1) cte_wp_at_tcbI'[where P="(=) cte"])
      apply (simp add: ps_clear_def3 field_simps)
     apply assumption+
   apply (simp add: cte_wp_at_ctes_of)
  apply (clarsimp simp: map_to_ctes_upd_cte ps_clear_def3 field_simps mask_def)
  done

declare foldl_True[simp]

lemma real_cte_at':
  "real_cte_at' p s \<Longrightarrow> cte_at' p s"
  by (clarsimp simp add: cte_wp_at_cases' obj_at'_def projectKOs
                         objBits_simps' cte_level_bits_def
                    del: disjCI)

lemma no_fail_getEndpoint [wp]:
  "no_fail (ep_at' ptr) (getEndpoint ptr)"
  apply (simp add: getEndpoint_def getObject_def
                   split_def)
  apply (rule no_fail_pre)
   apply wp
  apply (clarsimp simp add: obj_at'_def projectKOs objBits_simps'
                            lookupAround2_known1)
  apply (erule(1) ps_clear_lookupAround2)
    apply simp
   apply (simp add: field_simps)
   apply (erule is_aligned_no_wrap')
    apply (simp add: word_bits_conv)
   apply (clarsimp split: option.split_asm simp: objBits_simps' archObjSize_def)
  done

lemma get_ep_corres [corres]:
  "corres ep_relation (ep_at ptr) (ep_at' ptr)
     (get_endpoint ptr) (getEndpoint ptr)"
  apply (rule corres_no_failI)
   apply wp
  apply (simp add: get_simple_ko_def getEndpoint_def get_object_def
                   getObject_def bind_assoc ep_at_def2)
  apply (clarsimp simp: in_monad split_def bind_def gets_def get_def return_def)
  apply (clarsimp simp: assert_def fail_def obj_at_def return_def is_ep partial_inv_def)
  apply (clarsimp simp: loadObject_default_def in_monad projectKOs
                        in_magnitude_check objBits_simps')
  apply (clarsimp simp add: state_relation_def pspace_relation_def)
  apply (drule bspec)
   apply blast
  apply (simp add: other_obj_relation_def)
  done

declare magnitudeCheck_inv [wp]

declare alignCheck_inv [wp]

lemma setObject_ct_inv:
  "\<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace> setObject t (v::tcb) \<lbrace>\<lambda>rv s. P (ksCurThread s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setObject_cd_inv:
  "\<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> setObject t (v::tcb) \<lbrace>\<lambda>rv s. P (ksCurDomain s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setObject_it_inv:
"\<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace> setObject t (v::tcb) \<lbrace>\<lambda>rv s. P (ksIdleThread s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setObject_ksDomSchedule_inv:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace> setObject t (v::tcb) \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma projectKO_def2:
  "projectKO ko = assert_opt (projectKO_opt ko)"
  by (simp add: projectKO_def assert_opt_def)

lemma no_fail_magnitudeCheck[wp]:
  "no_fail (\<lambda>s. case y of None \<Rightarrow> True | Some z \<Rightarrow> 2 ^ n \<le> z - x)
    (magnitudeCheck x y n)"
  apply (clarsimp simp add: magnitudeCheck_def split: option.splits)
  apply (rule no_fail_pre, wp)
  apply simp
  done

lemma no_fail_setObject_other [wp]:
  fixes ob :: "'a :: pspace_storable"
  assumes x: "updateObject ob = updateObject_default ob"
  shows "no_fail (obj_at' (\<lambda>k::'a. objBits k = objBits ob) ptr)
                  (setObject ptr ob)"
  apply (simp add: setObject_def x split_def updateObject_default_def
                   projectKO_def2 alignCheck_def alignError_def)
  apply (rule no_fail_pre)
   apply (wp )
  apply (clarsimp simp: is_aligned_mask[symmetric] obj_at'_def
                        objBits_def[symmetric] projectKOs
                        project_inject lookupAround2_known1)
  apply (erule(1) ps_clear_lookupAround2)
    apply simp
   apply (erule is_aligned_get_word_bits)
    apply (subst add_diff_eq[symmetric])
    apply (erule is_aligned_no_wrap')
    apply simp
   apply simp
  apply fastforce
  done


lemma obj_relation_cut_same_type:
  "\<lbrakk> (y, P) \<in> obj_relation_cuts ko x; P ko z;
    (y', P') \<in> obj_relation_cuts ko' x'; P' ko' z \<rbrakk>
     \<Longrightarrow> (a_type ko = a_type ko') \<or> (\<exists>n n'. a_type ko = ACapTable n \<and> a_type ko' = ACapTable n')
         \<or> (\<exists>n n'. a_type ko = ASchedContext n \<and> a_type ko' = ASchedContext n')
         \<or> (\<exists>sz sz'. a_type ko = AArch (AUserData sz) \<and> a_type ko' = AArch (AUserData sz'))
         \<or> (\<exists>sz sz'. a_type ko = AArch (ADeviceData sz) \<and> a_type ko' = AArch (ADeviceData sz'))"
  apply (rule ccontr)
  apply (simp add: obj_relation_cuts_def2 a_type_def)
  apply (auto simp: other_obj_relation_def cte_relation_def
                    pte_relation_def pde_relation_def
             split: Structures_A.kernel_object.split_asm if_split_asm
                    Structures_H.kernel_object.split_asm
                    ARM_A.arch_kernel_obj.split_asm)
  done

definition exst_same :: "Structures_H.tcb \<Rightarrow> Structures_H.tcb \<Rightarrow> bool"  (* FIXME RT: probably needs updating *)
where
  "exst_same tcb tcb' \<equiv> tcbPriority tcb = tcbPriority tcb'
                      \<and> tcbDomain tcb = tcbDomain tcb'"

fun exst_same' :: "Structures_H.kernel_object \<Rightarrow> Structures_H.kernel_object \<Rightarrow> bool"
where
  "exst_same' (KOTCB tcb) (KOTCB tcb') = exst_same tcb tcb'" |
  "exst_same' _ _ = True"

lemma set_other_obj_corres:
  fixes ob' :: "'a :: pspace_storable"
  assumes x: "updateObject ob' = updateObject_default ob'"
  assumes z: "\<And>s. obj_at' P ptr s
               \<Longrightarrow> map_to_ctes ((ksPSpace s) (ptr \<mapsto> injectKO ob')) = map_to_ctes (ksPSpace s)"
  assumes t: "is_other_obj_relation_type (a_type ob)"
  assumes b: "\<And>ko. P ko \<Longrightarrow> objBits ko = objBits ob'"
  assumes e: "\<And>ko. P ko \<Longrightarrow> exst_same' (injectKO ko) (injectKO ob')"
  assumes P: "\<And>(v::'a::pspace_storable). (1 :: word32) < 2 ^ (objBits v)"
  shows      "other_obj_relation ob (injectKO (ob' :: 'a :: pspace_storable)) \<Longrightarrow>
  corres dc (obj_at (\<lambda>ko. a_type ko = a_type ob) ptr and obj_at (same_caps ob) ptr)
            (obj_at' (P :: 'a \<Rightarrow> bool) ptr)
            (set_object ptr ob) (setObject ptr ob')"
  supply image_cong_simp [cong del]
  apply (rule corres_no_failI)
   apply (rule no_fail_pre)
    apply wp
    apply (rule x)
   apply (clarsimp simp: b elim!: obj_at'_weakenE)
  apply (unfold set_object_def setObject_def)
  apply (clarsimp simp: in_monad split_def bind_def gets_def get_def Bex_def
                        put_def return_def modify_def get_object_def x
                        projectKOs obj_at_def
                        updateObject_default_def in_magnitude_check [OF _ P])
  apply (rename_tac ko)
  apply (clarsimp simp add: state_relation_def z)
  apply (clarsimp simp add: caps_of_state_after_update cte_wp_at_after_update
                            swp_def fun_upd_def obj_at_def)
  sorry (* FIXME RT
  apply (subst conj_assoc[symmetric])
  apply (rule conjI[rotated])
   apply (clarsimp simp add: ghost_relation_def)
   apply (erule_tac x=ptr in allE)+
   apply (clarsimp simp: obj_at_def a_type_def
                   split: Structures_A.kernel_object.splits if_split_asm)
   apply (simp split: arch_kernel_obj.splits if_splits)
  apply (fold fun_upd_def)
  apply (simp only: pspace_relation_def pspace_dom_update dom_fun_upd2 simp_thms)
  apply (elim conjE)
  apply (frule bspec, erule domI)
  apply (rule conjI)
   apply (rule ballI, drule(1) bspec)
   apply (drule domD)
   apply (clarsimp simp: is_other_obj_relation_type t)
   apply (drule(1) bspec)
   apply clarsimp
   apply (frule_tac ko'=ko and x'=ptr in obj_relation_cut_same_type,
           (fastforce simp add: is_other_obj_relation_type t)+)
   apply (erule disjE)
    apply (simp add: is_other_obj_relation_type t)
   apply (erule disjE)
    apply (insert t,
      clarsimp simp: is_other_obj_relation_type_CapTable a_type_def)
   apply (erule disjE)
    apply (insert t,
       clarsimp simp: is_other_obj_relation_type_UserData a_type_def)
   apply (insert t,
      clarsimp simp: is_other_obj_relation_type_DeviceData a_type_def)
  apply (simp only: ekheap_relation_def)
  apply (rule ballI, drule(1) bspec)
  apply (drule domD)
  apply (insert e)
  apply atomize
  apply (clarsimp simp: obj_at'_def)
  apply (erule_tac x=obj in allE)
  apply (clarsimp simp: projectKO_eq project_inject)
  apply (case_tac ob;
         simp_all add: a_type_def other_obj_relation_def etcb_relation_def
                       is_other_obj_relation_type t exst_same_def)
  by (clarsimp simp: is_other_obj_relation_type t exst_same_def
              split: Structures_A.kernel_object.splits Structures_H.kernel_object.splits
                     ARM_A.arch_kernel_obj.splits)+ *)

lemmas obj_at_simps = obj_at_def obj_at'_def projectKOs map_to_ctes_upd_other
                      is_other_obj_relation_type_def
                      a_type_def objBits_simps other_obj_relation_def
                      archObjSize_def pageBits_def

lemma set_ep_corres [corres]:
  "ep_relation e e' \<Longrightarrow>
  corres dc (ep_at ptr) (ep_at' ptr)
            (set_endpoint ptr e) (setEndpoint ptr e')"
  apply (simp add: set_simple_ko_def setEndpoint_def is_ep_def[symmetric])
    apply (corres_search search: set_other_obj_corres[where P="\<lambda>_. True"])
  apply (corressimp wp: get_object_ret get_object_wp)+
  by (fastforce simp: is_ep obj_at_simps objBits_defs partial_inv_def)

lemma set_ntfn_corres [corres]:
  "ntfn_relation ae ae' \<Longrightarrow>
  corres dc (ntfn_at ptr) (ntfn_at' ptr)
            (set_notification ptr ae) (setNotification ptr ae')"
  apply (simp add: set_simple_ko_def setNotification_def is_ntfn_def[symmetric])
       apply (corres_search search: set_other_obj_corres[where P="\<lambda>_. True"])
  apply (corressimp wp: get_object_ret get_object_wp)+
  by (fastforce simp: is_ntfn obj_at_simps objBits_defs partial_inv_def)

lemma no_fail_getNotification [wp]:
  "no_fail (ntfn_at' ptr) (getNotification ptr)"
  apply (simp add: getNotification_def getObject_def
                   split_def)
  apply (rule no_fail_pre)
   apply wp
  apply (clarsimp simp add: obj_at'_def projectKOs objBits_simps'
                            lookupAround2_known1)
  apply (erule(1) ps_clear_lookupAround2)
    apply simp
   apply (simp add: field_simps)
   apply (erule is_aligned_no_wrap')
    apply (simp add: word_bits_conv)
   apply (clarsimp split: option.split_asm simp: objBits_simps' archObjSize_def)
  done

lemma get_ntfn_corres:
  "corres ntfn_relation (ntfn_at ptr) (ntfn_at' ptr)
     (get_notification ptr) (getNotification ptr)"
  apply (rule corres_no_failI)
   apply wp
  apply (simp add: get_simple_ko_def getNotification_def get_object_def
                   getObject_def bind_assoc)
  apply (clarsimp simp: in_monad split_def bind_def gets_def get_def return_def)
  apply (clarsimp simp: assert_def fail_def obj_at_def return_def is_ntfn partial_inv_def)
  apply (clarsimp simp: loadObject_default_def in_monad projectKOs
                        in_magnitude_check objBits_simps')
  apply (clarsimp simp add: state_relation_def pspace_relation_def)
  apply (drule bspec)
   apply blast
  apply (simp add: other_obj_relation_def)
  done

lemma setObject_ko_wp_at:
  fixes v :: "'a :: pspace_storable"
  assumes R: "\<And>ko s y n. (updateObject v ko p y n s)
                   = (updateObject_default v ko p y n s)"
  assumes n: "\<And>v' :: 'a. objBits v' = n"
  assumes m: "(1 :: word32) < 2 ^ n"
  shows      "\<lbrace>\<lambda>s. obj_at' (\<lambda>x :: 'a. True) p s \<longrightarrow>
                    P (ko_wp_at' (if p = p' then K (P' (injectKO v)) else P')p' s)\<rbrace>
                setObject p v
              \<lbrace>\<lambda>rv s. P (ko_wp_at' P' p' s)\<rbrace>"
  apply (clarsimp simp: setObject_def valid_def in_monad
                        ko_wp_at'_def split_def
                        R updateObject_default_def
                        projectKOs obj_at'_real_def
             split del: if_split)
  apply (clarsimp simp: project_inject objBits_def[symmetric] n
                        in_magnitude_check [OF _ m]
                 elim!: rsubst[where P=P]
             split del: if_split)
  apply (rule iffI)
   apply (clarsimp simp: n ps_clear_upd' objBits_def[symmetric]
                  split: if_split_asm)
  apply (clarsimp simp: n project_inject objBits_def[symmetric]
                        ps_clear_upd'
                 split: if_split_asm)
  done

lemma typ_at'_valid_obj'_lift:
  assumes P: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at' T p s)\<rbrace>"
  notes [wp] = hoare_vcg_all_lift hoare_vcg_imp_lift' hoare_vcg_const_Ball_lift typ_at_lifts [OF P]
  shows      "\<lbrace>\<lambda>s. valid_obj' obj s\<rbrace> f \<lbrace>\<lambda>rv s. valid_obj' obj s\<rbrace>"
  apply (cases obj; simp add: valid_obj'_def hoare_TrueI)
        apply (rename_tac endpoint)
        apply (case_tac endpoint; simp add: valid_ep'_def, wp)
       apply (rename_tac notification)
       apply (case_tac "ntfnObj notification";
               simp add: valid_ntfn'_def valid_bound_tcb'_def split: option.splits,
               (wpsimp|rule conjI)+)
      apply (rename_tac tcb)
      apply (case_tac "tcbState tcb";
             simp add: valid_tcb'_def valid_tcb_state'_def split_def valid_bound_ntfn'_def
                split: option.splits, wpsimp)
     apply (wpsimp simp: valid_cte'_def)
    apply (rename_tac arch_kernel_object)
    apply (case_tac arch_kernel_object; wpsimp)
   apply (wpsimp simp: valid_sched_context'_def,
          clarsimp simp: valid_bound_ntfn'_def split: option.splits,
           wpsimp)
  apply (wpsimp simp: valid_reply'_def)
  done

lemmas setObject_valid_obj = typ_at'_valid_obj'_lift [OF setObject_typ_at']

lemma setObject_valid_objs':
  assumes x: "\<And>x n ko s ko' s'.
       \<lbrakk> (ko', s') \<in> fst (updateObject val ko ptr x n s); P s;
          valid_obj' ko s; lookupAround2 ptr (ksPSpace s) = (Some (x, ko), n) \<rbrakk>
           \<Longrightarrow> valid_obj' ko' s"
  shows "\<lbrace>valid_objs' and P\<rbrace> setObject ptr val \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (subgoal_tac "\<forall>ko. valid_obj' ko s \<longrightarrow> valid_obj' ko b")
   defer
   apply clarsimp
   apply (erule(1) use_valid [OF _ setObject_valid_obj])
  apply (clarsimp simp: setObject_def split_def in_monad
                        lookupAround2_char1)
  apply (simp add: valid_objs'_def)
  apply clarsimp
  apply (drule spec, erule mp)
  apply (drule(1) x)
    apply (simp add: ranI)
   apply (simp add: prod_eqI lookupAround2_char1)
  apply (clarsimp elim!: ranE split: if_split_asm simp: ranI)
  done

lemma setObject_iflive':
  fixes v :: "'a :: pspace_storable"
  assumes R: "\<And>ko s y n. (updateObject v ko ptr y n s)
                   = (updateObject_default v ko ptr y n s)"
  assumes n: "\<And>x :: 'a. objBits x = n"
  assumes m: "(1 :: word32) < 2 ^ n"
  assumes x: "\<And>x n tcb s t. \<lbrakk> t \<in> fst (updateObject v (KOTCB tcb) ptr x n s); P s;
                               lookupAround2 ptr (ksPSpace s) = (Some (x, KOTCB tcb), n) \<rbrakk>
                  \<Longrightarrow> \<exists>tcb'. t = (KOTCB tcb', s) \<and> (\<forall>(getF, setF) \<in> ran tcb_cte_cases. getF tcb' = getF tcb)"
  assumes y: "\<And>x n cte s. fst (updateObject v (KOCTE cte) ptr x n s) = {}"
  shows      "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s \<and> (live' (injectKO v) \<longrightarrow> ex_nonz_cap_to' ptr s) \<and> P s\<rbrace>
                setObject ptr v
              \<lbrace>\<lambda>rv s. if_live_then_nonz_cap' s\<rbrace>"
  unfolding if_live_then_nonz_cap'_def ex_nonz_cap_to'_def
  apply (rule hoare_pre)
   apply (simp only: imp_conv_disj)
   apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift)
    apply (rule setObject_ko_wp_at [OF R n m])
   apply (rule hoare_vcg_ex_lift)
   apply (rule setObject_cte_wp_at'[where Q = P, OF x y])
      apply assumption+
  apply clarsimp
  apply (clarsimp simp: ko_wp_at'_def)
  done

lemma setObject_qs[wp]:
  assumes x: "\<And>q n obj. \<lbrace>\<lambda>s. P (ksReadyQueues s)\<rbrace> updateObject v obj p q n \<lbrace>\<lambda>rv s. P (ksReadyQueues s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. P (ksReadyQueues s)\<rbrace> setObject p v \<lbrace>\<lambda>rv s. P (ksReadyQueues s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp x | simp)+
  done

lemma setObject_qsL1[wp]:
  assumes x: "\<And>q n obj. \<lbrace>\<lambda>s. P (ksReadyQueuesL1Bitmap s)\<rbrace> updateObject v obj p q n \<lbrace>\<lambda>rv s. P (ksReadyQueuesL1Bitmap s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. P (ksReadyQueuesL1Bitmap s)\<rbrace> setObject p v \<lbrace>\<lambda>rv s. P (ksReadyQueuesL1Bitmap s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp x | simp)+
  done

lemma setObject_qsL2[wp]:
  assumes x: "\<And>q n obj. \<lbrace>\<lambda>s. P (ksReadyQueuesL2Bitmap s)\<rbrace> updateObject v obj p q n \<lbrace>\<lambda>rv s. P (ksReadyQueuesL2Bitmap s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. P (ksReadyQueuesL2Bitmap s)\<rbrace> setObject p v \<lbrace>\<lambda>rv s. P (ksReadyQueuesL2Bitmap s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp x | simp)+
  done

lemma setObject_ifunsafe':
  fixes v :: "'a :: pspace_storable"
  assumes x: "\<And>x n tcb s t. \<lbrakk> t \<in> fst (updateObject v (KOTCB tcb) ptr x n s); P s;
                               lookupAround2 ptr (ksPSpace s) = (Some (x, KOTCB tcb), n) \<rbrakk>
                  \<Longrightarrow> \<exists>tcb'. t = (KOTCB tcb', s) \<and> (\<forall>(getF, setF) \<in> ran tcb_cte_cases. getF tcb' = getF tcb)"
  assumes y: "\<And>x n cte s. fst (updateObject v (KOCTE cte) ptr x n s) = {}"
  assumes z: "\<And>P. \<lbrace>\<lambda>s. P (intStateIRQNode (ksInterruptState s))\<rbrace>
                     setObject ptr v \<lbrace>\<lambda>rv s. P (intStateIRQNode (ksInterruptState s))\<rbrace>"
  shows      "\<lbrace>\<lambda>s. if_unsafe_then_cap' s \<and> P s\<rbrace>
                setObject ptr v
              \<lbrace>\<lambda>rv s. if_unsafe_then_cap' s\<rbrace>"
  apply (simp only: if_unsafe_then_cap'_def ex_cte_cap_to'_def
                    cte_wp_at_ctes_of)
  apply (rule hoare_use_eq_irq_node' [OF z])
  apply (rule setObject_ctes_of [OF x y], assumption+)
  done

lemma setObject_it[wp]:
  assumes x: "\<And>p q n ko. \<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace> updateObject val p q n ko \<lbrace>\<lambda>rv s. P (ksIdleThread s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace> setObject t val \<lbrace>\<lambda>rv s. P (ksIdleThread s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp x | simp)+
  done

lemma setObject_idle':
  fixes v :: "'a :: pspace_storable"
  assumes R: "\<And>ko s y n. (updateObject v ko ptr y n s)
                   = (updateObject_default v ko ptr y n s)"
  assumes n: "\<And>x :: 'a. objBits x = n"
  assumes m: "(1 :: word32) < 2 ^ n"
  assumes z: "\<And>P p q n ko.
       \<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace> updateObject v p q n ko
       \<lbrace>\<lambda>rv s. P (ksIdleThread s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. valid_idle' s \<and>
                   (ptr = ksIdleThread s \<longrightarrow>
                    (\<exists>obj (val :: 'a). projectKO_opt (injectKO val) = Some obj
                                      \<and> idle' (tcbState obj) \<and> tcbBoundNotification obj = None)
                    \<longrightarrow> (\<exists>obj. projectKO_opt (injectKO v) = Some obj \<and>
                          idle' (tcbState obj) \<and> tcbBoundNotification obj = None)) \<and>
                   P s\<rbrace>
                setObject ptr v
              \<lbrace>\<lambda>rv s. valid_idle' s\<rbrace>"
  apply (simp add: valid_idle'_def pred_tcb_at'_def o_def)
  apply (rule hoare_pre)
   apply (rule hoare_lift_Pf2 [where f="ksIdleThread"])
    apply (simp add: pred_tcb_at'_def obj_at'_real_def)
    sorry (* FIXME RT
    apply (rule setObject_ko_wp_at [OF R n m])
   apply (wp z)
  apply (clarsimp simp add: pred_tcb_at'_def obj_at'_real_def ko_wp_at'_def)
  apply (drule_tac x=obj in spec, simp)
  apply (clarsimp simp add: project_inject)
  apply (drule_tac x=obja in spec, simp)
  done *)
(* the conclusion should now be
  shows      "\<lbrace>\<lambda>s. valid_idle' s \<and>
                   (ptr = ksIdleThread s \<longrightarrow>
                    (\<exists>obj (val :: 'a). projectKO_opt (injectKO val) = Some obj
                                      \<and> idle' (tcbState obj) \<and> tcbBoundNotification obj = None
                                      \<and> tcbSchedContext obj = Some idle_sc_ptr \<and> tcbYieldTo obj = None)
                    \<longrightarrow> (\<exists>obj. projectKO_opt (injectKO v) = Some obj \<and>
                          idle' (tcbState obj) \<and> tcbBoundNotification obj = None
                          \<and> tcbSchedContext obj = Some idle_sc_ptr \<and> tcbYieldTo obj = None)) \<and>
                   P s\<rbrace>
                setObject ptr v
              \<lbrace>\<lambda>rv s. valid_idle' s\<rbrace>"
*)

lemma setObject_no_0_obj' [wp]:
  "\<lbrace>no_0_obj'\<rbrace> setObject p v \<lbrace>\<lambda>r. no_0_obj'\<rbrace>"
  apply (clarsimp simp: setObject_def split_def)
  apply (clarsimp simp: valid_def no_0_obj'_def ko_wp_at'_def in_monad
                        lookupAround2_char1 ps_clear_upd')
  done

lemma valid_updateCapDataI:
  "s \<turnstile>' c \<Longrightarrow> s \<turnstile>' updateCapData b x c"
  apply (unfold updateCapData_def Let_def ARM_H.updateCapData_def)
  apply (cases c)
  apply (simp_all add: isCap_defs valid_cap'_def capUntypedPtr_def isCap_simps
                       capAligned_def word_size word_bits_def word_bw_assocs)
  done

lemma no_fail_threadGet [wp]:
  "no_fail (tcb_at' t) (threadGet f t)"
  by (simp add: threadGet_def, wp)

lemma no_fail_getThreadState [wp]:
  "no_fail (tcb_at' t) (getThreadState t)"
  by (simp add: getThreadState_def, wp)

lemma no_fail_setObject_tcb [wp]:
  "no_fail (tcb_at' t) (setObject t (t'::tcb))"
  apply (rule no_fail_pre, wp)
   apply (rule ext)+
   apply simp
  apply (simp add: objBits_simps)
  done

lemma no_fail_threadSet [wp]:
  "no_fail (tcb_at' t) (threadSet f t)"
  apply (simp add: threadSet_def)
  apply (rule no_fail_pre, wp)
  apply simp
  done

lemma dmo_return' [simp]:
  "doMachineOp (return x) = return x"
  apply (simp add: doMachineOp_def select_f_def return_def gets_def get_def
                   bind_def modify_def put_def)
  done

lemma dmo_storeWordVM' [simp]:
  "doMachineOp (storeWordVM x y) = return ()"
  by (simp add: storeWordVM_def)

declare mapM_x_return [simp]

lemma no_fail_dmo' [wp]:
  "no_fail P f \<Longrightarrow> no_fail (P o ksMachineState) (doMachineOp f)"
  apply (simp add: doMachineOp_def split_def)
  apply (rule no_fail_pre, wp)
  apply simp
  apply (simp add: no_fail_def)
  done

lemma ct_in_state_thread_state_lift':
  assumes ct: "\<And>P. \<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksCurThread s)\<rbrace>"
  assumes st: "\<And>t. \<lbrace>st_tcb_at' P t\<rbrace> f \<lbrace>\<lambda>_. st_tcb_at' P t\<rbrace>"
  shows "\<lbrace>ct_in_state' P\<rbrace> f \<lbrace>\<lambda>_. ct_in_state' P\<rbrace>"
  apply (clarsimp simp: ct_in_state'_def)
  apply (clarsimp simp: valid_def)
  apply (frule (1) use_valid [OF _ ct])
  apply (drule (1) use_valid [OF _ st], assumption)
  done

lemma sch_act_wf_lift:
  assumes tcb: "\<And>P t. \<lbrace>st_tcb_at' P t\<rbrace> f \<lbrace>\<lambda>rv. st_tcb_at' P t\<rbrace>"
  assumes tcb_cd: "\<And>t. \<lbrace> tcb_in_cur_domain' t\<rbrace> f \<lbrace>\<lambda>_ . tcb_in_cur_domain' t \<rbrace>"
  assumes kCT: "\<And>P. \<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksCurThread s)\<rbrace>"
  assumes ksA: "\<And>P. \<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksSchedulerAction s)\<rbrace>"
  shows
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>
  f
  \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (frule (1) use_valid [OF _ ksA])
  apply (case_tac "ksSchedulerAction b", simp_all)
  apply (drule (2) use_valid [OF _ ct_in_state_thread_state_lift' [OF kCT tcb]])
  apply (clarsimp)
  apply (rule conjI)
  apply (drule (2) use_valid [OF _ tcb])
  apply (drule (2) use_valid [OF _ tcb_cd])
  done

lemma tcb_in_cur_domain'_lift:
  assumes a: "\<And>P. \<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksCurDomain s)\<rbrace>"
  assumes b: "\<And>x. \<lbrace>obj_at' (\<lambda>tcb. x = tcbDomain tcb) t\<rbrace> f \<lbrace>\<lambda>_. obj_at' (\<lambda>tcb. x = tcbDomain tcb) t\<rbrace>"
  shows "\<lbrace> tcb_in_cur_domain' t \<rbrace> f \<lbrace> \<lambda>_. tcb_in_cur_domain' t \<rbrace>"
  apply (simp add: tcb_in_cur_domain'_def)
  apply (rule_tac f="ksCurDomain" in  hoare_lift_Pf)
   apply (rule b)
  apply (rule a)
  done

lemma ct_idle_or_in_cur_domain'_lift:
  assumes a: "\<And>P. \<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace>       f \<lbrace>\<lambda>_ s. P (ksCurDomain s)\<rbrace>"
  assumes b: "\<And>P. \<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksSchedulerAction s)\<rbrace>"
  assumes c: "\<And>P. \<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace>      f \<lbrace>\<lambda>_ s. P (ksIdleThread s)\<rbrace>"
  assumes d: "\<And>P. \<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace>       f \<lbrace>\<lambda>_ s. P (ksCurThread s)\<rbrace>"
  assumes e: "\<And>d t t'. \<lbrace>\<lambda>s. t = t' \<or> obj_at' (\<lambda>tcb. d = tcbDomain tcb) t s\<rbrace>
                            f
                       \<lbrace>\<lambda>_ s. t = t' \<or> obj_at' (\<lambda>tcb. d = tcbDomain tcb) t s\<rbrace>"
  shows "\<lbrace> ct_idle_or_in_cur_domain' \<rbrace> f \<lbrace> \<lambda>_. ct_idle_or_in_cur_domain' \<rbrace>"
  apply (simp add: ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)
  apply (rule_tac f="ksCurThread" in  hoare_lift_Pf)
   apply (rule_tac f="ksIdleThread" in hoare_lift_Pf)
    apply (rule_tac f="ksSchedulerAction" in  hoare_lift_Pf)
     apply (rule_tac f="ksCurDomain" in  hoare_lift_Pf)
      apply (wp hoare_vcg_imp_lift)
       apply (rule e)
      apply simp
     apply (rule a)
    apply (rule b)
   apply (rule c)
  apply (rule d)
  done

lemmas cur_tcb_lift =
  hoare_lift_Pf [where f = ksCurThread and P = tcb_at', folded cur_tcb'_def]

lemma setObject_state_refs_of':
  assumes x: "updateObject val = updateObject_default val"
  assumes y: "(1 :: word32) < 2 ^ objBits val"
  shows
  "\<lbrace>\<lambda>s. P ((state_refs_of' s) (ptr := refs_of' (injectKO val)))\<rbrace>
     setObject ptr val
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  apply (clarsimp simp: setObject_def valid_def in_monad split_def
                        updateObject_default_def x in_magnitude_check
                        projectKOs y
                 elim!: rsubst[where P=P] intro!: ext
             split del: if_split cong: option.case_cong if_cong)
  apply (clarsimp simp: state_refs_of'_def objBits_def[symmetric]
                        ps_clear_upd'
                  cong: if_cong option.case_cong)
  done

lemma setObject_state_refs_of_eq:
  assumes x: "\<And>s s' obj obj' ptr' ptr''.
                  (obj', s') \<in> fst (updateObject val obj ptr ptr' ptr'' s)
                    \<Longrightarrow> refs_of' obj' = refs_of' obj"
  shows
  "\<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace>
     setObject ptr val
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  apply (clarsimp simp: setObject_def valid_def in_monad split_def
                        updateObject_default_def in_magnitude_check
                        projectKOs lookupAround2_char1
                 elim!: rsubst[where P=P] intro!: ext
             split del: if_split cong: option.case_cong if_cong)
  apply (frule x, drule updateObject_objBitsKO)
  apply (simp add: state_refs_of'_def ps_clear_upd'
             cong: option.case_cong if_cong)
  done

lemma ex_nonz_cap_to_pres':
  assumes y: "\<And>P p. \<lbrace>cte_wp_at' P p\<rbrace> f \<lbrace>\<lambda>rv. cte_wp_at' P p\<rbrace>"
  shows      "\<lbrace>ex_nonz_cap_to' p\<rbrace> f \<lbrace>\<lambda>rv. ex_nonz_cap_to' p\<rbrace>"
  apply (simp only: ex_nonz_cap_to'_def)
  apply (intro hoare_vcg_disj_lift hoare_vcg_ex_lift
               y hoare_vcg_all_lift)
  done

lemma valid_irq_handlers_lift':
  assumes x: "\<And>P. \<lbrace>\<lambda>s. P (cteCaps_of s)\<rbrace> f \<lbrace>\<lambda>rv s. P (cteCaps_of s)\<rbrace>"
  assumes y: "\<And>P. \<lbrace>\<lambda>s. P (ksInterruptState s)\<rbrace> f \<lbrace>\<lambda>rv s. P (ksInterruptState s)\<rbrace>"
  shows      "\<lbrace>valid_irq_handlers'\<rbrace> f \<lbrace>\<lambda>rv. valid_irq_handlers'\<rbrace>"
  apply (simp add: valid_irq_handlers'_def irq_issued'_def)
  apply (rule hoare_use_eq [where f=cteCaps_of, OF x y])
  done

lemmas valid_irq_handlers_lift'' = valid_irq_handlers_lift' [unfolded cteCaps_of_def]

lemma valid_global_refs_lift':
  assumes ctes: "\<And>P. \<lbrace>\<lambda>s. P (ctes_of s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ctes_of s)\<rbrace>"
  assumes arch: "\<And>P. \<lbrace>\<lambda>s. P (ksArchState s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksArchState s)\<rbrace>"
  assumes idle: "\<And>P. \<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksIdleThread s)\<rbrace>"
  assumes irqn: "\<And>P. \<lbrace>\<lambda>s. P (irq_node' s)\<rbrace> f \<lbrace>\<lambda>_ s. P (irq_node' s)\<rbrace>"
  assumes maxObj: "\<And>P. \<lbrace>\<lambda>s. P (gsMaxObjectSize s)\<rbrace> f \<lbrace>\<lambda>_ s. P (gsMaxObjectSize s)\<rbrace>"
  shows "\<lbrace>valid_global_refs'\<rbrace> f \<lbrace>\<lambda>_. valid_global_refs'\<rbrace>"
  apply (simp add: valid_global_refs'_def valid_refs'_def global_refs'_def valid_cap_sizes'_def)
  apply (rule hoare_lift_Pf [where f="ksArchState"])
   apply (rule hoare_lift_Pf [where f="ksIdleThread"])
    apply (rule hoare_lift_Pf [where f="irq_node'"])
     apply (rule hoare_lift_Pf [where f="gsMaxObjectSize"])
      apply (wp ctes hoare_vcg_const_Ball_lift arch idle irqn maxObj)+
  done

lemma valid_arch_state_lift':
  assumes typs: "\<And>T p P. \<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> f \<lbrace>\<lambda>_ s. P (typ_at' T p s)\<rbrace>"
  assumes arch: "\<And>P. \<lbrace>\<lambda>s. P (ksArchState s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksArchState s)\<rbrace>"
  shows "\<lbrace>valid_arch_state'\<rbrace> f \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  apply (simp add: valid_arch_state'_def valid_asid_table'_def
                   valid_global_pts'_def page_directory_at'_def
                   page_table_at'_def
                   All_less_Ball)
  apply (rule hoare_lift_Pf [where f="ksArchState"])
   apply (wp typs hoare_vcg_const_Ball_lift arch typ_at_lifts)+
  done

lemmas valid_irq_node_lift =
    hoare_use_eq_irq_node' [OF _ typ_at_lift_valid_irq_node']

lemmas untyped_ranges_zero_lift
    = hoare_use_eq[where f="gsUntypedZeroRanges"
        and Q="\<lambda>v s. untyped_ranges_zero_inv (f s) v" for f]

lemma valid_irq_states_lift':
  assumes x: "\<And>P. \<lbrace>\<lambda>s. P (intStateIRQTable (ksInterruptState s))\<rbrace> f \<lbrace>\<lambda>rv s. P (intStateIRQTable (ksInterruptState s))\<rbrace>"
  assumes y: "\<And>P. \<lbrace>\<lambda>s. P (irq_masks (ksMachineState s))\<rbrace> f \<lbrace>\<lambda>rv s. P (irq_masks (ksMachineState s))\<rbrace>"
  shows      "\<lbrace>valid_irq_states'\<rbrace> f \<lbrace>\<lambda>rv. valid_irq_states'\<rbrace>"
  apply (rule hoare_use_eq [where f="\<lambda>s. irq_masks (ksMachineState s)"], rule y)
  apply (rule hoare_use_eq [where f="\<lambda>s. intStateIRQTable (ksInterruptState s)"], rule x)
  apply wp
  done

lemma irqs_masked_lift:
  assumes "\<And>P. \<lbrace>\<lambda>s. P (intStateIRQTable (ksInterruptState s))\<rbrace> f
               \<lbrace>\<lambda>rv s. P (intStateIRQTable (ksInterruptState s))\<rbrace>"
  shows "\<lbrace>irqs_masked'\<rbrace> f \<lbrace>\<lambda>_. irqs_masked'\<rbrace>"
  apply (simp add: irqs_masked'_def)
  apply (wp assms)
  done

lemma setObject_pspace_domain_valid[wp]:
  "setObject ptr val \<lbrace>pspace_domain_valid\<rbrace>"
  by (fastforce simp: setObject_def split_def pspace_domain_valid_def valid_def in_monad
                      lookupAround2_char1
                dest: updateObject_objBitsKO
                split: if_split_asm)

lemma ct_not_inQ_lift:
  assumes sch_act: "\<And>P. \<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksSchedulerAction s)\<rbrace>"
      and not_inQ: "\<lbrace>\<lambda>s. obj_at' (Not \<circ> tcbQueued) (ksCurThread s) s\<rbrace>
                    f \<lbrace>\<lambda>_ s. obj_at' (Not \<circ> tcbQueued) (ksCurThread s) s\<rbrace>"
  shows "\<lbrace>ct_not_inQ\<rbrace> f \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  unfolding ct_not_inQ_def
  by (rule hoare_convert_imp [OF sch_act not_inQ])


end

context typ_at_props'
begin

lemmas valid_obj'[wp] = typ_at'_valid_obj'_lift[OF typ']

end

locale pspace_only' =
  fixes f :: "'a kernel"
  assumes pspace: "(rv, s') \<in> fst (f s) \<Longrightarrow> \<exists>g. s' = ksPSpace_update g s"
begin

lemma it[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace>"
  and ct[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace>"
  and cur_domain[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace>"
  and ksDomSchedule[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace>"
  and l1Bitmap[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksReadyQueuesL1Bitmap s)\<rbrace>"
  and l2Bitmap[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksReadyQueuesL2Bitmap s)\<rbrace>"
  and gsUserPages[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (gsUserPages s)\<rbrace>"
  and gsCNodes[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (gsCNodes s)\<rbrace>"
  and gsUntypedZeroRanges[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (gsUntypedZeroRanges s)\<rbrace>"
  and gsMaxObjectSize[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (gsMaxObjectSize s)\<rbrace>"
  and ksDomScheduleIdx[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksDomScheduleIdx s)\<rbrace>"
  and ksDomainTime[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksDomainTime s)\<rbrace>"
  and ksReadyQueues[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksReadyQueues s)\<rbrace>"
  and ksReleaseQueue[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksReleaseQueue s)\<rbrace>"
  and ksConsumedTime[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksConsumedTime s)\<rbrace>"
  and ksCurTime[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksCurTime s)\<rbrace>"
  and ksCurSc[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksCurSc s)\<rbrace>"
  and ksReprogramTimer[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksReprogramTimer s)\<rbrace>"
  and ksSchedulerAction[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace>"
  and ksInterruptState[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksInterruptState s)\<rbrace>"
  and ksWorkUnitsCompleted[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksWorkUnitsCompleted s)\<rbrace>"
  and ksArchState[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksArchState s)\<rbrace>"
  and ksMachineState[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksMachineState s)\<rbrace>"
  unfolding valid_def using pspace
  by (all \<open>fastforce\<close>)

end

locale simple_ko' =
  fixes f :: "obj_ref \<Rightarrow> 'a::pspace_storable \<Rightarrow> unit kernel"
  assumes f_def: "f p v = setObject p v"
  assumes default: "updateObject (v::'a) = updateObject_default (v::'a)"
  assumes not_tcb: "projectKO_opt (KOTCB tcb) = (None::'a option)"
  assumes not_cte: "projectKO_opt (KOCTE cte) = (None::'a option)"
  assumes objBits: "\<exists>n. \<forall>v. objBits (v::'a) = n \<and> (1::machine_word) < 2^n"
begin

lemma updateObject_tcb[simp]:
  "fst (updateObject (v::'a) (KOTCB tcb) p x n s) = {}"
  by (clarsimp simp: default updateObject_default_def in_monad projectKOs not_tcb bind_def)

lemma updateObject_cte[simp]:
  "fst (updateObject (v::'a) (KOCTE cte) p x n s) = {}"
  by (clarsimp simp: default updateObject_default_def in_monad projectKOs not_cte bind_def)

lemma cte_wp_at'[wp]: "f p v \<lbrace>\<lambda>s. P (cte_wp_at' Q p' s)\<rbrace>"
  unfolding f_def by (rule setObject_cte_wp_at2'[where Q="\<top>", simplified]; simp)

lemma ctes_of[wp]: "f p v \<lbrace>\<lambda>s. P (ctes_of s)\<rbrace>"
  unfolding f_def by (rule setObject_ctes_of[where Q="\<top>", simplified]; simp)

lemma valid_mdb'[wp]: "f p v \<lbrace>valid_mdb'\<rbrace>"
  unfolding valid_mdb'_def by wp

lemma pspace_aligned'[wp]: "f p v \<lbrace>pspace_aligned'\<rbrace>"
  and pspace_distinct'[wp]: "f p v \<lbrace>pspace_distinct'\<rbrace>"
  and no_0_obj'[wp]: "f p v \<lbrace>no_0_obj'\<rbrace>"
  unfolding f_def by (all \<open>wp\<close>)

lemma valid_objs':
  "\<lbrace>valid_objs' and valid_obj' (injectKO v) \<rbrace> f p v \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  unfolding f_def
  by (rule setObject_valid_objs')
     (clarsimp simp: default updateObject_default_def in_monad projectKOs)

lemma valid_pspace':
  "\<lbrace>valid_pspace' and valid_obj' (injectKO v) \<rbrace> f p v \<lbrace>\<lambda>_. valid_pspace'\<rbrace>"
  unfolding valid_pspace'_def by (wpsimp wp: valid_objs')

lemma not_inject_tcb[simp]:
  "injectKO (v::'a) \<noteq> KOTCB tcb"
  by (simp flip: project_inject add: projectKOs not_tcb)

lemma typeOf_not_tcb[simp]:
  "koTypeOf (injectKO (v::'a)) \<noteq> TCBT"
  by (cases "injectKO v"; simp)

lemma obj_at_tcb'[wp]:
  "f p v \<lbrace>\<lambda>s. P (obj_at' (Q :: tcb \<Rightarrow> bool) p' s)\<rbrace>"
  unfolding f_def obj_at'_real_def
  using objBits
  apply clarsimp
  apply (wp setObject_ko_wp_at; simp add: default)
  apply (clarsimp simp: obj_at'_def ko_wp_at'_def projectKOs)
  apply (case_tac ko; simp add: projectKOs not_tcb)
  done

lemma typ_at'[wp]:
  "f p v \<lbrace>\<lambda>s. P (typ_at' T p' s)\<rbrace>"
  unfolding f_def by (rule setObject_typ_at')

sublocale typ_at_props' "f p v" for p v by typ_at_props'

sublocale pspace_only' "f p v" for p v
  unfolding f_def
  by unfold_locales
     (fastforce simp: setObject_def updateObject_default_def magnitudeCheck_def default in_monad
                      split_def projectKOs
                split: option.splits)

lemma set_ep_valid_bitmapQ[wp]:
  "f p v \<lbrace> valid_bitmapQ \<rbrace>"
  unfolding bitmapQ_defs by (wpsimp wp: hoare_vcg_all_lift | wps)+

lemma bitmapQ_no_L1_orphans[wp]:
  "f p v \<lbrace> bitmapQ_no_L1_orphans \<rbrace>"
  unfolding bitmapQ_defs by (wpsimp wp: hoare_vcg_all_lift | wps)+

lemma bitmapQ_no_L2_orphans[wp]:
  "f p v \<lbrace> bitmapQ_no_L2_orphans \<rbrace>"
  unfolding bitmapQ_defs by (wpsimp wp: hoare_vcg_all_lift | wps)+

lemma valid_queues[wp]:
  "f p v \<lbrace> valid_queues \<rbrace>"
  unfolding valid_queues_def valid_queues_no_bitmap_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_ball_lift |wps)+
     (simp add: o_def pred_conj_def)

lemma set_ep_valid_queues'[wp]:
  "f p v \<lbrace>valid_queues'\<rbrace>"
  unfolding valid_queues'_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift)

lemma tcb_in_cur_domain'[wp]:
  "f p v \<lbrace>tcb_in_cur_domain' t\<rbrace>"
  by (rule tcb_in_cur_domain'_lift; wp)

lemma pred_tcb_at'[wp]:
  "f p v \<lbrace> \<lambda>s. Q (pred_tcb_at' proj P t s) \<rbrace>"
  unfolding pred_tcb_at'_def by wp

lemma sch_act_wf[wp]:
  "f p v \<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  by (wp sch_act_wf_lift)

lemma cur_tcb'[wp]:
  "f p v \<lbrace>cur_tcb'\<rbrace>"
  by (wp cur_tcb_lift)

lemma state_refs_of':
  "\<lbrace>\<lambda>s. P ((state_refs_of' s) (ptr := refs_of' (injectKO val)))\<rbrace>
   f ptr val
   \<lbrace>\<lambda>_ s. P (state_refs_of' s)\<rbrace>"
  unfolding f_def
  using objBits by (auto intro: setObject_state_refs_of' simp: default)

lemma cap_to'[wp]:
  "f p' v \<lbrace>ex_nonz_cap_to' p\<rbrace>"
  by (wp ex_nonz_cap_to_pres')

lemma ifunsafe'[wp]:
  "f p v \<lbrace>if_unsafe_then_cap'\<rbrace>"
  unfolding f_def
  apply (rule setObject_ifunsafe'[where P="\<top>", simplified])
    apply (clarsimp simp: default updateObject_default_def in_monad projectKOs not_tcb not_cte
                  intro!: equals0I)+
  apply (simp add: setObject_def split_def default)
  apply (wp updateObject_default_inv | simp)+
  done

lemmas irq_handlers[wp] = valid_irq_handlers_lift'' [OF ctes_of ksInterruptState]

lemma idle'[wp]:
  "f p v \<lbrace>valid_idle'\<rbrace>"
  unfolding f_def
  using objBits
  apply clarsimp
  apply (wp setObject_idle'[where P="\<top>"]; simp add: default objBits_simps' updateObject_default_inv)
  apply (clarsimp simp: projectKOs)
  done

lemma valid_arch_state'[wp]:
  "f p v \<lbrace> valid_arch_state' \<rbrace>"
  by (rule valid_arch_state_lift'; wp)

lemma valid_global_refs'[wp]:
  "f p v \<lbrace>valid_global_refs'\<rbrace>"
  by (rule valid_global_refs_lift'; wp)

lemmas valid_irq_node'[wp] = valid_irq_node_lift[OF ksInterruptState typ_at']
lemmas irq_states' [wp] = valid_irq_states_lift' [OF ksInterruptState ksMachineState]
lemmas irq_handlers'[wp] = valid_irq_handlers_lift'' [OF ctes_of ksInterruptState]
lemmas irqs_masked'[wp] = irqs_masked_lift[OF ksInterruptState]

lemma valid_machine_state'[wp]:
  "f p v \<lbrace>valid_machine_state'\<rbrace>"
  unfolding valid_machine_state'_def pointerInDeviceData_def pointerInUserData_def
  by (wp hoare_vcg_all_lift hoare_vcg_disj_lift)

lemma pspace_domain_valid[wp]:
  "f ptr val \<lbrace>pspace_domain_valid\<rbrace>"
  unfolding f_def by wp

lemmas x = ct_not_inQ_lift[OF ksSchedulerAction]

lemma ct_not_inQ[wp]:
  "f p v \<lbrace>ct_not_inQ\<rbrace>"
  apply (rule ct_not_inQ_lift, wp)
  apply (rule hoare_lift_Pf[where f=ksCurThread]; wp)
  done

lemma ct_idle_or_in_cur_domain'[wp]:
  "f p v \<lbrace> ct_idle_or_in_cur_domain' \<rbrace>"
  by (rule ct_idle_or_in_cur_domain'_lift; wp)

end

(* FIXME: should these be in Arch + sublocale instead? *)
interpretation set_ep': simple_ko' setEndpoint
  by unfold_locales (simp add: setEndpoint_def projectKO_opts_defs objBits_simps'|wp)+

interpretation set_ntfn': simple_ko' setNotification
  by unfold_locales (simp add: setNotification_def projectKO_opts_defs objBits_simps'|wp)+

interpretation set_reply': simple_ko' setReply
  by unfold_locales (simp add: setReply_def projectKO_opts_defs objBits_simps'|wp)+

interpretation set_sc': simple_ko' setSchedContext
  by unfold_locales (simp add: setSchedContext_def projectKO_opts_defs objBits_simps'|wp)+

interpretation tcb: pspace_only' "setObject p v" for v::tcb
  unfolding setObject_def
  by unfold_locales
     (fastforce simp: in_monad updateObject_default_def split_def magnitudeCheck_def projectKOs
                split: option.splits)

interpretation threadSet: pspace_only' "threadSet f p"
  unfolding threadSet_def
  apply unfold_locales
  apply (clarsimp simp: in_monad)
  apply (drule_tac P="(=) s" in use_valid[OF _ getObject_inv_tcb], rule refl)
  apply (fastforce dest:  tcb.pspace)
  done

context begin interpretation Arch . (*FIXME: arch_split*)

lemmas set_ep_valid_objs'[wp] =
  set_ep'.valid_objs'[simplified valid_obj'_def pred_conj_def, simplified]
lemmas set_ep_valid_pspace'[wp] =
  set_ep'.valid_pspace'[simplified valid_obj'_def pred_conj_def, simplified]

lemmas set_ntfn_valid_objs'[wp] =
  set_ntfn'.valid_objs'[simplified valid_obj'_def pred_conj_def, simplified]
lemmas set_ntfn_valid_pspace'[wp] =
  set_ntfn'.valid_pspace'[simplified valid_obj'_def pred_conj_def, simplified]

lemmas set_reply_valid_objs'[wp] =
  set_reply'.valid_objs'[simplified valid_obj'_def pred_conj_def, simplified]
lemmas set_reply_valid_pspace'[wp] =
  set_reply'.valid_pspace'[simplified valid_obj'_def pred_conj_def, simplified]

lemmas set_sc_valid_objs'[wp] =
  set_sc'.valid_objs'[simplified valid_obj'_def pred_conj_def, simplified]
lemmas set_sc_valid_pspace'[wp] =
  set_sc'.valid_pspace'[simplified valid_obj'_def pred_conj_def, simplified]


lemma set_ep_state_refs_of'[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of' s) (p := ep_q_refs_of' ep))\<rbrace>
     setEndpoint p ep
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  by (wp set_ep'.state_refs_of') (simp flip: fun_upd_def)

lemma set_ntfn_state_refs_of'[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of' s) (p := ntfn_q_refs_of' (ntfnObj ntfn) \<union>
                                    get_refs NTFNBound (ntfnBoundTCB ntfn) \<union>
                                    get_refs NTFNSchedContext (ntfnSc ntfn)))\<rbrace>
     setNotification p ntfn
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  by (wp set_ntfn'.state_refs_of') (simp flip: fun_upd_def)

lemma setSchedContext_state_refs_of'[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of' s)(p := get_refs SCNtfn (scNtfn sc) \<union>
                                   get_refs SCTcb (scTCB sc) \<union>
                                   get_refs SCYieldFrom (scYieldFrom sc) \<union>
                                   get_refs SCReply (scReply sc)))\<rbrace>
   setSchedContext p sc
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  by (wp set_sc'.state_refs_of') (simp flip: fun_upd_def)

lemma setReply_state_refs_of'[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of' s)(p := get_refs ReplySchedContext (replySc reply) \<union>
                                   get_refs ReplyTCB (replyTCB reply)))\<rbrace>
   setReply p reply
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  by (wp set_reply'.state_refs_of') (simp flip: fun_upd_def)

lemma setSchedContext_iflive'[wp]:
  "\<lbrace>if_live_then_nonz_cap' and ex_nonz_cap_to' p\<rbrace>
   setSchedContext p sc
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  unfolding setSchedContext_def
  by (wpsimp wp: setObject_iflive'[where P="\<top>"]
           simp: updateObject_default_def in_monad
                 projectKOs objBits_simps' bind_def
     |simp)+

lemma setReply_iflive'[wp]:
  "\<lbrace>if_live_then_nonz_cap' and ex_nonz_cap_to' p\<rbrace>
   setReply p reply
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  unfolding setReply_def
  by (wpsimp wp: setObject_iflive'[where P="\<top>"]
           simp: updateObject_default_def in_monad
                 projectKOs objBits_simps' bind_def
     |simp)+

lemma setEndpoint_iflive'[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s
      \<and> (v \<noteq> IdleEP \<longrightarrow> ex_nonz_cap_to' p s)\<rbrace>
   setEndpoint p v
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  unfolding setEndpoint_def
  by (wpsimp wp: setObject_iflive'[where P="\<top>"]
           simp: updateObject_default_def in_monad
                 projectKOs objBits_simps' bind_def
     |simp)+

lemma setReply_list_refs_of_replies'[wp]:
  "\<lbrace>\<lambda>s. P ((list_refs_of_replies' s)(p := list_refs_of_reply' reply))\<rbrace>
   setReply p reply
   \<lbrace>\<lambda>rv s. P (list_refs_of_replies' s)\<rbrace>"
  apply (wpsimp simp: setReply_def updateObject_default_def setObject_def split_def)
  apply (erule arg_cong[where f=P, THEN iffD1, rotated])
  apply (clarsimp simp: opt_map_def sym_refs_def fun_upd_def list_refs_of_reply'_def
                        map_set_def projectKO_opt_reply)
  apply (rule ext)
  apply (clarsimp simp: projectKO_opt_reply list_refs_of_reply'_def)
  done

lemma setObject_ksPSpace_only:
  "\<lbrakk> \<And>p q n ko. \<lbrace>P\<rbrace> updateObject val p q n ko \<lbrace>\<lambda>rv. P \<rbrace>;
        \<And>f s. P (ksPSpace_update f s) = P s \<rbrakk>
     \<Longrightarrow> \<lbrace>P\<rbrace> setObject ptr val \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp | simp | assumption)+
  done

lemma setObject_ksMachine:
  "\<lbrakk> \<And>p q n ko. \<lbrace>\<lambda>s. P (ksMachineState s)\<rbrace> updateObject val p q n ko \<lbrace>\<lambda>rv s. P (ksMachineState s)\<rbrace> \<rbrakk>
     \<Longrightarrow> \<lbrace>\<lambda>s. P (ksMachineState s)\<rbrace> setObject ptr val \<lbrace>\<lambda>rv s. P (ksMachineState s)\<rbrace>"
  by (simp add: setObject_ksPSpace_only)

lemma setObject_ksInterrupt:
  "\<lbrakk> \<And>p q n ko. \<lbrace>\<lambda>s. P (ksInterruptState s)\<rbrace> updateObject val p q n ko \<lbrace>\<lambda>rv s. P (ksInterruptState s)\<rbrace> \<rbrakk>
     \<Longrightarrow> \<lbrace>\<lambda>s. P (ksInterruptState s)\<rbrace> setObject ptr val \<lbrace>\<lambda>rv s. P (ksInterruptState s)\<rbrace>"
  by (simp add: setObject_ksPSpace_only)


lemma set_ntfn_iflive'[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s
      \<and> (live' (KONotification v) \<longrightarrow> ex_nonz_cap_to' p s)\<rbrace>
     setNotification p v
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: setNotification_def)
  apply (wp setObject_iflive'[where P="\<top>"])
       apply simp
      apply (simp add: objBits_simps)
     apply (simp add: objBits_simps')
    apply (clarsimp simp: updateObject_default_def in_monad projectKOs)
   apply (clarsimp simp: updateObject_default_def
                         projectKOs bind_def)
  apply clarsimp
  done

lemma valid_pde_mappings'_def2:
  "valid_pde_mappings' =
     (\<lambda>s. \<forall>x. pde_at' x s \<longrightarrow> obj_at' (valid_pde_mapping' (x && mask pdBits)) x s)"
  apply (clarsimp simp: valid_pde_mappings'_def typ_at_to_obj_at_arches)
  apply (rule ext, rule iff_allI)
  apply (clarsimp simp: obj_at'_def projectKOs)
  apply (auto simp add: objBits_simps archObjSize_def)
  done

lemma valid_pde_mappings_lift':
  assumes x: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at' T p s)\<rbrace>"
  assumes y: "\<And>x. \<lbrace>obj_at' (valid_pde_mapping' (x && mask pdBits)) x\<rbrace>
                    f \<lbrace>\<lambda>rv. obj_at' (valid_pde_mapping' (x && mask pdBits)) x\<rbrace>"
  shows      "\<lbrace>valid_pde_mappings'\<rbrace> f \<lbrace>\<lambda>rv. valid_pde_mappings'\<rbrace>"
  apply (simp only: valid_pde_mappings'_def2 imp_conv_disj)
  apply (rule hoare_vcg_all_lift hoare_vcg_disj_lift x y)+
  done

lemma set_ntfn_valid_pde_mappings'[wp]:
  "\<lbrace>valid_pde_mappings'\<rbrace> setNotification ptr val \<lbrace>\<lambda>rv. valid_pde_mappings'\<rbrace>"
  apply (rule valid_pde_mappings_lift')
   apply wp
  apply (simp add: setNotification_def)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp: updateObject_default_def in_monad)
  done

lemma set_ntfn_minor_invs': (* FIXME RT: needs statement update *)
  "\<lbrace>invs' and obj_at' (\<lambda>ntfn. ntfn_q_refs_of' (ntfnObj ntfn) = ntfn_q_refs_of' (ntfnObj val)
                           \<and> ntfn_bound_refs' (ntfnBoundTCB ntfn) = ntfn_bound_refs' (ntfnBoundTCB val))
                       ptr
         and valid_ntfn' val
         and (\<lambda>s. live' (KONotification val) \<longrightarrow> ex_nonz_cap_to' ptr s)
         and (\<lambda>s. ptr \<noteq> ksIdleThread s) \<rbrace>
     setNotification ptr val
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (clarsimp simp add: invs'_def valid_state'_def cteCaps_of_def)
  apply (wp irqs_masked_lift valid_irq_node_lift untyped_ranges_zero_lift,
            simp_all add: o_def)
  sorry (* FIXME RT: replies_of' preservation
  apply (clarsimp elim!: rsubst[where P=sym_refs]
                 intro!: ext
                  dest!: obj_at_state_refs_ofD')+
  *)


lemma ep_redux_simps':
  "ep_q_refs_of' (case xs of [] \<Rightarrow> IdleEP | y # ys \<Rightarrow> SendEP xs)
        = (set xs \<times> {EPSend})"
  "ep_q_refs_of' (case xs of [] \<Rightarrow> IdleEP | y # ys \<Rightarrow> RecvEP xs)
        = (set xs \<times> {EPRecv})"
  "ntfn_q_refs_of' (case xs of [] \<Rightarrow> IdleNtfn | y # ys \<Rightarrow> WaitingNtfn xs)
        = (set xs \<times> {NTFNSignal})"
  by (fastforce split: list.splits
                simp: valid_ep_def valid_ntfn_def)+


(* There are two wp rules for preserving valid_ioc over set_object.
   First, the more involved rule for CNodes and TCBs *)
(* Second, the simpler rule suitable for all objects except CNodes and TCBs. *)
lemma valid_refs'_def2:
  "valid_refs' R (ctes_of s) = (\<forall>cref. \<not>cte_wp_at' (\<lambda>c. R \<inter> capRange (cteCap c) \<noteq> {}) cref s)"
  by (auto simp: valid_refs'_def cte_wp_at_ctes_of ran_def)

lemma idle_is_global [intro!]:
  "ksIdleThread s \<in> global_refs' s"
  by (simp add: global_refs'_def)

lemma valid_globals_cte_wpD':
  "\<lbrakk> valid_global_refs' s; cte_wp_at' P p s \<rbrakk>
       \<Longrightarrow> \<exists>cte. P cte \<and> ksIdleThread s \<notin> capRange (cteCap cte)"
  by (fastforce simp: valid_global_refs'_def valid_refs'_def  cte_wp_at_ctes_of)

lemma dmo_aligned'[wp]:
  "\<lbrace>pspace_aligned'\<rbrace> doMachineOp f \<lbrace>\<lambda>_. pspace_aligned'\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply (wp select_wp)
  apply clarsimp
  done

lemma dmo_distinct'[wp]:
  "\<lbrace>pspace_distinct'\<rbrace> doMachineOp f \<lbrace>\<lambda>_. pspace_distinct'\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply (wp select_wp)
  apply clarsimp
  done

lemma dmo_valid_objs'[wp]:
  "\<lbrace>valid_objs'\<rbrace> doMachineOp f \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply (wp select_wp)
  apply clarsimp
  done

lemma dmo_inv':
  assumes R: "\<And>P. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. P\<rbrace>"
  shows "\<lbrace>P\<rbrace> doMachineOp f \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply (wp select_wp)
  apply clarsimp
  apply (drule in_inv_by_hoareD [OF R])
  apply simp
  done

crunch cte_wp_at'2[wp]: doMachineOp "\<lambda>s. P (cte_wp_at' P' p s)"

crunch typ_at'[wp]: doMachineOp "\<lambda>s. P (typ_at' T p s)"

lemmas doMachineOp_typ_ats[wp] = typ_at_lifts [OF doMachineOp_typ_at']

lemma doMachineOp_invs_bits[wp]:
  "\<lbrace>valid_pspace'\<rbrace> doMachineOp m \<lbrace>\<lambda>rv. valid_pspace'\<rbrace>"
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>
     doMachineOp m \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  "\<lbrace>Invariants_H.valid_queues\<rbrace> doMachineOp m \<lbrace>\<lambda>rv. Invariants_H.valid_queues\<rbrace>"
  "\<lbrace>valid_queues'\<rbrace> doMachineOp m \<lbrace>\<lambda>rv. valid_queues'\<rbrace>"
  "\<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace>
      doMachineOp m
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  "\<lbrace>if_live_then_nonz_cap'\<rbrace> doMachineOp m \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  "\<lbrace>cur_tcb'\<rbrace> doMachineOp m \<lbrace>\<lambda>rv. cur_tcb'\<rbrace>"
  "\<lbrace>if_unsafe_then_cap'\<rbrace> doMachineOp m \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  by (simp add: doMachineOp_def split_def
                valid_pspace'_def valid_queues_def valid_queues_no_bitmap_def bitmapQ_defs
       | wp cur_tcb_lift sch_act_wf_lift tcb_in_cur_domain'_lift
       | fastforce elim: state_refs_of'_pspaceI)+

crunch obj_at'[wp]: doMachineOp "\<lambda>s. P (obj_at' P' p s)"

crunch it[wp]: doMachineOp "\<lambda>s. P (ksIdleThread s)"
crunch idle'[wp]: doMachineOp "valid_idle'"
  (wp: crunch_wps simp: crunch_simps valid_idle'_pspace_itI)
crunch pde_mappings'[wp]: doMachineOp "valid_pde_mappings'"

end
end
