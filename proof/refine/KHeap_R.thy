(*
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2022, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory KHeap_R
imports
  ArchMachine_R ArchHeapStateRelationLemmas
begin

(* requalify interface lemmas which can't be locale assumptions due to free type variable *)
arch_requalify_facts
  aobjs_relation_lift_rcorres
  heap_ghost_relation_lift_rcorres

lemmas [rcorres_lift] = aobjs_relation_lift_rcorres

lemmas [rcorres_lift] = heap_ghost_relation_lift_rcorres

translations
  (type) "'a kernel" <=(type) "kernel_state \<Rightarrow> ('a \<times> kernel_state) set \<times> bool"

lemmas [simp] = fromPPtr_def PPtr_def

lemma obj_at_replyTCBs_of:
  "obj_at' (\<lambda>reply. replyTCB reply = tptr_opt) rptr s
   \<Longrightarrow> replyTCBs_of s rptr = tptr_opt"
  by (clarsimp simp: obj_at'_def opt_map_def)

abbreviation valid_replies'_alt :: "kernel_state \<Rightarrow> bool" where
  "valid_replies'_alt s \<equiv>
     (\<forall>rptr rp. ko_at' rp rptr s \<and> ((\<exists>rp'. replyNext rp = Some (Next rp')) \<or> replyPrev rp \<noteq> None)
                \<longrightarrow> (\<exists>tptr. replyTCB rp = Some tptr
                            \<and> st_tcb_at' ((=) (BlockedOnReply (Some rptr))) tptr s))"

lemma valid_replies'_def2:
  "pspace_distinct' s \<Longrightarrow> pspace_aligned' s \<Longrightarrow>
   valid_replies' s = valid_replies'_alt s"
  unfolding valid_replies'_def
  apply (rule iffI; clarsimp simp: obj_at'_def valid_sz_simps)
   apply (drule_tac x=rptr in spec, clarsimp simp: opt_map_def)
  apply (clarsimp simp: pspace_alignedD' pspace_distinctD' opt_map_def
                  split: option.splits)
  done

primrec same_caps' :: "kernel_object \<Rightarrow> kernel_object \<Rightarrow> bool" where
  "same_caps' val (KOTCB tcb) = (\<exists>tcb'. val = KOTCB tcb' \<and>
                                        (\<forall>(getF, t) \<in> ran tcb_cte_cases. getF tcb' = getF tcb))"
| "same_caps' val (KOCTE cte) = (val = KOCTE cte)"
| "same_caps' val (KOEndpoint ep) = (\<exists>ep'. val = KOEndpoint ep')"
| "same_caps' val (KONotification ntfn) = (\<exists>ntfn'. val = KONotification ntfn')"
| "same_caps' val (KOKernelData) = (val = KOKernelData)"
| "same_caps' val (KOUserData) = (val = KOUserData)"
| "same_caps' val (KOUserDataDevice) = (val = KOUserDataDevice)"
| "same_caps' val (KOArch ao) = (\<exists>ao'. val = KOArch ao')"
| "same_caps' val (KOSchedContext sc) = (\<exists>sc'. val = KOSchedContext sc')"
| "same_caps' val (KOReply r) = (\<exists>r'. val = KOReply r')"

lemma same_caps'_more_simps[simp]:
  "same_caps' (KOTCB tcb) val = (\<exists>tcb'. val = KOTCB tcb' \<and>
                                        (\<forall>(getF, t) \<in> ran tcb_cte_cases. getF tcb' = getF tcb))"
  "same_caps' (KOCTE cte) val = (val = KOCTE cte)"
  "same_caps' (KOEndpoint ep) val = (\<exists>ep'. val = KOEndpoint ep')"
  "same_caps' (KONotification ntfn) val = (\<exists>ntfn'. val = KONotification ntfn')"
  "same_caps' (KOKernelData) val = (val = KOKernelData)"
  "same_caps' (KOUserData) val = (val = KOUserData)"
  "same_caps' (KOUserDataDevice) val = (val = KOUserDataDevice)"
  "same_caps' (KOArch ao) val = (\<exists>ao'. val = KOArch ao')"
  "same_caps' (KOSchedContext sc) val = (\<exists>sc'. val = KOSchedContext sc')"
  "same_caps' (KOReply r) val = (\<exists>r'. val = KOReply r')"
  by (cases val; fastforce)+

lemma lookupAround2_known1:
  "m x = Some y \<Longrightarrow> fst (lookupAround2 x m) = Some (x, y)"
  by (fastforce simp: lookupAround2_char1)

abbreviation (input) set_ko' :: "machine_word \<Rightarrow> kernel_object \<Rightarrow> kernel_state \<Rightarrow> kernel_state" where
  "set_ko' ptr ko s \<equiv> s\<lparr>ksPSpace := (ksPSpace s)(ptr := Some ko)\<rparr>"

abbreviation (input) set_obj' ::
  "machine_word \<Rightarrow> ('a :: pspace_storable) \<Rightarrow> kernel_state \<Rightarrow> kernel_state"
  where
  "set_obj' ptr obj s \<equiv> set_ko' ptr (injectKO obj) s"

lemma koTypeOf_injectKO:
  fixes v :: "'a :: pspace_storable"
  shows "koTypeOf (injectKO v) = koType TYPE('a)"
  apply (cut_tac v1=v in iffD2 [OF project_inject, OF refl])
  apply (simp add: project_koType[symmetric])
  done

lemma typ_at_to_obj_at':
  "typ_at' (koType (TYPE ('a :: pspace_storable))) p s
     = obj_at' (\<top> :: 'a \<Rightarrow> bool) p s"
  by (simp add: typ_at'_def obj_at'_real_def project_koType[symmetric])

lemma setObject_modify_variable_size:
  "\<lbrakk>obj_at' (P :: 'a \<Rightarrow> bool) p s; updateObject v = updateObject_default v;
    (1 :: machine_word) < 2 ^ objBits v; obj_at' (\<lambda>obj. objBits v = objBits obj) p s\<rbrakk>
   \<Longrightarrow> setObject p v s = modify (ksPSpace_update (\<lambda>ps. ps (p \<mapsto> injectKO v))) s"
  for v :: "'a :: pspace_storable"
  apply (clarsimp simp: setObject_def split_def exec_gets obj_at'_def lookupAround2_known1
                        assert_opt_def updateObject_default_def bind_assoc)
  apply (simp add: projectKO_def alignCheck_assert)
  apply (simp add: project_inject objBits_def)
  apply (clarsimp simp only: koTypeOf_injectKO)
  apply (frule in_magnitude_check[where s'=s])
    apply (simp add: objBits_pos_power2[simplified objBits_def])
   apply fastforce
  apply (simp add: magnitudeCheck_assert in_monad bind_def gets_def oassert_opt_def
                   get_def return_def)
  apply (simp add: simpler_modify_def)
  done

lemma setObject_modify_variable_size_rewrite:
  fixes v :: "'a :: pspace_storable"
  assumes "updateObject v = updateObject_default v"
  assumes "(1 :: machine_word) < 2 ^ objBits v"
  shows "monadic_rewrite False True
           (obj_at' (P :: 'a \<Rightarrow> bool) p and obj_at' (\<lambda>obj. objBits v = objBits obj) p)
           (setObject p v) (modify (ksPSpace_update (\<lambda>ps. ps (p \<mapsto> injectKO v))))"
  using assms
  by (fastforce intro: setObject_modify_variable_size simp: monadic_rewrite_def obj_at'_def)

lemma setObject_default_wp:
  "\<lbrakk> updateObject v = updateObject_default v; (1 :: machine_word) < 2 ^ objBits v \<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s. obj_at' (\<lambda>obj::'a. objBits v = objBits obj) p s \<and>
        Q () (ksPSpace_update (\<lambda>ps. ps(p \<mapsto> injectKO v)) s)\<rbrace>
   setObject p v
   \<lbrace>Q\<rbrace>"
  for v :: "'a :: pspace_storable"
  by (clarsimp simp: valid_def simpler_modify_def
                     setObject_modify_variable_size[where P="\<lambda>ko. objBits v = objBits ko"])

lemma setObject_modify:
  "\<lbrakk>obj_at' (P :: 'a \<Rightarrow> bool) p s; updateObject v = updateObject_default v;
    (1 :: machine_word) < 2 ^ objBits v; \<And>ko. P ko \<Longrightarrow> objBits ko = objBits v \<rbrakk>
   \<Longrightarrow> setObject p v s = modify (ksPSpace_update (\<lambda>ps. ps (p \<mapsto> injectKO v))) s"
  for v :: "'a :: pspace_storable"
  apply (rule setObject_modify_variable_size)
     apply fastforce
    apply fastforce
  apply fastforce
  unfolding obj_at'_def
  by fastforce

lemma setObject_modify_rewrite:
  fixes v :: "'a :: pspace_storable"
  assumes "updateObject v = updateObject_default v"
  assumes "(1 :: machine_word) < 2 ^ objBits v"
  assumes "\<And>ko. P ko \<Longrightarrow> objBits ko = objBits v"
  shows "monadic_rewrite False True
           (obj_at' (P :: 'a \<Rightarrow> bool) p)
           (setObject p v) (modify (ksPSpace_update (\<lambda>ps. ps (p \<mapsto> injectKO v))))"
  using assms
  by (fastforce intro: setObject_modify_variable_size simp: monadic_rewrite_def obj_at'_def)

lemma ovalid_readObject[wp]:
  assumes R:
  "\<And>a n ko s obj::'a::pspace_storable.
  \<lbrakk> loadObject t t n ko s = Some a; projectKO_opt ko = Some obj \<rbrakk> \<Longrightarrow> a = obj"
  shows "ovalid (obj_at' P t) (readObject t) (\<lambda>(rv::'a::pspace_storable) _. P rv)"
  by (auto simp: obj_at'_def readObject_def split_def omonad_defs obind_def
                 lookupAround2_known1 ovalid_def
           dest: R)

definition isArchT :: "kernel_object_type \<Rightarrow> bool" where
  "isArchT T \<equiv> case T of ArchT _ \<Rightarrow> True | _ \<Rightarrow> False"

lemmas isArchT_simps[simp] = isArchT_def[split_simps kernel_object_type.split]

lemma isArchT_eq:
  "isArchT T = (\<exists>T'. T = ArchT T')"
  by (cases T; simp)

lemma isArch_koTypeOf_aobj_of':
  "(\<not>isArchT (koTypeOf ko)) = (aobj_of' ko = None)"
  by (cases ko; simp)

lemma typ_at_aobjs_of'_None:
  "\<lbrakk> typ_at' T p s; \<not>isArchT T \<rbrakk> \<Longrightarrow> aobjs_of' s p = None"
  unfolding typ_at'_def ko_wp_at'_def
  by (clarsimp simp: isArch_koTypeOf_aobj_of' opt_map_def)

lemma obj_at_getObject:
  assumes R:
  "\<And>a n ko s obj::'a::pspace_storable.
  \<lbrakk> loadObject t t n ko s = Some a; projectKO_opt ko = Some obj \<rbrakk> \<Longrightarrow> a = obj"
  shows "\<lbrace>obj_at' P t\<rbrace> getObject t \<lbrace>\<lambda>(rv::'a::pspace_storable) s. P rv\<rbrace>"
  unfolding getObject_def
  apply wpsimp
  using R use_ovalid[OF ovalid_readObject] by blast

declare projectKO_inv[wp]

lemma getObject_inv:
  "\<lbrace>P\<rbrace> getObject p \<lbrace>\<lambda>(rv :: 'a :: pspace_storable). P\<rbrace>"
  unfolding getObject_def by wpsimp

lemma getObject_tcb_inv[wp]:
  "\<lbrace>P\<rbrace> getObject l \<lbrace>\<lambda>(_ :: Structures_H.tcb). P\<rbrace>"
  by (rule getObject_inv)

lemma loadObject_default_Some[simp, intro!]:
  "\<lbrakk>projectKO_opt ko = Some (obj::'a);
                      is_aligned p (objBits obj); objBits obj < word_bits;
                      case_option True (\<lambda>x. 2 ^ (objBits obj) \<le> x - p) n; q = p\<rbrakk>
       \<Longrightarrow> bound (loadObject_default p q n ko s:: ('a::pre_storable) option)"
  by (clarsimp simp: loadObject_default_def split_def projectKO_def obind_def
                     alignCheck_def alignError_def magnitudeCheck_def
                     read_alignCheck_def read_alignError_def read_magnitudeCheck_def
                     unless_def gets_the_def is_aligned_mask omonad_defs
              split: option.splits) simp

lemmas loadObject_default_Some''[simp, intro!]
        = loadObject_default_Some[where p=p and s=s and n="snd (lookupAround2 p (ksPSpace s))" for p s,
                                 simplified]

lemma no_ofail_loadObject_default [simp]:
  "no_ofail (\<lambda>s. \<exists>obj. projectKO_opt ko = Some (obj::'a) \<and> objBits obj < word_bits \<and>
                      is_aligned p (objBits obj) \<and> q = p
                      \<and> case_option True (\<lambda>x. 2 ^ (objBits obj) \<le> x - p) n)
           (loadObject_default p q n ko :: ('a::pre_storable) kernel_r)"
  by (clarsimp simp: no_ofail_def)

method no_ofail_readObject_method =
  clarsimp simp: obj_at'_def readObject_def obind_def omonad_defs split_def no_ofail_def,
  rule ps_clear_lookupAround2, assumption+, simp,
  blast intro: is_aligned_no_overflow,
  clarsimp simp: gen_objBits_simps project_inject word_bits_def split: option.splits

lemma no_ofail_obj_at'_readObject_tcb[simp]:
  "no_ofail (obj_at' (P::tcb \<Rightarrow> bool) p) (readObject p::tcb kernel_r)"
  by no_ofail_readObject_method

lemma no_ofail_obj_at'_readObject_ep[simp]:
  "no_ofail (obj_at' (P::endpoint \<Rightarrow> bool) p) (readObject p::endpoint kernel_r)"
  by no_ofail_readObject_method

lemma no_ofail_obj_at'_readObject_ntfn[simp]:
  "no_ofail (obj_at' (P::notification \<Rightarrow> bool) p) (readObject p::notification kernel_r)"
  by no_ofail_readObject_method

lemma no_ofail_obj_at'_readObject_reply[simp]:
  "no_ofail (obj_at' (P::reply \<Rightarrow> bool) p) (readObject p::reply kernel_r)"
  by no_ofail_readObject_method

lemma no_ofail_obj_at'_readObject_sc[simp]:
  "no_ofail (obj_at' (P::sched_context \<Rightarrow> bool) p) (readObject p::sched_context kernel_r)"
  by no_ofail_readObject_method

lemmas no_ofail_tcb_at'_readObject[wp] = no_ofail_obj_at'_readObject_tcb[where P=\<top>]
lemmas no_ofail_ep_at'_readObject[wp] = no_ofail_obj_at'_readObject_ep[where P=\<top>]
lemmas no_ofail_ntfn_at'_readObject[wp] = no_ofail_obj_at'_readObject_ntfn[where P=\<top>]
lemmas no_ofail_reply_at'_readObject[wp] = no_ofail_obj_at'_readObject_reply[where P=\<top>]
lemmas no_ofail_sc_at'_readObject[wp] = no_ofail_obj_at'_readObject_sc[where P=\<top>]

lemma no_fail_getObject_misc[wp]:
  "no_fail (tcb_at' t) (getObject t :: tcb kernel)"
  "no_fail (sc_at' t) (getObject t :: sched_context kernel)"
  "no_fail (ep_at' t) (getObject t :: endpoint kernel)"
  "no_fail (ntfn_at' t) (getObject t :: notification kernel)"
  "no_fail (reply_at' t) (getObject t :: reply kernel)"
  by (wpsimp simp: getObject_def wp: no_ofail_gets_the)+

lemma lookupAround2_same1[simp]:
  "(fst (lookupAround2 x s) = Some (x, y)) = (s x = Some y)"
  apply (rule iffI)
   apply (simp add: lookupAround2_char1)
  apply (simp add: lookupAround2_known1)
  done

method readObject_obj_at'_method
  =  clarsimp simp: readObject_def obind_def omonad_defs split_def loadObject_default_def
                    obj_at'_def objBits_def scBits_pos_power2
             split: option.splits if_split_asm

lemma readObject_misc_ko_at'[simp]:
  shows
  readObject_ko_at'_tcb: "readObject p s = Some (tcb :: tcb) \<Longrightarrow> ko_at' tcb p s" and
  readObject_ko_at'_ep: "readObject p s = Some (ep :: endpoint) \<Longrightarrow> ko_at' ep p s" and
  readObject_ko_at'_ntfn: "readObject p s = Some (ntfn :: notification) \<Longrightarrow> ko_at' ntfn p s" and
  readObject_ko_at'_reply: "readObject p s = Some (reply :: reply) \<Longrightarrow> ko_at' reply p s" and
  readObject_ko_at'_sc: "readObject p s = Some (sc :: sched_context) \<Longrightarrow> ko_at' sc p s"
  by readObject_obj_at'_method+

lemma readObject_misc_obj_at'[simplified, simp]:
  shows
  readObject_tcb_at': "bound (readObject p s :: tcb option) \<Longrightarrow> tcb_at' p s" and
  readObject_ep_at': "bound (readObject p s :: endpoint option) \<Longrightarrow> ep_at' p s" and
  readObject_ntfn_at': "bound (readObject p s :: notification option) \<Longrightarrow> ntfn_at' p s" and
  readObject_reply_at': "bound (readObject p s :: reply option) \<Longrightarrow> reply_at' p s" and
  readObject_sc_at': "bound (readObject p s :: sched_context option) \<Longrightarrow> sc_at' p s"
  by readObject_obj_at'_method+

lemma getObject_tcb_at':
  "\<lbrace> \<top> \<rbrace> getObject t \<lbrace>\<lambda>r::tcb. tcb_at' t\<rbrace>"
  unfolding getObject_def by wpsimp

lemma get_object_def2:
  "get_object p = do
     kh \<leftarrow> gets kheap;
     assert (kh p \<noteq> None);
     return $ the $ kh p
   od"
  apply (rule ext)
  apply (rule monad_state_eqI)
    apply ((clarsimp simp: get_object_def gets_the_def gets_def assert_opt_def in_monad
                    split: option.splits)+)[2]
  by (clarsimp simp: snd_bind get_object_def snd_gets_the assert_def exec_gets return_def)

lemma getObject_def2:
  "getObject ptr = do
     map \<leftarrow> gets $ psMap \<circ> ksPSpace;
     (before, after) \<leftarrow> return (lookupAround2 (fromPPtr ptr) map);
     (ptr', val) \<leftarrow> assert_opt before;
     gets_the $ loadObject (fromPPtr ptr) ptr' after val
   od"
  apply (rule ext)
  apply (rule monad_state_eqI)
    apply (force simp: getObject_def readObject_def gets_the_def exec_gets obind_def split_def
                       omonad_defs assert_opt_def fail_def return_def in_monad
                split: option.splits)+
  by (clarsimp simp: snd_bind split_def getObject_def gets_the_def exec_gets assert_opt_def
                     readObject_def obind_def omonad_defs return_def fail_def
              split: option.splits)

lemma loadObject_default_def2:
  "(gets_the $ loadObject_default ptr ptr' next obj) = do
     assert (ptr = ptr');
     val \<leftarrow> (case projectKO_opt obj of None \<Rightarrow> fail | Some k \<Rightarrow> return k);
     alignCheck ptr (objBits val);
     assert (objBits val < word_bits);
     magnitudeCheck ptr next (objBits val);
     return val
   od"
  apply (rule ext)
  apply (rule monad_state_eqI)
    apply (force simp: loadObject_default_def gets_the_def exec_gets obind_def split_def
                       omonad_defs assert_opt_def fail_def return_def in_monad
                       read_magnitudeCheck_assert magnitudeCheck_assert
                split: option.splits if_splits)+
  by (force simp: snd_bind split_def loadObject_default_def gets_the_def exec_gets assert_opt_def
                  obind_def omonad_defs return_def fail_def projectKO_def assert_def
                  read_magnitudeCheck_assert magnitudeCheck_assert
                  read_alignError_def is_aligned_mask  alignCheck_def read_alignCheck_def
           split: option.splits)

lemma corres_get_tcb[corres]:
  "corres (tcb_relation \<circ> the) (tcb_at t) (tcb_at' t) (gets (get_tcb t)) (getObject t)"
  apply (rule corres_no_failI)
   apply wp
  apply (simp add: get_object_def get_tcb_def gets_def gets_the_def getObject_def)
  apply (clarsimp simp: in_monad split_def bind_def gets_def get_def return_def
                        assert_def fail_def obj_at_def is_tcb
                 dest!: readObject_misc_ko_at')
  apply (clarsimp simp: state_relation_def pspace_relation_def obj_at'_def)
  apply (drule bspec)
   apply blast
  apply (simp add: tcb_relation_cut_def)
  done

lemma updateObject_cte_is_tcb_or_cte:
  fixes cte :: cte and ptr :: machine_word
  shows "\<lbrakk> fst (lookupAround2 p (ksPSpace s)) = Some (q, ko);
           snd (lookupAround2 p (ksPSpace s)) = n;
           (ko', s') \<in> fst (updateObject cte ko p q n s) \<rbrakk>
         \<Longrightarrow> (\<exists>tcb getF setF. ko = KOTCB tcb \<and> s' = s \<and> tcb_cte_cases (p - q) = Some (getF, setF)
                             \<and> ko' = KOTCB (setF (\<lambda>x. cte) tcb) \<and> is_aligned q tcbBlockSizeBits
                             \<and> ps_clear q tcbBlockSizeBits s)
            \<or> (\<exists>cte'. ko = KOCTE cte' \<and> ko' = KOCTE cte \<and> s' = s
                      \<and> p = q \<and> is_aligned p cte_level_bits \<and> ps_clear p cte_level_bits s)"
  by (clarsimp simp: updateObject_cte typeError_def alignError_def gen_objBits_simps
                     in_monad in_magnitude_check3 lookupAround2_char1 tcb_cte_cases_neqs
                     tcbSlot_defs
               simp del: shiftl_1
               simp flip: cteSizeBits_cte_level_bits
               split: kernel_object.splits if_split_asm)

declare plus_1_less[simp]

lemma setObject_sc_at'_n[wp]:
  "setObject ptr val \<lbrace>\<lambda>s. P (sc_at'_n n p s)\<rbrace>"
  by (fastforce simp : valid_def setObject_def ko_wp_at'_def in_monad split_def updateObject_size
                       ps_clear_upd lookupAround2_char1 updateObject_type word_bits_def)

lemma updateObject_default_result:
  "(x, s'') \<in> fst (updateObject_default e ko p q n s) \<Longrightarrow> x = injectKO e"
  by (clarsimp simp add: updateObject_default_def in_monad)

lemma obj_at_setObject1:
  assumes R: "\<And>(v::'a::pspace_storable) p q n ko s x s''.
                (x, s'') \<in> fst (updateObject v ko p q n s) \<Longrightarrow> x = injectKO v"
  shows
  "\<lbrace> obj_at' (\<lambda>x::'a::pspace_storable. True) t \<rbrace>
   setObject p (v::'a::pspace_storable)
  \<lbrace> \<lambda>rv. obj_at' (\<lambda>x::'a::pspace_storable. True) t \<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (rule bind_wp [OF _ hoare_gets_sp])
  apply (clarsimp simp: valid_def in_monad obj_at'_def lookupAround2_char1 project_inject)
  apply (frule updateObject_size, drule R)
   apply (intro conjI impI, simp_all)
      apply fastforce+
  done

(* variant which can handle \<not> (obj_at' ...) *)
lemma obj_at_setObject2:
  fixes v :: "'a::pspace_storable"
  fixes P :: "'b::pspace_storable \<Rightarrow> bool"
  assumes R: "\<And>ko s' (v :: 'a) oko x y n s.
                (ko, s') \<in> fst (updateObject v oko x y n s) \<Longrightarrow> koTypeOf ko \<noteq> koType TYPE('b)"
  shows
    "\<lbrace>\<lambda>s. Q (obj_at' P t s) \<rbrace>
     setObject p (v::'a)
     \<lbrace>\<lambda>rv s. Q (obj_at' P t s) \<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (rule bind_wp [OF _ hoare_gets_sp])
  apply (clarsimp simp: valid_def in_monad)
  apply (frule updateObject_type)
  apply (drule R)
  apply (clarsimp simp: obj_at'_def)
  apply (cut_tac bool_function_four_cases[where f=Q])
  apply (erule disjE
         | clarsimp dest!: iffD1[OF project_koType, OF exI] simp: ps_clear_upd lookupAround2_char1)+
  done

\<comment>\<open> If the old and new versions of an object are the same size, then showing
    `obj_at'` for the updated state is the same as showing the predicate for
    the new value; we get to "reuse" the existing PSpace properties. \<close>
lemma same_size_obj_at'_set_obj'_iff:
  fixes obj :: "'a :: pspace_storable"
  assumes "obj_at' (\<lambda>old_obj :: 'a. objBits old_obj = objBits obj) ptr s"
  shows "obj_at' P ptr (set_obj' ptr obj s) = P obj"
  apply (rule iffI)
   apply (prop_tac "ko_at' obj ptr (set_obj' ptr obj s)")
    apply (clarsimp simp: obj_at'_def project_inject)
   apply (clarsimp simp: obj_at'_def)
  using assms
  apply (fastforce simp: obj_at'_def inj_def project_inject objBits_def)
  done

lemma tcb_at'_obj_at'_set_obj'[unfolded injectKO_tcb]:
  assumes "P (tcb :: tcb)"
      and "tcb_at' ptr s"
  shows "obj_at' P ptr (set_obj' ptr tcb s)"
  using assms
  apply (clarsimp simp: objBits_def objBitsKO_def inj_def
                        same_size_obj_at'_set_obj'_iff[where 'a=tcb, simplified])
  done

\<comment>\<open> Keeps a generic @{term obj_at'} (rather than a specific @{term "obj_at' (\<lambda>_. True)"}) to match
    in more simp contexts. \<close>
lemma tcb_obj_at'_set_obj'_iff:
  fixes tcb :: tcb
    and P Q :: "tcb \<Rightarrow> bool"
  shows "obj_at' P p s \<Longrightarrow> obj_at' Q p (set_obj' p tcb s) = Q tcb"
  apply (rule same_size_obj_at'_set_obj'_iff)
  apply (clarsimp simp: gen_objBits_simps obj_at'_def)
  done

lemmas tcb_obj_at'_pred_tcb'_set_obj'_iff =
  tcb_obj_at'_set_obj'_iff[where Q="test o proj o tcb_to_itcb'" for test proj,
                                 simplified gen_objBits_simps o_def, simplified,
                                 folded pred_tcb_at'_def]

lemma same_size_ko_wp_at'_set_ko'_iff:
  assumes "ko_wp_at' (\<lambda>old_ko. objBitsKO old_ko = objBitsKO ko) ptr s"
  shows "ko_wp_at' P ptr (set_ko' ptr ko s) = P ko"
  apply (rule iffI)
   apply (clarsimp simp: ko_wp_at'_def)
  using assms
  apply (clarsimp simp: ko_wp_at'_def)
  apply (erule ps_clear_domE)
  apply clarsimp
  apply blast
  done

\<comment>\<open> Moves the @{term ksPSpace_update} to the top. \<close>
lemma unfold_set_ko':
  "set_ko' ptr ko s = ksPSpace_update (\<lambda>ps. ps(ptr := Some ko)) s"
  by clarsimp

lemma ko_wp_at'_set_ko'_distinct:
  assumes "ptr \<noteq> ptr'"
          "ko_wp_at' \<top> ptr' s"
  shows "ko_wp_at' P ptr (set_ko' ptr' ko s) = ko_wp_at' P ptr s"
  using assms
  apply (clarsimp simp: ko_wp_at'_def)
  apply (rule iffI; clarsimp)
   apply (erule ps_clear_domE)
   apply clarsimp
   apply blast
  apply (erule ps_clear_domE)
  apply clarsimp
  apply blast
  done

lemma obj_at'_set_obj'_distinct:
  "\<lbrakk>p \<noteq> p'; obj_at' Q p' s\<rbrakk>
   \<Longrightarrow> obj_at' P p (set_ko' p' ko s) = obj_at' P p s"
  apply (fastforce simp: obj_at'_def ps_clear_upd)
  done

lemmas pred_tcb_at'_set_obj'_distinct =
  obj_at'_set_obj'_distinct[where P="test o proj o tcb_to_itcb'" for test proj,
                            simplified o_def, folded pred_tcb_at'_def]

lemmas pred_tcb_at'_set_obj'_iff =
  tcb_obj_at'_set_obj'_iff[where Q="test o proj o tcb_to_itcb'" for test proj,
                           simplified o_def injectKO_tcb, folded pred_tcb_at'_def]

\<comment>\<open> Used to show a stronger variant of @{thm obj_at_setObject2} for many concrete types.

    Needs to be a definition so we can easily refer to it within ML as a constant. \<close>
definition distinct_updateObject_types ::
  "('a :: pspace_storable) itself \<Rightarrow> ('b :: pspace_storable) itself \<Rightarrow> bool"
  where
  "distinct_updateObject_types t t' \<equiv>
    (\<forall>ko' s' (v :: 'a) ko p before after s.
      (ko', s') \<in> fst (updateObject v ko p before after s)
      \<longrightarrow> koTypeOf ko' \<noteq> koType TYPE('b))"

lemma setObject_distinct_types_preserves_obj_at'_pre:
  fixes v :: "'a :: pspace_storable"
    and P :: "'b :: pspace_storable \<Rightarrow> bool"
  assumes distinct_types[unfolded distinct_updateObject_types_def, rule_format]:
    "distinct_updateObject_types TYPE('a) TYPE('b)"
  shows "setObject p v \<lbrace>\<lambda>s. P' (obj_at' P t s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (rule bind_wp [OF _ hoare_gets_sp])
  apply (clarsimp simp: valid_def in_monad)
  apply (frule updateObject_type)
  apply (erule_tac P="P'" in rsubst)
  apply (drule distinct_types)
  apply (clarsimp simp: lookupAround2_char1)
  apply (case_tac "obj_at' P t s")
   apply (clarsimp simp: obj_at'_def)
   using project_koType ps_clear_upd
   apply fastforce
  apply (clarsimp simp: obj_at'_def ps_clear_upd)
  apply (intro impI conjI iffI; metis project_koType)
  done

\<comment>\<open> We're using @{command ML_goal} here because we want to show
    `distinct_updateObject_types TYPE('a) TYPE('b)` for around
    50 different combinations of 'a and 'b. Doing that by hand would
    be painful, and not as clear for future readers as this comment
    plus this ML code. \<close>
ML \<open>
local
  val ko_types = [
    @{typ notification},
    @{typ tcb},
    @{typ cte},
    @{typ sched_context},
    @{typ reply},
    @{typ endpoint}
  ];

  val skipped_pairs = [
    \<comment>\<open>This corresponds to the case where we're inserting a CTE into
       a TCB, which is the only case where the first two arguments
       to `updateObject` should have different types.

       See the comment on @{term updateObject} for more information.\<close>
    (@{typ cte}, @{typ tcb})
  ];

  fun skips (ts as (typ, typ')) =
      typ = typ' orelse Library.member (op =) skipped_pairs ts;

  fun mk_distinct_goal (typ, typ') =
      Const (@{const_name distinct_updateObject_types},
            Term.itselfT typ --> Term.itselfT typ' --> @{typ bool})
      $ Logic.mk_type typ
      $ Logic.mk_type typ';
in
  val distinct_updateObject_gen_types_goals =
      Library.map_product pair ko_types ko_types
      |> Library.filter_out skips
      |> List.map mk_distinct_goal
end
\<close>

ML_goal distinct_updateObject_gen_types: \<open>
  distinct_updateObject_gen_types_goals
\<close>
  apply -
  \<comment>\<open> The produced goals match the following pattern: \<close>
  apply (all \<open>match conclusion in \<open>distinct_updateObject_types _ _\<close> \<Rightarrow> -\<close>)
  unfolding distinct_updateObject_types_def
  apply safe
  apply (clarsimp simp: distinct_updateObject_types_def
                        setObject_def updateObject_cte updateObject_default_def
                        typeError_def in_monad
                 split: if_splits kernel_object.splits)+
  done

lemmas setObject_distinct_gen_types_preserves_obj_at'[wp] =
    distinct_updateObject_gen_types[THEN setObject_distinct_types_preserves_obj_at'_pre]

(* FIXME RT: these overlap substantially with `setObject_distinct_types_preserves_obj_at'`,
   but fixing that requires having names for the relevant subset of lemmas. We can't do that with
   attributes, but we might be able to do it with a new command (`lemmas_matching`?) once `match`
   is factored.

   This doesn't really matter in this case because you're never going to refer to these lemmas by
   name. *)
lemmas set_distinct_gen_types_preserves_obj_at'[wp] =
  setObject_distinct_gen_types_preserves_obj_at'[folded setReply_def setNotification_def setCTE_def
                                                        setSchedContext_def setEndpoint_def]

lemmas set_distinct_gen_types_preserves_pred_tcb_at'[wp] =
  set_distinct_gen_types_preserves_obj_at'[TRY[where P="test o proj o tcb_to_itcb'" for test proj,
                                               simplified o_def, folded pred_tcb_at'_def, rule_format]]
  setObject_distinct_gen_types_preserves_obj_at'[TRY[where P="test o proj o tcb_to_itcb'" for test proj,
                                                 simplified o_def, folded pred_tcb_at'_def,
                                                 rule_format]]

lemma obj_at_setObject3:
  fixes Q::"'a::pspace_storable \<Rightarrow> bool"
  fixes P::"'a::pspace_storable \<Rightarrow> bool"
  assumes R: "\<And>ko s y n. (updateObject v ko p y n s)
                   = (updateObject_default v ko p y n s)"
  assumes P: "\<And>(v::'a::pspace_storable). (1 :: machine_word) < 2 ^ (objBits v)"
  shows "\<lbrace>(\<lambda>s. P v)\<rbrace> setObject p v \<lbrace>\<lambda>rv. obj_at' P p\<rbrace>"
  apply (clarsimp simp add: valid_def in_monad obj_at'_def
                            setObject_def split_def
                            project_inject objBits_def[symmetric]
                            R updateObject_default_def
                            in_magnitude_check P ps_clear_upd)
  apply fastforce
  done

lemma setObject_tcb_strongest:
  "\<lbrace>\<lambda>s. if t = t' then P tcb else obj_at' P t' s\<rbrace>
   setObject t (tcb :: tcb)
   \<lbrace>\<lambda>rv. obj_at' P t'\<rbrace>"
  apply (cases "t = t'")
   apply simp
   apply (rule hoare_weaken_pre[OF obj_at_setObject3]; simp add: gen_objBits_simps)
  apply (clarsimp simp: setObject_def valid_def obj_at'_def split_def in_monad
                        updateObject_default_def ps_clear_upd)
  done

method setObject_easy_cases uses simp =
  clarsimp simp: setObject_def in_monad split_def valid_def lookupAround2_char1,
  erule rsubst[where P=P'], rule ext,
  clarsimp simp: updateObject_cte updateObject_default_def in_monad
                 typeError_def opt_map_def opt_pred_def projectKO_opts_defs
                 simp
          split: if_split_asm
                 Structures_H.kernel_object.split_asm

lemma setObject_endpoint_replies_of'[wp]:
  "setObject c (endpoint::endpoint) \<lbrace>\<lambda>s. P' (replies_of' s)\<rbrace>"
  by setObject_easy_cases

lemma setObject_endpoint_tcbs_of'[wp]:
  "setObject c (endpoint :: endpoint) \<lbrace>\<lambda>s. P' (tcbs_of' s)\<rbrace>"
  by setObject_easy_cases

lemma setObject_notification_replies_of'[wp]:
  "setObject c (notification::notification) \<lbrace>\<lambda>s. P' (replies_of' s)\<rbrace>"
  by setObject_easy_cases

lemma setObject_notification_tcbs_of'[wp]:
  "setObject c (notification :: notification) \<lbrace>\<lambda>s. P' (tcbs_of' s)\<rbrace>"
  by setObject_easy_cases

lemma setObject_tcb_replies_of'[wp]:
  "setObject c (tcb::tcb) \<lbrace>\<lambda>s. P' (replies_of' s)\<rbrace>"
  by setObject_easy_cases

lemma setObject_sched_context_replies_of'[wp]:
  "setObject c (sched_context::sched_context) \<lbrace>\<lambda>s. P' (replies_of' s)\<rbrace>"
  by setObject_easy_cases

lemma setObject_sched_context_tcbs_of'[wp]:
  "setObject c (sched_context :: sched_context) \<lbrace>\<lambda>s. P' (tcbs_of' s)\<rbrace>"
  by setObject_easy_cases

lemma setObject_cte_replies_of'[wp]:
  "setObject c (cte::cte) \<lbrace>\<lambda>s. P' (replies_of' s)\<rbrace>"
  by setObject_easy_cases

lemma setObject_endpoint_aobjs_of'[wp]:
  "setObject c (ep :: endpoint) \<lbrace>\<lambda>s. P' (aobjs_of' s)\<rbrace>"
  by setObject_easy_cases

lemma setObject_notification_aobjs_of'[wp]:
  "setObject c (ntfn :: notification) \<lbrace>\<lambda>s. P' (aobjs_of' s)\<rbrace>"
  by setObject_easy_cases

lemma setObject_cte_aobjs_of'[wp]:
  "setObject c (cte :: cte) \<lbrace>\<lambda>s. P' (aobjs_of' s)\<rbrace>"
  by setObject_easy_cases

lemma setObject_tcb_aobjs_of'[wp]:
  "setObject c (tcb :: tcb) \<lbrace>\<lambda>s. P' (aobjs_of' s)\<rbrace>"
  by setObject_easy_cases

lemma setObject_cte_tcbSchedNexts_of[wp]:
  "setObject c (cte :: cte) \<lbrace>\<lambda>s. P' (tcbSchedNexts_of s)\<rbrace>"
  by setObject_easy_cases

lemma setObject_cte_tcbSchedPrevs_of[wp]:
  "setObject c (cte :: cte) \<lbrace>\<lambda>s. P' (tcbSchedPrevs_of s)\<rbrace>"
  by setObject_easy_cases

lemma setObject_cte_tcbInReleaseQueue[wp]:
  "setObject c (cte :: cte) \<lbrace>\<lambda>s. P' (tcbInReleaseQueue |< tcbs_of' s)\<rbrace>"
  by setObject_easy_cases

lemma setObject_cte_tcbQueued[wp]:
  "setObject c (cte :: cte) \<lbrace>\<lambda>s. P' (tcbQueued |< tcbs_of' s)\<rbrace>"
  supply inQ_def[simp]
  by setObject_easy_cases

lemma setObject_cte_inQ[wp]:
  "setObject c (cte :: cte) \<lbrace>\<lambda>s. P' (inQ d p |< tcbs_of' s)\<rbrace>"
  supply inQ_def[simp]
  by setObject_easy_cases

lemma setObject_cte_tcbStates_of'[wp]:
  "setObject c (cte :: cte) \<lbrace>\<lambda>s. P' (tcbStates_of' s)\<rbrace>"
  by setObject_easy_cases

lemma setObject_reply_tcbs_of'[wp]:
  "setObject c (reply :: reply) \<lbrace>\<lambda>s. P' (tcbs_of' s)\<rbrace>"
  by setObject_easy_cases

lemma setObject_cte_tcbSCs_of[wp]:
  "setObject c (cte::cte) \<lbrace>\<lambda>s. P' (tcbSCs_of s)\<rbrace>"
  by setObject_easy_cases

lemma setObject_ntfns_of'[wp]:
  "setObject c (cte :: cte) \<lbrace>\<lambda>s. P' (ntfns_of' s)\<rbrace>"
  "setObject c (reply :: reply) \<lbrace>\<lambda>s. P' (ntfns_of' s)\<rbrace>"
  "setObject c (tcb :: tcb) \<lbrace>\<lambda>s. P' (ntfns_of' s)\<rbrace>"
  "setObject c (sched_context :: sched_context) \<lbrace>\<lambda>s. P' (ntfns_of' s)\<rbrace>"
  "setObject c (endpoint :: endpoint) \<lbrace>\<lambda>s. P' (ntfns_of' s)\<rbrace>"
  by setObject_easy_cases+

lemma setObject_eps_of'[wp]:
  "setObject c (cte :: cte) \<lbrace>\<lambda>s. P' (eps_of' s)\<rbrace>"
  "setObject c (reply :: reply) \<lbrace>\<lambda>s. P' (eps_of' s)\<rbrace>"
  "setObject c (tcb :: tcb) \<lbrace>\<lambda>s. P' (eps_of' s)\<rbrace>"
  "setObject c (sched_context :: sched_context) \<lbrace>\<lambda>s. P' (eps_of' s)\<rbrace>"
  "setObject c (notification :: notification) \<lbrace>\<lambda>s. P' (eps_of' s)\<rbrace>"
  by setObject_easy_cases+

lemma setObject_cnode_ctes_of'[wp]:
  "setObject c (sc :: sched_context) \<lbrace>\<lambda>s. P' (cnode_ctes_of' s)\<rbrace>"
  "setObject c (reply :: reply) \<lbrace>\<lambda>s. P' (cnode_ctes_of' s)\<rbrace>"
  "setObject c (tcb :: tcb) \<lbrace>\<lambda>s. P' (cnode_ctes_of' s)\<rbrace>"
  "setObject c (notification :: notification) \<lbrace>\<lambda>s. P' (cnode_ctes_of' s)\<rbrace>"
  "setObject c (endpoint :: endpoint) \<lbrace>\<lambda>s. P' (cnode_ctes_of' s)\<rbrace>"
  by setObject_easy_cases+

lemma setObject_kernelData_at[wp]:
  "setObject c (sc::sched_context) \<lbrace>\<lambda>s. P' (kernelData_at s)\<rbrace>"
  "setObject c (reply::reply) \<lbrace>\<lambda>s. P' (kernelData_at s)\<rbrace>"
  "setObject c (tcb::tcb) \<lbrace>\<lambda>s. P' (kernelData_at s)\<rbrace>"
  "setObject c (notification::notification) \<lbrace>\<lambda>s. P' (kernelData_at s)\<rbrace>"
  "setObject c (endpoint::endpoint) \<lbrace>\<lambda>s. P' (kernelData_at s)\<rbrace>"
  "setObject c (cte::cte) \<lbrace>\<lambda>s. P' (kernelData_at s)\<rbrace>"
  by (setObject_easy_cases simp: gen_objBits_simps; fastforce)+

lemma setObject_userDataDevice_at[wp]:
  "setObject c (sc::sched_context) \<lbrace>\<lambda>s. P' (userDataDevice_at s)\<rbrace>"
  "setObject c (reply::reply) \<lbrace>\<lambda>s. P' (userDataDevice_at s)\<rbrace>"
  "setObject c (tcb::tcb) \<lbrace>\<lambda>s. P' (userDataDevice_at s)\<rbrace>"
  "setObject c (notification::notification) \<lbrace>\<lambda>s. P' (userDataDevice_at s)\<rbrace>"
  "setObject c (endpoint::endpoint) \<lbrace>\<lambda>s. P' (userDataDevice_at s)\<rbrace>"
  "setObject c (cte::cte) \<lbrace>\<lambda>s. P' (userDataDevice_at s)\<rbrace>"
  by (setObject_easy_cases simp: gen_objBits_simps; fastforce)+

lemma setObject_userData_at[wp]:
  "setObject c (sc::sched_context) \<lbrace>\<lambda>s. P' (userData_at s)\<rbrace>"
  "setObject c (reply::reply) \<lbrace>\<lambda>s. P' (userData_at s)\<rbrace>"
  "setObject c (tcb::tcb) \<lbrace>\<lambda>s. P' (userData_at s)\<rbrace>"
  "setObject c (notification::notification) \<lbrace>\<lambda>s. P' (userData_at s)\<rbrace>"
  "setObject c (endpoint::endpoint) \<lbrace>\<lambda>s. P' (userData_at s)\<rbrace>"
  "setObject c (cte::cte) \<lbrace>\<lambda>s. P' (userData_at s)\<rbrace>"
  by (setObject_easy_cases simp: gen_objBits_simps; fastforce)+

\<comment>\<open> Warning: this may not be a weakest precondition. `setObject c`
    asserts that there's already a correctly-typed object at `c`,
    so a weaker valid precondition might be
    @{term "\<lambda>s. replies_of' s c \<noteq> None \<longrightarrow>  P' ((replies_of' s)(c \<mapsto> reply))"} \<close>
lemma setObject_reply_replies_of'[wp]:
  "\<lbrace>\<lambda>s. P' ((replies_of' s)(c \<mapsto> reply))\<rbrace>
  setObject c (reply::reply)
  \<lbrace>\<lambda>_ s. P' (replies_of' s)\<rbrace>"
  by setObject_easy_cases

\<comment>\<open> Warning: this may not be a weakest precondition. `setObject c`
    asserts that there's already a correctly-typed object at `c`,
    so a weaker valid precondition might be
    @{term "\<lambda>s. scs_of' s c \<noteq> None \<longrightarrow>  P' ((scs_of' s)(c \<mapsto> sched_context))"} \<close>
lemma setObject_sched_context_scs_of'[wp]:
  "\<lbrace>\<lambda>s. P' ((scs_of' s)(c \<mapsto> sched_context))\<rbrace>
   setObject c (sched_context::sched_context)
   \<lbrace>\<lambda>_ s. P' (scs_of' s)\<rbrace>"
  by setObject_easy_cases

lemma setObject_scs_of'[wp]:
  "setObject c (cte::cte) \<lbrace>\<lambda>s. P' (scs_of' s)\<rbrace>"
  "setObject c (reply::reply) \<lbrace>\<lambda>s. P' (scs_of' s)\<rbrace>"
  "setObject c (tcb::tcb) \<lbrace>\<lambda>s. P' (scs_of' s)\<rbrace>"
  "setObject c (notification::notification) \<lbrace>\<lambda>s. P' (scs_of' s)\<rbrace>"
  "setObject c (endpoint::endpoint) \<lbrace>\<lambda>s. P' (scs_of' s)\<rbrace>"
  by setObject_easy_cases+

lemma setObject_aobjs_of'[wp]:
  "setObject c (sc :: sched_context) \<lbrace>\<lambda>s. P' (aobjs_of' s)\<rbrace>"
  "setObject c (reply :: reply) \<lbrace>\<lambda>s. P' (aobjs_of' s)\<rbrace>"
  "setObject c (tcb :: tcb) \<lbrace>\<lambda>s. P' (aobjs_of' s)\<rbrace>"
  "setObject c (notification :: notification) \<lbrace>\<lambda>s. P' (aobjs_of' s)\<rbrace>"
  "setObject c (endpoint :: endpoint) \<lbrace>\<lambda>s. P' (aobjs_of' s)\<rbrace>"
  "setObject c (cte :: cte) \<lbrace>\<lambda>s. P' (aobjs_of' s)\<rbrace>"
  by (setObject_easy_cases simp: aobj_of'_def)+

lemmas setReply_replies_of' = setObject_reply_replies_of'[folded setReply_def]

lemmas setSchedContext_scs_of_of' =
  setObject_sched_context_scs_of'[folded setSchedContext_def]

crunch setNotification, setEndpoint, setCTE, setReply
  for scs_of'[wp]: "\<lambda>s. P (scs_of' s)"

lemma getObject_obj_at':
  assumes x: "\<And>q n ko. loadObject p q n ko =
                (loadObject_default p q n ko :: ('a :: pspace_storable) kernel_r)"
  shows      "\<lbrace> \<top> \<rbrace> getObject p \<lbrace>\<lambda>r::'a::pspace_storable. obj_at' ((=) r) p\<rbrace>"
  by (clarsimp simp: valid_def getObject_def in_monad omonad_defs readObject_def
                     loadObject_default_def obj_at'_def
                     split_def in_magnitude_check lookupAround2_char1
                     x project_inject objBits_def[symmetric]
              split: option.split_asm if_split_asm)

lemma getObject_valid_obj:
  assumes x: "\<And>p q n ko. loadObject p q n ko =
                (loadObject_default p q n ko :: ('a :: pspace_storable) kernel_r)"
  shows "\<lbrace> valid_objs' \<rbrace> getObject p \<lbrace>\<lambda>rv::'a::pspace_storable. valid_obj' (injectKO rv) \<rbrace>"
  apply (rule hoare_chain)
    apply (rule hoare_vcg_conj_lift)
     apply (rule getObject_obj_at' [OF x])
    apply (rule getObject_inv)
   apply (clarsimp, assumption)
  apply clarsimp
  apply (drule(1) obj_at_valid_objs')
  apply (clarsimp simp: project_inject)
  done

declare fail_inv[simp]

lemma typeError_inv [wp]:
  "\<lbrace>P\<rbrace> typeError x y \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: typeError_def | wp)+


lemma getObject_cte_inv [wp]: "\<lbrace>P\<rbrace> (getObject addr :: cte kernel) \<lbrace>\<lambda>rv. P\<rbrace>"
  by (wpsimp simp: getObject_def)

lemma getObject_ko_at:
  assumes x: "\<And>q n ko. loadObject p q n ko =
                (loadObject_default p q n ko :: ('a :: pspace_storable) kernel_r)"
  shows      "\<lbrace> \<top> \<rbrace> getObject p \<lbrace>\<lambda>r::'a::pspace_storable. ko_at' r p\<rbrace>"
  by (subst eq_commute, rule getObject_obj_at' [OF x])

lemma getObject_ko_at_tcb [wp]:
  "\<lbrace>\<top>\<rbrace> getObject p \<lbrace>\<lambda>rv::tcb. ko_at' rv p\<rbrace>"
  by (rule getObject_ko_at | simp add: gen_objBits_simps)+

lemma OMG_getObject_tcb:
  "\<lbrace>obj_at' P t\<rbrace> getObject t \<lbrace>\<lambda>(tcb :: tcb) s. P tcb\<rbrace>"
  apply (rule obj_at_getObject)
  apply (clarsimp simp: loadObject_default_def in_monad)
  done

lemma setObject_nosch:
  assumes x: "\<And>p q n ko. \<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> updateObject val p q n ko \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> setObject t val \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp x | simp)+
  done

context
begin

private method getObject_valid_obj =
  rule hoare_chain,
  rule getObject_valid_obj; clarsimp simp: gen_objBits_simps valid_obj'_def scBits_pos_power2

lemma get_ntfn'_valid_ntfn[wp]:
  "\<lbrace> valid_objs' \<rbrace> getNotification ep \<lbrace> valid_ntfn' \<rbrace>"
  unfolding getNotification_def by getObject_valid_obj

lemma get_sc_valid_sc'[wp]:
  "\<lbrace> valid_objs' \<rbrace> getSchedContext sc \<lbrace> valid_sched_context' \<rbrace>"
  unfolding getSchedContext_def by getObject_valid_obj

lemma get_reply_valid_reply'[wp]:
  "\<lbrace> valid_objs'\<rbrace> getReply sc \<lbrace> valid_reply' \<rbrace>"
  unfolding getReply_def by getObject_valid_obj

end

lemma get_ep_ko':
  "\<lbrace>\<top>\<rbrace> getEndpoint ep \<lbrace>\<lambda>rv. ko_at' rv ep\<rbrace>"
  unfolding getEndpoint_def
  by (rule getObject_ko_at; simp add: gen_objBits_simps)

lemma get_ntfn_ko':
  "\<lbrace>\<top>\<rbrace> getNotification ntfn \<lbrace>\<lambda>rv. ko_at' rv ntfn\<rbrace>"
  unfolding getNotification_def
  by (rule getObject_ko_at; simp add: gen_objBits_simps)

lemma get_sc_ko':
  "\<lbrace>\<top>\<rbrace> getSchedContext sc_ptr \<lbrace>\<lambda>sc. ko_at' sc sc_ptr\<rbrace>"
  unfolding getSchedContext_def
  by (rule getObject_ko_at; simp add: gen_objBits_simps scBits_pos_power2)

lemma get_reply_ko':
  "\<lbrace>\<top>\<rbrace> getReply reply_ptr \<lbrace>\<lambda>reply. ko_at' reply reply_ptr\<rbrace>"
  unfolding getReply_def
  by (rule getObject_ko_at; simp add: gen_objBits_simps)

context
begin

private method unfold_setObject_inmonad =
  (clarsimp simp: setObject_def split_def valid_def in_monad updateObject_size
                  objBits_def[symmetric] lookupAround2_char1 ps_clear_upd
            split: if_split_asm),
    (fastforce dest: bspec[OF _ domI])+

lemma setObject_distinct[wp]:
  "setObject p val \<lbrace>pspace_distinct'\<rbrace>"
  unfolding pspace_distinct'_def by (unfold_setObject_inmonad)

lemma setObject_aligned[wp]:
  "setObject p val \<lbrace>pspace_aligned'\<rbrace>"
  unfolding pspace_aligned'_def by (unfold_setObject_inmonad)

lemma setObject_bounded[wp]:
  "setObject p val \<lbrace>pspace_bounded'\<rbrace>"
  unfolding pspace_bounded'_def by (unfold_setObject_inmonad)

lemma setObject_canonical[wp]:
  "setObject p val \<lbrace>pspace_canonical'\<rbrace>"
  unfolding pspace_canonical'_def by (unfold_setObject_inmonad)

end

lemmas ps_clear_def3 = ps_clear_def2[OF order_less_imp_le[OF aligned_less_plus_1]]

(* FIXME rt merge: move to Word_lib *)
lemma max_word_minus_1[simp]: "0xFFFFFFFFFFFFFFFF + 2^x = (2^x - 1::64 word)"
  by simp

lemma ctes_of'_after_update:
  "ko_wp_at' (same_caps' val) p s \<Longrightarrow> ctes_of (s\<lparr>ksPSpace := (ksPSpace s)(p \<mapsto> val)\<rparr>) x = ctes_of s x"
  apply (clarsimp simp only: ko_wp_at'_def map_to_ctes_def Let_def)
  apply (rule if_cong)
    apply (cases val; fastforce split: if_splits)
   apply (cases val; fastforce split: if_splits)
  apply (rule if_cong)
    apply (cases val; clarsimp simp: objBitsKO_def tcbBlockSizeBits_def; fastforce)
   apply (cases val; clarsimp; fastforce dest!: bspec del: ranI intro!: ranI option.map_cong0)
  apply simp
  done

lemma tcb_cte_cases_small:
  "\<lbrakk> tcb_cte_cases v = Some (getF, setF) \<rbrakk>
      \<Longrightarrow> v < 2 ^ tcbBlockSizeBits"
  by (simp add: tcb_cte_cases_def gen_objBits_simps split: if_split_asm)

lemmas tcb_cte_cases_aligned_helpers =
  is_aligned_add_helper[OF _ tcb_cte_cases_small]
  is_aligned_sub_helper[OF _ tcb_cte_cases_small]

lemma tcb_cases_related:
  "tcb_cap_cases ref = Some (getF, setF, restr)
   \<Longrightarrow> \<exists>getF' setF'.
        (\<forall>x. tcb_cte_cases (cte_map (x, ref) - x) = Some (getF', setF'))
        \<and> (\<forall>tcb tcb'. tcb_relation tcb tcb' \<longrightarrow> cap_relation (getF tcb) (cteCap (getF' tcb')))"
  by (clarsimp simp: tcb_relation_def cte_map_def tcb_cap_cases_def tcb_cte_cases_neqs
                     tcb_cte_cases_def tcb_cnode_index_def
                     to_bl_1
               simp flip: cteSizeBits_cte_level_bits
               split: if_split_asm)

declare overflow_plus_one_self[simp]

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
    apply (clarsimp simp: ps_clear_upd lookupAround2_char1 y)
   apply (erule exEI [where 'a=machine_word])
   apply (clarsimp simp: ps_clear_upd lookupAround2_char1)
   apply (drule(1) x)
    apply (clarsimp simp: lookupAround2_char1 prod_eqI)
   apply (fastforce dest: bspec [OF _ ranI])
  apply (erule disjEI)
   apply (clarsimp simp: ps_clear_upd lookupAround2_char1
                  split: if_split_asm)
   apply (frule updateObject_type)
   apply (case_tac ba, simp_all add: y)[1]
  apply (erule exEI)
  apply (clarsimp simp: ps_clear_upd lookupAround2_char1
                 split: if_split_asm)
  apply (frule updateObject_type)
  apply (case_tac ba, simp_all)
  apply (drule(1) x)
   apply (clarsimp simp: prod_eqI lookupAround2_char1)
  apply (fastforce dest: bspec [OF _ ranI])
  done

lemma map_to_ctes_upd_cte:
  "\<lbrakk> s p = Some (KOCTE cte'); is_aligned p cte_level_bits;
     {p + 1..p + mask cte_level_bits} \<inter> dom s = {} \<rbrakk> \<Longrightarrow>
     map_to_ctes (s (p \<mapsto> (KOCTE cte))) = ((map_to_ctes s) (p \<mapsto> cte))"
  apply (rule ext)
  apply (simp    add: map_to_ctes_def Let_def dom_fun_upd2
           split del: if_split del: dom_fun_upd)
  apply (case_tac "x = p")
   apply (simp add: gen_objBits_simps cteSizeBits_cte_level_bits mask_def field_simps)
  apply (case_tac "(x && ~~ mask (objBitsKO (KOTCB undefined))) = p")
   apply clarsimp
  apply (simp del: dom_fun_upd add: dom_fun_upd2 split del: if_split cong: if_cong)
  done

lemma map_to_ctes_upd_tcb:
  "\<lbrakk> s p = Some (KOTCB tcb'); is_aligned p tcbBlockSizeBits; {p + 1..p + mask tcbBlockSizeBits} \<inter> dom s = {} \<rbrakk> \<Longrightarrow>
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
    apply (simp add: gen_objBits_simps field_simps map_to_ctes_def mask_def)
   apply (case_tac "x && ~~ mask (objBitsKO (KOTCB undefined)) = p")
    apply (case_tac "tcb_cte_cases (x - p)")
     apply (simp split del: if_split cong: if_cong option.case_cong)
    apply (subgoal_tac "s x = None")
     apply (simp add: field_simps gen_objBits_simps mask_def split del: if_split
                cong: if_cong option.case_cong)
     apply clarsimp
    apply (subst(asm) mask_in_range[where bits="objBitsKO v" for v])
     apply (simp add: gen_objBits_simps)
    apply (drule_tac a=x in equals0D)
    apply (simp add: dom_def gen_objBits_simps mask_def field_simps)
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
    apply (simp add: gen_objBits_simps field_simps)
   apply (clarsimp simp: tcb_cte_cases_def gen_objBits_simps
                  split: if_splits)
  apply (subst mask_in_range, assumption)
  apply (simp only: atLeastAtMost_iff order_refl simp_thms)
  apply (erule is_aligned_no_overflow)
  done

lemma real_cte_at':
  "real_cte_at' p s \<Longrightarrow> cte_at' p s"
  by (clarsimp simp add: cte_wp_at_cases' obj_at'_def gen_objBits_simps cteSizeBits_cte_level_bits
                    del: disjCI)

lemma no_fail_getMiscObject[wp]:
  "no_fail (ep_at' ptr) (getEndpoint ptr)"
  "no_fail (ntfn_at' ptr) (getNotification ptr)"
  "no_fail (reply_at' ptr) (getReply ptr)"
  "no_fail (sc_at' ptr) (getSchedContext ptr)"
  by (wpsimp simp: getEndpoint_def getNotification_def getReply_def getSchedContext_def)+

lemma getEndpoint_corres:
  "corres ep_relation (ep_at ptr) (ep_at' ptr)
     (get_endpoint ptr) (getEndpoint ptr)"
  apply (rule corres_no_failI)
   apply wp
  apply (simp add: get_simple_ko_def getEndpoint_def get_object_def gets_the_def
                   getObject_def bind_assoc ep_at_def2)
  apply (clarsimp simp: in_monad split_def bind_def gets_def get_def return_def
                 dest!: readObject_misc_ko_at')
  apply (clarsimp simp: assert_def fail_def obj_at_def return_def is_ep partial_inv_def)
  apply (clarsimp simp: state_relation_def pspace_relation_def obj_at'_def)
  apply (drule bspec)
   apply blast
  apply (simp add: ep_relation_def ep_relation_cut_def)
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

lemma read_magnitudeCheck_Some:
  "(case y of None \<Rightarrow> True | Some z \<Rightarrow> 2 ^ n \<le> z - x)
   \<longleftrightarrow> read_magnitudeCheck x y n s = Some ()"
  by (fastforce simp: read_magnitudeCheck_def split: option.splits if_split_asm; simp)

lemmas read_magnitudeCheck_Some'[simp, intro!] = read_magnitudeCheck_Some[THEN iffD1]
lemma no_fail_magnitudeCheck[wp]:
  "no_fail (\<lambda>s. case y of None \<Rightarrow> True | Some z \<Rightarrow> 2 ^ n \<le> z - x)
    (magnitudeCheck x y n)"
  apply (clarsimp simp: magnitudeCheck_def gets_the_def)
  apply (rule no_fail_pre, wp)
  apply simp
  done

lemma no_fail_setObject_other [wp]:
  fixes ob :: "'a :: pspace_storable"
  assumes x: "updateObject ob = updateObject_default ob"
  shows "no_fail (obj_at' (\<lambda>k::'a. objBits k = objBits ob) ptr)
                  (setObject ptr ob)"
  apply (simp add: setObject_def x split_def updateObject_default_def alignError_def
                   projectKO_def alignCheck_def read_alignCheck_def read_alignError_def)
  apply (rule no_fail_pre)
   apply wp
  apply (clarsimp simp: is_aligned_mask[symmetric] obj_at'_def omonad_defs
                        objBits_def[symmetric]
                        project_inject lookupAround2_known1)
  apply (erule(1) ps_clear_lookupAround2)
    apply simp
   apply (erule is_aligned_get_word_bits)
    apply (subst add_diff_eq[symmetric])
    apply (erule is_aligned_no_wrap')
    apply simp
   apply simp
  apply (fastforce simp: oassert_opt_def project_inject split: option.splits)
  done

lemma replyNexts_of_non_reply_update:
  "\<And>s'. \<lbrakk>typ_at' (koTypeOf ko) ptr s';
   koTypeOf ko \<noteq> ReplyT \<rbrakk>
     \<Longrightarrow> replyNexts_of (s'\<lparr>ksPSpace := (ksPSpace s')(ptr \<mapsto> ko)\<rparr>) = replyNexts_of s'"
  by (fastforce simp: typ_at'_def ko_wp_at'_def opt_map_def projectKO_opts_defs
               split: kernel_object.splits)

definition replyNext_same :: "'a :: pspace_storable \<Rightarrow> 'a \<Rightarrow> bool" where
  "replyNext_same obj1 obj2 \<equiv>
    (case (injectKO obj1, injectKO obj2) of
       (KOReply r1, KOReply r2) \<Rightarrow> replyNext r1 = replyNext r2
      | _ \<Rightarrow> True)"

lemma replyNexts_of_replyNext_same_update:
  "\<And>s'. \<lbrakk>typ_at' ReplyT ptr s'; ksPSpace s' ptr = Some ko;
   koTypeOf (injectKO (ob':: 'a :: pspace_storable)) = ReplyT;
   projectKO_opt ko = Some ab; replyNext_same (ob':: 'a) ab\<rbrakk>
     \<Longrightarrow> replyNexts_of (s'\<lparr>ksPSpace := (ksPSpace s')(ptr \<mapsto> injectKO ob')\<rparr>) = replyNexts_of s'"
  apply (cases "injectKO ob'"; clarsimp simp: typ_at'_def ko_wp_at'_def)
  by (cases ko; fastforce simp add: replyNext_same_def project_inject projectKO_opts_defs opt_map_def)

lemma replyPrevs_of_non_reply_update:
  "\<And>s'. \<lbrakk>typ_at' (koTypeOf ko) ptr s';
   koTypeOf ko \<noteq> ReplyT \<rbrakk>
     \<Longrightarrow> replyPrevs_of (s'\<lparr>ksPSpace := (ksPSpace s')(ptr \<mapsto> ko)\<rparr>) = replyPrevs_of s'"
  by (fastforce simp: typ_at'_def ko_wp_at'_def opt_map_def projectKO_opts_defs
               split: kernel_object.splits)

definition replyPrev_same :: "'a :: pspace_storable \<Rightarrow> 'a \<Rightarrow> bool" where
  "replyPrev_same obj1 obj2 \<equiv>
    (case (injectKO obj1, injectKO obj2) of
       (KOReply r1, KOReply r2) \<Rightarrow> replyPrev r1 = replyPrev r2
      | _ \<Rightarrow> True)"

lemma replyPrevs_of_replyPrev_same_update:
  "\<And>s'. \<lbrakk>typ_at' ReplyT ptr s'; ksPSpace s' ptr = Some ko;
   koTypeOf (injectKO (ob':: 'a :: pspace_storable)) = ReplyT;
   projectKO_opt ko = Some ab; replyPrev_same (ob':: 'a) ab\<rbrakk>
     \<Longrightarrow> replyPrevs_of (s'\<lparr>ksPSpace := (ksPSpace s')(ptr \<mapsto> injectKO ob')\<rparr>) = replyPrevs_of s'"
  apply (cases "injectKO ob'"; clarsimp simp: typ_at'_def ko_wp_at'_def)
  by (cases ko; fastforce simp add: replyPrev_same_def project_inject projectKO_opts_defs opt_map_def)

lemma tcbs_of'_non_tcb_update:
  "\<lbrakk>typ_at' (koTypeOf ko) ptr s'; koTypeOf ko \<noteq> TCBT\<rbrakk>
   \<Longrightarrow> tcbs_of' (s'\<lparr>ksPSpace := (ksPSpace s')(ptr \<mapsto> ko)\<rparr>) = tcbs_of' s'"
  by (fastforce simp: typ_at'_def ko_wp_at'_def opt_map_def projectKO_opts_defs
               split: kernel_object.splits)

lemma typ_at'_koTypeOf:
  "ko_at' ob' ptr b \<Longrightarrow> typ_at' (koTypeOf (injectKO ob')) ptr b"
  by (auto simp: typ_at'_def ko_wp_at'_def obj_at'_def project_inject)

lemmas gen_obj_at_simps =
  obj_at_def obj_at'_def map_to_ctes_upd_other a_type_def gen_objBits_simps

lemma get_reply_corres:
  "corres reply_relation (reply_at ptr) (reply_at' ptr)
     (get_reply ptr) (getReply ptr)"
  apply (rule corres_no_failI)
   apply wp
  apply (simp add: get_simple_ko_def getReply_def get_object_def
                   getObject_def bind_assoc gets_the_def)
  apply (clarsimp simp: in_monad split_def bind_def gets_def get_def return_def
                 dest!: readObject_misc_ko_at')
  apply (clarsimp simp: assert_def fail_def obj_at_def return_def is_reply partial_inv_def)
  apply (clarsimp simp add: state_relation_def pspace_relation_def obj_at'_def)
  apply (drule bspec)
   apply blast
  apply simp
  done

lemma getReply_TCB_corres:
  "corres (=) (reply_at ptr) (reply_at' ptr)
     (get_reply_tcb ptr) (liftM replyTCB (getReply ptr))"
  apply clarsimp
  apply (rule get_reply_corres[THEN corres_rel_imp])
  apply (clarsimp simp: reply_relation_def)
  done

lemma get_sc_corres_size:
  "corres (\<lambda>sc sc'. sc_relation sc n sc')
     (sc_obj_at n ptr) (sc_at' ptr)
     (get_sched_context ptr) (getSchedContext ptr)"
  apply (rule corres_no_failI)
   apply wp
  apply (simp add: get_sched_context_def getSchedContext_def get_object_def
                   getObject_def bind_assoc gets_the_def)
  apply (clarsimp simp: in_monad split_def bind_def gets_def get_def)
  apply (clarsimp simp: assert_def fail_def obj_at_def return_def is_sc_obj
                 split: Structures_A.kernel_object.splits
                 dest!: readObject_misc_ko_at')
  apply (clarsimp simp: state_relation_def pspace_relation_def obj_at'_def)
  apply (drule bspec)
   apply blast
  apply (clarsimp simp: scBits_simps sc_relation_def gen_objBits_simps)
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

\<comment>\<open>`idle_tcb_ps val` asserts that `val` is a pspace_storable value
   which corresponds to an idle TCB.\<close>
definition idle_tcb_ps :: "('a :: pspace_storable) \<Rightarrow> bool" where
  "idle_tcb_ps val \<equiv> (\<exists>tcb. projectKO_opt (injectKO val) = Some tcb \<and> idle_tcb' tcb)"

\<comment>\<open>`idle_sc_ps val` asserts that `val` is a pspace_storable value
   which corresponds to an idle SchedContext.\<close>
definition idle_sc_ps :: "('a :: pspace_storable) \<Rightarrow> bool" where
  "idle_sc_ps val \<equiv> (\<exists>sc. sc_of' (injectKO val) = Some sc \<and> idle_sc' sc)"

lemma setObject_no_0_obj' [wp]:
  "\<lbrace>no_0_obj'\<rbrace> setObject p v \<lbrace>\<lambda>r. no_0_obj'\<rbrace>"
  apply (clarsimp simp: setObject_def split_def)
  apply (clarsimp simp: valid_def no_0_obj'_def ko_wp_at'_def in_monad
                        lookupAround2_char1 ps_clear_upd)
  done

lemma no_ofail_threadRead[simp]:
  "no_ofail (obj_at' (P::tcb \<Rightarrow> bool) p) (threadRead f p)"
  unfolding threadRead_def oliftM_def no_ofail_def
  apply clarsimp
  apply (clarsimp simp: threadRead_def obind_def oliftM_def oreturn_def
                  split: option.split dest!: no_ofailD[OF no_ofail_obj_at'_readObject_tcb])
  done

lemmas no_ofail_threadRead_tcb_at'[wp] = no_ofail_threadRead[where P=\<top>]

lemma threadRead_tcb_at'':
  "bound (threadRead f t s) \<Longrightarrow> tcb_at' t s"
  by (clarsimp simp: threadRead_def oliftM_def elim!: obj_at'_weakenE)

lemmas threadRead_tcb_at' = threadRead_tcb_at''[simplified]

lemma threadRead_tcb_at'_eq:
  "(\<exists>y. threadRead f t s = Some y) = tcb_at' t s"
  apply (intro iffI)
   apply (fastforce elim!: threadRead_tcb_at')
  apply (fastforce intro: no_ofailD[OF no_ofail_threadRead])
  done

lemma ovalid_threadRead:
  "\<lblot>\<lambda>s. tcb_at' t s \<longrightarrow> (\<exists>tcb. ko_at' tcb t s \<and> P (f tcb) s)\<rblot>
   threadRead f t
   \<lblot>P\<rblot>"
  by (clarsimp simp: threadRead_def oliftM_def obind_def obj_at'_def ovalid_def
              dest!: readObject_misc_ko_at' split: option.split_asm)

lemma ovalid_threadRead_sp:
  "\<lblot>P\<rblot> threadRead f ptr \<lblot>\<lambda>rv s. \<exists>tcb :: tcb. ko_at' tcb ptr s \<and> f tcb = rv \<and> P s\<rblot>"
  by (clarsimp simp: threadRead_def oliftM_def obind_def obj_at'_def ovalid_def
              dest!: readObject_misc_ko_at' split: option.split_asm)

lemma no_fail_threadGet [wp]:
  "no_fail (tcb_at' t) (threadGet f t)"
  by (wpsimp simp: threadGet_def wp: no_ofail_gets_the)

lemma no_fail_getThreadState [wp]:
  "no_fail (tcb_at' t) (getThreadState t)"
  by (simp add: getThreadState_def, wp)

lemma no_fail_setObject_tcb [wp]:
  "no_fail (tcb_at' t) (setObject t (t'::tcb))"
  apply (rule no_fail_pre, wp)
   apply (rule ext)+
   apply simp
  apply (simp add: gen_objBits_simps)
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

lemma no_fail_dmo'[wp]:
  "no_fail P f \<Longrightarrow> no_fail (P o ksMachineState) (doMachineOp f)"
  apply (simp add: doMachineOp_def split_def)
  apply wp
  apply (simp add: no_fail_def)
  done

lemma setObject_ko_wp_at:
  fixes v :: "'a :: pspace_storable"
  assumes R: "\<And>ko s y n. (updateObject v ko p y n s)
                   = (updateObject_default v ko p y n s)"
  shows      "\<lbrace>\<lambda>s. obj_at' (\<lambda>x :: 'a. True) p s \<longrightarrow>
                    P (ko_wp_at' (if p = p' then K (P' (injectKO v)) else P')p' s)\<rbrace>
                setObject p v
              \<lbrace>\<lambda>rv s. P (ko_wp_at' P' p' s)\<rbrace>"
  apply (clarsimp simp: setObject_def valid_def in_monad
                        ko_wp_at'_def split_def in_magnitude_check
                        R updateObject_default_def obj_at'_real_def
             split del: if_split)
  apply (clarsimp simp: project_inject objBits_def[symmetric]
                 elim!: rsubst[where P=P]
             split del: if_split)
  apply (rule iffI)
   apply (clarsimp simp: ps_clear_upd objBits_def[symmetric]
                  split: if_split_asm)
  apply (clarsimp simp: project_inject objBits_def[symmetric]
                        ps_clear_upd
                 split: if_split_asm)
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

lemma valid_mdb'_lift:
  "(\<And>P. f \<lbrace>\<lambda>s. P (ctes_of s)\<rbrace>) \<Longrightarrow> f \<lbrace>valid_mdb'\<rbrace>"
  unfolding valid_mdb'_def
  apply simp
  done

lemma setObject_state_refs_of':
  assumes x: "updateObject val = updateObject_default val"
  shows
  "\<lbrace>\<lambda>s. P ((state_refs_of' s) (ptr := refs_of' (injectKO val)))\<rbrace>
   setObject ptr val
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  apply (clarsimp simp: setObject_def valid_def in_monad split_def
                        updateObject_default_def x in_magnitude_check
                 elim!: rsubst[where P=P] del: ext intro!: ext
             split del: if_split cong: option.case_cong if_cong)
  apply (clarsimp simp: state_refs_of'_def objBits_def[symmetric]
                        ps_clear_upd
                  cong: if_cong option.case_cong)
  done

lemma setObject_state_hyp_refs_of':
  assumes x: "updateObject val = updateObject_default val"
  shows
  "\<lbrace>\<lambda>s. P ((state_hyp_refs_of' s) (ptr := hyp_refs_of' (injectKO val)))\<rbrace>
     setObject ptr val
   \<lbrace>\<lambda>rv s. P (state_hyp_refs_of' s)\<rbrace>"
  apply (clarsimp simp: setObject_def valid_def in_monad split_def
                        updateObject_default_def x in_magnitude_check
                 elim!: rsubst[where P=P] del: ext intro!: ext
             split del: if_split cong: option.case_cong if_cong)
  apply (clarsimp simp: state_hyp_refs_of'_def objBits_def[symmetric]
                        ps_clear_upd
                  cong: if_cong option.case_cong)
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

lemmas valid_irq_node_lift =
    hoare_use_eq_irq_node' [OF _ valid_irq_node'_typ_at_lift]

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
  by (clarsimp simp: setObject_def split_def pspace_domain_valid_def valid_def
                     in_monad lookupAround2_char1 updateObject_size
              split: if_split_asm)

lemma obj_at'_ignoring_obj:
  "obj_at' (\<lambda>_ :: 'a :: pspace_storable. P) p s = (obj_at' (\<lambda>_ :: 'a. True) p s \<and> P)"
  by (rule iffI; clarsimp simp: obj_at'_def)

lemma forall_ko_at'_equiv_projection:
  "(\<lambda>s. \<forall>ko::'a::pspace_storable. ko_at' ko p s \<longrightarrow> P ko s) =
   (\<lambda>s. obj_at' (\<lambda>_::'a::pspace_storable. True) p s \<longrightarrow> P (the ((ksPSpace s |> projectKO_opt) p)) s)"
  by (fastforce simp: obj_at'_def opt_map_red)

lemma setObject_typ_at_inv:
  "setObject p v \<lbrace>typ_at' T p'\<rbrace>"
  by (clarsimp simp: setObject_def split_def valid_def typ_at'_def ko_wp_at'_def in_monad
                     lookupAround2_char1 ps_clear_upd updateObject_size updateObject_type)

lemma setObject_typ_at_not:
  "setObject p v \<lbrace>\<lambda>s. \<not> (typ_at' T p' s)\<rbrace>"
  apply (clarsimp simp: setObject_def valid_def in_monad split_def)
  apply (erule notE)
  by (clarsimp simp: typ_at'_def ko_wp_at'_def lookupAround2_char1
                     updateObject_size updateObject_type
              split: if_split_asm
              elim!: ps_clear_domE)
      fastforce+

lemma setObject_typ_at'[wp]:
  "setObject p v \<lbrace>\<lambda>s. P (typ_at' T p' s)\<rbrace>"
  by (blast intro: P_bool_lift setObject_typ_at_inv setObject_typ_at_not)

global_interpretation setObject: gen_typ_at_all_props' "setObject p v"
  by typ_at_props'

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
   apply (erule (1) use_valid[OF _ valid_obj'_typ_at_lift[OF setObject_typ_at' setObject_sc_at'_n]])
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


locale pspace_only' =
  fixes f :: "'a kernel"
  assumes pspace: "(rv, s') \<in> fst (f s) \<Longrightarrow> \<exists>g. s' = ksPSpace_update g s"
begin

lemma it[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace>"
  and ksIdleSC[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksIdleSC s)\<rbrace>"
  and ct[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace>"
  and cur_domain[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace>"
  and l1Bitmap[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksReadyQueuesL1Bitmap s)\<rbrace>"
  and l2Bitmap[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksReadyQueuesL2Bitmap s)\<rbrace>"
  and gsUserPages[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (gsUserPages s)\<rbrace>"
  and gsCNodes[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (gsCNodes s)\<rbrace>"
  and gsUntypedZeroRanges[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (gsUntypedZeroRanges s)\<rbrace>"
  and gsMaxObjectSize[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (gsMaxObjectSize s)\<rbrace>"
  and ksDomSchedule[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace>"
  and ksDomScheduleIdx[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksDomScheduleIdx s)\<rbrace>"
  and ksDomScheduleStart[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (ksDomScheduleStart s)\<rbrace>"
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

lemma sch_act_simple[wp]:
  "f \<lbrace>\<lambda>s. P (sch_act_simple s)\<rbrace>"
  apply (wpsimp wp: ksSchedulerAction simp: sch_act_simple_def)
  done

end

crunch getObject
  for (empty_fail) empty_fail[intro!, wp, simp]

locale simple_ko' =
  fixes f :: "obj_ref \<Rightarrow> 'a::pspace_storable \<Rightarrow> unit kernel"
    and g :: "obj_ref \<Rightarrow> 'a kernel"
  assumes f_def: "f p v = setObject p v"
  assumes g_def: "g p = getObject p"
  assumes default_update: "updateObject (v::'a) = updateObject_default (v::'a)"
  assumes default_load: "(loadObject ptr ptr' next obj :: 'a kernel_r) =
                              loadObject_default ptr ptr' next obj"
  assumes not_cte: "projectKO_opt (KOCTE cte) = (None::'a option)"
begin

lemma updateObject_cte[simp]:
  "fst (updateObject (v::'a) (KOCTE cte) p x n s) = {}"
  by (clarsimp simp: default_update updateObject_default_def in_monad not_cte bind_def)

lemma pspace_aligned'[wp]: "f p v \<lbrace>pspace_aligned'\<rbrace>"
  and pspace_distinct'[wp]: "f p v \<lbrace>pspace_distinct'\<rbrace>"
  and pspace_bounded'[wp]: "f p v \<lbrace>pspace_bounded'\<rbrace>"
  and no_0_obj'[wp]: "f p v \<lbrace>no_0_obj'\<rbrace>"
  and pspace_canonical'[wp]: "f p v \<lbrace>pspace_canonical'\<rbrace>"
  unfolding f_def by (all \<open>wpsimp simp: default_update updateObject_default_def in_monad\<close>)

lemma valid_objs':
  "\<lbrace>valid_objs' and valid_obj' (injectKO v) \<rbrace> f p v \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  unfolding f_def
  by (rule setObject_valid_objs')
     (clarsimp simp: default_update updateObject_default_def in_monad)+

lemma typ_at'[wp]:
  "f p v \<lbrace>\<lambda>s. P (typ_at' T p' s)\<rbrace>"
  unfolding f_def
  by (rule setObject_typ_at')

lemma sc_at'_n[wp]: "f p v \<lbrace>\<lambda>s. P (sc_at'_n n p' s)\<rbrace>"
  unfolding f_def
  by (clarsimp simp: valid_def setObject_def in_monad split_def ko_wp_at'_def ps_clear_upd
                     updateObject_size lookupAround2_char1 updateObject_type)

sublocale gen_typ_at_all_props' "f p v" for p v
  by typ_at_props'

sublocale pspace_only' "f p v" for p v
  unfolding f_def
  by unfold_locales
     (fastforce simp: setObject_def updateObject_default_def magnitudeCheck_def default_update
                      in_monad split_def
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

lemma state_refs_of':
  "\<lbrace>\<lambda>s. P ((state_refs_of' s) (ptr := refs_of' (injectKO val)))\<rbrace>
   f ptr val
   \<lbrace>\<lambda>_ s. P (state_refs_of' s)\<rbrace>"
  unfolding f_def
  by (auto intro: setObject_state_refs_of' simp: default_update)

lemma state_hyp_refs_of':
  "\<lbrace>\<lambda>s. P ((state_hyp_refs_of' s) (ptr := hyp_refs_of' (injectKO val)))\<rbrace>
   f ptr val
   \<lbrace>\<lambda>_ s. P (state_hyp_refs_of' s)\<rbrace>"
  unfolding f_def
  by (auto intro: setObject_state_hyp_refs_of' simp: default_update)

lemmas valid_irq_node'[wp] = valid_irq_node_lift[OF ksInterruptState typ_at']
lemmas irq_states' [wp] = valid_irq_states_lift' [OF ksInterruptState ksMachineState]
lemmas irqs_masked'[wp] = irqs_masked_lift[OF ksInterruptState]

lemma valid_machine_state'[wp]:
  "f p v \<lbrace>valid_machine_state'\<rbrace>"
  unfolding valid_machine_state'_def pointerInDeviceData_def pointerInUserData_def
  by (wp hoare_vcg_all_lift hoare_vcg_disj_lift)

lemma pspace_domain_valid[wp]:
  "f ptr val \<lbrace>pspace_domain_valid\<rbrace>"
  unfolding f_def by (wpsimp simp: default_update updateObject_default_def in_monad)

lemma setObject_wp:
  "\<lbrace>\<lambda>s. P (set_obj' ptr obj s)\<rbrace>
   setObject ptr (obj :: 'a :: pspace_storable)
   \<lbrace>\<lambda>_. P\<rbrace>"
  apply (wpsimp simp: setObject_def default_update updateObject_default_def fun_upd_def)
                                              (* FIXME: this is a simp rule, why isn't it available? *)
  done

lemmas set_wp = setObject_wp[folded f_def]

lemma setObject_pre:
  fixes obj :: 'a
  assumes "\<lbrace>P and obj_at' (\<lambda>old_obj :: 'a. objBits old_obj = objBits obj) p\<rbrace>
           setObject p obj
           \<lbrace>Q\<rbrace>"
  shows "\<lbrace>P\<rbrace> setObject p obj \<lbrace>Q\<rbrace>"
  supply simps = in_magnitude_check[OF _, unfolded objBits_def] valid_def
                 setObject_def in_monad split_def default_update updateObject_default_def
                 project_inject objBits_def
  using assms
  apply (clarsimp simp: simps)
  apply (rename_tac s ko)
  apply (drule_tac x=s in spec)
  apply (clarsimp simp: obj_at'_def split_paired_Ball project_inject)
  apply (erule impE)
   apply fastforce
  apply (drule spec, erule mp)
  apply (fastforce simp: simps)
  done

\<comment>\<open> Keeps the redundant @{term "obj_at \<top>"} precondition because this matches common abbreviations
    like @{term "tcb_at'"}.

    Lets the postcondition pointer depend on the state for things like @{term "ksCurThread"}. \<close>
lemma setObject_obj_at'_strongest:
  fixes obj :: 'a
  shows "\<lbrace>\<lambda>s. obj_at' (\<lambda>_:: 'a. True) ptr s
              \<and> obj_at' (\<lambda>old_obj :: 'a. objBits old_obj = objBits obj) ptr s
              \<longrightarrow> (let s' = set_obj' ptr obj s in
                    Q ((ptr = ptr' s' \<longrightarrow> P s' obj)
                       \<and> (ptr \<noteq> ptr' s' \<longrightarrow> obj_at' (P s') (ptr' s') s)))\<rbrace>
         setObject ptr obj
         \<lbrace>\<lambda>rv s. Q (obj_at' (P s) (ptr' s) s)\<rbrace>"
  apply (rule setObject_pre)
  apply (wpsimp wp: setObject_wp
              simp: Let_def)
  apply (elim impE)
   apply (clarsimp simp: obj_at'_def)
  apply (erule rsubst[where P=Q])
  apply (case_tac "ptr = ptr' (set_obj' ptr obj s)"; simp)
   apply (clarsimp simp: same_size_obj_at'_set_obj'_iff
                         obj_at'_ignoring_obj[where P="P f obj" for f])
  apply (clarsimp simp: obj_at'_def project_inject ps_clear_upd)
  done

lemmas obj_at'_strongest = setObject_obj_at'_strongest[folded f_def]

lemma setObject_obj_at':
  fixes v :: 'a
  shows "\<lbrace>\<lambda>s. obj_at' (\<lambda>_:: 'a. True) p s \<longrightarrow> P (if p = p' then P' v else obj_at' P' p' s)\<rbrace>
         setObject p v
         \<lbrace>\<lambda>rv s. P (obj_at' P' p' s)\<rbrace>"
  by (wpsimp wp: setObject_obj_at'_strongest split: if_splits)

lemmas obj_at' = setObject_obj_at'[folded f_def]

lemma readObject_wp:
  "\<lblot>\<lambda>s. \<forall>ko :: 'a. ko_at' ko p s \<longrightarrow> P ko s\<rblot>
   readObject p
   \<lblot>P\<rblot>"
  apply (wpsimp simp: default_load loadObject_default_def
                      projectKO_def readObject_def  split_def read_magnitudeCheck_def)
  apply (fastforce simp: obj_at'_def project_inject lookupAround2_no_after_ps_clear
                         lookupAround2_known1 objBits_def lookupAround2_after_ps_clear)
  done

lemmas getObject_wp = ovalid_gets_the[OF readObject_wp, simplified getObject_def[symmetric]]

lemma getObject_wp':
  "\<lbrace>\<lambda>s. obj_at' (\<lambda>_::'a. True) p s \<longrightarrow> P (the ((ksPSpace s |> projectKO_opt) p)) s\<rbrace>
   getObject p
   \<lbrace>P::'a \<Rightarrow> _ \<Rightarrow> _\<rbrace>"
  apply (wpsimp wp: getObject_wp)
  by (metis forall_ko_at'_equiv_projection)

lemmas get_wp = getObject_wp[folded g_def]
lemmas get_wp' = getObject_wp'[folded g_def]

lemma loadObject_default_inv:
  "\<lbrace>P\<rbrace> gets_the $ loadObject_default addr addr' next obj \<lbrace>\<lambda>rv. P\<rbrace>"
  by wpsimp

lemma getObject_inv:
  "\<lbrace>P\<rbrace> getObject p \<lbrace>\<lambda>(rv :: 'a). P\<rbrace>"
  by (wpsimp simp: default_load getObject_def split_def wp: loadObject_default_inv)

lemmas get_inv = getObject_inv[folded g_def]

lemma getObject_sp:
  "\<lbrace>P\<rbrace> getObject r \<lbrace>\<lambda>rv::'a. P and ko_at' rv r\<rbrace>"
  apply (clarsimp simp: getObject_def loadObject_default_def default_load
                        in_monad valid_def obj_at'_def project_inject
                        split_def readObject_def omonad_defs
                 split: if_split_asm option.split_asm)
  by (clarsimp simp: objBits_def)

lemmas getObject_sp' = getObject_sp[folded g_def]

lemma setObject_preserves_some_obj_at':
  "\<lbrace>\<lambda>s. obj_at' (\<lambda>_ :: 'a. True) p s \<longrightarrow> P (obj_at' (\<lambda>_ :: 'a. True) p' s)\<rbrace>
   setObject p (ko :: 'a)
   \<lbrace>\<lambda>_ s. P (obj_at' (\<lambda>_ :: 'a. True) p' s)\<rbrace>"
  apply (wpsimp wp: setObject_obj_at'_strongest)
  apply (case_tac "p = p'"; clarsimp)
  done

lemmas set_preserves_some_obj_at' = setObject_preserves_some_obj_at'[folded f_def]

lemma getObject_wp_rv_only:
  "\<lbrace>\<lambda>s. obj_at' (\<lambda>_:: 'a. True) p s \<longrightarrow> obj_at' (\<lambda>ko :: 'a. P ko) p s\<rbrace> getObject p \<lbrace>\<lambda>rv _. P rv\<rbrace>"
  apply (wpsimp wp: getObject_wp)
  apply (clarsimp simp: obj_at'_def)
  done

lemmas get_wp_rv_only = getObject_wp_rv_only[folded g_def]

lemma readObject_wp_state_only:
  "\<lblot>\<lambda>s. obj_at' (\<lambda>_ :: 'a. True) p s \<longrightarrow> P s\<rblot> readObject p \<lblot>\<lambda>_ :: 'a. P\<rblot>"
  apply (wpsimp wp: readObject_wp)
  apply (clarsimp simp: obj_at'_def)
  done

\<comment>\<open> Stronger than getObject_inv. \<close>
lemmas getObject_wp_state_only =
  ovalid_gets_the[OF readObject_wp_state_only, simplified getObject_def[symmetric]]

lemmas get_wp_state_only = getObject_wp_state_only[folded g_def]

lemma setObject_no_update:
  assumes [simp]: "\<And>ko :: 'a. Q (upd ko) = Q ko"
  shows
  "\<lbrace>\<lambda>s. P (obj_at' Q p' s) \<and> ko_at' ko p s\<rbrace>
   setObject p (upd ko)
   \<lbrace>\<lambda>_ s. P (obj_at' Q p' s)\<rbrace>"
  apply (wpsimp wp: setObject_obj_at'_strongest)
  apply (case_tac "p = p'"; clarsimp simp: obj_at'_def)
  done

lemmas set_no_update = setObject_no_update[folded f_def]

lemmas getObject_ko_at' = getObject_ko_at[OF default_load]

lemmas get_ko_at' = getObject_ko_at'[folded g_def]

lemmas ko_wp_at = setObject_ko_wp_at[where 'a='a, folded f_def,
                                     simplified default_update, simplified]

lemma setObject_ko_at':
  "\<lbrace>\<lambda>s. obj_at' (\<lambda>_ :: 'a. True) p s \<longrightarrow>
          (p = p' \<longrightarrow> P (ko = ko')) \<and>
          (p \<noteq> p' \<longrightarrow> P (ko_at' ko' p' s))\<rbrace>
   setObject p (ko :: 'a)
   \<lbrace>\<lambda>_ s. P (ko_at' (ko' :: 'a) p' s)\<rbrace>"
  apply (wpsimp wp: obj_at'_strongest[unfolded f_def])
  apply (case_tac "p = p'"; clarsimp simp: obj_at'_def)
  done

lemmas set_ko_at' = setObject_ko_at'[folded f_def]

lemma setObject_noop_rewrite:
  fixes obj :: 'a
  assumes "(1 :: machine_word) < 2 ^ objBits obj"
  shows "monadic_rewrite False True (ko_at' obj ptr) (setObject ptr obj) (return ())"
        (is "monadic_rewrite _ _ ?Q _ _")
  apply (rule monadic_rewrite_guard_imp)
   apply (rule monadic_rewrite_trans)
    apply (rule setObject_modify_variable_size_rewrite)
     apply (fastforce simp: default_update)
    apply (fastforce simp: assms)
   apply (rule monadic_rewrite_noop[where Q="?Q"])
     apply wpsimp
     apply (rename_tac P s)
     apply (erule_tac P=P in rsubst)
     apply (case_tac s; clarsimp)
     apply (fastforce simp: obj_at'_def project_inject)
    apply wpsimp
   apply wpsimp
  apply (fastforce simp: obj_at'_def)
  done

lemma no_ofail_readyObject:
  "no_ofail (obj_at' (P::'a::pspace_storable \<Rightarrow> bool) p) (readObject p :: 'a kernel_r)"
  apply (clarsimp simp: readObject_def obj_at'_def RISCV64_H.fromPPtr_def (* FIXME: arch split *)
                        obind_def omonad_defs split_def no_ofail_def)
  apply (erule (1) ps_clear_lookupAround2, simp+)
   apply (blast intro: is_aligned_no_overflow)
  apply (clarsimp split: option.splits)
   apply (rule context_conjI)
    apply (frule lookupAround2_known1)
    apply fastforce
   apply (force dest: lookupAround2_known1
                simp: default_load obind_def gen_objBits_simps project_inject)
  apply (rule context_conjI)
   apply (frule lookupAround2_known1)
   apply fastforce
  apply (force dest: lookupAround2_known1
               simp: default_load obind_def gen_objBits_simps project_inject)
  done

lemma no_fail_getObject:
  "no_fail (obj_at' (P::'a::pspace_storable \<Rightarrow> bool) p) (getObject p::'a kernel)"
  apply (clarsimp simp: getObject_def)
  apply (rule no_ofail_gets_the)
  apply (rule no_ofail_readyObject)
  done

lemma getObject_return_rewrite:
  "monadic_rewrite False True (ko_at' (obj::'a) ptr) (getObject ptr) (return obj)"
  apply (rule monadic_rewrite_add_return_l)
  apply (rule monadic_rewrite_guard_imp)
   apply (rule monadic_rewrite_symb_exec_l')
       apply (rule monadic_rewrite_guard_arg_cong)
       apply fastforce
      apply (rule getObject_inv)
     apply wpsimp
    apply clarsimp
    apply (rule no_fail_getObject)
   apply (wpsimp wp: getObject_wp)
  apply (fastforce simp: obj_at'_def)
  done

abbreviation (input) updateKernelObject :: "('a \<Rightarrow> 'a) \<Rightarrow> machine_word \<Rightarrow> unit kernel" where
  "updateKernelObject upd ptr \<equiv> do
     obj \<leftarrow> getObject ptr;
     setObject ptr (upd obj)
   od"

lemma updateKernelObject_unbundle:
  fixes obj :: 'a
  assumes "\<And>v :: 'a. objBits (upd_1 v) = objBits v"
  assumes "\<And>v :: 'a. objBits (upd_2 v) = objBits v"
  shows "monadic_rewrite False True \<top>
           (updateKernelObject (upd_2 o upd_1) ptr)
           (do updateKernelObject upd_1 ptr;
               updateKernelObject upd_2 ptr
            od)"
  apply (insert assms)
  apply (clarsimp simp: bind_assoc)
  apply (rule monadic_rewrite_guard_imp)
   \<comment> \<open>getObject at the start of both sides; match and rename to obj\<close>
   apply (rule monadic_rewrite_bind_tail)
    apply (rename_tac obj)
    apply (rule_tac P="(1 :: machine_word) < 2 ^ objBits obj" in monadic_rewrite_gen_asm)
    \<comment> \<open>rewrite setObject on the LHS\<close>
    apply (rule monadic_rewrite_trans)
     apply (fastforce intro: setObject_modify_rewrite simp: assms default_update)
    \<comment> \<open>rewrite setObject at the start on the RHS\<close>
    apply (rule monadic_rewrite_transverse)
     apply (rule monadic_rewrite_bind_head)
     apply (fastforce intro: setObject_modify_rewrite simp: assms default_update)
    \<comment> \<open>rewrite getObject in the middle of the RHS\<close>
    apply (rule monadic_rewrite_transverse)
     apply (rule monadic_rewrite_bind_tail)
      apply (rule monadic_rewrite_bind_head)
      apply (rule_tac obj="upd_1 obj" in getObject_return_rewrite)
     apply wpsimp
    \<comment> \<open>rewrite setObject at the end on the RHS\<close>
    apply (rule monadic_rewrite_transverse)
     apply (rule monadic_rewrite_bind_tail)
      apply (rule monadic_rewrite_bind_tail)
       apply (rename_tac obj')
       apply (rule_tac P="(1 :: machine_word) < 2 ^ objBits obj'" in monadic_rewrite_gen_asm)
       apply (fastforce intro: setObject_modify_rewrite simp: assms default_update)
      apply wpsimp
     apply wpsimp
    \<comment> \<open>the getObject is now a return; use @{thm return_bind}\<close>
    apply clarsimp
    apply (rule monadic_rewrite_transverse)
     \<comment> \<open>rewrite as one @{const modify}\<close>
     apply (subst modify_modify)
     apply (rule monadic_rewrite_refl)
    apply (fastforce intro: monadic_rewrite_guard_arg_cong[where P=\<top>]
                      simp: comp_def simp flip: fun_upd_def)
   apply (wpsimp wp: getObject_wp)
  apply (force simp: project_inject obj_at'_def objBits_def simp flip: fun_upd_def unfold_set_ko')
  done

lemmas updateKernelObect_bundle = monadic_rewrite_sym[OF updateKernelObject_unbundle]

lemmas updateKernelObect_bundle_eq = monadic_rewrite_to_eq[OF updateKernelObject_unbundle]

end

locale simple_non_tcb_ko' = simple_ko' "f:: obj_ref \<Rightarrow> 'a::pspace_storable \<Rightarrow> unit kernel"
                                       "g:: obj_ref \<Rightarrow> 'a kernel" for f g +
  assumes not_tcb: "projectKO_opt (KOTCB sc) = (None :: 'a option)"
begin

lemma updateObject_tcb[simp]:
  "fst (updateObject (v::'a) (KOTCB tcb) p x n s) = {}"
  by (clarsimp simp: default_update updateObject_default_def in_monad not_tcb bind_def)

lemma not_inject_tcb[simp]:
  "injectKO (v::'a) \<noteq> KOTCB tcb"
  by (simp flip: project_inject add: not_tcb)

lemma typeOf_not_tcb[simp]:
  "koTypeOf (injectKO (v::'a)) \<noteq> TCBT"
  by (cases "injectKO v"; simp)

lemma cte_wp_at'[wp]: "f p v \<lbrace>\<lambda>s. P (cte_wp_at' Q p' s)\<rbrace>"
  unfolding f_def by (rule setObject_cte_wp_at2'[where Q="\<top>", simplified]; simp)

lemma obj_at_tcb'[wp]:
  "f p v \<lbrace>\<lambda>s. P (obj_at' (Q :: tcb \<Rightarrow> bool) p' s)\<rbrace>"
  unfolding f_def obj_at'_real_def
  apply (wp setObject_ko_wp_at; simp add: default_update)
  apply (clarsimp simp: obj_at'_def ko_wp_at'_def)
  apply (case_tac ko; simp add: not_tcb)
  done

lemma valid_bitmaps[wp]:
  "f p v \<lbrace>valid_bitmaps\<rbrace>"
  by (wpsimp wp: valid_bitmaps_lift)

lemma pred_tcb_at'[wp]:
  "f p v \<lbrace> \<lambda>s. Q (pred_tcb_at' proj P t s) \<rbrace>"
  unfolding pred_tcb_at'_def by wp

lemma cap_to'[wp]:
  "f p' v \<lbrace>ex_nonz_cap_to' p\<rbrace>"
  by (wp ex_nonz_cap_to_pres')

end

locale simple_non_reply_ko' = simple_ko' "f:: obj_ref \<Rightarrow> 'a::pspace_storable \<Rightarrow> unit kernel"
                                         "g:: obj_ref \<Rightarrow> 'a kernel" for f g +
  assumes not_reply: "projectKO_opt (KOReply reply) = (None :: 'a option)"
begin

lemma updateObject_reply[simp]:
  "fst (updateObject (v::'a) (KOReply c) p x n s) = {}"
  by (clarsimp simp: default_update updateObject_default_def in_monad not_reply bind_def)

lemma not_inject_reply[simp]:
  "injectKO (v::'a) \<noteq> KOReply sc"
  by (simp flip: project_inject add: not_reply)

lemma typeOf_not_reply[simp]:
  "koTypeOf (injectKO (v::'a)) \<noteq> ReplyT"
  by (cases "injectKO v"; simp)

end

locale simple_non_tcb_non_reply_ko' =
   simple_non_reply_ko' "f:: obj_ref \<Rightarrow> 'a::pspace_storable \<Rightarrow> unit kernel"
                        "g:: obj_ref \<Rightarrow> 'a kernel" +
   simple_non_tcb_ko' "f:: obj_ref \<Rightarrow> 'a::pspace_storable \<Rightarrow> unit kernel"
                      "g:: obj_ref \<Rightarrow> 'a kernel" for f g
begin

\<comment>\<open> preservation of valid_replies' requires us to not be touching either of a Reply or a TCB \<close>

lemma valid_replies'[wp]:
  "\<lbrace>valid_replies' and pspace_distinct' and pspace_aligned'\<rbrace>
   f p v
   \<lbrace>\<lambda>_. valid_replies'\<rbrace>"
   (is "\<lbrace>?pre valid_replies'\<rbrace> _ \<lbrace>?post\<rbrace>")
  apply (rule_tac Q'="\<lambda>_. ?pre valid_replies'_alt" in hoare_post_imp;
         clarsimp simp: valid_replies'_def2)
  unfolding obj_at'_real_def
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift ko_wp_at hoare_vcg_ex_lift)
  by (fastforce simp: valid_replies'_def2 obj_at'_def ko_wp_at'_def)

end

locale simple_non_sc_ko' = simple_ko' "f:: obj_ref \<Rightarrow> 'a::pspace_storable \<Rightarrow> unit kernel"
                                      "g:: obj_ref \<Rightarrow> 'a kernel" for f g +
  assumes not_sc: "projectKO_opt (KOSchedContext sc) = (None :: 'a option)"
begin

lemma updateObject_sc[simp]:
  "fst (updateObject (v::'a) (KOSchedContext c) p x n s) = {}"
  by (clarsimp simp: default_update updateObject_default_def in_monad not_sc bind_def)

lemma not_inject_sc[simp]:
  "injectKO (v::'a) \<noteq> KOSchedContext sc"
  by (simp flip: project_inject add: not_sc)

lemma typeOf_not_sc[simp]:
  "koTypeOf (injectKO (v::'a)) \<noteq> SchedContextT"
  by (cases "injectKO v"; simp)

end

locale simple_non_tcb_non_sc_ko' =
   simple_non_sc_ko' "f:: obj_ref \<Rightarrow> 'a::pspace_storable \<Rightarrow> unit kernel"
                     "g:: obj_ref \<Rightarrow> 'a kernel" +
   simple_non_tcb_ko' "f:: obj_ref \<Rightarrow> 'a::pspace_storable \<Rightarrow> unit kernel"
                      "g:: obj_ref \<Rightarrow> 'a kernel" for f g

locale simple_non_tcb_non_sc_non_reply_ko' =
   simple_non_tcb_non_sc_ko' "f:: obj_ref \<Rightarrow> 'a::pspace_storable \<Rightarrow> unit kernel"
                             "g:: obj_ref \<Rightarrow> 'a kernel" +
   simple_non_tcb_non_reply_ko' "f:: obj_ref \<Rightarrow> 'a::pspace_storable \<Rightarrow> unit kernel"
                             "g:: obj_ref \<Rightarrow> 'a kernel" for f g

(* FIXME: should these be in Arch + sublocale instead? *)
interpretation set_ep': simple_non_tcb_non_sc_non_reply_ko' setEndpoint getEndpoint
  by unfold_locales (simp_all add: setEndpoint_def getEndpoint_def projectKO_opts_defs
                                   gen_objBits_simps)

interpretation set_ntfn': simple_non_tcb_non_sc_non_reply_ko' setNotification getNotification
  by unfold_locales (simp_all add: setNotification_def getNotification_def projectKO_opts_defs
                                   gen_objBits_simps)

interpretation set_reply': simple_non_tcb_non_sc_ko' setReply getReply
  by unfold_locales (simp_all add: setReply_def getReply_def projectKO_opts_defs gen_objBits_simps)

interpretation set_sc': simple_non_tcb_non_reply_ko' setSchedContext getSchedContext
  by unfold_locales (simp_all add: setSchedContext_def getSchedContext_def projectKO_opts_defs
                                   gen_objBits_simps)

interpretation set_tcb': simple_non_sc_ko' "\<lambda>p v. setObject p (v::tcb)"
                                           "\<lambda>p. getObject p :: tcb kernel"
  by unfold_locales (simp_all add: projectKO_opts_defs gen_objBits_simps)

lemma threadSet_pspace_only':
   "pspace_only' (threadSet f p)"
  unfolding threadSet_def
  apply unfold_locales
  apply (clarsimp simp: in_monad)
  apply (drule_tac P="(=) s" in use_valid[OF _ getObject_tcb_inv], rule refl)
  apply (fastforce dest: set_tcb'.pspace)
  done

interpretation threadSet: pspace_only' "threadSet f p"
   by (simp add: threadSet_pspace_only')

interpretation setBoundNotification: pspace_only' "setBoundNotification ntfnPtr tptr"
   by (simp add: setBoundNotification_def threadSet_pspace_only')

lemma updateSchedContext_decompose:
  "\<lbrakk>\<And>sc. objBits (g sc) = objBits sc; \<And>sc. objBits (f sc) = objBits sc\<rbrakk>
   \<Longrightarrow> monadic_rewrite False True (sc_at' scPtr)
         (updateSchedContext scPtr (g o f))
         (do updateSchedContext scPtr f;
             updateSchedContext scPtr g
          od)"
  apply (clarsimp simp: bind_assoc updateSchedContext_def getSchedContext_def setSchedContext_def)
  apply (rule monadic_rewrite_guard_imp)
   apply (subst bind_dummy_ret_val)+
   apply (rule set_sc'.updateKernelObject_unbundle[simplified bind_assoc comp_def])
    apply (clarsimp simp: gen_objBits_simps scBits_simps)+
  done

lemmas setNotification_cap_to'[wp]
    = ex_cte_cap_to'_pres [OF set_ntfn'.cte_wp_at' set_ntfn'.ksInterruptState]

lemmas setEndpoint_cap_to'[wp]
    = ex_cte_cap_to'_pres [OF set_ep'.cte_wp_at' set_ep'.ksInterruptState]

(* aliases for compatibility with master *)

lemmas setObject_ep_pre = set_ep'.setObject_pre
lemmas setObject_ntfn_pre = set_ntfn'.setObject_pre
lemmas setObject_tcb_pre = set_tcb'.setObject_pre
lemmas setObject_reply_pre = set_reply'.setObject_pre
lemmas setObject_sched_context_pre = set_sc'.setObject_pre

lemmas getEndpoint_wp = set_ep'.get_wp
lemmas getNotification_wp = set_ntfn'.get_wp
lemmas getTCB_wp = set_tcb'.get_wp
lemmas getReply_wp[wp] = set_reply'.get_wp
lemmas getSchedContext_wp[wp] = set_sc'.get_wp

lemmas getEndpoint_wp' = set_ep'.get_wp'
lemmas getNotification_wp' = set_ntfn'.get_wp'
lemmas getTCB_wp' = set_tcb'.get_wp'
lemmas getReply_wp' = set_reply'.get_wp'
lemmas getSchedContext_wp' = set_sc'.get_wp'

lemmas getObject_ep_inv = set_ep'.getObject_inv
lemmas getObject_ntfn_inv = set_ntfn'.getObject_inv
lemmas getObject_reply_inv = set_reply'.getObject_inv
lemmas getObject_sc_inv = set_sc'.getObject_inv
(* FIXME RT: the one below is deferred because it requires to
   move the simple_ko' locale at the beginning of this theory
   which turns out to be quite a lot more work *)
(*lemmas getObject_tcb_inv = set_tcb'.getObject_inv*)

lemmas get_ep_inv'[wp] = set_ep'.get_inv
lemmas get_ntfn_inv'[wp] = set_ntfn'.get_inv
lemmas get_tcb_inv' = set_tcb'.get_inv
lemmas get_reply_inv' = set_reply'.get_inv
lemmas get_sc_inv' = set_sc'.get_inv

lemmas get_ep_sp' = set_ep'.getObject_sp'
lemmas get_ntfn_sp' = set_ntfn'.getObject_sp'
lemmas get_tcb_sp' = set_tcb'.getObject_sp'
lemmas get_reply_sp' = set_reply'.getObject_sp'
lemmas get_sc_sp' = set_sc'.getObject_sp'

lemmas setObject_tcb_wp = set_tcb'.setObject_wp
lemmas setObject_sc_wp = set_sc'.setObject_wp
lemmas setObject_tcb_obj_at'_strongest = set_tcb'.setObject_obj_at'_strongest

lemmas set_ep_valid_objs'[wp] =
  set_ep'.valid_objs'[simplified valid_obj'_def pred_conj_def, simplified]

lemmas set_ntfn_valid_objs'[wp] =
  set_ntfn'.valid_objs'[simplified valid_obj'_def pred_conj_def, simplified]

lemmas set_reply_valid_objs'[wp] =
  set_reply'.valid_objs'[simplified valid_obj'_def pred_conj_def, simplified]

lemmas set_sc_valid_objs'[wp] =
  set_sc'.valid_objs'[simplified valid_obj'_def pred_conj_def, simplified]

lemma setObject_gen_obj_at:
  fixes v :: "'a :: pspace_storable"
  assumes R: "\<And>ko s y n. updateObject v ko p y n s = updateObject_default v ko p y n s"
  assumes o: "\<lbrace>\<lambda>s. obj_at' (\<lambda>x :: 'a. True) p s \<and> P s\<rbrace> setObject p v \<lbrace>Q\<rbrace>"
  shows      "\<lbrace>P\<rbrace> setObject p v \<lbrace>Q\<rbrace>"
  using o
  apply (clarsimp simp: valid_def setObject_def in_monad R
                        split_def updateObject_default_def
                        in_magnitude_check split_paired_Ball)
  apply (drule spec, drule mp, erule conjI[rotated])
   apply (simp add: obj_at'_def objBits_def project_inject)
   apply metis
  apply (simp add: split_paired_Ball)
  apply (drule spec, erule mp)
  apply (clarsimp simp: in_monad in_magnitude_check)
  done

lemma state_hyp_refs_of'_ep:
  "ep_at' epptr s \<Longrightarrow> (state_hyp_refs_of' s)(epptr := {}) = state_hyp_refs_of' s"
  by (rule ext) (clarsimp simp: state_hyp_refs_of'_def obj_at'_def)

lemma set_ep_state_hyp_refs_of'[wp]:
  "setEndpoint epptr ep \<lbrace>\<lambda>s. P (state_hyp_refs_of' s)\<rbrace>"
  unfolding setEndpoint_def
  apply (rule setObject_gen_obj_at, simp)
  apply (wp setObject_state_hyp_refs_of'; simp add: gen_objBits_simps state_hyp_refs_of'_ep)
  done

lemma state_hyp_refs_of'_ntfn:
  "ntfn_at' ntfn s \<Longrightarrow> (state_hyp_refs_of' s) (ntfn := {}) = state_hyp_refs_of' s"
  by (rule ext) (clarsimp simp: state_hyp_refs_of'_def obj_at'_def)

lemma set_ntfn_state_hyp_refs_of'[wp]:
  "setNotification epptr ntfn \<lbrace>\<lambda>s. P (state_hyp_refs_of' s)\<rbrace>"
  unfolding setNotification_def
  apply (rule setObject_gen_obj_at, simp)
  apply (wp setObject_state_hyp_refs_of'; simp add: gen_objBits_simps state_hyp_refs_of'_ntfn)
  done

lemma setSchedContext_state_refs_of'[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of' s)(p := get_refs SCNtfn (scNtfn sc) \<union>
                                   get_refs SCTcb (scTCB sc) \<union>
                                   get_refs SCYieldFrom (scYieldFrom sc) \<union>
                                   get_refs SCReply (scReply sc)))\<rbrace>
   setSchedContext p sc
   \<lbrace>\<lambda>_ s. P (state_refs_of' s)\<rbrace>"
  by (wp set_sc'.state_refs_of') (simp flip: fun_upd_def)

lemma state_hyp_refs_of'_sc:
  "sc_at' sc s \<Longrightarrow> (state_hyp_refs_of' s) (sc := {}) = state_hyp_refs_of' s"
  by (rule ext) (clarsimp simp: state_hyp_refs_of'_def obj_at'_def)

lemma set_sc_state_hyp_refs_of'[wp]:
  "setSchedContext p reply \<lbrace>\<lambda>s. P (state_hyp_refs_of' s)\<rbrace>"
  unfolding setSchedContext_def
  apply (rule setObject_gen_obj_at, simp)
  apply (wp setObject_state_hyp_refs_of'; simp add: gen_objBits_simps state_hyp_refs_of'_sc)
  done

lemma setReply_state_refs_of'[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of' s)(p := get_refs ReplySchedContext (replySC reply) \<union>
                                   get_refs ReplyTCB (replyTCB reply)))\<rbrace>
   setReply p reply
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  by (wp set_reply'.state_refs_of') (simp flip: fun_upd_def)

lemma state_hyp_refs_of'_reply:
  "reply_at' reply s \<Longrightarrow> (state_hyp_refs_of' s) (reply := {}) = state_hyp_refs_of' s"
  by (rule ext) (clarsimp simp: state_hyp_refs_of'_def obj_at'_def)

lemma set_reply_state_hyp_refs_of'[wp]:
  "setReply p reply \<lbrace>\<lambda>s. P (state_hyp_refs_of' s)\<rbrace>"
  unfolding setReply_def
  apply (rule setObject_gen_obj_at, simp)
  apply (wp setObject_state_hyp_refs_of'; simp add: gen_objBits_simps state_hyp_refs_of'_reply)
  done

lemma setReply_reply_projs[wp]:
  "\<lbrace>\<lambda>s. P ((replyNexts_of s)(rptr := replyNext_of reply))
          ((replyPrevs_of s)(rptr := replyPrev reply))
          ((replyTCBs_of s)(rptr := replyTCB reply))
          ((replySCs_of s)(rptr := replySC reply))\<rbrace>
   setReply rptr reply
   \<lbrace>\<lambda>_ s. P (replyNexts_of s) (replyPrevs_of s) (replyTCBs_of s) (replySCs_of s)\<rbrace>"
  apply (wpsimp simp: setReply_def updateObject_default_def setObject_def split_def)
  apply (erule rsubst4[where P=P])
     apply (clarsimp simp: ext opt_map_def list_refs_of_reply'_def map_set_def projectKO_opt_reply
                    split: option.splits)+
  done

lemma updateReply_wp_all:
  "\<lbrace>\<lambda>s. \<forall>ko. ko_at' ko rptr s \<longrightarrow> P (set_obj' rptr (upd ko) s)\<rbrace>
   updateReply rptr upd
   \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding updateReply_def
  apply (wpsimp wp: set_reply'.set_wp)
  done

lemma setReply_list_refs_of_replies'[wp]:
  "\<lbrace>\<lambda>s. P ((list_refs_of_replies' s)(p := list_refs_of_reply' reply))\<rbrace>
   setReply p reply
   \<lbrace>\<lambda>_ s. P (list_refs_of_replies' s)\<rbrace>"
  apply (wpsimp simp: setReply_def)
  apply (erule arg_cong[where f=P, THEN iffD1, rotated])
  apply (rule ext)
  apply (clarsimp simp: opt_map_def map_set_def)
  done

lemma setObject_ksPSpace_only:
  "\<lbrakk> \<And>p q n ko. updateObject val p q n ko \<lbrace>P\<rbrace>;
        \<And>f s. P (ksPSpace_update f s) = P s \<rbrakk>
     \<Longrightarrow> setObject ptr val \<lbrace>P\<rbrace>"
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

lemma setObject_tcb_pre':
  "\<lbrace>P and tcb_at' p\<rbrace> setObject p (t::tcb) \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> setObject p (t::tcb) \<lbrace>Q\<rbrace>"
  apply (rule setObject_tcb_pre)
  apply (clarsimp simp: valid_def setObject_def in_monad
                        split_def updateObject_default_def
                        in_magnitude_check gen_objBits_simps)
  done

lemma setObject_at_pre_default:
  assumes pre: "\<lbrace>P and obj_at' (\<lambda>_::'a. True) p\<rbrace> setObject p (v::'a::pspace_storable) \<lbrace>Q\<rbrace>"
  assumes R: "\<And>ko s y n. updateObject v ko p y n s = updateObject_default v ko p y n s"
  shows "\<lbrace>P\<rbrace> setObject p v \<lbrace>Q\<rbrace>"
  using pre
  apply (clarsimp simp: valid_def setObject_def in_monad R
                        split_def updateObject_default_def
                        in_magnitude_check split_paired_Ball)
  apply (drule spec, drule mp, erule conjI)
   apply (simp add: obj_at'_def objBits_def project_inject)
   apply metis
  apply (simp add: split_paired_Ball)
  apply (drule spec, erule mp)
  apply (clarsimp simp: in_monad in_magnitude_check)
  done

lemma setObject_pspace_no_overlap':
  assumes R: "\<And>ko s y n. updateObject v ko p y n s = updateObject_default v ko p y n s"
  shows "setObject p (v::'a::pspace_storable) \<lbrace>pspace_no_overlap' w s\<rbrace>"
  apply (clarsimp simp: setObject_def split_def valid_def in_monad R objBits_def
                        updateObject_default_def in_magnitude_check)
  apply (fastforce simp: pspace_no_overlap'_def project_inject)
  done

lemma setObject_tcb_pspace_no_overlap':
  "setObject t (tcb::tcb) \<lbrace>pspace_no_overlap' w s\<rbrace>"
  by (rule setObject_pspace_no_overlap')
     (clarsimp simp: setObject_def)

lemma sym_heap_sched_pointers_lift:
  assumes prevs: "\<And>P. f \<lbrace>\<lambda>s. P (tcbSchedPrevs_of s)\<rbrace>"
  assumes nexts: "\<And>P. f \<lbrace>\<lambda>s. P (tcbSchedNexts_of s)\<rbrace>"
  shows "f \<lbrace>sym_heap_sched_pointers\<rbrace>"
  by (rule_tac f=tcbSchedPrevs_of in hoare_lift_Pf2; wpsimp wp: assms)

lemma endpoint_live':
  "\<lbrakk>ko_at' ep ptr s; epState ep \<noteq> IdleEPState\<rbrakk> \<Longrightarrow> ko_wp_at' live' ptr s"
  by (clarsimp simp: live'_def ko_wp_at'_def obj_at'_def)

crunch updateEndpoint, updateNotification, updateSchedContext, updateReply
  for tcbs_of'[wp]: "\<lambda>s. P (tcbs_of' s)"
  (simp: getEndpoint_def wp: set_ep'.getObject_wp)

crunch threadSet, updateNotification, updateSchedContext, updateReply
  for eps_of'[wp]: "\<lambda>s. P (eps_of' s)"
  (simp: getEndpoint_def)

crunch threadSet, updateEndpoint, updateSchedContext, updateReply
  for ntfns_of'[wp]: "\<lambda>s. P (ntfns_of' s)"
  (simp: getEndpoint_def wp: set_ep'.getObject_wp)

crunch threadSet, updateEndpoint, updateNotification, updateReply
  for scs_of'[wp]: "\<lambda>s. P (scs_of' s)"
  (simp: getEndpoint_def wp: set_ep'.getObject_wp)

crunch threadSet, updateEndpoint, updateNotification, updateSchedContext
  for replies_of'[wp]: "\<lambda>s. P (replies_of' s)"
  (simp: getEndpoint_def wp: set_ep'.getObject_wp)

crunch threadSet, updateEndpoint, updateNotification, updateSchedContext, updateReply
  for aobjs_of'[wp]: "\<lambda>s. P (aobjs_of' s)"
  (simp: getEndpoint_def wp: set_ep'.getObject_wp)

crunch threadSet, updateEndpoint, updateNotification, updateSchedContext, updateReply
  for cnode_ctes_of'[wp]: "\<lambda>s. P (cnode_ctes_of' s)"
  and userDataDevice_at[wp]: "\<lambda>s. P (userDataDevice_at s)"
  and userData_at[wp]: "\<lambda>s. P (userData_at s)"
  and kernelData_at[wp]: "\<lambda>s. P (kernelData_at s)"

crunch setCTE
  for replies_of'[wp]: "\<lambda>s. P (replies_of' s)"
  and tcbSchedPrevs_of[wp]: "\<lambda>s. P (tcbSchedPrevs_of s)"
  and tcbSchedNexts_of[wp]: "\<lambda>s. P (tcbSchedNexts_of s)"
  and tcbInReleaseQueue[wp]: "\<lambda>s. P (tcbInReleaseQueue |< tcbs_of' s)"
  and tcbQueued[wp]: "\<lambda>s. P (tcbQueued |< tcbs_of' s)"
  and inQ_tcbs_of'[wp]: "\<lambda>s. P (inQ d p |< tcbs_of' s)"

lemma threadSet_wp:
  "\<lbrace>\<lambda>s. \<forall>tcb :: tcb. ko_at' tcb t s \<longrightarrow> P (set_obj' t (f tcb) s)\<rbrace>
   threadSet f t
   \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding threadSet_def
  apply (wpsimp wp: setObject_tcb_wp set_tcb'.getObject_wp)
  done

lemma threadSet_dom_tcbs_of'[wp]:
  "threadSet f tcbPtr \<lbrace>\<lambda>s. P (dom (tcbs_of' s))\<rbrace>"
  apply (wpsimp wp: threadSet_wp)
  apply (fastforce elim: rsubst[where P=P] simp: opt_map_def obj_at'_def)
  done

lemma updateEndpoint_wp:
  "\<lbrace>\<lambda>s. \<forall>ep :: endpoint. ko_at' ep epPtr s \<longrightarrow> P (set_obj' epPtr (f ep) s)\<rbrace>
   updateEndpoint epPtr f
   \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding updateEndpoint_def setEndpoint_def
  by (wpsimp wp: set_ep'.setObject_wp getEndpoint_wp)

lemma updateEndpoint_dom_eps_of'[wp]:
  "updateEndpoint a b \<lbrace>\<lambda>s. P (dom (eps_of' s))\<rbrace>"
  apply (wpsimp wp: updateEndpoint_wp)
  apply (fastforce elim!: rsubst[where P=P] simp: projectKO_opts_defs obj_at'_def opt_map_red)
  done

lemma updateNotification_wp:
  "\<lbrace>\<lambda>s. \<forall>ntfn :: notification. ko_at' ntfn ntfnPtr s \<longrightarrow> P (set_obj' ntfnPtr (f ntfn) s)\<rbrace>
   updateNotification ntfnPtr f
   \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding updateNotification_def setNotification_def
  by (wpsimp wp: set_ntfn'.setObject_wp getNotification_wp)

lemma updateReply_dom_replies_of'[wp]:
  "updateReply ptr f \<lbrace>\<lambda>s. P (dom (replies_of' s))\<rbrace>"
  apply (wpsimp wp: updateReply_wp_all)
  apply (fastforce elim!: rsubst[where P=P] simp: projectKO_opts_defs obj_at'_def opt_map_red)
  done

lemma aligned_distinct_obj_atI':
  "\<lbrakk> ksPSpace s x = Some ko; pspace_aligned' s; pspace_distinct' s; pspace_bounded' s; ko = injectKO v \<rbrakk>
      \<Longrightarrow> ko_at' v x s"
  apply (simp add: obj_at'_def project_inject pspace_distinct'_def pspace_aligned'_def)
  apply (drule bspec, erule domI)+
  apply (clarsimp simp: pspace_boundedD')
  done

lemma aligned'_distinct'_ko_wp_at'I:
  "\<lbrakk>ksPSpace s' x = Some ko; P ko; pspace_aligned' s'; pspace_distinct' s';
    if koTypeOf ko  = SchedContextT then pspace_bounded' s' else True\<rbrakk>
   \<Longrightarrow> ko_wp_at' P x s'"
  apply (simp add: ko_wp_at'_def pspace_distinct'_def pspace_aligned'_def)
  apply (drule bspec, erule domI)+
  apply (cases ko; force simp: valid_sz_simps pspace_bounded'_def)
  done

lemma aligned'_distinct'_ko_at'I:
  "\<lbrakk>ksPSpace s' x = Some ko;  pspace_aligned' s'; pspace_distinct' s';
    if koTypeOf ko  = SchedContextT then pspace_bounded' s' else True;
    ko = injectKO (v:: 'a :: pspace_storable)\<rbrakk>
   \<Longrightarrow> ko_at' v x s'"
  by (fastforce elim: aligned'_distinct'_ko_wp_at'I simp: obj_at'_real_def project_inject)

lemma dmo_aligned'[wp]:
  "\<lbrace>pspace_aligned'\<rbrace> doMachineOp f \<lbrace>\<lambda>_. pspace_aligned'\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply wp
  apply clarsimp
  done

lemma dmo_distinct'[wp]:
  "\<lbrace>pspace_distinct'\<rbrace> doMachineOp f \<lbrace>\<lambda>_. pspace_distinct'\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply wp
  apply clarsimp
  done

lemma dmo_valid_objs'[wp]:
  "\<lbrace>valid_objs'\<rbrace> doMachineOp f \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply wp
  apply clarsimp
  done

lemma dmo_inv':
  assumes R: "\<And>P. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. P\<rbrace>"
  shows "\<lbrace>P\<rbrace> doMachineOp f \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply wp
  apply clarsimp
  apply (drule in_inv_by_hoareD [OF R])
  apply simp
  done

crunch doMachineOp
  for cte_wp_at'2[wp]: "\<lambda>s. P (cte_wp_at' P' p s)"
  and typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"

global_interpretation doMachineOp: gen_typ_at_all_props' "doMachineOp mop"
  by typ_at_props'

lemma doMachineOp_invs_bits[wp]:
  "doMachineOp m \<lbrace>valid_pspace'\<rbrace>"
  "doMachineOp m \<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  "doMachineOp m \<lbrace>valid_bitmaps\<rbrace>"
  "doMachineOp m \<lbrace>valid_sched_pointers\<rbrace>"
  "doMachineOp m \<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace>"
  "doMachineOp m \<lbrace>\<lambda>s. P (state_hyp_refs_of' s)\<rbrace>"
  "doMachineOp m \<lbrace>if_live_then_nonz_cap'\<rbrace>"
  "doMachineOp m \<lbrace>cur_tcb'\<rbrace>"
  "doMachineOp m \<lbrace>if_unsafe_then_cap'\<rbrace>"
   by (simp add: doMachineOp_def split_def
       | wp
       | fastforce elim: state_refs_of'_pspaceI)+

crunch doMachineOp
  for obj_at'[wp]: "\<lambda>s. P (obj_at' P' p s)"
  and it[wp]: "\<lambda>s. P (ksIdleThread s)"
  and idle'[wp]: "valid_idle'"
  and ko_wp_at'[wp]: "\<lambda>s. P (ko_wp_at' T p s)"

lemmas is_aligned_add_step_le' = is_aligned_add_step_le[simplified mask_2pm1 add_diff_eq]

lemma objBitsKO_Data:
  "objBitsKO (if dev then KOUserDataDevice else KOUserData) = pageBits"
  by (simp add: objBits_def objBitsKO_def word_size_def)

lemma of_bl_shift_cte_level_bits:
  "(of_bl z :: machine_word) << cte_level_bits \<le> mask (cte_level_bits + length z)"
  by (simp add: le_mask_shiftl_le_mask of_bl_max)

lemma typ_at'_same_type:
  assumes "typ_at' T p s" "koTypeOf k = koTypeOf ko" "objBitsKO k = objBitsKO ko" "ksPSpace s p' = Some ko"
  shows "typ_at' T p (s\<lparr>ksPSpace :=(ksPSpace s)(p' \<mapsto> k)\<rparr>)"
  using assms
  by (clarsimp simp: typ_at'_def ko_wp_at'_def ps_clear_upd)

lemma cte_at'_same_type:
  "\<lbrakk>cte_wp_at' \<top> t s; koTypeOf k = koTypeOf ko;objBitsKO k = objBitsKO ko;
    ksPSpace s p = Some ko\<rbrakk>
      \<Longrightarrow> cte_wp_at' \<top> t (s\<lparr>ksPSpace := (ksPSpace s)(p \<mapsto> k)\<rparr>)"
  apply (simp add: cte_at_typ' typ_at'_same_type)
  apply (elim exE disjE)
   apply (rule disjI1, clarsimp simp: typ_at'_same_type)
  apply (rule disjI2, rule_tac x=n in exI, clarsimp simp: typ_at'_same_type)
  done

lemma sym_ref_Receive_or_Reply_replyTCB':
  "\<lbrakk> sym_refs (state_refs_of' s); ko_at' tcb tp s;
     tcbState tcb = BlockedOnReceive ep pl (Some rp)
     \<or> tcbState tcb = BlockedOnReply (Some rp) \<rbrakk> \<Longrightarrow>
    \<exists>reply. ksPSpace s rp = Some (KOReply reply) \<and> replyTCB reply = Some tp"
  apply (drule (1) sym_refs_obj_atD'[rotated, where p=tp])
  apply (clarsimp simp: state_refs_of'_def obj_at'_def)
  apply (clarsimp simp: ko_wp_at'_def)
  apply (erule disjE; clarsimp)
  apply (rename_tac koa; case_tac koa;
         simp add: get_refs_def2 tcb_st_refs_of'_def tcb_bound_refs'_def
            split: endpoint.split_asm ntfn.split_asm thread_state.split_asm if_split_asm)+
  done

lemma sym_ref_replyTCB_Receive_or_Reply:
  "\<lbrakk> ko_at' reply rp s; sym_refs (state_refs_of' s); replyTCB reply = Some tp \<rbrakk>
   \<Longrightarrow> st_tcb_at' (\<lambda>st. (\<exists>ep pl. st = BlockedOnReceive ep pl (Some rp))
                        \<or> st = BlockedOnReply (Some rp)) tp s"
  apply (drule (1) sym_refs_obj_atD'[rotated, where p=rp])
  apply (clarsimp simp: state_refs_of'_def pred_tcb_at'_def obj_at'_def)
  apply (clarsimp simp: ko_wp_at'_def)
  apply (rename_tac tcb; case_tac tcb;
         simp add: get_refs_def2 tcb_st_refs_of'_def tcb_bound_refs'_def
            split: ntfn.split_asm thread_state.split_asm)+
  done

(* cross lemmas *)

lemma obj_at'_is_canonical:
  "\<lbrakk>pspace_canonical' s; obj_at' P t s\<rbrakk> \<Longrightarrow> canonical_address t"
  by (force simp: obj_at'_def pspace_canonical'_def)

lemma tcbs_relation_tcb_relation_abs:
  "\<lbrakk>kheap s ptr = Some (TCB tcb); tcbs_relation s s'\<rbrakk>
   \<Longrightarrow> \<exists>tcb'. ksPSpace s' ptr = Some (KOTCB tcb') \<and> tcb_relation tcb tcb'"
  by (fastforce simp: map_relation_def opt_map_def tcbs_of_kh_def split: option.splits)

lemma tcbs_relation_tcb_relation_abs_obj_at':
  "\<lbrakk>kheap s ptr = Some (TCB tcb); tcbs_relation s s'; pspace_aligned' s'; pspace_distinct' s'\<rbrakk>
   \<Longrightarrow> \<exists>tcb'. ko_at' tcb' ptr s' \<and> tcb_relation tcb tcb'"
  apply (frule (1) tcbs_relation_tcb_relation_abs)
  apply (fastforce dest: aligned'_distinct'_ko_at'I[where 'a=tcb])
  done

lemma tcbs_relation_tcb_relation_conc:
  "\<lbrakk>ksPSpace s' ptr = Some (KOTCB tcb'); tcbs_relation s s'\<rbrakk>
   \<Longrightarrow> \<exists>tcb. kheap s ptr = Some (TCB tcb) \<and> tcb_relation tcb tcb'"
  by (force simp: map_relation_def opt_map_def tcbs_of_kh_def split: option.splits)

lemma tcb_at_cross_tcbs_relation:
  "\<lbrakk>tcb_at tcb_ptr s; tcbs_relation s s'; pspace_aligned' s'; pspace_distinct' s'\<rbrakk>
   \<Longrightarrow> tcb_at' tcb_ptr s'"
  apply (clarsimp simp: obj_at_def is_tcb_def)
  apply (clarsimp split: Structures_A.kernel_object.splits)
  apply (frule (3) tcbs_relation_tcb_relation_abs_obj_at')
  apply (clarsimp simp: obj_at'_def)
  done

lemma tcb_at_cross:
  "\<lbrakk>pspace_relation (kheap s) (ksPSpace s'); pspace_aligned' s'; pspace_distinct' s'; tcb_at t s\<rbrakk>
   \<Longrightarrow> tcb_at' t s'"
  by (fastforce dest: tcb_at_cross_tcbs_relation simp: pspace_relation_heap_pspace_relation)

lemma tcb_at'_cross:
  "\<lbrakk>pspace_relation (kheap s) (ksPSpace s'); tcb_at' ptr s'\<rbrakk> \<Longrightarrow> tcb_at ptr s"
  by (fastforce dest: tcbs_relation_tcb_relation_conc
                simp: obj_at'_def pspace_relation_heap_pspace_relation obj_at_def is_tcb_def)

lemma st_tcb_at_coerce_abstract':
  "\<lbrakk>st_tcb_at' P t s'; tcbs_relation s s'\<rbrakk>
   \<Longrightarrow> st_tcb_at (\<lambda>st. \<exists>st'. thread_state_relation st st' \<and> P st') t s"
  apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
  apply (frule (1) tcbs_relation_tcb_relation_conc)
  by (fastforce simp: st_tcb_at_def obj_at_def tcb_relation_def)

lemma st_tcb_at_coerce_abstract:
  "\<lbrakk>st_tcb_at' P t c; (a, c) \<in> state_relation\<rbrakk>
   \<Longrightarrow> st_tcb_at (\<lambda>st. \<exists>st'. thread_state_relation st st' \<and> P st') t a"
  by (fastforce elim!: st_tcb_at_coerce_abstract'
                 dest: state_relation_pspace_relation
                 simp: pspace_relation_heap_pspace_relation)

lemma aligned'_distinct'_obj_at'_propI:
  "\<lbrakk>ksPSpace s' x = Some ko;  pspace_aligned' s'; pspace_distinct' s';
    koTypeOf ko  = SchedContextT \<longrightarrow> pspace_bounded' s';
    ko = injectKO (v :: 'a :: pspace_storable); P v\<rbrakk>
   \<Longrightarrow> obj_at' P x s'"
  by (fastforce elim: aligned'_distinct'_ko_wp_at'I simp: obj_at'_real_def project_inject)

lemma st_tcb_at_coerce_concrete:
  "\<lbrakk>st_tcb_at P t s; (s, s') \<in> state_relation; pspace_aligned' s'; pspace_distinct' s'\<rbrakk>
   \<Longrightarrow> st_tcb_at' (\<lambda>st'. \<exists>st. thread_state_relation st st' \<and> P st) t s'"
  apply (frule state_relation_pspace_relation)
  apply (clarsimp simp: pspace_relation_heap_pspace_relation pred_tcb_at_def obj_at_def)
  apply (frule tcbs_relation_tcb_relation_abs)
   apply fastforce
  apply (fastforce intro: aligned'_distinct'_obj_at'_propI
                    simp: pred_tcb_at'_def tcb_relation_def)
  done

lemma st_tcb_at_runnable_cross:
  "\<lbrakk> st_tcb_at runnable t s; pspace_aligned' s'; pspace_distinct' s'; (s, s') \<in> state_relation \<rbrakk>
   \<Longrightarrow> st_tcb_at' runnable' t s'"
  apply (drule (3) st_tcb_at_coerce_concrete)
  by (clarsimp simp: pred_tcb_at'_def obj_at'_def sts_rel_runnable)

lemma st_tcb_at_activatable_cross:
  "\<lbrakk>st_tcb_at activatable t s; pspace_aligned' s'; pspace_distinct' s'; (s, s') \<in> state_relation\<rbrakk>
   \<Longrightarrow> st_tcb_at' activatable' t s'"
  apply (drule (3) st_tcb_at_coerce_concrete)
  by (clarsimp simp: pred_tcb_at'_def obj_at'_def sts_rel_activatable)

lemma bound_sc_tcb_at_cross:
  "\<lbrakk>bound_sc_tcb_at P t s; (s, s') \<in> state_relation; pspace_aligned' s'; pspace_distinct' s'\<rbrakk>
   \<Longrightarrow> tcb_at' t s' \<and> P (tcbSCs_of s' t)"
  by (fastforce dest!: state_relation_pspace_relation tcbs_relation_tcb_relation_abs_obj_at'
                 simp: pspace_relation_heap_pspace_relation pred_tcb_at_def obj_at_def
                       obj_at'_def tcb_relation_def opt_map_red)

lemma bound_yt_tcb_at_cross:
  "\<lbrakk>bound_yt_tcb_at P t s; (s, s') \<in> state_relation; pspace_aligned' s'; pspace_distinct' s'\<rbrakk>
   \<Longrightarrow> obj_at' (\<lambda>tcb'. \<exists>tcb. tcb_relation tcb tcb' \<and> P (tcb_yield_to tcb)) t s'"
  by (fastforce dest!: state_relation_pspace_relation tcbs_relation_tcb_relation_abs_obj_at'
                 simp: pspace_relation_heap_pspace_relation pred_tcb_at_def obj_at_def
                       obj_at'_def tcb_relation_def opt_map_red)

lemma eps_relation_ep_relation_abs:
  "\<lbrakk>kheap s ptr = Some (Structures_A.Endpoint ep); eps_relation s s'\<rbrakk>
   \<Longrightarrow> \<exists>ep'. ksPSpace s' ptr = Some (KOEndpoint ep') \<and> ep_relation ep ep'"
  by (fastforce simp: map_relation_def opt_map_def eps_of_kh_def split: option.splits )

lemma eps_relation_ep_relation_abs_obj_at':
  "\<lbrakk>kheap s ptr = Some (Structures_A.Endpoint ep); eps_relation s s';
    pspace_aligned' s'; pspace_distinct' s'\<rbrakk>
   \<Longrightarrow> \<exists>ep'. ko_at' ep' ptr s' \<and> ep_relation ep ep'"
  apply (frule (1) eps_relation_ep_relation_abs)
  apply (fastforce dest: aligned'_distinct'_ko_at'I[where 'a=endpoint])
  done

lemma eps_relation_ep_relation_conc:
  "\<lbrakk>ksPSpace s' ptr = Some (KOEndpoint ep'); eps_relation s s'\<rbrakk>
   \<Longrightarrow> \<exists>ep. kheap s ptr = Some (Structures_A.Endpoint ep) \<and> ep_relation ep ep'"
  by (force simp: map_relation_def opt_map_def eps_of_kh_def split: option.splits)

lemma ep_at_cross:
  "\<lbrakk>pspace_relation (kheap s) (ksPSpace s'); pspace_aligned' s'; pspace_distinct' s'; ep_at ptr s\<rbrakk>
   \<Longrightarrow> ep_at' ptr s'"
  apply (clarsimp simp: pspace_relation_heap_pspace_relation obj_at_def is_ep_def)
  apply (fastforce dest: eps_relation_ep_relation_abs_obj_at'
                   simp: obj_at'_def
                  split: Structures_A.kernel_object.splits)
  done

lemma ntfns_relation_ntfn_relation_abs:
  "\<lbrakk>kheap s ptr = Some (Structures_A.Notification ntfn); ntfns_relation s s'\<rbrakk>
   \<Longrightarrow> \<exists>ntfn'. ksPSpace s' ptr = Some (KONotification ntfn') \<and> ntfn_relation ntfn ntfn'"
  by (fastforce simp: map_relation_def opt_map_def tcbs_of_kh_def split: option.splits)

lemma ntfns_relation_ntfn_relation_abs_obj_at':
  "\<lbrakk>kheap s ptr = Some (Structures_A.Notification ntfn); ntfns_relation s s';
    pspace_aligned' s'; pspace_distinct' s'\<rbrakk>
   \<Longrightarrow> \<exists>ntfn'. ko_at' ntfn' ptr s' \<and> ntfn_relation ntfn ntfn'"
  apply (frule (1) ntfns_relation_ntfn_relation_abs)
  apply (fastforce dest: aligned'_distinct'_ko_at'I[where 'a=notification])
  done

lemma ntfns_relation_ntfn_relation_conc:
  "\<lbrakk>ksPSpace s' ptr = Some (KONotification ntfn'); ntfns_relation s s'\<rbrakk>
   \<Longrightarrow> \<exists>ntfn. kheap s ptr = Some (Structures_A.Notification ntfn) \<and> ntfn_relation ntfn ntfn'"
  by (force simp: map_relation_def opt_map_def split: option.splits)

lemma ntfn_at_cross:
  "\<lbrakk>pspace_relation (kheap s) (ksPSpace s'); pspace_aligned' s'; pspace_distinct' s'; ntfn_at ptr s\<rbrakk>
   \<Longrightarrow> ntfn_at' ptr s'"
  apply (clarsimp simp: pspace_relation_heap_pspace_relation obj_at_def is_ntfn_def)
  apply (fastforce dest: ntfns_relation_ntfn_relation_abs_obj_at'
                   simp: obj_at'_def
                  split: Structures_A.kernel_object.splits)
  done

lemma scs_relation_sc_relation_abs:
  "\<lbrakk>kheap s ptr = Some (Structures_A.SchedContext sc n); scs_relation s s'\<rbrakk>
   \<Longrightarrow> \<exists>sc'. ksPSpace s' ptr = Some (KOSchedContext sc')
             \<and> valid_sched_context_size n  \<and> sc_relation sc n sc'"
  apply (clarsimp simp: scs_relation_def)
  apply (drule_tac x=ptr in spec)
  apply (prop_tac "ptr \<in> dom (scs_of s)", force simp: opt_map_def scs_of_kh_def)
  apply (clarsimp simp: opt_map_def scs_of_kh_def split: option.splits kernel_object.splits)
  done

lemma scs_relation_sc_relation_abs_obj_at':
  "\<lbrakk>kheap s ptr = Some (Structures_A.SchedContext sc n); scs_relation s s';
    pspace_aligned' s'; pspace_distinct' s'; pspace_bounded' s'\<rbrakk>
   \<Longrightarrow> \<exists>sc'. ko_at' sc' ptr s' \<and> valid_sched_context_size n \<and> sc_relation sc n sc'"
  apply (frule (1) scs_relation_sc_relation_abs)
  apply (fastforce dest: aligned'_distinct'_ko_at'I[where 'a=sched_context])
  done

lemma scs_relation_sc_relation_conc:
  "\<lbrakk>ksPSpace s' ptr = Some (KOSchedContext sc'); scs_relation s s'\<rbrakk>
   \<Longrightarrow> \<exists>sc n. kheap s ptr = Some (Structures_A.SchedContext sc n) \<and> sc_relation sc n sc'
              \<and> valid_sched_context_size n"
  apply (clarsimp simp: scs_relation_def)
  apply (drule_tac x=ptr in spec)
  apply (prop_tac "ptr \<in> dom (scs_of' s')", force simp: opt_map_red)
  apply (drule sym[where s="dom _"])
  apply (clarsimp simp: scs_of_kh_def opt_map_def split: option.splits)
  done

lemma sc_at_cross_scs_relation:
  "\<lbrakk>sc_at sc_ptr s; scs_relation s s'; pspace_aligned' s'; pspace_distinct' s'; pspace_bounded' s'\<rbrakk>
   \<Longrightarrow> sc_at' sc_ptr s'"
  apply (clarsimp simp: obj_at_def is_sc_obj_def)
  apply (clarsimp split: Structures_A.kernel_object.splits)
  apply (frule (4) scs_relation_sc_relation_abs_obj_at')
  apply (clarsimp simp: obj_at'_def)
  done

lemma sc_at_cross:
  "\<lbrakk>pspace_relation (kheap s) (ksPSpace s'); pspace_aligned' s'; pspace_distinct' s';
    pspace_bounded' s'; sc_at ptr s\<rbrakk>
   \<Longrightarrow> sc_at' ptr s'"
  apply (clarsimp simp: pspace_relation_heap_pspace_relation obj_at_def is_sc_obj_def)
  apply (fastforce dest: scs_relation_sc_relation_abs_obj_at'
                   simp: obj_at'_def
                  split: Structures_A.kernel_object.splits)
  done

lemma sc_at_cross_valid_objs:
  "\<lbrakk>pspace_relation (kheap s) (ksPSpace s'); pspace_aligned' s'; pspace_distinct' s';
    pspace_bounded' s';  pred_map \<top> (scs_of s) ptr; valid_objs s\<rbrakk>
   \<Longrightarrow> sc_at' ptr s'"
  by (fastforce dest: scs_relation_sc_relation_abs_obj_at'
                simp: pspace_relation_heap_pspace_relation vs_all_heap_simps obj_at_def is_sc_obj
                      obj_at'_def)

lemma sc_obj_at_cross:
  "\<lbrakk>pspace_relation (kheap s) (ksPSpace s'); pspace_aligned' s'; pspace_distinct' s';
    pspace_bounded' s'; sc_obj_at n ptr s\<rbrakk>
   \<Longrightarrow> obj_at' (\<lambda>sc::sched_context. objBits sc = minSchedContextBits + n) ptr s'"
  apply (clarsimp simp: pspace_relation_heap_pspace_relation obj_at_def is_sc_obj_def)
  by (fastforce dest: scs_relation_sc_relation_abs_obj_at'
                simp: pspace_relation_heap_pspace_relation vs_all_heap_simps obj_at_def is_sc_obj
                      obj_at'_def gen_objBits_simps sc_relation_def
               split: Structures_A.kernel_object.splits)

lemma sc_at'_cross:
  "\<lbrakk>pspace_relation (kheap s) (ksPSpace s'); sc_at' ptr s'\<rbrakk> \<Longrightarrow> sc_at ptr s"
  by (fastforce dest!: scs_relation_sc_relation_conc heap_pspace_relation_scs_relation
                 simp: pspace_relation_heap_pspace_relation obj_at'_def obj_at_def is_sc_obj_def)

lemma sc_obj_at'_cross:
  "\<lbrakk>pspace_relation (kheap s) (ksPSpace s'); obj_at' (\<lambda>sc :: sched_context. scSize sc = n) ptr s'\<rbrakk>
   \<Longrightarrow> sc_obj_at n ptr s"
  by (fastforce dest!: scs_relation_sc_relation_conc heap_pspace_relation_scs_relation
                 simp: pspace_relation_heap_pspace_relation obj_at'_def obj_at_def is_sc_obj_def
                       sc_relation_def)

lemma sc_tcb_sc_at_bound_cross:
  "\<lbrakk>pspace_relation (kheap (s :: det_state)) (ksPSpace s'); valid_objs s;
    pspace_aligned' s'; pspace_distinct' s'; pspace_bounded' s'; sc_tcb_sc_at ((\<noteq>) None) scp s\<rbrakk>
   \<Longrightarrow> obj_at' (\<lambda>sc. \<exists>y. scTCB sc = Some y) scp s'"
  apply (clarsimp simp: obj_at_def sc_tcb_sc_at_def)
  apply (frule scs_relation_sc_relation_abs)
   apply (fastforce simp: pspace_relation_heap_pspace_relation)
  apply clarsimp
  apply (erule (2) aligned'_distinct'_obj_at'_propI)
    apply fastforce
   apply fastforce
  apply (clarsimp simp: obj_at'_def sc_relation_def)
  apply (rename_tac sc')
  apply (case_tac "scTCB sc'"; clarsimp)
  done

lemma replies_relation_reply_relation_abs:
  "\<lbrakk>kheap s ptr = Some (Structures_A.Reply reply); replies_relation s s'\<rbrakk>
   \<Longrightarrow> \<exists>reply'. ksPSpace s' ptr = Some (KOReply reply') \<and> reply_relation reply reply'"
  apply (clarsimp simp: map_relation_def)
  apply (drule_tac x=ptr in spec)
  apply (prop_tac "ptr \<in> dom (replies_of s)", force simp: opt_map_red)
  apply (clarsimp simp: scs_of_kh_def opt_map_def split: option.splits)
  done

lemma replies_relation_reply_relation_abs_obj_at':
  "\<lbrakk>kheap s ptr = Some (Structures_A.Reply reply); replies_relation s s';
    pspace_aligned' s'; pspace_distinct' s'\<rbrakk>
   \<Longrightarrow> \<exists>reply'. ko_at' reply' ptr s' \<and> reply_relation reply reply'"
  apply (frule (1) replies_relation_reply_relation_abs)
  apply (fastforce dest: aligned'_distinct'_ko_at'I[where 'a=reply])
  done

lemma replies_relation_reply_relation_conc:
  "\<lbrakk>ksPSpace s' ptr = Some (KOReply reply'); replies_relation s s'\<rbrakk>
   \<Longrightarrow> \<exists>reply. kheap s ptr = Some (Structures_A.Reply reply) \<and> reply_relation reply reply'"
  apply (clarsimp simp: map_relation_def)
  apply (drule_tac x=ptr in spec)
  apply (prop_tac "ptr \<in> dom (replies_of' s')", force simp: opt_map_def)
  apply (drule sym[where s="dom _"])
  apply (clarsimp simp: opt_map_def split: option.splits)
  done

lemma reply_at_cross:
  "\<lbrakk>pspace_relation (kheap s) (ksPSpace s'); pspace_aligned' s'; pspace_distinct' s';
    reply_at ptr s\<rbrakk>
   \<Longrightarrow> reply_at' ptr s'"
  apply (clarsimp simp: pspace_relation_heap_pspace_relation obj_at_def is_reply_def)
  apply (fastforce dest: replies_relation_reply_relation_abs
                  intro: aligned'_distinct'_obj_at'_propI
                  split: Structures_A.kernel_object.splits)
  done

lemma reply_at'_cross:
  "\<lbrakk>pspace_relation (kheap s) (ksPSpace s'); reply_at' ptr s'\<rbrakk> \<Longrightarrow> reply_at ptr s"
  by (fastforce dest: replies_relation_reply_relation_conc
                simp: obj_at'_def pspace_relation_heap_pspace_relation obj_at_def is_reply_def)

lemma state_relation_sc_relation'':
  "\<lbrakk>(s, s') \<in> state_relation; kheap s ptr = Some (kernel_object.SchedContext sc n); sc_at ptr s;
    ko_at' sc' ptr s'\<rbrakk>
   \<Longrightarrow> \<exists>n. sc_relation sc n sc'"
  apply (clarsimp simp: gen_obj_at_simps is_sc_obj)
  apply (drule (1) pspace_relation_absD[OF _ state_relation_pspace_relation, rotated])
  apply (fastforce simp: obj_at_def is_sc_obj_def)
  done

lemma real_cte_at_cross:
  "\<lbrakk>pspace_relation (kheap s) (ksPSpace s'); pspace_aligned' s'; pspace_distinct' s';
    real_cte_at ptr s\<rbrakk>
   \<Longrightarrow> real_cte_at' (cte_map ptr) s'"
  apply (clarsimp simp: obj_at_def is_ntfn)
  apply (drule (1) pspace_relation_absD)
  apply (clarsimp simp: is_cap_table well_formed_cnode_n_def)
  by (fastforce intro: aligned'_distinct'_obj_at'_propI simp: cte_relation_def)

lemma cur_tcb_cross:
  "\<lbrakk>cur_tcb s; pspace_aligned' s'; pspace_distinct' s'; (s,s') \<in> state_relation\<rbrakk> \<Longrightarrow> cur_tcb' s'"
  apply (clarsimp simp: cur_tcb'_def cur_tcb_def state_relation_def)
  apply (erule (3) tcb_at_cross)
  done

lemma cur_sc_tcb_cross:
  "\<lbrakk>(s, s') \<in> state_relation; valid_objs s; pspace_aligned' s'; pspace_distinct' s';
    pspace_bounded' s'; cur_sc_tcb s; schact_is_rct s\<rbrakk>
   \<Longrightarrow> obj_at' (\<lambda>sc. scTCB sc = Some (ksCurThread s')) (ksCurSc s') s'"
  apply (clarsimp simp: obj_at_def sc_tcb_sc_at_def cur_sc_tcb_def
                 dest!: schact_is_rct state_relationD)
  apply (frule (1) pspace_relation_absD)
  apply clarsimp
  apply (prop_tac "valid_sched_context_size n")
   apply (erule (1) valid_sched_context_size_objsI)
  apply (clarsimp simp: if_split_asm)
  apply (rename_tac z; case_tac z; simp)
  apply (fastforce elim!: aligned'_distinct'_obj_at'_propI
                    simp: obj_at'_def sc_relation_def)
  done

lemma sym_refs_cross:
  "\<lbrakk>sym_refs (state_refs_of s); (s, s') \<in> state_relation; pspace_aligned' s'; pspace_distinct' s';
    pspace_bounded' s'\<rbrakk>
   \<Longrightarrow> sym_refs (state_refs_of' s')"
  apply (frule state_relation_pspace_relation)
  apply (clarsimp simp: pspace_relation_heap_pspace_relation)
  apply (clarsimp simp: state_refs_of_def state_refs_of'_def sym_refs_def refs_of'_def
                 split: option.split kernel_object.splits)
  apply (rename_tac ptr ko)
  apply (drule_tac x=ptr in spec)
  apply (intro conjI impI allI)
     apply (frule heap_pspace_relation_ntfns_relation)
     apply (frule (1) ntfns_relation_ntfn_relation_conc)
     apply (clarsimp simp: ntfn_relation_def)
     apply (elim disjE)
      apply (force dest!: tcbs_relation_tcb_relation_abs_obj_at'
                    simp: refs_of_def get_refs_def2 tcb_bound_refs'_def tcb_relation_def obj_at'_def
                   split: Structures_A.kernel_object.splits option.splits)
     apply (force dest!: scs_relation_sc_relation_abs_obj_at'
                   simp: refs_of_def get_refs_def2 sc_relation_def obj_at'_def
                  split: Structures_A.kernel_object.splits option.splits)
    apply (frule heap_pspace_relation_tcbs_relation)
    apply (frule (1) tcbs_relation_tcb_relation_conc)
    apply (clarsimp simp: tcb_relation_def split: option.splits)
    apply (rename_tac ref tp)
    apply (elim disjE)
     apply (clarsimp simp: tcb_st_refs_of'_def)
     apply (drule_tac x="(ref, TCBReply)" in bspec)
      apply (force simp: tcb_st_refs_of_def split: Structures_A.thread_state.splits if_splits)
     apply (force dest!: replies_relation_reply_relation_abs_obj_at'
                   simp: refs_of_def get_refs_def2 obj_at'_def reply_relation_def
                  split: Structures_A.kernel_object.splits option.splits thread_state.splits
                         if_splits)
    apply (clarsimp simp: tcb_bound_refs'_def)
    subgoal
      by (elim disjE;
          force dest!: scs_relation_sc_relation_abs_obj_at'
                       ntfns_relation_ntfn_relation_abs_obj_at'
                 simp: ntfn_relation_def sc_relation_def refs_of_def get_refs_def2 obj_at'_def
                split: Structures_A.kernel_object.splits option.splits)
   apply (frule heap_pspace_relation_scs_relation)
   apply (frule (1) scs_relation_sc_relation_conc)
   apply (clarsimp simp: sc_relation_def split: option.splits)
   apply (elim disjE)
      apply (force dest!: ntfns_relation_ntfn_relation_abs_obj_at'
                    simp: ntfn_relation_def refs_of_def get_refs_def2 obj_at'_def
                   split: Structures_A.kernel_object.splits option.splits)
     apply (force dest!: tcbs_relation_tcb_relation_abs_obj_at'
                   simp: refs_of_def get_refs_def2 tcb_bound_refs'_def tcb_relation_def obj_at'_def
                  split: Structures_A.kernel_object.splits option.splits)
    apply (force dest!: tcbs_relation_tcb_relation_abs_obj_at'
                  simp: refs_of_def get_refs_def2 tcb_bound_refs'_def tcb_relation_def obj_at'_def
                 split: Structures_A.kernel_object.splits option.splits)
   apply (clarsimp simp: sc_relation_def get_refs_def2)
   apply (drule state_relation_sc_replies_relation)
   apply (frule_tac sc_ptr=ptr in sc_replies_relation_scReplies_of)
     apply (force simp: scs_relation_def obj_at_def is_sc_obj_def opt_map_def scs_of_kh_def
                        hd_opt_def
                 split: option.splits)
    apply (clarsimp simp: obj_at'_def opt_map_def)
   apply (force dest!: replies_relation_reply_relation_abs_obj_at'
                 simp: get_refs_def2 obj_at'_def reply_relation_def opt_map_def
                       sc_replies_of_scs_def map_project_def scs_of_kh_def refs_of_def hd_opt_def
                split: Structures_A.kernel_object.splits option.splits)
  apply (frule heap_pspace_relation_replies_relation)
  apply (frule (1) replies_relation_reply_relation_conc)
  apply (clarsimp simp: reply_relation_def split: option.splits)
  apply (rename_tac ref tp)
  apply (elim disjE)
   apply (clarsimp simp: refs_of_def get_refs_def2
                  split: Structures_A.kernel_object.splits option.splits)
   apply (frule heap_pspace_relation_scs_relation)
   apply (frule (4) scs_relation_sc_relation_abs_obj_at')
   apply (intro context_conjI impI allI)
     apply (clarsimp simp: get_refs_def2 refs_of_def refs_of'_def obj_at'_def split: option.splits)
    apply (clarsimp simp: get_refs_def2 obj_at'_def)
    apply (drule state_relation_sc_replies_relation)
    apply (frule_tac sc_ptr=ref in sc_replies_relation_scReplies_of)
      apply (clarsimp simp: scs_relation_def obj_at_def is_sc_obj_def)
     apply (clarsimp simp: opt_map_def)
    apply (clarsimp simp: opt_map_def sc_replies_of_scs_def map_project_def scs_of_kh_def)
   apply (force simp: obj_at'_def)
  apply (clarsimp simp: get_refs_def2 refs_of_def refs_of'_def
                 split: Structures_A.kernel_object.splits option.splits)
  by (force dest!: tcbs_relation_tcb_relation_abs_obj_at'
             simp: tcb_st_refs_of_def obj_at'_def tcb_relation_def
            split: if_splits Structures_A.thread_state.splits)

lemma ct_not_inQ_cross:
  "\<lbrakk>(s, s') \<in> state_relation; ct_not_in_q s; cur_tcb s; pspace_aligned' s'; pspace_distinct' s'\<rbrakk>
   \<Longrightarrow> ct_not_inQ s'"
  apply (frule state_relation_ready_queues_relation)
  apply (frule state_relation_sched_act_relation)
  apply (frule (3) cur_tcb_cross)
  apply (clarsimp simp: ct_not_inQ_def ct_not_in_q_def)
   apply (case_tac "scheduler_action s"; clarsimp)
  apply (clarsimp simp: not_queued_def)
  apply (rule ccontr)
  apply (prop_tac "obj_at' tcbQueued (ksCurThread s') s'")
   apply (clarsimp simp: gen_obj_at_simps cur_tcb'_def)
  apply normalise_obj_at'
  apply (rename_tac tcb)
  apply (drule_tac x="tcbDomain tcb" in spec)
  apply (drule_tac x="tcbPriority tcb" in spec)
  apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def list_queue_relation_def
                        Let_def)
  apply (drule_tac x="tcbDomain tcb" in spec)
  apply (drule_tac x="tcbPriority tcb" in spec)
  apply (fastforce simp: curthread_relation inQ_def in_opt_pred obj_at'_def opt_map_red)
  done

lemma sch_act_wf_cross:
  "\<lbrakk>(s,s') \<in> state_relation; valid_sched_action s; cur_tcb s; pspace_aligned' s'; pspace_distinct' s'\<rbrakk>
   \<Longrightarrow> sch_act_wf (ksSchedulerAction s') s'"
  apply (clarsimp simp: sch_act_wf_def)
  apply (cases "ksSchedulerAction s'"; clarsimp)
   apply (prop_tac "scheduler_action s = resume_cur_thread")
    apply (clarsimp simp: state_relation_def)
    apply (metis sched_act_relation.simps Structures_A.scheduler_action.exhaust
                 scheduler_action.simps)
   apply (frule curthread_relation)
   apply (frule state_relation_pspace_relation)
   apply (frule (2) cur_tcb_cross)
    apply fastforce
   apply (clarsimp simp: valid_sched_action_def is_activatable_def vs_all_heap_simps
                         ct_in_state'_def st_tcb_at'_def)
   apply (clarsimp simp: pspace_relation_def)
   apply (drule_tac x="cur_thread s" in bspec, fastforce)
   apply (drule_tac x="(cur_thread s, tcb_relation_cut)" in bspec, fastforce)
   apply (clarsimp simp: tcb_relation_cut_def)
   apply (rename_tac tcb)
   apply (case_tac "tcb_state tcb"; clarsimp simp: tcb_relation_def gen_obj_at_simps cur_tcb'_def)
  apply (rename_tac target)
  apply (clarsimp simp: valid_sched_action_def weak_valid_sched_action_def vs_all_heap_simps)
  apply (prop_tac "scheduler_action s = switch_thread target")
   apply (clarsimp simp: state_relation_def)
   apply (metis sched_act_relation.simps Structures_A.scheduler_action.exhaust
                scheduler_action.simps)
  apply (prop_tac "tcb_at' target s'")
   apply (fastforce intro!: tcb_at_cross
                      simp: obj_at_def is_tcb_def)
  apply (frule state_relation_pspace_relation)
  apply (clarsimp simp: pspace_relation_def)
  apply (drule_tac x=target in bspec, fastforce)
  apply (drule_tac x="(target, tcb_relation_cut)" in bspec, fastforce)
  apply (intro conjI)
   apply (fastforce intro!: st_tcb_at_runnable_cross
                      simp: obj_at_def pred_tcb_at_def)
  apply (clarsimp simp: tcb_relation_def gen_obj_at_simps switch_in_cur_domain_def
                        state_relation_def in_cur_domain_def tcb_in_cur_domain'_def
                        etcb_at'_def vs_all_heap_simps tcb_relation_cut_def)
  done

lemma ct_idle_or_in_cur_domain'_cross:
  "\<lbrakk>(s,s') \<in> state_relation; ct_in_cur_domain s; cur_tcb s; pspace_aligned' s'; pspace_distinct' s'\<rbrakk>
   \<Longrightarrow> ct_idle_or_in_cur_domain' s'"
  apply (clarsimp simp: ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def ct_in_cur_domain_def)
  apply (case_tac "cur_thread s = idle_thread s"; clarsimp)
   apply (clarsimp simp: state_relation_def)
  apply (frule curthread_relation)
  apply (frule (2) cur_tcb_cross)
   apply fastforce
  apply (prop_tac "scheduler_action s = resume_cur_thread")
   apply (clarsimp simp: state_relation_def)
   apply (metis sched_act_relation.simps Structures_A.scheduler_action.exhaust
                scheduler_action.simps)
  apply (clarsimp simp: in_cur_domain_def etcb_at_def vs_all_heap_simps gen_obj_at_simps cur_tcb'_def)
  apply (frule state_relation_pspace_relation)
  apply (clarsimp simp: pspace_relation_def)
  apply (drule_tac x="cur_thread s" in bspec)
   apply (clarsimp simp: cur_tcb_def obj_at_def)
  apply (drule_tac x="(cur_thread s, tcb_relation_cut)" in bspec)
   apply (clarsimp simp: cur_tcb_def obj_at_def is_tcb_def)
   apply (rename_tac tcb)
   apply (case_tac tcb; clarsimp)
  apply (clarsimp simp: cur_tcb_def obj_at_def is_tcb_def)
  apply (rename_tac tcb)
  apply (case_tac tcb; clarsimp)
  apply (clarsimp simp: tcb_relation_cut_def tcb_relation_def state_relation_def)
  done

lemma valid_idle'_cross:
  "\<lbrakk>(s,s') \<in> state_relation; valid_idle s; pspace_aligned' s'; pspace_distinct' s';
    pspace_bounded' s'; valid_objs s\<rbrakk>
   \<Longrightarrow> valid_idle' s'"
  apply (clarsimp simp: valid_idle'_def valid_idle_def pred_tcb_at_def obj_at_def)
  apply (prop_tac "ksIdleThread s' = idle_thread s")
   apply (clarsimp simp: state_relation_def)
  apply clarsimp
  apply (prop_tac "tcb_at' (ksIdleThread s') s'")
   apply (fastforce intro!: tcb_at_cross simp: obj_at_def state_relation_def is_tcb_def)
  apply (prop_tac "sc_at' (idle_sc_ptr) s'")
   apply (fastforce intro!: sc_at_cross valid_objs_valid_sched_context_size
                      simp: obj_at_def state_relation_def is_sc_obj_def)
  apply (frule state_relation_pspace_relation)
  apply (clarsimp simp: pspace_relation_def)
  apply (intro conjI)
   apply (drule_tac x="idle_thread s" in bspec, fastforce)
   apply (drule_tac x="(idle_thread s, tcb_relation_cut)" in bspec, fastforce)
   apply (clarsimp simp: gen_obj_at_simps idle_tcb'_def tcb_relation_def tcb_relation_cut_def)
  apply (drule_tac x="idle_sc_ptr" in bspec, fastforce)
  apply (drule_tac x="(idle_sc_ptr, sc_relation_cut)" in bspec)
   apply (fastforce intro: valid_objs_valid_sched_context_size)
  by (fastforce dest: sc_replies_prevs_walk
                simp: heap_walk_Nil_None gen_obj_at_simps sc_relation_def state_relation_def)

lemma ready_qs_runnable_cross:
  "\<lbrakk>(s, s') \<in> state_relation; pspace_aligned' s'; pspace_distinct' s'; valid_ready_qs s\<rbrakk>
   \<Longrightarrow> ready_qs_runnable s'"
  apply (clarsimp simp: ready_qs_runnable_def)
  apply normalise_obj_at'
  apply (frule state_relation_ready_queues_relation)
  apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def Let_def
                        list_queue_relation_def)
  apply (drule_tac x="tcbDomain ko" in spec)
  apply (drule_tac x="tcbPriority ko" in spec)
  apply (clarsimp simp: valid_ready_qs_def)
  apply (drule_tac x="tcbDomain ko" in spec)
  apply (drule_tac x="tcbPriority ko" in spec)
  apply clarsimp
  apply (drule_tac x=t in bspec)
   apply (fastforce simp: inQ_def in_opt_pred obj_at'_def opt_map_red)
  apply (fastforce dest: st_tcb_at_runnable_cross
              simp flip: tcb_at_kh_simps
                   simp: obj_at'_def st_tcb_at'_def)
  done

lemma replyTCBs_of_cross:
  "\<lbrakk>(s, s') \<in> state_relation; reply_tcb_reply_at P rptr s\<rbrakk>
   \<Longrightarrow> P (replyTCBs_of s' rptr)"
  apply (clarsimp simp: reply_at_ppred_def obj_at_def state_relation_def)
  apply (drule (1) pspace_relation_absD, clarsimp)
  apply (case_tac z; simp)
  apply (clarsimp simp: opt_map_def reply_relation_def)
  done

lemma replySCs_of_cross:
  "\<lbrakk>(s, s') \<in> state_relation; reply_sc_reply_at P rptr s\<rbrakk>
   \<Longrightarrow> P (replySCs_of s' rptr)"
  apply (clarsimp simp: reply_at_ppred_def obj_at_def is_tcb state_relation_def)
  apply (drule (1) pspace_relation_absD, clarsimp)
  apply (case_tac z; simp)
  apply (clarsimp simp: opt_map_def reply_relation_def)
  done

lemma valid_replies_sc_cross:
  "\<lbrakk>(s, s') \<in> state_relation; valid_replies s; sym_refs (state_refs_of s);
    pspace_aligned' s'; pspace_distinct' s'; reply_at rptr s\<rbrakk>
   \<Longrightarrow> valid_replies'_sc_asrt rptr s'"
  apply (clarsimp simp: valid_replies_defs valid_replies'_sc_asrt_def elim!: opt_mapE)
  apply (rename_tac scptr rp)
  apply (prop_tac "sc_replies_sc_at (\<lambda>rs. rptr \<in> set rs) scptr s")
   apply (frule_tac sc_ptr=scptr and reply_ptr=rptr in sym_refs_sc_replies_sc_at)
    apply (rule ccontr)
    apply (drule not_sk_obj_at_pred)
     apply (fastforce simp: sk_obj_at_pred_def obj_at_def is_obj_defs)
    apply (frule (1) replySCs_of_cross)
    apply (clarsimp simp: obj_at'_def opt_map_def)
   apply (clarsimp simp: sc_at_pred_n_eq_commute sc_at_ppred_def obj_at_def)
  apply (drule subsetD, force)
  apply (clarsimp simp: pred_tcb_at_eq_commute[symmetric])
  apply (frule (1) st_tcb_reply_state_refs)
  apply (drule (3) st_tcb_at_coerce_concrete)
  apply (drule replyTCBs_of_cross[where P="\<lambda>rtcb. rtcb = (Some tptr)" for tptr])
   apply (fastforce simp: sk_obj_at_pred_def2)
  apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
  done

lemma no_fail_setSchedContext[wp]:
  "no_fail (sc_at' ptr and (\<lambda>s'. ((\<lambda>k::sched_context. objBits k = objBits new) |< scs_of' s') ptr))
           (setSchedContext ptr new)"
  unfolding setSchedContext_def by (wpsimp simp: opt_map_def obj_at'_def opt_pred_def)

(* update wp rules without ko_at' *)
lemma updateSchedContext_wp:
  "\<lbrace>\<lambda>s. sc_at' sc_ptr s \<longrightarrow>
        Q (s\<lparr>ksPSpace := (ksPSpace s)(sc_ptr \<mapsto> KOSchedContext (f' (the (scs_of' s sc_ptr))))\<rparr>)\<rbrace>
   updateSchedContext sc_ptr f'
   \<lbrace>\<lambda>_. Q\<rbrace>"
  by (wpsimp simp: updateSchedContext_def wp: set_sc'.set_wp)
     (clarsimp simp: obj_at'_def opt_map_red elim!: rsubst[where P=Q])

lemma getCurThread_sp:
  "\<lbrace>P\<rbrace> getCurThread \<lbrace>\<lambda>rv. P and (\<lambda>s. rv = ksCurThread s)\<rbrace>"
  by (wpsimp simp: getCurThread_def)

lemma getSchedulerAction_sp:
  "\<lbrace>P\<rbrace> getSchedulerAction \<lbrace>\<lambda>rv. P and (\<lambda>s. rv = ksSchedulerAction s)\<rbrace>"
  by (wpsimp simp: getSchedulerAction_def)

lemma getReprogramTimer_sp:
  "\<lbrace>P\<rbrace> getReprogramTimer \<lbrace>\<lambda>rv. P and (\<lambda>s. rv = ksReprogramTimer s)\<rbrace>"
  by (wpsimp simp: getReprogramTimer_def)

lemma getIdleThread_sp:
  "\<lbrace>P\<rbrace> getIdleThread \<lbrace>\<lambda>rv. P and (\<lambda>s. rv = ksIdleThread s)\<rbrace>"
  by wpsimp

lemma getIdleSC_sp:
  "\<lbrace>P\<rbrace> getIdleSC \<lbrace>\<lambda>rv. P and (\<lambda>s. rv = ksIdleSC s)\<rbrace>"
  by wpsimp

lemma getReprogramTimer_wp[wp]:
  "\<lbrace>\<lambda>s. P (ksReprogramTimer s) s\<rbrace> getReprogramTimer \<lbrace>P\<rbrace>"
  by (wpsimp simp: getReprogramTimer_def)

lemma getConsumedTime_wp[wp]:
  "\<lbrace>\<lambda>s. P (ksConsumedTime s) s\<rbrace> getConsumedTime \<lbrace>P\<rbrace>"
  by (wpsimp simp: getConsumedTime_def)

lemma isRoundRobin_wp:
  "\<lbrace>\<lambda>s. \<forall>ko. ko_at' ko sc s \<longrightarrow> P (scPeriod ko = 0) s\<rbrace> isRoundRobin sc \<lbrace>P\<rbrace>"
  by (wpsimp simp: isRoundRobin_def)

lemma getCurSc_wp[wp]:
  "\<lbrace>\<lambda>s. P (ksCurSc s) s\<rbrace> getCurSc \<lbrace>P\<rbrace>"
  unfolding getCurSc_def
  by wpsimp

lemma getCurTime_wp[wp]:
  "\<lbrace>\<lambda>s. P (ksCurTime s) s\<rbrace> getCurTime \<lbrace>P\<rbrace>"
  unfolding getCurTime_def
  by wpsimp

lemma curDomain_wp[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s) s\<rbrace> curDomain \<lbrace>P\<rbrace>"
  unfolding curDomain_def
  by wpsimp

lemma curDomain_sp:
  "\<lbrace>P\<rbrace> curDomain \<lbrace>\<lambda>rv. P and (\<lambda>s. rv = ksCurDomain s)\<rbrace>"
  by wpsimp

lemma getReleaseQueue_wp[wp]:
  "\<lbrace>\<lambda>s. P (ksReleaseQueue s) s\<rbrace> getReleaseQueue \<lbrace>P\<rbrace>"
  unfolding getReleaseQueue_def
  by wpsimp

lemma getObject_sc_wp:
  "\<lbrace>\<lambda>s. sc_at' p s \<longrightarrow> (\<exists>t::sched_context. ko_at' t p s \<and> Q t s)\<rbrace> getObject p \<lbrace>Q\<rbrace>"
  by (clarsimp simp: getObject_def valid_def in_monad
                     split_def gen_objBits_simps loadObject_default_def
                     obj_at'_def in_magnitude_check
              dest!: readObject_misc_ko_at')

lemma getRefillNext_wp:
  "\<lbrace>\<lambda>s.  \<forall>sc. scs_of' s scPtr = Some sc \<longrightarrow> P (refillNext sc index) s\<rbrace>
   getRefillNext scPtr index
   \<lbrace>P\<rbrace>"
  apply (simp add: getRefillNext_def readRefillNext_def readSchedContext_def
             flip: getObject_def)
  apply (wpsimp wp: getObject_sc_wp)
  apply (clarsimp simp: obj_at'_def opt_map_def)
  done

lemma readRefillSize_SomeD:
  "readRefillSize scPtr s = Some sz \<Longrightarrow> \<exists>sc. ko_at' sc scPtr s \<and> refillSize sc = sz"
  apply (clarsimp simp: readRefillSize_def readSchedContext_def)
  apply (fastforce dest: readObject_ko_at'_sc)
  done

lemma getRefillSize_wp:
  "\<lbrace>\<lambda>s. \<forall>ko. ko_at' ko scp s \<longrightarrow> P (refillSize ko) s\<rbrace> getRefillSize scp \<lbrace>P\<rbrace>"
  apply (clarsimp simp: getRefillSize_def)
  apply wpsimp
  apply (fastforce dest: readRefillSize_SomeD)
  done

lemma getRefillFull_wp:
  "\<lbrace>\<lambda>s. \<forall>ko. ko_at' ko scp s \<longrightarrow> P (refillSize ko = scRefillMax ko) s\<rbrace> getRefillFull scp \<lbrace>P\<rbrace>"
  apply (clarsimp simp: getRefillFull_def readRefillFull_def getSchedContext_def[symmetric]
                        readSchedContext_def getObject_def[symmetric] getRefillSize_def[symmetric])
  apply (wpsimp wp: getRefillSize_wp)
  apply normalise_obj_at'
  done

lemma no_ofail_readCurTime[simp]:
  "no_ofail \<top> readCurTime"
  unfolding readCurTime_def by clarsimp

lemma ovalid_readCurTime[wp]:
  "\<lblot>\<lambda>s. P (ksCurTime s) s\<rblot> readCurTime \<lblot>\<lambda>r s. P r s \<and> r = ksCurTime s\<rblot>"
  by (simp add: readCurTime_def asks_def obind_def ovalid_def)

lemma readScActive_wp[wp]:
  "\<lblot>\<lambda>s. \<forall>ko. ko_at' ko scp s \<longrightarrow> P (0 < scRefillMax ko) s\<rblot> readScActive scp \<lblot>P\<rblot>"
  unfolding readScActive_def readSchedContext_def
  by (wpsimp wp: set_sc'.readObject_wp)

lemmas scActive_wp[wp] = ovalid_gets_the[OF readScActive_wp, simplified scActive_def[symmetric]]

lemma getRefills_wp:
  "\<lbrace>\<lambda>s. \<forall>ko. ko_at' ko scp s \<longrightarrow> P (scRefills ko) s\<rbrace>
   getRefills scp
   \<lbrace>P\<rbrace>"
  unfolding getRefills_def
  by wpsimp

lemma readRefillHead_SomeD:
  "readRefillHead scPtr s = Some refill \<Longrightarrow> \<exists>sc. ko_at' sc scPtr s \<and> refill = refillHd sc"
  apply (clarsimp simp: readRefillHead_def readSchedContext_def)
  apply (fastforce dest: readObject_ko_at'_sc)
  done

lemma readRefillHead_wp[wp]:
  "\<lblot>\<lambda>s. \<forall>sc. scs_of' s scPtr = Some sc \<longrightarrow> Q (refillHd sc) s\<rblot>
   readRefillHead scPtr
   \<lblot>Q\<rblot>"
  unfolding readRefillHead_def readSchedContext_def
  apply (wpsimp wp: set_sc'.readObject_wp)
  apply (clarsimp simp: opt_map_def obj_at'_def)
  done

lemmas getRefillHead_wp[wp] =
  ovalid_gets_the[OF readRefillHead_wp, simplified getRefillHead_def[symmetric]]

lemma readRefillTail_wp[wp]:
  "\<lblot>\<lambda>s. \<forall>sc. scs_of' s scPtr = Some sc \<longrightarrow> Q (refillTl sc) s\<rblot>
   readRefillTail scPtr
   \<lblot>Q\<rblot>"
  unfolding readRefillTail_def readSchedContext_def
  apply (wpsimp wp: set_sc'.readObject_wp)
  apply (clarsimp simp: opt_map_def obj_at'_def)
  done

lemmas getRefillTail_wp[wp] =
  ovalid_gets_the[OF readRefillTail_wp, simplified getRefillTail_def[symmetric]]

lemma getRefillHead_sp:
  "\<lbrace>P\<rbrace> getRefillHead scPtr \<lbrace>\<lambda>rv s. P s \<and> (\<exists>sc. scs_of' s scPtr = Some sc \<and> refillHd sc = rv)\<rbrace>"
  by wpsimp

lemma getRefillTail_sp:
  "\<lbrace>P\<rbrace> getRefillTail scPtr \<lbrace>\<lambda>rv s. P s \<and> (\<exists>sc. scs_of' s scPtr = Some sc \<and> refillTl sc = rv)\<rbrace>"
  by wpsimp

lemma readRefillReady_wp:
  "\<lblot>\<lambda>s. \<forall>sc. scs_of' s scp = Some sc \<longrightarrow> P (rTime (refillHd sc) \<le> ksCurTime s) s\<rblot>
   readRefillReady scp
   \<lblot>P\<rblot>"
  unfolding readRefillReady_def readCurTime_def
  by wpsimp

lemmas refillReady_wp[wp] =
  ovalid_gets_the[OF readRefillReady_wp, simplified refillReady_def[symmetric]]

lemma readRefillCapacity_SomeD:
  "readRefillCapacity scPtr usage s = Some capacity
   \<Longrightarrow> \<exists>sc. scs_of' s scPtr = Some sc \<and> capacity = refillCapacity usage (refillHd sc)"
  apply (clarsimp simp: readRefillCapacity_def)
  apply (fastforce dest: readRefillHead_SomeD simp: opt_map_def obj_at'_def)
  done

lemma getRefillCapacity_wp[wp]:
  "\<lbrace>\<lambda>s. \<forall>sc. scs_of' s scPtr = Some sc \<longrightarrow> P (refillCapacity usage (refillHd sc)) s\<rbrace>
   getRefillCapacity scPtr usage
   \<lbrace>P\<rbrace>"
  unfolding getRefillCapacity_def
  apply wpsimp
  apply (fastforce dest: readRefillCapacity_SomeD)
  done

lemma readRefillSufficient_SomeD:
  "readRefillSufficient scPtr usage s = Some sufficient
   \<Longrightarrow> \<exists>sc. scs_of' s scPtr = Some sc  \<and> sufficient = refillSufficient usage (refillHd sc)"
  apply (clarsimp simp: readRefillSufficient_def)
  apply (frule readRefillCapacity_SomeD)
  apply (fastforce simp: refillSufficient_def obj_at'_def opt_map_def split: option.splits)
  done

lemma getRefillSufficient_wp[wp]:
  "\<lbrace>\<lambda>s. \<forall>sc. scs_of' s scPtr = Some sc \<longrightarrow> P (refillSufficient usage (refillHd sc)) s\<rbrace>
   getRefillSufficient scPtr usage
   \<lbrace>P\<rbrace>"
  unfolding getRefillSufficient_def
  apply wpsimp
  apply (fastforce dest: readRefillSufficient_SomeD)
  done

(* projection rewrites *)

lemma pred_map_rewrite:
  "pred_map P proj = opt_pred P proj"
  by (fastforce simp: pred_map_def2 opt_pred_def)

abbreviation sc_of2 :: "Structures_A.kernel_object \<rightharpoonup> Structures_A.sched_context" where
  "sc_of2 ko \<equiv> case ko of kernel_object.SchedContext sc n \<Rightarrow> Some sc | _ \<Rightarrow> None"

abbreviation scs_of2 :: "'z state \<Rightarrow> obj_ref \<rightharpoonup> Structures_A.sched_context" where
  "scs_of2 \<equiv> (\<lambda>s. kheap s |> sc_of2)"

lemma scs_of_rewrite:
  "scs_of s = scs_of2 s"
  by (fastforce simp: sc_heap_of_state_def opt_map_def
              split: option.splits Structures_A.kernel_object.splits)

abbreviation sc_replies_of2 :: "'z state \<Rightarrow> obj_ref \<Rightarrow>obj_ref list option" where
  "sc_replies_of2 s \<equiv> scs_of2 s ||> sc_replies"

lemma sc_replies_of_rewrite:
  "sc_replies_of s = sc_replies_of2 s"
  by (fastforce simp: sc_heap_of_state_def sc_replies_of_scs_def opt_map_def map_project_def
              split: option.splits Structures_A.kernel_object.splits)

definition sc_replies_relation2_2 ::
  "(obj_ref \<rightharpoonup> obj_ref list) \<Rightarrow> (obj_ref \<rightharpoonup> obj_ref) \<Rightarrow> (obj_ref \<rightharpoonup> obj_ref) \<Rightarrow> bool"
  where
  "sc_replies_relation2_2 sc_repls scRepl replPrevs \<equiv>
     \<forall>p replies. sc_repls p = Some replies \<longrightarrow> heap_ls replPrevs (scRepl p) replies"

abbreviation sc_replies_relation2 :: "det_state \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "sc_replies_relation2 s s' \<equiv>
    sc_replies_relation2_2 (sc_replies_of2 s) (scReplies_of s') (replyPrevs_of s')"

lemmas sc_replies_relation2_def = sc_replies_relation2_2_def

lemma sc_replies_relation_rewrite:
  "sc_replies_relation s s' = sc_replies_relation2 s s'"
  unfolding sc_replies_relation_def sc_replies_relation2_def sc_replies_of_rewrite
  by simp

definition is_active_sc2 :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "is_active_sc2 p s \<equiv> ((\<lambda>sc. 0 < sc_refill_max sc) |< scs_of2 s) p"

definition active_sc_tcb_at' :: "obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "active_sc_tcb_at' tcbPtr s \<equiv> ((\<lambda>sc. 0 < scRefillMax sc) |< (tcbSCs_of s |> scs_of' s)) tcbPtr"

lemma is_active_sc_rewrite:
  "is_active_sc p s = is_active_sc2 p s"
  by (fastforce simp: is_active_sc2_def vs_all_heap_simps is_active_sc_def
                      active_sc_def opt_map_red opt_map_def opt_pred_def
               split: option.split_asm Structures_A.kernel_object.splits)

abbreviation valid_refills2 :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "valid_refills2 scp s \<equiv>
     ((\<lambda>sc. if sc_period sc = 0 then rr_valid_refills (sc_refills sc) (sc_refill_max sc) (sc_budget sc)
      else sp_valid_refills (sc_refills sc) (sc_refill_max sc) (sc_period sc) (sc_budget sc)) |<
     scs_of2 s) scp"

lemmas valid_refills2_def = rr_valid_refills_def sp_valid_refills_def

lemma valid_refills_rewrite:
  "valid_refills scp s = valid_refills2 scp s"
  by (fastforce simp: opt_map_red vs_all_heap_simps valid_refills_def opt_pred_def
               elim!: opt_mapE
               split: option.splits Structures_A.kernel_object.splits)

definition round_robin2 :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "round_robin2 sc_ptr s \<equiv> ((\<lambda>sc. sc_period sc = 0) |< scs_of2 s) sc_ptr"

lemma round_robin_rewrite:
  "round_robin scp s = round_robin2 scp s"
  by (clarsimp simp: round_robin_def round_robin2_def vs_all_heap_simps opt_map_def opt_pred_def
               elim!: opt_mapE
              split: option.splits Structures_A.kernel_object.splits)

abbreviation sc_refills_sc_at2 ::
  "(Structures_A.refill list \<Rightarrow> bool) \<Rightarrow> obj_ref \<Rightarrow> 'z state \<Rightarrow> bool"
  where
  "sc_refills_sc_at2 P scp s \<equiv> ((\<lambda>sc. P (sc_refills sc)) |< scs_of2 s) scp"

lemma sc_refills_sc_at_rewrite:
  "sc_refills_sc_at P scp s = sc_refills_sc_at2 P scp s"
  by (fastforce simp: sc_refills_sc_at_def obj_at_def is_sc_obj opt_map_red opt_pred_def
               elim!: opt_mapE
               split: option.splits Structures_A.kernel_object.split_asm)

lemmas projection_rewrites = pred_map_rewrite scs_of_rewrite is_active_sc_rewrite
                             sc_heap_of_state_def sc_refills_sc_at_rewrite
                             active_sc_at'_rewrite valid_refills_rewrite round_robin_rewrite

lemma is_active_sc'_cross:
  "\<lbrakk>pspace_relation (kheap s) (ksPSpace s'); is_active_sc2 ptr s\<rbrakk>
   \<Longrightarrow> is_active_sc' ptr s'"
  supply projection_rewrites[simp]
  apply (clarsimp simp: is_active_sc2_def is_active_sc'_def opt_pred_def
                 split: option.split_asm Structures_A.kernel_object.split_asm elim!: opt_mapE)
  apply (drule (1) pspace_relation_absD, clarsimp split: if_split_asm)
  apply (case_tac z; simp add: sc_relation_def opt_map_red)
  done

lemma set_refills_is_active_sc2[wp]:
  "set_refills ptr new \<lbrace>is_active_sc2 ptr'\<rbrace>"
  apply (wpsimp simp: is_active_sc2_def wp: set_refills_wp)
  by (clarsimp simp: obj_at_def opt_map_def opt_pred_def)

(* end : projection rewrites *)

(* updateSchedContext *)

lemma no_fail_updateSchedContext[wp]:
  "no_fail (sc_at' ptr and (\<lambda>s'. ((\<lambda>k::sched_context. objBits k = objBits (f k)) |< scs_of' s') ptr))
           (updateSchedContext ptr f)"
  by (wpsimp simp: updateSchedContext_def obj_at'_def opt_map_def opt_pred_def)

lemma updateSchedContext_sc_obj_at':
  "\<lbrace>if scPtr = scPtr' then (\<lambda>s. \<forall>ko. ko_at' ko scPtr' s \<longrightarrow> P (f ko)) else obj_at' P scPtr'\<rbrace>
   updateSchedContext scPtr f
   \<lbrace>\<lambda>rv. obj_at' P scPtr'\<rbrace>"
  supply if_split [split del]
  apply (simp add: updateSchedContext_def)
  apply (wpsimp wp: set_sc'.obj_at')
  apply (clarsimp split: if_splits simp: obj_at'_real_def ko_wp_at'_def)
  done

lemma updateSchedContext_sc_obj_at'_inv:
  "(\<And>sc. P (f sc) = P sc) \<Longrightarrow> updateSchedContext scPtr f \<lbrace>\<lambda>s. Q (obj_at' P scPtr' s)\<rbrace>"
  unfolding updateSchedContext_def
  by (wpsimp wp: set_sc'.obj_at')
     (clarsimp split: if_splits simp: obj_at'_real_def ko_wp_at'_def)

lemma update_sched_context_rewrite:
  "monadic_rewrite False True (sc_obj_at n scp)
    (update_sched_context scp f)
    (do sc \<leftarrow> get_sched_context scp;
        set_object scp (kernel_object.SchedContext (f sc) n)
     od)"
  apply (clarsimp simp: update_sched_context_def get_sched_context_def bind_assoc)
  apply (rule monadic_rewrite_bind_tail[OF _ get_object_sp])
  apply (rename_tac obj)
  apply (case_tac obj;
         fastforce simp: monadic_rewrite_pre_imp_eq set_object_def monadic_rewrite_def obj_at_def
                         is_sc_obj_def)
  done

lemmas sc_inv_state_eq' = getObject_sc_inv[THEN use_valid[rotated], rotated,
                                           where s=s and P="(=) s" for s, OF _ refl]

lemma sc_inv_state_eq:
  "(a :: sched_context, s') \<in> fst (getSchedContext p s) \<Longrightarrow> s' = s"
  by (fastforce dest: sc_inv_state_eq' simp: getSchedContext_def)

lemma getObject_idempotent:
  "monadic_rewrite False True (sc_at' ptr)
   (do rv \<leftarrow> (getObject ptr :: sched_context kernel);
       getObject ptr
    od)
   (getObject ptr :: sched_context kernel)"
  apply (clarsimp simp: monadic_rewrite_def)
  apply (rule monad_state_eqI)
    apply ((clarsimp simp: in_monad getObject_def split_def
                           loadObject_default_def scBits_pos_power2 gen_objBits_simps
                           lookupAround2_known1 in_magnitude_check)+)[2]
  apply (fastforce dest!: sc_inv_state_eq[simplified getSchedContext_def]
                          no_fail_getObject_misc[simplified no_fail_def, rule_format]
                    simp: snd_bind)
  done

(* end : updateSchedContext *)

(* this lets cross the sc size information from concrete to abstract *)
lemma ko_at_sc_cross:
  "\<lbrakk>pspace_relation (kheap s) (ksPSpace s'); ko_at' (sc'::sched_context) ptr s'\<rbrakk>
   \<Longrightarrow> sc_obj_at (objBits sc' - minSchedContextBits) ptr s"
  by (fastforce dest: scs_relation_sc_relation_conc
                simp: pspace_relation_heap_pspace_relation obj_at'_def obj_at_def is_sc_obj_def
                      gen_objBits_simps sc_relation_def)

lemma ko_at'_inj:
  "ko_at' ko ptr  s \<Longrightarrow> ko_at' ko' ptr s \<Longrightarrow> ko' = ko"
  by (clarsimp simp: obj_at'_real_def ko_wp_at'_def)

(* FIXME RT: Move these to AInvs where possible *)
(* FIXME RT: Try to unify with existing notions.
             See https://sel4.atlassian.net/browse/VER-1382 *)
definition injective_ref where
  "injective_ref ref heap \<equiv> (\<forall>q p1 p2. (p1, ref) \<in> heap q \<and> (p2, ref) \<in> heap q \<longrightarrow> p1 = p2)"

lemma sym_refs_inj:
  "\<lbrakk>sym_refs heap; injective_ref (symreftype ref) heap; (x, ref) \<in> heap y; (x, ref) \<in> heap y'\<rbrakk>
   \<Longrightarrow> y = y' "
  apply (clarsimp simp: sym_refs_def injective_ref_def)
  apply fastforce
  done

lemma sym_refs_inj2:
  "\<lbrakk>sym_refs heap; injective_ref ref heap; (x, ref) \<in> heap y; (y, symreftype ref) \<in> heap z\<rbrakk>
   \<Longrightarrow> x = z "
  apply (subgoal_tac "(y, symreftype ref) \<in> heap x")
   apply (erule (3) sym_refs_inj[where ref="symreftype ref", simplified])
  apply (fastforce simp: sym_refs_def)
  done

lemma injective_ref_SCTcb[simp]:
  "injective_ref SCTcb (state_refs_of' s) "
  apply (clarsimp simp: state_refs_of'_def injective_ref_def split: option.splits if_splits)
  apply (clarsimp simp: refs_of'_def)
  apply (rename_tac p0 ko p1 p2)
  apply (prop_tac "\<exists>z. ko = KOSchedContext z")
   apply (clarsimp split: kernel_object.splits)
     apply (clarsimp split: option.splits simp: get_refs_def)
    apply (clarsimp simp: tcb_st_refs_of'_def tcb_bound_refs'_def get_refs_def
                   split: Structures_H.thread_state.splits if_splits option.splits)
   apply (clarsimp simp: get_refs_def split: option.splits)
  apply (clarsimp simp: get_refs_def split: option.splits)
  done

lemma sch_act_simple_cross_rel:
  "cross_rel simple_sched_action sch_act_simple"
  apply (clarsimp simp: cross_rel_def)
  by (fastforce simp: simple_sched_action_def sch_act_simple_def
                dest: state_relation_sched_act_relation
               split: Structures_A.scheduler_action.splits)

lemma scheduler_act_sane_cross:
  "\<lbrakk>scheduler_act_sane s; (s, s') \<in> state_relation\<rbrakk> \<Longrightarrow> sch_act_sane s'"
  apply (clarsimp simp: scheduler_act_sane_def sch_act_sane_def)
  apply (frule state_relation_sched_act_relation)
  apply (drule curthread_relation)
  apply (cases "scheduler_action s"; clarsimp)
  done

lemma tcb_at'_ex1_ko_at':
  "tcb_at' t s \<Longrightarrow> \<exists>!tcb. ko_at' (tcb::tcb) t s"
  by (fastforce simp: obj_at'_def)

lemma ex1_ex_eq_all:
  "\<exists>!x. Q x \<Longrightarrow> (\<exists>x. Q x \<and> P x) = (\<forall>x. Q x \<longrightarrow> P x)"
  by fastforce

lemmas tcb_at'_ex_eq_all = ex1_ex_eq_all[OF tcb_at'_ex1_ko_at']

lemma receiveBlocked_equiv:
  "receiveBlocked st = is_BlockedOnReceive st"
  unfolding receiveBlocked_def
  by (case_tac st; simp)

lemma threadGet_getObject:
  "threadGet f t = do x <- getObject t;
                         return (f x)
                   od"
  apply (simp add: threadGet_def threadRead_def oliftM_def getObject_def[symmetric])
  done

lemma obj_at'_typ_at'[elim!]:
  "obj_at' (P :: ('a :: pspace_storable) \<Rightarrow> bool) p s \<Longrightarrow>
   obj_at' (\<top> :: ('a :: pspace_storable) \<Rightarrow> bool) p s"
  by (clarsimp simp: obj_at'_real_def ko_wp_at'_def)

lemma shows
  obj_at'_sc_tcbs_of_equiv:
    "obj_at' (\<lambda>x. scTCB x = Some t) p s = (sc_at' p s \<and> scTCBs_of s p = Some t)"
  and obj_at'_tcb_scs_of_equiv:
    "obj_at' (\<lambda>x. tcbSchedContext x = Some sc) p s = (tcb_at' p s \<and> tcbSCs_of s p = Some sc)"
  and obj_at'_replySCs_of_equiv:
    "obj_at' (\<lambda>a. replyNext a = Some (Head sc)) p s = (reply_at' p s \<and> replySCs_of s p = Some sc)"
  and obj_at'_scReplies_of_equiv:
    "obj_at' (\<lambda>a. scReply a = Some sc) p s = (sc_at' p s \<and> scReplies_of s p = Some sc)"
  by (intro iffI; clarsimp simp: obj_at'_real_def ko_wp_at'_def opt_map_def)+

lemma not_idle_scTCB:
  "\<lbrakk>sym_heap_tcbSCs s; valid_objs' s; valid_idle' s; p \<noteq> idle_sc_ptr; sc_at' p s\<rbrakk> \<Longrightarrow>
   obj_at' (\<lambda>x. scTCB x \<noteq> Some idle_thread_ptr) p s"
  apply (subgoal_tac "\<not>obj_at' (\<lambda>x. scTCB x = Some idle_thread_ptr) p s")
   apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def)
  apply (subst (asm) sym_heap_symmetric)
  apply (clarsimp simp: obj_at'_sc_tcbs_of_equiv sym_heap_def)
  apply (clarsimp simp: valid_idle'_def obj_at'_real_def ko_wp_at'_def idle_tcb'_def
                 elim!: opt_mapE)
  done

lemma not_idle_tcbSC:
  "\<lbrakk>sym_heap_tcbSCs s; valid_objs' s; valid_idle' s; p \<noteq> idle_thread_ptr; tcb_at' p s\<rbrakk> \<Longrightarrow>
   obj_at' (\<lambda>x. tcbSchedContext x \<noteq> Some idle_sc_ptr) p s"
  apply (subgoal_tac "\<not>obj_at' (\<lambda>x. tcbSchedContext x = Some idle_sc_ptr) p s")
   apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def)
  apply (clarsimp simp: obj_at'_tcb_scs_of_equiv sym_heap_def)
  apply (clarsimp simp: valid_idle'_def obj_at'_real_def ko_wp_at'_def idle_tcb'_def
                 elim!: opt_mapE)
  done

lemma setObject_tcb_tcbs_of':
  "\<lbrace>\<lambda>s. P' ((tcbs_of' s)(c \<mapsto> tcb))\<rbrace>
  setObject c (tcb::tcb)
  \<lbrace>\<lambda>_ s. P' (tcbs_of' s)\<rbrace>"
  by (setObject_easy_cases)

lemma threadSet_tcbSCs_of_inv:
  "\<forall>x. tcbSchedContext (f x) = tcbSchedContext x \<Longrightarrow>
  threadSet f t \<lbrace>\<lambda>s. P (tcbSCs_of s)\<rbrace>"
  unfolding threadSet_def
  apply (rule bind_wp[OF _ get_tcb_sp'])
  apply (wpsimp wp: setObject_tcb_tcbs_of')
  apply (erule subst[where P=P, rotated], rule ext)
  apply (clarsimp simp: opt_map_def obj_at'_real_def ko_wp_at'_def
                 split: option.splits)
  done

lemma aligned'_distinct'_obj_at'I:
  "\<lbrakk> \<exists>y. ksPSpace s p = Some (injectKO (y:: 'a::pspace_storable));
    pspace_aligned' s; pspace_distinct' s;
    (if koTypeOf (the (ksPSpace s p))  = SchedContextT then pspace_bounded' s else True)\<rbrakk>
   \<Longrightarrow> obj_at' (\<top> :: 'a::pspace_storable \<Rightarrow> bool) p s"
  apply (clarsimp)
  apply (frule_tac v=y in aligned'_distinct'_ko_at'I; simp?)
  apply (case_tac "injectKO y"; clarsimp simp: valid_sz_simps dest!: pspace_boundedD')
  done

lemma sym_refs_tcbSCs:
  "\<lbrakk>sym_refs (state_refs_of' s); pspace_aligned' s; pspace_distinct' s; pspace_bounded' s\<rbrakk>
   \<Longrightarrow> sym_heap_tcbSCs s"
  apply (clarsimp simp: sym_heap_def)
  apply (rule iffI)
   apply (drule_tac tp=SCTcb and x=p and y=p' in sym_refsE;
          force simp: get_refs_def2 state_refs_of'_def in_omonad refs_of_rev' tcb_bound_refs'_def
                dest: pspace_alignedD' pspace_distinctD' pspace_boundedD' elim!: opt_mapE
               split: if_split_asm option.split_asm)+
  by (drule_tac tp=TCBSchedContext and x=p' and y=p in sym_refsE;
      force simp: get_refs_def2 state_refs_of'_def in_omonad refs_of_rev'
            dest: pspace_alignedD' pspace_distinctD' pspace_boundedD'
           elim!: opt_mapE split: if_split_asm option.split_asm)+

lemma sym_refs_scReplies:
  "\<lbrakk>sym_refs (state_refs_of' s); pspace_aligned' s; pspace_distinct' s; pspace_bounded' s\<rbrakk>
   \<Longrightarrow> sym_heap_scReplies s"
  apply (clarsimp simp: sym_heap_def)
  apply (rule iffI)
   apply (drule_tac tp=ReplySchedContext and x=p and y=p' in sym_refsE;
          force simp: get_refs_def2 state_refs_of'_def opt_map_red refs_of_rev'
                dest: pspace_alignedD' pspace_distinctD' pspace_boundedD'
               elim!: opt_mapE
               split: if_split_asm option.split_asm)+
  by (drule_tac tp=SCReply and x=p' and y=p in sym_refsE;
      force simp: get_refs_def2 state_refs_of'_def opt_map_red refs_of_rev'
               dest: pspace_alignedD' pspace_distinctD' pspace_boundedD'
              elim!: opt_mapE
              split: if_split_asm option.split_asm)+

lemma setSchedContext_scTCBs_of:
  "\<lbrace>\<lambda>s. P (\<lambda>a. if a = scPtr then scTCB sc else scTCBs_of s a)\<rbrace>
   setSchedContext scPtr sc
   \<lbrace>\<lambda>_ s. P (scTCBs_of s)\<rbrace>"
  unfolding setSchedContext_def
  apply (wpsimp wp: setObject_sc_wp)
  apply (erule back_subst[where P=P], rule ext)
  by (clarsimp simp: opt_map_def)

lemma setSchedContext_scReplies_of:
  "\<lbrace>\<lambda>s. P (\<lambda>a. if a = scPtr then scReply sc else scReplies_of s a)\<rbrace>
   setSchedContext scPtr sc
   \<lbrace>\<lambda>_ s. P (scReplies_of s)\<rbrace>"
  unfolding setSchedContext_def
  apply (wpsimp wp: setObject_sc_wp)
  apply (erule back_subst[where P=P], rule ext)
  by (clarsimp simp: opt_map_def)

lemma updateSchedContext_scReplies_of:
  "(\<And>sc. scReply (f sc) = scReply sc) \<Longrightarrow> updateSchedContext scPtr f \<lbrace>\<lambda>s. P' (scReplies_of s)\<rbrace>"
  apply (wpsimp simp: updateSchedContext_def wp: setSchedContext_scReplies_of)
  apply (auto elim!: rsubst[where P=P'] simp: opt_map_def obj_at'_def)
  done

lemma getObject_tcb_wp:
  "\<lbrace>\<lambda>s. tcb_at' p s \<longrightarrow> (\<exists>t::tcb. ko_at' t p s \<and> Q t s)\<rbrace> getObject p \<lbrace>Q\<rbrace>"
  by (clarsimp simp: getObject_def valid_def in_monad
                     split_def gen_objBits_simps loadObject_default_def
                     obj_at'_def in_magnitude_check
              dest!: readObject_misc_ko_at')

lemma threadSet_tcbSCs_of:
  "\<lbrace>\<lambda>s. P (\<lambda>a. if a = t then tcbSchedContext (f (the (tcbs_of' s a))) else tcbSCs_of s a)\<rbrace>
   threadSet f t
   \<lbrace>\<lambda>_ s. P (tcbSCs_of s)\<rbrace>"
  unfolding threadSet_def
  apply (wpsimp wp: setObject_tcb_wp getObject_tcb_wp)
  apply (clarsimp simp: tcb_at'_ex_eq_all)
  apply (erule back_subst[where P=P], rule ext)
  apply (clarsimp simp: opt_map_def obj_at'_real_def ko_wp_at'_def)
  done

lemma shows
  replyNexts_Some_replySCs_None:
  "replyNexts_of s rp \<noteq> None \<Longrightarrow> replySCs_of s rp = None" and
  replySCs_Some_replyNexts_None:
  "replySCs_of s rp \<noteq> None \<Longrightarrow> replyNexts_of s rp = None"
  by (clarsimp simp: opt_map_def split: option.splits reply_next.splits)+

lemma pred_tcb_at'_equiv:
  "pred_tcb_at' p P t s = (tcb_at' t s \<and> P (p (tcb_to_itcb' (the (tcbs_of' s t)))))"
  by (rule iffI;
      clarsimp simp: pred_tcb_at'_def pred_map_def obj_at'_real_def ko_wp_at'_def opt_map_def)

lemma isBlockedOnSend_equiv:
  "isBlockedOnSend st = is_BlockedOnSend st"
  by (case_tac st; simp add: isBlockedOnSend_def)

lemma isSend_equiv:
  "isSend st = is_BlockedOnSend st"
  by (case_tac st; simp add: isSend_def)

lemma sch_act_wf_not_runnable_sch_act_not:
  "\<lbrakk>st_tcb_at' P t s; sch_act_wf (ksSchedulerAction s) s; \<forall>st. P st \<longrightarrow> \<not> runnable' st\<rbrakk> \<Longrightarrow>
   sch_act_not t s"
   by (clarsimp simp: pred_tcb_at'_def obj_at'_def)

lemma isTimeoutFault_fault_map[simp]:
  "isTimeoutFault (fault_map a) = is_timeout_fault a"
  by (clarsimp simp: isTimeoutFault_def fault_map_def is_timeout_fault_def
              split: ExceptionTypes_A.fault.splits)

lemma valid_bound_obj_lift:
  "f \<lbrace>P (the x)\<rbrace> \<Longrightarrow> f \<lbrace>valid_bound_obj P x\<rbrace>"
  unfolding valid_bound_obj_def
  by (case_tac x; wpsimp)

lemma valid_bound_obj'_lift:
  "f \<lbrace>P (the x)\<rbrace> \<Longrightarrow> f \<lbrace>valid_bound_obj' P x\<rbrace>"
  unfolding valid_bound_obj'_def
  by (case_tac x; wpsimp)

lemma sch_act_not_cross_rel:
  "cross_rel (scheduler_act_not t) (sch_act_not t)"
  unfolding cross_rel_def state_relation_def
  apply clarsimp
  apply (case_tac "scheduler_action s"; simp)
  by (clarsimp simp: scheduler_act_not_def sched_act_relation_def)

global_interpretation set_simple_ko: typ_at_pres "set_simple_ko C ptr ep"
  unfolding typ_at_pres_def by wpsimp

global_interpretation update_sk_obj_ref: typ_at_pres "update_sk_obj_ref C update ref new"
  unfolding typ_at_pres_def by wpsimp

lemma getReprogramTimer_corres:
  "corres (=) \<top> \<top> (gets reprogram_timer) getReprogramTimer"
  by (clarsimp simp: getReprogramTimer_def state_relation_def)

lemma setDomainTime_corres:
  "dt = dt' \<Longrightarrow>
  corres dc \<top> \<top> (modify (domain_time_update (\<lambda>_. dt))) (setDomainTime dt')"
  apply (clarsimp simp: setDomainTime_def, rule corres_modify)
  by (clarsimp simp: state_relation_def swp_def)

lemma setConsumedTime_corres:
  "ct = ct' \<Longrightarrow>
  corres dc \<top> \<top> (modify (consumed_time_update (\<lambda>_. ct))) (setConsumedTime ct')"
  apply (clarsimp simp: setConsumedTime_def, rule corres_modify)
  by (clarsimp simp: state_relation_def swp_def)

lemma setCurSc_corres:
  "sc = sc' \<Longrightarrow>
   corres dc \<top> \<top> (modify (cur_sc_update (\<lambda>_. sc))) (setCurSc sc')"
  apply (clarsimp simp: setCurSc_def, rule corres_modify)
  by (clarsimp simp: state_relation_def swp_def)

lemma refillSingle_equiv:
  "sc_valid_refills' sc \<Longrightarrow>
   (length (refills_map (scRefillHead sc) (refillSize sc) (scRefillMax sc) (scRefills sc)) = Suc 0)
   = (scRefillHead sc = scRefillTail sc)"
  apply (clarsimp simp: valid_sched_context'_def refills_map_def refillSize_def)
  apply (fastforce simp: Let_def)
  done


lemma getNotification_corres:
  "corres ntfn_relation (ntfn_at ptr) (pspace_aligned' and pspace_distinct')
     (get_notification ptr) (getNotification ptr)"
  apply (rule_tac Q'="ntfn_at' ptr" in corres_cross_add_guard)
   apply (frule state_relation_pspace_relation)
   apply (clarsimp simp: pspace_relation_heap_pspace_relation)
   apply (frule heap_pspace_relation_ntfns_relation)
   apply (clarsimp simp: obj_at_def is_ntfn_def)
   apply (rename_tac ko; case_tac ko; clarsimp)
   apply (fastforce dest!: ntfns_relation_ntfn_relation_abs_obj_at'
                     simp: obj_at'_def)
  apply (rule corres_no_failI)
   apply wpsimp
  apply (simp add: get_simple_ko_def getNotification_def get_object_def
                   getObject_def bind_assoc gets_the_def)
  apply (clarsimp simp: in_monad split_def bind_def gets_def get_def return_def
                 dest!: readObject_misc_ko_at')
  apply (clarsimp simp: assert_def fail_def obj_at_def return_def is_ntfn partial_inv_def)
  apply (clarsimp simp add: state_relation_def pspace_relation_def obj_at'_def)
  apply (drule bspec)
   apply blast
  apply (simp add: ntfn_relation_cut_def ntfn_relation_def)
  done

lemma get_sc_corres:
  "corres (\<lambda>sc sc'. \<exists>n. sc_relation sc n sc')
     (sc_at ptr ) (pspace_aligned' and pspace_distinct' and pspace_bounded')
     (get_sched_context ptr) (getSchedContext ptr)"
  apply (rule_tac Q'="sc_at' ptr" in corres_cross_add_guard)
   apply (frule state_relation_pspace_relation)
   apply (clarsimp simp: pspace_relation_heap_pspace_relation)
   apply (frule heap_pspace_relation_scs_relation)
   apply (clarsimp simp: obj_at_def is_sc_obj_def)
   apply (rename_tac ko n; case_tac ko; clarsimp)
   apply (fastforce dest!: scs_relation_sc_relation_abs_obj_at'
                     simp: obj_at'_def)
  apply (subst corres_bind_return)
   apply (subst corres_bind_return2)
    apply (rule corres_symb_exec_l[OF _ _ get_sched_context_sp])
      apply (rule corres_symb_exec_r[OF _ get_sc_sp'])
        apply (fastforce intro: state_relation_sc_relation'' simp: obj_at_def is_sc_obj_def)
       apply wpsimp
      apply wpsimp
     apply (rule get_sched_context_exs_valid)
     apply (fastforce intro: sc_atD1)
    apply wpsimp
    apply (fastforce intro: sc_atD1)
   apply simp+
  done

lemma refillSingle_corres:
  "scp = scp' \<Longrightarrow>
   corres (=)
     (sc_at scp)
     (pspace_aligned' and pspace_distinct' and pspace_bounded' and obj_at' sc_valid_refills' scp')
     (refill_single scp)
     (refillSingle scp')"
  apply (simp add: refill_single_def readRefillSingle_def refillSingle_def
                   refill_size_def get_refills_def readSchedContext_def
             flip: getSchedContext_def getObject_def)
  apply (rule stronger_corres_guard_imp)
    apply (rule_tac R'="\<lambda>sc s. sc_valid_refills' sc" and R="\<lambda>_ _ . True" in corres_split)
       apply (rule get_sc_corres)
      apply simp
      apply (metis (mono_tags, opaque_lifting) refillSingle_equiv sc_relation_def)
     apply wpsimp+
  apply (clarsimp simp: obj_at'_def)
  done

lemma active_sc_at'_cross:
  "\<lbrakk>(s,s') \<in> state_relation; pspace_aligned' s'; pspace_distinct' s'; pspace_bounded' s';
    is_active_sc sc_ptr s; sc_at sc_ptr s\<rbrakk>
   \<Longrightarrow> active_sc_at' sc_ptr s'"
  apply (frule state_relation_pspace_relation)
  apply (frule (4) sc_at_cross)
  apply (clarsimp simp: pspace_relation_def obj_at_def is_sc_obj_def)
  apply (drule_tac x=sc_ptr in bspec, blast)
  apply (clarsimp simp: sc_relation_def vs_all_heap_simps active_sc_at'_def obj_at'_def active_sc_def)
  done

lemma active_sc_at'_cross_valid_objs:
  "\<lbrakk>(s,s') \<in> state_relation; pspace_aligned' s'; pspace_distinct' s'; pspace_bounded' s';
    is_active_sc sc_ptr s; valid_objs s\<rbrakk>
   \<Longrightarrow> active_sc_at' sc_ptr s'"
  apply (frule state_relation_pspace_relation)
  apply (frule (3) sc_at_cross_valid_objs)
    apply (fastforce simp: vs_all_heap_simps )
   apply fastforce
  apply (clarsimp simp: vs_all_heap_simps )
  apply (frule valid_objs_valid_sched_context_size)
   apply fastforce
  apply (clarsimp simp: pspace_relation_def)
  apply (drule_tac x=sc_ptr in bspec, blast)
  apply (clarsimp simp: sc_relation_def active_sc_at'_def obj_at'_def active_sc_def)
  done

lemma is_active_sc'2_cross:
  "\<lbrakk>(s,s') \<in> state_relation; pspace_aligned' s'; pspace_distinct' s'; pspace_bounded' s';
    is_active_sc sc_ptr s; sc_at sc_ptr s\<rbrakk>
   \<Longrightarrow> is_active_sc' sc_ptr s'"
  apply (frule state_relation_pspace_relation)
  apply (frule (4) sc_at_cross)
  apply (clarsimp simp: pspace_relation_def obj_at_def is_sc_obj_def)
  apply (drule_tac x=sc_ptr in bspec, blast)
  apply (clarsimp simp: sc_relation_def vs_all_heap_simps obj_at'_def
                        active_sc_def opt_map_red StateRelation.is_active_sc'_def opt_pred_def)
  done

lemma active_sc_tcb_at_cross:
  "\<lbrakk>(s, s') \<in> state_relation; active_sc_tcb_at tcbPtr s; pspace_aligned' s'; pspace_distinct' s';
    pspace_bounded' s'; valid_objs s\<rbrakk>
   \<Longrightarrow> active_sc_tcb_at' tcbPtr s'"
  apply (clarsimp simp: vs_all_heap_simps)
  apply (rename_tac sc_ptr tcb sc n)
  apply (frule_tac state_relation_pspace_relation)
  apply (frule (2) tcb_at_cross[where t=tcbPtr])
   apply (clarsimp simp: obj_at_def is_tcb_def)
  apply (frule (1) pspace_relation_absD[where x=tcbPtr])
  apply clarsimp
  apply (rename_tac ko, case_tac ko; clarsimp simp: tcb_relation_cut_def)
  apply (frule (3) active_sc_at'_cross_valid_objs)
    apply (fastforce simp: vs_all_heap_simps)
   apply fastforce
  apply (rename_tac tcb')
  apply (prop_tac "tcbSchedContext tcb' = Some sc_ptr")
   apply (clarsimp simp: tcb_relation_def)
  apply (clarsimp simp: active_sc_tcb_at'_def in_omonad obj_at'_def active_sc_at'_def)
  done

defs tcbInReleaseQueue_imp_active_sc_tcb_at'_asrt_def:
  "tcbInReleaseQueue_imp_active_sc_tcb_at'_asrt \<equiv>
     \<lambda>s'. \<forall>tcbPtr.
           (tcbInReleaseQueue |< tcbs_of' s') tcbPtr
           \<longrightarrow> (tcb_at' tcbPtr s' \<and> active_sc_tcb_at' tcbPtr s')"

declare tcbInReleaseQueue_imp_active_sc_tcb_at'_asrt_def[simp]

lemma release_queue_active_sc_tcb_at_cross:
  "\<lbrakk>(s, s') \<in> state_relation; valid_release_q s;
    pspace_aligned' s'; pspace_distinct' s'; pspace_bounded' s'; valid_objs s\<rbrakk>
   \<Longrightarrow> \<forall>tcbPtr. (tcbInReleaseQueue |< tcbs_of' s') tcbPtr
                \<longrightarrow> (tcb_at' tcbPtr s' \<and> active_sc_tcb_at' tcbPtr s')"
  apply (clarsimp simp: valid_release_q_def)
  apply (drule_tac x=tcbPtr in bspec)
   apply (fastforce dest: heap_ls_unique state_relation_release_queue_relation
                    simp: release_queue_relation_def list_queue_relation_def)
  apply (rule conjI)
   apply (fastforce intro!: tcb_at_cross simp: obj_at_def is_tcb_def vs_all_heap_simps)
  apply (fastforce elim: active_sc_tcb_at_cross)
  done

lemma obj_at'_prop:
  "obj_at' P p s \<Longrightarrow> \<exists>ko obj. ksPSpace s p = Some ko \<and> projectKO ko s = Some obj \<and> P obj"
  by (fastforce simp: obj_at'_def')

lemma in_release_q_tcbInReleaseQueue_eq:
  "release_queue_relation s s' \<Longrightarrow> in_release_queue t s \<longleftrightarrow> (tcbInReleaseQueue |< tcbs_of' s') t"
  by (clarsimp simp: release_queue_relation_def list_queue_relation_def in_release_q_def)

lemma in_set_ready_queues_inQ_eq:
  "ready_queues_relation s s' \<Longrightarrow> t \<in> set (ready_queues s d p) \<longleftrightarrow> (inQ d p |< tcbs_of' s') t"
  by (clarsimp simp: ready_queues_relation_def ready_queue_relation_def Let_def)

lemma in_ready_q_tcbQueued_eq:
  "ready_queues_relation s s' \<Longrightarrow> in_ready_q t s \<longleftrightarrow> (tcbQueued |< tcbs_of' s') t"
  apply (intro iffI)
   apply (clarsimp simp: in_ready_q_def)
   apply (frule in_set_ready_queues_inQ_eq)
   apply (fastforce simp: inQ_def opt_map_def opt_pred_def split: option.splits)
  apply (fastforce simp: ready_queues_relation_def ready_queue_relation_def Let_def inQ_def
                         opt_pred_def in_ready_q_def
                  split: option.splits)
  done

lemma ready_or_release_cross:
  "\<lbrakk>ready_or_release s; ready_queues_relation s s'; release_queue_relation s s'\<rbrakk>
   \<Longrightarrow> ready_or_release' s'"
  apply (clarsimp simp: ready_or_release'_def ready_or_release_def opt_pred_conj[symmetric])
  apply (fastforce dest: in_release_q_tcbInReleaseQueue_eq in_ready_q_tcbQueued_eq)
  done

\<comment> \<open>Some methods to add invariants to the concrete guard of a corres proof. Often used for properties
    that are asserted to hold in the Haskell definition.\<close>

method add_sym_refs =
  rule_tac Q'="\<lambda>s'. sym_refs (state_refs_of' s')" in corres_cross_add_guard,
  (clarsimp simp: pred_conj_def)?,
  (elim conjE)?,
  (frule invs_sym_refs)?, (frule invs_psp_aligned)?, (frule invs_distinct)?,
  fastforce dest: sym_refs_cross

method add_ct_not_inQ =
  rule_tac Q'="\<lambda>s'. ct_not_inQ s'" in corres_cross_add_guard,
  (frule valid_sched_valid_sched_action)?,
  fastforce intro!: ct_not_inQ_cross simp: valid_sched_def

method add_sch_act_wf =
  rule_tac Q'="\<lambda>s'. sch_act_wf (ksSchedulerAction s') s'" in corres_cross_add_guard,
  fastforce intro!: sch_act_wf_cross simp: valid_sched_def

method add_ct_idle_or_in_cur_domain' =
  rule_tac Q'="\<lambda>s'. ct_idle_or_in_cur_domain' s'" in corres_cross_add_guard,
  fastforce intro!: ct_idle_or_in_cur_domain'_cross simp: valid_sched_def

method add_valid_idle' =
  rule_tac Q'="\<lambda>s'. valid_idle' s'" in corres_cross_add_guard,
  fastforce intro!: valid_idle'_cross

method add_ready_qs_runnable =
  rule_tac Q'=ready_qs_runnable in corres_cross_add_guard,
  (clarsimp simp: pred_conj_def)?,
  (frule valid_sched_valid_ready_qs)?, (frule invs_psp_aligned)?, (frule invs_distinct)?,
  fastforce dest: ready_qs_runnable_cross

method add_valid_replies for rptr uses simp =
  rule_tac Q'="\<lambda>s. valid_replies'_sc_asrt rptr s" in corres_cross_add_guard,
  fastforce elim: valid_replies_sc_cross simp: simp

method add_cur_tcb' =
  rule_tac Q'="\<lambda>s'. cur_tcb' s'" in corres_cross_add_guard,
  fastforce intro!: cur_tcb_cross

method add_active_sc_at' for scPtr :: machine_word =
  rule_tac Q'="\<lambda>s'. active_sc_at' scPtr s'" in corres_cross_add_guard,
  fastforce intro!: active_sc_at'_cross

definition ready_queues_runnable_except_set :: "obj_ref set \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
  "ready_queues_runnable_except_set except s \<equiv>
     \<forall>d p. \<forall>t\<in>set (ready_queues s d p). t \<notin> except \<longrightarrow> st_tcb_at runnable t s"

abbreviation "ready_queues_runnable s \<equiv> ready_queues_runnable_except_set {} s"

lemmas ready_queues_runnable_def = ready_queues_runnable_except_set_def

definition release_q_runnable_except_set :: "obj_ref set \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
  "release_q_runnable_except_set except s \<equiv>
     \<forall>t\<in>set (release_queue s). t \<notin> except \<longrightarrow> st_tcb_at runnable t s"

abbreviation "release_q_runnable s \<equiv> release_q_runnable_except_set {} s"

lemmas release_q_runnable_def = release_q_runnable_except_set_def

definition in_correct_ready_q :: "'z state \<Rightarrow> bool" where
  "in_correct_ready_q s \<equiv>
     \<forall>d p. \<forall>t\<in>set (ready_queues s d p).
            pred_map (\<lambda>t. etcb_priority t = p \<and> etcb_domain t = d) (etcbs_of s) t"

definition ready_qs_distinct :: "'z state \<Rightarrow> bool" where
  "ready_qs_distinct s \<equiv> \<forall>d p. distinct (ready_queues s d p)"

lemma in_correct_ready_q_lift:
  assumes e: "\<And>P. f \<lbrace>\<lambda>s. P (etcbs_of s)\<rbrace>"
  assumes r: "\<And>P. f \<lbrace>\<lambda>s. P (ready_queues s)\<rbrace>"
  shows "f \<lbrace>in_correct_ready_q\<rbrace>"
  unfolding in_correct_ready_q_def
  apply (rule hoare_pre)
   apply (wps assms | wpsimp)+
  done

lemma in_correct_ready_qD:
  "\<lbrakk>tcb_ptr \<in> set (ready_queues s d p); kheap s tcb_ptr = Some (TCB tcb); in_correct_ready_q s\<rbrakk>
   \<Longrightarrow> tcb_domain tcb = d \<and> tcb_priority tcb = p "
  by (fastforce simp: in_correct_ready_q_def vs_all_heap_simps)

lemma in_correct_ready_q_in_ready_q:
  "\<lbrakk>kheap s tcb_ptr = Some (TCB tcb); in_correct_ready_q s\<rbrakk>
   \<Longrightarrow> tcb_ptr \<in> set (ready_queues s (tcb_domain tcb) (tcb_priority tcb))
       = in_ready_q tcb_ptr s"
  by (fastforce simp: in_correct_ready_q_def in_ready_q_def vs_all_heap_simps)

lemma sched_flag_set_live:
  "\<lbrakk>kheap s ptr = Some (TCB tcb); sched_flag_set s' ptr; tcbs_relation s s';
    ready_queues_relation s s'; release_queue_relation s s'; ready_queues_runnable s;
    in_correct_ready_q s; release_q_runnable s; pspace_aligned' s'; pspace_distinct' s'\<rbrakk>
   \<Longrightarrow> live (TCB tcb)"
  apply (frule (1) tcbs_relation_tcb_relation_abs)
  apply clarsimp
  apply (elim disjE)
    apply (frule (1) in_ready_q_tcbQueued_eq[THEN iffD2])
    apply (clarsimp simp: live_def ready_queues_runnable_def)
    apply (drule_tac x="tcb_domain tcb" in spec)
    apply (drule_tac x="tcb_priority tcb" in spec)
    apply (drule_tac x=ptr in bspec)
     apply (force simp: in_correct_ready_qD in_ready_q_def)
    apply (fastforce simp: pred_tcb_at_def obj_at_def split: Structures_A.thread_state.splits)
   apply (frule (1) in_release_q_tcbInReleaseQueue_eq[THEN iffD2])
   apply (fastforce simp: live_def release_q_runnable_def in_release_q_def
                          pred_tcb_at_def obj_at_def)
  apply (prop_tac "st_tcb_at' inIPCQueueThreadState ptr s'")
   apply (fastforce intro: aligned'_distinct'_obj_at'_propI
                     simp: st_tcb_at'_def opt_pred_def opt_map_red)
  apply (fastforce dest: st_tcb_at_coerce_abstract' simp: pred_tcb_at_def obj_at_def live_def)
  done

lemma live'_sc_cross:
  "\<lbrakk>live_sc' sc'; kheap s ptr = Some (Structures_A.SchedContext sc n);
    ksPSpace s' ptr = Some (KOSchedContext sc'); sc_relation sc n sc'; sc_replies_relation s s'\<rbrakk>
   \<Longrightarrow> live (Structures_A.SchedContext sc n)"
  apply (clarsimp simp: live_sc'_def)
  apply (elim disjE)
     apply (clarsimp simp: sc_relation_def live_def live_sc_def)
    apply (clarsimp simp: sc_relation_def live_def live_sc_def)
   apply (clarsimp simp: sc_relation_def live_def live_sc_def)
  apply (clarsimp simp: obj_at_def live_def live_sc_def sc_replies_relation_def)
  apply (drule_tac x=ptr in spec)
  apply (fastforce simp: sc_replies_of_scs_def map_project_def scs_of_kh_def opt_map_def)
  done

lemma live'_reply_cross:
  "\<lbrakk>live_reply' reply'; kheap s ptr = Some (Structures_A.Reply reply);
    ksPSpace s' ptr = Some (KOReply reply'); reply_relation reply reply'; valid_replies' s';
    pspace_aligned' s'; pspace_distinct' s'\<rbrakk>
   \<Longrightarrow> live (Structures_A.Reply reply)"
  apply (clarsimp simp: reply_relation_def live_def live_reply_def live_reply'_def
                        valid_replies'_def)
  apply (drule_tac x=ptr in spec)
  apply (elim disjE)
   apply (clarsimp simp: opt_map_red)
   apply (prop_tac "\<exists>y. replyNexts_of s' ptr = Some y")
    apply (clarsimp simp: opt_map_red)
    apply (rename_tac reply_next, case_tac reply_next; clarsimp)
   apply (clarsimp simp: opt_map_red)
  apply (fastforce dest: spec[where x=ptr] simp: opt_map_red)
  done

lemma pspace_relation_cte_wp_at:
  "\<lbrakk>pspace_relation (kheap s) (ksPSpace s'); cte_wp_at ((=) c) (cref, oref) s; pspace_aligned' s';
    pspace_distinct' s'\<rbrakk>
   \<Longrightarrow> cte_wp_at' (\<lambda>cte. cap_relation c (cteCap cte)) (cte_map (cref, oref)) s'"
  apply (simp add: cte_wp_at_cases)
  apply (erule disjE)
   apply clarsimp
   apply (drule(1) pspace_relation_absD)
   apply (simp add: unpleasant_helper)
   apply (drule spec, drule mp, erule domI)
   apply (clarsimp simp: cte_relation_def)
   apply (drule(2) aligned'_distinct'_ko_at'I[where 'a=cte], simp)
    apply simp
   apply (drule ko_at_imp_cte_wp_at')
   apply (clarsimp elim!: cte_wp_at_weakenE')
  apply clarsimp
  apply (drule(1) pspace_relation_absD)
  apply (clarsimp simp: tcb_relation_cut_def)
  apply (simp split: kernel_object.split_asm)
  apply (drule(2) aligned'_distinct'_ko_at'I[where 'a=tcb], simp)
   apply simp
  apply (drule tcb_cases_related)
  apply (clarsimp simp: obj_at'_def gen_objBits_simps)
  apply (erule(2) cte_wp_at_tcbI')
   apply fastforce
  apply simp
  done

lemma ex_nonz_cap_to_ep_at_cross:
  "\<lbrakk>ex_nonz_cap_to ptr s; ep_at ptr s; valid_objs s; pspace_relation (kheap s) (ksPSpace s');
    pspace_aligned' s'; pspace_distinct' s'\<rbrakk>
   \<Longrightarrow> ex_nonz_cap_to' ptr s'"
  apply (clarsimp simp: ex_nonz_cap_to_def cte_wp_at_caps_of_state ex_nonz_cap_to'_def)
  apply (rename_tac oref cref cap)
  apply (frule (1) caps_of_state_valid_cap)
  apply (frule set_mp[OF zobj_refs_subseteq_obj_refs])
  apply (frule (2) valid_cap_ep_at_ep_cap)
  apply (rule_tac x="cte_map (oref, cref)" in exI)
  apply (simp add: caps_of_state_Some_simp)
  apply (frule (3) pspace_relation_cte_wp_at)
  apply (drule cte_wp_at_norm')
  apply clarsimp
  apply (erule cte_wp_at_weakenE')
  apply (case_tac cap; clarsimp)
  done

lemma ex_nonz_cap_to_ntfn_at_cross:
  "\<lbrakk>ex_nonz_cap_to ptr s; ntfn_at ptr s; valid_objs s; pspace_relation (kheap s) (ksPSpace s');
    pspace_aligned' s'; pspace_distinct' s'\<rbrakk>
   \<Longrightarrow> ex_nonz_cap_to' ptr s'"
  apply (clarsimp simp: ex_nonz_cap_to_def cte_wp_at_caps_of_state ex_nonz_cap_to'_def)
  apply (rename_tac oref cref cap)
  apply (frule (1) caps_of_state_valid_cap)
  apply (frule set_mp[OF zobj_refs_subseteq_obj_refs])
  apply (frule (2) valid_cap_ntfn_at_ntfn_cap)
  apply (rule_tac x="cte_map (oref, cref)" in exI)
  apply (simp add: caps_of_state_Some_simp)
  apply (frule (3) pspace_relation_cte_wp_at)
  apply (drule cte_wp_at_norm')
  apply clarsimp
  apply (erule cte_wp_at_weakenE')
  apply (case_tac cap; clarsimp)
  done

lemma ex_nonz_cap_to_sc_at_cross:
  "\<lbrakk>ex_nonz_cap_to ptr s; sc_at ptr s; valid_objs s; pspace_relation (kheap s) (ksPSpace s');
    pspace_aligned' s'; pspace_distinct' s'\<rbrakk>
   \<Longrightarrow> ex_nonz_cap_to' ptr s'"
  apply (clarsimp simp: ex_nonz_cap_to_def cte_wp_at_caps_of_state ex_nonz_cap_to'_def)
  apply (rename_tac oref cref cap)
  apply (frule (1) caps_of_state_valid_cap)
  apply (frule set_mp[OF zobj_refs_subseteq_obj_refs])
  apply (frule (2) valid_cap_sc_at_sc_cap)
  apply (rule_tac x="cte_map (oref, cref)" in exI)
  apply (simp add: caps_of_state_Some_simp)
  apply (frule (3) pspace_relation_cte_wp_at)
  apply (drule cte_wp_at_norm')
  apply clarsimp
  apply (erule cte_wp_at_weakenE')
  apply (case_tac cap; clarsimp)
  done

lemma ex_nonz_cap_to_reply_at_cross:
  "\<lbrakk>ex_nonz_cap_to ptr s; reply_at ptr s; valid_objs s; pspace_relation (kheap s) (ksPSpace s');
    pspace_aligned' s'; pspace_distinct' s'\<rbrakk>
   \<Longrightarrow> ex_nonz_cap_to' ptr s'"
  apply (clarsimp simp: ex_nonz_cap_to_def cte_wp_at_caps_of_state ex_nonz_cap_to'_def)
  apply (rename_tac oref cref cap)
  apply (frule (1) caps_of_state_valid_cap)
  apply (frule set_mp[OF zobj_refs_subseteq_obj_refs])
  apply (frule (2) valid_cap_reply_at_reply_cap)
  apply (rule_tac x="cte_map (oref, cref)" in exI)
  apply (simp add: caps_of_state_Some_simp)
  apply (frule (3) pspace_relation_cte_wp_at)
  apply (drule cte_wp_at_norm')
  apply clarsimp
  apply (erule cte_wp_at_weakenE')
  apply (case_tac cap; clarsimp simp: is_reply_cap_def)
  done

lemma ex_nonz_cap_to_tcb_at_cross:
  "\<lbrakk>ex_nonz_cap_to ptr s; tcb_at ptr s; valid_objs s; pspace_relation (kheap s) (ksPSpace s');
    pspace_aligned' s'; pspace_distinct' s'\<rbrakk>
   \<Longrightarrow> ex_nonz_cap_to' ptr s'"
  apply (clarsimp simp: ex_nonz_cap_to_def cte_wp_at_caps_of_state ex_nonz_cap_to'_def)
  apply (rename_tac oref cref cap)
  apply (frule (1) caps_of_state_valid_cap)
  apply (frule set_mp[OF zobj_refs_subseteq_obj_refs])
  apply (frule (2) obj_ref_is_tcb)
  apply (rule_tac x="cte_map (oref, cref)" in exI)
  apply (simp add: caps_of_state_Some_simp)
  apply (frule (3) pspace_relation_cte_wp_at)
  apply (drule cte_wp_at_norm')
  apply clarsimp
  apply (erule cte_wp_at_weakenE')
  apply (case_tac cap; clarsimp simp: is_zombie_def)
  done

locale KHeap_R =
  assumes koType_objBitsKO:
    "\<lbrakk>koTypeOf k' = koTypeOf k; koTypeOf k = SchedContextT \<longrightarrow> objBitsKO k' = objBitsKO k\<rbrakk>
     \<Longrightarrow> objBitsKO k' = objBitsKO k"
  assumes pspace_dom_update:
    "\<And>ps ptr x v.
     \<lbrakk> ps ptr = Some x; a_type x = a_type v \<rbrakk> \<Longrightarrow> pspace_dom (ps(ptr \<mapsto> v)) = pspace_dom ps"
  assumes cte_wp_at_ctes_of:
    "\<And>P p s. cte_wp_at' P p s = (\<exists>cte. ctes_of s p = Some cte \<and> P cte)"
  assumes ctes_of_canonical:
    "\<And>s p cte. \<lbrakk> pspace_canonical' s; ctes_of s p = Some cte \<rbrakk> \<Longrightarrow> canonical_address p"
  assumes valid_updateCapDataI:
    "\<And>s c b x. s \<turnstile>' c \<Longrightarrow> s \<turnstile>' updateCapData b x c"
  assumes idle_is_global[intro!]:
    "\<And>s. ksIdleThread s \<in> global_refs' s"
  (* can't quantify over a generic 'a::storable in a locale (setObject), so assume it for the
     two objects we require for this theory and requalify the generic lemmas later *)
  assumes setEndpoint_pspace_in_kernel_mappings'[wp]:
    "\<And>p ko. setEndpoint p ko \<lbrace>pspace_in_kernel_mappings'\<rbrace>"
  assumes setNotification_pspace_in_kernel_mappings'[wp]:
    "\<And>p ko. setNotification p ko \<lbrace>pspace_in_kernel_mappings'\<rbrace>"
  assumes hyp_live_live: "\<And>ko. hyp_live ko \<Longrightarrow> live ko"
  assumes hyp_live'_live': "\<And>ko'. hyp_live' ko' \<Longrightarrow> live' ko'"
  assumes hyp_live'_hyp_live:
    "\<And>t ko' (s :: det_state) s'.
     \<lbrakk>ksPSpace s' t = Some ko'; hyp_live' ko'; tcbs_relation s s'; aobjs_relation s s'\<rbrakk>
     \<Longrightarrow> \<exists>ko. kheap s t = Some ko \<and> hyp_live ko"
  assumes ex_nonz_cap_to_arch_obj_cross:
    "\<And>ptr (s :: det_state) s' ako.
      \<lbrakk>ex_nonz_cap_to ptr s; pspace_relation (kheap s) (ksPSpace s');
       valid_objs s; pspace_aligned' s'; pspace_distinct' s';
       ksPSpace s' ptr = Some (KOArch ako); live' (KOArch ako)\<rbrakk>
      \<Longrightarrow> ex_nonz_cap_to' ptr s'"
  assumes pspace_relation_cte_wp_atI':
    "\<And>(s::det_state) s' cte x.
     \<lbrakk> pspace_relation (kheap s) (ksPSpace s'); cte_wp_at' ((=) cte) x s'; valid_objs s \<rbrakk>
     \<Longrightarrow> \<exists>c slot. cte_wp_at ((=) c) slot s \<and> cap_relation c (cteCap cte) \<and> x = cte_map slot"
  assumes pspace_relation_sc_at:
  "\<And>(s::det_state) s' scp.
   \<lbrakk>pspace_relation (kheap s) (ksPSpace s'); scs_of' s' scp \<noteq> None\<rbrakk> \<Longrightarrow> sc_at scp s"
  assumes pspace_aligned_cross:
  "\<And>(s::det_state) s'.
   \<lbrakk>pspace_aligned s; pspace_relation (kheap s) (ksPSpace s')\<rbrakk> \<Longrightarrow> pspace_aligned' s'"
  assumes pspace_distinct_cross:
  "\<And>(s::det_state) s'.
   \<lbrakk>pspace_distinct s; pspace_aligned s; pspace_relation (kheap s) (ksPSpace s')\<rbrakk>
   \<Longrightarrow> pspace_distinct' s'"
  assumes pspace_relation_pspace_bounded':
  "\<And>(s::det_state) s'.
   \<lbrakk>pspace_relation (kheap s) (ksPSpace s')\<rbrakk> \<Longrightarrow> pspace_bounded' s'"
  assumes idle_sc_is_global[intro!]:
  "\<And>s. idle_sc_ptr \<in> global_refs' s"

begin

lemma setObject_cte_wp_at':
  assumes x: "\<And>x n tcb s t. \<lbrakk> t \<in> fst (updateObject v (KOTCB tcb) ptr x n s); Q s;
                               lookupAround2 ptr (ksPSpace s) = (Some (x, KOTCB tcb), n) \<rbrakk>
                  \<Longrightarrow> \<exists>tcb'. t = (KOTCB tcb', s) \<and> (\<forall>(getF, setF) \<in> ran tcb_cte_cases. getF tcb' = getF tcb)"
  assumes y: "\<And>x n cte s. fst (updateObject v (KOCTE cte) ptr x n s) = {}"
  shows      "\<lbrace>cte_wp_at' P p and Q\<rbrace> setObject ptr v \<lbrace>\<lambda>rv. cte_wp_at' P p\<rbrace>"
  unfolding pred_conj_def
  by (rule setObject_cte_wp_at2'[OF x y], assumption+)

lemma ctes_of_from_cte_wp_at:
  assumes x: "\<And>P P' p. \<lbrace>\<lambda>s. P (cte_wp_at' P' p s) \<and> Q s\<rbrace> f \<lbrace>\<lambda>r s. P (cte_wp_at' P' p s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. P (ctes_of s) \<and> Q s\<rbrace> f \<lbrace>\<lambda>rv s. P (ctes_of s)\<rbrace>"
  apply (clarsimp simp: valid_def
                 elim!: rsubst[where P=P]
                   del: ext intro!: ext)
  apply (case_tac "ctes_of s x", simp_all)
   apply (drule_tac P1=Not and P'1="\<top>" and p1=x in use_valid [OF _ x],
           simp_all add: cte_wp_at_ctes_of)
  apply (drule_tac P1=id and P'1="(=) aa" and p1=x in use_valid [OF _ x],
          simp_all add: cte_wp_at_ctes_of)
  done

lemmas setObject_ctes_of = ctes_of_from_cte_wp_at [OF setObject_cte_wp_at2']

lemma ctes_of_eq_cte_wp_at':
  "cte_wp_at' ((=) cte) x s \<Longrightarrow> ctes_of s x = Some cte"
  by (simp add: cte_wp_at_ctes_of)

lemma ctes_of_cte_wp_atD:
  "ctes_of s p = Some cte \<Longrightarrow> cte_wp_at' ((=) cte) p s"
  by (simp add: cte_wp_at_ctes_of)

lemma ctes_of_setObject_cte:
  "\<lbrace>\<lambda>s. P ((ctes_of s) (p \<mapsto> cte))\<rbrace> setObject p (cte :: cte) \<lbrace>\<lambda>rv s. P (ctes_of s)\<rbrace>"
  apply (clarsimp simp: setObject_def split_def valid_def in_monad)
  apply (drule(1) updateObject_cte_is_tcb_or_cte[OF _ refl, rotated])
  apply (elim exE conjE disjE rsubst[where P=P])
   apply (clarsimp simp: lookupAround2_char1)
   apply (subst map_to_ctes_upd_tcb; assumption?)
    apply (fastforce simp: mask_def gen_objBits_simps field_simps ps_clear_def3)
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

lemma setObject_state_refs_of_eq:
  assumes x: "\<And>s s' obj obj' ptr' ptr''.
                  (obj', s') \<in> fst (updateObject val obj ptr ptr' ptr'' s)
                    \<Longrightarrow> refs_of' obj' = refs_of' obj"
  shows
  "\<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace>
     setObject ptr val
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  apply (clarsimp simp: setObject_def valid_def in_monad split_def
                        updateObject_default_def in_magnitude_check lookupAround2_char1
                 elim!: rsubst[where P=P]
                   del: ext intro!: ext
             split del: if_split cong: option.case_cong if_cong)
  apply (frule x, drule updateObject_size)
  apply (simp add: state_refs_of'_def ps_clear_upd
             cong: option.case_cong if_cong)
  done

lemma setObject_state_hyp_refs_of_eq:
  assumes x: "\<And>s s' obj obj' ptr' ptr''.
                  (obj', s') \<in> fst (updateObject val obj ptr ptr' ptr'' s)
                    \<Longrightarrow> hyp_refs_of' obj' = hyp_refs_of' obj"
  shows
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of' s)\<rbrace>
     setObject ptr val
   \<lbrace>\<lambda>rv s. P (state_hyp_refs_of' s)\<rbrace>"
  apply (clarsimp simp: setObject_def valid_def in_monad split_def
                        updateObject_default_def in_magnitude_check
                        lookupAround2_char1
                 elim!: rsubst[where P=P] del: ext intro!: ext
             split del: if_split cong: option.case_cong if_cong)
  apply (frule x, drule updateObject_size)
  apply (simp add: state_hyp_refs_of'_def ps_clear_upd
             cong: option.case_cong if_cong)
  done

lemma valid_refs'_def2:
  "valid_refs' R (ctes_of s) = (\<forall>cref. \<not>cte_wp_at' (\<lambda>c. R \<inter> capRange (cteCap c) \<noteq> {}) cref s)"
  by (auto simp: valid_refs'_def cte_wp_at_ctes_of ran_def)

lemma live'_tcb_cross:
  "\<lbrakk>live' (KOTCB tcb'); kheap s ptr = Some (TCB tcb); ksPSpace s' ptr = Some (KOTCB tcb');
    tcbs_relation s s'; aobjs_relation s s'; ready_queues_relation s s'; release_queue_relation s s';
    ready_queues_runnable s; in_correct_ready_q s; release_q_runnable s; valid_sched_pointers s';
    pspace_aligned' s'; pspace_distinct' s'\<rbrakk>
   \<Longrightarrow> live (TCB tcb)"
  apply (frule (1) tcbs_relation_tcb_relation_abs)
  apply (clarsimp simp: live'_def)
  apply (elim disjE)
          apply (clarsimp simp: tcb_relation_def live_def)
         apply (clarsimp simp: tcb_relation_def live_def)
        apply (clarsimp simp: tcb_relation_def live_def)
       apply (clarsimp simp: valid_sched_pointers_def)
       apply (fastforce intro!: sched_flag_set_live simp: opt_map_def split: option.splits)
      apply (clarsimp simp: valid_sched_pointers_def)
      apply (fastforce intro!: sched_flag_set_live simp: opt_map_def split: option.splits)
     apply (fastforce intro!: sched_flag_set_live[where s'=s'] simp: opt_pred_def opt_map_red)
    apply (fastforce intro!: sched_flag_set_live[where s'=s'] simp: opt_pred_def opt_map_red)
   apply (prop_tac "st_tcb_at' (\<lambda>st. st \<noteq> Inactive \<and> st \<noteq> IdleThreadState) ptr s'")
    apply (fastforce intro: aligned'_distinct'_obj_at'_propI simp: st_tcb_at'_def)
   apply (fastforce dest: st_tcb_at_coerce_abstract' simp: pred_tcb_at_def obj_at_def live_def)
  apply (frule hyp_live'_live')
  apply (fastforce dest!: hyp_live'_hyp_live simp: live_def)
  done

lemma if_live_then_nonz_cap_to_cross:
  "\<lbrakk>if_live_then_nonz_cap s; (s, s') \<in> state_relation; valid_objs s; ready_queues_runnable s;
    in_correct_ready_q s; release_q_runnable s; pspace_aligned s; pspace_distinct s;
    valid_replies' s'; valid_sched_pointers s'\<rbrakk>
   \<Longrightarrow> if_live_then_nonz_cap' s'"
  apply (frule state_relation_pspace_relation)
  apply (frule (1) pspace_aligned_cross)
  apply (frule (2) pspace_distinct_cross)
  apply (frule pspace_relation_pspace_bounded')
  apply (clarsimp simp: pspace_relation_heap_pspace_relation)
  apply (clarsimp simp: if_live_then_nonz_cap'_def live'_def ko_wp_at'_def)
  apply (rename_tac ko, case_tac ko; clarsimp)
       apply (frule eps_relation_ep_relation_conc; fastforce?)
       apply clarsimp
       apply (rule ex_nonz_cap_to_ep_at_cross; fastforce?)
        apply (erule (1) if_live_then_nonz_capD2)
        apply (clarsimp simp: ep_relation_def obj_at_def live_def)
       apply (clarsimp simp: obj_at_def is_ep_def)
      apply (frule ntfns_relation_ntfn_relation_conc; fastforce?)
      apply clarsimp
      apply (rule ex_nonz_cap_to_ntfn_at_cross; fastforce?)
       apply (erule (1) if_live_then_nonz_capD2)
       apply (clarsimp simp: ntfn_relation_def obj_at_def
                             live_def live_ntfn_def live'_def live_ntfn'_def
                      split: ntfn.splits)
      apply (clarsimp simp: obj_at_def is_ntfn_def)
     apply (rename_tac tcb')
     apply (frule tcbs_relation_tcb_relation_conc; fastforce?)
     apply clarsimp
     apply (rule ex_nonz_cap_to_tcb_at_cross; fastforce?)
      apply (erule (1) if_live_then_nonz_capD2)
      apply (rule_tac tcb'=tcb' in live'_tcb_cross, (fastforce simp: live'_def)+)[1]
     apply (clarsimp simp: obj_at_def is_tcb_def)
    apply (frule state_relation_pspace_relation)
    apply (clarsimp simp: pspace_relation_heap_pspace_relation)
    apply (frule heap_pspace_relation_tcbs_relation)
    apply (frule heap_pspace_relation_aobjs_relation)
    apply (frule hyp_live'_live')
    apply (frule (3) hyp_live'_hyp_live)
    apply clarsimp
    apply (frule hyp_live_live)
    apply (fastforce intro!: ex_nonz_cap_to_arch_obj_cross if_live_then_nonz_capD2
                       simp: live_def)
   apply (frule scs_relation_sc_relation_conc; (fastforce simp: live'_def)?)
   apply clarsimp
   apply (rule ex_nonz_cap_to_sc_at_cross; fastforce?)
    apply (erule (1) if_live_then_nonz_capD2)
    apply (rule live'_sc_cross; fastforce?)
    apply (fastforce intro: state_relation_sc_replies_relation)
   apply (force intro!: sc_at_pred_n_sc_at simp: sc_at_pred_n_def obj_at_def)
  apply (frule replies_relation_reply_relation_conc; fastforce?)
  apply clarsimp
  apply (rule ex_nonz_cap_to_reply_at_cross; fastforce?)
   apply (erule (1) if_live_then_nonz_capD2)
   apply (force intro: live'_reply_cross)
  apply (clarsimp simp: obj_at_def is_reply_def)
  done

lemma valid_globals_cte_wpD':
  "\<lbrakk> valid_global_refs' s; cte_wp_at' P p s; ptr \<in> global_refs' s \<rbrakk>
       \<Longrightarrow> \<exists>cte. P cte \<and> ptr \<notin> capRange (cteCap cte)"
  by (fastforce simp: valid_global_refs'_def valid_refs'_def  cte_wp_at_ctes_of)

end

declare mapM_x_return[simp]

context KHeap_R begin

lemma non_sc_same_typ_at'_objBits_always_the_same:
  assumes "typ_at' t ptr s"
          "koTypeOf ko = t"
          "t \<noteq> SchedContextT"
  shows "ko_wp_at' (\<lambda>old_ko. objBitsKO old_ko = objBitsKO ko) ptr s"
  using assms
  apply (clarsimp simp: typ_at'_def ko_wp_at'_def)
  apply (rule koType_objBitsKO)
  apply simp+
  done

lemma ex_cap_to'_after_update:
  "\<lbrakk> ex_nonz_cap_to' p s; ko_wp_at' (same_caps' val) p' s \<rbrakk>
     \<Longrightarrow> ex_nonz_cap_to' p (s\<lparr>ksPSpace := (ksPSpace s)(p' \<mapsto> val)\<rparr>)"
  unfolding ex_nonz_cap_to'_def cte_wp_at_ctes_of
  using ctes_of'_after_update
  by fastforce

lemmas non_sc_same_typ_at'_ko_wp_at'_set_ko'_iff =
  same_size_ko_wp_at'_set_ko'_iff[OF non_sc_same_typ_at'_objBits_always_the_same]

lemma aligned_distinct_ko_at'I:
  fixes s :: det_state
  assumes p: "pspace_relation (kheap s) (ksPSpace s')"
  assumes ps: "pspace_aligned s" "pspace_distinct s"
  shows "\<lbrakk>ksPSpace s' x = Some ko; ko = injectKO (v:: 'a :: pspace_storable)\<rbrakk>
      \<Longrightarrow> ko_at' v x s'"
  apply (rule aligned'_distinct'_ko_at'I[OF _ pspace_aligned_cross[OF ps(1) p]]; simp)
  using assms by (fastforce dest!: pspace_distinct_cross simp: pspace_relation_pspace_bounded'[OF p])+

end

end
