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

lemma obj_at_replyTCBs_of:
  "obj_at' (\<lambda>reply. replyTCB reply = tptr_opt) rptr s
   \<Longrightarrow> replyTCBs_of s rptr = tptr_opt"
  by (clarsimp simp: obj_at'_def projectKOs opt_map_def)

abbreviation
  "valid_replies'_alt s \<equiv>
     (\<forall>rptr rp. ko_at' rp rptr s \<and> ((\<exists>rp'. replyNext rp = Some (Next rp')) \<or> replyPrev rp \<noteq> None)
                \<longrightarrow> (\<exists>tptr. replyTCB rp = Some tptr
                            \<and> st_tcb_at' ((=) (BlockedOnReply (Some rptr))) tptr s))"

lemma valid_replies'_def2:
  "pspace_distinct' s \<Longrightarrow> pspace_aligned' s \<Longrightarrow>
   valid_replies' s = valid_replies'_alt s"
  unfolding valid_replies'_def
  apply (rule iffI; clarsimp simp: obj_at'_def projectKOs)
   apply (drule_tac x=rptr in spec, clarsimp simp: opt_map_def)
  apply (clarsimp simp: pspace_alignedD' pspace_distinctD' opt_map_def projectKOs
                  split: option.splits)
  done

primrec
  same_caps' :: "Structures_H.kernel_object \<Rightarrow> Structures_H.kernel_object \<Rightarrow> bool"
where
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

abbreviation (input)
  set_ko' :: "machine_word \<Rightarrow> kernel_object \<Rightarrow> kernel_state \<Rightarrow> kernel_state"
where
  "set_ko' ptr ko s \<equiv> s\<lparr>ksPSpace := (ksPSpace s)(ptr := Some ko)\<rparr>"

abbreviation (input)
  set_obj' :: "machine_word \<Rightarrow> ('a :: pspace_storable) \<Rightarrow> kernel_state \<Rightarrow> kernel_state"
where
  "set_obj' ptr obj s \<equiv> set_ko' ptr (injectKO obj) s"

context begin interpretation Arch . (*FIXME: arch_split*)

lemma ovalid_readObject[wp]:
  assumes R:
  "\<And>a n ko s obj::'a::pspace_storable.
  \<lbrakk> loadObject t t n ko s = Some a; projectKO_opt ko = Some obj \<rbrakk> \<Longrightarrow> a = obj"
  shows "ovalid (obj_at' P t) (readObject t) (\<lambda>(rv::'a::pspace_storable) _. P rv)"
  by (auto simp: obj_at'_def readObject_def split_def omonad_defs obind_def
                 lookupAround2_known1 projectKOs ovalid_def
           dest: R)

lemma obj_at_getObject:
  assumes R:
  "\<And>a n ko s obj::'a::pspace_storable.
  \<lbrakk> loadObject t t n ko s = Some a; projectKO_opt ko = Some obj \<rbrakk> \<Longrightarrow> a = obj"
  shows "\<lbrace>obj_at' P t\<rbrace> getObject t \<lbrace>\<lambda>(rv::'a::pspace_storable) s. P rv\<rbrace>"
  unfolding getObject_def
  apply wpsimp
  using R use_ovalid[OF ovalid_readObject] by blast

declare projectKO_inv [wp]

lemma loadObject_default_inv:
  "loadObject_default addr addr' next obj o\<lbrace> P \<rbrace>" by (simp add: ovalid_def)

lemma getObject_inv:
  "\<lbrace>P\<rbrace> getObject p \<lbrace>\<lambda>(rv :: 'a :: pspace_storable). P\<rbrace>"
  unfolding getObject_def by wpsimp

lemma getObject_tcb_inv [wp]: "\<lbrace>P\<rbrace> getObject l \<lbrace>\<lambda>(rv :: Structures_H.tcb). P\<rbrace>"
  by (rule getObject_inv)

lemma loadObject_default_Some [simp]:
  "\<lbrakk>projectKO_opt ko = Some (obj::'a);
                      is_aligned p (objBits obj);
                      case_option True (\<lambda>x. 2 ^ (objBits obj) \<le> x - p) n; q = p\<rbrakk>
       \<Longrightarrow> bound (loadObject_default p q n ko s:: ('a::pre_storable) option)"
  by (clarsimp simp: loadObject_default_def split_def projectKO_def obind_def
                        alignCheck_def alignError_def magnitudeCheck_def projectKOs
                        read_alignCheck_def read_alignError_def read_magnitudeCheck_def
                        unless_def gets_the_def is_aligned_mask omonad_defs
             split: option.splits) simp

lemmas loadObject_default_Some'[simp, intro!] = loadObject_default_Some[simplified]
lemmas loadObject_default_Some''[simp, intro!]
        = loadObject_default_Some[where p=p and s=s and n="snd (lookupAround2 p (ksPSpace s))" for p s,
                                 simplified]

lemma no_ofail_loadObject_default [simp]:
  "no_ofail (\<lambda>s. \<exists>obj. projectKO_opt ko = Some (obj::'a) \<and>
                      is_aligned p (objBits obj) \<and> q = p
                      \<and> case_option True (\<lambda>x. 2 ^ (objBits obj) \<le> x - p) n)
           (loadObject_default p q n ko :: ('a::pre_storable) kernel_r)"
  by (clarsimp simp: no_ofail_def)

method no_ofail_readObject_method =
  clarsimp simp: obj_at'_def readObject_def obind_def omonad_defs split_def projectKO_eq no_ofail_def,
  rule ps_clear_lookupAround2, assumption+, simp,
  blast intro: is_aligned_no_overflow,
  clarsimp simp: objBits_simps' project_inject split: option.splits

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

lemma objBitsKO_bounded[simp]:
  "objBitsKO ko < word_bits"
  using scBits_max
  by (simp add: objBits_simps' word_bits_def pageBits_def archObjSize_def pdeBits_def pteBits_def
           split: Structures_H.kernel_object.split arch_kernel_object.split)

lemma typ_at_to_obj_at':
  "typ_at' (koType (TYPE ('a :: pspace_storable))) p s
     = obj_at' (\<top> :: 'a \<Rightarrow> bool) p s"
  by (simp add: typ_at'_def obj_at'_real_def project_koType[symmetric])

lemmas typ_at_to_obj_at_arches
  = typ_at_to_obj_at'[where 'a=pte, simplified]
    typ_at_to_obj_at'[where 'a=pde, simplified]
    typ_at_to_obj_at'[where 'a=asidpool, simplified]
    typ_at_to_obj_at'[where 'a=user_data, simplified]
    typ_at_to_obj_at'[where 'a=user_data_device, simplified]

lemmas page_table_at_obj_at'
  = page_table_at'_def[unfolded typ_at_to_obj_at_arches]

method readObject_obj_at'_method
  =  clarsimp simp: readObject_def obind_def omonad_defs split_def loadObject_default_def
                    obj_at'_def projectKOs objBits_simps' scBits_pos_power2
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

lemma koType_objBitsKO:
  "\<lbrakk>koTypeOf k' = koTypeOf k; koTypeOf k = SchedContextT \<longrightarrow> objBitsKO k' = objBitsKO k\<rbrakk>
     \<Longrightarrow> objBitsKO k' = objBitsKO k"
  by (auto simp: objBitsKO_def archObjSize_def
          split: Structures_H.kernel_object.splits
                 ARM_H.arch_kernel_object.splits)

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
                       omonad_defs assert_opt_def fail_def return_def in_monad ARM_H.fromPPtr_def
                split: option.splits)+
  by (clarsimp simp: snd_bind split_def getObject_def gets_the_def exec_gets assert_opt_def
                     readObject_def obind_def omonad_defs return_def fail_def
              split: option.splits)

lemma loadObject_default_def2:
  "(gets_the $ loadObject_default ptr ptr' next obj) = do
     assert (ptr = ptr');
     val \<leftarrow> (case projectKO_opt obj of None \<Rightarrow> fail | Some k \<Rightarrow> return k);
     alignCheck ptr (objBits val);
     magnitudeCheck ptr next (objBits val);
     return val
   od"
  apply (rule ext)
  apply (rule monad_state_eqI)
    apply (force simp: loadObject_default_def gets_the_def exec_gets obind_def split_def
                       omonad_defs assert_opt_def fail_def return_def in_monad ARM_H.fromPPtr_def
                       read_magnitudeCheck_assert magnitudeCheck_assert projectKOs
                split: option.splits if_splits)+
  by (force simp: snd_bind split_def loadObject_default_def gets_the_def exec_gets assert_opt_def
                  obind_def omonad_defs return_def fail_def projectKO_def assert_def
                  read_magnitudeCheck_assert magnitudeCheck_assert
                  read_alignError_def is_aligned_mask  alignCheck_def read_alignCheck_def
           split: option.splits)

lemma pspace_relation_tcb_at:
  assumes p: "pspace_relation (kheap s) (ksPSpace s')"
  assumes t: "tcbs_of' s' t \<noteq> None"
  shows "tcb_at t s" using assms
  by (fastforce elim!: pspace_dom_relatedE obj_relation_cutsE
                 simp: other_obj_relation_def obj_at_def projectKOs is_tcb_def
                split: Structures_A.kernel_object.split_asm if_split_asm
                       ARM_A.arch_kernel_obj.split_asm kernel_object.splits)

lemma pspace_relation_sc_at:
  assumes p: "pspace_relation (kheap s) (ksPSpace s')"
  assumes t: "scs_of' s' scp \<noteq> None"
  shows "sc_at scp s" using assms
  by (fastforce elim!: pspace_dom_relatedE obj_relation_cutsE
                 simp: other_obj_relation_def is_sc_obj obj_at_def projectKOs
                split: Structures_A.kernel_object.split_asm if_split_asm
                       ARM_A.arch_kernel_obj.split_asm)

lemma corres_get_tcb [corres]:
  "corres (tcb_relation \<circ> the) (tcb_at t) (tcb_at' t) (gets (get_tcb t)) (getObject t)"
  apply (rule corres_no_failI)
   apply wp
  apply (simp add: get_object_def get_tcb_def gets_def gets_the_def getObject_def)
  apply (clarsimp simp: in_monad split_def bind_def gets_def get_def return_def
                        assert_def fail_def obj_at_def is_tcb
                 dest!: readObject_misc_ko_at')
  apply (clarsimp simp: state_relation_def pspace_relation_def obj_at'_def projectKOs)
  apply (drule bspec)
   apply blast
  apply (simp add: other_obj_relation_def)
  done

lemmas tcbSlot_defs = tcbCTableSlot_def tcbVTableSlot_def tcbIPCBufferSlot_def
                      tcbFaultHandlerSlot_def tcbTimeoutHandlerSlot_def

text \<open>updateObject_cte lemmas\<close>

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
               in_monad map_bits_to_bl cte_level_bits_def in_magnitude_check
               lookupAround2_char1
         split: kernel_object.splits)
  apply (subst(asm) in_magnitude_check3, simp+)
   apply (simp add: in_monad tcbSlot_defs
             split: if_split_asm)
  apply (simp add: in_monad tcbSlot_defs
            split: if_split_asm)
  done

declare plus_1_less[simp]

lemma setObject_sc_at'_n[wp]:
  "setObject ptr val \<lbrace>\<lambda>s. P (sc_at'_n n p s)\<rbrace>"
  by (fastforce simp : valid_def setObject_def ko_wp_at'_def in_monad split_def updateObject_size
                       ps_clear_upd lookupAround2_char1 updateObject_type)

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
  apply (rule hoare_seq_ext [OF _ hoare_gets_post])
  apply (clarsimp simp: valid_def in_monad obj_at'_def
                        projectKOs lookupAround2_char1
                        project_inject)
  apply (frule updateObject_size, drule R)
   apply (intro conjI impI, simp_all)
      apply fastforce+
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
  apply (clarsimp simp: ps_clear_upd lookupAround2_char1)
  done

\<comment>\<open>
  If the old and new versions of an object are the same size, then showing
  `obj_at'` for the updated state is the same as showing the predicate for
  the new value; we get to "reuse" the existing PSpace properties.
\<close>
lemma same_size_obj_at'_set_obj'_iff:
  fixes obj :: "'a :: pspace_storable"
  assumes "obj_at' (\<lambda>old_obj :: 'a. objBits old_obj = objBits obj) ptr s"
  shows "obj_at' P ptr (set_obj' ptr obj s) = P obj"
  apply (rule iffI)
   apply (prop_tac "ko_at' obj ptr (set_obj' ptr obj s)")
    apply (clarsimp simp: obj_at'_def projectKO_eq project_inject)
   apply (clarsimp simp: obj_at'_def)
  using assms
  apply (fastforce simp: obj_at'_def inj_def projectKO_eq project_inject objBits_def)
  done

lemma tcb_at'_obj_at'_set_obj'[unfolded injectKO_tcb]:
  assumes "P (tcb :: tcb)"
      and "tcb_at' ptr s"
  shows "obj_at' P ptr (set_obj' ptr tcb s)"
  using assms
  apply (clarsimp simp: objBits_def objBitsKO_def inj_def
                        same_size_obj_at'_set_obj'_iff[where 'a=tcb, simplified])
  done

\<comment>\<open>
  Keeps a generic @{term obj_at'} (rather than a specific @{term "obj_at' (\<lambda>_. True)"}) to match
  in more simp contexts.
\<close>
lemma tcb_obj_at'_set_obj'_iff:
  fixes tcb :: tcb
    and P Q :: "tcb \<Rightarrow> bool"
  shows "obj_at' P p s \<Longrightarrow> obj_at' Q p (set_obj' p tcb s) = Q tcb"
  apply (rule same_size_obj_at'_set_obj'_iff)
  apply (clarsimp simp: objBits_simps obj_at'_def)
  done

lemmas tcb_obj_at'_pred_tcb'_set_obj'_iff =
  tcb_obj_at'_set_obj'_iff[where Q="test o proj o tcb_to_itcb'" for test proj,
                                 simplified objBits_simps o_def, simplified,
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

\<comment>\<open>
  Moves the @{term ksPSpace_update} to the top.
\<close>
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
  assumes "p \<noteq> p'"
          "obj_at' Q p' s"
  shows "obj_at' P p (set_ko' p' ko s) = obj_at' P p s"
  using assms apply -
  apply (rule iffI; fastforce simp: obj_at'_def projectKO_eq project_inject ps_clear_upd)
  done

lemmas pred_tcb_at'_set_obj'_distinct =
  obj_at'_set_obj'_distinct[where P="test o proj o tcb_to_itcb'" for test proj,
                            simplified o_def, folded pred_tcb_at'_def]

lemmas pred_tcb_at'_set_obj'_iff =
  tcb_obj_at'_set_obj'_iff[where Q="test o proj o tcb_to_itcb'" for test proj,
                           simplified o_def injectKO_tcb, folded pred_tcb_at'_def]

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

lemmas non_sc_same_typ_at'_ko_wp_at'_set_ko'_iff =
  same_size_ko_wp_at'_set_ko'_iff[OF non_sc_same_typ_at'_objBits_always_the_same]

(* Worth adding other typ_at's? *)
lemma typ_at'_ksPSpace_exI:
  "pde_at' ptr s \<Longrightarrow> \<exists>pde. ksPSpace s ptr = Some (KOArch (KOPDE pde))"
  "pte_at' ptr s \<Longrightarrow> \<exists>pte. ksPSpace s ptr = Some (KOArch (KOPTE pte))"
  apply -
  apply (clarsimp simp: typ_at'_def ko_wp_at'_def,
         (case_tac ko; clarsimp),
         (rename_tac arch, case_tac arch; clarsimp)?)+
  done

\<comment>\<open>
  Used to show a stronger variant of @{thm obj_at_setObject2}
  for many concrete types.

  Needs to be a definition so we can easily refer to it within
  ML as a constant.
\<close>
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
  apply (rule hoare_seq_ext [OF _ hoare_gets_post])
  apply (clarsimp simp: valid_def in_monad)
  apply (frule updateObject_type)
  apply (erule_tac P="P'" in rsubst)
  apply (drule distinct_types)
  apply (clarsimp simp: lookupAround2_char1)
  apply (case_tac "obj_at' P t s")
   apply (clarsimp simp: obj_at'_def projectKOs)
   using project_koType ps_clear_upd
   apply fastforce
  apply (clarsimp simp: obj_at'_def projectKOs ps_clear_upd)
  apply (intro impI conjI iffI; metis project_koType)
  done

\<comment>\<open>
  We're using @{command ML_goal} here because we want to show
  `distinct_updateObject_types TYPE('a) TYPE('b)` for around
  50 different combinations of 'a and 'b. Doing that by hand would
  be painful, and not as clear for future readers as this comment
  plus this ML code.
\<close>
ML \<open>
local
  val ko_types = [
    @{typ notification},
    @{typ tcb},
    @{typ cte},
    @{typ sched_context},
    @{typ reply},
    @{typ endpoint},

    (*FIXME: arch_split*)
    @{typ asidpool},
    @{typ pte},
    @{typ pde}
  ];

  val skipped_pairs = [
    \<comment>\<open>
      This corresponds to the case where we're inserting a CTE into
      a TCB, which is the only case where the first two arguments
      to `updateObject` should have different types.

      See the comment on @{term updateObject} for more information.
    \<close>
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
  val distinct_updateObject_types_goals =
      Library.map_product pair ko_types ko_types
      |> Library.filter_out skips
      |> List.map mk_distinct_goal
end
\<close>

ML_goal distinct_updateObject_types: \<open>
  distinct_updateObject_types_goals
\<close>
  apply -
  \<comment>\<open>
    The produced goals match the following pattern:
  \<close>
  apply (all \<open>match conclusion in \<open>distinct_updateObject_types _ _\<close> \<Rightarrow> -\<close>)
  unfolding distinct_updateObject_types_def
  apply safe
  apply (clarsimp simp: distinct_updateObject_types_def
                        setObject_def updateObject_cte updateObject_default_def
                        typeError_def in_monad
                 split: if_splits kernel_object.splits)+
  done

lemmas setObject_distinct_types_preserves_obj_at'[wp] =
    distinct_updateObject_types[THEN setObject_distinct_types_preserves_obj_at'_pre]

(* FIXME RT: these overlap substantially with `setObject_distinct_types_preserves_obj_at'`,
   but fixing that requires having names for the relevant subset of lemmas. We can't do that with
   attributes, but we might be able to do it with a new command (`lemmas_matching`?) once `match`
   is factored.

   This doesn't really matter in this case because you're never going to refer to these lemmas by
   name. *)
lemmas set_distinct_types_preserves_obj_at'[wp] =
  setObject_distinct_types_preserves_obj_at'[folded setReply_def setNotification_def setCTE_def
                                                    setSchedContext_def setEndpoint_def]

lemmas set_distinct_types_preserves_pred_tcb_at'[wp] =
  set_distinct_types_preserves_obj_at'[TRY[where P="test o proj o tcb_to_itcb'" for test proj,
                                           simplified o_def, folded pred_tcb_at'_def, rule_format]]
  setObject_distinct_types_preserves_obj_at'[TRY[where P="test o proj o tcb_to_itcb'" for test proj,
                                             simplified o_def, folded pred_tcb_at'_def,
                                             rule_format]]

end

lemma setObject_typ_at_inv:
  "\<lbrace>typ_at' T p'\<rbrace> setObject p v \<lbrace>\<lambda>r. typ_at' T p'\<rbrace>"
  by (clarsimp simp: setObject_def split_def valid_def typ_at'_def ko_wp_at'_def in_monad
                        lookupAround2_char1 ps_clear_upd updateObject_size updateObject_type)

lemma setObject_typ_at_not:
  "\<lbrace>\<lambda>s. \<not> (typ_at' T p' s)\<rbrace> setObject p v \<lbrace>\<lambda>r s. \<not> (typ_at' T p' s)\<rbrace>"
  apply (clarsimp simp: setObject_def valid_def in_monad split_def)
  apply (erule notE)
  by (clarsimp simp: typ_at'_def ko_wp_at'_def lookupAround2_char1
                     updateObject_size updateObject_type
              split: if_split_asm
              elim!: ps_clear_domE)
      fastforce+

lemma setObject_typ_at'[wp]:
  "\<lbrace>\<lambda>s. P (typ_at' T p' s)\<rbrace> setObject p v \<lbrace>\<lambda>r s. P (typ_at' T p' s)\<rbrace>"
  by (blast intro: P_bool_lift setObject_typ_at_inv setObject_typ_at_not)

global_interpretation setObject: typ_at_all_props' "setObject p v"
  by typ_at_props'

context begin interpretation Arch . (*FIXME: arch_split*)

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
   apply (erule exEI [where 'a=word32])
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

lemma setObject_cte_wp_at':
  assumes x: "\<And>x n tcb s t. \<lbrakk> t \<in> fst (updateObject v (KOTCB tcb) ptr x n s); Q s;
                               lookupAround2 ptr (ksPSpace s) = (Some (x, KOTCB tcb), n) \<rbrakk>
                  \<Longrightarrow> \<exists>tcb'. t = (KOTCB tcb', s) \<and> (\<forall>(getF, setF) \<in> ran tcb_cte_cases. getF tcb' = getF tcb)"
  assumes y: "\<And>x n cte s. fst (updateObject v (KOCTE cte) ptr x n s) = {}"
  shows      "\<lbrace>cte_wp_at' P p and Q\<rbrace> setObject ptr v \<lbrace>\<lambda>rv. cte_wp_at' P p\<rbrace>"
  unfolding pred_conj_def
  by (rule setObject_cte_wp_at2'[OF x y], assumption+)

lemma obj_at_setObject3:
  fixes Q::"'a::pspace_storable \<Rightarrow> bool"
  fixes P::"'a::pspace_storable \<Rightarrow> bool"
  assumes R: "\<And>ko s y n. (updateObject v ko p y n s)
                   = (updateObject_default v ko p y n s)"
  assumes P: "\<And>(v::'a::pspace_storable). (1 :: word32) < 2 ^ (objBits v)"
  shows "\<lbrace>(\<lambda>s. P v)\<rbrace> setObject p v \<lbrace>\<lambda>rv. obj_at' P p\<rbrace>"
  apply (clarsimp simp add: valid_def in_monad obj_at'_def
                            setObject_def split_def projectKOs
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
   apply (rule hoare_weaken_pre)
    apply (rule obj_at_setObject3)
     apply simp
    apply (simp add: objBits_simps')
   apply simp
  apply (simp add: setObject_def split_def)
  apply (clarsimp simp: valid_def obj_at'_def split_def in_monad
                        updateObject_default_def projectKOs
                        ps_clear_upd)
  done

method setObject_easy_cases =
  clarsimp simp: setObject_def in_monad split_def valid_def lookupAround2_char1,
  erule rsubst[where P=P'], rule ext,
  clarsimp simp: updateObject_cte updateObject_default_def in_monad
                 typeError_def opt_map_def projectKO_opts_defs projectKO_eq2
          split: if_split_asm
                 Structures_H.kernel_object.split_asm

lemma setObject_endpoint_replies_of'[wp]:
  "setObject c (endpoint::endpoint) \<lbrace>\<lambda>s. P' (replies_of' s)\<rbrace>"
  by setObject_easy_cases

lemma setObject_notification_replies_of'[wp]:
  "setObject c (notification::notification) \<lbrace>\<lambda>s. P' (replies_of' s)\<rbrace>"
  by setObject_easy_cases

lemma setObject_tcb_replies_of'[wp]:
  "setObject c (tcb::tcb) \<lbrace>\<lambda>s. P' (replies_of' s)\<rbrace>"
  by setObject_easy_cases

lemma setObject_sched_context_replies_of'[wp]:
  "setObject c (sched_context::sched_context) \<lbrace>\<lambda>s. P' (replies_of' s)\<rbrace>"
  by setObject_easy_cases

lemma setObject_cte_replies_of'[wp]:
  "setObject c (cte::cte) \<lbrace>\<lambda>s. P' (replies_of' s)\<rbrace>"
  by setObject_easy_cases

\<comment>\<open>
  Warning: this may not be a weakest precondition. `setObject c`
  asserts that there's already a correctly-typed object at `c`,
  so a weaker valid precondition might be @{term
    "\<lambda>s. replies_of' s c \<noteq> None \<longrightarrow>  P' ((replies_of' s)(c \<mapsto> reply))"
  }
\<close>
lemma setObject_reply_replies_of'[wp]:
  "\<lbrace>\<lambda>s. P' ((replies_of' s)(c \<mapsto> reply))\<rbrace>
  setObject c (reply::reply)
  \<lbrace>\<lambda>_ s. P' (replies_of' s)\<rbrace>"
  by setObject_easy_cases

\<comment>\<open>
  Warning: this may not be a weakest precondition. `setObject c`
  asserts that there's already a correctly-typed object at `c`,
  so a weaker valid precondition might be @{term
    "\<lambda>s. scs_of' s c \<noteq> None \<longrightarrow>  P' ((scs_of' s)(c \<mapsto> sched_context))"
  }
\<close>
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

lemmas setReply_replies_of' = setObject_reply_replies_of'[folded setReply_def]

crunches setNotification, setEndpoint, setSchedContext, setCTE
  for replies_of'[wp]: "\<lambda>s. P (replies_of' s)"

lemmas setSchedContext_scs_of_of' =
  setObject_sched_context_scs_of'[folded setSchedContext_def]

crunches setNotification, setEndpoint, setCTE, setReply
  for scs_of'[wp]: "\<lambda>s. P (scs_of' s)"

lemma getObject_obj_at':
  assumes x: "\<And>q n ko. loadObject p q n ko =
                (loadObject_default p q n ko :: ('a :: pspace_storable) kernel_r)"
  assumes P: "\<And>(v::'a::pspace_storable). (1 :: word32) < 2 ^ (objBits v)"
  shows      "\<lbrace> \<top> \<rbrace> getObject p \<lbrace>\<lambda>r::'a::pspace_storable. obj_at' ((=) r) p\<rbrace>"
  by (clarsimp simp: valid_def getObject_def in_monad omonad_defs readObject_def
                     loadObject_default_def obj_at'_def projectKOs
                     split_def in_magnitude_check lookupAround2_char1
                     x P project_inject objBits_def[symmetric]
              split: option.split_asm if_split_asm)

lemma getObject_valid_obj:
  assumes x: "\<And>p q n ko. loadObject p q n ko =
                (loadObject_default p q n ko :: ('a :: pspace_storable) kernel_r)"
  assumes P: "\<And>(v::'a::pspace_storable). (1 :: word32) < 2 ^ (objBits v)"
  shows "\<lbrace> valid_objs' \<rbrace> getObject p \<lbrace>\<lambda>rv::'a::pspace_storable. valid_obj' (injectKO rv) \<rbrace>"
  apply (rule hoare_chain)
    apply (rule hoare_vcg_conj_lift)
     apply (rule getObject_obj_at' [OF x P])
    apply (rule getObject_inv)
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
  by (wpsimp simp: getObject_def)

lemma getObject_ko_at:
  assumes x: "\<And>q n ko. loadObject p q n ko =
                (loadObject_default p q n ko :: ('a :: pspace_storable) kernel_r)"
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

context
begin

private method getObject_valid_obj =
  rule hoare_chain,
  rule getObject_valid_obj; clarsimp simp: objBits_simps' valid_obj'_def scBits_pos_power2

lemma get_ep'_valid_ep[wp]:
  "\<lbrace> valid_objs' \<rbrace> getEndpoint ep \<lbrace> valid_ep' \<rbrace>"
  unfolding getEndpoint_def by getObject_valid_obj

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
  by (rule getObject_ko_at; simp add: objBits_simps')

lemma get_ntfn_ko':
  "\<lbrace>\<top>\<rbrace> getNotification ntfn \<lbrace>\<lambda>rv. ko_at' rv ntfn\<rbrace>"
  unfolding getNotification_def
  by (rule getObject_ko_at; simp add: objBits_simps')

lemma get_sc_ko':
  "\<lbrace>\<top>\<rbrace> getSchedContext sc_ptr \<lbrace>\<lambda>sc. ko_at' sc sc_ptr\<rbrace>"
  unfolding getSchedContext_def
  by (rule getObject_ko_at; simp add: objBits_simps' scBits_pos_power2)

lemma get_reply_ko':
  "\<lbrace>\<top>\<rbrace> getReply reply_ptr \<lbrace>\<lambda>reply. ko_at' reply reply_ptr\<rbrace>"
  unfolding getReply_def
  by (rule getObject_ko_at; simp add: objBits_simps')

context
begin

private method unfold_setObject_inmonad =
  (clarsimp simp: setObject_def split_def valid_def in_monad projectKOs updateObject_size
                  objBits_def[symmetric] lookupAround2_char1 ps_clear_upd
            split: if_split_asm),
    (fastforce dest: bspec[OF _ domI])+

lemma setObject_distinct[wp]:
  "setObject p val \<lbrace>pspace_distinct'\<rbrace>"
  unfolding pspace_distinct'_def by (unfold_setObject_inmonad)

lemma setObject_aligned[wp]:
  "setObject p val \<lbrace>pspace_aligned'\<rbrace>"
  unfolding pspace_aligned'_def by (unfold_setObject_inmonad)

end

end

context begin interpretation Arch . (*FIXME: arch_split*)

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

lemma ctes_of'_after_update:
  "ko_wp_at' (same_caps' val) p s \<Longrightarrow> ctes_of (s\<lparr>ksPSpace := ksPSpace s(p \<mapsto> val)\<rparr>) x = ctes_of s x"
  apply (clarsimp simp only: ko_wp_at'_def map_to_ctes_def Let_def)
  apply (rule if_cong)
    apply (cases val; fastforce split: if_splits)
   apply (cases val; fastforce split: if_splits)
  apply (rule if_cong)
    apply (cases val; clarsimp; fastforce)
   apply (cases val; clarsimp simp: tcb_cte_cases_def)
  apply simp
  done

lemma ex_cap_to'_after_update:
  "\<lbrakk> ex_nonz_cap_to' p s; ko_wp_at' (same_caps' val) p' s \<rbrakk>
     \<Longrightarrow> ex_nonz_cap_to' p (s\<lparr>ksPSpace := ksPSpace s(p' \<mapsto> val)\<rparr>)"
  unfolding ex_nonz_cap_to'_def cte_wp_at_ctes_of
  using ctes_of'_after_update
  by fastforce

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

lemma no_fail_getMiscObject [wp]:
  "no_fail (ep_at' ptr) (getEndpoint ptr)"
  "no_fail (ntfn_at' ptr) (getNotification ptr)"
  "no_fail (reply_at' ptr) (getReply ptr)"
  "no_fail (sc_at' ptr) (getSchedContext ptr)"
  by (wpsimp simp: getEndpoint_def getNotification_def getReply_def getSchedContext_def)+

lemma get_ep_corres [corres]:
  "corres ep_relation (ep_at ptr) (ep_at' ptr)
     (get_endpoint ptr) (getEndpoint ptr)"
  apply (rule corres_no_failI)
   apply wp
  apply (simp add: get_simple_ko_def getEndpoint_def get_object_def gets_the_def
                   getObject_def bind_assoc ep_at_def2)
  apply (clarsimp simp: in_monad split_def bind_def gets_def get_def return_def
                 dest!: readObject_misc_ko_at')
  apply (clarsimp simp: assert_def fail_def obj_at_def return_def is_ep partial_inv_def)
  apply (rename_tac ep' ep)
  apply (clarsimp simp: state_relation_def pspace_relation_def obj_at'_def projectKOs)
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

(* FIXME RT: can we drop the obj_at' size equality condition? *)
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
                        objBits_def[symmetric] projectKOs
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

lemma replyNexts_of_non_reply_update:
  "\<And>s'. \<lbrakk>typ_at' (koTypeOf ko) ptr s';
   koTypeOf ko \<noteq> ReplyT \<rbrakk>
     \<Longrightarrow> replyNexts_of (s'\<lparr>ksPSpace := ksPSpace s'(ptr \<mapsto> ko)\<rparr>) = replyNexts_of s'"
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
     \<Longrightarrow> replyNexts_of (s'\<lparr>ksPSpace := ksPSpace s'(ptr \<mapsto> injectKO ob')\<rparr>) = replyNexts_of s'"
  apply (cases "injectKO ob'"; clarsimp simp: typ_at'_def ko_wp_at'_def)
  by (cases ko; fastforce simp add: replyNext_same_def project_inject projectKO_opts_defs opt_map_def)

lemma replyPrevs_of_non_reply_update:
  "\<And>s'. \<lbrakk>typ_at' (koTypeOf ko) ptr s';
   koTypeOf ko \<noteq> ReplyT \<rbrakk>
     \<Longrightarrow> replyPrevs_of (s'\<lparr>ksPSpace := ksPSpace s'(ptr \<mapsto> ko)\<rparr>) = replyPrevs_of s'"
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
     \<Longrightarrow> replyPrevs_of (s'\<lparr>ksPSpace := ksPSpace s'(ptr \<mapsto> injectKO ob')\<rparr>) = replyPrevs_of s'"
  apply (cases "injectKO ob'"; clarsimp simp: typ_at'_def ko_wp_at'_def)
  by (cases ko; fastforce simp add: replyPrev_same_def project_inject projectKO_opts_defs opt_map_def)

lemma set_other_obj_corres:
  fixes ob' :: "'a :: pspace_storable"
  assumes x: "updateObject ob' = updateObject_default ob'"
  assumes z: "\<And>s. obj_at' P ptr s
               \<Longrightarrow> map_to_ctes ((ksPSpace s) (ptr \<mapsto> injectKO ob')) = map_to_ctes (ksPSpace s)"
  assumes t: "is_other_obj_relation_type (a_type ob)"
  assumes b: "\<And>ko. P ko \<Longrightarrow> objBits ko = objBits ob'"
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
                        projectKOs obj_at_def in_magnitude_check[OF _ P]
                        updateObject_default_def)
  apply (rename_tac ko)
  apply (clarsimp simp add: state_relation_def z)
  apply (clarsimp simp add: caps_of_state_after_update cte_wp_at_after_update
                            swp_def fun_upd_def obj_at_def)
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
   apply (insert t)
   apply ((erule disjE
         | clarsimp simp: is_other_obj_relation_type is_other_obj_relation_type_def a_type_def)+)[1]
  (* sc_replies_relation *)
  apply (simp add: sc_replies_relation_def)
  apply (clarsimp simp: sc_replies_of_scs_def map_project_def scs_of_kh_def)
  apply (drule_tac x=p in spec)
  apply (rule conjI; clarsimp simp: sc_of_def split: Structures_A.kernel_object.split_asm if_split_asm)
   apply(clarsimp simp: a_type_def is_other_obj_relation_type_def)
  apply (rename_tac sc n)
  apply (prop_tac "typ_at' (koTypeOf (injectKO ob')) ptr b")
   apply (clarsimp simp: typ_at'_def ko_wp_at'_def obj_at'_def projectKO_opts_defs
                         is_other_obj_relation_type_def a_type_def other_obj_relation_def
                  split: Structures_A.kernel_object.split_asm if_split_asm
                         arch_kernel_obj.split_asm kernel_object.split_asm arch_kernel_object.split_asm)
  apply (drule replyPrevs_of_non_reply_update[simplified])
   apply (clarsimp simp: other_obj_relation_def; cases ob; cases "injectKO ob'";
          simp split: arch_kernel_obj.split_asm)
  apply (clarsimp simp add: opt_map_def sc_of_def)
  done

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

lemma reply_at'_cross:
  assumes p: "pspace_relation (kheap s) (ksPSpace s')"
  assumes t: "reply_at' ptr s'"
  shows "reply_at ptr s" using assms
  apply (clarsimp simp: obj_at'_def projectKOs)
  apply (erule (1) pspace_dom_relatedE)
  by (clarsimp simp: obj_relation_cuts_def2 obj_at_def is_reply cte_relation_def
                     other_obj_relation_def pte_relation_def pde_relation_def
              split: Structures_A.kernel_object.split_asm if_split_asm
                     ARM_A.arch_kernel_obj.split_asm)

lemma set_reply_corres: (* for reply update that doesn't touch the reply stack *)
  "reply_relation ae ae' \<Longrightarrow>
  corres dc \<top>
            (obj_at' (\<lambda>ko. replyPrev_same ae' ko) ptr)
            (set_reply ptr ae) (setReply ptr ae')"
  proof -
  have x: "updateObject ae' = updateObject_default ae'" by clarsimp
  have z: "\<And>s. reply_at' ptr s
               \<Longrightarrow> map_to_ctes ((ksPSpace s) (ptr \<mapsto> injectKO ae')) = map_to_ctes (ksPSpace s)"
    by (clarsimp simp: obj_at_simps)
  have b: "\<And>ko. (\<lambda>_ :: reply. True) ko \<Longrightarrow> objBits ko = objBits ae'"
    by (clarsimp simp: obj_at_simps)
  have P: "\<And>(v::'a::pspace_storable). (1 :: word32) < 2 ^ (objBits v)"
    by (clarsimp simp: obj_at_simps objBits_defs pteBits_def pdeBits_def scBits_pos_power2
                split: kernel_object.splits arch_kernel_object.splits)
  assume r: "reply_relation ae ae'"
  show ?thesis
    apply (simp add: set_simple_ko_def setReply_def is_reply_def[symmetric])
    supply image_cong_simp [cong del]
    apply (insert r)
    apply (rule corres_no_failI)
     apply (rule no_fail_pre)
      apply wp
      apply (rule x)
     apply (clarsimp simp: obj_at'_weakenE[OF _ b])
    apply (unfold set_object_def setObject_def)
    apply (clarsimp simp: in_monad split_def bind_def gets_def get_def Bex_def
                          put_def return_def modify_def get_object_def x
                          projectKOs obj_at_def obj_at'_def is_reply
                          updateObject_default_def in_magnitude_check[OF _ P])
    apply (prop_tac "reply_at ptr a")
     apply (clarsimp simp: obj_at'_def projectKOs dest!: state_relation_pspace_relation reply_at'_cross[where ptr=ptr])
    apply (clarsimp simp: obj_at_def is_reply)
    apply (rename_tac reply)
    apply (prop_tac "obj_at (same_caps (kernel_object.Reply ae)) ptr a")
     apply (clarsimp simp: obj_at_def is_reply)
    apply (clarsimp simp: state_relation_def
                          z[simplified obj_at'_def is_reply projectKO_eq projectKO_opts_defs, simplified])
    apply (clarsimp simp add: caps_of_state_after_update cte_wp_at_after_update
                              swp_def fun_upd_def obj_at_def)
    apply (subst conj_assoc[symmetric])
    apply (rule conjI[rotated])
     apply (clarsimp simp add: ghost_relation_def)
     apply (erule_tac x=ptr in allE)+
     apply (clarsimp simp: obj_at_def a_type_def
                     split: Structures_A.kernel_object.splits if_split_asm)
    apply (fold fun_upd_def)
    apply (simp only: pspace_relation_def simp_thms
                      pspace_dom_update[where x="kernel_object.Reply _"
                                          and v="kernel_object.Reply _",
                                        simplified a_type_def, simplified])
    apply (simp only: dom_fun_upd2 simp_thms)
    apply (elim conjE)
    apply (frule bspec, erule domI)
    apply (rule conjI)
     apply (rule ballI, drule(1) bspec)
     apply (drule domD)
     apply (clarsimp simp: project_inject split: if_split_asm kernel_object.split_asm)
     apply (rename_tac bb aa ba)
     apply (drule_tac x="(aa, ba)" in bspec, simp)
     apply clarsimp
     apply (frule_tac ko'="kernel_object.Reply reply" and x'=ptr in obj_relation_cut_same_type)
        apply simp+
     apply clarsimp
      (* sc_replies_relation *)
    apply (simp add: sc_replies_relation_def)
    apply (clarsimp simp: sc_replies_of_scs_def map_project_def scs_of_kh_def)
    apply (drule_tac x=p in spec)
    apply (rule conjI; clarsimp simp: sc_of_def split: Structures_A.kernel_object.split_asm if_split_asm)
    by (subst replyPrevs_of_replyPrev_same_update[simplified, where ob'=ae', simplified];
        simp add: typ_at'_def ko_wp_at'_def obj_at'_def project_inject opt_map_def sc_of_def)
  qed

lemma setReply_not_queued_corres: (* for reply updates on replies not in fst ` replies_with_sc *)
  "reply_relation r1 r2 \<Longrightarrow>
  corres dc (\<lambda>s. ptr \<notin> fst ` replies_with_sc s) (reply_at' ptr)
            (set_reply ptr r1) (setReply ptr r2)"
  proof -
  have x: "updateObject r2 = updateObject_default r2" by clarsimp
  have z: "\<And>s. reply_at' ptr s
               \<Longrightarrow> map_to_ctes ((ksPSpace s) (ptr \<mapsto> injectKO r2)) = map_to_ctes (ksPSpace s)"
    by (clarsimp simp: obj_at_simps)
  have b: "\<And>ko. (\<lambda>_ :: reply. True) ko \<Longrightarrow> objBits ko = objBits r2"
    by (clarsimp simp: obj_at_simps)
  have P: "\<And>(v::'a::pspace_storable). (1 :: word32) < 2 ^ (objBits v)"
    by (clarsimp simp: obj_at_simps objBits_defs pteBits_def pdeBits_def scBits_pos_power2
                split: kernel_object.splits arch_kernel_object.splits)
  assume r: "reply_relation r1 r2"
  show ?thesis
    apply (simp add: set_simple_ko_def setReply_def is_reply_def[symmetric])
    supply image_cong_simp [cong del]
    apply (insert r)
    apply (rule corres_no_failI)
     apply (rule no_fail_pre)
      apply wp
      apply (rule x)
     apply (clarsimp simp: obj_at'_weakenE[OF _ b])
    apply (unfold set_object_def setObject_def)
    apply (clarsimp simp: in_monad split_def bind_def gets_def get_def Bex_def
                          put_def return_def modify_def get_object_def x
                          projectKOs obj_at_def obj_at'_def is_reply
                          updateObject_default_def in_magnitude_check[OF _ P])
    apply (prop_tac "reply_at ptr a")
     apply (clarsimp simp: obj_at'_def projectKOs dest!: state_relation_pspace_relation reply_at'_cross[where ptr=ptr])
    apply (clarsimp simp: obj_at_def is_reply)
    apply (rename_tac reply)
    apply (prop_tac "obj_at (same_caps (kernel_object.Reply _)) ptr a")
     apply (clarsimp simp: obj_at_def is_reply)
    apply (clarsimp simp: state_relation_def
                          z[simplified obj_at'_def is_reply projectKO_eq projectKO_opts_defs, simplified])
    apply (clarsimp simp add: caps_of_state_after_update cte_wp_at_after_update
                              swp_def fun_upd_def obj_at_def)
    apply (subst conj_assoc[symmetric])
    apply (rule conjI[rotated])
     apply (clarsimp simp add: ghost_relation_def)
     apply (erule_tac x=ptr in allE)+
     apply (clarsimp simp: obj_at_def a_type_def
                     split: Structures_A.kernel_object.splits if_split_asm)
    apply (fold fun_upd_def)
    apply (simp only: pspace_relation_def simp_thms
                      pspace_dom_update[where x="kernel_object.Reply _"
                                          and v="kernel_object.Reply _",
                                        simplified a_type_def, simplified])
    apply (simp only: dom_fun_upd2 simp_thms)
    apply (elim conjE)
    apply (frule bspec, erule domI)
    apply (rule conjI)
     apply (rule ballI, drule(1) bspec)
     apply (drule domD)
     apply (clarsimp simp: project_inject split: if_split_asm kernel_object.split_asm)
     apply (rename_tac bb aa ba)
     apply (drule_tac x="(aa, ba)" in bspec, simp)
     apply clarsimp
     apply (frule_tac ko'="kernel_object.Reply reply" and x'=ptr in obj_relation_cut_same_type)
        apply simp+
     apply clarsimp
      (* sc_replies_relation *)
    apply (simp add: sc_replies_relation_def)
    apply (clarsimp simp: sc_replies_of_scs_def map_project_def scs_of_kh_def)
    apply (rule conjI; clarsimp simp: sc_of_def split: Structures_A.kernel_object.split_asm if_split_asm)
    apply (drule_tac x=p in spec)
   apply (subgoal_tac "((scs_of' b)(ptr := sc_of' (KOReply r2)) |> scReply) p = scReplies_of b p")
     apply simp
    apply (subgoal_tac "heap_ls (replyPrevs_of b) (scReplies_of b p) (sc_replies z)")
     apply (erule heap_path_heap_upd_not_in)
     apply (clarsimp simp: sc_at_pred_n_def obj_at_def replies_with_sc_def image_def)
     apply (drule_tac x=p in spec)
     apply (simp add: typ_at'_def ko_wp_at'_def obj_at'_def project_inject opt_map_def sc_of_def)
    apply (simp add: typ_at'_def ko_wp_at'_def obj_at'_def project_inject opt_map_def sc_of_def)
   apply (simp add: typ_at'_def ko_wp_at'_def obj_at'_def project_inject opt_map_def sc_of_def)
  done
  qed

lemma sc_at'_cross:
  assumes p: "pspace_relation (kheap s) (ksPSpace s')"
  assumes t: "sc_at' ptr s'"
  shows "sc_at ptr s" using assms
  apply (clarsimp simp: obj_at'_def projectKOs)
  apply (erule (1) pspace_dom_relatedE)
  by (clarsimp simp: obj_relation_cuts_def2 obj_at_def is_sc_obj cte_relation_def
                     other_obj_relation_def pte_relation_def pde_relation_def
              split: Structures_A.kernel_object.split_asm if_split_asm
                     ARM_A.arch_kernel_obj.split_asm)

lemma sc_obj_at'_cross:
  assumes p: "pspace_relation (kheap s) (ksPSpace s')"
  assumes t: "obj_at' (\<lambda>k::sched_context. objBits k = minSchedContextBits + n) ptr s'"
  shows "sc_obj_at n ptr s" using assms
  apply (clarsimp simp: obj_at'_def projectKOs)
  apply (erule (1) pspace_dom_relatedE)
  by (clarsimp simp: obj_relation_cuts_def2 obj_at_def is_sc_obj cte_relation_def
                     objBits_simps scBits_simps
                     other_obj_relation_def pte_relation_def pde_relation_def sc_relation_def
              split: Structures_A.kernel_object.split_asm if_split_asm
                     ARM_A.arch_kernel_obj.split_asm)

lemma setSchedContext_corres:
  assumes R': "sc_relation sc n sc'"
  assumes s: " n + minSchedContextBits = objBits sc'"
  shows "corres dc \<top>
         (obj_at' (\<lambda>k::sched_context. objBits k = objBits sc') ptr and (\<lambda>s'. heap_ls (replyPrevs_of s') (scReply sc') (sc_replies sc)))
            (set_object ptr (kernel_object.SchedContext sc n))
            (setSchedContext ptr sc')"
  proof -
  have z: "\<And>s. sc_at' ptr s
               \<Longrightarrow> map_to_ctes ((ksPSpace s) (ptr \<mapsto> injectKO sc')) = map_to_ctes (ksPSpace s)"
    by (clarsimp simp: obj_at_simps)
  have P: "\<And>(v::'a::pspace_storable). (1 :: word32) < 2 ^ (objBits v)"
    by (clarsimp simp: obj_at_simps objBits_defs pteBits_def pdeBits_def scBits_pos_power2
                split: kernel_object.splits arch_kernel_object.splits)
  show ?thesis
    apply (insert P R' s)
    apply (clarsimp simp: setSchedContext_def)
    apply (rule corres_no_failI)
     apply (rule no_fail_pre)
      apply wp
      apply clarsimp
     apply clarsimp
    apply clarsimp
    apply (rename_tac s s' rv; prop_tac "sc_obj_at n ptr s")
     apply (fastforce intro!: sc_obj_at'_cross dest: state_relation_pspace_relation simp: obj_at'_def)
    apply (clarsimp simp: obj_at_def is_sc_obj_def obj_at'_def projectKO_eq projectKO_opts_defs)
    apply (unfold update_sched_context_def set_object_def setObject_def)
    apply (clarsimp simp: in_monad split_def bind_def gets_def get_def Bex_def
                          put_def return_def modify_def get_object_def2
                          projectKOs obj_at_def a_type_def
                          updateObject_default_def in_magnitude_check[OF _ P]
                   split: Structures_A.kernel_object.splits)
    apply (prop_tac "obj_at (same_caps (kernel_object.SchedContext sc n)) ptr s")
     apply (clarsimp simp: obj_at_def)
    apply (clarsimp simp: state_relation_def
                          z[simplified obj_at'_def is_sc_obj_def projectKO_eq projectKO_opts_defs, simplified])
    apply (clarsimp simp: caps_of_state_after_update cte_wp_at_after_update
                              swp_def fun_upd_def obj_at_def)
    apply (subst conj_assoc[symmetric])
    apply (rule conjI[rotated])
     apply (clarsimp simp: ghost_relation_def)
     apply (erule_tac x=ptr in allE)+
     apply (clarsimp simp: obj_at_def a_type_def
                     split: Structures_A.kernel_object.splits if_split_asm)
    apply (fold fun_upd_def)
    apply (simp only: pspace_relation_def simp_thms
                      pspace_dom_update[where x="kernel_object.SchedContext _ _"
                                          and v="kernel_object.SchedContext _ _",
                                        simplified a_type_def, simplified])
    apply (simp only: dom_fun_upd2 simp_thms)
    apply (elim conjE)
    apply (frule bspec, erule domI)
    apply (rule conjI)
     apply (rule ballI, drule(1) bspec)
     apply (drule domD)
     apply (clarsimp simp: project_inject split: if_split_asm kernel_object.split_asm)
     apply (rename_tac sc0 x bb aa ba)
     apply (drule_tac x="(aa, ba)" in bspec, simp)
     apply clarsimp
     apply (frule_tac ko'="kernel_object.SchedContext sc0 n" and x'=ptr
              in obj_relation_cut_same_type)
        apply simp+
     apply (clarsimp simp: a_type_def split: Structures_A.kernel_object.split_asm if_split_asm)
      (* sc_replies_relation *)
    apply (clarsimp simp: sc_replies_relation_def sc_replies_of_scs_def map_project_def scs_of_kh_def)
    apply (drule_tac x=p in spec)
    by (auto simp: typ_at'_def ko_wp_at'_def opt_map_def sc_of_def projectKO_opts_defs
            split: if_splits)
qed

lemma setSchedContext_update_corres:
  assumes R': "sc_relation sc n sc' \<longrightarrow> sc_relation (f sc) n (f' (sc'::sched_context))"
  assumes s: "objBits sc' = objBits (f' sc')"
  shows "corres dc
         (\<lambda>s. kheap s ptr = Some (kernel_object.SchedContext sc n))
         (ko_at' sc' ptr and (\<lambda>s'. heap_ls (replyPrevs_of s') (scReply (f' sc')) (sc_replies (f sc))))
            (set_object ptr (kernel_object.SchedContext (f sc) n))
            (setSchedContext ptr (f' sc'))"
  apply (insert R' s)
  apply (rule_tac F="sc_relation sc n sc'" in corres_req)
   apply (drule state_relation_pspace_relation)
   apply (drule (1) pspace_relation_absD)
   apply (clarsimp simp: obj_at'_def projectKOs split: if_split_asm)
  apply (rule corres_guard_imp)
    apply (rule setSchedContext_corres)
  by (clarsimp simp: obj_at'_def sc_relation_def objBits_simps scBits_simps)+

lemma setSchedContext_no_stack_update_corres:
  "\<lbrakk>sc_relation sc n sc' \<longrightarrow> sc_relation (f sc) n (f' sc');
     sc_replies sc = sc_replies (f sc); objBits sc' = objBits (f' sc');
     scReply sc' = scReply (f' sc')\<rbrakk>
    \<Longrightarrow> corres dc
         (\<lambda>s. kheap s ptr = Some (kernel_object.SchedContext sc n))
         (ko_at' sc' ptr)
            (set_object ptr (kernel_object.SchedContext (f sc) n))
            (setSchedContext ptr (f' sc'))"
  apply (rule_tac F="sc_relation sc n sc'" in corres_req)
   apply (drule state_relation_pspace_relation)
   apply (drule (1) pspace_relation_absD)
   apply (clarsimp simp: obj_at'_def projectKOs split: if_split_asm)
  apply (rule stronger_corres_guard_imp)
    apply (rule setSchedContext_update_corres[where sc=sc and sc'=sc'])
     apply simp+
  apply (clarsimp dest!: state_relation_sc_replies_relation
                   simp: obj_at'_def projectKOs)
  apply (drule (2) sc_replies_relation_prevs_list)
  by fastforce

lemma get_ntfn_corres:
  "corres ntfn_relation (ntfn_at ptr) (ntfn_at' ptr)
     (get_notification ptr) (getNotification ptr)"
  apply (rule corres_no_failI)
   apply wp
  apply (simp add: get_simple_ko_def getNotification_def get_object_def
                   getObject_def bind_assoc gets_the_def)
  apply (clarsimp simp: in_monad split_def bind_def gets_def get_def return_def
                 dest!: readObject_misc_ko_at')
  apply (clarsimp simp: assert_def fail_def obj_at_def return_def is_ntfn partial_inv_def)
  apply (clarsimp simp add: state_relation_def pspace_relation_def obj_at'_def projectKOs)
  apply (drule bspec)
   apply blast
  apply (simp add: other_obj_relation_def)
  done

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
  apply (clarsimp simp add: state_relation_def pspace_relation_def obj_at'_def projectKOs)
  apply (drule bspec)
   apply blast
  apply (simp add: other_obj_relation_def)
  done

lemma getReply_TCB_corres:
  "corres (=) (reply_at ptr) (reply_at' ptr)
     (get_reply_tcb ptr) (liftM replyTCB (getReply ptr))"
  apply clarsimp
  apply (rule get_reply_corres[THEN corres_rel_imp])
  apply (clarsimp simp: reply_relation_def)
  done

lemma get_sc_corres:
  "corres (\<lambda>sc sc'. \<exists>n. sc_relation sc n sc') (sc_at ptr) (sc_at' ptr)
     (get_sched_context ptr) (getSchedContext ptr)"
  apply (rule corres_no_failI)
   apply wp
  apply (simp add: get_sched_context_def getSchedContext_def get_object_def
                   getObject_def bind_assoc gets_the_def)
  apply (clarsimp simp: in_monad split_def bind_def gets_def get_def return_def
                 dest!: readObject_misc_ko_at')
  apply (clarsimp simp: assert_def fail_def obj_at_def return_def is_sc_obj_def
                 split: Structures_A.kernel_object.splits)
  apply (clarsimp simp add: state_relation_def pspace_relation_def obj_at'_def projectKOs)
  apply (drule bspec)
   apply blast
  apply (fastforce simp add: other_obj_relation_def)
  done

lemma get_sc_corres_size:
  "corres (\<lambda>sc sc'. sc_relation sc n sc' \<and> n + minSchedContextBits = objBits sc')
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
  apply (clarsimp simp: state_relation_def pspace_relation_def obj_at'_def projectKOs)
  apply (drule bspec)
   apply blast
  apply (clarsimp simp: other_obj_relation_def scBits_simps sc_relation_def objBits_simps)
  done

lemma setObject_ko_wp_at:
  fixes v :: "'a :: pspace_storable"
  assumes R: "\<And>ko s y n. (updateObject v ko p y n s)
                   = (updateObject_default v ko p y n s)"
  assumes n: "\<And>v' :: 'a. (1 :: word32) < 2 ^ (objBits v')"
  shows      "\<lbrace>\<lambda>s. obj_at' (\<lambda>x :: 'a. True) p s \<longrightarrow>
                    P (ko_wp_at' (if p = p' then K (P' (injectKO v)) else P')p' s)\<rbrace>
                setObject p v
              \<lbrace>\<lambda>rv s. P (ko_wp_at' P' p' s)\<rbrace>"
  apply (clarsimp simp: setObject_def valid_def in_monad
                        ko_wp_at'_def split_def in_magnitude_check n
                        R updateObject_default_def
                        projectKOs obj_at'_real_def
             split del: if_split)
  apply (clarsimp simp: project_inject objBits_def[symmetric] n
                 elim!: rsubst[where P=P]
             split del: if_split)
  apply (rule iffI)
   apply (clarsimp simp: n ps_clear_upd objBits_def[symmetric]
                  split: if_split_asm)
  apply (clarsimp simp: n project_inject objBits_def[symmetric]
                        ps_clear_upd
                 split: if_split_asm)
  done

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
   apply (erule (1) use_valid [OF _ setObject.typ_at_sc_at'_n_lifts'(3)])
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
  assumes n: "\<And>v' :: 'a. (1 :: word32) < 2 ^ (objBits v')"
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
    apply (rule setObject_ko_wp_at [OF R n])
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

\<comment>\<open>
  `idle_tcb_ps val` asserts that `val` is a pspace_storable value
  which corresponds to an idle TCB.
\<close>
definition idle_tcb_ps :: "('a :: pspace_storable) \<Rightarrow> bool" where
  "idle_tcb_ps val \<equiv> (\<exists>tcb. projectKO_opt (injectKO val) = Some tcb \<and> idle_tcb' tcb)"

\<comment>\<open>
  `idle_sc_ps val` asserts that `val` is a pspace_storable value
  which corresponds to an idle SchedContext.
\<close>
definition idle_sc_ps :: "('a :: pspace_storable) \<Rightarrow> bool" where
  "idle_sc_ps val \<equiv> (\<exists>sc. sc_of' (injectKO val) = Some sc \<and> idle_sc' sc)"

lemma setObject_idle':
  fixes v :: "'a :: pspace_storable"
  assumes R: "\<And>ko s y n.
              (updateObject v ko ptr y n s) = (updateObject_default v ko ptr y n s)"
  assumes n: "\<And>v' :: 'a. (1 :: word32) < 2 ^ (objBits v')"
  assumes z: "\<And>P p q n ko.
              \<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace>
              updateObject v p q n ko
              \<lbrace>\<lambda>rv s. P (ksIdleThread s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. valid_idle' s
                   \<and> (ptr = ksIdleThread s
                        \<longrightarrow> (\<exists>val :: 'a. idle_tcb_ps val)
                        \<longrightarrow> idle_tcb_ps v)
                   \<and> (ptr = idle_sc_ptr
                        \<longrightarrow> (\<exists>val :: 'a. idle_sc_ps val)
                        \<longrightarrow> idle_sc_ps v)\<rbrace>
              setObject ptr v
              \<lbrace>\<lambda>rv s. valid_idle' s\<rbrace>"
  apply (simp add: valid_idle'_def pred_tcb_at'_def o_def)
  apply (rule hoare_pre)
   apply (rule hoare_lift_Pf2 [where f="ksIdleThread"])
    apply (simp add: pred_tcb_at'_def obj_at'_real_def)
    apply (wpsimp wp: setObject_ko_wp_at[OF R n])
   apply (wp z)
  apply (rule conjI)
   apply (clarsimp simp: pred_tcb_at'_def obj_at'_real_def ko_wp_at'_def idle_tcb_ps_def
                         idle_sc_ps_def)
   apply (rename_tac tcb sc obj)
   apply (drule_tac x=obj and y=tcb in spec2, clarsimp simp: project_inject)
  apply (clarsimp simp: pred_tcb_at'_def obj_at'_real_def ko_wp_at'_def idle_tcb_ps_def
                        idle_sc_ps_def)
  apply (rename_tac tcb sc obj)
  apply (drule_tac x=obj and y=sc in spec2, clarsimp simp: project_inject)
  done

lemma setObject_no_0_obj' [wp]:
  "\<lbrace>no_0_obj'\<rbrace> setObject p v \<lbrace>\<lambda>r. no_0_obj'\<rbrace>"
  apply (clarsimp simp: setObject_def split_def)
  apply (clarsimp simp: valid_def no_0_obj'_def ko_wp_at'_def in_monad
                        lookupAround2_char1 ps_clear_upd)
  done

lemma valid_updateCapDataI:
  "s \<turnstile>' c \<Longrightarrow> s \<turnstile>' updateCapData b x c"
  apply (unfold updateCapData_def Let_def ARM_H.updateCapData_def)
  apply (cases c)
  apply (simp_all add: isCap_defs valid_cap'_def capUntypedPtr_def isCap_simps
                       capAligned_def word_size word_bits_def word_bw_assocs)
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

lemma ovalid_threadRead:
  "o\<lbrace>\<lambda>s. tcb_at' t s \<longrightarrow> (\<exists>tcb. ko_at' tcb t s \<and> P (f tcb) s)\<rbrace>
    threadRead f t \<lbrace>P\<rbrace>"
  by (clarsimp simp: threadRead_def oliftM_def obind_def obj_at'_def ovalid_def
              dest!: readObject_misc_ko_at' split: option.split_asm)

lemma ovalid_threadRead_sp:
  "o\<lbrace>P\<rbrace> threadRead f ptr \<lbrace>\<lambda>rv s. \<exists>tcb :: tcb. ko_at' tcb ptr s \<and> f tcb = rv \<and> P s\<rbrace>"
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

lemma valid_mdb'_lift:
  "(\<And>P. f \<lbrace>\<lambda>s. P (ctes_of s)\<rbrace>) \<Longrightarrow> f \<lbrace>valid_mdb'\<rbrace>"
  unfolding valid_mdb'_def
  apply simp
  done

lemma setObject_state_refs_of':
  assumes x: "updateObject val = updateObject_default val"
  assumes y: "(1 :: word32) < 2 ^ objBits val"
  shows
  "\<lbrace>\<lambda>s. P ((state_refs_of' s) (ptr := refs_of' (injectKO val)))\<rbrace>
     setObject ptr val
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  apply (clarsimp simp: setObject_def valid_def in_monad split_def
                        updateObject_default_def x
                        projectKOs in_magnitude_check[OF _ y]
                 elim!: rsubst[where P=P] intro!: ext
             split del: if_split cong: option.case_cong if_cong)
  apply (clarsimp simp: state_refs_of'_def objBits_def[symmetric]
                        ps_clear_upd
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
                        lookupAround2_char1
                 elim!: rsubst[where P=P] intro!: ext
             split del: if_split cong: option.case_cong if_cong)
  apply (frule x)
  apply (simp add: state_refs_of'_def ps_clear_upd updateObject_size
             cong: option.case_cong if_cong)+
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
  by (clarsimp simp: setObject_def split_def pspace_domain_valid_def valid_def
                      in_monad lookupAround2_char1 updateObject_size
              split: if_split_asm)

lemma ct_not_inQ_lift:
  assumes sch_act: "\<And>P. \<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksSchedulerAction s)\<rbrace>"
      and not_inQ: "\<lbrace>\<lambda>s. obj_at' (Not \<circ> tcbQueued) (ksCurThread s) s\<rbrace>
                    f \<lbrace>\<lambda>_ s. obj_at' (Not \<circ> tcbQueued) (ksCurThread s) s\<rbrace>"
  shows "\<lbrace>ct_not_inQ\<rbrace> f \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  unfolding ct_not_inQ_def
  by (rule hoare_convert_imp [OF sch_act not_inQ])

lemma obj_at'_ignoring_obj:
  "obj_at' (\<lambda>_ :: 'a :: pspace_storable. P) p s = (obj_at' (\<lambda>_ :: 'a. True) p s \<and> P)"
  by (rule iffI; clarsimp simp: obj_at'_def)

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

lemma sch_act_simple[wp]:
  "f \<lbrace>\<lambda>s. P (sch_act_simple s)\<rbrace>"
  apply (wpsimp wp: ksSchedulerAction simp: sch_act_simple_def)
  done

end

locale simple_ko' =
  fixes f :: "obj_ref \<Rightarrow> 'a::pspace_storable \<Rightarrow> unit kernel"
    and g :: "obj_ref \<Rightarrow> 'a kernel"
  assumes f_def: "f p v = setObject p v"
  assumes g_def: "g p = getObject p"
  assumes default_update: "updateObject (v::'a) = updateObject_default (v::'a)"
  assumes default_load: "(loadObject ptr ptr' next obj :: 'a kernel_r) =
                              loadObject_default ptr ptr' next obj"
  assumes not_cte: "projectKO_opt (KOCTE cte) = (None::'a option)"
  assumes objBits: "\<forall>v. (1::machine_word) < 2^(objBits (v::'a))"
begin

lemma updateObject_cte[simp]:
  "fst (updateObject (v::'a) (KOCTE cte) p x n s) = {}"
  by (clarsimp simp: default_update updateObject_default_def in_monad projectKOs not_cte bind_def)

lemma pspace_aligned'[wp]: "f p v \<lbrace>pspace_aligned'\<rbrace>"
  and pspace_distinct'[wp]: "f p v \<lbrace>pspace_distinct'\<rbrace>"
  and no_0_obj'[wp]: "f p v \<lbrace>no_0_obj'\<rbrace>"
  unfolding f_def by (all \<open>wpsimp simp: default_update updateObject_default_def in_monad\<close>)

lemma valid_objs':
  "\<lbrace>valid_objs' and valid_obj' (injectKO v) \<rbrace> f p v \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  unfolding f_def
  by (rule setObject_valid_objs')
     (clarsimp simp: default_update updateObject_default_def in_monad projectKOs)+

lemma typ_at'[wp]:
  "f p v \<lbrace>\<lambda>s. P (typ_at' T p' s)\<rbrace>"
  unfolding f_def
  by (rule setObject_typ_at')

lemma sc_at'_n[wp]: "f p v \<lbrace>\<lambda>s. P (sc_at'_n n p' s)\<rbrace>"
  unfolding f_def
  by (clarsimp simp: valid_def setObject_def in_monad split_def ko_wp_at'_def ps_clear_upd
                     updateObject_size lookupAround2_char1 updateObject_type)

sublocale typ_at_all_props' "f p v" for p v by typ_at_props'

sublocale pspace_only' "f p v" for p v
  unfolding f_def
  by unfold_locales
     (fastforce simp: setObject_def updateObject_default_def magnitudeCheck_def default_update
                      in_monad split_def projectKOs
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
  using objBits by (auto intro: setObject_state_refs_of' simp: default_update)

lemma valid_arch_state'[wp]:
  "f p v \<lbrace> valid_arch_state' \<rbrace>"
  by (rule valid_arch_state_lift'; wp)

lemmas valid_irq_node'[wp] = valid_irq_node_lift[OF ksInterruptState typ_at']
lemmas irq_states' [wp] = valid_irq_states_lift' [OF ksInterruptState ksMachineState]
lemmas irqs_masked'[wp] = irqs_masked_lift[OF ksInterruptState]

lemma valid_machine_state'[wp]:
  "f p v \<lbrace>valid_machine_state'\<rbrace>"
  unfolding valid_machine_state'_def pointerInDeviceData_def pointerInUserData_def
  by (wp hoare_vcg_all_lift hoare_vcg_disj_lift)

lemma pspace_domain_valid[wp]:
  "f ptr val \<lbrace>pspace_domain_valid\<rbrace>"
  unfolding f_def by (wpsimp simp: default_update updateObject_default_def in_monad projectKOs)

lemmas x = ct_not_inQ_lift[OF ksSchedulerAction]

lemma setObject_wp:
  "\<lbrace>\<lambda>s. P (set_obj' ptr obj s)\<rbrace>
   setObject ptr (obj :: 'a :: pspace_storable)
   \<lbrace>\<lambda>_. P\<rbrace>"
  apply (wpsimp simp: setObject_def default_update updateObject_default_def fun_upd_def
                      ARM_H.fromPPtr_def) (* FIXME: arch split *)
                                          (* FIXME: this is a simp rule, why isn't it available? *)
  done

lemmas set_wp = setObject_wp[folded f_def]

\<comment>\<open>
  Keeps the redundant @{term "obj_at \<top>"} precondition because this matches common abbreviations
  like @{term "tcb_at'"}.
\<close>
lemma setObject_pre:
  fixes obj :: 'a
  assumes "\<lbrace>P and obj_at' (\<lambda>old_obj :: 'a. objBits old_obj = objBits obj) p
              and obj_at' (\<lambda>_ :: 'a. True) p\<rbrace>
           setObject p obj
           \<lbrace>Q\<rbrace>"
  shows "\<lbrace>P\<rbrace> setObject p obj \<lbrace>Q\<rbrace>"
  supply simps = in_magnitude_check[OF _ objBits[rule_format], unfolded objBits_def] valid_def
                 setObject_def in_monad split_def default_update updateObject_default_def
                 projectKO_eq2 project_inject objBits_def
                 ARM_H.fromPPtr_def (* FIXME: arch split *)
  using assms
  apply (clarsimp simp: simps)
  apply (rename_tac s ko)
  apply (drule_tac x=s in spec)
  apply (clarsimp simp: obj_at'_def projectKO_eq split_paired_Ball project_inject)
  apply (erule impE)
   apply fastforce
  apply (drule spec, erule mp)
  apply (fastforce simp: simps)
  done

\<comment>\<open>
  Keeps the redundant @{term "obj_at \<top>"} precondition because this matches common abbreviations
  like @{term "tcb_at'"}.

  Lets the postcondition pointer depend on the state for things like @{term "ksCurThread"}.
\<close>
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
  apply (erule rsubst[where P=Q])
  apply (case_tac "ptr = ptr' (set_obj' ptr obj s)"; simp)
   apply (clarsimp simp: same_size_obj_at'_set_obj'_iff
                         obj_at'_ignoring_obj[where P="P f obj" for f])
  apply (clarsimp simp: obj_at'_def projectKO_eq project_inject ps_clear_upd)
  done

lemmas obj_at'_strongest = setObject_obj_at'_strongest[folded f_def]

lemma setObject_obj_at':
  fixes v :: 'a
  shows "\<lbrace>\<lambda>s. obj_at' (\<lambda>_:: 'a. True) p s \<longrightarrow> P (if p = p' then P' v else obj_at' P' p' s)\<rbrace>
         setObject p v
         \<lbrace>\<lambda>rv s. P (obj_at' P' p' s)\<rbrace>"
  by (wpsimp wp: setObject_obj_at'_strongest split: if_splits)

lemmas obj_at' = setObject_obj_at'[folded f_def]

lemma getObject_wp:
  "\<lbrace>\<lambda>s. \<forall>ko :: 'a. ko_at' ko p s \<longrightarrow> P ko s\<rbrace>
   getObject p
   \<lbrace>P\<rbrace>"
  apply (wpsimp simp: getObject_def default_load ARM_H.fromPPtr_def loadObject_default_def
                      projectKO_def readObject_def omonad_defs split_def)
  apply (rename_tac ko)
  apply (prop_tac "ko_at' ko p s")
   apply (clarsimp simp: obj_at'_def project_inject projectKO_eq objBits_def[symmetric]
                         read_magnitudeCheck_def
                         lookupAround2_no_after_ps_clear
                         lookupAround2_after_ps_clear[OF _ _  sc_objBits_pos_power2]
                  split: if_split_asm option.split_asm)
  apply fastforce
  done

lemmas get_wp = getObject_wp[folded g_def]

lemma loadObject_default_inv:
  "\<lbrace>P\<rbrace> gets_the $ loadObject_default addr addr' next obj \<lbrace>\<lambda>rv. P\<rbrace>"
  by wpsimp

lemma getObject_inv:
  "\<lbrace>P\<rbrace> getObject p \<lbrace>\<lambda>(rv :: 'a). P\<rbrace>"
  by (wpsimp simp: default_load getObject_def split_def wp: loadObject_default_inv)

lemmas get_inv = getObject_inv[folded g_def]

lemma getObject_sp:
  "\<lbrace>P\<rbrace> getObject r \<lbrace>\<lambda>rv::'a. P and ko_at' rv r\<rbrace>"
  apply (clarsimp simp: getObject_def loadObject_default_def default_load objBits
                        projectKOs in_monad valid_def obj_at'_def project_inject
                        split_def ARM_H.fromPPtr_def readObject_def omonad_defs
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

\<comment>\<open> Stronger than getObject_inv. \<close>
lemma getObject_wp_state_only:
  "\<lbrace>\<lambda>s. obj_at' (\<lambda>_ :: 'a. True) p s \<longrightarrow> P s\<rbrace> getObject p \<lbrace>\<lambda>_ :: 'a. P\<rbrace>"
  apply (wpsimp wp: getObject_wp)
  apply (clarsimp simp: obj_at'_def)
  done

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

lemmas getObject_ko_at' = getObject_ko_at[OF default_load objBits[rule_format]]

lemmas get_ko_at' = getObject_ko_at'[folded g_def]

lemmas ko_wp_at = setObject_ko_wp_at[where 'a='a, folded f_def,
                                     simplified default_update objBits, simplified]

lemma setObject_valid_reply':
  "setObject p (ko :: 'a) \<lbrace>valid_reply' reply'\<rbrace>"
  unfolding valid_reply'_def valid_bound_obj'_def
  apply (wpsimp split: option.splits
                   wp: hoare_vcg_imp_lift' hoare_vcg_all_lift)
  apply fastforce
  done

lemmas set_valid_reply' = setObject_valid_reply'[folded f_def]

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

end

locale simple_non_tcb_ko' = simple_ko' "f:: obj_ref \<Rightarrow> 'a::pspace_storable \<Rightarrow> unit kernel"
                                       "g:: obj_ref \<Rightarrow> 'a kernel" for f g +
  assumes not_tcb: "projectKO_opt (KOTCB sc) = (None :: 'a option)"
begin

lemma updateObject_tcb[simp]:
  "fst (updateObject (v::'a) (KOTCB tcb) p x n s) = {}"
  by (clarsimp simp: default_update updateObject_default_def in_monad projectKOs not_tcb bind_def)

lemma not_inject_tcb[simp]:
  "injectKO (v::'a) \<noteq> KOTCB tcb"
  by (simp flip: project_inject add: projectKOs not_tcb)

lemma typeOf_not_tcb[simp]:
  "koTypeOf (injectKO (v::'a)) \<noteq> TCBT"
  by (cases "injectKO v"; simp)

lemma cte_wp_at'[wp]: "f p v \<lbrace>\<lambda>s. P (cte_wp_at' Q p' s)\<rbrace>"
  unfolding f_def by (rule setObject_cte_wp_at2'[where Q="\<top>", simplified]; simp)

lemma ctes_of[wp]: "f p v \<lbrace>\<lambda>s. P (ctes_of s)\<rbrace>"
  unfolding f_def by (rule setObject_ctes_of[where Q="\<top>", simplified]; simp)

lemma valid_mdb'[wp]: "f p v \<lbrace>valid_mdb'\<rbrace>"
  unfolding valid_mdb'_def by wp

lemma obj_at_tcb'[wp]:
  "f p v \<lbrace>\<lambda>s. P (obj_at' (Q :: tcb \<Rightarrow> bool) p' s)\<rbrace>"
  unfolding f_def obj_at'_real_def
  using objBits
  apply (wp setObject_ko_wp_at; simp add: default_update)
  apply (clarsimp simp: obj_at'_def ko_wp_at'_def projectKOs)
  apply (case_tac ko; simp add: projectKOs not_tcb)
  done

lemma valid_queues[wp]:
  "f p v \<lbrace> valid_queues \<rbrace>"
  unfolding valid_queues_def valid_queues_no_bitmap_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_ball_lift |wps)+

lemma valid_inQ_queues[wp]:
  "f p v \<lbrace> valid_inQ_queues \<rbrace>"
  unfolding valid_inQ_queues_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_ball_lift | wps)+

lemma set_non_tcb_valid_queues'[wp]:
  "f p v \<lbrace>valid_queues'\<rbrace>"
  unfolding valid_queues'_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift)

lemma set_non_tcb_valid_release_queue[wp]:
  "f p v \<lbrace>valid_release_queue\<rbrace>"
  unfolding valid_release_queue_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift | wps)+

lemma set_non_tcb_valid_release_queue'[wp]:
  "f p v \<lbrace>valid_release_queue'\<rbrace>"
  unfolding valid_release_queue'_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift | wps)+

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

lemma cap_to'[wp]:
  "f p' v \<lbrace>ex_nonz_cap_to' p\<rbrace>"
  by (wp ex_nonz_cap_to_pres')

lemma ifunsafe'[wp]:
  "f p v \<lbrace>if_unsafe_then_cap'\<rbrace>"
  unfolding f_def
  apply (rule setObject_ifunsafe'[where P="\<top>", simplified])
    apply (clarsimp simp: default_update updateObject_default_def in_monad projectKOs not_tcb
                          not_cte
                  intro!: equals0I)+
  apply (simp add: setObject_def split_def default_update)
  apply (wp updateObject_default_inv | simp)+
  done

lemmas irq_handlers[wp] = valid_irq_handlers_lift'' [OF ctes_of ksInterruptState]
lemmas irq_handlers'[wp] = valid_irq_handlers_lift'' [OF ctes_of ksInterruptState]

lemma valid_global_refs'[wp]:
  "f p v \<lbrace>valid_global_refs'\<rbrace>"
  by (rule valid_global_refs_lift'; wp)

lemma ct_not_inQ[wp]:
  "f p v \<lbrace>ct_not_inQ\<rbrace>"
  apply (rule ct_not_inQ_lift, wp)
  apply (rule hoare_lift_Pf[where f=ksCurThread]; wp)
  done

lemma ct_idle_or_in_cur_domain'[wp]:
  "f p v \<lbrace> ct_idle_or_in_cur_domain' \<rbrace>"
  by (rule ct_idle_or_in_cur_domain'_lift; wp)

lemma untyped_ranges_zero'[wp]:
  "f p ko \<lbrace>untyped_ranges_zero'\<rbrace>"
  unfolding cteCaps_of_def o_def
  apply (wpsimp wp: untyped_ranges_zero_lift)
  done

end

locale simple_non_reply_ko' = simple_ko' "f:: obj_ref \<Rightarrow> 'a::pspace_storable \<Rightarrow> unit kernel"
                                         "g:: obj_ref \<Rightarrow> 'a kernel" for f g +
  assumes not_reply: "projectKO_opt (KOReply reply) = (None :: 'a option)"
begin

lemma updateObject_reply[simp]:
  "fst (updateObject (v::'a) (KOReply c) p x n s) = {}"
  by (clarsimp simp: default_update updateObject_default_def in_monad projectKOs not_reply bind_def)

lemma not_inject_reply[simp]:
  "injectKO (v::'a) \<noteq> KOReply sc"
  by (simp flip: project_inject add: projectKOs not_reply)

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

\<comment>\<open>
  preservation of valid_replies' requires us to not be touching either of a Reply or a TCB
\<close>

lemma valid_replies'[wp]:
  "\<lbrace>valid_replies' and pspace_distinct' and pspace_aligned'\<rbrace>
   f p v
   \<lbrace>\<lambda>_. valid_replies'\<rbrace>"
   (is "\<lbrace>?pre valid_replies'\<rbrace> _ \<lbrace>?post\<rbrace>")
  apply (rule_tac Q="\<lambda>_. ?pre valid_replies'_alt" in hoare_post_imp;
         clarsimp simp: valid_replies'_def2)
  unfolding obj_at'_real_def
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift ko_wp_at hoare_vcg_ex_lift)
  by (fastforce simp: valid_replies'_def2 obj_at'_def ko_wp_at'_def projectKOs)

lemma valid_pspace':
  "\<lbrace>valid_pspace' and valid_obj' (injectKO v) \<rbrace> f p v \<lbrace>\<lambda>_. valid_pspace'\<rbrace>"
  unfolding valid_pspace'_def by (wpsimp wp: valid_objs')

end

locale simple_non_sc_ko' = simple_ko' "f:: obj_ref \<Rightarrow> 'a::pspace_storable \<Rightarrow> unit kernel"
                                      "g:: obj_ref \<Rightarrow> 'a kernel" for f g +
  assumes not_sc: "projectKO_opt (KOSchedContext sc) = (None :: 'a option)"
begin

lemma updateObject_sc[simp]:
  "fst (updateObject (v::'a) (KOSchedContext c) p x n s) = {}"
  by (clarsimp simp: default_update updateObject_default_def in_monad projectKOs not_sc bind_def)

lemma not_inject_sc[simp]:
  "injectKO (v::'a) \<noteq> KOSchedContext sc"
  by (simp flip: project_inject add: projectKOs not_sc)

lemma typeOf_not_sc[simp]:
  "koTypeOf (injectKO (v::'a)) \<noteq> SchedContextT"
  by (cases "injectKO v"; simp)

end

locale simple_non_tcb_non_sc_ko' =
   simple_non_sc_ko' "f:: obj_ref \<Rightarrow> 'a::pspace_storable \<Rightarrow> unit kernel"
                     "g:: obj_ref \<Rightarrow> 'a kernel" +
   simple_non_tcb_ko' "f:: obj_ref \<Rightarrow> 'a::pspace_storable \<Rightarrow> unit kernel"
                      "g:: obj_ref \<Rightarrow> 'a kernel" for f g
begin

\<comment>\<open>
  preservation of valid_idle' requires us to not be touching either of an SC or a TCB
\<close>

lemma idle'[wp]:
  "f p v \<lbrace>valid_idle'\<rbrace>"
  unfolding f_def
  using objBits
  apply (wp setObject_idle'
         ; simp add: default_update updateObject_default_inv idle_tcb_ps_def idle_sc_ps_def)
  apply (clarsimp simp: projectKOs)
  done

end

locale simple_non_tcb_non_sc_non_reply_ko' =
   simple_non_tcb_non_sc_ko' "f:: obj_ref \<Rightarrow> 'a::pspace_storable \<Rightarrow> unit kernel"
                             "g:: obj_ref \<Rightarrow> 'a kernel" +
   simple_non_tcb_non_reply_ko' "f:: obj_ref \<Rightarrow> 'a::pspace_storable \<Rightarrow> unit kernel"
                             "g:: obj_ref \<Rightarrow> 'a kernel" for f g

(* FIXME: should these be in Arch + sublocale instead? *)
interpretation set_ep': simple_non_tcb_non_sc_non_reply_ko' setEndpoint getEndpoint
  by unfold_locales (simp_all add: setEndpoint_def getEndpoint_def projectKO_opts_defs
                                   objBits_simps')

interpretation set_ntfn': simple_non_tcb_non_sc_non_reply_ko' setNotification getNotification
  by unfold_locales (simp_all add: setNotification_def getNotification_def projectKO_opts_defs
                                   objBits_simps')

interpretation set_reply': simple_non_tcb_non_sc_ko' setReply getReply
  by unfold_locales (simp_all add: setReply_def getReply_def projectKO_opts_defs objBits_simps')

interpretation set_sc': simple_non_tcb_non_reply_ko' setSchedContext getSchedContext
  by unfold_locales (simp_all add: setSchedContext_def getSchedContext_def projectKO_opts_defs
                                   objBits_simps' scBits_pos_power2)

interpretation set_tcb': simple_non_sc_ko' "\<lambda>p v. setObject p (v::tcb)"
                                           "\<lambda>p. getObject p :: tcb kernel"
  by unfold_locales (simp_all add: projectKO_opts_defs objBits_simps')

interpretation threadSet: pspace_only' "threadSet f p"
  unfolding threadSet_def
  apply unfold_locales
  apply (clarsimp simp: in_monad)
  apply (drule_tac P="(=) s" in use_valid[OF _ getObject_tcb_inv], rule refl)
  apply (fastforce dest: set_tcb'.pspace)
  done

context begin interpretation Arch . (*FIXME: arch_split*)

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
lemmas set_ep_valid_pspace'[wp] =
  set_ep'.valid_pspace'[simplified valid_obj'_def pred_conj_def, simplified]

lemmas set_ntfn_valid_objs'[wp] =
  set_ntfn'.valid_objs'[simplified valid_obj'_def pred_conj_def, simplified]
lemmas set_ntfn_valid_pspace'[wp] =
  set_ntfn'.valid_pspace'[simplified valid_obj'_def pred_conj_def, simplified]

lemmas set_reply_valid_objs'[wp] =
  set_reply'.valid_objs'[simplified valid_obj'_def pred_conj_def, simplified]

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
  "\<lbrace>\<lambda>s. P ((state_refs_of' s)(p := get_refs ReplySchedContext (replySC reply) \<union>
                                   get_refs ReplyTCB (replyTCB reply)))\<rbrace>
   setReply p reply
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  by (wp set_reply'.state_refs_of') (simp flip: fun_upd_def)

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

lemma setSchedContext_iflive'[wp]:
  "\<lbrace>if_live_then_nonz_cap' and (\<lambda>s. live_sc' sc \<longrightarrow> ex_nonz_cap_to' p s)\<rbrace>
   setSchedContext p sc
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  unfolding setSchedContext_def
  by (wpsimp wp: setObject_iflive'[where P="\<top>"]
           simp: updateObject_default_def in_monad scBits_pos_power2
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
   apply (clarsimp simp: updateObject_default_def in_monad
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

end

lemma set_ntfn_minor_invs':
  "\<lbrace>invs'
      and valid_ntfn' val
      and (\<lambda>s. live' (KONotification val) \<longrightarrow> ex_nonz_cap_to' ptr s)\<rbrace>
   setNotification ptr val
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (clarsimp simp add: invs'_def valid_state'_def cteCaps_of_def valid_dom_schedule'_def)
  apply (wpsimp wp: irqs_masked_lift valid_irq_node_lift untyped_ranges_zero_lift
              simp: o_def)
  done

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

lemma idle_sc_is_global [intro!]:
  "idle_sc_ptr \<in> global_refs' s"
  by (simp add: global_refs'_def)

lemma valid_globals_cte_wpD':
  "\<lbrakk> valid_global_refs' s; cte_wp_at' P p s; ptr \<in> global_refs' s \<rbrakk>
       \<Longrightarrow> \<exists>cte. P cte \<and> ptr \<notin> capRange (cteCap cte)"
  by (fastforce simp: valid_global_refs'_def valid_refs'_def  cte_wp_at_ctes_of)

lemmas valid_globals_cte_wpD'_idleThread = valid_globals_cte_wpD'[OF _ _ idle_is_global]
lemmas valid_globals_cte_wpD'_idleSC = valid_globals_cte_wpD'[OF _ _ idle_sc_is_global]

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

crunches doMachineOp
  for cte_wp_at'2[wp]: "\<lambda>s. P (cte_wp_at' P' p s)"
  and typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and sc_at'_n[wp]: "\<lambda>s. P (sc_at'_n n p s)"

global_interpretation doMachineOp: typ_at_all_props' "doMachineOp mop"
  by typ_at_props'

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
  "\<lbrace>sch_act_simple\<rbrace> doMachineOp mop \<lbrace>\<lambda>rv. sch_act_simple\<rbrace>"
  by (simp add: doMachineOp_def split_def sch_act_simple_def
       | wp cur_tcb_lift sch_act_wf_lift tcb_in_cur_domain'_lift
       | fastforce elim: state_refs_of'_pspaceI)+

crunches doMachineOp
  for obj_at'[wp]: "\<lambda>s. P (obj_at' P' p s)"
  and it[wp]: "\<lambda>s. P (ksIdleThread s)"
  and idle'[wp]: "valid_idle'"
  and pde_mappings'[wp]: "valid_pde_mappings'"
  and ko_wp_at'[wp]: "\<lambda>s. P (ko_wp_at' T p s)"

context begin interpretation Arch . (*FIXME: arch_split*)

lemmas bit_simps' = pteBits_def asidHighBits_def asid_low_bits_def
                    asid_high_bits_def minSchedContextBits_def
                    replySizeBits_def pageBits_def pdeBits_def ptBits_def pdBits_def

lemmas is_aligned_add_step_le' = is_aligned_add_step_le[simplified mask_2pm1 add_diff_eq]

lemma objBitsKO_Data:
  "objBitsKO (if dev then KOUserDataDevice else KOUserData) = pageBits"
  by (simp add: objBits_def objBitsKO_def word_size_def)

lemma of_bl_shift_cte_level_bits:
  "(of_bl z :: machine_word) << cte_level_bits \<le> mask (cte_level_bits + length z)"
  by word_bitwise
     (simp add: test_bit_of_bl word_size cte_level_bits_def rev_bl_order_simps)

lemma obj_relation_cuts_range_limit:
  "\<lbrakk> (p', P) \<in> obj_relation_cuts ko p; P ko ko' \<rbrakk>
   \<Longrightarrow> \<exists>x n. p' = p + x \<and> is_aligned x n \<and> n \<le> obj_bits ko \<and> x \<le> mask (obj_bits ko)"
   apply (erule (1) obj_relation_cutsE; clarsimp)
     apply (drule (1) wf_cs_nD)
     apply (clarsimp simp: cte_map_def[simplified word_shift_by_n])
     apply (rule_tac x=cte_level_bits in exI)
     apply (simp add: is_aligned_shift of_bl_shift_cte_level_bits)
       apply (rule_tac x=minSchedContextBits in exI)
       apply (simp add: bit_simps' min_sched_context_bits_def)
      apply (rule_tac x=replySizeBits in exI)
      apply (simp add: replySizeBits_def)
     apply (rule_tac x=pteBits in exI)
     apply (simp add: bit_simps is_aligned_shift mask_def pteBits_def)
     apply word_bitwise
    apply (rule_tac x=pdeBits in exI)
    apply (simp add: bit_simps is_aligned_shift mask_def pdeBits_def)
    apply word_bitwise
   apply (rule_tac x=pageBits in exI)
   apply (simp add: is_aligned_shift pbfs_atleast_pageBits is_aligned_mult_triv2)
   apply (simp add: mask_def shiftl_t2n mult_ac)
   apply (frule word_less_power_trans2, rule pbfs_atleast_pageBits)
    apply (simp add: pbfs_less_wb'[unfolded word_bits_def, simplified])
   apply (simp add: pbfs_less_wb'[unfolded word_bits_def, simplified])
  apply fastforce
  done

lemma obj_relation_cuts_range_mask_range:
  "\<lbrakk> (p', P) \<in> obj_relation_cuts ko p; P ko ko'; is_aligned p (obj_bits ko) \<rbrakk>
   \<Longrightarrow> p' \<in> mask_range p (obj_bits ko)"
  apply (drule (1) obj_relation_cuts_range_limit, clarsimp)
  apply (rule conjI)
   apply (rule word_plus_mono_right2; assumption?)
   apply (simp add: is_aligned_no_overflow_mask)
  apply (erule word_plus_mono_right)
  apply (simp add: is_aligned_no_overflow_mask)
  done

lemma obj_relation_cuts_obj_bits:
  "\<lbrakk> (p', P) \<in> obj_relation_cuts ko p; P ko ko' \<rbrakk> \<Longrightarrow> objBitsKO ko' \<le> obj_bits ko"
  apply (erule (1) obj_relation_cutsE;
          clarsimp simp: objBits_simps objBits_defs cte_level_bits_def sc_const_eq[symmetric]
                         pbfs_atleast_pageBits[simplified bit_simps] archObjSize_def pteBits_def
                         pdeBits_def)
  apply (clarsimp simp: scBits_inverse_sc_relation[simplified])
  apply (cases ko; simp add: other_obj_relation_def objBits_defs
                      split: kernel_object.splits)
  apply (rename_tac ako, case_tac ako; clarsimp)
  apply (rename_tac ako', case_tac ako'; clarsimp simp: archObjSize_def)
  done

lemma typ_at'_same_type:
  assumes "typ_at' T p s" "koTypeOf k = koTypeOf ko" "objBitsKO k = objBitsKO ko" "ksPSpace s p' = Some ko"
  shows "typ_at' T p (s\<lparr>ksPSpace :=ksPSpace s(p' \<mapsto> k)\<rparr>)"
  using assms
  by (clarsimp simp: typ_at'_def ko_wp_at'_def ps_clear_upd)

lemma cte_at'_same_type:
  "\<lbrakk>cte_wp_at' \<top> t s; koTypeOf k = koTypeOf ko;objBitsKO k = objBitsKO ko;
    ksPSpace s p = Some ko\<rbrakk>
      \<Longrightarrow> cte_wp_at' \<top> t (s\<lparr>ksPSpace := ksPSpace s(p \<mapsto> k)\<rparr>)"
  apply (simp add: cte_at_typ' typ_at'_same_type)
  apply (elim exE disjE)
   apply (rule disjI1, clarsimp simp: typ_at'_same_type)
  apply (rule disjI2, rule_tac x=n in exI, clarsimp simp: typ_at'_same_type)
  done

lemma valid_ep'_ep_update:
  "\<lbrakk> valid_objs' s; valid_ep' ep s; ep_at' epPtr s; ksPSpace s x = Some (KOEndpoint obj) \<rbrakk>
     \<Longrightarrow> valid_ep' obj (s\<lparr>ksPSpace := ksPSpace s(epPtr \<mapsto> KOEndpoint ep)\<rparr>)"
  apply (erule (1) valid_objsE')
  apply (fastforce simp: valid_objs'_def valid_obj'_def obj_at'_def projectKOs valid_ep'_def
                  split: endpoint.splits)
  done

lemma valid_cap'_ep_update:
  "\<lbrakk> valid_cap' cap s; valid_objs' s; valid_ep' ep s; ep_at' epPtr s \<rbrakk>
     \<Longrightarrow> valid_cap' cap (s\<lparr>ksPSpace := ksPSpace s(epPtr \<mapsto> KOEndpoint ep)\<rparr>)"
  supply ps_clear_upd[simp]
  apply (clarsimp simp: typ_at'_same_type ko_wp_at'_def cte_at'_same_type
                        valid_cap'_def obj_at'_def projectKOs objBits_simps
                 split: endpoint.splits capability.splits)
         apply fastforce+
       apply (clarsimp split: zombie_type.splits simp: projectKOs obj_at'_def typ_at'_same_type)
       apply (intro conjI impI; clarsimp)
        apply (drule_tac x=addr in spec, clarsimp)
       apply (drule_tac x=addr in spec, clarsimp)
      apply (clarsimp simp: ko_wp_at'_def valid_cap'_def obj_at'_def projectKOs objBits_simps
                            page_directory_at'_def page_table_at'_def
                            ARM_H.arch_capability.distinct ARM_H.arch_capability.inject
                     split: ARM_H.arch_capability.splits option.splits if_split_asm
           | rule_tac ko="KOEndpoint obj" in typ_at'_same_type[where p'=epPtr]
           | simp)+
     apply fastforce
    apply (clarsimp simp: valid_untyped'_def ko_wp_at'_def obj_range'_def split: if_split_asm)
     apply (drule_tac x=epPtr in spec, fastforce simp: objBits_simps)+
   apply (drule_tac x=addr in spec, fastforce)
  apply fastforce
  done

lemma valid_cap'_reply_update:
  "\<lbrakk> valid_cap' cap s; valid_objs' s; valid_reply' reply s; reply_at' rptr s \<rbrakk>
     \<Longrightarrow> valid_cap' cap (s\<lparr>ksPSpace := ksPSpace s(rptr \<mapsto> KOReply reply)\<rparr>)"
  supply ps_clear_upd[simp]
  apply (clarsimp simp: typ_at'_same_type ko_wp_at'_def cte_at'_same_type
                        valid_cap'_def obj_at'_def projectKOs objBits_simps
                 split: endpoint.splits capability.splits)
         apply fastforce+
      apply (clarsimp split: zombie_type.splits simp: projectKOs obj_at'_def typ_at'_same_type)
      apply (intro conjI impI; clarsimp)
       apply (drule_tac x=addr in spec, clarsimp)
      apply (drule_tac x=addr in spec, clarsimp)
     apply (clarsimp simp: ko_wp_at'_def valid_cap'_def obj_at'_def projectKOs objBits_simps
                           page_directory_at'_def page_table_at'_def
                    split: ARM_H.arch_capability.splits option.splits if_split_asm
          | rule_tac ko="KOReply obj" in typ_at'_same_type[where p'=rptr])+
    apply (clarsimp simp: valid_untyped'_def ko_wp_at'_def obj_range'_def split: if_split_asm)
     apply (drule_tac x=rptr in spec, fastforce simp: objBits_simps)+
   apply (drule_tac x=addr in spec, fastforce)
  apply fastforce
  done

lemma valid_tcb_state'_ep_update:
  "\<lbrakk> valid_objs' s; valid_ep' ep s; ep_at' epPtr s;  ksPSpace s x = Some (KOTCB obj) \<rbrakk>
     \<Longrightarrow> valid_tcb_state' (tcbState obj) (s\<lparr>ksPSpace := ksPSpace s(epPtr \<mapsto> KOEndpoint ep)\<rparr>)"
  apply (rule valid_objsE', simp, simp)
  by (fastforce simp: typ_at'_same_type ps_clear_upd objBits_simps valid_obj'_def projectKOs
                      valid_tcb_state'_def valid_bound_obj'_def valid_tcb'_def obj_at'_def
               split: option.splits thread_state.splits)

lemma valid_tcb_state'_reply_update:
  "\<lbrakk> valid_objs' s; valid_reply' reply s; reply_at' rptr s; ksPSpace s x = Some (KOTCB obj) \<rbrakk>
     \<Longrightarrow> valid_tcb_state' (tcbState obj) (s\<lparr>ksPSpace := ksPSpace s(rptr \<mapsto> KOReply reply)\<rparr>)"
  apply (rule valid_objsE', simp, simp)
  by (fastforce simp: typ_at'_same_type ps_clear_upd objBits_simps valid_obj'_def projectKOs
                      valid_bound_obj'_def valid_tcb'_def valid_tcb_state'_def obj_at'_def
               split: option.splits thread_state.splits)

lemma valid_tcb'_ep_update:
  "\<lbrakk> valid_objs' s; valid_ep' ep s; ep_at' epPtr s; ksPSpace s x = Some (KOTCB obj) \<rbrakk>
     \<Longrightarrow> valid_tcb' obj (s\<lparr>ksPSpace := ksPSpace s(epPtr \<mapsto> KOEndpoint ep)\<rparr>)"
  apply (rule valid_objsE', simp, simp)
  by (fastforce simp: typ_at'_same_type ps_clear_upd objBits_simps valid_obj'_def projectKOs
                      valid_bound_obj'_def valid_tcb'_def obj_at'_def valid_tcb_state'_ep_update
                      valid_cap'_ep_update
              split: option.splits thread_state.splits)

lemma valid_arch_obj'_ep_update:
  "\<lbrakk> valid_objs' s; valid_ep' ep s; ep_at' epPtr s; ksPSpace s x = Some (KOArch obj) \<rbrakk>
     \<Longrightarrow> valid_arch_obj' obj (s\<lparr>ksPSpace := ksPSpace s(epPtr \<mapsto> KOEndpoint ep)\<rparr>)"
  apply (rule valid_objsE', simp, simp)
  apply (cases obj; clarsimp simp: valid_arch_obj'_def valid_obj'_def obj_at'_def projectKOs
                            split: arch_kernel_object.splits)
    apply (rename_tac asid ep', case_tac asid, simp)
   apply (rename_tac pte ep', case_tac pte; simp add: valid_mapping'_def)
  apply (rename_tac pde ep', case_tac pde; simp add: valid_mapping'_def)
  done

lemma valid_arch_obj'_reply_update:
  "\<lbrakk> valid_objs' s; valid_reply' reply s; reply_at' rptr s; ksPSpace s x = Some (KOArch obj) \<rbrakk>
     \<Longrightarrow> valid_arch_obj' obj (s\<lparr>ksPSpace := ksPSpace s(rptr \<mapsto> KOReply reply)\<rparr>)"
  supply ps_clear_upd[simp]
  apply (rule valid_objsE', simp, simp)
  apply (cases obj; clarsimp simp: valid_arch_obj'_def valid_obj'_def obj_at'_def projectKOs
                            split: arch_kernel_object.splits)
    apply (rename_tac asid reply', case_tac asid, simp)
   apply (rename_tac pte reply', case_tac pte; simp add: valid_mapping'_def)
  apply (rename_tac pde reply', case_tac pde; simp add: valid_mapping'_def)
  done

end

lemma valid_obj'_ep_update:
  "\<lbrakk> valid_objs' s; valid_ep' ep s; ep_at' epPtr s; ksPSpace s x = Some obj\<rbrakk>
       \<Longrightarrow> valid_obj' obj (s\<lparr>ksPSpace := ksPSpace s(epPtr \<mapsto> KOEndpoint ep)\<rparr>)"
  apply (rule valid_objsE', simp, simp)
  apply (clarsimp simp: valid_obj'_def obj_at'_def projectKOs)
  by (cases obj;
      clarsimp simp: typ_at'_same_type valid_obj'_def obj_at'_def ps_clear_upd
                     valid_ntfn'_def  valid_bound_obj'_def valid_reply'_def valid_cte'_def
                     valid_sched_context'_def objBits_simps projectKOs valid_cap'_ep_update
                     valid_arch_obj'_ep_update valid_ep'_ep_update valid_tcb'_ep_update
              split: endpoint.splits ntfn.splits option.splits)
      fastforce+

lemma valid_obj'_reply_update:
  "\<lbrakk> valid_objs' s; valid_reply' reply s; reply_at' rptr s; ksPSpace s x = Some obj \<rbrakk>
     \<Longrightarrow> valid_obj' obj (s\<lparr>ksPSpace := ksPSpace s(rptr \<mapsto> KOReply reply)\<rparr>)"
  apply (rule valid_objsE', simp, simp)
  apply (cases obj; clarsimp simp: valid_obj'_def)
        apply (fastforce simp: valid_ep'_def obj_at'_def projectKOs split: endpoint.split)
       apply (fastforce simp: valid_bound_obj'_def valid_ntfn'_def obj_at'_def projectKOs
                       split: ntfn.splits option.split)
      apply (fastforce simp: valid_bound_obj'_def valid_tcb'_def valid_tcb_state'_reply_update
                             valid_cap'_reply_update obj_at'_def projectKOs tcb_cte_cases_def
                      split: option.split)
     apply (fastforce simp: valid_cap'_reply_update obj_at'_def valid_cte'_def projectKOs)
    apply (fastforce simp: valid_arch_obj'_reply_update obj_at'_def projectKOs)
   apply (fastforce simp: valid_sched_context'_def valid_bound_obj'_def
                          obj_at'_def projectKOs objBitsKO_def
                   split: option.split)
  apply (fastforce simp: valid_reply'_def valid_bound_obj'_def obj_at'_def projectKOs objBitsKO_def
                  split: option.split)
  done

lemma valid_objs'_ep_update:
  "\<lbrakk> valid_objs' s; valid_ep' ep s; ep_at' epPtr s \<rbrakk>
     \<Longrightarrow> valid_objs' (s\<lparr>ksPSpace := ksPSpace s(epPtr \<mapsto> KOEndpoint ep)\<rparr>)"
  apply (clarsimp simp: valid_objs'_def obj_at'_def projectKOs)
  apply (erule ranE)
  apply (clarsimp simp: ps_clear_upd split: if_split_asm)
   apply (fastforce simp: valid_obj'_def valid_ep'_def obj_at'_def ps_clear_upd
                          objBits_simps projectKOs
                   split: endpoint.splits)
  apply (fastforce intro!: valid_obj'_ep_update simp: valid_objs'_def obj_at'_def projectKOs)
  done

lemma valid_objs'_reply_update:
  "\<lbrakk> valid_objs' s; valid_reply' reply s; reply_at' rptr s \<rbrakk>
     \<Longrightarrow> valid_objs' (s\<lparr>ksPSpace := ksPSpace s(rptr \<mapsto> KOReply reply)\<rparr>)"
  apply (clarsimp simp: valid_objs'_def obj_at'_def projectKOs)
  apply (erule ranE)
  apply (clarsimp split: if_split_asm)
   apply (fastforce simp: valid_bound_obj'_def valid_obj'_def valid_reply'_def
                          obj_at'_def projectKOs objBitsKO_def
                   split: option.splits)
  apply (fastforce intro!: valid_obj'_reply_update simp: valid_objs'_def obj_at'_def projectKOs)
  done

lemma valid_release_queue_ksPSpace_update:
  "\<lbrakk>valid_release_queue s;
    ko_wp_at' (\<lambda>ko'. koTypeOf ko' = koTypeOf ko \<and> objBitsKO ko' = objBitsKO ko) ptr s;
    koTypeOf ko \<noteq> TCBT\<rbrakk> \<Longrightarrow>
    valid_release_queue (s\<lparr>ksPSpace := ksPSpace s(ptr \<mapsto> ko)\<rparr>)"
  by (fastforce simp: valid_release_queue_def ko_wp_at'_def obj_at'_def projectKOs ps_clear_upd)

lemma valid_release_queue'_ksPSpace_update:
  "\<lbrakk>valid_release_queue' s;
    ko_wp_at' (\<lambda>ko'. koTypeOf ko' = koTypeOf ko \<and> objBitsKO ko' = objBitsKO ko) ptr s;
    koTypeOf ko \<noteq> TCBT\<rbrakk> \<Longrightarrow>
    valid_release_queue' (s\<lparr>ksPSpace := ksPSpace s(ptr \<mapsto> ko)\<rparr>)"
  by (fastforce simp: valid_release_queue'_def ko_wp_at'_def obj_at'_def projectKOs ps_clear_upd)

lemma sym_ref_Receive_or_Reply_replyTCB':
  "\<lbrakk> sym_refs (state_refs_of' s); ko_at' tcb tp s;
     tcbState tcb = BlockedOnReceive ep pl (Some rp)
     \<or> tcbState tcb = BlockedOnReply (Some rp) \<rbrakk> \<Longrightarrow>
    \<exists>reply. ksPSpace s rp = Some (KOReply reply) \<and> replyTCB reply = Some tp"
  apply (drule (1) sym_refs_obj_atD'[rotated, where p=tp])
  apply (clarsimp simp: state_refs_of'_def projectKOs obj_at'_def)
  apply (clarsimp simp: ko_wp_at'_def)
  apply (erule disjE; clarsimp)
  apply (rename_tac koa; case_tac koa;
         simp add: get_refs_def2 ep_q_refs_of'_def ntfn_q_refs_of'_def
                   tcb_st_refs_of'_def tcb_bound_refs'_def
            split: endpoint.split_asm ntfn.split_asm thread_state.split_asm if_split_asm)+
  done

lemma sym_ref_replyTCB_Receive_or_Reply:
  "\<lbrakk> ko_at' reply rp s; sym_refs (state_refs_of' s); replyTCB reply = Some tp \<rbrakk>
   \<Longrightarrow> st_tcb_at' (\<lambda>st. (\<exists>ep pl. st = BlockedOnReceive ep pl (Some rp))
                        \<or> st = BlockedOnReply (Some rp)) tp s"
  apply (drule (1) sym_refs_obj_atD'[rotated, where p=rp])
  apply (clarsimp simp: state_refs_of'_def projectKOs pred_tcb_at'_def obj_at'_def)
  apply (clarsimp simp: ko_wp_at'_def)
  apply (rename_tac tcb; case_tac tcb;
         simp add: get_refs_def2 ntfn_q_refs_of'_def
                   tcb_st_refs_of'_def tcb_bound_refs'_def
            split: ntfn.split_asm thread_state.split_asm)+
  done

lemma sym_ref_BlockedOnSend_SendEP':
  "\<lbrakk> sym_refs (state_refs_of' s); st_tcb_at' ((=) (BlockedOnSend eptr p1 p2 p3 p4)) tp s\<rbrakk>
      \<Longrightarrow> \<exists>list. ko_wp_at' ((=) (KOEndpoint (SendEP list))) eptr s"
  apply (simp add: pred_tcb_at'_def)
  apply (drule (1) sym_refs_obj_atD'[rotated, where p=tp])
  apply (clarsimp simp: state_refs_of'_def projectKOs obj_at'_def)
  apply (drule sym[where s="BlockedOnSend _ _ _ _ _"])
  apply (clarsimp simp: ko_wp_at'_def)
  apply (rename_tac ko; case_tac ko;
         simp add: get_refs_def2 ep_q_refs_of'_def ntfn_q_refs_of'_def
                   tcb_st_refs_of'_def tcb_bound_refs'_def
            split: endpoint.split_asm ntfn.split_asm thread_state.split_asm if_split_asm)+
  done

lemma sym_ref_BlockedOnReceive_RecvEP':
  "\<lbrakk> sym_refs (state_refs_of' s); st_tcb_at' ((=) (BlockedOnReceive eptr pl ropt)) tp s\<rbrakk>
     \<Longrightarrow> \<exists>list. ko_wp_at' ((=) (KOEndpoint (RecvEP list))) eptr s"
  apply (simp add: pred_tcb_at'_def)
  apply (drule (1) sym_refs_obj_atD'[rotated, where p=tp])
  apply (clarsimp simp: state_refs_of'_def projectKOs obj_at'_def)
  apply (drule sym[where s="BlockedOnReceive _ _ _"])
  apply (clarsimp simp: ko_wp_at'_def split: if_split_asm)
   apply (rename_tac ko koa; case_tac ko;
          simp add: get_refs_def2 ep_q_refs_of'_def ntfn_q_refs_of'_def
                    tcb_st_refs_of'_def tcb_bound_refs'_def
             split: endpoint.split_asm ntfn.split_asm thread_state.split_asm if_split_asm)
  apply (rename_tac ko; case_tac ko;
         simp add: get_refs_def2 ep_q_refs_of'_def ntfn_q_refs_of'_def
                   tcb_st_refs_of'_def tcb_bound_refs'_def
            split: endpoint.split_asm ntfn.split_asm thread_state.split_asm if_split_asm)
  done

lemma Receive_or_Send_ep_at':
  "\<lbrakk> st = BlockedOnReceive epPtr pl rp \<or> st = BlockedOnSend epPtr p1 p2 p3 p4;
     valid_objs' s; st_tcb_at' ((=) st) t s\<rbrakk>
       \<Longrightarrow> ep_at' epPtr s"
  apply (drule (1) tcb_in_valid_state')
  by (fastforce simp: obj_at'_def valid_tcb_state'_def)

lemma ep_queued_st_tcb_at':
  "\<And>P. \<lbrakk>ko_at' ep ptr s; \<exists>rt. (t, rt) \<in> ep_q_refs_of' ep;
         valid_objs' s; sym_refs (state_refs_of' s);
         \<And>bo bbadge bgrant breply bcall r. P (Structures_H.BlockedOnSend bo bbadge bgrant breply bcall) \<and>
                         P (Structures_H.BlockedOnReceive bo bgrant r) \<rbrakk>
    \<Longrightarrow> st_tcb_at' P t s"
  apply (case_tac ep, simp_all)
  apply (frule(1) sym_refs_ko_atD', clarsimp, erule (1) my_BallE,
         clarsimp simp: pred_tcb_at'_def refs_of_rev' obj_at'_def ko_wp_at'_def projectKOs)+
  done

(* cross lemmas *)

context begin interpretation Arch . (*FIXME: arch_split*)

lemma pspace_aligned_cross:
  "\<lbrakk> pspace_aligned s; pspace_relation (kheap s) (ksPSpace s') \<rbrakk> \<Longrightarrow> pspace_aligned' s'"
  apply (clarsimp simp: pspace_aligned'_def pspace_aligned_def pspace_relation_def)
  apply (rename_tac p' ko')
  apply (prop_tac "p' \<in> pspace_dom (kheap s)", fastforce)
  apply (thin_tac "pspace_dom k = p" for k p)
  apply (clarsimp simp: pspace_dom_def)
  apply (drule bspec, fastforce)+
  apply clarsimp
  apply (rename_tac ko' a a' P ko)
  apply (erule (1) obj_relation_cutsE; clarsimp simp: objBits_simps)

  \<comment>\<open>CNode\<close>
     apply (clarsimp simp: cte_map_def)
     apply (simp only: cteSizeBits_def cte_level_bits_def)
     apply (rule is_aligned_add)
      apply (erule is_aligned_weaken, simp)
     apply (rule is_aligned_weaken)
    apply (rule is_aligned_mult_triv2, simp)

  \<comment>\<open>SchedContext, Reply\<close>
     apply ((clarsimp simp: minSchedContextBits_def min_sched_context_bits_def replySizeBits_def
                            scBits_inverse_sc_relation[simplified]
                     elim!: is_aligned_weaken)+)[2]

  \<comment>\<open>PageTable\<close>
   apply (clarsimp simp: archObjSize_def pteBits_def)
    apply (rule is_aligned_add)
     apply (erule is_aligned_weaken)
     apply simp
    apply (rule is_aligned_shift)

  \<comment>\<open>PageDirectory\<close>
   apply (clarsimp simp: archObjSize_def pdeBits_def)
    apply (rule is_aligned_add)
     apply (erule is_aligned_weaken, simp)
    apply (rule is_aligned_shift)

  \<comment>\<open>DataPage\<close>
   apply (rule is_aligned_add)
    apply (erule is_aligned_weaken)
    apply (clarsimp simp: pageBits_def pageBitsForSize_def)
    apply (case_tac sz; simp)
  apply (rule is_aligned_mult_triv2)

  \<comment>\<open>other_obj_relation\<close>
  apply (simp add: other_obj_relation_def)
  by (clarsimp simp: bit_simps' tcbBlockSizeBits_def epSizeBits_def ntfnSizeBits_def
              split: kernel_object.splits Structures_A.kernel_object.splits)
     (fastforce simp: archObjSize_def split: arch_kernel_object.splits arch_kernel_obj.splits)

lemma pspace_distinct_cross:
  "\<lbrakk> pspace_distinct s; pspace_aligned s; pspace_relation (kheap s) (ksPSpace s') \<rbrakk> \<Longrightarrow>
   pspace_distinct' s'"
  apply (frule (1) pspace_aligned_cross)
  apply (clarsimp simp: pspace_distinct'_def)
  apply (rename_tac p' ko')
  apply (rule pspace_dom_relatedE; assumption?)
  apply (rename_tac p ko P)
  apply (frule (1) pspace_alignedD')
  apply (frule (1) pspace_alignedD)
  apply (rule ps_clearI, assumption)
   apply (case_tac ko'; simp add: objBits_simps objBits_defs bit_simps' scBits_pos_power2)
   apply (clarsimp split: arch_kernel_object.splits simp: bit_simps' archObjSize_def)
  apply (rule ccontr, clarsimp)
  apply (rename_tac x' ko_x')
  apply (frule_tac x=x' in pspace_alignedD', assumption)
  apply (rule_tac x=x' in pspace_dom_relatedE; assumption?)
  apply (rename_tac x ko_x P')
  apply (frule_tac p=x in pspace_alignedD, assumption)
  apply (case_tac "p = x")
   apply clarsimp
   apply (erule (1) obj_relation_cutsE; clarsimp)
      apply (clarsimp simp: cte_relation_def cte_map_def objBits_simps)
      apply (rule_tac n=cteSizeBits in is_aligned_add_step_le'; assumption?)
     apply (clarsimp simp: pte_relation_def objBits_simps archObjSize_def)
     apply (rule_tac n=pteBits in is_aligned_add_step_le'; assumption?)
     apply (clarsimp simp: pde_relation_def objBits_simps archObjSize_def)
     apply (rule_tac n=pdeBits in is_aligned_add_step_le'; assumption?)
    apply (simp add: objBitsKO_Data)
    apply (rule_tac n=pageBits in is_aligned_add_step_le'; assumption?)
   apply (case_tac ko;
          simp split: if_split_asm
                 add: is_other_obj_relation_type_CapTable
                      is_other_obj_relation_type_SchedContext
                      is_other_obj_relation_type_Reply
                      a_type_def)
   apply (rename_tac ako,
          case_tac ako;
          simp add: is_other_obj_relation_type_def a_type_def split: if_split_asm)
  apply (frule (1) obj_relation_cuts_obj_bits)
  apply (drule (2) obj_relation_cuts_range_mask_range)+
  apply (prop_tac "x' \<in> mask_range p' (objBitsKO ko')", simp add: mask_def add_diff_eq)
  apply (frule_tac x=p and y=x in pspace_distinctD; assumption?)
  apply (drule (4) mask_range_subsetD)
  apply (erule (2) in_empty_interE)
  done

lemma aligned'_distinct'_ko_at'I:
  "\<lbrakk>ksPSpace s' x = Some ko;  pspace_aligned' s'; pspace_distinct' s';
    ko = injectKO (v:: 'a :: pspace_storable)\<rbrakk>
      \<Longrightarrow> ko_at' v x s'"
  apply (simp add: obj_at'_def projectKOs project_inject
                   pspace_distinct'_def pspace_aligned'_def)
  apply (drule bspec, erule domI)+
  apply simp
  done

lemma aligned_distinct_ko_at'I:
  assumes p: "pspace_relation (kheap s) (ksPSpace s')"
  assumes ps: "pspace_aligned s" "pspace_distinct s"
  shows "\<lbrakk>ksPSpace s' x = Some ko; ko = injectKO (v:: 'a :: pspace_storable)\<rbrakk>
      \<Longrightarrow> ko_at' v x s'"
  apply (rule aligned'_distinct'_ko_at'I[OF _ pspace_aligned_cross[OF ps(1) p]]; simp)
  using assms by (fastforce dest!: pspace_distinct_cross)

lemma tcb_at_cross:
  assumes p: "pspace_relation (kheap s) (ksPSpace s')"
  assumes aligned: "pspace_aligned s"
  assumes distinct: "pspace_distinct s"
  assumes t: "tcb_at t s"
  shows "tcb_at' t s'" using assms
  apply (clarsimp simp: obj_at_def is_tcb)
  apply (drule (1) pspace_relation_absD, clarsimp simp: other_obj_relation_def)
  apply (case_tac z; simp)
  by (fastforce dest!: aligned_distinct_ko_at'I[where 'a=tcb] elim: obj_at'_weakenE)

lemma st_tcb_at_coerce_abstract:
  assumes t: "st_tcb_at' P t c"
  assumes sr: "(a, c) \<in> state_relation"
  shows "st_tcb_at (\<lambda>st. \<exists>st'. thread_state_relation st st' \<and> P st') t a"
  using assms
  apply (clarsimp simp: state_relation_def pred_tcb_at'_def obj_at'_def
                        projectKOs)
  apply (erule (1) pspace_dom_relatedE)
  apply (erule (1) obj_relation_cutsE, simp_all)
  apply (clarsimp simp: st_tcb_at_def obj_at_def other_obj_relation_def
                        tcb_relation_def
                 split: Structures_A.kernel_object.split_asm if_split_asm
                        arch_kernel_obj.split_asm)+
  apply fastforce
  done

lemma st_tcb_at_coerce_concrete:
  assumes t: "st_tcb_at P t s"
  assumes sr: "(s, s') \<in> state_relation" "pspace_aligned s" "pspace_distinct s"
  shows "st_tcb_at' (\<lambda>st'. \<exists>st. thread_state_relation st st' \<and> P st) t s'"
  using assms
  apply (clarsimp simp: state_relation_def pred_tcb_at_def obj_at_def projectKOs)
  apply (frule (1) pspace_distinct_cross, fastforce simp: state_relation_def)
  apply (frule pspace_aligned_cross, fastforce simp: state_relation_def)
  apply (prop_tac "tcb_at t s", clarsimp simp: st_tcb_at_def obj_at_def is_tcb)
  apply (drule (2) tcb_at_cross[rotated], fastforce simp: state_relation_def)
  apply (clarsimp simp: state_relation_def pred_tcb_at'_def obj_at'_def projectKOs)
  apply (erule (1) pspace_dom_relatedE)
  apply (erule (1) obj_relation_cutsE, simp_all)
   apply (clarsimp simp: st_tcb_at'_def obj_at'_def other_obj_relation_def tcb_relation_def
                  split: Structures_A.kernel_object.split_asm if_split_asm)+
  apply fastforce
  done

lemma st_tcb_at_runnable_cross:
  "\<lbrakk> st_tcb_at runnable t s; pspace_aligned s; pspace_distinct s; (s, s') \<in> state_relation \<rbrakk>
       \<Longrightarrow> st_tcb_at' runnable' t s'"
  apply (drule (3) st_tcb_at_coerce_concrete)
  by (clarsimp simp: pred_tcb_at'_def obj_at'_def sts_rel_runnable)

lemma cur_tcb_cross:
  "\<lbrakk> cur_tcb s; pspace_aligned s; pspace_distinct s; (s,s') \<in> state_relation \<rbrakk> \<Longrightarrow> cur_tcb' s'"
  apply (clarsimp simp: cur_tcb'_def cur_tcb_def state_relation_def)
  apply (erule (3) tcb_at_cross)
  done

lemma reply_at_cross:
  assumes p: "pspace_relation (kheap s) (ksPSpace s')"
  assumes ps: "pspace_aligned s" "pspace_distinct s"
  assumes t: "reply_at ptr s"
  shows "reply_at' ptr s'"
  using assms
  apply (clarsimp simp: obj_at_def is_reply)
  apply (drule (1) pspace_relation_absD, clarsimp)
  apply (case_tac z; simp)
  by (fastforce dest!: aligned_distinct_ko_at'I[where 'a=reply] elim: obj_at'_weakenE)

lemma ep_at_cross:
  assumes p: "pspace_relation (kheap s) (ksPSpace s')"
  assumes ps: "pspace_aligned s" "pspace_distinct s"
  assumes t: "ep_at ptr s"
  shows "ep_at' ptr s'"
  using assms
  apply (clarsimp simp: obj_at_def is_ep)
  apply (drule (1) pspace_relation_absD, clarsimp simp: other_obj_relation_def)
  apply (case_tac z; simp)
  by (fastforce dest!: aligned_distinct_ko_at'I[where 'a=endpoint] elim: obj_at'_weakenE)

lemma ntfn_at_cross:
  assumes p: "pspace_relation (kheap s) (ksPSpace s')"
  assumes ps: "pspace_aligned s" "pspace_distinct s"
  assumes t: "ntfn_at ptr s"
  shows "ntfn_at' ptr s'"
  using assms
  apply (clarsimp simp: obj_at_def is_ntfn)
  apply (drule (1) pspace_relation_absD, clarsimp simp: other_obj_relation_def)
  apply (case_tac z; simp)
  by (fastforce dest!: aligned_distinct_ko_at'I[where 'a=notification] elim: obj_at'_weakenE)

lemma sc_at_cross:
  assumes p: "pspace_relation (kheap s) (ksPSpace s')"
  assumes ps: "pspace_aligned s" "pspace_distinct s"
  assumes t: "sc_at ptr s"
  shows "sc_at' ptr s'"
  using assms
  apply (clarsimp simp: obj_at_def is_sc_obj)
  apply (drule (1) pspace_relation_absD, clarsimp)
  apply (case_tac z; simp)
  by (fastforce dest!: aligned_distinct_ko_at'I[where 'a=sched_context] elim: obj_at'_weakenE)

lemma sc_at'_cross_rel:
  "cross_rel (pspace_aligned and pspace_distinct and sc_at t) (sc_at' t)"
  unfolding cross_rel_def state_relation_def
  apply clarsimp
  by (erule (3) sc_at_cross)

lemma sc_obj_at_cross:
  assumes p: "pspace_relation (kheap s) (ksPSpace s')"
  assumes ps: "pspace_aligned s" "pspace_distinct s"
  assumes t: "sc_obj_at n ptr s"
  shows "obj_at' (\<lambda>sc::sched_context. objBits sc = minSchedContextBits + n) ptr s'"
  using assms
  apply (clarsimp simp: obj_at_def is_sc_obj)
  apply (drule (1) pspace_relation_absD, clarsimp)
  apply (case_tac z; simp)
  apply (rename_tac sc')
  apply (drule (3) aligned_distinct_ko_at'I[where 'a=sched_context], simp)
  by (clarsimp simp: scBits_simps objBits_simps sc_relation_def obj_at'_def)

lemma real_cte_at_cross:
  assumes p: "pspace_relation (kheap s) (ksPSpace s')"
  assumes ps: "pspace_aligned s" "pspace_distinct s"
  assumes t: "real_cte_at ptr s"
  shows "real_cte_at' (cte_map ptr) s'"
  using assms
  apply (clarsimp simp: obj_at_def is_ntfn)
  apply (drule (1) pspace_relation_absD)
  apply (clarsimp simp: is_cap_table other_obj_relation_def well_formed_cnode_n_def)
  apply (prop_tac "\<exists>z. ksPSpace s' (cte_map (fst ptr, snd ptr)) = Some z \<and>
    cte_relation (snd ptr) (CNode (length (snd ptr)) cs) z")
  apply fastforce
  apply (clarsimp split: kernel_object.split_asm simp: cte_relation_def)
  by (fastforce dest!: aligned_distinct_ko_at'I[where 'a=cte] elim: obj_at'_weakenE)

lemma valid_tcb_state_cross:
  assumes "pspace_relation (kheap s) (ksPSpace s')"
          "thread_state_relation ts ts'"
          "pspace_aligned s"
          "pspace_distinct s"
          "valid_tcb_state ts s"
  shows "valid_tcb_state' ts' s'" using assms
  by (fastforce dest: ep_at_cross reply_at_cross ntfn_at_cross
                simp: valid_bound_obj'_def valid_tcb_state_def valid_tcb_state'_def
               split: Structures_A.thread_state.split_asm option.split_asm)

lemma state_refs_of_cross_eq:
  "\<lbrakk>(s, s') \<in> state_relation; pspace_aligned s; pspace_distinct s\<rbrakk>
       \<Longrightarrow> state_refs_of' s' = state_refs_of s"
  apply (rule sym)
  apply (rule ext, rename_tac p)
  apply (frule state_relation_pspace_relation)
  apply (frule (2) pspace_distinct_cross)
  apply (frule (1) pspace_aligned_cross)
  apply (clarsimp simp: state_refs_of_def state_refs_of'_def
                 split: option.split)
  apply (rule conjI; clarsimp)
   apply (rename_tac ko')
   apply (erule (1) pspace_dom_relatedE)
   apply (rename_tac ko P; case_tac ko; clarsimp split: if_split_asm simp: cte_relation_def)
   apply (rename_tac ako; case_tac ako; clarsimp simp: pte_relation_def pde_relation_def)
  apply (rule conjI; clarsimp)
   apply (drule (1) pspace_relation_None; clarsimp)
  apply (rule conjI[rotated]; clarsimp)
   apply (frule pspace_alignedD'; clarsimp dest!: pspace_distinctD')
  apply (rename_tac ko ko')
  apply (frule (1) pspace_relation_absD)
  apply (case_tac ko; clarsimp split: if_split_asm)
        apply (rename_tac n sz, drule_tac x=p and y="cte_relation (replicate n False)" in spec2)
        apply (fastforce simp: cte_relation_def cte_map_def well_formed_cnode_n_def)
       apply (find_goal \<open>match premises in "_ = Some (ArchObj _)" \<Rightarrow> -\<close>)
       apply (rename_tac ako; case_tac ako; simp)
          apply (case_tac ko'; clarsimp simp: other_obj_relation_def)
         apply ((drule_tac x=0 in spec, clarsimp simp:  pte_relation_def pde_relation_def)+)[2]
       apply (drule_tac x=p in spec, clarsimp)
       apply (rename_tac b sz)
       apply (drule_tac x="\<lambda>_ obj. obj = (if b then KOUserDataDevice else KOUserData)" in spec, clarsimp)
       apply (simp only: imp_ex)
       apply (drule_tac x=0 in spec, clarsimp simp: pageBitsForSize_def pageBits_def split: vmpage_size.split_asm)
      apply (all \<open>case_tac ko'; clarsimp simp: other_obj_relation_def\<close>)
      apply (rename_tac tcb tcb';
             clarsimp simp: tcb_relation_def arch_tcb_relation_def fault_rel_optionation_def
                            thread_state_relation_def tcb_st_refs_of_def tcb_st_refs_of'_def;
             rename_tac tcb'; case_tac "tcb_state tcb"; case_tac "tcbState tcb'";
             clarsimp simp: tcb_bound_refs'_def get_refs_def2 split: option.splits)
     apply (clarsimp simp: ep_q_refs_of_def ep_relation_def split: Structures_A.endpoint.splits)
    apply (clarsimp simp: ntfn_q_refs_of_def ntfn_relation_def split: Structures_A.ntfn.splits)
   apply (clarsimp simp: sc_relation_def get_refs_def2)
   apply (drule state_relation_sc_replies_relation)
   apply (frule sc_replies_relation_scReplies_of)
     apply (fastforce simp: obj_at_def is_sc_obj_def)
    apply (clarsimp simp: opt_map_def)
   apply (clarsimp simp: opt_map_def sc_replies_of_scs_def map_project_def scs_of_kh_def sc_of_def)
  apply (clarsimp simp: reply_relation_def split: Structures_A.ntfn.splits)
  done

end

method add_sym_refs =
  rule_tac Q="(\<lambda>s. sym_refs (state_refs_of' s))" in corres_cross_add_guard
  , (frule invs_sym_refs)?, (frule invs_psp_aligned)?, (frule invs_distinct)?
  , fastforce dest: state_refs_of_cross_eq

lemma state_refs_of_cross:
  "\<lbrakk>P (state_refs_of s); (s, s') \<in> state_relation; pspace_aligned s; pspace_distinct s\<rbrakk>
      \<Longrightarrow> P (state_refs_of' s')"
  by (clarsimp simp: state_refs_of_cross_eq elim!: rsubst[where P=P])

lemma ready_qs_runnable_cross:
  "\<lbrakk>(s, s') \<in> state_relation; pspace_aligned s; pspace_distinct s; valid_ready_qs s\<rbrakk>
   \<Longrightarrow> ready_qs_runnable s'"
  unfolding ready_qs_runnable_def
  by (fastforce simp: state_relation_def ready_queues_relation_def
                      in_ready_q_def st_tcb_at_runnable_cross
                dest: valid_ready_qs_in_ready_qD)

method add_ready_qs_runnable =
  rule_tac Q=ready_qs_runnable
        in corres_cross_add_guard
  , (clarsimp simp: pred_conj_def)?
  , (frule valid_sched_valid_ready_qs)?, (frule invs_psp_aligned)?, (frule invs_distinct)?
  , fastforce dest: ready_qs_runnable_cross

lemma replyTCBs_of_cross:
  "\<lbrakk>(s, s') \<in> state_relation; reply_tcb_reply_at P rptr s\<rbrakk>
   \<Longrightarrow> P (replyTCBs_of s' rptr)"
  apply (clarsimp simp: reply_at_ppred_def obj_at_def state_relation_def)
  apply (drule (1) pspace_relation_absD, clarsimp simp: other_obj_relation_def)
  apply (case_tac z; simp)
  apply (clarsimp simp: opt_map_def reply_relation_def)
  done

lemma replySCs_of_cross:
  "\<lbrakk>(s, s') \<in> state_relation; reply_sc_reply_at P rptr s\<rbrakk>
   \<Longrightarrow> P (replySCs_of s' rptr)"
  apply (clarsimp simp: reply_at_ppred_def obj_at_def is_tcb state_relation_def)
  apply (drule (1) pspace_relation_absD, clarsimp simp: other_obj_relation_def)
  apply (case_tac z; simp)
  apply (clarsimp simp: opt_map_def reply_relation_def)
  done

lemma valid_replies_sc_cross:
  "\<lbrakk>(s, s') \<in> state_relation; valid_replies s; sym_refs (state_refs_of s);
    pspace_aligned s; pspace_distinct s; reply_at rptr s\<rbrakk>
   \<Longrightarrow> valid_replies'_sc_asrt rptr s'"
  apply (clarsimp simp: valid_replies_defs valid_replies'_sc_asrt_def)
  apply (rename_tac scptr rp ko)
  apply (prop_tac "sc_replies_sc_at (\<lambda>rs. rptr \<in> set rs) scptr s")
   apply (frule_tac sc_ptr=scptr and reply_ptr=rptr in sym_refs_sc_replies_sc_at)
    apply (rule ccontr)
    apply (drule not_sk_obj_at_pred)
     apply (fastforce simp: sk_obj_at_pred_def obj_at_def is_obj_defs)
    apply (frule (1) replySCs_of_cross)
    apply (clarsimp simp: obj_at'_def projectKOs opt_map_def)
   apply (clarsimp simp: sc_at_pred_n_eq_commute sc_at_ppred_def obj_at_def)
  apply (drule subsetD, force)
  apply (clarsimp simp: pred_tcb_at_eq_commute[symmetric])
  apply (frule (1) st_tcb_reply_state_refs)
  apply (drule (3) st_tcb_at_coerce_concrete)
  apply (drule replyTCBs_of_cross[where P="\<lambda>rtcb. rtcb = (Some tptr)" for tptr])
   apply (fastforce simp: sk_obj_at_pred_def2)
  apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
  done

method add_valid_replies for rptr uses simp =
  rule_tac Q="\<lambda>s. valid_replies'_sc_asrt rptr s" in corres_cross_add_guard
  , fastforce elim: valid_replies_sc_cross simp: simp

lemma getCurThread_sp:
  "\<lbrace>P\<rbrace> getCurThread \<lbrace>\<lambda>rv. P and (\<lambda>s. rv = ksCurThread s)\<rbrace>"
  by (wpsimp simp: getCurThread_def)

lemma getSchedulerAction_sp:
  "\<lbrace>P\<rbrace> getSchedulerAction \<lbrace>\<lambda>rv. P and (\<lambda>s. rv = ksSchedulerAction s)\<rbrace>"
  by (wpsimp simp: getSchedulerAction_def)

lemma getReprogramTimer_sp:
  "\<lbrace>P\<rbrace> getReprogramTimer \<lbrace>\<lambda>rv. P and (\<lambda>s. rv = ksReprogramTimer s)\<rbrace>"
  by (wpsimp simp: getReprogramTimer_def)

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

lemma getReleaseQueue_wp[wp]:
  "\<lbrace>\<lambda>s. P (ksReleaseQueue s) s\<rbrace> getReleaseQueue \<lbrace>P\<rbrace>"
  unfolding getReleaseQueue_def
  by wpsimp

lemma getObject_sc_wp:
  "\<lbrace>\<lambda>s. sc_at' p s \<longrightarrow> (\<exists>t::sched_context. ko_at' t p s \<and> Q t s)\<rbrace> getObject p \<lbrace>Q\<rbrace>"
  by (clarsimp simp: getObject_def valid_def in_monad
                     split_def objBits_simps' loadObject_default_def
                     projectKOs obj_at'_def in_magnitude_check
              dest!: readObject_misc_ko_at')

lemma getRefillNext_getSchedContext:
  "getRefillNext scPtr index = do sc \<leftarrow> getSchedContext scPtr;
                                  return $ if index = scRefillMax sc - 1 then 0 else index + 1
                               od"
  apply (clarsimp simp: getRefillNext_def readRefillNext_def readSchedContext_def
                        getSchedContext_def getObject_def[symmetric])
  done

lemma getRefillNext_wp:
  "\<lbrace>\<lambda>s. \<forall>ko. ko_at' ko scPtr s \<longrightarrow> P (if index = scRefillMax ko - Suc 0 then 0 else index + 1) s\<rbrace>
   getRefillNext scPtr index
   \<lbrace>P\<rbrace>"
  apply (simp add: getRefillNext_getSchedContext)
  apply (wpsimp wp: getObject_sc_wp)
  done

lemma getRefillSize_def2:
  "getRefillSize scPtr = liftM scRefillCount (gets_the (readSchedContext scPtr))"
  apply (clarsimp simp: getRefillSize_def readRefillSize_def liftM_def oliftM_def)
  done

lemma getRefillSize_wp:
  "\<lbrace>\<lambda>s. \<forall>ko. ko_at' ko scp s \<longrightarrow> P (scRefillCount ko) s\<rbrace> getRefillSize scp \<lbrace>P\<rbrace>"
  apply (clarsimp simp: getRefillSize_def2)
  apply (wpsimp wp: simp: readSchedContext_def)
  done

lemma refillEmpty_wp:
  "\<lbrace>\<lambda>s. \<forall>ko. ko_at' ko scp s \<longrightarrow> P (scRefillCount ko = 0) s\<rbrace> refillEmpty scp \<lbrace>P\<rbrace>"
  unfolding refillEmpty_def
  by (wpsimp wp:)

lemma refillFull_wp:
  "\<lbrace>\<lambda>s. \<forall>ko. ko_at' ko scp s \<longrightarrow> P (scRefillCount ko = scRefillMax ko) s\<rbrace> refillFull scp \<lbrace>P\<rbrace>"
  unfolding refillFull_def
  by (wpsimp wp:)

lemma no_ofail_readCurTime[simp]:
  "no_ofail \<top> readCurTime"
  unfolding readCurTime_def by clarsimp

lemma ovalid_readCurTime[wp]:
  "o\<lbrace>\<lambda>s. P (ksCurTime s) s\<rbrace> readCurTime \<lbrace>\<lambda>r s. P r s \<and> r = ksCurTime s\<rbrace>"
  by (simp add: readCurTime_def asks_def obind_def ovalid_def)

lemma ovalid_readRefillReady[rule_format, simp]:
  "ovalid (\<lambda>s. \<forall>ko. ko_at' ko scp s \<longrightarrow> P (rTime (refillHd ko) \<le> ksCurTime s + kernelWCETTicks) s)
              (readRefillReady scp) P"
  unfolding readRefillReady_def readSchedContext_def ovalid_def
  by (fastforce simp: obind_def split: option.split_asm
                dest: use_ovalid[OF ovalid_readCurTime]
               dest!: readObject_misc_ko_at')


lemma refillReady_wp:
  "\<lbrace>\<lambda>s. \<forall>ko. ko_at' ko scp s \<longrightarrow> P (rTime (refillHd ko) \<le> ksCurTime s + kernelWCETTicks) s\<rbrace> refillReady scp \<lbrace>P\<rbrace>"
  unfolding refillReady_def
  by wpsimp (drule use_ovalid[OF ovalid_readRefillReady])

lemma scActive_wp:
  "\<lbrace>\<lambda>s. \<forall>ko. ko_at' ko scp s \<longrightarrow> P (0 < scRefillMax ko) s\<rbrace> scActive scp \<lbrace>P\<rbrace>"
  unfolding scActive_def
  by wpsimp

lemma getRefills_wp:
  "\<lbrace>\<lambda>s. \<forall>ko. ko_at' ko scp s \<longrightarrow> P (scRefills ko) s\<rbrace>
   getRefills scp
   \<lbrace>P\<rbrace>"
  unfolding getRefills_def
  by wpsimp

lemma refillSufficient_wp:
  "\<lbrace>\<lambda>s. \<forall>ko. ko_at' ko scp s \<longrightarrow> P (minBudget \<le> refillsCapacity k (scRefills ko) (scRefillHead ko)) s\<rbrace> refillSufficient scp k \<lbrace>P\<rbrace>"
  unfolding refillSufficient_def
  apply (wpsimp wp: getRefills_wp)
  by (clarsimp simp: sufficientRefills_def obj_at'_def)

(* projection rewrites *)

lemma pred_map_rewrite:
  "pred_map P proj = opt_pred P proj"
  by (fastforce simp: pred_map_def2)

abbreviation sc_of2 :: "Structures_A.kernel_object \<rightharpoonup> Structures_A.sched_context" where
  "sc_of2 ko \<equiv> case ko of kernel_object.SchedContext sc n \<Rightarrow> Some sc | _ \<Rightarrow> None"

abbreviation scs_of2 :: "'z state \<Rightarrow> obj_ref \<rightharpoonup> Structures_A.sched_context" where
  "scs_of2 \<equiv> (\<lambda>s. kheap s |> sc_of2)"

lemma scs_of_rewrite:
  "scs_of s = scs_of2 s"
  by (fastforce simp: sc_heap_of_state_def sc_of_def opt_map_def
              split: option.splits Structures_A.kernel_object.splits)

abbreviation
  "sc_replies_of2 s \<equiv> scs_of2 s ||> sc_replies"

lemma sc_replies_of_rewrite:
  "sc_replies_of s = sc_replies_of2 s"
  by (fastforce simp: sc_heap_of_state_def sc_replies_of_scs_def sc_of_def opt_map_def map_project_def
              split: option.splits Structures_A.kernel_object.splits)

definition
  sc_replies_relation2_2 ::
  "(obj_ref \<rightharpoonup> obj_ref list) \<Rightarrow> (obj_ref \<rightharpoonup> obj_ref) \<Rightarrow> (obj_ref \<rightharpoonup> obj_ref) \<Rightarrow> bool" where
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

(* end : projection rewrites *)

(* updateSchedContext *)

context begin interpretation Arch . (*FIXME: arch_split*)

lemma state_relation_sc_update:
  assumes
      R1: "\<forall>s s'. (s, s') \<in> state_relation \<longrightarrow>
         P s \<longrightarrow> P' s' \<longrightarrow> sc_at ptr s \<longrightarrow> sc_at' ptr s' \<longrightarrow>
           (\<forall>n. (((\<lambda>ko. obj_bits ko = min_sched_context_bits + n) |< kheap s) ptr) \<longrightarrow>
           sc_relation (the ((scs_of2 s ||> f) ptr)) n (the ((scs_of' s' ||> f') ptr)))"
  and R2: "\<forall>s s'. (s, s') \<in> state_relation \<longrightarrow>
         P s \<longrightarrow> P' s' \<longrightarrow> sc_at ptr s \<longrightarrow> sc_at' ptr s' \<longrightarrow>
           heap_ls (replyPrevs_of s')  (scReply (the ((scs_of' s' ||> f') ptr)))
             (sc_replies (the ((scs_of2 s ||> f) ptr)))"
  and sz: "\<forall>sc'::sched_context. objBits sc' = objBits (f' sc')"
  shows
  "\<lbrakk>(s, s') \<in> state_relation; P s; P' s'; sc_at ptr s; sc_at' ptr s'\<rbrakk> \<Longrightarrow>
     (kheap_update (\<lambda>hp p. if p = ptr
                           then
                             case hp ptr of
                                Some (kernel_object.SchedContext sc n)
                                   \<Rightarrow> Some (kernel_object.SchedContext (f sc) n)
                               | _ \<Rightarrow> hp ptr
                           else hp p) s,
     (ksPSpace_update (\<lambda>hp' p. if p = ptr
                               then case hp' ptr of
                                  Some (KOSchedContext sc')
                                     \<Rightarrow> Some (KOSchedContext (f' sc'))
                                 | _ \<Rightarrow> hp' ptr
                                else hp' p)) s') \<in> state_relation"
  supply pred_map_rewrite[simp] scs_of_rewrite[simp] opt_map_left_Some[simp]
         sc_replies_of_rewrite[simplified, simp]
  proof -
  have z': "\<And>s. sc_at' ptr s
               \<Longrightarrow> \<forall>sc'::sched_context. map_to_ctes ((\<lambda>hp' p. if p = ptr then case hp' ptr of
                              Some (KOSchedContext sc') \<Rightarrow> Some (KOSchedContext (f' sc'))
                            | _ \<Rightarrow> hp' ptr else hp' p) (ksPSpace s)) = map_to_ctes (ksPSpace s)"
    by (clarsimp simp: obj_at_simps fun_upd_def[symmetric])
  have z: "\<And>s sc'::sched_context. ko_at' sc' ptr s
               \<Longrightarrow> map_to_ctes (ksPSpace s(ptr \<mapsto> KOSchedContext (f' sc'))) = map_to_ctes (ksPSpace s)"
    by (clarsimp simp: obj_at_simps)
  have S: "\<And>(v::'a::pspace_storable). (1 :: word32) < 2 ^ (objBits v)"
    by (clarsimp simp: obj_at_simps objBits_defs pteBits_def pdeBits_def scBits_pos_power2
                split: kernel_object.splits arch_kernel_object.splits)
  assume H: "(s, s') \<in> state_relation" "P s" "P' s'" "sc_at ptr s" "sc_at' ptr s'"
  show ?thesis
    using H S sz
  apply -
    apply (insert R1[rule_format, OF H]
                  R2[rule_format, OF H])
    apply (clarsimp simp: state_relation_def)
    apply (clarsimp simp: obj_at_def is_sc_obj)
    apply (drule_tac x=n in meta_spec, clarsimp)
    apply (prop_tac "obj_at (same_caps (kernel_object.SchedContext _ n)) ptr s")
     apply (clarsimp simp: obj_at_def obj_bits_def)
    apply (clarsimp simp: obj_at'_def projectKOs fun_upd_def[symmetric]
                          z[simplified obj_at'_def projectKO_eq projectKO_opts_defs])
    apply (rename_tac n sc sc')
    apply (rule conjI)
     (* pspace_relation *)
     apply (simp only: pspace_relation_def simp_thms
                       pspace_dom_update[where x="kernel_object.SchedContext _ _"
                                           and v="kernel_object.SchedContext _ _",
                                         simplified a_type_def, simplified])
     apply (simp only: dom_fun_upd2 simp_thms)
     apply (elim conjE)
     apply (frule bspec, erule domI)
     apply (rule ballI, drule(1) bspec)
     apply (drule domD)
     apply (clarsimp simp: project_inject
                    split: if_split_asm kernel_object.split_asm)
     apply (drule_tac x=sc' in spec)
     apply (rename_tac bb aa ba)
     apply (drule_tac x="(aa, ba)" in bspec, simp)
     apply (clarsimp simp: objBits_def)
     apply (frule_tac ko'="kernel_object.SchedContext sc n" and x'=ptr in obj_relation_cut_same_type)
        apply simp+
     apply (erule obj_relation_cutsE)
            apply ((simp split: if_split_asm)+)[8]
    (* sc_replies_relation *)
    apply (frule (2) sc_replies_relation_prevs_list[simplified])
    apply (subst replyPrevs_of_non_reply_update[simplified]; (simp add: typ_at'_def ko_wp_at'_def)?)
    apply (simp add: sc_replies_relation_def)
    apply (rule conjI)
     (* ghost relation *)
     apply (clarsimp simp add: ghost_relation_def)
     apply (erule_tac x=ptr in allE)+
     apply (clarsimp simp: obj_at_def a_type_def is_sc_obj
                     split: Structures_A.kernel_object.splits if_split_asm)
    apply (rule conjI)
     (* cdt_relation *)
     apply (clarsimp simp add: cte_wp_at_cases cdt_relation_def)
    (* revokable_relation *)
    apply (prop_tac "kheap_update
                      (\<lambda>hp x.
                          if x = ptr
                          then case hp ptr of None \<Rightarrow> hp ptr
                               | Some (kernel_object.SchedContext sc n) \<Rightarrow>
                                   Some (kernel_object.SchedContext (f sc) n)
                               | Some _ \<Rightarrow> hp ptr
                          else hp x) s
             = s\<lparr> kheap := (kheap s)(ptr \<mapsto> kernel_object.SchedContext (f sc) n)\<rparr>" )
     apply (clarsimp simp: fun_upd_def)
    apply (simp only: fun_upd_def)
    apply (simp add: caps_of_state_after_update)
    done
qed

(* update wp rules without ko_at' *)
lemma updateSchedContext_wp:
  "\<lbrace> \<lambda>s. sc_at' sc_ptr s \<longrightarrow>
       Q (s\<lparr>ksPSpace := ksPSpace s(sc_ptr \<mapsto> KOSchedContext (f' (the (scs_of' s sc_ptr))))\<rparr>) \<rbrace>
   updateSchedContext sc_ptr f'
   \<lbrace> \<lambda>rv. Q \<rbrace>"
  by (wpsimp simp: updateSchedContext_def wp: set_sc'.set_wp)
     (clarsimp simp: obj_at'_def projectKOs opt_map_left_Some elim!: rsubst[where P=Q])

lemma no_fail_setSchedContext[wp]:
  "no_fail (sc_at' ptr and (\<lambda>s'. ((\<lambda>k::sched_context. objBits k = objBits new) |< scs_of' s') ptr)) (setSchedContext ptr new)"
  unfolding setSchedContext_def by (wpsimp simp: opt_map_def obj_at'_def projectKOs)

lemma no_fail_updateSchedContext[wp]:
  "no_fail (sc_at' ptr and (\<lambda>s'. ((\<lambda>k::sched_context. objBits k = objBits (f k)) |< scs_of' s') ptr))
         (updateSchedContext ptr f)"
  by (wpsimp simp: updateSchedContext_def obj_at'_def projectKOs opt_map_def)

lemma update_sched_context_rewrite:
  "monadic_rewrite False True (sc_obj_at n scp)
    (update_sched_context scp f)
      (do sc \<leftarrow> get_sched_context scp;
          set_object scp (kernel_object.SchedContext (f sc) n) od)"
  apply (clarsimp simp: update_sched_context_def get_sched_context_def bind_assoc)
  apply (rule monadic_rewrite_bind_tail)
   defer
   apply (rule get_object_sp)
  apply (case_tac obj; clarsimp simp: monadic_rewrite_refl3 set_object_def)
  apply (rule monadic_rewrite_bind_tail)
   defer
   apply (rule get_object_sp)
  apply (clarsimp simp: monadic_rewrite_def obj_at_def is_sc_obj_def)
  done

lemma updateSchedContext_corres_gen:
  assumes
      R1: "\<forall>s s'. (s, s') \<in> state_relation \<longrightarrow>
           P s \<longrightarrow> P' s' \<longrightarrow> sc_at ptr s \<longrightarrow> sc_at' ptr s' \<longrightarrow>
           (\<forall>n. (((\<lambda>ko. obj_bits ko = min_sched_context_bits + n) |< kheap s) ptr)\<longrightarrow>
           sc_relation (the ((scs_of2 s ||> f) ptr)) n (the ((scs_of' s' ||> f') ptr)))"
  and R2: "\<forall>s s'. (s, s') \<in> state_relation \<longrightarrow>
          P s \<longrightarrow> P' s' \<longrightarrow> sc_at ptr s \<longrightarrow> sc_at' ptr s' \<longrightarrow>
           heap_ls (replyPrevs_of s')  (scReply (the ((scs_of' s' ||> f') ptr)))
             (sc_replies (the ((scs_of2 s ||> f) ptr)))"
  and sz: "\<forall>sc'::sched_context. objBits sc' = objBits (f' sc')"
  shows "corres dc
         (sc_at ptr and P)
         (sc_at' ptr and P')
            (update_sched_context ptr f)
            (updateSchedContext ptr f')"
  unfolding corres_underlying_def using sz
  apply clarsimp
  apply (rename_tac s s')
  apply (drule obj_at_ko_at)
  apply (drule obj_at_ko_at')
  apply (clarsimp simp: is_sc_obj)
  apply (rename_tac sc' n sc)
  apply (rule conjI, clarsimp)
   apply (erule use_valid[OF _ updateSchedContext_wp])
   apply clarsimp
   apply (rule_tac x="((), s\<lparr>kheap := kheap s(ptr \<mapsto>
                  kernel_object.SchedContext (f sc) n)\<rparr>)" in bexI)
    apply clarsimp
    apply (drule state_relation_sc_update[OF R1 R2 sz, simplified])
      apply ((fastforce simp: obj_at_def is_sc_obj obj_at'_def projectKOs)+)[4]
    apply (clarsimp simp: obj_at_def obj_at'_def projectKOs fun_upd_def[symmetric] opt_map_left_Some)
    apply (case_tac s; case_tac s'; fastforce)
   apply (clarsimp simp: update_sched_context_def obj_at_def in_monad
                         get_object_def set_object_def a_type_def)
  apply (clarsimp intro!: no_failD[OF no_fail_updateSchedContext]
                    simp: obj_at'_def projectKOs opt_map_def)
  done

lemmas updateSchedContext_corres = updateSchedContext_corres_gen[where P=\<top> and P'=\<top>, simplified]

(* end : updateSchedContext *)

end

lemma get_sched_context_exs_valid:
  "\<exists>sc n. kheap s scp = Some (Structures_A.SchedContext sc n)
   \<Longrightarrow> \<lbrace>(=) s\<rbrace> get_sched_context scp \<exists>\<lbrace>\<lambda>_. (=) s\<rbrace>"
  by (clarsimp simp: get_sched_context_def get_object_def obj_at_def bind_def is_sc_obj_def
                     gets_def get_def return_def exs_valid_def gets_the_def
              split: Structures_A.kernel_object.splits)

lemma no_fail_simple_ko_at:
  "no_fail (ntfn_at p) (get_notification p)"
  "no_fail (ep_at p) (get_endpoint p)"
  "no_fail (reply_at p) (get_reply p)"
  by (wpsimp simp: get_simple_ko_def obj_at_def is_obj_defs a_type_def partial_inv_def
               wp: get_object_wp split:  Structures_A.kernel_object.splits)+

lemmas no_fail_get_notification[wp] = no_fail_simple_ko_at(1)
lemmas no_fail_get_reply[wp] = no_fail_simple_ko_at(2)
lemmas no_fail_get_endpoint[wp] = no_fail_simple_ko_at(3)

lemma get_sched_context_no_fail:
  "no_fail (\<lambda>s. sc_at ptr s) (get_sched_context ptr)"
  by (clarsimp simp: get_sched_context_def no_fail_def bind_def get_object_def return_def get_def
                     gets_def obj_at_def is_sc_obj_def gets_the_def
              split: Structures_A.kernel_object.splits)

(* FIXME RT: rename *)
(* this let us cross the sc size information from concrete to abstract *)
lemma ko_at'_cross:
  assumes p: "pspace_relation (kheap s) (ksPSpace s')"
  assumes t: "ko_at' (sc'::sched_context) ptr s'"
  shows "sc_obj_at (objBits sc' - minSchedContextBits) ptr s" using assms
  apply (clarsimp simp: obj_at'_def projectKOs)
  apply (erule (1) pspace_dom_relatedE)
  by (clarsimp simp: obj_relation_cuts_def2 obj_at_def is_sc_obj cte_relation_def
                     other_obj_relation_def pte_relation_def pde_relation_def
                     scBits_simps sc_relation_def objBits_simps
              split: Structures_A.kernel_object.split_asm if_split_asm
                     ARM_A.arch_kernel_obj.split_asm)

lemma update_sc_no_reply_stack_update_ko_at'_corres:
  assumes x: "\<And>sc n. sc_relation sc n sc' \<longrightarrow> sc_relation (f sc) n (f' sc')"
  assumes y: "\<And>sc. sc_replies sc = sc_replies (f sc)"
  assumes z: "objBits sc' = objBits (f' sc')"
  assumes r: "scReply sc' = scReply (f' sc')"
  shows
    "corres dc (sc_at ptr) (ko_at' sc' ptr)
            (update_sched_context ptr f)
            (setSchedContext ptr (f' sc'))"
  unfolding update_sched_context_def
  apply (rule corres_guard_imp)
    apply (rule corres_symb_exec_l'[where Q'="\<lambda>r s. ko_at r ptr s \<and> (\<exists>n. is_sc_obj n r)",
                                    where P="\<lambda>s. obj_at \<top> ptr s"])
      apply (rule corres_guard_imp[where P'=R and Q'=R for R])
        apply (rule_tac F="(\<exists>n. is_sc_obj n obj)" in corres_gen_asm)
        apply (case_tac obj; simp add: is_sc_obj_def)
        apply (rule setSchedContext_no_stack_update_corres[where f'=f'])
           apply (clarsimp simp: x obj_at_def intro!: y z r)+
     apply (fastforce simp: exs_valid_def get_object_def in_monad)
    apply (wpsimp wp: get_object_wp)
   apply (fastforce simp: obj_at_def)
  apply simp
  done

lemma update_sc_no_reply_stack_update_corres:
  "\<lbrakk>\<forall>sc n sc'. sc_relation sc n sc' \<longrightarrow> sc_relation (f sc) n (f' sc');
    \<forall>sc. sc_replies sc = sc_replies (f sc); \<forall>sc'. objBits sc' = objBits (f' sc');
    \<forall>sc'. scReply (f' sc') = scReply sc' \<rbrakk> \<Longrightarrow>
   corres dc (sc_at ptr and pspace_aligned and pspace_distinct) \<top>
          (update_sched_context ptr f)
         (do sc' <- getSchedContext ptr;
             setSchedContext ptr (f' sc')
          od)"
  apply (rule_tac Q="sc_at' ptr" in corres_cross_add_guard)
   apply (fastforce dest!: state_relationD sc_at_cross simp: obj_at'_def)
  apply (rule corres_symb_exec_r)
     apply (rule corres_guard1_imp)
      apply (rule update_sc_no_reply_stack_update_ko_at'_corres; simp)
     apply clarsimp
    apply (wpsimp wp: get_sched_context_exs_valid simp: is_sc_obj_def obj_at_def)
   apply (rename_tac ko; case_tac ko; simp)
   apply (wpsimp simp: obj_at_def is_sc_obj_def)+
  done

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
      apply (clarsimp split: Structures_H.endpoint.splits simp: ep_q_refs_of'_def)
     apply (clarsimp split: Structures_H.ntfn.splits option.splits
                      simp: ntfn_q_refs_of'_def get_refs_def)
    apply (clarsimp simp: tcb_st_refs_of'_def tcb_bound_refs'_def get_refs_def
                   split: Structures_H.thread_state.splits if_splits option.splits)
   apply (clarsimp simp: get_refs_def split: option.splits)
  apply (clarsimp simp: get_refs_def split: option.splits)
  done

lemma reply_at'_cross_rel:
  "cross_rel (pspace_aligned and pspace_distinct and reply_at t) (reply_at' t)"
  unfolding cross_rel_def state_relation_def
  apply clarsimp
  by (erule (3) reply_at_cross)

lemma sch_act_simple_cross_rel:
  "cross_rel simple_sched_action sch_act_simple"
  apply (clarsimp simp: cross_rel_def)
  by (fastforce simp: simple_sched_action_def sch_act_simple_def
                dest: state_relation_sched_act_relation
               split: Structures_A.scheduler_action.splits)

(* FIXME RT: move to Corres_UL.thy *)
lemma cross_relF:
  "(s, s') \<in> state_relation \<Longrightarrow> cross_rel A B \<Longrightarrow> A s \<Longrightarrow> B s'"
  by (clarsimp simp: cross_rel_def)

lemma valid_tcb_state'_simps[simp]:
  "valid_tcb_state' Running = \<top>"
  "valid_tcb_state' Inactive = \<top>"
  "valid_tcb_state' Restart = \<top>"
  "valid_tcb_state' IdleThreadState = \<top>"
  "valid_tcb_state' (BlockedOnSend ref b c d e) = ep_at' ref"
  "valid_tcb_state' (BlockedOnReply r) = valid_bound_reply' r"
  by (rule ext, simp add: valid_tcb_state'_def)+

lemma tcb_at'_ex1_ko_at':
  "tcb_at' t s \<Longrightarrow> \<exists>!tcb. ko_at' (tcb::tcb) t s"
  by (clarsimp simp: obj_at'_def)

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
  by (intro iffI; clarsimp simp: obj_at'_real_def ko_wp_at'_def projectKOs opt_map_def)+

lemma not_idle_scTCB:
  "\<lbrakk>sym_heap_tcbSCs s; valid_objs' s; valid_idle' s; p \<noteq> idle_sc_ptr; sc_at' p s\<rbrakk> \<Longrightarrow>
   obj_at' (\<lambda>x. scTCB x \<noteq> Some idle_thread_ptr) p s"
  apply (subgoal_tac "\<not>obj_at' (\<lambda>x. scTCB x = Some idle_thread_ptr) p s")
   apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def)
  apply (subst (asm) sym_heap_symmetric)
  apply (clarsimp simp: obj_at'_sc_tcbs_of_equiv sym_heap_def)
  apply (clarsimp simp: valid_idle'_def obj_at'_real_def ko_wp_at'_def idle_tcb'_def projectKOs)
  done

lemma not_idle_tcbSC:
  "\<lbrakk>sym_heap_tcbSCs s; valid_objs' s; valid_idle' s; p \<noteq> idle_thread_ptr; tcb_at' p s\<rbrakk> \<Longrightarrow>
   obj_at' (\<lambda>x. tcbSchedContext x \<noteq> Some idle_sc_ptr) p s"
  apply (subgoal_tac "\<not>obj_at' (\<lambda>x. tcbSchedContext x = Some idle_sc_ptr) p s")
   apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def)
  apply (clarsimp simp: obj_at'_tcb_scs_of_equiv sym_heap_def)
  apply (clarsimp simp: valid_idle'_def obj_at'_real_def ko_wp_at'_def idle_tcb'_def projectKOs)
  done

lemma setObject_tcb_tcbs_of':
  "\<lbrace>\<lambda>s. P' ((tcbs_of' s)(c \<mapsto> tcb))\<rbrace>
  setObject c (tcb::tcb)
  \<lbrace>\<lambda>_ s. P' (tcbs_of' s)\<rbrace>"
  by (setObject_easy_cases, clarsimp simp: ARM_H.fromPPtr_def)

lemma setObject_other_tcbs_of'[wp]:
  "setObject c (r::reply) \<lbrace>\<lambda>s. P' (tcbs_of' s)\<rbrace>"
  "setObject c (e::endpoint) \<lbrace>\<lambda>s. P' (tcbs_of' s)\<rbrace>"
  "setObject c (n::notification) \<lbrace>\<lambda>s. P' (tcbs_of' s)\<rbrace>"
  "setObject c (sc::sched_context) \<lbrace>\<lambda>s. P' (tcbs_of' s)\<rbrace>"
  by setObject_easy_cases+

lemma setObject_cte_tcbSCs_of[wp]:
  "setObject c (reply::cte) \<lbrace>\<lambda>s. P' (tcbSCs_of s)\<rbrace>"
  by setObject_easy_cases

lemma threadSet_tcbSCs_of_inv:
  "\<forall>x. tcbSchedContext (f x) = tcbSchedContext x \<Longrightarrow>
  threadSet f t \<lbrace>\<lambda>s. P (tcbSCs_of s)\<rbrace>"
  unfolding threadSet_def
  apply (rule hoare_seq_ext[OF _ get_tcb_sp'])
  apply (wpsimp wp: setObject_tcb_tcbs_of')
  apply (erule subst[where P=P, rotated], rule ext)
  apply (clarsimp simp: opt_map_def obj_at'_real_def ko_wp_at'_def projectKO_tcb
                 split: option.splits)
  done

lemma aligned'_distinct'_obj_at'I:
  "\<lbrakk> \<exists>y. ksPSpace s p = Some (injectKO (y:: 'a::pspace_storable)); pspace_aligned' s; pspace_distinct' s\<rbrakk>
   \<Longrightarrow> obj_at' (\<top> :: 'a::pspace_storable \<Rightarrow> bool) p s"
  apply (clarsimp)
  apply (frule (2) aligned'_distinct'_ko_at'I, simp)
  apply (clarsimp simp: obj_at'_def)
  done

(* FIXME RT: maybe move? *)
lemma prod_in_refsD:
  "\<And>ref x y. (x, ref) \<in> ep_q_refs_of' y \<Longrightarrow> ref \<in> {EPRecv, EPSend}"
  "\<And>ref x y. (x, ref) \<in> ntfn_q_refs_of' y \<Longrightarrow> ref \<in> {NTFNSignal}"
  "\<And>ref x y. (x, ref) \<in> tcb_st_refs_of' y \<Longrightarrow> ref \<in> {TCBBlockedRecv, TCBReply, TCBSignal, TCBBlockedSend}"
  "\<And>ref x a b c. (x, ref) \<in> tcb_bound_refs' a b c \<Longrightarrow> ref \<in> {TCBBound, TCBSchedContext, TCBYieldTo}"
  apply (rename_tac ep; case_tac ep; simp)
  apply (rename_tac ep; case_tac ep; simp)
  apply (rename_tac ep; case_tac ep; clarsimp split: if_splits)
  apply (clarsimp simp: tcb_bound_refs'_def get_refs_def2)
  done

lemma sym_refs_tcbSCs:
  "\<lbrakk>sym_refs (state_refs_of' s); pspace_aligned' s; pspace_distinct' s\<rbrakk>
   \<Longrightarrow> sym_heap_tcbSCs s"
  apply (clarsimp simp: sym_heap_def)
  apply (rule iffI)
   apply (drule_tac tp=SCTcb and x=p and y=p' in sym_refsE;
          force simp: get_refs_def2 state_refs_of'_def projectKOs opt_map_left_Some refs_of_rev'
                dest: pspace_alignedD' pspace_distinctD' split: if_split_asm option.split_asm)+
  by (drule_tac tp=TCBSchedContext and x=p' and y=p in sym_refsE;
      force simp: get_refs_def2 state_refs_of'_def projectKOs opt_map_left_Some refs_of_rev'
               dest: pspace_alignedD' pspace_distinctD' split: if_split_asm option.split_asm)+

lemma sym_refs_scReplies:
  "\<lbrakk>sym_refs (state_refs_of' s); pspace_aligned' s; pspace_distinct' s\<rbrakk>
   \<Longrightarrow> sym_heap_scReplies s"
  apply (clarsimp simp: sym_heap_def)
  apply (rule iffI)
   apply (drule_tac tp=ReplySchedContext and x=p and y=p' in sym_refsE;
          force simp: get_refs_def2 state_refs_of'_def projectKOs opt_map_left_Some refs_of_rev'
                dest: pspace_alignedD' pspace_distinctD' split: if_split_asm option.split_asm)+
  by (drule_tac tp=SCReply and x=p' and y=p in sym_refsE;
      force simp: get_refs_def2 state_refs_of'_def projectKOs opt_map_left_Some refs_of_rev'
               dest: pspace_alignedD' pspace_distinctD' split: if_split_asm option.split_asm)+

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

lemma getObject_tcb_wp:
  "\<lbrace>\<lambda>s. tcb_at' p s \<longrightarrow> (\<exists>t::tcb. ko_at' t p s \<and> Q t s)\<rbrace> getObject p \<lbrace>Q\<rbrace>"
  by (clarsimp simp: getObject_def valid_def in_monad
                     split_def objBits_simps' loadObject_default_def
                     projectKOs obj_at'_def in_magnitude_check
              dest!: readObject_misc_ko_at')


lemma threadSet_tcbSCs_of:
  "\<lbrace>\<lambda>s. P (\<lambda>a. if a = t then tcbSchedContext (f (the (tcbs_of' s a))) else tcbSCs_of s a)\<rbrace>
   threadSet f t
   \<lbrace>\<lambda>_ s. P (tcbSCs_of s)\<rbrace>"
  unfolding threadSet_def
  apply (wpsimp wp: setObject_tcb_wp getObject_tcb_wp)
  apply (clarsimp simp: tcb_at'_ex_eq_all)
  apply (erule back_subst[where P=P], rule ext)
  apply (clarsimp simp: opt_map_def obj_at'_real_def ko_wp_at'_def projectKOs)
  done

lemma shows
  replyNexts_Some_replySCs_None:
  "replyNexts_of s rp \<noteq> None \<Longrightarrow> replySCs_of s rp = None" and
  replySCs_Some_replyNexts_None:
  "replySCs_of s rp \<noteq> None \<Longrightarrow> replyNexts_of s rp = None"
  by (clarsimp simp: opt_map_def projectKOs split: option.splits reply_next.splits)+

lemma sym_heap_remove_only:
  "\<lbrakk> sym_heap h1 h2; h2 y = Some x \<rbrakk> \<Longrightarrow>
   sym_heap (\<lambda>a. if a = x then None else h1 a) (\<lambda>a. if a = y then None else h2 a)"
  supply opt_mapE [rule del]
  apply (clarsimp simp: sym_heap_def)
  apply (subst (asm) sym_heap_symmetric[simplified sym_heap_def], simp)
  done

lemma pred_tcb_at'_equiv:
  "pred_tcb_at' p P t s = (tcb_at' t s \<and> P (p (tcb_to_itcb' (the (tcbs_of' s t)))))"
  by (rule iffI;
      clarsimp simp: pred_tcb_at'_def pred_map_def obj_at'_real_def ko_wp_at'_def projectKOs
                     opt_map_def)

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

lemma ep_at'_cross_rel:
  "cross_rel (pspace_aligned and pspace_distinct and ep_at t) (ep_at' t)"
  unfolding cross_rel_def state_relation_def
  apply clarsimp
  by (erule (3) ep_at_cross)

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
   (length (refills_map (scRefillHead sc) (scRefillCount sc) (scRefillMax sc) (scRefills sc)) = Suc 0)
    = (scRefillHead sc = refillTailIndex sc)"
  apply (clarsimp simp: valid_sched_context'_def refillTailIndex_def refills_map_def)
  apply (case_tac "scRefillCount sc = Suc 0"; simp)
  apply (auto simp: Let_def)
  done

lemma refillSingle_corres:
  "scp = scp' \<Longrightarrow>
   corres (=) (sc_at scp) (obj_at' sc_valid_refills' scp')
     (refill_single scp)
     (refillSingle scp')"
  unfolding refill_single_def refillSingle_def
  apply (simp add: refill_size_def get_refills_def)
  apply (rule stronger_corres_guard_imp)
    apply (rule_tac R'="\<lambda>sc s. sc_valid_refills' sc" and R="\<lambda>_ _ . True" in corres_split)
       apply (rule get_sc_corres)
      apply simp
      apply (metis (mono_tags, hide_lams) refillSingle_equiv sc_relation_def)
     apply wpsimp+
  apply (clarsimp simp: obj_at'_def)
  done

lemma active_sc_at'_cross:
  "\<lbrakk>(s,s') \<in> state_relation; pspace_aligned s; pspace_distinct s; is_active_sc sc_ptr s;
    sc_at sc_ptr s\<rbrakk>
   \<Longrightarrow> active_sc_at' sc_ptr s'"
  apply (frule state_relation_pspace_relation)
  apply (frule (3) sc_at_cross)
  apply (clarsimp simp: pspace_relation_def obj_at_def is_sc_obj_def)
  apply (drule_tac x=sc_ptr in bspec, blast)
  apply (clarsimp simp: sc_relation_def vs_all_heap_simps active_sc_at'_def obj_at'_def projectKOs
                        active_sc_def)
  done

end
