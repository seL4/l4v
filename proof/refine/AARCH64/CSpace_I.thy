(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
   CSpace invariants
*)

theory CSpace_I
imports ArchAcc_R
begin

context begin interpretation Arch . (*FIXME: arch-split*)

lemma capUntypedPtr_simps [simp]:
  "capUntypedPtr (ThreadCap r) = r"
  "capUntypedPtr (NotificationCap r badge a b) = r"
  "capUntypedPtr (EndpointCap r badge a b c d) = r"
  "capUntypedPtr (Zombie r bits n) = r"
  "capUntypedPtr (ArchObjectCap x) = Arch.capUntypedPtr x"
  "capUntypedPtr (UntypedCap d r n f) = r"
  "capUntypedPtr (CNodeCap r n g n2) = r"
  "capUntypedPtr (ReplyCap r m a) = r"
  "Arch.capUntypedPtr (ASIDPoolCap r asid) = r"
  "Arch.capUntypedPtr (FrameCap r rghts sz d mapdata) = r"
  "Arch.capUntypedPtr (PageTableCap r pt_t mapdata2) = r"
  "Arch.capUntypedPtr (VCPUCap r) = r"
  by (auto simp: capUntypedPtr_def AARCH64_H.capUntypedPtr_def)

lemma rights_mask_map_UNIV [simp]:
  "rights_mask_map UNIV = allRights"
  by (simp add: rights_mask_map_def allRights_def)

lemma maskCapRights_allRights [simp]:
  "maskCapRights allRights c = c"
  unfolding maskCapRights_def isCap_defs allRights_def
            AARCH64_H.maskCapRights_def maskVMRights_def
  by (cases c) (simp_all add: Let_def split: arch_capability.split vmrights.split)

lemma getCTE_inv [wp]: "\<lbrace>P\<rbrace> getCTE addr \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: getCTE_def) wp

lemma getEndpoint_inv [wp]:
  "\<lbrace>P\<rbrace> getEndpoint ptr \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: getEndpoint_def getObject_inv loadObject_default_inv)

lemma getNotification_inv [wp]:
  "\<lbrace>P\<rbrace> getNotification ptr \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: getNotification_def getObject_inv loadObject_default_inv)

lemma getSlotCap_inv [wp]: "\<lbrace>P\<rbrace> getSlotCap addr \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: getSlotCap_def, wp)

declare resolveAddressBits.simps[simp del]

lemma cap_case_CNodeCap:
  "(case cap of CNodeCap a b c d \<Rightarrow> P
         | _ \<Rightarrow> Q)
      = (if isCNodeCap cap then P else Q)"
  by (cases cap, simp_all add: isCap_simps)

lemma resolveAddressBits_inv_induct:
  shows
  "s \<turnstile> \<lbrace>P\<rbrace>
     resolveAddressBits cap cref depth
   \<lbrace>\<lambda>rv. P\<rbrace>,\<lbrace>\<lambda>rv. P\<rbrace>"
proof (induct arbitrary: s rule: resolveAddressBits.induct)
  case (1 cap fn cref depth)
  show ?case
    apply (subst resolveAddressBits.simps)
    apply (simp add: Let_def split_def cap_case_CNodeCap[unfolded isCap_simps]
               split del: if_split cong: if_cong)
    apply (rule hoare_pre_spec_validE)
     apply ((elim exE | wp (once) spec_strengthen_postE[OF "1.hyps"])+,
              (rule refl conjI | simp add: in_monad split del: if_split)+)
            apply (wp | simp add: locateSlot_conv split del: if_split
                      | wp (once) hoare_drop_imps)+
  done
qed

lemma rab_inv' [wp]:
  "\<lbrace>P\<rbrace> resolveAddressBits cap addr depth \<lbrace>\<lambda>rv. P\<rbrace>"
  by (rule validE_valid, rule use_specE', rule resolveAddressBits_inv_induct)

lemmas rab_inv'' [wp] = rab_inv' [folded resolveAddressBits_decl_def]

crunch lookupCap
  for inv[wp]: P

lemma updateObject_cte_inv:
  "\<lbrace>P\<rbrace> updateObject (cte :: cte) ko x y n \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: updateObject_cte)
  apply (cases ko, simp_all add: typeError_def unless_def
                      split del: if_split
                           cong: if_cong)
   apply (wp | simp)+
  done

definition
  "no_mdb cte \<equiv> mdbPrev (cteMDBNode cte) = 0 \<and> mdbNext (cteMDBNode cte) = 0"

lemma mdb_next_update:
  "m (x \<mapsto> y) \<turnstile> a \<leadsto> b =
  (if a = x then mdbNext (cteMDBNode y) = b else m \<turnstile> a \<leadsto> b)"
  by (simp add: mdb_next_rel_def mdb_next_def)

lemma neg_no_loopsI:
  "m \<turnstile> c \<leadsto>\<^sup>+ c \<Longrightarrow> \<not> no_loops m"
  unfolding no_loops_def by auto

lemma valid_dlistEp [elim?]:
  "\<lbrakk> valid_dlist m; m p = Some cte; mdbPrev (cteMDBNode cte) \<noteq> 0;
     \<And>cte'. \<lbrakk> m (mdbPrev (cteMDBNode cte)) = Some cte';
              mdbNext (cteMDBNode cte') = p \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow>
  P"
  unfolding valid_dlist_def Let_def by blast

lemma valid_dlistEn [elim?]:
  "\<lbrakk> valid_dlist m; m p = Some cte; mdbNext (cteMDBNode cte) \<noteq> 0;
     \<And>cte'. \<lbrakk> m (mdbNext (cteMDBNode cte)) = Some cte';
              mdbPrev (cteMDBNode cte') = p \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow>
  P"
  unfolding valid_dlist_def Let_def by blast

lemmas valid_dlistE = valid_dlistEn valid_dlistEp

lemma mdb_next_update_other:
  "\<lbrakk> m (x \<mapsto> y) \<turnstile> a \<leadsto> b; x \<noteq> a \<rbrakk> \<Longrightarrow> m \<turnstile> a \<leadsto> b"
  by (simp add: mdb_next_rel_def mdb_next_def)

lemma mdb_trancl_update_other:
  assumes  upd: "m(p \<mapsto> cte) \<turnstile> x \<leadsto>\<^sup>+ y"
  and   nopath: "\<not> m \<turnstile> x \<leadsto>\<^sup>* p"
  shows "m \<turnstile> x \<leadsto>\<^sup>+ y"
  using upd nopath
proof induct
  case (base y)

  have "m \<turnstile> x \<leadsto> y"
  proof (rule mdb_next_update_other)
    from base show "p \<noteq> x" by clarsimp
  qed fact+

  thus ?case ..
next
  case (step y z)
  hence ih: "m \<turnstile> x \<leadsto>\<^sup>+ y" by auto

  from ih show ?case
  proof
    show "m \<turnstile> y \<leadsto> z"
    proof (rule mdb_next_update_other)
      show "p \<noteq> y"
      proof (cases "x = p")
        case True thus ?thesis using step.prems by simp
      next
        case False thus ?thesis using step.prems ih
          by - (erule contrapos_nn, rule trancl_into_rtrancl, simp)
      qed
    qed fact+
  qed
qed

lemma next_unfold':
  "m \<turnstile> c \<leadsto> y = (\<exists>cte. m c = Some cte \<and> mdbNext (cteMDBNode cte) = y)"
  unfolding mdb_next_rel_def
  by (simp add: next_unfold split: option.splits)

lemma no_self_loop_next_noloop:
  assumes no_loop: "no_loops m"
  and     lup: "m ptr = Some cte"
  shows   "mdbNext (cteMDBNode cte) \<noteq> ptr"
proof -
  from no_loop have "\<not> m \<turnstile> ptr \<leadsto> ptr"
    unfolding no_loops_def
    by - (drule spec, erule contrapos_nn, erule r_into_trancl)

  thus ?thesis using lup
    by (simp add: next_unfold')
qed


lemma valid_dlistI [intro?]:
  defines "nxt \<equiv> \<lambda>cte. mdbNext (cteMDBNode cte)"
  and     "prv \<equiv> \<lambda>cte. mdbPrev (cteMDBNode cte)"
  assumes r1: "\<And>p cte. \<lbrakk> m p = Some cte; prv cte \<noteq> 0 \<rbrakk> \<Longrightarrow> \<exists>cte'. m (prv cte) = Some cte' \<and> nxt cte' = p"
  and     r2: "\<And>p cte. \<lbrakk> m p = Some cte; nxt cte \<noteq> 0 \<rbrakk> \<Longrightarrow> \<exists>cte'. m (nxt cte) = Some cte' \<and> prv cte' = p"
  shows   "valid_dlist m"
  unfolding valid_dlist_def
  by (auto dest: r1 r2 simp: Let_def prv_def nxt_def)

lemma no_loops_tranclE:
  assumes nl: "no_loops m"
  and    nxt: "m \<turnstile> x \<leadsto>\<^sup>+ y"
  shows   "\<not> m \<turnstile> y \<leadsto>\<^sup>* x"
proof
  assume "m \<turnstile> y \<leadsto>\<^sup>* x"
  hence "m \<turnstile> x \<leadsto>\<^sup>+ x" using nxt
    by simp

  thus False using nl
    unfolding no_loops_def by auto
qed

lemma neg_next_rtrancl_trancl:
  "\<lbrakk> \<not> m \<turnstile> y \<leadsto>\<^sup>* r; m \<turnstile> x \<leadsto> y \<rbrakk> \<Longrightarrow> \<not> m \<turnstile> x \<leadsto>\<^sup>+ r"
  apply (erule contrapos_nn)
  apply (drule tranclD)
  apply (clarsimp simp: next_unfold')
  done

lemma next_trancl_split_tt:
  assumes p1: "m \<turnstile> x \<leadsto>\<^sup>+ y"
  and     p2: "m \<turnstile> x \<leadsto>\<^sup>+ p"
  and     nm: "\<not> m \<turnstile> p \<leadsto>\<^sup>* y"
  shows "m \<turnstile> y \<leadsto>\<^sup>* p"
  using p2 p1 nm
proof induct
  case base thus ?case
    by (clarsimp dest!: tranclD) (drule (1)  next_single_value, simp)
next
  case (step q r)

  show ?case
  proof (cases "q = y")
    case True thus ?thesis using step
      by fastforce
  next
    case False
    have "m \<turnstile> y \<leadsto>\<^sup>* q"
    proof (rule step.hyps)
      have "\<not> m \<turnstile> q \<leadsto>\<^sup>+ y"
        by (rule neg_next_rtrancl_trancl) fact+
      thus "\<not> m \<turnstile> q \<leadsto>\<^sup>* y" using False
        by (clarsimp dest!: rtranclD)
    qed fact+
    thus ?thesis by (rule rtrancl_into_rtrancl) fact+
  qed
qed

lemma no_loops_upd_last:
  assumes noloop: "no_loops m"
  and     nxt: "m \<turnstile> x \<leadsto>\<^sup>+ p"
  shows "m (p \<mapsto> cte) \<turnstile> x \<leadsto>\<^sup>+ p"
proof -
  from noloop nxt have xp: "x \<noteq> p"
    by (clarsimp dest!: neg_no_loopsI)

  from nxt show ?thesis using xp
  proof (induct rule: converse_trancl_induct')
    case (base y)
    hence "m (p \<mapsto> cte) \<turnstile> y \<leadsto> p" using noloop
      by (auto simp add: mdb_next_update)
    thus ?case ..
  next
    case (step y z)

    from noloop step have xp: "z \<noteq> p"
      by (clarsimp dest!: neg_no_loopsI)

    hence "m (p \<mapsto> cte) \<turnstile> y \<leadsto> z" using step
      by (simp add: mdb_next_update)

    moreover from xp have "m (p \<mapsto> cte) \<turnstile> z \<leadsto>\<^sup>+ p" using step.hyps assms
      by (auto simp del: fun_upd_apply)
    ultimately show ?case by (rule trancl_into_trancl2)
  qed
qed


lemma no_0_neq [intro?]:
  "\<lbrakk>m c = Some cte; no_0 m\<rbrakk> \<Longrightarrow> c \<noteq> 0"
  by (auto simp add: no_0_def)

lemma no_0_update:
  assumes no0: "no_0 m"
  and     pnz: "p \<noteq> 0"
  shows "no_0 (m(p \<mapsto> cte))"
  using no0 pnz unfolding no_0_def by simp

lemma has_loop_update:
  assumes lp: "m(p \<mapsto> cte) \<turnstile> c \<leadsto>\<^sup>+ c'"
  and    cn0: "c' \<noteq> 0"
  and  mnext: "mdbNext (cteMDBNode cte) = 0"
  and    mn0: "no_0 m"
  and    pn0: "p \<noteq> 0"
  shows "m \<turnstile> c \<leadsto>\<^sup>+ c'"
  using lp cn0
proof induct
  case (base y)
  have "m \<turnstile> c \<leadsto> y"
  proof (rule mdb_next_update_other)
    show "p \<noteq> c" using base
      by (clarsimp intro: contrapos_nn simp: mdb_next_update mnext)
  qed fact+

  thus ?case ..
next
  case (step y z)

  show ?case
  proof
    have "y \<noteq> 0" by (rule no_0_lhs [OF _  no_0_update]) fact+
    thus "m \<turnstile> c \<leadsto>\<^sup>+ y" using step by simp
  next
    have "z \<noteq> 0" by fact+
    hence "p \<noteq> y" using step.hyps mnext
      by (clarsimp simp: mdb_next_update)
    thus "m \<turnstile> y \<leadsto> z"
      by (rule mdb_next_update_other [OF step.hyps(2)])
  qed
qed

lemma mdb_rtrancl_update_other:
  assumes  upd: "m(p \<mapsto> cte) \<turnstile> x \<leadsto>\<^sup>* y"
  and   nopath: "\<not> m \<turnstile> x \<leadsto>\<^sup>* p"
  shows "m \<turnstile> x \<leadsto>\<^sup>* y"
  using upd
proof (cases rule: next_rtrancl_tranclE)
  case eq thus ?thesis by simp
next
  case trancl thus ?thesis
    by (auto intro: trancl_into_rtrancl elim: mdb_trancl_update_other [OF _ nopath])
qed

lemma mdb_trancl_other_update:
  assumes upd: "m \<turnstile> x \<leadsto>\<^sup>+ y"
  and      np: "\<not> m \<turnstile> x \<leadsto>\<^sup>* p"
  shows   "m(p \<mapsto> cte) \<turnstile> x \<leadsto>\<^sup>+ y"
  using upd
proof induct
  case (base q)
  from np have "x \<noteq> p" by clarsimp
  hence"m (p \<mapsto> cte) \<turnstile> x \<leadsto> q"
    using base by (simp add: mdb_next_update del: fun_upd_apply)
  thus ?case ..
next
  case (step q r)

  show ?case
  proof
    from step.hyps(1) np have "q \<noteq> p"
      by (auto elim!: contrapos_nn)

    thus x: "m(p \<mapsto> cte) \<turnstile> q \<leadsto> r"
      using step by (simp add: mdb_next_update del: fun_upd_apply)
  qed fact+
qed

lemma mdb_rtrancl_other_update:
  assumes upd: "m \<turnstile> x \<leadsto>\<^sup>* y"
  and  nopath: "\<not> m \<turnstile> x \<leadsto>\<^sup>* p"
  shows   "m(p \<mapsto> cte) \<turnstile> x \<leadsto>\<^sup>* y"
  using upd
proof (cases rule: next_rtrancl_tranclE)
  case eq thus ?thesis by simp
next
  case trancl thus ?thesis
    by (auto intro: trancl_into_rtrancl elim: mdb_trancl_other_update [OF _ nopath])
qed

lemma mdb_chain_0_update:
  assumes x: "m \<turnstile> mdbNext (cteMDBNode cte) \<leadsto>\<^sup>* 0"
  and    np: "\<not> m \<turnstile> mdbNext (cteMDBNode cte) \<leadsto>\<^sup>* p"
  assumes p: "p \<noteq> 0"
  assumes 0: "no_0 m"
  assumes n: "mdb_chain_0 m"
  shows "mdb_chain_0 (m(p \<mapsto> cte))"
   unfolding mdb_chain_0_def
proof rule
  fix x
  assume "x \<in> dom (m(p \<mapsto> cte))"
  hence x: "x = p \<or> x \<in> dom m" by simp

  have cnxt: "m(p \<mapsto> cte) \<turnstile> mdbNext (cteMDBNode cte) \<leadsto>\<^sup>* 0"
    by (rule mdb_rtrancl_other_update) fact+

  from x show "m(p \<mapsto> cte) \<turnstile> x \<leadsto>\<^sup>+ 0"
  proof
    assume xp: "x = p"
    show ?thesis
    proof (rule rtrancl_into_trancl2 [OF _ cnxt])
      show "m(p \<mapsto> cte) \<turnstile> x \<leadsto> mdbNext (cteMDBNode cte)" using xp
        by (simp add: mdb_next_update)
    qed
  next
    assume x: "x \<in> dom m"

    show ?thesis
    proof (cases "m \<turnstile> x \<leadsto>\<^sup>* p")
      case False
      from n have "m \<turnstile> x \<leadsto>\<^sup>+ 0"
        unfolding mdb_chain_0_def
        using x by auto

      thus ?thesis
        by (rule mdb_trancl_other_update) fact+
    next
      case True
      hence "m(p \<mapsto> cte) \<turnstile> x \<leadsto>\<^sup>* p"
      proof (cases rule: next_rtrancl_tranclE)
        case eq thus ?thesis by simp
      next
        case trancl
        have "no_loops m" by (rule mdb_chain_0_no_loops) fact+
        thus ?thesis
          by (rule trancl_into_rtrancl [OF no_loops_upd_last]) fact+
      qed
      moreover
      have "m(p \<mapsto> cte) \<turnstile> p \<leadsto> mdbNext (cteMDBNode cte)" by (simp add: mdb_next_update)
      ultimately show ?thesis using cnxt by simp
    qed
  qed
qed

lemma mdb_chain_0_update_0:
  assumes x: "mdbNext (cteMDBNode cte) = 0"
  assumes p: "p \<noteq> 0"
  assumes 0: "no_0 m"
  assumes n: "mdb_chain_0 m"
  shows "mdb_chain_0 (m(p \<mapsto> cte))"
  using x 0 p
  apply -
  apply (rule mdb_chain_0_update [OF _ _ p 0 n])
  apply (auto elim: next_rtrancl_tranclE dest: no_0_lhs_trancl)
  done

lemma valid_badges_0_update:
  assumes nx: "mdbNext (cteMDBNode cte) = 0"
  assumes pv: "mdbPrev (cteMDBNode cte) = 0"
  assumes p: "m p = Some cte'"
  assumes m: "no_mdb cte'"
  assumes 0: "no_0 m"
  assumes d: "valid_dlist m"
  assumes v: "valid_badges m"
  shows "valid_badges (m(p \<mapsto> cte))"
proof (unfold valid_badges_def, clarify)
  fix c c' cap cap' n n'
  assume c: "(m(p \<mapsto> cte)) c = Some (CTE cap n)"
  assume c': "(m(p \<mapsto> cte)) c' = Some (CTE cap' n')"
  assume nxt: "m(p \<mapsto> cte) \<turnstile> c \<leadsto> c'"

  from p 0 have p0: "p \<noteq> 0" by (clarsimp simp: no_0_def)

  from c' p0 0
  have "c' \<noteq> 0" by (clarsimp simp: no_0_def)
  with nx nxt
  have cp: "c \<noteq> p" by (clarsimp simp add: mdb_next_unfold)
  moreover
  from pv nx nxt p p0 c d m 0
  have "c' \<noteq> p"
    apply clarsimp
    apply (simp add: mdb_next_unfold split: if_split_asm)
    apply (erule (1) valid_dlistEn, simp)
    apply (clarsimp simp: no_mdb_def no_0_def)
    done
  moreover
  with nxt c c' cp
  have "m \<turnstile> c \<leadsto> c'" by (simp add: mdb_next_unfold)
  ultimately
  show "(sameRegionAs cap cap' \<longrightarrow>
          (isEndpointCap cap \<longrightarrow>
              capEPBadge cap \<noteq> capEPBadge cap' \<longrightarrow>
              capEPBadge cap' \<noteq> 0 \<longrightarrow>
              mdbFirstBadged n') \<and>
          (isNotificationCap cap \<longrightarrow>
              capNtfnBadge cap \<noteq> capNtfnBadge cap' \<longrightarrow>
              capNtfnBadge cap' \<noteq> 0 \<longrightarrow>
              mdbFirstBadged n')) \<and>
        valid_arch_badges cap cap' n'"
    using c c' v by (fastforce simp: valid_badges_def)
qed

definition
  "caps_no_overlap' m S \<equiv>
  \<forall>p c n. m p = Some (CTE c n) \<longrightarrow> capRange c \<inter> S = {}"

definition
  fresh_virt_cap_class :: "capclass \<Rightarrow> cte_heap \<Rightarrow> bool"
where
 "fresh_virt_cap_class C m \<equiv>
    C \<noteq> PhysicalClass \<longrightarrow> C \<notin> (capClass \<circ> cteCap) ` ran m"

lemma fresh_virt_cap_class_Physical[simp]:
  "fresh_virt_cap_class PhysicalClass = \<top>"
  by (rule ext, simp add: fresh_virt_cap_class_def)+

lemma fresh_virt_cap_classD:
  "\<lbrakk> m x = Some cte; fresh_virt_cap_class C m \<rbrakk>
     \<Longrightarrow> C \<noteq> PhysicalClass \<longrightarrow> capClass (cteCap cte) \<noteq> C"
  by (auto simp: fresh_virt_cap_class_def)

lemma capRange_untyped:
  "capRange cap' \<inter> untypedRange cap \<noteq> {} \<Longrightarrow> isUntypedCap cap"
  by (cases cap, auto simp: isCap_simps)

lemma capRange_of_untyped [simp]:
  "capRange (UntypedCap d r n f) = untypedRange (UntypedCap d r n f)"
  by (simp add: capRange_def isCap_simps capUntypedSize_def)

lemma caps_contained_no_overlap:
  "\<lbrakk> caps_no_overlap' m (capRange cap); caps_contained' m\<rbrakk>
    \<Longrightarrow> caps_contained' (m(p \<mapsto> CTE cap n))"
  apply (clarsimp simp add: caps_contained'_def)
  apply (rule conjI)
   apply clarsimp
   apply (rule conjI, clarsimp dest!: capRange_untyped)
   apply clarsimp
   apply (simp add: caps_no_overlap'_def)
   apply (erule_tac x=p' in allE, erule allE, erule impE, erule exI)
   apply (frule capRange_untyped)
   apply (clarsimp simp add: isCap_simps)
  apply clarsimp
  apply (simp add: caps_no_overlap'_def)
  apply (erule_tac x=pa in allE, erule allE, erule impE, erule exI)
  apply (frule capRange_untyped)
  apply (clarsimp simp: isCap_simps)
  apply blast
  done

lemma no_mdb_next:
  "\<lbrakk> m p = Some cte; no_mdb cte; valid_dlist m; no_0 m \<rbrakk> \<Longrightarrow> \<not> m \<turnstile> x \<leadsto> p"
  apply clarsimp
  apply (frule vdlist_nextD0)
    apply clarsimp
   apply assumption
  apply (clarsimp simp: mdb_prev_def no_mdb_def mdb_next_unfold)
  done

lemma no_mdb_rtrancl:
  "\<lbrakk> m p = Some cte; no_mdb cte; p \<noteq> x; valid_dlist m; no_0 m \<rbrakk> \<Longrightarrow> \<not> m \<turnstile> x \<leadsto>\<^sup>* p"
  apply (clarsimp dest!: rtranclD)
  apply (drule tranclD2)
  apply clarsimp
  apply (drule (3) no_mdb_next)
  apply fastforce
  done

lemma isNullCap [simp]:
  "isNullCap cap = (cap = NullCap)"
  by (simp add: isCap_simps)

lemma isDomainCap [simp]:
  "isDomainCap cap = (cap = DomainCap)"
  by (simp add: isCap_simps)

lemma isPhysicalCap[simp]:
  "isPhysicalCap cap = (capClass cap = PhysicalClass)"
  by (simp add: isPhysicalCap_def AARCH64_H.isPhysicalCap_def
         split: capability.split arch_capability.split)

definition capMasterCap :: "capability \<Rightarrow> capability" where
 "capMasterCap cap \<equiv> case cap of
   EndpointCap ref bdg s r g gr \<Rightarrow> EndpointCap ref 0 True True True True
 | NotificationCap ref bdg s r \<Rightarrow> NotificationCap ref 0 True True
 | CNodeCap ref bits gd gs \<Rightarrow> CNodeCap ref bits 0 0
 | ThreadCap ref \<Rightarrow> ThreadCap ref
 | ReplyCap ref master g \<Rightarrow> ReplyCap ref True True
 | UntypedCap d ref n f \<Rightarrow> UntypedCap d ref n 0
 | ArchObjectCap acap \<Rightarrow> ArchObjectCap (case acap of
      FrameCap ref rghts sz d mapdata \<Rightarrow>
         FrameCap ref VMReadWrite sz d None
    | ASIDPoolCap pool asid \<Rightarrow>
         ASIDPoolCap pool 0
    | PageTableCap ptr pt_t data \<Rightarrow>
         PageTableCap ptr pt_t None
    | VCPUCap ptr \<Rightarrow>
         VCPUCap ptr
    | _ \<Rightarrow> acap)
 | _ \<Rightarrow> cap"

lemmas capMasterCap_simps[simp] = capMasterCap_def[split_simps capability.split arch_capability.split]

lemma capMasterCap_eqDs1:
  "capMasterCap cap = EndpointCap ref bdg s r g gr
     \<Longrightarrow> bdg = 0 \<and> s \<and> r \<and> g \<and> gr
          \<and> (\<exists>bdg s r g gr. cap = EndpointCap ref bdg s r g gr)"
  "capMasterCap cap = NotificationCap ref bdg s r
     \<Longrightarrow> bdg = 0 \<and> s \<and> r
          \<and> (\<exists>bdg s r. cap = NotificationCap ref bdg s r)"
  "capMasterCap cap = CNodeCap ref bits gd gs
     \<Longrightarrow> gd = 0 \<and> gs = 0 \<and> (\<exists>gd gs. cap = CNodeCap ref bits gd gs)"
  "capMasterCap cap = ThreadCap ref
     \<Longrightarrow> cap = ThreadCap ref"
  "capMasterCap cap = NullCap
     \<Longrightarrow> cap = NullCap"
  "capMasterCap cap = DomainCap
     \<Longrightarrow> cap = DomainCap"
  "capMasterCap cap = IRQControlCap
     \<Longrightarrow> cap = IRQControlCap"
  "capMasterCap cap = IRQHandlerCap irq
     \<Longrightarrow> cap = IRQHandlerCap irq"
  "capMasterCap cap = Zombie ref tp n
     \<Longrightarrow> cap = Zombie ref tp n"
  "capMasterCap cap = UntypedCap d ref bits 0
     \<Longrightarrow> \<exists>f. cap = UntypedCap d ref bits f"
  "capMasterCap cap = ReplyCap ref master g
     \<Longrightarrow> master \<and> g \<and> (\<exists>master g. cap = ReplyCap ref master g)"
  "capMasterCap cap = ArchObjectCap (FrameCap ref rghts sz d mapdata)
     \<Longrightarrow> rghts = VMReadWrite \<and> mapdata = None
          \<and> (\<exists>rghts mapdata. cap = ArchObjectCap (FrameCap ref rghts sz d mapdata))"
  "capMasterCap cap = ArchObjectCap ASIDControlCap
     \<Longrightarrow> cap = ArchObjectCap ASIDControlCap"
  "capMasterCap cap = ArchObjectCap (ASIDPoolCap pool asid)
     \<Longrightarrow> asid = 0 \<and> (\<exists>asid. cap = ArchObjectCap (ASIDPoolCap pool asid))"
  "capMasterCap cap = ArchObjectCap (PageTableCap ptr pt_t data)
     \<Longrightarrow> data = None \<and> (\<exists>data. cap = ArchObjectCap (PageTableCap ptr pt_t data))"
  "capMasterCap cap = ArchObjectCap (VCPUCap v)
     \<Longrightarrow> cap = ArchObjectCap (VCPUCap v)"
  "capMasterCap cap = ArchObjectCap (SGISignalCap sirq target)
     \<Longrightarrow> cap = ArchObjectCap (SGISignalCap sirq target)"
  by (clarsimp simp: capMasterCap_def
              split: capability.split_asm arch_capability.split_asm)+

lemmas capMasterCap_eqDs[dest!] = capMasterCap_eqDs1 capMasterCap_eqDs1 [OF sym]

definition
  capBadge :: "capability \<Rightarrow> machine_word option"
where
 "capBadge cap \<equiv> if isEndpointCap cap then Some (capEPBadge cap)
                 else if isNotificationCap cap then Some (capNtfnBadge cap)
                 else None"

lemma capBadge_simps[simp]:
 "capBadge (UntypedCap d p n f)               = None"
 "capBadge (NullCap)                          = None"
 "capBadge (DomainCap)                        = None"
 "capBadge (EndpointCap ref badge s r g gr)   = Some badge"
 "capBadge (NotificationCap ref badge s r)    = Some badge"
 "capBadge (CNodeCap ref bits gd gs)          = None"
 "capBadge (ThreadCap ref)                    = None"
 "capBadge (Zombie ref b n)                   = None"
 "capBadge (ArchObjectCap cap)                = None"
 "capBadge (IRQControlCap)                    = None"
 "capBadge (IRQHandlerCap irq)                = None"
 "capBadge (ReplyCap tcb master g)            = None"
  by (simp add: capBadge_def isCap_defs)+

lemma capClass_Master:
  "capClass (capMasterCap cap) = capClass cap"
  by (simp add: capMasterCap_def split: capability.split arch_capability.split)

lemma capRange_Master:
  "capRange (capMasterCap cap) = capRange cap"
  by (simp add: capMasterCap_def split: capability.split arch_capability.split,
      simp add: capRange_def)

lemma master_eqI:
  "\<lbrakk> \<And>cap. F (capMasterCap cap) = F cap; F (capMasterCap cap) = F (capMasterCap cap') \<rbrakk>
     \<Longrightarrow> F cap = F cap'"
  by simp

lemmas isArchFrameCap_simps[simp] =
  isArchFrameCap_def[split_simps capability.split arch_capability.split]

lemma isCap_Master:
  "isZombie (capMasterCap cap) = isZombie cap"
  "isArchObjectCap (capMasterCap cap) = isArchObjectCap cap"
  "isThreadCap (capMasterCap cap) = isThreadCap cap"
  "isCNodeCap (capMasterCap cap) = isCNodeCap cap"
  "isNotificationCap (capMasterCap cap) = isNotificationCap cap"
  "isEndpointCap (capMasterCap cap) = isEndpointCap cap"
  "isUntypedCap (capMasterCap cap) = isUntypedCap cap"
  "isReplyCap (capMasterCap cap) = isReplyCap cap"
  "isIRQControlCap (capMasterCap cap) = isIRQControlCap cap"
  "isIRQHandlerCap (capMasterCap cap) = isIRQHandlerCap cap"
  "isNullCap (capMasterCap cap) = isNullCap cap"
  "isDomainCap (capMasterCap cap) = isDomainCap cap"
  "isArchFrameCap (capMasterCap cap) = isArchFrameCap cap"
  "isArchObjectCap cap \<Longrightarrow> isSGISignalCap (capCap (capMasterCap cap)) = isSGISignalCap (capCap cap)"
  by (auto simp: isCap_simps capMasterCap_def
           split: capability.split arch_capability.split)

lemma capUntypedSize_capBits:
  "capClass cap = PhysicalClass \<Longrightarrow> capUntypedSize cap = 2 ^ (capBits cap)"
  apply (simp add: capUntypedSize_def objBits_simps'
                   AARCH64_H.capUntypedSize_def bit_simps'
            split: capability.splits arch_capability.splits
                   zombie_type.splits)
  apply fastforce
  done

lemma sameRegionAs_def2:
 "sameRegionAs cap cap' = (\<lambda>cap cap'.
     (cap = cap'
          \<and> (\<not> isNullCap cap \<and> \<not> isZombie cap
              \<and> \<not> isUntypedCap cap \<and> \<not> isArchFrameCap cap)
          \<and> (\<not> isNullCap cap' \<and> \<not> isZombie cap'
              \<and> \<not> isUntypedCap cap' \<and> \<not> isArchFrameCap cap'))
      \<or> (capRange cap' \<noteq> {} \<and> capRange cap' \<subseteq> capRange cap
                 \<and> (isUntypedCap cap \<or> (isArchFrameCap cap \<and> isArchFrameCap cap')))
      \<or> (isIRQControlCap cap \<and> isIRQHandlerCap cap')
      \<or> (isIRQControlCap cap \<and> isArchObjectCap cap' \<and> isSGISignalCap (capCap cap')))
           (capMasterCap cap) (capMasterCap cap')"
  apply (cases "isUntypedCap cap")
   apply (clarsimp simp: sameRegionAs_def Let_def
                         isCap_Master capRange_Master capClass_Master)
   apply (clarsimp simp: isCap_simps
                         capMasterCap_def[where cap="UntypedCap d p n f" for d p n f])
   apply (simp add: capRange_def capUntypedSize_capBits)
   apply (intro impI iffI)
    apply (clarsimp del: subsetI intro!: range_subsetI)
   apply clarsimp
  apply (simp cong: conj_cong)
  apply (simp     add: capMasterCap_def sameRegionAs_def isArchFrameCap_def
                split: capability.split
            split del: if_split cong: if_cong)
  apply (simp    add: AARCH64_H.sameRegionAs_def isCap_simps
               split: arch_capability.split
           split del: if_split cong: if_cong)
  apply (clarsimp simp: capRange_def Let_def isCap_simps)
  apply (simp add: range_subset_eq2 cong: conj_cong)
  apply (simp add: conj_comms mask_def add_diff_eq isIRQControlCapDescendant_def)
  done

lemma sameObjectAs_def2:
 "sameObjectAs cap cap' = (\<lambda>cap cap'.
     (cap = cap'
          \<and> (\<not> isNullCap cap \<and> \<not> isZombie cap \<and> \<not> isUntypedCap cap)
          \<and> (\<not> isNullCap cap' \<and> \<not> isZombie cap' \<and> \<not> isUntypedCap cap')
          \<and> (isArchFrameCap cap \<longrightarrow> capRange cap \<noteq> {})
          \<and> (isArchFrameCap cap' \<longrightarrow> capRange cap' \<noteq> {})
          \<and> \<not> isIRQControlCap cap
          \<and> \<not>isArchSGISignalCap cap))
        (capMasterCap cap) (capMasterCap cap')"
  apply (simp add: sameObjectAs_def sameRegionAs_def2
                   isCap_simps capMasterCap_def
            split: capability.split)
  apply (clarsimp simp: AARCH64_H.sameObjectAs_def isCap_simps
                 split: arch_capability.split cong: if_cong)
  apply (clarsimp simp: AARCH64_H.sameRegionAs_def isCap_simps
                  split del: if_split cong: if_cong)
  apply (simp add: capRange_def isCap_simps mask_def add_diff_eq
              split del: if_split)
  apply fastforce
  done

lemmas sameRegionAs_def3 =
  sameRegionAs_def2 [simplified capClass_Master capRange_Master isCap_Master]

lemmas sameObjectAs_def3 =
  sameObjectAs_def2 [simplified capClass_Master capRange_Master isCap_Master]

lemma sameRegionAsE:
  "\<lbrakk> sameRegionAs cap cap';
     \<lbrakk> capMasterCap cap = capMasterCap cap'; \<not> isNullCap cap; \<not> isZombie cap;
         \<not> isUntypedCap cap; \<not> isArchFrameCap cap\<rbrakk> \<Longrightarrow> R;
     \<lbrakk> capRange cap' \<noteq> {}; capRange cap' \<subseteq> capRange cap; isUntypedCap cap \<rbrakk> \<Longrightarrow> R;
     \<lbrakk> capRange cap' \<noteq> {}; capRange cap' \<subseteq> capRange cap; isArchFrameCap cap;
          isArchFrameCap cap' \<rbrakk> \<Longrightarrow> R;
     \<lbrakk> isIRQControlCap cap; isIRQHandlerCap cap' \<rbrakk> \<Longrightarrow> R;
     \<lbrakk> isIRQControlCap cap; isArchObjectCap cap'; isSGISignalCap (capCap cap') \<rbrakk> \<Longrightarrow> R
      \<rbrakk> \<Longrightarrow> R"
  by  (simp add: sameRegionAs_def3, fastforce simp: isCap_Master)

lemma sameObjectAsE:
  "\<lbrakk> sameObjectAs cap cap';
     \<lbrakk> capMasterCap cap = capMasterCap cap'; \<not> isNullCap cap; \<not> isZombie cap;
         \<not> isUntypedCap cap;
         isArchFrameCap cap \<Longrightarrow> capRange cap \<noteq> {} \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by (clarsimp simp add: sameObjectAs_def3)

lemma sameObjectAs_sameRegionAs:
  "sameObjectAs cap cap' \<Longrightarrow> sameRegionAs cap cap'"
  by (clarsimp simp add: sameObjectAs_def2 sameRegionAs_def2 isCap_simps)

lemma sameObjectAs_sym:
  "sameObjectAs c d = sameObjectAs d c"
  by (auto simp: sameObjectAs_def2)

lemma untypedRange_Master:
  "untypedRange (capMasterCap cap) = untypedRange cap"
  by (simp add: capMasterCap_def split: capability.split)

lemma sameObject_capRange:
  "sameObjectAs cap cap' \<Longrightarrow> capRange cap' = capRange cap"
  apply (rule master_eqI, rule capRange_Master)
  apply (clarsimp simp: sameObjectAs_def2)
  done

lemma sameRegionAs_Null [simp]:
  "sameRegionAs c NullCap = False"
  "sameRegionAs NullCap c = False"
  by (simp add: sameRegionAs_def3 capRange_def isCap_simps)+

lemma isMDBParent_Null [simp]:
  "isMDBParentOf c (CTE NullCap m) = False"
  "isMDBParentOf (CTE NullCap m) c = False"
  unfolding isMDBParentOf_def by (auto split: cte.splits)

lemma capUntypedSize_simps [simp]:
  "capUntypedSize (ThreadCap r) = 1 << objBits (undefined::tcb)"
  "capUntypedSize (NotificationCap r badge a b) = 1 << objBits (undefined::Structures_H.notification)"
  "capUntypedSize (EndpointCap r badge a b c d) = 1 << objBits (undefined::endpoint)"
  "capUntypedSize (Zombie r zs n) = 1 << (zBits zs)"
  "capUntypedSize NullCap = 0"
  "capUntypedSize DomainCap = 1"
  "capUntypedSize (ArchObjectCap x) = Arch.capUntypedSize x"
  "capUntypedSize (UntypedCap d r n f) = 1 << n"
  "capUntypedSize (CNodeCap r n g n2) = 1 << (objBits (undefined::cte) + n)"
  "capUntypedSize (ReplyCap r m a) = 1 << objBits (undefined :: tcb)"
  "capUntypedSize IRQControlCap = 1"
  "capUntypedSize (IRQHandlerCap irq) = 1"
  by (auto simp add: capUntypedSize_def isCap_simps objBits_simps'
              split: zombie_type.splits)

lemma sameRegionAs_classes:
  "sameRegionAs cap cap' \<Longrightarrow> capClass cap = capClass cap'"
  apply (erule sameRegionAsE)
     apply (rule master_eqI, rule capClass_Master)
     apply simp
    apply (simp add: capRange_def split: if_split_asm)
   apply (clarsimp simp: isCap_simps)+
  done

lemma capAligned_capUntypedPtr:
  "\<lbrakk> capAligned cap; capClass cap = PhysicalClass \<rbrakk> \<Longrightarrow>
   capUntypedPtr cap \<in> capRange cap"
  by (simp add: capRange_def capAligned_def is_aligned_no_overflow)

lemma sameRegionAs_capRange_Int:
  "\<lbrakk> sameRegionAs cap cap'; capClass cap = PhysicalClass \<or> capClass cap' = PhysicalClass;
     capAligned cap; capAligned cap' \<rbrakk>
     \<Longrightarrow> capRange cap' \<inter> capRange cap \<noteq> {}"
  apply (frule sameRegionAs_classes, simp)
  apply (drule(1) capAligned_capUntypedPtr)+
  apply (erule sameRegionAsE)
      apply (subgoal_tac "capRange (capMasterCap cap') \<inter> capRange (capMasterCap cap) \<noteq> {}")
       apply (simp(no_asm_use) add: capRange_Master)
      apply (clarsimp simp: capRange_Master)
     apply blast
    apply blast
   apply (clarsimp simp: isCap_simps)
  apply (clarsimp simp: isCap_simps)
  done

lemma sameRegionAs_trans:
  "\<lbrakk> sameRegionAs a b; sameRegionAs b c \<rbrakk> \<Longrightarrow> sameRegionAs a c"
  apply (simp add: sameRegionAs_def2, elim conjE disjE, simp_all)
                by (auto simp: isCap_simps capRange_def) (* long *)

lemma capMasterCap_maskCapRights[simp]:
  "capMasterCap (maskCapRights msk cap)
    = capMasterCap cap"
  apply (cases cap;
         simp add: maskCapRights_def Let_def isCap_simps capMasterCap_def)
  apply (rename_tac arch_capability)
  apply (case_tac arch_capability;
         simp add: AARCH64_H.maskCapRights_def Let_def isCap_simps)
  done

lemma capBadge_maskCapRights[simp]:
  "capBadge (maskCapRights msk cap) = capBadge cap"
  apply (cases cap;
         simp add: maskCapRights_def Let_def isCap_simps capBadge_def)
  apply (rename_tac arch_capability)
  apply (case_tac arch_capability;
         simp add: AARCH64_H.maskCapRights_def Let_def isCap_simps)
  done

lemma getObject_cte_det:
  "(r::cte,s') \<in> fst (getObject p s) \<Longrightarrow> fst (getObject p s) = {(r,s)} \<and> s' = s"
  apply (clarsimp simp add: getObject_def bind_def get_def gets_def
                            return_def loadObject_cte split_def)
  apply (clarsimp split: kernel_object.split_asm if_split_asm option.split_asm
                   simp: in_monad typeError_def alignError_def magnitudeCheck_def)
       apply (simp_all add: bind_def return_def assert_opt_def split_def
                            alignCheck_def is_aligned_mask[symmetric]
                            unless_def when_def magnitudeCheck_def)
  done

lemma cte_wp_at_obj_cases':
  "cte_wp_at' P p s =
    (obj_at' P p s \<or> (\<exists>n \<in> dom tcb_cte_cases. obj_at' (P \<circ> (fst (the (tcb_cte_cases n)))) (p - n) s))"
  apply (simp add: cte_wp_at_cases' obj_at'_def)
  apply (rule iffI)
   apply (erule disjEI
           | clarsimp simp: objBits_simps' cte_level_bits_def
           | rule rev_bexI, erule domI)+
  apply fastforce
  done

lemma cte_wp_at_valid_objs_valid_cap':
  "\<lbrakk> cte_wp_at' P p s; valid_objs' s \<rbrakk> \<Longrightarrow> \<exists>cte. P cte \<and> s \<turnstile>' (cteCap cte)"
  apply (simp add: cte_wp_at_obj_cases')
  apply (elim disjE bexE conjE)
   apply (drule(1) obj_at_valid_objs')
   apply (clarsimp simp: valid_obj'_def valid_cte'_def)
  apply (drule(1) obj_at_valid_objs')
  apply (clarsimp simp: valid_obj'_def valid_cte'_def valid_tcb'_def)
  apply (fastforce dest: bspec [OF _ ranI])
  done

lemma getCTE_valid_cap:
  "\<lbrace>valid_objs'\<rbrace> getCTE t \<lbrace>\<lambda>cte s. s \<turnstile>' (cteCap cte) \<and> cte_at' t s\<rbrace>"
  apply (clarsimp simp add: getCTE_def valid_def)
  apply (frule in_inv_by_hoareD [OF getObject_cte_inv], clarsimp)
  apply (subst conj_commute)
  apply (subgoal_tac "cte_wp_at' ((=) a) t s")
   apply (rule conjI)
    apply (clarsimp elim!: cte_wp_at_weakenE')
   apply (drule(1) cte_wp_at_valid_objs_valid_cap')
   apply clarsimp
  apply (drule getObject_cte_det)
  apply (simp add: cte_wp_at'_def)
  done

lemmas getCTE_valid_cap' [wp] =
  getCTE_valid_cap [THEN hoare_conjD1 [unfolded pred_conj_def]]

lemma ctes_of_valid_cap':
  "\<lbrakk> ctes_of s p = Some (CTE c n); valid_objs' s\<rbrakk> \<Longrightarrow> s \<turnstile>' c"
  apply (rule cte_wp_at_valid_objs_valid_cap'[where P="(=) (CTE c n)", simplified])
   apply (simp add: cte_wp_at_ctes_of)
  apply assumption
  done

lemma valid_capAligned:
  "valid_cap' c s \<Longrightarrow> capAligned c"
  by (simp add: valid_cap'_def)

lemma caps_no_overlap'_no_region:
  "\<lbrakk> caps_no_overlap' m (capRange cap); valid_objs' s;
    m = ctes_of s; s \<turnstile>' cap; fresh_virt_cap_class (capClass cap) m \<rbrakk> \<Longrightarrow>
  \<forall>c n p. m p = Some (CTE c n) \<longrightarrow>
         \<not> sameRegionAs c cap \<and> \<not> sameRegionAs cap c"
  apply (clarsimp simp add: caps_no_overlap'_def)
  apply (erule allE)+
  apply (erule impE, erule exI)
  apply (frule (1) ctes_of_valid_cap')
  apply (drule valid_capAligned)+
  apply (case_tac "capClass cap = PhysicalClass")
   apply (auto dest: sameRegionAs_capRange_Int)[1]
  apply (drule(1) fresh_virt_cap_classD)
  apply (auto dest: sameRegionAs_classes)
  done

definition
 "initMDBNode \<equiv> MDB nullPointer nullPointer True True"

lemma init_next [simp]:
  "mdbNext initMDBNode = 0"
  by (simp add: initMDBNode_def nullPointer_def)

lemma init_prev [simp]:
  "mdbPrev initMDBNode = 0"
  by (simp add: initMDBNode_def nullPointer_def)

lemma mdb_chunked_init:
  assumes x: "m x = Some cte"
  assumes no_m: "no_mdb cte"
  assumes no_c: "caps_no_overlap' m (capRange cap)"
  assumes no_v: "fresh_virt_cap_class (capClass cap) m"
  assumes no_0: "no_0 m"
  assumes dlist: "valid_dlist m"
  assumes chain: "mdb_chain_0 m"
  assumes chunked: "mdb_chunked m"
  assumes valid: "valid_objs' s" "m = ctes_of s" "s \<turnstile>' cap"
  shows "mdb_chunked (m(x \<mapsto> CTE cap initMDBNode))"
  unfolding mdb_chunked_def
proof clarify
  fix p p' c c' n n'
  define m' where "m' \<equiv> m (x \<mapsto> CTE cap initMDBNode)"
  assume p: "m' p = Some (CTE c n)"
  assume p': "m' p' = Some (CTE c' n')"
  assume r: "sameRegionAs c c'"
  assume neq: "p \<noteq> p'"
  assume arch_assm: "mdb_chunked_arch_assms c"

  note no_region = caps_no_overlap'_no_region [OF no_c valid no_v]

  from chain x no_0
  have chain': "mdb_chain_0 m'"
    unfolding m'_def
    apply -
    apply (rule mdb_chain_0_update, clarsimp)
       apply clarsimp
       apply (drule rtranclD)
       apply (erule disjE, clarsimp)
       apply clarsimp
       apply (drule tranclD)
       apply (clarsimp simp: mdb_next_unfold)
      apply clarsimp
     apply assumption
    apply assumption
    done
  moreover
  from x no_0
  have x0 [simp]: "x \<noteq> 0" by clarsimp
  with no_0
  have "no_0 m'"
    unfolding m'_def
    by (rule no_0_update)
  ultimately
  have nl: "no_loops m'" by (rule mdb_chain_0_no_loops)

  from p p' r neq no_region
  have px: "p \<noteq> x"
    by (clarsimp simp: m'_def) blast
  moreover
  from p p' r neq no_region
  have p'x: "p' \<noteq> x"
    by (clarsimp simp: m'_def) blast
  ultimately
  have m:
   "(m \<turnstile> p \<leadsto>\<^sup>+ p' \<or> m \<turnstile> p' \<leadsto>\<^sup>+ p) \<and>
    (m \<turnstile> p \<leadsto>\<^sup>+ p' \<longrightarrow> is_chunk m c p p') \<and>
    (m \<turnstile> p' \<leadsto>\<^sup>+ p \<longrightarrow> is_chunk m c' p' p)"
    using chunked p p' neq r arch_assm
    unfolding mdb_chunked_def m'_def
    by simp

  from x no_m px [symmetric] dlist no_0
  have npx: "\<not> m \<turnstile> p \<leadsto>\<^sup>* x" by (rule no_mdb_rtrancl)

  from x no_m p'x [symmetric] dlist no_0
  have np'x: "\<not> m \<turnstile> p' \<leadsto>\<^sup>* x" by (rule no_mdb_rtrancl)

  show "(m' \<turnstile> p \<leadsto>\<^sup>+ p' \<or> m' \<turnstile> p' \<leadsto>\<^sup>+ p) \<and>
        (m' \<turnstile> p \<leadsto>\<^sup>+ p' \<longrightarrow> is_chunk m' c p p') \<and>
        (m' \<turnstile> p' \<leadsto>\<^sup>+ p \<longrightarrow> is_chunk m' c' p' p)"
  proof (cases "m \<turnstile> p \<leadsto>\<^sup>+ p'")
    case True
    with m
    have ch: "is_chunk m c p p'" by simp

    from True npx
    have "m' \<turnstile> p \<leadsto>\<^sup>+ p'"
      unfolding m'_def
      by (rule mdb_trancl_other_update)
    moreover
    with nl
    have "\<not> m' \<turnstile> p' \<leadsto>\<^sup>+ p"
      apply clarsimp
      apply (drule (1) trancl_trans)
      apply (simp add: no_loops_def)
      done
    moreover
    have "is_chunk m' c p p'"
      unfolding is_chunk_def
    proof clarify
      fix p''
      assume "m' \<turnstile> p \<leadsto>\<^sup>+ p''"
      with npx
      have "m \<turnstile> p \<leadsto>\<^sup>+ p''"
        unfolding m'_def
        by - (rule mdb_trancl_update_other)
      moreover
      then
      have p''x: "p'' \<noteq> x"
        using dlist x no_m no_0
        apply clarsimp
        apply (drule tranclD2)
        apply clarsimp
        apply (frule vdlist_nextD0, simp, assumption)
        apply (clarsimp simp: mdb_prev_def mdb_next_unfold no_mdb_def)
        done
      moreover
      assume "m' \<turnstile> p'' \<leadsto>\<^sup>* p'"
      {
        moreover
        from x no_m p''x [symmetric] dlist no_0
        have "\<not>m \<turnstile> p'' \<leadsto>\<^sup>* x" by (rule no_mdb_rtrancl)
        ultimately
        have "m \<turnstile> p'' \<leadsto>\<^sup>* p'"
          unfolding m'_def
          by (rule mdb_rtrancl_update_other)
      }
      ultimately
      have "\<exists>cap'' n''.
            m p'' = Some (CTE cap'' n'') \<and> sameRegionAs c cap''"
        using ch
        by (simp add: is_chunk_def)
      with p''x
      show "\<exists>cap'' n''.
             m' p'' = Some (CTE cap'' n'') \<and> sameRegionAs c cap''"
        by (simp add: m'_def)
    qed
    ultimately
    show ?thesis by simp
  next
    case False
    with m
    have p'p: "m \<turnstile> p' \<leadsto>\<^sup>+ p" by simp
    with m
    have ch: "is_chunk m c' p' p" by simp
    from p'p np'x
    have "m' \<turnstile> p' \<leadsto>\<^sup>+ p"
      unfolding m'_def
      by (rule mdb_trancl_other_update)
    moreover
    with nl
    have "\<not> m' \<turnstile> p \<leadsto>\<^sup>+ p'"
      apply clarsimp
      apply (drule (1) trancl_trans)
      apply (simp add: no_loops_def)
      done
    moreover
    have "is_chunk m' c' p' p"
      unfolding is_chunk_def
    proof clarify
      fix p''
      assume "m' \<turnstile> p' \<leadsto>\<^sup>+ p''"
      with np'x
      have "m \<turnstile> p' \<leadsto>\<^sup>+ p''"
        unfolding m'_def
        by - (rule mdb_trancl_update_other)
      moreover
      then
      have p''x: "p'' \<noteq> x"
        using dlist x no_m no_0
        apply clarsimp
        apply (drule tranclD2)
        apply clarsimp
        apply (frule vdlist_nextD0, simp, assumption)
        apply (clarsimp simp: mdb_prev_def mdb_next_unfold no_mdb_def)
        done
      moreover
      assume "m' \<turnstile> p'' \<leadsto>\<^sup>* p"
      {
        moreover
        from x no_m p''x [symmetric] dlist no_0
        have "\<not>m \<turnstile> p'' \<leadsto>\<^sup>* x" by (rule no_mdb_rtrancl)
        ultimately
        have "m \<turnstile> p'' \<leadsto>\<^sup>* p"
          unfolding m'_def
          by (rule mdb_rtrancl_update_other)
      }
      ultimately
      have "\<exists>cap'' n''.
            m p'' = Some (CTE cap'' n'') \<and> sameRegionAs c' cap''"
        using ch
        by (simp add: is_chunk_def)
      with p''x
      show "\<exists>cap'' n''.
             m' p'' = Some (CTE cap'' n'') \<and> sameRegionAs c' cap''"
        by (simp add: m'_def)
    qed
    ultimately
    show ?thesis by simp
  qed
qed

lemma cte_refs_capRange:
  "\<lbrakk> s \<turnstile>' c; \<forall>irq. c \<noteq> IRQHandlerCap irq \<rbrakk> \<Longrightarrow> cte_refs' c x \<subseteq> capRange c"
  apply (cases c; simp add: capRange_def isCap_simps)
    apply (clarsimp dest!: valid_capAligned
                    simp: capAligned_def objBits_simps field_simps)
    apply (frule tcb_cte_cases_small)
    apply (intro conjI)
     apply (erule(1) is_aligned_no_wrap')
    apply (rule word_plus_mono_right[where z="2^tcbBlockSizeBits - 1", simplified field_simps])
     apply (drule word_le_minus_one_leq, simp)
    apply (erule is_aligned_no_wrap'[where off="2^tcbBlockSizeBits - 1", simplified field_simps])
    apply (drule word_le_minus_one_leq)
    apply simp
   defer
   \<comment> \<open>CNodeCap\<close>
   apply (clarsimp simp: objBits_simps capAligned_def dest!: valid_capAligned)
   apply (rename_tac word1 nat1 word2 nat2 x)
   apply (subgoal_tac "x * 2^cteSizeBits < 2 ^ (cteSizeBits + nat1)")
    apply (intro conjI)
     apply (simp add: shiftl_t2n mult_ac)
     apply (erule(1) is_aligned_no_wrap')
    apply (simp add: add_diff_eq[symmetric])
    apply (rule word_plus_mono_right)
     apply simp
    apply (simp add: shiftl_t2n mult_ac)
    apply (erule is_aligned_no_wrap')
    apply simp
   apply (simp add: power_add field_simps mask_def)
   apply (erule word_mult_less_mono1)
    apply (simp add: objBits_defs)
   apply (frule power_strict_increasing [where a="2 :: nat" and n="y + z" for y z])
    apply simp
   apply (simp only: power_add)
   apply (simp add: word_bits_def)
  \<comment> \<open>Zombie\<close>
  apply (rename_tac word zombie_type nat)
  apply (clarsimp simp: capAligned_def valid_cap'_def objBits_simps)
  apply (subgoal_tac "xa * 2^cteSizeBits < 2 ^ zBits zombie_type")
   apply (intro conjI)
    apply (simp add: shiftl_t2n mult_ac)
    apply (erule(1) is_aligned_no_wrap')
   apply (simp add: add_diff_eq[symmetric])
   apply (rule word_plus_mono_right)
    apply (simp add: shiftl_t2n mult_ac)
   apply (erule is_aligned_no_wrap')
   apply simp
  apply (case_tac zombie_type)
   apply simp
   apply (rule div_lt_mult)
    apply (simp add: objBits_defs)
    apply (erule order_less_le_trans)
    apply (simp add: word_le_nat_alt)
    apply (subst le_unat_uoi[where z=5])
     apply simp
    apply simp
   apply (simp add: objBits_defs)
  apply (simp add: objBits_simps' power_add mult.commute)
  apply (rule word_mult_less_mono1)
    apply (erule order_less_le_trans)
    apply (simp add: word_le_nat_alt)
    apply (subst le_unat_uoi)
     apply (subst unat_power_lower)
      prefer 2
      apply assumption
     apply (simp add: word_bits_def)
    apply (simp add: word_bits_def)
   apply simp
  apply (frule power_strict_increasing [where a="2 :: nat" and n="y + z" for y z])
   apply simp
  apply (simp only: power_add)
  apply (simp add: word_bits_def)
  done

lemma untypedCapRange:
  "isUntypedCap cap \<Longrightarrow> capRange cap = untypedRange cap"
  by (clarsimp simp: isCap_simps)

lemma no_direct_loop [simp]:
  "no_loops m \<Longrightarrow> m (mdbNext node) \<noteq> Some (CTE cap node)"
  by (fastforce simp: mdb_next_rel_def mdb_next_def no_loops_def)

lemma no_loops_direct_simp:
  "no_loops m \<Longrightarrow> m \<turnstile> x \<leadsto> x = False"
  by (auto simp add: no_loops_def)

lemma no_loops_trancl_simp:
  "no_loops m \<Longrightarrow> m \<turnstile> x \<leadsto>\<^sup>+ x = False"
  by (auto simp add: no_loops_def)

lemma subtree_mdb_next:
  "m \<turnstile> a \<rightarrow> b \<Longrightarrow> m \<turnstile> a \<leadsto>\<^sup>+ b"
  by (erule subtree.induct) (auto simp: mdb_next_rel_def intro: trancl_into_trancl)
end

context mdb_order
begin

lemma no_loops: "no_loops m"
  using chain no_0 by (rule mdb_chain_0_no_loops)

lemma irrefl_direct_simp [iff]:
  "m \<turnstile> x \<leadsto> x = False"
  using no_loops by (rule no_loops_direct_simp)

lemma irrefl_trancl_simp [iff]:
  "m \<turnstile> x \<leadsto>\<^sup>+ x = False"
  using no_loops by (rule no_loops_trancl_simp)

lemma irrefl_subtree [iff]:
  "m \<turnstile> x \<rightarrow> x = False"
  by (clarsimp dest!: subtree_mdb_next)

end (* of context mdb_order *)

lemma no_loops_prev_next_0:
  fixes m :: cte_heap
  assumes src: "m src = Some (CTE src_cap src_node)"
  assumes no_loops: "no_loops m"
  assumes dlist: "valid_dlist m"
  shows "(mdbPrev src_node = mdbNext src_node) =
         (mdbPrev src_node = 0 \<and> mdbNext src_node = 0)"
proof -
  { assume "mdbPrev src_node = mdbNext src_node"
    moreover
    assume "mdbNext src_node \<noteq> 0"
    ultimately
    obtain cte where
      "m (mdbNext src_node) = Some cte"
      "mdbNext (cteMDBNode cte) = src"
      using src dlist
      by (fastforce simp add: valid_dlist_def Let_def)
    hence "m \<turnstile> src \<leadsto>\<^sup>+ src" using src
      apply -
      apply (rule trancl_trans)
       apply (rule r_into_trancl)
       apply (simp add: next_unfold')
      apply (rule r_into_trancl)
      apply (simp add: next_unfold')
      done
    with no_loops
    have False by (simp add: no_loops_def)
  }
  thus ?thesis by auto blast
qed

lemma no_loops_next_prev_0:
  fixes m :: cte_heap
  assumes "m src = Some (CTE src_cap src_node)"
  assumes "no_loops m"
  assumes "valid_dlist m"
  shows "(mdbNext src_node = mdbPrev src_node) =
         (mdbPrev src_node = 0 \<and> mdbNext src_node = 0)"
  apply (rule iffI)
  apply (drule sym)
   apply (simp add: no_loops_prev_next_0 [OF assms])
  apply clarsimp
  done

locale vmdb = mdb_next +
  assumes valid: "valid_mdb_ctes m"

sublocale vmdb < mdb_order
  using valid
  by (auto simp: greater_def greater_eq_def mdb_order_def valid_mdb_ctes_def)

context vmdb
begin

declare no_0 [intro!]
declare no_loops [intro!]

lemma dlist [intro!]: "valid_dlist m"
  using valid by (simp add: valid_mdb_ctes_def)

lemmas m_0_simps [iff] = no_0_simps [OF no_0]

lemma prev_next_0_p:
  assumes "m p = Some (CTE cap node)"
  shows "(mdbPrev node = mdbNext node) =
         (mdbPrev node = 0 \<and> mdbNext node = 0)"
  using assms by (rule no_loops_prev_next_0) auto

lemma next_prev_0_p:
  assumes "m p = Some (CTE cap node)"
  shows "(mdbNext node = mdbPrev node) =
         (mdbPrev node = 0 \<and> mdbNext node = 0)"
  using assms by (rule no_loops_next_prev_0) auto

lemmas dlistEn = valid_dlistEn [OF dlist]
lemmas dlistEp = valid_dlistEp [OF dlist]

lemmas dlist_prevD = vdlist_prevD [OF _ _ dlist no_0]
lemmas dlist_nextD = vdlist_nextD [OF _ _ dlist no_0]
lemmas dlist_prevD0 = vdlist_prevD0 [OF _ _ dlist]
lemmas dlist_nextD0 = vdlist_nextD0 [OF _ _ dlist]
lemmas dlist_prev_src_unique = vdlist_prev_src_unique [OF _ _ _ dlist]
lemmas dlist_next_src_unique = vdlist_next_src_unique [OF _ _ _ dlist]

lemma subtree_not_0 [simp]:
  "\<not>m \<turnstile> p \<rightarrow> 0"
  apply clarsimp
  apply (erule subtree.cases)
  apply auto
  done

lemma not_0_subtree [simp]:
  "\<not>m \<turnstile> 0 \<rightarrow> p"
  apply clarsimp
  apply (erule subtree.induct)
  apply (auto simp: mdb_next_unfold)
  done

lemma not_0_next [simp]:
  "\<not> m \<turnstile> 0 \<leadsto> p"
  by (clarsimp simp: mdb_next_unfold)

lemma not_0_trancl [simp]:
  "\<not> m \<turnstile> 0 \<leadsto>\<^sup>+ p"
  by (clarsimp dest!: tranclD)

lemma rtrancl0 [simp]:
  "m \<turnstile> 0 \<leadsto>\<^sup>* p = (p = 0)"
  by (auto dest!: rtranclD)

lemma valid_badges: "valid_badges m"
  using valid by (simp add: valid_mdb_ctes_def)

lemma nullcaps: "valid_nullcaps m"
  using valid by (simp add: valid_mdb_ctes_def)

lemma
  caps_contained: "caps_contained' m" and
  chunked: "mdb_chunked m" and
  untyped_mdb: "untyped_mdb' m" and
  untyped_inc: "untyped_inc' m" and
  class_links: "class_links m" and
  irq_control: "irq_control m"
  using valid by (simp add: valid_mdb_ctes_def)+

end (* of context vmdb *)

lemma no_self_loop_next:
  assumes vmdb: "valid_mdb_ctes m"
  and     lup: "m ptr = Some cte"
  shows   "mdbNext (cteMDBNode cte) \<noteq> ptr"
proof -
  from vmdb have "no_loops m" ..
  thus ?thesis
    by (rule no_self_loop_next_noloop) fact+
qed

lemma no_self_loop_prev:
  assumes vmdb: "valid_mdb_ctes m"
  and     lup: "m ptr = Some cte"
  shows   "mdbPrev (cteMDBNode cte) \<noteq> ptr"
proof
  assume prev: "mdbPrev (cteMDBNode cte) = ptr"

  from vmdb have "no_0 m" ..
  with lup have "ptr \<noteq> 0"
    by (rule no_0_neq)

  moreover have "mdbNext (cteMDBNode cte) \<noteq> ptr"
    by (rule no_self_loop_next) fact+

  moreover from vmdb have "valid_dlist m" ..

  ultimately show False using lup prev
    by - (erule (1) valid_dlistEp, simp_all)
qed


locale mdb_ptr = vmdb +
  fixes p cap node
  assumes m_p [intro!]: "m p = Some (CTE cap node)"
begin

lemma p_not_next [simp]:
  "(p = mdbNext node) = False"
  using valid m_p by (fastforce dest: no_self_loop_next)

lemma p_not_prev [simp]:
  "(p = mdbPrev node) = False"
  using valid m_p by (fastforce dest: no_self_loop_prev)

lemmas next_not_p [simp] = p_not_next [THEN x_sym]
lemmas prev_not_p [simp] = p_not_prev [THEN x_sym]

lemmas prev_next_0 [simp] = prev_next_0_p [OF m_p] next_prev_0_p [OF m_p]

lemma p_0 [simp]: "p \<noteq> 0" using m_p by clarsimp

lemma p_nextD:
  assumes p': "m p' = Some (CTE cap' node')"
  assumes eq: "mdbNext node = mdbNext node'"
  shows "p = p' \<or> mdbNext node = 0 \<and> mdbNext node' = 0"
proof (cases "mdbNext node = 0")
  case True thus ?thesis using eq by simp
next
  case False
  with eq have n': "mdbNext node' \<noteq> 0" by simp

  have "p = p'"
    apply (rule dlistEn [OF m_p, simplified, OF False])
    apply (simp add: eq)
    apply (rule dlistEn [OF p', simplified, OF n'])
    apply clarsimp
    done

  thus ?thesis by blast
qed

lemma p_next_eq:
  assumes "m p' = Some (CTE cap' node')"
  shows "(mdbNext node = mdbNext node') =
         (p = p' \<or> mdbNext node = 0 \<and> mdbNext node' = 0)"
  using assms m_p
  apply -
  apply (rule iffI)
   apply (erule (1) p_nextD)
  apply auto
  done

lemma p_prevD:
  assumes p': "m p' = Some (CTE cap' node')"
  assumes eq: "mdbPrev node = mdbPrev node'"
  shows "p = p' \<or> mdbPrev node = 0 \<and> mdbPrev node' = 0"
proof (cases "mdbPrev node = 0")
  case True thus ?thesis using eq by simp
next
  case False
  with eq have n': "mdbPrev node' \<noteq> 0" by simp

  have "p = p'"
    apply (rule dlistEp [OF m_p, simplified, OF False])
    apply (simp add: eq)
    apply (rule dlistEp [OF p', simplified, OF n'])
    apply clarsimp
    done

  thus ?thesis by blast
qed

lemma p_prev_eq:
  assumes "m p' = Some (CTE cap' node')"
  shows "(mdbPrev node = mdbPrev node') =
         (p = p' \<or> mdbPrev node = 0 \<and> mdbPrev node' = 0)"
  using assms m_p
  apply -
  apply (rule iffI)
   apply (erule (1) p_prevD)
  apply auto
  done

lemmas p_prev_qe = p_prev_eq [THEN x_sym]
lemmas p_next_qe = p_next_eq [THEN x_sym]

lemma m_p_prev [intro!]:
  "m \<turnstile> mdbPrev node \<leftarrow> p"
  using m_p by (clarsimp simp: mdb_prev_def)

lemma m_p_next [intro!]:
  "m \<turnstile> p \<leadsto> mdbNext node"
  using m_p by (clarsimp simp: mdb_next_unfold)

lemma next_p_prev:
  "mdbNext node \<noteq> 0 \<Longrightarrow> m \<turnstile> p \<leftarrow> mdbNext node"
  by (rule dlist_nextD0 [OF m_p_next])

lemma prev_p_next:
  "mdbPrev node \<noteq> 0 \<Longrightarrow> m \<turnstile> mdbPrev node \<leadsto> p"
  by (rule dlist_prevD0 [OF m_p_prev])

lemma p_next:
  "(m \<turnstile> p \<leadsto> p') = (p' = mdbNext node)"
  using m_p by (auto simp: mdb_next_unfold)

end (* of locale mdb_ptr *)

lemma no_mdb_not_target:
  "\<lbrakk> m \<turnstile> c \<leadsto> c'; m p = Some cte; no_mdb cte; valid_dlist m; no_0 m \<rbrakk>
  \<Longrightarrow> c' \<noteq> p"
  apply clarsimp
  apply (subgoal_tac "c \<noteq> 0")
   prefer 2
   apply (clarsimp simp: mdb_next_unfold)
  apply (drule (3) vdlist_nextD)
  apply (clarsimp simp: mdb_prev_def)
  apply (simp add: no_mdb_def)
  done

context begin interpretation Arch . (*FIXME: arch-split*)
lemma valid_dlist_init:
  "\<lbrakk> valid_dlist m; m p = Some cte; no_mdb cte \<rbrakk> \<Longrightarrow>
  valid_dlist (m (p \<mapsto> CTE cap initMDBNode))"
  apply (simp add: initMDBNode_def Let_def nullPointer_def)
  apply (clarsimp simp: no_mdb_def valid_dlist_def Let_def)
  apply fastforce
  done
end

lemma (in mdb_ptr) descendants_of_init':
  assumes n: "no_mdb (CTE cap node)"
  shows
  "descendants_of' p' (m(p \<mapsto> CTE c initMDBNode)) =
   descendants_of' p' m"
  apply (rule set_eqI)
  apply (simp add: descendants_of'_def)
  apply (rule iffI)
   apply (erule subtree.induct)
    apply (frule no_mdb_not_target [where p=p])
        apply simp
       apply (simp add: no_mdb_def)
      apply (rule valid_dlist_init[OF dlist, OF m_p n])
     apply (insert no_0)[1]
     apply (clarsimp simp: no_0_def)
    apply (clarsimp simp: mdb_next_unfold split: if_split_asm)
    apply (rule direct_parent)
      apply (clarsimp simp: mdb_next_unfold)
     apply assumption
    apply (clarsimp simp: parentOf_def split: if_split_asm)
   apply (frule no_mdb_not_target [where p=p])
       apply simp
      apply (simp add: no_mdb_def)
     apply (rule valid_dlist_init[OF dlist, OF m_p n])
    apply (insert no_0)[1]
    apply (clarsimp simp: no_0_def)
   apply (subgoal_tac "p' \<noteq> p")
    apply (erule trans_parent)
      apply (clarsimp simp: mdb_next_unfold split: if_split_asm)
     apply assumption
    apply (clarsimp simp: parentOf_def m_p split: if_split_asm)
   apply clarsimp
   apply (drule subtree_mdb_next)+
   apply (drule tranclD)+
   apply clarsimp
   apply (insert n)[1]
   apply (clarsimp simp: mdb_next_unfold m_p no_mdb_def)
  apply (erule subtree.induct)
   apply (frule no_mdb_not_target [where p=p], rule m_p, rule n)
     apply (rule dlist)
    apply (rule no_0)
   apply (subgoal_tac "p'\<noteq>p")
    prefer 2
    apply (insert n)[1]
    apply (clarsimp simp: mdb_next_unfold m_p no_mdb_def)
   apply (rule direct_parent)
     apply (clarsimp simp: mdb_next_unfold)
    apply assumption
   apply (clarsimp simp: parentOf_def)
  apply (frule no_mdb_not_target [where p=p], rule m_p, rule n)
    apply (rule dlist)
   apply (rule no_0)
  apply (subgoal_tac "c'\<noteq>p")
   prefer 2
   apply (insert n)[1]
   apply (clarsimp simp: mdb_next_unfold m_p no_mdb_def)
  apply (subgoal_tac "p'\<noteq>p")
   apply (erule trans_parent)
     apply (clarsimp simp: mdb_next_unfold)
    apply assumption
   apply (clarsimp simp: parentOf_def)
  apply clarsimp
  apply (drule subtree_mdb_next)
  apply (drule tranclD)
  apply clarsimp
  apply (insert n)
  apply (clarsimp simp: mdb_next_unfold no_mdb_def m_p)
  done

lemma untyped_mdb_init:
  "\<lbrakk> valid_mdb_ctes m; m p = Some cte; no_mdb cte;
     caps_no_overlap' m (capRange cap); untyped_mdb' m;
     valid_objs' s; s \<turnstile>' cap;
     m = ctes_of s\<rbrakk>
    \<Longrightarrow> untyped_mdb' (m(p \<mapsto> CTE cap initMDBNode))"
  apply (clarsimp simp add: untyped_mdb'_def)
  apply (rule conjI)
   apply clarsimp
   apply (simp add: caps_no_overlap'_def)
   apply (erule_tac x=p' in allE, erule allE, erule impE, erule exI)
   apply (drule (1) ctes_of_valid_cap')+
   apply (drule valid_capAligned)+
   apply (drule untypedCapRange)+
   apply simp
  apply (cases cte)
  apply (rename_tac capability mdbnode)
  apply clarsimp
  apply (subgoal_tac "mdb_ptr (ctes_of s) p capability mdbnode")
   prefer 2
   apply (simp add: vmdb_def mdb_ptr_def mdb_ptr_axioms_def)
  apply (clarsimp simp: mdb_ptr.descendants_of_init')
  apply (simp add: caps_no_overlap'_def)
  apply (erule_tac x=pa in allE, erule allE, erule impE, erule exI)
  apply (drule (1) ctes_of_valid_cap')+
  apply (drule valid_capAligned untypedCapRange)+
  apply simp
  apply blast
  done

lemma aligned_untypedRange_non_empty:
  "\<lbrakk>capAligned c; isUntypedCap c\<rbrakk> \<Longrightarrow> untypedRange c \<noteq> {}"
  apply (frule untypedCapRange)
  apply (drule capAligned_capUntypedPtr)
   apply (clarsimp simp: isCap_simps)
  apply blast
  done

lemma untypedRange_not_emptyD: "untypedRange c' \<noteq> {} \<Longrightarrow> isUntypedCap c'"
  by (case_tac c'; simp add: isCap_simps)

lemma usableRange_subseteq:
  "\<lbrakk>capAligned c';isUntypedCap c'\<rbrakk> \<Longrightarrow> usableUntypedRange c' \<subseteq> untypedRange c'"
  apply (clarsimp simp:isCap_simps capAligned_def mask_def add_diff_eq split:if_splits)
  apply (erule order_trans[OF is_aligned_no_wrap'])
   apply (erule of_nat_power)
   apply (simp add:word_bits_def)+
 done

lemma untypedRange_in_capRange: "untypedRange x \<subseteq> capRange x"
  by (case_tac x; simp add: capRange_def)

lemma untyped_inc_init:
  "\<lbrakk> valid_mdb_ctes m; m p = Some cte; no_mdb cte;
     caps_no_overlap' m (capRange cap);
     valid_objs' s; s \<turnstile>' cap;
     m = ctes_of s\<rbrakk>
    \<Longrightarrow> untyped_inc' (m(p \<mapsto> CTE cap initMDBNode))"
  apply (clarsimp simp add: valid_mdb_ctes_def untyped_inc'_def)
  apply (intro conjI impI)
   apply clarsimp
   apply (simp add: caps_no_overlap'_def)
   apply (erule_tac x=p' in allE, erule allE, erule impE, erule exI)
   apply (drule (1) ctes_of_valid_cap')+
   apply (drule valid_capAligned)+
   apply (frule usableRange_subseteq[OF _ untypedRange_not_emptyD])
    apply (drule (1) aligned_untypedRange_non_empty)
    apply assumption
   apply (frule_tac c' = c' in  usableRange_subseteq)
    apply (drule (1) aligned_untypedRange_non_empty)
    apply assumption
   apply (drule(1) aligned_untypedRange_non_empty)+
   apply (thin_tac "All P" for P)
    apply (subgoal_tac "untypedRange cap \<inter> untypedRange c' = {}")
    apply (intro conjI)
         apply simp
        apply (drule(2) set_inter_not_emptyD2)
        apply fastforce
       apply (drule(2) set_inter_not_emptyD1)
       apply fastforce
      apply (drule(2) set_inter_not_emptyD3)
      apply simp+
   apply (rule disjoint_subset2[OF _ disjoint_subset])
     apply (rule untypedRange_in_capRange)+
   apply (simp add:Int_ac)
  apply clarsimp
  apply (cases cte)
  apply (rename_tac capability mdbnode)
  apply clarsimp
  apply (subgoal_tac "mdb_ptr (ctes_of s) p capability mdbnode")
   prefer 2
   apply (simp add: vmdb_def mdb_ptr_def mdb_ptr_axioms_def valid_mdb_ctes_def untyped_inc'_def)
  apply (clarsimp simp: mdb_ptr.descendants_of_init')
  apply (simp add: caps_no_overlap'_def)
  apply (erule_tac x=pa in allE, erule allE, erule impE, erule exI)
  apply (drule (1) ctes_of_valid_cap')+
  apply (drule valid_capAligned)+
  apply (frule usableRange_subseteq[OF _ untypedRange_not_emptyD])
   apply (drule (1) aligned_untypedRange_non_empty)
   apply assumption
  apply (frule_tac c' = c in  usableRange_subseteq)
   apply (drule (1) aligned_untypedRange_non_empty)
   apply assumption
  apply (drule (1) aligned_untypedRange_non_empty)+
  apply (drule untypedCapRange)+
  apply (thin_tac "All P" for P)
   apply (subgoal_tac "untypedRange cap \<inter> untypedRange c = {}")
   apply (intro conjI)
        apply simp
       apply (drule(2) set_inter_not_emptyD1)
       apply fastforce
      apply (drule(2) set_inter_not_emptyD2)
      apply fastforce
     apply (drule(2) set_inter_not_emptyD3)
     apply simp+
  apply (rule disjoint_subset2[OF _ disjoint_subset])
    apply (rule untypedRange_in_capRange)+
  apply (simp add:Int_ac)
  done
context begin interpretation Arch . (*FIXME: arch-split*)
lemma valid_nullcaps_init:
  "\<lbrakk> valid_nullcaps m; cap \<noteq> NullCap \<rbrakk> \<Longrightarrow> valid_nullcaps (m(p \<mapsto> CTE cap initMDBNode))"
  by (simp add: valid_nullcaps_def initMDBNode_def nullPointer_def)
end

lemma class_links_init:
  "\<lbrakk> class_links m; no_0 m; m p = Some cte;
     no_mdb cte; valid_dlist m \<rbrakk>
   \<Longrightarrow> class_links (m(p \<mapsto> CTE cap initMDBNode))"
  apply (simp add: class_links_def split del: if_split)
  apply (erule allEI, erule allEI)
  apply simp
  apply (intro conjI impI)
    apply clarsimp
    apply (drule no_mdb_not_target[where p=p], simp)
       apply (simp add: no_mdb_def)
      apply (erule(2) valid_dlist_init)
     apply (clarsimp simp add: no_0_def)
    apply simp
   apply (clarsimp simp: mdb_next_unfold)
  apply (clarsimp simp: mdb_next_unfold)
  done

lemma distinct_zombies_copyE:
  "\<lbrakk> distinct_zombies m; m x = Some cte;
       capClass (cteCap cte') = PhysicalClass
               \<Longrightarrow> isZombie (cteCap cte) = isZombie (cteCap cte');
       \<lbrakk> capClass (cteCap cte') = PhysicalClass; isUntypedCap (cteCap cte) \<rbrakk>
               \<Longrightarrow> isUntypedCap (cteCap cte');
       \<lbrakk> capClass (cteCap cte') = PhysicalClass; isArchFrameCap (cteCap cte) \<rbrakk>
               \<Longrightarrow> isArchFrameCap (cteCap cte');
       isZombie (cteCap cte') \<Longrightarrow> x = y;
       capClass (cteCap cte') = PhysicalClass \<Longrightarrow>
               capBits (cteCap cte') = capBits (cteCap cte);
       capClass (cteCap cte') = PhysicalClass \<longrightarrow> capClass (cteCap cte) = PhysicalClass;
       capClass (cteCap cte') = PhysicalClass \<Longrightarrow>
            capUntypedPtr (cteCap cte') = capUntypedPtr (cteCap cte) \<rbrakk>
        \<Longrightarrow> distinct_zombies (m (y \<mapsto> cte'))"
  apply (simp add: distinct_zombies_def distinct_zombie_caps_def)
  apply clarsimp
  apply (intro allI conjI impI)
    apply clarsimp
    apply (drule_tac x=y in spec)
    apply (drule_tac x=ptr' in spec)
    apply (clarsimp simp: isCap_simps)
   apply clarsimp
   apply (drule_tac x=ptr in spec)
   apply (drule_tac x=x in spec)
   apply clarsimp
   apply auto[1]
  apply clarsimp
  apply (drule_tac x=ptr in spec)
  apply (drule_tac x=ptr' in spec)
  apply auto[1]
  done

lemmas distinct_zombies_sameE
    = distinct_zombies_copyE [where y=x and x=x for x, simplified,
                              OF _ _ _ _ _]
context begin interpretation Arch . (*FIXME: arch-split*)
lemma capBits_Master:
  "capBits (capMasterCap cap) = capBits cap"
  by (clarsimp simp: capMasterCap_def split: capability.split arch_capability.split)

lemma capUntyped_Master:
  "capUntypedPtr (capMasterCap cap) = capUntypedPtr cap"
  by (clarsimp simp: capMasterCap_def AARCH64_H.capUntypedPtr_def split: capability.split arch_capability.split)

lemma distinct_zombies_copyMasterE:
  "\<lbrakk> distinct_zombies m; m x = Some cte;
          capClass (cteCap cte') = PhysicalClass
             \<Longrightarrow> capMasterCap (cteCap cte) = capMasterCap (cteCap cte');
          isZombie (cteCap cte') \<Longrightarrow> x = y \<rbrakk>
       \<Longrightarrow> distinct_zombies (m (y \<mapsto> cte'))"
  apply (erule(1) distinct_zombies_copyE, simp_all)
       apply (rule master_eqI, rule isCap_Master, simp)
      apply (drule_tac f=isUntypedCap in arg_cong)
      apply (simp add: isCap_Master)
     apply (drule_tac f=isArchFrameCap in arg_cong)
     apply (simp add: isCap_Master)
    apply (rule master_eqI, rule capBits_Master, simp)
   apply clarsimp
   apply (drule_tac f=capClass in arg_cong, simp add: capClass_Master)
  apply (drule_tac f=capUntypedPtr in arg_cong, simp add: capUntyped_Master)
  done

lemmas distinct_zombies_sameMasterE
    = distinct_zombies_copyMasterE[where x=x and y=x for x, simplified,
                                   OF _ _ _]

lemma isZombie_capClass: "isZombie cap \<Longrightarrow> capClass cap = PhysicalClass"
  by (clarsimp simp: isCap_simps)

lemma distinct_zombies_unzombieE:
  "\<lbrakk> distinct_zombies m; m x = Some cte;
        isZombie (cteCap cte') \<longrightarrow> isZombie (cteCap cte);
        isUntypedCap (cteCap cte) \<longrightarrow> isUntypedCap (cteCap cte');
        isArchFrameCap (cteCap cte) \<longrightarrow> isArchFrameCap (cteCap cte');
        capClass (cteCap cte') = capClass (cteCap cte);
        capBits (cteCap cte') = capBits (cteCap cte);
        capUntypedPtr (cteCap cte') = capUntypedPtr (cteCap cte) \<rbrakk>
          \<Longrightarrow> distinct_zombies (m(x \<mapsto> cte'))"
  apply (simp add: distinct_zombies_def distinct_zombie_caps_def
                     split del: if_split)
  apply (erule allEI, erule allEI)
  apply clarsimp
  done

lemma distinct_zombies_seperateE:
  "\<lbrakk> distinct_zombies m;
      \<And>y cte. m y = Some cte \<Longrightarrow> x \<noteq> y
                \<Longrightarrow> \<not> isUntypedCap (cteCap cte)
                \<Longrightarrow> \<not> isArchFrameCap (cteCap cte)
                \<Longrightarrow> capClass (cteCap cte) = PhysicalClass
                \<Longrightarrow> capClass (cteCap cte') = PhysicalClass
                \<Longrightarrow> capUntypedPtr (cteCap cte) = capUntypedPtr (cteCap cte')
                \<Longrightarrow> capBits (cteCap cte) = capBits (cteCap cte') \<Longrightarrow> False \<rbrakk>
       \<Longrightarrow> distinct_zombies (m (x \<mapsto> cte'))"
  apply (simp add: distinct_zombies_def distinct_zombie_caps_def)
  apply (intro impI allI conjI)
    apply (clarsimp simp: isZombie_capClass)
    apply fastforce
   apply clarsimp
   apply (frule isZombie_capClass)
   apply (subgoal_tac "\<not> isUntypedCap (cteCap z) \<and> \<not> isArchFrameCap (cteCap z)")
    apply fastforce
   apply (clarsimp simp: isCap_simps)
  apply clarsimp
  apply (erule notE[rotated], elim allE, erule mp)
  apply auto[1]
  done

lemma distinct_zombies_init:
  "\<lbrakk> distinct_zombies m; caps_no_overlap' m (capRange (cteCap cte));
        capAligned (cteCap cte); \<forall>x cte. m x = Some cte \<longrightarrow> capAligned (cteCap cte) \<rbrakk>
       \<Longrightarrow> distinct_zombies (m (p \<mapsto> cte))"
  apply (erule distinct_zombies_seperateE)
  apply (rename_tac y cte')
  apply (clarsimp simp: caps_no_overlap'_def)
  apply (drule_tac x=y in spec)+
  apply (case_tac cte')
  apply (rename_tac capability mdbnode)
  apply clarsimp
  apply (subgoal_tac "capRange capability \<noteq> capRange (cteCap cte)")
   apply (clarsimp simp: capRange_def)
  apply (drule(1) capAligned_capUntypedPtr)+
  apply clarsimp
  done

definition
  "no_irq' m \<equiv> \<forall>p cte. m p = Some cte \<longrightarrow> cteCap cte \<noteq> IRQControlCap"

lemma no_irqD':
  "\<lbrakk> m p = Some (CTE IRQControlCap n); no_irq' m \<rbrakk> \<Longrightarrow> False"
  unfolding no_irq'_def
  apply (erule allE, erule allE, erule (1) impE)
  apply auto
  done

lemma irq_control_init:
  assumes no_irq: "cap = IRQControlCap \<longrightarrow> no_irq' m"
  assumes ctrl: "irq_control m"
  shows "irq_control (m(p \<mapsto> CTE cap initMDBNode))"
  using no_irq
  apply (clarsimp simp: irq_control_def)
  apply (rule conjI)
   apply (clarsimp simp: initMDBNode_def)
   apply (erule (1) no_irqD')
  apply clarsimp
  apply (frule irq_revocable, rule ctrl)
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (erule (1) no_irqD')
  apply clarsimp
  apply (erule (1) irq_controlD, rule ctrl)
  done

lemma valid_mdb_ctes_init:
  "\<lbrakk> valid_mdb_ctes m; m p = Some cte; no_mdb cte;
     caps_no_overlap' m (capRange cap); s \<turnstile>' cap;
     valid_objs' s; m = ctes_of s; cap \<noteq> NullCap;
     fresh_virt_cap_class (capClass cap) (ctes_of s);
     cap = capability.IRQControlCap \<longrightarrow> no_irq' (ctes_of s) \<rbrakk> \<Longrightarrow>
  valid_mdb_ctes (m (p \<mapsto> CTE cap initMDBNode))"
  apply (simp add: valid_mdb_ctes_def)
  apply (rule conjI, rule valid_dlist_init, simp+)
  apply (subgoal_tac "p \<noteq> 0")
   prefer 2
   apply (erule no_0_neq, clarsimp)
  apply (clarsimp simp: no_0_update)
  apply (rule conjI, rule mdb_chain_0_update_0, simp+)
  apply (rule conjI, rule valid_badges_0_update, simp+)
  apply (rule conjI, erule (1) caps_contained_no_overlap)
  apply (rule conjI, rule mdb_chunked_init, simp+)
  apply (rule conjI)
   apply (rule untyped_mdb_init, (simp add: valid_mdb_ctes_def)+)
  apply (rule conjI)
   apply (rule untyped_inc_init, (simp add: valid_mdb_ctes_def)+)
  apply (rule conjI)
   apply (erule(1) valid_nullcaps_init)
  apply (rule conjI, simp add: ut_revocable'_def initMDBNode_def)
  apply (rule conjI, erule(4) class_links_init)
  apply (rule conjI)
   apply (erule distinct_zombies_init, simp+)
    apply (erule valid_capAligned)
   apply clarsimp
   apply (case_tac ctea, clarsimp)
   apply (rule valid_capAligned, erule(1) ctes_of_valid_cap')
  apply (rule conjI)
   apply (erule (1) irq_control_init)
  apply (simp add: ran_def reply_masters_rvk_fb_def)
  apply (auto simp: initMDBNode_def)[1]
  done

lemma setCTE_state_refs_of'[wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace> setCTE p cte \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  unfolding setCTE_def
  apply (rule setObject_state_refs_of_eq)
  apply (clarsimp simp: updateObject_cte in_monad typeError_def
                        in_magnitude_check objBits_simps
                 split: kernel_object.split_asm if_split_asm)
  done

lemma setCTE_valid_mdb:
  fixes cap
  defines "cte \<equiv> CTE cap initMDBNode"
  shows
  "\<lbrace>\<lambda>s. valid_mdb' s \<and> cte_wp_at' no_mdb ptr s \<and>
        s \<turnstile>' cap \<and> valid_objs' s \<and> cap \<noteq> NullCap \<and>
        caps_no_overlap' (ctes_of s) (capRange cap) \<and>
        fresh_virt_cap_class (capClass cap) (ctes_of s) \<and>
        (cap = capability.IRQControlCap \<longrightarrow> no_irq' (ctes_of s))\<rbrace>
  setCTE ptr cte
  \<lbrace>\<lambda>r. valid_mdb'\<rbrace>"
  apply (simp add: valid_mdb'_def setCTE_def cte_def cte_wp_at_ctes_of)
  apply (wp ctes_of_setObject_cte)
  apply (clarsimp simp del: fun_upd_apply)
  apply (erule (8) valid_mdb_ctes_init [OF _ _ _ _ _ _ refl])
  done

lemma setCTE_valid_objs'[wp]:
  "\<lbrace>valid_objs' and (valid_cap' (cteCap cte)) \<rbrace>
    setCTE p cte \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  unfolding setCTE_def
  apply (rule setObject_valid_objs')
   apply (clarsimp simp: prod_eq_iff lookupAround2_char1 updateObject_cte objBits_simps)
  apply (clarsimp simp: prod_eq_iff lookupAround2_char1
                         updateObject_cte in_monad typeError_def
                         valid_obj'_def valid_tcb'_def valid_cte'_def
                         tcb_cte_cases_def cteSizeBits_def
                  split: kernel_object.split_asm if_split_asm)
  done

lemma getCTE_cte_wp_at:
  "\<lbrace>\<top>\<rbrace> getCTE p \<lbrace>\<lambda>rv. cte_wp_at' (\<lambda>c. c = rv) p\<rbrace>"
  apply (clarsimp simp: valid_def cte_wp_at'_def getCTE_def)
  apply (frule state_unchanged [OF getObject_cte_inv])
  apply simp
  apply (drule getObject_cte_det, simp)
  done

lemma getCTE_sp:
  "\<lbrace>P\<rbrace> getCTE p \<lbrace>\<lambda>rv. cte_wp_at' (\<lambda>c. c = rv) p and P\<rbrace>"
  apply (rule hoare_chain)
    apply (rule hoare_vcg_conj_lift)
     apply (rule getCTE_cte_wp_at)
    apply (rule getCTE_inv)
   apply (rule conjI, rule TrueI, assumption)
  apply simp
  done

lemmas setCTE_ad[wp] =
  setObject_aligned[where 'a=cte, folded setCTE_def]
  setObject_distinct[where 'a=cte, folded setCTE_def]
lemmas setCTE_map_to_ctes =
  ctes_of_setObject_cte[folded setCTE_def]

lemma getCTE_ctes_wp:
  "\<lbrace>\<lambda>s. \<forall>cte. ctes_of s ptr = Some cte \<longrightarrow> P cte s\<rbrace> getCTE ptr \<lbrace>P\<rbrace>"
  apply (rule hoare_strengthen_post, rule getCTE_sp)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

lemma updateMDB_valid_objs'[wp]:
  "\<lbrace>valid_objs'\<rbrace> updateMDB m p \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  apply (clarsimp simp add: updateMDB_def)
  apply (wp | simp)+
  done

lemma cte_overwrite:
  "cteMDBNode_update (\<lambda>x. m) (cteCap_update (\<lambda>x. c) v) = CTE c m"
  by (cases v, simp)

lemma setCTE_no_0_obj' [wp]:
  "\<lbrace>no_0_obj'\<rbrace> setCTE p c \<lbrace>\<lambda>_. no_0_obj'\<rbrace>"
  by (simp add: setCTE_def) wp

crunch setCTE
  for pspace_canonical'[wp]: pspace_canonical'

declare mresults_fail[simp]

end

end (* of theory *)
