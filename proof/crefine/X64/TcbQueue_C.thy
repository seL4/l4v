(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory TcbQueue_C
imports Ctac_lemmas_C
begin

context kernel
begin

lemma tcb_queueD:
  assumes queue_rel: "tcb_queue_relation getNext getPrev mp queue qprev qhead"
  and     valid_ntfn: "distinct queue"
  and      in_queue: "tcbp \<in> set queue"
  and        cs_tcb: "mp (tcb_ptr_to_ctcb_ptr tcbp) = Some tcb"
  shows "(if tcbp = hd queue then getPrev tcb = qprev
                  else (\<exists>n < (length queue) - 1. getPrev tcb = tcb_ptr_to_ctcb_ptr (queue ! n)
                                                                    \<and> tcbp = queue ! Suc n))
         \<and> (if tcbp = last queue then getNext tcb = NULL
                  else (\<exists>n < (length queue) - 1. tcbp = queue ! n
                        \<and> getNext tcb = tcb_ptr_to_ctcb_ptr (queue ! Suc n)))"
  (is "?prev tcb queue qprev \<and> ?next tcb queue")
  using queue_rel in_queue valid_ntfn
proof (induct queue arbitrary: qprev qhead)
  case Nil
  thus ?case by simp
next
  case (Cons tcb' tcbs qprev' qhead')
  have "tcbp = tcb' \<or> tcbp \<in> set tcbs" using Cons.prems by simp
  thus ?case
  proof
    assume tcbp: "tcbp = tcb'"
    hence "?prev tcb (tcb' # tcbs) qprev'"
      using Cons.prems cs_tcb by clarsimp
    moreover
    have "?next tcb (tcb' # tcbs)"
    proof (cases "tcbs = []")
      case True
      thus ?thesis using tcbp Cons.prems cs_tcb by clarsimp
    next
      case False
      hence "tcbp \<noteq> last tcbs" using tcbp Cons.prems by clarsimp
      thus ?thesis using False tcbp Cons.prems cs_tcb
        apply clarsimp
        apply (rule exI [where x = 0])
        apply simp
        apply (cases tcbs)
        apply simp_all
        done
    qed
    ultimately show ?thesis ..
  next
    assume tcbp: "tcbp \<in> set tcbs"
    obtain tcb2 where cs_tcb2: "mp (tcb_ptr_to_ctcb_ptr tcb') = Some tcb2"
      and rel2: "tcb_queue_relation getNext getPrev mp tcbs (tcb_ptr_to_ctcb_ptr tcb') (getNext tcb2)"
      using Cons.prems
      by clarsimp

    have ih: "?prev tcb tcbs (tcb_ptr_to_ctcb_ptr tcb') \<and> ?next tcb tcbs"
    proof (rule Cons.hyps)
      from Cons.prems show (* "\<forall>t\<in>set tcbs. tcb_at' t s"
        and *) "distinct tcbs" by simp_all
    qed fact+

    from tcbp Cons.prems have tcbp_not_tcb': "tcbp \<noteq> tcb'" by clarsimp
    from tcbp have tcbsnz: "tcbs \<noteq> []" by clarsimp
    hence hd_tcbs: "hd tcbs = tcbs ! 0" by (simp add: hd_conv_nth)

    show ?case
    proof (rule conjI)
      show "?prev tcb (tcb' # tcbs) qprev'"
        using ih [THEN conjunct1] tcbp_not_tcb' hd_tcbs tcbsnz
        apply (clarsimp split: if_split_asm)
        apply fastforce
        apply (rule_tac x = "Suc n" in exI)
        apply simp
        done
    next
      show "?next tcb (tcb' # tcbs)"
        using ih [THEN conjunct2] tcbp_not_tcb' hd_tcbs tcbsnz
        apply (clarsimp split: if_split_asm)
        apply (rule_tac x = "Suc n" in exI)
        apply simp
        done
    qed
  qed
qed

lemma tcb_queue_memberD:
  assumes queue_rel: "tcb_queue_relation getNext getPrev (cslift s') queue qprev qhead"
  and      in_queue: "tcbp \<in> set queue"
  and     valid_ntfn: "\<forall>t\<in>set queue. tcb_at' t s"
  and        rf_sr: "(s, s') \<in> rf_sr"
  shows "\<exists>tcb. cslift s' (tcb_ptr_to_ctcb_ptr tcbp) = Some tcb"
  using assms
  apply -
  apply (drule (1) bspec)
  apply (drule (1) tcb_at_h_t_valid)
  apply (clarsimp simp add: h_t_valid_clift_Some_iff)
  done

lemma tcb_queue_valid_ptrsD:
  assumes in_queue: "tcbp \<in> set queue"
  and        rf_sr: "(s, s') \<in> rf_sr"
  and    valid_ntfn: "\<forall>t\<in>set queue. tcb_at' t s" "distinct queue"
  and    queue_rel: "tcb_queue_relation getNext getPrev (cslift s') queue NULL qhead"
  shows "\<exists>tcb. cslift s' (tcb_ptr_to_ctcb_ptr tcbp) = Some tcb
               \<and> (getPrev tcb \<noteq> NULL \<longrightarrow> s' \<Turnstile>\<^sub>c (getPrev tcb)
                                           \<and> getPrev tcb \<in> tcb_ptr_to_ctcb_ptr ` set queue)
               \<and> (getNext tcb \<noteq> NULL \<longrightarrow> s' \<Turnstile>\<^sub>c (getNext tcb)
                                          \<and>  getNext tcb \<in> tcb_ptr_to_ctcb_ptr ` set queue)"
  using assms
  apply -
  apply (frule (3) tcb_queue_memberD)
  apply (elim exE)
  apply (frule (3) tcb_queueD)
  apply (auto intro!: tcb_at_h_t_valid elim!: bspec split: if_split_asm)
  done

lemma tcb_queue_relation_restrict0:
  "set queue \<subseteq> S \<Longrightarrow> tcb_queue_relation getNext getPrev mp queue qprev qhead =
  tcb_queue_relation getNext getPrev (restrict_map mp (tcb_ptr_to_ctcb_ptr ` S)) queue qprev qhead"
proof (induct queue arbitrary: S qprev qhead)
  case Nil thus ?case by simp
next
  case (Cons tcb tcbs S' qprev' qhead')
  thus ?case
    using Cons by auto
qed

lemma tcb_queue_relation_restrict:
  "tcb_queue_relation getNext getPrev mp queue qprev qhead =
  tcb_queue_relation getNext getPrev (restrict_map mp (tcb_ptr_to_ctcb_ptr ` set queue)) queue qprev qhead"
  apply (rule tcb_queue_relation_restrict0)
  apply simp
  done

lemma tcb_queue_relation_only_next_prev:
  assumes mapeq: "option_map getNext \<circ> mp = option_map getNext \<circ> mp'" "option_map getPrev \<circ> mp = option_map getPrev \<circ> mp'"
  shows "tcb_queue_relation getNext getPrev mp queue qprev qhead =  tcb_queue_relation getNext getPrev mp' queue qprev qhead"
proof (induct queue arbitrary: qprev qhead)
  case Nil thus ?case by simp
next
  case (Cons tcb tcbs qprev' qhead')
  thus ?case
    apply clarsimp
    apply (rule iffI)
     apply clarsimp
     apply (frule compD [OF mapeq(1)])
     apply clarsimp
     apply (frule compD [OF mapeq(2)])
     apply clarsimp
    apply clarsimp
    apply (frule compD [OF mapeq(1) [symmetric]])
    apply clarsimp
    apply (frule compD [OF mapeq(2) [symmetric]])
    apply clarsimp
    done
qed


lemma tcb_queue_relation_cong:
  assumes queuec: "queue = queue'"
  and        qpc: "qprev = qprev'"
  and        qhc: "qhead = qhead'"
  and        mpc: "\<And>p. p \<in> tcb_ptr_to_ctcb_ptr ` set queue' \<Longrightarrow> mp p = mp' p"
  shows "tcb_queue_relation getNext getPrev mp queue qprev qhead =
  tcb_queue_relation getNext getPrev mp' queue' qprev' qhead'" (is "?LHS = ?RHS")
proof -
  have "?LHS = tcb_queue_relation getNext getPrev (mp |` (tcb_ptr_to_ctcb_ptr ` set queue')) queue' qprev' qhead'"
    by (simp add: queuec qpc qhc, subst tcb_queue_relation_restrict, rule refl)

  also have "\<dots> = tcb_queue_relation getNext getPrev (mp' |` (tcb_ptr_to_ctcb_ptr ` set queue')) queue' qprev' qhead'"
    by (simp add: mpc cong: restrict_map_cong)

  also have "\<dots> = ?RHS"
    by (simp add: tcb_queue_relation_restrict [symmetric])

  finally show ?thesis .
qed

lemma tcb_queue_relation'_cong:
  assumes queuec: "queue = queue'"
  and        qhc: "qhead = qhead'"
  and        qpc: "qend = qend'"
  and        mpc: "\<And>p. p \<in> tcb_ptr_to_ctcb_ptr ` set queue' \<Longrightarrow> mp p = mp' p"
  shows "tcb_queue_relation' getNext getPrev mp queue qhead qend =
  tcb_queue_relation' getNext getPrev mp' queue' qhead' qend'" (is "?LHS = ?RHS")
proof -
  have "?LHS = tcb_queue_relation' getNext getPrev (mp |` (tcb_ptr_to_ctcb_ptr ` set queue')) queue' qhead' qend'"
    by (clarsimp simp add: queuec qpc qhc tcb_queue_relation'_def , subst tcb_queue_relation_restrict, rule refl)

  also have "\<dots> = tcb_queue_relation' getNext getPrev (mp' |` (tcb_ptr_to_ctcb_ptr ` set queue')) queue' qhead' qend'"
    by (simp add: mpc cong: restrict_map_cong)

  also have "\<dots> = ?RHS"
    by (simp add: tcb_queue_relation'_def tcb_queue_relation_restrict [symmetric])

  finally show ?thesis .
qed


lemma tcb_at_not_NULL:
  assumes tat: "tcb_at' t s"
  shows "tcb_ptr_to_ctcb_ptr t \<noteq> NULL"
proof
  assume "tcb_ptr_to_ctcb_ptr t = NULL"
  with tat have "tcb_at' (ctcb_ptr_to_tcb_ptr NULL) s"
    apply -
    apply (erule subst)
    apply simp
    done

  hence "is_aligned (ctcb_ptr_to_tcb_ptr NULL) tcbBlockSizeBits"
    by (rule tcb_aligned')

  moreover have "ctcb_ptr_to_tcb_ptr NULL !! ctcb_size_bits"
    unfolding ctcb_ptr_to_tcb_ptr_def ctcb_offset_defs
    by simp
  ultimately show False by (simp add: is_aligned_nth ctcb_offset_defs objBits_defs)
qed

lemma tcb_queue_relation_not_NULL:
  assumes   tq: "tcb_queue_relation getNext getPrev mp queue qprev qhead"
  and valid_ep: "\<forall>t\<in>set queue. tcb_at' t s"
  shows   "\<forall>t \<in> set queue. tcb_ptr_to_ctcb_ptr t \<noteq> NULL"
proof (cases "queue = []")
  case True thus ?thesis by simp
next
  case False
  show ?thesis
  proof (rule ballI, rule notI)
    fix t
    assume tq: "t \<in> set queue" and "tcb_ptr_to_ctcb_ptr t = NULL"
    hence "ctcb_ptr_to_tcb_ptr NULL \<in> set queue"
      apply -
      apply (erule subst)
      apply simp
      done

    with valid_ep(1) have "tcb_at' (ctcb_ptr_to_tcb_ptr NULL) s" ..
    thus False
      apply -
      apply (drule tcb_at_not_NULL)
      apply simp
      done
  qed
qed

lemmas tcb_queue_relation_not_NULL' = bspec [OF tcb_queue_relation_not_NULL]

lemma tcb_queue_relation_head_hd:
  assumes   tq: "tcb_queue_relation getNext getPrev mp queue qprev qhead"
  and     tcbs: "queue \<noteq> []"
  shows   "ctcb_ptr_to_tcb_ptr qhead = hd queue"
  using assms
  apply (cases queue)
   apply simp
  apply simp
  done

lemma tcb_queue_relation_next_not_NULL:
  assumes   tq: "tcb_queue_relation getNext getPrev mp queue qprev qhead"
  and valid_ep: "\<forall>t\<in>set queue. tcb_at' t s" "distinct queue"
  and     tcbs: "queue \<noteq> []"
  shows   "qhead \<noteq> NULL"
proof -
  have "ctcb_ptr_to_tcb_ptr qhead \<in> set queue" using tq tcbs
    by (simp add: tcb_queue_relation_head_hd)

  with tq valid_ep(1) have "tcb_ptr_to_ctcb_ptr (ctcb_ptr_to_tcb_ptr qhead) \<noteq> NULL"
    by (rule tcb_queue_relation_not_NULL')

  thus ?thesis by simp
qed

lemma tcb_queue_relation_ptr_rel:
  assumes   tq: "tcb_queue_relation getNext getPrev mp queue qprev qhead"
  and valid_ep: "\<forall>t\<in>set queue. tcb_at' t s" "distinct queue"
  and   cs_tcb: "mp (tcb_ptr_to_ctcb_ptr tcbp) = Some tcb"
  and prev_not_queue: "ctcb_ptr_to_tcb_ptr qprev \<notin> set queue"
  and in_queue: "tcbp \<in> set queue"
  shows "tcb_ptr_to_ctcb_ptr tcbp \<noteq> getNext tcb \<and> tcb_ptr_to_ctcb_ptr tcbp \<noteq> getPrev tcb
         \<and> (getNext tcb \<noteq> NULL \<longrightarrow> getNext tcb \<noteq> getPrev tcb)"
  using tq valid_ep in_queue cs_tcb prev_not_queue
  apply -
  apply (frule (3) tcb_queueD)
  apply (frule (2) tcb_queue_relation_not_NULL')
  apply (simp split: if_split_asm)
     apply (rule not_sym)
     apply (rule notI)
     apply simp
    apply (clarsimp simp: inj_eq distinct_conv_nth)
   apply (intro conjI impI)
     apply (clarsimp simp: inj_eq distinct_conv_nth)
    apply (rule not_sym)
    apply clarsimp
   apply clarsimp
  apply (clarsimp simp: inj_eq)
  apply (intro conjI impI)
     apply (clarsimp simp: distinct_conv_nth)
    apply (erule_tac s = "queue ! Suc n" in subst)
    apply (clarsimp simp: distinct_conv_nth)
   apply clarsimp
  apply (case_tac "na = Suc n")
   apply hypsubst
    apply (clarsimp simp: distinct_conv_nth)
  apply (clarsimp simp: distinct_conv_nth)
  done

lemma distinct_cons_nth:
  assumes dxs: "distinct xs"
  and      ln: "n < length xs"
  and      x: "x \<notin> set xs"
  shows    "(x # xs) ! n \<noteq> xs ! n"
proof
  assume n: "(x # xs) ! n = xs ! n"
  have ln': "n < length (x # xs)" using ln by simp
  have sln: "Suc n < length (x # xs)" using ln by simp

  from n have "(x # xs) ! n = (x # xs) ! Suc n" by simp
  moreover have "distinct (x # xs)" using dxs x by simp
  ultimately show False
    unfolding distinct_conv_nth
    apply -
    apply (drule spec, drule mp [OF _ ln'])
    apply (drule spec, drule mp [OF _ sln])
    apply simp
    done
qed

lemma distinct_nth:
  assumes dist: "distinct xs"
  and     ln: "n < length xs"
  and     lm: "m < length xs"
  shows   "(xs ! n = xs ! m) = (n = m)"
  using dist ln lm
  apply (cases "n = m")
   apply simp
  apply (clarsimp simp: distinct_conv_nth)
  done

lemma distinct_nth_cons:
  assumes dist: "distinct xs"
  and     xxs: "x \<notin> set xs"
  and     ln: "n < length xs"
  and     lm: "m < length xs"
  shows   "((x # xs) ! n = xs ! m) = (n = Suc m)"
proof (cases "n = Suc m")
  case True
  thus ?thesis by simp
next
  case False

  have ln': "n < length (x # xs)" using ln by simp
  have lm': "Suc m < length (x # xs)" using lm by simp

  have "distinct (x # xs)" using dist xxs by simp
  thus ?thesis using False
    unfolding distinct_conv_nth
    apply -
    apply (drule spec, drule mp [OF _ ln'])
    apply (drule spec, drule mp [OF _ lm'])
    apply clarsimp
    done
qed

lemma distinct_nth_cons':
  assumes dist: "distinct xs"
  and     xxs: "x \<notin> set xs"
  and     ln: "n < length xs"
  and     lm: "m < length xs"
  shows   "(xs ! n = (x # xs) ! m) = (m = Suc n)"
proof (cases "m = Suc n")
  case True
  thus ?thesis by simp
next
  case False

  have ln': "Suc n < length (x # xs)" using ln by simp
  have lm': "m < length (x # xs)" using lm by simp

  have "distinct (x # xs)" using dist xxs by simp
  thus ?thesis using False
    unfolding distinct_conv_nth
    apply -
    apply (drule spec, drule mp [OF _ ln'])
    apply (drule spec, drule mp [OF _ lm'])
    apply clarsimp
    done
qed

lemma nth_first_not_member:
  assumes xxs: "x \<notin> set xs"
  and     ln: "n < length xs"
  shows   "((x # xs) ! n = x) = (n = 0)"
  using xxs ln
  apply (cases n)
   apply simp
  apply clarsimp
  done

lemma tcb_queue_next_prev:
  assumes    qr: "tcb_queue_relation getNext getPrev mp queue qprev qhead"
  and       valid_ep: "\<forall>t\<in>set queue. tcb_at' t s" "distinct queue"
  and       tcb: "mp (tcb_ptr_to_ctcb_ptr tcbp) = Some tcb"
  and      tcb': "mp (tcb_ptr_to_ctcb_ptr tcbp') = Some tcb'"
  and        tq: "tcbp \<in> set queue" "tcbp' \<in> set queue"
  and prev_not_queue: "ctcb_ptr_to_tcb_ptr qprev \<notin> set queue"
  and      tcbs: "tcbp \<noteq> tcbp'"
  shows    "(getNext tcb = tcb_ptr_to_ctcb_ptr tcbp') =
            (getPrev tcb' = tcb_ptr_to_ctcb_ptr tcbp)"
  using qr valid_ep prev_not_queue tq tcb tcb' tcbs
  apply -
  apply (frule (1) tcb_queueD)
    apply (rule tq(1))
   apply (rule tcb)
  apply (frule (1) tcb_queueD)
    apply (rule tq(2))
   apply (rule tcb')
  apply (cases queue)
   apply simp
  apply (cut_tac bspec [OF tcb_queue_relation_not_NULL, OF qr valid_ep(1) tq(1)])
  apply (cut_tac bspec [OF tcb_queue_relation_not_NULL, OF qr valid_ep(1) tq(2)])
  apply (simp add: inj_eq split: if_split_asm)
           apply clarsimp
          apply clarsimp
         subgoal by (clarsimp simp: last_conv_nth  distinct_nth distinct_nth_cons)
        apply (clarsimp simp: last_conv_nth distinct_nth distinct_nth_cons)
        apply (subgoal_tac "list ! Suc na \<noteq> tcbp'")
         apply clarsimp
        apply clarsimp
       subgoal by (clarsimp  simp: last_conv_nth distinct_nth distinct_nth_cons nth_first_not_member)
      subgoal by (fastforce  simp: last_conv_nth distinct_nth distinct_nth_cons nth_first_not_member)
     subgoal by (clarsimp  simp: last_conv_nth distinct_nth distinct_nth_cons distinct_nth_cons' nth_first_not_member)
    by (fastforce simp: last_conv_nth distinct_nth distinct_nth_cons distinct_nth_cons' nth_first_not_member)


lemma null_not_in:
  "\<lbrakk>tcb_queue_relation getNext getPrev mp queue qprev qhead; \<forall>t\<in>set queue. tcb_at' t s; distinct queue\<rbrakk>
   \<Longrightarrow> ctcb_ptr_to_tcb_ptr NULL \<notin> set queue"
    apply -
    apply (rule notI)
    apply (drule (2) tcb_queue_relation_not_NULL')
    apply simp
    done

lemma tcb_queue_relationI':
  "\<lbrakk> tcb_queue_relation getNext getPrev hp queue NULL qhead;
     qend = (if queue = [] then NULL else (tcb_ptr_to_ctcb_ptr (last queue))) \<rbrakk>
  \<Longrightarrow> tcb_queue_relation' getNext getPrev hp queue qhead qend"
  unfolding tcb_queue_relation'_def
  by simp

lemma tcb_queue_relationE':
  "\<lbrakk> tcb_queue_relation' getNext getPrev hp queue qhead qend;
   \<lbrakk> tcb_queue_relation getNext getPrev hp queue NULL qhead;
     qend = (if queue = [] then NULL else (tcb_ptr_to_ctcb_ptr (last queue))) \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  unfolding tcb_queue_relation'_def
  by simp

lemma tcb_queue_relation'_queue_rel:
  "tcb_queue_relation' getNext getPrev hp queue qhead qend
  \<Longrightarrow> tcb_queue_relation getNext getPrev hp queue NULL qhead"
  unfolding tcb_queue_relation'_def
  by simp

lemma tcb_queue_singleton_iff:
  assumes queue_rel: "tcb_queue_relation getNext getPrev mp queue NULL qhead"
  and      in_queue: "tcbp \<in> set queue"
  and    valid_ntfn: "\<forall>t\<in>set queue. tcb_at' t s" "distinct queue"
  and       cs_tcb: "mp (tcb_ptr_to_ctcb_ptr tcbp) = Some tcb"
  shows    "(queue = [tcbp]) = (getNext tcb = NULL \<and> getPrev tcb = NULL)"
proof (rule iffI)
  assume "queue = [tcbp]"
  thus "(getNext tcb = NULL \<and> getPrev tcb = NULL)" using queue_rel cs_tcb
    by clarsimp
next
  assume asms: "getNext tcb = NULL \<and> getPrev tcb = NULL"
  hence "hd queue = tcbp" using queue_rel valid_ntfn in_queue cs_tcb
    apply -
    apply (drule (3) tcb_queueD)
    apply (rule classical)
    apply clarsimp
    apply (cut_tac x = "queue ! n" in bspec [OF tcb_queue_relation_not_NULL [OF  queue_rel valid_ntfn(1)]])
    apply clarsimp
    apply simp
    done
  moreover have "last queue = tcbp" using queue_rel valid_ntfn in_queue cs_tcb asms
    apply -
    apply (drule (3) tcb_queueD)
    apply (rule classical)
    apply clarsimp
    apply (cut_tac x = "queue ! Suc n" in bspec [OF tcb_queue_relation_not_NULL [OF  queue_rel valid_ntfn(1)]])
    apply clarsimp
    apply simp
    done
  moreover have "queue \<noteq> []" using in_queue by clarsimp
  ultimately show "queue = [tcbp]" using valid_ntfn in_queue
    apply clarsimp
    apply (simp add: hd_conv_nth last_conv_nth nth_eq_iff_index_eq)
    apply (cases queue)
    apply simp
    apply simp
    done
qed


lemma distinct_remove1_take_drop:
  "\<lbrakk> distinct ls; n < length ls \<rbrakk> \<Longrightarrow> remove1 (ls ! n) ls = (take n ls) @ drop (Suc n) ls"
proof (induct ls arbitrary: n)
  case Nil thus ?case by simp
next
  case (Cons x xs n)

  show ?case
  proof (cases n)
    case 0
    thus ?thesis by simp
  next
    case (Suc m)

    hence "((x # xs) ! n) \<noteq> x" using Cons.prems by clarsimp
    thus ?thesis using Suc Cons.prems by (clarsimp simp add: Cons.hyps)
  qed
qed


definition
  "upd_unless_null \<equiv> \<lambda>p v f. if p = NULL then f else fun_upd f p (Some v)"

lemma upd_unless_null_cong_helper:
  "\<And>p p' v mp S. \<lbrakk> p' \<in> tcb_ptr_to_ctcb_ptr ` S; ctcb_ptr_to_tcb_ptr p \<notin> S \<rbrakk> \<Longrightarrow> (upd_unless_null p v mp) p' = mp p'"
  unfolding upd_unless_null_def
  apply simp
  apply (intro impI conjI)
  apply (erule imageE)
  apply hypsubst
  apply (simp only: ctcb_ptr_to_ctcb_ptr)
  apply blast
  done

lemma tcbDequeue_update0:
  assumes in_queue: "tcbp \<in> set queue"
  and    valid_ntfn: "\<forall>t\<in>set queue. tcb_at' t s" "distinct queue"
  and    queue_rel: "tcb_queue_relation tn tp mp queue qprev qhead"
  and prev_not_queue: "ctcb_ptr_to_tcb_ptr qprev \<notin> set queue"
  and       cs_tcb: "mp (tcb_ptr_to_ctcb_ptr tcbp) = Some tcb"
  and            f: "\<And>v f g. tn (tn_update f v) = f (tn v) \<and> tp (tp_update g v) = g (tp v)
                           \<and> tn (tp_update f v) = tn v \<and> tp (tn_update g v) = tp v"
  shows "tcb_queue_relation tn tp
          (upd_unless_null (tn tcb) (tp_update (\<lambda>_. tp tcb) (the (mp (tn tcb))))
            (upd_unless_null (tp tcb) (tn_update (\<lambda>_. tn tcb) (the (mp (tp tcb)))) mp))
            (remove1 tcbp queue)
            (if tcb_ptr_to_ctcb_ptr tcbp = qhead then tp tcb else qprev)
            (if tcb_ptr_to_ctcb_ptr tcbp = qhead then tn tcb else qhead)"
  (is "tcb_queue_relation tn tp ?mp (remove1 tcbp queue) (?qprev qprev qhead) (?qhead qhead)")
  using queue_rel valid_ntfn prev_not_queue in_queue
proof (induct queue arbitrary: qprev qhead)
  case Nil
  thus ?case by simp
next
  case (Cons tcb' tcbs qprev' qhead')

  have "tcbp = tcb' \<or> tcbp \<in> set tcbs" using Cons.prems by simp
  thus ?case
  proof
    assume tcbp: "tcbp = tcb'"
    hence qp: "qprev' = tp tcb" and qh: "qhead' = tcb_ptr_to_ctcb_ptr tcb'"
      using Cons.prems cs_tcb by auto

    from Cons.prems have tq: "tcb_queue_relation tn tp mp tcbs (tcb_ptr_to_ctcb_ptr tcb') (tn tcb)"
      using Cons.prems cs_tcb tcbp by clarsimp

    note ind_prems = Cons.prems
    note ind_hyp   = Cons.hyps

    show ?thesis
    proof (cases tcbs)
      case Nil thus ?thesis using Cons.prems tcbp cs_tcb by clarsimp
    next
      case (Cons tcbs_hd tcbss)

      have nnull: "tn tcb \<noteq> NULL" using tq
      proof (rule tcb_queue_relation_next_not_NULL)
        from ind_prems show "\<forall>t\<in>set tcbs. tcb_at' t s"
          and "distinct tcbs" by simp_all
        show "tcbs \<noteq> []" using Cons by simp
      qed

      from Cons ind_prems have "tcbs_hd \<notin> set tcbss" by simp
      hence mpeq: "\<And>p. p \<in> tcb_ptr_to_ctcb_ptr ` set tcbss \<Longrightarrow> ?mp p = mp p"
        using tq cs_tcb tcbp Cons nnull ind_prems
        apply -
        apply (subst upd_unless_null_cong_helper, assumption, clarsimp)+
        apply simp
        done

      have "tcb_ptr_to_ctcb_ptr tcbp \<noteq> tn tcb \<and> tcb_ptr_to_ctcb_ptr tcbp \<noteq> tp tcb
         \<and> tn tcb \<noteq> tp tcb" using tq cs_tcb ind_prems nnull
        apply -
        apply (drule (5) tcb_queue_relation_ptr_rel)
        apply clarsimp
        done

      hence "?mp (tcb_ptr_to_ctcb_ptr tcbs_hd) = Some (tp_update (\<lambda>_. tp tcb) (the (mp (tn tcb))))"
        using qp qh tq cs_tcb tcbp Cons nnull
        by (simp add: upd_unless_null_def)

      thus ?thesis using qp qh tq cs_tcb tcbp Cons nnull
        apply (simp (no_asm) add: tcbp Cons split del: if_split)
        apply (subst tcb_queue_relation_cong [OF refl refl refl mpeq])
        apply assumption
        apply (clarsimp simp: f)
        done
    qed
  next
    assume inset: "tcbp \<in> set tcbs"
    hence  tcbp: "tcbp \<noteq> tcb'" using Cons.prems by clarsimp

    obtain tcb2 where cs_tcb2: "mp (tcb_ptr_to_ctcb_ptr tcb') = Some tcb2"
      and rel2: "tcb_queue_relation tn tp mp tcbs (tcb_ptr_to_ctcb_ptr tcb') (tn tcb2)"
      and qh: "qhead' = tcb_ptr_to_ctcb_ptr tcb'"
      and qp: "qprev' = tp tcb2"
      using Cons.prems
      by clarsimp

    have nnull: "tcb_ptr_to_ctcb_ptr tcb' \<noteq> NULL" using Cons.prems
      apply -
      apply (erule (1) tcb_queue_relation_not_NULL')
      apply simp
      done

    have ih: "tcb_queue_relation tn tp ?mp (remove1 tcbp tcbs)
                                     (?qprev (tcb_ptr_to_ctcb_ptr tcb') (tn tcb2))
                                     (?qhead (tn tcb2))" using rel2
    proof (rule Cons.hyps)
      from Cons.prems show "\<forall>t\<in>set tcbs. tcb_at' t s"
        and "distinct tcbs"
        and "ctcb_ptr_to_tcb_ptr (tcb_ptr_to_ctcb_ptr tcb') \<notin> set tcbs" by simp_all
    qed fact

    have tcb_next: "tn tcb \<noteq> tcb_ptr_to_ctcb_ptr tcb'"
      using Cons.prems tcb_queue_next_prev[OF Cons.prems(1), OF _ _ cs_tcb cs_tcb2]
            tcbp qp[symmetric]
      by auto

    show ?thesis using tcbp
    proof (cases "tn tcb2 = tcb_ptr_to_ctcb_ptr tcbp")
      case True
      hence tcb_prev: "tp tcb = tcb_ptr_to_ctcb_ptr tcb'" using Cons.prems cs_tcb2 cs_tcb not_sym [OF tcbp]
        apply -
        apply (subst tcb_queue_next_prev [symmetric], assumption+)
         apply simp
         apply simp
         apply simp
         apply (rule not_sym [OF tcbp])
        apply simp
        done

      hence "?mp (tcb_ptr_to_ctcb_ptr tcb') = Some (tn_update (\<lambda>_. tn tcb) tcb2)"
        using tcb_next nnull cs_tcb2 unfolding upd_unless_null_def by simp

      thus ?thesis using tcbp cs_tcb qh qp True ih tcb_prev
        by (simp add: inj_eq f)
    next
      case False
      hence tcb_prev: "tp tcb \<noteq> tcb_ptr_to_ctcb_ptr tcb'"
        using Cons.prems cs_tcb2 cs_tcb not_sym [OF tcbp]
        apply -
        apply (subst tcb_queue_next_prev [symmetric], assumption+)
         apply simp
         apply simp
         apply simp
         apply (rule not_sym [OF tcbp])
        apply simp
        done
      hence "?mp (tcb_ptr_to_ctcb_ptr tcb') = Some tcb2"
        using tcb_next nnull cs_tcb2 unfolding upd_unless_null_def by simp

      thus ?thesis using tcbp cs_tcb qh qp False ih tcb_prev
        by (simp add: inj_eq)
    qed
  qed
qed

lemma tcbDequeue_update:
  assumes queue_rel: "tcb_queue_relation' tn tp mp queue qhead qend"
  and      in_queue: "tcbp \<in> set queue"
  and    valid_ntfn: "\<forall>t\<in>set queue. tcb_at' t s" "distinct queue"
  and       cs_tcb: "mp (tcb_ptr_to_ctcb_ptr tcbp) = Some tcb"
  and            f: "\<And>v f g. tn (tn_update f v) = f (tn v) \<and> tp (tp_update g v) = g (tp v)
                           \<and> tn (tp_update f v) = tn v \<and> tp (tn_update g v) = tp v"
  shows "tcb_queue_relation' tn tp
          (upd_unless_null (tn tcb) (tp_update (\<lambda>_. tp tcb) (the (mp (tn tcb))))
            (upd_unless_null (tp tcb) (tn_update (\<lambda>_. tn tcb) (the (mp (tp tcb)))) mp))
            (remove1 tcbp queue)
            (if tp tcb = NULL then tn tcb else qhead)
            (if tn tcb = NULL then tp tcb else qend)"
proof -
  have ne: "NULL = (if tcb_ptr_to_ctcb_ptr tcbp = qhead then tp tcb else NULL)"
    using queue_rel in_queue cs_tcb
    apply -
    apply (drule tcb_queue_relation'_queue_rel)
    apply (clarsimp split: if_split)
    apply (cases queue)
     apply simp
    apply clarsimp
    done

  have if2: "(if tp tcb = NULL then tn tcb else qhead) =
             (if tcb_ptr_to_ctcb_ptr tcbp = qhead then tn tcb else qhead)"
    using tcb_queue_relation'_queue_rel [OF queue_rel] in_queue cs_tcb valid_ntfn
    apply -
    apply (cases queue)
     apply simp
    apply (frule (3) tcb_queueD)
    apply (simp add: inj_eq)
    apply (intro impI)
    apply simp
    apply (elim conjE exE)
    apply (cut_tac x = "queue ! n"
      in bspec [OF tcb_queue_relation_not_NULL [OF  tcb_queue_relation'_queue_rel [OF queue_rel] valid_ntfn(1)]])
    apply (rule nth_mem)
    apply clarsimp
    apply clarsimp
    done

  note null_not_in' = null_not_in [OF tcb_queue_relation'_queue_rel [OF queue_rel] valid_ntfn(1) valid_ntfn(2)]

  show ?thesis
  proof (rule tcb_queue_relationI')
    show "tcb_queue_relation tn tp
     (upd_unless_null (tn tcb)
       (tp_update (\<lambda>_. tp tcb) (the (mp (tn tcb))))
       (upd_unless_null (tp tcb)
         (tn_update (\<lambda>_. tn tcb) (the (mp (tp tcb)))) mp))
     (remove1 tcbp queue) NULL
     (if tp tcb = NULL then tn tcb else qhead)"
      using in_queue valid_ntfn tcb_queue_relation'_queue_rel [OF queue_rel] null_not_in' cs_tcb
      by (subst ne, subst if2, rule tcbDequeue_update0[rotated -1, OF f])
  next
    have r1: "(remove1 tcbp queue = []) = (tn tcb = NULL \<and> tp tcb = NULL)"
      using in_queue tcb_queue_relation'_queue_rel [OF queue_rel] cs_tcb valid_ntfn null_not_in'
      apply -
      apply (subst tcb_queue_singleton_iff [symmetric], assumption+)
      apply (fastforce simp: remove1_empty)
      done
    have "queue \<noteq> []" using in_queue by clarsimp
    thus "(if tn tcb = NULL then tp tcb else qend) =
          (if remove1 tcbp queue = [] then NULL else tcb_ptr_to_ctcb_ptr (last (remove1 tcbp queue)))"
      using queue_rel in_queue cs_tcb valid_ntfn
        tcb_queue_relation_not_NULL [OF tcb_queue_relation'_queue_rel [OF queue_rel] valid_ntfn(1)]
      apply -
      apply (erule tcb_queue_relationE')
      apply (frule (3) tcb_queueD)
      apply (subst r1)
      apply simp
      apply (intro impI conjI)
       apply (subgoal_tac "tcbp = last queue")
        apply simp
        apply (subgoal_tac "(remove1 (last queue) queue) \<noteq> []")
         apply (clarsimp simp: inj_eq last_conv_nth nth_eq_iff_index_eq length_remove1
           distinct_remove1_take_drop split: if_split_asm)
         apply arith
        apply (clarsimp simp: remove1_empty last_conv_nth hd_conv_nth nth_eq_iff_index_eq not_le split: if_split_asm)
        apply (cases queue)
         apply simp
        apply simp
       apply (fastforce simp: inj_eq split: if_split_asm)
      apply (clarsimp simp: last_conv_nth distinct_remove1_take_drop nth_eq_iff_index_eq inj_eq split: if_split_asm)
       apply arith
      apply (simp add: nth_append min_def nth_eq_iff_index_eq)
      apply clarsimp
      apply arith
      done
  qed
qed

lemmas tcbEPDequeue_update
    = tcbDequeue_update[where tn=tcbEPNext_C and tn_update=tcbEPNext_C_update
                          and tp=tcbEPPrev_C and tp_update=tcbEPPrev_C_update,
                        simplified]

lemma tcb_queue_relation_ptr_rel':
  assumes   tq: "tcb_queue_relation getNext getPrev mp queue NULL qhead"
  and valid_ep: "\<forall>t\<in>set queue. tcb_at' t s" "distinct queue"
  and   cs_tcb: "mp (tcb_ptr_to_ctcb_ptr tcbp) = Some tcb"
  and in_queue: "tcbp \<in> set queue"
  shows "tcb_ptr_to_ctcb_ptr tcbp \<noteq> getNext tcb \<and> tcb_ptr_to_ctcb_ptr tcbp \<noteq> getPrev tcb
         \<and> (getNext tcb \<noteq> NULL \<longrightarrow> getNext tcb \<noteq> getPrev tcb)"
  using tq valid_ep cs_tcb null_not_in [OF tq valid_ep(1) valid_ep(2)] in_queue
  by (rule tcb_queue_relation_ptr_rel)

lemma tcb_queue_head_empty_iff:
  "\<lbrakk> tcb_queue_relation getNext getPrev mp queue NULL qhead; \<forall>t \<in> set queue. tcb_at' t s \<rbrakk> \<Longrightarrow>
  (qhead = NULL) = (queue = [])"
  apply (rule classical)
  apply (cases queue)
   apply simp
  apply (frule (1) tcb_queue_relation_not_NULL)
  apply clarsimp
  done

lemma ctcb_ptr_to_tcb_ptr_aligned:
  assumes al: "is_aligned (ctcb_ptr_to_tcb_ptr ptr) tcbBlockSizeBits"
  shows   "is_aligned (ptr_val ptr) ctcb_size_bits"
proof -
  have "is_aligned (ptr_val (tcb_ptr_to_ctcb_ptr (ctcb_ptr_to_tcb_ptr ptr))) ctcb_size_bits"
    unfolding tcb_ptr_to_ctcb_ptr_def using al
    apply simp
    apply (erule aligned_add_aligned)
    apply (unfold ctcb_offset_defs, rule is_aligned_triv)
    apply (simp add: word_bits_conv objBits_defs)+
    done
  thus ?thesis by simp
qed

lemma ctcb_size_bits_ge_4: "4 \<le> ctcb_size_bits"
  by (simp add: ctcb_size_bits_def)

lemma tcb_queue_relation_next_mask:
  assumes   tq: "tcb_queue_relation getNext getPrev mp queue NULL qhead"
  and valid_ep: "\<forall>t\<in>set queue. tcb_at' t s" "distinct queue"
  and   cs_tcb: "mp (tcb_ptr_to_ctcb_ptr tcbp) = Some tcb"
  and in_queue: "tcbp \<in> set queue"
  and     bits: "bits \<le> ctcb_size_bits"
  shows "ptr_val (getNext tcb) && ~~ mask bits = ptr_val (getNext tcb)"
proof (cases "(getNext tcb) = NULL")
  case True
  thus ?thesis by simp
next
  case False

  hence "ctcb_ptr_to_tcb_ptr (getNext tcb) \<in> set queue" using assms
    apply -
    apply (drule (3) tcb_queueD)
    apply (clarsimp split: if_split_asm)
    done

  with valid_ep(1) have "tcb_at' (ctcb_ptr_to_tcb_ptr (getNext tcb)) s" ..
  hence "is_aligned (ctcb_ptr_to_tcb_ptr (getNext tcb)) tcbBlockSizeBits" by (rule tcb_aligned')
  hence "is_aligned (ptr_val (getNext tcb)) ctcb_size_bits" by (rule ctcb_ptr_to_tcb_ptr_aligned)
  thus ?thesis using bits by (simp add: is_aligned_neg_mask)
qed

lemma tcb_queue_relation_prev_mask:
  assumes   tq: "tcb_queue_relation getNext getPrev mp queue NULL qhead"
  and valid_ep: "\<forall>t\<in>set queue. tcb_at' t s" "distinct queue"
  and   cs_tcb: "mp (tcb_ptr_to_ctcb_ptr tcbp) = Some tcb"
  and in_queue: "tcbp \<in> set queue"
  and     bits: "bits \<le> ctcb_size_bits"
  shows "ptr_val (getPrev tcb) && ~~ mask bits = ptr_val (getPrev tcb)"
proof (cases "(getPrev tcb) = NULL")
  case True
  thus ?thesis by simp
next
  case False

  hence "ctcb_ptr_to_tcb_ptr (getPrev tcb) \<in> set queue" using assms
    apply -
    apply (drule (3) tcb_queueD)
    apply (clarsimp split: if_split_asm)
    done

  with valid_ep(1) have "tcb_at' (ctcb_ptr_to_tcb_ptr (getPrev tcb)) s" ..
  hence "is_aligned (ctcb_ptr_to_tcb_ptr (getPrev tcb)) tcbBlockSizeBits" by (rule tcb_aligned')
  hence "is_aligned (ptr_val (getPrev tcb)) ctcb_size_bits" by (rule ctcb_ptr_to_tcb_ptr_aligned)
  thus ?thesis using bits by (simp add: is_aligned_neg_mask)
qed

lemma tcb_queue_relation'_next_mask:
  assumes   tq: "tcb_queue_relation' getNext getPrev mp queue qhead qend"
  and valid_ep: "\<forall>t\<in>set queue. tcb_at' t s" "distinct queue"
  and   cs_tcb: "mp (tcb_ptr_to_ctcb_ptr tcbp) = Some tcb"
  and in_queue: "tcbp \<in> set queue"
  and     bits: "bits \<le> ctcb_size_bits"
  shows "ptr_val (getNext tcb) && ~~ mask bits = ptr_val (getNext tcb)"
  by (rule tcb_queue_relation_next_mask [OF tcb_queue_relation'_queue_rel], fact+)

lemma tcb_queue_relation'_prev_mask:
  assumes   tq: "tcb_queue_relation' getNext getPrev mp queue qhead qend"
  and valid_ep: "\<forall>t\<in>set queue. tcb_at' t s" "distinct queue"
  and   cs_tcb: "mp (tcb_ptr_to_ctcb_ptr tcbp) = Some tcb"
  and in_queue: "tcbp \<in> set queue"
  and     bits: "bits \<le> ctcb_size_bits"
  shows "ptr_val (getPrev tcb) && ~~ mask bits = ptr_val (getPrev tcb)"
  by (rule tcb_queue_relation_prev_mask [OF tcb_queue_relation'_queue_rel], fact+)

lemma tcb_queue_relation_next_sign:
  assumes
    "tcb_queue_relation getNext getPrev mp queue NULL qhead" and
    valid_ep: "\<forall>t\<in>set queue. tcb_at' t s"
    "distinct queue"
    "mp (tcb_ptr_to_ctcb_ptr tcbp) = Some tcb"
    "tcbp \<in> set queue"  and
    canon: "pspace_canonical' s"
  shows "sign_extend 47 (ptr_val (getNext tcb)) = ptr_val (getNext tcb)"
proof (cases "(getNext tcb) = NULL")
  case True
  thus ?thesis by simp
next
  case False

  hence "ctcb_ptr_to_tcb_ptr (getNext tcb) \<in> set queue" using assms
    apply -
    apply (drule (3) tcb_queueD)
    apply (clarsimp split: if_split_asm)
    done

  with valid_ep(1) have tcb: "tcb_at' (ctcb_ptr_to_tcb_ptr (getNext tcb)) s" ..
  with canon have "canonical_address (ctcb_ptr_to_tcb_ptr (getNext tcb))" by (simp add: obj_at'_is_canonical)
  moreover
  have "is_aligned (ctcb_ptr_to_tcb_ptr (getNext tcb)) tcbBlockSizeBits" using tcb by (rule tcb_aligned')
  ultimately
  have "canonical_address (ptr_val (getNext tcb))" by (rule canonical_address_ctcb_ptr)
  thus ?thesis
    by (simp add: sign_extend_canonical_address[symmetric])
qed

lemma tcb_queue_relation'_next_sign:
  "\<lbrakk> tcb_queue_relation' getNext getPrev mp queue qhead qend; \<forall>t\<in>set queue. tcb_at' t s;
     distinct queue; mp (tcb_ptr_to_ctcb_ptr tcbp) = Some tcb; tcbp \<in> set queue; pspace_canonical' s\<rbrakk>
\<Longrightarrow> sign_extend 47 (ptr_val (getNext tcb)) = ptr_val (getNext tcb)"
  by (rule tcb_queue_relation_next_sign [OF tcb_queue_relation'_queue_rel])

lemma tcb_queue_relation_prev_sign:
  assumes
    "tcb_queue_relation getNext getPrev mp queue NULL qhead" and
    valid_ep: "\<forall>t\<in>set queue. tcb_at' t s"
    "distinct queue"
    "mp (tcb_ptr_to_ctcb_ptr tcbp) = Some tcb"
    "tcbp \<in> set queue"  and
    canon: "pspace_canonical' s"
  shows "sign_extend 47 (ptr_val (getPrev tcb)) = ptr_val (getPrev tcb)"
proof (cases "(getPrev tcb) = NULL")
  case True
  thus ?thesis by simp
next
  case False

  hence "ctcb_ptr_to_tcb_ptr (getPrev tcb) \<in> set queue" using assms
    apply -
    apply (drule (3) tcb_queueD)
    apply (clarsimp split: if_split_asm)
    done

  with valid_ep(1) have tcb: "tcb_at' (ctcb_ptr_to_tcb_ptr (getPrev tcb)) s" ..
  with canon have "canonical_address (ctcb_ptr_to_tcb_ptr (getPrev tcb))" by (simp add: obj_at'_is_canonical)
  moreover
  have "is_aligned (ctcb_ptr_to_tcb_ptr (getPrev tcb)) tcbBlockSizeBits" using tcb by (rule tcb_aligned')
  ultimately
  have "canonical_address (ptr_val (getPrev tcb))" by (rule canonical_address_ctcb_ptr)
  thus ?thesis
    by (simp add: sign_extend_canonical_address[symmetric])
qed

lemma tcb_queue_relation'_prev_sign:
  "\<lbrakk> tcb_queue_relation' getNext getPrev mp queue qhead qend; \<forall>t\<in>set queue. tcb_at' t s;
     distinct queue; mp (tcb_ptr_to_ctcb_ptr tcbp) = Some tcb; tcbp \<in> set queue; pspace_canonical' s\<rbrakk>
\<Longrightarrow> sign_extend 47 (ptr_val (getPrev tcb)) = ptr_val (getPrev tcb)"
  by (rule tcb_queue_relation_prev_sign [OF tcb_queue_relation'_queue_rel])

lemma ntfn_ep_disjoint:
  assumes  srs: "sym_refs (state_refs_of' s)"
  and     epat: "ko_at' ep epptr s"
  and    ntfnat: "ko_at' ntfn ntfnptr s"
  and  ntfnq: "isWaitingNtfn (ntfnObj ntfn)"
  and   epq: "isSendEP ep \<or> isRecvEP ep"
  shows  "set (epQueue ep) \<inter> set (ntfnQueue (ntfnObj ntfn)) = {}"
  using srs epat ntfnat ntfnq epq
  apply -
  apply (subst disjoint_iff_not_equal, intro ballI, rule notI)
  apply (drule sym_refs_ko_atD', clarsimp)+
  apply clarsimp
  apply (clarsimp simp: isWaitingNtfn_def isSendEP_def isRecvEP_def
                 split: ntfn.splits endpoint.splits)
   apply (drule bspec, fastforce simp: ko_wp_at'_def)+
   apply (fastforce simp: ko_wp_at'_def refs_of_rev')
  apply (drule bspec, fastforce simp: ko_wp_at'_def)+
  apply (fastforce simp: ko_wp_at'_def refs_of_rev')
  done

lemma ntfn_ntfn_disjoint:
  assumes  srs: "sym_refs (state_refs_of' s)"
  and    ntfnat: "ko_at' ntfn ntfnptr s"
  and   ntfnat': "ko_at' ntfn' ntfnptr' s"
  and     ntfnq: "isWaitingNtfn (ntfnObj ntfn)"
  and    ntfnq': "isWaitingNtfn (ntfnObj ntfn')"
  and      neq: "ntfnptr' \<noteq> ntfnptr"
  shows  "set (ntfnQueue (ntfnObj ntfn)) \<inter> set (ntfnQueue (ntfnObj ntfn')) = {}"
  using srs ntfnat ntfnat' ntfnq ntfnq' neq
  apply -
  apply (subst disjoint_iff_not_equal, intro ballI, rule notI)
  apply (drule sym_refs_ko_atD', clarsimp)+
  apply clarsimp
  apply (clarsimp simp: isWaitingNtfn_def split: ntfn.splits)
   apply (drule bspec, fastforce simp: ko_wp_at'_def)+
   apply (clarsimp simp: ko_wp_at'_def refs_of_rev')
  done

lemma tcb_queue_relation'_empty[simp]:
  "tcb_queue_relation' getNext getPrev mp [] qhead qend =
      (qend = tcb_Ptr 0 \<and> qhead = tcb_Ptr 0)"
  by (simp add: tcb_queue_relation'_def)

lemma cnotification_relation_ntfn_queue:
  fixes ntfn :: "Structures_H.notification"
  defines "qs \<equiv> if isWaitingNtfn (ntfnObj ntfn) then set (ntfnQueue (ntfnObj ntfn)) else {}"
  assumes  ntfn: "cnotification_relation (cslift t) ntfn' b"
  and      srs: "sym_refs (state_refs_of' s)"
  and     koat: "ko_at' ntfn ntfnptr s"
  and    koat': "ko_at' ntfn' ntfnptr' s"
  and     mpeq: "(cslift t' |` (- (tcb_ptr_to_ctcb_ptr ` qs))) = (cslift t |` (- (tcb_ptr_to_ctcb_ptr ` qs)))"
  and      neq: "ntfnptr' \<noteq> ntfnptr"
  shows  "cnotification_relation (cslift t') ntfn' b"
proof -
    have rl: "\<And>p. \<lbrakk> p \<in> tcb_ptr_to_ctcb_ptr ` set (ntfnQueue (ntfnObj ntfn'));
                    isWaitingNtfn (ntfnObj ntfn); isWaitingNtfn (ntfnObj ntfn')\<rbrakk>
    \<Longrightarrow> cslift t p = cslift t' p" using srs koat' koat mpeq neq
    apply -
    apply (drule (3) ntfn_ntfn_disjoint [OF _ koat koat'])
    apply (erule restrict_map_eqI [symmetric])
    apply (erule imageE)
    apply (fastforce simp: disjoint_iff_not_equal inj_eq qs_def)
    done

  show ?thesis using ntfn rl mpeq unfolding cnotification_relation_def
    apply (simp add: Let_def)
    apply (cases "ntfnObj ntfn'")
       apply simp
      apply simp
     apply (cases "isWaitingNtfn (ntfnObj ntfn)")
      apply (simp add: isWaitingNtfn_def cong: tcb_queue_relation'_cong)
     apply (simp add: qs_def)
    done
qed

lemma cpspace_relation_ntfn_update_ntfn:
  fixes ntfn :: "Structures_H.notification"
  defines "qs \<equiv> if isWaitingNtfn (ntfnObj ntfn) then set (ntfnQueue (ntfnObj ntfn)) else {}"
  assumes koat: "ko_at' ntfn ntfnptr s"
  and     invs: "invs' s"
  and      cp: "cpspace_ntfn_relation (ksPSpace s) (t_hrs_' (globals t))"
  and     rel: "cnotification_relation (cslift t') ntfn' notification"
  and    mpeq: "(cslift t' |` (- (tcb_ptr_to_ctcb_ptr ` qs))) = (cslift t |` (- (tcb_ptr_to_ctcb_ptr ` qs)))"
  shows "cmap_relation (map_to_ntfns ((ksPSpace s)(ntfnptr \<mapsto> KONotification ntfn')))
           ((cslift t)(Ptr ntfnptr \<mapsto> notification)) Ptr (cnotification_relation (cslift t'))"
  using koat invs cp rel
  apply -
  apply (subst map_comp_update)
  apply (simp add: projectKO_opts_defs)
  apply (frule ko_at_projectKO_opt)
  apply (rule cmap_relationE1, assumption+)
  apply (erule (3) cmap_relation_upd_relI)
   apply (erule (1) cnotification_relation_ntfn_queue [OF _ invs_sym' koat])
     apply (erule (1) map_to_ko_atI')
    apply (fold qs_def, rule mpeq)
   apply assumption
  apply simp
  done

lemma cendpoint_relation_upd_tcb_no_queues:
  assumes cs: "mp thread = Some tcb"
  and   next_pres: "option_map tcbEPNext_C \<circ> mp = option_map tcbEPNext_C \<circ> mp'"
  and   prev_pres: "option_map tcbEPPrev_C \<circ> mp = option_map tcbEPPrev_C \<circ> mp'"
  shows "cendpoint_relation mp a b = cendpoint_relation mp' a b"
proof -
  show ?thesis
    unfolding cendpoint_relation_def
    apply (simp add: Let_def)
    apply (cases a)
    apply (simp add: tcb_queue_relation'_def tcb_queue_relation_only_next_prev [OF next_pres prev_pres, symmetric])+
    done
qed

lemma cnotification_relation_upd_tcb_no_queues:
  assumes cs: "mp thread = Some tcb"
  and   next_pres: "option_map tcbEPNext_C \<circ> mp = option_map tcbEPNext_C \<circ> mp'"
  and   prev_pres: "option_map tcbEPPrev_C \<circ> mp = option_map tcbEPPrev_C \<circ> mp'"
  shows "cnotification_relation mp a b = cnotification_relation mp' a b"
proof -
  show ?thesis
    unfolding cnotification_relation_def
    apply (simp add: Let_def)
    apply (cases "ntfnObj a")
      apply (simp add: tcb_queue_relation'_def tcb_queue_relation_only_next_prev [OF next_pres prev_pres, symmetric])+
    done
qed

lemma cendpoint_relation_ntfn_queue:
  assumes   srs: "sym_refs (state_refs_of' s)"
  and      koat: "ko_at' ntfn ntfnptr s"
  and iswaiting: "isWaitingNtfn (ntfnObj ntfn)"
  and      mpeq: "(cslift t' |` (- (tcb_ptr_to_ctcb_ptr ` set (ntfnQueue (ntfnObj ntfn)))))
  = (cslift t |` (- (tcb_ptr_to_ctcb_ptr ` set (ntfnQueue (ntfnObj ntfn)))))"
  and      koat': "ko_at' a epptr s"
  shows "cendpoint_relation (cslift t) a b = cendpoint_relation (cslift t') a b"
proof -
  have rl: "\<And>p. \<lbrakk> p \<in> tcb_ptr_to_ctcb_ptr ` set (epQueue a); isSendEP a \<or> isRecvEP a \<rbrakk>
    \<Longrightarrow> cslift t p = cslift t' p" using srs koat' koat iswaiting mpeq
    apply -
    apply (drule (4) ntfn_ep_disjoint)
    apply (erule restrict_map_eqI [symmetric])
    apply (erule imageE)
    apply (clarsimp simp: disjoint_iff_not_equal inj_eq)
    done

  show ?thesis
    unfolding cendpoint_relation_def using rl
    apply (simp add: Let_def)
    apply (cases a)
       apply (simp add: isRecvEP_def cong: tcb_queue_relation'_cong)
      apply simp
     apply (simp add: isSendEP_def isRecvEP_def cong: tcb_queue_relation'_cong)
    done
qed

lemma cvariable_relation_upd_const:
  "m x \<noteq> None
    \<Longrightarrow> cvariable_array_map_relation (m (x \<mapsto> y)) (\<lambda>x. n)
        = cvariable_array_map_relation m (\<lambda>x. n)"
  by (auto simp: fun_eq_iff cvariable_array_map_relation_def)

lemma ptr_span_ctcb_subset:
  "is_aligned p tcbBlockSizeBits \<Longrightarrow> ptr_span (tcb_ptr_to_ctcb_ptr p) \<subseteq> {p .. p + 2^tcbBlockSizeBits-1}"
  apply (simp add: tcb_ptr_to_ctcb_ptr_def ctcb_offset_def)
  apply (frule aligned_add_aligned[where m=ctcb_size_bits, OF _ is_aligned_triv],
         simp add: objBits_defs ctcb_size_bits_def)
  apply (subst upto_intvl_eq'; clarsimp)
   apply (erule is_aligned_no_wrap', simp add: ctcb_size_bits_def)
  apply (rule conjI)
   apply (erule is_aligned_no_wrap', simp add: objBits_defs ctcb_size_bits_def)
  apply (cut_tac word_add_le_mono1[where k=p and j="2^tcbBlockSizeBits-1"])
    apply (simp add: field_simps)
   apply (simp add: objBits_defs ctcb_size_bits_def)
  apply (subst field_simps, subst unat_plus_simple[where x=p, THEN iffD1, symmetric])
   apply (erule is_aligned_no_overflow')
  apply (rule unat_lt2p)
  done

(* FIXME: move *)
lemma tcb_at'_non_kernel_data_ref:
  "pspace_domain_valid s \<Longrightarrow> tcb_at' p s \<Longrightarrow> ptr_span (tcb_ptr_to_ctcb_ptr p) \<inter> kernel_data_refs = {}"
  apply (rule disjoint_subset[OF ptr_span_ctcb_subset])
   apply (erule tcb_aligned')
  apply (drule map_to_tcbs_from_tcb_at)
  apply (clarsimp simp: pspace_domain_valid_def map_comp_def split: option.splits)
  apply (drule spec, drule spec, drule (1) mp)
  apply (simp add: projectKOs objBits_simps)
  done

lemmas tcb_at'_non_kernel_data_ref'
  = tcb_at'_non_kernel_data_ref[OF invs'_pspace_domain_valid]

(* FIXME: move. Wants to go in SR_lemmas_C, but dependencies make this hard. *)
lemma fpu_null_state_heap_update_span_disjoint:
  assumes "ptr_span p \<inter> kernel_data_refs = {}"
  shows "fpu_null_state_relation (hrs_mem_update (heap_update p v) h) = fpu_null_state_relation h"
  by (cases "ptr_span (fpu_state_Ptr (symbol_table ''x86KSnullFpuState'')) \<subseteq> kernel_data_refs";
      clarsimp simp: fpu_null_state_relation_def lift_t_Some_iff hrs_mem_update
                     h_val_update_regions_disjoint
              dest!: disjoint_subset2[OF _ assms])

(* FIXME: move near tag_disj_via_td_name *)
lemma tag_not_less_via_td_name:
  assumes ta: "typ_name (typ_info_t TYPE('a)) \<noteq> pad_typ_name"
  assumes tina: "typ_name (typ_info_t TYPE('a)) \<notin> td_names (typ_info_t TYPE('b))"
  shows   "\<not> typ_uinfo_t TYPE('a::c_type) < typ_uinfo_t TYPE('b::c_type)"
  using assms
  by (auto simp: sub_typ_proper_def typ_tag_lt_def typ_simps dest: td_set_td_names)

(* FIXME: move *)
lemma td_set_map_td_commute[rule_format]:
  "\<forall>i. td_set (map_td f t) i = apfst (map_td f) ` td_set t i"
  "\<forall>i. td_set_struct (map_td_struct f st) i = apfst (map_td f) ` td_set_struct st i"
  "\<forall>i. td_set_list (map_td_list f ts) i = apfst (map_td f) ` td_set_list ts i"
  "\<forall>i. td_set_pair (map_td_pair f tp) i = apfst (map_td f) ` td_set_pair tp i"
  apply (induct t and st and ts and tp)
  apply simp_all
  apply (case_tac dt_pair; clarsimp simp: image_Un)
  done

(* FIXME: move *)
lemma td_set_export_uinfo_eq:
  "td_set (export_uinfo t) i = apfst export_uinfo ` td_set t i"
  unfolding export_uinfo_def by (rule td_set_map_td_commute)

(* FIXME: move *)
lemma td_set_adjust_ti_eq:
  "td_set (adjust_ti t a b) i = apfst (\<lambda>t. adjust_ti t a b) ` td_set t i"
  unfolding adjust_ti_def by (rule td_set_map_td_commute)

(* FIXME: move *)
lemma td_set_list_app:
  "td_set_list (ts @ ts') i = td_set_list ts i \<union> td_set_list ts' (i + size_td_list ts)"
  apply (induct ts arbitrary: i, simp)
  apply (rename_tac p ps i, case_tac p, simp add: Un_assoc field_simps)
  done

(* FIXME: move *)
lemma apfst_comp:
  "apfst f \<circ> apfst g = apfst (f \<circ> g)"
  by auto

lemma td_set_offset_wf[rule_format]:
  fixes td :: "'a typ_desc"
    and st :: "'a typ_struct"
    and ts :: "('a typ_desc, char list) dt_pair list"
    and tp :: "('a typ_desc, char list) dt_pair"
  shows "\<forall>s n m. (s, n) \<in> td_set td m \<longrightarrow> m \<le> n"
        "\<forall>s n m. (s, n) \<in> td_set_struct st m \<longrightarrow> m \<le> n"
        "\<forall>s n m. (s, n) \<in> td_set_list ts m \<longrightarrow> m \<le> n"
        "\<forall>s n m. (s, n) \<in> td_set_pair tp m \<longrightarrow> m \<le> n"
  apply (induct td and st and ts and tp)
  apply simp_all
  apply (case_tac dt_pair; fastforce)
  done

lemma field_lookup_offset_wf[rule_format]:
  fixes td :: "'a typ_desc"
    and st :: "'a typ_struct"
    and ts :: "('a typ_desc, char list) dt_pair list"
    and tp :: "('a typ_desc, char list) dt_pair"
  shows "\<forall>s n m f. field_lookup td f m = Some (s, n) \<longrightarrow> m \<le> n"
        "\<forall>s n m f. field_lookup_struct st f m = Some (s, n) \<longrightarrow> m \<le> n"
        "\<forall>s n m f. field_lookup_list ts f m = Some (s, n) \<longrightarrow> m \<le> n"
        "\<forall>s n m f. field_lookup_pair tp f m = Some (s, n) \<longrightarrow> m \<le> n"
  apply (induct td and st and ts and tp)
  apply simp_all
  apply (fastforce split: option.splits)+
  done

lemma td_set_field_lookup_wf[rule_format]:
  fixes td :: "'a typ_desc"
    and st :: "'a typ_struct"
    and ts :: "('a typ_desc, char list) dt_pair list"
    and tp :: "('a typ_desc, char list) dt_pair"
  shows "\<forall>k m. wf_desc td \<longrightarrow> k \<in> td_set td m \<longrightarrow> (\<exists>f. field_lookup td f m = Some k)"
        "\<forall>k m. wf_desc_struct st \<longrightarrow> k \<in> td_set_struct st m \<longrightarrow> (\<exists>f. field_lookup_struct st f m = Some k)"
        "\<forall>k m. wf_desc_list ts \<longrightarrow> k \<in> td_set_list ts m \<longrightarrow> (\<exists>f. field_lookup_list ts f m = Some k)"
        "\<forall>k m. wf_desc_pair tp \<longrightarrow> k \<in> td_set_pair tp m \<longrightarrow> (\<exists>f. field_lookup_pair tp f m = Some k)"
  using td_set_field_lookup'[of td st ts tp]
  apply -
  apply (clarsimp, frule td_set_offset_wf, drule spec, drule spec, drule spec, drule mp,
         erule rsubst[where P="\<lambda>n. (s,n) \<in> td_set" for s td_set], subst add_diff_inverse_nat,
         simp add: not_less, simp, simp)+
  done

lemma td_set_image_field_lookup:
  "wf_desc td \<Longrightarrow> k \<in> f ` td_set td m \<Longrightarrow> (\<exists>fn. option_map f (field_lookup td fn m) = Some k)"
  "wf_desc_struct st \<Longrightarrow> k \<in> f ` td_set_struct st m \<Longrightarrow> (\<exists>fn. option_map f (field_lookup_struct st fn m) = Some k)"
  "wf_desc_list ts \<Longrightarrow> k \<in> f ` td_set_list ts m \<Longrightarrow> (\<exists>fn. option_map f (field_lookup_list ts fn m) = Some k)"
  "wf_desc_pair tp \<Longrightarrow> k \<in> f ` td_set_pair tp m \<Longrightarrow> (\<exists>fn. option_map f (field_lookup_pair tp fn m) = Some k)"
  by (fastforce simp: image_def dest: td_set_field_lookup_wf)+

lemma field_lookup_td_set[rule_format]:
  fixes td :: "'a typ_desc"
    and st :: "'a typ_struct"
    and ts :: "('a typ_desc, char list) dt_pair list"
    and tp :: "('a typ_desc, char list) dt_pair"
  shows "\<forall>k m f. field_lookup td f m = Some k \<longrightarrow> k \<in> td_set td m"
        "\<forall>k m f. field_lookup_struct st f m = Some k \<longrightarrow> k \<in> td_set_struct st m"
        "\<forall>k m f. field_lookup_list ts f m = Some k \<longrightarrow> k \<in> td_set_list ts m"
        "\<forall>k m f. field_lookup_pair tp f m = Some k \<longrightarrow> k \<in> td_set_pair tp m"
  using td_set_field_lookup_rev'[of td st ts tp]
  apply -
  apply (clarsimp, frule field_lookup_offset_wf, drule spec, drule spec, drule spec, drule mp,
         rule exI, erule rsubst[where P="\<lambda>n. f = Some (s,n)" for f s], subst add_diff_inverse_nat,
         simp add: not_less, simp, simp)+
  done

lemma field_lookup_list_Some:
  assumes "wf_desc_list ts"
  assumes "field_lookup_list ts (fn # fns') m = Some (s, n)"
  shows "\<exists>td' m'. field_lookup_list ts [fn] m = Some (td', m') \<and> field_lookup td' fns' m' = Some (s, n)"
  using assms
  apply (induct ts arbitrary: m, simp)
  apply (rename_tac tp ts m, case_tac tp)
  apply (clarsimp split: if_splits option.splits simp: field_lookup_list_None)
  done

lemma field_lookup_Some_cases:
  assumes "wf_desc td"
  assumes "field_lookup td fns m = Some (s,n)"
  shows "case fns of
              [] \<Rightarrow> s = td \<and> m = n
            | fn # fns' \<Rightarrow> \<exists>td' m'. field_lookup td [fn] m = Some (td',m')
                                  \<and> field_lookup td' fns' m' = Some (s,n)"
  using assms
  apply (cases fns; simp)
  apply (cases td, rename_tac fn fns' st tn, clarsimp)
  apply (case_tac st; clarsimp simp: field_lookup_list_Some)
  done

lemma field_lookup_SomeE:
  assumes lookup: "field_lookup td fns m = Some (s,n)"
  assumes wf: "wf_desc td"
  assumes nil: "\<lbrakk> fns = []; s = td; m = n \<rbrakk> \<Longrightarrow> P"
  assumes some: "\<And>fn fns' td' m'. \<lbrakk> fns = fn # fns'; field_lookup td [fn] m = Some (td',m');
                                      field_lookup td' fns' m' = Some (s,n) \<rbrakk> \<Longrightarrow> P"
  shows P
  using field_lookup_Some_cases[OF wf lookup]
  by (cases fns) (auto simp add: nil some)

lemmas typ_combine_simps =
  ti_typ_pad_combine_def[where tag="TypDesc st tn" for st tn]
  ti_typ_combine_def[where tag="TypDesc st tn" for st tn]
  ti_pad_combine_def[where tag="TypDesc st tn" for st tn]
  align_td_array' size_td_array
  CompoundCTypes.field_names_list_def
  empty_typ_info_def
  final_pad_def padup_def
  align_of_def

bundle typ_combine_bundle =
  typ_combine_simps[simp]
  if_weak_cong[cong]

schematic_goal tcb_C_typ_info_unfold:
  "typ_info_t (?t :: tcb_C itself) = TypDesc ?st ?tn"
  including typ_combine_bundle by (simp add: tcb_C_typ_info tcb_C_tag_def)

schematic_goal arch_tcb_C_typ_info_unfold:
  "typ_info_t (?t :: arch_tcb_C itself) = TypDesc ?st ?tn"
  including typ_combine_bundle by (simp add: arch_tcb_C_typ_info arch_tcb_C_tag_def)

schematic_goal user_context_C_typ_info_unfold:
  "typ_info_t (?t :: user_context_C itself) = TypDesc ?st ?tn"
  including typ_combine_bundle by (simp add: user_context_C_typ_info user_context_C_tag_def)

schematic_goal user_fpu_state_C_typ_info_unfold:
  "typ_info_t (?t :: user_fpu_state_C itself) = TypDesc ?st ?tn"
  including typ_combine_bundle by (simp add: user_fpu_state_C_typ_info user_fpu_state_C_tag_def)

lemma user_fpu_state_C_in_tcb_C_offset:
  "(typ_uinfo_t TYPE(user_fpu_state_C), n) \<in> td_set (typ_uinfo_t TYPE(tcb_C)) 0 \<Longrightarrow> n = 0"
  \<comment> \<open>Examine the fields of tcb_C.\<close>
  apply (simp add: typ_uinfo_t_def tcb_C_typ_info_unfold td_set_export_uinfo_eq td_set_adjust_ti_eq
                   image_comp image_Un apfst_comp
              del: export_uinfo_typdesc_simp)
  apply (elim disjE)
  apply (all \<open>drule td_set_image_field_lookup[rotated]; clarsimp\<close>)
  apply (all \<open>drule arg_cong[where f=typ_name]; simp add: adjust_ti_def\<close>)
  apply (all \<open>(solves \<open>drule field_lookup_td_set; drule td_set_td_names; simp\<close>)?\<close>)
  \<comment> \<open>Only the arch_tcb_C may contain user_fpu_state_C, so examine the fields of that.\<close>
  apply (drule field_lookup_td_set)
  apply (simp add: arch_tcb_C_typ_info_unfold td_set_adjust_ti_eq)
  apply (drule td_set_image_field_lookup[rotated]; clarsimp simp: adjust_ti_def)
  \<comment> \<open>Similarly for user_context_C.\<close>
  apply (drule field_lookup_td_set)
  apply (simp add: user_context_C_typ_info_unfold td_set_adjust_ti_eq)
  apply (elim disjE)
  apply (all \<open>drule td_set_image_field_lookup[rotated]; clarsimp simp: adjust_ti_def\<close>)
  apply (all \<open>(solves \<open>drule field_lookup_td_set; drule td_set_td_names; simp\<close>)?\<close>)
  \<comment> \<open>Finally, we have user_fpu_state_C.\<close>
  apply (rename_tac fns s)
  apply (case_tac fns; clarsimp)
  \<comment> \<open>But we must also show that there is no user_fpu_state_C buried within user_fpu_state_C.\<close>
  apply (drule field_lookup_td_set)
  apply (simp add: user_fpu_state_C_typ_info_unfold td_set_adjust_ti_eq)
  apply (elim disjE; clarsimp simp: adjust_ti_def)
  apply (drule td_set_td_names; simp)
  done

context
  fixes t :: "tcb_C ptr"
  fixes tcb :: tcb_C
  fixes h u :: heap_raw_state
  fixes t_fpu :: "user_fpu_state_C ptr"
  defines "t_fpu \<equiv> fpu_state_Ptr &(user_context_Ptr &(atcb_Ptr &(t\<rightarrow>[''tcbArch_C''])\<rightarrow>[''tcbContext_C''])\<rightarrow>[''fpuState_C''])"
  defines "u \<equiv> hrs_mem_update (heap_update t tcb) h"
  assumes f: "clift u t_fpu = clift h t_fpu"
  assumes v: "hrs_htd h \<Turnstile>\<^sub>t t"
begin

lemma fpu_state_preservation:
  "(clift u :: user_fpu_state_C typ_heap) = clift h"
  apply (rule ext)
  apply (rename_tac null_fpu)
  apply (case_tac "ptr_val null_fpu = ptr_val t_fpu")
  subgoal for null_fpu
    using f by (cases null_fpu; clarsimp simp: u_def t_fpu_def lift_t_if split: if_splits)
  apply (subgoal_tac "hrs_htd h \<Turnstile>\<^sub>t t_fpu")
   prefer 2 subgoal
     unfolding t_fpu_def
     by (rule h_t_valid_field[OF h_t_valid_field[OF h_t_valid_field[OF v]]], simp+)
  using f v unfolding u_def t_fpu_def
  apply (cases h; case_tac "hrs_htd h \<Turnstile>\<^sub>t null_fpu";
         clarsimp simp: lift_t_if hrs_mem_update_def hrs_htd_def)
  apply (thin_tac "_ \<Turnstile>\<^sub>t fpu_state_Ptr _", thin_tac "h_val _ _ = h_val _ _", thin_tac "h = _")
  apply (rule h_val_heap_same; simp add: sub_typ_proper_def tag_not_less_via_td_name field_lvalue_def)
  apply (thin_tac "_ \<Turnstile>\<^sub>t _", thin_tac "_ \<Turnstile>\<^sub>t _", simp)
  apply (erule contrapos_np; simp add: field_of_t_def field_of_def)
  apply (drule user_fpu_state_C_in_tcb_C_offset)
  apply (simp add: unat_eq_0)
  done

lemma fpu_null_state_preservation:
  shows "fpu_null_state_relation u = fpu_null_state_relation h"
  by (simp add: fpu_null_state_relation_def fpu_state_preservation)

end

lemma rf_sr_tcb_update_no_queue:
  "\<lbrakk> (s, s') \<in> rf_sr;
     ko_at' tcb thread s;
     t_hrs_' (globals t) = hrs_mem_update (heap_update (tcb_ptr_to_ctcb_ptr thread) ctcb)
                                          (t_hrs_' (globals s'));
     tcbEPNext_C ctcb = tcbEPNext_C (the (cslift s' (tcb_ptr_to_ctcb_ptr thread)));
     tcbEPPrev_C ctcb = tcbEPPrev_C (the (cslift s' (tcb_ptr_to_ctcb_ptr thread)));
     fpuState_C (tcbContext_C (tcbArch_C ctcb))
       = fpuState_C (tcbContext_C (tcbArch_C (the (cslift s' (tcb_ptr_to_ctcb_ptr thread)))));
     (\<forall>x\<in>ran tcb_cte_cases. (\<lambda>(getF, setF). getF tcb' = getF tcb) x);
     ctcb_relation tcb' ctcb
   \<rbrakk>
  \<Longrightarrow> (s\<lparr>ksPSpace := (ksPSpace s)(thread \<mapsto> KOTCB tcb')\<rparr>,
       x\<lparr>globals := globals s'\<lparr>t_hrs_' := t_hrs_' (globals t)\<rparr>\<rparr>) \<in> rf_sr"
  unfolding rf_sr_def state_relation_def cstate_relation_def cpspace_relation_def
  apply (clarsimp simp: Let_def update_tcb_map_tos map_to_ctes_upd_tcb_no_ctes
                        heap_to_user_data_def)
  apply (frule (1) cmap_relation_ko_atD)
  apply (erule obj_atE')
  apply (clarsimp simp: projectKOs)
  apply (clarsimp simp: map_comp_update projectKO_opt_tcb cvariable_relation_upd_const
                        typ_heap_simps')
  apply (intro conjI)
       subgoal by (clarsimp simp: cmap_relation_def map_comp_update projectKO_opts_defs inj_eq)
      apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
      apply simp
      apply (rule cendpoint_relation_upd_tcb_no_queues, assumption+)
       subgoal by (clarsimp intro!: ext)
      subgoal by (clarsimp intro!: ext)
     apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
     apply simp
     apply (rule cnotification_relation_upd_tcb_no_queues, assumption+)
      subgoal by (clarsimp intro!: ext)
     subgoal by (clarsimp intro!: ext)
   subgoal by (clarsimp simp: carch_state_relation_def fpu_null_state_preservation typ_heap_simps')
  by (simp add: cmachine_state_relation_def)

lemmas rf_sr_tcb_update_no_queue2 =
  rf_sr_obj_update_helper[OF rf_sr_tcb_update_no_queue, simplified]

lemma tcb_queue_relation_not_in_q:
  "ctcb_ptr_to_tcb_ptr x \<notin> set xs \<Longrightarrow>
   tcb_queue_relation' nxtFn prvFn (hp(x := v)) xs start end
    = tcb_queue_relation' nxtFn prvFn hp xs start end"
  by (rule tcb_queue_relation'_cong, auto)

lemma rf_sr_tcb_update_not_in_queue:
  "\<lbrakk> (s, s') \<in> rf_sr; ko_at' tcb thread s;
    t_hrs_' (globals t) = hrs_mem_update (heap_update
      (tcb_ptr_to_ctcb_ptr thread) ctcb) (t_hrs_' (globals s'));
    \<not> live' (KOTCB tcb); invs' s;
    (\<forall>x\<in>ran tcb_cte_cases. (\<lambda>(getF, setF). getF tcb' = getF tcb) x);
    ctcb_relation tcb' ctcb \<rbrakk>
     \<Longrightarrow> (s\<lparr>ksPSpace := (ksPSpace s)(thread \<mapsto> KOTCB tcb')\<rparr>,
           x\<lparr>globals := globals s'\<lparr>t_hrs_' := t_hrs_' (globals t)\<rparr>\<rparr>) \<in> rf_sr"
  unfolding rf_sr_def state_relation_def cstate_relation_def cpspace_relation_def
  apply (clarsimp simp: Let_def update_tcb_map_tos map_to_ctes_upd_tcb_no_ctes
                        heap_to_user_data_def live'_def)
  apply (frule (1) cmap_relation_ko_atD)
  apply (erule obj_atE')
  apply (clarsimp simp: projectKOs)
  apply (clarsimp simp: map_comp_update projectKO_opt_tcb cvariable_relation_upd_const
                        typ_heap_simps')
  apply (subgoal_tac "\<forall>rf. \<not> ko_wp_at' (\<lambda>ko. rf \<in> refs_of' ko) thread s")
  prefer 2
   apply clarsimp
   apply (auto simp: obj_at'_def ko_wp_at'_def)[1]
  apply (intro conjI)
       subgoal by (clarsimp simp: cmap_relation_def map_comp_update projectKO_opts_defs inj_eq)
      apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
      apply clarsimp
      apply (subgoal_tac "thread \<notin> (fst ` ep_q_refs_of' a)")
       apply (clarsimp simp: cendpoint_relation_def Let_def split: Structures_H.endpoint.split)
       subgoal by (intro conjI impI allI, simp_all add: image_def tcb_queue_relation_not_in_q)[1]
      apply (drule(1) map_to_ko_atI')
      apply (drule sym_refs_ko_atD', clarsimp+)
      subgoal by blast
     apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
     apply clarsimp
     apply (subgoal_tac "thread \<notin> (fst ` ntfn_q_refs_of' (ntfnObj a))")
      apply (clarsimp simp: cnotification_relation_def Let_def
                     split: ntfn.splits)
      subgoal by (simp add: image_def tcb_queue_relation_not_in_q)[1]
     apply (drule(1) map_to_ko_atI')
     apply (drule sym_refs_ko_atD', clarsimp+)
     subgoal by blast
    apply (clarsimp simp: Let_def)
   apply (simp add: carch_state_relation_def)
   subgoal by (clarsimp simp: fpu_null_state_heap_update_span_disjoint[OF tcb_at'_non_kernel_data_ref']
                              global_ioport_bitmap_heap_update_tag_disj_simps obj_at'_def projectKOs)
  by (simp add: cmachine_state_relation_def)

end
end
