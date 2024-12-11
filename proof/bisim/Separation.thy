(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Restricted capabilities in the Separation Kernel Abstract Specification"

theory Separation
imports
  "ASepSpec.Syscall_SA"
  "AInvs.AInvs"
  "Lib.Bisim_UL"
  "Lib.LemmaBucket"
begin

text \<open>
  The seL4 kernel, when appropriately restricted, is a separation kernel. Any
  two processes in separate domains should behave the same as if they were
  processes running on two physically separated machines. They should not be
  aware of each other's existence and should not be able to communicate with
  each other except through well-defined channels. Importantly, it must be
  possible to show that there are no back channels through which one process
  can determine whether another process exists or what it is doing.

  In seL4 we achieve this by restricting the capabilities that a thread may
  possess. The restrictions are summarised in the predicate @{text
  separate_state} below (which indirectly depends on further predicates @{text
  separate_cnode_cap}, @{text separate_cap}, etc).

  a) A thread may only possess \emph{notification capabilities}
  (@{text NotificationCap}).

  b) Threads do not have caller capabilities. (A caller capability is a
  capability, placed in a special slot in the TCB, to allow replies. Since the
  @{text Reply} capability is disallowed so is the caller capability.)

  c) Pointers to other capability tables are disallowed meaning that the
  capability tree is flat. i.e. of depth 1

  Initialising the kernel so that these restrictions hold is not covered in
  the bisimulation proof, but can be achieved using the capDL initialiser.

  Note that this proof does not preclude threads from communicating via shared
  memory if the threads have been set up accordingly, which again can be done
  via the capDL initialiser.

  The proof does show that the kernel API after reaching a state that
  satisifies @{text separate_state} is that of a static separation kernel,
  that is, it only provides system calls for sending and receiving on
  notification objects and otherwise exhibits no dynamic behaviour.

  Systems with such a setup satisfy the preconditions of our separate
  non-intereference proof, which shows that information travels only along
  these authorised channels.
\<close>

definition
  separate_cap :: "cap \<Rightarrow> bool"
where
  "separate_cap cap \<equiv> case cap of
                             NotificationCap ptr badge rights \<Rightarrow> rights \<subseteq> {AllowRecv, AllowSend}
                           | NullCap                           \<Rightarrow> True
                           | _                                 \<Rightarrow> False"


lemma separate_capE:
  "\<lbrakk> separate_cap cap; cap = NullCap \<Longrightarrow> R; \<And>ptr badge rights. \<lbrakk> cap = NotificationCap ptr badge rights \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  unfolding separate_cap_def
  by (fastforce split: cap.splits)

definition
  "separate_cnode_cap cs cap \<equiv> case cap of
                                  CNodeCap p bits guard \<Rightarrow> (bits + length guard = word_bits) \<and>
                                                           (\<forall>off. case_option True separate_cap (cs (p, off)))
                                 | NullCap               \<Rightarrow> True
                                 | _                     \<Rightarrow> False"

definition
  "separate_tcb p cs \<equiv> case_option True (separate_cnode_cap cs) (cs (p, tcb_cnode_index 0))
                       \<and> cs (p, tcb_cnode_index 3) = Some NullCap" \<comment> \<open>ctable and caller cap\<close>

lemma separate_cnode_cap_rab:
  "\<lbrakk> separate_cnode_cap cs cap; length cref = word_bits \<rbrakk> \<Longrightarrow>
  resolve_address_bits (cap, cref) = (case cap of
                                         CNodeCap p bits guard \<Rightarrow> if guard \<le> cref then
                                                                     returnOk ((p, drop (length guard) cref), [])
                                                                 else
                                                                     (throwError (GuardMismatch (length cref) guard))
                                       | _ \<Rightarrow> throwError InvalidRoot)"
  unfolding separate_cnode_cap_def resolve_address_bits_def
  by (auto simp: word_bits_def resolve_address_bits'.simps split: cap.split_asm)

definition
  "separate_state s \<equiv> \<forall>p. tcb_at p s \<longrightarrow> separate_tcb p (caps_of_state s)"


lemma separate_cnode_capE:
  "\<lbrakk> separate_cnode_cap cs cap;
     cap = NullCap \<Longrightarrow> R;
    \<And>p bits guard. \<lbrakk> cap = CNodeCap p bits guard; bits + length guard = word_bits;
                     (\<forall>off cap'. cs (p, off) = Some cap' \<longrightarrow> separate_cap cap') \<rbrakk> \<Longrightarrow> R \<rbrakk>
   \<Longrightarrow> R"
  unfolding separate_cnode_cap_def
  by (auto split: cap.splits option.splits)

lemma valid_sep_cap_not_cnode:
  "\<lbrakk> s \<turnstile> cap; \<forall>off cap'. caps_of_state s (p, off) = Some cap' \<longrightarrow> separate_cap cap'; cap = CNodeCap p bits guard; bits \<le> length cref - length guard \<rbrakk>
  \<Longrightarrow> \<exists>cap'. caps_of_state s (p, take bits (drop (length guard) cref)) = Some cap' \<and> \<not> is_cnode_cap cap'"
  apply (clarsimp simp: valid_cap_simps not_less in_monad)
   apply (drule_tac offset = "take bits (drop (length guard) cref)" in cap_table_at_cte_at)
   apply simp
  apply (fastforce simp: cte_wp_at_caps_of_state separate_cap_def is_cap_simps)
  done

lemma bisim_gen_asm_r:
  assumes bs: "F \<Longrightarrow> bisim_underlying sr r P P' a b"
  shows   "bisim_underlying sr r P (P' and K F) a b"
  using bs
  by (fastforce intro!: bisim_underlyingI elim: bisim_underlyingE1  bisim_underlyingE2)

lemma bisim_separate_cap_cases:
  assumes nc: "cap = NullCap \<Longrightarrow> bisim R Pn Pn' m m'"
  and     ac: "\<And>ptr badge rights. \<lbrakk> cap = NotificationCap ptr badge rights \<rbrakk>
               \<Longrightarrow> bisim R (Pa ptr badge rights) (Pa' ptr badge rights) m m'"
  shows   "bisim R (\<lambda>s. (cap = NullCap \<longrightarrow> Pn s)
                    \<and> (\<forall>ptr badge rights. cap = NotificationCap ptr badge rights \<longrightarrow> Pa ptr badge rights s))
                   ((\<lambda>s. (cap = NullCap \<longrightarrow> Pn' s)
                    \<and> (\<forall>ptr badge rights. cap = NotificationCap ptr badge rights \<longrightarrow> Pa' ptr badge rights s))
                       and K (separate_cap cap)) m m'"
  using assms
  apply -
  apply (rule bisim_gen_asm_r)
  apply (erule separate_capE, simp_all)
  done

lemma caps_of_state_tcb:
  "\<lbrakk> get_tcb p s = Some tcb; option_map fst (tcb_cap_cases idx) = Some getF \<rbrakk> \<Longrightarrow> caps_of_state s (p, idx) = Some (getF tcb)"
  apply (drule get_tcb_SomeD)
  apply clarsimp
  apply (drule (1) cte_wp_at_tcbI [where t = "(p, idx)" and P = "(=) (getF tcb)", simplified])
  apply simp
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  done

lemma caps_of_state_tcb_cap_cases:
  "\<lbrakk> get_tcb p s = Some tcb; idx \<in> dom tcb_cap_cases \<rbrakk> \<Longrightarrow> caps_of_state s (p, idx) = Some ((the (option_map fst (tcb_cap_cases idx))) tcb)"
  apply (clarsimp simp: dom_def)
  apply (erule caps_of_state_tcb)
  apply simp
  done

lemma separate_state_get_tcbD:
  "\<lbrakk>separate_state s; get_tcb p s = Some tcb \<rbrakk> \<Longrightarrow>
  separate_cnode_cap (caps_of_state s) (tcb_ctable tcb) \<and> tcb_caller tcb = NullCap"
  unfolding separate_state_def
  apply (drule spec [where x = p])
  apply (simp add: tcb_at_def separate_tcb_def caps_of_state_tcb_cap_cases dom_tcb_cap_cases)
  done

lemma separate_state_simps[simp]:
  "\<And>f. separate_state (trans_state f s) = separate_state s"
  "\<And>f. separate_state (cdt_update f s) = separate_state s"
  "\<And>f. separate_state (is_original_cap_update f s) = separate_state s"
  "\<And>f. separate_state (domain_index_update f s) = separate_state s"
  "\<And>f. separate_state (cur_domain_update f s) = separate_state s"
  "\<And>f. separate_state (domain_time_update f s) = separate_state s"
  "\<And>f. separate_state (arch_state_update f s) = separate_state s"
  "\<And>f. separate_state (machine_state_update f s) = separate_state s"
  "\<And>f. separate_state (cur_thread_update f s) = separate_state s"
  "\<And>f. separate_state (ready_queues_update f s) = separate_state s"
  "\<And>f. separate_state (scheduler_action_update f s) = separate_state s"
  by (simp add: separate_state_def)+

end
