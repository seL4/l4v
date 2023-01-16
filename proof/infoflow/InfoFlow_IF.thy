(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory InfoFlow_IF
imports InfoFlow
begin

section \<open>InfoFlow lemmas\<close>

lemma pas_domains_distinct_inj:
  "\<lbrakk> pas_domains_distinct aag; l1 \<in> pasDomainAbs aag d; l2 \<in> pasDomainAbs aag d \<rbrakk>
     \<Longrightarrow> l1 = l2"
  apply (clarsimp simp: pas_domains_distinct_def)
  apply (drule_tac x=d in spec)
  apply auto
  done

lemma domain_has_unique_label:
  "pas_domains_distinct aag \<Longrightarrow> \<exists>l. pasDomainAbs aag d = {l}"
  by (simp add: pas_domains_distinct_def)

lemma domain_has_the_label:
  "\<lbrakk> pas_domains_distinct aag; l \<in> pasDomainAbs aag d \<rbrakk>
     \<Longrightarrow> the_elem (pasDomainAbs aag d) = l"
  apply (simp add: pas_domains_distinct_def)
  apply (metis singletonD the_elem_eq)
  done

lemma aag_can_read_self:
  "is_subject aag x \<Longrightarrow> aag_can_read aag x"
  by simp

lemma aag_can_read_read:
  "aag_has_auth_to aag Read x \<Longrightarrow> aag_can_read aag x"
  by (rule reads_read)

lemma aag_can_read_irq_self:
  "is_subject_irq aag x \<Longrightarrow> aag_can_read_irq aag x"
  by simp

lemma equiv_forE:
  assumes e: "equiv_for P f c c'"
  obtains "\<And>x. P x \<Longrightarrow> f c x = f c' x"
  apply (erule meta_mp)
  apply(erule e[simplified equiv_for_def, rule_format])
  done

lemma equiv_forI:
  "(\<And>x. P x \<Longrightarrow> f c x = f c' x) \<Longrightarrow> equiv_for P f c c'"
  by(simp add: equiv_for_def)

lemma equiv_forD:
  "\<lbrakk> equiv_for P f c c'; P x \<rbrakk> \<Longrightarrow> f c x = f c' x"
  by (blast elim: equiv_forE)

lemma equiv_for_comp:
  "equiv_for P (f \<circ> g) s s' = equiv_for P f (g s) (g s')"
  by (simp add: equiv_for_def)

lemma equiv_for_or:
  "equiv_for (A or B) f c c' = (equiv_for A f c c' \<and> equiv_for B f c c')"
  by (fastforce simp: equiv_for_def)

lemma equiv_for_id_update:
  "equiv_for P id c c' \<Longrightarrow>
   equiv_for P id (c(x := v)) (c'(x := v))"
  by (simp add: equiv_for_def)

lemma states_equiv_forI:
  "\<lbrakk> equiv_for P kheap s s';
     equiv_machine_state P (machine_state s) (machine_state s');
     equiv_for (P \<circ> fst) cdt s s';
     equiv_for P ekheap s s';
     equiv_for (P \<circ> fst) cdt_list s s';
     equiv_for (P \<circ> fst) is_original_cap s s';
     equiv_for Q interrupt_states s s';
     equiv_for Q interrupt_irq_node s s';
     equiv_asids R s s';
     equiv_for S ready_queues s s' \<rbrakk>
     \<Longrightarrow> states_equiv_for P Q R S s s'"
  by (auto simp: states_equiv_for_def)

definition for_each_byte_of_word :: "(obj_ref \<Rightarrow> bool) \<Rightarrow> obj_ref \<Rightarrow> bool" where
  "for_each_byte_of_word P w \<equiv> \<forall>y\<in>{w..w + (word_size - 1)}. P y"

locale InfoFlow_IF_1 =
  fixes aag :: "'a PAS"
  assumes equiv_asids_refl:
    "equiv_asids R s s"
  and equiv_asids_sym:
    "equiv_asids R s t \<Longrightarrow> equiv_asids R t s"
  and equiv_asids_trans:
    "\<lbrakk> equiv_asids R s t; equiv_asids R t u \<rbrakk> \<Longrightarrow> equiv_asids R s u"
  and equiv_asids_identical_kheap_updates:
    "\<lbrakk> equiv_asids R s s'; identical_kheap_updates s s' kh kh' \<rbrakk>
       \<Longrightarrow> equiv_asids R (s\<lparr>kheap := kh\<rparr>) (s'\<lparr>kheap := kh'\<rparr>)"
  and equiv_asids_False:
  "(\<And>x. P x \<Longrightarrow> False) \<Longrightarrow> equiv_asids P x y"
  and equiv_asids_triv:
    "\<lbrakk> equiv_asids R s s'; kheap t = kheap s; kheap t' = kheap s';
       arch_state t = arch_state s; arch_state t' = arch_state s' \<rbrakk>
       \<Longrightarrow> equiv_asids R t t'"
  and equiv_asids_non_asid_pool_kheap_update:
  "\<lbrakk> equiv_asids R s s'; non_asid_pool_kheap_update s kh; non_asid_pool_kheap_update s' kh' \<rbrakk>
     \<Longrightarrow> equiv_asids R (s\<lparr>kheap := kh\<rparr>) (s'\<lparr>kheap := kh'\<rparr>)"
  and globals_equiv_refl:
    "globals_equiv s s"
  and globals_equiv_sym:
    "globals_equiv s t \<Longrightarrow> globals_equiv t s"
  and globals_equiv_trans:
    "\<lbrakk> globals_equiv s t; globals_equiv t u \<rbrakk> \<Longrightarrow> globals_equiv s u"
  and equiv_asids_guard_imp:
    "\<lbrakk> equiv_asids R s s'; \<And>x. Q x \<Longrightarrow> R x \<rbrakk> \<Longrightarrow> equiv_asids Q s s'"
  and dmo_loadWord_rev:
    "reads_equiv_valid_inv A aag (K (for_each_byte_of_word (aag_can_read aag) p))
                                 (do_machine_op (loadWord p))"
begin

lemma states_equiv_for_machine_state_update:
  "\<lbrakk> states_equiv_for P Q R S s s'; equiv_machine_state P kh kh' \<rbrakk>
     \<Longrightarrow> states_equiv_for P Q R S (s\<lparr>machine_state := kh\<rparr>) (s'\<lparr>machine_state := kh'\<rparr>)"
  by (fastforce elim: equiv_forE elim!: equiv_asids_triv
               intro: equiv_forI simp: states_equiv_for_def)

lemma states_equiv_for_cdt_update:
  "\<lbrakk> states_equiv_for P Q R S s s'; equiv_for (P \<circ> fst) id kh kh' \<rbrakk>
     \<Longrightarrow> states_equiv_for P Q R S (s\<lparr>cdt := kh\<rparr>) (s'\<lparr>cdt := kh'\<rparr>)"
  by (fastforce elim: equiv_forE elim!: equiv_asids_triv
               intro: equiv_forI simp: states_equiv_for_def)

lemma states_equiv_for_cdt_list_update:
  "\<lbrakk> states_equiv_for P Q R S s s'; equiv_for (P \<circ> fst) id (kh (cdt_list s)) (kh' (cdt_list s')) \<rbrakk>
     \<Longrightarrow> states_equiv_for P Q R S (cdt_list_update kh s) (cdt_list_update kh' s')"
  by (fastforce elim: equiv_forE elim!: equiv_asids_triv
               intro: equiv_forI simp: states_equiv_for_def)

lemma states_equiv_for_is_original_cap_update:
  "\<lbrakk> states_equiv_for P Q R S s s'; equiv_for (P \<circ> fst) id kh kh' \<rbrakk>
     \<Longrightarrow> states_equiv_for P Q R S (s\<lparr>is_original_cap := kh\<rparr>) (s'\<lparr>is_original_cap := kh'\<rparr>)"
  by (fastforce elim: equiv_forE elim!: equiv_asids_triv
               intro: equiv_forI simp: states_equiv_for_def)

lemma states_equiv_for_interrupt_states_update:
  "\<lbrakk> states_equiv_for P Q R S s s'; equiv_for Q id kh kh' \<rbrakk>
    \<Longrightarrow> states_equiv_for P Q R S (s\<lparr>interrupt_states := kh\<rparr>) (s'\<lparr>interrupt_states := kh'\<rparr>)"
  by (fastforce elim: equiv_forE elim!: equiv_asids_triv
               intro: equiv_forI simp: states_equiv_for_def)

lemma states_equiv_for_interrupt_irq_node_update:
  "\<lbrakk> states_equiv_for P Q R S s s'; equiv_for Q id kh kh' \<rbrakk>
     \<Longrightarrow> states_equiv_for P Q R S (s\<lparr>interrupt_irq_node := kh\<rparr>) (s'\<lparr>interrupt_irq_node := kh'\<rparr>)"
  by (fastforce elim: equiv_forE elim!: equiv_asids_triv
               intro: equiv_forI simp: states_equiv_for_def)

lemma states_equiv_for_ready_queues_update:
  "\<lbrakk> states_equiv_for P Q R S s s'; equiv_for S id kh kh' \<rbrakk>
     \<Longrightarrow> states_equiv_for P Q R S (s\<lparr>ready_queues := kh\<rparr>) (s'\<lparr>ready_queues := kh'\<rparr>)"
  by (fastforce elim: equiv_forE elim!: equiv_asids_triv
               intro: equiv_forI simp: states_equiv_for_def)

lemma states_equiv_for_ekheap_update:
  "\<lbrakk> states_equiv_for P Q R S s s'; equiv_for P id (kh (ekheap s)) (kh' (ekheap s')) \<rbrakk>
     \<Longrightarrow> states_equiv_for P Q R S (ekheap_update kh s) (ekheap_update kh' s')"
  by (fastforce elim: equiv_forE elim!: equiv_asids_triv
               intro: equiv_forI simp: states_equiv_for_def)

lemma states_equiv_for_identical_ekheap_updates:
  "\<lbrakk> states_equiv_for P Q R S s s'; identical_ekheap_updates s s' (kh (ekheap s)) (kh' (ekheap s')) \<rbrakk>
     \<Longrightarrow> states_equiv_for P Q R S (ekheap_update kh s) (ekheap_update kh' s')"
  by (fastforce simp: identical_ekheap_updates_def equiv_for_def states_equiv_for_def equiv_asids_triv)

lemma states_equiv_for_identical_kheap_updates:
  "\<lbrakk> states_equiv_for P Q R S s s'; identical_kheap_updates s s' kh kh' \<rbrakk>
     \<Longrightarrow> states_equiv_for P Q R S (s\<lparr>kheap := kh\<rparr>) (s'\<lparr>kheap := kh'\<rparr>)"
  by (auto simp: states_equiv_for_def identical_kheap_updates_def
          elim!: equiv_forE equiv_asids_identical_kheap_updates
         intro!: equiv_forI)

end


lemma states_equiv_forE:
  assumes sef: "states_equiv_for P Q R S s s'"
  obtains "equiv_machine_state P (machine_state s) (machine_state s')"
          "equiv_for P kheap s s'"
          "equiv_for (P \<circ> fst) cdt s s'"
          "equiv_for (P \<circ> fst) cdt_list s s'"
          "equiv_for P ekheap s s'"
          "equiv_for (P \<circ> fst) is_original_cap s s'"
          "equiv_for Q interrupt_states s s'"
          "equiv_for Q interrupt_irq_node s s'"
          "equiv_asids R s s'"
          "equiv_for S ready_queues s s'"
  using sef[simplified states_equiv_for_def] by auto

lemma equiv_for_apply: "equiv_for P g (f s) (f s') = equiv_for P (g o f) s s'"
  by (simp add: equiv_for_def)

lemma states_equiv_forE_kheap:
  assumes sef: "states_equiv_for P Q R S s s'"
  obtains "\<And>x. P x \<Longrightarrow> kheap s x = kheap s' x"
  using sef by (auto simp: states_equiv_for_def elim: equiv_forE)

lemma states_equiv_forE_mem:
  assumes sef: "states_equiv_for P Q R S s s'"
  obtains "\<And>x. P x \<Longrightarrow>
    (underlying_memory (machine_state s)) x = (underlying_memory (machine_state s')) x \<and>
    (device_state (machine_state s)) x = (device_state (machine_state s')) x"
  using sef
  apply (clarsimp simp: states_equiv_for_def elim: equiv_forE)
  apply (elim equiv_forE)
  apply fastforce
  done

lemma states_equiv_forE_cdt:
  assumes sef: "states_equiv_for P Q R S s s'"
  obtains "\<And>x. P (fst x) \<Longrightarrow> cdt s x = cdt s' x"
  using sef by (auto simp: states_equiv_for_def elim: equiv_forE)

lemma states_equiv_forE_cdt_list:
  assumes sef: "states_equiv_for P Q R S s s'"
  obtains "\<And>x. P (fst x) \<Longrightarrow> cdt_list s x = cdt_list s' x"
  using sef by (auto simp: states_equiv_for_def elim: equiv_forE)

lemma states_equiv_forE_ekheap:
  assumes sef: "states_equiv_for P Q R S s s'"
  obtains "\<And>x. P x \<Longrightarrow> ekheap s x = ekheap s' x"
  using sef by (auto simp: states_equiv_for_def elim: equiv_forE)

lemma states_equiv_forE_is_original_cap:
  assumes sef: "states_equiv_for P Q R S s s'"
  obtains "\<And>x. P (fst x) \<Longrightarrow> is_original_cap s x = is_original_cap s' x"
  using sef by (auto simp: states_equiv_for_def elim: equiv_forE)

lemma states_equiv_forE_interrupt_states:
  assumes sef: "states_equiv_for P Q R S s s'"
  obtains "\<And>x. Q x \<Longrightarrow> interrupt_states s x = interrupt_states s' x"
  using sef by (auto simp: states_equiv_for_def elim: equiv_forE)

lemma states_equiv_forE_interrupt_irq_node:
  assumes sef: "states_equiv_for P Q R S s s'"
  obtains "\<And>x. Q x \<Longrightarrow> interrupt_irq_node s x = interrupt_irq_node s' x"
  using sef by (auto simp: states_equiv_for_def elim: equiv_forE)

lemma states_equiv_forE_ready_queues:
  assumes sef: "states_equiv_for P Q R S s s'"
  obtains "\<And>x. S x \<Longrightarrow> ready_queues s x = ready_queues s' x"
  using sef by (auto simp: states_equiv_for_def elim: equiv_forE)

lemma equiv_for_refl:
  "equiv_for P f s s"
  by (auto simp: equiv_for_def)

lemma equiv_for_sym:
  "equiv_for P f s t \<Longrightarrow> equiv_for P f t s"
  by (auto simp: equiv_for_def)

lemma equiv_for_trans:
  "\<lbrakk> equiv_for P f s t; equiv_for P f t u \<rbrakk> \<Longrightarrow> equiv_for P f s u"
  by (auto simp: equiv_for_def)


context InfoFlow_IF_1 begin

lemma states_equiv_for_refl:
  "states_equiv_for P Q R S s s"
  by (auto simp: states_equiv_for_def  intro: equiv_for_refl equiv_asids_refl)

lemma states_equiv_for_sym:
  "states_equiv_for P Q R S s t \<Longrightarrow> states_equiv_for P Q R S t s"
  by (auto simp: states_equiv_for_def intro: equiv_for_sym equiv_asids_sym simp: equiv_for_def)

lemma states_equiv_for_trans:
  "\<lbrakk> states_equiv_for P Q R S s t; states_equiv_for P Q R S t u \<rbrakk>
     \<Longrightarrow> states_equiv_for P Q R S s u"
  by (auto simp: states_equiv_for_def
          intro: equiv_for_trans equiv_asids_trans equiv_forI
           elim: equiv_forE)

end


(* FIXME MOVE *)
lemma or_comp_dist:
  "(A or B) \<circ> f = (A \<circ> f or B \<circ> f)"
  by (simp add: pred_disj_def comp_def)

lemma idle_equiv_refl:
  "idle_equiv s s"
  by (simp add: idle_equiv_def)

lemma idle_equiv_sym:
  "idle_equiv s s' \<Longrightarrow> idle_equiv s' s"
  by (clarsimp simp add: idle_equiv_def)

lemma idle_equiv_trans:
  "\<lbrakk> idle_equiv s s'; idle_equiv s' s'' \<rbrakk> \<Longrightarrow> idle_equiv s s''"
  by (clarsimp simp add: idle_equiv_def tcb_at_def get_tcb_def split: option.splits
                  kernel_object.splits)

lemma equiv_asids_aag_can_read_asid:
  "equiv_asids (aag_can_read_asid aag) s s' =
   (\<forall>d \<in> subjectReads (pasPolicy aag) (pasSubject aag). equiv_asids (\<lambda>x. d = pasASIDAbs aag x) s s')"
  by (auto simp: equiv_asids_def)

lemma reads_equiv_def2:
  "reads_equiv aag s s' = (states_equiv_for (aag_can_read aag) (aag_can_read_irq aag)
                                            (aag_can_read_asid aag) (aag_can_read_domain aag) s s' \<and>
                           cur_thread s = cur_thread s' \<and>
                           cur_domain s = cur_domain s' \<and>
                           scheduler_action s = scheduler_action s' \<and>
                           work_units_completed s = work_units_completed s' \<and>
                           irq_state (machine_state s) = irq_state (machine_state s'))"
  by (auto simp: reads_equiv_def equiv_for_def states_equiv_for_def equiv_asids_aag_can_read_asid)

lemma reads_equivE:
  assumes sef: "reads_equiv aag s s'"
  obtains "equiv_for (aag_can_read aag) kheap s s'"
          "equiv_machine_state (aag_can_read aag) (machine_state s) (machine_state s')"
          "equiv_for ((aag_can_read aag) \<circ> fst) cdt s s'"
          "equiv_for ((aag_can_read aag) \<circ> fst) cdt_list s s'"
          "equiv_for (aag_can_read aag) ekheap s s'"
          "equiv_for ((aag_can_read aag) \<circ> fst) is_original_cap s s'"
          "equiv_for (aag_can_read_irq aag) interrupt_states s s'"
          "equiv_for (aag_can_read_irq aag) interrupt_irq_node s s'"
          "equiv_asids (aag_can_read_asid aag) s s'"
          "equiv_for (aag_can_read_domain aag) ready_queues s s'"
          "cur_thread s = cur_thread s'"
          "cur_domain s = cur_domain s'"
          "scheduler_action s = scheduler_action s'"
          "work_units_completed s = work_units_completed s'"
          "irq_state (machine_state s) = irq_state (machine_state s')"
  using sef by (auto simp: reads_equiv_def2 elim: states_equiv_forE)


context InfoFlow_IF_1 begin

lemma reads_equiv_machine_state_update:
  "\<lbrakk> reads_equiv aag s s'; equiv_machine_state (aag_can_read aag) kh kh'; irq_state kh = irq_state kh' \<rbrakk>
     \<Longrightarrow> reads_equiv aag (s\<lparr>machine_state := kh\<rparr>) (s'\<lparr>machine_state := kh'\<rparr>)"
  by (fastforce simp: reads_equiv_def2 intro: states_equiv_for_machine_state_update)

lemma states_equiv_for_non_asid_pool_kheap_update:
  "\<lbrakk> states_equiv_for P Q R S s s'; equiv_for P id kh kh';
     non_asid_pool_kheap_update s kh; non_asid_pool_kheap_update s' kh' \<rbrakk>
     \<Longrightarrow> states_equiv_for P Q R S (s\<lparr>kheap := kh\<rparr>) (s'\<lparr>kheap := kh'\<rparr>)"
  by (fastforce elim: equiv_forE elim!: equiv_asids_non_asid_pool_kheap_update
               intro: equiv_forI simp: states_equiv_for_def)

lemma reads_equiv_non_asid_pool_kheap_update:
  "\<lbrakk> reads_equiv aag s s'; equiv_for (aag_can_read aag) id kh kh';
     non_asid_pool_kheap_update s kh; non_asid_pool_kheap_update s' kh' \<rbrakk>
     \<Longrightarrow> reads_equiv aag (s\<lparr>kheap := kh\<rparr>) (s'\<lparr>kheap := kh'\<rparr>)"
  by (fastforce simp: reads_equiv_def2 intro: states_equiv_for_non_asid_pool_kheap_update)

lemma reads_equiv_identical_kheap_updates:
  "\<lbrakk> reads_equiv aag s s'; identical_kheap_updates s s' kh kh' \<rbrakk>
     \<Longrightarrow> reads_equiv aag (s\<lparr>kheap := kh\<rparr>) (s'\<lparr>kheap := kh'\<rparr>)"
  by (fastforce simp: reads_equiv_def2 intro: states_equiv_for_identical_kheap_updates)

lemma reads_equiv_cdt_update:
  "\<lbrakk> reads_equiv aag s s'; equiv_for ((aag_can_read aag) \<circ> fst) id kh kh' \<rbrakk>
     \<Longrightarrow> reads_equiv aag (s\<lparr>cdt := kh\<rparr>) (s'\<lparr>cdt := kh'\<rparr>)"
  by (fastforce simp: reads_equiv_def2 intro: states_equiv_for_cdt_update)

lemma reads_equiv_cdt_list_update:
  "\<lbrakk> reads_equiv aag s s'; equiv_for ((aag_can_read aag) \<circ> fst) id (kh (cdt_list s)) (kh' (cdt_list s')) \<rbrakk>
     \<Longrightarrow> reads_equiv aag (cdt_list_update kh s) (cdt_list_update kh' s')"
  by (fastforce simp: reads_equiv_def2 intro: states_equiv_for_cdt_list_update)

lemma reads_equiv_identical_ekheap_updates:
  "\<lbrakk> reads_equiv aag s s'; identical_ekheap_updates s s' (kh (ekheap s)) (kh' (ekheap s')) \<rbrakk>
     \<Longrightarrow> reads_equiv aag (ekheap_update kh s) (ekheap_update kh' s')"
  by (fastforce simp: reads_equiv_def2 intro: states_equiv_for_identical_ekheap_updates)

lemma reads_equiv_ekheap_updates:
  "\<lbrakk> reads_equiv aag s s'; equiv_for (aag_can_read aag) id (kh (ekheap s)) (kh' (ekheap s')) \<rbrakk>
     \<Longrightarrow> reads_equiv aag (ekheap_update kh s) (ekheap_update kh' s')"
  by (fastforce simp: reads_equiv_def2 intro: states_equiv_for_ekheap_update)

lemma reads_equiv_is_original_cap_update:
  "\<lbrakk>reads_equiv aag s s'; equiv_for ((aag_can_read aag) \<circ> fst) id kh kh'\<rbrakk> \<Longrightarrow>
   reads_equiv aag (s\<lparr>is_original_cap := kh\<rparr>) (s'\<lparr>is_original_cap := kh'\<rparr>)"
  by (fastforce simp: reads_equiv_def2 intro: states_equiv_for_is_original_cap_update)

lemma reads_equiv_interrupt_states_update:
  "\<lbrakk> reads_equiv aag s s'; equiv_for (aag_can_read_irq aag) id kh kh' \<rbrakk>
     \<Longrightarrow> reads_equiv aag (s\<lparr>interrupt_states := kh\<rparr>) (s'\<lparr>interrupt_states := kh'\<rparr>)"
  by (fastforce simp: reads_equiv_def2 intro: states_equiv_for_interrupt_states_update)

lemma reads_equiv_interrupt_irq_node_update:
  "\<lbrakk> reads_equiv aag s s'; equiv_for (aag_can_read_irq aag) id kh kh' \<rbrakk>
     \<Longrightarrow> reads_equiv aag (s\<lparr>interrupt_irq_node := kh\<rparr>) (s'\<lparr>interrupt_irq_node := kh'\<rparr>)"
  by (fastforce simp: reads_equiv_def2 intro: states_equiv_for_interrupt_irq_node_update)

lemma reads_equiv_ready_queues_update:
  "\<lbrakk> reads_equiv aag s s'; equiv_for (aag_can_read_domain aag) id kh kh' \<rbrakk>
     \<Longrightarrow> reads_equiv aag (s\<lparr>ready_queues := kh\<rparr>) (s'\<lparr>ready_queues := kh'\<rparr>)"
  by (fastforce simp: reads_equiv_def2 intro: states_equiv_for_ready_queues_update)

lemma reads_equiv_scheduler_action_update:
  "reads_equiv aag s s' \<Longrightarrow>
   reads_equiv aag (s\<lparr>scheduler_action := kh\<rparr>) (s'\<lparr>scheduler_action := kh\<rparr>)"
  by (fastforce simp: reads_equiv_def2 states_equiv_for_def equiv_for_def elim!: equiv_asids_triv)

lemma reads_equiv_work_units_completed_update:
  "reads_equiv aag s s' \<Longrightarrow>
   reads_equiv aag (s\<lparr>work_units_completed := kh\<rparr>) (s'\<lparr>work_units_completed := kh\<rparr>)"
  by (fastforce simp: reads_equiv_def2 states_equiv_for_def equiv_for_def elim!: equiv_asids_triv)

lemma reads_equiv_work_units_completed_update':
  "reads_equiv aag s s' \<Longrightarrow>
   reads_equiv aag (s\<lparr>work_units_completed := (f (work_units_completed s))\<rparr>)
                   (s'\<lparr>work_units_completed := (f (work_units_completed s'))\<rparr>)"
  by (fastforce simp: reads_equiv_def2 states_equiv_for_def equiv_for_def elim!: equiv_asids_triv)

lemma affects_equiv_def2:
  "affects_equiv aag l s s' = states_equiv_for (aag_can_affect aag l)
                                               (aag_can_affect_irq aag l)
                                               (aag_can_affect_asid aag l)
                                               (aag_can_affect_domain aag l) s s'"
  by (auto simp: affects_equiv_def
           dest: equiv_forD
          elim!: states_equiv_forE
         intro!: states_equiv_forI equiv_forI equiv_asids_False)

lemma affects_equivE:
  assumes sef: "affects_equiv aag l s s'"
  obtains "equiv_for (aag_can_affect aag l) kheap s s'"
          "equiv_machine_state (aag_can_affect aag l) (machine_state s) (machine_state s')"
          "equiv_for ((aag_can_affect aag l) \<circ> fst) cdt s s'"
          "equiv_for ((aag_can_affect aag l) \<circ> fst) cdt_list s s'"
          "equiv_for (aag_can_affect aag l) ekheap s s'"
          "equiv_for ((aag_can_affect aag l) \<circ> fst) is_original_cap s s'"
          "equiv_for (aag_can_affect_irq aag l) interrupt_states s s'"
          "equiv_for (aag_can_affect_irq aag l) interrupt_irq_node s s'"
          "equiv_asids (aag_can_affect_asid aag l) s s'"
          "equiv_for (aag_can_affect_domain aag l) ready_queues s s'"
  using sef by (auto simp: affects_equiv_def2 elim: states_equiv_forE)

lemma affects_equiv_machine_state_update:
  "\<lbrakk> affects_equiv aag l s s'; equiv_machine_state (aag_can_affect aag l) kh kh' \<rbrakk>
     \<Longrightarrow> affects_equiv aag l (s\<lparr>machine_state := kh\<rparr>) (s'\<lparr>machine_state := kh'\<rparr>)"
  by (fastforce simp: affects_equiv_def2 intro: states_equiv_for_machine_state_update)

lemma affects_equiv_non_asid_pool_kheap_update:
  "\<lbrakk> affects_equiv aag l s s'; equiv_for (aag_can_affect aag l) id kh kh';
     non_asid_pool_kheap_update s kh; non_asid_pool_kheap_update s' kh' \<rbrakk>
     \<Longrightarrow> affects_equiv aag l (s\<lparr>kheap := kh\<rparr>) (s'\<lparr>kheap := kh'\<rparr>)"
  by (fastforce simp: affects_equiv_def2 intro: states_equiv_for_non_asid_pool_kheap_update)

lemma affects_equiv_identical_kheap_updates:
  "\<lbrakk>affects_equiv aag l s s';
    identical_kheap_updates s s' kh kh'\<rbrakk> \<Longrightarrow>
   affects_equiv aag l (s\<lparr>kheap := kh\<rparr>) (s'\<lparr>kheap := kh'\<rparr>)"
  by (fastforce simp: affects_equiv_def2 intro: states_equiv_for_identical_kheap_updates)

lemma affects_equiv_cdt_update:
  "\<lbrakk>affects_equiv aag l s s'; equiv_for ((aag_can_affect aag l) \<circ> fst) id kh kh'\<rbrakk> \<Longrightarrow>
   affects_equiv aag l (s\<lparr>cdt := kh\<rparr>) (s'\<lparr>cdt := kh'\<rparr>)"
  by (fastforce simp: affects_equiv_def2 intro: states_equiv_for_cdt_update)

lemma affects_equiv_cdt_list_update:
  "\<lbrakk>affects_equiv aag l s s'; equiv_for ((aag_can_affect aag l) \<circ> fst) id (kh (cdt_list s)) (kh' (cdt_list s'))\<rbrakk> \<Longrightarrow>
   affects_equiv aag l (cdt_list_update kh s) (cdt_list_update kh' s')"
  by (fastforce simp: affects_equiv_def2 intro: states_equiv_for_cdt_list_update)

lemma affects_equiv_identical_ekheap_updates:
  "\<lbrakk>affects_equiv aag l s s'; identical_ekheap_updates s s' (kh (ekheap s)) (kh' (ekheap s'))\<rbrakk> \<Longrightarrow>
    affects_equiv aag l (ekheap_update kh s) (ekheap_update kh' s')"
  by (fastforce simp: affects_equiv_def2 intro: states_equiv_for_identical_ekheap_updates)

lemma affects_equiv_ekheap_update:
  "\<lbrakk>affects_equiv aag l s s'; equiv_for (aag_can_affect aag l) id (kh (ekheap s)) (kh' (ekheap s')) \<rbrakk> \<Longrightarrow>
    affects_equiv aag l (ekheap_update kh s) (ekheap_update kh' s')"
  by (fastforce simp: affects_equiv_def2 intro: states_equiv_for_ekheap_update)

lemma affects_equiv_is_original_cap_update:
  "\<lbrakk>affects_equiv aag l s s'; equiv_for ((aag_can_affect aag l) \<circ> fst) id kh kh'\<rbrakk> \<Longrightarrow>
   affects_equiv aag l (s\<lparr>is_original_cap := kh\<rparr>) (s'\<lparr>is_original_cap := kh'\<rparr>)"
  by (fastforce simp: affects_equiv_def2 intro: states_equiv_for_is_original_cap_update)

lemma affects_equiv_interrupt_states_update:
  "\<lbrakk>affects_equiv aag l s s'; equiv_for (aag_can_affect_irq aag l) id kh kh'\<rbrakk> \<Longrightarrow>
   affects_equiv aag l (s\<lparr>interrupt_states := kh\<rparr>) (s'\<lparr>interrupt_states := kh'\<rparr>)"
  by (fastforce simp: affects_equiv_def2 intro: states_equiv_for_interrupt_states_update)

lemma affects_equiv_interrupt_irq_node_update:
  "\<lbrakk>affects_equiv aag l s s'; equiv_for (aag_can_affect_irq aag l) id kh kh'\<rbrakk> \<Longrightarrow>
   affects_equiv aag l (s\<lparr>interrupt_irq_node := kh\<rparr>) (s'\<lparr>interrupt_irq_node := kh'\<rparr>)"
  by (fastforce simp: affects_equiv_def2 intro: states_equiv_for_interrupt_irq_node_update)

lemma affects_equiv_ready_queues_update:
  "\<lbrakk>affects_equiv aag l s s'; equiv_for (aag_can_affect_domain aag l) id kh kh'\<rbrakk> \<Longrightarrow>
   affects_equiv aag l (s\<lparr>ready_queues := kh\<rparr>) (s'\<lparr>ready_queues := kh'\<rparr>)"
  by (fastforce simp: affects_equiv_def2 intro: states_equiv_for_ready_queues_update)

lemma affects_equiv_scheduler_action_update:
  "affects_equiv aag l s s' \<Longrightarrow>
   affects_equiv aag l (s\<lparr>scheduler_action := kh\<rparr>) (s'\<lparr>scheduler_action := kh\<rparr>)"
  by (fastforce simp: affects_equiv_def2 states_equiv_for_def equiv_for_def elim!: equiv_asids_triv)

lemma affects_equiv_work_units_completed_update:
  "affects_equiv aag l s s' \<Longrightarrow>
   affects_equiv aag l (s\<lparr>work_units_completed := kh\<rparr>) (s'\<lparr>work_units_completed := kh\<rparr>)"
  by (fastforce simp: affects_equiv_def2 states_equiv_for_def equiv_for_def elim!: equiv_asids_triv)

lemma affects_equiv_work_units_completed_update':
  "affects_equiv aag l s s' \<Longrightarrow>
   affects_equiv aag l (s\<lparr>work_units_completed := (f (work_units_completed s))\<rparr>)
                       (s'\<lparr>work_units_completed := (f (work_units_completed s'))\<rparr>)"
  by (fastforce simp: affects_equiv_def2 states_equiv_for_def equiv_for_def elim!: equiv_asids_triv)

(* reads_equiv and affects_equiv want to be equivalence relations *)
lemma reads_equiv_refl:
  "reads_equiv aag s s"
  by (auto simp: reads_equiv_def2 intro: states_equiv_for_refl equiv_asids_refl)

lemma reads_equiv_sym:
  "reads_equiv aag s t \<Longrightarrow> reads_equiv aag t s"
  by (auto simp: reads_equiv_def2 intro: states_equiv_for_sym equiv_asids_sym)

lemma reads_equiv_trans:
  "\<lbrakk> reads_equiv aag s t; reads_equiv aag t u \<rbrakk> \<Longrightarrow> reads_equiv aag s u"
  by (auto simp: reads_equiv_def2 intro: states_equiv_for_trans equiv_asids_trans)

lemma affects_equiv_refl:
  "affects_equiv aag l s s"
  by (auto simp: affects_equiv_def intro: states_equiv_for_refl equiv_asids_refl)

lemma affects_equiv_sym:
  "affects_equiv aag l s t \<Longrightarrow> affects_equiv aag l t s"
  by (auto simp: affects_equiv_def2 intro: states_equiv_for_sym equiv_asids_sym)

lemma affects_equiv_trans:
  "\<lbrakk> affects_equiv aag l s t; affects_equiv aag l t u \<rbrakk>
     \<Longrightarrow> affects_equiv aag l s u"
  by (auto simp: affects_equiv_def2 intro: states_equiv_for_trans equiv_asids_trans)

end


lemma globals_equivI:
  "\<lbrakk> doesnt_touch_globals P f; P s; (rv, s') \<in> fst (f s) \<rbrakk>
     \<Longrightarrow> globals_equiv s s'"
  by(fastforce simp: doesnt_touch_globals_def)

lemma reads_equiv_gD:
  "reads_equiv_g aag s s' \<Longrightarrow> reads_equiv aag s s' \<and> globals_equiv s s'"
  by(simp add: reads_equiv_g_def)

lemma reads_equiv_gI:
  "\<lbrakk> reads_equiv aag s s'; globals_equiv s s' \<rbrakk> \<Longrightarrow> reads_equiv_g aag s s'"
  by (simp add: reads_equiv_g_def)

lemma equiv_for_guard_imp:
  "\<lbrakk> equiv_for P f s s'; \<And>x. Q x \<Longrightarrow> P x \<rbrakk> \<Longrightarrow> equiv_for Q f s s'"
  by(auto simp: equiv_for_def)


context InfoFlow_IF_1 begin

(* since doesnt_touch_globals is true for all of the kernel except the scheduler,
   the following lemma shows that we can just prove reads_respects for it, and
   from there get the stronger reads_respects_g result that we need for the
   noninterference theorem *)
lemma reads_respects_g:
  "\<lbrakk> reads_respects aag l P f; doesnt_touch_globals Q f \<rbrakk>
     \<Longrightarrow> reads_respects_g aag l (P and Q) f"
  apply (clarsimp simp: equiv_valid_def2 equiv_valid_2_def)
  apply (drule reads_equiv_gD)
  apply (subgoal_tac "globals_equiv b ba", fastforce intro: reads_equiv_gI)
  apply (rule globals_equiv_trans)
   apply (rule globals_equiv_sym)
   apply (fastforce intro: globals_equivI)
  apply (rule globals_equiv_trans)
   apply (elim conjE, assumption)
  apply (fastforce intro: globals_equivI)
  done

(* prove doesnt_touch_globals as an invariant *)
lemma globals_equiv_invD:
  "\<lbrace>globals_equiv st and P\<rbrace> f \<lbrace>\<lambda>_. globals_equiv st\<rbrace>
   \<Longrightarrow> \<lbrace>P and (=) st\<rbrace> f \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  by (fastforce simp: valid_def intro: globals_equiv_refl)

lemma doesnt_touch_globalsI:
  assumes globals_equiv_inv: "\<And>st. \<lbrace>globals_equiv st and P\<rbrace> f \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  shows "doesnt_touch_globals P f"
  apply (clarsimp simp: doesnt_touch_globals_def)
  apply (cut_tac st=s in globals_equiv_inv)
  by (fastforce dest: globals_equiv_invD simp: valid_def)

(* Slightly nicer to use version to lift up trivial cases*)
lemma reads_respects_g_from_inv:
  "\<lbrakk> reads_respects aag l P f; \<And>st. f \<lbrace>globals_equiv st\<rbrace> \<rbrakk>
     \<Longrightarrow> reads_respects_g aag l P f"
  apply (rule equiv_valid_guard_imp)
   apply (erule reads_respects_g[where Q="\<lambda>s. True"])
   apply (rule doesnt_touch_globalsI)
   apply simp+
  done

lemma globals_equiv_ta_agnostic:
  "ta_agnostic (globals_equiv st)"
  sorry (* in RISCV64 this is true *)

(* as read_respects_g_from_inv, but for tainv *)
lemma reads_respects_g_from_tainv:
  "\<lbrakk> reads_respects aag l P f; \<And>st. f \<lbrace>ignore_ta (globals_equiv st)\<rbrace> \<rbrakk>
     \<Longrightarrow> reads_respects_g aag l P f"
  apply (subst (asm) agnostic_ignores, rule globals_equiv_ta_agnostic)+
  apply (erule reads_respects_g_from_inv; clarsimp)
  done

(*Useful for chaining OFs so we don't have to re-state rules*)
lemma reads_respects_g':
  assumes rev: "reads_respects aag l P f"
  assumes gev: "\<And>st. \<lbrace>\<lambda> s. R (globals_equiv st s) s\<rbrace> f \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  assumes and_imp: "\<And>st s. Q st s \<Longrightarrow> P s \<and> R (globals_equiv st s) s"
  assumes gev_imp: "\<And>st s. R (globals_equiv st s) s \<Longrightarrow> globals_equiv st s"
  shows "reads_respects_g aag l (Q st) f"
  apply (rule equiv_valid_guard_imp)
   apply (rule reads_respects_g[OF rev, where Q="\<lambda>s. R (globals_equiv st s) s"])
   apply (rule doesnt_touch_globalsI)
   apply (rule hoare_pre)
    apply (rule gev)
   apply clarsimp
   apply (frule gev_imp)
   apply (simp add: and_imp)+
  done

lemma states_equiv_for_guard_imp:
  assumes "states_equiv_for P Q R S s s'"
  and "\<And>x. P' x \<Longrightarrow> P x"
  and "\<And>x. Q' x \<Longrightarrow> Q x"
  and "\<And>x. R' x \<Longrightarrow> R x"
  and "\<And>x. S' x \<Longrightarrow> S x"
  shows "states_equiv_for P' Q' R' S' s s'"
  using assms by (auto simp: states_equiv_for_def intro: equiv_for_guard_imp equiv_asids_guard_imp)

lemma set_object_reads_respects:
  "reads_respects aag l \<top> (set_object True ptr obj)"
  apply(clarsimp simp: equiv_valid_def2 equiv_valid_2_def set_object_def get_object_def
                       ta_filter_def obind_def touch_object_def touch_objects_def
                       simpler_do_machine_op_addTouchedAddresses_def simpler_modify_def
                       bind_def' get_def gets_def put_def return_def fail_def assert_def
                split: option.splits)
  apply (rule conjI)
   sorry (* FIXME: broken by touched-addrs -robs
     Need a better simplifier, to update these elim rules, or prove these predicates TA-agnostic.
   apply (erule reads_equiv_identical_kheap_updates)
   apply (clarsimp simp: identical_kheap_updates_def)
  apply (erule affects_equiv_identical_kheap_updates)
  apply (clarsimp simp: identical_kheap_updates_def)
  done
*)

end


lemma cur_subject_reads_equiv_affects_equiv:
  "\<lbrakk> pasSubject aag = l; reads_equiv aag s s' \<rbrakk> \<Longrightarrow> affects_equiv aag l s s'"
  by (auto simp: reads_equiv_def2 affects_equiv_def equiv_for_def states_equiv_for_def)

(* This lemma says that, if we prove reads_respects above for all l, we will prove
   that information can flow into the domain only from what it is allowed to read. *)
lemma reads_equiv_self_reads_respects:
  "pasSubject aag = l \<Longrightarrow> reads_equiv_valid_inv \<top>\<top> aag P f = reads_respects aag l P f"
  unfolding equiv_valid_def2 equiv_valid_2_def
  by (fastforce intro: cur_subject_reads_equiv_affects_equiv)

lemma requiv_get_tcb_eq[intro]:
  "\<lbrakk> reads_equiv aag s t; is_subject aag thread \<rbrakk>
     \<Longrightarrow> get_tcb False thread s = get_tcb False thread t"
  by (auto simp: reads_equiv_def2 get_tcb_def elim: states_equiv_forE_kheap)

lemma requiv_cur_thread_eq[intro]:
  "reads_equiv aag s t \<Longrightarrow> cur_thread s = cur_thread t"
  by (simp add: reads_equiv_def2)

lemma requiv_cur_domain_eq[intro]:
  "reads_equiv aag s t \<Longrightarrow> cur_domain s = cur_domain t"
  by (simp add: reads_equiv_def2)

lemma requiv_sched_act_eq[intro]:
  "reads_equiv aag s t \<Longrightarrow> scheduler_action s = scheduler_action t"
  by (simp add: reads_equiv_def2)

lemma requiv_wuc_eq[intro]:
  "reads_equiv aag s t \<Longrightarrow> work_units_completed s = work_units_completed t"
  by (simp add: reads_equiv_def2)

lemma update_object_noop:
  "kheap s ptr = Some obj \<Longrightarrow> s\<lparr>kheap := kheap s(ptr \<mapsto> obj)\<rparr> = s"
  by (clarsimp simp: map_upd_triv)

lemma set_object_rev:
  "reads_equiv_valid_inv A aag (\<lambda> s. kheap s ptr = Some obj \<and> is_subject aag ptr) (set_object True ptr obj)"
  sorry (* FIXME: broken by touched-addrs -robs
  by (clarsimp simp: equiv_valid_def2 equiv_valid_2_def set_object_def bind_def
                      get_def gets_def put_def return_def assert_def get_object_def
                      obind_def ta_filter_def
                dest: update_object_noop)
*)

lemma lookup_error_on_failure_rev:
  "reads_equiv_valid_inv A aag P m \<Longrightarrow>
   reads_equiv_valid_inv A aag P (lookup_error_on_failure s m)"
  unfolding lookup_error_on_failure_def handleE'_def by (wp | wpc | simp)+

lemma internal_exst[simp]:
  "cdt_list_internal o exst = cdt_list"
  "ekheap_internal o exst = ekheap"
  by (simp_all add: o_def)

lemma gets_kheap_revrv':
  "reads_equiv_valid_rv_inv A aag (equiv_for (aag_can_read aag) id) \<top> (gets kheap)"
  apply (rule equiv_valid_rv_guard_imp)
   apply (rule gets_evrv)
  apply (fastforce simp: equiv_for_comp[symmetric] equiv_for_or or_comp_dist elim: reads_equivE)
  done

lemma gets_cdt_revrv':
  "reads_equiv_valid_rv_inv A aag (equiv_for (aag_can_read aag \<circ> fst) id) \<top> (gets cdt)"
  apply (rule equiv_valid_rv_guard_imp)
   apply (rule gets_evrv)
  apply (fastforce simp: equiv_for_comp[symmetric] equiv_for_or or_comp_dist elim: reads_equivE)
  done

lemma gets_cdt_list_revrv':
  "reads_equiv_valid_rv_inv A aag (equiv_for (aag_can_read aag \<circ> fst) id) \<top> (gets cdt_list)"
  apply(rule equiv_valid_rv_guard_imp)
   apply(rule gets_evrv)
  apply(fastforce simp: equiv_for_comp[symmetric] equiv_for_or or_comp_dist elim: reads_equivE)
  done

lemma gets_is_original_cap_revrv':
  "reads_equiv_valid_rv_inv A aag (equiv_for (aag_can_read aag \<circ> fst) id) \<top> (gets is_original_cap)"
  apply (rule equiv_valid_rv_guard_imp)
   apply (rule gets_evrv)
  apply (fastforce simp: equiv_for_comp[symmetric] equiv_for_or or_comp_dist elim: reads_equivE)
  done

lemma gets_ready_queues_revrv':
  "reads_equiv_valid_rv_inv A aag (equiv_for (aag_can_read_domain aag) id) \<top> (gets ready_queues)"
  apply (rule equiv_valid_rv_guard_imp)
   apply (rule gets_evrv)
  (* NB: only force works here *)
  apply (force simp: equiv_for_comp equiv_for_def disjoint_iff_not_equal elim: reads_equivE)
  done

(* We want to prove this kind of thing for functions that don't modify the state *)
lemma gets_cur_thread_ev:
  "reads_equiv_valid_inv A aag \<top> (gets cur_thread)"
  apply (rule equiv_valid_guard_imp)
  apply wp
  apply (simp add: reads_equiv_def)
  done

lemma as_user_rev:
  "reads_equiv_valid_inv A aag (K (det f \<and> (\<forall>P. f \<lbrace>P\<rbrace>) \<and> is_subject aag thread)) (as_user thread f)"
  unfolding as_user_def fun_app_def split_def
  apply (wp set_object_rev select_f_ev touch_object_wp')
    sorry (* FIXME: broken by touched-addrs -robs
  apply (rule conjI, fastforce)
  apply (clarsimp split: option.split_asm kernel_object.split_asm simp: get_tcb_def)
  apply (drule state_unchanged[rotated,symmetric])
   apply simp_all
  done
*)


context InfoFlow_IF_1 begin

lemma gets_kheap_revrv:
  "reads_equiv_valid_rv_inv (affects_equiv aag l) aag
                            (equiv_for (aag_can_read aag or aag_can_affect aag l) id) \<top> (gets kheap)"
  apply (rule equiv_valid_rv_guard_imp)
   apply (rule gets_evrv)
  apply (fastforce simp: equiv_for_comp[symmetric] equiv_for_or or_comp_dist
                   elim: reads_equivE affects_equivE)
  done

lemma gets_machine_state_revrv:
  "reads_equiv_valid_rv_inv (affects_equiv aag l) aag
     (equiv_machine_state (aag_can_read aag or aag_can_affect aag l) And equiv_irq_state)
     \<top> (gets machine_state)"
  by (fastforce simp: equiv_valid_2_def gets_def get_def return_def bind_def
                elim: reads_equivE affects_equivE equiv_forE
               intro: equiv_forI)

lemma gets_machine_state_revrv':
  "reads_equiv_valid_rv_inv A aag (equiv_machine_state (aag_can_read aag) And equiv_irq_state)
                            \<top> (gets machine_state)"
  by (fastforce simp: equiv_valid_2_def gets_def get_def return_def bind_def
                elim: reads_equivE affects_equivE equiv_forE
               intro: equiv_forI)

lemma gets_cdt_revrv:
  "reads_equiv_valid_rv_inv (affects_equiv aag l) aag
                            (equiv_for ((aag_can_read aag or aag_can_affect aag l) \<circ> fst) id)
                            \<top> (gets cdt)"
  apply (rule equiv_valid_rv_guard_imp)
   apply (rule gets_evrv)
  apply (fastforce simp: equiv_for_comp[symmetric] equiv_for_or or_comp_dist
                   elim: reads_equivE affects_equivE)
  done

lemma gets_cdt_list_revrv:
  "reads_equiv_valid_rv_inv (affects_equiv aag l) aag
                            (equiv_for ((aag_can_read aag or aag_can_affect aag l) \<circ> fst) id)
                            \<top> (gets cdt_list)"
  apply (rule equiv_valid_rv_guard_imp)
   apply (rule gets_evrv)
  apply (fastforce simp: equiv_for_comp[symmetric] equiv_for_or or_comp_dist
                   elim: reads_equivE affects_equivE)
  done

lemma gets_ekheap_revrv:
  "reads_equiv_valid_rv_inv (affects_equiv aag l) aag
                            (equiv_for (aag_can_read aag or aag_can_affect aag l) id) \<top> (gets ekheap)"
  apply (rule equiv_valid_rv_guard_imp)
   apply (rule gets_evrv)
  apply (fastforce simp: equiv_for_comp[symmetric] equiv_for_or or_comp_dist
                   elim: reads_equivE affects_equivE)
  done

lemma gets_is_original_cap_revrv:
  "reads_equiv_valid_rv_inv (affects_equiv aag l) aag
                            (equiv_for ((aag_can_read aag or aag_can_affect aag l) \<circ> fst) id)
                            \<top> (gets is_original_cap)"
  apply (rule equiv_valid_rv_guard_imp)
   apply (rule gets_evrv)
  apply (fastforce simp: equiv_for_comp[symmetric] equiv_for_or or_comp_dist
                  elim: reads_equivE affects_equivE)
  done

lemma gets_ready_queues_revrv:
  "reads_equiv_valid_rv_inv (affects_equiv aag l) aag
                            (equiv_for (aag_can_read_domain aag or aag_can_affect_domain aag l) id)
                            \<top> (gets ready_queues)"
  apply (rule equiv_valid_rv_guard_imp)
   apply (rule gets_evrv)
  (* NB: only clarsimp works here *)
  apply (clarsimp simp: equiv_for_def disjoint_iff_not_equal elim!: reads_equivE affects_equivE)
  done

lemma as_user_reads_respects:
  "reads_respects aag l (K (det f \<and> is_subject aag thread)) (as_user thread f)"
  apply (simp add: as_user_def split_def)
  apply (rule gen_asm_ev)
  apply (wp set_object_reads_respects select_f_ev gets_the_ev touch_object_wp')
    sorry (* FIXME: broken by touched-addrs -robs
  apply fastforce
  done
*)

end


lemma get_message_info_rev:
  "reads_equiv_valid_inv A aag (K (is_subject aag ptr)) (get_message_info ptr)"
  by (wpsimp wp: as_user_rev getRegister_inv simp: get_message_info_def det_getRegister)

lemma syscall_rev:
  assumes reads_res_m_fault:
    "reads_equiv_valid_inv A aag P m_fault"
  assumes reads_res_m_error:
    "\<And>v. reads_equiv_valid_inv A aag (Q (Inr v)) (m_error v)"
  assumes reads_res_h_fault:
    "\<And>v. reads_equiv_valid_inv A aag (Q (Inl v)) (h_fault v)"
  assumes reads_res_m_finalise:
    "\<And>v. reads_equiv_valid_inv A aag (R (Inr v)) (m_finalise v)"
  assumes reads_res_h_error:
    "\<And>v. reads_equiv_valid_inv A aag (R (Inl v)) (h_error v)"
  assumes m_fault_hoare:
    "\<lbrace>P\<rbrace> m_fault \<lbrace>Q\<rbrace>"
  assumes m_error_hoare:
    "\<And>v. \<lbrace>Q (Inr v)\<rbrace> m_error v \<lbrace>R\<rbrace>"
  shows "reads_equiv_valid_inv A aag P (Syscall_A.syscall m_fault h_fault m_error h_error m_finalise)"
  unfolding Syscall_A.syscall_def without_preemption_def fun_app_def
  by (wp assms equiv_valid_guard_imp[OF liftE_bindE_ev]
      | rule hoare_strengthen_post[OF m_error_hoare]
      | rule hoare_strengthen_post[OF m_fault_hoare]
      | wpc
      | fastforce)+

lemma syscall_reads_respects_g:
  assumes reads_res_m_fault:
    "reads_respects_g aag l P m_fault"
  assumes reads_res_m_error:
    "\<And>v. reads_respects_g aag l (Q'' v) (m_error v)"
  assumes reads_res_h_fault:
    "\<And>v. reads_respects_g aag l (Q' v) (h_fault v)"
  assumes reads_res_m_finalise:
    "\<And>v. reads_respects_g aag l (R'' v) (m_finalise v)"
  assumes reads_res_h_error:
    "\<And>v. reads_respects_g aag l (R' v) (h_error v)"
  assumes m_fault_hoare:
    "\<lbrace>P\<rbrace> m_fault \<lbrace>case_sum Q' Q''\<rbrace>"
  assumes m_error_hoare:
    "\<And>v. \<lbrace>Q'' v\<rbrace> m_error v \<lbrace>case_sum R' R''\<rbrace>"
  shows "reads_respects_g aag l P (Syscall_A.syscall m_fault h_fault m_error h_error m_finalise)"
  unfolding Syscall_A.syscall_def without_preemption_def fun_app_def
  by (wp assms equiv_valid_guard_imp[OF liftE_bindE_ev]
      | rule hoare_strengthen_post[OF m_error_hoare]
      | rule hoare_strengthen_post[OF m_fault_hoare]
      | wpc
      | fastforce)+


context InfoFlow_IF_1 begin

lemma do_machine_op_spec_reads_respects':
  assumes equiv_dmo:
   "equiv_valid_inv (equiv_machine_state (aag_can_read aag) And equiv_irq_state)
                    (equiv_machine_state (aag_can_affect aag l)) Q f"
  assumes guard:
    "\<And>s. P s \<Longrightarrow> Q (machine_state s)"
  shows
  "spec_reads_respects st aag l P (do_machine_op f)"
  unfolding do_machine_op_def spec_equiv_valid_def
  apply (rule equiv_valid_2_guard_imp)
   apply (rule_tac  R'="\<lambda> rv rv'. equiv_machine_state (aag_can_read aag or aag_can_affect aag l) rv rv' \<and> equiv_irq_state rv rv'" and Q="\<lambda> r s. st = s \<and> Q r" and Q'="\<lambda> r s. Q r" and P="(=) st" and P'="\<top>" in equiv_valid_2_bind)
       apply (rule gen_asm_ev2_l[simplified K_def pred_conj_def])
       apply (rule gen_asm_ev2_r')
       apply (rule_tac R'="\<lambda> (r, ms') (r', ms'').  r = r' \<and> equiv_machine_state (aag_can_read aag)  ms' ms'' \<and> equiv_machine_state (aag_can_affect aag l) ms' ms'' \<and> equiv_irq_state ms' ms''" and Q="\<lambda> r s. st = s" and Q'="\<top>\<top>" and P="\<top>" and P'="\<top>" in equiv_valid_2_bind_pre)
            apply (clarsimp simp: modify_def get_def put_def bind_def return_def equiv_valid_2_def)
            apply (fastforce intro: reads_equiv_machine_state_update affects_equiv_machine_state_update)
            apply (insert equiv_dmo)[1]
           apply (clarsimp simp: select_f_def equiv_valid_2_def equiv_valid_def2 equiv_for_or simp: split_def split: prod.splits simp: equiv_for_def)[1]
           apply (drule_tac x=rv in spec, drule_tac x=rv' in spec)
           apply (fastforce)
          apply (rule select_f_inv)
         apply (rule wp_post_taut)
        apply simp+
      apply (clarsimp simp: equiv_valid_2_def in_monad)
      apply (fastforce elim: reads_equivE affects_equivE equiv_forE intro: equiv_forI)
     apply (wp | simp add: guard)+
  done

(* most of the time (i.e. always except for getActiveIRQ) you'll want this rule *)
lemma do_machine_op_spec_reads_respects:
  assumes equiv_dmo:
   "equiv_valid_inv (equiv_machine_state (aag_can_read aag)) (equiv_machine_state (aag_can_affect aag l)) \<top> f"
  assumes irq_state_inv:
    "\<And>P. \<lbrace>\<lambda>ms. P (irq_state ms)\<rbrace> f \<lbrace>\<lambda>_ ms. P (irq_state ms)\<rbrace>"
  shows
    "spec_reads_respects st aag l \<top> (do_machine_op f)"
  apply (rule do_machine_op_spec_reads_respects'[where Q=\<top>, simplified])
  apply (clarsimp simp: equiv_valid_def2 equiv_valid_2_def)
  apply (subgoal_tac "equiv_irq_state b ba", simp)
   apply (insert equiv_dmo, fastforce simp: equiv_valid_def2 equiv_valid_2_def)
  apply (insert irq_state_inv)
  apply (drule_tac x="\<lambda>ms. ms = irq_state s" in meta_spec)
  apply (clarsimp simp: valid_def)
  apply (frule_tac x=s in spec)
  apply (erule (1) impE)
  apply (drule bspec, assumption, simp)
  apply (drule_tac x=t in spec, simp)
  apply (drule bspec, assumption)
  apply simp
  done

lemma do_machine_op_rev:
  assumes equiv_dmo: "equiv_valid_inv (equiv_machine_state (aag_can_read aag)) \<top>\<top> \<top> f"
  assumes mo_inv: "\<And>P. f \<lbrace>P\<rbrace>"
  shows "reads_equiv_valid_inv A aag \<top> (do_machine_op f)"
  unfolding do_machine_op_def equiv_valid_def2
  apply (rule_tac W="\<lambda> rv rv'. equiv_machine_state (aag_can_read aag) rv rv' \<and> equiv_irq_state rv rv'"
             and Q="\<lambda> rv s. rv = machine_state s " in equiv_valid_rv_bind)
    apply (blast intro: equiv_valid_rv_guard_imp[OF gets_machine_state_revrv'[simplified bipred_conj_def]])
   apply (rule_tac R'="\<lambda> (r, ms') (r', ms'').  r = r' \<and> equiv_machine_state (aag_can_read aag) ms' ms''"
              and Q="\<lambda> (r,ms') s. ms' = rv \<and> rv = machine_state s "
              and Q'="\<lambda> (r',ms'') s. ms'' = rv' \<and> rv' = machine_state s"
              and P="\<top>" and P'="\<top>" in equiv_valid_2_bind_pre)
        apply (clarsimp simp: modify_def get_def put_def bind_def return_def equiv_valid_2_def)
       apply (clarsimp simp: select_f_def equiv_valid_2_def)
       apply (insert equiv_dmo, clarsimp simp: equiv_valid_def2 equiv_valid_2_def)[1]
       apply blast
    apply (wp select_f_inv)+
    apply (fastforce simp: select_f_def dest: state_unchanged[OF mo_inv])+
  done

end


lemma do_machine_op_spec_rev:
  assumes equiv_dmo:
    "spec_equiv_valid_inv (machine_state st) (equiv_machine_state (aag_can_read aag)) \<top>\<top> \<top> f"
  assumes mo_inv: "\<And>P. f \<lbrace>P\<rbrace>"
  shows "reads_spec_equiv_valid_inv st A aag P (do_machine_op f)"
  unfolding do_machine_op_def spec_equiv_valid_def
  apply (rule equiv_valid_2_guard_imp)
   apply (rule_tac R'="\<lambda>rv rv'. equiv_machine_state (aag_can_read aag) rv rv' \<and>
                                equiv_irq_state rv rv'"
               and Q="\<lambda>r s. st = s \<and> r = machine_state s"
               and Q'="\<lambda>r s. r = machine_state s"
               and P="(=) st" and P'=\<top>
                in equiv_valid_2_bind)
       apply (rule_tac R'="\<lambda>(r, ms') (r', ms''). r = r' \<and>
                                                 equiv_machine_state (aag_can_read aag) ms' ms''"
                   and Q="\<lambda>(r,ms') s. ms' = rv \<and> rv = machine_state s \<and> st = s"
                   and Q'="\<lambda>(r,ms') s. ms' = rv' \<and> rv' = machine_state s"
                   and P="\<lambda>s. st = s \<and> rv = machine_state s" and P'="\<lambda> s. rv' = machine_state s"
                   and S="\<lambda>s. st = s \<and> rv = machine_state s" and S'="\<lambda>s. rv' = machine_state s"
                    in equiv_valid_2_bind_pre)
            apply (clarsimp simp: modify_def get_def put_def bind_def return_def equiv_valid_2_def)
           apply (clarsimp simp: select_f_def equiv_valid_2_def equiv_valid_def2 equiv_for_or
                                 split_def equiv_for_def
                          split: prod.splits)
           apply (insert equiv_dmo)[1]
           apply (clarsimp simp: spec_equiv_valid_def equiv_valid_2_def)
           apply (drule_tac x="machine_state t" in spec)
           apply (clarsimp simp: equiv_for_def)
           apply blast
          apply (wp select_f_inv)
          apply clarsimp
          apply (drule state_unchanged[OF mo_inv], simp)
         apply (wp select_f_inv)
         apply clarsimp
         apply (drule state_unchanged[OF mo_inv], simp)
        apply simp+
      apply (clarsimp simp: equiv_valid_2_def in_monad)
      apply (fastforce intro: elim: equiv_forE reads_equivE)
     apply (wp | simp)+
  done

lemma spec_equiv_valid_hoist_guard:
  "((P st) \<Longrightarrow> spec_equiv_valid_inv st I A \<top> f) \<Longrightarrow> spec_equiv_valid_inv st I A P f"
  by (clarsimp simp: spec_equiv_valid_def equiv_valid_2_def)

lemma for_each_byte_of_word_imp:
  "\<lbrakk> \<And>x. P x \<Longrightarrow> Q x; for_each_byte_of_word P p \<rbrakk>
     \<Longrightarrow> for_each_byte_of_word Q p"
  by (fastforce simp: for_each_byte_of_word_def)

lemma modifies_at_mostD:
  "\<lbrakk> modifies_at_most aag L P f; P s; (rv,s') \<in> fst(f s) \<rbrakk>
     \<Longrightarrow> equiv_but_for_labels aag L s s'"
  by (auto simp: modifies_at_most_def)

(* FIXME: Move *)
lemma invs_kernel_mappings:
  "invs s \<Longrightarrow> valid_kernel_mappings s"
  by (auto simp: invs_def valid_state_def)


context InfoFlow_IF_1 begin

lemma load_word_offs_rev:
  "for_each_byte_of_word (aag_can_read aag) (a + of_nat x * of_nat word_size)
   \<Longrightarrow> reads_equiv_valid_inv A aag \<top> (load_word_offs a x)"
  unfolding load_word_offs_def fun_app_def
  sorry (* FIXME: broken by touched-addrs -robs
  by (fastforce intro: equiv_valid_guard_imp[OF dmo_loadWord_rev])
*)

lemma modifies_at_mostI:
  assumes hoare: "\<And>st. \<lbrace>P and equiv_but_for_labels aag L st\<rbrace> f \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  shows "modifies_at_most aag L P f"
  apply (clarsimp simp: modifies_at_most_def)
  apply (erule use_valid)
   apply (rule hoare)
  apply (fastforce simp: equiv_but_for_labels_def states_equiv_for_refl)
  done

end

end
