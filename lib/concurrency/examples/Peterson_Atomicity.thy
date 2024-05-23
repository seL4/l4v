(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)
theory Peterson_Atomicity
imports
  Lib.Lib
  Atomicity_Lib
begin

text \<open>
 Preliminaries, a type of identities.
\<close>

datatype ident = A | B

primrec other_ident where
    "other_ident A = B"
  | "other_ident B = A"

lemma other_ident_split:
  "P (other_ident x) = ((x = A \<longrightarrow> P B) \<and> (x = B \<longrightarrow> P A))"
  by (cases x, simp_all)

lemma neq_A_B[simp]:
  "(x \<noteq> A) = (x = B)"
  "(A \<noteq> x) = (x = B)"
  "(x \<noteq> B) = (x = A)"
  "(B \<noteq> x) = (x = A)"
  by (simp | cases x)+

lemma forall_ident_eq:
  "(\<forall>ident. P ident) = (P A \<and> P B)"
  using ident.nchotomy
  by (metis (full_types))

lemma other_other_ident_simps[simp]:
  "other_ident (other_ident x) = x"
  "(other_ident x = y) = (x \<noteq> y)"
  "(x = other_ident y) = (x \<noteq> y)"
  by (simp_all split: other_ident_split add: eq_commute)

text \<open>
  The state of the algorithm. The variables A/B are condensed into
  an ab_v variable, so we can parametrise by thread A/B. The priority
  variable is t_v, and the critical section cs has two variable to
  operate on, cs1_v and cs2_v.

  Labels are needed to track where we're up to for the preconditions,
  relies and guarantees.\<close>

datatype label = Awaiting | Critical | Exited

record ('a, 'b) p_state =
  ab_v :: "ident \<Rightarrow> bool"
  ab_label :: "ident \<Rightarrow> label"
  t_v :: "ident"
  cs1_v :: "'a"
  cs2_v :: "'b"

locale mx_locale =
  fixes cs1 :: "'b \<Rightarrow> 'a"
    and cs2 :: "(('a, 'b) p_state, unit) tmonad"
    and csI :: "'b \<Rightarrow> bool"
begin

definition set_ab :: "ident \<Rightarrow> bool \<Rightarrow> ('a, 'b) p_state \<Rightarrow> ('a, 'b) p_state" where
  "set_ab ident trying s = (s \<lparr> ab_v := (ab_v s) (ident := trying) \<rparr>)"

definition set_label :: "ident \<Rightarrow> label \<Rightarrow> ('a, 'b) p_state \<Rightarrow> ('a, 'b) p_state" where
  "set_label ident label s = (s \<lparr> ab_label := (ab_label s) (ident := label) \<rparr>)"

definition locked :: "ident \<Rightarrow> ('a, 'b) p_state \<Rightarrow> bool" where
  "locked ident s = (ab_v s (other_ident ident) \<longrightarrow> t_v s = ident)"

definition acquire_lock :: "ident \<Rightarrow> (('a, 'b) p_state, unit) tmonad" where
  "acquire_lock ident = do
     interference;
     modify (set_ab ident True);
     modify (\<lambda>s. s \<lparr> t_v := other_ident ident \<rparr>);
     modify (set_label ident Awaiting);
     interference;
     Await (locked ident);
     modify (set_label ident Critical)
   od"

definition release_lock :: "ident \<Rightarrow> (('a, 'b) p_state, unit) tmonad" where
  "release_lock ident = do
     modify (set_ab ident False);
     modify (set_label ident Exited);
     interference;
     return ()
   od"

definition abs_critical_section :: "(('a, 'b) p_state, unit) tmonad" where
  "abs_critical_section = do
     interferences;
     modify (\<lambda>s. s \<lparr> cs1_v := cs1 (cs2_v s) \<rparr>);
     cs2;
     interference
   od"

definition abs_peterson_proc :: "ident \<Rightarrow> (('a, 'b) p_state, unit) tmonad" where
  "abs_peterson_proc ident = do
     acquire_lock ident;
     abs_critical_section;
     release_lock ident
   od"

definition critical_section :: "(('a, 'b) p_state, unit) tmonad" where
  "critical_section = do
     interference;
     modify (\<lambda>s. s \<lparr> cs1_v := cs1 (cs2_v s) \<rparr>);
     interference;
     cs2;
     interference
   od"

definition peterson_proc :: "ident \<Rightarrow> (('a, 'b) p_state, unit) tmonad" where
  "peterson_proc ident = do
     acquire_lock ident;
     critical_section;
     release_lock ident
   od"

abbreviation "critical label \<equiv> label = Critical"

text \<open>
  The required invariant. We can't both be in the critical section.
  Whenever neither of us is in the critical section, its invariant holds.\<close>
definition req_peterson_inv :: "('a, 'b) p_state \<Rightarrow> bool" where
  "req_peterson_inv s =
     (\<not> (critical (ab_label s A) \<and> critical (ab_label s B))
      \<and> (critical (ab_label s A) \<or> critical (ab_label s B) \<or> csI (cs2_v s)))"

text \<open>
  The key invariant. We can't both be enabled, where that means
  either we're in the critical section or waiting to enter with priority.\<close>
abbreviation (input) enabled :: "ident \<Rightarrow> ('a, 'b) p_state \<Rightarrow> bool" where
  "enabled ident s \<equiv>
     critical (ab_label s ident) \<or> ab_label s ident = Awaiting \<and> t_v s = ident"

definition key_peterson_inv :: "('a, 'b) p_state \<Rightarrow> bool" where
  "key_peterson_inv s = (\<not> (enabled A s \<and> enabled B s))"

text \<open>Some trivia about labels and variables.\<close>
definition local_peterson_inv :: "('a, 'b) p_state \<Rightarrow> bool" where
  "local_peterson_inv s = (\<forall>ident. ab_label s ident \<noteq> Exited \<longrightarrow> ab_v s ident)"

definition
  "invs s = (req_peterson_inv s \<and> key_peterson_inv s \<and> local_peterson_inv s)"

lemmas invs_defs = req_peterson_inv_def key_peterson_inv_def local_peterson_inv_def

definition peterson_rel :: "ident \<Rightarrow> ('a, 'b) p_state \<Rightarrow> ('a, 'b) p_state \<Rightarrow> bool" where
  "peterson_rel ident s_prior s =
     (\<comment> \<open>assume invs\<close> invs s_prior \<longrightarrow>
            \<comment> \<open>invariants are preserved\<close>
        (invs s
            \<comment> \<open>I won't adjust your variables\<close>
         \<and> (ab_v s (other_ident ident) = ab_v s_prior (other_ident ident))
         \<and> (ab_label s (other_ident ident) = ab_label s_prior (other_ident ident))
            \<comment> \<open>I will only ever give you priority\<close>
         \<and> (t_v s_prior = other_ident ident \<longrightarrow> t_v s = other_ident ident)
            \<comment> \<open>If you're in the critical section, I won't change cs2_v and cs1_v\<close>
         \<and> (critical (ab_label s_prior (other_ident ident))
              \<longrightarrow> cs2_v s = cs2_v s_prior \<and> cs1_v s = cs1_v s_prior)))"

lemma peterson_rel_rtranclp[simp]:
  "rtranclp (peterson_rel ident) = (peterson_rel ident)"
  apply (rule rtranclp_id2)
   apply (clarsimp simp: peterson_rel_def)
  apply (clarsimp simp: peterson_rel_def)
  done

lemma reflp_peterson_rel[simp]:
 "reflp (peterson_rel x)"
  apply (rule reflpI)
  apply (clarsimp simp add: peterson_rel_def)
  done
declare reflp_peterson_rel[THEN reflpD, simp]

lemma peterson_rel_imp_assume_invs:
  "\<lbrakk>invs x; peterson_rel ident x y \<and> invs x \<and> invs y \<longrightarrow> P x y\<rbrakk>
   \<Longrightarrow> peterson_rel ident x y \<longrightarrow> P x y"
  by (simp add: peterson_rel_def)

end

text \<open>
  We assume validity for the underspecified critical section code represented by
  @{text cs2}.

  We also assume some basic sanity properties about the structure of @{text cs2}.\<close>
locale mx_locale_wp = mx_locale cs1 cs2 csI for cs1 :: "'b \<Rightarrow> 'a" and cs2 and csI +
  assumes
    cs_wp: "\<forall>s c. I s \<and> lockf s \<longrightarrow> I s \<and> lockf (s \<lparr> cs2_v := c \<rparr>)
      \<Longrightarrow>
      \<lbrace>\<lambda>s0' s'. csI (cs2_v s') \<and> s0' = s0 \<and> s' = s \<and> I s \<and> lockf s
                \<and> cs1_v s' = cs1 (cs2_v s')\<rbrace>,
      \<lbrace>\<lambda>s0 s. I s0 \<and> lockf s0 \<longrightarrow> cs2_v s = cs2_v s0 \<and> I s \<and> lockf s \<and> cs1_v s = cs1_v s0\<rbrace>
      cs2
      \<lbrace>\<lambda>s0 s. I s0 \<longrightarrow> (\<exists>c. s = s0 \<lparr> cs2_v := c \<rparr>) \<and> I s \<and> lockf s\<rbrace>,
      \<lbrace>\<lambda>_ s0' s'. \<exists>c. csI c \<and> s' = s \<lparr> cs2_v := c \<rparr>
                      \<and> (\<exists>c'. s0' = s0 \<or> s0' = s \<lparr> cs2_v := c' \<rparr>)
                      \<and> I s' \<and> lockf s'\<rbrace>"
    and cs_closed: "prefix_closed cs2"
    and cs_not_env_steps_first: "not_env_steps_first cs2"
begin

method_setup rev_drule =
  \<open>Attrib.thms >>
   curry (fn (thms, ctxt) =>
     SIMPLE_METHOD (dresolve_tac ctxt thms 1 #> Seq.list_of #> rev #> Seq.of_list))\<close>

lemma cs2_wp_apply_peterson[wp]:
 "\<lbrace>\<lambda>s0 s. csI (cs2_v s)
     \<and> invs s0 \<and> invs s \<and> critical (ab_label s ident)
     \<and> cs1_v s = cs1 (cs2_v s)
     \<and> (\<forall>s0' c' c. csI c \<longrightarrow> (\<exists>c'. s0' = s0 \<or> s0' = s \<lparr> cs2_v := c' \<rparr>)
          \<longrightarrow>  Q () s0' (s \<lparr> cs2_v := c\<rparr>))\<rbrace>,
  \<lbrace>peterson_rel (other_ident ident)\<rbrace>
  cs2
  \<lbrace>peterson_rel ident\<rbrace>,
  \<lbrace>Q\<rbrace>"
  apply (rule validI_name_pre[OF cs_closed], clarsimp simp del: imp_disjL)
  apply (rule rg_weaken_pre)
   apply (rule validI_well_behaved[OF cs_closed])
     apply (rule rg_strengthen_post)
      apply (rule_tac s=s and ?s0.0=s0
                  and lockf="\<lambda>s. critical (ab_label s ident)"
                  and I="invs"
                   in cs_wp)
      apply (clarsimp simp: invs_defs invs_def)
     apply (clarsimp simp del: imp_disjL)
    apply (simp only: imp_conjL[symmetric])
    apply (thin_tac "\<forall>x. P x" for P)
    apply (clarsimp simp: peterson_rel_def)
   apply (thin_tac "\<forall>x. P x" for P)
   apply (clarsimp simp: peterson_rel_def)
   apply (cases ident; fastforce simp: invs_def key_peterson_inv_def)
  apply clarsimp
  done

lemma release_lock_mutual_excl:
  "\<lbrace>\<lambda>s0 s. peterson_rel ident s0 s \<and> invs s \<and> ab_label s ident = Critical \<and> csI (cs2_v s)\<rbrace>,
   \<lbrace>peterson_rel (other_ident ident)\<rbrace>
   release_lock ident
   \<lbrace>peterson_rel ident\<rbrace>,
   \<lbrace>\<lambda>rv s0 s. peterson_rel ident s0 s \<and> invs s \<and> ab_label s ident = Exited\<rbrace>"
  apply (simp add: release_lock_def)
  apply wpsimp
  apply (strengthen peterson_rel_imp_assume_invs | simp)+
  apply (cases ident)
   apply (safe, simp_all)
  by (clarsimp simp: peterson_rel_def set_label_def set_ab_def invs_defs
      | rule invs_def[THEN iffD2] conjI
      | rev_drule invs_def[THEN iffD1])+

lemma abs_critical_section_mutual_excl:
  "\<lbrace>\<lambda>s0 s. peterson_rel ident s0 s \<and> invs s \<and> invs s0 \<and> ab_label s ident = Critical \<and> csI (cs2_v s)\<rbrace>,
   \<lbrace>peterson_rel (other_ident ident)\<rbrace>
   abs_critical_section
   \<lbrace>peterson_rel ident\<rbrace>,
   \<lbrace>\<lambda>rv s0 s. peterson_rel ident s0 s \<and> invs s \<and> ab_label s ident = Critical \<and> csI (cs2_v s)\<rbrace>"
  apply (simp add: abs_critical_section_def)
  apply wpsimp
  apply (strengthen peterson_rel_imp_assume_invs | simp)+
  apply (cases ident)
   apply (safe, simp_all)
  by (clarsimp simp: peterson_rel_def invs_defs
      | rule invs_def[THEN iffD2] conjI
      | rev_drule invs_def[THEN iffD1])+

lemma acquire_lock_mutual_excl:
  "\<lbrace>\<lambda>s0 s. peterson_rel ident s0 s \<and> invs s \<and> ab_label s ident = Exited\<rbrace>,
   \<lbrace>peterson_rel (other_ident ident)\<rbrace>
   acquire_lock ident
   \<lbrace>peterson_rel ident\<rbrace>,
   \<lbrace>\<lambda>rv s0 s. peterson_rel ident s0 s \<and> invs s \<and> invs s0
              \<and> ab_label s ident = Critical \<and> csI (cs2_v s)\<rbrace>"
  apply (simp add: acquire_lock_def)
  apply (wpsimp wp: Await_sync_twp)
  apply (strengthen peterson_rel_imp_assume_invs | simp)+
  apply (cases ident)
   apply (safe, simp_all)
  by (clarsimp simp: peterson_rel_def set_label_def set_ab_def locked_def invs_defs
      | rule invs_def[THEN iffD2] conjI
      | rev_drule invs_def[THEN iffD1])+

theorem abs_peterson_proc_mutual_excl:
  "\<lbrace>\<lambda>s0 s. peterson_rel ident s0 s \<and> invs s \<and> ab_label s ident = Exited\<rbrace>,
   \<lbrace>peterson_rel (other_ident ident)\<rbrace>
   abs_peterson_proc ident
   \<lbrace>peterson_rel ident\<rbrace>,
   \<lbrace>\<lambda>rv s0 s. peterson_rel ident s0 s \<and> invs s \<and> ab_label s ident = Exited\<rbrace>"
  apply (simp add: abs_peterson_proc_def bind_assoc)
  apply (wpsimp wp: release_lock_mutual_excl acquire_lock_mutual_excl
                    abs_critical_section_mutual_excl)
  done

definition peterson_sr :: "(('a, 'b) p_state \<Rightarrow> ('a, 'b) p_state  \<Rightarrow> bool)" where
  "peterson_sr sa sc \<equiv>
     t_v sa = t_v sc \<and> ab_v sa = ab_v sc \<and> ab_label sa = ab_label sc \<and> cs2_v sa = cs2_v sc"

definition peterson_sr' :: "(('a, 'b) p_state \<Rightarrow> ('a, 'b) p_state  \<Rightarrow> bool)" where
  "peterson_sr' sa sc \<equiv> sa = sc \<lparr> cs1_v := cs1_v sa \<rparr>"

definition peterson_sr_cs1 :: "(('a, 'b) p_state \<Rightarrow> ('a, 'b) p_state  \<Rightarrow> bool)" where
  "peterson_sr_cs1 sa sc \<equiv> peterson_sr sa sc \<and> cs1_v sa = cs1_v sc"

end

text \<open>
  Finally we assume that we can prove refinement for @{text cs2}, although this
  may depend on being in a state where @{term cs1_v} has been correctly
  initialised.\<close>
locale mx_locale_refine = mx_locale_wp cs1 cs2 csI for cs1 :: "'b \<Rightarrow> 'a" and cs2 and csI +
  assumes
    cs_refine:
    "prefix_refinement peterson_sr peterson_sr_cs1 peterson_sr \<top>\<top>
                       (peterson_rel (other_ident ident)) (peterson_rel (other_ident ident))
                       (\<lambda>_ s. cs1_v s = cs1 (cs2_v s)) \<top>\<top>
                       cs2 cs2"
begin

lemma
  "peterson_sr = peterson_sr'"
  by (auto simp: p_state.splits peterson_sr_def peterson_sr'_def intro!: ext)

lemma peterson_sr_set_ab[simp]:
  "peterson_sr s t \<Longrightarrow> peterson_sr (set_ab ident v s) (set_ab ident v t)"
  by (simp add: peterson_sr_def set_ab_def)

lemma env_stable_peterson_sr:
  "env_stable AR R peterson_sr peterson_sr \<top>"
  by (fastforce simp: env_stable_def rely_stable_def env_rely_stable_iosr_def peterson_sr_def)

lemmas prefix_refinement_interference_peterson =
  prefix_refinement_interference[OF env_stable_peterson_sr]

lemma peterson_sr_reflp[simp]:
  "reflp peterson_sr"
  by (simp add: peterson_sr_def reflpI)

lemma peterson_sr_equivp[simp]:
  "equivp peterson_sr"
  by (auto simp: peterson_sr_def intro!: sympI equivpI transpI)

lemma peterson_sr_cs1_invs:
  "peterson_sr_cs1 s t \<Longrightarrow> invs s = invs t"
  apply (auto simp: peterson_sr_def peterson_sr_cs1_def invs_def
                    req_peterson_inv_def key_peterson_inv_def
                    local_peterson_inv_def)[1]
  done

lemma env_stable_peterson_sr_cs1:
  "env_stable (peterson_rel (other_ident ident)) (peterson_rel (other_ident ident))
               peterson_sr peterson_sr_cs1 (\<lambda>s. invs s \<and> critical (ab_label s ident))"
  apply (simp add: env_stable_def rely_stable_def env_rely_stable_iosr_def
                 peterson_rel_def)
  apply (rule conjI)
   apply (auto simp: peterson_sr_def peterson_sr_cs1_def)[1]
  apply (rule conjI)
   apply clarsimp
   apply (clarsimp simp: peterson_sr_cs1_invs)
   apply (auto simp: peterson_sr_cs1_def peterson_sr_def)[1]
  apply (auto simp: peterson_sr_cs1_def peterson_sr_def)[1]
  done

lemmas prefix_refinement_interference_peterson_cs1 =
  prefix_refinement_interference[OF env_stable_peterson_sr_cs1]

lemmas prefix_refinement_bind_2left_2right
  = prefix_refinement_bind[where a="Trace_Monad.bind a a'" and c="Trace_Monad.bind c c'" for a a' c c', simplified bind_assoc]
lemmas rel_tr_refinement_bind_left_general_2left_2right
  = rel_tr_refinement_bind_left_general[where f="Trace_Monad.bind f f'" and g="Trace_Monad.bind g g'" for f f' g g',
                                        simplified bind_assoc]

lemma peterson_rel_imp_invs:
  "\<lbrakk>peterson_rel ident x y; invs x\<rbrakk> \<Longrightarrow> invs y"
  by (simp add: peterson_rel_def)

lemma peterson_rel_imp_label:
  "\<lbrakk>peterson_rel (other_ident ident) x y; invs x\<rbrakk>
   \<Longrightarrow> ab_label x ident = ab_label y ident"
  by (simp add: peterson_rel_def)

lemma peterson_rel_set_label:
  "\<lbrakk>peterson_rel (other_ident ident) (set_label ident label s) s'; invs (set_label ident label s)\<rbrakk>
   \<Longrightarrow> ab_label s' ident = label"
  by (simp add: peterson_rel_def set_label_def)

lemma acquire_lock_refinement:
  "prefix_refinement peterson_sr peterson_sr peterson_sr dc
     (peterson_rel (other_ident ident)) (peterson_rel (other_ident ident))
     \<top>\<top> \<top>\<top>
     (acquire_lock ident) (acquire_lock ident)"
  apply (unfold acquire_lock_def)
  apply (rule prefix_refinement_weaken_pre)
    apply (rule prefix_refinement_bind_sr)
       apply (rule prefix_refinement_interference_peterson)
      apply (simp add: modify_modify_bind)
      apply (rule prefix_refinement_bind_sr)
         apply (rule pfx_refn_modifyT)
         apply (clarsimp simp add: peterson_sr_def set_label_def set_ab_def forall_ident_eq)
        apply (rule prefix_refinement_bind_sr)
           apply (rule prefix_refinement_interference_peterson)
          apply (rule prefix_refinement_bind_sr)
             apply (rule prefix_refinement_Await[OF env_stable_peterson_sr abs_rely_stableT])
              apply (clarsimp simp add: peterson_sr_def locked_def)
             apply (clarsimp simp add: peterson_sr_def locked_def)
            apply (rule pfx_refn_modifyT)
            apply (clarsimp simp add: peterson_sr_def set_label_def)
           apply (wpsimp wp: Await_sync_twp)+
  done

lemma peterson_sr_invs[simp]:
  "\<lbrakk>peterson_sr as cs; invs as\<rbrakk> \<Longrightarrow> invs cs"
  by (simp add: peterson_sr_def invs_def invs_defs)

lemma peterson_sr_invs_sym:
  "\<lbrakk>peterson_sr as cs; invs cs\<rbrakk> \<Longrightarrow> invs as"
  by (simp add: peterson_sr_def invs_def invs_defs)

lemma peterson_sr_ab_label:
  "peterson_sr as cs \<Longrightarrow> ab_label as = ab_label cs"
  by (simp add: peterson_sr_def)

lemma critical_section_refinement:
  "prefix_refinement peterson_sr peterson_sr peterson_sr dc
     (peterson_rel (other_ident ident)) (peterson_rel (other_ident ident))
     (\<lambda>_ s. invs s \<and> ab_label s ident = Critical) \<top>\<top>
     abs_critical_section critical_section"
  apply (simp add: abs_critical_section_def critical_section_def)
  apply pfx_refn_pre
    apply (rule prefix_refinement_interferences_split)
    apply (rule prefix_refinement_bind_sr)
       apply (rule prefix_refinement_interference_peterson)

      (* reorder the interference and modify*)
      apply (rule pfx_refinement_use_rel_tr_refinement_equivp
                  [where Q="\<lambda>s. invs s \<and> ab_label s (ident) = Critical"])
        apply (rule rel_tr_refinement_bind_left_general_2left_2right)
          apply simp
         apply (rule disjI1,
                     clarsimp simp: not_env_steps_first_all
                                    cs_not_env_steps_first release_lock_def)
        apply (rule rshuttle_modify_interference)
          apply (simp add: peterson_sr_def peterson_rel_def)
         apply (clarsimp simp: peterson_rel_def)
        apply (clarsimp simp: p_state.splits)
        apply (clarsimp simp: peterson_rel_def invs_def invs_defs)
       apply simp

      apply (rule prefix_refinement_bind_sr)
         apply (rule prefix_refinement_interference_peterson)
        apply (rule prefix_refinement_bind[where intsr=peterson_sr_cs1])
           apply (rule prefix_refinement_modifyT)
           apply (clarsimp simp add: peterson_sr_def peterson_sr_cs1_def)
          apply (rule prefix_refinement_bind_sr)
             apply (rule cs_refine)
            apply (rule prefix_refinement_interference_peterson)

           apply (wpsimp wp: cs_closed)+
  apply (subst peterson_rel_imp_label[symmetric], assumption, simp)
  apply (drule peterson_rel_imp_invs, simp)
  apply (simp add: peterson_sr_ab_label)
  done

lemma release_lock_refinement:
  "prefix_refinement peterson_sr peterson_sr peterson_sr dc
     (peterson_rel (other_ident ident)) (peterson_rel (other_ident ident))
     \<top>\<top> \<top>\<top>
     (release_lock ident) (release_lock ident)"
  apply (unfold release_lock_def)
  apply (rule prefix_refinement_weaken_pre)
    apply (simp add: modify_modify_bind)
    apply (rule prefix_refinement_bind_sr)
       apply (rule pfx_refn_modifyT)
       apply (clarsimp simp add: peterson_sr_def peterson_sr_cs1_def set_label_def set_ab_def)
      apply (rule prefix_refinement_interference_peterson)
     apply wpsimp+
  done

lemma critical_section_prefix_closed[simp]:
  "prefix_closed critical_section"
  by (auto intro!: prefix_closed_bind
           simp: cs_closed critical_section_def)

lemma abs_critical_section_prefix_closed[simp]:
  "prefix_closed abs_critical_section"
  by (auto intro!: prefix_closed_bind
           simp: cs_closed abs_critical_section_def)

lemma peterson_rel_trans:
  "\<lbrakk>peterson_rel ident x y; peterson_rel ident y z\<rbrakk>
   \<Longrightarrow> peterson_rel ident x z"
  by (clarsimp simp: peterson_rel_def)

lemma invs_set_label_Critical:
  "\<lbrakk>invs s; locked ident s; ab_label s ident = Awaiting\<rbrakk>
   \<Longrightarrow> invs (set_label ident Critical s)"
  by (auto simp: invs_def invs_defs set_label_def locked_def)

lemma acquire_lock_wp:
  "\<lbrace>\<lambda>s0 s. invs s \<and> ab_label s ident = Exited\<rbrace>,
   \<lbrace>peterson_rel (other_ident ident)\<rbrace>
   acquire_lock ident
   \<lbrace>\<top>\<top>\<rbrace>,
   \<lbrace>\<lambda>rv s0 s. invs s \<and> ab_label s ident = Critical\<rbrace>"
  apply (simp add: acquire_lock_def)
  apply (wpsimp wp: Await_sync_twp)
  apply (subst (asm) peterson_rel_imp_label, assumption+)
  apply (drule(1) peterson_rel_imp_invs)
  apply (drule(1) peterson_rel_trans)
  apply (thin_tac "peterson_rel (other_ident ident) s'a x")
  apply (frule peterson_rel_set_label)
   apply (fastforce simp: set_label_def set_ab_def
                          locked_def invs_def invs_defs)
  apply (drule peterson_rel_imp_invs)
   apply (fastforce simp: set_label_def set_ab_def
                          locked_def invs_def invs_defs)
  apply (clarsimp simp: invs_set_label_Critical)
  apply (clarsimp simp: set_label_def set_ab_def)
  done

lemma acquire_lock_prefix_closed[simp]:
  "prefix_closed (acquire_lock ident)"
  by (auto intro!: prefix_closed_bind
           simp: cs_closed acquire_lock_def)

theorem peterson_proc_refinement:
  "prefix_refinement peterson_sr peterson_sr peterson_sr dc
     (peterson_rel (other_ident ident)) (peterson_rel (other_ident ident))
     (\<lambda>_ s. invs s \<and> ab_label s ident = Exited)
     (\<lambda>_ s. invs s \<and> ab_label s ident = Exited)
     (abs_peterson_proc ident)
     (peterson_proc ident)"
  apply (simp add: abs_peterson_proc_def peterson_proc_def)
  apply (rule prefix_refinement_weaken_pre)
    apply (rule prefix_refinement_bind_sr)
       apply (rule acquire_lock_refinement)
      apply (rule prefix_refinement_bind_sr)
         apply (rule critical_section_refinement)
        apply (rule release_lock_refinement)
       apply (wpsimp wp: acquire_lock_wp
                     simp: pred_conj_def)+
  done

definition peterson_rel2 :: "ident \<Rightarrow> ('a, 'b) p_state \<Rightarrow> ('a, 'b) p_state \<Rightarrow> bool" where
  "peterson_rel2 ident s_prior s =
     (\<comment> \<open>assume invs\<close> invs s_prior \<longrightarrow>
        \<comment> \<open>If you're in the critical section, I won't change cs1_v\<close>
        (critical (ab_label s_prior (other_ident ident)) \<longrightarrow> cs1_v s = cs1_v s_prior))"

definition peterson_rel3 :: "ident \<Rightarrow> ('a, 'b) p_state \<Rightarrow> ('a, 'b) p_state \<Rightarrow> bool" where
  "peterson_rel3 ident s_prior s =
     (\<comment> \<open>assume invs\<close> invs s_prior \<longrightarrow>
         \<comment> \<open>invariants are preserved\<close>
        (invs s
            \<comment> \<open>I won't adjust your variables\<close>
         \<and> (ab_v s (other_ident ident) = ab_v s_prior (other_ident ident))
         \<and> (ab_label s (other_ident ident) = ab_label s_prior (other_ident ident))
            \<comment> \<open>I will only ever give you priority\<close>
         \<and> (t_v s_prior = other_ident ident \<longrightarrow> t_v s = other_ident ident)
            \<comment> \<open>If you're in the critical section, I won't change cs2_v\<close>
         \<and> (critical (ab_label s_prior (other_ident ident))
              \<longrightarrow> cs2_v s = cs2_v s_prior)))"

lemma peterson_rel_helpers:
  "peterson_rel2 ident s0 s \<and> peterson_rel3 ident s0 s
   \<longrightarrow> peterson_rel ident s0 s"
  by (clarsimp simp: peterson_rel_def peterson_rel2_def peterson_rel3_def)

lemma peterson_rel_peterson_rel2:
  "peterson_rel ident s0 s \<Longrightarrow> peterson_rel2 ident s0 s"
  by (clarsimp simp: peterson_rel_def peterson_rel2_def)

lemma peterson_sr_peterson_rel3:
  "\<lbrakk>peterson_sr as0 cs0; peterson_sr as cs; peterson_rel ident as0 as\<rbrakk>
   \<Longrightarrow> peterson_rel3 ident cs0 cs"
  apply (clarsimp simp: peterson_rel_def peterson_rel3_def invs_def
                        invs_defs peterson_sr_ab_label)
  apply (clarsimp simp: peterson_sr_def)
  done

lemma peterson_proc_prefix_closed[simp]:
  "prefix_closed (peterson_proc ident)"
  by (auto intro!: prefix_closed_bind
           simp: cs_closed peterson_proc_def acquire_lock_def release_lock_def)

lemma peterson_proc_mutual_excl_helper:
  "\<lbrace>\<lambda>s0 s. peterson_rel ident s0 s \<and> invs s \<and> ab_label s ident = Exited\<rbrace>,
   \<lbrace>peterson_rel (other_ident ident)\<rbrace>
   peterson_proc ident
   \<lbrace>peterson_rel3 ident\<rbrace>,
   \<lbrace>\<lambda>rv s0 s. peterson_rel3 ident s0 s \<and> invs s \<and> ab_label s ident = Exited\<rbrace>"
  apply (rule prefix_refinement_validI)
        apply (rule peterson_proc_refinement)
       apply (rule abs_peterson_proc_mutual_excl)
      apply clarsimp
      apply (rule_tac x=t0 in exI)
      apply (rule_tac x="t \<lparr>cs1_v := cs1_v t0\<rparr>" in exI)
      apply (clarsimp simp: peterson_rel_def peterson_sr_def)
     apply (rule_tac x="t \<lparr>cs1_v := cs1_v s0\<rparr>" in exI)
     apply (clarsimp simp: peterson_rel_def peterson_sr_def invs_def invs_defs)
    apply (clarsimp simp: peterson_sr_peterson_rel3)
   apply (clarsimp simp: peterson_sr_peterson_rel3 peterson_sr_ab_label)
  apply clarsimp
  done

lemma peterson_proc_mutual_excl_helper':
  "\<lbrace>\<lambda>s0 s. peterson_rel ident s0 s \<and> invs s \<and> ab_label s ident = Exited\<rbrace>,
   \<lbrace>peterson_rel (other_ident ident)\<rbrace>
   peterson_proc ident
   \<lbrace>peterson_rel2 ident\<rbrace>,
   \<lbrace>\<lambda>rv s0 s. peterson_rel2 ident s0 s \<and> invs s \<and> ab_label s ident = Exited\<rbrace>"
  apply (simp add: peterson_proc_def acquire_lock_def release_lock_def
                   critical_section_def)
  apply (wp Await_sync_twp | simp add: split_def
         | rule rg_strengthen_guar[OF _ peterson_rel_peterson_rel2])+
  apply (clarsimp simp: imp_conjL)
  apply (strengthen peterson_rel_imp_assume_invs | simp)+
  apply (cases ident)
   apply (safe, simp_all)
  by (clarsimp simp: peterson_rel_def peterson_rel2_def forall_ident_eq
                     set_label_def set_ab_def locked_def invs_defs cs_closed
      | rule invs_def[THEN iffD2] conjI
      | rev_drule invs_def[THEN iffD1])+

lemma peterson_proc_mutual_excl:
  "\<lbrace>\<lambda>s0 s. peterson_rel ident s0 s \<and> invs s \<and> ab_label s ident = Exited\<rbrace>,
   \<lbrace>peterson_rel (other_ident ident)\<rbrace>
   peterson_proc ident
   \<lbrace>peterson_rel ident\<rbrace>,
   \<lbrace>\<lambda>rv s0 s. peterson_rel ident s0 s \<and> invs s \<and> ab_label s ident = Exited\<rbrace>"
  apply (rule rg_strengthen_guar, rule rg_strengthen_post, rule validI_guar_post_conj_lift)
     apply (rule peterson_proc_mutual_excl_helper)
    apply (rule peterson_proc_mutual_excl_helper')
   apply (clarsimp simp: peterson_rel_helpers)+
  done

definition
  "abs_peterson_proc_system \<equiv>
     parallel (do repeat (abs_peterson_proc A); interference od)
              (do repeat (abs_peterson_proc B); interference od)"

lemma validI_repeat_interference:
  "\<lbrakk>\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_. P\<rbrace>; \<forall>s0 s. P s0 s \<longrightarrow> (\<forall>s'. R\<^sup>*\<^sup>* s s' \<longrightarrow> Q () s' s') \<and> G s0 s\<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> do repeat f; interference od \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  apply (rule bind_twp)
   apply simp
   apply (rule interference_twp)
  apply (rule rg_strengthen_post)
   apply (rule repeat_validI, assumption)
  apply simp
  done

lemma abs_peterson_proc_system_mutual_excl:
  "\<lbrace>\<lambda>s0 s. s0 = s \<and> invs s \<and> ab_label s = (\<lambda>_. Exited)\<rbrace>,
   \<lbrace>\<lambda>s0 s. s0 = s\<rbrace>
   abs_peterson_proc_system
   \<lbrace>\<lambda>s0 s. invs s0 \<longrightarrow> invs s\<rbrace>,
   \<lbrace>\<lambda>rv s0 s. invs s\<rbrace>"
  apply (rule rg_weaken_pre, rule rg_strengthen_post)
    apply (unfold abs_peterson_proc_system_def)
    apply (rule rg_validI[where Qf="\<lambda>_ _. invs" and Qg="\<lambda>_ _. invs"])
           apply (rule validI_repeat_interference[OF abs_peterson_proc_mutual_excl])
           apply (clarsimp simp: peterson_rel_imp_invs)
          apply (rule validI_repeat_interference[OF abs_peterson_proc_mutual_excl])
          apply (clarsimp simp: peterson_rel_imp_invs)
         apply (simp add: reflp_ge_eq)+
       apply (clarsimp simp: peterson_rel_def)+
  done

definition
  "peterson_proc_system \<equiv>
     parallel (do repeat (peterson_proc A); interference od)
              (do repeat (peterson_proc B); interference od)"

lemma abs_peterson_proc_prefix_closed[simp]:
  "prefix_closed (abs_peterson_proc ident)"
  by (auto intro!: prefix_closed_bind
           simp: cs_closed abs_peterson_proc_def acquire_lock_def release_lock_def)

lemma peterson_repeat_refinement:
  "prefix_refinement peterson_sr peterson_sr peterson_sr dc
     (peterson_rel (other_ident ident)) (peterson_rel (other_ident ident))
     (\<lambda>s0 s. peterson_rel ident s0 s \<and> invs s \<and> ab_label s ident = Exited)
     (\<lambda>s0 s. peterson_rel ident s0 s \<and> invs s \<and> ab_label s ident = Exited)
     (do repeat (abs_peterson_proc ident);
         interference
      od)
     (do repeat (peterson_proc ident);
         interference
      od)"
  apply (rule prefix_refinement_weaken_pre)
    apply (rule prefix_refinement_bind_sr)
       apply (rule prefix_refinement_repeat[rotated])
         apply (rule abs_peterson_proc_mutual_excl[THEN rg_strengthen_guar])
         apply simp
        apply (rule peterson_proc_mutual_excl[THEN rg_strengthen_guar, THEN rg_weaken_pre])
         apply simp+
       apply (rule peterson_proc_refinement[THEN prefix_refinement_weaken_pre])
        apply simp+
      apply (rule prefix_refinement_interference_peterson)
     apply wpsimp+
  done

theorem peterson_proc_system_refinement:
  "prefix_refinement peterson_sr peterson_sr peterson_sr dc
     (\<lambda>s0 s. s0 = s) (\<lambda>t0 t. t0 = t)
     (\<lambda>s0 s. s0 = s \<and> invs s \<and> ab_label s = (\<lambda>_. Exited))
     (\<lambda>t0 t. t0 = t \<and> invs t \<and> ab_label t = (\<lambda>_. Exited))
     abs_peterson_proc_system peterson_proc_system"
  apply (unfold abs_peterson_proc_system_def peterson_proc_system_def)
  apply (rule prefix_refinement_parallel')
         apply (rule prefix_refinement_weaken_rely, rule prefix_refinement_weaken_pre)
             apply (rule peterson_repeat_refinement)
            apply simp
           apply simp
          apply (rule eq_refl, rule bipred_disj_op_eq, simp)
         apply (rule eq_refl, rule bipred_disj_op_eq, simp)
        apply (rule prefix_refinement_weaken_rely, rule prefix_refinement_weaken_pre)
            apply (rule peterson_repeat_refinement)
           apply simp
          apply simp
         apply (rule eq_refl, rule bipred_disj_op_eq, simp)
        apply (rule eq_refl, rule bipred_disj_op_eq, simp)
       apply (clarsimp intro!: par_tr_fin_bind par_tr_fin_interference)
      apply (clarsimp intro!: par_tr_fin_bind par_tr_fin_interference)
     apply (rule rg_weaken_pre, rule rg_weaken_rely)
       apply (rule validI_repeat_interference; simp)
        apply (rule peterson_proc_mutual_excl)
       apply (simp+)[3]
    apply (rule rg_weaken_pre, rule rg_weaken_rely)
      apply (rule validI_repeat_interference; simp)
       apply (rule peterson_proc_mutual_excl)
      apply (simp+)[3]
   apply (rule rg_weaken_pre, rule rg_weaken_rely)
     apply (rule validI_repeat_interference; simp)
      apply (rule abs_peterson_proc_mutual_excl)
     apply (simp+)[3]
  apply (rule rg_weaken_pre, rule rg_weaken_rely)
    apply (rule validI_repeat_interference; simp)
     apply (rule abs_peterson_proc_mutual_excl)
    apply (simp+)[3]
  done

lemma peterson_proc_system_prefix_closed[simp]:
  "prefix_closed (peterson_proc_system)"
  by (auto intro!: prefix_closed_bind prefix_closed_parallel
             simp: cs_closed peterson_proc_system_def)

theorem peterson_proc_system_mutual_excl:
  "\<lbrace>\<lambda>s0 s. s0 = s \<and> invs s \<and> ab_label s = (\<lambda>_. Exited)\<rbrace>,
   \<lbrace>\<lambda>s0 s. s0 = s\<rbrace>
   peterson_proc_system
   \<lbrace>\<lambda>s0 s. invs s0 \<longrightarrow> invs s\<rbrace>,
   \<lbrace>\<lambda>rv s0 s. invs s\<rbrace>"
  apply (rule prefix_refinement_validI)
        apply (rule peterson_proc_system_refinement)
       apply (rule abs_peterson_proc_system_mutual_excl)
      apply (fastforce simp: peterson_rel_def peterson_sr_def)
     apply clarsimp
    apply (clarsimp simp: peterson_sr_invs_sym )
   apply clarsimp
  apply (fastforce simp: peterson_sr_def)
  done

end
end
