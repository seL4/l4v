(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Detype_AI
imports ArchRetype_AI
begin

context begin interpretation Arch .

requalify_facts
  valid_arch_mdb_detype
  clearMemory_invs
  invs_irq_state_independent
  init_arch_objects_invs_from_restricted
  caps_region_kernel_window_imp
  init_arch_objects_wps

end

declare clearMemory_invs[wp]

declare invs_irq_state_independent[intro!, simp]

locale Detype_AI =
  fixes state_ext_type :: "'a :: state_ext itself"
  assumes valid_globals_irq_node:
    "\<And>s cap ptr irq. \<lbrakk> valid_global_refs (s :: 'a state); cte_wp_at ((=) cap) ptr s \<rbrakk>
          \<Longrightarrow> interrupt_irq_node s irq \<notin> cap_range cap"
  assumes caps_of_state_ko:
    "\<And>cap s. valid_cap cap (s :: 'a state)
     \<Longrightarrow> is_untyped_cap cap \<or>
         cap_range cap = {} \<or>
         (\<forall>ptr \<in> cap_range cap. \<exists>ko. kheap s ptr = Some ko)"
  assumes mapM_x_storeWord:
   "\<And>ptr. is_aligned ptr word_size_bits
     \<Longrightarrow> mapM_x (\<lambda>x. storeWord (ptr + of_nat x * word_size) 0) [0..<n]
         = do ta \<leftarrow> gets touched_addresses;
       assert ({ptr + of_nat x * word_size| x. x<n} \<subseteq> ta);
       modify (underlying_memory_update
             (\<lambda>m x. if \<exists>k. x = ptr + of_nat k \<and> k < n * word_size then 0 else m x))
    od"
  assumes empty_fail_freeMemory:
    "empty_fail (freeMemory ptr bits)"
  assumes valid_ioports_detype:
    "valid_ioports (s::'a state) \<Longrightarrow> valid_ioports (detype (untyped_range cap) s)"

lemma obj_at_detype[simp]:
  "obj_at P p (detype S s) = (p \<notin> S \<and> obj_at P p s)"
  by (clarsimp simp: obj_at_def detype_def)

lemma pspace_detype[simp]:
  "(kheap (detype S s) ptr = Some x)
    = (kheap s ptr = Some x \<and> ptr \<notin> S)"
  by (simp add: detype_def)


lemma cte_wp_at_detype[simp]:
  "(cte_wp_at P p (detype S s))
    = (cte_wp_at P p s \<and> fst p \<notin> S)"
  apply (case_tac "fst p \<in> S")
   apply (simp add: cte_wp_at_cases)+
  done


lemma pred_tcb_at_detype[simp]:
  "(pred_tcb_at proj P t (detype S s))
    = (pred_tcb_at proj P t s \<and> t \<notin> S)"
  by (fastforce simp add: pred_tcb_at_def)


lemma cdt_detype[simp]:
  "cdt (detype S s) = cdt s"
  by (simp add: detype_def)


lemma caps_of_state_detype[simp]:
  "caps_of_state (detype S s) =
   (\<lambda>p. if fst p \<in> S then None else caps_of_state s p)"
  by (fastforce simp add: caps_of_state_cte_wp_at)


lemma state_refs_of_detype:
  "state_refs_of (detype S s) = (\<lambda>x. if x \<in> S then {} else state_refs_of s x)"
  by (rule ext, simp add: state_refs_of_def detype_def)


definition
  obj_reply_refs :: "cap \<Rightarrow> machine_word set"
where
 "obj_reply_refs cap \<equiv> obj_refs cap \<union>
   (case cap of cap.ReplyCap t m R \<Rightarrow> {t} | _ \<Rightarrow> {})"


lemma ex_cte_cap_to_obj_ref_disj:
  "ex_cte_cap_wp_to P ptr s
      \<Longrightarrow> ((\<exists>ptr'. cte_wp_at (\<lambda>cap. fst ptr \<in> obj_refs cap) ptr' s)
               \<or> (\<exists>ptr' irq. cte_wp_at ((=) (cap.IRQHandlerCap irq)) ptr' s
                               \<and> ptr = (interrupt_irq_node s irq, [])))"
  apply (clarsimp simp: ex_cte_cap_wp_to_def cte_wp_at_caps_of_state)
  apply (frule cte_refs_obj_refs_elem, erule disjE)
   apply fastforce
  apply clarsimp
  done


definition
  "descendants_range_in S p \<equiv>
  \<lambda>s. \<forall>p' \<in> descendants_of p (cdt s). cte_wp_at (\<lambda>c. cap_range c \<inter> S = {}) p' s"

lemma descendants_range_in_lift:
  assumes st: "\<And>P. \<lbrace>\<lambda>s. P (cdt s)\<rbrace> f \<lbrace>\<lambda>r s. P (cdt s)\<rbrace>"
  assumes untyped_range: "\<And>P p. \<lbrace>\<lambda>s. Q s \<and> cte_wp_at (\<lambda>c. P (cap_range c)) p s\<rbrace> f \<lbrace>\<lambda>r s. cte_wp_at (\<lambda>c. P (cap_range c)) p s\<rbrace>"
  shows "\<lbrace>Q and descendants_range_in S slot\<rbrace> f \<lbrace>\<lambda>r. descendants_range_in S slot\<rbrace>"
   apply (clarsimp simp:descendants_range_in_def)
   apply (rule hoare_pre)
   apply (wps st)
   apply (rule hoare_vcg_ball_lift)
   apply (wp untyped_range)
   apply clarsimp
 done


lemma set_cap_descendants_range_in:
  shows "\<lbrace>cte_wp_at (\<lambda>c. cap_range c = cap_range cap) slot and descendants_range_in S slot\<rbrace>
  set_cap cap slot \<lbrace>\<lambda>r. descendants_range_in S slot\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp:cte_wp_at_caps_of_state)
  apply (rule hoare_pre)
   apply (wp descendants_range_in_lift
     [where Q = "cte_wp_at (\<lambda>c. cap_range c = cap_range cap) slot"] )
   apply (wp set_cap_cte_wp_at)
   apply (clarsimp simp:cte_wp_at_caps_of_state)+
  done


lemma empty_descendants_range_in:
  "descendants_of p (cdt s) = {} \<Longrightarrow> descendants_range_in S p s"
  by (clarsimp simp:descendants_range_in_def)


lemma valid_mdb_descendants_range_in:
  "valid_mdb s \<Longrightarrow> descendants_range_in S p s = (\<forall>p'\<in>descendants_of p (cdt s).
  \<exists>c. (null_filter (caps_of_state s)) p' = Some c \<and> cap_range c \<inter> S = {})"
  apply (clarsimp simp:descendants_range_in_def
                  split:if_splits)
  apply (intro ext iffI ballI impI)
   apply (frule(1) bspec)
   apply (frule(1) descendants_of_cte_at)
   apply (clarsimp simp:cte_wp_at_caps_of_state null_filter_def descendants_of_def)
   apply (clarsimp simp:valid_mdb_no_null)
  apply (drule(1) bspec)
  apply (clarsimp simp:cte_wp_at_caps_of_state null_filter_def cap_range_def split:if_split_asm)
  done


definition
  "descendants_range cap p \<equiv>
  \<lambda>s. \<forall>p' \<in> descendants_of p (cdt s). cte_wp_at (\<lambda>c. cap_range c \<inter> cap_range cap = {}) p' s"

lemma descendants_rangeD:
  "\<lbrakk> descendants_range cap p s; cdt s \<Turnstile> p \<rightarrow> p' \<rbrakk> \<Longrightarrow>
  \<exists>c. caps_of_state s p' = Some c \<and> cap_range c \<inter> cap_range cap = {}"
  by (simp add: descendants_range_def descendants_of_def cte_wp_at_caps_of_state
           del: split_paired_All)


lemma subset_splitE:
  "\<lbrakk>A \<subseteq> B \<or> B \<subseteq> A \<or> A \<inter> B = {} ; A \<subset> B \<Longrightarrow>P;B \<subset> A \<Longrightarrow>P ;A = B \<Longrightarrow> P; A \<inter> B = {} \<Longrightarrow> P\<rbrakk> \<Longrightarrow>P"
  apply (simp add:subset_iff_psubset_eq)
  apply (elim disjE)
    apply auto
  done


lemma cap_range_untyped_range_eq[simp]:
  "is_untyped_cap a \<Longrightarrow> cap_range a = untyped_range a"
  by (clarsimp simp:is_cap_simps cap_range_def)


lemma (in Detype_AI) untyped_cap_descendants_range:
  "\<lbrakk>valid_pspace (s :: 'a state); caps_of_state s p = Some cap; is_untyped_cap cap;valid_mdb s;
   q\<in> descendants_of p (cdt s) \<rbrakk>
   \<Longrightarrow>  cte_wp_at (\<lambda>c. (cap_range c \<inter> usable_untyped_range cap = {})) q s"
   apply (clarsimp simp: valid_pspace_def)
   apply (frule(1) descendants_of_cte_at)
   apply (clarsimp simp:cte_wp_at_caps_of_state)
   apply (case_tac "is_untyped_cap capa")
     apply (frule(1) valid_cap_aligned[OF caps_of_state_valid])
     apply (frule_tac cap = capa in valid_cap_aligned[OF caps_of_state_valid])
      apply simp
     apply (frule_tac c = capa in untyped_range_non_empty)
      apply simp
     apply (frule_tac c = cap in untyped_range_non_empty)
      apply simp
     apply (clarsimp simp:valid_mdb_def)
     apply (drule untyped_incD)
       apply simp+
     apply clarify
     apply (erule subset_splitE)
       apply simp
       apply (thin_tac "P\<longrightarrow>Q" for P Q)+
       apply (clarsimp simp:descendants_of_def)
       apply (drule(1) trancl_trans)
       apply (simp add:vmdb_abs_def valid_mdb_def vmdb_abs.no_loops)
      apply simp
     apply simp
     apply (clarsimp simp:descendants_of_def | erule disjE)+
     apply (drule(1) trancl_trans)
     apply (simp add:vmdb_abs_def valid_mdb_def vmdb_abs.no_loops)+
   apply (thin_tac "P\<longrightarrow>Q" for P Q)+
   apply (erule(1) disjoint_subset2[OF usable_range_subseteq])
   apply (simp add:Int_ac)
  apply (drule(1) caps_of_state_valid)+
  apply (frule_tac cap = capa in caps_of_state_ko)
  apply (elim disjE)
   apply clarsimp+
  apply (clarsimp simp:valid_cap_def is_cap_simps valid_untyped_def
             simp del:usable_untyped_range.simps untyped_range.simps)
  apply (rule ccontr)
  apply (clarsimp dest!: int_not_emptyD simp del:usable_untyped_range.simps untyped_range.simps)
  apply (thin_tac "\<forall>x y z. P x y z" for P)
  apply (drule(1) bspec)
  apply (clarsimp dest!: int_not_emptyD simp del:usable_untyped_range.simps untyped_range.simps)
  apply (drule_tac x = x in spec)
  apply (clarsimp simp del:usable_untyped_range.simps untyped_range.simps)
  apply (drule(2) p_in_obj_range )
  apply (erule impE)
   apply (erule(1) notemptyI[OF IntI[OF _ subsetD[OF usable_range_subseteq]]])
    apply (simp add:is_cap_simps)
   apply assumption
  apply blast
  done


lemma untyped_children_in_mdbEE:
  assumes ass: "untyped_children_in_mdb s" "cte_wp_at ((=) cap) ptr s" "is_untyped_cap cap" "cte_wp_at P ptr' s"
  and  step1: "\<And>cap'. \<lbrakk>cte_wp_at ((=) cap') ptr' s; P cap'\<rbrakk> \<Longrightarrow> obj_refs cap' \<inter> untyped_range cap \<noteq> {}"
  and  step2: "\<And>cap'. \<lbrakk>cte_wp_at ((=) cap') ptr' s; cap_range cap' \<inter> untyped_range cap \<noteq> {};ptr' \<in> descendants_of ptr (cdt s) \<rbrakk> \<Longrightarrow> Q"
  shows "Q"
  using ass
  apply (clarsimp simp:cte_wp_at_caps_of_state)
  apply (rule step2)
     apply (simp add:cte_wp_at_caps_of_state)
    apply (drule step1[rotated])
     apply (simp add:cte_wp_at_caps_of_state)
    apply (simp add:cap_range_def)
    apply blast
  apply (simp add:untyped_children_in_mdb_def del:split_paired_All)
  apply (drule_tac x = ptr in spec)
  apply (drule_tac x = ptr' in spec)
  apply (erule impE)
  apply (clarsimp simp:cte_wp_at_caps_of_state)
  apply (drule step1[rotated])
   apply (clarsimp simp:cte_wp_at_caps_of_state)+
  done

definition
  "clear_um S \<equiv> (machine_state_update \<circ> underlying_memory_update)
                (\<lambda>m p. if p\<in>S then 0 else m p)"

interpretation clear_um:
  p_arch_idle_update_int_eq "clear_um S"
  by unfold_locales (simp_all add: clear_um_def)

lemma descendants_range_inD:
  "\<lbrakk>descendants_range_in S p s;p'\<in>descendants_of p (cdt s);caps_of_state s p' = Some cap\<rbrakk>
 \<Longrightarrow> cap_range cap \<inter> S = {}"
  by (auto simp:descendants_range_in_def cte_wp_at_caps_of_state dest!:bspec)

lemma descendants_range_def2:
  "descendants_range cap p = descendants_range_in (cap_range cap) p"
  by (simp add:descendants_range_in_def descendants_range_def)


lemma detype_clear_um_independent:
  "detype S (clear_um T s) = clear_um T (detype S s)"
  by (auto simp add: detype_def clear_um_def ext)


(* FIXME: move *)
lemma (in pspace_update_eq) zombies_final_eq[iff]:
  "zombies_final (f s) = zombies_final s"
  by (simp add: zombies_final_def is_final_cap'_def)


lemma valid_mdb_clear_um [iff]:
  "valid_mdb (clear_um S s) = valid_mdb s"
  by (simp add: clear_um_def)


lemma valid_ioc_clear_um[iff]:
  "valid_ioc (clear_um S s) = valid_ioc s"
  by (simp add: clear_um_def)


lemma cur_tcb_clear_um[iff]: "cur_tcb (clear_um S s) = cur_tcb s"
  by (simp add: clear_um_def cur_tcb_def)


lemma untyped_children_in_mdb_clear_um[iff]:
  "untyped_children_in_mdb (clear_um S s) = untyped_children_in_mdb s"
  by (simp add: untyped_children_in_mdb_def clear_um_def)



lemma descendants_inc_empty_slot:
  assumes desc_inc :"descendants_inc m cs'"
  assumes mdb:"mdb_cte_at (\<lambda>p. \<exists>c. cs p = Some c \<and> cap.NullCap \<noteq> c) m"
  assumes dom:"\<forall>x\<in> dom cs.  (cs' x = cs x)"
  shows "descendants_inc m cs"
  using desc_inc
  apply (simp add:descendants_inc_def del:split_paired_All)
  apply (intro allI impI)
  apply (drule spec)+
  apply (erule(1) impE)
  apply (simp add:descendants_of_def)
  apply (frule tranclD)
  apply (drule tranclD2)
  apply (simp add:cdt_parent_rel_def is_cdt_parent_def)
  apply (elim exE conjE)
  apply (drule mdb_cte_atD[OF _ mdb])+
  apply (elim exE conjE)
  apply (drule bspec[OF dom,OF domI])+
  apply simp
  done


lemma descendants_range_imply_no_descendants:
  "\<lbrakk>descendants_range cap p s;descendants_inc (cdt s) (caps_of_state s);
  is_untyped_cap cap; caps_of_state s p = Some cap;valid_objs s;valid_mdb s\<rbrakk>
  \<Longrightarrow> descendants_of p (cdt s)= {}"
  apply (simp add:descendants_range_def is_cap_simps descendants_inc_def del:split_paired_All)
  apply (elim exE)
  apply (rule equals0I)
  apply (drule(1) bspec)
  apply (drule spec)+
  apply (erule(1) impE)
  apply (drule(1) descendants_of_cte_at)
  apply (clarsimp simp:cte_wp_at_caps_of_state simp del:split_paired_All)
  apply (drule(1) physical_valid_cap_not_empty_range[OF caps_of_state_valid_cap,rotated])
   apply simp
  apply auto
  done

locale detype_locale =
  fixes cap and ptr and s
  assumes cap: "cte_wp_at ((=) cap) ptr s"
  and untyped: "is_untyped_cap cap"
  and  nodesc: "descendants_range cap ptr s"
  and    invs: "invs s"
  and   child: "untyped_children_in_mdb s"

context detype_locale begin

lemma drange:"descendants_range_in (cap_range cap) ptr (s :: 'a state)"
   using nodesc
   by (simp add:descendants_range_def2)

lemma iflive: "if_live_then_nonz_cap s"
    using invs by (simp add: invs_def valid_state_def valid_pspace_def)

lemma live_okE:
    "\<And>P p. \<lbrakk> obj_at P p s; \<And>obj. P obj \<Longrightarrow> live obj \<rbrakk>
    \<Longrightarrow> p \<notin> untyped_range cap"
    apply (drule if_live_then_nonz_capD [OF iflive])
     apply simp
    apply (rule notI)
    apply (erule ex_nonz_cap_toE)
    apply (erule untyped_children_in_mdbEE [OF child cap untyped])
     apply (clarsimp simp: zobj_refs_to_obj_refs)
     apply blast
    apply (drule descendants_range_inD[OF drange])
     apply (simp add:cte_wp_at_caps_of_state)
    apply (simp add:untyped)
    done

lemma ifunsafe: "if_unsafe_then_cap s"
  using invs by (simp add: invs_def valid_state_def valid_pspace_def)

lemma globals: "valid_global_refs s"
  using invs by (simp add: invs_def valid_state_def)


(* this is should be true *)
lemma state_refs: "state_refs_of (detype (untyped_range cap) s) = state_refs_of s"
  apply (rule ext, clarsimp simp add: state_refs_of_detype)
  apply (rule sym, rule equals0I, drule state_refs_of_elemD)
  apply (drule live_okE, rule refs_of_live, clarsimp)
  apply simp
  done

lemma idle: "idle_thread (detype (untyped_range cap) s) = idle_thread s"
  by (simp add: detype_def)

lemma valid_arch_caps: "valid_arch_caps s"
  using invs by (simp add: invs_def valid_state_def)

  (* moreover *)
lemma valid_arch_state: "valid_arch_state s" using invs
  by clarsimp
  (* moreover *)
lemma ut_mdb: "untyped_mdb (cdt s) (caps_of_state s)"
  using invs
  by (clarsimp dest!: invs_mdb simp add: valid_mdb_def)

lemma arch_state_det: "\<And>r. arch_state (detype r s) = arch_state s" (* SIMP DUP*)
  by (simp add: detype_def)

lemma no_obj_refs:
  "\<And>slot cap' x. \<lbrakk> caps_of_state s slot = Some cap';
                   x \<in> obj_refs cap'; x \<in> untyped_range cap \<rbrakk> \<Longrightarrow> False"
  using cap untyped
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (drule (2) untyped_mdbD)
    apply blast
   apply (rule ut_mdb)
  apply (drule descendants_range_inD[OF drange])
    apply (simp add:cte_wp_at_caps_of_state)
  apply (simp add:cap_range_def)
  apply blast
  done

lemma valid_pspace: "valid_pspace s" using invs
  by (simp add: invs_def valid_state_def)

lemma valid_global_objs: "valid_global_objs s"
  using invs by (clarsimp simp: invs_def valid_state_def)

lemma cap_is_valid: "valid_cap cap s"
  by (rule cte_wp_valid_cap[OF cap invs_valid_objs[OF invs]])

end


locale Detype_AI_2 =
  fixes cap ptr s
  assumes detype_invariants:
    "\<lbrakk> cte_wp_at ((=) cap) ptr s
     ; is_untyped_cap cap
     ; descendants_range cap ptr s
     ; invs s
     ; untyped_children_in_mdb s
     ; ct_active s
      \<rbrakk>
     \<Longrightarrow> (invs and untyped_children_in_mdb)
               (detype (untyped_range cap) (clear_um (untyped_range cap) s))"

locale detype_locale_gen_1 = Detype_AI "TYPE('a)" + detype_locale cap ptr s
  for cap ptr
  and s :: "('a :: state_ext) state" +
  assumes valid_cap:
    "\<And>cap'. \<lbrakk> s \<turnstile> cap'; obj_reply_refs cap' \<subseteq> (UNIV - untyped_range cap) \<rbrakk>
      \<Longrightarrow> detype (untyped_range cap) s \<turnstile> cap'"
  assumes glob_det: "\<And>r. global_refs (detype r s) = global_refs s"
  assumes arch_valid_obj:
    "\<And>p ao. \<lbrakk>ko_at (ArchObj ao) p s; arch_valid_obj ao s\<rbrakk>
       \<Longrightarrow> arch_valid_obj ao (detype (untyped_range cap) s)"
  assumes sym_hyp_refs_detype:
    "sym_refs (state_hyp_refs_of (detype (untyped_range cap) s))"
  assumes tcb_arch_detype:
    "\<And>p t. \<lbrakk>ko_at (TCB t) p s; valid_arch_tcb (tcb_arch t) s\<rbrakk>
       \<Longrightarrow> valid_arch_tcb (tcb_arch t) (detype (untyped_range cap) s)"

locale detype_locale_gen_2 = detype_locale_gen_1 cap ptr s
  for cap ptr
  and s :: "('a :: state_ext) state" +
  assumes detype_invs_assms:
    "valid_idle (detype (untyped_range cap) s)"
    "valid_arch_state (detype (untyped_range cap) s)"
    "valid_vspace_objs (detype (untyped_range cap) s)"
    "valid_arch_caps (detype (untyped_range cap) s)"
    "valid_kernel_mappings (detype (untyped_range cap) s)"
    "valid_global_objs (detype (untyped_range cap) s)"
    "valid_asid_map (detype (untyped_range cap) s)"
    "valid_global_vspace_mappings (detype (untyped_range cap) s)"
    "equal_kernel_mappings (detype (untyped_range cap) s)"
    "pspace_in_kernel_window (detype (untyped_range cap) s)"
    "valid_machine_state (clear_um (untyped_range cap) (detype (untyped_range cap) s))"
    "pspace_respects_device_region (clear_um (untyped_range cap) (detype (untyped_range cap) s))"
    "cap_refs_respects_device_region (clear_um (untyped_range cap) (detype (untyped_range cap) s))"

locale detype_locale_arch = detype_locale + Arch

context detype_locale_gen_1
begin

lemma irq_node:
  "interrupt_irq_node (s :: 'a state) irq \<notin> untyped_range cap"
  using valid_globals_irq_node [OF globals cap]
  by (simp add: cap_range_def)

lemma non_null_present:
    "\<And>p. cte_wp_at ((\<noteq>) cap.NullCap) p s \<Longrightarrow> fst p \<notin> untyped_range cap"
    apply (drule if_unsafe_then_capD[OF _ ifunsafe], simp)
    apply (drule ex_cte_cap_to_obj_ref_disj, erule disjE)
     apply clarsimp
     apply (erule untyped_children_in_mdbEE[OF child cap untyped])
      apply blast
     apply (drule descendants_range_inD[OF drange])
      apply (simp add:cte_wp_at_caps_of_state)
     apply (simp add:untyped)
    apply (clarsimp simp: irq_node)
    done

lemma non_filter_detype:
  "null_filter (caps_of_state s) = null_filter (caps_of_state (detype (untyped_range cap) s))"
  apply (intro iffI ext)
  apply (clarsimp simp: null_filter_def split:if_splits)+
  apply (rule ccontr)
  apply (clarsimp dest!:caps_of_state_cteD)
  apply (frule non_null_present[OF cte_wp_at_weakenE])
    apply (clarsimp simp:cte_wp_at_caps_of_state)
  apply simp
  done

lemma non_null_caps:
    "\<And>p c. \<lbrakk> caps_of_state s p = Some c; c \<noteq> cap.NullCap \<rbrakk>
     \<Longrightarrow> fst p \<notin> untyped_range cap"
    by (clarsimp simp: cte_wp_at_caps_of_state non_null_present)

lemma vreply: "valid_reply_caps s"
  using invs by (simp add: invs_def valid_state_def)

lemma vmaster: "valid_reply_masters s"
  using invs by (simp add: invs_def valid_state_def)

lemma valid_cap2:
    "\<And>cap'. \<lbrakk> \<exists>p. cte_wp_at ((=) cap') p s \<rbrakk>
    \<Longrightarrow> obj_reply_refs cap' \<subseteq> (UNIV - untyped_range cap)"
  apply clarsimp
  apply (simp add: obj_reply_refs_def, erule disjE)
   apply (erule untyped_children_in_mdbEE [OF child cap untyped])
    apply blast
   apply (drule descendants_range_inD[OF drange])
    apply (simp add:cte_wp_at_caps_of_state)
   apply (simp add:untyped)
  apply (clarsimp split: cap.split_asm bool.split_asm)
  apply (rename_tac t master rights)
  apply (case_tac master, simp_all)
   apply (frule valid_reply_mastersD' [OF _ vmaster])
   apply (fastforce simp: cte_wp_at_caps_of_state dest: non_null_caps)
  apply (subgoal_tac "has_reply_cap t s")
   apply (drule valid_reply_capsD [OF _ vreply])
   apply (simp add: pred_tcb_at_def)
   apply (fastforce simp: live_def dest: live_okE)
  apply (fastforce simp: has_reply_cap_def is_reply_cap_to_def elim:cte_wp_at_lift)
  done

(* invariants BEGIN *)

named_theorems detype_invs_lemmas

lemma refsym : "sym_refs (state_refs_of s)"
  using invs by (simp add: invs_def valid_state_def valid_pspace_def)

lemma hyprefsym : "sym_refs (state_hyp_refs_of s)"
  using invs by (simp add: invs_def valid_state_def valid_pspace_def)

lemma refs_of: "\<And>obj p. \<lbrakk> ko_at obj p s \<rbrakk> \<Longrightarrow> refs_of obj \<subseteq> (UNIV - untyped_range cap \<times> UNIV)"
 by (fastforce intro: refs_of_live dest!: sym_refs_ko_atD[OF _ refsym] live_okE)

lemma refs_of2: "\<And>obj p. kheap s p = Some obj
                     \<Longrightarrow> refs_of obj \<subseteq> (UNIV - untyped_range cap \<times> UNIV)"
  by (simp add: refs_of obj_at_def)

lemma valid_obj: "\<And>p obj. \<lbrakk> valid_obj p obj s; ko_at obj p s \<rbrakk>
                             \<Longrightarrow> valid_obj p obj (detype (untyped_range cap) s)"
    apply (clarsimp simp: valid_obj_def
                   split: Structures_A.kernel_object.split_asm)
        apply (clarsimp simp: valid_cs_def)
        apply (drule well_formed_cnode_valid_cs_size)
        apply (rule valid_cap)
         apply fastforce
        apply (rule valid_cap2)
        apply (erule ranE)
        apply (fastforce simp: obj_at_def intro!: cte_wp_at_cteI)
       apply (frule refs_of)
       apply (clarsimp simp: valid_tcb_def obj_at_def tcb_arch_detype)
       apply (rule conjI)
        apply (erule ballEI)
        apply (clarsimp elim!: ranE)
        apply (erule valid_cap [OF _ valid_cap2])
        apply (fastforce intro!: cte_wp_at_tcbI)
       apply (clarsimp simp: valid_tcb_state_def valid_bound_ntfn_def
                      split: Structures_A.thread_state.split_asm option.splits)
      apply (frule refs_of)
      apply (rename_tac endpoint)
      apply (case_tac endpoint, (fastforce simp: valid_ep_def)+)
     apply (frule refs_of)
     apply (rename_tac notification ntfn_ext)
     apply (case_tac "ntfn_obj ntfn_ext")
       apply (auto simp: valid_ntfn_def ntfn_bound_refs_def split: option.splits)
    apply (auto intro: arch_valid_obj)
  done

lemma valid_objs_detype[detype_invs_lemmas] : "valid_objs (detype (untyped_range cap) s)"
  using invs_valid_objs[OF invs]
  apply (clarsimp simp add: valid_objs_def dom_def)
  apply (erule allE, erule impE, erule exI)
  apply (clarsimp elim!: valid_obj)
  apply (simp add: obj_at_def)
  done

lemma pspace_aligned_detype[detype_invs_lemmas] :  "pspace_aligned (detype (untyped_range cap) s)"
  using invs_psp_aligned[OF invs]
  apply (clarsimp simp: pspace_aligned_def)
  apply (drule bspec, erule domI)
  apply (clarsimp simp: detype_def)
  done

lemma sym_refs_detype[detype_invs_lemmas] :
  "sym_refs (state_refs_of (detype (untyped_range cap) s))"
  using refsym by (simp add: state_refs)

lemmas [detype_invs_lemmas] = sym_hyp_refs_detype

lemma pspace_distinct_detype[detype_invs_lemmas]: "pspace_distinct (detype (untyped_range cap) s)"
  apply (insert invs, drule invs_distinct)
  apply (auto simp: pspace_distinct_def)
  done

lemma cut_tcb_detype[detype_invs_lemmas]:
  assumes ct_act: "ct_active s"
  shows "cur_tcb (detype (untyped_range cap) s)" (* CT_ACT *)
    apply (insert ct_act invs)
    apply (drule tcb_at_invs)
    apply (simp add: cur_tcb_def ct_in_state_def)
    apply (clarsimp simp: detype_def pred_tcb_at_def)
    apply (fastforce simp: live_def dest: live_okE)
    done

lemma live_okE2: "\<And>obj p. \<lbrakk> kheap s p = Some obj; live obj \<rbrakk>
                      \<Longrightarrow> p \<notin> untyped_range cap"
  by (simp add: live_okE[where P=live] obj_at_def)

lemma untyped_mdb : "\<And>m. untyped_mdb m (caps_of_state s)
                    \<Longrightarrow> untyped_mdb m (\<lambda>p. if fst p \<in> untyped_range cap then None else caps_of_state s p)"
  apply (simp only: untyped_mdb_def)
  apply (elim allEI)
  apply clarsimp
  done

lemma untyped_inc : "\<And>m. untyped_inc m (caps_of_state s)
                    \<Longrightarrow> untyped_inc m (\<lambda>p. if fst p \<in> untyped_range cap then None else caps_of_state s p)"
  apply (simp only: untyped_inc_def)
  apply (elim allEI)
  apply clarsimp
  done

lemma reply_caps_mdb : "\<And>m. reply_caps_mdb m (caps_of_state s)
                       \<Longrightarrow> reply_caps_mdb m (\<lambda>p. if fst p \<in> untyped_range cap then None else caps_of_state s p)"
  apply (simp only: reply_caps_mdb_def)
  apply (elim allEI)
  apply (clarsimp elim!: exEI)
  apply (fastforce dest: non_null_caps)
  done

lemma reply_masters_mdb : "\<And>m. reply_masters_mdb m (caps_of_state s)
                          \<Longrightarrow> reply_masters_mdb m (\<lambda>p. if fst p \<in> untyped_range cap then None else caps_of_state s p)"
  apply (simp only: reply_masters_mdb_def)
  apply (elim allEI)
  apply clarsimp
  apply (drule(1) bspec)
  apply (fastforce dest: non_null_caps)
  done

lemma reply_mdb : "\<And>m. reply_mdb m (caps_of_state s)
                  \<Longrightarrow> reply_mdb m (\<lambda>p. if fst p \<in> untyped_range cap then None else caps_of_state s p)"
  by (simp add: reply_mdb_def reply_caps_mdb reply_masters_mdb)

end

context detype_locale_gen_1 begin

lemma valid_mdb_detype[detype_invs_lemmas]: "valid_mdb (detype (untyped_range cap) s)"
  apply (insert invs, drule invs_mdb)
  apply (simp add: valid_mdb_def)
  apply (rule context_conjI)
   apply (safe intro!: mdb_cte_atI elim!: untyped_mdb untyped_inc reply_mdb)
        apply (drule(1) mdb_cte_atD)
        apply (clarsimp dest!: non_null_present)
       apply (drule(1) mdb_cte_atD)
       apply (clarsimp dest!: non_null_present)
      apply (erule descendants_inc_empty_slot)
       apply (clarsimp simp:cte_wp_at_caps_of_state swp_def)
      apply clarsimp
     apply (simp add: ut_revocable_def detype_def del: split_paired_All)
    apply (simp add: irq_revocable_def detype_def del: split_paired_All)
   apply (simp add: reply_master_revocable_def detype_def del: split_paired_All)
  apply (simp add: valid_arch_mdb_detype)
  done

lemma valid_ioports_detype[detype_invs_lemmas]:
  "valid_ioports (detype (untyped_range cap) s)"
  apply (insert invs, drule invs_valid_ioports)
  by (clarsimp simp: valid_ioports_detype)

lemma untype_children_detype[detype_invs_lemmas]: "untyped_children_in_mdb (detype (untyped_range cap) s)"
  apply (insert child)
  apply (simp add: untyped_children_in_mdb_def)
  apply (erule allEI)+
  apply (clarsimp simp: detype_def)
  done

lemma live_nonz_detype[detype_invs_lemmas]: "if_live_then_nonz_cap (detype (untyped_range cap) s)"
  apply (insert iflive)
  apply (simp add: if_live_then_nonz_cap_def ex_nonz_cap_to_def)
  apply (erule allEI)
  apply (rule impI, erule conjE, drule(1) mp)
  apply (erule exEI)
  apply clarsimp
  apply (frule non_null_present [OF cte_wp_at_weakenE])
   apply clarsimp+
  done

lemma irq_node_detype[simp]: (* duplicated lemma *)
  "\<And>r. interrupt_irq_node (detype r s) = interrupt_irq_node s"
  by (simp add: detype_def)
lemma INV_9[detype_invs_lemmas]: "if_unsafe_then_cap (detype (untyped_range cap) s)"
  apply (insert ifunsafe)
  apply (simp add: if_unsafe_then_cap_def ex_cte_cap_wp_to_def)
  apply (erule allEI, rule impI)
  apply (erule allEI)
  apply (clarsimp del: exE)
  apply (erule exEI)
  apply clarsimp
  apply (frule(1) non_null_caps)
  apply (frule non_null_present [OF cte_wp_at_weakenE])
   apply clarsimp+
  done

lemma zombies_final: "zombies_final s"
  using invs by (simp add: invs_def valid_state_def valid_pspace_def)

lemma zombies_final_detype[detype_invs_lemmas]: "zombies_final (detype (untyped_range cap) s)"
  apply (insert zombies_final)
  apply (simp add: zombies_final_def final_cap_at_eq)
  apply (elim allEI)
  apply (rule impI, erule conjE, drule(1) mp)
  apply (elim exEI conjE conjI allEI)
  apply (rule impI, elim conjE)
  apply simp
  done

lemma valid_refs_detype[detype_invs_lemmas]: "valid_global_refs (detype (untyped_range cap) s)"
  using globals
  by (simp add: valid_global_refs_def valid_refs_def glob_det)

lemma valid_reply_caps_detype[detype_invs_lemmas]:
  "valid_reply_caps (detype (untyped_range cap) s)"
    using vreply
    apply (clarsimp simp: valid_reply_caps_def has_reply_cap_def)
    apply (rule conjI)
     apply (erule allEI)
     apply (rule impI)
     apply (elim impE exE conjE, intro exI, assumption)
     apply (simp add: pred_tcb_at_def)
     apply (fastforce simp: live_def dest: live_okE)
    apply (clarsimp simp: unique_reply_caps_def)
    done

lemma valid_irq_detype[detype_invs_lemmas]: "valid_irq_node (detype (untyped_range cap) s)"
  using invs valid_globals_irq_node [OF globals cap]
  by (simp add: valid_irq_node_def invs_def valid_state_def cap_range_def)

lemma valid_reply_masters_detype[detype_invs_lemmas]:
  "valid_reply_masters (detype (untyped_range cap) s)"
  using vmaster by (clarsimp simp: valid_reply_masters_def)

lemma valid_irq_handlers_detype[detype_invs_lemmas]:
  "valid_irq_handlers (detype (untyped_range cap) s)"
  using invs
  apply (simp add: valid_irq_handlers_def ran_def irq_issued_def
                   invs_def valid_state_def)
  apply (force simp: detype_def)
  done

lemma only_idle_detype[detype_invs_lemmas]: "only_idle (detype (untyped_range cap) s)"
  proof -
    have "only_idle s"
      using invs by (simp add: invs_def valid_state_def)
    thus ?thesis
    apply (clarsimp simp: only_idle_def)
    apply (simp add: detype_def)
    done
  qed

lemma cap_refs_in_kernel_detype[detype_invs_lemmas]:
  "cap_refs_in_kernel_window (detype (untyped_range cap) s)"
proof -
  have "cap_refs_in_kernel_window s"
    using invs by (simp add: invs_def valid_state_def)
  thus ?thesis
    apply (simp add: cap_refs_in_kernel_window_def
                     valid_refs_def arch_state_det)
    done
qed

lemma valid_ioc_detype[detype_invs_lemmas]: "valid_ioc (detype (untyped_range cap) s)"
  proof -
    have "valid_ioc s" using invs by (simp add: invs_def valid_state_def)
    thus ?thesis
      apply (simp add: valid_ioc_def)
      apply (clarsimp simp: detype_def neq_commute)
      apply (drule spec, drule spec, erule impE, assumption)
      apply (frule_tac p="(a,b)" in non_null_present[simplified neq_commute])
      apply simp
      done
  qed

lemmas p2pm1_to_mask = add_mask_fold

lemma valid_irq_states_detype[detype_invs_lemmas]: "valid_irq_states
          (clear_um (untyped_range cap) (detype (untyped_range cap) s))"
  proof -
    have "valid_irq_states s" using invs by (simp add: invs_def valid_state_def)
    thus ?thesis
      apply(clarsimp simp: clear_um_def detype_def valid_irq_states_def)
      done
  qed

end

context detype_locale_gen_2 begin
lemma invariants:
  assumes ct_act: "ct_active s"
  shows "(invs and untyped_children_in_mdb)
         (detype (untyped_range cap) (clear_um (untyped_range cap) s))"
  using detype_invs_lemmas detype_invs_assms ct_act
  by (simp add: invs_def valid_state_def valid_pspace_def
                detype_clear_um_independent clear_um.state_refs_update)

end


(* detype_locale_gen_2 cap ptr s  *)
(* FIXME: move *)
lemma gets_modify_comm2:
  "\<forall>s. g (f s) = g s \<Longrightarrow>
   (do x \<leftarrow> modify f; y \<leftarrow> gets g; m x y od) =
   (do y \<leftarrow> gets g; x \<leftarrow> modify f; m x y od)"
  apply (rule ext)
  apply (drule spec)
  by (rule gets_modify_comm)


lemma dmo_detype_comm:
  assumes "empty_fail f"
  shows "do_machine_op f >>= (\<lambda>s. modify (detype S)) =
         modify (detype S) >>= (\<lambda>s. do_machine_op f)"
proof -
  have machine_state_detype: "\<forall>s. machine_state (detype S s) = machine_state s"
    by (simp add: detype_def)
  have detype_msu_independent:
    "\<And>f. detype S \<circ> machine_state_update f = machine_state_update f \<circ> detype S"
    by (simp add: detype_def ext)
  from assms
  show ?thesis
    apply (simp add: do_machine_op_def split_def bind_assoc)
    apply (simp add: gets_modify_comm2[OF machine_state_detype])
    apply (rule arg_cong_bind1)
    apply (simp add: empty_fail_def select_f_walk[OF empty_fail_modify]
                     modify_modify detype_msu_independent)
    done
qed

lemma (in Detype_AI) delete_objects_def2:
  "delete_objects ptr bits \<equiv>
   do modify (detype {ptr..ptr + 2 ^ bits - 1});
      do_machine_op (freeMemory ptr bits)
   od"
  by (rule eq_reflection)
     (simp add: delete_objects_def dmo_detype_comm[OF empty_fail_freeMemory])

(* FIXME: move *)
lemma modify_modify_bind:
  "(modify f >>= (\<lambda>_. (modify g >>= h))) =
   (modify (g \<circ> f) >>= h)"
  by (simp add: modify_modify bind_assoc[symmetric])


lemma dmo_untyped_children_in_mdb[wp]:
  "\<lbrace>\<lambda>s. untyped_children_in_mdb s\<rbrace>
   do_machine_op f
   \<lbrace>\<lambda>rv s. untyped_children_in_mdb s\<rbrace>"
  by (wp | simp add: untyped_mdb_alt[symmetric] do_machine_op_def split_def)+


lemma detype_machine_state_update_comm:
  "detype S (machine_state_update f s) =
   machine_state_update f (detype S s)"
  by (case_tac s, simp add: detype_def ext)


lemma interrupt_irq_node_detype[simp]:
  "interrupt_irq_node (detype S s) = interrupt_irq_node s"
  by (simp add: detype_def)


lemma cte_wp_at_delete_objects[wp]:
  "\<lbrace>\<lambda>s. Q (cte_wp_at (P (interrupt_irq_node s)) p s) \<and>
        fst p \<notin> {ptr..ptr + 2 ^ bits - 1}\<rbrace>
   delete_objects ptr bits
   \<lbrace>\<lambda>_ s. Q (cte_wp_at (P (interrupt_irq_node s)) p s)\<rbrace>"
  apply (simp add: delete_objects_def do_machine_op_def split_def)
  apply wp
  apply (simp add: detype_machine_state_update_comm)
  done



lemma cdt_delete_objects[wp]:
  "\<lbrace>\<lambda>s. P (cdt s)\<rbrace> delete_objects ptr bits \<lbrace>\<lambda>_ s. P (cdt s)\<rbrace>"
  by (wp | simp add: delete_objects_def do_machine_op_def split_def)+


lemma of_nat_le_pow:
  "\<lbrakk>x < 2 ^ n; n \<le> len_of TYPE('a)\<rbrakk> \<Longrightarrow> of_nat x \<le> (mask n :: 'a :: len word)"
  apply (drule_tac a="2::nat" in power_increasing, simp)
  apply (frule less_le_trans, assumption)
  apply (frule of_nat_mono_maybe_le[OF unat_lt2p[of "mask n:: 'a :: len word"],
                                    folded word_bits_def])
  apply simp
  apply (simp add: unat_mask min_def)
  apply (erule iffD1)
  apply simp
  done

lemma mapM_x_storeWord_step_aux2:
  "\<lbrakk>is_aligned ptr sz;
  sz \<le> word_bits;
  \<not> ptr + 2 ^ sz - 1 < ptr;
  xb < 2 ^ (sz - word_size_bits) \<rbrakk> \<Longrightarrow>
  ptr + word_of_nat xb * word_size \<in> {ptr + word_of_nat k |k. k < 2 ^ sz}"
  apply clarsimp
  apply (intro exI [where x="xb * word_size"])
  apply (intro conjI)
   apply (clarsimp simp:word_size_def)
  apply (metis word_size_word_size_bits One_nat_def add_diff_cancel_left' diff_diff_less lessI
         nat_1_add_1 nat_mult_power_less_eq)
  done


lemma mapM_x_storeWord_step_aux:
  "\<lbrakk>is_aligned ptr sz;
  sz \<le> word_bits;
  \<not> ptr + 2 ^ sz - 1 < ptr;
  k < 2 ^ sz\<rbrakk> \<Longrightarrow>
  ptr + word_of_nat k \<in> {ptr + word_of_nat x * word_size |x. x < 2 ^ (sz - word_size_bits)}"
  apply clarsimp
  oops

(* FIXME: copied from Retype_C and slightly adapted. *)
lemma (in Detype_AI) mapM_x_storeWord_step:
  assumes al: "is_aligned ptr sz"
  and    sz2: "word_size_bits \<le> sz"
  and     sz: "sz <= word_bits"
  shows "mapM_x (\<lambda>p. storeWord p 0) [ptr , ptr + word_size .e. ptr + 2 ^ sz - 1]
  = do ta \<leftarrow> gets touched_addresses;
       assert ({x. \<exists>k. x = ptr + of_nat k \<and> k < 2 ^ sz} \<subseteq> ta);
       modify (underlying_memory_update
         (\<lambda>m x. if x \<in> {x. \<exists>k. x = ptr + of_nat k \<and> k < 2 ^ sz} then 0 else m x))
    od"
  using al sz
  apply (simp only: upto_enum_step_def field_simps cong: if_cong)
  apply (prop_tac "\<not> ptr + 2 ^ sz - 1 < ptr")
   apply (subst not_less)
   apply (erule is_aligned_no_overflow)
  apply simp
  apply (simp add: mapM_x_map comp_def upto_enum_word del: upt.simps)
  apply (simp add: Suc_unat_mask_div_obfuscated[simplified mask_2pm1] min_def)
  apply (subst mapM_x_storeWord)
   apply (erule is_aligned_weaken [OF _ sz2])
  apply (rule ext)
  apply (clarsimp simp: assert_def fail_def return_def simpler_gets_def bind_def
                        simpler_modify_def
                 split: if_splits)
  apply (intro conjI; clarsimp)+
    apply (rule arg_cong2 [where f=underlying_memory_update, OF _ refl])
    apply (subgoal_tac "2^word_size_bits = (word_size :: nat)")
     apply (cut_tac power_add[symmetric,of "2::nat" "sz - word_size_bits" word_size_bits])
     apply (simp only: le_add_diff_inverse2[OF sz2])
    apply (simp add: word_size_size_bits_nat)
   subgoal sorry (* broken by touched-addrs. not sure if this is exactly the
   approach to take. need to take another look, and see how this approach goes. *)
   (* using mapM_x_storeWord_step_aux apply fastforce *)
  using mapM_x_storeWord_step_aux2 apply blast
  done

lemma (in Detype_AI) mapM_storeWord_clear_um:
  "\<lbrakk>is_aligned p n;
  word_size_bits\<le>n;
  n<=word_bits\<rbrakk> \<Longrightarrow>
  do_machine_op (mapM_x (\<lambda>p. storeWord p 0) [p, p + word_size .e. p + 2 ^ n - 1]) =
  do
    ta \<leftarrow> gets (\<lambda>s. touched_addresses (machine_state s));
    assert ({x. \<exists>k. x = p + of_nat k \<and> k < 2 ^ n} \<subseteq> ta);
    modify (clear_um {x.  \<exists>k. x = p + of_nat k \<and> k < 2 ^ n})
  od"
  apply (simp add: mapM_x_storeWord_step)
  apply (rule ext)
  apply (simp add: do_machine_op_def select_f_def split_def simpler_modify_def
                   simpler_gets_def bind_def return_def clear_um_def assert_def
                   fail_def)
  done

lemma intvl_range_conv':
  "\<lbrakk>is_aligned (ptr::'a :: len word) bits; bits \<le> len_of TYPE('a)\<rbrakk> \<Longrightarrow>
   (\<exists>k. x = ptr + of_nat k \<and> k < 2 ^ bits) \<longleftrightarrow> (ptr \<le> x \<and> x \<le> ptr + 2 ^ bits - 1)"
  apply (rule iffI)
   apply (clarsimp simp: x_power_minus_1 mask_2pm1[symmetric])
   apply (frule is_aligned_no_overflow'[simplified mask_2pm1[symmetric]])
   apply (rule conjI)
    apply (rule word_plus_mono_right2, assumption)
    apply (frule (2) of_nat_le_pow)
   apply (rule word_plus_mono_right)
    apply (rule word_of_nat_le)
    apply (simp add: unat_mask)
   apply simp
  apply (subgoal_tac "\<exists>x'. x = ptr + of_nat x' \<and> x' < 2 ^ len_of TYPE('a)")
   apply clarsimp
   apply (drule(1) word_le_minus_mono_left [where x=ptr])
   apply (simp only: p_assoc_help add_diff_cancel2)
   apply (rule_tac x="x'" in exI)
   apply (clarsimp simp: word_le_nat_alt unat_of_nat mask_2pm1[symmetric])
   apply (auto simp: unat_mask min_def le_less)[1]
  apply (rule_tac x="unat (x - ptr)" in exI)
  apply simp
  done

(* FIXME: The following lemma is similar to StoreWord_C.intvl_range_conv *)
(* FIXME: move *)
lemma intvl_range_conv:
  "\<lbrakk>is_aligned (ptr :: 'a :: len word) bits; bits \<le> len_of TYPE('a)\<rbrakk> \<Longrightarrow>
   {x. \<exists>k. x = ptr + of_nat k \<and> k < 2 ^ bits} = {ptr .. ptr + 2 ^ bits - 1}"
  by (rule set_eqI) (simp add: intvl_range_conv')


(* FIXME: move *)
lemma gets_modify_def:
  "gets f >>= (\<lambda>x. modify (g x)) = modify (\<lambda>s. g (f s) s)"
by (simp add: simpler_gets_def simpler_modify_def bind_def)


lemma valid_pspace_well_formed_cnode[intro?]:
  "\<lbrakk>valid_pspace s; kheap s x = Some (CNode sz ct)\<rbrakk> \<Longrightarrow> well_formed_cnode_n sz ct"
  by (erule (1) well_formed_cnode_valid_cs_size [OF valid_cs_sizeI])


lemmas cte_wp_at_cte_at = cte_wp_at_weakenE [OF _ TrueI]


lemma cte_wp_at_domI:
  "cte_wp_at P c s \<Longrightarrow> fst c \<in> dom (kheap s)"
  by (auto elim: cte_wp_atE)


lemmas cte_wp_at_casesE [consumes 1, case_names CapTable TCB] = cte_wp_atE


lemma dom_known_length:
  "\<lbrakk> dom f = {x. length x = n}; f xs = Some cap \<rbrakk> \<Longrightarrow> n = length xs"
  by (drule domI[where m=f], simp)


lemma (in Detype_AI) cte_map_not_null_outside: (*FIXME: arch_split*)
  "\<lbrakk> cte_wp_at ((\<noteq>) cap.NullCap) p (s :: 'a state);
     cte_wp_at ((=) cap) p' s;is_untyped_cap cap;
     descendants_range cap p' s; untyped_children_in_mdb s;
     if_unsafe_then_cap s; valid_global_refs s \<rbrakk>
     \<Longrightarrow> fst p \<notin> untyped_range cap"
  apply (simp add:descendants_range_def2)
  apply (case_tac "cte_wp_at (\<lambda>c. is_zombie c \<and> obj_ref_of c = fst p) p s")
   apply (rule ccontr)
   apply (erule(2) untyped_children_in_mdbEE[where ptr'=p])
     apply (simp add:cte_wp_at_caps_of_state is_cap_simps)
    apply (clarsimp simp:cte_wp_at_caps_of_state is_cap_simps)
   apply (drule descendants_range_inD)
     apply (simp add:cte_wp_at_caps_of_state)
    apply (simp add:cte_wp_at_caps_of_state)
   apply simp
  apply (drule(1) if_unsafe_then_capD, simp)
  apply (drule ex_cte_cap_to_obj_ref_disj, erule disjE)
   apply (clarsimp simp del:untyped_range.simps)+
   apply (erule(1) untyped_children_in_mdbEE [where P="\<lambda>c. fst p \<in> f c" for f])
      apply simp+
    apply fastforce
    apply (drule(1) descendants_range_inD)
     apply (simp add:cte_wp_at_caps_of_state)
   apply simp
  apply clarsimp
  apply (drule(1) valid_globals_irq_node, fastforce simp: cap_range_def)
  done


lemma corres_submonad2:
  "\<lbrakk> submonad f r g fn; submonad f' r' g' fn';
     \<forall>s s'. (s, s') \<in> sr \<and> g s \<and> g' s' \<longrightarrow> (f s, f' s') \<in> ssr;
     \<forall>s s' ss ss'. ((s, s') \<in> sr \<and> (ss, ss') \<in> ssr) \<longrightarrow> (r ss s, r' ss' s') \<in> sr;
     corres_underlying ssr nf nf' rvr P P' x x'\<rbrakk>
   \<Longrightarrow> corres_underlying sr nf nf' rvr (g and P o f) (g' and P' o f') (fn x) (fn' x')"
  apply (subst submonad.fn_is_sm, assumption)+
  apply (clarsimp simp: submonad_fn_def)
  apply (rule corres_split' [OF _ _ stateAssert_sp stateAssert_sp])
   apply (fastforce simp: corres_underlying_def stateAssert_def get_def
                         assert_def return_def bind_def)
  apply (rule corres_split' [where r'="\<lambda>x y. (x, y) \<in> ssr",
                             OF _ _ gets_sp gets_sp])
   apply clarsimp
  apply (rule corres_split' [where r'="\<lambda>(x, x') (y, y'). rvr x y \<and> (x', y') \<in> ssr",
                             OF _ _ hoare_post_taut hoare_post_taut])
   defer
   apply clarsimp
   apply (rule corres_split' [where r'=dc, OF _ _ hoare_post_taut hoare_post_taut])
    apply (simp add: corres_modify')
   apply clarsimp
  apply (simp add: corres_underlying_def select_f_def)
  apply fastforce
  done


lemma corres_submonad3:
  "\<lbrakk>submonad f r g fn; submonad f' r' g' fn';
    \<forall>s s'. (s, s') \<in> sr \<and> g s \<and> g' s' \<longrightarrow> (f s, f' s') \<in> ssr;
    \<forall>s s' ss ss'. ((s, s') \<in> sr \<and> (ss, ss') \<in> ssr) \<longrightarrow>
                  (r ss s, r' ss' s') \<in> sr;
    \<forall>s. G s \<longrightarrow> g s \<and> P (f s); \<forall>s'. G' s' \<longrightarrow> g' s' \<and> P' (f' s');
    corres_underlying ssr nf nf' rvr P P' x x'\<rbrakk>
   \<Longrightarrow> corres_underlying sr nf nf' rvr G G' (fn x) (fn' x')"
  apply (subst submonad.fn_is_sm, assumption)+
  apply (clarsimp simp: submonad_fn_def)
  apply (rule corres_split' [OF _ _ stateAssert_sp stateAssert_sp])
   apply (fastforce simp: corres_underlying_def stateAssert_def get_def
                         assert_def return_def bind_def)
  apply (rule corres_split' [where r'="\<lambda>x y. (x, y) \<in> ssr",
                             OF _ _ gets_sp gets_sp])
   apply clarsimp
  apply (rule corres_split' [where r'="\<lambda>(x, x') (y, y'). rvr x y \<and> (x', y') \<in> ssr",
                             OF _ _ hoare_post_taut hoare_post_taut])
   defer
   apply clarsimp
   apply (rule corres_split' [where r'=dc, OF _ _ hoare_post_taut hoare_post_taut])
    apply (simp add: corres_modify')
   apply clarsimp
  apply (simp add: corres_underlying_def select_f_def)
  apply fastforce
  done


lemma invs_untyped_children[elim!]:
  "invs s \<Longrightarrow> untyped_children_in_mdb s"
  by (clarsimp simp: invs_def valid_state_def valid_mdb_def
                     untyped_mdb_alt)

lemma dmo_valid_cap[wp]:
  "\<lbrace>\<lambda>s. s \<turnstile> cap.UntypedCap dev base magnitude idx\<rbrace>
   do_machine_op f
   \<lbrace>\<lambda>rv s. s \<turnstile> cap.UntypedCap dev base magnitude idx\<rbrace>"
  by (simp add: do_machine_op_def split_def | wp)+

lemma (in Detype_AI)cte_map_not_null_outside':
  "\<lbrakk>cte_wp_at ((=) (cap.UntypedCap dev q n m)) p' (s :: 'a state);
    descendants_range (cap.UntypedCap dev q n m) p' s; untyped_children_in_mdb s;
    if_unsafe_then_cap s; valid_global_refs s;
    cte_wp_at ((\<noteq>) cap.NullCap) p s\<rbrakk>
   \<Longrightarrow> fst p \<notin> untyped_range (cap.UntypedCap dev q n m)"
  by (erule (1) cte_map_not_null_outside, simp_all)

lemma refl_spec[simp]:
  "\<not> (\<forall>x. x \<noteq> y)"
  by clarsimp

lemma pre_helper:
  "\<And>base x n. \<lbrakk> is_aligned (base :: machine_word) (n + (a::nat)); n + a < word_bits \<rbrakk>
  \<Longrightarrow> base + (x && mask n) * 2^a \<in> {base .. base + 2 ^ (n + a) - 1}"
    apply (subgoal_tac "(x && mask n) * bit(a) < 2 ^ (n + a)")
     apply simp
     apply (rule context_conjI)
      apply (erule(1) is_aligned_no_wrap')
     apply (subst add_diff_eq[symmetric])
     apply (rule word_plus_mono_right)
      apply simp
     apply (erule is_aligned_no_wrap')
     apply simp
    apply (simp add: power_add)
    apply (rule word_mult_less_mono1)
      apply (rule and_mask_less_size, simp add: word_size word_bits_def)
     apply (simp add: p2_gt_0 word_bits_def)
    apply (simp add: word_bits_def)
    apply (drule power_strict_increasing[where a="2 :: nat"], simp_all)
    apply (simp add: power_add[where a="2::nat"])
    done


lemmas ucast_ucast_mask_8 = ucast_ucast_mask[where 'a=8, simplified, symmetric]

lemma pspace_no_overlap_obj_range:
  "\<lbrakk> pspace_no_overlap S s; kheap s p = Some obj \<rbrakk>
     \<Longrightarrow> obj_range p obj \<inter> S = {}"
  by (auto simp add: pspace_no_overlap_def obj_range_def field_simps)

(* FIXME: generalised version of Arch_AI.range_cover_full *)
lemma range_cover_full:
  "\<lbrakk>is_aligned (ptr :: 'a :: len word) sz;sz < len_of TYPE('a)\<rbrakk> \<Longrightarrow> range_cover ptr sz sz (Suc 0)"
   by (clarsimp simp:range_cover_def
     unat_eq_0 le_mask_iff[symmetric] word_and_le1)

lemma range_cover_plus_us:
  "range_cover ptr sz (m + us) (Suc 0) \<Longrightarrow> range_cover ptr sz m (2^us)"
  apply (erule range_cover_rel)
   apply simp+
  done


lemma caps_overlap_reserved_subseteq:
  "\<lbrakk>caps_overlap_reserved B s; A\<subseteq> B\<rbrakk> \<Longrightarrow> caps_overlap_reserved A s"
  apply (clarsimp simp:caps_overlap_reserved_def)
  apply (drule(1) bspec)
  apply (erule disjoint_subset2)
  apply simp
  done


lemma range_cover_le:
  "\<lbrakk>range_cover ptr sz us m; n\<le>m\<rbrakk> \<Longrightarrow> range_cover ptr sz us n"
  by (clarsimp simp:range_cover_def)


lemma range_cover_ptr_le:
  "\<lbrakk>range_cover ptr sz us (Suc (Suc n));ptr\<noteq> 0\<rbrakk>
   \<Longrightarrow> ptr \<le> ptr + (1 + of_nat n << us)"
  apply (frule range_cover_subset[where p = 0
    ,OF range_cover_le[where n = "Suc n"]])
  apply simp+
  apply (frule is_aligned_no_overflow[OF range_cover.aligned])
  apply (simp add:shiftl_t2n field_simps)
  apply (erule order_trans)+
  apply (rule word_sub_1_le)
  apply (drule(1) range_cover_no_0[where p = "Suc n"])
   apply simp
  apply (simp add:word_arith_nat_Suc power_add[symmetric] field_simps)
  done


lemma range_cover_tail_mask:
  "\<lbrakk>range_cover ptr sz us (Suc (Suc n));ptr \<noteq> 0\<rbrakk>
   \<Longrightarrow> ptr  + ((1::machine_word) + of_nat n << us)  && ~~ mask sz = ptr && ~~ mask sz"
  apply (frule(1) range_cover_ptr_le)
  apply (subst word_plus_and_or_coroll2[symmetric,where w = "mask sz" and t = ptr])
  apply (subst add.commute)
  apply (subst add.assoc)
  apply (subst is_aligned_add_helper[THEN conjunct2,OF is_aligned_neg_mask])
    apply (simp add:range_cover_def)
    apply (simp add:word_less_nat_alt)
    apply (rule le_less_trans[OF unat_plus_gt])
    apply (frule range_cover.range_cover_compare[where p = "Suc n"])
     apply simp
    apply (drule range_cover.sz)
   apply (simp add:word_arith_nat_Suc shiftl_t2n power_add[symmetric] field_simps)
  apply simp
  done


lemma range_cover_unat:
  "range_cover (ptr :: 'a :: len word) sz sb n
   \<Longrightarrow> unat ((ptr && mask sz) + (of_nat n * 2^ sb)) =
       unat (ptr && mask sz) + unat ( (of_nat n) * (2::'a word) ^ sb)"
       apply (rule unat_add_lem[THEN iffD1])
       apply (rule le_less_trans)
       apply (frule range_cover.unat_of_nat_shift[OF _ le_refl le_refl])
       apply (simp add:field_simps)
       apply (subst add.commute)
       apply (erule range_cover.range_cover_compare_bound)
       apply (rule power_strict_increasing)
       apply (clarsimp simp:range_cover_def)+
       done


lemma range_cover_offset:
  assumes offset: "p < n"
  and     cover : "range_cover ptr sz us n"
  shows "range_cover (ptr + (of_nat p) * 2 ^ us) sz us (n - p)"
  using assms range_cover.range_cover_compare_bound[OF cover]
  apply (clarsimp simp:range_cover_def)
  apply (intro conjI)
   apply (erule aligned_add_aligned)
    apply (subst mult.commute)
    apply (simp add:is_aligned_shiftl_self[unfolded shiftl_t2n])
   apply simp
  apply (rule nat_mult_le_cancel1[where k = "2^ us",THEN iffD1])
   apply simp
  apply (subst diff_mult_distrib2)
  apply (simp add: add_mult_distrib2)
  apply (simp add:shiftr_div_2n' field_simps minus_mod_eq_mult_div[symmetric])
  apply (rule le_trans[where j = "(n-p) * 2 ^ us + unat (ptr + of_nat p * 2 ^ us && mask sz)"])
   apply (clarsimp simp:field_simps diff_mult_distrib diff_le_mono2)
  apply (subst mask_eqs[symmetric])
  apply (subst less_mask_eq[where x = "(ptr && mask sz) + of_nat p * 2 ^ us"])
   apply (simp add:word_less_nat_alt)
   apply (rule le_less_trans[OF unat_plus_gt])
   apply (erule range_cover.range_cover_compare[OF cover])
  apply (simp add:range_cover_unat[OF range_cover_le[OF cover]] field_simps)
  apply (simp add:range_cover.unat_of_nat_shift[OF cover] diff_mult_distrib)
  apply (simp add:field_simps power_add[symmetric]
    range_cover.range_cover_compare_bound[OF cover])
  done


lemma range_cover_bound:
  assumes cover:"range_cover ptr sz us n"
  shows "0<n \<Longrightarrow> ptr \<le> ptr + of_nat n * 2^ us - 1"
  apply (cut_tac range_cover_subset[OF cover,where p = 0])
    apply (cut_tac Retype_AI.range_cover_subset_not_empty[OF _ cover , where x = 0])
     apply (clarsimp simp del: atLeastatMost_subset_iff)
     apply (drule_tac c=ptr in subsetD)
      apply simp
     apply simp
    apply (cut_tac range_cover_not_zero[OF _ cover])
    apply (simp add:word_gt_0)+
  done


lemma range_cover_compare_offset:
  "\<lbrakk>range_cover ptr sz us t; n + 1 < t;ptr \<noteq> 0\<rbrakk>
   \<Longrightarrow> ptr + (of_nat n << us) \<le> ptr + (1 + of_nat n << us)"
  apply (simp add:shiftl_t2n field_simps)
  apply (rule order_trans[OF range_cover_bound])
    apply (rule range_cover_offset[rotated])
     apply (erule_tac n = "n+1" in range_cover_le)
     apply simp+
  apply (simp add:field_simps)
  apply (rule word_sub_1_le)
  apply (drule_tac n = "n + 2" and p = "n + 1" in range_cover_no_0)
  apply (erule range_cover_le)
  apply simp
  apply simp
  apply (simp add:field_simps)
  done


lemma range_cover_sz':
  "range_cover (a :: 'a :: len word) b bits d \<Longrightarrow> bits < len_of TYPE('a)"
  by (clarsimp simp:range_cover_def)


end
