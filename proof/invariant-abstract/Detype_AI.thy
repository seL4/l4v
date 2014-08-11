(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory Detype_AI
imports Retype_AI
begin

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


lemma st_tcb_at_detype[simp]:
  "(st_tcb_at P t (detype S s))
    = (st_tcb_at P t s \<and> t \<notin> S)"
  by (fastforce simp add: st_tcb_at_def)


lemma cdt_detype[simp]:
  "cdt (detype S s) = cdt s"
  by (simp add: detype_def)


lemma caps_of_state_detype[simp]:
  "caps_of_state (detype S s) =
   (\<lambda>p. if fst p \<in> S then None else caps_of_state s p)"
  by (clarsimp simp add: caps_of_state_cte_wp_at
                 intro!: ext)


lemma state_refs_of_detype:
  "state_refs_of (detype S s) = (\<lambda>x. if x \<in> S then {} else state_refs_of s x)"
  by (rule ext, simp add: state_refs_of_def detype_def)


definition
  obj_reply_refs :: "cap \<Rightarrow> word32 set"
where
 "obj_reply_refs cap \<equiv> obj_refs cap \<union>
   (case cap of cap.ReplyCap t m \<Rightarrow> {t} | _ \<Rightarrow> {})"


lemma ex_cte_cap_to_obj_ref_disj:
  "ex_cte_cap_wp_to P ptr s
      \<Longrightarrow> ((\<exists>ptr'. cte_wp_at (\<lambda>cap. fst ptr \<in> obj_refs cap) ptr' s)
               \<or> (\<exists>ptr' irq. cte_wp_at (op = (cap.IRQHandlerCap irq)) ptr' s
                               \<and> ptr = (interrupt_irq_node s irq, [])))"
  apply (clarsimp simp: ex_cte_cap_wp_to_def cte_wp_at_caps_of_state)
  apply (frule cte_refs_obj_refs_elem, erule disjE)
   apply fastforce
  apply clarsimp
  done


lemma valid_globals_irq_node:
  "\<lbrakk> valid_global_refs s; cte_wp_at (op = cap) ptr s \<rbrakk>
        \<Longrightarrow> interrupt_irq_node s irq \<notin> cap_range cap"
  apply (erule(1) valid_global_refsD)
  apply (simp add: global_refs_def)
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
  apply (clarsimp simp:cte_wp_at_caps_of_state null_filter_def cap_range_def split:split_if_asm)
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


lemma caps_of_state_ko: 
  "valid_cap cap s \<Longrightarrow> is_untyped_cap cap \<or> cap_range cap = {} \<or> (\<forall>ptr \<in> cap_range cap. \<exists>ko. kheap s ptr = Some ko)"
  apply (case_tac cap)
    apply (clarsimp simp:cap_range_def valid_cap_def obj_at_def is_cap_simps split:option.splits)+
  apply (case_tac arch_cap)
    apply (fastforce simp:cap_range_def obj_at_def is_cap_simps split:option.splits)+
  done


lemma p_in_obj_range:
  "\<lbrakk> kheap s p = Some ko; pspace_aligned s; valid_objs s \<rbrakk> \<Longrightarrow> p \<in> obj_range p ko"
  apply (simp add: pspace_aligned_def)
  apply (drule bspec, erule domI)
  apply (drule valid_obj_sizes, erule ranI)
  apply (simp add: obj_range_def add_diff_eq[symmetric])
  apply (erule is_aligned_no_wrap')
  apply (erule word_power_less_1[where 'a=32, folded word_bits_def])
  done


lemma untyped_cap_descendants_range:
  "\<lbrakk>valid_pspace s; caps_of_state s p = Some cap; is_untyped_cap cap;valid_mdb s;
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
       apply (thin_tac "?P\<longrightarrow>?Q")+
       apply (clarsimp simp:descendants_of_def)
       apply (drule(1) trancl_trans)
       apply (simp add:vmdb_abs_def valid_mdb_def vmdb_abs.no_loops)
      apply simp
     apply simp
     apply (clarsimp simp:descendants_of_def | erule disjE)+
     apply (drule(1) trancl_trans)
     apply (simp add:vmdb_abs_def valid_mdb_def vmdb_abs.no_loops)+
   apply (thin_tac "?P\<longrightarrow>?Q")+
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
  apply (thin_tac "\<forall>x y z. ?P x y z")
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
  assumes ass: "untyped_children_in_mdb s" "cte_wp_at (op = cap) ptr s" "is_untyped_cap cap" "cte_wp_at P ptr' s" 
  and  step1: "\<And>cap'. \<lbrakk>cte_wp_at (op = cap') ptr' s; P cap'\<rbrakk> \<Longrightarrow> obj_refs cap' \<inter> untyped_range cap \<noteq> {}"
  and  step2: "\<And>cap'. \<lbrakk>cte_wp_at (op = cap') ptr' s; cap_range cap' \<inter> untyped_range cap \<noteq> {};ptr' \<in> descendants_of ptr (cdt s) \<rbrakk> \<Longrightarrow> Q"
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


locale detype_locale =
  fixes cap and ptr and s
  assumes cap: "cte_wp_at (op = cap) ptr s"
  and untyped: "is_untyped_cap cap"
  and  nodesc: "descendants_range cap ptr s"
  and    invs: "invs s"
  and   child: "untyped_children_in_mdb s"


lemma descendants_range_inD:
  "\<lbrakk>descendants_range_in S p s;p'\<in>descendants_of p (cdt s);caps_of_state s p' = Some cap\<rbrakk>
 \<Longrightarrow> cap_range cap \<inter> S = {}"
  by (auto simp:descendants_range_in_def cte_wp_at_caps_of_state dest!:bspec)


definition
  "clear_um S \<equiv> (machine_state_update \<circ> underlying_memory_update)
                (\<lambda>m p. if p\<in>S then 0 else m p)"

interpretation clear_um: 
  p_arch_idle_update_int_eq "clear_um S"
  by unfold_locales (simp_all add: clear_um_def)

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
  

context detype_locale
begin
lemma drange:"descendants_range_in (cap_range cap) ptr s"
   using nodesc
   by (simp add:descendants_range_def2)


lemma valid_cap:
    "\<And>cap'. \<lbrakk> s \<turnstile> cap'; obj_reply_refs cap' \<subseteq> (UNIV - untyped_range cap) \<rbrakk>
    \<Longrightarrow> detype (untyped_range cap) s \<turnstile> cap'"
  by (clarsimp simp: valid_cap_def valid_untyped_def obj_reply_refs_def
              split: cap.split_asm option.splits arch_cap.split_asm bool.split_asm)

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


lemma irq_node: "interrupt_irq_node s irq \<notin> untyped_range cap"
  using valid_globals_irq_node [OF globals cap]
  by (simp add: cap_range_def)


lemma non_null_present:
    "\<And>p. cte_wp_at (op \<noteq> cap.NullCap) p s \<Longrightarrow> fst p \<notin> untyped_range cap"
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
    "\<And>cap'. \<lbrakk> \<exists>p. cte_wp_at (op = cap') p s \<rbrakk>
    \<Longrightarrow> obj_reply_refs cap' \<subseteq> (UNIV - untyped_range cap)"
    apply clarsimp
    apply (simp add: obj_reply_refs_def, erule disjE)
     apply (erule untyped_children_in_mdbEE [OF child cap untyped])
      apply blast
     apply (drule descendants_range_inD[OF drange])
      apply (simp add:cte_wp_at_caps_of_state)
     apply (simp add:untyped)
    apply (clarsimp split: cap.split_asm bool.split_asm)
    apply (case_tac bool, simp_all)
     apply (frule valid_reply_mastersD [OF _ vmaster])
     apply (fastforce simp: cte_wp_at_caps_of_state dest: non_null_caps)
    apply (drule has_reply_cap_cte_wpD)
    apply (drule valid_reply_capsD [OF _ vreply])
    apply (simp add: st_tcb_at_def)
    apply (fastforce dest: live_okE)
    done

lemma invariants:
  assumes ct_act: "ct_active s"
  shows "(invs and untyped_children_in_mdb)
         (detype (untyped_range cap) (clear_um (untyped_range cap) s))"
proof (simp add: invs_def valid_state_def valid_pspace_def
                 detype_clear_um_independent clear_um.state_refs_update, safe)

  have refsym: "sym_refs (state_refs_of s)"
    using invs by (simp add: invs_def valid_state_def valid_pspace_def)
  have refs_of: "\<And>obj p. \<lbrakk> ko_at obj p s \<rbrakk> \<Longrightarrow> refs_of obj \<subseteq> (UNIV - untyped_range cap \<times> UNIV)"
    apply (drule sym_refs_ko_atD [OF _ refsym])
    apply clarsimp
    apply (drule(1) bspec)
    apply clarsimp
    apply (drule live_okE)
     apply (rule refs_of_live, clarsimp)
    apply simp
    done
  have refs_of2: "\<And>obj p. kheap s p = Some obj
                       \<Longrightarrow> refs_of obj \<subseteq> (UNIV - untyped_range cap \<times> UNIV)"
    by (simp add: refs_of obj_at_def)
  have valid_obj: "\<And>p obj. \<lbrakk> valid_obj p obj s; ko_at obj p s \<rbrakk>
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
       apply (clarsimp simp: valid_tcb_def obj_at_def)
       apply (rule conjI)
        apply (erule ballEI)
        apply (clarsimp elim!: ranE)
        apply (erule valid_cap [OF _ valid_cap2])
        apply (fastforce intro!: cte_wp_at_tcbI)
       apply (clarsimp simp: valid_tcb_state_def
                      split: Structures_A.thread_state.split_asm)
      apply (frule refs_of)
      apply (case_tac endpoint, (fastforce simp: valid_ep_def)+)
     apply (frule refs_of)
     apply (case_tac async_ep, (fastforce simp: valid_aep_def)+)
    done

  show "valid_objs (detype (untyped_range cap) s)"
    using invs_valid_objs[OF invs]
    apply (clarsimp simp add: valid_objs_def dom_def)
    apply (erule allE, erule impE, erule exI)
    apply (clarsimp elim!: valid_obj)
    apply (simp add: obj_at_def)
    done

  show "pspace_aligned (detype (untyped_range cap) s)"
    using invs_psp_aligned[OF invs]
    apply (clarsimp simp: pspace_aligned_def)
    apply (drule bspec, erule domI)
    apply (clarsimp simp: detype_def)
    done

  have state_refs: "state_refs_of (detype (untyped_range cap) s)
                      = state_refs_of s"
    apply (rule ext, clarsimp simp add: state_refs_of_detype)
    apply (rule sym, rule equals0I, drule state_refs_of_elemD)
    apply (drule live_okE, rule refs_of_live, clarsimp)
    apply simp
    done
  show "sym_refs (state_refs_of (detype (untyped_range cap) s))"
    using refsym by (simp add: state_refs)
  show "pspace_distinct (detype (untyped_range cap) s)"
    apply (insert invs, drule invs_distinct)
    apply (auto simp: pspace_distinct_def)
    done
  show "cur_tcb (detype (untyped_range cap) s)"
    apply (insert ct_act invs)
    apply (drule tcb_at_invs)
    apply (simp add: cur_tcb_def ct_in_state_def)
    apply (clarsimp simp: detype_def st_tcb_at_def)
    apply (drule live_okE)
     apply fastforce
    apply simp
    done
  have live_okE2: "\<And>obj p. \<lbrakk> kheap s p = Some obj; live obj \<rbrakk>
                        \<Longrightarrow> p \<notin> untyped_range cap"
    by (simp add: live_okE[where P=live] obj_at_def)
  have untyped_mdb : "\<And>m. untyped_mdb m (caps_of_state s)
                      \<Longrightarrow> untyped_mdb m (\<lambda>p. if fst p \<in> untyped_range cap then None else caps_of_state s p)"
    apply (simp only: untyped_mdb_def)
    apply (elim allEI)
    apply clarsimp
    done
  have untyped_inc : "\<And>m. untyped_inc m (caps_of_state s)
                      \<Longrightarrow> untyped_inc m (\<lambda>p. if fst p \<in> untyped_range cap then None else caps_of_state s p)"
    apply (simp only: untyped_inc_def)
    apply (elim allEI)
    apply clarsimp
    done
  have reply_caps_mdb : "\<And>m. reply_caps_mdb m (caps_of_state s)
                         \<Longrightarrow> reply_caps_mdb m (\<lambda>p. if fst p \<in> untyped_range cap then None else caps_of_state s p)"
    apply (simp only: reply_caps_mdb_def)
    apply (elim allEI)
    apply (clarsimp elim!: exEI)
    apply (fastforce dest: non_null_caps)
    done
  have reply_masters_mdb : "\<And>m. reply_masters_mdb m (caps_of_state s)
                            \<Longrightarrow> reply_masters_mdb m (\<lambda>p. if fst p \<in> untyped_range cap then None else caps_of_state s p)"
    apply (simp only: reply_masters_mdb_def)
    apply (elim allEI)
    apply clarsimp
    apply (drule(1) bspec)
    apply (fastforce dest: non_null_caps)
    done
  have reply_mdb : "\<And>m. reply_mdb m (caps_of_state s)
                    \<Longrightarrow> reply_mdb m (\<lambda>p. if fst p \<in> untyped_range cap then None else caps_of_state s p)"
    by (simp add: reply_mdb_def reply_caps_mdb reply_masters_mdb)
  show "valid_mdb (detype (untyped_range cap) s)"
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
    done
  show "untyped_children_in_mdb (detype (untyped_range cap) s)"
    apply (insert child)
    apply (simp add: untyped_children_in_mdb_def)
    apply (erule allEI)+
    apply (clarsimp simp: detype_def)
    done
  show "if_live_then_nonz_cap (detype (untyped_range cap) s)"
    apply (insert iflive)
    apply (simp add: if_live_then_nonz_cap_def ex_nonz_cap_to_def)
    apply (erule allEI)
    apply (rule impI, erule conjE, drule(1) mp)
    apply (erule exEI)
    apply clarsimp
    apply (frule non_null_present [OF cte_wp_at_weakenE])
     apply clarsimp+
    done
  have irq_node_detype[simp]:
    "\<And>r. interrupt_irq_node (detype r s) = interrupt_irq_node s"
    by (simp add: detype_def)
  show "if_unsafe_then_cap (detype (untyped_range cap) s)"
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
  have zombies_final: "zombies_final s"
    using invs by (simp add: invs_def valid_state_def valid_pspace_def)
  show "zombies_final (detype (untyped_range cap) s)"
    apply (insert zombies_final)
    apply (simp add: zombies_final_def final_cap_at_eq)
    apply (elim allEI)
    apply (rule impI, erule conjE, drule(1) mp)
    apply (elim exEI conjE conjI allEI)
    apply (rule impI, elim conjE)
    apply simp
    done
  have idle: "idle_thread (detype (untyped_range cap) s) = idle_thread s"
    by (simp add: detype_def)
  have "valid_idle s" using invs by (simp add: invs_def valid_state_def)
  thus "valid_idle (detype (untyped_range cap) s)"
    using valid_global_refsD [OF globals cap]
    by (fastforce simp add: valid_idle_def state_refs idle cap_range_def
                            global_refs_def)
  have glob_det[simp]: "\<And>r. global_refs (detype r s) = global_refs s"
    by (simp add: global_refs_def detype_def)
  show "valid_global_refs (detype (untyped_range cap) s)"
    using globals
    by (simp add: valid_global_refs_def valid_refs_def)
  have arch_state_det[simp]: "\<And>r. arch_state (detype r s) = arch_state s"
    by (simp add: detype_def)
  have valid_arch_caps: "valid_arch_caps s"
    using invs by (simp add: invs_def valid_state_def)
  have valid_vs_lookup: "valid_vs_lookup s"
    using valid_arch_caps by (simp add: valid_arch_caps_def)
  moreover
  have valid_arch_state: "valid_arch_state s" using invs
    by clarsimp
  moreover
  have ut_mdb: "untyped_mdb (cdt s) (caps_of_state s)"
    using invs
    by (clarsimp dest!: invs_mdb simp add: valid_mdb_def)
  ultimately
  show "valid_arch_state (detype (untyped_range cap) s)"
    using valid_global_refsD [OF globals cap] cap
    apply (simp add: valid_arch_state_def valid_asid_table_def
                  valid_global_pts_def global_refs_def
                  cap_range_def)
    apply (clarsimp simp: ran_def)
    apply (drule vs_lookup_atI)
    apply (drule (1) valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI])
    apply (clarsimp simp: cte_wp_at_caps_of_state)
    apply (drule untyped_mdbD, rule untyped, assumption)
      apply blast
     apply assumption
    apply (drule descendants_range_inD[OF drange])
      apply (simp add:cte_wp_at_caps_of_state)
    apply (simp add:cap_range_def)
    apply blast
    done

  show "valid_reply_caps (detype (untyped_range cap) s)"
    using vreply
    apply (clarsimp simp: valid_reply_caps_def has_reply_cap_def)
    apply (rule conjI)
     apply (erule allEI)
     apply (rule impI)
     apply (elim impE exE conjE, intro exI, assumption)
     apply (simp add: st_tcb_at_def)
     apply (fastforce dest: live_okE)
    apply (clarsimp simp: unique_reply_caps_def)
    done
  show "valid_irq_node (detype (untyped_range cap) s)"
    using invs valid_globals_irq_node [OF globals cap]
    by (simp add: valid_irq_node_def invs_def valid_state_def cap_range_def)
  show "valid_reply_masters (detype (untyped_range cap) s)"
    using vmaster by (clarsimp simp: valid_reply_masters_def)
  show "valid_irq_handlers (detype (untyped_range cap) s)"
    using invs
    apply (simp add: valid_irq_handlers_def ran_def irq_issued_def
                     invs_def valid_state_def)
    apply (force simp: detype_def)
    done

  from valid_global_refsD [OF globals cap]
  have global_pts:
    "\<And>p. \<lbrakk> p \<in> set (arm_global_pts (arch_state s)); p \<in> untyped_range cap \<rbrakk> \<Longrightarrow> False"
    by (simp add: cap_range_def global_refs_def)

  have vs_lookup [simp]: 
    "vs_lookup (detype (untyped_range cap) s) = vs_lookup s"
    apply (rule set_eqI)
    apply clarsimp
    apply (rule iffI)
     apply (erule vs_lookup_induct)
      apply simp
      apply (erule vs_lookup_atI)
     apply (erule vs_lookup_step)
     apply (clarsimp simp: vs_lookup1_def)
    apply (erule vs_lookup_induct)
     apply (rule vs_lookup_atI)
     apply simp
    apply (erule vs_lookup_step)
    apply (clarsimp simp: vs_lookup1_def)
    apply (drule valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI], rule valid_vs_lookup)
    apply (elim conjE exE)
    apply (insert cap)
    apply (simp add: cte_wp_at_caps_of_state)
    apply (drule untyped_mdbD, rule untyped, assumption)
      apply blast
     apply (rule ut_mdb)
    apply (drule descendants_range_inD[OF drange])
      apply (simp add:cte_wp_at_caps_of_state)
    apply (simp add:cap_range_def)
    apply blast
    done

  have vs_lookup_pages [simp]: 
    "vs_lookup_pages (detype (untyped_range cap) s) = vs_lookup_pages s"
    apply (rule set_eqI)
    apply clarsimp
    apply (rule iffI)
     apply (erule vs_lookup_pages_induct)
      apply simp
      apply (erule vs_lookup_pages_atI)
     apply (erule vs_lookup_pages_step)
     apply (clarsimp simp: vs_lookup_pages1_def)
    apply (erule vs_lookup_pages_induct)
     apply (rule vs_lookup_pages_atI)
     apply simp
    apply (erule vs_lookup_pages_step)
    apply (clarsimp simp: vs_lookup_pages1_def)
    apply (drule valid_vs_lookupD, rule valid_vs_lookup)
    apply (elim conjE exE)
    apply (insert cap)
    apply (simp add: cte_wp_at_caps_of_state)
    apply (drule untyped_mdbD, rule untyped, assumption)
      apply blast
     apply (rule ut_mdb)
    apply (drule descendants_range_inD[OF drange])
      apply (simp add:cte_wp_at_caps_of_state)
    apply (simp add:cap_range_def)
    apply blast
    done

  from cap untyped
  have no_obj_refs:
    "\<And>slot cap' x. \<lbrakk> caps_of_state s slot = Some cap'; 
                     x \<in> obj_refs cap'; x \<in> untyped_range cap \<rbrakk> \<Longrightarrow> False"
    apply (clarsimp simp: cte_wp_at_caps_of_state)
    apply (drule (2) untyped_mdbD)
      apply blast
     apply (rule ut_mdb)
    apply (drule descendants_range_inD[OF drange])
      apply (simp add:cte_wp_at_caps_of_state)
    apply (simp add:cap_range_def)
    apply blast
    done

  have vs_lookup_preserved:
    "\<And>x rf. \<lbrakk> x \<in> untyped_range cap; (rf \<rhd> x) s \<rbrakk> \<Longrightarrow> False"
    apply (drule valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI valid_vs_lookup])
    apply (fastforce intro: global_pts no_obj_refs)
    done

  have vs_lookup_pages_preserved:
    "\<And>x rf. \<lbrakk> x \<in> untyped_range cap; (rf \<unrhd> x) s \<rbrakk> \<Longrightarrow> False"
    apply (drule valid_vs_lookupD[OF _ valid_vs_lookup])
    apply (fastforce intro: global_pts no_obj_refs)
    done

  (* FIXME: This is really horrible but I can't get the automated methods
            to "get it". *)
  have valid_arch_obj:
    "\<And>ao p. \<lbrakk> valid_arch_obj ao s; ko_at (ArchObj ao) p s; (\<exists>\<rhd>p) s \<rbrakk> \<Longrightarrow>
         valid_arch_obj ao (detype (untyped_range cap) s)"
    apply (case_tac ao)
       apply (clarsimp simp: ran_def)
       apply (erule vs_lookup_preserved)
       apply (erule vs_lookup_step)
       apply (erule vs_lookup1I[OF _ _ refl])
       apply (simp add: vs_refs_def)
       apply (rule image_eqI[rotated])
        apply (erule graph_ofI)
       apply fastforce
      apply clarsimp
      apply (erule_tac x=x in allE)
      apply (case_tac "fun x", simp_all)[1]
       apply (drule_tac p'="(Platform.ptrFromPAddr word)" in vs_lookup_pages_step[OF vs_lookup_pages_vs_lookupI])
        apply (clarsimp simp: vs_lookup_pages1_def)
        apply (rule exI, erule conjI)
        apply (rule_tac x="VSRef (ucast x) (Some APageTable)" in exI)
        apply (rule conjI[OF refl])
        apply (clarsimp simp: vs_refs_pages_def graph_of_def pte_ref_pages_def)
        apply (rule_tac x="(x, (Platform.ptrFromPAddr word))" in image_eqI)
         apply (simp add: split_def) 
        apply simp
       apply (force dest!: vs_lookup_pages_preserved)
      apply (drule_tac p'="(Platform.ptrFromPAddr word)" in vs_lookup_pages_step[OF vs_lookup_pages_vs_lookupI])
       apply (clarsimp simp: vs_lookup_pages1_def)
       apply (rule exI, erule conjI)
       apply (rule_tac x="VSRef (ucast x) (Some APageTable)" in exI)
       apply (rule conjI[OF refl])
       apply (clarsimp simp: vs_refs_pages_def graph_of_def pte_ref_pages_def)
       apply (rule_tac x="(x, (Platform.ptrFromPAddr word))" in image_eqI)
        apply (simp add: split_def) 
       apply simp
      apply (force dest!: vs_lookup_pages_preserved)
     apply clarsimp
     apply (case_tac "fun x", simp_all)[1]
       apply (drule bspec, simp)
       apply (clarsimp simp: valid_pde_def)
       apply (drule_tac p'="(Platform.ptrFromPAddr word1)" in vs_lookup_pages_step[OF vs_lookup_pages_vs_lookupI])
       apply (clarsimp simp: vs_lookup_pages1_def)
        apply (rule exI, erule conjI)
        apply (rule_tac x="VSRef (ucast x) (Some APageDirectory)" in exI)
        apply (rule conjI[OF refl])
        apply (clarsimp simp: vs_refs_pages_def graph_of_def pde_ref_pages_def)
        apply (rule_tac x="(x, (Platform.ptrFromPAddr word1))" in image_eqI)
         apply (simp add: split_def) 
        apply (simp add: pde_ref_pages_def)
       apply (force dest!: vs_lookup_pages_preserved)
      apply (drule_tac p'="(Platform.ptrFromPAddr word1)" in vs_lookup_pages_step[OF vs_lookup_pages_vs_lookupI])
       apply (clarsimp simp: vs_lookup_pages1_def)
       apply (rule exI, erule conjI)
       apply (rule_tac x="VSRef (ucast x) (Some APageDirectory)" in exI)
       apply (rule conjI[OF refl])
       apply (clarsimp simp: vs_refs_pages_def graph_of_def pde_ref_pages_def)
       apply (rule_tac x="(x, (Platform.ptrFromPAddr word1))" in image_eqI)
        apply (simp add: split_def) 
       apply (simp add: pde_ref_pages_def)
      apply (force dest!: vs_lookup_pages_preserved)
      apply (drule_tac p'="(Platform.ptrFromPAddr word)" in vs_lookup_pages_step[OF vs_lookup_pages_vs_lookupI])
       apply (clarsimp simp: vs_lookup_pages1_def)
       apply (rule exI, erule conjI)
       apply (rule_tac x="VSRef (ucast x) (Some APageDirectory)" in exI)
       apply (rule conjI[OF refl])
       apply (clarsimp simp: vs_refs_pages_def graph_of_def pde_ref_pages_def)
       apply (rule_tac x="(x, (Platform.ptrFromPAddr word))" in image_eqI)
        apply (simp add: split_def) 
       apply (simp add: pde_ref_pages_def)
      apply (force dest!: vs_lookup_pages_preserved)
     apply clarsimp
    done

  have "valid_arch_objs s"
    using invs by fastforce 
  thus "valid_arch_objs (detype (untyped_range cap) s)"
    unfolding valid_arch_objs_def
    apply (simp add: vs_lookup)
    apply (auto intro: valid_arch_obj)
    done

  have "executable_arch_objs s"
    using invs by fastforce 
  thus "executable_arch_objs (detype (untyped_range cap) s)"
    unfolding executable_arch_objs_def
    apply (auto)
    done

  have unique_table_caps:
    "\<And>cps P. unique_table_caps cps
             \<Longrightarrow> unique_table_caps (\<lambda>x. if P x then None else cps x)"
    by (simp add: unique_table_caps_def)

  have unique_table_refs:
    "\<And>cps P. unique_table_refs cps
             \<Longrightarrow> unique_table_refs (\<lambda>x. if P x then None else cps x)"
    apply (simp only: unique_table_refs_def option.simps
                      simp_thms
               split: split_if)
    apply blast
    done

  have valid_vs_lookup:
    "valid_vs_lookup s \<Longrightarrow> valid_vs_lookup (detype (untyped_range cap) s)"
    apply (simp add: valid_vs_lookup_def del: split_paired_Ex)
    apply (elim allEI)
    apply (intro disjCI2 impI)
    apply (drule(1) mp)+
    apply (elim conjE)
    apply (erule exEI)
    apply clarsimp
    apply (drule non_null_caps)
     apply clarsimp+
    done

  have valid_table_caps:
    "valid_table_caps s \<Longrightarrow> valid_table_caps (detype (untyped_range cap) s)"
    apply (simp add: valid_table_caps_def del: imp_disjL)
    apply (elim allEI | rule impI)+
    apply clarsimp 
    apply (erule(2) no_obj_refs)
    done

  have valid_arch_caps: "valid_arch_caps s"
    using invs by (clarsimp simp: invs_def valid_state_def)
  thus "valid_arch_caps (detype (untyped_range cap) s)"
    by (simp add: valid_arch_caps_def
                  unique_table_caps valid_vs_lookup
                  unique_table_refs
                  valid_table_caps)

  have pd_at_global_pd: "page_directory_at (arm_global_pd (arch_state s)) s"
    using valid_arch_state by (simp add: valid_arch_state_def)

  have valid_global_objs: "valid_global_objs s"
    using invs by (clarsimp simp: invs_def valid_state_def)
  thus "valid_global_objs (detype (untyped_range cap) s)"
    using valid_global_refsD [OF globals cap]
    apply (simp add: valid_global_objs_def valid_ao_at_def)
    apply (elim conjE, intro conjI)
       apply (simp add: global_refs_def cap_range_def)
      apply (erule exEI)
      apply (insert pd_at_global_pd)[1]
      apply (clarsimp simp: obj_at_def a_type_simps empty_table_def)
     apply (simp add: global_refs_def cap_range_def)
    apply (clarsimp elim!: global_pts)
    done

  have "valid_kernel_mappings s"
    using invs by (simp add: invs_def valid_state_def)
  thus "valid_kernel_mappings (detype (untyped_range cap) s)"
    by (simp add: valid_kernel_mappings_def detype_def
                  ball_ran_eq)

  have "valid_asid_map s"
    using invs by (simp add: invs_def valid_state_def)
  thus "valid_asid_map (detype (untyped_range cap) s)"
    apply (clarsimp simp: valid_asid_map_def)
    apply (drule bspec, blast)
    apply (clarsimp simp: pd_at_asid_def)
    done

  have "only_idle s"
    using invs by (simp add: invs_def valid_state_def)
  thus "only_idle (detype (untyped_range cap) s)"
    apply (clarsimp simp: only_idle_def)
    apply (simp add: detype_def)
    done

  have "equal_kernel_mappings s"
    using invs by (simp add: invs_def valid_state_def)
  thus "equal_kernel_mappings (detype (untyped_range cap) s)"
    apply (simp add: equal_kernel_mappings_def)
    apply blast
    done

  have "valid_global_pd_mappings s"
    using invs by (simp add: invs_def valid_state_def)
  thus "valid_global_pd_mappings (detype (untyped_range cap) s)"
    using valid_global_refsD [OF globals cap] valid_global_objs
    apply -
    apply (erule valid_global_pd_mappings_pres, simp_all)
     apply (simp add: cap_range_def global_refs_def)+
    done

  have "pspace_in_kernel_window s"
    using invs by (simp add: invs_def valid_state_def)
  thus "pspace_in_kernel_window (detype (untyped_range cap) s)"
    apply (simp add: pspace_in_kernel_window_def)
    apply fastforce
    done
    
  have "cap_refs_in_kernel_window s"
    using invs by (simp add: invs_def valid_state_def)
  thus "cap_refs_in_kernel_window (detype (untyped_range cap) s)"
    apply (simp add: cap_refs_in_kernel_window_def
                     valid_refs_def)
    done

  have "valid_ioc s" using invs by (simp add: invs_def valid_state_def)
  thus "valid_ioc (detype (untyped_range cap) s)"
    apply (simp add: valid_ioc_def)
    apply (clarsimp simp: detype_def neq_commute)
    apply (drule spec, drule spec, erule impE, assumption)
    apply (frule_tac p="(a,b)" in non_null_present[simplified neq_commute])
    apply simp
    done

  have cap_is_valid: "valid_cap cap s"
    by (rule cte_wp_valid_cap[OF local.cap invs_valid_objs[OF invs]])

  (* FIXME: consider to source out. *)
  have p2pm1_to_mask[simp]: "\<And>p n. p + 2 ^ n - 1 = p + mask n"
    by (simp add: mask_2pm1 field_simps)

  from invs have valid_pspace: "valid_pspace s"
    by (simp add: invs_def valid_state_def)

  from invs have "valid_machine_state s" by (simp add: invs_def valid_state_def)
  thus "valid_machine_state
          (clear_um (untyped_range cap) (detype (untyped_range cap) s))"
    apply (clarsimp simp: valid_machine_state_def clear_um_def detype_def)
    apply (drule_tac x=p in spec, simp add: in_user_frame_def obj_at_def)
    apply (elim exEI exE conjE, simp)
    apply (frule valid_pspace_aligned[OF valid_pspace])
    apply (drule_tac ptr'=p in mask_in_range)
    apply (case_tac ko, simp_all add: a_type_simps split: split_if_asm)
    apply (case_tac arch_kernel_obj, simp_all add: a_type_simps)
    apply clarsimp
    using untyped cap_is_valid
    apply (case_tac cap, simp_all)
    apply (clarsimp simp add: valid_cap_def cap_aligned_def valid_untyped_def)
    apply (drule_tac x="p && ~~ mask (pageBitsForSize x)" in spec)
    apply (auto simp add: obj_range_def)
    done

  from invs have "valid_irq_states s" by (simp add: invs_def valid_state_def)
  thus "valid_irq_states
          (clear_um (untyped_range cap) (detype (untyped_range cap) s))"
    apply(clarsimp simp: clear_um_def detype_def valid_irq_states_def)
    done
qed

end


lemma detype_invariants:
  assumes cap: "cte_wp_at (op = cap) ptr s"
  and untyped: "is_untyped_cap cap"
  and  drange: "descendants_range cap ptr s"
  and    invs: "invs s"
  and   child: "untyped_children_in_mdb s"
  and  ct_act: "ct_active s"
  and  vreply: "valid_reply_caps s"
  and vmaster: "valid_reply_masters s"
  shows        "(invs and untyped_children_in_mdb)
                  (detype (untyped_range cap) (clear_um (untyped_range cap) s))"
  apply (rule_tac ptr=ptr in detype_locale.invariants)
   apply (unfold detype_locale_def, simp_all add: assms)
  done

(* FIXME: taken from Retype_C.thy and adapted wrt. the missing intvl syntax. *)
lemma mapM_x_storeWord:
  assumes al: "is_aligned ptr 2"
  shows "mapM_x (\<lambda>x. storeWord (ptr + of_nat x * 4) 0) [0..<n]
  = modify (underlying_memory_update
             (\<lambda>m x. if \<exists>k. x = ptr + of_nat k \<and> k < n * 4 then 0 else m x))"
proof (induct n)
  case 0
  thus ?case
    apply (rule ext)
    apply (simp add: mapM_x_mapM mapM_def sequence_def 
      modify_def get_def put_def bind_def return_def)
    done
next
  case (Suc n')

  have funs_eq:
    "\<And>m x. (if \<exists>k. x = ptr + of_nat k \<and> k < 4 + n' * 4 then 0
             else (m x :: word8)) =
           ((\<lambda>xa. if \<exists>k. xa = ptr + of_nat k \<and> k < n' * 4 then 0 else m xa)
           (ptr + of_nat n' * 4 := word_rsplit (0 :: word32) ! 3,
            ptr + of_nat n' * 4 + 1 := word_rsplit (0 :: word32) ! 2,
            ptr + of_nat n' * 4 + 2 := word_rsplit (0 :: word32) ! Suc 0,
            ptr + of_nat n' * 4 + 3 := word_rsplit (0 :: word32) ! 0)) x"
  proof -
    fix m x
    
    have xin': "\<And>x. (x < 4 + n' * 4) = (x < n' * 4 \<or> x = n' * 4
                     \<or> x = (n' * 4) + 1 \<or> x = (n' * 4) + 2 \<or> x = (n' * 4) + 3)"
      by (safe, simp_all)

    have xin: "(EX k. x = ptr + of_nat k \<and> k < 4 + n' * 4) =
               ((\<exists>k. x = ptr + of_nat k \<and> k < n' * 4) \<or>
                x = ptr + of_nat n' * 4 \<or> x = ptr + of_nat n' * 4 + 1 \<or>
                x = ptr + of_nat n' * 4 + 2 \<or> x = ptr + of_nat n' * 4 + 3)"
      by (simp add: xin' conj_disj_distribL ex_disj_distrib field_simps)
  
    show "?thesis m x" by (simp add: xin word_rsplit_0 cong: if_cong)
  qed

  from al have "is_aligned (ptr + of_nat n' * 4) 2"
    apply (rule aligned_add_aligned)
    apply (rule is_aligned_mult_triv2 [where n = 2, simplified])
    apply (simp add: word_bits_conv)+
    done

  thus ?case
    apply (simp add: mapM_x_append bind_assoc Suc.hyps mapM_x_singleton)
    apply (simp add: storeWord_def assert_def is_aligned_mask modify_modify
                     comp_def)
    apply (simp only: funs_eq)
    done
qed


(* FIXME: move *)
lemma unat_mask:
  "unat (mask n :: 'a :: len word) = 2 ^ (min n (len_of TYPE('a))) - 1"
  apply (subst min.commute)
  apply (simp add: mask_def not_less min_def  split: split_if_asm)
  apply (intro conjI impI)
   apply (simp add: unat_sub_if_size)
   apply (simp add: power_overflow word_size)
  apply (simp add: unat_sub_if_size)
  done


(* FIXME: move *)
lemmas unat_mask_word32 = unat_mask[where 'a=32, folded word_bits_def]


lemma Suc_unat_mask_div:
  "Suc (unat (mask sz div word_size::word32)) = 2 ^ (min sz word_bits - 2)"
  apply (case_tac "sz < word_bits")
   apply (case_tac "2\<le>sz")
    apply (clarsimp simp: word_size_def word_bits_def min_def mask_def)
    apply (drule (2) Suc_div_unat_helper
           [where 'a=32 and sz=sz and us=2, simplified, symmetric])
   apply (simp add: not_le word_size_def word_bits_def)
   apply (case_tac sz, simp add: unat_word_ariths)
   apply (case_tac nat, simp add: unat_word_ariths
                                  unat_mask_word32 min_def word_bits_def)
   apply simp
  apply (simp add: unat_word_ariths
                   unat_mask_word32 min_def word_bits_def word_size_def)
  done

(* FIXME: move *)
lemma word_div_0: "(0::'a::len word) div x = 0"
  by (simp add: word_arith_nat_div)

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
    apply (rule arg_cong2[where f=bind, OF refl], rule ext)
    apply (simp add: empty_fail_def select_f_walk[OF empty_fail_modify]
                     modify_modify detype_msu_independent)
    done
qed

(* FIXME: move *)
lemma empty_fail_freeMemory: "empty_fail (freeMemory ptr bits)"
  by (simp add: freeMemory_def mapM_x_mapM ef_storeWord)


lemma delete_objects_def2:
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


lemma region_in_kernel_window_detype[simp]:
  "region_in_kernel_window S (detype S' s)
      = region_in_kernel_window S s"
  by (simp add: region_in_kernel_window_def detype_def)


lemma region_in_kernel_window_machine_state_update[simp]:
  "region_in_kernel_window S (machine_state_update f s) =
   region_in_kernel_window S s"
  by (simp add: region_in_kernel_window_def)


lemma region_in_kernel_window_delete_objects[wp]:
  "\<lbrace>region_in_kernel_window S\<rbrace>
   delete_objects ptr bits
   \<lbrace>\<lambda>_. region_in_kernel_window S\<rbrace>"
  by (wp | simp add: delete_objects_def do_machine_op_def split_def)+


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

(* FIXME: move, fix underlying -1 problem *)
lemma maxword_32_conv: "(x::32 word) + 0xFFFFFFFF = x - 1" by simp

(* FIXME: copied from Retype_C and slightly adapted. *)
lemma mapM_x_storeWord_step:
  assumes al: "is_aligned ptr sz"
  and    sz2: "2 \<le> sz"
  and     sz: "sz <= word_bits"
  shows "mapM_x (\<lambda>p. storeWord p 0) [ptr , ptr + 4 .e. ptr + 2 ^ sz - 1] = 
  modify (underlying_memory_update
    (\<lambda>m x. if x \<in> {x. \<exists>k. x = ptr + of_nat k \<and> k < 2 ^ sz} then 0 else m x))"
  using al sz
  apply (simp only: upto_enum_step_def field_simps cong: if_cong)
  apply (subst if_not_P)
   apply (subst not_less)
   apply (erule is_aligned_no_overflow)
  apply (simp add: mapM_x_map comp_def upto_enum_word maxword_32_conv del: upt.simps)
  apply (simp add:Suc_unat_mask_div[simplified mask_2pm1 word_size_def] min_def)
  apply (subst mapM_x_storeWord) 
   apply (erule is_aligned_weaken [OF _ sz2])
  apply (rule arg_cong)
  apply (subgoal_tac "2^2 = (4::nat)")
   apply (cut_tac power_add[symmetric,of "2::nat" "sz - 2" 2])
   apply (simp only: le_add_diff_inverse2[OF sz2])   
  apply simp
  done


lemma mapM_storeWord_clear_um:
  "is_aligned p n \<Longrightarrow> 2\<le>n \<Longrightarrow> n<=word_bits \<Longrightarrow>
   do_machine_op (mapM_x (\<lambda>p. storeWord p 0) [p, p + 4 .e. p + 2 ^ n - 1]) =
   modify (clear_um {x.  \<exists>k. x = p + of_nat k \<and> k < 2 ^ n})"
  apply (simp add: mapM_x_storeWord_step)
  apply (rule ext)
  apply (simp add: do_machine_op_def select_f_def split_def simpler_modify_def
                   simpler_gets_def bind_def return_def clear_um_def)
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


lemma clb_is_16:
  "2 ^ cte_level_bits = (16 :: word32)" by (simp add: cte_level_bits_def)


lemmas cte_wp_at_cte_at = cte_wp_at_weakenE [OF _ TrueI]


lemma cte_wp_at_domI:
  "cte_wp_at P c s \<Longrightarrow> fst c \<in> dom (kheap s)"
  by (auto elim: cte_wp_atE)


lemmas cte_wp_at_casesE [consumes 1, case_names CapTable TCB] = cte_wp_atE


lemma dom_known_length:
  "\<lbrakk> dom f = {x. length x = n}; f xs = Some cap \<rbrakk> \<Longrightarrow> n = length xs"
  by (drule domI[where m=f], simp)


lemma of_bl_length2:
  "length xs < word_bits - cte_level_bits \<Longrightarrow> of_bl xs * 16 < (2 :: word32) ^ (length xs + 4)"
  apply (simp add: power_add)
  apply (rule word_mult_less_mono1)
    apply (rule of_bl_length, simp add: word_bits_def)
   apply simp
  apply simp
  apply (simp add: word_bits_def cte_level_bits_def)
  apply (rule order_less_le_trans)
   apply (erule power_strict_increasing)
   apply simp
  apply simp
  done


lemma cte_map_not_null_outside:
  "\<lbrakk> cte_wp_at (op \<noteq> cap.NullCap) p s; cte_wp_at (op = cap) p' s;is_untyped_cap cap;
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
     corres_underlying ssr nf rvr P P' x x'\<rbrakk>
   \<Longrightarrow> corres_underlying sr nf rvr (g and P o f) (g' and P' o f') (fn x) (fn' x')"
  apply (subst submonad.fn_is_sm, assumption)+
  apply (clarsimp simp: submonad_fn_def)
  apply (rule corres_split' [OF _ _ stateAssert_sp stateAssert_sp])
   apply (fastforce simp: corres_underlying_def stateAssert_def get_def
                         assert_def return_def bind_def)
  apply (rule corres_split' [where r'="\<lambda>x y. (x, y) \<in> ssr",
                             OF _ _ gets_sp gets_sp])
   apply (clarsimp simp: corres_gets)
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
    corres_underlying ssr nf rvr P P' x x'\<rbrakk>
   \<Longrightarrow> corres_underlying sr nf rvr G G' (fn x) (fn' x')"
  apply (subst submonad.fn_is_sm, assumption)+
  apply (clarsimp simp: submonad_fn_def)
  apply (rule corres_split' [OF _ _ stateAssert_sp stateAssert_sp])
   apply (fastforce simp: corres_underlying_def stateAssert_def get_def
                         assert_def return_def bind_def)
  apply (rule corres_split' [where r'="\<lambda>x y. (x, y) \<in> ssr",
                             OF _ _ gets_sp gets_sp])
   apply (clarsimp simp: corres_gets)
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

lemma delete_objects_invs[wp]:
  "\<lbrace>(\<lambda>s. \<exists>slot. cte_wp_at (op = (cap.UntypedCap ptr bits f)) slot s
    \<and> descendants_range (cap.UntypedCap ptr bits f) slot s) and
    invs and ct_active\<rbrace>
    delete_objects ptr bits \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: delete_objects_def)
  apply (simp add: freeMemory_def word_size_def bind_assoc
                   empty_fail_mapM_x ef_storeWord)
   apply (rule hoare_pre)
   apply (rule_tac G="is_aligned ptr bits \<and> 2 \<le> bits \<and> bits \<le> word_bits"
                in hoare_grab_asm)
   apply (simp add:mapM_storeWord_clear_um intvl_range_conv[where 'a=32, folded word_bits_def])
   apply wp
  apply clarsimp
  apply (frule invs_untyped_children)
  apply (frule detype_invariants, clarsimp+)
  apply (drule invs_valid_objs)
  apply (drule (1) cte_wp_valid_cap)
  apply (simp add: valid_cap_def cap_aligned_def)
  done


lemma dmo_valid_cap[wp]:
  "\<lbrace>\<lambda>s. s \<turnstile> cap.UntypedCap base magnitude idx\<rbrace>
   do_machine_op f
   \<lbrace>\<lambda>rv s. s \<turnstile> cap.UntypedCap base magnitude idx\<rbrace>"
  by (simp add: do_machine_op_def split_def | wp)+


lemma cte_map_not_null_outside':
  "\<lbrakk>cte_wp_at (op = (cap.UntypedCap q n m)) p' s;
    descendants_range (cap.UntypedCap q n m) p' s; untyped_children_in_mdb s;
    if_unsafe_then_cap s; valid_global_refs s;
    cte_wp_at (op \<noteq> cap.NullCap) p s\<rbrakk>
   \<Longrightarrow> fst p \<notin> untyped_range (cap.UntypedCap q n m)"
  by (erule (1) cte_map_not_null_outside, simp_all)

lemma refl_spec[simp]:
  "\<not> (\<forall>x. x \<noteq> y)"
  by clarsimp

lemma pre_helper:
  "\<And>base x n. \<lbrakk> is_aligned (base :: word32) (n + 4); n + 4 < word_bits \<rbrakk>
  \<Longrightarrow> base + (x && mask n) * 16 \<in> {base .. base + 2 ^ (n + 4) - 1}"
    apply (subgoal_tac "(x && mask n) * 0x10 < 2 ^ (n + 4)")
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
     apply simp
    apply (simp add: word_bits_def)
    apply (drule power_strict_increasing[where a="2 :: nat"], simp_all)
    done


lemma pre_helper2:
    "\<And>base x n. \<lbrakk> is_aligned (base :: word32) n; n < word_bits; 2 \<le> n; x < 2 ^ (n - 2) \<rbrakk>
             \<Longrightarrow> base + x * 4 \<in> {base .. base + 2 ^ n  - 1}"
    apply (subgoal_tac "x * 4 < 2 ^ n")
     apply simp
     apply (rule context_conjI)
      apply (erule(1) is_aligned_no_wrap')
     apply (subst add_diff_eq[symmetric])
     apply (rule word_plus_mono_right)
      apply simp
     apply (erule is_aligned_no_wrap')
     apply simp
    apply (drule word_mult_less_mono1[where k="2 ^ 2"])
      apply simp
     apply (subst unat_power_lower, simp add: word_bits_def)+
     apply (simp only: power_add[symmetric])
     apply (rule power_strict_increasing)
      apply (simp add: word_bits_def)
     apply simp
    apply (simp only: power_add[symmetric] le_add_diff_inverse2)
    apply simp
    done

lemmas ucast_ucast_mask_8 = ucast_ucast_mask[where 'a=8, simplified, symmetric]


lemma subset_eq_notI: "\<lbrakk>a\<in> B;a\<notin> C\<rbrakk> \<Longrightarrow> \<not> B \<subseteq> C" by auto


lemma pspace_no_overlap_obj_range:
  "\<lbrakk> pspace_no_overlap ptr sz s; kheap s p = Some obj; S \<subseteq> {ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1} \<rbrakk>
     \<Longrightarrow> obj_range p obj \<inter> S = {}"
  apply (simp add: pspace_no_overlap_def)
  apply (elim allE, drule(1) mp)
  apply (simp add: obj_range_def field_simps)
  apply fastforce
  done


lemma commute_grab_asm:
  "(F \<Longrightarrow> monad_commute P f g) \<Longrightarrow> (monad_commute (P and (K F)) f g)"
  by (clarsimp simp: monad_commute_def)


lemma pspace_no_overlapD3:
  "\<lbrakk>pspace_no_overlap ptr sz s;kheap s p = Some obj;is_aligned ptr sz\<rbrakk>
  \<Longrightarrow> obj_range p obj \<inter> {ptr..ptr + 2 ^ sz - 1} = {}"
  apply (unfold pspace_no_overlap_def)
  apply (drule spec)+
  apply (erule(1) impE)
  apply (simp only:is_aligned_neg_mask_eq obj_range_def p_assoc_help)
  done

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

lemma commute_name_pre_state:
assumes "\<And>s. P s \<Longrightarrow> monad_commute (op = s) f g"
shows "monad_commute P f g"
  using assms
  by (clarsimp simp:monad_commute_def)

lemma commute_rewrite:
assumes rewrite: "\<And>s. Q s \<Longrightarrow> f s = t s"
  and   hold  : "\<lbrace>P\<rbrace> g \<lbrace>\<lambda>x. Q\<rbrace>"
 shows  "monad_commute R t g \<Longrightarrow> monad_commute (P and Q and R) f g"
   apply (clarsimp simp:monad_commute_def bind_def split_def return_def)
   apply (drule_tac x = s in spec)
   apply (clarsimp simp:rewrite[symmetric])
    apply (intro conjI)
     apply (rule set_eqI)
     apply (rule iffI)
      apply clarsimp
      apply (rule bexI[rotated],assumption)
      apply (subst rewrite)
      apply (rule use_valid[OF _ hold])
     apply simp+
    apply (erule bexI[rotated],simp)
   apply clarsimp
   apply (rule bexI[rotated],assumption)
   apply (subst rewrite[symmetric])
    apply (rule use_valid[OF _ hold])
   apply simp+
   apply (erule bexI[rotated],simp)
  apply (intro iffI)
   apply clarsimp
   apply (rule bexI[rotated],assumption)
   apply simp
   apply (subst rewrite)
    apply (erule(1) use_valid[OF _ hold])
   apply simp
  apply (clarsimp)
  apply (drule bspec,assumption)
  apply clarsimp
  apply (metis rewrite use_valid[OF _ hold])
  done

lemma mapM_x_commute:
assumes commute:
  "\<And>r. monad_commute (P r) a (b r)"
and   single:
  "\<And>r x. \<lbrace>P r and K (f r \<noteq> f x) and P x\<rbrace> b x \<lbrace>\<lambda>v. P r \<rbrace>"
shows
  "monad_commute (\<lambda>s. (distinct (map f list)) \<and> (\<forall>r\<in> set list. P r s)) a (mapM_x b list)"
  apply (induct list)
   apply (clarsimp simp:mapM_x_Nil return_def bind_def monad_commute_def)
  apply (clarsimp simp:mapM_x_Cons)
  apply (rule monad_commute_guard_imp)
   apply (rule monad_commute_split)
     apply assumption
    apply (rule monad_commute_guard_imp[OF commute])
   apply assumption
   apply (wp hoare_vcg_ball_lift)
   apply (rule single)
  apply (clarsimp simp: image_def)
  apply auto
  done

lemma mask_sub: "n \<le> m \<Longrightarrow> mask m - mask n = mask m && ~~ mask n"
  apply (simp add: field_simps)
  apply (subst word_plus_and_or_coroll)
   apply (rule word_eqI,simp add:word_ops_nth_size)
  apply (rule word_eqI, simp add: word_ops_nth_size word_size)
  apply auto
  done


lemma  neg_mask_diff_bound:
  "sz'\<le> sz \<Longrightarrow>(ptr && ~~ mask sz') - (ptr && ~~ mask sz) \<le> 2 ^ sz - 2 ^ sz'"
  (is "_ \<Longrightarrow> ?lhs \<le> ?rhs")
proof -
  assume lt: "sz' \<le> sz"
  hence "?lhs = ptr && (mask sz && (~~ mask sz'))"
    apply (simp add: mask_out_sub_mask field_simps mask_and_mask min.absorb2)
    apply (simp add: mask_sub)
    apply (subst word_plus_and_or_coroll)
     apply (rule word_eqI, simp add: word_size word_ops_nth_size)
    apply (rule word_eqI, simp add: word_size word_ops_nth_size)
    apply auto
    done
  also have "\<dots> \<le> ?rhs" using lt
    apply (simp add: mask_sub[symmetric])
    apply (simp add: mask_def field_simps word_and_le1)
    done
  finally show ?thesis by simp
qed


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
   \<Longrightarrow> ptr  + ((1::word32) + of_nat n << us)  && ~~ mask sz = ptr && ~~ mask sz"
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


lemma monad_eq_split2: 
assumes eq: " g' s = g s"
assumes tail:"\<And>r s. Q r s \<Longrightarrow> f r s = f' r s"
and hoare:   "\<lbrace>P\<rbrace>g\<lbrace>\<lambda>r s. Q r s\<rbrace>" "P s"
shows "(g>>=f) s = (g'>>= f') s"
proof -
have pre: "\<And>aa bb. \<lbrakk>(aa, bb) \<in> fst (g s)\<rbrakk> \<Longrightarrow> Q aa bb"
  using hoare by (auto simp: valid_def)
show ?thesis
  apply (simp add:bind_def eq split_def image_def)
  apply (rule conjI)
   apply (rule set_eqI)
   apply (clarsimp simp:Union_eq)
   apply (metis pre surjective_pairing tail)
  apply (metis pre surjective_pairing tail)
  done
qed

lemma monad_eq_split_tail:
  "\<lbrakk>f = g;a s = b s\<rbrakk> \<Longrightarrow> (a >>= f) s = ((b >>= g) s)"
  by (simp add:bind_def)


lemma shift_distinct_helper:
  "\<lbrakk> (x :: 'a :: len word) < bound; y < bound; x \<noteq> y; x << n = y << n; n < len_of TYPE('a);
      bound - 1 \<le> 2 ^ ((len_of TYPE('a)) - n) - 1 \<rbrakk>
    \<Longrightarrow> P"
  apply (cases "n = 0")
   apply simp
  apply (drule word_plus_mono_right[where x=1])
   apply simp_all
   apply (subst word_le_sub1)
    apply (rule power_not_zero)
    apply simp
   apply simp
  apply (drule(1) order_less_le_trans)+
  apply (clarsimp simp: bang_eq)
  apply (drule_tac x="na + n" in spec)
  apply (simp add: nth_shiftl)
  apply (case_tac "na + n < len_of TYPE('a)", simp_all)
  apply safe
   apply (drule(1) nth_bounded)
    apply simp
   apply simp
  apply (drule(1) nth_bounded)
   apply simp
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
  apply (simp add:shiftr_div_2n' field_simps mult_div_cancel)
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


(* FIXME: move to GenericLib *)
lemma if3_fold2:
  "(if P then x else if Q then x else y) = (if P \<or> Q then x else y)" by simp

end
