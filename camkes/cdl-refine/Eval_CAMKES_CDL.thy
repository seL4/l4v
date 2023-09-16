(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Eval_CAMKES_CDL
imports
  "Policy_CAMKES_CDL"
  "DPolicy.Dpolicy"
  "Lib.FastMap"
  "Lib.RangeMap"
  "Lib.FP_Eval"
  "Lib.GenericTag"
begin

text \<open>
  Various helpers for the generated CAmkES-capDL integrity proofs that are
  produced from camkes-tool.

  The main integrity proofs proceed by more-or-less direct evaluation
  of the proof obligations in cdl_state_asids_to_policy__eval, etc.

  These proof obligations are nested @{const Ball} predicates that iterate
  over each object, cap, etc. in the generated capDL state.
\<close>

context begin interpretation Arch . (* FIXME: need this only to talk about ARM ASIDs *)

type_synonym asid_high = "7 word" (* FIXME: MOVE *)

section \<open>Generic policy labelling helpers\<close>

text \<open>Retrieve page tables mapped into a page directory. (AARCH32 only)\<close>
definition mapped_pts_of :: "cdl_heap \<Rightarrow> cdl_cap_map \<Rightarrow> cdl_object_id set"
  where
  "mapped_pts_of object_map pd_caps \<equiv>
      {pt_id. \<exists>pt \<in> ran pd_caps.
        case pt of FrameCap _ _ _ _ _ _ \<Rightarrow> False \<comment> \<open>ignore ARM section pages\<close>
                 | _ \<Rightarrow> pt_id \<in> cap_objects pt}"

text \<open>Retrieve frames mapped into a page directory. (AARCH32 only)\<close>
definition mapped_frames_of :: "cdl_heap \<Rightarrow> cdl_cap_map \<Rightarrow> cdl_object_id set"
  where
  "mapped_frames_of object_map pd_caps \<equiv>
      {frame_id.
         \<exists>pt_id \<in> mapped_pts_of object_map pd_caps.
           \<exists>frame \<in> ran (object_slots (the (object_map pt_id))).
             frame_id \<in> cap_objects frame}
    \<union> {section_id.
         \<exists>section \<in> ran pd_caps.
            case section of FrameCap _ _ _ _ _ _ \<Rightarrow> section_id \<in> cap_objects section
               | _ \<Rightarrow> False}"

text \<open>
  Resolve a schematic equality "{a, b, c, ...} = ?val", while checking
  that the LHS is a concrete set builder expression
\<close>
method assign_schematic_set =
  (((rule arg_cong[where f="insert _"])+)?, rule refl[where t="{}"])

text \<open>
  Resolve a schematic equality "(a = x \<and> b = y \<and> c = z \<and> \<dots>) = ?val",
  while checking that the LHS is a conjunction of equations
\<close>
method assign_schematic_eq_conjs =
  (((rule conj_cong[where P="_ = _", OF refl])+)?, rule refl[where t="_ = _"])

text \<open>
  Resolve a schematic equality of the form
  "((a1 = x1 \<and> a2 = x2 \<and> \<dots>) \<or> (b1 = y1 \<and> b2 = y2 \<and> \<dots>) \<or> \<dots>) = ?val",
  while ensuring that the LHS consists of equations in disjunctive normal form.
\<close>
method assign_schematic_dnf =
  (((rule disj_cong, assign_schematic_eq_conjs)+)?, assign_schematic_eq_conjs)

text \<open>Policy graph manipulation utils\<close>
lemma split_Collect_graph_edge:
  "Collect P = Collect (\<lambda>(from, auth, to). P (from, auth, to))"
  by simp

lemma Collect_graph_cong_helper:
  "(\<And>x y z. P x y z = P' x y z) \<Longrightarrow>
   Collect (\<lambda>(x, y, z). P x y z) = Collect (\<lambda>(x, y, z). P' x y z)"
  by simp

text \<open>
  VER-1030 forces us to create a huge number of (mostly spurious)
  DeleteDerived rights in @{const policy_of}. In fact, it forms a
  complete graph. We use that fact to help prove transitivity more
  efficiently.
\<close>
lemma proj_Collect_prod:
  "fst ` {(a, b). f a b} = {a. \<exists>b. f a b}"
  "snd ` {(a, b). f a b} = {b. \<exists>a. f a b}"
  by force+

lemma complete_graph_is_transitive[rotated 1, consumes 2]:
  "\<lbrakk> let edges = {(v, u). G v e u};
         verts = fst ` edges \<union> snd ` edges
     in \<forall>u \<in> verts. \<forall>v \<in> verts. G v e u;
     G u e v; G v e w \<rbrakk>
   \<Longrightarrow> G u e w"
  apply (simp (no_asm_use) add: proj_Collect_prod flip: Collect_disj_eq)
  by blast

(* version without self edges *)
lemma complete_graph_is_transitive'[rotated 1, consumes 2]:
  "\<lbrakk> let edges = {(v, u). G v e u};
         verts = fst ` edges \<union> snd ` edges
     in \<forall>u \<in> verts. \<forall>v \<in> verts. u \<noteq> v \<longrightarrow> G v e u;
     G u e v; G v e w; u \<noteq> v; v \<noteq> w; u \<noteq> w \<rbrakk>
   \<Longrightarrow> G u e w"
  apply (simp (no_asm_use) add: proj_Collect_prod flip: Collect_disj_eq)
  by blast

lemma Collect_case_prod_dnf:
  "{(a, b). a = x \<and> b = y} = {(x, y)}"
  "{(a, b). a = x \<and> b = y \<or> P a b} = insert (x, y) {(a, b). P a b}"
  "{(a, b). b = y \<and> a = x} = set [(x, y)]"
  "{(a, b). b = y \<and> a = x \<or> P a b} = insert (x, y) {(a, b). P a b}"
  by auto

text \<open>
  Simplified, automation-friendl(ier) intro for policy_wellformed, assuming that
  CAmkES never provides Grant auth across components, and we ignore components
  indirectly triggering interrupts.
\<close>

lemma camkes_policy_wellformedI:
  assumes "\<not>maySendIrqs"
      and "\<And>a. (agent, a, agent) \<in> aag"
      and "\<And>s auth r. (s, auth, r) \<in> aag \<Longrightarrow> (s, Control, s) \<in> aag"
      and "\<And>s r. (s, auth.Grant, r) \<in> aag \<Longrightarrow> s = r"
      and "\<And>s r. (s, Control, r) \<in> aag \<Longrightarrow> s = r"
      and "\<And>s auth. (s, Control, s) \<in> aag \<Longrightarrow> (s, auth, s) \<in> aag"
      and "\<And>s r. (s, Receive, r) \<in> aag \<Longrightarrow> s \<noteq> r \<Longrightarrow> (r, Control, r) \<in> aag \<Longrightarrow> False"
      and "\<And>s r. (s, Call, r) \<in> aag \<Longrightarrow> s \<noteq> r \<Longrightarrow> (r, Control, r) \<in> aag \<Longrightarrow> False"
      and "\<And>s ep. (s, Call, ep) \<in> aag \<Longrightarrow> (s, SyncSend, ep) \<in> aag"
      and "\<And>s r. (s, Reply, r) \<in> aag \<Longrightarrow> (r, DeleteDerived, s) \<in> aag"
      and "\<And>s r ep. (s, Call, ep) \<in> aag \<Longrightarrow> s \<noteq> ep \<Longrightarrow> (r, Receive, ep) \<in> aag
                     \<Longrightarrow> (r, Reply, s) \<in> aag"
      and "\<And>l1 l2 l3. (l1, DeleteDerived, l2) \<in> aag \<Longrightarrow> l1 \<noteq> l2 \<Longrightarrow>
                       (l2, DeleteDerived, l3) \<in> aag \<Longrightarrow> l1 \<noteq> l3 \<Longrightarrow> l2 \<noteq> l3 \<Longrightarrow>
                       (l1, DeleteDerived, l3) \<in> aag"
  shows "policy_wellformed aag maySendIrqs irqSet agent"
  unfolding policy_wellformed_def
  apply (insert assms)
  apply (safe; metis)
  done


section \<open>Word and pointer arithmetic helpers\<close>
lemma ptr_range_in_range:
  "0 < (p :: 'a::len word) + 2^sz \<Longrightarrow>
   (x \<in> ptr_range p sz) = (RangeMap.in_range (p, p + 2^sz) x)"
  apply (simp add: ptr_range_def RangeMap.in_range.simps)
  apply uint_arith
  done

lemma Collect_asid_high__eval_helper:
  "asid_high_bits_of ` {asid. fst (transform_asid asid) = asid_high \<and> asid \<noteq> 0} =
   (if asid_high < 2^asid_high_bits then {of_nat asid_high} else {})"
  (* cleanup... *)
  apply (case_tac "asid_high < 2^asid_high_bits")
   prefer 2
   apply (clarsimp simp: transform_asid_def asid_high_bits_of_def[abs_def])
   apply (erule contrapos_np)
   apply (subst arg_cong[where f="(<) _"])
    prefer 2
    apply (rule unat_lt2p)
   apply (simp add: asid_high_bits_def)
  apply (simp add: transform_asid_def asid_high_bits_of_def[abs_def])
  apply (rule set_eqI)
  apply (rule iffI)
   apply clarsimp
  apply (clarsimp simp: Collect_conj_eq image_iff)
  apply (rule_tac x="(of_nat asid_high << asid_low_bits) + 1" in bexI)
   apply (subst add.commute, subst shiftr_irrelevant)
     apply (clarsimp simp: asid_low_bits_def asid_high_bits_def)
    apply (clarsimp simp: is_aligned_shift)
   apply (subst shiftl_shiftr_id)
     apply (clarsimp simp: asid_low_bits_def asid_high_bits_def)
    apply (clarsimp simp: asid_low_bits_def asid_high_bits_def word_of_nat_less)
   apply (subst ucast_of_nat_small)
    apply (clarsimp simp: asid_high_bits_def)
   apply simp
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp: unat_ucast_eq_unat_and_mask)
   apply (subst add.commute, subst shiftr_irrelevant)
     apply (clarsimp simp: asid_low_bits_def asid_high_bits_def)
    apply (clarsimp simp: is_aligned_shift)
   apply (subst shiftl_shiftr_id)
     apply (clarsimp simp: asid_low_bits_def asid_high_bits_def)
    apply (clarsimp simp: asid_low_bits_def asid_high_bits_def word_of_nat_less)
   apply (fold asid_high_bits_def)
   apply (subst less_mask_eq)
    apply (clarsimp simp: asid_high_bits_def word_of_nat_less)
   apply (rule unat_of_nat_eq)
   apply (clarsimp simp: asid_high_bits_def)
  apply (rule less_is_non_zero_p1[where k="2^asid_high_bits << asid_low_bits"])
  apply (simp only: shiftl_t2n)
  apply (subst mult.commute, subst mult.commute, rule word_mult_less_mono1)
    apply (clarsimp simp: asid_high_bits_def word_of_nat_less)
   apply (clarsimp simp: asid_low_bits_def)
  apply (clarsimp simp: asid_low_bits_def asid_high_bits_def)
  done


section \<open>Assorted helpers\<close>
lemma fun_upds_to_map_of[THEN eq_reflection]:
  "Map.empty = map_of []"
  "((map_of xs)(k \<mapsto> v)) = map_of ((k, v) # xs)"
  by auto

lemma subst_eqn_helper:
  "(\<And>s. s = t \<longrightarrow> P s) \<Longrightarrow> P t"
  by simp

text \<open>Helper to lift FastMap lookups to "admissible labelling" predicates.\<close>
lemma iterate_labelling_helper:
  "\<lbrakk> m = map_of binds;
     distinct (map fst binds)
   \<rbrakk> \<Longrightarrow>
   (\<forall>obj label. m obj = Some label \<longrightarrow> label_of obj = label)
    = list_all (\<lambda>(k, v). label_of k = v) binds"
  apply (rule iffI)
   apply (blast intro: list_allI FastMap.map_of_lookups)
  apply (fastforce simp: list_all_iff)
  done


section \<open>Integrity proof automation\<close>

text \<open>Helpers to put the policy subgoals into a consistent form for our automation\<close>
lemma helper_pcs_refined_policyI:
  assumes cdt_policy: "\<And>p slot p' slot'.
                          cdl_cdt s (p, slot) = Some (p', slot') \<Longrightarrow>
                          (pasObjectAbs aag p', Control, pasObjectAbs aag p) \<in> pasPolicy aag"
      and delete_derived_policy: "\<And>p slot p' slot'.
                          cdl_cdt s (p, slot) = Some (p', slot') \<Longrightarrow>
                          (pasObjectAbs aag p', DeleteDerived, pasObjectAbs aag p) \<in> pasPolicy aag"
      and obj_policy: "\<And>p p_obj p_idx cap auth oref.
                          \<lbrakk> cdl_objects s p = Some p_obj;
                            object_slots p_obj p_idx = Some cap;
                            auth \<in> cdl_cap_auth_conferred cap;
                            oref \<in> cdl_obj_refs cap
                          \<rbrakk> \<Longrightarrow> (pasObjectAbs aag p, auth, pasObjectAbs aag oref) \<in> pasPolicy aag"
  shows "auth_graph_map (pasObjectAbs aag) (cdl_state_objs_to_policy s) \<subseteq> (pasPolicy aag)"
  apply (clarsimp simp: cdl_state_objs_to_policy_def auth_graph_map_def)
  by (fastforce elim: cdl_state_bits_to_policy.cases
                intro: obj_policy cdt_policy delete_derived_policy
                simp: opt_cap_def slots_of_def
                split: option.splits)

text \<open>More executable form of obj_policy\<close>
lemma helper_pcs_refined_policy__eval:
      (* policy specification, to be generated *)
  assumes policy_spec: "policy_spec \<subseteq> pasPolicy aag"
      and label_spec: "\<And>p l. label_spec p = Some l \<Longrightarrow> pasObjectAbs aag p = l"
      (* we don't handle the CDT for now, so these are unchanged *)
      and cdt_policy:
            "\<And>p slot p' slot'.
                 cdl_cdt s (p, slot) = Some (p', slot') \<Longrightarrow>
                 (pasObjectAbs aag p', Control, pasObjectAbs aag p) \<in> pasPolicy aag"
      and delete_derived_policy:
            "\<And>p slot p' slot'.
                 cdl_cdt s (p, slot) = Some (p', slot') \<Longrightarrow>
                 (pasObjectAbs aag p', DeleteDerived, pasObjectAbs aag p) \<in> pasPolicy aag"
      (* main specification, as nested set traversals *)
      and obj_policy:
            "\<forall>(p, p_obj) \<in> graph_of (cdl_objects s).
               (case label_spec p of
                  Some pl \<Rightarrow>
                     \<forall>(p_idx, cap) \<in> graph_of (object_slots p_obj).
                       \<forall>auth \<in> cdl_cap_auth_conferred cap.
                         \<forall>oref \<in> cdl_obj_refs cap.
                            (case label_spec oref of
                               Some orefl \<Rightarrow> generic_tag ''obj policy'' (p, cap, cdl_obj_refs cap)
                                                 ((pl, auth, orefl) \<in> policy_spec)
                             | _ \<Rightarrow> False)
                | _ \<Rightarrow> False)"
  shows "auth_graph_map (pasObjectAbs aag) (cdl_state_objs_to_policy s) \<subseteq> (pasPolicy aag)"
  apply (rule helper_pcs_refined_policyI)
    apply (blast intro: cdt_policy)
   apply (blast intro: delete_derived_policy)
  apply (fastforce simp: remove_generic_tag
                   intro: subsetD[OF policy_spec]
                   dest: label_spec obj_policy[simplified graph_of_def, simplified, rule_format]
                   split: option.splits)
  done

(* Efficient check for key distinctness *)
fun sorted_distinct :: "'a::linorder list \<Rightarrow> bool" where
    "sorted_distinct (x # y # xs) = (x < y \<and> sorted_distinct (y # xs))"
  | "sorted_distinct _ = True"

lemma sorted_distinct:
  "sorted_distinct xs \<Longrightarrow> sorted xs \<and> distinct xs"
  by (induct xs rule: sorted_distinct.induct; fastforce)

lemma sorted_distinct_conv:
  "sorted_distinct xs = (sorted xs \<and> distinct xs)"
  apply (induct xs)
   apply simp
  apply (rename_tac x xs, case_tac xs)
   apply simp
  apply fastforce
  done

(* This is a conditional rule and FP_Eval can't evaluate it.
   Below, we construct a workaround for this *)
lemma graph_of_map_of:
  "distinct (map fst binds) \<Longrightarrow> graph_of (map_of binds) = set binds"
  by (simp add: graph_of_def)

lemma graph_of_map_of_simp:
  "sorted_distinct (map fst binds) \<Longrightarrow> graph_of (map_of binds) = set binds"
  by (simp add: graph_of_def sorted_distinct_conv)

(* prevent looping if sorted_distinct fails for any reason *)
definition "graph_of_map_of__eval_FAIL binds \<equiv> graph_of (map_of binds)"

(* @{const rev} is because @{thm fun_upds_to_map_of} produces list in reverse order
   compared to the [_ \<mapsto> _...] syntax *)
lemma graph_of_map_of__sorted_eval:
  "graph_of (map_of binds) =
     (if sorted_distinct (rev (map fst binds)) then set binds else graph_of_map_of__eval_FAIL binds)"
  by (simp add: graph_of_map_of sorted_distinct_conv graph_of_map_of__eval_FAIL_def)

(* useful if we already have a distinctness theorem from somewhere *)
lemma graph_of_map_of__distinct_eval:
  "graph_of (map_of binds) =
     (if distinct (map fst binds) then set binds else graph_of_map_of__eval_FAIL binds)"
  by (simp add: graph_of_map_of graph_of_map_of__eval_FAIL_def)

lemma range_map_of_ptr_range:
  "\<lbrakk> RangeMap.range_map_of binds (p :: cdl_object_id) = Some ((p, p + 2^sz), l) \<rbrakk> \<Longrightarrow>
   (x \<in> ptr_range p sz) = (p \<le> x \<and> x < p + 2^sz)"
  apply (drule RangeMap.range_map_of_SomeD)
  apply (subst ptr_range_in_range)
   apply unat_arith
  apply (simp add: RangeMap.in_range.simps)
  done

lemma range_tree_ptr_range:
  "\<lbrakk> RangeMap.lookup_range_tree tree = RangeMap.range_map_of binds;
     RangeMap.monotonic_key_ranges binds;
     RangeMap.range_map_of binds (p :: cdl_object_id) = Some ((p, p + 2^sz), l);
     x \<in> ptr_range p sz \<rbrakk> \<Longrightarrow>
   RangeMap.lookup_range_tree tree x = Some ((p, p + 2^sz), l)"
  apply (subst (asm) range_map_of_ptr_range)
   apply fastforce
  apply (simp only:)
  apply (drule RangeMap.range_map_of_SomeD)
  apply (blast intro: RangeMap.range_map_of_single RangeMap.monotonic_key_ranges_disjoint)
  done

(*
   This matches exactly the expression for checking object accesses
   over a ptr_range (see cdl_obj_refs.simps).

   "map_option snd" comes from the expansion of the generated
   <app>_labelling predicate.

   The LHS expects the RangeMap to be defined in the form
   "((foo_id, foo_id + 2^sz), foo_label)", and only does anything
   useful in this branch.

   If this rewrite no longer works in the main proof, it may need adjustment.
 *)
lemma label_over_ptr_range:
  assumes "RangeMap.monotonic_key_ranges binds"
      and "\<And>x. label_spec x = map_option snd (RangeMap.range_map_of binds x)"
  shows
   "RangeMap.range_map_of binds obj_id = Some ((obj_id, obj_id + 2^sz), l) \<Longrightarrow>
    (\<forall>oref \<in> ptr_range (obj_id :: cdl_object_id) sz.
       case label_spec oref of
          Some l \<Rightarrow> P l | None \<Rightarrow> False)
     = P l"
  apply (rule iffI)
   apply (fastforce simp: range_map_of_ptr_range assms
                    dest: RangeMap.range_map_of_SomeD bspec)
  apply (clarsimp simp: assms)
  apply (subst (asm) range_map_of_ptr_range, assumption)
  apply (subst RangeMap.range_map_of_single;
         fastforce simp: RangeMap.range_map_of_single RangeMap.in_range.simps
                   intro: RangeMap.monotonic_key_ranges_disjoint assms
                   dest: RangeMap.range_map_of_SomeD)
  done

(* prevent looping if label_over_ptr_range fails for any reason *)
definition label_over_ptr_range_FAILED
  where "label_over_ptr_range_FAILED = Ball"

(* again, lift the conditional rule to a pure equation for fp_eval *)
lemma label_over_ptr_range_fp_eval:
  assumes "RangeMap.monotonic_key_ranges binds"
      and "\<And>x. label_spec x = map_option snd (RangeMap.range_map_of binds x)"
  shows
   "(\<forall>oref \<in> ptr_range (obj_id :: cdl_object_id) sz.
       case label_spec oref of Some l \<Rightarrow> P l | None \<Rightarrow> False)
     = (case RangeMap.range_map_of binds obj_id of
          Some ((obj_id', obj_end), l) \<Rightarrow>
             if obj_id' = obj_id \<and> obj_end = obj_id + 2^sz \<comment> \<open> = ptr_range\<close>
             then P l \<comment> \<open>this is the case we care about, the rest is just fluff\<close>
             else (label_over_ptr_range_FAILED (ptr_range obj_id sz)
                     (\<lambda>oref. case label_spec oref of Some l \<Rightarrow> P l | None \<Rightarrow> False))
        | None \<Rightarrow> (label_over_ptr_range_FAILED (ptr_range obj_id sz)
                     (\<lambda>oref. case label_spec oref of Some l \<Rightarrow> P l | None \<Rightarrow> False)))"
  apply (simp only: label_over_ptr_range_FAILED_def)
  (* rewrite "P l" in RHS *)
  apply (subst option.case_cong[where ?f2.0="case_prod _", OF refl refl])
   apply (clarsimp simp only:)
   apply wpfix
   apply (subst if_cong[OF refl _ refl])
    apply (clarsimp simp only:)
    apply (erule label_over_ptr_range[OF assms, symmetric])
   apply (rule refl)
  (* now both sides are identical in all cases *)
  apply (fastforce simp only: split: option.splits if_splits)
  done


lemma cdl_state_irqs_to_policy__eval:
  assumes policy_spec: "policy_spec \<subseteq> pasPolicy aag"
      and obj_label_spec: "\<And>p l. obj_label_spec p = Some l \<Longrightarrow> pasObjectAbs aag p = l"
      and irq_label_spec: "\<And>irq l. irq_label_spec irq = Some l \<Longrightarrow> pasIRQAbs aag irq = l"
  shows "\<forall>(p, p_obj) \<in> graph_of (cdl_objects s).
           (case obj_label_spec p of
              Some pl \<Rightarrow>
                 \<forall>(p_idx, cap) \<in> graph_of (object_slots p_obj).
                   \<forall>irq \<in> cdl_cap_irqs_controlled cap.
                      (case irq_label_spec irq of
                           Some irql \<Rightarrow> generic_tag ''irq policy'' (p, cap, irq)
                                            ((pl, Control, irql) \<in> policy_spec)
                         | _ \<Rightarrow> False)
            | _ \<Rightarrow> False)
         \<Longrightarrow> cdl_state_irqs_to_policy aag s \<subseteq> pasPolicy aag"
  apply clarsimp
  apply (erule cdl_state_irqs_to_policy_aux.cases)
  apply (fastforce simp: opt_cap_def slots_of_def graph_of_def remove_generic_tag
                   split: option.splits
                   dest: obj_label_spec irq_label_spec
                   intro: subsetD[OF policy_spec])
  done

lemma cdl_state_asids_to_policy__eval:
  assumes policy_spec: "policy_spec \<subseteq> pasPolicy aag"
      and obj_label_spec: "\<And>p l. obj_label_spec p = Some l \<Longrightarrow> pasObjectAbs aag p = l"
      and asid_label_spec: "\<And>asid l. asid_label_spec (asid_high_bits_of asid) = Some l \<Longrightarrow>
                                      pasASIDAbs aag asid = l"
      and cap_asids:
            "\<forall>(p, p_obj) \<in> graph_of (cdl_objects s).
               (case obj_label_spec p of
                  Some pl \<Rightarrow>
                     \<forall>(p_idx, cap) \<in> graph_of (object_slots p_obj).
                       \<forall>asid \<in> asid_high_bits_of ` cdl_cap_asid' cap.
                          (case asid_label_spec asid of
                               Some asidl \<Rightarrow> generic_tag ''asid policy'' (p, cap, asid)
                                                 ((pl, Control, asidl) \<in> policy_spec)
                             | _ \<Rightarrow> False)
                | _ \<Rightarrow> False)"
      and asid_table_lookups:
            "\<forall>(asid_high, asid_pool_cap) \<in> graph_of (cdl_asid_table s).
               \<not>is_null_cap asid_pool_cap \<longrightarrow>
               (case asid_label_spec (of_nat asid_high) of
                  Some asidl \<Rightarrow>
                     (case cdl_objects s (cap_object asid_pool_cap) of
                        Some asid_pool \<Rightarrow>
                           \<forall>(asid_low, pd_cap) \<in> graph_of (object_slots asid_pool).
                             if is_null_cap pd_cap then True else
                                (case obj_label_spec (cap_object pd_cap) of
                                     Some pdl \<Rightarrow> generic_tag ''asid PD policy'' (asid_high, pd_cap)
                                                     ((asidl, Control, pdl) \<in> policy_spec)
                                   | _ \<Rightarrow> False)
                      | _ \<Rightarrow> False)
                     \<and> (case obj_label_spec (cap_object asid_pool_cap) of
                           Some asid_pool_l \<Rightarrow>
                             generic_tag ''asid pool policy'' (asid_high, asid_pool_cap)
                                 ((asid_pool_l, AAuth ASIDPoolMapsASID, asidl) \<in> policy_spec)
                         | _ \<Rightarrow> False)
                | _ \<Rightarrow> False)"

  shows "cdl_state_asids_to_policy aag s \<subseteq> pasPolicy aag"
  apply clarsimp
  apply (erule cdl_state_asids_to_policy_aux.cases)
    using cap_asids[unfolded remove_generic_tag]
    apply (fastforce simp: opt_cap_def slots_of_def graph_of_def
                     dest: obj_label_spec asid_label_spec
                     intro: subsetD[OF policy_spec]
                     split: option.splits)
   using asid_table_lookups[unfolded remove_generic_tag]
   apply (fastforce simp: opt_cap_def slots_of_def graph_of_def transform_asid_def
                    dest: obj_label_spec asid_label_spec
                    intro: subsetD[OF policy_spec]
                    split: option.splits)
  using asid_table_lookups[unfolded remove_generic_tag]
  apply (fastforce simp: opt_cap_def slots_of_def graph_of_def transform_asid_def
                   dest: obj_label_spec asid_label_spec
                   intro: subsetD[OF policy_spec]
                   split: option.splits)
  done

section \<open>Automation simpsets\<close>

lemma Ball_eval:
  "Ball (insert x s) P = (P x \<and> Ball s P)"
  "Ball Set.empty P = True"
  by auto

lemma ball_cong_weak:
  "\<And>s s' P. s = s' \<Longrightarrow> Ball s P = Ball s' P"
  by simp

lemmas finite_set_simps =
        insert_iff empty_iff
        Un_insert_left Un_empty_left
        Int_insert_left Int_empty_left
        insert_Diff_if empty_Diff

(* missing from HOL-Word... *)
lemma bintrunc_1_1:
  "bintrunc 1 1 = 1"
  by auto

(* simpset for comparisons between word literals *)
lemmas word_rel_simps_small =
  order_refl (* shortcut *)
  rel_simps simp_thms
  word_less_alt word_le_def word_uint_eq_iff uint_0_eq uint_1
  (* need bintrunc to reduce numerals mod word size *)
  uint_bintrunc bintrunc_numeral_simps bintrunc_1_1
  numeral_One
  (* evaluating word size for bintrunc -- yuck *)
  len_num0 len_num1 len_bit0 len_bit1
  arith_simps mult_1_right pred_numeral_simps numeral_plus_one
  arith_special


(* test for simpset *)
ML \<open>
let
  val eval = Raw_Simplifier.rewrite @{context} false
               (map_filter FP_Eval.maybe_convert_eqn @{thms word_rel_simps_small});
  fun check word_typ cmp cmp_term x y = let
    val xt = HOLogic.mk_number word_typ x;
    val yt = HOLogic.mk_number word_typ y;
    val prop = Const (cmp_term, word_typ --> word_typ --> @{typ bool}) $ xt $ yt;
    val prop = (if cmp (x, y) then prop else @{term "HOL.Not"} $ prop)
               |> Thm.cterm_of @{context};
    val result = eval prop |> Thm.rhs_of;
  in if Thm.term_of result = @{term True} then () else
       error ("word_rel_simps_small test failed for: " ^ @{make_string} prop ^
              "\n  Result: " ^ @{make_string} result) end
in
  [@{typ word32}, @{typ word64}, @{typ "3 word"}]
  |> app (fn word_typ =>
      [(op<, @{const_name less}), (op<=, @{const_name less_eq}), (op=, @{const_name HOL.eq})]
      |> app (fn (cmp, cmp_term) =>
          List.tabulate (8, I)
          |> app (fn x =>
              List.tabulate (8, I)
              |> app (fn y =>
                  check word_typ cmp cmp_term x y
              )
          )
      )
  )
end
\<close>

lemma pow_2_numeral:
  "(2::'a::{numeral,semiring_1,power})^0 = 1"
  "(2::'a)^1 = 2"
  "(2::'a)^numeral n = 2 * 2^(numeral n - 1)"
  apply simp
  apply simp
  apply (metis numeral_eq_Suc pred_numeral_def power_Suc)
  done

(* needed to evaluate "ptr + 2^sz" expressions *)
lemmas word_pow_arith_simps =
  pow_2_numeral uint_word_arith_bintrs
  uint_0_eq uint_1 uint_bintrunc bintrunc_Suc_numeral numeral_One
  arith_simps arith_special
  nat_0 nat_one_as_int[symmetric] nat_numeral nat_numeral_diff_1 mult_1_right


lemmas object_slots_eval_simps
         [simplified fun_upds_to_map_of] = (* NB: convert Map.empty for FP_Eval compatibility *)
    object_slots_def cdl_object.case
    cdl_asid_pool.simps
    cdl_cnode.simps
    cdl_irq_node.simps
    cdl_page_table.simps
    cdl_page_directory.simps
    cdl_tcb.simps

(* Main simpset and congs *)
lemmas obj_policy_eval_simps =
        (* basics *)
        simp_thms if_True if_False
        Ball_eval option.case cdl_cap.case prod.case
        list.set prod.sel option.map option.set

        object_slots_eval_simps
        cdl_obj_refs.simps

        (* converting graph_of (map_of <caps...>) *)
        graph_of_map_of__sorted_eval rev.simps append.simps
        sorted_distinct.simps rel_simps list.map

        (* evaluating asid integrity *)
        cdl_cap_asid'.simps
        is_null_cap_def cap_object_simps
        image_empty
        semiring_1_class.of_nat_0 semiring_1_class.of_nat_1 semiring_1_class.of_nat_numeral

        (* evaluating irq integrity *)
        cdl_cap_irqs_controlled.simps

        (* evaluating cdl_cap_auth_conferred for obj integrity *)
        cdl_cap_auth_conferred_def
        cap_rights_to_auth_def vspace_cap_rights_to_auth_def
        rights.distinct finite_set_simps

lemmas obj_policy_eval_congs =
        if_weak_cong FP_Eval.let_weak_cong'
        ball_cong_weak option.case_cong_weak prod.case_cong_weak
        cdl_object.case_cong_weak cdl_cap.case_cong_weak

end
end
