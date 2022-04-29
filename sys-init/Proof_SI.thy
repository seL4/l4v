(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Proof_SI
  imports
    CreateObjects_SI
    CreateIRQCaps_SI
    DuplicateCaps_SI
    InitVSpace_SI
    InitTCB_SI
    InitCSpace_SI
    InitIRQ_SI
    StartThreads_SI
begin

(* This isn't actually all the combinations, but enough of them for what I needed. *)
lemma object_types_distinct:
  "tcb_at x s     \<Longrightarrow> \<not> cnode_at x s"
  "table_at x s   \<Longrightarrow> \<not> cnode_at x s"
  "table_at x s   \<Longrightarrow> \<not> tcb_at x s"
  "capless_at x s \<Longrightarrow> \<not> cnode_at x s"
  "capless_at x s \<Longrightarrow> \<not> tcb_at x s"
  "capless_at x s \<Longrightarrow> \<not> table_at x s"
  "capless_at x s \<Longrightarrow> \<not> pt_at x s"
  "capless_at x s \<Longrightarrow> \<not> pd_at x s"
  "capless_at x s \<Longrightarrow> \<not> asidpool_at x s"
  by (clarsimp simp: object_at_def is_tcb_def is_cnode_def is_pd_def is_pt_def
                     is_ep_def is_ntfn_def is_asidpool_def is_frame_def
                     is_untyped_def | rule conjI |
      clarsimp split: cdl_object.splits)+

lemma real_objects_some_type:
  "well_formed spec \<Longrightarrow>
   {obj_id. real_object_at obj_id spec \<and>
       \<not> cnode_at obj_id spec \<and>
       \<not> tcb_at obj_id spec \<and>
       \<not> pt_at obj_id spec \<and>
       \<not> pd_at obj_id spec \<and>
       \<not> untyped_at obj_id spec \<and>
       \<not> ep_at obj_id spec \<and>
       \<not> ntfn_at obj_id spec \<and>
       \<not> frame_at obj_id spec} = {}"
  apply (clarsimp simp: object_at_def is_tcb_def is_cnode_def is_pd_def is_pt_def
                        is_ep_def is_ntfn_def is_asidpool_def is_frame_def is_untyped_def)
  apply (clarsimp split: cdl_object.splits)
  apply (drule_tac obj_id=x in well_formed_asidpool_at)
  apply (clarsimp simp: real_object_at_def object_at_def is_asidpool_def irq_nodes_def is_irq_node_def
                 split: cdl_object.splits)
  by metis

lemma capdl_objects_by_parts:
  "well_formed spec \<Longrightarrow>
   (sep_map_set_conj P {obj_id. real_object_at obj_id spec}) =
   (sep_map_set_conj P {obj_id. cnode_at obj_id spec} \<and>*
    sep_map_set_conj P {obj_id. tcb_at obj_id spec} \<and>*
    sep_map_set_conj P {obj_id. table_at obj_id spec} \<and>*
    sep_map_set_conj P {obj_id. capless_at obj_id spec})"
  apply (rule sym)
  apply (subst (5) sep_map_set_conj_restrict [where t = "(\<lambda>obj. cnode_at obj spec)"], simp)
  apply (subst (6) sep_map_set_conj_restrict [where t = "(\<lambda>obj. tcb_at obj spec)"], simp)
  apply (subst (7) sep_map_set_conj_restrict [where t = "(\<lambda>obj. table_at obj spec)"], simp)
  apply (subst (8) sep_map_set_conj_restrict [where t = "(\<lambda>obj. capless_at obj spec)"], simp)
  apply (clarsimp simp: object_types_distinct real_object_not_irq_node real_objects_some_type
                  cong: rev_conj_cong)
  done

lemma objects_empty_by_parts:
  "well_formed spec \<Longrightarrow>
   (objects_empty spec t {obj_id. real_object_at obj_id spec}) =
   (objects_empty spec t {obj_id. cnode_at obj_id spec} \<and>*
    objects_empty spec t {obj_id. tcb_at obj_id spec} \<and>*
    objects_empty spec t {obj_id. table_at obj_id spec} \<and>*
    objects_empty spec t {obj_id. capless_at obj_id spec})"
  by (clarsimp simp: objects_empty_def capdl_objects_by_parts)

lemma objects_initialised_by_parts:
  "well_formed spec \<Longrightarrow>
   (objects_initialised spec t {obj_id. real_object_at obj_id spec}) =
   (objects_initialised spec t {obj_id. cnode_at obj_id spec} \<and>*
    objects_initialised spec t {obj_id. tcb_at obj_id spec} \<and>*
    objects_initialised spec t {obj_id. table_at obj_id spec} \<and>*
    objects_initialised spec t {obj_id. capless_at obj_id spec})"
  by (clarsimp simp: objects_initialised_def capdl_objects_by_parts)

lemma object_empty_object_initialised_capless:
  "capless_at obj_id spec \<Longrightarrow>
   object_empty spec t obj_id = object_initialised spec t obj_id"
  apply (rule ext)
  apply (clarsimp simp: object_empty_def object_initialised_def)
  apply (clarsimp simp: object_initialised_general_def object_default_state_def2)
  apply (fastforce simp: object_at_def update_slots_def object_initialised_state_def
                         object_default_state_def2 spec2s_def
                         is_ep_def is_ntfn_def is_asidpool_def
                         is_frame_def is_untyped_def cdl_frame.splits
                  split: cdl_object.splits)
  done

lemma objects_empty_objects_initialised_capless:
  "objects_empty spec t {obj_id. capless_at obj_id spec} =
   objects_initialised spec t {obj_id. capless_at obj_id spec}"
  apply (clarsimp simp: objects_empty_def objects_initialised_def)
  apply (rule sep.prod.cong, simp)
  apply (clarsimp simp: object_empty_object_initialised_capless)
  done

lemma valid_case_prod'[wp]:
  "(\<And>x y. \<lbrace>P x y\<rbrace> f x y \<lbrace>Q\<rbrace>) \<Longrightarrow> \<lbrace>P (fst v) (snd v)\<rbrace> case v of (x, y) \<Rightarrow> f x y \<lbrace>Q\<rbrace>"
  by (clarsimp split: prod.splits)

lemma le_list_all:
  "\<lbrakk>unat start < 2 ^ si_cnode_size; unat (end - 1) < 2 ^ si_cnode_size\<rbrakk>
   \<Longrightarrow> list_all (\<lambda>n. (n::32 word) < 2 ^ si_cnode_size) [start .e. end - 1]"
  apply (clarsimp simp: list_all_iff)
  apply (subst word_arith_power_alt)
  apply simp
  by (metis (no_types) dual_order.strict_trans2 unat_less_2_si_cnode_size word_of_int_numeral word_of_int_power_hom)

lemma card_eq_lengthI:
  "set xs = ys \<Longrightarrow> distinct xs \<Longrightarrow> length xs = card ys"
  by (induct xs arbitrary: ys; fastforce)

lemma length_filter_card:
  "\<lbrakk>s_list = sorted_list_of_set s; finite s\<rbrakk>
   \<Longrightarrow> length (filter P s_list) = card {x \<in> s. P x}"
  by (fastforce intro: card_eq_lengthI)


lemma the_map_of_zipE: "p \<in> set xs \<Longrightarrow> length xs \<le> length ys \<Longrightarrow> list_all P ys \<Longrightarrow> P (the (map_of (zip xs ys) p))"
  apply (induct xs arbitrary: ys; clarsimp)
  by (metis (no_types, lifting) cons_set_intro length_Cons list.set_intros(2) list_all_spec the_map_of_zip_inR)


lemma the_map_of_zipE': "p \<in> set xs \<Longrightarrow> length xs \<le> length ys \<Longrightarrow> list_all P (take (length xs) ys) \<Longrightarrow> P (the (map_of (zip xs ys) p))"
  apply (induct xs arbitrary: ys; clarsimp)
  apply (case_tac ys; clarsimp)
  done

lemma length_eq_set_eq: "set xs = set ys \<Longrightarrow> distinct xs \<Longrightarrow> distinct ys \<Longrightarrow> length xs = length ys"
  by (metis distinct_card)

lemma bij_betw_map_of': "set xs = S \<Longrightarrow> distinct xs \<Longrightarrow> distinct ys \<Longrightarrow> length xs = length ys \<Longrightarrow>  bij_betw (the \<circ> map_of (zip xs ys)) S  (set ys) "
  apply (clarsimp simp: comp_def bij_betw_def)
  apply (intro conjI)
   apply (rule map_of_zip_inj'; clarsimp)
  apply (clarsimp simp: image_def; rule set_eqI, rule iffI; clarsimp)
   apply (erule the_map_of_zipE'; clarsimp)
   apply (clarsimp simp: list_all_def)
  by (metis Some_to_the distinct_Ex1 map_of_zip_nth nth_mem)

lemma prod_bind_simp: "(do (x, y) <- f; g x y od) = (do x <- f; g (fst x) (snd x) od)  "
  by (rule ext, fastforce simp: bind_def split: prod.splits)

lemma kbind_bind: "(do x <- f; g od) = (do f; g od)  "
  by (rule ext, fastforce simp: bind_def split: prod.splits)

abbreviation "map_lists xs ys \<equiv> map_of (zip xs ys)"
notation map_lists ("(_ \<longmapsto> _)" [1000] 76)

lemma map_lists_restrict[simp]: "length ns = length xs \<Longrightarrow> ns \<longmapsto> (xs @ ys) = ns \<longmapsto> xs"
  apply (induct xs; clarsimp)
  apply (rule ext)
  by (metis append_Cons append_Nil2 length_Cons zip_Nil zip_append)


lemma distinct_append_disjoint: "distinct xs \<Longrightarrow> xs = ys @ zs \<Longrightarrow> set ys \<inter> set zs = {}"
  by (induct xs; clarsimp)

lemma split_list_distinct: "xs = as @ bs @ cs \<Longrightarrow> distinct xs \<Longrightarrow> distinct as \<and> distinct bs \<and> distinct cs \<and> set as \<inter> set bs = {} \<and> set as \<inter> set cs = {} \<and>
                                             set bs \<inter> set cs = {}"
  apply (intro conjI; clarsimp)
   apply blast
  apply blast
  done

lemma real_objects_are_objects[simp]: "{obj_id. real_object_at obj_id spec} \<subseteq> dom (cdl_objects spec)"
  by (metis (mono_tags) Collect_subset set_object_type(6))

lemma concat_snd_collect_children[simp]:
  "List.concat (map snd untyped_derivations) = collect_children untyped_derivations"
  apply (induction untyped_derivations)
  by (auto simp: collect_children_def)

definition
  "valid_boot_info_sizes ustart uend fstart fend \<equiv>
    unat ustart < 2 ^ si_cnode_size \<and>
    unat (uend - 1) < 2 ^ si_cnode_size \<and>
    unat fstart < 2 ^ si_cnode_size \<and>
    unat (fend - 1) < 2 ^ si_cnode_size \<and>
    uend \<noteq> 0 \<and> fend \<noteq> 0"

lemma valid_concat_regions_appends:
  "\<lbrakk>valid_concat_regions rg1 rg2; valid_concat_regions rg2 rg3;
    valid_concat_regions rg3 rg4; valid_concat_regions rg4 rg5\<rbrakk> \<Longrightarrow>
   valid_concat_regions rg1 (rg2 @2 rg3 @2 rg4 @2 rg5) \<and>
   valid_concat_regions rg2 (rg3 @2 rg4 @2 rg5) \<and> valid_concat_regions rg3 (rg4 @2 rg5) \<and>
   valid_region rg1 \<and> valid_region rg2 \<and> valid_region rg3 \<and> valid_region rg4 \<and> valid_region rg5"
  by auto

lemma sys_init_explicit:
  "\<lbrakk>well_formed spec;
    valid_untypeds (map fst untyped_derivations) untyped_cptrs ut_info untyped_caps;
    valid_derivations spec untyped_derivations untyped_map;
    obj_ids = sorted_list_of_set (dom (cdl_objects spec)); distinct obj_ids;
    real_ids = collect_children untyped_derivations;

    \<forall>irq\<in>used_irqs spec. t (cdl_irq_node spec irq) = Some (cdl_irq_node spec irq);
    (\<And>* map (\<lambda>(parent, children).
                 (=) (aligned_allocations spec (Min (available_range (cap_of (untyped_map parent)))) children))
              untyped_derivations) t;
    set (collect_children untyped_derivations) = {obj_id . real_object_at obj_id spec};
    card (used_irqs spec) + length (collect_children untyped_derivations) = length obj_ids;

    bi_untypeds bootinfo = (ustart, uend);
    bi_free_slots bootinfo = (fstart, fend);
    bi_untyped_information bootinfo = ut_info \<and>
    valid_boot_info_sizes ustart uend fstart fend;

    [ustart .e. uend - 1] = untyped_cptrs;
    (fstart, fend) = free_cptrs;
    length untyped_derivations = unat uend - unat ustart;
    dup_caps = (map_of (zip_region [obj\<leftarrow>real_ids. cnode_or_tcb_at obj spec]
                                   (drop_region (length obj_ids) free_cptrs)));
    untyped_map = make_untyped_map (map fst untyped_derivations) untyped_cptrs
                                   ut_info untyped_caps;

    length_region real_free_cptrs = length real_ids;
    length_region irq_free_cptrs = card (used_irqs spec);
    length_region dup_cap_free_cptrs = length [obj\<leftarrow>real_ids. cnode_or_tcb_at obj spec];
    length_region shared_frame_cap_cptrs = card (\<Union>(set ` get_frame_caps spec ` {obj. pd_at obj spec}));
    valid_slot_region real_free_cptrs; fst real_free_cptrs = fst free_cptrs;
    valid_slot_region irq_free_cptrs; valid_concat_regions real_free_cptrs irq_free_cptrs;
    valid_slot_region dup_cap_free_cptrs; valid_concat_regions irq_free_cptrs dup_cap_free_cptrs;
    valid_slot_region shared_frame_cap_cptrs; valid_concat_regions dup_cap_free_cptrs shared_frame_cap_cptrs;
    valid_slot_region remaining_cptrs; valid_concat_regions shared_frame_cap_cptrs remaining_cptrs;
    free_cptrs =
      real_free_cptrs @2 irq_free_cptrs @2 dup_cap_free_cptrs @2 shared_frame_cap_cptrs @2
      remaining_cptrs
   \<rbrakk> \<Longrightarrow>
   \<lbrace>\<guillemotleft>(\<And>* (cptr, cap) \<in> set (zip untyped_cptrs untyped_caps). (si_cnode_id, unat cptr) \<mapsto>c cap) \<and>*
     (\<And>* cptr \<in> set_region free_cptrs. (si_cnode_id, unat cptr) \<mapsto>c NullCap)  \<and>*
     (SETSEPCONJ obj_id:set (collect_children untyped_derivations). the (t obj_id) \<mapsto>o Untyped) \<and>*
     si_objects \<and>*
     si_irq_nodes spec \<and>*
     (SETSEPCONJ pd_id | pd_at pd_id spec.
       frame_duplicates_empty (make_frame_cap_map real_ids (shared_frame_cap_cptrs @2 remaining_cptrs) spec)
                              pd_id spec) \<and>*
     R\<guillemotright>\<rbrace>
    init_system spec bootinfo untyped_derivations
    \<lbrace>\<lambda>_ s.
      \<guillemotleft>objects_initialised spec t {obj_id. real_object_at obj_id spec} \<and>*
       irqs_initialised spec t (used_irqs spec) \<and>*
       (\<And>* cptr\<in>set_region (real_free_cptrs @2 irq_free_cptrs).
         (si_cnode_id, unat cptr) \<mapsto>c NullCap) \<and>*
       si_caps_at t dup_caps spec False {obj_id. cnode_or_tcb_at obj_id spec} \<and>*
       si_objects \<and>*
       (SETSEPCONJ cptr:set_region (shared_frame_cap_cptrs @2 remaining_cptrs).
         (si_cnode_id, unat cptr) \<mapsto>c NullCap) \<and>*
       (\<And>* map2 (\<lambda>slot. on_depleted_untyped_cap (sep_map_c (si_cnode_id, unat slot))) untyped_cptrs untyped_caps) \<and>*
       (SETSEPCONJ pd_id | pd_at pd_id spec.
         frame_duplicates_copied (make_frame_cap_map real_ids (shared_frame_cap_cptrs @2 remaining_cptrs) spec)
                                 pd_id spec t) \<and>*
       R\<guillemotright> s \<rbrace>"
  apply (clarsimp simp: valid_boot_info_sizes_def)
  apply (prop_tac "length (collect_children untyped_derivations) = length (filter (\<lambda>obj. real_object_at obj spec) obj_ids)")
   apply (rule length_eq_set_eq; clarsimp)
  apply (frule (1) le_list_all [where start = ustart])
  apply (frule (1) le_list_all [where start = fstart and ?end = fend])
  apply (frule well_formed_objects_card)
  apply (insert distinct_card [symmetric, where xs ="[obj\<leftarrow>obj_ids . cnode_or_tcb_at obj spec]"], simp)
  apply (clarsimp simp: init_system_def prod_bind_simp)
  apply (timeit \<open>(monster_mash)\<close>)
  apply (frule (3) valid_concat_regions_appends, (erule conjE)+)
  apply (clarsimp simp: kbind_bind well_formed_spec_used_irqs_compute parse_bootinfo_def
              simp del: K_bind_def)
  apply (wp sep_wp:
                 start_threads_sep[where t=t] init_cspace_sep[where t=t and free_cptrs=free_cptrs]
                 init_tcbs_sep[where t=t] init_vspace_sep[where t=t] init_pd_asids_sep[where t=t]
                 init_irqs_sep[where t=t and dev=False] duplicate_caps_sep'[where t=t and dev=False]
                 create_irq_caps_sep'[where t=t and spec = spec])
   apply (wp add: sep_lift_generic[OF
                  create_objects_sep'[where t=t and untyped_slots=untyped_cptrs and
                                            untyped_caps=untyped_caps and dev=False and
                                            untyped_map=untyped_map,
                                            simplified sep_wp_simp], simplified])+
  apply (clarsimp simp: objects_initialised_by_parts objects_empty_by_parts
                        objects_empty_objects_initialised_capless distinct_zipI1
                        sep_list_conj_sep_map_set_conj distinct_length_filter'
                        valid_untypeds_def)
  apply (intro conjI allI impI pred_conjI | sep_cancel+)+
    apply (fastforce simp: ran_def elim: well_formed_object_domain)
   apply (clarsimp simp: valid_slot_region_append)
  apply (intro conjI allI impI pred_conjI | sep_cancel+ | clarsimp)+
       apply (rule bij_betw_map_of'[simplified comp_def]; clarsimp)
      apply blast
     apply (rule the_map_of_zipE)
       apply (metis pd_at_is_real)
      apply clarsimp
     apply clarsimp
    apply blast
   apply blast
  apply blast
  done

(**************************************************
 * The top level lemma for system initialisation. *
 **************************************************)

definition valid_boot_info where
  "valid_boot_info bootinfo spec untyped_derivations t \<equiv> \<lambda>s.
  \<exists>untyped_caps untyped_map fstart fend ustart uend ut_info obj_ids real_obj_ids
   (real_free_cptrs :: bi_slot_region)
   (irq_free_cptrs :: bi_slot_region)
   (dup_cap_free_cptrs :: bi_slot_region)
   (shared_frame_cap_cptrs :: bi_slot_region)
   (remaining_cptrs :: bi_slot_region).
    ((\<And>* (cptr, cap) \<in> set (zip [ustart .e. uend - 1] untyped_caps). (si_cnode_id, unat cptr) \<mapsto>c cap) \<and>*
     (\<And>* cptr \<in> set_region (fstart, fend). (si_cnode_id, unat cptr) \<mapsto>c NullCap)  \<and>*
     (SETSEPCONJ obj_id:set (collect_children untyped_derivations). the (t obj_id) \<mapsto>o Untyped) \<and>*
     si_objects \<and>*
     si_irq_nodes spec \<and>*
     (SETSEPCONJ pd_id | pd_at pd_id spec.
       frame_duplicates_empty (make_frame_cap_map real_obj_ids ( shared_frame_cap_cptrs @2 remaining_cptrs)
                                                  spec)
                              pd_id spec)) s \<and>
     obj_ids = sorted_list_of_set (dom (cdl_objects spec)) \<and>
     real_obj_ids = collect_children untyped_derivations \<and>
     bi_untypeds bootinfo = (ustart, uend) \<and>
     bi_free_slots bootinfo = (fstart, fend) \<and>
     bi_untyped_information bootinfo = ut_info \<and>
     valid_boot_info_sizes ustart uend fstart fend \<and>
     length untyped_derivations = unat uend - unat ustart \<and>
     map (fst) untyped_derivations = [ustart .e. uend - 1] \<and>
     valid_untypeds (map fst untyped_derivations) [ustart .e. uend - 1] ut_info untyped_caps \<and>
     valid_derivations spec untyped_derivations untyped_map \<and>
     untyped_map = make_untyped_map (map fst untyped_derivations) [ustart .e. uend - 1]
                                    ut_info untyped_caps \<and>
     (\<forall>irq\<in>used_irqs spec. t (cdl_irq_node spec irq) = Some (cdl_irq_node spec irq)) \<and>
     ((\<And>* map (\<lambda>(parent, children).
                 (=) (aligned_allocations spec (Min (available_range (cap_of (untyped_map parent)))) children))
              untyped_derivations) t) \<and>
     set (collect_children untyped_derivations) = {obj_id . real_object_at obj_id spec} \<and>
     card (used_irqs spec) + length (collect_children untyped_derivations) = length obj_ids \<and>
     length_region real_free_cptrs = length real_obj_ids \<and>
     length_region irq_free_cptrs = card (used_irqs spec) \<and>
     length_region dup_cap_free_cptrs = length [obj\<leftarrow>real_obj_ids. cnode_or_tcb_at obj spec] \<and>
     length_region shared_frame_cap_cptrs = card (\<Union>(set ` get_frame_caps spec ` {obj. pd_at obj spec})) \<and>
     (fstart, fend) =
            real_free_cptrs @2
            irq_free_cptrs @2
            dup_cap_free_cptrs @2
            shared_frame_cap_cptrs @2 remaining_cptrs \<and>
     valid_slot_region real_free_cptrs \<and> fst real_free_cptrs = fstart \<and>
     valid_slot_region irq_free_cptrs \<and> valid_concat_regions real_free_cptrs irq_free_cptrs \<and>
     valid_slot_region dup_cap_free_cptrs \<and> valid_concat_regions irq_free_cptrs dup_cap_free_cptrs \<and>
     valid_slot_region shared_frame_cap_cptrs \<and> valid_concat_regions dup_cap_free_cptrs shared_frame_cap_cptrs \<and>
     valid_slot_region remaining_cptrs \<and> valid_concat_regions shared_frame_cap_cptrs remaining_cptrs"

definition si_final_objects ::
  "cdl_state \<Rightarrow> (cdl_object_id \<Rightarrow> cdl_object_id option) \<Rightarrow> sep_pred"
  where
  "si_final_objects spec t \<equiv> \<lambda>s.
   \<exists>dup_caps (untyped_cptrs::32 word list) (free_cptrs::32 word list) untyped_caps.
    ((\<And>*  cptr \<in> set (take (card (dom (cdl_objects spec))) free_cptrs).
          (si_cnode_id, unat cptr) \<mapsto>c NullCap) \<and>*
     (\<And>*  cptr \<in> set (drop (card (dom (cdl_objects spec)) +
                             card ({obj_id. cnode_or_tcb_at obj_id spec})) free_cptrs).
          (si_cnode_id, unat cptr) \<mapsto>c NullCap) \<and>*
     (\<And>* map2 (\<lambda>x. on_depleted_untyped_cap (sep_map_c (si_cnode_id, unat x))) untyped_cptrs untyped_caps) \<and>*
     (\<And>*  obj_id \<in> {obj_id. cnode_or_tcb_at obj_id spec}. (si_cap_at t dup_caps spec False obj_id)) \<and>*
      si_objects) s"

lemma sys_init:
  "\<lbrakk>well_formed spec;
    obj_ids = sorted_list_of_set (dom (cdl_objects spec));
    real_obj_ids = collect_children untyped_derivations\<rbrakk> \<Longrightarrow>
   \<lbrace>\<guillemotleft>valid_boot_info bootinfo spec untyped_derivations t \<and>* R\<guillemotright>\<rbrace>
   init_system spec bootinfo untyped_derivations
   \<lbrace>\<lambda>_ s.
    \<guillemotleft>objects_initialised spec t {obj_id. real_object_at obj_id spec} \<and>*
     irqs_initialised spec t (used_irqs spec) \<and>*
     si_final_objects spec t \<and>*
     (EXS map. (SETSEPCONJ pd_id | pd_at pd_id spec. frame_duplicates_copied map pd_id spec t)) \<and>*
     R\<guillemotright> s \<rbrace>"
  apply (insert distinct_card [where xs = "[obj\<leftarrow>real_obj_ids . cnode_or_tcb_at obj spec]"], simp)
  apply (clarsimp simp: valid_boot_info_def si_final_objects_def
                        sep_conj_exists sep_conj_assoc
              simp del: split_paired_Ex)
  apply (subst ex_conj_increase)+
  apply (rule hoare_ex_pre)+
  apply (rule hoare_grab_asm)+
  apply (rename_tac
           untyped_caps \<comment> \<open>fstart\<close> fend ustart uend real_free_cptrs irq_free_cptrs
           dup_cap_free_cptrs shared_frame_cap_cptrs remaining_cptrs)
  apply (rule hoare_chain)
    apply (rule sys_init_explicit[where obj_ids="sorted_list_of_set (dom (cdl_objects spec))"
                                        and t=t and R=R];
           assumption?)
              apply (solves \<open>simp\<close>)+
    apply (subst fst_conv)
    apply clarsimp
  apply (frule (3) valid_concat_regions_appends, (erule conjE)+)
   apply (simp add:length_filter_card)
  apply (simp add: si_objects_extra_caps_def si_caps_at_def
                        sep_conj_exists sep_conj_assoc)
  apply (rule_tac x="map_of (zip_region [obj \<leftarrow> real_obj_ids. cnode_or_tcb_at obj spec] dup_cap_free_cptrs)"
         in exI)
  apply (rule_tac x="[ustart .e. uend - 1]" in exI)
  apply (rule_tac x="list_region (fst real_free_cptrs, fend)" in exI)
  apply (rule_tac x=untyped_caps in exI)
  apply (rule_tac x="make_frame_cap_map real_obj_ids (shared_frame_cap_cptrs @2 remaining_cptrs) spec"
         in exI)
  apply (frule (3) valid_concat_regions_appends, (erule conjE)+)
  apply (clarsimp simp: sep_conj_ac)
  done

(*
definition injective :: "('a \<Rightarrow> 'b option) \<Rightarrow> bool"
  where "injective f \<equiv> inj_on f (dom f)"

lemma sys_init_paper:
  "\<lbrakk>well_formed spec; obj_ids = sorted_list_of_set (dom (cdl_objects spec))\<rbrakk> \<Longrightarrow>
     \<lbrace>\<guillemotleft>valid_boot_info bootinfo spec untyped_derivations t \<and>* R\<guillemotright>\<rbrace>
     init_system spec bootinfo obj_ids untyped_derivations
     \<lbrace>\<lambda>_ s. \<exists>\<phi>.
      \<guillemotleft>objects_initialised spec \<phi> {obj_id. real_object_at obj_id spec} \<and>*
       irqs_initialised spec \<phi> (used_irqs spec) \<and>*
       si_final_objects spec \<phi> \<and>*
       (EXS map. (SETSEPCONJ pd_id | pd_at pd_id spec. frame_duplicates_copied map pd_id spec \<phi>)) \<and>*
       R\<guillemotright> s \<and>
       injective \<phi> \<and> dom \<phi> = set obj_ids\<rbrace>"
  apply (rule hoare_strengthen_post)
  apply (fact sys_init)
  apply (fastforce simp: injective_def)
  done
*)

end
