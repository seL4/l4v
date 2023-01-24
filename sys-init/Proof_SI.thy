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

lemma parse_bootinfo_sep:
  "\<lbrace>\<guillemotleft>((\<And>* (cptr, cap) \<in> set (zip [ustart .e. uend - 1] untyped_caps). (si_cnode_id, unat cptr) \<mapsto>c cap) \<and>*
      (\<And>* cptr \<in> set [fstart .e. fend - 1]. (si_cnode_id, unat cptr) \<mapsto>c NullCap)  \<and>*
      (\<And>* obj_id\<in>(\<Union>cap\<in>set untyped_caps. cap_free_ids cap). obj_id \<mapsto>o Untyped) \<and>* R)
     and K (bi_untypes bootinfo = (ustart, uend) \<and>
            bi_free_slots bootinfo = (fstart, fend) \<and>
            unat ustart < 2 ^ si_cnode_size \<and>
            unat (uend - 1) < 2 ^ si_cnode_size \<and>
            unat fstart < 2 ^ si_cnode_size \<and>
            unat (fend - 1) < 2 ^ si_cnode_size \<and>
            uend \<noteq> 0 \<and>
            fend \<noteq> 0 \<and>
            list_all is_full_untyped_cap untyped_caps \<and>
            length untyped_caps = unat uend - unat ustart) \<guillemotright>\<rbrace>
    parse_bootinfo bootinfo
   \<lbrace>\<lambda>rv.
    \<guillemotleft>((\<And>* (cptr, cap) \<in> set (zip (fst rv) untyped_caps). (si_cnode_id, unat cptr) \<mapsto>c cap) \<and>*
      (\<And>* cptr \<in> set (snd rv). (si_cnode_id, unat cptr) \<mapsto>c NullCap)  \<and>*
      (\<And>* obj_id\<in>(\<Union>cap\<in>set untyped_caps. cap_free_ids cap). obj_id \<mapsto>o Untyped) \<and>* R) and
     K (rv = ([fst (bi_untypes bootinfo) .e. snd (bi_untypes bootinfo) - 1],
              [fst (bi_free_slots bootinfo) .e. snd (bi_free_slots bootinfo) - 1]))\<guillemotright> \<rbrace>"
  apply (clarsimp simp: parse_bootinfo_def)
  apply (cases bootinfo, clarsimp)
  apply wp
  apply (clarsimp simp: zip_map1 comp_def split_beta')
  done

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
  apply (fastforce simp: object_at_def update_slots_def
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

lemma valid_case_prod':
  "(\<And>x y. \<lbrace>P x y\<rbrace> f x y \<lbrace>Q\<rbrace>) \<Longrightarrow> \<lbrace>P (fst v) (snd v)\<rbrace> case v of (x, y) \<Rightarrow> f x y \<lbrace>Q\<rbrace>"
  by (clarsimp split: prod.splits)

lemma le_list_all:
  "\<lbrakk>unat start < 2 ^ si_cnode_size; unat (end - 1) < 2 ^ si_cnode_size\<rbrakk>
   \<Longrightarrow> list_all (\<lambda>n. (n::32 word) < 2 ^ si_cnode_size) [start .e. end - 1]"
  apply (clarsimp simp: list_all_iff)
  apply (subst word_arith_power_alt)
  apply simp
  by (metis (no_types) dual_order.strict_trans2 unat_less_2_si_cnode_size)

lemma list_all_drop:
  "list_all P xs \<Longrightarrow> list_all P (drop n xs)"
  by (fastforce simp: list_all_iff dest: in_set_dropD)

lemma dom_map_of_zip':
  "length xs \<le> length ys \<Longrightarrow> dom (map_of (zip xs ys)) = set xs"
  apply (subst zip_take_length [symmetric])
  apply (subst dom_map_of_zip, simp+)
  done

(* FIXME: MOVE (Lib) *)
lemma in_zip_map: "p \<in> set xs \<Longrightarrow> length xs \<le> length ys \<Longrightarrow> map_of (zip xs ys) p \<noteq> None"
  using dom_map_of_zip' by blast

lemma map_of_list_allE:
  "map_of (zip ys xs) p = Some v \<Longrightarrow> distinct ys \<Longrightarrow> list_all P xs \<Longrightarrow> P v"
  apply (induct ys arbitrary: xs; clarsimp)
  by (meson in_set_zipE list_all_spec map_of_SomeD)

lemma card_eq_lengthI:
  "set xs = ys \<Longrightarrow> distinct xs \<Longrightarrow> length xs = card ys"
  by (induct xs arbitrary: ys; fastforce)

lemma length_filter_card:
  "\<lbrakk>s_list = sorted_list_of_set s; finite s\<rbrakk>
   \<Longrightarrow> length (filter P s_list) = card {x \<in> s. P x}"
  by (fastforce intro: card_eq_lengthI)


lemma sys_init_explicit:
  "\<lbrakk>well_formed spec;
   set obj_ids = dom (cdl_objects spec); distinct obj_ids;
   real_ids = [obj_id \<leftarrow> obj_ids. real_object_at obj_id spec];
   length obj_ids + length [obj\<leftarrow>obj_ids. cnode_or_tcb_at obj spec] +
   card (\<Union>(set ` get_frame_caps spec ` {obj. pd_at obj spec})) \<le> unat fend - unat fstart;
   length untyped_caps = unat uend - unat ustart;
   distinct_sets (map cap_free_ids untyped_caps);
   list_all is_full_untyped_cap untyped_caps;
   list_all well_formed_untyped_cap untyped_caps;
   list_all (\<lambda>c. \<not> is_device_cap c) untyped_caps;
   bi_untypes bootinfo = (ustart, uend);
   bi_free_slots bootinfo = (fstart, fend);
   unat ustart < 2 ^ si_cnode_size;
   unat (uend - 1) < 2 ^ si_cnode_size;
   unat fstart < 2 ^ si_cnode_size;
   unat (fend - 1) < 2 ^ si_cnode_size;
   uend \<noteq> 0; fend \<noteq> 0;
   [ustart .e. uend - 1] = untyped_cptrs;
   [fstart .e. fend - 1] = free_cptrs;
   (map_of (zip [obj\<leftarrow>obj_ids . cnode_or_tcb_at obj spec] (drop (length obj_ids) [fstart .e. fend - 1]))) = dup_caps
   \<rbrakk> \<Longrightarrow>
   \<lbrace>\<guillemotleft>(\<And>* (cptr, cap) \<in> set (zip untyped_cptrs untyped_caps). (si_cnode_id, unat cptr) \<mapsto>c cap) \<and>*
     (\<And>* cptr \<in> set free_cptrs. (si_cnode_id, unat cptr) \<mapsto>c NullCap)  \<and>*
     (\<And>* obj_id\<in>(\<Union>cap\<in>set untyped_caps. cap_free_ids cap). obj_id \<mapsto>o Untyped) \<and>*
    si_objects \<and>*
    si_irq_nodes spec \<and>*
    (SETSEPCONJ pd_id | pd_at pd_id spec.
      frame_duplicates_empty (make_frame_cap_map obj_ids (drop (length obj_ids) free_cptrs) spec)
                             pd_id spec) \<and>*
    R\<guillemotright>\<rbrace>
   init_system spec bootinfo obj_ids
  \<lbrace>\<lambda>_ s. \<exists>t.
    \<guillemotleft>objects_initialised spec t {obj_id. real_object_at obj_id spec} \<and>*
     irqs_initialised spec t (used_irqs spec) \<and>*
    (\<And>* cptr\<in>set (take (card (dom (cdl_objects spec))) free_cptrs). (si_cnode_id, unat cptr) \<mapsto>c NullCap) \<and>*
     si_caps_at t dup_caps spec False {obj_id. cnode_or_tcb_at obj_id spec} \<and>*
     si_objects \<and>*
     si_objects_extra_caps (dom (cdl_objects spec))
                            (free_cptrs :: 32 word list)
                            (untyped_cptrs :: 32 word list) spec \<and>*
    (SETSEPCONJ pd_id | pd_at pd_id spec.
      frame_duplicates_copied (make_frame_cap_map obj_ids (drop (length obj_ids) free_cptrs) spec)
                              pd_id spec t) \<and>*
    R\<guillemotright> s \<and>
    inj_on t (dom (cdl_objects spec)) \<and> dom t = set obj_ids\<rbrace>"
  supply [[unify_search_bound = 1000]]
  apply clarsimp
  apply (frule (1) le_list_all [where start = ustart])
  apply (frule (1) le_list_all [where start = fstart])
  apply (frule well_formed_objects_card)
  apply (insert distinct_card [symmetric, where xs ="[obj\<leftarrow>obj_ids . cnode_or_tcb_at obj spec]"], simp)
  apply (frule distinct_card [symmetric])
  apply (clarsimp simp: init_system_def, wp valid_case_prod')
            apply (rule hoare_vcg_ex_lift, rename_tac t, rule_tac t=t in start_threads_sep [sep_wandise], simp)
           apply (rule hoare_vcg_ex_lift, rename_tac t, rule_tac t=t and
                                                  free_cptrs="[fstart .e. fend - 1]" in init_cspace_sep [sep_wandise])
          apply (rule hoare_vcg_ex_lift, rename_tac t, rule_tac t=t in init_tcbs_sep [sep_wandise])
         apply (rule hoare_vcg_ex_lift, rename_tac t, rule_tac t=t in init_vspace_sep [sep_wandise])
        apply (rule hoare_vcg_ex_lift, rename_tac t, rule_tac t=t in init_pd_asids_sep [sep_wandise])
       apply (rule hoare_vcg_ex_lift, rename_tac t, rule_tac t=t and dev=False in init_irqs_sep [sep_wandise])
      apply (rule hoare_vcg_ex_lift, rename_tac t, rule_tac t=t and dev=False and
                                             untyped_cptrs = "[ustart .e. uend - 1]" and
                                             free_cptrs_orig = "[fstart .e. fend - 1]" in duplicate_caps_sep [sep_wandise])
     apply (rule create_irq_caps_sep [where dev = False,sep_wandise,
            where free_cptrs_orig = "[fstart .e. fend - 1]"
              and untyped_cptrs = "[ustart .e. uend - 1]"
              and orig_caps = "map_of (zip [obj\<leftarrow>obj_ids. real_object_at obj spec]
                                           [fstart .e. fend - 1])"
              and spec = spec])
    apply (wp sep_wp: create_objects_sep [where untyped_caps = untyped_caps and dev = False])
   apply (wp sep_wp: parse_bootinfo_sep [where fstart = fstart
                                           and fend = fend
                                           and ustart = ustart
                                           and uend = uend
                                           and untyped_caps = untyped_caps])
  apply (subst objects_initialised_by_parts, assumption)
  apply (subst objects_empty_by_parts, assumption)+
  apply (subst objects_empty_objects_initialised_capless)+
  apply (clarsimp simp: linorder_not_le)
  apply (intro conjI allI impI pred_conjI | sep_cancel+)+
         apply fastforce
        apply (clarsimp simp: less_diff_conv)
        apply (rule list_all_drop, erule (1) le_list_all)
       apply clarsimp
       apply (subgoal_tac "map_of (zip (filter (\<lambda>obj. real_object_at obj spec) obj_ids) free_cptrs)
                                  p \<noteq> None")
        apply clarsimp
        apply (erule map_of_list_allE)
         apply (fastforce intro!: List.distinct_filter)
        apply (fastforce intro!: le_list_all)
       apply (rule in_zip_map)
        apply clarsimp
        apply (fastforce dest!: real_object_not_irq_node(3))
       apply (insert length_filter_le[where xs = obj_ids and P="\<lambda>obj. real_object_at obj spec"],
              fastforce)[1]
      apply (erule (1) le_list_all)
     apply (rule list_all_drop, erule (1) le_list_all)
    apply simp
   apply (subst dom_map_of_zip')
    apply (insert length_filter_le [where xs = obj_ids and P="\<lambda>obj. real_object_at obj spec"],
           fastforce)[1]
   apply simp
  apply (erule (1) le_list_all)
  done

(**************************************************
 * The top level lemma for system initialisation. *
 **************************************************)
(* FIXME, make the acquiring of the object_ids part of sys_init, not a parameter. *)

lemma sys_init:
  "\<lbrakk>well_formed spec; obj_ids = sorted_list_of_set (dom (cdl_objects spec))\<rbrakk> \<Longrightarrow>
   \<lbrace>\<guillemotleft>valid_boot_info bootinfo spec \<and>* R\<guillemotright>\<rbrace>
    init_system spec bootinfo obj_ids
   \<lbrace>\<lambda>_ s. \<exists>t.
    \<guillemotleft>objects_initialised spec t {obj_id. real_object_at obj_id spec} \<and>*
     irqs_initialised spec t (used_irqs spec) \<and>*
     si_final_objects spec t \<and>*
     (EXS map. (SETSEPCONJ pd_id | pd_at pd_id spec. frame_duplicates_copied map pd_id spec t)) \<and>*
     R\<guillemotright> s \<and>
     inj_on t (set obj_ids) \<and> dom t = set obj_ids\<rbrace>"
  apply (insert distinct_card [where xs = "[obj\<leftarrow>obj_ids . cnode_or_tcb_at obj spec]"], simp)
  apply (clarsimp simp: valid_boot_info_def si_final_objects_def
                        sep_conj_exists sep_conj_assoc)
  apply (subst ex_conj_increase)+
  apply (rule hoare_ex_pre)+
  apply (rule hoare_grab_asm)+
  apply (rule hoare_chain)
    apply (rule sys_init_explicit[where obj_ids="sorted_list_of_set (dom (cdl_objects spec))" and R=R],
          (assumption|simp add: unat_less_2_si_cnode_size' length_filter_card)+)
   apply sep_solve
  apply clarsimp
  apply (rule_tac x=t in exI)
  apply (clarsimp)
  apply (clarsimp simp: si_objects_extra_caps_def si_caps_at_def
                        sep_conj_exists sep_conj_assoc)
  apply (rule_tac x="(map_of (zip [obj \<leftarrow> obj_ids. cnode_or_tcb_at obj spec]
                                  (drop (length obj_ids) [fstart .e. fend - 1])))" in exI)
  apply (rule_tac x="[x .e. xa - 1]" in exI)
  apply (rule_tac x="[fstart .e. fend - 1]" in exI)
  apply (rule_tac x=untyped_capsa in exI)
  apply (rule_tac x=all_available_ids in exI)
  apply (rule_tac x="make_frame_cap_map obj_ids (drop (card (dom (cdl_objects spec)))
                                                      [fstart .e. fend - 1]) spec" in exI)
  apply (clarsimp simp: sep_conj_ac)
  done

definition injective :: "('a \<Rightarrow> 'b option) \<Rightarrow> bool"
where "injective f \<equiv> inj_on f (dom f)"

lemma sys_init_paper:
  "\<lbrakk>well_formed spec; obj_ids = sorted_list_of_set (dom (cdl_objects spec))\<rbrakk> \<Longrightarrow>
   \<lbrace>\<guillemotleft>valid_boot_info bootinfo spec \<and>* R\<guillemotright>\<rbrace>
   init_system spec bootinfo obj_ids
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

end
