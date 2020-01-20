(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory CompoundCTypes
imports Vanilla32 Padding
begin

definition empty_typ_info :: "typ_name \<Rightarrow> 'a typ_info" where
  "empty_typ_info tn \<equiv> TypDesc (TypAggregate []) tn"

primrec
  extend_ti :: "'a typ_info \<Rightarrow> 'a typ_info \<Rightarrow> field_name \<Rightarrow> 'a typ_info" and
  extend_ti_struct :: "'a field_desc typ_struct \<Rightarrow> 'a typ_info \<Rightarrow> field_name \<Rightarrow> 'a field_desc typ_struct"
where
  et0: "extend_ti (TypDesc st nm) t fn  = TypDesc (extend_ti_struct st t fn) nm"

| et1: "extend_ti_struct (TypScalar n sz algn) t fn = TypAggregate [DTPair t fn]"
| et2: "extend_ti_struct (TypAggregate ts) t fn = TypAggregate (ts@[DTPair t fn])"

lemma aggregate_empty_typ_info [simp]:
  "aggregate (empty_typ_info tn)"
  by (simp add: empty_typ_info_def)

lemma aggregate_extend_ti [simp]:
  "aggregate (extend_ti tag t f)"
  apply(cases tag)
  apply(rename_tac typ_struct xs)
  apply(case_tac typ_struct, auto)
  done

definition update_desc :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'b field_desc \<Rightarrow> 'a field_desc" where
  "update_desc f_ab f_upd_ab d \<equiv> \<lparr> field_access =  (field_access d) \<circ>  f_ab,
                                   field_update = \<lambda>bs v. f_upd_ab (field_update d bs (f_ab v)) v \<rparr>"

definition adjust_ti :: "'b typ_info \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a typ_info" where
  "adjust_ti t f_ab f_upd_ab \<equiv> map_td (\<lambda>n algn. update_desc f_ab f_upd_ab) t"

lemma typ_desc_size_update_ti [simp]:
  "(size_td (adjust_ti t f g) = size_td t)"
  by (simp add: adjust_ti_def)

definition fg_cons :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "fg_cons f g \<equiv>
     (\<forall>bs v. f (g bs v) = bs) \<and> (\<forall>bs bs' v. g bs (g bs' v) = g bs v) \<and> (\<forall>v. g (f v) v = v)"

lemma export_tag_adjust_ti [simp]:
  "\<forall>bs. fg_cons f g  \<longrightarrow> wf_fd t \<longrightarrow>
    export_uinfo (adjust_ti t f g) = export_uinfo t"
  "\<forall>bs. fg_cons f g \<longrightarrow> wf_fd_struct st \<longrightarrow>
    map_td_struct field_norm (map_td_struct (\<lambda>n algn d. update_desc f g d) st) =
    map_td_struct field_norm st"
  "\<forall>bs. fg_cons f g \<longrightarrow> wf_fd_list ts \<longrightarrow>
    map_td_list field_norm (map_td_list (\<lambda>n algn d. update_desc f g d) ts) =
    map_td_list field_norm ts"
  "\<forall>bs. fg_cons f g \<longrightarrow> wf_fd_pair x \<longrightarrow>
    map_td_pair field_norm (map_td_pair (\<lambda>n algn d. update_desc f g d) x) =
    map_td_pair field_norm x"
  unfolding adjust_ti_def
  by (induct t and st and ts and x, all \<open>clarsimp simp: export_uinfo_def\<close>)
     (fastforce simp: update_desc_def field_norm_def fg_cons_def fd_cons_struct_def
                      fd_cons_access_update_def fd_cons_desc_def)

definition ti_typ_combine ::
  "'b::c_type itself \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> field_name \<Rightarrow> 'a typ_info \<Rightarrow> 'a typ_info"
  where
  "ti_typ_combine t_b f_ab f_upd_ab fn tag \<equiv>
     let nf = adjust_ti (typ_info_t TYPE('b)) f_ab f_upd_ab in extend_ti tag nf fn"

primrec
  padding_fields :: "'a typ_desc \<Rightarrow> field_name list" and
  padding_fields_struct :: "'a typ_struct \<Rightarrow> field_name list"
where
  pf0: "padding_fields (TypDesc st tn) = padding_fields_struct st"

| pf1: "padding_fields_struct (TypScalar n algn d) = []"
| pf2: "padding_fields_struct (TypAggregate xs) = filter (\<lambda>x. hd x = CHR ''!'') (map dt_snd xs)"

primrec
  non_padding_fields :: "'a typ_desc \<Rightarrow> field_name list" and
  non_padding_fields_struct :: "'a typ_struct \<Rightarrow> field_name list"
where
  npf0: "non_padding_fields (TypDesc st tn) = non_padding_fields_struct st"

| npf1: "non_padding_fields_struct (TypScalar n algn d) = []"
| npf2: "non_padding_fields_struct (TypAggregate xs) = filter (\<lambda>x. hd x \<noteq> CHR ''!'') (map dt_snd xs)"

definition field_names_list :: "'a typ_desc \<Rightarrow> field_name list" where
  "field_names_list tag \<equiv> non_padding_fields tag @ padding_fields tag"

definition ti_pad_combine :: "nat \<Rightarrow> 'a typ_info \<Rightarrow> 'a typ_info" where
  "ti_pad_combine n tag \<equiv>
     let
       fn = foldl (@) ''!pad_'' (field_names_list tag);
       td = \<lparr> field_access = \<lambda>v. id, field_update = \<lambda>bs. id \<rparr>;
       nf = TypDesc (TypScalar n 0 td) ''!pad_typ''
     in extend_ti tag nf fn"

lemma aggregate_ti_pad_combine [simp]:
  "aggregate (ti_pad_combine n tag)"
  by (simp add: ti_pad_combine_def Let_def)

definition ti_typ_pad_combine ::
  "'b::c_type itself \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> field_name \<Rightarrow> 'a typ_info \<Rightarrow> 'a typ_info"
  where
  "ti_typ_pad_combine t_b f_ab f_upd_ab fn tag \<equiv>
     let
       pad = padup (align_of TYPE('b)) (size_td tag);
       ntag = if 0 < pad then ti_pad_combine pad tag else tag
     in
       ti_typ_combine t_b f_ab f_upd_ab fn ntag"

definition final_pad :: "'a typ_info \<Rightarrow> 'a typ_info" where
  "final_pad tag \<equiv>
     let n = padup (2^align_td tag) (size_td  tag) in if 0 < n then ti_pad_combine n tag else tag"

lemma field_names_list_empty_typ_info [simp]:
  "set (field_names_list (empty_typ_info tn)) = {}"
  by (simp add: empty_typ_info_def field_names_list_def)

lemma field_names_list_extend_ti [simp]:
  "set (field_names_list (extend_ti tag t fn)) = set (field_names_list tag) \<union> {fn}"
  unfolding field_names_list_def
  apply(case_tac tag)
  apply(rename_tac typ_struct xs)
  apply(case_tac typ_struct; simp)
  done

lemma field_names_list_ti_typ_combine [simp]:
  "set (field_names_list (ti_typ_combine t_b f_ab f_upd_ab fn tag))
     = set (field_names_list tag) \<union> {fn}"
  by (clarsimp simp: ti_typ_combine_def Let_def)

lemma field_names_list_ti_pad_combine [simp]:
  "set (field_names_list (ti_pad_combine n tag))
     = set (field_names_list tag) \<union> {foldl (@) ''!pad_'' (field_names_list tag)}"
  by (clarsimp simp: ti_pad_combine_def Let_def)

\<comment> \<open>matches on padding\<close>
lemma hd_string_hd_fold_eq [simp, rule_format]:
  "\<lbrakk> s \<noteq> []; hd s = CHR ''!'' \<rbrakk> \<Longrightarrow> hd (foldl (@) s xs) = CHR ''!''"
  by (induct xs arbitrary: s; clarsimp)

lemma field_names_list_ti_typ_pad_combine [simp]:
  "hd x \<noteq> CHR ''!'' \<Longrightarrow>
      x \<in> set (field_names_list (ti_typ_pad_combine t_b f_ab f_upd_ab fn tag))
          = (x \<in> set (field_names_list tag) \<union> {fn})"
  by (auto simp: ti_typ_pad_combine_def Let_def)

lemma wf_desc_empty_typ_info [simp]:
  "wf_desc (empty_typ_info tn)"
  by (simp add: empty_typ_info_def)

lemma wf_desc_extend_ti:
  "\<lbrakk> wf_desc tag; wf_desc t; f \<notin> set (field_names_list tag) \<rbrakk> \<Longrightarrow>
      wf_desc (extend_ti tag t f)"
  unfolding field_names_list_def
  apply(cases tag, rename_tac typ_struct xs)
  apply(case_tac typ_struct; clarsimp)
  done

lemma foldl_append_length:
  "length (foldl (@) s xs) \<ge> length s"
  apply(induct xs arbitrary: s, clarsimp)
  apply(rename_tac a list s)
  apply(drule_tac x="s@a" in meta_spec)
  apply clarsimp
  done

lemma foldl_append_nmem:
  "s \<noteq> [] \<Longrightarrow> foldl (@) s xs \<notin> set xs"
  apply(induct xs arbitrary: s, clarsimp)
  apply(rename_tac a list s)
  apply(drule_tac x="s@a" in meta_spec)
  apply clarsimp
  apply(subgoal_tac "length (foldl (@) (s@a) list) \<ge> length (s@a)")
   apply simp
  apply(rule foldl_append_length)
  done

lemma wf_desc_ti_pad_combine:
  "wf_desc tag \<Longrightarrow> wf_desc (ti_pad_combine n tag)"
  apply(clarsimp simp: ti_pad_combine_def Let_def)
  apply(erule wf_desc_extend_ti)
   apply simp
  apply(rule foldl_append_nmem, simp)
  done

lemma wf_desc_adjust_ti [simp]:
  "wf_desc (adjust_ti t f g) = wf_desc (t::'a typ_info)"
  by (simp add: adjust_ti_def wf_desc_map)

lemma wf_desc_ti_typ_combine:
  "\<lbrakk> wf_desc tag; fn \<notin> set (field_names_list tag) \<rbrakk> \<Longrightarrow>
    wf_desc (ti_typ_combine (t_b::'a::wf_type itself) f_ab f_upd_ab fn tag)"
  by (fastforce simp: ti_typ_combine_def Let_def elim: wf_desc_extend_ti)

lemma wf_desc_ti_typ_pad_combine:
  "\<lbrakk> wf_desc tag;  fn \<notin> set (field_names_list tag); hd fn \<noteq> CHR ''!'' \<rbrakk> \<Longrightarrow>
   wf_desc (ti_typ_pad_combine (t_b::'a::wf_type itself) f_ab f_upd_ab fn tag)"
  unfolding ti_typ_pad_combine_def Let_def
  by (auto intro!: wf_desc_ti_typ_combine wf_desc_ti_pad_combine)

lemma wf_desc_final_pad:
  "wf_desc tag \<Longrightarrow> wf_desc (final_pad tag)"
  by (auto simp: final_pad_def Let_def elim: wf_desc_ti_pad_combine)

lemma wf_size_desc_extend_ti:
  "\<lbrakk> wf_size_desc tag; wf_size_desc t \<rbrakk> \<Longrightarrow> wf_size_desc (extend_ti tag t fn)"
  apply(cases tag, rename_tac typ_struct list)
  apply(case_tac typ_struct, auto)
  done

lemma wf_size_desc_ti_pad_combine:
  "\<lbrakk> wf_size_desc tag; 0 < n \<rbrakk> \<Longrightarrow> wf_size_desc (ti_pad_combine n tag)"
  by (fastforce simp: ti_pad_combine_def Let_def elim: wf_size_desc_extend_ti)

lemma wf_size_desc_adjust_ti:
  "wf_size_desc (adjust_ti t f g) = wf_size_desc (t::'a typ_info)"
  by (simp add: adjust_ti_def wf_size_desc_map)

lemma wf_size_desc_ti_typ_combine:
  "wf_size_desc tag \<Longrightarrow> wf_size_desc (ti_typ_combine (t_b::'a::wf_type itself) f_ab f_upd_ab fn tag)"
  by (fastforce simp: wf_size_desc_adjust_ti ti_typ_combine_def Let_def elim: wf_size_desc_extend_ti)

lemma wf_size_desc_ti_typ_pad_combine:
  "wf_size_desc tag \<Longrightarrow>
    wf_size_desc (ti_typ_pad_combine (t_b::'a::wf_type itself) f_ab f_upd_ab fn tag)"
  by (auto simp: ti_typ_pad_combine_def Let_def
           intro: wf_size_desc_ti_typ_combine
           elim: wf_size_desc_ti_pad_combine)

lemma wf_size_desc_ti_typ_combine_empty [simp]:
  "wf_size_desc (ti_typ_combine (t_b::'a::wf_type itself) f_ab f_upd_ab fn (empty_typ_info tn))"
  by (clarsimp simp: ti_typ_combine_def Let_def empty_typ_info_def wf_size_desc_adjust_ti)

lemma wf_size_desc_ti_typ_pad_combine_empty [simp]:
  "wf_size_desc (ti_typ_pad_combine (t_b::'a::wf_type itself) f_ab f_upd_ab fn
      (empty_typ_info tn))"
  by (clarsimp simp: ti_typ_pad_combine_def Let_def ti_typ_combine_def empty_typ_info_def
                     ti_pad_combine_def wf_size_desc_adjust_ti)

lemma wf_size_desc_final_pad:
  "wf_size_desc tag \<Longrightarrow> wf_size_desc (final_pad tag)"
  by (fastforce simp: final_pad_def Let_def elim: wf_size_desc_ti_pad_combine)

lemma wf_fdp_set_comp_simp [simp]:
  "wf_fdp {(a, n # b) |a b. (a, b) \<in> tf_set t} = wf_fdp (tf_set t)"
  unfolding wf_fdp_def by fastforce

lemma lf_set_adjust_ti':
  "\<forall>d fn. d \<in> lf_set (map_td (\<lambda>n algn d. update_desc f g d) t) fn \<longrightarrow>
      (\<exists>y. lf_fd d=update_desc f g (lf_fd y) \<and> lf_sz d=lf_sz y \<and> lf_fn d=lf_fn y \<and> y \<in> lf_set t fn)"
  "\<forall>d fn. d \<in> lf_set_struct (map_td_struct (\<lambda>n algn d. update_desc f g d) st) fn \<longrightarrow>
      (\<exists>y. lf_fd d=update_desc f g (lf_fd y) \<and> lf_sz d=lf_sz y \<and> lf_fn d=lf_fn y \<and> y \<in> lf_set_struct st fn)"
  "\<forall>d fn. d \<in> lf_set_list (map_td_list (\<lambda>n algn d. update_desc f g d) ts) fn \<longrightarrow>
      (\<exists>y. lf_fd d=update_desc f g (lf_fd y) \<and> lf_sz d=lf_sz y \<and> lf_fn d=lf_fn y \<and> y \<in> lf_set_list ts fn)"
  "\<forall>d fn. d \<in> lf_set_pair (map_td_pair (\<lambda>n algn d. update_desc f g d) x) fn \<longrightarrow>
      (\<exists>y. lf_fd d=update_desc f g (lf_fd y) \<and> lf_sz d=lf_sz y \<and> lf_fn d=lf_fn y \<and> y \<in> lf_set_pair x fn)"
  unfolding update_desc_def
  by (induct t and st and ts and x) fastforce+

lemma lf_set_adjust_ti:
  "\<lbrakk> d \<in> lf_set (adjust_ti t f g) fn; \<And>y. g (f y) y = y \<rbrakk> \<Longrightarrow>
      (\<exists>y. lf_fd d=update_desc f g (lf_fd y) \<and> lf_sz d=lf_sz y \<and> lf_fn d=lf_fn y \<and> y \<in> lf_set t fn)"
  by (simp add: lf_set_adjust_ti' adjust_ti_def)

lemma fd_cons_struct_id_simp [simp]:
  "fd_cons_struct (TypScalar n algn \<lparr>field_access = \<lambda>v. id, field_update = \<lambda>bs. id\<rparr>)"
  by (auto simp: fd_cons_struct_def fd_cons_double_update_def
                 fd_cons_update_access_def fd_cons_access_update_def fd_cons_length_def
                 fd_cons_update_normalise_def fd_cons_desc_def)

lemma field_desc_adjust_ti:
  "fg_cons f g \<longrightarrow>
     field_desc (adjust_ti (t::'a typ_info) f g) =
     update_desc  f g (field_desc t)"
  "fg_cons f g \<longrightarrow>
     field_desc_struct (map_td_struct (\<lambda>n algn d. update_desc  f g d) st) =
     update_desc  f g (field_desc_struct st)"
  "fg_cons f g \<longrightarrow>
     field_desc_list (map_td_list (\<lambda>n algn d. update_desc f g d) ts) =
     update_desc  f g (field_desc_list ts)"
  "fg_cons f g \<longrightarrow>
     field_desc_pair (map_td_pair (\<lambda>n algn d. update_desc f g d) x) =
     update_desc  f g (field_desc_pair x)"
  unfolding adjust_ti_def
  by (induct t and st and ts and x) (fastforce simp: fg_cons_def update_desc_def)+

lemma update_ti_adjust_ti:
  "fg_cons f g \<Longrightarrow> update_ti_t (adjust_ti t f g) bs v = g (update_ti_t t bs (f v)) v"
  using field_desc_adjust_ti(1) [of f g t]
  by (clarsimp simp: update_desc_def)

declare field_desc_def [simp del]

lemma aggregate_ti_typ_combine [simp]:
  "aggregate (ti_typ_combine t_b f_ab f_upd_ab fn tag)"
  by (simp add: ti_typ_combine_def Let_def)

lemma aggregate_ti_typ_pad_combine [simp]:
  "aggregate (ti_typ_pad_combine t_b f_ab f_upd_ab fn tag)"
  by (simp add: ti_typ_pad_combine_def Let_def)

lemma align_of_empty_typ_info [simp]:
  "align_td (empty_typ_info tn) = 0"
  by (simp add: empty_typ_info_def)

lemma align_of_tag_list [simp]:
  "align_td_list (xs @ [DTPair t fn]) = max (align_td_list xs) (align_td t)"
  by (induct_tac xs) auto

lemma align_of_extend_ti [simp]:
  "aggregate ti \<Longrightarrow> align_td (extend_ti ti t fn) = max (align_td ti) (align_td t)"
  apply (cases ti, rename_tac typ_struct xs)
  apply (case_tac typ_struct; clarsimp)
  done

lemma align_of_adjust_ti [simp]:
  "align_td (adjust_ti t f g) = align_td (t::'a typ_info)"
  by (simp add: adjust_ti_def)

lemma align_of_ti_typ_combine [simp]:
  "aggregate ti \<Longrightarrow>
     align_td (ti_typ_combine (t::'a::c_type itself) f g fn ti) =
     max (align_td ti) (align_td (typ_info_t (TYPE('a))))"
  by (clarsimp simp: ti_typ_combine_def Let_def align_of_def)

lemma align_of_ti_pad_combine [simp]:
  "aggregate ti \<Longrightarrow> align_td (ti_pad_combine n ti) = align_td ti"
  by (clarsimp simp: ti_pad_combine_def Let_def max_def)

lemma align_of_final_pad:
  "aggregate ti \<Longrightarrow> align_td (final_pad ti) = align_td ti"
  by (auto simp: final_pad_def Let_def max_def)

lemma align_of_ti_typ_pad_combine [simp]:
  "aggregate ti \<Longrightarrow>
     align_td (ti_typ_pad_combine (t::'a::c_type itself) f g fn ti) =
     max (align_td ti) (align_td (typ_info_t TYPE('a)))"
  by (clarsimp simp: ti_typ_pad_combine_def Let_def)

definition fu_s_comm_set :: "(byte list \<Rightarrow> 'a \<Rightarrow> 'a) set \<Rightarrow> (byte list \<Rightarrow> 'a \<Rightarrow> 'a) set \<Rightarrow> bool"
  where
  "fu_s_comm_set X Y \<equiv> \<forall>x y. x \<in> X \<and> y \<in> Y \<longrightarrow> (\<forall>v bs bs'. x bs (y bs' v) = y bs' (x bs v))"

lemma fc_empty_ti [simp]:
  "fu_commutes (update_ti_t (empty_typ_info tn)) f"
  by (auto simp: fu_commutes_def empty_typ_info_def)

lemma fc_extend_ti:
  "\<lbrakk> fu_commutes (update_ti_t s) h; fu_commutes (update_ti_t t) h \<rbrakk>
      \<Longrightarrow> fu_commutes (update_ti_t (extend_ti s t fn)) h"
  apply(case_tac s, rename_tac typ_struct xs)
  apply(case_tac typ_struct, auto simp: fu_commutes_def)
  done

lemma fc_update_ti:
  "\<lbrakk> fu_commutes (update_ti_t ti) h; fg_cons f g;
     \<forall>v bs bs'. g bs (h bs' v) = h bs' (g bs v); \<forall>bs v. f (h bs v) = f v  \<rbrakk>
   \<Longrightarrow> fu_commutes (update_ti_t (adjust_ti t f g)) h"
  by (auto simp: fu_commutes_def update_ti_adjust_ti)

lemma fc_ti_typ_combine:
  "\<lbrakk> fu_commutes (update_ti_t ti) h; fg_cons f g;
     \<forall>v bs bs'. g bs (h bs' v) = h bs' (g bs v); \<forall>bs v. f (h bs v) = f v \<rbrakk>
   \<Longrightarrow> fu_commutes (update_ti_t (ti_typ_combine t f g fn ti)) h"
  apply(clarsimp simp: ti_typ_combine_def Let_def)
  apply(rule fc_extend_ti, assumption)
  apply(rule fc_update_ti; simp)
  done

lemma fc_ti_pad_combine:
  "fu_commutes (update_ti_t ti) f \<Longrightarrow> fu_commutes (update_ti_t (ti_pad_combine n ti)) f"
  apply(clarsimp simp: ti_pad_combine_def Let_def)
  apply(rule fc_extend_ti, assumption)
  apply(auto simp: fu_commutes_def)
  done

lemma fc_ti_typ_pad_combine:
  "\<lbrakk> fu_commutes (update_ti_t ti) h; fg_cons f g;
     \<forall>v bs bs'. g bs (h bs' v) = h bs' (g bs v); \<forall>bs v. f (h bs v) = f v \<rbrakk>
   \<Longrightarrow> fu_commutes (update_ti_t (ti_typ_pad_combine t f g fn ti)) h"
  apply(clarsimp simp: ti_typ_pad_combine_def Let_def)
  apply(rule conjI; clarsimp)
   apply(rule fc_ti_typ_combine; assumption?)
   apply(erule fc_ti_pad_combine)
  apply(erule (3) fc_ti_typ_combine)
  done

definition fu_eq_mask :: "'a typ_info \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "fu_eq_mask ti f \<equiv>
     \<forall>bs v v'. length bs = size_td ti \<longrightarrow> update_ti_t ti bs (f v) = update_ti_t ti bs (f v')"

lemma fu_eq_mask:
  "\<lbrakk> length bs = size_td ti; fu_eq_mask ti id  \<rbrakk> \<Longrightarrow>
      update_ti_t ti bs v = update_ti_t ti bs w"
 by (clarsimp simp: fu_eq_mask_def update_ti_t_def)

lemma fu_eq_mask_ti_pad_combine:
  "\<lbrakk> fu_eq_mask ti f; aggregate ti \<rbrakk> \<Longrightarrow> fu_eq_mask (ti_pad_combine n ti) f"
  unfolding ti_pad_combine_def Let_def
  apply(case_tac ti, rename_tac typ_struct xs)
  apply(case_tac typ_struct, auto simp: fu_eq_mask_def update_ti_list_t_def)
  done

lemma fu_eq_mask_final_pad:
  "\<lbrakk> fu_eq_mask ti f; aggregate ti \<rbrakk> \<Longrightarrow> fu_eq_mask (final_pad ti) f"
  by (fastforce simp: final_pad_def Let_def elim: fu_eq_mask_ti_pad_combine)

definition upd_local :: "('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "upd_local g \<equiv> \<forall>j k v v'. g k v = g k v' \<longrightarrow> g j v = g j v'"

lemma fg_cons_upd_local:
  "fg_cons f g \<Longrightarrow> upd_local g"
  apply(clarsimp simp: fg_cons_def upd_local_def)
  apply(drule_tac f="g j" in arg_cong)
  apply simp
  done

lemma fu_eq_mask_ti_typ_combine:
  "\<lbrakk> fu_eq_mask ti (\<lambda>v. (g (f undefined) (h v))); fg_cons f g;
      fu_commutes (update_ti_t ti) g; aggregate ti \<rbrakk> \<Longrightarrow>
      fu_eq_mask (ti_typ_combine (t::'a::mem_type itself) f g fn ti) h"
  apply(frule fg_cons_upd_local)
  apply(clarsimp simp: ti_typ_combine_def Let_def)
  apply(case_tac ti, rename_tac typ_struct xs)
  apply(case_tac typ_struct; clarsimp)
  apply(rename_tac xs')
  apply(clarsimp simp: fu_eq_mask_def update_ti_adjust_ti)
  apply(clarsimp simp: update_ti_list_t_def size_of_def)
  apply(rule conjI; clarsimp)
   prefer 2
   apply fastforce
  apply(subst upd [where w="f undefined"])
   apply(simp add: size_of_def)
  apply(subst upd [where w="f undefined" and v="f (h v')" for v'])
   apply(simp add: size_of_def)
  apply(subgoal_tac "fu_commutes (\<lambda>v. update_ti_list_t xs' v) g")
   apply(clarsimp simp: fu_commutes_def)
   apply(frule_tac x="h v" in spec)
   apply(rotate_tac -1)
   apply(drule_tac x="take (size_td_list xs') bs" in spec)
   apply(drule_tac x="update_ti_t (typ_info_t TYPE('a))
                                  (drop (size_td_list xs') bs) (f undefined)" in spec)
   apply(frule_tac x="h v'" in spec)
   apply(rotate_tac -1)
   apply(drule_tac x="take (size_td_list xs') bs" in spec)
   apply(drule_tac x="update_ti_t (typ_info_t TYPE('a))
                                  (drop (size_td_list xs') bs) (f undefined)" in spec)
   apply(clarsimp simp: update_ti_list_t_def)
   apply(drule_tac x="take (size_td_list xs') bs" in spec)
   apply simp
   apply(rotate_tac -1)
   apply(drule_tac x="v" in spec)
   apply(rotate_tac -1)
   apply(drule_tac x="v'" in spec)
   apply(frule_tac x="h v" in spec)
   apply(drule_tac x="(take (size_td_list xs') bs)" in spec)
   apply(drule_tac x="f undefined" in spec)
   apply(frule_tac x="h v'" in spec)
   apply(drule_tac x="(take (size_td_list xs') bs)" in spec)
   apply(drule_tac x="f undefined" in spec)
   apply(thin_tac "\<forall>v bs bs'. X v bs bs'" for X)
   apply simp
   apply(unfold upd_local_def)
   apply fast
  apply(unfold fu_commutes_def)
  apply(thin_tac "\<forall>bs. X bs" for X)
  apply(thin_tac "\<forall>x y z a. X x y z a" for X)
  apply(clarsimp simp: update_ti_list_t_def)
  done

lemma fu_eq_mask_ti_typ_pad_combine:
  "\<lbrakk> fu_eq_mask ti (\<lambda>v. (g (f undefined) (h v))); fg_cons f g;
      fu_commutes (update_ti_t ti) g; aggregate ti \<rbrakk> \<Longrightarrow>
      fu_eq_mask (ti_typ_pad_combine (t::'a::mem_type itself) f g fn ti) h"
  by (fastforce simp: ti_typ_pad_combine_def Let_def
                intro: fu_eq_mask_ti_typ_combine fu_eq_mask_ti_pad_combine fc_ti_pad_combine)

lemma fu_eq_mask_empty_typ_info_g:
  "\<exists>k. \<forall>v. f v = k \<Longrightarrow> fu_eq_mask t f"
  by (auto simp: fu_eq_mask_def)

lemma fu_eq_mask_empty_typ_info:
  "\<forall>v. f v = undefined \<Longrightarrow> fu_eq_mask t f"
 by (auto simp: fu_eq_mask_def)

lemma size_td_extend_ti:
  "aggregate s \<Longrightarrow> size_td (extend_ti s t fn) = size_td s + size_td t"
  by (cases s, rename_tac typ_struct xs) (case_tac typ_struct; simp)

lemma size_td_ti_pad_combine:
  "aggregate ti \<Longrightarrow> size_td (ti_pad_combine n ti) = n + size_td ti"
  unfolding ti_pad_combine_def Let_def by (simp add: size_td_extend_ti)

lemma align_of_dvd_size_of_final_pad [simp]:
  "aggregate ti \<Longrightarrow> 2^align_td (final_pad ti) dvd size_td (final_pad ti)"
  unfolding final_pad_def Let_def
  by (fastforce simp: size_td_ti_pad_combine ac_simps padup_dvd intro: dvd_padup_add)

lemma size_td_lt_ti_pad_combine:
  "aggregate t \<Longrightarrow> size_td (ti_pad_combine n t) = size_td t + n"
  by (metis add.commute size_td_ti_pad_combine)

lemma size_td_lt_ti_typ_combine:
  "aggregate ti \<Longrightarrow>
    size_td (ti_typ_combine (t::'b::c_type itself) f g fn ti) =
    size_td ti + size_td (typ_info_t TYPE('b))"
  by (clarsimp simp: ti_typ_combine_def Let_def size_td_extend_ti)

lemma size_td_lt_ti_typ_pad_combine:
  "aggregate ti  \<Longrightarrow>
      size_td (ti_typ_pad_combine (t::'b::c_type itself) f g fn ti) =
        (let k = size_td ti in
           k + size_td (typ_info_t TYPE('b)) + padup (2^(align_td (typ_info_t TYPE('b)))) k)"
  unfolding ti_typ_pad_combine_def Let_def
  by (auto simp: size_td_lt_ti_typ_combine size_td_ti_pad_combine align_of_def)

lemma size_td_lt_final_pad:
  "aggregate tag \<Longrightarrow>
   size_td (final_pad tag) = (let k=size_td tag in k + padup (2^align_td tag) k)"
  by (auto simp: final_pad_def Let_def size_td_ti_pad_combine)

lemma size_td_empty_typ_info [simp]:
  "size_td (empty_typ_info tn) = 0"
  by (clarsimp simp: empty_typ_info_def)

lemma wf_lf_empty_typ_info [simp]:
  "wf_lf {}"
  by (auto simp: wf_lf_def empty_typ_info_def)

lemma lf_fn_disj_fn:
  "fn \<notin> set (field_names_list (TypDesc (TypAggregate xs) tn)) \<Longrightarrow>
   lf_fn ` lf_set_list xs [] \<inter> lf_fn ` lf_set t [fn] = {}"
  apply(induct xs arbitrary: fn t tn, clarsimp)
  apply(rename_tac a list fn t tn)
  apply(case_tac a, clarsimp)
  apply(drule_tac x=fn in meta_spec)
  apply(drule_tac x=t in meta_spec)
  apply(drule_tac x=tn in meta_spec)
  apply(drule meta_mp, fastforce simp: field_names_list_def split: if_split_asm)
  apply(safe)
   apply(fastforce dest!: lf_set_fn simp: field_names_list_def prefix_def less_eq_list_def
                  split: if_split_asm)
  by force


lemma wf_lf_extend_ti:
  "\<lbrakk> wf_lf (lf_set t []); wf_lf (lf_set ti []); wf_desc t; fn \<notin> set (field_names_list ti);
     ti_ind (lf_set ti []) (lf_set t []) \<rbrakk> \<Longrightarrow>
   wf_lf (lf_set (extend_ti ti t fn) [])"
  apply(cases ti, rename_tac typ_struct xs)
  apply(case_tac typ_struct; clarsimp)
   apply(subst wf_lf_fn; simp)
  apply(subst wf_lf_list, erule lf_fn_disj_fn)
  apply(subst ti_ind_sym2)
  apply(subst ti_ind_fn)
  apply(subst ti_ind_sym2)
  apply clarsimp
  apply(subst wf_lf_fn; simp)
  done

lemma wf_lf_ti_pad_combine:
  "wf_lf (lf_set ti []) \<Longrightarrow> wf_lf (lf_set (ti_pad_combine n ti) [])"
  apply(clarsimp simp: ti_pad_combine_def Let_def)
  apply(rule wf_lf_extend_ti)
      apply(clarsimp simp: wf_lf_def fd_cons_desc_def fd_cons_double_update_def
                           fd_cons_update_access_def fd_cons_access_update_def fd_cons_length_def)
     apply assumption
    apply(clarsimp)
   apply(rule foldl_append_nmem)
   apply clarsimp
  apply(clarsimp simp: ti_ind_def fu_commutes_def fa_fu_ind_def)
  done

lemma wf_lf_final_pad:
  "wf_lf (lf_set ti []) \<Longrightarrow> wf_lf (lf_set (final_pad ti) [])"
  by (auto simp: final_pad_def Let_def elim: wf_lf_ti_pad_combine)

lemma wf_lf_adjust_ti:
  "\<lbrakk> wf_lf (lf_set t []); \<And>v. g (f v) v = v;
      \<And>bs bs' v. g bs (g bs' v) = g bs v; \<And>bs v. f (g bs v) = bs \<rbrakk>
      \<Longrightarrow> wf_lf (lf_set (adjust_ti t f g) [])"
  apply(clarsimp simp: wf_lf_def)
  apply(drule lf_set_adjust_ti; clarsimp)
  apply(rule conjI)
   apply(fastforce simp: fd_cons_desc_def fd_cons_double_update_def update_desc_def
                         fd_cons_update_access_def fd_cons_access_update_def fd_cons_length_def)
  apply(fastforce simp: fu_commutes_def update_desc_def fa_fu_ind_def dest!: lf_set_adjust_ti)
  done

lemma ti_ind_empty_typ_info [simp]:
  "ti_ind (lf_set (empty_typ_info tn) []) (lf_set (adjust_ti k f g) [])"
  by (clarsimp simp: ti_ind_def empty_typ_info_def)

lemma ti_ind_extend_ti:
  "\<lbrakk> ti_ind (lf_set t []) (lf_set (adjust_ti k f g) []);
      ti_ind (lf_set ti []) (lf_set (adjust_ti k f g) []) \<rbrakk>
      \<Longrightarrow> ti_ind (lf_set (extend_ti ti t fn) []) (lf_set (adjust_ti k f g) [])"
  apply(case_tac ti, rename_tac typ_struct xs)
  apply(case_tac typ_struct; clarsimp, subst ti_ind_fn, simp)
  done

lemma ti_ind_ti_pad_combine:
  "ti_ind (lf_set ti []) (lf_set (adjust_ti k f g) []) \<Longrightarrow>
      ti_ind (lf_set (ti_pad_combine n ti) []) (lf_set (adjust_ti k f g) [])"
  apply(clarsimp simp: ti_pad_combine_def Let_def)
  apply(rule ti_ind_extend_ti)
   apply(clarsimp simp: ti_ind_def fu_commutes_def fa_fu_ind_def)
  apply assumption
  done

definition f_ind :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a field_desc set \<Rightarrow> bool" where
  "f_ind f X \<equiv> \<forall>x bs v. x \<in> X \<longrightarrow> f (field_update x bs v) = f v"

definition fu_s_comm_k :: "'a leaf_desc set \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "fu_s_comm_k X k \<equiv> \<forall>x. x \<in> field_update ` lf_fd ` X \<longrightarrow> fu_commutes x k"

definition g_ind :: "'a leaf_desc set \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "g_ind X g \<equiv> fu_s_comm_k X g"

definition fa_ind :: "'a field_desc set \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "fa_ind X g \<equiv> \<forall>x bs v. x \<in> X \<longrightarrow> field_access x (g bs v) = field_access x v"

lemma lf_fd_fn:
  "\<forall>fn. lf_fd ` (lf_set (t::'a typ_info) fn) = lf_fd ` (lf_set t [])"
  "\<forall>fn. lf_fd ` (lf_set_struct (st::'a field_desc typ_struct) fn) = lf_fd ` (lf_set_struct st [])"
  "\<forall>fn. lf_fd ` (lf_set_list (ts::('a typ_info,field_name) dt_pair list) fn) = lf_fd ` (lf_set_list ts [])"
  "\<forall>fn. lf_fd ` (lf_set_pair (x::('a typ_info,field_name) dt_pair) fn) = lf_fd ` (lf_set_pair x [])"
  by (induct t and st and ts and x, all \<open>clarsimp simp: image_Un\<close>) metis+

lemma lf_set_empty_typ_info [simp]:
  "lf_set (empty_typ_info tn) fn = {}"
  by (clarsimp simp: empty_typ_info_def)

lemma g_ind_empty [simp]:
  "g_ind {} g"
  by (clarsimp simp: g_ind_def fu_s_comm_k_def)

lemma g_ind_extend_ti:
  "\<lbrakk> g_ind (lf_set s []) g; g_ind (lf_set t []) g \<rbrakk> \<Longrightarrow>
      g_ind (lf_set (extend_ti s t fn) []) g"
  using lf_fd_fn(1)
  by (cases s, rename_tac typ_struct xs)
     (case_tac typ_struct; fastforce simp: g_ind_def image_Un fu_s_comm_k_def)

lemma g_ind_ti_typ_combine:
  "\<lbrakk> g_ind (lf_set ti []) h; \<And>w u v. g w (h u v) = h u (g w v);
      \<And>w v. f (h w v) = f v; \<And>v. g (f v) v = v \<rbrakk>
      \<Longrightarrow> g_ind (lf_set (ti_typ_combine t f g fn ti) []) h"
  apply(clarsimp simp: ti_typ_combine_def Let_def)
  apply(erule g_ind_extend_ti)
  apply(clarsimp simp: g_ind_def fu_s_comm_k_def)
  apply(drule lf_set_adjust_ti)
   apply clarsimp
  apply(clarsimp simp: update_desc_def fu_commutes_def )
  done

lemma g_ind_ti_pad_combine:
  "g_ind ((lf_set ti [])) g \<Longrightarrow> g_ind ((lf_set (ti_pad_combine n ti) [])) g"
  apply(clarsimp simp: ti_pad_combine_def Let_def)
  apply(erule g_ind_extend_ti)
  apply(auto simp: g_ind_def fu_s_comm_k_def fu_commutes_def)
  done

lemma g_ind_ti_typ_pad_combine:
  "\<lbrakk> g_ind (lf_set ti []) h; \<And>w u v. g w (h u v) = h u (g w v);
      \<And>w v. f (h w v) = f v; \<And>v. g (f v) v = v \<rbrakk>
      \<Longrightarrow> g_ind (lf_set (ti_typ_pad_combine t f g fn ti) []) h"
  unfolding ti_typ_pad_combine_def Let_def
  by (fastforce intro!: g_ind_ti_typ_combine g_ind_ti_pad_combine)

lemma f_ind_empty [simp]:
  "f_ind f {}"
  by (clarsimp simp: f_ind_def)

lemma f_ind_extend_ti:
  "\<lbrakk> f_ind f (lf_fd ` lf_set s []); f_ind f (lf_fd ` lf_set t []) \<rbrakk> \<Longrightarrow>
      f_ind f (lf_fd ` lf_set (extend_ti s t fn) [])"
  using lf_fd_fn(1)
  by (cases s, rename_tac typ_struct xs)
     (case_tac typ_struct; fastforce simp: f_ind_def image_Un fu_s_comm_k_def)

lemma f_ind_ti_typ_combine:
  "\<lbrakk> f_ind h (lf_fd ` lf_set ti []); \<And>v w. h (g w v) = h v;
      \<And>v. g (f v) v = v  \<rbrakk>
      \<Longrightarrow> f_ind h (lf_fd ` lf_set (ti_typ_combine t f g fn ti) [])"
  apply(clarsimp simp: ti_typ_combine_def Let_def)
  apply(erule f_ind_extend_ti)
  apply(clarsimp simp: f_ind_def)
  apply(drule lf_set_adjust_ti)
   apply clarsimp
  apply(clarsimp simp: update_desc_def)
  done

lemma f_ind_ti_pad_combine:
  "f_ind f (lf_fd ` (lf_set t [])) \<Longrightarrow> f_ind f (lf_fd ` (lf_set (ti_pad_combine n t) []))"
  apply(clarsimp simp: ti_pad_combine_def Let_def)
  apply(erule f_ind_extend_ti)
  apply(auto simp: f_ind_def)
  done

lemma f_ind_ti_typ_pad_combine:
  "\<lbrakk> f_ind h (lf_fd ` lf_set ti []); \<And>v w. h (g w v) = h v; \<And>v. g (f v) v = v  \<rbrakk>
      \<Longrightarrow> f_ind h (lf_fd ` lf_set (ti_typ_pad_combine t f g fn ti) [])"
  by (auto simp: ti_typ_pad_combine_def Let_def intro: f_ind_ti_typ_combine f_ind_ti_pad_combine)

lemma fa_ind_empty [simp]:
  "fa_ind {} g"
  by (clarsimp simp: fa_ind_def)

lemma fa_ind_extend_ti:
  "\<lbrakk> fa_ind (lf_fd ` lf_set s []) g; fa_ind (lf_fd ` lf_set t []) g \<rbrakk> \<Longrightarrow>
      fa_ind (lf_fd ` lf_set (extend_ti s t fn) []) g"
  using lf_fd_fn(1)
  by (cases s, rename_tac typ_struct xs)
     (case_tac typ_struct; fastforce simp: fa_ind_def image_Un fu_s_comm_k_def)


lemma fa_ind_ti_typ_combine:
  "\<lbrakk> fa_ind (lf_fd ` lf_set ti []) h; \<And>v w. f (h w v) = f v;
      \<And>v. g (f v) v = v   \<rbrakk>
      \<Longrightarrow> fa_ind (lf_fd ` lf_set (ti_typ_combine t f g fn ti) []) h"
  apply(clarsimp simp: ti_typ_combine_def Let_def)
  apply(erule fa_ind_extend_ti)
  apply(clarsimp simp: fa_ind_def fu_s_comm_k_def)
  apply(drule lf_set_adjust_ti)
   apply clarsimp
  apply(clarsimp simp: update_desc_def fu_commutes_def)
  done

lemma fa_ind_ti_pad_combine:
  "fa_ind (lf_fd ` (lf_set ti [])) g \<Longrightarrow> fa_ind (lf_fd ` (lf_set (ti_pad_combine n ti) [])) g"
  apply(clarsimp simp: ti_pad_combine_def Let_def)
  apply(erule fa_ind_extend_ti)
  apply(auto simp: fa_ind_def)
  done

lemma fa_ind_ti_typ_pad_combine:
  "\<lbrakk> fa_ind (lf_fd ` lf_set ti []) h; \<And>v w. f (h w v) = f v;
      \<And>v. g (f v) v = v   \<rbrakk>
      \<Longrightarrow> fa_ind (lf_fd ` lf_set (ti_typ_pad_combine t f g fn ti) []) h"
  by (auto simp: ti_typ_pad_combine_def Let_def intro: fa_ind_ti_typ_combine fa_ind_ti_pad_combine)

lemma wf_lf_ti_typ_combine:
  "\<lbrakk> wf_lf (lf_set ti []); fn \<notin> set (field_names_list ti);
      \<And>v. g (f v) v = v; \<And>w u v. g w (g u v) = g w v;
      \<And>w v. f (g w v) = w;
      g_ind (lf_set ti []) g; f_ind f (lf_fd ` lf_set ti []);
      fa_ind (lf_fd ` lf_set ti []) g \<rbrakk> \<Longrightarrow>
      wf_lf (lf_set (ti_typ_combine (t::'a::wf_type itself) f g fn ti) [])"
  apply(clarsimp simp: ti_typ_combine_def Let_def)
  apply(rule wf_lf_extend_ti; simp?)
   apply(rule wf_lf_adjust_ti; simp)
  apply(clarsimp simp: ti_ind_def)
  apply(drule lf_set_adjust_ti, simp)
  apply(clarsimp simp: fu_commutes_def update_desc_def g_ind_def f_ind_def fu_s_comm_k_def
                       fa_fu_ind_def fa_ind_def)
  done

lemma wf_lf_ti_typ_pad_combine:
  "\<lbrakk> wf_lf (lf_set ti []); fn \<notin> set (field_names_list ti); hd fn \<noteq> CHR ''!'';
      \<And>v. g (f v) v = v; \<And>w u v. g w (g u v) = g w v;
      \<And>w v. f (g w v) = w;
      g_ind (lf_set ti []) g; f_ind f (lf_fd ` lf_set ti []);
      fa_ind (lf_fd ` lf_set ti []) g \<rbrakk> \<Longrightarrow>
      wf_lf (lf_set (ti_typ_pad_combine (t::'a::wf_type itself) f g fn ti) [])"
  apply(clarsimp simp: ti_typ_pad_combine_def Let_def)
  apply (fastforce intro!: wf_lf_ti_typ_combine wf_lf_ti_pad_combine g_ind_ti_pad_combine
                           f_ind_ti_pad_combine fa_ind_ti_pad_combine)
  done

lemma align_field_empty_typ_info [simp]:
  "align_field (empty_typ_info tn)"
  by (clarsimp simp: empty_typ_info_def align_field_def)

lemma align_td_field_lookup:
  "\<forall>f m s n. field_lookup (t::'a typ_desc) f m = Some (s,n) \<longrightarrow> align_td s \<le> align_td t"
  "\<forall>f m s n. field_lookup_struct (st::'a typ_struct) f m = Some (s,n) \<longrightarrow> align_td s \<le> align_td_struct st"
  "\<forall>f m s n. field_lookup_list (ts::('a typ_desc,field_name) dt_pair list) f m = Some (s,n) \<longrightarrow> align_td s \<le> align_td_list ts"
  "\<forall>f m s n. field_lookup_pair (x::('a typ_desc,field_name) dt_pair) f m = Some (s,n) \<longrightarrow> align_td s \<le> align_td_pair x"
  by (induct t and st and ts and x, all \<open>clarsimp\<close>)
     (fastforce simp: max_def split: option.splits)

lemma align_field_extend_ti:
  "\<lbrakk> align_field s; align_field t; 2^(align_td t) dvd size_td s \<rbrakk> \<Longrightarrow>
      align_field (extend_ti s t fn)"
  apply(case_tac s, clarsimp, thin_tac "s = X" for X)
  apply(rename_tac typ_struct xs)
  apply(case_tac typ_struct, clarsimp)
   apply(clarsimp simp: align_field_def split: option.splits)
  apply(clarsimp simp: align_field_def)
  apply(subst (asm) field_lookup_list_append)
  apply(clarsimp split: if_split_asm option.splits)
   apply(case_tac f, clarsimp)
   apply clarsimp
   apply(frule field_lookup_offset2)
   apply (rename_tac lista s n listb)
   apply(drule_tac x=listb in spec, drule_tac x=s in spec)
   apply(drule_tac x="n - size_td_list lista" in spec)
   apply clarsimp
   apply(drule dvd_diffD)
     apply(subgoal_tac "2^align_td s dvd (2::nat)^align_td t ")
      apply(drule (2) dvd_trans)
     apply(rule le_imp_power_dvd)
     apply(subst align_td_field_lookup)
      apply fast
     apply simp
    apply(drule (1) field_lookup_offset_le)
   apply assumption
  apply(case_tac f, clarsimp)
  apply(drule_tac x="a#list" in spec)
  apply clarsimp
  done

lemma align_field_ti_pad_combine:
  "align_field ti \<Longrightarrow> align_field (ti_pad_combine n ti)"
  apply(clarsimp simp: ti_pad_combine_def Let_def)
  apply(erule align_field_extend_ti)
   apply(clarsimp simp: align_field_def)
  apply clarsimp
  done

lemma align_field_final_pad:
  "align_field ti \<Longrightarrow> align_field (final_pad ti)"
  apply(clarsimp simp: final_pad_def Let_def split: if_split_asm)
  apply(erule align_field_ti_pad_combine)
  done

lemma field_lookup_adjust_ti_None:
  "\<forall>fn m s n. field_lookup (adjust_ti t f g) fn m = None \<longrightarrow>
      (field_lookup t fn m = None)"
  "\<forall>fn m s n. field_lookup_struct (map_td_struct (\<lambda>n algn d. update_desc f g d) st)
        fn m = None \<longrightarrow>
        (field_lookup_struct st fn m = None)"
  "\<forall>fn m s n. field_lookup_list (map_td_list (\<lambda>n algn d. update_desc f g d) ts) fn m = None \<longrightarrow>
        (field_lookup_list ts fn m = None)"
  "\<forall>fn m s n. field_lookup_pair (map_td_pair (\<lambda>n algn d. update_desc f g d) x) fn m = None \<longrightarrow>
        (field_lookup_pair x fn m = None)"
  apply (induct t and st and ts and x, all \<open>clarsimp simp: adjust_ti_def split: option.splits\<close>)
  apply (rename_tac dt_pair list fn m, case_tac dt_pair, clarsimp)
  done

lemma field_lookup_adjust_ti' [rule_format]:
  "\<forall>fn m s n. field_lookup (adjust_ti t f g) fn m = Some (s,n) \<longrightarrow>
      (\<exists>s'. field_lookup t fn m = Some (s',n) \<and> align_td s = align_td s')"
  "\<forall>fn m s n. field_lookup_struct (map_td_struct (\<lambda>n algn d. update_desc f g d) st)
        fn m = Some (s,n) \<longrightarrow>
        (\<exists>s'. field_lookup_struct st fn m = Some (s',n) \<and> align_td s = align_td s')"
  "\<forall>fn m s n. field_lookup_list (map_td_list (\<lambda>n algn d. update_desc f g d) ts) fn m = Some (s,n) \<longrightarrow>
        (\<exists>s'. field_lookup_list ts fn m = Some (s',n) \<and> align_td s = align_td s')"
  "\<forall>fn m s n. field_lookup_pair (map_td_pair (\<lambda>n algn d. update_desc f g d) x) fn m = Some (s,n) \<longrightarrow>
        (\<exists>s'. field_lookup_pair x fn m = Some (s',n) \<and> align_td s = align_td s')"
  apply(induct t and st and ts and x, all \<open>clarsimp\<close>)
    apply(clarsimp simp: adjust_ti_def)
   apply(clarsimp split: option.splits)
    apply(rule conjI; clarsimp)
     apply(case_tac dt_pair, clarsimp)
    apply(case_tac dt_pair, clarsimp split: if_split_asm)
    apply(drule_tac x=fn in spec)
    apply clarsimp
    apply(fold adjust_ti_def)
    apply(subst (asm) field_lookup_adjust_ti_None; simp)
   apply fastforce
  apply fastforce
  done

lemma field_lookup_adjust_ti:
  "\<lbrakk> field_lookup (adjust_ti t f g) fn m = Some (s,n) \<rbrakk> \<Longrightarrow>
      (\<exists>s'. field_lookup t fn m = Some (s',n) \<and> align_td s = align_td s')"
  by (rule field_lookup_adjust_ti')

lemma align_adjust_ti:
  "align_field ti \<Longrightarrow> align_field (adjust_ti ti f g)"
  apply(clarsimp simp: align_field_def)
  apply(drule field_lookup_adjust_ti)
  apply clarsimp
  done

lemma align_field_ti_typ_combine:
  "\<lbrakk> align_field ti; 2 ^ align_td (typ_info_t TYPE('a)) dvd size_td ti \<rbrakk> \<Longrightarrow>
   align_field (ti_typ_combine (t::'a::mem_type itself) f g fn ti)"
  apply(clarsimp simp: ti_typ_combine_def Let_def)
  apply(rule align_field_extend_ti, assumption)
   apply(rule align_adjust_ti)
   apply(rule align_field)
  apply simp
  done

lemma align_field_ti_typ_pad_combine:
  "\<lbrakk> align_field ti; aggregate ti \<rbrakk> \<Longrightarrow>
   align_field (ti_typ_pad_combine (t::'a::mem_type itself) f g fn ti)"
  unfolding ti_typ_pad_combine_def Let_def
  by (fastforce simp: size_td_ti_pad_combine ac_simps padup_dvd align_of_def
                intro: dvd_padup_add align_field_ti_typ_combine align_field_ti_pad_combine)

lemma npf_extend_ti [simp]:
  "non_padding_fields (extend_ti s t fn) = non_padding_fields s @
      (if hd fn = CHR ''!'' then [] else [fn])"
  by (case_tac s, rename_tac typ_struct xs)
     (case_tac typ_struct; simp)

lemma npf_ti_pad_combine [simp]:
  "non_padding_fields (ti_pad_combine n tag) = non_padding_fields tag"
  by (clarsimp simp: ti_pad_combine_def Let_def)

lemma npf_ti_typ_combine [simp]:
  "hd fn \<noteq> CHR ''!'' \<Longrightarrow>
   non_padding_fields (ti_typ_combine t_b f g fn tag) = non_padding_fields tag @ [fn]"
  by (clarsimp simp: ti_typ_combine_def Let_def)

lemma npf_ti_typ_pad_combine [simp]:
  "hd fn \<noteq> CHR ''!'' \<Longrightarrow>
   non_padding_fields (ti_typ_pad_combine t_b f g fn tag) = non_padding_fields tag @ [fn]"
  by (clarsimp simp: ti_typ_pad_combine_def Let_def)

lemma npf_final_pad [simp]:
  "non_padding_fields (final_pad tag) = non_padding_fields tag"
  by (clarsimp simp: final_pad_def Let_def)

lemma npf_empty_typ_info [simp]:
  "non_padding_fields (empty_typ_info tn) = []"
  by (clarsimp simp: empty_typ_info_def)

definition field_fd' :: "'a typ_info \<Rightarrow> qualified_field_name \<rightharpoonup> 'a field_desc" where
  "field_fd' t f \<equiv> case field_lookup t f 0 of None \<Rightarrow> None | Some x \<Rightarrow> Some (field_desc (fst x))"

lemma padup_zero [simp]:
  "padup n 0 = 0"
  by (clarsimp simp: padup_def)

lemma padup_same [simp]:
  "padup n n = 0"
  by (clarsimp simp: padup_def)

lemmas size_td_simps_1 = size_td_lt_final_pad size_td_lt_ti_typ_pad_combine
                         aggregate_ti_typ_pad_combine aggregate_empty_typ_info

lemmas size_td_simps_2 = padup_def align_of_final_pad align_of_def

lemmas size_td_simps = size_td_simps_1 size_td_simps_2

end
