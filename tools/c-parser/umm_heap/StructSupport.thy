(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory StructSupport
imports SepCode SepInv
begin

lemma field_lookup_list_Some2 [rule_format]:
  "fn \<notin> dt_snd ` set ts \<Longrightarrow>
   field_lookup_list (ts@[DTPair t fn]) (fn # fs) m = field_lookup t fs (m + size_td_list ts)"
  apply(induct ts arbitrary: m; clarsimp split: option.splits)
  apply(rename_tac a list m)
  apply(safe; case_tac a; clarsimp simp: ac_simps split: if_split_asm)
  done

lemma fnl_set:
  "set (CompoundCTypes.field_names_list (TypDesc (TypAggregate xs) tn)) = dt_snd ` set xs"
  by (auto simp: CompoundCTypes.field_names_list_def)

lemma fnl_extend_ti:
  "\<lbrakk> fn \<notin> set (CompoundCTypes.field_names_list tag); aggregate tag \<rbrakk> \<Longrightarrow>
    field_lookup (extend_ti tag t fn) (f # fs) m =
      (if f=fn then field_lookup t fs (size_td tag+m) else field_lookup tag (f # fs) m)"
  apply(cases tag, rename_tac typ_struct xs)
  apply(case_tac typ_struct; simp)
   apply(simp add: ac_simps field_lookup_list_Some2 fnl_set)
  apply(clarsimp simp: field_lookup_list_append split: option.splits)
  done

lemma fl_ti_pad_combine:
  "\<lbrakk> hd f \<noteq> CHR ''!''; aggregate tag \<rbrakk> \<Longrightarrow>
      field_lookup (ti_pad_combine n tag) (f#fs) m = field_lookup tag (f#fs) m"
  by (auto simp: ti_pad_combine_def Let_def fnl_extend_ti foldl_append_nmem)

lemma fl_ti_typ_combine:
  "\<lbrakk> fn \<notin> set (CompoundCTypes.field_names_list tag); aggregate tag \<rbrakk> \<Longrightarrow>
      field_lookup (ti_typ_combine (t_b::'b::c_type itself) f_ab f_upd_ab fn tag) (f#fs) m =
        (if f=fn
         then field_lookup (adjust_ti (typ_info_t TYPE('b)) f_ab f_upd_ab) fs (size_td tag+m)
         else field_lookup tag (f # fs) m)"
  by (simp add: ti_typ_combine_def Let_def fnl_extend_ti)

lemma fl_ti_typ_combine_match:
  "\<lbrakk> fn \<notin> set (CompoundCTypes.field_names_list tag); aggregate tag \<rbrakk> \<Longrightarrow>
      field_lookup (ti_typ_combine (t_b::'b::c_type itself) f_ab f_upd_ab fn tag) (fn#fs) m =
        field_lookup (adjust_ti (typ_info_t TYPE('b)) f_ab f_upd_ab) fs (size_td tag+m)"
  by (simp add: fl_ti_typ_combine)

lemma fl_ti_typ_combine_mismatch:
  "\<lbrakk> fn \<notin> set (CompoundCTypes.field_names_list tag); aggregate tag; f \<noteq> fn \<rbrakk> \<Longrightarrow>
      field_lookup (ti_typ_combine (t_b::'b::c_type itself) f_ab f_upd_ab fn tag) (f#fs) m =
        field_lookup tag (f # fs) m"
  by (simp add: fl_ti_typ_combine)

lemma fl_ti_typ_pad_combine:
  "\<lbrakk> fn \<notin> set (CompoundCTypes.field_names_list tag); hd f \<noteq> CHR ''!''; hd fn \<noteq> CHR ''!'';
      aggregate tag \<rbrakk> \<Longrightarrow>
      field_lookup (ti_typ_pad_combine (t_b::'b::c_type itself) f_ab f_upd_ab fn tag) (f#fs) m =
        (if f=fn
         then field_lookup (adjust_ti (typ_info_t TYPE('b)) f_ab f_upd_ab) fs
                                      (padup (align_of TYPE('b))
                           (size_td tag) + size_td tag+m)
         else field_lookup tag (f # fs) m)"
  unfolding ti_typ_pad_combine_def Let_def
  by (subst fl_ti_typ_combine; clarsimp) (simp add: fl_ti_pad_combine size_td_ti_pad_combine)

lemma fl_ti_typ_pad_combine_match:
  "\<lbrakk> fn \<notin> set (CompoundCTypes.field_names_list tag); hd fn \<noteq> CHR ''!'';
      aggregate tag \<rbrakk> \<Longrightarrow>
      field_lookup (ti_typ_pad_combine (t_b::'b::c_type itself) f_ab f_upd_ab fn tag) (fn#fs) m =
        field_lookup (adjust_ti (typ_info_t TYPE('b)) f_ab f_upd_ab) fs
                                (padup (align_of TYPE('b))
                     (size_td tag) + size_td tag+m)"
  by (simp add: fl_ti_typ_pad_combine)

lemma fl_ti_typ_pad_combine_mismatch:
  "\<lbrakk> fn \<notin> set (CompoundCTypes.field_names_list tag); hd f \<noteq> CHR ''!''; hd fn \<noteq> CHR ''!'';
      aggregate tag; f \<noteq> fn \<rbrakk> \<Longrightarrow>
      field_lookup (ti_typ_pad_combine (t_b::'b::c_type itself) f_ab f_upd_ab fn tag) (f#fs) m =
        field_lookup tag (f # fs) m"
  by (simp add: fl_ti_typ_pad_combine)

lemma fl_final_pad:
  "\<lbrakk> hd f \<noteq> CHR ''!''; aggregate tag \<rbrakk> \<Longrightarrow>
      field_lookup (final_pad tag) (f#fs) m = field_lookup tag (f#fs) m"
  by (clarsimp simp: final_pad_def Let_def fl_ti_pad_combine)

lemma field_lookup_adjust_ti2' [rule_format]:
  "\<forall>fn m s n. field_lookup ti fn m = Some (s,n) \<longrightarrow>
      (field_lookup (adjust_ti ti f g) fn m = Some (adjust_ti s f g,n))"
  "\<forall>fn m s n. field_lookup_struct st fn m = Some (s,n) \<longrightarrow>
      field_lookup_struct (map_td_struct (\<lambda>n algn d. update_desc f g d) st) fn m = Some (adjust_ti s f g,n)"
  "\<forall>fn m s n. field_lookup_list ts fn m = Some (s,n) \<longrightarrow>
      field_lookup_list (map_td_list (\<lambda>n algn d. update_desc f g d) ts) fn m = Some (adjust_ti s f g,n)"
  "\<forall>fn m s n. field_lookup_pair x fn m = Some (s,n) \<longrightarrow>
      field_lookup_pair (map_td_pair (\<lambda>n algn d. update_desc f g d) x) fn m = Some (adjust_ti s f g,n)"
  apply(induct ti and st and ts and x, all \<open>clarsimp\<close>)
    apply(clarsimp simp: adjust_ti_def)
   apply(clarsimp split: option.splits)
   apply(fastforce simp: split_DTPair_all simp flip: adjust_ti_def split: if_split_asm
                   dest: field_lookup_adjust_ti)
  apply (clarsimp simp flip: adjust_ti_def)
  done

lemma field_lookup_adjust_ti2:
  "field_lookup t fn m = Some (s,n) \<Longrightarrow>
      field_lookup (adjust_ti t f g) fn m = Some (adjust_ti s f g,n)"
  by (simp add: field_lookup_adjust_ti2')

lemma fl_update:
  "field_lookup (adjust_ti ti f g) fs m =
      (case_option None (\<lambda>(t,n). Some (adjust_ti t f g,n)) (field_lookup ti fs m))"
  apply(clarsimp split: option.splits)
  apply safe
   apply(rule ccontr, clarsimp)
   apply(drule field_lookup_adjust_ti, clarsimp)
  apply(erule field_lookup_adjust_ti2)
  done

lemmas fl_simps = fl_final_pad fl_ti_pad_combine
    fl_ti_typ_combine_match fl_ti_typ_combine_mismatch
    fl_ti_typ_pad_combine_match fl_ti_typ_pad_combine_mismatch

lemma access_ti_props_simps [simp]:
  "\<forall>g x. access_ti (adjust_ti (tag::'a typ_info) (f::'b \<Rightarrow> 'a) g) x = access_ti tag (f x)"
  "\<forall>g x. access_ti_struct (map_td_struct (\<lambda>n algn d. update_desc f g d) (st::'a field_desc typ_struct)) x = access_ti_struct st (f x)"
  "\<forall>g x. access_ti_list (map_td_list (\<lambda>n algn d. update_desc f g d) (ts::('a field_desc typ_desc, char list) dt_pair list)) x = access_ti_list ts (f x)"
  "\<forall>g x. access_ti_pair (map_td_pair (\<lambda>n algn d. update_desc f g d) (k::('a field_desc typ_desc, char list) dt_pair)) x = access_ti_pair k (f x)"
  unfolding adjust_ti_def
  by (induct tag and st and ts and k) (auto simp: update_desc_def)

lemma field_norm_blah:
  "\<lbrakk> \<forall>u v. f (g u v) = u; fd_cons_access_update d n \<rbrakk> \<Longrightarrow>
       field_norm  n algn (update_desc f g d) = field_norm  n algn d"
  by (auto simp: update_desc_def field_norm_def  fd_cons_access_update_def)


(* FIXME: should be generalised to just an extensionality principle on the
   map function, but to be usable here we'd need to rewrite the wf_fdp
   property in that way *)
lemma map_td_ext':
  "wf_fd t \<and> (\<forall>n algn d. fd_cons_access_update d n \<longrightarrow> (f n algn d = g n algn d)) \<longrightarrow> map_td f t = map_td g t"
  "wf_fd_struct st \<and> (\<forall>n algn d. fd_cons_access_update d n \<longrightarrow> (f n algn d = g n algn d)) \<longrightarrow> map_td_struct f st = map_td_struct g st"
  "wf_fd_list ts \<and> (\<forall>n algn d. fd_cons_access_update d n \<longrightarrow> (f n algn d = g n algn d)) \<longrightarrow> map_td_list f ts = map_td_list g ts"
  "wf_fd_pair x \<and> (\<forall>n algn d. fd_cons_access_update d n \<longrightarrow> (f n algn d = g n algn d)) \<longrightarrow> map_td_pair f x = map_td_pair g x"
  by (induct t and st and ts and x)
     (auto simp: fd_cons_struct_def fd_cons_access_update_def fd_cons_desc_def)

lemma map_td_extI:
  "\<lbrakk> wf_fd t; (\<forall>n algn d. fd_cons_access_update d n \<longrightarrow> (f n algn d = g n algn d)) \<rbrakk>
      \<Longrightarrow> map_td f t = map_td g t"
  by (simp add: map_td_ext')

lemma export_tag_adjust_ti2 [simp]:
  "\<lbrakk> \<forall>u v. f (g u v) = u; wf_lf (lf_set t []); wf_desc t \<rbrakk> \<Longrightarrow>
      export_uinfo (adjust_ti t f g) = (export_uinfo t)"
  unfolding export_uinfo_def adjust_ti_def map_td_map
  by (fastforce simp: field_norm_blah intro: wf_fdp_fdD map_td_extI elim: wf_lf_fdp)

lemma field_names_list:
  "field_names_list (xs@ys) t = field_names_list xs t @ field_names_list ys t"
  by (induct xs) auto

lemma field_names_extend_ti:
  "typ_name t \<noteq> typ_name ti \<Longrightarrow>
   field_names (extend_ti ti xi fn) t = field_names ti t @ (map (\<lambda>fs. fn#fs) (field_names xi t))"
  by (cases ti, rename_tac typ_struct xs)
     (case_tac typ_struct; fastforce simp: field_names_list)

lemma field_names_ti_pad_combine:
  "\<lbrakk> typ_name t \<noteq> typ_name ti; hd (typ_name t) \<noteq> CHR ''!'' \<rbrakk> \<Longrightarrow>
      field_names (ti_pad_combine n ti) t = field_names ti t"
  by (clarsimp simp: ti_pad_combine_def Let_def field_names_extend_ti export_uinfo_def size_map_td)

lemma field_names_final_pad:
  "\<lbrakk> typ_name t \<noteq> typ_name ti; hd (typ_name t) \<noteq> CHR ''!'' \<rbrakk> \<Longrightarrow>
      field_names (final_pad ti) t = field_names ti t"
  by (clarsimp simp: final_pad_def Let_def field_names_ti_pad_combine)

lemma field_names_adjust_ti:
  assumes "fg_cons f g"
  shows
  "wf_fd ti \<longrightarrow>
     field_names (adjust_ti (ti::'a typ_info) f g) t = field_names ti t"
  "wf_fd_struct st \<longrightarrow>
     field_names_struct ((map_td_struct (\<lambda>n algn d. update_desc f g d)
                                        (st::'a field_desc typ_struct))) t =
       field_names_struct st t"
  "wf_fd_list ts \<longrightarrow>
     field_names_list (map_td_list (\<lambda>n algn d. update_desc f g d)
                                   (ts::('a field_desc typ_desc, char list) dt_pair list)) t =
       field_names_list ts t"
  "wf_fd_pair x \<longrightarrow>
     field_names_pair (map_td_pair (\<lambda>n algn d. update_desc f g d)
                                   (x::('a field_desc typ_desc, char list) dt_pair)) t =
       field_names_pair x t" using assms
  by (induct ti and st and ts and x) (auto simp: adjust_ti_def)

lemma field_names_ti_typ_combine:
  "\<lbrakk> typ_name t \<noteq> typ_name ti; fg_cons f g \<rbrakk> \<Longrightarrow>
      field_names (ti_typ_combine (t_b::'b::mem_type itself) f g fn ti) t =
        field_names ti t @ map ((#) fn) (field_names (typ_info_t TYPE('b)) t)"
  by (clarsimp simp: ti_typ_combine_def Let_def field_names_adjust_ti field_names_extend_ti
                     export_uinfo_def size_map_td)

lemma size_empty_typ_info [simp]:
  "size (empty_typ_info tn) = 2"
  by (simp add: empty_typ_info_def)

lemma list_size_char:
  "size_list (\<lambda>c. 0) xs = length xs"
  by (induct xs) auto

lemma size_ti_extend_ti [simp]:
  "aggregate ti \<Longrightarrow> size (extend_ti ti t fn) = size ti + size t + 2"
  by (cases ti, rename_tac typ_struct xs) (case_tac typ_struct, auto simp: list_size_char)

lemma typ_name_empty_typ_info [simp]:
  "typ_name (empty_typ_info tn) = tn"
  by (clarsimp simp: empty_typ_info_def)

lemma typ_name_extend_ti [simp]:
  "typ_name (extend_ti ti t fn) = typ_name ti"
  by (cases ti, simp)

lemma typ_name_ti_pad_combine [simp]:
  "typ_name (ti_pad_combine n ti) = typ_name ti"
  by (clarsimp simp: ti_pad_combine_def Let_def)

lemma typ_name_ti_typ_combine [simp]:
  "typ_name (ti_typ_combine (t_b::'b::c_type itself) f g fn ti) = typ_name ti"
  by (clarsimp simp: ti_typ_combine_def Let_def)

lemma typ_name_ti_typ_pad_combine [simp]:
  "typ_name (ti_typ_pad_combine (t_b::'b::c_type itself) f g fn ti) = typ_name ti"
  by (clarsimp simp: ti_typ_pad_combine_def Let_def)

lemma typ_name_ti_final_pad [simp]:
  "typ_name (final_pad ti) = typ_name ti"
  by (clarsimp simp: final_pad_def Let_def)

lemma typ_name_map_td [simp]:
  "typ_name (map_td f td) = typ_name td"
  by (cases td, simp)

lemma field_names_ti_typ_pad_combine:
  "\<lbrakk> typ_name t \<noteq> typ_name ti; fg_cons f g; aggregate ti; hd (typ_name t) \<noteq> CHR ''!'' \<rbrakk> \<Longrightarrow>
      field_names (ti_typ_pad_combine (t_b::'b::mem_type itself) f g fn ti) t =
        field_names ti t @ map ((#) fn) (field_names (typ_info_t TYPE('b)) t)"
  by (auto simp: ti_typ_pad_combine_def Let_def field_names_ti_typ_combine field_names_ti_pad_combine)

lemma field_names_empty_typ_info:
  "typ_name t \<noteq> tn \<Longrightarrow> field_names (empty_typ_info tn) t = []"
  by(clarsimp simp: empty_typ_info_def)

lemma sep_heap_update_global_super_fl':
  "\<lbrakk> (p \<mapsto>\<^sub>g u \<and>\<^sup>* R) (lift_state (h,d));
      field_lookup (typ_info_t TYPE('b::mem_type)) f 0 = Some (t,n);
      export_uinfo t = (typ_uinfo_t TYPE('a));
      w = update_ti_t t (to_bytes_p v) u \<rbrakk> \<Longrightarrow>
      ((p \<mapsto>\<^sub>g w) \<and>\<^sup>* R)
      (lift_state (heap_update (Ptr &(p\<rightarrow>f)) (v::'a::mem_type) h,d))"
  by (auto dest: sep_heap_update_global_super_fl)

lemma sep_heap_update_global_super_fl'_inv:
  "\<lbrakk> (p \<mapsto>\<^sup>i\<^sub>g u \<and>\<^sup>* R) (lift_state (h,d));
      field_lookup (typ_info_t TYPE('b::mem_type)) f 0 = Some (t,n);
      export_uinfo t = (typ_uinfo_t TYPE('a));
      w = update_ti_t t (to_bytes_p v) u\<rbrakk> \<Longrightarrow>
   ((p \<mapsto>\<^sup>i\<^sub>g w) \<and>\<^sup>* R) (lift_state (heap_update (Ptr &(p\<rightarrow>f)) (v::'a::mem_type) h,d))"
  unfolding sep_map_inv_def
  by (simp only:sep_conj_assoc) (erule (2) sep_heap_update_global_super_fl)

lemma sep_map'_field_map':
  "\<lbrakk> ((p::'b::mem_type ptr) \<hookrightarrow>\<^sub>g v) s; field_lookup (typ_info_t TYPE('b)) f 0
      = Some (d,n); export_uinfo d = typ_uinfo_t TYPE('a);
      guard_mono g h \<rbrakk> \<Longrightarrow>
      ((Ptr (&(p\<rightarrow>f))::'a::mem_type ptr) \<hookrightarrow>\<^sub>h from_bytes (access_ti\<^sub>0 d v)) s"
  by (subst sep_map'_unfold_exc, subst (asm) sep_map'_def)
     (fastforce simp: sep_map'_def elim: sep_conj_impl sep_map_field_map')

lemma sep_map'_field_map:
  "\<lbrakk> ((p::'b::mem_type ptr) \<hookrightarrow>\<^sub>g v) s; field_lookup (typ_info_t TYPE('b)) f 0
      = Some (d,n); export_uinfo d = typ_uinfo_t TYPE('a);
      guard_mono g h; w=from_bytes (access_ti\<^sub>0 d v) \<rbrakk> \<Longrightarrow>
      ((Ptr (&(p\<rightarrow>f))::'a::mem_type ptr) \<hookrightarrow>\<^sub>h w) s"
  by (simp add: sep_map'_field_map')

lemma inter_sub:
  "\<lbrakk> Y \<subseteq> X; Y = Z \<rbrakk> \<Longrightarrow> X \<inter> Y = Z"
  by fast

lemma sep_map'_field_map_inv:
  "\<lbrakk> ((p::'b::mem_type ptr) \<hookrightarrow>\<^sup>i\<^sub>g v) s; field_lookup (typ_info_t TYPE('b)) f 0 = Some (d,n);
     export_uinfo d = typ_uinfo_t TYPE('a); guard_mono g h; w=from_bytes (access_ti\<^sub>0 d v) \<rbrakk> \<Longrightarrow>
   ((Ptr &(p\<rightarrow>f)::'a::mem_type ptr) \<hookrightarrow>\<^sup>i\<^sub>h w) s"
  apply(unfold sep_map'_inv_def)
  apply(drule sep_conjD, clarsimp simp: sep_conj_ac)
  apply(subst sep_map'_unfold_exc)
  apply(subst sep_conj_assoc [symmetric])
  apply(rule_tac s\<^sub>0="(s\<^sub>1 ++ s\<^sub>0) |` {(x,y) | x y. x \<in> {&(p\<rightarrow>f)..+size_td d}}" and
                 s\<^sub>1="(s\<^sub>1 ++ s\<^sub>0) |` (dom (s\<^sub>1 ++ s\<^sub>0) - {(x,y) | x y. x \<in> {&(p\<rightarrow>f)..+size_td d}})"
                 in sep_conjI)
     apply(subst sep_conj_com)
     apply(rule_tac s\<^sub>0="(s\<^sub>1 ++ s\<^sub>0) |` s_footprint ((Ptr &(p\<rightarrow>f))::'a::mem_type ptr)" and
                    s\<^sub>1="(s\<^sub>1 ++ s\<^sub>0) |` ({(x, y) |x y. x \<in> {&(p\<rightarrow>f)..+size_td d}} -
                                       s_footprint ((Ptr &(p\<rightarrow>f))::'a::mem_type ptr))" in sep_conjI)
        apply(drule (3) sep_map'_field_map')
        apply(clarsimp simp: sep_conj_ac sep_map'_def sep_conj_def)
        apply(rule_tac x="s\<^sub>0' |` s_footprint ((Ptr &(p\<rightarrow>f))::'a::mem_type ptr)" in exI)
        apply(rule_tac x="s\<^sub>1'" in exI)
        apply(clarsimp simp: sep_conj_ac)
        apply(rule conjI)
         apply(fastforce simp: map_disj_def sep_conj_ac)
        apply(subst map_add_com[where h\<^sub>0="a ++ b" for a b])
         apply(fastforce simp: map_disj_def sep_conj_ac)
        apply(subst map_add_assoc)
        apply(simp add: map_add_restrict)
        apply(frule sep_map_dom_exc)
        apply(rotate_tac -1)
        apply(drule sym)
        apply(thin_tac "s = x" for x)
        apply(fastforce simp: restrict_map_disj_dom_empty map_ac_simps sep_conj_ac)
       apply(clarsimp simp: inv_footprint_def sep_conj_ac)
       apply(rule inter_sub)
        apply(clarsimp simp: sep_conj_ac)
        apply(frule_tac p=p in field_tag_sub)
        apply(drule (1) subsetD)
        apply(clarsimp simp: sep_conj_ac)
        apply(clarsimp simp: sep_conj_ac sep_map'_def sep_conj_def)
        apply(drule sep_map_dom_exc)
        apply(subgoal_tac "s\<^sub>1' (x,y) \<noteq> None")
         apply(clarsimp simp: sep_conj_ac)
         apply(subst map_add_comm)
          apply(fastforce simp: map_disj_def sep_conj_ac)
         apply simp
        apply(clarsimp simp: sep_conj_ac, fast)
       apply(fastforce dest: export_size_of)
      apply(fastforce simp: map_disj_def)
     apply clarsimp
     apply(subst subset_map_restrict_sub_add; simp?)
     apply(fastforce intro!: intvlI dest: export_size_of
                     simp: size_of_def s_footprint_def s_footprint_untyped_def)
    apply simp
   apply(fastforce simp: map_disj_def)
  apply (metis (lifting) map_add_com map_add_restrict_comp_right_dom map_le_iff_map_add_commute
                         restrict_map_sub_add restrict_map_sub_disj)
  done

lemma guard_mono_True [simp]:
  "guard_mono f (\<lambda>x. True)"
  by (simp add: guard_mono_def)

lemma access_ti\<^sub>0_to_bytes [simp]:
  "access_ti\<^sub>0 (typ_info_t TYPE('a::c_type)) = (to_bytes_p::'a \<Rightarrow> byte list)"
  by (auto simp: to_bytes_p_def to_bytes_def access_ti\<^sub>0_def size_of_def)

lemma update_ti_s_from_bytes:
  "length bs = size_of TYPE('a) \<Longrightarrow>
      update_ti_t (typ_info_t TYPE('a::mem_type)) bs x = from_bytes bs"
  by (simp add: from_bytes_def upd)

lemma access_ti\<^sub>0_update_ti [simp]:
  "access_ti\<^sub>0 (adjust_ti ti f g) = access_ti\<^sub>0 ti \<circ> f"
  by (auto simp: access_ti\<^sub>0_def)

lemma update_ti_s_adjust_ti:  (* FIXME: eliminate; first assumption redundant *)
  "\<lbrakk> length bs = size_td ti; fg_cons f g \<rbrakk> \<Longrightarrow>
      update_ti_t (adjust_ti ti f g) bs v = g (update_ti_t ti bs (f v)) v"
  by (rule update_ti_adjust_ti)

lemma update_ti_s_adjust_ti_to_bytes_p [simp]:
  "fg_cons f g \<Longrightarrow>
   update_ti_t (adjust_ti (typ_info_t TYPE('a)) f g) (to_bytes_p (v::'a::mem_type)) w = g v w"
  apply(simp add: update_ti_adjust_ti to_bytes_p_def to_bytes_def)
  apply(subst upd_rf; simp add: size_of_def fd_cons_length)
  apply(subst fd_cons_update_access; simp)
  done

(* td_names stuff *)

definition
  "pad_typ_name \<equiv> ''!pad_typ''"

primrec
  td_names :: "'a typ_desc \<Rightarrow> (char list) set" and
  td_names_struct :: "'a typ_struct \<Rightarrow> (char list) set" and
  td_names_list :: "'a typ_pair list \<Rightarrow> (char list) set" and
  td_names_pair :: "'a typ_pair \<Rightarrow> (char list) set"
where
  tnm0:  "td_names (TypDesc st nm) = ({nm} \<union> td_names_struct st) - {pad_typ_name}"

| tnm1:  "td_names_struct (TypScalar n algn d) = {}"
| tnm2:  "td_names_struct (TypAggregate xs) = td_names_list xs"

| tnm3:  "td_names_list [] = {}"
| tnm4:  "td_names_list (x#xs) = td_names_pair x \<union> td_names_list xs"

| tnm5:  "td_names_pair (DTPair t nm) = td_names t"

lemma td_set_td_names:
  "\<And>(tp :: 'a typ_desc) n m. \<lbrakk>(tp, n) \<in> td_set tp' m; typ_name tp \<noteq> pad_typ_name \<rbrakk> \<Longrightarrow>
     typ_name tp \<in> td_names tp'" and
  "\<And>(tp :: 'a typ_desc) n m. \<lbrakk>(tp, n) \<in> td_set_struct tps m; typ_name tp \<noteq> pad_typ_name \<rbrakk> \<Longrightarrow>
     typ_name tp \<in> td_names_struct tps" and
  "\<And>(tp :: 'a typ_desc) n m. \<lbrakk>(tp, n) \<in> td_set_list tpl m; typ_name tp \<noteq> pad_typ_name \<rbrakk> \<Longrightarrow>
     typ_name tp \<in> td_names_list tpl" and
  "\<And>(tp :: 'a typ_desc) n m. \<lbrakk>(tp, n) \<in> td_set_pair tpr m; typ_name tp \<noteq> pad_typ_name \<rbrakk>\<Longrightarrow>
     typ_name tp \<in> td_names_pair tpr"
  by (induct tp' and tps and tpl and tpr) auto

lemma td_names_map_td [simp]:
  "td_names (map_td f tp) = td_names tp"
  "td_names_struct (map_td_struct f tps) = td_names_struct tps"
  "td_names_list (map_td_list f tpl) = td_names_list tpl"
  "td_names_pair (map_td_pair f tpr) = td_names_pair tpr"
  by (induct tp and tps and tpl and tpr) simp_all

lemma td_names_list_append [simp]:
  "td_names_list (a @ b) = td_names_list a \<union> td_names_list b"
  by (induct a; simp add: Un_assoc)

lemma pad_typ_name_td_names: (* dangerous in [simp]? *)
  "A - {pad_typ_name} \<union> td_names tp = (A \<union> td_names tp) - {pad_typ_name}"
  by (cases tp) fastforce

lemma td_names_extend_ti [simp]:
  shows "td_names (extend_ti tp tp' ls) = td_names tp \<union> td_names tp'" and
  "td_names_struct (extend_ti_struct tps tp' ls) = td_names_struct tps \<union> td_names tp'"
  by (induct tp and tps) (simp_all add: pad_typ_name_td_names)

lemma td_names_pad_combine [simp]:
  "td_names (ti_pad_combine m td) = td_names td"
  unfolding ti_pad_combine_def
  by (simp add: Let_def pad_typ_name_def)

lemma td_names_final_pad [simp]:
  "td_names (final_pad td) = td_names td"
  unfolding final_pad_def
  by (simp add: Let_def)

lemma td_names_adjust_ti [simp]:
  "td_names (adjust_ti td f u) = td_names td"
  unfolding adjust_ti_def
  by (simp add: Let_def)

lemma td_names_typ_combine [simp]:
  fixes its :: "('a :: c_type) itself"
  shows "td_names (ti_typ_combine its f u fn td) = (td_names (typ_info_t TYPE('a))  \<union> td_names td)"
  unfolding ti_typ_combine_def
  by (simp add: Let_def Un_ac)

lemma td_names_typ_pad_combine [simp]:
  fixes its :: "('a :: c_type) itself"
  shows "td_names (ti_typ_pad_combine its f u nm td) = td_names (typ_info_t TYPE('a)) \<union> td_names td"
  unfolding ti_typ_pad_combine_def
  by (simp add: Let_def)

lemma td_names_empty_typ_info [simp]:
  shows "td_names (empty_typ_info nm) = {nm} - {pad_typ_name}"
  unfolding empty_typ_info_def
  by (simp add: Let_def)

lemma td_names_ptr [simp]:
  "td_names (typ_info_t TYPE(('a :: c_type) ptr)) = {typ_name_itself TYPE('a) @ ''+ptr''}"
  by (simp add: pad_typ_name_def)

lemma td_names_word8 [simp]:
  fixes x :: "byte itself"
  shows "td_names (typ_info_t x) = {''word00010''}"
 by (simp add: pad_typ_name_def nat_to_bin_string.simps)

lemma td_names_word32 [simp]:
  "td_names (typ_info_t TYPE(32 word)) = {''word0000010''}"
  by (simp add: pad_typ_name_def nat_to_bin_string.simps)

lemma td_names_word64 [simp]:
  "td_names (typ_info_t TYPE(64 word)) = {''word00000010''}"
  by (simp add: pad_typ_name_def nat_to_bin_string.simps)

lemma td_names_export_uinfo [simp]:
  "td_names (export_uinfo td) = td_names td"
  unfolding export_uinfo_def
  by simp

lemma typ_name_export_uinfo [simp]:
  "typ_name (export_uinfo td) = typ_name td"
  unfolding export_uinfo_def
  by simp

lemma replicate_Suc_append:
  "replicate (Suc n) x = replicate n x @ [x]"
  by (induct n; simp)

lemma list_eq_subset:
  "xs = ys \<Longrightarrow> set ys \<subseteq> set xs" by simp

lemma td_names_array_tag_n:
  "td_names ((array_tag_n n) :: (('a::c_type,'b::finite) array field_desc typ_desc)) =
     {typ_name (typ_info_t TYPE('a)) @ ''_array_'' @ nat_to_bin_string (card (UNIV :: 'b set))} \<union>
     (if n = 0 then {} else td_names (typ_info_t TYPE('a)))"
  apply (induct n; simp add: array_tag_n.simps pad_typ_name_def)
  apply (subst Diff_triv; clarsimp simp: typ_uinfo_t_def)
  apply (fastforce dest: list_eq_subset)
  done

lemma td_names_array [simp]:
  "td_names (typ_info_t TYPE(('a :: c_type)['b :: finite])) =
     {typ_name (typ_info_t TYPE('a)) @ ''_array_'' @ nat_to_bin_string (card (UNIV :: 'b set))} \<union>
     td_names (typ_info_t TYPE('a))"
  by (simp add: typ_info_array array_tag_def td_names_array_tag_n)

lemma tag_disj_via_td_name:
  assumes ta: "typ_name (typ_info_t TYPE('a :: c_type)) \<noteq> pad_typ_name"
  and     tb: "typ_name (typ_info_t TYPE('b :: c_type)) \<noteq> pad_typ_name"
  and   tina: "typ_name (typ_info_t TYPE('a :: c_type)) \<notin> td_names (typ_info_t TYPE('b :: c_type))"
  and   tinb: "typ_name (typ_info_t TYPE('b :: c_type)) \<notin> td_names (typ_info_t TYPE('a :: c_type))"
  shows   "typ_uinfo_t TYPE('a :: c_type) \<bottom>\<^sub>t typ_uinfo_t TYPE('b :: c_type)"
  by (auto simp add: typ_simps dest: td_set_td_names simp: ta tb tina tinb)

lemma lift_t_hrs_mem_update_fld:
  fixes val :: "'b :: mem_type" and ptr :: "'a :: mem_type ptr"
  assumes   fl: "field_lookup (typ_info_t TYPE('a)) f 0 \<equiv>
                   Some (adjust_ti (typ_info_t TYPE('b)) xf (xfu \<circ> (\<lambda>x _. x)), m')"
  and   xf_xfu: "fg_cons xf (xfu \<circ> (\<lambda>x _. x))"
  and       cl: "lift_t g hp ptr = Some z"
  shows "(lift_t g (hrs_mem_update (heap_update (Ptr &(ptr\<rightarrow>f)) val) hp)) =
         lift_t g hp(ptr \<mapsto> xfu (\<lambda>_. val) z)"
  (is "?LHS = ?RHS")
proof -
  let ?ati = "adjust_ti (typ_info_t TYPE('b)) xf (xfu \<circ> (\<lambda>x _. x))"
  have eui: "typ_uinfo_t TYPE('b) = export_uinfo (?ati)" using xf_xfu
    by (simp add: typ_uinfo_t_def)

  have cl': "lift_t g (fst hp, snd hp) ptr = Some z" using cl by simp

  have "?LHS = super_field_update_t (Ptr &(ptr\<rightarrow>f)) val (lift_t g (fst hp, snd hp))"
    unfolding hrs_mem_update_def split_def
  proof (rule lift_t_super_field_update [OF h_t_valid_sub])
    from cl' show "snd hp, g \<Turnstile>\<^sub>t ptr" by (rule lift_t_h_t_valid)

    show fti: "field_ti TYPE('a) f = Some ?ati"
      by (simp add: field_ti_def fl)

    moreover show "export_uinfo (?ati) = typ_uinfo_t TYPE('b)"
      by (rule eui [symmetric])

    ultimately show "TYPE('b) \<le>\<^sub>\<tau> TYPE('a)" by (rule field_ti_sub_typ)
  qed

  also
  have "\<dots> = lift_t g hp(ptr \<mapsto> update_ti_t (adjust_ti (typ_info_t TYPE('b)) xf (xfu \<circ> (\<lambda>x _. x)))
                                            (to_bytes_p val) z)"
    by (simp add: cl eui fl super_field_update_lookup)

  also have "\<dots> = ?RHS" using xf_xfu
    by (simp add: update_ti_adjust_ti update_ti_s_from_bytes)

  finally show ?thesis .
qed

declare pad_typ_name_def [simp]

lemma typ_name_array_tag_n:
  "typ_name (array_tag_n n :: ('a ::c_type ['b :: finite]) field_desc typ_desc) =
     typ_name (typ_info_t TYPE('a)) @ ''_array_'' @ nat_to_bin_string (card (UNIV :: 'b set))"
  by (induct n; clarsimp simp: array_tag_n.simps typ_uinfo_t_def)

lemma typ_name_array [simp]:
  "typ_name (typ_info_t TYPE('a::c_type['b :: finite])) =
    typ_name (typ_info_t TYPE('a)) @ ''_array_'' @ nat_to_bin_string (card (UNIV :: 'b set))"
  by (simp add: typ_info_array array_tag_def typ_name_array_tag_n)

end
