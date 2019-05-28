(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(* License: BSD, terms see file ./LICENSE *)

theory CTypes
imports
  CTypesDefs "HOL-Eisbach.Eisbach_Tools"
begin


lemma fu_commutes:
  "fu_commutes f g \<Longrightarrow> f bs (g bs' v) = g bs' (f bs v)"
  by (simp add: fu_commutes_def)


lemma size_td_list_append [simp]:
  "size_td_list (xs@ys) = size_td_list xs + size_td_list ys"
  by (induct_tac xs, auto)


lemma access_ti_append:
  "\<And>bs. length bs = size_td_list (xs@ys) \<Longrightarrow>
      access_ti_list (xs@ys) t bs =
          access_ti_list xs t (take (size_td_list xs) bs) @
          access_ti_list ys t (drop (size_td_list xs) bs)"
proof (induct xs)
  case Nil show ?case by simp
next
  case (Cons x xs) thus ?case by (simp add: min_def ac_simps drop_take)
qed

lemma update_ti_append [simp]:
  "\<And>bs. update_ti_list (xs@ys) bs v =
      update_ti_list xs (take (size_td_list xs) bs)
          (update_ti_list ys (drop (size_td_list xs) bs) v)"
proof (induct xs)
  case Nil show ?case by simp
next
  case (Cons x xs) thus ?case by (simp add: drop_take ac_simps min_def)
qed

lemma update_ti_struct_t_typscalar [simp]:
  "update_ti_struct_t (TypScalar n algn d) =
      (\<lambda>bs. if length bs = n then field_update d bs else id)"
  by (rule ext, simp add: update_ti_struct_t_def)

lemma update_ti_list_t_empty [simp]:
  "update_ti_list_t [] = (\<lambda>x. id)"
  by (rule ext, simp add: update_ti_list_t_def)

lemma update_ti_list_t_cons [simp]:
  "update_ti_list_t (x#xs) = (\<lambda>bs v.
      if length bs = size_td_pair x + size_td_list xs then
          update_ti_pair_t x (take (size_td_pair x) bs)
              (update_ti_list_t xs (drop (size_td_pair x) bs) v) else
          v)"
  by (force simp: update_ti_list_t_def update_ti_pair_t_def min_def)

lemma update_ti_append_s [simp]:
  "\<And>bs. update_ti_list_t (xs@ys) bs v = (
      if length bs = size_td_list xs + size_td_list ys then
          update_ti_list_t xs (take (size_td_list xs) bs)
              (update_ti_list_t ys (drop (size_td_list xs) bs) v) else
          v)"
proof (induct xs)
  case Nil show ?case by (simp add: update_ti_list_t_def)
next
  case (Cons x xs) thus ?case by (simp add: min_def drop_take ac_simps)
qed

lemma update_ti_pair_t_dtpair [simp]:
  "update_ti_pair_t (DTPair t f) = update_ti_t t"
  by (rule ext, simp add: update_ti_pair_t_def update_ti_t_def)

text \<open>---------------------------------------------------------------\<close>

lemma field_desc_empty [simp]:
  "field_desc (TypDesc (TypAggregate []) nm) =
    \<lparr> field_access = \<lambda>x bs. [],
      field_update = \<lambda>x. id \<rparr>"
  by (force simp: update_ti_t_def)


lemma export_uinfo_typdesc_simp [simp]:
  "export_uinfo (TypDesc st nm) = map_td field_norm (TypDesc st nm)"
  by (simp add: export_uinfo_def)

lemma map_td_list_append [simp]:
  "map_td_list f (xs@ys) = map_td_list f xs @ map_td_list f ys"
  by (induct_tac xs) auto


lemma dt_snd_map_td_list:
  "dt_snd ` set (map_td_list f ts) = dt_snd ` set ts"
proof (induct ts)
  case (Cons x xs) thus ?case by (cases x) auto
qed simp

lemma wf_desc_map:
  shows "wf_desc (map_td f t) = wf_desc t" and
        "wf_desc_struct (map_td_struct f st) = wf_desc_struct st" and
        "wf_desc_list (map_td_list f ts) = wf_desc_list ts" and
        "wf_desc_pair (map_td_pair f x) = wf_desc_pair x"
proof (induct t and st and ts and x)
  case (Cons_typ_desc x xs) thus ?case
    by (cases x, auto simp: dt_snd_map_td_list)
qed auto

lemma wf_desc_list_append [simp]:
  "wf_desc_list (xs@ys) =
   (wf_desc_list xs \<and> wf_desc_list ys \<and> dt_snd ` set xs \<inter> dt_snd ` set ys = {})"
  by (induct_tac xs, auto)

lemma wf_size_desc_list_append [simp]:
  "wf_size_desc_list (xs@ys) = (wf_size_desc_list xs \<and> wf_size_desc_list ys)"
  by (induct_tac xs, auto)

lemma norm_tu_list_append [simp]:
  "norm_tu_list (xs@ys) bs =
   norm_tu_list xs (take (size_td_list xs) bs) @ norm_tu_list ys (drop (size_td_list xs) bs)"
  by (induct xs arbitrary: bs, auto simp: min_def ac_simps drop_take)

lemma wf_size_desc_gt:
  shows "wf_size_desc (t::'a typ_desc) \<Longrightarrow> 0 < size_td t" and
        "wf_size_desc_struct st \<Longrightarrow> 0 < size_td_struct (st::'a typ_struct)" and
        "\<lbrakk> ts \<noteq> []; wf_size_desc_list ts \<rbrakk> \<Longrightarrow> 0 < size_td_list (ts::'a typ_pair list)" and
        "wf_size_desc_pair x \<Longrightarrow> 0 < size_td_pair (x::'a typ_pair)"
  by (induct t and st and ts and x rule: typ_desc_typ_struct_inducts, auto)

lemma field_lookup_empty [simp]:
  "field_lookup t [] n = Some (t,n)"
  by (case_tac t, clarsimp)


lemma field_lookup_pair_empty [simp]:
  "field_lookup_pair x [] n = None"
  by (case_tac x, clarsimp)

lemma field_lookup_list_empty [simp]:
  "field_lookup_list ts [] n = None"
  by (induct ts arbitrary: n, auto)

lemma field_lookup_struct_empty [simp]:
  "field_lookup_struct st [] n = None"
  by (case_tac st, auto)

lemma field_lookup_list_append [rule_format]:
  "field_lookup_list (xs@ys) f n = (case field_lookup_list xs f n of
                                      None \<Rightarrow> field_lookup_list ys f (n + size_td_list xs)
                                    | Some y \<Rightarrow> Some y)"
proof (induct xs arbitrary: n)
  case Nil show ?case by simp
next
  case (Cons x xs) thus ?case
    by (cases x) (auto simp: ac_simps split: option.splits)
qed

lemma field_lookup_list_None:
  "f \<notin> dt_snd ` set ts \<Longrightarrow> field_lookup_list ts (f#fs) m = None"
proof (induct ts arbitrary: f fs m)
  case (Cons x _) thus ?case by (cases x) auto
qed simp

lemma field_lookup_list_Some:
  "f \<in> dt_snd ` set ts \<Longrightarrow> field_lookup_list ts [f] m \<noteq> None"
proof (induct ts arbitrary: f m)
  case (Cons x _) thus ?case by (cases x) auto
qed simp

lemma field_lookup_offset_le:
  shows "\<And>s m n f. field_lookup t f m = Some ((s::'a typ_desc),n) \<Longrightarrow> m \<le> n" and
        "\<And>s m n f. field_lookup_struct st f m = Some ((s::'a typ_desc),n) \<Longrightarrow> m \<le> n" and
        "\<And>s m n f. field_lookup_list ts f m = Some ((s::'a typ_desc),n) \<Longrightarrow> m \<le> n" and
        "\<And>s m n f. field_lookup_pair x f m = Some ((s::'a typ_desc),n) \<Longrightarrow> m \<le> n"
proof (induct t and st and ts and x)
  case (Cons_typ_desc x xs) thus ?case by (fastforce split: option.splits)
qed (auto split: if_split_asm)

lemma field_lookup_offset':
  shows "\<And>f m m' n t'. (field_lookup t f m = Some ((t'::'a typ_desc),m + n)) =
          (field_lookup t f m' = Some (t',m' + n))" and
        "\<And>f m m' n t'. (field_lookup_struct st f m = Some ((t'::'a typ_desc),m + n)) =
          (field_lookup_struct st f m' = Some (t',m' + n))" and
        "\<And>f m m' n t'. (field_lookup_list ts f m = Some ((t'::'a typ_desc),m + n)) =
          (field_lookup_list ts f m' = Some (t',m' + n))" and
        "\<And>f m m' n t'. (field_lookup_pair x f m = Some ((t'::'a typ_desc),m + n)) =
          (field_lookup_pair x f m' = Some (t',m' + n))"
proof (induct t and st and ts and x)
  case (Cons_typ_desc x xs)
  show ?case
  proof
    assume ls: "field_lookup_list (x # xs) f m = Some (t', m + n)"
    show "field_lookup_list (x # xs) f m' = Some (t', m' + n)" (is "?X")
    proof cases
      assume ps: "field_lookup_pair x f m = None"
      moreover from this ls have "\<exists>k. n = size_td (dt_fst x) + k"
        by (clarsimp dest!: field_lookup_offset_le, arith)
      moreover from ps have "field_lookup_pair x f m' = None"
        by -
           (rule ccontr, clarsimp, subgoal_tac "\<exists>k. b = m' + k",
            clarsimp simp: Cons_typ_desc [where m'=m],
            clarsimp dest!: field_lookup_offset_le, arith)
      ultimately show "?X" using ls
        by (clarsimp simp: add.assoc [symmetric])
           (subst (asm) Cons_typ_desc [where m'="m' + size_td (dt_fst x)"], fast)
    next
      assume nps: "field_lookup_pair x f m \<noteq> None"
      moreover from this have "field_lookup_pair x f m' \<noteq> None"
        by (clarsimp, subgoal_tac "\<exists>k. b = m + k", clarsimp)
           (subst (asm) Cons_typ_desc [where m'=m'], fast,
            clarsimp dest!: field_lookup_offset_le, arith)
      ultimately show "?X" using ls
        by (clarsimp, subst (asm) Cons_typ_desc [where m'=m'], simp)
    qed
  next
    assume ls: "field_lookup_list (x # xs) f m' = Some (t', m' + n)"
    show "field_lookup_list (x # xs) f m = Some (t', m + n)" (is "?X")
    proof cases
      assume ps: "field_lookup_pair x f m' = None"
      moreover from this ls have "\<exists>k. n = size_td (dt_fst x) + k"
        by (clarsimp dest!: field_lookup_offset_le, arith)
      moreover from ps have "field_lookup_pair x f m = None"
        by -
           (rule ccontr, clarsimp, subgoal_tac "\<exists>k. b = m + k",
            clarsimp simp: Cons_typ_desc [where m'=m'],
            clarsimp dest!: field_lookup_offset_le, arith)
      ultimately show "?X" using ls
        by (clarsimp simp: add.assoc [symmetric])
           (subst (asm) Cons_typ_desc [where m'="m + size_td (dt_fst x)"], fast)
    next
      assume nps: "field_lookup_pair x f m' \<noteq> None"
      moreover from this have "field_lookup_pair x f m \<noteq> None"
        by (clarsimp, subgoal_tac "\<exists>k. b = m' + k", clarsimp)
           (subst (asm) Cons_typ_desc [where m'=m], fast,
            clarsimp dest!: field_lookup_offset_le, arith)
      ultimately show "?X" using ls
        by (clarsimp, subst (asm) Cons_typ_desc [where m'=m], simp)
    qed
  qed
qed auto

lemma field_lookup_offset:
  "(field_lookup t f m = Some (t',m + n)) = (field_lookup t f 0 = Some (t',n))"
  by (simp add: field_lookup_offset' [where m'=0])

lemma field_lookup_offset2:
  "field_lookup t f m = Some (t',n) \<Longrightarrow> field_lookup t f 0 = Some (t',n - m)"
  by (simp add: field_lookup_offset_le
           flip: field_lookup_offset [where m=m])

lemma field_lookup_list_offset:
  "(field_lookup_list ts f m = Some (t',m + n)) = (field_lookup_list ts f 0 = Some (t',n))"
  by (simp add: field_lookup_offset' [where m'=0])

lemma field_lookup_list_offset2:
  "field_lookup_list ts f m = Some (t',n) \<Longrightarrow> field_lookup_list ts f 0 = Some (t',n - m)"
  by (simp add: field_lookup_offset_le
           flip: field_lookup_list_offset [where m=m])

lemma field_lookup_list_offset3:
  "field_lookup_list ts f 0 = Some (t',n) \<Longrightarrow> field_lookup_list ts f m = Some (t',m + n)"
  by (simp add: field_lookup_list_offset)

lemma field_lookup_list_offsetD:
  "\<lbrakk> field_lookup_list ts f 0 = Some (s,k);
      field_lookup_list ts f m = Some (t,n) \<rbrakk> \<Longrightarrow> s=t \<and> n=m+k"
  by (subgoal_tac "\<exists>k. n = m + k", clarsimp simp: field_lookup_list_offset)
     (clarsimp dest!: field_lookup_offset_le, arith)

lemma field_lookup_offset_None:
  "(field_lookup t f m = None) = (field_lookup t f 0 = None)"
  by (auto simp: field_lookup_offset2 field_lookup_offset [where m=m,symmetric]
           intro: ccontr)

lemma field_lookup_list_offset_None:
  "(field_lookup_list ts f m = None) = (field_lookup_list ts f 0 = None)"
  by (auto simp: field_lookup_list_offset2 field_lookup_list_offset [where m=m,symmetric]
           intro: ccontr)

lemma map_td_size [simp]:
  shows "size_td (map_td f t) = size_td t" and
        "size_td_struct (map_td_struct f st) = size_td_struct st" and
        "size_td_list (map_td_list f ts) = size_td_list ts" and
        "size_td_pair (map_td_pair f x) = size_td_pair x"
  by (induct t and st and ts and x, auto)

lemma export_uinfo_size [simp]:
  "size_td (export_uinfo t) = size_td (t::'a typ_info)"
  by (simp add: export_uinfo_def)

lemma typ_uinfo_size [simp]:
  "size_td (typ_uinfo_t TYPE('a)) = size_td (typ_info_t TYPE('a::c_type))"
  by (simp add: typ_uinfo_t_def export_uinfo_def)

lemma wf_size_desc_map:
  shows "wf_size_desc (map_td f t) = wf_size_desc t" and
        "wf_size_desc_struct (map_td_struct f st) = wf_size_desc_struct st" and
        "wf_size_desc_list (map_td_list f ts) = wf_size_desc_list ts" and
        "wf_size_desc_pair (map_td_pair f x) = wf_size_desc_pair x"
  by (induct t and st and ts and x)
     (all \<open>simp\<close>, (case_tac list; simp))

lemma map_td_flr_Some [simp]:
  "map_td_flr f (Some (t,n)) = Some (map_td f t,n)"
  by (clarsimp simp: map_td_flr_def)

lemma map_td_flr_None [simp]:
  "map_td_flr f None = None"
  by (clarsimp simp: map_td_flr_def)

lemma field_lookup_map:
  shows "\<And>f m s. field_lookup t f m = s \<Longrightarrow>
            field_lookup (map_td fupd t) f m = map_td_flr fupd s" and
        "\<And>f m s. field_lookup_struct st f m = s \<Longrightarrow>
            field_lookup_struct (map_td_struct fupd st) f m = map_td_flr fupd s" and
        "\<And>f m s. field_lookup_list ts f m = s \<Longrightarrow>
            field_lookup_list (map_td_list fupd ts) f m = map_td_flr fupd s" and
        "\<And>f m s. field_lookup_pair x f m = s \<Longrightarrow>
            field_lookup_pair (map_td_pair fupd x) f m = map_td_flr fupd s"
proof (induct t and st and ts and x)
  case (Cons_typ_desc x xs) thus ?case
    by (clarsimp, cases x, auto simp: map_td_flr_def split: option.splits)
qed auto

lemma field_lookup_export_uinfo_Some:
  "field_lookup (t::'a typ_info) f m = Some (s,n) \<Longrightarrow>
      field_lookup (export_uinfo t) f m = Some (export_uinfo s,n)"
  by (simp add: export_uinfo_def field_lookup_map)

lemma field_lookup_struct_export_Some:
  "field_lookup_struct (st::'a typ_struct) f m = Some (s,n) \<Longrightarrow>
      field_lookup_struct (map_td_struct fupd st) f m = Some (map_td fupd s,n)"
  by (simp add: field_lookup_map)

lemma field_lookup_struct_export_None:
  "field_lookup_struct (st::'a typ_struct) f m = None \<Longrightarrow>
      field_lookup_struct (map_td_struct fupd st) f m = None"
  by (simp add: field_lookup_map)

lemma field_lookup_list_export_Some:
  "field_lookup_list (ts::'a typ_pair list) f m = Some (s,n) \<Longrightarrow>
      field_lookup_list (map_td_list fupd ts) f m = Some (map_td fupd s,n)"
  by (simp add: field_lookup_map)

lemma field_lookup_list_export_None:
  "field_lookup_list (ts::'a typ_pair list) f m = None \<Longrightarrow>
      field_lookup_list (map_td_list fupd ts) f m = None"
  by (simp add: field_lookup_map)

lemma field_lookup_pair_export_Some:
  "field_lookup_pair (x::'a typ_pair) f m = Some (s,n) \<Longrightarrow>
      field_lookup_pair (map_td_pair fupd x) f m = Some (map_td fupd s,n)"
  by (simp add: field_lookup_map)

lemma field_lookup_pair_export_None:
  "field_lookup_pair (x::'a typ_pair) f m = None \<Longrightarrow>
      field_lookup_pair (map_td_pair fupd x) f m = None"
  by (simp add: field_lookup_map)

lemma import_flr_Some [simp]:
  "import_flr f (Some (map_td f t,n)) (Some (t,n))"
  by (clarsimp simp: import_flr_def)

lemma import_flr_None [simp]:
  "import_flr f None None"
  by (clarsimp simp: import_flr_def)

lemma field_lookup_export_uinfo_rev'':
  "\<And>f m s. field_lookup (map_td fupd t) f m = s \<Longrightarrow>
      import_flr fupd s ((field_lookup t f m)::'a flr)"
  "\<And>f m s. field_lookup_struct (map_td_struct fupd st) f m = s \<Longrightarrow>
      import_flr fupd s ((field_lookup_struct st f m)::'a flr)"
  "\<And>f m s. field_lookup_list (map_td_list fupd  ts) f m = s \<Longrightarrow>
      import_flr fupd s ((field_lookup_list ts f m)::'a flr)"
  "\<And>f m s. field_lookup_pair (map_td_pair fupd x) f m = s \<Longrightarrow>
      import_flr fupd s ((field_lookup_pair x f m)::'a  flr)"
  apply(induct t and st and ts and x)
       apply(all \<open>clarsimp\<close>)
   apply(clarsimp simp: import_flr_def export_uinfo_def)
  apply(clarsimp split: option.splits)
  apply(case_tac f, clarsimp+)
  apply(rule conjI, clarsimp)
   apply(rule conjI, clarsimp)
    apply(case_tac dt_pair, simp)
   apply clarsimp
   apply(drule_tac fupd=fupd in field_lookup_pair_export_Some)
   apply simp
  apply clarsimp
  apply(rule conjI; clarsimp)
   apply(drule_tac fupd=fupd in field_lookup_pair_export_None)
   apply simp
  apply fastforce
  done

lemma field_lookup_export_uinfo_rev':
  "(\<forall>f m s. field_lookup (map_td fupd t) f m = s \<longrightarrow>
      import_flr fupd s ((field_lookup t f m)::'a flr)) \<and>
   (\<forall>f m s. field_lookup_struct (map_td_struct fupd st) f m = s \<longrightarrow>
      import_flr fupd s ((field_lookup_struct st f m)::'a flr)) \<and>
   (\<forall>f m s. field_lookup_list (map_td_list fupd  ts) f m = s \<longrightarrow>
      import_flr fupd s ((field_lookup_list ts f m)::'a flr)) \<and>
   (\<forall>f m s. field_lookup_pair (map_td_pair fupd x) f m = s \<longrightarrow>
      import_flr fupd s ((field_lookup_pair x f m)::'a  flr))"
  by (auto simp: field_lookup_export_uinfo_rev'')


lemma field_lookup_export_uinfo_Some_rev:
  "field_lookup (export_uinfo (t::'a typ_info)) f m = Some (s,n) \<Longrightarrow>
      \<exists>k. field_lookup t f m = Some (k,n) \<and> export_uinfo k = s"
  apply(insert field_lookup_export_uinfo_rev' [of field_norm t undefined undefined undefined])
  apply clarsimp
  apply(drule_tac x=f in spec)
  apply(drule_tac x=m in spec)
  apply(clarsimp simp: import_flr_def export_uinfo_def split: option.splits)
  done

lemma field_lookup_offset_untyped_eq [simp]:
  "field_lookup (typ_info_t TYPE('a)) f 0 = Some (s,n) \<Longrightarrow>
      field_offset_untyped (typ_uinfo_t TYPE('a::c_type)) f = n"
  apply(simp add: field_offset_untyped_def typ_uinfo_t_def)
  apply(drule field_lookup_export_uinfo_Some)
  apply(simp add: typ_uinfo_t_def export_uinfo_def)
  done

lemma field_lookup_offset_eq [simp]:
  "field_lookup (typ_info_t TYPE('a)) f 0 = Some (s,n) \<Longrightarrow>
      field_offset TYPE('a::c_type) f = n"
  by(simp add: field_offset_def)

lemma field_offset_self [simp]:
  "field_offset t [] = 0"
  by (simp add: field_offset_def field_offset_untyped_def)

lemma field_ti_self [simp]:
  "field_ti TYPE('a) [] = Some (typ_info_t TYPE('a::c_type))"
  by (simp add: field_ti_def)

lemma field_size_self [simp]:
  "field_size TYPE('a) [] = size_td (typ_info_t TYPE('a::c_type))"
  by (simp add: field_size_def)


lemma field_lookup_prefix_None'':
  "(\<forall>f g m. field_lookup (t::'a typ_desc) f m = None \<longrightarrow> field_lookup t (f@g) m = None)"
  "(\<forall>f g m. field_lookup_struct (st::'a typ_struct) f m = None \<longrightarrow> f \<noteq> [] \<longrightarrow>
      field_lookup_struct st (f@g) m = None)"
  "(\<forall>f g m. field_lookup_list (ts::'a typ_pair list) f m = None \<longrightarrow> f \<noteq> [] \<longrightarrow>
      field_lookup_list ts (f@g) m = None)"
  "(\<forall>f g m. field_lookup_pair (x::'a typ_pair) f m = None \<longrightarrow> f \<noteq> [] \<longrightarrow>
      field_lookup_pair x (f@g) m = None)"
  by (induct t and st and ts and x)
     (clarsimp split: option.splits)+

lemma field_lookup_prefix_None' [rule_format]:
  "(\<forall>f g m. field_lookup (t::'a typ_desc) f m = None \<longrightarrow> field_lookup t (f@g) m = None) \<and>
   (\<forall>f g m. field_lookup_struct (st::'a typ_struct) f m = None \<longrightarrow> f \<noteq> [] \<longrightarrow>
      field_lookup_struct st (f@g) m = None) \<and>
   (\<forall>f g m. field_lookup_list (ts::'a typ_pair list) f m = None \<longrightarrow> f \<noteq> [] \<longrightarrow>
      field_lookup_list ts (f@g) m = None) \<and>
   (\<forall>f g m. field_lookup_pair (x::'a typ_pair) f m = None \<longrightarrow> f \<noteq> [] \<longrightarrow>
      field_lookup_pair x (f@g) m = None)"
  by (auto simp: field_lookup_prefix_None'')


lemma field_lookup_prefix_Some'':
  "(\<forall>f g t' m n. field_lookup t f m = Some ((t'::'a typ_desc),n) \<longrightarrow> wf_desc t \<longrightarrow>
      field_lookup t (f@g) m = field_lookup t' g n)"
  "(\<forall>f g t' m n. field_lookup_struct st f m = Some ((t'::'a typ_desc),n) \<longrightarrow> wf_desc_struct st \<longrightarrow>
      field_lookup_struct st (f@g) m = field_lookup t' g n)"
  "(\<forall>f g t' m n. field_lookup_list ts f m = Some ((t'::'a typ_desc),n) \<longrightarrow> wf_desc_list ts \<longrightarrow>
      field_lookup_list ts (f@g) m = field_lookup t' g n)"
  "(\<forall>f g t' m n. field_lookup_pair x f m = Some ((t'::'a typ_desc),n) \<longrightarrow> wf_desc_pair x \<longrightarrow>
      field_lookup_pair x (f@g) m = field_lookup t' g n)"
  apply(induct t and st and ts and x, all \<open>clarsimp\<close>)
  apply(clarsimp split: option.splits)
   apply(subst (asm) field_lookup_prefix_None', assumption; clarsimp)
  apply(case_tac dt_pair)
  apply(case_tac f, clarsimp)
  by (clarsimp simp: field_lookup_list_None split: if_split_asm)

lemma field_lookup_prefix_Some' [rule_format]:
  "(\<forall>f g t' m n. field_lookup t f m = Some ((t'::'a typ_desc),n) \<longrightarrow> wf_desc t \<longrightarrow>
      field_lookup t (f@g) m = field_lookup t' g n) \<and>
   (\<forall>f g t' m n. field_lookup_struct st f m = Some ((t'::'a typ_desc),n) \<longrightarrow> wf_desc_struct st \<longrightarrow>
      field_lookup_struct st (f@g) m = field_lookup t' g n) \<and>
   (\<forall>f g t' m n. field_lookup_list ts f m = Some ((t'::'a typ_desc),n) \<longrightarrow> wf_desc_list ts \<longrightarrow>
      field_lookup_list ts (f@g) m = field_lookup t' g n) \<and>
   (\<forall>f g t' m n. field_lookup_pair x f m = Some ((t'::'a typ_desc),n) \<longrightarrow> wf_desc_pair x \<longrightarrow>
      field_lookup_pair x (f@g) m = field_lookup t' g n)"
  by (auto simp: field_lookup_prefix_Some'')

lemma field_lvalue_empty_simp [simp]:
  "Ptr &(p\<rightarrow>[]) = p"
  by (simp add: field_lvalue_def field_offset_def field_offset_untyped_def)

lemma map_td_align [simp]:
  "align_td (map_td f t) = align_td (t::'a typ_desc)"
  "align_td_struct (map_td_struct f st) = align_td_struct (st::'a typ_struct)"
  "align_td_list (map_td_list f ts) = align_td_list (ts::'a typ_pair list)"
  "align_td_pair (map_td_pair f x) = align_td_pair (x::'a typ_pair)"
  by (induct t and st and ts and x) auto

lemma typ_uinfo_align [simp]:
  "align_td (export_uinfo t) = align_td (t::'a typ_info)"
  by (simp add: export_uinfo_def)

lemma ptr_aligned_Ptr_0 [simp]:
  "ptr_aligned NULL"
  by (simp add: ptr_aligned_def)

lemma td_set_self [simp]:
  "(t,m) \<in> td_set t m"
  by (case_tac t, simp)

lemma td_set_wf_size_desc [rule_format]:
  "(\<forall>s m n. wf_size_desc t \<longrightarrow> ((s::'a typ_desc),m) \<in> td_set t n \<longrightarrow> wf_size_desc s)"
  "(\<forall>s m n. wf_size_desc_struct st \<longrightarrow> ((s::'a typ_desc),m) \<in> td_set_struct st n \<longrightarrow> wf_size_desc s)"
  "(\<forall>s m n. wf_size_desc_list ts \<longrightarrow> ((s::'a typ_desc),m) \<in> td_set_list ts n \<longrightarrow> wf_size_desc s)"
  "(\<forall>s m n. wf_size_desc_pair x \<longrightarrow> ((s::'a typ_desc),m) \<in> td_set_pair x n \<longrightarrow> wf_size_desc s)"
  by (induct t and st and ts and x) force+

lemma td_set_size_lte':
  "(\<forall>s k m. ((s::'a typ_desc),k) \<in> td_set t m \<longrightarrow> size s = size t \<and> s=t \<and> k=m \<or> size s < size t)"
  "(\<forall>s k m. ((s::'a typ_desc),k) \<in> td_set_struct st m \<longrightarrow> size s < size st)"
  "(\<forall>s k m. ((s::'a typ_desc),k) \<in> td_set_list xs m \<longrightarrow> size s < size_list (size_dt_pair size (\<lambda>_. 0)) xs)"
  "(\<forall>s k m. ((s::'a typ_desc),k) \<in> td_set_pair x m \<longrightarrow> size s < size_dt_pair size (\<lambda>_. 0) x)"
  by (induct t and st and xs and x) force+

lemma td_set_size_lte:
  "(s,k) \<in> td_set t m \<Longrightarrow> size s = size t \<and> s=t \<and> k=m \<or>
      size s < size t"
  by (simp add: td_set_size_lte')

lemma td_set_struct_size_lte:
  "(s,k) \<in> td_set_struct st m \<Longrightarrow> size s < size st"
  by (simp add: td_set_size_lte')

lemma td_set_list_size_lte:
  "(s,k) \<in> td_set_list ts m \<Longrightarrow> size s < size_list (size_dt_pair size (\<lambda>_. 0)) ts"
  by (simp add: td_set_size_lte')

lemma td_aggregate_not_in_td_set_list [simp]:
  "\<not> (TypDesc (TypAggregate xs) tn,k) \<in> td_set_list xs m"
  by (fastforce dest: td_set_list_size_lte simp: size_char_def)

lemma sub_size_td:
  "(s::'a typ_desc) \<le> t \<Longrightarrow> size s \<le> size t"
  by (fastforce dest: td_set_size_lte simp: typ_tag_le_def)

lemma sub_tag_antisym:
  "\<lbrakk> (s::'a typ_desc) \<le> t; t \<le> s \<rbrakk> \<Longrightarrow> s=t"
  apply(frule sub_size_td)
  apply(frule sub_size_td [where t=s])
  apply(clarsimp simp: typ_tag_le_def)
  apply(drule td_set_size_lte)
  apply clarsimp
  done

lemma sub_tag_refl:
  "(s::'a typ_desc) \<le> s"
  unfolding typ_tag_le_def by (cases s, fastforce)

lemma sub_tag_sub':
  "\<forall>s m n. ((s::'a typ_desc),n) \<in> td_set t m \<longrightarrow> td_set s n \<subseteq> td_set t m"
  "\<forall>s m n. ((s::'a typ_desc),n) \<in> td_set_struct ts m \<longrightarrow> td_set s n \<subseteq> td_set_struct ts m"
  "\<forall>s m n. ((s::'a typ_desc),n) \<in> td_set_list xs m \<longrightarrow> td_set s n \<subseteq> td_set_list xs m"
  "\<forall>s m n. ((s::'a typ_desc),n) \<in> td_set_pair x m \<longrightarrow> td_set s n \<subseteq> td_set_pair x m"
  by (induct t and ts and xs and x) fastforce+

lemma sub_tag_sub:
  "(s,n) \<in> td_set t m \<Longrightarrow> td_set s n \<subseteq> td_set t m"
  by (simp add: sub_tag_sub')

lemma td_set_fst:
  "\<forall>m n. fst ` td_set (s::'a typ_desc) m = fst ` td_set s n"
  "\<forall>m n. fst ` td_set_struct (st::'a typ_struct) m = fst ` td_set_struct st n"
  "\<forall>m n. fst ` td_set_list (xs::'a typ_pair list) m = fst ` td_set_list xs n"
  "\<forall>m n. fst ` td_set_pair (x::'a typ_pair) m = fst ` td_set_pair x n"
  by (induct s and st and xs and x) (all \<open>clarsimp\<close>, fast, fast)

lemma sub_tag_trans:
  "\<lbrakk> (s::'a typ_desc) \<le> t; t \<le> u \<rbrakk> \<Longrightarrow> s \<le> u"
  apply(clarsimp simp: typ_tag_le_def)
  apply(rename_tac n n')
  apply(subgoal_tac "s \<in> fst ` td_set t 0")
   apply(subgoal_tac "s \<in> fst ` td_set t n'")
    apply(drule_tac n=n' in sub_tag_sub)
    apply force
   apply(subgoal_tac "fst ` td_set t 0 = fst ` td_set t n'")
    apply fast
   apply(simp add: td_set_fst)
  apply force
  done

(*FIXME: move*)
instantiation typ_desc :: (type) order
begin
instance
  apply intro_classes
     apply(fastforce simp: typ_tag_lt_def typ_tag_le_def dest: td_set_size_lte)
    apply(rule sub_tag_refl)
   apply(erule (1) sub_tag_trans)
  apply(erule (1) sub_tag_antisym)
  done
end

lemma td_set_offset_size'':
  "\<forall>s m n. ((s::'a typ_desc),n) \<in> td_set t m  \<longrightarrow> size_td s + (n - m) \<le> size_td t"
  "\<forall>s m n. ((s::'a typ_desc),n) \<in> td_set_struct st m \<longrightarrow> size_td s + (n - m) \<le> size_td_struct st"
  "\<forall>s m n. ((s::'a typ_desc),n) \<in> td_set_list ts m \<longrightarrow> size_td s + (n - m) \<le> size_td_list ts"
  "\<forall>s m n. ((s::'a typ_desc),n) \<in> td_set_pair x m \<longrightarrow> size_td s + (n - m) \<le> size_td_pair x"
  by (induct t and st and ts and x, all \<open>clarsimp\<close>)
     (case_tac dt_pair, fastforce)

lemma td_set_offset_size':
  "(\<forall>s m n. ((s::'a typ_desc),n) \<in> td_set t m  \<longrightarrow> size_td s + (n - m) \<le> size_td t) \<and>
    (\<forall>s m n. ((s::'a typ_desc),n) \<in> td_set_struct st m \<longrightarrow> size_td s + (n - m) \<le> size_td_struct st) \<and>
    (\<forall>s m n. ((s::'a typ_desc),n) \<in> td_set_list ts m \<longrightarrow> size_td s + (n - m) \<le> size_td_list ts) \<and>
    (\<forall>s m n. ((s::'a typ_desc),n) \<in> td_set_pair x m \<longrightarrow> size_td s + (n - m) \<le> size_td_pair x)"
  by (auto simp: td_set_offset_size'')

lemma td_set_offset_size:
  "(s,n) \<in> td_set t 0 \<Longrightarrow> size_td s + n \<le> size_td t"
  using td_set_offset_size' [of t undefined undefined undefined] by fastforce

lemma td_set_struct_offset_size:
  "(s,n) \<in> td_set_struct st m \<Longrightarrow> size_td s + (n - m) \<le> size_td_struct st"
  using td_set_offset_size' [of undefined st undefined undefined] by clarsimp

lemma td_set_list_offset_size:
  "(s,n) \<in> td_set_list ts 0 \<Longrightarrow> size_td s + n \<le> size_td_list ts"
  using td_set_offset_size' [of undefined undefined ts undefined]
  by fastforce

lemma td_set_offset_size_m:
  "(s,n) \<in> td_set t m \<Longrightarrow> size_td s + (n - m) \<le> size_td t"
  using insert td_set_offset_size' [of t undefined undefined undefined]
  by clarsimp

lemma td_set_list_offset_size_m:
  "(s,n) \<in> td_set_list t m \<Longrightarrow> size_td s + (n - m) \<le> size_td_list t"
  using insert td_set_offset_size' [of undefined undefined t undefined]
  by clarsimp

lemma td_set_pair_offset_size_m:
  "(s,n) \<in> td_set_pair t m \<Longrightarrow> size_td s + (n - m) \<le> size_td_pair t"
  using td_set_offset_size' [of undefined undefined undefined t]
  by clarsimp

lemma td_set_offset_le':
  "\<forall>s m n. ((s::'a typ_desc),n) \<in> td_set t m \<longrightarrow> m \<le> n"
  "\<forall>s m n. ((s::'a typ_desc),n) \<in> td_set_struct st m \<longrightarrow> m \<le> n"
  "\<forall>s m n. ((s::'a typ_desc),n) \<in> td_set_list ts m \<longrightarrow> m \<le> n"
  "\<forall>s m n. ((s::'a typ_desc),n) \<in> td_set_pair x m \<longrightarrow> m \<le> n"
  by (induct t and st and ts and x) fastforce+

lemma td_set_list_offset_le:
  "(s,n) \<in> td_set_list ts m \<Longrightarrow> m \<le> n"
  by (simp add: td_set_offset_le')

lemma td_set_pair_offset_le:
  "(s,n) \<in> td_set_pair ts m \<Longrightarrow> m \<le> n"
  by (simp add: td_set_offset_le')

lemma field_of_self [simp]:
  "field_of 0 t t"
  by (simp add: field_of_def)

lemma td_set_export_uinfo':
  "\<forall>f m n s. ((s::'a typ_info),n) \<in> td_set t m \<longrightarrow>
     (export_uinfo s,n) \<in> td_set (export_uinfo t) m"
  "\<forall>f m n s. ((s::'a typ_info),n) \<in> td_set_struct st m \<longrightarrow>
     (export_uinfo s,n) \<in> td_set_struct (map_td_struct field_norm st) m"
  "\<forall>f m n s. ((s::'a typ_info),n) \<in> td_set_list ts m \<longrightarrow>
     (export_uinfo s,n) \<in> td_set_list (map_td_list field_norm ts) m"
  "\<forall>f m n s. ((s::'a typ_info),n) \<in> td_set_pair x m \<longrightarrow>
     (export_uinfo s,n) \<in> td_set_pair (map_td_pair field_norm x) m"
  apply(induct t and st and ts and x)
       apply (all \<open>clarsimp\<close>)
   apply(case_tac dt_pair, simp add: export_uinfo_def)
  apply(simp add: export_uinfo_def)
  done

lemma td_set_export_uinfo:
  "(\<forall>f m n s. ((s::'a typ_info),n) \<in> td_set t m \<longrightarrow>
      (export_uinfo s,n) \<in> td_set (export_uinfo t) m) \<and>
   (\<forall>f m n s. ((s::'a typ_info),n) \<in> td_set_struct st m \<longrightarrow>
      (export_uinfo s,n) \<in> td_set_struct (map_td_struct field_norm st) m) \<and>
   (\<forall>f m n s. ((s::'a typ_info),n) \<in> td_set_list ts m \<longrightarrow>
      (export_uinfo s,n) \<in> td_set_list (map_td_list field_norm ts) m) \<and>
   (\<forall>f m n s. ((s::'a typ_info),n) \<in> td_set_pair x m \<longrightarrow>
      (export_uinfo s,n) \<in> td_set_pair (map_td_pair field_norm x) m)"
  by (auto simp: td_set_export_uinfo')


lemma td_set_export_uinfoD:
  "(s,n) \<in> td_set t m \<Longrightarrow> (export_uinfo s,n) \<in> td_set (export_uinfo t) m"
  using td_set_export_uinfo [of t undefined undefined undefined] by clarsimp

lemma td_set_field_lookup'':
  "\<forall>s m n. wf_desc t \<longrightarrow> (((s::'a typ_desc),m + n) \<in> td_set t m \<longrightarrow>
     (\<exists>f. field_lookup t f m = Some (s,m+n)))"
  "\<forall>s m n. wf_desc_struct st \<longrightarrow> (((s::'a typ_desc),m + n) \<in> td_set_struct st m \<longrightarrow>
     (\<exists>f. field_lookup_struct st f m = Some (s,m+n)))"
  "\<forall>s m n. wf_desc_list ts \<longrightarrow> (((s::'a typ_desc),m + n) \<in> td_set_list ts m \<longrightarrow>
     (\<exists>f. field_lookup_list ts f m = Some (s,m+n)))"
  "\<forall>s m n. wf_desc_pair x \<longrightarrow> (((s::'a typ_desc),m + n) \<in> td_set_pair x m \<longrightarrow>
     (\<exists>f. field_lookup_pair x f m = Some (s,m+n)))"
  apply(induct t and st and ts and x)
       apply clarsimp
       apply(case_tac s, clarsimp)
       apply (rule conjI)
        apply clarsimp
        apply(rule_tac x="[]" in exI)
        apply clarsimp+
       apply((erule allE)+, erule (1) impE)
       apply clarsimp
       apply(case_tac f, clarsimp+)
       apply(rename_tac x xs)
       apply(rule_tac x="x#xs" in exI)
       apply clarsimp
      apply clarsimp+
   apply(rule conjI, clarsimp)
    apply((erule allE)+, erule (1) impE)
    apply(clarsimp, case_tac f, clarsimp+)
    apply(rename_tac x xs)
    apply(rule_tac x="x#xs" in exI)
    apply(clarsimp)
   apply clarsimp
   apply(thin_tac "\<forall>s. P s" for P)
   apply(drule_tac x=s in spec)
   apply(drule_tac x="m + size_td (dt_fst dt_pair)" in spec)
   apply(drule_tac x="n - size_td (dt_fst dt_pair)" in spec)
   apply(frule td_set_list_offset_le)
   apply clarsimp
   apply(rule_tac x=f in exI)
   apply(clarsimp split: option.splits)
   apply(case_tac dt_pair, clarsimp split: if_split_asm)
   apply(case_tac f, clarsimp+)
   apply(simp add: field_lookup_list_None)
  apply clarsimp
  apply((erule allE)+, erule (1) impE)
  apply clarsimp
  apply(rule_tac x="list#f" in exI)
  apply clarsimp
  done

lemma td_set_field_lookup':
  "(\<forall>s m n. wf_desc t \<longrightarrow> (((s::'a typ_desc),m + n) \<in> td_set t m \<longrightarrow>
      (\<exists>f. field_lookup t f m = Some (s,m+n)))) \<and>
    (\<forall>s m n. wf_desc_struct st \<longrightarrow> (((s::'a typ_desc),m + n) \<in> td_set_struct st m \<longrightarrow>
      (\<exists>f. field_lookup_struct st f m = Some (s,m+n)))) \<and>
    (\<forall>s m n. wf_desc_list ts \<longrightarrow> (((s::'a typ_desc),m + n) \<in> td_set_list ts m \<longrightarrow>
      (\<exists>f. field_lookup_list ts f m = Some (s,m+n)))) \<and>
    (\<forall>s m n. wf_desc_pair x \<longrightarrow> (((s::'a typ_desc),m + n) \<in> td_set_pair x m \<longrightarrow>
      (\<exists>f. field_lookup_pair x f m = Some (s,m+n))))"
  by (auto simp: td_set_field_lookup'')


lemma td_set_field_lookup_rev'':
  "\<forall>s m n. (\<exists>f. field_lookup t f m = Some (s,m+n)) \<longrightarrow>
     ((s::'a typ_desc),m + n) \<in> td_set t m"
  "\<forall>s m n. (\<exists>f. field_lookup_struct st f m = Some (s,m+n)) \<longrightarrow>
     ((s::'a typ_desc),m + n) \<in> td_set_struct st m"
  "\<forall>s m n. (\<exists>f. field_lookup_list ts f m = Some (s,m+n)) \<longrightarrow>
     ((s::'a typ_desc),m + n) \<in> td_set_list ts m"
  "\<forall>s m n. (\<exists>f. field_lookup_pair x f m = Some (s,m+n)) \<longrightarrow>
     ((s::'a typ_desc),m + n) \<in> td_set_pair x m"
  apply(induct t and st and ts and x)
       apply clarsimp
       apply(case_tac f, clarsimp)
       apply clarsimp
       apply((erule allE)+, erule impE, fast)
       apply fast
      apply clarsimp+
   apply(clarsimp split: option.splits)
    apply(thin_tac "All P" for P)
    apply(drule_tac x=s in spec)
    apply(drule_tac x="m + size_td (dt_fst dt_pair)" in spec)
    apply(drule_tac x="n - size_td (dt_fst dt_pair)" in spec)
    apply(erule impE)
     apply(frule field_lookup_offset_le)
     apply clarsimp
     apply fast
    apply(frule field_lookup_offset_le)
    apply clarsimp
   apply((erule allE)+, erule impE, fast)
   apply assumption
  apply clarsimp
  apply(case_tac f, clarsimp+)
  apply((erule allE)+, erule impE, fast)
  apply assumption
  done

lemma td_set_field_lookup_rev':
  "(\<forall>s m n. (\<exists>f. field_lookup t f m = Some (s,m+n)) \<longrightarrow>
      ((s::'a typ_desc),m + n) \<in> td_set t m) \<and>
    (\<forall>s m n. (\<exists>f. field_lookup_struct st f m = Some (s,m+n)) \<longrightarrow>
      ((s::'a typ_desc),m + n) \<in> td_set_struct st m) \<and>
    (\<forall>s m n. (\<exists>f. field_lookup_list ts f m = Some (s,m+n)) \<longrightarrow>
      ((s::'a typ_desc),m + n) \<in> td_set_list ts m) \<and>
    (\<forall>s m n. (\<exists>f. field_lookup_pair x f m = Some (s,m+n)) \<longrightarrow>
      ((s::'a typ_desc),m + n) \<in> td_set_pair x m)"
  by (auto simp: td_set_field_lookup_rev'')

lemma td_set_field_lookup:
  "wf_desc t \<Longrightarrow> k \<in> td_set t 0 = (\<exists>f. field_lookup t f 0 = Some k)"
  using td_set_field_lookup' [of t undefined undefined undefined]
        td_set_field_lookup_rev' [of t undefined undefined undefined]
  apply clarsimp
  apply(case_tac k, clarsimp)
  apply (rule iffI)
   apply(drule_tac x=a in spec)
   apply(drule_tac x=0 in spec)
   apply fastforce
  apply(thin_tac "All P" for P)
  apply(drule_tac x=a in spec)
  apply(drule_tac x=0 in spec)
  by fastforce

lemma td_set_field_lookupD:
  "field_lookup t f m = Some k \<Longrightarrow> k \<in> td_set t m"
  using td_set_field_lookup_rev' [of t undefined undefined undefined]
  apply(case_tac k, clarsimp)
  apply(drule_tac x=a in spec)
  apply(drule_tac x=m in spec)
  apply(drule_tac x="b - m" in spec)
  apply(frule field_lookup_offset_le)
  apply clarsimp
  done

lemma td_set_struct_field_lookup_structD:
  "field_lookup_struct st f m = Some k \<Longrightarrow> k \<in> td_set_struct st m"
  using td_set_field_lookup_rev' [of undefined st undefined undefined]
  apply(case_tac k, clarsimp)
  apply(thin_tac "All P" for P)
  apply(drule_tac x=a in spec)
  apply(drule_tac x=m in spec)
  apply(drule_tac x="b - m" in spec)
  apply(frule field_lookup_offset_le)
  apply clarsimp
  done

lemma field_lookup_struct_td_simp [simp]:
  "field_lookup_struct ts f m \<noteq> Some (TypDesc ts nm, m)"
  by (fastforce dest: td_set_struct_field_lookup_structD td_set_struct_size_lte)


lemma td_set_list_field_lookup_listD:
  "field_lookup_list xs f m = Some k \<Longrightarrow> k \<in> td_set_list xs m"
  using td_set_field_lookup_rev' [of undefined undefined xs undefined]
  apply(case_tac k, clarsimp)
  apply(thin_tac "All P" for P)
  apply(thin_tac "All P" for P)
  apply(drule_tac x=a in spec)
  apply(drule_tac x=m in spec)
  apply(drule_tac x="b - m" in spec)
  apply(frule field_lookup_offset_le)
  apply clarsimp
  done

lemma td_set_pair_field_lookup_pairD:
  "field_lookup_pair x f m = Some k \<Longrightarrow> k \<in> td_set_pair x m"
  using td_set_field_lookup_rev' [of undefined undefined undefined x]
  apply(case_tac k, clarsimp)
  apply(thin_tac "All P" for P)
  apply(thin_tac "All P" for P)
  apply(thin_tac "All P" for P)
  apply(drule_tac x=a in spec)
  apply(drule_tac x=m in spec)
  apply(drule_tac x="b - m" in spec)
  apply(frule field_lookup_offset_le)
  apply clarsimp
  done


lemma field_lookup_wf_size_desc_gt:
  "\<lbrakk> field_lookup t f n = Some (a,b); wf_size_desc t \<rbrakk> \<Longrightarrow> 0 < size_td a"
  by (fastforce simp: td_set_wf_size_desc wf_size_desc_gt dest!: td_set_field_lookupD)

lemma field_lookup_inject'':
  "\<forall>f g m s. wf_size_desc t \<longrightarrow> field_lookup (t::'a typ_desc) f m = Some s \<and> field_lookup t g m = Some s \<longrightarrow> f=g"
  "\<forall>f g m s. wf_size_desc_struct st \<longrightarrow> field_lookup_struct (st::'a typ_struct) f m = Some s \<and> field_lookup_struct  st g m = Some s \<longrightarrow> f=g"
  "\<forall>f g m s. wf_size_desc_list ts \<longrightarrow> field_lookup_list (ts::'a typ_pair list) f m = Some s \<and> field_lookup_list ts g m = Some s \<longrightarrow> f=g"
  "\<forall>f g m s. wf_size_desc_pair x \<longrightarrow> field_lookup_pair (x::'a typ_pair) f m = Some s \<and> field_lookup_pair x g m = Some s \<longrightarrow> f=g"
  apply(induct t and st and ts and x, all \<open>clarsimp\<close>)
    apply fast
   apply(clarsimp split: option.splits)
      apply fast
     apply(frule td_set_pair_field_lookup_pairD)
     apply(drule field_lookup_offset_le)
     apply(drule td_set_pair_offset_size_m)
     apply(thin_tac "\<forall>f g. P f g" for P)+
     apply(case_tac dt_pair, simp)
     apply(subgoal_tac "0 < size_td a", simp)
     apply(clarsimp split: if_split_asm; drule (2) field_lookup_wf_size_desc_gt)
    apply(frule td_set_pair_field_lookup_pairD)
    apply(drule field_lookup_offset_le)
    apply(drule td_set_pair_offset_size_m)
    apply(thin_tac "\<forall>f g. P f g" for P)+
    apply(case_tac dt_pair, simp )
    apply(subgoal_tac "0 < size_td a", simp)
    apply(clarsimp split: if_split_asm; drule (2) field_lookup_wf_size_desc_gt)+
   apply best
  apply(drule_tac x="tl f" in spec)
  apply(drule_tac x="tl g" in spec)
  apply(case_tac f; simp)
  apply(case_tac g; simp)
  apply fastforce
  done

lemma field_lookup_inject':
  "(\<forall>f g m s. wf_size_desc t \<longrightarrow> field_lookup (t::'a typ_desc) f m = Some s \<and> field_lookup t g m = Some s \<longrightarrow> f=g) \<and>
      (\<forall>f g m s. wf_size_desc_struct st \<longrightarrow> field_lookup_struct (st::'a typ_struct) f m = Some s \<and> field_lookup_struct  st g m = Some s \<longrightarrow> f=g) \<and>
      (\<forall>f g m s. wf_size_desc_list ts \<longrightarrow> field_lookup_list (ts::'a typ_pair list) f m = Some s \<and> field_lookup_list ts g m = Some s \<longrightarrow> f=g) \<and>
      (\<forall>f g m s. wf_size_desc_pair x \<longrightarrow> field_lookup_pair (x::'a typ_pair) f m = Some s \<and> field_lookup_pair x g m = Some s \<longrightarrow> f=g)"
  by (auto simp: field_lookup_inject'')


lemma field_lookup_inject:
  "\<lbrakk> field_lookup (t::'a typ_desc) f m = Some s;
      field_lookup t g m = Some s; wf_size_desc t \<rbrakk> \<Longrightarrow> f=g"
  using field_lookup_inject' [of t undefined undefined undefined]
  apply(cases s)
  apply clarsimp
  apply(drule_tac x=f in spec)
  apply(drule_tac x=g in spec)
  apply fast
  done

lemma fd_cons_update_normalise:
  "\<lbrakk> fd_cons_update_access d n; fd_cons_access_update d n;
        fd_cons_double_update d; fd_cons_length d n \<rbrakk> \<Longrightarrow>
        fd_cons_update_normalise d n"
  apply(clarsimp simp: fd_cons_update_access_def fd_cons_update_normalise_def norm_desc_def)
  apply(drule_tac x="field_update d bs v" in spec)
  apply(drule_tac x="replicate (length bs) 0" in spec)
  apply clarsimp
  apply(clarsimp simp: fd_cons_access_update_def)
  apply(drule_tac x=bs in spec)
  apply clarsimp
  apply(drule_tac x="replicate (length bs) 0" in spec)
  apply clarsimp
  apply(drule_tac x=v in spec)
  apply(drule_tac x=undefined in spec)
  apply clarsimp
  apply(clarsimp simp: fd_cons_double_update_def)
  apply(drule_tac x="v" in spec)
  apply(drule_tac x="field_access d (field_update d bs undefined)
                                    (replicate (length bs) 0)" in spec)
  apply(drule_tac x=bs in spec)
  apply clarsimp
  apply(erule impE)
   apply(clarsimp simp: fd_cons_length_def)
  apply clarsimp
  done

lemma update_ti_t_update_ti_struct_t [simp]:
  "update_ti_t (TypDesc st tn) = update_ti_struct_t st"
  by (auto simp: update_ti_t_def update_ti_struct_t_def)

lemma fd_cons_fd_cons_struct [simp]:
  "fd_cons (TypDesc st tn) = fd_cons_struct st"
  by (clarsimp simp: fd_cons_def fd_cons_struct_def)

lemma update_ti_struct_t_update_ti_list_t [simp]:
  "update_ti_struct_t (TypAggregate ts) = update_ti_list_t ts"
  by (auto simp: update_ti_struct_t_def update_ti_list_t_def)

lemma fd_cons_struct_fd_cons_list [simp]:
  "fd_cons_struct (TypAggregate ts) = fd_cons_list ts"
  by (clarsimp simp: fd_cons_struct_def fd_cons_list_def)

lemma fd_cons_list_empty [simp]:
  "fd_cons_list []"
  by (clarsimp simp: fd_cons_list_def fd_cons_double_update_def
    fd_cons_update_access_def fd_cons_access_update_def fd_cons_length_def
    fd_cons_update_normalise_def update_ti_list_t_def fd_cons_desc_def)

lemma fd_cons_double_update_list_append:
  "\<lbrakk> fd_cons_double_update (field_desc_list xs);
      fd_cons_double_update (field_desc_list ys);
      fu_commutes (field_update (field_desc_list xs)) (field_update (field_desc_list ys)) \<rbrakk> \<Longrightarrow>
      fd_cons_double_update (field_desc_list (xs@ys))"
  by (auto simp: fd_cons_double_update_def fu_commutes_def)

lemma fd_cons_update_access_list_append:
  "\<lbrakk> fd_cons_update_access (field_desc_list xs) (size_td_list xs);
      fd_cons_update_access (field_desc_list ys) (size_td_list ys);
      fd_cons_length (field_desc_list xs) (size_td_list xs);
      fd_cons_length (field_desc_list ys) (size_td_list ys) \<rbrakk> \<Longrightarrow>
      fd_cons_update_access (field_desc_list (xs@ys)) (size_td_list (xs@ys))"
 by (auto simp: fd_cons_update_access_def fd_cons_length_def access_ti_append)

(* FIXME MOVE *)
lemma min_ll:
  "min (x + y) x = (x::nat)"
  by simp

lemma fd_cons_access_update_list_append:
  "\<lbrakk> fd_cons_access_update (field_desc_list xs) (size_td_list xs);
      fd_cons_access_update (field_desc_list ys) (size_td_list ys);
      fu_commutes (field_update (field_desc_list xs)) (field_update (field_desc_list ys)) \<rbrakk> \<Longrightarrow>
      fd_cons_access_update (field_desc_list (xs@ys)) (size_td_list (xs@ys))"
  apply(clarsimp simp: fd_cons_access_update_def)
  apply(drule_tac x="take (size_td_list xs) bs" in spec)
  apply clarsimp
  apply(erule impE)
   apply(clarsimp simp: min_def)
  apply(simp add: access_ti_append)
  apply(drule_tac x="drop (size_td_list xs) bs" in spec)
  apply clarsimp
  apply(drule_tac x="take (size_td_list xs) bs'" in spec)
  apply(simp add: min_ll)
  apply(drule_tac x="update_ti_list_t ys (drop (size_td_list xs) bs) v" in spec)
  apply(drule_tac x="update_ti_list_t ys (drop (size_td_list xs) bs) v'" in spec)
  apply simp
  apply(frule_tac bs="take (size_td_list xs) bs" and
                  bs'="drop (size_td_list xs) bs" and v=v in fu_commutes)
  apply clarsimp
  apply(frule_tac bs="take (size_td_list xs) bs" and
                  bs'="drop (size_td_list xs) bs" and v=v' in fu_commutes)
  apply clarsimp
  done

lemma fd_cons_length_list_append:
  "\<lbrakk> fd_cons_length (field_desc_list xs) (size_td_list xs);
     fd_cons_length (field_desc_list ys) (size_td_list ys) \<rbrakk> \<Longrightarrow>
   fd_cons_length (field_desc_list (xs@ys)) (size_td_list (xs@ys))"
  by (auto simp: fd_cons_length_def access_ti_append)

lemma wf_fdp_insert:
  "wf_fdp (insert x xs) \<Longrightarrow> wf_fdp {x} \<and> wf_fdp xs"
  by (auto simp: wf_fdp_def)

lemma wf_fdp_fd_cons:
  "\<lbrakk> wf_fdp X; (t,m) \<in> X \<rbrakk> \<Longrightarrow> fd_cons t"
  by (auto simp: wf_fdp_def)

lemma wf_fdp_fu_commutes:
  "\<lbrakk> wf_fdp X; (s,m) \<in> X; (t,n) \<in> X; \<not> m \<le> n; \<not> n \<le> m \<rbrakk> \<Longrightarrow>
      fu_commutes (field_update (field_desc s)) (field_update (field_desc t))"
  by (auto simp: wf_fdp_def)

lemma wf_fdp_fa_fu_ind:
  "\<lbrakk> wf_fdp X; (s,m) \<in> X; (t,n) \<in> X; \<not> m \<le> n; \<not> n \<le> m \<rbrakk> \<Longrightarrow>
      fa_fu_ind (field_desc s) (field_desc t) (size_td t) (size_td s)"
  by (auto simp: wf_fdp_def)

lemma wf_fdp_mono:
  "\<lbrakk> wf_fdp Y; X \<subseteq> Y \<rbrakk> \<Longrightarrow> wf_fdp X"
  by (fastforce simp: wf_fdp_def)

lemma tf0 [simp]:
  "tf_set (TypDesc st nm) = {(TypDesc st nm,[])} \<union> tf_set_struct st"
  by (auto simp: tf_set_def tf_set_struct_def)

lemma tf1 [simp]:  "tf_set_struct (TypScalar m algn d) = {}"
  by (clarsimp simp: tf_set_struct_def)

lemma tf2 [simp]:  "tf_set_struct (TypAggregate xs) = tf_set_list xs"
  by (auto simp: tf_set_struct_def tf_set_list_def)

lemma tf3 [simp]:  "tf_set_list [] = {}"
  by (simp add: tf_set_list_def)

lemma tf4:  "tf_set_list (x#xs) = tf_set_pair x \<union> {t. t \<in> tf_set_list xs \<and> snd t \<notin>  snd ` tf_set_pair x}"
  apply(clarsimp simp: tf_set_list_def tf_set_pair_def)
  apply(cases x)
  apply clarsimp
  apply(rename_tac a b)
  apply(rule equalityI; clarsimp)
   apply(rename_tac a' b')
   apply(case_tac b'; clarsimp)
   apply(erule disjE; clarsimp?)
   apply(fastforce dest: field_lookup_list_offset2 split: option.splits)[1]
  apply (rule conjI; clarsimp)
  apply(rename_tac ys n)
  apply(case_tac ys; clarsimp split: option.splits)
  apply(rule conjI; clarsimp simp: image_def)
   apply(drule_tac m="size_td a" in field_lookup_list_offset3)
   apply fast
  apply(drule_tac m="size_td a" in field_lookup_list_offset3)
  apply fast
  done

lemma tf4D:
  "t \<in> tf_set_list (x#xs) \<Longrightarrow> t \<in> (tf_set_pair x \<union> tf_set_list xs)"
  by (clarsimp simp: tf4)

lemma tf4' [simp]:  "wf_desc_list (x#xs) \<Longrightarrow>
  tf_set_list (x#xs) = tf_set_pair x \<union> tf_set_list xs"
  apply(simp add: tf4)
  apply(rule equalityI; clarsimp)
  apply(rename_tac ys)
  apply(clarsimp simp: tf_set_pair_def tf_set_list_def)
  apply(case_tac x, simp)
  apply(clarsimp split: if_split_asm)
  apply(case_tac ys; simp)
  apply(drule_tac fs=list and m=0 in field_lookup_list_None)
  apply fastforce
  done

lemma tf5 [simp]:  "tf_set_pair (DTPair t m) = {(a,m#b) | a b. (a,b) \<in> tf_set t}"
  apply(clarsimp simp: tf_set_pair_def tf_set_def)
  apply(rule equalityI; clarsimp)
  apply(rename_tac xs n)
  apply(case_tac xs; clarsimp)
  done

lemma tf_set_self [simp]:
  "(t,[]) \<in> tf_set t"
  by (clarsimp simp: tf_set_def)


lemma tf_set_list_mem [rule_format]:
  "\<forall>t n. wf_desc_list ts \<longrightarrow>  DTPair t n \<in> set ts \<longrightarrow> (t,[n]) \<in> tf_set_list ts"
  by (induct_tac ts) auto

lemma tf_set_list_append [rule_format]:
  "\<forall>ys. wf_desc_list (xs@ys) \<longrightarrow> tf_set_list (xs@ys) = tf_set_list xs \<union> tf_set_list ys"
  apply(induct_tac xs; clarsimp)
  apply(subst tf4'; fastforce)
  done

lemma lf_set_list_append [simp]:
  "lf_set_list (xs@ys) fn = lf_set_list xs fn \<union> lf_set_list ys fn"
  by (induct_tac xs) auto

lemma ti_ind_sym:
  "ti_ind X Y \<Longrightarrow> ti_ind Y X"
  by (auto simp: ti_ind_def fu_commutes_def)

lemma ti_ind_sym2:
  "ti_ind X Y = ti_ind Y X"
  by (blast dest: ti_ind_sym)

lemma ti_ind_list [simp]:
  "ti_ind (X \<union> Y) Z = (ti_ind X Z \<and> ti_ind Y Z)"
  unfolding ti_ind_def by auto

lemma ti_empty [simp]:
  "ti_ind {} X"
  by (simp add: ti_ind_def)

lemma wf_lf_list:
  "lf_fn ` X \<inter> lf_fn ` Y = {} \<Longrightarrow>
      wf_lf (X \<union> Y) = (wf_lf X \<and> wf_lf Y \<and> ti_ind X Y)"
  unfolding wf_lf_def ti_ind_def field_desc_def fu_commutes_def
  apply (rule iffI; clarsimp)
   apply(frule_tac x=x in spec)
   apply(drule_tac x=y in spec)
   apply clarsimp
   apply(drule_tac x=y in spec)
   apply(drule_tac x=x in spec)
   apply clarsimp
   apply fastforce
  apply fast
  done

lemma wf_lf_listD:
  "wf_lf (X \<union> Y) \<Longrightarrow> wf_lf X \<and> wf_lf Y"
  unfolding wf_lf_def ti_ind_def field_desc_def fu_commutes_def by clarsimp

lemma ti_ind_fn:
  "\<forall>fn. ti_ind (lf_set t fn) Y = ti_ind (lf_set t []) Y"
  "\<forall>fn. ti_ind (lf_set_struct st fn) Y = ti_ind (lf_set_struct st []) Y"
  "\<forall>fn. ti_ind (lf_set_list ts fn) Y = ti_ind (lf_set_list ts []) Y"
  "\<forall>fn. ti_ind (lf_set_pair x fn) Y = ti_ind (lf_set_pair x []) Y"
  apply(induct t and st and ts and x, all \<open>clarsimp\<close>)
    apply (fastforce simp: ti_ind_def)
   apply auto
  done

lemma ti_ind_ld_td':
  "ti_ind (lf_set t []) Y \<longrightarrow> ti_ind {t2d (t,[])} Y"
  "ti_ind (lf_set_struct st []) Y \<longrightarrow> ti_ind {\<lparr> lf_fd = field_desc_struct st, lf_sz = size_td_struct st, lf_fn = [] \<rparr>} Y"
  "ti_ind (lf_set_list ts []) Y \<longrightarrow> ti_ind {\<lparr> lf_fd = field_desc_list ts, lf_sz = size_td_list ts, lf_fn = [] \<rparr>} Y"
  "ti_ind (lf_set_pair x []) Y \<longrightarrow> ti_ind {\<lparr> lf_fd = field_desc_pair x, lf_sz = size_td_pair x, lf_fn = [] \<rparr>} Y"
  apply(induct t and st and ts and x, all \<open>clarsimp simp: t2d_def\<close>)
     apply((clarsimp simp: ti_ind_def fu_commutes_def fa_fu_ind_def)+)[3]
  apply(subst (asm) ti_ind_fn)
  apply simp
  done

lemma ti_ind_ld_td_struct:
  "ti_ind (lf_set_struct st fn) Y \<Longrightarrow>
   ti_ind {\<lparr> lf_fd = field_desc_struct st, lf_sz = size_td_struct st, lf_fn = [] \<rparr>} Y"
  by (subst (asm) ti_ind_fn) (simp only: ti_ind_ld_td')

lemma ti_ind_ld_td_list:
  "ti_ind (lf_set_list ts fn) Y \<Longrightarrow>
   ti_ind {\<lparr> lf_fd = field_desc_list ts, lf_sz = size_td_list ts, lf_fn = [] \<rparr>} Y"
  by (subst (asm) ti_ind_fn) (simp only: ti_ind_ld_td')

lemma ti_ind_ld_td_pair:
  "ti_ind (lf_set_pair x fn) Y \<Longrightarrow>
   ti_ind {\<lparr> lf_fd = field_desc_pair x, lf_sz = size_td_pair x, lf_fn = [] \<rparr>} Y"
  by (subst (asm) ti_ind_fn) (simp only: ti_ind_ld_td')

lemma ti_ind_ld':
  "ti_ind (lf_set t []) Y \<longrightarrow> ti_ind (t2d ` (tf_set t)) Y"
  "ti_ind (lf_set_struct st []) Y \<longrightarrow> ti_ind (t2d ` (tf_set_struct st)) Y"
  "ti_ind (lf_set_list ts []) Y \<longrightarrow> ti_ind (t2d ` (tf_set_list ts)) Y"
  "ti_ind (lf_set_pair x []) Y \<longrightarrow> ti_ind (t2d ` (tf_set_pair x)) Y"
  apply(induct t and st and ts and x, all \<open>clarsimp\<close>)
    apply(frule ti_ind_ld_td_struct)
    apply(subst insert_def)
    apply(subst ti_ind_list)
    apply(clarsimp simp: ti_ind_def t2d_def)
   apply(clarsimp simp: ti_ind_def t2d_def)
   apply(drule tf4D)
   apply clarsimp
   apply(erule disjE)
    apply(thin_tac "All P" for P)
    apply(thin_tac "All P" for P)
    apply(drule_tac x="t2d (a,b)" in spec)
    apply(thin_tac "\<forall>x y. P x y" for P)
    apply(drule_tac x="y" in spec)
    apply(fastforce simp: t2d_def image_def)
   apply(thin_tac "All P" for P)
   apply(thin_tac "All P" for P)
   apply(thin_tac "All P" for P)
   apply(drule_tac x="t2d (a,b)" in spec)
   apply(drule_tac x="y" in spec)
   apply(fastforce simp: t2d_def image_def)
  apply(rotate_tac)
  apply(subst (asm) ti_ind_fn)
  apply(simp add: t2d_def)
  apply(clarsimp simp: ti_ind_def)
  apply(thin_tac "All P" for P)
  apply(drule_tac x="t2d (aa,ba)" in spec)
  apply(drule_tac x=y in spec)
  apply(fastforce simp: t2d_def image_def)
  done

lemma ti_ind_ld:
  "ti_ind (lf_set t fn) Y \<Longrightarrow> ti_ind (t2d ` (tf_set t)) Y"
  by (subst (asm) ti_ind_fn) (simp only: ti_ind_ld')

lemma ti_ind_ld_struct:
  "ti_ind (lf_set_struct t fn) Y \<Longrightarrow> ti_ind (t2d ` (tf_set_struct t)) Y"
  by (subst (asm) ti_ind_fn) (simp only: ti_ind_ld')

lemma ti_ind_ld_list:
  "ti_ind (lf_set_list t fn) Y \<Longrightarrow> ti_ind (t2d ` (tf_set_list t)) Y"
  by (subst (asm) ti_ind_fn) (simp only: ti_ind_ld')

lemma ti_ind_ld_pair:
  "ti_ind (lf_set_pair t fn) Y \<Longrightarrow> ti_ind (t2d ` (tf_set_pair t)) Y"
  by (subst (asm) ti_ind_fn) (simp only: ti_ind_ld')

lemma lf_set_fn':
  "\<forall>s fn. s \<in> lf_set (t::'a typ_info) fn \<longrightarrow> fn \<le> lf_fn s"
  "\<forall>s fn. s \<in> lf_set_struct (st::'a typ_info_struct) fn \<longrightarrow> fn \<le> lf_fn s"
  "\<forall>s fn. s \<in> lf_set_list (ts::'a typ_info_pair list) fn \<longrightarrow> fn \<le> lf_fn s"
  "\<forall>s fn. s \<in> lf_set_pair (x::'a typ_info_pair) fn \<longrightarrow> fn \<le> lf_fn s"
  apply(induct t and st and ts and x, all \<open>clarsimp\<close>)
  apply(drule_tac x=s in spec)
  apply(drule_tac x="fn @ [list]" in spec)
  apply(clarsimp simp: prefix_def less_eq_list_def)
  done

lemma lf_set_fn:
  "s \<in> lf_set (t::'a typ_info) fn \<Longrightarrow> fn \<le> lf_fn s"
  by (clarsimp simp: lf_set_fn')

lemma ln_fn_disj [rule_format]:
  "\<forall>x. dt_snd x \<notin> dt_snd ` set xs \<longrightarrow> lf_fn ` lf_set_pair x fn \<inter> lf_fn ` lf_set_list xs fn = {}"
  apply (induct_tac xs; clarsimp)
  apply (rule set_eqI, clarsimp)
  apply (erule disjE)
   apply (clarsimp dest!: lf_set_fn simp: split_DTPair_all prefix_def less_eq_list_def)
  apply fastforce
  done

lemma wf_lf_fn:
  "\<forall>fn. wf_desc t \<longrightarrow> wf_lf (lf_set (t::'a typ_info) fn) = wf_lf (lf_set t [])"
  "\<forall>fn. wf_desc_struct st \<longrightarrow> wf_lf (lf_set_struct (st::'a typ_info_struct) fn) = wf_lf (lf_set_struct  st [])"
  "\<forall>fn. wf_desc_list ts \<longrightarrow> wf_lf (lf_set_list (ts::'a typ_info_pair list) fn) = wf_lf (lf_set_list ts [])"
  "\<forall>fn. wf_desc_pair x \<longrightarrow> wf_lf (lf_set_pair (x::'a typ_info_pair) fn) = wf_lf (lf_set_pair x [])"
  apply(induct t and st and ts and x)
       apply clarify
       apply(drule_tac x=fn in spec)
       apply clarsimp
      apply clarsimp
      apply(clarsimp simp: wf_lf_def)
     apply clarify
     apply(drule_tac x=fn in spec)
     apply clarsimp
    apply(clarsimp simp: wf_lf_def)
   apply clarify
   apply(drule_tac x=fn in spec)+
   apply clarsimp
   apply(subst wf_lf_list)
    apply(erule ln_fn_disj)
   apply(subst wf_lf_list)
    apply(erule ln_fn_disj)
   apply clarsimp
   apply(subst ti_ind_fn)
   apply(subst ti_ind_sym2)
   apply(subst ti_ind_fn)
   apply(subst ti_ind_sym2)
   apply(clarsimp)
  apply clarify
  apply(frule_tac x="[list]" in spec)
  apply(drule_tac x="fn@[list]" in spec)
  apply clarsimp
  done

lemma wf_lf_fd_cons':
  "\<forall>m. wf_lf (lf_set (t::'a typ_info) []) \<longrightarrow> wf_desc t \<longrightarrow> fd_cons t"
  "\<forall>m. wf_lf (lf_set_struct (st::'a typ_info_struct) []) \<longrightarrow> wf_desc_struct st \<longrightarrow> fd_cons_struct st"
  "\<forall>m. wf_lf (lf_set_list (ts::'a typ_info_pair list) []) \<longrightarrow> wf_desc_list ts \<longrightarrow> fd_cons_list ts"
  "\<forall>m. wf_lf (lf_set_pair (x::'a typ_info_pair) []) \<longrightarrow> wf_desc_pair x \<longrightarrow> fd_cons_pair x"
  apply(induct t and st and ts and x)
       apply clarsimp
      apply(clarsimp simp: wf_lf_def fd_cons_struct_def fd_cons_def)
      apply(clarsimp simp: fd_cons_desc_def fd_cons_double_update_def fd_cons_update_access_def
                           fd_cons_access_update_def fd_cons_length_def)
     apply clarsimp
    apply clarsimp
   apply clarsimp
   apply(subst (asm) wf_lf_list)
    apply(erule ln_fn_disj)
   apply clarsimp
   apply(drule ti_ind_ld_td_pair)
   apply(drule ti_ind_sym)
   apply(drule ti_ind_ld_td_list)
   apply(drule ti_ind_sym)
   apply(clarsimp simp: ti_ind_def)
   apply(clarsimp simp: fd_cons_list_def fd_cons_desc_def)
   apply(rule conjI)
    apply(clarsimp simp: fd_cons_pair_def fd_cons_double_update_def fd_cons_desc_def)
    apply(simp add: fu_commutes_def)
   apply(rule conjI)
    apply(clarsimp simp: fd_cons_pair_def fd_cons_update_access_def fd_cons_desc_def)
    apply(clarsimp simp: fd_cons_length_def)
   apply(rule conjI)
    apply(clarsimp simp: fd_cons_pair_def fd_cons_desc_def)
    apply(clarsimp simp: fd_cons_access_update_def)
    apply(simp add: fu_commutes_def)
    apply(clarsimp simp: fa_fu_ind_def)
    apply(thin_tac "All P" for P)
    apply(thin_tac "All P" for P)
    apply(thin_tac "All P" for P)
    apply(rotate_tac -4)
    apply(drule_tac x="take (size_td_pair dt_pair) bs" in spec)
    apply clarsimp
    apply(erule impE)
     apply(clarsimp simp: min_def split: if_split_asm)
    apply(rotate_tac -1)
    apply(drule_tac x="take (size_td_pair dt_pair) bs'" in spec)
    apply(simp add: min_ll)
    apply(drule_tac x=v in spec)
    apply(drule_tac x=v' in spec)
    apply simp
   apply(clarsimp simp: fd_cons_length_def fd_cons_pair_def fd_cons_desc_def)
  apply clarsimp
  apply(rotate_tac)
  apply(subst (asm) wf_lf_fn, assumption)
  apply(clarsimp simp: fd_cons_def fd_cons_pair_def export_uinfo_def)
  done

lemma wf_lf_fd_cons:
  "\<lbrakk> wf_lf (lf_set t fn); wf_desc t \<rbrakk> \<Longrightarrow> fd_cons t"
  by (subst (asm) wf_lf_fn; simp only: wf_lf_fd_cons')

lemma wf_lf_fd_cons_struct:
  "\<lbrakk> wf_lf (lf_set_struct t fn); wf_desc_struct t \<rbrakk> \<Longrightarrow> fd_cons_struct t"
  by (subst (asm) wf_lf_fn; simp only: wf_lf_fd_cons')

lemma wf_lf_fd_cons_list:
  "\<lbrakk> wf_lf (lf_set_list t fn); wf_desc_list t \<rbrakk> \<Longrightarrow> fd_cons_list t"
  by (subst (asm) wf_lf_fn; simp only: wf_lf_fd_cons')

lemma wf_lf_fd_cons_pair:
  "\<lbrakk> wf_lf (lf_set_pair t fn); wf_desc_pair t \<rbrakk> \<Longrightarrow> fd_cons_pair t"
  by (subst (asm) wf_lf_fn; simp only: wf_lf_fd_cons')

lemma wf_lf_fdp':
  "\<forall>m. wf_lf (lf_set (t::'a typ_info) []) \<longrightarrow> wf_desc t \<longrightarrow> wf_fdp (tf_set t)"
  "\<forall>m. wf_lf (lf_set_struct (st::'a typ_info_struct) []) \<longrightarrow> wf_desc_struct st \<longrightarrow> wf_fdp (tf_set_struct st)"
  "\<forall>m. wf_lf (lf_set_list (ts::'a typ_info_pair list) []) \<longrightarrow> wf_desc_list ts \<longrightarrow> wf_fdp (tf_set_list ts)"
  "\<forall>m. wf_lf (lf_set_pair (x::'a typ_info_pair) []) \<longrightarrow> wf_desc_pair x \<longrightarrow> wf_fdp (tf_set_pair x)"
  apply(induct t and st and ts and x, all \<open>clarsimp simp: wf_fdp_def\<close>)
    apply (fastforce elim: wf_lf_fd_cons_struct)
   apply(subst (asm) wf_lf_list)
    apply(erule ln_fn_disj)
   apply clarsimp
   apply(drule ti_ind_ld_pair)
   apply(drule ti_ind_sym)
   apply(drule ti_ind_ld_list)
   apply(drule ti_ind_sym)
   apply(rule conjI, clarsimp)
    apply(erule disjE, fast)
    apply(clarsimp simp: ti_ind_def t2d_def)
    apply(drule_tac x="t2d (x,m)" in spec)
    apply(drule_tac x="t2d (y,n)" in spec)
    apply(clarsimp simp: t2d_def image_def)
    apply(erule impE)
     apply(rule conjI)
      apply(rule_tac x="(x,m)" in bexI)
       apply clarsimp
      apply assumption
     apply(rule_tac x="(y,n)" in bexI)
      apply clarsimp
     apply assumption
    apply clarsimp
   apply clarsimp
   apply(erule disjE)
    apply(clarsimp simp: ti_ind_def t2d_def)
    apply(drule_tac x="t2d (y,n)" in spec)
    apply(drule_tac x="t2d (x,m)" in spec)
    apply(clarsimp simp: t2d_def image_def)
    apply(erule impE)
     apply(rule)
      apply(rule_tac x="(y,n)" in bexI)
       apply clarsimp
      apply assumption
     apply(rule_tac x="(x,m)" in bexI)
      apply clarsimp
     apply assumption
    apply clarsimp
    apply(clarsimp simp: fu_commutes_def)
   apply fast
  apply(rotate_tac)
  apply(subst (asm) wf_lf_fn, assumption)
  apply(clarsimp simp: wf_fdp_def)
  apply fast
  done

lemma wf_lf_fdp:
  "\<lbrakk> wf_lf (lf_set t []); wf_desc t \<rbrakk> \<Longrightarrow> wf_fdp (tf_set t)"
  by (simp only: wf_lf_fdp')

lemma wf_fd_field_lookup [rule_format]:
  "\<forall>f m n s. wf_fd (t::'a typ_info) \<longrightarrow> field_lookup t f m = Some (s,n) \<longrightarrow> wf_fd s"
  "\<forall>f m n s. wf_fd_struct (st::'a typ_info_struct) \<longrightarrow> field_lookup_struct st f m = Some (s,n) \<longrightarrow> wf_fd s"
  "\<forall>f m n s. wf_fd_list (ts::'a typ_info_pair list) \<longrightarrow> field_lookup_list ts f m = Some (s,n) \<longrightarrow> wf_fd s"
  "\<forall>f m n s. wf_fd_pair (x::'a typ_info_pair) \<longrightarrow> field_lookup_pair x f m = Some (s,n) \<longrightarrow> wf_fd s"
  by (induct t and st and ts and x) (clarsimp split: option.splits)+

lemma wf_fd_field_lookupD:
  "\<lbrakk> field_lookup t f m = Some (s,n); wf_fd t \<rbrakk> \<Longrightarrow> wf_fd s"
  by (rule wf_fd_field_lookup)

lemma wf_fd_tf_set:
  "\<lbrakk> wf_fd t; ((s::'a typ_info),m) \<in> tf_set t \<rbrakk> \<Longrightarrow> wf_fd s"
  by (fastforce simp: tf_set_def wf_fd_field_lookupD)

lemma tf_set_field_lookupD:
  "field_lookup t f m = Some (s,n) \<Longrightarrow> (s,f) \<in> tf_set t"
  unfolding tf_set_def
  by (clarsimp simp flip: field_lookup_offset[where m=m] dest!: field_lookup_offset_le) arith

lemma fu_commutes_ts [rule_format]:
  "(\<forall>t. t \<in> dt_fst ` set ts \<longrightarrow> fu_commutes d (update_ti_t t)) \<longrightarrow>
      fu_commutes d (update_ti_list_t ts)"
  by (induct ts; clarsimp simp: fu_commutes_def) (clarsimp simp: split_DTPair_all)

lemma fa_fu_ind_ts [rule_format]:
  "(\<forall>t. t \<in> dt_fst ` set ts \<longrightarrow> fa_fu_ind d (field_desc t) (size_td t) n) \<longrightarrow>
      fa_fu_ind d \<lparr> field_access = access_ti_list ts,
              field_update = update_ti_list_t ts\<rparr>
           (size_td_list ts) n"
  by (induct ts; clarsimp simp: fa_fu_ind_def) (clarsimp simp: split_DTPair_all)

lemma fa_fu_ind_ts2 [rule_format]:
  "(\<forall>t. t \<in> dt_fst ` set ts \<longrightarrow> fa_fu_ind (field_desc t) d n (size_td t)) \<longrightarrow>
      fa_fu_ind \<lparr> field_access = access_ti_list ts,
              field_update = update_ti_list_t ts\<rparr> d
           n (size_td_list ts)"
  by (induct ts; clarsimp simp: fa_fu_ind_def) (clarsimp simp: split_DTPair_all)

lemma wf_fdp_fd [rule_format]:
  "\<forall>m. wf_fdp (tf_set t) \<longrightarrow> wf_desc t \<longrightarrow> wf_fd (t::'a typ_info)"
  "\<forall>m. (case st of TypScalar sz algn d \<Rightarrow> fd_cons_struct (TypScalar sz algn d)
           | _ \<Rightarrow> wf_fdp (tf_set_struct st)) \<longrightarrow> wf_desc_struct st \<longrightarrow> wf_fd_struct (st::'a typ_info_struct)"
  "\<forall>m. wf_fdp (tf_set_list ts) \<longrightarrow> wf_desc_list ts \<longrightarrow> wf_fd_list (ts::'a typ_info_pair list)"
  "\<forall>m. wf_fdp (tf_set_pair x) \<longrightarrow> wf_desc_pair x \<longrightarrow> wf_fd_pair (x::'a typ_info_pair)"
  apply(induct t and st and ts and x, all \<open>clarsimp\<close>)
    apply(clarsimp split: typ_struct.split_asm)
     apply(clarsimp simp: wf_fdp_def fd_cons_def fd_cons_struct_def)
    apply (fastforce dest: wf_fdp_mono)
   apply (rename_tac dt_pair xs)
   apply (rule conjI, fastforce dest: wf_fdp_mono)
   apply (rule conjI)
    apply(subgoal_tac "wf_fdp (tf_set_list xs)", simp)
    apply (fastforce elim: wf_fdp_mono)
   apply(clarsimp simp: wf_fdp_def)
   apply(case_tac dt_pair, clarsimp)
   apply(rename_tac a b)
   apply(frule_tac x=a in spec)
   apply(drule_tac x="[b]" in spec)
   apply clarsimp
   apply (rule conjI)
    apply(rule fu_commutes_ts)
    apply clarsimp
    apply(rename_tac x)
    apply(drule_tac x="dt_fst x" in spec, erule impE, rule_tac x="[dt_snd x]" in exI)
     apply(fastforce simp: image_iff tf_set_list_mem)
    apply simp
   apply(rule conjI)
    apply(rule fa_fu_ind_ts)
    apply clarsimp
    apply(rename_tac x)
    apply(drule_tac x="dt_fst x" in spec, erule impE, rule_tac x="[dt_snd x]" in exI)
     apply(fastforce simp: image_iff tf_set_list_mem)
    apply simp
   apply(rule fa_fu_ind_ts2)
   apply(drule_tac x=t in spec)
   apply clarsimp
   apply(case_tac x, clarsimp)
   apply(rename_tac aa ba)
   apply(drule_tac x="[ba]" in spec)
   apply clarsimp
   apply(simp add: tf_set_list_mem)
   apply clarsimp
   apply(thin_tac "All P" for P)
   apply(drule_tac x=a in spec)
   apply (erule impE, rule_tac x="[b]" in exI)
    apply simp
    apply(rule, clarsimp)
     apply(clarsimp simp: image_def)
     apply(drule_tac x="DTPair aa b" in bspec, simp+)[1]
    apply(clarsimp simp: image_def)
    apply(drule_tac x="DTPair aa ba" in bspec, simp+)[1]
   apply simp
  apply(clarsimp simp: wf_fdp_def)
  apply(drule_tac x=x in spec)
  apply(drule_tac x="list#m" in spec)
  apply clarsimp
  apply(drule_tac x=y in spec)
  apply auto
  done

lemma wf_fdp_fdD:
  "\<lbrakk> wf_fdp (tf_set t); wf_desc t \<rbrakk> \<Longrightarrow> wf_fd (t::'a typ_info)"
  by (rule wf_fdp_fd)

lemma wf_fdp_fd_listD:
  "\<lbrakk> wf_fdp (tf_set_list t); wf_desc_list t \<rbrakk> \<Longrightarrow> wf_fd_list t"
  by (rule wf_fdp_fd)

lemma fd_consistentD:
  "\<lbrakk> field_lookup t f 0 = Some (s,n); fd_consistent t \<rbrakk>
      \<Longrightarrow> fd_cons s"
  by (fastforce simp: fd_consistent_def)

lemma wf_fd_cons_access_update' [rule_format]:
  "wf_fd (t::'a typ_info) \<longrightarrow> fd_cons_access_update (field_desc t) (size_td t)"
  "wf_fd_struct (st::'a typ_info_struct) \<longrightarrow> fd_cons_access_update (field_desc_struct st) (size_td_struct st)"
  "wf_fd_list (ts::'a typ_info_pair list) \<longrightarrow> fd_cons_access_update (field_desc_list ts) (size_td_list ts)"
  "wf_fd_pair (x::'a typ_info_pair) \<longrightarrow> fd_cons_access_update (field_desc_pair x) (size_td_pair x)"
  apply(induct t and st and ts and x, all \<open>clarsimp split: typ_struct.splits\<close>)
    apply(clarsimp simp: fd_cons_access_update_def fd_cons_struct_def fd_cons_desc_def)
   apply(clarsimp simp: fd_cons_access_update_def)
  apply(clarsimp simp: fd_cons_access_update_def)
  apply(simp add: fu_commutes_def)
  apply(clarsimp simp: fa_fu_ind_def)
  apply(drule_tac x="(take (size_td_pair dt_pair) bs)" in spec)
  apply(erule impE)
   apply(clarsimp simp: min_def split: if_split_asm)
  apply(rotate_tac -1)
  apply(drule_tac x="take (size_td_pair dt_pair) bs'" in spec)
  apply(simp add: min_ll)
  apply(rotate_tac -1)
  apply(drule_tac x=v in spec)
  apply(rotate_tac -1)
  apply(drule_tac x=v' in spec)
  apply simp
  done


lemma wf_fd_cons_access_updateD:
  "wf_fd t \<Longrightarrow> fd_cons_access_update (field_desc t) (size_td t)"
  by (rule wf_fd_cons_access_update')

lemma wf_fd_cons_access_update_structD:
  "wf_fd_struct t \<Longrightarrow> fd_cons_access_update (field_desc_struct t) (size_td_struct t)"
  by (rule wf_fd_cons_access_update')

lemma wf_fd_cons_access_update_listD:
  "wf_fd_list t \<Longrightarrow> fd_cons_access_update (field_desc_list t) (size_td_list t)"
  by (rule wf_fd_cons_access_update')

lemma wf_fd_cons_access_update_pairD:
  "wf_fd_pair t \<Longrightarrow> fd_cons_access_update (field_desc_pair t) (size_td_pair t)"
  by (rule wf_fd_cons_access_update')

lemma wf_fd_norm_tu:
  "\<forall>bs. wf_fd t \<longrightarrow> length bs = size_td t \<longrightarrow> norm_tu (export_uinfo (t::'a typ_info)) bs = (access_ti t (update_ti_t t bs undefined) (replicate (size_td t) 0))"
  "\<forall>bs. wf_fd_struct st \<longrightarrow> length bs = size_td_struct st \<longrightarrow> norm_tu_struct (map_td_struct field_norm (st::'a typ_info_struct)) bs = (access_ti_struct st (update_ti_struct_t st bs undefined) (replicate (size_td_struct st) 0))"
  "\<forall>bs. wf_fd_list ts \<longrightarrow> length bs = size_td_list ts \<longrightarrow> norm_tu_list (map_td_list field_norm (ts::'a typ_info_pair list)) bs = (access_ti_list ts (update_ti_list_t ts bs undefined) (replicate (size_td_list ts) 0))"
  "\<forall>bs. wf_fd_pair x \<longrightarrow> length bs = size_td_pair x \<longrightarrow> norm_tu_pair (map_td_pair field_norm (x::'a typ_info_pair)) bs = (access_ti_pair x (update_ti_pair_t x bs undefined) (replicate (size_td_pair x) 0))"
  apply(induct t and st and ts and x, all \<open>clarsimp simp: export_uinfo_def\<close>)
   apply(simp add: field_norm_def)
  apply(simp add: fu_commutes_def)
  apply(simp add: fa_fu_ind_def)
  apply(drule wf_fd_cons_access_update_listD)
  apply(clarsimp simp: fd_cons_access_update_def export_uinfo_def min_def)
  done

lemma wf_fd_norm_tuD:
  "\<lbrakk> wf_fd t; length bs = size_td t \<rbrakk>  \<Longrightarrow> norm_tu (export_uinfo t) bs =
      (access_ti\<^sub>0 t (update_ti_t t bs undefined))"
  using wf_fd_norm_tu(1) [of t] by (clarsimp simp: access_ti\<^sub>0_def)

lemma wf_fd_norm_tu_structD:
  "\<lbrakk> wf_fd_struct t; length bs = size_td_struct t \<rbrakk> \<Longrightarrow> norm_tu_struct (map_td_struct field_norm t) bs =
      (access_ti_struct t (update_ti_struct_t t bs undefined) (replicate (size_td_struct t) 0))"
  using wf_fd_norm_tu(2) [of t] by clarsimp

lemma wf_fd_norm_tu_listD:
  "\<lbrakk> wf_fd_list t; length bs = size_td_list t \<rbrakk> \<Longrightarrow> norm_tu_list (map_td_list field_norm t) bs =
      (access_ti_list t (update_ti_list_t t bs undefined) (replicate (size_td_list t) 0))"
  using wf_fd_norm_tu(3) [of t] by clarsimp

lemma wf_fd_norm_tu_pairD:
  "\<lbrakk> wf_fd_pair t; length bs = size_td_pair t \<rbrakk> \<Longrightarrow> norm_tu_pair (map_td_pair field_norm t) bs =
      (access_ti_pair t (update_ti_pair_t t bs undefined) (replicate (size_td_pair t) 0))"
  using wf_fd_norm_tu(4) [of t] by clarsimp

lemma wf_fd_cons [rule_format]:
  "wf_fd t \<longrightarrow> fd_cons (t::'a typ_info)"
  "wf_fd_struct st \<longrightarrow> fd_cons_struct (st::'a typ_info_struct)"
  "wf_fd_list ts \<longrightarrow> fd_cons_list (ts::'a typ_info_pair list)"
  "wf_fd_pair x \<longrightarrow> fd_cons_pair (x::'a typ_info_pair)"
  apply(induct t and st and ts and x, all \<open>clarsimp\<close>)
   apply(clarsimp simp: fd_cons_list_def fd_cons_desc_def)
   apply (rule conjI)
    apply(clarsimp simp: fd_cons_pair_def fd_cons_double_update_def fd_cons_desc_def)
    apply(simp add: fu_commutes_def)
   apply (rule conjI)
    apply(clarsimp simp: fd_cons_pair_def fd_cons_update_access_def fd_cons_desc_def)
    apply(clarsimp simp: fd_cons_length_def)
   apply (rule conjI)
    apply(clarsimp simp: fd_cons_pair_def fd_cons_desc_def)
    apply(clarsimp simp: fd_cons_access_update_def fu_commutes_def fa_fu_ind_def)
    apply(rotate_tac -4)
    apply(drule_tac x="take (size_td_pair dt_pair) bs" in spec)
    apply clarsimp
    apply(erule impE)
     apply(clarsimp simp: min_def split: if_split_asm)
    apply(rotate_tac -1)
    apply(drule_tac x="take (size_td_pair dt_pair) bs'" in spec)
    apply(simp add: min_ll)
    apply(rotate_tac -1)
    apply(drule_tac x=v in spec)
    apply(rotate_tac -1)
    apply(drule_tac x=v' in spec)
    apply simp
   apply(clarsimp simp: fd_cons_length_def fd_cons_pair_def  fd_cons_desc_def)
  apply(clarsimp simp: fd_cons_def fd_cons_pair_def export_uinfo_def)
  done

lemma wf_fd_consD:
  "wf_fd t \<Longrightarrow> fd_cons t"
  by (rule wf_fd_cons)

lemma wf_fd_cons_structD:
  "wf_fd_struct t \<Longrightarrow> fd_cons_struct t"
  by (rule wf_fd_cons)

lemma wf_fd_cons_listD:
  "wf_fd_list t \<Longrightarrow> fd_cons_list t"
  by (rule wf_fd_cons)

lemma wf_fd_cons_pairD:
  "wf_fd_pair t \<Longrightarrow> fd_cons_pair t"
  by (rule wf_fd_cons)

lemma fd_cons_list_append:
  "\<lbrakk> wf_fd_list xs; wf_fd_list ys; fu_commutes
      (field_update (field_desc_list xs)) (field_update (field_desc_list ys)) \<rbrakk> \<Longrightarrow>
      fd_cons_list (xs@ys)"
  apply(frule wf_fd_cons_listD)
  apply(frule wf_fd_cons_listD [where t=ys])
  apply(unfold fd_cons_list_def fd_cons_desc_def)
  apply(fastforce intro: fd_cons_double_update_list_append fd_cons_update_access_list_append
                         fd_cons_access_update_list_append fd_cons_length_list_append)
  done


lemma wf_fd [simp]:
  "wf_fd (typ_info_t TYPE('a::wf_type))"
  by (fastforce intro: wf_fdp_fdD wf_lf_fdp wf_lf)

lemma fd_cons [simp]:
  "fd_consistent (typ_info_t TYPE('a::wf_type))"
  unfolding fd_consistent_def by (fastforce intro: wf_fd_consD wf_fd_field_lookupD)

lemma field_lvalue_append [simp]:
  "\<lbrakk> field_ti TYPE('b::wf_type) f = Some t;
      export_uinfo t = typ_uinfo_t TYPE('a::c_type);
      field_ti TYPE('a) g = Some k \<rbrakk> \<Longrightarrow>
          &(((Ptr &((p::'b ptr)\<rightarrow>f))::'a ptr)\<rightarrow>g) = &(p\<rightarrow>f@g)"
  apply(clarsimp simp: field_lvalue_def field_ti_def field_offset_def
                       field_offset_untyped_def typ_uinfo_t_def
                 split: option.splits)
  apply(subst field_lookup_prefix_Some')
    apply(fastforce dest: field_lookup_export_uinfo_Some)
   apply(simp add: export_uinfo_def wf_desc_map)
  apply(drule field_lookup_export_uinfo_Some)
  apply(simp add: export_uinfo_def)
  apply(drule field_lookup_export_uinfo_Some)
  apply(simp add: export_uinfo_def)
  apply(rename_tac m n)
  apply(subgoal_tac "field_lookup (typ_uinfo_t TYPE('a)) g m = Some (export_uinfo k, m + n)")
   apply(simp add: typ_uinfo_t_def export_uinfo_def)
  apply(simp add: typ_uinfo_t_def field_lookup_offset export_uinfo_def)
  done

lemma field_access_update_take_drop [rule_format]:
  "\<forall>f s m n bs bs' v. field_lookup t f m = Some (s,m+n) \<longrightarrow>
      length bs = size_td t \<longrightarrow> length bs' = size_td s \<longrightarrow> wf_fd t \<longrightarrow>
      field_access (field_desc s) (field_update (field_desc t) bs v) bs'
          = field_access (field_desc s) (field_update (field_desc s)
              (take (size_td (s::'a typ_info)) (drop n bs)) undefined) bs'"
  "\<forall>f s m n bs bs' v. field_lookup_struct st f m = Some (s,m+n) \<longrightarrow>
      length bs = size_td_struct st \<longrightarrow> length bs' = size_td s \<longrightarrow> wf_fd_struct st \<longrightarrow>
      field_access (field_desc s) (field_update (field_desc_struct st) bs v) bs'
          = field_access (field_desc s) (field_update (field_desc s)
              (take (size_td (s::'a typ_info)) (drop n bs)) undefined) bs'"
  "\<forall>f s m n bs bs' v. field_lookup_list ts f m = Some (s,m+n) \<longrightarrow>
      length bs = size_td_list ts \<longrightarrow> length bs' = size_td s \<longrightarrow> wf_fd_list ts \<longrightarrow>
      field_access (field_desc s) (field_update (field_desc_list ts) bs v) bs'
          = field_access (field_desc s) (field_update (field_desc s)
              (take (size_td (s::'a typ_info)) (drop n bs)) undefined) bs'"
  "\<forall>f s m n bs bs' v. field_lookup_pair x f m = Some (s,m+n) \<longrightarrow>
      length bs = size_td_pair x \<longrightarrow> length bs' = size_td s \<longrightarrow> wf_fd_pair x \<longrightarrow>
      field_access (field_desc s) (field_update (field_desc_pair x) bs v) bs'
          = field_access (field_desc s) (field_update (field_desc s)
              (take (size_td (s::'a typ_info)) (drop n bs)) undefined) bs'"
  apply(induct t and st and ts and x, all \<open>clarsimp\<close>)
   apply(fastforce dest!: wf_fd_cons_structD
                   simp: fd_cons_struct_def fd_cons_desc_def fd_cons_access_update_def)
  apply(clarsimp simp: fd_cons_desc_def split: option.splits)
   apply(case_tac f; clarsimp)
   apply(thin_tac "All P" for P)
   apply(drule_tac x="a#lista" in spec)
   apply(drule_tac x="s" in spec)
   apply(drule_tac x="m + size_td (dt_fst dt_pair)" in spec)
   apply(drule_tac x="n - size_td (dt_fst dt_pair)" in spec)
   apply clarsimp
   apply(frule field_lookup_offset_le)
   apply simp
   apply(case_tac dt_pair, clarsimp simp: fu_commutes_def)
  apply(case_tac f; clarsimp)
  apply(drule_tac x="a#lista" in spec)
  apply(drule_tac x="s" in spec)
  apply(drule_tac x="m" in spec)
  apply(drule_tac x="n" in spec)
  apply clarsimp
  apply(frule field_lookup_offset_le)
  apply simp
  apply(case_tac dt_pair, clarsimp)
  apply(clarsimp split: if_split_asm)
  by(fastforce dest: td_set_field_lookupD td_set_offset_size_m simp: ac_simps drop_take min_def)

lemma field_access_update_take_dropD:
  "\<lbrakk> field_lookup t f m = Some (s,m+n); length bs = size_td t;
      length bs' = size_td s; wf_fd t \<rbrakk> \<Longrightarrow>
      field_access (field_desc s) (field_update (field_desc t) bs v) bs'
          = field_access (field_desc s) (field_update (field_desc s)
              (take (size_td (s::'a typ_info)) (drop n bs)) undefined) bs'"
  by (rule field_access_update_take_drop)

lemma fi_fa_consistentD:
  "\<lbrakk> field_lookup (typ_info_t TYPE('a::wf_type)) f 0 = Some (d,n);
      length bs = size_of TYPE('a) \<rbrakk> \<Longrightarrow>
      field_access (field_desc d) (from_bytes bs) (replicate (size_td d) 0) =
      norm_tu (export_uinfo d) (take (size_td d) (drop n bs))"
  apply(clarsimp simp: field_offset_def from_bytes_def size_of_def)
  apply(frule field_lookup_export_uinfo_Some)
  apply(subst wf_fd_norm_tuD)
    apply(fastforce intro: wf_fd_field_lookupD)
   apply(clarsimp simp: min_def split: if_split_asm)
   apply(drule td_set_field_lookupD)
   apply(drule td_set_offset_size)
   apply simp
  apply(frule field_access_update_take_dropD[where v=undefined and m=0 and
                                                   bs'="replicate (size_td d) 0",simplified]; simp?)
  apply(simp add: min_def access_ti\<^sub>0_def)
  done

lemma length_super_update_bs [simp]:
  "n + length v \<le> length bs \<Longrightarrow> length (super_update_bs v bs n) = length bs"
  by (clarsimp simp: super_update_bs_def)

lemma drop_super_update_bs:
  "\<lbrakk> k \<le> n; n \<le> length bs \<rbrakk> \<Longrightarrow> drop k (super_update_bs v bs n) = super_update_bs v (drop k bs) (n - k)"
  by (simp add: super_update_bs_def take_drop)

lemma drop_super_update_bs2:
  "\<lbrakk> n \<le> length bs; n + length v \<le> k \<rbrakk> \<Longrightarrow>
      drop k (super_update_bs v bs n) = drop k bs"
  by (clarsimp simp: super_update_bs_def min_def split: if_split_asm)

lemma take_super_update_bs:
  "\<lbrakk> k \<le> n; n \<le> length bs \<rbrakk> \<Longrightarrow> take k (super_update_bs v bs n) = take k bs"
  by (clarsimp simp: super_update_bs_def min_def split: if_split_asm)

lemma take_super_update_bs2:
  "\<lbrakk> n \<le> length bs; n + length v \<le> k \<rbrakk> \<Longrightarrow>
      take k (super_update_bs v bs n) = super_update_bs v (take k bs) n"
  apply (clarsimp simp: super_update_bs_def min_def split: if_split_asm)
  apply (case_tac "n=k"; simp add: drop_take)
  done

lemma fi_fu_consistent [rule_format]:
  "\<forall>f m n s bs v w. field_lookup t f m = Some (s,n + m) \<longrightarrow> wf_fd t \<longrightarrow>
      length bs = size_td t \<longrightarrow> length v = size_td (s::'a typ_info) \<longrightarrow>
      field_update (field_desc t) (super_update_bs v bs n) w =
          field_update (field_desc s) v (field_update (field_desc t) bs w)"
  "\<forall>f m n s bs v w. field_lookup_struct st f m = Some (s,n + m) \<longrightarrow> wf_fd_struct st \<longrightarrow>
      length bs = size_td_struct  st \<longrightarrow> length v = size_td (s::'a typ_info) \<longrightarrow>
      field_update (field_desc_struct st) (super_update_bs v bs n) w =
          field_update (field_desc s) v (field_update (field_desc_struct  st) bs w)"
  "\<forall>f m n s bs v w. field_lookup_list ts f m = Some (s,n + m) \<longrightarrow> wf_fd_list ts \<longrightarrow>
      length bs = size_td_list ts \<longrightarrow> length v = size_td (s::'a typ_info) \<longrightarrow>
      field_update (field_desc_list ts) (super_update_bs v bs n) w =
          field_update (field_desc s) v (field_update (field_desc_list ts) bs w)"
  "\<forall>f m n s bs v w. field_lookup_pair x f m = Some (s,n + m) \<longrightarrow> wf_fd_pair x \<longrightarrow>
      length bs = size_td_pair x \<longrightarrow> length v = size_td (s::'a typ_info) \<longrightarrow>
      field_update (field_desc_pair x) (super_update_bs v bs n) w =
          field_update (field_desc s) v (field_update (field_desc_pair x) bs w)"
  apply(induct t and st and ts and x, all \<open>clarsimp\<close>)
   apply(drule wf_fd_cons_structD)
   apply(clarsimp simp: fd_cons_struct_def fd_cons_double_update_def super_update_bs_def
                        fd_cons_desc_def)
  apply(case_tac f; clarsimp)
  apply(clarsimp simp: fd_cons_desc_def split: option.splits)
   apply(clarsimp simp: fu_commutes_def)
   apply(rotate_tac -3)
   apply(drule_tac x="a#lista" in spec)
   apply(drule_tac x="m + size_td (dt_fst dt_pair)" in spec)
   apply(drule_tac x="n - size_td (dt_fst dt_pair)" in spec)
   apply(drule_tac x=s in spec)
   apply(frule field_lookup_offset_le)
   apply simp
   apply(drule td_set_list_field_lookup_listD)
   apply(drule td_set_list_offset_size_m)
   apply(clarsimp simp: split_DTPair_all drop_super_update_bs take_super_update_bs)
  apply(simp add: fu_commutes_def)
  apply(drule_tac x=w in spec)
  apply(frule_tac x="take (size_td_pair dt_pair) (super_update_bs v bs n)" in spec)
  apply(rotate_tac -1)
  apply(drule_tac x="drop (size_td_pair dt_pair) (super_update_bs v bs n)" in spec)
  apply(rotate_tac -1)
  apply(drule sym)
  apply simp
  apply(drule_tac x="a#lista" in spec)
  apply(drule_tac x="m" in spec)
  apply(drule_tac x="n" in spec)
  apply(drule_tac x="s" in spec)
  apply clarsimp
  apply(drule_tac x="take (size_td_pair dt_pair) bs" in spec, erule impE)
   apply(clarsimp simp: min_def split: if_split_asm)
  apply(rotate_tac -1)
  apply(drule_tac x=v in spec)
  apply clarsimp
  apply(drule_tac x="update_ti_list_t list (drop (size_td_pair dt_pair)
                                                 (super_update_bs v bs n)) w" in spec)
  apply(clarsimp simp: split_DTPair_all split: if_split_asm)
  apply(frule td_set_field_lookupD)
  apply(drule td_set_offset_size_m)
  apply(simp add: take_super_update_bs2 drop_super_update_bs2)
  done

lemma fi_fu_consistentD:
  "\<lbrakk> field_lookup t f 0 = Some (s,n); wf_fd t; length bs = size_td t;
      length v = size_td s \<rbrakk> \<Longrightarrow>
      field_update (field_desc t) (super_update_bs v bs n) w =
          field_update (field_desc s) v (field_update (field_desc t) bs w)"
  using fi_fu_consistent(1) [of t f 0] by clarsimp

lemma norm:
  "length bs = size_of TYPE('a) \<Longrightarrow>
      from_bytes (norm_bytes TYPE('a::wf_type) bs) = ((from_bytes bs)::'a)"
  apply(simp add: from_bytes_def norm_bytes_def)
  apply(subgoal_tac "wf_fd (typ_info_t TYPE('a))")
   apply(drule wf_fd_consD)
   apply(clarsimp simp: fd_cons_def fd_cons_desc_def)
   apply(drule (3) fd_cons_update_normalise)
   apply(fastforce simp: fd_cons_update_normalise_def size_of_def wf_fd_norm_tuD norm_desc_def
                         access_ti\<^sub>0_def)
  apply simp
  done

lemma len:
  "length bs = size_of TYPE('a) \<Longrightarrow>
      length (to_bytes (x::'a::wf_type) bs) = size_of TYPE('a)"
  apply(simp add: size_of_def to_bytes_def)
  apply(subgoal_tac "wf_fd (typ_info_t TYPE('a))")
   apply(drule wf_fd_consD)
   apply(clarsimp simp: fd_cons_def fd_cons_length_def fd_cons_desc_def)
  apply simp
  done

lemma sz_nzero:
  "0 < size_of (TYPE('a::wf_type))"
  unfolding size_of_def
  apply(subgoal_tac "wf_size_desc (typ_info_t TYPE('a))")
   apply(simp add: wf_size_desc_gt)
  apply simp
  done

lemma not_disj_fn_empty1 [simp]:
  "\<not> disj_fn [] s"
  by (simp add: disj_fn_def)

lemma fd_path_cons [simp]:
  "f \<notin> fs_path (x#xs) = (disj_fn f x \<and> f \<notin> fs_path xs)"
  by (auto simp: fs_path_def disj_fn_def)

lemma fu_commutes_lookup_disjD:
  "\<lbrakk> field_lookup t f m = Some (d,n); field_lookup t f' m' = Some (d',n');
      disj_fn f f'; wf_fdp (tf_set t) \<rbrakk> \<Longrightarrow>
      fu_commutes (field_update (field_desc (d::'a typ_info)))
          (field_update (field_desc d'))"
  by (auto simp: disj_fn_def wf_fdp_def dest!: tf_set_field_lookupD)

lemma field_lookup_fa_fu_lhs:
  "\<forall>f m n s d k. field_lookup t f m = Some (s,n) \<longrightarrow> fa_fu_ind (field_desc t) d k (size_td t)
      \<longrightarrow> wf_fd t \<longrightarrow> fa_fu_ind (field_desc (s::'a typ_info)) d k (size_td s)"
  "\<forall>f m n s d k. field_lookup_struct st f m = Some (s,n) \<longrightarrow> fa_fu_ind (field_desc_struct st) d k (size_td_struct st)
      \<longrightarrow> wf_fd_struct st \<longrightarrow> fa_fu_ind (field_desc (s::'a typ_info)) d k (size_td s)"
  "\<forall>f m n s d k. field_lookup_list ts f m = Some (s,n) \<longrightarrow> fa_fu_ind (field_desc_list ts) d k (size_td_list ts)
      \<longrightarrow> wf_fd_list ts \<longrightarrow> fa_fu_ind (field_desc (s::'a typ_info)) d k (size_td s)"
  "\<forall>f m n s d k. field_lookup_pair x f m = Some (s,n) \<longrightarrow> fa_fu_ind (field_desc_pair x) d k (size_td_pair x)
      \<longrightarrow> wf_fd_pair x \<longrightarrow> fa_fu_ind (field_desc (s::'a typ_info)) d k (size_td s)"
  apply(induct t and st and ts and x, all \<open>clarsimp simp: fa_fu_ind_def\<close>)
  apply(rename_tac dt_pair list f m n s d v bs bs')
  apply(clarsimp split: option.splits)
   apply(rotate_tac -3)
   apply(drule_tac x=f in spec)
   apply(drule_tac x="m + size_td (dt_fst dt_pair)" in spec)
   apply(drule_tac x=n in spec)
   apply(drule_tac x=s in spec)
   apply clarsimp
   apply(drule_tac x=d in spec)
   apply(drule_tac x="length bs" in spec)
   apply(erule impE)
    apply clarsimp
    apply(rename_tac v ys ys')
    apply(drule_tac x=v in spec)
    apply(drule_tac x=ys in spec)
    apply clarsimp
    apply(drule_tac x="replicate (size_td_pair dt_pair) 0 @ ys'" in spec)
    apply clarsimp
    apply(drule wf_fd_cons_pairD)
    apply(clarsimp simp: fd_cons_pair_def fd_cons_length_def fd_cons_desc_def)
   apply clarsimp
  apply(drule_tac x=f in spec)
  apply(drule_tac x=m in spec)
  apply(drule_tac x=n in spec)
  apply(drule_tac x=s in spec)
  apply clarsimp
  apply(drule_tac x=d in spec)
  apply(drule_tac x="length bs" in spec)
  apply(erule impE)
   apply clarsimp
   apply(rename_tac v ys ys')
   apply(drule_tac x=v in spec)
   apply(drule_tac x=ys in spec)
   apply clarsimp
   apply(drule_tac x="ys'@replicate (size_td_list list) 0" in spec)
   apply clarsimp
   apply(drule wf_fd_cons_pairD)
   apply(clarsimp simp: fd_cons_pair_def fd_cons_length_def fd_cons_desc_def)
  apply clarsimp
  done

lemma field_lookup_fa_fu_lhs_listD:
  "\<lbrakk> field_lookup_list ts f m = Some (s,n); fa_fu_ind (field_desc_list ts) d k (size_td_list ts);
      wf_fd_list ts \<rbrakk> \<Longrightarrow> fa_fu_ind (field_desc (s::'a typ_info)) d k (size_td s) "
  using field_lookup_fa_fu_lhs(3) [of ts] by clarsimp

lemma field_lookup_fa_fu_lhs_pairD:
  "\<lbrakk> field_lookup_pair x f m = Some (s,n); fa_fu_ind (field_desc_pair x) d k (size_td_pair x);
      wf_fd_pair x \<rbrakk> \<Longrightarrow> fa_fu_ind (field_desc (s::'a typ_info)) d k (size_td s)"
  using field_lookup_fa_fu_lhs(4) [of x] by clarsimp

lemma field_lookup_fa_fu_rhs:
  "\<forall>f m n s d k . field_lookup t f m = Some (s,n) \<longrightarrow> fa_fu_ind d (field_desc t) (size_td t) k
      \<longrightarrow> wf_fd t \<longrightarrow> fa_fu_ind d (field_desc (s::'a typ_info)) (size_td s) k"
  "\<forall>f m n s d k. field_lookup_struct st f m = Some (s,n) \<longrightarrow> fa_fu_ind d (field_desc_struct st) (size_td_struct st) k
      \<longrightarrow> wf_fd_struct st \<longrightarrow> fa_fu_ind d (field_desc (s::'a typ_info)) (size_td s) k"
  "\<forall>f m n s d k. field_lookup_list ts f m = Some (s,n) \<longrightarrow> fa_fu_ind d (field_desc_list ts) (size_td_list ts) k
      \<longrightarrow> wf_fd_list ts \<longrightarrow> fa_fu_ind d (field_desc (s::'a typ_info)) (size_td s) k"
  "\<forall>f m n s d k. field_lookup_pair x f m = Some (s,n) \<longrightarrow> fa_fu_ind d (field_desc_pair x) (size_td_pair x) k
      \<longrightarrow> wf_fd_pair x \<longrightarrow> fa_fu_ind d (field_desc (s::'a typ_info)) (size_td s) k"
  apply(induct t and st and ts and x, all \<open>clarsimp simp: fa_fu_ind_def\<close>)
  apply(rename_tac dt_pair list f m n s d v bs bs')
  apply(clarsimp split: option.splits)
   apply(rotate_tac -3)
   apply(drule_tac x=f in spec)
   apply(drule_tac x="m + size_td (dt_fst dt_pair)" in spec)
   apply(drule_tac x=n in spec)
   apply(drule_tac x=s in spec)
   apply clarsimp
   apply(drule_tac x=d in spec)
   apply(drule_tac x="length bs'" in spec)
   apply(erule impE)
    apply clarsimp
    apply(rename_tac v ys ys')
    apply(drule_tac x=v in spec)
    apply(drule_tac x="access_ti_pair dt_pair v (replicate (size_td_pair dt_pair) 0)@ys" in spec)
    apply clarsimp
    apply(erule impE)
     apply(drule wf_fd_cons_pairD)
     apply(clarsimp simp: fd_cons_pair_def fd_cons_length_def fd_cons_desc_def)
    apply(drule_tac x="ys'" in spec)
    apply clarsimp
    apply(drule wf_fd_cons_pairD)
    apply(clarsimp simp: fd_cons_pair_def fd_cons_length_def fd_cons_update_access_def fd_cons_desc_def)
    apply(clarsimp simp: fu_commutes_def)
   apply clarsimp
  apply(drule_tac x=f in spec)
  apply(drule_tac x=m in spec)
  apply(drule_tac x=n in spec)
  apply(drule_tac x=s in spec)
  apply clarsimp
  apply(drule_tac x=d in spec)
  apply(drule_tac x="length bs'" in spec)
  apply(erule impE)
   apply clarsimp
   apply(rename_tac v ys ys')
   apply(drule_tac x=v in spec)
   apply(drule_tac x="ys@access_ti_list list v (replicate (size_td_list list) 0)" in spec)
   apply(drule wf_fd_cons_pairD)
   apply(drule wf_fd_cons_listD)
   apply(clarsimp simp: fd_cons_pair_def fd_cons_list_def fd_cons_length_def
                        fd_cons_update_access_def fd_cons_desc_def)
  apply fastforce
  done

lemma field_lookup_fa_fu_rhs_listD:
  "\<lbrakk> field_lookup_list ts f m = Some (s,n);
      fa_fu_ind d (field_desc_list ts) (size_td_list ts) k; wf_fd_list ts \<rbrakk> \<Longrightarrow>
      fa_fu_ind d (field_desc (s::'a typ_info)) (size_td s) k"
  using field_lookup_fa_fu_rhs(3) [of ts] by simp

lemma field_lookup_fa_fu_rhs_pairD:
  "\<lbrakk> field_lookup_pair x f m = Some (s,n);
      fa_fu_ind d (field_desc_pair x) (size_td_pair x) k; wf_fd_pair x \<rbrakk> \<Longrightarrow>
      fa_fu_ind d (field_desc (s::'a typ_info)) (size_td s) k"
  using field_lookup_fa_fu_rhs(4) [of x] by simp

lemma fa_fu_lookup_ind_list_pair:
  "\<lbrakk> field_lookup_pair x f m = Some (d',n); wf_fd_pair x;
      field_lookup_list ts f' m' = Some (d,n'); wf_fd_list ts;
      fa_fu_ind (field_desc_list ts) (field_desc_pair x) (size_td_pair x) (size_td_list ts) \<rbrakk>
      \<Longrightarrow> fa_fu_ind (field_desc d) (field_desc d') (size_td d') (size_td d)"
  apply(drule (2) field_lookup_fa_fu_lhs_listD)
  apply(drule (3) field_lookup_fa_fu_rhs_pairD)
  done

lemma fa_fu_lookup_ind_pair_list:
  "\<lbrakk> field_lookup_pair x f m = Some (d,n); wf_fd_pair x;
      field_lookup_list ts f' m' = Some (d',n'); wf_fd_list ts;
      fa_fu_ind (field_desc_pair x) (field_desc_list ts) (size_td_list ts) (size_td_pair x) \<rbrakk>
      \<Longrightarrow> fa_fu_ind (field_desc d) (field_desc d') (size_td d') (size_td d)"
  apply(drule (2) field_lookup_fa_fu_lhs_pairD)
  apply(drule (3) field_lookup_fa_fu_rhs_listD)
  done

lemma fa_fu_lookup_disj:
  "\<forall>f m d n f' m' d' n'. field_lookup t f m = Some (d,n) \<longrightarrow>
      field_lookup t f' m' = Some (d',n') \<longrightarrow> disj_fn f f' \<longrightarrow>
      wf_fd t \<longrightarrow> fa_fu_ind (field_desc (d::'a typ_info)) (field_desc d') (size_td d') (size_td d)"
  "\<forall>f m d n f' m' d' n'. field_lookup_struct st f m = Some (d,n) \<longrightarrow>
      field_lookup_struct st f' m' = Some (d',n') \<longrightarrow> disj_fn f f' \<longrightarrow>
      wf_fd_struct st \<longrightarrow> fa_fu_ind (field_desc (d::'a typ_info)) (field_desc d') (size_td d') (size_td d)"
  "\<forall>f m d n f' m' d' n'. field_lookup_list ts f m = Some (d,n) \<longrightarrow>
      field_lookup_list ts f' m' = Some (d',n') \<longrightarrow> disj_fn f f' \<longrightarrow>
      wf_fd_list ts \<longrightarrow> fa_fu_ind (field_desc (d::'a typ_info)) (field_desc d') (size_td d') (size_td d)"
  "\<forall>f m d n f' m' d' n'. field_lookup_pair x f m = Some (d,n) \<longrightarrow>
      field_lookup_pair x f' m' = Some (d',n') \<longrightarrow> disj_fn f f' \<longrightarrow>
      wf_fd_pair x \<longrightarrow> fa_fu_ind (field_desc (d::'a typ_info)) (field_desc d') (size_td d') (size_td d)"
  apply(induct t and st and ts and x, all \<open>clarsimp simp: disj_fn_def\<close>)
   apply(rename_tac dt_pair list f m d n f' m' d' n')
   apply(clarsimp simp: split: option.splits)
      apply(thin_tac "All P" for P)
      apply(drule_tac x=f in spec)
      apply(drule_tac x="m + size_td (dt_fst dt_pair)" in spec)
      apply(drule_tac x=d in spec)
      apply clarsimp
      apply(drule_tac x=f' in spec)
      apply(drule_tac x="m' + size_td (dt_fst dt_pair)" in spec)
      apply(drule_tac x=d' in spec)
      apply clarsimp
     apply(drule (3) fa_fu_lookup_ind_list_pair; simp)
    apply(drule (3) fa_fu_lookup_ind_pair_list; simp)
   apply(drule_tac x=f in spec)
   apply(drule_tac x=m in spec)
   apply(drule_tac x=d in spec)
   apply clarsimp
   apply(thin_tac "All P" for P)
   apply(drule_tac x=f' in spec)
   apply(drule_tac x=m' in spec)
   apply(drule_tac x=d' in spec)
   apply clarsimp
  apply(rename_tac typ_desc f m d n f' m' d' n')
  apply(drule_tac x="tl f" in spec)
  apply(drule_tac x=m in spec)
  apply(drule_tac x=d in spec)
  apply clarsimp
  apply(drule_tac x="tl f'" in spec)
  apply(drule_tac x=m' in spec)
  apply(drule_tac x=d' in spec)
  apply clarsimp
  apply(case_tac f; clarsimp)
  apply(case_tac f'; clarsimp)
  done

lemma fa_fu_lookup_disjD:
  "\<lbrakk> field_lookup t f m = Some (d,n); field_lookup t f' m' = Some (d',n');
      disj_fn f f'; wf_fd t \<rbrakk> \<Longrightarrow>
      fa_fu_ind (field_desc (d::'a typ_info)) (field_desc d') (size_td d') (size_td d)"
 using fa_fu_lookup_disj(1) [of t] by fastforce

lemma field_access_update_disj:
  "\<lbrakk> field_lookup t f m = Some (d,n); field_lookup t f' m' = Some (d',n');
      disj_fn f f'; length bs = size_td d'; length bs' = size_td d; wf_fd t \<rbrakk> \<Longrightarrow>
      access_ti d (update_ti_t d' bs v) bs' = access_ti d v bs'"
  by (fastforce dest: fa_fu_lookup_disjD simp: fa_fu_ind_def)

lemma td_set_list_intvl_sub:
  "(d,n) \<in> td_set_list t m \<Longrightarrow> {of_nat n..+size_td d} \<subseteq> {of_nat m..+size_td_list t}"
  apply(frule td_set_list_offset_le)
  apply(drule td_set_list_offset_size_m)
  apply clarsimp
  apply(drule intvlD, clarsimp)
  apply(clarsimp simp: intvl_def)
  apply(rule_tac x="k + n - m" in exI)
  apply simp
  done

lemma td_set_pair_intvl_sub:
  "(d,n) \<in> td_set_pair t m \<Longrightarrow> {of_nat n..+size_td d} \<subseteq> {of_nat m..+size_td_pair t}"
  apply(frule td_set_pair_offset_le)
  apply(drule td_set_pair_offset_size_m)
  apply clarsimp
  apply(drule intvlD, clarsimp)
  apply(clarsimp simp: intvl_def)
  apply(rule_tac x="k + n - m" in exI)
  apply simp
  done

lemma intvl_inter_le:
  assumes inter: "a + of_nat k = c + of_nat ka" and lt_d: "ka < d" and lt_ka: "k \<le> ka"
  shows "a \<in> {c..+d}"
proof -
  from lt_ka inter have "a = c + of_nat (ka - k)" by (simp add: field_simps)
  moreover from lt_d have "ka - k < d" by simp
  ultimately show ?thesis by (force simp: intvl_def)
qed

lemma intvl_inter:
  assumes nondisj: "{a..+b} \<inter> {c..+d} \<noteq> {}"
  shows "a \<in> {c..+d} \<or> c \<in> {a..+b}"
proof -
  from nondisj obtain k ka where "a + of_nat k = c + of_nat ka"
    and "k < b" and "ka < d" by (force simp: intvl_def)
  thus ?thesis by (force intro: intvl_inter_le)
qed

lemma init_intvl_disj:
  "k + z < addr_card \<Longrightarrow> {(p::addr)+of_nat k..+z} \<inter> {p..+k} = {}"
  apply(case_tac "k \<noteq> 0"; simp)
  apply(rule ccontr)
  apply(drule intvl_inter)
  apply(erule disjE)
   apply(drule intvlD, clarsimp)
   apply(metis add_lessD1 len_of_addr_card less_trans mod_less order_less_irrefl unat_of_nat)
  apply(drule intvlD, clarsimp)
  apply(subst (asm) Abs_fnat_homs)
  apply(subst (asm) Word.of_nat_0)
  apply(subst (asm) len_of_addr_card)
  apply clarsimp
  apply(case_tac q; simp)
  done

lemma final_intvl_disj:
  "\<lbrakk> k + z \<le> n; n < addr_card \<rbrakk> \<Longrightarrow>
      {(p::addr)+of_nat k..+z} \<inter> {p+(of_nat k + of_nat z)..+n - (k+z)} = {}"
  apply(case_tac "z \<noteq> 0"; simp)
  apply(rule ccontr)
  apply(drule intvl_inter)
  apply(erule disjE)
   apply(drule intvlD, clarsimp)
   apply(subst (asm) Abs_fnat_homs)
   apply(subst (asm) Word.of_nat_0)
   apply(subst (asm) len_of_addr_card)
   apply clarsimp
   apply(case_tac q; simp)
  apply(drule intvlD, clarsimp)
  apply(subst (asm) word_unat.norm_eq_iff [symmetric])
  apply(subst (asm) len_of_addr_card)
  apply simp
  done

lemma fa_fu_lookup_disj_inter:
  "\<forall>f m d n f' d' n'. field_lookup t f m = Some (d,n) \<longrightarrow>
      field_lookup t f' m = Some (d',n') \<longrightarrow> disj_fn f f' \<longrightarrow>
      wf_fd t \<longrightarrow> size_td t < addr_card \<longrightarrow>
      {(of_nat n)::addr..+size_td (d::'a typ_info)} \<inter> {of_nat n'..+size_td d'} = {}"
  "\<forall>f m d n f' m d' n'. field_lookup_struct st f m = Some (d,n) \<longrightarrow>
      field_lookup_struct st f' m = Some (d',n') \<longrightarrow> disj_fn f f' \<longrightarrow>
      wf_fd_struct st \<longrightarrow> size_td_struct st < addr_card \<longrightarrow>
      {(of_nat n)::addr..+size_td (d::'a typ_info)} \<inter> {of_nat n'..+size_td d'} = {}"
  "\<forall>f m d n f' m d' n'. field_lookup_list ts f m = Some (d,n) \<longrightarrow>
      field_lookup_list ts f' m = Some (d',n') \<longrightarrow> disj_fn f f' \<longrightarrow>
      wf_fd_list ts \<longrightarrow> size_td_list ts < addr_card \<longrightarrow>
      {(of_nat n)::addr..+size_td (d::'a typ_info)} \<inter> {of_nat n'..+size_td d'} = {}"
  "\<forall>f m d n f' m d' n'. field_lookup_pair x f m = Some (d,n) \<longrightarrow>
      field_lookup_pair x f' m = Some (d',n') \<longrightarrow> disj_fn f f' \<longrightarrow>
      wf_fd_pair x \<longrightarrow> size_td_pair x < addr_card \<longrightarrow>
      {(of_nat n)::addr..+size_td (d::'a typ_info)} \<inter> {of_nat n'..+size_td d'} = {}"
  apply(induct t and st and ts and x, all \<open>clarsimp simp: disj_fn_def\<close>)
   apply(rule set_eqI)
   apply(clarsimp split: option.splits)
      apply fastforce
     apply(drule td_set_list_field_lookup_listD)
     apply(drule td_set_list_intvl_sub)
     apply(drule td_set_pair_field_lookup_pairD)
     apply(drule td_set_pair_intvl_sub)
     apply(fastforce dest: init_intvl_disj simp: split_DTPair_all)
    apply(drule td_set_list_field_lookup_listD)
    apply(drule td_set_list_intvl_sub)
    apply(drule td_set_pair_field_lookup_pairD)
    apply(drule td_set_pair_intvl_sub)
    apply(fastforce dest: init_intvl_disj simp: split_DTPair_all)
   apply fastforce
  apply(rule set_eqI, clarsimp)
  apply(case_tac f; clarsimp)
  apply(case_tac f'; clarsimp)
  apply(fastforce simp: disj_fn_def)
  done

lemma fa_fu_lookup_disj_interD:
  "\<lbrakk> field_lookup t f m = Some (d,n); field_lookup t f' m = Some (d',n');
      disj_fn f f'; wf_fd t; size_td t < addr_card \<rbrakk> \<Longrightarrow>
      {(of_nat n)::addr..+size_td (d::'a typ_info)} \<inter> {of_nat n'..+size_td d'} = {}"
  using fa_fu_lookup_disj_inter(1) [of t] by clarsimp

lemma fa_fu_lookup_disj_inter_listD:
  "\<lbrakk> field_lookup_list ts f m = Some (d,n);
      field_lookup_list ts f' m = Some (d',n'); disj_fn f f';
      wf_fd_list ts; size_td_list ts < addr_card \<rbrakk> \<Longrightarrow>
      {(of_nat n)::addr..+size_td (d::'a typ_info)} \<inter>
          {of_nat n'..+size_td d'} = {}"
  using fa_fu_lookup_disj_inter(3) [of ts] by clarsimp

lemma upd_rf:
  "length bs = size_of TYPE('a) \<Longrightarrow>
      update_ti_t (typ_info_t TYPE('a::mem_type_sans_size)) bs v
          = update_ti_t (typ_info_t TYPE('a)) bs w"
  by (simp add: upd)

lemma inv:
  "length bs = size_of TYPE('a) \<Longrightarrow>
      from_bytes (to_bytes (x::'a::mem_type_sans_size) bs) = x"
  unfolding from_bytes_def to_bytes_def
  apply(subgoal_tac "wf_fd (typ_info_t TYPE('a))")
   apply(drule wf_fd_consD)
   apply(clarsimp simp: fd_cons_def fd_cons_update_access_def fd_cons_desc_def)
   apply(drule_tac x=x in spec)
   apply(insert upd [where v=x and w=undefined and bs="access_ti (typ_info_t TYPE('a)) x bs"])
   apply(clarsimp simp: update_ti_t_def  fd_cons_length_def size_of_def split: if_split_asm )
  apply simp
  done

lemma align:
  "align_of (TYPE('a::mem_type)) dvd addr_card"
  apply(clarsimp simp: dvd_def align_of_def)
  apply(subgoal_tac "align_of TYPE('a) < addr_card")
   apply(subst (asm) align_of_def)
   apply(rule_tac x="2^(len_of TYPE(addr_bitsize) - align_td (typ_info_t TYPE('a)))" in exI)
   apply clarsimp
   apply(subgoal_tac "align_td (typ_info_t TYPE('a)) < addr_bitsize")
    apply(simp add: addr_card flip: power_add)
   apply(rule_tac a="2" in power_less_imp_less_exp; simp add: addr_card)
  apply (metis align_size_of dvd_imp_le less_trans max_size nat_less_le sz_nzero)
  done

lemma to_bytes_inj:
  "to_bytes (v::'a::mem_type) = to_bytes (v'::'a) \<Longrightarrow> v=v'"
  apply (drule_tac x="replicate (size_of TYPE('a)) 0" in fun_cong)
  apply (drule_tac f="from_bytes::byte list \<Rightarrow> 'a" in arg_cong)
  apply (simp add: inv)
  done

lemmas unat_simps = unat_simps' max_size

lemmas mem_type_simps [simp] = inv len sz_nzero max_size align

lemma ptr_aligned_plus:
  assumes aligned: "ptr_aligned (p::'a::mem_type ptr) "
  shows "ptr_aligned (p +\<^sub>p i)"
proof -
  have "int (align_of TYPE('a)) dvd (i * int (size_of TYPE('a)))"
    by (simp add: align_size_of)
  with aligned show ?thesis
    apply (case_tac p, simp add: ptr_aligned_def ptr_add_def scast_id)
    apply (simp only: unat_simps len_signed)
    apply (metis align align_size_of dvd_add dvd_mod dvd_mult2 mult.commute)
    done
qed


lemma mem_type_self [simp]:
  "ptr_val (p::'a::mem_type ptr) \<in> {ptr_val p..+size_of TYPE('a)}"
  by (rule intvl_self, rule sz_nzero)

lemma intvl_Suc_nmem [simp]:
  "(p::addr) \<notin> {p + 1..+size_of TYPE('a::mem_type) - Suc 0}"
  by (rule intvl_Suc_nmem', subst len_of_addr_card, rule max_size)

lemma wf_size_desc_typ_uinfo_t_simp [simp]:
  "wf_size_desc (typ_uinfo_t TYPE('a::mem_type))"
  by (simp add: typ_uinfo_t_def export_uinfo_def wf_size_desc_map)


lemma aggregate_map [simp]:
  "aggregate (map_td f t) = aggregate t"
  apply(case_tac t)
  apply(rename_tac st n)
  apply(case_tac st; simp)
  done


lemma simple_tag_not_aggregate2 [simp]:
  "typ_uinfo_t TYPE('a::simple_mem_type) \<noteq> TypDesc (TypAggregate ts) tn"
  by (metis aggregate.simps aggregate_map aggregate_struct.simps(2) export_uinfo_def simple_tag
            typ_uinfo_t_def)

lemma simple_tag_not_aggregate3 [simp]:
  "typ_info_t TYPE('a::simple_mem_type) \<noteq> TypDesc (TypAggregate ts) tn"
  by (metis aggregate.simps aggregate_struct.simps(2) simple_tag)

lemma field_of_t_mem:
  "field_of_t (p::'b::mem_type ptr) (q::'a::mem_type ptr) \<Longrightarrow>
   ptr_val p \<in> {ptr_val q..+size_of TYPE('a)}"
  apply(clarsimp simp: field_of_t_def field_of_def intvl_def)
  apply(rule_tac x="unat (ptr_val p - ptr_val q)" in exI)
  apply simp
  apply(drule td_set_offset_size)
  apply(clarsimp simp: size_of_def)
  by (metis add.commute add.right_neutral add_mono_thms_linordered_field(4) mem_type_simps(3)
            not_less size_of_def)

lemma map_td_map:
  "map_td f (map_td g t) = map_td (\<lambda>n algn. f n algn o g n algn) t"
  "map_td_struct f (map_td_struct g st) = map_td_struct (\<lambda>n algn. f n algn o g n algn) st"
  "map_td_list f (map_td_list g ts) = map_td_list (\<lambda>n algn. f n algn o g n algn) ts"
  "map_td_pair f (map_td_pair g x) = map_td_pair (\<lambda>n algn. f n algn o g n algn) x"
  by (induct t and st and ts and x) auto

lemma field_of_t_simple:
  "field_of_t p (x::'a::simple_mem_type ptr) \<Longrightarrow> ptr_val p = ptr_val x"
  apply(clarsimp simp: field_of_t_def)
  apply(cases "typ_uinfo_t TYPE('a)")
  apply(rename_tac st n)
  apply(case_tac st; clarsimp)
  apply(clarsimp simp: field_of_def unat_eq_zero)
  done


lemma fold_td'_unfold:
 "fold_td' t =
    (let (f,s) = t in
     case s of TypDesc st nm \<Rightarrow>
       (case st of
          TypScalar n algn d \<Rightarrow> d
        | TypAggregate ts \<Rightarrow> f nm (map (\<lambda>x. case x of DTPair t n \<Rightarrow> (fold_td' (f,t),n)) ts)))"
  by (cases t, simp) (case_tac b, simp)



lemma fold_td_alt_def':
  "fold_td f t = (case t of
                    TypDesc st nm \<Rightarrow>
                      (case st of
                         TypScalar n algn d \<Rightarrow> d
                       | TypAggregate ts \<Rightarrow> f nm (map (\<lambda>x. (fold_td f (dt_fst x),dt_snd x)) ts)))"
  apply(case_tac t)
  apply(clarsimp split: typ_desc.split typ_struct.splits dt_pair.splits)
  by (metis (no_types, lifting) dt_pair.case dt_pair_collapse)

lemma fold_td_alt_def:
  "fold_td f t \<equiv> (case t of
                    TypDesc st nm \<Rightarrow>
                      (case st of
                         TypScalar n algn d \<Rightarrow> d
                       | TypAggregate ts \<Rightarrow> f nm (map (\<lambda>x. (fold_td f (dt_fst x),dt_snd x)) ts)))"
  by (fastforce simp: fold_td_alt_def' simp del: fold_td_def)


lemma map_td'_map':
  "map_td f t = (map_td' (f,t))"
  "TypDesc (map_td_struct f st) (typ_name t) = (map_td' (f,TypDesc st (typ_name t)))"
  "TypDesc (TypAggregate (map_td_list f ts)) (typ_name t) = map_td' (f,TypDesc (TypAggregate ts) (typ_name t))"
  "map_td_pair f x = DTPair (map_td' (f,dt_fst x)) (dt_snd x)"
  by (induct t and st and ts and x) (auto simp: split_DTPair_all)

lemma map_td'_map:
  "map_td f t = (case t of TypDesc st nm \<Rightarrow> TypDesc (case st of
           TypScalar n algn d \<Rightarrow> TypScalar n algn (f n algn d) |
           TypAggregate ts \<Rightarrow> TypAggregate (map (\<lambda>x. DTPair (map_td f (dt_fst x)) (dt_snd x)) ts)) nm)"
  apply(subst map_td'_map')
  apply(subst map_td'_map')
  apply(case_tac t, simp add: typ_struct.splits)
  apply(auto simp: split_DTPair_all)
  done

lemma map_td_alt_def:
  "map_td f t \<equiv> (case t of TypDesc st nm \<Rightarrow> TypDesc (case st of
           TypScalar n algn d \<Rightarrow> TypScalar n algn (f n algn d) |
           TypAggregate ts \<Rightarrow> TypAggregate (map (\<lambda>x. DTPair (map_td f (dt_fst x)) (dt_snd x)) ts)) nm)"
  by (simp add: map_td'_map)

lemma size_td_fm':
  "size_td (t::'a typ_desc) = fold_td tnSum (map_td (\<lambda>n x d. n) t)"
  "size_td_struct (st::'a typ_struct) = fold_td_struct (typ_name t) tnSum (map_td_struct (\<lambda>n x d. n) st)"
  "size_td_list (ts::'a typ_pair list) = fold_td_list (typ_name t) tnSum (map_td_list (\<lambda>n x d. n) ts)"
  "size_td_pair (x::'a typ_pair) = fold_td_pair tnSum (map_td_pair (\<lambda>n x d. n) x)"
  by (induct t and st and ts and x) (auto simp: tnSum_def split: dt_pair.splits)

lemma size_td_fm:
  "size_td (t::'a typ_desc) \<equiv> fold_td tnSum (map_td (\<lambda>n algn d. n) t)"
  using size_td_fm'(1) [of t] by clarsimp

lemma align_td_fm':
  "align_td (t::'a typ_desc) = fold_td tnMax (map_td (\<lambda>n x d. x) t)"
  "align_td_struct (st::'a typ_struct) = fold_td_struct (typ_name t) tnMax (map_td_struct (\<lambda>n x d. x) st)"
  "align_td_list (ts::'a typ_pair list) = fold_td_list (typ_name t) tnMax (map_td_list (\<lambda>n x d. x) ts)"
  "align_td_pair (x::'a typ_pair) = fold_td_pair tnMax (map_td_pair (\<lambda>n x d. x) x)"
  by (induct t and st and ts and x) (auto simp: tnMax_def split: dt_pair.splits)

lemma align_td_fm:
  "align_td (t::'a typ_desc) \<equiv> fold_td tnMax (map_td (\<lambda>n algn d. algn) t)"
  using align_td_fm'(1) [of t] by clarsimp

lemma case_dt_pair:
  "snd ` case_dt_pair (\<lambda>t. Pair (f t)) ` X = dt_snd ` X"
  by (force simp: image_iff split_DTPair_all split: dt_pair.splits)

lemma map_DTPair_dt_snd:
  "map_td_pair f x = DTPair a b \<Longrightarrow> b = dt_snd x"
  by (metis dt_pair.inject map_td'_map'(4))

lemma wf_desc_fm':
  "wf_desc (t::'a typ_desc) = fold_td wfd (map_td (\<lambda>n x d. True) t)"
  "wf_desc_struct (st::'a typ_struct) = fold_td_struct (typ_name t) wfd (map_td_struct (\<lambda>n x d. True) st)"
  "wf_desc_list (ts::'a typ_pair list) = fold_td_list (typ_name t) wfd (map_td_list (\<lambda>n x d. True) ts)"
  "wf_desc_pair (x::'a typ_pair) = fold_td_pair wfd (map_td_pair (\<lambda>n x d. True) x)"
  supply split_DTPair_all[simp] dt_pair.splits[split]
  apply (induct t and st and ts and x, all \<open>clarsimp simp: wfd_def image_comp[symmetric]\<close>)
  apply (rule iffI; clarsimp)
   apply (metis (no_types) dt_snd.simps dt_snd_map_td_list imageI)
  by (metis (mono_tags) case_dt_pair dt_snd.simps dt_snd_map_td_list image_eqI)

lemma wf_desc_fm:
  "wf_desc (t::'a typ_desc) \<equiv> fold_td wfd (map_td (\<lambda>n algn d. True) t)"
  using wf_desc_fm'(1) [of t] by auto

lemma update_tag_list_empty [simp]:
  "(map_td_list f xs = []) = (xs = [])"
  by (case_tac xs, auto)

lemma wf_size_desc_fm':
  "wf_size_desc (t::'a typ_desc) = fold_td wfsd (map_td (\<lambda>n x d. 0 < n) t)"
  "wf_size_desc_struct (st::'a typ_struct) = fold_td_struct (typ_name t) wfsd (map_td_struct (\<lambda>n x d. 0 < n) st)"
  "ts \<noteq> [] \<longrightarrow> wf_size_desc_list (ts::'a typ_pair list) = fold_td_list (typ_name t) wfsd (map_td_list (\<lambda>n x d. 0 < n) ts)"
  "wf_size_desc_pair (x::'a typ_pair) = fold_td_pair wfsd (map_td_pair (\<lambda>n x d. 0 < n) x)"
  by (induct t and st and ts and x) (auto simp: wfsd_def split: dt_pair.splits)

lemma wf_size_desc_fm:
  "wf_size_desc (t::'a typ_desc) \<equiv> fold_td wfsd (map_td (\<lambda>n algn d. 0 < n) t)"
  using wf_size_desc_fm'(1) [of t] by auto

end
