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

(* Isolated experiment with closed representations of mutual recursive
   functions

   Currently unused
*)

theory Closed
imports CTypes
begin

definition
  fat :: "typ_name \<Rightarrow> ((nat \<times> ('a \<Rightarrow> byte list \<Rightarrow> byte list)) \<times> field_name) list \<Rightarrow> nat \<times> ('a \<Rightarrow> byte list \<Rightarrow> byte list)"
where
  "fat \<equiv> \<lambda>tn ts. foldr (\<lambda>((m,f),k) (n,g). (m+n,\<lambda>v bs. f v (take m bs) @ g v (drop m bs))) ts ((0,\<lambda>b bs.[]))"

definition
  fut :: "typ_name \<Rightarrow> ((nat \<times> (byte list \<Rightarrow> 'a \<Rightarrow> 'a)) \<times> field_name) list \<Rightarrow>
          nat \<times> (byte list \<Rightarrow> 'a \<Rightarrow> 'a)"
where
  "fut \<equiv> \<lambda>tn ts. foldr (\<lambda>((m,f),k) (n,g). (m+n, \<lambda>bs v. f (take m bs) (g (drop m bs) v))) ts (0, \<lambda>bs. id)"

definition
  tyn :: "typ_name \<Rightarrow> ((nat \<times> (byte list \<Rightarrow> byte list)) \<times> field_name) list \<Rightarrow>
          nat \<times> (byte list \<Rightarrow> byte list)"
where
  "tyn \<equiv> \<lambda>tn ts. foldr (\<lambda>((m,f),k) (n,g). (m+n, \<lambda>bs. f (take m bs) @ g (drop m bs))) ts (0, \<lambda>bs. [])"

lemma size_td_fst_field_access:
  "size_td (t::'a typ_info) = fst (fold_td fat
      (map_td (\<lambda>n x d. (n, field_access d)) t))"
  "size_td_struct (st::'a typ_info_struct) = fst (fold_td_struct (typ_name t) fat (map_td_struct (\<lambda>n x d. (n, field_access d)) st))"
  "size_td_list (ts::'a typ_info_pair list) = fst (fold_td_list (typ_name t) fat  (map_td_list (\<lambda>n x d. (n, field_access d)) ts))"
  "size_td_pair (x::'a typ_info_pair) = fst (fold_td_pair fat  (map_td_pair (\<lambda>n x d. (n, field_access d)) x))"
apply(induct t and st and ts and x)
     apply(auto simp: fat_def split_def split: dt_pair.splits)
done

lemma fat_cons:
  "fat tn (t#ts) = (let ((m,f),k) = t; (n,g) = fat tn ts in
      (m+n, \<lambda>v bs. f v (take m bs) @ (g v (drop m bs))))"
apply(simp add: Let_def fat_def)
apply(case_tac t, simp)
apply(case_tac a, simp+)
done


lemma access_ti_fm':
  "access_ti (t::'a typ_info) = snd (fold_td fat (map_td (\<lambda>n x d. (n,field_access d)) t))"
  "access_ti_struct (st::'a typ_info_struct) = snd (fold_td_struct (typ_name t) fat (map_td_struct (\<lambda>n x d. (n,field_access d)) st))"
  "access_ti_list (ts::'a typ_info_pair list) = snd (fold_td_list (typ_name t) fat (map_td_list (\<lambda>n x d. (n, field_access d) ) ts))"
  "access_ti_pair (x::'a typ_info_pair) = snd (fold_td_pair fat (map_td_pair (\<lambda>n x d. (n, field_access d)) x))"
apply(induct t and st and ts and x)
     apply(auto simp: fat_def split: dt_pair.splits)
apply(rule ext)+
apply(simp add: size_td_fst_field_access)
apply(simp add: fat_def)
apply(simp add: Let_def split_def)
done

lemma access_ti_fm:
  "access_ti (t::'a typ_info) \<equiv> snd (fold_td fat (map_td (\<lambda>n algn d. (n,field_access d)) t))"
apply(insert access_ti_fm'(1) [of t])
apply auto
done

lemma fut_cons:
  "fut tn (t#ts) = (let ((m,f),k) = t; (n,g) = fut tn ts in
      (m+n, \<lambda>bs v. f (take m bs) (g (drop m bs) v)))"
apply(simp add: Let_def fut_def)
apply(case_tac t, simp)
apply(case_tac a, simp+)
done

lemma size_td_fst_field_update:
  "size_td (t::'a typ_info) = fst (fold_td fut
      (map_td (\<lambda>n x d. (n, field_update d)) t))"
  "size_td_struct (st::'a typ_info_struct) = fst (fold_td_struct (typ_name t) fut (map_td_struct (\<lambda>n x d. (n, field_update d)) st))"
  "size_td_list (ts::'a typ_info_pair list) = fst (fold_td_list (typ_name t) fut  (map_td_list (\<lambda>n x d. (n, field_update d)) ts))"
  "size_td_pair (x::'a typ_info_pair) = fst (fold_td_pair fut  (map_td_pair (\<lambda>n x d. (n, field_update d)) x))"
apply(induct t and st and ts and x)
     apply(auto simp: fut_def split_def split: dt_pair.splits)
done

lemma update_ti_fm':
  "update_ti (t::'a typ_info) = snd (fold_td fut
      (map_td (\<lambda>n x d. (n, field_update d)) t))"
  "update_ti_struct (st::'a typ_info_struct) = snd (fold_td_struct (typ_name t) fut  (map_td_struct (\<lambda>n x d. (n, field_update d)) st))"
  "update_ti_list (ts::'a typ_info_pair list) = snd (fold_td_list (typ_name t) fut  (map_td_list (\<lambda>n x d. (n, field_update d)) ts))"
  "update_ti_pair (x::'a typ_info_pair) = snd (fold_td_pair fut  (map_td_pair (\<lambda>n x d. (n, field_update d)) x))"
apply(induct t and st and ts and x)
     apply(auto simp: split: dt_pair.splits)
  apply(clarsimp split: typ_struct_splits)
  apply(simp add: fut_def)
 apply(simp add: fut_def)
apply(rule ext)+
apply(simp add: size_td_fst_field_update)
apply(subst fut_cons)
apply(simp add: Let_def split_def)
done

lemma update_ti_fm:
  "update_ti (t::'a typ_info) \<equiv> snd (fold_td fut (map_td (\<lambda>n algn d. (n,field_update d)) t))"
apply(insert update_ti_fm'(1) [of t])
apply simp
done

lemma size_td_fst_norm_tu:
  "size_td (t::typ_uinfo) = fst (fold_td tyn
      (map_td (\<lambda>n x d. (n,  d)) t))"
  "size_td_struct (st::normalisor typ_struct) = fst (fold_td_struct (typ_name t) tyn (map_td_struct (\<lambda>n x d. (n,  d)) st))"
  "size_td_list (ts::typ_uinfo_pair list) = fst (fold_td_list (typ_name t) tyn  (map_td_list (\<lambda>n x d. (n,  d)) ts))"
  "size_td_pair (x::typ_uinfo_pair) = fst (fold_td_pair tyn  (map_td_pair (\<lambda>n x d. (n,  d)) x))"
apply(induct t and st and ts and x)
     apply(auto simp: tyn_def split_def split: dt_pair.splits)
done

lemma tyn_cons:
  "tyn tn (t#ts) = (let ((m,f),k) = t; (n,g) = tyn tn ts in
      (m+n, \<lambda>bs. f (take m bs) @ g (drop m bs)))"
apply(simp add: Let_def tyn_def)
apply(case_tac t, simp)
apply(case_tac a, simp+)
done

lemma norm_tu_fm':
  "norm_tu (t::normalisor typ_desc) = snd (fold_td tyn (map_td (\<lambda>n algn d. (n,d)) t))"
  "norm_tu_struct (st::normalisor typ_struct) = snd (fold_td_struct (typ_name t) tyn (map_td_struct (\<lambda>n algn d. (n,d)) st))"
  "norm_tu_list (ts::(normalisor typ_desc,field_name) dt_pair list) = snd (fold_td_list (typ_name t) tyn  (map_td_list (\<lambda>n x d. (n,d)) ts))"
  "norm_tu_pair (x::(normalisor typ_desc,field_name) dt_pair) = snd (fold_td_pair tyn  (map_td_pair (\<lambda>n x d. (n,d)) x))"
apply(induct t and st and ts and x)
     apply(auto simp: split: dt_pair.splits)
  apply(clarsimp simp: tyn_def split: typ_struct_splits)
 apply(simp add: tyn_def)
apply(rule ext)+
apply(simp add: size_td_fst_norm_tu)
apply(subst tyn_cons)
apply(simp add: Let_def split_def)
done

lemma norm_tu_fm:
  "norm_tu (t::typ_uinfo) \<equiv> snd (fold_td tyn (map_td (\<lambda>n algn d. (n,d)) t))"
apply(insert norm_tu_fm'(1) [of t])
apply simp
done

end
