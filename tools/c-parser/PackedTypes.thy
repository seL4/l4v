(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory PackedTypes
imports "Word_Lib.WordSetup" CProof
begin

section \<open>Underlying definitions for the class axioms\<close>

text \<open>field_access / field_update is the identity for packed types\<close>

definition fa_fu_idem :: "'a field_desc \<Rightarrow> nat \<Rightarrow> bool" where
  "fa_fu_idem fd n \<equiv>
     \<forall>bs bs' v. length bs = n \<longrightarrow> length bs' = n \<longrightarrow> field_access fd (field_update fd bs v) bs' = bs"

(* Is it better to do this or to use a fold over td?  This seems easier to use *)
primrec
  td_fafu_idem :: "'a field_desc typ_desc \<Rightarrow> bool" and
  td_fafu_idem_struct :: "'a field_desc typ_struct \<Rightarrow> bool" and
  td_fafu_idem_list :: " ('a field_desc typ_desc, char list) dt_pair list \<Rightarrow> bool" and
  td_fafu_idem_pair :: "('a field_desc typ_desc, char list) dt_pair \<Rightarrow> bool"
where
  fai0: "td_fafu_idem (TypDesc ts n) = td_fafu_idem_struct ts"

| fai1: "td_fafu_idem_struct (TypScalar n algn d) = fa_fu_idem d n"
| fai2: "td_fafu_idem_struct (TypAggregate ts) = td_fafu_idem_list ts"

| fai3: "td_fafu_idem_list [] = True"
| fai4: "td_fafu_idem_list (x#xs) = (td_fafu_idem_pair x \<and> td_fafu_idem_list xs)"

| fai5: "td_fafu_idem_pair (DTPair x n) = td_fafu_idem x"

lemmas td_fafu_idem_simps = fai0 fai1 fai2 fai3 fai4 fai5

text \<open>field_access is independent of the underlying bytes\<close>

definition  fa_heap_indep :: "'a field_desc \<Rightarrow> nat \<Rightarrow> bool" where
  "fa_heap_indep fd n \<equiv>
     \<forall>bs bs' v. length bs = n \<longrightarrow> length bs' = n \<longrightarrow> field_access fd v bs = field_access fd v bs'"


primrec
  td_fa_hi :: "'a field_desc typ_desc \<Rightarrow> bool" and
  td_fa_hi_struct :: "'a field_desc typ_struct \<Rightarrow> bool" and
  td_fa_hi_list :: "('a field_desc typ_desc, char list) dt_pair list \<Rightarrow> bool" and
  td_fa_hi_pair :: "('a field_desc typ_desc, char list) dt_pair \<Rightarrow> bool"
where
  fahi0: "td_fa_hi (TypDesc ts n) = td_fa_hi_struct ts"

| fahi1: "td_fa_hi_struct (TypScalar n algn d) = fa_heap_indep d n"
| fahi2: "td_fa_hi_struct (TypAggregate ts) = td_fa_hi_list ts"

| fahi3: "td_fa_hi_list [] = True"
| fahi4: "td_fa_hi_list (x#xs) = (td_fa_hi_pair x \<and> td_fa_hi_list xs)"

| fahi5: "td_fa_hi_pair (DTPair x n) = td_fa_hi x"

lemmas td_fa_hi_simps = fahi0 fahi1 fahi2 fahi3 fahi4 fahi5

section \<open>Lemmas about td_fafu_idem\<close>

lemma field_lookup_td_fafu_idem:
  shows "\<And>(s :: 'a field_desc typ_desc) f m n.
           \<lbrakk> field_lookup t f m = Some (s, n); td_fafu_idem t \<rbrakk> \<Longrightarrow> td_fafu_idem s"
  and   "\<And>(s :: 'a field_desc typ_desc) f m n.
           \<lbrakk> field_lookup_struct st f m = Some (s, n); td_fafu_idem_struct st \<rbrakk> \<Longrightarrow> td_fafu_idem s"
  and   "\<And>(s :: 'a field_desc typ_desc) f m n.
           \<lbrakk> field_lookup_list ts f m = Some (s, n); td_fafu_idem_list ts \<rbrakk> \<Longrightarrow> td_fafu_idem s"
  and   "\<And>(s :: 'a field_desc typ_desc) f m n.
           \<lbrakk> field_lookup_pair p f m = Some (s, n); td_fafu_idem_pair p \<rbrakk> \<Longrightarrow> td_fafu_idem s"
  by (induct t and st and ts and p) (auto split: if_split_asm option.splits)

lemma field_access_update_same:
  fixes t :: "'a :: mem_type field_desc typ_desc" and st :: "'a field_desc typ_struct"
  shows "\<And>(v :: 'a) bs bs'. \<lbrakk> td_fafu_idem t; wf_fd t; length bs = size_td t; length bs' = size_td t\<rbrakk>
  \<Longrightarrow> access_ti t (update_ti t bs v) bs' = bs"
  and "\<And>(v :: 'a) bs bs'. \<lbrakk> td_fafu_idem_struct st; wf_fd_struct st; length bs = size_td_struct st; length bs' = size_td_struct st \<rbrakk>
  \<Longrightarrow> access_ti_struct st (update_ti_struct st bs v) bs' = bs"
  and "\<And>(v :: 'a) bs bs'. \<lbrakk> td_fafu_idem_list ts; wf_fd_list ts; length bs = size_td_list ts; length bs' = size_td_list ts\<rbrakk>
  \<Longrightarrow> access_ti_list ts (update_ti_list ts bs v) bs' = bs"
  and "\<And>(v :: 'a) bs bs'. \<lbrakk> td_fafu_idem_pair p; wf_fd_pair p; length bs = size_td_pair p; length bs' = size_td_pair p\<rbrakk>
  \<Longrightarrow> access_ti_pair p (update_ti_pair p bs v) bs' = bs"
proof (induct t and st and ts and p)
  case TypScalar thus ?case by (clarsimp simp: fa_fu_idem_def)
next
  case (Cons_typ_desc p' ts' v bs bs')
  hence "fu_commutes (update_ti_pair_t p') (update_ti_list_t ts')" by clarsimp
  moreover
  have "update_ti_pair p' (take (size_td_pair p') bs) = update_ti_pair_t p' (take (size_td_pair p') bs)"
    using Cons_typ_desc.prems by (simp add: update_ti_pair_t_def min_ll)
  moreover
  have "update_ti_list ts' (drop (size_td_pair p') bs) = update_ti_list_t ts' (drop (size_td_pair p') bs)"
    using Cons_typ_desc.prems by (simp add: update_ti_list_t_def)
  ultimately have updeq:
    "(update_ti_pair p' (take (size_td_pair p') bs) (update_ti_list ts' (drop (size_td_pair p') bs) v))
    = (update_ti_list ts' (drop (size_td_pair p') bs) (update_ti_pair p' (take (size_td_pair p') bs) v))"
    unfolding fu_commutes_def by simp

  show ?case using Cons_typ_desc.prems
    by (clarsimp simp add: Cons_typ_desc.hyps) (simp add: updeq  Cons_typ_desc.hyps)
qed simp+

lemma access_ti_pair_dt_fst:
  "access_ti_pair p v bs = access_ti (dt_fst p) v bs"
  by (cases p, simp)

lemma size_td_pair_dt_fst:
  "size_td_pair p = size_td (dt_fst p)"
  by (cases p, simp)

lemma wf_fd_pair_dt_fst:
  "wf_fd_pair p = wf_fd (dt_fst p)"
  by (cases p, simp)

lemma field_lookup_offset2:
  assumes fl: "(field_lookup t f (m + n) = Some (s, q))"
  shows   "field_lookup t f m = Some (s, q - n)"
proof -
  from fl have le: "m + n \<le> q"
    by (rule field_lookup_offset_le)

  hence "q = (m + n) + (q - (m + n))"
    by simp

  hence "field_lookup t f (m + n) = Some (s, (m + n) + (q - (m + n)))" using fl by simp

  hence "field_lookup t f m = Some (s, m + (q - (m + n)))"
    by (rule iffD1 [OF field_lookup_offset'(1)])

  thus ?thesis using le by simp
qed

lemma field_lookup_offset2_list:
  assumes fl: "(field_lookup_list ts f (m + n) = Some (s, q))"
  shows   "field_lookup_list ts f m = Some (s, q - n)"
proof -
  from fl have le: "m + n \<le> q"
    by (rule field_lookup_offset_le)

  hence "q = (m + n) + (q - (m + n))"
    by simp

  hence "field_lookup_list ts f (m + n) = Some (s, (m + n) + (q - (m + n)))" using fl by simp

  hence "field_lookup_list ts f m = Some (s, m + (q - (m + n)))"
    by (rule iffD1 [OF field_lookup_offset'(3)])

  thus ?thesis using le by simp
qed

lemma field_lookup_offset2_pair:
  assumes fl: "(field_lookup_pair p f (m + n) = Some (s, q))"
  shows   "field_lookup_pair p f m = Some (s, q - n)"
proof -
  from fl have le: "m + n \<le> q"
    by (rule field_lookup_offset_le)

  hence "q = (m + n) + (q - (m + n))"
    by simp

  hence "field_lookup_pair p f (m + n) = Some (s, (m + n) + (q - (m + n)))" using fl by simp

  hence "field_lookup_pair p f m = Some (s, m + (q - (m + n)))"
    by (rule iffD1 [OF field_lookup_offset'(4)])

  thus ?thesis using le by simp
qed

lemma field_lookup_offset_size':
  shows "field_lookup t f 0 = Some (t',n) \<Longrightarrow> size_td t' + n \<le> size_td t"
  apply(drule td_set_field_lookupD)
  apply(erule td_set_offset_size)
done

lemma field_access_update_nth_inner:
  shows "\<And>f (s :: 'a :: mem_type field_desc typ_desc) n x v bs bs'.
  \<lbrakk> field_lookup t f 0 = Some (s, n); n \<le> x; x < n + size_td s; td_fafu_idem s; wf_fd s; wf_fd t;
  length bs = size_td s; length bs' = size_td t \<rbrakk>
  \<Longrightarrow> access_ti t (update_ti s bs v) bs' ! x = bs ! (x - n)"

  and "\<And>f (s :: 'a  :: mem_type field_desc typ_desc) n x v bs bs'.
  \<lbrakk>field_lookup_struct st f 0 = Some (s, n); n \<le> x; x < n + size_td s; td_fafu_idem s; wf_fd s; wf_fd_struct st;
  length bs = size_td s; length bs' = size_td_struct st \<rbrakk>
  \<Longrightarrow> access_ti_struct st (update_ti s bs v) bs' ! x = bs ! (x - n)"

  and "\<And>f (s :: 'a  :: mem_type field_desc typ_desc) n x v bs bs'.
  \<lbrakk>field_lookup_list ts f 0 = Some (s, n); n \<le> x; x < n + size_td s; td_fafu_idem s; wf_fd s; wf_fd_list ts;
  length bs = size_td s; length bs' = size_td_list ts\<rbrakk>
  \<Longrightarrow> access_ti_list ts (update_ti s bs v) bs' ! x = bs ! (x - n)"

  and "\<And>f (s :: 'a  :: mem_type field_desc typ_desc) n x v bs bs'.
  \<lbrakk>field_lookup_pair p f 0 = Some (s, n); n \<le> x; x < n + size_td s; td_fafu_idem s; wf_fd s; wf_fd_pair p;
  length bs = size_td s; length bs' = size_td_pair p\<rbrakk>
  \<Longrightarrow> access_ti_pair p (update_ti s bs v) bs' ! x = bs ! (x - n)"
proof (induct t and st and ts and p)
  case (TypDesc typ_struct ls f s n x v bs bs')

  show ?case
  proof (cases "f = []")
    case False thus ?thesis using TypDesc by clarsimp
  next
    case True
    thus ?thesis using TypDesc.prems
      by (simp add: field_access_update_same)
  qed
next
  case (Cons_typ_desc p' ts' f s n x v bs bs')
  have nlex: "n \<le> x" and xln: "x < n + size_td s"
    and lbs: "length bs = size_td s" and lbs': "length bs' = size_td_list (p' # ts')" by fact+
  from Cons_typ_desc have wf: "wf_fd (dt_fst p')" and wfts: "wf_fd_list ts'" by (cases p', auto)

  {
    assume fl: "field_lookup_list ts' f (size_td (dt_fst p')) = Some (s, n)"

    hence mlt: "size_td (dt_fst p') \<le> n"
      by (rule field_lookup_offset_le)

    hence "size_td (dt_fst p') \<le> x"
      by (rule order_trans) fact

    hence ?case using wf lbs lbs'
    proof (simp add: nth_append length_fa_ti access_ti_pair_dt_fst size_td_pair_dt_fst)
      from fl have fl': "field_lookup_list ts' f 0 = Some (s, n - size_td (dt_fst p'))"
        by (rule field_lookup_offset2_list [where m = 0, simplified])

      show "access_ti_list ts' (update_ti s bs v) (drop (size_td (dt_fst p')) bs') ! (x - size_td (dt_fst p')) = bs ! (x - n)"
        using mlt nlex xln lbs lbs' wf wfts \<open>td_fafu_idem s\<close> \<open>wf_fd s\<close>
        by (simp add: Cons_typ_desc.hyps(2) [OF fl'] size_td_pair_dt_fst)
    qed
  }
  moreover
  {
    note ih = Cons_typ_desc.hyps(1)[simplified access_ti_pair_dt_fst wf_fd_pair_dt_fst]

    assume fl: "field_lookup_pair p' f 0 = Some (s, n)"

    hence "x < size_td (dt_fst p')"
      apply (cases p')
      apply (simp split: if_split_asm)
      apply (drule field_lookup_offset_size')
      apply (rule order_less_le_trans [OF xln])
      apply simp
      done

    hence ?case using wf lbs lbs' nlex xln wf wfts \<open>td_fafu_idem s\<close> \<open>wf_fd s\<close>
      by (simp add: nth_append length_fa_ti access_ti_pair_dt_fst size_td_pair_dt_fst ih[OF fl])
  }
  ultimately show ?case using \<open>field_lookup_list (p' # ts') f 0 = Some (s, n)\<close> by (simp split: option.splits)
qed (clarsimp split: if_split_asm)+

subsection \<open>td_fa_hi\<close>

(* \<lbrakk> size_of TYPE('a::mem_type) \<le> length h; size_of TYPE('a) \<le> length h' \<rbrakk> \<Longrightarrow> *)

lemma fa_heap_indepD:
  "\<lbrakk> fa_heap_indep fd n; length bs = n; length bs' = n \<rbrakk> \<Longrightarrow>
  field_access fd v bs = field_access fd v bs'"
  unfolding fa_heap_indep_def
  apply (drule spec, drule spec, drule spec)
  apply (drule (1) mp)
  apply (erule (1) mp)
  done

(* The simplifier spins on the IHs here, hence the proofs for each case *)
lemma td_fa_hi_heap_independence:
  shows "\<And>(v :: 'a :: mem_type) h h'. \<lbrakk> td_fa_hi t; length h = size_td t; length h' = size_td t \<rbrakk>
  \<Longrightarrow> access_ti t v h = access_ti t v h'"
  and   "\<And>(v :: 'a :: mem_type) h h'. \<lbrakk> td_fa_hi_struct st; length h = size_td_struct st; length h' = size_td_struct st\<rbrakk>
  \<Longrightarrow> access_ti_struct st v h = access_ti_struct st v h'"
  and   "\<And>(v :: 'a :: mem_type) h h'. \<lbrakk> td_fa_hi_list ts;  length h = size_td_list ts; length h' = size_td_list ts \<rbrakk>
  \<Longrightarrow> access_ti_list ts v h = access_ti_list ts v h'"
  and   "\<And>(v :: 'a :: mem_type) h h'. \<lbrakk> td_fa_hi_pair p;  length h = size_td_pair p; length h' = size_td_pair p \<rbrakk>
  \<Longrightarrow> access_ti_pair p v h = access_ti_pair p v h'"
proof (induct t and st and ts and p)
  case TypDesc
  from TypDesc.prems show ?case
    by (simp) (erule (2) TypDesc.hyps)
next
  case TypScalar
  from TypScalar.prems show ?case
    by simp (erule (2) fa_heap_indepD)
next
  case TypAggregate
  from TypAggregate.prems show ?case
    by (simp) (erule (2) TypAggregate.hyps)
next
  case Nil_typ_desc thus ?case by simp
next
  case Cons_typ_desc
  from Cons_typ_desc.prems show ?case
    apply simp
    apply (erule conjE)
    apply (rule arg_cong2 [where f = "(@)"])
    apply (erule Cons_typ_desc.hyps; simp)
    apply (erule Cons_typ_desc.hyps; simp)
    done
next
  case DTPair_typ_desc
  from DTPair_typ_desc.prems show ?case
    by simp (erule (2) DTPair_typ_desc.hyps)
qed

section \<open>Simp rules for deriving packed props from the type combinators\<close>

subsection \<open>td_fafu_idem\<close>

lemma td_fafu_idem_final_pad:
  "padup (2 ^ align_td t) (size_td t) = 0
  \<Longrightarrow> td_fafu_idem (final_pad t) = td_fafu_idem t"
  unfolding final_pad_def
  by (clarsimp simp add: padup_def Let_def)

lemma td_fafu_idem_ti_typ_pad_combine:
  fixes t :: "'a :: c_type itself" and s :: "'b :: c_type field_desc typ_desc"
  assumes pad: "padup (align_of TYPE('a)) (size_td s) = 0"
  shows "td_fafu_idem (ti_typ_pad_combine t xf xfu nm s) = td_fafu_idem (ti_typ_combine t xf xfu nm s)"
  unfolding ti_typ_pad_combine_def using pad
  by (clarsimp simp: Let_def)

lemma td_fafu_idem_list_append:
  fixes xs :: "'a :: c_type field_desc typ_pair list"
  shows "td_fafu_idem_list (xs @ ys) = (td_fafu_idem_list xs \<and> td_fafu_idem_list ys)"
  by (induct xs) simp+

lemma td_fafu_idem_extend_ti:
  fixes t :: "'a :: c_type field_desc typ_desc"
  assumes as: "td_fafu_idem s"
  and     at: "td_fafu_idem t"
  shows "td_fafu_idem (extend_ti s t nm)" using as at
  by (cases s, rename_tac typ_struct xs)
     (case_tac typ_struct; simp add: td_fafu_idem_list_append)

lemma fd_cons_access_updateD:
  "\<lbrakk> fd_cons_access_update d n; length bs = n; length bs' = n\<rbrakk> \<Longrightarrow>
   field_access d (field_update d bs v) bs' = field_access d (field_update d bs v') bs'"
  unfolding fd_cons_access_update_def by clarsimp

lemma fa_fu_idem_update_desc:
  fixes a :: "'a field_desc"
  assumes fg: "fg_cons xf xfu"
  and     fd: "fd_cons_struct (TypScalar n n' a)"
  shows   "fa_fu_idem (update_desc xf xfu a) n = fa_fu_idem a n"
proof
  assume asm: "fa_fu_idem (update_desc xf xfu a) n"

  let ?fu = "\<lambda>bs. if length bs = n then field_update a bs else id"
  let ?a' = "\<lparr> field_access = field_access a, field_update = ?fu \<rparr>"

  show "fa_fu_idem a n"
    unfolding fa_fu_idem_def
  proof (intro impI conjI allI)
    fix bs :: "byte list" and bs' :: "byte list" and v
    assume l: "length bs = n" and l': "length bs' = n"

    hence "(\<forall>v. field_access a (field_update a bs (xf v)) bs' = bs)
           = (\<forall>v. field_access a (?fu bs (xf v)) bs' = bs)" by simp

    also have "\<dots> = (\<forall>v. field_access a (field_update a bs v) bs' = bs)" using fd
      apply -
      apply (rule iffI)
       apply (rule allI)
       apply (subst (asm) fd_cons_access_updateD [OF _ l l', where d = ?a', simplified])
        apply (simp add: fd_cons_struct_def fd_cons_desc_def)
       apply (fastforce simp: l l')
      apply (fastforce simp: l l')
      done

    finally show "field_access a (field_update a bs v) bs' = bs" using asm fg l l'
      by (clarsimp simp add: update_desc_def fa_fu_idem_def fg_cons_def)
  qed
next
  assume "fa_fu_idem a n"
  thus "fa_fu_idem (update_desc xf xfu a) n"
    unfolding fa_fu_idem_def update_desc_def using fg
    by (clarsimp simp add: update_desc_def fa_fu_idem_def fg_cons_def)
qed

lemma td_fafu_idem_map_td_update_desc:
  assumes fg: "fg_cons xf xfu"
  shows  "wf_fd t \<Longrightarrow> td_fafu_idem (map_td (\<lambda>_ _. update_desc xf xfu) t) = td_fafu_idem t"
  and    "wf_fd_struct st \<Longrightarrow> td_fafu_idem_struct (map_td_struct (\<lambda>_ _. update_desc xf xfu) st) = td_fafu_idem_struct st"
  and    "wf_fd_list ts \<Longrightarrow> td_fafu_idem_list (map_td_list (\<lambda>_ _. update_desc xf xfu) ts) = td_fafu_idem_list ts"
  and    "wf_fd_pair p \<Longrightarrow> td_fafu_idem_pair (map_td_pair (\<lambda>_ _. update_desc xf xfu) p) = td_fafu_idem_pair p"
  by (induct t and st and ts and p) (auto elim!: fa_fu_idem_update_desc [OF fg])

lemmas td_fafu_idem_adjust_ti = td_fafu_idem_map_td_update_desc(1)[folded adjust_ti_def]

lemma td_fafu_idem_ti_typ_combine:
  fixes s :: "'b :: c_type field_desc typ_desc"
  assumes fg: "fg_cons xf xfu"
  and    tda: "td_fafu_idem (typ_info_t TYPE('a :: mem_type))"
  and    tds: "td_fafu_idem s"
  shows "td_fafu_idem (ti_typ_combine TYPE('a :: mem_type) xf xfu nm s)"
  unfolding ti_typ_combine_def using tda tds
  apply (clarsimp simp: Let_def)
  apply (cases s)
  apply (rename_tac typ_struct xs)
  apply (case_tac typ_struct)
   apply simp
   apply (subst td_fafu_idem_adjust_ti [OF fg wf_fd], assumption)
  apply (simp add: td_fafu_idem_list_append)
  apply (subst td_fafu_idem_adjust_ti [OF fg wf_fd], assumption)
  done

lemma td_fafu_idem_ptr:
   "td_fafu_idem (typ_info_t TYPE('a :: c_type ptr))"
  apply (clarsimp simp add: fa_fu_idem_def)
  apply (subst word_rsplit_rcat_size)
   apply (clarsimp simp add: size_of_def word_size)
  apply simp
  done

lemma td_fafu_idem_word:
   "td_fafu_idem (typ_info_t TYPE('a :: len8 word))"
  apply(clarsimp simp: fa_fu_idem_def)
  apply (subst word_rsplit_rcat_size)
   apply (insert len8_dv8)
   apply (clarsimp simp add: size_of_def word_size)
   apply (subst dvd_div_mult_self; simp)
  apply simp
  done

lemma fg_cons_array [simp]:
  "n < card (UNIV :: 'b :: finite set) \<Longrightarrow>
   fg_cons (\<lambda>x. index x n) (\<lambda>x f. Arrays.update (f :: 'a['b]) n x)"
  unfolding fg_cons_def by simp

lemma td_fafu_idem_array_n:
  "\<lbrakk> td_fafu_idem (typ_info_t TYPE('a)); n \<le> card (UNIV :: 'b set) \<rbrakk> \<Longrightarrow>
   td_fafu_idem (array_tag_n n :: ('a :: mem_type ['b :: finite]) field_desc typ_desc)"
  by (induct n; simp add: array_tag_n.simps empty_typ_info_def)
     (simp add: td_fafu_idem_ti_typ_combine)

lemma td_fafu_idem_array:
  "td_fafu_idem (typ_info_t TYPE('a)) \<Longrightarrow> td_fafu_idem (typ_info_t TYPE('a :: mem_type ['b :: finite]))"
  by (clarsimp simp: typ_info_array array_tag_def fa_fu_idem_def td_fafu_idem_array_n)

lemma td_fafu_idem_empty_typ_info:
  "td_fafu_idem (empty_typ_info t)"
  unfolding empty_typ_info_def
  by simp

subsection \<open>td_fa_hi\<close>

(* These are mostly identical to the above --- surely there is something which implies both? *)

lemma td_fa_hi_final_pad:
  "padup (2 ^ align_td t) (size_td t) = 0
  \<Longrightarrow> td_fa_hi (final_pad t) = td_fa_hi t"
  unfolding final_pad_def
  by (clarsimp simp add: padup_def Let_def)

lemma td_fa_hi_ti_typ_pad_combine:
  fixes t :: "'a :: c_type itself" and s :: "'b :: c_type field_desc typ_desc"
  assumes pad: "padup (align_of TYPE('a)) (size_td s) = 0"
  shows "td_fa_hi (ti_typ_pad_combine t xf xfu nm s) = td_fa_hi (ti_typ_combine t xf xfu nm s)"
  unfolding ti_typ_pad_combine_def using pad
  by (clarsimp simp: Let_def)

lemma td_fa_hi_list_append:
  fixes xs :: "'a :: c_type field_desc typ_pair list"
  shows "td_fa_hi_list (xs @ ys) = (td_fa_hi_list xs \<and> td_fa_hi_list ys)"
  by (induct xs) simp+

lemma td_fa_hi_extend_ti:
  fixes t :: "'a :: c_type field_desc typ_desc"
  assumes as: "td_fa_hi s"
  and     at: "td_fa_hi t"
  shows "td_fa_hi (extend_ti s t nm)" using as at
  by (cases s, rename_tac typ_struct xs)
     (case_tac typ_struct; simp add: td_fa_hi_list_append)

lemma fa_heap_indep_update_desc:
  fixes a :: "'a field_desc"
  assumes fg: "fg_cons xf xfu"
  and     fd: "fd_cons_struct (TypScalar n n' a)"
  shows   "fa_heap_indep (update_desc xf xfu a) n = fa_heap_indep a n"
proof
  assume asm: "fa_heap_indep (update_desc xf xfu a) n"

  have xf_xfu: "\<And>v v'. xf (xfu v v') = v" using fg
    unfolding fg_cons_def
    by simp

  show "fa_heap_indep a n"
    unfolding fa_heap_indep_def
  proof (intro impI conjI allI)
    fix bs :: "byte list" and bs' :: "byte list" and v
    assume l: "length bs = n" and l': "length bs' = n"
    with asm
    have "field_access (update_desc xf xfu a) (xfu v undefined) bs =
          field_access (update_desc xf xfu a) (xfu v undefined) bs'"
      by (rule fa_heap_indepD)

    thus "field_access a v bs = field_access a v bs'"
      unfolding update_desc_def
      by (simp add: xf_xfu)
  qed
next
  assume asm: "fa_heap_indep a n"
  show "fa_heap_indep (update_desc xf xfu a) n"
    unfolding fa_heap_indep_def update_desc_def
  proof (simp, intro impI conjI allI)
    fix bs :: "byte list" and bs' :: "byte list" and v
    assume l: "length bs = n" and l': "length bs' = n"

    with asm show "field_access a (xf v) bs = field_access a (xf v) bs'"
      by (rule fa_heap_indepD)
  qed
qed

lemma td_fa_hi_map_td_update_desc:
  assumes fg: "fg_cons xf xfu"
  shows  "wf_fd t \<Longrightarrow> td_fa_hi (map_td (\<lambda>_ _. update_desc xf xfu) t) = td_fa_hi t"
  and    "wf_fd_struct st \<Longrightarrow> td_fa_hi_struct (map_td_struct (\<lambda>_ _. update_desc xf xfu) st) = td_fa_hi_struct st"
  and    "wf_fd_list ts \<Longrightarrow> td_fa_hi_list (map_td_list (\<lambda>_ _. update_desc xf xfu) ts) = td_fa_hi_list ts"
  and    "wf_fd_pair p \<Longrightarrow> td_fa_hi_pair (map_td_pair (\<lambda>_ _. update_desc xf xfu) p) = td_fa_hi_pair p"
  by (induct t and st and ts and p) (auto elim!: fa_heap_indep_update_desc [OF fg])

lemmas td_fa_hi_adjust_ti = td_fa_hi_map_td_update_desc(1)[folded adjust_ti_def]

lemma td_fa_hi_ti_typ_combine:
  fixes s :: "'b :: c_type field_desc typ_desc"
  assumes fg: "fg_cons xf xfu"
  and    tda: "td_fa_hi (typ_info_t TYPE('a :: mem_type))"
  and    tds: "td_fa_hi s"
  shows "td_fa_hi (ti_typ_combine TYPE('a :: mem_type) xf xfu nm s)"
  unfolding ti_typ_combine_def Let_def using tda tds
  by (cases s, rename_tac typ_struct xs)
     (case_tac typ_struct; simp add: td_fa_hi_list_append td_fa_hi_adjust_ti[OF fg wf_fd])

lemma td_fa_hi_ptr:
   "td_fa_hi (typ_info_t TYPE('a :: c_type ptr))"
  by (clarsimp simp add: fa_heap_indep_def)

lemma td_fa_hi_word:
   "td_fa_hi (typ_info_t TYPE('a :: len8 word))"
  by (clarsimp simp add: fa_heap_indep_def)

lemma td_fa_hi_array_n:
  "\<lbrakk>td_fa_hi (typ_info_t TYPE('a)); n \<le> card (UNIV :: 'b set) \<rbrakk> \<Longrightarrow> td_fa_hi (array_tag_n n :: ('a :: mem_type ['b :: finite]) field_desc typ_desc)"
  by (induct n; simp add: array_tag_n.simps empty_typ_info_def td_fa_hi_ti_typ_combine)

lemma td_fa_hi_array:
  "td_fa_hi (typ_info_t TYPE('a)) \<Longrightarrow> td_fa_hi (typ_info_t TYPE('a :: mem_type ['b :: finite]))"
  by (clarsimp simp add: typ_info_array array_tag_def fa_fu_idem_def td_fa_hi_array_n)

lemma td_fa_hi_empty_typ_info:
  "td_fa_hi (empty_typ_info t)"
  unfolding empty_typ_info_def
  by simp

section \<open>The type class and simp sets\<close>

text \<open>Packed types, with no padding, have the defining property that
        access is invariant under substitution of the underlying heap and
        access/update is the identity\<close>

class packed_type = mem_type +
  assumes td_fafu_idem: "td_fafu_idem (typ_info_t TYPE('a::c_type))"
  assumes td_fa_hi:     "td_fa_hi (typ_info_t TYPE('a::c_type))"

lemmas td_fafu_idem_intro_simps =
  \<comment> \<open>Axioms\<close>
  td_fafu_idem
  \<comment> \<open>Combinators\<close>
  td_fafu_idem_final_pad td_fafu_idem_ti_typ_pad_combine td_fafu_idem_ti_typ_combine td_fafu_idem_empty_typ_info
  \<comment> \<open>Constructors\<close>
  td_fafu_idem_ptr td_fafu_idem_word td_fafu_idem_array

lemmas td_fa_hi_intro_simps =
  \<comment> \<open>Axioms\<close>
  td_fa_hi
  \<comment> \<open>Combinators\<close>
  td_fa_hi_final_pad td_fa_hi_ti_typ_pad_combine td_fa_hi_ti_typ_combine td_fa_hi_empty_typ_info
  \<comment> \<open>Constructors\<close>
  td_fa_hi_ptr td_fa_hi_word td_fa_hi_array

lemma align_td_array':
  "align_td (typ_info_t TYPE('a :: c_type['b :: finite])) = align_td (typ_info_t TYPE('a))"
  by (simp add: typ_info_array array_tag_def align_td_array_tag)

lemmas packed_type_intro_simps =
  td_fafu_idem_intro_simps td_fa_hi_intro_simps align_td_array' size_td_simps size_td_array

lemma access_ti_append':
  "\<And>list.
   access_ti_list (xs @ ys) t list =
     access_ti_list xs t (take (size_td_list xs) list) @
     access_ti_list ys t (drop (size_td_list xs) list)"
proof(induct xs)
  case Nil show ?case by simp
next
  case (Cons x xs) thus ?case by (simp add: min_def ac_simps drop_take)
qed

section \<open>Instances\<close>

text \<open>Words (of multiple of 8 size) are packed\<close>

instantiation word :: (len8) packed_type
begin
instance
  by (intro_classes; rule td_fafu_idem_word td_fa_hi_word)
end

text \<open>Pointers are always packed\<close>

instantiation ptr :: (c_type)packed_type
begin
instance
  by (intro_classes; simp add: fa_fu_idem_def word_rsplit_rcat_size word_size fa_heap_indep_def)
end

text \<open>Arrays of packed types are in turn packed\<close>

class array_outer_packed = packed_type + array_outer_max_size
class array_inner_packed = array_outer_packed + array_inner_max_size

instance word :: (len8)array_outer_packed ..
instance word :: (len8)array_inner_packed ..

instance array :: (array_outer_packed, array_max_count) packed_type
  by (intro_classes; simp add: td_fafu_idem_intro_simps td_fa_hi_intro_simps)

instance array :: (array_inner_packed, array_max_count) array_outer_packed ..

section \<open>Theorems about packed types\<close>

subsection \<open>td_fa_hi\<close>

lemma heap_independence:
  "\<lbrakk>length h = size_of TYPE('a :: packed_type); length h' = size_of TYPE('a) \<rbrakk>
  \<Longrightarrow> access_ti (typ_info_t TYPE('a)) v h = access_ti (typ_info_t TYPE('a)) v h'"
  by (rule td_fa_hi_heap_independence(1)[OF td_fa_hi], simp_all add: size_of_def)

theorem packed_heap_update_collapse:
 fixes u::"'a::packed_type"
 fixes v::"'a"
 shows "heap_update p v (heap_update p u h) = heap_update p v h"
  unfolding heap_update_def
  apply(rule ext)
  apply(case_tac "x \<in> {ptr_val p..+size_of TYPE('a)}")
   apply(simp add: heap_update_mem_same_point)
   apply(simp add:to_bytes_def)
   apply(subst heap_independence, simp)
    prefer 2
    apply(rule refl)
   apply(simp)
  apply(simp add: heap_update_nmem_same)
  done

lemma packed_heap_update_collapse_hrs:
  fixes p :: "'a :: packed_type ptr"
  shows "hrs_mem_update (heap_update p v) (hrs_mem_update (heap_update p v') hp) =
         hrs_mem_update (heap_update p v) hp"
  unfolding hrs_mem_update_def
  by (simp add: split_def packed_heap_update_collapse)

subsection \<open>td_fafu_idem\<close>

lemma order_leE:
  fixes x :: "'a :: order"
  shows "\<lbrakk> x \<le> y; x = y \<Longrightarrow> P; x < y \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto simp: order_le_less)

lemma of_nat_mono_maybe_le:
  shows "\<lbrakk>X < 2 ^ len_of TYPE('a); Y \<le> X\<rbrakk> \<Longrightarrow> (of_nat Y :: 'a :: len word) \<le> of_nat X"
  apply (erule order_leE)
   apply simp
  apply (rule order_less_imp_le)
  apply (erule (1) of_nat_mono_maybe)
  done

lemma intvl_le_lower:
  fixes x :: "'a :: len word"
  shows "\<lbrakk> x \<in> {y..+n}; y \<le> y + of_nat (n - 1); n < 2 ^ len_of TYPE('a) \<rbrakk> \<Longrightarrow> y \<le> x"
  apply (drule intvlD)
  apply (elim conjE exE)
  apply (erule ssubst)
  apply (erule word_plus_mono_right2)
  apply (rule of_nat_mono_maybe_le)
   apply simp
  apply simp
  done

lemma intvl_less_upper:
  fixes x :: "'a :: len word"
  shows "\<lbrakk> x \<in> {y..+n}; y \<le> y + of_nat (n - 1); n < 2 ^ len_of TYPE('a) \<rbrakk> \<Longrightarrow> x \<le> y + of_nat (n - 1)"
  apply (drule intvlD)
  apply (elim conjE exE)
  apply (erule ssubst)
  apply (rule word_plus_mono_right; assumption?)
  apply (rule of_nat_mono_maybe_le; simp)
  done

lemma packed_type_access_ti:
  fixes v :: "'a :: packed_type"
  assumes lbs: "length bs = size_of TYPE('a)"
  shows "access_ti (typ_info_t TYPE('a)) v bs = access_ti\<^sub>0 (typ_info_t TYPE('a)) v"
  unfolding access_ti\<^sub>0_def
  by (rule heap_independence; simp add: lbs size_of_def)

lemma update_ti_update_ti_t:
  "length bs = size_td s \<Longrightarrow> update_ti s bs v = update_ti_t s bs v"
  unfolding update_ti_t_def by simp

lemma heap_list_nth:
  "m < n \<Longrightarrow> heap_list hp n p ! m = hp (p + of_nat m)"
proof (induct m arbitrary: n p)
  case (0 n' p')
  thus ?case by (cases n', simp_all)
next
  case (Suc m' n' p')
  show ?case
  proof (cases n')
    case 0 thus ?thesis using \<open>Suc m' < n'\<close> by simp
  next
    case (Suc n'')
    hence "m' < n''" using \<open>Suc m' < n'\<close> by simp
    thus ?thesis using Suc
      by (simp add: Suc.hyps ac_simps)
  qed
qed

lemma c_guard_field_lvalue:
  fixes p :: "'a :: mem_type ptr"
  assumes cg: "c_guard p"
  and     fl: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (t, n)"
  and     eu: "export_uinfo t = typ_uinfo_t TYPE('b :: mem_type)"
  shows   "c_guard (Ptr &(p\<rightarrow>f) :: 'b :: mem_type ptr)"
  unfolding c_guard_def
proof (rule conjI)
  from cg fl eu show "ptr_aligned (Ptr &(p\<rightarrow>f) :: 'b ptr)"
    by (rule c_guard_ptr_aligned_fl)
next
  from eu have std: "size_td t = size_of TYPE('b)" using fl
    by (simp add: export_size_of)

  from cg have "c_null_guard p" unfolding c_guard_def ..
  thus "c_null_guard (Ptr &(p\<rightarrow>f)  :: 'b ptr)" unfolding c_null_guard_def
    apply (rule contrapos_nn)
    apply (rule subsetD [OF field_tag_sub, OF fl])
    apply (simp add: std)
    done
qed


lemma c_guard_no_wrap:
  fixes p :: "'a :: mem_type ptr"
  assumes cgrd: "c_guard p"
  shows   "ptr_val p \<le> ptr_val p + of_nat (size_of TYPE('a) - 1)"
  using cgrd unfolding c_guard_def c_null_guard_def
  apply -
  apply (erule conjE)
  apply (erule contrapos_np)
  apply (simp add: intvl_def)
  apply (drule word_wrap_of_natD)
  apply (erule exE)
  apply (rule exI)
  apply (simp add: nat_le_Suc_less)
  done

theorem packed_heap_super_field_update:
  fixes v :: "'a :: packed_type" and p :: "'b :: packed_type ptr"
  assumes fl: "field_lookup (typ_info_t TYPE('b)) f 0 = Some (t, n)"
  and   cgrd: "c_guard p"
  and     eu: "export_uinfo t = typ_uinfo_t TYPE('a)"
  shows   "heap_update (Ptr &(p\<rightarrow>f)) v hp = heap_update p (update_ti t (to_bytes_p v) (h_val hp p)) hp"
  unfolding heap_update_def to_bytes_def
proof (simp add: packed_type_access_ti, rule ext)
  fix x
  let ?LHS = "heap_update_list &(p\<rightarrow>f) (to_bytes_p v) hp x"
  let ?RHS = "heap_update_list (ptr_val p) (to_bytes_p (update_ti t (to_bytes_p v) (h_val hp p))) hp x"

  from cgrd have al: "ptr_val p \<le> ptr_val p + of_nat (size_of TYPE('b) - 1)" by (rule c_guard_no_wrap)

  have szb: "size_of TYPE('b) < 2 ^ len_of TYPE(addr_bitsize)"
    apply (fold card_word)
    apply (fold addr_card_def)
    apply (rule max_size)
    done

  have szt: "n + size_td t \<le> size_of TYPE('b)"
    unfolding size_of_def
    by (subst add.commute, rule field_lookup_offset_size [OF fl])
  moreover have t0: "0 < size_td t" using fl wf_size_desc
    by (rule field_lookup_wf_size_desc_gt)
  ultimately have szn: "n < size_of TYPE('b)" by simp
  from szt have szt1: "n + (size_td t - 1) \<le> size_of TYPE('b)"
    by simp

  have b0: "0 < size_of (TYPE ('b))" using wf_size_desc
    unfolding size_of_def
    by (rule wf_size_desc_gt)

  have uofn: "unat (of_nat n :: addr_bitsize word) = n" using szn szb
    by (simp add: nat_less_le unat_of_nat_eq)

  from eu have std: "size_td t = size_of TYPE('a)" using fl
    by (simp add: export_size_of)

  hence "?LHS = (if x \<in> {&(p\<rightarrow>f)..+size_td t} then (to_bytes_p v) ! unat (x - &(p\<rightarrow>f)) else hp x)"
    by (simp add: heap_update_mem_same_point heap_update_nmem_same)
  also have "... = ?RHS"
  proof (simp, intro impI conjI)
    assume xin: "x \<in> {&(p\<rightarrow>f)..+size_td t}"
    have "to_bytes_p v ! unat (x - &(p\<rightarrow>f)) = to_bytes_p (update_ti t (to_bytes_p v) (h_val hp p)) ! unat (x - ptr_val p)"
    proof (simp add: to_bytes_p_def to_bytes_def, subst field_access_update_nth_inner(1)[OF fl, simplified])

      have "c_guard (Ptr &(p\<rightarrow>f) :: 'a ptr)" using cgrd fl eu
        by (rule c_guard_field_lvalue)
      hence pft: "&(p\<rightarrow>f) \<le> &(p\<rightarrow>f) + of_nat (size_td t - 1)"
        apply -
        apply (drule c_guard_no_wrap)
        apply (simp add: std)
        done

      have szt': "size_td t < 2 ^ len_of TYPE(addr_bitsize)"
        apply (subst std)
        apply (fold card_word)
        apply (fold addr_card_def)
        apply (rule max_size)
        done

      have ofn: "of_nat n \<le> x - ptr_val p"
      proof (rule le_minus')
        from xin show "ptr_val p + of_nat n \<le> x" using pft szt'
          unfolding field_lvalue_def field_lookup_offset_eq [OF fl]
          by (rule intvl_le_lower)
      next
        from szb szn have "of_nat n \<le> (of_nat (size_of TYPE('b) - 1) :: addr_bitsize word)"
          apply -
          apply (rule of_nat_mono_maybe_le)
           apply simp_all
          done
        with al show "ptr_val p \<le> ptr_val p + of_nat n"
          by (rule word_plus_mono_right2)
      qed

      thus nlt: "n \<le> unat (x - ptr_val p)"
        by (simp add: word_le_nat_alt uofn)
      have "x \<le> ptr_val p + (of_nat n + of_nat (size_td t - 1))" using xin pft szt' t0
        unfolding field_lvalue_def field_lookup_offset_eq [OF fl]
        apply -
        apply (drule (2) intvl_less_upper)
        apply (simp add: add.assoc)
        done
      moreover have "x \<in> {ptr_val p..+size_of TYPE('b)}" using fl xin
        by (rule subsetD [OF field_tag_sub])
      ultimately have "x - ptr_val p \<le> (of_nat n + of_nat (size_td t - 1))" using al szb
        apply -
        apply (rule word_diff_ls(4)[where xa=x and x=x for x, simplified])
         apply (metis (hide_lams, mono_tags) add.commute of_nat_add)
        apply (erule (2) intvl_le_lower)
        done
      moreover have "unat (of_nat n + of_nat (size_td t - 1) :: addr_bitsize word) = n + size_td t - 1"
        using t0 order_le_less_trans [OF szt1 szb]
        apply (subst Abs_fnat_homs(1))
        apply (subst unat_of_nat)
        apply simp
        done
      ultimately have "unat (x - ptr_val p) \<le> n + size_td t - 1"
        by (simp add: word_le_nat_alt)
      thus "unat (x - ptr_val p) < n + size_td t" using t0
        by simp

      show "td_fafu_idem t"
        by (rule field_lookup_td_fafu_idem(1)[OF fl td_fafu_idem])

      show "wf_fd t"
        by (rule wf_fd_field_lookupD [OF fl wf_fd])

      show "length (access_ti (typ_info_t TYPE('a)) v (replicate (size_of TYPE('a)) 0)) = size_td t"
        using wf_fd [where 'a = 'a]
        by (simp add: length_fa_ti size_of_def std)

      show "length (replicate (size_of TYPE('b)) 0) = size_td (typ_info_t TYPE('b))"
        by (simp add: size_of_def)

      have "unat (x - &(p\<rightarrow>f)) = unat ((x - ptr_val p) - of_nat n)"
        by (simp add: field_lvalue_def field_lookup_offset_eq [OF fl])
      also have "\<dots> = unat (x - ptr_val p) - n"
        by (simp add: unat_sub [OF ofn] uofn)
      finally have "unat (x - &(p\<rightarrow>f)) = unat (x - ptr_val p) - n" .

      thus "access_ti (typ_info_t TYPE('a)) v (replicate (size_of TYPE('a)) 0) ! unat (x - &(p\<rightarrow>f)) =
        access_ti (typ_info_t TYPE('a)) v (replicate (size_of TYPE('a)) 0) ! (unat (x - ptr_val p) - n)"
        by simp
    qed

    thus "to_bytes_p v ! unat (x - &(p\<rightarrow>f)) = ?RHS"
    proof (subst heap_update_mem_same_point, simp_all)
      show "x \<in> {ptr_val p..+size_of TYPE('b)}" using fl xin
        by (rule subsetD [OF field_tag_sub])
    qed
  next
    assume xni: "x \<notin> {&(p\<rightarrow>f)..+size_td t}"
    have "?RHS = (if x \<in> {ptr_val p..+size_of TYPE('b)}
          then (to_bytes_p (update_ti t (to_bytes_p v) (h_val hp p))) ! unat (x - ptr_val p) else hp x)"
      by (simp add: heap_update_mem_same_point heap_update_nmem_same)

    also
    {
      assume xin: "x \<in> {ptr_val p..+size_of TYPE('b)}"

      hence "access_ti (typ_info_t TYPE('b))
        (update_ti_t t (access_ti (typ_info_t TYPE('a)) v (replicate (size_of TYPE('a)) 0)) (h_val hp p))
        (replicate (size_of TYPE('b)) 0) ! unat (x - ptr_val p) = hp x"
      proof (subst field_access_update_nth_disjD [OF fl])
        have "x - ptr_val p \<le> of_nat (size_of TYPE('b) - 1)"
        proof (rule word_diff_ls(4)[where xa=x and x=x for x, simplified])
          from xin show "x \<le> of_nat (size_of TYPE('b) - 1) + ptr_val p" using al szb
            by (subst add.commute, rule intvl_less_upper)
          show "ptr_val p \<le> x" using xin al szb
            by (rule intvl_le_lower)
        qed
        thus unx: "unat (x - ptr_val p) < size_td (typ_info_t TYPE('b))" using szb b0
          by (simp add: word_le_nat_alt size_of_def unat_of_nat)

        show "unat (x - ptr_val p) < n - 0 \<or> n - 0 + size_td t \<le> unat (x - ptr_val p)" using xin xni
          unfolding field_lvalue_def field_lookup_offset_eq [OF fl]
          apply -
          apply (erule intvl_cut)
           apply simp
          apply (rule max_size)
          done

        show "wf_fd (typ_info_t TYPE('b))" by (rule wf_fd)
            (* clag *)
        show "length (access_ti (typ_info_t TYPE('a)) v (replicate (size_of TYPE('a)) 0)) = size_td t"
          using wf_fd [where 'a = 'a]
          by (simp add: length_fa_ti size_of_def std)

        show "length (replicate (size_of TYPE('b)) 0) = size_td (typ_info_t TYPE('b))"
          by (simp add: size_of_def)

        have "heap_list hp (size_td (typ_info_t TYPE('b))) (ptr_val p) ! unat (x - ptr_val p) = hp x"
          apply (subst heap_list_nth)
           apply (rule unx)
          apply simp
          done

        thus "access_ti (typ_info_t TYPE('b)) (h_val hp p) (replicate (size_of TYPE('b)) 0) ! unat (x - ptr_val p) = hp x"
          unfolding h_val_def
          by (simp add: from_bytes_def update_ti_t_def size_of_def field_access_update_same(1)[OF td_fafu_idem wf_fd])
      qed
    }
    hence "\<dots> = hp x"
      by (simp add: to_bytes_p_def to_bytes_def update_ti_update_ti_t length_fa_ti [OF wf_fd] std size_of_def)
    finally show "hp x = ?RHS" by simp
  qed
  finally show "?LHS = ?RHS" .
qed

end
