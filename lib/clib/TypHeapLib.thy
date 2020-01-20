(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory TypHeapLib
imports "CParser.CTranslation"
begin

(* This file contains everything you need to know and use for the
   day-to-day solving of TypHeap related goals.  See KernelState.thy for
   abbreviations for cslift etc. *)

section "Abbreviations and helpers"

(* The idea here is to make sure that all abbreviations have defs that let you know they are an abbrev. *)
definition "is_an_abbreviation \<equiv> True"

(* specialised to c_guard *)
abbreviation
  "clift \<equiv> lift_t c_guard"

lemma clift_def: "is_an_abbreviation" by (simp add: is_an_abbreviation_def)

lemma field_ti_field_lookupE:
  "\<lbrakk> field_ti TYPE('a :: c_type) f = Some t; \<And>n. \<lbrakk>field_lookup (typ_info_t TYPE('a)) f 0 = Some (t, n) \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  unfolding field_ti_def
  by (clarsimp split: option.splits)

section "Basic operations"

subsection "clift"

lemma c_guard_clift:
  "clift hp p = Some x \<Longrightarrow> c_guard p"
  by (rule lift_t_g)

lemma clift_heap_update:
  fixes p :: "'a :: mem_type ptr"
  shows "hrs_htd hp \<Turnstile>\<^sub>t p \<Longrightarrow> clift (hrs_mem_update (heap_update p v) hp) = clift hp(p \<mapsto> v)"
  unfolding hrs_mem_update_def
  apply (cases hp)
  apply (simp add: split_def hrs_htd_def)
  apply (erule lift_t_heap_update)
  done

lemma clift_heap_update_same:
  fixes p :: "'a :: mem_type ptr"
  shows "\<lbrakk> hrs_htd hp \<Turnstile>\<^sub>t p; typ_uinfo_t TYPE('a) \<bottom>\<^sub>t typ_uinfo_t TYPE('b) \<rbrakk>
  \<Longrightarrow> clift (hrs_mem_update (heap_update p v) hp) = (clift hp :: 'b :: mem_type typ_heap)"
  unfolding hrs_mem_update_def
  apply (cases hp)
  apply (simp add: split_def hrs_htd_def)
  apply (erule lift_t_heap_update_same)
  apply simp
  done

lemmas clift_heap_update_same_td_name = clift_heap_update_same [OF _  tag_disj_via_td_name, unfolded pad_typ_name_def]

subsection "h_val"

lemmas h_val_clift = lift_t_lift [where g = c_guard, unfolded CTypesDefs.lift_def, simplified]
lemma h_val_clift':
  "clift hp p = Some v \<Longrightarrow> h_val (hrs_mem hp) p = v"
  unfolding hrs_mem_def by (cases hp, simp add: h_val_clift)

subsection "h_t_valid"

lemma clift_Some_eq_valid:
  "(\<exists>v. clift hp p = Some v) = (hrs_htd hp \<Turnstile>\<^sub>t p)"
  apply (cases hp)
  apply (simp add: lift_t_if hrs_htd_def)
  done

lemma h_t_valid_clift_Some_iff:
  "(hrs_htd hp \<Turnstile>\<^sub>t p) = (\<exists>v. clift hp p = Some v)"
  apply (cases hp)
  apply (simp add: lift_t_if hrs_htd_def)
  done

lemma h_t_valid_clift:
  "clift hp p = Some v \<Longrightarrow> hrs_htd hp \<Turnstile>\<^sub>t p"
  apply (cases hp, simp add: hrs_htd_def)
  apply (erule lift_t_h_t_valid)
  done

lemma c_guard_h_t_valid:
  "hrs_htd hp \<Turnstile>\<^sub>t p \<Longrightarrow> c_guard p"
  by (simp add: h_t_valid_def)

section "field_lvalue"
(* field_lvalue is the name of &(p\<rightarrow>f) *)

subsection "heap_update"

lemma heap_update_field:
  "\<lbrakk>field_ti TYPE('a :: packed_type) f = Some t; c_guard p;
  export_uinfo t = export_uinfo (typ_info_t TYPE('b :: packed_type))\<rbrakk>
  \<Longrightarrow> heap_update (Ptr &(p\<rightarrow>f) :: 'b ptr) v hp =
  heap_update p (update_ti t (to_bytes_p v) (h_val hp p)) hp"
  apply (erule field_ti_field_lookupE)
  apply (erule (2) packed_heap_super_field_update [unfolded typ_uinfo_t_def])
  done

lemma heap_update_field':
  "\<lbrakk>field_ti TYPE('a :: packed_type) f = Some t; c_guard p;
  export_uinfo t = export_uinfo (typ_info_t TYPE('b :: packed_type))\<rbrakk>
  \<Longrightarrow> heap_update (Ptr &(p\<rightarrow>f) :: 'b ptr) v hp =
  heap_update p (update_ti_t t (to_bytes_p v) (h_val hp p)) hp"
  apply (erule field_ti_field_lookupE)
  apply (subst packed_heap_super_field_update [unfolded typ_uinfo_t_def])
     apply assumption+
  apply (drule export_size_of [simplified typ_uinfo_t_def])
  apply (simp add: update_ti_t_def)
  done

lemma heap_update_field_hrs:
  fixes p :: "'a :: packed_type ptr" and v :: "'b :: packed_type"
  shows "\<lbrakk>field_ti TYPE('a) f = Some t; c_guard p;
    export_uinfo t = export_uinfo (typ_info_t TYPE('b))\<rbrakk>
  \<Longrightarrow> hrs_mem_update (heap_update (Ptr &(p\<rightarrow>f)) v) hp =
    hrs_mem_update (heap_update p (update_ti_t t (to_bytes_p v) (h_val (hrs_mem hp) p))) hp"
  unfolding hrs_mem_update_def
  apply (simp add: split_def)
  apply (subst heap_update_field)
     apply assumption
    apply assumption
   apply assumption
  apply (frule export_size_of [unfolded typ_uinfo_t_def])
  apply (simp add: update_ti_t_def hrs_mem_def)
  done

lemma heap_update_field_ext:
  "\<lbrakk>field_ti TYPE('a :: packed_type) f = Some t; c_guard p;
  export_uinfo t = export_uinfo (typ_info_t TYPE('b :: packed_type))\<rbrakk>
  \<Longrightarrow> heap_update (Ptr &(p\<rightarrow>f) :: 'b ptr) =
  (\<lambda>v hp. heap_update p (update_ti t (to_bytes_p v) (h_val hp p)) hp)"
  apply (rule ext, rule ext)
  apply (erule (2) heap_update_field)
  done

subsection "c_guard"

lemma c_guard_field:
  "\<lbrakk>c_guard (p :: 'a :: mem_type ptr); field_ti TYPE('a :: mem_type) f = Some t;
  export_uinfo t = export_uinfo (typ_info_t TYPE('b :: mem_type))\<rbrakk>
  \<Longrightarrow> c_guard (Ptr &(p\<rightarrow>f) :: 'b :: mem_type ptr)"
  apply (erule field_ti_field_lookupE)
  apply (erule (1) c_guard_field_lvalue)
   apply (simp add: typ_uinfo_t_def)
   done

subsection "clift"

lemma clift_field:
  fixes v :: "'a :: mem_type" and p :: "'a :: mem_type ptr"
  assumes lf: "clift hp p = Some v"
  and     fl: "field_ti TYPE('a) f = Some t"
  and     eu: "export_uinfo t = export_uinfo (typ_info_t TYPE('b  :: mem_type))"
  shows   "clift hp (Ptr &(p\<rightarrow>f) :: 'b :: mem_type ptr) = Some (from_bytes (access_ti\<^sub>0 t v))"
  using lf fl eu
  apply (clarsimp elim!: field_ti_field_lookupE)
  apply (erule (2) lift_t_mono [unfolded typ_uinfo_t_def])
  apply (rule c_guard_mono)
  done

subsubsection "Updates"

lemma clift_field_update:
  fixes val :: "'b :: mem_type" and ptr :: "'a :: mem_type ptr"
  assumes   fl: "field_ti TYPE('a) f = Some t"
  and       eu: "export_uinfo t = export_uinfo (typ_info_t TYPE('b))"
  and       cl: "clift hp ptr = Some z"
  shows "(clift (hrs_mem_update (heap_update (Ptr &(ptr\<rightarrow>f)) val) hp)) =
  clift hp(ptr \<mapsto> field_update (field_desc t) (to_bytes_p val) z)"
  (is "?LHS = ?RHS")
proof -
  have cl': "clift (fst hp, snd hp) ptr = Some z" using cl by simp

  have "?LHS = super_field_update_t (Ptr &(ptr\<rightarrow>f)) val (clift (fst hp, snd hp))"
    unfolding hrs_mem_update_def split_def
  proof (rule lift_t_super_field_update [OF h_t_valid_sub, unfolded typ_uinfo_t_def])
    from cl' show "snd hp \<Turnstile>\<^sub>t ptr" by (rule lift_t_h_t_valid)
    show "TYPE('b) \<le>\<^sub>\<tau> TYPE('a)" using fl eu by (rule field_ti_sub_typ [unfolded typ_uinfo_t_def])
  qed fact+

  also have "\<dots> = ?RHS" using fl eu cl
    apply -
    apply (erule field_ti_field_lookupE)
    apply (subst super_field_update_lookup [unfolded typ_uinfo_t_def])
    apply assumption
    apply simp
    apply simp
    apply simp
    done

  finally show ?thesis .
qed

subsection "cparent"
(* cparent gives the address of the outerlying structure.  It is equivalent to the c expression
   ptr - offset_of field
*)

definition
  cparent :: "('a :: c_type) ptr \<Rightarrow> string list \<Rightarrow> ('b :: c_type) ptr"
  where
  "cparent p fs \<equiv> THE p'. p = Ptr &(p'\<rightarrow>fs)"

lemma cparent_field [simp]:
  "cparent (Ptr &(p\<rightarrow>fs)) fs = p"
  unfolding cparent_def
  by (simp add: field_lvalue_def)

lemma cparent_def2:
  fixes p :: "'b :: c_type ptr"
  shows "cparent p f \<equiv> (Ptr (ptr_val p - of_nat (field_offset TYPE('a :: c_type) f)) :: 'a :: c_type ptr)"
  (is "cparent p f \<equiv> ?p'")
proof -
  have pv: "p = Ptr &(?p'\<rightarrow>f)"
    by (simp add: field_lvalue_def field_simps)
  show "cparent p f \<equiv> ?p'"
    by (subst pv) simp
qed

lemma field_cparent [simp]:
  fixes p :: "'a :: c_type ptr"
  shows "(Ptr &(cparent p f :: 'b :: c_type ptr \<rightarrow>f)) = p"
  by (simp add: cparent_def2 field_lvalue_def)

(* If we know the value at the parent, we can derive the value at the field *)
lemma clift_cparentE:
  fixes v :: "'a :: mem_type" and p :: "'b :: mem_type ptr"
  assumes lf: "clift hp (cparent p fs :: 'a ptr) = Some v"
  and     fl: "field_ti TYPE('a) fs = Some t"
  and     eu: "export_uinfo t = export_uinfo (typ_info_t TYPE('b))"
  shows   "clift hp p = Some (from_bytes (access_ti\<^sub>0 t v))"
  unfolding cparent_def
proof -
  have pv: "p = Ptr &((Ptr (ptr_val p - of_nat (field_offset TYPE('a) fs)) :: 'a ptr)\<rightarrow>fs)"
    (is "p = Ptr &(?p'\<rightarrow>fs)") by (simp add: field_lvalue_def field_simps)
  have cp: "cparent p fs = ?p'"
    by (subst pv) simp

  from lf have lf': "clift hp ?p' = Some v"
    by (simp add: cparent_def2)

  have "clift hp (Ptr &(?p'\<rightarrow>fs) :: 'b ptr) = Some (from_bytes (access_ti\<^sub>0 t v))" using lf' fl eu
    by (rule clift_field)

  thus ?thesis
    by (simp add: pv [symmetric])
qed

lemma heap_update_to_cparent:
  fixes p :: "'b :: packed_type ptr" and fs :: "char list list"
  defines "cp \<equiv> cparent p fs :: 'a :: packed_type ptr"
  assumes fl: "field_ti TYPE('a :: packed_type) fs = Some t"
  and     cg: "c_guard cp"
  and     eu: "export_uinfo t = export_uinfo (typ_info_t TYPE('b))"
  shows   "heap_update p v hp = heap_update cp (update_ti t (to_bytes_p v) (h_val hp cp)) hp"
  (is "?LHS = ?RHS")
proof -
  have "?LHS = heap_update (Ptr &(cp\<rightarrow>fs)) v hp"
    unfolding cp_def by simp

  moreover have "\<dots> = ?RHS" using fl cg eu
    by (fastforce intro: heap_update_field)

  finally show ?thesis .
qed

lemma c_guard_cparent:
 "\<lbrakk> c_guard ((cparent p f)::'a::mem_type ptr);
    field_ti TYPE('a) f = Some t;
    export_uinfo t = typ_uinfo_t TYPE('b) \<rbrakk> \<Longrightarrow>
  c_guard (p::'b::mem_type ptr)"
 apply(subst field_cparent[symmetric, where f=f])
 apply(rule c_guard_field, (simp add:typ_uinfo_t_def)+)
done

lemma parent_update_child:
 fixes p::"'b::packed_type ptr"
 shows
 "\<lbrakk> c_guard ((cparent p f)::'a::packed_type ptr); field_ti TYPE('a) f = Some t;
   export_uinfo t = export_uinfo (typ_info_t TYPE('b))\<rbrakk>
\<Longrightarrow> hrs_mem_update (heap_update p v) hp =
   hrs_mem_update
    (heap_update ((cparent p f)::'a ptr)
      (update_ti_t t (to_bytes_p v) (h_val (hrs_mem hp) (cparent p f))))
    hp"
 apply(subst field_cparent[symmetric, where f=f and 'b='a])
 apply(rule heap_update_field_hrs, simp+)
done

subsection "h_val"
(* h_val looks up the heap to construct a value of the desired type (Used to be CTypeDefs.lift) *)

lemma h_val_field_clift:
  fixes pa :: "'a :: mem_type ptr"
  assumes cl: "clift (h, d) pa = Some v"
  and     fl: "field_ti TYPE('a) f = Some t"
  and     eu: "export_uinfo t = export_uinfo (typ_info_t TYPE('b :: mem_type))"
  shows   "h_val h (Ptr &(pa\<rightarrow>f) :: 'b :: mem_type ptr) = from_bytes (access_ti\<^sub>0 t v)"
  using cl fl eu
  apply -
  apply (rule h_val_clift)
  apply (clarsimp simp: field_ti_def split: option.splits)
  apply (erule (2) lift_t_mono [unfolded typ_uinfo_t_def])
  apply (rule c_guard_mono)
  done

lemma h_val_field_clift':
  fixes pa :: "'a :: mem_type ptr"
  assumes cl: "clift hp pa = Some v"
  and     fl: "field_ti TYPE('a) f = Some t"
  and     eu: "export_uinfo t = export_uinfo (typ_info_t TYPE('b :: mem_type))"
  shows   "h_val (hrs_mem hp) (Ptr &(pa\<rightarrow>f) :: 'b :: mem_type ptr) = from_bytes (access_ti\<^sub>0 t v)"
  using cl fl eu
  apply (cases hp)
  apply (simp add: h_val_field_clift hrs_mem_def)
  done

lemma clift_subtype:
  "\<lbrakk> clift hp ((cparent p f)::'a::mem_type ptr) = Some v;
     field_ti TYPE('a) f = Some t;
     export_uinfo t = export_uinfo (typ_info_t TYPE('b::mem_type)) \<rbrakk> \<Longrightarrow>
   clift hp (p::'b ptr) = Some (from_bytes (access_ti\<^sub>0 t v))"
 apply(subst field_cparent[symmetric, where f=f])
 apply(rule clift_field)
   apply(simp)+
done

subsection "h_t_valid"

lemma h_t_valid_field:
  fixes p :: "'a :: mem_type ptr"
  assumes htv: "d \<Turnstile>\<^sub>t p"
  and     fti: "field_ti TYPE('a :: mem_type) f = Some t"
  and      eu: "export_uinfo t = export_uinfo (typ_info_t TYPE('b :: mem_type))"
  shows    "d \<Turnstile>\<^sub>t (Ptr &(p\<rightarrow>f) :: 'b :: mem_type ptr)"
  using htv fti eu
  apply -
  apply (clarsimp simp: field_ti_def split: option.splits)
  apply (erule (1) h_t_valid_mono [rule_format, unfolded typ_uinfo_t_def])
   apply (rule c_guard_mono)
  apply assumption
  done

lemma h_t_valid_guard_subst:
  "\<lbrakk> d,g \<Turnstile>\<^sub>t p; g' p \<rbrakk> \<Longrightarrow> d,g' \<Turnstile>\<^sub>t p"
 apply(simp add:h_t_valid_def)
done

lemma h_t_valid_field':
  fixes p::"'a::mem_type ptr"
  shows
  "\<lbrakk> field_ti TYPE('a) f = Some t;
     export_uinfo t = typ_uinfo_t TYPE('b);
     d,g \<Turnstile>\<^sub>t p; g' ((Ptr &(p\<rightarrow>f))::'b::mem_type ptr) \<rbrakk> \<Longrightarrow> d,g' \<Turnstile>\<^sub>t Ptr &(p\<rightarrow>f)"
 apply(simp add:h_t_valid_guard_subst[OF h_t_valid_sub])
done

lemma h_t_valid_c_guard_field:
  fixes p::"'a::mem_type ptr"
  shows
  "\<lbrakk> d \<Turnstile>\<^sub>t p;
     field_ti TYPE('a) f = Some t;
     export_uinfo t = typ_uinfo_t TYPE('b) \<rbrakk> \<Longrightarrow>
   d \<Turnstile>\<^sub>t ((Ptr &(p\<rightarrow>f))::'b::mem_type ptr)"
 apply(simp add:h_t_valid_field c_guard_field h_t_valid_c_guard typ_uinfo_t_def)
done

lemma h_t_valid_cparent:
 "\<lbrakk> field_ti TYPE('a) f = Some t;
    export_uinfo t = typ_uinfo_t TYPE('b);
    d,g \<Turnstile>\<^sub>t ((cparent p f)::'a::mem_type ptr); g' (p::'b::mem_type ptr) \<rbrakk> \<Longrightarrow>
  d,g' \<Turnstile>\<^sub>t p"
 apply(subst field_cparent[symmetric, where f=f])
 apply(rule h_t_valid_field')
    apply(assumption)
   apply(simp add:typ_uinfo_t_def)
  apply(assumption)
 apply(simp)
done

lemma h_t_valid_c_guard_cparent:
 fixes p::"'b::mem_type ptr"
 shows
 "\<lbrakk> d \<Turnstile>\<^sub>t ((cparent p f)::'a::mem_type ptr);
    field_ti TYPE('a) f = Some t;
    export_uinfo t = typ_uinfo_t TYPE('b) \<rbrakk> \<Longrightarrow>
  d \<Turnstile>\<^sub>t p"
 apply(rule h_t_valid_cparent)
    apply(assumption)
   apply(simp add:typ_uinfo_t_def)
  apply(assumption)
 apply(rule c_guard_cparent)
   apply(rule h_t_valid_c_guard, assumption)
  apply(assumption)
 apply(simp add:typ_uinfo_t_def)
done

lemma c_guard_array_c_guard:
  "c_guard (ptr_coerce p :: ('b :: c_type, 'a :: finite) array ptr) \<Longrightarrow> c_guard (p :: 'b ptr)"
  apply (clarsimp simp: c_guard_def)
  apply (rule conjI)
   apply (clarsimp simp: ptr_aligned_def align_of_def align_td_array)
  apply (simp add: c_null_guard_def)
  apply (erule contra_subsetD [rotated])
  apply (rule intvl_start_le)
  apply simp
  done

lemma c_guard_array_field:
  assumes parent_cguard: "c_guard (p :: 'a :: mem_type ptr)"
  and subfield: "field_ti TYPE('a :: mem_type) f = Some t"
  and type_match: "export_uinfo t = export_uinfo (typ_info_t TYPE(('b :: array_outer_max_size, 'c :: array_max_count) array))"
  shows "c_guard (Ptr &(p\<rightarrow>f) :: 'b ptr)"
  by (metis c_guard_array_c_guard c_guard_field parent_cguard ptr_coerce.simps subfield type_match)

instantiation ptr :: (type) enum
begin

  definition "enum_ptr \<equiv> map Ptr enum_class.enum"
  definition "enum_all_ptr P \<equiv> enum_class.enum_all (\<lambda>v. P (Ptr v))"
  definition "enum_ex_ptr P \<equiv> enum_class.enum_ex (\<lambda>v. P (Ptr v))"

  instance
    apply (intro_classes)
       apply (clarsimp simp: enum_ptr_def)
       apply (metis ptr.exhaust surj_def)
      apply (clarsimp simp: enum_ptr_def distinct_map)
      apply (metis injI ptr.inject)
     apply (clarsimp simp: enum_all_ptr_def)
     apply (rule iffI)
      apply (rule allI)
      apply (erule_tac x="ptr_val x" in allE)
      apply force
     apply force
    apply (clarsimp simp: enum_ex_ptr_def)
    apply (rule iffI)
     apply force
    apply clarsimp
    apply (rule_tac x="ptr_val x" in exI)
    apply clarsimp
    done
end

subsection \<open>Type Combinators and Padding\<close>

lemma ti_typ_pad_combine_empty_ti:
  fixes tp :: "'b :: c_type itself"
  shows "ti_typ_pad_combine tp lu upd fld (empty_typ_info n) =
  TypDesc (TypAggregate [DTPair (adjust_ti (typ_info_t TYPE('b)) lu upd) fld]) n"
  by (simp add: ti_typ_pad_combine_def ti_typ_combine_def empty_typ_info_def Let_def)

lemma ti_typ_combine_empty_ti:
  fixes tp :: "'b :: c_type itself"
  shows "ti_typ_combine tp lu upd fld (empty_typ_info n) =
  TypDesc (TypAggregate [DTPair (adjust_ti (typ_info_t TYPE('b)) lu upd) fld]) n"
  by (simp add: ti_typ_combine_def empty_typ_info_def Let_def)

lemma ti_typ_pad_combine_td:
  fixes tp :: "'b :: c_type itself"
  shows "padup (align_of TYPE('b)) (size_td_struct st) = 0 \<Longrightarrow>
  ti_typ_pad_combine tp lu upd fld (TypDesc st n) =
  TypDesc (extend_ti_struct st (adjust_ti (typ_info_t TYPE('b)) lu upd) fld) n"
  by (simp add: ti_typ_pad_combine_def ti_typ_combine_def Let_def)

lemma ti_typ_combine_td:
  fixes tp :: "'b :: c_type itself"
  shows "padup (align_of TYPE('b)) (size_td_struct st) = 0 \<Longrightarrow>
  ti_typ_combine tp lu upd fld (TypDesc st n) =
  TypDesc (extend_ti_struct st (adjust_ti (typ_info_t TYPE('b)) lu upd) fld) n"
  by (simp add: ti_typ_combine_def Let_def)

lemma update_ti_t_pad_combine:
  assumes std: "size_td td' mod 2 ^ align_td (typ_info_t TYPE('a :: c_type)) = 0"
  shows "update_ti_t (ti_typ_pad_combine TYPE('a :: c_type) lu upd fld td') bs v =
  update_ti_t (ti_typ_combine TYPE('a :: c_type) lu upd fld td') bs v"
  using std
  by (simp add: ti_typ_pad_combine_def size_td_simps Let_def)

subsection \<open>
  The orphanage: miscellaneous lemmas pulled up to (roughly) where they belong.
\<close>

lemma uinfo_array_tag_n_m_not_le_typ_name:
  "typ_name (typ_info_t TYPE('b)) @ ''_array_'' @ nat_to_bin_string m
      \<notin> td_names (typ_info_t TYPE('a))
    \<Longrightarrow> \<not> uinfo_array_tag_n_m TYPE('b :: c_type) n m \<le> typ_uinfo_t TYPE('a :: c_type)"
  apply (clarsimp simp: typ_tag_le_def typ_uinfo_t_def)
  apply (drule td_set_td_names)
   apply (clarsimp simp: uinfo_array_tag_n_m_def typ_uinfo_t_def)
   apply (drule arg_cong[where f="\<lambda>xs. set ''r'' \<subseteq> set xs"], simp)
  apply (simp add: uinfo_array_tag_n_m_def typ_uinfo_t_def)
  done

lemma tag_not_le_via_td_name:
  "typ_name (typ_info_t TYPE('a)) \<notin> td_names (typ_info_t TYPE('b))
    \<Longrightarrow> typ_name (typ_info_t TYPE('a)) \<noteq> pad_typ_name
    \<Longrightarrow> \<not> typ_uinfo_t TYPE('a :: c_type) \<le> typ_uinfo_t TYPE ('b :: c_type)"
  apply (clarsimp simp: typ_tag_le_def typ_uinfo_t_def)
  apply (drule td_set_td_names, simp+)
  done

(* Simplifier setup *)

(* Basic idea:
    - Try to stay at highest level, i.e., c_guard, then ptr_valid, then clift
    - remove all field references.
    - try the less costly clift_update

*)

lemmas typ_heap_simps =
  \<comment> \<open>c_guard\<close>
  c_guard_field
  c_guard_h_t_valid
  \<comment> \<open>h_t_valid\<close>
  h_t_valid_field
  h_t_valid_clift
  \<comment> \<open>h_val\<close>
  h_val_field_clift'
  h_val_clift'
  \<comment> \<open>clift\<close>
  clift_field
  clift_field_update
  heap_update_field_hrs
  heap_update_field'
  clift_heap_update
  clift_heap_update_same_td_name \<comment> \<open>Try this last (is expensive)\<close>

end
