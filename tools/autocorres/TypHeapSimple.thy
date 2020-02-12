(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(*
 * This file contains theorems for dealing with a "simply" lifted
 * heap, where each byte of memory can be accessed as one (and only)
 * type.
 *
 * This is a simpler model of Tuch's "lift_t" model, where nested
 * struct fields cannot be directly accessed as pointers.
 *)

theory TypHeapSimple
imports
  "CLib.TypHeapLib"
begin

(*
 * Each address in the heap can contain one of three things:
 *
 *   - A type tag, which inidicates that this address is the first
 *     byte of an object;
 *
 *   - A footprint, which indicates that this address is a latter byte
 *     of an object;
 *
 *   - Nothing, which indicates that this address does not fall inside
 *     an object.
 *)
datatype heap_typ_contents =
    HeapType typ_uinfo
  | HeapFootprint
  | HeapEmpty

(*
 * Given a Tuch-style heap representation (where each memory location
 * contains a set of different types, representing nested field types)
 * calculate a single top-level type of the heap.
 *
 * We just want to commit to a single type for this heap location,
 * and nothing more.
 *)
definition
  heap_type_tag :: "heap_typ_desc \<Rightarrow> addr \<Rightarrow> heap_typ_contents"
where
  "heap_type_tag d a \<equiv>
     (if fst (d a) = False \<or> (\<forall>x. (snd (d a)) x = None) \<or> (\<forall>x. (snd (d a)) x \<noteq> None) then
       HeapEmpty
     else
       case (snd (d a)) (GREATEST x. snd (d a) x \<noteq> None) of
         Some (_, False) \<Rightarrow> HeapFootprint
       | Some (x, True) \<Rightarrow> HeapType x
       | None \<Rightarrow> HeapEmpty)"

(*
 * Determine if the heap has a valid footprint for the given type at
 * the given address.
 *
 * A valid footprint means that the user has committed that the given
 * memory location will only be used for the given type.
 *
 * A "simple" footprint differs from the Tuch-style because we only
 * commit to a single type, and have no support for accessing nested
 * structures.
 *)
definition
  valid_simple_footprint :: "heap_typ_desc \<Rightarrow> addr \<Rightarrow> typ_uinfo \<Rightarrow> bool"
where
  "valid_simple_footprint d x t \<equiv>
    heap_type_tag d x = HeapType t \<and>
      (\<forall>y. y \<in> {x + 1..+  (size_td t)- Suc 0} \<longrightarrow> heap_type_tag d y = HeapFootprint)"

lemma valid_simple_footprintI:
  "\<lbrakk> heap_type_tag d x = HeapType t; \<And>y. y \<in> {x + 1..+(size_td t) - Suc 0} \<Longrightarrow> heap_type_tag d y = HeapFootprint \<rbrakk>
      \<Longrightarrow> valid_simple_footprint d x t"
  by (clarsimp simp: valid_simple_footprint_def)

lemma valid_simple_footprintD:
  "valid_simple_footprint d x t \<Longrightarrow> heap_type_tag d x = HeapType t"
  by (simp add: valid_simple_footprint_def)

lemma valid_simple_footprintD2:
  "\<lbrakk> valid_simple_footprint d x t; y \<in> {x + 1..+(size_td t) - Suc 0} \<rbrakk> \<Longrightarrow> heap_type_tag d y = HeapFootprint"
  by (simp add: valid_simple_footprint_def)

lemma typ_slices_not_empty:
    "typ_slices (x::('a::{mem_type} itself)) \<noteq> []"
  apply (clarsimp simp: typ_slices_def)
  done

lemma last_typ_slice_t:
    "(last (typ_slice_t t 0)) = (t, True)"
  apply (case_tac t)
  apply clarsimp
  done

lemma if_eqI:
 "\<lbrakk> a \<Longrightarrow> x = z; \<not> a \<Longrightarrow> y = z \<rbrakk> \<Longrightarrow> (if a then x else y) = z"
  by simp

lemma heap_type_tag_ptr_retyp:
    "snd (s (ptr_val t)) = Map.empty \<Longrightarrow>
        heap_type_tag (ptr_retyp (t :: 'a::mem_type ptr) s) (ptr_val t) = HeapType (typ_uinfo_t TYPE('a))"
  apply (unfold ptr_retyp_def heap_type_tag_def)
  apply (subst htd_update_list_index, fastforce, fastforce)+
  apply (rule if_eqI)
   apply clarsimp
   apply (erule disjE)
    apply (erule_tac x=0 in allE)
    apply clarsimp
   apply (erule_tac x="length (typ_slice_t (typ_uinfo_t TYPE('a)) 0)" in allE)
   apply (clarsimp simp: list_map_eq)
  apply (clarsimp simp: list_map_eq last_conv_nth [simplified, symmetric] last_typ_slice_t
            split: option.splits if_split_asm prod.splits)
  done

lemma not_snd_last_typ_slice_t:
    "k \<noteq> 0 \<Longrightarrow> \<not> snd (last (typ_slice_t z k))"
  by (case_tac z, clarsimp)

lemma heap_type_tag_ptr_retyp_rest:
    "\<lbrakk> snd (s (ptr_val t + k)) = Map.empty; 0 < k; unat k < size_td (typ_uinfo_t TYPE('a)) \<rbrakk> \<Longrightarrow>
        heap_type_tag (ptr_retyp (t :: 'a::mem_type ptr) s) (ptr_val t + k) = HeapFootprint"
  apply (unfold ptr_retyp_def heap_type_tag_def)
  apply (subst htd_update_list_index, simp, clarsimp,
      metis intvlI size_of_def word_unat.Rep_inverse)+
  apply (rule if_eqI)
   apply clarsimp
   apply (erule disjE)
    apply (erule_tac x=0 in allE)
    apply (clarsimp simp: size_of_def)
   apply (erule_tac x="length (typ_slice_t (typ_uinfo_t TYPE('a)) (unat k))" in allE)
   apply (clarsimp simp: size_of_def list_map_eq)
  apply (clarsimp simp: list_map_eq last_conv_nth [simplified, symmetric] size_of_def
      split: option.splits if_split_asm prod.splits bool.splits)
   apply (metis surj_pair)
  apply (subst (asm) (2) surjective_pairing)
  apply (subst (asm) not_snd_last_typ_slice_t)
   apply clarsimp
   apply unat_arith
  apply simp
  done

lemma typ_slices_addr_card [simp]:
    "length (typ_slices (x::('a::{mem_type} itself))) < addr_card"
  apply (clarsimp simp: typ_slices_def)
  done

lemma htd_update_list_same':
  "\<lbrakk>0 < unat k; unat k \<le> addr_card - length v\<rbrakk> \<Longrightarrow> htd_update_list (p + k) v h p = h p"
  apply (insert htd_update_list_same [where v=v and p=p and h=h and k="unat k"])
  apply clarsimp
  done

lemma unat_less_impl_less:
    "unat a < unat b \<Longrightarrow> a < b"
  by unat_arith

lemma valid_simple_footprint_ptr_retyp:
    "\<lbrakk> \<forall>k < size_td (typ_uinfo_t TYPE('a)). snd (s (ptr_val t + of_nat k)) = Map.empty;
        1 \<le> size_td (typ_uinfo_t TYPE('a));
        size_td (typ_uinfo_t TYPE('a)) < addr_card \<rbrakk>
        \<Longrightarrow> valid_simple_footprint (ptr_retyp (t :: 'a::mem_type ptr) s) (ptr_val t) (typ_uinfo_t TYPE('a))"
  apply (clarsimp simp: valid_simple_footprint_def)
  apply (rule conjI)
   apply (subst heap_type_tag_ptr_retyp)
    apply (erule allE [where x="0"])
    apply clarsimp
   apply clarsimp
  apply (clarsimp simp: intvl_def)
  apply (erule_tac x="k + 1" in allE)
  apply (erule impE)
   apply (metis One_nat_def less_diff_conv)
  apply (subst add.assoc, subst heap_type_tag_ptr_retyp_rest)
     apply clarsimp
    apply (case_tac "1 + of_nat k = (0 :: addr)")
     apply (metis add.left_neutral intvlI intvl_Suc_nmem size_of_def)
    apply unat_arith
   apply clarsimp
   apply (metis lt_size_of_unat_simps size_of_def Suc_eq_plus1 One_nat_def less_diff_conv of_nat_Suc)
  apply simp
  done

(* Determine if the given pointer is valid in the given heap. *)
definition
  heap_ptr_valid :: "heap_typ_desc \<Rightarrow> 'a::c_type ptr \<Rightarrow> bool"
where
  "heap_ptr_valid d p \<equiv>
      valid_simple_footprint d (ptr_val (p::'a ptr)) (typ_uinfo_t TYPE('a))
        \<and> c_guard p"

(*
 * Lift a heap from raw bytes and a heap description into
 * higher-level objects.
 *
 * This differs from Tuch's "lift_t" because we only support
 * simple lifting; that is, each byte in the heap may only
 * be accessed as a single type. Accessing struct fields by
 * their pointers is not supported.
 *)
definition
  simple_lift :: "heap_raw_state \<Rightarrow> ('a::c_type) ptr \<Rightarrow> 'a option"
where
  "simple_lift s p = (
     if (heap_ptr_valid (hrs_htd s) p) then
       (Some (h_val (hrs_mem s) p))
     else
       None)"

lemma simple_lift_heap_ptr_valid:
  "simple_lift s p = Some x \<Longrightarrow> heap_ptr_valid (hrs_htd s) p"
  apply (clarsimp simp: simple_lift_def split: if_split_asm)
  done

lemma simple_lift_c_guard:
  "simple_lift s p = Some x \<Longrightarrow> c_guard p"
  apply (clarsimp simp: simple_lift_def heap_ptr_valid_def split: if_split_asm)
  done

(* Two valid footprints will either overlap completely or not at all. *)
lemma valid_simple_footprint_neq:
  assumes valid_p: "valid_simple_footprint d p s"
      and valid_q: "valid_simple_footprint d q t"
      and neq: "p \<noteq> q"
  shows "p \<notin> {q..+ (size_td t)}"
proof -
  have heap_type_p: "heap_type_tag d p = HeapType s"
    apply (metis valid_p valid_simple_footprint_def)
    done

  have heap_type_q: "heap_type_tag d q = HeapType t"
    apply (metis valid_q valid_simple_footprint_def)
    done

  have heap_type_q_footprint:
    "\<And>x. x \<in> {(q + 1)..+(size_td t - Suc 0)} \<Longrightarrow> heap_type_tag d x = HeapFootprint"
    apply (insert valid_q)
    apply (simp add: valid_simple_footprint_def)
    done

  show ?thesis
    using heap_type_q_footprint heap_type_p neq
         intvl_neq_start heap_type_q
    by (metis heap_typ_contents.simps(2))
qed

(* Two valid footprints with different types will never overlap. *)
lemma valid_simple_footprint_type_neq:
  "\<lbrakk> valid_simple_footprint d p s;
     valid_simple_footprint d q t;
     s \<noteq> t \<rbrakk> \<Longrightarrow>
   p \<notin> {q..+ (size_td t)}"
  apply (subgoal_tac "p \<noteq> q")
   apply (rule valid_simple_footprint_neq, simp_all)[1]
  apply (clarsimp simp: valid_simple_footprint_def)
  done

lemma valid_simple_footprint_neq_disjoint:
  "\<lbrakk> valid_simple_footprint d p s; valid_simple_footprint d q t; p \<noteq> q \<rbrakk> \<Longrightarrow>
      {p..+(size_td s)} \<inter> {q..+ (size_td t)} = {}"
  apply (rule ccontr)
  apply (fastforce simp: valid_simple_footprint_neq dest!: intvl_inter)
  done

lemma valid_simple_footprint_type_neq_disjoint:
  "\<lbrakk> valid_simple_footprint d p s;
     valid_simple_footprint d q t;
     s \<noteq> t \<rbrakk> \<Longrightarrow>
   {p..+(size_td s)} \<inter> {q..+ (size_td t)} = {}"
  apply (subgoal_tac "p \<noteq> q")
   apply (rule valid_simple_footprint_neq_disjoint, simp_all)[1]
  apply (clarsimp simp: valid_simple_footprint_def)
  done

lemma heap_ptr_valid_neq_disjoint:
  "\<lbrakk> heap_ptr_valid d (p::'a::c_type ptr);
     heap_ptr_valid d (q::'b::c_type ptr);
     ptr_val p \<noteq> ptr_val q \<rbrakk> \<Longrightarrow>
   {ptr_val p..+size_of TYPE('a)} \<inter>
          {ptr_val q..+size_of TYPE('b)} = {}"
  apply (clarsimp simp only: size_of_tag [symmetric])
  apply (rule valid_simple_footprint_neq_disjoint [where d="d"])
    apply (clarsimp simp: heap_ptr_valid_def)
   apply (clarsimp simp: heap_ptr_valid_def)
  apply simp
  done

lemma heap_ptr_valid_type_neq_disjoint:
  "\<lbrakk> heap_ptr_valid d (p::'a::c_type ptr);
     heap_ptr_valid d (q::'b::c_type ptr);
     typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE('b) \<rbrakk> \<Longrightarrow>
   {ptr_val p..+size_of TYPE('a)} \<inter>
          {ptr_val q..+size_of TYPE('b)} = {}"
  apply (subgoal_tac "ptr_val p \<noteq> ptr_val q")
   apply (rule heap_ptr_valid_neq_disjoint, auto)[1]
  apply (clarsimp simp: heap_ptr_valid_def valid_simple_footprint_def)
  done

(* If we update one pointer in the heap, other valid pointers will be unaffected. *)
lemma heap_ptr_valid_heap_update_other:
  assumes val_p: "heap_ptr_valid d (p::'a::mem_type ptr)"
      and val_q: "heap_ptr_valid d (q::'b::c_type ptr)"
      and neq: "ptr_val p \<noteq> ptr_val q"
  shows "h_val (heap_update p v h) q = h_val h q"
  apply (clarsimp simp: h_val_def heap_update_def)
  apply (subst heap_list_update_disjoint_same)
   apply simp
   apply (rule heap_ptr_valid_neq_disjoint [OF val_p val_q neq])
  apply simp
  done

(* If we update one type in the heap, other types will be unaffected. *)
lemma heap_ptr_valid_heap_update_other_typ:
  assumes val_p: "heap_ptr_valid d (p::'a::mem_type ptr)"
      and val_q: "heap_ptr_valid d (q::'b::c_type ptr)"
      and neq: "typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE('b)"
  shows "h_val (heap_update p v h) q = h_val h q"
  apply (clarsimp simp: h_val_def heap_update_def)
  apply (subst heap_list_update_disjoint_same)
   apply simp
   apply (rule heap_ptr_valid_type_neq_disjoint [OF val_p val_q neq])
  apply simp
  done

(* Updating the raw heap is equivalent to updating the lifted heap. *)
lemma simple_lift_heap_update:
  "\<lbrakk> heap_ptr_valid (hrs_htd h) p \<rbrakk> \<Longrightarrow>
      simple_lift (hrs_mem_update (heap_update p v) h)
          = (simple_lift h)(p := Some (v::'a::mem_type))"
  apply (rule ext)
  apply (clarsimp simp: simple_lift_def hrs_mem_update h_val_heap_update)
  apply (fastforce simp: heap_ptr_valid_heap_update_other)
  done

(* Updating the raw heap of one type doesn't affect the lifted heap of other types. *)
lemma simple_lift_heap_update_other:
  "\<lbrakk> heap_ptr_valid (hrs_htd d) (p::'b::mem_type ptr);
     typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE('b) \<rbrakk> \<Longrightarrow>
   simple_lift (hrs_mem_update (heap_update p v) d) = ((simple_lift d)::'a::c_type typ_heap)"
  apply (rule ext)+
  apply (clarsimp simp: simple_lift_def h_val_heap_update hrs_mem_update)
  apply (auto intro: heap_ptr_valid_heap_update_other_typ)
  done

lemma h_val_simple_lift:
  "simple_lift h p = Some v \<Longrightarrow> h_val (hrs_mem h) p = v"
  apply (clarsimp simp: simple_lift_def split: if_split_asm)
  done

lemma h_val_field_simple_lift:
  "\<lbrakk> simple_lift h (pa :: 'a ptr) = Some (v::'a::mem_type);
     \<exists>t. field_ti TYPE('a) f = Some t;
     export_uinfo (the (field_ti TYPE('a) f)) = export_uinfo (typ_info_t TYPE('b :: mem_type)) \<rbrakk> \<Longrightarrow>
   h_val (hrs_mem h) (Ptr &(pa\<rightarrow>f) :: 'b :: mem_type ptr) = from_bytes (access_ti\<^sub>0 (the (field_ti TYPE('a) f)) v)"
  apply (clarsimp simp: simple_lift_def split: if_split_asm)
  apply (clarsimp simp: h_val_field_from_bytes)
  done

lemma simple_lift_heap_update':
  "simple_lift h p = Some v' \<Longrightarrow>
      simple_lift (hrs_mem_update (heap_update (p::('a::{mem_type}) ptr) v) h)
          = (simple_lift h)(p := Some v)"
  apply (rule simple_lift_heap_update)
  apply (erule simple_lift_heap_ptr_valid)
  done

lemma simple_lift_hrs_mem_update_None [simp]:
    "(simple_lift (hrs_mem_update a hp) x = None) = (simple_lift hp x = None)"
  apply (clarsimp simp: simple_lift_def)
  done

lemma simple_lift_data_eq:
   "\<lbrakk> h_val (hrs_mem h) p = h_val (hrs_mem h') p';
     heap_ptr_valid (hrs_htd h) p = heap_ptr_valid (hrs_htd h') p' \<rbrakk> \<Longrightarrow>
    simple_lift h p = simple_lift h' p'"
  apply (clarsimp simp: simple_lift_def)
  done

lemma h_val_heap_update_disjoint:
  "\<lbrakk> {ptr_val p ..+ size_of TYPE('a::c_type)}
        \<inter> {ptr_val q ..+ size_of TYPE('b::mem_type)} = {} \<rbrakk> \<Longrightarrow>
      h_val (heap_update (q :: 'b ptr) r h) (p :: 'a ptr) = h_val h p"
  apply (clarsimp simp: h_val_def)
  apply (clarsimp simp: heap_update_def)
  apply (subst heap_list_update_disjoint_same)
   apply clarsimp
   apply blast
   apply clarsimp
  done

lemma update_ti_t_valid_size:
  "size_of TYPE('b) = size_td t \<Longrightarrow>
   update_ti_t t (to_bytes_p (val::'b::mem_type)) obj = update_ti t (to_bytes_p val) obj"
  apply (clarsimp simp: update_ti_t_def to_bytes_p_def)
  done

lemma h_val_field_from_bytes':
  "\<lbrakk> field_ti TYPE('a::{mem_type}) f = Some t;
     export_uinfo t = export_uinfo (typ_info_t TYPE('b::{mem_type})) \<rbrakk> \<Longrightarrow>
    h_val h (Ptr &(pa\<rightarrow>f) :: 'b ptr) = from_bytes (access_ti\<^sub>0 t (h_val h pa))"
  apply (insert h_val_field_from_bytes[where f=f and pa=pa and t=t and h="(h,x)"
                                         and 'a='a and 'b='b for x])
  apply (clarsimp simp: hrs_mem_def)
  done

lemma simple_lift_super_field_update_lookup:
  fixes dummy :: "'b :: mem_type"
  assumes "field_lookup (typ_info_t TYPE('b::mem_type)) f 0 = Some (s,n)"
    and "typ_uinfo_t TYPE('a) = export_uinfo s"
    and "simple_lift h p = Some v'"
  shows "(super_field_update_t (Ptr (&(p\<rightarrow>f))) (v::'a::mem_type) ((simple_lift h)::'b ptr \<Rightarrow> 'b option)) =
          ((simple_lift h)(p \<mapsto> field_update (field_desc s) (to_bytes_p v) v'))"
proof -
  from assms have [simp]: "unat (of_nat n :: addr) = n"
     apply (subst unat_of_nat)
     apply (subst mod_less)
      apply (drule td_set_field_lookupD)+
      apply (drule td_set_offset_size)+
      apply (subst len_of_addr_card)
      apply (subst (asm) size_of_def [symmetric, where t="TYPE('b)"])+
      apply (subgoal_tac "size_of TYPE('b) < addr_card")
       apply arith
      apply simp
     apply simp
     done
  from assms show ?thesis
    apply (clarsimp simp: super_field_update_t_def)
    apply (rule ext)
    apply (clarsimp simp: field_lvalue_def split: option.splits)
    apply (safe, simp_all)
       apply (frule_tac v=v and v'=v' in update_field_update)
       apply (clarsimp simp: field_of_t_def field_of_def typ_uinfo_t_def)
       apply (frule_tac m=0 in field_names_SomeD2)
        apply simp
       apply clarsimp
       apply (simp add: field_typ_def field_typ_untyped_def)
       apply (frule field_lookup_export_uinfo_Some)
       apply (frule_tac s=k in field_lookup_export_uinfo_Some)
       apply simp
       apply (drule (1) field_lookup_inject)
        apply (subst typ_uinfo_t_def [symmetric, where t="TYPE('b)"])
        apply simp
       apply simp
      apply (drule field_of_t_mem)+
      apply (case_tac h)
      apply (clarsimp simp: simple_lift_def split: if_split_asm)
      apply (drule (1) heap_ptr_valid_neq_disjoint)
       apply simp
      apply fast
     apply (clarsimp simp: field_of_t_def field_of_def)
     apply (subst (asm) td_set_field_lookup)
      apply simp
     apply simp
     apply (frule field_lookup_export_uinfo_Some)
     apply (simp add: typ_uinfo_t_def)
    apply (clarsimp simp: field_of_t_def field_of_def)
    apply (subst (asm) td_set_field_lookup)
     apply simp
    apply simp
    apply (frule field_lookup_export_uinfo_Some)
    apply (simp add: typ_uinfo_t_def)
    done
qed

lemma field_offset_addr_card:
  "\<exists>x. field_lookup (typ_info_t TYPE('a::mem_type)) f 0 = Some x
    \<Longrightarrow> field_offset TYPE('a) f < addr_card"
  apply (clarsimp simp: field_offset_def field_offset_untyped_def typ_uinfo_t_def)
  apply (subst field_lookup_export_uinfo_Some)
   apply assumption
  apply (frule td_set_field_lookupD)
  apply (drule td_set_offset_size)
  apply (insert max_size [where ?'a="'a"])
  apply (clarsimp simp: size_of_def)
  done

lemma unat_of_nat_field_offset:
  "\<exists>x. field_lookup (typ_info_t TYPE('a::mem_type)) f 0 = Some x \<Longrightarrow>
      unat (of_nat (field_offset TYPE('a) f)  :: addr) = field_offset TYPE('a) f"
  apply (subst word_unat.Abs_inverse)
   apply (clarsimp simp: unats_def)
   apply (insert field_offset_addr_card [where f=f and ?'a="'a"])[1]
   apply (fastforce simp: addr_card)
  apply simp
  done

lemma field_of_t_field_lookup:
  assumes a: "field_lookup (typ_info_t TYPE('a::mem_type)) f 0 = Some (s, n)"
  assumes b: "export_uinfo s = typ_uinfo_t TYPE('b::mem_type)"
  assumes n: "n = field_offset TYPE('a) f"
  shows "field_of_t (Ptr &(ptr\<rightarrow>f) :: ('b ptr)) (ptr :: 'a ptr)"
  apply (clarsimp simp del: field_lookup_offset_eq
      simp: field_of_t_def field_of_def)
  apply (subst td_set_field_lookup)
   apply (rule wf_desc_typ_tag)
  apply (rule exI [where x=f])
  using a[simplified n] b
  apply (clarsimp simp: typ_uinfo_t_def)
  apply (subst field_lookup_export_uinfo_Some)
   apply assumption
  apply (clarsimp simp del: field_lookup_offset_eq
      simp: field_lvalue_def unat_of_nat_field_offset)
  done

lemma simple_lift_field_update':
  fixes val :: "'b :: mem_type" and ptr :: "'a :: mem_type ptr"
  assumes   fl: "field_lookup (typ_info_t TYPE('a)) f 0 =
                     Some (adjust_ti (typ_info_t TYPE('b)) xf xfu, n)"
  and   xf_xfu: "fg_cons xf xfu"
  and       cl: "simple_lift hp ptr = Some z"
  shows "(simple_lift (hrs_mem_update (heap_update (Ptr &(ptr\<rightarrow>f)) val) hp)) =
                simple_lift hp(ptr \<mapsto> xfu val z)"
    (is "?LHS = ?RHS")
proof (rule ext)
  fix p

  have eui: "typ_uinfo_t TYPE('b) =
       export_uinfo (adjust_ti (typ_info_t TYPE('b)) xf xfu)"
    using xf_xfu
    apply (subst export_tag_adjust_ti2 [OF _ wf_lf wf_desc])
    apply (simp add: fg_cons_def )
    apply (rule meta_eq_to_obj_eq [OF typ_uinfo_t_def])
    done

  have n_is_field_offset: "n = field_offset TYPE('a) f"
    apply (insert field_lookup_offset_eq [OF fl])
    apply (clarsimp)
    done

  have equal_case: "?LHS ptr = ?RHS ptr"
    apply (insert cl)
    apply (clarsimp simp: simple_lift_def split: if_split_asm)
    apply (clarsimp simp: hrs_mem_update)
    apply (subst h_val_super_update_bs)
     apply (rule field_of_t_field_lookup [OF fl])
      apply (clarsimp simp: eui)
     apply (clarsimp simp: n_is_field_offset)
    apply clarsimp
    apply (unfold from_bytes_def)
    apply (subst fi_fu_consistentD [where f=f and s="adjust_ti (typ_info_t TYPE('b)) xf xfu"])
        apply (clarsimp simp: fl)
        apply (clarsimp simp: n_is_field_offset field_lvalue_def)
        apply (metis unat_of_nat_field_offset fl)
       apply clarsimp
      apply (clarsimp simp: size_of_def)
     apply (clarsimp simp: size_of_def)
    apply clarsimp
    apply (subst update_ti_s_from_bytes)
     apply clarsimp
    apply (subst update_ti_adjust_ti)
     apply (rule xf_xfu)
    apply (subst update_ti_s_from_bytes)
     apply clarsimp
    apply clarsimp
    apply (clarsimp simp: h_val_def)
    done

  show "?LHS p = ?RHS p"
    apply (case_tac "p = ptr")
     apply (erule ssubst)
     apply (rule equal_case)
    apply (insert cl)
    apply (clarsimp simp: simple_lift_def hrs_mem_update split: if_split_asm)
    apply (rule h_val_heap_update_disjoint)
    apply (insert field_tag_sub [OF fl, where p=ptr])
    apply (clarsimp simp: size_of_def)
    apply (clarsimp simp: heap_ptr_valid_def)
    apply (frule (1) valid_simple_footprint_neq_disjoint, fastforce)
    apply clarsimp
    apply blast
    done
qed

lemma simple_lift_field_update:
  fixes val :: "'b :: mem_type" and ptr :: "'a :: mem_type ptr"
  assumes   fl: "field_ti TYPE('a) f =
                     Some (adjust_ti (typ_info_t TYPE('b)) xf (xfu o (\<lambda>x _. x)))"
  and   xf_xfu: "fg_cons xf (xfu o (\<lambda>x _. x))"
  and       cl: "simple_lift hp ptr = Some z"
  shows "(simple_lift (hrs_mem_update (heap_update (Ptr &(ptr\<rightarrow>f)) val) hp)) =
                simple_lift hp(ptr \<mapsto> xfu (\<lambda>_. val) z)"
    (is "?LHS = ?RHS")
  apply (insert fl [unfolded field_ti_def])
  apply (clarsimp split: option.splits)
  apply (subst simple_lift_field_update' [where xf=xf and xfu="xfu o (\<lambda>x _. x)" and z=z])
     apply (clarsimp simp: o_def split: option.splits)
     apply (rule refl)
    apply (rule xf_xfu)
   apply (rule cl)
  apply clarsimp
  done

lemma simple_heap_diff_types_impl_diff_ptrs:
  "\<lbrakk> heap_ptr_valid h (p::('a::c_type) ptr);
     heap_ptr_valid h (q::('b::c_type) ptr);
     typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE('b) \<rbrakk> \<Longrightarrow>
   ptr_val p \<noteq> ptr_val q"
  apply (clarsimp simp: heap_ptr_valid_def)
  apply (clarsimp simp: valid_simple_footprint_def)
  done

lemma h_val_update_regions_disjoint:
  "\<lbrakk> { ptr_val p ..+ size_of TYPE('a) } \<inter> { ptr_val x ..+ size_of TYPE('b)} = {} \<rbrakk> \<Longrightarrow>
        h_val (heap_update p (v::('a::mem_type)) h) x = h_val h (x::('b::c_type) ptr)"
  apply (clarsimp simp: heap_update_def)
  apply (clarsimp simp: h_val_def)
  apply (subst heap_list_update_disjoint_same)
   apply clarsimp
  apply clarsimp
  done

lemma simple_lift_field_update_t:
  fixes    val :: "'b :: mem_type" and ptr :: "'a :: mem_type ptr"
  assumes  fl: "field_ti TYPE('a) f = Some t"
  and      diff: "typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE('c :: c_type)"
  and      eu: "export_uinfo t = export_uinfo (typ_info_t TYPE('b))"
  and      cl: "simple_lift hp ptr = Some z"
  shows "((simple_lift (hrs_mem_update (heap_update (Ptr &(ptr\<rightarrow>f)) val) hp)) :: 'c ptr \<Rightarrow> 'c option) =
             simple_lift hp"
  apply (rule ext)
  apply (case_tac "simple_lift hp x")
   apply clarsimp
  apply (case_tac "ptr_val x = ptr_val ptr")
   apply clarsimp
   apply (clarsimp simp: simple_lift_def hrs_mem_update split: if_split_asm)
   apply (cut_tac simple_lift_heap_ptr_valid [OF cl])
   apply (drule (1) simple_heap_diff_types_impl_diff_ptrs [OF _ _ diff])
   apply simp
  apply (clarsimp simp: simple_lift_def hrs_mem_update split: if_split_asm)
  apply (rule field_ti_field_lookupE [OF fl])
  apply (frule_tac p=ptr in field_tag_sub)
  apply (clarsimp simp: h_val_def heap_update_def)
  apply (subst heap_list_update_disjoint_same)
   apply clarsimp
   apply (cut_tac simple_lift_heap_ptr_valid [OF cl])
   apply (drule (2) heap_ptr_valid_neq_disjoint)
   apply (clarsimp simp: export_size_of [unfolded typ_uinfo_t_def, OF eu])
   apply blast
  apply simp
  done

lemma simple_lift_heap_update_other':
  "\<lbrakk> simple_lift h (p::'b::mem_type ptr) = Some v';
     typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE('b) \<rbrakk> \<Longrightarrow>
   simple_lift (hrs_mem_update (heap_update p v) h) = ((simple_lift h)::'a::c_type typ_heap)"
  apply (rule simple_lift_heap_update_other)
   apply (erule simple_lift_heap_ptr_valid)
  apply simp
  done

(* If you update bytes inside an object of one type, it won't affect
 * heaps of other types. *)
lemma simple_lift_heap_update_bytes_in_other:
  "\<lbrakk> simple_lift h (p::'b::mem_type ptr) = Some v';
     typ_uinfo_t TYPE('b) \<noteq> typ_uinfo_t TYPE('c);
     { ptr_val q ..+ size_of TYPE('a)} \<subseteq> {ptr_val p  ..+ size_of TYPE('b) }  \<rbrakk> \<Longrightarrow>
   simple_lift (hrs_mem_update (heap_update (q::'a::mem_type ptr) v) h) = ((simple_lift h)::'c::mem_type typ_heap)"
  apply (rule ext)
  apply (clarsimp simp: simple_lift_def split: if_split_asm)
  apply (drule (1) heap_ptr_valid_type_neq_disjoint, simp)
  apply (clarsimp simp: hrs_mem_update)
  apply (rule h_val_heap_update_disjoint)
  apply blast
  done

lemma typ_name_neq:
    "typ_name (export_uinfo (typ_info_t TYPE('a::c_type)))
        \<noteq> typ_name (export_uinfo (typ_info_t TYPE('b::c_type)))
    \<Longrightarrow> typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE('b)"
  apply (metis typ_uinfo_t_def)
  done

lemma of_nat_mod_div_decomp:
  "of_nat k
        = of_nat (k div size_of TYPE('b)) * of_nat (size_of TYPE('b::mem_type)) +
              of_nat (k mod size_of TYPE('b))"
  by (metis mod_div_decomp of_nat_add of_nat_mult)

lemma c_guard_array_c_guard:
  "\<lbrakk> \<And>x. x < CARD('a) \<Longrightarrow> c_guard (ptr_coerce p +\<^sub>p int x :: 'b ptr) \<rbrakk> \<Longrightarrow> c_guard ( p :: ('b :: mem_type, 'a :: finite) array ptr)"
  apply atomize
  apply (clarsimp simp: c_guard_def)
  apply (rule conjI)
   apply (drule_tac x=0 in spec)
   apply (clarsimp simp: ptr_aligned_def align_of_def align_td_array)
  apply (simp add: c_null_guard_def)
  apply (clarsimp simp: intvl_def)
  apply (drule_tac x="k div size_of TYPE('b)" in spec)
  apply (erule impE)
   apply (metis (full_types) less_nat_zero_code mult_is_0 neq0_conv td_gal_lt)
  apply clarsimp
  apply (drule_tac x="k mod size_of TYPE('b)" in spec)
  apply (clarsimp simp: CTypesDefs.ptr_add_def)
  apply (subst (asm) add.assoc)
  apply (subst (asm) of_nat_mod_div_decomp [symmetric])
  apply clarsimp
  done

lemma heap_list_update_list':
  "\<lbrakk> n + x \<le> length v; length v < addr_card; q = (p + of_nat x) \<rbrakk> \<Longrightarrow>
      heap_list (heap_update_list p v h) n q = take n (drop x v)"
  by (metis heap_list_update_list)

lemma outside_intvl_range:
    "p \<notin> {a ..+ b} \<Longrightarrow> p < a \<or> p \<ge> a + of_nat b"
  apply (clarsimp simp: intvl_def not_le not_less)
  apply (drule_tac x="unat (p-a)" in spec)
  apply clarsimp
  apply (metis add_diff_cancel2 le_less_linear le_unat_uoi
      mpl_lem not_add_less2 unat_mono word_less_minus_mono_left)
  done

lemma first_in_intvl:
  "b \<noteq> 0 \<Longrightarrow> a \<in> {a ..+ b}"
  by (force simp: intvl_def)

lemma zero_not_in_intvl_no_overflow:
  "0 \<notin> {a :: 'a::len word ..+ b} \<Longrightarrow> unat a + b \<le> 2 ^ len_of TYPE('a)"
  apply (rule ccontr)
  apply (simp add: intvl_def not_le)
  apply (drule_tac x="2 ^ len_of TYPE('a) - unat a" in spec)
  apply (clarsimp simp: not_less)
  apply (erule disjE)
  apply (metis (erased, hide_lams) diff_add_inverse less_imp_add_positive of_nat_2p of_nat_add
           unat_lt2p word_neq_0_conv word_unat.Rep_inverse)
  apply (metis le_add_diff_inverse le_antisym le_diff_conv le_refl
           less_imp_le_nat add.commute not_add_less1 unat_lt2p)
  done

lemma intvl_split:
  "\<lbrakk> n \<ge> a \<rbrakk> \<Longrightarrow> { p :: ('a :: len) word ..+ n } = { p ..+ a } \<union> { p + of_nat a ..+ (n - a)}"
  apply (rule set_eqI, rule iffI)
   apply (clarsimp simp: intvl_def not_less)
   apply (rule_tac x=k in exI)
   apply clarsimp
   apply (rule classical)
   apply (drule_tac x="k - a" in spec)
   apply (clarsimp simp: not_less)
   apply (metis diff_less_mono not_less)
  apply (clarsimp simp: intvl_def not_less)
  apply (rule_tac x="unat (x - p)" in exI)
  apply clarsimp
  apply (erule disjE)
   apply clarsimp
   apply (metis le_unat_uoi less_or_eq_imp_le not_less order_trans)
  apply clarsimp
  apply (metis le_def le_eq_less_or_eq le_unat_uoi less_diff_conv
    add.commute of_nat_add)
  done

lemma heap_ptr_valid_range_not_NULL:
  "heap_ptr_valid htd (p :: ('a :: c_type) ptr)
      \<Longrightarrow> 0 \<notin> {ptr_val p ..+ size_of TYPE('a)}"
  apply (clarsimp simp: heap_ptr_valid_def)
  apply (metis c_guard_def c_null_guard_def)
  done

lemma heap_ptr_valid_last_byte_no_overflow:
  "heap_ptr_valid htd (p :: ('a :: c_type) ptr)
      \<Longrightarrow> unat (ptr_val p) + size_of TYPE('a) \<le> 2 ^ len_of TYPE(addr_bitsize)"
  by (metis c_guard_def c_null_guard_def heap_ptr_valid_def
        zero_not_in_intvl_no_overflow)

lemma heap_ptr_valid_intersect_array:
  "\<lbrakk> \<forall>j < n. heap_ptr_valid htd (p +\<^sub>p int j);
        heap_ptr_valid htd (q :: ('a :: c_type) ptr) \<rbrakk>
         \<Longrightarrow> (\<exists>m < n. q = (p +\<^sub>p int m))
    \<or> ({ptr_val p ..+ size_of TYPE ('a) * n} \<inter> {ptr_val q ..+ size_of TYPE ('a :: c_type)} = {})"
  apply (induct n)
   apply clarsimp
  apply atomize
  apply simp
  apply (case_tac "n = 0")
   apply clarsimp
   apply (metis heap_ptr_valid_neq_disjoint ptr_val_inj)
  apply (erule disjE)
   apply (metis less_Suc_eq)
  apply (case_tac "q = p +\<^sub>p int n")
   apply force
  apply (frule_tac x=n in spec)
  apply (erule impE, simp)
  apply (drule (1) heap_ptr_valid_neq_disjoint)
  apply simp
  apply (simp add: CTypesDefs.ptr_add_def)
  apply (rule disjI2)
  apply (cut_tac a=" of_nat n * of_nat (size_of TYPE('a))"
      and p="ptr_val p" and n="n * size_of TYPE('a) + size_of TYPE('a)" in intvl_split)
   apply clarsimp
  apply (clarsimp simp: field_simps Int_Un_distrib2)
  apply (metis IntI emptyE intvl_empty intvl_inter intvl_self neq0_conv)
  done

(* Simplification rules for dealing with "lift_simple". *)

lemmas simple_lift_simps =
  typ_name_neq
  simple_lift_c_guard
  h_val_simple_lift
  simple_lift_heap_update'
  simple_lift_heap_update_other'
  c_guard_field
  h_val_field_simple_lift
  simple_lift_field_update
  simple_lift_field_update_t
  c_guard_array_field
  nat_to_bin_string_simps

(* Old name for the above simpset. *)
lemmas typ_simple_heap_simps = simple_lift_simps

end
