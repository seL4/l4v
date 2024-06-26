
theory HeapTac
imports CParser.CTranslation CParser.TypHeapLib "../../lib/ML_Utils/TermPatternAntiquote"
begin

text \<open> The basic idea is that we wish to take a term Q and construct a term P such that

        H |- P = Q.
    
        where H is some set of hypotheses obtained by assuming some of the premises of a set of
        rewrite rules.  There will be some magic here to figure out which rules to apply, so this
        is not going to be a generic tactic (as opposed to e.g. strengthen)
     \<close>

syntax "_Clift" :: "type \<Rightarrow> logic" ("(1CLIFT/(1'(_')))")

translations
  "CLIFT('t)" => "CONST lift_t CONST c_guard :: _ \<Rightarrow> ('t ptr => 't option)"

lemma len8_div_8_nonzero [simp]:
  "len_of TYPE('a :: len8) div 8 \<noteq> 0"
proof -
  have "0 < len_of TYPE('a)" by (rule len_gt_0)
  thus ?thesis
    by (simp add: len8_bytes)
qed

lemma typ_uinfo_same_size:
  shows "len_of TYPE('a) = len_of TYPE('b) \<Longrightarrow> typ_uinfo_t TYPE ('a :: len8 word) = typ_uinfo_t TYPE ('b :: len8 word)"
  apply (simp add: peer_typ_def typ_info_word typ_uinfo_t_def tag_disj_def sub_typ_def 
                   typ_tag_le_def field_norm_def len_exp_def cong: if_cong)
  apply (rule ext)
  apply (clarsimp simp add: word_rsplit_rcat_size len8_bytes word_size)
  done

lemmas len_of_signed_unsigned = len_signed [where x = "TYPE (('a  :: len8) signed)"]

lemma word_rsplit_ucast:
  fixes v :: "'a :: len8 word"
  shows "len_of TYPE('a) = len_of TYPE('b) \<Longrightarrow> word_rsplit (ucast v :: 'b :: len8 word) = (word_rsplit v :: byte list)"
  apply (simp add: word_rsplit_upt [where n = "len_of TYPE('a) div 8"] word_size len8_bytes size_of_def)
  apply clarsimp
  apply (rule word_eqI)
  apply (simp add: nth_ucast nth_shiftr word_size len8_bytes)
  done

lemma h_val_heap_update_word_same_size:
  fixes p :: "('a :: len8) word ptr" and q :: "('b :: len8) word ptr"
  assumes valid: "d \<Turnstile>\<^sub>t p" "d \<Turnstile>\<^sub>t q"
  and   lens: "len_of TYPE('a) = len_of TYPE('b)"
  shows "h_val (heap_update p v hp) q = (if ptr_val q = ptr_val p then ucast v else h_val hp q)"
proof (cases "ptr_val q = ptr_val p")
  case True
  have "size_of TYPE('b word) = size_of TYPE('a word)" using lens
    unfolding size_of_def by (simp add: typ_info_word)
  thus ?thesis using True lens
    apply (simp add: h_val_def heap_update_def)
    apply (subst heap_list_update_to_bytes)
    apply(simp add: from_bytes_def to_bytes_def typ_info_word  word_rsplit_ucast [OF lens, symmetric] 
                    word_rcat_rsplit 
                    length_word_rsplit_even_size [OF refl, where m = "len_of TYPE('a) div 8"]
                    word_size len8_bytes)
    done
next
  case False
  thus ?thesis using valid
    by (simp add: h_val_heap_same_peer)
qed

lemma size_of_word:
  "size_of TYPE ('a word) = len_of TYPE('a :: len8) div 8"
  unfolding size_of_def by (simp add: typ_info_word)

lemma h_t_valid_ptr_coerce_same_size:
  fixes p :: "'a :: len8 word ptr"
  assumes lens: "len_of TYPE('a) = len_of TYPE('b :: len8)"
  shows "d \<Turnstile>\<^sub>t PTR_COERCE('a word \<rightarrow> 'b word) p = d \<Turnstile>\<^sub>t p"
  using lens
  unfolding h_t_valid_def
  by (simp add: typ_uinfo_same_size [where 'a = 'a] c_guard_def c_null_guard_def size_of_word ptr_aligned_def align_of_word)
  
lemma lift_t_heap_update_word_same_size:
  fixes p :: "('a :: len8) word ptr"
  assumes valid: "hrs_htd hp \<Turnstile>\<^sub>t p"
  and   lens: "len_of TYPE('a) = len_of TYPE('b)"
  shows "CLIFT('b :: len8 word) (hrs_mem_update (heap_update p v) hp) = 
         (CLIFT('b word) hp)(ptr_coerce p := Some (ucast v))"
  using valid lens
  apply -
  apply (rule ext)
  apply (rename_tac q)
  apply (cases hp)
  apply (simp add: lift_t_if hrs_mem_update_def hrs_htd_def split del: if_split)
  apply (simp add: h_t_valid_ptr_coerce_same_size h_val_heap_update_word_same_size)
  apply (cases p)
  apply (case_tac q)
  apply simp
  done  

(* Slightly customised for the heap tactic, assumes g = c_guard *)
section {* Moving field update *}

lemmas heaptac_lift_t_heap_update_at_type = clift_heap_update

lemmas heaptac_lift_t_heap_update_at_word_same_size = lift_t_heap_update_word_same_size

lemma sub_typ_proper_sub_typ:
  "t <\<^sub>\<tau> u \<Longrightarrow> t \<le>\<^sub>\<tau> u"
  unfolding sub_typ_def sub_typ_proper_def by simp

lemma heaptac_lift_t_heap_update_at_super:
  fixes p :: "('b :: mem_type) ptr"
  assumes "hrs_htd hp \<Turnstile>\<^sub>t p"
  and     lt: "TYPE('b) <\<^sub>\<tau> TYPE('a)"
  shows "CLIFT('a :: mem_type) (hrs_mem_update (heap_update p v) hp) = super_field_update_t p v (CLIFT('a) hp)"
  using assms sub_typ_proper_sub_typ [OF lt]
  by  (cases hp) (clarsimp simp: hrs_htd_def lift_t_super_field_update hrs_mem_update_def )
  
lemma heaptac_lift_t_heap_update_at_sub:
  fixes p :: "('b :: mem_type) ptr"
  assumes "hrs_htd hp \<Turnstile>\<^sub>t p"
  and     "TYPE('a) <\<^sub>\<tau> TYPE('b)"
  shows "CLIFT('a :: mem_type) (hrs_mem_update (heap_update p v) hp) = 
         sub_field_update_t (TypHeap.field_names (typ_info_t TYPE('b)) (typ_uinfo_t TYPE('a))) p v (CLIFT('a) hp)"
  using assms 
  by (cases hp) (clarsimp simp: hrs_htd_def hrs_mem_update_def lift_t_sub_field_update sub_typ_proper_def 
                                sub_typ_def typ_tag_lt_def)

lemma heaptac_lift_t_heap_update_at_other:
  fixes p :: "('b :: mem_type) ptr"
  assumes "hrs_htd hp \<Turnstile>\<^sub>t p"
  and     "typ_uinfo_t TYPE('a) \<bottom>\<^sub>t typ_uinfo_t TYPE('b)"
  shows "CLIFT('a :: mem_type) (hrs_mem_update (heap_update p v) hp) = CLIFT('a) hp"
  using assms
  by (cases hp) (clarsimp simp: hrs_htd_def hrs_mem_update_def lift_t_heap_update_same)


lemma size_list_is_length: "size_list (\<lambda>x. 0) = length"
  apply (rule ext)
  apply (simp add: size_list_conv_sum_list)
  done

thm typ_desc_typ_struct_inducts

lemma field_lookup_size_typ_desc_lt:
  "\<And>fs m n. \<lbrakk> length fs > 0; field_lookup t fs m = Some (s,n) \<rbrakk> \<Longrightarrow> size_typ_desc f s < size_typ_desc f t"
  "\<And>fs m n. \<lbrakk> length fs > 0; field_lookup_struct st fs m = Some (s,n) \<rbrakk> \<Longrightarrow> size_typ_desc f s < size_typ_struct f st"
  "\<And>fs m n. \<lbrakk> length fs > 0; field_lookup_list ts fs m = Some (s,n) \<rbrakk> \<Longrightarrow> size_typ_desc f s < size_list (size_dt_pair (size_typ_desc f) (\<lambda>x. 0)) ts"
  "\<And>fs m n. \<lbrakk> length fs > 0; field_lookup_pair x fs m = Some (s,n) \<rbrakk> \<Longrightarrow> size_typ_desc f s < size_dt_pair (size_typ_desc f) (\<lambda>x. 0) x"
  find_theorems size_dt_pair size_list
     apply (induction t and st and ts and x  arbitrary: s and s and s and s and s)
       apply (auto split: option.splits simp: less_SucI size_list_conv_sum_list trans_less_add1 trans_less_add2)[4]
   apply (fastforce split: if_split_asm option.splits)
   apply (clarsimp split: if_split if_split_asm simp: handy_if_lemma cong: if_cong)
  apply (case_tac "tl fs")
   apply simp
  apply fastforce
  done

lemma field_lookup_not_self:
  "field_lookup t (f # fs) n = Some (t', v) \<Longrightarrow> t' \<noteq> t"
  apply (drule field_lookup_size_typ_desc_lt [rotated])
   apply simp
  apply clarsimp
  done

lemma field_lookup_into_sub_typ:
  "map_option fst (field_lookup (typ_uinfo_t TYPE('a :: c_type)) [f] 0) 
   = Some (typ_uinfo_t TYPE('b :: c_type))
  \<Longrightarrow> TYPE('b) <\<^sub>\<tau> TYPE('a)"
  unfolding sub_typ_proper_def typ_tag_lt_def typ_tag_le_def
  apply clarsimp
  apply rule
  apply (drule td_set_field_lookupD)
   apply (erule exI)
  apply (erule field_lookup_not_self)
  done

lemma sub_typ_proper_into_field_lookup:
  assumes "TYPE('b :: wf_type) <\<^sub>\<tau> TYPE('a :: wf_type)"
  shows "\<exists>fs. fs \<noteq> [] \<and> 
              map_option fst (field_lookup (typ_uinfo_t TYPE('a)) fs 0) = Some (typ_uinfo_t TYPE('b))"
  using assms unfolding sub_typ_proper_def typ_tag_lt_def typ_tag_le_def
  apply (clarsimp simp: td_set_field_lookup)
  apply (rule_tac x = f in exI)
  apply clarsimp
  done

lemma field_ti_into_sub_typ:
  "map_option export_uinfo (field_ti TYPE('a :: c_type) [f])
   = Some (export_uinfo (typ_info_t TYPE('b :: c_type)))
  \<Longrightarrow> TYPE('b) <\<^sub>\<tau> TYPE('a)"
  apply (rule field_lookup_into_sub_typ)
  apply (clarsimp simp: typ_uinfo_t_def field_ti_def split: option.splits)
  apply (drule field_lookup_export_uinfo_Some)
  apply auto
  done

lemma field_ti_into_sub_typ_one:
  "map_option export_uinfo (field_ti TYPE('a :: c_type) [f])
   = Some (export_uinfo (typ_info_t TYPE('b :: c_type)))
  \<Longrightarrow> TYPE('b) <\<^sub>\<tau> TYPE('a)"
  by (rule field_ti_into_sub_typ)

lemma heaptac_export_tag_adjust_ti:
    "fg_cons f g \<Longrightarrow> export_uinfo (adjust_ti (typ_info_t TYPE('a :: wf_type)) f g) = export_uinfo (typ_info_t TYPE('a))"
    apply (subst export_tag_adjust_ti)
      apply simp
     apply (rule wf_fd)
    apply simp
   done

(* UNUSED *)
lemma sub_typ_proper_into_not_field_of_t:
  fixes p :: "'a :: c_type ptr" and q :: "'b :: c_type ptr"
  shows "TYPE('b) <\<^sub>\<tau> TYPE('a) \<Longrightarrow> \<not> field_of_t p q"
  apply (erule contrapos_pn)
  apply (simp add: sub_typ_proper_def sub_typ_def typ_tag_lt_def field_of_t_def)
  apply (drule field_of_sub)
  apply simp
  done

(* UNUSED *)
lemma field_of_t_sub:
  fixes p :: "'a :: c_type ptr" and q :: "'b :: c_type ptr"
  shows "field_of_t p q \<Longrightarrow> TYPE('a) \<le>\<^sub>\<tau> TYPE('b)"
  unfolding field_of_t_def sub_typ_def
  by (erule field_of_sub)

(*
  We have that p :: 'b contains an 'a, and 'a contains a field (say fld) :: 'c,
 but not the 'c from p -- p\<rightarrow>f 

*)

lemma field_of_t_field_lookup:
  fixes c :: "'c :: c_type ptr" and p :: "'p :: wf_type ptr"
  assumes "field_of_t c p"
  shows "\<exists>f n. field_lookup (typ_uinfo_t TYPE('p)) f 0 = Some (typ_uinfo_t TYPE('c), unat (ptr_val c - ptr_val p))"
  using assms unfolding field_of_t_def field_of_def
  by (auto simp: td_set_field_lookup)

lemma triangle_not_field_of:
  fixes p :: "'a :: mem_type ptr" and q :: "'b :: mem_type ptr"
  assumes p: "d,g \<Turnstile>\<^sub>t p" and q: "d,g' \<Turnstile>\<^sub>t q"
  and  fg: "fg_cons acc (upd \<circ> (\<lambda>x _. x))"
  and  fl_f: "field_ti TYPE('a) [f] = Some (adjust_ti (typ_info_t TYPE('c)) acc (upd \<circ> (\<lambda>x _ . x)))"
  (* and   fl_f: "field_lookup (typ_uinfo_t TYPE('a)) [f] 0 = Some (typ_uinfo_t TYPE('c), n)" *)
  and   b_sub_a: "TYPE('b) <\<^sub>\<tau> TYPE('a)"
  and   c_sub_b: "TYPE('c) <\<^sub>\<tau> TYPE('b)"
  shows "\<not> field_of_t (PTR('c :: mem_type) &(p\<rightarrow>[f])) q"
proof (cases "field_of_t q p")
  case False
  have "{ptr_val q..+size_of TYPE('b)} \<inter> {ptr_val p..+size_of TYPE('a)} = {}"
  proof (rule h_t_valid_neq_disjoint) 
    show "\<not> TYPE('a) <\<^sub>\<tau> TYPE('b)" using b_sub_a
      apply (clarsimp simp add: sub_typ_proper_def)
      apply (drule (1) order_less_trans)
      apply simp
      done
  qed fact+
  moreover have "&(p\<rightarrow>[f]) \<in> {ptr_val p..+size_of TYPE('a)}" using fl_f
    apply -
    apply (simp add: typ_uinfo_t_def field_ti_def split: option.splits)
    apply clarsimp
    apply (rule set_mp)
     apply (erule field_tag_sub)
    apply (rule intvl_self)
    apply (erule field_lookup_wf_size_desc_gt)
    apply simp
    done
  ultimately show ?thesis
    apply -
    apply rule
    apply (drule field_of_t_mem)
    apply auto
    done
next
  let ?n' = "unat (ptr_val q - ptr_val p)"

  case True
  then obtain f' s' where fl_f': "field_lookup (typ_info_t TYPE('a)) f' 0 = Some (s', ?n')"
      and s': "export_uinfo s' = typ_uinfo_t TYPE('b)"
    by (clarsimp simp: typ_uinfo_t_def dest!: field_of_t_field_lookup field_lookup_export_uinfo_Some_rev)

  moreover from fl_f obtain s n where fl_f2: "field_lookup (typ_info_t TYPE('a)) [f] 0 = Some (s, n)"
    and s: "export_uinfo s = typ_uinfo_t TYPE('c)" using fg
    by (clarsimp simp: typ_uinfo_t_def dest!: field_lookup_export_uinfo_Some_rev simp: field_ti_def heaptac_export_tag_adjust_ti split: option.splits cong: rev_conj_cong)

  from fl_f2 fl_f' have "{of_nat n..+size_td s} \<inter> {(of_nat ?n' :: 32 word)..+size_td s'} = {}"
  proof (rule fa_fu_lookup_disj_interD)
    have "f' \<noteq> []" using fl_f' s' b_sub_a
      by (clarsimp simp: typ_uinfo_t_def sub_typ_proper_def)
    moreover have "hd f' \<noteq> f" 
    proof
      assume "hd f' = f"
      hence "field_lookup s (tl f') n = Some (s', ?n')" using fl_f' fl_f2 s s' `f' \<noteq> []`
        apply(clarsimp simp add: neq_Nil_conv)
        apply (drule_tac g = "tl f'" in field_lookup_prefix_Some''(1) [rule_format, where f = "[f]", symmetric])
         apply simp
        apply (clarsimp simp: sub_typ_def typ_tag_le_def)
        done
      hence "field_lookup s (tl f') 0 = Some (s', ?n' - n)" 
        apply -
        apply  (rule field_lookup_offset2)
        apply simp
        done

      hence "TYPE('b) \<le>\<^sub>\<tau> TYPE('c)" using s s'
        apply -
        apply (drule td_set_field_lookupD [where t = s])
        apply (drule td_set_export_uinfoD)
        apply (simp add: typ_uinfo_t_def sub_typ_def typ_tag_le_def)
        apply (erule exI)
        done
      thus False using c_sub_b
        by (simp add: sub_typ_proper_def sub_typ_def)
    qed
   ultimately show "disj_fn [f] f'" unfolding disj_fn_def
     by (cases f'; auto)
  qed (simp add: max_size [unfolded size_of_def])+
   
  show ?thesis
  proof
    let ?n = "unat (&(p\<rightarrow>[f]) - ptr_val q)"

    assume "field_of_t (PTR('c) &(p\<rightarrow>[f])) q"  

    hence "ptr_val (PTR('c) &(p\<rightarrow>[f])) \<in> {ptr_val q..+size_of TYPE('b)}"
      by (rule field_of_t_mem)
    hence "&(p\<rightarrow>[f]) \<in> {ptr_val q..+size_of TYPE('b)}" by simp

    moreover 

    from `{of_nat n..+size_td s} \<inter> {(of_nat ?n' :: 32 word)..+size_td s'} = {}`
    have "{ptr_val p + of_nat n..+size_td s} \<inter> {ptr_val q..+size_td s'} = {}"
      apply - 
      apply (subst (asm) intvl_disj_offset [symmetric, where x = "ptr_val p"])
      apply simp
      done
    hence "{&(p\<rightarrow>[f])..+size_td s} \<inter> {ptr_val q..+size_of TYPE('b)} = {}" using fl_f2 s'
      apply -
      apply (drule field_lookup_offset_eq [symmetric])
      apply (simp add: field_lvalue_def export_size_of)
      done
    moreover have "&(p\<rightarrow>[f]) \<in> {&(p\<rightarrow>[f])..+size_td s}" using s
      apply -
      apply (rule intvl_self)
      apply (simp add: export_size_of [symmetric])
      done

    ultimately show False by auto
  qed
qed

lemma super_field_update_triangle:
  fixes p :: "'a :: mem_type ptr" 
  assumes b_sub_a: "TYPE('b) <\<^sub>\<tau> TYPE('a)" 
  and     c_sub_b: "TYPE('c) <\<^sub>\<tau> TYPE('b)"
  and    "h_t_valid (hrs_htd hp) c_guard p"
  and  fg: "fg_cons acc (upd \<circ> (\<lambda>x _. x))"
  and  fl_f: "field_ti TYPE('a) [f] = Some (adjust_ti (typ_info_t TYPE('c)) acc (upd \<circ> (\<lambda>x _ . x)))"
  shows "super_field_update_t (PTR('c::mem_type) &(p\<rightarrow>[f])) v (CLIFT('b::mem_type) hp) = (CLIFT('b) hp)"
  using assms unfolding super_field_update_t_def
  apply -
  apply (rule ext)
  apply (clarsimp split: option.splits)
  apply (drule (5) triangle_not_field_of [OF _ h_t_valid_clift])
  apply simp
  done

lemma heaptac_lift_t_heap_update_at_triangle:
  fixes p :: "('a :: mem_type) ptr"
  assumes "hrs_htd hp \<Turnstile>\<^sub>t p"
  and     b_sub_a: "TYPE('b) <\<^sub>\<tau> TYPE('a)"
  and     c_sub_b: "TYPE('c) <\<^sub>\<tau> TYPE('b)"
  and  fg: "fg_cons acc (upd \<circ> (\<lambda>x _. x))"
  and  fl_f: "field_ti TYPE('a) [f] = Some (adjust_ti (typ_info_t TYPE('c)) acc (upd \<circ> (\<lambda>x _ . x)))"
  shows "CLIFT('b :: mem_type) (hrs_mem_update (heap_update (PTR('c::mem_type) &(p\<rightarrow>[f])) v) hp)
        = (CLIFT('b) hp)"
  using assms sub_typ_proper_sub_typ [OF b_sub_a] sub_typ_proper_sub_typ [OF c_sub_b]
  by  (cases hp) (clarsimp simp: hrs_htd_def lift_t_super_field_update [OF h_t_valid_field] hrs_mem_update_def super_field_update_triangle)

section {* Moving field accesses *}

lemma heaptac_lift_t_access_at_field:
  fixes p :: "'a :: mem_type ptr"
  assumes "hrs_htd hp \<Turnstile>\<^sub>t p"
  and     "fg_cons acc (upd \<circ> (\<lambda>x _. x))"
  and     "field_ti TYPE('a) [f] = Some (adjust_ti (typ_info_t TYPE('b)) acc (upd \<circ> (\<lambda>x _ . x)))"
  shows   "CLIFT('b :: mem_type) hp (Ptr &(p \<rightarrow> [f])) = map_option acc (CLIFT('a :: mem_type) hp p)"
  using assms
  apply -
  apply (clarsimp simp: h_t_valid_clift_Some_iff)
  apply (subst clift_field)
     apply assumption
    apply assumption
   apply (subst export_tag_adjust_ti)
     apply assumption
    apply (rule wf_fd)
   apply simp
  apply simp
  done

(* Plus the usual HOL ones.  
   FIXME: This is super inefficient as you get False \<and> False \<and> ... \<and> False 
*)

(* Extra td_names *)
(* FIXME: move back into l4v *)

lemma td_names_signed_word8 [simp]:
  "td_names (typ_info_t TYPE(8 signed word)) = {''word00010''}"
  by (simp add: typ_info_word nat_to_bin_string.simps)

lemma td_names_word16 [simp]:
  "td_names (typ_info_t TYPE(16 word)) =  {''word000010''}"
  by (simp add: typ_info_word nat_to_bin_string.simps)

lemma td_names_signed_word16 [simp]:
  "td_names (typ_info_t TYPE(16 signed word)) =  {''word000010''}"
  by (simp add: typ_info_word nat_to_bin_string.simps)

lemma td_names_signed_word32 [simp]:
  "td_names (typ_info_t TYPE(32 signed word)) = {''word0000010''}"
  by (simp add:  typ_info_word nat_to_bin_string.simps)

lemma td_names_signed_word64 [simp]:
  "td_names (typ_info_t TYPE(64 signed word)) = {''word00000010''}"
  by (simp add:  typ_info_word nat_to_bin_string.simps)

lemmas heaptac_tag_disj_simps = 
  list.simps append.simps insert_iff empty_iff Un_iff
  td_names_word8
  td_names_signed_word8
  td_names_word16
  td_names_signed_word16
  td_names_word32
  td_names_signed_word32
  td_names_word64
  td_names_signed_word64
  td_names_ptr
  td_names_array       
  typ_name_words
  typ_name_swords
  ptr_typ_name
  typ_name_itself_word
                                            
(* h_t_valid *)

lemma heaptac_h_t_valid_hrs_mem_update:
  "h_t_valid (hrs_htd hp) g p \<Longrightarrow> h_t_valid (hrs_htd (hrs_mem_update f hp)) g p" by simp

lemma heaptac_h_t_valid_field:
  fixes p :: "'a :: mem_type ptr"
  assumes "d \<Turnstile>\<^sub>t p"
  and     "fg_cons acc (upd \<circ> (\<lambda>x _. x))"
  and     "field_ti TYPE('a) [f] = Some (adjust_ti (typ_info_t TYPE('b)) acc (upd \<circ> (\<lambda>x _ . x)))"
  shows   "d \<Turnstile>\<^sub>t PTR('b :: mem_type) &(p\<rightarrow>[f])"
  using assms
  apply -
  apply (rule h_t_valid_field)
  apply assumption+
  apply (subst export_tag_adjust_ti)
  apply assumption
  apply (rule wf_fd)
  apply simp
  done

lemmas heaptac_h_t_valid_ptr_coerces = 
  iffD2 [OF h_t_valid_ptr_coerce_same_size [OF len_of_signed_unsigned]]
  iffD2 [OF h_t_valid_ptr_coerce_same_size [OF len_of_signed_unsigned [symmetric]]]
  
lemmas heaptac_h_t_valid_intros = heaptac_h_t_valid_hrs_mem_update heaptac_h_t_valid_field
  heaptac_h_t_valid_ptr_coerces

(* Conv rules *)

(* The idea here is that we use _field_lookup, then _field_lookup2 as many times as possible.
   The idea here is that if we have p\<rightarrow>f\<rightarrow>g, then this rule will give us a clift at the type of p\<rightarrow>f,
   whereas using _field_lookup2 will give us a clift at type p, which might give better results with
   the tactic (i.e., less super/subs)

   FIXME: is this actually true?
   FIXME: we disable lookup2 at the moment
*)

(* The 'id' here is so we can match it later *)
lemma heaptac_lift_t_move_field_lookup:
  fixes p :: "'a :: packed_type ptr"
  assumes  "h_t_valid (hrs_htd hp) c_guard p"
  and      "fg_cons acc (upd \<circ> (\<lambda>x _. x))"
  and      "field_ti TYPE('a) [f] = Some (adjust_ti (typ_info_t TYPE('b)) acc (upd \<circ> (\<lambda>x _ . x)))"
  shows "CLIFT('c :: mem_type) (hrs_mem_update (heap_update (PTR('b :: packed_type) &(p\<rightarrow>[f])) v) hp) 
       = CLIFT('c            ) (hrs_mem_update (heap_update p (id (upd (\<lambda>_. v)) (the (CLIFT('a) hp p)))) hp)"
  using assms
  apply -
  apply (subst heap_update_field_hrs)
  apply assumption
  apply (rule h_t_valid_c_guard, assumption)
  apply simp
  apply (cases hp)
  apply (simp add: lift_t_if hrs_htd_def hrs_mem_def)
  done

lemma heaptac_lift_t_move_field_lookup2:
  fixes p :: "'a :: mem_type ptr" and p' :: "'d :: packed_type ptr"
  assumes  "hrs_htd hp \<Turnstile>\<^sub>t p'"
  and      "fg_cons acc (upd \<circ> (\<lambda>x _. x))"
  and      "field_ti TYPE('d) [f] = Some (adjust_ti (typ_info_t TYPE('b)) acc (upd \<circ> (\<lambda>x _ . x)))"
  shows    "CLIFT('c :: mem_type) (hrs_mem_update (heap_update p (id F (the (CLIFT('b :: mem_type) hp (PTR('b) &(p'\<rightarrow>[f])))))) hp')
          = CLIFT('c :: mem_type) (hrs_mem_update (heap_update p (id (F \<circ> acc) (the (CLIFT('d) hp p')))) hp')"
  using assms
  by (clarsimp simp: h_t_valid_clift_Some_iff clift_field)

(* Just strips the id *)
lemma heaptac_lift_t_move_field_lookup3:
  fixes p :: "'a :: mem_type ptr" and p' :: "'d :: packed_type ptr"
  shows    "CLIFT('c :: mem_type) (hrs_mem_update (heap_update p (id F v)) hp')
          = CLIFT('c :: mem_type) (hrs_mem_update (heap_update p (F v)) hp')" by simp

lemma match_h_t_valid: "h_t_valid a b c \<Longrightarrow> h_t_valid a b c" .

(* sub typ *)

lemma sub_typ_trans:
  "\<lbrakk> TYPE ('a :: c_type) \<le>\<^sub>\<tau> TYPE ('b :: c_type); TYPE ('b) \<le>\<^sub>\<tau> TYPE ('c :: c_type) \<rbrakk> \<Longrightarrow> TYPE ('a) \<le>\<^sub>\<tau> TYPE ('c)"
  unfolding sub_typ_def by simp

lemma sub_typ_proper_trans:
  "\<lbrakk> TYPE ('a :: c_type) <\<^sub>\<tau> TYPE ('b :: c_type); TYPE ('b) <\<^sub>\<tau> TYPE ('c :: c_type) \<rbrakk> \<Longrightarrow> TYPE ('a) <\<^sub>\<tau> TYPE ('c)"
  unfolding sub_typ_proper_def by simp

lemma sub_typ_refl: "TYPE ('a :: c_type) \<le>\<^sub>\<tau> TYPE ('a)" unfolding sub_typ_def by simp

(* Strengthening via rewrites and hyps *)

(* Basically,   

      H |- A = B     H' |- A 
      -----------------------
      H' |- AND (H - H') \<and> B \<Longrightarrow> A 

  special cases for:
  * A \<longrightarrow> B, make sure we add hyps at B
  * if b then A else B, add at A and B
  
*)

lemma match_eqI: "A = B \<Longrightarrow> A = B" .

definition "flush_hyps H P \<equiv> H \<longrightarrow> P"

(* Used for selectively extracting hyps, esp. under binders.  E.g.
  
  Given P x == Q x under {H x, H'}

  we want to turn \<forall>x. P x into \<forall>x. H x \<and> Q x while leaving 
any hypotheses to higher levels 

*)
definition "flush_hyps_for x H P \<equiv> H \<longrightarrow> P"

lemma mark_flush_hyps: "flush_hyps H P \<Longrightarrow> H \<longrightarrow> P" unfolding flush_hyps_def .
lemma flush_hypsI: "H \<longrightarrow> P \<Longrightarrow> flush_hyps H P" unfolding flush_hyps_def .
lemma flush_hyps_forI: "H \<longrightarrow> P \<Longrightarrow> flush_hyps_for x H P" unfolding flush_hyps_for_def .
lemma match_flush_hyps_for: "flush_hyps_for x H P \<Longrightarrow> flush_hyps_for x H P" . 

lemmas conj_under_implies = conjE [rotated]
lemma x_implies_true_implies_x: "X \<Longrightarrow> (True \<Longrightarrow> X)" by simp

lemma eq_into_imp: "(P \<equiv> Q) \<Longrightarrow> Q \<longrightarrow> P" by simp

lemma h_val_is_the_lift_t:
  "hrs_htd hp \<Turnstile>\<^sub>t p \<Longrightarrow> h_val (hrs_mem hp) p = the (CLIFT('a :: mem_type) hp p)"
  by (clarsimp simp: h_t_valid_clift_Some_iff intro!: h_val_clift')

(* "True \<longrightarrow>" here so that we get simplification of the h_t_valid.  FIXME! *)
lemma heaptac_h_t_valid_ptr_safe:
   "d \<Turnstile>\<^sub>t p \<Longrightarrow> True \<longrightarrow> ptr_safe p d"
  by (rule impI, erule h_t_valid_ptr_safe)

lemma heaptac_h_t_valid_h_t_valid:
   "d \<Turnstile>\<^sub>t p \<Longrightarrow> True \<longrightarrow> d \<Turnstile>\<^sub>t p" by simp

(* Not in the set because we need to pick a state, use as an arg to umm_strg:

  apply (umm_strg h_t_valid_c_guard_str [where d = "hrd_htd (t_hrs_' s)"])

*)
lemma h_t_valid_c_guard_str:
   "d \<Turnstile>\<^sub>t p \<Longrightarrow> True \<longrightarrow> c_guard p" 
   by (simp add: h_t_valid_c_guard)

lemma strengthen_via_rewr_start:
  "flush_hyps H (P \<longrightarrow> Q) \<Longrightarrow> P \<Longrightarrow> H \<Longrightarrow> Q"
  unfolding flush_hyps_def by simp

lemma strengthen_via_rewr_imp_lhs_start:
  "flush_hyps H (P = P') \<Longrightarrow> P' \<longrightarrow> Q \<Longrightarrow> H \<Longrightarrow> P \<longrightarrow> Q"
  unfolding flush_hyps_def by simp

(* We resolve P against the first assumption, rewrite, and then continue.
*) 
lemma strengthen_via_rewr_asm_start:
  "P \<Longrightarrow> flush_hyps H (P = P') \<Longrightarrow> (P' \<Longrightarrow> R) \<Longrightarrow> H \<Longrightarrow> R"
  unfolding flush_hyps_def by simp

ML_file "memo_cache.ML" 
ML_file "umm_support.ML"
 
lemmas strengthen_via_rewr_cleanup_rules [umm_cleanup] = 
  heaptac_h_t_valid_ptr_safe
  heaptac_h_t_valid_h_t_valid

method_setup umm_strg = \<open> Umm_Support.method \<close> "Simplify lift_t/heap_update"

method_setup umm_strg_imp_lhs = \<open> Umm_Support.method_imp_lhs \<close>
  "Simplify lift_t/heap_update on the LHS of an implication"
method_setup umm_strg_asms = \<open> Umm_Support.method_asm \<close>
  "Simplify lift_t/heap_update on the assumptions of the current goal"

method_setup umm_strg_full = \<open> Umm_Support.method_full \<close>
  "Simplify lift_t/heap_update on assumptions and concl. of the current goal"

lemma umm_all_cong [umm_cong]:
  "(\<And>x. flush_hyps_for x (H x) (P x \<longrightarrow> Q x)) \<Longrightarrow> (\<forall>x. H x \<and> P x) \<longrightarrow> (\<forall>x. Q x)"
  unfolding flush_hyps_for_def by simp

lemma umm_ex_cong [umm_cong]:
  "(\<And>x. flush_hyps_for x (H x) (P x \<longrightarrow> Q x)) \<Longrightarrow> (\<exists>x. H x \<and> P x) \<longrightarrow> (\<exists>x. Q x)"
  unfolding flush_hyps_for_def by auto
  
lemma umm_imp_weak_cong [umm_cong]:
  "P = P' \<Longrightarrow> flush_hyps H (Q' \<longrightarrow> Q) \<Longrightarrow> (P' \<longrightarrow> (H \<and> Q')) \<longrightarrow> (P \<longrightarrow> Q)" 
  unfolding flush_hyps_def by simp

lemma umm_ite_cong [umm_cong]:
  "b' = b 
  \<Longrightarrow> flush_hyps H (P \<longrightarrow> P') 
  \<Longrightarrow> flush_hyps H' (Q \<longrightarrow> Q')
  \<Longrightarrow> (if b then H \<and> P else H' \<and> Q) \<longrightarrow> (if b' then P' else Q')"
  unfolding flush_hyps_def by simp

lemma umm_let_weak_cong [umm_cong]:
  "v' = v \<Longrightarrow> (\<And>x. flush_hyps_for x (H x) (P x \<longrightarrow> P' x)) \<Longrightarrow> (Let v (\<lambda>x. H x \<and> P x) \<longrightarrow> Let v' P')"
  unfolding flush_hyps_for_def by simp

lemma umm_case_prod_cong [umm_cong]:
  assumes "v = v'"
  and     "\<And>p q. flush_hyps_for (p, q) (H p q) (f' p q \<longrightarrow> f p q)"
  shows "case_prod (\<lambda>p q. H p q \<and> f' p q) v' \<longrightarrow> case_prod f v"
  using assms unfolding flush_hyps_for_def
  by (cases v; auto)

declare conj_mono [umm_cong]
declare disj_mono [umm_cong]

(* This allows us to use the strengthen_tac for e.g. imp_lhs *)
lemma umm_flush_hyps_cong [umm_cong]:
  "flush_hyps H P \<Longrightarrow> flush_hyps H P" .

lemma umm_flush_hyps_for_cong [umm_cong]:
  "flush_hyps_for x H P \<Longrightarrow> flush_hyps_for x H P" .

end