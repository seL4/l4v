(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Memcpy
imports
  "CParser.CTranslation"
  "AutoCorres.AutoCorres"
begin

abbreviation "ADDR_MAX \<equiv> UWORD_MAX TYPE(addr_bitsize)"

(* Helper for noticing when you accidentally haven't constrained an of_nat *)
abbreviation "of_nat_addr \<equiv> of_nat::(nat \<Rightarrow> addr)"

lemma byte_ptr_guarded:
    "ptr_val (x::8 word ptr) \<noteq> 0 \<Longrightarrow> c_guard x"
  unfolding c_guard_def c_null_guard_def ptr_aligned_def
  by (clarsimp simp: intvl_Suc)

(* FIXME: MOVE *)
lemma ptr_add_coerce: "ptr_val (((ptr_coerce x)::('a::{c_type}) ptr) +\<^sub>p a) = (ptr_val x) + (of_int a * of_nat (size_of TYPE('a)))"
  apply (case_tac x)
  apply (clarsimp simp: CTypesDefs.ptr_add_def)
  done

(* FIXME: MOVE *)
(* Casting a valid pointer to char* and incrementing it by a value less than
 * the size of the underlying type does not give us NULL.
 *)
lemma ptr_contained:"\<lbrakk> c_guard (x::('a::c_type) ptr); size_of TYPE('a) = sz;
                       0 \<le> i; i < int sz; (y::8 word ptr) = ptr_coerce x\<rbrakk> \<Longrightarrow> c_guard (y +\<^sub>p i)"
  apply (rule byte_ptr_guarded)
  unfolding c_guard_def c_null_guard_def ptr_add_def
  apply simp
  apply (clarsimp simp: CTypesDefs.ptr_add_def intvl_def)
  apply (erule allE [where x="nat i"])
  apply (clarsimp simp: nat_less_iff of_nat_nat)
  done

external_file "memcpy.c"
install_C_file "memcpy.c"

(* FIXME: MOVE *)
lemma squash_auxupd_id[polish]:
  "modify (t_hrs_'_update (hrs_htd_update id)) = skip"
  by (monad_eq simp: skip_def id_def hrs_htd_update_def)

autocorres [no_heap_abs=memcpy memcpy_int] "memcpy.c"

(* Dereference a pointer *)
abbreviation "deref s x \<equiv> h_val (hrs_mem (t_hrs_' s)) x"

(* char* cast *)
abbreviation "byte_cast x \<equiv> ((ptr_coerce x)::8 word ptr)"

context memcpy begin

lemma memcpy_char:
  "\<lbrace> \<lambda>s. c_guard (x::8 word ptr) \<and>
         c_guard (y::8 word ptr) \<and>
         unat sz = size_of TYPE(8 word) \<and>
         P (deref s x) \<and>
         x \<noteq> y\<rbrace>
      memcpy' (ptr_coerce y) (ptr_coerce x) sz
   \<lbrace>\<lambda> _ s. P (deref s y) \<rbrace>!"
  (* Evaluate sz *)
  apply clarsimp

  unfolding memcpy'_def
  apply (clarsimp simp:skip_def)
  apply wp

  (* Unroll the loop twice *)
  apply (subst whileLoop_unroll, wp)
     apply (subst whileLoop_unroll, wp)

  (* The remaining loop is never encountered *)
       apply (rule validNF_false_pre)
      apply wp+

  (* Finally we're left with the single assignment *)
  apply (clarsimp simp:hrs_mem_update h_val_heap_update)
  apply unat_arith
 done

lemma of_nat_prop_exp: "n < 32 \<Longrightarrow> of_nat (2 ^ n) = 2 ^ (of_nat n)"
  by clarsimp

lemma memcpy_word:
  "\<lbrace> \<lambda>s. c_guard (x::32 word ptr) \<and>
         c_guard (y::32 word ptr) \<and>
         unat sz = size_of TYPE(32 word) \<and>
         P (deref s x) \<and>
         x \<noteq> y \<rbrace>
      memcpy' (ptr_coerce y) (ptr_coerce x) sz
   \<lbrace> \<lambda>_ s. P (deref s y) \<rbrace>!"
  apply clarsimp
  unfolding memcpy'_def apply (clarsimp simp:skip_def)
  apply (rule validNF_assume_pre)
  apply (subgoal_tac "{ptr_val x ..+ unat sz} \<inter> {ptr_val y ..+ unat sz} = {}")
   apply (subst whileLoop_add_inv [where
     I="\<lambda>i s.  unat i \<le> unat sz \<and>
                (\<forall>a < i. deref s (byte_cast x +\<^sub>p uint a) = deref s (byte_cast y +\<^sub>p uint a)) \<and>
                P (deref s x)" and
     M="\<lambda>(i, s). unat sz - unat i"])
   apply (wp validNF_whileLoop_inv_measure_twosteps)
      apply clarsimp
      apply (rule conjI, unat_arith)
      apply (rule conjI, clarsimp)
       apply (case_tac "a = i")
        apply (clarsimp)
        apply (erule_tac x=i in allE)
        apply (clarsimp simp:hrs_mem_update h_val_heap_update)
        apply (subst h_val_heap_same)
            apply (rule ptr_retyp_h_t_valid)
            apply simp
           apply (rule ptr_retyp_disjoint)
            apply (rule ptr_retyp_h_t_valid)
            apply simp
           apply (clarsimp simp:ptr_add_def intvl_def CTypesDefs.ptr_add_def)
          apply simp
         apply (clarsimp simp: CTypesDefs.ptr_add_def field_of_t_simple)
         apply (drule field_of_t_simple)
         apply clarsimp
        apply simp
       apply (subgoal_tac "a < i")
        apply (clarsimp simp:hrs_mem_update)
        apply (subst h_val_heap_update_disjoint)

         (* The current goal should be obvious to unat_arith, but for some reason isn't *)
         apply (clarsimp simp:ptr_add_def intvl_def disjoint_iff_not_equal)
         apply (erule_tac x="ptr_val x + a" in allE, clarsimp)
         apply (erule impE)
          apply (rule_tac x="unat a" in exI, clarsimp)
          apply unat_arith

         apply (erule_tac x="ptr_val y + i" and
                          P="\<lambda>ya. (\<exists>k. ya = ptr_val y + of_nat k \<and> k < 4) \<longrightarrow> ptr_val y + i \<noteq> ya" in allE, clarsimp)
         apply (erule_tac x="unat i" in allE, clarsimp)
          apply unat_arith
         apply (clarsimp simp:CTypesDefs.ptr_add_def)
        apply (subst h_val_heap_update_disjoint)
         (* Similar goal to the previous irritation, but this time Isabelle decides to play ball *)
         apply (clarsimp simp:ptr_add_def intvl_def ptr_val_def disjoint_iff_not_equal)
        apply (clarsimp simp:CTypesDefs.ptr_add_def)
       apply (clarsimp simp:CTypesDefs.ptr_add_def)
      apply unat_arith

      apply (rule conjI)
       apply (subst hrs_mem_update)+
       apply (subst h_val_heap_update_disjoint)
        apply (clarsimp simp: disjoint_iff_not_equal)
        apply (clarsimp simp:CTypesDefs.ptr_add_def intvl_def)
        apply (erule_tac x="ptr_val x + of_nat k" in allE)
        apply (erule impE)
         apply (rule_tac x="k" in exI)
         apply simp
        apply (erule_tac x="ptr_val y + i" and
                         P="\<lambda>ya. (\<exists>k. ya = ptr_val y + of_nat k \<and> k < 4) \<longrightarrow> ptr_val x + of_nat k \<noteq> ya" in allE)
        apply (erule impE)
         apply (rule_tac x="unat i" in exI)
         apply simp
         apply unat_arith
        apply simp
       apply simp

      (* Yet more tedium that unat_arith doesn't like *)
      apply (rule conjI)
       apply (rule byte_ptr_guarded,
              clarsimp simp:CTypesDefs.ptr_add_def c_guard_def c_null_guard_def intvl_def,
              (erule_tac x="unat i" in allE)+,
              clarsimp,
              unat_arith)+

     apply wp
     apply unat_arith
    apply clarsimp
    apply (subgoal_tac "deref sa x = deref sa y")
     apply clarsimp
    apply (clarsimp simp: h_val_def)[1]
    apply (rule arg_cong[where f=from_bytes])
    apply (subst numeral_eqs(3))+
    apply simp
    apply (rule_tac x=0 in allE, assumption, erule impE, unat_arith)
    apply (rule_tac x=1 in allE, assumption, erule impE, unat_arith)
    apply (rule_tac x=2 in allE, assumption, erule impE, unat_arith)
    apply (rule_tac x=3 in allE, assumption, erule impE, unat_arith)
    apply (simp add:CTypesDefs.ptr_add_def)
    apply (simp add: add.commute from_bytes_eq)
   apply clarsimp
  apply (clarsimp simp:intvl_def disjoint_iff_not_equal)
  apply (drule_tac x=x and y=y and j="of_nat k" and i="of_nat ka" and n=2 in neq_imp_bytes_disjoint)
        apply assumption
       apply (case_tac "k = 0", clarsimp) (* insert "k > 0" *)
       apply (clarsimp simp:unat_of_nat_len)
      apply (case_tac "ka = 0", clarsimp)
      apply (clarsimp simp:unat_of_nat_len)
     apply assumption
    apply clarsimp+
  done

text \<open>The bytes at the pointer @{term p} are @{term bs}.\<close>
definition
  bytes_at :: "'a globals_scheme \<Rightarrow> 'b::c_type ptr \<Rightarrow> word8 list \<Rightarrow> bool"
where
  "bytes_at s p bs \<equiv> length bs = 0 \<or>
                      (length bs \<le> ADDR_MAX \<and> (\<forall>i \<in> {0..(length bs - 1)}. deref s (byte_cast p +\<^sub>p (of_nat i)) = bs ! i))"

lemma bytes_at_none[simp]: "bytes_at s p []"
  by (clarsimp simp:bytes_at_def)

text \<open>The bytes of typed pointer @{term p} are @{term bs}.\<close>
definition
  bytes_of :: "'a globals_scheme \<Rightarrow> 'b::c_type ptr \<Rightarrow> word8 list \<Rightarrow> bool"
where
  "bytes_of s p bs \<equiv> length bs = size_of TYPE('b) \<and> bytes_at s p bs"

text \<open>The bytes at a char pointer are just it dereferenced.\<close>
lemma bytes_of_char[simp]: "bytes_of s (p::8word ptr) bs = (length bs = 1 \<and> deref s p = hd bs)"
  apply (clarsimp simp:bytes_of_def bytes_at_def)
  apply (rule iffI)
   apply clarsimp
   apply (erule disjE)
    apply clarsimp+
   apply (rule hd_conv_nth[symmetric])
   apply clarsimp+
  apply (subgoal_tac "hd bs = bs ! 0")
   apply simp
  apply (rule hd_conv_nth)
  apply clarsimp
  done

text \<open>A pointer does not wrap around memory.\<close>
definition
  no_wrap :: "'a::c_type ptr \<Rightarrow> nat \<Rightarrow> bool"
where
  "no_wrap p sz \<equiv> 0 \<notin> {ptr_val p ..+ sz}"

text \<open>Two pointers do not overlap.\<close>
definition
  no_overlap :: "'a::c_type ptr \<Rightarrow> 'b::c_type ptr \<Rightarrow> nat \<Rightarrow> bool"
where
  "no_overlap p q sz \<equiv> {ptr_val p ..+ sz} \<inter> {ptr_val q ..+ sz} = {}"

lemma no_overlap_sym: "no_overlap x y = no_overlap y x"
  apply (rule ext)
  apply (clarsimp simp:no_overlap_def)
  by blast

(* FIXME: MOVE *)
lemma h_val_not_id:
  fixes x :: "'a::mem_type ptr"
    and y :: "'b::mem_type ptr"
  shows "{ptr_val x..+size_of TYPE('a)} \<inter> {ptr_val y..+size_of TYPE('b)} = {}
     \<Longrightarrow> h_val (hrs_mem (hrs_mem_update (heap_update x v) s)) y = h_val (hrs_mem s) y"
  apply (subst hrs_mem_heap_update[symmetric])
  apply (subst h_val_heap_update_disjoint)
   apply blast
  apply clarsimp
  done

definition
  update_bytes :: "'a globals_scheme \<Rightarrow> 'b::mem_type ptr \<Rightarrow> word8 list \<Rightarrow> 'a globals_scheme"
where
  "update_bytes s p bs \<equiv> s\<lparr>t_hrs_' := hrs_mem_update (heap_update_list (ptr_val p) bs) (t_hrs_' s)\<rparr>"

lemma the_horse_says_neigh: "(s\<lparr>t_hrs_' := x\<rparr> = s\<lparr>t_hrs_' := y\<rparr>) = (x = y)"
 by (metis (erased, lifting) globals.cases_scheme globals.select_convs(1) globals.update_convs(1))

lemma upto_singleton[simp]:"[x..x] = [x]"
  by (simp add: upto_rec1)

lemma update_bytes_ignore_ptr_coerce[simp]: "update_bytes s (ptr_coerce p) = update_bytes s p"
  by (clarsimp simp:update_bytes_def intro!:ext)

lemma hrs_mem_update_commute:
  "f \<circ> g = g \<circ> f \<Longrightarrow> hrs_mem_update f (hrs_mem_update g s) = hrs_mem_update g (hrs_mem_update f s)"
  by (metis (no_types, lifting) comp_eq_elim hrs_htd_def hrs_htd_mem_update hrs_mem_def hrs_mem_f prod.collapse)

lemma hrs_mem_update_collapse:
  "hrs_mem_update f (hrs_mem_update g s) = hrs_mem_update (f \<circ> g) s"
  by (metis comp_eq_dest_lhs hrs_htd_def hrs_htd_mem_update hrs_mem_def hrs_mem_f prod.collapse)

lemma update_bytes_reorder:
  "{ptr_val p..+length cs} \<inter> {ptr_val q..+length bs} = {} \<Longrightarrow>
      update_bytes (update_bytes s q bs) p cs = update_bytes (update_bytes s p cs) q bs"
  apply (clarsimp simp:update_bytes_def)
  apply (subst the_horse_says_neigh)
  apply (subst hrs_mem_update_commute)
   apply (clarsimp intro!:ext)
   apply (subst heap_update_list_commute)
    apply clarsimp+
  done

lemma lt_step_down: "\<lbrakk>(x::nat) < y; x = y - 1 \<longrightarrow> P; x < y - 1 \<longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by force

(* XXX: This proof makes me sad. *)
lemma under_uint_imp_no_overflow: "x < ADDR_MAX \<Longrightarrow> ((of_nat x)::addr) + 1 \<noteq> 0"
  apply (induct x)
   apply (clarsimp simp:UWORD_MAX_def)+
  apply unat_arith
  apply (clarsimp simp:UWORD_MAX_def)
  apply (cut_tac y=x and z="(of_nat (ADDR_MAX - 1))::addr" in le_unat_uoi)
   apply (clarsimp simp:UWORD_MAX_def)+
  done

lemma heap_update_list_append3:
  "1 + length ys < 2 ^ word_bits \<Longrightarrow>
    heap_update_list s (y # ys) hp = heap_update_list s [y] (heap_update_list (s + 1) ys hp)"
  apply clarsimp
  apply (subst heap_update_list_append2[where xs="[y]", simplified])
   apply clarsimp+
  done

lemma hrs_mem_update_cong': "f = g \<Longrightarrow> hrs_mem_update f s = hrs_mem_update g s"
  by presburger

lemma update_bytes_append: "length bs \<le> ADDR_MAX \<Longrightarrow>
  update_bytes s p (b # bs) = update_bytes (update_bytes s p [b]) (byte_cast p +\<^sub>p 1) bs"
  apply (clarsimp simp:update_bytes_def)
  apply (subst the_horse_says_neigh)
  apply (subst hrs_mem_update_commute)
   apply (rule ext)+
   apply simp
   apply (case_tac "xa = ptr_val p")
    apply (clarsimp simp:fun_upd_def)
    apply (subst heap_update_nmem_same)
     apply (clarsimp simp:intvl_def ptr_add_def)
     apply (subgoal_tac "k < ADDR_MAX")
      prefer 2
      apply unat_arith
     apply (drule under_uint_imp_no_overflow)
     apply unat_arith
    apply clarsimp
   apply (subst heap_update_list_update)
    apply simp
   apply (clarsimp simp:fun_upd_def)
  apply (subst hrs_mem_update_collapse)
  apply (rule hrs_mem_update_cong')
  apply (clarsimp simp:ptr_add_def)
  apply (rule ext)
  apply (cut_tac xs="[b]" and ys=bs and s="ptr_val p" and hp=x in heap_update_list_append)
  apply (clarsimp simp:fun_upd_def intro!:ext)
  apply (rule conjI)
   apply clarsimp
   apply (subst heap_update_nmem_same)
    apply (clarsimp simp:ptr_add_def intvl_def)
    apply (subgoal_tac "k < ADDR_MAX")
     prefer 2
     apply unat_arith
    apply (drule under_uint_imp_no_overflow)
    apply unat_arith
   apply clarsimp
  apply clarsimp
  apply (case_tac "xa \<in> {ptr_val p + 1..+length bs}")
  apply (subst heap_update_mem_same_point)
    apply simp
   apply (subgoal_tac "addr_card = ADDR_MAX + 1")
    apply clarsimp
   apply (clarsimp simp:addr_card UWORD_MAX_def)
  apply (subst heap_update_mem_same_point)
    apply simp
   apply (subgoal_tac "addr_card = ADDR_MAX + 1")
    apply clarsimp
   apply (clarsimp simp:addr_card UWORD_MAX_def)
  apply clarsimp
  apply (subst heap_update_nmem_same)
   apply clarsimp
  apply (subst heap_update_nmem_same)
   apply clarsimp+
  done

lemma update_bytes_postpend: "length bs = x + 1 \<Longrightarrow>
  update_bytes s p bs = update_bytes (update_bytes s p (take x bs)) (byte_cast p +\<^sub>p (of_nat x)) [bs ! x]"
  apply (clarsimp simp:update_bytes_def)
  apply (subst the_horse_says_neigh)
  apply (clarsimp simp:ptr_add_def)
  apply (subst heap_update_list_concat_fold_hrs_mem)
   apply clarsimp+
  by (metis append_eq_conv_conj append_self_conv hd_drop_conv_nth2 lessI take_hd_drop)

lemma h_val_not_id_general:
  fixes y :: "'a::mem_type ptr"
  shows "\<forall>i \<in> {0..+size_of TYPE('a)}. \<forall>g. f g (ptr_val y + i) = g (ptr_val y + i)
     \<Longrightarrow> h_val (hrs_mem (hrs_mem_update f s)) y = h_val (hrs_mem s) y"
  apply (subst hrs_mem_update)
  apply (clarsimp simp:h_val_def)
  apply (subgoal_tac "heap_list (f (hrs_mem s)) (size_of TYPE('a)) (ptr_val y) =
                      heap_list (hrs_mem s) (size_of TYPE('a)) (ptr_val y)")
   apply clarsimp
  apply (cut_tac h="f (hrs_mem s)" and p="ptr_val y" and n="size_of TYPE('a)"
                 and h'="hrs_mem s" in heap_list_h_eq2)
   apply (erule_tac x="x - ptr_val y" in  ballE)
    apply clarsimp
   apply (clarsimp simp:intvl_def)+
  done

lemma h_val_not_id_list:
  fixes y :: "'a::mem_type ptr"
  shows "{x..+length vs} \<inter> {ptr_val y..+size_of TYPE('a)} = {}
     \<Longrightarrow> h_val (hrs_mem (hrs_mem_update (heap_update_list x vs) s)) y = h_val (hrs_mem s) y"
  apply (subst h_val_not_id_general)
   apply clarsimp
   apply (metis (erased, hide_lams) disjoint_iff_not_equal heap_update_nmem_same intvlD intvlI
          monoid_add_class.add.left_neutral)
  apply clarsimp
  done

lemma h_val_id_update_bytes:
  fixes q :: "'a::mem_type ptr"
  shows "{ptr_val q..+size_of TYPE('a)} \<inter> {ptr_val p..+length bs} = {}
          \<Longrightarrow> deref (update_bytes s p bs) q = deref s q"
  apply (clarsimp simp:update_bytes_def)
  apply (subst h_val_not_id_list)
   apply blast
  by simp

lemma bytes_at_len: "bytes_at s p bs \<Longrightarrow> length bs \<le> ADDR_MAX"
  by (clarsimp simp:bytes_at_def, fastforce)

(* Another sad proof. *)
lemma le_uint_max_imp_id: "x \<le> ADDR_MAX \<Longrightarrow> unat ((of_nat x)::addr) = x"
  apply (induct x)
   apply (clarsimp simp: UWORD_MAX_def)+
  apply unat_arith
  apply clarsimp
  done

lemma update_bytes_id: "update_bytes s p [] = s"
  apply (clarsimp simp:update_bytes_def)
  apply (subst heap_update_list_base')
  by (simp add: hrs_mem_update_id3)

lemma a_horse_by_any_other_name: "t_hrs_'_update f s = s\<lparr>t_hrs_' := f (t_hrs_' s)\<rparr>"
  by auto

lemma heap_update_list_singleton: "heap_update_list p [x] = heap_update (Ptr p) x"
  apply (rule ext)
  by (metis heap_update_def ptr_val.simps to_bytes_word8)

lemma update_bytes_eq: "\<lbrakk>s = s'; p = p'; bs = bs'\<rbrakk> \<Longrightarrow> update_bytes s p bs = update_bytes s' p' bs'"
  by clarsimp

text \<open>
  Memcpy does what it says on the box.
\<close>
lemma memcpy_wp':
  fixes src :: "'a::mem_type ptr"
    and dst :: "'b::mem_type ptr"
  shows "\<forall>s0 bs.
  \<lbrace>\<lambda>s. s = s0 \<and> c_guard src \<and> c_guard dst \<and> sz = of_nat (length bs) \<and> bytes_at s src bs \<and>
       no_wrap src (unat sz) \<and> no_wrap dst (unat sz) \<and> no_overlap src dst (unat sz)\<rbrace>
    memcpy' (ptr_coerce dst) (ptr_coerce src) sz
  \<lbrace>\<lambda>r s. r = ptr_coerce dst \<and> bytes_at s dst bs \<and> s = update_bytes s0 dst bs\<rbrace>!"
  apply (rule allI)+
  apply (rule validNF_assume_pre)
  unfolding memcpy'_def
  apply clarsimp
  apply (subst whileLoop_add_inv[where
    I="\<lambda>i s. unat i \<le> unat sz \<and>
             bytes_at s dst (take (unat i) bs) \<and>
             bytes_at s src bs \<and>
             s = update_bytes s0 dst (take (unat i) bs)" and
    M="\<lambda>(i, s). unat sz - unat i"])
  apply wp
    apply clarsimp
    apply (rule conjI)
     apply unat_arith
    apply (rule conjI)
     apply (simp add:bytes_at_def)
     apply (case_tac "bs = []")
      apply (rule disjI1)
      apply clarsimp
     apply (rule disjI2)
     apply clarsimp
     apply (rule conjI)
      apply unat_arith
     apply clarsimp
     apply (case_tac "unat i = ia")
      apply clarsimp
      apply (subgoal_tac "int (unat i) = uint i")
       prefer 2
       apply (subst uint_nat)
       apply simp
      apply simp
      apply (subst h_val_id)
      apply (subst h_val_id_update_bytes)
       apply (clarsimp simp:no_overlap_def ptr_add_def)
       apply (subgoal_tac "{ptr_val src + i..+Suc 0} \<subseteq> {ptr_val src..+unat (of_nat_addr (length bs))}")
        prefer 2
        apply (clarsimp simp:intvl_def)
        apply (rule_tac x="unat i" in exI)
        apply unat_arith
       apply (subgoal_tac "{ptr_val dst..+unat i} \<subseteq> {ptr_val dst..+unat (of_nat_addr (length bs))}")
        prefer 2
        apply (clarsimp simp:intvl_def)
        apply (rule exI, rule conjI, rule refl)
        apply (simp add: unat_of_nat)
       apply blast
      apply (erule_tac x="unat i" and P="\<lambda>x. deref s0 (byte_cast src +\<^sub>p int x) = bs ! x" in ballE)
       apply clarsimp
       apply (subst nth_take)
        apply unat_arith
       apply simp
      apply (erule disjE)
       apply clarsimp+
     apply (erule disjE)
      apply (subgoal_tac "length bs \<noteq> 0")
       prefer 2
       apply clarsimp
      apply (case_tac "unat i = 0")
       apply unat_arith
      apply linarith
     apply (subst h_val_not_id)
      apply (clarsimp simp:ptr_add_def intvl_def)
      (* Isabelle, why do you have to make it so hard? *)
      apply (erule_tac P="unat (of_nat ia) = ia" in notE)
      apply (cut_tac y=ia and z="(of_nat ADDR_MAX)::addr" in le_unat_uoi)
       apply (subgoal_tac "unat ((of_nat ADDR_MAX)::addr) = ADDR_MAX")
        prefer 2
        apply (simp add: unat_of_nat)
       apply (simp add: unat_of_nat)
      apply clarsimp
     apply clarsimp
     apply (erule_tac x=ia and A="{0..min (length bs) (unat i) - Suc 0}" in ballE)
      apply clarsimp
      apply (subst nth_take, unat_arith)+
      apply simp
     apply clarsimp
     apply unat_arith
    apply (rule conjI)
     apply (clarsimp simp:bytes_at_def)
     apply (subst h_val_not_id)
      apply (clarsimp simp:no_overlap_def)
      apply (subgoal_tac "ptr_val (byte_cast dst +\<^sub>p uint i) \<in> {ptr_val dst..+unat (of_nat (length bs))}")
       prefer 2
       apply (clarsimp simp:ptr_add_def intvl_def)
       apply (rule_tac x="unat i" in exI)
       apply clarsimp
       apply unat_arith
      (* More or less symmetric subgoal *)
      apply (subgoal_tac "ptr_val (byte_cast src +\<^sub>p int ia) \<in> {ptr_val src..+unat ((of_nat (length bs))::addr)}")
       prefer 2
       apply (clarsimp simp:ptr_add_def intvl_def)
       apply (rule_tac x=ia in exI)
       apply clarsimp
       apply (subgoal_tac "unat ((of_nat (length bs))::addr) = length bs")
        apply clarsimp
        apply arith
       apply (cut_tac y="length bs" and z="(of_nat ADDR_MAX)::addr" in le_unat_uoi)
        apply (simp add: unat_of_nat)
       apply arith
      apply (clarsimp simp:intvl_def ptr_add_def)
      apply blast
     apply clarsimp
    apply (rule conjI)
     apply (subst h_val_id_update_bytes)
      apply (clarsimp simp:no_overlap_def ptr_add_def)
      apply (subgoal_tac "{ptr_val src + i..+Suc 0} \<subseteq> {ptr_val src..+unat (of_nat_addr (length bs))}")
       prefer 2
       apply (clarsimp simp:intvl_def)
       apply (rule_tac x="unat i" in exI)
       apply unat_arith
      apply (subgoal_tac "{ptr_val dst..+min (length bs) (unat i)} \<subseteq> {ptr_val dst..+unat (of_nat_addr (length bs))}")
       prefer 2
       apply (clarsimp simp:intvl_def)
       apply (rule_tac x=ka in exI)
       apply unat_arith
      apply blast
     apply (subgoal_tac "deref s0 (byte_cast src +\<^sub>p uint i) = bs ! (unat i)")
      apply clarsimp
      apply (subgoal_tac "update_bytes s0 dst (take (unat (i + 1)) bs) =
                          update_bytes (update_bytes s0 dst (take (unat i) bs)) (byte_cast dst +\<^sub>p uint i) [bs ! unat i]")
       apply clarsimp
       apply (subgoal_tac
               "\<forall>s'. t_hrs_'_update (hrs_mem_update (heap_update (byte_cast dst +\<^sub>p uint i) (bs ! unat i))) s' =
                     update_bytes s' (byte_cast dst +\<^sub>p uint i) [bs ! unat i]")
        apply fast
       apply (clarsimp simp:update_bytes_def)
       apply (subst a_horse_by_any_other_name)
       apply (subst the_horse_says_neigh)
       apply (clarsimp simp:ptr_add_def)
       apply (subst heap_update_list_singleton)
       apply simp
      apply (cut_tac s=s0 and p=dst and bs="take (unat (i + 1)) bs" and x="unat i"
                     in update_bytes_postpend)
       apply (subgoal_tac "unat (i + 1) \<le> length bs")
        apply clarsimp
        apply unat_arith
       apply (subgoal_tac "unat i < length bs")
        apply unat_arith
       apply (rule unat_less_helper)
       apply simp
      apply clarsimp
      apply (rule update_bytes_eq)
        apply (subgoal_tac "min (unat i) (unat (i + 1)) = unat i")
         apply clarsimp
        apply clarsimp
        apply unat_arith
       apply (clarsimp simp:ptr_add_def)
      apply clarsimp
      apply (rule nth_take)
      apply unat_arith
     apply (clarsimp simp:bytes_at_def)
     apply (erule disjE)
      apply clarsimp
     apply clarsimp
     apply (erule_tac x="unat i" in ballE)
      apply (subst (asm) uint_nat[symmetric])
      apply simp
     apply clarsimp
     apply (subgoal_tac "unat i < length bs")
      prefer 2
      apply (rule unat_less_helper)
      apply simp
     apply unat_arith
    apply (rule conjI)
     apply unat_arith
    apply (rule conjI)
     apply (rule byte_ptr_guarded)
     apply (clarsimp simp:no_wrap_def intvl_def ptr_add_def)
     apply (erule_tac x="unat i" in allE)
     apply clarsimp
    apply (rule byte_ptr_guarded)
    apply (clarsimp simp:no_wrap_def intvl_def ptr_add_def)
    apply (erule_tac x="unat i" and
                     P="\<lambda>x. ptr_val dst + ((of_nat x)::addr) = 0 \<longrightarrow> \<not> x < unat ((of_nat_addr (length bs))::addr)"
                    in allE)
    apply clarsimp
   apply clarsimp
   apply (rule conjI)
    apply (subgoal_tac "unat i = length bs")
     apply clarsimp
    apply (case_tac "length bs = 0")
     apply clarsimp
    apply (subgoal_tac "length bs \<le> ADDR_MAX")
     prefer 2
     apply (clarsimp simp:bytes_at_def)
    (* XXX: We keep introducing this subgoal; we should do it once and for all up top. *)
    apply (subgoal_tac "unat ((of_nat (length bs))::addr) = length bs")
     prefer 2
     apply (cut_tac y="length bs" and z="(of_nat ADDR_MAX)::addr" in le_unat_uoi)
      apply (clarsimp simp:UWORD_MAX_def)
     apply clarsimp+
    apply unat_arith
   (* insert a bunch a tedium... *)
   apply (subgoal_tac "unat i = length bs")
    prefer 2
    apply (drule bytes_at_len)
    apply (subgoal_tac "unat (of_nat_addr (length bs)) = length bs")
     prefer 2
     apply (rule le_uint_max_imp_id)
     apply simp
    apply unat_arith
   apply clarsimp
  apply (simp add:update_bytes_id)
  done

lemma validNF_make_schematic_post':
  "(\<forall>s0 x. \<lbrace> \<lambda>s. P s0 x s \<rbrace> f \<lbrace> \<lambda>rv s. Q s0 x rv s \<rbrace>!) \<Longrightarrow>
   \<lbrace> \<lambda>s. \<exists>s0 x. P s0 x s \<and> (\<forall>rv s'. Q s0 x rv s' \<longrightarrow> Q' rv s') \<rbrace> f \<lbrace> Q'\<rbrace>!"
  by (auto simp add: valid_def validNF_def no_fail_def split: prod.splits)

lemmas memcpy_wp = memcpy_wp'[THEN validNF_make_schematic_post', simplified]

lemma h_val_not_id_update_bytes:
  fixes q :: "'a::mem_type ptr"
  shows "\<lbrakk>ptr_val p = ptr_val q; length bs = size_of TYPE('a)\<rbrakk> \<Longrightarrow>
            deref (update_bytes s p bs) q = from_bytes bs"
  apply (clarsimp simp:update_bytes_def h_val_def)
  apply (subst hrs_mem_update)
  apply (cut_tac p="ptr_val q" and v=bs and h="hrs_mem (t_hrs_' s)" in heap_list_update)
   apply clarsimp
   apply (metis less_imp_le max_size)
  by clarsimp

text \<open>
  Test that we can use memcpy in a compositional proof. The following proof can be done much more
  pleasantly, but we're just trying to check that the memcpy WP lemma is usable.
  TODO: This relies on disabling heap abstraction for the calling function as well. We should be
  able to phrase an exec_concrete WP lemma over memcpy that lets us prove properties about
  heap-abstracted callers. This will need AutoCorres support to connect is_valid_* with
  c_guard/no_overlap/no_wrap.
\<close>

definition
  memcpy_int_spec :: "sword32 ptr \<Rightarrow> sword32 ptr \<Rightarrow> bool"
where
  "memcpy_int_spec dst src \<equiv>
    \<forall>x. \<lbrace>\<lambda>s. deref s src = x \<and>
             {ptr_val src..+4} \<inter> {ptr_val dst..+4} = {} \<and>
             c_guard src \<and> c_guard dst \<and>
             no_wrap src 4 \<and> no_wrap dst 4\<rbrace>
          memcpy_int' dst src
        \<lbrace>\<lambda>_ s. deref s dst = x\<rbrace>!"

lemma memcpy_int_wp'[unfolded memcpy_int_spec_def]: "memcpy_int_spec dst src"
  unfolding memcpy_int_spec_def
  apply (rule allI)
  unfolding memcpy_int'_def
  apply (wp memcpy_wp)
  apply clarsimp
  apply (rule_tac x="[deref s (byte_cast src),
                      deref s (byte_cast src +\<^sub>p 1),
                      deref s (byte_cast src +\<^sub>p 2),
                      deref s (byte_cast src +\<^sub>p 3)]" in exI)
  apply (clarsimp simp:bytes_at_def no_overlap_def UINT_MAX_def)
  apply (rule conjI)
   apply clarsimp
   apply (case_tac "i = 0", clarsimp)
   apply (case_tac "i = 1", clarsimp)
   apply (case_tac "i = 2", clarsimp)
   apply (case_tac "i = 3", clarsimp)
   apply clarsimp
  apply clarsimp
  apply (subst h_val_not_id_update_bytes)
    apply clarsimp+
  apply (clarsimp simp:h_val_def)
  apply (subgoal_tac "heap_list (hrs_mem (t_hrs_' s)) 4 (ptr_val src) =
                      deref s (byte_cast src) # (heap_list (hrs_mem (t_hrs_' s)) 3 (ptr_val src + 1))")
   prefer 2
   apply (clarsimp simp:h_val_def)
   apply (metis Suc_numeral from_bytes_eq heap_list_rec semiring_norm(2) semiring_norm(8))
  apply (subgoal_tac "heap_list (hrs_mem (t_hrs_' s)) 3 (ptr_val src + 1) =
                      deref s (byte_cast src +\<^sub>p 1) # (heap_list (hrs_mem (t_hrs_' s)) 2 (ptr_val src + 2))")
   prefer 2
   apply (clarsimp simp:h_val_def ptr_add_def)
   apply (cut_tac h="hrs_mem (t_hrs_' s)" and p="ptr_val src + 1" and n=2 in heap_list_rec)
   apply clarsimp
   apply (simp add: add.commute from_bytes_eq)
  apply clarsimp
  apply (subgoal_tac "heap_list (hrs_mem (t_hrs_' s)) 2 (ptr_val src + 2) =
                      deref s (byte_cast src +\<^sub>p 2) # (heap_list (hrs_mem (t_hrs_' s)) 1 (ptr_val src + 3))")
   prefer 2
   apply (cut_tac h="hrs_mem (t_hrs_' s)" and p="ptr_val src + 2" and n=3 in heap_list_rec)
   apply (clarsimp simp:h_val_def ptr_add_def from_bytes_eq)
   apply (metis (no_types, hide_lams) Suc_eq_plus1 heap_list_base heap_list_rec is_num_normalize(1)
                monoid_add_class.add.left_neutral one_add_one one_plus_numeral semiring_norm(3))
  apply (clarsimp simp:h_val_def ptr_add_def from_bytes_eq)
  done

text \<open>memcpying a typed variable is equivalent to assignment.\<close>
lemma memcpy_type_wp':
  fixes dst :: "'a::mem_type ptr"
    and src :: "'a::mem_type ptr"
  shows "\<forall>s0 bs.
   \<lbrace>\<lambda>s. s = s0 \<and> c_guard dst \<and> c_guard src \<and> sz = of_nat (size_of TYPE('a)) \<and>
        no_overlap dst src (unat sz) \<and> no_wrap dst (unat sz) \<and> no_wrap src (unat sz) \<and>
        bytes_of s src bs\<rbrace>
     memcpy' (ptr_coerce dst) (ptr_coerce src) sz
   \<lbrace>\<lambda>r s. r = ptr_coerce dst \<and> bytes_of s dst bs \<and> s = update_bytes s0 dst bs\<rbrace>!"
  apply (rule allI)+
  apply (wp memcpy_wp)
  apply clarsimp
  apply (rule_tac x=bs in exI)
  apply clarsimp
  apply (subst no_overlap_sym)
  apply (clarsimp simp:bytes_of_def)
  done

lemmas memcpy_type_wp = memcpy_type_wp'[THEN validNF_make_schematic_post', simplified]

text \<open>Confirm that we can also prove memcpy_int using the previous generic lemma.\<close>
lemma memcpy_int_wp''[unfolded memcpy_int_spec_def]: "memcpy_int_spec dst src"
  unfolding memcpy_int_spec_def memcpy_int'_def
  apply (rule allI)
  apply (wp memcpy_type_wp)
  (* Remainder mostly clagged from the original proof above. *)
  apply clarsimp
  apply (rule conjI, clarsimp simp:no_overlap_def, blast)
  apply (rule_tac x="[deref s (byte_cast src),
                      deref s (byte_cast src +\<^sub>p 1),
                      deref s (byte_cast src +\<^sub>p 2),
                      deref s (byte_cast src +\<^sub>p 3)]" in exI)
  apply (rule conjI)
   apply (clarsimp simp:bytes_of_def bytes_at_def UINT_MAX_def)
   apply (case_tac "i = 0", clarsimp)
   apply (case_tac "i = 1", clarsimp)
   apply (case_tac "i = 2", clarsimp)
   apply (case_tac "i = 3", clarsimp)
   apply clarsimp
  apply clarsimp
  apply (subst h_val_not_id_update_bytes, clarsimp+)
  apply (clarsimp simp:h_val_def)
  apply (subgoal_tac "heap_list (hrs_mem (t_hrs_' s)) 4 (ptr_val src) =
                      deref s (byte_cast src) # (heap_list (hrs_mem (t_hrs_' s)) 3 (ptr_val src + 1))")
   prefer 2
   apply (clarsimp simp:h_val_def from_bytes_eq)
   apply (subst heap_list_rec[symmetric])
   apply simp
  apply (subgoal_tac "heap_list (hrs_mem (t_hrs_' s)) 3 (ptr_val src + 1) =
                      deref s (byte_cast src +\<^sub>p 1) # (heap_list (hrs_mem (t_hrs_' s)) 2 (ptr_val src + 2))")
   prefer 2
   apply (clarsimp simp:h_val_def ptr_add_def)
   apply (cut_tac h="hrs_mem (t_hrs_' s)" and p="ptr_val src + 1" and n=2 in heap_list_rec)
   apply (clarsimp simp: from_bytes_eq)
   apply (metis add.commute)
  apply clarsimp
  apply (subgoal_tac "heap_list (hrs_mem (t_hrs_' s)) 2 (ptr_val src + 2) =
                      deref s (byte_cast src +\<^sub>p 2) # (heap_list (hrs_mem (t_hrs_' s)) 1 (ptr_val src + 3))")
   prefer 2
   apply (cut_tac h="hrs_mem (t_hrs_' s)" and p="ptr_val src + 2" and n=3 in heap_list_rec)
   apply (clarsimp simp:h_val_def ptr_add_def from_bytes_eq)
   apply (metis (no_types, hide_lams) Suc_eq_plus1 heap_list_base heap_list_rec is_num_normalize(1)
                monoid_add_class.add.left_neutral one_add_one one_plus_numeral semiring_norm(3))
  apply (clarsimp simp:h_val_def ptr_add_def from_bytes_eq)
  done

lemma bytes_of_imp_at[simp]: "bytes_of s x bs \<Longrightarrow> bytes_at s x bs"
  by (clarsimp simp:bytes_of_def bytes_at_def)

lemma bytes_at_imp_of:
  fixes x :: "'a::mem_type ptr"
  shows "\<lbrakk>bytes_at s x bs; length bs = size_of TYPE('a)\<rbrakk> \<Longrightarrow> bytes_of s x bs"
  by (clarsimp simp:bytes_of_def bytes_at_def)

text \<open>
  Memcpying from a source to a destination via an intermediary does what it should. This is close to
  the desirable property we want for CAmkES systems; i.e. that copying into your IPC buffer on one
  side and then out on the other gives you back what you put in. Note that the type of the
  intermediate pointer is irrelevant and we don't need to assume that the source and final
  destination do not overlap.
\<close>
lemma memcpy_seq:
  fixes x :: "'a::mem_type ptr"
    and y :: "'b::mem_type ptr"
    and z :: "'a::mem_type ptr"
  shows "\<forall>s0 bs.
   \<lbrace>\<lambda>s. s = s0 \<and> sz = of_nat (size_of TYPE('a)) \<and>
        c_guard x \<and> c_guard y \<and> c_guard z \<and>
        no_wrap x (unat sz) \<and> no_wrap y (unat sz) \<and> no_wrap z (unat sz) \<and>
        no_overlap x y (unat sz) \<and> no_overlap y z (unat sz) \<and>
        bytes_of s x bs\<rbrace>
    do memcpy' (ptr_coerce y) (ptr_coerce x) sz;
       memcpy' (ptr_coerce z) (ptr_coerce y) sz
    od
   \<lbrace>\<lambda>r s. r = ptr_coerce z \<and> bytes_of s z bs\<rbrace>!"
  apply (rule allI)+
  apply (wp memcpy_wp)
  apply clarsimp
  apply (rule_tac x=bs in exI)
  apply clarsimp
  apply (rule conjI, clarsimp simp:bytes_of_def)
  apply clarsimp
  apply (rule_tac x=bs in exI)
  apply (rule conjI, clarsimp simp:bytes_of_def)
  apply clarsimp
  apply (rule bytes_at_imp_of)
   apply (clarsimp simp:bytes_of_def)+
  done

lemma update_ti_eq:
  fixes x :: "'a::mem_type"
    and y :: 'a
  shows "\<lbrakk>length bs = size_of TYPE('a); bs = bs'\<rbrakk>
          \<Longrightarrow> update_ti_t (typ_info_t TYPE('a)) bs x = update_ti_t (typ_info_t TYPE('a)) bs' y"
  by (clarsimp simp:upd)

lemma from_bytes_cong: "x = y \<Longrightarrow> from_bytes x = from_bytes y"
  by simp

declare from_bytes_eq [simp]

text \<open>
  If you dereference a pointer, the value you get is the same as the underlying bytes backing that
  memory.
\<close>
lemma val_eq_bytes:
  fixes x :: "'a::mem_type ptr"
  shows "deref s x = from_bytes (map (\<lambda>off. deref s (byte_cast x +\<^sub>p of_nat off)) [0..<size_of TYPE('a)])"
  apply (clarsimp simp:h_val_def ptr_add_def)
  apply (rule from_bytes_cong)
  apply (rule nth_equalityI)
   apply clarsimp+
  apply (subst heap_list_nth)
   apply clarsimp+
  done

lemma extract_list_elem: "i < n \<Longrightarrow> f i = (map f [0..<n]) ! i"
  apply (induct i)
   apply clarsimp+
  done

lemma update_deref:
  fixes x :: "'a::mem_type ptr"
  shows "size_of TYPE('a) = length bs \<Longrightarrow> deref (update_bytes s x bs) x = from_bytes bs"
  apply (clarsimp simp:update_bytes_def)
  apply (subst hrs_mem_update)
  apply (clarsimp simp:h_val_def)
  apply (subst heap_list_update)
   apply (metis less_imp_le max_size)
  apply clarsimp
  done

text \<open>
  The memcpy_int proof can now be completed more elegantly. Note that the body of this proof is more
  generic than the previous attempts and doesn't involve manually reasoning about each byte.
\<close>
lemma memcpy_int_wp'''[unfolded memcpy_int_spec_def]: "memcpy_int_spec dst src"
  unfolding memcpy_int_spec_def memcpy_int'_def
  apply (rule allI)
  apply (wp memcpy_type_wp)
  apply clarsimp
  apply (rule conjI, clarsimp simp:no_overlap_def, blast)
  apply (rule_tac x="map (\<lambda>i. deref s (byte_cast src +\<^sub>p of_nat i)) [0..<size_of TYPE(32sword)]" in exI)
  apply (rule conjI)
   apply (clarsimp simp:bytes_of_def bytes_at_def UINT_MAX_def)+
  apply (subst update_deref)
   apply clarsimp
  apply (cut_tac s=s and x=src in val_eq_bytes)
  apply clarsimp
  done

lemma bytes_at_heap_list:
  fixes x :: "'a::mem_type ptr"
  shows "\<lbrakk>n \<le> ADDR_MAX; no_wrap x n\<rbrakk>
          \<Longrightarrow> bytes_at s x (heap_list (hrs_mem (t_hrs_' s)) n (ptr_val x))"
  apply (clarsimp simp:bytes_at_def ptr_add_def h_val_def)
  apply (subst heap_list_nth)
   apply unat_arith
  apply clarsimp
  done

text \<open>
  A collection of useful type-generic implications for moving from the abstract heap to the concrete
  heap.
\<close>
definition
  is_valid_imp_c_guard :: "(lifted_globals \<Rightarrow> 'b::mem_type ptr \<Rightarrow> bool) \<Rightarrow> bool"
where
  "is_valid_imp_c_guard is_valid \<equiv> \<forall>s p. is_valid (lift_global_heap s) p \<longrightarrow> c_guard p"
definition
  is_valid_imp_no_null :: "(lifted_globals \<Rightarrow> 'b::mem_type ptr \<Rightarrow> bool) \<Rightarrow> bool"
where
  "is_valid_imp_no_null is_valid \<equiv>
     \<forall>s p. is_valid (lift_global_heap s) p \<longrightarrow> 0 \<notin> {ptr_val p..of_nat (size_of TYPE('b))}"
definition
  is_valid_imp_no_wrap :: "(lifted_globals \<Rightarrow> 'b::mem_type ptr \<Rightarrow> bool) \<Rightarrow> bool"
where
  "is_valid_imp_no_wrap is_valid \<equiv>
     \<forall>s p. is_valid (lift_global_heap s) p \<longrightarrow> no_wrap p (size_of TYPE('b))"
definition
  is_valid_imp_no_overlap :: "(lifted_globals \<Rightarrow> 'b::mem_type ptr \<Rightarrow> bool) \<Rightarrow> bool"
where
  "is_valid_imp_no_overlap is_valid \<equiv>
     \<forall>s p q. is_valid (lift_global_heap s) p \<and> is_valid (lift_global_heap s) q \<and> p \<noteq> q
               \<longrightarrow> no_overlap p q (size_of TYPE('b))"
definition
  is_valid_imp_heap_ptr_valid :: "(lifted_globals \<Rightarrow> 'b::mem_type ptr \<Rightarrow> bool) \<Rightarrow> bool"
where
  "is_valid_imp_heap_ptr_valid is_valid \<equiv>
     \<forall>s p. is_valid (lift_global_heap s) p \<longrightarrow> heap_ptr_valid (hrs_htd (t_hrs_' s)) p"

text \<open>We can easily discharge these for a given type.\<close>
lemma is_valid_w32_imp_c_guard[unfolded is_valid_imp_c_guard_def, simplified]:
    "is_valid_imp_c_guard is_valid_w32"
  unfolding is_valid_imp_c_guard_def
  apply clarsimp
  apply (subst (asm) lifted_globals_ext_simps)
  apply clarsimp
  apply (rule simple_lift_c_guard, force)
  done

lemma is_valid_w32_imp_no_null[unfolded is_valid_imp_no_null_def, simplified]:
    "is_valid_imp_no_null is_valid_w32"
  unfolding is_valid_imp_no_null_def
  apply clarsimp
  apply (subst (asm) lifted_globals_ext_simps)
  apply clarsimp
  apply (drule simple_lift_c_guard)
  apply (clarsimp simp:c_guard_def c_null_guard_def intvl_def)
  by force

lemma is_valid_w32_imp_no_wrap[unfolded is_valid_imp_no_wrap_def, simplified]:
    "is_valid_imp_no_wrap is_valid_w32"
  unfolding is_valid_imp_no_wrap_def no_wrap_def
  apply clarsimp
  apply (subst (asm) lifted_globals_ext_simps)
  apply clarsimp
  apply (drule simple_lift_c_guard)
  apply (clarsimp simp:c_guard_def c_null_guard_def intvl_def)
  done

lemma is_valid_w32_imp_no_overlap[unfolded is_valid_imp_no_overlap_def, simplified]:
    "is_valid_imp_no_overlap is_valid_w32"
  unfolding is_valid_imp_no_overlap_def no_wrap_def
  apply clarsimp
  apply (subst (asm) lifted_globals_ext_simps)+
  apply clarsimp
  apply (drule simple_lift_heap_ptr_valid)+
  apply (clarsimp simp:no_overlap_def)
  apply (cut_tac p=p and q=q and d="hrs_htd (t_hrs_' s)" in heap_ptr_valid_neq_disjoint)
     apply clarsimp+
  done

lemma is_valid_w32_imp_heap_ptr_valid[unfolded is_valid_imp_heap_ptr_valid_def, simplified]:
    "is_valid_imp_heap_ptr_valid is_valid_w32"
  unfolding is_valid_imp_heap_ptr_valid_def
  apply clarsimp
  apply (subst (asm) lifted_globals_ext_simps)
  apply clarsimp
  by (rule simple_lift_heap_ptr_valid, force)

text \<open>
  With that support in place, we can now prove a heap-abstracted call to memcpy of a type in a
  reasonably generic way. Note that we leverage the relationship between
  is_valid_*/lift_global_heap/simple_lift to transfer assumptions across the boundary between the
  abstract and concrete heaps.
\<close>
lemma
  fixes dst :: "32word ptr"
    and src :: "32word ptr"
  shows "\<forall>s0 x.
   \<lbrace>\<lambda>s. s = s0 \<and> is_valid_w32 s dst \<and> is_valid_w32 s src \<and> sz = of_nat (size_of TYPE(32word)) \<and>
        heap_w32 s src = x \<and> dst \<noteq> src\<rbrace>
     exec_concrete lift_global_heap (memcpy' (ptr_coerce dst) (ptr_coerce src) sz)
   \<lbrace>\<lambda>r s. r = ptr_coerce dst \<and> heap_w32 s dst = x\<rbrace>!"
  including nf_no_pre
  apply (rule allI)+
  apply (wp memcpy_wp)
  apply (clarsimp simp:is_valid_w32_imp_c_guard
                       is_valid_w32_imp_no_wrap
                       is_valid_w32_imp_no_overlap)
  apply (rule_tac x="map (\<lambda>i. deref s (byte_cast src +\<^sub>p of_nat i)) [0..<size_of TYPE(32word)]" in exI)
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp:bytes_at_def UINT_MAX_def)
  apply clarsimp
  apply (subst lifted_globals_ext_simps(3))+
  apply (clarsimp simp:simple_lift_def is_valid_w32_imp_heap_ptr_valid)
  apply (rule conjI)
   apply clarsimp
   apply (subst update_deref)
    apply clarsimp+
   apply (cut_tac s=s and x=src in val_eq_bytes)
   apply clarsimp
  apply (clarsimp simp:update_bytes_def is_valid_w32_imp_heap_ptr_valid)
  done

text \<open>
  Let's do the same instantiation for a structure. Note that the proof text for the following lemmas
  is identical to the word 32 instantiation above. These could be straightforwardly abstracted into
  a locale which could be automatically interpreted with the use of generated proofs.
\<close>
lemma is_valid_my_structure_imp_c_guard[unfolded is_valid_imp_c_guard_def, simplified]:
    "is_valid_imp_c_guard is_valid_my_structure_C"
  unfolding is_valid_imp_c_guard_def
  apply clarsimp
  apply (subst (asm) lifted_globals_ext_simps)
  apply clarsimp
  apply (rule simple_lift_c_guard, force)
  done

lemma is_valid_my_structure_imp_no_null[unfolded is_valid_imp_no_null_def, simplified]:
    "is_valid_imp_no_null is_valid_my_structure_C"
  unfolding is_valid_imp_no_null_def
  apply clarsimp
  apply (subst (asm) lifted_globals_ext_simps)
  apply clarsimp
  apply (drule simple_lift_c_guard)
  apply (clarsimp simp:c_guard_def c_null_guard_def intvl_def)
  by force

lemma is_valid_my_structure_imp_no_wrap[unfolded is_valid_imp_no_wrap_def, simplified]:
    "is_valid_imp_no_wrap is_valid_my_structure_C"
  unfolding is_valid_imp_no_wrap_def no_wrap_def
  apply clarsimp
  apply (subst (asm) lifted_globals_ext_simps)
  apply clarsimp
  apply (drule simple_lift_c_guard)
  apply (clarsimp simp:c_guard_def c_null_guard_def intvl_def)
  done

lemma is_valid_my_structure_imp_no_overlap[unfolded is_valid_imp_no_overlap_def, simplified]:
    "is_valid_imp_no_overlap is_valid_my_structure_C"
  unfolding is_valid_imp_no_overlap_def no_wrap_def
  apply clarsimp
  apply (subst (asm) lifted_globals_ext_simps)+
  apply clarsimp
  apply (drule simple_lift_heap_ptr_valid)+
  apply (clarsimp simp:no_overlap_def)
  apply (cut_tac p=p and q=q and d="hrs_htd (t_hrs_' s)" in heap_ptr_valid_neq_disjoint)
     apply clarsimp+
  done

lemma is_valid_my_structure_imp_heap_ptr_valid[unfolded is_valid_imp_heap_ptr_valid_def, simplified]:
    "is_valid_imp_heap_ptr_valid is_valid_my_structure_C"
  unfolding is_valid_imp_heap_ptr_valid_def
  apply clarsimp
  apply (subst (asm) lifted_globals_ext_simps)
  apply clarsimp
  by (rule simple_lift_heap_ptr_valid, force)

text \<open>
  Again, we can now trivially transfer Hoare triple properties.
\<close>
lemma
  fixes dst :: "my_structure_C ptr"
    and src :: "my_structure_C ptr"
  shows "\<forall>s0 x.
   \<lbrace>\<lambda>s. s = s0 \<and> is_valid_my_structure_C s dst \<and> is_valid_my_structure_C s src \<and>
        heap_my_structure_C s src = x \<and> dst \<noteq> src\<rbrace>
     memcpy_struct' dst src
   \<lbrace>\<lambda>r s. r = dst \<and> heap_my_structure_C s dst = x\<rbrace>!"
  including nf_no_pre
  apply (rule allI)+
  unfolding memcpy_struct'_def
  apply (wp memcpy_wp)
  apply (clarsimp simp:is_valid_my_structure_imp_c_guard)
  apply (rule_tac x="map (\<lambda>i. deref s (byte_cast src +\<^sub>p of_nat i)) [0..<size_of TYPE(my_structure_C)]" in exI)
  apply (clarsimp simp:is_valid_my_structure_imp_no_wrap is_valid_my_structure_imp_no_overlap)
  apply (rule conjI)
   apply (clarsimp simp:bytes_at_def UINT_MAX_def)
  apply clarsimp
  apply (subst lifted_globals_ext_simps)+
  apply (clarsimp simp:simple_lift_def is_valid_my_structure_imp_heap_ptr_valid)
  apply (rule conjI)
   apply clarsimp
   apply (subst update_deref)
    apply clarsimp
   apply (cut_tac s=s and x=src in val_eq_bytes)
   apply clarsimp
  apply (clarsimp simp:update_bytes_def is_valid_my_structure_imp_heap_ptr_valid)
  done

end

end
