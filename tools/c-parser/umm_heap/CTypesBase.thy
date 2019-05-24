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

(*
  Structures supporting CTypes.
  Primarily sets up types, defines pointers and the raw heap view.
*)

theory CTypesBase
imports
  "./$L4V_ARCH/Addr_Type"
  "HOL-Library.Prefix_Order"
  "Word_Lib.Signed_Words"
begin

section "Type setup"

type_synonym byte = "8 word"

class unit_class =
  assumes there_is_only_one: "x = y"

instantiation unit :: unit_class
begin
instance by (intro_classes, simp)
end

subsection "Pointers"

datatype 'a ptr = Ptr addr

abbreviation
  NULL :: "'a ptr" where
  "NULL \<equiv> Ptr 0"

ML \<open>
structure Ptr_Syntax =
struct

  val show_ptr_types = Attrib.setup_config_bool @{binding show_ptr_types} (K true)

  fun ptr_tr' cnst ctxt typ ts = if Config.get ctxt show_ptr_types then
      case Term.strip_type typ of
        ([@{typ addr}], Type (@{type_name "ptr"}, [T])) =>
          list_comb
            (Syntax.const cnst $ Syntax_Phases.term_of_typ ctxt T
            , ts)
        | _ => raise Match
  else raise Match

  fun ptr_coerce_tr' cnst ctxt typ ts = if Config.get ctxt show_ptr_types then
      case Term.strip_type typ of
        ([Type (@{type_name ptr}, [S])], Type (@{type_name "ptr"}, [T])) =>
          list_comb
            (Syntax.const cnst $ Syntax_Phases.term_of_typ ctxt S
                               $ Syntax_Phases.term_of_typ ctxt T
            , ts)
        | _ => raise Match
  else raise Match
end
\<close>

syntax
  "_Ptr" :: "type \<Rightarrow> logic" ("(1PTR/(1'(_')))")
translations
  "PTR('a)" => "CONST Ptr :: (addr \<Rightarrow> 'a ptr)"
typed_print_translation
  \<open> [(@{const_syntax Ptr}, Ptr_Syntax.ptr_tr' @{syntax_const "_Ptr"})] \<close>

primrec
  ptr_val :: "'a ptr \<Rightarrow> addr"
where
  ptr_val_def: "ptr_val (Ptr a) = a"

primrec
  ptr_coerce :: "'a ptr \<Rightarrow> 'b ptr" where
  "ptr_coerce (Ptr a) = Ptr a"

syntax
  "_Ptr_coerce" :: "type \<Rightarrow> type \<Rightarrow> logic" ("(1PTR'_COERCE/(1'(_ \<rightarrow> _')))")
translations
  "PTR_COERCE('a \<rightarrow> 'b)" => "CONST ptr_coerce :: ('a ptr \<Rightarrow> 'b ptr)"
typed_print_translation
  \<open> [(@{const_syntax ptr_coerce}, Ptr_Syntax.ptr_coerce_tr' @{syntax_const "_Ptr_coerce"})] \<close>

definition
  (* no ctype/memtype-class constraints on these so as to allow comparison of
     void * pointers, which are represented as Isabelle type unit ptr *)
  ptr_less :: "'a ptr \<Rightarrow> 'a ptr \<Rightarrow> bool" (infixl "<\<^sub>p" 50) where
  "p <\<^sub>p q \<equiv> ptr_val p < ptr_val q"

definition
  ptr_le :: "'a ptr \<Rightarrow> 'a ptr \<Rightarrow> bool" (infixl "\<le>\<^sub>p" 50) where
  "p \<le>\<^sub>p q \<equiv> ptr_val p \<le> ptr_val q"

instantiation ptr :: (type) ord
begin

definition
  ptr_less_def': "p < q \<equiv> p <\<^sub>p q"
definition
  ptr_le_def': "p \<le> q \<equiv> p \<le>\<^sub>p q"

instance ..

end

lemma ptr_val_case: "ptr_val p = (case p of Ptr v \<Rightarrow> v)"
  by (cases p) simp

instantiation ptr :: (type) linorder
begin
instance
  by (intro_classes)
     (unfold ptr_le_def' ptr_le_def ptr_less_def' ptr_less_def ptr_val_case,
      auto split: ptr.splits)
end

subsection "Raw heap"

text \<open>A raw map from addresses to bytes\<close>

type_synonym heap_mem = "addr \<Rightarrow> byte"

text \<open>For heap h, pointer p and nat n, (heap_list h n p) returns the list
        of bytes in the heap taken from addresses {p..+n}\<close>

primrec
  heap_list :: "heap_mem \<Rightarrow> nat \<Rightarrow> addr \<Rightarrow> byte list"
where
  heap_list_base: "heap_list h 0 p = []"
| heap_list_rec:  "heap_list h (Suc n) p = h p # heap_list h n (p + 1)"


section "Intervals"

text \<open>
  For word a and nat b, {a..+b} is the set of words x,
  with unat (x - a) < b.\<close>

definition
  intvl :: "'a::len word \<times> nat \<Rightarrow> 'a::len word set" where
  "intvl x \<equiv> {z. \<exists>k. z = fst x + of_nat k \<and> k < snd x}"

abbreviation
  "intvl_abbr" :: "'a::len word \<Rightarrow> nat \<Rightarrow> 'a word set" ("{_..+_}") where
  "{a..+b} \<equiv> intvl (a,b)"


section "dt_pair: a reimplementation of 2 item tuples"

datatype
    ('a,'b) dt_pair = DTPair 'a 'b

primrec
  dt_fst :: "('a,'b) dt_pair \<Rightarrow> 'a"
where
  "dt_fst (DTPair a b) = a"

primrec
  dt_snd :: "('a,'b) dt_pair \<Rightarrow> 'b"
where
  "dt_snd (DTPair a b) = b"


lemma split_DTPair_All:
  "(\<forall>x. P x) = (\<forall>a b. P (DTPair a b))"
  by (rule iffI; clarsimp) (case_tac x, simp)

lemma surjective_dt_pair:
  "p = DTPair (dt_fst p) (dt_snd p)"
  by (cases p) simp

lemmas dt_pair_collapse [simp] = surjective_dt_pair[symmetric]

lemma split_DTPair_all[no_atp]: "(\<And>x. PROP P x) \<equiv> (\<And>a b. PROP P (DTPair a b))"
proof
  fix a b
  assume "\<And>x. PROP P x"
  then show "PROP P (DTPair a b)" .
next
  fix x
  assume "\<And>a b. PROP P (DTPair a b)"
  from \<open>PROP P (DTPair (dt_fst x) (dt_snd x))\<close> show "PROP P x" by simp
qed


type_synonym normalisor = "byte list \<Rightarrow> byte list"


section "Properties of pointers"

lemma Ptr_ptr_val [simp]:
  "Ptr (ptr_val p) = p"
  by (case_tac p) simp

lemma ptr_val_ptr_coerce [simp]:
  "ptr_val (ptr_coerce p) = ptr_val p"
  by (case_tac p) simp

lemma Ptr_ptr_coerce [simp]:
  "Ptr (ptr_val p) = ptr_coerce p"
  by (case_tac p) simp

lemma ptr_coerce_id [simp]:
  "ptr_coerce p = p"
  by (case_tac p) simp

lemma ptr_coerce_idem [simp]:
  "ptr_coerce (ptr_coerce p) = ptr_coerce p"
  by (case_tac p) simp

lemma ptr_val_inj [simp]:
  "(ptr_val p = ptr_val q) = (p = q)"
  by (case_tac p, case_tac q) auto

lemma ptr_coerce_NULL [simp]:
  "(ptr_coerce p = NULL) = (p = NULL)"
  by (case_tac p) simp

lemma NULL_ptr_val:
  "(p = NULL) = (ptr_val p = 0)"
  by (case_tac p) simp

instantiation ptr :: (type) finite
begin
instance
  by (intro_classes)
     (auto intro!: finite_code finite_imageD [where f=ptr_val] injI)
end

section "Properties of the raw heap"

lemma heap_list_length [simp]:
  "length (heap_list h n p) = n"
  by (induct n arbitrary: p) auto

lemma heap_list_split:
  shows "k \<le> n \<Longrightarrow> heap_list h n x = heap_list h k x @ heap_list h (n - k) (x + of_nat k)"
proof (induct n arbitrary: k x)
  case 0 thus ?case by simp
next
  case (Suc n) thus ?case
    by (cases k, auto simp: ac_simps)
qed

lemma heap_list_split2:
  "heap_list h (x + y) p = heap_list h x p @ heap_list h y (p + of_nat x)"
  by (subst heap_list_split [where k=x], auto)


section "Properties of intervals"

lemma intvlI:
  "x < n \<Longrightarrow> p + of_nat x \<in> {p..+n}"
  by (force simp: intvl_def)

lemma intvlD:
  "q \<in> {p..+n} \<Longrightarrow> \<exists>k. q = p + of_nat k \<and> k < n"
  by (force simp: intvl_def)

lemma intvl_empty [simp]:
  "{p..+0} = {}"
  by (fast dest: intvlD)

lemma intvl_Suc:
  "q \<in> {p..+Suc 0} \<Longrightarrow> p = q"
  by (force dest: intvlD)

lemma intvl_self:
  "0 < n \<Longrightarrow> x \<in> {x..+n}"
  by (force simp: intvl_def)

lemma intvl_start_inter:
  "\<lbrakk> 0 < m; 0 < n \<rbrakk> \<Longrightarrow> {p..+m} \<inter> {p..+n} \<noteq> {}"
  by (force simp: disjoint_iff_not_equal dest: intvl_self)

lemma intvl_overflow:
  assumes "2^len_of TYPE('a) \<le> n"
  shows "{(p::'a::len word)..+n} = UNIV"
proof -
  have witness:
    "\<And>x. x = p + of_nat (unat (x - p)) \<and> unat (x - p) < n"
    using assms by simp unat_arith
  show ?thesis unfolding intvl_def by (auto intro!: witness)
qed

declare of_nat_diff [simp]

lemma intvl_self_offset:
  fixes p::"'a::len word"
  assumes a: "2^len_of TYPE('a) - n < x" and b: "x < 2^len_of TYPE('a)" and
      c: "(p::'a::len word) \<notin> {p + of_nat x..+n}"
  shows False
proof -
  let ?j = "2^len_of TYPE('a) - x"
  from b have b': "of_nat x + of_nat ?j  = (0::'a::len word)" using of_nat_2p by auto
  moreover from a b have "?j < n" by arith
  with b b' c show  ?thesis by (force simp: intvl_def)
qed

lemma intvl_mem_offset:
  "\<lbrakk> q \<in> {p..+unat x}; q \<notin> {p..+unat y}; unat y \<le> unat x \<rbrakk> \<Longrightarrow>
      q \<in> {p + y..+unat x - unat y}"
  by (clarsimp simp: intvl_def) (rule_tac x="k - unat y" in exI, auto)

lemma intvl_plus_sub_offset:
  "x \<in> {p + y..+q - unat y} \<Longrightarrow> x \<in> {p..+q}"
  by (clarsimp simp: intvl_def) (rule_tac x="k + unat y" in exI, auto)

lemma intvl_plus_sub_Suc:
  "x \<in> {p + 1..+q - Suc 0} \<Longrightarrow> x \<in> {p..+q}"
  by (rule intvl_plus_sub_offset [where y=1], simp)

lemma intvl_neq_start:
  "\<lbrakk> (q::'a::len word) \<in> {p..+n}; p \<noteq> q \<rbrakk> \<Longrightarrow> q \<in> {p + 1..+n - Suc 0}"
  by (clarsimp simp: intvl_def)
     (metis (no_types) Suc_diff_1 add.commute add_Suc_right diff_diff_left neq0_conv
                       of_nat_Suc semiring_1_class.of_nat_0 zero_less_diff)

lemmas unat_simps' =
  word_arith_nat_defs word_unat.eq_norm len_of_addr_card mod_less

lemma intvl_offset_nmem:
  "\<lbrakk> q \<in> {(p::'a::len word)..+unat x}; y \<le>  2^len_of TYPE('a) - unat x \<rbrakk> \<Longrightarrow>
      q \<notin> {p + x..+y}"
  apply (clarsimp simp: intvl_def)
  apply (simp only: unat_simps')
  apply (subst (asm) word_unat.Abs_inject)
    apply (auto simp: unats_def)
  done

lemma intvl_Suc_nmem' [simp]:
  "n < 2^len_of TYPE('a) \<Longrightarrow> (p::'a::len word) \<notin> {p + 1..+n - Suc 0}"
  by (clarsimp simp: intvl_def)
     (unat_arith, simp only: unat_simps')

lemma intvl_start_le:
  "x \<le> y \<Longrightarrow> {p..+x} \<subseteq> {p..+y}"
  by (force simp: intvl_def)

lemma intvl_sub_eq:
  assumes "x \<le> y"
  shows "{p + x..+unat (y - x)} = {p..+unat y} - {p..+unat x}"
proof -
  have "unat y - unat x \<le> 2 ^ len_of TYPE('a) - unat x"
    by (insert unat_lt2p [of y], arith)
  moreover have "x \<le> y" by fact
  moreover hence "unat (y - x) = unat y - unat x"
    by (simp add: word_le_nat_alt, unat_arith)
  ultimately show ?thesis
    by (force dest: intvl_offset_nmem intvl_mem_offset elim: intvl_plus_sub_offset
              simp: word_le_nat_alt)

qed

end
