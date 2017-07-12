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

(* Definitions supporting the extremely long CTypes.thy *)

theory CTypesDefs
imports
  CTypesBase
begin

section "C types setup"

type_synonym field_name = string
type_synonym qualified_field_name = "field_name list"

type_synonym typ_name = string


text {* A typ_desc wraps a typ_struct with a typ name.
        A typ_struct is either a Scalar, with size, alignment and either a
        field accessor/updator pair (for typ_info) or a 'normalisor'
        (for typ_uinfo), or an Aggregate, with a list of typ_desc,
        field name pairs.*}

datatype (plugins del: size)
         'a typ_desc   = TypDesc "'a typ_struct" typ_name
    and  'a typ_struct = TypScalar nat nat "'a" |
                         TypAggregate "('a typ_desc,field_name) dt_pair list"

(* FIXME: eliminate eventually *)
datatype_compat dt_pair
datatype_compat typ_desc typ_struct

(* FIXME: these recreate the precise order of subgoals of the old datatype package *)
lemma typ_desc_induct:
  "\<lbrakk>\<And>typ_struct list. P2 typ_struct \<Longrightarrow> P1 (TypDesc typ_struct list); \<And>nat1 nat2 a. P2 (TypScalar nat1 nat2 a);
       \<And>list. P3 list \<Longrightarrow> P2 (TypAggregate list); P3 []; \<And>dt_pair list. \<lbrakk>P4 dt_pair; P3 list\<rbrakk> \<Longrightarrow> P3 (dt_pair # list);
       \<And>typ_desc list. P1 typ_desc \<Longrightarrow> P4 (DTPair typ_desc list)\<rbrakk>
      \<Longrightarrow> P1 typ_desc"
   by (rule compat_typ_desc.induct)

lemma typ_struct_induct:
    "\<lbrakk>\<And>typ_struct list. P2 typ_struct \<Longrightarrow> P1 (TypDesc typ_struct list); \<And>nat1 nat2 a. P2 (TypScalar nat1 nat2 a);
       \<And>list. P3 list \<Longrightarrow> P2 (TypAggregate list); P3 []; \<And>dt_pair list. \<lbrakk>P4 dt_pair; P3 list\<rbrakk> \<Longrightarrow> P3 (dt_pair # list);
       \<And>typ_desc list. P1 typ_desc \<Longrightarrow> P4 (DTPair typ_desc list)\<rbrakk>
      \<Longrightarrow> P2 typ_struct"
   by (rule compat_typ_struct.induct)

lemma typ_list_induct:
    "\<lbrakk>\<And>typ_struct list. P2 typ_struct \<Longrightarrow> P1 (TypDesc typ_struct list); \<And>nat1 nat2 a. P2 (TypScalar nat1 nat2 a);
      \<And>list. P3 list \<Longrightarrow> P2 (TypAggregate list); P3 []; \<And>dt_pair list. \<lbrakk>P4 dt_pair; P3 list\<rbrakk> \<Longrightarrow> P3 (dt_pair # list);
      \<And>typ_desc list. P1 typ_desc \<Longrightarrow> P4 (DTPair typ_desc list)\<rbrakk>
     \<Longrightarrow> P3 list"
   by (rule compat_typ_desc_char_list_dt_pair_list.induct)

lemma typ_dt_pair_induct:
    "\<lbrakk>\<And>typ_struct list. P2 typ_struct \<Longrightarrow> P1 (TypDesc typ_struct list); \<And>nat1 nat2 a. P2 (TypScalar nat1 nat2 a);
      \<And>list. P3 list \<Longrightarrow> P2 (TypAggregate list); P3 []; \<And>dt_pair list. \<lbrakk>P4 dt_pair; P3 list\<rbrakk> \<Longrightarrow> P3 (dt_pair # list);
      \<And>typ_desc list. P1 typ_desc \<Longrightarrow> P4 (DTPair typ_desc list)\<rbrakk>
     \<Longrightarrow> P4 dt_pair"
   by (rule compat_typ_desc_char_list_dt_pair.induct)

-- "Declare as default induct rule with old case names"
lemmas typ_desc_typ_struct_inducts [case_names
  TypDesc TypScalar TypAggregate Nil_typ_desc Cons_typ_desc DTPair_typ_desc, induct type] =
  typ_desc_induct typ_struct_induct typ_list_induct typ_dt_pair_induct

-- "Make sure list induct rule is tried first"
declare list.induct [induct type]

type_synonym 'a typ_pair = "('a typ_desc,field_name) dt_pair"

type_synonym typ_uinfo = "normalisor typ_desc"
type_synonym typ_uinfo_struct = "normalisor typ_struct"
type_synonym typ_uinfo_pair = "normalisor typ_pair"

record 'a field_desc =
  field_access :: "'a \<Rightarrow> byte list \<Rightarrow> byte list"
  field_update :: "byte list \<Rightarrow> 'a \<Rightarrow> 'a"

type_synonym 'a typ_info = "'a field_desc typ_desc"
type_synonym 'a typ_info_struct = "'a field_desc typ_struct"
type_synonym 'a typ_info_pair = "'a field_desc typ_pair"

definition fu_commutes :: "('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('c \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "fu_commutes f g \<equiv> \<forall>v bs bs'. f bs (g bs' v) = g bs' (f bs v)"


text {* size_td returns the sum of the sizes of all Scalar fields
        comprising a typ_desc i.e. the overall size of the type *}

(* Could express this and many other typ_desc primrecs as tree fold/map
   combos, but the intuition this way is clearer for anything non-trivial *)
primrec
  size_td :: "'a typ_desc \<Rightarrow> nat" and
  size_td_struct :: "'a typ_struct \<Rightarrow> nat" and
  size_td_list :: "'a typ_pair list \<Rightarrow> nat" and
  size_td_pair :: "'a typ_pair \<Rightarrow> nat"
where
  tz0: "size_td (TypDesc st nm) = size_td_struct st"

| tz1: "size_td_struct (TypScalar n algn d) = n"
| tz2: "size_td_struct (TypAggregate xs) = size_td_list xs"

| tz3: "size_td_list [] = 0"
| tz4: "size_td_list (x#xs) = size_td_pair x + size_td_list xs"

| tz5: "size_td_pair (DTPair t n) = size_td t"


text {* access_ti overlays the byte-wise representation of an object
        on a given byte list, given the typ_info (i.e. the layout) *}

primrec
  access_ti :: "'a typ_info \<Rightarrow> ('a \<Rightarrow> byte list \<Rightarrow> byte list)" and
  access_ti_struct :: "'a typ_info_struct \<Rightarrow>
    ('a \<Rightarrow> byte list \<Rightarrow> byte list)" and
  access_ti_list :: "'a typ_info_pair list \<Rightarrow>
    ('a \<Rightarrow> byte list \<Rightarrow> byte list)" and
  access_ti_pair :: "'a typ_info_pair \<Rightarrow> ('a \<Rightarrow> byte list \<Rightarrow> byte list)"
where
  fa0: "access_ti (TypDesc st nm) = access_ti_struct st"

| fa1: "access_ti_struct (TypScalar n algn d) = field_access d"
| fa2: "access_ti_struct (TypAggregate xs) = access_ti_list xs"

| fa3: "access_ti_list [] = (\<lambda>v bs. [])"
| fa4: "access_ti_list (x#xs) =
         (\<lambda>v bs. access_ti_pair x v (take (size_td_pair x) bs) @
                 access_ti_list xs v (drop (size_td_pair x) bs))"

| fa5: "access_ti_pair (DTPair t nm) = access_ti t"

text \<open>@{text access_ti\<^sub>0} overlays the representation of an object on a
        list of zero bytes\<close>

definition access_ti\<^sub>0 :: "'a typ_info \<Rightarrow> ('a \<Rightarrow> byte list)" where
  "access_ti\<^sub>0 t \<equiv> \<lambda>v. access_ti t v (replicate (size_td t) 0)"

text {* update_ti updates an object, given a list of bytes (the
        representation of the new value), and the typ_info *}

primrec
  update_ti :: "'a typ_info \<Rightarrow> (byte list \<Rightarrow> 'a \<Rightarrow> 'a)" and
  update_ti_struct :: "'a typ_info_struct \<Rightarrow> (byte list \<Rightarrow> 'a \<Rightarrow> 'a)" and
  update_ti_list :: "'a typ_info_pair list \<Rightarrow> (byte list \<Rightarrow> 'a \<Rightarrow> 'a)" and
  update_ti_pair :: "'a typ_info_pair \<Rightarrow> (byte list \<Rightarrow> 'a \<Rightarrow> 'a)"
where
  fu0: "update_ti (TypDesc st nm) = update_ti_struct st"

| fu1: "update_ti_struct (TypScalar n algn d) = field_update d"
| fu2: "update_ti_struct (TypAggregate xs) = update_ti_list xs"

| fu3: "update_ti_list [] = (\<lambda>bs. id)"
| fu4: "update_ti_list (x#xs) = (\<lambda>bs v.
         update_ti_pair x (take (size_td_pair x) bs)
             (update_ti_list xs (drop (size_td_pair x) bs) v))"

| fu5: "update_ti_pair (DTPair t nm) = update_ti t"


text {* update_ti_t updates an object only if the length of the
        supplied representation equals the object size *}

definition update_ti_t :: "'a typ_info \<Rightarrow> (byte list \<Rightarrow> 'a \<Rightarrow> 'a)" where
  "update_ti_t t \<equiv> \<lambda>bs. if length bs = size_td t then
      update_ti t bs else id"

definition update_ti_struct_t :: "'a typ_info_struct \<Rightarrow> (byte list \<Rightarrow> 'a \<Rightarrow> 'a)" where
  "update_ti_struct_t t \<equiv> \<lambda>bs. if length bs = size_td_struct t then
      update_ti_struct t bs else id"

definition update_ti_list_t :: "'a typ_info_pair list  \<Rightarrow> (byte list \<Rightarrow> 'a \<Rightarrow> 'a)" where
  "update_ti_list_t t \<equiv> \<lambda>bs. if length bs = size_td_list t then
      update_ti_list t bs else id"

definition update_ti_pair_t :: "'a typ_info_pair \<Rightarrow> (byte list \<Rightarrow> 'a \<Rightarrow> 'a)" where
  "update_ti_pair_t t \<equiv> \<lambda>bs. if length bs = size_td_pair t then
      update_ti_pair t bs else id"


text {* field_desc generates the access/update pair for a field,
        given the field's type_desc *}

definition field_desc :: "'a typ_info \<Rightarrow> 'a field_desc" where
  "field_desc t \<equiv> \<lparr> field_access = access_ti t,
      field_update = update_ti_t t \<rparr>"

declare field_desc_def [simp add]

definition field_desc_struct :: "'a typ_info_struct \<Rightarrow> 'a field_desc" where
  "field_desc_struct t \<equiv> \<lparr> field_access = access_ti_struct t,
      field_update = update_ti_struct_t t \<rparr>"

declare field_desc_struct_def [simp add]

definition field_desc_list :: "'a typ_info_pair list \<Rightarrow> 'a field_desc"
where
  "field_desc_list t \<equiv> \<lparr> field_access = access_ti_list t,
      field_update = update_ti_list_t t \<rparr>"

declare field_desc_list_def [simp add]

definition field_desc_pair :: "'a typ_info_pair \<Rightarrow> 'a field_desc"
where
  "field_desc_pair t \<equiv> \<lparr> field_access = access_ti_pair t,
      field_update = update_ti_pair_t t \<rparr>"

declare field_desc_pair_def [simp add]


primrec
  map_td :: "(nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a typ_desc \<Rightarrow> 'b typ_desc" and
  map_td_struct :: "(nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a typ_struct  \<Rightarrow> 'b typ_struct" and
  map_td_list :: "(nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a typ_pair list \<Rightarrow>
    'b typ_pair list" and
  map_td_pair :: "(nat \<Rightarrow> nat \<Rightarrow> 'a  \<Rightarrow> 'b) \<Rightarrow> 'a typ_pair \<Rightarrow> 'b typ_pair"
where
  mat0: "map_td f (TypDesc st nm) = TypDesc (map_td_struct f st) nm"

| mat1: "map_td_struct f (TypScalar n algn d) = TypScalar n algn (f n algn d)"
| mat2: "map_td_struct f (TypAggregate xs) = TypAggregate (map_td_list f xs)"

| mat3: "map_td_list f [] = []"
| mat4: "map_td_list f (x#xs) = map_td_pair f x # map_td_list f xs"

| mat5: "map_td_pair f (DTPair t n) = DTPair (map_td f t) n"

definition field_norm :: "nat \<Rightarrow> nat \<Rightarrow> 'a field_desc \<Rightarrow> (byte list \<Rightarrow> byte list)"
where
  "field_norm \<equiv> \<lambda>n algn d bs.
      if length bs = n then
          field_access d (field_update d bs undefined) (replicate n 0) else
          []"

definition export_uinfo :: "'a typ_info \<Rightarrow> typ_uinfo" where
  "export_uinfo t \<equiv> map_td field_norm t"


primrec
  wf_desc :: "'a typ_desc \<Rightarrow> bool" and
  wf_desc_struct :: "'a typ_struct \<Rightarrow> bool" and
  wf_desc_list :: "'a typ_pair list \<Rightarrow> bool" and
  wf_desc_pair :: "'a typ_pair \<Rightarrow> bool"
where
  wfd0: "wf_desc (TypDesc ts n) = wf_desc_struct ts"

| wfd1: "wf_desc_struct (TypScalar n algn d) = True"
| wfd2: "wf_desc_struct (TypAggregate ts) = wf_desc_list ts"

| wfd3: "wf_desc_list [] = True"
| wfd4: "wf_desc_list (x#xs) = (wf_desc_pair x \<and> \<not> dt_snd x \<in> dt_snd ` set xs \<and>
          wf_desc_list xs)"

| wfd5: "wf_desc_pair (DTPair x n) = wf_desc x"

primrec
  wf_size_desc :: "'a typ_desc \<Rightarrow> bool" and
  wf_size_desc_struct :: "'a typ_struct \<Rightarrow> bool" and
  wf_size_desc_list :: "'a typ_pair list \<Rightarrow> bool" and
  wf_size_desc_pair :: "'a typ_pair \<Rightarrow> bool"
where
  wfsd0: "wf_size_desc (TypDesc ts n) = wf_size_desc_struct ts"

| wfsd1: "wf_size_desc_struct (TypScalar n algn d) = (0 < n)"
| wfsd2: "wf_size_desc_struct (TypAggregate ts) =
           (ts \<noteq> [] \<and> wf_size_desc_list ts)"

| wfsd3: "wf_size_desc_list [] = True"
| wfsd4: "wf_size_desc_list (x#xs) =
           (wf_size_desc_pair x \<and> wf_size_desc_list xs)"

| wfsd5: "wf_size_desc_pair (DTPair x n) = wf_size_desc x"


definition
  typ_struct :: "'a typ_desc \<Rightarrow> 'a typ_struct"
where
  "typ_struct t = (case t of TypDesc st sz \<Rightarrow> st)"

lemma typ_struct [simp]:
  "typ_struct (TypDesc st sz) = st"
  by (simp add: typ_struct_def)

primrec
  typ_name :: "'a typ_desc \<Rightarrow> typ_name"
where
  "typ_name (TypDesc st nm) = nm"

primrec
  norm_tu :: "typ_uinfo \<Rightarrow> normalisor" and
  norm_tu_struct :: "typ_uinfo_struct \<Rightarrow> normalisor" and
  norm_tu_list :: "typ_uinfo_pair list \<Rightarrow> normalisor" and
  norm_tu_pair :: "typ_uinfo_pair \<Rightarrow> normalisor"
where
  tn0: "norm_tu (TypDesc st nm) = norm_tu_struct st"

| tn1: "norm_tu_struct (TypScalar n aln f) = f"
| tn2: "norm_tu_struct (TypAggregate xs) = norm_tu_list xs"

| tn3: "norm_tu_list [] = (\<lambda>bs. [])"
| tn4: "norm_tu_list (x#xs) = (\<lambda>bs.
         norm_tu_pair x (take (size_td_pair x) bs) @
         norm_tu_list xs (drop (size_td_pair x) bs))"

| tn5: "norm_tu_pair (DTPair t n) = norm_tu t"

class c_type

instance c_type \<subseteq> type ..

consts
  typ_info_t :: "'a::c_type itself \<Rightarrow> 'a typ_info"
  typ_name_itself :: "'a::c_type itself \<Rightarrow> typ_name"

definition typ_uinfo_t :: "'a::c_type itself \<Rightarrow> typ_uinfo" where
  "typ_uinfo_t t \<equiv> export_uinfo (typ_info_t TYPE('a))"

definition to_bytes :: "'a::c_type \<Rightarrow> byte list \<Rightarrow> byte list" where
  "to_bytes v \<equiv> access_ti (typ_info_t TYPE('a)) v"


(* from_bytes is now total - all partial C types 'a need to be instantiated
   as c_types using 'a option and the parser needs to do some work
   extracting the value and generating guards for non-None when these are
   used. Luckily for us in our work we never use them. *)
definition from_bytes :: "byte list \<Rightarrow> 'a::c_type" where
  "from_bytes bs \<equiv>
      field_update (field_desc (typ_info_t TYPE('a))) bs undefined"


type_synonym 'a flr = "('a typ_desc \<times> nat) option"

primrec
  field_lookup :: "'a typ_desc \<Rightarrow> qualified_field_name \<Rightarrow> nat \<Rightarrow> 'a flr" and
  field_lookup_struct :: "'a typ_struct \<Rightarrow> qualified_field_name \<Rightarrow> nat \<Rightarrow>
    'a flr" and
  field_lookup_list :: "'a typ_pair list \<Rightarrow> qualified_field_name \<Rightarrow> nat \<Rightarrow>
    'a flr" and
  field_lookup_pair :: "'a typ_pair \<Rightarrow> qualified_field_name \<Rightarrow> nat \<Rightarrow> 'a flr"
where
  fl0: "field_lookup (TypDesc st nm) f m =
         (if f=[] then Some (TypDesc st nm,m) else field_lookup_struct st f m)"

| fl1: "field_lookup_struct (TypScalar n algn d) f m = None"
| fl2: "field_lookup_struct (TypAggregate xs) f m = field_lookup_list xs f m"

| fl3: "field_lookup_list [] f m = None"
| fl4: "field_lookup_list (x#xs) f m = (
         case field_lookup_pair x f m of
           None \<Rightarrow> field_lookup_list xs f (m + size_td (dt_fst x)) |
           Some y \<Rightarrow> Some y)"

| fl5: "field_lookup_pair (DTPair t nm) f m =
         (if nm=hd f \<and> f \<noteq> [] then field_lookup t (tl f) m else None)"


definition map_td_flr :: "(nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow>
  ('a typ_desc \<times> nat) option \<Rightarrow> 'b flr"
where
  "map_td_flr f \<equiv> case_option None (\<lambda>(s,n). Some (map_td f s,n))"


definition
  import_flr :: "(nat \<Rightarrow> nat \<Rightarrow> 'b \<Rightarrow> 'a) \<Rightarrow> 'a flr \<Rightarrow> ('b typ_desc \<times> nat) option \<Rightarrow> bool"
where
  "import_flr f s k \<equiv> case_option (k=None)
      (\<lambda>(s,m). case_option False (\<lambda>(t,n). n=m \<and> map_td f t=s) k )
      s"

definition
  field_offset_untyped :: "'a typ_desc \<Rightarrow> qualified_field_name \<Rightarrow> nat"
where
  "field_offset_untyped t n \<equiv> snd (the (field_lookup t n 0))"

definition
  field_offset :: "'a::c_type itself \<Rightarrow> qualified_field_name \<Rightarrow> nat"
where
  "field_offset t n \<equiv> field_offset_untyped (typ_uinfo_t TYPE('a)) n"

definition
  field_ti :: "'a::c_type itself \<Rightarrow> qualified_field_name \<rightharpoonup> 'a typ_info"
where
  "field_ti t n \<equiv> case_option None (Some \<circ> fst)
      (field_lookup (typ_info_t TYPE('a)) n 0)"


definition
  field_size :: "'a::c_type itself \<Rightarrow> qualified_field_name \<Rightarrow> nat"
where
  "field_size t n \<equiv> size_td (the (field_ti t n))"

definition
  field_lvalue :: "'a::c_type ptr \<Rightarrow> qualified_field_name \<Rightarrow> addr" ("&'(_\<rightarrow>_')")
where
  "&(p\<rightarrow>f) \<equiv> ptr_val (p::'a ptr) + of_nat (field_offset TYPE('a) f)"

definition
  size_of :: "'a::c_type itself \<Rightarrow> nat" where
  "size_of t \<equiv> size_td (typ_info_t TYPE('a))"

definition
  norm_bytes :: "'a::c_type itself \<Rightarrow> normalisor" where
  "norm_bytes t \<equiv> norm_tu (export_uinfo (typ_info_t t))"

definition to_bytes_p :: "'a::c_type \<Rightarrow> byte list" where
  "to_bytes_p v \<equiv> to_bytes v (replicate (size_of TYPE('a)) 0)"

primrec
  align_td :: "'a typ_desc \<Rightarrow> nat" and
  align_td_struct :: "'a typ_struct \<Rightarrow> nat" and
  align_td_list :: "'a typ_pair list \<Rightarrow> nat" and
  align_td_pair :: "'a typ_pair \<Rightarrow> nat"
where
  al0:  "align_td (TypDesc st nm) = align_td_struct st"

| al1:  "align_td_struct (TypScalar n algn d) = algn"
| al2:  "align_td_struct (TypAggregate xs) = align_td_list xs"

| al3:  "align_td_list [] = 0"
| al4:  "align_td_list (x#xs) = max (align_td_pair x) (align_td_list xs)"

| al5:  "align_td_pair (DTPair t n) = align_td t"


definition align_of :: "'a::c_type itself \<Rightarrow> nat" where
  "align_of t \<equiv> 2^(align_td (typ_info_t TYPE('a)))"

definition
  ptr_add :: "('a::c_type) ptr \<Rightarrow> int \<Rightarrow> 'a ptr" (infixl "+\<^sub>p" 65)
where
  "ptr_add (a :: ('a::c_type) ptr) w \<equiv>
     Ptr (ptr_val a + of_int w * of_nat (size_of (TYPE('a))))"

lemma ptr_add_def':
  "ptr_add (Ptr p :: ('a::c_type) ptr) n
      = (Ptr (p + of_int n * of_nat (size_of TYPE('a))))"
  by (cases p, auto simp: ptr_add_def scast_id)

definition
  ptr_sub :: "('a::c_type) ptr \<Rightarrow> ('a::c_type) ptr \<Rightarrow> 32 signed word" (infixl "-\<^sub>p" 65)
where
  "ptr_sub (a :: ('a::c_type) ptr) p \<equiv>
     ucast (ptr_val a - ptr_val p) div of_nat (size_of (TYPE('a)))"

definition ptr_aligned :: "'a::c_type ptr \<Rightarrow> bool" where
  "ptr_aligned p \<equiv> align_of TYPE('a) dvd unat (ptr_val (p::'a ptr))"

primrec
  td_set :: "'a typ_desc \<Rightarrow> nat \<Rightarrow> ('a typ_desc \<times> nat) set" and
  td_set_struct :: "'a typ_struct \<Rightarrow> nat \<Rightarrow> ('a typ_desc \<times> nat) set" and
  td_set_list :: "'a typ_pair list \<Rightarrow> nat \<Rightarrow> ('a typ_desc \<times> nat) set" and
  td_set_pair :: "'a typ_pair \<Rightarrow> nat \<Rightarrow> ('a typ_desc \<times> nat) set"
where
  ts0:  "td_set (TypDesc st nm) m = {(TypDesc st nm,m)} \<union> td_set_struct st m"

| ts1:  "td_set_struct (TypScalar n algn d) m = {}"
| ts2:  "td_set_struct (TypAggregate xs) m = td_set_list xs m"

| ts3:  "td_set_list [] m = {}"
| ts4:  "td_set_list (x#xs) m = td_set_pair x m \<union> td_set_list xs (m + size_td (dt_fst x))"

| ts5:  "td_set_pair (DTPair t nm) m = td_set t m"


instantiation typ_desc :: (type) ord
begin

definition
  typ_tag_le_def:  "s \<le> (t::'a typ_desc) \<equiv> (\<exists>n. (s,n) \<in> td_set t 0)"
definition
  typ_tag_lt_def: "s < (t::'a typ_desc) \<equiv> s \<le> t \<and> s \<noteq> t"
instance ..

end


definition
  fd_cons_double_update :: "'a field_desc \<Rightarrow> bool"
where
  "fd_cons_double_update d \<equiv>
      (\<forall>v bs bs'. length bs = length bs' \<longrightarrow> field_update d bs (field_update d bs' v) = field_update d bs v)"

definition
  fd_cons_update_access :: "'a field_desc \<Rightarrow> nat \<Rightarrow> bool"
where
  "fd_cons_update_access d n \<equiv>
      (\<forall>v bs. length bs = n \<longrightarrow> field_update d (field_access d v bs) v = v)"

definition
  norm_desc  :: "'a field_desc \<Rightarrow> nat \<Rightarrow> (byte list \<Rightarrow> byte list)"
where
  "norm_desc d n \<equiv> \<lambda>bs. field_access d (field_update d bs undefined) (replicate n 0)"

definition
  fd_cons_length :: "'a field_desc \<Rightarrow> nat \<Rightarrow> bool"
where
  "fd_cons_length d n \<equiv> \<forall>v bs. length bs = n \<longrightarrow> length (field_access d v bs) = n"

definition
  fd_cons_access_update :: "'a field_desc \<Rightarrow> nat \<Rightarrow> bool"
where
  "fd_cons_access_update d n \<equiv> \<forall>bs bs' v v'. length bs = n \<longrightarrow>
      length bs' = n \<longrightarrow>
      field_access d (field_update d bs v) bs' = field_access d (field_update d bs v') bs'"


definition
  fd_cons_update_normalise :: "'a field_desc \<Rightarrow> nat \<Rightarrow> bool"
where
  "fd_cons_update_normalise d n  \<equiv>
      (\<forall>v bs. length bs=n \<longrightarrow> field_update d (norm_desc d n bs) v = field_update d bs v)"


definition
  fd_cons_desc :: "'a field_desc \<Rightarrow> nat \<Rightarrow> bool"
where
  "fd_cons_desc d n \<equiv> fd_cons_double_update d \<and>
      fd_cons_update_access d n \<and>
      fd_cons_access_update d n \<and>
      fd_cons_length d n"

definition
  fd_cons :: "'a typ_info \<Rightarrow> bool"
where
  "fd_cons t \<equiv> fd_cons_desc (field_desc t) (size_td t)"

definition
  fd_cons_struct :: "'a typ_info_struct \<Rightarrow> bool"
where
  "fd_cons_struct t \<equiv> fd_cons_desc (field_desc_struct t) (size_td_struct t)"

definition
  fd_cons_list :: "'a typ_info_pair list \<Rightarrow> bool"
where
  "fd_cons_list t \<equiv> fd_cons_desc (field_desc_list t) (size_td_list t)"

definition
  fd_cons_pair :: "'a typ_info_pair \<Rightarrow> bool"
where
  "fd_cons_pair t \<equiv> fd_cons_desc (field_desc_pair t) (size_td_pair t)"


definition
  fa_fu_ind :: "'a field_desc \<Rightarrow> 'a field_desc \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>bool"
where
  "fa_fu_ind d d' n n' \<equiv> \<forall>v bs bs'. length bs = n \<longrightarrow> length bs' = n' \<longrightarrow>
      field_access d (field_update d' bs v) bs' = field_access d v bs'"

definition
  wf_fdp :: "('a typ_info \<times> qualified_field_name) set \<Rightarrow> bool"
where
  "wf_fdp t \<equiv> \<forall>x m. (x,m) \<in> t \<longrightarrow> (fd_cons x \<and> (\<forall>y n. (y,n) \<in> t \<and> \<not> m \<le> n \<and> \<not> n \<le> m
      \<longrightarrow> fu_commutes (field_update (field_desc x)) (field_update (field_desc y)) \<and>
          fa_fu_ind (field_desc x) (field_desc y) (size_td y) (size_td x)))"

lemma wf_fdp_list:
  "wf_fdp (xs \<union> ys) \<Longrightarrow> wf_fdp xs \<and> wf_fdp ys"
  by (auto simp: wf_fdp_def)


primrec
  wf_fd :: "'a typ_info \<Rightarrow> bool" and
  wf_fd_struct :: "'a typ_info_struct \<Rightarrow> bool" and
  wf_fd_list :: "'a typ_info_pair list \<Rightarrow> bool" and
  wf_fd_pair :: "'a typ_info_pair \<Rightarrow> bool"
where
  wffd0:  "wf_fd (TypDesc ts n) = (wf_fd_struct ts)"

| wffd1:  "wf_fd_struct (TypScalar n algn d) = fd_cons_struct (TypScalar n algn d)"
| wffd2:  "wf_fd_struct (TypAggregate ts) = wf_fd_list ts"

| wffd3:  "wf_fd_list [] = True"
| wffd4:  "wf_fd_list (x#xs) = (wf_fd_pair x \<and> wf_fd_list xs \<and>
      fu_commutes (update_ti_pair_t x) (update_ti_list_t xs) \<and>
      fa_fu_ind (field_desc_pair x) (field_desc_list xs) (size_td_list xs) (size_td_pair x)\<and>
      fa_fu_ind (field_desc_list xs) (field_desc_pair x) (size_td_pair x) (size_td_list xs))"

| wffd5:  "wf_fd_pair (DTPair x n) = wf_fd x"


definition
  tf_set :: "'a typ_info \<Rightarrow> ('a typ_info \<times> qualified_field_name) set"
where
  "tf_set td \<equiv> {(s,f) | s f. \<exists>n. field_lookup td f 0 = Some (s,n)}"

definition
  tf_set_struct :: "'a typ_info_struct \<Rightarrow> ('a typ_info \<times> qualified_field_name) set"
where
  "tf_set_struct td \<equiv> {(s,f) | s f. \<exists>n. field_lookup_struct td f 0 = Some (s,n)}"

definition
  tf_set_list :: "'a typ_info_pair list \<Rightarrow> ('a typ_info \<times> qualified_field_name) set"
where
  "tf_set_list td \<equiv> {(s,f) | s f. \<exists>n. field_lookup_list td f 0 = Some (s,n)}"

definition
  tf_set_pair :: "'a typ_info_pair \<Rightarrow> ('a typ_info \<times> qualified_field_name) set"
where
  "tf_set_pair td \<equiv> {(s,f) | s f. \<exists>n. field_lookup_pair td f 0 = Some (s,n)}"


record 'a leaf_desc =
  lf_fd :: "'a field_desc"
  lf_sz :: nat
  lf_fn :: qualified_field_name

primrec
  lf_set :: "'a typ_info \<Rightarrow> qualified_field_name \<Rightarrow> 'a leaf_desc set" and
  lf_set_struct :: "'a typ_info_struct \<Rightarrow> qualified_field_name \<Rightarrow> 'a leaf_desc set" and
  lf_set_list :: "'a typ_info_pair list \<Rightarrow> qualified_field_name \<Rightarrow> 'a leaf_desc set" and
  lf_set_pair :: "'a typ_info_pair \<Rightarrow> qualified_field_name \<Rightarrow> 'a leaf_desc set"
where
  fds0:  "lf_set (TypDesc st nm) fn = lf_set_struct st fn"

| fds1:  "lf_set_struct (TypScalar n algn d) fn = {(\<lparr> lf_fd = d, lf_sz = n, lf_fn = fn \<rparr>)}"
| fds2:  "lf_set_struct (TypAggregate xs) fn = lf_set_list xs fn"

| fds3:  "lf_set_list [] fn = {}"
| fds4:  "lf_set_list (x#xs) fn = lf_set_pair x fn \<union> lf_set_list xs fn"

| fds5:  "lf_set_pair (DTPair t n) fn = lf_set t (fn@[n])"


definition
  wf_lf :: "'a leaf_desc set \<Rightarrow> bool"
where
  "wf_lf D \<equiv> \<forall>x. x \<in> D \<longrightarrow> (fd_cons_desc (lf_fd x) (lf_sz x) \<and> (\<forall>y. y \<in> D \<longrightarrow> lf_fn y \<noteq> lf_fn x
      \<longrightarrow> fu_commutes (field_update (lf_fd x)) (field_update (lf_fd y)) \<and>
          fa_fu_ind (lf_fd x) (lf_fd y) (lf_sz y) (lf_sz x)))"

definition
  ti_ind :: "'a leaf_desc set \<Rightarrow> 'a leaf_desc set \<Rightarrow> bool"
where
  "ti_ind X Y \<equiv> \<forall>x y. x \<in> X \<and> y \<in> Y \<longrightarrow> (
      fu_commutes (field_update (lf_fd x)) (field_update (lf_fd y)) \<and>
          fa_fu_ind (lf_fd x) (lf_fd y) (lf_sz y) (lf_sz x) \<and>
          fa_fu_ind (lf_fd y) (lf_fd x) (lf_sz x) (lf_sz y))"


definition
  t2d :: "('a typ_info \<times> qualified_field_name) \<Rightarrow> 'a leaf_desc"
where
  "t2d x \<equiv> \<lparr> lf_fd = field_desc (fst x), lf_sz = size_td (fst x), lf_fn = snd x\<rparr>"


definition
  fd_consistent :: "'a typ_info \<Rightarrow> bool"
where
  "fd_consistent t \<equiv> \<forall>f s n. field_lookup t f 0 = Some (s,n)
      \<longrightarrow> fd_cons s"

class wf_type = c_type +
  assumes wf_desc [simp]: "wf_desc (typ_info_t TYPE('a::c_type))"
  assumes wf_size_desc [simp]: "wf_size_desc (typ_info_t TYPE('a::c_type))"
  assumes wf_lf [simp]: "wf_lf (lf_set (typ_info_t TYPE('a::c_type)) [])"

definition
  super_update_bs :: "byte list \<Rightarrow> byte list \<Rightarrow> nat \<Rightarrow> byte list"
where
  "super_update_bs v bs n \<equiv> take n bs @ v @
      drop (n + length v) bs"

definition
  disj_fn :: "qualified_field_name \<Rightarrow> qualified_field_name \<Rightarrow> bool"
where
  "disj_fn s t \<equiv> \<not> s \<le> t \<and> \<not> t \<le> s"

definition
  fs_path :: "qualified_field_name list \<Rightarrow> qualified_field_name set"
where
  "fs_path xs \<equiv> {x. \<exists>k. k \<in> set xs \<and> x \<le> k} \<union> {x. \<exists>k. k \<in> set xs \<and> k \<le> x}"

definition
  field_names :: "'a typ_desc \<Rightarrow> qualified_field_name set"
where
  "field_names t \<equiv> {f. field_lookup t f 0 \<noteq> None}"

definition
  align_field :: "'a typ_desc \<Rightarrow> bool"
where
  "align_field ti \<equiv> \<forall>f s n. field_lookup ti f 0 = Some (s,n) \<longrightarrow>
      2^(align_td s) dvd n"

class mem_type_sans_size = wf_type +
  assumes upd:
     "length bs = size_of TYPE('a) \<longrightarrow>
      update_ti_t (typ_info_t TYPE('a::c_type)) bs v
          = update_ti_t (typ_info_t TYPE('a)) bs w"
  assumes align_size_of: "align_of (TYPE('a::c_type)) dvd size_of TYPE('a)"
  assumes align_field: "align_field (typ_info_t TYPE('a::c_type))"


class mem_type = mem_type_sans_size +
  assumes max_size: "size_of (TYPE('a::c_type)) < addr_card"


primrec
  aggregate :: "'a typ_desc \<Rightarrow> bool" and
  aggregate_struct :: "'a typ_struct \<Rightarrow> bool"
where
  "aggregate (TypDesc st tn) = aggregate_struct st"

| "aggregate_struct (TypScalar n algn d) = False"
| "aggregate_struct (TypAggregate ts) = True"

class simple_mem_type = mem_type +
  assumes simple_tag: "\<not> aggregate (typ_info_t TYPE('a::c_type))"

definition
  field_of :: "addr \<Rightarrow> 'a typ_desc \<Rightarrow> 'a typ_desc \<Rightarrow> bool"
where
  "field_of q s t \<equiv> (s,unat q) \<in> td_set t 0"

definition
  field_of_t :: "'a::c_type ptr \<Rightarrow> 'b::c_type ptr \<Rightarrow> bool"
where
  "field_of_t p q \<equiv> field_of (ptr_val p - ptr_val q) (typ_uinfo_t TYPE('a))
      (typ_uinfo_t TYPE('b))"

definition
  h_val :: "heap_mem \<Rightarrow> 'a::c_type ptr \<Rightarrow> 'a"
where
  "h_val h \<equiv> \<lambda>p. from_bytes (heap_list h (size_of TYPE ('a))
      (ptr_val (p::'a ptr)))"

primrec
  heap_update_list :: "addr \<Rightarrow> byte list \<Rightarrow> heap_mem \<Rightarrow> heap_mem"
where
  heap_update_list_base: "heap_update_list p [] h = h"
| heap_update_list_rec:
  "heap_update_list p (x#xs) h = heap_update_list (p + 1) xs (h(p:= x))"

type_synonym 'a typ_heap_g = "'a ptr \<Rightarrow> 'a"

(* FIXME: now redundant with h_val *)
definition
  lift :: "heap_mem \<Rightarrow> 'a::c_type typ_heap_g"
where
  "lift h \<equiv> h_val h"

definition
  heap_update :: "'a::c_type ptr \<Rightarrow> 'a \<Rightarrow> heap_mem \<Rightarrow> heap_mem"
where
  "heap_update p v h \<equiv> heap_update_list (ptr_val p) (to_bytes v (heap_list h (size_of TYPE('a)) (ptr_val p))) h"

fun
  fold_td' :: "(typ_name \<Rightarrow> ('a \<times> field_name) list \<Rightarrow> 'a) \<times> 'a typ_desc \<Rightarrow> 'a"
where
fot0: "fold_td' (f,TypDesc st nm) = (case st of
           TypScalar n algn d \<Rightarrow> d |
           TypAggregate ts \<Rightarrow> f nm (map (\<lambda>x. case x of DTPair t n \<Rightarrow> (fold_td' (f,t),n)) ts))"


definition
  fold_td :: "(typ_name \<Rightarrow> ('a \<times> field_name) list \<Rightarrow> 'a) \<Rightarrow> 'a typ_desc \<Rightarrow> 'a"
where
  "fold_td \<equiv> \<lambda>f t. fold_td' (f,t)"

declare fold_td_def [simp]

definition
  fold_td_struct :: "typ_name \<Rightarrow> (typ_name \<Rightarrow> ('a \<times> field_name) list \<Rightarrow> 'a) \<Rightarrow> 'a typ_struct \<Rightarrow> 'a"
where
  "fold_td_struct tn f st \<equiv> (case st of
           TypScalar n algn d \<Rightarrow> d |
           TypAggregate ts \<Rightarrow> f tn (map (\<lambda>x. case x of DTPair t n \<Rightarrow> (fold_td' (f,t),n)) ts))"

declare fold_td_struct_def [simp]

definition
  fold_td_list :: "typ_name \<Rightarrow> (typ_name \<Rightarrow> ('a \<times> field_name) list \<Rightarrow> 'a) \<Rightarrow> 'a typ_pair list \<Rightarrow> 'a"
where
  "fold_td_list tn f ts \<equiv> f tn (map (\<lambda>x. case x of DTPair t n \<Rightarrow> (fold_td' (f,t),n)) ts)"

declare fold_td_list_def [simp]

definition
  fold_td_pair :: "(typ_name \<Rightarrow> ('a \<times> field_name) list \<Rightarrow> 'a) \<Rightarrow> 'a typ_pair \<Rightarrow> 'a"
where
  "fold_td_pair f x \<equiv> (case x of DTPair t n \<Rightarrow> fold_td' (f,t))"

declare fold_td_pair_def [simp]

fun
  map_td' :: "(nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'b) \<times> 'a typ_desc \<Rightarrow> 'b typ_desc"
where
  "map_td' (f,TypDesc st nm) = (TypDesc (case st of
           TypScalar n algn d \<Rightarrow> TypScalar n algn (f n algn d) |
           TypAggregate ts \<Rightarrow> TypAggregate (map (\<lambda>x. case x of DTPair t n \<Rightarrow> DTPair (map_td' (f,t)) n) ts)) nm)"

definition
  tnSum :: "typ_name \<Rightarrow> (nat \<times> field_name) list \<Rightarrow> nat"
where
  "tnSum \<equiv> \<lambda>tn ts. foldr (op + o fst) ts 0"

definition
  tnMax :: "typ_name \<Rightarrow> (nat \<times> field_name) list \<Rightarrow> nat"
where
  "tnMax \<equiv> \<lambda>tn ts. foldr (\<lambda>x y. max (fst x) y) ts 0"

definition
  wfd :: "typ_name \<Rightarrow> (bool \<times> field_name) list \<Rightarrow> bool"
where
  "wfd \<equiv> \<lambda>tn ts. distinct (map snd ts) \<and> foldr (op \<and>) (map fst ts) True"

definition
  wfsd :: "typ_name \<Rightarrow> (bool \<times> field_name) list \<Rightarrow> bool"
where
  "wfsd \<equiv> \<lambda>tn ts. ts \<noteq> [] \<and> foldr (op \<and>) (map fst ts) True"

end
