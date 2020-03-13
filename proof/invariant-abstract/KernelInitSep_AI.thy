(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory KernelInitSep_AI
imports
  "ASpec.KernelInit_A"
  "Sep_Algebra.Sep_Algebra_L4v"
  Invariants_AI
begin

(* UNFINISHED; paused project *)

text \<open>Migration candidates\<close>

lemma hoare_gen_asmE':
  (* XXX: this should be the non-' version really, which is misnamed *)
  "(P \<Longrightarrow> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>) \<Longrightarrow> \<lbrace>P' and (K P)\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (simp add: validE_R_def validE_def valid_def) blast

lemma unat_less_power_n:
  "n = 2 ^ len_of TYPE('a) \<Longrightarrow> unat (x::'a::len word) < n"
  by (simp add: unat_less_power)

lemma subset_union:
  "S \<subset> T \<Longrightarrow> (S \<union> T) = T"
  by blast

lemma singleton_subsetI:
  "\<lbrakk> i \<in> S ; S - {i} \<noteq> {} \<rbrakk> \<Longrightarrow> {i} \<subset> S"
  by blast

lemma bl_length_set_equal:
  fixes i :: "bool list"
  shows "{x. length x = length i} = {i} \<Longrightarrow> i = []"
  apply (cases i, clarsimp)
  apply (drule_tac x="(\<not>a) # list" in eqset_imp_iff)
  apply simp
  done

lemma bl_length_set_singleton_subset:
  fixes i :: "bool list"
  assumes notnil: "i \<noteq> []"
  shows "{i} \<subset> {x. length x = length i}" (is "_ \<subset> ?s")
  using notnil
proof -
  from notnil obtain b bs where i: "i = b # bs" by (cases i, simp)

  have b: "b # bs \<in> ?s" using i by simp
  have notb: "(\<not>b) # bs \<in> ?s" using i by simp

  from b notb have "?s - {b # bs} \<noteq> {}" by blast

  thus ?thesis using i by (auto intro!: singleton_subsetI)
qed

lemma insert_same_length_id:
  "insert i {x. length x = length i} = {x. length x = length i}"
  by auto


text \<open>
  Recursive sequence of length n along a ring, starting at p.
  Wrapping permitted.\<close>
primrec
  len_seq :: "'a::ring_1 \<Rightarrow> nat \<Rightarrow> 'a list"
where
  "len_seq p 0 = []"
| "len_seq p (Suc n) = p # (len_seq (p + 1) n)"

lemma len_seq_length [simp]:
  fixes p :: "'a::ring_1"
  shows "length (len_seq p sz) = sz"
  by (induct sz arbitrary: p, auto)

lemma len_seq_Cons:
  "0 < sz \<Longrightarrow> len_seq p sz = p # len_seq (p+1) (sz - 1)"
  by (induct sz arbitrary: p, auto)

lemma map_fun_Suc_upt_Cons:
  assumes xn: "x \<le> n"
  assumes gf: "\<And>n. g (Suc n) = f n"
  shows "map g [x..<Suc n] = (g x) # map f [x..<n]"
proof -
  have ss: "[Suc x..<Suc n] = map Suc [x..<n]"
    by (subst map_Suc_upt[symmetric], rule refl)
  show ?thesis using xn
    by (simp add: upt_conv_Cons ss gf del: upt_Suc)
qed

lemma len_seq_map_upt_eq:
  fixes p :: "'a::ring_1"
  shows "len_seq p sz = map (\<lambda>n. p + of_nat n) [0..<sz]"
proof (induct sz arbitrary: p)
  case 0 thus ?case by simp
next
  case (Suc sz)
  hence IH: "len_seq (p + 1) sz = map (\<lambda>n. p + 1 + of_nat n) [0..<sz]" by simp
  show ?case
    by (simp only: len_seq.simps IH map_fun_Suc_upt_Cons) fastforce
qed

lemma len_seq_no_wrap:
  fixes p :: "'a :: len word"
  assumes sz: "n < 2 ^ len_of TYPE('a)"
  shows "p \<notin> set (len_seq (p + 1) n)"
proof (rule ccontr, simp)
  assume pin: "p \<in> set (len_seq (p + 1) n)"
  then obtain q where q: "p + 1 + of_nat q = p" and qn: "q < n"
    by (auto simp: len_seq_map_upt_eq)
  hence "of_nat q + 1 = (0 :: 'a word)" by (simp add: add.commute)

  moreover
  from qn have "of_nat q + (1::'a word) \<noteq> 0" using sz
    by (fastforce intro!: less_is_non_zero_p1[where k="of_nat n :: 'a word"]
                 intro: word_of_nat_less simp: unat_of_nat_eq)

  ultimately show False by blast
qed


section \<open>Definitions\<close>

subsection \<open>Partial Validity of Kernel Objects (i.e. cnodes)\<close>

text \<open>Same as @{term "well_formed_cnode_n"}, but allow gaps.\<close>
definition
  bounded_cnode_n :: "nat \<Rightarrow> cnode_contents \<Rightarrow> bool" where
  "bounded_cnode_n n \<equiv> \<lambda>cs. \<forall>x \<in> dom cs. length x = n"

text \<open>Same as @{term "valid_cs_size"}, but allowing gaps\<close>
definition
  bounded_cs_size :: "nat \<Rightarrow> cnode_contents \<Rightarrow> bool" where
  "bounded_cs_size sz cs \<equiv> sz < word_bits - cte_level_bits
                           \<and> bounded_cnode_n sz cs"

text \<open>
  Kernel object respects bounds set by its own size. This is only a problem
  for cnodes.
\<close>
definition
  bounded_ko :: "kernel_object \<Rightarrow> bool" where
  "bounded_ko ko = (case ko of CNode sz cs \<Rightarrow> bounded_cs_size sz cs
                             | _ \<Rightarrow> True)"

subsection \<open>
  Types and sizes of abstract kernel objects without checking any
  well-formedness.\<close>

text \<open>Like @{term "a_type"}, but don't check wellformed on cnodes\<close>
definition
  a_base_type :: "Structures_A.kernel_object \<Rightarrow> a_type" where
 "a_base_type ko \<equiv> case ko of
           CNode sz cspace          \<Rightarrow> ACapTable sz
         | TCB tcb                  \<Rightarrow> ATCB
         | Endpoint endpoint        \<Rightarrow> AEndpoint
         | Notification notification   \<Rightarrow> ANTFN
         | ArchObj ao               \<Rightarrow> AArch (case ao of
           PageTable pt             \<Rightarrow> APageTable
         | PageDirectory pd         \<Rightarrow> APageDirectory
         | DataPage sz              \<Rightarrow> AIntData sz
         | Arch_Structs_A.ASIDPool f \<Rightarrow> AASIDPool)"

lemmas a_base_type_simps [simp] =
  a_base_type_def [split_simps kernel_object.split arch_kernel_obj.split]

text \<open>
  These correspond to @{term "arch_kobj_size"} and @{term "obj_bits"}, but
  since we can derive all the information necessary from the type, we use the
  type.
  We provide abbreviations for convenience;
  @{text "a_base_type_bits (a_base_type ...)"} is rather verbose.
\<close>

definition
  aa_base_type_bits :: "aa_type \<Rightarrow> nat" where
  "aa_base_type_bits t \<equiv>
    case t of APageTable \<Rightarrow> 10
            | APageDirectory \<Rightarrow> 14
            | AIntData sz \<Rightarrow> pageBitsForSize sz
            | AASIDPool \<Rightarrow> pageBits"

lemmas aa_base_type_bits_simps [simp] =
  aa_base_type_bits_def [split_simps aa_type.split]

definition
  a_base_type_bits :: "a_type \<Rightarrow> nat" where
  "a_base_type_bits t \<equiv>
    case t of ACapTable sz \<Rightarrow> cte_level_bits + sz
            | ATCB \<Rightarrow> 9
            | AEndpoint \<Rightarrow> 4
            | ANTFN \<Rightarrow> 4
            | AArch aot \<Rightarrow> aa_base_type_bits aot"

lemmas a_base_type_bits_simps [simp] =
  a_base_type_bits_def [split_simps a_type.split]

abbreviation
  "t_obj_bits ko \<equiv> a_base_type_bits (a_base_type ko)"

lemmas t_obj_bits_def = a_base_type_bits_def

text \<open>
  Whether an index is a valid cnode index for the given type, i.e.\ can we set
  that cap to something and end up with a bounded object.
\<close>

definition
  abt_valid_cnode_index :: "a_type \<Rightarrow> cnode_index \<Rightarrow> bool" where
  "abt_valid_cnode_index atyp i \<equiv> (case atyp
     of ACapTable sz \<Rightarrow> length i = sz
      | ATCB \<Rightarrow> i \<in> tcb_cnode_index ` {0,1,2,3,4}
      | _ \<Rightarrow> False)"

abbreviation
  "valid_cnode_index ko \<equiv> abt_valid_cnode_index (a_base_type ko)"

lemmas valid_cnode_index_def = abt_valid_cnode_index_def


subsection \<open>Component structure of objects\<close>

text \<open>
  Components available for given object types.
\<close>

text \<open>
  What components are available for a given kernel object
  (we should see a subset of these in the ghost state).
  Note that [] is the ``fields'' component, containing unsplittable information for a
  given object, such as non-cap fields of a tcb or all fields of an endpoint.\<close>

primrec
  aa_base_type_components :: "aa_type \<Rightarrow> component set" where
  "aa_base_type_components AASIDPool = {x. length x = 10}" (* 2^10 components *)
| "aa_base_type_components APageTable = {x. length x = 8}" (* 2^8 components *)
| "aa_base_type_components APageDirectory = {x. length x = 12}" (* 2^12 components *)
| "aa_base_type_components (AIntData sz) = {}" (* no core, type only *)

primrec
  a_base_type_components :: "a_type \<Rightarrow> component set" where
  "a_base_type_components (ACapTable sz) = {x. length x = sz}"
| "a_base_type_components ATCB = insert [] (tcb_cnode_index ` {0,1,2,3,4})"
                                 (* core & 5 caps *)
| "a_base_type_components AEndpoint = {[]}" (* core only *)
| "a_base_type_components ANTFN = {[]}" (* core only *)
| "a_base_type_components (AArch aot) = aa_base_type_components aot"

abbreviation
  "ko_components ko \<equiv> a_base_type_components (a_base_type ko)"

text \<open>Relationship between caps and components.\<close>

(* XXX: see @{text "nat_to_cref"} *)
definition
  a_base_type_cmp_of :: "a_type \<Rightarrow> cnode_index \<Rightarrow> component" where
  "a_base_type_cmp_of atyp i \<equiv> case atyp of ACapTable _ \<Rightarrow> i
                                          | ATCB \<Rightarrow> i"

abbreviation
  "cmp_of ko \<equiv> a_base_type_cmp_of (a_base_type ko)"


subsection \<open>Component-wise Combining of Kernel Objects\<close>

text \<open>
  Combining objects of the same type (strictly speaking it's a right override,
  although realistically it only makes sense if the first object's components
  are disjoint from those of the second). Crucially, NOT DEFINED for two
  objects of different types, as that makes no sense whatsoever.\<close>

definition
  ao_override :: "arch_kernel_obj \<Rightarrow> arch_kernel_obj \<Rightarrow> component set
                 \<Rightarrow> arch_kernel_obj" where
  "ao_override obj1 obj2 cmps \<equiv>
     (case obj1
        of ASIDPool o1 \<Rightarrow>
             (case obj2 of ASIDPool o2 \<Rightarrow>
                ASIDPool (\<lambda>bs. if to_bl bs \<in> cmps then o2 bs else o1 bs))
         | PageTable o1 \<Rightarrow>
             (case obj2 of PageTable o2 \<Rightarrow>
                PageTable (\<lambda>bs. if to_bl bs \<in> cmps then o2 bs else o1 bs))
         | PageDirectory o1 \<Rightarrow>
             (case obj2 of PageDirectory o2 \<Rightarrow>
                PageDirectory (\<lambda>bs. if to_bl bs \<in> cmps then o2 bs else o1 bs))
         | DataPage o1 \<Rightarrow> (case obj2 of DataPage o2 \<Rightarrow> DataPage o2))"
           (* DataPage has no core, type only *)

definition
  tcb_override :: "Structures_A.tcb \<Rightarrow> Structures_A.tcb \<Rightarrow> component set
                   \<Rightarrow> Structures_A.tcb" where
  (* 6 fields counted as "core" (component []), plus 5 caps (tcb_cnode_index 0..4) *)
  "tcb_override t1 t2 cmps \<equiv>
     t1\<lparr> tcb_state := tcb_state (if [] \<in> cmps then t2 else t1),
         tcb_fault_handler := tcb_fault_handler (if [] \<in> cmps then t2 else t1),
         tcb_ipc_buffer := tcb_ipc_buffer (if [] \<in> cmps then t2 else t1),
         tcb_context := tcb_context (if [] \<in> cmps then t2 else t1),
         tcb_fault := tcb_fault (if [] \<in> cmps then t2 else t1),
         tcb_bound_notification := tcb_bound_notification (if [] \<in> cmps then t2 else t1),
         tcb_ctable := tcb_ctable (if tcb_cnode_index 0 \<in> cmps then t2 else t1),
         tcb_vtable := tcb_vtable (if tcb_cnode_index 1 \<in> cmps then t2 else t1),
         tcb_reply := tcb_reply (if tcb_cnode_index 2 \<in> cmps then t2 else t1),
         tcb_caller := tcb_caller (if tcb_cnode_index 3 \<in> cmps then t2 else t1),
         tcb_ipcframe := tcb_ipcframe (if tcb_cnode_index 4 \<in> cmps then t2 else t1)
       \<rparr>"

definition
  ko_override :: "Structures_A.kernel_object \<Rightarrow> Structures_A.kernel_object
                 \<Rightarrow> component set \<Rightarrow> Structures_A.kernel_object" where
  "ko_override obj1 obj2 cmps =
     (case obj1
        of CNode sz o1 \<Rightarrow>
           (case obj2 of CNode sz2 o2 \<Rightarrow>
              CNode sz2 (\<lambda>bs. if bs \<in> cmps then o2 bs else o1 bs))
         | TCB o1 \<Rightarrow> (case obj2 of TCB o2 \<Rightarrow> TCB (tcb_override o1 o2 cmps))
         | Endpoint o1 \<Rightarrow>
           (case obj2 of Endpoint o2 \<Rightarrow>
              Endpoint (if [] \<in> cmps then o2 else o1)) (* core only *)
         | Notification o1 \<Rightarrow>
           (case obj2 of Notification o2 \<Rightarrow>
              Notification (if [] \<in> cmps then o2 else o1) (* core only *))
         | ArchObj ao1 \<Rightarrow>
           (case obj2 of ArchObj ao2 \<Rightarrow> ArchObj (ao_override ao1 ao2 cmps)))"

text \<open>
  Object ``cleaning'', i.e. getting the components we don't have into a known
  state. Otherwise if we combine @{text "(cnode1,{to_bl 2, to_bl 3})"} and
  @{text "(cnode2,{to_bl 4, to_bl 5})"} we don't
  know anything about component @{text "to_bl 1"}, and so can't claim commutativity.

  Using undefined everywhere, as expected, except for CNodes where
  CNode undefined is not necessarily well-formed, which affects its type.
\<close>

definition
  ao_clean :: "arch_kernel_obj \<Rightarrow> component set \<Rightarrow> arch_kernel_obj" where
  "ao_clean ao cmps \<equiv>
    (case ao
       of Arch_Structs_A.ASIDPool aobj \<Rightarrow>
            ao_override (Arch_Structs_A.ASIDPool undefined) ao cmps
        | PageTable aobj \<Rightarrow> ao_override (PageTable undefined) ao cmps
        | PageDirectory aobj \<Rightarrow> ao_override (PageDirectory undefined) ao cmps
        | DataPage aobj \<Rightarrow> DataPage aobj)" (* type only *)

definition
  ko_clean :: "kernel_object \<Rightarrow> component set \<Rightarrow> kernel_object" where
  "ko_clean ko cmps \<equiv>
    (case ko
       of CNode sz obj \<Rightarrow> ko_override (CNode sz empty) ko cmps
        | TCB obj \<Rightarrow> ko_override (TCB undefined) ko cmps
        | Endpoint obj \<Rightarrow> ko_override (Endpoint undefined) ko cmps
        | Notification obj \<Rightarrow> ko_override (Notification undefined) ko cmps
        | ArchObj obj \<Rightarrow> ArchObj (ao_clean obj cmps))"


text \<open>Combining objects\<close>

definition
  ko_combine :: "(kernel_object \<times> component set)
                 \<Rightarrow> (kernel_object \<times> component set)
                 \<Rightarrow> (kernel_object \<times> component set)" where
  "ko_combine kcmp1 kcmp2 \<equiv>
    (case kcmp1 of (o1,cs1) \<Rightarrow> (case kcmp2 of (o2,cs2) \<Rightarrow>
    (ko_override (ko_clean o1 cs1) (ko_clean o2 cs2) cs2, cs1 \<union> cs2)))"


text \<open>Updating a cap in a specific kernel object\<close>

text \<open>
  This is the non-monadic counterpart to @{term set_cap_local}.
  We use silent failure here, since we want generic lemmas to hold, such
  as that @{term set_ko_cap} preserves the kernel object type. If we returned
  undefined, we can't prove those without the extra assumption everywhere that
  @{term "cap_of ko i = Some c"}.
\<close>

definition (* non-monadic counterpart to set_cap(_local) *)
  set_ko_cap :: "kernel_object \<Rightarrow> cnode_index \<Rightarrow> cap \<Rightarrow> kernel_object" where
  "set_ko_cap ko i cap \<equiv>
    (case ko of CNode sz cn \<Rightarrow> CNode sz (cn(i \<mapsto> cap))
              | TCB tcb \<Rightarrow>
                   (if i = tcb_cnode_index 0 then
                       TCB $ tcb \<lparr> tcb_ctable := cap \<rparr>
                   else if i = tcb_cnode_index 1 then
                       TCB $ tcb \<lparr> tcb_vtable := cap \<rparr>
                   else if i = tcb_cnode_index 2 then
                       TCB $ tcb \<lparr> tcb_reply := cap \<rparr>
                   else if i = tcb_cnode_index 3 then
                       TCB $ tcb \<lparr> tcb_caller := cap \<rparr>
                   else if i = tcb_cnode_index 4 then
                       TCB $ tcb \<lparr> tcb_ipcframe := cap \<rparr>
                   else
                       ko)
              | _ \<Rightarrow> ko)"


subsection \<open>Object-component Maps\<close>

text \<open>
  When we annotate the abstract kernel heap with the components of kernel
  objects we are allowed to access at each address, we get an
  object-component map. This map is the core of the separation logic, since
  it allows us to perform local reasoning beyond the granularity of a kernel
  object. In other words, if we have a kernel object at address p in two
  kheaps, we can still call the heaps disjoint if they are annotated with
  disjoint components.

  In lemmas, ``object-component map'' is typically abbreviated to ``ocm''.
\<close>

type_synonym
  obj_comp_map = "paddr \<rightharpoonup> (kernel_object \<times> component set)"

definition
  ko_has_cap :: "kernel_object \<Rightarrow> component set \<Rightarrow> cnode_index \<Rightarrow> cap \<Rightarrow> bool"
  where
  "ko_has_cap ko cmps i c \<equiv> cap_of (ko_clean ko cmps) i = Some c \<and>
                            (cmp_of ko i) \<in> cmps"

definition
  "ocm_has_cap ocm p ko cmps i c \<equiv> ocm p = Some (ko, cmps) \<and>
                                   ko_has_cap ko cmps i c"

definition
  obj_comp_map_add :: "obj_comp_map \<Rightarrow> obj_comp_map \<Rightarrow> obj_comp_map" where
  "obj_comp_map_add h1 h2 \<equiv>
     (\<lambda>p. (case h1 p
             of Some oc1 \<Rightarrow> (case h2 p
                              of Some oc2 \<Rightarrow> Some (ko_combine oc1 oc2)
                               | None \<Rightarrow> Some oc1)
              | None \<Rightarrow> h2 p))"

text \<open>
  Disjunction (per address):
  If it's in one heap but not the other (or in neither),
  consider the object maps disjoint.

  Looking at the objects through only the components we have:
    If the objects have different types, they are not disjoint.
    If the objects have the same type, but the different heaps cover different
    components, then they are disjoint.

  Exceptions to the above when both objects have the same type:
    If an object is structurally unsound (i.e. is a cnode with entries not of
    the right length), we treat the component coverage as if it was
    @{term "UNIV"}.
    If a component set is either @{term "{}"} or includes components outside
    of sane values for the given object type, we treat it as @{term "UNIV"}.

  We need the exceptions in order to be able to define a predicate that says
  ``we have the entire object and all information about it'', and be able to
  detype/retype this object while preserving the frame rule. If we can
  construct anything separate from the entire object that also talks about the
  object's type, we cannot prove the frame rule. This means no objects with no
  components or ficticious components (they convey no information except the
  object type at that address). This also means no magical cnodes where a
  cnode of size 2 can suddenly develop a entry over 9000.
\<close>

definition
  "sane_components ko cmps \<equiv> bounded_ko ko \<and> cmps \<noteq> {}
                             \<and> cmps \<subseteq> ko_components ko"

definition
  "check_components ko cmps \<equiv> if sane_components ko cmps then cmps else UNIV"

definition
  obj_comp_map_disj :: "obj_comp_map \<Rightarrow> obj_comp_map \<Rightarrow> bool" where
  "obj_comp_map_disj h1 h2 \<equiv>
     (\<forall>p. case (h1 p, h2 p)
            of (Some (o1,c1), Some (o2,c2))
                 \<Rightarrow> a_base_type o1 = a_base_type o2
                    \<and> check_components (ko_clean o1 c1) c1
                      \<inter> check_components (ko_clean o2 c2) c2 = {}
             | _ \<Rightarrow> True)"


subsection \<open>
  State used for separation algebra; encompasses the object-component map, as well as free and available memory.
\<close>

datatype sep_state = SepState obj_comp_map "obj_ref set" "obj_ref set"
                           (* comp. map    free mem      avail mem *)

type_synonym
  sep_assert = "sep_state \<Rightarrow> bool"

translations
  (type) "sep_assert" <= (type) "sep_state \<Rightarrow> bool"

text \<open>SepState accessors\<close>

definition
  sep_state_ocm :: "sep_state \<Rightarrow> obj_comp_map" where
  "sep_state_ocm s \<equiv> case s of SepState ocm _ _ \<Rightarrow> ocm"

definition
  sep_state_free :: "sep_state \<Rightarrow> obj_ref set" where
  "sep_state_free s \<equiv> case s of SepState _ free _ \<Rightarrow> free"

definition
  sep_state_avail :: "sep_state \<Rightarrow> obj_ref set" where
  "sep_state_avail s \<equiv> case s of SepState _ _ avail \<Rightarrow> avail"

lemmas sep_state_accessors =
  sep_state_ocm_def sep_state_free_def sep_state_avail_def

definition
  lift_sep_state :: "'z ki_state \<Rightarrow> sep_state" where
  "lift_sep_state ki \<equiv>
     let kh = kheap (ki_kernel_state ki)
     in SepState (\<lambda>p. case kh p
                        of Some obj \<Rightarrow> Some (ko_clean obj (ki_components ki p),
                                             ki_components ki p)
                         | _ \<Rightarrow> None)
                 (ki_free_mem ki)
                 (ki_available_mem ki)"

text \<open>
  Lifting a kernel state @{text "s"} onto an existing kernel init state
  @{text "kis"}.\<close>
abbreviation
  "kis_lift kis s \<equiv> lift_sep_state (kis\<lparr>ki_kernel_state := s\<rparr>)"

definition
  kheap_shadow :: "obj_comp_map \<Rightarrow> paddr \<Rightarrow> paddr set" where
  "kheap_shadow kh p \<equiv>
     set (len_seq (p+1) (2 ^ t_obj_bits (fst (the (kh p))) - 1))"

definition
  "kheap_shadows kh \<equiv> \<Union>(kheap_shadow kh ` dom kh)"

text \<open>Addresses used up by objects in the kernel heap\<close>
definition
  kheap_dom :: "(obj_comp_map) \<Rightarrow> paddr set" where
  "kheap_dom kh \<equiv> dom kh \<union> kheap_shadows kh"

definition
  sep_disj :: "sep_state \<Rightarrow> sep_state \<Rightarrow> bool" where
  (* if we try to combine two sane heaps, a region can't end up being:
     - free in one and available in the other
     - free/available in one and in the heap in the other
     - in both heaps with the same component
     - an object in one heap and a shadow (the Nones that follow an object
       until its last memory address) in the other
  *)
  "sep_disj s1 s2 =
     (case s1 of SepState kh1 free1 avail1 \<Rightarrow>
     (case s2 of SepState kh2 free2 avail2 \<Rightarrow>

     ((free1 \<union> avail1) \<inter> (free2 \<union> avail2) = {} \<and>
      kheap_dom kh1 \<inter> (free2 \<union> avail2) = {} \<and>
      kheap_dom kh2 \<inter> (free1 \<union> avail1) = {} \<and>
      obj_comp_map_disj kh1 kh2 \<and>
      kheap_shadows kh1 \<inter> dom kh2 = {} \<and>
      kheap_shadows kh2 \<inter> dom kh1 = {}) ))"

definition
  sep_add :: "sep_state \<Rightarrow> sep_state \<Rightarrow> sep_state" where
  "sep_add s1 s2 =
     (case s1 of SepState kh1 free1 avail1 \<Rightarrow>
     (case s2 of SepState kh2 free2 avail2 \<Rightarrow>
     SepState (obj_comp_map_add kh1 kh2) (free1 \<union> free2) (avail1 \<union> avail2)
     ))"

definition
  sep_empty :: "sep_state" where
  "sep_empty = SepState empty {} {}"


subsection \<open>Maps-to Predicates\<close>

text \<open>pretty raw function to talk about a single object's components at a given address\<close>
definition
  sep_map_base :: "paddr \<Rightarrow> kernel_object \<Rightarrow> component set \<Rightarrow> sep_assert" where
  "sep_map_base p ko cmps s \<equiv> (case s of SepState ocm free avail \<Rightarrow>
        ocm p = Some (ko_clean ko cmps, cmps) \<and>
        sane_components (ko_clean ko cmps) cmps \<and>
        dom ocm = {p} \<and> (* sep_conj takes care of shadow intersections *)
        is_aligned p (t_obj_bits ko) \<and>
        free = {} \<and>
        avail = {})"
  (* XXX: can this be the same as the empty assertion when cmps = {}? *)

text \<open>same thing, but talking about the entire object at an address\<close>
definition
  sep_map_ko :: "paddr \<Rightarrow> kernel_object \<Rightarrow> sep_assert" where
  "sep_map_ko p ko \<equiv> sep_map_base p ko (ko_components ko)"

text \<open>
  An object of the specified type with a set cap. We need to specify the type
  in order to be able to reassemble cnodes, and also to not have to prove
  things such as that @{const set_cap} doesn't change the object's type.\<close>
definition
  sep_map_cap :: "a_type \<Rightarrow> cslot_ptr \<Rightarrow> cap \<Rightarrow> sep_assert" where
  "sep_map_cap atyp cptr cap \<equiv> case cptr of (p,i) \<Rightarrow>
     (\<lambda>s. \<exists>ko. sep_map_base p ko {cmp_of ko i} s \<and>
               a_base_type ko = atyp \<and>
               cap_of ko i = Some cap)"

text \<open>declaring a region of memory is free (unallocated)\<close>
definition
  sep_free :: "paddr \<Rightarrow> nat \<Rightarrow> sep_assert" where
  "sep_free p sz s = (case s of SepState ocm free avail \<Rightarrow>
     (dom ocm = {} \<and> free = set (len_seq p sz) \<and> avail = {}))"

text \<open>declaring a region of memory is available (allocated but untyped)\<close>
definition
  sep_available :: "paddr \<Rightarrow> nat \<Rightarrow> sep_assert" where
  "sep_available p sz s = (case s of SepState ocm free avail \<Rightarrow>
     (dom ocm = {} \<and> free = {} \<and> avail = set (len_seq p sz)))"


subsection \<open>Cap-level Updates of the Kernel Init State\<close>

text \<open>
  The @{term sep_update_cap} function is equivalent to what
  @{term set_cap_local} does at the monadic kernel state level, but phrased
  non-monadically and more conveniently for the separation state level.
\<close>

definition
  sep_update_cap :: "cslot_ptr \<Rightarrow> cap \<Rightarrow> sep_state \<Rightarrow> sep_state" where
  "sep_update_cap cp cap s \<equiv> (case cp of (p,i) \<Rightarrow>
     (case s of SepState ocm f a \<Rightarrow>
     SepState (ocm(p \<mapsto> (set_ko_cap (fst (the (ocm p))) i cap,
                        snd (the (ocm p))))) f a ))"



section \<open>Proofs\<close> (* ------------------------------------------------- *)

subsection \<open>Component structure of objects\<close>

lemma bounded_ko_t_obj_bits:
  "bounded_ko ko \<Longrightarrow> t_obj_bits ko < word_bits"
  by (clarsimp simp: bounded_ko_def cte_level_bits_def word_bits_def
                     bounded_cs_size_def a_base_type_bits_def a_base_type_def
                     pageBitsForSize_def pageBits_def
               split: kernel_object.splits arch_kernel_obj.splits
                      vmpage_size.splits)

lemma tcb_eq: (* so the simplifier doesn't barf on tcb_override_commute *)
  "\<lbrakk> tcb_state (tcb1::Structures_A.tcb) = tcb_state (tcb2::Structures_A.tcb) ;
     tcb_fault_handler tcb1 = tcb_fault_handler tcb2 ;
     tcb_ipc_buffer tcb1 = tcb_ipc_buffer tcb2 ;
     tcb_context tcb1 = tcb_context tcb2 ;
     tcb_fault tcb1 = tcb_fault tcb2 ;
     tcb_ctable tcb1 = tcb_ctable tcb2 ;
     tcb_vtable tcb1 = tcb_vtable tcb2 ;
     tcb_reply tcb1 = tcb_reply tcb2 ;
     tcb_caller tcb1 = tcb_caller tcb2 ;
     tcb_ipcframe tcb1 = tcb_ipcframe tcb2 ;
     tcb_bound_notification tcb1 = tcb_bound_notification tcb2 \<rbrakk> \<Longrightarrow> tcb1 = tcb2"
  by (cases tcb1, cases tcb2) auto

lemma tcb_cnode_index_not_Nil:
  "tcb_cnode_index i \<noteq> []"
  by (clarsimp simp: tcb_cnode_index_def)

lemma tcb_cnode_index_Nil_False [simp]:
  "(tcb_cnode_index i = []) = False"
  "([] = tcb_cnode_index i) = False"
  by (auto simp: tcb_cnode_index_not_Nil tcb_cnode_index_not_Nil[symmetric])


subsection \<open>Component-wise Combining of Kernel Objects\<close>

lemma tcb_override_index_simps:
  "tcb_override tcb tcb' {tcb_cnode_index 0}
     = tcb \<lparr>tcb_ctable := tcb_ctable tcb'\<rparr>"
  "tcb_override tcb tcb' {tcb_cnode_index (Suc 0)}
     = tcb \<lparr>tcb_vtable := tcb_vtable tcb'\<rparr>"
  "tcb_override tcb tcb' {tcb_cnode_index 2}
     = tcb \<lparr>tcb_reply := tcb_reply tcb'\<rparr>"
  "tcb_override tcb tcb' {tcb_cnode_index 3}
     = tcb \<lparr>tcb_caller := tcb_caller tcb'\<rparr>"
  "tcb_override tcb tcb' {tcb_cnode_index 4}
     = tcb \<lparr>tcb_ipcframe := tcb_ipcframe tcb'\<rparr>"
  by (simp_all add: tcb_override_def)

lemma tcb_field_cmp_right_simps:
  "[] \<in> cmps \<Longrightarrow> tcb_state (tcb_override tcb tcb' cmps) = tcb_state tcb'"
  "[] \<in> cmps \<Longrightarrow> tcb_fault_handler (tcb_override tcb tcb' cmps)
                   = tcb_fault_handler tcb'"
  "[] \<in> cmps \<Longrightarrow> tcb_ipc_buffer (tcb_override tcb tcb' cmps)
                   = tcb_ipc_buffer tcb'"
  "[] \<in> cmps \<Longrightarrow> tcb_context (tcb_override tcb tcb' cmps)
                   = tcb_context tcb'"
  "[] \<in> cmps \<Longrightarrow> tcb_fault (tcb_override tcb tcb' cmps)
                   = tcb_fault tcb'"
  "[] \<in> cmps \<Longrightarrow> tcb_bound_notification (tcb_override tcb tcb' cmps) = tcb_bound_notification tcb'"
  "tcb_cnode_index 0 \<in> cmps \<Longrightarrow> tcb_ctable (tcb_override tcb tcb' cmps)
                                  = tcb_ctable tcb'"
  "tcb_cnode_index (Suc 0) \<in> cmps \<Longrightarrow> tcb_vtable (tcb_override tcb tcb' cmps)
                                        = tcb_vtable tcb'"
  "tcb_cnode_index 2 \<in> cmps \<Longrightarrow> tcb_reply (tcb_override tcb tcb' cmps)
                                  = tcb_reply tcb'"
  "tcb_cnode_index 3 \<in> cmps \<Longrightarrow> tcb_caller (tcb_override tcb tcb' cmps)
                                  = tcb_caller tcb'"
  "tcb_cnode_index 4 \<in> cmps \<Longrightarrow> tcb_ipcframe (tcb_override tcb tcb' cmps)
                                  = tcb_ipcframe tcb'"
  by (simp_all add: tcb_override_def)

lemma tcb_override_index_cmps_simps:
  "tcb_cnode_index 0 \<in> cmps
   \<Longrightarrow> tcb_override ko (ko'\<lparr>tcb_ctable := cap\<rparr>) cmps
   = tcb_override ko ko' cmps \<lparr>tcb_ctable := cap\<rparr>"
  "tcb_cnode_index (Suc 0) \<in> cmps
   \<Longrightarrow> tcb_override ko (ko'\<lparr>tcb_vtable := cap\<rparr>) cmps
   = tcb_override ko ko' cmps \<lparr>tcb_vtable := cap\<rparr>"
  "tcb_cnode_index 2 \<in> cmps
   \<Longrightarrow> tcb_override ko (ko'\<lparr>tcb_reply := cap\<rparr>) cmps
   = tcb_override ko ko' cmps \<lparr>tcb_reply := cap\<rparr>"
  "tcb_cnode_index 3 \<in> cmps
   \<Longrightarrow> tcb_override ko (ko'\<lparr>tcb_caller := cap\<rparr>) cmps
   = tcb_override ko ko' cmps \<lparr>tcb_caller := cap\<rparr>"
  "tcb_cnode_index 4 \<in> cmps
   \<Longrightarrow> tcb_override ko (ko'\<lparr>tcb_ipcframe := cap\<rparr>) cmps
   = tcb_override ko ko' cmps \<lparr>tcb_ipcframe := cap\<rparr>"
  by (simp_all add: tcb_override_def)

lemma tcb_override_index_sub_cmps_simps:
  "tcb_override ko ko' (cmps - {tcb_cnode_index 0}) \<lparr> tcb_ctable := cap \<rparr>
   = tcb_override ko ko' cmps \<lparr> tcb_ctable := cap \<rparr>"
  "tcb_override ko ko' (cmps - {tcb_cnode_index (Suc 0)}) \<lparr> tcb_vtable := cap \<rparr>
   = tcb_override ko ko' cmps \<lparr> tcb_vtable := cap \<rparr>"
  "tcb_override ko ko' (cmps - {tcb_cnode_index 2}) \<lparr> tcb_reply := cap \<rparr>
   = tcb_override ko ko' cmps \<lparr> tcb_reply := cap \<rparr>"
  "tcb_override ko ko' (cmps - {tcb_cnode_index 3}) \<lparr> tcb_caller := cap \<rparr>
   = tcb_override ko ko' cmps \<lparr> tcb_caller := cap \<rparr>"
  "tcb_override ko ko' (cmps - {tcb_cnode_index 4}) \<lparr> tcb_ipcframe := cap \<rparr>
   = tcb_override ko ko' cmps \<lparr> tcb_ipcframe := cap \<rparr>"
  by (simp_all add: tcb_override_def)

text \<open>
  Unfolding @{text tcb_override_def} the index is known is a really bad idea
  in terms of simplifier performance in actual lemmas. These rules help avoid
  that scenario.\<close>
lemmas tcb_override_index_assist = tcb_override_index_simps
         tcb_override_index_cmps_simps tcb_override_index_sub_cmps_simps
         tcb_field_cmp_right_simps

lemma ko_clean_preserves_type [simp]:
  "a_base_type (ko_clean ko cmps) = a_base_type ko"
  by (auto simp: ko_clean_def ko_override_def ao_clean_def ao_override_def
           split: kernel_object.splits arch_kernel_obj.splits)

lemma t_obj_bits_ko_clean_simp [simp]:
  "t_obj_bits (ko_clean ko cmps) = t_obj_bits ko"
  by (clarsimp split: Structures_A.kernel_object.splits arch_kernel_obj.splits)

lemma ko_components_ko_clean_simp [simp]:
  "ko_components (ko_clean ko cmps) = ko_components ko"
  by (clarsimp split: Structures_A.kernel_object.splits arch_kernel_obj.splits)

lemma ko_override_a_base_type [simp]:
  "a_base_type o1 = a_base_type o2
   \<Longrightarrow> a_base_type (ko_override o1 o2 c2) = a_base_type o2"
  by (clarsimp simp: a_base_type_def ko_override_def ao_override_def
               split: kernel_object.splits arch_kernel_obj.splits)

lemma ao_clean_twice [simp]:
  "ao_clean (ao_clean ao cmps) cmps = ao_clean ao cmps"
  by (fastforce split: arch_kernel_obj.splits
                simp: ao_clean_def ao_override_def)

lemma ko_clean_twice_subset:
  "\<lbrakk> cmps' \<subseteq> cmps \<rbrakk> \<Longrightarrow> ko_clean (ko_clean ko cmps) cmps' = ko_clean ko cmps'"
  apply (clarsimp simp: ko_clean_def ao_clean_def ko_override_def
                        ao_override_def
                  split: kernel_object.splits arch_kernel_obj.splits)
  apply (fastforce intro!: tcb_eq simp: tcb_override_def)
  done

lemma ko_clean_twice [simp]:
  "ko_clean (ko_clean ko cmps) cmps = ko_clean ko cmps"
  by (simp add: ko_clean_twice_subset)

lemma ko_clean_id:
  "bounded_ko ko \<Longrightarrow> ko_clean ko (ko_components ko) = ko"
  apply (clarsimp simp: ko_clean_def ko_override_def ao_clean_def
                        ao_override_def bounded_ko_def
                  split: kernel_object.splits arch_kernel_obj.splits)
   apply (clarsimp intro!: ext simp: bounded_cs_size_def bounded_cnode_n_def)
   apply (case_tac "fun bs", simp, clarsimp simp: unat_of_bl_length dom_def)
  apply (fastforce intro!: tcb_eq simp: tcb_override_index_assist)
  done

lemma ko_clean_ko_override_id:
  "\<lbrakk> a_base_type ko = a_base_type ko' ; cmps \<inter> cmps' = {} \<rbrakk>
   \<Longrightarrow> ko_clean (ko_override ko ko' cmps) cmps' = ko_clean ko cmps'"
  apply (cases ko)
      apply (simp_all add: ko_clean_def ko_override_def a_base_type_def
                      split: kernel_object.splits)
      apply fastforce
     apply (rule tcb_eq | fastforce simp: tcb_override_def)+
  apply (case_tac arch_kernel_obj)
  apply (fastforce split: arch_kernel_obj.splits
                   simp: ao_clean_def ao_override_def)+
  done

lemma ao_override_pull_out_ao_clean [simp]:
  "\<lbrakk> a_base_type (ArchObj ao1) = a_base_type (ArchObj ao2) \<rbrakk>
   \<Longrightarrow> ao_override (ao_clean ao1 cmps1) ao2 cmps2
      = ao_clean (ao_override ao1 ao2 cmps2) (cmps1 \<union> cmps2)"
  by (auto simp: ao_clean_def ao_override_def
           split: arch_kernel_obj.splits)

lemma ko_override_pull_out_ko_clean [simp]:
  "\<lbrakk> a_base_type ko1 = a_base_type ko2 \<rbrakk>
   \<Longrightarrow> ko_override (ko_clean ko1 cmps1) ko2 cmps2
      = ko_clean (ko_override ko1 ko2 cmps2) (cmps1 \<union> cmps2)"
  by (clarsimp simp: ko_clean_def ko_override_def a_base_type_def
                  split: kernel_object.splits)
     (auto simp: tcb_override_def)

lemma ko_override_ko_clean_right [simp]:
  "\<lbrakk> a_base_type ko1 = a_base_type ko2 \<rbrakk>
   \<Longrightarrow> (ko_override ko1 (ko_clean ko2 cmps2) cmps2)
      = (ko_override ko1 ko2 cmps2) "
  apply (clarsimp simp: ko_clean_def ko_override_def a_base_type_def
                  split: kernel_object.splits)
    apply (fastforce simp: tcb_override_def)+
  apply (fastforce simp: ao_override_def ao_clean_def
                   split: arch_kernel_obj.splits)
  done

lemma ko_override_self [simp]:
  "ko_override ko ko cmps = ko"
  by (cases ko)
     (auto simp: ko_override_def tcb_override_def ao_override_def
           split: arch_kernel_obj.splits)

lemma cap_of_ko_cleanD:
  "\<lbrakk> cap_of (ko_clean ko cmps) i = Some c ; (cmp_of ko i) \<in> cmps \<rbrakk>
   \<Longrightarrow> cap_of ko i = Some c"
  unfolding cap_of_def ko_clean_def
  by (clarsimp simp: ko_override_def a_base_type_cmp_of_def tcb_cnode_map_def
                     tcb_override_index_assist
               split: kernel_object.splits option.splits if_split_asm)

lemma cap_of_ko_clean_contained_cap:
  "cmp_of ko i \<in> cmps
   \<Longrightarrow> cap_of (ko_clean ko cmps) i = cap_of ko i"
  unfolding cap_of_def ko_clean_def
  by (clarsimp simp: ko_override_def a_base_type_cmp_of_def
               split: kernel_object.splits)
     (fastforce simp: tcb_cnode_map_def a_base_type_cmp_of_def
                      tcb_override_index_assist)

lemma cap_of_ko_clean_same_cap [simp]:
  "cap_of (ko_clean ko {cmp_of ko i}) i = cap_of ko i"
  by (clarsimp simp: cap_of_ko_clean_contained_cap)

lemma ko_clean_one_cap_eq:
  "\<lbrakk> cap_of ko i = Some cap ; cap_of ko' i = Some cap ;
     a_base_type ko = a_base_type ko' ;
     cmp = {cmp_of ko' i} \<rbrakk>
   \<Longrightarrow> ko_clean ko cmp = ko_clean ko' cmp"
  apply (clarsimp simp: ko_clean_def a_base_type_def cap_of_def
                  split: kernel_object.splits)
   apply (fastforce simp: ko_override_def a_base_type_cmp_of_def
                    split: if_split_asm)
  apply (clarsimp simp: tcb_cnode_map_def a_base_type_cmp_of_def
                        ko_override_def tcb_override_index_assist
                  split: if_split_asm)
  done

lemma tcb_override_commute:
  "c1 \<inter> c2 = {}
   \<Longrightarrow> tcb_override (tcb_override undefined tcb1 c1)
                   (tcb_override undefined tcb2 c2) c2
      = tcb_override (tcb_override undefined tcb2 c2)
                     (tcb_override undefined tcb1 c1) c1"
  by (rule tcb_eq)
     (fastforce simp: tcb_override_def)+

lemma tcb_override_assoc:
  "tcb_override (tcb_override (a::Structures_A.tcb) b cs1) c cs2
   = tcb_override a (tcb_override b c cs2) (cs1 \<union> cs2)"
  by (fastforce simp: tcb_override_def)

lemma tcb_override_twice_same [simp]:
  "tcb_override x (tcb_override (x::Structures_A.tcb) y cmps) cmps =
       tcb_override x y cmps"
  by (fastforce simp: tcb_override_def intro!: tcb_eq)

lemma tcb_cnode_map_tcb_override_left:
  "i \<notin> cmps
   \<Longrightarrow> tcb_cnode_map (tcb_override tcb tcb' cmps) i = tcb_cnode_map tcb i"
  apply (clarsimp simp: tcb_cnode_map_def tcb_override_def
                  split: if_split_asm option.splits)
  apply (rule conjI | clarsimp simp: eval_nat_numeral)+
  done

lemma tcb_cnode_map_tcb_override_right:
  "i \<in> cmps
   \<Longrightarrow> tcb_cnode_map (tcb_override tcb tcb' cmps) i = tcb_cnode_map tcb' i"
  by (fastforce simp: tcb_cnode_map_def tcb_override_index_assist
                split: if_split_asm option.splits)

lemmas tcb_cnode_map_tcb_overrides = tcb_cnode_map_tcb_override_right
                                     tcb_cnode_map_tcb_override_left

lemma cap_of_ko_override_left:
  "\<lbrakk> cmp_of ko i \<notin> cmps ; a_base_type ko = a_base_type ko' \<rbrakk>
   \<Longrightarrow> cap_of (ko_override ko ko' cmps) i = cap_of ko i"
  by (clarsimp simp: a_base_type_def cap_of_def ko_clean_def
                     ko_override_def a_base_type_cmp_of_def
                     tcb_cnode_map_tcb_overrides
               split: kernel_object.splits option.splits)

lemma cap_of_ko_override_right:
  "\<lbrakk> cmp_of ko i \<in> cmps ; a_base_type ko = a_base_type ko' \<rbrakk>
   \<Longrightarrow> cap_of (ko_override ko ko' cmps) i = cap_of ko' i"
  by (clarsimp simp: a_base_type_def cap_of_def ko_clean_def
                     ko_override_def a_base_type_cmp_of_def
                     tcb_cnode_map_tcb_overrides
               split: kernel_object.splits option.splits)

lemmas cap_of_ko_overrides = cap_of_ko_override_right cap_of_ko_override_left

lemma cap_of_ko_clean:
  "\<lbrakk> cmp_of ko i \<in> cmps \<rbrakk>
   \<Longrightarrow> cap_of (ko_clean ko cmps) i = cap_of ko i"
  by (clarsimp simp: cap_of_def ko_clean_def a_base_type_cmp_of_def
                     ko_override_def
                     a_base_type_def tcb_cnode_map_tcb_overrides
               split: kernel_object.splits)+

lemma bounded_ko_clean:
  "bounded_ko ko \<Longrightarrow> bounded_ko (ko_clean ko cmps)"
  by (auto simp: bounded_ko_def ko_clean_def ko_override_def
                 bounded_cs_size_def bounded_cnode_n_def
           split: kernel_object.splits if_split_asm)

lemma bounded_ko_override:
  "\<lbrakk> bounded_ko o1 ; bounded_ko o2 ; a_base_type o1 = a_base_type o2 \<rbrakk>
       \<Longrightarrow> bounded_ko (ko_override o1 o2 cmps)"
  by (fastforce simp: bounded_ko_def ko_override_def bounded_cs_size_def
                      a_base_type_def bounded_cnode_n_def
                split: kernel_object.splits if_split_asm)

lemma bounded_ko_clean_ko_override:
  "\<lbrakk> bounded_ko (ko_clean o1 c1) ; bounded_ko (ko_clean o2 c2) ;
     a_base_type o1 = a_base_type o2\<rbrakk>
   \<Longrightarrow> bounded_ko (ko_clean (ko_override o1 o2 c2) (c1 \<union> c2))"
  by (fastforce simp: bounded_ko_def ko_clean_def ko_override_def
                      a_base_type_def bounded_cs_size_def bounded_cnode_n_def
                split: kernel_object.splits option.splits if_split_asm)
  (* XXX: long-running proof *)

lemma sane_components_ko_clean_ko_override:
  "\<lbrakk> sane_components (ko_clean o1 c1) c1 ; sane_components (ko_clean o2 c2) c2;
     a_base_type o1 = a_base_type o2 \<rbrakk>
   \<Longrightarrow> sane_components (ko_clean (ko_override o1 o2 c2) (c1 \<union> c2)) (c1 \<union> c2)"
  by (clarsimp simp: sane_components_def bounded_ko_clean_ko_override)

lemma bounded_ko_clean_ko_overrideD:
  "\<lbrakk> bounded_ko (ko_clean (ko_override o1 o2 c2) (c1 \<union> c2)) ;
     c1 \<inter> c2 = {} ; a_base_type o1 = a_base_type o2 \<rbrakk>
   \<Longrightarrow> bounded_ko (ko_clean o1 c1) \<and> bounded_ko (ko_clean o2 c2)"
  by (fastforce simp: bounded_ko_def a_base_type_def ko_clean_def
                     ko_override_def bounded_cs_size_def bounded_cnode_n_def
               split: kernel_object.splits if_split_asm)

lemma sane_components_ko_clean_ko_overrideD:
  "\<lbrakk> sane_components (ko_clean (ko_override o1 o2 c2) (c1 \<union> c2)) (c1 \<union> c2) ;
     c1 \<inter> c2 = {} ; c1 \<noteq> {} ; c2 \<noteq> {} ; a_base_type o1 = a_base_type o2 \<rbrakk>
   \<Longrightarrow> sane_components (ko_clean o1 c1) c1 \<and>
       sane_components (ko_clean o2 c2) c2"
  by (fastforce simp: sane_components_def dest!: bounded_ko_clean_ko_overrideD)

lemma ko_override_assoc:
  "\<lbrakk> a_base_type o1 = a_base_type o2 ; a_base_type o2 = a_base_type o3 \<rbrakk>
   \<Longrightarrow> ko_override (ko_override o1 o2 cs1) o3 cs2
   = ko_override o1 (ko_override o2 o3 cs2) (cs1 \<union> cs2)"
  unfolding a_base_type_def
  apply (clarsimp split: kernel_object.splits)
      apply (clarsimp intro!: ext simp: ko_override_def tcb_override_assoc)+
  apply (clarsimp split: arch_kernel_obj.splits)
     apply (clarsimp intro!: ext simp: ao_override_def)+
  done

lemma ko_combine_assoc:
  "\<lbrakk> a_base_type o1 = a_base_type o2 ; a_base_type o2 = a_base_type o3 \<rbrakk>
   \<Longrightarrow> ko_combine (ko_combine (o1,c1) (o2,c2)) (o3,c3)
      = ko_combine (o1,c1) (ko_combine (o2,c2) (o3,c3))"
  by (clarsimp simp: ko_combine_def ko_override_assoc Un_assoc)

lemma ko_combine_commute:
  "\<lbrakk> check_components (ko_clean o1 c1) c1
      \<inter> check_components (ko_clean o2 c2) c2 = {} ;
     a_base_type o1 = a_base_type o2 \<rbrakk>
   \<Longrightarrow> ko_combine (o1,c1) (o2,c2) = ko_combine (o2,c2) (o1,c1)"
  unfolding ko_combine_def
  by (clarsimp simp: Un_commute ko_override_def ko_clean_def
                     check_components_def
                     tcb_override_commute ao_clean_def sane_components_def
               split: kernel_object.splits arch_kernel_obj.splits if_split_asm)
     \<comment> \<open>ao_override_def is too much for auto/fastforce above\<close>
     (auto intro!: ext simp: ao_override_def split: if_split_asm)


subsection \<open>
  Check on Kernel Object and Components for Considering Disjunction\<close>

lemma check_components_id:
  "\<lbrakk> bounded_ko ko ; cmps \<subseteq> ko_components ko ; cmps \<noteq> {} \<rbrakk>
   \<Longrightarrow> check_components ko cmps = cmps"
  by (clarsimp simp: check_components_def sane_components_def)

lemma check_components_UNIV:
  "check_components ko {} = UNIV"
  "\<not> bounded_ko ko \<Longrightarrow> check_components ko cmps = UNIV"
  "\<not> (cmps \<subseteq> ko_components ko) \<Longrightarrow> check_components ko cmps = UNIV"
  by (auto simp: check_components_def sane_components_def)

lemma check_components_not_empty:
  "check_components ko cmps \<noteq> {}"
  by (clarsimp simp: check_components_def sane_components_def)

lemma check_components_Int_emptyD:
  assumes int: "check_components o1 c1 \<inter> check_components o2 c2 = {}"
  shows "c1 \<noteq> {} \<and> c2 \<noteq> {} \<and> bounded_ko o1 \<and> bounded_ko o2 \<and>
      c1 \<subseteq> ko_components o1 \<and> c2 \<subseteq> ko_components o2 \<and> c1 \<inter> c2 = {}"
proof -

  from int have noteq: "c1 \<noteq> {} \<and> c2 \<noteq> {}"
    by (auto simp: check_components_UNIV check_components_not_empty)

  moreover
  from int have bounded: "bounded_ko o1 \<and> bounded_ko o2"
    by (auto intro: ccontr
             simp: check_components_UNIV check_components_not_empty)
  moreover
  from int have subs: "c1 \<subseteq> ko_components o1" "c2 \<subseteq> ko_components o2"
    by - (rule ccontr,
          simp add: check_components_UNIV check_components_not_empty)+

  ultimately show ?thesis using int
    by (simp add: check_components_id)
qed


subsection \<open>Updating a cap in a specific kernel object\<close>

lemma a_base_type_set_ko_cap [simp]:
  "a_base_type (set_ko_cap ko i cap) = a_base_type ko"
  by (cases ko, auto simp: set_ko_cap_def cap_of_def tcb_cnode_map_def)

lemma cap_of_set_ko_cap [simp]:
  "cap_of ko i = Some c \<Longrightarrow> cap_of (set_ko_cap ko i cap) i = Some cap"
  by (cases ko, auto simp: set_ko_cap_def cap_of_def tcb_cnode_map_def
                     split: if_split_asm)

lemma cap_of_set_ko_cap_via_other:
  "\<lbrakk> a_base_type ko = a_base_type ko' ; cap_of ko' i = Some cap' \<rbrakk>
   \<Longrightarrow> cap_of (set_ko_cap ko i cap) i = Some cap"
  by (clarsimp simp: cap_of_def set_ko_cap_def a_base_type_def
                     tcb_cnode_map_def
               split: kernel_object.splits)

lemma bounded_set_ko_cap:
  "\<lbrakk> bounded_ko ko ; cap_of ko i = Some c \<rbrakk>
   \<Longrightarrow> bounded_ko (set_ko_cap ko i cap)"
  by (fastforce simp: bounded_ko_def set_ko_cap_def cap_of_def
                      tcb_cnode_map_def bounded_cs_size_def bounded_cnode_n_def
               split: kernel_object.splits)

lemma bounded_ko_clean_set_ko_cap:
  "\<lbrakk> bounded_ko (ko_clean ko cmps) ; cap_of ko i = Some c ; cmp_of ko i \<in> cmps \<rbrakk>
   \<Longrightarrow> bounded_ko (ko_clean (set_ko_cap ko i cap) cmps)"
  by (fastforce simp: bounded_ko_def set_ko_cap_def cap_of_def ko_clean_def
                      ko_override_def tcb_cnode_map_def a_base_type_cmp_of_def
                      bounded_cs_size_def bounded_cnode_n_def
                split: kernel_object.splits if_split_asm)

lemma ko_override_is_set_ko_cap:
  "\<lbrakk> cap_of ko' i = Some cap' ; a_base_type ko = a_base_type ko' \<rbrakk>
   \<Longrightarrow> ko_override ko ko' {cmp_of ko' i} = set_ko_cap ko i cap'"
  apply (clarsimp simp: set_ko_cap_def cap_of_def ko_override_def
                        a_base_type_def
                  split: kernel_object.splits arch_kernel_obj.splits)
   apply (clarsimp intro!: ext simp: a_base_type_cmp_of_def)
  apply (fastforce simp: tcb_cnode_map_def a_base_type_cmp_of_def
                         tcb_override_index_assist)
  done

lemma ko_override_with_set_ko_cap:
  "\<lbrakk> a_base_type ko = a_base_type ko' ; valid_cnode_index ko' i \<rbrakk>
   \<Longrightarrow> ko_override ko (set_ko_cap ko' i cap) {cmp_of ko' i}
       = set_ko_cap ko i cap"
  apply (clarsimp simp: set_ko_cap_def abt_valid_cnode_index_def
                        a_base_type_def a_base_type_cmp_of_def
                  split: kernel_object.splits)
   apply (fastforce simp: ko_override_def tcb_override_index_assist)+
  done

lemma ko_override_set_ko_cap:
  "\<lbrakk> a_base_type ko = a_base_type ko' ; cmp_of ko i \<in> cmps ;
     cmps \<inter> cmps' = {} ; cap_of (ko_clean ko cmps) i = Some c \<rbrakk>
   \<Longrightarrow>
   (ko_override (ko_clean (set_ko_cap ko i cap) cmps)
                (ko_clean ko' cmps') cmps')
   = (set_ko_cap (ko_override (ko_clean ko cmps)
                              (ko_clean ko' cmps') cmps') i cap)"
  apply (frule (1) cap_of_ko_cleanD)
  apply (clarsimp simp: ko_clean_def ko_override_def a_base_type_def
                        a_base_type_cmp_of_def cap_of_def
                  split: kernel_object.splits option.splits)
   apply (fastforce simp: set_ko_cap_def)
  apply (clarsimp simp: set_ko_cap_def tcb_cnode_map_def split: if_split_asm)
      apply (rule tcb_eq | fastforce simp: tcb_override_def)+
      (* XXX: long-running proof *)
  done

lemma ko_clean_set_ko_cap:
  "\<lbrakk> cmp_of ko i \<in> cmps \<rbrakk>
   \<Longrightarrow>
   ko_clean (set_ko_cap ko i cap) cmps = set_ko_cap (ko_clean ko (cmps)) i cap"
  apply (clarsimp simp: ko_clean_def a_base_type_def a_base_type_cmp_of_def
                        cap_of_def ko_override_def
                  split: kernel_object.splits option.splits)
      apply (fastforce simp: set_ko_cap_def)
     apply (simp_all add: set_ko_cap_def)
  apply (fastforce simp: tcb_override_index_assist)
  done

lemma ko_clean_set_ko_cap': (* more specific version *)
  "\<lbrakk> cmp_of ko i \<in> cmps ; cap_of (set_ko_cap ko i cap) i = Some cap \<rbrakk>
   \<Longrightarrow>
   ko_clean (set_ko_cap ko i cap) cmps
    = set_ko_cap (ko_clean ko (cmps - {cmp_of ko i})) i cap"
  apply (clarsimp simp: ko_clean_def a_base_type_def a_base_type_cmp_of_def
                        cap_of_def ko_override_def
                  split: kernel_object.splits option.splits)
      apply (fastforce simp: set_ko_cap_def)
     apply (simp_all add: set_ko_cap_def)
   apply (clarsimp split: if_split_asm)
  apply (clarsimp split: if_split_asm)
       apply (simp add: tcb_override_index_assist tcb_cnode_map_def)+
  done

lemma ko_clean_set_ko_cap_id:
  "\<lbrakk> cmp_of ko i \<notin> cmps \<rbrakk>
   \<Longrightarrow> ko_clean (set_ko_cap ko i cap) cmps = ko_clean ko cmps"
  apply (cases ko)
      apply (clarsimp simp: set_ko_cap_def ko_clean_def ko_override_def
                            a_base_type_cmp_of_def)
      apply fastforce
     apply (clarsimp simp: set_ko_cap_def ko_clean_def a_base_type_cmp_of_def
                           ko_override_def
                     split: if_split_asm)
     apply (rule conjI | rule tcb_eq | fastforce simp: tcb_override_def)+
    apply (clarsimp simp: set_ko_cap_def)+
  done

lemma valid_cnode_index_cap_of_set_ko_cap:
  "\<lbrakk> valid_cnode_index ko i \<rbrakk>
   \<Longrightarrow> cap_of (set_ko_cap ko i cap) i = Some cap"
  apply (cases ko, simp_all add: abt_valid_cnode_index_def
                                 a_base_type_def set_ko_cap_def cap_of_def
                   split: kernel_object.splits)
  apply (fastforce simp: tcb_override_index_assist tcb_cnode_map_def)
  done

lemma abt_valid_cnode_index_singleton_component_subset:
  "\<lbrakk> abt_valid_cnode_index atyp i ; 0 < length i \<rbrakk>
   \<Longrightarrow> {a_base_type_cmp_of atyp i} \<subset> a_base_type_components atyp"
  apply (clarsimp simp: abt_valid_cnode_index_def a_base_type_cmp_of_def
                  split: a_type.splits)
   apply fastforce
  apply (erule bl_length_set_singleton_subset)
  done

lemma abt_valid_cnode_index_in_components:
  "abt_valid_cnode_index atyp i \<Longrightarrow> i \<in> a_base_type_components atyp"
  by (clarsimp simp: abt_valid_cnode_index_def a_base_type_components_def
               split: a_type.splits)


subsection \<open>Object-component Maps\<close>

lemma ocm_disj_empty [simp]:
  "obj_comp_map_disj cmps Map.empty"
  by (auto simp: obj_comp_map_disj_def split: option.splits)

lemma ocm_disj_commute:
  "obj_comp_map_disj h1 h2 = obj_comp_map_disj h2 h1"
  by (fastforce simp: obj_comp_map_disj_def split: option.splits)

lemma ocm_add_empty [simp]:
  "obj_comp_map_add x empty = x"
  by (rule ext, fastforce simp: obj_comp_map_add_def split: option.splits)

lemma dom_ocm_map_add [simp]:
  "dom (obj_comp_map_add kh1 kh2) = dom kh1 \<union> dom kh2"
  by (auto simp: obj_comp_map_add_def dom_def split: option.split)

lemma ocm_a_base_type_eq:
  "\<lbrakk> obj_comp_map_disj kh1 kh2 ; x \<in> dom kh1 ; x \<in> dom kh2 \<rbrakk>
   \<Longrightarrow> a_base_type (fst (the (kh1 x))) = a_base_type (fst (the (kh2 x)))"
  by (clarsimp simp: obj_comp_map_disj_def split: option.splits)

lemma ocm_add_commute:
  "obj_comp_map_disj h1 h2
   \<Longrightarrow> obj_comp_map_add h1 h2 = obj_comp_map_add h2 h1"
  by (fastforce simp: obj_comp_map_add_def obj_comp_map_disj_def
               elim: ko_combine_commute split: option.splits
               intro!: ext)

lemma ocm_add_assoc:
  "\<lbrakk> obj_comp_map_disj x y ; obj_comp_map_disj y z ; obj_comp_map_disj x z \<rbrakk>
   \<Longrightarrow> obj_comp_map_add (obj_comp_map_add x y) z
      = obj_comp_map_add x (obj_comp_map_add y z)"
  by (rule ext)
     (fastforce simp: obj_comp_map_add_def obj_comp_map_disj_def
                     ko_combine_assoc
               split: option.splits)

lemma ocm_disj_add:
  "obj_comp_map_disj y z
   \<Longrightarrow> (obj_comp_map_disj x (obj_comp_map_add y z))
      = (obj_comp_map_disj x y \<and> obj_comp_map_disj x z)"
  apply (rule iffI)
   apply (simp add: obj_comp_map_disj_def obj_comp_map_add_def)
   apply (rule conjI)
    apply (rule allI)
    apply (erule_tac x=p in allE)+
    apply (clarsimp simp: ko_combine_def split: option.splits)
    apply (clarsimp dest!: check_components_Int_emptyD
                    simp: check_components_id)[1]
    apply blast
   apply (rule allI)
   apply (erule_tac x=p in allE)+
   apply (clarsimp simp: ko_combine_def split: option.splits)
   apply (clarsimp dest!: check_components_Int_emptyD
                   simp: check_components_id)
   apply blast
  apply (clarsimp simp: obj_comp_map_disj_def obj_comp_map_add_def)
  apply (erule_tac x=p in allE)+
  apply (case_tac "p \<in> dom z")
   apply (clarsimp simp: dom_def ko_combine_def split: option.splits)
   apply (rename_tac p objz cz objx cx objy cy)
   apply (clarsimp dest!: check_components_Int_emptyD
                   simp: check_components_id)
   apply (auto simp: check_components_id bounded_ko_clean_ko_override
               split: option.splits)
  done

lemma ocm_has_cap_disj_add:
  "\<lbrakk> ocm_has_cap x p ko cmps i c ; obj_comp_map_disj x y \<rbrakk>
   \<Longrightarrow> \<exists>ko' cmps'. ocm_has_cap (obj_comp_map_add x y) p ko' cmps' i c"
  apply (clarsimp simp: ocm_has_cap_def obj_comp_map_add_def
                        obj_comp_map_disj_def
                  split: option.splits)
  apply (clarsimp simp: ko_combine_def ko_has_cap_def)
  apply (erule_tac x=p in allE)
  apply (clarsimp dest!: check_components_Int_emptyD
                  simp: cap_of_ko_clean_contained_cap)
  apply (subst cap_of_ko_override_left)
    apply auto
  done


subsection \<open>Instantiation to a Separation Algebra.\<close>

lemma kheap_dom_alt_def:
  "kheap_dom kh \<equiv> \<Union> ((\<lambda>p . set (len_seq p
                                  (2 ^ t_obj_bits (fst (the (kh p))))))
                     ` dom kh)"
  by (rule eq_reflection)
     (auto simp: kheap_dom_def kheap_shadows_def kheap_shadow_def
                 len_seq_Cons)

lemma kheap_shadows_dom_empty [simp]:
  "kheap_shadows empty = {}"
  by (simp add: kheap_shadows_def)

lemma kheap_dom_empty [simp]:
  "kheap_dom empty = {}"
  by (simp add: kheap_dom_def)

lemma sep_state_eq_piecewiseI:
  "\<lbrakk> sep_state_ocm x = sep_state_ocm y ;
     sep_state_free x = sep_state_free y ;
     sep_state_avail x = sep_state_avail y \<rbrakk>
   \<Longrightarrow> x = y"
  by (cases x, cases y)
     (clarsimp simp: sep_state_accessors)

lemma sep_disj_zero:
  "sep_disj x sep_empty"
  by (simp add: sep_disj_def sep_empty_def split: sep_state.splits)

lemma sep_disj_commute:
  "sep_disj x y \<Longrightarrow> sep_disj y x"
  by (cases x, cases y, simp add: sep_disj_def Int_commute ocm_disj_commute)

lemma sep_add_zero:
  "sep_add x sep_empty = x"
  by (cases x, simp add: sep_empty_def sep_add_def)

lemma sep_add_commute:
  "sep_disj x y \<Longrightarrow> sep_add x y = sep_add y x"
  by (fastforce simp: sep_add_def sep_disj_def split: sep_state.splits
               elim: ocm_add_commute)

lemma sep_add_assoc:
  "\<lbrakk> sep_disj x y ; sep_disj y z ; sep_disj x z \<rbrakk>
   \<Longrightarrow> sep_add (sep_add x y) z = sep_add x (sep_add y z)"
  by (auto simp: sep_add_def sep_disj_def ocm_add_assoc
           split: sep_state.splits)

lemma ocm_shadow_eq_both:
  "\<lbrakk> x \<in> dom kh ; x \<in> dom kh' ;
     a_base_type (fst (the (kh x))) = a_base_type (fst (the (kh' x))) \<rbrakk>
   \<Longrightarrow> kheap_shadow kh x = kheap_shadow kh' x"
  by (clarsimp simp: kheap_shadow_def)

lemma kheap_shadow_unchanged:
"\<lbrakk> obj_comp_map_disj kh1 kh2 ; kh1 x \<noteq> None \<rbrakk>
 \<Longrightarrow> kheap_shadow (obj_comp_map_add kh1 kh2) x = kheap_shadow kh1 x"
  unfolding obj_comp_map_add_def
  apply (case_tac "x \<in> dom kh2")
   apply (rule ocm_shadow_eq_both, clarsimp+)
   apply (fastforce dest!: ocm_a_base_type_eq simp: ko_combine_def dom_def)
  apply (rule ocm_shadow_eq_both, auto split: option.splits)
  done

lemma kheap_shadows_ocm_add:
  "obj_comp_map_disj kh1 kh2
   \<Longrightarrow> kheap_shadows (obj_comp_map_add kh1 kh2)
      = (kheap_shadows kh1 \<union> kheap_shadows kh2)"
  apply (clarsimp simp: kheap_shadows_def)
  apply (rule set_eqI)
  apply clarsimp
  apply (rule iffI)
   apply (erule disjE)
    apply (fastforce simp: kheap_shadow_unchanged)
   apply (subst (asm) ocm_add_commute, assumption)
   apply (fastforce simp: kheap_shadow_unchanged ocm_disj_commute)
  apply (erule disjE)
   apply clarsimp
   apply (rule_tac x=xa in bexI)
    apply (simp add: kheap_shadow_unchanged)
   apply clarsimp
  apply (subst disj_commute)
  apply clarsimp
  apply (subst ocm_add_commute, assumption)
  apply (subst (asm) ocm_disj_commute)
  apply (rule_tac x=xa in bexI)
   apply (simp add: kheap_shadow_unchanged)
  apply clarsimp
  done (* yuck. *)

lemma kheap_dom_ocm_add:
  "obj_comp_map_disj kh1 kh2
   \<Longrightarrow> kheap_dom (obj_comp_map_add kh1 kh2) = (kheap_dom kh1 \<union> kheap_dom kh2)"
  by (simp add: kheap_dom_def kheap_shadows_ocm_add Un_ac)

text \<open>
  I use these to hand-hold tools through the next proof; automated tactics
  just choke.
\<close>

lemma empty_Inter_UnD:
  "A \<inter> (B \<union> C) = {} \<Longrightarrow> A \<inter> B = {} \<and> A \<inter> C = {}"
  by blast

lemma empty_Inter_UnD_left:
  "(B \<union> C) \<inter> A = {} \<Longrightarrow> B \<inter> A = {} \<and> C \<inter> A = {}"
  by blast

lemma empty_Inter_UnI:
  "\<lbrakk> A \<inter> B = {} ; A \<inter> C = {} \<rbrakk> \<Longrightarrow> A \<inter> (B \<union> C) = {}"
  by blast

lemma empty_Inter_UnI_left:
  "\<lbrakk> A \<inter> C = {} ; B \<inter> C = {} \<rbrakk> \<Longrightarrow> (A \<union> B) \<inter> C = {}"
  by blast

lemma sep_disj_add:
  "sep_disj y z \<Longrightarrow> sep_disj x (sep_add y z) = (sep_disj x y \<and> sep_disj x z)"
  unfolding sep_add_def sep_disj_def
  apply (clarsimp simp: kheap_dom_ocm_add kheap_shadows_ocm_add ocm_disj_add
                  split: sep_state.splits)
  apply (rule iffI)
   apply (clarsimp dest!: empty_Inter_UnD empty_Inter_UnD_left)
   apply ((rule conjI | intro empty_Inter_UnI empty_Inter_UnI_left
           | simp add: Int_commute)+)[1]
   \<comment> \<open>concludes first branch of iffI\<close>
  apply (clarsimp dest!: empty_Inter_UnD empty_Inter_UnD_left)
  apply ((rule conjI | intro empty_Inter_UnI empty_Inter_UnI_left
          | simp add: Int_commute)+)[1]
  done

instantiation sep_state :: stronger_sep_algebra
begin

definition
  "(+) \<equiv> sep_add"
definition
  "sep_disj_sep_state \<equiv> sep_disj"
definition
  "0 = sep_empty"

instance
  apply default
       apply (unfold plus_sep_state_def sep_disj_sep_state_def
                     zero_sep_state_def)
       apply (blast intro: sep_disj_zero sep_disj_commute sep_add_zero
                           sep_add_commute)+
   apply (blast intro!: sep_add_assoc sep_disj_add)+
  done

end

lemmas sep_disj_defs = sep_disj_sep_state_def sep_disj_def
lemmas sep_add_defs = plus_sep_state_def sep_add_def
lemmas sep_empty_defs = zero_sep_state_def sep_empty_def

lemma sep_state_free_plus [simp]:
  "sep_state_free (x + y) = sep_state_free x \<union> sep_state_free y"
  by (clarsimp simp: sep_state_accessors sep_add_defs split: sep_state.splits)

lemma sep_state_avail_plus [simp]:
  "sep_state_avail (x + y) = sep_state_avail x \<union> sep_state_avail y"
  by (clarsimp simp: sep_state_accessors sep_add_defs split: sep_state.splits)

lemma sep_disj_ocmD:
  "x ## y \<Longrightarrow> obj_comp_map_disj (sep_state_ocm x) (sep_state_ocm y)"
  by (clarsimp simp: sep_disj_defs sep_state_ocm_def split: sep_state.splits)


subsection \<open>Properties of maps-to predicates\<close>

subsubsection \<open>Properties of @{term sep_map_base}\<close>

lemma sep_map_baseI:
  "\<lbrakk> sep_state_ocm s p = Some (ko_clean ko cmps, cmps) ;
     sane_components (ko_clean ko cmps) cmps ;
     dom (sep_state_ocm s) = {p} ;
     is_aligned p (t_obj_bits ko) ;
     sep_state_free s = {} ;
     sep_state_avail s = {} \<rbrakk>
   \<Longrightarrow> sep_map_base p ko cmps s"
  by (clarsimp simp: sep_map_base_def sep_state_accessors
               split: sep_state.splits)

lemma sep_map_baseD:
  "sep_map_base p ko cmps s
   \<Longrightarrow> sep_state_ocm s p = Some (ko_clean ko cmps, cmps) \<and>
     sane_components (ko_clean ko cmps) cmps \<and>
     dom (sep_state_ocm s) = {p} \<and>
     is_aligned p (t_obj_bits ko) \<and>
     sep_state_free s = {} \<and>
     sep_state_avail s = {}"
  by (fastforce simp: sep_map_base_def sep_state_accessors
               split: sep_state.splits)

lemma (* sanity check *)
  "sep_map_base p ko cmps s \<Longrightarrow> sep_map_base p ko cmps s"
  apply (drule sep_map_baseD, clarsimp)
  apply (rule sep_map_baseI)
  apply auto
  done

lemma sep_map_base_consequences:
  "(sep_map_base p ko cmps \<and>* P) s
   \<Longrightarrow> \<exists>ko' cmps'.
       sane_components (ko_clean ko cmps) cmps \<and>
       sep_state_ocm s p = Some (ko', cmps') \<and>
       cmps \<subseteq> cmps' \<and>
       cmps \<noteq> {} \<and>
       ko_clean ko' cmps' = ko' \<and>
       ko_clean ko' cmps = ko_clean ko cmps \<and>
       a_base_type ko' = a_base_type ko \<and>
       p \<in> dom (sep_state_ocm s) \<and>
       is_aligned p (t_obj_bits ko)"
  apply (clarsimp dest!: sep_conjD
                  simp: sep_disj_defs sep_add_defs sep_state_accessors
                  split: sep_state.splits)
  apply (drule sep_map_baseD)
  apply (clarsimp simp: sep_state_accessors)
  apply (clarsimp simp: obj_comp_map_add_def obj_comp_map_disj_def
                  split: option.splits)
  apply (erule_tac x=p in allE)
  apply (rule conjI, clarsimp simp: sane_components_def)
  apply (clarsimp simp: ko_combine_def)
  apply (drule check_components_Int_emptyD)
  apply clarsimp
  apply (clarsimp simp: ko_clean_twice_subset Int_commute
                        ko_clean_ko_override_id)
  done

lemma sep_map_base_dom:
  "sep_map_base p ko cmps s \<Longrightarrow> dom (sep_state_ocm s) = {p}"
  by (drule sep_map_baseD, simp)

lemma sep_map_base_aligned:
  "sep_map_base p ko cmps s \<Longrightarrow> is_aligned p (t_obj_bits ko)"
  by (drule sep_map_baseD, simp)

lemma sep_map_base_in_dom:
  "sep_map_base p ko cmps s \<Longrightarrow> p \<in> dom (sep_state_ocm s)"
  by (simp add: sep_map_base_dom)

lemma sep_map_base_set_ko_cap_id:
  "cmp_of ko i \<notin> cmps
   \<Longrightarrow> sep_map_base p (set_ko_cap ko i cap) cmps = sep_map_base p ko cmps"
  by (fastforce intro!: ext simp: sep_map_base_def ko_clean_set_ko_cap_id
                cong: sep_state.case_cong)

lemma sep_map_base_lock_type':
  "(sep_map_base p ko cmps \<and>* P) s
   \<Longrightarrow> \<forall>ko'. sep_state_ocm s p = Some (ko', cmps')
            \<longrightarrow> a_base_type ko' = a_base_type ko"
  apply (clarsimp dest!: sep_conjD simp: sep_disj_defs obj_comp_map_disj_def
                         sep_add_defs obj_comp_map_add_def sep_state_accessors
                  split: sep_state.splits)
  apply (erule_tac x=p in allE)
  apply (clarsimp dest!: sep_map_baseD split: option.splits
                  simp: sep_state_accessors ko_combine_def)
  done

lemma sep_map_base_implode_eq:
  "\<lbrakk> a_base_type ko1 = a_base_type ko2 ;
     cmps1 \<inter> cmps2 = {} ; cmps1 \<noteq> {} ; cmps2 \<noteq> {} \<rbrakk>
   \<Longrightarrow> (sep_map_base p ko1 cmps1 \<and>* sep_map_base p ko2 cmps2)
       = sep_map_base p (ko_override ko1 ko2 cmps2) (cmps1 \<union> cmps2)"
  apply (rule ext, rename_tac s)
  apply (rule iffI)
   apply (clarsimp simp: sep_add_defs sep_disj_defs sep_state_accessors
                         sep_map_base_def
                   dest!: sep_conjD sep_map_baseD split: sep_state.splits)
   apply (simp add: obj_comp_map_add_def ko_combine_def
                    sane_components_ko_clean_ko_override)
  apply (clarsimp dest!: sep_map_baseD)
  apply (rule_tac x="SepState [p \<mapsto> (ko_clean ko1 cmps1, cmps1)] {} {}"
              and y="SepState [p \<mapsto> (ko_clean ko2 cmps2, cmps2)] {} {}"
              in sep_conjI)
     apply (fastforce simp: sep_map_base_def
                     dest!: sane_components_ko_clean_ko_overrideD)
    apply (fastforce simp: sep_map_base_def
                    dest!: sane_components_ko_clean_ko_overrideD)
   apply (drule (4) sane_components_ko_clean_ko_overrideD)
     \<comment> \<open>why can't clarsimp apply this with dest!: ?\<close>
   apply (clarsimp simp: sep_disj_defs kheap_shadows_def kheap_shadow_def
                         obj_comp_map_disj_def check_components_def
                         sane_components_def)

   apply (drule bounded_ko_t_obj_bits)+
   apply simp
   apply (drule_tac a="2::nat" in power_strict_increasing, simp)
   apply (drule_tac n="Suc 0" in less_imp_diff_less)
   apply (simp only: word_bits_def)
   apply (blast dest: len_seq_no_wrap)

  apply (clarsimp simp: sep_add_defs sep_state_accessors obj_comp_map_add_def
                        ko_combine_def
                  split: sep_state.splits)
  apply (rule ext)
  apply (auto simp: ko_combine_def split: option.splits)
  done

lemma sep_map_base_subset_explode_eq:
  "\<lbrakk> cmps' \<subseteq> cmps; cmps' \<noteq> {} \<rbrakk>
   \<Longrightarrow> sep_map_base p ko cmps
      = (sep_map_base p ko cmps' \<and>*
         (if cmps = cmps' then \<box> else sep_map_base p ko (cmps - cmps')))"
  apply (simp split: if_split_asm, intro impI)
  apply (subst sep_map_base_implode_eq, fastforce+)
  apply (simp add: subset_union)
  done

lemma sep_map_base_same_types:
  "\<lbrakk> (sep_map_base p ko cmps \<and>* P) s ;
     (sep_map_base p ko cmps \<and>* P) s \<Longrightarrow> (sep_map_base p ko' cmps' \<and>* Q) s \<rbrakk>
   \<Longrightarrow> a_base_type ko = a_base_type ko'"
  by (clarsimp dest!: sep_map_base_consequences)

lemma sep_map_base_set_ko_cap_implode:
  "\<lbrakk> (sep_map_base p ko cmps \<and>*
      sep_map_base p (set_ko_cap ko' i cap) {cmp_of ko' i}) s ;
     cmp_of ko i \<notin> cmps ; valid_cnode_index ko' i \<rbrakk>
   \<Longrightarrow> sep_map_base p (set_ko_cap ko i cap) (cmps \<union> {cmp_of ko i}) s"
  apply (subgoal_tac "a_base_type ko = a_base_type ko'")
   prefer 2
   apply (drule_tac sep_map_base_same_types)
    apply (sep_select_asm 2)
    apply sep_cancel
    apply simp
  apply (subgoal_tac "cmps \<noteq> {}")
   prefer 2
   apply (frule sep_map_base_consequences, clarsimp)
  apply (clarsimp simp: sep_map_base_implode_eq ko_override_with_set_ko_cap)
  done


subsubsection \<open>Properties of @{term sep_map_cap}\<close>

lemma sep_map_base_sep_map_capI:
  "\<lbrakk> sep_map_base p ko {cmp} s ; cmp = cmp_of ko i ; cap_of ko i = Some cap \<rbrakk>
   \<Longrightarrow> sep_map_cap (a_base_type ko) (p,i) cap s"
  by (fastforce simp: sep_map_cap_def)

lemma sep_map_base_sep_map_capI':
  "\<lbrakk> (sep_map_base p ko {cmp} \<and>* P) s ; cmp = cmp_of ko i ;
     cap_of ko i = Some cap \<rbrakk>
   \<Longrightarrow> (sep_map_cap (a_base_type ko) (p,i) cap \<and>* P) s"
  by (sep_cancel add: sep_map_base_sep_map_capI) simp

lemma sep_map_capI:
  "\<lbrakk> sep_state_ocm s p = Some (ko_clean ko {cmp_of ko i}, {cmp_of ko i}) ;
     a_base_type ko = atyp ;
     cap_of (ko_clean ko {cmp_of ko i}) i = Some cap ;
     sane_components (ko_clean ko {cmp_of ko i}) {cmp_of ko i};
     dom (sep_state_ocm s) = {p} ;
     is_aligned p (t_obj_bits ko) ;
     sep_state_free s = {} ;
     sep_state_avail s = {} \<rbrakk>
   \<Longrightarrow> sep_map_cap atyp (p,i) cap s"
  unfolding sep_map_cap_def
  by (fastforce intro!: sep_map_baseI
               simp: sane_components_def bounded_ko_clean)

lemma sep_map_capD:
  "sep_map_cap atyp (p,i) cap s
   \<Longrightarrow> \<exists>ko. sep_state_ocm s p = Some (ko, {cmp_of ko i}) \<and>
     ko_clean ko {cmp_of ko i} = ko \<and>
     a_base_type ko = atyp \<and>
     cap_of ko i = Some cap \<and>
     sane_components ko {cmp_of ko i} \<and>
     dom (sep_state_ocm s) = {p} \<and>
     is_aligned p (t_obj_bits ko) \<and>
     sep_state_free s = {} \<and>
     sep_state_avail s = {}"
  unfolding sep_map_cap_def
  by (clarsimp dest!: sep_map_baseD simp: sane_components_def)

lemma (* sanity check *)
  "sep_map_cap atyp (p, i) cap s \<Longrightarrow> sep_map_cap atyp (p, i) cap s"
  apply (drule sep_map_capD, clarsimp)
  apply (rule sep_map_capI)
  apply auto
  done

lemma sep_map_cap_ocm_has_capI:
  "sep_map_cap atyp (p,i) cap s
   \<Longrightarrow> \<exists>ko cmps. ocm_has_cap (sep_state_ocm s) p ko cmps i cap"
  by (fastforce dest: sep_map_capD simp: ocm_has_cap_def ko_has_cap_def)

lemma sep_map_cap'_ocm_has_capI:
  "(sep_map_cap atyp (p,i) cap \<and>* P) s
   \<Longrightarrow> \<exists>ko cmps. ocm_has_cap (sep_state_ocm s) p ko cmps i cap"
  by (fastforce dest!: sep_conjD dest: sep_map_cap_ocm_has_capI
               elim: ocm_has_cap_disj_add split: sep_state.splits
               simp: sep_disj_defs sep_add_defs sep_state_accessors)

lemma sep_map_cap_abt_valid_cnode_index:
  "sep_map_cap atyp (p, i) cap s \<Longrightarrow> abt_valid_cnode_index atyp i"
  by (drule sep_map_capD, clarsimp)
     (clarsimp simp: abt_valid_cnode_index_def sane_components_def
                     a_base_type_def a_base_type_cmp_of_def
                     bounded_ko_def cap_of_def tcb_cnode_map_def
               split: kernel_object.splits)

lemma sep_map_cap_abt_valid_cnode_index':
  "(sep_map_cap atyp (p, i) cap \<and>* P) s \<Longrightarrow> abt_valid_cnode_index atyp i"
  by (clarsimp dest!: sep_conjD simp: sep_map_cap_abt_valid_cnode_index)

lemma sep_map_cap_sep_map_base:
  "\<lbrakk> sep_map_cap atyp (p,i) cap s ; a_base_type ko = atyp \<rbrakk>
   \<Longrightarrow> sep_map_base p (set_ko_cap ko i cap) {cmp_of ko i} s"
  apply (frule sep_map_cap_abt_valid_cnode_index)
  apply (drule sep_map_capD, clarsimp)
  apply (clarsimp simp: sep_map_base_def sep_state_accessors
                  split: sep_state.splits)
  apply (subst ko_clean_one_cap_eq[symmetric])
      apply (simp add: valid_cnode_index_cap_of_set_ko_cap)+
  apply (subst ko_clean_one_cap_eq[symmetric])
      apply (simp add: valid_cnode_index_cap_of_set_ko_cap)+
  done

lemma sep_map_cap_sep_map_base': (* XXX: sep_drule doesn't work with this *)
  "\<lbrakk> (sep_map_cap atyp (p,i) cap \<and>* P) s ; a_base_type ko = atyp \<rbrakk>
   \<Longrightarrow> (sep_map_base p (set_ko_cap ko i cap) {cmp_of ko i} \<and>* P) s"
  by (sep_cancel add: sep_map_cap_sep_map_base)+

lemma sep_map_base_sep_map_cap_implode:
  "\<lbrakk> (sep_map_base p ko cmps \<and>* sep_map_cap atyp (p,i) cap) s ;
     cmp_of ko i \<notin> cmps \<rbrakk>
   \<Longrightarrow> sep_map_base p (set_ko_cap ko i cap) (cmps \<union> {cmp_of ko i}) s"
  apply (sep_frule sep_map_cap_abt_valid_cnode_index')
  apply (subgoal_tac "a_base_type ko = atyp")
   apply (drule (1) sep_map_cap_sep_map_base'[where ko=ko])
   apply (sep_select_asm 2)
   apply (erule (1) sep_map_base_set_ko_cap_implode, simp)
  apply (clarsimp simp: sep_map_cap_def sep_conj_exists)
  apply (sep_select_asm 2)
  apply (erule sep_map_base_same_types)
  apply sep_cancel
  done
  (* FIXME: these rules use cmps \<union> {cmp_of ko i}, but that gets simplified
            to insert {cmp_of ko i} cmps, so rules might not match *)

lemma sep_map_base_sep_map_cap_implode':
  "\<lbrakk> (sep_map_base p ko cmps \<and>* sep_map_cap atyp (p,i) cap \<and>* P) s ;
     cmp_of ko i \<notin> cmps \<rbrakk>
   \<Longrightarrow> (sep_map_base p (set_ko_cap ko i cap) (cmps \<union> {cmp_of ko i}) \<and>* P) s"
  by (sep_cancel add: sep_map_base_sep_map_cap_implode)+

lemma sep_map_base_set_ko_cap_sep_map_cap_explode:
  "\<lbrakk> sep_map_base p (set_ko_cap ko i cap) (cmps \<union> {cmp_of ko i}) s ;
     cmp_of ko i \<notin> cmps ; cmps \<noteq> {} ; valid_cnode_index ko i \<rbrakk>
   \<Longrightarrow> (sep_map_base p ko cmps \<and>* sep_map_cap (a_base_type ko) (p,i) cap) s"
  apply (subst (asm) sep_map_base_subset_explode_eq[where cmps'="cmps"])
    apply fastforce
   apply assumption
  apply (simp split: if_split_asm)
   apply fastforce
  apply (simp add: sep_map_base_set_ko_cap_id insert_subtract_new)
  apply sep_cancel
  apply (fastforce dest!: sep_map_base_sep_map_capI
                   intro: valid_cnode_index_cap_of_set_ko_cap
                   split: if_split_asm)
  done


subsection \<open>Cap-level Updates of the Kernel Init State\<close>

lemma sep_map_cap_update_cap:
  "(sep_map_cap atyp p old_cap) s \<Longrightarrow> (sep_map_cap atyp p cap) (sep_update_cap p cap s)"
  apply (cases p)
  apply (clarsimp dest!: sep_map_capD split: sep_state.splits
                  simp: sep_update_cap_def sep_state_accessors
                        sane_components_def)
  apply (rule_tac ko="set_ko_cap ko b cap" in sep_map_capI)
      apply (auto simp: sep_state_accessors sane_components_def
                        ko_clean_set_ko_cap
                  intro: bounded_ko_clean_set_ko_cap bounded_set_ko_cap)
 done

lemma kheap_shadow_upd:
  "\<lbrakk> kh p = Some (ko',cmps') ; a_base_type ko' = a_base_type ko \<rbrakk>
   \<Longrightarrow> kheap_shadow (kh(p \<mapsto> (ko,cmps))) = kheap_shadow kh"
  by (rule ext, auto intro: ocm_shadow_eq_both simp: kheap_shadow_def)

lemma kheap_dom_upd:
  "\<lbrakk> kh p = Some (ko', cmps') ; a_base_type ko' = a_base_type ko \<rbrakk>
   \<Longrightarrow> kheap_dom (kh(p \<mapsto> (ko, cmps))) = kheap_dom kh"
  by (clarsimp simp: kheap_dom_def kheap_shadows_def)
     (fastforce simp only: kheap_shadow_upd)

lemma obj_comp_map_disj_set_ko_cap:
  "\<lbrakk> obj_comp_map_disj x y ; ocm_has_cap x p ko cmps i c \<rbrakk>
   \<Longrightarrow> obj_comp_map_disj (x(p \<mapsto> (set_ko_cap ko i cap, cmps))) y"
  apply (clarsimp simp: obj_comp_map_disj_def split_def ocm_has_cap_def
                     ko_has_cap_def
               dest: cap_of_ko_cleanD split: option.splits)
  apply (erule_tac x=p in allE, clarsimp)
  apply (clarsimp dest!: check_components_Int_emptyD cap_of_ko_cleanD)
  apply (subst check_components_id,
         simp_all add: bounded_ko_clean_set_ko_cap check_components_id)
  apply (subst bounded_ko_clean_set_ko_cap)
   apply simp_all
  apply (drule cap_of_ko_cleanD)
   apply simp
  apply simp
  done (* yuck *)

lemma sep_update_cap_disj:
  "\<lbrakk> x ## y ; ocm_has_cap (sep_state_ocm x) p ko cmps i c \<rbrakk>
   \<Longrightarrow> sep_update_cap (p, i) cap x ## y"
  unfolding ocm_has_cap_def ko_has_cap_def
  apply (clarsimp simp: sep_disj_defs sep_state_accessors sep_update_cap_def
                  split: sep_state.splits)
  apply (subst kheap_dom_upd, assumption)
   apply (fastforce dest!: cap_of_ko_cleanD)
  apply (subst obj_comp_map_disj_set_ko_cap, assumption+)
   apply (fastforce simp: ocm_has_cap_def ko_has_cap_def)
  apply (clarsimp simp: kheap_shadows_def)
  apply (subst kheap_shadow_upd, assumption)
   apply simp
  apply (subst kheap_shadow_upd, assumption)
   apply simp
  apply clarsimp
  apply (rule conjI)
   apply blast
  apply blast
  done (* yuck *)

lemma sep_state_free_sep_update_cap [simp]:
  "sep_state_free (sep_update_cap kcmp cap s) = sep_state_free s"
  by (clarsimp simp: sep_update_cap_def sep_state_accessors
               split: sep_state.splits prod.splits)

lemma sep_state_avail_sep_update_cap [simp]:
  "sep_state_avail (sep_update_cap (p,i) cap s) = sep_state_avail s"
  by (clarsimp simp: sep_update_cap_def sep_state_accessors
               split: sep_state.splits prod.splits)

lemma sep_update_cap_disj_add:
  "\<lbrakk> x ## y ; ocm_has_cap (sep_state_ocm x) p ko cmps i c \<rbrakk>
   \<Longrightarrow> sep_update_cap (p,i) cap (x + y) = sep_update_cap (p,i) cap x + y"
  apply (clarsimp intro!: sep_state_eq_piecewiseI
               simp: sep_disj_defs sep_state_ocm_def sep_update_cap_def
                     sep_add_defs obj_comp_map_add_def ocm_has_cap_def
               split: sep_state.splits option.splits)
  apply (rule conjI)
   apply clarsimp
   apply  (fastforce intro!: ext split: option.splits
               dest!: check_components_Int_emptyD
               simp: ko_has_cap_def obj_comp_map_disj_def
                     ko_combine_def ko_override_set_ko_cap)
   apply (clarsimp)
   apply (rule ext)
   apply clarsimp
   apply (clarsimp simp: ko_has_cap_def obj_comp_map_disj_def
                         ko_combine_def ko_override_set_ko_cap)
   apply (erule_tac x=p in allE)
   apply (subst ko_override_set_ko_cap, simp_all)
   apply clarsimp
   apply (drule check_components_Int_emptyD)
   apply clarsimp
   done

lemma sep_map_cap_update_cap':
  assumes sep: "(sep_map_cap atyp p old_cap \<and>* P) s"
  shows "(sep_map_cap atyp p cap \<and>* P) (sep_update_cap p cap s)"
proof -
  from sep obtain s1 s2 where s: "s = s1 + s2" and s_disj: "s1 ## s2"
    and oldmap: "(sep_map_cap atyp p old_cap) s1" and P: "P s2"
    by (blast dest: sep_conjD)

  let ?s1' = "sep_update_cap p cap s1"

  from oldmap have newmap: "sep_map_cap atyp p cap ?s1'"
    by (fastforce intro: sep_map_cap_update_cap)

  moreover have "?s1' ## s2" using s_disj oldmap
    by (cases p, fastforce dest!: sep_map_capD elim: sep_update_cap_disj
                          simp: ocm_has_cap_def ko_has_cap_def)

  moreover have "sep_update_cap p cap s = sep_update_cap p cap s1 + s2"
    using s oldmap s_disj
    by (cases p, fastforce dest!: sep_map_cap_ocm_has_capI
                          simp: sep_update_cap_disj_add)

  ultimately show ?thesis using s_disj by (blast intro: sep_conjI P)
qed


subsection \<open>Properties of Lifting Kernel States into Init\<close>

text \<open>
  This style of lift-reasoning is used for low-level interaction with other
  wp rules and establishing a link between kernel state operations and
  kernel init state predicates.
\<close>

lemma dom_ocm_dom_kheap_kis_lift:
  "dom (sep_state_ocm (kis_lift kis s)) = dom (kheap s)"
  by (fastforce simp: sep_state_ocm_def lift_sep_state_def
               split: option.splits)

lemma sep_state_ocm_ki_components:
  "sep_state_ocm (lift_sep_state kis) p = Some (a,b)
   \<Longrightarrow> ki_components kis p = b"
  by (fastforce simp: sep_state_ocm_def lift_sep_state_def
               split: option.splits)

lemma sep_map_base_kis_liftD:
  "sep_map_base p ko cmps (kis_lift kis s)
   \<Longrightarrow> \<exists>ko'. kheap s p = Some ko' \<and>
            dom (kheap s) = {p} \<and>
            is_aligned p (t_obj_bits ko) \<and>
            ki_components kis p = cmps \<and>
            ko_clean ko' cmps = ko_clean ko cmps \<and>
            sane_components (ko_clean ko' cmps) cmps \<and>
            ki_free_mem kis = {} \<and>
            ki_available_mem kis = {}"
  by (auto simp: lift_sep_state_def sep_map_base_def split: option.splits)

lemma sep_map_base_kis_liftI:
  "\<lbrakk> kheap s p = Some ko' ; dom (kheap s) = {p} ;
     is_aligned p (t_obj_bits ko) ;
     ki_components kis p = cmps ;
     ko_clean ko' cmps = ko_clean ko cmps ;
     sane_components (ko_clean ko' cmps) cmps ;
     ki_free_mem kis = {} \<and>
     ki_available_mem kis = {} \<rbrakk>
   \<Longrightarrow> sep_map_base p ko cmps (kis_lift kis s)"
  by (fastforce simp: lift_sep_state_def sep_map_base_def)

lemma sep_map_cap_kis_liftD:
  "sep_map_cap atyp (p,i) cap (kis_lift kis s)
   \<Longrightarrow> \<exists>ko. kheap s p = Some ko \<and>
            dom (kheap s) = {p} \<and>
            is_aligned p (t_obj_bits ko) \<and>
            ki_components kis p = {cmp_of ko i} \<and>
            a_base_type ko = atyp \<and>
            cap_of ko i = Some cap \<and>
            sane_components (ko_clean ko {cmp_of ko i}) {cmp_of ko i} \<and>
            ki_free_mem kis = {} \<and>
            ki_available_mem kis = {}"
proof (clarsimp dest!: sep_map_base_kis_liftD simp: sep_map_cap_def)
  fix x ko'
  assume align: "is_aligned p (t_obj_bits x)"
  assume a: "cap_of x i = Some cap"
  assume b: "ko_clean ko' {cmp_of x i} = ko_clean x {cmp_of x i}"

  hence "a_base_type (ko_clean ko' {cmp_of x i})
          = a_base_type (ko_clean x {cmp_of x i})"
    by simp
  hence ts [simp]: "a_base_type ko' = a_base_type x" (is ?t) by simp

  assume c: "sane_components (ko_clean x {cmp_of x i}) {cmp_of x i}"

  have x: "cmp_of x i = cmp_of ko' i" (is ?x) using b by simp
  moreover
  have "cap_of ko' i = Some cap" (is ?y) using a b
    by - (rule_tac cmps="{cmp_of x i}" in cap_of_ko_cleanD, auto)
  moreover
  have "sane_components (ko_clean ko' {cmp_of ko' i}) {cmp_of ko' i}" (is ?z)
    using c
    by (clarsimp simp: sane_components_def b)
  ultimately
  show "is_aligned p (t_obj_bits ko') \<and> ?x \<and> ?t \<and> ?y \<and> ?z" using align
    by auto
qed

lemma sep_map_cap_kis_liftI:
  "\<lbrakk> kheap s p = Some ko ; dom (kheap s) = {p} ;
     is_aligned p (t_obj_bits ko) ;
     ki_components kis p = {cmp_of ko i} ;
     a_base_type ko = atyp \<and>
     cap_of ko i = Some cap ;
     sane_components (ko_clean ko {cmp_of ko i}) {cmp_of ko i} ;
     ki_free_mem kis = {} ;
     ki_available_mem kis = {} \<rbrakk>
   \<Longrightarrow> sep_map_cap atyp (p,i) cap (kis_lift kis s)"
  apply (clarsimp simp: sep_map_cap_def)
  apply (rule_tac x=ko in exI)
  apply (fastforce intro!: sep_map_base_kis_liftI split: option.splits
                   simp: lift_sep_state_def sep_state_accessors)
  done


end
