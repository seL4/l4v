(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Generator_CAMKES_CDL imports
  "../adl-spec/Types_CAMKES"
  "../adl-spec/Library_CAMKES"
  "../../spec/capDL/Syscall_D"
  Types_CAMKES_CDL
  "../../proof/access-control/Dpolicy"
begin

text {*
  This theory is a work in progress on specifying the CapDL-producing logic of the CAmkES code
  generator as an Isabelle function.
*}

text {*
  Merge two CapDL states to form a single one. Note that, in the case of conflicts, the second takes
  precedence.
*}
definition
  merge_cdl :: "cdl_state \<Rightarrow> cdl_state \<Rightarrow> cdl_state"
where
  "merge_cdl a b \<equiv> b\<lparr>
     cdl_objects := cdl_objects b ++ cdl_objects a,
     cdl_cdt := cdl_cdt b ++ cdl_cdt a,
     cdl_asid_table := cdl_asid_table b ++ cdl_asid_table a\<rparr>"

lemma map_add_id[simp]: "x ++ x = x"
  by (metis map_add_le_mapI map_le_antisym map_le_map_add map_le_refl)

lemma map_add_subsume: "dom x \<subseteq> dom y \<Longrightarrow> x ++ y = y"
  by (metis dom_map_add map_le_antisym map_le_def map_le_map_add sup.orderE)

lemma merge_id: "merge_cdl x x = x"
  by (clarsimp simp:merge_cdl_def)

definition merge_objs :: "cdl_state \<Rightarrow> cdl_heap \<Rightarrow> cdl_state"
  where "merge_objs a b \<equiv> merge_cdl a (a\<lparr>cdl_objects := b\<rparr>)"

(* convenience *)
definition sum :: "nat list \<Rightarrow> nat"
  where "sum xs \<equiv> fold (\<lambda>a b. a + b) xs 0"

(* convenience *)
definition enumerate' :: "word32 \<Rightarrow> 'a list \<Rightarrow> (word32 \<times> 'a) list"
  where "enumerate' start xs = map (\<lambda>(a, b). (of_nat a, b)) (enumerate (unat start) xs)"

definition
  lop :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "lop n xs \<equiv> take (length xs - n) xs"

abbreviation behead
  where "behead s pref \<equiv> drop (length pref) s"

abbreviation trunc
  where "trunc s suf \<equiv> lop (length suf) s"

(* Cap rights *)
abbreviation "G \<equiv> {AllowGrant}"
abbreviation "R \<equiv> {AllowRead}"
abbreviation "RG \<equiv> {AllowRead, AllowGrant}"
abbreviation "RW \<equiv> {AllowRead, AllowWrite}"
abbreviation "RWG \<equiv> {AllowRead, AllowWrite, AllowGrant}"
abbreviation "W \<equiv> {AllowWrite}"
abbreviation "WG \<equiv> {AllowWrite, AllowGrant}"

text {*
  A type for representing extra information relating to hardware interrupts that will be appended
  to a generated CapDL specification. We would prefer not to deal with interrupts, but CapDL
  represents each interrupt as a mapping to a single-slot CNode. We need to note the existence of
  these artificial CNodes for the final correspondence proof.
*}
record irqs =
  irqs_map :: "cdl_irq \<Rightarrow> cdl_object_id"
  irqs_objects :: cdl_heap

definition
  valid_irqs :: "cdl_state \<Rightarrow> cdl_heap \<Rightarrow> irqs \<Rightarrow> bool"
where
  "valid_irqs initial extra irqs \<equiv>
     range (irqs_map irqs) = dom (irqs_objects irqs) \<and>
     dom (cdl_objects initial) \<inter> dom (irqs_objects irqs) = {} \<and>
     dom extra \<inter> dom (irqs_objects irqs) = {} \<and>
     (\<forall>x \<in> ran (irqs_objects irqs). case x of
        Types_D.CNode c \<Rightarrow> c = \<lparr>cdl_cnode_caps = empty, cdl_cnode_size_bits = 0\<rparr>
      | _ \<Rightarrow> False)"

text {*
  Predicate that the extra capability distribution we provide to the @{text generate} function is a
  valid extension to the basic distribution we generate. Essentially the extension must only contain
  address space objects.
*}
definition
  valid_extra :: "cdl_state \<Rightarrow> cdl_heap \<Rightarrow> bool"
where
  "valid_extra initial extra \<equiv>
     (\<forall>obj \<in> range extra. case obj of
          None \<Rightarrow> True
        | Some (Types_D.PageDirectory _) \<Rightarrow> True
        | Some (Types_D.PageTable _) \<Rightarrow> True
        | Some (Types_D.Frame _) \<Rightarrow> True
        | _ \<Rightarrow> False) \<and>
     dom (cdl_objects initial) \<inter> dom extra = {}"

text {*
  Now, for each of the types of items present in a base CAmkES-derived CapDL specification (CNodes,
  TCBs, endpoints), we define two things:
   * count - How many of this type of object we have; and
   * objects - A list of these objects ordered by cdl_object_id.
  Note that a CAmkES-derived CapDL specification naturally groups objects of the same type in a
  single, contiguous block. The reason we need to define the count separately to the object list
  itself is that, in some cases, the count of a type of object is required before we are actually at
  the point where we can define the object list itself. This is basically to work around circular
  dependencies.
*}

definition cnode_count :: "camkes_state \<Rightarrow> nat"
  where "cnode_count spec \<equiv> length (components (composition spec))"

definition tcb_count :: "camkes_state \<Rightarrow> nat"
  where "tcb_count spec \<equiv>
    length (components (composition spec)) + sum (map
      (\<lambda>(_, c). length (provides c) + length (requires c) + length (emits c) +
                length (consumes c) + length (dataports c)) (components (composition spec)))"

lemma more_tcbs_than_cnodes: "tcb_count spec \<ge> cnode_count spec"
  by (clarsimp simp:tcb_count_def cnode_count_def)

definition
  ep_objs' :: "camkes_state \<Rightarrow> (string \<times> connection \<times> cdl_object) list"
where
  "ep_objs' spec \<equiv> concat (map (\<lambda>(n, c).
     if conn_type c = seL4RPC then
       [(n @ ''_ep'', c, Types_D.Endpoint)]
     else if conn_type c = seL4Asynch then
       [(n @ ''_ntfn'', c, Types_D.Notification)]
     else
       []) (connections (composition spec)))"

definition ep_objs :: "camkes_state \<Rightarrow> (string \<times> cdl_object) list"
  where "ep_objs spec \<equiv> map (\<lambda>(n, c, e). (n, e)) (ep_objs' spec)"

definition ep_count :: "camkes_state \<Rightarrow> nat"
  where "ep_count spec \<equiv> length (ep_objs spec)"

text {*
  When debugging a system (or when you would like your threads to terminate smoothly), we install
  TCB caps for all a component instance's threads in the first few CNode slots. When producing a
  verified system, we do not install these TCB caps, but we still need to account for the slots
  they would occupy as an offset into the CNode at which the following caps begin. Note, that we
  intentionally leave these slots empty so that any code expecting to invoke a TCB cap causes a cap
  fault, rather than incorrectly invoking an endpoint.
*}
definition cap_offset :: "camkes_state \<Rightarrow> string \<Rightarrow> nat"
  where "cap_offset spec instance \<equiv> 2 +
    (\<lambda>(_, c). length (requires c) + length (provides c) + length (dataports c) +
              length (emits c) + length (consumes c))
      (hd (filter (\<lambda>(n, _). n = instance) (components (composition spec))))"

lemma helper1: "map (length \<circ> (\<lambda>(a, b). P a b # map (f a b) (Q a b))) xs =
                  map (\<lambda>(a, b). 1 + length (Q a b)) xs"
  by clarsimp

lemma helper2: "(\<Sum>x \<leftarrow> xs. Suc (f x)) = length xs + (\<Sum>x \<leftarrow> xs. f x)"
  apply (induct xs)
   by clarsimp+

lemma helper3: "(\<Sum>(a, b) \<leftarrow> xs. Suc (f a b)) = length xs + (\<Sum>(a, b) \<leftarrow> xs. f a b)"
  apply (induct xs)
   by clarsimp+

lemma helper4: "fold op + ((map (\<lambda>(a, b). f a b) xs)::nat list) 0 = (\<Sum>(a, b) \<leftarrow> xs. f a b)"
  apply (subst fold_plus_sum_list_rev)
  apply (subst sum_list_rev)
  by clarsimp

lemma set_of_enumerate:"card (set (enumerate n xs)) = length xs"
  by (metis distinct_card distinct_enumerate length_enumerate)

lemma collapse_fst:"fst ` (\<lambda>x. (f x, g x)) ` s = f ` s"
  by force

lemma collapse_fst2:"fst ` (\<lambda>(x, y). (f x, g y)) ` s = (\<lambda>x. f (fst x)) ` s"
  by force

lemma collapse_fst3:"(\<lambda>x. f (fst x)) ` set (enumerate n xs) = f ` set [n..<n + length xs]"
  by (metis image_image list.set_map map_fst_enumerate)

lemma card_of_dom_bounded:
  fixes f :: "'a \<Rightarrow> 'b option"
  assumes "finite (UNIV::'a set)"
  shows "card (dom f) \<le> CARD('a)"
  by (metis assms card_seteq linear top_greatest)

lemma helper8: "x \<in> f ` S = (\<exists>y \<in> S. f y = x)"
  by blast

lemma helper7:
  "n \<le> CARD(cdl_object_id) \<Longrightarrow> card ((of_nat::nat \<Rightarrow> cdl_object_id) ` {0..<n}) = card {0..<n}"
  apply clarsimp
  apply (induct n)
   apply clarsimp+
  apply (subgoal_tac "{0..<Suc n} = {0..<n} \<union> {n}")
   prefer 2
   apply clarsimp
   apply fastforce
  apply clarsimp
  apply (subst card_insert_disjoint)
    apply clarsimp
   apply (subst atLeast0LessThan)
   apply (subgoal_tac "(of_nat::nat \<Rightarrow> cdl_object_id) ` {..<n} = {..<of_nat n}")
    prefer 2
    apply (rule equalityI)
     apply clarsimp
     apply (subst (asm) card_word)
     apply clarsimp
     apply (rule of_nat_mono_maybe)
      apply clarsimp+
      apply (subst helper8)
      apply (rule bexI) (* sorry for schematics *)
       apply (rule word_unat.Rep_inverse')
       apply force
      apply clarsimp
      apply (subst (asm) card_word)
      apply clarsimp
      apply (metis (erased, hide_lams) Divides.mod_less_eq_dividend order_less_le_trans unat_of_nat word_less_nat_alt)
     by clarsimp+

lemma helper6: "n \<le> CARD(cdl_object_id) \<Longrightarrow> card ((of_nat::nat \<Rightarrow> cdl_object_id) ` {0..<n}) = n"
  apply (subst helper7)
   by clarsimp+

lemma third_in: "(a, b, c) \<in> S \<Longrightarrow> c \<in> (snd \<circ> snd) ` S"
  by (metis (erased, hide_lams) helper8 image_comp snd_conv)

lemma helper9: "(a \<in> (snd \<circ> snd) ` (set (enumerate i xs))) = (a \<in> snd ` (set xs))"
  by (metis map_map map_snd_enumerate set_map)

abbreviation "is_some s \<equiv> \<not> Option.is_none s"

lemma helper11: "is_some (map_of (enumerate' n xs) x) \<Longrightarrow> \<exists>y. map_of (enumerate' n xs) x = Some y"
  by (metis (full_types) is_none_code(1) not_Some_eq)

lemma helper10: "map_of (enumerate' n xs) x = Some y \<Longrightarrow> y \<in> set xs"
  apply (clarsimp simp:enumerate'_def)
  by (metis enumerate_eq_zip in_set_zipE map_of_SomeD zip_map1)

lemma helper14:
  "(map_of xs ++ map_of ys) x = (case map_of ys x of None \<Rightarrow> map_of xs x | Some x' \<Rightarrow> Some x')"
  apply (case_tac "(map_of xs ++ map_of ys) x")
   apply clarsimp+
  apply (case_tac "map_of ys x")
   by clarsimp+

lemma helper15:
  "(map_of xs ++ map_of ys ++ map_of zs) x =
     (case map_of zs x of None \<Rightarrow> (case map_of ys x of None \<Rightarrow> map_of xs x
                                                     | Some x' \<Rightarrow> Some x')
                        | Some x' \<Rightarrow> Some x')"
  apply (case_tac "(map_of xs ++ map_of ys ++ map_of zs) x")
   apply clarsimp+
  apply (case_tac "map_of zs x")
   apply clarsimp
   apply (case_tac "map_of ys x")
    by clarsimp+

lemma helper13: "map_of (map (\<lambda>(n, y). (the_id_of n, y)) xs) x = Some z \<Longrightarrow> z \<in> snd ` set xs"
  proof -
    assume "map_of (map (\<lambda>(n, y). (the_id_of n, y)) xs) x = Some z"
    hence "(x, z) \<in> (\<lambda>(uu, y). (the_id_of uu, y)) ` set xs" using map_of_SomeD by fastforce
    thus "z \<in> snd ` set xs" using helper8 by fastforce
  qed

lemma helper12: "valid_extra a b \<Longrightarrow> dom (cdl_objects a) \<inter> dom b = {}"
  by (clarsimp simp:valid_extra_def)

lemma helper16: "(a, b) \<in> set (enumerate x ys) \<Longrightarrow> b \<in> set ys"
  by (metis enumerate_eq_zip in_set_zip2)

lemma helper17: "distinct (map fst xs) \<Longrightarrow> ran (map_of xs) = set (map snd xs)"
  apply (cut_tac xs="map fst xs" and ys="map snd xs" in ran_map_of_zip[symmetric])
    apply clarsimp+
  by (simp add: ran_distinct)

lemma helper18: "x \<in> ran (map_of xs) \<Longrightarrow> x \<in> set (map snd xs)"
  by (metis (mono_tags, hide_lams) helper8 map_of_SomeD ranE set_map snd_conv)

lemma helper19: "x \<in> ran (xs ++ ys ++ zs) \<Longrightarrow> x \<in> ran xs \<or> x \<in> ran ys \<or> x \<in> ran zs"
  by (smt map_add_Some_iff ranE ranI)

lemma helper21: "None \<notin> S \<Longrightarrow> Some x \<in> S = (x \<in> the ` S)"
  apply (rule iffI)
   apply force
  apply (subst in_these_eq[symmetric])
  apply (clarsimp simp:Option.these_def)
  apply (case_tac "\<exists>y. xa = Some y")
   by clarsimp+

lemma helper20: "the ` Set.filter (\<lambda>s. \<not> Option.is_none s) (range f) = ran f"
  apply (rule subset_antisym)
   apply clarsimp
   apply (case_tac "f x", simp_all)
   apply (simp add: ranI)
  apply clarsimp
  apply (subst helper21[symmetric])
   apply clarsimp+
  apply (erule ranE)
  by (metis range_eqI)

lemma helper23:
  "x \<in> ran (cdl_objects (merge_objs a b)) \<Longrightarrow> x \<in> ran (cdl_objects a) \<or> x \<in> ran b"
  apply (clarsimp simp:merge_objs_def merge_cdl_def)
  by (metis helper19 map_add_id)

type_synonym label = string

text {*
  We assume that the user, when instantiating the following locale to use the contained lemmas, will
  provide us with a function to find the object IDs of the IPC buffers. We need to assume this
  because the IPC buffer frames (and caps to them) are inferred late in the CapDL generation
  process, while deriving the rest of the backing frames for the address space.
*}
locale cdl_translation =
  fixes ipc_buffer :: "string \<Rightarrow> nat \<Rightarrow> cdl_object_id option"
  assumes buffers_distinct: "\<And>n i m j. \<exists>f. ipc_buffer n i = Some f \<and> ipc_buffer m j = Some f
                               \<Longrightarrow> n = m \<and> i = j"
  fixes id_of :: "string \<Rightarrow> cdl_object_id option"
  assumes ids_distinct: "\<And>n m. \<exists>i. id_of n = Some i \<and> id_of m = Some i \<Longrightarrow> n = m"

  fixes garbage :: label
  fixes irq_label :: label
begin

abbreviation the_ipc_buffer :: "string \<Rightarrow> nat \<Rightarrow> cdl_object_id"
  where "the_ipc_buffer name index \<equiv> the (ipc_buffer name index)"

abbreviation the_id_of :: "string \<Rightarrow> cdl_object_id"
  where "the_id_of name \<equiv> the (id_of name)"

abbreviation the_cnode_of :: "string \<Rightarrow> cdl_object_id"
  where "the_cnode_of instance \<equiv> the_id_of (''cnode_'' @ instance)"

(* XXX: Assumes no shared address space components. *)
abbreviation the_pd_of :: "string \<Rightarrow> cdl_object_id"
  where "the_pd_of instance \<equiv> the_id_of (''pd_'' @ instance @ ''_group_bin'')"

text {*
  The contents of a CNode of a given component instance. It is easier to define this out-of-line
  here.
*}
definition
  cap_map :: "camkes_state \<Rightarrow> string \<Rightarrow> nat \<Rightarrow> cdl_cap option"
where
  "cap_map spec instance \<equiv> map_of (enumerate (cap_offset spec instance) (concat (
     map (\<lambda>(n, c, _). if conn_type c = seL4RPC then (
                        if fst (conn_from c) = instance then
                          [Types_D.EndpointCap (the_id_of n) 0 RW]
                        else if fst (conn_to c) = instance then
                          [Types_D.EndpointCap (the_id_of n) 0 RW]
                        else
                          [])
                      else if conn_type c = seL4Asynch then (
                        if fst (conn_from c) = instance then
                          [Types_D.NotificationCap (the_id_of n) 0 W]
                        else if fst (conn_to c) = instance then
                          [Types_D.NotificationCap (the_id_of n) 0 R]
                        else
                          [])
                      else
                        []) (ep_objs' spec))))"

text {*
  Various minutiae related to CNode sizes. Ordinarily, in a hand-written system, this would not be a
  big deal. However, in CAmkES we automatically infer the CNode size based on the number of
  capabilities it needs to contain. The definition below is intended to replicate the calculation in
  the python-capdl module.
*}
definition cnode_size_bits :: "camkes_state \<Rightarrow> string \<Rightarrow> nat"
  where "cnode_size_bits spec name \<equiv>
    LEAST bits. 2 ^ bits > Max (dom (cap_map spec name) \<union> {2})"

definition cnode_size :: "camkes_state \<Rightarrow> string \<Rightarrow> nat"
  where "cnode_size spec instance \<equiv> 2 ^ (cnode_size_bits spec instance)"

definition cnode_guard_size :: "camkes_state \<Rightarrow> string \<Rightarrow> nat"
  where "cnode_guard_size spec instance \<equiv> 32 - cnode_size_bits spec instance"

text {* All CNodes have a guard of 0. *}
definition cnode_guard :: "camkes_state \<Rightarrow> string \<Rightarrow> 32 word"
  where "cnode_guard _ _ \<equiv> 0"

definition
  cnode_objs :: "camkes_state \<Rightarrow> (string \<times> cdl_object) list"
where
  "cnode_objs spec \<equiv>
     map (\<lambda>n. (''cnode_'' @ n,
               Types_D.CNode \<lparr>cdl_cnode_caps = cap_map spec n,
                              cdl_cnode_size_bits = cnode_size_bits spec n\<rparr>))
       (instance_names spec)"

lemma cnode_count_correct: "cnode_count spec = length (cnode_objs spec)"
  by (clarsimp simp:cnode_count_def cnode_objs_def instance_names_def)

definition
  tcb_objs :: "camkes_state \<Rightarrow> (string \<times> cdl_object) list"
where
  "tcb_objs spec \<equiv> concat (
     (* The 'control' TCB *)
     map (\<lambda>(n, c). (n @ ''_tcb_0_control'', Types_D.Tcb \<lparr>cdl_tcb_caps = [
       cspace \<mapsto> Types_D.CNodeCap (the_cnode_of n) (cnode_guard spec n) (cnode_guard_size spec n)
                   (cnode_size_bits spec n),
       vspace \<mapsto> Types_D.PageDirectoryCap (the_pd_of n) Real None,
       ipc_buffer_slot \<mapsto> Types_D.FrameCap False (the_ipc_buffer n 0) RW 12 Real None],
                        cdl_tcb_fault_endpoint = 0,
                        cdl_tcb_intent = undefined,
                        cdl_tcb_has_fault = False,
                        cdl_tcb_domain = 0\<rparr>) #

     (* The interface TCBs *)
     map (\<lambda>(i, inf). (n @ ''_tcb_'' @ inf, Types_D.Tcb \<lparr>cdl_tcb_caps = [
       cspace \<mapsto> Types_D.CNodeCap (the_cnode_of n) (cnode_guard spec n) (cnode_guard_size spec n)
                   (cnode_size_bits spec n),
       vspace \<mapsto> Types_D.PageDirectoryCap (the_pd_of n) Real None,
       ipc_buffer_slot \<mapsto> Types_D.FrameCap False (the_ipc_buffer n (i + 1)) RW 12 Real None],
                   cdl_tcb_fault_endpoint = 0,
                   cdl_tcb_intent = undefined,
                   cdl_tcb_has_fault = False,
                   cdl_tcb_domain = 0\<rparr>))
         (enumerate 0 (map fst (provides c) @ map fst (requires c) @ map fst (emits c) @
                       map fst (consumes c) @ map fst (dataports c))))

     (components (composition spec)))"

lemma tcb_count_correct: "tcb_count spec = length (tcb_objs spec)"
  apply (clarsimp simp:tcb_count_def tcb_objs_def sum_def)
  apply (subst length_concat)
  apply clarsimp
  apply (subst helper1)
  apply clarsimp
  apply (subst helper3)
  apply (subst helper4)
  apply clarsimp
  by (metis (no_types, hide_lams) add.commute add.left_commute)

text {* The CapDL heap; that is, all the objects in the system. *}
definition
  obj_heap :: "camkes_state \<Rightarrow> cdl_object_id \<Rightarrow> cdl_object option"
where
  "obj_heap spec \<equiv> map_of (map (\<lambda>(n, i). (the_id_of n, i)) (
     cnode_objs spec @ tcb_objs spec @ ep_objs spec))"

definition obj_heap_size :: "camkes_state \<Rightarrow> nat"
  where "obj_heap_size spec \<equiv> cnode_count spec + tcb_count spec + ep_count spec"

lemma obj_heap_dom_bounded:"card (dom (obj_heap spec)) \<le> CARD(cdl_object_id)"
  apply (rule card_mono[where B=UNIV])
   by clarsimp+

text {* Low-level generator. This describes the actual logic of the CAmkES code generator. *}
definition
  generate' :: "camkes_state \<Rightarrow> cdl_state"
where
  "generate' spec \<equiv> \<lparr>
     cdl_arch = ARM11,
     cdl_objects = obj_heap spec,
     cdl_cdt = empty,
     cdl_current_thread = undefined,
     cdl_irq_node = undefined,
     cdl_asid_table = empty,
     cdl_current_domain = undefined\<rparr>"

text {*
  An object abstraction (that is, a mapping from object IDs to labels) for a CAmkES-generated
  specification. WIP.
*}
definition
  poa_of :: "camkes_state \<Rightarrow> cdl_heap \<Rightarrow> irqs \<Rightarrow> label agent_map"
where
  "poa_of spec extra irqs \<equiv> (\<lambda>id. case (

     (* Labelling of the output of the low-level generator: *)
     fold (op ++)
       (map (\<lambda>(name, _). [the_id_of name \<mapsto> behead name ''cnode_'']) (cnode_objs spec))
         Map.empty

     ++
     fold (op ++)
       (map (\<lambda>(name, _). [the_id_of name \<mapsto> trunc name ''_ep'']) (ep_objs spec)) Map.empty
     ++
     fold (op ++)
       (map (\<lambda>(name, _). [the_id_of name \<mapsto> behead name ''tcb_'']) (tcb_objs spec)) Map.empty

     (* Labelling of address space objects: *)
     ++
     (\<lambda>id. case extra id of
             Some _ \<Rightarrow> if \<exists>name. id_of name = Some id
                          then Some (trunc
                                      (behead (SOME name. id_of name = Some id) ''frame_'')
                                        ''_group_bin_0000'')
                          else None
           | None \<Rightarrow> None)

     (* Labelling of IRQ objects: *)
     ++
     (\<lambda>id. if id \<in> dom (irqs_objects irqs)
              then Some irq_label
              else None)

     ) id of Some l \<Rightarrow> l | None \<Rightarrow> garbage)"

abbreviation "edge_subject \<equiv> fst"
abbreviation "edge_auth \<equiv> fst o snd"
abbreviation "edge_object \<equiv> snd o snd"

text {*
  A policy describing the authority between labels in a CapDL system. Note that the only meaningful
  relationships here are the authority implied by endpoints. TODO: shared memory.
*}
definition
  policy_of :: "camkes_state \<Rightarrow> cdl_heap \<Rightarrow> irqs \<Rightarrow> label auth_graph"
where
  "policy_of spec extra irqs \<equiv>
     (* Every label has every authority over itself. *)
     {edge. edge_subject edge = edge_object edge} \<union>

     (* Senders on seL4RPC connections. *)
     {edge. \<exists>from. from \<in> fst ` set (components (composition spec)) \<and>
                   (\<exists>conn \<in> set (connections (composition spec)).
                      fst (conn_from (snd conn)) = from \<and>
                      conn_type (snd conn) = seL4RPC \<and>
                      edge_object edge = fst conn) \<and>
                    edge_subject edge = from \<and>
                    edge_auth edge \<in> {Receive, Reset, SyncSend}} \<union>

     (* Receivers on seL4RPC connections. *)
     {edge. \<exists>to. to \<in> fst ` set (components (composition spec)) \<and>
                 (\<exists>conn \<in> set (connections (composition spec)).
                    fst (conn_to (snd conn)) = to \<and>
                    conn_type (snd conn) = seL4RPC \<and>
                    edge_object edge = fst conn) \<and>
                  edge_subject edge = to \<and>
                  edge_auth edge \<in> {Receive, Reset, SyncSend}} \<union>

     (* Senders on seL4Asynch connections. *)
     {edge. \<exists>from. from \<in> fst ` set (components (composition spec)) \<and>
                   (\<exists>conn \<in> set (connections (composition spec)).
                      fst (conn_from (snd conn)) = from \<and>
                      conn_type (snd conn) = seL4Asynch \<and>
                      edge_object edge = fst conn) \<and>
                    edge_subject edge = from \<and>
                    edge_auth edge \<in> {Notify, Reset}} \<union>

     (* Receivers on seL4Asynch connections. *)
     {edge. \<exists>to. to \<in> fst ` set (components (composition spec)) \<and>
                 (\<exists>conn \<in> set (connections (composition spec)).
                    fst (conn_to (snd conn)) = to \<and>
                    conn_type (snd conn) = seL4Asynch \<and>
                    edge_object edge = fst conn) \<and>
                  edge_subject edge = to \<and>
                  edge_auth edge \<in> {Receive, Reset}}"

lemma pw_decompose:
  "\<lbrakk>\<forall>agent. (\<forall>agent'. (agent, Control, agent') \<in> aag \<longrightarrow> agent = agent')
         \<and> (\<forall>a. (agent, a, agent) \<in> aag);
    \<exists>agent. policy_wellformed aag mirqs irqs agent\<rbrakk>
    \<Longrightarrow> \<forall>agent. policy_wellformed aag False irqs agent"
  by (clarsimp simp:policy_wellformed_def)

lemma no_trans_grant: "subj = obj \<or> (subj, Grant, obj) \<notin> policy_of spec extras irqs"
  by (clarsimp simp:policy_of_def)

lemma pw_control:
  "\<lbrakk>policy_wellformed policy mirqs irqs l; (s, Receive, l) \<in> policy\<rbrakk> \<Longrightarrow> (l, Control, s) \<in> policy"
  apply (rule_tac ep=l and mirqs=mirqs and irqs=irqs and l=l in aag_wellformed_grant_Control_to_recv)
    apply (rule_tac mirqs=mirqs and irqs=irqs in aag_wellformed_refl)
    by assumption+

lemma pw_control':
  "\<lbrakk>policy_wellformed policy mirqs irqs l; (s, Receive, l) \<in> policy\<rbrakk> \<Longrightarrow> (s, Control, l) \<in> policy"
  apply (rule_tac ep=l and mirqs=mirqs and irqs=irqs and l=l in aag_wellformed_grant_Control_to_send)
    apply (rule_tac mirqs=mirqs and irqs=irqs in aag_wellformed_refl)
    by assumption+

lemma pw_same_label:
  "\<lbrakk>policy_wellformed policy mirqs irqs l; (s, Receive, l) \<in> policy\<rbrakk> \<Longrightarrow> s = l"
  apply (frule_tac s=s in pw_control, assumption)
  apply (frule_tac s=s in pw_control', assumption)
  apply (rule sym)
  apply (rule_tac aag=policy and mirqs=mirqs and irqs=irqs in aag_wellformed_Control)
   by assumption+

lemma policy_wf: "wellformed_assembly spec \<Longrightarrow>
    \<forall>agent. policy_wellformed (policy_of spec extras irqs) False {irq_label} agent"
  apply (clarsimp simp:policy_wellformed_def)
  apply (rule conjI)
   apply (clarsimp simp:policy_of_def)
  apply (rule conjI)
   apply (clarsimp simp:policy_of_def)
  apply clarsimp
  apply (rename_tac subj subj' obj)
  apply (cut_tac subj=subj and obj=obj and spec=spec and extras=extras and irqs=irqs in no_trans_grant)
  apply clarsimp
  oops

(* TODO *)
definition
  pas_of :: "camkes_state \<Rightarrow> cdl_heap \<Rightarrow> irqs \<Rightarrow> label PAS set"
where
  "pas_of spec extra irqs \<equiv> {pas.
     pasObjectAbs pas = poa_of spec extra irqs \<and>
     (\<forall>asid. pasASIDAbs pas asid = garbage) \<and>
     (\<forall>irq. pasIRQAbs pas irq = irq_label) \<and>
     pasPolicy pas = policy_of spec extra irqs \<and>
     pasSubject pas \<notin> {garbage, irq_label} \<and>
     \<not> pasMayActivate pas \<and>
     \<not> pasMayEditReadyQueues pas \<and>
     \<not> pasMaySendIrqs pas \<and>
     (\<forall>domain. (domain = 0 \<and> pasDomainAbs pas domain \<noteq> garbage) \<or>
               (domain \<noteq> 0 \<and> pasDomainAbs pas domain = garbage))
   }"

text {*
  Top-level state generator. We validate the capability extension and then use the low-level
  generator above.
*}
definition
  state_of :: "camkes_state \<Rightarrow> cdl_heap \<Rightarrow> irqs \<Rightarrow> cdl_state option"
where
  "state_of spec extra irqs \<equiv>
     if valid_extra (generate' spec) extra \<and> valid_irqs (generate' spec) extra irqs then
       Some ((merge_objs
               (merge_objs (generate' spec) extra) (irqs_objects irqs))
                 \<lparr>cdl_irq_node := irqs_map irqs\<rparr>)
     else
       None"

lemma state_of_implies_valid:
  "state_of spec extra irqs = Some cdl \<Longrightarrow> valid_extra (generate' spec) extra"
  by (metis state_of_def option.distinct(1))

lemma state_of_implies_valid2:
  "state_of spec extra irqs = Some cdl \<Longrightarrow> valid_irqs (generate' spec) extra irqs"
  by (metis state_of_def option.distinct(1))

lemma merge_contained:
  "\<lbrakk>z = merge_cdl x y; cdl_objects z u = Some v\<rbrakk>
     \<Longrightarrow> cdl_objects x u = Some v \<or> cdl_objects y u = Some v"
  by (clarsimp simp:merge_cdl_def)

abbreviation "obj_ids cdl \<equiv> dom (cdl_objects cdl)"
abbreviation "obj_ids' extra \<equiv> dom extra"
abbreviation "obj_count cdl \<equiv> card (obj_ids cdl)"
abbreviation "obj_count' extra \<equiv> card (obj_ids' extra)"
abbreviation "objs cdl \<equiv> the ` (Set.filter is_some (range (cdl_objects cdl)))"
abbreviation "objs' extra \<equiv> the ` (Set.filter is_some (range extra))"

lemma valid_only_pds_pts_frames:
  "valid_extra initial cdl \<Longrightarrow> \<forall>i \<in> objs' cdl. case i of Types_D.PageDirectory _ \<Rightarrow> True
                                                       | Types_D.PageTable _ \<Rightarrow> True
                                                       | Types_D.Frame _ \<Rightarrow> True
                                                       | _ \<Rightarrow> False"
  apply (clarsimp simp:valid_extra_def)
  apply (erule_tac x=xa in allE)
  by (metis case_option_If2 Option.is_none_def)

lemma cnode_objs_only_cnodes:
  "\<forall>(_, i) \<in> set (cnode_objs spec). case i of Types_D.CNode _ \<Rightarrow> True | _ \<Rightarrow> False"
  by (clarsimp simp:cnode_objs_def)

lemma tcb_objs_only_tcbs: "\<forall>(_, i) \<in> set (tcb_objs spec). case i of Types_D.Tcb _ \<Rightarrow> True | _ \<Rightarrow> False"
  apply (clarsimp simp:tcb_objs_def)
  apply (erule disjE)
   by clarsimp+

lemma ep_objs_only_eps:
  "\<forall>(_, i) \<in> set (ep_objs spec). case i of Types_D.Endpoint \<Rightarrow> True | Types_D.Notification \<Rightarrow> True | _ \<Rightarrow> False"
  apply (clarsimp simp:ep_objs_def ep_objs'_def)
  by (metis cdl_object.simps(98) cdl_object.simps(99))

lemma generated_no_pds_pts_frames:
  "generate' spec = cdl \<Longrightarrow>
     \<not>(\<exists>x \<in> objs cdl. case x of Types_D.PageDirectory _ \<Rightarrow> True
                               | Types_D.PageTable _ \<Rightarrow> True
                               | Types_D.Frame _ \<Rightarrow> True
                               | _ \<Rightarrow> False)"
  apply (clarsimp simp:generate'_def obj_heap_def)
  apply (subst (asm) helper15)+
  apply (case_tac "map_of (map (\<lambda>(n, y). (the_id_of n, y)) (cnode_objs spec)) xa")
   apply clarsimp
   apply (case_tac "map_of (map (\<lambda>(n, y). (the_id_of n, y)) (tcb_objs spec)) xa")
    apply clarsimp
    apply (case_tac "map_of (map (\<lambda>(n, y). (the_id_of n, y)) (ep_objs spec)) xa")
     apply (clarsimp; fail)
    apply clarsimp
    apply (insert ep_objs_only_eps[where spec=spec], clarsimp)
    apply (drule helper13)
    apply clarsimp
    apply (rename_tac a' b')
    apply (erule_tac x="(a', b')" in ballE)
     apply clarsimp
     apply (case_tac b', simp_all)
   apply (insert tcb_objs_only_tcbs[where spec=spec], clarsimp)
   apply (drule helper13)
   apply clarsimp
   apply (rename_tac a' b')
   apply (erule_tac x="(a', b')" and A="set (tcb_objs spec)" in ballE)
    apply clarsimp
    apply (case_tac b', simp_all)
  apply (insert cnode_objs_only_cnodes[where spec=spec], clarsimp)
  apply (drule helper13)
  apply clarsimp
  apply (rename_tac a' b')
  apply (erule_tac x="(a', b')" and A="set (cnode_objs spec)" in ballE)
   apply clarsimp
   by (case_tac b', simp_all)

lemma generated_objects_disjoint:
  "state_of spec extra irqs = Some cdl \<Longrightarrow>
     obj_count (generate' spec) + obj_count' extra + obj_count' (irqs_objects irqs) = obj_count cdl"
  apply (frule state_of_implies_valid, frule state_of_implies_valid2)
  apply (subst card_Un_disjoint[symmetric], simp_all)
   apply (clarsimp simp:helper12)
  apply (subst card_Un_disjoint[symmetric], simp_all)
   apply (subgoal_tac "dom extra \<inter> dom (irqs_objects irqs) = {}")
    prefer 2
    apply (rule ccontr)
    apply (subst (asm) not_empty_eq)
    apply clarsimp
    apply (rename_tac obj1 obj2)
    apply (clarsimp simp:valid_irqs_def)
    apply blast
   apply (clarsimp simp:valid_irqs_def)
   apply blast
  apply (clarsimp simp:state_of_def merge_cdl_def merge_objs_def)
  by (simp add: Un_assoc)

lemma only_endpoint_caps:
  "\<forall>cap \<in> ran (cap_map a xs). case cap of Types_D.EndpointCap _ _ _ \<Rightarrow> True
                                        | Types_D.NotificationCap _ _ _ \<Rightarrow> True
                                        | _ \<Rightarrow> False"
  apply (clarsimp simp:cap_map_def)
  apply (subst (asm) ran_distinct)
   apply clarsimp+
  apply (drule helper16)
  apply clarsimp
  apply (rename_tac connection irrelevant)
  apply (case_tac "conn_type connection = seL4RPC", simp_all)
   by (case_tac "from_component connection = xs", simp_all)+

lemma valid_only_empty_cnodes:
  "valid_irqs spec extra irqs \<Longrightarrow> \<forall>obj \<in> ran (irqs_objects irqs). case obj of
     Types_D.CNode c \<Rightarrow> c = \<lparr>cdl_cnode_caps = empty, cdl_cnode_size_bits = 0\<rparr>
   | _ \<Rightarrow> False"
  by (clarsimp simp:valid_irqs_def)

lemma only_endpoint_caps2:
  "\<forall>(name, cnode) \<in> set (cnode_objs spec). case cnode of
     Types_D.CNode c \<Rightarrow> (\<forall>cap \<in> ran (cdl_cnode_caps c). case cap of
       Types_D.EndpointCap _ _ _ \<Rightarrow> True
     | Types_D.NotificationCap _ _ _ \<Rightarrow> True
     | _ \<Rightarrow> False)
   | _ \<Rightarrow> False"
  apply (clarsimp simp:cnode_objs_def)
  apply (rename_tac name cap)
  apply (cut_tac a=spec and xs=name in only_endpoint_caps)
  apply (erule_tac x=cap in ballE)
   apply assumption
  by clarsimp

text {* All the caps in a generated spec are only to endpoints. *}
lemma generated_caps_limited:
  "state_of spec extra irqs = Some cdl \<Longrightarrow>
     \<forall>cnode \<in> ((\<lambda>c. case c of Types_D.CNode c' \<Rightarrow> c') `
                 (Set.filter (\<lambda>c. case c of Types_D.CNode _ \<Rightarrow> True | _ \<Rightarrow> False)
                   (Map.ran (cdl_objects cdl)))).
       \<forall>cap \<in> (Map.ran (cdl_cnode_caps cnode)).
         case cap of Types_D.EndpointCap _ _ _ \<Rightarrow> True
                   | Types_D.NotificationCap _ _ _ \<Rightarrow> True
                   | _ \<Rightarrow> False"
  apply (clarsimp simp:state_of_def)
  apply (rename_tac cap)
  apply (subgoal_tac "valid_extra (generate' spec) extra")
   prefer 2
   apply (rule ccontr)
   apply clarsimp+
  apply (subgoal_tac "valid_irqs (generate' spec) extra irqs")
   prefer 2
   apply (rule ccontr)
   apply clarsimp+
  apply (drule helper23)
  apply (erule disjE)
   apply (drule helper23)
   apply (erule disjE)
    apply (clarsimp simp:generate'_def obj_heap_def)
    apply (drule helper19)
    apply (case_tac "cnode \<in> ran (map_of (map (\<lambda>(n, y). (the_id_of n, y)) (ep_objs spec)))")
     apply (drule helper18)
     apply clarsimp
     apply (rename_tac name cnode)
     apply (cut_tac spec=spec in ep_objs_only_eps)
     apply (erule_tac x="(name, cnode)" in ballE)
      apply clarsimp
      apply (case_tac cnode; simp_all)
     apply clarsimp
    apply (case_tac "cnode \<in> ran (map_of (map (\<lambda>(n, y). (the_id_of n, y)) (tcb_objs spec)))")
     apply (drule helper18)
     apply clarsimp
     apply (rename_tac name cnode)
     apply (cut_tac spec=spec in tcb_objs_only_tcbs)
     apply (erule_tac x="(name, cnode)" in ballE)
      apply clarsimp
      apply (case_tac cnode; simp_all)
     apply clarsimp
    apply clarsimp
    apply (drule helper18)
    apply clarsimp
    apply (rename_tac name cnode)
    apply (cut_tac spec=spec in only_endpoint_caps2)
    apply (erule_tac x="(name, cnode)" in ballE)
     apply clarsimp
     apply (case_tac cnode; simp_all)
    apply clarsimp
   apply (drule valid_only_pds_pts_frames)
   apply (erule_tac x=cnode in ballE)
    apply (case_tac cnode; simp_all)
   apply (simp add: helper20)
  apply (drule valid_only_empty_cnodes)
  apply (erule_tac x=cnode in ballE)
   apply (case_tac cnode; simp_all)
  by clarsimp

text {* Compose the functions for producing a state and PAS into a single top-level generator. *}
definition
  generate :: "camkes_state \<Rightarrow> cdl_heap \<Rightarrow> irqs \<Rightarrow> (cdl_state \<times> label PAS set) option"
where
  "generate spec extra irqs \<equiv>
     case state_of spec extra irqs of Some state \<Rightarrow> Some (state, pas_of spec extra irqs)
                                    | None \<Rightarrow> None"

lemma "\<lbrakk>generate spec extra irqs = Some (state, pases); pas \<in> pases;
        (subject, Control, object) \<in> pasPolicy pas\<rbrakk>
         \<Longrightarrow> subject = object"
  apply (clarsimp simp:generate_def pas_of_def policy_of_def)
  apply (case_tac "state_of spec extra irqs"; clarsimp)+
  done

end

end
