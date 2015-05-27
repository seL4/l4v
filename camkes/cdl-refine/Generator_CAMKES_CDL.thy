theory Generator_CAMKES_CDL imports
  "../adl-spec/Types_CAMKES"
  "../adl-spec/Library_CAMKES"
  "../../spec/capDL/Syscall_D"
  Types_CAMKES_CDL
  "../../lib/WordLemmaBucket"
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

text {* Convenience abbreviation for not being in a syscall. *}
definition
  no_intent :: cdl_full_intent
where
  "no_intent \<equiv> \<lparr>
     cdl_intent_op = None,
     cdl_intent_error = False,
     cdl_intent_cap = 0,
     cdl_intent_extras = [],
     cdl_intent_recv_slot = None\<rparr>"

(* convenience *)
definition enumerate' :: "word32 \<Rightarrow> 'a list \<Rightarrow> (word32 \<times> 'a) list"
  where "enumerate' start xs = map (\<lambda>(a, b). (of_nat a, b)) (enumerate (unat start) xs)"

(* Cap rights *)
abbreviation "G \<equiv> {AllowGrant}"
abbreviation "R \<equiv> {AllowRead}"
abbreviation "RG \<equiv> {AllowRead, AllowGrant}"
abbreviation "RW \<equiv> {AllowRead, AllowWrite}"
abbreviation "RWG \<equiv> {AllowRead, AllowWrite, AllowGrant}"
abbreviation "W \<equiv> {AllowWrite}"
abbreviation "WG \<equiv> {AllowWrite, AllowGrant}"

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
        | Some (PageDirectory _) \<Rightarrow> True
        | Some (PageTable _) \<Rightarrow> True
        | Some (Frame _) \<Rightarrow> True
        | _ \<Rightarrow> False) \<and>
     dom (cdl_objects initial) \<inter> dom extra = {}"

text {*
  Various minutiae related to CNode sizes. Ordinarily, in a hand-written system, this would not be a
  big deal. However, in CAmkES we automatically infer the CNode size based on the number of
  capabilities it needs to contain.
*}
definition cnode_size_bits :: "camkes_state \<Rightarrow> string \<Rightarrow> nat"
  where "cnode_size_bits spec name \<equiv> 12" (* TODO *)
definition cnode_size :: "camkes_state \<Rightarrow> string \<Rightarrow> nat"
  where "cnode_size spec instance \<equiv> 2 ^ (cnode_size_bits spec instance)" (* TODO *)

definition cnode_guard_size :: "camkes_state \<Rightarrow> string \<Rightarrow> nat"
  where "cnode_guard_size spec instance \<equiv> 32 - cnode_size_bits spec instance"

text {* All CNodes have a guard of 0. *}
definition cnode_guard :: "camkes_state \<Rightarrow> string \<Rightarrow> 32 word"
  where "cnode_guard _ _ \<equiv> 0"

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
       [(n @ ''_ep'', c, Endpoint)]
     else if conn_type c = seL4Asynch then
       [(n @ ''_aep'', c, AsyncEndpoint)]
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
  where "cap_offset spec instance \<equiv> 1 +
    (\<lambda>(_, c). length (requires c) + length (provides c) + length (dataports c) +
              length (emits c) + length (consumes c))
      (hd (filter (\<lambda>(n, _). n = instance) (components (composition spec))))"

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
                          [EndpointCap (the_id_of n) 0 RWG]
                        else if fst (conn_to c) = instance then
                          [EndpointCap (the_id_of n) 0 R]
                        else
                          [])
                      else if conn_type c = seL4Asynch then (
                        if fst (conn_from c) = instance then
                          [AsyncEndpointCap (the_id_of n) 0 W]
                        else if fst (conn_to c) = instance then
                          [AsyncEndpointCap (the_id_of n) 0 R]
                        else
                          [])
                      else
                        []) (ep_objs' spec))))"

definition
  cnode_objs :: "camkes_state \<Rightarrow> (string \<times> cdl_object) list"
where
  "cnode_objs spec \<equiv>
     map (\<lambda>n. (''cnode_'' @ n,
               CNode \<lparr>cdl_cnode_caps = cap_map spec n,
                      cdl_cnode_size_bits = cnode_size_bits spec n\<rparr>))
       (instance_names spec)"

lemma cnode_count_correct: "cnode_count spec = length (cnode_objs spec)"
  by (clarsimp simp:cnode_count_def cnode_objs_def instance_names_def)

definition
  tcb_objs :: "camkes_state \<Rightarrow> (string \<times> cdl_object) list"
where
  "tcb_objs spec \<equiv> concat (
     (* The 'control' TCB *)
     map (\<lambda>(n, c). (n @ ''_tcb__control'', Tcb \<lparr>cdl_tcb_caps = [
       cspace \<mapsto> CNodeCap (the_cnode_of n) (cnode_guard spec n) (cnode_guard_size spec n)
                   (cnode_size_bits spec n),
       vspace \<mapsto> PageDirectoryCap (the_pd_of n) Real None,
       reply_slot \<mapsto> NullCap,
       caller_slot \<mapsto> NullCap,
       ipc_buffer_slot \<mapsto> FrameCap (the_ipc_buffer n 0) RW 12 Real None,
       fault_ep_slot \<mapsto> NullCap],
                        cdl_tcb_fault_endpoint = 0,
                        cdl_tcb_intent = no_intent,
                        cdl_tcb_has_fault = False,
                        cdl_tcb_domain = 0\<rparr>) # 

     (* The interface TCBs *)
     map (\<lambda>(i, inf). (n @ ''_tcb_'' @ inf, Tcb \<lparr>cdl_tcb_caps = [
       cspace \<mapsto> CNodeCap (the_cnode_of n) (cnode_guard spec n) (cnode_guard_size spec n)
                   (cnode_size_bits spec n),
       vspace \<mapsto> PageDirectoryCap (the_pd_of n) Real None,
       reply_slot \<mapsto> NullCap,
       caller_slot \<mapsto> NullCap,
       ipc_buffer_slot \<mapsto> FrameCap (the_ipc_buffer n (i + 1)) RW 12 Real None,
       fault_ep_slot \<mapsto> NullCap],
                   cdl_tcb_fault_endpoint = 0,
                   cdl_tcb_intent = no_intent,
                   cdl_tcb_has_fault = False,
                   cdl_tcb_domain = 0\<rparr>))
         (enumerate 0 (map fst (provides c) @ map fst (requires c) @ map fst (emits c) @
                       map fst (consumes c) @ map fst (dataports c))))

     (components (composition spec)))"

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
  apply (subst fold_plus_listsum_rev)
  apply (subst listsum_rev)
  by clarsimp

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

lemma obj_heap_dom_bounded:"card (dom (obj_heap spec)) \<le> CARD(cdl_object_id)"
  apply (rule card_mono[where B=UNIV])
   by clarsimp+

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

text {* Low-level generator. This describes the actual logic of the CAmkES code generator. *}
definition
  generate' :: "camkes_state \<Rightarrow> cdl_state"
where
  "generate' spec \<equiv> \<lparr>
     cdl_arch = ARM11,
     cdl_objects = obj_heap spec,
     cdl_cdt = empty,
     cdl_current_thread = undefined,
     cdl_irq_node = irq_map,
     cdl_asid_table = empty,
     cdl_current_domain = undefined\<rparr>"

text {*
  Top-level generator. We validate the capability extension and then use the low-level generator
  above.
*}
definition
  generate :: "camkes_state \<Rightarrow> cdl_heap \<Rightarrow> cdl_state option"
where
  "generate spec extra \<equiv>
     if valid_extra (generate' spec) extra then
       Some (merge_objs (generate' spec) extra)
     else
       None"

lemma generated_implies_valid: "generate spec extra = Some cdl \<Longrightarrow> valid_extra (generate' spec) extra"
  by (metis generate_def option.distinct(1))

lemma merge_contained:
  "\<lbrakk>z = merge_cdl x y; cdl_objects z u = Some v\<rbrakk>
     \<Longrightarrow> cdl_objects x u = Some v \<or> cdl_objects y u = Some v"
  by (clarsimp simp:merge_cdl_def)

abbreviation "is_some s \<equiv> \<not> Option.is_none s"
abbreviation "obj_ids cdl \<equiv> dom (cdl_objects cdl)"
abbreviation "obj_ids' extra \<equiv> dom extra"
abbreviation "obj_count cdl \<equiv> card (obj_ids cdl)"
abbreviation "obj_count' extra \<equiv> card (obj_ids' extra)"
abbreviation "objs cdl \<equiv> the ` (Set.filter is_some (range (cdl_objects cdl)))"
abbreviation "objs' extra \<equiv> the ` (Set.filter is_some (range extra))"

lemma valid_only_pds_pts_frames:
  "valid_extra init cdl \<Longrightarrow> \<forall>i \<in> objs' cdl. case i of PageDirectory _ \<Rightarrow> True
                                                   | PageTable _ \<Rightarrow> True
                                                   | Frame _ \<Rightarrow> True
                                                   | _ \<Rightarrow> False"
  apply (clarsimp simp:valid_extra_def)
  apply (erule_tac x=xa in allE)
  by (metis case_option_If2 is_none_def)

lemma cnode_objs_only_cnodes:
  "\<forall>(_, i) \<in> set (cnode_objs spec). case i of CNode _ \<Rightarrow> True | _ \<Rightarrow> False"
  by (clarsimp simp:cnode_objs_def)

lemma tcb_objs_only_tcbs: "\<forall>(_, i) \<in> set (tcb_objs spec). case i of Tcb _ \<Rightarrow> True | _ \<Rightarrow> False"
  apply (clarsimp simp:tcb_objs_def)
  apply (erule disjE)                                       
   by clarsimp+

lemma third_in: "(a, b, c) \<in> S \<Longrightarrow> c \<in> (snd \<circ> snd) ` S"
  by (metis (erased, hide_lams) helper8 image_comp snd_conv)

lemma helper9: "(a \<in> (snd \<circ> snd) ` (set (enumerate i xs))) = (a \<in> snd ` (set xs))"
  by (metis map_map map_snd_enumerate set_map)

lemma ep_objs_only_eps:
  "\<forall>(_, i) \<in> set (ep_objs spec). case i of Endpoint \<Rightarrow> True | AsyncEndpoint \<Rightarrow> True | _ \<Rightarrow> False"
  apply (clarsimp simp:ep_objs_def ep_objs'_def)
  by (metis cdl_object.simps(98) cdl_object.simps(99))

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

lemma generated_no_pds_pts_frames:
  "generate' spec = cdl \<Longrightarrow>
     \<not>(\<exists>x \<in> objs cdl. case x of PageDirectory _ \<Rightarrow> True
                               | PageTable _ \<Rightarrow> True
                               | Frame _ \<Rightarrow> True
                               | _ \<Rightarrow> False)"
  apply (clarsimp simp:generate'_def obj_heap_def)
  apply (subst (asm) helper15)+
  apply (case_tac "map_of (map (\<lambda>(n, y). (the_id_of n, y)) (cnode_objs spec)) xa")
   apply clarsimp
   apply (case_tac "map_of (map (\<lambda>(n, y). (the_id_of n, y)) (tcb_objs spec)) xa")
  oops (* TODO *)

lemma helper12: "valid_extra a b \<Longrightarrow> dom (cdl_objects a) \<inter> dom b = {}"
  by (clarsimp simp:valid_extra_def)

lemma generated_objects_disjoint:
  "generate spec extra = Some cdl \<Longrightarrow> obj_count (generate' spec) + obj_count' extra = obj_count cdl"
  apply (frule generated_implies_valid)
  apply (subst card_Un_disjoint[symmetric])
     apply clarsimp+
   apply (clarsimp simp:helper12)
  by (clarsimp simp:generate_def merge_cdl_def merge_objs_def)

end

end
