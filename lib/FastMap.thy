(*
 * Copyright 2018, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory FastMap
imports
  LemmaBucket
  Qualify
begin

text \<open>
  Efficient rules and tactics for working with large lookup tables (maps).

  Features:
    \<^item> Define a binary lookup tree for any lookup table (requires linorder keys)
    \<^item> Conversion from lookup tree to lookup lists
    \<^item> Pre-computation of lookup results and domain/range sets

  See FastMap_Test for examples.
\<close>

(*
 * TODO:
 *
 *   • Storing the (large) auxilliary theorems with Local_Theory.notes
 *     seems to take quadratic time. Investigate this, or work around
 *     it by hiding the map data behind additional constants.
 *
 *   • Still a bit slower than the StaticFun package. Streamline the
 *     rulesets and proofs.
 *
 *   • We use a lot of manual convs for performance and to avoid
 *     relying on the dynamic simpset. However, we should clean up the
 *     convs and move as much as possible to (simp only:) invocations.
 *
 *     Note that running simp on deeply nested terms (e.g. lists)
 *     always takes quadratic time and we can't use it there. This is
 *     because rewritec unconditionally calls eta_conversion (urgh).
 *
 *   • The injectivity prover currently hardcodes inj_def into the
 *     simpset. This should be changed at some point, probably by
 *     asking the user to prove it beforehand.
 *
 *   • Using the simplifier to evaluate tree lookups is still quite
 *     slow because it looks at the entire tree term (even though
 *     most of it is irrelevant for any given lookup). We should
 *     provide a tactic or simproc to do this.
 *
 *     We already generate lookup theorems for keys in the map, so
 *     this tactic should be optimised for missing keys.
 *
 *   • The linorder requirement can be cumbersome. It arises because
 *     we express the map_of conversion as a general theorem using
 *     lookup_tree_valid. An alternative approach is to extend what
 *     StaticFun does, and cleverly extract the set of all relevant
 *     bindings from the tree on a case-by-case basis.
 *
 *     We would still need to evaluate the key ordering function on
 *     the input keys, but any arbitrary relation would be allowed.
 *     This one probably calls for a wizard.
 *)

locale FastMap
qualify FastMap

text \<open>
  Binary lookup tree. This is largely an implementation detail, so we
  choose the structure to make automation easier (e.g. separate fields
  for the key and value).
\<close>
datatype ('k, 'v) Tree = Leaf | Node 'k 'v "('k, 'v) Tree" "('k, 'v) Tree"

primrec
  lookup_tree :: "('k, 'v) Tree \<Rightarrow> ('k \<Rightarrow> 'ok :: linorder) \<Rightarrow> 'k \<Rightarrow> 'v option"
where
  "lookup_tree Leaf fn x = None"
| "lookup_tree (Node k v l r) fn x =
     (if fn x = fn k then Some v
      else if fn x < fn k then lookup_tree l fn x
      else lookup_tree r fn x)"

text \<open>
  Predicate for well-formed lookup trees.
  This states that the keys are distinct and appear in ascending order.
  It also returns the lowest and highest keys in the tree (or None for empty trees).
\<close>
primrec lookup_tree_valid where
  "lookup_tree_valid (key :: ('k \<Rightarrow> 'ok :: linorder)) Leaf = (True, None)"
| "lookup_tree_valid key (Node k v lt rt) =
     (let (lt_valid, lt_range) = lookup_tree_valid key lt;
          (rt_valid, rt_range) = lookup_tree_valid key rt;
          lt_low = (case lt_range of None \<Rightarrow> k | Some (low, high) \<Rightarrow> low);
          rt_high = (case rt_range of None \<Rightarrow> k | Some (low, high) \<Rightarrow> high)
      in (lt_valid \<and> rt_valid \<and>
          (case lt_range of None \<Rightarrow> True | Some (low, high) \<Rightarrow> key high < key k) \<and>
          (case rt_range of None \<Rightarrow> True | Some (low, high) \<Rightarrow> key k < key low),
          Some (lt_low, rt_high)))"

lemma lookup_tree_valid_simps':
  "lookup_tree_valid key Leaf = (True, None)"
  "lookup_tree_valid key (Node k v Leaf Leaf) = (True, Some (k, k))"
  "\<lbrakk> lookup_tree_valid key (Node lk lv llt lrt) = (True, Some (llow, lhigh));
     key lhigh < key k
   \<rbrakk> \<Longrightarrow> lookup_tree_valid key (Node k v (Node lk lv llt lrt) Leaf) =
           (True, Some (llow, k))"
  "\<lbrakk> lookup_tree_valid key (Node rk rv rlt rrt) = (True, Some (rlow, rhigh));
     key k < key rlow
   \<rbrakk> \<Longrightarrow> lookup_tree_valid key (Node k v Leaf (Node rk rv rlt rrt)) =
           (True, Some (k, rhigh))"
  "\<lbrakk> lookup_tree_valid key (Node lk lv llt lrt) = (True, Some (llow, lhigh));
     lookup_tree_valid key (Node rk rv rlt rrt) = (True, Some (rlow, rhigh));
     key lhigh < key k;
     key k < key rlow
   \<rbrakk> \<Longrightarrow> lookup_tree_valid key (Node k v (Node lk lv llt lrt) (Node rk rv rlt rrt)) =
           (True, Some (llow, rhigh))"
  by auto

lemma lookup_tree_valid_empty:
  "lookup_tree_valid key tree = (True, None) \<Longrightarrow> tree = Leaf"
  apply (induct tree)
   apply simp
  apply (fastforce split: prod.splits option.splits if_splits)
  done

lemma lookup_tree_valid_range:
  "lookup_tree_valid key tree = (True, Some (low, high)) \<Longrightarrow> key low \<le> key high"
  apply (induct tree arbitrary: low high)
   apply simp
  apply (fastforce split: prod.splits option.splits if_splits)
  done

lemma lookup_tree_valid_in_range:
  "lookup_tree_valid key tree = (True, Some (low, high)) \<Longrightarrow>
   lookup_tree tree key k = Some v \<Longrightarrow>
   key k \<in> {key low .. key high}"
  apply (induct tree arbitrary: k v low high)
   apply simp
  apply (fastforce split: prod.splits option.splits if_split_asm
                   dest: lookup_tree_valid_empty lookup_tree_valid_range)
  done

lemma lookup_tree_valid_in_range_None:
  "lookup_tree_valid key tree = (True, Some (low, high)) \<Longrightarrow>
   key k \<notin> {key low .. key high} \<Longrightarrow>
   lookup_tree tree key k = None"
  using lookup_tree_valid_in_range by fastforce

text \<open>
  Flatten a lookup tree into an assoc-list.
  As long as the tree is well-formed, both forms are equivalent.
\<close>
primrec lookup_tree_to_map where
  "lookup_tree_to_map Leaf = []"
| "lookup_tree_to_map (Node k v lt rt) = lookup_tree_to_map lt @ [(k, v)] @ lookup_tree_to_map rt"

lemma lookup_tree_to_map_range:
  "lookup_tree_valid key tree = (True, Some (low, high)) \<Longrightarrow>
   (k, v) \<in> set (lookup_tree_to_map tree) \<Longrightarrow>
   key k \<in> {key low .. key high}"
  apply (induct tree arbitrary: k v low high)
   apply simp
  apply (fastforce split: prod.splits option.splits if_split_asm
                   dest: lookup_tree_valid_empty lookup_tree_valid_range)
  done

lemma lookup_tree_dom_distinct_sorted_:
  "fst (lookup_tree_valid key tree) \<Longrightarrow>
   distinct (lookup_tree_to_map tree) \<and> sorted (map (key o fst) (lookup_tree_to_map tree))"
  apply (induct tree)
   apply simp
  apply (fastforce simp: sorted_append
                   split: prod.splits option.splits if_splits
                   dest: lookup_tree_valid_empty lookup_tree_valid_range
                         lookup_tree_valid_in_range lookup_tree_to_map_range
                   elim: lookup_tree_valid_in_range_None)
  done

lemmas lookup_tree_dom_distinct = lookup_tree_dom_distinct_sorted_[THEN conjunct1]
lemmas lookup_tree_dom_sorted = lookup_tree_dom_distinct_sorted_[THEN conjunct2]

(* The goal is eta-expanded and flipped, which seems to help the proof *)
lemma lookup_tree_to_map_of_:
  "fst (lookup_tree_valid key tree) \<Longrightarrow>
   map_of (map (apfst key) (lookup_tree_to_map tree)) (key k) = lookup_tree tree key k"
  apply (induct tree arbitrary: k)
   apply simp
  (* this big blob just does case distinctions of both subtrees and
     all possible lookup results within each, then solves *)
  (* slow 10s *)
  apply (fastforce simp: apfst_def map_prod_def map_add_def
                   split: prod.splits option.splits if_splits
                   dest: lookup_tree_valid_empty lookup_tree_valid_range lookup_tree_valid_in_range
                   elim: lookup_tree_valid_in_range_None)
  done

(* Standard form of above *)
lemma lookup_tree_to_map_of:
  "fst (lookup_tree_valid key tree) \<Longrightarrow>
   lookup_tree tree key = map_of (map (apfst key) (lookup_tree_to_map tree)) o key"
  apply (rule ext)
  apply (simp add: lookup_tree_to_map_of_)
  done

lemma map_of_key:
  "inj key \<Longrightarrow> map_of (map (apfst key) binds) o key = map_of binds"
  apply (rule ext)
  apply (induct binds)
   apply simp
  apply (clarsimp simp: inj_def dom_def)
  done

lemma lookup_tree_to_map_of_distinct:
  "\<lbrakk> fst (lookup_tree_valid key tree);
     lookup_tree_to_map tree = binds;
     lookup_tree tree key = map_of (map (apfst key) binds) o key
   \<rbrakk> \<Longrightarrow> distinct (map (key o fst) binds)"
  apply (drule sym[where t = binds])
  apply clarsimp
  apply (thin_tac "binds = _")
  apply (induct tree)
   apply simp
  apply (fastforce simp: map_add_def lookup_tree_to_map_of
                   split: prod.splits option.splits if_splits
                   dest: lookup_tree_valid_empty lookup_tree_valid_range
                         lookup_tree_valid_in_range lookup_tree_to_map_range
                   elim: lookup_tree_valid_in_range_None)
  done

lemma distinct_inj:
  "inj f \<Longrightarrow> distinct xs = distinct (map f xs)"
  apply (induct xs)
   apply simp
  apply (simp add: inj_image_mem_iff)
  done

(* Top-level rule for converting to lookup list.
   We add a distinctness assertion for inferring the range of values. *)
lemma lookup_tree_to_map_of_gen:
  "\<lbrakk> inj key;
     fst (lookup_tree_valid key tree);
     lookup_tree_to_map tree = binds
   \<rbrakk> \<Longrightarrow> lookup_tree tree key = map_of binds \<and> distinct (map fst binds)"
  using lookup_tree_to_map_of
  apply (fastforce intro: lookup_tree_to_map_of_distinct
                   simp: map_of_key distinct_inj)
  done

text \<open>
  Domain and range of a @{const map_of}.
  Like @{thm dom_map_of_conv_image_fst} but leaving out the set bloat.
\<close>
lemma dom_map_of_conv_list:
  "dom (map_of xs) = set (map fst xs)"
  by (simp add: dom_map_of_conv_image_fst)

lemma ran_map_of_conv_list:
  "distinct (map fst xs) \<Longrightarrow> ran (map_of xs) = set (map snd xs)"
  by (erule distinct_map_via_ran)

text \<open>
  Read lookup rules from a @{const map_of}.
\<close>

lemma map_of_lookups:
  "m = map_of binds \<and> distinct (map fst binds) \<Longrightarrow>
   list_all (\<lambda>(k, v). m k = Some v) binds"
  apply (induct binds)
   apply simp
  apply (force simp: list_all_iff)
  done

(* Helper for converting from maps defined as @{const fun_upd} chains,
 * which are applied in reverse order *)
lemma map_of_rev:
  "distinct (map fst binds) \<Longrightarrow>
   map_of (rev binds) = map_of binds"
  apply (subgoal_tac "distinct (map fst (rev binds))")
   apply (rule ext)
   apply (induct binds)
    apply simp
   apply (force simp: map_add_def split: option.splits)
  apply (metis distinct_rev rev_map)
  done

lemma list_all_dest:
  "list_all P [(x, y)] \<equiv> P (x, y)"
  "list_all P ((x, y) # z # xs) \<equiv> (P (x, y) \<and> list_all P (z # xs))"
  by auto

(* Tail-recursive list conversion.
 * FIXME: unused; we currently use the default simp rules with manual convs *)
experiment begin
primrec lookup_tree_to_map_append where
  "lookup_tree_to_map_append Leaf xs = xs"
| "lookup_tree_to_map_append (Node k v lt rt) xs =
     lookup_tree_to_map_append lt ((k, v) # lookup_tree_to_map_append rt xs)"

lemma lookup_tree_to_map_append:
  "lookup_tree_to_map tree @ xs = lookup_tree_to_map_append tree xs"
  apply (induct tree arbitrary: xs; fastforce)
  done

lemma lookup_tree_to_map_eval:
  "lookup_tree_to_map tree = lookup_tree_to_map_append tree []"
  by (simp add: lookup_tree_to_map_append[symmetric])
end

(* Install lookup rules that don't depend on if_cong/if_weak_cong setup *)
lemma lookup_tree_simps'[simp]:
  "lookup_tree Leaf fn x = None"
  "fn x = fn y \<Longrightarrow> lookup_tree (Node y v l r) fn x = Some v"
  "fn x < fn y \<Longrightarrow> lookup_tree (Node y v l r) fn x = lookup_tree l fn x"
  "fn x > fn y \<Longrightarrow> lookup_tree (Node y v l r) fn x = lookup_tree r fn x"
  by auto
declare lookup_tree.simps[simp del]

ML \<open>
structure FastMap = struct

(* utils *)
fun mk_optionT typ = Type ("Option.option", [typ])
fun dest_optionT (Type ("Option.option", [typ])) = typ
  | dest_optionT t = raise TYPE ("dest_optionT", [t], [])

val lhs_conv = Conv.fun_conv o Conv.arg_conv
val rhs_conv = Conv.arg_conv
(* first order rewr_conv *)
fun fo_rewr_conv rule ct = let
  val (pure_eq, eqn) =
        ((true, Thm.instantiate (Thm.first_order_match (Thm.lhs_of rule, ct)) rule)
         handle TERM _ =>
           (false, Thm.instantiate (Thm.first_order_match (fst (Thm.dest_binop (Thm.dest_arg (Thm.cprop_of rule))), ct)) rule))
        handle Pattern.MATCH => raise CTERM ("fo_rewr_conv", [Thm.cprop_of rule, ct]);
  in if pure_eq then eqn else eqn RS @{thm eq_reflection} end;
fun fo_rewrs_conv rules = Conv.first_conv (map fo_rewr_conv rules);

(* Tree builder code, copied from StaticFun *)

(* Actually build the tree -- theta (n lg(n)) *)
fun build_tree' _ mk_leaf [] = mk_leaf
  | build_tree' mk_node mk_leaf xs = let
    val len = length xs
    val (ys, zs) = chop (len div 2) xs
  in case zs of [] => error "build_tree': impossible"
    | ((a, b) :: zs) => mk_node a b (build_tree' mk_node mk_leaf ys)
        (build_tree' mk_node mk_leaf zs)
  end

fun build_tree ord xs = case xs of [] => error "build_tree : empty"
  | (idx, v) :: _ => let
    val idxT = fastype_of idx
    val vT = fastype_of v
    val treeT = Type (@{type_name Tree}, [idxT, vT])
    val mk_leaf = Const (@{const_name Leaf}, treeT)
    val node = Const (@{const_name Node},
        idxT --> vT --> treeT --> treeT --> treeT)
    fun mk_node a b l r = node $ a $ b $ l $ r
    val lookup = Const (@{const_name lookup_tree},
        treeT --> fastype_of ord --> idxT
            --> Type (@{type_name option}, [vT]))
  in
    lookup $ (build_tree' mk_node mk_leaf xs) $ ord
  end

fun define_partial_map_tree name mappings ord ctxt = let
    val tree = build_tree ord mappings
  in Local_Theory.define
    ((name, NoSyn), ((Thm.def_binding name, []), tree)) ctxt
    |> apfst (apsnd snd)
  end

(* Prove key ordering theorems. This lets us issue precise error messages
   when the user gives us keys whose ordering cannot be verified.
   We will also need these thms to prove the lookup_tree_valid property. *)
fun prove_key_ord_thms tree_name keyT mappings get_key simp_ctxt ctxt =
  let
    val solver = simp_tac (simp_ctxt ctxt [] []) 1;
  in
    fst (split_last mappings) ~~ tl mappings
    |> map_index (fn (i, ((k1, _), (k2, _))) => let
           val prop = Const (@{const_name less}, keyT --> keyT --> HOLogic.boolT) $
                            (get_key $ k1) $ (get_key $ k2)
                      |> HOLogic.mk_Trueprop;
           val thm = case try (Goal.prove ctxt [] [] prop) (K solver) of
                        SOME x => x
                      | _ => raise TERM (tree_name ^ ": failed to prove less-than ordering for keys #" ^
                                         string_of_int i ^ ", #" ^ string_of_int (i + 1),
                                         [prop]);
         in thm end)
  end;

(* Prove lookup_tree_valid *)
fun prove_tree_valid tree_name mappings kT keyT tree_term get_key simp_ctxt ctxt = let
    val key_ord_thms = prove_key_ord_thms tree_name keyT mappings get_key simp_ctxt ctxt;
    val treeT = fastype_of tree_term
    val valid_resultT = HOLogic.mk_prodT (HOLogic.boolT, mk_optionT (HOLogic.mk_prodT (kT, kT)))
    val tree_valid_prop =
          HOLogic.mk_Trueprop (
            Const (@{const_name fst}, valid_resultT --> HOLogic.boolT) $
            (Const (@{const_name lookup_tree_valid}, (kT --> keyT) --> treeT --> valid_resultT) $
               get_key $ tree_term))
    val solver = simp_tac (put_simpset HOL_basic_ss ctxt
                           addsimps (@{thms prod.sel lookup_tree_valid_simps'} @ key_ord_thms)) 1
  in Goal.prove ctxt [] [] tree_valid_prop (K solver) end

fun solve_simp_tac name ctxt = SUBGOAL (fn (t, i) =>
      (simp_tac ctxt THEN_ALL_NEW SUBGOAL (fn (t', _) =>
          raise TERM (name ^ ": unsolved", [t, t']))) i)

fun convert_tree_to_map kT valT mappings lookup_const tree_def tree_valid_thm simp_ctxt ctxt = let
  val lookupT = fastype_of lookup_const
  (* map_eq = "<tree_const> = map_of <mappings>" *)
  val bindT = HOLogic.mk_prodT (kT, valT)
  val mapping_list = HOLogic.mk_list bindT (map HOLogic.mk_prod mappings)
  val map_eq = HOLogic.mk_eq (lookup_const, Const (@{const_name map_of}, HOLogic.listT bindT --> lookupT) $ mapping_list)
  (* distinct_pred = "distinct (map fst <mappings>)" *)
  val distinct_pred =
        Const (@{const_name distinct}, HOLogic.listT kT --> HOLogic.boolT) $
          (Const (@{const_name map}, (bindT --> kT) --> HOLogic.listT bindT --> HOLogic.listT kT) $
             Const (@{const_name fst}, bindT --> kT) $
             mapping_list)
  val convert_prop = HOLogic.mk_Trueprop (
        HOLogic.mk_conj (map_eq, distinct_pred)
        )
  fun TIMED desc tac = fn st => Seq.make (K (Timing.timeap_msg ("tactic timing for " ^ desc) (fn () => Seq.pull (tac st)) ()))

  val lookup_tree_to_map_eval = let
    (* allow recursive conv in cv2, deferred by function application *)
    infix 1 then_conv'
    fun (cv1 then_conv' cv2) ct =
      let
        val eq1 = cv1 ct;
        val eq2 = cv2 () (Thm.rhs_of eq1);
      in
        if Thm.is_reflexive eq1 then eq2
        else if Thm.is_reflexive eq2 then eq1
        else Thm.transitive eq1 eq2
      end;

    fun append_conv () =
            fo_rewr_conv @{thm append.simps(1)} else_conv
            (fo_rewr_conv @{thm append.simps(2)} then_conv'
             (fn () => rhs_conv (append_conv ())))
    fun to_map_conv () =
            fo_rewr_conv @{thm lookup_tree_to_map.simps(1)} else_conv
            (fo_rewr_conv @{thm lookup_tree_to_map.simps(2)[simplified append.simps]} then_conv'
             (fn () => lhs_conv (to_map_conv ())) then_conv'
             (fn () => rhs_conv (rhs_conv (to_map_conv ()))) then_conv
             append_conv ())
  in to_map_conv () end

  val solver =
        TIMED "unfold" (Conv.gconv_rule (Conv.arg_conv (lhs_conv (lhs_conv (K tree_def)))) 1 #> Seq.succeed) THEN
        TIMED "main rule" (resolve_tac ctxt @{thms lookup_tree_to_map_of_gen} 1) THEN
          TIMED "solve inj" (solve_simp_tac "convert_tree_to_map" (simp_ctxt ctxt @{thms simp_thms} @{thms inj_def}) 1) THEN
         TIMED "resolve valid" (resolve_tac ctxt [tree_valid_thm] 1) THEN
        TIMED "convert tree" (Conv.gconv_rule (Conv.arg_conv (lhs_conv lookup_tree_to_map_eval)) 1 #> Seq.succeed) THEN
        resolve_tac ctxt @{thms refl} 1
  val convert_thm = Goal.prove ctxt [] [] convert_prop (K solver)
  in convert_thm end

(* Obtain domain and range from lookup list *)
fun domain_range_common dom_ran_const xT xs lookup_const tree_map_eqn intro_conv_tac ctxt = let
  val lookupT = fastype_of lookup_const
  val prop = HOLogic.mk_Trueprop (
        HOLogic.mk_eq (
          Const (dom_ran_const, lookupT --> HOLogic.mk_setT xT) $ lookup_const,
          Const (@{const_name set}, HOLogic.listT xT --> HOLogic.mk_setT xT) $
            (HOLogic.mk_list xT xs)
        ))
  val tree_map_eqn' = tree_map_eqn RS @{thm eq_reflection}
  val map_eqns = @{thms list.map prod.sel}
  val solver =
        (Conv.gconv_rule (Conv.arg_conv (lhs_conv (Conv.arg_conv (K tree_map_eqn')))) 1 #> Seq.succeed) THEN
        intro_conv_tac THEN
        (Conv.gconv_rule (Conv.arg_conv (lhs_conv (
             Conv.top_conv (K (Conv.try_conv (fo_rewrs_conv map_eqns))) ctxt
           ))) 1 #> Seq.succeed) THEN
        resolve_tac ctxt @{thms refl} 1
  in Goal.prove ctxt [] [] prop (K solver) end;

fun tree_domain kT mappings lookup_const tree_map_eqn ctxt =
  domain_range_common
    @{const_name dom} kT (map fst mappings) lookup_const tree_map_eqn
    (* like (subst dom_map_of_conv_list) but faster *)
    (resolve_tac ctxt @{thms dom_map_of_conv_list[THEN trans]} 1)
    ctxt;

fun tree_range valT mappings lookup_const tree_map_eqn map_distinct_thm ctxt =
  domain_range_common
    @{const_name ran} valT (map snd mappings) lookup_const tree_map_eqn
    (* like (subst ran_map_of_conv_list) but faster *)
    (resolve_tac ctxt @{thms ran_map_of_conv_list[THEN trans]} 1 THEN
     resolve_tac ctxt [map_distinct_thm] 1)
    ctxt;

(* Choosing names for the const and its theorems. The constant will be named with
   map_name; Local_Theory.define may also add extra names (e.g. <map_name>_def) *)
type name_opts = {
    map_name: string,
    tree_valid_thm: string,
    tree_map_eqn: string,
    keys_distinct_thm: string,
    lookup_thms: string,
    domain_thm: string,
    range_thm: string
};

fun name_opts_default (map_name: string): name_opts = {
    map_name = map_name,
    tree_valid_thm = map_name ^ "_tree_valid",
    tree_map_eqn = map_name ^ "_tree_to_map",
    keys_distinct_thm = map_name ^ "_keys_distinct",
    lookup_thms = map_name ^ "_lookups",
    domain_thm = map_name ^ "_domain",
    range_thm = map_name ^ "_range"
};

(* Top level interface *)
fun define_map
            (name_opts: name_opts)
            (mappings: (term * term) list)
            (get_key: term) (* function to get linorder key, must be injective *)
            (extra_simps: thm list)
            (minimal_simp: bool) (* true: start with minimal simpset; extra_simps must be adequate *)
            ctxt = let
    fun simp_ctxt ctxt basic_simps more_simps = if minimal_simp
      then put_simpset HOL_basic_ss ctxt addsimps (basic_simps @ extra_simps @ more_simps)
      else ctxt addsimps (extra_simps @ more_simps)

    val _ = tracing (#map_name name_opts ^ ": defining tree")
    val start = Timing.start ()
    val ((lookup_const, tree_def), ctxt) =
            define_partial_map_tree (Binding.name (#map_name name_opts)) mappings get_key ctxt
    val (tree_const, _ $ tree_term $ _) = Logic.dest_equals (Thm.prop_of tree_def)
    val (kT, keyT) = dest_funT (fastype_of get_key)
    val valT = dest_optionT (snd (dest_funT (fastype_of tree_const)))
    val _ = tracing ("  done: " ^ Timing.message (Timing.result start))

    val _ = tracing (#map_name name_opts ^ ": proving tree is well-formed")
    val start = Timing.start ()
    val tree_valid_thm = prove_tree_valid (#map_name name_opts) mappings kT keyT tree_term get_key simp_ctxt ctxt
    val (_, ctxt) = ctxt |> Local_Theory.notes
        [((Binding.name (#tree_valid_thm name_opts), []), [([tree_valid_thm], [])])]
    val _ = tracing ("  done: " ^ Timing.message (Timing.result start))

    val _ = tracing (#map_name name_opts ^ ": converting tree to map")
    val start = Timing.start ()
    val convert_thm =
          convert_tree_to_map kT valT mappings lookup_const tree_def tree_valid_thm simp_ctxt ctxt
    val [tree_map_eqn, map_distinct_thm] = HOLogic.conj_elims ctxt convert_thm
    val _ = tracing ("  done: " ^ Timing.message (Timing.result start))
    val _ = tracing (#map_name name_opts ^ ": storing map and distinctness theorems")
    val start = Timing.start ()
    val (_, ctxt) = ctxt |> Local_Theory.notes
        [((Binding.name (#tree_map_eqn name_opts), []), [([tree_map_eqn], [])]),
         ((Binding.name (#keys_distinct_thm name_opts), []), [([map_distinct_thm], [])])]
    val _ = tracing ("  done: " ^ Timing.message (Timing.result start))

    val _ = tracing (#map_name name_opts ^ ": obtaining lookup rules")
    val start = Timing.start ()
    val combined_lookup_thm =
          (convert_thm RS @{thm map_of_lookups})
          |> Conv.fconv_rule (Conv.top_conv (K (Conv.try_conv (fo_rewrs_conv @{thms list_all_dest}))) ctxt)
    val _ = tracing ("  splitting... " ^ Timing.message (Timing.result start))
    val lookup_thms = HOLogic.conj_elims ctxt combined_lookup_thm
                      |> map (Conv.fconv_rule (Conv.arg_conv (Conv.rewr_conv @{thm prod.case[THEN eq_reflection]})))

    val _ = if length lookup_thms = length mappings then () else
              raise THM ("wrong number of lookup thms: " ^ string_of_int (length lookup_thms) ^
                         " instead of " ^ string_of_int (length mappings), 0,
                         lookup_thms)
    val (_, ctxt) = ctxt |> Local_Theory.notes
        [((Binding.name (#lookup_thms name_opts), []), [(lookup_thms, [])])]
    val _ = tracing ("  done: " ^ Timing.message (Timing.result start))

    (* domain and range *)
    val _ = tracing (#map_name name_opts ^ ": getting domain and range")
    val start = Timing.start ()
    val domain_thm = timeap_msg "  calculate domain"
            (tree_domain kT mappings lookup_const tree_map_eqn) ctxt
    val range_thm = timeap_msg "  calculate range"
            (tree_range valT mappings lookup_const tree_map_eqn map_distinct_thm) ctxt
    val (_, ctxt) = ctxt |> Local_Theory.notes
        [((Binding.name (#domain_thm name_opts), []), [([domain_thm], [])]),
         ((Binding.name (#range_thm name_opts), []), [([range_thm], [])])]
    val _ = tracing ("  done: " ^ Timing.message (Timing.result start))
  in ctxt end

end
\<close>

end_qualify

end