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
 *   • Storing the auxilliary list theorems with Local_Theory.notes
 *     takes quadratic time. Unfortunately, this seems to be a problem
 *     deep inside the Isabelle implementation. One might try to wrap
 *     the lists in new constants, but Local_Theory.define also takes
 *     quadratic time.
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
 *   • The key ordering prover is currently hardcoded to simp_tac;
 *     this should also be generalised. On the other hand, the user
 *     could work around this by manually supplying a simpset with
 *     precisely the needed theorems.
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

locale FastMap begin

text \<open>
  Binary lookup tree. This is largely an implementation detail, so we
  choose the structure to make automation easier (e.g. separate fields
  for the key and value).

  We could reuse HOL.Tree instead, but the proofs would need changing.
\<close>
datatype ('k, 'v) Tree =
    Leaf
  | Node 'k 'v "('k, 'v) Tree" "('k, 'v) Tree"

primrec lookup_tree :: "('k \<Rightarrow> 'ok :: linorder) \<Rightarrow> ('k, 'v) Tree \<Rightarrow> 'k \<Rightarrow> 'v option"
  where
    "lookup_tree key Leaf x = None"
  | "lookup_tree key (Node k v l r) x =
       (if key x = key k then Some v
        else if key x < key k then lookup_tree key l x
        else lookup_tree key r x)"

text \<open>
  Predicate for well-formed lookup trees.
  This states that the keys are distinct and appear in ascending order.
  It also returns the lowest and highest keys in the tree (or None for empty trees).
\<close>
primrec lookup_tree_valid ::
        "('k \<Rightarrow> 'ok :: linorder) \<Rightarrow> ('k, 'v) Tree \<Rightarrow> bool \<times> ('k \<times> 'k) option"
  where
    "lookup_tree_valid key Leaf = (True, None)"
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
   lookup_tree key tree k = Some v \<Longrightarrow>
   key k \<in> {key low .. key high}"
  apply (induct tree arbitrary: k v low high)
   apply simp
  apply (fastforce split: prod.splits option.splits if_split_asm
                   dest: lookup_tree_valid_empty lookup_tree_valid_range)
  done

lemma lookup_tree_valid_in_range_None:
  "lookup_tree_valid key tree = (True, Some (low, high)) \<Longrightarrow>
   key k \<notin> {key low .. key high} \<Longrightarrow>
   lookup_tree key tree k = None"
  using lookup_tree_valid_in_range by fastforce

text \<open>
  Flatten a lookup tree into an assoc-list.
  As long as the tree is well-formed, both forms are equivalent.
\<close>
primrec lookup_tree_to_list :: "('k, 'v) Tree \<Rightarrow> ('k \<times> 'v) list"
  where
    "lookup_tree_to_list Leaf = []"
  | "lookup_tree_to_list (Node k v lt rt) =
        lookup_tree_to_list lt @ [(k, v)] @ lookup_tree_to_list rt"

lemma lookup_tree_to_list_range:
  "lookup_tree_valid key tree = (True, Some (low, high)) \<Longrightarrow>
   (k, v) \<in> set (lookup_tree_to_list tree) \<Longrightarrow>
   key k \<in> {key low .. key high}"
  apply (induct tree arbitrary: k v low high)
   apply simp
  apply (fastforce split: prod.splits option.splits if_split_asm
                   dest: lookup_tree_valid_empty lookup_tree_valid_range)
  done

lemma lookup_tree_dom_distinct_sorted_:
  "fst (lookup_tree_valid key tree) \<Longrightarrow>
   distinct (lookup_tree_to_list tree) \<and> sorted (map (key o fst) (lookup_tree_to_list tree))"
  apply (induct tree)
   apply simp
  apply (fastforce simp: sorted_append
                   split: prod.splits option.splits if_splits
                   dest: lookup_tree_valid_empty lookup_tree_valid_range
                         lookup_tree_valid_in_range lookup_tree_to_list_range
                   elim: lookup_tree_valid_in_range_None)
  done

lemmas lookup_tree_dom_distinct = lookup_tree_dom_distinct_sorted_[THEN conjunct1]
lemmas lookup_tree_dom_sorted = lookup_tree_dom_distinct_sorted_[THEN conjunct2]

(* This goal is eta-expanded and flipped, which seems to help its proof *)
lemma lookup_tree_to_list_of_:
  "fst (lookup_tree_valid key tree) \<Longrightarrow>
   map_of (map (apfst key) (lookup_tree_to_list tree)) (key k) = lookup_tree key tree k"
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
lemma lookup_tree_to_list_of:
  "fst (lookup_tree_valid key tree) \<Longrightarrow>
   lookup_tree key tree = map_of (map (apfst key) (lookup_tree_to_list tree)) o key"
  apply (rule ext)
  apply (simp add: lookup_tree_to_list_of_)
  done

lemma map_of_key:
  "inj key \<Longrightarrow> map_of (map (apfst key) binds) o key = map_of binds"
  apply (rule ext)
  apply (induct binds)
   apply simp
  apply (clarsimp simp: inj_def dom_def)
  done

lemma lookup_tree_to_list_of_distinct:
  "\<lbrakk> fst (lookup_tree_valid key tree);
     lookup_tree_to_list tree = binds;
     lookup_tree key tree = map_of (map (apfst key) binds) o key
   \<rbrakk> \<Longrightarrow> distinct (map (key o fst) binds)"
  apply (drule sym[where t = binds])
  apply clarsimp
  apply (thin_tac "binds = _")
  apply (induct tree)
   apply simp
  apply (fastforce simp: map_add_def lookup_tree_to_list_of
                   split: prod.splits option.splits if_splits
                   dest: lookup_tree_valid_empty lookup_tree_valid_range
                         lookup_tree_valid_in_range lookup_tree_to_list_range
                   elim: lookup_tree_valid_in_range_None)
  done

(* Top-level rule for converting to lookup list.
   We add a distinctness assertion for inferring the range of values. *)
lemma lookup_tree_to_list_of_gen:
  "\<lbrakk> inj key;
     fst (lookup_tree_valid key tree);
     lookup_tree_to_list tree = binds
   \<rbrakk> \<Longrightarrow> lookup_tree key tree = map_of binds \<and> distinct (map fst binds)"
  using lookup_tree_to_list_of
  apply (fastforce intro: lookup_tree_to_list_of_distinct
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

(* Install lookup rules that don't depend on if_cong/if_weak_cong setup *)
lemma lookup_tree_simps':
  "lookup_tree key Leaf x = None"
  "key x = key k \<Longrightarrow> lookup_tree key (Node k v l r) x = Some v"
  "key x < key k \<Longrightarrow> lookup_tree key (Node k v l r) x = lookup_tree key l x"
  "key x > key k \<Longrightarrow> lookup_tree key (Node k v l r) x = lookup_tree key r x"
  by auto
end

declare FastMap.lookup_tree.simps[simp del]
declare FastMap.lookup_tree_simps'[simp]

ML \<open>
structure FastMap = struct

(* utils *)
fun mk_optionT typ = Type ("Option.option", [typ])
fun dest_optionT (Type ("Option.option", [typ])) = typ
  | dest_optionT t = raise TYPE ("dest_optionT", [t], [])

(* O(1) version of thm RS @{thm eq_reflection} *)
fun then_eq_reflection thm = let
  val (x, y) = Thm.dest_binop (Thm.dest_arg (Thm.cprop_of thm));
  val cT = Thm.ctyp_of_cterm x;
  val rule = @{thm eq_reflection} |> Thm.instantiate' [SOME cT] [SOME x, SOME y];
  in Thm.implies_elim rule thm end;

val lhs_conv = Conv.fun_conv o Conv.arg_conv
val rhs_conv = Conv.arg_conv
(* first order rewr_conv *)
fun fo_rewr_conv rule ct = let
  val (pure_eq, eqn) =
        ((true, Thm.instantiate (Thm.first_order_match (Thm.lhs_of rule, ct)) rule)
         handle TERM _ =>
           (false, Thm.instantiate (Thm.first_order_match
                      (fst (Thm.dest_binop (Thm.dest_arg (Thm.cprop_of rule))), ct)) rule))
        handle Pattern.MATCH => raise CTERM ("fo_rewr_conv", [Thm.cprop_of rule, ct]);
  in if pure_eq then eqn else then_eq_reflection eqn end;
fun fo_rewrs_conv rules = Conv.first_conv (map fo_rewr_conv rules);

(* Evaluate a term with rewrite rules. Unlike the simplifier, this
 * does only one top-down pass, but that's enough for tasks like
 * pushing List.map through a list. Also runs much faster. *)
fun fo_topdown_rewr_conv rules ctxt =
      Conv.top_conv (K (Conv.try_conv (fo_rewrs_conv rules))) ctxt

(* Allow recursive conv in cv2, deferred by function application *)
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

(*
 * Helper that makes it easier to describe where to apply a conv.
 * This takes a skeleton term and applies the conversion wherever "HERE"
 * appears in the skeleton.
 *
 * FIXME: use HOL-Library.Rewrite instead
 *)
fun conv_at skel conv ctxt ct = let
  fun mismatch current_skel current_ct =
    raise TERM ("conv_at mismatch", [current_skel, Thm.term_of current_ct, skel, Thm.term_of ct])

  fun walk (Free ("HERE", _)) ctxt ct = conv ct
    | walk (skel as skel_f $ skel_x) ctxt ct =
        (case Thm.term_of ct of
            f $ x => Conv.combination_conv (walk skel_f ctxt) (walk skel_x ctxt) ct
          | _ => mismatch skel ct)
    | walk (skel as Abs (_, _, skel_body)) ctxt ct =
        (case Thm.term_of ct of
            Abs _ => Conv.abs_conv (fn (v, ctxt') => walk skel_body ctxt') ctxt ct
          | _ => mismatch skel ct)
    (* Also check that Consts match the skeleton pattern *)
    | walk (skel as Const (skel_name, _)) ctxt ct =
        if (case Thm.term_of ct of Const (name, _) => name = skel_name | _ => false)
        then Thm.reflexive ct
        else mismatch skel ct
    (* Default case *)
    | walk _ ctxt ct = Thm.reflexive ct
  in walk skel ctxt ct end

fun gconv_at_tac pat conv ctxt = Conv.gconv_rule (conv_at pat conv ctxt) 1 #> Seq.succeed


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

fun build_tree xs = case xs of [] => error "build_tree : empty"
  | (idx, v) :: _ => let
    val idxT = fastype_of idx
    val vT = fastype_of v
    val treeT = Type (@{type_name FastMap.Tree}, [idxT, vT])
    val mk_leaf = Const (@{const_name FastMap.Leaf}, treeT)
    val node = Const (@{const_name FastMap.Node},
        idxT --> vT --> treeT --> treeT --> treeT)
    fun mk_node a b l r = node $ a $ b $ l $ r
  in
    build_tree' mk_node mk_leaf xs
  end

fun define_partial_map_tree map_name mappings ord_term ctxt = let
    val (idxT, vT) = apply2 fastype_of (hd mappings)
    val treeT = Type (@{type_name FastMap.Tree}, [idxT, vT])
    val lookup = Const (@{const_name FastMap.lookup_tree},
                        fastype_of ord_term --> treeT --> idxT
                            --> Type (@{type_name option}, [vT]))
    val map_term = lookup $ ord_term $ build_tree mappings
    val ((map_const, (_, map_def)), ctxt) =
          Local_Theory.define ((map_name, NoSyn), ((Thm.def_binding map_name, []), map_term)) ctxt
  in
    ((map_const, map_def), ctxt)
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
           in case try (Goal.prove ctxt [] [] prop) (K solver) of
                  SOME x => x
                | _ => raise TERM (tree_name ^ ": failed to prove less-than ordering for keys #" ^
                                   string_of_int i ^ ", #" ^ string_of_int (i + 1),
                                   [prop])
           end)
  end;

(* Prove lookup_tree_valid *)
fun prove_tree_valid tree_name mappings kT keyT tree_term get_key simp_ctxt ctxt = let
    val key_ord_thms = prove_key_ord_thms tree_name keyT mappings get_key simp_ctxt ctxt;
    val treeT = fastype_of tree_term
    val valid_resultT = HOLogic.mk_prodT (HOLogic.boolT, mk_optionT (HOLogic.mk_prodT (kT, kT)))
    val tree_valid_prop =
          HOLogic.mk_Trueprop (
            Const (@{const_name fst}, valid_resultT --> HOLogic.boolT) $
            (Const (@{const_name FastMap.lookup_tree_valid},
                    (kT --> keyT) --> treeT --> valid_resultT) $
               get_key $ tree_term))
    val solver = simp_tac (put_simpset HOL_basic_ss ctxt
                           addsimps (@{thms prod.sel FastMap.lookup_tree_valid_simps'} @
                                     key_ord_thms)) 1
  in Goal.prove ctxt [] [] tree_valid_prop (K solver) end

fun solve_simp_tac name ctxt = SUBGOAL (fn (t, i) =>
      (simp_tac ctxt THEN_ALL_NEW SUBGOAL (fn (t', _) =>
          raise TERM (name ^ ": unsolved", [t, t']))) i)

fun convert_to_lookup_list kT valT mappings map_const map_def tree_valid_thm simp_ctxt ctxt = let
  val lookupT = fastype_of map_const
  (* map_eq = "<tree_const> = map_of <mappings>" *)
  val bindT = HOLogic.mk_prodT (kT, valT)
  val lookup_list = HOLogic.mk_list bindT (map HOLogic.mk_prod mappings)
  val map_of_Const = Const (@{const_name map_of}, HOLogic.listT bindT --> lookupT)
  val map_eq = HOLogic.mk_eq (map_const, map_of_Const $ lookup_list)
  (* distinct_pred = "distinct (map fst <mappings>)" *)
  val distinct_pred =
        Const (@{const_name distinct}, HOLogic.listT kT --> HOLogic.boolT) $
          (Const (@{const_name map}, (bindT --> kT) --> HOLogic.listT bindT --> HOLogic.listT kT) $
             Const (@{const_name fst}, bindT --> kT) $
             lookup_list)
  val convert_prop = HOLogic.mk_Trueprop (
        HOLogic.mk_conj (map_eq, distinct_pred)
        )
  fun TIMED desc tac = fn st =>
        Seq.make (K (Timing.timeap_msg ("tactic timing for " ^ desc)
                          (fn () => Seq.pull (tac st)) ()))

  val append_basecase = @{thm append.simps(1)}
  val append_rec = @{thm append.simps(2)}
  val lookup_tree_to_list_basecase = @{thm FastMap.lookup_tree_to_list.simps(1)}
  val lookup_tree_to_list_rec = @{thm FastMap.lookup_tree_to_list.simps(2)[simplified append.simps]}

  val lookup_tree_to_list_eval = let
    fun append_conv () =
            fo_rewr_conv append_basecase else_conv
            (fo_rewr_conv append_rec then_conv'
             (fn () => rhs_conv (append_conv ())))
    fun to_map_conv () =
            fo_rewr_conv lookup_tree_to_list_basecase else_conv
            (fo_rewr_conv lookup_tree_to_list_rec then_conv'
             (fn () => lhs_conv (to_map_conv ())) then_conv'
             (fn () => rhs_conv (rhs_conv (to_map_conv ()))) then_conv
             append_conv ())
  in to_map_conv () end

  val solver =
        TIMED "unfold" (gconv_at_tac @{term "Trueprop (HERE = map_of dummy1 \<and> dummy2)"}
                                     (K map_def) ctxt)
        THEN
        TIMED "main rule" (resolve_tac ctxt @{thms FastMap.lookup_tree_to_list_of_gen} 1)
        THEN
          TIMED "solve inj" (solve_simp_tac "solve inj"
                              (simp_ctxt ctxt @{thms simp_thms} @{thms inj_def}) 1)
          THEN
         TIMED "resolve valid" (resolve_tac ctxt [tree_valid_thm] 1)
         THEN
        TIMED "convert tree" (gconv_at_tac @{term "Trueprop (HERE = dummy1)"}
                                           lookup_tree_to_list_eval ctxt)
        THEN
        resolve_tac ctxt @{thms refl} 1
  val convert_thm = Goal.prove ctxt [] [] convert_prop (K solver)
  in convert_thm end

(* Obtain domain and range from lookup list *)
fun domain_range_common dom_ran_const xT xs map_const lookup_list_eqn intro_conv_tac ctxt = let
  val mapT = fastype_of map_const
  val prop = HOLogic.mk_Trueprop (
        HOLogic.mk_eq (
          Const (dom_ran_const, mapT --> HOLogic.mk_setT xT) $ map_const,
          Const (@{const_name set}, HOLogic.listT xT --> HOLogic.mk_setT xT) $
            (HOLogic.mk_list xT xs)
        ))
  val lookup_list_eqn' = then_eq_reflection lookup_list_eqn
  val map_fst_snd_conv = fo_topdown_rewr_conv @{thms list.map prod.sel} ctxt
  val solver =
        (gconv_at_tac @{term "Trueprop (dom_ran_dummy1 HERE = dummy2)"}
                      (K lookup_list_eqn') ctxt)
        THEN
        intro_conv_tac
        THEN
        gconv_at_tac @{term "Trueprop (HERE = dummy1)"} map_fst_snd_conv ctxt
        THEN
        resolve_tac ctxt @{thms refl} 1
  in Goal.prove ctxt [] [] prop (K solver) end;

fun tree_domain kT mappings map_const lookup_list_eqn ctxt =
  domain_range_common
    @{const_name dom} kT (map fst mappings) map_const lookup_list_eqn
    (* like (subst dom_map_of_conv_list) but faster *)
    (resolve_tac ctxt @{thms FastMap.dom_map_of_conv_list[THEN trans]} 1)
    ctxt;

fun tree_range valT mappings map_const lookup_list_eqn map_distinct_thm ctxt =
  domain_range_common
    @{const_name ran} valT (map snd mappings) map_const lookup_list_eqn
    (* like (subst ran_map_of_conv_list) but faster *)
    (resolve_tac ctxt @{thms FastMap.ran_map_of_conv_list[THEN trans]} 1 THEN
     resolve_tac ctxt [map_distinct_thm] 1)
    ctxt;


(* Choosing names for the const and its theorems. The constant will be named with
   map_name; Local_Theory.define may also add extra names (e.g. <map_name>_def) *)
type name_opts = {
    map_name: string,
    tree_valid_thm: string,
    to_lookup_list: string,
    keys_distinct_thm: string,
    lookup_thms: string,
    domain_thm: string,
    range_thm: string
};

fun name_opts_default (map_name: string): name_opts = {
    map_name = map_name,
    tree_valid_thm = map_name ^ "_tree_valid",
    to_lookup_list = map_name ^ "_to_lookup_list",
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

    val (kT, keyT) = dest_funT (fastype_of get_key)
    val valT = fastype_of (snd (hd mappings))

    val _ = tracing (#map_name name_opts ^ ": defining tree")
    val start = Timing.start ()
    val ((map_const, map_def), ctxt) =
            define_partial_map_tree
                (Binding.name (#map_name name_opts))
                mappings get_key ctxt
    val _ = tracing ("  done: " ^ Timing.message (Timing.result start))

    val _ = tracing (#map_name name_opts ^ ": proving tree is well-formed")
    val start = Timing.start ()
    val _ $ _ $ tree_term = Thm.term_of (Thm.rhs_of map_def)
    val tree_valid_thm =
          prove_tree_valid (#map_name name_opts) mappings kT keyT tree_term get_key simp_ctxt ctxt
    val (_, ctxt) = ctxt |> Local_Theory.notes
        [((Binding.name (#tree_valid_thm name_opts), []), [([tree_valid_thm], [])])]
    val _ = tracing ("  done: " ^ Timing.message (Timing.result start))

    val _ = tracing (#map_name name_opts ^ ": converting tree to map")
    val start = Timing.start ()
    val convert_thm =
          convert_to_lookup_list kT valT mappings map_const map_def tree_valid_thm simp_ctxt ctxt
    val [lookup_list_eqn, map_distinct_thm] = HOLogic.conj_elims ctxt convert_thm
    val _ = tracing ("  done: " ^ Timing.message (Timing.result start))
    val _ = tracing (#map_name name_opts ^ ": storing map and distinctness theorems")
    val start = Timing.start ()
    val (_, ctxt) = ctxt |> Local_Theory.notes
        [((Binding.name (#to_lookup_list name_opts), []), [([lookup_list_eqn], [])]),
         ((Binding.name (#keys_distinct_thm name_opts), []), [([map_distinct_thm], [])])]
    val _ = tracing ("  done: " ^ Timing.message (Timing.result start))

    val _ = tracing (#map_name name_opts ^ ": obtaining lookup rules")
    val start = Timing.start ()
    fun dest_list_all_conv () =
          fo_rewr_conv @{thm FastMap.list_all_dest(1)} else_conv
          (fo_rewr_conv @{thm FastMap.list_all_dest(2)} then_conv'
           (fn () => rhs_conv (dest_list_all_conv())))
    val combined_lookup_thm =
          (convert_thm RS @{thm FastMap.map_of_lookups})
          |> Conv.fconv_rule (conv_at @{term "Trueprop HERE"} (dest_list_all_conv ()) ctxt)
    val _ = tracing ("  splitting... " ^ Timing.message (Timing.result start))
    val lookup_thms =
          HOLogic.conj_elims ctxt combined_lookup_thm
          |> map (Conv.fconv_rule (conv_at @{term "Trueprop HERE"}
                                     (fo_rewr_conv @{thm prod.case[THEN eq_reflection]}) ctxt))

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
            (tree_domain kT mappings map_const lookup_list_eqn) ctxt
    val range_thm = timeap_msg "  calculate range"
            (tree_range valT mappings map_const lookup_list_eqn map_distinct_thm) ctxt
    val (_, ctxt) = ctxt |> Local_Theory.notes
        [((Binding.name (#domain_thm name_opts), []), [([domain_thm], [])]),
         ((Binding.name (#range_thm name_opts), []), [([range_thm], [])])]
    val _ = tracing ("  done: " ^ Timing.message (Timing.result start))
  in ctxt end

end
\<close>

end