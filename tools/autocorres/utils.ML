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
 * Miscellaneous functions and utilities.
 *
 * TODO: many of these are no longer used and should be cleaned.
 *)
structure Utils =
struct

(*
 * Catch-all for invalid inputs: Instead of raising MATCH, describe what
 * the invalid input was.
 *)
exception InvalidInput of string;
fun invalid_typ s (t : typ) =
    raise InvalidInput ("Expected " ^ s ^ ", but got '" ^ (@{make_string} t) ^ "'")
fun invalid_term s (t : term) =
    raise InvalidInput ("Expected " ^ s ^ ", but got '" ^ (@{make_string} t) ^ "'")
fun invalid_input s t =
    raise InvalidInput ("Expected " ^ s ^ ", but got '" ^ t ^ "'")

(* Different sides of a binary operator. *)
fun rhs_of (Const _ $ _ $ r) = r
  | rhs_of t = raise (TERM ("rhs_of", [t]))
fun lhs_of (Const _ $ l $ _) = l
  | lhs_of t = raise (TERM ("lhs_of", [t]))

fun rhs_of_eq (Const (@{const_name "Trueprop"}, _) $ eq) = rhs_of_eq eq
  | rhs_of_eq (Const (@{const_name "Pure.eq"}, _) $ _ $ r) = r
  | rhs_of_eq (Const (@{const_name "HOL.eq"}, _) $ _ $ r) = r
  | rhs_of_eq t = raise (TERM ("rhs_of_eq", [t]))

fun lhs_of_eq (Const (@{const_name "Trueprop"}, _) $ eq) = lhs_of_eq eq
  | lhs_of_eq (Const (@{const_name "Pure.eq"}, _) $ l $ _) = l
  | lhs_of_eq (Const (@{const_name "HOL.eq"}, _) $ l $ _) = l
  | lhs_of_eq t = raise (TERM ("lhs_of_eq", [t]))

fun clhs_of ct = nth (Drule.strip_comb ct |> #2) 0
fun crhs_of ct = nth (Drule.strip_comb ct |> #2) 1
fun chead_of ct = Drule.strip_comb ct |> fst
fun ctail_of ct = Drule.strip_comb ct |> snd |> hd
fun cterm_nth_arg ct n =
  (Drule.strip_comb ct |> snd |> (fn x => nth x n))
  handle Subscript =>
    raise CTERM ("Argument " ^ (@{make_string} n) ^ " doesn't exist", [ct])
fun term_nth_arg t n =
  (Term.strip_comb t |> snd |> (fn x => nth x n))
  handle Subscript =>
    raise TERM ("Argument " ^ (@{make_string} n) ^ " doesn't exist", [t])

(* Convert a term into a string. *)
fun term_to_string ctxt t =
  Syntax.check_term ctxt t
  |> Thm.cterm_of ctxt
  |> @{make_string}

(* Warning with 'autocorres' prefix. *)
fun ac_warning str = warning ("autocorres: " ^ str)

(* List functions that should really be included in PolyML. *)

fun zipWith f (x::xs) (y::ys) = f x y :: zipWith f xs ys
  | zipWith _ _ _ = []
fun zip xs ys = zipWith (curry I) xs ys
fun zip3 (x::xs) (y::ys) (z::zs) = ((x,y,z)::(zip3 xs ys zs))
  | zip3 _ _ _ = []

fun findIndex p =
  let fun find _ [] = NONE
        | find n (x::xs) = if p x then SOME (x, n) else find (n+1) xs
  in find 0 end

fun enumerate xs = let
  fun enum _ [] = []
    | enum n (x::xs) = (n, x) :: enum (n+1) xs
  in enum 0 xs end

fun nubBy _ [] = []
  | nubBy f (x::xs) = x :: filter (fn y => f x <> f y) (nubBy f xs)

fun accumulate f acc xs = let
  fun walk results acc [] = (results [], acc)
    | walk results acc (x::xs) = let
        val acc' = f x acc;
        in walk (results o cons acc') acc' xs end;
  in walk I acc xs end;

(* Define a constant "name" of type "term" into the local theory "lthy". *)
fun define_const name term lthy =
  let
    val lthy = lthy |> Local_Theory.open_target |> snd
    val ((_, (_, thm)), lthy) = Local_Theory.define ((Binding.name name, NoSyn), (Binding.empty_atts, term)) lthy
    val lthy' = Local_Theory.close_target lthy
    val thm' = Morphism.thm (Local_Theory.target_morphism lthy) thm
  in
    (thm', lthy')
  end

(*
 * Define a constant "name" of value "term" into the local theory "lthy".
 *
 * Arguments "args" to the term may be given, which consist of a list of names
 * and types.
 *)
fun define_const_args name hidden term args lthy =
  let
    fun maybe_hide x = if hidden then Binding.concealed x else x

    (* Generate a header for the term. *)
    val head = betapplys (Free (name, (map snd args) ---> fastype_of term), args |> map Free)
    val new_term = Logic.mk_equals (head, term)

    (* Define the constant. *)
   val lthy = lthy |> Local_Theory.open_target |> snd
   val ((_, (_, thm)), lthy) =
        Specification.definition (SOME (maybe_hide (Binding.name name), NONE, NoSyn))
            [] [] (Binding.empty_atts, new_term) lthy

    (* Integrate into the current locale. *)
    val lthy' = Local_Theory.close_target lthy
    val thm' = Morphism.thm (Local_Theory.target_morphism lthy) thm
  in
    (Thm.prop_of thm' |> lhs_of |> Term.head_of, thm', lthy')
  end

(* Define lemmas into the local theory. *)
fun define_lemmas name thm_list lthy =
  let
    val lthy = lthy |> Local_Theory.open_target |> snd
    val ((_, thms), lthy) = Local_Theory.note ((Binding.name name, []), thm_list) lthy
    (*
     * Restore the theory; not entirely sure why this is needed, but prevents
     * definitions from taking O(n^2) time (where "n" is the number of
     * definitions previously made).
     *)
    val lthy' = Local_Theory.close_target lthy
    val thms' = map (Morphism.thm (Local_Theory.target_morphism lthy)) thms
  in
    (thms', lthy')
  end

(* Define a single lemma into the local theory. *)
fun define_lemma name thm lthy =
  let
    val lthy = lthy |> Local_Theory.open_target |> snd
    val (thms, lthy) = define_lemmas name [thm] lthy
    val lthy = Local_Theory.close_target lthy
  in
    (hd thms, lthy)
  end

(* Return an instance of the term "name". *)
fun get_term ctxt name =
  Syntax.read_term ctxt name

(* Calculate a fixpoint. *)
fun fixpoint f eq init =
  let
    val new = f init
  in
    if (eq (new, init)) then init else (fixpoint f eq new)
  end

(*
 * Convenience function for generating types.
 *
 *   gen_typ @{typ "'a + 'b"} [@{typ word32}, @{typ nat}]
 *
 * will generate @{typ "word32 + nat"}
 *)
fun gen_typ t params =
  let
    fun typ_convert (TFree (a, _)) =
        String.extract (a, 1, NONE)
        |> (fn x => ord x - ord "a")
        |> nth params
      | typ_convert x = x
  in
    Term.map_atyps typ_convert t
  end

(* Anonymous variable name for a lambda abstraction. *)
(* TODO this is unused *)
val dummy_abs_name = Name.internal Name.uu

(*
 * Determine if the given term contains the given subterm.
 *)
fun contains_subterm needle haysack =
  exists_subterm (fn a => a = needle) haysack

(*
 * cterm_instantiate with named parameter.
 *
 * (from records package)
 *)
fun named_cterm_instantiate ctxt values thm =
let
  fun match name ((name', _), _) = name = name'
  fun getvar name =
    (case find_first (match name) (Term.add_vars (Thm.prop_of thm) []) of
          SOME var =>  #1 var
        | NONE => raise THM ("named_cterm_instantiate: " ^ name, 0, [thm]));
in
  infer_instantiate ctxt (map (apfst getvar) values) thm
end

(*
 * Fetch all unique schematics in the given term.
 *)
fun get_vars t =
let
  val all_vars = fold_aterms (fn x => fn l =>
    (case x of Var _ => (x :: l) | _ => l)) t []
in
  sort_distinct Term_Ord.fast_term_ord all_vars
end

(*
 * Given a function "f" that returns either SOME cterm or NONE, instantiate
 * every schematic variable in the given function with the result of "f".
 *
 * If NONE is returned, the variable is left as-is.
 *)
fun instantiate_thm_vars ctxt f thm =
let
  (* Fetch all vars. *)
  val all_vars = get_vars (Thm.prop_of thm)

  (* Get instantiations. *)
  val insts = map_filter (fn Var var =>
    Option.map (fn x => (#1 var, x)) (f var)) all_vars
in
  infer_instantiate ctxt insts thm
end

(*
 * Given a list of name/cterm pairs, instantiate schematic variables in the
 * given "thm" with the given name with the cterm values.
 *)
fun instantiate_thm ctxt vars thm =
let
  val dict = Symtab.make vars
in
  instantiate_thm_vars ctxt (fn ((n, _), _) => Symtab.lookup dict n) thm
end

(* Apply a conversion to the n'th argument of a term. If n < 0, count from the end. *)
fun nth_arg_conv n conv c =
let
  val num_args = Drule.strip_comb c |> snd |> length;
  val num_strips = num_args - (if n < 0 then num_args + 1 + n else n);
  val new_conv = fold (fn _ => fn x => Conv.fun_conv x) (replicate num_strips ()) (Conv.arg_conv conv)
in
  new_conv c
end
handle Subscript => Conv.no_conv c

fun lhs_conv cv = Conv.combination_conv (Conv.arg_conv cv) Conv.all_conv;
fun rhs_conv cv = Conv.combination_conv Conv.all_conv cv

(*
 * Unsafe varify.
 *
 * Convert Var's to Free's, avoiding naming colisions.
 *
 * FIXME : Uses of this function are all broken.
 *)
fun unsafe_unvarify term =
let
  fun used_names (Free (x, _)) = [x]
    | used_names (a $ b) = (used_names a) @ (used_names b)
    | used_names (Abs (_, _, x)) = used_names x
    | used_names _ = []
  val term_names = used_names term
in
  map_aterms
    (fn Var ((x, _), T) => Free (singleton (Name.variant_list term_names) x, T)
      | x => x) term
  |> map_types Logic.unvarifyT_global
end

(* Attempt to guess if the given theorem is a "cong" rule. *)
fun is_cong thm =
  case (Thm.concl_of thm) of
       (Const (@{const_name "HOL.Trueprop"}, _) $ (Const (@{const_name "HOL.eq"}, _) $ lhs $ rhs)) =>
         (Term.head_of lhs = Term.head_of rhs)
     | _ => false

(* Given two theorems, attempt to rename bound variables in theorem "new" to
 * use the names in theorem "old". *)
fun thm_restore_names ctxt old_thm new_thm =
let
  fun restore_names old new =
    case (old, new) of
        (Abs (old_name, _, old_body), Abs (_, new_T, new_body)) =>
          Abs (old_name, new_T, restore_names old_body new_body)
      | ((x1 $ y1), (x2 $ y2)) =>
          (restore_names x1 x2 $ restore_names y1 y2)
      | (_, other) => other
  val renamed_prop = restore_names (Thm.prop_of old_thm) (Thm.prop_of new_thm)
in
  Thm.cterm_of ctxt renamed_prop
  |> Goal.init
  |> resolve_tac ctxt [new_thm] 1
  |> Seq.hd
  |> Goal.finish ctxt
end

(*
 * Find the term "term" in the term "body", and pull it out into a lambda
 * function.
 *
 * For instance:
 *
 *   abs_over "x" @{term "cat"} @{term "cat + dog"}
 *
 * would result in the (SOME @{term "%x. x + dog"}).
 *)
fun abs_over varname term body =
  Term.lambda_name (varname, term) (incr_boundvars 1 body)

(*
 * Abstract over a tuple of variables.
 *
 * For example, given the list ["a", "b"] of variables to abstract over, and
 * the term "a + b + c", we will produce "%(a, b). a + b + c" where "a" and "b"
 * have become bound.
 *
 * If the input is a single-element list, this function is equivalent to
 * "abs_over".
 *)
fun abs_over_tuple [] body =
      absdummy @{typ unit} body
  | abs_over_tuple [(var_name, abs_term)] body =
      abs_over var_name abs_term body
  | abs_over_tuple ((var_name, abs_term)::xs) body =
     HOLogic.mk_case_prod (abs_over var_name abs_term (abs_over_tuple xs body))

(*
 * Construct a term with the given args, replacing type variables in "term"
 * with appropriate values.
 *
 * We assume types in "args" are fully fixed and concrete.
 *)
fun mk_term thy term args =
let
  (* Strip off "n" arguments from the given type, returning
   * the type of each of those arguments and the remainder. *)
  fun strip_typ t 0 = ([], t)
    | strip_typ (Type ("fun", [S, T])) n =
       let
         val (rest, base) = strip_typ T (n - 1)
       in
         (S :: rest, base)
       end
    | strip_typ _ _ = raise TERM ("Invalid number of arguments", term :: args)
  val (argT, _) = strip_typ (fastype_of term) (List.length args)

  (* Match arguments types to the input arguments. *)
  val env = fold (Sign.typ_match thy)
      ((map Logic.varifyT_global argT) ~~ (map fastype_of args)) (Vartab.empty)
      handle Type.TYPE_MATCH =>
        raise TERM ("Could not construct constant due to type errors", term :: args)

  (* Apply the type to our constant. *)
  val new_term =
      Envir.subst_term_types env (map_types Logic.varifyT_global term)
      |> map_types Logic.unvarifyT_global
in
  betapplys (new_term, args)
end

(* Put commas between a list of strings. *)
fun commas l =
  map Pretty.str l
  |> Pretty.commas
  |> Pretty.enclose "" ""
  |> Pretty.unformatted_string_of

(* Make a list of conjunctions. *)
fun mk_conj_list [] = @{term "HOL.True"}
  | mk_conj_list [x] = x
  | mk_conj_list (x::xs) = HOLogic.mk_conj (x, (mk_conj_list xs))

(* Destruct a list of conjunctions. *)
fun dest_conj_list (Const (@{const_name "HOL.conj"}, _) $ l $ r)
        = l :: dest_conj_list r
  | dest_conj_list x = [x]

(*
 * Apply the given tactic to the given theorem, providing (brief) diagnostic
 * messages if something goes wrong.
 *)
fun apply_tac (step : string) tac (thm : thm) =
  (tac thm |> Seq.hd) handle Option =>
    raise TERM ("Failed to apply tactic during " ^ quote step, Thm.prems_of thm)

(*
 * A "the" operator that explains what is going wrong.
 *)
fun the' str x =
    (the x) handle Option => error str

(*
 * Map every item in a term from bottom to top. We differ from
 * "map_aterms" because we will visit compound terms, such as
 * "a $ b $ c".
 *)
fun term_map_bot f (Abs (a, t, b)) = f (Abs (a, t, term_map_bot f b))
  | term_map_bot f (a $ b) = f (term_map_bot f a $ term_map_bot f b)
  | term_map_bot f x = f x

(*
 * Map every item in a term from top to bottom. A second parameter is
 * returned by our mapping function "f" which is set to true if we
 * should halt recursion after a particular replacement.
 *)
fun term_map_top' f x =
  (case f x of
    (x, true) => x
  | (Abs (a, t, b), false) => Abs (a, t, term_map_top' f b)
  | ((a $ b), false) => term_map_top' f a $ term_map_top' f b
  | (x, false) => x)
fun term_map_top f x = term_map_top' (fn x => (f x, false)) x

(*
 * Map every item in a term from top to bottom, collecting items
 * in a list along the way.
 *)
fun term_fold_map_top' f x =
  (case f x of
    (l, x, true) => (l, x)
  | (l, Abs (a, t, b), false) =>
    let
      val (new_l, new_t) = term_fold_map_top' f b
    in
      (l @ new_l, Abs (a, t, new_t))
    end
  | (l, (a $ b), false) =>
    let
      val (list_a, new_a) = term_fold_map_top' f a
      val (list_b, new_b) = term_fold_map_top' f b
    in
      (l @ list_a @ list_b, new_a $ new_b)
    end
  | (l, x, false) => (l, x))
fun term_fold_map_top f x =
  term_fold_map_top' (fn x =>
    ((f x, false) |> (fn ((a, b), c) => (a, b, c)))) x

(*
 * Map all levels of the simpset.
 *)
fun simp_map f =
  Context.map_proof (
    Local_Theory.declaration {syntax = false, pervasive = false} (
      K (Simplifier.map_ss f)))
  |> Context.proof_map

(*
 * Add a thm to the simpset.
 *)
fun simp_add thms =
  simp_map (fn ctxt => ctxt addsimps thms)

(*
 * Delete a thm from a simpset.
 *)
fun simp_del thms =
  simp_map (fn ctxt => ctxt delsimps thms)

(*
 * Define a (possibly recursive) set of functions.
 *
 * We take a list of functions. For each function, we have a name, list
 * of arguments, and a body (which is assumed to have a lambda
 * abstraction for each argument).
 *
 * Recursion (and mutual recursion) can be achieved by the body
 * containing a free variable with the name of the function to be called
 * of the correct type.
 *
 * Termination must be able to be automatically proved for recursive
 * function definitions to succeed. This implies that recursive
 * functions must have at least one argument (lest there be no arguments
 * to prove termination on).
 *
 * For example, the input:
 *
 *     [("fact", [("n", @{typ nat}], @{term "%n. if n = 0 then 1 else n * fact (n - 1))})]
 *
 * would define a new function "fact".
 *
 * We return a tuple:
 *
 *   (<list of function definition thms>, <new context>)
 *)
fun define_functions func_defs hidden is_recursive lthy =
let
  fun maybe_hide x = if hidden then Binding.concealed x else x

  (* Define a set of mutually recursive functions. The function package
   * refuses to make a definition that doesn't take any arguments, so we
   * use this strictly for functions with at least one argument. *)
  fun define_recursive_function func_defs lthy =
  let
    (* Automatic pattern completeness / termination methods from
     * the "function" package. *)
    fun pat_completeness_auto ctxt =
      Pat_Completeness.pat_completeness_tac ctxt 1
      THEN auto_tac ctxt
    fun prove_termination lthy =
      Function.prove_termination NONE
        (Function_Common.termination_prover_tac false lthy) lthy

    (* Get the list of function bindings. *)
    val function_bindings = map (fn (name, _, _) =>
        (maybe_hide (Binding.name name), NONE, NoSyn)) func_defs

    (* Get the list of function bodies. *)
    fun mk_fun_term name args body =
    let
      (* Get the type of the function, and generate a free term for it. *)
      val fun_free = Free (name, fastype_of body)

      (* Create a head of the function, with appropriate arguments. *)
      val fun_head = betapplys (fun_free, map Free args)
      val fun_body = betapplys (body, map Free args)
    in
      HOLogic.mk_Trueprop (HOLogic.mk_eq (fun_head, fun_body))
    end
    val function_bodies = map (fn (a,b,c) => mk_fun_term a b c) func_defs

    (* Define the function. *)
    val lthy = lthy |> Local_Theory.open_target |> snd
    val ctxt' = Function.add_function
      function_bindings
      (map (fn x => ((Binding.empty_atts, x), [], [])) function_bodies)
      Function_Common.default_config pat_completeness_auto lthy
      |> snd
      |> Local_Theory.close_target
      |> prove_termination
      |> snd

    (* Frustratingly, the function package doesn't actually hand us back the
     * definition it just created. Instead, we fetch it out of the new context
     * by guessing its name. *)
    val simps_names = map (fn def => #1 def ^ ".simps") func_defs
    val thms = map (Proof_Context.get_thm ctxt') simps_names

    (* Take the functions out of the simpset to avoid unintended unfolding. *)
    val ctxt' = simp_del thms ctxt'
  in
    (map mk_meta_eq thms, ctxt')
  end
in
  case (is_recursive, func_defs) of
      (* Single non-recursive function. *)
      (false, [(name, args, body)]) =>
        define_const_args name hidden (betapplys (body, map Free args)) args lthy
        |> (fn (_, thm, def) => ([thm], def))

    | (true, _) =>
      (* Recursion or mutual recursion. *)
      define_recursive_function func_defs lthy
end

(* Abstract over the given term with a forall constant. *)
fun forall v t = HOLogic.all_const (fastype_of v) $ lambda v t

(* Convert Var's into foralls. *)
fun vars_to_forall term =
   fold (fn p => fn t => forall p t) (get_vars term) term

(* Convert Var's into meta-foralls. *)
fun vars_to_metaforall term =
   fold (fn p => fn t => Logic.all p t) (get_vars term) term

(* Emulate [abs_def] thm attribute. *)
fun abs_def ctxt =
    Drule.export_without_context #> Local_Defs.meta_rewrite_rule ctxt #> Drule.abs_def

(*
 * Create a string from a template and a set of values.
 *
 * Template variables are of the form "%n" where "n" is a number between 0 and
 * 9, indicating the value to substitute in.
 *
 * For example, the template "moo %0 cow %1" with the values ["cat", "dog"]
 * would genereate "moo cat cow dog".
 *)
fun subs_template template vals =
let
  fun subs_template' vals (#"%"::v::xs) =
        (nth vals ((Char.ord v) - (Char.ord #"0"))) @ subs_template' vals xs
    | subs_template' vals (v::xs) = v :: (subs_template' vals xs)
    | subs_template' _ [] = []
in
  subs_template' (map String.explode vals) (String.explode template)
  |> String.implode
end

(* Prove a set of rules, giving them the given names. *)
fun prove_rules name lemmas tac lthy =
let
  val thms = map (fn txt =>
    Syntax.read_prop lthy txt
    |> Syntax.check_term lthy
    |> (fn x => Goal.prove lthy [] [] x (K tac))
    |> Thm.forall_intr_frees
    ) lemmas
in
  Local_Theory.note ((Binding.name name, []), thms) lthy |> snd
end

(* Prove a rule from the given string, giving it the given name. *)
fun prove_rule name lemma tac lthy =
  prove_rules name [lemma] tac lthy

(* Simple invocation of metis. *)
val metis_tac = Metis_Tactic.metis_tac
        ATP_Proof_Reconstruct.partial_type_encs
        ATP_Proof_Reconstruct.default_metis_lam_trans
fun metis_insert_tac ctxt rules =
  (Method.insert_tac ctxt rules) THEN' (metis_tac ctxt [])

(*
 * Decoding and parsing Isabelle terms into ML terms.
 *)

(* Decode a list. *)
fun decode_isa_list t =
  HOLogic.dest_list t handle TERM _ => invalid_term "isabelle list" t

(* Encode a list. *)
fun encode_isa_list T xs = HOLogic.mk_list T xs

(* Decode a chracter. *)
fun decode_isa_char t =
  Char.chr (HOLogic.dest_char t) handle TERM _ => invalid_term "isabelle char" t

(* Encode a character. *)
fun encode_isa_char t = HOLogic.mk_char (Char.ord t)

(* Decode a string. *)
fun decode_isa_string t =
  decode_isa_list t
  |> map decode_isa_char
  |> String.implode

(* Encode a string. *)
fun encode_isa_string s =
  String.explode s
  |> map encode_isa_char
  |> encode_isa_list @{typ char}

(* Transform an ML list of strings into an isabelle list of strings. *)
fun ml_str_list_to_isa s =
  map encode_isa_string s
  |> encode_isa_list @{typ "string"}

(* Transform an isabelle list of strings into an ML list of strings. *)
fun isa_str_list_to_ml t =
  decode_isa_list t
  |> map decode_isa_string

(*
 * Chain a series of state-predicates together.
 *
 * Each input has the form "%s. P s", where "s" is of type "stateT".
 *)
fun chain_preds stateT [] = Abs ("s", stateT, @{term "HOL.True"})
  | chain_preds     _ [x] = x
  | chain_preds stateT (x::xs) =
      Const (@{const_name "pred_conj"},
          (stateT --> @{typ bool}) --> (stateT --> @{typ bool}) --> (stateT --> @{typ bool}))
        $ x $ (chain_preds stateT xs)

(*
 * Given a term of the form "Abs (a, T, x)" and a function "f" that processes a
 * term into another, feed the term "x" to "f" such that bound variables are
 * replaced with free variables, and then abstracted out again once "f" is
 * complete.
 *
 * For example, if we are called with:
 *
 *   concrete_abs f (Abs ("x", @{typ nat}, Bound 0))
 *
 * then "f" will be given "Free ("x", @{typ nat})", and such instances of this
 * free variable will be abstracted out again once "f" is complete.
 *
 * The variant "concrete_abs'" does not perform the abstraction step, but
 * instead returns the Free variable used.
 *)
fun concrete_abs' ctxt t =
let
  fun get_lambda_name (Abs (n, _, _)) = n
    | get_lambda_name _ = "x"
  val first_argT = domain_type (fastype_of t)
  val [(n', _)] = Variable.variant_frees ctxt [t] [(get_lambda_name t, ())]
  val free = Free (n', first_argT)
in
  ((betapply (t, free)), free, n')
end
fun concrete_abs ctxt f t =
let
  val (term, free, name) = concrete_abs' ctxt t
in
  f term |>> abs_over name free
end

(*
 * Given a definition "thm" of the form:
 *
 *    x a b c == a + b + c
 *
 * return the "thm" with arguments instantiated.
 *)
fun inst_args ctxt vals thm =
let
  (* Fetch schematic variables on the LHS, stripping away locale assumptions
   * and locale fixed variables first. *)
  val vars = Thm.cprop_of thm
    |> Drule.strip_imp_concl
    |> clhs_of
    |> Drule.strip_comb
    |> snd
    |> filter (Thm.term_of #> is_Var)
    |> map (#1 o dest_Var o Thm.term_of)
in
  Drule.infer_instantiate ctxt ((take (length vals) vars) ~~ vals) thm
end

(*
 * A tactic like "rtac", but only performs first-order matching.
 *)
fun first_order_rule_tac thm n goal_thm =
let
  val thy = Thm.theory_of_thm goal_thm
  val ctxt = Proof_Context.init_global thy

  (* First-order match "thm" against the n'th premise of our goal. *)
  val thm_term = Thm.concl_of thm
  val goal_term = Logic.nth_prem (n, Thm.prop_of goal_thm)
  val tenv = Pattern.first_order_match thy (thm_term, goal_term)
      (Vartab.empty, Vartab.empty) |> snd

  (* Instantiate "thm" with the matched values. *)
  val inst = map (fn (var_name, (var_type, value)) =>
        (var_name, Thm.cterm_of ctxt value))
      (Vartab.dest tenv)
  val new_thm = infer_instantiate ctxt inst thm
in
  resolve_tac ctxt [new_thm] n goal_thm
end
handle Pattern.MATCH => Seq.empty

(*
 * Unfold all instances of the given theorem once, but don't
 * recursively unfold.
 *)
fun unfold_once_tac ctxt thm =
  CONVERSION (Conv.bottom_conv (K (Conv.try_conv (Conv.rewr_conv thm))) ctxt)

(* Set a simpset as being hidden, so warnings are not printed from it. *)
fun set_hidden_ctxt ctxt =
  Context_Position.set_visible false ctxt

(*
 * Get all facts currently defined.
 *
 * Clagged from "Find_Theorems.all_facts_of".
 *)
fun all_facts_of ctxt =
  let
    val local_facts = Proof_Context.facts_of ctxt;
    val global_facts = Global_Theory.facts_of (Proof_Context.theory_of ctxt);
  in
    maps Facts.selections
     (Facts.dest_static false [global_facts] local_facts @
      Facts.dest_static false [] global_facts)
  end;

(* Guess the name of a thm. *)
fun guess_thm_name ctxt thm =
  List.find (fn x => Thm.eq_thm (thm, snd x)) (all_facts_of ctxt)
  |> Option.map (fst #> Facts.string_of_ref)

(* Expand type abbreviations. *)
fun expand_type_abbrevs ctxt t = Thm.typ_of (Thm.ctyp_of ctxt t)

(*
 * Instantiate the schematics in a thm from the given environment.
 *)
fun instantiate_normalize_from_env ctxt env =
let
  fun prep_type (x, (S, ty)) =
    ((x,S), Thm.ctyp_of ctxt ty)
  fun prep_term (x, (T, t)) =
    ((x,T), Thm.cterm_of ctxt t)
  val term_vals = Vartab.dest (Envir.term_env env)
  val typ_vals = Vartab.dest (Envir.type_env env)
in
  (Drule.instantiate_normalize
      (map prep_type typ_vals, map prep_term term_vals))
end

(*
 * A conversion with behaviour similar to "apply subst".
 *
 * In particular, it can apply a rewrite rule of the form:
 *
 *   ?A + ?A == f
 *
 * whereas "rewrite_conv" and friends will fail because of the reuse of
 * the schematic ?A on the left-hand-side.
 *)
fun subst_conv_raw ctxt thm ct =
let
  val thy = Proof_Context.theory_of ctxt
  val lhs = lhs_of (Thm.concl_of thm)

  (* Determine if the types match. *)
  val maybe_match =
    (Sign.typ_unify thy (fastype_of lhs, fastype_of (Thm.term_of ct)) (Vartab.empty, 0); true)
    handle Type.TUNIFY => false
  val maybe_match2 =
    (Type.raw_unify  (fastype_of lhs, fastype_of (Thm.term_of ct)) (Vartab.empty); true)
    handle Type.TUNIFY => false

  val _ = if maybe_match <> maybe_match2 then
       raise CTERM ("bub", [ct]) else ()

  (* If so, attempt to unify. *)
  val env =
    if maybe_match then
      Unify.matchers (Context.Proof ctxt) [(lhs, Thm.term_of ct)]
      handle ListPair.UnequalLengths => Seq.empty
           | Term.TERM _ => Seq.empty
    else
      Seq.empty
in
  case Seq.pull env of
    NONE =>
      Conv.no_conv ct
  | SOME (env, _) =>
      Conv.rewr_conv (instantiate_normalize_from_env ctxt env thm) ct
end
fun subst_conv ctxt thm =
  (Thm.eta_conversion
      then_conv subst_conv_raw ctxt (Drule.eta_contraction_rule thm))

(* A conversion to wade through any Isabelle/Pure or Isabelle/HOL
 * logical gunf. *)
fun remove_meta_conv conv ctxt ct =
  (case Thm.term_of ct of
    Const (@{const_name "Pure.all"}, _) $ Abs _ =>
      Conv.arg_conv (Conv.abs_conv (fn (_, ctxt) =>
          remove_meta_conv conv ctxt) ctxt) ct
  | Const (@{const_name "Trueprop"}, _) $ _ =>
      Conv.arg_conv (remove_meta_conv conv ctxt) ct
  | _ =>
     conv ctxt ct
  )

(*
 * When executing inside a context, execute the function "f" outside the
 * context, importing the results back in.
 *
 * For example:
 *
 *    exec_background_result (define_const "three" @{term "3 :: nat"}) lthy
 *
 * will define the constant "three" outside of the current locale.
 *)
fun exec_background_result f =
  let val f' = apsnd Local_Theory.exit_global o f o Named_Target.theory_init
  in Local_Theory.background_theory_result f' end

fun exec_background f lthy =
  exec_background_result (fn lthy => ((), f lthy)) lthy
  |> snd

(* Messages for non-critical errors. *)
val keep_going_instruction =
  "\nPlease notify the AutoCorres maintainers of this failure. " ^
  "In the meantime, use \"autocorres [keep_going]\" to ignore the failure."
val keep_going_info =
  "\nIgnoring this error because keep_going is enabled."

(* Raise exceptions unless keep_going is set. *)
fun TERM_non_critical keep_going msg term =
  if keep_going then warning (msg ^ keep_going_info)
  else raise TERM (msg ^ keep_going_instruction, term)

fun CTERM_non_critical keep_going msg ct =
  if keep_going then warning (msg ^ keep_going_info)
  else raise CTERM (msg ^ keep_going_instruction, ct)

fun THM_non_critical keep_going msg n thm =
  if keep_going then warning (msg ^ keep_going_info)
  else raise THM (msg ^ keep_going_instruction, n, thm)

(* Perform a "Method.trace" on the given list of thms if the given tactic
 * succeeds. *)
fun trace_rule ctxt goal rule =
  if Config.get ctxt Method.rule_trace then
  let
    val _ = Goal_Display.string_of_goal ctxt goal |> tracing
    val _ = (case guess_thm_name ctxt rule of
        SOME x => Pretty.str x
      | NONE => Thm.pretty_thm_item ctxt rule)
      |> Pretty.string_of |> tracing
  in
    ()
  end
  else ();

(* Apply the given tactic. If successful, trace the given "thm" and current
 * goal state. *)
fun trace_if_success ctxt thm tac goal =
  (tac THEN (fn y => (trace_rule ctxt goal thm; all_tac y))) goal

(* Get the type a pointer points to. *)
fun dest_ptrT T = dest_Type T |> snd |> hd
fun mk_ptrT T = Type (@{type_name "ptr"}, [T])

(* Get / dest an option type. *)
fun dest_optionT (Type ("Option.option", [x])) = x
fun mk_optionT T = Type (@{type_name "option"}, [T])

(* Construct other terms. *)
fun mk_the T t = Const (@{const_name "the"}, mk_optionT T --> T) $ t
fun mk_Some T t = Const (@{const_name "Some"}, T --> mk_optionT T) $ t
fun mk_fun_upd rangeT domT f src dest =
  Const (@{const_name "fun_upd"}, (rangeT --> domT) --> rangeT --> domT --> rangeT --> domT)
    $ f $ src $ dest
fun mk_bool true = @{term True}
  | mk_bool false = @{term False}

(* Succeed only if there are no subgoals. *)
fun solved_tac thm =
  if Thm.nprems_of thm = 0 then Seq.single thm else Seq.empty

(* Convenience function for making simprocs. *)
fun mk_simproc' ctxt (name : string, pats : string list, proc : Proof.context -> cterm -> thm option) = let
  in Simplifier.make_simproc ctxt name
       {lhss = map (Proof_Context.read_term_pattern ctxt) pats,
        proc = K proc} end

(* Get named_theorems in reverse order. We use this for translation rulesets
 * so that user-added rules can override the built-in ones. *)
fun get_rules ctxt = Named_Theorems.get ctxt #> rev

(* As Substring.position but searches from the end *)
fun positionr pat s = let
  val (s0, begin0, size0) = Substring.base s
  fun search i = if i < begin0 then
                   (s, Substring.substring (s0, begin0 + size0, 0)) (* not found *)
                 else if Substring.isPrefix pat (Substring.substring (s0, i, size0 - i)) then
                   (Substring.substring (s0, begin0, i), (* found *)
                    Substring.substring (s0, begin0 + i, size0 - i))
                 else search (i - 1)
  in search size0 end
val _ = assert (apply2 Substring.string (positionr "br" (Substring.full "abracadabra"))
                 = ("abracada", "bra")) ""
val _ = assert (apply2 Substring.string (positionr "xx" (Substring.full "abracadabra"))
                 = ("abracadabra", "")) ""

(* Merge a list of Symtabs. *)
fun symtab_merge allow_dups tabs =
      maps Symtab.dest tabs
      |> (if allow_dups then sort_distinct (fast_string_ord o apply2 fst) else I)
      |> Symtab.make;

(* Merge with custom merge operation. *)
fun symtab_merge_with merge (tab1, tab2) =
  sort_distinct fast_string_ord (Symtab.keys tab1 @ Symtab.keys tab2)
  |> map (fn k => (k, case (Symtab.lookup tab1 k, Symtab.lookup tab2 k) of
                          (SOME x1, SOME x2) => merge (x1, x2)
                        | (SOME x1, NONE) => x1
                        | (NONE, SOME x2) => x2
                        (* (NONE, NONE) impossible *)))
  |> Symtab.make

end (* structure Utils *)


(*
 * Future sequence.
 * This is similar to seq except that values are computed eagerly and then cached.
 * See AutoCorresUtil for an overview of how this is used in AutoCorres.
 *)
signature FSEQ = sig
  type 'a fseq;

  (* Standard list operations *)
  val empty: unit -> 'a fseq;
  val mk: (unit -> ('a * 'a fseq) option) -> 'a fseq;
  val cons: 'a -> 'a fseq -> 'a fseq;
  val fcons: (unit -> 'a * 'a fseq) -> 'a fseq;
  val uncons: 'a fseq -> ('a * 'a fseq) option;
  val null: 'a fseq -> bool;
  val hd: 'a fseq -> 'a;
  val tl: 'a fseq -> 'a fseq;

  val append: 'a fseq -> 'a fseq -> 'a fseq;
  val map: ('a -> 'b) -> 'a fseq -> 'b fseq;
  val fold_map: ('acc -> 'a -> 'b * 'acc) -> 'acc -> 'a fseq -> 'b fseq;

  val of_list: 'a list -> 'a fseq;
  val list_of: 'a fseq -> 'a list;

  (* Only waits on the shortest prefix of the sequence that contains
   * a matching value. We rely on this to maximise parallelism
   * between conversions. *)
  val find: ('a -> bool) -> 'a fseq -> 'a option;
end;

structure FSeq : FSEQ = struct
  datatype 'a fseq_base = fseqNil
                        | fseqCons of 'a * 'a fseq_base future;
  type 'a fseq = 'a fseq_base future;

  fun empty () = Future.value fseqNil;
  fun mk f =
        Future.fork (fn _ =>
            case f () of NONE => fseqNil
                       | SOME x => fseqCons x);
  fun fcons f = mk (fn _ => SOME (f ()));
  fun cons x xs = Future.value (fseqCons (x, xs));
  fun uncons xs =
      case Future.join xs of
          fseqNil => NONE
        | fseqCons p => SOME p;
  fun null xs = not (isSome (uncons xs));
  fun hd xs = fst (the (uncons xs));
  fun tl xs = snd (the (uncons xs));

  fun append xs ys =
      xs |> Future.map (fn x =>
              case x of fseqNil => Future.join ys
                      | fseqCons (x, xs') => fseqCons (x, append xs' ys));
  fun map f xs =
      Future.fork (fn () =>
          case Future.join xs of
              fseqNil => fseqNil
            | fseqCons (x, xs') => fseqCons (f x, map f xs'));
  fun fold_map f acc xs =
      Future.fork (fn () =>
          case Future.join xs of
              fseqNil => fseqNil
            | fseqCons (x, xs') =>
                let val (x', acc') = f acc x;
                in fseqCons (x', fold_map f acc' xs') end);

  fun of_list [] = empty ()
    | of_list (x::xs) = cons x (of_list xs);
  fun list_of xs =
        case Future.join xs of
            fseqNil => []
          | fseqCons (x, xs') => x :: list_of xs';

  fun find P xs =
        case Future.join xs of
            fseqNil => NONE
          | fseqCons (x, xs') => if P x then SOME x else find P xs';
end;

(* Memoization using a serialized cache. *)
signature Memo = sig
  type arg;
  val memo: (arg -> 'a) -> (arg -> 'a);
end;

functor Memo(Table: TABLE) = struct
  type arg = Table.key;
  fun memo f = let
    val table = Synchronized.var "" Table.empty;
    in fn a =>
         Synchronized.change_result table (fn tab =>
             case Table.lookup tab a of
                 SOME r => (r, tab)
               | NONE => let
                   val r = f a;
                   in (r, Table.update (a, r) tab) end)
    end;
end;
structure String_Memo = Memo(Symtab);

(* Insist the the given tactic solves a subgoal. *)
fun SOLVES tac = (((K tac) THEN_ALL_NEW (K no_tac)) 1)

(* Given a list of tactics, try them all, backtracking when necessary. *)
fun APPEND_LIST tacs = fold_rev (curry op APPEND) tacs no_tac;
