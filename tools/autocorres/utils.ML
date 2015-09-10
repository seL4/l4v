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
 *)
structure Utils =
struct

(*
 * Catch-all for invalid inputs: Instead of raising MATCH, describe what
 * the invalid input was.
 *)
exception InvalidInput of string;
fun invalid_typ s (t : typ) =
    raise InvalidInput ("Expected " ^ s ^ ", but got '" ^ (PolyML.makestring t) ^ "'")
fun invalid_term s (t : term) =
    raise InvalidInput ("Expected " ^ s ^ ", but got '" ^ (PolyML.makestring t) ^ "'")
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
    raise CTERM ("Argument " ^ (PolyML.makestring n) ^ " doesn't exist", [ct])
fun term_nth_arg t n =
  (Term.strip_comb t |> snd |> (fn x => nth x n))
  handle Subscript =>
    raise TERM ("Argument " ^ (PolyML.makestring n) ^ " doesn't exist", [t])

(* Convert a term into a string. *)
fun term_to_string ctxt t =
  Syntax.check_term ctxt t
  |> Thm.cterm_of ctxt
  |> PolyML.makestring

(* Warning with 'autocorres' prefix. *)
fun ac_warning str = warning ("autocorres: " ^ str)

(* List functions that should really be included in PolyML. *)

fun zipWith _ [] _ = []
  | zipWith _ _ [] = []
  | zipWith f (x::xs) (y::ys) = f x y :: zipWith f xs ys
fun zip xs ys = zipWith (fn x => fn y => (x, y)) xs ys
fun zip3 [] [] [] = []
    | zip3 (x::xs) (y::ys) (z::zs) = ((x,y,z)::(zip3 xs ys zs))

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

(* Define a constant "name" of type "term" into the local theory "lthy". *)
fun define_const name term lthy =
  let
    val ((_, (_, thm)), lthy) = Local_Theory.define ((Binding.name name, NoSyn), (Attrib.empty_binding, term)) lthy
    val lthy' = Local_Theory.restore lthy
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
    val ((_, (_, thm)), lthy) =
        Specification.definition ((SOME (maybe_hide (Binding.name name), NONE, NoSyn)),
            (Attrib.empty_binding, new_term)) lthy

    (* Integrate into the current locale. *)
    val lthy' = Local_Theory.restore lthy
    val thm' = Morphism.thm (Local_Theory.target_morphism lthy) thm
  in
    (Thm.prop_of thm' |> lhs_of |> Term.head_of, thm', lthy')
  end

(* Define lemmas into the local theory. *)
fun define_lemmas name thm_list lthy =
  let
    val ((_, thms), lthy) = Local_Theory.note ((Binding.name name, []), thm_list) lthy
    (*
     * Restore the theory; not entirely sure why this is needed, but prevents
     * definitions from taking O(n^2) time (where "n" is the number of
     * definitions previously made).
     *)
    val lthy' = Local_Theory.restore lthy
    val thms' = map (Morphism.thm (Local_Theory.target_morphism lthy)) thms
  in
    (thms', lthy')
  end

(* Define a single lemma into the local theory. *)
fun define_lemma name thm lthy =
  let
    val (thms, lthy) = define_lemmas name [thm] lthy
    val lthy = Local_Theory.restore lthy
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
fun named_cterm_instantiate values thm =
let
  fun match name ((name', _), _) = name = name'
  fun getvar name =
    (case find_first (match name) (Term.add_vars (Thm.prop_of thm) []) of
          SOME var => Thm.cterm_of (Proof_Context.init_global (Thm.theory_of_thm thm)) (Var var)
        | NONE => raise THM ("named_cterm_instantiate: " ^ name, 0, [thm]));
in
  cterm_instantiate (map (apfst getvar) values) thm
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
    Option.map (fn x => (Thm.cterm_of ctxt (Var var), x)) (f var)) all_vars
in
  cterm_instantiate insts thm
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
  |> rtac new_thm 1
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
     HOLogic.mk_split (abs_over var_name abs_term (abs_over_tuple xs body))

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
  |> Pretty.str_of

(* Make a list of conjunctions. *)
fun mk_conj_list [] = @{term "HOL.True"}
  | mk_conj_list [x] = x
  | mk_conj_list (x::xs) = HOLogic.mk_conj (x, (mk_conj_list xs))

(* Destruct a list of conjunctions. *)
fun dest_conj_list (Const (@{const_name "HOL.conj"}, _) $ l $ r)
        = dest_conj_list l @ dest_conj_list r
  | dest_conj_list x = [x]

(*
 * Apply the given tactic to the given theorem, providing (brief) diagnostic
 * messages if something goes wrong.
 *)
fun apply_tac (step : string) tac (thm : thm) =
  (tac thm |> Seq.hd) handle Option =>
    error ("Failed to apply tactic during '" ^ step ^ "': " ^ (
        (PolyML.makestring (cprems_of thm))))

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
        (Function_Common.termination_prover_tac lthy) lthy

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
    val ctxt' = Function.add_function
      function_bindings
      (map (fn x => (Attrib.empty_binding, x)) function_bodies)
      Function_Common.default_config pat_completeness_auto lthy
      |> snd
      |> Local_Theory.restore
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
  (Method.insert_tac rules) THEN' (metis_tac ctxt [])

(*
 * Decoding and parsing Isabelle terms into ML terms.
 *)

(* Decode a Nibble. *)
fun decode_isa_nibble t =
  case t of
    (Const (@{const_name "Nibble0"}, _)) => 0
  | (Const (@{const_name "Nibble1"}, _)) => 1
  | (Const (@{const_name "Nibble2"}, _)) => 2
  | (Const (@{const_name "Nibble3"}, _)) => 3
  | (Const (@{const_name "Nibble4"}, _)) => 4
  | (Const (@{const_name "Nibble5"}, _)) => 5
  | (Const (@{const_name "Nibble6"}, _)) => 6
  | (Const (@{const_name "Nibble7"}, _)) => 7
  | (Const (@{const_name "Nibble8"}, _)) => 8
  | (Const (@{const_name "Nibble9"}, _)) => 9
  | (Const (@{const_name "NibbleA"}, _)) => 10
  | (Const (@{const_name "NibbleB"}, _)) => 11
  | (Const (@{const_name "NibbleC"}, _)) => 12
  | (Const (@{const_name "NibbleD"}, _)) => 13
  | (Const (@{const_name "NibbleE"}, _)) => 14
  | (Const (@{const_name "NibbleF"}, _)) => 15
  | _ => invalid_term "Nibble constant" t

(* Encode a nibble. *)
fun encode_isa_nibble t =
  case t of
    0  => @{term "Nibble0"}
  | 1  => @{term "Nibble1"}
  | 2  => @{term "Nibble2"}
  | 3  => @{term "Nibble3"}
  | 4  => @{term "Nibble4"}
  | 5  => @{term "Nibble5"}
  | 6  => @{term "Nibble6"}
  | 7  => @{term "Nibble7"}
  | 8  => @{term "Nibble8"}
  | 9  => @{term "Nibble9"}
  | 10 => @{term "NibbleA"}
  | 11 => @{term "NibbleB"}
  | 12 => @{term "NibbleC"}
  | 13 => @{term "NibbleD"}
  | 14 => @{term "NibbleE"}
  | 15 => @{term "NibbleF"}
  | _ => invalid_input "Number from 1--15" (PolyML.makestring t)

(* Decode a list. *)
fun decode_isa_list t =
  case t of
    (Const (@{const_name "list.Cons"}, _) $ x $ xs) => (x :: decode_isa_list xs)
  | (Const (@{const_name "list.Nil"}, _)) => []
  | _ => invalid_term "isabelle list" t

(* Encode a list. *)
fun encode_isa_list T [] =
      (@{mk_term "[] :: ?'a list" ('a)} T)
  | encode_isa_list T (x::xs) =
      (@{mk_term "?x # ?xs" (x, xs)} (x, encode_isa_list T xs))

(* Decode a chracter. *)
fun decode_isa_char t =
  case t of
    (Const (@{const_name "char.Char"}, _) $ a $ b) =>
      Char.chr (decode_isa_nibble a * 16 + decode_isa_nibble b)
  | _ => invalid_term "isabelle char" t

(* Encode a character. *)
fun encode_isa_char t =
  @{mk_term "Char ?a ?b" (a, b)} (
    encode_isa_nibble (Char.ord t div 16), encode_isa_nibble (Char.ord t mod 16))

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
 * Given a term of the form "%(a, b, c). X a b c" send the function
 * "f" the term with the abstracted variables converted into concrete
 * free variables.
 *
 * This is like "concrete_abs", but supports "case_prod.
 *)
fun concrete_split' ctxt t =
let
  fun do_split (Const (@{const_name "case_prod"}, _) $ t) =
    let
      (* Abstract the first variable in the split... *)
      val (new_term, free, name) = concrete_abs' ctxt t

      (* Recursively abstract the rest. *)
      val (final_term, rest) = do_split new_term
    in
      (final_term, (free, name) :: rest)
    end
    | do_split t =
    let
      (* Abstract the final variable in a split. *)
      val (new_term, free, name) = concrete_abs' ctxt t
    in
      (new_term, [(free, name)])
    end
in
  do_split t
end
fun concrete_split ctxt f t =
let
  val ((new_t, r), free_vars) = concrete_split' ctxt t |>> f
in
  (abs_over_tuple (map (fn (x, y) => (y, x)) free_vars) new_t, r)
end

(*
 * Given a definition "thm" of the form:
 *
 *    x a b c == a + b + c
 *
 * return the "thm" with arguments instantiated.
 *)
fun inst_args vals thm =
let
  (* Fetch schematic variables on the LHS, stripping away locale assumptions
   * and locale fixed variables first. *)
  val vars = Thm.cprop_of thm
    |> Drule.strip_imp_concl
    |> clhs_of
    |> Drule.strip_comb
    |> snd
    |> filter (Thm.term_of #> is_Var)
in
  Drule.cterm_instantiate ((take (length vals) vars) ~~ vals) thm
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
        (Thm.cterm_of ctxt (Var (var_name, var_type)), Thm.cterm_of ctxt value))
      (Vartab.dest tenv)
  val new_thm = cterm_instantiate inst thm
in
  rtac new_thm n goal_thm
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

(*
 * Declare a constant (without any definition) in the local theory.
 * Currently used to declare termination measures of recursive functions.
 * The constant is added to the lthy and also to a symbol table.
*)
fun declare_constant (symtab_name, const_name, const_typ) (consts_symtab, lthy) =
let
  val bind = ((Binding.name const_name, const_typ), NoSyn)
  fun add_const thy = Sign.declare_const lthy bind thy
  val (const_term, lthy') = Local_Theory.raw_theory_result add_const lthy
in
  (Symtab.update_new (symtab_name, const_term) consts_symtab, lthy')
end

(*
 * Define a previously-declared constant in the local theory.
 * Its definition is added to the lthy and also to a symbol table.
 *)
fun define_constant (symtab_name, thm_name, const_name, const_def) (defs_symtab, lthy) =
let
  val const_def' = Primitive_Defs.dest_def lthy Term.is_Const
                                           (K false) (K false) const_def
                   |> snd
  fun def_const thy = Thm.add_def lthy true true (Binding.name const_name, const_def') thy
  val ((_, thm), lthy) = Local_Theory.raw_theory_result def_const lthy
  val (_, lthy') = define_lemma thm_name thm lthy
in
  (Symtab.update_new (symtab_name, thm) defs_symtab, lthy')
end

(* Expand type abbreviations. *)
fun expand_type_abbrevs ctxt t = Thm.typ_of (Thm.ctyp_of ctxt t)

(*
 * Instantiate the schematics in a thm from the given environment.
 *)
fun instantiate_normalize_from_env ctxt env =
let
  fun prep_type (x, (S, ty)) =
    (Thm.ctyp_of ctxt (TVar (x, S)), Thm.ctyp_of ctxt ty)
  fun prep_term (x, (T, t)) =
    (Thm.cterm_of ctxt (Var (x, T)), Thm.cterm_of ctxt t)
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

(* Assert no flex flex pairs in the given theorem. *)
fun no_flexflex_tac thm =
  if not (null (#tpairs (Thm.rep_thm thm))) then
    (raise THM ("Flex-flex pairs in goal", 1, [thm]))
  else
    all_tac thm

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
      | NONE => Display.pretty_thm_item ctxt rule)
      |> Pretty.string_of |> tracing
  in
    ()
  end
  else ();

(* Apply the given tactic. If successful, trace the given "thm" and current
 * goal state. *)
fun trace_if_success ctxt thm tac goal =
  (tac THEN (fn y => (trace_rule ctxt goal thm; all_tac y))) goal


end

(* Shortcut for "named_cterm_instantiate". *)
infix 0 WHERE;
fun a WHERE b = Utils.named_cterm_instantiate b a;

(* Insist the the given tactic solves a subgoal. *)
fun SOLVES tac = (((K tac) THEN_ALL_NEW (K no_tac)) 1)

(* Given a list of tactics, try them all, backtracking when necessary. *)
fun APPEND_LIST tacs = fold_rev (curry op APPEND) tacs no_tac;

(* Version of "OF'" where an arbitrary resolution is taken in the event that
 * multiple exist. *)
infix 0 OF'
fun op OF' (b, a) =
let
  fun aux_of b [] = Seq.single b
    | aux_of b (x::xs) = Seq.maps (fn b => aux_of b xs)
        (Thm.biresolution NONE false [(false, x)] 1 b)
  val result = aux_of b a
    |> Seq.list_of
    |> distinct Thm.eq_thm
in
  case result of
    [] => raise THM ("No unifiers", 0, b :: a)
  | [x] => x
  | (x::xs) => (warning ("Multiple unifiers! Arbitrarily selecting the first. "
      ^ (PolyML.makestring (x::xs))); x)
end

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

(* Succeed only if there are no subgoals. *)
fun solved_tac thm =
  if Thm.nprems_of thm = 0 then Seq.single thm else Seq.empty
