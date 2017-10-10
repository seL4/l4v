(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

signature ISAR_KEY_VALUE =
sig
    val name_ty      : typ
    val intname_to_term : int -> term

    val ord_ty       : typ
    val ord_term     : term

    val ordsimps    : simpset
end;

signature STATIC_FUN =
sig
    val define_tree_and_thms : string -> ((term option * thm) * string) list
                               -> local_theory -> (bstring * thm list) list * local_theory

    val prove_tree_lemmata : Proof.context -> thm -> thm list

    (* Allows testing *)
    val add_defs : (string * term) list -> local_theory -> thm list * local_theory
    val intname_to_term : int -> term
end

functor SFun (KeyVal : ISAR_KEY_VALUE) :> STATIC_FUN =
struct

val alpha        = TFree ("'a", ["HOL.type"])
val beta         = TFree ("'b", ["HOL.type"])
val gamma        = TFree ("'c", ["Orderings.linorder"])

val intname_to_term  = KeyVal.intname_to_term

(* Actually build the tree -- theta (n lg(n)) *)
fun build_tree' mk_node mk_leaf xs n = if n = 0
                       then mk_leaf
                       else (let
                                 val n' = n div 2
                                 val xs' = List.drop (xs, n' + 1)
                                 val (a, b) = nth xs n'
                             in (* The second term accounts for floor in div *)
                                 mk_node a b (build_tree' mk_node mk_leaf xs n')
                                         (build_tree' mk_node mk_leaf xs' (n - n' - 1))
                             end)

fun build_tree xs =
    let
        val val_ty = type_of (snd (hd xs)) (* PARTIAL!! *)
        val ty_substs =
            [(alpha, KeyVal.name_ty), (beta, val_ty),
             (gamma, KeyVal.ord_ty)
            ]
        val subst  = subst_atomic_types ty_substs
        val node   = subst @{term "StaticFun.Node"}
        val mk_leaf = subst @{term "StaticFun.Leaf"}
        val lookup_tree = subst @{term "StaticFun.lookup_tree"}
        fun mk_node a b l r = node $ a $ b $ l $ r
    in
        lookup_tree $ (build_tree' mk_node mk_leaf xs (length xs)) $ KeyVal.ord_term
    end

fun add_defs defs lthy : thm list * local_theory = let
  fun mk1 ((name, rhs), (xs, lthy)) = let
    val b = Binding.make(name, Position.none)
    val ((_, (_, d)), lthy') =
        Local_Theory.define ((b, NoSyn), ((Thm.def_binding b, []), rhs)) lthy
  in
    (d :: xs, lthy')
  end
  val (xs, lthy') = List.foldl mk1 ([], lthy) defs
in
  (rev xs, lthy')
end

fun add_def def = add_defs [def] #>> hd

fun define_tree name xs thy : thm * local_theory =
    let
        val tree        = build_tree xs
    in
        add_def (name, tree) thy
    end

val mydk   = nth @{thms tree_gives_valsD} 0
val mydl   = nth @{thms tree_gives_valsD} 1
val mydr   = nth @{thms tree_gives_valsD} 2
val mycg   = @{thm tree_gives_vals_setonly_cong}
val mysets = @{thms tree_vals_set_simps}

val simpset =
    Simplifier.put_simpset KeyVal.ordsimps @{context}
    |> (fn ctxt => ctxt addsimps mysets)
    |> Simplifier.add_cong mycg
    |> simpset_of

fun make_tree_lemma _ [] = []
  | make_tree_lemma ctxt thms =
    let
      val mapsimp = map (simplify (put_simpset simpset ctxt))
      val left    = mapsimp (thms RL [mydl])
      val right   = mapsimp (thms RL [mydr])
      val rule    = mapsimp (thms RL [mydk])
    in
      (* Add rule to theory *)
      make_tree_lemma ctxt left @ rule @ make_tree_lemma ctxt right
    end

fun prove_tree_lemmata ctxt tree_def
    = make_tree_lemma ctxt [tree_def RS @{thm tree_gives_valsI}]

val zip = curry (op ~~)

fun make_lemmas tree_def defs (ctxt : Proof.context) =
    let
    in
        prove_tree_lemmata ctxt tree_def
                |> zip defs
                |> map (fn (d, t) => Local_Defs.fold ctxt [d] t)
    end

fun add_thms lthy names thms = let
  fun mk1 (n, t) = ((Binding.make(n,Position.none), []), [([t],[])])
in
  Local_Theory.notes (ListPair.map mk1 (names,thms)) lthy
end

fun map_option f [] = []
  | map_option f (x :: xs) =
    let val rest = map_option f xs
    in (case f x of
           NONE    => rest
         | SOME x' => x' :: rest)
    end



fun define_tree_and_thms name defs thy = let
  fun is_Some_filter (_, ((NONE, _), _)) = NONE
    | is_Some_filter (n, ((SOME x, y), z)) = SOME (n, x, y, z)
  val defs' =
      map_option is_Some_filter
                 (List.tabulate (length defs,
                                 intname_to_term o (fn n => n + 1)) ~~
                  defs)
  val vals      = map (fn (n, v, _, _) => (n, v)) defs'
  val proc_defs = map #3 defs'
  val names     = map #4 defs'
  val (def, thy') = define_tree name vals thy
  val lemmas = make_lemmas def proc_defs thy'
in
  add_thms thy' names lemmas
end
end (* functor *)

structure StaticFun = SFun
(struct
      val name_ty = @{typ "int"}
      val intname_to_term = IsabelleTermsTypes.mk_int_numeral
      val ord_ty = @{typ "int"}
      val ord_term = @{term "id :: int => int"}
      val ordsimps = simpset_of (
          put_simpset HOL_basic_ss @{context} addsimps @{thms int_simpset})
 end);


structure TestStaticFun =
struct

open StaticFun;

fun define_test_tree name sz thy =
    let
        fun tab f             = List.tabulate (sz, f)
        fun mk_proc n         = ("name" ^ Int.toString n ^ "_'proc", intname_to_term n)
        val gen_entry         = SOME o StaticFun.intname_to_term
        fun gen_names n       = "name" ^ Int.toString n ^ "_impl"
        val (proc_defs, thy') = add_defs (tab mk_proc) thy
    in
        define_tree_and_thms name (tab gen_entry ~~ proc_defs ~~ tab gen_names) thy'
    end

fun define_test_tree2 name sz thy =
    let
        fun tab f        = List.tabulate (sz, f)
        fun mk_proc n    = ("name" ^ Int.toString n ^ "_'proc", intname_to_term n)
        val (proc_defs, thy') = add_defs (tab mk_proc) thy
    in
        ([], thy')
    end

local structure P = Parse and K = Keyword in

val treeP =
    Outer_Syntax.command
        @{command_keyword "test_tree"}
        "Create an example tree with associated lemmas"
        (P.name -- P.nat
                >> (fn (name, sz) => Toplevel.local_theory NONE
                                                           (fn thy => define_test_tree name sz thy |> #2 )))

val treeP =
    Outer_Syntax.command
        @{command_keyword "test_tree2"}
        "Create an example tree with associated lemmas"
        (P.name -- P.nat
                >> (fn (name, sz) => Toplevel.local_theory NONE
                                                           (fn thy => define_test_tree2 name sz thy |> #2 )))

end
end

(*
structure StaticFunString = SFun
(struct
      type N = string
      type V = int
      val name_ty = @{typ "string"}
      val name_to_term = TermsTypes.mk_string
      val int_name = fn x => ("keyname" ^ Int.toString x)

      val val_ty = @{typ "nat"}
      val val_to_term = TermsTypes.mk_nat_numeral
      val int_val = fn x => x

      val ord_ty = @{typ "StringOrd.anotherBL"}w
      val ord_term =  @{term string_to_anbl}

      val compare = String.compare
      val ordsimps = HOL_basic_ss addsimps @{thms string_ord_simps}
 end);

*)
