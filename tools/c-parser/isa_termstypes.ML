(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

signature ISABELLE_TERMS_TYPES =
sig

  (* Types *)
  val typ_ord : typ * typ -> order
  val expand_tyabbrevs : Proof.context -> typ -> typ

  val alpha : typ
  val beta : typ
  val prop : typ
  val unit : typ
  val bool : typ
  val bool3 : typ (* bool => bool => bool; type of conj, disj,...*)
  val nat : typ
  val int : typ
  val char_ty : typ
  val string_ty : typ

  val dom_rng : typ -> typ * typ
  val dom : typ -> typ

  val mk_option_ty : typ -> typ
  val dest_option_ty : typ ->typ

  val mk_itself_type : typ -> typ

  val mk_list_type : typ -> typ
  val dest_list_type : typ -> typ

  val mk_set_type : typ -> typ
  val dest_set_type : typ -> typ

  val mk_prod_ty : typ * typ -> typ
  val list_mk_prod_ty : typ list -> typ (* unit when list is empty *)
  val dest_prod_ty : typ -> typ * typ (* TYPE when type is not a product *)

  val mk_numeral_type : int -> typ
  val dest_numeral_type : typ -> int

  structure TypTable : TABLE where type key = typ
  val match_type_frees : { pattern: typ, m : typ } -> typ TypTable.table option
  (* Terms *)

  (* -- core constructions *)
  val subst_frees : typ TypTable.table -> term -> term
  val list_mk_comb : term * term list -> term
  val strip_comb : term -> (term * term list)

  val mk_abs : term * term -> term
  val list_mk_abs : term list * term -> term
  val unbeta : {bv : term, body : term } -> term
  val variant : term list -> term -> term

  val mk_TYPE : typ -> term
  val K_rec : typ -> term
  val mk_arbitrary : typ -> term

  (* -- equalities and functions *)
  val mk_eqt : term * term -> term
  val mk_noteq : term * term -> term
  val mk_defeqn : term * term -> term
  val mk_fun_upd : term * term * term -> term (* fn, dom, rng *)
  val mk_comp_t : typ * typ * typ -> term (* 'a -> 'b -> 'c *)

  (* -- boolean constructions *)
  val mk_prop : term -> term

  val True : term
  val False : term

  val not_t : term
  val mk_neg : term -> term

  val conjunction : term
  val mk_conj : term * term -> term
  val list_mk_conj : term list -> term (* Fail on empty list *)

  val mk_imp : term * term -> term

  val mk_cond : term * term * term -> term
  val mk_forall : term * term -> term
  val strip_forall : term -> term list * term
  val list_mk_forall : term list * term -> term
  val mk_exists : term * term -> term
  val list_mk_exists : term list * term -> term

  val mk_SOME : term -> term (* Hilbert choice *)

  (* -- tuples *)
  val unit_value : term
  val mk_fst : term -> term
  val mk_pair : term * term -> term
  val list_mk_pair : term list -> term (* unit when list is empty *)
  val mk_split : term -> term
  val list_mk_pabs : term list * term -> term

  (* -- options *)
  val mk_Some : term -> term (* Some constructor *)
  val mk_the : term -> term
  val mk_case_option : term * term * term -> term (* none,some,optionvalue *)


  (* -- lists *)
  val mk_list_nil : typ -> term
  val mk_list_cons : term * term -> term
  val mk_list_singleton : term -> term
  val mk_list_update_t : typ -> term
  val mk_list_nth : term * term -> term (* number first *)
  val mk_replicate : term * term -> term (* number first *)
  val list_mk_append : term list -> term (* TERM when list is empty *)

  (* -- characters, strings *)
  val mk_char : char -> term
  val mk_string : string -> term

  (* -- sets *)
  val mk_empty : typ -> term
  val mk_UNIV : typ -> term
  val mk_IN : term * term -> term
  val mk_Un : term * term -> term
  val mk_insert : term * term -> term
  val list_mk_set : typ -> term list -> term
  val mk_CARD : typ -> term
                (* creates `card Univ` term, which prints specially *)
  val mk_collect_t : typ -> term
  val mk_compl : term -> term
  val mk_inter : term * term -> term
  val mk_cross : term * term -> term

  (* -- numbers *)
  val mk_zero : typ -> term
  val mk_one : typ -> term
  val mk_numeral : typ -> int -> term (* typ is destination type *)
  val numb_to_int : term -> int
  val mk_nat_numeral : int -> term
  val mk_int_numeral : int -> term
  val mk_leq : term * term -> term
  val mk_plus : term * term -> term
  val mk_sub : term * term -> term
  val mk_times : term * term -> term
  val mk_divides : term * term -> term
  val mk_sdiv : term * term -> term
  val mk_smod : term * term -> term
  val mk_uminus : term -> term

  val thy2ctxt : theory -> Proof.context

  val prim_mk_defn : string -> term -> theory -> theory

end


structure IsabelleTermsTypes : ISABELLE_TERMS_TYPES =
struct

type typ = Term.typ
type term = Term.term
type theory = Context.theory

(* ----------------------------------------------------------------------
    Types
   ---------------------------------------------------------------------- *)

fun typ_ord (ty1, ty2) =
    case (ty1, ty2) of
      (Type tyi1, Type tyi2) => prod_ord string_ord
                                         (list_ord typ_ord)
                                         (tyi1, tyi2)
    | (Type _, _) => LESS
    | (_, Type _) => GREATER
    | (TFree fi1, TFree fi2) => prod_ord string_ord
                                         (list_ord string_ord)
                                         (fi1, fi2)
    | (TFree _, _) => LESS
    | (_, TFree _) => GREATER
    | (TVar tv1, TVar tv2) => prod_ord (prod_ord string_ord int_ord)
                                       (list_ord string_ord)
                                       (tv1, tv2)

structure TypTable = Table(struct type key = typ val ord = typ_ord end)

fun match_type_frees {pattern,m} =
  let
    fun recurse (acc:typ TypTable.table) pmlist =
      case pmlist of
        [] => SOME acc
      | (pty, mty) :: rest =>
        let
        in
          case (pty, mty) of
            (Type(op1, args1), Type(op2, args2)) =>
              if op1 = op2 then recurse acc (ListPair.zip(args1,args2) @ rest)
              else NONE
          | (TFree _, _) => (case TypTable.lookup_key acc pty of
                               NONE => recurse (TypTable.update(pty,mty) acc) rest
                             | SOME (_, ty') => if typ_ord(ty',mty) = EQUAL then
                                             recurse acc rest
                                           else NONE)
          | (TVar id1, TVar id2) => if id1 = id2 then recurse acc rest else NONE
          | _ => NONE
        end
  in
    recurse TypTable.empty [(pattern,m)]
  end

fun subst_frees tab tm =
  let
    fun mapthis ty =
      case TypTable.lookup_key tab ty of
        NONE => map_atyps mapthis ty
      | SOME(_, ty') => ty'
  in
    Term.map_types mapthis tm
  end


(* standard types *)
val prop = @{typ "prop"}
val unit = @{typ "unit"}
val bool = @{typ "bool"}
val bool3 = bool --> (bool --> bool)
val nat = @{typ "nat"}
val int = @{typ "int"}
val char_ty = @{typ "char"}
val string_ty = @{typ "string"}
fun mk_itself_type ty = Type(@{type_name "itself"}, [ty])
fun mk_list_type ty = Type(@{type_name "list"}, [ty])
fun mk_prod_ty (ty1, ty2) = Type(@{type_name "prod"}, [ty1, ty2])
fun list_mk_prod_ty tys =
    case tys of
      [] => unit
    | [ty] => ty
    | h::t => mk_prod_ty (h, list_mk_prod_ty t)
fun dest_prod_ty ty =
    case ty of
      Type("Product_Type.prod", [arg1, arg2]) => (arg1, arg2)
    | _ => raise TYPE("Type not a product", [ty], [])
fun mk_set_type ty = Type(@{type_name "set"}, [ty])
fun dest_set_type ty =
  case ty of
    Type(@{type_name "set"}, [e]) => e
  | _ => raise TYPE("Type not a set", [ty], [])
fun dest_list_type ty =
    case ty of
      Type("List.list", args) => hd args
    | _ => raise TYPE( "dest_list_type: not a list type", [ty], [])

val alpha = TFree("'a", ["HOL.type"])
val beta = TFree("'b", ["HOL.type"])
fun dom_rng ty =
    case ty of
      Type("fun", [x,y]) => (x,y)
    | _ => raise TYPE("type not a function type", [ty], [])
val dom = fst o dom_rng
fun mk_option_ty ty = Type(@{type_name "option"}, [ty])
fun dest_option_ty ty =
    case ty of
      Type(@{type_name "option"}, args) => hd args
    | _ => raise Fail "dest_option_type: not an option type"

fun mk_numeral_type n =
    if n <= 0 then raise Fail "mk_numeral_type: arg < 1"
    else if n = 1 then @{typ "Numeral_Type.num1"}
    else let
        val (q,r) = IntInf.divMod(n, 2)
        fun optor ty =
            if r = 1 then Type(@{type_name "Numeral_Type.bit1"}, [ty])
            else Type(@{type_name "Numeral_Type.bit0"}, [ty])
      in
        optor (mk_numeral_type q)
      end

fun dest_numeral_type ty =
    case ty of
      Type(@{type_name "Numeral_Type.bit1"}, [arg]) =>
           2 * dest_numeral_type arg + 1
    | Type(@{type_name "Numeral_Type.bit0"}, [arg]) =>
           2 * dest_numeral_type arg
    | @{typ "Numeral_Type.num1"} => 1
    | ty => raise TYPE ("Not a numeral type", [ty], [])

fun expand_tyabbrevs sg ty = Thm.typ_of (Thm.ctyp_of sg ty)

(* ----------------------------------------------------------------------
    Terms
   ---------------------------------------------------------------------- *)


(* standard isabelle terms *)
fun mk_prop t = @{term "Trueprop"} $ t
val unit_value = @{term "Product_Type.Unity"}

(* this used to be K_record, now is (%x _. x) *)
fun K_rec T = Abs ("x",T, Abs ("_",T, Bound 1))

fun list_mk_comb(f, args) = List.foldl (fn (x,f) => f $ x) f args
val strip_comb = Term.strip_comb

val not_t = @{term "Not"}
fun mk_neg t = not_t $ t

val True = @{term "True"}
val False = @{term "False"}
fun mk_cond (g,t,e) = let
  val ty = type_of t
in
  Const(@{const_name "HOL.If"}, bool --> ty --> ty --> ty) $ g $ t $ e
end

fun vary v =
  case v of
    Free(vnm, vty) => Free(vnm ^ "'", vty)
  | _ => raise TERM("Not a variable", [v])

fun variant vs v =
  case v of
    Free _ =>
    let
      fun recurse v =
        if List.exists (fn v' => v' = v) vs then recurse (vary v)
        else v
    in
      recurse v
    end
  | _ => raise TERM ("Not a variable", [v])

fun mk_abs (v, t) = lambda v t

fun unbeta{bv,body} =
  case bv of
    Free p => Term.absfree p body
  | _ => raise TERM ("Not a variable", [bv])

fun mk_forall(v,t) =
  case v of
      Free (_,ty) =>
        Const(@{const_name "HOL.All"}, (ty --> bool) --> bool) $ mk_abs(v, t)
    | _ => raise TERM ("Not a variable", [v])

fun list_mk_forall(vs,t) = List.foldr mk_forall t vs

fun strip_forall t =
  let
    fun recurse acc t =
      case t of
        Const(@{const_name "HOL.All"}, _) $ Abs(vnm, vty, body) =>
          recurse (Free(vnm,vty)::acc) body
      | _ => (acc, t)
    val (vs, body) = recurse [] t
  in
    (List.rev vs, Term.subst_bounds(vs,body))
  end

fun mk_exists(v,t) =
  case v of
      Free(_,ty) =>
        Const(@{const_name "HOL.Ex"}, (ty --> bool) --> bool) $ mk_abs(v,t)
    | _ => raise TERM ("Not a variable", [v])
fun list_mk_exists(vs, b) = List.foldr mk_exists b vs

fun mk_SOME t = let
  val ty = type_of t
  val dom = #1 (dom_rng ty)
in
  Const(@{const_name "Hilbert_Choice.Eps"}, ty --> dom) $ t
end
val conjunction = @{term "op &"}
fun mk_conj(t1,t2) = conjunction $ t1 $ t2
fun list_mk_conj cs =
    case cs of
      [] => raise Fail "list_mk_conj: empty list"
    | [c] => c
    | c::cs => mk_conj(c,list_mk_conj cs)

fun mk_imp(t1,t2) = Const(@{const_name "HOL.implies"}, bool --> bool --> bool) $ t1 $ t2

fun mk_pair (t1,t2) = let
  val ty1 = type_of t1
  val ty2 = type_of t2
in
  Const(@{const_name "Pair"}, ty1 --> ty2 --> mk_prod_ty (ty1,ty2)) $ t1 $ t2
end

fun mk_fst t = let
  val (ty1, _) = dest_prod_ty (type_of t)
in
  Const(@{const_name "fst"}, type_of t --> ty1) $ t
end

fun mk_list_nil ty =
    Const(@{const_name "List.list.Nil"}, mk_list_type ty)

fun mk_list_cons (w, ws) = let
  val ty = type_of w
in
  Const(@{const_name "List.list.Cons"}, ty --> mk_list_type ty --> mk_list_type ty) $ w $ ws
end

fun mk_list_singleton w = let
  val ty = type_of w
in
  mk_list_cons (w, mk_list_nil ty)
end

fun list_mk_pair tlist =
    case tlist of
      [] => unit_value
    | _::_ => let val (front,last) = split_last tlist
              in
                List.foldr mk_pair last front
              end




fun list_mk_abs (vs, bdy) = List.foldr mk_abs bdy vs

fun mk_split t = let
  val ty = type_of t
  val (d1, r1) = dom_rng ty
  val (d2, r) = dom_rng r1
in
  Const(@{const_name "case_prod"}, ty --> (mk_prod_ty(d1, d2) --> r)) $ t
end

fun list_mk_pabs (vs, bdy) =
    case vs of
      [] => bdy
    | [v] => mk_abs(v, bdy)
    | [_,_] => mk_split(list_mk_abs(vs, bdy))
    | h::t => mk_split(mk_abs(h, list_mk_pabs(t, bdy)))

fun mk_case_option (none_t, some_f, opt) =
    Const(@{const_name "Option.case_option"},
          type_of none_t --> type_of some_f --> type_of opt -->
          type_of none_t) $ none_t $ some_f $ opt

fun mk_list_update_t ty = Const(@{const_name "List.list_update"},
                                mk_list_type ty --> nat -->
                                             ty --> mk_list_type ty)
fun mk_collect_t ty = Const(@{const_name "Collect"},
                            (ty --> bool) --> mk_set_type ty)
fun mk_list_nth (list,n) = let
  val listty = type_of list
  val elty = dest_list_type listty
in
  Const("List.nth", listty --> nat --> elty) $ list $ n
end

fun mk_replicate (n, el) =
    Const("List.replicate", nat --> type_of el --> mk_list_type (type_of el)) $
    n $ el
fun list_mk_append tlist =
    case tlist of
      [] => raise TERM ("list_mk_append: empty list", [])
    | [x] => x
    | h::t => Const(@{const_name "List.append"},
                    type_of h --> type_of h --> type_of h) $
                   h $ list_mk_append t

fun mk_fun_upd(f, domval, rngval) = let
  val domty = type_of domval
  val rngty = type_of rngval
in
  Const("fun_upd", (domty --> rngty) --> domty --> rngty -->
                   domty --> rngty) $ f $ domval $ rngval
end

fun mk_comp_t (a_ty,b_ty,c_ty) = Const("Fun.comp", (b_ty --> c_ty) -->
    (a_ty --> b_ty) --> (a_ty --> c_ty))

fun mk_eqt(t1, t2) = let
  val ty1 = type_of t1
  val ty2 = type_of t2
  val _ = @{assert} (ty1 = ty2)
in
  Const(@{const_name "HOL.eq"}, ty1 --> (ty1 --> bool)) $ t1 $ t2
end
fun mk_noteq (t1,t2) = mk_neg(mk_eqt(t1,t2))
fun mk_defeqn (t1,t2) = let
  val ty1 = type_of t1
in
  Const(@{const_name "Pure.eq"}, ty1 --> ty1 --> prop) $ t1 $ t2
end

fun mk_char c = HOLogic.mk_char (Char.ord c)
fun mk_string s = HOLogic.mk_list char_ty (map mk_char (String.explode s))

fun mk_Some t = let
  val ty = type_of t
in
  Const(@{const_name "Option.Some"}, ty --> mk_option_ty ty) $ t
end

fun mk_the t = let
  val oty = type_of t
  val ty = dest_option_ty (type_of t)
in
  Const(@{const_name "Option.the"}, oty --> ty) $ t
end

fun mk_TYPE ty = Const(@{const_name "Pure.type"}, mk_itself_type ty)

(* sets *)
fun mk_IN(t1, t2) = let
  val ty = type_of t1
  val ty2 = mk_set_type ty
  val _ = @{assert} (ty2 = type_of t2)
in
  Const(@{const_name "Set.member"}, ty --> mk_set_type ty --> bool) $ t1 $ t2
end

fun mk_Un(t1, t2) = let
  val ty = type_of t1
in
  (* used to be "Set.union", will probably be again in next Isabelle version *)
  Const(@{const_name "sup"}, ty --> ty --> ty) $ t1 $ t2
end

(* used to be "Set.empty", will probably be again in next Isabelle version *)
fun mk_empty elem_ty = Const(@{const_name "bot"}, mk_set_type elem_ty)

fun mk_insert (et, st) = let
  val sty = type_of st
in
  Const(@{const_name "Set.insert"}, type_of et --> sty --> sty) $ et $ st
end

(* used to be "Set.UNIV", will probably be again in next Isabelle version *)
fun mk_UNIV ty = Const(@{const_name "top"}, mk_set_type ty)
fun mk_CARD ty =
    Const(@{const_name "Finite_Set.card"}, mk_set_type ty --> nat) $ mk_UNIV ty
fun list_mk_set ty list = List.foldl mk_insert (mk_empty ty) list

(* have to spell out full-name, rather defeating point of const_name antiquote, because
   something called SmallStep.inf gets in the way otherwise *)
fun mk_inter(t1, t2) =
  Const(@{const_name "Lattices.inf_class.inf"}, type_of t1 --> type_of t1 --> type_of t1) $ t1 $ t2

fun mk_cross(t1, t2) =
  let
    val e1ty = dest_set_type (type_of t1)
    val e2ty = dest_set_type (type_of t2)
    val rty = mk_set_type (mk_prod_ty(e1ty, e2ty))
  in
    Const(@{const_name "Sigma"}, type_of t1 --> (e1ty --> type_of t2) --> rty) $
    t1 $ mk_abs(Free("_", e1ty), t2)
  end

fun mk_compl t =
  Const(@{const_name "uminus"}, type_of t --> type_of t) $ t

(* numerals *)
fun mk_zero ty = Const(@{const_name "Groups.zero_class.zero"}, ty)
fun mk_one ty = Const(@{const_name "Groups.one_class.one"}, ty)

val mk_numeral = HOLogic.mk_number

val mk_nat_numeral = mk_numeral nat
val mk_int_numeral = mk_numeral int

fun calc acc base t =
    case t of
      Const(@{const_name "Num.num.Bit0"}, _) $ t' =>
        calc acc (base * 2) t'
    | Const(@{const_name "Num.num.Bit1"}, _) $ t' =>
        calc (acc + base) (base * 2) t'
    | Const(@{const_name "Num.num.One"}, _) => acc
    | _ => raise TERM ("Not a numeral", [t])

fun numb_to_int t =
    case t of
      Const(@{const_name "Groups.zero_class.zero"}, _) => 0
    | Const(@{const_name "Groups.one_class.one"}, _) => 1
    | Const(@{const_name "Suc"}, _) $
           Const(@{const_name "Groups.zero_class.zero"}, _) => 1
    | Const(@{const_name "Num.numeral_class.numeral"}, _) $ t => calc 0 1 t
    | t => raise TERM ("TermsTypes.numb_to_int: not a number term", [t])

(* arithmetic *)
fun mk_leq(t1, t2) = let
  val ty = type_of t1
in
  Const(@{const_name "Orderings.ord_class.less_eq"}, ty --> ty --> bool) $ t1 $ t2
end
fun mk_plus(t1, t2) = let
  val ty = type_of t1
in
  Const(@{const_name "Groups.plus_class.plus"}, ty --> ty --> ty) $ t1 $ t2
end
fun mk_sub(t1, t2) = let
  val ty = type_of t1
in
  Const(@{const_name "Groups.minus_class.minus"}, ty --> ty --> ty) $ t1 $ t2
end
fun mk_divides(t1, t2) = let
  val ty = type_of t1
in
  Const(@{const_name "dvd"}, ty --> ty --> bool) $ t1 $ t2
end
fun mk_times(t1,t2) = let
  val ty = type_of t1
in
  Const(@{const_name "times"}, ty --> ty --> ty) $ t1 $ t2
end
fun mk_sdiv(t1,t2) = let
  val ty = type_of t1
in
  Const(@{const_name "sdiv"}, ty --> ty --> ty) $ t1 $ t2
end
fun mk_smod(t1,t2) = let
  val ty = type_of t1
in
  Const(@{const_name "smod"}, ty --> ty --> ty) $ t1 $ t2
end

fun mk_uminus t = let
  val ty = type_of t
in
  Const(@{const_name "uminus"}, ty --> ty) $ t
end

(* ----------------------------------------------------------------------
    useful functions on cterms
   ---------------------------------------------------------------------- *)

val thy2ctxt = Context_Position.set_visible false o Proof_Context.init_global

fun mk_arbitrary ty = Const(@{const_name "undefined"}, ty)

fun prim_mk_defn s t thy = let
  val ty = type_of t
  val fvar = Free(s, ty)
  val eqn = Logic.mk_equals(fvar, t)
  val binding0 = Binding.make(s ^ "_def", Position.none)
  val binding = (binding0, []) (* [] is a Token.src list *)
  val lthy = Named_Target.theory_init thy
  val (_, lthy') = Specification.definition NONE [] [] (binding, eqn) lthy
in
  Local_Theory.exit_global lthy'
end

end (* struct *)
