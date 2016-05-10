(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

structure CTypeDatatype =
struct
datatype inttype = datatype BaseCTypes.base_inttype
datatype 'c ctype =
         Signed of inttype
       | Unsigned of inttype
       | Bool
       | PlainChar
       | StructTy of string
       | EnumTy of string option
       | Ptr of 'c ctype
       | Array of 'c ctype * 'c option
       | Bitfield of bool * 'c (* true for signed field *)
       | Ident of string
       | Function of 'c ctype * 'c ctype list
       | Void
end

signature CTYPE =
sig
  datatype inttype = datatype CTypeDatatype.inttype
  val inttyname : inttype -> string
  val inttype_compare : inttype * inttype -> order
  val int_width : inttype -> IntInf.int (* size in bits *)
  val int_sizeof : inttype -> int (* size in bytes *)

  datatype ctype = datatype CTypeDatatype.ctype
  val is_signed : 'a ctype -> bool
  val scalar_type : 'a ctype -> bool
  val ptr_type : 'a ctype -> bool
  val integer_type : 'a ctype -> bool
  val arithmetic_type : 'a ctype -> bool
  val array_type : 'a ctype -> bool
  val function_type : 'a ctype -> bool
  val aggregate_type : 'a ctype -> bool

  val fparam_norm : 'a ctype -> 'a ctype
  val param_norm : 'a ctype -> 'a ctype
  val remove_enums : 'a ctype -> 'a ctype
  val integer_promotions : 'a ctype -> 'a ctype
  val arithmetic_conversion : 'a ctype * 'a ctype -> 'a ctype
  val unify_types : ''a ctype * ''a ctype -> ''a ctype
  val imax : 'a ctype -> IntInf.int
  val imin : 'a ctype -> IntInf.int
  val ty_width : 'a ctype -> IntInf.int (* only for integral types *)
  val sizeof : (string -> int) -> int ctype -> int
               (* function gives sizes for structs (by name) *)


  val tyname0 : ('a -> string) -> 'a ctype -> string
  val tyname : int ctype -> string
  val ctype_compare : ('a * 'a -> order) -> 'a ctype * 'a ctype -> order
  structure ImplementationTypes : sig
    val size_t : 'a ctype
    val ptrdiff_t : 'a ctype
    val ptrval_t : 'a ctype
  end
end

structure CType : CTYPE =
struct
open CTypeDatatype
fun inttyname ty =
    case ty of
      Char => "char"
    | Short => "short"
    | Int => "int"
    | Long => "long"
    | LongLong => "longlong"

fun irank Char = 1 | irank Short = 2 | irank Int = 3 | irank Long = 4 |
    irank LongLong = 5

val inttype_compare = measure_cmp irank

fun bool_compare (b1,b2) = if b1 = b2 then EQUAL
                           else if b1 = false then LESS
                           else GREATER


fun is_signed (Signed _) = true
  | is_signed PlainChar = ImplementationNumbers.char_signedp
  | is_signed _ = false


fun tyname0 f ty = let
  val tyname = tyname0 f
  fun seplist [] = ""
    | seplist [x] = tyname x
    | seplist (h::t) = String.concat [tyname h, ",", seplist t]
in
  case ty of
    Signed ity => (case ity of Char => "signed_char" | _ => inttyname ity)
  | Unsigned x => let
    in
      case x of
        Int => "unsigned"
      | _ => "unsigned_"^inttyname x
    end
  | PlainChar => "char"
  | Bool => "_Bool"
  | Ptr ty0 => "ptr_to_" ^ tyname ty0
  | Array(ty0, SOME sz) => tyname ty0 ^ "_array" ^ f sz
  | Array(ty0, NONE) => tyname ty0 ^ "_array[incomplete]"
  | StructTy s => "struct_" ^ s
  | Ident s => "typedef_"^s
  | Bitfield (true, n) => "int:"^f n
  | Bitfield (false,n) => "unsigned:"^f n
  | Void => "void"
  | Function (ret, ptys) =>
      String.concat ["[", seplist ptys, "]->", tyname ret]
  | EnumTy (SOME s) => "enum_"^s
  | EnumTy NONE => "anonymous_enum"
end

val tyname = tyname0 Int.toString


fun integer_conversion_rank ty =
    case ty of
      Signed i => irank i
    | Unsigned i => irank i
    | EnumTy _ => irank Int
    | PlainChar => irank Char
    | Bool => 0
    | _ => ~1

structure ImplementationTypes =
struct
  val size_t = Unsigned Int
  val ptrdiff_t = Signed Int
  val ptrval_t = Unsigned ImplementationNumbers.ptr_t
end

fun scalar_type ty =
    case ty  of
      Signed _ => true
    | Unsigned _ => true
    | PlainChar => true
    | Ptr _ => true
    | EnumTy _ => true
    | Array _ => true (* coz it decays to a pointer *)
    | Bool => true
    | _ => false

fun ptr_type (Ptr _) = true
  | ptr_type _ = false

fun integer_type ty = scalar_type ty andalso not (ptr_type ty)

val arithmetic_type = integer_type (* in the absence of floating types *)

fun fparam_norm ty = let
in
  case ty of
    Ptr (Array(ty,NONE)) => Ptr (Ptr (fparam_norm ty))
  | Ptr ty => Ptr (fparam_norm ty)
  | Array (ty,sz) => Array(fparam_norm ty, sz)
  | Function (ret, args) => Function(fparam_norm ret, map param_norm args)
  | ty => ty
end
and param_norm ty =
    case ty of
      Function (ret,args) =>
      Ptr (Function (fparam_norm ret, map param_norm args))
    | Array (ty, sz) => Ptr (fparam_norm ty)
    | ty => fparam_norm ty

fun array_type (Array _) = true
  | array_type _ = false
fun function_type (Function _) = true
  | function_type _ = false

fun remove_enums ty =
    case ty of
      Ptr ty => Ptr (remove_enums ty)
    | Array(ty, x) => Array(remove_enums ty, x)
    | Function(rettype, argtypes) => Function(remove_enums rettype,
                                              map remove_enums argtypes)
    | EnumTy _ => Signed Int
    | _ => ty


fun tysz_rank ty =
    case ty of
      Signed _ => 0
    | Unsigned _ => 1
    | StructTy _ => 2
    | EnumTy _ => 3
    | Ptr _ => 4
    | Array _ => 5
    | Bitfield _ => 6
    | Ident _ => 7
    | Function _ => 8
    | Void => 9
    | PlainChar => 10
    | Bool => 11

fun ctype_compare cecmp (ty1, ty2) =
  case (ty1, ty2) of
    (Signed i1, Signed i2) => inttype_compare(i1,i2)
  | (Unsigned i1, Unsigned i2) => inttype_compare(i1, i2)
  | (StructTy s1, StructTy s2) => String.compare(s1, s2)
  | (EnumTy s1, EnumTy s2) => option_compare String.compare(s1, s2)
  | (Ptr ty1, Ptr ty2) => ctype_compare cecmp (ty1, ty2)
  | (Array tysz1, Array tysz2) =>
      pair_compare(ctype_compare cecmp, option_compare cecmp) (tysz1,tysz2)
  | (Bitfield bce1, Bitfield bce2) =>
      pair_compare(bool_compare, cecmp) (bce1, bce2)
  | (Ident s1, Ident s2) => String.compare(s1, s2)
  | (Function f1, Function f2) =>
      pair_compare(ctype_compare cecmp, list_compare (ctype_compare cecmp))
                  (f1, f2)
  | _ => measure_cmp tysz_rank (ty1, ty2)


fun integer_promotions ty = let
  open ImplementationNumbers
  (* see 6.3.1.1 *)
in
  case ty of
    Bool => Signed Int
  | Signed Char => Signed Int
  | Unsigned Char => if UCHAR_MAX > INT_MAX then Unsigned Int else Signed Int
  | Signed Short => Signed Int
  | Unsigned Short => if USHORT_MAX > INT_MAX then Unsigned Int else Signed Int
  | PlainChar => if CHAR_MAX > INT_MAX then Unsigned Int else Signed Int
  | EnumTy _ => Signed Int (* arbitrary! Implementations may do this
                              differently *)
  | ty => ty
end

fun imax ty = let
  open ImplementationNumbers
in
  case ty of
    Bool => 1
  | PlainChar => CHAR_MAX
  | Unsigned Char => UCHAR_MAX
  | Signed Char => SCHAR_MAX
  | Unsigned Short => USHORT_MAX
  | Signed Short => SHORT_MAX
  | Signed Int => INT_MAX
  | Unsigned Int => UINT_MAX
  | Signed Long => LONG_MAX
  | Unsigned Long => ULONG_MAX
  | Signed LongLong => LLONG_MAX
  | Unsigned LongLong => ULLONG_MAX
  | _ => raise Fail ("imax called on bad type: "^tyname0 (fn _ => "") ty)
end

fun imin ty = let
  open ImplementationNumbers
in
  case ty of
    Unsigned _ => 0
  | Bool => 0
  | Signed Char => SCHAR_MIN
  | Signed Short => SHORT_MIN
  | Signed Int => INT_MIN
  | Signed Long => LONG_MIN
  | Signed LongLong => LLONG_MIN
  | PlainChar => CHAR_MIN
  | _ => raise Fail ("Abysn.imin called on: "^tyname0 (fn _ => "") ty)
end

fun arithmetic_conversion (t1,t2) = let
  val t1' = integer_promotions t1
  val t2' = integer_promotions t2
  val cmp =
      ctype_compare
          (fn p => raise Fail "arithmetic_conversion: comparing non-arithmetic\
                              \ types")
  fun signedp (Signed i) = (true, i)
    | signedp (Unsigned i) = (false, i)
    | signedp _ = raise Fail "arithmetic_conversion.signedp: comparing \
                             \non-arithmetic types"
  fun doit (t1, t2) =
      case cmp(t1, t2) of
        EQUAL => t1
      | GREATER => doit(t2, t1)
      | LESS => let
          val (sp1, i1) = signedp t1
          val (sp2, i2) = signedp t2
          val r1 = integer_conversion_rank t1
          val r2 = integer_conversion_rank t2
        in
          if sp1 = sp2 then t2
          else if r1 < r2 then t2 (* t2 is unsigned, t1 is signed *)
          else if imax t1 >= imax t2 then t1
          else Unsigned i1
        end
in
  doit (t1', t2')
end

fun unify_types (ty1, ty2) = let
  (* for use in conditional expressions where the type of the branches
     needs to be the same, but might give different types when analysed
     independently, as would happen in something like
         ptr_valid(ptr) ? ptr : 0;
  *)
  fun ptype ty = ptr_type ty orelse case ty of Array _ => true | _ => false
in
  if ptype ty1 andalso not (ptype ty2) then unify_types (ty2, ty1)
  else let
      val ty2 = case ty2 of Array (ty,_) => Ptr ty | _ => ty2
    in
      case (ty1, ty2) of
        (Signed _, Ptr _) => ty2
      | (Unsigned _, Ptr _) => ty2
      | (PlainChar, Ptr _) => ty2
      | (EnumTy _, Ptr _) => ty2
      | (Ptr subty1, Ptr subty2) => if subty1 = Void then ty2
                                    else if subty2 = Void then ty1
                                    else if subty1 = subty2 then ty1
                                    else raise Fail "Not unifiable"
      | _ => if integer_type ty1 andalso integer_type ty2 then
               arithmetic_conversion (ty1, ty2)
             else if ty1 = ty2 then ty1
             else raise Fail "Not unifiable"
    end
end

val fi = IntInf.fromInt
val ti = IntInf.toInt
local open ImplementationNumbers
in
fun int_width Char = CHAR_BIT
  | int_width Short = shortWidth
  | int_width Int = intWidth
  | int_width Long = longWidth
  | int_width LongLong = llongWidth


fun ty_width (Signed i) = int_width i
  | ty_width (Unsigned i) = int_width i
  | ty_width PlainChar = CHAR_BIT
  | ty_width ty = raise Fail ("Absyn.ty_width: non integral argument: "^
                              tyname0 (fn _ => "") ty)

fun int_sizeof ty = ti (int_width ty div CHAR_BIT)

end


fun sizeof (structsizes : string -> Int.int) ty : Int.int = let
  open ImplementationNumbers
in
  case ty of
    Signed i => int_sizeof i
  | Unsigned i => int_sizeof i
  | PlainChar => 1
  | Bool => ti (boolWidth div CHAR_BIT)
  | StructTy s => structsizes s
  | EnumTy s => int_sizeof Int
  | Ptr _ => ti (ptrWidth div CHAR_BIT)
  | Array(base, SOME sz) => sz * sizeof structsizes base
  | Array(base, NONE) => raise Fail "Can't compute size for incomplete array"
  | Bitfield _ => raise Fail "Can't compute sizes for bit-fields"
  | Ident _ => raise Fail "Can't compute sizes for type-defs"
  | Function _ => raise Fail "Can't compute sizes for functions"
  | Void => raise Fail "Can't compute a size for void"
end

fun aggregate_type (StructTy _) = true
  | aggregate_type (Array _) = true
  | aggregate_type _ = false

(* an approximation, ignoring the type variable component *)
fun eqty(ty1, ty2) =
    case (ty1, ty2) of
      (Signed ity1, Signed ity2) => ity1 = ity2
    | (Unsigned ity1, Unsigned ity2) => ity1 = ity2
    | (PlainChar, PlainChar) => true
    | (StructTy s1, StructTy s2) => s1 = s2
    | (EnumTy s1, EnumTy s2) => s1 = s2
    | (Ptr ty1, Ptr ty2) => eqty(ty1, ty2)
    | (Array(ty1,_), Array(ty2,_)) => eqty(ty1,ty2)
    | (Bitfield(b1, _), Bitfield(b2,_)) => b1 = b2
    | (Ident s1, Ident s2) => s1 = s2
    | (Function(retty1, args1), Function(retty2, args2)) =>
         eqty(retty1,retty2) andalso
         ListPair.all eqty (args1, args2)
    | (Void, Void) => true
    | _ => false
end (* struct *)
