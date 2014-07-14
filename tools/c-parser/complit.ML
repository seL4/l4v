(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(* code for manipulating "paths" into C99's compound
   literal expressions *)

signature COMPLIT =
sig

datatype valpath = idx of int | fld of string
type cty = int Absyn.ctype
type senv = (string * (string * cty) list) list

val type_at_path : cty -> senv -> valpath list -> cty

val extend_to_leaf : cty -> senv -> valpath list -> valpath list

val bump_path : cty -> senv -> valpath -> valpath option
val leaf_inc_path : cty -> senv -> valpath list -> valpath list option
val vpl_toString : valpath list -> string

val find_type : cty -> senv -> valpath list -> cty -> valpath list option

val find_ilist_size : Absyn.ecenv -> (Absyn.designator list * Absyn.initializer) list -> int

end


structure complit : COMPLIT =
struct

open Absyn Basics
datatype valpath = idx of int | fld of string
type cty = int Absyn.ctype
type senv = (string * (string * cty) list) list

fun vpname (idx i) = "["^Int.toString i^"]"
  | vpname (fld s) = "." ^ s

fun vpl_toString [] = ""
  | vpl_toString (h::t) = vpname h ^ vpl_toString t

fun get_fields senv snm =
    case assoc(senv, snm) of
      NONE => raise Fail ("get_fields: no struct called "^snm)
    | SOME flds => flds

fun get_fld_type senv (snm, fldname) =
    case assoc(get_fields senv snm, fldname) of
      NONE => raise Fail ("get_fld_type: no field "^fldname^" in "^snm)
    | SOME ty => ty

fun get_next_field e list =
    case list of
      [] => NONE
    | (e',_) :: t => if e' = e then
                       case t of [] => NONE
                               | (e'', _) :: _ => SOME e''
                     else get_next_field e t

fun type_at_path rootty senv pth =
    case pth of
      [] => rootty
    | idx i :: rest => let
      in
        case rootty of
          Array(ety,SOME cnt) =>
            if 0 <= i andalso i < cnt then
              type_at_path ety senv rest
            else
              raise Fail ("type_at_path: bad index "^
                          Int.toString i ^ " for " ^
                          tyname rootty)
        | _ => raise Fail ("type_at_path: index selector ["^Int.toString i^
                           "], for "^tyname rootty)
      end
    | fld s :: rest => let
      in
        case rootty of
          StructTy snm => type_at_path (get_fld_type senv (snm, s)) senv rest
        | _ => raise Fail ("type_at_path: bad type ("^tyname rootty^
                           ") for field "^s)
      end


fun extend_to_leaf rootty senv pth =
  case type_at_path rootty senv pth of
    Array(ety, _) => pth @ [idx 0] @ extend_to_leaf ety senv []
  | StructTy snm => let
      val flds = get_fields senv snm
      val (hdfld, hdty) = case flds of
                            [] => raise Fail ("extend_to_leaf: struct "^snm^
                                              " has no fields")
                          | h::_ => h
    in
      pth @ [fld hdfld] @ extend_to_leaf hdty senv []
    end
  | _ => pth

fun bump_path ty_above senv el =
    case (ty_above, el) of
      (Array(_, SOME cnt), idx i) => if i < cnt - 1 then SOME (idx (i + 1))
                                     else NONE
    | (StructTy snm, fld f) => let
        val flds = get_fields senv snm
      in
        Option.map fld (get_next_field f flds)
      end
    | _ => raise Fail ("bump_path: bad combination of type and valpath: "^
                       Absyn.tyname ty_above ^ " " ^ vpname el)


fun leaf_inc_path rootty senv pth = let
  fun recurse rootty pth =
      case pth of
        [] => raise Fail "Can't increment an empty path"
      | [h] => let
        in
          case bump_path rootty senv h of
            NONE => NONE
          | SOME h' => SOME (extend_to_leaf rootty senv [h'])
        end
      | h::t => let
        in
          case recurse (type_at_path rootty senv [h]) t of
            NONE => let
            in
              case bump_path rootty senv h of
                NONE => NONE
              | SOME p => SOME (extend_to_leaf rootty senv [p])
            end
          | SOME p' => SOME (extend_to_leaf rootty senv (h :: p'))
        end
in
  recurse rootty pth
end

fun find_type rootty senv input_path findty = let
  fun recurse curty p =
      case p of
        [] => NONE
      | (x::xs) => let
          val candidate_ty = type_at_path curty senv [x]
        in
          if candidate_ty = findty then SOME [x]
          else Option.map (fn t => x::t) (recurse candidate_ty xs)
        end
in
  recurse rootty input_path
end

fun find_ilist_size ecenv ilist = let
  fun recurse maxsofar last ilist =
      case ilist of
        [] => maxsofar
      | (dlist,_) :: rest => let
        in
          case dlist of
            [] => recurse (Int.max(maxsofar, last + 1)) (last + 1) rest
          | DesignE i_exp :: _ =>  let
              val i = IntInf.toInt (consteval ecenv i_exp + 1)
            in
              recurse (Int.max(maxsofar, i)) i rest
            end
          | DesignFld _ :: _ =>
              raise Fail "find_ilist_size: fld designator in array \
                         \initializer??"
        end
in
  recurse 0 0 ilist
end


end (* struct *)
