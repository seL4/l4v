(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(* provide an inputLine function à la old version of the Basis Library *)
structure StrictCBasics =
struct
  fun inputLine istr = case TextIO.inputLine istr of
                         NONE => ""
                       | SOME s => s

  (*
  val inputLine = TextIO.inputLine
  *)

  (* fix for Isabelle library change *)
  fun assoc x = uncurry (AList.lookup (op =)) x;

  (* recreated from Isabelle library change *)
  fun assert p msg = if p then () else error msg;


fun list_compare cfn =
 let fun comp ([],[]) = EQUAL
       | comp ([], _) = LESS
       | comp (_, []) = GREATER
       | comp (h1::t1, h2::t2) =
          case cfn (h1,h2) of EQUAL => comp (t1,t2) | x => x
  in comp end;

fun pair_compare (acmp, bcmp) ((a1, b1), (a2, b2)) =
    case acmp(a1, a2) of
      EQUAL => bcmp(b1, b2)
    | x => x

fun option_compare _ (NONE, SOME _) = LESS
  | option_compare _ (NONE, NONE) = EQUAL
  | option_compare _ (SOME _, NONE) = GREATER
  | option_compare cmp (SOME x, SOME y) = cmp(x,y)

fun measure_cmp f (x,y) = Int.compare(f x, f y)
fun inv_img_cmp f c (x,y) = c (f x, f y)

structure CNameTab = Table
  (struct type key = {varname : string,
                      fnname : string option}
          fun ord ({varname = vn1, fnname = fn1},
                   {varname = vn2, fnname = fn2}) =
              pair_compare (option_compare String.compare,
                            String.compare)
                           ((fn1, vn1), (fn2, vn2))
   end)
end;
open StrictCBasics

datatype more_info = MungedVar of { munge : string, owned_by : string option}
                   | EnumC
                   | FunctionName

signature FLIP_TABLE =
sig
  type key
  type 'a table
  val flip : key list table -> key list table
end
functor FlipTable(structure Table : TABLE) : FLIP_TABLE =
struct
  type key = Table.key
  type 'a table = 'a Table.table
  fun flip table = let
    fun foldthis (k:key,elems:key list) acc =
        List.foldl (fn (e,acc) => Table.cons_list (e,k) acc) acc elems
  in
    Table.fold foldthis table Table.empty
  end
end
local
  structure FlipSymTab = FlipTable(structure Table = Symtab)
in
  val flip_symtab = FlipSymTab.flip
end
