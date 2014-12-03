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
 * Sets of items.
 *
 * Currently implemented using sorted lists.
 *)

signature SET =
sig
  type key
  type 'a set

  val empty : key set
  val is_empty : key set -> bool
  val make : key list -> key set
  val dest : key set -> key list
  val inter : key set -> key set -> key set
  val subtract : key set -> key set -> key set (* NOTE: subtracts first from second *)
  val union : key set -> key set -> key set
  val union_sets : key set list -> key set
  val insert : key -> key set -> key set
  val contains : key set -> key -> bool
  val subset : (key set * key set) -> bool
  val card: key set -> int
  val map: (key -> key) -> key set -> key set
  val filter: (key -> bool) -> key set -> key set
end;

functor Set(Key: KEY): SET =
struct

type key = Key.key;

(*
 * We wrap everything in a private datatype to enforce the user to only use the
 * abstract interface.
 *)
datatype 'a set = S of 'a list;

(* Make a set from a list. *)
fun make x = Ord_List.make Key.ord x |> S

(* Convert the set back into a list. *)
fun dest (S x) = x

(* Emptiness *)
val empty = S []
fun is_empty (S x) = (length x = 0)

(* Set manipulation. *)
fun inter (S a) (S b) = Ord_List.inter Key.ord a b |> S
fun subtract (S a) (S b) = Ord_List.subtract Key.ord a b |> S
fun union (S a) (S b) = Ord_List.union Key.ord a b |> S
fun insert a (S b) = Ord_List.insert Key.ord a b |> S
fun union_sets l = fold union l empty
fun contains (S l) a = Ord_List.member Key.ord l a
fun subset (S a, S b) = Ord_List.subset Key.ord (a, b)
fun card (S a) = length a
fun map f (S a) = make (List.map f a)
fun filter f (S a) = S (List.filter f a)

end;

structure Intset = Set(type key = int val ord = int_ord);
structure Symset = Set(type key = string val ord = fast_string_ord);
structure Varset = Set(type key = (string * typ) val ord =
    fn (a,b) => Term_Ord.var_ord (((fst a, 0), snd a), ((fst b, 0), snd b)));
structure Typset = Set(type key = typ val ord = Term_Ord.typ_ord);

type varset = Varset.key Varset.set
type symset = Symset.key Symset.set
type typset = Typset.key Typset.set

