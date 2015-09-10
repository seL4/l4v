(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

structure StrictCBasics =
struct

fun inputLine istr = case TextIO.inputLine istr of
                       NONE => ""
                     | SOME s => s

fun assoc (l, x) =
    case l of
      [] => NONE
    | (k,v) :: rest => if k = x then SOME v else assoc(rest, x)

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

fun option_compare cfn vals =
    case vals of
      (NONE, NONE) => EQUAL
    | (NONE, _) => LESS
    | (_, NONE) => GREATER
    | (SOME v1, SOME v2) => cfn(v1, v2)


fun measure_cmp f (x,y) = Int.compare(f x, f y)
fun inv_img_cmp f c (x,y) = c (f x, f y)

end
open StrictCBasics

fun apsnd f (x,y) = (x,f y)


structure Hoare =
struct
  fun varname s = s ^ "_'"
end

infix 1 |> ||>> |->

structure Basics =
struct
  fun cons h t = h::t
  fun x |> f = f x
  fun (x,y) ||>> f = let val (z, y') = f y in ((x,z), y') end
  fun (x,y) |-> f = f x y
  fun pair x y = (x,y)
  val the = valOf
  fun snd (x,y) = y
  fun these NONE = []
    | these (SOME l) = l
  fun fold _ [] y = y
    | fold f (x :: xs) y = fold f xs (f x y)
  fun fold_rev _ [] y = y
    | fold_rev f (x :: xs) y = f x (fold_rev f xs y)

  fun K x y = x
  fun I x = x

end

open Basics

infix mem union
structure Library =
struct

  val int_ord = Int.compare
  val fast_string_ord = String.compare

  fun maps f [] = []
    | maps f (x :: xs) = f x @ maps f xs

  fun filter_out f = List.filter (not o f)
  fun fold_index f = let
    fun fold_aux (_: int) [] y = y
      | fold_aux i (x :: xs) y = fold_aux (i + 1) xs (f (i, x) y)
  in
    fold_aux 0
  end


  fun member eq list x = let
    fun memb [] = false
      | memb (y :: ys) = eq (x, y) orelse memb ys
  in memb list end

  fun x mem xs = member (op =) xs x

  fun insert eq x xs = if member eq xs x then xs else x :: xs

  fun remove eq x xs = if member eq xs x then
                         filter_out (fn y => eq (x, y)) xs
                       else xs
  fun update eq x xs = cons x (remove eq x xs)

  fun merge _ ([], ys) = ys
    | merge eq (xs, ys) = fold_rev (insert eq) ys xs

  fun swap (x,y) = (y,x)

  fun subset eq (xs, ys) = List.all (member eq ys) xs

  (*set equality*)
  fun eq_list eq (list1, list2) = let
    fun eq_lst (x :: xs, y :: ys) = eq (x, y) andalso eq_lst (xs, ys)
      | eq_lst _ = true
  in
    length list1 = length list2 andalso eq_lst (list1, list2)
  end

  fun eq_set eq (xs, ys) =
      eq_list eq (xs, ys) orelse
      (subset eq (xs,ys) andalso subset (eq o swap) (ys,xs))


  fun apfst f (x, y) = (f x, y)

  fun separate sep list = let
  fun recurse acc list =
      case list of
        [] => List.rev acc
      | [e] => List.rev (e::acc)
      | e::rest => recurse (sep::e::acc) rest
  in
    recurse [] list
  end

  fun uncurry f (x,y) = f x y

  (*union of sets represented as lists: no repetitions*)
  fun union eq = List.foldl (uncurry (insert eq))

  fun single x = [x]

  fun get_first f l =
      case l of
        [] => NONE
      | h :: t => (case f h of NONE => get_first f t | x => x)

  val is_some = isSome
  val pointer_eq = MLton.eq

  fun prod_ord a_ord b_ord ((x, y), (x', y')) =
      (case a_ord (x, x') of EQUAL => b_ord (y, y') | ord => ord);


end

open Library
