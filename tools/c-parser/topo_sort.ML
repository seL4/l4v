(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

signature TOPO_SORT =
sig

  val topo_sort : {cmp: 'a * 'a -> order, graph : 'a -> 'a list,
                   converse : 'a -> 'a list} ->
                  'a list ->
                  'a list list
  (* a "topological sort" that sorts the graph into topologically ordered
     strongly connected components, using Tarjan's algorithm.  *)

end

structure Topo_Sort : TOPO_SORT =
struct

fun dfs_finishes (cmp, neighbours) nodes = let
  datatype 'a action = Visit of 'a | Finish of 'a
  fun recurse visited result actlist =
      case actlist of
        [] => result
      | Visit n :: rest => if Binaryset.member(visited, n) then
                             recurse visited result rest
                           else let
                               val ns = map Visit (neighbours n)
                             in
                               recurse (Binaryset.add(visited, n))
                                       result
                                       (ns @ (Finish n :: rest))
                             end
      | Finish n :: rest => recurse visited (n::result) rest
in
  recurse (Binaryset.empty cmp) [] (map Visit nodes)
end

fun fcons _ [] = raise Fail "Should never happen"
  | fcons x (h::t) = (x::h) :: t
fun dfs_trees (cmp, neighbours) nodes = let
  datatype 'a action = Visit of 'a | Initial of 'a
  fun recurse visited result actlist =
      case actlist of
        [] => result
      | Initial n :: rest => if Binaryset.member(visited,n) then
                               recurse visited result rest
                             else
                               recurse (Binaryset.add(visited, n))
                                       ([n] :: result)
                                       (map Visit (neighbours n) @ rest)
      | Visit n :: rest => if Binaryset.member(visited, n) then
                             recurse visited result rest
                           else
                             recurse (Binaryset.add(visited, n))
                                     (fcons n result)
                                     (map Visit (neighbours n) @ rest)
in
  recurse (Binaryset.empty cmp) [] (map Initial nodes)
end

fun topo_sort {cmp, graph, converse} nodes =
    dfs_trees (cmp, converse) (dfs_finishes (cmp, graph) nodes)


(*
fun ns 0 = [1]
  | ns 1 = [2,3]
  | ns 2  = []
  | ns 3 = [5,7]
  | ns 4 = []
  | ns 5 = [8,9]
  | ns 6 = []
  | ns 7 = [3,4,6]
  | ns 8 = [5]
  | ns 9 = [];
fun ns' 0 = []
  | ns' 1 = [0]
  | ns' 2 = [1]
  | ns' 3 = [1,7]
  | ns' 4 = [7]
  | ns' 5 = [3,8]
  | ns' 6 = [7]
  | ns' 7 = [3]
  | ns' 8 = [5]
  | ns' 9 = [5];

fun eg235 n =
    case n of
      1 => [2]
    | 2 => [3,5,6]
    | 3 => [4,7]
    | 4 => [3,8]
    | 5 => [1,6]
    | 6 => [7]
    | 7 => [6,8]
    | 8 => [8]
fun eg235' n =
    case n of
      1 => [5]
    | 2 => [1]
    | 3 => [2,4]
    | 4 => [3]
    | 5 => [2]
    | 6 => [2,5,7]
    | 7 => [3,6]
    | 8 => [8]

val sscs = dfs_trees (Int.compare, eg235')
                     (dfs_finishes (Int.compare, eg235) [1,2,3,4,5,6,7,8])
*)
end; (* struct *)
