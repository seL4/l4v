(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*********************************************************************************************************************)
(*                                                                                                                   *)
(*  This file contains the functions building the tool that translates AUTHORITY GRAPHS into INFOFLOW POLICY GRAPHS  *)
(*                                                                                                                   *)
(*********************************************************************************************************************)


#open "stack";;

(* We define type auth, describing the different authority labels *)

type auth = Read|Write|Receive|ASyncSend|SyncSend|Control|Reset|ASIDPodMapsASID;;


(*********************************************************************************************************************)


(* We define a bunch of elementary functions *)


(* is_in g x checks whether x is an element of the list g *)

let rec is_in g x= match g with
|[] -> false
|a::l -> (a=x)||(is_in l x);;



(* simp_list l deletes elements in l so that every element does appear only once in the end *)

let rec simp_list l = match l with
|[] -> []
|a::list -> if (is_in list a) then (simp_list list) else a::(simp_list list);;



(* map f l maps f to every element of the list l *)

let rec map f = function
|[] -> []
|a::l -> (f a)::(map f l);;



(* unite l, where l is a 'a list list, appends all the list in l to give back a single list *)

let rec unite = function
|[] -> []
|a::l->a@(unite l);;



(* fixpoint f x does a fixpoint computation on x *)
(* Simplification is necessary on (f x) for the step. We do it on x to ensure termination *)

let rec fixpoint f x =
let a = simp_list x and b = simp_list (f x) in match (a=b) with
|true -> a
|false -> fixpoint f b;;



(* is_in_list2 g x, where x = (u,e,l) is of type ('a,auth,'a list), checks if there is an element a in the third field of x such that the edge (u,e,a) is in g *)

let rec is_in_list2 g x = match x with
|(_,_,[])-> false
|(i,j,a::l)-> is_in g (i,j,a) || is_in_list2 g (i,j,l);;



(* is_in_such g f checks if there is an element x in g such that (f g) holds *)

let rec is_in_such g f = match g with
|[] -> false
|(t::l) -> (is_in g t && f t)||is_in_such l f;;



(* those_is_in_such2 g f grabs all the elements x in l such that (f x) holds *)

let rec those_is_in_such2 g f = match g with
  |[] -> []
  |a::l -> if (is_in g a && f a) then a::(those_is_in_such2 l f) else (those_is_in_such2 l f);;



(* inter_non_empty l1 l2 checks if there is an element both in l1 and l2 *)

let rec inter_non_empty l1 l2 = match l1 with
|[] -> false
|(a::l) -> is_in l2 a || inter_non_empty l l2;;



(* nodes g returns the list of all nodes in the graph g *)
(* We simplify it so that every node only appears once *)

let rec nodes g =
  let rec nodes_aux g = match g with
    |[] -> []
    |(a,auth,b)::l->a::b::(nodes_aux l)
  in simp_list (nodes_aux g);;


(*********************************************************************************************************************)


(* add_selfedges g adds the self-edges to autority graph g *)

let rec add_selfedges g =
  let rec add_selfedge l x = match l with
    |[] -> []
    |a::l -> (x,a,x)::(add_selfedge l x)
  in let authorities = [Read;Write;Receive;ASyncSend;SyncSend;Control;Reset;ASIDPodMapsASID]
  in unite (map (add_selfedge authorities) (nodes g));;


(*********************************************************************************************************************)


(* subjectReadsp g l x acc is the function that checks is x is in the "subjectReads g l" set, where acc is that set during the fixpoint computation *)
(* NB : some rules are particular cases, only useful if the self-edges have been ommitted *)

let subjectReadsp g l x acc =
  (l=x)||
  is_in g (l,Read,x)||
  is_in g (l,Receive,x)||
  is_in g (l,SyncSend,x)||
  is_in_such acc (fun t -> is_in g (t, Read, x))||
   (
     is_in_such acc (fun t -> is_in g (t,SyncSend, x) || is_in g (t, Receive,x))
       &&
     is_in_such (nodes g) (fun a -> is_in g (a,ASyncSend,x) || is_in g (a,SyncSend,x) || is_in g (a,Reset,x))
   )||
  is_in_such acc (fun b -> is_in g (x,Write,b))||
   (
     let f = (fun ep -> is_in g (x,SyncSend,ep)) in
     is_in_such acc f
      &&
     (let ep_list = those_is_in_such2 acc f in let h = (fun a -> (is_in_list2 g (a,Receive,ep_list) || is_in_list2 g (a,Reset,ep_list))) in
     is_in_such (nodes g) h)
   )||
   (
     let f = (fun ep -> is_in g (x,Receive,ep)) in
     is_in_such acc f
      &&
     (let ep_list = those_is_in_such2 acc f in let h = (fun a -> is_in_list2 g (a,SyncSend,ep_list)) in
     is_in_such (nodes g) h)
   )||
  is_in g (x,Receive,l)||is_in g (x,SyncSend,l)||is_in g (x,Write,l)
;;



(* subjectReads g l computes the list containing the elements of the set "subjectReads g l", via a fixpoint computation *)

let subjectReads g l =
  let subjectReadsq g l ac=
    let rec subjectReads_aux g l node_list acc= match (node_list) with
      |[] -> acc
      |(x::list) -> if (subjectReadsp g l x acc) then x::(subjectReads_aux g l list (x::acc))
                                                 else (subjectReads_aux g l list (acc))
    in simp_list (subjectReads_aux g l (nodes g) ac)
  in fixpoint (subjectReadsq g l) [];;



(* subjectAffectsp g l x acc is the function that checks is x is in the "subjectAffects g l" set, where acc is that set during the fixpoint computation *)
(* NB : some rules are particular cases, only useful if the self-edges have been ommitted *)

let subjectAffectsp g l x =
  (l=x)||
  is_in g (l,Control,x)||
  is_in g (l,Write,x)||
  is_in g (l,Receive,x)||
  is_in g (l,ASyncSend,x)||
  is_in g (l,SyncSend,x)||
  is_in g (l,Reset,x)||
  is_in g (l,ASIDPodMapsASID,x)||
  (
    let f = (fun ep -> is_in g (l,SyncSend,ep)||is_in g (l,ASyncSend,ep) ) in
    is_in_such (nodes g) f
     &&
    (
      let ep_list = those_is_in_such2 (nodes g) f in let h = (fun lp -> is_in_list2 g (lp,Receive,ep_list) && is_in g (lp,Write,x))
    in is_in_such (nodes g) h
    )
  )||
  (
    let f = (fun ep -> is_in g (l,Reset,ep) ) in
    is_in_such (nodes g) f
     &&
    (
      let ep_list = those_is_in_such2 (nodes g) f in let h = (fun lp -> (is_in_list2 g (lp,Receive,ep_list)||is_in_list2 g (lp,SyncSend,ep_list)) && is_in g (lp,Write,x))
    in is_in_such (nodes g) h
    )
  )||
  inter_non_empty
     (those_is_in_such2 (nodes g) (fun ep -> is_in g (l,Receive,ep)) )
     (those_is_in_such2 (nodes g) (fun ep -> is_in g (x,SyncSend,ep)) ) ||
  inter_non_empty
     (those_is_in_such2 (nodes g) (fun ep -> is_in g (l,SyncSend,ep)||is_in g (l,ASyncSend,ep)||is_in g (l,Reset,ep)) )
     (those_is_in_such2 (nodes g) (fun ep -> is_in g (x,Receive,ep)) ) ||
  is_in g (x,SyncSend,l)||
  is_in g (x,Receive,l)||
  inter_non_empty
     (those_is_in_such2 (nodes g) (fun lp -> is_in g (lp,Receive,l)||is_in g (lp,SyncSend,l)) )
     (those_is_in_such2 (nodes g) (fun lp -> is_in g (lp,Write,x)) );;



(* subjectAffects g l computes the list containing the elements of the set "subjectAffects g l", via a fixpoint computation *)

let subjectAffects g l =
  let subjectAffectsq g l ac=
    let rec subjectAffects_aux g l node_list acc= match (node_list) with
      |[] -> []
      |(x::list) -> if (subjectAffectsp g l x) then x::(subjectAffects_aux g l list (x::acc))
                                                 else (subjectAffects_aux g l list acc)
    in simp_list (subjectAffects_aux g l (nodes g) ac)
  in fixpoint (subjectAffectsq g l) [];;



(*********************************************************************************************************************)


(* clear_infoflow g removes all self-edges in the infoflow policy graph g *)

let rec clear_infoflow =function
|[] ->[]
|a::l -> let (p,q)=a in
           if (p=q) then clear_infoflow l
                    else a::(clear_infoflow l);;



(* infoflow g computes the translation of the authority graph g into its infoflow policy without deleting the self edges *)

let infoflow g =
  let rec aux g list l = match list with
    |[] -> []
    |x::li -> let b = inter_non_empty (subjectAffects g l) (subjectReads g x) in
                if b then (l,x)::(aux g li l)
                     else aux g li l
  in let res = map (aux g (nodes g)) (nodes g)
  in unite res;;


(*********************************************************************************************************************)


(* we compute info_flow for several examples *)

(* we define two authority graphs *)

let g1=[("L",Write,"SP");("L",Read,"SP");("L",ASyncSend,"AEP");("H",Read,"SP");("H",Receive,"AEP")];;
let g2=[("T",ASyncSend,"AEP1");("T",ASyncSend,"AEP2");("CTR",Receive,"AEP1");("CTR",Read,"C");("CTR",Write,"C");
        ("C",Read,"CTR");("C",Write,"CTR");("CTR",SyncSend,"EP");("RM",Receive,"EP");("RM",Receive,"AEP2")];;


(* Example 1 *)

nodes g1;;

map (fun l -> subjectReads g2 l) (nodes g2);;
map (fun l-> subjectAffects g2 l) (nodes g2);;

infoflow g1;;

let g1_complete = add_selfedges g1 in infoflow (g1@g1_complete);;

let g1_complete = add_selfedges g1 in clear_infoflow (infoflow (g1@g1_complete));;


(* Example 2 *)

nodes g2;;

map (fun l -> subjectReads g2 l) (nodes g2);;
map (fun l-> subjectAffects g2 l) (nodes g2);;

infoflow g2;;

let g2_complete = add_selfedges g2 in infoflow (g2@g2_complete);;

let g2_complete = add_selfedges g2 in clear_infoflow (infoflow (g2@g2_complete));;


(*********************************************************************************************************************)
(*********************************************************************************************************************)


(* this new section deals with representing the info_flow graphs *)

(* we first implement Tarjan's algorithm to find the partition of a oriented graph into strongly connected components *)


(*********************************************************************************************************************)

(* first some basic functions *)

(* find x t return true if x is in t and else otherwise *)

let find x t =
  let n = vect_length t in
    let rec aux x t i = match (i=n) with
      |true -> false
      |false -> (t.(i) = x) || aux x t (i+1)
  in aux x t 1;;



(* we define the exception NotFound *)

exception NotFound;;



(* find_index x t returns the index of x in t if t contains x, and raises NotFound otherwise *)

let find_index x t=
  let n = vect_length t in
    let rec aux x t i = match (i=n) with
      |true -> raise NotFound
      |false ->  if (t.(i) = x) then i else aux x t (i+1)
  in aux x t 0;;



(* successors g x returns the successors of x in g in an infoflow graph *)

let successors g x =
  let rec aux g x h = match g with
    |[] -> simp_list h
    |(a,c)::l -> if (a=x) then aux l x (c::h) else aux l x h
  in aux g x [];;



(* apply f l applies recursively function f, of type 'a -> Unit, on the elements of l *)

let rec apply f = function
  |[] -> ()
  |a::l -> (f a;apply f l);;


(* nodes_infoflow g computes the list of nodes in the infoflow graph g *)

let rec nodes_infoflow g =
  let rec nodes_aux g = match g with
    |[] -> []
    |(a,b)::l->a::b::(nodes_aux l)
  in simp_list (nodes_aux g);;



(*********************************************************************************************************************)


(* we define the tarjanp function, computing the partition of the infoflow graph g in strongly connected components *)
(* BEWARE : THIS FUNCTION USES GRAPHS LABELLED BY int *)


let tarjanp g =
  let n = list_length (nodes_infoflow g) in
  let num = ref 0 in
  let p = new () in
  let partition = ref [] in
  let numt = make_vect n (-1) in
  let numAccessible = make_vect n (-1) in
  let dans_P = make_vect n false in
  let rec parcours g v = begin
    numt.(v) <- (!num);
    numAccessible.(v) <- (!num);
    num := 1 + (!num);
    push v p;
    dans_P.(v) <- true;
    let l = successors g v in
    let rec aux = function
      |[] -> ()
      |w::rest -> begin
                  if (numt.(w) = -1)
                  then (
                       parcours g w;
                       numAccessible.(v) <- min (numAccessible.(v)) (numAccessible.(w))
                       )
                  else if (dans_P.(w))
                       then numAccessible.(v) <- min (numAccessible.(v)) (numt.(w))
                       else ();
                  aux rest
                  end
    in aux l;
    if (numAccessible.(v) = numt.(v))
    then let C = ref [] in
         let w = ref (-1) in
         begin
         w := pop p;
         dans_P.(!w) <- false;
         C := (!w)::(!C);
         while (v<>(!w)) do
           (
           w := pop p;
           dans_P.(!w) <- false;
           C := (!w)::(!C)
           )
                         done;
    partition := (!C)::(!partition)
         end
 end
  in
  apply (fun v -> (if (numt.(v)=(-1)) then parcours g v)) (nodes_infoflow g);
  !partition;;



(* we define 2 functions mapping the labels in the infoflow graph to int, and back to string *)

let rec string2int_labels name_t = function
|[] -> []
|(x,y)::l -> let i = find_index x name_t in
               let j = find_index y name_t in
               (i,j)::(string2int_labels name_t l);;


let rec int2string_labels name_t = function
|[] -> []
|i::l -> name_t.(i)::(int2string_labels name_t l);;



(* tarjan g, where g is an infoflow graph, computes the partition of g in strongly connected components *)

let tarjan g =
  let n = list_length (nodes_infoflow g) in
  let name_tab = vect_of_list (nodes_infoflow g) in
  let gi = string2int_labels name_tab g in
  let p = tarjanp gi in
  map (int2string_labels name_tab) p;;



(* Examples *)

tarjan (infoflow g1);;
tarjan (infoflow g2);;



(*********************************************************************************************************************)


(* We now build the reduced graph, by building the edges between the new nodes *)

(* exists_edge_info_flow g u v checks whether there is an edge in g from an element of node list u to an element of node list v *)

let rec exists_edge_infoflow g u v = match g with
  |[] -> false
  |(x,y)::l -> ((is_in u x) && (is_in v y))||exists_edge_infoflow l u v;;



(* simp_infoflow g computes the reduced (or simplified) infoflow graph, where the new nodes are the strongly connected components from the original infoflow policy *)

let simp_infoflow g =
  let rec search_edges g u v = match u with
    |[] -> []
    |a::l -> if (exists_edge_infoflow g a v) then (a,v)::(search_edges g l v) else (search_edges g l v)
  in let t = tarjan g in
  simp_list (unite (map (search_edges g t) t));;



(* Examples *)

simp_infoflow (infoflow g1);;
simp_infoflow (infoflow g2);;


clear_infoflow (simp_infoflow (infoflow g1));;
clear_infoflow (simp_infoflow (infoflow g2));;
