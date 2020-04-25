--
-- Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
--
-- SPDX-License-Identifier: GPL-2.0-only
--

module Main (
main
) where

import Data.List ( nub, intersect, intersperse )
import Data.Graph
import Data.Graph.SCC (scc)
import Data.Array

data Auth = Read
          | Write
          | Receive
          | ASyncSend
          | SyncSend
          | Control
          | Reset
          | ASIDPoolMapsASID
          | Grant
          deriving (Eq,Show)

type Authority_edge = (String,Auth,String)
type Authority_graph = [Authority_edge]

type Infoflow_edge = (String,String)
type Infoflow_graph = [Infoflow_edge]

type Infoflow_graph_Int = [(Int,Int)]
type Simp_infoflow_node_Int = [Int]
type Simp_infoflow_Int = [(Simp_infoflow_node_Int,Simp_infoflow_node_Int)]

type Simp_infoflow = [([String],[String])]

-- 'fixpoint f x' computes the least fixed poInt of 'f' by beginning computation in 'x'
fixpoint :: ([String] -> [String]) -> [String] -> [String]
fixpoint f x = y
  where
  a = x
  b = f x
  y = if a==b then b else fixpoint f b

-- 'elem_authority_edge g (a,auth,l)' returns True if there is an edge with label 'auth' from 'a' to an element of 'l' in the authority graph 'g', and False otherwise
elem_authority_edge ::  Authority_graph -> String -> [Auth] -> [String] -> Bool
elem_authority_edge g i j = any (\a -> any (\auth -> (i,auth,a) `elem` g) j)

-- 'Inter_non_empty l1 l2' returns True if l1 and l2 have a common element, and False otherwise
inter_non_empty :: [String] -> [String] -> Bool
inter_non_empty l1 l2 = not (null (l1 `intersect` l2))

-- 'nodes_authority g' returns the list of nodes in authority graph 'g'
nodes_authority :: Authority_graph -> [String]
nodes_authority g = nub (aux g)
  where
    aux :: Authority_graph -> [String]
    aux []             = []
    aux ((a,auth,b):l) = a:b:(aux l)

-- 'add_selfedges_auth g' adds all selfedges to 'g'
add_selfedges_auth :: Authority_graph -> Authority_graph
add_selfedges_auth g = let aux :: [Auth] -> String -> Authority_graph
                           aux [] x    = []
                           aux (a:l) x = (x,a,x):(aux l x) in
                       let authorities = [Read, Write, Receive, ASyncSend, SyncSend, Control, Reset, ASIDPoolMapsASID , Grant] in
                       g ++ (concatMap (aux authorities) (nodes_authority g))

{- 'subjectReadsp g l x nodes_g acc', where 'g' is the authority graph,
                                            'l' the current node,
                                            'x' the node we test,
                                            'nodes_g' the list of nodes in 'g',
                                            'acc' the current version of the 'subjectReads g l' nub (as a list), used for the fixed poInt computation,
   returns True if there is a rule including 'x' in 'subjectReads g l', and False otherwise -}
subjectReadsp :: Authority_graph -> String -> String -> [String] -> [String] -> Bool
subjectReadsp g l x nodes_g acc =
   or [ l == x
      , any (\(l',auth,x') -> (l == l' && x == x' && (auth `elem` [Read, Receive, SyncSend]))) g
      , any (\t -> (t,Read,x) `elem` g) acc
      , (
          any (\t -> elem_authority_edge g t [SyncSend,Receive] [x]) acc
          &&
          any (\a -> elem_authority_edge g a [ASyncSend,SyncSend,Reset] [x]) nodes_g
        )
      , any (\b -> (x,Write,b) `elem` g) acc
      , (
          let ep_list = filter (\ep -> elem (x,SyncSend,ep) g) acc
              h a = elem_authority_edge g a [Receive,Reset] ep_list
          in not (null ep_list) && any h nodes_g
        )
      , (
          let ep_list = filter (\ep -> elem (x,Receive,ep) g) acc
              h = (\a -> elem_authority_edge g a [SyncSend] ep_list )
          in not (null ep_list) && any h nodes_g
        )
      ]


-- 'subjectReads g l nodes_g' returns the 'subjectReads g l' nub, as a list
subjectReads :: Authority_graph -> String -> [String] -> [String]
subjectReads g l nodes_g = fixpoint (nub . aux nodes_g) []
  where
    aux :: [String] -> [String] -> [String]
    aux [] acc       = acc
    aux (x:list) acc = aux list (if subjectReadsp g l x nodes_g acc then x:acc else acc)


{- 'subjectAffectsp g l x nodes_g', where 'g' is the authority graph,
                                            'l' the current node,
                                            'x' the node we test,
                                            'nodes_g' the list of nodes in 'g',on,
   returns True if there is a rule including 'x' in 'subjectAffects g l', and False otherwise -}

subjectAffectsp :: Authority_graph -> String -> String -> [String] -> Bool
subjectAffectsp g l x nodes_g =
  or [ l == x
     , elem_authority_edge g l [Write, Receive, ASyncSend, SyncSend, Control, Reset, ASIDPoolMapsASID] [x]
     , (
         let ep_list = filter (\ep -> elem_authority_edge g l [ASyncSend,SyncSend] [ep]) nodes_g
             h = (\lp -> elem_authority_edge g lp [Receive] ep_list && (lp,Write,x) `elem` g)
         in not (null ep_list) && any h nodes_g
       )
     , (
         let ep_list = filter (\ep -> (l,Reset,ep) `elem` g ) nodes_g
             h = (\lp -> elem_authority_edge g lp [Receive,SyncSend] ep_list && (lp,Write,x) `elem` g )
         in not (null ep_list) && any h nodes_g
       )
     , inter_non_empty
          (filter (\ep -> elem (l,Receive,ep) g) nodes_g)
          (filter (\ep -> elem (x,SyncSend,ep) g) nodes_g)
          ]

-- 'subjectAffects g l nodes_g' returns the 'subjectAffects g l' nub, as a list
subjectAffects :: Authority_graph -> String -> [String] -> [String]
subjectAffects g l nodes_g = fixpoint (nub . aux nodes_g) []
  where
    aux :: [String] -> [String] -> [String]
    aux [] acc       = acc
    aux (x:list) acc = aux list (if subjectAffectsp g l x nodes_g then x:acc else acc)

-- 'infoflow g' computes the infoflow graph from authority graph 'g'
infoflow :: Authority_graph -> Infoflow_graph
infoflow g = let nodes_g = nodes_authority g in
             let aux :: Authority_graph -> [String] -> String -> [Infoflow_edge]
                 aux g [] l = []
                 aux g (x:list) l = let b = inter_non_empty (subjectAffects g l nodes_g) (subjectReads g x nodes_g) in
                                    if b then (l,x):(aux g list l) else aux g list l
             in concatMap (aux g nodes_g) nodes_g

-- 'del_selfedges_infoflow g' deletes the selfedges in an infoflow-type graph g, simplified or not
del_selfedges_infoflow :: (Eq a) => [(a,a)] -> [(a,a)]
del_selfedges_infoflow = filter (\(p,q) -> p/=q)

-- 'nodes_infoflow g' returns the list of nodes in the infoflow graph 'g'
nodes_infoflow :: Infoflow_graph -> [String]
nodes_infoflow g = let aux :: Infoflow_graph -> [String]
                       aux [] = []
                       aux ((a,b):l) = a:b:(aux l)
                   in nub (aux g)

-- add_scheduler_infoflow g' adds all edges from a new node ('Scheduler') to every node in g
add_scheduler_infoflow :: Infoflow_graph -> Infoflow_graph
add_scheduler_infoflow g = ("Scheduler","Scheduler") : g ++ (map (\a -> ("Scheduler",a)) . nodes_infoflow) g

-------------------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------------------


--THIS PART DEALS WITH SIMPLIFYING THE INFOFLOW GRAPH, BY GATHERING NODES IN THE SAME STRONGLY CONNECTED COMPONENT TOGETHER

-- ##not commented part : begin##
list_index :: (Eq a) => a -> [a] -> Int
list_index x [] = -1
list_index x (y:l) = if (y==x) then 1 else (1 + list_index x l)


stringToIntMap :: [String] -> (String -> [String] -> Int,[String] -> Int -> String)
stringToIntMap l = (f,g)
  where f s l = list_index s l
        g l n = l!!(n-1)


node_sup :: Infoflow_graph_Int -> Int
node_sup g = let aux [] n        = n
                 aux ((a,b):l) n = aux l (max (max a b) n)
             in aux g 0


mapInfoflowStringToInt :: (String -> Int) -> Infoflow_graph -> Infoflow_graph_Int
mapInfoflowStringToInt f []        = []
mapInfoflowStringToInt f ((a,b):l) = (f a,f b):(mapInfoflowStringToInt f l)


ipgToGraph :: Infoflow_graph_Int -> Graph
ipgToGraph g = let aux :: [(Int,[Int])] -> (Int,Int) -> [(Int,[Int])]
                   aux [] (a,b)        = [(a,[b])]
                   aux ((x,m):l) (a,b) = if (a==x)
                                           then (a,b:m):l
                                           else (x,m):(aux l (a,b))
               in
               let aux2 :: [(Int,[Int])] -> [(Int,Int)] -> [(Int,[Int])]
                   aux2 l []    = l
                   aux2 l (a:m) = aux2 (aux l a) m
               in array (1,node_sup g) (aux2 [] g)


mapSipgIntToString :: (Int -> String) -> Simp_infoflow_Int -> Simp_infoflow
mapSipgIntToString f []        = []
mapSipgIntToString f ((a,b):g) = (map f a,map f b):(mapSipgIntToString f g)


nodes_sipg :: [(Int,[Int])] -> [Simp_infoflow_node_Int]
nodes_sipg []        = []
nodes_sipg ((a,b):l) = b:(nodes_sipg l)


exist_edge_ipg :: Infoflow_graph_Int -> Simp_infoflow_node_Int -> Simp_infoflow_node_Int -> Bool
exist_edge_ipg [] u v        = False
exist_edge_ipg ((a,b):l) u v =  (elem a u && elem b v) || exist_edge_ipg l u v

-- ##not commented part : end##

-- 'simp_infoflow g' returns the simplified infoflow graph, where nodes are now the strongly connected components (SCC) of 'g', and edges are defined by : there is an edge from 'SCC a' to 'SCC b' if there is an edge from an element of 'a' to an element of 'b'
simp_infoflow :: Infoflow_graph -> Simp_infoflow
simp_infoflow g = y
  where
    nodes_if = nodes_infoflow g
    (f,h) = stringToIntMap nodes_if
    g_Int = mapInfoflowStringToInt (\x -> f x nodes_if) g
    search_edges :: Infoflow_graph_Int -> [Simp_infoflow_node_Int] -> Simp_infoflow_node_Int -> Simp_infoflow_Int
    search_edges g [] v    = []
    search_edges g (a:l) v = if (exist_edge_ipg g a v)
                               then (a,v):(search_edges g l v)
                               else search_edges g l v
    t = nodes_sipg ( fst (Data.Graph.SCC.scc (ipgToGraph g_Int)))
    sipg_Int = concat (map (search_edges g_Int t) t)
    y = mapSipgIntToString (h nodes_if) sipg_Int

-- 'simplified_infoflow_nodeToString l' is a function used for display, collapsing a String list Into a single String, separating elements with a ','
simplified_infoflow_nodeToString :: [String] -> String
simplified_infoflow_nodeToString = concat . intersperse ","

-- 'graphviz_input_simplified_infoflow g' returns a String containing the graphviz code to display the simplified infoflo graph
graphviz_input_simplified_infoflow :: Simp_infoflow -> String
graphviz_input_simplified_infoflow g = let aux []        = ""
                                           aux ((a,b):l) = "<"++ (simplified_infoflow_nodeToString a)++"> -> <"++(simplified_infoflow_nodeToString b)++">;"++ "\n"++(aux l) in
                                       "digraph G {"++"\n"++(aux g)++"}"++"\n"

-- 'acces_to_infoflow g b' computes the simplified infoflow graph from authority graph 'g'
-- if b == True, then the Scheduler is added
authority_to_infoflow :: Authority_graph -> Bool -> Simp_infoflow
authority_to_infoflow g b = let g_complete = add_selfedges_auth g in
                            if b
                              then let g_infoflow = add_scheduler_infoflow (infoflow g_complete) in simp_infoflow g_infoflow
                              else simp_infoflow (infoflow g_complete)

------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------

-- THIS PART DEALS WITH WELLFORMEDNESS OF AN AUTHORITY GRAPH

-- 'condition1 aag agent l' checks that if there is a Control-edge from 'agent' to an element 'a' of 'l' in 'aag', then 'a==agent'
condition1 :: Authority_graph -> String -> [String] -> Bool
condition1 aag agent = all (\a -> notElem (agent,Control,a) aag || agent==a)

-- 'condition2 aag agent l' checks that every selfedges of 'agent' labeled by an element of 'l' is in 'aag'
condition2 :: Authority_graph -> String -> [Auth] -> Bool
condition2 aag agent = all (\a -> elem (agent,a,agent) aag)

-- 'condition3 aag' checks that '(s,Grant,ep) in aag & (r,Receive,ep) in aag --> (r,Control,s) & (s,Control,r)' for every r,s,ep in aag
condition3 :: Authority_graph -> Bool
condition3 aag = res
  where
    aux aag r s= all (\ep -> or [ notElem (s,Grant,ep) aag
                                , notElem (r,Receive,ep) aag
                                , elem (s,Control,r) aag && elem (r,Control,s) aag
                                ])
    nodes = nodes_authority aag
    f r s = aux aag r s nodes
    g r = all (\x -> x==True) (map (f r) nodes)
    res = all (\x -> x==True) (map g nodes)

-- 'wellformed aag' checks that 'aag' is wellformed
wellformed :: Authority_graph -> Bool
wellformed aag = res
  where
    nodes = nodes_authority aag
    authorities = [Read, Write, Receive, ASyncSend, SyncSend, Control, Reset, ASIDPoolMapsASID, Grant]
    res = and [ all (\agent -> condition1 aag agent nodes) nodes
              , all (\agent -> condition2 aag agent authorities) nodes
              , condition3 aag
              ]


-- ## IN PROGRESS

{-

condition1_debug :: Authority_graph -> String -> [String] -> Bool
condition1_debug aag agent []    = True
condition1_debug aag agent (a:l) = if not (elem (agent, Control,a) agg) then
--(not (elem (agent,Control,a) aag) || agent==a) && condition1_debug aag agent l


condition2_debug :: Authority_graph -> String -> [Auth] -> Bool
condition2_debug aag agent []    = True
condition2_debug aag agent (a:l) = elem (agent,a,agent) aag && condition2_debug aag agent l


condition3_debug :: Authority_graph -> Bool
condition3_debug aag = let aux aag s r []     = True
                           aux aag s r (ep:l) = (not (
                                                 elem (s,Grant,ep) aag
                                                 &&
                                                 elem (r,Receive,ep) aag
                                                )
                                                ||
                                                (
                                                 elem (s,Control,r) aag
                                                 &&
                                                 elem (r,Control,s) aag
                                                )
                                                ) && aux aag s r l in
                        let nodes = nodes_authority aag in
                        let f r s = aux aag r s nodes in
                        let g r = all (\x -> x==True) (map (f r) nodes) in
                        all (\x -> x==True) (map g nodes)


wellformed_debug :: Authority_graph -> Bool
wellformed_debug aag = let nodes = nodes_authority aag in
                       let authorities = [Read, Write, Receive, ASyncSend, SyncSend, Control, Reset, ASIDPoolMapsASID, Grant] in
                       all (\agent -> condition1_debug aag agent nodes) nodes &&
                       all (\agent -> condition2_debug aag agent authorities) nodes &&
                       condition3_debug aag



-}




main = do

-- We treat example 1 in infoflow/PolicyExample.thy

  let g1 = [("T",ASyncSend,"AEP1"),("T",ASyncSend,"AEP2"),("CTR",Receive,"AEP1"),("CTR",Read,"C"),("CTR",Write,"C"),("C",Read,"CTR"),("C",Write,"CTR"),("CTR",SyncSend,"EP"),("RM",Receive,"EP"),("RM",Receive,"AEP2")]
  let g1_complete = add_selfedges_auth g1
  print g1
  print ("**********************")
  print (infoflow g1_complete)
  print ("**********************")
  print (simp_infoflow (infoflow g1_complete))
  print ("**********************")
  print (authority_to_infoflow g1 True)
  print ("**********************")
  putStr (graphviz_input_simplified_infoflow (authority_to_infoflow g1 True))
  print ("##############################")


-- We treat example 1 in infoflow/PolicyExample.thy and we add the Scheduler

  let g1' = [("T",ASyncSend,"AEP1"),("T",ASyncSend,"AEP2"),("CTR",Receive,"AEP1"),("CTR",Read,"C"),("CTR",Write,"C"),("C",Read,"CTR"),("C",Write,"CTR"),("CTR",SyncSend,"EP"),("RM",Receive,"EP"),("RM",Receive,"AEP2")]
  let g1_complete' = add_selfedges_auth g1'
  print g1'
  print ("**********************")
  print (infoflow g1_complete')
  print ("**********************")
  print (simp_infoflow (infoflow g1_complete'))
  print ("**********************")
  print (authority_to_infoflow g1' False)
  print ("**********************")
  putStr (graphviz_input_simplified_infoflow (authority_to_infoflow g1' False))
  print ("##############################")


-- We treat example 2 in infoflow/PolicyExample.thy

  let g2 = [("Low",Read,"SharedPage"),("Low",Write,"SharedPage"),("Low",ASyncSend,"AEP"),("High",Read,"SharedPage"),("High",Receive,"AEP")]
  let g2_complete = add_selfedges_auth g2
  print g2
  print ("**********************")
  print (infoflow g2_complete)
  print ("**********************")
  print (simp_infoflow (infoflow g2_complete))
  print ("**********************")
  print (authority_to_infoflow g2 False)
  print ("**********************")
  putStr (graphviz_input_simplified_infoflow (authority_to_infoflow g2 False))
  print ("##############################")


-- We treat the example in infoflow/ExampleSystemPolicyFlows

  let g3 = [("UT3",SyncSend,"EP3"),("UT3",Reset,"EP3"),("T3",Receive,"EP3"),("T3",Reset,"EP3"),("IRQ",Read,"IRQ")]
  let g3_complete = add_selfedges_auth g3
  print g3
  print ("**********************")
  print (infoflow g3_complete)
  print ("**********************")
  print (simp_infoflow (infoflow g3_complete))
  print ("**********************")
  print (authority_to_infoflow g3 True)
  print ("**********************")
  putStr (graphviz_input_simplified_infoflow (authority_to_infoflow g3 True))
  print ("##############################")


  let g4 = [("A",Read,"X"),("B",ASIDPoolMapsASID,"X"),("B",Read,"Y"),("C",ASIDPoolMapsASID,"Y"),("C",Read,"Z"),("A",ASIDPoolMapsASID,"Z")]
  let g4_complete = add_selfedges_auth g4
  print g4
  print ("**********************")
  print (infoflow g4_complete)
  print ("**********************")
  print (simp_infoflow (infoflow g4_complete))
  print ("**********************")
  print (authority_to_infoflow g4 False)
  print ("**********************")
  putStr (graphviz_input_simplified_infoflow (authority_to_infoflow g4 False))
  print ("##############################")


  let authorities = [Read, Write, Receive, ASyncSend, SyncSend, Control, Reset, ASIDPoolMapsASID, Grant]
  print (condition1 g2_complete "Low" (nodes_authority g2))
  print (condition2 g2_complete "Low" authorities)
  print (condition3 g2_complete)
  print (wellformed g2_complete)


