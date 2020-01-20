(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory StaticFun
imports
  Main
begin

datatype ('a, 'b) Tree = Node 'a 'b "('a, 'b) Tree" "('a, 'b) Tree" | Leaf

primrec
  lookup_tree :: "('a, 'b) Tree \<Rightarrow> ('a \<Rightarrow> 'c :: linorder) \<Rightarrow> 'a \<Rightarrow> 'b option"
where
  "lookup_tree Leaf fn x = None"
| "lookup_tree (Node y v l r) fn x = (if fn x = fn y then Some v
                                      else if fn x < fn y then lookup_tree l fn x
                                      else lookup_tree r fn x)"

definition optional_strict_range :: "('a :: linorder) option \<Rightarrow> 'a option \<Rightarrow> 'a set"
where
  "optional_strict_range x y = {z. (x = None \<or> the x < z) \<and> (y = None \<or> z < the y)}"

lemma optional_strict_range_split:
  "z \<in> optional_strict_range x y
    \<Longrightarrow> optional_strict_range x (Some z) = ({..< z} \<inter> optional_strict_range x y)
        \<and> optional_strict_range (Some z) y = ({z <..} \<inter> optional_strict_range x y)"
  by (auto simp add: optional_strict_range_def)

lemma optional_strict_rangeI:
  "z \<in> optional_strict_range None None"
  "z < y \<Longrightarrow> z \<in> optional_strict_range None (Some y)"
  "x < z \<Longrightarrow> z \<in> optional_strict_range (Some x) None"
  "x < z \<Longrightarrow> z < y \<Longrightarrow> z \<in> optional_strict_range (Some x) (Some y)"
  by (simp_all add: optional_strict_range_def)

definition
  tree_eq_fun_in_range :: "('a, 'b) Tree \<Rightarrow> ('a \<Rightarrow> 'c :: linorder) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> 'c set \<Rightarrow> bool"
where
 "tree_eq_fun_in_range T ord f S \<equiv> \<forall>x. (ord x \<in> S) \<longrightarrow> f x = lookup_tree T ord x"

lemma tree_eq_fun_in_range_from_def:
  "\<lbrakk> f \<equiv> lookup_tree T ord \<rbrakk>
    \<Longrightarrow> tree_eq_fun_in_range T ord f (optional_strict_range None None)"
  by (simp add: tree_eq_fun_in_range_def)

lemma tree_eq_fun_in_range_split:
  "tree_eq_fun_in_range (Node z v l r) ord f (optional_strict_range x y)
    \<Longrightarrow> ord z \<in> optional_strict_range x y
    \<Longrightarrow> tree_eq_fun_in_range l ord f (optional_strict_range x (Some (ord z)))
        \<and> f z = Some v
        \<and> tree_eq_fun_in_range r ord f (optional_strict_range (Some (ord z)) y)"
  apply (simp add: tree_eq_fun_in_range_def optional_strict_range_split)
  apply fastforce
  done

ML \<open>

structure StaticFun = struct

(* Actually build the tree -- theta (n lg(n)) *)
fun build_tree' _ mk_leaf [] = mk_leaf
  | build_tree' mk_node mk_leaf xs = let
    val len = length xs
    val (ys, zs) = chop (len div 2) xs
  in case zs of [] => error "build_tree': impossible"
    | ((a, b) :: zs) => mk_node a b (build_tree' mk_node mk_leaf ys)
        (build_tree' mk_node mk_leaf zs)
  end

fun build_tree ord xs = case xs of [] => error "build_tree : empty"
  | (idx, v) :: _ => let
    val idxT = fastype_of idx
    val vT = fastype_of v
    val treeT = Type (@{type_name StaticFun.Tree}, [idxT, vT])
    val mk_leaf = Const (@{const_name StaticFun.Leaf}, treeT)
    val node = Const (@{const_name StaticFun.Node},
        idxT --> vT --> treeT --> treeT --> treeT)
    fun mk_node a b l r = node $ a $ b $ l $ r
    val lookup = Const (@{const_name StaticFun.lookup_tree},
        treeT --> fastype_of ord --> idxT
            --> Type (@{type_name option}, [vT]))
  in
    lookup $ (build_tree' mk_node mk_leaf xs) $ ord
  end

fun define_partial_map_tree name mappings ord ctxt = let
    val tree = build_tree ord mappings
  in Local_Theory.define
    ((name, NoSyn), ((Thm.def_binding name, []), tree)) ctxt
    |> apfst (apsnd snd)
  end

fun prove_partial_map_thms thm ctxt = let
    val init = thm RS @{thm tree_eq_fun_in_range_from_def}
    fun rec_tree thm = case Thm.concl_of thm of
    @{term Trueprop} $ (Const (@{const_name tree_eq_fun_in_range}, _)
        $ (Const (@{const_name Node}, _) $ z $ v $ _ $ _) $ _ $ _ $ _) => let
        val t' = thm RS @{thm tree_eq_fun_in_range_split}
        val solve_simp_tac = SUBGOAL (fn (t, i) =>
            (simp_tac ctxt THEN_ALL_NEW SUBGOAL (fn (t', _) =>
                raise TERM ("prove_partial_map_thms: unsolved", [t, t']))) i)
        val r = t' |> (resolve_tac ctxt @{thms optional_strict_rangeI}
            THEN_ALL_NEW solve_simp_tac) 1 |> Seq.hd
        val l = r RS @{thm conjunct1}
        val kr = r RS @{thm conjunct2}
        val k = kr RS @{thm conjunct1}
        val r = kr RS @{thm conjunct2}
      in rec_tree l @ [((z, v), k)] @ rec_tree r end
    | _ => []
  in rec_tree init end

fun define_tree_and_save_thms name names mappings ord exsimps ctxt = let
    val ((tree, def_thm), ctxt) = define_partial_map_tree name mappings ord ctxt
    val thms = prove_partial_map_thms def_thm (ctxt addsimps exsimps)
    val (idents, thms) = map_split I thms
    val _ = map (fn ((x, y), (x', y')) => (x aconv x' andalso y aconv y')
        orelse raise TERM ("define_tree_and_thms: different", [x, y, x', y']))
        (mappings ~~ idents)
    val (_, ctxt) = Local_Theory.notes
        (map (fn (s, t) => ((Binding.name s, []), [([t], [])]))
        (names ~~ thms)) ctxt
  in (tree, ctxt) end

fun define_tree_and_thms_with_defs name names key_defs opt_values ord ctxt = let
    val data = names ~~ (key_defs ~~ opt_values)
        |> map_filter (fn (_, (_, NONE)) => NONE | (nm, (thm, SOME v))
            => SOME (nm, (fst (Logic.dest_equals (Thm.concl_of thm)), v)))
    val (names, mappings) = map_split I data
  in define_tree_and_save_thms name names mappings ord key_defs ctxt end

end

\<close>

(* testing

local_setup {* StaticFun.define_tree_and_save_thms @{binding tree}
  ["one", "two", "three"]
  [(@{term "Suc 0"}, @{term "Suc 0"}),
    (@{term "2 :: nat"}, @{term "15 :: nat"}),
    (@{term "3 :: nat"}, @{term "1 :: nat"})]
  @{term "id :: nat \<Rightarrow> nat"}
  #> snd
*}
print_theorems

*)

end
