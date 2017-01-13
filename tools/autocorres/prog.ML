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
 * Abstract data structures for representing and performing basic analysis on
 * programs.
 *)
structure Prog =
struct

(* Convenience abbreviations for set manipulation. *)
infix 1 INTER MINUS UNION
val empty_set = Varset.empty
val make_set = Varset.make
val union_sets = Varset.union_sets
fun (a INTER b) = Varset.inter a b
fun (a MINUS b) = Varset.subtract b a
fun (a UNION b) = Varset.union a b

(*
 * A parsed program.
 *
 *   "'a" is a generic type that appears at every node.
 *
 *   "'e" is an expression type that appears once for each expression.
 *
 *   "'m" is a modification type that appears only in modification clauses.
 *
 *   "'c" is meta-data associated with calls.
 *)
datatype ('a, 'e, 'm, 'c) prog =
    Init of ('a * 'm)
  | Modify of ('a * 'e * 'm)
  | Guard of ('a * 'e)
  | Throw of 'a
  | Call of ('a * 'e list * 'e * 'm * 'c)
  | Spec of ('a * 'e)
  | Fail of 'a
  | While of ('a * 'e * ('a, 'e, 'm, 'c) prog)
  | Condition of ('a * 'e * ('a, 'e, 'm, 'c) prog * ('a, 'e, 'm, 'c) prog)
  | Seq of ('a * ('a, 'e, 'm, 'c) prog * ('a, 'e, 'm, 'c) prog)
  | Catch of ('a * ('a, 'e, 'm, 'c) prog * ('a, 'e, 'm, 'c) prog)
  | RecGuard of ('a * ('a, 'e, 'm, 'c) prog)

datatype call_type = DecMeasure | NewMeasure

(* Extract the data associated with the node. *)
fun get_node_data prog =
  case prog of
      Init (a, _) => a
    | Modify (a, _, _) => a
    | Guard (a, _) => a
    | Throw a => a
    | Call (a, _, _, _, _) => a
    | Spec (a, _) => a
    | Fail a => a
    | While (a, _, _) => a
    | Condition (a, _, _, _) => a
    | Seq (a, _, _) => a
    | Catch (a, _, _) => a
    | RecGuard (a, _) => a

(* Merge data payloads of two structurally identical programs. *)
fun zip_progs progA progB =
  case (progA, progB) of
      (Init (a1, m1), Init (a2, m2)) =>
        Init ((a1, a2), (m1, m2))
    | (Modify (a1, e1, m1), Modify (a2, e2, m2)) =>
        Modify ((a1, a2), (e1, e2), (m1, m2))
    | (Guard (a1, e1), Guard (a2, e2)) =>
        Guard ((a1, a2), (e1, e2))
    | (Throw a1, Throw a2) =>
        Throw ((a1, a2))
    | (Call (a1, e1, ee1, m1, c1), Call (a2, e2, ee2, m2, c2)) =>
        Call ((a1, a2), Utils.zip e1 e2, (ee1, ee2), (m1, m2), (c1, c2))
    | (Spec (a1, e1), Spec (a2, e2)) =>
        Spec ((a1, a2), (e1, e2))
    | (Fail a1, Fail a2) =>
        Fail ((a1, a2))
    | (While (a1, e1, body1), While (a2, e2, body2)) =>
        While ((a1, a2), (e1, e2), zip_progs body1 body2)
    | (Condition (a1, e1, lhs1, rhs1), Condition (a2, e2, lhs2, rhs2)) =>
        Condition ((a1, a2), (e1, e2), zip_progs lhs1 lhs2, zip_progs rhs1 rhs2)
    | (Seq (a1, lhs1, rhs1), Seq (a2, lhs2, rhs2)) =>
        Seq ((a1, a2), zip_progs lhs1 lhs2, zip_progs rhs1 rhs2)
    | (Catch (a1, lhs1, rhs1), Catch (a2, lhs2, rhs2)) =>
        Catch ((a1, a2), zip_progs lhs1 lhs2, zip_progs rhs1 rhs2)
    | (RecGuard (a1, body1), RecGuard (a2, body2)) =>
        RecGuard ((a1, a2), zip_progs body1 body2)
    | other =>
        Utils.invalid_input "structurally identical programs" (@{make_string} other)

(* Map the data payloads of a given program. *)
fun map_prog node_fn expr_fn mod_fn call_fn prog =
  case prog of
      Init (a, m) => Init (node_fn a, mod_fn m)
    | Modify (a, e, m) => Modify (node_fn a, expr_fn e, mod_fn m)
    | Guard (a, e) => Guard (node_fn a, expr_fn e)
    | Throw a => Throw (node_fn a)
    | Call (a, e, ee, m, c) => Call (node_fn a, map expr_fn e, expr_fn ee, mod_fn m, call_fn c)
    | Spec (a, e) => Spec (node_fn a, expr_fn e)
    | Fail a => Fail (node_fn a)
    | While (a, e, body) =>
        While (node_fn a, expr_fn e, map_prog node_fn expr_fn mod_fn call_fn body)
    | Condition (a, e, lhs, rhs) =>
        Condition (node_fn a, expr_fn e,
            map_prog node_fn expr_fn mod_fn call_fn lhs,
            map_prog node_fn expr_fn mod_fn call_fn rhs)
    | Seq (a, lhs, rhs) =>
        Seq (node_fn a,
            map_prog node_fn expr_fn mod_fn call_fn lhs,
            map_prog node_fn expr_fn mod_fn call_fn rhs)
    | Catch (a, lhs, rhs) =>
        Catch (node_fn a,
            map_prog node_fn expr_fn mod_fn call_fn lhs,
            map_prog node_fn expr_fn mod_fn call_fn rhs)
    | RecGuard (a, body) =>
        RecGuard (node_fn a, map_prog node_fn expr_fn mod_fn call_fn body)

(* Fold nodes of the program together in pre-order. *)
fun fold_prog node_fn expr_fn mod_fn call_fn prog v =
  case prog of
      Init (a, m) => (node_fn a #> mod_fn m) v
    | Modify (a, e, m) => (node_fn a #> expr_fn e #> mod_fn m) v
    | Guard (a, e) => (node_fn a #> expr_fn e) v
    | Throw a => (node_fn a) v
    | Call (a, e, ee, m, c) =>
        (node_fn a #> fold expr_fn e #> expr_fn ee #> mod_fn m #> call_fn c) v
    | Spec (a, e) => (node_fn a #> expr_fn e) v
    | Fail a => (node_fn a) v
    | While (a, e, body) =>
        (node_fn a #> expr_fn e
            #> fold_prog node_fn expr_fn mod_fn call_fn body) v
    | Condition (a, e, lhs, rhs) =>
        (node_fn a #> expr_fn e
            #> fold_prog node_fn expr_fn mod_fn call_fn lhs
            #> fold_prog node_fn expr_fn mod_fn call_fn rhs) v
    | Seq (a, lhs, rhs) =>
        (node_fn a
            #> fold_prog node_fn expr_fn mod_fn call_fn lhs
            #> fold_prog node_fn expr_fn mod_fn call_fn rhs) v
    | Catch (a, lhs, rhs) =>
        (node_fn a
            #> fold_prog node_fn expr_fn mod_fn call_fn lhs
            #> fold_prog node_fn expr_fn mod_fn call_fn rhs) v
    | RecGuard (a, body) =>
        (node_fn a
            #> fold_prog node_fn expr_fn mod_fn call_fn body) v

(*
 * Perform a liveness analysis on the given program.
 *
 * Each node's data will contain the set of live variables _prior_ to the block
 * being executed.
 *
 * For instance:
 *
 *    Condition (a < 3)          -- [a, b, c] live
 *       Modify (x := b)         -- [b, x] live
 *       Modify (x := c)         -- [c, x] live
 *    Modify (ret := x)          -- [x] live
 *)
local
fun calc_live_vars' term succ_live throw_live =
let
  fun set_from_some x =
    case x of
        NONE => empty_set
      | SOME x => make_set [x]
in
  case term of
      Init (old, written_vars) =>
        Init (old UNION (succ_live MINUS (set_from_some written_vars)), written_vars)
    | Modify (old, read_vars, written_vars) =>
        Modify (old UNION read_vars UNION (succ_live MINUS (set_from_some written_vars)), read_vars, written_vars)
    | Call (old, read_vars, ret_read_vars, written_vars, call_data) =>
        Call (old UNION (union_sets read_vars)
            UNION ret_read_vars
            UNION (succ_live MINUS (set_from_some written_vars)),
            read_vars, ret_read_vars, written_vars, call_data)
    | Guard (old, read_vars) =>
        Guard (old UNION succ_live UNION read_vars, read_vars)
    | Throw _ =>
        Throw throw_live
    | Spec (old, read_vars) =>
        Spec (old UNION read_vars, read_vars)
    | Fail _ =>
        Fail succ_live
    | While (old, read_vars, body) =>
        let
          val new_body = calc_live_vars' body (succ_live UNION old) throw_live
          val body_live = get_node_data new_body
        in
          While (old UNION body_live UNION read_vars, read_vars, new_body)
        end
    | Condition (old, read_vars, lhs, rhs) =>
        let
          val new_lhs = calc_live_vars' lhs succ_live throw_live
          val lhs_live = get_node_data new_lhs
          val new_rhs = calc_live_vars' rhs succ_live throw_live
          val rhs_live = get_node_data new_rhs
        in
          Condition (old UNION lhs_live UNION rhs_live UNION read_vars, read_vars, new_lhs, new_rhs)
        end
    | Seq (old, lhs, rhs) =>
        let
          val new_rhs = calc_live_vars' rhs succ_live throw_live
          val rhs_live = get_node_data new_rhs
          val new_lhs = calc_live_vars' lhs rhs_live throw_live
          val lhs_live = get_node_data new_lhs
        in
          Seq (old UNION lhs_live, new_lhs, new_rhs)
        end
    | Catch (old, lhs, rhs) =>
        let
          val new_rhs = calc_live_vars' rhs succ_live throw_live
          val rhs_live = get_node_data new_rhs
          val new_lhs = calc_live_vars' lhs succ_live rhs_live
          val lhs_live = get_node_data new_lhs
        in
          Catch (old UNION lhs_live, new_lhs, new_rhs)
        end
    | RecGuard (old, body) =>
        let
          val new_body = calc_live_vars' body succ_live throw_live
          val body_live = get_node_data new_body
        in
          RecGuard (old UNION body_live, new_body)
        end
end
in
fun calc_live_vars prog output_vars =
  let
    val init = map_prog (fn _ => empty_set) (fn (_, a, _) => a) (fn x => x) (fn x => x) prog
  in
    Utils.fixpoint (fn x => calc_live_vars' x output_vars empty_set) (op =) init
  end
end


(*
 * Get the variables read by each block of code.
 *
 * Each node's data will contain the set of variables read in the
 * given block.
 *)
fun get_read_vars term =
  case term of
      Init (_, written_vars) =>
        Init (empty_set, written_vars)
    | Modify (_, read_vars, written_vars) =>
        Modify (read_vars, read_vars, written_vars)
    | Call (_, read_vars, ret_read_vars, written_vars, call_data) =>
        Call (union_sets read_vars, read_vars, ret_read_vars, written_vars, call_data)
    | Guard (_, read_vars) =>
        Guard (read_vars, read_vars)
    | Throw _ =>
        Throw empty_set
    | Spec (_, read_vars) =>
        Spec (read_vars, read_vars)
    | Fail _ =>
        Fail empty_set
    | While (_, read_vars, body) =>
        let
          val new_body = get_read_vars body
          val new_reads = get_node_data new_body
        in
          While (new_reads UNION read_vars, read_vars, new_body)
        end
    | Condition (_, read_vars, lhs, rhs) =>
        let
          val new_lhs = get_read_vars lhs
          val new_rhs = get_read_vars rhs
          val new_reads = get_node_data new_lhs UNION get_node_data new_rhs
        in
          Condition (new_reads UNION read_vars, read_vars, new_lhs, new_rhs)
        end
    | Seq (_, lhs, rhs) =>
        let
          val new_lhs = get_read_vars lhs
          val new_rhs = get_read_vars rhs
          val new_reads = get_node_data new_lhs UNION get_node_data new_rhs
        in
          Seq (new_reads, new_lhs, new_rhs)
        end
    | Catch (_, lhs, rhs) =>
        let
          val new_lhs = get_read_vars lhs
          val new_rhs = get_read_vars rhs
          val new_reads = get_node_data new_lhs UNION get_node_data new_rhs
        in
          Catch (new_reads, new_lhs, new_rhs)
        end
    | RecGuard (_, body) =>
        let
          val new_body = get_read_vars body
          val new_reads = get_node_data new_body
        in
          RecGuard (new_reads, new_body)
        end

(*
 * Get the variables modified by each block of code.
 *
 * Each node's data will contain the set of variables modified in the
 * given block.
 *)
fun get_modified_vars term =
let
  (* Union variables, treating "NONE" as the set UNIV. *)
  infix UNION'
  fun (_ UNION' NONE) = NONE
    | (NONE UNION' _) = NONE
    | ((SOME x) UNION' (SOME y)) = SOME (x UNION y)

  (* Create a set from the given list, treating NONE as empty. *)
  fun set_from_some x =
    case x of
        NONE => empty_set
      | SOME x => make_set [x]
in
  case term of
      Init (_, written_vars) =>
        Init (SOME (set_from_some written_vars), written_vars)
    | Modify (_, read_vars, written_vars) =>
        Modify (SOME (set_from_some written_vars), read_vars, written_vars)
    | Call (_, read_vars, ret_read_vars, written_vars, call_data) =>
        Call (SOME (set_from_some written_vars), read_vars, ret_read_vars, written_vars, call_data)
    | Guard (_, read_vars) =>
        Guard (SOME empty_set, read_vars)
    | Throw _ =>
        Throw (SOME empty_set)
    | Spec (_, read_vars) =>
        Spec (NONE, read_vars)
    | Fail _ =>
        Fail (SOME empty_set)
    | While (_, read_vars, body) =>
        let
          val new_body = get_modified_vars body
          val new_modifies = get_node_data new_body
        in
          While (new_modifies, read_vars, new_body)
        end
    | Condition (_, read_vars, lhs, rhs) =>
        let
          val new_lhs = get_modified_vars lhs
          val new_rhs = get_modified_vars rhs
          val new_modifies = get_node_data new_lhs UNION' get_node_data new_rhs
        in
          Condition (new_modifies, read_vars, new_lhs, new_rhs)
        end
    | Seq (_, lhs, rhs) =>
        let
          val new_lhs = get_modified_vars lhs
          val new_rhs = get_modified_vars rhs
          val new_modifies = get_node_data new_lhs UNION' get_node_data new_rhs
        in
          Seq (new_modifies, new_lhs, new_rhs)
        end
    | Catch (_, lhs, rhs) =>
        let
          val new_lhs = get_modified_vars lhs
          val new_rhs = get_modified_vars rhs
          val new_modifies = get_node_data new_lhs UNION' get_node_data new_rhs
        in
          Catch (new_modifies, new_lhs, new_rhs)
        end
    | RecGuard (_, body) =>
        let
          val new_body = get_modified_vars body
          val new_modifies = get_node_data new_body
        in
          RecGuard (new_modifies, new_body)
        end
end

end
