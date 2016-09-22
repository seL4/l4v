(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(* Title: Tactics for abstract separation algebras
   Authors: Gerwin Klein and Rafal Kolanski, 2012
   Maintainers: Gerwin Klein <kleing at cse.unsw.edu.au>
                Rafal Kolanski <rafal.kolanski at nicta.com.au>
*)

(* Separating Conjunction (and Top, AKA sep_true) {{{

  This defines the constants and theorems necessary for the conjunct
  selection and cancelling tactic, as well as utility functions.
*)

structure SepConj =
struct

val sep_conj_term = @{term sep_conj}
val sep_conj_str = "**"
val sep_conj_ac = @{thms sep_conj_ac}
val sep_conj_impl = @{thm sep_conj_impl}

fun is_sep_conj_const (Const (@{const_name sep_conj}, _)) = true
  | is_sep_conj_const _ = false

fun is_sep_conj_term (Const t $ _ $ _ $ _) = is_sep_conj_const (Const t)
  | is_sep_conj_term _ = false

fun is_sep_conj_prop (Const _ $ t) = is_sep_conj_term t
  | is_sep_conj_prop _ = false

fun strip_sep_conj (Const (@{const_name sep_conj},_) $ t1 $ t2 $ _) =
  [t1] @ (strip_sep_conj t2)
  | strip_sep_conj (Const (@{const_name sep_conj},_) $ t1 $ t2) =
  [t1] @ (strip_sep_conj t2)
  (* dig through eta exanded terms: *)
  | strip_sep_conj (Abs (_, _, t $ Bound 0)) = strip_sep_conj t
  | strip_sep_conj t = [t]

fun is_sep_true_term (Abs (_, _, Const (@{const_name True}, _))) = true
  | is_sep_true_term _ = false

fun mk_sep_conj (t1, t2) = sep_conj_term $ t1 $ t2

(* Types of conjuncts and name of state type, for term construction *)
val sep_conj_cjt_typ = type_of sep_conj_term |> domain_type
val sep_conj_state_typn = domain_type sep_conj_cjt_typ |> dest_TFree |> #1

end

(* }}} *)

(* Function application terms {{{ *)
(* Dealing with function applications of the type
     Const/Free(name,type) $ arg1 $ arg2 $ ... $ last_arg *)
structure FunApp =
struct

(* apply a function term to a Free with given name *)
fun fun_app_free t free_name = t $ Free (free_name, type_of t |> domain_type)

end (* }}} *)

(* Selecting Conjuncts in Premise or Conclusion {{{ *)

(* Constructs a rearrangement lemma of the kind:
   (A ** B ** C) s ==> (C ** A ** B) s
   When cjt_select = 2 (0-based index of C) and
   cjt_select = 3 (number of conjuncts to use), conclusion = true
   "conclusion" specifies whether the rearrangement occurs in conclusion
   (for dtac) or the premise (for rtac) of the rule.
*)

fun mk_sep_select_rule ctxt conclusion (cjt_count, cjt_selects) =
let
  fun variants nctxt names = fold_map Name.variant names nctxt
  val (state, nctxt0) = Name.variant "s" (Variable.names_of ctxt)
  fun mk_cjt n = Free (n, type_of SepConj.sep_conj_term |> domain_type)
  fun sep_conj_prop cjts =
        FunApp.fun_app_free (foldr1 SepConj.mk_sep_conj (map mk_cjt cjts)) state |> HOLogic.mk_Trueprop
  (* concatenate string and string of an int *)
  fun conc_str_int str int = str ^ Int.toString int
  (* make the conjunct names *)
  val (cjts, _) = 1 upto cjt_count |> map (conc_str_int "a") |> variants nctxt0
  (* make normal-order separation conjunction terms *)
  val orig = sep_conj_prop cjts

  (* make reordered separation conjunction terms *)

  (* We gather the needed conjuncts, and then append it the original list with those conjuncts removed *)
  fun dropit n (x::xs) is = if exists (fn y => y = n) is then dropit (n+1) xs is else x :: dropit (n+1) xs is
    | dropit _ [] _ = []

  fun nths_to_front idxs xs = map (nth xs) idxs @ dropit 0 xs idxs 
  val reordered = sep_conj_prop (nths_to_front cjt_selects cjts)
  val goal = Logic.mk_implies (if conclusion then (orig, reordered) else (reordered, orig))

  (* simp add: sep_conj_ac *)
  val sep_conj_ac_tac = Simplifier.asm_full_simp_tac
                          (put_simpset HOL_basic_ss ctxt addsimps SepConj.sep_conj_ac)

in
  Goal.prove ctxt [] [] goal (fn _ => sep_conj_ac_tac 1)
  |> Drule.generalize ([SepConj.sep_conj_state_typn], state :: cjts)
end

fun conj_length ctxt ct =
let 
  val ((_, ct'), _) = Variable.focus_cterm NONE ct ctxt
  val concl = ct' |> Drule.strip_imp_concl |> Thm.term_of
in
  concl |> HOLogic.dest_Trueprop |> SepConj.strip_sep_conj |> length
end

local 
  fun all_uniq xs = forall (fn x => length (filter (fn y => x = y) xs) = 1 ) xs 
in
  fun sep_selects_tac ctxt ns =
  let
    fun sep_select_tac' ctxt ns (ct, i) =
    let
      fun th ns = mk_sep_select_rule ctxt false ((conj_length ctxt ct),ns)
    in
      if not (all_uniq ns)
      then error ("Duplicate numbers in arguments")
      else resolve0_tac [th ns] i handle Subscript => no_tac 
    end
  in
    CSUBGOAL (sep_select_tac' ctxt (map (fn m => m - 1) ns))
  end
end

fun UNSOLVED' tac i st =
  tac i st |> Seq.filter (fn st' => Thm.nprems_of st' = Thm.nprems_of st)

fun sep_flatten ctxt = 
let
  fun simptac i =
    CHANGED_PROP (full_simp_tac (put_simpset HOL_basic_ss ctxt addsimps [@{thm sep_conj_assoc}]) i)
in
  UNSOLVED' simptac
end

fun sep_select_tactic lens_tac ns ctxt =
let 
  val sep_select = sep_selects_tac ctxt
  val iffI = @{thm iffI}
  val sep_conj_ac_tac = 
        Simplifier.asm_full_simp_tac (put_simpset HOL_basic_ss ctxt addsimps SepConj.sep_conj_ac)
in
  lens_tac THEN'
  resolve0_tac [iffI] THEN'
  sep_select ns THEN'
  assume_tac ctxt THEN'         
  sep_conj_ac_tac
end
