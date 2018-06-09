(*
 *
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)
theory Datatype_Schematic

imports Main

begin

text {*
Introduces a method for improving unification outcomes for
schematics with datatype expressions as parameters.

There are two variants:
  1. In cases where a schematic is applied to a constant
like @{term True}, we wrap the constant to avoid some
undesirable unification candidates.

  2. In cases where a schematic is applied to a constructor expression
like @{term "Some x"} or @{term "(x, y)"}, we supply selector expressions
like @{term "the"} or @{term "fst"} to provide more unification candidates.
This is only done if parameter that would be selected (e.g. @{term x} in
@{term "Some x"}) contains bound variables which the schematic does not have
as parameters.
*}

definition
  ds_id :: "'a \<Rightarrow> 'a"
where
  "ds_id = (\<lambda>x. x)"

lemma wrap_ds_id:
  "x = ds_id x"
  by (simp add: ds_id_def)

ML {*
structure Datatype_Schematic = struct

(* gathers schematic applications from the goal. no effort is made
   to normalise bound variables here, since we'll always be comparing
   elements within a compound application which will be at the same
   level as regards lambdas. *)
fun gather_schem_apps (f $ x) insts = let
    val (f, xs) = strip_comb (f $ x)
    val insts = fold (gather_schem_apps) (f :: xs) insts
  in if is_Var f then (f, xs) :: insts else insts end
  | gather_schem_apps (Abs (_, _, t)) insts
    = gather_schem_apps t insts
  | gather_schem_apps _ insts = insts

val actions = Symtab.make_list [
    (@{const_name Pair}, (0, @{const_name fst}, @{thms prod.sel})),
    (@{const_name Pair}, (1, @{const_name snd}, @{thms prod.sel})),
    (@{const_name Some}, (0, @{const_name the}, @{thms option.sel})),
    (@{const_name Cons}, (0, @{const_name hd}, @{thms list.sel})),
    (@{const_name Cons}, (1, @{const_name tl}, @{thms list.sel}))]

fun sfirst xs f = get_first f xs

fun get_action prop = let
    val schem_insts = gather_schem_apps prop []
    fun mk_sel selname T i = let
        val (argTs, resT) = strip_type T
      in Const (selname, resT --> nth argTs i) end
  in
    sfirst schem_insts
    (fn (var, xs) => sfirst (xs ~~ (0 upto (length xs - 1)))
        (try (fn (x, idx) => let
            val (c, ys) = strip_comb x
            val (fname, T) = dest_Const c
            val acts = Symtab.lookup_list actions fname
            fun interesting arg = not (member Term.aconv_untyped xs arg)
                andalso exists (fn i => not (member (=) xs (Bound i)))
                    (Term.loose_bnos arg)
          in the (sfirst acts (fn (i, selname, thms) => if interesting (nth ys i)
            then SOME (var, idx, mk_sel selname T i, thms) else NONE))
          end)))
  end

fun get_bound_tac ctxt = SUBGOAL (fn (t, i) => case get_action t of
  SOME (Var ((nm, ix), T), idx, sel, thms) => (fn t => let
    val (argTs, _) = strip_type T
    val ix2 = Thm.maxidx_of t + 1
    val xs = map (fn (i, T) => Free ("x" ^ string_of_int i, T))
        (1 upto length argTs ~~ argTs)
    val nx = sel $ nth xs idx
    val v' = Var ((nm, ix2), fastype_of nx --> T)
    val inst_v = fold lambda (rev xs) (betapplys (v' $ nx, xs))
    val t' = Drule.infer_instantiate ctxt
        [((nm, ix), Thm.cterm_of ctxt inst_v)] t
    val t'' = Conv.fconv_rule (Thm.beta_conversion true) t'
  in safe_full_simp_tac (clear_simpset ctxt addsimps thms) i t'' end)
  | _ => no_tac)

fun id_applicable (f $ x) = let
    val (f, xs) = strip_comb (f $ x)
    val here = is_Var f andalso exists is_Const xs
  in here orelse exists id_applicable (f :: xs) end
  | id_applicable (Abs (_, _, t)) = id_applicable t
  | id_applicable _ = false

fun combination_conv cv1 cv2 ct =
  let
    val (ct1, ct2) = Thm.dest_comb ct
    val r1 = SOME (cv1 ct1) handle Option => NONE
    val r2 = SOME (cv2 ct2) handle Option => NONE
    fun mk _ (SOME res) = res
      | mk ct NONE = Thm.reflexive ct
  in case (r1, r2) of
      (NONE, NONE) => raise Option
    | _ => Thm.combination (mk ct1 r1) (mk ct2 r2)
  end

val wrap = mk_meta_eq @{thm wrap_ds_id}

fun wrap_const_conv _ ct = if is_Const (Thm.term_of ct)
        andalso fastype_of (Thm.term_of ct) <> @{typ unit}
    then Conv.rewr_conv wrap ct
    else raise Option

fun combs_conv conv ctxt ct = case Thm.term_of ct of
    _ $ _ => combination_conv (combs_conv conv ctxt) (conv ctxt) ct
  | _ => conv ctxt ct

fun wrap_conv ctxt ct = case Thm.term_of ct of
    Abs _ => Conv.sub_conv wrap_conv ctxt ct
  | f $ x => if is_Var (head_of f) then combs_conv wrap_const_conv ctxt ct
    else if not (id_applicable (f $ x)) then raise Option
    else combs_conv wrap_conv ctxt ct
  | _ => raise Option

fun CONVERSION_opt conv i t = CONVERSION conv i t
    handle Option => no_tac t

fun wrap_tac ctxt = CONVERSION_opt (wrap_conv ctxt)

fun tac1 ctxt = REPEAT_ALL_NEW (get_bound_tac ctxt) THEN' (TRY o wrap_tac ctxt)

fun tac ctxt = tac1 ctxt ORELSE' wrap_tac ctxt

val method
    = Args.context >> (fn _ => fn ctxt => Method.SIMPLE_METHOD' (tac ctxt));

end
*}

method_setup datatype_schem = {* Datatype_Schematic.method *}

lemma datatype_schem_demo:
  "\<exists>f. \<forall>y. f True (Some [x, (y, z)]) = y"
  apply (rule exI, rule allI)
  apply datatype_schem
  apply (rule refl)
  done

end
