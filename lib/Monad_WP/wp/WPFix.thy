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
theory WPFix

imports
  "../Datatype_Schematic"
  "../Strengthen"

begin

text \<open>
WPFix handles four issues which are annoying with precondition schematics:
  1. Schematics in obligation (postcondition) positions which remain unset
after goals are solved. They should be instantiated to True.
  2. Schematics which appear in multiple precondition positions. They should
be instantiated to a conjunction and then separated.
  3/4. Schematics applied to datatype expressions such as @{term True} or
@{term "Some x"}. See @{theory "Lib.Datatype_Schematic"} for details.
\<close>

lemma use_strengthen_prop_intro:
  "PROP P \<Longrightarrow> PROP (strengthen_implementation.st_prop1 (PROP Q) (PROP P))
    \<Longrightarrow> PROP Q"
  unfolding strengthen_implementation.st_prop1_def
  apply (drule(1) meta_mp)+
  apply assumption
  done

definition
  target_var :: "int \<Rightarrow> 'a \<Rightarrow> 'a"
where
  "target_var n x = x"

lemma strengthen_to_conjunct1_target:
  "strengthen_implementation.st True (\<longrightarrow>)
    (target_var n (P \<and> Q)) (target_var n P)"
  by (simp add: strengthen_implementation.st_def target_var_def)

lemma strengthen_to_conjunct2_target_trans:
  "strengthen_implementation.st True (\<longrightarrow>)
        (target_var n Q) R
    \<Longrightarrow> strengthen_implementation.st True (\<longrightarrow>)
        (target_var n (P \<and> Q)) R"
  by (simp add: strengthen_implementation.st_def target_var_def)

lemma target_var_drop_func:
  "target_var n f = (\<lambda>x. target_var n (f x))"
  by (simp add: target_var_def)

named_theorems wp_fix_strgs

lemma strg_target_to_true:
  "strengthen_implementation.st F (\<longrightarrow>) (target_var n True) True"
  by (simp add: target_var_def strengthen_implementation.strengthen_refl)

ML \<open>
structure WPFix = struct

val st_refl = @{thm strengthen_implementation.strengthen_refl}
val st_refl_True = @{thm strengthen_implementation.strengthen_refl[where x=True]}
val st_refl_target_True = @{thm strg_target_to_true}
val st_refl_non_target
    = @{thm strengthen_implementation.strengthen_refl[where x="target_var (-1) v" for v]}

val conv_to_target = mk_meta_eq @{thm target_var_def[symmetric]}

val tord = Term_Ord.fast_term_ord
fun has_var vars t = not (null (Ord_List.inter tord vars
        (Ord_List.make tord (map Var (Term.add_vars t [])))))

fun get_vars prop = map Var (Term.add_vars prop [])
    |> Ord_List.make tord
    |> filter (fn v => snd (strip_type (fastype_of v)) = HOLogic.boolT)

val st_intro = @{thm use_strengthen_prop_intro}
val st_not = @{thms strengthen_implementation.strengthen_Not}
val st_conj2_trans = @{thm strengthen_to_conjunct2_target_trans}
val st_conj1 = @{thm strengthen_to_conjunct1_target}

(* assumes Strengthen.goal_predicate g is "st" *)
fun dest_strg g = case Strengthen.goal_predicate g of
    "st" => (case HOLogic.dest_Trueprop (Logic.strip_assums_concl g) of
        (Const _ $ mode $ rel $ lhs $ rhs) => ("st", SOME (mode, rel, lhs, rhs))
      | _ => error ("dest_strg " ^ @{make_string} g)
    )
  | nm => (nm, NONE)

fun get_target (Const (@{const_name target_var}, _) $ n $ _)
  = (try (HOLogic.dest_number #> snd) n)
  | get_target _ = NONE

fun is_target P t = case get_target t of NONE => false
  | SOME v => P v

fun is_target_head P (f $ v) = is_target P (f $ v) orelse is_target_head P f
  | is_target_head _ _ = false

fun has_target P (f $ v) = is_target P (f $ v)
    orelse has_target P f orelse has_target P v
  | has_target P (Abs (_, _, t)) = has_target P t
  | has_target _ _ = false

fun apply_strgs congs ctxt = SUBGOAL (fn (t, i) => case
        dest_strg t of
    ("st_prop1", _) => resolve_tac ctxt congs i
  | ("st_prop2", _) => resolve_tac ctxt congs i
  | ("st", SOME (_, _, lhs, _)) => resolve_tac ctxt st_not i
    ORELSE eresolve_tac ctxt [thin_rl] i
    ORELSE resolve_tac ctxt [st_refl_non_target] i
    ORELSE (if is_target_head (fn v => v >= 0) lhs
        then no_tac
        else if not (has_target (fn v => v >= 0) lhs)
        then resolve_tac ctxt [st_refl] i
        else if is_Const (head_of lhs)
        then (resolve_tac ctxt congs i ORELSE resolve_tac ctxt [st_refl] i)
        else resolve_tac ctxt [st_refl] i
    )
  | _ => no_tac
  )

fun strg_proc ctxt = let
    val congs1 = Named_Theorems.get ctxt @{named_theorems wp_fix_strgs}
    val thy = Proof_Context.theory_of ctxt
    val congs2 = Strengthen.Congs.get thy
    val strg = apply_strgs (congs1 @ congs2) ctxt
  in REPEAT_ALL_NEW strg end

fun target_var_conv vars ctxt ct = case Thm.term_of ct of
    Abs _ => Conv.sub_conv (target_var_conv vars) ctxt ct
  | Var v => Conv.rewr_conv (Drule.infer_instantiate ctxt
        [(("n", 1), Thm.cterm_of ctxt (HOLogic.mk_number @{typ int}
            (find_index (fn v2 => v2 = Var v) vars)))] conv_to_target) ct
  | _ $ _ => Datatype_Schematic.combs_conv (target_var_conv vars) ctxt ct
  | _ => raise Option

fun st_intro_tac ctxt = CSUBGOAL (fn (ct, i) => fn thm => let
        val intro = Drule.infer_instantiate ctxt [(("Q", 0), ct)]
          (Thm.incr_indexes (Thm.maxidx_of thm + 1) st_intro)
      in compose_tac ctxt (false, intro, 2) i
      end thm)

fun intro_tac ctxt vs = SUBGOAL (fn (t, i) => if has_var vs t
    then CONVERSION (target_var_conv vs ctxt) i
        THEN CONVERSION (Simplifier.full_rewrite (clear_simpset ctxt
            addsimps @{thms target_var_drop_func}
        )) i
        THEN st_intro_tac ctxt i
    else all_tac)

fun classify v thm = let
    val has_t = has_target (fn v' => v' = v)
    val relevant = filter (has_t o fst)
        (Thm.prems_of thm ~~ (1 upto Thm.nprems_of thm))
        |> map (apfst (Logic.strip_assums_concl #> Envir.beta_eta_contract))
    fun class t = case dest_strg t of
        ("st", SOME (@{term True}, @{term "(-->)"}, lhs, _))
            => if has_t lhs then SOME true else NONE
      | ("st", SOME (@{term False}, @{term "(-->)"}, lhs, _))
            => if has_t lhs then SOME false else NONE
      | _ => NONE
    val classn = map (apfst class) relevant
    fun get k = map snd (filter (fn (k', _) => k' = k) classn)
  in if (null relevant) then NONE
    else if not (null (get NONE))
    then NONE
    else if null (get (SOME true))
    then SOME ("to_true", map snd relevant)
    else if length (get (SOME true)) > 1
    then SOME ("to_conj", get (SOME true))
    else NONE
  end

fun ONGOALS tac is = let
    val is = rev (sort int_ord is)
  in EVERY (map tac is) end

fun act_on ctxt ("to_true", is)
    = ONGOALS (resolve_tac ctxt [st_refl_target_True]) is
  | act_on ctxt ("to_conj", is)
    = ONGOALS (resolve_tac ctxt [st_conj2_trans]) (drop 1 is)
      THEN (if length is > 2 then act_on ctxt ("to_conj", drop 1 is)
        else ONGOALS (resolve_tac ctxt [st_refl]) (drop 1 is))
      THEN ONGOALS (resolve_tac ctxt [st_conj1]) (take 1 is)
  | act_on _ (s, _) = error ("act_on: " ^ s)

fun act ctxt check vs thm = let
    val acts = map_filter (fn v => classify v thm) vs
  in if null acts
    then (if check then no_tac else all_tac) thm
    else (act_on ctxt (hd acts) THEN act ctxt false vs) thm end

fun cleanup ctxt = SUBGOAL (fn (t, i) => case Strengthen.goal_predicate t of
    "st" => resolve_tac ctxt [st_refl] i
  | _ => all_tac)

fun tac ctxt = SUBGOAL (fn (t, _) => let
    val vs = get_vars t
  in if null vs then no_tac else ALLGOALS (intro_tac ctxt vs)
    THEN ALLGOALS (TRY o strg_proc ctxt)
    THEN act ctxt true (0 upto (length vs - 1))
    THEN ALLGOALS (cleanup ctxt)
    THEN Local_Defs.unfold_tac ctxt @{thms target_var_def}
  end)

fun both_tac ctxt = (Datatype_Schematic.tac ctxt THEN' (TRY o tac ctxt))
    ORELSE' tac ctxt

val method =
  Method.sections [Datatype_Schematic.add_section] >>
    (fn _ => fn ctxt => Method.SIMPLE_METHOD' (both_tac ctxt));

end
\<close>

method_setup wpfix = \<open>WPFix.method\<close>

lemma demo1:
  "(\<exists>Ia Ib Ic Id Ra.
    (Ia (Suc 0) \<longrightarrow> Qa)
  \<and> (Ib \<longrightarrow> Qb)
  \<and> (Ic \<longrightarrow> Ra)
  \<and> (Id \<longrightarrow> Qc)
  \<and> (Id \<longrightarrow> Qd)
  \<and> (Qa \<and> Qb \<and> Qc \<and> Qd \<longrightarrow> Ia v \<and> Ib \<and> Ic \<and> Id))"
  apply (intro exI conjI impI)
   (* apply assumption+ won't work here, since it will pick Id
      incorrectly. the presence of the goal ?Ra is also dangerous.
      wpfix handles this by setting Ra to True and splitting
      Id into a conjunction. *)
  apply (wpfix | assumption)+
  apply auto
  done

lemma demo2:
  assumes P: "\<And>x. P (x + Suc x) \<longrightarrow> R (Inl x)"
        "\<And>x. P ((x * 2) - 1) \<longrightarrow> R (Inr x)"
  assumes P17: "P 17"
  shows "\<exists>I. I (Some 9)
    \<and> (\<forall>x. I x \<longrightarrow> (case x of None \<Rightarrow> R (Inl 8) | Some y \<Rightarrow> R (Inr y)))
    \<and> (\<forall>x. I x \<longrightarrow> (case x of None \<Rightarrow> R (Inr 9) | Some y \<Rightarrow> R (Inl (y - 1))))"
  apply (intro exI conjI[rotated] allI)
    apply (case_tac x; simp)
     apply wpfix
     apply (rule P)
    apply wpfix
    apply (rule P)
   apply (case_tac x; simp)
    apply wpfix
    apply (rule P)
   apply wpfix
   apply (rule P)
  apply (simp add: P17)
  done

\<comment> \<open>
  Shows how to use @{attribute datatype_schematic} rules as "accessors".
\<close>
lemma (in datatype_schem_demo) demo3:
  "\<exists>x. \<forall>a b. x (basic a b) = a"
  apply (rule exI, (rule allI)+)
  apply (wpfix add: get_basic_0.simps) \<comment> \<open>Only exposes `a` to the schematic.\<close>
  by (rule refl)

end
