(*
 * Copyright 2015, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory ProvePart
imports Main
begin

text \<open>Introduces a (sort-of) tactic for proving part of a goal by automatic
methods. The split between the proven and unproven part goes down into conjunction,
implication etc. The unproven parts are left in (roughly) their original form.\<close>

text \<open>
The first part is to take a goal and split it into two conjuncts,
e.g. "a \<and> (\<forall>x. b \<and> c x)
    = (((P1 \<longrightarrow> a) \<and> (\<forall>x. (P2 \<longrightarrow> b) \<and> (P3 \<longrightarrow> c x)))
        \<and> ((\<not> P1 \<longrightarrow> a) \<and> (\<forall>x. (\<not> P2 \<longrightarrow> b) \<and> (\<not> P3 \<longrightarrow> c x)))"

The first conjunct is then attacked by some automatic method.

The final part is to eliminate any goals remaining after that
automatic method by setting the Pi to False. The remaining Pi
(whose goal fragments were solved) are set to True. If the
resulting goals cannot be solved by setting to False, or if
no Pi are actually set to true, the process fails.
\<close>

lemma logic_to_conj_thm_workers:
  "A = (A' \<and> A'') \<Longrightarrow> B = (B' \<and> B'')
    \<Longrightarrow> (A \<and> B) = ((A' \<and> B') \<and> (A'' \<and> B''))"
  "B = (B' \<and> B'')
    \<Longrightarrow> (A \<or> B) = ((A \<or> B') \<and> (A \<or> B''))"
  "\<lbrakk> \<And>x. P x = (P' x \<and> P'' x) \<rbrakk>
    \<Longrightarrow> (\<forall>x. P x) = ((\<forall>x. P' x) \<and> (\<forall>x. P'' x))"
  "\<lbrakk> \<And>x. P x = (P' x \<and> P'' x) \<rbrakk>
    \<Longrightarrow> (\<forall>x \<in> S. P x) = ((\<forall>x \<in> S. P' x) \<and> (\<forall>x \<in> S. P'' x))"
  "B = (B' \<and> B'')
    \<Longrightarrow> (A \<longrightarrow> B) = ((A \<longrightarrow> B') \<and> (A \<longrightarrow> B''))"
  by auto

ML \<open>
structure Split_To_Conj = struct

fun abs_name (Abs (s, _, _)) = s
  | abs_name _ = "x"

fun all_type (Const (@{const_name "All"}, T) $ _)
    = domain_type (domain_type T)
  | all_type (Const (@{const_name "Ball"}, T) $ _ $ _)
    = domain_type (domain_type (range_type T))
  | all_type t = raise TERM ("all_type", [t])

fun split_thm prefix ctxt t = let
    val ok = not (String.isPrefix "Q" prefix orelse String.isPrefix "R" prefix)
    val _ = ok orelse error ("split_thm: prefix has prefix Q/R: " ^ prefix)
    fun params (@{term "(\<and>)"} $ x $ y) Ts = params x Ts @ params y Ts
      | params (@{term "(\<or>)"} $ _ $ y) Ts = (Ts, SOME @{typ bool}) :: params y Ts
      | params (all as (Const (@{const_name "All"}, _) $ t)) Ts
        = params (betapply (t, Bound 0)) (all_type all :: Ts)
      | params (ball as (Const (@{const_name "Ball"}, T) $ _ $ t)) Ts
        = (Ts, SOME (domain_type T)) :: params (betapply (t, Bound 0)) (all_type ball :: Ts)
      | params (@{term "(\<longrightarrow>)"} $ _ $ t) Ts = (Ts, SOME @{typ bool}) :: params t Ts
      | params _ Ts = [(Ts, NONE)]
    val ps = params t []
    val Ps = Variable.variant_frees ctxt [t]
        (replicate (length ps) (prefix, @{typ bool}))
        |> map Free
    val Qs = Variable.variant_frees ctxt [t]
        (map (fn (ps, T) => case T of NONE => ("Q", ps ---> @{typ bool})
                | SOME T => ("R", ps ---> T)) ps)
        |> map Free
    val Qs = map (fn (Q, (ps, _)) => Term.list_comb (Q, map Bound (0 upto (length ps - 1))))
        (Qs ~~ ps)
    fun assemble_bits (@{term "(\<and>)"} $ x $ y) Ps = let
        val (x, Ps) = assemble_bits x Ps
        val (y, Ps) = assemble_bits y Ps
      in (@{term "(\<and>)"} $ x $ y, Ps) end
      | assemble_bits (@{term "(\<or>)"} $ _ $ y) Ps = let
        val x = hd Ps
        val (y, Ps) = assemble_bits y (tl Ps)
      in (@{term "(\<or>)"} $ x $ y, Ps) end
      | assemble_bits (all as (Const (@{const_name "All"}, T) $ t)) Ps = let
        val nm = abs_name t
        val (t, Ps) = assemble_bits (betapply (t, Bound 0)) Ps
      in (Const (@{const_name "All"}, T) $ Abs (nm, all_type all, t), Ps) end
      | assemble_bits (ball as (Const (@{const_name "Ball"}, T) $ _ $ t)) Ps = let
        val nm = abs_name t
        val S = hd Ps
        val (t, Ps) = assemble_bits (betapply (t, Bound 0)) (tl Ps)
      in (Const (@{const_name "Ball"}, T) $ S $ Abs (nm, all_type ball, t), Ps) end
      | assemble_bits (@{term "(\<longrightarrow>)"} $ _ $ y) Ps = let
        val x = hd Ps
        val (y, Ps) = assemble_bits y (tl Ps)
      in (@{term "(\<longrightarrow>)"} $ x $ y, Ps) end
      | assemble_bits _ Ps = (hd Ps, tl Ps)
    val bits_lhs = assemble_bits t Qs |> fst
    fun imp tf (P, Q) = if String.isPrefix "R" (fst (dest_Free (head_of Q))) then Q
        else HOLogic.mk_imp (if tf then P else HOLogic.mk_not P, Q)
    val bits_true = assemble_bits t (map (imp true) (Ps ~~ Qs)) |> fst
    val bits_false = assemble_bits t (map (imp false) (Ps ~~ Qs)) |> fst
    val concl = HOLogic.mk_eq (bits_lhs, HOLogic.mk_conj (bits_true, bits_false))
      |> HOLogic.mk_Trueprop
  in (Goal.prove ctxt (map (fst o dest_Free o head_of) Qs) [] concl
    (K (REPEAT_ALL_NEW (resolve_tac ctxt
        @{thms logic_to_conj_thm_workers cases_simp[symmetric]}) 1)),
        map dest_Free Ps)
  end

fun get_split_tac prefix ctxt tac = SUBGOAL (fn (t, i) =>
  let
    val concl = HOLogic.dest_Trueprop (Logic.strip_assums_concl t)
    val (thm, Ps) = split_thm prefix ctxt concl
  in (resolve0_tac [ @{thm iffD2} ] THEN' resolve0_tac [thm] THEN' tac Ps) end i)

end
\<close>

text \<open>Testing.\<close>

ML \<open>
Split_To_Conj.split_thm "P" @{context}
  @{term "x & y & (\<forall>t \<in> UNIV. \<forall>n. True \<longrightarrow> z t n)"}
\<close>

ML \<open>
structure Partial_Prove = struct

fun inst_frees_tac _ Ps ct = REPEAT_DETERM o SUBGOAL (fn (t, _) =>
  fn thm => case Term.add_frees t [] |> filter (member (=) Ps)
  of [] => Seq.empty
  | (f :: _) => let
    val idx = Thm.maxidx_of thm + 1
    val var = ((fst f, idx), snd f)
  in thm |> Thm.generalize ([], [fst f]) idx
    |> Thm.instantiate ([], [(var, ct)])
    |> Seq.single
  end)

fun cleanup_tac ctxt Ps
    = inst_frees_tac ctxt Ps @{cterm False}
      THEN' asm_full_simp_tac ctxt

fun finish_tac ctxt Ps = inst_frees_tac ctxt Ps @{cterm True}
    THEN' CONVERSION (Conv.params_conv ~1 (fn ctxt =>
            (Conv.concl_conv ~1 (Simplifier.rewrite (put_simpset HOL_ss ctxt)))
        ) ctxt)

fun test_start_partial_prove ctxt i t = let
    val j = Thm.nprems_of t - i
  in Split_To_Conj.get_split_tac ("P_" ^ string_of_int j ^ "_") ctxt
        (K (K all_tac)) i t
  end

fun test_end_partial_prove ctxt t = let
    fun match_P (s, T) = case space_explode "_" s of
        ["P", n, _] => try (fn () => ((s, T), the (Int.fromString n))) ()
      | _ => NONE
    val Ps = Term.add_frees (Thm.concl_of t) [] |> map_filter match_P
    fun getmax ((x, n) :: xs) max maxes = if n > max then getmax xs n [x]
      else getmax xs max maxes
      | getmax [] max maxes = (max, maxes)
    val (j, Ps) = getmax Ps 0 []
    val i = Thm.nprems_of t - j
  in REPEAT_DETERM (FIRSTGOAL (fn k => if k < i then cleanup_tac ctxt Ps k else no_tac))
    THEN finish_tac ctxt Ps i end t

fun partial_prove tactic ctxt i
    = Split_To_Conj.get_split_tac ("P_" ^ string_of_int i ^ "_") ctxt
      (fn Ps => fn i => tactic i THEN finish_tac ctxt Ps i) i

fun method (ctxtg, []) = (fn ctxt => Method.SIMPLE_METHOD (test_start_partial_prove ctxt 1),
    (ctxtg, []))
  | method args = error "Partial_Prove: still working on that"

fun fin_method () = Scan.succeed (fn ctxt => Method.SIMPLE_METHOD (test_end_partial_prove ctxt))

end
\<close>

method_setup partial_prove = \<open>Partial_Prove.method\<close>
  "partially prove a compound goal by some automatic method"

method_setup finish_partial_prove = \<open>Partial_Prove.fin_method ()\<close>
  "partially prove a compound goal by some automatic method"

end
