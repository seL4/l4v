theory WPBang

imports WP "../Strengthen" NonDetMonadVCG

begin

text {*
  Splitting up predicates in a particular way.
*}

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

ML {*
structure Split_To_Conj = struct
(* Split a composite predicate into two, see test example below. *)

fun abs_name (Abs (s, _, _)) = s
  | abs_name _ = "x"

fun all_type (Const (@{const_name "All"}, T) $ _)
    = domain_type (domain_type T)
  | all_type (Const (@{const_name "Ball"}, T) $ _ $ _)
    = domain_type (domain_type (range_type T))
  | all_type t = raise TERM ("all_type", [t])

fun split_thm ctxt t = let
    fun params (@{term "op \<and>"} $ x $ y) Ts = params x Ts @ params y Ts
      | params (@{term "op \<or>"} $ _ $ y) Ts = (Ts, SOME @{typ bool}) :: params y Ts
      | params (all as (Const (@{const_name "All"}, _) $ t)) Ts
        = params (betapply (t, Bound 0)) (all_type all :: Ts)
      | params (ball as (Const (@{const_name "Ball"}, T) $ _ $ t)) Ts
        = (Ts, SOME (domain_type T)) :: params (betapply (t, Bound 0)) (all_type ball :: Ts)
      | params (@{term "op \<longrightarrow>"} $ _ $ t) Ts = (Ts, SOME @{typ bool}) :: params t Ts
      | params _ Ts = [(Ts, NONE)]
    val ps = params t []
    val Ps = Variable.variant_frees ctxt [t]
        (replicate (length ps) ("P", @{typ bool}))
        |> map Free
    val Qs = Variable.variant_frees ctxt [t]
        (map (fn (ps, T) => case T of NONE => ("Q", ps ---> @{typ bool})
                | SOME T => ("R", ps ---> T)) ps)
        |> map Free
    val Qs = map (fn (Q, (ps, _)) => Term.list_comb (Q, map Bound (0 upto (length ps - 1))))
        (Qs ~~ ps)
    fun assemble_bits (@{term "op \<and>"} $ x $ y) Ps = let
        val (x, Ps) = assemble_bits x Ps
        val (y, Ps) = assemble_bits y Ps
      in (@{term "op \<and>"} $ x $ y, Ps) end
      | assemble_bits (@{term "op \<or>"} $ _ $ y) Ps = let
        val x = hd Ps
        val (y, Ps) = assemble_bits y (tl Ps)
      in (@{term "op \<or>"} $ x $ y, Ps) end
      | assemble_bits (all as (Const (@{const_name "All"}, T) $ t)) Ps = let
        val nm = abs_name t
        val (t, Ps) = assemble_bits (betapply (t, Bound 0)) Ps
      in (Const (@{const_name "All"}, T) $ Abs (nm, all_type all, t), Ps) end
      | assemble_bits (ball as (Const (@{const_name "Ball"}, T) $ _ $ t)) Ps = let
        val nm = abs_name t
        val S = hd Ps
        val (t, Ps) = assemble_bits (betapply (t, Bound 0)) (tl Ps)
      in (Const (@{const_name "Ball"}, T) $ S $ Abs (nm, all_type ball, t), Ps) end
      | assemble_bits (@{term "op \<longrightarrow>"} $ _ $ y) Ps = let
        val x = hd Ps
        val (y, Ps) = assemble_bits y (tl Ps)
      in (@{term "op \<longrightarrow>"} $ x $ y, Ps) end
      | assemble_bits _ Ps = (hd Ps, tl Ps)
    val bits_lhs = assemble_bits t Qs |> fst
    fun imp tf (P, Q) = if String.isPrefix "R" (fst (dest_Free (head_of Q))) then Q
        else HOLogic.mk_imp (if tf then P else HOLogic.mk_not P, Q)
    val bits_true = assemble_bits t (map (imp true) (Ps ~~ Qs)) |> fst
    val bits_false = assemble_bits t (map (imp false) (Ps ~~ Qs)) |> fst
    val concl = HOLogic.mk_eq (bits_lhs, HOLogic.mk_conj (bits_true, bits_false))
      |> HOLogic.mk_Trueprop
  in Goal.prove ctxt (map (fst o dest_Free o head_of) Qs) [] concl
    (K (REPEAT_ALL_NEW (resolve_tac ctxt
        @{thms logic_to_conj_thm_workers cases_simp[symmetric]}) 1))
  end

end
*}

text {* Testing the split. *}
ML {*
Split_To_Conj.split_thm @{context}
  @{term "x & y & (\<forall>t \<in> UNIV. \<forall>n. True \<longrightarrow> z t n)"}
*}

lemma conj_prove_lhsE:
  "P \<and> Q \<Longrightarrow> (P \<Longrightarrow> P') \<Longrightarrow> P' \<and> Q"
  by simp

text {* Applying safe WP rules. *}
ML {*
structure WP_Safe = struct

fun inst_frees_tac ctxt Ps ct = REPEAT_DETERM o SUBGOAL (fn (t, _) =>
  fn thm => case Term.add_frees t [] |> filter (member (op =) Ps)
  of [] => Seq.empty
  | (f :: _) => let
    val idx = Thm.maxidx_of thm + 1
    val var = Thm.cterm_of ctxt (Var ((fst f, idx), snd f))
  in thm |> Thm.generalize ([], [fst f]) idx
    |> Thm.instantiate ([], [(var, ct)])
    |> Seq.single
  end)

fun check_has_frees_tac Ps (_ : int) thm = let
    val fs = Term.add_frees (Thm.prop_of thm) [] |> filter (member (op =) Ps)
  in if null fs then Seq.empty else Seq.single thm end

fun wp_bang wp_safe_rules ctxt = let
    val wp_safe_rules_conj = ((wp_safe_rules RL @{thms hoare_vcg_conj_lift hoare_vcg_R_conj})
        RL @{thms hoare_strengthen_post hoare_post_imp_R})
      |> map (rotate_prems 1)
  in
    resolve_tac ctxt wp_safe_rules_conj
    THEN' SUBGOAL (fn (t, i) => let
      val eq_to_conj_thm = Split_To_Conj.split_thm ctxt
        (HOLogic.dest_Trueprop (Logic.strip_assums_concl t))
      val Ps = Term.add_frees (Thm.prop_of eq_to_conj_thm) []
    in rtac @{thm iffD2} i THEN rtac eq_to_conj_thm i
      THEN etac @{thm conj_prove_lhsE} i
      THEN (REPEAT_ALL_NEW ((CHANGED o asm_full_simp_tac ctxt) ORELSE' Classical.safe_steps_tac ctxt)
        THEN_ALL_NEW inst_frees_tac ctxt Ps @{cterm "False"}
        THEN_ALL_NEW (check_has_frees_tac Ps THEN' asm_full_simp_tac ctxt)
      ) i
      THEN inst_frees_tac ctxt Ps @{cterm "True"} i
      THEN simp_tac ctxt i
    end)
  end

val wpe_args =
  Attrib.thms >> curry (fn (rules, ctxt) =>
    Method.SIMPLE_METHOD (
      wp_bang rules ctxt 1
    )
  );

end
*}

method_setup wpe = {* WP_Safe.wpe_args *}
  "applies 'safe' wp rules to eliminate postcondition components"

text {* Testing. *}
lemma 
  assumes x: "\<lbrace> P \<rbrace> f \<lbrace> \<lambda>rv. Q \<rbrace>"
       and y: "\<lbrace> P \<rbrace> f \<lbrace> \<lambda>rv. R \<rbrace>"
  shows
  "\<lbrace> P \<rbrace> f \<lbrace> \<lambda>rv s. \<forall>x y. (fst rv = Some x \<longrightarrow> Q s)
    \<and> (snd rv = Some y \<longrightarrow> Q s )
    \<and> R s \<rbrace>"
  apply (rule hoare_pre)
   apply (wpe x)
   apply (wp y)
  apply simp
  done

end
