(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory ProveGraphRefine
imports GraphRefine GlobalsSwap FieldAccessors AsmSemanticsRespects CommonOpsLemmas
begin

ML \<open>
val do_trace = false;

fun trace_tac ctxt msg i =
    if do_trace
    then print_tac ctxt ("(tracing subgoal " ^ Int.toString i ^ "): " ^ msg)
    else all_tac;
\<close>

lemma const_globals_in_memory_heap_updateE:
  "\<lbrakk> globals_list_distinct D symtab gs;
    const_globals_in_memory symtab gs hmem;
    htd_safe D htd;
    ptr_safe (p :: ('a :: wf_type) ptr) htd \<rbrakk>
     \<Longrightarrow> const_globals_in_memory symtab gs (heap_update p val hmem)"
  by (simp add: const_globals_in_memory_heap_update)

lemma disjoint_h_val_globals_swap_insert:
  "\<lbrakk> global_acc_valid g_hrs g_hrs_upd;
     globals_list_distinct D symtab xs;
     htd_safe D htd;
     ptr_safe (p :: ('a :: wf_type) ptr) htd \<rbrakk>
     \<Longrightarrow> h_val (hrs_mem (g_hrs (globals s))) p
         = h_val (hrs_mem (g_hrs (globals_swap g_hrs g_hrs_upd symtab xs (globals s)))) p"
  (* the current apparatus produces goals where the Simpl-derived
     h_vals are applied to a globals swap and the graph-derived
     h_vals lack it. we thus *add* a globals swap since that is the
     case where we can prove ptr_safe *)
  apply (rule disjoint_h_val_globals_swap[symmetric], assumption+)
  apply (clarsimp simp: ptr_safe_def htd_safe_def del: subsetI)
  apply blast
  done

lemma disjoint_heap_update_globals_swap_rearranged:
  "\<lbrakk> global_acc_valid g_hrs g_hrs_upd;
     globals_list_distinct D symtab xs;
     htd_safe D htd;
     ptr_safe (p :: ('a :: wf_type) ptr) htd \<rbrakk>
     \<Longrightarrow> hrs_mem (g_hrs (globals_swap g_hrs g_hrs_upd symtab xs (g_hrs_upd (hrs_mem_update (heap_update p v)) gs)))
         = heap_update p v (hrs_mem (g_hrs (globals_swap g_hrs g_hrs_upd symtab xs gs)))"
  apply (subst disjoint_heap_update_globals_swap[symmetric], assumption+)
   apply (clarsimp simp: ptr_safe_def htd_safe_def del: subsetI)
   apply blast
  apply (simp add: global_acc_valid_def hrs_mem_update)
  done

lemma hrs_mem_update_triv:
  "hrs_mem_update (\<lambda>_. hrs_mem x) x = x"
  by (cases x, simp_all add: hrs_mem_update_def hrs_mem_def)

lemma h_t_valid_orig_and_ptr_safe:
  "h_t_valid d g p \<Longrightarrow> h_t_valid d g p \<and> ptr_safe p d"
  by (simp add: h_t_valid_ptr_safe)

lemma array_ptr_index_coerce:
  fixes p :: "(('a :: c_type)['b :: finite]) ptr"
  shows "n < CARD ('b)
    \<Longrightarrow> array_ptr_index p False n = array_ptr_index p True n"
  by (simp add: array_ptr_index_def)

lemma unat_mono_thms:
  "unat (a + b :: ('a :: len) word) \<le> unat a + unat b"
  "unat (a * b) \<le> unat a * unat b"
  by (simp_all add: unat_word_ariths)

lemma unat_mono_intro:
  "unat a \<le> x \<Longrightarrow> x < b \<Longrightarrow> unat a < b"
  "unat a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> unat a \<le> b"
  "unat a \<le> x \<Longrightarrow> x \<le> 0 \<Longrightarrow> unat a = 0"
  by simp_all

lemma word_neq_0_conv_neg_conv:
  "(\<not> 0 < (n :: ('a :: len) word)) = (n = 0)"
  by (cases "n = 0", simp_all)

lemmas unat_ucast_upcasts =
  unat_ucast_upcast[OF is_up[where 'a=32 and 'b=64, simplified]]

definition
  drop_sign :: "('a :: len) signed word \<Rightarrow> 'a word"
where
  "drop_sign = ucast"

lemma sint_drop_sign_isomorphism:
  "sint (drop_sign x) = sint x"
  by (simp add: drop_sign_def word_sint_msb_eq uint_up_ucast is_up_def
                source_size_def target_size_def word_size msb_ucast_eq)

lemma drop_sign_isomorphism_ariths:
  "(x = y) = (drop_sign x = drop_sign y)"
  "(x < y) = (drop_sign x < drop_sign y)"
  "(x \<le> y) = (drop_sign x \<le> drop_sign y)"
  "(x <s y) = (drop_sign x <s drop_sign y)"
  "(x <=s y) = (drop_sign x <=s drop_sign y)"
  "drop_sign (x + y) = drop_sign x + drop_sign y"
  "drop_sign (x - y) = drop_sign x - drop_sign y"
  "drop_sign (x * y) = drop_sign x * drop_sign y"
  "drop_sign (x div y) = drop_sign x div drop_sign y"
  "drop_sign (x sdiv y) = drop_sign x sdiv drop_sign y"
  "drop_sign (- y) = - drop_sign y"
  "drop_sign (if P then x else y) = (if P then drop_sign x else drop_sign y)"
  "drop_sign (w ^ n) = drop_sign w ^ n"
  by (simp_all add: drop_sign_def word_less_def
                    word_le_def word_sless_def word_sle_def
                    sint_drop_sign_isomorphism[unfolded drop_sign_def]
                    word_uint.Rep_inject[symmetric]
                    uint_up_ucast is_up_def source_size_def
                    target_size_def word_size
                    uint_word_arith_bintrs
                    word_arith_power_alt
                    uint_word_of_int
                    uint_div_alt sdiv_word_def sdiv_int_def
               del: word_uint.Rep_inject of_int_power)

lemma drop_sign_isomorphism_bitwise:
  "drop_sign (x AND y) = drop_sign x AND drop_sign y"
  "drop_sign (x OR y) = (drop_sign x) OR (drop_sign y)"
  "drop_sign (x XOR y) = drop_sign x XOR drop_sign y"
  "drop_sign (~~ y) = ~~ drop_sign y"
  "drop_sign (shiftl x n) = shiftl (drop_sign x) n"
  "drop_sign (shiftr x n) = shiftr (drop_sign x) n"
  "drop_sign (sshiftr x n) = sshiftr (drop_sign x) n"
  "drop_sign (ucast z) = ucast z"
  "drop_sign (scast z) = scast z"
  "ucast x = ucast (drop_sign x)"
  "scast x = scast (drop_sign x)"
  by (all \<open>(word_eqI_solve simp: drop_sign_def test_bit_bin)\<close>)

lemma drop_sign_of_nat:
  "drop_sign (of_nat n) = of_nat n"
  by (metis down_cast_same drop_sign_def is_up_is_down_remove_sign(2) scast_of_nat)

lemma drop_sign_to_bl:
  "to_bl (drop_sign w) = to_bl w"
  by (simp add: drop_sign_def to_bl_ucast)

lemma drop_sign_extra_bl_ops:
  "drop_sign (bv_clz w) = bv_clz (drop_sign w)"
  "drop_sign (bv_ctz w) = bv_ctz (drop_sign w)"
  "drop_sign (bv_popcount w) = bv_popcount (drop_sign w)"
  by (simp_all add: bv_clz_def bv_ctz_def bv_popcount_def drop_sign_of_nat
                    word_ctz_def word_clz_def pop_count_def drop_sign_to_bl)

lemma drop_sign_number[simp]:
  "drop_sign (numeral n) = numeral n"
  "drop_sign (- numeral n) = - numeral n"
  "drop_sign 0 = 0" "drop_sign 1 = 1"
  by (simp_all add: drop_sign_def ucast_def del: unsigned_numeral)

lemma drop_sign_minus_1[simp]:
  "drop_sign (-1) = (-1)"
  by (clarsimp simp add: drop_sign_def ucast_def uint_word_ariths)

lemma drop_sign_projections:
  "unat x = unat (drop_sign x)"
  "uint x = uint (drop_sign x)"
  "sint x = sint (drop_sign x)"
  apply (simp_all add: sint_drop_sign_isomorphism)
  apply (auto simp: unat_ucast_upcast uint_up_ucast drop_sign_def is_up_def
                    source_size_def target_size_def word_size)
  done

lemmas drop_sign_isomorphism
    = drop_sign_isomorphism_ariths drop_sign_projections
        drop_sign_isomorphism_bitwise drop_sign_of_nat
        drop_sign_extra_bl_ops

lemma drop_sign_h_val[simp]:
  "drop_sign (h_val hp p :: ('a :: len8) signed word) = h_val hp (ptr_coerce p)"
  using len8_dv8[where 'a='a]
  apply (simp add: h_val_def drop_sign_def)
  apply (simp add: from_bytes_ucast_isom word_size size_of_def typ_info_word)
  done

lemma drop_sign_heap_update[simp]:
  "heap_update p v = heap_update (ptr_coerce p) (drop_sign v)"
  using len8_dv8[where 'a='a]
  apply (simp add: heap_update_def drop_sign_def fun_eq_iff)
  apply (simp add: to_bytes_ucast_isom word_size size_of_def typ_info_word)
  done

lemma typ_uinfo_t_signed_word:
  "typ_uinfo_t TYPE (('a :: len8) signed word) = typ_uinfo_t TYPE ('a word)"
  using len8_dv8[where 'a='a]
  apply (simp add: typ_uinfo_t_def typ_info_word)
  apply (clarsimp simp: field_norm_def fun_eq_iff)
  apply (simp add: word_rsplit_rcat_size word_size)
  done

lemma align_td_signed_word:
  "align_td (typ_info_t TYPE (('a :: len8) signed word))
    = align_td (typ_info_t TYPE (('a :: len8) word))"
  using arg_cong[where f=align_td, OF typ_uinfo_t_signed_word[where 'a='a]]
  by (simp add: typ_uinfo_t_def)

lemma size_td_signed_word:
  "size_td (typ_info_t TYPE (('a :: len8) signed word))
    = size_td (typ_info_t TYPE (('a :: len8) word))"
  by (simp add: typ_info_word)

lemma pointer_inverse_safe_sign:
  "ptr_inverse_safe (ptr :: (('a :: len8) signed word ptr))
    = ptr_inverse_safe (ptr_coerce ptr :: 'a word ptr)"
  by (simp add: fun_eq_iff ptr_inverse_safe_def s_footprint_def
                c_guard_def ptr_aligned_def c_null_guard_def
                typ_uinfo_t_signed_word align_td_signed_word align_of_def
                size_of_def size_td_signed_word)

lemma ptr_equalities_to_ptr_val:
  "(Ptr addr = p) = (addr = ptr_val p)"
  "(p = Ptr addr) = (ptr_val p = addr)"
  by (simp | cases p)+

lemma unat_ucast_if_up:
  "unat (ucast (x :: ('a :: len) word) :: ('b :: len) word)
    = (if len_of TYPE('a) \<le> len_of TYPE('b) then unat x else unat x mod 2 ^ len_of TYPE ('b))"
  apply (simp, safe intro!: unat_ucast unat_ucast_upcast)
  apply (simp add: is_up_def source_size_def target_size_def word_size)
  done

(* FIXME: these 2 duplicated from crefine *)
lemma Collect_const_mem:
  "(x \<in> (if P then UNIV else {})) = P"
  by simp

lemma typ_uinfo_t_diff_from_typ_name:
  "typ_name (typ_info_t TYPE ('a :: c_type)) \<noteq> typ_name (typ_info_t TYPE('b :: c_type))
    \<Longrightarrow> typ_uinfo_t (aty :: 'a itself) \<noteq> typ_uinfo_t (bty :: 'b itself)"
  by (clarsimp simp: typ_uinfo_t_def td_diff_from_typ_name)

lemmas ptr_add_assertion_unfold_numeral
    = ptr_add_assertion_def[where offs="numeral n" for n, simplified]
      ptr_add_assertion_def[where offs="uminus (numeral n)" for n, simplified]
      ptr_add_assertion_def[where offs=0, simplified]
      ptr_add_assertion_def[where offs=1, simplified]

definition machine_word_truncate_nat :: "nat => machine_word \<Rightarrow> machine_word"
where
  "machine_word_truncate_nat n x = (if unat x \<le> n then x else of_nat n)"

lemma machine_word_truncate_noop:
  "unat x < Suc n \<Longrightarrow> machine_word_truncate_nat n x = x"
  by (simp add: machine_word_truncate_nat_def)

lemma fold_of_nat_eq_Ifs_proof:
  "\<lbrakk> unat (x :: machine_word) \<notin> set ns \<Longrightarrow> y = z;
      \<And>n. n \<in> set ns \<Longrightarrow> x = of_nat n \<Longrightarrow> f n = z \<rbrakk>
    \<Longrightarrow> foldr (\<lambda>n v. if x = of_nat n then f n else v) ns y = z"
  apply (induct ns)
   apply simp
  apply (atomize(full))
  apply clarsimp
  done

lemma fold_of_nat_eq_Ifs[simplified word_bits_conv]:
  "m < 2 ^ word_bits
    \<Longrightarrow> foldr (\<lambda>n v. if x = of_nat n then f n else v) [0 ..< m] (f m)
        = f (unat (machine_word_truncate_nat m x))"
  apply (rule fold_of_nat_eq_Ifs_proof)
   apply (simp_all add: machine_word_truncate_nat_def word_bits_def take_bit_nat_eq_self unat_of_nat)
  done

lemma less_is_non_zero_p1':
  fixes a :: "'a :: len word"
  shows "a < k \<Longrightarrow> 1 + a \<noteq> 0"
  by (metis less_is_non_zero_p1 add.commute)

lemma(in comm_semiring_1) add_mult_comms:
  "a + b + c = a + c + b"
  "a * b * c = a * c * b"
  by (rule semiring_normalization_rules)+

lemma array_index_update_If:
  "i < CARD ('b :: finite)
    \<Longrightarrow> Arrays.index (Arrays.update arr j x) i
        = (if i = j then x else Arrays.index (arr :: ('a['b])) i)"
  by simp

\<comment> \<open>Of the assumptions, only pos is needed to prove the conclusion.
    The guard assumptions are there to ensure that when used as a simp rule,
    the RHS array pointer gets an appropriate type.\<close>
lemma ptr_safe_ptr_add_array_ptr_index_int:
  assumes guard: "ptr_safe (Ptr p::('a['b]) ptr) htd" (* "nat i < CARD('b)" *)
  assumes pos: "0 \<le> i"
  shows "(Ptr p::'a::c_type ptr) +\<^sub>p i = array_ptr_index (Ptr p::('a['b::finite]) ptr) False (nat i)"
  using pos by (simp add: array_ptr_index_def)

lemma ptr_safe_ptr_add_array_ptr_index_sint:
  assumes guard: "ptr_safe (Ptr p::('a['b]) ptr) htd" "i <s of_nat CARD('b)"
  assumes pos: "0 <=s i"
  shows "(Ptr p::'a::c_type ptr) +\<^sub>p sint i = array_ptr_index (Ptr p::('a['b::finite]) ptr) False (unat i)"
  using pos by (simp add: array_ptr_index_def int_unat sint_eq_uint word_sle_msb_le)

lemmas ptr_safe_ptr_add_array_ptr_index =
  ptr_safe_ptr_add_array_ptr_index_int
  ptr_safe_ptr_add_array_ptr_index_sint

lemma ptr_safe_Array_element_0:
  "ptr_safe (PTR('a::mem_type['b::finite]) p) htd \<Longrightarrow> ptr_safe (PTR('a) p) htd"
  by (drule ptr_safe_Array_element[where coerce=False and n=0]; simp add: array_ptr_index_def)

ML \<open>
fun preserve_skel_conv consts arg_conv ct = let
    val (hd, xs) = strip_comb (Thm.term_of ct)
    val self = preserve_skel_conv consts arg_conv
  in if is_Const hd andalso member (op =) consts
        (fst (dest_Const hd))
    then  if null xs then Conv.all_conv ct
        else Conv.combination_conv self self ct
    else arg_conv ct end

fun fold_of_nat_eq_Ifs ctxt tm = let
    fun recr (Const (@{const_name If}, _)
            $ (@{term "(=) :: machine_word => _"} $ _ $ n) $ y $ z)
        = (SOME n, y) :: recr z
      | recr t = [(NONE, t)]
    val (ns, vs) = recr tm |> map_split I
    val ns = map_filter I ns |> map (HOLogic.dest_number #> snd)
    val _ = (ns = (0 upto (length ns - 1)))
        orelse raise TERM ("fold_of_nat_eq_Ifs: ns", [tm])
    val _ = length vs > 1
        orelse raise TERM ("fold_of_nat_eq_Ifs: no If", [tm])
    val n = @{term "n_hopefully_uniq :: nat"}
    fun get_pat @{term "0 :: nat"} @{term "Suc 0 :: nat"} = n
      | get_pat (f $ x) (g $ y) = get_pat f g $ get_pat x y
      | get_pat (a as Abs (s, T, t)) (a' as Abs (_, T', t'))
          = ((T = T' orelse raise TERM ("fold_array_conditional: get_pat", [a, a']))
              ; Abs (s, T, get_pat t t'))
      | get_pat t t' = (t aconv t' orelse raise TERM ("fold_array_conditional: get_pat", [t, t'])
              ; t)
    val pat = lambda n (get_pat (nth vs 0) (nth vs 1))
    val m = HOLogic.mk_number @{typ nat} (length vs - 1)
    val conv = preserve_skel_conv [fst (dest_Const @{term "(==>)"}),
            @{const_name Trueprop}, fst (dest_Const @{term "(==)"}),
            @{const_name If}]
        (Simplifier.rewrite ctxt)
    val thm = @{thm fold_of_nat_eq_Ifs}
      |> infer_instantiate ctxt [(("f",0), Thm.cterm_of ctxt pat),
          (("m",0), Thm.cterm_of ctxt m)]
      |> simplify (put_simpset HOL_basic_ss ctxt
          addsimprocs [Word_Bitwise_Tac.expand_upt_simproc]
          addsimps @{thms foldr.simps id_apply o_apply})
      |> mk_meta_eq
      |> Conv.fconv_rule conv
  in thm end

val fold_of_nat_eq_Ifs_simproc = Simplifier.make_simproc
  (Proof_Context.init_global @{theory})
  { name = "fold_of_nat_eq_Ifs"
  , kind = Simproc
  , lhss = [@{term "If (x = 0) y z"}]
  , proc = fn _ => fn ctxt => try (fold_of_nat_eq_Ifs ctxt) o Thm.term_of
  , identifier = []
  }

fun unfold_assertion_data_get_set_conv ctxt tm = let
    val (f, xs) = strip_comb tm
    val (f_nm, _) = dest_Const f
    val procs = map_filter (fn (Const (s, _)) => if String.isSuffix "_'proc" s
        then SOME s else NONE | _ => NONE) xs
    val defs = map (suffix "_def" #> Proof_Context.get_thm ctxt) (f_nm :: procs)
  in Simplifier.rewrite (ctxt addsimps defs) (Thm.cterm_of ctxt tm) end

val unfold_assertion_data_get_set = Simplifier.make_simproc
  (Proof_Context.init_global @{theory})
  { name = "unfold_assertion_data_get"
  , kind = Simproc
  , lhss = [@{term "ghost_assertion_data_get k acc s"}, @{term "ghost_assertion_data_set k v upd"}]
  , proc = fn _ => fn ctxt => SOME o (unfold_assertion_data_get_set_conv ctxt) o Thm.term_of
  , identifier = []
  }

\<close>

ML \<open>
fun wrap_tac tac i t = if Thm.nprems_of t = 0 then no_tac t else let
    val t' = Goal.restrict i 1 t
    val r = tac 1 t'
  in case Seq.pull r of NONE => Seq.empty
    | SOME (t'', _) => Seq.single (Goal.unrestrict i t'')
  end

fun eqsubst_wrap_tac ctxt thms = wrap_tac (EqSubst.eqsubst_tac ctxt [0] thms)
fun eqsubst_asm_wrap_tac ctxt thms = wrap_tac (EqSubst.eqsubst_asm_tac ctxt [0] thms)
fun eqsubst_either_wrap_tac ctxt thms = (eqsubst_asm_wrap_tac ctxt thms
    ORELSE' eqsubst_wrap_tac ctxt thms)
\<close>


ML \<open>
structure ProveSimplToGraphGoals = struct

fun goal_eq (g, g') =
    (eq_list (op aconv) (Logic.strip_assums_hyp g, Logic.strip_assums_hyp g'))
    andalso (Logic.strip_assums_concl g aconv Logic.strip_assums_concl g')
    andalso (map snd (Logic.strip_params g) = map snd (Logic.strip_params g'))

fun tactic_check s tac = let
  in fn i => fn t => case Seq.list_of (tac i t)
    of [] => Seq.empty
    | [t'] => let
        val orig_goals = Thm.prems_of t
        val new_goals = Thm.prems_of t'
      in (eq_list goal_eq (take (i - 1) orig_goals, take (i - 1) new_goals)
          andalso eq_list goal_eq (drop i orig_goals,
              drop (i + length new_goals - length orig_goals) new_goals))
        orelse raise THM ("tactic " ^ s ^ " broke the rules!", i, [t, t'])
        ; Seq.single t'
      end
    | _ => raise THM ("tactic " ^ s ^ " nondeterministic", i, [t])
  end

(* FIXME: shadows SimplExport *)
fun get_c_type_size ctxt (Type (@{type_name array}, [elT, nT])) =
    get_c_type_size ctxt elT * Word_Lib.dest_binT nT
  | get_c_type_size _ @{typ word8} = 1
  | get_c_type_size _ @{typ word16} = 2
  | get_c_type_size _ @{typ word32} = 4
  | get_c_type_size _ @{typ word64} = 8
  | get_c_type_size ctxt (Type (@{type_name ptr}, [_])) =
        get_c_type_size ctxt @{typ machine_word}
  | get_c_type_size ctxt (Type (@{type_name word}, [Type (@{type_name signed}, [t])]))
    = get_c_type_size ctxt (Type (@{type_name word}, [t]))
  | get_c_type_size ctxt (T as Type (s, _)) = let
    val thm = Proof_Context.get_thm ctxt (s ^ "_size")
      handle ERROR _ => raise TYPE ("get_c_type_size: couldn't get size", [T], [])
  in (Thm.rhs_of thm |> Thm.term_of |> HOLogic.dest_number |> snd)
    handle TERM (s, ts) => raise TYPE ("get_c_type_size: " ^ s, [T], ts)
  end
  | get_c_type_size _ T = raise TYPE ("get_c_type_size:", [T], [])

fun enum_simps csenv ctxt = let
    val Absyn.CE ecenv = ProgramAnalysis.cse2ecenv csenv;
  in
    #enumenv ecenv |> Symtab.dest
       |> map (Proof_Context.get_thm ctxt o suffix "_def" o fst)
  end

fun safe_goal_tac ctxt =
  REPEAT_ALL_NEW (DETERM o CHANGED o safe_steps_tac ctxt)

fun res_from_ctxt tac_name thm_name ctxt thm = let
    val thm_from_ctxt = Proof_Context.get_thm ctxt thm_name
      handle ERROR _ => raise THM (tac_name ^ ": need thm " ^ thm_name, 1, [])
  in thm_from_ctxt RS thm
    handle THM _ => raise THM (tac_name ^ ": need thm to resolve: " ^ thm_name,
        1, [thm_from_ctxt, thm])
  end

val except_tac = SimplToGraphProof.except_tac

fun warn_schem_tac msg ctxt tac = SUBGOAL (fn (t, i) => let
    val _ = if null (Term.add_var_names t []) then ()
      else warning ("schematic in goal: " ^ msg ^ ": "
        ^ Pretty.string_of (Syntax.pretty_term ctxt t))
  in tac i end)

fun ptr_safe_arr_field_tac ctxt =
    EVERY' [
      eqsubst_either_wrap_tac ctxt @{thms ptr_safe_ptr_add_array_ptr_index},
      resolve_tac ctxt @{thms ptr_safe_field} THEN' assume_tac ctxt THEN' asm_full_simp_tac ctxt,
      asm_full_simp_tac (ctxt addsimps @{thms typ_uinfo_t_def}),
      asm_full_simp_tac ctxt
    ]

fun prove_ptr_safe reason ctxt = DETERM o
    warn_schem_tac "prove_ptr_safe" ctxt
    (TRY o REPEAT_ALL_NEW (eqsubst_either_wrap_tac ctxt
                @{thms array_ptr_index_coerce nat_uint_less_helper}
            )
        THEN_ALL_NEW (TRY o REPEAT_ALL_NEW (ptr_safe_arr_field_tac ctxt))
        THEN_ALL_NEW asm_full_simp_tac (ctxt addsimps
            @{thms ptr_safe_ptr_add_array_ptr_index
                   word_sle_msb_le word_sless_msb_less
                   nat_uint_less_helper})
        THEN_ALL_NEW asm_simp_tac (ctxt addsimps
            @{thms ptr_safe_field[unfolded typ_uinfo_t_def]
                   ptr_safe_Array_element unat_less_helper unat_def[symmetric]
                   ptr_safe_Array_element_0
                   h_t_valid_Array_element' h_t_valid_field
                   nat_uint_less_helper upcast_less_unat_less})
        THEN_ALL_NEW except_tac ctxt
            ("prove_ptr_safe: failed for " ^ reason)
    )

fun get_disjoint_h_val_globals_swap ctxt =
    @{thm disjoint_h_val_globals_swap_insert}
        |> res_from_ctxt "prove_heap_update_id" "global_acc_valid" ctxt
        |> res_from_ctxt "prove_heap_update_id" "globals_list_distinct" ctxt

fun prove_heap_update_id ctxt = DETERM o let
    val thm = get_disjoint_h_val_globals_swap ctxt
  in fn i => (resolve_tac ctxt @{thms heap_update_id_Array heap_update_id} i
        ORELSE except_tac ctxt "prove_heap_update_id: couldn't init" i)
    THEN (simp_tac ctxt
    THEN_ALL_NEW (* simp_tac will solve goal unless globals swap involved *)
    ((resolve0_tac [thm]
      ORELSE' (resolve0_tac [@{thm sym}] THEN' resolve0_tac [thm])
      ORELSE' except_tac ctxt "prove_heap_update_id: couldn't rtac")
    THEN' (assume_tac ctxt (* htd_safe assumption *)
      ORELSE' except_tac ctxt "prove_heap_update_id: couldn't atac")
    THEN' prove_ptr_safe "prove_heap_update" ctxt)) i
  end

fun get_field_h_val_rewrites ctxt =
    Proof_Context.get_thms ctxt "field_h_val_rewrites"
        handle ERROR _ => raise THM
            ("run add_field_h_val_rewrites on ctxt", 1, [])

fun get_field_offset_rewrites ctxt =
    Proof_Context.get_thms ctxt "field_offset_rewrites"
        handle ERROR _ => raise THM
            ("run add_field_offset_rewrites on ctxt", 1, [])

fun get_globals_rewrites ctxt = let
    val gsr = Proof_Context.get_thms ctxt "globals_swap_rewrites"
    val cgr = Proof_Context.get_thms ctxt "const_globals_rewrites_with_swap"
    val pinv = Proof_Context.get_thms ctxt "pointer_inverse_safe_global_rules"
    val pinv2 = map (simplify (put_simpset HOL_basic_ss ctxt
        addsimps @{thms pointer_inverse_safe_sign ptr_coerce.simps})) pinv
  in (gsr, cgr, pinv @ pinv2) end
        handle ERROR _ => raise THM
            ("run add_globals_swap_rewrites on ctxt", 1, [])

fun add_symbols (Free (_, _) $ s) xs = (case try HOLogic.dest_string s
        of SOME str => str :: xs | _ => xs)
  | add_symbols (f $ x) xs = add_symbols f (add_symbols x xs)
  | add_symbols (Abs (_, _, t)) xs = add_symbols t xs
  | add_symbols _ xs = xs

fun get_symbols t = add_symbols t [] |> Ord_List.make fast_string_ord

fun get_expand_const_globals ctxt goal = let
    val goal_symbs = get_symbols goal
    val cgr = #2 (get_globals_rewrites ctxt)
    val cgr_missing = filter_out (fn t => Ord_List.subset fast_string_ord
        (get_symbols (Thm.concl_of t), goal_symbs)) cgr
    val cgs_unfold = map (Thm.concl_of #> HOLogic.dest_Trueprop
        #> HOLogic.dest_eq #> fst #> dest_Const #> fst) cgr_missing
    val cgs_unfold_defs = map (suffix "_def"
        #> Proof_Context.get_thm ctxt) cgs_unfold
  in cgs_unfold_defs end

fun normalise_mem_accs reason ctxt = DETERM o let
    val gr = get_globals_rewrites ctxt
    val msg' = "normalise_mem_accs: " ^ reason
    fun msg str = msg' ^ ": " ^ str
    val init_simps = @{thms hrs_mem_update
                       heap_access_Array_element'
                       o_def fupdate_def
                       pointer_inverse_safe_sign
                       ptr_safe_ptr_add_array_ptr_index
                       unat_less_helper nat_uint_less_helper
            } @ get_field_h_val_rewrites ctxt
        @ #1 gr @ #2 gr
    val h_val = get_disjoint_h_val_globals_swap ctxt
    val disjoint_h_val_tac
    = (eqsubst_asm_wrap_tac ctxt [h_val] ORELSE' eqsubst_wrap_tac ctxt [h_val])
         THEN' (assume_tac ctxt ORELSE' except_tac ctxt (msg "couldn't atac"))
  in
    asm_full_simp_tac (ctxt addsimps init_simps addsimps [h_val])
    THEN_ALL_NEW warn_schem_tac msg' ctxt (K all_tac)
    THEN_ALL_NEW
        (TRY o REPEAT_ALL_NEW ((eqsubst_asm_wrap_tac ctxt
                    @{thms heap_access_Array_element'}
                ORELSE' eqsubst_wrap_tac ctxt
                    @{thms heap_access_Array_element'}
                ORELSE' disjoint_h_val_tac)
            THEN_ALL_NEW asm_full_simp_tac (ctxt addsimps init_simps)))
    THEN_ALL_NEW
        SUBGOAL (fn (t, i) => case
            Envir.beta_eta_contract (Logic.strip_assums_concl t)
          of @{term Trueprop} $ (Const (@{const_name h_t_valid}, _) $ _ $ _ $ _)
              => prove_ptr_safe msg' ctxt i
            | @{term Trueprop} $ (Const (@{const_name ptr_safe}, _) $ _ $ _)
              => prove_ptr_safe msg' ctxt i
            | _ => all_tac)
    THEN_ALL_NEW full_simp_tac (ctxt addsimps @{thms h_val_word_simps nat_uint_less_helper})
  end

val heap_update_id_nonsense
    = Thm.trivial (Thm.cterm_of @{context} (Proof_Context.read_term_pattern @{context}
        "Trueprop (heap_update ?p (h_val ?hp' ?p) (hrs_mem ?hrs) = hrs_mem ?hrs)"))

fun prove_mem_equality_init_simpset ctxt =
    ctxt addsimps
      @{thms hrs_mem_update heap_update_Array_update heap_access_Array_element' o_def}
        @ get_field_h_val_rewrites ctxt

fun prove_mem_equality_unpack_simpset ctxt =
    ctxt addsimps
      @{thms heap_update_def to_bytes_array
             heap_update_list_append
             h_val_word_simps
             heap_update_word_simps
             heap_list_update_word_simps
             to_bytes_sword
             drop_sign_isomorphism
             field_lvalue_offset_eq ptr_add_def
             array_ptr_index_def
             take_heap_list_min drop_heap_list_general
             ucast_nat_def of_int_sint_scast of_int_uint_ucast
             heap_access_Array_element field_lvalue_def}
        @ Proof_Context.get_thms ctxt "field_to_bytes_rewrites"
        @ (get_field_h_val_rewrites ctxt)
      addsimprocs [Word_Bitwise_Tac.expand_upt_simproc]
      delsimps @{thms One_nat_def}
      addsimps @{thms One_nat_def[symmetric]}
    handle ERROR _ => raise THM
      ("prove_mem_equality: run add_field_to_bytes_rewrites on ctxt", 1, [])

fun prove_mem_equality_unchecked ctxt = let
    fun heap_update_id_proofs ctxt =
        REPEAT_ALL_NEW (eqsubst_wrap_tac ctxt [heap_update_id_nonsense]
            THEN' prove_heap_update_id ctxt)

  in
    (trace_tac ctxt "prove_mem_equality: initial state")
    THEN_ALL_NEW (simp_tac (prove_mem_equality_init_simpset ctxt))
    THEN_ALL_NEW warn_schem_tac "prove_mem_equality: before subst" ctxt (K all_tac)
    THEN_ALL_NEW (TRY o REPEAT_ALL_NEW ((eqsubst_wrap_tac ctxt
            @{thms heap_access_Array_element' heap_update_Array_update})
        THEN_ALL_NEW simp_tac (prove_mem_equality_init_simpset ctxt)))
    THEN_ALL_NEW TRY o heap_update_id_proofs ctxt
    THEN_ALL_NEW SUBGOAL (fn (t, i) => if
        exists_Const (fn (s, T) => s = @{const_name heap_update}
            andalso get_c_type_size ctxt (domain_type (range_type T)) > 256
        ) t
        then except_tac ctxt "prove_mem_equality: unfolding large heap_update" i
        else all_tac)
    (* need to normalise_mem_accs first as it operates on typed pointer ops
       and won't function after we unpack them *)
    THEN_ALL_NEW normalise_mem_accs "prove_mem_equality" ctxt
    THEN_ALL_NEW asm_lr_simp_tac (prove_mem_equality_unpack_simpset ctxt)
    THEN_ALL_NEW simp_tac (ctxt addsimps @{thms add_ac mult_ac add_mult_comms})
  end

fun prove_mem_equality ctxt = DETERM o
    (prove_mem_equality_unchecked ctxt
    THEN_ALL_NEW SUBGOAL (fn (t, i) =>
      if exists_Const (fn (s, _) =>
                 s = @{const_name store_word8}
          orelse s = @{const_name store_word32}
          orelse s = @{const_name store_word64}
          orelse s = @{const_name heap_update}
          orelse s = @{const_name heap_update_list}) t
      then except_tac ctxt "prove_mem_equality: remaining mem upds" i
      else all_tac))

fun prove_global_equality ctxt
    = simp_tac (ctxt addsimps (#1 (get_globals_rewrites ctxt)))
        THEN' prove_mem_equality ctxt

fun clean_heap_upd_swap ctxt = DETERM o let
    val thm = @{thm disjoint_heap_update_globals_swap_rearranged}
    val thm = res_from_ctxt "clean_heap_upd_swap" "global_acc_valid" ctxt thm
    val thm = res_from_ctxt "clean_heap_upd_swap" "globals_list_distinct" ctxt thm
  in fn i => resolve_tac ctxt [@{thm trans}]  i
    THEN (resolve_tac ctxt [thm] i
      ORELSE except_tac ctxt "clean_heap_upd_swap: couldn't rtac" i)
    THEN (assume_tac ctxt i (* htd_safe assumption *)
      ORELSE except_tac ctxt "clean_heap_upd_swap: couldn't atac" i)
    THEN prove_ptr_safe "clean_upd_upd_swap" ctxt i
  end

fun clean_htd_upd_swap ctxt = let
    val thm = @{thm globals_swap_hrs_htd_update[symmetric]}
    val thm = res_from_ctxt "clean_htd_upd_swap" "global_acc_valid" ctxt thm
    val thm = res_from_ctxt "clean_htd_upd_swap" "globals_list_valid" ctxt thm
  in simp_tac (ctxt addsimps [thm])
    THEN_ALL_NEW (except_tac ctxt "clean_htd_upd_swap: not finished")
  end

fun heap_upd_kind (Const (@{const_name heap_update}, _) $ _ $ _ $ _)
    = "HeapUpd"
  | heap_upd_kind (Const (@{const_name hrs_mem}, _) $ v)
    = let
    val gs = exists_Const (fn (s, _) => s = @{const_name globals_swap}) v
    val hu = exists_Const (fn (s, _) => s = @{const_name heap_update}) v
    val htd = exists_Const (fn (s, _) => s = @{const_name hrs_htd_update}) v
  in (gs orelse raise TERM ("heap_upd_kind: hrs_mem but no globals_swap", [v]));
    if hu then "HeapUpdWithSwap" else if htd then "HTDUpdateWithSwap"
        else "GlobalUpd"
  end
  | heap_upd_kind t = raise TERM ("heap_upd_kind: unknown", [t])

fun decompose_mem_goals_init post trace ctxt = warn_schem_tac "decompose_mem_goals" ctxt
  (trace_tac ctxt "decompose_mem_goals: init" THEN' SUBGOAL (fn (t, i) =>
  (case Envir.beta_eta_contract (Logic.strip_assums_concl t) of
    @{term Trueprop} $ (Const (@{const_name const_globals_in_memory}, _) $ _ $ _ $ _)
        => let val thm = res_from_ctxt "decompose_mem_goals"
                        "globals_list_distinct" ctxt
                        @{thm const_globals_in_memory_heap_updateE}
        in (eresolve_tac ctxt [thm] THEN' assume_tac ctxt THEN' prove_ptr_safe "const_globals" ctxt)
            ORELSE' except_tac ctxt "decompose_mem_goals: const globals"
        end
    | @{term Trueprop} $ (Const (@{const_name pglobal_valid}, _) $ _ $ _ $ _)
        => asm_full_simp_tac (ctxt addsimps @{thms pglobal_valid_def}
              addsimps #3 (get_globals_rewrites ctxt))
    | @{term Trueprop} $ (@{term "(=) :: heap_mem \<Rightarrow> _"} $ x $ y) => let
        val query = (heap_upd_kind x, heap_upd_kind y)
        val _ = if trace then writeln ("decompose_mem_goals: " ^ @{make_string} query)
            else ()
      in case (heap_upd_kind x, heap_upd_kind y) of
          ("HeapUpd", "HeapUpd") => post ctxt
        | ("HeapUpdWithSwap", "HeapUpd")
            => clean_heap_upd_swap ctxt THEN' post ctxt
        | ("HeapUpd", "HeapUpdWithSwap") =>
            resolve_tac ctxt [@{thm sym}]
              THEN' clean_heap_upd_swap ctxt THEN' post ctxt
        | ("HeapUpd", "GlobalUpd") =>
            simp_tac (ctxt addsimps (#1 (get_globals_rewrites ctxt)))
              THEN_ALL_NEW (post ctxt)
        | ("GlobalUpd", "HeapUpd") =>
            simp_tac (ctxt addsimps (#1 (get_globals_rewrites ctxt)))
              THEN_ALL_NEW (post ctxt)
        | ("HTDUpdateWithSwap", _)
            => clean_htd_upd_swap ctxt
        | (_, "HTDUpdateWithSwap")
            => resolve_tac ctxt [@{thm sym}] THEN' clean_htd_upd_swap ctxt
        | _ => raise TERM ("decompose_mem_goals: mixed up "
            ^ heap_upd_kind x ^ "," ^ heap_upd_kind y, [x, y])
      end THEN_ALL_NEW warn_schem_tac "decompose_mem_goals: after"
        ctxt (K all_tac)
    | _ => K all_tac) i)
    THEN' trace_tac ctxt "decompose_mem_goals: end")

val decompose_mem_goals = decompose_mem_goals_init prove_mem_equality

fun unat_mono_tac ctxt = resolve_tac ctxt @{thms unat_mono_intro}
    THEN' ((((TRY o REPEAT_ALL_NEW (resolve_tac ctxt @{thms unat_mono_thms}))
                THEN_ALL_NEW resolve_tac ctxt [@{thm order_refl}])
            THEN_ALL_NEW except_tac ctxt "unat_mono_tac: escaped order_refl")
        ORELSE' except_tac ctxt "unat_mono_tac: couldn't get started")
    THEN' (asm_full_simp_tac (ctxt addsimps @{thms
            word_sless_to_less word_sle_to_le
        })
        THEN_ALL_NEW asm_full_simp_tac (ctxt addsimps @{thms
            word_less_nat_alt word_le_nat_alt
            unat_ucast_if_up
        })
        THEN_ALL_NEW except_tac ctxt "unat_mono_tac: unsolved")

fun dest_ptr_add_assertion ctxt = SUBGOAL (fn (t, i) =>
    if Term.exists_Const (fn (s, _) => s = @{const_name parray_valid}) t
        then (full_simp_tac (ctxt addsimps @{thms ptr_add_assertion'
            typ_uinfo_t_diff_from_typ_name parray_valid_def
            ptr_add_assertion_unfold_numeral} delsimps @{thms One_nat_def})
          THEN_ALL_NEW TRY o REPEAT_ALL_NEW (dresolve_tac ctxt
            @{thms ptr_add_assertion_uintD[rule_format]
                   ptr_add_assertion_sintD[rule_format]})
          THEN_ALL_NEW TRY o safe_goal_tac ctxt
          THEN_ALL_NEW SUBGOAL (fn (t, i) =>
            if Term.exists_Const (fn (s, _) => s = @{const_name ptr_add_assertion}
                orelse s = @{const_name ptr_add_assertion'}) t
            then except_tac ctxt "dest_ptr_add_assertion" i
            else all_tac)
        ) i
    else all_tac)

fun tactic_check' (ss, t) = (ss, tactic_check (hd ss) t)

fun graph_refine_proof_tacs csenv ctxt = let
    val ctxt = ctxt delsimps @{thms shiftl_numeral_numeral shiftl1_is_mult}
        |> Splitter.del_split @{thm if_split}
        |> Simplifier.del_cong @{thm if_weak_cong}

  in [
        (["step 1: normalise some word arithmetic. this needs",
            "to be done before any general simplification.",
            "also unfold some things that may be in assumptions",
            "and should be unfolded"],
        full_simp_tac (put_simpset HOL_basic_ss ctxt addsimps @{thms
              guard_arith_simps
              mex_def meq_def}
              addsimps [Proof_Context.get_thm ctxt "simpl_invariant_def"])),
        (["step 2: normalise a lot of things that occur in",
            "simpl->graph that are extraneous"],
        SUBGOAL (fn (t, i) =>
            asm_full_simp_tac (ctxt addsimps @{thms eq_impl_def
                    var_word32_def var_word8_def var_mem_def
                    var_word64_def var_word16_def var_ghoststate_def
                    var_htd_def var_acc_var_upd
                    var_ms_def init_vars_def
                    return_vars_def upd_vars_def save_vals_def
                    asm_args_to_list_def asm_rets_to_list_def
                    mem_upd_def mem_acc_def hrs_mem_update
                    hrs_htd_update
                    fupdate_def
                    hrs_mem_update_triv

                    (* this includes wrappers for word arithmetic
                       and other simpl actions*)
                    bvlshr_def bvashr_def bvshl_def bv_clz_def
                    }
                (* we should also unfold enumerations, since the graph
                   representation does this, and we need to normalise
                   word arithmetic the same way on both sides. *)
                addsimps (enum_simps csenv ctxt)
                (* unfold constant globals unless we can see their symbols
                   somewhere else in the goal *)
                addsimps (get_expand_const_globals ctxt t)
                (* and fold up expanded array accesses, and clean up assertion_data get/set *)
                addsimprocs [fold_of_nat_eq_Ifs_simproc, unfold_assertion_data_get_set]
            ) i)),
        (["step 3: split into goals with safe steps",
            "also derive ptr_safe assumptions from h_t_valid",
            "and adjust ptr_add_assertion facts",
            "also work on some asm_semantics problems"],
        trace_tac ctxt "step 3: init" THEN' (TRY o safe_goal_tac ctxt)
            THEN_ALL_NEW (TRY o DETERM o resolve_tac ctxt @{thms TrueI})
            THEN_ALL_NEW warn_schem_tac "step 3" ctxt (K all_tac)
            THEN_ALL_NEW (TRY o DETERM
                o REPEAT_ALL_NEW (dresolve_tac ctxt [@{thm h_t_valid_orig_and_ptr_safe}]))
            THEN_ALL_NEW (TRY o DETERM o (eresolve_tac ctxt [@{thm asm_semantics_protects_globs_revD[rule_format]}]
                THEN_ALL_NEW asm_full_simp_tac ctxt))
            THEN_ALL_NEW (TRY o safe_goal_tac ctxt)),
        (["step 4: split up memory write problems",
          "and expand ptr_add_assertion if needed."],
        trace_tac ctxt "step 4: init" THEN' decompose_mem_goals false ctxt
          THEN_ALL_NEW dest_ptr_add_assertion ctxt),
        (["step 5: normalise memory reads"],
        normalise_mem_accs "step 5" ctxt),
        (["step 6: explicitly apply some inequalities"],
        TRY o DETERM o REPEAT_ALL_NEW
            (eqsubst_either_wrap_tac ctxt @{thms machine_word_truncate_noop})),
        (["step 7: try to simplify out all remaining word logic"],
        asm_full_simp_tac (ctxt addsimps @{thms
                        pvalid_def pweak_valid_def palign_valid_def
                        field_lvalue_offset_eq array_ptr_index_def ptr_add_def
                        mask_def unat_less_helper
                        word_sle_def[THEN iffD2] word_sless_alt[THEN iffD2]
                        drop_sign_isomorphism
                        ptr_equalities_to_ptr_val
                        word_neq_0_conv_neg_conv
                        ucast_nat_def of_int_sint_scast of_int_uint_ucast
                        unat_ucast_upcasts
                        ptr_val_inj[symmetric]
                        fold_all_htd_updates
                        array_assertion_shrink_right
                        sdiv_word_def sdiv_int_def
                        signed_ge_zero_scast_eq_ucast
                        unatSuc[OF less_is_non_zero_p1'] unatSuc2[OF less_is_non_zero_p1]
                        less_shift_targeted_cast_convs
                } delsimps @{thms ptr_val_inj})),
        (["step 8: try rewriting ring equalitites",
            "this must be done after general simplification",
            "because of a bug in the simpset for 2 ^ n",
            "(unfolded in Suc notation if addition is commuted)"],
        asm_full_simp_tac (ctxt addsimps @{thms field_simps})),
        (["step 9: attack unat less-than properties explicitly"],
        TRY o unat_mono_tac ctxt)

    ]

  end

fun graph_refine_proof_full_tac csenv ctxt = EVERY
    (map (fn (ss, t) => ALLGOALS
        (t ORELSE' except_tac ctxt ("FAILED: " ^ space_implode "\n" ss)))
        (graph_refine_proof_tacs csenv ctxt))

fun graph_refine_proof_full_goal_tac csenv ctxt i t
    = (foldr1 (op THEN_ALL_NEW)
        (map snd (graph_refine_proof_tacs csenv ctxt)) i t)
        |> try Seq.hd |> (fn NONE => Seq.empty | SOME t => Seq.single t)

fun debug_tac csenv ctxt = let
    val tacs = graph_refine_proof_tacs csenv ctxt
    fun wrap_tacs [] _ t = all_tac t
      | wrap_tacs ((nms, tac) :: tacs) i t = case try ((tac) i #> Seq.hd) t
        of NONE => (warning ("step failed: " ^ commas nms); all_tac t)
         | SOME t' => ((fn _ => fn _ => all_tac t') THEN_ALL_NEW wrap_tacs tacs) i t
  in wrap_tacs tacs end

fun debug_step_tac csenv ctxt step = let
    val tac = nth (graph_refine_proof_tacs csenv ctxt) (step - 1)
    fun wrap_tac (nms, tac) i t = case try (tac i #> Seq.hd) t
        of NONE => (warning ("step failed: " ^ commas nms); all_tac t)
         | SOME t' => all_tac t'
  in wrap_tac tac end

fun simpl_to_graph_thm funs csenv ctxt nm = let
    val hints = SimplToGraphProof.mk_hints funs ctxt nm
    val init_thm = SimplToGraphProof.simpl_to_graph_upto_subgoals funs hints nm
        ctxt
    val res_thm = init_thm |> graph_refine_proof_full_tac csenv ctxt |> Seq.hd
    val _ = if Thm.nprems_of res_thm = 0 then ()
        else raise THM ("simpl_to_graph_thm: unsolved subgoals", 1, [res_thm])
    (* FIXME: make the hidden assumptions of the thm appear again *)
  in res_thm end
    handle
      TERM (s, ts) => raise TERM ("simpl_to_graph_thm: " ^ nm
        ^ ": " ^ s, ts)
    | THM (s, idx, ts) => raise THM ("simpl_to_graph_thm: " ^ nm
        ^ ": " ^ s, idx, ts)

fun test_graph_refine_proof funs csenv ctxt nm = case
    Symtab.lookup funs nm of SOME (_, _, NONE) => ("skipped " ^ nm, @{thm TrueI})
  | _ => let
    val hints = SimplToGraphProof.mk_hints funs ctxt nm
    val init_thm = SimplToGraphProof.simpl_to_graph_upto_subgoals funs hints nm ctxt
    val res_thm = init_thm |> ALLGOALS (graph_refine_proof_full_goal_tac csenv ctxt)
        |> Seq.hd
    val succ = case Thm.nprems_of res_thm of 0 => "success on "
        | n => string_of_int n ^ " failed goals: "
  in (succ ^ nm, res_thm) end handle TERM (s, ts) => raise TERM ("test_graph_refine_proof: " ^ nm
        ^ ": " ^ s, ts)

\<comment>\<open>
  Utility for configuring SimplToGraphProof with debugging features.
\<close>
type debug_config = {
  \<comment>\<open> Functions with these names won't be tested. \<close>
  skips: string list,
  \<comment>\<open> If non-empty, *only* functions with these names will be tested. \<close>
  only: string list,

  \<comment>\<open>
    Timeout for proofs. Any individual proof that takes longer
    than this will be aborted and logged.
  \<close>
  timeout: Time.time option
};

type debug = {
  config: debug_config,

  \<comment>\<open>
    Logs the names of functions when they pass or fail tests, or timeout,
    or are skipped because they don't have a definition.
  \<close>
  successes: (string list) Unsynchronized.ref,
  failures: (string list) Unsynchronized.ref,
  timeouts: (string list) Unsynchronized.ref,
  new_skips: (string list) Unsynchronized.ref
};

fun new_debug (config: debug_config): debug = {
  config = config,
  new_skips = Unsynchronized.ref [],
  successes = Unsynchronized.ref [],
  failures = Unsynchronized.ref [],
  timeouts = Unsynchronized.ref []
}

fun no_debug (): debug = new_debug { skips = [], only = [], timeout = NONE };

fun insert (dbg: debug) field x = change (field dbg) (curry (op ::) x)

fun filter_fns (dbg: debug) =
    (if null (#only (#config dbg)) then I else filter (member (op =) (#only (#config dbg)))) #>
    (if null (#skips (#config dbg)) then I else filter_out (member (op =) (#skips (#config dbg))))

fun has (dbg: debug) field = not (null (! (field dbg)))

fun interleave _ [] = []
  | interleave _ [a] = [a]
  | interleave x (a :: b :: xs) = a :: x :: interleave x (b :: xs);

\<comment>\<open>
  Produces a string that should be valid SML; useful for copy-pasting lists of functions
  to modify debug lists.
\<close>
fun render_ML_string_list xs =
  if null xs
  then "(none)"
  else
    let
      val lines = map (fn x => "\"" ^ x ^ "\"") xs |> interleave ",\n" |> List.foldr (op ^) ""
    in "[\n" ^ lines ^ "\n]" end;

fun print (dbg: debug) msg field =
  let
    val data = !(field dbg);
    val _ = writeln msg;
  in render_ML_string_list data |> writeln end

fun timeout (dbg: debug) f =
  case #timeout (#config dbg) of
      SOME time => Timeout.apply time f
    | NONE => f;

fun test_graph_refine_proof_with_def funs csenv ctxt dbg nm =
  case Symtab.lookup funs nm of
      SOME (_, _, NONE) => (insert dbg #new_skips nm; "skipped " ^ nm)
    | _ =>
      let
        val ctxt = define_graph_fun_short funs nm ctxt
        fun do_proof nm = (simpl_to_graph_thm funs csenv ctxt nm; insert dbg #successes nm)
        fun try_proof nm =
            ((timeout dbg do_proof) nm)
            handle
              TERM (message, data) =>
                (insert dbg #failures nm; raise TERM ("failure for " ^ nm ^ ": " ^ message, data))
            | THM (message, idx, data) =>
                (insert dbg #failures nm; raise THM ("failure for " ^ nm ^ ": " ^ message, idx, data))
            | Timeout.TIMEOUT t =>
                (insert dbg #timeouts nm; raise Timeout.TIMEOUT t);
        val (time, _) = Timing.timing try_proof nm
      in "success on " ^ nm ^ "  [" ^ Timing.message time ^ "]" end

fun test_all_graph_refine_proofs_after funs csenv ctxt dbg nm = let
    val ss = Symtab.keys funs
    val n = case nm of NONE => ~1 | SOME nm' => find_index (fn s => s = nm') ss
    val ss = if n = ~1 then ss else drop (n + 1) ss
    val err = prefix "ERROR for: " #> error
    val _ = map (fn s => (writeln ("testing: " ^ s);
        writeln (test_graph_refine_proof_with_def funs csenv ctxt dbg s))
      handle TERM _ => err s | TYPE _ => err s | THM _ => err s) ss
  in "success" end

fun test_all_graph_refine_proofs_parallel funs csenv ctxt dbg = let
    val ss = Symtab.keys funs |> filter_fns dbg
    fun test_and_log nm =
        (test_graph_refine_proof_with_def funs csenv ctxt dbg nm |> writeln)
        handle
          TERM (msg, _) => warning msg
        | THM (msg, _, _) => warning msg
        | Timeout.TIMEOUT _ => warning ("Timeout for " ^ nm)
    val (time, _) = Timing.timing (Par_List.map test_and_log) ss
    val time_msg = "[" ^ Timing.message time ^ "]"
    val failure_msg =
        if has dbg #failures
        then SOME "Failures! Check the `#failures` field of the debug parameter.\n"
        else NONE;
    val timeout_msg =
        if has dbg #timeouts
        then SOME "Timeouts! Check the `#timeouts` field of the debug parameter.\n"
        else NONE;
    val msg =
        if isSome failure_msg orelse isSome timeout_msg
        then SOME (Option.getOpt (failure_msg, "") ^ Option.getOpt (timeout_msg, ""))
        else NONE
  in
    case msg of
      SOME msg => error (msg ^ time_msg)
    | NONE => "success! " ^ time_msg
  end

end
\<close>

end
