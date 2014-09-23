theory ProveGraphRefine

imports GraphRefine
  GlobalsSwap FieldAccessors

begin

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
  by simp_all

lemma word_neq_0_conv_neg_conv:
  "(\<not> 0 < (n :: ('a :: len) word)) = (n = 0)"
  by (cases "n = 0", simp_all)

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
  "drop_sign (- y) = - drop_sign y"
  "drop_sign (if P then x else y) = (if P then drop_sign x else drop_sign y)"
  by (simp_all add: drop_sign_def word_less_def
                    word_le_def word_sless_def word_sle_def
                    sint_drop_sign_isomorphism[unfolded drop_sign_def]
                    word_uint.Rep_inject[symmetric]
                    uint_up_ucast is_up_def source_size_def
                    target_size_def word_size
                    uint_word_arith_bintrs
               del: word_uint.Rep_inject)

lemma drop_sign_isomorphism_bitwise:
  "drop_sign (x AND y) = drop_sign x AND drop_sign y"
  "drop_sign (bitOR x y) = bitOR (drop_sign x) (drop_sign y)"
  "drop_sign (x XOR y) = drop_sign x XOR drop_sign y"
  "drop_sign (~~ y) = ~~ drop_sign y"
  "drop_sign (shiftl x n) = shiftl (drop_sign x) n"
  "drop_sign (shiftr x n) = shiftr (drop_sign x) n"
  "drop_sign (sshiftr x n) = sshiftr (drop_sign x) n"
  "drop_sign (ucast z) = ucast z"
  "drop_sign (scast z) = scast z"
  "ucast x = ucast (drop_sign x)"
  "scast x = scast (drop_sign x)"
  by (rule word_eqI
          | simp add: word_size drop_sign_def nth_ucast nth_shiftl
                      nth_shiftr nth_sshiftr word_ops_nth_size
                      nth_scast
          | safe
          | simp add: test_bit_bin)+

lemma drop_sign_number[simp]:
  "drop_sign (numeral n) = numeral n"
  "drop_sign (- numeral n) = - numeral n"
  "drop_sign 0 = 0" "drop_sign 1 = 1"
  by (simp_all add: drop_sign_def ucast_def)

lemmas drop_sign_isomorphism
    = drop_sign_isomorphism_ariths
        drop_sign_isomorphism_bitwise
        ucast_id 

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

lemma Collect_const_mem:
  "(x \<in> (if P then UNIV else {})) = P"
  by simp

definition word32_truncate_nat :: "nat => word32 \<Rightarrow> word32"
where
  "word32_truncate_nat n x = (if unat x \<le> n then x else of_nat n)"

lemma word32_truncate_noop:
  "unat x < Suc n \<Longrightarrow> word32_truncate_nat n x = x"
  by (simp add: word32_truncate_nat_def)

lemma fold_of_nat_eq_Ifs_proof:
  "\<lbrakk> unat (x :: word32) \<notin> set ns \<Longrightarrow> y = z;
      \<And>n. n \<in> set ns \<Longrightarrow> x = of_nat n \<Longrightarrow> f n = z \<rbrakk>
    \<Longrightarrow> foldr (\<lambda>n v. if x = of_nat n then f n else v) ns y = z"
  apply (induct ns)
   apply simp
  apply (atomize(full))
  apply clarsimp
  done

lemma fold_of_nat_eq_Ifs:
  "m < 2 ^ 32
    \<Longrightarrow> foldr (\<lambda>n v. if x = of_nat n then f n else v) [0 ..< m] (f m)
        = f (unat (word32_truncate_nat m x))"
  apply (rule fold_of_nat_eq_Ifs_proof)
   apply (simp_all add: word32_truncate_nat_def unat_of_nat)
  done

lemma of_int_sint_scast:
  "of_int (sint x) = scast x"
  by (simp add: scast_def word_of_int)

ML {*
fun preserve_skel_conv consts arg_conv ct = let
    val (hd, xs) = strip_comb (term_of ct)
    val self = preserve_skel_conv consts arg_conv
  in if is_Const hd andalso member (op =) consts
        (fst (dest_Const hd))
    then  if null xs then Conv.all_conv ct
        else Conv.combination_conv self self ct
    else arg_conv ct end

fun fold_of_nat_eq_Ifs ctxt tm = let
    fun recr (Const (@{const_name If}, _)
            $ (@{term "op = :: word32 => _"} $ _ $ n) $ y $ z)
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
    val thy = Proof_Context.theory_of ctxt
    val m = HOLogic.mk_number @{typ nat} (length vs - 1)
    val conv = preserve_skel_conv [fst (dest_Const @{term "op ==>"}),
            @{const_name Trueprop}, fst (dest_Const @{term "op =="}),
            @{const_name If}]
        (Simplifier.rewrite ctxt)
    val thm = @{thm fold_of_nat_eq_Ifs}
      |> cterm_instantiate [(@{cpat "?f :: nat \<Rightarrow> ?'a"}, cterm_of thy pat),
          (@{cpat "?m :: nat"}, cterm_of thy m)]
      |> simplify (put_simpset HOL_basic_ss ctxt
          addsimprocs [Word_Bitwise_Tac.expand_upt_simproc]
          addsimps @{thms foldr.simps id_apply o_apply})
      |> mk_meta_eq
      |> Conv.fconv_rule conv
  in thm end

val fold_of_nat_eq_Ifs_simproc = Simplifier.simproc_global_i
  @{theory} "fold_of_nat_eq_Ifs"
  [@{term "If (x = 0) y z"}] (try o fold_of_nat_eq_Ifs)
*}


ML {*
fun wrap_tac tac i t = let
    val t' = Goal.restrict i 1 t
    val r = tac 1 t'
  in case Seq.pull r of NONE => Seq.empty
    | SOME (t'', _) => Seq.single (Goal.unrestrict i t'')
  end

fun eqsubst_wrap_tac ctxt thms = wrap_tac (EqSubst.eqsubst_tac ctxt [0] thms)
fun eqsubst_asm_wrap_tac ctxt thms = wrap_tac (EqSubst.eqsubst_asm_tac ctxt [0] thms)
fun eqsubst_either_wrap_tac ctxt thms = (eqsubst_asm_wrap_tac ctxt thms
    ORELSE' eqsubst_wrap_tac ctxt thms)
*}

ML {*
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
  | get_c_type_size _ (Type (@{type_name ptr}, [_])) = 4
  | get_c_type_size ctxt (T as Type (s, _)) = let
    val thm = Proof_Context.get_thm ctxt (s ^ "_size")
      handle ERROR _ => raise TYPE ("get_c_type_size: couldn't get size", [T], [])
  in Thm.rhs_of thm |> term_of |> HOLogic.dest_number |> snd end
  | get_c_type_size _ T = raise TYPE ("get_c_type_size:", [T], [])

fun enum_simps csenv ctxt = let
    val Absyn.CE ecenv = ProgramAnalysis.cse2ecenv csenv;
  in
    #enumenv ecenv |> Symtab.dest
       |> map (Proof_Context.get_thm ctxt o suffix "_def" o fst)
  end

fun safe_goal_tac_no_iff ctxt =
  REPEAT_ALL_NEW (DETERM o CHANGED o safe_steps_tac ctxt)

fun res_from_ctxt tac_name thm_name ctxt thm = let
    val thm_from_ctxt = Proof_Context.get_thm ctxt thm_name
      handle ERROR _ => raise THM (tac_name ^ ": need thm " ^ thm_name, 1, [])
  in thm_from_ctxt RS thm
    handle THM _ => raise THM (tac_name ^ ": need thm to resolve: " ^ thm_name,
        1, [thm_from_ctxt, thm])
  end

val except_tac = SimplToGraphProof.except_tac

fun prove_ptr_safe reason ctxt = DETERM o
    (TRY o REPEAT_ALL_NEW (eqsubst_either_wrap_tac ctxt
                @{thms array_ptr_index_coerce}
            )
        THEN_ALL_NEW asm_simp_tac (ctxt addsimps
            @{thms ptr_safe_field[unfolded typ_uinfo_t_def]
                   ptr_safe_Array_element unat_less_helper
                   h_t_valid_Array_element' h_t_valid_field})
        THEN_ALL_NEW except_tac ctxt
            ("prove_ptr_safe: failed for " ^ reason)
    )

fun get_disjoint_h_val_globals_swap ctxt =
    @{thm disjoint_h_val_globals_swap_insert}
        |> res_from_ctxt "prove_heap_update_id" "global_acc_valid" ctxt
        |> res_from_ctxt "prove_heap_update_id" "globals_list_distinct" ctxt

fun prove_heap_update_id ctxt = DETERM o let
    val thm = get_disjoint_h_val_globals_swap ctxt
  in fn i => (resolve_tac @{thms heap_update_id_Array heap_update_id} i
        ORELSE except_tac ctxt "prove_heap_update_id: couldn't init" i)
    THEN (simp_tac ctxt
    THEN_ALL_NEW (* simp_tac will solve goal unless globals swap involved *)
    ((rtac thm
      ORELSE' (rtac @{thm sym} THEN' rtac thm)
      ORELSE' except_tac ctxt "prove_heap_update_id: couldn't rtac")
    THEN' (atac (* htd_safe assumption *)
      ORELSE' except_tac ctxt "prove_heap_update_id: couldn't atac")
    THEN' prove_ptr_safe "prove_heap_update" ctxt)) i
  end

fun get_field_h_val_rewrites ctxt =
    Proof_Context.get_thms ctxt "field_h_val_rewrites"
        handle ERROR _ => raise THM
            ("run add_field_h_val_rewrites on ctxt", 1, [])

fun get_globals_rewrites ctxt = let
    val gsr = Proof_Context.get_thms ctxt "globals_swap_rewrites"
    val cgr = Proof_Context.get_thms ctxt "const_globals_rewrites_with_swap"
  in (gsr, cgr) end
        handle ERROR _ => raise THM
            ("run add_globals_swap_rewrites on ctxt", 1, [])

fun normalise_mem_accs ctxt = DETERM o let
    val init_simps = @{thms hrs_mem_update
                       heap_access_Array_element'
                       o_def
            } @ get_field_h_val_rewrites ctxt
        @ #2 (get_globals_rewrites ctxt)
        @ #1 (get_globals_rewrites ctxt)
    val h_val = get_disjoint_h_val_globals_swap ctxt
    val disjoint_h_val_tac
    = (eqsubst_asm_wrap_tac ctxt [h_val] ORELSE' eqsubst_wrap_tac ctxt [h_val])
         THEN' (atac ORELSE' except_tac ctxt "normalise_mem_accs: couldn't atac")
  in
    asm_full_simp_tac (ctxt addsimps init_simps addsimps [h_val])
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
              => prove_ptr_safe "normalise_mem_accs" ctxt i
            | @{term Trueprop} $ (Const (@{const_name ptr_safe}, _) $ _ $ _)
              => prove_ptr_safe "normalise_mem_accs" ctxt i
            | _ => all_tac)
    THEN_ALL_NEW full_simp_tac (ctxt addsimps @{thms h_val_ptr h_val_word32 h_val_word8})
  end

val heap_update_id_nonsense
    = Thm.trivial @{cpat "Trueprop
        (heap_update ?p (h_val ?hp' ?p) (hrs_mem ?hrs) = hrs_mem ?hrs)"}

fun prove_mem_equality ctxt = DETERM o let
    val init_simpset = ctxt
        addsimps @{thms hrs_mem_update heap_update_Array_update
               heap_access_Array_element'
               o_def
        } @ get_field_h_val_rewrites ctxt
    val unpack_simpset = ctxt
        addsimps @{thms heap_update_def to_bytes_array
               heap_update_list_append heap_list_update_ptr heap_list_update_word32
               h_val_word8 heap_list_update_word8
               field_lvalue_offset_eq ptr_add_def
               array_ptr_index_def
               h_val_word32 h_val_ptr
               take_heap_list_min drop_heap_list_general
               ucast_nat_def of_int_sint_scast
        } @ Proof_Context.get_thms ctxt "field_to_bytes_rewrites"
        addsimprocs [Word_Bitwise_Tac.expand_upt_simproc]
      handle ERROR _ => raise THM
        ("prove_mem_equality: run add_field_to_bytes_rewrites on ctxt", 1, [])

    fun heap_update_id_proofs ctxt = 
        REPEAT_ALL_NEW (eqsubst_wrap_tac ctxt [heap_update_id_nonsense]
            THEN' prove_heap_update_id ctxt)

  in simp_tac init_simpset
    THEN_ALL_NEW (TRY o REPEAT_ALL_NEW ((eqsubst_wrap_tac ctxt
            @{thms heap_access_Array_element' heap_update_Array_update})
        THEN_ALL_NEW simp_tac init_simpset))
    THEN_ALL_NEW TRY o heap_update_id_proofs ctxt
    THEN_ALL_NEW SUBGOAL (fn (t, i) => if
        exists_Const (fn (s, T) => s = @{const_name heap_update}
            andalso get_c_type_size ctxt (domain_type (range_type T)) > 256
        ) t
        then except_tac ctxt "prove_mem_equality: unfolding large heap_update" i
        else all_tac)
    (* need to normalise_mem_accs first as it operates on typed pointer ops
       and won't function after we unpack them *)
    THEN_ALL_NEW normalise_mem_accs ctxt
    THEN_ALL_NEW simp_tac unpack_simpset
    THEN_ALL_NEW simp_tac (ctxt addsimps @{thms store_word32s_equality_fold
        store_word32s_equality_final add.commute})
    THEN_ALL_NEW simp_tac (ctxt addsimprocs [store_word32s_equality_simproc]
        addsimps @{thms store_word32s_equality_final add.commute})
    THEN_ALL_NEW SUBGOAL (fn (t, i) => if exists_Const
            (fn (s, _) => s = @{const_name store_word32}
                orelse s = @{const_name heap_update}
                orelse s = @{const_name heap_update_list}) t
        then except_tac ctxt "prove_mem_equality: remaining mem upds" i
        else all_tac)
  end

fun prove_global_equality ctxt
    = simp_tac (ctxt addsimps (#1 (get_globals_rewrites ctxt)))
        THEN' prove_mem_equality ctxt

fun clean_heap_upd_swap ctxt = DETERM o let
    val thm = @{thm disjoint_heap_update_globals_swap_rearranged}
    val thm = res_from_ctxt "clean_heap_upd_swap" "global_acc_valid" ctxt thm
    val thm = res_from_ctxt "clean_heap_upd_swap" "globals_list_distinct" ctxt thm
  in fn i => rtac @{thm trans}  i
    THEN (rtac thm i
      ORELSE except_tac ctxt "clean_heap_upd_swap: couldn't rtac" i)
    THEN (atac i (* htd_safe assumption *)
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

fun decompose_mem_goals trace ctxt = SUBGOAL (fn (t, i) =>
  case Envir.beta_eta_contract (Logic.strip_assums_concl t) of
    @{term Trueprop} $ (Const (@{const_name const_globals_in_memory}, _) $ _ $ _ $ _)
        => let val thm = res_from_ctxt "decompose_mem_goals"
                        "globals_list_distinct" ctxt
                        @{thm const_globals_in_memory_heap_updateE}
        in (etac thm THEN' atac THEN' prove_ptr_safe "const_globals" ctxt)
            ORELSE' except_tac ctxt "decompose_mem_goals: const globals"
        end i
    | @{term Trueprop} $ (@{term "op = :: heap_mem \<Rightarrow> _"} $ x $ y) => let
        val query = (heap_upd_kind x, heap_upd_kind y)
        val _ = if trace then writeln ("decompose_mem_goals: " ^ @{make_string} query)
            else ()
      in case (heap_upd_kind x, heap_upd_kind y) of
          ("HeapUpd", "HeapUpd") => prove_mem_equality ctxt i
        | ("HeapUpdWithSwap", "HeapUpd")
            => clean_heap_upd_swap ctxt i THEN prove_mem_equality ctxt i
        | ("HeapUpd", "HeapUpdWithSwap") =>
            rtac @{thm sym} i THEN clean_heap_upd_swap ctxt i THEN prove_mem_equality ctxt i
        | ("HeapUpd", "GlobalUpd") => prove_global_equality ctxt i
        | ("GlobalUpd", "HeapUpd") => prove_global_equality ctxt i
        | ("HTDUpdateWithSwap", _)
            => clean_htd_upd_swap ctxt i
        | (_, "HTDUpdateWithSwap")
            => rtac @{thm sym} i THEN clean_htd_upd_swap ctxt i
        | _ => raise TERM ("decompose_mem_goals: mixed up "
            ^ heap_upd_kind x ^ "," ^ heap_upd_kind y, [x, y])
      end
    | _ => all_tac)

fun unat_mono_tac ctxt = resolve_tac @{thms unat_mono_intro}
    THEN' ((((TRY o REPEAT_ALL_NEW (resolve_tac @{thms unat_mono_thms}))
                THEN_ALL_NEW rtac @{thm order_refl})
            THEN_ALL_NEW except_tac ctxt "unat_mono_tac: escaped order_refl")
        ORELSE' except_tac ctxt "unat_mono_tac: couldn't get started")
    THEN' (asm_full_simp_tac (ctxt addsimps @{thms
            word_sless_to_less word_sle_to_le
            extra_sle_sless_unfolds
        })
        THEN_ALL_NEW asm_full_simp_tac (ctxt addsimps @{thms
            word_less_nat_alt word_le_nat_alt
            unat_ucast_if_up extra_sle_sless_unfolds
        })
        THEN_ALL_NEW except_tac ctxt "unat_mono_tac: unsolved")

fun tactic_check' (ss, t) = (ss, tactic_check (hd ss) t)

fun graph_refine_proof_tacs csenv ctxt = let
    (* FIXME: fix shiftr_no and sshiftr_no in Word *)
    val ctxt = ctxt delsimps @{thms shiftr_no sshiftr_no shiftl_numeral}
        |> Splitter.del_split @{thm split_if}
        |> Simplifier.del_cong @{thm if_weak_cong}

  in [
        (["step 1: normalise some word arithmetic. this needs",
            "to be done before any general simplification.",
            "also unfold some things that may be in assumptions",
            "and should be unfolded"],
        full_simp_tac ((put_simpset HOL_basic_ss ctxt) addsimps @{thms
              signed_arith_ineq_checks_to_eq_word32
              signed_arith_eq_checks_to_ord
              signed_mult_eq_checks32_to_64
              signed_shift_guard_to_word_32
              mex_def meq_def}
              addsimps [Proof_Context.get_thm ctxt "simpl_invariant_def"])),
        (["step 2: normalise a lot of things that occur in",
            "simpl->graph that are extraneous"],
        asm_full_simp_tac (ctxt addsimps @{thms eq_impl_def
                    var_word32_def var_word8_def var_mem_def
                    var_htd_def var_acc_var_upd
                    var_ms_def init_vars_def
                    return_vars_def upd_vars_def save_vals_def
                    mem_upd_def mem_acc_def hrs_mem_update
                    hrs_htd_update
                    fupdate_def

                    (* this includes wrappers for word arithmetic
                       and other simpl actions*)
                    bvlshr_def bvashr_def bvshl_def bv_clz_def

                    (* and some stupidity *)
                    Collect_const_mem
                    }
                (* we should also unfold enumerations, since the graph
                   representation does this, and we need to normalise
                   word arithmetic the same way on both sides. *)
                addsimps (enum_simps csenv ctxt)
                (* and fold up expanded array accesses *)
                addsimprocs [fold_of_nat_eq_Ifs_simproc]
            )),
        (["step 3: split into goals with safe steps",
            "also derive ptr_safe assumptions from h_t_valid"],
        (TRY o safe_goal_tac_no_iff ctxt)
            THEN_ALL_NEW (TRY o DETERM o REPEAT_ALL_NEW (dtac @{thm h_t_valid_orig_and_ptr_safe}))
            THEN_ALL_NEW (TRY o safe_goal_tac_no_iff ctxt)),
        (["step 4: split up memory write problems."],
        decompose_mem_goals false ctxt),
        (["step 5: normalise memory reads"],
        normalise_mem_accs ctxt),
        (["step 6: explicitly apply some inequalities"],
        TRY o DETERM o REPEAT_ALL_NEW
            (eqsubst_either_wrap_tac ctxt @{thms word32_truncate_noop})),
        (["step 7: try to simplify out all remaining word logic"],
        asm_full_simp_tac (ctxt addsimps @{thms
                        pvalid_def pweak_valid_def palign_valid_def
                        field_lvalue_offset_eq array_ptr_index_def ptr_add_def
                        mask_def unat_less_helper
                        word_sle_def[THEN iffD2] word_sless_alt[THEN iffD2]
                        drop_sign_isomorphism max_word_minus
                        ptr_equalities_to_ptr_val
                        extra_sle_sless_unfolds
                        word_neq_0_conv_neg_conv
                        ucast_nat_def
                        (* ucast_id *) scast_id of_int_sint_scast
                        ptr_val_inj[symmetric]
                        fold_all_htd_updates
                }
                delsimps @{thms ptr_val_inj}
            )),
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

fun graph_refine_proof_full_goal_tac csenv ctxt
    = (foldr1 (op THEN_ALL_NEW)
        (map snd (graph_refine_proof_tacs csenv ctxt)))

fun simpl_to_graph_thm funs csenv ctxt nm = let
    val hints = SimplToGraphProof.mk_hints funs ctxt nm
    val init_thm = SimplToGraphProof.simpl_to_graph_upto_subgoals funs hints nm
        ctxt
    val res_thm = init_thm |> graph_refine_proof_full_tac csenv ctxt |> Seq.hd
    val _ = if Thm.nprems_of res_thm = 0 then ()
        else raise THM ("simpl_to_graph_thm: unsolved subgoals", 1, [res_thm])
    (* FIXME: make the hidden assumptions of the thm appear again *)
  in res_thm end

fun test_graph_refine_proof funs csenv ctxt nm = case
    Symtab.lookup funs nm of SOME (_, _, NONE) => "skipped " ^ nm
  | _ => let
    val ctxt = define_graph_fun_short funs nm ctxt
  in simpl_to_graph_thm funs csenv ctxt nm;
    "success on " ^ nm end

fun test_all_graph_refine_proofs_after funs csenv ctxt nm = let
    val ss = Symtab.keys funs
    val n = case nm of NONE => ~1 | SOME nm' => find_index (fn s => s = nm') ss
    val ss = if n = ~1 then ss else drop (n + 1) ss
    val err = prefix "ERROR for: " #> error
    val _ = map (fn s => (writeln ("testing: " ^ s);
        writeln (test_graph_refine_proof funs csenv ctxt s))
      handle TERM _ => err s | TYPE _ => err s | THM _ => err s) ss
  in "success" end

end
*}

end
