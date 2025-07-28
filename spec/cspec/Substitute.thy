(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Substitute

imports
  "CKernel.Kernel_C"
  "AsmRefine.GlobalsSwap"
begin

ML \<open>

structure SubstituteSpecs = struct

val list_abs = uncurry (fold_rev (fn (x, T) => fn t => Abs (x, T, t)));

fun get_rhs thm =
    snd (Logic.dest_equals (Thm.concl_of thm))
    handle TYPE _ =>
      snd (HOLogic.dest_eq (Thm.concl_of thm));

fun get_lhs thm =
    fst (Logic.dest_equals (Thm.concl_of thm))
    handle TYPE _ =>
      fst (HOLogic.dest_eq (Thm.concl_of thm));

fun term_convert prefix convs (tm as Const (name, _)) =
    if not (String.isPrefix prefix name) then tm
    else the (Termtab.lookup convs tm)
  | term_convert _ _ tm = tm;

fun suspicious_term ctxt s t = if Term.add_var_names t [] = [] then ()
  else (tracing ("suspicious " ^ s);
    Syntax.pretty_term ctxt t |> Pretty.string_of |> tracing;
    ())

val debug_trace = ref (Bound 0);

fun convert prefix src_ctxt proc (tm as Const (name, _)) (convs, ctxt) =
  ((term_convert prefix convs tm; (convs, ctxt))
  handle Option =>
 let
    val cname = unprefix prefix name;
    val def_thm = Proof_Context.get_thm src_ctxt (cname ^ "_def")
    val rhs = get_rhs def_thm;
    val _ = suspicious_term ctxt "init rhs" rhs;
    val consts = Term.add_consts rhs [];
    val (convs, ctxt) = fold (convert prefix src_ctxt proc o Const)
        consts (convs, ctxt);
    val rhs' = map_aterms (term_convert prefix convs) rhs;
    val rhs'' = proc ctxt cname rhs';
    val _ = suspicious_term ctxt "adjusted rhs" rhs'';

  in if rhs'' aconv rhs
    then (Termtab.insert (K true) (tm, tm) convs,
        ctxt
        |> Local_Theory.begin_nested |> snd
        |> Local_Theory.abbrev Syntax.mode_default ((Binding.name cname, NoSyn), get_lhs def_thm)
        |> snd |> Local_Theory.note ((Binding.name (cname ^ "_def"), []), [def_thm])
        |> snd |> Local_Theory.end_nested
    )

  else let
      val _ = tracing ("Defining " ^ cname);

      val pre_def_ctxt = ctxt
      val b = Binding.name cname
      val ctxt = Local_Theory.begin_nested ctxt |> snd
      val ((tm', _), ctxt) = Local_Theory.define
          ((b, NoSyn), ((Thm.def_binding b, []), rhs'')) ctxt
      val tm'' = Morphism.term (Proof_Context.export_morphism ctxt pre_def_ctxt) tm'
      val ctxt = Local_Theory.end_nested ctxt

      val lhs_argTs = get_lhs def_thm |> strip_comb |> snd |> map fastype_of;
      val abs_tm = list_abs (map (pair "_") lhs_argTs, tm'')

    in (Termtab.insert (K true) (tm, abs_tm) convs, ctxt) end
  end)
  | convert _ _ _ (tm) _ = raise TERM ("convert: not Const", [tm])


fun prove_impl_tac ctxt ss =
    SUBGOAL (fn (t, n) => let
        val lhs = t |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> fst;
        val cnames = Term.add_const_names lhs []
          |> filter (String.isSuffix "_'proc");
        val unfolds = map (Proof_Context.get_thm ctxt o suffix "_def"
          o Long_Name.base_name) cnames;
      in simp_tac (put_simpset ss ctxt addsimps unfolds) n
      end);

fun convert_impls ctxt = let

    val thm = Proof_Context.get_thm ctxt "\<Gamma>_def"

    val proc_defs = (Term.add_const_names (Thm.concl_of thm) [])
      |> filter (String.isSuffix Hoare.proc_deco)
      |> map (suffix "_def" #> Proof_Context.get_thm ctxt)

    val tree_lemmata = StaticFun.prove_partial_map_thms thm
        (ctxt addsimps proc_defs)

    fun impl_name_from_proc (Const (s, _)) = s
            |> Long_Name.base_name
            |> unsuffix Hoare.proc_deco
            |> suffix HoarePackage.implementationN
      | impl_name_from_proc t = raise TERM ("impl_name_from_proc", [t])

    val saves = tree_lemmata |> map (apfst (fst #> impl_name_from_proc))

  in Local_Theory.notes (map (fn (n, t) => ((Binding.name n, []), [([t], [])])) saves)
    ctxt |> snd end

fun take_all_actions prefix src_ctxt proc tm csenv
      styargs ctxt = let
    val (_, ctxt) = convert prefix src_ctxt proc tm (Termtab.empty, ctxt);
  in ctxt
    |> convert_impls
    |> Modifies_Proofs.prove_all_modifies_goals_local csenv (fn _ => true) styargs
  end

end

\<close>

ML \<open>
fun com_rewrite f t = case fastype_of t of
    (comT as Type (@{type_name com}, [s, _, ft]))
      => let
    val gd = Const (@{const_name Guard},
                ft --> (HOLogic.mk_setT s) --> comT --> comT)
    fun add_guard ((f, gd_s), c) = gd $ f $ gd_s $ c;

    val seq = Const (@{const_name Seq}, comT --> comT --> comT);
    val skip = Const (@{const_name Skip}, comT);
    fun add_guards_to_seq gs (Const (@{const_name Seq}, _) $ a $ b)
        = seq $ add_guards_to_seq gs a $ b
      | add_guards_to_seq gs c
        = seq $ foldr add_guard skip gs $ c;

    fun add_guards c [] = c
      | add_guards ((w as Const (@{const_name While}, _)) $ S $ c) gs
        = seq $ (w $ S $ add_guards_to_seq gs c) $ foldr add_guard skip gs
      | add_guards (call as (Const (@{const_name call}, _) $ _ $ _ $ _ $ _)) gs
        = foldr add_guard (seq $ call $ foldr add_guard skip gs) gs
      | add_guards c gs = foldr add_guard c gs;

    fun inner t = case t of
      (Const (@{const_name "switch"}, T) $ v $ set_com_list) => let
        val (ss, cs) = map_split HOLogic.dest_prod
          (HOLogic.dest_list set_com_list);
        val cs' = map inner cs;
        val (v', gs) = f v;
        val (ss', gss) = map_split f ss;
        val listT = HOLogic.mk_prodT
          (HOLogic.mk_setT (range_type (domain_type T)), comT);
      in foldr add_guard (head_of t $ v' $ HOLogic.mk_list listT
            (map HOLogic.mk_prod (ss' ~~ cs')))
          (gs @ flat gss)
      end
      | _ => let
        val (h, xs) = strip_comb t;
        (* assumption: we can only get into the com type with one of the
           constructors or pseudo-constructors, which don't need rewriting,
           so we can ignore h *)
        val xTs = xs ~~ (fastype_of h |> strip_type |> fst);
        fun upd_arg (x, T) = if T = comT then (inner x, []) else f x;
        val (ys, gss) = map_split upd_arg xTs;
      in add_guards (list_comb (h, ys)) (flat gss) end
  in inner (Envir.beta_eta_contract t) end
  | _ => t;

\<close>

setup \<open>DefineGlobalsList.define_globals_list_i
  "../c/build/$L4V_ARCH/kernel_all.c_pp" @{typ globals}\<close>


locale substitute_pre
  = fixes symbol_table :: "string \<Rightarrow> addr"
      and domain :: "addr set"

begin

abbreviation
 "globals_list \<equiv> kernel_all_global_addresses.global_data_list"

end

locale kernel_all_substitute = substitute_pre
begin

ML \<open>
fun mk_rew (t as Abs (s, T, _)) = mk_rew (betapply (t, Var ((s, 0), T)))
  | mk_rew t = HOLogic.dest_eq t

val mk_varifyT = Term.map_types Logic.varifyT_global

local
val c_guard_rew =
  @{term "\<lambda>p b. Guard C_Guard {s. c_guard (p s)} b
     = Guard C_Guard {s. h_t_valid (hrs_htd (t_hrs_' (globals s))) c_guard (p s)} b"}
  |> mk_varifyT |> mk_rew

val c_guard_rew_weak =
  @{term "\<lambda>p b. Guard C_Guard {s. c_guard (p s)} b
         = Guard C_Guard {s. ptr_safe (p s) (hrs_htd (t_hrs_' (globals s)))
            \<and> c_guard (p s)} b"}
      |> mk_varifyT |> mk_rew

in
fun strengthen_c_guards ss thy s =
  if (exists (curry (op =) s) ss)
  then Pattern.rewrite_term thy [c_guard_rew_weak] []
  else Pattern.rewrite_term thy [c_guard_rew] []
end;
\<close>

lemmas global_data_defs
    = kernel_all_global_addresses.global_data_defs

lemmas globals_list_def
    = kernel_all_global_addresses.global_data_list_def

ML \<open>

(* the unvarify sets ?symbol_table back to symbol_table. be careful *)
val global_datas = @{thms global_data_defs}
  |> map (Thm.concl_of #> Logic.unvarify_global
        #> Logic.dest_equals #> snd #> Envir.beta_eta_contract)

val const_globals = map_filter
    (fn (Const (@{const_name const_global_data}, _) $ nm $ t)
        => SOME (HOLogic.dest_string nm, t)
        | _ => NONE) global_datas

local

val hrs_htd_update_guard_rew1 =
    @{term "\<lambda>u. Basic (\<lambda>s. globals_update (t_hrs_'_update (hrs_htd_update (u s))) s)
         = Guard C_Guard {s. globals_list_distinct (fst ` dom_s (u s (hrs_htd (t_hrs_' (globals s)))))
                         symbol_table globals_list}
           (Basic (\<lambda>s. globals_update (t_hrs_'_update (id hrs_htd_update (u s))) s))"}
        |> mk_rew

val hrs_htd_update_guard_rew2 =
  @{term "t_hrs_'_update (id hrs_htd_update f) = t_hrs_'_update (hrs_htd_update f)"}
  |> Logic.varify_global |> HOLogic.dest_eq;

val consts = map snd const_globals

val index_eq_set_helper
  = Syntax.parse_term @{context} (String.concat
    ["\<lambda>str t n c. {s :: globals myvars. c \<longrightarrow>",
        "h_val (hrs_mem (t_hrs_' (globals s)))",
        " (CTypesDefs.ptr_add (Ptr (symbol_table str)) (of_nat (n s)))",
        " = t s}"])

val eq_set_helper
  = Syntax.parse_term @{context} (String.concat
    ["\<lambda>str t c. {s :: globals myvars. c \<longrightarrow>",
        "h_val (hrs_mem (t_hrs_' (globals s)))",
        " (Ptr (symbol_table str)) = t}"])

val s = @{term "s :: globals myvars"}

val grab_name_str = head_of #> dest_Const #> fst #> Long_Name.base_name
    #> HOLogic.mk_string

in

fun const_global_asserts ctxt cond
  (t as (Const (@{const_name index}, _) $ arr $ n)) = if member (op =) consts arr
    then [(index_eq_set_helper $ grab_name_str arr
        $ lambda s t $ lambda s n $ cond) |> Syntax.check_term ctxt]
    else []
  | const_global_asserts ctxt cond (Const c) = if member (op =) consts (Const c)
    then [(eq_set_helper $ grab_name_str (Const c) $ Const c $ cond)
        |> Syntax.check_term ctxt]
    else []
  | const_global_asserts ctxt cond (f $ x) = if member (op =) consts (f $ x)
    then [(eq_set_helper $ grab_name_str (f $ x) $ (f $ x) $ cond)
        |> Syntax.check_term ctxt]
    else const_global_asserts ctxt cond f @ const_global_asserts ctxt cond x
  | const_global_asserts ctxt cond (a as Abs (_, @{typ "globals myvars"}, _))
    = const_global_asserts ctxt cond (betapply (a, s))
  | const_global_asserts ctxt cond (Abs (_, _, t))
    = const_global_asserts ctxt cond t
  | const_global_asserts _ _ _ = []

fun guard_rewritable_globals const_cond ctxt =
  Pattern.rewrite_term @{theory} [hrs_htd_update_guard_rew2] []
  o Pattern.rewrite_term @{theory} [hrs_htd_update_guard_rew1] []
  o com_rewrite (fn t =>
     (t, map (pair @{term C_Guard})
        (case const_cond of SOME cond => const_global_asserts ctxt cond t
                | NONE => [])))

val guard_htd_updates_with_domain = com_rewrite
  (fn t => if fastype_of t = @{typ "globals myvars \<Rightarrow> globals myvars"}
        andalso Term.exists_Const (fn (s, _) => s = @{const_name "hrs_htd_update"}) t
        then (t, [(@{term MemorySafety}, betapply (@{term "\<lambda>f :: globals myvars \<Rightarrow> globals myvars.
                {s. htd_safe domain (hrs_htd (t_hrs_' (globals s)))
              \<and> htd_safe domain (hrs_htd (t_hrs_' (globals (f s))))}"}, t))])
        else (t, []))

val guard_halt = com_rewrite
  (fn t => if t = @{term "halt_'proc"}
    then (t, [(@{term DontReach}, @{term "{} :: globals myvars set"})])
    else (t, []))

fun acc_ptr_adds (Const (@{const_name h_val}, _) $ m $ (Const (@{const_name ptr_add}, _) $ p $ n))
    = [(p, n, true)] @ maps acc_ptr_adds [m, p, n]
  | acc_ptr_adds (Const (@{const_name heap_update}, _) $ (Const (@{const_name ptr_add}, _) $ p $ n))
    = [(p, n, true)] @ maps acc_ptr_adds [p, n]
  | acc_ptr_adds (Const (@{const_name ptr_add}, _) $ p $ n)
    = [(p, n, false)] @ maps acc_ptr_adds [p, n]
  | acc_ptr_adds (f $ x) = maps acc_ptr_adds [f, x]
  | acc_ptr_adds (abs as Abs (_, T, t)) = if T = @{typ "globals myvars"}
    then acc_ptr_adds (betapply (abs, @{term "s :: globals myvars"}))
    else acc_ptr_adds t
  | acc_ptr_adds _ = []

fun mk_bool true = @{term True} | mk_bool false = @{term False}

val guard_acc_ptr_adds = com_rewrite
  (fn t => (t, acc_ptr_adds t |> map (fn (p, n, strong) => let
    val assn = Const (@{const_name ptr_add_assertion'},
            fastype_of p --> @{typ "int \<Rightarrow> bool \<Rightarrow> heap_typ_desc \<Rightarrow> bool"})
        $ p $ n $ mk_bool strong
        $ @{term "hrs_htd (t_hrs_' (globals (s :: globals myvars)))"}
    val gd = HOLogic.mk_Collect ("s", @{typ "globals myvars"}, assn)
  in (@{term MemorySafety}, gd) end)))

end

\<close>

cond_sorry_modifies_proofs SORRY_MODIFIES_PROOFS

ML \<open>
  Feedback.verbosity_level := ~1;
\<close>

local_setup \<open>
SubstituteSpecs.take_all_actions
  "Kernel_C.kernel_all_global_addresses."
  (Locale.init "Kernel_C.kernel_all_global_addresses" @{theory})
  (fn ctxt => fn s => guard_rewritable_globals NONE ctxt
    o (strengthen_c_guards ["memset_body", "memcpy_body", "memzero_body"]
          (Proof_Context.theory_of ctxt) s)
    o guard_halt
    o guard_htd_updates_with_domain
    o guard_acc_ptr_adds)
  @{term kernel_all_global_addresses.\<Gamma>}
  (CalculateState.get_csenv @{theory} "../c/build/$L4V_ARCH/kernel_all.c_pp" |> the)
  [@{typ "globals myvars"}, @{typ int}, @{typ strictc_errortype}]
\<close>

end

end
