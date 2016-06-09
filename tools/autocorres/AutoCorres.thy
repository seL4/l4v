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
 * Top-level AutoCorres theorem.
 *)

theory AutoCorres
imports
  SimplConv
  ExceptionRewrite
  L1Valid
  LocalVarExtract
  L2Peephole
  L2Opt
  TypeStrengthen
  Polish
  TypHeapSimple
  HeapLift
  WordAbstract
  "../../lib/Monad_WP/OptionMonadWP"
  "../../lib/Apply_Trace"
  AutoCorresSimpset
  "../../lib/ml-helpers/TermPatternAntiquote"
  keywords "autocorres" :: thy_decl
begin

(* Remove various rules from the default simpset that don't really help. *)
declare word_neq_0_conv [simp del]
declare neq0_conv [simp del]
declare fun_upd_apply[simp del]

declare hoare_wp_combsE(4) [wp del, wp_comb del]
declare hoare_wp_combsE(5) [wp del, wp_comb del]
declare hoare_wp_combsE(6) [wp del, wp_comb del]

lemmas [wp del, wp_comb del] = hoare_wp_state_combsE

declare hoare_wp_combs(1)  [wp del, wp_comb del]
declare hoare_wp_combs(3)  [wp del, wp_comb del]

(* Machinery for generating final corres thm *)
lemma corresTA_trivial: "corresTA (\<lambda>_. True) (\<lambda>x. x) (\<lambda>x. x) A A"
  apply (auto intro: corresXF_I)
  done

(* Dummy preconditions for more convenient usage *)
lemma L2Tcorres_trivial_from_local_var_extract:
  "L2corres st rx ex P A C \<Longrightarrow> L2Tcorres id A A"
  by (rule L2Tcorres_id)

lemma corresTA_trivial_from_heap_lift:
  "L2Tcorres st A C \<Longrightarrow> corresTA (\<lambda>_. True) (\<lambda>x. x) (\<lambda>x. x) A A"
  by (rule corresTA_trivial)


lemma corresXF_from_L2_call:
  "L2_call c_WA = A \<Longrightarrow> corresXF (\<lambda>s. s) (\<lambda>rv s. rv) y (\<lambda>_. True) A c_WA"
  apply (clarsimp simp: corresXF_def L2_call_def L2_defs)
  apply (monad_eq split: sum.splits)
  apply force
  done

(* The final ac_corres theorem. *)
lemma ac_corres_chain:
"\<lbrakk> L1corres check_termination Gamma c_L1 c;
   L2corres st_L2 rx_L2 (\<lambda>_. ()) P_L2 c_L2 c_L1;
   L2Tcorres st_HL c_HL c_L2;
   corresTA P_WA rx_WA ex_WA c_WA c_HL;
   L2_call c_WA = A
 \<rbrakk> \<Longrightarrow>
  ac_corres (st_HL o st_L2) check_termination Gamma (rx_WA o rx_L2) (P_L2 and (P_WA o st_HL o st_L2)) A c"
  apply (rule ccorresE_corresXF_merge)
       apply (unfold L1corres_alt_def)
       apply assumption
      apply (unfold L2corres_def L2Tcorres_def corresTA_def)
      apply (drule corresXF_from_L2_call)
      apply ((drule (1) corresXF_corresXF_merge)+, assumption)
     apply (clarsimp simp: L2_call_def L2_defs)
     apply (rule handleE'_nothrow_rhs)
     apply simp
    apply clarsimp
   apply clarsimp
  apply clarsimp
  done

(*
 * Functions that don't have a body in the C file (i.e., they are
 * prototyped and called, but are never defined) will be abstracted
 * into a "fail" command by AutoCorres.
 *
 * More accurately, they will be abstracted into:
 *
 *     guard (\<lambda>s. INVALID_FUNCTION)
 *
 * where "INVALID_FUNCTION" is "False").
 *
 * We convert this above form into this alternative definition, so
 * users have a better idea what is going on.
 *)
definition "FUNCTION_BODY_NOT_IN_INPUT_C_FILE \<equiv> fail"

lemma [polish]:
  "guard (\<lambda>s. UNDEFINED_FUNCTION) \<equiv> FUNCTION_BODY_NOT_IN_INPUT_C_FILE"
  "(FUNCTION_BODY_NOT_IN_INPUT_C_FILE >>= m) = FUNCTION_BODY_NOT_IN_INPUT_C_FILE"
  "unknown >>= (\<lambda>x. FUNCTION_BODY_NOT_IN_INPUT_C_FILE) = FUNCTION_BODY_NOT_IN_INPUT_C_FILE"
  "unknown >>= (K_bind FUNCTION_BODY_NOT_IN_INPUT_C_FILE) = FUNCTION_BODY_NOT_IN_INPUT_C_FILE"
  by (monad_eq simp: UNDEFINED_FUNCTION_def FUNCTION_BODY_NOT_IN_INPUT_C_FILE_def)+

(* Rewrites that will be applied before collecting statistics. *)
lemmas ac_statistics_rewrites =
    (* Setup "L1_seq" to have a sane lines-of-spec measurement. *)
    L1_seq_def bindE_K_bind [THEN eq_reflection]
    (* Convert L2 to standard exception monads. *)
    L2_defs'

ML_file "../../lib/set.ML"
ML_file "trace_antiquote.ML"
ML_file "mkterm_antiquote.ML"
ML_file "utils.ML"
ML_file "autocorres_trace.ML"
ML_file "autocorres_data.ML"
ML_file "statistics.ML"
ML_file "program_info.ML"
ML_file "function_info.ML"
ML_file "prog.ML"
ML_file "autocorres_util.ML"
ML_file "exception_rewrite.ML"
ML_file "simpl_conv.ML"
ML_file "l2_opt.ML"
ML_file "local_var_extract.ML"
ML_file "record_utils.ML"
ML_file "heap_lift_base.ML"
ML_file "heap_lift.ML"
ML_file "word_abstract.ML"
ML_file "pretty_bound_var_names.ML"
ML_file "monad_convert.ML"
ML_file "type_strengthen.ML"
ML_file "autocorres.ML"

declare [[ML_print_depth=42]]
ML_file "autocorres_util2.ML"
ML_file "simpl_conv2.ML"
ML_file "local_var_extract2.ML"

(* Setup "autocorres" keyword. *)
ML {*
  Outer_Syntax.command @{command_keyword "autocorres"}
    "Abstract the output of the C parser into a monadic representation."
    (AutoCorres.autocorres_parser >>
      (Toplevel.theory o (fn (opt, filename) => AutoCorres.do_autocorres opt filename)))
*}

ML \<open>

fun assume_called_functions_corres ctxt fn_info callees
    get_fn_type get_fn_assumption get_fn_args get_const_name callers_measure_var =
let
  (* Assume the existence of a function, along with a theorem about its
   * behaviour. *)
  fun assume_func ctxt fn_name is_recursive_call =
  let
    val fn_args = get_fn_args fn_name

    (* Fix a variable for the function. *)
    val ([fixed_fn_name], ctxt') = Variable.variant_fixes [get_const_name fn_name] ctxt
    val fn_free = Free (fixed_fn_name, get_fn_type fn_name)

    (* Fix a variable for the measure and function arguments. *)
    val (measure_var_name :: arg_names, ctxt'')
        = Variable.variant_fixes ("rec_measure'" :: (map fst fn_args)) ctxt'
    val fn_arg_terms = map (fn (n, T) => Free (n, T)) (arg_names ~~ (map snd fn_args))
    val my_measure_var = Free (measure_var_name, @{typ nat})

    (*
     * A measure variable is needed to handle recursion: for recursive calls,
     * we need to decrement the caller's input measure value (and our
     * assumption will need to assume this to). This is so we can later prove
     * termination of our function definition: the measure always reaches zero.
     *
     * Non-recursive calls can have a fresh value.
     *)
    val measure_var =
      if is_recursive_call then
        @{const "recguard_dec"} $ callers_measure_var
      else
        my_measure_var

    (* Create our assumption. *)
    val assumption =
        get_fn_assumption ctxt'' fn_name fn_free fn_arg_terms
            is_recursive_call measure_var
        |> fold Logic.all (rev ((if is_recursive_call then [] else [my_measure_var]) @ fn_arg_terms))
        |> Sign.no_vars ctxt'
        |> Thm.cterm_of ctxt'
    val ([thm], ctxt''') = Assumption.add_assumes [assumption] ctxt'

    (* Generate a morphism for escaping this context. *)
    val m = (Assumption.export_morphism ctxt''' ctxt')
        $> (Variable.export_morphism ctxt' ctxt)
  in
    (fn_free, thm, ctxt''', m)
  end

  (* Apply each assumption. *)
  val (res, (ctxt', m)) = fold_map (
    fn (fn_name, is_recursive_call) =>
      fn (ctxt, m) =>
        let
          val (free, thm, ctxt', m') =
              assume_func ctxt fn_name is_recursive_call
        in
          ((fn_name, (is_recursive_call, free, thm)), (ctxt', m' $> m))
        end)
    callees (ctxt, Morphism.identity)
in
  (ctxt', m, res)
end;

(*
fun assume_called_functions_corres ctxt fn_info callees
    get_fn_type get_fn_assumption get_fn_args get_const_name callers_measure_var
*)
assume_called_functions_corres @{context} () [("a", false), ("r", true)]
  (K @{typ "nat \<Rightarrow> nat \<Rightarrow> string \<Rightarrow> string"})
  (fn ctxt => fn name => fn term => fn args => fn is_rec => fn meas =>
    HOLogic.mk_Trueprop (@{term "my_corres :: (string \<Rightarrow> string) \<Rightarrow> bool"} $ betapplys (term, meas :: args)))
  (fn f => if f = "a" then [("arg_a", @{typ nat})] else [("arg_r", @{typ nat})])
  I @{term "rec_measure :: nat"}
\<close>

end
