(*
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory Trace_Schematic_Insts
imports
  Main
begin

text \<open>
  See Trace_Schematic_Insts_Test for tests and examples.
\<close>

text \<open>
  We use this to stash a list of the schematics in the conclusion of
  the proof state. After running a method, we can read off the
  schematic instantiations (if any) from this list, then restore the
  original conclusion. Schematic types are added as "undefined :: ?'a"
  (for now, we don't worry about types that don't have sort "type").

  TODO: there ought to be some standard way of stashing things into
  the proof state. Find out what that is and refactor
\<close>
definition container :: "'a \<Rightarrow> bool \<Rightarrow> bool"
  where
  "container a b \<equiv> True"

lemma proof_state_add:
  "Pure.prop PROP P \<equiv> PROP Pure.prop (container True xs \<Longrightarrow> PROP P)"
  by (simp add: container_def)

lemma proof_state_remove:
  "PROP Pure.prop (container True xs \<Longrightarrow> PROP P) \<equiv> Pure.prop (PROP P)"
  by (simp add: container_def)

lemma rule_add:
  "PROP P \<equiv> (container True xs \<Longrightarrow> PROP P)"
  by (simp add: container_def)

lemma rule_remove:
  "(container True xs \<Longrightarrow> PROP P) \<equiv> PROP P"
  by (simp add: container_def)

lemma elim:
  "container a b"
  by (simp add: container_def)

ML \<open>
signature TRACE_SCHEMATIC_INSTS = sig
  type instantiations = (term * (int * term)) list * (typ * typ) list

  val trace_schematic_insts:
        Method.method -> (instantiations -> unit) -> Method.method
  val default_report:
        Proof.context -> string -> instantiations -> unit

  val trace_schematic_insts_tac:
        Proof.context ->
        (instantiations -> instantiations -> unit) ->
        (thm -> int -> tactic) ->
        thm -> int -> tactic
  val default_rule_report:
        Proof.context -> string -> instantiations -> instantiations -> unit

  val skip_dummy_state: Method.method -> Method.method
  val make_term_container: term list -> term
  val dest_term_container: term -> term list

  val attach_proof_annotations: Proof.context -> term list -> thm -> thm
  val detach_proof_annotations: Proof.context -> thm -> (int * term) list * thm

  val attach_rule_annotations: Proof.context -> term list -> thm -> thm
  val detach_rule_result_annotations: Proof.context -> thm -> (int * term) list * thm
end

structure Trace_Schematic_Insts: TRACE_SCHEMATIC_INSTS = struct

\<comment>\<open>
  Each pair is a (schematic, instantiation) pair.

  The int in the term instantiations is the number of binders which are
  due to subgoal bounds.

  An explanation: if we instantiate some schematic `?P` within
  a subgoal like @{term "\<And>x y. Q"}, it might be instantiated to @{term "\<lambda>a. R a x"}.
  We need to capture `x` when reporting the instantiation, so we report that `?P`
  has been instantiated to @{term "\<lambda>x y a. R a x"}. In order to distinguish between
  the bound `x`, `y`, and `a`, we record that the two outermost binders are
  actually due to the subgoal bounds.
\<close>
type instantiations = (term * (int * term)) list * (typ * typ) list

\<comment>\<open>
  Work around Isabelle running every apply method on a dummy proof state
\<close>
fun skip_dummy_state method =
  fn facts => fn (ctxt, st) =>
    case Thm.prop_of st of
        Const (@{const_name Pure.prop}, _) $
          (Const (@{const_name Pure.term}, _) $ Const (@{const_name Pure.dummy_pattern}, _)) =>
          Seq.succeed (Seq.Result (ctxt, st))
      | _ => method facts (ctxt, st);

\<comment>\<open>
  Utils
\<close>
fun rewrite_state_concl eqn st =
  Conv.fconv_rule (Conv.concl_conv (Thm.nprems_of st) (K eqn)) st

\<comment>\<open>
  Strip the @{term Pure.prop} that wraps proof state conclusions
\<close>
fun strip_prop ct =
      case Thm.term_of ct of
        Const (@{const_name "Pure.prop"}, @{typ "prop \<Rightarrow> prop"}) $ _ => Thm.dest_arg ct
      | _ => raise CTERM ("strip_prop: head is not Pure.prop", [ct])

fun cconcl_of st =
  funpow (Thm.nprems_of st) Thm.dest_arg (Thm.cprop_of st)
  |> strip_prop

fun vars_of_term t =
  Term.add_vars t []
  |> sort_distinct Term_Ord.var_ord

fun type_vars_of_term t =
  Term.add_tvars t []
  |> sort_distinct Term_Ord.tvar_ord

\<comment>\<open>
  Create annotation list
\<close>
fun make_term_container ts =
      fold (fn t => fn container =>
              Const (@{const_name proof_state_term__container},
                    fastype_of t --> @{typ "bool \<Rightarrow> bool"}) $
                t $ container)
        (rev ts) @{term "True"}

\<comment>\<open>
  Retrieve annotation list
\<close>
fun dest_term_container
      (Const (@{const_name proof_state_term__container}, _) $ x $ list) =
          x :: dest_term_container list
  | dest_term_container _ = []

\<comment>\<open>
  Attach some terms to a proof state, by "hiding" them in the protected goal.
\<close>
fun attach_proof_annotations ctxt terms st =
  let
    val container = make_term_container terms
    (* FIXME: this might affect st's maxidx *)
    val add_eqn =
          Thm.instantiate
            ([],
             [((("P", 0), @{typ prop}), cconcl_of st),
              ((("xs", 0), @{typ bool}), Thm.cterm_of ctxt container)])
            @{thm proof_state_add}
  in
    rewrite_state_concl add_eqn st
  end

\<comment>\<open>
  Retrieve attached terms from a proof state
\<close>
fun detach_proof_annotations ctxt st =
  let
    val st_concl = cconcl_of st
    val (ccontainer', real_concl) = Thm.dest_implies st_concl
    val ccontainer =
          ccontainer'
          |> Thm.dest_arg (* strip Trueprop *)
          |> Thm.dest_arg (* strip outer "p_s_t__c True" *)
    val terms =
          ccontainer
          |> Thm.term_of
          |> dest_term_container
    val remove_eqn =
          Thm.instantiate
            ([],
             [((("P", 0), @{typ prop}), real_concl),
              ((("xs", 0), @{typ bool}), ccontainer)])
            @{thm proof_state_term__container_remove}
  in
    (terms, rewrite_state_concl remove_eqn st)
  end

(* ML interface, calls the supplied function with schematic unifications
   (will be given all variables, including those that haven't been instantiated) *)
fun trace_schematic_insts method callback
  = fn facts => fn (ctxt, st) =>
    let val tvars = map TVar (type_vars_of_term (Thm.prop_of st))
        val tvar_carriers = map (fn tvar => Const (@{const_name undefined}, tvar)) tvars
        val vars = map Var (vars_of_term (Thm.prop_of st))
        val annotated_st = attach_proof_annotations ctxt (vars @ tvar_carriers) st
    in (* Run the method *)
      method facts (ctxt, annotated_st)
      |> Seq.map_result (fn (ctxt', annotated_st') => let
            (* Retrieve the stashed list, now with unifications *)
            val (annotations, st') = detach_proof_annotations ctxt' annotated_st'
            val (var_annotations, tvar_annotations) = chop (length vars) annotations
            (* Report the list *)
            (* TODO: provide attached Bounds as well? *)
            val _ = callback (vars ~~ var_annotations) (tvars ~~ map fastype_of tvar_annotations)
         in (ctxt', st') end)
    end

(* Default callback. Prints nontrivial instantiations to tracing output
   with the given title line *)
fun default_report ctxt title var_insts tvar_insts =
  let
    val vars_lines =
        map (fn (var, inst) =>
          if var = inst then "" (* don't show unchanged *) else
              "  " ^ Syntax.string_of_term ctxt var ^ "  =>  " ^
              Syntax.string_of_term ctxt inst ^ "\n")
        var_insts
    val tvars_lines =
        map (fn (tvar, inst) =>
          if tvar = inst then "" (* don't show unchanged *) else
              "  " ^ Syntax.string_of_typ ctxt tvar ^ "  =>  " ^
              Syntax.string_of_typ ctxt inst ^ "\n")
        tvar_insts
    val all_insts = String.concat (vars_lines @ tvars_lines)
  (* TODO: add a quiet flag, to suppress output when nothing was instantiated *)
  in title ^ "\n" ^ (if all_insts = "" then "  (no instantiations)\n" else all_insts)
     |> tracing
  end
end
\<close>

method_setup trace_schematic_insts = \<open>
  let
    open Trace_Schematic_Insts
  in
    (Scan.option (Scan.lift Parse.liberal_name) -- Method.text_closure) >>
    (fn (maybe_title, method_text) => fn ctxt =>
      trace_schematic_insts
          (Method.evaluate method_text ctxt)
          (default_report ctxt
              (Option.getOpt (maybe_title, "trace_schematic_insts:")))
      |> skip_dummy_state
    )
  end
\<close> "Method combinator to trace schematic variable and type instantiations"

end
