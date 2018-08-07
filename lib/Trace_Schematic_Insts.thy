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
  the proof goal. Find out what that is and refactor
\<close>
definition trace_schematic_insts__container :: "'a \<Rightarrow> bool \<Rightarrow> bool"
  where
  "trace_schematic_insts__container a b \<equiv> True"

lemma trace_schematic_insts__container_add:
  "Pure.prop PROP P \<equiv> PROP Pure.prop (trace_schematic_insts__container True xs \<Longrightarrow> PROP P)"
  by (simp add: trace_schematic_insts__container_def)

lemma trace_schematic_insts__container_remove:
  "PROP Pure.prop (trace_schematic_insts__container True xs \<Longrightarrow> PROP P) \<equiv> Pure.prop (PROP P)"
  by (simp add: trace_schematic_insts__container_def)

ML \<open>
structure Trace_Schematic_Insts = struct

(* Work around Isabelle running every apply method on a dummy proof state *)
fun skip_dummy_state (method: Method.method) : Method.method =
  fn facts => fn (ctxt, st) =>
    case Thm.prop_of st of
        Const ("Pure.prop", _) $ (Const ("Pure.term", _) $ Const ("Pure.dummy_pattern", _)) =>
          Seq.succeed (Seq.Result (ctxt, st))
      | _ => method facts (ctxt, st);

(* Utils *)
fun rewrite_state_concl (eqn: thm) (st: thm) : thm =
  Conv.fconv_rule (Conv.concl_conv (Thm.nprems_of st) (K eqn)) st

(* Strip the @{term Prop.prop} that wraps proof state conclusions *)
fun strip_prop (ct: cterm): cterm = case Thm.term_of ct of
        Const ("Pure.prop", @{typ "prop \<Rightarrow> prop"}) $ _ => Thm.dest_arg ct
      | _ => raise CTERM ("strip_prop: head is not Pure.prop", [ct])

fun cconcl_of (st: thm): cterm =
  funpow (Thm.nprems_of st) Thm.dest_arg (Thm.cprop_of st)
  |> strip_prop

fun vars_of_term (t: term): (indexname * typ) list =
  Term.add_vars t []
  |> sort_distinct Term_Ord.var_ord

fun type_vars_of_term (t: term): (indexname * sort) list =
  Term.add_tvars t []
  |> sort_distinct Term_Ord.tvar_ord

(* Create annotation list *)
fun make_schematics_container ts =
      fold (fn t => fn container =>
              Const (@{const_name trace_schematic_insts__container},
                    fastype_of t --> @{typ "bool \<Rightarrow> bool"}) $
                t $ container)
        (rev ts) @{term "True"}

(* Retrieve annotation list *)
fun dest_schematics_container
      (Const (@{const_name trace_schematic_insts__container}, _) $ @{term True} $ list) =
      let fun dest (Const (@{const_name trace_schematic_insts__container}, _) $ x $ list) =
                x :: dest list
            | dest _ = []
      in dest list end
  | dest_schematics_container t =
      raise TERM ("Trace_Schematic_Insts internal error: not a schematic container", [t])

(* ML interface, calls the supplied function with schematic unifications
   (will be given all variables, including those that haven't been instantiated) *)
fun trace_schematic_insts
      (method: Method.method)
      (callback: (term * term) list -> (typ * typ) list -> unit)
  : Method.method
  = fn facts => fn (ctxt, st) =>
    let val tvars = map TVar (type_vars_of_term (Thm.prop_of st))
        val tvar_carriers = map (fn tvar => Const (@{const_name undefined}, tvar)) tvars
        val vars = map Var (vars_of_term (Thm.prop_of st))
        val container = make_schematics_container (vars @ tvar_carriers)

        (* FIXME: this might affect st's maxidx *)
        val add_schematics_eqn = Thm.instantiate
              ([],
               [((("P", 0), @{typ prop}), cconcl_of st),
                ((("xs", 0), @{typ bool}), Thm.cterm_of ctxt container)])
              @{thm trace_schematic_insts__container_add}
        (* Now stash it into st *)
        val annotated_st = rewrite_state_concl add_schematics_eqn st
    in (* Run the method *)
       method facts (ctxt, annotated_st)
       |> Seq.map_result (fn (ctxt', annotated_st') => let
            val st'_concl = cconcl_of annotated_st'
            (* Retrieve the stashed list, now with unifications *)
            val st'_annotations =
                  st'_concl
                  |> Thm.dest_implies |> fst
                  |> Thm.dest_arg (* strip Trueprop *)
            val container' = Thm.term_of st'_annotations |> dest_schematics_container
            val (var_annotations, tvar_annotations) = chop (length vars) container'
            (* Report the list *)
            (* TODO: provide attached Bounds as well? *)
            val _ = callback (vars ~~ var_annotations) (tvars ~~ map fastype_of tvar_annotations)

            (* Restore original conclusion of st *)
            val st'_real_concl =
                  st'_concl
                  |> Thm.dest_implies |> snd
            val dest_schematics_eqn = Thm.instantiate
                  ([],
                   [((("P", 0), @{typ prop}), st'_real_concl),
                    ((("xs", 0), @{typ bool}),
                     Thm.dest_arg st'_annotations (* strip outer "t_s_i__c True" *))])
                  @{thm trace_schematic_insts__container_remove}
            val st' = rewrite_state_concl dest_schematics_eqn annotated_st'
       in (ctxt', st') end)
    end
end
\<close>

method_setup trace_schematic_insts = \<open>
  let
    fun show_insts ctxt title var_insts tvar_insts = let
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
  in
    (Scan.option (Scan.lift Parse.liberal_name) -- Method.text_closure) >>
    (fn (maybe_title, method_text) => fn ctxt =>
      Trace_Schematic_Insts.trace_schematic_insts
          (Method.evaluate method_text ctxt)
          (show_insts ctxt (Option.getOpt (maybe_title, "trace_schematic_insts:")))
      |> Trace_Schematic_Insts.skip_dummy_state
    )
  end
\<close> "Method combinator to trace schematic variable and type instantiations"

end