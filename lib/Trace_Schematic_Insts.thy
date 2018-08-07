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
  "Word_Lib/Word_Lib"
begin

text \<open>
  Combinator to trace schematic variables that are unified by a given method.
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
  "Pure.prop PROP P \<equiv> PROP Pure.prop (trace_schematic_insts__container a b \<Longrightarrow> PROP P)"
  by (simp add: trace_schematic_insts__container_def)

lemma trace_schematic_insts__container_remove:
  "PROP Pure.prop (trace_schematic_insts__container a b \<Longrightarrow> PROP P) \<equiv> Pure.prop (PROP P)"
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

fun cconcl_of (st: thm) : cterm =
  funpow (Thm.nprems_of st) Thm.dest_arg (Thm.cprop_of st)

fun fst_ord ord ((a, _), (b, _)) = ord (a, b)

(* Get schematic vars in term *)
fun vars_of_term (t: term): (indexname * typ) list = let
  fun descend (f $ x) = descend f @ descend x
    | descend (Var v) = [v]
    | descend (Abs (_, _, t)) = descend t
    | descend _ = []
  in descend t |> sort_distinct (fst_ord (prod_ord string_ord int_ord)) end

fun type_vars_of_term (t: term): (indexname * sort) list = let
  fun descend_t (Type (_, tys)) = List.concat (map descend_t tys)
    | descend_t (TFree _) = []
    | descend_t (TVar tv) = [tv]
  fun descend (Const (_, ty)) = descend_t ty
    | descend (Var (_, ty)) = descend_t ty
    | descend (Free (_, ty)) = descend_t ty
    | descend (f $ x) = descend f @ descend x
    | descend (Abs (_, ty, t)) = descend_t ty @ descend t
    | descend _ = []
  in descend t |> sort_distinct (fst_ord (prod_ord string_ord int_ord)) end

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
        val tvar_list = fold (fn tvar => fn t =>
                Const (@{const_name trace_schematic_insts__container},
                       tvar --> @{typ "bool \<Rightarrow> bool"}) $
                  Const (@{const_name undefined}, tvar) $ t)
                (rev tvars) @{term "True"}

        val vars = map Var (vars_of_term (Thm.prop_of st))
        val var_list = fold (fn var => fn t =>
                Const (@{const_name trace_schematic_insts__container},
                       fastype_of var --> @{typ "bool \<Rightarrow> bool"}) $ var $ t)
                (rev vars) tvar_list

        (* FIXME: infer_instantiate' may be slow/unsafe? *)
        val add_schematics_eqn = Drule.infer_instantiate' ctxt
              (map SOME [cconcl_of st |> Thm.dest_arg, @{cterm "True"},
                         Thm.cterm_of ctxt var_list])
              @{thm trace_schematic_insts__container_add}
        val annotated_st = rewrite_state_concl add_schematics_eqn st
    in method facts (ctxt, annotated_st)
       |> Seq.map_result (fn (ctxt', annotated_st') => let
            val st'_concl = cconcl_of annotated_st' |> Thm.dest_arg
            (* get annotations *)
            val st'_annotations = st'_concl |> Thm.dest_arg1 |> Thm.dest_arg
            val annotations = Thm.term_of st'_annotations |> dest_schematics_container
            (* TODO: provide attached Bounds as well? *)
            val (var_annotations, tvar_annotations) = chop (length vars) annotations
            val _ = callback (vars ~~ var_annotations) (tvars ~~ map fastype_of tvar_annotations)

            (* restore original concl *)
            val st'_real_concl = st'_concl |> Thm.dest_arg
            val dest_schematics_eqn = Drule.infer_instantiate' ctxt'
                  (map SOME [@{cterm "True"}, Thm.dest_arg st'_annotations, st'_real_concl])
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
        (* TODO: add a quiet flag for when nothing was instantiated *)
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


section \<open>Examples\<close>
experiment begin

text \<open>Schematic variables\<close>
lemma "\<lbrakk> \<forall>x. P x \<rbrakk> \<Longrightarrow> P x"
  apply (drule spec)
  apply (trace_schematic_insts \<open>assumption\<close>)
  done

definition foo :: "'a \<Rightarrow> bool"
  where "foo x = True"

lemma fooI1:
  "foo 0 \<Longrightarrow> foo x"
  by (simp add: foo_def)

lemma fooI2:
  "foo x \<Longrightarrow> foo 0"
  by (simp add: foo_def)

lemma fooI2':
  "foo x \<Longrightarrow> foo (0 :: nat)"
  by (erule fooI2)

text \<open>Schematic type variables\<close>
lemma "foo x \<Longrightarrow> foo y"
  apply (rule fooI1)
  apply (trace_schematic_insts \<open>erule fooI2'\<close>)
  done

text \<open>When backtracking, every recursive invocation is traced\<close>
lemma "\<lbrakk> \<forall>x. Q x \<longrightarrow> R x; \<forall>x. P x \<longrightarrow> Q x; P x; P y \<longrightarrow> R x \<rbrakk> \<Longrightarrow> R x"
  apply (drule spec)
  apply (drule spec)
  apply (trace_schematic_insts impE1 \<open>erule impE\<close>,
         trace_schematic_insts impE2 \<open>erule impE\<close>,
         (trace_schematic_insts "try assumption" \<open>assumption\<close>)+; fail)
  done

end

(* TODO: proper test suite *)

end