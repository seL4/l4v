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
 * Configuring type strengthen rules.
 * Based on type_strengthen.thy.
 *)
theory type_strengthen_tricks imports
  "../../AutoCorres"
begin

install_C_file "type_strengthen.c"

(* We can configure the type strengthen rules individually.
   For example, suppose that we do not want to lift loops to the option monad: *)
declare gets_theE_L2_while [ts_rule option del]

context type_strengthen begin
ML \<open>
FunctionInfo2.init_function_info @{context} "type_strengthen.c"
|> Symtab.dest
|> map (fn (f, info) => (f, Symset.dest (#callees info), Symset.dest (#rec_callees info)))
\<close>

ML \<open>
val result_infos: FunctionInfo2.function_info Symtab.table FunctionInfo2.Phasetab.table Unsynchronized.ref
     = Unsynchronized.ref FunctionInfo2.Phasetab.empty;
\<close>

local_setup \<open>
fn lthy =>
let val filename = "type_strengthen.c";
    val simpl_info = FunctionInfo2.init_function_info lthy filename;
    val prog_info = ProgramInfo.get_prog_info lthy filename;

    val do_opt = true;
    val trace_opt = false;
    val keep_going = false;

    val l1_results =
      SimplConv2.translate filename prog_info simpl_info
        true true false (fn f => "l1_" ^ f ^ "'") lthy;
    val l2_results =
      LocalVarExtract2.translate filename prog_info l1_results
        do_opt trace_opt (fn f => "l2_" ^ f ^ "'");

    val gen_word_heaps = true;
    val heap_abs_syntax = true;
    val (l2_results', HL_setup) =
      HeapLift2.prepare_heap_lift filename prog_info l2_results lthy
        (fn fld => fld ^ "'") gen_word_heaps heap_abs_syntax;

    val no_heap_abs = ["opt_j"];
    val force_heap_abs = [];
(*
    val hl_results = l2_results;
*)
    val hl_results =
      HeapLift2.translate filename prog_info l2_results' HL_setup
        (Symset.make no_heap_abs) (Symset.make force_heap_abs)
        heap_abs_syntax keep_going
        [] do_opt trace_opt (fn f => "hl_" ^ f ^ "'");

    val unsigned_abs = ["opt_a"];
    val no_signed_abs = [];
(*
    val wa_results = hl_results;
*)
    val wa_results =
      WordAbstract2.translate filename prog_info hl_results
        (Symset.make unsigned_abs) (Symset.make no_signed_abs) []
        do_opt trace_opt (fn f => "wa_" ^ f ^ "'");

    val ts_rules = Monad_Types.get_ordered_rules [] (Context.Proof lthy);
    val ts_results =
      TypeStrengthen2.translate ts_rules Symtab.empty filename prog_info
        wa_results (fn f => f ^ "'") keep_going do_opt;

    val l1_results' = FSeq.list_of l1_results |> map snd |> TypeStrengthen2.symtab_merge false;
    val l2_results' = FSeq.list_of l2_results |> map snd |> TypeStrengthen2.symtab_merge false;
    val hl_results' = FSeq.list_of hl_results |> map snd |> TypeStrengthen2.symtab_merge false;
    val wa_results' = FSeq.list_of wa_results |> map snd |> TypeStrengthen2.symtab_merge false;
    val ts_results' = FSeq.list_of ts_results |> map snd |> TypeStrengthen2.symtab_merge false;
    val _ = result_infos := FunctionInfo2.Phasetab.make
              [(FunctionInfo2.CP, simpl_info),
               (FunctionInfo2.L1, l1_results'),
               (FunctionInfo2.L2, l2_results'),
               (FunctionInfo2.HL, hl_results'),
               (FunctionInfo2.WA, wa_results'),
               (FunctionInfo2.TS, ts_results')];
in FSeq.list_of ts_results |> List.last |> fst end
\<close>

thm opt_a'.simps opt_a2'_def
(* heap_abs_syntax test *)
thm st_i'.simps
thm exc_f'_def

(* gen_word_heaps test *)
term is_valid_w64

ML \<open>
FunctionInfo2.Phasetab.dest (!result_infos)
|> app (fn (phase, infos) =>
     (tracing ("Info for " ^ FunctionInfo2.string_of_phase phase);
      Symtab.dest infos |> app (fn (_, x) => @{trace} x)))
\<close>

end

(* We can also specify which monads are used for type strengthening.
   Here, we exclude the read-only monad completely, and specify
   rules for some individual functions. *)
autocorres [
  ts_rules = pure option nondet,
  ts_force option = pure_f,
  skip_heap_abs
  ] "type_strengthen.c"

context type_strengthen begin

(* pure_f (and indirectly, pure_f2) are now lifted to the option monad. *)
thm pure_f'_def pure_f2'_def
thm pure_g'_def pure_h'_def
    pure_i'_def pure_j'_def pure_k'_def pure_div_roundup'_def
(* gets_f and gets_g are now lifted to the option monad. *)
thm gets_f'_def gets_g'_def
thm opt_f'_def opt_g'_def opt_h'.simps opt_i'_def
    opt_j'_def opt_a'.simps
(* opt_l is now lifted to the state monad. *)
thm opt_l'_def
thm st_f'_def st_g'_def st_h'_def st_i'.simps (* hax'_def *)
thm exc_f'_def
end

end