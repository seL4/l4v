(*  Title:      hoare.ML
    Author:     Norbert Schirmer, TU Muenchen

Copyright (C) 2004-2007 Norbert Schirmer

This library is free software; you can redistribute it and/or modify
it under the terms of the GNU Lesser General Public License as
published by the Free Software Foundation; either version 2.1 of the
License, or (at your option) any later version.

This library is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307
USA
*)

signature HOARE =
sig
  datatype hoareMode = Partial | Total
  val gen_proc_rec: Proof.context -> hoareMode -> int -> thm
  datatype state_kind = Record | Function
  datatype par_kind = In | Out
  val deco: string
  val proc_deco: string
  val par_deco: string -> string
  val chopsfx: string -> string -> string
  val is_state_var: string -> bool
  val extern: Proof.context -> string -> string
  val remdeco: Proof.context -> string -> string
  val remdeco': string -> string
  val undeco: Proof.context -> term -> term
  val varname: string -> string
  val resuffix: string -> string -> string -> string
  type proc_info =
    {params: ((par_kind * string) list),
     recursive: bool,
     state_kind: state_kind}
  type hoare_tac = (bool -> int -> tactic) -> Proof.context -> hoareMode -> int -> tactic
  type hoare_data =
   {proc_info: proc_info Symtab.table,
    active_procs: string list list,
    default_state_kind: state_kind,
    generate_guard: (stamp * (Proof.context -> term -> term option)),
    wp_tacs: (string * hoare_tac) list,
    hoare_tacs: (string * hoare_tac) list,
    vcg_simps: thm list}
  val get_data: Proof.context -> hoare_data
  val get_params: string -> Proof.context -> (par_kind * string) list option
  val get_default_state_kind: Proof.context -> state_kind
  val get_state_kind: string -> Proof.context -> state_kind option
  val clique_name: string list -> string
  val install_generate_guard: (Proof.context -> term -> term option) ->
    Context.generic -> Context.generic
  val generate_guard: Proof.context -> term -> term option
  val BasicSimpTac: Proof.context -> state_kind ->
    bool -> thm list -> (int -> tactic) -> int -> tactic
  val hoare: (Proof.context -> Proof.method) context_parser
  val hoare_raw: (Proof.context -> Proof.method) context_parser
  val vcg: (Proof.context -> Proof.method) context_parser
  val vcg_step: (Proof.context -> Proof.method) context_parser
  val hoare_rule: (Proof.context -> Proof.method) context_parser
  
  val add_foldcongsimps: thm list -> theory -> theory
  val get_foldcong_ss : theory -> simpset
  val add_foldcongs : thm list -> theory -> theory
  val modeqN : string
  val modexN : string
  val implementationN : string
  val specL : string

  val vcg_tac : string -> string -> string list -> Proof.context -> int -> tactic
  val hoare_rule_tac : Proof.context -> thm list -> int -> tactic

  datatype 'a bodykind = BodyTyp of 'a | BodyTerm of 'a
  val proc_specs : (bstring * string) list parser
  val add_params : morphism -> string -> (par_kind * string) list ->
                   Context.generic -> Context.generic
  val set_default_state_kind : state_kind -> Context.generic -> Context.generic
  val add_state_kind : morphism -> string -> state_kind -> Context.generic ->
                       Context.generic
  val add_recursive : morphism -> string -> Context.generic -> Context.generic
end;

structure Hoare: HOARE =
struct

(* Misc *)

val record_vanish = Attrib.setup_config_bool @{binding hoare_record_vanish} (K true);
val use_generalise = Attrib.setup_config_bool @{binding hoare_use_generalise} (K false);
val sort_variables = Attrib.setup_config_bool @{binding hoare_sort_variables} (K true);
val use_cond_inv_modifies = Attrib.setup_config_bool @{binding hoare_use_cond_inv_modifies} (K true);

val hoare_trace = Attrib.setup_config_bool @{binding hoare_trace} (K false);

val body_def_sfx = "_body";

val programN = "\<Gamma>";
val hoare_ctxtL = "hoare";
val specL = "_spec";
val procL = "_proc";

val bodyP = "_impl";

val modifysfx = "_modifies";
val modexN = "Hoare.mex";
val modeqN = "Hoare.meq";

val KNF = @{const_name StateFun.K_statefun};


(* Some abstract syntax operations *)

val Trueprop = HOLogic.mk_Trueprop;

infix 0 ===;
val (op ===) = Trueprop o HOLogic.mk_eq;

fun is_empty_set (Const (@{const_name Orderings.bot}, _)) = true
  | is_empty_set _ = false;

fun mk_Int Ts A B = let val T = fastype_of1 (Ts, A)
  in Const (@{const_name Lattices.inf}, T --> T --> T) $ A $ B end;

fun mk_Un T (A, B) = Const (@{const_name Lattices.sup}, T --> T --> T) $ A $ B;

fun dest_Un (Const (@{const_name Lattices.sup}, _) $ t1 $ t2) = dest_Un t1 @ dest_Un t2
  | dest_Un t = [t]

fun mk_UN' dT rT t = 
  let
    val dTs = HOLogic.mk_setT dT;
  in
    Const (@{const_name Complete_Lattices.SUPREMUM},
      dTs --> (dT --> rT) --> rT) $
      Const (@{const_name Orderings.top}, dTs) $ t
  end;

fun mk_UN ((x, T), P) = mk_UN' T (fastype_of P) (absfree (x, T) P);

fun dest_UN (Const (@{const_name Complete_Lattices.SUPREMUM}, _) $ Const (@{const_name Orderings.top}, _) $ Abs (x, T, t)) =
      let val (vars, body) = dest_UN t
      in ((x, T) :: vars, body) end
  | dest_UN t = ([], t);

fun tap_UN (Const (@{const_name Complete_Lattices.SUPREMUM}, _) $ Const (@{const_name Orderings.top}, _) $ t) = SOME t
  | tap_UN _ = NONE;


(* Fetching the rules *)

datatype hoareMode = Partial | Total

fun get_rule p t Partial = p
  | get_rule p t Total   = t

val Guard = get_rule @{thm HoarePartial.Guard} @{thm HoareTotal.Guard};

val GuardStrip = get_rule @{thm HoarePartial.GuardStrip} @{thm HoareTotal.GuardStrip};

val GuaranteeAsGuard = get_rule @{thm HoarePartial.GuaranteeAsGuard} @{thm HoareTotal.GuaranteeAsGuard};

val Guarantee = get_rule @{thm HoarePartial.Guarantee} @{thm HoareTotal.Guarantee};

val GuaranteeStrip = get_rule @{thm HoarePartial.GuaranteeStrip} @{thm HoareTotal.GuaranteeStrip};

val GuardsNil = get_rule @{thm HoarePartial.GuardsNil} @{thm HoareTotal.GuardsNil};

val GuardsCons = get_rule @{thm HoarePartial.GuardsCons} @{thm HoareTotal.GuardsCons};

val GuardsConsGuaranteeStrip =
      get_rule @{thm HoarePartial.GuardsConsGuaranteeStrip} @{thm HoareTotal.GuardsConsGuaranteeStrip};

val Skip = get_rule @{thm HoarePartial.Skip} @{thm HoareTotal.Skip};

val Basic = get_rule @{thm HoarePartial.Basic} @{thm HoareTotal.Basic};

val BasicCond = get_rule @{thm HoarePartial.BasicCond} @{thm HoareTotal.BasicCond};

val Spec = get_rule @{thm HoarePartial.Spec} @{thm HoareTotal.Spec};

val SpecIf = get_rule @{thm HoarePartial.SpecIf} @{thm HoareTotal.SpecIf};

val Throw = get_rule @{thm HoarePartial.Throw} @{thm HoareTotal.Throw};

val Raise = get_rule @{thm HoarePartial.raise} @{thm HoareTotal.raise};

val Catch = get_rule @{thm HoarePartial.Catch} @{thm HoareTotal.Catch};

val CondCatch = get_rule @{thm HoarePartial.condCatch} @{thm HoareTotal.condCatch};

val CatchSwap = get_rule @{thm HoarePartial.CatchSwap} @{thm HoareTotal.CatchSwap};

val CondCatchSwap = get_rule @{thm HoarePartial.condCatchSwap} @{thm HoareTotal.condCatchSwap};

val Seq = get_rule @{thm HoarePartial.Seq} @{thm HoareTotal.Seq};

val SeqSwap = get_rule @{thm HoarePartial.SeqSwap} @{thm HoareTotal.SeqSwap};

val BSeq = get_rule @{thm HoarePartial.BSeq} @{thm HoareTotal.BSeq};

val Cond = get_rule @{thm HoarePartial.Cond} @{thm HoareTotal.Cond};

val CondInv'Partial = @{thm HoarePartial.CondInv'};
val CondInv'Total = @{thm HoareTotal.CondInv'};
val CondInv' = get_rule CondInv'Partial CondInv'Total;

val SwitchNil = get_rule @{thm HoarePartial.switchNil} @{thm HoareTotal.switchNil};

val SwitchCons = get_rule @{thm HoarePartial.switchCons} @{thm HoareTotal.switchCons};

val CondSwap = get_rule @{thm HoarePartial.CondSwap} @{thm HoareTotal.CondSwap};

val While = get_rule @{thm HoarePartial.While} @{thm HoareTotal.While};

val WhileAnnoG = get_rule @{thm HoarePartial.WhileAnnoG} @{thm HoareTotal.WhileAnnoG};

val WhileAnnoFix = get_rule @{thm HoarePartial.WhileAnnoFix'} @{thm HoareTotal.WhileAnnoFix'};

val WhileAnnoGFix = get_rule @{thm HoarePartial.WhileAnnoGFix} @{thm HoareTotal.WhileAnnoGFix};

val BindR = get_rule @{thm HoarePartial.Bind} @{thm HoareTotal.Bind};

val Block = get_rule @{thm HoarePartial.Block} @{thm HoareTotal.Block};

val BlockSwap = get_rule @{thm HoarePartial.BlockSwap} @{thm HoareTotal.BlockSwap};

val Proc = get_rule @{thm HoarePartial.ProcSpec} @{thm HoareTotal.ProcSpec};

val ProcNoAbr = get_rule @{thm HoarePartial.ProcSpecNoAbrupt} @{thm HoareTotal.ProcSpecNoAbrupt};

val ProcBody = get_rule @{thm HoarePartial.ProcBody} @{thm HoareTotal.ProcBody};

val CallBody = get_rule @{thm HoarePartial.CallBody} @{thm HoareTotal.CallBody};

val FCall = get_rule @{thm HoarePartial.FCall} @{thm HoareTotal.FCall};

val ProcRecSpecs = get_rule @{thm HoarePartial.ProcRecSpecs} @{thm HoareTotal.ProcRecSpecs};

val ProcModifyReturnSameFaults =
      get_rule @{thm HoarePartial.ProcModifyReturnSameFaults} @{thm HoareTotal.ProcModifyReturnSameFaults};

val ProcModifyReturn = get_rule @{thm HoarePartial.ProcModifyReturn} @{thm HoareTotal.ProcModifyReturn};

val ProcModifyReturnNoAbr = get_rule @{thm HoarePartial.ProcModifyReturnNoAbr} @{thm HoareTotal.ProcModifyReturnNoAbr};

val ProcModifyReturnNoAbrSameFaultsPartial =
      @{thm HoarePartial.ProcModifyReturnNoAbrSameFaults};
val ProcModifyReturnNoAbrSameFaultsTotal =
      @{thm HoareTotal.ProcModifyReturnNoAbrSameFaults};
val ProcModifyReturnNoAbrSameFaults =
      get_rule ProcModifyReturnNoAbrSameFaultsPartial ProcModifyReturnNoAbrSameFaultsTotal;

val TrivPost = get_rule @{thm HoarePartial.TrivPost} @{thm HoareTotal.TrivPost};

val TrivPostNoAbr = get_rule @{thm HoarePartial.TrivPostNoAbr} @{thm HoareTotal.TrivPostNoAbr};

val DynProcProcPar = get_rule @{thm HoarePartial.DynProcProcPar} @{thm HoareTotal.DynProcProcPar};

val DynProcProcParNoAbr = get_rule @{thm HoarePartial.DynProcProcParNoAbrupt} @{thm HoareTotal.DynProcProcParNoAbrupt};

val ProcProcParModifyReturn = get_rule @{thm HoarePartial.ProcProcParModifyReturn} @{thm HoareTotal.ProcProcParModifyReturn};

val ProcProcParModifyReturnSameFaultsPartial =
      @{thm HoarePartial.ProcProcParModifyReturnSameFaults};
val ProcProcParModifyReturnSameFaultsTotal =
      @{thm HoareTotal.ProcProcParModifyReturnSameFaults};
val ProcProcParModifyReturnSameFaults =
      get_rule ProcProcParModifyReturnSameFaultsPartial
               ProcProcParModifyReturnSameFaultsTotal;

val ProcProcParModifyReturnNoAbr =
      get_rule @{thm HoarePartial.ProcProcParModifyReturnNoAbr} @{thm HoareTotal.ProcProcParModifyReturnNoAbr};

val ProcProcParModifyReturnNoAbrSameFaultsPartial =
      @{thm HoarePartial.ProcProcParModifyReturnNoAbrSameFaults};
val ProcProcParModifyReturnNoAbrSameFaultsTotal   =
      @{thm HoareTotal.ProcProcParModifyReturnNoAbrSameFaults};
val ProcProcParModifyReturnNoAbrSameFaults =
      get_rule ProcProcParModifyReturnNoAbrSameFaultsPartial
               ProcProcParModifyReturnNoAbrSameFaultsTotal;

val DynCom = get_rule @{thm HoarePartial.DynComConseq} @{thm HoareTotal.DynComConseq};

val AugmentContext = get_rule @{thm HoarePartial.augment_context'} @{thm HoareTotal.augment_context'};

val AugmentEmptyFaults = get_rule @{thm HoarePartial.augment_emptyFaults} @{thm HoareTotal.augment_emptyFaults};

val AsmUN = get_rule @{thm HoarePartial.AsmUN} @{thm HoareTotal.AsmUN};

val SpecAnno = get_rule @{thm HoarePartial.SpecAnno'} @{thm HoareTotal.SpecAnno'};

val SpecAnnoNoAbrupt = get_rule @{thm HoarePartial.SpecAnnoNoAbrupt} @{thm HoareTotal.SpecAnnoNoAbrupt};

val LemAnno = get_rule @{thm HoarePartial.LemAnno} @{thm HoareTotal.LemAnno};

val LemAnnoNoAbrupt = get_rule @{thm HoarePartial.LemAnnoNoAbrupt} @{thm HoareTotal.LemAnnoNoAbrupt};



val singleton_conv_sym = @{thm Set.singleton_conv2} RS sym;

val anno_defs = [@{thm Language.whileAnno_def},@{thm Language.whileAnnoG_def},@{thm Language.specAnno_def},
                 @{thm Language.whileAnnoGFix_def},@{thm Language.whileAnnoFix_def},@{thm Language.lem_def}];
val strip_simps =
  @{thm Language.strip_simp} :: @{thm Option.option.map(2)} :: @{thms Language.strip_guards_simps};
val normalize_simps =
 [@{thm Language.while_def}, @{thm Language.bseq_def}, @{thm List.append_Nil}, @{thm List.append_Cons}] @
  @{thms List.list.cases} @
  @{thms Language.flatten_simps} @
  @{thms Language.sequence.simps} @
  @{thms Language.normalize_simps} @
  @{thms Language.guards.simps} @
  [@{thm fst_conv}, @{thm snd_conv}];
val K_rec_convs = [];
val K_fun_convs = [@{thm StateFun.K_statefun_apply}, @{thm StateFun.K_statefun_comp}];
val K_convs = K_rec_convs @ K_fun_convs;
val K_rec_congs = [];
val K_fun_congs = [@{thm StateFun.K_statefun_cong}];
val K_congs = K_rec_congs @ K_fun_congs;

(* misc. aux. functions *)

(* first_subterm
 * yields result x of P for first subterm for which P is (SOME x),
   and all bound variables on the path
 * to that term
 *)
fun first_subterm_dest P =
  let fun first abs_vars t =
        (case P t of
           SOME x => SOME (abs_vars,x)
         |_=> (case t of
                u $ v => (case first abs_vars u of
                            NONE => first abs_vars v
                          | SOME x => SOME x)
              | Abs (c,T,u) => first (abs_vars @ [(c,T)]) u
              | _ => NONE))
  in first [] end;


(* first_subterm
 * yields first subterm for which P holds, and all bound variables on the path
 * to that term
 *)
fun first_subterm P =
  let fun P' t = if P t then SOME t else NONE;
  in first_subterm_dest P' end;

(* max_subterm_dest
 * yields results of P for all maximal subterms for which P is (SOME x),
 * and all bound variables on the path to that subterm
 *)
fun max_subterms_dest P =
  let fun collect abs_vars t =
        (case P t of
           SOME x => [(abs_vars,x)]
         |_=> (case t of
                u $ v => collect abs_vars u @ collect abs_vars v
              | Abs (c,T,u) => collect (abs_vars @ [(c,T)]) u
              | _ => []))
  in collect [] end;

fun last [] = raise Empty
  | last [x] = x
  | last (_::xs) = last xs;

fun dest_splits (Const (@{const_name case_prod},_)$Abs (n,T,t)) = (n,T)::dest_splits t
  | dest_splits (Const (@{const_name case_prod},_)$Abs (n,T,t)$_) = (n,T)::dest_splits t
  | dest_splits (Abs (n,T,_)) = [(n,T)]
  | dest_splits _ = [];

fun idx eq [] x = ~1
  | idx eq (x::rs) y =
      if eq x y then 0
      else let val i = idx eq rs y in if i < 0 then i else i+1 end;

fun resuffix sfx1 sfx2 s =
  suffix sfx2 (unsuffix sfx1 s)
  handle Fail _ => s;

(* state space representation dependent functions *)

datatype state_kind = Record | Function
fun state_simprocs Record   = [Record.simproc]
  | state_simprocs Function = [Record.simproc, StateFun.lookup_simproc];

fun state_upd_simproc Record   = Record.upd_simproc
  | state_upd_simproc Function = StateFun.update_simproc;

fun state_ex_sel_eq_simproc Record   = Record.ex_sel_eq_simproc
  | state_ex_sel_eq_simproc Function = StateFun.ex_lookup_eq_simproc;

val state_split_simp_tac = Record.split_simp_tac
val state_hierarchy = Record.dest_recTs


fun stateT_id T = case (state_hierarchy T) of [] => NONE | Ts => SOME (last Ts);

fun globalsT (Type (_, T :: _)) = SOME T
  | globalsT _ = NONE;

fun stateT_ids T =
  (case stateT_id T of
     NONE => NONE
   | SOME sT => (case globalsT T of
                   NONE => SOME [sT]
                 | SOME gT => (case stateT_id gT of
                                 NONE => SOME [sT]
                                | SOME gT' => SOME [sT,gT'])));

datatype par_kind = In | Out


(*** utilities ***)

(* utils for variable name decorations *)


val deco = "_'";
val proc_deco = "_'proc";

fun par_deco name = deco ^ name ^ deco;

fun chopsfx sfx str =
    (case try (unsuffix sfx) str of
       SOME s => s
     | NONE   => str)

val is_state_var = can (unsuffix deco);

(* removes the suffix of the string beginning with deco.
 *  "xys_'a" --> "xys";
 * The a is also chopped, since sometimes the bound variables
 * are renamed, I think SELECT_GOAL in rename_goal is to blame
 *)
fun remdeco' str =
    let
        fun chop (p::ps) (x::xs) = chop ps xs
          | chop []      xs      = []
          | chop (p::ps) []      = error "remdeco: code should never be reached";

        fun remove prf (s as (x::xs)) = if is_prefix (op =) prf s then chop prf s
                                        else (x::remove prf xs)
          | remove prf [] = [];

    in String.implode (remove (String.explode deco) (String.explode str)) end;

fun extern ctxt s =
  (case try (Proof_Context.extern_const ctxt o Lexicon.unmark_const) s of
     NONE => s
   | SOME s' => s');

fun remdeco ctxt s = remdeco' (extern ctxt s);

fun undeco ctxt (Const (c, T)) = Const (remdeco ctxt c, T)
  | undeco ctxt ((f as Const (@{syntax_const "_free"},_)) $ Free (x, T)) =
      (*f$*)Const (remdeco' x, T)
  | undeco ctxt (Const _ $ _ $ ((Const (@{syntax_const "_free"},_)) $ Free (x, T))) =
      (*f$*)Const (remdeco' x, T)
  | undeco ctxt (Free (c, T)) = Const (remdeco' c, T)
  | undeco ctxt x = x

fun varname x = x ^ deco

val dest_string = map (chr o HOLogic.dest_char) o HOLogic.dest_list;

fun dest_string' t =
     (case try dest_string t of
       SOME s => implode s
      | NONE => (case t of
                   Free (s,_) => s
                 | Const (s,_) => Long_Name.base_name s
                 | _ => raise TERM ("dest_string'",[t])))


fun is_state_space_var Tids t =
    let
      fun is_stateT T = (case stateT_id T of NONE => 0
                         | SOME id => if member (op =) Tids id then ~1 else 0);
    in
      (case t of
         Const _ $ Abs (_,T,_) => is_stateT T
       | Free (_,T) => is_stateT T
       | _ => 0)
    end;


datatype callMode = Static | Parameter

fun proc_name Static (Const (p,_)$_) = resuffix deco proc_deco (Long_Name.base_name p)
  | proc_name Static (Const (@{const_name StateFun.lookup},_)$_$Free (p,_)$_) =
       suffix proc_deco (remdeco' (Long_Name.base_name p))
  | proc_name Static p = dest_string' p
  | proc_name Parameter (Const (p,_)) = resuffix deco proc_deco (Long_Name.base_name p)
  | proc_name Parameter (Abs (_,_,Const (p,_)$Bound 0)) =
      resuffix deco proc_deco (Long_Name.base_name p)
  | proc_name Parameter (Abs (_,_,Const (@{const_name StateFun.lookup},_)$_$Free (p,_)$_)) =
      suffix proc_deco (remdeco' (Long_Name.base_name p))
  | proc_name _ t = raise TERM ("proc_name",[t]);



fun dest_call (Const (@{const_name Language.call},_)$init$pname$return$c) =
           (init,pname,return,c,Static,true)
  | dest_call (Const (@{const_name Language.fcall},_)$init$pname$return$_$c) =
           (init,pname,return,c,Static,true)
  | dest_call (Const (@{const_name Language.com.Call},_)$pname) =
           (Bound 0,pname,Bound 0,Bound 0,Static,false)
  | dest_call (Const (@{const_name Language.dynCall},_)$init$pname$return$c) =
           (init,pname,return,c,Parameter,true)
  | dest_call t = raise TERM ("Hoare.dest_call: unexpected term",[t]);

fun dest_whileAnno (Const (@{const_name Language.whileAnnoG},_) $gs$b$I$V$c) =
        (SOME gs,b,I,V,c,false)
  | dest_whileAnno (Const (@{const_name Language.whileAnno},_) $b$I$V$c) = (NONE,b,I,V,c,false)
  | dest_whileAnno (Const (@{const_name Language.whileAnnoGFix},_)$gs$b$I$V$c) =
        (SOME gs,b,I,V,c,true)
  | dest_whileAnno (Const (@{const_name Language.whileAnnoFix},_) $b$I$V$c) = (NONE,b,I,V,c,true)
  | dest_whileAnno t = raise TERM ("Hoare.dest_while: unexpected term",[t]);

fun dest_Guard (Const (@{const_name Language.com.Guard},_)$f$g$c) = (f,g,c,false)
  | dest_Guard (Const (@{const_name Language.guaranteeStrip},_)$f$g$c) = (f,g,c,true)
  | dest_Guard t = raise TERM ("Hoare.dest_guard: unexpected term",[t]);



(*** extend theory by procedure definition ***)

fun add_declaration name decl thy =
  thy
  |> Named_Target.init name
  |> Local_Theory.declaration {syntax = false, pervasive = false} decl
  |> Local_Theory.exit
  |> Proof_Context.theory_of;

(* data kind 'HOL/hoare' *)

type proc_info =
  {params: ((par_kind * string) list),
   recursive: bool,
   state_kind: state_kind}

type hoare_tac = (bool -> int -> tactic) -> Proof.context -> hoareMode -> int -> tactic;

type hoare_data =
 {proc_info: proc_info Symtab.table,
  active_procs: string list list,
  default_state_kind: state_kind,
  generate_guard: (stamp * (Proof.context -> term -> term option)),
  wp_tacs: (string * hoare_tac) list,
  hoare_tacs: (string * hoare_tac) list,
  vcg_simps: thm list};


fun make_hoare_data proc_info active_procs default_state_kind generate_guard
     wp_tacs hoare_tacs vcg_simps =
  {proc_info = proc_info, active_procs = active_procs, default_state_kind = default_state_kind,
   generate_guard = generate_guard,
   wp_tacs = wp_tacs, hoare_tacs = hoare_tacs, vcg_simps = vcg_simps};

structure Hoare_Data = Generic_Data
(
  type T = hoare_data;

  val empty = make_hoare_data
               (Symtab.empty: proc_info Symtab.table) (* smlnj needs typing *)
               ([]:string list list)
               (Function)
               (stamp (),(K (K NONE)): Proof.context -> term -> term option)
               ([]:(string * hoare_tac) list)
               ([]:(string * hoare_tac) list)
               ([]:thm list);

  val extend = I;

  (* FIXME exponential blowup due to append !? *)
  fun merge ({proc_info = proc_info1, active_procs = active_procs1,
                 default_state_kind = _,
                  generate_guard = (stmp1,generate_gaurd1),
                 wp_tacs = wp_tacs1, hoare_tacs = hoare_tacs1, vcg_simps = vcg_simps1},
                {proc_info = proc_info2, active_procs = active_procs2,
                 default_state_kind = default_state_kind2,
                 generate_guard = (stmp2, _),
                 wp_tacs = wp_tacs2, hoare_tacs = hoare_tacs2, vcg_simps=vcg_simps2}) : T =
      if stmp1=stmp2 then
          make_hoare_data (Symtab.merge (K true) (proc_info1,proc_info2))
                          (active_procs1 @ active_procs2)
                          (default_state_kind2)
                          (stmp1,generate_gaurd1)
                          (wp_tacs1 @ wp_tacs2)
                          (hoare_tacs1 @ hoare_tacs2)
                          (Thm.merge_thms (vcg_simps1,vcg_simps2))
      else error ("Theories have different aux. functions to generate guards")
);

val get_data = Hoare_Data.get o Context.Proof;


(* access 'params' *)

fun mk_free ctxt name =
  let
    val ctxt' = Context.proof_of ctxt;
    val n' = Variable.intern_fixed ctxt' name |> perhaps Long_Name.dest_hidden;
    val T' = Proof_Context.infer_type ctxt' (n', dummyT) handle ERROR _ => dummyT
  in (Free (n',T')) end;


fun morph_name ctxt phi name =
  (case Morphism.term phi (mk_free ctxt name) of
     Free (x,_) => x
   | _ => name);


datatype 'a bodykind = BodyTyp of 'a | BodyTerm of 'a

fun set_default_state_kind sk ctxt =
  let
    val {proc_info,active_procs,default_state_kind,generate_guard,wp_tacs,hoare_tacs,
           vcg_simps,...}
            = Hoare_Data.get ctxt;
      val data = make_hoare_data proc_info active_procs sk
                   generate_guard wp_tacs hoare_tacs vcg_simps;
  in Hoare_Data.put data ctxt end;

val get_default_state_kind = #default_state_kind o get_data;

fun add_active_procs phi ps ctxt =
  let
      val {proc_info,active_procs,default_state_kind,generate_guard,wp_tacs,hoare_tacs,
           vcg_simps,...}
            = Hoare_Data.get ctxt;
      val data = make_hoare_data proc_info
                   ((map (morph_name ctxt phi) ps)::active_procs)
                   default_state_kind
                   generate_guard wp_tacs hoare_tacs vcg_simps;
  in Hoare_Data.put data ctxt end;


fun add_hoare_tacs tacs ctxt =
  let
      val {proc_info,active_procs, default_state_kind, generate_guard,wp_tacs,hoare_tacs,
           vcg_simps,...}
            = Hoare_Data.get ctxt;
      val data = make_hoare_data proc_info active_procs default_state_kind generate_guard
                   wp_tacs (hoare_tacs@tacs) vcg_simps;
  in Hoare_Data.put data ctxt end;

fun map_vcg_simps f ctxt =
  let
      val {proc_info,active_procs,default_state_kind,generate_guard,wp_tacs,hoare_tacs,
           vcg_simps,...}
            = Hoare_Data.get ctxt;
      val data = make_hoare_data proc_info active_procs default_state_kind generate_guard
                   wp_tacs hoare_tacs (f vcg_simps);
  in Hoare_Data.put data ctxt end;

fun thy_attrib f = Thm.declaration_attribute (fn thm => map_vcg_simps (f thm));

val vcg_simpadd = Thm.add_thm
val vcg_simpdel = Thm.del_thm

val vcg_simp_add = thy_attrib vcg_simpadd;
val vcg_simp_del = thy_attrib vcg_simpdel;


(* add 'procedure' *)

fun mk_proc_info params recursive state_kind =
   {params=params,recursive=recursive,state_kind=state_kind};
val empty_proc_info = {params=[],recursive=false,state_kind=Record};

fun map_proc_info_params f {params,recursive,state_kind} =
     mk_proc_info (f params) recursive state_kind;
fun map_proc_info_recursive f {params,recursive,state_kind} =
     mk_proc_info params (f recursive) state_kind;
fun map_proc_info_state_kind f {params,recursive,state_kind} =
     mk_proc_info params recursive (f state_kind);



fun add_params phi name frmls ctxt =
  let
      val {proc_info,active_procs,default_state_kind,generate_guard,wp_tacs,hoare_tacs,
           vcg_simps,...}
            = Hoare_Data.get ctxt;
      val params = map (apsnd (morph_name ctxt phi)) frmls;
      val f = map_proc_info_params (K params);
      val default = f empty_proc_info;
      val proc_info' = Symtab.map_default (morph_name ctxt phi name,default) f proc_info;
      val data = make_hoare_data proc_info' active_procs default_state_kind
                   generate_guard wp_tacs hoare_tacs vcg_simps;
  in Hoare_Data.put data ctxt end;

fun get_params name ctxt =
  Option.map #params (Symtab.lookup (#proc_info (get_data ctxt)) name);


fun add_recursive phi name ctxt =
  let
     val {proc_info,active_procs,default_state_kind,generate_guard,wp_tacs,hoare_tacs,
          vcg_simps,...}
          = Hoare_Data.get ctxt;
     val f = map_proc_info_recursive (K true);
     val default = f empty_proc_info;
     val proc_info'= Symtab.map_default (morph_name ctxt phi name,default) f proc_info;
     val data = make_hoare_data proc_info' active_procs default_state_kind
                  generate_guard wp_tacs hoare_tacs vcg_simps;
  in Hoare_Data.put data ctxt end;

fun get_recursive name ctxt =
  Option.map #recursive (Symtab.lookup (#proc_info (get_data ctxt)) name);

fun add_state_kind phi name sk ctxt =
  let
     val {proc_info,active_procs,default_state_kind,generate_guard,wp_tacs,hoare_tacs,
          vcg_simps,...}
          = Hoare_Data.get ctxt;
     val f = map_proc_info_state_kind (K sk);
     val default = f empty_proc_info;
     val proc_info'= Symtab.map_default (morph_name ctxt phi name,default) f proc_info;
     val data = make_hoare_data proc_info' active_procs default_state_kind
                  generate_guard wp_tacs hoare_tacs vcg_simps;
  in Hoare_Data.put data ctxt end;

fun get_state_kind name ctxt =
  Option.map #state_kind (Symtab.lookup (#proc_info (get_data ctxt)) name);

fun install_generate_guard f ctxt =
  let
    val {proc_info,active_procs, default_state_kind, generate_guard,wp_tacs,hoare_tacs,
         vcg_simps,...} =
         Hoare_Data.get ctxt;
    val data = make_hoare_data proc_info active_procs default_state_kind (stamp (), f)
                wp_tacs hoare_tacs vcg_simps
  in Hoare_Data.put data ctxt end;

fun generate_guard ctxt = snd (#generate_guard (get_data ctxt)) ctxt;


fun check_procedures_definition procs thy =
    let
        val ctxt = Proof_Context.init_global thy;

        fun already_defined name =
            if is_some (get_params name ctxt)
            then ["procedure " ^ quote name ^ " already defined"]
            else []

        val err_already_defined = maps (already_defined o #1) procs;

        fun duplicate_procs names =
            (case duplicates (op =) names of
               [] => []
             | dups => ["Duplicate procedures " ^ commas_quote dups]);

        val err_duplicate_procs = duplicate_procs (map #1 procs);

        fun duplicate_pars name pars =
            (case duplicates (op =) (map fst pars) of
               [] => []
             | dups => ["Duplicate parameters in procedure "
                        ^ quote name ^ ": " ^ commas_quote dups]);

        val err_duplicate_pars =
             maps (fn (name,inpars,outpars,locals,_,_,_) =>
                      duplicate_pars name (inpars @ locals) @
                      duplicate_pars name (outpars @ locals)) procs;
        (* FIXME: Check that no global variables are used as result parameters *)
        val errs = err_already_defined @ err_duplicate_procs @ err_duplicate_pars;
    in if null errs then () else error (cat_lines errs)
    end;


fun add_parameter_info phi cname (name,(inpars,outpars,state_kind)) ctxt =
    let fun par_deco' T = if T = "" then deco else par_deco (cname name);
        val pars = map (fn (par,T) => (In,suffix (par_deco' T) par)) inpars@
                   map (fn (par,T) => (Out,suffix (par_deco' T) par)) outpars;

        val ctxt_decl = ctxt
              |> add_params phi name pars
              |> add_state_kind phi name state_kind
    in ctxt_decl
    end;

fun mk_loc_exp xs = 
  let fun mk_expr s = (s,(("",false),Expression.Named []))
  in (map mk_expr xs,[]) end;

val parametersN = "_parameters";
val variablesN = "_variables";
val signatureN = "_signature";
val bodyN      = "_body";
val implementationN = "_impl";
val cliqueN = "_clique";
val clique_namesN = "_clique_names";
val NoBodyN = @{const_name Vcg.NoBody};
val statetypeN = "StateType";
val proc_nameT = HOLogic.stringT;

fun expression_no_pos (expr, fixes) : Expression.expression =
  (map (fn (name, inst) => ((name, Position.none), inst)) expr, fixes);

fun add_locale name expr elems thy =
  thy 
  |> Expression.add_locale (Binding.name name) (Binding.name name) expr elems
  |> snd
  |> Local_Theory.exit;

fun add_locale' name expr elems thy =
  thy 
  |> Expression.add_locale (Binding.name name) (Binding.name name) expr elems
  ||> Local_Theory.exit;

fun add_locale_cmd name expr elems thy =
  thy 
  |> Expression.add_locale_cmd (Binding.name name) (Binding.name name)
    (expression_no_pos expr) elems
  |> snd
  |> Local_Theory.exit;

fun read_typ thy raw_T env =
  let
    val ctxt' =
      Proof_Context.init_global thy
      |> fold (Variable.declare_typ o TFree) env;
    val T = Syntax.read_typ ctxt' raw_T;
    val env' = Term.add_tfreesT T env;
  in (T, env') end;

fun add_variable_statespaces (cname, (inpars, outpars, locvars)) thy =
  let
    val inpars'  = if forall (fn (_,T) => T = "") inpars then [] else inpars;
    val outpars' = if forall (fn (_,T) => T = "") outpars then [] else outpars;
    fun prep_comp (n, T) env =
      let
        val (T', env') = read_typ thy T env handle ERROR msg =>
          cat_error msg ("The error(s) above occurred in component " ^ quote n)
      in ((n, T'), env') end;

    val (in_outs,in_out_env) = fold_map prep_comp (distinct (op =) (inpars'@outpars')) [];
    val (locs,var_env) = fold_map prep_comp locvars in_out_env;

    val parSP = cname ^ parametersN;
    val in_outs' = map (apfst (suffix (par_deco cname))) in_outs;
    val in_out_args = map fst in_out_env;

    val varSP = cname ^ variablesN;
    val locs' = map (apfst (suffix (par_deco cname))) locs;
    val var_args = map fst var_env;

  in if null inpars' andalso null outpars' andalso null locvars
     then
       thy
       |> add_locale_cmd parSP ([],[]) [] |> Proof_Context.theory_of
       |> add_locale_cmd varSP ([],[]) [] |> Proof_Context.theory_of
     else
       thy
       |> StateSpace.define_statespace_i (SOME statetypeN) in_out_args parSP [] in_outs'
       |> StateSpace.define_statespace_i (SOME statetypeN)
           var_args varSP [((cname, false), ((map TFree in_out_env),parSP,[]))] locs'
  end;

fun intern_locale thy = Locale.intern thy #> perhaps Long_Name.dest_hidden;

fun apply_in_context thy lexp f t =
  let
    fun name_variant lname =
         if intern_locale thy lname = lname then lname
         else name_variant (lname ^ "'");
  in
    thy
    (* Create a dummy locale in dummy theory just to read the term *)
    |> add_locale_cmd (name_variant "foo") lexp []
    |> (fn ctxt => f ctxt t)
  end;

fun add_abbrev loc mode name spec thy =
  thy
  |> Named_Target.init loc
  |> (fn lthy => let val t = Syntax.read_term (Local_Theory.target_of lthy) spec;
      in Local_Theory.abbrev mode ((Binding.name name, NoSyn), t) lthy end)
  |> #2
  |> Local_Theory.exit
  |> Proof_Context.theory_of;


exception TOPSORT of string
fun topsort less [] = []
  | topsort less xs =
  let
    fun list_all P xs = fold (fn x => fn b => b andalso P x) xs true;

    fun split_min n (x::xs) =
      if n=0 then raise TOPSORT "no minimum in list"
      else if list_all (less x) xs then (x,xs)
      else split_min (n-1) (xs@[x]);

    fun tsort [] = []
      | tsort xs = let val (x,xs') = split_min (length xs) xs;
                   in x::tsort xs' end;
  in tsort xs end;


fun clique_name clique =
      (foldr1 (fn (a,b) => a ^ "_" ^ b) (map (unsuffix proc_deco) clique));


fun error_to_warning msg f thy =
  f thy handle ERROR msg' => (warning (msg' ^ "\n" ^ msg); thy);


fun procedures_definition locname procs thy =
  let
    val procs' = map (fn (name,a,b,c,d,e,f) => (suffix proc_deco name,a,b,c,d,e,f)) procs;
    val _ = check_procedures_definition procs' thy;
    val name_pars  =
         map (fn (name,inpars,outpars,_,_,_,sk)  => (name,(inpars,outpars,sk))) procs';
    val name_vars = map (fn (name,inpars,outpars,locals,_,_,_)  =>
                            (name,(inpars,outpars,locals))) procs';
    val name_body  = map (fn (name,_,_,_,body,_,_)  => (name,body)) procs';
    val name_pars_specs = map (fn (name,inpars,outpars,_,_,specs,sk) =>
                                  (name,(inpars,outpars,sk),specs)) procs';
    val names       = map #1 procs';
    val sk = #7 (hd procs');

    val thy = thy |> Context.theory_map (set_default_state_kind sk);

    val (all_callss,cliques,is_recursive,has_body) =
      let
        val ctxt =
          Context.Theory thy
          |> fold (add_parameter_info  Morphism.identity (unsuffix proc_deco)) name_pars
          |> StateSpace.set_silent true

        fun read_body (_, body) =
          Syntax.read_term (Context.proof_of ctxt) body;

        val bodies = map read_body name_body;
        fun dcall t =
          (case try dest_call t of
             SOME (_,p,_,_,m,_) => SOME (proc_name m p)
           | _ => NONE);
        fun in_names x = if member (op =) names x then SOME x else NONE;
        fun add_edges n = fold (fn x => Graph.add_edge (n, x));

        val all_callss = map (map snd o max_subterms_dest dcall) bodies;
        val callss = map (map_filter in_names) all_callss;
        val graph = fold (fn n => Graph.new_node (n, ())) names Graph.empty;
        val graph' = fold2 add_edges names callss graph;
        fun idx x = find_index (fn y => x=y) names;
        fun name_ord (a,b) = int_ord (idx a, idx b);
        val cliques = Graph.strong_conn graph';
        val cliques' = map (sort name_ord) cliques;

        val my_calls = these o AList.lookup (op =) (names ~~ map (distinct (op =)) callss);
        val my_body = AList.lookup (op =) (names ~~ bodies);

        fun is_recursive n =
          exists (fn [_] => false | ns => member (op =) ns n) (Graph.strong_conn graph');

        fun has_body n =
          (case my_body n of
             SOME (Const (c,_)) => c <> NoBodyN
           | _ => true)

        fun clique_less c1 c2 = null
          (inter (op =) (distinct (op =) (maps my_calls c1)) c2);

        val cliques'' = topsort clique_less cliques';
      in (all_callss,cliques'',is_recursive,has_body) end;

    (* cliques may only depend on ones to the left, so it is safe to
     * add the locales from the left to the right. *)

    fun my_clique n = Library.find_first (fn c => member (op =) c n) cliques;

    fun lname sfx clique = suffix sfx (clique_name clique);
    fun cname n = clique_name (the (my_clique n));
    fun parameter_info_decl phi = fold (add_parameter_info phi cname) name_pars;


    fun get_loc sfx clique n =
        if member (op =) clique n then NONE else SOME (resuffix proc_deco sfx n);

    fun parent_locales thy sfx clique =
      let
        val calls = distinct (op =) (flat
                     (map_filter (AList.lookup (op =) (names ~~ all_callss)) clique));
      in map (intern_locale thy)
            (distinct (op =) (map_filter (get_loc sfx clique) calls))
      end;

    val names_all_callss = names ~~ map (distinct (op =)) all_callss;
    val get_calls = the o AList.lookup (op =) names_all_callss;

    fun clique_vars clique =
      let
        fun add name (ins,outs,locs) =
         let val (nins,nouts,nlocs) = the (AList.lookup (op =) name_vars name)
         in (ins@nins,outs@nouts,locs@nlocs) end;
        val (is,os,ls) = fold add clique ([],[],[]);
      in (lname "" clique, (distinct (op =) is, distinct (op =) os, distinct (op =) ls)) end;

    fun add_signature_locale (cname, name) thy =
      let
        val name' = unsuffix proc_deco name;
        val fixes = [Element.Fixes [(Binding.name name, SOME proc_nameT, NoSyn)]];
        (* FIXME: may use HOLogic.typeT as soon as locale type-inference works properly *)
        val pE = mk_loc_exp [intern_locale thy (suffix parametersN cname)];
        val sN = suffix signatureN  name';
      in thy
         |> add_locale sN pE fixes
         |> Proof_Context.theory_of
         |> (fn thy => add_declaration (intern_locale thy sN) parameter_info_decl thy)
      end;


   fun mk_bdy_def read_term name =
      let
        val name' = unsuffix proc_deco name;
        val bdy = read_term (the (AList.lookup (op =) name_body name));
        val bdy_defN = suffix body_def_sfx name';
        val b = Binding.name bdy_defN;
      in ((b, NoSyn), ((Thm.def_binding b, []), bdy)) end;

   fun add_body_locale (name, _) thy =
      let
        val name' = unsuffix proc_deco name;
        val callees = filter_out (fn n => n = name) (get_calls name)

        val fixes = [Element.Fixes [(Binding.name name, SOME proc_nameT, NoSyn)]];
            (* FIXME: may use HOLogic.typeT as soon as locale type-inference works properly *)
        val pE = mk_loc_exp
                  (map (intern_locale thy)
                    ([lname variablesN (the (my_clique name))]@
                     the_list locname@
                     map (resuffix proc_deco signatureN) callees));


        fun def lthy =
          let val read = Syntax.read_term
                          (Context.proof_map (add_active_procs Morphism.identity
                             (the (my_clique name)))
                           (Local_Theory.target_of lthy))
          in mk_bdy_def read name
          end;

        fun add_decl_and_def lname ctxt =
            ctxt
            |> Proof_Context.theory_of
            |> Named_Target.init lname
            |> Local_Theory.declaration {syntax = false, pervasive = false} parameter_info_decl
            |> (fn lthy => if has_body name
                           then snd (Local_Theory.define (def lthy) lthy)
                           else lthy)
            |> Local_Theory.exit
            |> Proof_Context.theory_of;

      in thy
         |> add_locale' (suffix bodyN name') pE fixes
         |-> add_decl_and_def
      end;

   fun mk_def_eq _ read_term name =
      if has_body name
      then
         let
           (* FIXME: All the read_term stuff is just because type-inference/abbrevs for
            * new locale elements does not work right now;
            * We read the term to expand the abbreviations, then we print it again
            * (without folding the abbreviation) and reread as string  *)
           val name' = unsuffix proc_deco name;
           val bdy_defN = suffix body_def_sfx name';
           val rhs = read_term ("Some " ^ bdy_defN);
           val nt  = read_term name;
           val Free (gamma,_) = read_term programN;
           val eq = HOLogic.Trueprop$
                     HOLogic.mk_eq (Free (gamma,fastype_of nt --> fastype_of rhs)$nt,rhs)
           val eqs =
             YXML.string_of_body (Term_XML.Encode.term (map_types (K dummyT) eq));
           val assms = Element.Assumes [((Binding.name (suffix bodyP name'), []),[(eqs,[])])]
         in [assms]
         end
      else [];

   fun add_impl_locales clique thy =
      let
        val cliqN =  lname cliqueN clique;
        val cnamesN = lname clique_namesN clique;
        val multiple_procs = length clique > 1;
        val add_distinct_procs_namespace =
            if multiple_procs
            then StateSpace.namespace_definition cnamesN proc_nameT ([],[]) [] clique
            else I;
        val bodyLs = map (suffix bodyN o unsuffix proc_deco) clique;
        fun pE thy = mk_loc_exp (map (intern_locale thy) (hoare_ctxtL::bodyLs)
                              @ (parent_locales thy implementationN clique)
                              @ (if multiple_procs then [intern_locale thy cnamesN] else []));
        fun read_term thy = apply_in_context thy (pE thy) Syntax.read_term;
        fun elems thy = maps (mk_def_eq thy (read_term thy)) clique;
        fun add_recursive_info phi name =
            if is_recursive name then (add_recursive phi name) else I;
        fun proc_declaration phi = add_active_procs phi clique;
        fun recursive_declaration phi ctxt =
            ctxt |> fold (add_recursive_info phi) clique;


        fun add_impl_locale name thy =
          let
            val implN = suffix implementationN (unsuffix proc_deco name);
            val parentN = intern_locale thy cliqN
            val parent = mk_loc_exp [parentN];
          in thy
             |> add_locale_cmd implN parent []
             |> Proof_Context.theory_of
             |> (fn thy => Interpretation.global_sublocale parentN
                  (mk_loc_exp [intern_locale thy implN]) [] [] thy)
             |> Proof.global_terminal_proof
                 ((Method.Basic (fn ctxt => Method.SIMPLE_METHOD
                                 (Locale.intro_locales_tac false ctxt [])), Position.no_range), NONE)
             |> Proof_Context.theory_of
          end;

      in thy
         |> add_distinct_procs_namespace
         |> (fn thy =>
              add_locale_cmd cliqN (pE thy) (elems thy) thy)
         |> Proof_Context.theory_of
         |> fold add_impl_locale clique
         |> (fn thy => add_declaration (intern_locale thy cliqN) proc_declaration thy)
         |> (fn thy => add_declaration (intern_locale thy cliqN)
                recursive_declaration thy)
      end;

   fun add_spec_locales (name, _, specs) thy =
      let
        val name' = unsuffix proc_deco name;
        val ps = (suffix signatureN name' :: the_list locname);
        val ps' = hoare_ctxtL :: ps ;
        val pE = mk_loc_exp (map (intern_locale thy) ps)
        val pE' = mk_loc_exp (map (intern_locale thy) ps')

        fun read thy =
         apply_in_context thy
            (mk_loc_exp [intern_locale thy (suffix cliqueN (cname name))])
            (Syntax.read_prop);

        fun proc_declaration phi =
                 (*parameter_info_decl phi o  already in signature *)
                 add_active_procs phi (the (my_clique name));

        fun add_locale'' (thm_name,spec) thy =
          let
            val spec' = read thy spec;
            val elem = Element.Assumes [((Binding.name thm_name, []), [(spec', [])])];
          in thy
             |> add_locale thm_name pE' [elem]
             |> Proof_Context.theory_of
             |> (fn thy =>
                  add_declaration (intern_locale thy thm_name) proc_declaration thy)
             |> error_to_warning ("abbreviation: '" ^ thm_name  ^ "' not added")
                  (add_abbrev (intern_locale thy (suffix cliqueN (cname name))) Syntax.mode_input thm_name spec)
          end;
      in thy |> fold add_locale'' specs end;

  in
    thy
    |> fold (add_variable_statespaces o clique_vars) cliques
    |> fold (fn c => fold (fn n => add_signature_locale (lname "" c, n)) c) cliques
    |> fold add_body_locale name_pars
    |> fold add_impl_locales cliques
    |> fold add_spec_locales name_pars_specs
  end;



(*********************  theory extender interface ********************************)

(** package setup **)

(* outer syntax *)

val var_declP  = Parse.name -- (@{keyword "::"} |-- Parse.!!! Parse.typ_group);
val var_declP' = Parse.name >> (fn n => (n,""));

val localsP = Scan.repeat var_declP;

val argP = var_declP;
val argP' = var_declP';

val not_eqP = Scan.ahead (Scan.unless @{keyword "="} (Scan.one (K true)))

val proc_decl_statespace =
  (Parse.short_ident --| @{keyword "("}) --
      ((Parse.list argP) -- (Scan.optional (@{keyword "|"} |-- Parse.list argP) []) --| @{keyword ")"})
      --| not_eqP

val proc_decl_record =
  (Parse.short_ident --| @{keyword "("}) --
      ((Parse.list argP') -- (Scan.optional (@{keyword "|"} |-- Parse.list argP') []) --| @{keyword ")"})
      --| Scan.option @{keyword "="}

val proc_decl = proc_decl_statespace >> pair Function || proc_decl_record >> pair Record;

val loc_decl = Scan.optional (@{keyword "where"} |-- localsP --| @{keyword "in"}) []

val proc_body = Parse.term_group (*>> BodyTerm*)


fun proc_specs x = (Parse.!!! (Scan.repeat (Parse_Spec.thm_name ":" -- Parse.prop_group))
    >> map (fn ((thm_name, _), prop) => (Binding.name_of thm_name, prop))) x

val par_loc =
  Scan.option (@{keyword "("} |-- @{keyword "imports"} |-- Parse.name --| @{keyword ")"});


val _ =
  Outer_Syntax.command @{command_keyword procedures} "define procedures"
    (par_loc -- (Parse.and_list1 (proc_decl -- loc_decl -- proc_body -- proc_specs))
      >> (fn (loc,decls) =>
          let
            val decls' = map (fn ((((state_kind,(name,(ins,outs))),ls),bdy),specs) =>
                                 (name,ins,outs,ls,bdy,specs,state_kind))
                           decls
          in Toplevel.theory (procedures_definition loc decls')
          end));


val _ =
  Outer_Syntax.command @{command_keyword hoarestate} "define state space for hoare logic"
    (StateSpace.statespace_decl >> (fn ((args,name),(parents,comps)) =>
      Toplevel.theory
        (StateSpace.define_statespace args name parents (map (apfst (suffix deco)) comps))));



(***************************  Auxiliary Functions for integration of  ********************)
(***************************  automatic program analysers             ********************)

fun dest_conjs t =
  (case HOLogic.dest_conj t of
     [t1,t2] => dest_conjs t1 @ dest_conjs t2
   | ts => ts);

fun split_guard (Const (@{const_name Collect},CT)$(Abs (s,T,t))) =
     let
       fun mkCollect t = Const (@{const_name Collect},CT)$(Abs (s,T,t));
     in map mkCollect (dest_conjs t) end
  | split_guard t = [t];

fun split_guards gs =
  let
    fun norm c f g = map (fn g => c$f$g) (split_guard g);
    fun norm_guard ((c as Const (@{const_name Pair},_))$f$g) = norm c f g
      | norm_guard ((c as Const (@{const_name Language.guaranteeStripPair},_))$f$g) = norm c f g
      | norm_guard t = [t];
  in maps norm_guard (HOLogic.dest_list gs)
  end

fun fold_com f t =
  let
    (* traverse does not descend into abstractions, like in DynCom, call, etc. *)
    fun traverse cnt (c as Const (@{const_name Language.com.Skip},_)) = (cnt,f cnt c [] [])
      | traverse cnt ((c as Const (@{const_name Language.com.Basic},_))$g) = (cnt, f cnt c [g] [])
      | traverse cnt ((c as Const (@{const_name Language.com.Spec},_))$r) = (cnt, f cnt c [r] [])
      | traverse cnt ((c as Const (@{const_name Language.com.Seq},_))$c1$c2) =
          let
            val (cnt1,v1) = traverse cnt c1;
            val (cnt2,v2) = traverse cnt1 c2;
          in (cnt2, f cnt c [] [v1,v2]) end
      | traverse cnt ((c as Const (@{const_name Language.com.Cond},_))$b$c1$c2) =
          let
            val (cnt1,v1) = traverse cnt c1;
            val (cnt2,v2) = traverse cnt1 c2;
          in (cnt2, f cnt c [b] [v1,v2]) end
      | traverse cnt ((c as Const (@{const_name Language.com.While},_))$b$c1) =
          let val (cnt1,v1) = traverse cnt c1 in (cnt1, f cnt c [b] [v1]) end
      | traverse cnt ((c as Const (@{const_name Language.com.Call},_))$p) = (cnt, f cnt c [p] [])
      | traverse cnt ((c as Const (@{const_name Language.com.DynCom},_))$c1) = (cnt, f cnt c [c1] [])
      | traverse cnt ((c as Const (@{const_name Language.com.Guard},_))$flt$g$c1) =
          let val (cnt1,v1) = traverse (cnt + length (split_guard g)) c1
          in (cnt1, f cnt c [flt,g] [v1]) end
      | traverse cnt (c as Const (@{const_name Language.com.Throw},_)) = (cnt,f cnt c [] [])
      | traverse cnt ((c as Const (@{const_name Language.com.Catch},_))$c1$c2) =
          let
            val (cnt1,v1) = traverse cnt c1;
            val (cnt2,v2) = traverse cnt1 c2;
          in (cnt2, f cnt c [] [v1,v2]) end
      | traverse cnt ((c as Const (@{const_name Language.guards},_))$gs$c1) =
          let
            val (cnt1,v1) = traverse (cnt + length (split_guards gs)) c1;
          in (cnt1, f cnt c [gs] [v1]) end
      | traverse cnt ((c as Const (@{const_name Language.block},_))$init$c1$return$c2) =
          let val (cnt1,v1) = traverse cnt c1 in (cnt1, f cnt c [init,return,c2] [v1]) end
      | traverse cnt ((c as Const (@{const_name Language.call},_))$init$p$return$c1) =
           (cnt, f cnt c [init,p,return,c1] [])
      | traverse cnt ((c as Const (@{const_name Language.whileAnno},_))$b$I$V$c1) =
          let val (cnt1,v1) = traverse cnt c1 in (cnt1, f cnt c [b,I,V] [v1]) end
      | traverse cnt ((c as Const (@{const_name Language.whileAnnoG},_))$gs$b$I$V$c1) =
          let val (cnt1,v1) = traverse (cnt + length (split_guards gs)) c1
          in (cnt1, f cnt c [gs,b,I,V] [v1]) end
      | traverse _ t = raise TERM ("fold_com: unknown command",[t]);
   in snd (traverse 0 t) end;

(***************************  Tactics ****************************************************)


(*** Aux. tactics ***)


fun cond_rename_bvars cond name thm =
  let
    fun rename (tm as (Abs (x, T, t))) =
          if cond tm then Abs (name x, T, rename t) else Abs (x, T, rename t)
      | rename (t $ u) = rename t $ rename u
      | rename a = a;
  in Thm.renamed_prop (rename (Thm.prop_of thm)) thm end;

val rename_bvars = cond_rename_bvars (K true);

fun trace_tac ctxt str st = (if Config.get ctxt hoare_trace then tracing str else (); all_tac st);

fun error_tac str st = (error str;no_tac st);

fun rename_goal ctxt name =
    EVERY' [K (trace_tac ctxt "rename_goal -- START"),
            SELECT_GOAL (PRIMITIVE (rename_bvars name)),
            K (trace_tac ctxt "rename_goal -- STOP")];

(* splits applications of tupled arguments to a schematic Variables, e.g.
 *  ALL a b. ?P (a,b) --> ?Q (a,b) gets
 *  ALL a b. ?P a b --> ?Q a b
 * only tuples nested to the right are splitted.
 *)
fun split_pair_apps ctxt thm =
  let
    val t = Thm.prop_of thm;
    fun mk_subst subst (Abs (x,T,t)) = mk_subst subst t
      | mk_subst subst (t as (t1$t2)) =
         (case strip_comb t of
            (var as Var (v,vT),args) =>
            (if not (AList.defined (op =) subst var)
             then
              let
                val len = length args;
                val (argTs,bdyT) = strip_type vT;
                val (z, _) = Name.variant "z" (fold Term.declare_term_frees args Name.context);
                val frees = map (apfst (fn i => z^string_of_int i))
                                (0 upto (len - 1) ~~ argTs);
                fun splitT (Type (@{type_name Product_Type.prod}, [T1, T2])) = T1::splitT T2
                  | splitT T = [T];

                fun pair_depth (Const (@{const_name Pair},aT)$t1$t2) = 1 + (pair_depth t2)
                  | pair_depth _ = 0;

                fun mk_sel max free i  =
                  let val snds = funpow i HOLogic.mk_snd (Free free)
                  in if i=max then snds else HOLogic.mk_fst snds end;


                fun split (free,arg) =
                  let
                    val depth = (pair_depth arg);
                  in if depth = 0 then [Free free]
                     else map (mk_sel depth free) (0 upto depth)
                  end;


                val args' = maps split (frees ~~ args);
                val argTs' = maps splitT argTs;
                val inst = fold_rev absfree frees (list_comb (Var (v,argTs' ---> bdyT), args'))
              in subst@[(var,inst)]
              end
             else subst)
          | _ =>  mk_subst (mk_subst subst t1) t2)
      | mk_subst subst t = subst;

  val subst = map (fn (v,t) => (dest_Var v, Thm.cterm_of ctxt t)) (mk_subst [] t);

  in full_simplify (put_simpset HOL_basic_ss ctxt addsimps [@{thm fst_conv}, @{thm snd_conv}])
       (Drule.instantiate_normalize ([],subst) thm)
  end;

(* Generates split theorems, for !!,!,? quantifiers and for UN, e.g.
 * ALL x. P x = ALL a b. P a b
 *)
fun mk_split_thms ctxt (vars as _::_)  =
  let
    val thy = Proof_Context.theory_of ctxt;
    val names = map fst vars;
    val types = map snd vars;
    val free_vars = map Free vars;
    val pT = foldr1 HOLogic.mk_prodT types;
    val x = (singleton (Name.variant_list names) "x", pT);
    val xp = foldr1 HOLogic.mk_prod free_vars;
    val tfree_names = fold Term.add_tfree_names free_vars [];
    val zeta = TFree (singleton (Name.variant_list tfree_names) "z", Sign.defaultS thy);

    val split_meta_prop =
      let val P = Free (singleton (Name.variant_list names) "P", pT --> Term.propT)
      in Logic.mk_equals (Logic.all (Free x) (P $ Free x), fold_rev Logic.all free_vars (P $ xp))
      end;

    val P = Free (singleton (Name.variant_list names) "P", pT --> HOLogic.boolT);

    val split_object_prop =
      let fun ALL vs t = Library.foldr (fn ((v,T),t) => HOLogic.mk_all (v,T,t)) (vs,t)
      in (ALL [x] (P $ Free x)) === (ALL vars (P $ xp))
      end;

    val split_ex_prop =
      let fun EX vs t = Library.foldr (fn ((v,T),t) => HOLogic.mk_exists (v,T,t)) (vs,t)
      in (EX [x] (P $ Free x)) === (EX vars (P $ xp))
      end;

    val split_UN_prop =
      let val P = Free (singleton (Name.variant_list names) "P", pT --> HOLogic.mk_setT zeta);
          fun UN vs t = Library.foldr mk_UN (vs, t)
      in (UN [x] (P $ Free x)) === (UN vars (P $ xp))
      end;

    fun prove_simp simps prop =
      let val ([prop'], _) = Variable.importT_terms [prop] ctxt  (* FIXME continue context!? *)
      in
        Goal.prove_global thy [] [] prop'
          (fn {context = ctxt, ...} =>
            ALLGOALS (simp_tac (put_simpset HOL_basic_ss ctxt addsimps simps)))
      end;

    val split_meta   = prove_simp [@{thm split_paired_all}] split_meta_prop;
    val split_object = prove_simp [@{thm split_paired_All}] split_object_prop;
    val split_ex     = prove_simp [@{thm split_paired_Ex}] split_ex_prop;
    val split_UN     = prove_simp [@{thm Hoare.split_paired_UN}] split_UN_prop;
  in [split_meta,split_object,split_ex,split_UN]
  end
 | mk_split_thms _ _ = raise Match;


fun rename_aux_var name rule =
  let fun is_aux_var (Abs ("Z",TVar(_,_),_)) = true
        | is_aux_var _ = false;
  in cond_rename_bvars is_aux_var (K name) rule end;

(* adapts single auxiliary variable in a rule to potentialy multiple auxiliary
 * variables in actual specification, e.g. if vars are a b,
 * split_app=false: ALL Z. ?P Z gets to ALL a b. ?P (a,b)
 * split_app=true:  ALL Z. ?P Z gets to ALL a b. ?P a b
 * If only one auxiliary variable is given, the variables are just renamed,
 * If no auxiliary is given, unit is inserted for Z:
 * ALL Z. ?P Z gets P ()
 *)
fun adapt_aux_var ctxt split_app (vars as (_::_::_)) tvar_rules =
     let
       val thy = Proof_Context.theory_of ctxt;
       val max_idx = fold Integer.max (map (Thm.maxidx_of o snd) tvar_rules) 0;
       val types = map (fn i => TVar (("z",i),Sign.defaultS thy))
                    (max_idx + 1 upto (max_idx + length vars));
       fun tvar n = (n, Sign.defaultS thy);
       val pT = Thm.ctyp_of ctxt (foldr1 HOLogic.mk_prodT types);
       val rules' = map (fn (z,r) => (Drule.instantiate_normalize ([(tvar z,pT)],[]) r)) tvar_rules;
       val splits = mk_split_thms ctxt (vars ~~ types);
       val rules'' = map (full_simplify (put_simpset HOL_basic_ss ctxt addsimps splits)) rules';
     in if split_app then (map (split_pair_apps ctxt) rules'') else rules'' end
  | adapt_aux_var _ _ ([name]) tvar_rules = map (rename_aux_var name o snd) tvar_rules
  | adapt_aux_var ctxt _ ([]) tvar_rules =
      let
        val thy = Proof_Context.theory_of ctxt;
        fun tvar n = (n, Sign.defaultS thy);
        val uT = Thm.ctyp_of ctxt HOLogic.unitT;
        val rules' = map (fn (z,r) => (Drule.instantiate_normalize ([(tvar z,uT)],[]) r)) tvar_rules;
        val splits = [@{thm Hoare.unit_meta},@{thm Hoare.unit_object},@{thm Hoare.unit_ex},@{thm Hoare.unit_UN}];
        val rules'' = map (full_simplify (put_simpset HOL_basic_ss ctxt addsimps splits)) rules';
      in rules'' end


(* Generates a rule for recursion for n procedures out of general recursion rule *)
fun gen_call_rec_rule ctxt specs_name n rule =
  let
    val thy = Proof_Context.theory_of ctxt;
    val maxidx = Thm.maxidx_of rule;
    val vars = Term.add_vars (Thm.prop_of rule) [];
    fun get_type n = the (AList.lookup (op =) vars (n, 0));
    val (Type (_, [Type (_, [assT, Type (_, [pT,_])])])) = get_type specs_name;
    val zT = TVar (("z",maxidx+1),Sign.defaultS thy)

    fun mk_var i n T = Var ((n ^ string_of_int i,0),T);

    val quadT = HOLogic.mk_prodT (assT,
                          HOLogic.mk_prodT (pT,
                           HOLogic.mk_prodT (assT,assT)));
    val quadT_set = HOLogic.mk_setT quadT;
    fun mk_spec i =
      let
         val quadruple = HOLogic.mk_ptuple (HOLogic.flat_tupleT_paths quadT) quadT
                [mk_var i "P" (zT --> assT)$Bound 0,
                 mk_var i "p" pT,
                 mk_var i "Q" (zT --> assT)$Bound 0,
                 mk_var i "A" (zT --> assT)$Bound 0];
         val single = HOLogic.mk_set quadT [quadruple];
     in mk_UN' zT quadT_set (Abs ("Z", zT, single)) end;

     val Specs = foldr1 (mk_Un quadT_set) (map mk_spec (1 upto n));
     val rule' =
       Thm.instantiate' [] [SOME (Thm.cterm_of ctxt Specs)] rule
       |> full_simplify (put_simpset (simpset_of @{theory_context Main}) ctxt
              addsimps [@{thm Hoare.conjE_simp},@{thm Hoare.in_Specs_simp},@{thm Hoare.in_set_Un_simp},@{thm split_all_conj},
                        @{thm image_Un},@{thm image_Un_single_simp}] )
       |> rename_bvars (fn s => if member (op =) ["s","\<sigma>"] s then s else "Z")
  in rule'
  end;

fun gen_proc_rec ctxt mode n =
  gen_call_rec_rule ctxt "Specs" n (ProcRecSpecs mode);

(*** verification condition generator ***)

(* simplifications on "Collect" sets, like {s. P s} Int {s. Q s} = {s. P s & Q s} *)
fun merge_assertion_simp_tac ctxt thms =
     simp_tac (put_simpset HOL_basic_ss ctxt
                   addsimps ([@{thm Hoare.CollectInt_iff},@{thm HOL.conj_assoc},@{thm Hoare.Compl_Collect},singleton_conv_sym,
                   @{thm Set.Int_empty_right},@{thm Set.Int_empty_left},@{thm Un_empty_right},@{thm Un_empty_left}]@thms)) ;

(* The following probably shouldn't live here, but refactoring
   so that Hoare could depend on recursive_records does not look feasible.
   The upshot is that there's a duplicate foldcong_ss set here. *)
structure FoldCongData = Theory_Data
(
  type T = simpset;
  val empty = HOL_basic_ss;

  val copy = I;
  val extend = I;
  val merge = merge_ss;
)

val get_foldcong_ss = FoldCongData.get

fun add_foldcongs congs thy = FoldCongData.map (fn ss =>
        Proof_Context.init_global thy
        |> put_simpset ss
        |> fold Simplifier.add_cong congs
        |> simpset_of) thy

fun add_foldcongsimps simps thy = FoldCongData.map (fn ss =>
        Proof_Context.init_global thy
        |> put_simpset ss
        |> (fn ctxt => ctxt addsimps simps)
        |> simpset_of) thy

(* propagates state into "Collect" sets and simplifies selections updates like:
 *  s:{s. P s} = P s
 *)
fun in_assertion_simp_tac ctxt state_kind thms i =
 let
     val vcg_simps = #vcg_simps (get_data ctxt);
     val fold_simps = get_foldcong_ss (Proof_Context.theory_of ctxt)
 in
   EVERY [simp_tac
            (put_simpset HOL_basic_ss ctxt addsimps ([mem_Collect_eq,@{thm Set.Un_iff},@{thm Set.Int_iff},
                                     @{thm Set.empty_subsetI}, @{thm Set.empty_iff}, UNIV_I,
                                     @{thm Hoare.Collect_False}]@thms@K_convs@vcg_simps)
                          addsimprocs (state_simprocs state_kind)
                          |> fold Simplifier.add_cong K_congs)  i
           THEN_MAYBE
           (simp_tac (put_simpset fold_simps ctxt addsimprocs [state_upd_simproc state_kind])  i)
         ]
 end;


fun assertion_simp_tac ctxt state_kind thms i =
    merge_assertion_simp_tac ctxt [] i
    THEN_MAYBE in_assertion_simp_tac ctxt state_kind thms i

(* simplify equality test on strings (and datatype-constructors) and propagate result*)
fun string_eq_simp_tac ctxt =
  simp_tac (put_simpset HOL_basic_ss ctxt
    addsimps (@{thms list.inject} @ @{thms char.inject}
      @ @{thms list.distinct} @ @{thms simp_thms}));
    


fun assertion_string_eq_simp_tac ctxt state_kind thms i =
    assertion_simp_tac ctxt state_kind thms i THEN_MAYBE string_eq_simp_tac ctxt i;


fun before_set2pred_simp_tac ctxt =
  (simp_tac (put_simpset HOL_basic_ss ctxt addsimps [singleton_conv_sym,
                                    @{thm Hoare.CollectInt_iff},
                                    @{thm Hoare.Compl_Collect}]));

(*****************************************************************************)
(** set2pred transforms sets inclusion into predicates implication,         **)
(** maintaining the original variable names.                                **)
(** Ex. "{x. x=0} <= {x. x <= 1}" -set2pred-> "x=0 --> x <= 1"              **)
(** Subgoals containing intersections (A Int B) or complement sets (-A)     **)
(** are first simplified by "before_set2pred_simp_tac", that returns only   **)
(** subgoals of the form "{x. P x} <= {x. Q x}", which are easily           **)
(** transformed.                                                            **)
(** This transformation may solve very easy subgoals due to a ligth         **)
(** simplification done by full_simp_tac                                    **)
(*****************************************************************************)

fun set2pred_tac ctxt i thm =
  ((before_set2pred_simp_tac ctxt i) THEN_MAYBE
          (EVERY [trace_tac ctxt "set2pred",
                  resolve_tac ctxt [subsetI] i,
                  resolve_tac ctxt [CollectI] i,
                  dresolve_tac ctxt [CollectD] i,
                  full_simp_tac (put_simpset HOL_basic_ss ctxt) i ])) thm


(*****************************************************************************)
(** BasicSimpTac is called to simplify all verification conditions. It does **)
(** a light simplification by applying "mem_Collect_eq"                     **)
(** then it tries to solve subgoals of the form "A <= A" and then if        **)
(** set2pred is true it                                                     **)
(** transforms any other into predicates, applying then                     **)
(** the tactic chosen by the user, which may solve the subgoal completely   **)
(** (MaxSimpTac).                                                           **)
(*****************************************************************************)

fun MaxSimpTac ctxt tac i =
  TRY (FIRST[resolve_tac ctxt [subset_refl] i,
      set2pred_tac ctxt i THEN_MAYBE tac i,
      trace_tac ctxt "final_tac failed"
      ]);

fun BasicSimpTac ctxt state_kind set2pred thms tac i =
 EVERY [(trace_tac ctxt "BasicSimpTac -- START --"),
         assertion_simp_tac ctxt state_kind thms i
         THEN_MAYBE (if set2pred then MaxSimpTac ctxt tac i else TRY (resolve_tac ctxt [subset_refl] i)),
        (trace_tac ctxt "BasicSimpTac -- STOP --")];
(*
 EVERY [(trace_tac ctxt "BasicSimpTac -- START --"),
         simp_tac
          (HOL_basic_ss addsimps [mem_Collect_eq,@{thm Hoare.CollectInt_iff},
                                  @{thm Set.empty_subsetI}, @{thm Set.empty_iff}, UNIV_I]
                        addsimprocs [state_simproc sk]) i
         THEN_MAYBE
         simp_tac (HOL_basic_ss  addsimprocs [state_upd_simproc sk]) i
         THEN_MAYBE (if set2pred then MaxSimpTac ctxt tac i else TRY (rtac subset_refl i)),
        (trace_tac ctxt "BasicSimpTac -- STOP --")];
*)



(*
fun simp_state_eq_tac Record state_space =
  full_simp_tac (HOL_basic_ss addsimprocs (state_simprocs Record))
  THEN_MAYBE'
  full_simp_tac (HOL_basic_ss addsimprocs [state_upd_simproc Record])
  THEN_MAYBE'
  (state_split_simp_tac [] state_space)
  | simp_state_eq_tac StateFun state_space =
*)

fun post_conforms_tac ctxt state_kind i =
   EVERY [REPEAT1 (resolve_tac ctxt [allI,impI] i),
          ((fn i => TRY (resolve_tac ctxt [conjI] i))
           THEN_ALL_NEW
          (fn i => (REPEAT (resolve_tac ctxt [allI,impI] i))
                    THEN (full_simp_tac (put_simpset HOL_basic_ss ctxt addsimps
                             [mem_Collect_eq,@{thm Set.singleton_iff},@{thm Set.empty_iff},UNIV_I]
                             addsimprocs (state_simprocs state_kind)) i))) i];


fun dest_hoare_raw (Const(@{const_name HoarePartialDef.hoarep},_)$G$T$F$P$C$Q$A) = (P,C,Q,A,Partial,G,T,F)
  | dest_hoare_raw (Const(@{const_name HoareTotalDef.hoaret},_)$G$T$F$P$C$Q$A) = (P,C,Q,A,Total,G,T,F)
  | dest_hoare_raw t = raise TERM ("Hoare.dest_hoare_raw: unexpected term",[t])


fun mk_hoare_abs Ts (P,C,Q,A,mode,G,T,F) =
  let
    val hoareT = map (curry fastype_of1 Ts) [G,T,F,P,C,Q,A] ---> HOLogic.boolT;
    val hoareC = (case mode of Partial => Const (@{const_name HoarePartialDef.hoarep},hoareT)
                     | Total => Const (@{const_name HoareTotalDef.hoaret},hoareT));
  in hoareC$G$T$F$P$C$Q$A end;


val is_hoare = can dest_hoare_raw

fun dest_hoare t =
    let
      val triple =
        (strip_qnt_body @{const_name "All"} o
          HOLogic.dest_Trueprop o strip_qnt_body @{const_name Pure.all}) t;
    in
      dest_hoare_raw triple
    end;


fun get_aux_tvar rule =
  let
    fun aux_hoare (Abs ("Z",TVar (z,_),t)) =
          if is_hoare (strip_qnt_body @{const_name All} t)
          then SOME z
          else NONE
      | aux_hoare _ = NONE;
  in (case first_subterm_dest (aux_hoare) (Thm.prop_of rule) of
        SOME (_,z) => (z,rule)
      | NONE => raise TERM ("get_aux_tvar: No auxiliary variable of hoare-rule found",
                             [Thm.prop_of rule]))
  end;

fun strip_vars t =
  let
    val bdy = (HOLogic.dest_Trueprop o Logic.strip_assums_concl) t;
  in strip_qnt_vars @{const_name Pure.all} t @ strip_qnt_vars @{const_name All} bdy end;


local
(* ex_simps are necessary in case of multiple logical variables. The state will
   usually be the first variable. EX s a b. s=s' ... . We have to transport
   EX s to s=s' to perform the substitution *)

val conseq1_ss_base =
  simpset_of (put_simpset HOL_basic_ss @{context}
    addsimps ([mem_Collect_eq,@{thm Set.singleton_iff},@{thm Set.Int_iff},
              @{thm Set.empty_iff},UNIV_I,
              @{thm HOL.conj_assoc}, @{thm disj_assoc}] @ @{thms Hoare.all_imp_eq_triv}
              @K_convs @ @{thms simp_thms} @ @{thms ex_simps} @ @{thms all_simps})
    delsimps [@{thm Hoare.all_imp_to_ex}]
    |> fold Simplifier.add_cong K_congs)
val conseq1_ss_record =
  simpset_of (put_simpset conseq1_ss_base @{context} addsimprocs (state_simprocs Record));
val conseq1_ss_fun =
  simpset_of (put_simpset conseq1_ss_base @{context} addsimprocs (state_simprocs Function));
fun conseq1_ss Record   = conseq1_ss_record
  | conseq1_ss Function = conseq1_ss_fun;

val conseq2_ss_base =
  simpset_of (put_simpset HOL_basic_ss @{context}
    addsimps (@{thms Hoare.all_imp_eq_triv} @ @{thms simp_thms} @ @{thms ex_simps} @ @{thms all_simps})
    delsimps [@{thm Hoare.all_imp_to_ex}]
    |> Simplifier.add_cong @{thm imp_cong});

val conseq2_ss_record =
  simpset_of (put_simpset conseq2_ss_base @{context}
    addsimprocs [state_upd_simproc Record, state_ex_sel_eq_simproc Record]);
val conseq2_ss_fun =
  simpset_of (put_simpset conseq2_ss_base @{context}
    addsimprocs [state_upd_simproc Function, state_ex_sel_eq_simproc Function]);
fun conseq2_ss Record   = conseq2_ss_record
  | conseq2_ss Function = conseq2_ss_fun;

in

fun raw_conseq_simp_tac ctxt state_kind thms i =
  let
    val ctxt' = Config.put simp_depth_limit 0 ctxt;
  in
     simp_tac (put_simpset (conseq1_ss state_kind) ctxt' addsimps thms) i
     THEN_MAYBE
     simp_tac (put_simpset (conseq2_ss state_kind) ctxt') i
  end

end

val conseq_simp_tac = raw_conseq_simp_tac;

(* Generates the hoare-quadruples that can be derived out of the hoare-context T *)
fun gen_context_thms ctxt mode params G T F =
  let
    val Type (_,[comT]) = range_type (fastype_of G);

    fun destQuadruple (Const (@{const_name Set.insert},_) $ PpQA $ Const (@{const_name Orderings.bot}, _)) = PpQA
      | destQuadruple t = raise Match;

    fun mkCallQuadruple (Const (@{const_name Pair}, _) $ P $ (Const (@{const_name Pair}, _)
        $ p $ (Const(@{const_name Pair}, _) $ Q $ A))) =
      let val Call_p = Const (@{const_name Language.com.Call}, fastype_of p --> comT) $ p;
      in (P, Call_p, Q, A) end;

    fun mkHoare mode G T F (vars,PpQA) =
      let
        val hoare =
          (case mode of Partial => @{const_name HoarePartialDef.hoarep}
          | Total => @{const_name HoareTotalDef.hoaret});
        (* FIXME: Use future Proof_Context.rename_vars or make closed term and remove by hand *)
        (*
        fun free_params ps t = foldr (fn ((x,xT),t) => snd (variant_abs (x,xT,t))) (ps,t);
        val PpQA' = mkCallQuadruple (strip_qnt_body @{const_name Pure.all} (free_params params (Term.list_all (vars,PpQA))));
        *)
        val params' = (Variable.variant_frees ctxt [PpQA] params);
        val bnds = map Bound (0 upto (length vars  - 1));
        fun free_params_vars t = subst_bounds (bnds @ rev (map Free params' ), t)
        fun free_params t = subst_bounds (rev (map Free params' ), t)
        val (P',p',Q',A') = mkCallQuadruple (free_params_vars PpQA);

        val T' = free_params T;
        val G' = free_params G;
        val F' = free_params F;
        val bdy = mk_hoare_abs [] (P',p',Q',A',mode,G',T',F');

      in (HOLogic.mk_Trueprop (HOLogic.list_all (vars,bdy)), map fst params')
      end;

    fun hoare_context_specs mode G T F =
      let fun mk t = try (mkHoare mode G T F o apsnd destQuadruple o dest_UN) t;
      in map_filter mk (dest_Un T) end;


    fun mk_prove mode (prop,params) =
      let
        val vars = map fst (strip_qnt_vars @{const_name All}
                             (HOLogic.dest_Trueprop (Logic.strip_assums_concl prop)));
        val [asmUN'] = adapt_aux_var ctxt true vars [get_aux_tvar (AsmUN mode)]
      in Goal.prove ctxt params [] prop
          (fn thms =>
            EVERY[trace_tac ctxt "extracting specifications from hoare context",
                  resolve_tac ctxt [asmUN'] 1,
                  DEPTH_SOLVE_1 (resolve_tac ctxt [subset_refl,refl] 1 ORELSE
                    ((resolve_tac ctxt [@{thm Hoare.subset_unI1}] 1 APPEND resolve_tac ctxt [@{thm Hoare.subset_unI2}] 1)
                     ORELSE
                     (resolve_tac ctxt [@{thm Hoare.subset_singleton_insert1}] 1
                      APPEND resolve_tac ctxt [@{thm Hoare.subset_singleton_insert2}] 1)))
                  ORELSE error_tac ("vcg: cannot extract specifications from context")
                 ])
      end;

    val specs = hoare_context_specs mode G T F;
  in map (mk_prove mode) specs end;


fun is_modifies_clause t =
    exists_subterm (fn (Const (@{const_name Hoare.meq},_)) => true| _ => false)
           (#3 (dest_hoare (Logic.strip_assums_concl t)))
    handle (TERM _) => false;
val is_spec_clause = not o is_modifies_clause;


(* e.g: Intg => the_Intg
        lift Intg => lift the_Intg
        map Ingt => map the_Intg
        Hp o lift Intg => lift the_Intg o the_Hp
*)
fun swap_constr_destr f (t as (Const (@{const_name Fun.id},_))) = t
  | swap_constr_destr f  (t as (Const (c,Type ("fun",[T,valT])))) =
     (Const (f c, Type ("fun",[valT,T]))
      handle Empty => raise TERM ("Hoare.swap_constr_destr",[t]))
  | swap_constr_destr f (Const ("StateFun.map_fun",Type ("fun",   (* FIXME unknown "StateFun.map_fun" !? *)
                                             [Type ("fun",[T,valT]),
                                              Type ("fun",[Type ("fun",[xT,T']),
                                                           Type ("fun",[xT',valT'])])]))$g) =
      Const ("StateFun.map_fun",Type("fun",[Type ("fun",[valT,T]),
                                         Type ("fun",[Type ("fun",[xT,valT']),
                                                      Type ("fun",[xT',T'])])]))$
        swap_constr_destr f g
  | swap_constr_destr f (Const (@{const_name Fun.comp},Type ("fun",
                                       [Type ("fun",[bT',cT]),
                                        Type ("fun",[Type ("fun",[aT ,bT]),
                                                     Type ("fun",[aT',cT'])])]))$h$g) =
     let
       val h'=swap_constr_destr f h;
       val g'=swap_constr_destr f g;
     in Const (@{const_name Fun.comp},Type ("fun",
                                       [Type ("fun",[bT,aT]),
                                        Type ("fun",[Type ("fun",[cT,bT']),
                                                     Type ("fun",[cT',aT'])])]))$g'$h'
     end
  | swap_constr_destr f (Const (@{const_name List.map},Type ("fun",
                                         [Type ("fun",[aT,bT]),
                                          Type ("fun",[asT,bsT])]))$g) =
     (Const (@{const_name List.map},Type ("fun",
                          [Type ("fun",[bT,aT]),
                           Type ("fun",[bsT,asT])]))$swap_constr_destr f g)
  | swap_constr_destr f t = raise TERM ("Hoare.swap_constr_destr",[t]);

(* FIXME: unused? *)
val destr_to_constr =
    let
      fun convert c =
        let
          val (path,base) = split_last (Long_Name.explode c);
        in Long_Name.implode (path @ ["val",unprefix "the_" base]) end;
    in  swap_constr_destr convert end;

fun gen_call_tac cont_tac mode cmode state_kind state_space ctxt asms spec_sfx
                 pname return has_args _ =
  let
    val thy = Proof_Context.theory_of ctxt;
    val pname' = unsuffix proc_deco pname;
    val spec = (case AList.lookup (op =) asms pname of
                 SOME s => SOME s
               | NONE =>  try (Proof_Context.get_thm ctxt) (suffix spec_sfx pname'));

    fun auxvars_for p t =
         (case first_subterm_dest (try dest_call) t of
           SOME (vars,(_,p',_,_,m,_)) => (if m=Static andalso
                                           p=(dest_string' p')
                                        then SOME vars
                                        else NONE)
          | NONE => NONE);

    fun get_auxvars_for p t =
          (case (map_filter ((auxvars_for p) o snd) (max_subterms_dest tap_UN t)) of
            (vars::_) => vars
           | _ => []);


    fun spec_tac augment_rule augment_emptyFaults _ spec i =
         let
           val spec' = augment_emptyFaults OF [spec]
                       handle THM _ => spec;
         in
           EVERY [resolve_tac ctxt [augment_rule] i,
                  resolve_tac ctxt [spec'] (i+1),
                  TRY (resolve_tac ctxt [subset_refl, @{thm Set.empty_subsetI}, @{thm Set.Un_upper1}, @{thm Set.Un_upper2}] i)]
         end;

    fun check_spec name P thm =
         (case try dest_hoare (Thm.concl_of thm) of
               SOME spc => (case try dest_call (#2 spc) of
                             SOME (_,p,_,_,m,_) => if proc_name m p = name andalso
                                                    P (Thm.concl_of thm)
                                                 then SOME (#5 spc,thm)
                                                 else NONE
                            | _ => NONE)
             | _ => NONE)

    fun find_dyn_specs name P thms = map_filter (check_spec name P) thms;

    fun get_spec name P thms =
         case find_dyn_specs name P thms of
          (spec_mode,spec)::_ => SOME (spec_mode,spec)
         | _ => NONE;


    fun solve_spec augment_rule _ augment_emptyFaults mode _ (SOME spec_mode) (SOME spec) i=
        if mode=Partial andalso spec_mode=Total
        then resolve_tac ctxt [@{thm HoareTotal.hoaret_to_hoarep'}] i THEN spec_tac augment_rule augment_emptyFaults mode spec i
        else if mode=spec_mode then spec_tac augment_rule augment_emptyFaults mode spec i
              else error("vcg: cannot use a partial correctness specification of "
                          ^ pname' ^ " for a total correctness proof")
      | solve_spec _ asmUN_rule _ mode Static _ _ i =(* try to infer spec out of context *)
         EVERY[trace_tac ctxt "inferring specification from hoare context1",
               resolve_tac ctxt [asmUN_rule] i,
               DEPTH_SOLVE_1 (resolve_tac ctxt [subset_refl,refl] i ORELSE
                ((resolve_tac ctxt [@{thm Hoare.subset_unI1}] i APPEND resolve_tac ctxt [@{thm Hoare.subset_unI2}] i)
                 ORELSE
                 (resolve_tac ctxt [@{thm Hoare.subset_singleton_insert1}] i
                  APPEND resolve_tac ctxt [@{thm Hoare.subset_singleton_insert2}] i)))
               ORELSE error_tac ("vcg: cannot infer specification of "
                                   ^ pname' ^ " from context")
               (* if tactic for DEPTH_SOLVE_1 would create new subgoals,
                  use SELECT_GOAL and DEPTH_SOLVE *)
              ]

      | solve_spec augment_rule asmUN_rule augment_emptyFaults mode Parameter _ _ i =
          (* try to infer spec out of assumptions *)
         let
             fun tac thms =
              (case (find_dyn_specs pname is_spec_clause thms) of
                (spec_mode,spec)::_
                 => solve_spec augment_rule asmUN_rule augment_emptyFaults mode Parameter
                       (SOME spec_mode) (SOME spec) 1
               | _ => all_tac)
         in Subgoal.FOCUS (tac o #prems) ctxt i end

    val strip_spec_vars = strip_qnt_vars @{const_name All} o HOLogic.dest_Trueprop;

    fun apply_call_tac ctxt pname mode cmode spec_mode spec_goal is_abr
                       spec (subgoal,i) =
      let
        val spec_vars = map fst
             (case spec of
                SOME sp => (strip_spec_vars (Thm.concl_of sp))
              | NONE => (case try (dest_hoare) subgoal of
                           SOME (_,_,_,_,_,_,Theta,_) => get_auxvars_for pname Theta
                          | _ => []));

        fun get_call_rule Static mode is_abr  =
            if is_abr then Proc mode else ProcNoAbr mode
          | get_call_rule Parameter mode is_abr =
                if is_abr then DynProcProcPar mode else DynProcProcParNoAbr mode;

        val [call_rule,augment_ctxt_rule,asmUN_rule, augment_emptyFaults] =
                adapt_aux_var ctxt true spec_vars
                  (map get_aux_tvar
                    [get_call_rule cmode mode is_abr,
                     AugmentContext mode,
                     AsmUN mode,
                     AugmentEmptyFaults mode]);

      in EVERY [resolve_tac ctxt [call_rule] i,
                trace_tac ctxt "call_tac -- basic_tac -- solving spec",
                solve_spec augment_ctxt_rule asmUN_rule augment_emptyFaults
                           mode cmode spec_mode spec spec_goal]
      end;

    fun basic_tac spec i =
        let
           val msg ="Theorem " ^pname'^spec_sfx ^
                    " is no proper specification for procedure " ^pname'^
                     "; trying to infer specification from hoare context";
           fun spec' s mode abr =
                if is_modifies_clause (Thm.concl_of s)
                then if abr then (TrivPost mode) OF [s] else (TrivPostNoAbr mode) OF [s]
                else s;

           val (is_abr,spec_mode,spec,spec_has_args) =
                                          (* is there a proper specification fact? *)
               case spec of NONE => (true,NONE,NONE,false)
               | SOME s
                 => case try dest_hoare (Thm.concl_of s) of
                      NONE => (warning msg;(true,NONE,NONE,false))
                    | SOME (_,c,Q,spec_abr,spec_mode,_,_,_)
                      => case try dest_call c of
                           NONE => (warning msg;(true,NONE,NONE,false))
                         | SOME (_,p,_,_,m,spec_has_args)
                           => if proc_name m p = pname
                              then if (mode=Total andalso spec_mode=Partial)
                                   then (warning msg;(true,NONE,NONE,false))
                                   else if is_empty_set spec_abr then
                                            (false,SOME spec_mode,
                                              SOME (spec' s spec_mode false),spec_has_args)
                                        else (true,SOME spec_mode,
                                                 SOME (spec' s spec_mode true),spec_has_args)
                              else (warning msg;(true,NONE,NONE,false));

           val () = if spec_has_args
                    then error "procedure call in specification must be parameterless!"
                    else ();

           val spec_goal = i+2;
        in
           EVERY[trace_tac ctxt "call_tac -- basic_tac -- START --",
                 SUBGOAL
                   (apply_call_tac ctxt pname mode cmode spec_mode spec_goal is_abr spec) i,
                 resolve_tac ctxt [allI] (i+1),
                 resolve_tac ctxt [allI] (i+1),
                 cont_tac (i+1),
                 trace_tac ctxt "call_tac -- basic_tac -- simplify",
                 conseq_simp_tac ctxt state_kind [@{thm StateSpace.upd_globals_def}] i,
                 trace_tac ctxt "call_tac -- basic_tac -- STOP --"]
        end;

    fun get_modifies (Const (@{const_name Collect},_) $ Abs (_,_,m)) = m
      | get_modifies t =  raise TERM ("gen_call_tac.get_modifies",[t]);

    fun get_updates (Abs (_,_,t)) = get_updates t
      | get_updates (Const (@{const_name Hoare.mex},_) $ t) = get_updates t
      | get_updates (Const (@{const_name Hoare.meq},T) $ _ $ upd) = (T,upd)
      | get_updates t = raise TERM ("gen_call_tac.get_updates",[t]);



    (* return has the form: %s t. s(|globals:=globals t,...|)
     * should be translated to %s t. s(|globals := globals s(|m := m (globals t),...|),...|)
     * for all m in the modifies list.
     *)
     fun mk_subst gT meqT =
       fst (Sign.typ_unify thy (gT,domain_type meqT) (Vartab.empty,0));

     fun mk_selR subst gT (upd,uT) =
       let val vT = range_type (hd (binder_types uT));
       in Const (unsuffix Record.updateN upd,gT --> (Envir.norm_type subst vT)) end;

     (* lookup:: "('v => 'a) => 'n => ('n => 'v) => 'a"
      * update:: "('v => 'a) => ('a => 'v) => 'n => ('a => 'a) => ('n => 'v) => ('n => 'v)"
      *)
     fun mk_selF subst uT d n =
       let
          val vT_a::a_vT::nT::aT_aT::n_vT::_ = binder_types uT;
          val lT = (Envir.norm_type subst (vT_a --> nT --> n_vT --> (domain_type aT_aT)));
          val d' = map_types (Envir.norm_type subst) d;
       in Const (@{const_name StateFun.lookup},lT)$d'$n
       end;

     fun mk_rupdR subst gT (upd,uT) =
       let val [vT,_] = binder_types uT
       in Const (upd,(Envir.norm_type subst vT) --> gT --> gT) end;


     fun K_fun kn uT =
         let val T=range_type (hd (binder_types uT)) in Const (kn,T --> T --> T) end;

     fun K_rec uT t =
         let val T=range_type (hd (binder_types uT))
         in Abs ("_", T, incr_boundvars 1 t) end;

     fun mk_supdF subst uT d c n =
       let
         val uT' = Envir.norm_type subst uT;
         val c' = map_types (Envir.norm_type subst) c;
         val d' = map_types (Envir.norm_type subst) d;
       in Const (@{const_name StateFun.update},uT')$d'$c'$n end;

     fun modify_updatesR subst gT glob ((Const (upd,uT))$_$(Const _$Z)) =
             mk_rupdR subst gT (upd,uT)$
               (K_rec uT (mk_selR subst gT (upd,uT)$(glob$Bound 0)))$(glob$Bound 1)
       | modify_updatesR subst gT glob ((Const (upd,uT))$_$s) =
             mk_rupdR subst gT (upd,uT)$
               (K_rec uT (mk_selR subst gT (upd,uT)$(glob$Bound 0)))$
               modify_updatesR subst gT glob s
       | modify_updatesR subst gT glob ((_$Z)) = (glob$Bound 1) (* may_not_modify *)
       | modify_updatesR _ _ _ t = raise TERM ("gen_call_tac.modify_updatesR",[t]);

     fun modify_updatesF subst _ glob
          (Const (@{const_name StateFun.update},uT)$d$c$n$_$(Const globs$Z)) =
             mk_supdF subst uT d c n$
               (K_fun KNF uT$(mk_selF subst uT d n$(glob$Bound 0)))$(glob$Bound 1)
       | modify_updatesF subst gT glob (Const (@{const_name StateFun.update},uT)$d$c$n$_$s) =
             mk_supdF subst uT d c n$
               (K_fun KNF uT$(mk_selF subst uT d n$(glob$Bound 0)))$modify_updatesF subst gT glob s
       | modify_updatesF subst _ glob ((globs$Z)) = (glob$Bound 1) (* may_not_modify *)
       | modify_updatesF _ _ _ t = raise TERM ("gen_call_tac.modify_updatesF",[t]);

     fun modify_updates Record = modify_updatesR
       | modify_updates _ = modify_updatesF


     fun globalsT (Const (gupd,T)) = domain_type (hd (binder_types T))
       | globalsT t = raise TERM ("gen_call_tac.globalsT",[t]);


     fun mk_upd meqT mods (gupd$(Abs (dmy,dmyT,(glob$Bound 1)))$Bound 1) =
       let val gT = (globalsT gupd);
           val subst = mk_subst gT meqT;
       in (gupd$(Abs (dmy,dmyT,incr_boundvars 1
                   (modify_updates state_kind subst gT glob mods)))$Bound 1) end
       | mk_upd meqT mods (upd$v$s) = upd$v$mk_upd meqT mods s
       | mk_upd _ _ t = raise TERM ("gen_call_tac.mk_upd",[t]);

     fun modify_return (meqT,mods) (Abs (s,T,Abs (t,U,upd))) =
           (Abs (s,T,Abs (t,U,mk_upd meqT mods upd)))
       | modify_return _ t = raise TERM ("get_call_tac.modify_return",[t]);

     fun modify_tac spec modifies_thm i =
       try (fn () =>
        let
          val (_,call,modif_spec_nrm,modif_spec_abr,modif_spec_mode,G,Theta,_) =
                dest_hoare (Thm.concl_of modifies_thm);
          val is_abr = not (is_empty_set modif_spec_abr);
          val emptyTheta = is_empty_set Theta;
          (*val emptyFaults = is_empty_set F;*)
          val spec_has_args = #6 (dest_call call);
          val () = if spec_has_args
              then error "procedure call in modifies-specification must be parameterless!"
              else ();
          val (mxprem,ModRet) = (case cmode of
                 Static =>
                  (8,if is_abr
                     then if emptyTheta then (ProcModifyReturn mode)
                          else (ProcModifyReturnSameFaults mode)
                     else if emptyTheta then (ProcModifyReturnNoAbr mode)
                          else (ProcModifyReturnNoAbrSameFaults mode))
               | Parameter =>
                  (9,if is_abr
                     then if emptyTheta then (ProcProcParModifyReturn mode)
                          else (ProcProcParModifyReturnSameFaults mode)
                     else if emptyTheta then (ProcProcParModifyReturnNoAbr mode)
                          else (ProcProcParModifyReturnNoAbrSameFaults mode)));

          val to_prove_prem = (case cmode of Static => 0 | Parameter => 1);
          val spec_goal = if is_abr then i + mxprem - 5 else i + mxprem - 6

          val mods_nrm = modif_spec_nrm |> get_modifies |> get_updates;
          val return' = modify_return mods_nrm return;
(*
          val return' = if is_abr
                        then let val mods_abr =
                                   modif_spec_abr |> get_modifies |> get_updates;
                             in modify_return mods_abr return end
                        else return;*)

          val cret = Thm.cterm_of ctxt return';
          val (_,_,return'_var,_,_,_) = nth (Thm.prems_of ModRet) to_prove_prem
                                                  |> dest_hoare |> #2 |> dest_call;

          val ModRet' = infer_instantiate ctxt [(#1 (dest_Var return'_var), cret)] ModRet;
          val modifies_thm_partial = if modif_spec_mode = Total
                                     then @{thm HoareTotal.hoaret_to_hoarep'} OF [modifies_thm] else modifies_thm;

          fun solve_modifies_tac i =
                (clarsimp_tac ((ctxt
                  |> put_claset (claset_of @{theory_context Set})
                  |> put_simpset (simpset_of @{theory_context Set}))
                  addsimps ([@{thm Hoare.mex_def},@{thm Hoare.meq_def},@{thm StateSpace.upd_globals_def}]@K_convs)
                  addsimprocs (state_upd_simproc Record::(state_simprocs state_kind))
                  |> fold Simplifier.add_cong K_congs) i)
                THEN_MAYBE
                EVERY [trace_tac ctxt "modify_tac: splitting record",
                       state_split_simp_tac ctxt [] state_space i];
          val cnt = i + mxprem;

        in
            EVERY[trace_tac ctxt "call_tac -- modifies_tac --",
                  resolve_tac ctxt [ModRet'] i,
                  solve_spec (AugmentContext Partial) (AsmUN Partial)
                     (AugmentEmptyFaults Partial) Partial Static
                     (SOME Partial) (SOME modifies_thm_partial) spec_goal,
                  if is_abr then
                   EVERY [trace_tac ctxt "call_tac -- Solving abrupt modifies --",
                          solve_modifies_tac (cnt - 6)]
                  else all_tac,
                  trace_tac ctxt "call_tac -- Solving Modifies --",
                  solve_modifies_tac (cnt - 7),
                  basic_tac spec (cnt - 8),
                  if cmode = Parameter
                  then EVERY [resolve_tac ctxt [subset_refl] (cnt - 8),
                              simp_tac (put_simpset HOL_basic_ss ctxt
                                addsimps (@{thm Hoare.CollectInt_iff} :: @{thms simp_thms})) 1]
                  else all_tac]
        end) ()
      |> (fn SOME res => res
           | NONE => raise TERM ("get_call_tac.modify_tac: no proper modifies spec", []));

  fun specs_of_assms_tac thms =
       (case get_spec pname is_spec_clause thms of
          SOME (_,spec) => (case get_spec pname is_modifies_clause thms of
                              SOME (_,modifies_thm) => modify_tac (SOME spec) modifies_thm 1
                            | NONE => basic_tac (SOME spec) 1)
        | NONE => (warning ("no proper specification for procedure " ^pname^
                           " in assumptions"); all_tac));

  val test_modify_in_ctxt_tac =
    let val mname = (suffix modifysfx pname');
        val mspec = (case try (Proof_Context.get_thm ctxt) mname of
                      SOME s => SOME s
                     | NONE => (case AList.lookup (op =) asms pname of
                                 SOME s => if is_modifies_clause (Thm.concl_of s)
                                           then SOME s else NONE
                                | NONE => NONE));

    in (case mspec of
           NONE => basic_tac spec
         | SOME modifies_thm =>
             (case check_spec pname is_modifies_clause modifies_thm of
                SOME _ => modify_tac spec modifies_thm
              | NONE => (warning ("ignoring theorem " ^ (suffix modifysfx pname') ^
                                  "; no proper modifies specification for procedure "^pname');
                         basic_tac spec)))
    end;

  fun inline_bdy_tac has_args i =
    (case try (Proof_Context.get_thm ctxt) (suffix bodyP pname') of
       NONE => no_tac
     | SOME impl =>
        (case try (Proof_Context.get_thm ctxt) (suffix (body_def_sfx^"_def") pname') of
           NONE => no_tac
         | SOME bdy =>
            (tracing ("No specification found for procedure \"" ^ pname' ^
                                "\". Inlining procedure!");
             if has_args then
                EVERY [trace_tac ctxt "inline_bdy_tac args",
                       resolve_tac ctxt [CallBody mode] i,
                       resolve_tac ctxt [impl] (i+3),
                       resolve_tac ctxt [allI] (i+2),
                       resolve_tac ctxt [allI] (i+2),
                       in_assertion_simp_tac ctxt state_kind [] (i+2),
                       cont_tac (i+2),
                       resolve_tac ctxt [allI] (i+1),in_assertion_simp_tac ctxt state_kind [bdy] (i+1),
                       cont_tac (i+1),
                       in_assertion_simp_tac ctxt state_kind [@{thm StateSpace.upd_globals_def}] i]
              else EVERY [trace_tac ctxt "inline_bdy_tac no args",
                          resolve_tac ctxt [ProcBody mode] i,
                          resolve_tac ctxt [impl] (i+2),
                          simp_tac (put_simpset HOL_basic_ss ctxt addsimps [bdy]) (i+1),
                          cont_tac (i+1)])));

  in
    (case cmode of
       Static => if get_recursive pname ctxt = SOME false
                 andalso is_none spec
                 then inline_bdy_tac has_args
                 else test_modify_in_ctxt_tac
     | Parameter =>
         (case spec of
            NONE => (tracing "no spec found!"; Subgoal.FOCUS (specs_of_assms_tac o #prems) ctxt)
          | SOME spec =>
              (tracing "found spec!"; case check_spec pname is_spec_clause spec of
                 SOME _ => test_modify_in_ctxt_tac
               | NONE => (warning ("ignoring theorem " ^ (suffix spec_sfx pname') ^
                          "; no proper specification for procedure " ^pname');
                          Subgoal.FOCUS (specs_of_assms_tac o #prems) ctxt))))
  end;

fun call_tac cont_tac mode state_kind state_space ctxt asms spec_sfx t =
  let
     val (_,c,_,_,_,_,_,F) = dest_hoare (Logic.strip_assums_concl t);
     fun gen_tac (_,pname,return,c,cmode,has_args) =
           gen_call_tac cont_tac mode cmode state_kind state_space ctxt asms spec_sfx
                         (proc_name cmode pname) return has_args F;
  in gen_tac (dest_call c) end
  handle TERM _ => K no_tac;

fun solve_in_Faults_tac ctxt i =
    resolve_tac ctxt [UNIV_I, @{thm in_insert_hd}] i
    ORELSE
    SELECT_GOAL (SOLVE (simp_tac (put_simpset (simpset_of @{theory_context Set}) ctxt) 1)) i;

local
fun triv_simp ctxt = merge_assertion_simp_tac ctxt [mem_Collect_eq] THEN'
         simp_tac (put_simpset HOL_basic_ss ctxt addsimps @{thms simp_thms}
           |> fold Simplifier.add_cong [@{thm conj_cong}, @{thm imp_cong}]);
    (* a guarded while produces stupid things, since the guards are
          put at the end of the body and in the invariant (rule WhileAnnoG):
         - guard: g /\ g
         - guarantee: g --> g *)
in
fun guard_tac ctxt strip cont_tac mode (t,i) =
  let
    val (_,c,_,_,_,_,_,F) = dest_hoare (Logic.strip_assums_concl t);
    val (_,_,_,doStrip) = dest_Guard c;
    val guarantees = if strip orelse doStrip
                     then [GuardStrip mode, GuaranteeStrip mode]
                     else [Guarantee mode]

    fun basic_tac i =
          EVERY [resolve_tac ctxt [Guard mode, GuaranteeAsGuard mode] i,
                 trace_tac ctxt "Guard", cont_tac (i+1),
                 triv_simp ctxt i]


    fun guarantee_tac i =
          EVERY [resolve_tac ctxt guarantees i,
                 solve_in_Faults_tac ctxt (i+2),
                 cont_tac (i+1),
                 triv_simp ctxt i]
  in if is_empty_set F then EVERY [trace_tac ctxt "Guard: basic_tac", basic_tac i]
    else EVERY [trace_tac ctxt "Guard: trying guarantee_tac", guarantee_tac i ORELSE basic_tac i]
  end handle TERM _ => no_tac
end;

fun wf_tac ctxt =
  simp_tac (put_simpset HOL_basic_ss ctxt
    addsimps [@{thm Wellfounded.wf_measure},@{thm Wellfounded.wf_lex_prod},@{thm Wfrec.wf_same_fst}, @{thm Hoare.wf_measure_lex_prod},@{thm Wellfounded.wf_inv_image}]);

fun in_rel_simp ctxt =
  simp_tac (put_simpset HOL_basic_ss ctxt
    addsimps [@{thm Hoare.in_measure_iff},@{thm Hoare.in_lex_iff},@{thm Hoare.in_mlex_iff},@{thm Hoare.in_inv_image_iff}, @{thm split_conv}]);

fun while_annotate_tac ctxt inv i st =
  let
    val annotateWhile = Thm.lift_rule (Thm.cprem_of st i) @{thm HoarePartial.reannotateWhileNoGuard};
    val lifted_inv = fold_rev Term.abs (Logic.strip_params (Logic.get_goal (Thm.prop_of st) i)) inv;
    val invVar = (#1 o strip_comb o #3 o dest_whileAnno o #2 o dest_hoare)
                  (List.last (Thm.prems_of annotateWhile));
    val annotate =
      infer_instantiate ctxt [(#1 (dest_Var invVar), Thm.cterm_of ctxt lifted_inv)] annotateWhile;
 in  ((trace_tac ctxt ("annotating While with: " ^ Syntax.string_of_term ctxt lifted_inv ))
       THEN
       compose_tac ctxt (false,annotate,1) i) st
 end;

fun cond_annotate_tac ctxt inv mode (_,i) st =
  let
    val annotateCond = Thm.lift_rule (Thm.cprem_of st i) (CondInv' mode);
    val lifted_inv = fold_rev Term.abs (Logic.strip_params (Logic.get_goal (Thm.prop_of st) i)) inv;
    val invVar = List.last (Thm.prems_of annotateCond) |> dest_hoare |> #3 |> strip_comb |> #1;
    val annotate =
      infer_instantiate ctxt [(#1 (dest_Var invVar), Thm.cterm_of ctxt lifted_inv)] annotateCond;
  in  ((trace_tac ctxt ("annotating Cond with: "^ Syntax.string_of_term ctxt lifted_inv))
       THEN
       compose_tac ctxt (false,annotate,5) i) st
 end;

fun basic_while_tac ctxt state_kind cont_tac tac mode i =
  let
    fun common_tac i =
         EVERY[if mode=Total then wf_tac ctxt (i+3) else all_tac,
               BasicSimpTac ctxt state_kind true [] tac (i+2),
               if mode=Total
               then in_rel_simp ctxt (i+1) THEN (resolve_tac ctxt [allI] (i+1))
               else all_tac,
               cont_tac (i+1)
               ]

    fun basic_tac i =
          EVERY [resolve_tac ctxt [While mode] i,
                 common_tac i]
  in
     EVERY [trace_tac ctxt "basic_while_tac: basic_tac", basic_tac i]
  end;

fun while_tac ctxt state_kind inv cont_tac tac mode t i=
    let
      val basic_tac  = basic_while_tac ctxt state_kind cont_tac tac mode;
    in
        (case inv of
           NONE => basic_tac i
         | SOME I => EVERY [while_annotate_tac ctxt I i, basic_tac i])

    end
    handle TERM _ => no_tac

fun dest_split (Abs (x,T,t)) =
     let val (vs,recomb,bdy) = dest_split t;
     in ((x,T)::vs,fn t' => Abs (x,T,recomb t'),bdy) end
  | dest_split (c as Const (@{const_name case_prod},_)$Abs(x,T,t)) =
     let val (vs,recomb,bdy) = dest_split t;
     in ((x,T)::vs,fn t' => c$Abs (x,T,recomb t'),bdy) end
  | dest_split t = ([],I,t);

fun whileAnnoG_tac ctxt strip_guards mode t i st =
  let
    val (_,c,_,_,_,_,_,F) = dest_hoare (Logic.strip_assums_concl t);
    val (SOME grds,_,I,_,_,fix) = dest_whileAnno c;
    val Rule = if fix then WhileAnnoGFix mode else WhileAnnoG mode;
    fun extract_faults (Const (@{const_name Set.insert}, _) $ t $ _) = [t]
      | extract_faults _ = [];
    fun leave_grd fs (Const (@{const_name Pair}, _) $ f $ g) =
          if member (op =) fs f andalso strip_guards then NONE else SOME g
      | leave_grd fs (Const (@{const_name Language.guaranteeStripPair}, _) $ f $ g) =
          if member (op =) fs f then NONE else SOME g
      | leave_grd fs _ = NONE;
    val (I_vs,I_recomb,I') = dest_split I;
    val grds' = map_filter (leave_grd (extract_faults F)) (HOLogic.dest_list grds);
    val pars = (Logic.strip_params (Logic.get_goal (Thm.prop_of st) i));
    val J = fold_rev Term.abs pars (I_recomb (fold_rev (mk_Int (map snd (pars@I_vs))) grds' I'));
    val WhileG = Thm.lift_rule (Thm.cprem_of st i) Rule;
    val invVar = (fst o strip_comb o #3 o dest_whileAnno o (fn xs => nth xs 1) o snd
      o strip_comb o #2 o dest_hoare) (List.last (Thm.prems_of WhileG));
    val WhileGInst = infer_instantiate ctxt [(#1 (dest_Var invVar), Thm.cterm_of ctxt J)] WhileG;
  in ((trace_tac ctxt ("WhileAnnoG, adding guards to invariant: " ^ Syntax.string_of_term ctxt J))
      THEN compose_tac ctxt (false,WhileGInst,1) i) st
  end
  handle TERM _ => no_tac st
       | Bind   => no_tac st

(* renames bound state variable according to name given in goal,
 * before rule specAnno is applied, and solves sidecondition *)

fun gen_Anno_tac dest rules tac cont_tac ctxt state_kind (t,i) st =
  let
    val vars = (dest o #2 o dest_hoare) (Logic.strip_assums_concl t);
    val rules' = (case (List.filter (not o null) (map dest_splits vars)) of
                    [] => rules
                  |(xs::_) => adapt_aux_var ctxt false (map fst xs) (map get_aux_tvar rules));
  in EVERY [resolve_tac ctxt rules' i,
            tac,
            simp_tac (put_simpset HOL_basic_ss ctxt addsimps ([@{thm split_conv}, refl, @{thm Hoare.triv_All_eq}]@anno_defs)
                      addsimprocs [@{simproc case_prod_beta}]) (i+2),
            simp_tac (put_simpset HOL_basic_ss ctxt addsimps [@{thm split_conv}]) (i+1),
            simp_tac (put_simpset HOL_basic_ss ctxt addsimps [@{thm split_conv}]) i,
            REPEAT (resolve_tac ctxt [allI] (i+1)),
            cont_tac (i+1),
            conseq_simp_tac ctxt state_kind [] i] st
  end
  handle TERM _ => no_tac st;


fun specAnno_tac ctxt state_kind cont_tac mode =
  let
    fun dest_specAnno (Const (@{const_name Language.specAnno},_)$P$c$Q$A) = [P,c,Q,A]
      | dest_specAnno t = raise TERM ("dest_specAnno",[t]);

    val rules = [SpecAnnoNoAbrupt mode,SpecAnno mode];
  in gen_Anno_tac dest_specAnno rules all_tac cont_tac ctxt state_kind end;

fun whileAnnoFix_tac ctxt state_kind cont_tac mode (t,i) =
  let
    fun dest (Const (@{const_name Language.whileAnnoFix},_)$b$I$V$c) = [I,V,c]
      | dest t = raise TERM ("dest_whileAnnoFix",[t]);

    val rules = [WhileAnnoFix mode];
    fun wf_tac' i = EVERY [REPEAT (resolve_tac ctxt [allI] i),
                           simp_tac (put_simpset HOL_basic_ss ctxt addsimps [@{thm split_conv}]) i,
                           wf_tac ctxt i];
    val tac = if mode=Total
              then EVERY [wf_tac' (i+3),in_rel_simp ctxt (i+1)]
              else all_tac
  in gen_Anno_tac dest rules tac cont_tac ctxt state_kind (t,i) end;

fun lemAnno_tac ctxt state_kind mode (t,i) st =
  let

    fun dest_name (Const (x,_)) = x
      | dest_name (Free (x,_)) = x
      | dest_name t = raise TERM ("dest_name",[t]);

    fun dest_lemAnno ctxt (Const (@{const_name Language.lem},_)$n$c) =
      let val x = Long_Name.base_name (dest_name n);
      in
         (case try (Proof_Context.get_thm ctxt) x of
            NONE => error ("No lemma: '" ^ x ^ "' found.")
          | SOME spec => (strip_qnt_vars @{const_name All}
                           (HOLogic.dest_Trueprop (Thm.concl_of spec)),spec))
      end
      | dest_lemAnno _ t = raise TERM ("dest_lemAnno",[t]);

    val (vars,spec) = dest_lemAnno ctxt (#2 (dest_hoare t));
    val rules = [LemAnnoNoAbrupt mode,LemAnno mode];
    val rules' = (case vars of
                    [] => rules
                  | xs => adapt_aux_var ctxt true (map fst xs) (map get_aux_tvar rules));

  in EVERY [resolve_tac ctxt rules' i,
            resolve_tac ctxt [spec] (i+1),
            conseq_simp_tac ctxt state_kind [] i] st
  end
  handle TERM _ => no_tac st;

fun prems_tac ctxt i = TRY (resolve_tac ctxt (Assumption.all_prems_of ctxt) i);



fun mk_proc_assoc thms =
  let
    fun name (_,p,_,_,cmode,_) = proc_name cmode p;
    fun proc_name thm = thm |> Thm.concl_of |> dest_hoare |> #2 |> dest_call |> name;
  in map (fn thm => (proc_name thm,thm)) thms end;


fun mk_hoare_tac cont ctxt mode i (name,tac) =
     EVERY [trace_tac ctxt ("trying: " ^ name),tac cont ctxt mode i];


(* the main hoare tactic *)
fun HoareTac annotate_inv exspecs
             strip_guards mode state_kind state_space
             spec_sfx ctxt tac st =
 let
     val (P,c,Q,A,_,G,T,F) = dest_hoare (Logic.strip_assums_concl
                                       (Logic.get_goal (Thm.prop_of st) 1));
     val wp_tacs = #wp_tacs (get_data ctxt);
     val hoare_tacs = #hoare_tacs (get_data ctxt);
     val params = (strip_vars (Logic.get_goal (Thm.prop_of st) 1));
     val Inv = (if annotate_inv
                then (* Take the postcondition of the triple as invariant for all *)
                     (* while loops (makes sense for the modifies clause)         *)
                     SOME Q
                else NONE);
     val exspecthms = map (Proof_Context.get_thm ctxt) exspecs;
     val asms =
       try (fn () =>
         mk_proc_assoc (gen_context_thms ctxt mode params G T F @ exspecthms)) ()
       |> the_default [];

     fun while_annoG_tac (t,i) =
           whileAnnoG_tac ctxt (annotate_inv orelse strip_guards) mode t i;
     fun WlpTac tac i = (* WlpTac does not end with subset_refl *)
         FIRST
         ([EVERY [resolve_tac ctxt [Seq mode] i,trace_tac ctxt "Seq",HoareRuleTac tac false (i+1)],
          EVERY [resolve_tac ctxt [Catch mode] i,trace_tac ctxt "Catch",HoareRuleTac tac false (i+1)],
          EVERY [resolve_tac ctxt [CondCatch mode] i,trace_tac ctxt "CondCatch",HoareRuleTac tac false (i+1)],
          EVERY [resolve_tac ctxt [BSeq mode] i,trace_tac ctxt "BSeq",HoareRuleTac tac false (i+1)],
          EVERY [resolve_tac ctxt [FCall mode] i,trace_tac ctxt "FCall"],
          EVERY [resolve_tac ctxt [GuardsNil mode] i,trace_tac ctxt "GuardsNil"],
          EVERY [resolve_tac ctxt [GuardsConsGuaranteeStrip mode] i,
                 trace_tac ctxt "GuardsConsGuaranteeStrip"],
          EVERY [resolve_tac ctxt [GuardsCons mode] i,trace_tac ctxt "GuardsCons"],
          EVERY [SUBGOAL while_annoG_tac i]
          ]
         @
         map (mk_hoare_tac (HoareRuleTac tac) ctxt mode i) wp_tacs)

     and HoareRuleTac tac pre_cond i st =
         let fun call (t,i) = call_tac (HoareRuleTac tac false)
                                mode state_kind state_space ctxt asms spec_sfx t i

             fun cond_tac i =  if annotate_inv andalso Config.get ctxt use_cond_inv_modifies then
                                 EVERY[SUBGOAL (cond_annotate_tac ctxt (the Inv) mode) i,
                                       HoareRuleTac tac false (i+4),
                                       HoareRuleTac tac false (i+3),
                                       BasicSimpTac ctxt state_kind true [] tac (i+2),
                                       BasicSimpTac ctxt state_kind true [] tac (i+1)
                                      ]
                               else
                                 EVERY[resolve_tac ctxt [Cond mode] i,trace_tac ctxt "Cond",
                                       HoareRuleTac tac false (i+2),
                                       HoareRuleTac tac false (i+1)];
             fun switch_tac i = EVERY[resolve_tac ctxt [SwitchNil mode] i, trace_tac ctxt "SwitchNil"]
                                ORELSE
                                EVERY[resolve_tac ctxt [SwitchCons mode] i,trace_tac ctxt "SwitchCons",
                                     HoareRuleTac tac false (i+2),
                                     HoareRuleTac tac false (i+1)];
            fun while_tac' (t,i) = while_tac ctxt state_kind Inv
                                      (HoareRuleTac tac true) tac mode t i;
         in st |>
           ( (WlpTac tac i THEN HoareRuleTac tac pre_cond i)
             ORELSE
             (FIRST([EVERY[resolve_tac ctxt [Skip mode] i,trace_tac ctxt "Skip"],
                    EVERY[resolve_tac ctxt [BasicCond mode] i, trace_tac ctxt "BasicCond",
                          assertion_simp_tac ctxt state_kind [] i],
                    (resolve_tac ctxt [Basic mode] i THEN trace_tac ctxt "Basic")
                        THEN_MAYBE (assertion_simp_tac ctxt state_kind [] i),
                          (* we don't really need simplificaton here. The question is
                             if it is better to simplify the assertion after each Basic step,
                             so that intermediate assertions stay "small", or if we just
                             accumulate the raw assertions and leave the simplification to
                             the final BasicSimpTac *)
                    EVERY[resolve_tac ctxt [Throw mode] i, trace_tac ctxt "Throw"],
                    (resolve_tac ctxt [Raise mode] i THEN trace_tac ctxt "Raise")
                        THEN_MAYBE (assertion_string_eq_simp_tac ctxt state_kind [] i),
                    cond_tac i,
                    switch_tac i,
                    EVERY[resolve_tac ctxt [Block mode] i, trace_tac ctxt "Block",
                          resolve_tac ctxt [allI] (i+2),
                          resolve_tac ctxt [allI] (i+2),
                          HoareRuleTac tac false (i+2),
                          resolve_tac ctxt [allI] (i+1),
                          in_assertion_simp_tac ctxt state_kind [] (i+1),
                          HoareRuleTac tac false (i+1)],
                    SUBGOAL while_tac' i,
                    SUBGOAL (guard_tac ctxt (annotate_inv orelse strip_guards)
                                       (HoareRuleTac tac false) mode) i,
                    EVERY[SUBGOAL (specAnno_tac ctxt state_kind
                                     (HoareRuleTac tac true) mode) i],
                    EVERY[SUBGOAL (whileAnnoFix_tac ctxt state_kind
                                     (HoareRuleTac tac true) mode) i],
                    EVERY[resolve_tac ctxt [SpecIf mode] i, trace_tac ctxt "SpecIf",
                          assertion_simp_tac ctxt state_kind [] i],
                    (resolve_tac ctxt [Spec mode] i THEN trace_tac ctxt "Spec")
                        THEN_MAYBE (assertion_simp_tac ctxt state_kind [@{thm split_conv}] i),
                    EVERY[resolve_tac ctxt [BindR mode] i, trace_tac ctxt "Bind",
                      resolve_tac ctxt [allI] (i+1),
                      HoareRuleTac tac false (i+1)],
                    EVERY[resolve_tac ctxt [DynCom mode] i, trace_tac ctxt "DynCom"],
                    EVERY[trace_tac ctxt "calling call_tac",SUBGOAL call i],
                    EVERY[trace_tac ctxt "LemmaAnno",SUBGOAL (lemAnno_tac ctxt state_kind mode) i]]
                    @
                    map (mk_hoare_tac (HoareRuleTac tac) ctxt mode i) hoare_tacs)
              THEN (if pre_cond
                    then EVERY [trace_tac ctxt "pre_cond",
                                TRY (BasicSimpTac ctxt state_kind true [] tac i),
                                             (* FIXME: Do we need TRY *)
                                trace_tac ctxt "after BasicSimpTac"]
                    else (resolve_tac ctxt [subset_refl] i))))
         end;
 in ((K (EVERY [REPEAT (resolve_tac ctxt [allI] 1), HoareRuleTac tac true 1]))
     THEN_ALL_NEW (prems_tac ctxt)) 1 st
      (*Procedure specifications may have an locale assumption as premise. These are
        accumulated by the vcg and are be solved afterward by prems_tac
      *)
 end;

fun prefer_tac i = (Tactic.defer_tac i THEN PRIMITIVE (Thm.permute_prems 0 ~1));

fun HoareStepTac strip_guards mode state_kind state_space spec_sfx ctxt tac st =
 let
     val asms =
       try (fn () =>
         let val (_,_,_,_,_,G,T,F) = dest_hoare (Logic.strip_assums_concl
                                                (Logic.get_goal (Thm.prop_of st) 1));
             val params = (strip_vars (Logic.get_goal (Thm.prop_of st) 1));
         in mk_proc_assoc (gen_context_thms ctxt mode params G T F)
         end) ()
       |> the_default [];

     fun result_tac i = TRY (EVERY [resolve_tac ctxt [Basic mode] i,
         resolve_tac ctxt [subset_refl] i]);
     fun call (t,i) = call_tac result_tac mode state_kind state_space ctxt asms spec_sfx t i

     fun final_simp_tac i =
          EVERY [full_simp_tac (put_simpset HOL_basic_ss ctxt addsimps [mem_Collect_eq]) i,
                 REPEAT (eresolve_tac ctxt [conjE] i),
                 TRY (hyp_subst_tac_thin true ctxt i),
                 BasicSimpTac ctxt state_kind true [] tac i]
     fun while_annoG_tac (t,i) = whileAnnoG_tac ctxt strip_guards mode t i;

 in st |>
    (REPEAT (resolve_tac ctxt [allI] 1)
     THEN
     FIRST [resolve_tac ctxt [subset_refl] 1,
           EVERY[resolve_tac ctxt [Skip mode] 1,TRY (BasicSimpTac ctxt state_kind false [] tac 1)],
           EVERY[resolve_tac ctxt [BasicCond mode] 1,trace_tac ctxt "BasicCond",
                 TRY (BasicSimpTac ctxt state_kind false [] tac 1)],
           EVERY[resolve_tac ctxt [Basic mode] 1,TRY (BasicSimpTac ctxt state_kind false [] tac 1)],
           EVERY[resolve_tac ctxt [Throw mode] 1,TRY (BasicSimpTac ctxt state_kind false [] tac 1)],
           EVERY[resolve_tac ctxt [Raise mode] 1,TRY (assertion_string_eq_simp_tac ctxt state_kind [] 1)],
           resolve_tac ctxt [SeqSwap mode] 1
             THEN_MAYBE HoareStepTac strip_guards mode state_kind state_space spec_sfx
                          ctxt tac,
           EVERY[resolve_tac ctxt [BSeq mode] 1,
                 prefer_tac 2
                 THEN_MAYBE HoareStepTac strip_guards mode state_kind state_space spec_sfx
                              ctxt tac],
           resolve_tac ctxt [CondSwap mode] 1,
           resolve_tac ctxt [SwitchNil mode] 1,
           resolve_tac ctxt [SwitchCons mode] 1,
           EVERY [SUBGOAL while_annoG_tac 1],
           EVERY[resolve_tac ctxt [While mode] 1,
                 if mode=Total then wf_tac ctxt 4 else all_tac,
                 BasicSimpTac ctxt state_kind false [] tac 3,
                 if mode=Total then in_rel_simp ctxt 2 THEN (resolve_tac ctxt [allI] 2) else all_tac,
                 BasicSimpTac ctxt state_kind false [] tac 1],
           resolve_tac ctxt [CatchSwap mode] 1,
           resolve_tac ctxt [CondCatchSwap mode] 1,
           EVERY[resolve_tac ctxt [BlockSwap mode] 1, resolve_tac ctxt [allI] 1,
              resolve_tac ctxt [allI] 1,
              resolve_tac ctxt [allI] 2,
              BasicSimpTac ctxt state_kind false [] tac 2],
           resolve_tac ctxt [GuardsNil mode] 1,
           resolve_tac ctxt [GuardsConsGuaranteeStrip mode] 1,
           resolve_tac ctxt [GuardsCons mode] 1,
           SUBGOAL (guard_tac ctxt strip_guards (fn i => all_tac) mode) 1,
           EVERY[SUBGOAL (specAnno_tac ctxt state_kind (K all_tac) mode) 1],
           EVERY[SUBGOAL (whileAnnoFix_tac ctxt state_kind (K all_tac) mode) 1],
           EVERY[resolve_tac ctxt [SpecIf mode] 1,trace_tac ctxt "SpecIf",
                 TRY (BasicSimpTac ctxt state_kind false [] tac 1)],
           EVERY[resolve_tac ctxt [Spec mode] 1,
                 TRY (BasicSimpTac ctxt state_kind false [@{thm split_conv}] tac 1)],
           EVERY[resolve_tac ctxt [BindR mode] 1,
             resolve_tac ctxt [allI] 2, prefer_tac 2],
           EVERY[resolve_tac ctxt [FCall mode] 1],
           EVERY[resolve_tac ctxt [DynCom mode] 1],
           EVERY[SUBGOAL call 1, BasicSimpTac ctxt state_kind false [] tac 1],
           EVERY[SUBGOAL (lemAnno_tac ctxt state_kind mode) 1,
                 BasicSimpTac ctxt state_kind false [] tac 1],
           final_simp_tac 1
           ])
 end;

(*****************************************************************************)
(**  Generalise verification condition                                      **)
(*****************************************************************************)

structure RecordSplitState : SPLIT_STATE =
struct

val globals = @{const_name StateSpace.state.globals};

fun isState (Const _$Abs (s,T,t)) =
      (case (state_hierarchy T) of
        ((n,_)::_) => n = "StateSpace.state.state" andalso
          is_none (try dest_hoare_raw (strip_qnt_body @{const_name All} t))
      | _ => false)
  | isState _ = false;

fun isFreeState (Free (_,T)) =
     (case (state_hierarchy T) of
        ((n,_)::_) => n = "StateSpace.state.state"
      | _ => false)
  | isFreeState _ = false;

val abs_state = Option.map snd o first_subterm isFreeState;


fun sel_eq (Const (x,_)$_) y = (x=y)
  | sel_eq t y = raise TERM ("RecordSplitState.sel_eq",[t]);

val sel_idx = idx sel_eq;

fun bound xs (t as (Const (x,_)$_)) =
     let val i = sel_idx xs x
     in if i < 0 then (length xs, xs@[t]) else (i,xs) end
  | bound xs t = raise TERM ("RecordSplitState.bound",[t]);

fun abs_var _ (Const (x,T)$_) =
     (remdeco' (Long_Name.base_name x),range_type T)
  | abs_var _ t = raise TERM ("RecordSplitState.abs_var",[t]);

fun fld_eq (x, _) y = (x = y)

fun fld_idx xs x = idx fld_eq xs x;

fun sort_vars ctxt T vars =
  let
    val thy = Proof_Context.theory_of ctxt;
    val (flds,_) = Record.get_recT_fields thy T;
    val gT = the (AList.lookup (fn (x:string,y) => x=y) flds globals);
    val (gflds,_) = (Record.get_recT_fields thy gT
                     handle TYPE _ => ([],("",dummyT)));

    fun compare (Const _$Free _, Const _$(Const _$Free _)) = GREATER
      | compare (Const (s1,_)$Free _, Const (s2,_)$Free _) =
           int_ord (fld_idx flds s1, fld_idx flds s2)
      | compare (Const (s1,_)$(Const _$Free _), Const (s2,_)$(Const _$Free _)) =
           int_ord (fld_idx gflds s1, fld_idx gflds s2)
      | compare _ = LESS;
  in sort (rev_order o compare) vars end;


fun fold_state_prop loc glob app abs other inc s res (t as (Const (sel,_)$Free (s',_))) =
         if s'=s
         then if is_state_var sel
              then loc inc res t
              else raise TERM ("RecordSplitState.fold_state_prop",[t])
         else other res t
  | fold_state_prop loc glob app abs other inc s res
      (t as ((t1 as (Const (sel,_)))$(t2 as (Const (glb,_)$Free (s',_))))) =
         if s'=s andalso is_state_var sel andalso (glb=globals)
         then glob inc res t
         else let val res1 = fold_state_prop loc glob app abs other inc s res t1
                  val res2 = fold_state_prop loc glob app abs other inc s res1 t2
              in app res1 res2
              end
  | fold_state_prop loc glob app abs other inc s res (t as (Free (s',_))) =
         if s'=s then raise TERM ("RecordSplitState.fold_state_prop",[t])
         else other res t
  | fold_state_prop loc glob app abs other inc s res (t1$t2) =
         let val res1 = fold_state_prop loc glob app abs other inc s res t1
             val res2 = fold_state_prop loc glob app abs other inc s res1 t2
         in app res1 res2 end
  | fold_state_prop loc glob app abs other inc s res (Abs (x,T,t)) =
         let val res1 = fold_state_prop loc glob app abs other (inc+1) s res t
         in abs x T res1
         end
  | fold_state_prop loc glob app abs other inc s res t = other res t

fun collect_vars s t =
  let
    fun loc _ vars t  = snd (bound vars t);
    fun glob _ vars t = snd (bound vars t);
    fun app _ vars2 = vars2;
    fun abs _ _ vars = vars;
    fun other vars _ = vars;
  in fold_state_prop loc glob app abs other 0 s [] t end;

fun abstract_vars vars s t =
  let
    fun loc inc _ t  = let val i = fst (bound vars t) in Bound (i+inc) end;
    fun glob inc _ t = let val i = fst (bound vars t) in Bound (i+inc) end;
    fun app t1 t2 = t1$t2;
    fun abs x T t = Abs (x,T,t);
    fun other _ t = t;
    val dummy = Bound 0;
  in fold_state_prop loc glob app abs other 0 s dummy t end;

fun split_state ctxt s T t =
  let
    val vars  = collect_vars s t;
    val vars' = if Config.get ctxt sort_variables then sort_vars ctxt T vars else vars;
  in (abstract_vars vars' s t,rev vars') end;

fun ex_tac ctxt _ st = Record.split_simp_tac ctxt @{thms simp_thms} (K ~1) 1 st;

end;

structure FunSplitState : SPLIT_STATE =
struct

val full_globalsN = @{const_name StateSpace.state.globals};

fun isState (Const _$Abs (s,T,t)) =
      (case (state_hierarchy T) of
        ((n,_)::_) => n = "StateSpace.state.state" andalso
          is_none (try dest_hoare_raw (strip_qnt_body @{const_name All} t))
      | _ => false)
  | isState _ = false;

fun isFreeState (Free (_,T)) =
      (case (state_hierarchy T) of
        ((n,_)::_) => n = "StateSpace.state.state"
      | _ => false)
  | isFreeState _ = false;

val abs_state = Option.map snd o first_subterm isFreeState;

fun comp_name t =
    case try (implode o dest_string) t of
      SOME str => str
    | NONE => (case t of
                 Free (s,_) => s
               | Const (s,_) => s
               | t => raise TERM ("FunSplitState.comp_name",[t]))

fun sel_name (Const _$_$name$_) = comp_name name
  | sel_name t = raise TERM ("FunSplitState.sel_name",[t]);

fun sel_raw_name (Const _$_$name$_) = name
  | sel_raw_name t = raise TERM ("FunSplitState.sel_raw_name",[t]);

fun component_type (Const _$_$_$(sel$_)) = range_type (fastype_of sel)
  | component_type t = raise TERM ("FunSplitState.component_type",[t]);

fun component_name (Const _$_$_$((Const (sel,_)$_))) = sel
  | component_name t = raise TERM ("FunSplitState.component_name",[t]);

fun sel_type (Const _$destr$_$_) = range_type (fastype_of destr)
  | sel_type t = raise TERM ("FunSplitState.sel_type",[t]);

fun sel_destr (Const _$destr$_$_) = destr
  | sel_destr t = raise TERM ("FunSplitState.sel_destr",[t]);

fun sel_eq t y = (sel_name t = y)
  | sel_eq t y = raise TERM ("FunSplitState.sel_eq",[t]);

val sel_idx = idx sel_eq;

fun bound xs t =
     let val i = sel_idx xs (sel_name t)
     in if i < 0 then (length xs, xs@[t]) else (i,xs) end
  | bound xs t = raise TERM ("FunSplitState.bound",[t]);

fun fold_state_prop var app abs other inc s res
      (t as (Const (@{const_name StateFun.lookup},_)$destr$name$(Const _$Free (s',_)))) =
         if s'=s
         then var inc res t
         else other res t (*raise TERM ("FunSplitState.fold_state_prop",[t])*)
  | fold_state_prop var app abs other inc s res (t as (Free (s',_))) =
         if s'=s then raise TERM ("FunSplitState.fold_state_prop",[t])
         else other res t
  | fold_state_prop var app abs other inc s res (t1$t2) =
         let val res1 = fold_state_prop var app abs other inc s res t1
             val res2 = fold_state_prop var app abs other inc s res1 t2
         in app res1 res2 end
  | fold_state_prop var app abs other inc s res (Abs (x,T,t)) =
         let val res1 = fold_state_prop var app abs other (inc+1) s res t
         in abs x T res1
         end
  | fold_state_prop var app abs other inc s res t = other res t

fun collect_vars s t =
  let
    fun var _ vars t  = snd (bound vars t);
    fun app _ vars2 = vars2;
    fun abs _ _ vars = vars;
    fun other vars _ = vars;
  in fold_state_prop var app abs other 0 s [] t end;

fun abstract_vars vars s t =
  let
    fun var inc _ t  = let val i = fst (bound vars t) in Bound (i+inc) end;
    fun app t1 t2 = t1$t2;
    fun abs x T t = Abs (x,T,t);
    fun other _ t = t;
    val dummy = Bound 0;
  in fold_state_prop var app abs other 0 s dummy t end;

fun sort_vars ctxt vars =
  let
    val fld_idx = idx (fn s1:string => fn s2 => s1 = s2);
    fun compare (_$_$n$(Const (s1,_)$_),_$_$m$(Const (s2,_)$_)) =
      let
        val n' = remdeco' (comp_name n);
        val m' = remdeco' (comp_name m);
      in if s1 = full_globalsN
         then if s2 = full_globalsN then
              string_ord (n',m')
              else LESS
         else if s2 = full_globalsN then GREATER
              else string_ord (n',m')
      end
      | compare (t1,t2) = raise TERM ("FunSplitState.sort_vars.compare",[t1,t2]);
  in sort (rev_order o compare) vars end;

fun split_state ctxt s _ t =
  let
    val vars  = collect_vars s t;
    val vars' = if Config.get ctxt sort_variables then sort_vars ctxt vars else vars;
  in (abstract_vars vars' s t,rev vars') end;

fun abs_var _ t = (remdeco' (sel_name t), sel_type t);

(* Proof for: EX x_1 ... x_n. P x_1 ... x_n
 *            ==> EX s. P (lookup destr_1 "x_1" s) ... (lookup destr_n "x_n" s)
 * Implementation:
 * 1. Eliminate existential quantifiers in premise
 * 2. Instantiate s with:
       (%x. undefined)("x_1" := constr_1 x_1, ..., "x_n" := constr_n x_n)
 * 3. Simplify
 *)

local

val ss =
  simpset_of
    (put_simpset (simpset_of @{theory_context Fun}) @{context}
      addsimps (@{thm StateFun.lookup_def} :: @{thm StateFun.id_id_cancel}
      :: @{thms list.inject} @ @{thms char.inject}
      @ @{thms list.distinct} @ @{thms simp_thms})
    addsimprocs [Record.simproc, StateFun.lazy_conj_simproc]
    |> fold Simplifier.add_cong @{thms block_conj_cong});

in

fun ex_tac ctxt vs st =
  let
    val vs' = rev vs;
    val (Const (_,exT)$_) = HOLogic.dest_Trueprop
                             (Logic.strip_imp_concl (Logic.get_goal (Thm.prop_of st) 1));
    val sT = domain_type (domain_type exT);

    val s0 = Const (@{const_name HOL.undefined},sT);

    fun streq (s1:string,s2) = s1=s2 ;
    fun mk_init []      = []
      | mk_init (t::ts) =
          let
             val xs = mk_init ts;
             val n = component_name t;
             val T = component_type t;
          in if AList.defined streq xs n then xs
             else (n,(T,Const (n,sT --> component_type t)$s0))::xs
          end;

    fun mk_upd (i,t) xs  =
      let
        val selN = component_name t;
        val selT = component_type t;
        val (_,s) = the (AList.lookup streq xs selN);
        val strT = domain_type selT;
        val valT = range_type selT;
        val constr = destr_to_constr (sel_destr t);
        val name = (sel_raw_name t);
        val upd =
          Const (@{const_name Fun.fun_upd}, (strT --> valT)-->strT-->valT--> (strT --> valT)) $
            s $ name $ (constr $ Bound i)
      in AList.update streq (selN,(selT,upd)) xs
      end;

    val upds = fold_index mk_upd vs' (mk_init vs');

    val upd = fold (fn (n,(T,upd)) => fn s =>
                      Const (n ^ Record.updateN, T --> sT --> sT)$upd$s)
                upds
                s0;

    val inst = fold_rev (Term.abs o (fn t => (sel_name t, sel_type t))) vs upd;
    fun lift_inst_ex_tac i st =
      let
        val rule  = Thm.lift_rule (Thm.cprem_of st i) (Drule.incr_indexes st exI);
        val (_$x) = HOLogic.dest_Trueprop (Logic.strip_assums_concl (hd (Thm.prems_of rule)));
        val inst_rule =
          infer_instantiate ctxt [(#1 (dest_Var (head_of x)), Thm.cterm_of ctxt inst)] rule;
      in (compose_tac ctxt (false,inst_rule, Thm.nprems_of exI) i st) end;


  in EVERY [REPEAT_DETERM_N (length vs) (eresolve_tac ctxt [exE] 1),
            lift_inst_ex_tac 1,
            simp_tac (put_simpset ss ctxt) 1
           ] st end
end
(* Test: What happens when there are no lookups., EX s. True *)



end;

structure GeneraliseRecord = GeneraliseFun (structure SplitState=RecordSplitState);
structure GeneraliseStateFun = GeneraliseFun (structure SplitState=FunSplitState);

fun generalise Record = GeneraliseRecord.GENERALISE
  | generalise Function = GeneraliseStateFun.GENERALISE;

(*****************************************************************************)
(** record_vanish_tac splits up the records of a verification condition,    **)
(** trying to generate a predicate without records.                         **)
(** A typical verification condition with a procedure call will have the    **)
(** form "!!s Z. s=Z ==> ..., where s and Z are records                     **)
(*****************************************************************************)

(* FIXME: Check out if removing the useless vars is a performance issue.
   If so, maybe we can remove all useless vars at once (no iterated simplification)
   or try to avoid introducing them.
   Bevore splitting the gaol we can simplifiy the goal with state_simproc this may leed
   to better performance...
*)
fun record_vanish_tac ctxt state_kind state_space i =
  if Config.get ctxt record_vanish then
    let
        val rem_useless_vars_simps = [Drule.triv_forall_equality,@{thm Hoare.triv_All_eq},@{thm Hoare.triv_Ex_eq}];
        val rem_useless_vars_simpset = empty_simpset ctxt addsimps rem_useless_vars_simps;
        fun no_spec (t as (Const (@{const_name All},_)$_)) =
              is_none (try dest_hoare_raw (strip_qnt_body @{const_name All} t))
          | no_spec _ = true;
        fun state_space_no_spec t = if state_space t <> 0 andalso no_spec t then
                                    ~1 else 0;
    in EVERY [trace_tac ctxt "record_vanish_tac -- START --",
              REPEAT (eresolve_tac ctxt [conjE] i),
              trace_tac ctxt "record_vanish_tac -- hyp_subst_tac ctxt --",
              TRY (hyp_subst_tac_thin true ctxt i),
              full_simp_tac rem_useless_vars_simpset i,
               (* hyp_subst_tac may have made some state variables unnecessary. We do not
                  want to split them to avoid naming conflicts and increase performance *)
              trace_tac ctxt "record_vanish_tac -- Splitting records --",
              if Config.get ctxt use_generalise orelse state_kind = Function
              then generalise state_kind ctxt i
              else state_split_simp_tac ctxt rem_useless_vars_simps state_space_no_spec i
              (*THEN_MAYBE
              EVERY [trace_tac ctxt "record_vanish_tac -- removing useless vars --",
                     full_simp_tac rem_useless_vars_simpset i,
                     trace_tac ctxt "record_vanish_tac -- STOP --"]*)
              ]
    end
  else
    all_tac;

(* solve_modifies_tac tries to solve modifies-clauses automatically;
 * The following strategy is followed:
 * After clar-simplifying the modifies clause we remain with a goal of the form
 *
 *  EX a b. s(|A := x|) = s(|A:=a,B:=b|)
 *
 * (or because of conditional statements conjunctions of these kind of goals)
 * We split up the state-records and simplify (record_vanish_tac) and get to a goal of the form:
 *
 * EX a b. (|A=x,B=B|) = (|A=a,B=b|).
 *
 * If the modifies clause was correct we just have to introduce the existential quantifies
 * and apply reflexivity.
 * If not we just simplify the goal.
*)


local

val state_fun_update_ss =
  simpset_of (put_simpset HOL_basic_ss @{context}
    addsimps ([@{thm StateFun.update_def}, @{thm id_def}, @{thm fun_upd_apply}, @{thm if_True}, @{thm if_False}]
      @ @{thms list.inject} @ @{thms char.inject}
      @ @{thms list.distinct} @ @{thms simp_thms} @ K_fun_convs)
    addsimprocs [DistinctTreeProver.distinct_simproc ["distinct_fields", "distinct_fields_globals"]]
    |> Simplifier.add_cong @{thm imp_cong} (* K_fun_congs  FIXME: Stefan fragen*)
    |> Splitter.add_split @{thm split_if});

in

fun solve_modifies_tac ctxt state_kind state_space i st =
  let
    val thy = Proof_Context.theory_of ctxt;
    fun is_split_state (trm as (Const (@{const_name Pure.all},_)$Abs(x,T,t))) =
      if state_space trm <> 0 then
        try (fn () =>
          let
            fun seed (_ $ v $ st) = seed st
              | seed (_ $ t) = (1,t) (* split only state pair *)
              | seed t = (~1,t) (* split globals completely *)
            val all_vars = strip_qnt_vars @{const_name Pure.all} t;
            val concl = HOLogic.dest_Trueprop (Logic.strip_assums_concl t);
            val ex_vars = strip_qnt_vars @{const_name Ex} concl;
            val state = Bound (length all_vars + length ex_vars);
            val (Const (@{const_name HOL.eq},_)$x_upd$x_upd') = strip_qnt_body @{const_name Ex} concl;
            val (split,sd) = seed x_upd;
          in if sd = state then split else 0 end) ()
        |> the_default 0
      else 0
      | is_split_state t = 0;
    val simp_ctxt = put_simpset HOL_ss ctxt addsimps (@{thm Ex_True} :: @{thm Ex_False} :: Record.get_extinjects thy);
      fun try_solve Record i = (*(SOLVE*)
          (((fn k => (TRY (REPEAT_ALL_NEW (resolve_tac ctxt [conjI, impI, allI]) k)))
            THEN_ALL_NEW
          (fn k => EVERY [state_split_simp_tac ctxt [] is_split_state k,
                          simp_tac simp_ctxt k THEN_MAYBE rename_goal ctxt remdeco' k
                          ])) i) (*)*)
        | try_solve _ i =
           ((fn k => (TRY (REPEAT_ALL_NEW (resolve_tac ctxt [conjI, impI, allI]) k)))
             THEN_ALL_NEW
            (fn k => REPEAT (resolve_tac ctxt [exI] k) THEN
                     resolve_tac ctxt [ext] k THEN
                     simp_tac (put_simpset state_fun_update_ss ctxt) k
                     THEN_MAYBE
                     (REPEAT_ALL_NEW (resolve_tac ctxt [conjI,impI,refl]) k))) i
  in
    ((trace_tac ctxt "solve_modifies_tac" THEN
     clarsimp_tac ((ctxt
        |> put_claset (claset_of @{theory_context HOL})
        |> put_simpset (simpset_of @{theory_context Set}))
        addsimps ([@{thm Hoare.mex_def},@{thm Hoare.meq_def}]@K_convs)
        addsimprocs (state_upd_simproc Record::(state_simprocs Record))
        |> fold Simplifier.add_cong K_congs) i)
    THEN_MAYBE
     try_solve state_kind i) st
  end;
end

fun proc_lookup_simp_tac ctxt i st =
  try (fn () =>
    let
      val name = (Logic.concl_of_goal (Thm.prop_of st) i)
            |> dest_hoare |> #2 |> strip_comb |> #2 |> last |> strip_comb |> #2 |> last;
            (* the$(Gamma$name) or the$(strip$Gamma$name) *)
      val pname = (unsuffix proc_deco (dest_string' name));
      val thms =  map_filter I (map (try (Proof_Context.get_thm ctxt))
                              [suffix bodyP pname,
                               suffix (body_def_sfx^"_def") pname,
                               suffix procL pname^"."^ (suffix (body_def_sfx^"_def") pname)]);
    in simp_tac (put_simpset HOL_basic_ss ctxt addsimps thms @ strip_simps @ @{thms option.sel}) i st end) ()
  |> the_default (Seq.single st);

fun proc_lookup_in_dom_simp_tac ctxt i st =
  try (fn () =>
    let
      val _$name$_  = (HOLogic.dest_Trueprop (Logic.concl_of_goal (Thm.prop_of st) i));
          (* name : Gamma *)
      val pname = (unsuffix proc_deco (dest_string' name));
      val thms =  map_filter I (map (try (Proof_Context.get_thm ctxt))
                                 [suffix bodyP pname]);
    in
      simp_tac (put_simpset HOL_basic_ss ctxt
        addsimps (@{thm Hoare.lookup_Some_in_dom} :: @{thm dom_strip} :: thms)) i st end) ()
  |> the_default (Seq.single st);


fun HoareRuleTac ctxt insts fixes st =
  let
    val annotate_simp_tac =
      simp_tac (put_simpset HOL_basic_ss ctxt
        addsimps (anno_defs@normalize_simps)
        addsimprocs [@{simproc case_prod_beta}]);
    fun is_com_eq (Const (@{const_name Trueprop},_)$(Const (@{const_name HOL.eq},T)$_$_)) =
          (case (binder_types T) of
             (Type (@{type_name Language.com},_)::_) => true
           | _ => false)
       | is_com_eq _ = false;
    fun annotate_tac i st =
        if is_com_eq (Logic.concl_of_goal (Thm.prop_of st) i)
        then annotate_simp_tac i st
        else all_tac st;
  in
    ((fn i => REPEAT (resolve_tac ctxt [allI] i)) THEN'
      Rule_Insts.res_inst_tac ctxt insts fixes st)
      THEN_ALL_NEW annotate_tac
  end;

fun HoareCallRuleTac state_kind state_space ctxt thms i st =
  let
    fun dest_All (Const (@{const_name All},_)$t) = SOME t
      | dest_All _ = NONE;

    fun auxvars t =
         (case (map_filter ((first_subterm is_hoare) o snd) (max_subterms_dest dest_All t)) of
             ((vars,_)::_) => vars
           | _ => []);

    fun auxtype rule =
         (case (auxvars (Thm.prop_of rule)) of
           [] => NONE
          | vs => (case (last vs) of
                     (_,TVar (z,_)) => SOME (z,rule)
                   | _ => NONE));

    val thms' =
      let val auxvs = map fst (auxvars (Logic.concl_of_goal (Thm.prop_of st) i));
          val tvar_thms = map_filter auxtype thms
      in if length thms = length tvar_thms
         then adapt_aux_var ctxt true auxvs tvar_thms
         else thms
      end;
    val is_sidecondition = not o can dest_hoare;
    fun solve_sidecondition_tac (t,i) =
        if is_sidecondition t
        then FIRST
               [CHANGED_PROP (wf_tac ctxt i),
                (*init_conforms_tac state_kind state_space i,*)
                post_conforms_tac ctxt state_kind i THEN_MAYBE
                 (if is_modifies_clause t
                  then solve_modifies_tac ctxt state_kind state_space i
                  else all_tac),
                proc_lookup_in_dom_simp_tac ctxt i
                ]
        else in_rel_simp ctxt i THEN
             simp_tac (put_simpset HOL_basic_ss ctxt addsimps [@{thm Un_empty_left},@{thm Un_empty_right}]) i THEN
             proc_lookup_simp_tac ctxt i

    fun basic_tac i = (((resolve_tac ctxt thms')
                       THEN_ALL_NEW
                       (fn k => (SUBGOAL solve_sidecondition_tac k))) i)
  in  (basic_tac
        ORELSE'
       (fn k =>
         (REPEAT (resolve_tac ctxt [allI] k))
           THEN EVERY [resolve_tac ctxt thms' k])) i st
  end;

(* vcg_polish_tac tries to solve modifies-clauses automatically; for other specifications the
 * records are only splitted and simplified.
*)
fun vcg_polish_tac solve_modifies ctxt state_kind state_space i =
    if solve_modifies
    then solve_modifies_tac ctxt state_kind state_space i
    else record_vanish_tac ctxt state_kind state_space i
         THEN_MAYBE EVERY [rename_goal ctxt remdeco' i(*,
                           simp_tac (HOL_basic_ss addsimps @{thms simp_thms})) i*)];

fun is_funtype (Type ("fun", _)) = true
  | is_funtype _ = false;

fun state_kind_of ctxt T =
  let
    val thy = Proof_Context.theory_of ctxt;
    val (s,sT) = nth (fst (Record.get_recT_fields thy T)) 1;
  in if Long_Name.base_name s = "locals" andalso is_funtype sT then Function else Record end
  handle Subscript => Record;

fun find_state_space_in_triple ctxt t =
  try (fn () =>
    (case first_subterm is_hoare t of
       NONE => NONE
     | SOME (abs_vars,triple) =>
        let
           val (_,com,_,_,mode,_,_,_) = dest_hoare_raw triple;
           val T = fastype_of1 (map snd abs_vars,com)
           val Type(_,state_spaceT::_) = T;
           val SOME Tids = stateT_ids state_spaceT;
        in SOME (Tids,mode, state_kind_of ctxt state_spaceT)
        end)) ()
  |> Option.join;

fun get_state_space_in_subset_eq ctxt t =
  (* get state type from the following kind of terms: P <= Q, s: P *)
  try (fn () =>
    let
      val (subset_eq,_) =
        (strip_comb o HOLogic.dest_Trueprop o strip_qnt_body @{const_name Pure.all}) t;
      val Ts = map snd (strip_vars t);
      val T = fastype_of1 (Ts,subset_eq);
      val Type (_, [_,Type (_, [Type (_, [state_spaceT]), _])]) = T; 
              (* also works for "in": x : P *)
      val SOME Tids = stateT_ids state_spaceT;
    in (Tids,Partial, state_kind_of ctxt state_spaceT) end) ();

fun get_state_space ctxt i st =
  (case try (Logic.concl_of_goal (Thm.prop_of st)) i of
     SOME t => (case find_state_space_in_triple ctxt t of
                  SOME sp => SOME sp
                | NONE => get_state_space_in_subset_eq ctxt t)
   | NONE => NONE);

fun mk_hoare_tac hoare_tac finish_tac annotate_inv exnames
                 strip_guards spec_sfx ctxt i st =
    case get_state_space ctxt i st of
       SOME (Tids,mode,kind)
       => SELECT_GOAL
            (hoare_tac annotate_inv exnames strip_guards mode kind (is_state_space_var Tids)
                   spec_sfx ctxt (finish_tac kind (is_state_space_var Tids))) i st
     | NONE => no_tac st

fun vcg_tac spec_sfx strip_guards exnames ctxt i st =
  mk_hoare_tac HoareTac (vcg_polish_tac (spec_sfx="_modifies") ctxt)
      (spec_sfx="_modifies") exnames (strip_guards="true") spec_sfx ctxt i st;

fun hoare_tac spec_sfx strip_guards _ ctxt i st =
  let fun tac state_kind state_space i = if spec_sfx="_modifies"
               then solve_modifies_tac ctxt state_kind state_space i
               else all_tac;

  in mk_hoare_tac HoareTac tac (spec_sfx="_modifies") []
                  (strip_guards="true") spec_sfx ctxt i st
  end;

fun hoare_raw_tac spec_sfx strip_guards exnames ctxt i st =
  mk_hoare_tac HoareTac (K (K (K all_tac)))
     (spec_sfx="_modifies") [] (strip_guards="true") spec_sfx
     ctxt i st;


fun hoare_step_tac spec_sfx strip_guards exnames ctxt i st =
  mk_hoare_tac (K (K HoareStepTac)) (vcg_polish_tac (spec_sfx="_modifies")
     ctxt) false [] (strip_guards="true") spec_sfx ctxt i st;

fun hoare_rule_tac ctxt thms i st = SUBGOAL (fn _ =>
    (case get_state_space ctxt i st of
       SOME (Tids,_,kind) => HoareCallRuleTac kind (is_state_space_var Tids) ctxt thms i
     | NONE => error "could not find proper state space type (structure or record) in goal")) i st;


(*** Methods ***)

val hoare_rule = Rule_Insts.method HoareRuleTac hoare_rule_tac;

val argP = Args.name --| @{keyword "="} -- Args.name
val argsP = Scan.repeat argP
val default_args = [("spec","spec"),("strip_guards","false")]

val vcg_simp_modifiers =
  [Args.add -- Args.colon >> K (Method.modifier vcg_simp_add @{here}),
   Args.del -- Args.colon >> K (Method.modifier vcg_simp_del @{here})];

fun assocs2 key = map snd o filter (curry (op =) key o fst);

fun gen_simp_method tac =
  Scan.lift (argsP >> (fn args => args @ default_args)) --|
  Method.sections vcg_simp_modifiers >>
    (fn args => fn ctxt => Method.SIMPLE_METHOD'
      (tac ("_" ^ the (AList.lookup (op =) args "spec"))
        (the (AList.lookup (op =) args "strip_guards"))
        (assocs2 "exspec" args) ctxt));

val hoare = gen_simp_method hoare_tac;
val hoare_raw = gen_simp_method hoare_raw_tac;
val vcg = gen_simp_method vcg_tac;
val vcg_step = gen_simp_method hoare_step_tac;


val trace_hoare_users = Unsynchronized.ref false

fun print_subgoal_tac ctxt s i =
    SUBGOAL (fn (prem, _) => trace_tac ctxt (s ^ (Syntax.string_of_term ctxt prem))) i

fun mk_hoare_thm thm _ ctxt _ i =
    EVERY [resolve_tac ctxt [thm] i,
      if !trace_hoare_users then print_subgoal_tac ctxt "Tracing: " i
      else all_tac]

val vcg_hoare_add =
    Thm.declaration_attribute (fn thm => add_hoare_tacs [(Thm.derivation_name thm, mk_hoare_thm thm)])

exception UNDEF
val vcg_hoare_del =
    Thm.declaration_attribute (fn _ => fn _ => raise UNDEF)


(* setup theory *)

val _ =
  Theory.setup
    (Attrib.setup @{binding vcg_simp} (Attrib.add_del vcg_simp_add vcg_simp_del)
      "declaration of Simplifier rule for vcg"
    #>
    Attrib.setup @{binding vcg_hoare} (Attrib.add_del vcg_hoare_add vcg_hoare_del)
      "declaration of wp rule for vcg")
    (*#> add_wp_tacs initial_wp_tacs*)

end;
