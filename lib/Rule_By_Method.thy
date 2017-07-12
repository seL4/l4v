(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Rule_By_Method
imports
  Main
  "~~/src/HOL/Eisbach/Eisbach_Tools"
begin

ML \<open>
signature RULE_BY_METHOD =
sig
  val rule_by_tac: Proof.context -> {vars : bool, prop: bool} ->
    (Proof.context -> tactic) -> (Proof.context -> tactic) list -> Position.T -> thm
end;


fun atomize ctxt = Conv.fconv_rule (Object_Logic.atomize ctxt);

fun fix_schematics ctxt raw_st =
  let
    val ((schematic_types, [st']), ctxt1) = Variable.importT [raw_st] ctxt;
    fun certify_inst ctxt inst = map (apsnd (Thm.cterm_of ctxt)) (#2 inst)
    val (schematic_terms, ctxt2) =
      Variable.import_inst true [Thm.prop_of st'] ctxt1
      |>> certify_inst ctxt1;
    val schematics = (schematic_types, schematic_terms);
  in (Thm.instantiate schematics st', ctxt2) end

fun curry_asm ctxt st = if Thm.nprems_of st = 0 then Seq.empty else
let

  val prems = Thm.cprem_of st 1 |> Thm.term_of |> Logic.strip_imp_prems;

  val (thesis :: xs,ctxt') = Variable.variant_fixes ("thesis" :: replicate (length prems) "P") ctxt;

  val rl =
    xs
    |> map (fn x => Thm.cterm_of ctxt' (Free (x, propT)))
    |> Conjunction.mk_conjunction_balanced
    |> (fn xs => Thm.apply (Thm.apply @{cterm "Pure.imp"} xs) (Thm.cterm_of ctxt' (Free (thesis,propT))))
    |> Thm.assume
    |> Conjunction.curry_balanced (length prems)
    |> Drule.implies_intr_hyps

  val rl' = singleton (Variable.export ctxt' ctxt) rl;

  in Thm.bicompose (SOME ctxt) {flatten = false, match = false, incremented = false}
              (false, rl', 1) 1 st end;

val drop_trivial_imp =
let
  val asm =
    Thm.assume (Drule.protect @{cprop "(PROP A \<Longrightarrow> PROP A) \<Longrightarrow> PROP A"})
    |> Goal.conclude;

in
  Thm.implies_elim  asm (Thm.trivial @{cprop "PROP A"})
  |> Drule.implies_intr_hyps
  |> Thm.generalize ([],["A"]) 1
  |> Drule.zero_var_indexes
 end

val drop_trivial_imp' =
let
  val asm =
    Thm.assume (Drule.protect @{cprop "(PROP P \<Longrightarrow> A) \<Longrightarrow> A"})
    |> Goal.conclude;

  val asm' = Thm.assume @{cprop "PROP P == Trueprop A"}

in
  Thm.implies_elim asm (asm' COMP Drule.equal_elim_rule1)
  |> Thm.implies_elim (asm' COMP Drule.equal_elim_rule2)
  |> Drule.implies_intr_hyps
  |> Thm.permute_prems 0 ~1
  |> Thm.generalize ([],["A","P"]) 1
  |> Drule.zero_var_indexes
 end

fun atomize_equiv_tac ctxt i =
  Object_Logic.full_atomize_tac ctxt i
  THEN PRIMITIVE (fn st'  =>
  let val (_,[A,_]) = Drule.strip_comb (Thm.cprem_of st' i) in
  if Object_Logic.is_judgment ctxt (Thm.term_of A) then st'
  else error ("Failed to fully atomize result:\n" ^ (Syntax.string_of_term ctxt (Thm.term_of A))) end)


structure Data = Proof_Data
(
  type T = thm list * bool;
  fun init _ = ([],false);
);

val empty_rule_prems = Data.map (K ([],true));

fun add_rule_prem thm = Data.map (apfst (Thm.add_thm thm));

fun with_rule_prems enabled parse =
  Scan.state :|-- (fn context =>
  let
    val context' = Context.proof_of context |> Data.map (K ([Drule.free_dummy_thm],enabled))
                   |> Context.Proof
  in Scan.lift (Scan.pass context' parse) end)


fun get_rule_prems ctxt =
  let
    val (thms,b) = Data.get ctxt
  in if (not b) then [] else thms end


fun zip_subgoal assume tac (ctxt,st : thm) = if Thm.nprems_of st = 0 then Seq.single (ctxt,st) else
let
  fun bind_prems st' =
  let
    val prems = Drule.cprems_of st';
    val (asms, ctxt') = Assumption.add_assumes prems ctxt;
    val ctxt'' = fold add_rule_prem asms ctxt';
    val st'' = Goal.conclude (Drule.implies_elim_list st' (map Thm.assume prems));
  in (ctxt'',st'') end

  fun defer_prems st' =
  let
    val nprems = Thm.nprems_of st';
    val st'' = Thm.permute_prems 0 nprems (Goal.conclude st');
  in (ctxt,st'') end;


in
  tac ctxt (Goal.protect 1 st)
  |> Seq.map (if assume then bind_prems else defer_prems)  end


fun zip_subgoals assume tacs pos ctxt st =
let
  val nprems = Thm.nprems_of st;
  val _ = nprems < length tacs andalso error ("More tactics than rule assumptions" ^ Position.here pos);
  val tacs' = map (zip_subgoal assume) (tacs @ (replicate (nprems - length tacs) (K all_tac)));
  val ctxt' = empty_rule_prems ctxt;
in Seq.EVERY tacs' (ctxt',st) end;

fun rule_by_tac' ctxt {vars,prop} tac asm_tacs pos raw_st =
  let
    val (st,ctxt1) = if vars then (raw_st,ctxt) else fix_schematics ctxt raw_st;

    val ([x],ctxt2) = Proof_Context.add_fixes [(Binding.name Auto_Bind.thesisN,NONE, NoSyn)] ctxt1;

    val thesis = if prop then Free (x,propT) else Object_Logic.fixed_judgment ctxt2 x;

    val cthesis = Thm.cterm_of ctxt thesis;

    val revcut_rl' = Thm.instantiate' [] ([NONE,SOME cthesis]) @{thm revcut_rl};

    fun is_thesis t = Logic.strip_assums_concl t aconv thesis;

    fun err thm str = error (str ^ Position.here pos ^ "\n" ^
      (Pretty.string_of (Goal_Display.pretty_goal ctxt thm)));

    fun pop_thesis st =
    let
      val prems = Thm.prems_of st |> tag_list 0;
      val (i,_) = (case filter (is_thesis o snd) prems of
        [] => err st "Lost thesis"
        | [x] => x
        | _ => err st "More than one result obtained");
     in st |> Thm.permute_prems 0 i  end

    val asm_st =
    (revcut_rl' OF [st])
    |> (fn st => Goal.protect (Thm.nprems_of st - 1) st)


    val (ctxt3,concl_st) = case Seq.pull (zip_subgoals (not vars) asm_tacs pos ctxt2 asm_st) of
      SOME (x,_) => x
    | NONE => error ("Failed to apply tactics to rule assumptions. " ^ (Position.here pos));

    val concl_st_prepped =
      concl_st
      |> Goal.conclude
      |> (fn st => Goal.protect (Thm.nprems_of st) st |> Thm.permute_prems 0 ~1 |> Goal.protect 1)

    val concl_st_result = concl_st_prepped
      |> (tac ctxt3
          THEN (PRIMITIVE pop_thesis)
          THEN curry_asm ctxt
          THEN PRIMITIVE (Goal.conclude #> Thm.permute_prems 0 1 #> Goal.conclude))

    val result = (case Seq.pull concl_st_result of
      SOME (result,_) => singleton (Proof_Context.export ctxt3 ctxt) result
      | NONE => err concl_st_prepped "Failed to apply tactic to rule conclusion:")

    val drop_rule = if prop then drop_trivial_imp else drop_trivial_imp'

    val result' = ((Goal.protect (Thm.nprems_of result -1) result) RS drop_rule)
    |> (if prop then all_tac else
       (atomize_equiv_tac ctxt (Thm.nprems_of result)
       THEN resolve_tac ctxt @{thms Pure.reflexive} (Thm.nprems_of result)))
    |> Seq.hd
    |> Raw_Simplifier.norm_hhf ctxt

  in Drule.zero_var_indexes result' end;

fun rule_by_tac is_closed ctxt args tac asm_tacs pos raw_st =
 let val f = rule_by_tac' ctxt args tac asm_tacs pos
  in
   if is_closed orelse Context_Position.is_really_visible ctxt then SOME (f raw_st)
   else try f raw_st
 end

fun pos_closure (scan : 'a context_parser) :
  (('a * (Position.T * bool)) context_parser) = (fn (context,toks) =>
  let
    val (((context',x),tr_toks),toks') = Scan.trace (Scan.pass context (Scan.state -- scan)) toks;
    val pos = Token.range_of tr_toks;
    val is_closed = exists (fn t => is_some (Token.get_value t)) tr_toks
  in ((x,(Position.range_position pos, is_closed)),(context',toks')) end)

val parse_flags = Args.mode "schematic" -- Args.mode "raw_prop" >> (fn (b,b') => {vars = b, prop = b'})

fun tac m ctxt =
  Method.NO_CONTEXT_TACTIC ctxt
    (Method.evaluate_runtime m ctxt []);

(* Declare as a mixed attribute to avoid any partial evaluation *)

fun handle_dummy f (context, thm) =
  case (f context thm) of SOME thm' => (NONE, SOME thm')
  | NONE => (SOME context, SOME Drule.free_dummy_thm)

val (rule_prems_by_method : attribute context_parser) = Scan.lift parse_flags :-- (fn flags =>
  pos_closure (Scan.repeat1
    (with_rule_prems (not (#vars flags)) Method.text_closure ||
      Scan.lift (Args.$$$ "_" >> (K Method.succeed_text))))) >>
        (fn (flags,(ms,(pos, is_closed))) => handle_dummy (fn context =>
          rule_by_tac is_closed (Context.proof_of context) flags (K all_tac) (map tac ms) pos))

val (rule_concl_by_method : attribute context_parser) = Scan.lift parse_flags :-- (fn flags =>
  pos_closure (with_rule_prems (not (#vars flags)) Method.text_closure)) >>
    (fn (flags,(m,(pos, is_closed))) => handle_dummy (fn context =>
      rule_by_tac is_closed (Context.proof_of context) flags (tac m) [] pos))

val _ = Theory.setup
  (Global_Theory.add_thms_dynamic (@{binding "rule_prems"},
    (fn context => get_rule_prems (Context.proof_of context))) #>
   Attrib.setup @{binding "#"} rule_prems_by_method
    "transform rule premises with method" #>
   Attrib.setup @{binding "@"} rule_concl_by_method
    "transform rule conclusion with method" #>
   Attrib.setup @{binding atomized}
    (Scan.succeed (Thm.rule_attribute []
      (fn context => fn thm =>
        Conv.fconv_rule (Object_Logic.atomize (Context.proof_of context)) thm
          |> Drule.zero_var_indexes)))
    "atomize rule")
\<close>

experiment begin

ML \<open>
  val [att] = @{attributes [@\<open>erule thin_rl, cut_tac TrueI, fail\<close>]}
  val k = Attrib.attribute @{context} att
  val _ = case (try k (Context.Proof @{context}, Drule.dummy_thm)) of
    SOME _ => error "Should fail"
    | _ => ()
  \<close>

lemmas baz = [[@\<open>erule thin_rl, rule revcut_rl[of "P \<longrightarrow> P \<and> P"], simp\<close>]] for P

lemmas bazz[THEN impE] = TrueI[@\<open>erule thin_rl, rule revcut_rl[of "P \<longrightarrow> P \<and> P"], simp\<close>] for P

lemma "Q \<longrightarrow> Q \<and> Q" by (rule baz)

method silly_rule for P :: bool uses rule =
  (rule [[@\<open>erule thin_rl, cut_tac rule, drule asm_rl[of P]\<close>]])

lemma assumes A shows A by (silly_rule A rule: \<open>A\<close>)

lemma assumes A[simp]: "A" shows A
  apply (match conclusion in P for P \<Rightarrow>
       \<open>rule [[@\<open>erule thin_rl, rule revcut_rl[of "P"], simp\<close>]]\<close>)
  done

end

end
