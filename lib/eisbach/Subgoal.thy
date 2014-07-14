(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Subgoal
imports Main
begin

definition Focus' :: "prop \<Rightarrow> prop" where "Focus' x \<equiv> x"

consts "Focus" :: "prop"

lemma FocusI:"PROP P \<Longrightarrow> PROP Focus' (PROP P)" by (simp add: Focus'_def)

ML {* fun mk_focus ts = Conjunction.intr_balanced (fold_rev (cons o Drule.mk_term) ts []) RS @{thm FocusI}*}

ML {* fun dest_focus t = 
  let
   
    val (head,args) = Drule.strip_comb t
    val _ = (term_of head = @{const Focus}) orelse error ("Not a Focus: " ^ (@{make_string} t))
     
  in
    map (Thm.dest_arg) (Conjunction.dest_conjunctions (hd args))  end
    
  *}

ML {* fun focus_intro thm = 
  let
    val (cts,_) = thm
    |> cprop_of
    |> Thm.dest_implies
    |>> dest_focus
    
    val _ = tracing (@{make_string} (mk_focus cts))
  in
    (thm OF [(mk_focus cts)],cts)
  end
  
*}


ML{*

(*  Title:      Pure/subgoal.ML
    Author:     Makarius

Tactical operations with explicit subgoal focus, based on canonical
proof decomposition.  The "visible" part of the text within the
context is fixed, the remaining goal may be schematic.
*)

signature SUBGOAL2 =
sig
  type focus = {context: Proof.context, params: (string * cterm) list, prems: thm list,
    oldparams: cterm list,
    asms: cterm list, concl: cterm, schematics: (ctyp * ctyp) list * (cterm * cterm) list}
  val focus_params: Proof.context -> int -> thm -> focus * thm
  val focus_prems: Proof.context -> int -> thm -> focus * thm
  val focus: Proof.context -> int -> thm -> focus * thm
  val gen_focus: bool * bool * bool * bool -> Proof.context -> int -> thm -> focus * thm
  val retrofit: Proof.context -> Proof.context -> (string * cterm) list -> cterm list ->
    int -> thm -> thm -> thm Seq.seq
  val retrofit': Proof.context -> focus -> bool -> bool -> int -> thm -> thm -> thm Seq.seq
  val FOCUS_PARAMS: (focus -> tactic) -> Proof.context -> int -> tactic
  val FOCUS_PREMS: (focus -> tactic) -> Proof.context -> int -> tactic
  val FOCUS: (focus -> tactic) -> Proof.context -> int -> tactic
  val FOCUS_KEEP: (focus -> tactic) -> Proof.context -> int -> tactic
  val SUBPROOF: (focus -> tactic) -> Proof.context -> int -> tactic
  val check_focus: Proof.context -> thm -> bool
end;

structure Subgoal2: SUBGOAL2 =
struct

(* focus *)

type focus = {context: Proof.context, params: (string * cterm) list, 
  oldparams: cterm list, prems: thm list,
  asms: cterm list, concl: cterm, schematics: (ctyp * ctyp) list * (cterm * cterm) list};

fun subst ctxt n rule = Conv.gconv_rule (Conv.concl_conv n (Conv.top_sweep_conv (K  (Conv.rewr_conv rule)) ctxt)) 1

fun freeze ctxt prop =
  let
 
    val (schematics, ctxt3) =
      Variable.import_inst true ([Thm.term_of (Thm.cprem_of prop 1)]) ctxt
      |>> Thm.certify_inst (Thm.theory_of_thm prop);

    val frozen_prop = Thm.instantiate schematics prop;
  in
    (frozen_prop,schematics,ctxt3) end;
  
(*Add var constraints to goal*)
fun add_implicit_vars ctxt schematics prop  = 
  let
    val thy = Thm.theory_of_cterm prop;
    val cert = Thm.cterm_of thy;
    
    val eqs = map (cert o Logic.mk_equals o pairself Thm.term_of o swap) schematics;
   
    val goal = prop
    |> Thm.instantiate_cterm ([],schematics)
    |> not (null schematics) ? (curry Drule.list_implies eqs)
    |> Goal.init;
   
    val (frozen_goal,(_,_),ctxt1) = freeze ctxt goal;

    val frozen_prem = Thm.cprem_of frozen_goal 1;
    val rewrites = take (length schematics) (Drule.strip_imp_prems frozen_prem);

    val (rewritten_goal,subgoals) = frozen_goal
    |> fold (subst ctxt1 (length schematics) o Thm.assume) rewrites
    |> (fn thm => (thm,Drule.cprems_of thm));        
    
    val new_goal = rewritten_goal
      |> fold (Thm.elim_implies o Thm.assume) subgoals
      |> Goal.conclude
      |> fold (curry (op COMP) o Thm.assume) rewrites
      |> Drule.implies_intr_list rewrites
      |> Thm.implies_intr (cert (Logic.mk_term @{term Focus}))
      |> Goal.protect 0
      |> Drule.implies_intr_list subgoals
      |> fold (K (Seq.hd o etac Drule.thin_rl 1)) (schematics)
      |> singleton (Variable.export ctxt1 ctxt);
    

    val concl =  Thm.term_of (Drule.strip_imp_concl (cprop_of new_goal));
    
    val imps = map Logic.dest_equals
      (take (length schematics) (tl (Logic.strip_imp_prems (Logic.unprotect concl))));
      
    val schematics' = map2 
      (fn (_,newschem) => fn (oldschem,_)
          => (cert newschem,oldschem)) imps schematics;
         
   in
      (Drule.cterm_instantiate schematics' new_goal) end;
   

fun mk_new_head n t = 
  let
    val (head,args) = strip_comb t
  in
    list_comb (Free (n,fastype_of head),args) end;
  
  

    
(* lift and retrofit *)

(*
     B [?'b, ?y]
  ----------------
  B ['b, y params]
*)
fun lift_import idx params concl_vars th ctxt =
  let
    val cert = Thm.cterm_of (Proof_Context.theory_of ctxt);
    val ((_, [th']), ctxt') = Variable.importT [th] ctxt;
    
    val Ts = map (#T o Thm.rep_cterm) params; 
    val ts = map Thm.term_of params;

      
    val prop = Thm.full_prop_of th';
   
 
    val _ = tracing (@{make_string} prop)
    val vars = rev (Term.add_vars prop []);
    val _ = tracing (@{make_string} vars)
    val (ys, ctxt'') = Variable.variant_fixes (map (Name.clean o #1 o #1) vars) ctxt';
    val (ys', ctxt''') = Variable.variant_fixes ys ctxt'';
    val ys'' = ListPair.zip (ys,ys')
    
    fun var_inst v (y,y') =
      let
        val ((x, i), T) = v;

        val (U, args) =
          if member (op =) concl_vars v then (T, [])
          else (Ts ---> T, ts);
        val u = Free (y, U);
        val u' = Free (y',U);
        in ((((Var v, list_comb (u, args)), (u', Var ((x, i + idx), U))),(u,u'))) end;
        
    val ((inst1,inst2), eqps) = (map2 var_inst vars ys'')
    |> split_list
    ||> map (pairself cert)
    |>> split_list
    |>> pairself (map (pairself cert))
    
    
    val eqs = map (fn (t,t') => (Thm.mk_binop ( cert (Const("==",(typ_of o ctyp_of_term) t --> (typ_of o ctyp_of_term) t' --> propT))) t t')) eqps
    
    fun subst rule = Conv.fconv_rule (Conv.top_sweep_conv (K  (Conv.rewr_conv rule)) ctxt''')
          
    val th'' = th' 
    |> Thm.instantiate ([], inst1)
    |> fold (subst o Thm.assume) eqs
   
    
  in (((inst1,inst2,eqs), th''), (ctxt'')) end;

(*
       [x, A x]
          :
       B x ==> C
  ------------------
  [!!x. A x ==> B x]
          :
          C
*)
fun lift_subgoals keep_prems params asms nprems th =
  let
  
    val lift =
      not keep_prems ? curry Drule.list_implies asms
      #> fold_rev Thm.all_name params;
          
    val unlift =
      Drule.forall_elim_list (map #2 params) o Thm.assume
      #> not keep_prems ? fold (Thm.elim_implies o Thm.assume) asms;
   
    val subgoals = map lift (take nprems (Drule.strip_imp_prems (Thm.cprop_of th)));
    
    val th' = fold (Thm.elim_implies o unlift) subgoals th;
  in (subgoals, th') end;

fun clear_asms schematics asms thm =
  let
    val nsubgoals = nprems_of thm
    val nschems = length schematics
    val nprems = (Logic.count_prems  (Logic.unprotect (concl_of thm))) - nschems - 1

    val names = map ((fn (Free (n,_)) => n) o term_of o snd) schematics
    
    
    val interm3 = Goal.conclude thm
      |> Thm.permute_prems 0 nsubgoals
      |> (op OF) o rpair [(Drule.mk_term @{cterm Focus})]
      |> Thm.permute_prems 0 nschems
      |> (fn t => Drule.implies_elim_list t  (map (Thm.assume) asms))
      |> Drule.implies_intr_list asms
      |> Thm.permute_prems 0 (nsubgoals + nprems)
      |> Drule.generalize ([],names)
      
    val insts = map (Thm.dest_equals) (take nschems (cprems_of interm3))
  
    val interm4 = Thm.instantiate ([],insts) interm3
    |> fold (curry op COMP o Thm.reflexive o snd) insts
    |> Thm.permute_prems 0 nprems
    

  in
    interm4 end;  
  
fun clear_spurious_tpairs params thm =
  let
  
    val tpairs = (#tpairs (rep_thm thm))
    val cert = Thm.cterm_of (Thm.theory_of_thm thm)
    fun abs t = fold_rev lambda (map term_of params) t
    
    val eq_pairs = map (cert o Logic.mk_equals o pairself abs) tpairs

    val thm' = thm
    |> Drule.implies_intr_list eq_pairs
    |> tap (fn t => tracing (@{make_string} (crep_thm t)))
    |> fold (fn ct => fn t => (Thm.reflexive (Thm.dest_equals_lhs ct)) COMP t) eq_pairs
    |> Drule.instantiate_normalize ([],[])
    
  in
    thm' end  

(* Retrofit focused goal to given goal. Works in the presence of flex-flex pairs.
   Preserves any flex-flex pairs produced in the focused context, clearing
   mentions of now-fixed params.*)

fun retrofit' ctxt0 (focus: focus) keep_prems keep_schematics i st1 st0 =
  let
  
    val params = #params focus;
    val ctxt1 = #context focus;
    val asms = #asms focus;
    val schematics = #schematics focus;
    val cert = Thm.cterm_of (Proof_Context.theory_of ctxt1);   
      
    val idx = Thm.maxidx_of st0 + 1;
    val ps = map #2 params; 

    val st1' = st1
    |> clear_spurious_tpairs ps
    
       
    val concl_vars = Term.add_vars (Logic.strip_imp_concl (Thm.full_prop_of st1')) []
    
    val st1'' = st1'
    |> clear_asms (snd schematics) asms
    
    val (((_,subgoal_inst,eqs), st2), ctxt2) = lift_import idx ps concl_vars st1'' ctxt1;
    
    val (subgoals, st3) = lift_subgoals keep_prems params asms (nprems_of st1) st2;

    val result = st3
      |> Drule.forall_intr_list ps
    
      |> Drule.implies_intr_list subgoals
      |> Drule.implies_intr_list eqs

      |> singleton (Variable.export ctxt2 ctxt0)
      |> Thm.adjust_maxidx_thm idx     

      |> (fn t => Thm.bicompose {flatten = true, match = false, incremented = false} (false, t, Thm.nprems_of st1 + (length eqs)) i st0)
      |> Seq.map (fn t => t
        |> fold_rev (Thm.forall_intr o #1) subgoal_inst
        |> fold (Thm.forall_elim o #2) subgoal_inst
        |> fold (fn _ => fn t => (@{thm Pure.reflexive} RS t)) eqs
        )

  in result end


fun retrofit ctxt0 ctxt1 params asms i st0 st1 =
  retrofit' ctxt1 {context = ctxt0, params = params, oldparams = [], asms = asms, prems = map Thm.assume asms, 
                    schematics = ([],[]), concl = cprop_of Drule.dummy_thm} false false i st0 st1
                    
fun map_context f ({context, params, oldparams, prems, asms, concl, schematics} : focus) = 
  ({context = f context,
    params = params,
    oldparams = oldparams,
    prems = prems,
    asms = asms,
    concl = concl,
    schematics = schematics} : focus)


structure Sanity_Check = Generic_Data
(
  type T = (thm -> bool);
  val empty : T = (K true)
  fun extend t : T = t;
  fun merge (t1,t2): T = (fn t => t1 t andalso t2 t);
);  

(* Only fail focus check if the goal is still intact *)
fun still_focused thm = thm
  |> Thm.concl_of
  |> Logic.strip_imp_concl
  |> Logic.unprotect
  |> Logic.strip_imp_prems
  |> Option.map (((op =) o (pair (Logic.mk_term @{const Focus}))) o fst) o List.getItem
  |> the_default false
    
fun gen_focus (do_prems, do_concl, keep_prems, keep_schematics) ctxt i raw_st =
  let
    val st = Simplifier.norm_hhf_protect raw_st;
    
    val ((schematic_types, [st']), ctxt1) = Variable.importT [st] ctxt;
    val ((params, goal), ctxt2) = Variable.focus_cterm (Thm.cprem_of st' i) ctxt1;
    val (asms, concl) =
      if do_prems then (Drule.strip_imp_prems goal, Drule.strip_imp_concl goal)
      else ([], goal);
    val text = asms @ (if do_concl then [concl] else []);

    val ((_, schematic_terms), ctxt3) =
      Variable.import_inst true (map Thm.term_of text) ctxt2
      |>> Thm.certify_inst (Thm.theory_of_thm raw_st);
    
    val schematics = (schematic_types, schematic_terms);
          

    val concl' = (if keep_prems then goal else concl)
      |> (if keep_schematics then add_implicit_vars ctxt3 schematic_terms 
            else Goal.init o (Thm.instantiate_cterm schematics))       
    
    val asms' = map (Thm.instantiate_cterm schematics) asms;
    
    val (prems, context) = Assumption.add_assumes asms' ctxt3;
    
    val focus = {context = context, params = params, prems = prems,
      oldparams = [],
      asms = asms', concl = (Thm.instantiate_cterm schematics concl), schematics = (schematic_types,schematic_terms)}
    
     (*TODO: Optimization: Sanity check should be able to just examine schematics to see if
                           their instantiations contain params they don't have access to/themselves*)
     val context' = Context.proof_map (Sanity_Check.map (fn f => (fn t =>
      let
        val othm = try (Seq.hd o (retrofit' ctxt focus keep_prems keep_schematics i t)) raw_st;
        val result = case othm of NONE => not (still_focused t) | SOME thm => f thm;
      in
        result end)))
        

  in
    (map_context context' focus, concl')
  end;
  
fun check_focus ctxt thm = (Sanity_Check.get (Context.Proof ctxt)) thm

val focus_params = gen_focus (false, false,false,false);
val focus_prems = gen_focus (true, false,false,false);
val focus = gen_focus (true, true,false,false);
                    
(* tacticals *)

fun GEN_FOCUS flags tac ctxt i st =
  if Thm.nprems_of st < i then Seq.empty
  else
    let val (args as {context = ctxt', params, asms, prems, ...}, st') = gen_focus flags ctxt i st;
        val (_,_,keep_prems,keep_schematics) = flags;
    in Seq.lifts (retrofit' ctxt args keep_prems keep_schematics i) (tac args st') st end;

val FOCUS_PARAMS = GEN_FOCUS (false, false,false,false);
val FOCUS_PREMS = GEN_FOCUS (true, false,false,false);
val FOCUS = GEN_FOCUS (true, true,false,false);
val FOCUS_KEEP = GEN_FOCUS (true,true,true,true);


fun SUBPROOF tac ctxt = FOCUS (Seq.map (Goal.check_finished ctxt) oo tac) ctxt;

end;

val SUBPROOF = Subgoal.SUBPROOF;
*}



end
