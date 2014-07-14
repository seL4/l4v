(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory SpecGraph
imports Main
begin 



ML {*
signature SPEC_GRAPH =
sig

  datatype spec_type =
    Definition | Function | PFunction | Constructor | 
    Inductive | Overloaded | Axiom | Case | Record
  
  type entry = {typ: typ,
              finished : bool,
              id : int, 
              contains : (int * int) list list,
              spec_type : spec_type, 
              term_size : int, 
              overloaded : bool,
              defs : thm list};
  

   type graph_entry = {name : string, 
                   theory : string, 
                   contains : (int * int) list list,
                   def_names: string list,
                   spec_type: spec_type,
                   size : int}
                   
                   

  type T
                   
                   
  val get_defs : Proof.context -> term -> (term * (spec_type * thm list)) * term list
  
  val graph_spec: Proof.context -> term -> (entry list * T)

  val empty: T

  val extend_spec: Proof.context -> term -> T -> T
  
  val add_definition_override: term list -> thm list -> spec_type -> local_theory -> local_theory
  
  val get_entries: Proof.context -> T -> term -> entry list

  val dest: T -> entry list
  
  val get_entry_by_id : T -> int -> entry
  
  val get_graph: theory -> T -> graph_entry Int_Graph.T
  
  val graph_from_term: Proof.context -> term -> graph_entry Int_Graph.T
    
  val get_named_constants: graph_entry Int_Graph.T -> string -> int list
  
  val is_definition: graph_entry Int_Graph.T -> string -> bool
  
  val encode_graph: graph_entry Int_Graph.T XML.Encode.T
  
  val decode_graph : graph_entry Int_Graph.T XML.Decode.T

  
end
*}

ML {* structure Spec_Graph : SPEC_GRAPH =
struct

fun choice xs = 
  let
    fun choice' x (y :: ys) = fold (fn chs => append ((choice' (x @ [chs]) ys))) y []
      | choice' x  [] = [x];
  in choice' [] xs end;

(*Carefully choose the target thy from ancestors to
  avoid tainting thm. This is very slow, but hopefully
  not run frequently.*)
fun instantiate thy (tenv : Envir.tenv,tyenv : Type.tyenv) thm = 
  let

    fun do_inst thy = 
    let
      val cert = Thm.cterm_of thy;
      val certT = Thm.ctyp_of thy;
    
      val dtenv = Vartab.dest tenv
      |> map (fn (xi,(T,t)) => pairself cert (Var(xi,T),t));
    
      val dtyenv = Vartab.dest tyenv
      |> map (fn (xi,(c,T)) => pairself certT (TVar(xi,c),T));
    in
      Drule.instantiate_normalize (dtyenv,dtenv) thm end
      
    val n = Context.theory_name (Thm.theory_of_thm thm)

    val nodes = (rev (Theory.nodes_of thy))

    val candidate_thys = List.drop (nodes,(find_index (fn thy => Context.theory_name thy = n) nodes))
    
  in get_first (fn thy => try do_inst thy) (candidate_thys) |> the end;

datatype spec_type = 
    Definition | Function | PFunction | Constructor | 
    Inductive | Overloaded | Axiom | Case | Record;

fun get_record_accessor ctxt (c as Const(n,T)) = 
  (let
    val thy = Proof_Context.theory_of ctxt
    val (a,b) = Term.dest_funT T
    val recT = Term.dest_funT b |> fst handle TYPE _ => a
    val (s,_) = Term.dest_Type recT
    val recname = (Long_Name.implode o fst o split_last o Long_Name.explode) s
    val info = Record.get_info thy recname
    |> Option.map 
      (fn info => 
        let
          val consts_of = map (term_of o Thm.lhs_of) (#update_defs info @ #select_defs info)
        in
          find_first (fn Const(n',_) => n = n' | _ => false) consts_of end)
    |> Option.join
    |> Option.map (fn t => [(Record,([t],[]))])
    
   
  in
    the_default [] info end handle TYPE _ => [] | Bind => [])
  | get_record_accessor _ _ = []
(*
fun get_record_spec ctxt t =
  let
    val thy = Proof_Context.theory_of ctxt
  in
    if is_record_accessor thy t then
      [*)
    
    
fun get_const_term t = 
  let 
    val t' = case t of (_ $ t $ _) => t
                                | (_ $ (_ $ t $ _)) => t 
                                | _ => error ("Failed to extract head constant from thm:\n" ^ (@{make_string} t));
    val (head,_) = strip_comb t';
  in head end;
  
fun get_const thm = get_const_term (prop_of thm)
    
fun get_function_spec ctxt (t as Const(n,T)) =
  let
    val info = Function.get_info ctxt t;
    
    fun is_this_const t = let val (Const(nm,_)) = get_const_term t in nm = n end
    
    val (spec,simps) = if #is_partial info 
      then (PFunction,#psimps info)
        ||> filter (fn thm => is_this_const (Thm.concl_of thm))
      else (Function,(the (#simps info)))
        ||> filter (fn thm => is_this_const (prop_of thm))
  in [(spec,(#fs info,simps))] end handle Empty => [];

fun get_real_const ctxt n = Const (n,Consts.the_constraint (Proof_Context.consts_of ctxt) n)  
  
fun get_constr ctxt (c as (Const(n,T))) = 
  let
    val thy = Proof_Context.theory_of ctxt;
    val t = Datatype.info_of_constr thy (n,T)
    |> Option.map (fn _ => (get_real_const ctxt n));
  in 
    case t of SOME t => [(Constructor,([t],[]))] 
            | NONE => [] 
  end;
  
fun get_case ctxt (c as (Const(n,T))) = 
  let
    val thy = Proof_Context.theory_of ctxt;
    val t = Datatype.info_of_case thy n
    |> Option.map (pair (get_real_const ctxt n));
  in 
    case t of SOME (t,info) => [(Case,([t],#case_rewrites info))] 
            | NONE => [] 
  end;


structure Rules = Generic_Data
(
  type T = (spec_type * (term list * thm list)) Item_Net.T;
  val empty : T =
    Item_Net.init
      (fn ((spec1,(ts1,ths1)), (spec2,(ts2,ths2))) =>
        eq_list (op aconv) (ts1,ts2) andalso
        eq_list Thm.eq_thm_prop (ths1, ths2)
        andalso spec1 = spec2)
      (#1 o #2);
  val extend = I;
  val merge = Item_Net.merge;
);

fun get_override ctxt t = Item_Net.retrieve (Rules.get (Context.Proof ctxt)) t

fun add_definition_override ts thms spec_type lthy = lthy
  |> Local_Theory.declaration {syntax = false, pervasive = true}
    (fn phy => fn context => context 
      |> Rules.map (Item_Net.update ((spec_type,(map (Morphism.term phy) ts, map (Morphism.thm phy) thms)))));
  


fun truncate base suffix = if String.isSuffix suffix base then
    String.substring (base,0,size base - size suffix) else base;

    
(* Used to retrieve definitions which were declared outside the normal mechanisms. *)
fun deep_inspect ctxt (Const (nm,_))=
  let
    val thy = (Proof_Context.theory_of ctxt);
    val thys = rev (Theory.nodes_of thy);
    
    val (thy,specs) = get_first (fn thy => Option.filter (not o null o snd) (thy,(Defs.specifications_of (Theory.defs_of thy) nm))) thys
    |> the_default (thy,[]);

    fun proc_spec (spec : Defs.spec) = case (#def spec) of
    SOME def => (case (try (Global_Theory.get_thm thy) (truncate def "_raw")) of
      SOME thm => cons (Definition,([get_const thm],[thm]))
      | NONE => I)
    | NONE => I;

  in fold proc_spec specs [] end;
    
fun typ_matches TU  = (Type.raw_match TU Vartab.empty;true)
  handle Type.TYPE_MATCH => false;


fun safe_matches (t,t') = 
  typ_matches ( t, (Logic.incr_tvar (maxidx_of_typ t + 1) t'));

fun match_const (Const(n,T),Const(n',T')) = if n = n' then safe_matches (T,T') else false
  | match_const _ = false


fun get_defs ctxt (c as Const (n,T)) =
  let
    
    val c_gen = get_real_const ctxt n
  
    val thy = Proof_Context.theory_of ctxt

    fun spec_trans s = case s of 
       Spec_Rules.Inductive => Inductive
      | Spec_Rules.Co_Inductive => Inductive
      | Spec_Rules.Equational => Definition
      | Spec_Rules.Unknown => Axiom

    fun incr_indexes t t' = Logic.incr_indexes ([],maxidx_of_term t + 1) t'

    fun retrieve t = map (apfst spec_trans) (Spec_Rules.retrieve ctxt t)

    fun trace_match t t' = match_const (t,t')
    
    val specs = get_first (fn f => Option.filter (not o null) (f c)) 
      [get_record_accessor ctxt,
       get_override ctxt,
       get_case ctxt,
       get_function_spec ctxt,
       get_constr ctxt,
       retrieve,
       deep_inspect ctxt]
      |> (fn t => Option.getOpt (t,[]));

    fun do_map (spec_type,(ts',thms)) =
      find_first (fn t' => trace_match t' c) ts'
      |> Option.map (fn t' => (t',(spec_type,thms)));
    
    fun get_overloads (_,(ts',_)) = find_first (fn t' => trace_match c_gen t') ts';

  in
    case specs of 
        [] => ((c_gen,(Axiom,[])),[])
      | _ => 
        case (map_filter do_map specs) of 
          [] => ((c_gen,((Overloaded),[])),(map_filter get_overloads specs)) 
          | [t] => (t,[])
          | ts => (warning ("Overlapping overloaded specifications. " ^ (@{make_string} (ts,specs)) ^ " picking the first one arbitrarily.");(hd ts,[]))
  end;


fun safe_pattern_zip pats Ts = 
let
  val maxidx_pat = fold (fn pat => fn i => Int.max (maxidx_of_typ pat,i)) pats 0;
  
  fun do_map T i = 
    let val T' = Logic.incr_tvar (i + 1) T in (T',maxidx_of_typ T') end;
    
  in (pats ~~ fst (fold_map do_map Ts (maxidx_pat))) end;
    

  
type entry = {typ: typ,
              finished : bool,
              id : int, 
              contains : (int * int) list list,
              spec_type : spec_type, 
              term_size : int, 
              overloaded : bool,
              defs : thm list};

              
              
type T = {symtab : entry list Symtab.table, maxidx : int, fuel : int}

fun dest (net : T) = Symtab.dest (#symtab net)
  |> map snd
  |> flat

val (empty : T) = {symtab = Symtab.empty, maxidx = 0, fuel = 1000000}

fun map_T f g (t : T) = ({symtab = f (#symtab t), maxidx = g (#maxidx t), fuel = if #fuel t = 0 then error "Ran out of time" else #fuel t - 1} : T)

fun map_symtab f = map_T f I

val incr_maxidx = map_T I (fn i => i + 1)

fun eq_id (e : entry,e' : entry) = (#id e = #id e')

fun is_overloaded (Overloaded) = true
  | is_overloaded _ = false

fun new_entry nm typ defs spec_type net =
  let
  
    val entry = ({typ = typ, id = #maxidx net,
    contains = [], spec_type = spec_type, term_size = 0, 
    overloaded = is_overloaded spec_type, defs = defs, finished = false} : entry);

    val ex_entries = Symtab.lookup_list (#symtab net) nm

    val _ = if member (op =) (map #typ ex_entries) typ then 
      error ("Entry exists for: "^ nm ^ " with typ: " ^ (@{make_string} typ) ^ "." ^ (@{make_string} (ex_entries,entry)))
    else ()

    val net' = map_symtab (Symtab.insert_list eq_id (nm,entry)) net
    |> incr_maxidx                 
    
  in (entry,net') end;

fun get_entry_by_id (net : T) i = snd (the (find_first (fn (_,(e : entry)) => #id e = i) (Symtab.dest_list (#symtab net))));

fun Symtab_update_list eq (key,x) symtab = symtab
  |> Symtab.remove_list eq (key,x)
  |> Symtab.insert_list eq (key,x)

fun update_entry nm entry = map_symtab (Symtab_update_list eq_id (nm,entry))
 
  
fun finish_entry (entry : entry) (term_size,contains) overloaded = 
  ({typ = #typ entry,id = #id entry, contains = contains, spec_type = #spec_type entry, term_size = term_size,
  overloaded = overloaded orelse #overloaded entry, defs = #defs entry, finished = true} : entry);
                                                                                   




fun least_general (es,nm,T) thy Ts =
  let
    fun is_general T = exists (fn T' => T <> T' andalso safe_matches (T,T')) Ts
  in
    case (filter_out is_general Ts) of [T] => T 
    | Ts' => (warning ("No least general overloaded type known for " ^ nm ^
    " with typ " ^ (@{make_string} T) ^ ". Existing types are: " ^ (@{make_string} Ts') ^ " picking one arbitrarily."); hd Ts') end;

    
(*Avoid spurious overloadings*)
fun trivial_env (tyenv : Type.tyenv) =
  let    
    val ts = (Vartab.dest tyenv)
    
    val ts' = ts
    |> ListPair.unzip
    |> snd
    
    fun trivial (_,(_,(TVar(_,_)))) = true
       | trivial _ = false
       
    val is_trivial = (forall trivial ts) andalso not (has_duplicates (fn ((_,T),(_,T')) => T = T') ts')   
    
  in
     is_trivial end
    
    
fun calculate_overloads ctxt (net : T) (ts,(entry : entry)) = 
  let
    val thy = Proof_Context.theory_of ctxt
    
    val (nm,_) = (the (find_first (fn (_,(e : entry)) => #id e = #id entry) (Symtab.dest_list (#symtab net))));
    
    val ovts = Symtab.lookup_list (#symtab net) nm
    |> filter_out (fn e => #id e = #id entry)
    |> map #typ
    
    fun calculate_overload t = 
      let
       
        val ovts' = map (Logic.incr_tvar (maxidx_of_typ t + 1)) ovts
          |> filter (fn ovt => typ_matches (t,ovt))              

      in
        if null ovts' then NONE else SOME (t,ovts') 
      end;

                                 
  in if not (#overloaded entry) then [] else (map_filter (calculate_overload o fastype_of) ts) end;
       
  
fun spec_size' ctxt t (cs,(net : T)) =
  let
   
    val thy = Proof_Context.theory_of ctxt;

    fun add_to (e : entry) c (i,es) =
      let
        fun insert' cs = insert (op =) (c : term) cs;
                            
        fun do_rec ((i,cs,e') :: es) = if (#id e) = (#id e') then ((i + 1,insert' cs,e') :: es) else ((i,cs,e') :: do_rec es)
          | do_rec [] = [(1,[c],e)];
        
       in (i + 1,do_rec es) end;

    fun try_dest_implies t = (t |> Thm.dest_implies |> snd) handle TERM _ => t

    fun process_def s t' = (case s of
    Definition => Local_Defs.meta_rewrite_rule ctxt
        #> cprop_of
        #> try_dest_implies
        #> Thm.dest_equals_rhs
        #> term_of
  | Function => Local_Defs.meta_rewrite_rule ctxt
        #> cprop_of
        #> try_dest_implies
        #> Thm.dest_equals_rhs
        #> term_of
  | Case => Local_Defs.meta_rewrite_rule ctxt
        #> cprop_of
        #> try_dest_implies
        #> Thm.dest_equals_rhs
        #> term_of
   | PFunction => Local_Defs.meta_rewrite_rule ctxt
        #> cprop_of
        #> Thm.dest_implies
        #> snd
        #> Thm.dest_equals_rhs
        #> term_of
   | _ => Thm.prop_of) t' handle TERM (e,t'') => error ("Failed to process def: " ^ e ^ (@{make_string} (t',s,t'')));

   (*Catch edge cases with hidden consts*)
   
   

   fun add_entry has_overloaded c (t as (Const(n,T')),(spec_type,defs)) ovs (cs,(net : T)) = 
      let
        val T = fastype_of c;

        val env = Type.raw_match (T',Logic.incr_tvar (maxidx_of_typ T' + 1) (Type.strip_sorts T)) Vartab.empty handle TYPE_MATCH => error (@{make_string} (T',Type.strip_sorts T));
               
        val (entry,net') = new_entry n T' defs spec_type net;
        
        val ((_,ovs'),net') =  fold (find true) ovs ((0,[]),net')
        
        
        val ((szs,css),net'') = fold_map (fn thm => fn net => spec_size' ctxt (process_def spec_type thm) ((0,[]),net)) defs net'
        |>> ListPair.unzip
                
        
        val (ts,ovss') = fold (fn (_,ov,e) => append (calculate_overloads ctxt net'' (ov,e))) (flat css) []
          |> ListPair.unzip
          ||> choice;
        
          
        fun add_extra (tyenv,t) (overloaded,net) =    
        let
          val defs' = map (instantiate thy (Vartab.empty,tyenv)) defs;
          val (_,net') = add_entry true t (t,(spec_type,defs')) ovs ((0,[]),net) ;          
        in
          (true,net') end;
          
        val (ts') = if has_overloaded then [] else ovss'
        |> map_filter (fn ovs => SOME (fold (fn (ts,ov) => Sign.typ_match thy (ts,ov)) (safe_pattern_zip ts ovs) (Vartab.empty)) handle Type.TYPE_MATCH => NONE)
        |> map_filter (fn tyenv => if Vartab.is_empty tyenv orelse trivial_env tyenv then NONE else SOME ((tyenv,Const(n,Envir.norm_type tyenv T'))))

        
        val (overloaded,net''') = fold add_extra ts' (false,net'')

        val entry' = finish_entry entry (Integer.sum szs,map (map (fn (i,_,e) => (i,#id e))) css) overloaded        
        
      in (add_to entry' c cs,update_entry n entry' net''') end
     
    and find has_overloaded (c as Const (n,T)) (cs,net : T) =
    let
      val ((Const(n',T'),(spec_type,defs)),ovs) = get_defs ctxt c
      val results = Symtab.lookup_list (#symtab net) n'
      |> filter (fn e => safe_matches (#typ e,T))

    in
      (case results of 
      [e] => if is_overloaded (#spec_type e) andalso not (is_overloaded spec_type) andalso not (#finished e)
             then add_entry has_overloaded c (Const(n',T'),(spec_type,defs)) ovs (cs,net)
             else (add_to e c cs,net)      
     | [] => (add_entry has_overloaded c (Const(n',T'),(spec_type,defs)) ovs (cs,net))
     | es => 
      (let
        val T = least_general (es,n,T) thy (fold (cons o #typ) es [])
        val e = the (find_first (fn e => T = #typ e) es)
      in
        (add_to e c cs,net) end))
    end

   | find _ _ ((i,cs),net) = ((i + 1,cs),net)     
  in
    fold_aterms (find false) t (cs,net) end;

    
fun get_entries ctxt (net : T) t = 
  let
    fun do_get_entry (c as Const(n,T)) =
      let
        val thy = Proof_Context.theory_of ctxt
        val ((Const(n',T'),(spec_type,defs)),ovs) = get_defs ctxt c
        val results = Symtab.lookup_list (#symtab net) n'
          |> filter (fn e => safe_matches (#typ e,T))
      in
        case results of
          [e] => SOME e
          | [] => NONE
          | es => 
            (let
              val T = least_general (es,n,T) thy (fold (cons o #typ) es [])
              val e = the (find_first (fn e => T = #typ e) es)
             in SOME e end)
       end
       | do_get_entry _ = NONE
  
    
  in fold_aterms ((fn (SOME e) => cons e | NONE => I) o do_get_entry) t [] end;    
    
fun graph_spec ctxt t = 
  let
    val (_,net) = spec_size' ctxt (singleton (Variable.polymorphic ctxt) t) ((0,[]),empty);

  in (get_entries ctxt net t,net) end;

fun extend_spec ctxt t net = 
  let
    val (_,net') = spec_size' ctxt t ((0,[]),net);

  in net' end;

type graph_entry = {name : string, 
                   theory : string, 
                   contains : (int * int) list list, 
                   spec_type: spec_type,
                   def_names: string list,
                   size : int}


fun declared_theory thy nm=
  let
    val thys = rev (Theory.nodes_of thy);
    
    fun is_declared thy = (Consts.the_const (Sign.consts_of thy) nm;true) handle TYPE _ => false

  in find_first is_declared thys
    |> the handle Option => error ("Can't find constant " ^ nm ^ " in ancestors") end;


      
      

    
fun get_graph thy (net : T) =
  let
    val flattened = Symtab.dest (#symtab net)
    |> map (fn (n,e) => map (pair n) e)
    |> flat    
    
        
    
    fun make_graph_entry (n,entry : entry) = 
    let
      
     fun add_def_name def = if Thm.has_name_hint def then
      cons (Thm.get_name_hint def) else I

     fun get_theory (def :: _) = Thm.theory_of_thm def
       | get_theory _ = (declared_theory thy n)
    
      val gentry = ({name = n, 
                   theory = get_theory (#defs entry) |> Context.theory_name, 
                   contains = #contains entry, 
                   spec_type = #spec_type entry,
                   def_names = fold add_def_name (#defs entry) [],
                   size = #term_size entry} : graph_entry)
       
      val edges = map (map snd) (#contains entry)
      |> flat
    in ((#id entry,gentry),edges) end
            
  in 
    Int_Graph.make (map make_graph_entry flattened)
    end;

    
fun graph_from_term ctxt t =
  let
    val (e,g) = graph_spec ctxt t
  in
    get_graph (Proof_Context.theory_of ctxt) g end;

local
  open XML.Encode
    
fun spec_type_tostring spec_type = case spec_type of   
  Definition => "Definition"
 | Function => "Function"
 | PFunction => "PFunction"
 | Constructor => "Constructor"
 | Inductive => "Inductive"
 | Overloaded => "Overloaded"
 | Axiom => "Axiom"
 | Case => "Case"
 | Record => "Record"
 

in


fun entry_to_properties (e : graph_entry) = []
  |> Properties.put ("name",#name e)
  |> Properties.put ("theory", #theory e)
  |> Properties.put ("size", signed_string_of_int (#size e))
  |> Properties.put ("spec_type", spec_type_tostring (#spec_type e))

fun encode_entry (e as {name, theory, contains, spec_type, def_names, size} : graph_entry) =
  (pair (pair properties (list (list (pair int int)))) (list string)) ((entry_to_properties e,contains),def_names)

val encode_graph = Int_Graph.encode XML.Encode.int encode_entry  


end

local 
  open XML.Decode

fun spec_type_fromstring str = case str of
  "Definition" => Definition
 | "Function" => Function
 | "PFunction" => PFunction
 | "Constructor" => Constructor
 | "Inductive" => Inductive
 | "Overloaded" => Overloaded
 | "Axiom" => Axiom
 | "Case" => Case
 | "Record" => Record
 | _ => error "Unknown spec type"
 
 
fun properties_to_entry ((props,contains),def_names) =
  let
    fun get s = Properties.get props s |> the
  in
    ({name = get "name", theory = get "theory",
     size = Int.fromString (get "size") |> the,
     spec_type = spec_type_fromstring (get "spec_type"),
     contains = contains,
     def_names = def_names} : graph_entry) end
 
in

val decode_entry  =
  (pair (pair properties (list (list (pair int int)))) (list string))

fun decode_graph body = Int_Graph.decode XML.Decode.int decode_entry body
|> Int_Graph.map (fn _ => properties_to_entry)

end

fun get_named_constants graph nm = Int_Graph.fold (fn (k,({name,...},_)) => if name = nm then cons k else I) graph []

fun is_definition graph nm = Int_Graph.fold (fn (_,({def_names,...},_)) => fn b => if member (op =) def_names nm then true else b) graph false
    

end;
*}

(*
ML {* 

local

val _ = Outer_Syntax.command @{command_spec "spec_graph"} "write out specification graph of a given term" 
        (Parse.term -- Parse.path >> (fn (t,n) => 
          Toplevel.keep (fn state =>
            let
              val ctxt = Toplevel.context_of state
              val t = Syntax.read_term ctxt t
            in  write_graph (Spec_Graph.graph_from_term ctxt t) n end)))
in            
end
*}
*)

ML {* val if_true = Global_Theory.get_thm  (Thy_Info.get_theory "HOL") "if_True" *}
ML {* val if_false = Global_Theory.get_thm  (Thy_Info.get_theory "HOL") "if_False" *}

local_setup {* Spec_Graph.add_definition_override [@{term "If"}] [if_true,if_false] Spec_Graph.Case *}

ML {* Spec_Graph.graph_spec @{context} @{term "Num.numeral_class.numeral"}  |> snd |> Spec_Graph.get_graph @{theory}*}

ML {* fun get_def_thms str ctxt ts = 
  let
    val this_thy = Proof_Context.theory_of ctxt
  
    val nthy = Option.map (fn str => Context.this_theory this_thy str |> Context.theory_name) str
  
    val consts = map (snd o snd o fst o Spec_Graph.get_defs ctxt) ts
    |> flat
    |> distinct (Thm.eq_thm_prop)
   
    fun do_filter nthy t =
      let
        val nthys = map Context.theory_name (Theory.nodes_of (Thm.theory_of_thm t))
      in
        member (op =) nthys nthy end
        
    val consts' = (case nthy of SOME nthy => filter (do_filter nthy) | NONE => I) consts
   
    
  in
    consts' end *}
  
(*Depends on theory name. Kind of ugly*)    
method_setup unfold_all_consts = {* Scan.lift (Scan.option (Args.name)) >> 
  (fn str => fn ctxt => SIMPLE_METHOD (fn t => CHANGED_PROP (Local_Defs.unfold_tac ctxt (get_def_thms str ctxt (map Const (Term.add_consts (prop_of t) [])))) t)) *} 

method_setup unfold_consts = {* Scan.repeat1 Args.term >> 
  (fn ts => fn ctxt => SIMPLE_METHOD (fn t => CHANGED_PROP (Local_Defs.unfold_tac ctxt (get_def_thms NONE ctxt ts)) t)) *}  

end
