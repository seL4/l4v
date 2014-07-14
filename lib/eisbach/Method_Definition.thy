(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Method_Definition
imports Subgoal
keywords
  "method_definition" :: thy_decl and "facts" and "methods" and
  "ML_method_definition" :: thy_decl % "ML" and
  "match" and
  "srcs" and
  "postfix_meth"
  "mixfix_meth" "\<mapsto>" "\<bar>" "\<Rightarrow>" "@" "#"
  
begin


(*Normalize term environment wrt to type environment*)
ML {* fun normalize_env (tyenv,tenv) =
  let
    val tenv' = Vartab.map (K (fn (T,t) 
                      => (Envir.subst_type tyenv T,Envir.subst_term_types tyenv t))) tenv
  in
    (tyenv,tenv') end; *}
                                        
(*FIXME: Belongs in Args*)
ML {* fun toks_of src = let val ((_,toks),_) = Args.dest_src src in toks end;*}

ML {* fun map_toks f src = let val ((name,toks),pos) = Args.dest_src src in Args.src ((name,f toks),pos) end;*}

section {* Rich methods *}

ML {*
signature RICH_METHOD =
sig
 
  type basic_rich_method = (string list * term list * (thm list) list * tactic list) -> Proof.context -> tactic
  
  
  datatype rich_method =
    Basic of basic_rich_method |
    Source of Args.src |
    Infix of string * (rich_method * rich_method) |
    Postfix of (string * string list) * rich_method |
    Match_Bind of Args.src * (Args.src * rich_method) list |
    Focus of term * rich_method
    
  type rich_method_args = string list * term list * ((bool * string) list) * (string list)  
    
  val fold_map_src: bool -> (Args.src -> 'a -> Args.src * 'a) -> rich_method -> 'a -> rich_method * 'a
  val map_src: bool -> (Args.src -> Args.src) -> rich_method -> rich_method
  val fold_src: bool -> (Args.src -> 'a -> 'a) -> rich_method -> 'a -> 'a
  val the_method : Proof.context -> string -> rich_method_args * rich_method
  val check: Proof.context -> xstring * Position.T -> string * (rich_method_args * rich_method)

  val define_rich_method: binding ->
    (binding * typ option * mixfix) list -> string list -> (bool * string) list -> string list -> rich_method ->
    Proof.context -> local_theory
  val define_rich_method_cmd: binding ->
    (binding * string option * mixfix) list -> string list -> (bool * string) list -> string list -> rich_method ->
    Proof.context -> local_theory
  val set_basic_method : basic_rich_method -> Context.generic -> Context.generic
  val tactic_of : Proof.context -> thm list -> rich_method -> tactic
  val apply_rich_method : rich_method -> Position.range -> Proof.state -> Proof.state Seq.result Seq.seq

  val parse_rich_method: (rich_method * Position.range) parser
  
  val rich_method_as_text: rich_method -> Method.text
  val collect_global_syntax: Context.generic -> unit

  val add_method_fact: xstring -> thm -> Context.generic -> Context.generic
  val del_method_fact: xstring -> thm -> Context.generic -> Context.generic
  
  val get_method_fact: Context.generic -> xstring -> thm list

  val clear_method_fact: xstring -> Context.generic -> Context.generic

  val premsN: string

  val free_thm : thm
end;

structure Rich_Method: RICH_METHOD =
struct

(* type rich_method *)

type basic_rich_method = (string list * term list * (thm list) list * tactic list) -> Proof.context -> tactic

(* Literal strings, terms, facts, methods *)
type rich_method_args = string list * term list * ((bool * string) list) * (string list);


         
datatype rich_method =
    Basic of basic_rich_method |
    Source of Args.src |
    Infix of string * (rich_method * rich_method) |
    Postfix of (string * string list) * rich_method |
    Match_Bind of Args.src * (Args.src * rich_method) list |
    Focus of term * rich_method

fun src_term_lift f t a =
  let
    val src = Args.src (("",[Token.mk_term t]),Position.none)
    val (src',a') = f src a
    val ((_,[tok]),_) = Args.dest_src src'
    val SOME (Token.Term t') = Token.get_value tok
  in
    (t',a') end;
    
fun fold_map_src focus f src (a : 'a) =
let

fun fold_map_src' (Source src) a =
      let val (src', a') = f src a in (Source src', a') end
  | fold_map_src' (Infix (x,(text1,text2))) a =
      let val ([text1',text2'], a') = fold_map fold_map_src' [text1,text2] a
      in (Infix (x,(text1',text2')), a') end
  | fold_map_src' (Postfix (x,text)) a =
      let val (text', a') = fold_map_src' text a
      in (Postfix (x,text'), a') end
  | fold_map_src' (Focus (t,text)) a = if (not focus) then (Focus (t,text),a) else
      let 
        val (t',a') = src_term_lift f t a
        val (text', a'') = fold_map_src' text a'
      in (Focus (t',text'), a'') end
  | fold_map_src' (Match_Bind (src,matches)) a =
      let val (t',a') = (f src a)
          val (matches',a'') = fold_map fold_matches matches a'
      in (Match_Bind (t',matches'),a'') end
  | fold_map_src' (Basic _) _ =  error "Found basic rich_method in combinator tree"
and fold_matches (t,rm) a =
  let
    val (t',a') = (f t a)
    val (rm',a'') = fold_map_src' rm a'
  in
    ((t',rm'),a'') end;
in
  fold_map_src' src a end;
      

fun fold_src focus f src a = #2 (fold_map_src focus (fn src => fn a => (src, f src a)) src a);
fun map_src focus f src = #1 (fold_map_src focus (fn src => fn () => (f src, ())) src ());



local

  fun replace_value tok (terms,facts) =
    (case (Token.get_value tok, (terms,facts)) of
      (SOME (Token.Typ _), (t :: rest,_)) =>
        (Token.map_value (K (Token.Typ (Logic.dest_type t))) tok, (rest,facts))
    | (SOME (Token.Term _), (t :: rest,_)) =>
        (Token.map_value (K (Token.Term t)) tok, (rest,facts))
    | (SOME (Token.Fact _), (_,fact :: rest)) =>
        (Token.map_value (K (Token.Fact fact)) tok, (terms,rest))
    | _ => (tok, (terms,facts)));
  
    
  fun replace_values src t =
    let
      val ((name, toks), pos) = Args.dest_src src;
      val (toks', t') = fold_map replace_value toks t;
      val src' = Args.src ((name, toks'), pos);
    in (src', t') end;

in

(* Map terms/facts as list across rich method *)
fun burrow_values_result focus f g (terms,text) =
  let
    

    fun cons_facts tok (terms,facts) =
      (case Token.get_value tok of
        SOME (Token.Typ T) => ((Logic.mk_type T) :: terms,facts)
      | SOME (Token.Term t) => (t :: terms,facts)
      | SOME (Token.Fact fact) => (terms,fact :: facts)
      | _ => (terms,facts));

    val (body_terms,body_facts) = 
      apsnd rev (apfst rev (fold_src focus (fn src => fold cons_facts (toks_of src)) text ([],[])))
    val (a,ts) = g (terms @ body_terms)
    val (terms',body_terms') = chop (length terms) ts;
    val body_facts' = burrow f (body_facts);
    
    val (text',([],[])) = fold_map_src focus replace_values text (body_terms',body_facts');

  in (a,(terms', text')) end;
  
fun burrow_values focus f g (args,text) = snd (burrow_values_result focus f (pair () o g) (args,text))

end;


(*Simultaneous instantiation, for application of terms to rich methods*)
fun instantiate_values focus ctxt tyenv insts text =
  let
    val tyenv' = Type.raw_unifys (ListPair.unzip (map (fn ((xi,T),t) => (T,fastype_of t)) insts)) tyenv;
    val instTs = map (fn (xi,(S,T)) => ((xi,S),T)) (Vartab.dest tyenv');
    
    val insts' = map (fn ((xi,T),t) => ((xi,Term_Subst.instantiateT instTs T),(Term_Subst.instantiate (instTs,[]) t))) insts;


    fun do_instantiate [] = []
      | do_instantiate ts = ts
      |> map Logic.mk_term
      |> Logic.mk_conjunction_list
        |> Term_Subst.instantiate (instTs,[]) (* FIXME: More thinking about why this is necessary*)
        |> Term_Subst.instantiate (instTs,insts')
        |> Logic.dest_conjunction_list
        |> map Logic.dest_term;
  
    val ([],text') = burrow_values focus I do_instantiate ([],text);
    
  in
    text' end;
    
fun instantiate_values_env focus ctxt (instTs,insts) text =
  let   
    val insts_env = map (fn (xi,(T,t)) => ((xi,T),t)) (Vartab.dest insts);
  in
    instantiate_values focus ctxt instTs insts_env text end;

(*Internal dummy theorem used as placeholder for matching and parameter passing*)

local 
val free_thmN = "Method_Definition_free_thm";
in

val free_thm = Thm.tag_rule (free_thmN,"") Drule.dummy_thm;
  
fun is_free_thm thm = Option.isSome (AList.lookup (op =) (Thm.get_tags thm) free_thmN);
 
end;

fun is_free_fact [thm] = is_free_thm thm
    | is_free_fact _ = false;

(*Token value mapping based on token identifier*)
fun gen_instantiate focus g insts text =
  let
    fun do_instantiate content v =
    let
      val optv = AList.lookup (op =) insts content
    in
      the_default v (Option.map (g v) optv) end;

    fun instantiate_tok tok = 
      let
        val content = Token.content_of tok;
      in
        Token.map_value (do_instantiate content) tok end;
        
    val text' = map_src focus (map_toks (map instantiate_tok)) text
  
  in
    text' end;

(*FIXME: Does not respect match scope (i.e. facts cannot be shadowed).
         Fix1: Pass around fact environment
         Fix2: Unique identifiers for free facts*)
fun instantiate_facts focus insts text =
  let
    fun do_instantiate (Token.Fact f) f' = if is_free_fact f then (Token.Fact f') else (Token.Fact f)
      | do_instantiate v x = v
  in
    gen_instantiate focus do_instantiate insts text end;

fun instantiate_strs insts text =
  let
    fun do_instantiate (Token.Text t) t' = (Token.Text t')
      | do_instantiate v x = v
  in
    gen_instantiate false do_instantiate insts text end;
      

fun transform_rich_method phi ((args,terms,facts,meths),richm) =
  let
    val (terms',richm') = burrow_values true (Morphism.fact phi) (map (Morphism.term phi)) (terms,richm);
  in
    ((args,terms',facts,meths),richm') end;

  
(*FIXME: Clagged from Args. More permissive inner src parsing
  Necesarry to correctly nest rich method parsers for higher order methods *)

fun token atom = Scan.ahead Parse.not_eof --| atom;

val argument_kinds =
 [Token.Ident, Token.LongIdent, Token.SymIdent, Token.Var, Token.TypeIdent, Token.TypeVar,
  Token.Nat, Token.Float, Token.String, Token.AltString, Token.Verbatim];


fun parse_args is_symid =
  let
    
    fun is_symid_permissive false = is_symid
      | is_symid_permissive true = (fn s =>
        s <> "(" andalso s <> ")" andalso s <> "[" andalso s <> "]")
    
    fun argument blk =
      Parse.group (fn () => "argument")
        (Scan.one (fn tok =>
          let val kind = Token.kind_of tok in
            member (op =) argument_kinds kind orelse
            Token.keyword_with (is_symid_permissive blk) tok
          end))

    fun args blk x = Scan.optional (args1 blk) [] x
    and args1 blk x =
      ((Scan.repeat1
        (Scan.repeat1 (argument blk) ||
          argsp "(" ")" ||
          argsp "[" "]")) >> flat) x
    and argsp l r x =
      (token (Parse.$$$ l) ::: Parse.!!! (args true @@@ (token (Parse.$$$ r) >> single))) x;
  in (args, args1) end;

fun parse1 is_symid = #2 (parse_args is_symid) false;
(*End of clag*)

    
(* Wraps an attribute to gracefully error
   when invoked on a free thm by producing a new free_thm.*)

(* TODO: Analysis of instances in which this creates incorrect/inconsistent closures*)
fun wrap_attribute att (context,thm) =

  if (is_free_thm thm) then
    case (try att (context,thm)) of
      SOME (context',thm') => (context',thm')
    | NONE => (NONE,SOME free_thm)
  else 
      att (context,thm) handle
        THM (err,errno,thms) => 
          if (List.exists is_free_thm thms) then (NONE,SOME free_thm)
          else raise THM (err,errno,thms)


(* maintain rich methods *)

structure Data = Generic_Data
(
  type T = (rich_method_args * rich_method) Name_Space.table;
  val empty : T = (Name_Space.empty_table "rich_method");
  fun extend (tab) : T = (tab);
  fun merge ((tab1), (tab2)): T = (Name_Space.merge_tables (tab1, tab2));
);

(* Recreated core tacticals go here. Necessary due to "apply" rebinding escaping theory import chain
   as a result of stateful Isar syntax  *)
   
val global_method_syntax = Unsynchronized.ref ([] : (string * (rich_method_args * rich_method)) list)

structure Method_Syntax = Generic_Data
(
  type T = (string * (rich_method_args * rich_method)) list
  val empty : T = []
  fun extend (tab) : T = (tab);
  fun merge (tab1,tab2): T = (union (eq_fst (op =)) tab1 tab2) (*FIXME: Syntax clashes*)
);

fun get_method_from_syntax ctxt s = 
  case (AList.lookup (op =) (Method_Syntax.get (Context.Proof ctxt)) s) of
  SOME m => m
| NONE => (CRITICAL (fn () => case (AList.lookup (op =) (!global_method_syntax) s) of
        SOME m => m
      | NONE => error ("Couldn't find method for tactical " ^ s)))

fun add_method_syntax a = Method_Syntax.map (AList.update (op =) a)

val get_methods = Data.get o Context.Proof;

(*TODO: Error if we don't run inside the correct theory file (this one) to prevent accidentally
  clobbering global syntax *)
  
fun collect_global_syntax context = 
  (CRITICAL (fn () => 
    Unsynchronized.change global_method_syntax (K (Method_Syntax.get context))))

fun the_method ctxt name =
  (case Symtab.lookup (#2 (get_methods ctxt)) name of
    SOME meth => meth
  | NONE => error ("Unknown rich method " ^ quote name));

fun check ctxt = Name_Space.check (Context.Proof ctxt) (get_methods ctxt);


fun add_rich_method strict bind args meth = 
  Context.proof_map (fn context => 
    (Data.map) (#2 o Name_Space.define context strict (bind,(args,meth))) context)
    

val premsN = "prems"    
 
(* Instantiate nested rich method based on focused conclusion and bind 
   focused assumptions to local fact *)
fun focus_context (focus : Subgoal2.focus) t txt =
  let
    val ctxt = #context focus;
    val concl = HOLogic.dest_Trueprop (term_of (#concl focus));
    val Var (conclxi,conclT) = t;   
    val txt' = txt
    |> instantiate_facts false [(premsN, (#prems focus))]  
    |> instantiate_values false ctxt Vartab.empty [((conclxi,conclT),concl)];
  in
    (ctxt,txt') end;

(* Core apply semantics, generalized over interpretation functions.

   f: Evaluate leaf method/rich_method and arguments (from src) into thm sequence
   g: Evaluate given rich_method (already parsed) with provided arguments
   match: evaluate match and instantiate nested rich methods based on results
          (produced ctxt is for legacy purposes and is the original ctxt in practice)
   *)
fun seq_methods match f g ctxt using rmethod thm =
  let         
    fun eval ctxt (Source src) thm = (f ctxt using src) thm
      | eval ctxt (Infix (s,(txt1,txt2))) thm = g ctxt using
        ((get_method_from_syntax ctxt s),([],[],[],[(txt1,Position.none),(txt2,Position.none)])) thm
      | eval ctxt (Postfix ((s,arg),txt)) thm = g ctxt using
        ((get_method_from_syntax ctxt s),(arg,[],[],[(txt,Position.none)])) thm
      | eval ctxt (Match_Bind (src,m1)) thm = (fn st => Seq.maps (fn (ctxt,m1') => eval ctxt m1' st) (match src ctxt m1)) thm
      | eval ctxt (Focus (t,txt)) thm = Subgoal2.FOCUS_KEEP (fn focus => 
        let 
          val (ctxt',txt') = focus_context focus t txt;
        in eval ctxt' txt' end) ctxt 1 thm
      | eval _ (Basic _) _ = error "Found basic rich_method in combinator tree"
  in eval ctxt rmethod thm end; 
  
(* Shallow rich_method traversal, generalized over interpretation functions.
   Used to generate closure and export terms.
   h: map src (for exporting)
   match: create matched context to fix bound patterns
   f: "execute" src (for closure) *)
     
fun map_methods h match focus f ctxt rmethod = 
let
  fun eval ctxt (Source src) = let val _ = f ctxt src in (Source (h ctxt src)) end
    | eval ctxt (Infix (s,(txt1,txt2))) = Infix (s,(eval ctxt txt1,eval ctxt txt2))
    | eval ctxt (Postfix (s,txt)) = Postfix (s,(eval ctxt txt))
    | eval ctxt (Match_Bind (src,txt)) = 
      let 
        val matches = match src ctxt txt
        val i = map2 (fn (src,rm) => fn ctxt => (h ctxt src,eval ctxt rm)) txt matches
      in (Match_Bind (h ctxt src,i)) end
    | eval ctxt (Focus (t,txt)) = Focus (fst (src_term_lift (fn src => K(h ctxt src,())) t ()),(eval (focus ctxt) txt))
    | eval _ (Basic _) = error "Found basic rich_method in combinator tree"
   in eval ctxt rmethod end;
   
fun tap_methods match focus f ctxt rmethod = 
  let
    val _ = map_methods (K I) match focus f ctxt rmethod
  in
    K (Seq.single (Drule.dummy_thm)) end;

(* Manage stateful method keywords to instrument parsers*)
(*FIXME: Can we tag minor keywords somehow to avoid this? *)
val method_syntax = Unsynchronized.ref (([],([],[])) : (int * string) list * 
                                                     ((int * string) list *
                                                     (int * (string * string)) list))

fun get_method_syntax () = 
  let
    val (infix_syn,(postfix_syn,mixfix_syn)) = ! method_syntax
  in
    (map snd infix_syn,map snd postfix_syn, map snd mixfix_syn) end;

fun change_method_syntax f = CRITICAL (fn () =>
  Unsynchronized.change method_syntax f);

local

  fun add_and_sort s = (sort (fn (x,y) => int_ord (fst x, fst y)) o ((insert (eq_snd (op =)) s)));
  
in

fun add_infix_syntax s = change_method_syntax (apfst (add_and_sort s));

fun add_postfix_syntax s = change_method_syntax ((apsnd o apfst) (add_and_sort s));
  
fun add_mixfix_syntax s = change_method_syntax ((apsnd o apsnd) (add_and_sort s));
  
end;

fun is_symid_meth s =
  let
    val (infix_syn,postfix_syn,mixfix_syn) = get_method_syntax ();
  in
  not (member (op =) infix_syn s) andalso not (member (op =)  postfix_syn s)
  andalso (List.all (fn (x,y) => s <> y andalso s <> x) mixfix_syn)
    andalso Token.ident_or_symbolic s end;



(* rich_method parser.
   Generates nested parsing structure based on current method syntax.
   Defers parsing of matches and method arguments. *)
(*TODO: Needs cleanup*)
local

  fun parse' x =
  
  let
    val (infix_syn,postfix_syn,mixfix_syn) = get_method_syntax ()
                           
    fun bracks l r scan = Args.$$$ l |-- scan --| Args.$$$ r;
  
    fun unparse toks = fold (fn tok => fn s => s ^ (Token.unparse tok)) toks ""

    fun mixfix_parsers init ((x,y) :: xs) = 
      (init -- bracks x y (Parse.position Args.parse) >> (fn (m,(toks,pos)) => Postfix ((x ^ y,[unparse toks]),m))) ||
      (mixfix_parsers init xs)
     | mixfix_parsers _ [] = Scan.fail
     
      

    fun meth5 x = ((@{keyword "match"} |-- Parse.!!! 
                    ((Parse.position (Args.parse1 (curry (op <>) "in")) >> (fn (toks,pos) => (Args.src (("",toks),pos)))))
                     -- (@{keyword "in"} |--  
                  Parse.enum1 "\<bar>" (Parse.position (Args.parse1 (fn t => t <> "\<Rightarrow>" andalso t <> "\<bar>" andalso is_symid_meth t)) -- 
                            (@{keyword "\<Rightarrow>"} |-- meth4 )))) 
                     >> (fn (src,m1) => Match_Bind (src,map (apfst (fn (toks,pos) => (Args.src (("",toks),pos)))) m1))) x
    and meth4 x =
     (Parse.position (Parse.xname >> rpair []) >> (Source o Args.src) ||
      Parse.$$$ "(" |-- Parse.!!! (meth0 --| Parse.$$$ ")")) x
    and meth3 x =
     (meth4 -- Parse.keyword_with (member (op =) postfix_syn) >> (fn (m,x) => Postfix ((x,[]),m)) ||
       mixfix_parsers meth4 mixfix_syn ||
      meth5 ||
      meth4) x
    and meth2 x =
     (Parse.position (Parse.xname --(parse1 (is_symid_meth))) >>  (Source o Args.src) ||
      meth3) x
    and meth_infix ts x =
     case ts of (t :: ts) =>
      ((Parse.enum1 t (meth_infix ts)) >> 
            (fn [m] => m | (m :: ms) => fold (curry (Infix o pair t o swap)) ms m)) x
     | _ => meth2 x
    and meth0 x = meth_infix (infix_syn) x
  
  in
    meth3 x end;
    
in

val parse_rich_method =
  Scan.trace (parse') >> (fn (m, toks) => (m, Token.position_range_of toks));

end;

(*TODO: Handle rule_cases*)
fun apply_standard_method src ctxt using thm =
  let
    val thy = Proof_Context.theory_of ctxt        
    val seq = (Method.apply (Method.method thy src) ctxt using) thm    
  in
     Seq.map snd seq end;



(* Manage named lemma sets*)

structure Method_Facts = Generic_Data
(
  type T = (thm Item_Net.T) Name_Space.table;
  val empty = Name_Space.empty_table "method_facts";
  val extend = I;
  val merge = (Name_Space.join_tables (K (Item_Net.merge)))

);


fun lookup_method_fact context name =
  let
    val (space,tab) = Method_Facts.get context
    val name' = Name_Space.intern space name
    val fact = Symtab.lookup tab name'
  in
    (the_default Thm.full_rules fact) end;

fun get_method_fact context name = Item_Net.content (lookup_method_fact context name)

fun map_method_fact f name context =
    Method_Facts.map (fn (space,tab) =>
    let
      val (name',_) = Name_Space.check context (space,tab) (name,Position.none)
      val tab' = Symtab.map_entry name' f tab 
    in
      (space,tab') end) context;

fun declare_method_fact binding context = Method_Facts.map 
  (#2 o Name_Space.define context false (binding,lookup_method_fact context (Binding.name_of binding))) context

fun add_method_fact name thm = map_method_fact (Item_Net.update thm) name
fun del_method_fact name thm = map_method_fact (Item_Net.remove thm) name
fun clear_method_fact name = map_method_fact (K Thm.full_rules) name

local
  
  fun parse_term_args term_args (context,st) =
    let
      val ctxt = Context.proof_of context
      fun do_parse t = 
      let
        val T = fastype_of t
        val parser = if T = propT then Syntax.parse_prop else Syntax.parse_term
      in
        Args.named_term (parser ctxt #> (Type.constraint (Type_Infer.paramify_vars (fastype_of t)))) end;

      fun rep [] x = Scan.succeed [] x
        | rep (t :: ts) x  = ((Scan.trace (do_parse t)) -- rep ts >> op ::) x;
      val (result,rest) = rep term_args st
      val (ts,toks) = ListPair.unzip result
      val ts' =  Syntax.check_terms ctxt ts
      val _ = map2 (fn t => fn [tok] => Token.assign (SOME (Token.Term t)) tok) ts' toks
      
    in (ts',(context,rest)) end;
    
  fun parse_meth_args meth_args =
    let
      fun rep 0 x = Scan.succeed [] x
        | rep k x = (parse_rich_method -- rep (k - 1) >> op ::) x;
    in rep (length meth_args) end;
  
  fun parse_src_args src_args =
     let
       fun rep 0 x = Scan.succeed [] x
         | rep k x = (Args.named_text I -- rep (k - 1) >> op ::) x;
      in rep (length src_args) end;

  fun parse_fact_args fact_args =
    let
      val ss = map (fn a => Args.$$$ a --| Args.colon) fact_args;
      val thms =
        Scan.repeat (Scan.unless (Scan.lift (Scan.first ss)) Attrib.multi_thm) >> flat;
      val section = Scan.lift (Scan.first ss) -- thms;
    in Scan.repeat section >> (AList.group (op =) #> map (apsnd flat)) end;

fun collect_fact_sets ctxt parsed_facts (group,name) =
    let
      val arg_fact = the_default [] (AList.lookup (op =) parsed_facts name)
      val ctxt' = Context.proof_map (fold (add_method_fact name) arg_fact) ctxt
    in
      ctxt' end;
    
fun get_full_fact parsed_facts (group,name) ctxt = 
    let
      val arg_fact = the_default [] (AList.lookup (op =) parsed_facts name)
      val (ctxt',final_fact) = 
      if group then 
        let
          val ctxt' = Context.proof_map (fold (add_method_fact name) arg_fact) ctxt;
        in
          (ctxt',get_method_fact (Context.Proof ctxt') name) end
      else
        (ctxt,arg_fact)
    in
      ((name,final_fact),ctxt) end;

  fun sort_parsed_facts ctxt fact_args (parsed_facts : (string * thm list) list) = 
    fold_map (get_full_fact parsed_facts) fact_args ctxt
    
in


fun parse_args ctxt src =
  let
    val ((raw_name, _), pos) = Args.dest_src src; 
    val (_, ((src_args0,term_args0, fact_args0, meth_args0), meth0)) = check ctxt (raw_name, pos);

    val ((((src_args,term_args), parsed_facts), parsed_methods), _) = ctxt
      |> Proof_Context.set_mode Proof_Context.mode_schematic
      |> Args.context_syntax "rich_method"
        (Scan.lift (parse_src_args src_args0) --
         parse_term_args term_args0 --
         parse_fact_args (map snd fact_args0) --
         Scan.lift (parse_meth_args meth_args0)) src;
       
    val parsed_methods' = map (apsnd Position.set_range) parsed_methods;
  in
       (((src_args0,term_args0,fact_args0,meth_args0) : rich_method_args ,meth0),
       (src_args,term_args,parsed_facts,parsed_methods'))
       end;

(* Lookup rich_method by name, falling back to standard methods if not found*)

(*TODO: Rewrite method setup and method_definition commands to avoid clashes *)
fun apply_src eval_args box_method ctxt using src =
      let
        val ((raw_name,_),pos) = Args.dest_src src;
        val (space,tab) = get_methods ctxt;
        val name = Name_Space.intern space raw_name;
      in 
        (case Symtab.lookup tab name of
          SOME _ => eval_args ctxt using (parse_args ctxt src)
          | NONE => box_method (apply_standard_method src) ctxt using) end;


fun intern_method_names ctxt meth = 
  let
    val (space,_) = get_methods ctxt;
  in
    map_src true (Args.map_name (Name_Space.intern space)) meth end;

            
fun gen_apply apply_method box_method =
  let  
    fun eval_args ctxt using
          ((((src_args0,term_args0,fact_args0,meth_args0) : rich_method_args),meth0),
            (src_args,term_args,fact_args,method_args)) =
      case meth0 of (Basic f) => box_method (fn ctxt => fn using => 
      let
        val (nfacts,ctxt') = (sort_parsed_facts ctxt fact_args0 fact_args)
      in     
      f (src_args,term_args,
        map snd nfacts, 
        (map (fn (rm,_) => apply_method ctxt' using rm) method_args)) ctxt' end) ctxt using
        | _ =>
        let
          val term_args_var = map (fn (Var (xi,t)) => (xi,t)) term_args0;
          
          val (nfacts,ctxt') = (sort_parsed_facts ctxt fact_args0 fact_args);
          
          val meth1 = meth0
          |> instantiate_values true ctxt Vartab.empty (term_args_var ~~ term_args)
          |> instantiate_facts true nfacts
          |> instantiate_strs (src_args0 ~~ src_args)

          fun close_rich_method rm =        
            Basic ((K ( K (apply_method ctxt' using rm))))

          val ctxt'' = ctxt'
            |> fold (fn (name,(meth,pos)) => 
              add_rich_method false (Binding.make (name,pos)) ([],[],[],[]) meth) 
                                        (meth_args0 ~~ (map (apfst close_rich_method) method_args))

          in
            apply_method ctxt'' using meth1 end;
    
     in
      eval_args end;

 end;

 
(*Matching*)

datatype match =
  Match_thms of thm list * ((term * string option) list)
| Match_terms of (term list) * (term list)


fun check_match ctxt (Match_thms (a,tns)) = 
  let
    val (ts,ns) = ListPair.unzip tns;
    val ts' = Syntax.check_terms ctxt ts;
  in
    Match_thms (a,ListPair.zip (ts',ns)) end
  | check_match ctxt (Match_terms (a,ts)) = Match_terms (a,Syntax.check_terms ctxt ts)
  
fun finish_parse parser src =
      let 
        val parse_eof = Parse.!!! (parser --| Scan.ahead Parse.eof)
      in
        the (Scan.read Token.stopper parse_eof src) end;

fun parse_match final src src' ctxt = 
  let
    val ctxt' = Proof_Context.set_mode Proof_Context.mode_schematic ctxt;   
      
    val parse_term = if final then Args.named_term (Syntax.read_term ctxt') else 
      Parse.term >> (Syntax.parse_term ctxt');
      
    val parse_prop= if final then Args.named_term (Syntax.read_prop ctxt') else 
      Parse.prop >> (Syntax.parse_prop ctxt');

    (*Conditionally parse patterns depending on match type*)
    val match_parse = 
      finish_parse ((Scan.ahead Parse.string |-- Parse.!!! (Scan.pass (Context.Proof ctxt') Args.term)) >> 
        (fn t => Parse.and_list (parse_term) >>  (Match_terms o pair [t])) ||
    ((Scan.pass (Context.Proof ctxt) Attrib.multi_thm) >> 
        (fn thms => Parse.and_list (
        (Scan.option (Parse.name --| Args.colon ) -- 
        parse_prop)) >>  (Match_thms o pair thms o map swap)))) src;
    
  in
    check_match ctxt' (finish_parse match_parse src') end;
          

fun all_pats_bound prop_pat e = 
  let
    val real_vars = map fst (Term.add_vars prop_pat []);
  in
    List.all (fn xi' => Vartab.exists (fn (xi,_) => xi = xi') e) real_vars end;

fun matches ctxt (tyenv,tenv) pat t =
  let    
    val pat' = pat
    |> Envir.subst_term_types tyenv
    |> Envir.subst_term (normalize_env (tyenv,tenv));
        
    val matches =  Unify.matchers (Proof_Context.theory_of ctxt) [(pat',t)]    
  in
    matches
    |> Seq.map (fn e => (Vartab.merge (op =) (tyenv,Envir.type_env e), 
                      Vartab.merge (op =) (tenv,Envir.term_env e)))
    |> Seq.filter (all_pats_bound pat' o snd)
  end;
    
(* Choice function. 
    Lazily generate all possible ways of selecting out of a list of lists*)
fun choice xs = 
  let
    fun choice' x (y :: ys) = fold (fn chs => Seq.append ((choice' (x @ [chs]) ys))) y Seq.empty
      | choice' x  [] = Seq.single x;
  in
    choice' [] xs end;
    
fun generalize_params ctxt t = 
  let
    val ((st,t'),ctxt') = Variable.focus t ctxt
    val [t''] = Variable.export_terms ctxt' ctxt [t']
  in
    t'' end;

(* Many-to-many matching of
   patterns to items, with initial filtering through
   a store (get) *)
fun match_get ctxt prop_pats prep_pat prep_item get =
  let
    fun match_thm (pat,item) env =
      let
        val item' = prep_item item;
        val pat' =  (prep_pat pat);              
        val matches = matches ctxt env pat' item';
      in
        matches end;
        
    val all_matches = choice (map (get) prop_pats)      
        |> Seq.map (fn t =>
          let
            val pairs = (prop_pats ~~ t)
          in           
            (pairs,Seq.EVERY (map match_thm pairs) (Vartab.empty,Vartab.empty)) end)      
    in
      all_matches end;

fun dest_all_conjs thm = 
  let
    val (thm1,thm2) = Conjunction.elim thm
  in
    dest_all_conjs thm1 @ dest_all_conjs thm2 end handle THM _ => [thm]
      
fun real_match ctxt text (Match_thms (thms,pats)) =
  let
    val thms' = flat (map dest_all_conjs thms)
    val net = fold Item_Net.update thms' (Item_Net.init Thm.eq_thm_prop (single o Thm.full_prop_of))
   
    fun map_insts (((_,SOME n),thm)::insts) = (n,[thm]) :: (map_insts insts)
      | map_insts (_::insts) = map_insts insts
      | map_insts [] = []
    
  in
    match_get ctxt pats fst (Thm.full_prop_of) (Item_Net.retrieve net o fst)
    |> Seq.map (fn (insts,envs) => 
      let
        val text' = instantiate_facts true (map_insts insts) text
      in
        Seq.map (fn ts => (ctxt,instantiate_values_env true ctxt ts text')) envs end)
    |> Seq.flat end
  
 | real_match ctxt text (Match_terms (terms,pats)) =
  let
    val net = fold Item_Net.update terms (Item_Net.init (op =) single)
  in
    match_get ctxt pats I I (Item_Net.retrieve net)
    |> Seq.map (fn (_,envs) => 
        Seq.map (fn ts => (ctxt,instantiate_values_env true ctxt ts text)) envs)
    |> Seq.flat end;

fun real_matches src ctxt pats =
  let
    fun do_match (src',rm) ctxt = 
      real_match ctxt rm (parse_match true (toks_of src) (toks_of src') ctxt)
  in
    Seq.FIRST (map do_match pats) ctxt end;

    
(* Aggresively ensure unfocusing can still occur after executing leaf standard methods*)
(*TODO: Proper evaluation of checking focus late versus checking often/early*)
fun wrap_focus_check tac ctxt using thm =
  (tac ctxt using thm)
  |> Seq.filter (Subgoal2.check_focus ctxt)
    
fun tactic_of ctxt using = 
  let
    val eval_args = gen_apply tactic_of wrap_focus_check
  in
    seq_methods real_matches (apply_src eval_args wrap_focus_check) eval_args ctxt using end;

(* "fake" matching. Creates fixed terms to back schematics
   in patterns (for subsequent exporting). *)
fun fake_matches' src src' ctxt =
  let
    
    (*FIXME: Rethink how parsing is done here*)
    val match = parse_match false src src' ctxt
    
    val pats = case match of (Match_thms (_,tns)) => map fst tns
                              | (Match_terms (_,ts)) => ts

    val xis = (distinct (eq_fst (op =)) (fold Term.add_vars pats []))
    
    fun upd_ctxt (_,SOME n) = Proof_Context.put_thms true (n,SOME [free_thm])
      | upd_ctxt _ = I;
    
    val ctxt' = ctxt
      |> Variable.set_body true
      |> Variable.add_fixes (map (fn (xi,_) => ((string_of_indexname xi))) xis)
      |>> map2 (fn (xi,T) => fn n => (xi,SOME (Free (n,T)))) xis
      |-> Proof_Context.bind_terms
      |> (case match of 
             Match_thms (_,tns) => fold upd_ctxt tns
           | _ => I)
    
    (* Assign token values based on all known type information *)
    (* Horrible *)
    val _ = parse_match true src src' ctxt';

  in
    ctxt' end;
  
fun fake_matches src ctxt srcs =
  let
    fun do_match (src',rm) = fake_matches' (toks_of src) (toks_of src') ctxt;
  in
    map do_match srcs end;

(*Currently focusing does not require modifying
  the hypothetical dummy context as the concl term
  and prems local fact are bound at the start*)
  
fun fake_focus ctxt = ctxt

(* "box" a method by running it a dummy context.
    Here we are only concerned with its parser running
    and getting the implicit value assignment for its arguments *)

fun box_method g = (fn ctxt => fn using => let val _ = try Seq.pull (g ctxt using Drule.dummy_thm) in 
  K (Seq.single (Drule.dummy_thm)) end)


  
(* "apply" a rich method, shallowly executing the leaf parsers
   to collect implicit values *)                     
fun apply_fake ctxt = 
  let                                  
    val dummy_apply = (fn ctxt => apply_src 
        (fn _ => fn _ => fn c => 
          let
            val (_,(_,_,_,x)) = c;
            (* Close up inner methods*)
            val _ = map (apply_fake ctxt o fst) x
          in
          all_tac end) box_method ctxt [])
  in
  tap_methods fake_matches fake_focus dummy_apply ctxt end;
  
fun export_tags ctxt ctxt' thms = 
  let
    val tagss = (map Thm.get_tags thms)
    val thms' = Variable.export ctxt ctxt' thms
  in
    map2 (Thm.map_tags o K) tagss thms' end;

local
fun src_closure ctxt meth =
  let
    val _ = apply_fake ctxt meth
  in () end;

fun focus_test t src = 
    let     
      val ((_,toks),pos) = Args.dest_src src
      fun needs_focus ((SOME (Token.Term t')),_) = Term.exists_subterm (curry (op =) t) t'
        | needs_focus ((SOME (Token.Fact thms)),tok) = is_free_fact thms andalso Token.content_of tok = premsN
        | needs_focus _ = false
    in
      List.exists (needs_focus o `Token.get_value) toks end;

(* Focus wherever implicitly bound conclusion and local assumptions are used *)
fun implicit_focus t rmethod =
  let         
    fun eval (Source src) = (focus_test t src ? Focus o pair t) (Source src)
      | eval (Infix (s,(txt1,txt2))) = Infix(s,(eval txt1,eval txt2))
      | eval (Postfix ((s,arg),txt)) = Postfix ((s,arg),eval txt)
      | eval (Match_Bind (src,m1)) = (focus_test t src ? Focus o pair t) (Match_Bind (src, map (apsnd eval) m1))
      | eval (Focus _) = error "Found explicit focus while implicitly focusing"
      | eval (Basic _) = error "Found basic rich_method in combinator tree"
  in eval rmethod end;

in

(* Implicitly assign values used during
   method parsing and export to the given lthy*)
  

fun method_closure lthy ctxt meth0 =
  let 
    val meth1 = map_src true Args.assignable meth0;
    val (conclN,ctxt') = ctxt
      |> Proof_Context.put_thms true (premsN,  SOME [free_thm])
      |> Proof_Context.add_fixes ([(Binding.name "concl",SOME @{typ bool},NoSyn)])
      |-> (fn [n] => pair n o (Proof_Context.bind_terms [(("concl",0),SOME (Free (n,@{typ bool})))]));
      
    val () = src_closure ctxt' meth1;
    
    
    val meth2 = map_src true Args.closure meth1
    |> implicit_focus (Free(conclN,@{typ bool}));

      
  fun extern_body ctxt src =
    let
      val ([],(Source src')) = burrow_values true (export_tags ctxt lthy) (Variable.export_terms ctxt lthy) ([],Source src)
    in
      src' end;
     
    val meth3 = map_methods extern_body fake_matches fake_focus (K (K I)) ctxt' meth2;

  in meth3 end;

end;

fun apply_real rm = Proof.apply (Method.Basic (fn ctxt => 
                      Method.RAW_METHOD (fn using => (tactic_of ctxt using (method_closure ctxt ctxt rm)))));
  

fun apply_rich_method rm pos state = 
  state
    |> Seq.APPEND (apply_real rm #> Seq.make_results,
      (Seq.single o Proof_Display.method_error "" (Position.set_range pos) o Proof.raw_goal));
                

(*Needed if we do our own tokenization again*)
fun parse_method ctxt (txt, pos) =
  let
    (*tokenize*)
    val syms = Symbol_Pos.explode (txt, pos);
    val toks =
      Source.of_list syms
      |> Token.source' {do_recover = NONE}
        (fn () => (#1 (Keyword.get_lexicons ()), Scan.empty_lexicon))
      |> Source.exhaust;
    val _ = toks |> List.app (fn tok =>
      if Token.keyword_with Symbol.is_ascii_identifier tok then
        Context_Position.report ctxt (Token.position_of tok) Markup.keyword1
      else ());

    (*parse*)
    val proper_toks = filter Token.is_proper toks;
   
    val parse_method = Parse.!!! (parse_rich_method --| Scan.ahead Parse.eof);
    val (method_text, _) = the (Scan.read Token.stopper parse_method proper_toks);
    
  in method_text end;
  
 
(* define rich method *)

val default_rich_method = Source (Args.src (("-",[]),Position.none))

local
    
  fun gen_mk_rich_method prep_vars prep_method binding raw_fixes srcs set_fact_args meth_args raw_meth lthy =
    let
      
      val (xs, ctxt1) = lthy |> prep_vars raw_fixes |-> Proof_Context.add_fixes;
      val (Ts, ctxt2) = ctxt1 |> fold_map Proof_Context.inferred_param xs;
      
      val term_args = map Free (xs ~~ Ts);

      val fact_args = set_fact_args
      
      fun mk_bind s = Binding.qualify false (Binding.name_of binding) (Binding.make (s,Position.none))

      val ctxt3 = ctxt2
        |> Context.proof_map (Attrib.set_attribute_morphism wrap_attribute)
        |> fold (fn a => Proof_Context.put_thms true (a, SOME [free_thm])) (map snd fact_args)
        |> fold (fn a => add_rich_method true (mk_bind a) 
                                              ([],[],[],[]) default_rich_method) meth_args;
      
                                              
      val term_args' = (Variable.export_terms ctxt3 lthy) term_args;
      
      val ctxt4 = ctxt3
        |> add_rich_method true binding (srcs,term_args',fact_args,meth_args) default_rich_method;      
      
      val meth' =
        prep_method ctxt4 raw_meth
        |> method_closure lthy ctxt4;
                   
      
      val rich_method' = ((srcs,term_args', fact_args, meth_args), meth');

      (*TODO Bind to actual declared position*)
      (*TODO Allow absolute addressing for fact groups that come from other theories*)

      val new_groups = map_filter 
        (fn (b,n) => if b then SOME (Binding.make (n,Position.none)) else NONE) set_fact_args;
    in
      lthy |> Local_Theory.declaration {syntax = false, pervasive = true}
        (fn phi => fn context =>
          let val thy = Context.theory_of context in
            context |> (Data.map)
              (#2 o Name_Space.define context true
                (Morphism.binding phi binding, transform_rich_method phi rich_method'))
                |> fold (declare_method_fact o Morphism.binding phi) new_groups
          end) end;
in

val define_rich_method = gen_mk_rich_method Proof_Context.cert_vars (K I);
val define_rich_method_cmd = gen_mk_rich_method Proof_Context.read_vars (K I);
end;

val parse_fact = (Args.bracks Parse.name >> pair true) || (Parse.name >> pair false)
                      
val _ =
  Outer_Syntax.local_theory @{command_spec "method_definition"} "define proof method"
    (Parse.binding -- 
      Scan.optional (@{keyword "srcs"} |-- Parse.!!! (Scan.repeat1 Parse.name)) [] --
      Parse.for_fixes --     
      Scan.optional (@{keyword "facts"} |-- Parse.!!! (Scan.repeat1 parse_fact)) [] --
      Scan.optional (@{keyword "methods"} |-- Parse.!!! (Scan.repeat1 Parse.name)) [] --
      (@{keyword "="} |-- Parse.!!! parse_rich_method)
      >> (fn (((((b,srcs), xs), facts), meths), (rm,_)) => define_rich_method_cmd b xs srcs facts meths rm));
      
val _ =
  Outer_Syntax.command @{command_spec "method_setup"} "define proof method in ML"
    (Parse.position Parse.name --
        Parse.!!! (@{keyword "="} |-- Parse.ML_source -- Scan.optional Parse.text "")
      >> (fn (name, (txt, cmt)) => Toplevel.theory (Method.method_setup name txt cmt)));

(*Just used for drop off of compiled method*)    
structure Compiled_Method = Generic_Data
(
  type T = basic_rich_method;
  val empty : T = undefined;
  fun extend x : T = undefined;
  fun merge (x, y): T = undefined;
);

fun set_basic_method f = (Compiled_Method.map (K f))

val the_basic_method = Compiled_Method.get
      
(* compile ML source *)

fun compile_method strings terms facts meths ctxt (txt, pos) =
  let
    fun mk_list ss = ML_Syntax.print_list I ss
    val txt' = ML_Lex.read Position.none 
                ("fn (" ^ mk_list strings ^ "," ^ mk_list terms ^ "," ^ mk_list (map snd facts) ^ "," ^ mk_list meths ^ ") => fn ctxt =>") @ 
                ML_Lex.read pos txt
  in
    Context.Proof ctxt
      |> (ML_Context.expression pos
        "val meth: Rich_Method.basic_rich_method" "Rich_Method.set_basic_method meth" (txt'))
      |> the_basic_method end
  
fun gen_define_basic_method prep_vars binding syn src_args raw_fixes raw_facts meths txt lthy =
  let
    val (xs, ctxt1) = lthy |> prep_vars raw_fixes |-> Proof_Context.add_fixes;
    val (Ts, ctxt2) = ctxt1 |> fold_map Proof_Context.inferred_param xs;
    
    val term_args = map Free (xs ~~ Ts);
    
    val term_args' = Variable.export_terms ctxt2 lthy term_args
    
    val facts = raw_facts
    val args = (src_args,term_args',facts,meths)
    val basic_meth = compile_method src_args xs facts meths lthy txt
    

   fun declare context = case syn of SOME (syntype,((syml,symr),priority)) =>
        let
          val _ = case (syntype,args) of ("infix",([],[],[],[_,_])) => add_infix_syntax (priority,syml)
  
                                | ("postfix_meth",([],[],[],[_])) =>
                                      add_postfix_syntax (priority,syml)
                                | ("mixfix_meth",([_],[],[],[_])) =>
                                      add_mixfix_syntax (priority,(syml,symr))
                                | _ => error "Mismatched number of arguments for syntax type"
        in
          add_method_syntax (syml ^ symr,(args, Basic basic_meth)) context end
     | NONE => context
  
  in
    lthy |> Local_Theory.declaration {syntax = false, pervasive = true}
      (fn phi => fn context =>
          context |> (Data.map)
            (#2 o Name_Space.define context true
              (Morphism.binding phi binding, (args,Basic basic_meth)))
           |> declare) end;

val define_basic_method_cmd = gen_define_basic_method Proof_Context.read_vars


(*FIXME: Some duplication here*)
val _ =
  Outer_Syntax.local_theory @{command_spec "ML_method_definition"} "define proof method"
    (Parse.binding --
      Scan.option (Args.parens ((@{keyword "infix"} || @{keyword "postfix_meth"}) -- 
                                          Parse.!!! (Parse.keyword -- Parse.int) >> 
                                        (fn (x,(y,z)) => (x,((y,""),z)))
                                || @{keyword "mixfix_meth"} -- 
                                Parse.!!! (Parse.keyword -- Parse.keyword -- Parse.int))) --
      Scan.optional (@{keyword "srcs"} |-- Parse.!!! (Scan.repeat1 Parse.name)) [] --
      Parse.for_fixes --
      Scan.optional (@{keyword "facts"} |-- Parse.!!! (Scan.repeat1 parse_fact)) [] --
      Scan.optional (@{keyword "methods"} |-- Parse.!!! (Scan.repeat1 Parse.name)) [] --
      (@{keyword "="} |-- Parse.!!! (Parse.source_position Parse.text))
      >> (fn ((((((b, syn), strings), terms), facts), meths), txt) => 
                define_basic_method_cmd b syn strings terms facts meths txt));

val _ = Theory.setup (Attrib.setup @{binding "add"} 
            (Scan.lift Parse.xname >> (fn nm => Thm.declaration_attribute (add_method_fact nm))) "add to method fact" )

val _ = Theory.setup (Attrib.setup @{binding "del"} 
            (Scan.lift Parse.xname >> (fn nm => Thm.declaration_attribute (del_method_fact nm))) "remove from method fact" )


fun rich_method_as_text rm =
  let
    val text = Method.Basic (fn ctxt => 
      Method.RAW_METHOD (fn using => tactic_of ctxt using (method_closure ctxt ctxt rm)))
  in
    text end;                
                
end;
*}

     
  
section {* Tacticals *}

(* Standard tacticals *)
ML_method_definition ORELSE (infix | 1) methods meth1 meth2 = "meth1 ORELSE meth2"
ML_method_definition THEN (infix , 5) methods meth1 meth2 = "meth1 THEN meth2"
ML_method_definition ALL (postfix_meth + 0) methods meth1 = "REPEAT1 meth1"
ML_method_definition TRY (postfix_meth ? 1) methods meth1 = "TRY meth1"

ML {* 

fun protect n th = Drule.comp_no_flatten (th, n) 1 Drule.protectI;

fun restrict n st =
  if n < 1 orelse n > Thm.nprems_of st
  then (I,st)
  else (Goal.conclude,protect n st);

 *}


ML {*
  fun select_goals n meth state =
  state
  |> ALLGOALS Goal.conjunction_tac
  |> Seq.maps (fn goal =>
   (if (Thm.nprems_of goal = 0) then Seq.empty else
    goal
    |> Goal.restrict 1 n
    |> Goal.conjunction_tac 1
    |> Seq.maps meth
    |> Seq.map (fn goal' => Goal.unrestrict 1 goal'))) *}

ML_method_definition RESTRICT (mixfix_meth [ ] 1) srcs i methods meth1 = {*
 let
   val (i',rest) = Library.read_int (Symbol.explode i)
   val _ = (rest <> []) andalso (error "Not a number")
 in
  select_goals i' meth1 end*}

(* Export standard tacticals to global syntax space*)    
ML {* Rich_Method.collect_global_syntax (Context.Proof @{context}) *}    


(* New tacticals *)
ML_method_definition ALLGOALS (postfix_meth @ 20) methods meth1 = "ALLGOALS (SELECT_GOAL meth1)"
      
ML_method_definition SOLVES (postfix_meth # 1) methods meth1 = 
  "SOLVED' (SELECT_GOAL meth1) 1"
  
ML_method_definition THEN_ALL_NEW (infix \<mapsto> 20) methods meth1 meth2 = 
      "THEN_ALL_NEW (SELECT_GOAL meth1,SELECT_GOAL meth2) 1"
      

(*Redefine Isar outer syntax commands*)

ML {*
val _ =
  Outer_Syntax.command @{command_spec "apply"} "apply rich proof method"
    (Rich_Method.parse_rich_method  
      >> (fn (rm,pos) => Toplevel.print o Toplevel.proofs (Rich_Method.apply_rich_method rm pos)));
      

val _ =
  Outer_Syntax.command @{command_spec "by"} "terminal backward proof"
    (Rich_Method.parse_rich_method -- Scan.option Rich_Method.parse_rich_method >> 
      (fn (rm,orm) => Isar_Cmd.terminal_proof ((apfst Rich_Method.rich_method_as_text) rm, Option.map (apfst Rich_Method.rich_method_as_text) orm)));
*}

setup {*
  ML_Antiquote.value @{binding name_ref}
    (Scan.lift (Parse.position Args.name) >>
      (ML_Syntax.print_pair ML_Syntax.print_string ML_Syntax.print_position)) *}

(* "proof" deliberately left out due to lack of rule cases support*)

end
