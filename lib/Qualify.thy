(*
  Post-hoc qualification of global constants, facts and types using name space aliasing.
  Can be used to add mandatory qualification to otherwise non-localised commands (i.e. "record",
  "instantiation").

  This is a hack that should be replaced with proper "context begin ... end" blocks when
  commands are appropriately localized.
*)

theory Qualify
imports Main
keywords "qualify" :: thy_decl and "end_qualify" :: thy_decl
begin
ML \<open>

type qualify_args = {name : string, deep : bool}

structure Data = Theory_Data
  (
    type T = (theory * qualify_args) option * 
             ((string * 
              ((binding Symtab.table) * (* facts *)
               (binding Symtab.table) * (* consts *)
               (binding Symtab.table) (* types *))) list);
    val empty = (NONE, []);
    val extend = I;
    fun merge (((_, tabs), (_, tabs')) : T * T) = 
      (NONE, AList.join (op =) 
      (fn _ => fn ((facts, consts, types), (facts', consts', types')) =>
        (Symtab.merge (op =) (facts, facts'), 
         Symtab.merge (op =) (consts, consts'),
         Symtab.merge (op =) (types, types')))
      (tabs, tabs'));
  );

fun get_qualify thy = fst (Data.get thy);

fun get_tabs_of thy str = 
  the_default (Symtab.empty, Symtab.empty, Symtab.empty) (AList.lookup (op =) (snd (Data.get thy)) str);

fun get_facts_of thy str = #1 (get_tabs_of thy str);

fun get_consts_of thy str = #2 (get_tabs_of thy str);

fun get_types_of thy str = #3 (get_tabs_of thy str);

fun map_tabs_of str f thy = 
  Data.map (apsnd (AList.map_default (op =) (str, (Symtab.empty, Symtab.empty, Symtab.empty)) f)) thy;

fun map_facts_of str f thy = map_tabs_of str (@{apply 3(1)} f) thy;

fun map_consts_of str f thy = map_tabs_of str (@{apply 3(2)} f) thy;

fun map_types_of str f thy = map_tabs_of str (@{apply 3(3)} f) thy;

fun make_bind space thy nm = 
  let
    val short_name = 
      Name_Space.extern_shortest (Proof_Context.init_global thy) space nm 
      |> Long_Name.explode |> rev |> tl |> rev;
    val long_name = Long_Name.explode nm |> tl |> rev |> tl |> rev;
    
    fun do_make_bind (short_qual :: l) (_ :: l') b = Binding.qualify true short_qual (do_make_bind l l' b)
      | do_make_bind [] (long_qual :: l) b = Binding.qualify false long_qual (do_make_bind [] l b)
      | do_make_bind [] [] b = b
      | do_make_bind _ _ _ = raise Fail "Mismatched long and short identifiers"

    val b = do_make_bind short_name long_name (Binding.make (Long_Name.base_name nm, Position.none))
  
  in b end;

fun get_new_facts old_thy facts = 
  let
    val space = Facts.space_of facts;
  in
     Facts.dest_static false [Global_Theory.facts_of old_thy] facts
     |> map (fn (nm, _) => `(make_bind space old_thy) nm)
  end

fun get_new_consts old_thy consts =
  let
    val new_consts = #constants (Consts.dest consts)
    |> map fst;

    val space = #const_space (Consts.dest consts);
    
    val consts = 
      filter (fn nm => not (can (Consts.the_const (Sign.consts_of old_thy)) nm) andalso
                       can (Consts.the_const consts) nm) new_consts
      |> map (fn nm => `(make_bind space old_thy) nm);

  in consts end;

fun get_new_types old_thy types =
  let
    val new_types = #types (Type.rep_tsig types);
    val space = Name_Space.space_of_table new_types;

    val old_types = #types (Type.rep_tsig (Sign.tsig_of old_thy));
   
    val types = (new_types
      |> Name_Space.fold_table (fn (nm, _) => 
           not (Name_Space.defined old_types nm) ? cons nm)) []
      |> map (fn nm => `(make_bind space old_thy) nm);
  in types end;

fun add_qualified qual nm =
  let
    val nm' = Long_Name.explode nm |> rev |> tl |> hd;
  in if qual = nm' then cons nm else I end
  handle List.Empty => I

fun make_bind_local nm = 
  let
    val base = Long_Name.explode nm |> tl |> tl |> rev |> tl |> rev;
  in fold (Binding.qualify true) base (Binding.make (Long_Name.base_name nm, Position.none)) end;

fun set_global_qualify (args : qualify_args) thy =
  let
    val str = #name args
    val _ = Locale.check thy (str, Position.none)
    val _ = case get_qualify thy of SOME _ => error "Already in a qualify block!" | NONE => ();

    val thy' = Data.map (apfst (K (SOME (thy,args)))) thy;

  in if #deep args then
  let

    val facts = 
      Facts.fold_static (fn (nm, _) => add_qualified str nm) (Global_Theory.facts_of thy) []
      |> map (`make_bind_local)

    val consts = fold (fn (nm, _) => add_qualified str nm) (#constants (Consts.dest (Sign.consts_of thy))) []
      |> map (`make_bind_local)                                                

    val types = 
      Name_Space.fold_table (fn (nm, _) => add_qualified str nm) (#types (Type.rep_tsig (Sign.tsig_of thy))) []
      |> map (`make_bind_local)

    val thy'' = thy'
     |> map_facts_of str (fold (fn (b, nm) => (Symtab.update (nm, b))) facts)
     |> map_consts_of str (fold (fn (b, nm) => (Symtab.update (nm, b))) consts)
     |> map_types_of str (fold (fn (b, nm) => (Symtab.update (nm, b))) types)

    val thy''' = thy''
    |> fold (fn (nm, b) => Global_Theory.alias_fact b nm) (Symtab.dest (get_facts_of thy'' str))
    |> fold (fn (nm, b) => Sign.const_alias b nm) (Symtab.dest (get_consts_of thy'' str))
    |> fold (fn (nm, b) => Sign.type_alias b nm) (Symtab.dest (get_types_of thy'' str))

  in thy''' end
  else thy'
  end

val _ =
  Outer_Syntax.command @{command_keyword qualify} "begin global qualification"
    (Parse.name -- Args.mode "deep">> 
      (fn (str, deep) => Toplevel.theory (set_global_qualify {name = str, deep = deep})));

fun syntax_alias global_alias local_alias b name =
  Local_Theory.declaration {syntax = true, pervasive = true} (fn phi =>
    let val b' = Morphism.binding phi b
    in Context.mapping (global_alias b' name) (local_alias b' name) end);

val fact_alias = syntax_alias Global_Theory.alias_fact Proof_Context.fact_alias;
val const_alias = syntax_alias Sign.const_alias Proof_Context.const_alias;
val type_alias = syntax_alias Sign.type_alias Proof_Context.type_alias;



fun end_global_qualify thy =
  let
    val (old_thy, args) = 
      case get_qualify thy of
        SOME x => x 
      | NONE => error "Not in a global qualify"

    val nm = #name args

    val facts = get_new_facts old_thy (Global_Theory.facts_of thy);

    val consts = get_new_consts old_thy (Sign.consts_of thy);

    val types = get_new_types old_thy (Sign.tsig_of thy);


    val thy' = thy
     |> map_facts_of nm (fold (fn (b, nm) => (Symtab.update (nm, b))) facts)
     |> map_consts_of nm (fold (fn (b, nm) => (Symtab.update (nm, b))) consts)
     |> map_types_of nm (fold (fn (b, nm) => (Symtab.update (nm, b))) types);

    val facts' = (if #deep args then (map swap (Symtab.dest (get_facts_of thy' nm))) else facts);
    val consts' = (if #deep args then (map swap (Symtab.dest (get_consts_of thy' nm))) else consts);
    val types' = (if #deep args then (map swap (Symtab.dest (get_types_of thy' nm))) else types);

    val thy'' = thy'      
     |> (fn thy => fold (Global_Theory.hide_fact false o snd) facts' thy)
     |> (fn thy => fold (Sign.hide_const false o snd) consts' thy)
     |> (fn thy => fold (Sign.hide_type false o snd) types' thy);

    val lthy = Named_Target.begin (nm, Position.none) thy'';

    val lthy' = lthy
      |> fold (uncurry fact_alias) facts'
      |> fold (uncurry const_alias) consts'
      |> fold (uncurry type_alias) types';

  in Local_Theory.exit_global lthy' |> Data.map (apfst (K NONE)) end

val _ =
  Outer_Syntax.command @{command_keyword end_qualify} "end global qualification"
    (Scan.succeed
      (Toplevel.theory end_global_qualify));


\<close>

setup \<open>Theory.at_end 
  (fn thy => case get_qualify thy of SOME (_, nm) => 
    SOME (end_global_qualify thy) | NONE => NONE)\<close>

end