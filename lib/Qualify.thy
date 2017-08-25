(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

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

type qualify_args = {name : string, target_name : string}

structure Data = Theory_Data
  (
    type T = (theory * qualify_args) option;
    val empty = NONE;
    val extend = I;
    fun merge ((_, _) : T * T) = NONE;
  );

fun get_qualify thy = Data.get thy;

fun make_bind space thy nm =
  let
    val short_name =
      Name_Space.extern (Proof_Context.init_global thy |> Config.put Name_Space.names_short true) space nm
      |> Long_Name.explode |> rev |> tl |> rev;
    val long_name = Long_Name.explode nm |> tl |> rev |> tl |> rev;

    fun do_make_bind (short_qual :: l) (_ :: l') b = Binding.qualify true short_qual (do_make_bind l l' b)
      | do_make_bind [] (long_qual :: l) b = Binding.qualify false long_qual (do_make_bind [] l b)
      | do_make_bind [] [] b = b
      | do_make_bind _ _ _ =
        raise Fail ("Mismatched long and short identifiers:\nsource:" ^ nm ^ "\nshort:" ^ (@{make_string} short_name) ^ "\nlong:" ^
          (@{make_string} long_name))

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
    val nm' = Long_Name.explode nm |> tl |> hd;
  in if qual = nm' then cons nm else I end
  handle List.Empty => I

fun make_bind_local nm =
  let
    val base = Long_Name.explode nm |> tl |> tl |> rev |> tl |> rev;
  in fold (Binding.qualify true) base (Binding.make (Long_Name.base_name nm, Position.none)) end;

fun set_global_qualify (args : qualify_args) thy =
  let
    val _ = Locale.check thy (#target_name args, Position.none)
    val _ = case get_qualify thy of SOME _ => error "Already in a qualify block!" | NONE => ();

    val thy' = Data.map (K (SOME (thy,args))) thy;

  in  thy'  end

val _ =
  Outer_Syntax.command @{command_keyword qualify} "begin global qualification"
    (Parse.name -- Parse.opt_target>>
      (fn (str, target) =>
          Toplevel.theory (set_global_qualify {name = str, target_name = case target of SOME (nm, _) => nm | _ => str})));

fun syntax_alias global_alias local_alias b name =
  Local_Theory.declaration {syntax = true, pervasive = true} (fn phi =>
    let val b' = Morphism.binding phi b
    in Context.mapping (global_alias b' name) (local_alias b' name) end);

val alias_fact = syntax_alias Global_Theory.alias_fact Proof_Context.alias_fact;
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

    val thy'' = thy
     |> (fn thy => fold (Global_Theory.hide_fact false o snd) facts thy)
     |> (fn thy => fold (Sign.hide_const false o snd) consts thy)
     |> (fn thy => fold (Sign.hide_type false o snd) types thy);

    val lthy = Named_Target.begin (#target_name args, Position.none) thy''
      |> Local_Theory.map_background_naming (Name_Space.parent_path #> Name_Space.mandatory_path nm);

    val lthy' = lthy
      |> fold (uncurry alias_fact) facts
      |> fold (uncurry const_alias) consts
      |> fold (uncurry type_alias) types;

  in Local_Theory.exit_global lthy' |> Data.map (K NONE) end

val _ =
  Outer_Syntax.command @{command_keyword end_qualify} "end global qualification"
    (Scan.succeed
      (Toplevel.theory end_global_qualify));


\<close>

setup \<open>Theory.at_end
  (fn thy => case get_qualify thy of SOME (_, nm) =>
    SOME (end_global_qualify thy) | NONE => NONE)\<close>

end
