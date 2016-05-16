(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 * 
 * Base of autolevity.
 * Needs to be installed to track command start/end locations 
 *)

theory AutoLevity_Base
imports Main
keywords "levity_tag" :: thy_decl
begin

ML\<open>

fun pos_ord use_offset (pos1, pos2) =
  let
    fun get_offset pos = if use_offset then Position.offset_of pos else SOME 0;

    fun get_props pos = 
      (SOME (Position.file_of pos |> the,
            (Position.line_of pos |> the,
             get_offset pos |> the)), NONE)
      handle Option => (NONE, Position.parse_id pos)
   
    val props1 = get_props pos1;
    val props2 = get_props pos2;

  in prod_ord 
      (option_ord (prod_ord string_ord (prod_ord int_ord int_ord)))
      (option_ord (int_ord))
      (props1, props2) end

structure Postab = Table(type key = Position.T val ord = (pos_ord false));
structure Postab_strict = Table(type key = Position.T val ord = (pos_ord true));


signature AUTOLEVITY_BASE =
sig
type extras = {levity_tag : string option, subgoals : int}
val get_transactions : unit -> ((string * extras) Postab_strict.table) Symtab.table;
val setup_command_hook: unit -> unit;
  
end;

structure AutoLevity_Base : AUTOLEVITY_BASE =
struct
type extras = {levity_tag : string option, subgoals : int}


val transactions = Synchronized.var "hook" 
  (Symtab.empty : ((string * extras) Postab_strict.table) Symtab.table);

fun get_transactions () =
  Synchronized.value transactions;

structure Data = Theory_Data
  (
    type T = string option;
    val empty = NONE;
    val extend = I;
    fun merge ((_, _) : T * T) = NONE;
  );

val _ =
  Outer_Syntax.command @{command_keyword levity_tag} "tag for levity"
    (Parse.string >> (fn str =>
      Toplevel.local_theory NONE NONE 
        (Local_Theory.raw_theory (Data.put (SOME str)))))

fun get_subgoals' state =
let
  val proof_state = Toplevel.proof_of state;
  val {goal, ...} = Proof.raw_goal proof_state;
in Thm.nprems_of goal end

fun get_subgoals state = the_default ~1 (try get_subgoals' state);

fun setup_command_hook () =
  Toplevel.add_hook (fn transition => fn start_state => fn end_state =>
  let
    val pos = Toplevel.pos_of transition;
    val name = Toplevel.name_of transition;

    val thy = Toplevel.theory_of start_state;
    
    val thynm = Context.theory_name thy;

    val end_thy = Toplevel.theory_of end_state;

    val levity_input = if name = "levity_tag" then Data.get end_thy else NONE;
 
    val subgoals = get_subgoals start_state;

    val entry = {levity_tag = levity_input, subgoals = subgoals}
                                                 
    val _ = 
      Synchronized.change transactions 
              (Symtab.map_default (thynm, Postab_strict.empty) 
                (Postab_strict.update_new (pos, (name, entry))))
  in () end)

end
\<close>


end