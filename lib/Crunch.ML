(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

structure CrunchTheoryData = Theory_Data
  (struct
     type T =
       ((Token.src list -> string -> string
         -> (string * ((Facts.ref * Token.src list), xstring) sum) list
         -> string list -> local_theory -> local_theory)
        * (string list -> string list -> theory -> theory)) Symtab.table
     val empty = Symtab.empty
     val extend = I
     val merge = Symtab.merge (fn _ => true);
   end);

fun get_crunch_instance name lthy =
  CrunchTheoryData.get lthy
  |> (fn tab => Symtab.lookup tab name)

fun add_crunch_instance name instance lthy  =
  CrunchTheoryData.map (Symtab.update_new (name, instance)) lthy

structure CallCrunch =
struct

local structure P = Parse and K = Keyword in

(* Read a list of names, up to the next section identifier *)
fun read_thm_list section sections =
    let val match_section_name = Scan.first (map (P.reserved o #1) sections)
in
    Scan.repeat (Scan.unless match_section_name (#2 section))
end

fun read_section all_sections section =
    (P.reserved (#1 section) -- P.$$$ ":") |-- read_thm_list section all_sections
    >> map (fn n => (#1 section, n))

fun read_sections sections =
    Scan.repeat (Scan.first (map (read_section sections) sections)) >> List.concat

val crunch_parser =
    (((Scan.optional (P.$$$ "(" |-- P.name --| P.$$$ ")") "" -- P.name
     -- Parse.opt_attribs --| P.$$$ ":") -- P.list1 P.const -- Scan.optional P.term ""
     -- Scan.optional
       (P.$$$ "(" |-- read_sections [wp_sect,wp_del_sect,ignore_sect,simp_sect,simp_del_sect,rule_sect,rule_del_sect,ignore_del_sect] --| P.$$$ ")")
       []
    )
    >> (fn (((((crunch_instance, prp_name), att_srcs), consts), extra), wpigs) =>
           (fn lthy =>
             (case get_crunch_instance crunch_instance (Proof_Context.theory_of lthy) of
                 NONE => error ("Crunch has not been defined for " ^ crunch_instance)
               | SOME (crunch_x, _) =>
                   crunch_x att_srcs extra prp_name wpigs consts lthy))));

val crunches_parser =
    (((P.list1 P.const --| P.$$$ "for")
     -- P.and_list1 ((Scan.optional (P.$$$ "(" |-- P.name --| P.$$$ ")") "" -- P.name
         -- Parse.opt_attribs) -- Scan.optional (P.$$$ ":" |-- P.term) "")
     -- Scan.optional
       (P.$$$ "(" |-- read_sections [wp_sect,wp_del_sect,ignore_sect,simp_sect,simp_del_sect,rule_sect,rule_del_sect,ignore_del_sect] --| P.$$$ ")")
       []
    )
    >> (fn ((consts, confs), wpigs) =>
           fold (fn (((crunch_instance, prp_name), att_srcs), extra) => fn lthy =>
             (case get_crunch_instance crunch_instance (Proof_Context.theory_of lthy) of
                 NONE => error ("Crunch has not been defined for " ^ crunch_instance)
               | SOME (crunch_x, _) =>
                   crunch_x att_srcs extra prp_name wpigs consts lthy)) confs));

(*
 example: crunch(kind) inv[wp]: f,g  P  (wp: h_P simp: .. ignore: ..)

 or: crunches f,g for (kind)inv: P and (kind2)inv2: Q (wp: etc)

 where: crunch = command keyword
        kind   = instance of crunch, e.g. valid, no_fail
        inv    = lemma name pattern
        [wp]   = optional list of attributes for all proved thms
        f,g    = constants under investigation
        P,Q    = property to be shown (not required for no_fail/empty_fail instance)
        h_P    = wp lemma to use (h will not be unfolded)
        simp: ..   = simp lemmas to use
        ignore: .. = constants to ignore for unfolding

 will prove lemmas for f and for any constituents required.
 for the default crunch instance "valid", lemmas of the form
    "{P and X} f {%_. P}" will be proven.
 the additional preconditions X are propagated upwards from similar
    preconditions in preexisting lemmas.

 There is a longer description of what each crunch does in crunch-cmd.ML
*)

val crunchP =
    Outer_Syntax.local_theory
        @{command_keyword "crunch"}
        "crunch through monadic definitions with a given property"
        crunch_parser

val crunchesP =
    Outer_Syntax.local_theory
        @{command_keyword "crunches"}
        "crunch through monadic definitions with multiple properties"
        crunches_parser

val add_sect = ("add", Parse.const >> Constant);
val del_sect = ("del", Parse.const >> Constant);

val crunch_ignoreP =
    Outer_Syntax.local_theory
         @{command_keyword "crunch_ignore"}
        "add to and delete from list of things that crunch should ignore in finding prerequisites"
        ((Scan.optional (P.$$$ "(" |-- P.name --| P.$$$ ")") "" -- Scan.optional
          (P.$$$ "(" |-- read_sections [add_sect, del_sect] --| P.$$$ ")")
          []
        )
        >> (fn (crunch_instance, wpigs) => fn lthy =>
               let fun const_name const = dest_Const (read_const lthy const) |> #1;
                   val add = wpigs |> filter (fn (s,_) => s = #1 add_sect) |> map #2 |> constants
                                   |> map const_name;
                   val del = wpigs |> filter (fn (s,_) => s = #1 del_sect) |> map #2 |> constants
                                   |> map const_name;
                   val crunch_ignore_add_del = (case get_crunch_instance crunch_instance (Proof_Context.theory_of lthy) of
                     NONE => error ("Crunch has not been defined for " ^ crunch_instance)
                   | SOME x => snd x);
               in
                  Local_Theory.raw_theory (crunch_ignore_add_del add del) lthy
               end));

end;

fun setup thy = thy

end;

