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
    type T = ((Token.src list -> string -> string -> (string * xstring) list
         -> string list -> local_theory -> local_theory) * (string list -> string list -> theory -> theory)) Symtab.table
    val empty = Symtab.empty
    val extend = I
    val merge = Symtab.merge (fn _ => true);
end);

fun get_crunch_instance name lthy =
  CrunchTheoryData.get lthy
  |> (fn tab => Symtab.lookup tab name)

fun add_crunch_instance name instance lthy  =
  CrunchTheoryData.map (Symtab.update_new (name, instance)) lthy

structure CrunchValidInstance : CrunchInstance =
struct
  type extra = term;
  val eq_extra = ae_conv;
  val name = "valid";
  val has_preconds = true;
  fun mk_term pre body post =
    (Syntax.parse_term @{context} "valid") $ pre $ body $ Abs ("_", dummyT, post);
  fun get_precond (Const (@{const_name "valid"}, _) $ pre $ _ $ _) = pre
    | get_precond _ = error "get_precond: not a hoare triple";
  fun put_precond pre ((v as Const (@{const_name "valid"}, _)) $ _ $ body $ post)
        = v $ pre $ body $ post
    | put_precond _ _ = error "put_precond: not a hoare triple";
  fun dest_term ((Const (@{const_name "valid"}, _)) $ pre $ body $ post)
        = SOME (pre, body, betapply (post, Bound 0))
    | dest_term _ = NONE
  val pre_thms = @{thms "hoare_pre"};
  val wpc_tactic = wp_cases_tactic_weak;
  fun parse_extra ctxt extra
        = case extra of 
            "" => error "A post condition is required"
          | extra => let val post = Syntax.parse_term ctxt extra in (post, post) end;
  val magic = Syntax.parse_term @{context}
    "\<lambda>mapp_lambda_ignore. valid P_free_ignore mapp_lambda_ignore Q_free_ignore"
end;

structure CrunchValid : CRUNCH = Crunch(CrunchValidInstance);

structure CrunchNoFailInstance : CrunchInstance =
struct
  type extra = unit;
  val eq_extra = op =;
  val name = "no_fail";
  val has_preconds = true;
  fun mk_term pre body _ =
    (Syntax.parse_term @{context} "no_fail") $ pre $ body;
  fun get_precond (Const (@{const_name "no_fail"}, _) $ pre $ _ ) = pre
    | get_precond _ = error "get_precond: not a no_fail term";
  fun put_precond pre ((v as Const (@{const_name "no_fail"}, _)) $ _ $ body)
        = v $ pre $ body
    | put_precond _ _ = error "put_precond: not a no_fail term";
  fun dest_term ((Const (@{const_name "no_fail"}, _)) $ pre $ body)
        = SOME (pre, body, ())
    | dest_term _ = NONE
  val pre_thms = @{thms "no_fail_pre"};
  val wpc_tactic = wp_cases_tactic_weak;
  fun parse_extra ctxt extra
        = case extra of
            "" => (Syntax.parse_term ctxt "%_. True", ())
          | _ => (Syntax.parse_term ctxt extra, ());
  val magic = Syntax.parse_term @{context}
    "\<lambda>mapp_lambda_ignore. no_fail P_free_ignore mapp_lambda_ignore"
end;

structure CrunchNoFail : CRUNCH = Crunch(CrunchNoFailInstance);

structure CrunchEmptyFailInstance : CrunchInstance =
struct
  type extra = unit;
  val eq_extra = op =;
  val name = "empty_fail";
  val has_preconds = false;
  fun mk_term _ body _ =
    (Syntax.parse_term @{context} "empty_fail") $ body;
  fun get_precond _ = error "crunch empty_fail should not be calling get_precond";
  fun put_precond _ _ = error "crunch empty_fail should not be calling put_precond";
  fun dest_term (Const (@{const_name empty_fail}, _) $ b)
    = SOME (Term.dummy, b, ())
    | dest_term _ = NONE
  val pre_thms = [];
  val wpc_tactic = wp_cases_tactic_weak;
  fun parse_extra ctxt extra
        = case extra of
            "" => (Syntax.parse_term ctxt "%_. True", ())
          | _ => error "empty_fail does not need a precondition";
  val magic = Syntax.parse_term @{context}
    "\<lambda>mapp_lambda_ignore. empty_fail mapp_lambda_ignore"
end;

structure CrunchEmptyFail : CRUNCH = Crunch(CrunchEmptyFailInstance);

structure CrunchValidEInstance : CrunchInstance =
struct
  type extra = term * term;
  fun eq_extra ((a, b), (c, d)) = (ae_conv (a, c) andalso ae_conv (b, d));
  val name = "valid_E";
  val has_preconds = true;
  fun mk_term pre body extra =
    (Syntax.parse_term @{context} "validE") $ pre $ body $
                   Abs ("_", dummyT, fst extra) $ Abs ("_", dummyT, snd extra);
  fun get_precond (Const (@{const_name "validE"}, _) $ pre $ _ $ _ $ _) = pre
    | get_precond _ = error "get_precond: not a validE term";
  fun put_precond pre ((v as Const (@{const_name "validE"}, _)) $ _ $ body $ post $ post')
        = v $ pre $ body $ post $ post'
    | put_precond _ _ = error "put_precond: not a validE term";
  fun dest_term (Const (@{const_name "validE"}, _) $ pre $ body $ p1 $ p2)
    = SOME (pre, body, (betapply (p1, Bound 0), betapply (p2, Bound 0)))
    | dest_term _ = NONE
  val pre_thms = @{thms "hoare_pre"};
  val wpc_tactic = wp_cases_tactic_weak;
  fun parse_extra ctxt extra
        = case extra of 
            "" => error "A post condition is required"
          | extra => let val post = Syntax.parse_term ctxt extra in (post, (post, post)) end;
  val magic = Syntax.parse_term @{context}
    "\<lambda>mapp_lambda_ignore. validE P_free_ignore mapp_lambda_ignore Q_free_ignore Q_free_ignore"
end;

structure CrunchValidE : CRUNCH = Crunch(CrunchValidEInstance);

structure CallCrunch =
struct

local structure P = Parse and K = Keyword in

(* FIXME: Slightly outdated: *)
(*
 example: crunch inv[wp]: f P (wp: h_P simp: .. ignore: ..)

 where: crunch = command keyword
        inv    = lemma name pattern
        [wp]   = optional list of attributes for all proved thms
        f      = constant under investigation
        P      = property to be shown
        h_P    = wp lemma to use (h will not be unfolded)
        simp: ..   = simp lemmas to use
        ignore: .. = constants to ignore for unfolding

 will prove:
 "{P and X} f {%_. P}" and any lemmas of this form for constituents of f,
     for additional preconditions X propagated upwards from additional
     preconditions in preexisting lemmas for constituents of f.
*)

(* Read a list of names, up to the next section identifier *)
fun read_thm_list sections =
    let val match_section_name = Scan.first (map P.reserved sections) 
in
    Scan.repeat (Scan.unless match_section_name (P.name || P.long_ident))
end

fun read_section all_sections section =
    (P.reserved section -- P.$$$ ":") |-- read_thm_list all_sections >> map (fn n => (section, n)) 

fun read_sections sections =
    Scan.repeat (Scan.first (map (read_section sections) sections)) >> List.concat

val crunchP =
    Outer_Syntax.local_theory
        @{command_keyword "crunch"}
        "crunch through monadic definitions with a given property"
        (((Scan.optional (P.$$$ "(" |-- P.name --| P.$$$ ")") "" -- P.name
         -- Parse.opt_attribs --| P.$$$ ":") -- P.list1 P.name -- Scan.optional P.term ""
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

val add_sect = "add";
val del_sect = "del";

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
                   val add = wpigs |> filter (fn (s,_) => s = add_sect)
                                   |> map (const_name o #2);
                   val del = wpigs |> filter (fn (s,_) => s = del_sect)
                                   |> map (const_name o #2);
                   val crunch_ignore_add_del = (case get_crunch_instance crunch_instance (Proof_Context.theory_of lthy) of
                     NONE => error ("Crunch has not been defined for " ^ crunch_instance)
                   | SOME x => snd x);
               in
                  Local_Theory.raw_theory (crunch_ignore_add_del add del) lthy
                  (* |> (fn lthy => Named_Target.reinit lthy lthy) *)
               end));

end;

fun setup thy = thy

end;

