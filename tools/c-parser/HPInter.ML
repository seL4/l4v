(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(* interface to Norbert Schirmer's Hoare Package code *)
structure HPfninfo =
struct

  type t = {fname : string,
            inparams : (string * typ * int Absyn.ctype option) list,
            outparams : (string * typ * int Absyn.ctype) list,
            body : Absyn.ext_decl HoarePackage.bodykind option,
            spec : (string * Element.context) list,
            mod_annotated_protop : bool,
            recursivep : bool}

end

signature HPINTER =
sig

  type csenv = ProgramAnalysis.csenv
  type fninfo = HPfninfo.t
  val globalsN : string
  val asm_to_string : (term -> string) -> ('typ,term,'fact) Element.ctxt -> string
  val mk_fninfo : theory -> csenv -> (string -> bool) ->
                  Absyn.ext_decl list -> fninfo list
  val make_function_definitions :
      string ->                  (* name of locale where definitions will live *)
      csenv ->                   (* result of ProgramAnalysis over declarations *)
      typ list ->                (* type arguments to state type operator *)
      thm list ->                (* theorems defining names of functions *)
      fninfo list ->             (* result of mk_fninfo above *)
      (Absyn.ext_decl list -> Proof.context -> (string * term * term) list) ->
                                 (* compilation/translation function *)
      string ->                  (* name of globals locale *)
      (typ,'a,'b) Element.ctxt list ->
                                 (* globals living in the globals locale *)
      theory ->
      (string * theory)


end

structure HPInter : HPINTER =
struct

type fninfo = HPfninfo.t
type csenv = ProgramAnalysis.csenv

(* make function information - perform a preliminary analysis on the
   abstract syntax to extract function names, parameters and specifications *)
fun mk_fninfo thy csenv includeP decllist : fninfo list = let
  open Absyn NameGeneration
  (* don't fold top-level declarations into the table again: the program
     analysis that built the csenv in the first place will have already
     grabbed this *)
  fun toInclude (FnDefn((_, fname), _, _, _)) = includeP (node fname)
    | toInclude _ = false
  val table = List.foldl
                (fn (d, tab) => if toInclude d then
                                  ProgramAnalysis.update_hpfninfo0 d tab
                                else tab)
                (ProgramAnalysis.get_hpfninfo csenv)
                decllist
  fun parse_spec fname fspec =
      case fspec of
        fnspec spec => let
          val toklist = Token.explode (Thy_Header.get_keywords thy) Position.none (node spec)
                        (* it might be nice to remember where the spec came
                           from so we could put in a reasonable pos'n above *)
          val filtered = List.filter Token.is_proper toklist
          val eof = Token.stopper
          val nameproplist = valOf (Scan.read eof
                                              HoarePackage.proc_specs
                                              filtered)
                             handle Option =>
                               raise Fail ("Failed to scan spec for "^fname)
          fun nprop2Assume (name, prop) =
              ((Binding.name name, []), [(prop, [])])
        in
          [("", Element.Assumes (map nprop2Assume nameproplist))]
        end
      | fn_modifies slist => let
          val mgoal = Modifies_Proofs.gen_modify_goalstring csenv fname slist
        in
          [("", Element.Assumes [((Binding.name (fname ^ "_modifies"), []),
                                  [(mgoal, [])])])]
        end
      | didnt_translate => []
      | gcc_attribs _ => []
      | relspec _ => [] (* fixme *)
  fun parse_specs fname fspecs =
      List.concat (map (parse_spec fname) fspecs)
  fun mk_ret rettype =
      if rettype = Void then []
      else [(MString.dest (return_var_name rettype),
             CalculateState.ctype_to_typ (thy, rettype),
             rettype)]
  fun to_param vi = let
    open CalculateState ProgramAnalysis
    val cty = get_vi_type vi
    val typ = ctype_to_typ (thy,cty)
  in
    (MString.dest (get_mname vi), typ, SOME cty)
  end
  fun foldthis (_, d) acc =
      case d of
        FnDefn((_ (* retty *),fname_w), _ (* inparams *), prepost, _ (* body *)) => let
          open HoarePackage CalculateState ProgramAnalysis
          val fname = node fname_w
          val rettype = valOf (get_rettype fname csenv)
        in
          {fname = fname,
           inparams = map to_param (valOf (get_params fname csenv))
                      handle Option =>
                        raise Fail ("mk_fninfo: No function information for "^
                                    fname),
           outparams = mk_ret rettype,
           recursivep = is_recursivefn csenv fname,
           body = SOME (BodyTerm d), spec = parse_specs fname prepost,
           mod_annotated_protop = false}
          ::
          acc
        end
      | Decl d0 => let
        in
          case node d0 of
            ExtFnDecl { name, specs, params = _, rettype = _ } => let
              open CalculateState ProgramAnalysis
              val fname = node name
              val params = map to_param (valOf (get_params fname csenv))
                  handle Option =>
                         raise Fail ("mk_fninfo: No function information for "^
                                     fname)
              val rettype = valOf (get_rettype fname csenv)
	      val _ = tracing ("Added external decl for " ^ fname ^
			       " with " ^ Int.toString (length params) ^
                               " args.")
              val spec = parse_specs fname specs
              val mod_annotated_protop = isSome (get_modifies csenv fname)
              val body = NONE
            in
              {fname = fname,
               inparams = params, recursivep = false,
               outparams = mk_ret rettype, body = body,
               spec = spec, mod_annotated_protop = mod_annotated_protop}
              ::
              acc
            end
          | _ => acc
        end
in
  Symtab.fold foldthis table []
end

fun mkSpecFunction thy cse styargs (f : fninfo) = let
  open TermsTypes
  val {fname,...} = f
  val state_ty = hd styargs
  val mods = fname |> ProgramAnalysis.get_modifies cse
                   |> valOf |> Binaryset.listItems
  val s = Free("s", state_ty)
  val t = Free("t", state_ty)
  val relbody = Modifies_Proofs.gen_modify_body thy state_ty s t mods
  val collect_t = mk_collect_t (mk_prod_ty (state_ty, state_ty))
  val fbody = mk_Spec(styargs, collect_t $ list_mk_pabs([s,t], relbody))
in
  (fname, fbody, fbody)
end


(* compile bodies - turn a list of AST values into a term list *)
fun compile_fninfos cse styargs compfn lthy (fninfo : fninfo list) = let
  open HoarePackage
  fun partition (acc as (asts,specs)) fns =
      case fns of
        [] => (List.rev asts, specs)
      | {body = SOME (BodyTerm x),...} :: t => partition (x::asts,specs) t
      | (i as {mod_annotated_protop = true, ...}) :: t =>
          partition (asts,i::specs) t
      | _ :: t => partition acc t
  val (asts,toSpec) = partition ([],[]) fninfo
in
  compfn asts lthy @
  map (mkSpecFunction (Proof_Context.theory_of lthy) cse styargs) toSpec
end

fun rhs_extras rhs =
    Term.fold_aterms
        (fn v as Free _ => insert (op aconv) v | _ => I)
        rhs
        [];

fun extract_fixes elems = let
  open Element
  fun fix2term (n,tyopt,_) =
      case tyopt of
        NONE => NONE
      | SOME ty => SOME (Free(Binding.name_of n,ty))
  fun recurse elems =
      case elems of
        [] => []
      | Fixes fs::rest => List.mapPartial fix2term fs @ recurse rest
      | _ :: rest => recurse rest
in
  recurse elems
end

fun create_bodyloc_elems globs thy (name, body_t, body_stripped_t) =
let
  val rhs_vars0 = rhs_extras body_t

  (* Library.subtract has arguments in wrong order - sheesh! *)
  val rhs_vars = subtract (op aconv) globs rhs_vars0

  fun mk_rhs(nm, vars, t) = let
    val t0 = TermsTypes.list_mk_abs (vars, t)
  in
    (nm, Term.map_types (Sign.certify_typ thy) t0)
  end

  val eqt_stripped = mk_rhs(name ^ "_body", [], body_stripped_t)
  val eqt = mk_rhs(name ^ (if null rhs_vars then "_body" else "_invs_body"),
                   rhs_vars, body_t)
  fun eqn_to_definfo (nm, t) = let
    val b = Binding.name nm
  in
    ((b, NoSyn), ((Thm.def_binding b, []), t))
  end
  val elems =
      if null rhs_vars then [eqn_to_definfo eqt]
      else [eqn_to_definfo eqt_stripped, eqn_to_definfo eqt]
  type lthy_def_info = (binding * mixfix) * (Attrib.binding * term)
in
  (elems : lthy_def_info list,
   (name, if null rhs_vars then body_t else body_stripped_t))
end

val globalsN = "_global_addresses"
fun add_syntax (name,recp,inpars,outpars) thy = let
  open HoarePackage
  val name = suffix HoarePackage.proc_deco name
  val pars = map (fn par => (In,varname par)) inpars@
             map (fn par => (Out,varname par)) outpars

  val thy_decl =
      thy |> Context.theory_map (add_params Morphism.identity name pars)
          |> Context.theory_map
              (add_state_kind Morphism.identity name HoarePackage.Record)
          |> (if recp then
                Context.theory_map (add_recursive Morphism.identity name)
              else (fn x => x))
in
  thy_decl
end

fun asm_to_string tmw e =
    case e of
      Element.Assumes asms => let
        fun asm_element pfx ((nm, _ (*attrs*)), ttmlist) =
            pfx ^ Binding.name_of nm ^ ": " ^
            commas (map (tmw o #1) ttmlist) ^ "\n"
      in
        "Assumes:" ^ (if length asms = 1 then
                        " " ^ String.concat (map (asm_element "") asms)
                      else
                        "\n" ^ String.concat (map (asm_element "  ") asms))
      end
    | Element.Fixes stysynlist =>
        "Fixes: " ^ commas (map (Binding.name_of o #1) stysynlist) ^ "\n"
    | _ => "??\n"
;

fun extract_element_asms e =
    case e of
      Element.Assumes asms =>
        map (fn (nm, [(t,_)]) => (nm, t)
              | _ => raise Fail "extract_element_term: malformed Assumes") asms
    | _ => raise Fail "extract_element_term: malformed element"
;

(* The following is modelled on the code in HoarePackage.procedures_definition
*)
fun make_function_definitions localename
                              (cse : ProgramAnalysis.csenv)
                              (styargs : typ list)
                              (nmdefs : thm list)
                              (fninfo : fninfo list)
                              compfn
                              globloc
                              globals_elems
                              thy =
let
  open HoarePackage
  val localename_b = Binding.name localename
  val thy = thy |> Context.theory_map (HoarePackage.set_default_state_kind
                                       HoarePackage.Record)
  val name_pars =
      map (fn {fname,inparams,outparams,recursivep,...} =>
                (fname, recursivep, map #1 inparams, map #1 outparams))
          fninfo
  val name_specs = map (fn {fname,spec,...} => (fname,spec)) fninfo
  val thy = List.foldr (uncurry add_syntax) thy name_pars
  val lthy = Named_Target.init globloc thy
  val name_body = compile_fninfos cse styargs compfn lthy fninfo
  val _ = tracing "Translated all functions"
  val globs = extract_fixes globals_elems

  val body_elems = map (create_bodyloc_elems globs thy) name_body

  fun add_body_defs ((elems, _ (* name-body *)), lthy) = let
    fun foldthis (e, lthy) = let
      val _ = tracing ("Adding body_def for " ^ Binding.name_of (#1 (#1 e)))
    in
      Local_Theory.restore (#2 (Local_Theory.define e lthy))
    end
  in
    List.foldl foldthis lthy elems
  end
  val lthy = List.foldl add_body_defs lthy body_elems
  val thy = Local_Theory.exit_global lthy

  (* set up _impl by defining \<Gamma> *)
  val thy =
      if List.exists (isSome o #body) fninfo then let
          val lthy = Named_Target.init globloc thy
          fun get_body fni = let
            val nm = #fname fni
          in
            case (#body fni, #mod_annotated_protop fni) of
              (NONE, false) => NONE
            | _ => let
                val realnm =
                    Consts.intern (Proof_Context.consts_of lthy) (nm ^ "_body")
              in
                SOME (Syntax.check_term lthy (Const(realnm, dummyT)))
              end
          end
          (* name for thm, (proc constant, body constant) *)
          val (_, lthy) = StaticFun.define_tree_and_thms_with_defs
              @{binding \<Gamma>} (map (suffix HoarePackage.implementationN o #fname) fninfo)
              nmdefs (map get_body fninfo) @{term "id :: int => int"} lthy
        in
          Local_Theory.exit_global lthy
        end
      else thy

  val globloc_expr = ([(globloc, (("", false), Expression.Named []))], [])

  (* three levels of folding - woohoo *)
  fun add_spec_locales ((name,specs), (localemap, thy)) = let
    (* add any spec locales *)
    fun foldthis ((_, e), (localemap, thy)) = let
      val lnm_strs = extract_element_asms e
      fun innerfold (((speclocalename_b,_), tstr), (localemap, thy)) = let
        val speclocalename = Binding.name_of speclocalename_b
        (* jump into an lthy corresponding to globloc to parse the tstr; this lthy
           is dropped and not used again *)
        val lthy = Named_Target.init globloc thy
        val t = Syntax.read_term lthy tstr
        val _ = tracing ("Adding spec locale "^speclocalename^
                         (if speclocalename = "" then "" else " ")^
                         "for function "^name ^ " (" ^ tstr ^ ")")
        val e' = Element.Assumes [((speclocalename_b,[]),
                                   [(TermsTypes.mk_prop t, [])])]
        val speclocalename_b = Binding.map_name
                                   (fn s => if s = "" then
                                              suffix HoarePackage.specL name
                                            else s)
                                   speclocalename_b
        val (locname, ctxt') =
            Expression.add_locale
                speclocalename_b
                speclocalename_b
                globloc_expr
                [e']
                thy
        (* localename is the name we wanted, locname is the name Isabelle
           gives back to us.  This will be properly qualified yadda yadda *)
      in
        (Symtab.update (speclocalename, locname) localemap,
         Local_Theory.exit_global ctxt')
      end
    in
      List.foldl innerfold (localemap,thy) lnm_strs
    end
    val (speclocnames,thy) = List.foldl foldthis (localemap, thy) specs
  in
    (speclocnames, thy)
  end
  val (_ (* specloc_names *), thy) =
      List.foldl add_spec_locales (Symtab.empty, thy) name_specs

  val (globloc, ctxt) =
      Expression.add_locale localename_b localename_b globloc_expr [] thy

in
  (globloc, Local_Theory.exit_global ctxt)
end


end (* struct *)
