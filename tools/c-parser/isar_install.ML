(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

signature ISAR_INSTALL =
sig

  type additional_options
  val GhostState : string -> additional_options
  val get_Csyntax : theory -> string -> Absyn.ext_decl list
  val gen_umm_types_file : string -> string -> theory -> theory
  val do_cpp : {error_detail : int, cpp_path : string option} ->
               {includes : string list, filename : string} -> string * bool
  val install_C_file : (((bool option * bool option) * bool option) * string) *
                       additional_options list option ->
                       theory -> theory
  val interactive_install : string -> theory -> theory
  val mk_thy_relative : theory -> string -> string

  val extra_trace_filename : string Config.T
  val cpp_path : string Config.T

  val installed_C_files : theory
    -> {c_filename : string, locale_names : string list,
        options: (bool * bool * bool),
        additional_options: additional_options list} list
end

structure IsarInstall : ISAR_INSTALL =
struct

type 'a wrap = 'a Region.Wrap.t

fun setup_feedback extra_output_filename = let
    val trace_extra = case extra_output_filename of
        NONE => K ()
      | SOME f => let
        val out = TextIO.openOut f
      in fn s => (TextIO.output (out, s); TextIO.flushOut out) end
    val add_extra = case extra_output_filename of
        NONE => (fn _ => fn f => f)
      | SOME _ => (fn pfx => fn f => fn s => (trace_extra (pfx ^ s); f s))
  in
    Feedback.errorf := add_extra "ERROR: " (ignore o error);
    Feedback.warnf := add_extra "" warning;
    Feedback.informf := add_extra "" (Output.tracing o Feedback.timestamp)
  end

val extra_trace_filename = let
  val (config, setup) =
      Attrib.config_string @{binding "CParser_extra_trace_file"} (K "")
in
  Context.>>(Context.map_theory setup);
  config
end

fun setup_feedback_thy thy = let
    val str = Config.get_global thy extra_trace_filename
  in setup_feedback (if str = "" then NONE else SOME str) end

val _ = setup_feedback NONE

structure C_Includes = Theory_Data
(struct
   type T = string list
   val empty = []
   val extend = I
   val merge = Library.merge (op =)
end);

datatype additional_options = MachineState of string | GhostState of string | CRoots of string list

type install_data = {c_filename : string, locale_names : string list,
        options: (bool * bool * bool),
        additional_options: additional_options list}
structure C_Installs = Theory_Data
(struct
   type T = install_data list
   val empty = []
   val extend = I
   val merge = Library.merge (op =)
end);
val installed_C_files = C_Installs.get

structure IsaPath = Path

val get_Cdir = Resources.master_directory

fun mk_thy_relative thy s =
    if OS.Path.isRelative s then OS.Path.concat(Path.implode (get_Cdir thy), s)
    else s

val cpp_path = let
  val (cpp_path_config, cpp_path_setup) =
      Attrib.config_string (Binding.name "cpp_path") (K "/usr/bin/cpp")
in
  Context.>>(Context.map_theory cpp_path_setup);
  cpp_path_config
end

val munge_info_fname = let
  val (mifname_config, mifname_setup) =
      Attrib.config_string (Binding.name "munge_info_fname") (K "")
in
  Context.>>(Context.map_theory mifname_setup);
  mifname_config
end

val report_cpp_errors = let
  val (report_cpp_errors_config, report_cpp_errors_setup) =
      Attrib.config_int (Binding.name "report_cpp_errors") (K 10)
in
  Context.>>(Context.map_theory report_cpp_errors_setup);
  report_cpp_errors_config
end

fun do_cpp {error_detail, cpp_path} {includes, filename} =
  case cpp_path of
      NONE => (File.standard_path (Path.explode filename), false)
    | SOME p =>
      let
        open OS.FileSys OS.Process
        val tmpname = tmpName()
        val err_tmpname = tmpName()
        val includes_string = String.concat (map (fn s => "-I\""^s^"\" ") includes)
        fun plural 1 = "" | plural _ = "s"
        val cmdline =
            p ^ " " ^ includes_string ^ " -CC \"" ^ filename ^ "\" > " ^ tmpname ^ " 2> " ^ err_tmpname
      in
        if isSuccess (system cmdline)
        then (OS.FileSys.remove err_tmpname; (tmpname, true))
        else let val _ = OS.FileSys.remove tmpname
                 val (msg, rest) = File.read_lines (Path.explode err_tmpname) |> chop error_detail
                 val _ = OS.FileSys.remove err_tmpname
                 val _ = warning ("cpp failed on " ^ filename ^ "\nCommand: " ^ cmdline ^
                                  "\n\nOutput:\n" ^
                                  cat_lines (msg @ (if null rest then [] else
                                                    ["(... " ^ string_of_int (length rest) ^
                                                     " more line" ^ plural (length rest) ^ ")"])))
             in raise Feedback.WantToExit ("cpp failed on " ^ filename) end
      end

fun get_Csyntax thy s = let
  val _ = setup_feedback_thy thy
  val cpp_option =
      case Config.get_global thy cpp_path of
          "" => NONE
        | s => SOME s
  val cpp_error_count = Config.get_global thy report_cpp_errors
  val (ast0, _) =
      StrictCParser.parse
          (do_cpp {error_detail = cpp_error_count, cpp_path = cpp_option})
          15
          (C_Includes.get thy)
          (mk_thy_relative thy s)
      handle IO.Io {name, ...} => error ("I/O error on "^name)
in
  ast0 |> SyntaxTransforms.remove_anonstructs |> SyntaxTransforms.remove_typedefs
end

fun define_naming_scheme [] _ = I
  | define_naming_scheme fninfo nmdefs = let
  fun name_term fni = SOME (HOLogic.mk_string (#fname fni))
  fun name_name fni = #fname fni ^ "_name"

  in StaticFun.define_tree_and_thms_with_defs
      (Binding.name NameGeneration.naming_scheme_name)
      (map name_name fninfo) nmdefs
      (map name_term fninfo) @{term "id :: int => int"}
  #> snd end

fun define_function_names fninfo thy = let
  open Feedback
  fun decl1 (fni, (n, defs, lthy)) = let
    open TermsTypes
    val cname = suffix HoarePackage.proc_deco (#fname fni)
    val _ = informStr (4, "Adding ("^cname^" :: int) = "^Int.toString n)
    val b = Binding.name cname
    val ((_, (_, th)), lthy) =
        lthy
        |> Local_Theory.open_target |> snd
        |>Local_Theory.define ((b, NoSyn),
                              ((Thm.def_binding b, []), mk_int_numeral n))
    val lthy' = Local_Theory.close_target lthy
    val morph  = Proof_Context.export_morphism lthy lthy'
    val th'     = Morphism.thm morph th

  in
    (n + 1, th' :: defs, lthy')
  end
  val (_, defs, lthy) =
      List.foldl decl1 (1, [], Named_Target.theory_init thy) fninfo
  val lthy' = define_naming_scheme fninfo (List.rev defs) lthy
in
  (defs, Local_Theory.exit_global lthy')
end


fun print_addressed_vars cse = let
  open ProgramAnalysis Feedback
  val globs = get_globals cse
  val _ = informStr (0, "There are "^Int.toString (length globs)^" globals: "^
                        commas_quote (map srcname globs))
  val addressed = get_addressed cse
  val addr_vars = map MString.dest (MSymTab.keys addressed)
  val _ = informStr (0, "There are "^Int.toString (length addr_vars)^
                        " addressed variables: "^ commas_quote addr_vars)
in
  ()
end

fun define_global_initializers globloc msgpfx name_munger mungedb cse globs thy = let
  open ProgramAnalysis Absyn
  val lthy = Named_Target.init globloc thy
  val globinits = let
    val inittab = get_globinits cse
    fun foldthis (gnm : MString.t, gty) defs = let
      val rhs_opt = MSymTab.lookup inittab gnm
      val rhs_t =
          case  rhs_opt of
            NONE => ExpressionTranslation.zero_term thy (get_senv cse) gty
          | SOME rhs => let
              open ExpressionTranslation
              fun error _ = (Feedback.errorStr'(eleft rhs, eright rhs,
                                                "Illegal form in initialisor for\
                                                \ global");
                             raise Fail "Bad global initialisation")
              val fakeTB = TermsTypes.TB {var_updator = error, var_accessor = error,
                                          rcd_updator = error, rcd_accessor = error}
              fun varinfo s = stmt_translation.state_varlookup "" s mungedb
              val ei = expr_term lthy cse fakeTB varinfo rhs
              val ei = case gty of
                         Array _ => ei
                       | _ => typecast(thy,gty,ei)
            in
              rval_of ei (Free("x", TermsTypes.bool))
               (* the Free("x",bool) is arbitrary as the constant
                  expression should be ignoring the state argument *)
            end
    in
      (gnm, gty, rhs_t) :: defs
    end
  in
    MSymTab.fold foldthis globs []
  end
  fun define1 ((nm, ty, value), lthy) = let
    open Feedback
    val _ = informStr(2,
                      msgpfx ^ MString.dest nm ^ " (of C type "^
                      Absyn.tyname ty ^") to have value "^
                      Syntax.string_of_term lthy value)
    val b = Binding.name (MString.dest (name_munger nm))
    val (_, lthy) =
        Local_Theory.define
            ((b, NoSyn), ((Thm.def_binding b, []), value))
            lthy
  in
    lthy
  end
in
  List.foldl define1 lthy globinits
             |> Local_Theory.exit_global
end

val use_anon_vars = let
  val (uavconfig, uavsetup) = Attrib.config_bool (Binding.name "use_anonymous_local_variables") (K false)
in
  Context.>>(Context.map_theory uavsetup);
  uavconfig
end

val allow_underscore_idents = let
  val (auiconfig, auisetup) = Attrib.config_bool (Binding.name "allow_underscore_idents") (K false)
in
  Context.>>(Context.map_theory auisetup);
  auiconfig
end

fun get_callees cse slist = let
  val {callgraph = cg,...} = ProgramAnalysis.compute_callgraphs cse
  fun recurse acc worklist =
      case worklist of
          [] => acc
        | fnname :: rest =>
          if Binaryset.member(acc, fnname) then recurse acc rest
          else
            case Symtab.lookup cg fnname of
                NONE => recurse (Binaryset.add(acc, fnname)) rest
              | SOME set => recurse (Binaryset.add(acc, fnname))
                                    (Binaryset.listItems set @ rest)
in
  recurse (Binaryset.empty String.compare) slist
end

fun install_C_file0 (((((memsafe),ctyps),cdefs),s),statetylist_opt) thy = let
  val _ = setup_feedback_thy thy
  val {base = localename,...} = OS.Path.splitBaseExt (OS.Path.file s)
  val _ = not (Long_Name.is_qualified localename) orelse
            raise Fail ("Base of filename looks like qualified Isabelle ID: "^
                        localename)
  val _ = localename <> "" orelse
          raise Fail ("Filename (>'" ^ s ^
                      "'<) gives \"\" as locale name, which is illegal")
  val statetylist = case statetylist_opt of NONE => [] | SOME l => List.rev l
  val mstate_ty =
      case get_first (fn (MachineState s) => SOME s | _ => NONE) statetylist of
        NONE => TermsTypes.nat
      | SOME s => Syntax.read_typ_global thy s
  val roots_opt =
      get_first (fn CRoots slist => SOME slist | _ => NONE) statetylist
  val gstate_ty =
      case get_first (fn (GhostState s) => SOME s | _ => NONE) statetylist of
        NONE => TermsTypes.unit
      | SOME s => Syntax.read_typ_global thy s
  val thy = Config.put_global CalculateState.current_C_filename s thy
  val thy = CalculateState.store_ghostty (s, gstate_ty) thy
  val anon_vars = Config.get_global thy use_anon_vars
  val uscore_idents = Config.get_global thy allow_underscore_idents

  val o2b = isSome
  val install_typs = not (o2b cdefs) orelse (o2b ctyps)
  val install_defs = not (o2b ctyps) orelse (o2b cdefs)
  val ms = o2b memsafe
  val ast = get_Csyntax thy s
  open ProgramAnalysis CalculateState Feedback
  val owners =
      (* non-null if there are any globals that have owned_by annotations *)
      let
        open StmtDecl RegionExtras
        fun getowner d =
            case d of
                Decl d =>
                (case node d of
                     VarDecl (_, _, _, _, attrs) => get_owned_by attrs
                   | _ => NONE)
              | _ => NONE
      in
        List.mapPartial getowner ast
      end
  val mifname = case Config.get_global thy munge_info_fname of
                  "" => NONE
                | s => SOME s

  val ((ast, _ (* init_stmts *)), cse) =
      process_decls {anon_vars=anon_vars,owners = owners,
                     allow_underscore_idents = uscore_idents,
                     munge_info_fname = mifname}
                    ast
  val () = export_mungedb cse
  val thy = store_csenv (s, cse) thy

  val _ = print_addressed_vars cse
  val ecenv = cse2ecenv cse
  val thy = define_enum_consts ecenv thy
  val state = create_state cse
  val (thy, rcdinfo) = mk_thy_types cse install_typs thy
  val ast = SyntaxTransforms.remove_embedded_fncalls cse ast
in
  if install_defs then let
      val (thy, vdecls, globs) =
          mk_thy_decls
            state {owners=owners,gstate_ty=gstate_ty,mstate_ty=mstate_ty} thy
      val loc_b = Binding.name (suffix HPInter.globalsN localename)
      val (globloc, ctxt) =
          Expression.add_locale loc_b loc_b ([], []) globs thy
      val thy = Local_Theory.exit_global ctxt
      val _ = Output.state ("Created locale for globals (" ^ Binding.print loc_b ^
                       ")- with " ^ Int.toString (length globs) ^
                       " globals elements")
      val _ = app (fn e => Output.state ("-- " ^ HPInter.asm_to_string (Syntax.string_of_term ctxt) e))
                  globs
      val mungedb = mk_mungedb vdecls
      val thy = CalculateState.store_mungedb (s, mungedb) thy
      val thy =
          define_global_initializers globloc "Defining untouched global constant "
                                     NameGeneration.untouched_global_name
                                     mungedb
                                     cse
                                     (calc_untouched_globals cse)
                                     thy
      val thy =
          if Config.get_global thy CalculateState.record_globinits then let
              val globs0 = get_globals cse
              val globs_types = map (fn vi => (get_mname vi, get_vi_type vi)) globs0
              val glob_table = MSymTab.make globs_types
            in
              define_global_initializers
                  globloc "Defining initializers for all globals "
                  NameGeneration.global_initializer_name
                  mungedb
                  cse
                  glob_table
                  thy
            end
          else (Feedback.informStr (0,
                    "Ignoring initialisations of modified globals (if any)");
                thy)
      open TermsTypes
      val (globty, styargs) = let
        val globty0 = Type(Sign.intern_type thy
                                            NameGeneration.global_rcd_name, [])
        val globty = expand_tyabbrevs (thy2ctxt thy) globty0
        val statetype0 =
            Type(Sign.intern_type thy NameGeneration.local_rcd_name, [globty])
        val statetype = expand_tyabbrevs (thy2ctxt thy) statetype0
            (* only happens if no local variables, = no functions declared,
               = pretty bogus
               (decl_only and bigstruct test cases are like this though) *)
            handle TYPE _  => alpha
      in
        (globty, [statetype, int, StrictC_errortype_ty])
      end
      val toTranslate = Option.map (get_callees cse) roots_opt
      val toTranslate_s =
          case toTranslate of
              NONE => "all functions"
            | SOME set => "functions " ^
                          String.concatWith ", " (Binaryset.listItems set) ^
                          " (derived from "^
                          String.concatWith ", " (valOf roots_opt) ^ ")"
      val _ =
          Feedback.informStr (0, "Beginning function translation for " ^
                    toTranslate_s)
      val toTranslateP =
          case toTranslate of
              NONE => (fn _ => true)
            | SOME set => (fn s => Binaryset.member(set,s))
      val fninfo : HPInter.fninfo list = HPInter.mk_fninfo thy cse toTranslateP ast
      val (nmdefs, thy) = define_function_names fninfo thy
      val compile_bodies =
          stmt_translation.define_functions (globty, styargs)
                                            mungedb
                                            cse
                                            fninfo
                                            rcdinfo
                                            ms
      val (loc2, thy) =
          HPInter.make_function_definitions localename
                                            cse
                                            styargs
                                            (List.rev nmdefs)
                                            fninfo
                                            compile_bodies
                                            globloc
                                            globs
                                            thy
      val thy =
          if not (Symtab.is_empty (get_defined_functions cse)) then
            Modifies_Proofs.prove_all_modifies_goals thy cse toTranslateP styargs loc2
          else thy (* like this is ever going to happen *)
    in
      C_Installs.map (fn ss =>
        {c_filename = s, locale_names = [globloc, loc2],
          options = (ms, install_typs, install_defs),
          additional_options = statetylist} :: ss) thy
    end
  else
      C_Installs.map (fn ss =>
        {c_filename = s, locale_names = [],
          options = (ms, install_typs, install_defs),
          additional_options = statetylist} :: ss) thy
end handle e as TYPE (s,tys,tms) =>
         (Feedback.informStr (0, s ^ "\n" ^
                   Int.toString (length tms) ^ " term(s): " ^
                   String.concatWith
                       ", "
                       (map (Syntax.string_of_term @{context}) tms) ^ "\n" ^
                   Int.toString (length tys) ^ " type(s): "^
                   String.concatWith
                       ", "
                       (map (Syntax.string_of_typ @{context}) tys));
          raise e)

fun install_C_file args thy =
    thy |> install_C_file0 args
        |> Config.put_global CalculateState.current_C_filename ""

(* for interactive debugging/testing *)
fun interactive_install s thy =
  install_C_file ((((NONE, NONE), NONE), s), NONE) thy
  handle TYPE (s,tys,tms) =>
         (Feedback.informStr (0, s ^ "\n" ^
                   Int.toString (length tms) ^ " term(s): " ^
                   String.concatWith
                       ", "
                       (map (Syntax.string_of_term @{context}) tms) ^ "\n" ^
                   Int.toString (length tys) ^ " type(s): "^
                   String.concatWith
                       ", "
                       (map (Syntax.string_of_typ @{context}) tys));
          thy);


fun install_C_types s thy = let
  open CalculateState ProgramAnalysis
  val ast = get_Csyntax thy s
  val (_, cse) =
      process_decls {
        anon_vars = Config.get_global thy use_anon_vars,
        allow_underscore_idents = Config.get_global thy allow_underscore_idents,
        munge_info_fname = NONE,
        owners = []} ast
  val (thy, _) = mk_thy_types cse true thy
in
  thy
end

fun gen_umm_types_file inputfile outputfile thy = let
  open ProgramAnalysis
  val ast = get_Csyntax thy inputfile
  val (_, cse) =
      process_decls {
        anon_vars = Config.get_global thy use_anon_vars,
        allow_underscore_idents = Config.get_global thy allow_underscore_idents,
        munge_info_fname = NONE,
        owners = []} ast
  val _ = CalculateState.gen_umm_types_file cse outputfile
in
  thy
end

val memsafeN = "memsafe"
val typesN = "c_types"
val defsN = "c_defs"
val mtypN = "machinety"
val ghosttypN = "ghostty"
val rootsN = "roots"

local
  structure P = Parse
  structure K = Keyword
in
fun new_include s thy = C_Includes.map (fn sl => mk_thy_relative thy s::sl) thy

val _ = Outer_Syntax.command @{command_keyword "new_C_include_dir"}
                            "add a directory to the include path"
                            (P.text >> (Toplevel.theory o new_include))

val file_inclusion = let
  val typoptions =
      P.reserved mtypN |-- (P.$$$ "=" |-- P.text >> MachineState) ||
      P.reserved ghosttypN |-- (P.$$$ "=" |-- P.text >> GhostState) ||
      P.reserved rootsN |-- (P.$$$ "=" |-- (P.$$$ "[" |-- P.enum1 "," P.text --| P.$$$ "]") >> CRoots)
in
    ((Scan.option (P.$$$ memsafeN)) --
     (Scan.option (P.$$$ typesN)) --
     (Scan.option (P.$$$ defsN)) -- P.text --
     (Scan.option
          (P.$$$ "[" |-- P.enum1 "," typoptions --| P.$$$ "]"))) >>
    (Toplevel.theory o install_C_file)
end

val _ =
    Outer_Syntax.command
      @{command_keyword "install_C_file"}
      "import a C file"
      file_inclusion

val _ =
    Outer_Syntax.command
      @{command_keyword "install_C_types"}
      "install types from a C file"
      (P.text >> (Toplevel.theory o install_C_types))

end

end; (* struct *)
