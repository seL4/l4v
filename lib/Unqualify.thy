(*
  Drop mandatory qualifiers from internal locale facts, constants and types
  Optionally add a different qualifier
*)

theory Unqualify
imports Main
keywords "unqualify_facts" :: thy_decl and "unqualify_consts" :: thy_decl and "unqualify_types" :: thy_decl
begin

ML \<open>

local

fun map_option _ NONE = NONE
  | map_option f (SOME x) = SOME (f x)

fun make_binding_raw (nm, pos) =
  let
    val path = Long_Name.explode nm |> rev;
    val b' = fold (Binding.qualify true) (tl path) (Binding.make (hd path, pos));
  in b' end

fun make_binding b =
  let
    val nm = Binding.name_of b;
    val pos = Binding.pos_of b;
  in make_binding_raw (nm, pos) end

val parse_opt_target = Parse.opt_target >> 
  (map_option (apfst (fn raw_nm =>
          case try (unprefix "$") raw_nm of SOME nm' => getenv_strict nm' | NONE => raw_nm)))

val unqualify_parse = parse_opt_target -- Scan.option (Args.parens Parse.name) -- Scan.repeat1 Parse.binding

in

val _ =
  Outer_Syntax.command @{command_keyword unqualify_facts} "unqualify facts"
    (unqualify_parse >> (fn ((target,qual),bs) =>
      Toplevel.local_theory NONE target (fn lthy =>
      let                            
        val facts = Proof_Context.facts_of lthy;

        fun retrieve b = Facts.retrieve (Context.Proof lthy) facts (Binding.name_of b, Binding.pos_of b);


        val thmss = map (`retrieve) bs
          |> map (fn ({thms, ...}, b) => (make_binding b, thms));

        val lthy' = Local_Theory.background_theory (fn thy =>
          let
            val naming = the_default I (map_option Name_Space.mandatory_path qual) Name_Space.global_naming;
            val thy' = Context.theory_map (Name_Space.map_naming (K naming)) thy;
            val export = Morphism.fact (Local_Theory.standard_morphism lthy (Proof_Context.init_global thy));
          in
            fold (fn (b, thms) => Global_Theory.store_thms (b,export thms) #> snd) thmss thy'
          end) lthy

       in
       lthy'
       end)))

val k = Parse.for_fixes


val _ =
  Outer_Syntax.command @{command_keyword unqualify_consts} "unqualify consts"
    (parse_opt_target -- Scan.option (Args.parens Parse.name) -- 
      Scan.repeat1 (Parse.position Parse.term) >> (fn ((target,qual),bs) =>
      Toplevel.local_theory NONE target (fn lthy =>
      let

        val ts = map (`(Syntax.parse_term lthy o fst)) bs;

        fun get_const 
            (( t as Const ("_type_constraint_", _) $
                (Const ("_type_constraint_", _) $
                  Const (nm, _))), (_, pos)) = ((nm, pos), t)
           | get_const (t as (Const ("_type_constraint_", _) $
                  Const (nm, _)), (_, pos)) = ((nm, pos), t)
           | get_const (t, (_,pos)) = error ("Not a constant or abbreviation: " ^ Syntax.string_of_term lthy t ^ Position.here pos)

        val ts' = map (apsnd (Syntax.check_term lthy) o apfst make_binding_raw o get_const) ts;

        val lthy' = Local_Theory.background_theory (fn thy =>
          let
            val naming = the_default I (map_option Name_Space.mandatory_path qual) Name_Space.global_naming;
            val thy' = Context.theory_map (Name_Space.map_naming (K naming)) thy;
            val export = Morphism.term (Local_Theory.standard_morphism lthy (Proof_Context.init_global thy));
  
          in
            fold (fn (b, t) =>
              let
                val b' = make_binding b;
                val nm = Binding.name_of b';
              in
               Sign.add_abbrev nm (b', export t) #> snd
              end) ts' thy'
          end) lthy

       in
       lthy'
       end)))


val _ =
  Outer_Syntax.command @{command_keyword unqualify_types} "unqualify types"
    (parse_opt_target -- Scan.option (Args.parens Parse.name) -- 
      Scan.repeat1 (Parse.position Parse.typ) >> (fn ((target,qual),bs) =>
      Toplevel.local_theory NONE target (fn lthy =>
      let
        
        fun err (T, pos) = 
          error ("Not a defined type or type synonym: " ^ Syntax.string_of_typ lthy T ^ Position.here pos)

   
        val Ts = map (`(Syntax.parse_typ lthy o fst)) bs;

        fun get_type (T, (_, pos)) = case try dest_Type T of
        SOME (nm, Ts) => (if can dest_funT T then err (T,pos) else ((nm, pos), (T,Ts)))
        | NONE => err (T,pos)

        fun check_Ts (T,Ts) = (Syntax.check_typ lthy T, 
          fold Term.add_tfree_namesT Ts [])

        val Ts' = map (apsnd check_Ts o apfst make_binding_raw o get_type) Ts;

        val lthy' = Local_Theory.background_theory (fn thy =>
          let
            val naming = the_default I (map_option Name_Space.mandatory_path qual) Name_Space.global_naming;
            val thy' = Context.theory_map (Name_Space.map_naming (K naming)) thy;
          in
            fold (fn (b, (T,frees)) =>
              let
                val b' = make_binding b;
              in
               Sign.add_type_abbrev lthy (b',frees, T)
              end) Ts' thy'
          end) lthy

       in
       lthy'
       end)))

end

\<close>

end