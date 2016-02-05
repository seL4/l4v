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


in

val _ =
  Outer_Syntax.command @{command_keyword unqualify_facts} "unqualify facts"
    (Parse.opt_target -- Scan.option (Args.parens Parse.name) -- Parse.xthms1 >> 
      (fn ((target,qual),rfs) =>
      Toplevel.local_theory NONE target (fn lthy =>
      let                            
        val facts = Proof_Context.facts_of lthy;

        val nms =  
          map (fn (rf, atts) => (Facts.select rf []; ((Facts.name_of_ref rf, Facts.pos_of_ref rf), atts))) rfs;

        fun retrieve ((nm, pos), _)  = Facts.retrieve (Context.Proof lthy) facts (nm, pos);


        val thmss = map (`retrieve) nms
          |> map (fn ({thms, static, ...}, b) => 
            (if not static then error ("Can't unqualify dynamic fact: " ^ (fst (fst b)) ^ Position.here (snd (fst b)))
            else (apfst make_binding_raw b, thms)));

        val naming = Sign.naming_of (Proof_Context.theory_of lthy)
          |> the_default I (map_option Name_Space.mandatory_path qual);

        val lthy' = Local_Theory.background_theory (fn thy =>
          let
            val thy' = Context.theory_map (Name_Space.map_naming (K naming)) thy;
            val global_ctxt = (Proof_Context.init_global thy);
            val morph = Local_Theory.standard_morphism lthy global_ctxt;
            val thmss' = map (fn ((b, att),thms) => ((b, []), [(thms, Attrib.check_attribs global_ctxt att)])) thmss; 
          in
            snd (Attrib.global_notes Thm.lemmaK (Attrib.transform_facts morph thmss') thy')
          end) lthy

       in
       lthy'
       end)))

val _ =
  Outer_Syntax.command @{command_keyword unqualify_consts} "unqualify consts"
    (Parse.opt_target -- Scan.option (Args.parens Parse.name) -- 
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

        val naming = Sign.naming_of (Proof_Context.theory_of lthy)
          |> the_default I (map_option Name_Space.mandatory_path qual);

        val lthy' = Local_Theory.background_theory (fn thy =>
          let
            val thy' = Context.theory_map (Name_Space.map_naming (K naming)) thy;
            val export = Morphism.term (Local_Theory.standard_morphism lthy (Proof_Context.init_global thy));
  
          in
            fold (fn (b, t) =>
              let
                val b' = make_binding b;
              in
               Sign.add_abbrev Print_Mode.input (b', export t) #> snd
              end) ts' thy'
          end) lthy

       in
       lthy'
       end)))


val _ =
  Outer_Syntax.command @{command_keyword unqualify_types} "unqualify types"
    (Parse.opt_target -- Scan.option (Args.parens Parse.name) -- 
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

        val naming = Sign.naming_of (Proof_Context.theory_of lthy)
          |> the_default I (map_option Name_Space.mandatory_path qual);

        val lthy' = Local_Theory.background_theory (fn thy =>
          let
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