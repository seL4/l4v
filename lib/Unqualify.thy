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

fun make_notation b =

  let
    val str = Binding.name_of b
      |> String.translate(fn #"_" => "'_" | x => Char.toString x)

  in str end

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
      Scan.repeat1 (Parse.position (Parse.const -- Scan.option (Parse.$$$ "::" |-- Parse.typ))) >> (fn ((target,qual),bs) =>
      Toplevel.local_theory NONE target (fn lthy =>
      let

        fun read_const (t, T_in) =
        let
          val (nm, T) = dest_Const (Proof_Context.read_const {proper = true, strict = false} lthy t);
  
        in case map_option (Syntax.read_typ lthy) T_in of
            SOME T' => (nm, T')
           | NONE => (nm, T) end

        val ts = map (`( read_const o fst)) bs;

        fun get_const (((nm, T) , (_, pos))) = ((nm, pos), Const (nm, T))

        val ts' = map (apfst make_binding_raw o get_const) ts;

        val naming = Sign.naming_of (Proof_Context.theory_of lthy)
          |> the_default I (map_option Name_Space.mandatory_path qual);

        val lthy' = Local_Theory.background_theory (fn thy =>
          let
            val thy' = Context.theory_map (Name_Space.map_naming (K naming)) thy;
            val export = Morphism.term (Local_Theory.standard_morphism lthy (Proof_Context.init_global thy));
            
  
          in
            fold (fn (b, t) =>
              let
                val b' = b 
                  |> make_binding;
                val t' = export t;

              in
                Sign.add_abbrev Print_Mode.internal(b', t') #> snd #>
                Sign.notation true ("", false) [(t', Delimfix (make_notation b'))]
              end) ts' thy'
          end) lthy

       in
       lthy'
       end)))
                                                  

val _ =
  Outer_Syntax.command @{command_keyword unqualify_types} "unqualify types"
    (Parse.opt_target -- Scan.option (Args.parens Parse.name) -- 
      Scan.repeat1 (Parse.position Parse.type_const) >> (fn ((target,qual),bs) =>
      Toplevel.local_theory NONE target (fn lthy =>
      let

        
        fun err (T, pos) = 
          error ("Not a defined type or type synonym: " ^ Syntax.string_of_typ lthy T ^ Position.here pos)

   
        val Ts = map (`(Proof_Context.read_type_name {proper = true, strict = false} lthy o fst)) bs;

        fun get_type (T, (_, pos)) = case try dest_Type T of
        SOME (nm, Ts) => (if can dest_funT T then err (T,pos) else ((nm, pos), (nm,Ts)))
        | NONE => err (T,pos)

        val Ts' = map (apfst make_binding_raw o get_type) Ts;

        val naming = Sign.naming_of (Proof_Context.theory_of lthy)
          |> the_default I (map_option Name_Space.mandatory_path qual);

        val lthy' = Local_Theory.background_theory (fn thy =>
          let
            val thy' = Context.theory_map (Name_Space.map_naming (K naming)) thy;
          in
            fold (fn (b, (nm,frees_raw)) =>
              let

                val Ts = lthy
                  |> Variable.invent_types (map (fn _ => Proof_Context.default_sort lthy ("'a",~1)) frees_raw)
                  |> fst
                  |> map TFree

                val T = Type (nm, Ts)
                val frees = map (fst o dest_TFree) Ts
                val b' = make_binding b;

                val str = make_notation b'
                  |> fold (fn _ => fn s => "_ " ^ s) Ts

              in
                Sign.add_type_abbrev lthy (b',frees, T) #>
                Sign.type_notation true ("", false) [(T, Delimfix str)]
              end) Ts' thy'
          end) lthy

       in
       lthy'
       end)))

end
\<close>

end