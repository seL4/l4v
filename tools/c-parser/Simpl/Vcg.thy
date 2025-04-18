(*  Author:      Norbert Schirmer
    Maintainer:  Norbert Schirmer, norbert.schirmer at web de

Copyright (C) 2004-2008 Norbert Schirmer
Copyright (c) 2022 Apple Inc. All rights reserved.

*)

section \<open>Facilitating the Hoare Logic\<close>
theory Vcg
imports StateSpace "HOL-Statespace.StateSpaceLocale" Generalise
keywords "procedures" "hoarestate" :: thy_defn
begin

axiomatization NoBody::"('s,'p,'f) com"

ML_file \<open>hoare.ML\<close>

method_setup hoare = "Hoare.hoare"
  "raw verification condition generator for Hoare Logic"

method_setup hoare_raw = "Hoare.hoare_raw"
  "even more raw verification condition generator for Hoare Logic"

method_setup vcg = "Hoare.vcg"
  "verification condition generator for Hoare Logic"

method_setup vcg_step = "Hoare.vcg_step"
  "single verification condition generation step with light simplification"


method_setup hoare_rule = "Hoare.hoare_rule"
  "apply single hoare rule and solve certain sideconditions"

text \<open>Variables of the programming language are represented as components
of a record. To avoid cluttering up the namespace of Isabelle with lots of
typical variable names, we append a unusual suffix at the end of each name by
parsing
\<close>

definition list_multsel:: "'a list \<Rightarrow> nat list \<Rightarrow> 'a list" (infixl \<open>!!\<close> 100)
  where "xs !! ns = map (nth xs) ns"

definition list_multupd:: "'a list \<Rightarrow> nat list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "list_multupd xs ns ys = foldl (\<lambda>xs (n,v). xs[n:=v]) xs (zip ns ys)"

nonterminal lmupdbinds and lmupdbind

syntax
  \<comment> \<open>multiple list update\<close>
  "_lmupdbind":: "['a, 'a] => lmupdbind"    (\<open>(2_ [:=]/ _)\<close>)
  "" :: "lmupdbind => lmupdbinds"    (\<open>_\<close>)
  "_lmupdbinds" :: "[lmupdbind, lmupdbinds] => lmupdbinds"    (\<open>_,/ _\<close>)
  "_LMUpdate" :: "['a, lmupdbinds] => 'a"    (\<open>_/[(_)]\<close> [900,0] 900)

syntax_consts
  "_lmupdbind" "_lmupdbinds" "_LMUpdate" == list_multupd

translations
  "_LMUpdate xs (_lmupdbinds b bs)" == "_LMUpdate (_LMUpdate xs b) bs"
  "xs[is[:=]ys]" == "CONST list_multupd xs is ys"


subsection \<open>Some Fancy Syntax\<close>


(* priority guidline:
 * If command should be atomic for the guard it must have at least priority 21.
 *)

text \<open>reverse application\<close>
definition rapp:: "'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b" (infixr \<open>|>\<close> 60)
  where "rapp x f = f x"


nonterminal
  newinit and
  newinits and
  locinit and
  locinits and
  switchcase and
  switchcases and
  grds and
  grd and
  bdy and
  basics and
  basic and
  basicblock

notation
  Skip  (\<open>SKIP\<close>) and
  Throw  (\<open>THROW\<close>)

syntax
  "_raise":: "'c \<Rightarrow> 'c \<Rightarrow> ('a,'b,'f) com"       (\<open>(RAISE _ :==/ _)\<close> [30, 30] 23)
  "_seq"::"('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com" (\<open>_;;/ _\<close> [20, 21] 20)
  "_guarantee"     :: "'s set \<Rightarrow> grd"       (\<open>_\<surd>\<close> [1000] 1000)
  "_guaranteeStrip":: "'s set \<Rightarrow> grd"       (\<open>_#\<close> [1000] 1000)
  "_grd"           :: "'s set \<Rightarrow> grd"       (\<open>_\<close> [1000] 1000)
  "_last_grd"      :: "grd \<Rightarrow> grds"         (\<open>_\<close> 1000)
  "_grds"          :: "[grd, grds] \<Rightarrow> grds" (\<open>_,/ _\<close> [999,1000] 1000)
  "_guards"        :: "grds \<Rightarrow> ('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com"
                                            (\<open>(_/\<longmapsto> _)\<close> [60, 21] 23)
  "_quote"       :: "'b => ('a => 'b)"
  "_antiquoteCur0"  :: "('a => 'b) => 'b"       (\<open>\<acute>_\<close> [1000] 1000)
  "_antiquoteCur"  :: "('a => 'b) => 'b"
  "_antiquoteOld0"  :: "('a => 'b) => 'a => 'b"       (\<open>\<^bsup>_\<^esup>_\<close> [1000,1000] 1000)
  "_antiquoteOld"  :: "('a => 'b) => 'a => 'b"
  "_Assert"      :: "'a => 'a set"            (\<open>(\<lbrace>_\<rbrace>)\<close> [0] 1000)
  "_AssertState" :: "idt \<Rightarrow> 'a => 'a set"     (\<open>(\<lbrace>_. _\<rbrace>)\<close> [1000,0] 1000)
  "_Assign"      :: "'b => 'b => ('a,'p,'f) com"    (\<open>(_ :==/ _)\<close> [30, 30] 23)
  "_Init"        :: "ident \<Rightarrow> 'c \<Rightarrow> 'b \<Rightarrow> ('a,'p,'f) com"
                                             (\<open>(\<acute>_ :==\<^bsub>_\<^esub>/ _)\<close> [30,1000, 30] 23)
  "_GuardedAssign":: "'b => 'b => ('a,'p,'f) com"    (\<open>(_ :==\<^sub>g/ _)\<close> [30, 30] 23)
  "_newinit"      :: "[ident,'a] \<Rightarrow> newinit" (\<open>(2\<acute>_ :==/ _)\<close>)
  ""             :: "newinit \<Rightarrow> newinits"    (\<open>_\<close>)
  "_newinits"    :: "[newinit, newinits] \<Rightarrow> newinits" (\<open>_,/ _\<close>)
  "_New"         :: "['a, 'b, newinits] \<Rightarrow> ('a,'b,'f) com"
                                            (\<open>(_ :==/(2 NEW _/ [_]))\<close> [30, 65, 0] 23)
  "_GuardedNew"  :: "['a, 'b, newinits] \<Rightarrow> ('a,'b,'f) com"
                                            (\<open>(_ :==\<^sub>g/(2 NEW _/ [_]))\<close> [30, 65, 0] 23)
  "_NNew"         :: "['a, 'b, newinits] \<Rightarrow> ('a,'b,'f) com"
                                            (\<open>(_ :==/(2 NNEW _/ [_]))\<close> [30, 65, 0] 23)
  "_GuardedNNew"  :: "['a, 'b, newinits] \<Rightarrow> ('a,'b,'f) com"
                                            (\<open>(_ :==\<^sub>g/(2 NNEW _/ [_]))\<close> [30, 65, 0] 23)

  "_Cond"        :: "'a bexp => ('a,'p,'f) com => ('a,'p,'f) com => ('a,'p,'f) com"
        (\<open>(0IF (_)/ (2THEN/ _)/ (2ELSE _)/ FI)\<close> [0, 0, 0] 71)
  "_Cond_no_else":: "'a bexp => ('a,'p,'f) com => ('a,'p,'f) com"
        (\<open>(0IF (_)/ (2THEN/ _)/ FI)\<close> [0, 0] 71)
  "_GuardedCond" :: "'a bexp => ('a,'p,'f) com => ('a,'p,'f) com => ('a,'p,'f) com"
        (\<open>(0IF\<^sub>g (_)/ (2THEN _)/ (2ELSE _)/ FI)\<close> [0, 0, 0] 71)
  "_GuardedCond_no_else":: "'a bexp => ('a,'p,'f) com => ('a,'p,'f) com"
        (\<open>(0IF\<^sub>g (_)/ (2THEN _)/ FI)\<close> [0, 0] 71)
  "_While_inv_var"   :: "'a bexp => 'a assn  \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bdy
                          \<Rightarrow> ('a,'p,'f) com"
        (\<open>(0WHILE (_)/ INV (_)/ VAR (_) /_)\<close>  [25, 0, 0, 81] 71)
  "_WhileFix_inv_var"   :: "'a bexp => pttrn \<Rightarrow> ('z \<Rightarrow> 'a assn)  \<Rightarrow>
                            ('z \<Rightarrow> ('a \<times> 'a) set) \<Rightarrow> bdy
                          \<Rightarrow> ('a,'p,'f) com"
        (\<open>(0WHILE (_)/ FIX _./ INV (_)/ VAR (_) /_)\<close>  [25, 0, 0, 0, 81] 71)
  "_WhileFix_inv"   :: "'a bexp => pttrn \<Rightarrow> ('z \<Rightarrow> 'a assn)  \<Rightarrow> bdy
                          \<Rightarrow> ('a,'p,'f) com"
        (\<open>(0WHILE (_)/ FIX _./ INV (_) /_)\<close>  [25, 0, 0, 81] 71)
  "_GuardedWhileFix_inv_var"   :: "'a bexp => pttrn \<Rightarrow> ('z \<Rightarrow> 'a assn)  \<Rightarrow>
                            ('z \<Rightarrow> ('a \<times> 'a) set) \<Rightarrow> bdy
                          \<Rightarrow> ('a,'p,'f) com"
        (\<open>(0WHILE\<^sub>g (_)/ FIX _./ INV (_)/ VAR (_) /_)\<close>  [25, 0, 0, 0, 81] 71)
  "_GuardedWhileFix_inv_var_hook"   :: "'a bexp \<Rightarrow> ('z \<Rightarrow> 'a assn)  \<Rightarrow>
                            ('z \<Rightarrow> ('a \<times> 'a) set) \<Rightarrow> bdy
                          \<Rightarrow> ('a,'p,'f) com"
  "_GuardedWhileFix_inv"   :: "'a bexp => pttrn \<Rightarrow> ('z \<Rightarrow> 'a assn)  \<Rightarrow> bdy
                          \<Rightarrow> ('a,'p,'f) com"
        (\<open>(0WHILE\<^sub>g (_)/ FIX _./ INV (_)/_)\<close>  [25, 0, 0, 81] 71)

  "_GuardedWhile_inv_var"::
       "'a bexp => 'a assn  \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bdy \<Rightarrow> ('a,'p,'f) com"
        (\<open>(0WHILE\<^sub>g (_)/ INV (_)/ VAR (_) /_)\<close>  [25, 0, 0, 81] 71)
  "_While_inv"   :: "'a bexp => 'a assn => bdy => ('a,'p,'f) com"
        (\<open>(0WHILE (_)/ INV (_) /_)\<close>  [25, 0, 81] 71)
  "_GuardedWhile_inv"   :: "'a bexp => 'a assn => ('a,'p,'f) com => ('a,'p,'f) com"
        (\<open>(0WHILE\<^sub>g (_)/ INV (_) /_)\<close>  [25, 0, 81] 71)
  "_While"       :: "'a bexp => bdy => ('a,'p,'f) com"
        (\<open>(0WHILE (_) /_)\<close>  [25, 81] 71)
  "_GuardedWhile"       :: "'a bexp => bdy => ('a,'p,'f) com"
        (\<open>(0WHILE\<^sub>g (_) /_)\<close>  [25, 81] 71)
  "_While_guard"       :: "grds => 'a bexp => bdy => ('a,'p,'f) com"
        (\<open>(0WHILE (_/\<longmapsto> (1_)) /_)\<close>  [1000,25,81] 71)
  "_While_guard_inv":: "grds \<Rightarrow>'a bexp\<Rightarrow>'a assn\<Rightarrow>bdy \<Rightarrow> ('a,'p,'f) com"
        (\<open>(0WHILE (_/\<longmapsto> (1_)) INV (_) /_)\<close>  [1000,25,0,81] 71)
  "_While_guard_inv_var":: "grds \<Rightarrow>'a bexp\<Rightarrow>'a assn\<Rightarrow>('a\<times>'a) set
                             \<Rightarrow>bdy \<Rightarrow> ('a,'p,'f) com"
        (\<open>(0WHILE (_/\<longmapsto> (1_)) INV (_)/ VAR (_) /_)\<close>  [1000,25,0,0,81] 71)
  "_WhileFix_guard_inv_var":: "grds \<Rightarrow>'a bexp\<Rightarrow>pttrn\<Rightarrow>('z\<Rightarrow>'a assn)\<Rightarrow>('z\<Rightarrow>('a\<times>'a) set)
                             \<Rightarrow>bdy \<Rightarrow> ('a,'p,'f) com"
        (\<open>(0WHILE (_/\<longmapsto> (1_)) FIX _./ INV (_)/ VAR (_) /_)\<close>  [1000,25,0,0,0,81] 71)
  "_WhileFix_guard_inv":: "grds \<Rightarrow>'a bexp\<Rightarrow>pttrn\<Rightarrow>('z\<Rightarrow>'a assn)
                             \<Rightarrow>bdy \<Rightarrow> ('a,'p,'f) com"
        (\<open>(0WHILE (_/\<longmapsto> (1_)) FIX _./ INV (_)/_)\<close>  [1000,25,0,0,81] 71)

  "_Try_Catch":: "('a,'p,'f) com \<Rightarrow>('a,'p,'f) com \<Rightarrow> ('a,'p,'f) com"
        (\<open>(0TRY (_)/ (2CATCH _)/ END)\<close>  [0,0] 71)

  "_DoPre" :: "('a,'p,'f) com \<Rightarrow> ('a,'p,'f) com"
  "_Do" :: "('a,'p,'f) com \<Rightarrow> bdy" (\<open>(2DO/ (_)) /OD\<close> [0] 1000)
  "_Lab":: "'a bexp \<Rightarrow> ('a,'p,'f) com \<Rightarrow> bdy"
            (\<open>_\<bullet>/_\<close> [1000,71] 81)
  "":: "bdy \<Rightarrow> ('a,'p,'f) com" (\<open>_\<close>)
  "_Spec":: "pttrn \<Rightarrow> 's set \<Rightarrow>  ('s,'p,'f) com \<Rightarrow> 's set \<Rightarrow> 's set \<Rightarrow> ('s,'p,'f) com"
            (\<open>(ANNO _. _/ (_)/ _,/_)\<close> [0,1000,20,1000,1000] 60)
  "_SpecNoAbrupt":: "pttrn \<Rightarrow> 's set \<Rightarrow>  ('s,'p,'f) com \<Rightarrow> 's set \<Rightarrow> ('s,'p,'f) com"
            (\<open>(ANNO _. _/ (_)/ _)\<close> [0,1000,20,1000] 60)
  "_LemAnno":: "'n \<Rightarrow> ('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com"
              (\<open>(0 LEMMA (_)/ _ END)\<close> [1000,0] 71)
  "_locnoinit"    :: "ident \<Rightarrow> locinit"               (\<open>\<acute>_\<close>)
  "_locinit"      :: "[ident,'a] \<Rightarrow> locinit"          (\<open>(2\<acute>_ :==/ _)\<close>)
  ""             :: "locinit \<Rightarrow> locinits"             (\<open>_\<close>)
  "_locinits"    :: "[locinit, locinits] \<Rightarrow> locinits" (\<open>_,/ _\<close>)
  "_Loc":: "[locinits,('s,'p,'f) com] \<Rightarrow> ('s,'p,'f) com"
                                         (\<open>(2 LOC _;;/ (_) COL)\<close> [0,0] 71)
  "_Switch":: "('s \<Rightarrow> 'v) \<Rightarrow> switchcases \<Rightarrow> ('s,'p,'f) com"
              (\<open>(0 SWITCH (_)/ _ END)\<close> [22,0] 71)
  "_switchcase":: "'v set \<Rightarrow> ('s,'p,'f) com \<Rightarrow> switchcase" (\<open>_\<Rightarrow>/ _\<close> )
  "_switchcasesSingle"  :: "switchcase \<Rightarrow> switchcases" (\<open>_\<close>)
  "_switchcasesCons":: "switchcase \<Rightarrow> switchcases \<Rightarrow> switchcases"
                       (\<open>_/ | _\<close>)
  "_Basic":: "basicblock \<Rightarrow> ('s,'p,'f) com" (\<open>(0BASIC/ (_)/ END)\<close> [22] 71)
  "_BasicBlock":: "basics \<Rightarrow> basicblock" (\<open>_\<close>)
  "_BAssign"   :: "'b => 'b => basic"    (\<open>(_ :==/ _)\<close> [30, 30] 23)
  ""           :: "basic \<Rightarrow> basics"             (\<open>_\<close>)
  "_basics"    :: "[basic, basics] \<Rightarrow> basics" (\<open>_,/ _\<close>)

syntax (ASCII)
  "_Assert"      :: "'a => 'a set"           (\<open>({|_|})\<close> [0] 1000)
  "_AssertState" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a set"    (\<open>({|_. _|})\<close> [1000,0] 1000)
  "_While_guard"       :: "grds => 'a bexp => bdy \<Rightarrow> ('a,'p,'f) com"
        (\<open>(0WHILE (_|-> /_) /_)\<close>  [0,0,1000] 71)
  "_While_guard_inv":: "grds\<Rightarrow>'a bexp\<Rightarrow>'a assn\<Rightarrow>bdy \<Rightarrow> ('a,'p,'f) com"
        (\<open>(0WHILE (_|-> /_) INV (_) /_)\<close>  [0,0,0,1000] 71)
  "_guards" :: "grds \<Rightarrow> ('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com" (\<open>(_|->_ )\<close> [60, 21] 23)

syntax (output)
  "_hidden_grds"      :: "grds" (\<open>\<dots>\<close>)

translations
  "_Do c" => "c"
  "b\<bullet> c" => "CONST condCatch c b SKIP"
  "b\<bullet> (_DoPre c)" <= "CONST condCatch c b SKIP"
  "l\<bullet> (CONST whileAnnoG gs b I V c)" <= "l\<bullet> (_DoPre (CONST whileAnnoG gs b I V c))"
  "l\<bullet> (CONST whileAnno b I V c)" <= "l\<bullet> (_DoPre (CONST whileAnno b I V c))"
  "CONST condCatch c b SKIP" <= "(_DoPre (CONST condCatch c b SKIP))"
  "_Do c" <= "_DoPre c"
  "c;; d" == "CONST Seq c d"
  "_guarantee g" => "(CONST True, g)"
  "_guaranteeStrip g" == "CONST guaranteeStripPair (CONST True) g"
  "_grd g" => "(CONST False, g)"
  "_grds g gs" => "g#gs"
  "_last_grd g" => "[g]"
  "_guards gs c" == "CONST guards gs c"

  "{|s. P|}"                   == "{|_antiquoteCur((=) s) \<and> P |}"
  "{|b|}"                   => "CONST Collect (_quote b)"
  "IF b THEN c1 ELSE c2 FI" => "CONST Cond {|b|} c1 c2"
  "IF b THEN c1 FI"         ==  "IF b THEN c1 ELSE SKIP FI"
  "IF\<^sub>g b THEN c1 FI"        ==  "IF\<^sub>g b THEN c1 ELSE SKIP FI"

  "_While_inv_var b I V c"          => "CONST whileAnno {|b|} I V c"
  "_While_inv_var b I V (_DoPre c)" <= "CONST whileAnno {|b|} I V c"
  "_While_inv b I c"                 == "_While_inv_var b I (CONST undefined) c"
  "_While b c"                       == "_While_inv b {|CONST undefined|} c"

  "_While_guard_inv_var gs b I V c"          => "CONST whileAnnoG gs {|b|} I V c"
(*  "_While_guard_inv_var gs b I V (_DoPre c)" <= "CONST whileAnnoG gs {|b|} I V c"*)
  "_While_guard_inv gs b I c"       == "_While_guard_inv_var gs b I (CONST undefined) c"
  "_While_guard gs b c"             == "_While_guard_inv gs b {|CONST undefined|} c"

  "_GuardedWhile_inv b I c"  == "_GuardedWhile_inv_var b I (CONST undefined) c"
  "_GuardedWhile b c"        == "_GuardedWhile_inv b {|CONST undefined|} c"
(*  "\<^bsup>s\<^esup>A"                      => "A s"*)
  "TRY c1 CATCH c2 END"     == "CONST Catch c1 c2"
  "ANNO s. P c Q,A" => "CONST specAnno (\<lambda>s. P) (\<lambda>s. c) (\<lambda>s. Q) (\<lambda>s. A)"
  "ANNO s. P c Q" == "ANNO s. P c Q,{}"

  "_WhileFix_inv_var b z I V c" => "CONST whileAnnoFix {|b|} (\<lambda>z. I) (\<lambda>z. V) (\<lambda>z. c)"
  "_WhileFix_inv_var b z I V (_DoPre c)" <= "_WhileFix_inv_var {|b|} z I V c"
  "_WhileFix_inv b z I c" == "_WhileFix_inv_var b z I (CONST undefined) c"

  "_GuardedWhileFix_inv b z I c" == "_GuardedWhileFix_inv_var b z I (CONST undefined) c"

  "_GuardedWhileFix_inv_var b z I V c" =>
                         "_GuardedWhileFix_inv_var_hook {|b|} (\<lambda>z. I) (\<lambda>z. V) (\<lambda>z. c)"

  "_WhileFix_guard_inv_var gs b z I V c" =>
                                      "CONST whileAnnoGFix gs {|b|} (\<lambda>z. I) (\<lambda>z. V) (\<lambda>z. c)"
  "_WhileFix_guard_inv_var gs b z I V (_DoPre c)" <=
                                      "_WhileFix_guard_inv_var gs {|b|} z I V c"
  "_WhileFix_guard_inv gs b z I c" == "_WhileFix_guard_inv_var gs b z I (CONST undefined) c"
  "LEMMA x c END" == "CONST lem x c"
translations
 "(_switchcase V c)" => "(V,c)"
 "(_switchcasesSingle b)" => "[b]"
 "(_switchcasesCons b bs)" => "CONST Cons b bs"
 "(_Switch v vs)" => "CONST switch (_quote v) vs"

parse_ast_translation \<open>
  let
    fun tr c asts = Ast.mk_appl (Ast.Constant c) (map Ast.strip_positions asts)
  in
   [(@{syntax_const "_antiquoteCur0"}, K (tr @{syntax_const "_antiquoteCur"})),
    (@{syntax_const "_antiquoteOld0"}, K (tr @{syntax_const "_antiquoteOld"}))]
  end
\<close>

print_ast_translation \<open>
  let
    fun tr c asts = Ast.mk_appl (Ast.Constant c) asts
  in
   [(@{syntax_const "_antiquoteCur"}, K (tr @{syntax_const "_antiquoteCur0"})),
    (@{syntax_const "_antiquoteOld"}, K (tr @{syntax_const "_antiquoteOld0"}))]
  end
\<close>

print_ast_translation \<open>
  let
    fun dest_abs (Ast.Appl [Ast.Constant @{syntax_const "_abs"}, x, t]) = (x, t)
      | dest_abs _ = raise Match;
    fun spec_tr' [P, c, Q, A] =
      let
        val (x',P') = dest_abs P;
        val (_ ,c') = dest_abs c;
        val (_ ,Q') = dest_abs Q;
        val (_ ,A') = dest_abs A;
      in
        if (A' = Ast.Constant @{const_syntax bot})
        then Ast.mk_appl (Ast.Constant @{syntax_const "_SpecNoAbrupt"}) [x', P', c', Q']
        else Ast.mk_appl (Ast.Constant @{syntax_const "_Spec"}) [x', P', c', Q', A']
      end;
    fun whileAnnoFix_tr' [b, I, V, c] =
      let
        val (x',I') = dest_abs I;
        val (_ ,V') = dest_abs V;
        val (_ ,c') = dest_abs c;
      in
        Ast.mk_appl (Ast.Constant @{syntax_const "_WhileFix_inv_var"}) [b, x', I', V', c']
      end;
  in
   [(@{const_syntax specAnno}, K spec_tr'),
    (@{const_syntax whileAnnoFix}, K whileAnnoFix_tr')]
  end
\<close>



syntax
  "_faccess"  :: "'ref \<Rightarrow> ('ref \<Rightarrow> 'v) \<Rightarrow> 'v"
   (\<open>_\<rightarrow>_\<close> [65,1000] 100)

syntax (ASCII)
  "_faccess"  :: "'ref \<Rightarrow> ('ref \<Rightarrow> 'v) \<Rightarrow> 'v"
   (\<open>_->_\<close> [65,1000] 100)

translations

 "p\<rightarrow>f"        =>  "f p"
 "g\<rightarrow>(_antiquoteCur f)" <= "_antiquoteCur f g"


nonterminal par and pars and actuals

syntax
  "_par" :: "'a \<Rightarrow> par"                                (\<open>_\<close>)
  ""    :: "par \<Rightarrow> pars"                               (\<open>_\<close>)
  "_pars" :: "[par,pars] \<Rightarrow> pars"                      (\<open>_,/_\<close>)
  "_actuals" :: "pars \<Rightarrow> actuals"                      (\<open>'(_')\<close>)
  "_actuals_empty" :: "actuals"                        (\<open>'(')\<close>)

syntax "_Call" :: "'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) com)" (\<open>CALL __\<close> [1000,1000] 21)
       "_GuardedCall" :: "'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) com)" (\<open>CALL\<^sub>g __\<close> [1000,1000] 21)
       "_CallAss":: "'a \<Rightarrow> 'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) com)"
             (\<open>_ :== CALL __\<close> [30,1000,1000] 21)
       "_Call_exn" :: "'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) com)" (\<open>CALL\<^sub>e __\<close> [1000,1000] 21)
       "_CallAss_exn":: "'a \<Rightarrow> 'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) com)"
             (\<open>_ :== CALL\<^sub>e __\<close> [30,1000,1000] 21)
       "_Proc" :: "'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) com)" (\<open>PROC __\<close> 21)
       "_ProcAss":: "'a \<Rightarrow> 'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) com)"
             (\<open>_ :== PROC __\<close> [30,1000,1000] 21)
       "_GuardedCallAss":: "'a \<Rightarrow> 'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) com)"
             (\<open>_ :== CALL\<^sub>g __\<close> [30,1000,1000] 21)
       "_DynCall" :: "'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) com)" (\<open>DYNCALL __\<close> [1000,1000] 21)
       "_GuardedDynCall" :: "'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) com)" (\<open>DYNCALL\<^sub>g __\<close> [1000,1000] 21)
       "_DynCallAss":: "'a \<Rightarrow> 'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) com)"
             (\<open>_ :== DYNCALL __\<close> [30,1000,1000] 21)
       "_DynCall_exn" :: "'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) com)" (\<open>DYNCALL\<^sub>e __\<close> [1000,1000] 21)
       "_DynCallAss_exn":: "'a \<Rightarrow> 'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) com)"
             (\<open>_ :== DYNCALL\<^sub>e __\<close> [30,1000,1000] 21)
       "_GuardedDynCallAss":: "'a \<Rightarrow> 'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) com)"
             (\<open>_ :== DYNCALL\<^sub>g __\<close> [30,1000,1000] 21)

       "_Bind":: "['s \<Rightarrow> 'v, idt, 'v \<Rightarrow> ('s,'p,'f) com] \<Rightarrow> ('s,'p,'f) com"
                      (\<open>_ \<ggreater> _./ _\<close> [22,1000,21] 21)
       "_bseq"::"('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com"
           (\<open>_\<ggreater>/ _\<close> [22, 21] 21)
       "_FCall" :: "['p,actuals,idt,(('a,string,'f) com)]\<Rightarrow> (('a,string,'f) com)"
                      (\<open>CALL __ \<ggreater> _./ _\<close> [1000,1000,1000,21] 21)



translations
"_Bind e i c" == "CONST bind (_quote e) (\<lambda>i. c)"
"_FCall p acts i c" == "_FCall p acts (\<lambda>i. c)"
"_bseq c d" == "CONST bseq c d"



nonterminal modifyargs

syntax
  "_may_modify" :: "['a,'a,modifyargs] \<Rightarrow> bool"
        (\<open>_ may'_only'_modify'_globals _ in [_]\<close> [100,100,0] 100)
  "_may_not_modify" :: "['a,'a] \<Rightarrow> bool"
        (\<open>_ may'_not'_modify'_globals _\<close> [100,100] 100)
  "_may_modify_empty" :: "['a,'a] \<Rightarrow> bool"
        (\<open>_ may'_only'_modify'_globals _ in []\<close> [100,100] 100)
  "_modifyargs" :: "[id,modifyargs] \<Rightarrow> modifyargs" (\<open>_,/ _\<close>)
  ""            :: "id => modifyargs"              (\<open>_\<close>)

translations
"s may_only_modify_globals Z in []" => "s may_not_modify_globals Z"


definition Let':: "['a, 'a => 'b] => 'b"
  where "Let' = Let"

ML_file \<open>hoare_syntax.ML\<close>


parse_translation \<open>
  let
    val argsC = @{syntax_const "_modifyargs"};
    val globalsN = "globals";
    val ex = @{const_syntax mex};
    val eq = @{const_syntax meq};
    val varn = Hoare.varname;

    fun extract_args (Const (argsC,_)$Free (n,_)$t) = varn n::extract_args t
      | extract_args (Free (n,_)) = [varn n]
      | extract_args t            = raise TERM ("extract_args", [t])

    fun idx [] y = error "idx: element not in list"
     |  idx (x::xs) y = if x=y then 0 else (idx xs y)+1

    fun gen_update ctxt names (name,t) =
        Hoare_Syntax.update_comp ctxt NONE [] false true name (Bound (idx names name)) t

    fun gen_updates ctxt names t = Library.foldr (gen_update ctxt names) (names,t)

    fun gen_ex (name,t) = Syntax.const ex $ Abs (name,dummyT,t)

    fun gen_exs names t = Library.foldr gen_ex (names,t)


    fun tr ctxt s Z names =
      let val upds = gen_updates ctxt (rev names) (Syntax.free globalsN$Z);
          val eq   = Syntax.const eq $ (Syntax.free globalsN$s) $ upds;
      in gen_exs names eq end;

    fun may_modify_tr ctxt [s,Z,names] = tr ctxt s Z
                                           (sort_strings (extract_args names))
    fun may_not_modify_tr ctxt [s,Z] = tr ctxt s Z []
  in
   [(@{syntax_const "_may_modify"}, may_modify_tr),
    (@{syntax_const "_may_not_modify"}, may_not_modify_tr)]
  end
\<close>


print_translation \<open>
  let
    val argsC = @{syntax_const "_modifyargs"};
    val chop = Hoare.chopsfx Hoare.deco;

    fun get_state ( _ $ _ $ t) = get_state t  (* for record-updates*)
      | get_state ( _ $ _ $ _ $ _ $ _ $ t) = get_state t (* for statespace-updates *)
      | get_state (globals$(s as Const (@{syntax_const "_free"},_) $ Free _)) = s
      | get_state (globals$(s as Const (@{syntax_const "_bound"},_) $ Free _)) = s
      | get_state (globals$(s as Const (@{syntax_const "_var"},_) $ Var _)) = s
      | get_state (globals$(s as Const _)) = s
      | get_state (globals$(s as Free _)) = s
      | get_state (globals$(s as Bound _)) = s
      | get_state t              = raise Match;

    fun mk_args [n] = Syntax.free (chop n)
      | mk_args (n::ns) = Syntax.const argsC $ Syntax.free (chop n) $ mk_args ns
      | mk_args _      = raise Match;

    fun tr' names (Abs (n,_,t)) = tr' (n::names) t
      | tr' names (Const (@{const_syntax mex},_) $ t) = tr' names t
      | tr' names (Const (@{const_syntax meq},_) $ (globals$s) $ upd) =
            let val Z = get_state upd;

            in (case names of
                  [] => Syntax.const @{syntax_const "_may_not_modify"} $ s $ Z
                | xs => Syntax.const @{syntax_const "_may_modify"} $ s $ Z $ mk_args (rev names))
            end;

    fun may_modify_tr' [t] = tr' [] t
    fun may_not_modify_tr' [_$s,_$Z] = Syntax.const @{syntax_const "_may_not_modify"} $ s $ Z
  in
    [(@{const_syntax mex}, K may_modify_tr'),
     (@{const_syntax meq}, K may_not_modify_tr')]
  end
\<close>


(* decorate state components with suffix *)
(*
parse_ast_translation {*
 [(@{syntax_const "_Free"}, K Hoare_Syntax.free_arg_ast_tr),
  (@{syntax_const "_In"}, K Hoare_Syntax.in_arg_ast_tr),
  (@{syntax_const "_Where"}, K Hoare_Syntax.where_arg_ast_tr @{syntax_const "_Where"}),
  (@{syntax_const "_WhereElse"}, K Hoare_Syntax.where_arg_ast_tr @{syntax_const "_WhereElse"})
]
*}
*)
(*
parse_ast_translation {*
 [(@{syntax_const "_antiquoteOld"},
    Hoare_Syntax.antiquoteOld_varname_tr @{syntax_const "_antiquoteOld"})]
*}
*)


parse_translation \<open>
 [(@{syntax_const "_antiquoteCur"},
    K (Hoare_Syntax.antiquote_varname_tr @{syntax_const "_antiquoteCur"}))]
\<close>


parse_translation \<open>
 [(@{syntax_const "_antiquoteOld"}, Hoare_Syntax.antiquoteOld_tr),
  (@{syntax_const "_Call"}, Hoare_Syntax.call_tr false false []),
  (@{syntax_const "_Call_exn"}, Hoare_Syntax.call_tr false true []),
  (@{syntax_const "_FCall"}, Hoare_Syntax.fcall_tr),
  (@{syntax_const "_CallAss"}, Hoare_Syntax.call_ass_tr false false []),
  (@{syntax_const "_CallAss_exn"}, Hoare_Syntax.call_ass_tr false true []),
  (@{syntax_const "_GuardedCall"}, Hoare_Syntax.call_tr false true []),
  (@{syntax_const "_GuardedCallAss"}, Hoare_Syntax.call_ass_tr false true []),
  (@{syntax_const "_Proc"}, Hoare_Syntax.proc_tr),
  (@{syntax_const "_ProcAss"}, Hoare_Syntax.proc_ass_tr),
  (@{syntax_const "_DynCall"}, Hoare_Syntax.call_tr true false []),
  (@{syntax_const "_DynCall_exn"}, Hoare_Syntax.call_tr true true []),
  (@{syntax_const "_DynCallAss"}, Hoare_Syntax.call_ass_tr true false []),
  (@{syntax_const "_DynCallAss_exn"}, Hoare_Syntax.call_ass_tr true true []),
  (@{syntax_const "_GuardedDynCall"}, Hoare_Syntax.call_tr true true []),
  (@{syntax_const "_GuardedDynCallAss"}, Hoare_Syntax.call_ass_tr true true []),
  (@{syntax_const "_BasicBlock"}, Hoare_Syntax.basic_assigns_tr)]
\<close>

(*
  (@{syntax_const "_Call"}, Hoare_Syntax.call_ast_tr),
  (@{syntax_const "_CallAss"}, Hoare_Syntax.call_ass_ast_tr),
  (@{syntax_const "_GuardedCall"}, Hoare_Syntax.guarded_call_ast_tr),
  (@{syntax_const "_GuardedCallAss"}, Hoare_Syntax.guarded_call_ass_ast_tr)
*)

parse_translation \<open>
  let
    fun quote_tr ctxt [t] = Hoare_Syntax.quote_tr ctxt @{syntax_const "_antiquoteCur"} t
      | quote_tr ctxt ts = raise TERM ("quote_tr", ts);
  in [(@{syntax_const "_quote"}, quote_tr)] end
\<close>



parse_translation \<open>
 [(@{syntax_const "_Assign"}, Hoare_Syntax.assign_tr),
  (@{syntax_const "_raise"}, Hoare_Syntax.raise_tr),
  (@{syntax_const "_New"}, Hoare_Syntax.new_tr),
  (@{syntax_const "_NNew"}, Hoare_Syntax.nnew_tr),
  (@{syntax_const "_GuardedAssign"}, Hoare_Syntax.guarded_Assign_tr),
  (@{syntax_const "_GuardedNew"}, Hoare_Syntax.guarded_New_tr),
  (@{syntax_const "_GuardedNNew"}, Hoare_Syntax.guarded_NNew_tr),
  (@{syntax_const "_GuardedWhile_inv_var"}, Hoare_Syntax.guarded_While_tr),
  (@{syntax_const "_GuardedWhileFix_inv_var_hook"}, Hoare_Syntax.guarded_WhileFix_tr),
  (@{syntax_const "_GuardedCond"}, Hoare_Syntax.guarded_Cond_tr),
  (@{syntax_const "_Basic"}, Hoare_Syntax.basic_tr)]
\<close>

parse_translation \<open>
 [(@{syntax_const "_Init"}, Hoare_Syntax.init_tr),
  (@{syntax_const "_Loc"}, Hoare_Syntax.loc_tr)]
\<close>


print_translation \<open>
 [(@{const_syntax Basic}, Hoare_Syntax.assign_tr'),
  (@{const_syntax raise}, Hoare_Syntax.raise_tr'),
  (@{const_syntax Basic}, Hoare_Syntax.new_tr'),
  (@{const_syntax Basic}, Hoare_Syntax.init_tr'),
  (@{const_syntax Spec}, Hoare_Syntax.nnew_tr'),
  (@{const_syntax block}, Hoare_Syntax.loc_tr'),
  (@{const_syntax Collect}, Hoare_Syntax.assert_tr'),
  (@{const_syntax Cond}, Hoare_Syntax.bexp_tr' "_Cond"),
  (@{const_syntax switch}, Hoare_Syntax.switch_tr'),
  (@{const_syntax Basic}, Hoare_Syntax.basic_tr'),
  (@{const_syntax guards}, Hoare_Syntax.guards_tr'),
  (@{const_syntax whileAnnoG}, Hoare_Syntax.whileAnnoG_tr'),
  (@{const_syntax whileAnnoGFix}, Hoare_Syntax.whileAnnoGFix_tr'),
  (@{const_syntax bind}, Hoare_Syntax.bind_tr')]
\<close>


print_translation \<open>
  let
    fun spec_tr' ctxt ((coll as Const _)$
                   ((splt as Const _) $ (t as (Abs (s,T,p))))::ts) =
          let
            fun selector (Const (c, T)) = Hoare.is_state_var c
              | selector (Const (@{syntax_const "_free"}, _) $ (Free (c, T))) =
                  Hoare.is_state_var c
              | selector _ = false;
          in
            if Hoare_Syntax.antiquote_applied_only_to selector p then
              Syntax.const @{const_syntax Spec} $ coll $
                (splt $ Hoare_Syntax.quote_mult_tr' ctxt selector
                    Hoare_Syntax.antiquoteCur Hoare_Syntax.antiquoteOld  (Abs (s,T,t)))
             else raise Match
          end
      | spec_tr' _ ts = raise Match
  in [(@{const_syntax Spec}, spec_tr')] end
\<close>

syntax
"_Measure":: "('a \<Rightarrow> nat) \<Rightarrow> ('a \<times> 'a) set"
      (\<open>MEASURE _\<close> [22] 1)
"_Mlex":: "('a \<Rightarrow> nat) \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set"
      (infixr \<open><*MLEX*>\<close> 30)

syntax_consts
"_Measure" == measure and
"_Mlex" == mlex_prod

translations
 "MEASURE f"       => "(CONST measure) (_quote f)"
 "f <*MLEX*> r"       => "(_quote f) <*mlex*> r"



print_translation \<open>
  let
    fun selector (Const (c,T)) = Hoare.is_state_var c
      | selector _ = false;

    fun measure_tr' ctxt ((t as (Abs (_,_,p)))::ts) =
          if Hoare_Syntax.antiquote_applied_only_to selector p
          then Hoare_Syntax.app_quote_tr' ctxt (Syntax.const @{syntax_const "_Measure"}) (t::ts)
          else raise Match
      | measure_tr' _ _ = raise Match

    fun mlex_tr' ctxt ((t as (Abs (_,_,p)))::r::ts) =
          if Hoare_Syntax.antiquote_applied_only_to selector p
          then Hoare_Syntax.app_quote_tr' ctxt (Syntax.const @{syntax_const "_Mlex"}) (t::r::ts)
          else raise Match
      | mlex_tr' _ _ = raise Match

  in
   [(@{const_syntax measure}, measure_tr'),
    (@{const_syntax mlex_prod}, mlex_tr')]
  end
\<close>


print_translation \<open>
 [(@{const_syntax call}, Hoare_Syntax.call_tr'),
  (@{const_syntax dynCall}, Hoare_Syntax.dyn_call_tr'),
  (@{const_syntax call_exn}, Hoare_Syntax.call_exn_tr'),
  (@{const_syntax dynCall_exn}, Hoare_Syntax.dyn_call_exn_tr'),
  (@{const_syntax fcall}, Hoare_Syntax.fcall_tr'),
  (@{const_syntax Call}, Hoare_Syntax.proc_tr')]
\<close>

end
