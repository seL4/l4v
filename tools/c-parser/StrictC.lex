(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

structure Tokens = Tokens

type pos = SourcePos.t

type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult= (svalue,pos) token

fun error (e, l : pos, r : pos) = Feedback.errorStr' (l, r, e)

fun mkNumber base (left, right, string) = let
  fun reader i = SOME (String.sub(string, i), i + 1) handle Subscript => NONE
  val (value, residue_i) = valOf (IntInf.scan base reader 0)
  val suffix = String.extract(string, residue_i, NONE)
in
  Tokens.NUMERIC_CONSTANT ({value = value, base = base, suffix = suffix},
                           left, right)
end


fun tok(t,s,l,r) = let
in
  t (SourceFile.getPos(s,l),SourceFile.getPos(s,r))
end

datatype retstate = SINITIAL | STDEF | STS | STSI | STSS
type lexstate = {
  source : SourceFile.t,
  in_comment : bool ref,
  commentStart : SourcePos.t ref,
  stringlitContent : string list ref,
  stringlitStart : SourcePos.t ref,
  charlitContent : IntInf.int list ref,
  charlitStart : SourcePos.t ref,
  tokpdepth : IntInf.int ref,
  tokbdepth : IntInf.int ref,
  tokidseen : bool ref,
  in_attr : bool ref,
  return : retstate ref,
  type_info : string list list ref
}
type lexarg = lexstate
type arg = lexarg

val getPos = SourceFile.getPos

fun attr_begin ({return,in_attr,...}:lexstate) s = (return := s; in_attr := true)

val eof = (fn {source,in_comment,in_attr,commentStart,...} : lexstate =>
              let val pos = SourceFile.lineStart source
              in
                if !in_comment then
                  Feedback.errorStr (Region.make {left = !commentStart,
                                                  right = pos},
                                     "unclosed comment")
                else if !in_attr then
                  Feedback.errorStr (Region.make {left = !commentStart,
                                                  right = pos},
                                     "unclosed __attribute__")
                else ();
                Tokens.EOF (pos, pos)
              end)

fun type_info_newscope ({type_info,...}:lexstate) = type_info := [] :: !type_info
fun type_info_leavescope ({type_info,...}:lexstate) = type_info := tl (!type_info)
fun is_type_name ({type_info,...}:lexstate) s = let
  fun lookup [] = false
    | lookup (h::t) = (case List.find (fn s' => s = s') h of
                         NONE => lookup t
                       | SOME _ => true)
in
  lookup (!type_info)
end

fun update_type_info ({type_info,...}:lexstate) s =
    type_info := (s :: hd (!type_info)) :: (tl (!type_info))

fun mk_ident f (s,l,r) =
  f (NameGeneration.mkIdentUScoreSafe s,l,r)
val mk_tokident = mk_ident Tokens.ID

(* b is true iff called from non-tdef mode *)
fun resolve_id (b, arg as {source=src,tokidseen,...}:lexstate, l, s) =
    if is_type_name arg (NameGeneration.mkIdentUScoreSafe s) then
      mk_ident Tokens.TYPEID (s, getPos(src,l), getPos(src, l + size s - 1))
    else (if not b andalso not (!tokidseen) then
            (update_type_info arg (NameGeneration.mkIdentUScoreSafe s);
             tokidseen := true)
          else ();
          mk_ident Tokens.ID (s, getPos(src,l), getPos(src, l + size s - 1)))

fun new_state fname : lexstate = {
  tokpdepth = ref 0,
  tokbdepth = ref 0,
  in_attr = ref false,
  return = ref SINITIAL,
  in_comment = ref false,
  type_info = ref [[]],
  tokidseen = ref false,
  source = SourceFile.new fname,
  commentStart = ref SourcePos.bogus,
  stringlitContent = ref [],
  stringlitStart = ref SourcePos.bogus,
  charlitContent = ref [],
  charlitStart = ref SourcePos.bogus
}

fun charlitbegin ({return,charlitContent,charlitStart,...}:lexstate) pos rs =
    (return := rs;
     charlitContent := [];
     charlitStart := pos);

%%
%header (functor StrictCLexFun(structure Tokens: StrictC_TOKENS));
%arg ({source, in_comment, commentStart, stringlitContent, stringlitStart, charlitContent, charlitStart, tokpdepth, tokbdepth, tokidseen, return,...}:UserDeclarations.lexstate);
%s SLSLCOMMENT TRADCOMMENT TDEF TS TSI TSS ATTRIBUTE SPEC_COMM0 SPECIAL_COMMENT
   SPEC_STRINGLIT SPEC_COMMJUNK CHARLIT;
alpha=[A-Za-z];
digit=[0-9];
newline="\n" | "\013\n";
unsignedsuffix = u | U;
longsuffix = l | L;
longlongsuffix = ll | LL;
intsuffix= {unsignedsuffix}{longsuffix}?
         | {unsignedsuffix}{longlongsuffix}
         | {longsuffix}{unsignedsuffix}?
         | {longlongsuffix}{unsignedsuffix}?;
integer=([1-9]{digit}*|0){intsuffix}?;
octint=0{digit}+{intsuffix}?;
hexint=("0x"|"0X")({digit}|[a-fA-F])+{intsuffix}?;
identifier=({alpha}|"_")({alpha}|{digit}|"_")*;
ws = [\ \t];
commentbody = ([^*]*(\*[^/])?)*;
attr_start = "__attribute__"{ws}*"((";
%%

<INITIAL,TSI>";"  => (tok(Tokens.YSEMI,source,yypos,yypos));
<TDEF,TSS,TS>";"  => (YYBEGIN INITIAL; tok(Tokens.YSEMI,source,yypos,yypos));


<INITIAL,TSI>","  => (tok(Tokens.YCOMMA,source,yypos,yypos+size yytext-1));
<TDEF,TSS,TS>","  => (if !tokpdepth = 0 then tokidseen := false else ();
                      tok(Tokens.YCOMMA,source,yypos,yypos+size yytext-1));
<INITIAL,TSI>"("  => (tok(Tokens.LPAREN,source,yypos,yypos+size yytext-1));
<TDEF,TSS>"("     => (tokpdepth := !tokpdepth + 1;
                      tok(Tokens.LPAREN,source,yypos,yypos+size yytext-1));
<INITIAL,TSI>")"  => (tok(Tokens.RPAREN,source,yypos,yypos+size yytext-1));
<TDEF,TSS>")"     => (tokpdepth := !tokpdepth - 1;
                      tok(Tokens.RPAREN,source,yypos,yypos+size yytext-1));

<INITIAL>"{"      => (type_info_newscope yyarg;
                      tok(Tokens.LCURLY,source,yypos,yypos+size yytext-1));
<TS,TSS>"{"       => (YYBEGIN TSI; tokbdepth := 1;
                      tok(Tokens.LCURLY,source,yypos,yypos+size yytext-1));
<TSI>"{"          => (tokbdepth := !tokbdepth + 1;
                      tok(Tokens.LCURLY,source,yypos,yypos+size yytext-1));

<INITIAL>"}"      => (type_info_leavescope yyarg;
                      tok(Tokens.RCURLY,source,yypos,yypos+size yytext-1));
<TSI>"}"          => (tokbdepth := !tokbdepth - 1;
                      if !tokbdepth = 0 then YYBEGIN TDEF else ();
                      tok(Tokens.RCURLY,source,yypos,yypos+size yytext-1));
<TSS,TS>"}"       => (tok(Tokens.RCURLY,source,yypos,yypos+size yytext-1));


<INITIAL,TS,TSS,TSI>"struct"
                  => (tok(Tokens.STRUCT,source,yypos,yypos+size yytext-1));
<TDEF>"struct"    => (YYBEGIN TS;
                      tok(Tokens.STRUCT,source,yypos,yypos+size yytext-1));
<TDEF>"union"     => (YYBEGIN TS;
                      tok(Tokens.UNION,source,yypos,yypos+size yytext-1));
<TDEF>"enum"      => (YYBEGIN TS;
                      tok(Tokens.YENUM,source,yypos,yypos+size yytext-1));

<INITIAL>"typedef"=> (YYBEGIN TDEF;
                      tokpdepth := 0;
                      tokbdepth := 0;
                      tokidseen := false;
                      tok(Tokens.TYPEDEF,source,yypos,yypos+size yytext-1));
<TS,TDEF,TSI,TSS>"typedef"
                   => (error("typedef not allowed here",
                             getPos(source, yypos),
                             getPos(source, yypos + 6));
                       continue());
<INITIAL>"register"=> (tok(Tokens.YREGISTER,source,yypos,yypos+size yytext-1));
<INITIAL>"_Thread_local" =>
                     (tok(Tokens.THREAD_LOCAL,source,yypos,yypos+size yytext-1));
<INITIAL>"auto" =>   (tok(Tokens.AUTO,source,yypos,yypos+size yytext-1));

<TDEF>"/*" =>        (YYBEGIN TRADCOMMENT; in_comment := true;
                      return := STDEF;
                      commentStart := getPos(source, yypos);
                      continue());
<INITIAL>"/**"    => (YYBEGIN SPEC_COMM0; continue());
<INITIAL>"/*"     => (YYBEGIN TRADCOMMENT; in_comment := true;
                      return := SINITIAL;
                      commentStart := getPos (source, yypos);
                      continue());
<TS>"/*"          => (YYBEGIN TRADCOMMENT; in_comment := true;
                      return := STS;
                      commentStart := getPos (source, yypos);
                      continue());
<TSI>"/*"         => (YYBEGIN TRADCOMMENT; in_comment := true;
                      return := STSI;
                      commentStart := getPos (source, yypos);
                      continue());
<TSS>"/*"         => (YYBEGIN TRADCOMMENT; in_comment := true;
                      return := STSS;
                      commentStart := getPos (source, yypos);
                      continue());

<INITIAL>"//"     => (YYBEGIN SLSLCOMMENT;
                      return := SINITIAL;
                      continue());
<TDEF>"//" =>        (YYBEGIN SLSLCOMMENT;
                      return := STDEF;
                      continue());
<TS>"//"          => (YYBEGIN SLSLCOMMENT;
                      return := STS;
                      continue());
<TSI>"//" =>         (YYBEGIN SLSLCOMMENT;
                      return := STSI;
                      continue());
<TSS>"//"     =>     (YYBEGIN SLSLCOMMENT;
                      return := STSS;
                      continue());

<INITIAL>"'" => (YYBEGIN CHARLIT;
                 charlitbegin yyarg (getPos(source, yypos)) SINITIAL;
                 continue());
<TDEF>"'" =>    (YYBEGIN CHARLIT;
                 charlitbegin yyarg (getPos(source, yypos)) STDEF;
                 continue());
<TS>"'" =>      (YYBEGIN CHARLIT;
                 charlitbegin yyarg (getPos(source, yypos)) STS;
                 continue());
<TSI>"'" =>     (YYBEGIN CHARLIT;
                 charlitbegin yyarg (getPos(source, yypos)) STSI;
                 continue());
<TSS>"'" =>     (YYBEGIN CHARLIT;
                 charlitbegin yyarg (getPos(source, yypos)) STSS;
                 continue());

<INITIAL,TDEF,TS,TSS,TSI>{newline}       =>
     (SourceFile.newline(source,yypos+1); continue());
<INITIAL,TDEF,TS,TSS,TSI>{ws}+    =>
     (continue());
<INITIAL,TDEF,TS,TSS,TSI>"*"      =>
     (tok(Tokens.YSTAR,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"."      =>
     (tok(Tokens.YDOT,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>":"      =>
     (tok(Tokens.YCOLON,source,yypos,yypos));
<INITIAL,TDEF,TS,TSS,TSI>"["      =>
     (tok(Tokens.LBRACKET,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"]"      =>
     (tok(Tokens.RBRACKET,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"&"      =>
     (tok(Tokens.YAMPERSAND,source,yypos,yypos));
<INITIAL,TDEF,TS,TSS,TSI>"="      =>
     (tok(Tokens.YEQ,source,yypos,yypos));
<INITIAL,TDEF,TS,TSS,TSI>"=="     =>
     (tok(Tokens.EQUALS,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"!="     =>
     (tok(Tokens.NOTEQUALS,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"?"      =>
     (tok(Tokens.QMARK,source,yypos,yypos));
<INITIAL,TDEF,TS,TSS,TSI>"++"     =>
     (tok(Tokens.PLUSPLUS,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"+="     =>
     (tok(Tokens.PLUSEQ,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"-="     =>
     (tok(Tokens.MINUSEQ,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"*="     =>
     (tok(Tokens.MULEQ,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"|="     =>
     (tok(Tokens.BOREQ,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"&="     =>
     (tok(Tokens.BANDEQ,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>">>="     =>
     (tok(Tokens.RSHIFTEQ,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"<<="     =>
     (tok(Tokens.LSHIFTEQ,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"/="     =>
     (tok(Tokens.DIVEQ,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"%="     =>
     (tok(Tokens.MODEQ,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"^="     =>
     (tok(Tokens.BXOREQ,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"+"      =>
     (tok(Tokens.YPLUS,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"&&"     =>
     (tok(Tokens.LOGICALAND,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"||"     =>
     (tok(Tokens.LOGICALOR,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"|"     =>
     (tok(Tokens.BITWISEOR,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"^"     =>
     (tok(Tokens.BITWISEXOR,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"<<"      =>
     (tok(Tokens.LEFTSHIFT,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"<"      =>
     (tok(Tokens.YLESS,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>">>"     =>
     (tok(Tokens.RIGHTSHIFT,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>">"      =>
     (tok(Tokens.YGREATER,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"<="     =>
     (tok(Tokens.YLE,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>">="     =>
     (tok(Tokens.YGE,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"/"      =>
     (tok(Tokens.SLASH,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"%"      =>
     (tok(Tokens.MOD,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"--"     =>
     (tok(Tokens.MINUSMINUS,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"-"      =>
     (tok(Tokens.YMINUS,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"!"      =>
     (tok(Tokens.YNOT,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"~"      =>
     (tok(Tokens.YBITNOT,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"->"     =>
     (tok(Tokens.ARROW,source,yypos,yypos+size yytext-1));

<INITIAL,TDEF,TS,TSS,TSI>"extern" =>
     (tok(Tokens.EXTERN,source,yypos,yypos+size yytext-1));

<INITIAL,TDEF,TS,TSS,TSI>"unsigned" =>
     (tok(Tokens.UNSIGNED,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"signed" =>
     (tok(Tokens.SIGNED,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"short"  =>
     (tok(Tokens.SHORT,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"long"   =>
     (tok(Tokens.LONG,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"int"    =>
     (tok(Tokens.INT,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"char"   =>
     (tok(Tokens.CHAR,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"_Bool"   =>
     (tok(Tokens.BOOL,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"void"   =>
     (tok(Tokens.VOID,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"inline"    =>
     (tok(Tokens.INLINE,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"_Noreturn"    =>
     (tok(Tokens.NORETURN,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"static"    =>
     (tok(Tokens.STATIC,source,yypos,yypos+size yytext-1));



<INITIAL,TDEF,TS,TSS,TSI>"if"     =>
     (tok(Tokens.YIF,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"else"   =>
     (tok(Tokens.YELSE,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"while"  =>
     (tok(Tokens.YWHILE,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"const"  =>
     (tok(Tokens.CONST,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"volatile"  =>
     (tok(Tokens.VOLATILE,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"restrict"  =>
     (tok(Tokens.RESTRICT,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"switch"  =>
     (tok(Tokens.SWITCH,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"case"  =>
     (tok(Tokens.CASE,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"default"  =>
     (tok(Tokens.DEFAULT,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"do"  =>
     (tok(Tokens.YDO,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"for"    =>
     (tok(Tokens.YFOR,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"break"  =>
     (tok(Tokens.YBREAK,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"continue" =>
     (tok(Tokens.YCONTINUE,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"return" =>
     (tok(Tokens.YRETURN,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"sizeof" =>
     (tok(Tokens.YSIZEOF,source,yypos,yypos+size yytext-1));
<INITIAL,TS,TSS,TSI>"enum" =>
     (tok(Tokens.YENUM,source,yypos,yypos+size yytext-1));
<INITIAL,TDEF,TS,TSS,TSI>"__attribute__" =>
     (tok(Tokens.GCC_ATTRIBUTE,source,yypos,yypos+size yytext-1));
<INITIAL>"__asm__" | "asm" => (tok(Tokens.YASM,source,yypos,yypos + size yytext - 1));

<INITIAL,TDEF,TS,TSS,TSI>{integer} =>
     (let val left = getPos(source, yypos)
          val right = getPos(source, yypos + size yytext - 1)
      in
        mkNumber StringCvt.DEC (left, right, yytext)
      end);

<INITIAL,TDEF,TS,TSS,TSI>{hexint} =>
     (let val left = getPos(source, yypos)
          val right = getPos(source, yypos + size yytext - 1)
      in
        mkNumber StringCvt.HEX (left, right, String.extract(yytext,2,NONE))
      end);

<INITIAL,TDEF,TS,TSS,TSI>{octint} =>
     (let val left = getPos(source, yypos)
          val right = getPos(source, yypos + size yytext - 1)
      in
        mkNumber StringCvt.OCT (left, right, yytext)
      end);

<INITIAL,TSS,TSI,TS,TDEF>^"# "{integer}" "\"[^\"]+\"(" "{integer})*{newline} =>
            (let val (_::nstr::fstr::_) = String.tokens Char.isSpace yytext
                 val n = valOf (Int.fromString nstr)
                 val f = String.substring(fstr, 1, size fstr - 2)
             in
               SourceFile.lineDirective (source, SOME f,
                                     {lineNum = n,
                                      lineStart = yypos + size yytext});
               continue()
             end);

<INITIAL,TSS,TSI,TS,TDEF>^"#line" {ws}+ {integer} {ws}+ \"[-A-Za-z0-9_.<>/\032]+\"{ws}*{newline} =>
            (let val (_::nstr::fstr::_) = String.tokens Char.isSpace yytext
                 val n = valOf (Int.fromString nstr)
                 val f = String.substring(fstr, 1, size fstr - 2)
             in
               SourceFile.lineDirective (source, SOME f,
                                     {lineNum = n,
                                      lineStart = yypos + size yytext});
               continue()
             end);


<INITIAL,TSS,TSI,TS,TDEF>^"#pragma".*{newline} =>
   (SourceFile.newline(source, yypos + size yytext); continue());

<INITIAL,TSI>{identifier} => (resolve_id(true, yyarg, yypos, yytext));
<TDEF,TSS>{identifier} => (resolve_id(!tokpdepth <> 0, yyarg, yypos, yytext));
<TS>{identifier} => (YYBEGIN TSS;
                     mk_tokident(yytext, getPos(source, yypos),
                                 getPos(source, yypos + size yytext - 1)));



<INITIAL>.        => (error ("ignoring bad character "^yytext,
                             getPos(source, yypos),
                             getPos (source, yypos));
                      continue());
<TDEF,TSI,TSS,TS>. => (error("Character "^yytext^" can not follow typedef",
                            getPos(source,yypos),
                            getPos(source,yypos));
                       continue());



<SLSLCOMMENT>{newline} => (YYBEGIN (case !return of
                               SINITIAL => INITIAL
                             | STDEF => TDEF
                             | STS => TS
                             | STSS => TSS
                             | STSI => TSI);
                    in_comment := false;
                    SourceFile.newline(source, yypos+1);
                    continue());
<SLSLCOMMENT>. => (continue());

<TRADCOMMENT>{newline} => (SourceFile.newline(source,yypos+1); continue());
<TRADCOMMENT>"*/" => (YYBEGIN (case !return of
                                 SINITIAL => INITIAL
                               | STDEF => TDEF
                               | STS => TS
                               | STSS => TSS
                               | STSI => TSI);
                      in_comment := false;
                      continue());
<TRADCOMMENT>.  => (continue());


<SPECIAL_COMMENT,SPEC_COMM0>INV(ARIANT)?: =>
   (YYBEGIN SPECIAL_COMMENT;
    tok(Tokens.INVARIANT,source,yypos,yypos+size yytext - 1));

<SPECIAL_COMMENT,SPEC_COMM0>FNSPEC =>
   (YYBEGIN SPECIAL_COMMENT;
    tok(Tokens.FNSPEC,source,yypos,yypos+size yytext - 1));

<SPECIAL_COMMENT,SPEC_COMM0>RELSPEC =>
  (YYBEGIN SPECIAL_COMMENT;
   tok(Tokens.RELSPEC,source,yypos,yypos+size yytext - 1));

<SPECIAL_COMMENT,SPEC_COMM0>MODIFIES: =>
  (YYBEGIN SPECIAL_COMMENT;
   tok(Tokens.MODIFIES,source,yypos,yypos+size yytext-1));

<SPECIAL_COMMENT,SPEC_COMM0>AUXUPD: =>
  (YYBEGIN SPECIAL_COMMENT;
   tok(Tokens.AUXUPD,source,yypos,yypos+size yytext-1));

<SPECIAL_COMMENT,SPEC_COMM0>GHOSTUPD: =>
  (YYBEGIN SPECIAL_COMMENT;
   tok(Tokens.GHOSTUPD,source,yypos,yypos+size yytext-1));

<SPECIAL_COMMENT,SPEC_COMM0>SPEC: =>
  (YYBEGIN SPECIAL_COMMENT;
   tok(Tokens.SPEC_BEGIN,source,yypos,yypos+size yytext-1));

<SPECIAL_COMMENT,SPEC_COMM0>END-SPEC: =>
  (YYBEGIN SPECIAL_COMMENT;
   tok(Tokens.SPEC_END,source,yypos,yypos+size yytext-1));

<SPECIAL_COMMENT,SPEC_COMM0>DONT_TRANSLATE =>
  (YYBEGIN SPECIAL_COMMENT;
   tok(Tokens.DONT_TRANSLATE,source,yypos,yypos+size yytext-1));

<SPECIAL_COMMENT,SPEC_COMM0>CALLS =>
  (YYBEGIN SPECIAL_COMMENT;
   tok (Tokens.CALLS,source,yypos,yypos + size yytext - 1));

<SPECIAL_COMMENT,SPEC_COMM0>OWNED_BY =>
  (YYBEGIN SPECIAL_COMMENT;
   tok (Tokens.OWNED_BY,source,yypos,yypos + size yytext - 1));


<SPECIAL_COMMENT,SPEC_COMM0>{ws}+ => (continue());
<SPEC_COMM0,SPEC_COMMJUNK>"*/" => (YYBEGIN INITIAL; continue());
<SPECIAL_COMMENT,SPEC_COMM0,SPEC_COMMJUNK>{newline} => (SourceFile.newline(source, yypos+1); continue());
<SPEC_COMM0>. => (YYBEGIN SPEC_COMMJUNK; continue());
<SPEC_COMMJUNK>. => (continue());

<SPECIAL_COMMENT>"\"" => (YYBEGIN SPEC_STRINGLIT;
                          stringlitContent := [];
                          stringlitStart := getPos(source,yypos);
                          continue());
<SPECIAL_COMMENT>":" => (tok(Tokens.YCOLON,source,yypos,yypos));
<SPECIAL_COMMENT>";" => (tok(Tokens.YSEMI,source,yypos,yypos));
<SPECIAL_COMMENT>"[" => (tok(Tokens.LBRACKET,source,yypos,yypos));
<SPECIAL_COMMENT>"]" => (tok(Tokens.RBRACKET,source,yypos,yypos));
<SPECIAL_COMMENT>"*" => (tok(Tokens.YSTAR,source,yypos,yypos));
<SPECIAL_COMMENT>{identifier} =>
  (mk_tokident(yytext,getPos(source,yypos),
               getPos(source,yypos + size yytext - 1)));
<SPECIAL_COMMENT>"*/" => (YYBEGIN INITIAL;
                          tok(Tokens.SPEC_BLOCKEND,source,yypos,yypos+2));
<SPECIAL_COMMENT>. => (error("Illegal character ("^yytext^
                             ") in special annotation",
                             getPos(source,yypos),
                             getPos(source,yypos));
                       continue());


<SPEC_STRINGLIT>"\"" =>
  (YYBEGIN SPECIAL_COMMENT;
   Tokens.STRING_LITERAL(String.concat (List.rev (!stringlitContent)),
                         !stringlitStart,
                         getPos(source,yypos+size yytext)));

<SPEC_STRINGLIT>"\\\"" => (stringlitContent := "\"" :: !stringlitContent;
                           continue());
<SPEC_STRINGLIT>. => (stringlitContent := yytext :: !stringlitContent;
                      continue());
<SPEC_STRINGLIT>{newline} => (SourceFile.newline(source,yypos+1);
                       stringlitContent := yytext :: !stringlitContent;
                       continue());

<INITIAL,TDEF,TS,TSS,TSI>"\"" ([^\"] | "\\\"")* "\"" =>
    (Tokens.STRING_LITERAL(String.substring(yytext,1,size yytext - 2),
                           getPos(source,yypos),
                           getPos(source,yypos + size yytext)));

<CHARLIT>[^'\\] => (charlitContent :=
                      IntInf.fromInt (Char.ord (String.sub(yytext,0))) ::
                      !charlitContent;
                    continue());

<CHARLIT>"\\" ['\"?\\abfnrtv] =>
  (let val c = String.sub(yytext,1)
       val i = case c of
                 #"a" => 7
               | #"b" => 8
               | #"f" => 12
               | #"n" => 10
               | #"r" => 13
               | #"t" => 9
               | #"v" => 11
               | c => Char.ord c
                      (* assumes SML char is no bigger than target's *)
   in
     charlitContent :=
     IntInf.fromInt i :: !charlitContent;
     continue()
   end);

<CHARLIT>"\\" [0-7]+ => (let
                           open IntInf
                           val i = valOf (StringCvt.scanString
                                              (scan StringCvt.OCT)
                                              (String.extract(yytext, 1, NONE)))
                         in
                           if i > ImplementationNumbers.UCHAR_MAX then
                             error("Character literal component too large!",
                                   getPos(source, yypos),
                                   getPos(source, yypos))
                           else ();
                           charlitContent := i :: !charlitContent;
                           continue()
                         end);

<CHARLIT>"\\x" [0-9A-Fa-f]+ => (
  let
    open IntInf
    val i = valOf (StringCvt.scanString (scan StringCvt.HEX)
                                        (String.extract (yytext, 1, NONE)))
  in
    if i > ImplementationNumbers.UCHAR_MAX then
      error("Character literal component too large!",
            getPos(source, yypos),
            getPos(source, yypos))
    else ();
    charlitContent := i :: !charlitContent;
    continue()
  end);

<CHARLIT>"'" => (let val rs = case !return of
                                SINITIAL => INITIAL
                              | STDEF => TDEF
                              | STS => TS
                              | STSS => TSS
                              | STSI => TSI
                     val l = !charlitStart and r = getPos(source, yypos)
                     fun tok i = Tokens.NUMERIC_CONSTANT
                                     ({value = i, suffix = "",
                                       base = StringCvt.DEC}, l, r)
                     open ImplementationNumbers
                 in
                   YYBEGIN rs;
                   case !charlitContent of
                     [i] => tok (charliteral_conversion i)
                   | _ => (error("Malformed character literal",l,r); tok 0)
                 end);

<CHARLIT>. => (let val l = !charlitStart
                   val r = getPos(source, yypos)
               in
                 error("Malformed character literal", l, r);
                 Tokens.NUMERIC_CONSTANT({value = 0, suffix = "",
                                          base = StringCvt.DEC}, l, r)
               end);
