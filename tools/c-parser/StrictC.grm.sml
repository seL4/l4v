(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

functor StrictCLrValsFun(structure Token : TOKEN)
 : sig structure ParserData : PARSER_DATA
       structure Tokens : StrictC_TOKENS
   end
 = 
struct
structure ParserData=
struct
structure Header = 
struct
(** @LICENSE(NICTA_OKL_EXCLUSIVE) **)

open Absyn NameGeneration
val errorStr' = Feedback.errorStr'
val warnStr' = Feedback.warnStr'
val bogus = SourcePos.bogus

fun lleft [] = bogus
  | lleft (h :: t) = left h
fun lright [] = bogus
  | lright x = right (List.last x)
type adecl = (expr ctype -> expr ctype) wrap
type 'a ddecl = string wrap
                * adecl
                * (expr ctype * string wrap option) wrap list option
                * 'a list
type addecl = gcc_attribute ddecl
infix ood  (* composition of declarators *)
fun ooa(adec1, adec2) = let
  (* composition of abstract declarators *)
  val a1 = node adec1
  val a2 = node adec2
in
  wrap(a1 o a2, left adec1, right adec2)
end

fun ood(ddw, adec) = let
  val (nm, adec0, params, data) = node ddw
in
  wrap((nm, ooa(adec0,adec), params, data), left ddw, right adec)
end

fun add_attributes(ddw, attrs) = let
  val (nm, adec, ps, data0) = node ddw
in
  wrap((nm, adec, ps, attrs @ data0), left ddw, right ddw)
end


fun addparams(dw : 'a ddecl wrap, ps) : 'a ddecl wrap = let
  val (nm, a, pso, data) = node dw
in
  case pso of
    SOME _ => dw
  | NONE => wrap((nm,a,SOME ps,data), left dw, right dw)
end

fun check_params
      (plist : (expr ctype * string wrap option) wrap list wrap)
      : (expr ctype * string wrap option) wrap list =
    case node plist of
      [] => (Feedback.warnStr'(left plist, right plist,
                               "Avoid empty parameter lists in C; \
                               \prefer \"(void)\"");
             [])
    | x as [tysw] => (case node tysw of
                        (Void, NONE) => []
                      | _ => x)
    | x => x



fun fndecl l r (ps : expr ctype list) =
    wrap((fn ty => Function(ty, ps)), l, r)
fun ptrdecl l r = wrap (Ptr, l, r)
fun arraydecl l r n = wrap ((fn ty => Array (ty, n)), l, r)

val one_const = expr_int 1
val zero_const = expr_int 0
fun postinc e = Assign(e,ebogwrap(BinOp(Plus,e,one_const)))
fun postdec e = Assign(e,ebogwrap(BinOp(Minus,e,one_const)))


fun resolve_fnname e =
    case enode e of
      Var (s,_) => s
    | _ => (errorStr'(eleft e, eright e,
                      "Can't use this expression as function name");
            "_bad name_")


fun handle_builtin_fns e =
    case enode e of
      EFnCall (fn_e, args) => let
      in
        case enode fn_e of
          Var(s,_) =>
          if s = NameGeneration.mkIdentUScoreSafe "__builtin_expect" then
            case args of
              [x,y] => x
            | _ => (Feedback.errorStr'(eleft e, eright e,
                                       "__builtin_expect must take 2 args.");
                    expr_int 0)
          else e
        | _ => e
      end
    | _ => e

fun delvoidcasts e =
    case enode e of
      TypeCast (tywrap, e0) => let
      in
        case node tywrap of
          Void => e0
        | _ => e
      end
    | _ => e


fun parse_stdassignop (e1,opn,e2) = let
  val e2 = handle_builtin_fns e2
  val r_e = case opn of
              NONE => e2
            | SOME abop => ewrap(BinOp(abop,e1,e2), eleft e2, eright e2)
in
  case enode e2 of
    EFnCall (f_e, args) => let
      fun e_ok e =
          case enode e of
            Var _ => true
          | StructDot(e0, fld) => e_ok e0
          | _ => false
    in
      if e_ok e1 andalso opn = NONE then
        AssignFnCall(SOME e1, f_e, args)
      else
        Assign(e1,r_e)
    end
  | _ => Assign(e1,r_e)
end

fun check_names (fname:string) plist = let
  fun check i ps =
      case ps of
        [] => []
      | pw :: rest =>
          (case node pw of
             (ty, SOME nm) => (ty,nm) :: check (i + 1) rest
           | (ty, NONE) => (errorStr'(left pw, right pw,
                                      "Parameter #"^Int.toString i^
                                      " of function "^fname^
                                      " has no name");
                            (ty, wrap("__fake", bogus, bogus)) ::
                            check (i + 1) rest))
in
  check 1 plist
end

type struct_field = (expr ctype * string wrap * expr option)
type struct_fields = struct_field list
type struct_id_decl = string wrap * struct_fields

local val scount = ref 0
in
fun gen_struct_id () = (scount := !scount + 1;
                        "ISA_anon_struct___"^Int.toString (!scount))
fun gen_enum_name () = (scount := !scount + 1;
                        wrap("ISA_anon_enum___" ^ Int.toString (!scount),
                             SourcePos.bogus, SourcePos.bogus))
end

datatype storage_class_specifier = TypeDef | Extern | Static | Auto | Register
datatype type_qualifier = Const | Volatile | Restrict
datatype typespectok = ts_unsigned
                     | ts_signed
                     | ts_bool
                     | ts_char
                     | ts_int
                     | ts_long
                     | ts_longlong
                     | ts_short
                     | ts_void
type struct_or_union_specifier = expr ctype wrap * struct_id_decl wrap list
type enum_specifier = (string option wrap *
                       (string wrap * expr option) list) wrap
datatype type_specifier = Tstok of typespectok wrap
                        | Tsstruct of struct_or_union_specifier
                        | Tsenum of enum_specifier
                        | Tstypeid of string wrap
fun tsleft (Tstok tok) = left tok
  | tsleft (Tsstruct (ty, _)) = left ty
  | tsleft (Tstypeid s) = left s
  | tsleft (Tsenum es) = left es
fun tsright (Tstok tok) = right tok
  | tsright (Tsstruct (ty, _)) = right ty
  | tsright (Tstypeid s) = right s
  | tsright (Tsenum es) = right es

datatype decl_specifier = Storage of storage_class_specifier wrap
                        | TypeQual of type_qualifier wrap
                        | TypeSpec of type_specifier
                        | FunSpec of Absyn.fnspec wrap

fun dslleft [] = raise Fail "dslleft: nil"
  | dslleft (h :: t) =
    case h of
      Storage s => left s
    | TypeQual s => left s
    | FunSpec s => left s
    | TypeSpec ts => tsleft ts
fun dslright dsl =
    case dsl of
      [] => raise Fail "dslright: nil"
    | [h] => (case h of
                Storage s => right s
              | TypeQual s => right s
              | FunSpec s => right s
              | TypeSpec ts => tsright ts)
    | h::t => dslright t


fun parse_siddecl (s : struct_id_decl wrap) : declaration wrap = let
  val (nm, fields) = node s
  fun ok_inttype ity = (ity = Int)
  fun f (ty : expr ctype, s : string wrap, opbit : expr option) = let
    fun error r = (errorStr'(left s, r, "Bad base-type for bitfield");
                   Bitfield(true, one_const))
    val ty' : expr ctype =
        case opbit of
          NONE => ty
        | SOME e => (case ty of
                       Signed ity =>
                       if ok_inttype ity then
                         Bitfield(true, e)
                       else error (eright e)
                     | Unsigned ity =>
                       if ok_inttype ity then
                         Bitfield(false, e)
                       else error (eright e)
                     | _ => error (eright e))
  in
    (ty',s)
  end
  val fields' = map f fields
in
  wrap(StructDecl(nm, fields'), left s, right s)
end

fun empty_enumspec es = [wrap(EnumDecl (node es), left es, right es)]

fun empty_declarator (ds : decl_specifier list) : declaration wrap list =
    case ds of
      [] => raise Fail "empty_declarator: nil"
    | Storage x :: rest =>
                (errorStr'(left x, right x,
                           "Storage class qualifier not accompanied by \
                           \declarator");
                 empty_declarator rest)
    | TypeQual tq :: rest =>
                 (errorStr'(left tq, right tq,
                            "Type-qualifier not accompanied by declarator");
                  empty_declarator rest)
    | FunSpec fs :: rest =>
                 (errorStr'(left fs, right fs,
                            "Function-specifier not accompanied by declarator");
                  empty_declarator rest)
    | TypeSpec (Tstok tok) :: rest =>
                 (errorStr'(left tok, right tok,
                            "Type not accompanied by declarator");
                  empty_declarator rest)
    | TypeSpec (Tstypeid s) :: rest =>
                 (errorStr'(left s, right s,
                            "Type-id ("^node s^ ") not accompanied by declarator");
                  empty_declarator rest)
    | [TypeSpec (Tsstruct (_, siddecls))] => map parse_siddecl siddecls
    | TypeSpec (Tsstruct s) :: rest =>
                 (errorStr'(dslleft rest, dslright rest,
                            "Extraneous crap after struct declaration");
                  empty_declarator [TypeSpec (Tsstruct s)])
    | [TypeSpec (Tsenum es)] => empty_enumspec es
    | TypeSpec (Tsenum es) :: rest =>
                 (errorStr'(dslleft rest, dslright rest,
                            "Extraneous crap after enum declaration");
                  empty_enumspec es)

fun ity_of_tok tstok =
    case node tstok of
      ts_int => Int
    | ts_char => Char
    | ts_short => Short
    | ts_long => Long
    | ts_longlong => LongLong
    | x => raise Fail "ty_of_tok: invariant failure"

fun sort_toks (bases, sgnmods) dsl =
    case dsl of
      [] => (bases, sgnmods)
    | TypeSpec (Tstok tk) :: r =>
            (case node tk of
               ts_unsigned => sort_toks (bases, tk :: sgnmods) r
             | ts_signed => sort_toks (bases, tk :: sgnmods) r
             | _ => sort_toks (wrap(Tstok tk, left tk, right tk) :: bases,
                               sgnmods) r)
    | TypeSpec (x as Tsstruct (ty,_)) :: r =>
        sort_toks (wrap(x, left ty, right ty)::bases, sgnmods) r
    | TypeSpec (x as Tstypeid sw) :: r =>
        sort_toks (wrap(x,left sw,right sw)::bases, sgnmods) r
    | TypeSpec (x as Tsenum es) :: r =>
        sort_toks (wrap(x,left es, right es)::bases, sgnmods) r
    | _ :: r => sort_toks (bases, sgnmods) r

fun extract_fnspecs (dsl : decl_specifier list) : fnspec list =
    List.mapPartial (fn FunSpec fs => SOME (node fs) | _ => NONE) dsl

fun extract_type (dsl : decl_specifier list wrap) : expr ctype wrap = let
  val (bases : type_specifier wrap list,
       sgnmods : typespectok wrap list) = sort_toks ([], []) (node dsl)
  fun is_base b (tn : type_specifier wrap) =
      case node tn of
          Tstok t => node t = b
        | _ => false
  fun is_intmod (tn : type_specifier wrap) =
      case node tn of
          Tstok t => (case node t of
                          ts_short => true
                        | ts_long => true
                        | _ => false)
        | _ => false
  fun handle_integral_remainder had_int list =
      case list of
          [] => NONE
        | [x] => if had_int then
                   if is_intmod x then SOME x
                   else
                     (errorStr'(left x, right x, "Bad combination with 'int'");
                      SOME x)
                 else SOME x
        | [x,y] => (case (node x, node y) of
                        (Tstok k1, Tstok k2) => let
                          (* order here is reverse of occurrence in input *)
                          val l = left y and r = right x
                        in
                          if node k1 = ts_long andalso node k2 = ts_long then
                            SOME (wrap (Tstok (wrap(ts_longlong, l, r)), l, r))
                          else
                            (errorStr'(l, r, "Two type-specifiers"); SOME x)
                        end
                      | _ => (errorStr'(left x, right x, "Two type-specifiers");
                              SOME x))
        | h::t => (errorStr'(left h, right h, "Too many type-specifiers");
                   SOME h)

  fun check_baseclashes list =
      case list of
        [] => NONE
      | [x] => SOME x
      | _ =>
        case List.partition (is_base ts_int) list of
            ([], _) => handle_integral_remainder false list
          | ([_], rest) => handle_integral_remainder true rest
          | (t::_, _) => (errorStr'(left t, right t, "Too many 'int' specifiers");
                          SOME t)

  fun check_modclashes list =
      case list of
        [] => NONE
      | [x] => SOME x
      | h :: t => (errorStr'(left h, right h, "Multiple type-specifiers");
                   SOME h)
  val basety = check_baseclashes bases
  val sgnmod = check_modclashes sgnmods
in
  case (basety, sgnmod) of
    (NONE, NONE) => (errorStr'(left dsl, right dsl,
                               "No base type in declaration");
                     wrap(Signed Int, bogus, bogus))
  | (SOME b, NONE) => let
    in
      case node b of
        Tstok tk => (case node tk of
                       ts_void => wrap(Void, left tk, right tk)
                     | ts_char => wrap(PlainChar, left tk, right tk)
                     | ts_bool => wrap(Bool, left tk, right tk)
                     | x => wrap(Signed (ity_of_tok tk),
                                 left tk, right tk))
      | Tsstruct (ty, _) => ty
      | Tstypeid s => wrap(Ident (node s), left s, right s)
      | Tsenum e => wrap (EnumTy (node (#1 (node e))), left e, right e)
    end
  | (NONE, SOME m) =>
    (case node m of
       ts_unsigned => wrap(Unsigned Int, left m, right m)
     | ts_signed => wrap (Signed Int, left m, right m)
     | x => raise Fail "finalty2: inv failure")
  | (SOME b, SOME m) =>
     case node b of
       Tstok tk =>
       (case node tk of
            ts_void => (errorStr'(left m, right m,
                                  "Signedness modifier on void");
                        wrap(Void, left tk, right tk))
          | ts_bool => (errorStr'(left m, right m,
                                  "Signedness modifier on _Bool");
                        wrap(Bool, left tk, right tk))
          | _ =>
            let
            in
              case node m of
                  ts_unsigned => wrap(Unsigned (ity_of_tok tk),
                                      left m, right tk)
                | ts_signed => wrap(Signed (ity_of_tok tk),
                                    left m, right tk)
                | x => raise Fail "finalty3: inv failure"
            end)
     | Tstypeid s => (errorStr'(left m, right m,
                                "Signedness modifier on typedef id");
                      wrap(Ident (node s), left s, right s))
     | Tsstruct(ty,_) => (errorStr'(left m, right m,
                                    "Signedness modifier on struct");
                          ty)
     | Tsenum e => (errorStr'(left m, right m, "Signedness modifier on enum");
                    wrap(EnumTy (node (#1 (node e))), left e, right e))
end

(* returns a (SourcePos.t * SourcePos.t) option *)
fun has_typedef (dsl : decl_specifier list wrap) = let
  fun check dsls =
      case dsls of
        [] => NONE
      | Storage s :: rest =>
                (case node s of TypeDef => SOME (left s, right s)
                              | _ => check rest)
      | _ :: rest => check rest
in
  check (node dsl)
end

(* returns a (SourcePos.t * SourcePos.t) option *)
fun has_extern (dsl : decl_specifier list wrap) = let
  fun check dsls =
      case dsls of
        [] => NONE
      | Storage s :: rest => (case node s of Extern => SOME (left s, right s)
                                           | _ => check rest)
      | _ :: rest => check rest
in
  check (node dsl)
end

fun first_sdecls (dsl : decl_specifier list) =
    case dsl of
      [] => []
    | TypeSpec (Tsstruct(ty, sdecls)) :: _ => sdecls
    | _ :: rest => first_sdecls rest

fun first_enum_dec (dsl : decl_specifier list) =
    case dsl of
      [] => NONE
    | TypeSpec (Tsenum es) :: rest => if null (#2 (node es)) then
                                        first_enum_dec rest
                                      else SOME es
    | _ :: rest => first_enum_dec rest

fun wonky_pdec_check dsl = let
  val _ =
      case has_typedef dsl of
        NONE => ()
      | SOME (l,r) => errorStr'(l, r, "Typedefs forbidden in parameters")
  val _ =
      case has_extern dsl of
        NONE => ()
      | SOME (l,r) => errorStr'(l,r, "Extern forbidden in parameters")
  val _ = case first_sdecls (node dsl) of
            [] => ()
          | sd :: _ => let
              val sw = #1 (node sd)
            in
              errorStr' (left sw, right sw,
                         "Don't declare structs in parameters")
            end
  val _ = case first_enum_dec (node dsl) of
            NONE => ()
          | SOME es  => errorStr'(left es, right es,
                                  "Don't declare enumerations in parameters")
in
  ()
end

fun unwrap_params pms =
    map (fn w => apsnd (Option.map node) (node w)) (valOf pms)


(* is not a function definition, is at least one declarator
   This means this could be a
     a) list of variable/function declarations (initialised or not)
     b) list of typedefs
 *)
fun make_declaration (dsl : decl_specifier list wrap)
                     (idl : (addecl wrap * initializer option) wrap list) =
let
  val basetype = extract_type dsl
  val is_typedef = isSome (has_typedef dsl)
  val is_extern = isSome (has_extern dsl)
  val sdecls = first_sdecls (node dsl)
  val endecs = case first_enum_dec (node dsl) of
                 NONE => []
               | SOME es => [wrap(EnumDecl (node es), left es, right es)]
  val fnspecs = extract_fnspecs (node dsl)

  fun handle_declarator idw = let
    val (d : addecl wrap, iopt : initializer option) = node idw
    val (nm, a : adecl, params, attrs) = node d
    val finaltype = (node a) (node basetype)
  in
    if is_typedef then let
        val _ = case iopt of
                  SOME i => errorStr'(left idw, right idw,
                                      "Can't initialise a typedef")
                | _ => ()
      in
        wrap(TypeDecl[(finaltype,nm)], left idw, right idw)
      end
    else
      case finaltype of
        Function(rettype, ptys) => let
          val _ = case iopt of
                    SOME _ => errorStr'(left idw, right idw,
                                        "Can't initialise a function!")
                  | NONE => ()
        in
          wrap(ExtFnDecl { rettype = rettype, name = nm,
                           params = unwrap_params params,
                           specs = merge_specs [gcc_attribs attrs] fnspecs},
               left idw, right idw)
        end
      | _ => let
          val _ =
              if is_extern andalso isSome iopt then
                errorStr'(left idw, right idw, "Don't initialise externs")
              else ()
        in
          wrap(VarDecl(finaltype, nm, not is_extern, iopt, attrs),
               left idw, right idw)
        end
  end
in
  endecs @
  map handle_declarator idl @
  map parse_siddecl sdecls
end

fun last_blockitem (bilist : block_item list) = let
  val bi = List.last bilist
  fun recurse bi =
    case bi of
      BI_Stmt st => (case snode st of
                       Block bilist => last_blockitem bilist
                     | _ => bi)
    | _ => bi
in
  recurse bi
end

fun CaseEndBI bi =
    case bi of
      BI_Stmt st => CaseEndStmt st
    | BI_Decl d => false
and CaseEndStmt st =
    case snode st of
      Break => true
    | Return _ => true
    | ReturnFnCall _ => true
    | IfStmt(g, t, e) => CaseEndStmt t andalso CaseEndStmt e
    | Block bilist => CaseEndBI (last_blockitem bilist)
    | _ => false

fun front [] = []
  | front [h] = []
  | front (x::xs) = x :: front xs

fun removelast_if_break bilist = let
  fun singcase bi =
      case bi of
        BI_Stmt st => let
        in
          case snode st of
            Break => []
          | Block bilist => [BI_Stmt
                                 (swrap (Block (removelast_if_break bilist),
                                         sleft st, sright st))]
          | _ => [bi]
        end
      | _ => [bi]
in
  case bilist of
    [] => []
  | [bi] => singcase bi
  | bi :: bis => bi :: removelast_if_break bis
end

fun mk_defaultcase_last caselist = let
  fun extract_default caselist =
      case caselist of
        [] => (NONE, [])
      | (c as (labs, bilist)) :: rest => let
          fun is_dflt lab =
              case node lab of
                NONE => true
              | _ => false
        in
          case List.find is_dflt (node labs) of
            NONE => let
              val (df, rest) = extract_default rest
            in
              (df, c::rest)
            end
          | SOME d => let
            in
              if length (node labs) > 1 then
                warnStr'(left d, right d,
                         "This default: label should be the only label\
                         \ associated with this case")
              else ();
              (SOME (wrap([d], left labs, right labs), bilist), rest)
            end
        end
  val (dflt, rest) = extract_default caselist
in
  case dflt of
    NONE => caselist @ [(bogwrap [bogwrap NONE],
                         [BI_Stmt (swrap(EmptyStmt, bogus, bogus))])]
  | SOME d => rest @ [d]
end


fun switch_check scaselist leftp rightp = let
  val _ = case length scaselist of
            0 => errorStr'(leftp, rightp, "Switch has no cases")
          | 1 => errorStr'(leftp, rightp, "Switch has only one case")
          | _ => ()
  fun check_for_breaks (labs, bilist) =
      if not (CaseEndBI (last_blockitem bilist)) then
        errorStr'(left labs, right labs,
                  "Switch case beginning here does not end with a break \
                  \or return")
      else ()
  val _ = app check_for_breaks (front scaselist)
          (* only check front of list, allowing for last case to fall through
             to end without a break *)
  val scaselist = mk_defaultcase_last scaselist
  fun striplabwrap (lab : expr option wrap) = node lab
  fun striplablist llist = map striplabwrap (node llist)
in
  map (fn (labs,bod) => (striplablist labs, removelast_if_break bod)) scaselist
end


fun check_for_proto d = let
  val dec = node d
in
  case dec of
    ExtFnDecl _ => (errorStr'(left d, right d,
                              "Don't put function prototypes other than at \
                              \top level"); d)
  | _ => d
end


end
structure LrTable = Token.LrTable
structure Token = Token
local open LrTable in 
val table=let val actionRows =
"\
\\001\000\001\000\000\000\000\000\
\\001\000\001\000\230\001\000\000\
\\001\000\001\000\231\001\035\000\041\000\060\000\040\000\061\000\039\000\
\\062\000\038\000\063\000\037\000\064\000\036\000\065\000\035\000\
\\066\000\034\000\067\000\033\000\070\000\032\000\072\000\031\000\
\\074\000\030\000\075\000\029\000\076\000\028\000\077\000\027\000\
\\078\000\026\000\080\000\025\000\081\000\024\000\082\000\023\000\
\\083\000\022\000\086\000\021\000\088\000\020\000\091\000\019\000\
\\094\000\018\000\096\000\017\000\000\000\
\\001\000\001\000\232\001\000\000\
\\001\000\001\000\233\001\035\000\233\001\060\000\233\001\061\000\233\001\
\\062\000\233\001\063\000\233\001\064\000\233\001\065\000\233\001\
\\066\000\233\001\067\000\233\001\070\000\233\001\072\000\233\001\
\\074\000\233\001\075\000\233\001\076\000\233\001\077\000\233\001\
\\078\000\233\001\080\000\233\001\081\000\233\001\082\000\233\001\
\\083\000\233\001\086\000\233\001\088\000\233\001\091\000\233\001\
\\094\000\233\001\096\000\233\001\000\000\
\\001\000\001\000\234\001\035\000\234\001\060\000\234\001\061\000\234\001\
\\062\000\234\001\063\000\234\001\064\000\234\001\065\000\234\001\
\\066\000\234\001\067\000\234\001\070\000\234\001\072\000\234\001\
\\074\000\234\001\075\000\234\001\076\000\234\001\077\000\234\001\
\\078\000\234\001\080\000\234\001\081\000\234\001\082\000\234\001\
\\083\000\234\001\086\000\234\001\088\000\234\001\091\000\234\001\
\\094\000\234\001\096\000\234\001\000\000\
\\001\000\001\000\008\002\002\000\008\002\005\000\008\002\007\000\008\002\
\\008\000\008\002\012\000\008\002\018\000\008\002\020\000\008\002\
\\021\000\008\002\022\000\008\002\035\000\008\002\036\000\008\002\
\\038\000\008\002\039\000\008\002\040\000\008\002\041\000\008\002\
\\042\000\008\002\043\000\008\002\044\000\008\002\045\000\008\002\
\\046\000\008\002\047\000\008\002\060\000\008\002\061\000\008\002\
\\062\000\008\002\063\000\008\002\064\000\008\002\065\000\008\002\
\\066\000\008\002\067\000\008\002\069\000\008\002\070\000\008\002\
\\071\000\008\002\072\000\008\002\074\000\008\002\075\000\008\002\
\\076\000\008\002\077\000\008\002\078\000\008\002\080\000\008\002\
\\081\000\008\002\082\000\008\002\083\000\008\002\084\000\008\002\
\\085\000\008\002\086\000\008\002\088\000\008\002\089\000\008\002\
\\091\000\008\002\092\000\008\002\094\000\008\002\095\000\008\002\
\\096\000\008\002\000\000\
\\001\000\001\000\009\002\002\000\009\002\005\000\009\002\007\000\009\002\
\\008\000\009\002\012\000\009\002\018\000\009\002\020\000\009\002\
\\021\000\009\002\022\000\009\002\035\000\009\002\036\000\009\002\
\\038\000\009\002\039\000\009\002\040\000\009\002\041\000\009\002\
\\042\000\009\002\043\000\009\002\044\000\009\002\045\000\009\002\
\\046\000\009\002\047\000\009\002\060\000\009\002\061\000\009\002\
\\062\000\009\002\063\000\009\002\064\000\009\002\065\000\009\002\
\\066\000\009\002\067\000\009\002\069\000\009\002\070\000\009\002\
\\071\000\009\002\072\000\009\002\074\000\009\002\075\000\009\002\
\\076\000\009\002\077\000\009\002\078\000\009\002\080\000\009\002\
\\081\000\009\002\082\000\009\002\083\000\009\002\084\000\009\002\
\\085\000\009\002\086\000\009\002\088\000\009\002\089\000\009\002\
\\091\000\009\002\092\000\009\002\094\000\009\002\095\000\009\002\
\\096\000\009\002\000\000\
\\001\000\001\000\018\002\035\000\018\002\060\000\018\002\061\000\018\002\
\\062\000\018\002\063\000\018\002\064\000\018\002\065\000\018\002\
\\066\000\018\002\067\000\018\002\070\000\018\002\072\000\018\002\
\\074\000\018\002\075\000\018\002\076\000\018\002\077\000\018\002\
\\078\000\018\002\080\000\018\002\081\000\018\002\082\000\018\002\
\\083\000\018\002\086\000\018\002\088\000\018\002\091\000\018\002\
\\094\000\018\002\096\000\018\002\000\000\
\\001\000\001\000\026\002\002\000\026\002\005\000\026\002\007\000\026\002\
\\008\000\026\002\012\000\026\002\018\000\026\002\020\000\026\002\
\\021\000\026\002\022\000\026\002\035\000\026\002\036\000\026\002\
\\037\000\026\002\038\000\026\002\039\000\026\002\040\000\026\002\
\\041\000\026\002\042\000\026\002\043\000\026\002\044\000\026\002\
\\045\000\026\002\046\000\026\002\047\000\026\002\060\000\026\002\
\\061\000\026\002\062\000\026\002\063\000\026\002\064\000\026\002\
\\065\000\026\002\066\000\026\002\067\000\026\002\069\000\026\002\
\\070\000\026\002\071\000\026\002\072\000\026\002\074\000\026\002\
\\075\000\026\002\076\000\026\002\077\000\026\002\078\000\026\002\
\\080\000\026\002\081\000\026\002\082\000\026\002\083\000\026\002\
\\084\000\026\002\085\000\026\002\086\000\026\002\088\000\026\002\
\\089\000\026\002\090\000\026\002\091\000\026\002\092\000\026\002\
\\094\000\026\002\095\000\026\002\096\000\026\002\000\000\
\\001\000\002\000\235\001\005\000\235\001\006\000\235\001\009\000\235\001\
\\011\000\235\001\012\000\235\001\035\000\235\001\060\000\235\001\
\\061\000\235\001\062\000\235\001\063\000\235\001\064\000\235\001\
\\065\000\235\001\066\000\235\001\067\000\235\001\069\000\235\001\
\\070\000\235\001\072\000\235\001\074\000\235\001\075\000\235\001\
\\076\000\235\001\077\000\235\001\078\000\235\001\080\000\235\001\
\\081\000\235\001\082\000\235\001\083\000\235\001\086\000\235\001\
\\088\000\235\001\091\000\235\001\094\000\235\001\096\000\235\001\000\000\
\\001\000\002\000\236\001\005\000\236\001\006\000\236\001\009\000\236\001\
\\011\000\236\001\012\000\236\001\035\000\236\001\060\000\236\001\
\\061\000\236\001\062\000\236\001\063\000\236\001\064\000\236\001\
\\065\000\236\001\066\000\236\001\067\000\236\001\069\000\236\001\
\\070\000\236\001\072\000\236\001\074\000\236\001\075\000\236\001\
\\076\000\236\001\077\000\236\001\078\000\236\001\080\000\236\001\
\\081\000\236\001\082\000\236\001\083\000\236\001\086\000\236\001\
\\088\000\236\001\091\000\236\001\094\000\236\001\096\000\236\001\000\000\
\\001\000\002\000\237\001\005\000\237\001\006\000\237\001\009\000\237\001\
\\011\000\237\001\012\000\237\001\035\000\237\001\060\000\237\001\
\\061\000\237\001\062\000\237\001\063\000\237\001\064\000\237\001\
\\065\000\237\001\066\000\237\001\067\000\237\001\069\000\237\001\
\\070\000\237\001\072\000\237\001\074\000\237\001\075\000\237\001\
\\076\000\237\001\077\000\237\001\078\000\237\001\080\000\237\001\
\\081\000\237\001\082\000\237\001\083\000\237\001\086\000\237\001\
\\088\000\237\001\091\000\237\001\094\000\237\001\096\000\237\001\000\000\
\\001\000\002\000\238\001\005\000\238\001\006\000\238\001\009\000\238\001\
\\011\000\238\001\012\000\238\001\035\000\238\001\060\000\238\001\
\\061\000\238\001\062\000\238\001\063\000\238\001\064\000\238\001\
\\065\000\238\001\066\000\238\001\067\000\238\001\069\000\238\001\
\\070\000\238\001\072\000\238\001\074\000\238\001\075\000\238\001\
\\076\000\238\001\077\000\238\001\078\000\238\001\080\000\238\001\
\\081\000\238\001\082\000\238\001\083\000\238\001\086\000\238\001\
\\088\000\238\001\091\000\238\001\094\000\238\001\096\000\238\001\000\000\
\\001\000\002\000\239\001\005\000\239\001\006\000\239\001\009\000\239\001\
\\011\000\239\001\012\000\239\001\035\000\239\001\060\000\239\001\
\\061\000\239\001\062\000\239\001\063\000\239\001\064\000\239\001\
\\065\000\239\001\066\000\239\001\067\000\239\001\069\000\239\001\
\\070\000\239\001\072\000\239\001\074\000\239\001\075\000\239\001\
\\076\000\239\001\077\000\239\001\078\000\239\001\080\000\239\001\
\\081\000\239\001\082\000\239\001\083\000\239\001\086\000\239\001\
\\088\000\239\001\091\000\239\001\094\000\239\001\096\000\239\001\000\000\
\\001\000\002\000\240\001\005\000\240\001\006\000\240\001\009\000\240\001\
\\011\000\240\001\012\000\240\001\035\000\240\001\060\000\240\001\
\\061\000\240\001\062\000\240\001\063\000\240\001\064\000\240\001\
\\065\000\240\001\066\000\240\001\067\000\240\001\069\000\240\001\
\\070\000\240\001\072\000\240\001\074\000\240\001\075\000\240\001\
\\076\000\240\001\077\000\240\001\078\000\240\001\080\000\240\001\
\\081\000\240\001\082\000\240\001\083\000\240\001\086\000\240\001\
\\088\000\240\001\091\000\240\001\094\000\240\001\096\000\240\001\000\000\
\\001\000\002\000\241\001\005\000\241\001\006\000\241\001\009\000\241\001\
\\011\000\241\001\012\000\241\001\035\000\241\001\060\000\241\001\
\\061\000\241\001\062\000\241\001\063\000\241\001\064\000\241\001\
\\065\000\241\001\066\000\241\001\067\000\241\001\069\000\241\001\
\\070\000\241\001\072\000\241\001\074\000\241\001\075\000\241\001\
\\076\000\241\001\077\000\241\001\078\000\241\001\080\000\241\001\
\\081\000\241\001\082\000\241\001\083\000\241\001\086\000\241\001\
\\088\000\241\001\091\000\241\001\094\000\241\001\096\000\241\001\000\000\
\\001\000\002\000\242\001\005\000\242\001\006\000\242\001\007\000\242\001\
\\009\000\242\001\011\000\242\001\012\000\242\001\013\000\242\001\
\\015\000\242\001\035\000\242\001\060\000\242\001\061\000\242\001\
\\062\000\242\001\063\000\242\001\064\000\242\001\065\000\242\001\
\\066\000\242\001\067\000\242\001\069\000\242\001\070\000\242\001\
\\072\000\242\001\074\000\242\001\075\000\242\001\076\000\242\001\
\\077\000\242\001\078\000\242\001\080\000\242\001\081\000\242\001\
\\082\000\242\001\083\000\242\001\086\000\242\001\088\000\242\001\
\\091\000\242\001\094\000\242\001\095\000\242\001\096\000\242\001\000\000\
\\001\000\002\000\243\001\005\000\243\001\006\000\243\001\007\000\243\001\
\\009\000\243\001\011\000\243\001\012\000\243\001\013\000\243\001\
\\015\000\243\001\035\000\243\001\060\000\243\001\061\000\243\001\
\\062\000\243\001\063\000\243\001\064\000\243\001\065\000\243\001\
\\066\000\243\001\067\000\243\001\069\000\243\001\070\000\243\001\
\\072\000\243\001\074\000\243\001\075\000\243\001\076\000\243\001\
\\077\000\243\001\078\000\243\001\080\000\243\001\081\000\243\001\
\\082\000\243\001\083\000\243\001\086\000\243\001\088\000\243\001\
\\091\000\243\001\094\000\243\001\095\000\243\001\096\000\243\001\000\000\
\\001\000\002\000\010\002\005\000\010\002\006\000\010\002\009\000\010\002\
\\011\000\010\002\012\000\010\002\035\000\041\000\060\000\040\000\
\\061\000\039\000\062\000\038\000\063\000\037\000\064\000\036\000\
\\065\000\035\000\066\000\034\000\067\000\033\000\069\000\010\002\
\\070\000\032\000\072\000\031\000\074\000\030\000\075\000\029\000\
\\076\000\028\000\077\000\027\000\078\000\026\000\080\000\025\000\
\\081\000\024\000\082\000\023\000\083\000\022\000\086\000\021\000\
\\088\000\020\000\091\000\019\000\094\000\018\000\096\000\017\000\000\000\
\\001\000\002\000\011\002\005\000\011\002\006\000\011\002\009\000\011\002\
\\011\000\011\002\012\000\011\002\069\000\011\002\000\000\
\\001\000\002\000\012\002\005\000\012\002\006\000\012\002\009\000\012\002\
\\011\000\012\002\012\000\012\002\035\000\041\000\060\000\040\000\
\\061\000\039\000\062\000\038\000\063\000\037\000\064\000\036\000\
\\065\000\035\000\066\000\034\000\067\000\033\000\069\000\012\002\
\\070\000\032\000\072\000\031\000\074\000\030\000\075\000\029\000\
\\076\000\028\000\077\000\027\000\078\000\026\000\080\000\025\000\
\\081\000\024\000\082\000\023\000\083\000\022\000\086\000\021\000\
\\088\000\020\000\091\000\019\000\094\000\018\000\096\000\017\000\000\000\
\\001\000\002\000\013\002\005\000\013\002\006\000\013\002\009\000\013\002\
\\011\000\013\002\012\000\013\002\069\000\013\002\000\000\
\\001\000\002\000\014\002\005\000\014\002\006\000\014\002\009\000\014\002\
\\011\000\014\002\012\000\014\002\035\000\041\000\060\000\040\000\
\\061\000\039\000\062\000\038\000\063\000\037\000\064\000\036\000\
\\065\000\035\000\066\000\034\000\067\000\033\000\069\000\014\002\
\\070\000\032\000\072\000\031\000\074\000\030\000\075\000\029\000\
\\076\000\028\000\077\000\027\000\078\000\026\000\080\000\025\000\
\\081\000\024\000\082\000\023\000\083\000\022\000\086\000\021\000\
\\088\000\020\000\091\000\019\000\094\000\018\000\096\000\017\000\000\000\
\\001\000\002\000\015\002\005\000\015\002\006\000\015\002\009\000\015\002\
\\011\000\015\002\012\000\015\002\069\000\015\002\000\000\
\\001\000\002\000\016\002\005\000\016\002\006\000\016\002\009\000\016\002\
\\011\000\016\002\012\000\016\002\035\000\041\000\060\000\040\000\
\\061\000\039\000\062\000\038\000\063\000\037\000\064\000\036\000\
\\065\000\035\000\066\000\034\000\067\000\033\000\069\000\016\002\
\\070\000\032\000\072\000\031\000\074\000\030\000\075\000\029\000\
\\076\000\028\000\077\000\027\000\078\000\026\000\080\000\025\000\
\\081\000\024\000\082\000\023\000\083\000\022\000\086\000\021\000\
\\088\000\020\000\091\000\019\000\094\000\018\000\096\000\017\000\000\000\
\\001\000\002\000\017\002\005\000\017\002\006\000\017\002\009\000\017\002\
\\011\000\017\002\012\000\017\002\069\000\017\002\000\000\
\\001\000\002\000\029\002\005\000\029\002\007\000\029\002\008\000\029\002\
\\012\000\029\002\018\000\029\002\020\000\029\002\021\000\029\002\
\\022\000\029\002\035\000\029\002\036\000\029\002\038\000\029\002\
\\039\000\029\002\040\000\029\002\041\000\029\002\042\000\029\002\
\\043\000\029\002\044\000\029\002\045\000\029\002\046\000\029\002\
\\047\000\029\002\060\000\029\002\061\000\029\002\062\000\029\002\
\\063\000\029\002\064\000\029\002\065\000\029\002\066\000\029\002\
\\067\000\029\002\069\000\029\002\070\000\029\002\071\000\029\002\
\\072\000\029\002\074\000\029\002\075\000\029\002\076\000\029\002\
\\077\000\029\002\078\000\029\002\080\000\029\002\081\000\029\002\
\\082\000\029\002\083\000\029\002\084\000\029\002\085\000\029\002\
\\086\000\029\002\088\000\029\002\089\000\029\002\091\000\029\002\
\\092\000\029\002\094\000\029\002\095\000\029\002\096\000\029\002\000\000\
\\001\000\002\000\030\002\005\000\030\002\007\000\030\002\008\000\030\002\
\\012\000\030\002\018\000\030\002\020\000\030\002\021\000\030\002\
\\022\000\030\002\035\000\030\002\036\000\030\002\038\000\030\002\
\\039\000\030\002\040\000\030\002\041\000\030\002\042\000\030\002\
\\043\000\030\002\044\000\030\002\045\000\030\002\046\000\030\002\
\\047\000\030\002\060\000\030\002\061\000\030\002\062\000\030\002\
\\063\000\030\002\064\000\030\002\065\000\030\002\066\000\030\002\
\\067\000\030\002\069\000\030\002\070\000\030\002\071\000\030\002\
\\072\000\030\002\074\000\030\002\075\000\030\002\076\000\030\002\
\\077\000\030\002\078\000\030\002\080\000\030\002\081\000\030\002\
\\082\000\030\002\083\000\030\002\084\000\030\002\085\000\030\002\
\\086\000\030\002\088\000\030\002\089\000\030\002\091\000\030\002\
\\092\000\030\002\094\000\030\002\095\000\030\002\096\000\030\002\000\000\
\\001\000\002\000\037\002\005\000\037\002\006\000\037\002\009\000\037\002\
\\035\000\041\000\060\000\040\000\061\000\039\000\062\000\038\000\
\\063\000\037\000\064\000\036\000\065\000\035\000\066\000\034\000\
\\067\000\033\000\069\000\037\002\070\000\032\000\072\000\031\000\
\\076\000\028\000\077\000\027\000\078\000\026\000\000\000\
\\001\000\002\000\038\002\005\000\038\002\006\000\038\002\009\000\038\002\
\\069\000\038\002\000\000\
\\001\000\002\000\039\002\005\000\039\002\006\000\039\002\009\000\039\002\
\\035\000\041\000\060\000\040\000\061\000\039\000\062\000\038\000\
\\063\000\037\000\064\000\036\000\065\000\035\000\066\000\034\000\
\\067\000\033\000\069\000\039\002\070\000\032\000\072\000\031\000\
\\076\000\028\000\077\000\027\000\078\000\026\000\000\000\
\\001\000\002\000\040\002\005\000\040\002\006\000\040\002\009\000\040\002\
\\069\000\040\002\000\000\
\\001\000\002\000\041\002\005\000\041\002\006\000\041\002\009\000\041\002\
\\011\000\041\002\012\000\041\002\035\000\041\002\060\000\041\002\
\\061\000\041\002\062\000\041\002\063\000\041\002\064\000\041\002\
\\065\000\041\002\066\000\041\002\067\000\041\002\069\000\041\002\
\\070\000\041\002\072\000\041\002\074\000\041\002\075\000\041\002\
\\076\000\041\002\077\000\041\002\078\000\041\002\080\000\041\002\
\\081\000\041\002\082\000\041\002\083\000\041\002\086\000\041\002\
\\088\000\041\002\091\000\041\002\094\000\041\002\096\000\041\002\000\000\
\\001\000\002\000\042\002\005\000\042\002\006\000\042\002\009\000\042\002\
\\011\000\042\002\012\000\042\002\035\000\042\002\060\000\042\002\
\\061\000\042\002\062\000\042\002\063\000\042\002\064\000\042\002\
\\065\000\042\002\066\000\042\002\067\000\042\002\069\000\042\002\
\\070\000\042\002\072\000\042\002\074\000\042\002\075\000\042\002\
\\076\000\042\002\077\000\042\002\078\000\042\002\080\000\042\002\
\\081\000\042\002\082\000\042\002\083\000\042\002\086\000\042\002\
\\088\000\042\002\091\000\042\002\094\000\042\002\096\000\042\002\000\000\
\\001\000\002\000\043\002\005\000\043\002\006\000\043\002\009\000\043\002\
\\011\000\043\002\012\000\043\002\035\000\043\002\060\000\043\002\
\\061\000\043\002\062\000\043\002\063\000\043\002\064\000\043\002\
\\065\000\043\002\066\000\043\002\067\000\043\002\069\000\043\002\
\\070\000\043\002\072\000\043\002\074\000\043\002\075\000\043\002\
\\076\000\043\002\077\000\043\002\078\000\043\002\080\000\043\002\
\\081\000\043\002\082\000\043\002\083\000\043\002\086\000\043\002\
\\088\000\043\002\091\000\043\002\094\000\043\002\096\000\043\002\000\000\
\\001\000\002\000\044\002\005\000\044\002\006\000\044\002\009\000\044\002\
\\011\000\044\002\069\000\044\002\076\000\028\000\077\000\027\000\
\\078\000\026\000\088\000\044\002\094\000\044\002\000\000\
\\001\000\002\000\045\002\005\000\045\002\006\000\045\002\009\000\045\002\
\\011\000\045\002\069\000\045\002\088\000\045\002\094\000\045\002\000\000\
\\001\000\002\000\072\002\005\000\072\002\006\000\072\002\007\000\072\002\
\\009\000\072\002\011\000\072\002\012\000\072\002\035\000\072\002\
\\060\000\072\002\061\000\072\002\062\000\072\002\063\000\072\002\
\\064\000\072\002\065\000\072\002\066\000\072\002\067\000\072\002\
\\069\000\072\002\070\000\072\002\072\000\072\002\074\000\072\002\
\\075\000\072\002\076\000\072\002\077\000\072\002\078\000\072\002\
\\080\000\072\002\081\000\072\002\082\000\072\002\083\000\072\002\
\\086\000\072\002\088\000\072\002\091\000\072\002\094\000\072\002\
\\096\000\072\002\000\000\
\\001\000\002\000\073\002\005\000\073\002\006\000\073\002\007\000\073\002\
\\009\000\073\002\011\000\073\002\012\000\073\002\035\000\073\002\
\\060\000\073\002\061\000\073\002\062\000\073\002\063\000\073\002\
\\064\000\073\002\065\000\073\002\066\000\073\002\067\000\073\002\
\\069\000\073\002\070\000\073\002\072\000\073\002\074\000\073\002\
\\075\000\073\002\076\000\073\002\077\000\073\002\078\000\073\002\
\\080\000\073\002\081\000\073\002\082\000\073\002\083\000\073\002\
\\086\000\073\002\088\000\073\002\091\000\073\002\094\000\073\002\
\\096\000\073\002\000\000\
\\001\000\002\000\074\002\005\000\074\002\006\000\074\002\007\000\094\000\
\\009\000\074\002\011\000\074\002\012\000\074\002\035\000\074\002\
\\060\000\074\002\061\000\074\002\062\000\074\002\063\000\074\002\
\\064\000\074\002\065\000\074\002\066\000\074\002\067\000\074\002\
\\069\000\074\002\070\000\074\002\072\000\074\002\074\000\074\002\
\\075\000\074\002\076\000\074\002\077\000\074\002\078\000\074\002\
\\080\000\074\002\081\000\074\002\082\000\074\002\083\000\074\002\
\\086\000\074\002\088\000\074\002\091\000\074\002\094\000\074\002\
\\096\000\074\002\000\000\
\\001\000\002\000\075\002\005\000\075\002\006\000\075\002\009\000\075\002\
\\011\000\075\002\012\000\075\002\035\000\075\002\060\000\075\002\
\\061\000\075\002\062\000\075\002\063\000\075\002\064\000\075\002\
\\065\000\075\002\066\000\075\002\067\000\075\002\069\000\075\002\
\\070\000\075\002\072\000\075\002\074\000\075\002\075\000\075\002\
\\076\000\075\002\077\000\075\002\078\000\075\002\080\000\075\002\
\\081\000\075\002\082\000\075\002\083\000\075\002\086\000\075\002\
\\088\000\075\002\091\000\075\002\094\000\075\002\096\000\075\002\000\000\
\\001\000\002\000\076\002\005\000\076\002\006\000\076\002\009\000\076\002\
\\011\000\076\002\012\000\076\002\035\000\076\002\060\000\076\002\
\\061\000\076\002\062\000\076\002\063\000\076\002\064\000\076\002\
\\065\000\076\002\066\000\076\002\067\000\076\002\069\000\076\002\
\\070\000\076\002\072\000\076\002\074\000\076\002\075\000\076\002\
\\076\000\076\002\077\000\076\002\078\000\076\002\080\000\076\002\
\\081\000\076\002\082\000\076\002\083\000\076\002\086\000\076\002\
\\088\000\076\002\091\000\076\002\094\000\076\002\096\000\076\002\000\000\
\\001\000\002\000\077\002\005\000\077\002\006\000\077\002\009\000\077\002\
\\011\000\077\002\012\000\077\002\035\000\077\002\060\000\077\002\
\\061\000\077\002\062\000\077\002\063\000\077\002\064\000\077\002\
\\065\000\077\002\066\000\077\002\067\000\077\002\069\000\077\002\
\\070\000\077\002\072\000\077\002\074\000\077\002\075\000\077\002\
\\076\000\077\002\077\000\077\002\078\000\077\002\080\000\077\002\
\\081\000\077\002\082\000\077\002\083\000\077\002\086\000\077\002\
\\088\000\077\002\091\000\077\002\094\000\077\002\096\000\077\002\000\000\
\\001\000\002\000\078\002\005\000\078\002\006\000\078\002\009\000\078\002\
\\011\000\078\002\012\000\078\002\035\000\078\002\060\000\078\002\
\\061\000\078\002\062\000\078\002\063\000\078\002\064\000\078\002\
\\065\000\078\002\066\000\078\002\067\000\078\002\069\000\078\002\
\\070\000\078\002\072\000\078\002\074\000\078\002\075\000\078\002\
\\076\000\078\002\077\000\078\002\078\000\078\002\080\000\078\002\
\\081\000\078\002\082\000\078\002\083\000\078\002\086\000\078\002\
\\088\000\078\002\091\000\078\002\094\000\078\002\096\000\078\002\000\000\
\\001\000\002\000\079\002\005\000\079\002\006\000\079\002\009\000\079\002\
\\011\000\079\002\012\000\079\002\035\000\079\002\060\000\079\002\
\\061\000\079\002\062\000\079\002\063\000\079\002\064\000\079\002\
\\065\000\079\002\066\000\079\002\067\000\079\002\069\000\079\002\
\\070\000\079\002\072\000\079\002\074\000\079\002\075\000\079\002\
\\076\000\079\002\077\000\079\002\078\000\079\002\080\000\079\002\
\\081\000\079\002\082\000\079\002\083\000\079\002\086\000\079\002\
\\088\000\079\002\091\000\079\002\094\000\079\002\096\000\079\002\000\000\
\\001\000\002\000\080\002\005\000\080\002\006\000\080\002\009\000\080\002\
\\011\000\080\002\012\000\080\002\035\000\080\002\060\000\080\002\
\\061\000\080\002\062\000\080\002\063\000\080\002\064\000\080\002\
\\065\000\080\002\066\000\080\002\067\000\080\002\069\000\080\002\
\\070\000\080\002\072\000\080\002\074\000\080\002\075\000\080\002\
\\076\000\080\002\077\000\080\002\078\000\080\002\080\000\080\002\
\\081\000\080\002\082\000\080\002\083\000\080\002\086\000\080\002\
\\088\000\080\002\091\000\080\002\094\000\080\002\096\000\080\002\000\000\
\\001\000\002\000\081\002\005\000\081\002\006\000\081\002\009\000\081\002\
\\011\000\081\002\012\000\081\002\035\000\081\002\060\000\081\002\
\\061\000\081\002\062\000\081\002\063\000\081\002\064\000\081\002\
\\065\000\081\002\066\000\081\002\067\000\081\002\069\000\081\002\
\\070\000\081\002\072\000\081\002\074\000\081\002\075\000\081\002\
\\076\000\081\002\077\000\081\002\078\000\081\002\080\000\081\002\
\\081\000\081\002\082\000\081\002\083\000\081\002\086\000\081\002\
\\088\000\081\002\091\000\081\002\094\000\081\002\096\000\081\002\000\000\
\\001\000\002\000\082\002\005\000\082\002\006\000\082\002\009\000\082\002\
\\011\000\082\002\012\000\082\002\035\000\082\002\060\000\082\002\
\\061\000\082\002\062\000\082\002\063\000\082\002\064\000\082\002\
\\065\000\082\002\066\000\082\002\067\000\082\002\069\000\082\002\
\\070\000\082\002\072\000\082\002\074\000\082\002\075\000\082\002\
\\076\000\082\002\077\000\082\002\078\000\082\002\080\000\082\002\
\\081\000\082\002\082\000\082\002\083\000\082\002\086\000\082\002\
\\088\000\082\002\091\000\082\002\094\000\082\002\096\000\082\002\000\000\
\\001\000\002\000\083\002\005\000\083\002\006\000\083\002\009\000\083\002\
\\011\000\083\002\012\000\083\002\035\000\083\002\060\000\083\002\
\\061\000\083\002\062\000\083\002\063\000\083\002\064\000\083\002\
\\065\000\083\002\066\000\083\002\067\000\083\002\069\000\083\002\
\\070\000\083\002\072\000\083\002\074\000\083\002\075\000\083\002\
\\076\000\083\002\077\000\083\002\078\000\083\002\080\000\083\002\
\\081\000\083\002\082\000\083\002\083\000\083\002\086\000\083\002\
\\088\000\083\002\091\000\083\002\094\000\083\002\096\000\083\002\000\000\
\\001\000\002\000\084\002\005\000\084\002\006\000\084\002\009\000\084\002\
\\011\000\084\002\012\000\084\002\035\000\084\002\060\000\084\002\
\\061\000\084\002\062\000\084\002\063\000\084\002\064\000\084\002\
\\065\000\084\002\066\000\084\002\067\000\084\002\069\000\084\002\
\\070\000\084\002\072\000\084\002\074\000\084\002\075\000\084\002\
\\076\000\084\002\077\000\084\002\078\000\084\002\080\000\084\002\
\\081\000\084\002\082\000\084\002\083\000\084\002\086\000\084\002\
\\088\000\084\002\091\000\084\002\094\000\084\002\096\000\084\002\000\000\
\\001\000\002\000\085\002\005\000\085\002\006\000\085\002\009\000\085\002\
\\011\000\085\002\012\000\085\002\035\000\085\002\060\000\085\002\
\\061\000\085\002\062\000\085\002\063\000\085\002\064\000\085\002\
\\065\000\085\002\066\000\085\002\067\000\085\002\069\000\085\002\
\\070\000\085\002\072\000\085\002\074\000\085\002\075\000\085\002\
\\076\000\085\002\077\000\085\002\078\000\085\002\080\000\085\002\
\\081\000\085\002\082\000\085\002\083\000\085\002\086\000\085\002\
\\088\000\085\002\091\000\085\002\094\000\085\002\096\000\085\002\000\000\
\\001\000\002\000\086\002\005\000\086\002\006\000\086\002\009\000\086\002\
\\011\000\086\002\012\000\086\002\035\000\086\002\060\000\086\002\
\\061\000\086\002\062\000\086\002\063\000\086\002\064\000\086\002\
\\065\000\086\002\066\000\086\002\067\000\086\002\069\000\086\002\
\\070\000\086\002\072\000\086\002\074\000\086\002\075\000\086\002\
\\076\000\086\002\077\000\086\002\078\000\086\002\080\000\086\002\
\\081\000\086\002\082\000\086\002\083\000\086\002\086\000\086\002\
\\088\000\086\002\091\000\086\002\094\000\086\002\096\000\086\002\000\000\
\\001\000\002\000\087\002\005\000\087\002\006\000\087\002\009\000\087\002\
\\011\000\087\002\012\000\087\002\035\000\087\002\060\000\087\002\
\\061\000\087\002\062\000\087\002\063\000\087\002\064\000\087\002\
\\065\000\087\002\066\000\087\002\067\000\087\002\069\000\087\002\
\\070\000\087\002\072\000\087\002\074\000\087\002\075\000\087\002\
\\076\000\087\002\077\000\087\002\078\000\087\002\080\000\087\002\
\\081\000\087\002\082\000\087\002\083\000\087\002\086\000\087\002\
\\088\000\087\002\091\000\087\002\094\000\087\002\096\000\087\002\000\000\
\\001\000\002\000\088\002\005\000\088\002\006\000\088\002\009\000\088\002\
\\011\000\088\002\012\000\088\002\035\000\088\002\060\000\088\002\
\\061\000\088\002\062\000\088\002\063\000\088\002\064\000\088\002\
\\065\000\088\002\066\000\088\002\067\000\088\002\069\000\088\002\
\\070\000\088\002\072\000\088\002\074\000\088\002\075\000\088\002\
\\076\000\088\002\077\000\088\002\078\000\088\002\080\000\088\002\
\\081\000\088\002\082\000\088\002\083\000\088\002\086\000\088\002\
\\088\000\088\002\091\000\088\002\094\000\088\002\096\000\088\002\000\000\
\\001\000\002\000\089\002\005\000\089\002\006\000\089\002\009\000\089\002\
\\011\000\089\002\012\000\089\002\035\000\089\002\060\000\089\002\
\\061\000\089\002\062\000\089\002\063\000\089\002\064\000\089\002\
\\065\000\089\002\066\000\089\002\067\000\089\002\069\000\089\002\
\\070\000\089\002\072\000\089\002\074\000\089\002\075\000\089\002\
\\076\000\089\002\077\000\089\002\078\000\089\002\080\000\089\002\
\\081\000\089\002\082\000\089\002\083\000\089\002\086\000\089\002\
\\088\000\089\002\091\000\089\002\094\000\089\002\096\000\089\002\000\000\
\\001\000\002\000\090\002\005\000\090\002\006\000\090\002\009\000\090\002\
\\011\000\090\002\012\000\090\002\035\000\090\002\060\000\090\002\
\\061\000\090\002\062\000\090\002\063\000\090\002\064\000\090\002\
\\065\000\090\002\066\000\090\002\067\000\090\002\069\000\090\002\
\\070\000\090\002\072\000\090\002\074\000\090\002\075\000\090\002\
\\076\000\090\002\077\000\090\002\078\000\090\002\080\000\090\002\
\\081\000\090\002\082\000\090\002\083\000\090\002\086\000\090\002\
\\088\000\090\002\091\000\090\002\094\000\090\002\096\000\090\002\000\000\
\\001\000\002\000\091\002\005\000\091\002\006\000\091\002\009\000\091\002\
\\011\000\091\002\012\000\091\002\035\000\091\002\060\000\091\002\
\\061\000\091\002\062\000\091\002\063\000\091\002\064\000\091\002\
\\065\000\091\002\066\000\091\002\067\000\091\002\069\000\091\002\
\\070\000\091\002\072\000\091\002\074\000\091\002\075\000\091\002\
\\076\000\091\002\077\000\091\002\078\000\091\002\080\000\091\002\
\\081\000\091\002\082\000\091\002\083\000\091\002\086\000\091\002\
\\088\000\091\002\091\000\091\002\094\000\091\002\096\000\091\002\000\000\
\\001\000\002\000\092\002\005\000\092\002\006\000\092\002\007\000\100\000\
\\009\000\092\002\011\000\092\002\012\000\092\002\035\000\092\002\
\\060\000\092\002\061\000\092\002\062\000\092\002\063\000\092\002\
\\064\000\092\002\065\000\092\002\066\000\092\002\067\000\092\002\
\\069\000\092\002\070\000\092\002\072\000\092\002\074\000\092\002\
\\075\000\092\002\076\000\092\002\077\000\092\002\078\000\092\002\
\\080\000\092\002\081\000\092\002\082\000\092\002\083\000\092\002\
\\086\000\092\002\088\000\092\002\091\000\092\002\094\000\092\002\
\\096\000\092\002\000\000\
\\001\000\002\000\113\002\005\000\113\002\007\000\113\002\018\000\113\002\
\\020\000\113\002\021\000\113\002\022\000\113\002\047\000\113\002\
\\069\000\113\002\071\000\113\002\092\000\113\002\000\000\
\\001\000\002\000\120\002\005\000\120\002\018\000\120\002\020\000\120\002\
\\021\000\120\002\022\000\120\002\047\000\120\002\069\000\120\002\
\\071\000\120\002\092\000\120\002\000\000\
\\001\000\002\000\121\002\005\000\121\002\018\000\121\002\020\000\121\002\
\\021\000\121\002\022\000\121\002\047\000\121\002\069\000\121\002\
\\071\000\121\002\092\000\121\002\000\000\
\\001\000\002\000\122\002\005\000\122\002\018\000\122\002\020\000\122\002\
\\021\000\122\002\022\000\122\002\047\000\122\002\069\000\122\002\
\\071\000\122\002\092\000\122\002\000\000\
\\001\000\002\000\123\002\005\000\123\002\018\000\123\002\020\000\123\002\
\\021\000\123\002\022\000\123\002\047\000\123\002\069\000\123\002\
\\071\000\123\002\092\000\123\002\000\000\
\\001\000\002\000\124\002\005\000\124\002\018\000\124\002\020\000\124\002\
\\021\000\124\002\022\000\124\002\047\000\124\002\069\000\124\002\
\\071\000\124\002\092\000\124\002\000\000\
\\001\000\002\000\125\002\005\000\125\002\018\000\125\002\020\000\125\002\
\\021\000\125\002\022\000\125\002\047\000\125\002\069\000\125\002\
\\071\000\125\002\092\000\125\002\000\000\
\\001\000\002\000\126\002\005\000\126\002\018\000\126\002\020\000\126\002\
\\021\000\126\002\022\000\126\002\047\000\126\002\069\000\126\002\
\\071\000\126\002\092\000\126\002\000\000\
\\001\000\002\000\127\002\005\000\127\002\018\000\127\002\020\000\127\002\
\\021\000\127\002\022\000\127\002\047\000\127\002\069\000\127\002\
\\071\000\127\002\092\000\127\002\000\000\
\\001\000\002\000\128\002\005\000\128\002\018\000\128\002\020\000\128\002\
\\021\000\128\002\022\000\128\002\047\000\128\002\069\000\128\002\
\\071\000\128\002\092\000\128\002\000\000\
\\001\000\002\000\129\002\005\000\129\002\018\000\129\002\020\000\129\002\
\\021\000\129\002\022\000\129\002\047\000\129\002\069\000\129\002\
\\071\000\129\002\092\000\129\002\000\000\
\\001\000\002\000\130\002\005\000\130\002\018\000\130\002\020\000\130\002\
\\021\000\130\002\022\000\130\002\047\000\130\002\069\000\130\002\
\\071\000\130\002\092\000\130\002\000\000\
\\001\000\002\000\131\002\005\000\131\002\007\000\131\002\008\000\131\002\
\\012\000\131\002\018\000\131\002\020\000\131\002\021\000\131\002\
\\022\000\131\002\035\000\131\002\036\000\131\002\037\000\131\002\
\\038\000\131\002\039\000\131\002\040\000\131\002\041\000\131\002\
\\042\000\131\002\043\000\131\002\044\000\131\002\045\000\131\002\
\\046\000\131\002\047\000\131\002\060\000\131\002\061\000\131\002\
\\062\000\131\002\063\000\131\002\064\000\131\002\065\000\131\002\
\\066\000\131\002\067\000\131\002\069\000\131\002\070\000\131\002\
\\071\000\131\002\072\000\131\002\074\000\131\002\075\000\131\002\
\\076\000\131\002\077\000\131\002\078\000\131\002\080\000\131\002\
\\081\000\131\002\082\000\131\002\083\000\131\002\084\000\131\002\
\\085\000\131\002\086\000\131\002\088\000\131\002\089\000\131\002\
\\090\000\131\002\091\000\131\002\092\000\131\002\094\000\131\002\
\\095\000\131\002\096\000\131\002\000\000\
\\001\000\002\000\132\002\005\000\132\002\007\000\132\002\008\000\132\002\
\\012\000\132\002\018\000\132\002\020\000\132\002\021\000\132\002\
\\022\000\132\002\035\000\132\002\036\000\132\002\037\000\132\002\
\\038\000\132\002\039\000\132\002\040\000\132\002\041\000\132\002\
\\042\000\132\002\043\000\132\002\044\000\132\002\045\000\132\002\
\\046\000\132\002\047\000\132\002\060\000\132\002\061\000\132\002\
\\062\000\132\002\063\000\132\002\064\000\132\002\065\000\132\002\
\\066\000\132\002\067\000\132\002\069\000\132\002\070\000\132\002\
\\071\000\132\002\072\000\132\002\074\000\132\002\075\000\132\002\
\\076\000\132\002\077\000\132\002\078\000\132\002\080\000\132\002\
\\081\000\132\002\082\000\132\002\083\000\132\002\084\000\132\002\
\\085\000\132\002\086\000\132\002\088\000\132\002\089\000\132\002\
\\090\000\132\002\091\000\132\002\092\000\132\002\094\000\132\002\
\\095\000\132\002\096\000\132\002\000\000\
\\001\000\002\000\133\002\005\000\133\002\007\000\133\002\008\000\133\002\
\\012\000\133\002\018\000\133\002\020\000\133\002\021\000\133\002\
\\022\000\133\002\035\000\133\002\036\000\133\002\037\000\133\002\
\\038\000\133\002\039\000\133\002\040\000\133\002\041\000\133\002\
\\042\000\133\002\043\000\133\002\044\000\133\002\045\000\133\002\
\\046\000\133\002\047\000\133\002\060\000\133\002\061\000\133\002\
\\062\000\133\002\063\000\133\002\064\000\133\002\065\000\133\002\
\\066\000\133\002\067\000\133\002\069\000\133\002\070\000\133\002\
\\071\000\133\002\072\000\133\002\074\000\133\002\075\000\133\002\
\\076\000\133\002\077\000\133\002\078\000\133\002\080\000\133\002\
\\081\000\133\002\082\000\133\002\083\000\133\002\084\000\133\002\
\\085\000\133\002\086\000\133\002\088\000\133\002\089\000\133\002\
\\090\000\133\002\091\000\133\002\092\000\133\002\094\000\133\002\
\\095\000\133\002\096\000\133\002\000\000\
\\001\000\002\000\134\002\005\000\134\002\007\000\134\002\008\000\134\002\
\\012\000\134\002\018\000\134\002\020\000\134\002\021\000\134\002\
\\022\000\134\002\035\000\134\002\036\000\134\002\037\000\134\002\
\\038\000\134\002\039\000\134\002\040\000\134\002\041\000\134\002\
\\042\000\134\002\043\000\134\002\044\000\134\002\045\000\134\002\
\\046\000\134\002\047\000\134\002\060\000\134\002\061\000\134\002\
\\062\000\134\002\063\000\134\002\064\000\134\002\065\000\134\002\
\\066\000\134\002\067\000\134\002\069\000\134\002\070\000\134\002\
\\071\000\134\002\072\000\134\002\074\000\134\002\075\000\134\002\
\\076\000\134\002\077\000\134\002\078\000\134\002\080\000\134\002\
\\081\000\134\002\082\000\134\002\083\000\134\002\084\000\134\002\
\\085\000\134\002\086\000\134\002\088\000\134\002\089\000\134\002\
\\090\000\134\002\091\000\134\002\092\000\134\002\094\000\134\002\
\\095\000\134\002\096\000\134\002\000\000\
\\001\000\002\000\135\002\005\000\135\002\007\000\135\002\008\000\135\002\
\\012\000\135\002\018\000\135\002\020\000\135\002\021\000\135\002\
\\022\000\135\002\035\000\135\002\036\000\135\002\037\000\135\002\
\\038\000\135\002\039\000\135\002\040\000\135\002\041\000\135\002\
\\042\000\135\002\043\000\135\002\044\000\135\002\045\000\135\002\
\\046\000\135\002\047\000\135\002\060\000\135\002\061\000\135\002\
\\062\000\135\002\063\000\135\002\064\000\135\002\065\000\135\002\
\\066\000\135\002\067\000\135\002\069\000\135\002\070\000\135\002\
\\071\000\135\002\072\000\135\002\074\000\135\002\075\000\135\002\
\\076\000\135\002\077\000\135\002\078\000\135\002\080\000\135\002\
\\081\000\135\002\082\000\135\002\083\000\135\002\084\000\135\002\
\\085\000\135\002\086\000\135\002\088\000\135\002\089\000\135\002\
\\090\000\135\002\091\000\135\002\092\000\135\002\094\000\135\002\
\\095\000\135\002\096\000\135\002\000\000\
\\001\000\002\000\136\002\005\000\136\002\007\000\136\002\008\000\136\002\
\\012\000\136\002\018\000\136\002\020\000\136\002\021\000\136\002\
\\022\000\136\002\035\000\136\002\036\000\136\002\037\000\136\002\
\\038\000\136\002\039\000\136\002\040\000\136\002\041\000\136\002\
\\042\000\136\002\043\000\136\002\044\000\136\002\045\000\136\002\
\\046\000\136\002\047\000\136\002\060\000\136\002\061\000\136\002\
\\062\000\136\002\063\000\136\002\064\000\136\002\065\000\136\002\
\\066\000\136\002\067\000\136\002\069\000\136\002\070\000\136\002\
\\071\000\136\002\072\000\136\002\074\000\136\002\075\000\136\002\
\\076\000\136\002\077\000\136\002\078\000\136\002\080\000\136\002\
\\081\000\136\002\082\000\136\002\083\000\136\002\084\000\136\002\
\\085\000\136\002\086\000\136\002\088\000\136\002\089\000\136\002\
\\090\000\136\002\091\000\136\002\092\000\136\002\094\000\136\002\
\\095\000\136\002\096\000\136\002\000\000\
\\001\000\002\000\137\002\005\000\137\002\007\000\137\002\008\000\137\002\
\\012\000\137\002\018\000\137\002\020\000\137\002\021\000\137\002\
\\022\000\137\002\035\000\137\002\036\000\137\002\037\000\137\002\
\\038\000\137\002\039\000\137\002\040\000\137\002\041\000\137\002\
\\042\000\137\002\043\000\137\002\044\000\137\002\045\000\137\002\
\\046\000\137\002\047\000\137\002\060\000\137\002\061\000\137\002\
\\062\000\137\002\063\000\137\002\064\000\137\002\065\000\137\002\
\\066\000\137\002\067\000\137\002\069\000\137\002\070\000\137\002\
\\071\000\137\002\072\000\137\002\074\000\137\002\075\000\137\002\
\\076\000\137\002\077\000\137\002\078\000\137\002\080\000\137\002\
\\081\000\137\002\082\000\137\002\083\000\137\002\084\000\137\002\
\\085\000\137\002\086\000\137\002\088\000\137\002\089\000\137\002\
\\090\000\137\002\091\000\137\002\092\000\137\002\094\000\137\002\
\\095\000\137\002\096\000\137\002\000\000\
\\001\000\002\000\138\002\005\000\138\002\007\000\138\002\008\000\138\002\
\\012\000\138\002\018\000\138\002\020\000\138\002\021\000\138\002\
\\022\000\138\002\035\000\138\002\036\000\138\002\037\000\138\002\
\\038\000\138\002\039\000\138\002\040\000\138\002\041\000\138\002\
\\042\000\138\002\043\000\138\002\044\000\138\002\045\000\138\002\
\\046\000\138\002\047\000\138\002\060\000\138\002\061\000\138\002\
\\062\000\138\002\063\000\138\002\064\000\138\002\065\000\138\002\
\\066\000\138\002\067\000\138\002\069\000\138\002\070\000\138\002\
\\071\000\138\002\072\000\138\002\074\000\138\002\075\000\138\002\
\\076\000\138\002\077\000\138\002\078\000\138\002\080\000\138\002\
\\081\000\138\002\082\000\138\002\083\000\138\002\084\000\138\002\
\\085\000\138\002\086\000\138\002\088\000\138\002\089\000\138\002\
\\090\000\138\002\091\000\138\002\092\000\138\002\094\000\138\002\
\\095\000\138\002\096\000\138\002\000\000\
\\001\000\002\000\139\002\005\000\139\002\007\000\139\002\008\000\139\002\
\\012\000\139\002\018\000\139\002\020\000\139\002\021\000\139\002\
\\022\000\139\002\035\000\139\002\036\000\139\002\037\000\139\002\
\\038\000\139\002\039\000\139\002\040\000\139\002\041\000\139\002\
\\042\000\139\002\043\000\139\002\044\000\139\002\045\000\139\002\
\\046\000\139\002\047\000\139\002\060\000\139\002\061\000\139\002\
\\062\000\139\002\063\000\139\002\064\000\139\002\065\000\139\002\
\\066\000\139\002\067\000\139\002\069\000\139\002\070\000\139\002\
\\071\000\139\002\072\000\139\002\074\000\139\002\075\000\139\002\
\\076\000\139\002\077\000\139\002\078\000\139\002\080\000\139\002\
\\081\000\139\002\082\000\139\002\083\000\139\002\084\000\139\002\
\\085\000\139\002\086\000\139\002\088\000\139\002\089\000\139\002\
\\090\000\139\002\091\000\139\002\092\000\139\002\094\000\139\002\
\\095\000\139\002\096\000\139\002\000\000\
\\001\000\002\000\140\002\005\000\140\002\007\000\140\002\008\000\140\002\
\\012\000\140\002\018\000\140\002\020\000\140\002\021\000\140\002\
\\022\000\140\002\035\000\140\002\036\000\140\002\037\000\184\001\
\\038\000\140\002\039\000\140\002\040\000\140\002\041\000\140\002\
\\042\000\140\002\043\000\140\002\044\000\140\002\045\000\140\002\
\\046\000\140\002\047\000\140\002\060\000\140\002\061\000\140\002\
\\062\000\140\002\063\000\140\002\064\000\140\002\065\000\140\002\
\\066\000\140\002\067\000\140\002\069\000\140\002\070\000\140\002\
\\071\000\140\002\072\000\140\002\074\000\140\002\075\000\140\002\
\\076\000\140\002\077\000\140\002\078\000\140\002\080\000\140\002\
\\081\000\140\002\082\000\140\002\083\000\140\002\084\000\140\002\
\\085\000\140\002\086\000\140\002\088\000\140\002\089\000\140\002\
\\090\000\140\002\091\000\140\002\092\000\140\002\094\000\140\002\
\\095\000\140\002\096\000\140\002\000\000\
\\001\000\002\000\141\002\005\000\141\002\007\000\141\002\008\000\141\002\
\\012\000\141\002\018\000\141\002\020\000\141\002\021\000\141\002\
\\022\000\141\002\035\000\141\002\036\000\141\002\037\000\141\002\
\\038\000\141\002\039\000\141\002\040\000\141\002\041\000\141\002\
\\042\000\141\002\043\000\141\002\044\000\141\002\045\000\141\002\
\\046\000\141\002\047\000\141\002\060\000\141\002\061\000\141\002\
\\062\000\141\002\063\000\141\002\064\000\141\002\065\000\141\002\
\\066\000\141\002\067\000\141\002\069\000\141\002\070\000\141\002\
\\071\000\141\002\072\000\141\002\074\000\141\002\075\000\141\002\
\\076\000\141\002\077\000\141\002\078\000\141\002\080\000\141\002\
\\081\000\141\002\082\000\141\002\083\000\141\002\084\000\141\002\
\\085\000\141\002\086\000\141\002\088\000\141\002\089\000\141\002\
\\090\000\141\002\091\000\141\002\092\000\141\002\094\000\141\002\
\\095\000\141\002\096\000\141\002\000\000\
\\001\000\002\000\142\002\005\000\142\002\007\000\142\002\008\000\142\002\
\\012\000\142\002\018\000\142\002\020\000\142\002\021\000\142\002\
\\022\000\142\002\035\000\142\002\036\000\142\002\037\000\142\002\
\\038\000\142\002\039\000\142\002\040\000\142\002\041\000\142\002\
\\042\000\142\002\043\000\142\002\044\000\142\002\045\000\142\002\
\\046\000\142\002\047\000\142\002\060\000\142\002\061\000\142\002\
\\062\000\142\002\063\000\142\002\064\000\142\002\065\000\142\002\
\\066\000\142\002\067\000\142\002\069\000\142\002\070\000\142\002\
\\071\000\142\002\072\000\142\002\074\000\142\002\075\000\142\002\
\\076\000\142\002\077\000\142\002\078\000\142\002\080\000\142\002\
\\081\000\142\002\082\000\142\002\083\000\142\002\084\000\142\002\
\\085\000\142\002\086\000\142\002\088\000\142\002\089\000\142\002\
\\090\000\142\002\091\000\142\002\092\000\142\002\094\000\142\002\
\\095\000\142\002\096\000\142\002\000\000\
\\001\000\002\000\143\002\005\000\143\002\007\000\143\002\008\000\143\002\
\\012\000\143\002\018\000\143\002\020\000\143\002\021\000\143\002\
\\022\000\143\002\035\000\143\002\036\000\143\002\037\000\143\002\
\\038\000\143\002\039\000\143\002\040\000\143\002\041\000\143\002\
\\042\000\143\002\043\000\143\002\044\000\143\002\045\000\143\002\
\\046\000\143\002\047\000\143\002\060\000\143\002\061\000\143\002\
\\062\000\143\002\063\000\143\002\064\000\143\002\065\000\143\002\
\\066\000\143\002\067\000\143\002\069\000\143\002\070\000\143\002\
\\071\000\143\002\072\000\143\002\074\000\143\002\075\000\143\002\
\\076\000\143\002\077\000\143\002\078\000\143\002\080\000\143\002\
\\081\000\143\002\082\000\143\002\083\000\143\002\084\000\143\002\
\\085\000\143\002\086\000\143\002\088\000\143\002\089\000\143\002\
\\090\000\143\002\091\000\143\002\092\000\143\002\094\000\143\002\
\\095\000\143\002\096\000\143\002\000\000\
\\001\000\002\000\144\002\005\000\144\002\007\000\144\002\008\000\144\002\
\\012\000\144\002\018\000\144\002\020\000\144\002\021\000\144\002\
\\022\000\144\002\035\000\144\002\036\000\144\002\037\000\144\002\
\\038\000\144\002\039\000\144\002\040\000\144\002\041\000\144\002\
\\042\000\144\002\043\000\144\002\044\000\144\002\045\000\144\002\
\\046\000\144\002\047\000\144\002\060\000\144\002\061\000\144\002\
\\062\000\144\002\063\000\144\002\064\000\144\002\065\000\144\002\
\\066\000\144\002\067\000\144\002\069\000\144\002\070\000\144\002\
\\071\000\144\002\072\000\144\002\074\000\144\002\075\000\144\002\
\\076\000\144\002\077\000\144\002\078\000\144\002\080\000\144\002\
\\081\000\144\002\082\000\144\002\083\000\144\002\084\000\144\002\
\\085\000\144\002\086\000\144\002\088\000\144\002\089\000\144\002\
\\090\000\144\002\091\000\144\002\092\000\144\002\094\000\144\002\
\\095\000\144\002\096\000\144\002\000\000\
\\001\000\002\000\145\002\005\000\145\002\007\000\145\002\008\000\145\002\
\\012\000\145\002\018\000\145\002\020\000\145\002\021\000\145\002\
\\022\000\145\002\035\000\145\002\036\000\145\002\037\000\145\002\
\\038\000\145\002\039\000\145\002\040\000\145\002\041\000\145\002\
\\042\000\145\002\043\000\145\002\044\000\145\002\045\000\145\002\
\\046\000\145\002\047\000\145\002\060\000\145\002\061\000\145\002\
\\062\000\145\002\063\000\145\002\064\000\145\002\065\000\145\002\
\\066\000\145\002\067\000\145\002\069\000\145\002\070\000\145\002\
\\071\000\145\002\072\000\145\002\074\000\145\002\075\000\145\002\
\\076\000\145\002\077\000\145\002\078\000\145\002\080\000\145\002\
\\081\000\145\002\082\000\145\002\083\000\145\002\084\000\145\002\
\\085\000\145\002\086\000\145\002\088\000\145\002\089\000\145\002\
\\090\000\145\002\091\000\145\002\092\000\145\002\094\000\145\002\
\\095\000\145\002\096\000\145\002\000\000\
\\001\000\002\000\146\002\005\000\146\002\007\000\146\002\008\000\146\002\
\\012\000\146\002\018\000\146\002\020\000\146\002\021\000\146\002\
\\022\000\146\002\035\000\146\002\036\000\146\002\037\000\146\002\
\\038\000\146\002\039\000\146\002\040\000\146\002\041\000\146\002\
\\042\000\146\002\043\000\146\002\044\000\146\002\045\000\146\002\
\\046\000\146\002\047\000\146\002\060\000\146\002\061\000\146\002\
\\062\000\146\002\063\000\146\002\064\000\146\002\065\000\146\002\
\\066\000\146\002\067\000\146\002\069\000\146\002\070\000\146\002\
\\071\000\146\002\072\000\146\002\074\000\146\002\075\000\146\002\
\\076\000\146\002\077\000\146\002\078\000\146\002\080\000\146\002\
\\081\000\146\002\082\000\146\002\083\000\146\002\084\000\146\002\
\\085\000\146\002\086\000\146\002\088\000\146\002\089\000\146\002\
\\090\000\146\002\091\000\146\002\092\000\146\002\094\000\146\002\
\\095\000\146\002\096\000\146\002\000\000\
\\001\000\002\000\147\002\005\000\147\002\007\000\147\002\008\000\147\002\
\\012\000\147\002\018\000\147\002\020\000\147\002\021\000\147\002\
\\022\000\147\002\035\000\147\002\036\000\147\002\037\000\147\002\
\\038\000\147\002\039\000\147\002\040\000\147\002\041\000\147\002\
\\042\000\147\002\043\000\147\002\044\000\147\002\045\000\147\002\
\\046\000\147\002\047\000\147\002\060\000\147\002\061\000\147\002\
\\062\000\147\002\063\000\147\002\064\000\147\002\065\000\147\002\
\\066\000\147\002\067\000\147\002\069\000\147\002\070\000\147\002\
\\071\000\147\002\072\000\147\002\074\000\147\002\075\000\147\002\
\\076\000\147\002\077\000\147\002\078\000\147\002\080\000\147\002\
\\081\000\147\002\082\000\147\002\083\000\147\002\084\000\147\002\
\\085\000\147\002\086\000\147\002\088\000\147\002\089\000\147\002\
\\090\000\147\002\091\000\147\002\092\000\147\002\094\000\147\002\
\\095\000\147\002\096\000\147\002\000\000\
\\001\000\002\000\148\002\005\000\148\002\007\000\148\002\008\000\148\002\
\\012\000\148\002\018\000\148\002\020\000\148\002\021\000\148\002\
\\022\000\148\002\035\000\148\002\036\000\148\002\037\000\148\002\
\\038\000\148\002\039\000\148\002\040\000\148\002\041\000\148\002\
\\042\000\148\002\043\000\148\002\044\000\148\002\045\000\148\002\
\\046\000\148\002\047\000\148\002\060\000\148\002\061\000\148\002\
\\062\000\148\002\063\000\148\002\064\000\148\002\065\000\148\002\
\\066\000\148\002\067\000\148\002\069\000\148\002\070\000\148\002\
\\071\000\148\002\072\000\148\002\074\000\148\002\075\000\148\002\
\\076\000\148\002\077\000\148\002\078\000\148\002\080\000\148\002\
\\081\000\148\002\082\000\148\002\083\000\148\002\084\000\148\002\
\\085\000\148\002\086\000\148\002\088\000\148\002\089\000\148\002\
\\090\000\148\002\091\000\148\002\092\000\148\002\094\000\148\002\
\\095\000\148\002\096\000\148\002\000\000\
\\001\000\002\000\149\002\005\000\149\002\007\000\149\002\008\000\149\002\
\\012\000\149\002\018\000\149\002\020\000\149\002\021\000\149\002\
\\022\000\149\002\035\000\149\002\036\000\149\002\037\000\149\002\
\\038\000\149\002\039\000\149\002\040\000\149\002\041\000\149\002\
\\042\000\149\002\043\000\149\002\044\000\149\002\045\000\149\002\
\\046\000\149\002\047\000\149\002\060\000\149\002\061\000\149\002\
\\062\000\149\002\063\000\149\002\064\000\149\002\065\000\149\002\
\\066\000\149\002\067\000\149\002\069\000\149\002\070\000\149\002\
\\071\000\149\002\072\000\149\002\074\000\149\002\075\000\149\002\
\\076\000\149\002\077\000\149\002\078\000\149\002\080\000\149\002\
\\081\000\149\002\082\000\149\002\083\000\149\002\084\000\149\002\
\\085\000\149\002\086\000\149\002\088\000\149\002\089\000\149\002\
\\090\000\149\002\091\000\149\002\092\000\149\002\094\000\149\002\
\\095\000\149\002\096\000\149\002\000\000\
\\001\000\002\000\150\002\005\000\150\002\007\000\150\002\008\000\150\002\
\\012\000\150\002\018\000\150\002\020\000\150\002\021\000\150\002\
\\022\000\150\002\035\000\150\002\036\000\150\002\037\000\150\002\
\\038\000\150\002\039\000\150\002\040\000\150\002\041\000\150\002\
\\042\000\150\002\043\000\150\002\044\000\150\002\045\000\150\002\
\\046\000\150\002\047\000\150\002\060\000\150\002\061\000\150\002\
\\062\000\150\002\063\000\150\002\064\000\150\002\065\000\150\002\
\\066\000\150\002\067\000\150\002\069\000\150\002\070\000\150\002\
\\071\000\150\002\072\000\150\002\074\000\150\002\075\000\150\002\
\\076\000\150\002\077\000\150\002\078\000\150\002\080\000\150\002\
\\081\000\150\002\082\000\150\002\083\000\150\002\084\000\150\002\
\\085\000\150\002\086\000\150\002\088\000\150\002\089\000\150\002\
\\090\000\150\002\091\000\150\002\092\000\150\002\094\000\150\002\
\\095\000\150\002\096\000\150\002\000\000\
\\001\000\002\000\168\002\005\000\168\002\007\000\168\002\012\000\168\002\
\\018\000\168\002\020\000\168\002\021\000\168\002\022\000\168\002\
\\036\000\168\002\038\000\168\002\039\000\168\002\040\000\168\002\
\\041\000\168\002\042\000\168\002\043\000\168\002\044\000\168\002\
\\047\000\168\002\069\000\168\002\071\000\168\002\084\000\168\002\
\\085\000\168\002\089\000\168\002\092\000\168\002\095\000\168\002\000\000\
\\001\000\002\000\169\002\005\000\169\002\007\000\169\002\012\000\169\002\
\\018\000\169\002\020\000\169\002\021\000\169\002\022\000\169\002\
\\036\000\169\002\038\000\169\002\039\000\169\002\040\000\169\002\
\\041\000\169\002\042\000\169\002\043\000\169\002\044\000\169\002\
\\047\000\169\002\069\000\169\002\071\000\169\002\079\000\012\001\
\\084\000\169\002\085\000\169\002\089\000\169\002\092\000\169\002\
\\095\000\169\002\000\000\
\\001\000\002\000\170\002\005\000\170\002\007\000\170\002\012\000\170\002\
\\018\000\170\002\020\000\170\002\021\000\170\002\022\000\170\002\
\\036\000\170\002\038\000\170\002\039\000\170\002\040\000\170\002\
\\041\000\170\002\042\000\170\002\043\000\170\002\044\000\170\002\
\\047\000\170\002\069\000\170\002\071\000\170\002\084\000\170\002\
\\085\000\170\002\089\000\170\002\092\000\170\002\095\000\170\002\000\000\
\\001\000\002\000\174\002\005\000\174\002\007\000\174\002\012\000\174\002\
\\018\000\174\002\020\000\174\002\021\000\174\002\022\000\174\002\
\\036\000\174\002\038\000\174\002\039\000\174\002\040\000\174\002\
\\041\000\174\002\042\000\174\002\043\000\174\002\044\000\174\002\
\\045\000\177\001\046\000\176\001\047\000\174\002\069\000\174\002\
\\071\000\174\002\084\000\174\002\085\000\174\002\089\000\174\002\
\\092\000\174\002\095\000\174\002\000\000\
\\001\000\002\000\175\002\005\000\175\002\007\000\175\002\012\000\175\002\
\\018\000\175\002\020\000\175\002\021\000\175\002\022\000\175\002\
\\036\000\175\002\038\000\175\002\039\000\175\002\040\000\175\002\
\\041\000\175\002\042\000\175\002\043\000\175\002\044\000\175\002\
\\047\000\175\002\069\000\175\002\071\000\175\002\084\000\175\002\
\\085\000\175\002\089\000\175\002\092\000\175\002\095\000\175\002\000\000\
\\001\000\002\000\176\002\005\000\176\002\007\000\176\002\012\000\176\002\
\\018\000\176\002\020\000\176\002\021\000\176\002\022\000\176\002\
\\036\000\176\002\038\000\176\002\039\000\176\002\040\000\176\002\
\\041\000\176\002\042\000\176\002\043\000\176\002\044\000\176\002\
\\045\000\176\002\046\000\176\002\047\000\176\002\069\000\176\002\
\\071\000\176\002\084\000\176\002\085\000\176\002\089\000\176\002\
\\092\000\176\002\095\000\176\002\000\000\
\\001\000\002\000\177\002\005\000\177\002\007\000\177\002\012\000\177\002\
\\018\000\177\002\020\000\177\002\021\000\177\002\022\000\177\002\
\\036\000\177\002\038\000\177\002\039\000\177\002\040\000\177\002\
\\041\000\177\002\042\000\177\002\043\000\177\002\044\000\177\002\
\\045\000\177\002\046\000\177\002\047\000\177\002\069\000\177\002\
\\071\000\177\002\084\000\177\002\085\000\177\002\089\000\177\002\
\\092\000\177\002\095\000\177\002\000\000\
\\001\000\002\000\178\002\005\000\178\002\012\000\178\002\018\000\178\002\
\\020\000\178\002\021\000\178\002\022\000\178\002\047\000\178\002\
\\069\000\178\002\071\000\178\002\092\000\178\002\000\000\
\\001\000\002\000\179\002\005\000\179\002\012\000\179\002\018\000\179\002\
\\020\000\179\002\021\000\179\002\022\000\179\002\047\000\179\002\
\\069\000\179\002\071\000\179\002\092\000\179\002\000\000\
\\001\000\002\000\225\002\003\000\225\002\004\000\225\002\006\000\225\002\
\\008\000\225\002\010\000\225\002\011\000\225\002\012\000\225\002\
\\013\000\225\002\014\000\225\002\017\000\225\002\018\000\225\002\
\\021\000\225\002\048\000\225\002\049\000\225\002\050\000\225\002\
\\051\000\225\002\052\000\225\002\053\000\225\002\054\000\225\002\
\\055\000\225\002\056\000\225\002\057\000\225\002\058\000\225\002\
\\059\000\225\002\084\000\225\002\000\000\
\\001\000\002\000\226\002\003\000\226\002\004\000\226\002\006\000\226\002\
\\008\000\226\002\010\000\226\002\011\000\226\002\012\000\226\002\
\\013\000\226\002\014\000\226\002\017\000\226\002\018\000\226\002\
\\021\000\226\002\048\000\226\002\049\000\226\002\050\000\226\002\
\\051\000\226\002\052\000\226\002\053\000\226\002\054\000\226\002\
\\055\000\226\002\056\000\226\002\057\000\226\002\058\000\226\002\
\\059\000\226\002\084\000\226\002\000\000\
\\001\000\002\000\227\002\003\000\227\002\004\000\227\002\006\000\227\002\
\\008\000\227\002\010\000\227\002\011\000\227\002\012\000\227\002\
\\013\000\227\002\014\000\227\002\017\000\227\002\018\000\227\002\
\\021\000\227\002\048\000\227\002\049\000\227\002\050\000\227\002\
\\051\000\227\002\052\000\227\002\053\000\227\002\054\000\227\002\
\\055\000\227\002\056\000\227\002\057\000\227\002\058\000\227\002\
\\059\000\227\002\084\000\227\002\000\000\
\\001\000\002\000\228\002\003\000\228\002\004\000\228\002\006\000\228\002\
\\008\000\228\002\010\000\228\002\011\000\228\002\012\000\228\002\
\\013\000\228\002\014\000\228\002\017\000\228\002\018\000\228\002\
\\021\000\228\002\048\000\228\002\049\000\228\002\050\000\228\002\
\\051\000\228\002\052\000\228\002\053\000\228\002\054\000\228\002\
\\055\000\228\002\056\000\228\002\057\000\228\002\058\000\228\002\
\\059\000\228\002\084\000\228\002\000\000\
\\001\000\002\000\229\002\003\000\229\002\004\000\229\002\006\000\229\002\
\\008\000\229\002\010\000\229\002\011\000\229\002\012\000\229\002\
\\013\000\229\002\014\000\229\002\015\000\229\002\017\000\229\002\
\\018\000\229\002\021\000\229\002\023\000\229\002\024\000\229\002\
\\025\000\229\002\026\000\229\002\027\000\229\002\028\000\229\002\
\\029\000\229\002\030\000\229\002\031\000\229\002\032\000\229\002\
\\033\000\229\002\034\000\229\002\048\000\229\002\049\000\229\002\
\\050\000\229\002\051\000\229\002\052\000\229\002\053\000\229\002\
\\054\000\229\002\055\000\229\002\056\000\229\002\057\000\229\002\
\\058\000\229\002\059\000\229\002\084\000\229\002\000\000\
\\001\000\002\000\230\002\003\000\230\002\004\000\230\002\006\000\230\002\
\\008\000\230\002\010\000\230\002\011\000\230\002\012\000\230\002\
\\013\000\230\002\014\000\230\002\015\000\230\002\017\000\230\002\
\\018\000\230\002\021\000\230\002\023\000\230\002\024\000\230\002\
\\025\000\230\002\026\000\230\002\027\000\230\002\028\000\230\002\
\\029\000\230\002\030\000\230\002\031\000\230\002\032\000\230\002\
\\033\000\230\002\034\000\230\002\048\000\230\002\049\000\230\002\
\\050\000\230\002\051\000\230\002\052\000\230\002\053\000\230\002\
\\054\000\230\002\055\000\230\002\056\000\230\002\057\000\230\002\
\\058\000\230\002\059\000\230\002\084\000\230\002\000\000\
\\001\000\002\000\231\002\003\000\231\002\004\000\231\002\005\000\191\000\
\\006\000\231\002\008\000\231\002\009\000\190\000\010\000\231\002\
\\011\000\231\002\012\000\231\002\013\000\231\002\014\000\231\002\
\\015\000\231\002\016\000\189\000\017\000\231\002\018\000\231\002\
\\021\000\231\002\023\000\231\002\024\000\231\002\025\000\231\002\
\\026\000\231\002\027\000\231\002\028\000\231\002\029\000\231\002\
\\030\000\231\002\031\000\231\002\032\000\231\002\033\000\231\002\
\\034\000\231\002\048\000\231\002\049\000\231\002\050\000\231\002\
\\051\000\231\002\052\000\231\002\053\000\231\002\054\000\231\002\
\\055\000\231\002\056\000\231\002\057\000\231\002\058\000\231\002\
\\059\000\231\002\068\000\188\000\084\000\231\002\000\000\
\\001\000\002\000\231\002\003\000\231\002\004\000\231\002\005\000\191\000\
\\009\000\190\000\012\000\231\002\014\000\231\002\015\000\252\002\
\\016\000\189\000\017\000\231\002\018\000\231\002\021\000\231\002\
\\023\000\252\002\024\000\252\002\025\000\252\002\026\000\252\002\
\\027\000\252\002\028\000\252\002\029\000\252\002\030\000\252\002\
\\031\000\252\002\032\000\252\002\033\000\252\002\034\000\252\002\
\\048\000\231\002\049\000\231\002\050\000\231\002\051\000\231\002\
\\052\000\231\002\053\000\231\002\054\000\231\002\055\000\231\002\
\\056\000\231\002\057\000\231\002\058\000\231\002\059\000\231\002\
\\068\000\188\000\000\000\
\\001\000\002\000\232\002\003\000\232\002\004\000\232\002\006\000\232\002\
\\008\000\232\002\010\000\232\002\011\000\232\002\012\000\232\002\
\\013\000\232\002\014\000\232\002\015\000\232\002\017\000\232\002\
\\018\000\232\002\021\000\232\002\023\000\232\002\024\000\232\002\
\\025\000\232\002\026\000\232\002\027\000\232\002\028\000\232\002\
\\029\000\232\002\030\000\232\002\031\000\232\002\032\000\232\002\
\\033\000\232\002\034\000\232\002\048\000\232\002\049\000\232\002\
\\050\000\232\002\051\000\232\002\052\000\232\002\053\000\232\002\
\\054\000\232\002\055\000\232\002\056\000\232\002\057\000\232\002\
\\058\000\232\002\059\000\232\002\084\000\232\002\000\000\
\\001\000\002\000\233\002\003\000\233\002\004\000\233\002\006\000\233\002\
\\008\000\233\002\010\000\233\002\011\000\233\002\012\000\233\002\
\\013\000\233\002\014\000\233\002\015\000\233\002\017\000\233\002\
\\018\000\233\002\021\000\233\002\023\000\233\002\024\000\233\002\
\\025\000\233\002\026\000\233\002\027\000\233\002\028\000\233\002\
\\029\000\233\002\030\000\233\002\031\000\233\002\032\000\233\002\
\\033\000\233\002\034\000\233\002\048\000\233\002\049\000\233\002\
\\050\000\233\002\051\000\233\002\052\000\233\002\053\000\233\002\
\\054\000\233\002\055\000\233\002\056\000\233\002\057\000\233\002\
\\058\000\233\002\059\000\233\002\084\000\233\002\000\000\
\\001\000\002\000\234\002\003\000\234\002\004\000\234\002\006\000\234\002\
\\008\000\234\002\010\000\234\002\011\000\234\002\012\000\234\002\
\\013\000\234\002\014\000\234\002\015\000\234\002\017\000\234\002\
\\018\000\234\002\021\000\234\002\023\000\234\002\024\000\234\002\
\\025\000\234\002\026\000\234\002\027\000\234\002\028\000\234\002\
\\029\000\234\002\030\000\234\002\031\000\234\002\032\000\234\002\
\\033\000\234\002\034\000\234\002\048\000\234\002\049\000\234\002\
\\050\000\234\002\051\000\234\002\052\000\234\002\053\000\234\002\
\\054\000\234\002\055\000\234\002\056\000\234\002\057\000\234\002\
\\058\000\234\002\059\000\234\002\084\000\234\002\000\000\
\\001\000\002\000\235\002\003\000\235\002\004\000\235\002\006\000\235\002\
\\008\000\235\002\010\000\235\002\011\000\235\002\012\000\235\002\
\\013\000\235\002\014\000\235\002\015\000\235\002\017\000\235\002\
\\018\000\235\002\021\000\235\002\023\000\235\002\024\000\235\002\
\\025\000\235\002\026\000\235\002\027\000\235\002\028\000\235\002\
\\029\000\235\002\030\000\235\002\031\000\235\002\032\000\235\002\
\\033\000\235\002\034\000\235\002\048\000\235\002\049\000\235\002\
\\050\000\235\002\051\000\235\002\052\000\235\002\053\000\235\002\
\\054\000\235\002\055\000\235\002\056\000\235\002\057\000\235\002\
\\058\000\235\002\059\000\235\002\084\000\235\002\000\000\
\\001\000\002\000\236\002\003\000\236\002\004\000\236\002\006\000\236\002\
\\008\000\236\002\010\000\236\002\011\000\236\002\012\000\236\002\
\\013\000\236\002\014\000\236\002\015\000\236\002\017\000\236\002\
\\018\000\236\002\021\000\236\002\023\000\236\002\024\000\236\002\
\\025\000\236\002\026\000\236\002\027\000\236\002\028\000\236\002\
\\029\000\236\002\030\000\236\002\031\000\236\002\032\000\236\002\
\\033\000\236\002\034\000\236\002\048\000\236\002\049\000\236\002\
\\050\000\236\002\051\000\236\002\052\000\236\002\053\000\236\002\
\\054\000\236\002\055\000\236\002\056\000\236\002\057\000\236\002\
\\058\000\236\002\059\000\236\002\084\000\236\002\000\000\
\\001\000\002\000\236\002\003\000\236\002\004\000\236\002\012\000\236\002\
\\014\000\236\002\015\000\253\002\017\000\236\002\018\000\236\002\
\\021\000\236\002\023\000\253\002\024\000\253\002\025\000\253\002\
\\026\000\253\002\027\000\253\002\028\000\253\002\029\000\253\002\
\\030\000\253\002\031\000\253\002\032\000\253\002\033\000\253\002\
\\034\000\253\002\048\000\236\002\049\000\236\002\050\000\236\002\
\\051\000\236\002\052\000\236\002\053\000\236\002\054\000\236\002\
\\055\000\236\002\056\000\236\002\057\000\236\002\058\000\236\002\
\\059\000\236\002\000\000\
\\001\000\002\000\237\002\003\000\237\002\004\000\237\002\006\000\237\002\
\\008\000\237\002\010\000\237\002\011\000\237\002\012\000\237\002\
\\013\000\237\002\014\000\237\002\015\000\237\002\017\000\237\002\
\\018\000\237\002\021\000\237\002\023\000\237\002\024\000\237\002\
\\025\000\237\002\026\000\237\002\027\000\237\002\028\000\237\002\
\\029\000\237\002\030\000\237\002\031\000\237\002\032\000\237\002\
\\033\000\237\002\034\000\237\002\048\000\237\002\049\000\237\002\
\\050\000\237\002\051\000\237\002\052\000\237\002\053\000\237\002\
\\054\000\237\002\055\000\237\002\056\000\237\002\057\000\237\002\
\\058\000\237\002\059\000\237\002\084\000\237\002\000\000\
\\001\000\002\000\238\002\003\000\238\002\004\000\238\002\006\000\238\002\
\\007\000\115\001\008\000\238\002\010\000\238\002\011\000\238\002\
\\012\000\238\002\013\000\238\002\014\000\238\002\015\000\238\002\
\\017\000\238\002\018\000\238\002\021\000\238\002\023\000\238\002\
\\024\000\238\002\025\000\238\002\026\000\238\002\027\000\238\002\
\\028\000\238\002\029\000\238\002\030\000\238\002\031\000\238\002\
\\032\000\238\002\033\000\238\002\034\000\238\002\048\000\238\002\
\\049\000\238\002\050\000\238\002\051\000\238\002\052\000\238\002\
\\053\000\238\002\054\000\238\002\055\000\238\002\056\000\238\002\
\\057\000\238\002\058\000\238\002\059\000\238\002\084\000\238\002\000\000\
\\001\000\002\000\239\002\003\000\239\002\004\000\239\002\005\000\239\002\
\\006\000\239\002\008\000\239\002\009\000\239\002\010\000\239\002\
\\011\000\239\002\012\000\239\002\013\000\239\002\014\000\239\002\
\\015\000\239\002\016\000\239\002\017\000\239\002\018\000\239\002\
\\021\000\239\002\023\000\239\002\024\000\239\002\025\000\239\002\
\\026\000\239\002\027\000\239\002\028\000\239\002\029\000\239\002\
\\030\000\239\002\031\000\239\002\032\000\239\002\033\000\239\002\
\\034\000\239\002\048\000\239\002\049\000\239\002\050\000\239\002\
\\051\000\239\002\052\000\239\002\053\000\239\002\054\000\239\002\
\\055\000\239\002\056\000\239\002\057\000\239\002\058\000\239\002\
\\059\000\239\002\068\000\239\002\084\000\239\002\000\000\
\\001\000\002\000\240\002\003\000\240\002\004\000\240\002\005\000\240\002\
\\006\000\240\002\008\000\240\002\009\000\240\002\010\000\240\002\
\\011\000\240\002\012\000\240\002\013\000\240\002\014\000\240\002\
\\015\000\240\002\016\000\240\002\017\000\240\002\018\000\240\002\
\\021\000\240\002\023\000\240\002\024\000\240\002\025\000\240\002\
\\026\000\240\002\027\000\240\002\028\000\240\002\029\000\240\002\
\\030\000\240\002\031\000\240\002\032\000\240\002\033\000\240\002\
\\034\000\240\002\048\000\240\002\049\000\240\002\050\000\240\002\
\\051\000\240\002\052\000\240\002\053\000\240\002\054\000\240\002\
\\055\000\240\002\056\000\240\002\057\000\240\002\058\000\240\002\
\\059\000\240\002\068\000\240\002\084\000\240\002\000\000\
\\001\000\002\000\241\002\003\000\241\002\004\000\241\002\005\000\241\002\
\\006\000\241\002\008\000\241\002\009\000\241\002\010\000\241\002\
\\011\000\241\002\012\000\241\002\013\000\241\002\014\000\241\002\
\\015\000\241\002\016\000\241\002\017\000\241\002\018\000\241\002\
\\021\000\241\002\023\000\241\002\024\000\241\002\025\000\241\002\
\\026\000\241\002\027\000\241\002\028\000\241\002\029\000\241\002\
\\030\000\241\002\031\000\241\002\032\000\241\002\033\000\241\002\
\\034\000\241\002\048\000\241\002\049\000\241\002\050\000\241\002\
\\051\000\241\002\052\000\241\002\053\000\241\002\054\000\241\002\
\\055\000\241\002\056\000\241\002\057\000\241\002\058\000\241\002\
\\059\000\241\002\068\000\241\002\084\000\241\002\000\000\
\\001\000\002\000\242\002\003\000\242\002\004\000\242\002\005\000\242\002\
\\006\000\242\002\008\000\242\002\009\000\242\002\010\000\242\002\
\\011\000\242\002\012\000\242\002\013\000\242\002\014\000\242\002\
\\015\000\242\002\016\000\242\002\017\000\242\002\018\000\242\002\
\\021\000\242\002\023\000\242\002\024\000\242\002\025\000\242\002\
\\026\000\242\002\027\000\242\002\028\000\242\002\029\000\242\002\
\\030\000\242\002\031\000\242\002\032\000\242\002\033\000\242\002\
\\034\000\242\002\048\000\242\002\049\000\242\002\050\000\242\002\
\\051\000\242\002\052\000\242\002\053\000\242\002\054\000\242\002\
\\055\000\242\002\056\000\242\002\057\000\242\002\058\000\242\002\
\\059\000\242\002\068\000\242\002\084\000\242\002\000\000\
\\001\000\002\000\243\002\003\000\243\002\004\000\243\002\005\000\243\002\
\\006\000\243\002\008\000\243\002\009\000\243\002\010\000\243\002\
\\011\000\243\002\012\000\243\002\013\000\243\002\014\000\243\002\
\\015\000\243\002\016\000\243\002\017\000\243\002\018\000\243\002\
\\021\000\243\002\023\000\243\002\024\000\243\002\025\000\243\002\
\\026\000\243\002\027\000\243\002\028\000\243\002\029\000\243\002\
\\030\000\243\002\031\000\243\002\032\000\243\002\033\000\243\002\
\\034\000\243\002\048\000\243\002\049\000\243\002\050\000\243\002\
\\051\000\243\002\052\000\243\002\053\000\243\002\054\000\243\002\
\\055\000\243\002\056\000\243\002\057\000\243\002\058\000\243\002\
\\059\000\243\002\068\000\243\002\084\000\243\002\000\000\
\\001\000\002\000\244\002\003\000\244\002\004\000\244\002\005\000\244\002\
\\006\000\244\002\008\000\244\002\009\000\244\002\010\000\244\002\
\\011\000\244\002\012\000\244\002\013\000\244\002\014\000\244\002\
\\015\000\244\002\016\000\244\002\017\000\244\002\018\000\244\002\
\\021\000\244\002\023\000\244\002\024\000\244\002\025\000\244\002\
\\026\000\244\002\027\000\244\002\028\000\244\002\029\000\244\002\
\\030\000\244\002\031\000\244\002\032\000\244\002\033\000\244\002\
\\034\000\244\002\048\000\244\002\049\000\244\002\050\000\244\002\
\\051\000\244\002\052\000\244\002\053\000\244\002\054\000\244\002\
\\055\000\244\002\056\000\244\002\057\000\244\002\058\000\244\002\
\\059\000\244\002\068\000\244\002\084\000\244\002\000\000\
\\001\000\002\000\245\002\003\000\245\002\004\000\245\002\005\000\245\002\
\\006\000\245\002\008\000\245\002\009\000\245\002\010\000\245\002\
\\011\000\245\002\012\000\245\002\013\000\245\002\014\000\245\002\
\\015\000\245\002\016\000\245\002\017\000\245\002\018\000\245\002\
\\021\000\245\002\023\000\245\002\024\000\245\002\025\000\245\002\
\\026\000\245\002\027\000\245\002\028\000\245\002\029\000\245\002\
\\030\000\245\002\031\000\245\002\032\000\245\002\033\000\245\002\
\\034\000\245\002\048\000\245\002\049\000\245\002\050\000\245\002\
\\051\000\245\002\052\000\245\002\053\000\245\002\054\000\245\002\
\\055\000\245\002\056\000\245\002\057\000\245\002\058\000\245\002\
\\059\000\245\002\068\000\245\002\084\000\245\002\000\000\
\\001\000\002\000\246\002\003\000\246\002\004\000\246\002\005\000\246\002\
\\006\000\246\002\008\000\246\002\009\000\246\002\010\000\246\002\
\\011\000\246\002\012\000\246\002\013\000\246\002\014\000\246\002\
\\015\000\246\002\016\000\246\002\017\000\246\002\018\000\246\002\
\\021\000\246\002\023\000\246\002\024\000\246\002\025\000\246\002\
\\026\000\246\002\027\000\246\002\028\000\246\002\029\000\246\002\
\\030\000\246\002\031\000\246\002\032\000\246\002\033\000\246\002\
\\034\000\246\002\048\000\246\002\049\000\246\002\050\000\246\002\
\\051\000\246\002\052\000\246\002\053\000\246\002\054\000\246\002\
\\055\000\246\002\056\000\246\002\057\000\246\002\058\000\246\002\
\\059\000\246\002\068\000\246\002\084\000\246\002\000\000\
\\001\000\002\000\247\002\003\000\247\002\004\000\247\002\005\000\247\002\
\\006\000\247\002\008\000\247\002\009\000\247\002\010\000\247\002\
\\011\000\247\002\012\000\247\002\013\000\247\002\014\000\247\002\
\\015\000\247\002\016\000\247\002\017\000\247\002\018\000\247\002\
\\021\000\247\002\023\000\247\002\024\000\247\002\025\000\247\002\
\\026\000\247\002\027\000\247\002\028\000\247\002\029\000\247\002\
\\030\000\247\002\031\000\247\002\032\000\247\002\033\000\247\002\
\\034\000\247\002\048\000\247\002\049\000\247\002\050\000\247\002\
\\051\000\247\002\052\000\247\002\053\000\247\002\054\000\247\002\
\\055\000\247\002\056\000\247\002\057\000\247\002\058\000\247\002\
\\059\000\247\002\068\000\247\002\084\000\247\002\000\000\
\\001\000\002\000\248\002\003\000\248\002\004\000\248\002\005\000\248\002\
\\006\000\248\002\008\000\248\002\009\000\248\002\010\000\248\002\
\\011\000\248\002\012\000\248\002\013\000\248\002\014\000\248\002\
\\015\000\248\002\016\000\248\002\017\000\248\002\018\000\248\002\
\\021\000\248\002\023\000\248\002\024\000\248\002\025\000\248\002\
\\026\000\248\002\027\000\248\002\028\000\248\002\029\000\248\002\
\\030\000\248\002\031\000\248\002\032\000\248\002\033\000\248\002\
\\034\000\248\002\048\000\248\002\049\000\248\002\050\000\248\002\
\\051\000\248\002\052\000\248\002\053\000\248\002\054\000\248\002\
\\055\000\248\002\056\000\248\002\057\000\248\002\058\000\248\002\
\\059\000\248\002\068\000\248\002\084\000\248\002\092\000\187\000\000\000\
\\001\000\002\000\249\002\003\000\249\002\004\000\249\002\005\000\249\002\
\\006\000\249\002\008\000\249\002\009\000\249\002\010\000\249\002\
\\011\000\249\002\012\000\249\002\013\000\249\002\014\000\249\002\
\\015\000\249\002\016\000\249\002\017\000\249\002\018\000\249\002\
\\021\000\249\002\023\000\249\002\024\000\249\002\025\000\249\002\
\\026\000\249\002\027\000\249\002\028\000\249\002\029\000\249\002\
\\030\000\249\002\031\000\249\002\032\000\249\002\033\000\249\002\
\\034\000\249\002\048\000\249\002\049\000\249\002\050\000\249\002\
\\051\000\249\002\052\000\249\002\053\000\249\002\054\000\249\002\
\\055\000\249\002\056\000\249\002\057\000\249\002\058\000\249\002\
\\059\000\249\002\068\000\249\002\084\000\249\002\092\000\249\002\000\000\
\\001\000\002\000\250\002\003\000\250\002\004\000\250\002\005\000\250\002\
\\006\000\250\002\008\000\250\002\009\000\250\002\010\000\250\002\
\\011\000\250\002\012\000\250\002\013\000\250\002\014\000\250\002\
\\015\000\250\002\016\000\250\002\017\000\250\002\018\000\250\002\
\\021\000\250\002\023\000\250\002\024\000\250\002\025\000\250\002\
\\026\000\250\002\027\000\250\002\028\000\250\002\029\000\250\002\
\\030\000\250\002\031\000\250\002\032\000\250\002\033\000\250\002\
\\034\000\250\002\048\000\250\002\049\000\250\002\050\000\250\002\
\\051\000\250\002\052\000\250\002\053\000\250\002\054\000\250\002\
\\055\000\250\002\056\000\250\002\057\000\250\002\058\000\250\002\
\\059\000\250\002\068\000\250\002\084\000\250\002\092\000\250\002\000\000\
\\001\000\002\000\251\002\003\000\251\002\004\000\251\002\005\000\251\002\
\\006\000\251\002\008\000\251\002\009\000\251\002\010\000\251\002\
\\011\000\251\002\012\000\251\002\013\000\251\002\014\000\251\002\
\\015\000\251\002\016\000\251\002\017\000\251\002\018\000\251\002\
\\021\000\251\002\023\000\251\002\024\000\251\002\025\000\251\002\
\\026\000\251\002\027\000\251\002\028\000\251\002\029\000\251\002\
\\030\000\251\002\031\000\251\002\032\000\251\002\033\000\251\002\
\\034\000\251\002\048\000\251\002\049\000\251\002\050\000\251\002\
\\051\000\251\002\052\000\251\002\053\000\251\002\054\000\251\002\
\\055\000\251\002\056\000\251\002\057\000\251\002\058\000\251\002\
\\059\000\251\002\068\000\251\002\084\000\251\002\000\000\
\\001\000\002\000\051\000\005\000\055\002\006\000\055\002\009\000\055\002\
\\011\000\055\002\069\000\055\002\076\000\028\000\077\000\027\000\
\\078\000\026\000\088\000\055\002\094\000\055\002\000\000\
\\001\000\002\000\051\000\005\000\056\002\006\000\056\002\009\000\056\002\
\\011\000\056\002\069\000\056\002\088\000\056\002\094\000\056\002\000\000\
\\001\000\002\000\051\000\005\000\050\000\012\000\049\000\069\000\048\000\000\000\
\\001\000\002\000\051\000\005\000\050\000\069\000\048\000\000\000\
\\001\000\002\000\051\000\005\000\229\000\006\000\019\002\009\000\228\000\
\\035\000\041\000\060\000\040\000\061\000\039\000\062\000\038\000\
\\063\000\037\000\064\000\036\000\065\000\035\000\066\000\034\000\
\\067\000\033\000\069\000\048\000\070\000\032\000\072\000\031\000\
\\074\000\030\000\075\000\029\000\076\000\028\000\077\000\027\000\
\\078\000\026\000\080\000\025\000\081\000\024\000\082\000\023\000\
\\083\000\022\000\086\000\021\000\088\000\020\000\091\000\019\000\
\\094\000\018\000\096\000\017\000\000\000\
\\001\000\002\000\051\000\005\000\229\000\006\000\025\002\009\000\228\000\
\\011\000\025\002\069\000\048\000\000\000\
\\001\000\002\000\051\000\005\000\061\001\006\000\019\002\009\000\228\000\
\\035\000\041\000\060\000\040\000\061\000\039\000\062\000\038\000\
\\063\000\037\000\064\000\036\000\065\000\035\000\066\000\034\000\
\\067\000\033\000\070\000\032\000\072\000\031\000\074\000\030\000\
\\075\000\029\000\076\000\028\000\077\000\027\000\078\000\026\000\
\\080\000\025\000\081\000\024\000\082\000\023\000\083\000\022\000\
\\086\000\021\000\088\000\020\000\091\000\019\000\094\000\018\000\
\\096\000\017\000\000\000\
\\001\000\002\000\051\000\005\000\061\001\006\000\107\002\009\000\228\000\000\000\
\\001\000\002\000\092\000\000\000\
\\001\000\002\000\132\000\005\000\131\000\006\000\195\002\018\000\129\000\
\\020\000\128\000\021\000\127\000\022\000\126\000\047\000\125\000\
\\069\000\124\000\071\000\123\000\092\000\122\000\000\000\
\\001\000\002\000\132\000\005\000\131\000\006\000\105\001\018\000\129\000\
\\020\000\128\000\021\000\127\000\022\000\126\000\047\000\125\000\
\\069\000\124\000\071\000\123\000\092\000\122\000\000\000\
\\001\000\002\000\132\000\005\000\131\000\007\000\141\000\008\000\109\002\
\\009\000\237\000\016\000\236\000\018\000\129\000\020\000\128\000\
\\021\000\127\000\022\000\126\000\047\000\125\000\069\000\124\000\
\\071\000\123\000\092\000\122\000\000\000\
\\001\000\002\000\132\000\005\000\131\000\007\000\141\000\009\000\237\000\
\\016\000\236\000\018\000\129\000\020\000\128\000\021\000\127\000\
\\022\000\126\000\047\000\125\000\069\000\124\000\071\000\123\000\
\\092\000\122\000\000\000\
\\001\000\002\000\132\000\005\000\131\000\007\000\141\000\018\000\129\000\
\\020\000\128\000\021\000\127\000\022\000\126\000\047\000\125\000\
\\069\000\124\000\071\000\123\000\092\000\122\000\000\000\
\\001\000\002\000\132\000\005\000\131\000\007\000\115\001\018\000\129\000\
\\020\000\128\000\021\000\127\000\022\000\126\000\047\000\125\000\
\\069\000\124\000\071\000\123\000\092\000\122\000\000\000\
\\001\000\002\000\132\000\005\000\131\000\010\000\130\000\018\000\129\000\
\\020\000\128\000\021\000\127\000\022\000\126\000\047\000\125\000\
\\069\000\124\000\071\000\123\000\092\000\122\000\000\000\
\\001\000\002\000\132\000\005\000\131\000\010\000\069\001\018\000\129\000\
\\020\000\128\000\021\000\127\000\022\000\126\000\047\000\125\000\
\\069\000\124\000\071\000\123\000\092\000\122\000\000\000\
\\001\000\002\000\132\000\005\000\131\000\012\000\185\002\018\000\129\000\
\\020\000\128\000\021\000\127\000\022\000\126\000\047\000\125\000\
\\069\000\124\000\071\000\123\000\092\000\122\000\000\000\
\\001\000\002\000\132\000\005\000\131\000\012\000\009\001\018\000\129\000\
\\020\000\128\000\021\000\127\000\022\000\126\000\047\000\125\000\
\\069\000\124\000\071\000\123\000\092\000\122\000\000\000\
\\001\000\002\000\132\000\005\000\131\000\018\000\129\000\020\000\128\000\
\\021\000\127\000\022\000\126\000\035\000\041\000\047\000\125\000\
\\060\000\040\000\061\000\039\000\062\000\038\000\063\000\037\000\
\\064\000\036\000\065\000\035\000\066\000\034\000\067\000\033\000\
\\069\000\124\000\070\000\032\000\071\000\123\000\072\000\031\000\
\\076\000\028\000\077\000\027\000\078\000\026\000\092\000\122\000\000\000\
\\001\000\002\000\132\000\005\000\131\000\018\000\129\000\020\000\128\000\
\\021\000\127\000\022\000\126\000\047\000\125\000\069\000\124\000\
\\071\000\123\000\092\000\122\000\000\000\
\\001\000\002\000\132\000\005\000\213\000\018\000\129\000\020\000\128\000\
\\021\000\127\000\022\000\126\000\047\000\125\000\069\000\124\000\
\\071\000\123\000\092\000\122\000\000\000\
\\001\000\002\000\164\000\005\000\131\000\007\000\082\000\008\000\027\002\
\\012\000\163\000\018\000\129\000\020\000\128\000\021\000\127\000\
\\022\000\126\000\035\000\041\000\036\000\162\000\038\000\161\000\
\\039\000\160\000\040\000\159\000\041\000\158\000\042\000\157\000\
\\043\000\156\000\044\000\155\000\045\000\027\002\046\000\027\002\
\\047\000\125\000\060\000\040\000\061\000\039\000\062\000\038\000\
\\063\000\037\000\064\000\036\000\065\000\035\000\066\000\034\000\
\\067\000\033\000\069\000\124\000\070\000\032\000\071\000\123\000\
\\072\000\031\000\074\000\030\000\075\000\029\000\076\000\028\000\
\\077\000\027\000\078\000\026\000\080\000\025\000\081\000\024\000\
\\082\000\023\000\083\000\022\000\084\000\154\000\085\000\153\000\
\\086\000\021\000\088\000\020\000\089\000\152\000\091\000\019\000\
\\092\000\122\000\094\000\018\000\095\000\151\000\096\000\017\000\000\000\
\\001\000\002\000\164\000\005\000\131\000\007\000\082\000\008\000\027\002\
\\012\000\163\000\018\000\129\000\020\000\128\000\021\000\127\000\
\\022\000\126\000\035\000\041\000\036\000\162\000\038\000\161\000\
\\039\000\160\000\040\000\159\000\041\000\158\000\042\000\157\000\
\\043\000\156\000\044\000\155\000\047\000\125\000\060\000\040\000\
\\061\000\039\000\062\000\038\000\063\000\037\000\064\000\036\000\
\\065\000\035\000\066\000\034\000\067\000\033\000\069\000\124\000\
\\070\000\032\000\071\000\123\000\072\000\031\000\074\000\030\000\
\\075\000\029\000\076\000\028\000\077\000\027\000\078\000\026\000\
\\080\000\025\000\081\000\024\000\082\000\023\000\083\000\022\000\
\\084\000\154\000\085\000\153\000\086\000\021\000\088\000\020\000\
\\089\000\152\000\091\000\019\000\092\000\122\000\094\000\018\000\
\\095\000\151\000\096\000\017\000\000\000\
\\001\000\002\000\164\000\005\000\131\000\007\000\082\000\012\000\163\000\
\\018\000\129\000\020\000\128\000\021\000\127\000\022\000\126\000\
\\036\000\162\000\038\000\161\000\039\000\160\000\040\000\159\000\
\\041\000\158\000\042\000\157\000\043\000\156\000\044\000\155\000\
\\047\000\125\000\069\000\124\000\071\000\123\000\084\000\154\000\
\\085\000\153\000\089\000\152\000\090\000\031\002\092\000\122\000\
\\095\000\151\000\000\000\
\\001\000\002\000\164\000\005\000\131\000\007\000\082\000\012\000\163\000\
\\018\000\129\000\020\000\128\000\021\000\127\000\022\000\126\000\
\\036\000\162\000\038\000\161\000\039\000\160\000\040\000\159\000\
\\041\000\158\000\042\000\157\000\043\000\156\000\044\000\155\000\
\\047\000\125\000\069\000\124\000\071\000\123\000\084\000\154\000\
\\085\000\153\000\089\000\152\000\090\000\033\002\092\000\122\000\
\\095\000\151\000\000\000\
\\001\000\002\000\164\000\005\000\131\000\007\000\082\000\012\000\163\000\
\\018\000\129\000\020\000\128\000\021\000\127\000\022\000\126\000\
\\036\000\162\000\038\000\161\000\039\000\160\000\040\000\159\000\
\\041\000\158\000\042\000\157\000\043\000\156\000\044\000\155\000\
\\047\000\125\000\069\000\124\000\071\000\123\000\084\000\154\000\
\\085\000\153\000\089\000\152\000\092\000\122\000\095\000\151\000\000\000\
\\001\000\002\000\194\000\003\000\193\000\004\000\192\000\006\000\222\002\
\\008\000\222\002\010\000\222\002\011\000\222\002\012\000\222\002\
\\013\000\222\002\014\000\222\002\017\000\222\002\018\000\222\002\
\\021\000\222\002\048\000\222\002\049\000\222\002\050\000\222\002\
\\051\000\222\002\052\000\222\002\053\000\222\002\054\000\222\002\
\\055\000\222\002\056\000\222\002\057\000\222\002\058\000\222\002\
\\059\000\222\002\084\000\222\002\000\000\
\\001\000\002\000\194\000\003\000\193\000\004\000\192\000\006\000\223\002\
\\008\000\223\002\010\000\223\002\011\000\223\002\012\000\223\002\
\\013\000\223\002\014\000\223\002\017\000\223\002\018\000\223\002\
\\021\000\223\002\048\000\223\002\049\000\223\002\050\000\223\002\
\\051\000\223\002\052\000\223\002\053\000\223\002\054\000\223\002\
\\055\000\223\002\056\000\223\002\057\000\223\002\058\000\223\002\
\\059\000\223\002\084\000\223\002\000\000\
\\001\000\002\000\194\000\003\000\193\000\004\000\192\000\006\000\224\002\
\\008\000\224\002\010\000\224\002\011\000\224\002\012\000\224\002\
\\013\000\224\002\014\000\224\002\017\000\224\002\018\000\224\002\
\\021\000\224\002\048\000\224\002\049\000\224\002\050\000\224\002\
\\051\000\224\002\052\000\224\002\053\000\224\002\054\000\224\002\
\\055\000\224\002\056\000\224\002\057\000\224\002\058\000\224\002\
\\059\000\224\002\084\000\224\002\000\000\
\\001\000\002\000\095\001\005\000\094\001\006\000\187\002\069\000\124\000\
\\071\000\123\000\092\000\122\000\000\000\
\\001\000\002\000\095\001\005\000\094\001\012\000\180\002\035\000\041\000\
\\060\000\040\000\061\000\039\000\062\000\038\000\063\000\037\000\
\\064\000\036\000\065\000\035\000\066\000\034\000\067\000\033\000\
\\069\000\124\000\070\000\032\000\071\000\123\000\072\000\031\000\
\\074\000\030\000\075\000\029\000\076\000\028\000\077\000\027\000\
\\078\000\026\000\080\000\025\000\081\000\024\000\082\000\023\000\
\\083\000\022\000\086\000\021\000\088\000\020\000\091\000\019\000\
\\092\000\122\000\094\000\018\000\096\000\017\000\000\000\
\\001\000\002\000\095\001\005\000\094\001\069\000\124\000\071\000\123\000\
\\092\000\122\000\000\000\
\\001\000\005\000\057\002\006\000\057\002\009\000\057\002\011\000\057\002\
\\069\000\057\002\088\000\057\002\094\000\057\002\000\000\
\\001\000\005\000\058\002\006\000\058\002\009\000\058\002\011\000\058\002\
\\069\000\058\002\088\000\058\002\094\000\058\002\000\000\
\\001\000\005\000\062\002\006\000\062\002\007\000\062\002\009\000\062\002\
\\011\000\062\002\012\000\062\002\013\000\062\002\015\000\062\002\
\\088\000\062\002\094\000\062\002\095\000\062\002\000\000\
\\001\000\005\000\063\002\006\000\063\002\007\000\063\002\009\000\063\002\
\\011\000\063\002\012\000\063\002\013\000\063\002\015\000\063\002\
\\087\000\063\001\088\000\063\002\094\000\063\002\095\000\063\002\000\000\
\\001\000\005\000\064\002\006\000\064\002\007\000\064\002\009\000\064\002\
\\011\000\064\002\012\000\064\002\013\000\064\002\015\000\064\002\
\\088\000\064\002\094\000\064\002\095\000\064\002\000\000\
\\001\000\005\000\065\002\006\000\065\002\007\000\065\002\009\000\065\002\
\\011\000\065\002\012\000\065\002\013\000\065\002\015\000\065\002\
\\088\000\065\002\094\000\065\002\095\000\065\002\000\000\
\\001\000\005\000\066\002\006\000\066\002\007\000\066\002\009\000\066\002\
\\011\000\066\002\012\000\066\002\013\000\066\002\015\000\066\002\
\\088\000\066\002\094\000\066\002\095\000\066\002\000\000\
\\001\000\005\000\067\002\006\000\067\002\007\000\067\002\009\000\067\002\
\\011\000\067\002\012\000\067\002\013\000\067\002\015\000\067\002\
\\088\000\067\002\094\000\067\002\095\000\067\002\000\000\
\\001\000\005\000\068\002\006\000\068\002\007\000\068\002\009\000\068\002\
\\011\000\068\002\012\000\068\002\013\000\068\002\015\000\068\002\
\\088\000\068\002\094\000\068\002\095\000\068\002\000\000\
\\001\000\005\000\069\002\006\000\069\002\007\000\069\002\009\000\069\002\
\\011\000\069\002\012\000\069\002\013\000\069\002\015\000\069\002\
\\088\000\069\002\094\000\069\002\095\000\069\002\000\000\
\\001\000\005\000\070\002\006\000\070\002\007\000\070\002\009\000\070\002\
\\011\000\070\002\012\000\070\002\013\000\070\002\015\000\070\002\
\\088\000\070\002\094\000\070\002\095\000\070\002\000\000\
\\001\000\005\000\071\002\006\000\071\002\007\000\071\002\009\000\071\002\
\\011\000\071\002\012\000\071\002\013\000\071\002\015\000\071\002\
\\088\000\071\002\094\000\071\002\095\000\071\002\000\000\
\\001\000\005\000\100\002\006\000\100\002\009\000\100\002\011\000\100\002\000\000\
\\001\000\005\000\101\002\006\000\101\002\009\000\101\002\011\000\101\002\000\000\
\\001\000\005\000\102\002\006\000\102\002\009\000\102\002\011\000\102\002\000\000\
\\001\000\005\000\103\002\006\000\103\002\009\000\103\002\011\000\103\002\000\000\
\\001\000\005\000\104\002\006\000\104\002\009\000\104\002\011\000\104\002\000\000\
\\001\000\005\000\105\002\006\000\105\002\009\000\105\002\011\000\105\002\000\000\
\\001\000\005\000\151\002\077\000\000\001\000\000\
\\001\000\005\000\152\002\000\000\
\\001\000\005\000\050\000\069\000\048\000\000\000\
\\001\000\005\000\050\000\069\000\048\000\088\000\020\000\094\000\018\000\000\000\
\\001\000\005\000\058\000\000\000\
\\001\000\005\000\077\000\006\000\059\002\007\000\059\002\009\000\076\000\
\\011\000\059\002\012\000\059\002\013\000\059\002\015\000\059\002\
\\088\000\020\000\094\000\018\000\095\000\075\000\000\000\
\\001\000\005\000\077\000\006\000\060\002\007\000\060\002\009\000\076\000\
\\011\000\060\002\012\000\060\002\013\000\060\002\015\000\060\002\
\\088\000\020\000\094\000\018\000\095\000\075\000\000\000\
\\001\000\005\000\077\000\006\000\061\002\007\000\061\002\009\000\076\000\
\\011\000\061\002\012\000\061\002\013\000\061\002\015\000\061\002\
\\088\000\020\000\094\000\018\000\095\000\075\000\000\000\
\\001\000\005\000\089\000\000\000\
\\001\000\005\000\104\000\000\000\
\\001\000\005\000\191\000\009\000\190\000\015\000\252\002\016\000\189\000\
\\023\000\252\002\024\000\252\002\025\000\252\002\026\000\252\002\
\\027\000\252\002\028\000\252\002\029\000\252\002\030\000\252\002\
\\031\000\252\002\032\000\252\002\033\000\252\002\034\000\252\002\
\\068\000\188\000\000\000\
\\001\000\005\000\229\000\006\000\097\002\009\000\228\000\011\000\097\002\
\\069\000\048\000\088\000\020\000\094\000\018\000\000\000\
\\001\000\005\000\004\001\000\000\
\\001\000\005\000\005\001\000\000\
\\001\000\005\000\013\001\000\000\
\\001\000\005\000\014\001\000\000\
\\001\000\005\000\018\001\006\000\247\001\011\000\247\001\000\000\
\\001\000\005\000\061\001\006\000\097\002\009\000\228\000\000\000\
\\001\000\005\000\066\001\006\000\098\002\009\000\065\001\011\000\098\002\000\000\
\\001\000\005\000\066\001\006\000\099\002\009\000\065\001\011\000\099\002\000\000\
\\001\000\005\000\082\001\000\000\
\\001\000\005\000\160\001\000\000\
\\001\000\005\000\188\001\092\000\187\000\000\000\
\\001\000\005\000\224\001\092\000\187\000\000\000\
\\001\000\006\000\244\001\069\000\171\000\000\000\
\\001\000\006\000\245\001\011\000\017\001\000\000\
\\001\000\006\000\246\001\000\000\
\\001\000\006\000\248\001\011\000\248\001\000\000\
\\001\000\006\000\249\001\011\000\249\001\000\000\
\\001\000\006\000\250\001\011\000\143\001\000\000\
\\001\000\006\000\251\001\000\000\
\\001\000\006\000\019\002\035\000\041\000\060\000\040\000\061\000\039\000\
\\062\000\038\000\063\000\037\000\064\000\036\000\065\000\035\000\
\\066\000\034\000\067\000\033\000\070\000\032\000\072\000\031\000\
\\074\000\030\000\075\000\029\000\076\000\028\000\077\000\027\000\
\\078\000\026\000\080\000\025\000\081\000\024\000\082\000\023\000\
\\083\000\022\000\086\000\021\000\088\000\020\000\091\000\019\000\
\\094\000\018\000\096\000\017\000\000\000\
\\001\000\006\000\020\002\000\000\
\\001\000\006\000\021\002\011\000\223\000\000\000\
\\001\000\006\000\022\002\000\000\
\\001\000\006\000\023\002\011\000\023\002\000\000\
\\001\000\006\000\024\002\011\000\024\002\000\000\
\\001\000\006\000\106\002\000\000\
\\001\000\006\000\153\002\000\000\
\\001\000\006\000\154\002\013\000\151\001\092\000\187\000\000\000\
\\001\000\006\000\155\002\000\000\
\\001\000\006\000\156\002\013\000\186\001\000\000\
\\001\000\006\000\157\002\000\000\
\\001\000\006\000\158\002\013\000\217\001\000\000\
\\001\000\006\000\159\002\000\000\
\\001\000\006\000\160\002\011\000\225\001\092\000\187\000\000\000\
\\001\000\006\000\161\002\000\000\
\\001\000\006\000\162\002\009\000\169\001\013\000\162\002\092\000\122\000\000\000\
\\001\000\006\000\163\002\013\000\163\002\000\000\
\\001\000\006\000\164\002\011\000\187\001\013\000\164\002\000\000\
\\001\000\006\000\165\002\013\000\165\002\000\000\
\\001\000\006\000\166\002\011\000\166\002\013\000\166\002\000\000\
\\001\000\006\000\167\002\011\000\167\002\013\000\167\002\000\000\
\\001\000\006\000\188\002\000\000\
\\001\000\006\000\189\002\011\000\201\001\084\000\200\001\000\000\
\\001\000\006\000\190\002\000\000\
\\001\000\006\000\191\002\000\000\
\\001\000\006\000\192\002\011\000\192\002\084\000\192\002\000\000\
\\001\000\006\000\193\002\011\000\193\002\084\000\193\002\000\000\
\\001\000\006\000\194\002\011\000\194\002\084\000\194\002\000\000\
\\001\000\006\000\196\002\000\000\
\\001\000\006\000\197\002\011\000\111\001\000\000\
\\001\000\006\000\198\002\000\000\
\\001\000\006\000\199\002\008\000\199\002\010\000\199\002\011\000\199\002\
\\012\000\199\002\013\000\199\002\014\000\209\000\048\000\208\000\
\\084\000\199\002\000\000\
\\001\000\006\000\200\002\008\000\200\002\010\000\200\002\011\000\200\002\
\\012\000\200\002\013\000\200\002\084\000\200\002\000\000\
\\001\000\006\000\201\002\008\000\201\002\010\000\201\002\011\000\201\002\
\\012\000\201\002\013\000\201\002\014\000\201\002\048\000\201\002\
\\049\000\210\000\084\000\201\002\000\000\
\\001\000\006\000\202\002\008\000\202\002\010\000\202\002\011\000\202\002\
\\012\000\202\002\013\000\202\002\014\000\202\002\048\000\202\002\
\\049\000\210\000\084\000\202\002\000\000\
\\001\000\006\000\203\002\008\000\203\002\010\000\203\002\011\000\203\002\
\\012\000\203\002\013\000\203\002\014\000\203\002\048\000\203\002\
\\049\000\203\002\050\000\207\000\084\000\203\002\000\000\
\\001\000\006\000\204\002\008\000\204\002\010\000\204\002\011\000\204\002\
\\012\000\204\002\013\000\204\002\014\000\204\002\048\000\204\002\
\\049\000\204\002\050\000\207\000\084\000\204\002\000\000\
\\001\000\006\000\205\002\008\000\205\002\010\000\205\002\011\000\205\002\
\\012\000\205\002\013\000\205\002\014\000\205\002\048\000\205\002\
\\049\000\205\002\050\000\205\002\051\000\206\000\084\000\205\002\000\000\
\\001\000\006\000\206\002\008\000\206\002\010\000\206\002\011\000\206\002\
\\012\000\206\002\013\000\206\002\014\000\206\002\048\000\206\002\
\\049\000\206\002\050\000\206\002\051\000\206\000\084\000\206\002\000\000\
\\001\000\006\000\207\002\008\000\207\002\010\000\207\002\011\000\207\002\
\\012\000\207\002\013\000\207\002\014\000\207\002\021\000\205\000\
\\048\000\207\002\049\000\207\002\050\000\207\002\051\000\207\002\
\\084\000\207\002\000\000\
\\001\000\006\000\208\002\008\000\208\002\010\000\208\002\011\000\208\002\
\\012\000\208\002\013\000\208\002\014\000\208\002\021\000\205\000\
\\048\000\208\002\049\000\208\002\050\000\208\002\051\000\208\002\
\\084\000\208\002\000\000\
\\001\000\006\000\209\002\008\000\209\002\010\000\209\002\011\000\209\002\
\\012\000\209\002\013\000\209\002\014\000\209\002\021\000\209\002\
\\048\000\209\002\049\000\209\002\050\000\209\002\051\000\209\002\
\\052\000\204\000\053\000\203\000\084\000\209\002\000\000\
\\001\000\006\000\210\002\008\000\210\002\010\000\210\002\011\000\210\002\
\\012\000\210\002\013\000\210\002\014\000\210\002\021\000\210\002\
\\048\000\210\002\049\000\210\002\050\000\210\002\051\000\210\002\
\\052\000\204\000\053\000\203\000\084\000\210\002\000\000\
\\001\000\006\000\211\002\008\000\211\002\010\000\211\002\011\000\211\002\
\\012\000\211\002\013\000\211\002\014\000\211\002\021\000\211\002\
\\048\000\211\002\049\000\211\002\050\000\211\002\051\000\211\002\
\\052\000\211\002\053\000\211\002\054\000\202\000\055\000\201\000\
\\056\000\200\000\057\000\199\000\084\000\211\002\000\000\
\\001\000\006\000\212\002\008\000\212\002\010\000\212\002\011\000\212\002\
\\012\000\212\002\013\000\212\002\014\000\212\002\021\000\212\002\
\\048\000\212\002\049\000\212\002\050\000\212\002\051\000\212\002\
\\052\000\212\002\053\000\212\002\054\000\202\000\055\000\201\000\
\\056\000\200\000\057\000\199\000\084\000\212\002\000\000\
\\001\000\006\000\213\002\008\000\213\002\010\000\213\002\011\000\213\002\
\\012\000\213\002\013\000\213\002\014\000\213\002\021\000\213\002\
\\048\000\213\002\049\000\213\002\050\000\213\002\051\000\213\002\
\\052\000\213\002\053\000\213\002\054\000\202\000\055\000\201\000\
\\056\000\200\000\057\000\199\000\084\000\213\002\000\000\
\\001\000\006\000\214\002\008\000\214\002\010\000\214\002\011\000\214\002\
\\012\000\214\002\013\000\214\002\014\000\214\002\021\000\214\002\
\\048\000\214\002\049\000\214\002\050\000\214\002\051\000\214\002\
\\052\000\214\002\053\000\214\002\054\000\214\002\055\000\214\002\
\\056\000\214\002\057\000\214\002\058\000\196\000\059\000\195\000\
\\084\000\214\002\000\000\
\\001\000\006\000\215\002\008\000\215\002\010\000\215\002\011\000\215\002\
\\012\000\215\002\013\000\215\002\014\000\215\002\021\000\215\002\
\\048\000\215\002\049\000\215\002\050\000\215\002\051\000\215\002\
\\052\000\215\002\053\000\215\002\054\000\215\002\055\000\215\002\
\\056\000\215\002\057\000\215\002\058\000\196\000\059\000\195\000\
\\084\000\215\002\000\000\
\\001\000\006\000\216\002\008\000\216\002\010\000\216\002\011\000\216\002\
\\012\000\216\002\013\000\216\002\014\000\216\002\021\000\216\002\
\\048\000\216\002\049\000\216\002\050\000\216\002\051\000\216\002\
\\052\000\216\002\053\000\216\002\054\000\216\002\055\000\216\002\
\\056\000\216\002\057\000\216\002\058\000\196\000\059\000\195\000\
\\084\000\216\002\000\000\
\\001\000\006\000\217\002\008\000\217\002\010\000\217\002\011\000\217\002\
\\012\000\217\002\013\000\217\002\014\000\217\002\021\000\217\002\
\\048\000\217\002\049\000\217\002\050\000\217\002\051\000\217\002\
\\052\000\217\002\053\000\217\002\054\000\217\002\055\000\217\002\
\\056\000\217\002\057\000\217\002\058\000\196\000\059\000\195\000\
\\084\000\217\002\000\000\
\\001\000\006\000\218\002\008\000\218\002\010\000\218\002\011\000\218\002\
\\012\000\218\002\013\000\218\002\014\000\218\002\021\000\218\002\
\\048\000\218\002\049\000\218\002\050\000\218\002\051\000\218\002\
\\052\000\218\002\053\000\218\002\054\000\218\002\055\000\218\002\
\\056\000\218\002\057\000\218\002\058\000\196\000\059\000\195\000\
\\084\000\218\002\000\000\
\\001\000\006\000\219\002\008\000\219\002\010\000\219\002\011\000\219\002\
\\012\000\219\002\013\000\219\002\014\000\219\002\017\000\198\000\
\\018\000\197\000\021\000\219\002\048\000\219\002\049\000\219\002\
\\050\000\219\002\051\000\219\002\052\000\219\002\053\000\219\002\
\\054\000\219\002\055\000\219\002\056\000\219\002\057\000\219\002\
\\058\000\219\002\059\000\219\002\084\000\219\002\000\000\
\\001\000\006\000\220\002\008\000\220\002\010\000\220\002\011\000\220\002\
\\012\000\220\002\013\000\220\002\014\000\220\002\017\000\198\000\
\\018\000\197\000\021\000\220\002\048\000\220\002\049\000\220\002\
\\050\000\220\002\051\000\220\002\052\000\220\002\053\000\220\002\
\\054\000\220\002\055\000\220\002\056\000\220\002\057\000\220\002\
\\058\000\220\002\059\000\220\002\084\000\220\002\000\000\
\\001\000\006\000\221\002\008\000\221\002\010\000\221\002\011\000\221\002\
\\012\000\221\002\013\000\221\002\014\000\221\002\017\000\198\000\
\\018\000\197\000\021\000\221\002\048\000\221\002\049\000\221\002\
\\050\000\221\002\051\000\221\002\052\000\221\002\053\000\221\002\
\\054\000\221\002\055\000\221\002\056\000\221\002\057\000\221\002\
\\058\000\221\002\059\000\221\002\084\000\221\002\000\000\
\\001\000\006\000\166\000\000\000\
\\001\000\006\000\222\000\000\000\
\\001\000\006\000\016\001\000\000\
\\001\000\006\000\030\001\092\000\187\000\000\000\
\\001\000\006\000\057\001\000\000\
\\001\000\006\000\058\001\000\000\
\\001\000\006\000\101\001\000\000\
\\001\000\006\000\110\001\000\000\
\\001\000\006\000\113\001\000\000\
\\001\000\006\000\120\001\000\000\
\\001\000\006\000\121\001\000\000\
\\001\000\006\000\130\001\000\000\
\\001\000\006\000\140\001\000\000\
\\001\000\006\000\141\001\000\000\
\\001\000\006\000\142\001\000\000\
\\001\000\006\000\149\001\000\000\
\\001\000\006\000\152\001\000\000\
\\001\000\006\000\159\001\000\000\
\\001\000\006\000\202\001\000\000\
\\001\000\006\000\203\001\000\000\
\\001\000\006\000\218\001\000\000\
\\001\000\006\000\228\001\000\000\
\\001\000\007\000\070\000\069\000\069\000\070\000\068\000\000\000\
\\001\000\007\000\072\000\069\000\069\000\070\000\068\000\000\000\
\\001\000\007\000\082\000\011\000\053\002\012\000\053\002\015\000\081\000\000\000\
\\001\000\007\000\115\001\000\000\
\\001\000\007\000\155\001\000\000\
\\001\000\008\000\028\002\045\000\028\002\046\000\028\002\000\000\
\\001\000\008\000\035\002\035\000\041\000\060\000\040\000\061\000\039\000\
\\062\000\038\000\063\000\037\000\064\000\036\000\065\000\035\000\
\\066\000\034\000\067\000\033\000\070\000\032\000\072\000\031\000\
\\076\000\028\000\077\000\027\000\078\000\026\000\000\000\
\\001\000\008\000\036\002\000\000\
\\001\000\008\000\046\002\035\000\046\002\060\000\046\002\061\000\046\002\
\\062\000\046\002\063\000\046\002\064\000\046\002\065\000\046\002\
\\066\000\046\002\067\000\046\002\070\000\046\002\072\000\046\002\
\\076\000\046\002\077\000\046\002\078\000\046\002\000\000\
\\001\000\008\000\093\002\011\000\093\002\000\000\
\\001\000\008\000\094\002\011\000\094\002\000\000\
\\001\000\008\000\095\002\011\000\095\002\015\000\185\000\000\000\
\\001\000\008\000\096\002\011\000\096\002\000\000\
\\001\000\008\000\108\002\011\000\075\001\000\000\
\\001\000\008\000\110\002\000\000\
\\001\000\008\000\111\002\011\000\111\002\000\000\
\\001\000\008\000\112\002\011\000\112\002\000\000\
\\001\000\008\000\118\002\011\000\118\002\012\000\118\002\000\000\
\\001\000\008\000\119\002\011\000\119\002\012\000\119\002\000\000\
\\001\000\008\000\171\002\045\000\177\001\046\000\176\001\000\000\
\\001\000\008\000\172\002\000\000\
\\001\000\008\000\173\002\045\000\173\002\046\000\173\002\000\000\
\\001\000\008\000\177\000\000\000\
\\001\000\008\000\184\000\011\000\183\000\000\000\
\\001\000\008\000\254\000\000\000\
\\001\000\008\000\021\001\000\000\
\\001\000\008\000\026\001\011\000\025\001\000\000\
\\001\000\008\000\028\001\069\000\103\000\000\000\
\\001\000\008\000\076\001\000\000\
\\001\000\008\000\108\001\069\000\103\000\000\000\
\\001\000\008\000\164\001\000\000\
\\001\000\008\000\194\001\000\000\
\\001\000\009\000\116\002\015\000\116\002\016\000\116\002\000\000\
\\001\000\009\000\117\002\015\000\117\002\016\000\117\002\000\000\
\\001\000\009\000\062\000\069\000\061\000\082\000\005\002\083\000\005\002\
\\086\000\005\002\091\000\005\002\093\000\005\002\000\000\
\\001\000\009\000\062\000\069\000\061\000\093\000\005\002\000\000\
\\001\000\009\000\237\000\015\000\114\002\016\000\236\000\000\000\
\\001\000\009\000\169\001\092\000\122\000\000\000\
\\001\000\010\000\172\000\000\000\
\\001\000\010\000\211\000\000\000\
\\001\000\010\000\109\001\000\000\
\\001\000\010\000\119\001\000\000\
\\001\000\010\000\123\001\000\000\
\\001\000\010\000\148\001\000\000\
\\001\000\010\000\208\001\000\000\
\\001\000\011\000\049\002\012\000\049\002\013\000\024\001\000\000\
\\001\000\011\000\050\002\012\000\050\002\000\000\
\\001\000\011\000\053\002\012\000\053\002\015\000\081\000\000\000\
\\001\000\011\000\054\002\012\000\054\002\000\000\
\\001\000\011\000\184\002\012\000\184\002\000\000\
\\001\000\011\000\079\000\012\000\051\002\000\000\
\\001\000\011\000\023\001\012\000\047\002\000\000\
\\001\000\011\000\132\001\012\000\182\002\000\000\
\\001\000\012\000\048\002\000\000\
\\001\000\012\000\052\002\000\000\
\\001\000\012\000\181\002\000\000\
\\001\000\012\000\183\002\000\000\
\\001\000\012\000\186\002\000\000\
\\001\000\012\000\078\000\000\000\
\\001\000\012\000\238\000\000\000\
\\001\000\012\000\006\001\000\000\
\\001\000\012\000\007\001\000\000\
\\001\000\012\000\022\001\000\000\
\\001\000\012\000\080\001\000\000\
\\001\000\012\000\081\001\000\000\
\\001\000\012\000\096\001\000\000\
\\001\000\012\000\124\001\000\000\
\\001\000\012\000\133\001\000\000\
\\001\000\012\000\158\001\000\000\
\\001\000\012\000\170\001\000\000\
\\001\000\012\000\215\001\000\000\
\\001\000\013\000\093\000\000\000\
\\001\000\013\000\112\001\000\000\
\\001\000\013\000\195\001\000\000\
\\001\000\013\000\210\001\000\000\
\\001\000\015\000\115\002\000\000\
\\001\000\015\000\253\002\023\000\253\002\024\000\253\002\025\000\253\002\
\\026\000\253\002\027\000\253\002\028\000\253\002\029\000\253\002\
\\030\000\253\002\031\000\253\002\032\000\253\002\033\000\253\002\
\\034\000\253\002\000\000\
\\001\000\015\000\252\000\023\000\251\000\024\000\250\000\025\000\249\000\
\\026\000\248\000\027\000\247\000\028\000\246\000\029\000\245\000\
\\030\000\244\000\031\000\243\000\032\000\242\000\033\000\241\000\
\\034\000\240\000\000\000\
\\001\000\015\000\252\000\023\000\199\001\024\000\198\001\025\000\249\000\
\\026\000\248\000\027\000\247\000\028\000\246\000\029\000\245\000\
\\030\000\244\000\031\000\243\000\032\000\242\000\033\000\241\000\
\\034\000\240\000\000\000\
\\001\000\015\000\073\001\000\000\
\\001\000\015\000\131\001\000\000\
\\001\000\035\000\041\000\060\000\040\000\061\000\039\000\062\000\038\000\
\\063\000\037\000\064\000\036\000\065\000\035\000\066\000\034\000\
\\067\000\033\000\070\000\032\000\072\000\031\000\074\000\030\000\
\\075\000\029\000\076\000\028\000\077\000\027\000\078\000\026\000\
\\080\000\025\000\081\000\024\000\082\000\023\000\083\000\022\000\
\\086\000\021\000\088\000\020\000\091\000\019\000\094\000\018\000\
\\096\000\017\000\000\000\
\\001\000\035\000\041\000\060\000\040\000\061\000\039\000\062\000\038\000\
\\063\000\037\000\064\000\036\000\065\000\035\000\066\000\034\000\
\\067\000\033\000\070\000\032\000\072\000\031\000\076\000\028\000\
\\077\000\027\000\078\000\026\000\000\000\
\\001\000\038\000\138\001\000\000\
\\001\000\069\000\059\000\000\000\
\\001\000\069\000\066\000\000\000\
\\001\000\069\000\066\000\082\000\002\002\083\000\002\002\086\000\002\002\
\\091\000\002\002\093\000\002\002\000\000\
\\001\000\069\000\103\000\000\000\
\\001\000\069\000\031\001\000\000\
\\001\000\069\000\032\001\000\000\
\\001\000\069\000\077\001\000\000\
\\001\000\069\000\189\001\000\000\
\\001\000\082\000\254\001\083\000\254\001\086\000\254\001\091\000\254\001\
\\093\000\254\001\000\000\
\\001\000\082\000\255\001\083\000\255\001\086\000\255\001\091\000\255\001\
\\093\000\255\001\000\000\
\\001\000\082\000\000\002\083\000\000\002\086\000\000\002\091\000\000\002\
\\093\000\000\002\000\000\
\\001\000\082\000\001\002\083\000\001\002\086\000\001\002\091\000\001\002\
\\093\000\001\002\000\000\
\\001\000\082\000\003\002\083\000\003\002\086\000\003\002\091\000\003\002\
\\093\000\003\002\000\000\
\\001\000\082\000\004\002\083\000\004\002\086\000\004\002\091\000\004\002\
\\093\000\004\002\000\000\
\\001\000\082\000\006\002\083\000\006\002\086\000\006\002\091\000\006\002\
\\093\000\006\002\000\000\
\\001\000\082\000\007\002\083\000\007\002\086\000\007\002\091\000\007\002\
\\093\000\007\002\000\000\
\\001\000\082\000\023\000\083\000\022\000\086\000\021\000\091\000\019\000\
\\093\000\252\001\000\000\
\\001\000\090\000\032\002\000\000\
\\001\000\090\000\034\002\000\000\
\\001\000\090\000\153\001\000\000\
\\001\000\092\000\064\000\000\000\
\\001\000\092\000\122\000\000\000\
\\001\000\092\000\173\000\000\000\
\\001\000\092\000\001\001\000\000\
\\001\000\092\000\002\001\000\000\
\\001\000\092\000\003\001\000\000\
\\001\000\092\000\098\001\000\000\
\\001\000\092\000\171\001\000\000\
\\001\000\092\000\212\001\000\000\
\\001\000\093\000\253\001\000\000\
\\001\000\093\000\052\000\000\000\
\\001\000\093\000\090\000\000\000\
\\001\000\093\000\083\001\000\000\
\\001\000\093\000\084\001\000\000\
\\001\000\093\000\085\001\000\000\
\\001\000\093\000\139\001\000\000\
\\001\000\093\000\147\001\000\000\
\\001\000\093\000\190\001\000\000\
\\001\000\093\000\220\001\000\000\
\"
val actionRowNumbers =
"\113\001\016\000\051\000\021\000\
\\004\000\005\000\131\000\146\001\
\\132\001\025\000\023\000\052\000\
\\019\000\002\000\001\000\013\000\
\\184\000\127\001\116\001\066\001\
\\136\001\117\001\012\000\014\000\
\\035\000\034\000\033\000\011\000\
\\010\000\032\001\053\000\047\000\
\\049\000\048\000\045\000\046\000\
\\044\000\050\000\043\000\033\001\
\\022\000\187\000\090\001\082\001\
\\034\001\183\000\166\000\006\000\
\\132\000\129\000\015\000\145\001\
\\026\000\024\000\020\000\003\000\
\\188\000\147\001\124\001\066\001\
\\137\000\126\001\129\001\125\001\
\\103\001\040\000\039\000\038\000\
\\114\001\058\000\119\001\171\000\
\\172\000\189\000\144\000\211\000\
\\007\000\132\000\008\000\142\000\
\\152\000\182\000\185\000\010\001\
\\162\000\130\000\036\000\204\000\
\\018\000\130\001\070\001\138\001\
\\114\001\029\000\038\001\054\001\
\\132\000\031\000\119\001\041\001\
\\055\001\043\001\137\001\125\000\
\\123\000\116\000\106\000\100\000\
\\104\000\156\000\002\001\007\001\
\\255\000\253\000\251\000\249\000\
\\247\000\243\000\245\000\071\001\
\\127\000\128\000\122\000\150\000\
\\149\000\149\000\149\000\149\000\
\\168\000\148\000\149\000\212\000\
\\011\001\213\000\134\000\086\001\
\\079\001\049\001\080\001\141\000\
\\107\000\091\001\109\001\028\000\
\\086\000\151\000\056\001\027\000\
\\131\000\180\000\139\001\140\001\
\\141\001\192\000\193\000\092\001\
\\093\001\147\000\092\000\194\000\
\\195\000\082\000\149\000\186\000\
\\169\000\163\000\037\000\012\001\
\\205\000\196\000\066\001\118\001\
\\057\001\030\000\039\001\042\000\
\\094\001\083\001\077\001\032\000\
\\058\001\059\001\054\000\149\000\
\\013\001\126\000\120\001\121\001\
\\149\000\138\000\149\000\149\000\
\\149\000\149\000\149\000\149\000\
\\149\000\149\000\149\000\149\000\
\\149\000\149\000\149\000\149\000\
\\149\000\149\000\149\000\149\000\
\\149\000\167\000\114\000\148\000\
\\110\000\111\000\109\000\108\000\
\\014\001\015\001\136\000\112\000\
\\165\000\113\001\199\000\216\000\
\\215\000\191\000\145\000\133\000\
\\068\001\111\001\142\000\048\001\
\\045\001\060\001\122\001\149\000\
\\072\000\149\000\070\000\069\000\
\\065\000\068\000\067\000\066\000\
\\063\000\064\000\062\000\061\000\
\\095\001\096\001\060\000\037\001\
\\009\000\200\000\181\000\148\001\
\\149\001\150\001\149\000\160\000\
\\079\000\078\000\097\001\077\000\
\\155\000\093\000\142\001\149\000\
\\149\000\113\000\016\001\204\000\
\\139\000\131\001\128\001\041\000\
\\040\001\132\000\149\000\061\001\
\\055\000\042\001\056\000\044\001\
\\173\000\120\000\119\000\072\001\
\\017\001\240\000\241\000\103\000\
\\102\000\101\000\009\001\008\001\
\\158\000\157\000\004\001\003\001\
\\006\001\005\001\001\001\000\001\
\\254\000\252\000\250\000\246\000\
\\104\001\248\000\018\001\124\000\
\\143\000\217\000\197\000\135\000\
\\170\000\067\001\214\000\149\000\
\\211\000\198\000\073\001\176\000\
\\019\001\020\001\107\001\059\000\
\\047\001\140\000\050\001\065\001\
\\074\001\098\001\084\000\083\000\
\\137\001\153\000\088\000\087\000\
\\021\001\190\000\112\001\084\001\
\\087\001\099\001\146\000\099\000\
\\148\000\149\000\076\000\115\001\
\\151\001\022\001\023\001\017\000\
\\206\000\024\001\209\000\207\000\
\\085\001\078\001\057\000\117\000\
\\118\000\149\000\149\000\115\000\
\\105\000\141\000\152\001\075\001\
\\025\001\175\000\174\000\178\000\
\\046\001\064\001\071\000\219\000\
\\026\001\133\001\135\001\154\000\
\\036\001\149\000\161\000\098\000\
\\089\001\100\001\027\001\108\001\
\\201\000\091\000\092\000\155\000\
\\208\000\149\000\242\000\244\000\
\\062\001\164\000\177\000\179\000\
\\218\000\227\000\101\001\143\001\
\\134\001\051\001\081\001\088\001\
\\159\000\035\001\149\000\155\000\
\\080\000\210\000\121\000\228\000\
\\221\000\229\000\202\000\123\001\
\\090\000\153\001\094\000\155\000\
\\051\001\063\001\105\001\149\000\
\\110\001\234\000\233\000\028\001\
\\029\001\073\000\155\000\220\000\
\\227\000\069\001\149\000\076\001\
\\089\000\095\000\151\000\052\001\
\\085\000\097\000\106\001\149\000\
\\239\000\238\000\144\001\161\000\
\\092\000\102\001\081\000\223\000\
\\230\000\030\001\137\001\053\001\
\\096\000\237\000\154\001\236\000\
\\155\000\074\000\222\000\137\001\
\\231\000\203\000\235\000\075\000\
\\224\000\225\000\149\000\137\001\
\\031\001\226\000\232\000\000\000"
val gotoT =
"\
\\001\000\227\001\002\000\014\000\003\000\013\000\006\000\012\000\
\\007\000\011\000\010\000\010\000\012\000\009\000\013\000\008\000\
\\014\000\007\000\020\000\006\000\028\000\005\000\040\000\004\000\
\\068\000\003\000\069\000\002\000\092\000\001\000\000\000\
\\000\000\
\\000\000\
\\006\000\012\000\007\000\011\000\010\000\010\000\012\000\009\000\
\\013\000\008\000\014\000\007\000\020\000\040\000\068\000\003\000\
\\069\000\002\000\092\000\001\000\000\000\
\\000\000\
\\000\000\
\\058\000\045\000\059\000\044\000\064\000\043\000\065\000\042\000\
\\066\000\041\000\000\000\
\\000\000\
\\013\000\008\000\014\000\051\000\000\000\
\\006\000\012\000\007\000\011\000\010\000\010\000\012\000\009\000\
\\013\000\008\000\014\000\007\000\020\000\052\000\068\000\003\000\
\\069\000\002\000\092\000\001\000\000\000\
\\006\000\012\000\007\000\011\000\010\000\010\000\012\000\009\000\
\\013\000\008\000\014\000\007\000\020\000\053\000\068\000\003\000\
\\069\000\002\000\092\000\001\000\000\000\
\\000\000\
\\006\000\012\000\007\000\011\000\010\000\010\000\012\000\009\000\
\\013\000\008\000\014\000\007\000\020\000\054\000\068\000\003\000\
\\069\000\002\000\092\000\001\000\000\000\
\\002\000\055\000\003\000\013\000\006\000\012\000\007\000\011\000\
\\010\000\010\000\012\000\009\000\013\000\008\000\014\000\007\000\
\\020\000\006\000\028\000\005\000\040\000\004\000\068\000\003\000\
\\069\000\002\000\092\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\090\000\058\000\000\000\
\\016\000\061\000\000\000\
\\015\000\063\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\070\000\065\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\070\000\069\000\000\000\
\\000\000\
\\067\000\072\000\092\000\071\000\000\000\
\\000\000\
\\000\000\
\\041\000\078\000\000\000\
\\066\000\082\000\092\000\081\000\000\000\
\\000\000\
\\000\000\
\\058\000\045\000\059\000\083\000\066\000\041\000\000\000\
\\010\000\086\000\011\000\085\000\058\000\084\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\090\000\089\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\007\000\011\000\010\000\097\000\021\000\096\000\029\000\095\000\
\\030\000\094\000\068\000\093\000\069\000\002\000\000\000\
\\000\000\
\\008\000\100\000\009\000\099\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\072\000\119\000\075\000\118\000\076\000\117\000\077\000\116\000\
\\078\000\115\000\079\000\114\000\080\000\113\000\081\000\112\000\
\\082\000\111\000\083\000\110\000\084\000\109\000\085\000\108\000\
\\086\000\107\000\087\000\106\000\088\000\105\000\089\000\104\000\
\\099\000\103\000\000\000\
\\006\000\012\000\007\000\011\000\010\000\010\000\012\000\009\000\
\\013\000\008\000\014\000\007\000\020\000\134\000\037\000\133\000\
\\038\000\132\000\039\000\131\000\068\000\003\000\069\000\002\000\
\\092\000\001\000\000\000\
\\000\000\
\\058\000\045\000\059\000\136\000\064\000\043\000\065\000\135\000\
\\066\000\041\000\000\000\
\\000\000\
\\024\000\138\000\072\000\137\000\075\000\118\000\076\000\117\000\
\\077\000\116\000\078\000\115\000\079\000\114\000\080\000\113\000\
\\081\000\112\000\082\000\111\000\083\000\110\000\084\000\109\000\
\\085\000\108\000\086\000\107\000\087\000\106\000\088\000\105\000\
\\089\000\104\000\099\000\103\000\000\000\
\\006\000\012\000\007\000\011\000\010\000\010\000\012\000\009\000\
\\013\000\008\000\014\000\007\000\020\000\148\000\028\000\147\000\
\\035\000\146\000\036\000\145\000\041\000\144\000\042\000\143\000\
\\068\000\003\000\069\000\002\000\071\000\142\000\072\000\141\000\
\\075\000\118\000\076\000\117\000\077\000\116\000\078\000\115\000\
\\079\000\114\000\080\000\113\000\081\000\112\000\082\000\111\000\
\\083\000\110\000\084\000\109\000\085\000\108\000\086\000\107\000\
\\087\000\140\000\088\000\105\000\089\000\104\000\092\000\001\000\
\\099\000\103\000\000\000\
\\066\000\163\000\000\000\
\\067\000\072\000\092\000\071\000\000\000\
\\000\000\
\\000\000\
\\058\000\165\000\000\000\
\\010\000\086\000\011\000\166\000\000\000\
\\091\000\168\000\093\000\167\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\007\000\011\000\010\000\097\000\021\000\096\000\029\000\172\000\
\\030\000\094\000\068\000\093\000\069\000\002\000\000\000\
\\007\000\011\000\010\000\097\000\021\000\173\000\068\000\093\000\
\\069\000\002\000\000\000\
\\007\000\011\000\010\000\097\000\021\000\096\000\029\000\174\000\
\\030\000\094\000\068\000\093\000\069\000\002\000\000\000\
\\000\000\
\\058\000\045\000\059\000\178\000\062\000\177\000\063\000\176\000\
\\066\000\041\000\000\000\
\\007\000\011\000\010\000\097\000\021\000\179\000\068\000\093\000\
\\069\000\002\000\000\000\
\\008\000\180\000\009\000\099\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\099\000\184\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\085\000\210\000\087\000\106\000\088\000\105\000\089\000\104\000\
\\099\000\103\000\000\000\
\\085\000\108\000\086\000\212\000\087\000\106\000\088\000\105\000\
\\089\000\104\000\099\000\103\000\000\000\
\\085\000\108\000\086\000\213\000\087\000\106\000\088\000\105\000\
\\089\000\104\000\099\000\103\000\000\000\
\\085\000\108\000\086\000\214\000\087\000\106\000\088\000\105\000\
\\089\000\104\000\099\000\103\000\000\000\
\\085\000\108\000\086\000\215\000\087\000\106\000\088\000\105\000\
\\089\000\104\000\099\000\103\000\000\000\
\\000\000\
\\007\000\011\000\010\000\097\000\021\000\218\000\034\000\217\000\
\\068\000\093\000\069\000\002\000\072\000\216\000\075\000\118\000\
\\076\000\117\000\077\000\116\000\078\000\115\000\079\000\114\000\
\\080\000\113\000\081\000\112\000\082\000\111\000\083\000\110\000\
\\084\000\109\000\085\000\108\000\086\000\107\000\087\000\106\000\
\\088\000\105\000\089\000\104\000\099\000\103\000\000\000\
\\085\000\108\000\086\000\219\000\087\000\106\000\088\000\105\000\
\\089\000\104\000\099\000\103\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\058\000\225\000\059\000\224\000\060\000\223\000\061\000\222\000\
\\066\000\041\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\022\000\233\000\023\000\232\000\024\000\231\000\025\000\230\000\
\\026\000\229\000\027\000\228\000\072\000\137\000\075\000\118\000\
\\076\000\117\000\077\000\116\000\078\000\115\000\079\000\114\000\
\\080\000\113\000\081\000\112\000\082\000\111\000\083\000\110\000\
\\084\000\109\000\085\000\108\000\086\000\107\000\087\000\106\000\
\\088\000\105\000\089\000\104\000\099\000\103\000\000\000\
\\000\000\
\\000\000\
\\057\000\237\000\000\000\
\\000\000\
\\000\000\
\\006\000\012\000\007\000\011\000\010\000\010\000\012\000\009\000\
\\013\000\008\000\014\000\007\000\020\000\148\000\028\000\147\000\
\\035\000\251\000\036\000\145\000\041\000\144\000\042\000\143\000\
\\068\000\003\000\069\000\002\000\071\000\142\000\072\000\141\000\
\\075\000\118\000\076\000\117\000\077\000\116\000\078\000\115\000\
\\079\000\114\000\080\000\113\000\081\000\112\000\082\000\111\000\
\\083\000\110\000\084\000\109\000\085\000\108\000\086\000\107\000\
\\087\000\140\000\088\000\105\000\089\000\104\000\092\000\001\000\
\\099\000\103\000\000\000\
\\000\000\
\\000\000\
\\058\000\045\000\059\000\136\000\064\000\043\000\065\000\042\000\
\\066\000\041\000\000\000\
\\005\000\253\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\072\000\006\001\075\000\118\000\076\000\117\000\077\000\116\000\
\\078\000\115\000\079\000\114\000\080\000\113\000\081\000\112\000\
\\082\000\111\000\083\000\110\000\084\000\109\000\085\000\108\000\
\\086\000\107\000\087\000\106\000\088\000\105\000\089\000\104\000\
\\099\000\103\000\000\000\
\\018\000\009\001\019\000\008\001\000\000\
\\000\000\
\\000\000\
\\000\000\
\\085\000\108\000\086\000\013\001\087\000\106\000\088\000\105\000\
\\089\000\104\000\099\000\103\000\000\000\
\\067\000\072\000\092\000\071\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\090\000\017\001\000\000\
\\015\000\018\001\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\009\000\025\001\000\000\
\\000\000\
\\072\000\027\001\075\000\118\000\076\000\117\000\077\000\116\000\
\\078\000\115\000\079\000\114\000\080\000\113\000\081\000\112\000\
\\082\000\111\000\083\000\110\000\084\000\109\000\085\000\108\000\
\\086\000\107\000\087\000\106\000\088\000\105\000\089\000\104\000\
\\099\000\103\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\072\000\031\001\075\000\118\000\076\000\117\000\077\000\116\000\
\\078\000\115\000\079\000\114\000\080\000\113\000\081\000\112\000\
\\082\000\111\000\083\000\110\000\084\000\109\000\085\000\108\000\
\\086\000\107\000\087\000\106\000\088\000\105\000\089\000\104\000\
\\099\000\103\000\000\000\
\\072\000\034\001\073\000\033\001\074\000\032\001\075\000\118\000\
\\076\000\117\000\077\000\116\000\078\000\115\000\079\000\114\000\
\\080\000\113\000\081\000\112\000\082\000\111\000\083\000\110\000\
\\084\000\109\000\085\000\108\000\086\000\107\000\087\000\106\000\
\\088\000\105\000\089\000\104\000\099\000\103\000\000\000\
\\085\000\108\000\086\000\035\001\087\000\106\000\088\000\105\000\
\\089\000\104\000\099\000\103\000\000\000\
\\085\000\108\000\086\000\036\001\087\000\106\000\088\000\105\000\
\\089\000\104\000\099\000\103\000\000\000\
\\085\000\108\000\086\000\037\001\087\000\106\000\088\000\105\000\
\\089\000\104\000\099\000\103\000\000\000\
\\082\000\038\001\084\000\109\000\085\000\108\000\086\000\107\000\
\\087\000\106\000\088\000\105\000\089\000\104\000\099\000\103\000\000\000\
\\082\000\039\001\084\000\109\000\085\000\108\000\086\000\107\000\
\\087\000\106\000\088\000\105\000\089\000\104\000\099\000\103\000\000\000\
\\084\000\040\001\085\000\108\000\086\000\107\000\087\000\106\000\
\\088\000\105\000\089\000\104\000\099\000\103\000\000\000\
\\084\000\041\001\085\000\108\000\086\000\107\000\087\000\106\000\
\\088\000\105\000\089\000\104\000\099\000\103\000\000\000\
\\082\000\111\000\083\000\042\001\084\000\109\000\085\000\108\000\
\\086\000\107\000\087\000\106\000\088\000\105\000\089\000\104\000\
\\099\000\103\000\000\000\
\\082\000\111\000\083\000\043\001\084\000\109\000\085\000\108\000\
\\086\000\107\000\087\000\106\000\088\000\105\000\089\000\104\000\
\\099\000\103\000\000\000\
\\082\000\111\000\083\000\044\001\084\000\109\000\085\000\108\000\
\\086\000\107\000\087\000\106\000\088\000\105\000\089\000\104\000\
\\099\000\103\000\000\000\
\\082\000\111\000\083\000\045\001\084\000\109\000\085\000\108\000\
\\086\000\107\000\087\000\106\000\088\000\105\000\089\000\104\000\
\\099\000\103\000\000\000\
\\081\000\046\001\082\000\111\000\083\000\110\000\084\000\109\000\
\\085\000\108\000\086\000\107\000\087\000\106\000\088\000\105\000\
\\089\000\104\000\099\000\103\000\000\000\
\\081\000\047\001\082\000\111\000\083\000\110\000\084\000\109\000\
\\085\000\108\000\086\000\107\000\087\000\106\000\088\000\105\000\
\\089\000\104\000\099\000\103\000\000\000\
\\080\000\048\001\081\000\112\000\082\000\111\000\083\000\110\000\
\\084\000\109\000\085\000\108\000\086\000\107\000\087\000\106\000\
\\088\000\105\000\089\000\104\000\099\000\103\000\000\000\
\\079\000\049\001\080\000\113\000\081\000\112\000\082\000\111\000\
\\083\000\110\000\084\000\109\000\085\000\108\000\086\000\107\000\
\\087\000\106\000\088\000\105\000\089\000\104\000\099\000\103\000\000\000\
\\078\000\050\001\079\000\114\000\080\000\113\000\081\000\112\000\
\\082\000\111\000\083\000\110\000\084\000\109\000\085\000\108\000\
\\086\000\107\000\087\000\106\000\088\000\105\000\089\000\104\000\
\\099\000\103\000\000\000\
\\075\000\051\001\077\000\116\000\078\000\115\000\079\000\114\000\
\\080\000\113\000\081\000\112\000\082\000\111\000\083\000\110\000\
\\084\000\109\000\085\000\108\000\086\000\107\000\087\000\106\000\
\\088\000\105\000\089\000\104\000\099\000\103\000\000\000\
\\072\000\052\001\075\000\118\000\076\000\117\000\077\000\116\000\
\\078\000\115\000\079\000\114\000\080\000\113\000\081\000\112\000\
\\082\000\111\000\083\000\110\000\084\000\109\000\085\000\108\000\
\\086\000\107\000\087\000\106\000\088\000\105\000\089\000\104\000\
\\099\000\103\000\000\000\
\\077\000\053\001\078\000\115\000\079\000\114\000\080\000\113\000\
\\081\000\112\000\082\000\111\000\083\000\110\000\084\000\109\000\
\\085\000\108\000\086\000\107\000\087\000\106\000\088\000\105\000\
\\089\000\104\000\099\000\103\000\000\000\
\\000\000\
\\000\000\
\\007\000\011\000\010\000\097\000\021\000\218\000\034\000\054\001\
\\068\000\093\000\069\000\002\000\072\000\216\000\075\000\118\000\
\\076\000\117\000\077\000\116\000\078\000\115\000\079\000\114\000\
\\080\000\113\000\081\000\112\000\082\000\111\000\083\000\110\000\
\\084\000\109\000\085\000\108\000\086\000\107\000\087\000\106\000\
\\088\000\105\000\089\000\104\000\099\000\103\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\058\000\058\001\060\000\057\001\061\000\222\000\000\000\
\\000\000\
\\104\000\060\001\000\000\
\\006\000\012\000\007\000\011\000\010\000\010\000\012\000\009\000\
\\013\000\008\000\014\000\007\000\020\000\134\000\037\000\133\000\
\\039\000\062\001\068\000\003\000\069\000\002\000\092\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\061\000\065\001\066\000\082\000\092\000\081\000\000\000\
\\072\000\066\001\075\000\118\000\076\000\117\000\077\000\116\000\
\\078\000\115\000\079\000\114\000\080\000\113\000\081\000\112\000\
\\082\000\111\000\083\000\110\000\084\000\109\000\085\000\108\000\
\\086\000\107\000\087\000\106\000\088\000\105\000\089\000\104\000\
\\099\000\103\000\000\000\
\\006\000\012\000\007\000\011\000\010\000\010\000\012\000\009\000\
\\013\000\008\000\014\000\007\000\020\000\134\000\037\000\133\000\
\\038\000\069\001\039\000\131\000\058\000\225\000\059\000\083\000\
\\060\000\068\001\061\000\222\000\066\000\041\000\068\000\003\000\
\\069\000\002\000\092\000\001\000\000\000\
\\026\000\070\001\027\000\228\000\000\000\
\\000\000\
\\024\000\072\001\072\000\137\000\075\000\118\000\076\000\117\000\
\\077\000\116\000\078\000\115\000\079\000\114\000\080\000\113\000\
\\081\000\112\000\082\000\111\000\083\000\110\000\084\000\109\000\
\\085\000\108\000\086\000\107\000\087\000\106\000\088\000\105\000\
\\089\000\104\000\099\000\103\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\072\000\076\001\075\000\118\000\076\000\117\000\077\000\116\000\
\\078\000\115\000\079\000\114\000\080\000\113\000\081\000\112\000\
\\082\000\111\000\083\000\110\000\084\000\109\000\085\000\108\000\
\\086\000\107\000\087\000\106\000\088\000\105\000\089\000\104\000\
\\099\000\103\000\000\000\
\\000\000\
\\072\000\077\001\075\000\118\000\076\000\117\000\077\000\116\000\
\\078\000\115\000\079\000\114\000\080\000\113\000\081\000\112\000\
\\082\000\111\000\083\000\110\000\084\000\109\000\085\000\108\000\
\\086\000\107\000\087\000\106\000\088\000\105\000\089\000\104\000\
\\099\000\103\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\072\000\084\001\075\000\118\000\076\000\117\000\077\000\116\000\
\\078\000\115\000\079\000\114\000\080\000\113\000\081\000\112\000\
\\082\000\111\000\083\000\110\000\084\000\109\000\085\000\108\000\
\\086\000\107\000\087\000\106\000\088\000\105\000\089\000\104\000\
\\099\000\103\000\000\000\
\\006\000\012\000\007\000\011\000\010\000\010\000\012\000\009\000\
\\013\000\008\000\014\000\007\000\020\000\148\000\028\000\091\001\
\\049\000\090\001\050\000\089\001\051\000\088\001\052\000\087\001\
\\068\000\003\000\069\000\002\000\071\000\086\001\087\000\085\001\
\\088\000\105\000\089\000\104\000\092\000\001\000\099\000\103\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\041\000\144\000\042\000\095\001\071\000\142\000\072\000\141\000\
\\075\000\118\000\076\000\117\000\077\000\116\000\078\000\115\000\
\\079\000\114\000\080\000\113\000\081\000\112\000\082\000\111\000\
\\083\000\110\000\084\000\109\000\085\000\108\000\086\000\107\000\
\\087\000\140\000\088\000\105\000\089\000\104\000\099\000\103\000\000\000\
\\000\000\
\\000\000\
\\072\000\097\001\075\000\118\000\076\000\117\000\077\000\116\000\
\\078\000\115\000\079\000\114\000\080\000\113\000\081\000\112\000\
\\082\000\111\000\083\000\110\000\084\000\109\000\085\000\108\000\
\\086\000\107\000\087\000\106\000\088\000\105\000\089\000\104\000\
\\099\000\103\000\000\000\
\\072\000\098\001\075\000\118\000\076\000\117\000\077\000\116\000\
\\078\000\115\000\079\000\114\000\080\000\113\000\081\000\112\000\
\\082\000\111\000\083\000\110\000\084\000\109\000\085\000\108\000\
\\086\000\107\000\087\000\106\000\088\000\105\000\089\000\104\000\
\\099\000\103\000\000\000\
\\000\000\
\\000\000\
\\091\000\168\000\093\000\100\001\000\000\
\\072\000\102\001\075\000\118\000\076\000\117\000\077\000\116\000\
\\078\000\115\000\079\000\114\000\080\000\113\000\081\000\112\000\
\\082\000\111\000\083\000\110\000\084\000\109\000\085\000\108\000\
\\086\000\107\000\087\000\106\000\088\000\105\000\089\000\104\000\
\\094\000\101\001\099\000\103\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\058\000\045\000\059\000\178\000\062\000\177\000\063\000\104\001\
\\066\000\041\000\000\000\
\\072\000\105\001\075\000\118\000\076\000\117\000\077\000\116\000\
\\078\000\115\000\079\000\114\000\080\000\113\000\081\000\112\000\
\\082\000\111\000\083\000\110\000\084\000\109\000\085\000\108\000\
\\086\000\107\000\087\000\106\000\088\000\105\000\089\000\104\000\
\\099\000\103\000\000\000\
\\009\000\025\001\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\085\000\108\000\086\000\112\001\087\000\106\000\088\000\105\000\
\\089\000\104\000\099\000\103\000\000\000\
\\000\000\
\\061\000\065\001\000\000\
\\006\000\012\000\007\000\011\000\010\000\010\000\012\000\009\000\
\\013\000\008\000\014\000\007\000\020\000\134\000\037\000\133\000\
\\038\000\069\001\039\000\131\000\058\000\058\001\060\000\068\001\
\\061\000\222\000\068\000\003\000\069\000\002\000\092\000\001\000\000\000\
\\000\000\
\\090\000\114\001\000\000\
\\000\000\
\\072\000\115\001\075\000\118\000\076\000\117\000\077\000\116\000\
\\078\000\115\000\079\000\114\000\080\000\113\000\081\000\112\000\
\\082\000\111\000\083\000\110\000\084\000\109\000\085\000\108\000\
\\086\000\107\000\087\000\106\000\088\000\105\000\089\000\104\000\
\\099\000\103\000\000\000\
\\006\000\012\000\007\000\011\000\010\000\010\000\012\000\009\000\
\\013\000\008\000\014\000\007\000\020\000\134\000\037\000\133\000\
\\038\000\116\001\039\000\131\000\068\000\003\000\069\000\002\000\
\\092\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\022\000\120\001\023\000\232\000\024\000\231\000\025\000\230\000\
\\026\000\229\000\027\000\228\000\072\000\137\000\075\000\118\000\
\\076\000\117\000\077\000\116\000\078\000\115\000\079\000\114\000\
\\080\000\113\000\081\000\112\000\082\000\111\000\083\000\110\000\
\\084\000\109\000\085\000\108\000\086\000\107\000\087\000\106\000\
\\088\000\105\000\089\000\104\000\099\000\103\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\095\000\124\001\099\000\123\001\000\000\
\\041\000\144\000\042\000\127\001\043\000\126\001\044\000\125\001\
\\071\000\142\000\072\000\141\000\075\000\118\000\076\000\117\000\
\\077\000\116\000\078\000\115\000\079\000\114\000\080\000\113\000\
\\081\000\112\000\082\000\111\000\083\000\110\000\084\000\109\000\
\\085\000\108\000\086\000\107\000\087\000\140\000\088\000\105\000\
\\089\000\104\000\099\000\103\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\053\000\133\001\072\000\132\001\075\000\118\000\076\000\117\000\
\\077\000\116\000\078\000\115\000\079\000\114\000\080\000\113\000\
\\081\000\112\000\082\000\111\000\083\000\110\000\084\000\109\000\
\\085\000\108\000\086\000\107\000\087\000\106\000\088\000\105\000\
\\089\000\104\000\099\000\103\000\000\000\
\\000\000\
\\007\000\011\000\010\000\097\000\021\000\218\000\034\000\134\001\
\\068\000\093\000\069\000\002\000\072\000\216\000\075\000\118\000\
\\076\000\117\000\077\000\116\000\078\000\115\000\079\000\114\000\
\\080\000\113\000\081\000\112\000\082\000\111\000\083\000\110\000\
\\084\000\109\000\085\000\108\000\086\000\107\000\087\000\106\000\
\\088\000\105\000\089\000\104\000\099\000\103\000\000\000\
\\085\000\108\000\086\000\135\001\087\000\106\000\088\000\105\000\
\\089\000\104\000\099\000\103\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\072\000\034\001\073\000\142\001\075\000\118\000\076\000\117\000\
\\077\000\116\000\078\000\115\000\079\000\114\000\080\000\113\000\
\\081\000\112\000\082\000\111\000\083\000\110\000\084\000\109\000\
\\085\000\108\000\086\000\107\000\087\000\106\000\088\000\105\000\
\\089\000\104\000\099\000\103\000\000\000\
\\072\000\143\001\075\000\118\000\076\000\117\000\077\000\116\000\
\\078\000\115\000\079\000\114\000\080\000\113\000\081\000\112\000\
\\082\000\111\000\083\000\110\000\084\000\109\000\085\000\108\000\
\\086\000\107\000\087\000\106\000\088\000\105\000\089\000\104\000\
\\099\000\103\000\000\000\
\\000\000\
\\000\000\
\\022\000\144\001\023\000\232\000\024\000\231\000\025\000\230\000\
\\026\000\229\000\027\000\228\000\072\000\137\000\075\000\118\000\
\\076\000\117\000\077\000\116\000\078\000\115\000\079\000\114\000\
\\080\000\113\000\081\000\112\000\082\000\111\000\083\000\110\000\
\\084\000\109\000\085\000\108\000\086\000\107\000\087\000\106\000\
\\088\000\105\000\089\000\104\000\099\000\103\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\096\000\148\001\000\000\
\\000\000\
\\000\000\
\\000\000\
\\041\000\144\000\042\000\127\001\044\000\152\001\071\000\142\000\
\\072\000\141\000\075\000\118\000\076\000\117\000\077\000\116\000\
\\078\000\115\000\079\000\114\000\080\000\113\000\081\000\112\000\
\\082\000\111\000\083\000\110\000\084\000\109\000\085\000\108\000\
\\086\000\107\000\087\000\140\000\088\000\105\000\089\000\104\000\
\\099\000\103\000\000\000\
\\000\000\
\\072\000\154\001\075\000\118\000\076\000\117\000\077\000\116\000\
\\078\000\115\000\079\000\114\000\080\000\113\000\081\000\112\000\
\\082\000\111\000\083\000\110\000\084\000\109\000\085\000\108\000\
\\086\000\107\000\087\000\106\000\088\000\105\000\089\000\104\000\
\\099\000\103\000\000\000\
\\051\000\155\001\052\000\087\001\071\000\086\001\087\000\085\001\
\\088\000\105\000\089\000\104\000\099\000\103\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\018\000\009\001\019\000\159\001\000\000\
\\041\000\144\000\042\000\160\001\071\000\142\000\072\000\141\000\
\\075\000\118\000\076\000\117\000\077\000\116\000\078\000\115\000\
\\079\000\114\000\080\000\113\000\081\000\112\000\082\000\111\000\
\\083\000\110\000\084\000\109\000\085\000\108\000\086\000\107\000\
\\087\000\140\000\088\000\105\000\089\000\104\000\099\000\103\000\000\000\
\\000\000\
\\072\000\102\001\075\000\118\000\076\000\117\000\077\000\116\000\
\\078\000\115\000\079\000\114\000\080\000\113\000\081\000\112\000\
\\082\000\111\000\083\000\110\000\084\000\109\000\085\000\108\000\
\\086\000\107\000\087\000\106\000\088\000\105\000\089\000\104\000\
\\094\000\161\001\099\000\103\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\099\000\166\001\101\000\165\001\102\000\164\001\103\000\163\001\000\000\
\\000\000\
\\000\000\
\\000\000\
\\045\000\173\001\046\000\172\001\047\000\171\001\048\000\170\001\000\000\
\\000\000\
\\000\000\
\\054\000\179\001\055\000\178\001\056\000\177\001\071\000\176\001\
\\087\000\085\001\088\000\105\000\089\000\104\000\099\000\103\000\000\000\
\\000\000\
\\072\000\180\001\075\000\118\000\076\000\117\000\077\000\116\000\
\\078\000\115\000\079\000\114\000\080\000\113\000\081\000\112\000\
\\082\000\111\000\083\000\110\000\084\000\109\000\085\000\108\000\
\\086\000\107\000\087\000\106\000\088\000\105\000\089\000\104\000\
\\099\000\103\000\000\000\
\\041\000\144\000\042\000\181\001\071\000\142\000\072\000\141\000\
\\075\000\118\000\076\000\117\000\077\000\116\000\078\000\115\000\
\\079\000\114\000\080\000\113\000\081\000\112\000\082\000\111\000\
\\083\000\110\000\084\000\109\000\085\000\108\000\086\000\107\000\
\\087\000\140\000\088\000\105\000\089\000\104\000\099\000\103\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\097\000\183\001\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\047\000\189\001\048\000\170\001\000\000\
\\041\000\144\000\042\000\190\001\071\000\142\000\072\000\141\000\
\\075\000\118\000\076\000\117\000\077\000\116\000\078\000\115\000\
\\079\000\114\000\080\000\113\000\081\000\112\000\082\000\111\000\
\\083\000\110\000\084\000\109\000\085\000\108\000\086\000\107\000\
\\087\000\140\000\088\000\105\000\089\000\104\000\099\000\103\000\000\000\
\\045\000\191\001\046\000\172\001\047\000\171\001\048\000\170\001\000\000\
\\000\000\
\\000\000\
\\072\000\194\001\075\000\118\000\076\000\117\000\077\000\116\000\
\\078\000\115\000\079\000\114\000\080\000\113\000\081\000\112\000\
\\082\000\111\000\083\000\110\000\084\000\109\000\085\000\108\000\
\\086\000\107\000\087\000\106\000\088\000\105\000\089\000\104\000\
\\099\000\103\000\000\000\
\\057\000\195\001\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\041\000\144\000\042\000\202\001\071\000\142\000\072\000\141\000\
\\075\000\118\000\076\000\117\000\077\000\116\000\078\000\115\000\
\\079\000\114\000\080\000\113\000\081\000\112\000\082\000\111\000\
\\083\000\110\000\084\000\109\000\085\000\108\000\086\000\107\000\
\\087\000\140\000\088\000\105\000\089\000\104\000\099\000\103\000\000\000\
\\000\000\
\\099\000\166\001\101\000\165\001\102\000\203\001\103\000\163\001\000\000\
\\099\000\166\001\101\000\165\001\103\000\204\001\000\000\
\\072\000\205\001\075\000\118\000\076\000\117\000\077\000\116\000\
\\078\000\115\000\079\000\114\000\080\000\113\000\081\000\112\000\
\\082\000\111\000\083\000\110\000\084\000\109\000\085\000\108\000\
\\086\000\107\000\087\000\106\000\088\000\105\000\089\000\104\000\
\\099\000\103\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\006\000\012\000\007\000\011\000\010\000\010\000\012\000\009\000\
\\013\000\008\000\014\000\007\000\020\000\148\000\028\000\147\000\
\\035\000\207\001\036\000\145\000\041\000\144\000\042\000\143\000\
\\068\000\003\000\069\000\002\000\071\000\142\000\072\000\141\000\
\\075\000\118\000\076\000\117\000\077\000\116\000\078\000\115\000\
\\079\000\114\000\080\000\113\000\081\000\112\000\082\000\111\000\
\\083\000\110\000\084\000\109\000\085\000\108\000\086\000\107\000\
\\087\000\140\000\088\000\105\000\089\000\104\000\092\000\001\000\
\\099\000\103\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\072\000\209\001\075\000\118\000\076\000\117\000\077\000\116\000\
\\078\000\115\000\079\000\114\000\080\000\113\000\081\000\112\000\
\\082\000\111\000\083\000\110\000\084\000\109\000\085\000\108\000\
\\086\000\107\000\087\000\106\000\088\000\105\000\089\000\104\000\
\\099\000\103\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\055\000\211\001\056\000\177\001\071\000\176\001\087\000\085\001\
\\088\000\105\000\089\000\104\000\099\000\103\000\000\000\
\\018\000\009\001\019\000\212\001\000\000\
\\000\000\
\\000\000\
\\098\000\214\001\000\000\
\\000\000\
\\000\000\
\\099\000\217\001\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\041\000\144\000\042\000\219\001\071\000\142\000\072\000\141\000\
\\075\000\118\000\076\000\117\000\077\000\116\000\078\000\115\000\
\\079\000\114\000\080\000\113\000\081\000\112\000\082\000\111\000\
\\083\000\110\000\084\000\109\000\085\000\108\000\086\000\107\000\
\\087\000\140\000\088\000\105\000\089\000\104\000\099\000\103\000\000\000\
\\000\000\
\\000\000\
\\099\000\221\001\100\000\220\001\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\072\000\224\001\075\000\118\000\076\000\117\000\077\000\116\000\
\\078\000\115\000\079\000\114\000\080\000\113\000\081\000\112\000\
\\082\000\111\000\083\000\110\000\084\000\109\000\085\000\108\000\
\\086\000\107\000\087\000\106\000\088\000\105\000\089\000\104\000\
\\099\000\103\000\000\000\
\\099\000\221\001\100\000\225\001\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\"
val numstates = 484
val numrules = 280
val s = ref "" and index = ref 0
val string_to_int = fn () => 
let val i = !index
in index := i+2; Char.ord(String.sub(!s,i)) + Char.ord(String.sub(!s,i+1)) * 256
end
val string_to_list = fn s' =>
    let val len = String.size s'
        fun f () =
           if !index < len then string_to_int() :: f()
           else nil
   in index := 0; s := s'; f ()
   end
val string_to_pairlist = fn (conv_key,conv_entry) =>
     let fun f () =
         case string_to_int()
         of 0 => EMPTY
          | n => PAIR(conv_key (n-1),conv_entry (string_to_int()),f())
     in f
     end
val string_to_pairlist_default = fn (conv_key,conv_entry) =>
    let val conv_row = string_to_pairlist(conv_key,conv_entry)
    in fn () =>
       let val default = conv_entry(string_to_int())
           val row = conv_row()
       in (row,default)
       end
   end
val string_to_table = fn (convert_row,s') =>
    let val len = String.size s'
        fun f ()=
           if !index < len then convert_row() :: f()
           else nil
     in (s := s'; index := 0; f ())
     end
local
  val memo = Array.array(numstates+numrules,ERROR)
  val _ =let fun g i=(Array.update(memo,i,REDUCE(i-numstates)); g(i+1))
       fun f i =
            if i=numstates then g i
            else (Array.update(memo,i,SHIFT (STATE i)); f (i+1))
          in f 0 handle Subscript => ()
          end
in
val entry_to_action = fn 0 => ACCEPT | 1 => ERROR | j => Array.sub(memo,(j-2))
end
val gotoT=Array.fromList(string_to_table(string_to_pairlist(NT,STATE),gotoT))
val actionRows=string_to_table(string_to_pairlist_default(T,entry_to_action),actionRows)
val actionRowNumbers = string_to_list actionRowNumbers
val actionT = let val actionRowLookUp=
let val a=Array.fromList(actionRows) in fn i=>Array.sub(a,i) end
in Array.fromList(map actionRowLookUp actionRowNumbers)
end
in LrTable.mkLrTable {actions=actionT,gotos=gotoT,numRules=numrules,
numStates=numstates,initialState=STATE 0}
end
end
local open Header in
type pos = SourcePos.t
type arg = SourceFile.t
structure MlyValue = 
struct
datatype svalue = VOID' | ntVOID of unit ->  unit
 | STRING_LITERAL of unit ->  (string)
 | NUMERIC_CONSTANT of unit ->  (Absyn.numliteral_info)
 | TYPEID of unit ->  (string) | ID of unit ->  (string)
 | calls_block of unit ->  (string wrap list option)
 | namedstringexplist1 of unit ->  (namedstringexp list)
 | namedstringexplist of unit ->  (namedstringexp list)
 | namedstringexp of unit ->  (namedstringexp)
 | stringlist1 of unit ->  (string list)
 | cstring_literal of unit ->  (string wrap)
 | asmmod3 of unit ->  (string list)
 | asmmod2 of unit ->  (namedstringexp list*string list)
 | asmmod1 of unit ->  (namedstringexp list*namedstringexp list*string list)
 | asmblock of unit ->  (asmblock)
 | attribute_parameter_list1 of unit ->  (expr list)
 | attribute_list of unit ->  (gcc_attribute list)
 | attribute_specifier of unit ->  (gcc_attribute list wrap)
 | attribute of unit ->  (gcc_attribute option)
 | idlist of unit ->  (string wrap list)
 | constant of unit ->  (literalconstant)
 | primary_expression of unit ->  (expr)
 | postfix_expression of unit ->  (expr)
 | cast_expression of unit ->  (expr)
 | unary_expression of unit ->  (expr)
 | multiplicative_expression of unit ->  (expr)
 | shift_expression of unit ->  (expr)
 | additive_expression of unit ->  (expr)
 | relational_expression of unit ->  (expr)
 | equality_expression of unit ->  (expr)
 | AND_expression of unit ->  (expr)
 | exclusive_OR_expression of unit ->  (expr)
 | inclusive_OR_expression of unit ->  (expr)
 | logical_OR_expression of unit ->  (expr)
 | logical_AND_expression of unit ->  (expr)
 | opt_rexpr_list of unit ->  (expr list wrap)
 | rexpr_list of unit ->  (expr list wrap)
 | rexpression of unit ->  (expr) | lexpression of unit ->  (expr)
 | struct_id of unit ->  (string wrap)
 | struct_or_union_specifier of unit ->  (struct_or_union_specifier)
 | type_specifier of unit ->  (type_specifier)
 | asm_declarator_mod of unit ->  (unit)
 | direct_declarator of unit ->  (addecl wrap)
 | init_declarator_list of unit ->  ( ( addecl wrap * initializer option )  wrap list)
 | init_declarator of unit ->  ( ( addecl wrap * initializer option )  wrap)
 | struct_declarator_list of unit ->  ( ( addecl wrap * expr option )  list wrap)
 | struct_declarator of unit ->  ( ( addecl wrap * expr option )  wrap)
 | direct_abstract_declarator of unit ->  (adecl)
 | abstract_declarator of unit ->  (adecl)
 | declarator of unit ->  (addecl wrap) | pointer of unit ->  (adecl)
 | assignop of unit ->  (binoptype option)
 | opt_for3_exprbase of unit ->  (statement)
 | opt_for3_expr0 of unit ->  (statement list)
 | opt_for3_expr of unit ->  (statement)
 | opt_for2_expr of unit ->  (expr)
 | opt_for1_exprbase of unit ->  (statement)
 | opt_for1_expr0 of unit ->  (statement list)
 | opt_for1_expr of unit ->  (statement)
 | opt_for1_bitem of unit ->  (block_item list)
 | label of unit ->  (expr option wrap)
 | labellist of unit ->  (expr option wrap list wrap)
 | switchcase of unit ->  ( ( expr option wrap list wrap * block_item list ) )
 | switchcase_list of unit ->  ( ( expr option wrap list wrap * block_item list )  list)
 | statement_list1 of unit ->  (statement list)
 | statement_list of unit ->  (statement list)
 | statement of unit ->  (statement)
 | compound_statement of unit ->  (block_item list wrap)
 | function_definition of unit ->  (ext_decl)
 | parameter_list1 of unit ->  ( ( expr ctype  * string wrap option )  wrap list wrap)
 | parameter_list of unit ->  ( ( expr ctype * string wrap option )  wrap list wrap)
 | parameter_declaration of unit ->  ( ( expr ctype * string wrap option )  wrap)
 | block_item of unit ->  (block_item list)
 | block_item_list of unit ->  (block_item list)
 | type_name of unit ->  (expr ctype wrap)
 | integral_type of unit ->  (inttype wrap)
 | elementary_type of unit ->  (expr ctype)
 | type_definition of unit ->  (declaration)
 | struct_declaration of unit ->  (struct_fields wrap*struct_id_decl wrap list)
 | struct_declaration_list of unit ->  (struct_fields wrap*struct_id_decl wrap list)
 | declaration of unit ->  (declaration wrap list)
 | designator of unit ->  (designator)
 | designator_list of unit ->  (designator list)
 | designation of unit ->  (designator list)
 | initializer of unit ->  (initializer wrap)
 | dinitializer of unit ->  ( ( designator list * initializer ) )
 | initializer_list of unit ->  ( ( designator list * initializer )  list)
 | specifier_qualifier_list of unit ->  (decl_specifier list wrap)
 | declaration_specifiers of unit ->  (decl_specifier list wrap)
 | invariant_option of unit ->  (string wrap option)
 | invariant of unit ->  (string wrap)
 | modlist of unit ->  (string wrap list)
 | rel_spec of unit ->  (string wrap)
 | fnspecs of unit ->  (string wrap)
 | special_function_specs of unit ->  (fnspec wrap list wrap)
 | special_function_spec of unit ->  (fnspec wrap)
 | function_specifiers of unit ->  (fnspec wrap list wrap)
 | type_qualifier_list of unit ->  (type_qualifier wrap list)
 | type_qualifier of unit ->  (type_qualifier wrap)
 | enumerator of unit ->  ( ( string wrap * expr option ) )
 | enumerator_list of unit ->  ( ( string wrap * expr option )  list)
 | enum_specifier of unit ->  (enum_specifier)
 | storage_class_specifier of unit ->  (storage_class_specifier wrap)
 | optvolatile of unit ->  (bool)
 | optfnspec of unit ->  (string option wrap)
 | external_declaration of unit ->  (ext_decl list)
 | translation_unit of unit ->  (ext_decl list)
 | begin of unit ->  (ext_decl list)
end
type svalue = MlyValue.svalue
type result = ext_decl list
end
structure EC=
struct
open LrTable
val is_keyword =
fn (T 37) => true | (T 38) => true | (T 35) => true | (T 71) => true
 | (T 39) => true | (T 36) => true | (T 59) => true | (T 61) => true
 | (T 62) => true | (T 63) => true | (T 65) => true | (T 73) => true
 | (T 11) => true | (T 6) => true | (T 7) => true | _ => false
val preferred_change = 
(nil
,(T 11) :: nil
)::
nil
val noShift = 
fn (T 0) => true | _ => false
val showTerminal =
fn (T 0) => "EOF"
  | (T 1) => "YSTAR"
  | (T 2) => "SLASH"
  | (T 3) => "MOD"
  | (T 4) => "LPAREN"
  | (T 5) => "RPAREN"
  | (T 6) => "LCURLY"
  | (T 7) => "RCURLY"
  | (T 8) => "LBRACKET"
  | (T 9) => "RBRACKET"
  | (T 10) => "YCOMMA"
  | (T 11) => "YSEMI"
  | (T 12) => "YCOLON"
  | (T 13) => "QMARK"
  | (T 14) => "YEQ"
  | (T 15) => "YDOT"
  | (T 16) => "YPLUS"
  | (T 17) => "YMINUS"
  | (T 18) => "YAND"
  | (T 19) => "YNOT"
  | (T 20) => "YAMPERSAND"
  | (T 21) => "YBITNOT"
  | (T 22) => "PLUSPLUS"
  | (T 23) => "MINUSMINUS"
  | (T 24) => "PLUSEQ"
  | (T 25) => "MINUSEQ"
  | (T 26) => "BANDEQ"
  | (T 27) => "BOREQ"
  | (T 28) => "MULEQ"
  | (T 29) => "DIVEQ"
  | (T 30) => "MODEQ"
  | (T 31) => "BXOREQ"
  | (T 32) => "LSHIFTEQ"
  | (T 33) => "RSHIFTEQ"
  | (T 34) => "YENUM"
  | (T 35) => "YIF"
  | (T 36) => "YELSE"
  | (T 37) => "YWHILE"
  | (T 38) => "YDO"
  | (T 39) => "YRETURN"
  | (T 40) => "YBREAK"
  | (T 41) => "YCONTINUE"
  | (T 42) => "YFOR"
  | (T 43) => "SWITCH"
  | (T 44) => "CASE"
  | (T 45) => "DEFAULT"
  | (T 46) => "YSIZEOF"
  | (T 47) => "LOGICALOR"
  | (T 48) => "LOGICALAND"
  | (T 49) => "BITWISEOR"
  | (T 50) => "BITWISEXOR"
  | (T 51) => "EQUALS"
  | (T 52) => "NOTEQUALS"
  | (T 53) => "YLE"
  | (T 54) => "YGE"
  | (T 55) => "YLESS"
  | (T 56) => "YGREATER"
  | (T 57) => "LEFTSHIFT"
  | (T 58) => "RIGHTSHIFT"
  | (T 59) => "INT"
  | (T 60) => "BOOL"
  | (T 61) => "CHAR"
  | (T 62) => "LONG"
  | (T 63) => "SHORT"
  | (T 64) => "SIGNED"
  | (T 65) => "UNSIGNED"
  | (T 66) => "VOID"
  | (T 67) => "ARROW"
  | (T 68) => "ID"
  | (T 69) => "TYPEID"
  | (T 70) => "NUMERIC_CONSTANT"
  | (T 71) => "STRUCT"
  | (T 72) => "UNION"
  | (T 73) => "TYPEDEF"
  | (T 74) => "EXTERN"
  | (T 75) => "CONST"
  | (T 76) => "VOLATILE"
  | (T 77) => "RESTRICT"
  | (T 78) => "INVARIANT"
  | (T 79) => "INLINE"
  | (T 80) => "STATIC"
  | (T 81) => "FNSPEC"
  | (T 82) => "RELSPEC"
  | (T 83) => "AUXUPD"
  | (T 84) => "GHOSTUPD"
  | (T 85) => "MODIFIES"
  | (T 86) => "CALLS"
  | (T 87) => "OWNED_BY"
  | (T 88) => "SPEC_BEGIN"
  | (T 89) => "SPEC_END"
  | (T 90) => "DONT_TRANSLATE"
  | (T 91) => "STRING_LITERAL"
  | (T 92) => "SPEC_BLOCKEND"
  | (T 93) => "GCC_ATTRIBUTE"
  | (T 94) => "YASM"
  | (T 95) => "YREGISTER"
  | _ => "bogus-term"
local open Header in
val errtermvalue=
fn _ => MlyValue.VOID'
end
val terms = (T 0) :: (T 1) :: (T 2) :: (T 3) :: (T 4) :: (T 5) :: (T 6
) :: (T 7) :: (T 8) :: (T 9) :: (T 10) :: (T 11) :: (T 12) :: (T 13)
 :: (T 14) :: (T 15) :: (T 16) :: (T 17) :: (T 18) :: (T 19) :: (T 20)
 :: (T 21) :: (T 22) :: (T 23) :: (T 24) :: (T 25) :: (T 26) :: (T 27)
 :: (T 28) :: (T 29) :: (T 30) :: (T 31) :: (T 32) :: (T 33) :: (T 34)
 :: (T 35) :: (T 36) :: (T 37) :: (T 38) :: (T 39) :: (T 40) :: (T 41)
 :: (T 42) :: (T 43) :: (T 44) :: (T 45) :: (T 46) :: (T 47) :: (T 48)
 :: (T 49) :: (T 50) :: (T 51) :: (T 52) :: (T 53) :: (T 54) :: (T 55)
 :: (T 56) :: (T 57) :: (T 58) :: (T 59) :: (T 60) :: (T 61) :: (T 62)
 :: (T 63) :: (T 64) :: (T 65) :: (T 66) :: (T 67) :: (T 71) :: (T 72)
 :: (T 73) :: (T 74) :: (T 75) :: (T 76) :: (T 77) :: (T 78) :: (T 79)
 :: (T 80) :: (T 81) :: (T 82) :: (T 83) :: (T 84) :: (T 85) :: (T 86)
 :: (T 87) :: (T 88) :: (T 89) :: (T 90) :: (T 92) :: (T 93) :: (T 94)
 :: (T 95) :: nil
end
structure Actions =
struct 
type int = Int.int
exception mlyAction of int
local open Header in
val actions = 
fn (i392:int,defaultPos,stack,
    (source):arg) =>
case (i392,stack)
of (0,(_,(MlyValue.translation_unit translation_unit1,
translation_unit1left,translation_unit1right))::rest671) => let val 
result=MlyValue.begin(fn _ => let val translation_unit as 
translation_unit1=translation_unit1 ()
 in (translation_unit) end
)
 in (LrTable.NT 0,(result,translation_unit1left,translation_unit1right
),rest671) end
| (1,(_,(MlyValue.external_declaration external_declaration1,
external_declaration1left,external_declaration1right))::rest671) => 
let val result=MlyValue.translation_unit(fn _ => let val 
external_declaration as external_declaration1=external_declaration1 ()
 in (external_declaration) end
)
 in (LrTable.NT 1,(result,external_declaration1left,
external_declaration1right),rest671) end
| (2,(_,(MlyValue.translation_unit translation_unit1,_,
translation_unit1right))::(_,(MlyValue.external_declaration 
external_declaration1,external_declaration1left,_))::rest671) => let 
val result=MlyValue.translation_unit(fn _ => let val 
external_declaration as external_declaration1=external_declaration1 ()
val translation_unit as translation_unit1=translation_unit1 ()
 in (external_declaration @ translation_unit) end
)
 in (LrTable.NT 1,(result,external_declaration1left,
translation_unit1right),rest671) end
| (3,(_,(MlyValue.function_definition function_definition1,
function_definition1left,function_definition1right))::rest671) => let 
val result=MlyValue.external_declaration(fn _ => let val 
function_definition as function_definition1=function_definition1 ()
 in ([function_definition]) end
)
 in (LrTable.NT 2,(result,function_definition1left,
function_definition1right),rest671) end
| (4,(_,(MlyValue.declaration declaration1,declaration1left,
declaration1right))::rest671) => let val result=
MlyValue.external_declaration(fn _ => let val declaration as 
declaration1=declaration1 ()
 in (map Decl declaration) end
)
 in (LrTable.NT 2,(result,declaration1left,declaration1right),rest671)
 end
| (5,(_,(_,TYPEDEFleft as TYPEDEF1left,TYPEDEFright as TYPEDEF1right))
::rest671) => let val result=MlyValue.storage_class_specifier(fn _ => 
(wrap(TypeDef, TYPEDEFleft, TYPEDEFright)))
 in (LrTable.NT 5,(result,TYPEDEF1left,TYPEDEF1right),rest671) end
| (6,(_,(_,EXTERNleft as EXTERN1left,EXTERNright as EXTERN1right))::
rest671) => let val result=MlyValue.storage_class_specifier(fn _ => (
wrap(Extern, EXTERNleft, EXTERNright)))
 in (LrTable.NT 5,(result,EXTERN1left,EXTERN1right),rest671) end
| (7,(_,(_,STATICleft as STATIC1left,STATICright as STATIC1right))::
rest671) => let val result=MlyValue.storage_class_specifier(fn _ => (
wrap(Static, STATICleft, STATICright)))
 in (LrTable.NT 5,(result,STATIC1left,STATIC1right),rest671) end
| (8,(_,(_,YREGISTERleft as YREGISTER1left,YREGISTERright as 
YREGISTER1right))::rest671) => let val result=
MlyValue.storage_class_specifier(fn _ => (
wrap(Register, YREGISTERleft, YREGISTERright)))
 in (LrTable.NT 5,(result,YREGISTER1left,YREGISTER1right),rest671) end
| (9,(_,(_,INLINEleft as INLINE1left,INLINEright as INLINE1right))::
rest671) => let val result=MlyValue.function_specifiers(fn _ => (
wrap([], INLINEleft, INLINEright)))
 in (LrTable.NT 11,(result,INLINE1left,INLINE1right),rest671) end
| (10,(_,(_,_,SPEC_BLOCKEND1right))::(_,(
MlyValue.special_function_specs special_function_specs1,
special_function_specs1left,_))::rest671) => let val result=
MlyValue.function_specifiers(fn _ => let val special_function_specs
 as special_function_specs1=special_function_specs1 ()
 in (special_function_specs) end
)
 in (LrTable.NT 11,(result,special_function_specs1left,
SPEC_BLOCKEND1right),rest671) end
| (11,(_,(MlyValue.attribute_specifier attribute_specifier1,
attribute_specifier1left,attribute_specifier1right))::rest671) => let 
val result=MlyValue.function_specifiers(fn _ => let val 
attribute_specifier as attribute_specifier1=attribute_specifier1 ()
 in (
wrap ([apnode gcc_attribs attribute_specifier],
                       left attribute_specifier,
                       right attribute_specifier)
) end
)
 in (LrTable.NT 11,(result,attribute_specifier1left,
attribute_specifier1right),rest671) end
| (12,(_,(_,_,RPAREN2right))::_::(_,(MlyValue.attribute_list 
attribute_list1,_,_))::_::_::(_,(_,GCC_ATTRIBUTEleft as 
GCC_ATTRIBUTE1left,_))::rest671) => let val result=
MlyValue.attribute_specifier(fn _ => let val attribute_list as 
attribute_list1=attribute_list1 ()
 in (wrap(attribute_list, GCC_ATTRIBUTEleft, RPAREN2right)) end
)
 in (LrTable.NT 91,(result,GCC_ATTRIBUTE1left,RPAREN2right),rest671)
 end
| (13,(_,(_,_,SPEC_BLOCKENDright as SPEC_BLOCKEND1right))::(_,(
MlyValue.ID ID1,_,_))::(_,(_,OWNED_BYleft as OWNED_BY1left,_))::
rest671) => let val result=MlyValue.attribute_specifier(fn _ => let 
val ID as ID1=ID1 ()
 in (wrap([OWNED_BY ID], OWNED_BYleft, SPEC_BLOCKENDright)) end
)
 in (LrTable.NT 91,(result,OWNED_BY1left,SPEC_BLOCKEND1right),rest671)
 end
| (14,rest671) => let val result=MlyValue.attribute_list(fn _ => ([]))
 in (LrTable.NT 92,(result,defaultPos,defaultPos),rest671) end
| (15,(_,(MlyValue.attribute attribute1,attribute1left,attribute1right
))::rest671) => let val result=MlyValue.attribute_list(fn _ => let 
val attribute as attribute1=attribute1 ()
 in (case attribute of NONE => [] | SOME a => [a]) end
)
 in (LrTable.NT 92,(result,attribute1left,attribute1right),rest671)
 end
| (16,(_,(MlyValue.attribute_list attribute_list1,_,
attribute_list1right))::_::(_,(MlyValue.attribute attribute1,
attribute1left,_))::rest671) => let val result=MlyValue.attribute_list
(fn _ => let val attribute as attribute1=attribute1 ()
val attribute_list as attribute_list1=attribute_list1 ()
 in (
case attribute of NONE => attribute_list
                                 | SOME a => a :: attribute_list
) end
)
 in (LrTable.NT 92,(result,attribute1left,attribute_list1right),
rest671) end
| (17,(_,(MlyValue.ID ID1,ID1left,ID1right))::rest671) => let val 
result=MlyValue.attribute(fn _ => let val ID as ID1=ID1 ()
 in (
let val idstr = if String.isPrefix "__" ID andalso
                                    String.sub(ID,size ID - 1) = #"_" andalso
                                    String.sub(ID,size ID - 2) = #"_" andalso
                                    size ID > 4
                                 then
                                   String.substring(ID,2,size ID - 4)
                                 else ID
                 in
                   SOME (GCC_AttribID idstr)
                 end
) end
)
 in (LrTable.NT 90,(result,ID1left,ID1right),rest671) end
| (18,(_,(_,_,RPAREN1right))::_::(_,(MlyValue.ID ID1,ID1left,_))::
rest671) => let val result=MlyValue.attribute(fn _ => let val ID as 
ID1=ID1 ()
 in (SOME (GCC_AttribFn (ID, []))) end
)
 in (LrTable.NT 90,(result,ID1left,RPAREN1right),rest671) end
| (19,(_,(_,_,RPAREN1right))::(_,(MlyValue.attribute_parameter_list1 
attribute_parameter_list11,_,_))::_::(_,(MlyValue.ID ID1,ID1left,_))::
rest671) => let val result=MlyValue.attribute(fn _ => let val ID as 
ID1=ID1 ()
val attribute_parameter_list1 as attribute_parameter_list11=
attribute_parameter_list11 ()
 in (SOME (GCC_AttribFn (ID, attribute_parameter_list1))) end
)
 in (LrTable.NT 90,(result,ID1left,RPAREN1right),rest671) end
| (20,(_,(MlyValue.rexpression rexpression1,rexpression1left,
rexpression1right))::rest671) => let val result=
MlyValue.attribute_parameter_list1(fn _ => let val rexpression as 
rexpression1=rexpression1 ()
 in ([rexpression]) end
)
 in (LrTable.NT 93,(result,rexpression1left,rexpression1right),rest671
) end
| (21,(_,(MlyValue.attribute_parameter_list1 
attribute_parameter_list11,_,attribute_parameter_list11right))::_::(_,
(MlyValue.rexpression rexpression1,rexpression1left,_))::rest671) => 
let val result=MlyValue.attribute_parameter_list1(fn _ => let val 
rexpression as rexpression1=rexpression1 ()
val attribute_parameter_list1 as attribute_parameter_list11=
attribute_parameter_list11 ()
 in (rexpression :: attribute_parameter_list1) end
)
 in (LrTable.NT 93,(result,rexpression1left,
attribute_parameter_list11right),rest671) end
| (22,(_,(MlyValue.special_function_spec special_function_spec1,
special_function_spec1left,special_function_spec1right))::rest671) => 
let val result=MlyValue.special_function_specs(fn _ => let val 
special_function_spec as special_function_spec1=special_function_spec1
 ()
 in (
wrap([special_function_spec], left special_function_spec,
                      right special_function_spec)
) end
)
 in (LrTable.NT 13,(result,special_function_spec1left,
special_function_spec1right),rest671) end
| (23,(_,(MlyValue.special_function_specs special_function_specs1,_,
special_function_specs1right))::(_,(MlyValue.special_function_spec 
special_function_spec1,special_function_spec1left,_))::rest671) => 
let val result=MlyValue.special_function_specs(fn _ => let val 
special_function_spec as special_function_spec1=special_function_spec1
 ()
val special_function_specs as special_function_specs1=
special_function_specs1 ()
 in (
wrap (special_function_spec :: node special_function_specs,
                       left special_function_spec,
                       right special_function_specs)
) end
)
 in (LrTable.NT 13,(result,special_function_spec1left,
special_function_specs1right),rest671) end
| (24,(_,(MlyValue.idlist idlist1,_,idlist1right))::(_,(_,MODIFIESleft
 as MODIFIES1left,MODIFIESright))::rest671) => let val result=
MlyValue.special_function_spec(fn _ => let val idlist as idlist1=
idlist1 ()
 in (
case idlist of
                     [] => wrap(fn_modifies [], MODIFIESleft, MODIFIESright)
                   | _ => wrap(fn_modifies (map node idlist),
                               MODIFIESleft,
                               right (List.last idlist))
) end
)
 in (LrTable.NT 12,(result,MODIFIES1left,idlist1right),rest671) end
| (25,(_,(MlyValue.fnspecs fnspecs1,_,fnspecs1right))::(_,(_,
FNSPECleft as FNSPEC1left,_))::rest671) => let val result=
MlyValue.special_function_spec(fn _ => let val fnspecs as fnspecs1=
fnspecs1 ()
 in (wrap(fnspec fnspecs, FNSPECleft, right fnspecs)) end
)
 in (LrTable.NT 12,(result,FNSPEC1left,fnspecs1right),rest671) end
| (26,(_,(MlyValue.rel_spec rel_spec1,_,rel_spec1right))::(_,(_,
RELSPECleft as RELSPEC1left,_))::rest671) => let val result=
MlyValue.special_function_spec(fn _ => let val rel_spec as rel_spec1=
rel_spec1 ()
 in (wrap(relspec rel_spec, RELSPECleft, right rel_spec)) end
)
 in (LrTable.NT 12,(result,RELSPEC1left,rel_spec1right),rest671) end
| (27,(_,(_,DONT_TRANSLATEleft as DONT_TRANSLATE1left,
DONT_TRANSLATEright as DONT_TRANSLATE1right))::rest671) => let val 
result=MlyValue.special_function_spec(fn _ => (
wrap(didnt_translate, DONT_TRANSLATEleft, DONT_TRANSLATEright)))
 in (LrTable.NT 12,(result,DONT_TRANSLATE1left,DONT_TRANSLATE1right),
rest671) end
| (28,(_,(MlyValue.STRING_LITERAL STRING_LITERAL1,_,
STRING_LITERALright as STRING_LITERAL1right))::_::(_,(MlyValue.ID ID1,
IDleft as ID1left,_))::rest671) => let val result=MlyValue.fnspecs(fn 
_ => let val ID as ID1=ID1 ()
val STRING_LITERAL as STRING_LITERAL1=STRING_LITERAL1 ()
 in (
wrap(ID ^ ": \"" ^ STRING_LITERAL ^ "\"", IDleft,
                      STRING_LITERALright)
) end
)
 in (LrTable.NT 14,(result,ID1left,STRING_LITERAL1right),rest671) end
| (29,(_,(MlyValue.fnspecs fnspecs1,_,fnspecs1right))::(_,(
MlyValue.STRING_LITERAL STRING_LITERAL1,_,_))::_::(_,(MlyValue.ID ID1,
IDleft as ID1left,_))::rest671) => let val result=MlyValue.fnspecs(fn 
_ => let val ID as ID1=ID1 ()
val STRING_LITERAL as STRING_LITERAL1=STRING_LITERAL1 ()
val fnspecs as fnspecs1=fnspecs1 ()
 in (
wrap((ID ^ ": \"" ^ STRING_LITERAL ^ "\"\n" ^ node fnspecs,
                      IDleft,
                      right fnspecs))
) end
)
 in (LrTable.NT 14,(result,ID1left,fnspecs1right),rest671) end
| (30,(_,(MlyValue.STRING_LITERAL STRING_LITERAL1,STRING_LITERALleft
 as STRING_LITERAL1left,STRING_LITERALright as STRING_LITERAL1right))
::rest671) => let val result=MlyValue.rel_spec(fn _ => let val 
STRING_LITERAL as STRING_LITERAL1=STRING_LITERAL1 ()
 in (
wrap("\"" ^ STRING_LITERAL ^ "\"", STRING_LITERALleft,
                       STRING_LITERALright)
) end
)
 in (LrTable.NT 15,(result,STRING_LITERAL1left,STRING_LITERAL1right),
rest671) end
| (31,rest671) => let val result=MlyValue.idlist(fn _ => ([]))
 in (LrTable.NT 89,(result,defaultPos,defaultPos),rest671) end
| (32,(_,(MlyValue.idlist idlist1,_,idlist1right))::(_,(MlyValue.ID 
ID1,IDleft as ID1left,IDright))::rest671) => let val result=
MlyValue.idlist(fn _ => let val ID as ID1=ID1 ()
val idlist as idlist1=idlist1 ()
 in (wrap(ID,IDleft,IDright) :: idlist) end
)
 in (LrTable.NT 89,(result,ID1left,idlist1right),rest671) end
| (33,(_,(MlyValue.idlist idlist1,_,idlist1right))::(_,(_,_,
RBRACKETright))::_::(_,(_,LBRACKETleft as LBRACKET1left,_))::rest671)
 => let val result=MlyValue.idlist(fn _ => let val idlist as idlist1=
idlist1 ()
 in (
wrap(NameGeneration.phantom_state_name, LBRACKETleft,
                      RBRACKETright) :: idlist
) end
)
 in (LrTable.NT 89,(result,LBRACKET1left,idlist1right),rest671) end
| (34,(_,(_,_,YSEMI1right))::(_,(MlyValue.declaration_specifiers 
declaration_specifiers1,declaration_specifiers1left,_))::rest671) => 
let val result=MlyValue.declaration(fn _ => let val 
declaration_specifiers as declaration_specifiers1=
declaration_specifiers1 ()
 in (empty_declarator (node declaration_specifiers)) end
)
 in (LrTable.NT 27,(result,declaration_specifiers1left,YSEMI1right),
rest671) end
| (35,(_,(_,_,YSEMI1right))::(_,(MlyValue.init_declarator_list 
init_declarator_list1,_,_))::(_,(MlyValue.declaration_specifiers 
declaration_specifiers1,declaration_specifiers1left,_))::rest671) => 
let val result=MlyValue.declaration(fn _ => let val 
declaration_specifiers as declaration_specifiers1=
declaration_specifiers1 ()
val init_declarator_list as init_declarator_list1=
init_declarator_list1 ()
 in (make_declaration declaration_specifiers init_declarator_list) end
)
 in (LrTable.NT 27,(result,declaration_specifiers1left,YSEMI1right),
rest671) end
| (36,(_,(MlyValue.storage_class_specifier storage_class_specifier1,
storage_class_specifier1left,storage_class_specifier1right))::rest671)
 => let val result=MlyValue.declaration_specifiers(fn _ => let val 
storage_class_specifier as storage_class_specifier1=
storage_class_specifier1 ()
 in (
wrap([Storage storage_class_specifier],
                      left storage_class_specifier,
                      right storage_class_specifier)
) end
)
 in (LrTable.NT 19,(result,storage_class_specifier1left,
storage_class_specifier1right),rest671) end
| (37,(_,(MlyValue.declaration_specifiers declaration_specifiers1,_,
declaration_specifiers1right))::(_,(MlyValue.storage_class_specifier 
storage_class_specifier1,storage_class_specifier1left,_))::rest671)
 => let val result=MlyValue.declaration_specifiers(fn _ => let val 
storage_class_specifier as storage_class_specifier1=
storage_class_specifier1 ()
val declaration_specifiers as declaration_specifiers1=
declaration_specifiers1 ()
 in (
wrap(Storage storage_class_specifier ::
                      node declaration_specifiers,
                      left storage_class_specifier,
                      right declaration_specifiers)
) end
)
 in (LrTable.NT 19,(result,storage_class_specifier1left,
declaration_specifiers1right),rest671) end
| (38,(_,(MlyValue.type_specifier type_specifier1,type_specifier1left,
type_specifier1right))::rest671) => let val result=
MlyValue.declaration_specifiers(fn _ => let val type_specifier as 
type_specifier1=type_specifier1 ()
 in (
wrap([TypeSpec type_specifier], tsleft type_specifier,
                      tsright type_specifier)
) end
)
 in (LrTable.NT 19,(result,type_specifier1left,type_specifier1right),
rest671) end
| (39,(_,(MlyValue.declaration_specifiers declaration_specifiers1,_,
declaration_specifiers1right))::(_,(MlyValue.type_specifier 
type_specifier1,type_specifier1left,_))::rest671) => let val result=
MlyValue.declaration_specifiers(fn _ => let val type_specifier as 
type_specifier1=type_specifier1 ()
val declaration_specifiers as declaration_specifiers1=
declaration_specifiers1 ()
 in (
wrap(TypeSpec type_specifier :: node declaration_specifiers,
                      tsleft type_specifier,
                      right declaration_specifiers)
) end
)
 in (LrTable.NT 19,(result,type_specifier1left,
declaration_specifiers1right),rest671) end
| (40,(_,(MlyValue.type_qualifier type_qualifier1,type_qualifier1left,
type_qualifier1right))::rest671) => let val result=
MlyValue.declaration_specifiers(fn _ => let val type_qualifier as 
type_qualifier1=type_qualifier1 ()
 in (
wrap([TypeQual type_qualifier],
                      left type_qualifier,
                      right type_qualifier)
) end
)
 in (LrTable.NT 19,(result,type_qualifier1left,type_qualifier1right),
rest671) end
| (41,(_,(MlyValue.declaration_specifiers declaration_specifiers1,_,
declaration_specifiers1right))::(_,(MlyValue.type_qualifier 
type_qualifier1,type_qualifier1left,_))::rest671) => let val result=
MlyValue.declaration_specifiers(fn _ => let val type_qualifier as 
type_qualifier1=type_qualifier1 ()
val declaration_specifiers as declaration_specifiers1=
declaration_specifiers1 ()
 in (
wrap(TypeQual type_qualifier :: node declaration_specifiers,
                      left type_qualifier,
                      right declaration_specifiers)
) end
)
 in (LrTable.NT 19,(result,type_qualifier1left,
declaration_specifiers1right),rest671) end
| (42,(_,(MlyValue.function_specifiers function_specifiers1,
function_specifiers1left,function_specifiers1right))::rest671) => let 
val result=MlyValue.declaration_specifiers(fn _ => let val 
function_specifiers as function_specifiers1=function_specifiers1 ()
 in (
wrap(map FunSpec (node function_specifiers),
                      left function_specifiers,
                      right function_specifiers)
) end
)
 in (LrTable.NT 19,(result,function_specifiers1left,
function_specifiers1right),rest671) end
| (43,(_,(MlyValue.declaration_specifiers declaration_specifiers1,_,
declaration_specifiers1right))::(_,(MlyValue.function_specifiers 
function_specifiers1,function_specifiers1left,_))::rest671) => let 
val result=MlyValue.declaration_specifiers(fn _ => let val 
function_specifiers as function_specifiers1=function_specifiers1 ()
val declaration_specifiers as declaration_specifiers1=
declaration_specifiers1 ()
 in (
wrap(map FunSpec (node function_specifiers) @
                      node declaration_specifiers,
                      left function_specifiers,
                      right declaration_specifiers)
) end
)
 in (LrTable.NT 19,(result,function_specifiers1left,
declaration_specifiers1right),rest671) end
| (44,(_,(MlyValue.compound_statement compound_statement1,_,
compound_statement1right))::(_,(MlyValue.declarator declarator1,_,
declaratorright))::(_,(MlyValue.declaration_specifiers 
declaration_specifiers1,declaration_specifiersleft as 
declaration_specifiers1left,_))::rest671) => let val result=
MlyValue.function_definition(fn _ => let val declaration_specifiers
 as declaration_specifiers1=declaration_specifiers1 ()
val declarator as declarator1=declarator1 ()
val compound_statement as compound_statement1=compound_statement1 ()
 in (
let val basetype = extract_type declaration_specifiers
             val fnspecs = extract_fnspecs (node declaration_specifiers)
             val _ =
                 case has_typedef declaration_specifiers of
                   NONE => ()
                 | SOME (l,r) =>
                    errorStr'(l, r, "Typedef illegal in function def")
             val (nm, ad, params0, attrs) = node declarator
             val params =
                 case params0 of
                   NONE => (errorStr'(left declarator,
                                      right declarator,
                                      "Function def with no params!");
                            [])
                 | SOME ps => check_names (node nm) ps
             val rettype = case (node ad) (node basetype) of
                             Function(retty, _) => retty
                           | _ => (errorStr'(left declarator,
                                             right compound_statement,
                                             "Attempted fn def with bad \
                                             \declarator");
                                   node basetype)
             val fnspecs = merge_specs [gcc_attribs attrs] fnspecs
         in
           if List.exists (fn fs => fs = didnt_translate) fnspecs then
             Decl (wrap(ExtFnDecl{rettype = rettype,
                                  params = unwrap_params params0,
                                  name = nm,
                                  specs = fnspecs},
                        declaration_specifiersleft,
                        declaratorright))
           else
             FnDefn((rettype, nm), params, fnspecs, compound_statement)
         end
) end
)
 in (LrTable.NT 39,(result,declaration_specifiers1left,
compound_statement1right),rest671) end
| (45,rest671) => let val result=MlyValue.parameter_list(fn _ => (
wrap([], defaultPos, defaultPos)))
 in (LrTable.NT 37,(result,defaultPos,defaultPos),rest671) end
| (46,(_,(MlyValue.parameter_list1 parameter_list11,
parameter_list11left,parameter_list11right))::rest671) => let val 
result=MlyValue.parameter_list(fn _ => let val parameter_list1 as 
parameter_list11=parameter_list11 ()
 in (parameter_list1) end
)
 in (LrTable.NT 37,(result,parameter_list11left,parameter_list11right)
,rest671) end
| (47,(_,(MlyValue.parameter_declaration parameter_declaration1,
parameter_declaration1left,parameter_declaration1right))::rest671) => 
let val result=MlyValue.parameter_list1(fn _ => let val 
parameter_declaration as parameter_declaration1=parameter_declaration1
 ()
 in (
wrap([parameter_declaration], left parameter_declaration,
                      right parameter_declaration)
) end
)
 in (LrTable.NT 38,(result,parameter_declaration1left,
parameter_declaration1right),rest671) end
| (48,(_,(MlyValue.parameter_list1 parameter_list11,_,
parameter_list11right))::_::(_,(MlyValue.parameter_declaration 
parameter_declaration1,parameter_declaration1left,_))::rest671) => 
let val result=MlyValue.parameter_list1(fn _ => let val 
parameter_declaration as parameter_declaration1=parameter_declaration1
 ()
val parameter_list1 as parameter_list11=parameter_list11 ()
 in (
wrap(parameter_declaration :: node parameter_list1,
                      left parameter_declaration, right parameter_list1)
) end
)
 in (LrTable.NT 38,(result,parameter_declaration1left,
parameter_list11right),rest671) end
| (49,(_,(MlyValue.declarator declarator1,_,declarator1right))::(_,(
MlyValue.declaration_specifiers declaration_specifiers1,
declaration_specifiers1left,_))::rest671) => let val result=
MlyValue.parameter_declaration(fn _ => let val declaration_specifiers
 as declaration_specifiers1=declaration_specifiers1 ()
val declarator as declarator1=declarator1 ()
 in (
let val basety = extract_type declaration_specifiers
                     val _ = wonky_pdec_check declaration_specifiers
                     val (nm, a, _, _) = node declarator
                 in
                   wrap((node a (node basety), SOME nm),
                        left declaration_specifiers,
                        right declarator)
                 end
) end
)
 in (LrTable.NT 36,(result,declaration_specifiers1left,
declarator1right),rest671) end
| (50,(_,(MlyValue.abstract_declarator abstract_declarator1,_,
abstract_declarator1right))::(_,(MlyValue.declaration_specifiers 
declaration_specifiers1,declaration_specifiers1left,_))::rest671) => 
let val result=MlyValue.parameter_declaration(fn _ => let val 
declaration_specifiers as declaration_specifiers1=
declaration_specifiers1 ()
val abstract_declarator as abstract_declarator1=abstract_declarator1 
()
 in (
let val basety = extract_type declaration_specifiers
                     val _ = wonky_pdec_check declaration_specifiers
                     val a = node abstract_declarator
                 in
                   wrap((a (node basety), NONE),
                        left declaration_specifiers,
                        right abstract_declarator)
                 end
) end
)
 in (LrTable.NT 36,(result,declaration_specifiers1left,
abstract_declarator1right),rest671) end
| (51,(_,(MlyValue.declaration_specifiers declaration_specifiers1,
declaration_specifiers1left,declaration_specifiers1right))::rest671)
 => let val result=MlyValue.parameter_declaration(fn _ => let val 
declaration_specifiers as declaration_specifiers1=
declaration_specifiers1 ()
 in (
let val basety = extract_type declaration_specifiers
                     val _ = wonky_pdec_check declaration_specifiers
                 in
                   wrap((node basety, NONE),
                        left declaration_specifiers,
                        right declaration_specifiers)
                 end
) end
)
 in (LrTable.NT 36,(result,declaration_specifiers1left,
declaration_specifiers1right),rest671) end
| (52,(_,(_,_,RCURLYright as RCURLY1right))::(_,(
MlyValue.block_item_list block_item_list1,_,_))::(_,(_,LCURLYleft as 
LCURLY1left,_))::rest671) => let val result=
MlyValue.compound_statement(fn _ => let val block_item_list as 
block_item_list1=block_item_list1 ()
 in (wrap(block_item_list, LCURLYleft, RCURLYright)) end
)
 in (LrTable.NT 40,(result,LCURLY1left,RCURLY1right),rest671) end
| (53,rest671) => let val result=MlyValue.block_item_list(fn _ => ([])
)
 in (LrTable.NT 34,(result,defaultPos,defaultPos),rest671) end
| (54,(_,(MlyValue.block_item_list block_item_list1,_,
block_item_list1right))::(_,(MlyValue.block_item block_item1,
block_item1left,_))::rest671) => let val result=
MlyValue.block_item_list(fn _ => let val block_item as block_item1=
block_item1 ()
val block_item_list as block_item_list1=block_item_list1 ()
 in (block_item @ block_item_list) end
)
 in (LrTable.NT 34,(result,block_item1left,block_item_list1right),
rest671) end
| (55,(_,(MlyValue.declaration declaration1,declaration1left,
declaration1right))::rest671) => let val result=MlyValue.block_item(
fn _ => let val declaration as declaration1=declaration1 ()
 in (map BI_Decl declaration) end
)
 in (LrTable.NT 35,(result,declaration1left,declaration1right),rest671
) end
| (56,(_,(MlyValue.statement statement1,statement1left,statement1right
))::rest671) => let val result=MlyValue.block_item(fn _ => let val 
statement as statement1=statement1 ()
 in ([BI_Stmt statement]) end
)
 in (LrTable.NT 35,(result,statement1left,statement1right),rest671)
 end
| (57,rest671) => let val result=MlyValue.statement_list(fn _ => ([]))
 in (LrTable.NT 42,(result,defaultPos,defaultPos),rest671) end
| (58,(_,(MlyValue.statement_list1 statement_list11,
statement_list11left,statement_list11right))::rest671) => let val 
result=MlyValue.statement_list(fn _ => let val statement_list1 as 
statement_list11=statement_list11 ()
 in (statement_list1) end
)
 in (LrTable.NT 42,(result,statement_list11left,statement_list11right)
,rest671) end
| (59,(_,(MlyValue.statement statement1,statement1left,statement1right
))::rest671) => let val result=MlyValue.statement_list1(fn _ => let 
val statement as statement1=statement1 ()
 in ([statement]) end
)
 in (LrTable.NT 43,(result,statement1left,statement1right),rest671)
 end
| (60,(_,(MlyValue.statement_list1 statement_list11,_,
statement_list11right))::(_,(MlyValue.statement statement1,
statement1left,_))::rest671) => let val result=
MlyValue.statement_list1(fn _ => let val statement as statement1=
statement1 ()
val statement_list1 as statement_list11=statement_list11 ()
 in (statement::statement_list1) end
)
 in (LrTable.NT 43,(result,statement1left,statement_list11right),
rest671) end
| (61,(_,(MlyValue.struct_declaration struct_declaration1,
struct_declaration1left,struct_declaration1right))::rest671) => let 
val result=MlyValue.struct_declaration_list(fn _ => let val 
struct_declaration as struct_declaration1=struct_declaration1 ()
 in (struct_declaration) end
)
 in (LrTable.NT 28,(result,struct_declaration1left,
struct_declaration1right),rest671) end
| (62,(_,(MlyValue.struct_declaration_list struct_declaration_list1,_,
struct_declaration_list1right))::(_,(MlyValue.struct_declaration 
struct_declaration1,struct_declaration1left,_))::rest671) => let val 
result=MlyValue.struct_declaration_list(fn _ => let val 
struct_declaration as struct_declaration1=struct_declaration1 ()
val struct_declaration_list as struct_declaration_list1=
struct_declaration_list1 ()
 in (
let val (sflds1, siddecls1) = struct_declaration
                     val (sflds2, siddecls2) = struct_declaration_list
                 in
                   (wrap(node sflds1 @ node sflds2, left sflds1, right sflds2),
                    siddecls1 @ siddecls2)
                 end
) end
)
 in (LrTable.NT 28,(result,struct_declaration1left,
struct_declaration_list1right),rest671) end
| (63,(_,(MlyValue.type_specifier type_specifier1,type_specifier1left,
type_specifier1right))::rest671) => let val result=
MlyValue.specifier_qualifier_list(fn _ => let val type_specifier as 
type_specifier1=type_specifier1 ()
 in (
wrap([TypeSpec type_specifier],
                      tsleft type_specifier,
                      tsright type_specifier)
) end
)
 in (LrTable.NT 20,(result,type_specifier1left,type_specifier1right),
rest671) end
| (64,(_,(MlyValue.specifier_qualifier_list specifier_qualifier_list1,
_,specifier_qualifier_list1right))::(_,(MlyValue.type_specifier 
type_specifier1,type_specifier1left,_))::rest671) => let val result=
MlyValue.specifier_qualifier_list(fn _ => let val type_specifier as 
type_specifier1=type_specifier1 ()
val specifier_qualifier_list as specifier_qualifier_list1=
specifier_qualifier_list1 ()
 in (
wrap(TypeSpec type_specifier :: node specifier_qualifier_list,
                      tsleft type_specifier, right specifier_qualifier_list)
) end
)
 in (LrTable.NT 20,(result,type_specifier1left,
specifier_qualifier_list1right),rest671) end
| (65,(_,(MlyValue.type_qualifier type_qualifier1,type_qualifier1left,
type_qualifier1right))::rest671) => let val result=
MlyValue.specifier_qualifier_list(fn _ => let val type_qualifier as 
type_qualifier1=type_qualifier1 ()
 in (
wrap([TypeQual type_qualifier],
                      left type_qualifier, right type_qualifier)
) end
)
 in (LrTable.NT 20,(result,type_qualifier1left,type_qualifier1right),
rest671) end
| (66,(_,(MlyValue.specifier_qualifier_list specifier_qualifier_list1,
_,specifier_qualifier_list1right))::(_,(MlyValue.type_qualifier 
type_qualifier1,type_qualifier1left,_))::rest671) => let val result=
MlyValue.specifier_qualifier_list(fn _ => let val type_qualifier as 
type_qualifier1=type_qualifier1 ()
val specifier_qualifier_list as specifier_qualifier_list1=
specifier_qualifier_list1 ()
 in (
wrap(TypeQual type_qualifier :: node specifier_qualifier_list,
                      left type_qualifier, right specifier_qualifier_list)
) end
)
 in (LrTable.NT 20,(result,type_qualifier1left,
specifier_qualifier_list1right),rest671) end
| (67,(_,(_,CONSTleft as CONST1left,CONSTright as CONST1right))::
rest671) => let val result=MlyValue.type_qualifier(fn _ => (
wrap(Const, CONSTleft, CONSTright)))
 in (LrTable.NT 9,(result,CONST1left,CONST1right),rest671) end
| (68,(_,(_,VOLATILEleft as VOLATILE1left,VOLATILEright as 
VOLATILE1right))::rest671) => let val result=MlyValue.type_qualifier(
fn _ => (wrap(Volatile, VOLATILEleft, VOLATILEright)))
 in (LrTable.NT 9,(result,VOLATILE1left,VOLATILE1right),rest671) end
| (69,(_,(_,RESTRICTleft as RESTRICT1left,RESTRICTright as 
RESTRICT1right))::rest671) => let val result=MlyValue.type_qualifier(
fn _ => (wrap(Restrict, RESTRICTleft, RESTRICTright)))
 in (LrTable.NT 9,(result,RESTRICT1left,RESTRICT1right),rest671) end
| (70,(_,(MlyValue.type_qualifier type_qualifier1,type_qualifier1left,
type_qualifier1right))::rest671) => let val result=
MlyValue.type_qualifier_list(fn _ => let val type_qualifier as 
type_qualifier1=type_qualifier1 ()
 in ([type_qualifier]) end
)
 in (LrTable.NT 10,(result,type_qualifier1left,type_qualifier1right),
rest671) end
| (71,(_,(MlyValue.type_qualifier_list type_qualifier_list1,_,
type_qualifier_list1right))::(_,(MlyValue.type_qualifier 
type_qualifier1,type_qualifier1left,_))::rest671) => let val result=
MlyValue.type_qualifier_list(fn _ => let val type_qualifier as 
type_qualifier1=type_qualifier1 ()
val type_qualifier_list as type_qualifier_list1=type_qualifier_list1 
()
 in (type_qualifier::type_qualifier_list) end
)
 in (LrTable.NT 10,(result,type_qualifier1left,
type_qualifier_list1right),rest671) end
| (72,(_,(_,_,YSEMI1right))::(_,(MlyValue.struct_declarator_list 
struct_declarator_list1,_,_))::(_,(MlyValue.specifier_qualifier_list 
specifier_qualifier_list1,specifier_qualifier_list1left,_))::rest671)
 => let val result=MlyValue.struct_declaration(fn _ => let val 
specifier_qualifier_list as specifier_qualifier_list1=
specifier_qualifier_list1 ()
val struct_declarator_list as struct_declarator_list1=
struct_declarator_list1 ()
 in (
let val basetype = extract_type specifier_qualifier_list
                     val sdecls = first_sdecls (node specifier_qualifier_list)
                     val _ = case first_enum_dec (node specifier_qualifier_list) of
                               NONE => ()
                             | SOME es => errorStr'(left es, right es,
                                                    "Don't declare enumerations\
                                                    \ inside structs")
                     fun apply_decltor sd = let
                       val (ddw, eop) = sd
                       val (nm,ad,_,_) = node ddw
                     in
                       (node ad (node basetype), apnode C_field_name nm, eop)
                     end
                 in
                   (wrap(map apply_decltor (node struct_declarator_list),
                         left basetype, right struct_declarator_list),
                    sdecls)
                 end
) end
)
 in (LrTable.NT 29,(result,specifier_qualifier_list1left,YSEMI1right),
rest671) end
| (73,(_,(MlyValue.struct_declarator struct_declarator1,
struct_declarator1left,struct_declarator1right))::rest671) => let val 
result=MlyValue.struct_declarator_list(fn _ => let val 
struct_declarator as struct_declarator1=struct_declarator1 ()
 in (
wrap ([node struct_declarator], left struct_declarator,
                            right struct_declarator)
) end
)
 in (LrTable.NT 62,(result,struct_declarator1left,
struct_declarator1right),rest671) end
| (74,(_,(MlyValue.struct_declarator_list struct_declarator_list1,_,
struct_declarator_list1right))::_::(_,(MlyValue.struct_declarator 
struct_declarator1,struct_declarator1left,_))::rest671) => let val 
result=MlyValue.struct_declarator_list(fn _ => let val 
struct_declarator as struct_declarator1=struct_declarator1 ()
val struct_declarator_list as struct_declarator_list1=
struct_declarator_list1 ()
 in (
wrap (node struct_declarator::node struct_declarator_list,
                       left struct_declarator, right struct_declarator_list)
) end
)
 in (LrTable.NT 62,(result,struct_declarator1left,
struct_declarator_list1right),rest671) end
| (75,(_,(MlyValue.declarator declarator1,declarator1left,
declarator1right))::rest671) => let val result=
MlyValue.struct_declarator(fn _ => let val declarator as declarator1=
declarator1 ()
 in (wrap((declarator, NONE), left declarator, right declarator)) end
)
 in (LrTable.NT 61,(result,declarator1left,declarator1right),rest671)
 end
| (76,(_,(MlyValue.rexpression rexpression1,_,rexpression1right))::_::
(_,(MlyValue.declarator declarator1,declarator1left,_))::rest671) => 
let val result=MlyValue.struct_declarator(fn _ => let val declarator
 as declarator1=declarator1 ()
val rexpression as rexpression1=rexpression1 ()
 in (
wrap((declarator, SOME rexpression), left declarator,
                      eright rexpression)
) end
)
 in (LrTable.NT 61,(result,declarator1left,rexpression1right),rest671)
 end
| (77,(_,(MlyValue.init_declarator init_declarator1,
init_declarator1left,init_declarator1right))::rest671) => let val 
result=MlyValue.init_declarator_list(fn _ => let val init_declarator
 as init_declarator1=init_declarator1 ()
 in ([init_declarator]) end
)
 in (LrTable.NT 64,(result,init_declarator1left,init_declarator1right)
,rest671) end
| (78,(_,(MlyValue.init_declarator_list init_declarator_list1,_,
init_declarator_list1right))::_::(_,(MlyValue.init_declarator 
init_declarator1,init_declarator1left,_))::rest671) => let val result=
MlyValue.init_declarator_list(fn _ => let val init_declarator as 
init_declarator1=init_declarator1 ()
val init_declarator_list as init_declarator_list1=
init_declarator_list1 ()
 in (init_declarator :: init_declarator_list) end
)
 in (LrTable.NT 64,(result,init_declarator1left,
init_declarator_list1right),rest671) end
| (79,(_,(MlyValue.declarator declarator1,declarator1left,
declarator1right))::rest671) => let val result=
MlyValue.init_declarator(fn _ => let val declarator as declarator1=
declarator1 ()
 in (wrap((declarator, NONE), left declarator, right declarator)) end
)
 in (LrTable.NT 63,(result,declarator1left,declarator1right),rest671)
 end
| (80,(_,(MlyValue.initializer initializer1,_,initializer1right))::_::
(_,(MlyValue.declarator declarator1,declarator1left,_))::rest671) => 
let val result=MlyValue.init_declarator(fn _ => let val declarator as 
declarator1=declarator1 ()
val initializer as initializer1=initializer1 ()
 in (
wrap((declarator, SOME (node initializer)),
                      left declarator, right initializer)
) end
)
 in (LrTable.NT 63,(result,declarator1left,initializer1right),rest671)
 end
| (81,(_,(_,YSTARleft as YSTAR1left,YSTARright as YSTAR1right))::
rest671) => let val result=MlyValue.pointer(fn _ => (
ptrdecl YSTARleft YSTARright))
 in (LrTable.NT 57,(result,YSTAR1left,YSTAR1right),rest671) end
| (82,(_,(MlyValue.type_qualifier_list type_qualifier_list1,_,
type_qualifier_list1right))::(_,(_,YSTARleft as YSTAR1left,_))::
rest671) => let val result=MlyValue.pointer(fn _ => let val 
type_qualifier_list as type_qualifier_list1=type_qualifier_list1 ()
 in (ptrdecl YSTARleft (right (List.last type_qualifier_list))) end
)
 in (LrTable.NT 57,(result,YSTAR1left,type_qualifier_list1right),
rest671) end
| (83,(_,(MlyValue.pointer pointer1,_,pointer1right))::(_,(_,YSTARleft
 as YSTAR1left,YSTARright))::rest671) => let val result=
MlyValue.pointer(fn _ => let val pointer as pointer1=pointer1 ()
 in (ooa(ptrdecl YSTARleft YSTARright, pointer)) end
)
 in (LrTable.NT 57,(result,YSTAR1left,pointer1right),rest671) end
| (84,(_,(MlyValue.pointer pointer1,_,pointer1right))::(_,(
MlyValue.type_qualifier_list type_qualifier_list1,_,_))::(_,(_,
YSTARleft as YSTAR1left,_))::rest671) => let val result=
MlyValue.pointer(fn _ => let val type_qualifier_list as 
type_qualifier_list1=type_qualifier_list1 ()
val pointer as pointer1=pointer1 ()
 in (
ooa(ptrdecl YSTARleft (right (List.last type_qualifier_list)),
                     pointer)
) end
)
 in (LrTable.NT 57,(result,YSTAR1left,pointer1right),rest671) end
| (85,(_,(MlyValue.direct_declarator direct_declarator1,_,
direct_declarator1right))::(_,(MlyValue.pointer pointer1,pointer1left,
_))::rest671) => let val result=MlyValue.declarator(fn _ => let val 
pointer as pointer1=pointer1 ()
val direct_declarator as direct_declarator1=direct_declarator1 ()
 in (ood(direct_declarator, pointer)) end
)
 in (LrTable.NT 58,(result,pointer1left,direct_declarator1right),
rest671) end
| (86,(_,(MlyValue.direct_declarator direct_declarator1,_,
direct_declarator1right))::(_,(MlyValue.attribute_specifier 
attribute_specifier1,_,_))::(_,(MlyValue.pointer pointer1,pointer1left
,_))::rest671) => let val result=MlyValue.declarator(fn _ => let val 
pointer as pointer1=pointer1 ()
val attribute_specifier as attribute_specifier1=attribute_specifier1 
()
val direct_declarator as direct_declarator1=direct_declarator1 ()
 in (
ood(add_attributes(direct_declarator,
                                    node attribute_specifier),
                     pointer)
) end
)
 in (LrTable.NT 58,(result,pointer1left,direct_declarator1right),
rest671) end
| (87,(_,(MlyValue.direct_declarator direct_declarator1,
direct_declarator1left,direct_declarator1right))::rest671) => let val 
result=MlyValue.declarator(fn _ => let val direct_declarator as 
direct_declarator1=direct_declarator1 ()
 in (direct_declarator) end
)
 in (LrTable.NT 58,(result,direct_declarator1left,
direct_declarator1right),rest671) end
| (88,(_,(_,_,SPEC_BLOCKEND1right))::(_,(MlyValue.idlist idlist1,_,_))
::(_,(_,CALLS1left,_))::rest671) => let val result=
MlyValue.calls_block(fn _ => let val idlist as idlist1=idlist1 ()
 in (SOME idlist) end
)
 in (LrTable.NT 103,(result,CALLS1left,SPEC_BLOCKEND1right),rest671)
 end
| (89,rest671) => let val result=MlyValue.calls_block(fn _ => (NONE))
 in (LrTable.NT 103,(result,defaultPos,defaultPos),rest671) end
| (90,(_,(MlyValue.ID ID1,IDleft as ID1left,IDright as ID1right))::
rest671) => let val result=MlyValue.direct_declarator(fn _ => let val 
ID as ID1=ID1 ()
 in (
wrap((wrap(ID, IDleft, IDright),
                       wrap((fn t => t), IDleft, IDright),
                       NONE,
                       []),
                      IDleft, IDright)
) end
)
 in (LrTable.NT 65,(result,ID1left,ID1right),rest671) end
| (91,(_,(_,_,RBRACKETright as RBRACKET1right))::(_,(
MlyValue.rexpression rexpression1,_,_))::(_,(_,LBRACKETleft,_))::(_,(
MlyValue.direct_declarator direct_declarator1,direct_declarator1left,_
))::rest671) => let val result=MlyValue.direct_declarator(fn _ => let 
val direct_declarator as direct_declarator1=direct_declarator1 ()
val rexpression as rexpression1=rexpression1 ()
 in (
ood(direct_declarator,
                     arraydecl LBRACKETleft RBRACKETright (SOME rexpression))
) end
)
 in (LrTable.NT 65,(result,direct_declarator1left,RBRACKET1right),
rest671) end
| (92,(_,(_,_,RBRACKETright as RBRACKET1right))::(_,(_,LBRACKETleft,_)
)::(_,(MlyValue.direct_declarator direct_declarator1,
direct_declarator1left,_))::rest671) => let val result=
MlyValue.direct_declarator(fn _ => let val direct_declarator as 
direct_declarator1=direct_declarator1 ()
 in (
ood(direct_declarator,
                     arraydecl LBRACKETleft RBRACKETright NONE)
) end
)
 in (LrTable.NT 65,(result,direct_declarator1left,RBRACKET1right),
rest671) end
| (93,(_,(_,_,RPARENright as RPAREN1right))::(_,(MlyValue.declarator 
declarator1,_,_))::(_,(_,LPARENleft as LPAREN1left,_))::rest671) => 
let val result=MlyValue.direct_declarator(fn _ => let val declarator
 as declarator1=declarator1 ()
 in (wrap(node declarator, LPARENleft, RPARENright)) end
)
 in (LrTable.NT 65,(result,LPAREN1left,RPAREN1right),rest671) end
| (94,(_,(MlyValue.calls_block calls_block1,_,calls_block1right))::_::
(_,(MlyValue.parameter_list parameter_list1,_,_))::_::(_,(
MlyValue.direct_declarator direct_declarator1,direct_declarator1left,_
))::rest671) => let val result=MlyValue.direct_declarator(fn _ => let 
val direct_declarator as direct_declarator1=direct_declarator1 ()
val parameter_list as parameter_list1=parameter_list1 ()
val calls_block1=calls_block1 ()
 in (
let val ps = check_params parameter_list
                 in
                   addparams(ood(direct_declarator,
                                 fndecl (left direct_declarator)
                                        (right direct_declarator)
                                        (map (#1 o node) ps)),
                             ps)
                 end
) end
)
 in (LrTable.NT 65,(result,direct_declarator1left,calls_block1right),
rest671) end
| (95,(_,(MlyValue.attribute_specifier attribute_specifier1,_,
attribute_specifier1right))::(_,(MlyValue.direct_declarator 
direct_declarator1,direct_declarator1left,_))::rest671) => let val 
result=MlyValue.direct_declarator(fn _ => let val direct_declarator
 as direct_declarator1=direct_declarator1 ()
val attribute_specifier as attribute_specifier1=attribute_specifier1 
()
 in (
add_attributes(direct_declarator,
                                node attribute_specifier)
) end
)
 in (LrTable.NT 65,(result,direct_declarator1left,
attribute_specifier1right),rest671) end
| (96,(_,(MlyValue.asm_declarator_mod asm_declarator_mod1,_,
asm_declarator_mod1right))::(_,(MlyValue.direct_declarator 
direct_declarator1,direct_declarator1left,_))::rest671) => let val 
result=MlyValue.direct_declarator(fn _ => let val direct_declarator
 as direct_declarator1=direct_declarator1 ()
val asm_declarator_mod1=asm_declarator_mod1 ()
 in (direct_declarator) end
)
 in (LrTable.NT 65,(result,direct_declarator1left,
asm_declarator_mod1right),rest671) end
| (97,(_,(_,_,RPAREN1right))::(_,(MlyValue.cstring_literal 
cstring_literal1,_,_))::_::(_,(_,YASM1left,_))::rest671) => let val 
result=MlyValue.asm_declarator_mod(fn _ => let val cstring_literal1=
cstring_literal1 ()
 in (()) end
)
 in (LrTable.NT 66,(result,YASM1left,RPAREN1right),rest671) end
| (98,(_,(MlyValue.ID ID1,IDleft as ID1left,IDright as ID1right))::
rest671) => let val result=MlyValue.struct_id(fn _ => let val ID as 
ID1=ID1 ()
 in (wrap(ID, IDleft, IDright)) end
)
 in (LrTable.NT 69,(result,ID1left,ID1right),rest671) end
| (99,(_,(MlyValue.TYPEID TYPEID1,TYPEIDleft as TYPEID1left,
TYPEIDright as TYPEID1right))::rest671) => let val result=
MlyValue.struct_id(fn _ => let val TYPEID as TYPEID1=TYPEID1 ()
 in (wrap(TYPEID, TYPEIDleft, TYPEIDright)) end
)
 in (LrTable.NT 69,(result,TYPEID1left,TYPEID1right),rest671) end
| (100,(_,(MlyValue.struct_id struct_id1,_,struct_id1right))::(_,(_,
STRUCTleft as STRUCT1left,_))::rest671) => let val result=
MlyValue.struct_or_union_specifier(fn _ => let val struct_id as 
struct_id1=struct_id1 ()
 in (
(wrap(StructTy
                           (C_struct_name (node struct_id)),
                       STRUCTleft,
                       right struct_id),
                  [])
) end
)
 in (LrTable.NT 68,(result,STRUCT1left,struct_id1right),rest671) end
| (101,(_,(_,_,RCURLYright as RCURLY1right))::(_,(
MlyValue.struct_declaration_list struct_declaration_list1,_,_))::_::(_
,(MlyValue.struct_id struct_id1,_,_))::(_,(_,STRUCTleft as STRUCT1left
,_))::rest671) => let val result=MlyValue.struct_or_union_specifier(
fn _ => let val struct_id as struct_id1=struct_id1 ()
val struct_declaration_list as struct_declaration_list1=
struct_declaration_list1 ()
 in (
let val (flds, decls) = struct_declaration_list
                     val raw_s_name = node struct_id
                     val munged_name = C_struct_name raw_s_name
                     val sname_w = wrap(munged_name, left struct_id,
                                        right struct_id)
                 in
                   (wrap(StructTy munged_name, STRUCTleft, right struct_id),
                    wrap((sname_w, node flds),
                         STRUCTleft, RCURLYright) :: decls)
                 end
) end
)
 in (LrTable.NT 68,(result,STRUCT1left,RCURLY1right),rest671) end
| (102,(_,(_,_,RCURLYright as RCURLY1right))::(_,(
MlyValue.struct_declaration_list struct_declaration_list1,_,_))::(_,(_
,LCURLYleft,_))::(_,(_,STRUCTleft as STRUCT1left,STRUCTright))::
rest671) => let val result=MlyValue.struct_or_union_specifier(fn _ => 
let val struct_declaration_list as struct_declaration_list1=
struct_declaration_list1 ()
 in (
let
                   val (flds, decls) = struct_declaration_list
                   val anonid = gen_struct_id ()
                   val anonw = wrap(anonid, STRUCTright, LCURLYleft)
                 in
                   (wrap(StructTy anonid, STRUCTleft, LCURLYleft),
                    wrap((anonw, node flds), STRUCTleft, RCURLYright) ::
                    decls)
                 end
) end
)
 in (LrTable.NT 68,(result,STRUCT1left,RCURLY1right),rest671) end
| (103,(_,(_,INTleft as INT1left,INTright as INT1right))::rest671) => 
let val result=MlyValue.type_specifier(fn _ => (
Tstok(wrap(ts_int, INTleft, INTright))))
 in (LrTable.NT 67,(result,INT1left,INT1right),rest671) end
| (104,(_,(_,CHARleft as CHAR1left,CHARright as CHAR1right))::rest671)
 => let val result=MlyValue.type_specifier(fn _ => (
Tstok(wrap(ts_char, CHARleft, CHARright))))
 in (LrTable.NT 67,(result,CHAR1left,CHAR1right),rest671) end
| (105,(_,(_,SHORTleft as SHORT1left,SHORTright as SHORT1right))::
rest671) => let val result=MlyValue.type_specifier(fn _ => (
Tstok(wrap(ts_short, SHORTleft, SHORTright))))
 in (LrTable.NT 67,(result,SHORT1left,SHORT1right),rest671) end
| (106,(_,(_,LONGleft as LONG1left,LONGright as LONG1right))::rest671)
 => let val result=MlyValue.type_specifier(fn _ => (
Tstok(wrap(ts_long, LONGleft, LONGright))))
 in (LrTable.NT 67,(result,LONG1left,LONG1right),rest671) end
| (107,(_,(_,VOIDleft as VOID1left,VOIDright as VOID1right))::rest671)
 => let val result=MlyValue.type_specifier(fn _ => (
Tstok(wrap(ts_void, VOIDleft, VOIDright))))
 in (LrTable.NT 67,(result,VOID1left,VOID1right),rest671) end
| (108,(_,(_,SIGNEDleft as SIGNED1left,SIGNEDright as SIGNED1right))::
rest671) => let val result=MlyValue.type_specifier(fn _ => (
Tstok(wrap(ts_signed, SIGNEDleft, SIGNEDright))))
 in (LrTable.NT 67,(result,SIGNED1left,SIGNED1right),rest671) end
| (109,(_,(_,UNSIGNEDleft as UNSIGNED1left,UNSIGNEDright as 
UNSIGNED1right))::rest671) => let val result=MlyValue.type_specifier(
fn _ => (Tstok(wrap(ts_unsigned, UNSIGNEDleft, UNSIGNEDright))))
 in (LrTable.NT 67,(result,UNSIGNED1left,UNSIGNED1right),rest671) end
| (110,(_,(_,BOOLleft as BOOL1left,BOOLright as BOOL1right))::rest671)
 => let val result=MlyValue.type_specifier(fn _ => (
Tstok(wrap(ts_bool, BOOLleft, BOOLright))))
 in (LrTable.NT 67,(result,BOOL1left,BOOL1right),rest671) end
| (111,(_,(MlyValue.struct_or_union_specifier 
struct_or_union_specifier1,struct_or_union_specifier1left,
struct_or_union_specifier1right))::rest671) => let val result=
MlyValue.type_specifier(fn _ => let val struct_or_union_specifier as 
struct_or_union_specifier1=struct_or_union_specifier1 ()
 in (Tsstruct struct_or_union_specifier) end
)
 in (LrTable.NT 67,(result,struct_or_union_specifier1left,
struct_or_union_specifier1right),rest671) end
| (112,(_,(MlyValue.enum_specifier enum_specifier1,enum_specifier1left
,enum_specifier1right))::rest671) => let val result=
MlyValue.type_specifier(fn _ => let val enum_specifier as 
enum_specifier1=enum_specifier1 ()
 in (Tsenum enum_specifier) end
)
 in (LrTable.NT 67,(result,enum_specifier1left,enum_specifier1right),
rest671) end
| (113,(_,(MlyValue.TYPEID TYPEID1,TYPEIDleft as TYPEID1left,
TYPEIDright as TYPEID1right))::rest671) => let val result=
MlyValue.type_specifier(fn _ => let val TYPEID as TYPEID1=TYPEID1 ()
 in (Tstypeid(wrap(TYPEID, TYPEIDleft, TYPEIDright))) end
)
 in (LrTable.NT 67,(result,TYPEID1left,TYPEID1right),rest671) end
| (114,(_,(_,_,RCURLYright as RCURLY1right))::(_,(
MlyValue.enumerator_list enumerator_list1,_,_))::_::(_,(_,YENUMleft
 as YENUM1left,YENUMright))::rest671) => let val result=
MlyValue.enum_specifier(fn _ => let val enumerator_list as 
enumerator_list1=enumerator_list1 ()
 in (
wrap((wrap(NONE, YENUMleft, YENUMright), enumerator_list),
                      YENUMleft, RCURLYright)
) end
)
 in (LrTable.NT 6,(result,YENUM1left,RCURLY1right),rest671) end
| (115,(_,(_,_,RCURLYright as RCURLY1right))::(_,(
MlyValue.enumerator_list enumerator_list1,_,_))::_::(_,(
MlyValue.struct_id struct_id1,_,_))::(_,(_,YENUMleft as YENUM1left,_))
::rest671) => let val result=MlyValue.enum_specifier(fn _ => let val 
struct_id as struct_id1=struct_id1 ()
val enumerator_list as enumerator_list1=enumerator_list1 ()
 in (
wrap((apnode SOME struct_id, enumerator_list),
                      YENUMleft, RCURLYright)
) end
)
 in (LrTable.NT 6,(result,YENUM1left,RCURLY1right),rest671) end
| (116,(_,(_,_,RCURLYright as RCURLY1right))::_::(_,(
MlyValue.enumerator_list enumerator_list1,_,_))::_::(_,(_,YENUMleft
 as YENUM1left,YENUMright))::rest671) => let val result=
MlyValue.enum_specifier(fn _ => let val enumerator_list as 
enumerator_list1=enumerator_list1 ()
 in (
wrap((wrap(NONE, YENUMleft, YENUMright), enumerator_list),
                      YENUMleft, RCURLYright)
) end
)
 in (LrTable.NT 6,(result,YENUM1left,RCURLY1right),rest671) end
| (117,(_,(_,_,RCURLYright as RCURLY1right))::_::(_,(
MlyValue.enumerator_list enumerator_list1,_,_))::_::(_,(
MlyValue.struct_id struct_id1,_,_))::(_,(_,YENUMleft as YENUM1left,_))
::rest671) => let val result=MlyValue.enum_specifier(fn _ => let val 
struct_id as struct_id1=struct_id1 ()
val enumerator_list as enumerator_list1=enumerator_list1 ()
 in (
wrap((apnode SOME struct_id, enumerator_list),
                      YENUMleft, RCURLYright)
) end
)
 in (LrTable.NT 6,(result,YENUM1left,RCURLY1right),rest671) end
| (118,(_,(MlyValue.struct_id struct_id1,_,struct_idright as 
struct_id1right))::(_,(_,YENUMleft as YENUM1left,_))::rest671) => let 
val result=MlyValue.enum_specifier(fn _ => let val struct_id as 
struct_id1=struct_id1 ()
 in (wrap((apnode SOME struct_id, []), YENUMleft, struct_idright)) end
)
 in (LrTable.NT 6,(result,YENUM1left,struct_id1right),rest671) end
| (119,(_,(MlyValue.enumerator enumerator1,enumerator1left,
enumerator1right))::rest671) => let val result=
MlyValue.enumerator_list(fn _ => let val enumerator as enumerator1=
enumerator1 ()
 in ([enumerator]) end
)
 in (LrTable.NT 7,(result,enumerator1left,enumerator1right),rest671)
 end
| (120,(_,(MlyValue.enumerator enumerator1,_,enumerator1right))::_::(_
,(MlyValue.enumerator_list enumerator_list1,enumerator_list1left,_))::
rest671) => let val result=MlyValue.enumerator_list(fn _ => let val 
enumerator_list as enumerator_list1=enumerator_list1 ()
val enumerator as enumerator1=enumerator1 ()
 in (enumerator_list @ [enumerator]) end
)
 in (LrTable.NT 7,(result,enumerator_list1left,enumerator1right),
rest671) end
| (121,(_,(MlyValue.ID ID1,IDleft as ID1left,IDright as ID1right))::
rest671) => let val result=MlyValue.enumerator(fn _ => let val ID as 
ID1=ID1 ()
 in ((wrap(ID,IDleft,IDright), NONE)) end
)
 in (LrTable.NT 8,(result,ID1left,ID1right),rest671) end
| (122,(_,(MlyValue.rexpression rexpression1,_,rexpression1right))::_
::(_,(MlyValue.ID ID1,IDleft as ID1left,IDright))::rest671) => let 
val result=MlyValue.enumerator(fn _ => let val ID as ID1=ID1 ()
val rexpression as rexpression1=rexpression1 ()
 in ((wrap(ID,IDleft,IDright), SOME rexpression)) end
)
 in (LrTable.NT 8,(result,ID1left,rexpression1right),rest671) end
| (123,(_,(MlyValue.pointer pointer1,pointer1left,pointer1right))::
rest671) => let val result=MlyValue.abstract_declarator(fn _ => let 
val pointer as pointer1=pointer1 ()
 in (pointer) end
)
 in (LrTable.NT 59,(result,pointer1left,pointer1right),rest671) end
| (124,(_,(MlyValue.direct_abstract_declarator 
direct_abstract_declarator1,_,direct_abstract_declarator1right))::(_,(
MlyValue.pointer pointer1,pointer1left,_))::rest671) => let val result
=MlyValue.abstract_declarator(fn _ => let val pointer as pointer1=
pointer1 ()
val direct_abstract_declarator as direct_abstract_declarator1=
direct_abstract_declarator1 ()
 in (
wrap (node direct_abstract_declarator o
                                     node pointer,
                                     left pointer,
                                     right direct_abstract_declarator)
) end
)
 in (LrTable.NT 59,(result,pointer1left,
direct_abstract_declarator1right),rest671) end
| (125,(_,(MlyValue.direct_abstract_declarator 
direct_abstract_declarator1,direct_abstract_declarator1left,
direct_abstract_declarator1right))::rest671) => let val result=
MlyValue.abstract_declarator(fn _ => let val 
direct_abstract_declarator as direct_abstract_declarator1=
direct_abstract_declarator1 ()
 in (direct_abstract_declarator) end
)
 in (LrTable.NT 59,(result,direct_abstract_declarator1left,
direct_abstract_declarator1right),rest671) end
| (126,(_,(_,_,RPARENright as RPAREN1right))::(_,(
MlyValue.abstract_declarator abstract_declarator1,_,_))::(_,(_,
LPARENleft as LPAREN1left,_))::rest671) => let val result=
MlyValue.direct_abstract_declarator(fn _ => let val 
abstract_declarator as abstract_declarator1=abstract_declarator1 ()
 in (wrap(node abstract_declarator, LPARENleft, RPARENright)) end
)
 in (LrTable.NT 60,(result,LPAREN1left,RPAREN1right),rest671) end
| (127,(_,(_,_,RBRACKETright as RBRACKET1right))::(_,(
MlyValue.rexpression rexpression1,_,_))::(_,(_,LBRACKETleft as 
LBRACKET1left,_))::rest671) => let val result=
MlyValue.direct_abstract_declarator(fn _ => let val rexpression as 
rexpression1=rexpression1 ()
 in (arraydecl LBRACKETleft RBRACKETright (SOME rexpression)) end
)
 in (LrTable.NT 60,(result,LBRACKET1left,RBRACKET1right),rest671) end
| (128,(_,(_,_,RBRACKETright as RBRACKET1right))::(_,(_,LBRACKETleft
 as LBRACKET1left,_))::rest671) => let val result=
MlyValue.direct_abstract_declarator(fn _ => (
ptrdecl LBRACKETleft RBRACKETright))
 in (LrTable.NT 60,(result,LBRACKET1left,RBRACKET1right),rest671) end
| (129,(_,(_,_,RBRACKETright as RBRACKET1right))::(_,(
MlyValue.rexpression rexpression1,_,_))::(_,(_,LBRACKETleft,_))::(_,(
MlyValue.direct_abstract_declarator direct_abstract_declarator1,
direct_abstract_declarator1left,_))::rest671) => let val result=
MlyValue.direct_abstract_declarator(fn _ => let val 
direct_abstract_declarator as direct_abstract_declarator1=
direct_abstract_declarator1 ()
val rexpression as rexpression1=rexpression1 ()
 in (
ooa(direct_abstract_declarator,
                     arraydecl LBRACKETleft RBRACKETright (SOME rexpression))
) end
)
 in (LrTable.NT 60,(result,direct_abstract_declarator1left,
RBRACKET1right),rest671) end
| (130,(_,(_,_,RPARENright as RPAREN1right))::(_,(
MlyValue.parameter_list parameter_list1,_,_))::(_,(_,LPARENleft as 
LPAREN1left,_))::rest671) => let val result=
MlyValue.direct_abstract_declarator(fn _ => let val parameter_list as 
parameter_list1=parameter_list1 ()
 in (
let val ps = check_params parameter_list
                 in
                   fndecl LPARENleft RPARENright (map (#1 o node) ps)
                 end
) end
)
 in (LrTable.NT 60,(result,LPAREN1left,RPAREN1right),rest671) end
| (131,(_,(_,_,RPARENright as RPAREN1right))::(_,(
MlyValue.parameter_list parameter_list1,_,_))::(_,(_,LPARENleft,_))::(
_,(MlyValue.direct_abstract_declarator direct_abstract_declarator1,
direct_abstract_declarator1left,_))::rest671) => let val result=
MlyValue.direct_abstract_declarator(fn _ => let val 
direct_abstract_declarator as direct_abstract_declarator1=
direct_abstract_declarator1 ()
val parameter_list as parameter_list1=parameter_list1 ()
 in (
let val ps = check_params parameter_list
                 in
                   ooa(direct_abstract_declarator,
                       fndecl LPARENleft RPARENright (map (#1 o node) ps))
                 end
) end
)
 in (LrTable.NT 60,(result,direct_abstract_declarator1left,
RPAREN1right),rest671) end
| (132,(_,(MlyValue.abstract_declarator abstract_declarator1,_,
abstract_declarator1right))::(_,(MlyValue.specifier_qualifier_list 
specifier_qualifier_list1,specifier_qualifier_list1left,_))::rest671)
 => let val result=MlyValue.type_name(fn _ => let val 
specifier_qualifier_list as specifier_qualifier_list1=
specifier_qualifier_list1 ()
val abstract_declarator as abstract_declarator1=abstract_declarator1 
()
 in (
let
                   val sql = specifier_qualifier_list
                   val basety = extract_type sql
                   val _ = case has_typedef sql of
                             NONE => ()
                           | SOME (l,r) =>
                               errorStr'(l,r, "Typedef illegal here")
                 in
                   wrap(node abstract_declarator (node basety),
                        left specifier_qualifier_list,
                        right abstract_declarator)
                 end
) end
)
 in (LrTable.NT 33,(result,specifier_qualifier_list1left,
abstract_declarator1right),rest671) end
| (133,(_,(MlyValue.specifier_qualifier_list specifier_qualifier_list1
,specifier_qualifier_list1left,specifier_qualifier_list1right))::
rest671) => let val result=MlyValue.type_name(fn _ => let val 
specifier_qualifier_list as specifier_qualifier_list1=
specifier_qualifier_list1 ()
 in (
let
                   val sql = specifier_qualifier_list
                   val basety = extract_type sql
                   val _ = case has_typedef sql of
                             NONE => ()
                             | SOME (l,r) =>
                                 errorStr'(l,r, "Typedef illegal here")
                 in
                   basety
                 end
) end
)
 in (LrTable.NT 33,(result,specifier_qualifier_list1left,
specifier_qualifier_list1right),rest671) end
| (134,(_,(MlyValue.dinitializer dinitializer1,dinitializer1left,
dinitializer1right))::rest671) => let val result=
MlyValue.initializer_list(fn _ => let val dinitializer as 
dinitializer1=dinitializer1 ()
 in ([dinitializer]) end
)
 in (LrTable.NT 21,(result,dinitializer1left,dinitializer1right),
rest671) end
| (135,(_,(_,_,YCOMMA1right))::(_,(MlyValue.dinitializer dinitializer1
,dinitializer1left,_))::rest671) => let val result=
MlyValue.initializer_list(fn _ => let val dinitializer as 
dinitializer1=dinitializer1 ()
 in ([dinitializer]) end
)
 in (LrTable.NT 21,(result,dinitializer1left,YCOMMA1right),rest671)
 end
| (136,(_,(MlyValue.initializer_list initializer_list1,_,
initializer_list1right))::_::(_,(MlyValue.dinitializer dinitializer1,
dinitializer1left,_))::rest671) => let val result=
MlyValue.initializer_list(fn _ => let val dinitializer as 
dinitializer1=dinitializer1 ()
val initializer_list as initializer_list1=initializer_list1 ()
 in (dinitializer :: initializer_list) end
)
 in (LrTable.NT 21,(result,dinitializer1left,initializer_list1right),
rest671) end
| (137,(_,(MlyValue.initializer initializer1,_,initializer1right))::(_
,(MlyValue.designation designation1,designation1left,_))::rest671) => 
let val result=MlyValue.dinitializer(fn _ => let val designation as 
designation1=designation1 ()
val initializer as initializer1=initializer1 ()
 in ((designation, node initializer)) end
)
 in (LrTable.NT 22,(result,designation1left,initializer1right),rest671
) end
| (138,(_,(MlyValue.initializer initializer1,initializer1left,
initializer1right))::rest671) => let val result=MlyValue.dinitializer(
fn _ => let val initializer as initializer1=initializer1 ()
 in (([], node initializer)) end
)
 in (LrTable.NT 22,(result,initializer1left,initializer1right),rest671
) end
| (139,(_,(_,_,YEQ1right))::(_,(MlyValue.designator_list 
designator_list1,designator_list1left,_))::rest671) => let val result=
MlyValue.designation(fn _ => let val designator_list as 
designator_list1=designator_list1 ()
 in (designator_list) end
)
 in (LrTable.NT 24,(result,designator_list1left,YEQ1right),rest671)
 end
| (140,(_,(MlyValue.designator designator1,designator1left,
designator1right))::rest671) => let val result=
MlyValue.designator_list(fn _ => let val designator as designator1=
designator1 ()
 in ([designator]) end
)
 in (LrTable.NT 25,(result,designator1left,designator1right),rest671)
 end
| (141,(_,(MlyValue.designator_list designator_list1,_,
designator_list1right))::(_,(MlyValue.designator designator1,
designator1left,_))::rest671) => let val result=
MlyValue.designator_list(fn _ => let val designator as designator1=
designator1 ()
val designator_list as designator_list1=designator_list1 ()
 in (designator :: designator_list) end
)
 in (LrTable.NT 25,(result,designator1left,designator_list1right),
rest671) end
| (142,(_,(_,_,RBRACKET1right))::(_,(MlyValue.rexpression rexpression1
,_,_))::(_,(_,LBRACKET1left,_))::rest671) => let val result=
MlyValue.designator(fn _ => let val rexpression as rexpression1=
rexpression1 ()
 in (DesignE rexpression) end
)
 in (LrTable.NT 26,(result,LBRACKET1left,RBRACKET1right),rest671) end
| (143,(_,(MlyValue.ID ID1,_,ID1right))::(_,(_,YDOT1left,_))::rest671)
 => let val result=MlyValue.designator(fn _ => let val ID as ID1=ID1 
()
 in (DesignFld (C_field_name ID)) end
)
 in (LrTable.NT 26,(result,YDOT1left,ID1right),rest671) end
| (144,(_,(MlyValue.rexpression rexpression1,rexpression1left,
rexpression1right))::rest671) => let val result=MlyValue.initializer(
fn _ => let val rexpression as rexpression1=rexpression1 ()
 in (wrap(InitE rexpression, eleft rexpression, eright rexpression))
 end
)
 in (LrTable.NT 23,(result,rexpression1left,rexpression1right),rest671
) end
| (145,(_,(_,_,RCURLYright as RCURLY1right))::(_,(
MlyValue.initializer_list initializer_list1,_,_))::(_,(_,LCURLYleft
 as LCURLY1left,_))::rest671) => let val result=MlyValue.initializer(
fn _ => let val initializer_list as initializer_list1=
initializer_list1 ()
 in (wrap(InitList initializer_list, LCURLYleft, RCURLYright)) end
)
 in (LrTable.NT 23,(result,LCURLY1left,RCURLY1right),rest671) end
| (146,(_,(_,YEQ1left,YEQ1right))::rest671) => let val result=
MlyValue.assignop(fn _ => (NONE))
 in (LrTable.NT 56,(result,YEQ1left,YEQ1right),rest671) end
| (147,(_,(_,PLUSEQ1left,PLUSEQ1right))::rest671) => let val result=
MlyValue.assignop(fn _ => (SOME Plus))
 in (LrTable.NT 56,(result,PLUSEQ1left,PLUSEQ1right),rest671) end
| (148,(_,(_,MINUSEQ1left,MINUSEQ1right))::rest671) => let val result=
MlyValue.assignop(fn _ => (SOME Minus))
 in (LrTable.NT 56,(result,MINUSEQ1left,MINUSEQ1right),rest671) end
| (149,(_,(_,BOREQ1left,BOREQ1right))::rest671) => let val result=
MlyValue.assignop(fn _ => (SOME BitwiseOr))
 in (LrTable.NT 56,(result,BOREQ1left,BOREQ1right),rest671) end
| (150,(_,(_,BANDEQ1left,BANDEQ1right))::rest671) => let val result=
MlyValue.assignop(fn _ => (SOME BitwiseAnd))
 in (LrTable.NT 56,(result,BANDEQ1left,BANDEQ1right),rest671) end
| (151,(_,(_,BXOREQ1left,BXOREQ1right))::rest671) => let val result=
MlyValue.assignop(fn _ => (SOME BitwiseXOr))
 in (LrTable.NT 56,(result,BXOREQ1left,BXOREQ1right),rest671) end
| (152,(_,(_,MULEQ1left,MULEQ1right))::rest671) => let val result=
MlyValue.assignop(fn _ => (SOME Times))
 in (LrTable.NT 56,(result,MULEQ1left,MULEQ1right),rest671) end
| (153,(_,(_,DIVEQ1left,DIVEQ1right))::rest671) => let val result=
MlyValue.assignop(fn _ => (SOME Divides))
 in (LrTable.NT 56,(result,DIVEQ1left,DIVEQ1right),rest671) end
| (154,(_,(_,MODEQ1left,MODEQ1right))::rest671) => let val result=
MlyValue.assignop(fn _ => (SOME Modulus))
 in (LrTable.NT 56,(result,MODEQ1left,MODEQ1right),rest671) end
| (155,(_,(_,LSHIFTEQ1left,LSHIFTEQ1right))::rest671) => let val 
result=MlyValue.assignop(fn _ => (SOME LShift))
 in (LrTable.NT 56,(result,LSHIFTEQ1left,LSHIFTEQ1right),rest671) end
| (156,(_,(_,RSHIFTEQ1left,RSHIFTEQ1right))::rest671) => let val 
result=MlyValue.assignop(fn _ => (SOME RShift))
 in (LrTable.NT 56,(result,RSHIFTEQ1left,RSHIFTEQ1right),rest671) end
| (157,(_,(_,_,YSEMIright as YSEMI1right))::(_,(MlyValue.rexpression 
rexpression1,_,_))::(_,(MlyValue.assignop assignop1,_,_))::(_,(
MlyValue.lexpression lexpression1,lexpression1left,_))::rest671) => 
let val result=MlyValue.statement(fn _ => let val lexpression as 
lexpression1=lexpression1 ()
val assignop as assignop1=assignop1 ()
val rexpression as rexpression1=rexpression1 ()
 in (
swrap(parse_stdassignop(lexpression, assignop, rexpression),
             eleft lexpression, YSEMIright)
) end
)
 in (LrTable.NT 41,(result,lexpression1left,YSEMI1right),rest671) end
| (158,(_,(_,_,YSEMIright as YSEMI1right))::(_,(MlyValue.rexpression 
rexpression1,rexpression1left,_))::rest671) => let val result=
MlyValue.statement(fn _ => let val rexpression as rexpression1=
rexpression1 ()
 in (
let val e = delvoidcasts (handle_builtin_fns rexpression)
           val l = eleft rexpression and r = YSEMIright
           val empty = swrap (EmptyStmt, l, r)
       in
         case enode e of
           EFnCall(fn_e, args) => swrap(AssignFnCall(NONE, fn_e, args),l,r)
         | _ => if is_number e then empty
                else if fncall_free e then
                  (warnStr'(l, r,
                            "Ignoring (oddly expressed) expression without \
                            \side effect");
                   empty)
                else
                  (errorStr'(l, r, "Illegal bare expression containing \
                                   \function calls");
                   empty)
       end
) end
)
 in (LrTable.NT 41,(result,rexpression1left,YSEMI1right),rest671) end
| (159,(_,(MlyValue.statement statement1,_,statement1right))::(_,(
MlyValue.invariant_option invariant_option1,_,_))::_::(_,(
MlyValue.rexpression rexpression1,_,_))::_::(_,(_,YWHILEleft as 
YWHILE1left,_))::rest671) => let val result=MlyValue.statement(fn _
 => let val rexpression as rexpression1=rexpression1 ()
val invariant_option as invariant_option1=invariant_option1 ()
val statement as statement1=statement1 ()
 in (
let val body = swrap(Trap(ContinueT, statement), sleft statement,
                            sright statement)
           val loop = swrap(While(rexpression, invariant_option, body),
                            YWHILEleft, sright statement)
       in
         swrap(Trap(BreakT, loop), YWHILEleft, sright statement)
       end
) end
)
 in (LrTable.NT 41,(result,YWHILE1left,statement1right),rest671) end
| (160,(_,(_,_,YSEMIright as YSEMI1right))::_::(_,(
MlyValue.rexpression rexpression1,_,_))::_::_::(_,(MlyValue.statement 
statement1,_,_))::(_,(MlyValue.invariant_option invariant_option1,_,_)
)::(_,(_,YDOleft as YDO1left,_))::rest671) => let val result=
MlyValue.statement(fn _ => let val invariant_option as 
invariant_option1=invariant_option1 ()
val statement as statement1=statement1 ()
val rexpression as rexpression1=rexpression1 ()
 in (
let val body = swrap (Trap(ContinueT, statement),
                             sleft statement, sright statement)
           val loop = swrap(While(rexpression, invariant_option, body),
                            YDOleft, YSEMIright)
       in
         swrap(Trap(BreakT,
                    swrap(Block [BI_Stmt body, BI_Stmt loop],
                          sleft statement, YSEMIright)),
               YDOleft, YSEMIright)
       end
) end
)
 in (LrTable.NT 41,(result,YDO1left,YSEMI1right),rest671) end
| (161,(_,(MlyValue.statement statement1,_,statement1right))::(_,(
MlyValue.invariant_option invariant_option1,_,_))::_::(_,(
MlyValue.opt_for3_expr opt_for3_expr1,_,_))::_::(_,(
MlyValue.opt_for2_expr opt_for2_expr1,_,_))::(_,(
MlyValue.opt_for1_bitem opt_for1_bitem1,_,_))::_::(_,(_,YFORleft as 
YFOR1left,_))::rest671) => let val result=MlyValue.statement(fn _ => 
let val opt_for1_bitem as opt_for1_bitem1=opt_for1_bitem1 ()
val opt_for2_expr as opt_for2_expr1=opt_for2_expr1 ()
val opt_for3_expr as opt_for3_expr1=opt_for3_expr1 ()
val invariant_option as invariant_option1=invariant_option1 ()
val statement as statement1=statement1 ()
 in (
let val body0 = swrap(Trap(ContinueT, statement),
                             sleft statement, sright statement)
           val body = swrap(Block [BI_Stmt body0, BI_Stmt opt_for3_expr],
                            sleft statement, sright statement)
           val loop = swrap(While(opt_for2_expr, invariant_option, body),
                            YFORleft, sright statement)
           val tp_loop = swrap(Trap(BreakT, loop), YFORleft, sright statement)
       in
         swrap(Block (opt_for1_bitem @ [BI_Stmt tp_loop]),
               YFORleft, sright statement)
       end
) end
)
 in (LrTable.NT 41,(result,YFOR1left,statement1right),rest671) end
| (162,(_,(_,_,YSEMIright as YSEMI1right))::(_,(MlyValue.rexpression 
rexpression1,_,_))::(_,(_,YRETURNleft as YRETURN1left,_))::rest671)
 => let val result=MlyValue.statement(fn _ => let val rexpression as 
rexpression1=rexpression1 ()
 in (
case enode (handle_builtin_fns rexpression) of
         EFnCall(fn_e, args) =>
           swrap(ReturnFnCall (fn_e, args), YRETURNleft, YSEMIright)
       | e => swrap(Return (SOME rexpression),YRETURNleft,YSEMIright)
) end
)
 in (LrTable.NT 41,(result,YRETURN1left,YSEMI1right),rest671) end
| (163,(_,(_,_,YSEMIright as YSEMI1right))::(_,(_,YRETURNleft as 
YRETURN1left,_))::rest671) => let val result=MlyValue.statement(fn _
 => (swrap(Return NONE, YRETURNleft, YSEMIright)))
 in (LrTable.NT 41,(result,YRETURN1left,YSEMI1right),rest671) end
| (164,(_,(_,_,YSEMIright as YSEMI1right))::(_,(_,YBREAKleft as 
YBREAK1left,_))::rest671) => let val result=MlyValue.statement(fn _
 => (swrap(Break, YBREAKleft, YSEMIright)))
 in (LrTable.NT 41,(result,YBREAK1left,YSEMI1right),rest671) end
| (165,(_,(_,_,YSEMIright as YSEMI1right))::(_,(_,YCONTINUEleft as 
YCONTINUE1left,_))::rest671) => let val result=MlyValue.statement(fn _
 => (swrap(Continue,YCONTINUEleft,YSEMIright)))
 in (LrTable.NT 41,(result,YCONTINUE1left,YSEMI1right),rest671) end
| (166,(_,(MlyValue.statement statement1,_,statement1right))::_::(_,(
MlyValue.rexpression rexpression1,_,_))::_::(_,(_,YIFleft as YIF1left,
_))::rest671) => let val result=MlyValue.statement(fn _ => let val 
rexpression as rexpression1=rexpression1 ()
val statement as statement1=statement1 ()
 in (
swrap(IfStmt (rexpression, statement,
                     swrap(EmptyStmt, defaultPos, defaultPos)),
             YIFleft,
             sright statement)
) end
)
 in (LrTable.NT 41,(result,YIF1left,statement1right),rest671) end
| (167,(_,(MlyValue.statement statement2,_,statement2right))::_::(_,(
MlyValue.statement statement1,_,_))::_::(_,(MlyValue.rexpression 
rexpression1,_,_))::_::(_,(_,YIFleft as YIF1left,_))::rest671) => let 
val result=MlyValue.statement(fn _ => let val rexpression as 
rexpression1=rexpression1 ()
val statement1=statement1 ()
val statement2=statement2 ()
 in (
swrap(IfStmt(rexpression, statement1, statement2), YIFleft,
             sright statement2)
) end
)
 in (LrTable.NT 41,(result,YIF1left,statement2right),rest671) end
| (168,(_,(_,YSEMIleft as YSEMI1left,YSEMIright as YSEMI1right))::
rest671) => let val result=MlyValue.statement(fn _ => (
swrap(EmptyStmt,YSEMIleft,YSEMIright)))
 in (LrTable.NT 41,(result,YSEMI1left,YSEMI1right),rest671) end
| (169,(_,(_,_,YSEMIright as YSEMI1right))::_::(_,(
MlyValue.lexpression lexpression1,lexpression1left,_))::rest671) => 
let val result=MlyValue.statement(fn _ => let val lexpression as 
lexpression1=lexpression1 ()
 in (swrap(postinc lexpression, eleft lexpression, YSEMIright)) end
)
 in (LrTable.NT 41,(result,lexpression1left,YSEMI1right),rest671) end
| (170,(_,(_,_,YSEMIright as YSEMI1right))::_::(_,(
MlyValue.lexpression lexpression1,lexpression1left,_))::rest671) => 
let val result=MlyValue.statement(fn _ => let val lexpression as 
lexpression1=lexpression1 ()
 in (swrap(postdec lexpression, eleft lexpression, YSEMIright)) end
)
 in (LrTable.NT 41,(result,lexpression1left,YSEMI1right),rest671) end
| (171,(_,(_,_,RCURLYright as RCURLY1right))::(_,(
MlyValue.switchcase_list switchcase_list1,_,_))::_::_::(_,(
MlyValue.rexpression rexpression1,_,_))::_::(_,(_,SWITCHleft as 
SWITCH1left,_))::rest671) => let val result=MlyValue.statement(fn _
 => let val rexpression as rexpression1=rexpression1 ()
val switchcase_list as switchcase_list1=switchcase_list1 ()
 in (
swrap(Trap(BreakT,
                  swrap(Switch(rexpression,
                               switch_check switchcase_list
                                            SWITCHleft RCURLYright),
                        SWITCHleft, RCURLYright)),
             SWITCHleft, RCURLYright)
) end
)
 in (LrTable.NT 41,(result,SWITCH1left,RCURLY1right),rest671) end
| (172,(_,(MlyValue.compound_statement compound_statement1,
compound_statement1left,compound_statement1right))::rest671) => let 
val result=MlyValue.statement(fn _ => let val compound_statement as 
compound_statement1=compound_statement1 ()
 in (
swrap(Block (node compound_statement), left compound_statement,
             right compound_statement)
) end
)
 in (LrTable.NT 41,(result,compound_statement1left,
compound_statement1right),rest671) end
| (173,(_,(_,_,SPEC_BLOCKEND1right))::(_,(MlyValue.STRING_LITERAL 
STRING_LITERAL1,_,STRING_LITERALright))::(_,(_,AUXUPDleft as 
AUXUPD1left,_))::rest671) => let val result=MlyValue.statement(fn _
 => let val STRING_LITERAL as STRING_LITERAL1=STRING_LITERAL1 ()
 in (swrap(Auxupd STRING_LITERAL, AUXUPDleft, STRING_LITERALright))
 end
)
 in (LrTable.NT 41,(result,AUXUPD1left,SPEC_BLOCKEND1right),rest671)
 end
| (174,(_,(_,_,SPEC_BLOCKEND1right))::(_,(MlyValue.STRING_LITERAL 
STRING_LITERAL1,_,STRING_LITERALright))::(_,(_,GHOSTUPDleft as 
GHOSTUPD1left,_))::rest671) => let val result=MlyValue.statement(fn _
 => let val STRING_LITERAL as STRING_LITERAL1=STRING_LITERAL1 ()
 in (swrap(Ghostupd STRING_LITERAL, GHOSTUPDleft, STRING_LITERALright)
) end
)
 in (LrTable.NT 41,(result,GHOSTUPD1left,SPEC_BLOCKEND1right),rest671)
 end
| (175,(_,(_,_,SPEC_BLOCKEND2right))::(_,(MlyValue.STRING_LITERAL 
STRING_LITERAL2,_,_))::(_,(_,_,SPEC_ENDright))::(_,(
MlyValue.statement_list statement_list1,_,_))::_::(_,(
MlyValue.STRING_LITERAL STRING_LITERAL1,_,_))::(_,(_,SPEC_BEGINleft
 as SPEC_BEGIN1left,_))::rest671) => let val result=MlyValue.statement
(fn _ => let val STRING_LITERAL1=STRING_LITERAL1 ()
val statement_list as statement_list1=statement_list1 ()
val STRING_LITERAL2=STRING_LITERAL2 ()
 in (
let
        open Substring
        val ss = full STRING_LITERAL1
        val (before_fullstop, inc_stop) = splitl (fn c => c <> #".") ss
        val after_stop = triml 1 inc_stop
      in
        swrap(Spec((string before_fullstop, string after_stop),
                   statement_list,STRING_LITERAL2),
            SPEC_BEGINleft,
            SPEC_ENDright)
      end
) end
)
 in (LrTable.NT 41,(result,SPEC_BEGIN1left,SPEC_BLOCKEND2right),
rest671) end
| (176,(_,(_,_,YSEMIright as YSEMI1right))::_::(_,(MlyValue.asmblock 
asmblock1,_,_))::_::(_,(MlyValue.optvolatile optvolatile1,_,_))::(_,(_
,YASMleft as YASM1left,_))::rest671) => let val result=
MlyValue.statement(fn _ => let val optvolatile as optvolatile1=
optvolatile1 ()
val asmblock as asmblock1=asmblock1 ()
 in (
swrap(AsmStmt({volatilep = optvolatile, asmblock = asmblock}),
             YASMleft, YSEMIright)
) end
)
 in (LrTable.NT 41,(result,YASM1left,YSEMI1right),rest671) end
| (177,rest671) => let val result=MlyValue.optvolatile(fn _ => (false)
)
 in (LrTable.NT 4,(result,defaultPos,defaultPos),rest671) end
| (178,(_,(_,VOLATILE1left,VOLATILE1right))::rest671) => let val 
result=MlyValue.optvolatile(fn _ => (true))
 in (LrTable.NT 4,(result,VOLATILE1left,VOLATILE1right),rest671) end
| (179,(_,(MlyValue.asmmod1 asmmod11,_,asmmod11right))::(_,(
MlyValue.cstring_literal cstring_literal1,cstring_literal1left,_))::
rest671) => let val result=MlyValue.asmblock(fn _ => let val 
cstring_literal as cstring_literal1=cstring_literal1 ()
val asmmod1 as asmmod11=asmmod11 ()
 in (
{head = node cstring_literal,
                            mod1 = #1 asmmod1,
                            mod2 = #2 asmmod1,
                            mod3 = #3 asmmod1}
) end
)
 in (LrTable.NT 94,(result,cstring_literal1left,asmmod11right),rest671
) end
| (180,rest671) => let val result=MlyValue.asmmod1(fn _ => ([], [], []
))
 in (LrTable.NT 95,(result,defaultPos,defaultPos),rest671) end
| (181,(_,(MlyValue.asmmod2 asmmod21,_,asmmod21right))::(_,(
MlyValue.namedstringexplist namedstringexplist1,_,_))::(_,(_,
YCOLON1left,_))::rest671) => let val result=MlyValue.asmmod1(fn _ => 
let val namedstringexplist as namedstringexplist1=namedstringexplist1 
()
val asmmod2 as asmmod21=asmmod21 ()
 in (namedstringexplist, #1 asmmod2, #2 asmmod2) end
)
 in (LrTable.NT 95,(result,YCOLON1left,asmmod21right),rest671) end
| (182,rest671) => let val result=MlyValue.asmmod2(fn _ => ([], []))
 in (LrTable.NT 96,(result,defaultPos,defaultPos),rest671) end
| (183,(_,(MlyValue.asmmod3 asmmod31,_,asmmod31right))::(_,(
MlyValue.namedstringexplist namedstringexplist1,_,_))::(_,(_,
YCOLON1left,_))::rest671) => let val result=MlyValue.asmmod2(fn _ => 
let val namedstringexplist as namedstringexplist1=namedstringexplist1 
()
val asmmod3 as asmmod31=asmmod31 ()
 in ((namedstringexplist, asmmod3)) end
)
 in (LrTable.NT 96,(result,YCOLON1left,asmmod31right),rest671) end
| (184,rest671) => let val result=MlyValue.asmmod3(fn _ => ([]))
 in (LrTable.NT 97,(result,defaultPos,defaultPos),rest671) end
| (185,(_,(MlyValue.stringlist1 stringlist11,_,stringlist11right))::(_
,(_,YCOLON1left,_))::rest671) => let val result=MlyValue.asmmod3(fn _
 => let val stringlist1 as stringlist11=stringlist11 ()
 in (stringlist1) end
)
 in (LrTable.NT 97,(result,YCOLON1left,stringlist11right),rest671) end
| (186,(_,(MlyValue.cstring_literal cstring_literal1,
cstring_literal1left,cstring_literal1right))::rest671) => let val 
result=MlyValue.stringlist1(fn _ => let val cstring_literal as 
cstring_literal1=cstring_literal1 ()
 in ([node cstring_literal]) end
)
 in (LrTable.NT 99,(result,cstring_literal1left,cstring_literal1right)
,rest671) end
| (187,(_,(MlyValue.stringlist1 stringlist11,_,stringlist11right))::_
::(_,(MlyValue.cstring_literal cstring_literal1,cstring_literal1left,_
))::rest671) => let val result=MlyValue.stringlist1(fn _ => let val 
cstring_literal as cstring_literal1=cstring_literal1 ()
val stringlist1 as stringlist11=stringlist11 ()
 in (node cstring_literal :: stringlist1) end
)
 in (LrTable.NT 99,(result,cstring_literal1left,stringlist11right),
rest671) end
| (188,rest671) => let val result=MlyValue.namedstringexplist(fn _ => 
([]))
 in (LrTable.NT 101,(result,defaultPos,defaultPos),rest671) end
| (189,(_,(MlyValue.namedstringexplist1 namedstringexplist11,
namedstringexplist11left,namedstringexplist11right))::rest671) => let 
val result=MlyValue.namedstringexplist(fn _ => let val 
namedstringexplist1 as namedstringexplist11=namedstringexplist11 ()
 in (namedstringexplist1) end
)
 in (LrTable.NT 101,(result,namedstringexplist11left,
namedstringexplist11right),rest671) end
| (190,(_,(MlyValue.namedstringexp namedstringexp1,namedstringexp1left
,namedstringexp1right))::rest671) => let val result=
MlyValue.namedstringexplist1(fn _ => let val namedstringexp as 
namedstringexp1=namedstringexp1 ()
 in ([namedstringexp]) end
)
 in (LrTable.NT 102,(result,namedstringexp1left,namedstringexp1right),
rest671) end
| (191,(_,(MlyValue.namedstringexplist1 namedstringexplist11,_,
namedstringexplist11right))::_::(_,(MlyValue.namedstringexp 
namedstringexp1,namedstringexp1left,_))::rest671) => let val result=
MlyValue.namedstringexplist1(fn _ => let val namedstringexp as 
namedstringexp1=namedstringexp1 ()
val namedstringexplist1 as namedstringexplist11=namedstringexplist11 
()
 in (namedstringexp :: namedstringexplist1) end
)
 in (LrTable.NT 102,(result,namedstringexp1left,
namedstringexplist11right),rest671) end
| (192,(_,(_,_,RPAREN1right))::(_,(MlyValue.rexpression rexpression1,_
,_))::_::(_,(MlyValue.cstring_literal cstring_literal1,
cstring_literal1left,_))::rest671) => let val result=
MlyValue.namedstringexp(fn _ => let val cstring_literal as 
cstring_literal1=cstring_literal1 ()
val rexpression as rexpression1=rexpression1 ()
 in ((NONE, node cstring_literal, rexpression)) end
)
 in (LrTable.NT 100,(result,cstring_literal1left,RPAREN1right),rest671
) end
| (193,(_,(_,_,RPAREN1right))::(_,(MlyValue.rexpression rexpression1,_
,_))::_::(_,(MlyValue.cstring_literal cstring_literal1,_,_))::_::(_,(
MlyValue.ID ID1,_,_))::(_,(_,LBRACKET1left,_))::rest671) => let val 
result=MlyValue.namedstringexp(fn _ => let val ID as ID1=ID1 ()
val cstring_literal as cstring_literal1=cstring_literal1 ()
val rexpression as rexpression1=rexpression1 ()
 in ((SOME ID, node cstring_literal, rexpression)) end
)
 in (LrTable.NT 100,(result,LBRACKET1left,RPAREN1right),rest671) end
| (194,(_,(_,_,SPEC_BLOCKEND1right))::(_,(MlyValue.STRING_LITERAL 
STRING_LITERAL1,STRING_LITERALleft,STRING_LITERALright))::(_,(_,
INVARIANT1left,_))::rest671) => let val result=MlyValue.invariant(fn _
 => let val STRING_LITERAL as STRING_LITERAL1=STRING_LITERAL1 ()
 in (wrap(STRING_LITERAL, STRING_LITERALleft, STRING_LITERALright))
 end
)
 in (LrTable.NT 17,(result,INVARIANT1left,SPEC_BLOCKEND1right),rest671
) end
| (195,rest671) => let val result=MlyValue.invariant_option(fn _ => (
NONE))
 in (LrTable.NT 18,(result,defaultPos,defaultPos),rest671) end
| (196,(_,(MlyValue.invariant invariant1,invariant1left,
invariant1right))::rest671) => let val result=
MlyValue.invariant_option(fn _ => let val invariant as invariant1=
invariant1 ()
 in (SOME invariant) end
)
 in (LrTable.NT 18,(result,invariant1left,invariant1right),rest671)
 end
| (197,rest671) => let val result=MlyValue.switchcase_list(fn _ => ([]
))
 in (LrTable.NT 44,(result,defaultPos,defaultPos),rest671) end
| (198,(_,(MlyValue.switchcase_list switchcase_list1,_,
switchcase_list1right))::(_,(MlyValue.switchcase switchcase1,
switchcase1left,_))::rest671) => let val result=
MlyValue.switchcase_list(fn _ => let val switchcase as switchcase1=
switchcase1 ()
val switchcase_list as switchcase_list1=switchcase_list1 ()
 in (switchcase :: switchcase_list) end
)
 in (LrTable.NT 44,(result,switchcase1left,switchcase_list1right),
rest671) end
| (199,(_,(MlyValue.block_item_list block_item_list1,_,
block_item_list1right))::(_,(MlyValue.statement statement1,_,_))::(_,(
MlyValue.labellist labellist1,labellist1left,_))::rest671) => let val 
result=MlyValue.switchcase(fn _ => let val labellist as labellist1=
labellist1 ()
val statement as statement1=statement1 ()
val block_item_list as block_item_list1=block_item_list1 ()
 in ((labellist, BI_Stmt statement :: block_item_list)) end
)
 in (LrTable.NT 45,(result,labellist1left,block_item_list1right),
rest671) end
| (200,(_,(MlyValue.label label1,label1left,label1right))::rest671)
 => let val result=MlyValue.labellist(fn _ => let val label as label1=
label1 ()
 in (wrap([label], left label, right label)) end
)
 in (LrTable.NT 46,(result,label1left,label1right),rest671) end
| (201,(_,(MlyValue.labellist labellist1,_,labellist1right))::(_,(
MlyValue.label label1,label1left,_))::rest671) => let val result=
MlyValue.labellist(fn _ => let val label as label1=label1 ()
val labellist as labellist1=labellist1 ()
 in (wrap(label::node labellist, left label, right labellist)) end
)
 in (LrTable.NT 46,(result,label1left,labellist1right),rest671) end
| (202,(_,(_,_,YCOLONright as YCOLON1right))::(_,(MlyValue.rexpression
 rexpression1,_,_))::(_,(_,CASEleft as CASE1left,_))::rest671) => let 
val result=MlyValue.label(fn _ => let val rexpression as rexpression1=
rexpression1 ()
 in (wrap(SOME rexpression, CASEleft, YCOLONright)) end
)
 in (LrTable.NT 47,(result,CASE1left,YCOLON1right),rest671) end
| (203,(_,(_,_,YCOLONright as YCOLON1right))::(_,(_,DEFAULTleft as 
DEFAULT1left,_))::rest671) => let val result=MlyValue.label(fn _ => (
wrap(NONE, DEFAULTleft, YCOLONright)))
 in (LrTable.NT 47,(result,DEFAULT1left,YCOLON1right),rest671) end
| (204,(_,(_,_,YSEMI1right))::(_,(MlyValue.opt_for1_expr 
opt_for1_expr1,opt_for1_expr1left,_))::rest671) => let val result=
MlyValue.opt_for1_bitem(fn _ => let val opt_for1_expr as 
opt_for1_expr1=opt_for1_expr1 ()
 in ([BI_Stmt opt_for1_expr]) end
)
 in (LrTable.NT 48,(result,opt_for1_expr1left,YSEMI1right),rest671)
 end
| (205,(_,(MlyValue.declaration declaration1,declaration1left,
declaration1right))::rest671) => let val result=
MlyValue.opt_for1_bitem(fn _ => let val declaration as declaration1=
declaration1 ()
 in (map BI_Decl declaration) end
)
 in (LrTable.NT 48,(result,declaration1left,declaration1right),rest671
) end
| (206,rest671) => let val result=MlyValue.opt_for1_expr(fn _ => (
swrap(EmptyStmt, defaultPos, defaultPos)))
 in (LrTable.NT 49,(result,defaultPos,defaultPos),rest671) end
| (207,(_,(MlyValue.opt_for1_expr0 opt_for1_expr01,opt_for1_expr01left
,opt_for1_expr01right))::rest671) => let val result=
MlyValue.opt_for1_expr(fn _ => let val opt_for1_expr0 as 
opt_for1_expr01=opt_for1_expr01 ()
 in (
if length opt_for1_expr0 = 1 then
         hd opt_for1_expr0
       else swrap(Block(map BI_Stmt opt_for1_expr0),
                  sleft (hd opt_for1_expr0),
                  sright (List.last opt_for1_expr0))
) end
)
 in (LrTable.NT 49,(result,opt_for1_expr01left,opt_for1_expr01right),
rest671) end
| (208,(_,(MlyValue.opt_for1_exprbase opt_for1_exprbase1,
opt_for1_exprbase1left,opt_for1_exprbase1right))::rest671) => let val 
result=MlyValue.opt_for1_expr0(fn _ => let val opt_for1_exprbase as 
opt_for1_exprbase1=opt_for1_exprbase1 ()
 in ([opt_for1_exprbase]) end
)
 in (LrTable.NT 50,(result,opt_for1_exprbase1left,
opt_for1_exprbase1right),rest671) end
| (209,(_,(MlyValue.opt_for1_expr0 opt_for1_expr01,_,
opt_for1_expr01right))::_::(_,(MlyValue.opt_for1_exprbase 
opt_for1_exprbase1,opt_for1_exprbase1left,_))::rest671) => let val 
result=MlyValue.opt_for1_expr0(fn _ => let val opt_for1_exprbase as 
opt_for1_exprbase1=opt_for1_exprbase1 ()
val opt_for1_expr0 as opt_for1_expr01=opt_for1_expr01 ()
 in (opt_for1_exprbase::opt_for1_expr0) end
)
 in (LrTable.NT 50,(result,opt_for1_exprbase1left,opt_for1_expr01right
),rest671) end
| (210,(_,(MlyValue.rexpression rexpression1,_,rexpression1right))::_
::(_,(MlyValue.lexpression lexpression1,lexpression1left,_))::rest671)
 => let val result=MlyValue.opt_for1_exprbase(fn _ => let val 
lexpression as lexpression1=lexpression1 ()
val rexpression as rexpression1=rexpression1 ()
 in (
swrap(Assign(lexpression,rexpression),
             eleft lexpression, eright rexpression)
) end
)
 in (LrTable.NT 51,(result,lexpression1left,rexpression1right),rest671
) end
| (211,rest671) => let val result=MlyValue.opt_for2_expr(fn _ => (
expr_int 1))
 in (LrTable.NT 52,(result,defaultPos,defaultPos),rest671) end
| (212,(_,(MlyValue.rexpression rexpression1,rexpression1left,
rexpression1right))::rest671) => let val result=MlyValue.opt_for2_expr
(fn _ => let val rexpression as rexpression1=rexpression1 ()
 in (rexpression) end
)
 in (LrTable.NT 52,(result,rexpression1left,rexpression1right),rest671
) end
| (213,rest671) => let val result=MlyValue.opt_for3_expr(fn _ => (
swrap(EmptyStmt,defaultPos,defaultPos)))
 in (LrTable.NT 53,(result,defaultPos,defaultPos),rest671) end
| (214,(_,(MlyValue.opt_for3_expr0 opt_for3_expr01,opt_for3_expr01left
,opt_for3_expr01right))::rest671) => let val result=
MlyValue.opt_for3_expr(fn _ => let val opt_for3_expr0 as 
opt_for3_expr01=opt_for3_expr01 ()
 in (
if length opt_for3_expr0 = 1 then
         hd opt_for3_expr0
       else swrap(Block(map BI_Stmt opt_for3_expr0),
                  sleft (hd opt_for3_expr0),
                  sright (List.last opt_for3_expr0))
) end
)
 in (LrTable.NT 53,(result,opt_for3_expr01left,opt_for3_expr01right),
rest671) end
| (215,(_,(MlyValue.opt_for3_exprbase opt_for3_exprbase1,
opt_for3_exprbase1left,opt_for3_exprbase1right))::rest671) => let val 
result=MlyValue.opt_for3_expr0(fn _ => let val opt_for3_exprbase as 
opt_for3_exprbase1=opt_for3_exprbase1 ()
 in ([opt_for3_exprbase]) end
)
 in (LrTable.NT 54,(result,opt_for3_exprbase1left,
opt_for3_exprbase1right),rest671) end
| (216,(_,(_,_,SPEC_BLOCKEND1right))::(_,(MlyValue.STRING_LITERAL 
STRING_LITERAL1,_,STRING_LITERALright))::(_,(_,AUXUPDleft,_))::(_,(
MlyValue.opt_for3_exprbase opt_for3_exprbase1,opt_for3_exprbase1left,_
))::rest671) => let val result=MlyValue.opt_for3_expr0(fn _ => let 
val opt_for3_exprbase as opt_for3_exprbase1=opt_for3_exprbase1 ()
val STRING_LITERAL as STRING_LITERAL1=STRING_LITERAL1 ()
 in (
[opt_for3_exprbase, swrap(Auxupd STRING_LITERAL, AUXUPDleft,
                                           STRING_LITERALright)]
) end
)
 in (LrTable.NT 54,(result,opt_for3_exprbase1left,SPEC_BLOCKEND1right)
,rest671) end
| (217,(_,(MlyValue.opt_for3_expr0 opt_for3_expr01,_,
opt_for3_expr01right))::_::(_,(MlyValue.opt_for3_exprbase 
opt_for3_exprbase1,opt_for3_exprbase1left,_))::rest671) => let val 
result=MlyValue.opt_for3_expr0(fn _ => let val opt_for3_exprbase as 
opt_for3_exprbase1=opt_for3_exprbase1 ()
val opt_for3_expr0 as opt_for3_expr01=opt_for3_expr01 ()
 in (opt_for3_exprbase::opt_for3_expr0) end
)
 in (LrTable.NT 54,(result,opt_for3_exprbase1left,opt_for3_expr01right
),rest671) end
| (218,(_,(MlyValue.rexpression rexpression1,_,rexpression1right))::(_
,(MlyValue.assignop assignop1,_,_))::(_,(MlyValue.lexpression 
lexpression1,lexpression1left,_))::rest671) => let val result=
MlyValue.opt_for3_exprbase(fn _ => let val lexpression as lexpression1
=lexpression1 ()
val assignop as assignop1=assignop1 ()
val rexpression as rexpression1=rexpression1 ()
 in (
swrap(parse_stdassignop(lexpression, assignop, rexpression),
             eleft lexpression, eright rexpression)
) end
)
 in (LrTable.NT 55,(result,lexpression1left,rexpression1right),rest671
) end
| (219,(_,(_,_,PLUSPLUSright as PLUSPLUS1right))::(_,(
MlyValue.lexpression lexpression1,lexpression1left,_))::rest671) => 
let val result=MlyValue.opt_for3_exprbase(fn _ => let val lexpression
 as lexpression1=lexpression1 ()
 in (
swrap(postinc lexpression, eleft lexpression,
                       PLUSPLUSright)
) end
)
 in (LrTable.NT 55,(result,lexpression1left,PLUSPLUS1right),rest671)
 end
| (220,(_,(_,_,MINUSMINUSright as MINUSMINUS1right))::(_,(
MlyValue.lexpression lexpression1,lexpression1left,_))::rest671) => 
let val result=MlyValue.opt_for3_exprbase(fn _ => let val lexpression
 as lexpression1=lexpression1 ()
 in (
swrap(postdec lexpression, eleft lexpression,
                       MINUSMINUSright)
) end
)
 in (LrTable.NT 55,(result,lexpression1left,MINUSMINUS1right),rest671)
 end
| (221,rest671) => let val result=MlyValue.opt_rexpr_list(fn _ => (
wrap([], defaultPos, defaultPos)))
 in (LrTable.NT 73,(result,defaultPos,defaultPos),rest671) end
| (222,(_,(MlyValue.rexpr_list rexpr_list1,rexpr_list1left,
rexpr_list1right))::rest671) => let val result=MlyValue.opt_rexpr_list
(fn _ => let val rexpr_list as rexpr_list1=rexpr_list1 ()
 in (rexpr_list) end
)
 in (LrTable.NT 73,(result,rexpr_list1left,rexpr_list1right),rest671)
 end
| (223,(_,(MlyValue.rexpression rexpression1,rexpression1left,
rexpression1right))::rest671) => let val result=MlyValue.rexpr_list(
fn _ => let val rexpression as rexpression1=rexpression1 ()
 in (
wrap([rexpression], eleft rexpression,
                               eright rexpression)
) end
)
 in (LrTable.NT 72,(result,rexpression1left,rexpression1right),rest671
) end
| (224,(_,(MlyValue.rexpr_list rexpr_list1,_,rexpr_list1right))::_::(_
,(MlyValue.rexpression rexpression1,rexpression1left,_))::rest671) => 
let val result=MlyValue.rexpr_list(fn _ => let val rexpression as 
rexpression1=rexpression1 ()
val rexpr_list as rexpr_list1=rexpr_list1 ()
 in (
wrap (rexpression :: node rexpr_list,
                       eleft rexpression, right rexpr_list)
) end
)
 in (LrTable.NT 72,(result,rexpression1left,rexpr_list1right),rest671)
 end
| (225,(_,(MlyValue.logical_OR_expression logical_OR_expression1,
logical_OR_expression1left,logical_OR_expression1right))::rest671) => 
let val result=MlyValue.rexpression(fn _ => let val 
logical_OR_expression as logical_OR_expression1=logical_OR_expression1
 ()
 in (logical_OR_expression) end
)
 in (LrTable.NT 71,(result,logical_OR_expression1left,
logical_OR_expression1right),rest671) end
| (226,(_,(MlyValue.rexpression rexpression2,_,rexpression2right))::_
::(_,(MlyValue.rexpression rexpression1,_,_))::_::(_,(
MlyValue.logical_OR_expression logical_OR_expression1,
logical_OR_expression1left,_))::rest671) => let val result=
MlyValue.rexpression(fn _ => let val logical_OR_expression as 
logical_OR_expression1=logical_OR_expression1 ()
val rexpression1=rexpression1 ()
val rexpression2=rexpression2 ()
 in (
ewrap(CondExp(logical_OR_expression, rexpression1,
                               rexpression2),
                       eleft logical_OR_expression,
                       eright rexpression2)
) end
)
 in (LrTable.NT 71,(result,logical_OR_expression1left,
rexpression2right),rest671) end
| (227,(_,(MlyValue.logical_AND_expression logical_AND_expression1,
logical_AND_expression1left,logical_AND_expression1right))::rest671)
 => let val result=MlyValue.logical_OR_expression(fn _ => let val 
logical_AND_expression as logical_AND_expression1=
logical_AND_expression1 ()
 in (logical_AND_expression) end
)
 in (LrTable.NT 75,(result,logical_AND_expression1left,
logical_AND_expression1right),rest671) end
| (228,(_,(MlyValue.logical_AND_expression logical_AND_expression1,_,
logical_AND_expression1right))::_::(_,(MlyValue.logical_OR_expression 
logical_OR_expression1,logical_OR_expression1left,_))::rest671) => 
let val result=MlyValue.logical_OR_expression(fn _ => let val 
logical_OR_expression as logical_OR_expression1=logical_OR_expression1
 ()
val logical_AND_expression as logical_AND_expression1=
logical_AND_expression1 ()
 in (
ewrap(BinOp(LogOr, logical_OR_expression,
                             logical_AND_expression),
                       eleft logical_OR_expression,
                       eright logical_AND_expression)
) end
)
 in (LrTable.NT 75,(result,logical_OR_expression1left,
logical_AND_expression1right),rest671) end
| (229,(_,(MlyValue.inclusive_OR_expression inclusive_OR_expression1,
inclusive_OR_expression1left,inclusive_OR_expression1right))::rest671)
 => let val result=MlyValue.logical_AND_expression(fn _ => let val 
inclusive_OR_expression as inclusive_OR_expression1=
inclusive_OR_expression1 ()
 in (inclusive_OR_expression) end
)
 in (LrTable.NT 74,(result,inclusive_OR_expression1left,
inclusive_OR_expression1right),rest671) end
| (230,(_,(MlyValue.inclusive_OR_expression inclusive_OR_expression1,_
,inclusive_OR_expression1right))::_::(_,(
MlyValue.logical_AND_expression logical_AND_expression1,
logical_AND_expression1left,_))::rest671) => let val result=
MlyValue.logical_AND_expression(fn _ => let val logical_AND_expression
 as logical_AND_expression1=logical_AND_expression1 ()
val inclusive_OR_expression as inclusive_OR_expression1=
inclusive_OR_expression1 ()
 in (
ewrap(BinOp(LogAnd, logical_AND_expression, inclusive_OR_expression),
                       eleft logical_AND_expression,
                       eright inclusive_OR_expression)
) end
)
 in (LrTable.NT 74,(result,logical_AND_expression1left,
inclusive_OR_expression1right),rest671) end
| (231,(_,(MlyValue.exclusive_OR_expression exclusive_OR_expression1,
exclusive_OR_expression1left,exclusive_OR_expression1right))::rest671)
 => let val result=MlyValue.inclusive_OR_expression(fn _ => let val 
exclusive_OR_expression as exclusive_OR_expression1=
exclusive_OR_expression1 ()
 in (exclusive_OR_expression) end
)
 in (LrTable.NT 76,(result,exclusive_OR_expression1left,
exclusive_OR_expression1right),rest671) end
| (232,(_,(MlyValue.exclusive_OR_expression exclusive_OR_expression1,_
,exclusive_OR_expression1right))::_::(_,(
MlyValue.inclusive_OR_expression inclusive_OR_expression1,
inclusive_OR_expression1left,_))::rest671) => let val result=
MlyValue.inclusive_OR_expression(fn _ => let val 
inclusive_OR_expression as inclusive_OR_expression1=
inclusive_OR_expression1 ()
val exclusive_OR_expression as exclusive_OR_expression1=
exclusive_OR_expression1 ()
 in (
ewrap(BinOp(BitwiseOr, inclusive_OR_expression,
                              exclusive_OR_expression),
                        eleft inclusive_OR_expression,
                        eright exclusive_OR_expression)
) end
)
 in (LrTable.NT 76,(result,inclusive_OR_expression1left,
exclusive_OR_expression1right),rest671) end
| (233,(_,(MlyValue.AND_expression AND_expression1,AND_expression1left
,AND_expression1right))::rest671) => let val result=
MlyValue.exclusive_OR_expression(fn _ => let val AND_expression as 
AND_expression1=AND_expression1 ()
 in (AND_expression) end
)
 in (LrTable.NT 77,(result,AND_expression1left,AND_expression1right),
rest671) end
| (234,(_,(MlyValue.AND_expression AND_expression1,_,
AND_expression1right))::_::(_,(MlyValue.exclusive_OR_expression 
exclusive_OR_expression1,exclusive_OR_expression1left,_))::rest671)
 => let val result=MlyValue.exclusive_OR_expression(fn _ => let val 
exclusive_OR_expression as exclusive_OR_expression1=
exclusive_OR_expression1 ()
val AND_expression as AND_expression1=AND_expression1 ()
 in (
ewrap(BinOp(BitwiseXOr, exclusive_OR_expression,
                              AND_expression),
                        eleft exclusive_OR_expression,
                        eright AND_expression)
) end
)
 in (LrTable.NT 77,(result,exclusive_OR_expression1left,
AND_expression1right),rest671) end
| (235,(_,(MlyValue.equality_expression equality_expression1,
equality_expression1left,equality_expression1right))::rest671) => let 
val result=MlyValue.AND_expression(fn _ => let val equality_expression
 as equality_expression1=equality_expression1 ()
 in (equality_expression) end
)
 in (LrTable.NT 78,(result,equality_expression1left,
equality_expression1right),rest671) end
| (236,(_,(MlyValue.equality_expression equality_expression1,_,
equality_expression1right))::_::(_,(MlyValue.AND_expression 
AND_expression1,AND_expression1left,_))::rest671) => let val result=
MlyValue.AND_expression(fn _ => let val AND_expression as 
AND_expression1=AND_expression1 ()
val equality_expression as equality_expression1=equality_expression1 
()
 in (
ewrap(BinOp(BitwiseAnd, AND_expression, equality_expression),
                       eleft AND_expression,
                       eright equality_expression)
) end
)
 in (LrTable.NT 78,(result,AND_expression1left,
equality_expression1right),rest671) end
| (237,(_,(MlyValue.relational_expression relational_expression1,
relational_expression1left,relational_expression1right))::rest671) => 
let val result=MlyValue.equality_expression(fn _ => let val 
relational_expression as relational_expression1=relational_expression1
 ()
 in (relational_expression) end
)
 in (LrTable.NT 79,(result,relational_expression1left,
relational_expression1right),rest671) end
| (238,(_,(MlyValue.relational_expression relational_expression1,_,
relational_expression1right))::_::(_,(MlyValue.equality_expression 
equality_expression1,equality_expression1left,_))::rest671) => let 
val result=MlyValue.equality_expression(fn _ => let val 
equality_expression as equality_expression1=equality_expression1 ()
val relational_expression as relational_expression1=
relational_expression1 ()
 in (
ewrap(BinOp(Equals, equality_expression, relational_expression),
                       eleft equality_expression,
                       eright relational_expression)
) end
)
 in (LrTable.NT 79,(result,equality_expression1left,
relational_expression1right),rest671) end
| (239,(_,(MlyValue.relational_expression relational_expression1,_,
relational_expression1right))::_::(_,(MlyValue.equality_expression 
equality_expression1,equality_expression1left,_))::rest671) => let 
val result=MlyValue.equality_expression(fn _ => let val 
equality_expression as equality_expression1=equality_expression1 ()
val relational_expression as relational_expression1=
relational_expression1 ()
 in (
ewrap(BinOp(NotEquals, equality_expression, relational_expression),
                       eleft equality_expression,
                       eright relational_expression)
) end
)
 in (LrTable.NT 79,(result,equality_expression1left,
relational_expression1right),rest671) end
| (240,(_,(MlyValue.shift_expression shift_expression1,
shift_expression1left,shift_expression1right))::rest671) => let val 
result=MlyValue.relational_expression(fn _ => let val shift_expression
 as shift_expression1=shift_expression1 ()
 in (shift_expression) end
)
 in (LrTable.NT 80,(result,shift_expression1left,
shift_expression1right),rest671) end
| (241,(_,(MlyValue.shift_expression shift_expression1,_,
shift_expression1right))::_::(_,(MlyValue.relational_expression 
relational_expression1,relational_expression1left,_))::rest671) => 
let val result=MlyValue.relational_expression(fn _ => let val 
relational_expression as relational_expression1=relational_expression1
 ()
val shift_expression as shift_expression1=shift_expression1 ()
 in (
ewrap(BinOp(Lt, relational_expression, shift_expression),
                       eleft relational_expression,
                       eright shift_expression)
) end
)
 in (LrTable.NT 80,(result,relational_expression1left,
shift_expression1right),rest671) end
| (242,(_,(MlyValue.shift_expression shift_expression1,_,
shift_expression1right))::_::(_,(MlyValue.relational_expression 
relational_expression1,relational_expression1left,_))::rest671) => 
let val result=MlyValue.relational_expression(fn _ => let val 
relational_expression as relational_expression1=relational_expression1
 ()
val shift_expression as shift_expression1=shift_expression1 ()
 in (
ewrap(BinOp(Gt, relational_expression, shift_expression),
                       eleft relational_expression,
                       eright shift_expression)
) end
)
 in (LrTable.NT 80,(result,relational_expression1left,
shift_expression1right),rest671) end
| (243,(_,(MlyValue.shift_expression shift_expression1,_,
shift_expression1right))::_::(_,(MlyValue.relational_expression 
relational_expression1,relational_expression1left,_))::rest671) => 
let val result=MlyValue.relational_expression(fn _ => let val 
relational_expression as relational_expression1=relational_expression1
 ()
val shift_expression as shift_expression1=shift_expression1 ()
 in (
ewrap(BinOp(Leq, relational_expression, shift_expression),
                       eleft relational_expression,
                       eright shift_expression)
) end
)
 in (LrTable.NT 80,(result,relational_expression1left,
shift_expression1right),rest671) end
| (244,(_,(MlyValue.shift_expression shift_expression1,_,
shift_expression1right))::_::(_,(MlyValue.relational_expression 
relational_expression1,relational_expression1left,_))::rest671) => 
let val result=MlyValue.relational_expression(fn _ => let val 
relational_expression as relational_expression1=relational_expression1
 ()
val shift_expression as shift_expression1=shift_expression1 ()
 in (
ewrap(BinOp(Geq, relational_expression, shift_expression),
                       eleft relational_expression,
                       eright shift_expression)
) end
)
 in (LrTable.NT 80,(result,relational_expression1left,
shift_expression1right),rest671) end
| (245,(_,(MlyValue.additive_expression additive_expression1,
additive_expression1left,additive_expression1right))::rest671) => let 
val result=MlyValue.shift_expression(fn _ => let val 
additive_expression as additive_expression1=additive_expression1 ()
 in (additive_expression) end
)
 in (LrTable.NT 82,(result,additive_expression1left,
additive_expression1right),rest671) end
| (246,(_,(MlyValue.additive_expression additive_expression1,_,
additive_expression1right))::_::(_,(MlyValue.shift_expression 
shift_expression1,shift_expression1left,_))::rest671) => let val 
result=MlyValue.shift_expression(fn _ => let val shift_expression as 
shift_expression1=shift_expression1 ()
val additive_expression as additive_expression1=additive_expression1 
()
 in (
ewrap(BinOp(LShift, shift_expression, additive_expression),
                        eleft shift_expression,
                        eright additive_expression)
) end
)
 in (LrTable.NT 82,(result,shift_expression1left,
additive_expression1right),rest671) end
| (247,(_,(MlyValue.additive_expression additive_expression1,_,
additive_expression1right))::_::(_,(MlyValue.shift_expression 
shift_expression1,shift_expression1left,_))::rest671) => let val 
result=MlyValue.shift_expression(fn _ => let val shift_expression as 
shift_expression1=shift_expression1 ()
val additive_expression as additive_expression1=additive_expression1 
()
 in (
ewrap(BinOp(RShift, shift_expression, additive_expression),
                        eleft shift_expression,
                        eright additive_expression)
) end
)
 in (LrTable.NT 82,(result,shift_expression1left,
additive_expression1right),rest671) end
| (248,(_,(MlyValue.multiplicative_expression 
multiplicative_expression1,multiplicative_expression1left,
multiplicative_expression1right))::rest671) => let val result=
MlyValue.additive_expression(fn _ => let val multiplicative_expression
 as multiplicative_expression1=multiplicative_expression1 ()
 in (multiplicative_expression) end
)
 in (LrTable.NT 81,(result,multiplicative_expression1left,
multiplicative_expression1right),rest671) end
| (249,(_,(MlyValue.multiplicative_expression 
multiplicative_expression1,_,multiplicative_expression1right))::_::(_,
(MlyValue.additive_expression additive_expression1,
additive_expression1left,_))::rest671) => let val result=
MlyValue.additive_expression(fn _ => let val additive_expression as 
additive_expression1=additive_expression1 ()
val multiplicative_expression as multiplicative_expression1=
multiplicative_expression1 ()
 in (
ewrap(BinOp(Plus, additive_expression, multiplicative_expression),
                     eleft additive_expression,
                     eright multiplicative_expression)
) end
)
 in (LrTable.NT 81,(result,additive_expression1left,
multiplicative_expression1right),rest671) end
| (250,(_,(MlyValue.multiplicative_expression 
multiplicative_expression1,_,multiplicative_expression1right))::_::(_,
(MlyValue.additive_expression additive_expression1,
additive_expression1left,_))::rest671) => let val result=
MlyValue.additive_expression(fn _ => let val additive_expression as 
additive_expression1=additive_expression1 ()
val multiplicative_expression as multiplicative_expression1=
multiplicative_expression1 ()
 in (
ewrap(BinOp(Minus, additive_expression, multiplicative_expression),
                     eleft additive_expression,
                     eright multiplicative_expression)
) end
)
 in (LrTable.NT 81,(result,additive_expression1left,
multiplicative_expression1right),rest671) end
| (251,(_,(MlyValue.cast_expression cast_expression1,
cast_expression1left,cast_expression1right))::rest671) => let val 
result=MlyValue.multiplicative_expression(fn _ => let val 
cast_expression as cast_expression1=cast_expression1 ()
 in (cast_expression) end
)
 in (LrTable.NT 83,(result,cast_expression1left,cast_expression1right)
,rest671) end
| (252,(_,(MlyValue.cast_expression cast_expression1,_,
cast_expression1right))::_::(_,(MlyValue.multiplicative_expression 
multiplicative_expression1,multiplicative_expression1left,_))::rest671
) => let val result=MlyValue.multiplicative_expression(fn _ => let 
val multiplicative_expression as multiplicative_expression1=
multiplicative_expression1 ()
val cast_expression as cast_expression1=cast_expression1 ()
 in (
ewrap(BinOp(Times, multiplicative_expression, cast_expression),
                eleft multiplicative_expression,
                eright cast_expression)
) end
)
 in (LrTable.NT 83,(result,multiplicative_expression1left,
cast_expression1right),rest671) end
| (253,(_,(MlyValue.cast_expression cast_expression1,_,
cast_expression1right))::_::(_,(MlyValue.multiplicative_expression 
multiplicative_expression1,multiplicative_expression1left,_))::rest671
) => let val result=MlyValue.multiplicative_expression(fn _ => let 
val multiplicative_expression as multiplicative_expression1=
multiplicative_expression1 ()
val cast_expression as cast_expression1=cast_expression1 ()
 in (
ewrap(BinOp(Divides, multiplicative_expression, cast_expression),
                eleft multiplicative_expression,
                eright cast_expression)
) end
)
 in (LrTable.NT 83,(result,multiplicative_expression1left,
cast_expression1right),rest671) end
| (254,(_,(MlyValue.cast_expression cast_expression1,_,
cast_expression1right))::_::(_,(MlyValue.multiplicative_expression 
multiplicative_expression1,multiplicative_expression1left,_))::rest671
) => let val result=MlyValue.multiplicative_expression(fn _ => let 
val multiplicative_expression as multiplicative_expression1=
multiplicative_expression1 ()
val cast_expression as cast_expression1=cast_expression1 ()
 in (
ewrap(BinOp(Modulus, multiplicative_expression, cast_expression),
                eleft multiplicative_expression,
                eright cast_expression)
) end
)
 in (LrTable.NT 83,(result,multiplicative_expression1left,
cast_expression1right),rest671) end
| (255,(_,(MlyValue.unary_expression unary_expression1,
unary_expression1left,unary_expression1right))::rest671) => let val 
result=MlyValue.cast_expression(fn _ => let val unary_expression as 
unary_expression1=unary_expression1 ()
 in (unary_expression) end
)
 in (LrTable.NT 85,(result,unary_expression1left,
unary_expression1right),rest671) end
| (256,(_,(MlyValue.cast_expression cast_expression1,_,
cast_expression1right))::_::(_,(MlyValue.type_name type_name1,_,_))::(
_,(_,LPARENleft as LPAREN1left,_))::rest671) => let val result=
MlyValue.cast_expression(fn _ => let val type_name as type_name1=
type_name1 ()
val cast_expression as cast_expression1=cast_expression1 ()
 in (
ewrap(TypeCast(type_name, cast_expression), LPARENleft,
              eright cast_expression)
) end
)
 in (LrTable.NT 85,(result,LPAREN1left,cast_expression1right),rest671)
 end
| (257,(_,(MlyValue.postfix_expression postfix_expression1,
postfix_expression1left,postfix_expression1right))::rest671) => let 
val result=MlyValue.unary_expression(fn _ => let val 
postfix_expression as postfix_expression1=postfix_expression1 ()
 in (postfix_expression) end
)
 in (LrTable.NT 84,(result,postfix_expression1left,
postfix_expression1right),rest671) end
| (258,(_,(MlyValue.cast_expression cast_expression1,_,
cast_expression1right))::(_,(_,YMINUSleft as YMINUS1left,_))::rest671)
 => let val result=MlyValue.unary_expression(fn _ => let val 
cast_expression as cast_expression1=cast_expression1 ()
 in (
ewrap(UnOp(Negate, cast_expression), YMINUSleft,
                       eright cast_expression)
) end
)
 in (LrTable.NT 84,(result,YMINUS1left,cast_expression1right),rest671)
 end
| (259,(_,(MlyValue.cast_expression cast_expression1,_,
cast_expression1right))::(_,(_,YNOTleft as YNOT1left,_))::rest671) => 
let val result=MlyValue.unary_expression(fn _ => let val 
cast_expression as cast_expression1=cast_expression1 ()
 in (
ewrap(UnOp(Not, cast_expression),
                       YNOTleft, eright cast_expression)
) end
)
 in (LrTable.NT 84,(result,YNOT1left,cast_expression1right),rest671)
 end
| (260,(_,(MlyValue.cast_expression cast_expression1,_,
cast_expression1right))::(_,(_,YBITNOTleft as YBITNOT1left,_))::
rest671) => let val result=MlyValue.unary_expression(fn _ => let val 
cast_expression as cast_expression1=cast_expression1 ()
 in (
ewrap(UnOp(BitNegate, cast_expression),
                       YBITNOTleft, eright cast_expression)
) end
)
 in (LrTable.NT 84,(result,YBITNOT1left,cast_expression1right),rest671
) end
| (261,(_,(MlyValue.cast_expression cast_expression1,_,
cast_expression1right))::(_,(_,YAMPERSANDleft as YAMPERSAND1left,_))::
rest671) => let val result=MlyValue.unary_expression(fn _ => let val 
cast_expression as cast_expression1=cast_expression1 ()
 in (
ewrap(UnOp(Addr, cast_expression),
                       YAMPERSANDleft, eright cast_expression)
) end
)
 in (LrTable.NT 84,(result,YAMPERSAND1left,cast_expression1right),
rest671) end
| (262,(_,(MlyValue.cast_expression cast_expression1,_,
cast_expression1right))::(_,(_,YSTARleft as YSTAR1left,_))::rest671)
 => let val result=MlyValue.unary_expression(fn _ => let val 
cast_expression as cast_expression1=cast_expression1 ()
 in (
ewrap(Deref cast_expression, YSTARleft,
                       eright cast_expression)
) end
)
 in (LrTable.NT 84,(result,YSTAR1left,cast_expression1right),rest671)
 end
| (263,(_,(MlyValue.unary_expression unary_expression1,_,
unary_expression1right))::(_,(_,YSIZEOFleft as YSIZEOF1left,_))::
rest671) => let val result=MlyValue.unary_expression(fn _ => let val 
unary_expression as unary_expression1=unary_expression1 ()
 in (
ewrap(Sizeof unary_expression, YSIZEOFleft,
                       eright unary_expression)
) end
)
 in (LrTable.NT 84,(result,YSIZEOF1left,unary_expression1right),
rest671) end
| (264,(_,(_,_,RPARENright as RPAREN1right))::(_,(MlyValue.type_name 
type_name1,_,_))::_::(_,(_,YSIZEOFleft as YSIZEOF1left,_))::rest671)
 => let val result=MlyValue.unary_expression(fn _ => let val type_name
 as type_name1=type_name1 ()
 in (ewrap(SizeofTy type_name, YSIZEOFleft, RPARENright)) end
)
 in (LrTable.NT 84,(result,YSIZEOF1left,RPAREN1right),rest671) end
| (265,(_,(MlyValue.primary_expression primary_expression1,
primary_expression1left,primary_expression1right))::rest671) => let 
val result=MlyValue.postfix_expression(fn _ => let val 
primary_expression as primary_expression1=primary_expression1 ()
 in (primary_expression) end
)
 in (LrTable.NT 86,(result,primary_expression1left,
primary_expression1right),rest671) end
| (266,(_,(_,_,RBRACKETright as RBRACKET1right))::(_,(
MlyValue.rexpression rexpression1,_,_))::_::(_,(
MlyValue.postfix_expression postfix_expression1,
postfix_expression1left,_))::rest671) => let val result=
MlyValue.postfix_expression(fn _ => let val postfix_expression as 
postfix_expression1=postfix_expression1 ()
val rexpression as rexpression1=rexpression1 ()
 in (
ewrap(ArrayDeref(postfix_expression, rexpression),
               eleft postfix_expression,
               RBRACKETright)
) end
)
 in (LrTable.NT 86,(result,postfix_expression1left,RBRACKET1right),
rest671) end
| (267,(_,(_,_,RPARENright as RPAREN1right))::(_,(
MlyValue.opt_rexpr_list opt_rexpr_list1,_,_))::_::(_,(
MlyValue.postfix_expression postfix_expression1,
postfix_expression1left,_))::rest671) => let val result=
MlyValue.postfix_expression(fn _ => let val postfix_expression as 
postfix_expression1=postfix_expression1 ()
val opt_rexpr_list as opt_rexpr_list1=opt_rexpr_list1 ()
 in (
let
           val e = ewrap(EFnCall(postfix_expression, node opt_rexpr_list),
                         eleft postfix_expression,
                         RPARENright)
         in
           handle_builtin_fns e
         end
) end
)
 in (LrTable.NT 86,(result,postfix_expression1left,RPAREN1right),
rest671) end
| (268,(_,(MlyValue.ID ID1,_,IDright as ID1right))::_::(_,(
MlyValue.postfix_expression postfix_expression1,
postfix_expression1left,_))::rest671) => let val result=
MlyValue.postfix_expression(fn _ => let val postfix_expression as 
postfix_expression1=postfix_expression1 ()
val ID as ID1=ID1 ()
 in (
ewrap(StructDot(postfix_expression, C_field_name ID),
               eleft postfix_expression,
               IDright)
) end
)
 in (LrTable.NT 86,(result,postfix_expression1left,ID1right),rest671)
 end
| (269,(_,(MlyValue.ID ID1,_,IDright as ID1right))::_::(_,(
MlyValue.postfix_expression postfix_expression1,
postfix_expression1left,_))::rest671) => let val result=
MlyValue.postfix_expression(fn _ => let val postfix_expression as 
postfix_expression1=postfix_expression1 ()
val ID as ID1=ID1 ()
 in (
ewrap(StructDot(ewrap(Deref postfix_expression,
                               eleft postfix_expression,
                               eright postfix_expression),
                         C_field_name ID),
               eleft postfix_expression,
               IDright)
) end
)
 in (LrTable.NT 86,(result,postfix_expression1left,ID1right),rest671)
 end
| (270,(_,(_,_,RCURLYright as RCURLY1right))::(_,(
MlyValue.initializer_list initializer_list1,_,_))::_::_::(_,(
MlyValue.type_name type_name1,_,_))::(_,(_,LPARENleft as LPAREN1left,_
))::rest671) => let val result=MlyValue.postfix_expression(fn _ => 
let val type_name as type_name1=type_name1 ()
val initializer_list as initializer_list1=initializer_list1 ()
 in (
ewrap(CompLiteral(node type_name, initializer_list),
                LPARENleft, RCURLYright)
) end
)
 in (LrTable.NT 86,(result,LPAREN1left,RCURLY1right),rest671) end
| (271,(_,(MlyValue.ID ID1,IDleft as ID1left,IDright as ID1right))::
rest671) => let val result=MlyValue.primary_expression(fn _ => let 
val ID as ID1=ID1 ()
 in (ewrap(Var (ID, ref NONE), IDleft, IDright)) end
)
 in (LrTable.NT 87,(result,ID1left,ID1right),rest671) end
| (272,(_,(MlyValue.constant constant1,constant1left,constant1right))
::rest671) => let val result=MlyValue.primary_expression(fn _ => let 
val constant as constant1=constant1 ()
 in (ewrap(Constant constant, left constant, right constant)) end
)
 in (LrTable.NT 87,(result,constant1left,constant1right),rest671) end
| (273,(_,(_,_,RPARENright as RPAREN1right))::(_,(MlyValue.rexpression
 rexpression1,_,_))::(_,(_,LPARENleft as LPAREN1left,_))::rest671) => 
let val result=MlyValue.primary_expression(fn _ => let val rexpression
 as rexpression1=rexpression1 ()
 in (ewrap(enode rexpression, LPARENleft, RPARENright)) end
)
 in (LrTable.NT 87,(result,LPAREN1left,RPAREN1right),rest671) end
| (274,(_,(MlyValue.cstring_literal cstring_literal1,
cstring_literal1left,cstring_literal1right))::rest671) => let val 
result=MlyValue.primary_expression(fn _ => let val cstring_literal as 
cstring_literal1=cstring_literal1 ()
 in (
let val l = left cstring_literal  and r = right cstring_literal
        in
          ewrap(Constant (wrap (STRING_LIT (node cstring_literal), l, r)), l, r)
        end
) end
)
 in (LrTable.NT 87,(result,cstring_literal1left,cstring_literal1right)
,rest671) end
| (275,(_,(MlyValue.STRING_LITERAL STRING_LITERAL1,_,
STRING_LITERALright as STRING_LITERAL1right))::(_,(
MlyValue.cstring_literal cstring_literal1,cstring_literal1left,_))::
rest671) => let val result=MlyValue.cstring_literal(fn _ => let val 
cstring_literal as cstring_literal1=cstring_literal1 ()
val STRING_LITERAL as STRING_LITERAL1=STRING_LITERAL1 ()
 in (
wrap(node cstring_literal ^ STRING_LITERAL, left cstring_literal,
             STRING_LITERALright)
) end
)
 in (LrTable.NT 98,(result,cstring_literal1left,STRING_LITERAL1right),
rest671) end
| (276,(_,(MlyValue.STRING_LITERAL STRING_LITERAL1,STRING_LITERALleft
 as STRING_LITERAL1left,STRING_LITERALright as STRING_LITERAL1right))
::rest671) => let val result=MlyValue.cstring_literal(fn _ => let val 
STRING_LITERAL as STRING_LITERAL1=STRING_LITERAL1 ()
 in (wrap(STRING_LITERAL, STRING_LITERALleft, STRING_LITERALright))
 end
)
 in (LrTable.NT 98,(result,STRING_LITERAL1left,STRING_LITERAL1right),
rest671) end
| (277,(_,(MlyValue.NUMERIC_CONSTANT NUMERIC_CONSTANT1,
NUMERIC_CONSTANTleft as NUMERIC_CONSTANT1left,NUMERIC_CONSTANTright
 as NUMERIC_CONSTANT1right))::rest671) => let val result=
MlyValue.constant(fn _ => let val NUMERIC_CONSTANT as 
NUMERIC_CONSTANT1=NUMERIC_CONSTANT1 ()
 in (
wrap(NUMCONST NUMERIC_CONSTANT,
                                  NUMERIC_CONSTANTleft,
                                  NUMERIC_CONSTANTright)
) end
)
 in (LrTable.NT 88,(result,NUMERIC_CONSTANT1left,
NUMERIC_CONSTANT1right),rest671) end
| (278,(_,(MlyValue.postfix_expression postfix_expression1,
postfix_expression1left,postfix_expression1right))::rest671) => let 
val result=MlyValue.lexpression(fn _ => let val postfix_expression as 
postfix_expression1=postfix_expression1 ()
 in (postfix_expression) end
)
 in (LrTable.NT 70,(result,postfix_expression1left,
postfix_expression1right),rest671) end
| (279,(_,(MlyValue.cast_expression cast_expression1,_,
cast_expression1right))::(_,(_,YSTARleft as YSTAR1left,_))::rest671)
 => let val result=MlyValue.lexpression(fn _ => let val 
cast_expression as cast_expression1=cast_expression1 ()
 in (
ewrap(Deref cast_expression, YSTARleft,
                                      eright cast_expression)
) end
)
 in (LrTable.NT 70,(result,YSTAR1left,cast_expression1right),rest671)
 end
| _ => raise (mlyAction i392)
end
val void = MlyValue.VOID'
val extract = fn a => (fn MlyValue.begin x => x
| _ => let exception ParseInternal
	in raise ParseInternal end) a ()
end
end
structure Tokens : StrictC_TOKENS =
struct
type svalue = ParserData.svalue
type ('a,'b) token = ('a,'b) Token.token
fun EOF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 0,(
ParserData.MlyValue.VOID',p1,p2))
fun YSTAR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 1,(
ParserData.MlyValue.VOID',p1,p2))
fun SLASH (p1,p2) = Token.TOKEN (ParserData.LrTable.T 2,(
ParserData.MlyValue.VOID',p1,p2))
fun MOD (p1,p2) = Token.TOKEN (ParserData.LrTable.T 3,(
ParserData.MlyValue.VOID',p1,p2))
fun LPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 4,(
ParserData.MlyValue.VOID',p1,p2))
fun RPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 5,(
ParserData.MlyValue.VOID',p1,p2))
fun LCURLY (p1,p2) = Token.TOKEN (ParserData.LrTable.T 6,(
ParserData.MlyValue.VOID',p1,p2))
fun RCURLY (p1,p2) = Token.TOKEN (ParserData.LrTable.T 7,(
ParserData.MlyValue.VOID',p1,p2))
fun LBRACKET (p1,p2) = Token.TOKEN (ParserData.LrTable.T 8,(
ParserData.MlyValue.VOID',p1,p2))
fun RBRACKET (p1,p2) = Token.TOKEN (ParserData.LrTable.T 9,(
ParserData.MlyValue.VOID',p1,p2))
fun YCOMMA (p1,p2) = Token.TOKEN (ParserData.LrTable.T 10,(
ParserData.MlyValue.VOID',p1,p2))
fun YSEMI (p1,p2) = Token.TOKEN (ParserData.LrTable.T 11,(
ParserData.MlyValue.VOID',p1,p2))
fun YCOLON (p1,p2) = Token.TOKEN (ParserData.LrTable.T 12,(
ParserData.MlyValue.VOID',p1,p2))
fun QMARK (p1,p2) = Token.TOKEN (ParserData.LrTable.T 13,(
ParserData.MlyValue.VOID',p1,p2))
fun YEQ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 14,(
ParserData.MlyValue.VOID',p1,p2))
fun YDOT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 15,(
ParserData.MlyValue.VOID',p1,p2))
fun YPLUS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 16,(
ParserData.MlyValue.VOID',p1,p2))
fun YMINUS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 17,(
ParserData.MlyValue.VOID',p1,p2))
fun YAND (p1,p2) = Token.TOKEN (ParserData.LrTable.T 18,(
ParserData.MlyValue.VOID',p1,p2))
fun YNOT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 19,(
ParserData.MlyValue.VOID',p1,p2))
fun YAMPERSAND (p1,p2) = Token.TOKEN (ParserData.LrTable.T 20,(
ParserData.MlyValue.VOID',p1,p2))
fun YBITNOT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 21,(
ParserData.MlyValue.VOID',p1,p2))
fun PLUSPLUS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 22,(
ParserData.MlyValue.VOID',p1,p2))
fun MINUSMINUS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 23,(
ParserData.MlyValue.VOID',p1,p2))
fun PLUSEQ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 24,(
ParserData.MlyValue.VOID',p1,p2))
fun MINUSEQ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 25,(
ParserData.MlyValue.VOID',p1,p2))
fun BANDEQ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 26,(
ParserData.MlyValue.VOID',p1,p2))
fun BOREQ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 27,(
ParserData.MlyValue.VOID',p1,p2))
fun MULEQ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 28,(
ParserData.MlyValue.VOID',p1,p2))
fun DIVEQ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 29,(
ParserData.MlyValue.VOID',p1,p2))
fun MODEQ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 30,(
ParserData.MlyValue.VOID',p1,p2))
fun BXOREQ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 31,(
ParserData.MlyValue.VOID',p1,p2))
fun LSHIFTEQ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 32,(
ParserData.MlyValue.VOID',p1,p2))
fun RSHIFTEQ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 33,(
ParserData.MlyValue.VOID',p1,p2))
fun YENUM (p1,p2) = Token.TOKEN (ParserData.LrTable.T 34,(
ParserData.MlyValue.VOID',p1,p2))
fun YIF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 35,(
ParserData.MlyValue.VOID',p1,p2))
fun YELSE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 36,(
ParserData.MlyValue.VOID',p1,p2))
fun YWHILE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 37,(
ParserData.MlyValue.VOID',p1,p2))
fun YDO (p1,p2) = Token.TOKEN (ParserData.LrTable.T 38,(
ParserData.MlyValue.VOID',p1,p2))
fun YRETURN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 39,(
ParserData.MlyValue.VOID',p1,p2))
fun YBREAK (p1,p2) = Token.TOKEN (ParserData.LrTable.T 40,(
ParserData.MlyValue.VOID',p1,p2))
fun YCONTINUE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 41,(
ParserData.MlyValue.VOID',p1,p2))
fun YFOR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 42,(
ParserData.MlyValue.VOID',p1,p2))
fun SWITCH (p1,p2) = Token.TOKEN (ParserData.LrTable.T 43,(
ParserData.MlyValue.VOID',p1,p2))
fun CASE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 44,(
ParserData.MlyValue.VOID',p1,p2))
fun DEFAULT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 45,(
ParserData.MlyValue.VOID',p1,p2))
fun YSIZEOF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 46,(
ParserData.MlyValue.VOID',p1,p2))
fun LOGICALOR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 47,(
ParserData.MlyValue.VOID',p1,p2))
fun LOGICALAND (p1,p2) = Token.TOKEN (ParserData.LrTable.T 48,(
ParserData.MlyValue.VOID',p1,p2))
fun BITWISEOR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 49,(
ParserData.MlyValue.VOID',p1,p2))
fun BITWISEXOR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 50,(
ParserData.MlyValue.VOID',p1,p2))
fun EQUALS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 51,(
ParserData.MlyValue.VOID',p1,p2))
fun NOTEQUALS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 52,(
ParserData.MlyValue.VOID',p1,p2))
fun YLE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 53,(
ParserData.MlyValue.VOID',p1,p2))
fun YGE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 54,(
ParserData.MlyValue.VOID',p1,p2))
fun YLESS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 55,(
ParserData.MlyValue.VOID',p1,p2))
fun YGREATER (p1,p2) = Token.TOKEN (ParserData.LrTable.T 56,(
ParserData.MlyValue.VOID',p1,p2))
fun LEFTSHIFT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 57,(
ParserData.MlyValue.VOID',p1,p2))
fun RIGHTSHIFT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 58,(
ParserData.MlyValue.VOID',p1,p2))
fun INT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 59,(
ParserData.MlyValue.VOID',p1,p2))
fun BOOL (p1,p2) = Token.TOKEN (ParserData.LrTable.T 60,(
ParserData.MlyValue.VOID',p1,p2))
fun CHAR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 61,(
ParserData.MlyValue.VOID',p1,p2))
fun LONG (p1,p2) = Token.TOKEN (ParserData.LrTable.T 62,(
ParserData.MlyValue.VOID',p1,p2))
fun SHORT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 63,(
ParserData.MlyValue.VOID',p1,p2))
fun SIGNED (p1,p2) = Token.TOKEN (ParserData.LrTable.T 64,(
ParserData.MlyValue.VOID',p1,p2))
fun UNSIGNED (p1,p2) = Token.TOKEN (ParserData.LrTable.T 65,(
ParserData.MlyValue.VOID',p1,p2))
fun VOID (p1,p2) = Token.TOKEN (ParserData.LrTable.T 66,(
ParserData.MlyValue.VOID',p1,p2))
fun ARROW (p1,p2) = Token.TOKEN (ParserData.LrTable.T 67,(
ParserData.MlyValue.VOID',p1,p2))
fun ID (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 68,(
ParserData.MlyValue.ID (fn () => i),p1,p2))
fun TYPEID (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 69,(
ParserData.MlyValue.TYPEID (fn () => i),p1,p2))
fun NUMERIC_CONSTANT (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 70
,(ParserData.MlyValue.NUMERIC_CONSTANT (fn () => i),p1,p2))
fun STRUCT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 71,(
ParserData.MlyValue.VOID',p1,p2))
fun UNION (p1,p2) = Token.TOKEN (ParserData.LrTable.T 72,(
ParserData.MlyValue.VOID',p1,p2))
fun TYPEDEF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 73,(
ParserData.MlyValue.VOID',p1,p2))
fun EXTERN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 74,(
ParserData.MlyValue.VOID',p1,p2))
fun CONST (p1,p2) = Token.TOKEN (ParserData.LrTable.T 75,(
ParserData.MlyValue.VOID',p1,p2))
fun VOLATILE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 76,(
ParserData.MlyValue.VOID',p1,p2))
fun RESTRICT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 77,(
ParserData.MlyValue.VOID',p1,p2))
fun INVARIANT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 78,(
ParserData.MlyValue.VOID',p1,p2))
fun INLINE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 79,(
ParserData.MlyValue.VOID',p1,p2))
fun STATIC (p1,p2) = Token.TOKEN (ParserData.LrTable.T 80,(
ParserData.MlyValue.VOID',p1,p2))
fun FNSPEC (p1,p2) = Token.TOKEN (ParserData.LrTable.T 81,(
ParserData.MlyValue.VOID',p1,p2))
fun RELSPEC (p1,p2) = Token.TOKEN (ParserData.LrTable.T 82,(
ParserData.MlyValue.VOID',p1,p2))
fun AUXUPD (p1,p2) = Token.TOKEN (ParserData.LrTable.T 83,(
ParserData.MlyValue.VOID',p1,p2))
fun GHOSTUPD (p1,p2) = Token.TOKEN (ParserData.LrTable.T 84,(
ParserData.MlyValue.VOID',p1,p2))
fun MODIFIES (p1,p2) = Token.TOKEN (ParserData.LrTable.T 85,(
ParserData.MlyValue.VOID',p1,p2))
fun CALLS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 86,(
ParserData.MlyValue.VOID',p1,p2))
fun OWNED_BY (p1,p2) = Token.TOKEN (ParserData.LrTable.T 87,(
ParserData.MlyValue.VOID',p1,p2))
fun SPEC_BEGIN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 88,(
ParserData.MlyValue.VOID',p1,p2))
fun SPEC_END (p1,p2) = Token.TOKEN (ParserData.LrTable.T 89,(
ParserData.MlyValue.VOID',p1,p2))
fun DONT_TRANSLATE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 90,(
ParserData.MlyValue.VOID',p1,p2))
fun STRING_LITERAL (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 91,(
ParserData.MlyValue.STRING_LITERAL (fn () => i),p1,p2))
fun SPEC_BLOCKEND (p1,p2) = Token.TOKEN (ParserData.LrTable.T 92,(
ParserData.MlyValue.VOID',p1,p2))
fun GCC_ATTRIBUTE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 93,(
ParserData.MlyValue.VOID',p1,p2))
fun YASM (p1,p2) = Token.TOKEN (ParserData.LrTable.T 94,(
ParserData.MlyValue.VOID',p1,p2))
fun YREGISTER (p1,p2) = Token.TOKEN (ParserData.LrTable.T 95,(
ParserData.MlyValue.VOID',p1,p2))
end
end
