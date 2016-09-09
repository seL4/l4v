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
(**
 ** Copyright 2014, NICTA
 **
 ** This software may be distributed and modified according to the terms of
 ** the BSD 2-Clause license. Note that NO WARRANTY is provided.
 ** See "LICENSE_BSD2.txt" for details.
 **
 ** @TAG(NICTA_BSD)
 **)

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
fun gen_struct_id () =
      (scount := !scount + 1;
       NameGeneration.internalAnonStructPfx^Int.toString (!scount))
end

datatype storage_class_specifier = TypeDef | Extern | Static | Auto | Register | Thread_Local
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

fun scs_to_SC scs =
  case scs of
      Extern => SOME SC_EXTERN
    | Static => SOME SC_STATIC
    | Thread_Local => SOME SC_THRD_LOCAL
    | Register => SOME SC_REGISTER
    | Auto => SOME SC_AUTO
    | TypeDef => NONE

val extract_storage_specs =
  List.mapPartial (fn Storage scs_w => scs_to_SC (node scs_w)
                    | _ => NONE)

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
  val storage_specs = extract_storage_specs (node dsl)

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
          wrap(VarDecl(finaltype, nm, storage_specs, iopt, attrs),
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
\\001\000\001\000\235\001\000\000\
\\001\000\001\000\236\001\012\000\045\000\035\000\044\000\060\000\043\000\
\\061\000\042\000\062\000\041\000\063\000\040\000\064\000\039\000\
\\065\000\038\000\066\000\037\000\067\000\036\000\070\000\035\000\
\\072\000\034\000\074\000\033\000\075\000\032\000\076\000\031\000\
\\077\000\030\000\078\000\029\000\080\000\028\000\081\000\027\000\
\\082\000\026\000\083\000\025\000\084\000\024\000\085\000\023\000\
\\086\000\022\000\089\000\021\000\091\000\020\000\094\000\019\000\
\\097\000\018\000\099\000\017\000\000\000\
\\001\000\001\000\237\001\000\000\
\\001\000\001\000\238\001\012\000\238\001\035\000\238\001\060\000\238\001\
\\061\000\238\001\062\000\238\001\063\000\238\001\064\000\238\001\
\\065\000\238\001\066\000\238\001\067\000\238\001\070\000\238\001\
\\072\000\238\001\074\000\238\001\075\000\238\001\076\000\238\001\
\\077\000\238\001\078\000\238\001\080\000\238\001\081\000\238\001\
\\082\000\238\001\083\000\238\001\084\000\238\001\085\000\238\001\
\\086\000\238\001\089\000\238\001\091\000\238\001\094\000\238\001\
\\097\000\238\001\099\000\238\001\000\000\
\\001\000\001\000\239\001\012\000\239\001\035\000\239\001\060\000\239\001\
\\061\000\239\001\062\000\239\001\063\000\239\001\064\000\239\001\
\\065\000\239\001\066\000\239\001\067\000\239\001\070\000\239\001\
\\072\000\239\001\074\000\239\001\075\000\239\001\076\000\239\001\
\\077\000\239\001\078\000\239\001\080\000\239\001\081\000\239\001\
\\082\000\239\001\083\000\239\001\084\000\239\001\085\000\239\001\
\\086\000\239\001\089\000\239\001\091\000\239\001\094\000\239\001\
\\097\000\239\001\099\000\239\001\000\000\
\\001\000\001\000\240\001\012\000\240\001\035\000\240\001\060\000\240\001\
\\061\000\240\001\062\000\240\001\063\000\240\001\064\000\240\001\
\\065\000\240\001\066\000\240\001\067\000\240\001\070\000\240\001\
\\072\000\240\001\074\000\240\001\075\000\240\001\076\000\240\001\
\\077\000\240\001\078\000\240\001\080\000\240\001\081\000\240\001\
\\082\000\240\001\083\000\240\001\084\000\240\001\085\000\240\001\
\\086\000\240\001\089\000\240\001\091\000\240\001\094\000\240\001\
\\097\000\240\001\099\000\240\001\000\000\
\\001\000\001\000\018\002\002\000\018\002\005\000\018\002\007\000\018\002\
\\008\000\018\002\012\000\018\002\018\000\018\002\020\000\018\002\
\\021\000\018\002\022\000\018\002\035\000\018\002\036\000\018\002\
\\038\000\018\002\039\000\018\002\040\000\018\002\041\000\018\002\
\\042\000\018\002\043\000\018\002\044\000\018\002\045\000\018\002\
\\046\000\018\002\047\000\018\002\060\000\018\002\061\000\018\002\
\\062\000\018\002\063\000\018\002\064\000\018\002\065\000\018\002\
\\066\000\018\002\067\000\018\002\069\000\018\002\070\000\018\002\
\\071\000\018\002\072\000\018\002\074\000\018\002\075\000\018\002\
\\076\000\018\002\077\000\018\002\078\000\018\002\080\000\018\002\
\\081\000\018\002\082\000\018\002\083\000\018\002\084\000\018\002\
\\085\000\018\002\086\000\018\002\087\000\018\002\088\000\018\002\
\\089\000\018\002\091\000\018\002\092\000\018\002\094\000\018\002\
\\095\000\018\002\097\000\018\002\098\000\018\002\099\000\018\002\000\000\
\\001\000\001\000\019\002\002\000\019\002\005\000\019\002\007\000\019\002\
\\008\000\019\002\012\000\019\002\018\000\019\002\020\000\019\002\
\\021\000\019\002\022\000\019\002\035\000\019\002\036\000\019\002\
\\038\000\019\002\039\000\019\002\040\000\019\002\041\000\019\002\
\\042\000\019\002\043\000\019\002\044\000\019\002\045\000\019\002\
\\046\000\019\002\047\000\019\002\060\000\019\002\061\000\019\002\
\\062\000\019\002\063\000\019\002\064\000\019\002\065\000\019\002\
\\066\000\019\002\067\000\019\002\069\000\019\002\070\000\019\002\
\\071\000\019\002\072\000\019\002\074\000\019\002\075\000\019\002\
\\076\000\019\002\077\000\019\002\078\000\019\002\080\000\019\002\
\\081\000\019\002\082\000\019\002\083\000\019\002\084\000\019\002\
\\085\000\019\002\086\000\019\002\087\000\019\002\088\000\019\002\
\\089\000\019\002\091\000\019\002\092\000\019\002\094\000\019\002\
\\095\000\019\002\097\000\019\002\098\000\019\002\099\000\019\002\000\000\
\\001\000\001\000\028\002\012\000\028\002\035\000\028\002\060\000\028\002\
\\061\000\028\002\062\000\028\002\063\000\028\002\064\000\028\002\
\\065\000\028\002\066\000\028\002\067\000\028\002\070\000\028\002\
\\072\000\028\002\074\000\028\002\075\000\028\002\076\000\028\002\
\\077\000\028\002\078\000\028\002\080\000\028\002\081\000\028\002\
\\082\000\028\002\083\000\028\002\084\000\028\002\085\000\028\002\
\\086\000\028\002\089\000\028\002\091\000\028\002\094\000\028\002\
\\097\000\028\002\099\000\028\002\000\000\
\\001\000\001\000\036\002\002\000\036\002\005\000\036\002\007\000\036\002\
\\008\000\036\002\012\000\036\002\018\000\036\002\020\000\036\002\
\\021\000\036\002\022\000\036\002\035\000\036\002\036\000\036\002\
\\037\000\036\002\038\000\036\002\039\000\036\002\040\000\036\002\
\\041\000\036\002\042\000\036\002\043\000\036\002\044\000\036\002\
\\045\000\036\002\046\000\036\002\047\000\036\002\060\000\036\002\
\\061\000\036\002\062\000\036\002\063\000\036\002\064\000\036\002\
\\065\000\036\002\066\000\036\002\067\000\036\002\069\000\036\002\
\\070\000\036\002\071\000\036\002\072\000\036\002\074\000\036\002\
\\075\000\036\002\076\000\036\002\077\000\036\002\078\000\036\002\
\\080\000\036\002\081\000\036\002\082\000\036\002\083\000\036\002\
\\084\000\036\002\085\000\036\002\086\000\036\002\087\000\036\002\
\\088\000\036\002\089\000\036\002\091\000\036\002\092\000\036\002\
\\093\000\036\002\094\000\036\002\095\000\036\002\097\000\036\002\
\\098\000\036\002\099\000\036\002\000\000\
\\001\000\002\000\241\001\005\000\241\001\006\000\241\001\009\000\241\001\
\\011\000\241\001\012\000\241\001\035\000\241\001\060\000\241\001\
\\061\000\241\001\062\000\241\001\063\000\241\001\064\000\241\001\
\\065\000\241\001\066\000\241\001\067\000\241\001\069\000\241\001\
\\070\000\241\001\072\000\241\001\074\000\241\001\075\000\241\001\
\\076\000\241\001\077\000\241\001\078\000\241\001\080\000\241\001\
\\081\000\241\001\082\000\241\001\083\000\241\001\084\000\241\001\
\\085\000\241\001\086\000\241\001\089\000\241\001\091\000\241\001\
\\094\000\241\001\097\000\241\001\099\000\241\001\000\000\
\\001\000\002\000\242\001\005\000\242\001\006\000\242\001\009\000\242\001\
\\011\000\242\001\012\000\242\001\035\000\242\001\060\000\242\001\
\\061\000\242\001\062\000\242\001\063\000\242\001\064\000\242\001\
\\065\000\242\001\066\000\242\001\067\000\242\001\069\000\242\001\
\\070\000\242\001\072\000\242\001\074\000\242\001\075\000\242\001\
\\076\000\242\001\077\000\242\001\078\000\242\001\080\000\242\001\
\\081\000\242\001\082\000\242\001\083\000\242\001\084\000\242\001\
\\085\000\242\001\086\000\242\001\089\000\242\001\091\000\242\001\
\\094\000\242\001\097\000\242\001\099\000\242\001\000\000\
\\001\000\002\000\243\001\005\000\243\001\006\000\243\001\009\000\243\001\
\\011\000\243\001\012\000\243\001\035\000\243\001\060\000\243\001\
\\061\000\243\001\062\000\243\001\063\000\243\001\064\000\243\001\
\\065\000\243\001\066\000\243\001\067\000\243\001\069\000\243\001\
\\070\000\243\001\072\000\243\001\074\000\243\001\075\000\243\001\
\\076\000\243\001\077\000\243\001\078\000\243\001\080\000\243\001\
\\081\000\243\001\082\000\243\001\083\000\243\001\084\000\243\001\
\\085\000\243\001\086\000\243\001\089\000\243\001\091\000\243\001\
\\094\000\243\001\097\000\243\001\099\000\243\001\000\000\
\\001\000\002\000\244\001\005\000\244\001\006\000\244\001\009\000\244\001\
\\011\000\244\001\012\000\244\001\035\000\244\001\060\000\244\001\
\\061\000\244\001\062\000\244\001\063\000\244\001\064\000\244\001\
\\065\000\244\001\066\000\244\001\067\000\244\001\069\000\244\001\
\\070\000\244\001\072\000\244\001\074\000\244\001\075\000\244\001\
\\076\000\244\001\077\000\244\001\078\000\244\001\080\000\244\001\
\\081\000\244\001\082\000\244\001\083\000\244\001\084\000\244\001\
\\085\000\244\001\086\000\244\001\089\000\244\001\091\000\244\001\
\\094\000\244\001\097\000\244\001\099\000\244\001\000\000\
\\001\000\002\000\245\001\005\000\245\001\006\000\245\001\009\000\245\001\
\\011\000\245\001\012\000\245\001\035\000\245\001\060\000\245\001\
\\061\000\245\001\062\000\245\001\063\000\245\001\064\000\245\001\
\\065\000\245\001\066\000\245\001\067\000\245\001\069\000\245\001\
\\070\000\245\001\072\000\245\001\074\000\245\001\075\000\245\001\
\\076\000\245\001\077\000\245\001\078\000\245\001\080\000\245\001\
\\081\000\245\001\082\000\245\001\083\000\245\001\084\000\245\001\
\\085\000\245\001\086\000\245\001\089\000\245\001\091\000\245\001\
\\094\000\245\001\097\000\245\001\099\000\245\001\000\000\
\\001\000\002\000\246\001\005\000\246\001\006\000\246\001\009\000\246\001\
\\011\000\246\001\012\000\246\001\035\000\246\001\060\000\246\001\
\\061\000\246\001\062\000\246\001\063\000\246\001\064\000\246\001\
\\065\000\246\001\066\000\246\001\067\000\246\001\069\000\246\001\
\\070\000\246\001\072\000\246\001\074\000\246\001\075\000\246\001\
\\076\000\246\001\077\000\246\001\078\000\246\001\080\000\246\001\
\\081\000\246\001\082\000\246\001\083\000\246\001\084\000\246\001\
\\085\000\246\001\086\000\246\001\089\000\246\001\091\000\246\001\
\\094\000\246\001\097\000\246\001\099\000\246\001\000\000\
\\001\000\002\000\247\001\005\000\247\001\006\000\247\001\009\000\247\001\
\\011\000\247\001\012\000\247\001\035\000\247\001\060\000\247\001\
\\061\000\247\001\062\000\247\001\063\000\247\001\064\000\247\001\
\\065\000\247\001\066\000\247\001\067\000\247\001\069\000\247\001\
\\070\000\247\001\072\000\247\001\074\000\247\001\075\000\247\001\
\\076\000\247\001\077\000\247\001\078\000\247\001\080\000\247\001\
\\081\000\247\001\082\000\247\001\083\000\247\001\084\000\247\001\
\\085\000\247\001\086\000\247\001\089\000\247\001\091\000\247\001\
\\094\000\247\001\097\000\247\001\099\000\247\001\000\000\
\\001\000\002\000\248\001\005\000\248\001\006\000\248\001\009\000\248\001\
\\011\000\248\001\012\000\248\001\035\000\248\001\060\000\248\001\
\\061\000\248\001\062\000\248\001\063\000\248\001\064\000\248\001\
\\065\000\248\001\066\000\248\001\067\000\248\001\069\000\248\001\
\\070\000\248\001\072\000\248\001\074\000\248\001\075\000\248\001\
\\076\000\248\001\077\000\248\001\078\000\248\001\080\000\248\001\
\\081\000\248\001\082\000\248\001\083\000\248\001\084\000\248\001\
\\085\000\248\001\086\000\248\001\089\000\248\001\091\000\248\001\
\\094\000\248\001\097\000\248\001\099\000\248\001\000\000\
\\001\000\002\000\249\001\005\000\249\001\006\000\249\001\009\000\249\001\
\\011\000\249\001\012\000\249\001\035\000\249\001\060\000\249\001\
\\061\000\249\001\062\000\249\001\063\000\249\001\064\000\249\001\
\\065\000\249\001\066\000\249\001\067\000\249\001\069\000\249\001\
\\070\000\249\001\072\000\249\001\074\000\249\001\075\000\249\001\
\\076\000\249\001\077\000\249\001\078\000\249\001\080\000\249\001\
\\081\000\249\001\082\000\249\001\083\000\249\001\084\000\249\001\
\\085\000\249\001\086\000\249\001\089\000\249\001\091\000\249\001\
\\094\000\249\001\097\000\249\001\099\000\249\001\000\000\
\\001\000\002\000\250\001\005\000\250\001\006\000\250\001\009\000\250\001\
\\011\000\250\001\012\000\250\001\035\000\250\001\060\000\250\001\
\\061\000\250\001\062\000\250\001\063\000\250\001\064\000\250\001\
\\065\000\250\001\066\000\250\001\067\000\250\001\069\000\250\001\
\\070\000\250\001\072\000\250\001\074\000\250\001\075\000\250\001\
\\076\000\250\001\077\000\250\001\078\000\250\001\080\000\250\001\
\\081\000\250\001\082\000\250\001\083\000\250\001\084\000\250\001\
\\085\000\250\001\086\000\250\001\089\000\250\001\091\000\250\001\
\\094\000\250\001\097\000\250\001\099\000\250\001\000\000\
\\001\000\002\000\251\001\005\000\251\001\006\000\251\001\007\000\251\001\
\\009\000\251\001\011\000\251\001\012\000\251\001\013\000\251\001\
\\015\000\251\001\035\000\251\001\060\000\251\001\061\000\251\001\
\\062\000\251\001\063\000\251\001\064\000\251\001\065\000\251\001\
\\066\000\251\001\067\000\251\001\069\000\251\001\070\000\251\001\
\\072\000\251\001\074\000\251\001\075\000\251\001\076\000\251\001\
\\077\000\251\001\078\000\251\001\080\000\251\001\081\000\251\001\
\\082\000\251\001\083\000\251\001\084\000\251\001\085\000\251\001\
\\086\000\251\001\089\000\251\001\091\000\251\001\094\000\251\001\
\\097\000\251\001\098\000\251\001\099\000\251\001\000\000\
\\001\000\002\000\252\001\005\000\252\001\006\000\252\001\007\000\252\001\
\\009\000\252\001\011\000\252\001\012\000\252\001\013\000\252\001\
\\015\000\252\001\035\000\252\001\060\000\252\001\061\000\252\001\
\\062\000\252\001\063\000\252\001\064\000\252\001\065\000\252\001\
\\066\000\252\001\067\000\252\001\069\000\252\001\070\000\252\001\
\\072\000\252\001\074\000\252\001\075\000\252\001\076\000\252\001\
\\077\000\252\001\078\000\252\001\080\000\252\001\081\000\252\001\
\\082\000\252\001\083\000\252\001\084\000\252\001\085\000\252\001\
\\086\000\252\001\089\000\252\001\091\000\252\001\094\000\252\001\
\\097\000\252\001\098\000\252\001\099\000\252\001\000\000\
\\001\000\002\000\020\002\005\000\020\002\006\000\020\002\009\000\020\002\
\\011\000\020\002\012\000\020\002\035\000\044\000\060\000\043\000\
\\061\000\042\000\062\000\041\000\063\000\040\000\064\000\039\000\
\\065\000\038\000\066\000\037\000\067\000\036\000\069\000\020\002\
\\070\000\035\000\072\000\034\000\074\000\033\000\075\000\032\000\
\\076\000\031\000\077\000\030\000\078\000\029\000\080\000\028\000\
\\081\000\027\000\082\000\026\000\083\000\025\000\084\000\024\000\
\\085\000\023\000\086\000\022\000\089\000\021\000\091\000\020\000\
\\094\000\019\000\097\000\018\000\099\000\017\000\000\000\
\\001\000\002\000\021\002\005\000\021\002\006\000\021\002\009\000\021\002\
\\011\000\021\002\012\000\021\002\069\000\021\002\000\000\
\\001\000\002\000\022\002\005\000\022\002\006\000\022\002\009\000\022\002\
\\011\000\022\002\012\000\022\002\035\000\044\000\060\000\043\000\
\\061\000\042\000\062\000\041\000\063\000\040\000\064\000\039\000\
\\065\000\038\000\066\000\037\000\067\000\036\000\069\000\022\002\
\\070\000\035\000\072\000\034\000\074\000\033\000\075\000\032\000\
\\076\000\031\000\077\000\030\000\078\000\029\000\080\000\028\000\
\\081\000\027\000\082\000\026\000\083\000\025\000\084\000\024\000\
\\085\000\023\000\086\000\022\000\089\000\021\000\091\000\020\000\
\\094\000\019\000\097\000\018\000\099\000\017\000\000\000\
\\001\000\002\000\023\002\005\000\023\002\006\000\023\002\009\000\023\002\
\\011\000\023\002\012\000\023\002\069\000\023\002\000\000\
\\001\000\002\000\024\002\005\000\024\002\006\000\024\002\009\000\024\002\
\\011\000\024\002\012\000\024\002\035\000\044\000\060\000\043\000\
\\061\000\042\000\062\000\041\000\063\000\040\000\064\000\039\000\
\\065\000\038\000\066\000\037\000\067\000\036\000\069\000\024\002\
\\070\000\035\000\072\000\034\000\074\000\033\000\075\000\032\000\
\\076\000\031\000\077\000\030\000\078\000\029\000\080\000\028\000\
\\081\000\027\000\082\000\026\000\083\000\025\000\084\000\024\000\
\\085\000\023\000\086\000\022\000\089\000\021\000\091\000\020\000\
\\094\000\019\000\097\000\018\000\099\000\017\000\000\000\
\\001\000\002\000\025\002\005\000\025\002\006\000\025\002\009\000\025\002\
\\011\000\025\002\012\000\025\002\069\000\025\002\000\000\
\\001\000\002\000\026\002\005\000\026\002\006\000\026\002\009\000\026\002\
\\011\000\026\002\012\000\026\002\035\000\044\000\060\000\043\000\
\\061\000\042\000\062\000\041\000\063\000\040\000\064\000\039\000\
\\065\000\038\000\066\000\037\000\067\000\036\000\069\000\026\002\
\\070\000\035\000\072\000\034\000\074\000\033\000\075\000\032\000\
\\076\000\031\000\077\000\030\000\078\000\029\000\080\000\028\000\
\\081\000\027\000\082\000\026\000\083\000\025\000\084\000\024\000\
\\085\000\023\000\086\000\022\000\089\000\021\000\091\000\020\000\
\\094\000\019\000\097\000\018\000\099\000\017\000\000\000\
\\001\000\002\000\027\002\005\000\027\002\006\000\027\002\009\000\027\002\
\\011\000\027\002\012\000\027\002\069\000\027\002\000\000\
\\001\000\002\000\039\002\005\000\039\002\007\000\039\002\008\000\039\002\
\\012\000\039\002\018\000\039\002\020\000\039\002\021\000\039\002\
\\022\000\039\002\035\000\039\002\036\000\039\002\038\000\039\002\
\\039\000\039\002\040\000\039\002\041\000\039\002\042\000\039\002\
\\043\000\039\002\044\000\039\002\045\000\039\002\046\000\039\002\
\\047\000\039\002\060\000\039\002\061\000\039\002\062\000\039\002\
\\063\000\039\002\064\000\039\002\065\000\039\002\066\000\039\002\
\\067\000\039\002\069\000\039\002\070\000\039\002\071\000\039\002\
\\072\000\039\002\074\000\039\002\075\000\039\002\076\000\039\002\
\\077\000\039\002\078\000\039\002\080\000\039\002\081\000\039\002\
\\082\000\039\002\083\000\039\002\084\000\039\002\085\000\039\002\
\\086\000\039\002\087\000\039\002\088\000\039\002\089\000\039\002\
\\091\000\039\002\092\000\039\002\094\000\039\002\095\000\039\002\
\\097\000\039\002\098\000\039\002\099\000\039\002\000\000\
\\001\000\002\000\040\002\005\000\040\002\007\000\040\002\008\000\040\002\
\\012\000\040\002\018\000\040\002\020\000\040\002\021\000\040\002\
\\022\000\040\002\035\000\040\002\036\000\040\002\038\000\040\002\
\\039\000\040\002\040\000\040\002\041\000\040\002\042\000\040\002\
\\043\000\040\002\044\000\040\002\045\000\040\002\046\000\040\002\
\\047\000\040\002\060\000\040\002\061\000\040\002\062\000\040\002\
\\063\000\040\002\064\000\040\002\065\000\040\002\066\000\040\002\
\\067\000\040\002\069\000\040\002\070\000\040\002\071\000\040\002\
\\072\000\040\002\074\000\040\002\075\000\040\002\076\000\040\002\
\\077\000\040\002\078\000\040\002\080\000\040\002\081\000\040\002\
\\082\000\040\002\083\000\040\002\084\000\040\002\085\000\040\002\
\\086\000\040\002\087\000\040\002\088\000\040\002\089\000\040\002\
\\091\000\040\002\092\000\040\002\094\000\040\002\095\000\040\002\
\\097\000\040\002\098\000\040\002\099\000\040\002\000\000\
\\001\000\002\000\047\002\005\000\047\002\006\000\047\002\009\000\047\002\
\\035\000\044\000\060\000\043\000\061\000\042\000\062\000\041\000\
\\063\000\040\000\064\000\039\000\065\000\038\000\066\000\037\000\
\\067\000\036\000\069\000\047\002\070\000\035\000\072\000\034\000\
\\076\000\031\000\077\000\030\000\078\000\029\000\000\000\
\\001\000\002\000\048\002\005\000\048\002\006\000\048\002\009\000\048\002\
\\069\000\048\002\000\000\
\\001\000\002\000\049\002\005\000\049\002\006\000\049\002\009\000\049\002\
\\035\000\044\000\060\000\043\000\061\000\042\000\062\000\041\000\
\\063\000\040\000\064\000\039\000\065\000\038\000\066\000\037\000\
\\067\000\036\000\069\000\049\002\070\000\035\000\072\000\034\000\
\\076\000\031\000\077\000\030\000\078\000\029\000\000\000\
\\001\000\002\000\050\002\005\000\050\002\006\000\050\002\009\000\050\002\
\\069\000\050\002\000\000\
\\001\000\002\000\051\002\005\000\051\002\006\000\051\002\009\000\051\002\
\\011\000\051\002\012\000\051\002\035\000\051\002\060\000\051\002\
\\061\000\051\002\062\000\051\002\063\000\051\002\064\000\051\002\
\\065\000\051\002\066\000\051\002\067\000\051\002\069\000\051\002\
\\070\000\051\002\072\000\051\002\074\000\051\002\075\000\051\002\
\\076\000\051\002\077\000\051\002\078\000\051\002\080\000\051\002\
\\081\000\051\002\082\000\051\002\083\000\051\002\084\000\051\002\
\\085\000\051\002\086\000\051\002\089\000\051\002\091\000\051\002\
\\094\000\051\002\097\000\051\002\099\000\051\002\000\000\
\\001\000\002\000\052\002\005\000\052\002\006\000\052\002\009\000\052\002\
\\011\000\052\002\012\000\052\002\035\000\052\002\060\000\052\002\
\\061\000\052\002\062\000\052\002\063\000\052\002\064\000\052\002\
\\065\000\052\002\066\000\052\002\067\000\052\002\069\000\052\002\
\\070\000\052\002\072\000\052\002\074\000\052\002\075\000\052\002\
\\076\000\052\002\077\000\052\002\078\000\052\002\080\000\052\002\
\\081\000\052\002\082\000\052\002\083\000\052\002\084\000\052\002\
\\085\000\052\002\086\000\052\002\089\000\052\002\091\000\052\002\
\\094\000\052\002\097\000\052\002\099\000\052\002\000\000\
\\001\000\002\000\053\002\005\000\053\002\006\000\053\002\009\000\053\002\
\\011\000\053\002\012\000\053\002\035\000\053\002\060\000\053\002\
\\061\000\053\002\062\000\053\002\063\000\053\002\064\000\053\002\
\\065\000\053\002\066\000\053\002\067\000\053\002\069\000\053\002\
\\070\000\053\002\072\000\053\002\074\000\053\002\075\000\053\002\
\\076\000\053\002\077\000\053\002\078\000\053\002\080\000\053\002\
\\081\000\053\002\082\000\053\002\083\000\053\002\084\000\053\002\
\\085\000\053\002\086\000\053\002\089\000\053\002\091\000\053\002\
\\094\000\053\002\097\000\053\002\099\000\053\002\000\000\
\\001\000\002\000\054\002\005\000\054\002\006\000\054\002\009\000\054\002\
\\011\000\054\002\069\000\054\002\076\000\031\000\077\000\030\000\
\\078\000\029\000\091\000\054\002\097\000\054\002\000\000\
\\001\000\002\000\055\002\005\000\055\002\006\000\055\002\009\000\055\002\
\\011\000\055\002\069\000\055\002\091\000\055\002\097\000\055\002\000\000\
\\001\000\002\000\082\002\005\000\082\002\006\000\082\002\007\000\082\002\
\\009\000\082\002\011\000\082\002\012\000\082\002\035\000\082\002\
\\060\000\082\002\061\000\082\002\062\000\082\002\063\000\082\002\
\\064\000\082\002\065\000\082\002\066\000\082\002\067\000\082\002\
\\069\000\082\002\070\000\082\002\072\000\082\002\074\000\082\002\
\\075\000\082\002\076\000\082\002\077\000\082\002\078\000\082\002\
\\080\000\082\002\081\000\082\002\082\000\082\002\083\000\082\002\
\\084\000\082\002\085\000\082\002\086\000\082\002\089\000\082\002\
\\091\000\082\002\094\000\082\002\097\000\082\002\099\000\082\002\000\000\
\\001\000\002\000\083\002\005\000\083\002\006\000\083\002\007\000\083\002\
\\009\000\083\002\011\000\083\002\012\000\083\002\035\000\083\002\
\\060\000\083\002\061\000\083\002\062\000\083\002\063\000\083\002\
\\064\000\083\002\065\000\083\002\066\000\083\002\067\000\083\002\
\\069\000\083\002\070\000\083\002\072\000\083\002\074\000\083\002\
\\075\000\083\002\076\000\083\002\077\000\083\002\078\000\083\002\
\\080\000\083\002\081\000\083\002\082\000\083\002\083\000\083\002\
\\084\000\083\002\085\000\083\002\086\000\083\002\089\000\083\002\
\\091\000\083\002\094\000\083\002\097\000\083\002\099\000\083\002\000\000\
\\001\000\002\000\084\002\005\000\084\002\006\000\084\002\007\000\098\000\
\\009\000\084\002\011\000\084\002\012\000\084\002\035\000\084\002\
\\060\000\084\002\061\000\084\002\062\000\084\002\063\000\084\002\
\\064\000\084\002\065\000\084\002\066\000\084\002\067\000\084\002\
\\069\000\084\002\070\000\084\002\072\000\084\002\074\000\084\002\
\\075\000\084\002\076\000\084\002\077\000\084\002\078\000\084\002\
\\080\000\084\002\081\000\084\002\082\000\084\002\083\000\084\002\
\\084\000\084\002\085\000\084\002\086\000\084\002\089\000\084\002\
\\091\000\084\002\094\000\084\002\097\000\084\002\099\000\084\002\000\000\
\\001\000\002\000\085\002\005\000\085\002\006\000\085\002\009\000\085\002\
\\011\000\085\002\012\000\085\002\035\000\085\002\060\000\085\002\
\\061\000\085\002\062\000\085\002\063\000\085\002\064\000\085\002\
\\065\000\085\002\066\000\085\002\067\000\085\002\069\000\085\002\
\\070\000\085\002\072\000\085\002\074\000\085\002\075\000\085\002\
\\076\000\085\002\077\000\085\002\078\000\085\002\080\000\085\002\
\\081\000\085\002\082\000\085\002\083\000\085\002\084\000\085\002\
\\085\000\085\002\086\000\085\002\089\000\085\002\091\000\085\002\
\\094\000\085\002\097\000\085\002\099\000\085\002\000\000\
\\001\000\002\000\086\002\005\000\086\002\006\000\086\002\009\000\086\002\
\\011\000\086\002\012\000\086\002\035\000\086\002\060\000\086\002\
\\061\000\086\002\062\000\086\002\063\000\086\002\064\000\086\002\
\\065\000\086\002\066\000\086\002\067\000\086\002\069\000\086\002\
\\070\000\086\002\072\000\086\002\074\000\086\002\075\000\086\002\
\\076\000\086\002\077\000\086\002\078\000\086\002\080\000\086\002\
\\081\000\086\002\082\000\086\002\083\000\086\002\084\000\086\002\
\\085\000\086\002\086\000\086\002\089\000\086\002\091\000\086\002\
\\094\000\086\002\097\000\086\002\099\000\086\002\000\000\
\\001\000\002\000\087\002\005\000\087\002\006\000\087\002\009\000\087\002\
\\011\000\087\002\012\000\087\002\035\000\087\002\060\000\087\002\
\\061\000\087\002\062\000\087\002\063\000\087\002\064\000\087\002\
\\065\000\087\002\066\000\087\002\067\000\087\002\069\000\087\002\
\\070\000\087\002\072\000\087\002\074\000\087\002\075\000\087\002\
\\076\000\087\002\077\000\087\002\078\000\087\002\080\000\087\002\
\\081\000\087\002\082\000\087\002\083\000\087\002\084\000\087\002\
\\085\000\087\002\086\000\087\002\089\000\087\002\091\000\087\002\
\\094\000\087\002\097\000\087\002\099\000\087\002\000\000\
\\001\000\002\000\088\002\005\000\088\002\006\000\088\002\009\000\088\002\
\\011\000\088\002\012\000\088\002\035\000\088\002\060\000\088\002\
\\061\000\088\002\062\000\088\002\063\000\088\002\064\000\088\002\
\\065\000\088\002\066\000\088\002\067\000\088\002\069\000\088\002\
\\070\000\088\002\072\000\088\002\074\000\088\002\075\000\088\002\
\\076\000\088\002\077\000\088\002\078\000\088\002\080\000\088\002\
\\081\000\088\002\082\000\088\002\083\000\088\002\084\000\088\002\
\\085\000\088\002\086\000\088\002\089\000\088\002\091\000\088\002\
\\094\000\088\002\097\000\088\002\099\000\088\002\000\000\
\\001\000\002\000\089\002\005\000\089\002\006\000\089\002\009\000\089\002\
\\011\000\089\002\012\000\089\002\035\000\089\002\060\000\089\002\
\\061\000\089\002\062\000\089\002\063\000\089\002\064\000\089\002\
\\065\000\089\002\066\000\089\002\067\000\089\002\069\000\089\002\
\\070\000\089\002\072\000\089\002\074\000\089\002\075\000\089\002\
\\076\000\089\002\077\000\089\002\078\000\089\002\080\000\089\002\
\\081\000\089\002\082\000\089\002\083\000\089\002\084\000\089\002\
\\085\000\089\002\086\000\089\002\089\000\089\002\091\000\089\002\
\\094\000\089\002\097\000\089\002\099\000\089\002\000\000\
\\001\000\002\000\090\002\005\000\090\002\006\000\090\002\009\000\090\002\
\\011\000\090\002\012\000\090\002\035\000\090\002\060\000\090\002\
\\061\000\090\002\062\000\090\002\063\000\090\002\064\000\090\002\
\\065\000\090\002\066\000\090\002\067\000\090\002\069\000\090\002\
\\070\000\090\002\072\000\090\002\074\000\090\002\075\000\090\002\
\\076\000\090\002\077\000\090\002\078\000\090\002\080\000\090\002\
\\081\000\090\002\082\000\090\002\083\000\090\002\084\000\090\002\
\\085\000\090\002\086\000\090\002\089\000\090\002\091\000\090\002\
\\094\000\090\002\097\000\090\002\099\000\090\002\000\000\
\\001\000\002\000\091\002\005\000\091\002\006\000\091\002\009\000\091\002\
\\011\000\091\002\012\000\091\002\035\000\091\002\060\000\091\002\
\\061\000\091\002\062\000\091\002\063\000\091\002\064\000\091\002\
\\065\000\091\002\066\000\091\002\067\000\091\002\069\000\091\002\
\\070\000\091\002\072\000\091\002\074\000\091\002\075\000\091\002\
\\076\000\091\002\077\000\091\002\078\000\091\002\080\000\091\002\
\\081\000\091\002\082\000\091\002\083\000\091\002\084\000\091\002\
\\085\000\091\002\086\000\091\002\089\000\091\002\091\000\091\002\
\\094\000\091\002\097\000\091\002\099\000\091\002\000\000\
\\001\000\002\000\092\002\005\000\092\002\006\000\092\002\009\000\092\002\
\\011\000\092\002\012\000\092\002\035\000\092\002\060\000\092\002\
\\061\000\092\002\062\000\092\002\063\000\092\002\064\000\092\002\
\\065\000\092\002\066\000\092\002\067\000\092\002\069\000\092\002\
\\070\000\092\002\072\000\092\002\074\000\092\002\075\000\092\002\
\\076\000\092\002\077\000\092\002\078\000\092\002\080\000\092\002\
\\081\000\092\002\082\000\092\002\083\000\092\002\084\000\092\002\
\\085\000\092\002\086\000\092\002\089\000\092\002\091\000\092\002\
\\094\000\092\002\097\000\092\002\099\000\092\002\000\000\
\\001\000\002\000\093\002\005\000\093\002\006\000\093\002\009\000\093\002\
\\011\000\093\002\012\000\093\002\035\000\093\002\060\000\093\002\
\\061\000\093\002\062\000\093\002\063\000\093\002\064\000\093\002\
\\065\000\093\002\066\000\093\002\067\000\093\002\069\000\093\002\
\\070\000\093\002\072\000\093\002\074\000\093\002\075\000\093\002\
\\076\000\093\002\077\000\093\002\078\000\093\002\080\000\093\002\
\\081\000\093\002\082\000\093\002\083\000\093\002\084\000\093\002\
\\085\000\093\002\086\000\093\002\089\000\093\002\091\000\093\002\
\\094\000\093\002\097\000\093\002\099\000\093\002\000\000\
\\001\000\002\000\094\002\005\000\094\002\006\000\094\002\009\000\094\002\
\\011\000\094\002\012\000\094\002\035\000\094\002\060\000\094\002\
\\061\000\094\002\062\000\094\002\063\000\094\002\064\000\094\002\
\\065\000\094\002\066\000\094\002\067\000\094\002\069\000\094\002\
\\070\000\094\002\072\000\094\002\074\000\094\002\075\000\094\002\
\\076\000\094\002\077\000\094\002\078\000\094\002\080\000\094\002\
\\081\000\094\002\082\000\094\002\083\000\094\002\084\000\094\002\
\\085\000\094\002\086\000\094\002\089\000\094\002\091\000\094\002\
\\094\000\094\002\097\000\094\002\099\000\094\002\000\000\
\\001\000\002\000\095\002\005\000\095\002\006\000\095\002\009\000\095\002\
\\011\000\095\002\012\000\095\002\035\000\095\002\060\000\095\002\
\\061\000\095\002\062\000\095\002\063\000\095\002\064\000\095\002\
\\065\000\095\002\066\000\095\002\067\000\095\002\069\000\095\002\
\\070\000\095\002\072\000\095\002\074\000\095\002\075\000\095\002\
\\076\000\095\002\077\000\095\002\078\000\095\002\080\000\095\002\
\\081\000\095\002\082\000\095\002\083\000\095\002\084\000\095\002\
\\085\000\095\002\086\000\095\002\089\000\095\002\091\000\095\002\
\\094\000\095\002\097\000\095\002\099\000\095\002\000\000\
\\001\000\002\000\096\002\005\000\096\002\006\000\096\002\009\000\096\002\
\\011\000\096\002\012\000\096\002\035\000\096\002\060\000\096\002\
\\061\000\096\002\062\000\096\002\063\000\096\002\064\000\096\002\
\\065\000\096\002\066\000\096\002\067\000\096\002\069\000\096\002\
\\070\000\096\002\072\000\096\002\074\000\096\002\075\000\096\002\
\\076\000\096\002\077\000\096\002\078\000\096\002\080\000\096\002\
\\081\000\096\002\082\000\096\002\083\000\096\002\084\000\096\002\
\\085\000\096\002\086\000\096\002\089\000\096\002\091\000\096\002\
\\094\000\096\002\097\000\096\002\099\000\096\002\000\000\
\\001\000\002\000\097\002\005\000\097\002\006\000\097\002\009\000\097\002\
\\011\000\097\002\012\000\097\002\035\000\097\002\060\000\097\002\
\\061\000\097\002\062\000\097\002\063\000\097\002\064\000\097\002\
\\065\000\097\002\066\000\097\002\067\000\097\002\069\000\097\002\
\\070\000\097\002\072\000\097\002\074\000\097\002\075\000\097\002\
\\076\000\097\002\077\000\097\002\078\000\097\002\080\000\097\002\
\\081\000\097\002\082\000\097\002\083\000\097\002\084\000\097\002\
\\085\000\097\002\086\000\097\002\089\000\097\002\091\000\097\002\
\\094\000\097\002\097\000\097\002\099\000\097\002\000\000\
\\001\000\002\000\098\002\005\000\098\002\006\000\098\002\009\000\098\002\
\\011\000\098\002\012\000\098\002\035\000\098\002\060\000\098\002\
\\061\000\098\002\062\000\098\002\063\000\098\002\064\000\098\002\
\\065\000\098\002\066\000\098\002\067\000\098\002\069\000\098\002\
\\070\000\098\002\072\000\098\002\074\000\098\002\075\000\098\002\
\\076\000\098\002\077\000\098\002\078\000\098\002\080\000\098\002\
\\081\000\098\002\082\000\098\002\083\000\098\002\084\000\098\002\
\\085\000\098\002\086\000\098\002\089\000\098\002\091\000\098\002\
\\094\000\098\002\097\000\098\002\099\000\098\002\000\000\
\\001\000\002\000\099\002\005\000\099\002\006\000\099\002\009\000\099\002\
\\011\000\099\002\012\000\099\002\035\000\099\002\060\000\099\002\
\\061\000\099\002\062\000\099\002\063\000\099\002\064\000\099\002\
\\065\000\099\002\066\000\099\002\067\000\099\002\069\000\099\002\
\\070\000\099\002\072\000\099\002\074\000\099\002\075\000\099\002\
\\076\000\099\002\077\000\099\002\078\000\099\002\080\000\099\002\
\\081\000\099\002\082\000\099\002\083\000\099\002\084\000\099\002\
\\085\000\099\002\086\000\099\002\089\000\099\002\091\000\099\002\
\\094\000\099\002\097\000\099\002\099\000\099\002\000\000\
\\001\000\002\000\100\002\005\000\100\002\006\000\100\002\009\000\100\002\
\\011\000\100\002\012\000\100\002\035\000\100\002\060\000\100\002\
\\061\000\100\002\062\000\100\002\063\000\100\002\064\000\100\002\
\\065\000\100\002\066\000\100\002\067\000\100\002\069\000\100\002\
\\070\000\100\002\072\000\100\002\074\000\100\002\075\000\100\002\
\\076\000\100\002\077\000\100\002\078\000\100\002\080\000\100\002\
\\081\000\100\002\082\000\100\002\083\000\100\002\084\000\100\002\
\\085\000\100\002\086\000\100\002\089\000\100\002\091\000\100\002\
\\094\000\100\002\097\000\100\002\099\000\100\002\000\000\
\\001\000\002\000\101\002\005\000\101\002\006\000\101\002\009\000\101\002\
\\011\000\101\002\012\000\101\002\035\000\101\002\060\000\101\002\
\\061\000\101\002\062\000\101\002\063\000\101\002\064\000\101\002\
\\065\000\101\002\066\000\101\002\067\000\101\002\069\000\101\002\
\\070\000\101\002\072\000\101\002\074\000\101\002\075\000\101\002\
\\076\000\101\002\077\000\101\002\078\000\101\002\080\000\101\002\
\\081\000\101\002\082\000\101\002\083\000\101\002\084\000\101\002\
\\085\000\101\002\086\000\101\002\089\000\101\002\091\000\101\002\
\\094\000\101\002\097\000\101\002\099\000\101\002\000\000\
\\001\000\002\000\102\002\005\000\102\002\006\000\102\002\007\000\104\000\
\\009\000\102\002\011\000\102\002\012\000\102\002\035\000\102\002\
\\060\000\102\002\061\000\102\002\062\000\102\002\063\000\102\002\
\\064\000\102\002\065\000\102\002\066\000\102\002\067\000\102\002\
\\069\000\102\002\070\000\102\002\072\000\102\002\074\000\102\002\
\\075\000\102\002\076\000\102\002\077\000\102\002\078\000\102\002\
\\080\000\102\002\081\000\102\002\082\000\102\002\083\000\102\002\
\\084\000\102\002\085\000\102\002\086\000\102\002\089\000\102\002\
\\091\000\102\002\094\000\102\002\097\000\102\002\099\000\102\002\000\000\
\\001\000\002\000\123\002\005\000\123\002\007\000\123\002\018\000\123\002\
\\020\000\123\002\021\000\123\002\022\000\123\002\047\000\123\002\
\\069\000\123\002\071\000\123\002\095\000\123\002\000\000\
\\001\000\002\000\130\002\005\000\130\002\018\000\130\002\020\000\130\002\
\\021\000\130\002\022\000\130\002\047\000\130\002\069\000\130\002\
\\071\000\130\002\095\000\130\002\000\000\
\\001\000\002\000\131\002\005\000\131\002\018\000\131\002\020\000\131\002\
\\021\000\131\002\022\000\131\002\047\000\131\002\069\000\131\002\
\\071\000\131\002\095\000\131\002\000\000\
\\001\000\002\000\132\002\005\000\132\002\018\000\132\002\020\000\132\002\
\\021\000\132\002\022\000\132\002\047\000\132\002\069\000\132\002\
\\071\000\132\002\095\000\132\002\000\000\
\\001\000\002\000\133\002\005\000\133\002\018\000\133\002\020\000\133\002\
\\021\000\133\002\022\000\133\002\047\000\133\002\069\000\133\002\
\\071\000\133\002\095\000\133\002\000\000\
\\001\000\002\000\134\002\005\000\134\002\018\000\134\002\020\000\134\002\
\\021\000\134\002\022\000\134\002\047\000\134\002\069\000\134\002\
\\071\000\134\002\095\000\134\002\000\000\
\\001\000\002\000\135\002\005\000\135\002\018\000\135\002\020\000\135\002\
\\021\000\135\002\022\000\135\002\047\000\135\002\069\000\135\002\
\\071\000\135\002\095\000\135\002\000\000\
\\001\000\002\000\136\002\005\000\136\002\018\000\136\002\020\000\136\002\
\\021\000\136\002\022\000\136\002\047\000\136\002\069\000\136\002\
\\071\000\136\002\095\000\136\002\000\000\
\\001\000\002\000\137\002\005\000\137\002\018\000\137\002\020\000\137\002\
\\021\000\137\002\022\000\137\002\047\000\137\002\069\000\137\002\
\\071\000\137\002\095\000\137\002\000\000\
\\001\000\002\000\138\002\005\000\138\002\018\000\138\002\020\000\138\002\
\\021\000\138\002\022\000\138\002\047\000\138\002\069\000\138\002\
\\071\000\138\002\095\000\138\002\000\000\
\\001\000\002\000\139\002\005\000\139\002\018\000\139\002\020\000\139\002\
\\021\000\139\002\022\000\139\002\047\000\139\002\069\000\139\002\
\\071\000\139\002\095\000\139\002\000\000\
\\001\000\002\000\140\002\005\000\140\002\018\000\140\002\020\000\140\002\
\\021\000\140\002\022\000\140\002\047\000\140\002\069\000\140\002\
\\071\000\140\002\095\000\140\002\000\000\
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
\\085\000\141\002\086\000\141\002\087\000\141\002\088\000\141\002\
\\089\000\141\002\091\000\141\002\092\000\141\002\093\000\141\002\
\\094\000\141\002\095\000\141\002\097\000\141\002\098\000\141\002\
\\099\000\141\002\000\000\
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
\\085\000\142\002\086\000\142\002\087\000\142\002\088\000\142\002\
\\089\000\142\002\091\000\142\002\092\000\142\002\093\000\142\002\
\\094\000\142\002\095\000\142\002\097\000\142\002\098\000\142\002\
\\099\000\142\002\000\000\
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
\\085\000\143\002\086\000\143\002\087\000\143\002\088\000\143\002\
\\089\000\143\002\091\000\143\002\092\000\143\002\093\000\143\002\
\\094\000\143\002\095\000\143\002\097\000\143\002\098\000\143\002\
\\099\000\143\002\000\000\
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
\\085\000\144\002\086\000\144\002\087\000\144\002\088\000\144\002\
\\089\000\144\002\091\000\144\002\092\000\144\002\093\000\144\002\
\\094\000\144\002\095\000\144\002\097\000\144\002\098\000\144\002\
\\099\000\144\002\000\000\
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
\\085\000\145\002\086\000\145\002\087\000\145\002\088\000\145\002\
\\089\000\145\002\091\000\145\002\092\000\145\002\093\000\145\002\
\\094\000\145\002\095\000\145\002\097\000\145\002\098\000\145\002\
\\099\000\145\002\000\000\
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
\\085\000\146\002\086\000\146\002\087\000\146\002\088\000\146\002\
\\089\000\146\002\091\000\146\002\092\000\146\002\093\000\146\002\
\\094\000\146\002\095\000\146\002\097\000\146\002\098\000\146\002\
\\099\000\146\002\000\000\
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
\\085\000\147\002\086\000\147\002\087\000\147\002\088\000\147\002\
\\089\000\147\002\091\000\147\002\092\000\147\002\093\000\147\002\
\\094\000\147\002\095\000\147\002\097\000\147\002\098\000\147\002\
\\099\000\147\002\000\000\
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
\\085\000\148\002\086\000\148\002\087\000\148\002\088\000\148\002\
\\089\000\148\002\091\000\148\002\092\000\148\002\093\000\148\002\
\\094\000\148\002\095\000\148\002\097\000\148\002\098\000\148\002\
\\099\000\148\002\000\000\
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
\\085\000\149\002\086\000\149\002\087\000\149\002\088\000\149\002\
\\089\000\149\002\091\000\149\002\092\000\149\002\093\000\149\002\
\\094\000\149\002\095\000\149\002\097\000\149\002\098\000\149\002\
\\099\000\149\002\000\000\
\\001\000\002\000\150\002\005\000\150\002\007\000\150\002\008\000\150\002\
\\012\000\150\002\018\000\150\002\020\000\150\002\021\000\150\002\
\\022\000\150\002\035\000\150\002\036\000\150\002\037\000\189\001\
\\038\000\150\002\039\000\150\002\040\000\150\002\041\000\150\002\
\\042\000\150\002\043\000\150\002\044\000\150\002\045\000\150\002\
\\046\000\150\002\047\000\150\002\060\000\150\002\061\000\150\002\
\\062\000\150\002\063\000\150\002\064\000\150\002\065\000\150\002\
\\066\000\150\002\067\000\150\002\069\000\150\002\070\000\150\002\
\\071\000\150\002\072\000\150\002\074\000\150\002\075\000\150\002\
\\076\000\150\002\077\000\150\002\078\000\150\002\080\000\150\002\
\\081\000\150\002\082\000\150\002\083\000\150\002\084\000\150\002\
\\085\000\150\002\086\000\150\002\087\000\150\002\088\000\150\002\
\\089\000\150\002\091\000\150\002\092\000\150\002\093\000\150\002\
\\094\000\150\002\095\000\150\002\097\000\150\002\098\000\150\002\
\\099\000\150\002\000\000\
\\001\000\002\000\151\002\005\000\151\002\007\000\151\002\008\000\151\002\
\\012\000\151\002\018\000\151\002\020\000\151\002\021\000\151\002\
\\022\000\151\002\035\000\151\002\036\000\151\002\037\000\151\002\
\\038\000\151\002\039\000\151\002\040\000\151\002\041\000\151\002\
\\042\000\151\002\043\000\151\002\044\000\151\002\045\000\151\002\
\\046\000\151\002\047\000\151\002\060\000\151\002\061\000\151\002\
\\062\000\151\002\063\000\151\002\064\000\151\002\065\000\151\002\
\\066\000\151\002\067\000\151\002\069\000\151\002\070\000\151\002\
\\071\000\151\002\072\000\151\002\074\000\151\002\075\000\151\002\
\\076\000\151\002\077\000\151\002\078\000\151\002\080\000\151\002\
\\081\000\151\002\082\000\151\002\083\000\151\002\084\000\151\002\
\\085\000\151\002\086\000\151\002\087\000\151\002\088\000\151\002\
\\089\000\151\002\091\000\151\002\092\000\151\002\093\000\151\002\
\\094\000\151\002\095\000\151\002\097\000\151\002\098\000\151\002\
\\099\000\151\002\000\000\
\\001\000\002\000\152\002\005\000\152\002\007\000\152\002\008\000\152\002\
\\012\000\152\002\018\000\152\002\020\000\152\002\021\000\152\002\
\\022\000\152\002\035\000\152\002\036\000\152\002\037\000\152\002\
\\038\000\152\002\039\000\152\002\040\000\152\002\041\000\152\002\
\\042\000\152\002\043\000\152\002\044\000\152\002\045\000\152\002\
\\046\000\152\002\047\000\152\002\060\000\152\002\061\000\152\002\
\\062\000\152\002\063\000\152\002\064\000\152\002\065\000\152\002\
\\066\000\152\002\067\000\152\002\069\000\152\002\070\000\152\002\
\\071\000\152\002\072\000\152\002\074\000\152\002\075\000\152\002\
\\076\000\152\002\077\000\152\002\078\000\152\002\080\000\152\002\
\\081\000\152\002\082\000\152\002\083\000\152\002\084\000\152\002\
\\085\000\152\002\086\000\152\002\087\000\152\002\088\000\152\002\
\\089\000\152\002\091\000\152\002\092\000\152\002\093\000\152\002\
\\094\000\152\002\095\000\152\002\097\000\152\002\098\000\152\002\
\\099\000\152\002\000\000\
\\001\000\002\000\153\002\005\000\153\002\007\000\153\002\008\000\153\002\
\\012\000\153\002\018\000\153\002\020\000\153\002\021\000\153\002\
\\022\000\153\002\035\000\153\002\036\000\153\002\037\000\153\002\
\\038\000\153\002\039\000\153\002\040\000\153\002\041\000\153\002\
\\042\000\153\002\043\000\153\002\044\000\153\002\045\000\153\002\
\\046\000\153\002\047\000\153\002\060\000\153\002\061\000\153\002\
\\062\000\153\002\063\000\153\002\064\000\153\002\065\000\153\002\
\\066\000\153\002\067\000\153\002\069\000\153\002\070\000\153\002\
\\071\000\153\002\072\000\153\002\074\000\153\002\075\000\153\002\
\\076\000\153\002\077\000\153\002\078\000\153\002\080\000\153\002\
\\081\000\153\002\082\000\153\002\083\000\153\002\084\000\153\002\
\\085\000\153\002\086\000\153\002\087\000\153\002\088\000\153\002\
\\089\000\153\002\091\000\153\002\092\000\153\002\093\000\153\002\
\\094\000\153\002\095\000\153\002\097\000\153\002\098\000\153\002\
\\099\000\153\002\000\000\
\\001\000\002\000\154\002\005\000\154\002\007\000\154\002\008\000\154\002\
\\012\000\154\002\018\000\154\002\020\000\154\002\021\000\154\002\
\\022\000\154\002\035\000\154\002\036\000\154\002\037\000\154\002\
\\038\000\154\002\039\000\154\002\040\000\154\002\041\000\154\002\
\\042\000\154\002\043\000\154\002\044\000\154\002\045\000\154\002\
\\046\000\154\002\047\000\154\002\060\000\154\002\061\000\154\002\
\\062\000\154\002\063\000\154\002\064\000\154\002\065\000\154\002\
\\066\000\154\002\067\000\154\002\069\000\154\002\070\000\154\002\
\\071\000\154\002\072\000\154\002\074\000\154\002\075\000\154\002\
\\076\000\154\002\077\000\154\002\078\000\154\002\080\000\154\002\
\\081\000\154\002\082\000\154\002\083\000\154\002\084\000\154\002\
\\085\000\154\002\086\000\154\002\087\000\154\002\088\000\154\002\
\\089\000\154\002\091\000\154\002\092\000\154\002\093\000\154\002\
\\094\000\154\002\095\000\154\002\097\000\154\002\098\000\154\002\
\\099\000\154\002\000\000\
\\001\000\002\000\155\002\005\000\155\002\007\000\155\002\008\000\155\002\
\\012\000\155\002\018\000\155\002\020\000\155\002\021\000\155\002\
\\022\000\155\002\035\000\155\002\036\000\155\002\037\000\155\002\
\\038\000\155\002\039\000\155\002\040\000\155\002\041\000\155\002\
\\042\000\155\002\043\000\155\002\044\000\155\002\045\000\155\002\
\\046\000\155\002\047\000\155\002\060\000\155\002\061\000\155\002\
\\062\000\155\002\063\000\155\002\064\000\155\002\065\000\155\002\
\\066\000\155\002\067\000\155\002\069\000\155\002\070\000\155\002\
\\071\000\155\002\072\000\155\002\074\000\155\002\075\000\155\002\
\\076\000\155\002\077\000\155\002\078\000\155\002\080\000\155\002\
\\081\000\155\002\082\000\155\002\083\000\155\002\084\000\155\002\
\\085\000\155\002\086\000\155\002\087\000\155\002\088\000\155\002\
\\089\000\155\002\091\000\155\002\092\000\155\002\093\000\155\002\
\\094\000\155\002\095\000\155\002\097\000\155\002\098\000\155\002\
\\099\000\155\002\000\000\
\\001\000\002\000\156\002\005\000\156\002\007\000\156\002\008\000\156\002\
\\012\000\156\002\018\000\156\002\020\000\156\002\021\000\156\002\
\\022\000\156\002\035\000\156\002\036\000\156\002\037\000\156\002\
\\038\000\156\002\039\000\156\002\040\000\156\002\041\000\156\002\
\\042\000\156\002\043\000\156\002\044\000\156\002\045\000\156\002\
\\046\000\156\002\047\000\156\002\060\000\156\002\061\000\156\002\
\\062\000\156\002\063\000\156\002\064\000\156\002\065\000\156\002\
\\066\000\156\002\067\000\156\002\069\000\156\002\070\000\156\002\
\\071\000\156\002\072\000\156\002\074\000\156\002\075\000\156\002\
\\076\000\156\002\077\000\156\002\078\000\156\002\080\000\156\002\
\\081\000\156\002\082\000\156\002\083\000\156\002\084\000\156\002\
\\085\000\156\002\086\000\156\002\087\000\156\002\088\000\156\002\
\\089\000\156\002\091\000\156\002\092\000\156\002\093\000\156\002\
\\094\000\156\002\095\000\156\002\097\000\156\002\098\000\156\002\
\\099\000\156\002\000\000\
\\001\000\002\000\157\002\005\000\157\002\007\000\157\002\008\000\157\002\
\\012\000\157\002\018\000\157\002\020\000\157\002\021\000\157\002\
\\022\000\157\002\035\000\157\002\036\000\157\002\037\000\157\002\
\\038\000\157\002\039\000\157\002\040\000\157\002\041\000\157\002\
\\042\000\157\002\043\000\157\002\044\000\157\002\045\000\157\002\
\\046\000\157\002\047\000\157\002\060\000\157\002\061\000\157\002\
\\062\000\157\002\063\000\157\002\064\000\157\002\065\000\157\002\
\\066\000\157\002\067\000\157\002\069\000\157\002\070\000\157\002\
\\071\000\157\002\072\000\157\002\074\000\157\002\075\000\157\002\
\\076\000\157\002\077\000\157\002\078\000\157\002\080\000\157\002\
\\081\000\157\002\082\000\157\002\083\000\157\002\084\000\157\002\
\\085\000\157\002\086\000\157\002\087\000\157\002\088\000\157\002\
\\089\000\157\002\091\000\157\002\092\000\157\002\093\000\157\002\
\\094\000\157\002\095\000\157\002\097\000\157\002\098\000\157\002\
\\099\000\157\002\000\000\
\\001\000\002\000\158\002\005\000\158\002\007\000\158\002\008\000\158\002\
\\012\000\158\002\018\000\158\002\020\000\158\002\021\000\158\002\
\\022\000\158\002\035\000\158\002\036\000\158\002\037\000\158\002\
\\038\000\158\002\039\000\158\002\040\000\158\002\041\000\158\002\
\\042\000\158\002\043\000\158\002\044\000\158\002\045\000\158\002\
\\046\000\158\002\047\000\158\002\060\000\158\002\061\000\158\002\
\\062\000\158\002\063\000\158\002\064\000\158\002\065\000\158\002\
\\066\000\158\002\067\000\158\002\069\000\158\002\070\000\158\002\
\\071\000\158\002\072\000\158\002\074\000\158\002\075\000\158\002\
\\076\000\158\002\077\000\158\002\078\000\158\002\080\000\158\002\
\\081\000\158\002\082\000\158\002\083\000\158\002\084\000\158\002\
\\085\000\158\002\086\000\158\002\087\000\158\002\088\000\158\002\
\\089\000\158\002\091\000\158\002\092\000\158\002\093\000\158\002\
\\094\000\158\002\095\000\158\002\097\000\158\002\098\000\158\002\
\\099\000\158\002\000\000\
\\001\000\002\000\159\002\005\000\159\002\007\000\159\002\008\000\159\002\
\\012\000\159\002\018\000\159\002\020\000\159\002\021\000\159\002\
\\022\000\159\002\035\000\159\002\036\000\159\002\037\000\159\002\
\\038\000\159\002\039\000\159\002\040\000\159\002\041\000\159\002\
\\042\000\159\002\043\000\159\002\044\000\159\002\045\000\159\002\
\\046\000\159\002\047\000\159\002\060\000\159\002\061\000\159\002\
\\062\000\159\002\063\000\159\002\064\000\159\002\065\000\159\002\
\\066\000\159\002\067\000\159\002\069\000\159\002\070\000\159\002\
\\071\000\159\002\072\000\159\002\074\000\159\002\075\000\159\002\
\\076\000\159\002\077\000\159\002\078\000\159\002\080\000\159\002\
\\081\000\159\002\082\000\159\002\083\000\159\002\084\000\159\002\
\\085\000\159\002\086\000\159\002\087\000\159\002\088\000\159\002\
\\089\000\159\002\091\000\159\002\092\000\159\002\093\000\159\002\
\\094\000\159\002\095\000\159\002\097\000\159\002\098\000\159\002\
\\099\000\159\002\000\000\
\\001\000\002\000\160\002\005\000\160\002\007\000\160\002\008\000\160\002\
\\012\000\160\002\018\000\160\002\020\000\160\002\021\000\160\002\
\\022\000\160\002\035\000\160\002\036\000\160\002\037\000\160\002\
\\038\000\160\002\039\000\160\002\040\000\160\002\041\000\160\002\
\\042\000\160\002\043\000\160\002\044\000\160\002\045\000\160\002\
\\046\000\160\002\047\000\160\002\060\000\160\002\061\000\160\002\
\\062\000\160\002\063\000\160\002\064\000\160\002\065\000\160\002\
\\066\000\160\002\067\000\160\002\069\000\160\002\070\000\160\002\
\\071\000\160\002\072\000\160\002\074\000\160\002\075\000\160\002\
\\076\000\160\002\077\000\160\002\078\000\160\002\080\000\160\002\
\\081\000\160\002\082\000\160\002\083\000\160\002\084\000\160\002\
\\085\000\160\002\086\000\160\002\087\000\160\002\088\000\160\002\
\\089\000\160\002\091\000\160\002\092\000\160\002\093\000\160\002\
\\094\000\160\002\095\000\160\002\097\000\160\002\098\000\160\002\
\\099\000\160\002\000\000\
\\001\000\002\000\178\002\005\000\178\002\007\000\178\002\012\000\178\002\
\\018\000\178\002\020\000\178\002\021\000\178\002\022\000\178\002\
\\036\000\178\002\038\000\178\002\039\000\178\002\040\000\178\002\
\\041\000\178\002\042\000\178\002\043\000\178\002\044\000\178\002\
\\047\000\178\002\069\000\178\002\071\000\178\002\087\000\178\002\
\\088\000\178\002\092\000\178\002\095\000\178\002\098\000\178\002\000\000\
\\001\000\002\000\179\002\005\000\179\002\007\000\179\002\012\000\179\002\
\\018\000\179\002\020\000\179\002\021\000\179\002\022\000\179\002\
\\036\000\179\002\038\000\179\002\039\000\179\002\040\000\179\002\
\\041\000\179\002\042\000\179\002\043\000\179\002\044\000\179\002\
\\047\000\179\002\069\000\179\002\071\000\179\002\079\000\017\001\
\\087\000\179\002\088\000\179\002\092\000\179\002\095\000\179\002\
\\098\000\179\002\000\000\
\\001\000\002\000\180\002\005\000\180\002\007\000\180\002\012\000\180\002\
\\018\000\180\002\020\000\180\002\021\000\180\002\022\000\180\002\
\\036\000\180\002\038\000\180\002\039\000\180\002\040\000\180\002\
\\041\000\180\002\042\000\180\002\043\000\180\002\044\000\180\002\
\\047\000\180\002\069\000\180\002\071\000\180\002\087\000\180\002\
\\088\000\180\002\092\000\180\002\095\000\180\002\098\000\180\002\000\000\
\\001\000\002\000\184\002\005\000\184\002\007\000\184\002\012\000\184\002\
\\018\000\184\002\020\000\184\002\021\000\184\002\022\000\184\002\
\\036\000\184\002\038\000\184\002\039\000\184\002\040\000\184\002\
\\041\000\184\002\042\000\184\002\043\000\184\002\044\000\184\002\
\\045\000\182\001\046\000\181\001\047\000\184\002\069\000\184\002\
\\071\000\184\002\087\000\184\002\088\000\184\002\092\000\184\002\
\\095\000\184\002\098\000\184\002\000\000\
\\001\000\002\000\185\002\005\000\185\002\007\000\185\002\012\000\185\002\
\\018\000\185\002\020\000\185\002\021\000\185\002\022\000\185\002\
\\036\000\185\002\038\000\185\002\039\000\185\002\040\000\185\002\
\\041\000\185\002\042\000\185\002\043\000\185\002\044\000\185\002\
\\047\000\185\002\069\000\185\002\071\000\185\002\087\000\185\002\
\\088\000\185\002\092\000\185\002\095\000\185\002\098\000\185\002\000\000\
\\001\000\002\000\186\002\005\000\186\002\007\000\186\002\012\000\186\002\
\\018\000\186\002\020\000\186\002\021\000\186\002\022\000\186\002\
\\036\000\186\002\038\000\186\002\039\000\186\002\040\000\186\002\
\\041\000\186\002\042\000\186\002\043\000\186\002\044\000\186\002\
\\045\000\186\002\046\000\186\002\047\000\186\002\069\000\186\002\
\\071\000\186\002\087\000\186\002\088\000\186\002\092\000\186\002\
\\095\000\186\002\098\000\186\002\000\000\
\\001\000\002\000\187\002\005\000\187\002\007\000\187\002\012\000\187\002\
\\018\000\187\002\020\000\187\002\021\000\187\002\022\000\187\002\
\\036\000\187\002\038\000\187\002\039\000\187\002\040\000\187\002\
\\041\000\187\002\042\000\187\002\043\000\187\002\044\000\187\002\
\\045\000\187\002\046\000\187\002\047\000\187\002\069\000\187\002\
\\071\000\187\002\087\000\187\002\088\000\187\002\092\000\187\002\
\\095\000\187\002\098\000\187\002\000\000\
\\001\000\002\000\188\002\005\000\188\002\012\000\188\002\018\000\188\002\
\\020\000\188\002\021\000\188\002\022\000\188\002\047\000\188\002\
\\069\000\188\002\071\000\188\002\095\000\188\002\000\000\
\\001\000\002\000\189\002\005\000\189\002\012\000\189\002\018\000\189\002\
\\020\000\189\002\021\000\189\002\022\000\189\002\047\000\189\002\
\\069\000\189\002\071\000\189\002\095\000\189\002\000\000\
\\001\000\002\000\235\002\003\000\235\002\004\000\235\002\006\000\235\002\
\\008\000\235\002\010\000\235\002\011\000\235\002\012\000\235\002\
\\013\000\235\002\014\000\235\002\017\000\235\002\018\000\235\002\
\\021\000\235\002\048\000\235\002\049\000\235\002\050\000\235\002\
\\051\000\235\002\052\000\235\002\053\000\235\002\054\000\235\002\
\\055\000\235\002\056\000\235\002\057\000\235\002\058\000\235\002\
\\059\000\235\002\087\000\235\002\000\000\
\\001\000\002\000\236\002\003\000\236\002\004\000\236\002\006\000\236\002\
\\008\000\236\002\010\000\236\002\011\000\236\002\012\000\236\002\
\\013\000\236\002\014\000\236\002\017\000\236\002\018\000\236\002\
\\021\000\236\002\048\000\236\002\049\000\236\002\050\000\236\002\
\\051\000\236\002\052\000\236\002\053\000\236\002\054\000\236\002\
\\055\000\236\002\056\000\236\002\057\000\236\002\058\000\236\002\
\\059\000\236\002\087\000\236\002\000\000\
\\001\000\002\000\237\002\003\000\237\002\004\000\237\002\006\000\237\002\
\\008\000\237\002\010\000\237\002\011\000\237\002\012\000\237\002\
\\013\000\237\002\014\000\237\002\017\000\237\002\018\000\237\002\
\\021\000\237\002\048\000\237\002\049\000\237\002\050\000\237\002\
\\051\000\237\002\052\000\237\002\053\000\237\002\054\000\237\002\
\\055\000\237\002\056\000\237\002\057\000\237\002\058\000\237\002\
\\059\000\237\002\087\000\237\002\000\000\
\\001\000\002\000\238\002\003\000\238\002\004\000\238\002\006\000\238\002\
\\008\000\238\002\010\000\238\002\011\000\238\002\012\000\238\002\
\\013\000\238\002\014\000\238\002\017\000\238\002\018\000\238\002\
\\021\000\238\002\048\000\238\002\049\000\238\002\050\000\238\002\
\\051\000\238\002\052\000\238\002\053\000\238\002\054\000\238\002\
\\055\000\238\002\056\000\238\002\057\000\238\002\058\000\238\002\
\\059\000\238\002\087\000\238\002\000\000\
\\001\000\002\000\239\002\003\000\239\002\004\000\239\002\006\000\239\002\
\\008\000\239\002\010\000\239\002\011\000\239\002\012\000\239\002\
\\013\000\239\002\014\000\239\002\015\000\239\002\017\000\239\002\
\\018\000\239\002\021\000\239\002\023\000\239\002\024\000\239\002\
\\025\000\239\002\026\000\239\002\027\000\239\002\028\000\239\002\
\\029\000\239\002\030\000\239\002\031\000\239\002\032\000\239\002\
\\033\000\239\002\034\000\239\002\048\000\239\002\049\000\239\002\
\\050\000\239\002\051\000\239\002\052\000\239\002\053\000\239\002\
\\054\000\239\002\055\000\239\002\056\000\239\002\057\000\239\002\
\\058\000\239\002\059\000\239\002\087\000\239\002\000\000\
\\001\000\002\000\240\002\003\000\240\002\004\000\240\002\006\000\240\002\
\\008\000\240\002\010\000\240\002\011\000\240\002\012\000\240\002\
\\013\000\240\002\014\000\240\002\015\000\240\002\017\000\240\002\
\\018\000\240\002\021\000\240\002\023\000\240\002\024\000\240\002\
\\025\000\240\002\026\000\240\002\027\000\240\002\028\000\240\002\
\\029\000\240\002\030\000\240\002\031\000\240\002\032\000\240\002\
\\033\000\240\002\034\000\240\002\048\000\240\002\049\000\240\002\
\\050\000\240\002\051\000\240\002\052\000\240\002\053\000\240\002\
\\054\000\240\002\055\000\240\002\056\000\240\002\057\000\240\002\
\\058\000\240\002\059\000\240\002\087\000\240\002\000\000\
\\001\000\002\000\241\002\003\000\241\002\004\000\241\002\005\000\196\000\
\\006\000\241\002\008\000\241\002\009\000\195\000\010\000\241\002\
\\011\000\241\002\012\000\241\002\013\000\241\002\014\000\241\002\
\\015\000\241\002\016\000\194\000\017\000\241\002\018\000\241\002\
\\021\000\241\002\023\000\241\002\024\000\241\002\025\000\241\002\
\\026\000\241\002\027\000\241\002\028\000\241\002\029\000\241\002\
\\030\000\241\002\031\000\241\002\032\000\241\002\033\000\241\002\
\\034\000\241\002\048\000\241\002\049\000\241\002\050\000\241\002\
\\051\000\241\002\052\000\241\002\053\000\241\002\054\000\241\002\
\\055\000\241\002\056\000\241\002\057\000\241\002\058\000\241\002\
\\059\000\241\002\068\000\193\000\087\000\241\002\000\000\
\\001\000\002\000\241\002\003\000\241\002\004\000\241\002\005\000\196\000\
\\009\000\195\000\012\000\241\002\014\000\241\002\015\000\006\003\
\\016\000\194\000\017\000\241\002\018\000\241\002\021\000\241\002\
\\023\000\006\003\024\000\006\003\025\000\006\003\026\000\006\003\
\\027\000\006\003\028\000\006\003\029\000\006\003\030\000\006\003\
\\031\000\006\003\032\000\006\003\033\000\006\003\034\000\006\003\
\\048\000\241\002\049\000\241\002\050\000\241\002\051\000\241\002\
\\052\000\241\002\053\000\241\002\054\000\241\002\055\000\241\002\
\\056\000\241\002\057\000\241\002\058\000\241\002\059\000\241\002\
\\068\000\193\000\000\000\
\\001\000\002\000\242\002\003\000\242\002\004\000\242\002\006\000\242\002\
\\008\000\242\002\010\000\242\002\011\000\242\002\012\000\242\002\
\\013\000\242\002\014\000\242\002\015\000\242\002\017\000\242\002\
\\018\000\242\002\021\000\242\002\023\000\242\002\024\000\242\002\
\\025\000\242\002\026\000\242\002\027\000\242\002\028\000\242\002\
\\029\000\242\002\030\000\242\002\031\000\242\002\032\000\242\002\
\\033\000\242\002\034\000\242\002\048\000\242\002\049\000\242\002\
\\050\000\242\002\051\000\242\002\052\000\242\002\053\000\242\002\
\\054\000\242\002\055\000\242\002\056\000\242\002\057\000\242\002\
\\058\000\242\002\059\000\242\002\087\000\242\002\000\000\
\\001\000\002\000\243\002\003\000\243\002\004\000\243\002\006\000\243\002\
\\008\000\243\002\010\000\243\002\011\000\243\002\012\000\243\002\
\\013\000\243\002\014\000\243\002\015\000\243\002\017\000\243\002\
\\018\000\243\002\021\000\243\002\023\000\243\002\024\000\243\002\
\\025\000\243\002\026\000\243\002\027\000\243\002\028\000\243\002\
\\029\000\243\002\030\000\243\002\031\000\243\002\032\000\243\002\
\\033\000\243\002\034\000\243\002\048\000\243\002\049\000\243\002\
\\050\000\243\002\051\000\243\002\052\000\243\002\053\000\243\002\
\\054\000\243\002\055\000\243\002\056\000\243\002\057\000\243\002\
\\058\000\243\002\059\000\243\002\087\000\243\002\000\000\
\\001\000\002\000\244\002\003\000\244\002\004\000\244\002\006\000\244\002\
\\008\000\244\002\010\000\244\002\011\000\244\002\012\000\244\002\
\\013\000\244\002\014\000\244\002\015\000\244\002\017\000\244\002\
\\018\000\244\002\021\000\244\002\023\000\244\002\024\000\244\002\
\\025\000\244\002\026\000\244\002\027\000\244\002\028\000\244\002\
\\029\000\244\002\030\000\244\002\031\000\244\002\032\000\244\002\
\\033\000\244\002\034\000\244\002\048\000\244\002\049\000\244\002\
\\050\000\244\002\051\000\244\002\052\000\244\002\053\000\244\002\
\\054\000\244\002\055\000\244\002\056\000\244\002\057\000\244\002\
\\058\000\244\002\059\000\244\002\087\000\244\002\000\000\
\\001\000\002\000\245\002\003\000\245\002\004\000\245\002\006\000\245\002\
\\008\000\245\002\010\000\245\002\011\000\245\002\012\000\245\002\
\\013\000\245\002\014\000\245\002\015\000\245\002\017\000\245\002\
\\018\000\245\002\021\000\245\002\023\000\245\002\024\000\245\002\
\\025\000\245\002\026\000\245\002\027\000\245\002\028\000\245\002\
\\029\000\245\002\030\000\245\002\031\000\245\002\032\000\245\002\
\\033\000\245\002\034\000\245\002\048\000\245\002\049\000\245\002\
\\050\000\245\002\051\000\245\002\052\000\245\002\053\000\245\002\
\\054\000\245\002\055\000\245\002\056\000\245\002\057\000\245\002\
\\058\000\245\002\059\000\245\002\087\000\245\002\000\000\
\\001\000\002\000\246\002\003\000\246\002\004\000\246\002\006\000\246\002\
\\008\000\246\002\010\000\246\002\011\000\246\002\012\000\246\002\
\\013\000\246\002\014\000\246\002\015\000\246\002\017\000\246\002\
\\018\000\246\002\021\000\246\002\023\000\246\002\024\000\246\002\
\\025\000\246\002\026\000\246\002\027\000\246\002\028\000\246\002\
\\029\000\246\002\030\000\246\002\031\000\246\002\032\000\246\002\
\\033\000\246\002\034\000\246\002\048\000\246\002\049\000\246\002\
\\050\000\246\002\051\000\246\002\052\000\246\002\053\000\246\002\
\\054\000\246\002\055\000\246\002\056\000\246\002\057\000\246\002\
\\058\000\246\002\059\000\246\002\087\000\246\002\000\000\
\\001\000\002\000\246\002\003\000\246\002\004\000\246\002\012\000\246\002\
\\014\000\246\002\015\000\007\003\017\000\246\002\018\000\246\002\
\\021\000\246\002\023\000\007\003\024\000\007\003\025\000\007\003\
\\026\000\007\003\027\000\007\003\028\000\007\003\029\000\007\003\
\\030\000\007\003\031\000\007\003\032\000\007\003\033\000\007\003\
\\034\000\007\003\048\000\246\002\049\000\246\002\050\000\246\002\
\\051\000\246\002\052\000\246\002\053\000\246\002\054\000\246\002\
\\055\000\246\002\056\000\246\002\057\000\246\002\058\000\246\002\
\\059\000\246\002\000\000\
\\001\000\002\000\247\002\003\000\247\002\004\000\247\002\006\000\247\002\
\\008\000\247\002\010\000\247\002\011\000\247\002\012\000\247\002\
\\013\000\247\002\014\000\247\002\015\000\247\002\017\000\247\002\
\\018\000\247\002\021\000\247\002\023\000\247\002\024\000\247\002\
\\025\000\247\002\026\000\247\002\027\000\247\002\028\000\247\002\
\\029\000\247\002\030\000\247\002\031\000\247\002\032\000\247\002\
\\033\000\247\002\034\000\247\002\048\000\247\002\049\000\247\002\
\\050\000\247\002\051\000\247\002\052\000\247\002\053\000\247\002\
\\054\000\247\002\055\000\247\002\056\000\247\002\057\000\247\002\
\\058\000\247\002\059\000\247\002\087\000\247\002\000\000\
\\001\000\002\000\248\002\003\000\248\002\004\000\248\002\006\000\248\002\
\\007\000\120\001\008\000\248\002\010\000\248\002\011\000\248\002\
\\012\000\248\002\013\000\248\002\014\000\248\002\015\000\248\002\
\\017\000\248\002\018\000\248\002\021\000\248\002\023\000\248\002\
\\024\000\248\002\025\000\248\002\026\000\248\002\027\000\248\002\
\\028\000\248\002\029\000\248\002\030\000\248\002\031\000\248\002\
\\032\000\248\002\033\000\248\002\034\000\248\002\048\000\248\002\
\\049\000\248\002\050\000\248\002\051\000\248\002\052\000\248\002\
\\053\000\248\002\054\000\248\002\055\000\248\002\056\000\248\002\
\\057\000\248\002\058\000\248\002\059\000\248\002\087\000\248\002\000\000\
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
\\059\000\249\002\068\000\249\002\087\000\249\002\000\000\
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
\\059\000\250\002\068\000\250\002\087\000\250\002\000\000\
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
\\059\000\251\002\068\000\251\002\087\000\251\002\000\000\
\\001\000\002\000\252\002\003\000\252\002\004\000\252\002\005\000\252\002\
\\006\000\252\002\008\000\252\002\009\000\252\002\010\000\252\002\
\\011\000\252\002\012\000\252\002\013\000\252\002\014\000\252\002\
\\015\000\252\002\016\000\252\002\017\000\252\002\018\000\252\002\
\\021\000\252\002\023\000\252\002\024\000\252\002\025\000\252\002\
\\026\000\252\002\027\000\252\002\028\000\252\002\029\000\252\002\
\\030\000\252\002\031\000\252\002\032\000\252\002\033\000\252\002\
\\034\000\252\002\048\000\252\002\049\000\252\002\050\000\252\002\
\\051\000\252\002\052\000\252\002\053\000\252\002\054\000\252\002\
\\055\000\252\002\056\000\252\002\057\000\252\002\058\000\252\002\
\\059\000\252\002\068\000\252\002\087\000\252\002\000\000\
\\001\000\002\000\253\002\003\000\253\002\004\000\253\002\005\000\253\002\
\\006\000\253\002\008\000\253\002\009\000\253\002\010\000\253\002\
\\011\000\253\002\012\000\253\002\013\000\253\002\014\000\253\002\
\\015\000\253\002\016\000\253\002\017\000\253\002\018\000\253\002\
\\021\000\253\002\023\000\253\002\024\000\253\002\025\000\253\002\
\\026\000\253\002\027\000\253\002\028\000\253\002\029\000\253\002\
\\030\000\253\002\031\000\253\002\032\000\253\002\033\000\253\002\
\\034\000\253\002\048\000\253\002\049\000\253\002\050\000\253\002\
\\051\000\253\002\052\000\253\002\053\000\253\002\054\000\253\002\
\\055\000\253\002\056\000\253\002\057\000\253\002\058\000\253\002\
\\059\000\253\002\068\000\253\002\087\000\253\002\000\000\
\\001\000\002\000\254\002\003\000\254\002\004\000\254\002\005\000\254\002\
\\006\000\254\002\008\000\254\002\009\000\254\002\010\000\254\002\
\\011\000\254\002\012\000\254\002\013\000\254\002\014\000\254\002\
\\015\000\254\002\016\000\254\002\017\000\254\002\018\000\254\002\
\\021\000\254\002\023\000\254\002\024\000\254\002\025\000\254\002\
\\026\000\254\002\027\000\254\002\028\000\254\002\029\000\254\002\
\\030\000\254\002\031\000\254\002\032\000\254\002\033\000\254\002\
\\034\000\254\002\048\000\254\002\049\000\254\002\050\000\254\002\
\\051\000\254\002\052\000\254\002\053\000\254\002\054\000\254\002\
\\055\000\254\002\056\000\254\002\057\000\254\002\058\000\254\002\
\\059\000\254\002\068\000\254\002\087\000\254\002\000\000\
\\001\000\002\000\255\002\003\000\255\002\004\000\255\002\005\000\255\002\
\\006\000\255\002\008\000\255\002\009\000\255\002\010\000\255\002\
\\011\000\255\002\012\000\255\002\013\000\255\002\014\000\255\002\
\\015\000\255\002\016\000\255\002\017\000\255\002\018\000\255\002\
\\021\000\255\002\023\000\255\002\024\000\255\002\025\000\255\002\
\\026\000\255\002\027\000\255\002\028\000\255\002\029\000\255\002\
\\030\000\255\002\031\000\255\002\032\000\255\002\033\000\255\002\
\\034\000\255\002\048\000\255\002\049\000\255\002\050\000\255\002\
\\051\000\255\002\052\000\255\002\053\000\255\002\054\000\255\002\
\\055\000\255\002\056\000\255\002\057\000\255\002\058\000\255\002\
\\059\000\255\002\068\000\255\002\087\000\255\002\000\000\
\\001\000\002\000\000\003\003\000\000\003\004\000\000\003\005\000\000\003\
\\006\000\000\003\008\000\000\003\009\000\000\003\010\000\000\003\
\\011\000\000\003\012\000\000\003\013\000\000\003\014\000\000\003\
\\015\000\000\003\016\000\000\003\017\000\000\003\018\000\000\003\
\\021\000\000\003\023\000\000\003\024\000\000\003\025\000\000\003\
\\026\000\000\003\027\000\000\003\028\000\000\003\029\000\000\003\
\\030\000\000\003\031\000\000\003\032\000\000\003\033\000\000\003\
\\034\000\000\003\048\000\000\003\049\000\000\003\050\000\000\003\
\\051\000\000\003\052\000\000\003\053\000\000\003\054\000\000\003\
\\055\000\000\003\056\000\000\003\057\000\000\003\058\000\000\003\
\\059\000\000\003\068\000\000\003\087\000\000\003\000\000\
\\001\000\002\000\001\003\003\000\001\003\004\000\001\003\005\000\001\003\
\\006\000\001\003\008\000\001\003\009\000\001\003\010\000\001\003\
\\011\000\001\003\012\000\001\003\013\000\001\003\014\000\001\003\
\\015\000\001\003\016\000\001\003\017\000\001\003\018\000\001\003\
\\021\000\001\003\023\000\001\003\024\000\001\003\025\000\001\003\
\\026\000\001\003\027\000\001\003\028\000\001\003\029\000\001\003\
\\030\000\001\003\031\000\001\003\032\000\001\003\033\000\001\003\
\\034\000\001\003\048\000\001\003\049\000\001\003\050\000\001\003\
\\051\000\001\003\052\000\001\003\053\000\001\003\054\000\001\003\
\\055\000\001\003\056\000\001\003\057\000\001\003\058\000\001\003\
\\059\000\001\003\068\000\001\003\087\000\001\003\000\000\
\\001\000\002\000\002\003\003\000\002\003\004\000\002\003\005\000\002\003\
\\006\000\002\003\008\000\002\003\009\000\002\003\010\000\002\003\
\\011\000\002\003\012\000\002\003\013\000\002\003\014\000\002\003\
\\015\000\002\003\016\000\002\003\017\000\002\003\018\000\002\003\
\\021\000\002\003\023\000\002\003\024\000\002\003\025\000\002\003\
\\026\000\002\003\027\000\002\003\028\000\002\003\029\000\002\003\
\\030\000\002\003\031\000\002\003\032\000\002\003\033\000\002\003\
\\034\000\002\003\048\000\002\003\049\000\002\003\050\000\002\003\
\\051\000\002\003\052\000\002\003\053\000\002\003\054\000\002\003\
\\055\000\002\003\056\000\002\003\057\000\002\003\058\000\002\003\
\\059\000\002\003\068\000\002\003\087\000\002\003\095\000\192\000\000\000\
\\001\000\002\000\003\003\003\000\003\003\004\000\003\003\005\000\003\003\
\\006\000\003\003\008\000\003\003\009\000\003\003\010\000\003\003\
\\011\000\003\003\012\000\003\003\013\000\003\003\014\000\003\003\
\\015\000\003\003\016\000\003\003\017\000\003\003\018\000\003\003\
\\021\000\003\003\023\000\003\003\024\000\003\003\025\000\003\003\
\\026\000\003\003\027\000\003\003\028\000\003\003\029\000\003\003\
\\030\000\003\003\031\000\003\003\032\000\003\003\033\000\003\003\
\\034\000\003\003\048\000\003\003\049\000\003\003\050\000\003\003\
\\051\000\003\003\052\000\003\003\053\000\003\003\054\000\003\003\
\\055\000\003\003\056\000\003\003\057\000\003\003\058\000\003\003\
\\059\000\003\003\068\000\003\003\087\000\003\003\095\000\003\003\000\000\
\\001\000\002\000\004\003\003\000\004\003\004\000\004\003\005\000\004\003\
\\006\000\004\003\008\000\004\003\009\000\004\003\010\000\004\003\
\\011\000\004\003\012\000\004\003\013\000\004\003\014\000\004\003\
\\015\000\004\003\016\000\004\003\017\000\004\003\018\000\004\003\
\\021\000\004\003\023\000\004\003\024\000\004\003\025\000\004\003\
\\026\000\004\003\027\000\004\003\028\000\004\003\029\000\004\003\
\\030\000\004\003\031\000\004\003\032\000\004\003\033\000\004\003\
\\034\000\004\003\048\000\004\003\049\000\004\003\050\000\004\003\
\\051\000\004\003\052\000\004\003\053\000\004\003\054\000\004\003\
\\055\000\004\003\056\000\004\003\057\000\004\003\058\000\004\003\
\\059\000\004\003\068\000\004\003\087\000\004\003\095\000\004\003\000\000\
\\001\000\002\000\005\003\003\000\005\003\004\000\005\003\005\000\005\003\
\\006\000\005\003\008\000\005\003\009\000\005\003\010\000\005\003\
\\011\000\005\003\012\000\005\003\013\000\005\003\014\000\005\003\
\\015\000\005\003\016\000\005\003\017\000\005\003\018\000\005\003\
\\021\000\005\003\023\000\005\003\024\000\005\003\025\000\005\003\
\\026\000\005\003\027\000\005\003\028\000\005\003\029\000\005\003\
\\030\000\005\003\031\000\005\003\032\000\005\003\033\000\005\003\
\\034\000\005\003\048\000\005\003\049\000\005\003\050\000\005\003\
\\051\000\005\003\052\000\005\003\053\000\005\003\054\000\005\003\
\\055\000\005\003\056\000\005\003\057\000\005\003\058\000\005\003\
\\059\000\005\003\068\000\005\003\087\000\005\003\000\000\
\\001\000\002\000\055\000\005\000\065\002\006\000\065\002\009\000\065\002\
\\011\000\065\002\069\000\065\002\076\000\031\000\077\000\030\000\
\\078\000\029\000\091\000\065\002\097\000\065\002\000\000\
\\001\000\002\000\055\000\005\000\066\002\006\000\066\002\009\000\066\002\
\\011\000\066\002\069\000\066\002\091\000\066\002\097\000\066\002\000\000\
\\001\000\002\000\055\000\005\000\054\000\012\000\053\000\069\000\052\000\000\000\
\\001\000\002\000\055\000\005\000\054\000\069\000\052\000\000\000\
\\001\000\002\000\055\000\005\000\234\000\006\000\029\002\009\000\233\000\
\\035\000\044\000\060\000\043\000\061\000\042\000\062\000\041\000\
\\063\000\040\000\064\000\039\000\065\000\038\000\066\000\037\000\
\\067\000\036\000\069\000\052\000\070\000\035\000\072\000\034\000\
\\074\000\033\000\075\000\032\000\076\000\031\000\077\000\030\000\
\\078\000\029\000\080\000\028\000\081\000\027\000\082\000\026\000\
\\083\000\025\000\084\000\024\000\085\000\023\000\086\000\022\000\
\\089\000\021\000\091\000\020\000\094\000\019\000\097\000\018\000\
\\099\000\017\000\000\000\
\\001\000\002\000\055\000\005\000\234\000\006\000\035\002\009\000\233\000\
\\011\000\035\002\069\000\052\000\000\000\
\\001\000\002\000\055\000\005\000\066\001\006\000\029\002\009\000\233\000\
\\035\000\044\000\060\000\043\000\061\000\042\000\062\000\041\000\
\\063\000\040\000\064\000\039\000\065\000\038\000\066\000\037\000\
\\067\000\036\000\070\000\035\000\072\000\034\000\074\000\033\000\
\\075\000\032\000\076\000\031\000\077\000\030\000\078\000\029\000\
\\080\000\028\000\081\000\027\000\082\000\026\000\083\000\025\000\
\\084\000\024\000\085\000\023\000\086\000\022\000\089\000\021\000\
\\091\000\020\000\094\000\019\000\097\000\018\000\099\000\017\000\000\000\
\\001\000\002\000\055\000\005\000\066\001\006\000\117\002\009\000\233\000\000\000\
\\001\000\002\000\096\000\000\000\
\\001\000\002\000\136\000\005\000\135\000\006\000\205\002\018\000\133\000\
\\020\000\132\000\021\000\131\000\022\000\130\000\047\000\129\000\
\\069\000\128\000\071\000\127\000\095\000\126\000\000\000\
\\001\000\002\000\136\000\005\000\135\000\006\000\110\001\018\000\133\000\
\\020\000\132\000\021\000\131\000\022\000\130\000\047\000\129\000\
\\069\000\128\000\071\000\127\000\095\000\126\000\000\000\
\\001\000\002\000\136\000\005\000\135\000\007\000\145\000\008\000\119\002\
\\009\000\242\000\016\000\241\000\018\000\133\000\020\000\132\000\
\\021\000\131\000\022\000\130\000\047\000\129\000\069\000\128\000\
\\071\000\127\000\095\000\126\000\000\000\
\\001\000\002\000\136\000\005\000\135\000\007\000\145\000\009\000\242\000\
\\016\000\241\000\018\000\133\000\020\000\132\000\021\000\131\000\
\\022\000\130\000\047\000\129\000\069\000\128\000\071\000\127\000\
\\095\000\126\000\000\000\
\\001\000\002\000\136\000\005\000\135\000\007\000\145\000\018\000\133\000\
\\020\000\132\000\021\000\131\000\022\000\130\000\047\000\129\000\
\\069\000\128\000\071\000\127\000\095\000\126\000\000\000\
\\001\000\002\000\136\000\005\000\135\000\007\000\120\001\018\000\133\000\
\\020\000\132\000\021\000\131\000\022\000\130\000\047\000\129\000\
\\069\000\128\000\071\000\127\000\095\000\126\000\000\000\
\\001\000\002\000\136\000\005\000\135\000\010\000\134\000\018\000\133\000\
\\020\000\132\000\021\000\131\000\022\000\130\000\047\000\129\000\
\\069\000\128\000\071\000\127\000\095\000\126\000\000\000\
\\001\000\002\000\136\000\005\000\135\000\010\000\074\001\018\000\133\000\
\\020\000\132\000\021\000\131\000\022\000\130\000\047\000\129\000\
\\069\000\128\000\071\000\127\000\095\000\126\000\000\000\
\\001\000\002\000\136\000\005\000\135\000\012\000\195\002\018\000\133\000\
\\020\000\132\000\021\000\131\000\022\000\130\000\047\000\129\000\
\\069\000\128\000\071\000\127\000\095\000\126\000\000\000\
\\001\000\002\000\136\000\005\000\135\000\012\000\014\001\018\000\133\000\
\\020\000\132\000\021\000\131\000\022\000\130\000\047\000\129\000\
\\069\000\128\000\071\000\127\000\095\000\126\000\000\000\
\\001\000\002\000\136\000\005\000\135\000\018\000\133\000\020\000\132\000\
\\021\000\131\000\022\000\130\000\035\000\044\000\047\000\129\000\
\\060\000\043\000\061\000\042\000\062\000\041\000\063\000\040\000\
\\064\000\039\000\065\000\038\000\066\000\037\000\067\000\036\000\
\\069\000\128\000\070\000\035\000\071\000\127\000\072\000\034\000\
\\076\000\031\000\077\000\030\000\078\000\029\000\095\000\126\000\000\000\
\\001\000\002\000\136\000\005\000\135\000\018\000\133\000\020\000\132\000\
\\021\000\131\000\022\000\130\000\047\000\129\000\069\000\128\000\
\\071\000\127\000\095\000\126\000\000\000\
\\001\000\002\000\136\000\005\000\218\000\018\000\133\000\020\000\132\000\
\\021\000\131\000\022\000\130\000\047\000\129\000\069\000\128\000\
\\071\000\127\000\095\000\126\000\000\000\
\\001\000\002\000\168\000\005\000\135\000\007\000\086\000\008\000\037\002\
\\012\000\167\000\018\000\133\000\020\000\132\000\021\000\131\000\
\\022\000\130\000\035\000\044\000\036\000\166\000\038\000\165\000\
\\039\000\164\000\040\000\163\000\041\000\162\000\042\000\161\000\
\\043\000\160\000\044\000\159\000\045\000\037\002\046\000\037\002\
\\047\000\129\000\060\000\043\000\061\000\042\000\062\000\041\000\
\\063\000\040\000\064\000\039\000\065\000\038\000\066\000\037\000\
\\067\000\036\000\069\000\128\000\070\000\035\000\071\000\127\000\
\\072\000\034\000\074\000\033\000\075\000\032\000\076\000\031\000\
\\077\000\030\000\078\000\029\000\080\000\028\000\081\000\027\000\
\\082\000\026\000\083\000\025\000\084\000\024\000\085\000\023\000\
\\086\000\022\000\087\000\158\000\088\000\157\000\089\000\021\000\
\\091\000\020\000\092\000\156\000\094\000\019\000\095\000\126\000\
\\097\000\018\000\098\000\155\000\099\000\017\000\000\000\
\\001\000\002\000\168\000\005\000\135\000\007\000\086\000\008\000\037\002\
\\012\000\167\000\018\000\133\000\020\000\132\000\021\000\131\000\
\\022\000\130\000\035\000\044\000\036\000\166\000\038\000\165\000\
\\039\000\164\000\040\000\163\000\041\000\162\000\042\000\161\000\
\\043\000\160\000\044\000\159\000\047\000\129\000\060\000\043\000\
\\061\000\042\000\062\000\041\000\063\000\040\000\064\000\039\000\
\\065\000\038\000\066\000\037\000\067\000\036\000\069\000\128\000\
\\070\000\035\000\071\000\127\000\072\000\034\000\074\000\033\000\
\\075\000\032\000\076\000\031\000\077\000\030\000\078\000\029\000\
\\080\000\028\000\081\000\027\000\082\000\026\000\083\000\025\000\
\\084\000\024\000\085\000\023\000\086\000\022\000\087\000\158\000\
\\088\000\157\000\089\000\021\000\091\000\020\000\092\000\156\000\
\\094\000\019\000\095\000\126\000\097\000\018\000\098\000\155\000\
\\099\000\017\000\000\000\
\\001\000\002\000\168\000\005\000\135\000\007\000\086\000\012\000\167\000\
\\018\000\133\000\020\000\132\000\021\000\131\000\022\000\130\000\
\\036\000\166\000\038\000\165\000\039\000\164\000\040\000\163\000\
\\041\000\162\000\042\000\161\000\043\000\160\000\044\000\159\000\
\\047\000\129\000\069\000\128\000\071\000\127\000\087\000\158\000\
\\088\000\157\000\092\000\156\000\093\000\041\002\095\000\126\000\
\\098\000\155\000\000\000\
\\001\000\002\000\168\000\005\000\135\000\007\000\086\000\012\000\167\000\
\\018\000\133\000\020\000\132\000\021\000\131\000\022\000\130\000\
\\036\000\166\000\038\000\165\000\039\000\164\000\040\000\163\000\
\\041\000\162\000\042\000\161\000\043\000\160\000\044\000\159\000\
\\047\000\129\000\069\000\128\000\071\000\127\000\087\000\158\000\
\\088\000\157\000\092\000\156\000\093\000\043\002\095\000\126\000\
\\098\000\155\000\000\000\
\\001\000\002\000\168\000\005\000\135\000\007\000\086\000\012\000\167\000\
\\018\000\133\000\020\000\132\000\021\000\131\000\022\000\130\000\
\\036\000\166\000\038\000\165\000\039\000\164\000\040\000\163\000\
\\041\000\162\000\042\000\161\000\043\000\160\000\044\000\159\000\
\\047\000\129\000\069\000\128\000\071\000\127\000\087\000\158\000\
\\088\000\157\000\092\000\156\000\095\000\126\000\098\000\155\000\000\000\
\\001\000\002\000\199\000\003\000\198\000\004\000\197\000\006\000\232\002\
\\008\000\232\002\010\000\232\002\011\000\232\002\012\000\232\002\
\\013\000\232\002\014\000\232\002\017\000\232\002\018\000\232\002\
\\021\000\232\002\048\000\232\002\049\000\232\002\050\000\232\002\
\\051\000\232\002\052\000\232\002\053\000\232\002\054\000\232\002\
\\055\000\232\002\056\000\232\002\057\000\232\002\058\000\232\002\
\\059\000\232\002\087\000\232\002\000\000\
\\001\000\002\000\199\000\003\000\198\000\004\000\197\000\006\000\233\002\
\\008\000\233\002\010\000\233\002\011\000\233\002\012\000\233\002\
\\013\000\233\002\014\000\233\002\017\000\233\002\018\000\233\002\
\\021\000\233\002\048\000\233\002\049\000\233\002\050\000\233\002\
\\051\000\233\002\052\000\233\002\053\000\233\002\054\000\233\002\
\\055\000\233\002\056\000\233\002\057\000\233\002\058\000\233\002\
\\059\000\233\002\087\000\233\002\000\000\
\\001\000\002\000\199\000\003\000\198\000\004\000\197\000\006\000\234\002\
\\008\000\234\002\010\000\234\002\011\000\234\002\012\000\234\002\
\\013\000\234\002\014\000\234\002\017\000\234\002\018\000\234\002\
\\021\000\234\002\048\000\234\002\049\000\234\002\050\000\234\002\
\\051\000\234\002\052\000\234\002\053\000\234\002\054\000\234\002\
\\055\000\234\002\056\000\234\002\057\000\234\002\058\000\234\002\
\\059\000\234\002\087\000\234\002\000\000\
\\001\000\002\000\100\001\005\000\099\001\006\000\197\002\069\000\128\000\
\\071\000\127\000\095\000\126\000\000\000\
\\001\000\002\000\100\001\005\000\099\001\012\000\190\002\035\000\044\000\
\\060\000\043\000\061\000\042\000\062\000\041\000\063\000\040\000\
\\064\000\039\000\065\000\038\000\066\000\037\000\067\000\036\000\
\\069\000\128\000\070\000\035\000\071\000\127\000\072\000\034\000\
\\074\000\033\000\075\000\032\000\076\000\031\000\077\000\030\000\
\\078\000\029\000\080\000\028\000\081\000\027\000\082\000\026\000\
\\083\000\025\000\084\000\024\000\085\000\023\000\086\000\022\000\
\\089\000\021\000\091\000\020\000\094\000\019\000\095\000\126\000\
\\097\000\018\000\099\000\017\000\000\000\
\\001\000\002\000\100\001\005\000\099\001\069\000\128\000\071\000\127\000\
\\095\000\126\000\000\000\
\\001\000\005\000\067\002\006\000\067\002\009\000\067\002\011\000\067\002\
\\069\000\067\002\091\000\067\002\097\000\067\002\000\000\
\\001\000\005\000\068\002\006\000\068\002\009\000\068\002\011\000\068\002\
\\069\000\068\002\091\000\068\002\097\000\068\002\000\000\
\\001\000\005\000\072\002\006\000\072\002\007\000\072\002\009\000\072\002\
\\011\000\072\002\012\000\072\002\013\000\072\002\015\000\072\002\
\\091\000\072\002\097\000\072\002\098\000\072\002\000\000\
\\001\000\005\000\073\002\006\000\073\002\007\000\073\002\009\000\073\002\
\\011\000\073\002\012\000\073\002\013\000\073\002\015\000\073\002\
\\090\000\068\001\091\000\073\002\097\000\073\002\098\000\073\002\000\000\
\\001\000\005\000\074\002\006\000\074\002\007\000\074\002\009\000\074\002\
\\011\000\074\002\012\000\074\002\013\000\074\002\015\000\074\002\
\\091\000\074\002\097\000\074\002\098\000\074\002\000\000\
\\001\000\005\000\075\002\006\000\075\002\007\000\075\002\009\000\075\002\
\\011\000\075\002\012\000\075\002\013\000\075\002\015\000\075\002\
\\091\000\075\002\097\000\075\002\098\000\075\002\000\000\
\\001\000\005\000\076\002\006\000\076\002\007\000\076\002\009\000\076\002\
\\011\000\076\002\012\000\076\002\013\000\076\002\015\000\076\002\
\\091\000\076\002\097\000\076\002\098\000\076\002\000\000\
\\001\000\005\000\077\002\006\000\077\002\007\000\077\002\009\000\077\002\
\\011\000\077\002\012\000\077\002\013\000\077\002\015\000\077\002\
\\091\000\077\002\097\000\077\002\098\000\077\002\000\000\
\\001\000\005\000\078\002\006\000\078\002\007\000\078\002\009\000\078\002\
\\011\000\078\002\012\000\078\002\013\000\078\002\015\000\078\002\
\\091\000\078\002\097\000\078\002\098\000\078\002\000\000\
\\001\000\005\000\079\002\006\000\079\002\007\000\079\002\009\000\079\002\
\\011\000\079\002\012\000\079\002\013\000\079\002\015\000\079\002\
\\091\000\079\002\097\000\079\002\098\000\079\002\000\000\
\\001\000\005\000\080\002\006\000\080\002\007\000\080\002\009\000\080\002\
\\011\000\080\002\012\000\080\002\013\000\080\002\015\000\080\002\
\\091\000\080\002\097\000\080\002\098\000\080\002\000\000\
\\001\000\005\000\081\002\006\000\081\002\007\000\081\002\009\000\081\002\
\\011\000\081\002\012\000\081\002\013\000\081\002\015\000\081\002\
\\091\000\081\002\097\000\081\002\098\000\081\002\000\000\
\\001\000\005\000\110\002\006\000\110\002\009\000\110\002\011\000\110\002\000\000\
\\001\000\005\000\111\002\006\000\111\002\009\000\111\002\011\000\111\002\000\000\
\\001\000\005\000\112\002\006\000\112\002\009\000\112\002\011\000\112\002\000\000\
\\001\000\005\000\113\002\006\000\113\002\009\000\113\002\011\000\113\002\000\000\
\\001\000\005\000\114\002\006\000\114\002\009\000\114\002\011\000\114\002\000\000\
\\001\000\005\000\115\002\006\000\115\002\009\000\115\002\011\000\115\002\000\000\
\\001\000\005\000\161\002\077\000\005\001\000\000\
\\001\000\005\000\162\002\000\000\
\\001\000\005\000\054\000\069\000\052\000\000\000\
\\001\000\005\000\054\000\069\000\052\000\091\000\020\000\097\000\018\000\000\000\
\\001\000\005\000\062\000\000\000\
\\001\000\005\000\081\000\006\000\069\002\007\000\069\002\009\000\080\000\
\\011\000\069\002\012\000\069\002\013\000\069\002\015\000\069\002\
\\091\000\020\000\097\000\018\000\098\000\079\000\000\000\
\\001\000\005\000\081\000\006\000\070\002\007\000\070\002\009\000\080\000\
\\011\000\070\002\012\000\070\002\013\000\070\002\015\000\070\002\
\\091\000\020\000\097\000\018\000\098\000\079\000\000\000\
\\001\000\005\000\081\000\006\000\071\002\007\000\071\002\009\000\080\000\
\\011\000\071\002\012\000\071\002\013\000\071\002\015\000\071\002\
\\091\000\020\000\097\000\018\000\098\000\079\000\000\000\
\\001\000\005\000\093\000\000\000\
\\001\000\005\000\108\000\000\000\
\\001\000\005\000\196\000\009\000\195\000\015\000\006\003\016\000\194\000\
\\023\000\006\003\024\000\006\003\025\000\006\003\026\000\006\003\
\\027\000\006\003\028\000\006\003\029\000\006\003\030\000\006\003\
\\031\000\006\003\032\000\006\003\033\000\006\003\034\000\006\003\
\\068\000\193\000\000\000\
\\001\000\005\000\234\000\006\000\107\002\009\000\233\000\011\000\107\002\
\\069\000\052\000\091\000\020\000\097\000\018\000\000\000\
\\001\000\005\000\009\001\000\000\
\\001\000\005\000\010\001\000\000\
\\001\000\005\000\018\001\000\000\
\\001\000\005\000\019\001\000\000\
\\001\000\005\000\023\001\006\000\000\002\011\000\000\002\000\000\
\\001\000\005\000\066\001\006\000\107\002\009\000\233\000\000\000\
\\001\000\005\000\071\001\006\000\108\002\009\000\070\001\011\000\108\002\000\000\
\\001\000\005\000\071\001\006\000\109\002\009\000\070\001\011\000\109\002\000\000\
\\001\000\005\000\087\001\000\000\
\\001\000\005\000\165\001\000\000\
\\001\000\005\000\193\001\095\000\192\000\000\000\
\\001\000\005\000\229\001\095\000\192\000\000\000\
\\001\000\006\000\253\001\069\000\176\000\076\000\175\000\000\000\
\\001\000\006\000\254\001\011\000\022\001\000\000\
\\001\000\006\000\255\001\000\000\
\\001\000\006\000\001\002\011\000\001\002\000\000\
\\001\000\006\000\002\002\011\000\002\002\000\000\
\\001\000\006\000\003\002\011\000\003\002\000\000\
\\001\000\006\000\004\002\011\000\148\001\000\000\
\\001\000\006\000\005\002\000\000\
\\001\000\006\000\029\002\035\000\044\000\060\000\043\000\061\000\042\000\
\\062\000\041\000\063\000\040\000\064\000\039\000\065\000\038\000\
\\066\000\037\000\067\000\036\000\070\000\035\000\072\000\034\000\
\\074\000\033\000\075\000\032\000\076\000\031\000\077\000\030\000\
\\078\000\029\000\080\000\028\000\081\000\027\000\082\000\026\000\
\\083\000\025\000\084\000\024\000\085\000\023\000\086\000\022\000\
\\089\000\021\000\091\000\020\000\094\000\019\000\097\000\018\000\
\\099\000\017\000\000\000\
\\001\000\006\000\030\002\000\000\
\\001\000\006\000\031\002\011\000\228\000\000\000\
\\001\000\006\000\032\002\000\000\
\\001\000\006\000\033\002\011\000\033\002\000\000\
\\001\000\006\000\034\002\011\000\034\002\000\000\
\\001\000\006\000\116\002\000\000\
\\001\000\006\000\163\002\000\000\
\\001\000\006\000\164\002\013\000\156\001\095\000\192\000\000\000\
\\001\000\006\000\165\002\000\000\
\\001\000\006\000\166\002\013\000\191\001\000\000\
\\001\000\006\000\167\002\000\000\
\\001\000\006\000\168\002\013\000\222\001\000\000\
\\001\000\006\000\169\002\000\000\
\\001\000\006\000\170\002\011\000\230\001\095\000\192\000\000\000\
\\001\000\006\000\171\002\000\000\
\\001\000\006\000\172\002\009\000\174\001\013\000\172\002\095\000\126\000\000\000\
\\001\000\006\000\173\002\013\000\173\002\000\000\
\\001\000\006\000\174\002\011\000\192\001\013\000\174\002\000\000\
\\001\000\006\000\175\002\013\000\175\002\000\000\
\\001\000\006\000\176\002\011\000\176\002\013\000\176\002\000\000\
\\001\000\006\000\177\002\011\000\177\002\013\000\177\002\000\000\
\\001\000\006\000\198\002\000\000\
\\001\000\006\000\199\002\011\000\206\001\087\000\205\001\000\000\
\\001\000\006\000\200\002\000\000\
\\001\000\006\000\201\002\000\000\
\\001\000\006\000\202\002\011\000\202\002\087\000\202\002\000\000\
\\001\000\006\000\203\002\011\000\203\002\087\000\203\002\000\000\
\\001\000\006\000\204\002\011\000\204\002\087\000\204\002\000\000\
\\001\000\006\000\206\002\000\000\
\\001\000\006\000\207\002\011\000\116\001\000\000\
\\001\000\006\000\208\002\000\000\
\\001\000\006\000\209\002\008\000\209\002\010\000\209\002\011\000\209\002\
\\012\000\209\002\013\000\209\002\014\000\214\000\048\000\213\000\
\\087\000\209\002\000\000\
\\001\000\006\000\210\002\008\000\210\002\010\000\210\002\011\000\210\002\
\\012\000\210\002\013\000\210\002\087\000\210\002\000\000\
\\001\000\006\000\211\002\008\000\211\002\010\000\211\002\011\000\211\002\
\\012\000\211\002\013\000\211\002\014\000\211\002\048\000\211\002\
\\049\000\215\000\087\000\211\002\000\000\
\\001\000\006\000\212\002\008\000\212\002\010\000\212\002\011\000\212\002\
\\012\000\212\002\013\000\212\002\014\000\212\002\048\000\212\002\
\\049\000\215\000\087\000\212\002\000\000\
\\001\000\006\000\213\002\008\000\213\002\010\000\213\002\011\000\213\002\
\\012\000\213\002\013\000\213\002\014\000\213\002\048\000\213\002\
\\049\000\213\002\050\000\212\000\087\000\213\002\000\000\
\\001\000\006\000\214\002\008\000\214\002\010\000\214\002\011\000\214\002\
\\012\000\214\002\013\000\214\002\014\000\214\002\048\000\214\002\
\\049\000\214\002\050\000\212\000\087\000\214\002\000\000\
\\001\000\006\000\215\002\008\000\215\002\010\000\215\002\011\000\215\002\
\\012\000\215\002\013\000\215\002\014\000\215\002\048\000\215\002\
\\049\000\215\002\050\000\215\002\051\000\211\000\087\000\215\002\000\000\
\\001\000\006\000\216\002\008\000\216\002\010\000\216\002\011\000\216\002\
\\012\000\216\002\013\000\216\002\014\000\216\002\048\000\216\002\
\\049\000\216\002\050\000\216\002\051\000\211\000\087\000\216\002\000\000\
\\001\000\006\000\217\002\008\000\217\002\010\000\217\002\011\000\217\002\
\\012\000\217\002\013\000\217\002\014\000\217\002\021\000\210\000\
\\048\000\217\002\049\000\217\002\050\000\217\002\051\000\217\002\
\\087\000\217\002\000\000\
\\001\000\006\000\218\002\008\000\218\002\010\000\218\002\011\000\218\002\
\\012\000\218\002\013\000\218\002\014\000\218\002\021\000\210\000\
\\048\000\218\002\049\000\218\002\050\000\218\002\051\000\218\002\
\\087\000\218\002\000\000\
\\001\000\006\000\219\002\008\000\219\002\010\000\219\002\011\000\219\002\
\\012\000\219\002\013\000\219\002\014\000\219\002\021\000\219\002\
\\048\000\219\002\049\000\219\002\050\000\219\002\051\000\219\002\
\\052\000\209\000\053\000\208\000\087\000\219\002\000\000\
\\001\000\006\000\220\002\008\000\220\002\010\000\220\002\011\000\220\002\
\\012\000\220\002\013\000\220\002\014\000\220\002\021\000\220\002\
\\048\000\220\002\049\000\220\002\050\000\220\002\051\000\220\002\
\\052\000\209\000\053\000\208\000\087\000\220\002\000\000\
\\001\000\006\000\221\002\008\000\221\002\010\000\221\002\011\000\221\002\
\\012\000\221\002\013\000\221\002\014\000\221\002\021\000\221\002\
\\048\000\221\002\049\000\221\002\050\000\221\002\051\000\221\002\
\\052\000\221\002\053\000\221\002\054\000\207\000\055\000\206\000\
\\056\000\205\000\057\000\204\000\087\000\221\002\000\000\
\\001\000\006\000\222\002\008\000\222\002\010\000\222\002\011\000\222\002\
\\012\000\222\002\013\000\222\002\014\000\222\002\021\000\222\002\
\\048\000\222\002\049\000\222\002\050\000\222\002\051\000\222\002\
\\052\000\222\002\053\000\222\002\054\000\207\000\055\000\206\000\
\\056\000\205\000\057\000\204\000\087\000\222\002\000\000\
\\001\000\006\000\223\002\008\000\223\002\010\000\223\002\011\000\223\002\
\\012\000\223\002\013\000\223\002\014\000\223\002\021\000\223\002\
\\048\000\223\002\049\000\223\002\050\000\223\002\051\000\223\002\
\\052\000\223\002\053\000\223\002\054\000\207\000\055\000\206\000\
\\056\000\205\000\057\000\204\000\087\000\223\002\000\000\
\\001\000\006\000\224\002\008\000\224\002\010\000\224\002\011\000\224\002\
\\012\000\224\002\013\000\224\002\014\000\224\002\021\000\224\002\
\\048\000\224\002\049\000\224\002\050\000\224\002\051\000\224\002\
\\052\000\224\002\053\000\224\002\054\000\224\002\055\000\224\002\
\\056\000\224\002\057\000\224\002\058\000\201\000\059\000\200\000\
\\087\000\224\002\000\000\
\\001\000\006\000\225\002\008\000\225\002\010\000\225\002\011\000\225\002\
\\012\000\225\002\013\000\225\002\014\000\225\002\021\000\225\002\
\\048\000\225\002\049\000\225\002\050\000\225\002\051\000\225\002\
\\052\000\225\002\053\000\225\002\054\000\225\002\055\000\225\002\
\\056\000\225\002\057\000\225\002\058\000\201\000\059\000\200\000\
\\087\000\225\002\000\000\
\\001\000\006\000\226\002\008\000\226\002\010\000\226\002\011\000\226\002\
\\012\000\226\002\013\000\226\002\014\000\226\002\021\000\226\002\
\\048\000\226\002\049\000\226\002\050\000\226\002\051\000\226\002\
\\052\000\226\002\053\000\226\002\054\000\226\002\055\000\226\002\
\\056\000\226\002\057\000\226\002\058\000\201\000\059\000\200\000\
\\087\000\226\002\000\000\
\\001\000\006\000\227\002\008\000\227\002\010\000\227\002\011\000\227\002\
\\012\000\227\002\013\000\227\002\014\000\227\002\021\000\227\002\
\\048\000\227\002\049\000\227\002\050\000\227\002\051\000\227\002\
\\052\000\227\002\053\000\227\002\054\000\227\002\055\000\227\002\
\\056\000\227\002\057\000\227\002\058\000\201\000\059\000\200\000\
\\087\000\227\002\000\000\
\\001\000\006\000\228\002\008\000\228\002\010\000\228\002\011\000\228\002\
\\012\000\228\002\013\000\228\002\014\000\228\002\021\000\228\002\
\\048\000\228\002\049\000\228\002\050\000\228\002\051\000\228\002\
\\052\000\228\002\053\000\228\002\054\000\228\002\055\000\228\002\
\\056\000\228\002\057\000\228\002\058\000\201\000\059\000\200\000\
\\087\000\228\002\000\000\
\\001\000\006\000\229\002\008\000\229\002\010\000\229\002\011\000\229\002\
\\012\000\229\002\013\000\229\002\014\000\229\002\017\000\203\000\
\\018\000\202\000\021\000\229\002\048\000\229\002\049\000\229\002\
\\050\000\229\002\051\000\229\002\052\000\229\002\053\000\229\002\
\\054\000\229\002\055\000\229\002\056\000\229\002\057\000\229\002\
\\058\000\229\002\059\000\229\002\087\000\229\002\000\000\
\\001\000\006\000\230\002\008\000\230\002\010\000\230\002\011\000\230\002\
\\012\000\230\002\013\000\230\002\014\000\230\002\017\000\203\000\
\\018\000\202\000\021\000\230\002\048\000\230\002\049\000\230\002\
\\050\000\230\002\051\000\230\002\052\000\230\002\053\000\230\002\
\\054\000\230\002\055\000\230\002\056\000\230\002\057\000\230\002\
\\058\000\230\002\059\000\230\002\087\000\230\002\000\000\
\\001\000\006\000\231\002\008\000\231\002\010\000\231\002\011\000\231\002\
\\012\000\231\002\013\000\231\002\014\000\231\002\017\000\203\000\
\\018\000\202\000\021\000\231\002\048\000\231\002\049\000\231\002\
\\050\000\231\002\051\000\231\002\052\000\231\002\053\000\231\002\
\\054\000\231\002\055\000\231\002\056\000\231\002\057\000\231\002\
\\058\000\231\002\059\000\231\002\087\000\231\002\000\000\
\\001\000\006\000\170\000\000\000\
\\001\000\006\000\227\000\000\000\
\\001\000\006\000\021\001\000\000\
\\001\000\006\000\035\001\095\000\192\000\000\000\
\\001\000\006\000\062\001\000\000\
\\001\000\006\000\063\001\000\000\
\\001\000\006\000\106\001\000\000\
\\001\000\006\000\115\001\000\000\
\\001\000\006\000\118\001\000\000\
\\001\000\006\000\125\001\000\000\
\\001\000\006\000\126\001\000\000\
\\001\000\006\000\135\001\000\000\
\\001\000\006\000\145\001\000\000\
\\001\000\006\000\146\001\000\000\
\\001\000\006\000\147\001\000\000\
\\001\000\006\000\154\001\000\000\
\\001\000\006\000\157\001\000\000\
\\001\000\006\000\164\001\000\000\
\\001\000\006\000\207\001\000\000\
\\001\000\006\000\208\001\000\000\
\\001\000\006\000\223\001\000\000\
\\001\000\006\000\233\001\000\000\
\\001\000\007\000\074\000\069\000\073\000\070\000\072\000\000\000\
\\001\000\007\000\076\000\069\000\073\000\070\000\072\000\000\000\
\\001\000\007\000\086\000\011\000\063\002\012\000\063\002\015\000\085\000\000\000\
\\001\000\007\000\120\001\000\000\
\\001\000\007\000\160\001\000\000\
\\001\000\008\000\038\002\045\000\038\002\046\000\038\002\000\000\
\\001\000\008\000\045\002\035\000\044\000\060\000\043\000\061\000\042\000\
\\062\000\041\000\063\000\040\000\064\000\039\000\065\000\038\000\
\\066\000\037\000\067\000\036\000\070\000\035\000\072\000\034\000\
\\076\000\031\000\077\000\030\000\078\000\029\000\000\000\
\\001\000\008\000\046\002\000\000\
\\001\000\008\000\056\002\035\000\056\002\060\000\056\002\061\000\056\002\
\\062\000\056\002\063\000\056\002\064\000\056\002\065\000\056\002\
\\066\000\056\002\067\000\056\002\070\000\056\002\072\000\056\002\
\\076\000\056\002\077\000\056\002\078\000\056\002\000\000\
\\001\000\008\000\103\002\011\000\103\002\000\000\
\\001\000\008\000\104\002\011\000\104\002\000\000\
\\001\000\008\000\105\002\011\000\105\002\015\000\190\000\000\000\
\\001\000\008\000\106\002\011\000\106\002\000\000\
\\001\000\008\000\118\002\011\000\080\001\000\000\
\\001\000\008\000\120\002\000\000\
\\001\000\008\000\121\002\011\000\121\002\000\000\
\\001\000\008\000\122\002\011\000\122\002\000\000\
\\001\000\008\000\128\002\011\000\128\002\012\000\128\002\000\000\
\\001\000\008\000\129\002\011\000\129\002\012\000\129\002\000\000\
\\001\000\008\000\181\002\045\000\182\001\046\000\181\001\000\000\
\\001\000\008\000\182\002\000\000\
\\001\000\008\000\183\002\045\000\183\002\046\000\183\002\000\000\
\\001\000\008\000\182\000\000\000\
\\001\000\008\000\189\000\011\000\188\000\000\000\
\\001\000\008\000\003\001\000\000\
\\001\000\008\000\026\001\000\000\
\\001\000\008\000\031\001\011\000\030\001\000\000\
\\001\000\008\000\033\001\069\000\107\000\000\000\
\\001\000\008\000\081\001\000\000\
\\001\000\008\000\113\001\069\000\107\000\000\000\
\\001\000\008\000\169\001\000\000\
\\001\000\008\000\199\001\000\000\
\\001\000\009\000\126\002\015\000\126\002\016\000\126\002\000\000\
\\001\000\009\000\127\002\015\000\127\002\016\000\127\002\000\000\
\\001\000\009\000\066\000\069\000\065\000\085\000\015\002\086\000\015\002\
\\089\000\015\002\094\000\015\002\096\000\015\002\000\000\
\\001\000\009\000\066\000\069\000\065\000\096\000\015\002\000\000\
\\001\000\009\000\242\000\015\000\124\002\016\000\241\000\000\000\
\\001\000\009\000\174\001\095\000\126\000\000\000\
\\001\000\010\000\177\000\000\000\
\\001\000\010\000\216\000\000\000\
\\001\000\010\000\114\001\000\000\
\\001\000\010\000\124\001\000\000\
\\001\000\010\000\128\001\000\000\
\\001\000\010\000\153\001\000\000\
\\001\000\010\000\213\001\000\000\
\\001\000\011\000\059\002\012\000\059\002\013\000\029\001\000\000\
\\001\000\011\000\060\002\012\000\060\002\000\000\
\\001\000\011\000\063\002\012\000\063\002\015\000\085\000\000\000\
\\001\000\011\000\064\002\012\000\064\002\000\000\
\\001\000\011\000\194\002\012\000\194\002\000\000\
\\001\000\011\000\083\000\012\000\061\002\000\000\
\\001\000\011\000\028\001\012\000\057\002\000\000\
\\001\000\011\000\137\001\012\000\192\002\000\000\
\\001\000\012\000\058\002\000\000\
\\001\000\012\000\062\002\000\000\
\\001\000\012\000\191\002\000\000\
\\001\000\012\000\193\002\000\000\
\\001\000\012\000\196\002\000\000\
\\001\000\012\000\045\000\035\000\044\000\060\000\043\000\061\000\042\000\
\\062\000\041\000\063\000\040\000\064\000\039\000\065\000\038\000\
\\066\000\037\000\067\000\036\000\070\000\035\000\072\000\034\000\
\\074\000\033\000\075\000\032\000\076\000\031\000\077\000\030\000\
\\078\000\029\000\080\000\028\000\081\000\027\000\082\000\026\000\
\\083\000\025\000\084\000\024\000\085\000\023\000\086\000\022\000\
\\089\000\021\000\091\000\020\000\094\000\019\000\097\000\018\000\
\\099\000\017\000\000\000\
\\001\000\012\000\082\000\000\000\
\\001\000\012\000\243\000\000\000\
\\001\000\012\000\011\001\000\000\
\\001\000\012\000\012\001\000\000\
\\001\000\012\000\027\001\000\000\
\\001\000\012\000\085\001\000\000\
\\001\000\012\000\086\001\000\000\
\\001\000\012\000\101\001\000\000\
\\001\000\012\000\129\001\000\000\
\\001\000\012\000\138\001\000\000\
\\001\000\012\000\163\001\000\000\
\\001\000\012\000\175\001\000\000\
\\001\000\012\000\220\001\000\000\
\\001\000\013\000\097\000\000\000\
\\001\000\013\000\117\001\000\000\
\\001\000\013\000\200\001\000\000\
\\001\000\013\000\215\001\000\000\
\\001\000\015\000\125\002\000\000\
\\001\000\015\000\007\003\023\000\007\003\024\000\007\003\025\000\007\003\
\\026\000\007\003\027\000\007\003\028\000\007\003\029\000\007\003\
\\030\000\007\003\031\000\007\003\032\000\007\003\033\000\007\003\
\\034\000\007\003\000\000\
\\001\000\015\000\001\001\023\000\000\001\024\000\255\000\025\000\254\000\
\\026\000\253\000\027\000\252\000\028\000\251\000\029\000\250\000\
\\030\000\249\000\031\000\248\000\032\000\247\000\033\000\246\000\
\\034\000\245\000\000\000\
\\001\000\015\000\001\001\023\000\204\001\024\000\203\001\025\000\254\000\
\\026\000\253\000\027\000\252\000\028\000\251\000\029\000\250\000\
\\030\000\249\000\031\000\248\000\032\000\247\000\033\000\246\000\
\\034\000\245\000\000\000\
\\001\000\015\000\078\001\000\000\
\\001\000\015\000\136\001\000\000\
\\001\000\035\000\044\000\060\000\043\000\061\000\042\000\062\000\041\000\
\\063\000\040\000\064\000\039\000\065\000\038\000\066\000\037\000\
\\067\000\036\000\070\000\035\000\072\000\034\000\074\000\033\000\
\\075\000\032\000\076\000\031\000\077\000\030\000\078\000\029\000\
\\080\000\028\000\081\000\027\000\082\000\026\000\083\000\025\000\
\\084\000\024\000\085\000\023\000\086\000\022\000\089\000\021\000\
\\091\000\020\000\094\000\019\000\097\000\018\000\099\000\017\000\000\000\
\\001\000\035\000\044\000\060\000\043\000\061\000\042\000\062\000\041\000\
\\063\000\040\000\064\000\039\000\065\000\038\000\066\000\037\000\
\\067\000\036\000\070\000\035\000\072\000\034\000\076\000\031\000\
\\077\000\030\000\078\000\029\000\000\000\
\\001\000\038\000\143\001\000\000\
\\001\000\069\000\063\000\000\000\
\\001\000\069\000\070\000\000\000\
\\001\000\069\000\070\000\085\000\012\002\086\000\012\002\089\000\012\002\
\\094\000\012\002\096\000\012\002\000\000\
\\001\000\069\000\107\000\000\000\
\\001\000\069\000\036\001\000\000\
\\001\000\069\000\037\001\000\000\
\\001\000\069\000\082\001\000\000\
\\001\000\069\000\194\001\000\000\
\\001\000\085\000\008\002\086\000\008\002\089\000\008\002\094\000\008\002\
\\096\000\008\002\000\000\
\\001\000\085\000\009\002\086\000\009\002\089\000\009\002\094\000\009\002\
\\096\000\009\002\000\000\
\\001\000\085\000\010\002\086\000\010\002\089\000\010\002\094\000\010\002\
\\096\000\010\002\000\000\
\\001\000\085\000\011\002\086\000\011\002\089\000\011\002\094\000\011\002\
\\096\000\011\002\000\000\
\\001\000\085\000\013\002\086\000\013\002\089\000\013\002\094\000\013\002\
\\096\000\013\002\000\000\
\\001\000\085\000\014\002\086\000\014\002\089\000\014\002\094\000\014\002\
\\096\000\014\002\000\000\
\\001\000\085\000\016\002\086\000\016\002\089\000\016\002\094\000\016\002\
\\096\000\016\002\000\000\
\\001\000\085\000\017\002\086\000\017\002\089\000\017\002\094\000\017\002\
\\096\000\017\002\000\000\
\\001\000\085\000\023\000\086\000\022\000\089\000\021\000\094\000\019\000\
\\096\000\006\002\000\000\
\\001\000\093\000\042\002\000\000\
\\001\000\093\000\044\002\000\000\
\\001\000\093\000\158\001\000\000\
\\001\000\095\000\068\000\000\000\
\\001\000\095\000\126\000\000\000\
\\001\000\095\000\178\000\000\000\
\\001\000\095\000\006\001\000\000\
\\001\000\095\000\007\001\000\000\
\\001\000\095\000\008\001\000\000\
\\001\000\095\000\103\001\000\000\
\\001\000\095\000\176\001\000\000\
\\001\000\095\000\217\001\000\000\
\\001\000\096\000\007\002\000\000\
\\001\000\096\000\056\000\000\000\
\\001\000\096\000\094\000\000\000\
\\001\000\096\000\088\001\000\000\
\\001\000\096\000\089\001\000\000\
\\001\000\096\000\090\001\000\000\
\\001\000\096\000\144\001\000\000\
\\001\000\096\000\152\001\000\000\
\\001\000\096\000\195\001\000\000\
\\001\000\096\000\225\001\000\000\
\"
val actionRowNumbers =
"\095\001\020\000\055\000\025\000\
\\004\000\005\000\135\000\152\001\
\\138\001\029\000\027\000\056\000\
\\023\000\002\000\001\000\014\000\
\\188\000\133\001\122\001\071\001\
\\142\001\123\001\015\000\016\000\
\\018\000\013\000\017\000\039\000\
\\038\000\037\000\012\000\011\000\
\\037\001\057\000\051\000\053\000\
\\052\000\049\000\050\000\048\000\
\\054\000\047\000\038\001\006\000\
\\026\000\191\000\096\001\087\001\
\\039\001\187\000\170\000\007\000\
\\136\000\133\000\019\000\151\001\
\\030\000\028\000\024\000\003\000\
\\192\000\153\001\130\001\071\001\
\\141\000\132\001\135\001\131\001\
\\109\001\044\000\043\000\042\000\
\\120\001\062\000\125\001\175\000\
\\176\000\193\000\148\000\216\000\
\\008\000\136\000\009\000\146\000\
\\156\000\186\000\189\000\015\001\
\\166\000\134\000\040\000\208\000\
\\022\000\136\001\075\001\144\001\
\\120\001\033\000\043\001\059\001\
\\136\000\035\000\125\001\046\001\
\\060\001\048\001\143\001\129\000\
\\127\000\120\000\110\000\104\000\
\\108\000\160\000\007\001\012\001\
\\004\001\002\001\000\001\254\000\
\\252\000\248\000\250\000\076\001\
\\131\000\132\000\126\000\154\000\
\\153\000\153\000\153\000\153\000\
\\172\000\152\000\153\000\217\000\
\\016\001\218\000\138\000\091\001\
\\084\001\054\001\085\001\145\000\
\\111\000\097\001\115\001\032\000\
\\090\000\155\000\061\001\031\000\
\\135\000\184\000\145\001\146\001\
\\147\001\196\000\197\000\098\001\
\\099\001\151\000\096\000\198\000\
\\199\000\086\000\153\000\190\000\
\\173\000\167\000\041\000\017\001\
\\209\000\211\000\200\000\071\001\
\\124\001\062\001\034\000\044\001\
\\046\000\100\001\088\001\082\001\
\\036\000\063\001\064\001\058\000\
\\153\000\018\001\130\000\126\001\
\\127\001\153\000\142\000\153\000\
\\153\000\153\000\153\000\153\000\
\\153\000\153\000\153\000\153\000\
\\153\000\153\000\153\000\153\000\
\\153\000\153\000\153\000\153\000\
\\153\000\153\000\171\000\118\000\
\\152\000\114\000\115\000\113\000\
\\112\000\019\001\020\001\140\000\
\\116\000\169\000\119\001\203\000\
\\221\000\220\000\195\000\149\000\
\\137\000\073\001\117\001\146\000\
\\053\001\050\001\065\001\128\001\
\\153\000\076\000\153\000\074\000\
\\073\000\069\000\072\000\071\000\
\\070\000\067\000\068\000\066\000\
\\065\000\101\001\102\001\064\000\
\\042\001\010\000\204\000\185\000\
\\154\001\155\001\156\001\153\000\
\\164\000\083\000\082\000\103\001\
\\081\000\159\000\097\000\148\001\
\\153\000\153\000\117\000\021\001\
\\208\000\143\000\137\001\134\001\
\\045\000\045\001\136\000\153\000\
\\066\001\059\000\047\001\060\000\
\\049\001\177\000\124\000\123\000\
\\077\001\022\001\245\000\246\000\
\\107\000\106\000\105\000\014\001\
\\013\001\162\000\161\000\009\001\
\\008\001\011\001\010\001\006\001\
\\005\001\003\001\001\001\255\000\
\\251\000\110\001\253\000\023\001\
\\128\000\147\000\222\000\201\000\
\\139\000\174\000\072\001\219\000\
\\153\000\216\000\202\000\078\001\
\\180\000\024\001\025\001\113\001\
\\063\000\052\001\144\000\055\001\
\\070\001\079\001\104\001\088\000\
\\087\000\143\001\157\000\092\000\
\\091\000\026\001\194\000\118\001\
\\089\001\092\001\105\001\150\000\
\\103\000\152\000\153\000\080\000\
\\121\001\157\001\027\001\028\001\
\\021\000\210\000\029\001\214\000\
\\212\000\090\001\083\001\061\000\
\\121\000\122\000\153\000\153\000\
\\119\000\109\000\145\000\158\001\
\\080\001\030\001\179\000\178\000\
\\182\000\051\001\069\001\075\000\
\\224\000\031\001\139\001\141\001\
\\158\000\041\001\153\000\165\000\
\\102\000\094\001\106\001\032\001\
\\114\001\205\000\095\000\096\000\
\\159\000\213\000\153\000\247\000\
\\249\000\067\001\168\000\181\000\
\\183\000\223\000\232\000\107\001\
\\149\001\140\001\056\001\086\001\
\\093\001\163\000\040\001\153\000\
\\159\000\084\000\215\000\125\000\
\\233\000\226\000\234\000\206\000\
\\129\001\094\000\159\001\098\000\
\\159\000\056\001\068\001\111\001\
\\153\000\116\001\239\000\238\000\
\\033\001\034\001\077\000\159\000\
\\225\000\232\000\074\001\153\000\
\\081\001\093\000\099\000\155\000\
\\057\001\089\000\101\000\112\001\
\\153\000\244\000\243\000\150\001\
\\165\000\096\000\108\001\085\000\
\\228\000\235\000\035\001\143\001\
\\058\001\100\000\242\000\160\001\
\\241\000\159\000\078\000\227\000\
\\143\001\236\000\207\000\240\000\
\\079\000\229\000\230\000\153\000\
\\143\001\036\001\231\000\237\000\
\\000\000"
val gotoT =
"\
\\001\000\232\001\002\000\014\000\003\000\013\000\006\000\012\000\
\\007\000\011\000\010\000\010\000\012\000\009\000\013\000\008\000\
\\014\000\007\000\020\000\006\000\028\000\005\000\040\000\004\000\
\\068\000\003\000\069\000\002\000\092\000\001\000\000\000\
\\000\000\
\\000\000\
\\006\000\012\000\007\000\011\000\010\000\010\000\012\000\009\000\
\\013\000\008\000\014\000\007\000\020\000\044\000\068\000\003\000\
\\069\000\002\000\092\000\001\000\000\000\
\\000\000\
\\000\000\
\\058\000\049\000\059\000\048\000\064\000\047\000\065\000\046\000\
\\066\000\045\000\000\000\
\\000\000\
\\013\000\008\000\014\000\055\000\000\000\
\\006\000\012\000\007\000\011\000\010\000\010\000\012\000\009\000\
\\013\000\008\000\014\000\007\000\020\000\056\000\068\000\003\000\
\\069\000\002\000\092\000\001\000\000\000\
\\006\000\012\000\007\000\011\000\010\000\010\000\012\000\009\000\
\\013\000\008\000\014\000\007\000\020\000\057\000\068\000\003\000\
\\069\000\002\000\092\000\001\000\000\000\
\\000\000\
\\006\000\012\000\007\000\011\000\010\000\010\000\012\000\009\000\
\\013\000\008\000\014\000\007\000\020\000\058\000\068\000\003\000\
\\069\000\002\000\092\000\001\000\000\000\
\\002\000\059\000\003\000\013\000\006\000\012\000\007\000\011\000\
\\010\000\010\000\012\000\009\000\013\000\008\000\014\000\007\000\
\\020\000\006\000\028\000\005\000\040\000\004\000\068\000\003\000\
\\069\000\002\000\092\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\090\000\062\000\000\000\
\\016\000\065\000\000\000\
\\015\000\067\000\000\000\
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
\\070\000\069\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\070\000\073\000\000\000\
\\000\000\
\\000\000\
\\067\000\076\000\092\000\075\000\000\000\
\\000\000\
\\000\000\
\\041\000\082\000\000\000\
\\066\000\086\000\092\000\085\000\000\000\
\\000\000\
\\000\000\
\\058\000\049\000\059\000\087\000\066\000\045\000\000\000\
\\010\000\090\000\011\000\089\000\058\000\088\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\090\000\093\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\007\000\011\000\010\000\101\000\021\000\100\000\029\000\099\000\
\\030\000\098\000\068\000\097\000\069\000\002\000\000\000\
\\000\000\
\\008\000\104\000\009\000\103\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\072\000\123\000\075\000\122\000\076\000\121\000\077\000\120\000\
\\078\000\119\000\079\000\118\000\080\000\117\000\081\000\116\000\
\\082\000\115\000\083\000\114\000\084\000\113\000\085\000\112\000\
\\086\000\111\000\087\000\110\000\088\000\109\000\089\000\108\000\
\\099\000\107\000\000\000\
\\006\000\012\000\007\000\011\000\010\000\010\000\012\000\009\000\
\\013\000\008\000\014\000\007\000\020\000\138\000\037\000\137\000\
\\038\000\136\000\039\000\135\000\068\000\003\000\069\000\002\000\
\\092\000\001\000\000\000\
\\000\000\
\\058\000\049\000\059\000\140\000\064\000\047\000\065\000\139\000\
\\066\000\045\000\000\000\
\\000\000\
\\024\000\142\000\072\000\141\000\075\000\122\000\076\000\121\000\
\\077\000\120\000\078\000\119\000\079\000\118\000\080\000\117\000\
\\081\000\116\000\082\000\115\000\083\000\114\000\084\000\113\000\
\\085\000\112\000\086\000\111\000\087\000\110\000\088\000\109\000\
\\089\000\108\000\099\000\107\000\000\000\
\\006\000\012\000\007\000\011\000\010\000\010\000\012\000\009\000\
\\013\000\008\000\014\000\007\000\020\000\152\000\028\000\151\000\
\\035\000\150\000\036\000\149\000\041\000\148\000\042\000\147\000\
\\068\000\003\000\069\000\002\000\071\000\146\000\072\000\145\000\
\\075\000\122\000\076\000\121\000\077\000\120\000\078\000\119\000\
\\079\000\118\000\080\000\117\000\081\000\116\000\082\000\115\000\
\\083\000\114\000\084\000\113\000\085\000\112\000\086\000\111\000\
\\087\000\144\000\088\000\109\000\089\000\108\000\092\000\001\000\
\\099\000\107\000\000\000\
\\066\000\167\000\000\000\
\\067\000\076\000\092\000\075\000\000\000\
\\000\000\
\\000\000\
\\058\000\169\000\000\000\
\\010\000\090\000\011\000\170\000\000\000\
\\091\000\172\000\093\000\171\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\007\000\011\000\010\000\101\000\021\000\100\000\029\000\177\000\
\\030\000\098\000\068\000\097\000\069\000\002\000\000\000\
\\007\000\011\000\010\000\101\000\021\000\178\000\068\000\097\000\
\\069\000\002\000\000\000\
\\007\000\011\000\010\000\101\000\021\000\100\000\029\000\179\000\
\\030\000\098\000\068\000\097\000\069\000\002\000\000\000\
\\000\000\
\\058\000\049\000\059\000\183\000\062\000\182\000\063\000\181\000\
\\066\000\045\000\000\000\
\\007\000\011\000\010\000\101\000\021\000\184\000\068\000\097\000\
\\069\000\002\000\000\000\
\\008\000\185\000\009\000\103\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\099\000\189\000\000\000\
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
\\085\000\215\000\087\000\110\000\088\000\109\000\089\000\108\000\
\\099\000\107\000\000\000\
\\085\000\112\000\086\000\217\000\087\000\110\000\088\000\109\000\
\\089\000\108\000\099\000\107\000\000\000\
\\085\000\112\000\086\000\218\000\087\000\110\000\088\000\109\000\
\\089\000\108\000\099\000\107\000\000\000\
\\085\000\112\000\086\000\219\000\087\000\110\000\088\000\109\000\
\\089\000\108\000\099\000\107\000\000\000\
\\085\000\112\000\086\000\220\000\087\000\110\000\088\000\109\000\
\\089\000\108\000\099\000\107\000\000\000\
\\000\000\
\\007\000\011\000\010\000\101\000\021\000\223\000\034\000\222\000\
\\068\000\097\000\069\000\002\000\072\000\221\000\075\000\122\000\
\\076\000\121\000\077\000\120\000\078\000\119\000\079\000\118\000\
\\080\000\117\000\081\000\116\000\082\000\115\000\083\000\114\000\
\\084\000\113\000\085\000\112\000\086\000\111\000\087\000\110\000\
\\088\000\109\000\089\000\108\000\099\000\107\000\000\000\
\\085\000\112\000\086\000\224\000\087\000\110\000\088\000\109\000\
\\089\000\108\000\099\000\107\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\058\000\230\000\059\000\229\000\060\000\228\000\061\000\227\000\
\\066\000\045\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\022\000\238\000\023\000\237\000\024\000\236\000\025\000\235\000\
\\026\000\234\000\027\000\233\000\072\000\141\000\075\000\122\000\
\\076\000\121\000\077\000\120\000\078\000\119\000\079\000\118\000\
\\080\000\117\000\081\000\116\000\082\000\115\000\083\000\114\000\
\\084\000\113\000\085\000\112\000\086\000\111\000\087\000\110\000\
\\088\000\109\000\089\000\108\000\099\000\107\000\000\000\
\\000\000\
\\000\000\
\\057\000\242\000\000\000\
\\000\000\
\\000\000\
\\006\000\012\000\007\000\011\000\010\000\010\000\012\000\009\000\
\\013\000\008\000\014\000\007\000\020\000\152\000\028\000\151\000\
\\035\000\000\001\036\000\149\000\041\000\148\000\042\000\147\000\
\\068\000\003\000\069\000\002\000\071\000\146\000\072\000\145\000\
\\075\000\122\000\076\000\121\000\077\000\120\000\078\000\119\000\
\\079\000\118\000\080\000\117\000\081\000\116\000\082\000\115\000\
\\083\000\114\000\084\000\113\000\085\000\112\000\086\000\111\000\
\\087\000\144\000\088\000\109\000\089\000\108\000\092\000\001\000\
\\099\000\107\000\000\000\
\\000\000\
\\000\000\
\\058\000\049\000\059\000\140\000\064\000\047\000\065\000\046\000\
\\066\000\045\000\000\000\
\\005\000\002\001\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\072\000\011\001\075\000\122\000\076\000\121\000\077\000\120\000\
\\078\000\119\000\079\000\118\000\080\000\117\000\081\000\116\000\
\\082\000\115\000\083\000\114\000\084\000\113\000\085\000\112\000\
\\086\000\111\000\087\000\110\000\088\000\109\000\089\000\108\000\
\\099\000\107\000\000\000\
\\018\000\014\001\019\000\013\001\000\000\
\\000\000\
\\000\000\
\\000\000\
\\085\000\112\000\086\000\018\001\087\000\110\000\088\000\109\000\
\\089\000\108\000\099\000\107\000\000\000\
\\067\000\076\000\092\000\075\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\090\000\022\001\000\000\
\\015\000\023\001\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\009\000\030\001\000\000\
\\000\000\
\\072\000\032\001\075\000\122\000\076\000\121\000\077\000\120\000\
\\078\000\119\000\079\000\118\000\080\000\117\000\081\000\116\000\
\\082\000\115\000\083\000\114\000\084\000\113\000\085\000\112\000\
\\086\000\111\000\087\000\110\000\088\000\109\000\089\000\108\000\
\\099\000\107\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\072\000\036\001\075\000\122\000\076\000\121\000\077\000\120\000\
\\078\000\119\000\079\000\118\000\080\000\117\000\081\000\116\000\
\\082\000\115\000\083\000\114\000\084\000\113\000\085\000\112\000\
\\086\000\111\000\087\000\110\000\088\000\109\000\089\000\108\000\
\\099\000\107\000\000\000\
\\072\000\039\001\073\000\038\001\074\000\037\001\075\000\122\000\
\\076\000\121\000\077\000\120\000\078\000\119\000\079\000\118\000\
\\080\000\117\000\081\000\116\000\082\000\115\000\083\000\114\000\
\\084\000\113\000\085\000\112\000\086\000\111\000\087\000\110\000\
\\088\000\109\000\089\000\108\000\099\000\107\000\000\000\
\\085\000\112\000\086\000\040\001\087\000\110\000\088\000\109\000\
\\089\000\108\000\099\000\107\000\000\000\
\\085\000\112\000\086\000\041\001\087\000\110\000\088\000\109\000\
\\089\000\108\000\099\000\107\000\000\000\
\\085\000\112\000\086\000\042\001\087\000\110\000\088\000\109\000\
\\089\000\108\000\099\000\107\000\000\000\
\\082\000\043\001\084\000\113\000\085\000\112\000\086\000\111\000\
\\087\000\110\000\088\000\109\000\089\000\108\000\099\000\107\000\000\000\
\\082\000\044\001\084\000\113\000\085\000\112\000\086\000\111\000\
\\087\000\110\000\088\000\109\000\089\000\108\000\099\000\107\000\000\000\
\\084\000\045\001\085\000\112\000\086\000\111\000\087\000\110\000\
\\088\000\109\000\089\000\108\000\099\000\107\000\000\000\
\\084\000\046\001\085\000\112\000\086\000\111\000\087\000\110\000\
\\088\000\109\000\089\000\108\000\099\000\107\000\000\000\
\\082\000\115\000\083\000\047\001\084\000\113\000\085\000\112\000\
\\086\000\111\000\087\000\110\000\088\000\109\000\089\000\108\000\
\\099\000\107\000\000\000\
\\082\000\115\000\083\000\048\001\084\000\113\000\085\000\112\000\
\\086\000\111\000\087\000\110\000\088\000\109\000\089\000\108\000\
\\099\000\107\000\000\000\
\\082\000\115\000\083\000\049\001\084\000\113\000\085\000\112\000\
\\086\000\111\000\087\000\110\000\088\000\109\000\089\000\108\000\
\\099\000\107\000\000\000\
\\082\000\115\000\083\000\050\001\084\000\113\000\085\000\112\000\
\\086\000\111\000\087\000\110\000\088\000\109\000\089\000\108\000\
\\099\000\107\000\000\000\
\\081\000\051\001\082\000\115\000\083\000\114\000\084\000\113\000\
\\085\000\112\000\086\000\111\000\087\000\110\000\088\000\109\000\
\\089\000\108\000\099\000\107\000\000\000\
\\081\000\052\001\082\000\115\000\083\000\114\000\084\000\113\000\
\\085\000\112\000\086\000\111\000\087\000\110\000\088\000\109\000\
\\089\000\108\000\099\000\107\000\000\000\
\\080\000\053\001\081\000\116\000\082\000\115\000\083\000\114\000\
\\084\000\113\000\085\000\112\000\086\000\111\000\087\000\110\000\
\\088\000\109\000\089\000\108\000\099\000\107\000\000\000\
\\079\000\054\001\080\000\117\000\081\000\116\000\082\000\115\000\
\\083\000\114\000\084\000\113\000\085\000\112\000\086\000\111\000\
\\087\000\110\000\088\000\109\000\089\000\108\000\099\000\107\000\000\000\
\\078\000\055\001\079\000\118\000\080\000\117\000\081\000\116\000\
\\082\000\115\000\083\000\114\000\084\000\113\000\085\000\112\000\
\\086\000\111\000\087\000\110\000\088\000\109\000\089\000\108\000\
\\099\000\107\000\000\000\
\\075\000\056\001\077\000\120\000\078\000\119\000\079\000\118\000\
\\080\000\117\000\081\000\116\000\082\000\115\000\083\000\114\000\
\\084\000\113\000\085\000\112\000\086\000\111\000\087\000\110\000\
\\088\000\109\000\089\000\108\000\099\000\107\000\000\000\
\\072\000\057\001\075\000\122\000\076\000\121\000\077\000\120\000\
\\078\000\119\000\079\000\118\000\080\000\117\000\081\000\116\000\
\\082\000\115\000\083\000\114\000\084\000\113\000\085\000\112\000\
\\086\000\111\000\087\000\110\000\088\000\109\000\089\000\108\000\
\\099\000\107\000\000\000\
\\077\000\058\001\078\000\119\000\079\000\118\000\080\000\117\000\
\\081\000\116\000\082\000\115\000\083\000\114\000\084\000\113\000\
\\085\000\112\000\086\000\111\000\087\000\110\000\088\000\109\000\
\\089\000\108\000\099\000\107\000\000\000\
\\000\000\
\\000\000\
\\007\000\011\000\010\000\101\000\021\000\223\000\034\000\059\001\
\\068\000\097\000\069\000\002\000\072\000\221\000\075\000\122\000\
\\076\000\121\000\077\000\120\000\078\000\119\000\079\000\118\000\
\\080\000\117\000\081\000\116\000\082\000\115\000\083\000\114\000\
\\084\000\113\000\085\000\112\000\086\000\111\000\087\000\110\000\
\\088\000\109\000\089\000\108\000\099\000\107\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\058\000\063\001\060\000\062\001\061\000\227\000\000\000\
\\000\000\
\\104\000\065\001\000\000\
\\006\000\012\000\007\000\011\000\010\000\010\000\012\000\009\000\
\\013\000\008\000\014\000\007\000\020\000\138\000\037\000\137\000\
\\039\000\067\001\068\000\003\000\069\000\002\000\092\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\061\000\070\001\066\000\086\000\092\000\085\000\000\000\
\\072\000\071\001\075\000\122\000\076\000\121\000\077\000\120\000\
\\078\000\119\000\079\000\118\000\080\000\117\000\081\000\116\000\
\\082\000\115\000\083\000\114\000\084\000\113\000\085\000\112\000\
\\086\000\111\000\087\000\110\000\088\000\109\000\089\000\108\000\
\\099\000\107\000\000\000\
\\006\000\012\000\007\000\011\000\010\000\010\000\012\000\009\000\
\\013\000\008\000\014\000\007\000\020\000\138\000\037\000\137\000\
\\038\000\074\001\039\000\135\000\058\000\230\000\059\000\087\000\
\\060\000\073\001\061\000\227\000\066\000\045\000\068\000\003\000\
\\069\000\002\000\092\000\001\000\000\000\
\\026\000\075\001\027\000\233\000\000\000\
\\000\000\
\\024\000\077\001\072\000\141\000\075\000\122\000\076\000\121\000\
\\077\000\120\000\078\000\119\000\079\000\118\000\080\000\117\000\
\\081\000\116\000\082\000\115\000\083\000\114\000\084\000\113\000\
\\085\000\112\000\086\000\111\000\087\000\110\000\088\000\109\000\
\\089\000\108\000\099\000\107\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\072\000\081\001\075\000\122\000\076\000\121\000\077\000\120\000\
\\078\000\119\000\079\000\118\000\080\000\117\000\081\000\116\000\
\\082\000\115\000\083\000\114\000\084\000\113\000\085\000\112\000\
\\086\000\111\000\087\000\110\000\088\000\109\000\089\000\108\000\
\\099\000\107\000\000\000\
\\000\000\
\\072\000\082\001\075\000\122\000\076\000\121\000\077\000\120\000\
\\078\000\119\000\079\000\118\000\080\000\117\000\081\000\116\000\
\\082\000\115\000\083\000\114\000\084\000\113\000\085\000\112\000\
\\086\000\111\000\087\000\110\000\088\000\109\000\089\000\108\000\
\\099\000\107\000\000\000\
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
\\072\000\089\001\075\000\122\000\076\000\121\000\077\000\120\000\
\\078\000\119\000\079\000\118\000\080\000\117\000\081\000\116\000\
\\082\000\115\000\083\000\114\000\084\000\113\000\085\000\112\000\
\\086\000\111\000\087\000\110\000\088\000\109\000\089\000\108\000\
\\099\000\107\000\000\000\
\\006\000\012\000\007\000\011\000\010\000\010\000\012\000\009\000\
\\013\000\008\000\014\000\007\000\020\000\152\000\028\000\096\001\
\\049\000\095\001\050\000\094\001\051\000\093\001\052\000\092\001\
\\068\000\003\000\069\000\002\000\071\000\091\001\087\000\090\001\
\\088\000\109\000\089\000\108\000\092\000\001\000\099\000\107\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\041\000\148\000\042\000\100\001\071\000\146\000\072\000\145\000\
\\075\000\122\000\076\000\121\000\077\000\120\000\078\000\119\000\
\\079\000\118\000\080\000\117\000\081\000\116\000\082\000\115\000\
\\083\000\114\000\084\000\113\000\085\000\112\000\086\000\111\000\
\\087\000\144\000\088\000\109\000\089\000\108\000\099\000\107\000\000\000\
\\000\000\
\\000\000\
\\072\000\102\001\075\000\122\000\076\000\121\000\077\000\120\000\
\\078\000\119\000\079\000\118\000\080\000\117\000\081\000\116\000\
\\082\000\115\000\083\000\114\000\084\000\113\000\085\000\112\000\
\\086\000\111\000\087\000\110\000\088\000\109\000\089\000\108\000\
\\099\000\107\000\000\000\
\\072\000\103\001\075\000\122\000\076\000\121\000\077\000\120\000\
\\078\000\119\000\079\000\118\000\080\000\117\000\081\000\116\000\
\\082\000\115\000\083\000\114\000\084\000\113\000\085\000\112\000\
\\086\000\111\000\087\000\110\000\088\000\109\000\089\000\108\000\
\\099\000\107\000\000\000\
\\000\000\
\\000\000\
\\091\000\172\000\093\000\105\001\000\000\
\\072\000\107\001\075\000\122\000\076\000\121\000\077\000\120\000\
\\078\000\119\000\079\000\118\000\080\000\117\000\081\000\116\000\
\\082\000\115\000\083\000\114\000\084\000\113\000\085\000\112\000\
\\086\000\111\000\087\000\110\000\088\000\109\000\089\000\108\000\
\\094\000\106\001\099\000\107\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\058\000\049\000\059\000\183\000\062\000\182\000\063\000\109\001\
\\066\000\045\000\000\000\
\\072\000\110\001\075\000\122\000\076\000\121\000\077\000\120\000\
\\078\000\119\000\079\000\118\000\080\000\117\000\081\000\116\000\
\\082\000\115\000\083\000\114\000\084\000\113\000\085\000\112\000\
\\086\000\111\000\087\000\110\000\088\000\109\000\089\000\108\000\
\\099\000\107\000\000\000\
\\009\000\030\001\000\000\
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
\\085\000\112\000\086\000\117\001\087\000\110\000\088\000\109\000\
\\089\000\108\000\099\000\107\000\000\000\
\\000\000\
\\061\000\070\001\000\000\
\\006\000\012\000\007\000\011\000\010\000\010\000\012\000\009\000\
\\013\000\008\000\014\000\007\000\020\000\138\000\037\000\137\000\
\\038\000\074\001\039\000\135\000\058\000\063\001\060\000\073\001\
\\061\000\227\000\068\000\003\000\069\000\002\000\092\000\001\000\000\000\
\\000\000\
\\090\000\119\001\000\000\
\\000\000\
\\072\000\120\001\075\000\122\000\076\000\121\000\077\000\120\000\
\\078\000\119\000\079\000\118\000\080\000\117\000\081\000\116\000\
\\082\000\115\000\083\000\114\000\084\000\113\000\085\000\112\000\
\\086\000\111\000\087\000\110\000\088\000\109\000\089\000\108\000\
\\099\000\107\000\000\000\
\\006\000\012\000\007\000\011\000\010\000\010\000\012\000\009\000\
\\013\000\008\000\014\000\007\000\020\000\138\000\037\000\137\000\
\\038\000\121\001\039\000\135\000\068\000\003\000\069\000\002\000\
\\092\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\022\000\125\001\023\000\237\000\024\000\236\000\025\000\235\000\
\\026\000\234\000\027\000\233\000\072\000\141\000\075\000\122\000\
\\076\000\121\000\077\000\120\000\078\000\119\000\079\000\118\000\
\\080\000\117\000\081\000\116\000\082\000\115\000\083\000\114\000\
\\084\000\113\000\085\000\112\000\086\000\111\000\087\000\110\000\
\\088\000\109\000\089\000\108\000\099\000\107\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\095\000\129\001\099\000\128\001\000\000\
\\041\000\148\000\042\000\132\001\043\000\131\001\044\000\130\001\
\\071\000\146\000\072\000\145\000\075\000\122\000\076\000\121\000\
\\077\000\120\000\078\000\119\000\079\000\118\000\080\000\117\000\
\\081\000\116\000\082\000\115\000\083\000\114\000\084\000\113\000\
\\085\000\112\000\086\000\111\000\087\000\144\000\088\000\109\000\
\\089\000\108\000\099\000\107\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\053\000\138\001\072\000\137\001\075\000\122\000\076\000\121\000\
\\077\000\120\000\078\000\119\000\079\000\118\000\080\000\117\000\
\\081\000\116\000\082\000\115\000\083\000\114\000\084\000\113\000\
\\085\000\112\000\086\000\111\000\087\000\110\000\088\000\109\000\
\\089\000\108\000\099\000\107\000\000\000\
\\000\000\
\\007\000\011\000\010\000\101\000\021\000\223\000\034\000\139\001\
\\068\000\097\000\069\000\002\000\072\000\221\000\075\000\122\000\
\\076\000\121\000\077\000\120\000\078\000\119\000\079\000\118\000\
\\080\000\117\000\081\000\116\000\082\000\115\000\083\000\114\000\
\\084\000\113\000\085\000\112\000\086\000\111\000\087\000\110\000\
\\088\000\109\000\089\000\108\000\099\000\107\000\000\000\
\\085\000\112\000\086\000\140\001\087\000\110\000\088\000\109\000\
\\089\000\108\000\099\000\107\000\000\000\
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
\\072\000\039\001\073\000\147\001\075\000\122\000\076\000\121\000\
\\077\000\120\000\078\000\119\000\079\000\118\000\080\000\117\000\
\\081\000\116\000\082\000\115\000\083\000\114\000\084\000\113\000\
\\085\000\112\000\086\000\111\000\087\000\110\000\088\000\109\000\
\\089\000\108\000\099\000\107\000\000\000\
\\072\000\148\001\075\000\122\000\076\000\121\000\077\000\120\000\
\\078\000\119\000\079\000\118\000\080\000\117\000\081\000\116\000\
\\082\000\115\000\083\000\114\000\084\000\113\000\085\000\112\000\
\\086\000\111\000\087\000\110\000\088\000\109\000\089\000\108\000\
\\099\000\107\000\000\000\
\\000\000\
\\000\000\
\\022\000\149\001\023\000\237\000\024\000\236\000\025\000\235\000\
\\026\000\234\000\027\000\233\000\072\000\141\000\075\000\122\000\
\\076\000\121\000\077\000\120\000\078\000\119\000\079\000\118\000\
\\080\000\117\000\081\000\116\000\082\000\115\000\083\000\114\000\
\\084\000\113\000\085\000\112\000\086\000\111\000\087\000\110\000\
\\088\000\109\000\089\000\108\000\099\000\107\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\096\000\153\001\000\000\
\\000\000\
\\000\000\
\\000\000\
\\041\000\148\000\042\000\132\001\044\000\157\001\071\000\146\000\
\\072\000\145\000\075\000\122\000\076\000\121\000\077\000\120\000\
\\078\000\119\000\079\000\118\000\080\000\117\000\081\000\116\000\
\\082\000\115\000\083\000\114\000\084\000\113\000\085\000\112\000\
\\086\000\111\000\087\000\144\000\088\000\109\000\089\000\108\000\
\\099\000\107\000\000\000\
\\000\000\
\\072\000\159\001\075\000\122\000\076\000\121\000\077\000\120\000\
\\078\000\119\000\079\000\118\000\080\000\117\000\081\000\116\000\
\\082\000\115\000\083\000\114\000\084\000\113\000\085\000\112\000\
\\086\000\111\000\087\000\110\000\088\000\109\000\089\000\108\000\
\\099\000\107\000\000\000\
\\051\000\160\001\052\000\092\001\071\000\091\001\087\000\090\001\
\\088\000\109\000\089\000\108\000\099\000\107\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\018\000\014\001\019\000\164\001\000\000\
\\041\000\148\000\042\000\165\001\071\000\146\000\072\000\145\000\
\\075\000\122\000\076\000\121\000\077\000\120\000\078\000\119\000\
\\079\000\118\000\080\000\117\000\081\000\116\000\082\000\115\000\
\\083\000\114\000\084\000\113\000\085\000\112\000\086\000\111\000\
\\087\000\144\000\088\000\109\000\089\000\108\000\099\000\107\000\000\000\
\\000\000\
\\072\000\107\001\075\000\122\000\076\000\121\000\077\000\120\000\
\\078\000\119\000\079\000\118\000\080\000\117\000\081\000\116\000\
\\082\000\115\000\083\000\114\000\084\000\113\000\085\000\112\000\
\\086\000\111\000\087\000\110\000\088\000\109\000\089\000\108\000\
\\094\000\166\001\099\000\107\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\099\000\171\001\101\000\170\001\102\000\169\001\103\000\168\001\000\000\
\\000\000\
\\000\000\
\\000\000\
\\045\000\178\001\046\000\177\001\047\000\176\001\048\000\175\001\000\000\
\\000\000\
\\000\000\
\\054\000\184\001\055\000\183\001\056\000\182\001\071\000\181\001\
\\087\000\090\001\088\000\109\000\089\000\108\000\099\000\107\000\000\000\
\\000\000\
\\072\000\185\001\075\000\122\000\076\000\121\000\077\000\120\000\
\\078\000\119\000\079\000\118\000\080\000\117\000\081\000\116\000\
\\082\000\115\000\083\000\114\000\084\000\113\000\085\000\112\000\
\\086\000\111\000\087\000\110\000\088\000\109\000\089\000\108\000\
\\099\000\107\000\000\000\
\\041\000\148\000\042\000\186\001\071\000\146\000\072\000\145\000\
\\075\000\122\000\076\000\121\000\077\000\120\000\078\000\119\000\
\\079\000\118\000\080\000\117\000\081\000\116\000\082\000\115\000\
\\083\000\114\000\084\000\113\000\085\000\112\000\086\000\111\000\
\\087\000\144\000\088\000\109\000\089\000\108\000\099\000\107\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\097\000\188\001\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\047\000\194\001\048\000\175\001\000\000\
\\041\000\148\000\042\000\195\001\071\000\146\000\072\000\145\000\
\\075\000\122\000\076\000\121\000\077\000\120\000\078\000\119\000\
\\079\000\118\000\080\000\117\000\081\000\116\000\082\000\115\000\
\\083\000\114\000\084\000\113\000\085\000\112\000\086\000\111\000\
\\087\000\144\000\088\000\109\000\089\000\108\000\099\000\107\000\000\000\
\\045\000\196\001\046\000\177\001\047\000\176\001\048\000\175\001\000\000\
\\000\000\
\\000\000\
\\072\000\199\001\075\000\122\000\076\000\121\000\077\000\120\000\
\\078\000\119\000\079\000\118\000\080\000\117\000\081\000\116\000\
\\082\000\115\000\083\000\114\000\084\000\113\000\085\000\112\000\
\\086\000\111\000\087\000\110\000\088\000\109\000\089\000\108\000\
\\099\000\107\000\000\000\
\\057\000\200\001\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\041\000\148\000\042\000\207\001\071\000\146\000\072\000\145\000\
\\075\000\122\000\076\000\121\000\077\000\120\000\078\000\119\000\
\\079\000\118\000\080\000\117\000\081\000\116\000\082\000\115\000\
\\083\000\114\000\084\000\113\000\085\000\112\000\086\000\111\000\
\\087\000\144\000\088\000\109\000\089\000\108\000\099\000\107\000\000\000\
\\000\000\
\\099\000\171\001\101\000\170\001\102\000\208\001\103\000\168\001\000\000\
\\099\000\171\001\101\000\170\001\103\000\209\001\000\000\
\\072\000\210\001\075\000\122\000\076\000\121\000\077\000\120\000\
\\078\000\119\000\079\000\118\000\080\000\117\000\081\000\116\000\
\\082\000\115\000\083\000\114\000\084\000\113\000\085\000\112\000\
\\086\000\111\000\087\000\110\000\088\000\109\000\089\000\108\000\
\\099\000\107\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\006\000\012\000\007\000\011\000\010\000\010\000\012\000\009\000\
\\013\000\008\000\014\000\007\000\020\000\152\000\028\000\151\000\
\\035\000\212\001\036\000\149\000\041\000\148\000\042\000\147\000\
\\068\000\003\000\069\000\002\000\071\000\146\000\072\000\145\000\
\\075\000\122\000\076\000\121\000\077\000\120\000\078\000\119\000\
\\079\000\118\000\080\000\117\000\081\000\116\000\082\000\115\000\
\\083\000\114\000\084\000\113\000\085\000\112\000\086\000\111\000\
\\087\000\144\000\088\000\109\000\089\000\108\000\092\000\001\000\
\\099\000\107\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\072\000\214\001\075\000\122\000\076\000\121\000\077\000\120\000\
\\078\000\119\000\079\000\118\000\080\000\117\000\081\000\116\000\
\\082\000\115\000\083\000\114\000\084\000\113\000\085\000\112\000\
\\086\000\111\000\087\000\110\000\088\000\109\000\089\000\108\000\
\\099\000\107\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\055\000\216\001\056\000\182\001\071\000\181\001\087\000\090\001\
\\088\000\109\000\089\000\108\000\099\000\107\000\000\000\
\\018\000\014\001\019\000\217\001\000\000\
\\000\000\
\\000\000\
\\098\000\219\001\000\000\
\\000\000\
\\000\000\
\\099\000\222\001\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\041\000\148\000\042\000\224\001\071\000\146\000\072\000\145\000\
\\075\000\122\000\076\000\121\000\077\000\120\000\078\000\119\000\
\\079\000\118\000\080\000\117\000\081\000\116\000\082\000\115\000\
\\083\000\114\000\084\000\113\000\085\000\112\000\086\000\111\000\
\\087\000\144\000\088\000\109\000\089\000\108\000\099\000\107\000\000\000\
\\000\000\
\\000\000\
\\099\000\226\001\100\000\225\001\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\072\000\229\001\075\000\122\000\076\000\121\000\077\000\120\000\
\\078\000\119\000\079\000\118\000\080\000\117\000\081\000\116\000\
\\082\000\115\000\083\000\114\000\084\000\113\000\085\000\112\000\
\\086\000\111\000\087\000\110\000\088\000\109\000\089\000\108\000\
\\099\000\107\000\000\000\
\\099\000\226\001\100\000\230\001\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\"
val numstates = 489
val numrules = 285
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
  | (T 81) => "NORETURN"
  | (T 82) => "THREAD_LOCAL"
  | (T 83) => "AUTO"
  | (T 84) => "FNSPEC"
  | (T 85) => "RELSPEC"
  | (T 86) => "AUXUPD"
  | (T 87) => "GHOSTUPD"
  | (T 88) => "MODIFIES"
  | (T 89) => "CALLS"
  | (T 90) => "OWNED_BY"
  | (T 91) => "SPEC_BEGIN"
  | (T 92) => "SPEC_END"
  | (T 93) => "DONT_TRANSLATE"
  | (T 94) => "STRING_LITERAL"
  | (T 95) => "SPEC_BLOCKEND"
  | (T 96) => "GCC_ATTRIBUTE"
  | (T 97) => "YASM"
  | (T 98) => "YREGISTER"
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
 :: (T 87) :: (T 88) :: (T 89) :: (T 90) :: (T 91) :: (T 92) :: (T 93)
 :: (T 95) :: (T 96) :: (T 97) :: (T 98) :: nil
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
| (5,(_,(_,YSEMI1left,YSEMI1right))::rest671) => let val result=
MlyValue.external_declaration(fn _ => ([]))
 in (LrTable.NT 2,(result,YSEMI1left,YSEMI1right),rest671) end
| (6,(_,(_,TYPEDEFleft as TYPEDEF1left,TYPEDEFright as TYPEDEF1right))
::rest671) => let val result=MlyValue.storage_class_specifier(fn _ => 
(wrap(TypeDef, TYPEDEFleft, TYPEDEFright)))
 in (LrTable.NT 5,(result,TYPEDEF1left,TYPEDEF1right),rest671) end
| (7,(_,(_,EXTERNleft as EXTERN1left,EXTERNright as EXTERN1right))::
rest671) => let val result=MlyValue.storage_class_specifier(fn _ => (
wrap(Extern, EXTERNleft, EXTERNright)))
 in (LrTable.NT 5,(result,EXTERN1left,EXTERN1right),rest671) end
| (8,(_,(_,STATICleft as STATIC1left,STATICright as STATIC1right))::
rest671) => let val result=MlyValue.storage_class_specifier(fn _ => (
wrap(Static, STATICleft, STATICright)))
 in (LrTable.NT 5,(result,STATIC1left,STATIC1right),rest671) end
| (9,(_,(_,YREGISTERleft as YREGISTER1left,YREGISTERright as 
YREGISTER1right))::rest671) => let val result=
MlyValue.storage_class_specifier(fn _ => (
wrap(Register, YREGISTERleft, YREGISTERright)))
 in (LrTable.NT 5,(result,YREGISTER1left,YREGISTER1right),rest671) end
| (10,(_,(_,AUTOleft as AUTO1left,AUTOright as AUTO1right))::rest671)
 => let val result=MlyValue.storage_class_specifier(fn _ => (
wrap(Auto, AUTOleft, AUTOright)))
 in (LrTable.NT 5,(result,AUTO1left,AUTO1right),rest671) end
| (11,(_,(_,THREAD_LOCALleft as THREAD_LOCAL1left,THREAD_LOCALright
 as THREAD_LOCAL1right))::rest671) => let val result=
MlyValue.storage_class_specifier(fn _ => (
wrap(Thread_Local, THREAD_LOCALleft,
                                             THREAD_LOCALright)
))
 in (LrTable.NT 5,(result,THREAD_LOCAL1left,THREAD_LOCAL1right),
rest671) end
| (12,(_,(_,INLINEleft as INLINE1left,INLINEright as INLINE1right))::
rest671) => let val result=MlyValue.function_specifiers(fn _ => (
wrap([], INLINEleft, INLINEright)))
 in (LrTable.NT 11,(result,INLINE1left,INLINE1right),rest671) end
| (13,(_,(_,NORETURNleft as NORETURN1left,NORETURNright as 
NORETURN1right))::rest671) => let val result=
MlyValue.function_specifiers(fn _ => (
wrap([wrap(gcc_attribs [GCC_AttribID "noreturn"],
                            NORETURNleft, NORETURNright)],
                      NORETURNleft, NORETURNright)
))
 in (LrTable.NT 11,(result,NORETURN1left,NORETURN1right),rest671) end
| (14,(_,(_,_,SPEC_BLOCKEND1right))::(_,(
MlyValue.special_function_specs special_function_specs1,
special_function_specs1left,_))::rest671) => let val result=
MlyValue.function_specifiers(fn _ => let val special_function_specs
 as special_function_specs1=special_function_specs1 ()
 in (special_function_specs) end
)
 in (LrTable.NT 11,(result,special_function_specs1left,
SPEC_BLOCKEND1right),rest671) end
| (15,(_,(MlyValue.attribute_specifier attribute_specifier1,
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
| (16,(_,(_,_,RPAREN2right))::_::(_,(MlyValue.attribute_list 
attribute_list1,_,_))::_::_::(_,(_,GCC_ATTRIBUTEleft as 
GCC_ATTRIBUTE1left,_))::rest671) => let val result=
MlyValue.attribute_specifier(fn _ => let val attribute_list as 
attribute_list1=attribute_list1 ()
 in (wrap(attribute_list, GCC_ATTRIBUTEleft, RPAREN2right)) end
)
 in (LrTable.NT 91,(result,GCC_ATTRIBUTE1left,RPAREN2right),rest671)
 end
| (17,(_,(_,_,SPEC_BLOCKENDright as SPEC_BLOCKEND1right))::(_,(
MlyValue.ID ID1,_,_))::(_,(_,OWNED_BYleft as OWNED_BY1left,_))::
rest671) => let val result=MlyValue.attribute_specifier(fn _ => let 
val ID as ID1=ID1 ()
 in (wrap([OWNED_BY ID], OWNED_BYleft, SPEC_BLOCKENDright)) end
)
 in (LrTable.NT 91,(result,OWNED_BY1left,SPEC_BLOCKEND1right),rest671)
 end
| (18,rest671) => let val result=MlyValue.attribute_list(fn _ => ([]))
 in (LrTable.NT 92,(result,defaultPos,defaultPos),rest671) end
| (19,(_,(MlyValue.attribute attribute1,attribute1left,attribute1right
))::rest671) => let val result=MlyValue.attribute_list(fn _ => let 
val attribute as attribute1=attribute1 ()
 in (case attribute of NONE => [] | SOME a => [a]) end
)
 in (LrTable.NT 92,(result,attribute1left,attribute1right),rest671)
 end
| (20,(_,(MlyValue.attribute_list attribute_list1,_,
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
| (21,(_,(MlyValue.ID ID1,ID1left,ID1right))::rest671) => let val 
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
| (22,(_,(_,CONST1left,CONST1right))::rest671) => let val result=
MlyValue.attribute(fn _ => (SOME (GCC_AttribID "const")))
 in (LrTable.NT 90,(result,CONST1left,CONST1right),rest671) end
| (23,(_,(_,_,RPAREN1right))::_::(_,(MlyValue.ID ID1,ID1left,_))::
rest671) => let val result=MlyValue.attribute(fn _ => let val ID as 
ID1=ID1 ()
 in (SOME (GCC_AttribFn (ID, []))) end
)
 in (LrTable.NT 90,(result,ID1left,RPAREN1right),rest671) end
| (24,(_,(_,_,RPAREN1right))::(_,(MlyValue.attribute_parameter_list1 
attribute_parameter_list11,_,_))::_::(_,(MlyValue.ID ID1,ID1left,_))::
rest671) => let val result=MlyValue.attribute(fn _ => let val ID as 
ID1=ID1 ()
val attribute_parameter_list1 as attribute_parameter_list11=
attribute_parameter_list11 ()
 in (SOME (GCC_AttribFn (ID, attribute_parameter_list1))) end
)
 in (LrTable.NT 90,(result,ID1left,RPAREN1right),rest671) end
| (25,(_,(MlyValue.rexpression rexpression1,rexpression1left,
rexpression1right))::rest671) => let val result=
MlyValue.attribute_parameter_list1(fn _ => let val rexpression as 
rexpression1=rexpression1 ()
 in ([rexpression]) end
)
 in (LrTable.NT 93,(result,rexpression1left,rexpression1right),rest671
) end
| (26,(_,(MlyValue.attribute_parameter_list1 
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
| (27,(_,(MlyValue.special_function_spec special_function_spec1,
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
| (28,(_,(MlyValue.special_function_specs special_function_specs1,_,
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
| (29,(_,(MlyValue.idlist idlist1,_,idlist1right))::(_,(_,MODIFIESleft
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
| (30,(_,(MlyValue.fnspecs fnspecs1,_,fnspecs1right))::(_,(_,
FNSPECleft as FNSPEC1left,_))::rest671) => let val result=
MlyValue.special_function_spec(fn _ => let val fnspecs as fnspecs1=
fnspecs1 ()
 in (wrap(fnspec fnspecs, FNSPECleft, right fnspecs)) end
)
 in (LrTable.NT 12,(result,FNSPEC1left,fnspecs1right),rest671) end
| (31,(_,(MlyValue.rel_spec rel_spec1,_,rel_spec1right))::(_,(_,
RELSPECleft as RELSPEC1left,_))::rest671) => let val result=
MlyValue.special_function_spec(fn _ => let val rel_spec as rel_spec1=
rel_spec1 ()
 in (wrap(relspec rel_spec, RELSPECleft, right rel_spec)) end
)
 in (LrTable.NT 12,(result,RELSPEC1left,rel_spec1right),rest671) end
| (32,(_,(_,DONT_TRANSLATEleft as DONT_TRANSLATE1left,
DONT_TRANSLATEright as DONT_TRANSLATE1right))::rest671) => let val 
result=MlyValue.special_function_spec(fn _ => (
wrap(didnt_translate, DONT_TRANSLATEleft, DONT_TRANSLATEright)))
 in (LrTable.NT 12,(result,DONT_TRANSLATE1left,DONT_TRANSLATE1right),
rest671) end
| (33,(_,(MlyValue.STRING_LITERAL STRING_LITERAL1,_,
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
| (34,(_,(MlyValue.fnspecs fnspecs1,_,fnspecs1right))::(_,(
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
| (35,(_,(MlyValue.STRING_LITERAL STRING_LITERAL1,STRING_LITERALleft
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
| (36,rest671) => let val result=MlyValue.idlist(fn _ => ([]))
 in (LrTable.NT 89,(result,defaultPos,defaultPos),rest671) end
| (37,(_,(MlyValue.idlist idlist1,_,idlist1right))::(_,(MlyValue.ID 
ID1,IDleft as ID1left,IDright))::rest671) => let val result=
MlyValue.idlist(fn _ => let val ID as ID1=ID1 ()
val idlist as idlist1=idlist1 ()
 in (wrap(ID,IDleft,IDright) :: idlist) end
)
 in (LrTable.NT 89,(result,ID1left,idlist1right),rest671) end
| (38,(_,(MlyValue.idlist idlist1,_,idlist1right))::(_,(_,_,
RBRACKETright))::_::(_,(_,LBRACKETleft as LBRACKET1left,_))::rest671)
 => let val result=MlyValue.idlist(fn _ => let val idlist as idlist1=
idlist1 ()
 in (
wrap(NameGeneration.phantom_state_name, LBRACKETleft,
                      RBRACKETright) :: idlist
) end
)
 in (LrTable.NT 89,(result,LBRACKET1left,idlist1right),rest671) end
| (39,(_,(_,_,YSEMI1right))::(_,(MlyValue.declaration_specifiers 
declaration_specifiers1,declaration_specifiers1left,_))::rest671) => 
let val result=MlyValue.declaration(fn _ => let val 
declaration_specifiers as declaration_specifiers1=
declaration_specifiers1 ()
 in (empty_declarator (node declaration_specifiers)) end
)
 in (LrTable.NT 27,(result,declaration_specifiers1left,YSEMI1right),
rest671) end
| (40,(_,(_,_,YSEMI1right))::(_,(MlyValue.init_declarator_list 
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
| (41,(_,(MlyValue.storage_class_specifier storage_class_specifier1,
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
| (42,(_,(MlyValue.declaration_specifiers declaration_specifiers1,_,
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
| (43,(_,(MlyValue.type_specifier type_specifier1,type_specifier1left,
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
| (44,(_,(MlyValue.declaration_specifiers declaration_specifiers1,_,
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
| (45,(_,(MlyValue.type_qualifier type_qualifier1,type_qualifier1left,
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
| (46,(_,(MlyValue.declaration_specifiers declaration_specifiers1,_,
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
| (47,(_,(MlyValue.function_specifiers function_specifiers1,
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
| (48,(_,(MlyValue.declaration_specifiers declaration_specifiers1,_,
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
| (49,(_,(MlyValue.compound_statement compound_statement1,_,
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
| (50,rest671) => let val result=MlyValue.parameter_list(fn _ => (
wrap([], defaultPos, defaultPos)))
 in (LrTable.NT 37,(result,defaultPos,defaultPos),rest671) end
| (51,(_,(MlyValue.parameter_list1 parameter_list11,
parameter_list11left,parameter_list11right))::rest671) => let val 
result=MlyValue.parameter_list(fn _ => let val parameter_list1 as 
parameter_list11=parameter_list11 ()
 in (parameter_list1) end
)
 in (LrTable.NT 37,(result,parameter_list11left,parameter_list11right)
,rest671) end
| (52,(_,(MlyValue.parameter_declaration parameter_declaration1,
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
| (53,(_,(MlyValue.parameter_list1 parameter_list11,_,
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
| (54,(_,(MlyValue.declarator declarator1,_,declarator1right))::(_,(
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
| (55,(_,(MlyValue.abstract_declarator abstract_declarator1,_,
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
| (56,(_,(MlyValue.declaration_specifiers declaration_specifiers1,
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
| (57,(_,(_,_,RCURLYright as RCURLY1right))::(_,(
MlyValue.block_item_list block_item_list1,_,_))::(_,(_,LCURLYleft as 
LCURLY1left,_))::rest671) => let val result=
MlyValue.compound_statement(fn _ => let val block_item_list as 
block_item_list1=block_item_list1 ()
 in (wrap(block_item_list, LCURLYleft, RCURLYright)) end
)
 in (LrTable.NT 40,(result,LCURLY1left,RCURLY1right),rest671) end
| (58,rest671) => let val result=MlyValue.block_item_list(fn _ => ([])
)
 in (LrTable.NT 34,(result,defaultPos,defaultPos),rest671) end
| (59,(_,(MlyValue.block_item_list block_item_list1,_,
block_item_list1right))::(_,(MlyValue.block_item block_item1,
block_item1left,_))::rest671) => let val result=
MlyValue.block_item_list(fn _ => let val block_item as block_item1=
block_item1 ()
val block_item_list as block_item_list1=block_item_list1 ()
 in (block_item @ block_item_list) end
)
 in (LrTable.NT 34,(result,block_item1left,block_item_list1right),
rest671) end
| (60,(_,(MlyValue.declaration declaration1,declaration1left,
declaration1right))::rest671) => let val result=MlyValue.block_item(
fn _ => let val declaration as declaration1=declaration1 ()
 in (map BI_Decl declaration) end
)
 in (LrTable.NT 35,(result,declaration1left,declaration1right),rest671
) end
| (61,(_,(MlyValue.statement statement1,statement1left,statement1right
))::rest671) => let val result=MlyValue.block_item(fn _ => let val 
statement as statement1=statement1 ()
 in ([BI_Stmt statement]) end
)
 in (LrTable.NT 35,(result,statement1left,statement1right),rest671)
 end
| (62,rest671) => let val result=MlyValue.statement_list(fn _ => ([]))
 in (LrTable.NT 42,(result,defaultPos,defaultPos),rest671) end
| (63,(_,(MlyValue.statement_list1 statement_list11,
statement_list11left,statement_list11right))::rest671) => let val 
result=MlyValue.statement_list(fn _ => let val statement_list1 as 
statement_list11=statement_list11 ()
 in (statement_list1) end
)
 in (LrTable.NT 42,(result,statement_list11left,statement_list11right)
,rest671) end
| (64,(_,(MlyValue.statement statement1,statement1left,statement1right
))::rest671) => let val result=MlyValue.statement_list1(fn _ => let 
val statement as statement1=statement1 ()
 in ([statement]) end
)
 in (LrTable.NT 43,(result,statement1left,statement1right),rest671)
 end
| (65,(_,(MlyValue.statement_list1 statement_list11,_,
statement_list11right))::(_,(MlyValue.statement statement1,
statement1left,_))::rest671) => let val result=
MlyValue.statement_list1(fn _ => let val statement as statement1=
statement1 ()
val statement_list1 as statement_list11=statement_list11 ()
 in (statement::statement_list1) end
)
 in (LrTable.NT 43,(result,statement1left,statement_list11right),
rest671) end
| (66,(_,(MlyValue.struct_declaration struct_declaration1,
struct_declaration1left,struct_declaration1right))::rest671) => let 
val result=MlyValue.struct_declaration_list(fn _ => let val 
struct_declaration as struct_declaration1=struct_declaration1 ()
 in (struct_declaration) end
)
 in (LrTable.NT 28,(result,struct_declaration1left,
struct_declaration1right),rest671) end
| (67,(_,(MlyValue.struct_declaration_list struct_declaration_list1,_,
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
| (68,(_,(MlyValue.type_specifier type_specifier1,type_specifier1left,
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
| (69,(_,(MlyValue.specifier_qualifier_list specifier_qualifier_list1,
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
| (70,(_,(MlyValue.type_qualifier type_qualifier1,type_qualifier1left,
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
| (71,(_,(MlyValue.specifier_qualifier_list specifier_qualifier_list1,
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
| (72,(_,(_,CONSTleft as CONST1left,CONSTright as CONST1right))::
rest671) => let val result=MlyValue.type_qualifier(fn _ => (
wrap(Const, CONSTleft, CONSTright)))
 in (LrTable.NT 9,(result,CONST1left,CONST1right),rest671) end
| (73,(_,(_,VOLATILEleft as VOLATILE1left,VOLATILEright as 
VOLATILE1right))::rest671) => let val result=MlyValue.type_qualifier(
fn _ => (wrap(Volatile, VOLATILEleft, VOLATILEright)))
 in (LrTable.NT 9,(result,VOLATILE1left,VOLATILE1right),rest671) end
| (74,(_,(_,RESTRICTleft as RESTRICT1left,RESTRICTright as 
RESTRICT1right))::rest671) => let val result=MlyValue.type_qualifier(
fn _ => (wrap(Restrict, RESTRICTleft, RESTRICTright)))
 in (LrTable.NT 9,(result,RESTRICT1left,RESTRICT1right),rest671) end
| (75,(_,(MlyValue.type_qualifier type_qualifier1,type_qualifier1left,
type_qualifier1right))::rest671) => let val result=
MlyValue.type_qualifier_list(fn _ => let val type_qualifier as 
type_qualifier1=type_qualifier1 ()
 in ([type_qualifier]) end
)
 in (LrTable.NT 10,(result,type_qualifier1left,type_qualifier1right),
rest671) end
| (76,(_,(MlyValue.type_qualifier_list type_qualifier_list1,_,
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
| (77,(_,(_,_,YSEMI1right))::(_,(MlyValue.struct_declarator_list 
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
| (78,(_,(MlyValue.struct_declarator struct_declarator1,
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
| (79,(_,(MlyValue.struct_declarator_list struct_declarator_list1,_,
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
| (80,(_,(MlyValue.declarator declarator1,declarator1left,
declarator1right))::rest671) => let val result=
MlyValue.struct_declarator(fn _ => let val declarator as declarator1=
declarator1 ()
 in (wrap((declarator, NONE), left declarator, right declarator)) end
)
 in (LrTable.NT 61,(result,declarator1left,declarator1right),rest671)
 end
| (81,(_,(MlyValue.rexpression rexpression1,_,rexpression1right))::_::
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
| (82,(_,(MlyValue.init_declarator init_declarator1,
init_declarator1left,init_declarator1right))::rest671) => let val 
result=MlyValue.init_declarator_list(fn _ => let val init_declarator
 as init_declarator1=init_declarator1 ()
 in ([init_declarator]) end
)
 in (LrTable.NT 64,(result,init_declarator1left,init_declarator1right)
,rest671) end
| (83,(_,(MlyValue.init_declarator_list init_declarator_list1,_,
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
| (84,(_,(MlyValue.declarator declarator1,declarator1left,
declarator1right))::rest671) => let val result=
MlyValue.init_declarator(fn _ => let val declarator as declarator1=
declarator1 ()
 in (wrap((declarator, NONE), left declarator, right declarator)) end
)
 in (LrTable.NT 63,(result,declarator1left,declarator1right),rest671)
 end
| (85,(_,(MlyValue.initializer initializer1,_,initializer1right))::_::
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
| (86,(_,(_,YSTARleft as YSTAR1left,YSTARright as YSTAR1right))::
rest671) => let val result=MlyValue.pointer(fn _ => (
ptrdecl YSTARleft YSTARright))
 in (LrTable.NT 57,(result,YSTAR1left,YSTAR1right),rest671) end
| (87,(_,(MlyValue.type_qualifier_list type_qualifier_list1,_,
type_qualifier_list1right))::(_,(_,YSTARleft as YSTAR1left,_))::
rest671) => let val result=MlyValue.pointer(fn _ => let val 
type_qualifier_list as type_qualifier_list1=type_qualifier_list1 ()
 in (ptrdecl YSTARleft (right (List.last type_qualifier_list))) end
)
 in (LrTable.NT 57,(result,YSTAR1left,type_qualifier_list1right),
rest671) end
| (88,(_,(MlyValue.pointer pointer1,_,pointer1right))::(_,(_,YSTARleft
 as YSTAR1left,YSTARright))::rest671) => let val result=
MlyValue.pointer(fn _ => let val pointer as pointer1=pointer1 ()
 in (ooa(ptrdecl YSTARleft YSTARright, pointer)) end
)
 in (LrTable.NT 57,(result,YSTAR1left,pointer1right),rest671) end
| (89,(_,(MlyValue.pointer pointer1,_,pointer1right))::(_,(
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
| (90,(_,(MlyValue.direct_declarator direct_declarator1,_,
direct_declarator1right))::(_,(MlyValue.pointer pointer1,pointer1left,
_))::rest671) => let val result=MlyValue.declarator(fn _ => let val 
pointer as pointer1=pointer1 ()
val direct_declarator as direct_declarator1=direct_declarator1 ()
 in (ood(direct_declarator, pointer)) end
)
 in (LrTable.NT 58,(result,pointer1left,direct_declarator1right),
rest671) end
| (91,(_,(MlyValue.direct_declarator direct_declarator1,_,
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
| (92,(_,(MlyValue.direct_declarator direct_declarator1,
direct_declarator1left,direct_declarator1right))::rest671) => let val 
result=MlyValue.declarator(fn _ => let val direct_declarator as 
direct_declarator1=direct_declarator1 ()
 in (direct_declarator) end
)
 in (LrTable.NT 58,(result,direct_declarator1left,
direct_declarator1right),rest671) end
| (93,(_,(_,_,SPEC_BLOCKEND1right))::(_,(MlyValue.idlist idlist1,_,_))
::(_,(_,CALLS1left,_))::rest671) => let val result=
MlyValue.calls_block(fn _ => let val idlist as idlist1=idlist1 ()
 in (SOME idlist) end
)
 in (LrTable.NT 103,(result,CALLS1left,SPEC_BLOCKEND1right),rest671)
 end
| (94,rest671) => let val result=MlyValue.calls_block(fn _ => (NONE))
 in (LrTable.NT 103,(result,defaultPos,defaultPos),rest671) end
| (95,(_,(MlyValue.ID ID1,IDleft as ID1left,IDright as ID1right))::
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
| (96,(_,(_,_,RBRACKETright as RBRACKET1right))::(_,(
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
| (97,(_,(_,_,RBRACKETright as RBRACKET1right))::(_,(_,LBRACKETleft,_)
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
| (98,(_,(_,_,RPARENright as RPAREN1right))::(_,(MlyValue.declarator 
declarator1,_,_))::(_,(_,LPARENleft as LPAREN1left,_))::rest671) => 
let val result=MlyValue.direct_declarator(fn _ => let val declarator
 as declarator1=declarator1 ()
 in (wrap(node declarator, LPARENleft, RPARENright)) end
)
 in (LrTable.NT 65,(result,LPAREN1left,RPAREN1right),rest671) end
| (99,(_,(MlyValue.calls_block calls_block1,_,calls_block1right))::_::
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
| (100,(_,(MlyValue.attribute_specifier attribute_specifier1,_,
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
| (101,(_,(MlyValue.asm_declarator_mod asm_declarator_mod1,_,
asm_declarator_mod1right))::(_,(MlyValue.direct_declarator 
direct_declarator1,direct_declarator1left,_))::rest671) => let val 
result=MlyValue.direct_declarator(fn _ => let val direct_declarator
 as direct_declarator1=direct_declarator1 ()
val asm_declarator_mod1=asm_declarator_mod1 ()
 in (direct_declarator) end
)
 in (LrTable.NT 65,(result,direct_declarator1left,
asm_declarator_mod1right),rest671) end
| (102,(_,(_,_,RPAREN1right))::(_,(MlyValue.cstring_literal 
cstring_literal1,_,_))::_::(_,(_,YASM1left,_))::rest671) => let val 
result=MlyValue.asm_declarator_mod(fn _ => let val cstring_literal1=
cstring_literal1 ()
 in (()) end
)
 in (LrTable.NT 66,(result,YASM1left,RPAREN1right),rest671) end
| (103,(_,(MlyValue.ID ID1,IDleft as ID1left,IDright as ID1right))::
rest671) => let val result=MlyValue.struct_id(fn _ => let val ID as 
ID1=ID1 ()
 in (wrap(ID, IDleft, IDright)) end
)
 in (LrTable.NT 69,(result,ID1left,ID1right),rest671) end
| (104,(_,(MlyValue.TYPEID TYPEID1,TYPEIDleft as TYPEID1left,
TYPEIDright as TYPEID1right))::rest671) => let val result=
MlyValue.struct_id(fn _ => let val TYPEID as TYPEID1=TYPEID1 ()
 in (wrap(TYPEID, TYPEIDleft, TYPEIDright)) end
)
 in (LrTable.NT 69,(result,TYPEID1left,TYPEID1right),rest671) end
| (105,(_,(MlyValue.struct_id struct_id1,_,struct_id1right))::(_,(_,
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
| (106,(_,(_,_,RCURLYright as RCURLY1right))::(_,(
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
| (107,(_,(_,_,RCURLYright as RCURLY1right))::(_,(
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
| (108,(_,(_,INTleft as INT1left,INTright as INT1right))::rest671) => 
let val result=MlyValue.type_specifier(fn _ => (
Tstok(wrap(ts_int, INTleft, INTright))))
 in (LrTable.NT 67,(result,INT1left,INT1right),rest671) end
| (109,(_,(_,CHARleft as CHAR1left,CHARright as CHAR1right))::rest671)
 => let val result=MlyValue.type_specifier(fn _ => (
Tstok(wrap(ts_char, CHARleft, CHARright))))
 in (LrTable.NT 67,(result,CHAR1left,CHAR1right),rest671) end
| (110,(_,(_,SHORTleft as SHORT1left,SHORTright as SHORT1right))::
rest671) => let val result=MlyValue.type_specifier(fn _ => (
Tstok(wrap(ts_short, SHORTleft, SHORTright))))
 in (LrTable.NT 67,(result,SHORT1left,SHORT1right),rest671) end
| (111,(_,(_,LONGleft as LONG1left,LONGright as LONG1right))::rest671)
 => let val result=MlyValue.type_specifier(fn _ => (
Tstok(wrap(ts_long, LONGleft, LONGright))))
 in (LrTable.NT 67,(result,LONG1left,LONG1right),rest671) end
| (112,(_,(_,VOIDleft as VOID1left,VOIDright as VOID1right))::rest671)
 => let val result=MlyValue.type_specifier(fn _ => (
Tstok(wrap(ts_void, VOIDleft, VOIDright))))
 in (LrTable.NT 67,(result,VOID1left,VOID1right),rest671) end
| (113,(_,(_,SIGNEDleft as SIGNED1left,SIGNEDright as SIGNED1right))::
rest671) => let val result=MlyValue.type_specifier(fn _ => (
Tstok(wrap(ts_signed, SIGNEDleft, SIGNEDright))))
 in (LrTable.NT 67,(result,SIGNED1left,SIGNED1right),rest671) end
| (114,(_,(_,UNSIGNEDleft as UNSIGNED1left,UNSIGNEDright as 
UNSIGNED1right))::rest671) => let val result=MlyValue.type_specifier(
fn _ => (Tstok(wrap(ts_unsigned, UNSIGNEDleft, UNSIGNEDright))))
 in (LrTable.NT 67,(result,UNSIGNED1left,UNSIGNED1right),rest671) end
| (115,(_,(_,BOOLleft as BOOL1left,BOOLright as BOOL1right))::rest671)
 => let val result=MlyValue.type_specifier(fn _ => (
Tstok(wrap(ts_bool, BOOLleft, BOOLright))))
 in (LrTable.NT 67,(result,BOOL1left,BOOL1right),rest671) end
| (116,(_,(MlyValue.struct_or_union_specifier 
struct_or_union_specifier1,struct_or_union_specifier1left,
struct_or_union_specifier1right))::rest671) => let val result=
MlyValue.type_specifier(fn _ => let val struct_or_union_specifier as 
struct_or_union_specifier1=struct_or_union_specifier1 ()
 in (Tsstruct struct_or_union_specifier) end
)
 in (LrTable.NT 67,(result,struct_or_union_specifier1left,
struct_or_union_specifier1right),rest671) end
| (117,(_,(MlyValue.enum_specifier enum_specifier1,enum_specifier1left
,enum_specifier1right))::rest671) => let val result=
MlyValue.type_specifier(fn _ => let val enum_specifier as 
enum_specifier1=enum_specifier1 ()
 in (Tsenum enum_specifier) end
)
 in (LrTable.NT 67,(result,enum_specifier1left,enum_specifier1right),
rest671) end
| (118,(_,(MlyValue.TYPEID TYPEID1,TYPEIDleft as TYPEID1left,
TYPEIDright as TYPEID1right))::rest671) => let val result=
MlyValue.type_specifier(fn _ => let val TYPEID as TYPEID1=TYPEID1 ()
 in (Tstypeid(wrap(TYPEID, TYPEIDleft, TYPEIDright))) end
)
 in (LrTable.NT 67,(result,TYPEID1left,TYPEID1right),rest671) end
| (119,(_,(_,_,RCURLYright as RCURLY1right))::(_,(
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
| (120,(_,(_,_,RCURLYright as RCURLY1right))::(_,(
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
| (121,(_,(_,_,RCURLYright as RCURLY1right))::_::(_,(
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
| (122,(_,(_,_,RCURLYright as RCURLY1right))::_::(_,(
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
| (123,(_,(MlyValue.struct_id struct_id1,_,struct_idright as 
struct_id1right))::(_,(_,YENUMleft as YENUM1left,_))::rest671) => let 
val result=MlyValue.enum_specifier(fn _ => let val struct_id as 
struct_id1=struct_id1 ()
 in (wrap((apnode SOME struct_id, []), YENUMleft, struct_idright)) end
)
 in (LrTable.NT 6,(result,YENUM1left,struct_id1right),rest671) end
| (124,(_,(MlyValue.enumerator enumerator1,enumerator1left,
enumerator1right))::rest671) => let val result=
MlyValue.enumerator_list(fn _ => let val enumerator as enumerator1=
enumerator1 ()
 in ([enumerator]) end
)
 in (LrTable.NT 7,(result,enumerator1left,enumerator1right),rest671)
 end
| (125,(_,(MlyValue.enumerator enumerator1,_,enumerator1right))::_::(_
,(MlyValue.enumerator_list enumerator_list1,enumerator_list1left,_))::
rest671) => let val result=MlyValue.enumerator_list(fn _ => let val 
enumerator_list as enumerator_list1=enumerator_list1 ()
val enumerator as enumerator1=enumerator1 ()
 in (enumerator_list @ [enumerator]) end
)
 in (LrTable.NT 7,(result,enumerator_list1left,enumerator1right),
rest671) end
| (126,(_,(MlyValue.ID ID1,IDleft as ID1left,IDright as ID1right))::
rest671) => let val result=MlyValue.enumerator(fn _ => let val ID as 
ID1=ID1 ()
 in ((wrap(ID,IDleft,IDright), NONE)) end
)
 in (LrTable.NT 8,(result,ID1left,ID1right),rest671) end
| (127,(_,(MlyValue.rexpression rexpression1,_,rexpression1right))::_
::(_,(MlyValue.ID ID1,IDleft as ID1left,IDright))::rest671) => let 
val result=MlyValue.enumerator(fn _ => let val ID as ID1=ID1 ()
val rexpression as rexpression1=rexpression1 ()
 in ((wrap(ID,IDleft,IDright), SOME rexpression)) end
)
 in (LrTable.NT 8,(result,ID1left,rexpression1right),rest671) end
| (128,(_,(MlyValue.pointer pointer1,pointer1left,pointer1right))::
rest671) => let val result=MlyValue.abstract_declarator(fn _ => let 
val pointer as pointer1=pointer1 ()
 in (pointer) end
)
 in (LrTable.NT 59,(result,pointer1left,pointer1right),rest671) end
| (129,(_,(MlyValue.direct_abstract_declarator 
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
| (130,(_,(MlyValue.direct_abstract_declarator 
direct_abstract_declarator1,direct_abstract_declarator1left,
direct_abstract_declarator1right))::rest671) => let val result=
MlyValue.abstract_declarator(fn _ => let val 
direct_abstract_declarator as direct_abstract_declarator1=
direct_abstract_declarator1 ()
 in (direct_abstract_declarator) end
)
 in (LrTable.NT 59,(result,direct_abstract_declarator1left,
direct_abstract_declarator1right),rest671) end
| (131,(_,(_,_,RPARENright as RPAREN1right))::(_,(
MlyValue.abstract_declarator abstract_declarator1,_,_))::(_,(_,
LPARENleft as LPAREN1left,_))::rest671) => let val result=
MlyValue.direct_abstract_declarator(fn _ => let val 
abstract_declarator as abstract_declarator1=abstract_declarator1 ()
 in (wrap(node abstract_declarator, LPARENleft, RPARENright)) end
)
 in (LrTable.NT 60,(result,LPAREN1left,RPAREN1right),rest671) end
| (132,(_,(_,_,RBRACKETright as RBRACKET1right))::(_,(
MlyValue.rexpression rexpression1,_,_))::(_,(_,LBRACKETleft as 
LBRACKET1left,_))::rest671) => let val result=
MlyValue.direct_abstract_declarator(fn _ => let val rexpression as 
rexpression1=rexpression1 ()
 in (arraydecl LBRACKETleft RBRACKETright (SOME rexpression)) end
)
 in (LrTable.NT 60,(result,LBRACKET1left,RBRACKET1right),rest671) end
| (133,(_,(_,_,RBRACKETright as RBRACKET1right))::(_,(_,LBRACKETleft
 as LBRACKET1left,_))::rest671) => let val result=
MlyValue.direct_abstract_declarator(fn _ => (
ptrdecl LBRACKETleft RBRACKETright))
 in (LrTable.NT 60,(result,LBRACKET1left,RBRACKET1right),rest671) end
| (134,(_,(_,_,RBRACKETright as RBRACKET1right))::(_,(
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
| (135,(_,(_,_,RPARENright as RPAREN1right))::(_,(
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
| (136,(_,(_,_,RPARENright as RPAREN1right))::(_,(
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
| (137,(_,(MlyValue.abstract_declarator abstract_declarator1,_,
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
| (138,(_,(MlyValue.specifier_qualifier_list specifier_qualifier_list1
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
| (139,(_,(MlyValue.dinitializer dinitializer1,dinitializer1left,
dinitializer1right))::rest671) => let val result=
MlyValue.initializer_list(fn _ => let val dinitializer as 
dinitializer1=dinitializer1 ()
 in ([dinitializer]) end
)
 in (LrTable.NT 21,(result,dinitializer1left,dinitializer1right),
rest671) end
| (140,(_,(_,_,YCOMMA1right))::(_,(MlyValue.dinitializer dinitializer1
,dinitializer1left,_))::rest671) => let val result=
MlyValue.initializer_list(fn _ => let val dinitializer as 
dinitializer1=dinitializer1 ()
 in ([dinitializer]) end
)
 in (LrTable.NT 21,(result,dinitializer1left,YCOMMA1right),rest671)
 end
| (141,(_,(MlyValue.initializer_list initializer_list1,_,
initializer_list1right))::_::(_,(MlyValue.dinitializer dinitializer1,
dinitializer1left,_))::rest671) => let val result=
MlyValue.initializer_list(fn _ => let val dinitializer as 
dinitializer1=dinitializer1 ()
val initializer_list as initializer_list1=initializer_list1 ()
 in (dinitializer :: initializer_list) end
)
 in (LrTable.NT 21,(result,dinitializer1left,initializer_list1right),
rest671) end
| (142,(_,(MlyValue.initializer initializer1,_,initializer1right))::(_
,(MlyValue.designation designation1,designation1left,_))::rest671) => 
let val result=MlyValue.dinitializer(fn _ => let val designation as 
designation1=designation1 ()
val initializer as initializer1=initializer1 ()
 in ((designation, node initializer)) end
)
 in (LrTable.NT 22,(result,designation1left,initializer1right),rest671
) end
| (143,(_,(MlyValue.initializer initializer1,initializer1left,
initializer1right))::rest671) => let val result=MlyValue.dinitializer(
fn _ => let val initializer as initializer1=initializer1 ()
 in (([], node initializer)) end
)
 in (LrTable.NT 22,(result,initializer1left,initializer1right),rest671
) end
| (144,(_,(_,_,YEQ1right))::(_,(MlyValue.designator_list 
designator_list1,designator_list1left,_))::rest671) => let val result=
MlyValue.designation(fn _ => let val designator_list as 
designator_list1=designator_list1 ()
 in (designator_list) end
)
 in (LrTable.NT 24,(result,designator_list1left,YEQ1right),rest671)
 end
| (145,(_,(MlyValue.designator designator1,designator1left,
designator1right))::rest671) => let val result=
MlyValue.designator_list(fn _ => let val designator as designator1=
designator1 ()
 in ([designator]) end
)
 in (LrTable.NT 25,(result,designator1left,designator1right),rest671)
 end
| (146,(_,(MlyValue.designator_list designator_list1,_,
designator_list1right))::(_,(MlyValue.designator designator1,
designator1left,_))::rest671) => let val result=
MlyValue.designator_list(fn _ => let val designator as designator1=
designator1 ()
val designator_list as designator_list1=designator_list1 ()
 in (designator :: designator_list) end
)
 in (LrTable.NT 25,(result,designator1left,designator_list1right),
rest671) end
| (147,(_,(_,_,RBRACKET1right))::(_,(MlyValue.rexpression rexpression1
,_,_))::(_,(_,LBRACKET1left,_))::rest671) => let val result=
MlyValue.designator(fn _ => let val rexpression as rexpression1=
rexpression1 ()
 in (DesignE rexpression) end
)
 in (LrTable.NT 26,(result,LBRACKET1left,RBRACKET1right),rest671) end
| (148,(_,(MlyValue.ID ID1,_,ID1right))::(_,(_,YDOT1left,_))::rest671)
 => let val result=MlyValue.designator(fn _ => let val ID as ID1=ID1 
()
 in (DesignFld (C_field_name ID)) end
)
 in (LrTable.NT 26,(result,YDOT1left,ID1right),rest671) end
| (149,(_,(MlyValue.rexpression rexpression1,rexpression1left,
rexpression1right))::rest671) => let val result=MlyValue.initializer(
fn _ => let val rexpression as rexpression1=rexpression1 ()
 in (wrap(InitE rexpression, eleft rexpression, eright rexpression))
 end
)
 in (LrTable.NT 23,(result,rexpression1left,rexpression1right),rest671
) end
| (150,(_,(_,_,RCURLYright as RCURLY1right))::(_,(
MlyValue.initializer_list initializer_list1,_,_))::(_,(_,LCURLYleft
 as LCURLY1left,_))::rest671) => let val result=MlyValue.initializer(
fn _ => let val initializer_list as initializer_list1=
initializer_list1 ()
 in (wrap(InitList initializer_list, LCURLYleft, RCURLYright)) end
)
 in (LrTable.NT 23,(result,LCURLY1left,RCURLY1right),rest671) end
| (151,(_,(_,YEQ1left,YEQ1right))::rest671) => let val result=
MlyValue.assignop(fn _ => (NONE))
 in (LrTable.NT 56,(result,YEQ1left,YEQ1right),rest671) end
| (152,(_,(_,PLUSEQ1left,PLUSEQ1right))::rest671) => let val result=
MlyValue.assignop(fn _ => (SOME Plus))
 in (LrTable.NT 56,(result,PLUSEQ1left,PLUSEQ1right),rest671) end
| (153,(_,(_,MINUSEQ1left,MINUSEQ1right))::rest671) => let val result=
MlyValue.assignop(fn _ => (SOME Minus))
 in (LrTable.NT 56,(result,MINUSEQ1left,MINUSEQ1right),rest671) end
| (154,(_,(_,BOREQ1left,BOREQ1right))::rest671) => let val result=
MlyValue.assignop(fn _ => (SOME BitwiseOr))
 in (LrTable.NT 56,(result,BOREQ1left,BOREQ1right),rest671) end
| (155,(_,(_,BANDEQ1left,BANDEQ1right))::rest671) => let val result=
MlyValue.assignop(fn _ => (SOME BitwiseAnd))
 in (LrTable.NT 56,(result,BANDEQ1left,BANDEQ1right),rest671) end
| (156,(_,(_,BXOREQ1left,BXOREQ1right))::rest671) => let val result=
MlyValue.assignop(fn _ => (SOME BitwiseXOr))
 in (LrTable.NT 56,(result,BXOREQ1left,BXOREQ1right),rest671) end
| (157,(_,(_,MULEQ1left,MULEQ1right))::rest671) => let val result=
MlyValue.assignop(fn _ => (SOME Times))
 in (LrTable.NT 56,(result,MULEQ1left,MULEQ1right),rest671) end
| (158,(_,(_,DIVEQ1left,DIVEQ1right))::rest671) => let val result=
MlyValue.assignop(fn _ => (SOME Divides))
 in (LrTable.NT 56,(result,DIVEQ1left,DIVEQ1right),rest671) end
| (159,(_,(_,MODEQ1left,MODEQ1right))::rest671) => let val result=
MlyValue.assignop(fn _ => (SOME Modulus))
 in (LrTable.NT 56,(result,MODEQ1left,MODEQ1right),rest671) end
| (160,(_,(_,LSHIFTEQ1left,LSHIFTEQ1right))::rest671) => let val 
result=MlyValue.assignop(fn _ => (SOME LShift))
 in (LrTable.NT 56,(result,LSHIFTEQ1left,LSHIFTEQ1right),rest671) end
| (161,(_,(_,RSHIFTEQ1left,RSHIFTEQ1right))::rest671) => let val 
result=MlyValue.assignop(fn _ => (SOME RShift))
 in (LrTable.NT 56,(result,RSHIFTEQ1left,RSHIFTEQ1right),rest671) end
| (162,(_,(_,_,YSEMIright as YSEMI1right))::(_,(MlyValue.rexpression 
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
| (163,(_,(_,_,YSEMIright as YSEMI1right))::(_,(MlyValue.rexpression 
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
| (164,(_,(MlyValue.statement statement1,_,statement1right))::(_,(
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
| (165,(_,(_,_,YSEMIright as YSEMI1right))::_::(_,(
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
| (166,(_,(MlyValue.statement statement1,_,statement1right))::(_,(
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
| (167,(_,(_,_,YSEMIright as YSEMI1right))::(_,(MlyValue.rexpression 
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
| (168,(_,(_,_,YSEMIright as YSEMI1right))::(_,(_,YRETURNleft as 
YRETURN1left,_))::rest671) => let val result=MlyValue.statement(fn _
 => (swrap(Return NONE, YRETURNleft, YSEMIright)))
 in (LrTable.NT 41,(result,YRETURN1left,YSEMI1right),rest671) end
| (169,(_,(_,_,YSEMIright as YSEMI1right))::(_,(_,YBREAKleft as 
YBREAK1left,_))::rest671) => let val result=MlyValue.statement(fn _
 => (swrap(Break, YBREAKleft, YSEMIright)))
 in (LrTable.NT 41,(result,YBREAK1left,YSEMI1right),rest671) end
| (170,(_,(_,_,YSEMIright as YSEMI1right))::(_,(_,YCONTINUEleft as 
YCONTINUE1left,_))::rest671) => let val result=MlyValue.statement(fn _
 => (swrap(Continue,YCONTINUEleft,YSEMIright)))
 in (LrTable.NT 41,(result,YCONTINUE1left,YSEMI1right),rest671) end
| (171,(_,(MlyValue.statement statement1,_,statement1right))::_::(_,(
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
| (172,(_,(MlyValue.statement statement2,_,statement2right))::_::(_,(
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
| (173,(_,(_,YSEMIleft as YSEMI1left,YSEMIright as YSEMI1right))::
rest671) => let val result=MlyValue.statement(fn _ => (
swrap(EmptyStmt,YSEMIleft,YSEMIright)))
 in (LrTable.NT 41,(result,YSEMI1left,YSEMI1right),rest671) end
| (174,(_,(_,_,YSEMIright as YSEMI1right))::_::(_,(
MlyValue.lexpression lexpression1,lexpression1left,_))::rest671) => 
let val result=MlyValue.statement(fn _ => let val lexpression as 
lexpression1=lexpression1 ()
 in (swrap(postinc lexpression, eleft lexpression, YSEMIright)) end
)
 in (LrTable.NT 41,(result,lexpression1left,YSEMI1right),rest671) end
| (175,(_,(_,_,YSEMIright as YSEMI1right))::_::(_,(
MlyValue.lexpression lexpression1,lexpression1left,_))::rest671) => 
let val result=MlyValue.statement(fn _ => let val lexpression as 
lexpression1=lexpression1 ()
 in (swrap(postdec lexpression, eleft lexpression, YSEMIright)) end
)
 in (LrTable.NT 41,(result,lexpression1left,YSEMI1right),rest671) end
| (176,(_,(_,_,RCURLYright as RCURLY1right))::(_,(
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
| (177,(_,(MlyValue.compound_statement compound_statement1,
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
| (178,(_,(_,_,SPEC_BLOCKEND1right))::(_,(MlyValue.STRING_LITERAL 
STRING_LITERAL1,_,STRING_LITERALright))::(_,(_,AUXUPDleft as 
AUXUPD1left,_))::rest671) => let val result=MlyValue.statement(fn _
 => let val STRING_LITERAL as STRING_LITERAL1=STRING_LITERAL1 ()
 in (swrap(Auxupd STRING_LITERAL, AUXUPDleft, STRING_LITERALright))
 end
)
 in (LrTable.NT 41,(result,AUXUPD1left,SPEC_BLOCKEND1right),rest671)
 end
| (179,(_,(_,_,SPEC_BLOCKEND1right))::(_,(MlyValue.STRING_LITERAL 
STRING_LITERAL1,_,STRING_LITERALright))::(_,(_,GHOSTUPDleft as 
GHOSTUPD1left,_))::rest671) => let val result=MlyValue.statement(fn _
 => let val STRING_LITERAL as STRING_LITERAL1=STRING_LITERAL1 ()
 in (swrap(Ghostupd STRING_LITERAL, GHOSTUPDleft, STRING_LITERALright)
) end
)
 in (LrTable.NT 41,(result,GHOSTUPD1left,SPEC_BLOCKEND1right),rest671)
 end
| (180,(_,(_,_,SPEC_BLOCKEND2right))::(_,(MlyValue.STRING_LITERAL 
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
| (181,(_,(_,_,YSEMIright as YSEMI1right))::_::(_,(MlyValue.asmblock 
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
| (182,rest671) => let val result=MlyValue.optvolatile(fn _ => (false)
)
 in (LrTable.NT 4,(result,defaultPos,defaultPos),rest671) end
| (183,(_,(_,VOLATILE1left,VOLATILE1right))::rest671) => let val 
result=MlyValue.optvolatile(fn _ => (true))
 in (LrTable.NT 4,(result,VOLATILE1left,VOLATILE1right),rest671) end
| (184,(_,(MlyValue.asmmod1 asmmod11,_,asmmod11right))::(_,(
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
| (185,rest671) => let val result=MlyValue.asmmod1(fn _ => ([], [], []
))
 in (LrTable.NT 95,(result,defaultPos,defaultPos),rest671) end
| (186,(_,(MlyValue.asmmod2 asmmod21,_,asmmod21right))::(_,(
MlyValue.namedstringexplist namedstringexplist1,_,_))::(_,(_,
YCOLON1left,_))::rest671) => let val result=MlyValue.asmmod1(fn _ => 
let val namedstringexplist as namedstringexplist1=namedstringexplist1 
()
val asmmod2 as asmmod21=asmmod21 ()
 in (namedstringexplist, #1 asmmod2, #2 asmmod2) end
)
 in (LrTable.NT 95,(result,YCOLON1left,asmmod21right),rest671) end
| (187,rest671) => let val result=MlyValue.asmmod2(fn _ => ([], []))
 in (LrTable.NT 96,(result,defaultPos,defaultPos),rest671) end
| (188,(_,(MlyValue.asmmod3 asmmod31,_,asmmod31right))::(_,(
MlyValue.namedstringexplist namedstringexplist1,_,_))::(_,(_,
YCOLON1left,_))::rest671) => let val result=MlyValue.asmmod2(fn _ => 
let val namedstringexplist as namedstringexplist1=namedstringexplist1 
()
val asmmod3 as asmmod31=asmmod31 ()
 in ((namedstringexplist, asmmod3)) end
)
 in (LrTable.NT 96,(result,YCOLON1left,asmmod31right),rest671) end
| (189,rest671) => let val result=MlyValue.asmmod3(fn _ => ([]))
 in (LrTable.NT 97,(result,defaultPos,defaultPos),rest671) end
| (190,(_,(MlyValue.stringlist1 stringlist11,_,stringlist11right))::(_
,(_,YCOLON1left,_))::rest671) => let val result=MlyValue.asmmod3(fn _
 => let val stringlist1 as stringlist11=stringlist11 ()
 in (stringlist1) end
)
 in (LrTable.NT 97,(result,YCOLON1left,stringlist11right),rest671) end
| (191,(_,(MlyValue.cstring_literal cstring_literal1,
cstring_literal1left,cstring_literal1right))::rest671) => let val 
result=MlyValue.stringlist1(fn _ => let val cstring_literal as 
cstring_literal1=cstring_literal1 ()
 in ([node cstring_literal]) end
)
 in (LrTable.NT 99,(result,cstring_literal1left,cstring_literal1right)
,rest671) end
| (192,(_,(MlyValue.stringlist1 stringlist11,_,stringlist11right))::_
::(_,(MlyValue.cstring_literal cstring_literal1,cstring_literal1left,_
))::rest671) => let val result=MlyValue.stringlist1(fn _ => let val 
cstring_literal as cstring_literal1=cstring_literal1 ()
val stringlist1 as stringlist11=stringlist11 ()
 in (node cstring_literal :: stringlist1) end
)
 in (LrTable.NT 99,(result,cstring_literal1left,stringlist11right),
rest671) end
| (193,rest671) => let val result=MlyValue.namedstringexplist(fn _ => 
([]))
 in (LrTable.NT 101,(result,defaultPos,defaultPos),rest671) end
| (194,(_,(MlyValue.namedstringexplist1 namedstringexplist11,
namedstringexplist11left,namedstringexplist11right))::rest671) => let 
val result=MlyValue.namedstringexplist(fn _ => let val 
namedstringexplist1 as namedstringexplist11=namedstringexplist11 ()
 in (namedstringexplist1) end
)
 in (LrTable.NT 101,(result,namedstringexplist11left,
namedstringexplist11right),rest671) end
| (195,(_,(MlyValue.namedstringexp namedstringexp1,namedstringexp1left
,namedstringexp1right))::rest671) => let val result=
MlyValue.namedstringexplist1(fn _ => let val namedstringexp as 
namedstringexp1=namedstringexp1 ()
 in ([namedstringexp]) end
)
 in (LrTable.NT 102,(result,namedstringexp1left,namedstringexp1right),
rest671) end
| (196,(_,(MlyValue.namedstringexplist1 namedstringexplist11,_,
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
| (197,(_,(_,_,RPAREN1right))::(_,(MlyValue.rexpression rexpression1,_
,_))::_::(_,(MlyValue.cstring_literal cstring_literal1,
cstring_literal1left,_))::rest671) => let val result=
MlyValue.namedstringexp(fn _ => let val cstring_literal as 
cstring_literal1=cstring_literal1 ()
val rexpression as rexpression1=rexpression1 ()
 in ((NONE, node cstring_literal, rexpression)) end
)
 in (LrTable.NT 100,(result,cstring_literal1left,RPAREN1right),rest671
) end
| (198,(_,(_,_,RPAREN1right))::(_,(MlyValue.rexpression rexpression1,_
,_))::_::(_,(MlyValue.cstring_literal cstring_literal1,_,_))::_::(_,(
MlyValue.ID ID1,_,_))::(_,(_,LBRACKET1left,_))::rest671) => let val 
result=MlyValue.namedstringexp(fn _ => let val ID as ID1=ID1 ()
val cstring_literal as cstring_literal1=cstring_literal1 ()
val rexpression as rexpression1=rexpression1 ()
 in ((SOME ID, node cstring_literal, rexpression)) end
)
 in (LrTable.NT 100,(result,LBRACKET1left,RPAREN1right),rest671) end
| (199,(_,(_,_,SPEC_BLOCKEND1right))::(_,(MlyValue.STRING_LITERAL 
STRING_LITERAL1,STRING_LITERALleft,STRING_LITERALright))::(_,(_,
INVARIANT1left,_))::rest671) => let val result=MlyValue.invariant(fn _
 => let val STRING_LITERAL as STRING_LITERAL1=STRING_LITERAL1 ()
 in (wrap(STRING_LITERAL, STRING_LITERALleft, STRING_LITERALright))
 end
)
 in (LrTable.NT 17,(result,INVARIANT1left,SPEC_BLOCKEND1right),rest671
) end
| (200,rest671) => let val result=MlyValue.invariant_option(fn _ => (
NONE))
 in (LrTable.NT 18,(result,defaultPos,defaultPos),rest671) end
| (201,(_,(MlyValue.invariant invariant1,invariant1left,
invariant1right))::rest671) => let val result=
MlyValue.invariant_option(fn _ => let val invariant as invariant1=
invariant1 ()
 in (SOME invariant) end
)
 in (LrTable.NT 18,(result,invariant1left,invariant1right),rest671)
 end
| (202,rest671) => let val result=MlyValue.switchcase_list(fn _ => ([]
))
 in (LrTable.NT 44,(result,defaultPos,defaultPos),rest671) end
| (203,(_,(MlyValue.switchcase_list switchcase_list1,_,
switchcase_list1right))::(_,(MlyValue.switchcase switchcase1,
switchcase1left,_))::rest671) => let val result=
MlyValue.switchcase_list(fn _ => let val switchcase as switchcase1=
switchcase1 ()
val switchcase_list as switchcase_list1=switchcase_list1 ()
 in (switchcase :: switchcase_list) end
)
 in (LrTable.NT 44,(result,switchcase1left,switchcase_list1right),
rest671) end
| (204,(_,(MlyValue.block_item_list block_item_list1,_,
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
| (205,(_,(MlyValue.label label1,label1left,label1right))::rest671)
 => let val result=MlyValue.labellist(fn _ => let val label as label1=
label1 ()
 in (wrap([label], left label, right label)) end
)
 in (LrTable.NT 46,(result,label1left,label1right),rest671) end
| (206,(_,(MlyValue.labellist labellist1,_,labellist1right))::(_,(
MlyValue.label label1,label1left,_))::rest671) => let val result=
MlyValue.labellist(fn _ => let val label as label1=label1 ()
val labellist as labellist1=labellist1 ()
 in (wrap(label::node labellist, left label, right labellist)) end
)
 in (LrTable.NT 46,(result,label1left,labellist1right),rest671) end
| (207,(_,(_,_,YCOLONright as YCOLON1right))::(_,(MlyValue.rexpression
 rexpression1,_,_))::(_,(_,CASEleft as CASE1left,_))::rest671) => let 
val result=MlyValue.label(fn _ => let val rexpression as rexpression1=
rexpression1 ()
 in (wrap(SOME rexpression, CASEleft, YCOLONright)) end
)
 in (LrTable.NT 47,(result,CASE1left,YCOLON1right),rest671) end
| (208,(_,(_,_,YCOLONright as YCOLON1right))::(_,(_,DEFAULTleft as 
DEFAULT1left,_))::rest671) => let val result=MlyValue.label(fn _ => (
wrap(NONE, DEFAULTleft, YCOLONright)))
 in (LrTable.NT 47,(result,DEFAULT1left,YCOLON1right),rest671) end
| (209,(_,(_,_,YSEMI1right))::(_,(MlyValue.opt_for1_expr 
opt_for1_expr1,opt_for1_expr1left,_))::rest671) => let val result=
MlyValue.opt_for1_bitem(fn _ => let val opt_for1_expr as 
opt_for1_expr1=opt_for1_expr1 ()
 in ([BI_Stmt opt_for1_expr]) end
)
 in (LrTable.NT 48,(result,opt_for1_expr1left,YSEMI1right),rest671)
 end
| (210,(_,(MlyValue.declaration declaration1,declaration1left,
declaration1right))::rest671) => let val result=
MlyValue.opt_for1_bitem(fn _ => let val declaration as declaration1=
declaration1 ()
 in (map BI_Decl declaration) end
)
 in (LrTable.NT 48,(result,declaration1left,declaration1right),rest671
) end
| (211,rest671) => let val result=MlyValue.opt_for1_expr(fn _ => (
swrap(EmptyStmt, defaultPos, defaultPos)))
 in (LrTable.NT 49,(result,defaultPos,defaultPos),rest671) end
| (212,(_,(MlyValue.opt_for1_expr0 opt_for1_expr01,opt_for1_expr01left
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
| (213,(_,(MlyValue.opt_for1_exprbase opt_for1_exprbase1,
opt_for1_exprbase1left,opt_for1_exprbase1right))::rest671) => let val 
result=MlyValue.opt_for1_expr0(fn _ => let val opt_for1_exprbase as 
opt_for1_exprbase1=opt_for1_exprbase1 ()
 in ([opt_for1_exprbase]) end
)
 in (LrTable.NT 50,(result,opt_for1_exprbase1left,
opt_for1_exprbase1right),rest671) end
| (214,(_,(MlyValue.opt_for1_expr0 opt_for1_expr01,_,
opt_for1_expr01right))::_::(_,(MlyValue.opt_for1_exprbase 
opt_for1_exprbase1,opt_for1_exprbase1left,_))::rest671) => let val 
result=MlyValue.opt_for1_expr0(fn _ => let val opt_for1_exprbase as 
opt_for1_exprbase1=opt_for1_exprbase1 ()
val opt_for1_expr0 as opt_for1_expr01=opt_for1_expr01 ()
 in (opt_for1_exprbase::opt_for1_expr0) end
)
 in (LrTable.NT 50,(result,opt_for1_exprbase1left,opt_for1_expr01right
),rest671) end
| (215,(_,(MlyValue.rexpression rexpression1,_,rexpression1right))::_
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
| (216,rest671) => let val result=MlyValue.opt_for2_expr(fn _ => (
expr_int 1))
 in (LrTable.NT 52,(result,defaultPos,defaultPos),rest671) end
| (217,(_,(MlyValue.rexpression rexpression1,rexpression1left,
rexpression1right))::rest671) => let val result=MlyValue.opt_for2_expr
(fn _ => let val rexpression as rexpression1=rexpression1 ()
 in (rexpression) end
)
 in (LrTable.NT 52,(result,rexpression1left,rexpression1right),rest671
) end
| (218,rest671) => let val result=MlyValue.opt_for3_expr(fn _ => (
swrap(EmptyStmt,defaultPos,defaultPos)))
 in (LrTable.NT 53,(result,defaultPos,defaultPos),rest671) end
| (219,(_,(MlyValue.opt_for3_expr0 opt_for3_expr01,opt_for3_expr01left
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
| (220,(_,(MlyValue.opt_for3_exprbase opt_for3_exprbase1,
opt_for3_exprbase1left,opt_for3_exprbase1right))::rest671) => let val 
result=MlyValue.opt_for3_expr0(fn _ => let val opt_for3_exprbase as 
opt_for3_exprbase1=opt_for3_exprbase1 ()
 in ([opt_for3_exprbase]) end
)
 in (LrTable.NT 54,(result,opt_for3_exprbase1left,
opt_for3_exprbase1right),rest671) end
| (221,(_,(_,_,SPEC_BLOCKEND1right))::(_,(MlyValue.STRING_LITERAL 
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
| (222,(_,(MlyValue.opt_for3_expr0 opt_for3_expr01,_,
opt_for3_expr01right))::_::(_,(MlyValue.opt_for3_exprbase 
opt_for3_exprbase1,opt_for3_exprbase1left,_))::rest671) => let val 
result=MlyValue.opt_for3_expr0(fn _ => let val opt_for3_exprbase as 
opt_for3_exprbase1=opt_for3_exprbase1 ()
val opt_for3_expr0 as opt_for3_expr01=opt_for3_expr01 ()
 in (opt_for3_exprbase::opt_for3_expr0) end
)
 in (LrTable.NT 54,(result,opt_for3_exprbase1left,opt_for3_expr01right
),rest671) end
| (223,(_,(MlyValue.rexpression rexpression1,_,rexpression1right))::(_
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
| (224,(_,(_,_,PLUSPLUSright as PLUSPLUS1right))::(_,(
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
| (225,(_,(_,_,MINUSMINUSright as MINUSMINUS1right))::(_,(
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
| (226,rest671) => let val result=MlyValue.opt_rexpr_list(fn _ => (
wrap([], defaultPos, defaultPos)))
 in (LrTable.NT 73,(result,defaultPos,defaultPos),rest671) end
| (227,(_,(MlyValue.rexpr_list rexpr_list1,rexpr_list1left,
rexpr_list1right))::rest671) => let val result=MlyValue.opt_rexpr_list
(fn _ => let val rexpr_list as rexpr_list1=rexpr_list1 ()
 in (rexpr_list) end
)
 in (LrTable.NT 73,(result,rexpr_list1left,rexpr_list1right),rest671)
 end
| (228,(_,(MlyValue.rexpression rexpression1,rexpression1left,
rexpression1right))::rest671) => let val result=MlyValue.rexpr_list(
fn _ => let val rexpression as rexpression1=rexpression1 ()
 in (
wrap([rexpression], eleft rexpression,
                               eright rexpression)
) end
)
 in (LrTable.NT 72,(result,rexpression1left,rexpression1right),rest671
) end
| (229,(_,(MlyValue.rexpr_list rexpr_list1,_,rexpr_list1right))::_::(_
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
| (230,(_,(MlyValue.logical_OR_expression logical_OR_expression1,
logical_OR_expression1left,logical_OR_expression1right))::rest671) => 
let val result=MlyValue.rexpression(fn _ => let val 
logical_OR_expression as logical_OR_expression1=logical_OR_expression1
 ()
 in (logical_OR_expression) end
)
 in (LrTable.NT 71,(result,logical_OR_expression1left,
logical_OR_expression1right),rest671) end
| (231,(_,(MlyValue.rexpression rexpression2,_,rexpression2right))::_
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
| (232,(_,(MlyValue.logical_AND_expression logical_AND_expression1,
logical_AND_expression1left,logical_AND_expression1right))::rest671)
 => let val result=MlyValue.logical_OR_expression(fn _ => let val 
logical_AND_expression as logical_AND_expression1=
logical_AND_expression1 ()
 in (logical_AND_expression) end
)
 in (LrTable.NT 75,(result,logical_AND_expression1left,
logical_AND_expression1right),rest671) end
| (233,(_,(MlyValue.logical_AND_expression logical_AND_expression1,_,
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
| (234,(_,(MlyValue.inclusive_OR_expression inclusive_OR_expression1,
inclusive_OR_expression1left,inclusive_OR_expression1right))::rest671)
 => let val result=MlyValue.logical_AND_expression(fn _ => let val 
inclusive_OR_expression as inclusive_OR_expression1=
inclusive_OR_expression1 ()
 in (inclusive_OR_expression) end
)
 in (LrTable.NT 74,(result,inclusive_OR_expression1left,
inclusive_OR_expression1right),rest671) end
| (235,(_,(MlyValue.inclusive_OR_expression inclusive_OR_expression1,_
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
| (236,(_,(MlyValue.exclusive_OR_expression exclusive_OR_expression1,
exclusive_OR_expression1left,exclusive_OR_expression1right))::rest671)
 => let val result=MlyValue.inclusive_OR_expression(fn _ => let val 
exclusive_OR_expression as exclusive_OR_expression1=
exclusive_OR_expression1 ()
 in (exclusive_OR_expression) end
)
 in (LrTable.NT 76,(result,exclusive_OR_expression1left,
exclusive_OR_expression1right),rest671) end
| (237,(_,(MlyValue.exclusive_OR_expression exclusive_OR_expression1,_
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
| (238,(_,(MlyValue.AND_expression AND_expression1,AND_expression1left
,AND_expression1right))::rest671) => let val result=
MlyValue.exclusive_OR_expression(fn _ => let val AND_expression as 
AND_expression1=AND_expression1 ()
 in (AND_expression) end
)
 in (LrTable.NT 77,(result,AND_expression1left,AND_expression1right),
rest671) end
| (239,(_,(MlyValue.AND_expression AND_expression1,_,
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
| (240,(_,(MlyValue.equality_expression equality_expression1,
equality_expression1left,equality_expression1right))::rest671) => let 
val result=MlyValue.AND_expression(fn _ => let val equality_expression
 as equality_expression1=equality_expression1 ()
 in (equality_expression) end
)
 in (LrTable.NT 78,(result,equality_expression1left,
equality_expression1right),rest671) end
| (241,(_,(MlyValue.equality_expression equality_expression1,_,
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
| (242,(_,(MlyValue.relational_expression relational_expression1,
relational_expression1left,relational_expression1right))::rest671) => 
let val result=MlyValue.equality_expression(fn _ => let val 
relational_expression as relational_expression1=relational_expression1
 ()
 in (relational_expression) end
)
 in (LrTable.NT 79,(result,relational_expression1left,
relational_expression1right),rest671) end
| (243,(_,(MlyValue.relational_expression relational_expression1,_,
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
| (244,(_,(MlyValue.relational_expression relational_expression1,_,
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
| (245,(_,(MlyValue.shift_expression shift_expression1,
shift_expression1left,shift_expression1right))::rest671) => let val 
result=MlyValue.relational_expression(fn _ => let val shift_expression
 as shift_expression1=shift_expression1 ()
 in (shift_expression) end
)
 in (LrTable.NT 80,(result,shift_expression1left,
shift_expression1right),rest671) end
| (246,(_,(MlyValue.shift_expression shift_expression1,_,
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
| (247,(_,(MlyValue.shift_expression shift_expression1,_,
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
| (248,(_,(MlyValue.shift_expression shift_expression1,_,
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
| (249,(_,(MlyValue.shift_expression shift_expression1,_,
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
| (250,(_,(MlyValue.additive_expression additive_expression1,
additive_expression1left,additive_expression1right))::rest671) => let 
val result=MlyValue.shift_expression(fn _ => let val 
additive_expression as additive_expression1=additive_expression1 ()
 in (additive_expression) end
)
 in (LrTable.NT 82,(result,additive_expression1left,
additive_expression1right),rest671) end
| (251,(_,(MlyValue.additive_expression additive_expression1,_,
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
| (252,(_,(MlyValue.additive_expression additive_expression1,_,
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
| (253,(_,(MlyValue.multiplicative_expression 
multiplicative_expression1,multiplicative_expression1left,
multiplicative_expression1right))::rest671) => let val result=
MlyValue.additive_expression(fn _ => let val multiplicative_expression
 as multiplicative_expression1=multiplicative_expression1 ()
 in (multiplicative_expression) end
)
 in (LrTable.NT 81,(result,multiplicative_expression1left,
multiplicative_expression1right),rest671) end
| (254,(_,(MlyValue.multiplicative_expression 
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
| (255,(_,(MlyValue.multiplicative_expression 
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
| (256,(_,(MlyValue.cast_expression cast_expression1,
cast_expression1left,cast_expression1right))::rest671) => let val 
result=MlyValue.multiplicative_expression(fn _ => let val 
cast_expression as cast_expression1=cast_expression1 ()
 in (cast_expression) end
)
 in (LrTable.NT 83,(result,cast_expression1left,cast_expression1right)
,rest671) end
| (257,(_,(MlyValue.cast_expression cast_expression1,_,
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
| (258,(_,(MlyValue.cast_expression cast_expression1,_,
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
| (259,(_,(MlyValue.cast_expression cast_expression1,_,
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
| (260,(_,(MlyValue.unary_expression unary_expression1,
unary_expression1left,unary_expression1right))::rest671) => let val 
result=MlyValue.cast_expression(fn _ => let val unary_expression as 
unary_expression1=unary_expression1 ()
 in (unary_expression) end
)
 in (LrTable.NT 85,(result,unary_expression1left,
unary_expression1right),rest671) end
| (261,(_,(MlyValue.cast_expression cast_expression1,_,
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
| (262,(_,(MlyValue.postfix_expression postfix_expression1,
postfix_expression1left,postfix_expression1right))::rest671) => let 
val result=MlyValue.unary_expression(fn _ => let val 
postfix_expression as postfix_expression1=postfix_expression1 ()
 in (postfix_expression) end
)
 in (LrTable.NT 84,(result,postfix_expression1left,
postfix_expression1right),rest671) end
| (263,(_,(MlyValue.cast_expression cast_expression1,_,
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
| (264,(_,(MlyValue.cast_expression cast_expression1,_,
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
| (265,(_,(MlyValue.cast_expression cast_expression1,_,
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
| (266,(_,(MlyValue.cast_expression cast_expression1,_,
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
| (267,(_,(MlyValue.cast_expression cast_expression1,_,
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
| (268,(_,(MlyValue.unary_expression unary_expression1,_,
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
| (269,(_,(_,_,RPARENright as RPAREN1right))::(_,(MlyValue.type_name 
type_name1,_,_))::_::(_,(_,YSIZEOFleft as YSIZEOF1left,_))::rest671)
 => let val result=MlyValue.unary_expression(fn _ => let val type_name
 as type_name1=type_name1 ()
 in (ewrap(SizeofTy type_name, YSIZEOFleft, RPARENright)) end
)
 in (LrTable.NT 84,(result,YSIZEOF1left,RPAREN1right),rest671) end
| (270,(_,(MlyValue.primary_expression primary_expression1,
primary_expression1left,primary_expression1right))::rest671) => let 
val result=MlyValue.postfix_expression(fn _ => let val 
primary_expression as primary_expression1=primary_expression1 ()
 in (primary_expression) end
)
 in (LrTable.NT 86,(result,primary_expression1left,
primary_expression1right),rest671) end
| (271,(_,(_,_,RBRACKETright as RBRACKET1right))::(_,(
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
| (272,(_,(_,_,RPARENright as RPAREN1right))::(_,(
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
| (273,(_,(MlyValue.ID ID1,_,IDright as ID1right))::_::(_,(
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
| (274,(_,(MlyValue.ID ID1,_,IDright as ID1right))::_::(_,(
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
| (275,(_,(_,_,RCURLYright as RCURLY1right))::(_,(
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
| (276,(_,(MlyValue.ID ID1,IDleft as ID1left,IDright as ID1right))::
rest671) => let val result=MlyValue.primary_expression(fn _ => let 
val ID as ID1=ID1 ()
 in (ewrap(Var (ID, ref NONE), IDleft, IDright)) end
)
 in (LrTable.NT 87,(result,ID1left,ID1right),rest671) end
| (277,(_,(MlyValue.constant constant1,constant1left,constant1right))
::rest671) => let val result=MlyValue.primary_expression(fn _ => let 
val constant as constant1=constant1 ()
 in (ewrap(Constant constant, left constant, right constant)) end
)
 in (LrTable.NT 87,(result,constant1left,constant1right),rest671) end
| (278,(_,(_,_,RPARENright as RPAREN1right))::(_,(MlyValue.rexpression
 rexpression1,_,_))::(_,(_,LPARENleft as LPAREN1left,_))::rest671) => 
let val result=MlyValue.primary_expression(fn _ => let val rexpression
 as rexpression1=rexpression1 ()
 in (ewrap(enode rexpression, LPARENleft, RPARENright)) end
)
 in (LrTable.NT 87,(result,LPAREN1left,RPAREN1right),rest671) end
| (279,(_,(MlyValue.cstring_literal cstring_literal1,
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
| (280,(_,(MlyValue.STRING_LITERAL STRING_LITERAL1,_,
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
| (281,(_,(MlyValue.STRING_LITERAL STRING_LITERAL1,STRING_LITERALleft
 as STRING_LITERAL1left,STRING_LITERALright as STRING_LITERAL1right))
::rest671) => let val result=MlyValue.cstring_literal(fn _ => let val 
STRING_LITERAL as STRING_LITERAL1=STRING_LITERAL1 ()
 in (wrap(STRING_LITERAL, STRING_LITERALleft, STRING_LITERALright))
 end
)
 in (LrTable.NT 98,(result,STRING_LITERAL1left,STRING_LITERAL1right),
rest671) end
| (282,(_,(MlyValue.NUMERIC_CONSTANT NUMERIC_CONSTANT1,
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
| (283,(_,(MlyValue.postfix_expression postfix_expression1,
postfix_expression1left,postfix_expression1right))::rest671) => let 
val result=MlyValue.lexpression(fn _ => let val postfix_expression as 
postfix_expression1=postfix_expression1 ()
 in (postfix_expression) end
)
 in (LrTable.NT 70,(result,postfix_expression1left,
postfix_expression1right),rest671) end
| (284,(_,(MlyValue.cast_expression cast_expression1,_,
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
fun NORETURN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 81,(
ParserData.MlyValue.VOID',p1,p2))
fun THREAD_LOCAL (p1,p2) = Token.TOKEN (ParserData.LrTable.T 82,(
ParserData.MlyValue.VOID',p1,p2))
fun AUTO (p1,p2) = Token.TOKEN (ParserData.LrTable.T 83,(
ParserData.MlyValue.VOID',p1,p2))
fun FNSPEC (p1,p2) = Token.TOKEN (ParserData.LrTable.T 84,(
ParserData.MlyValue.VOID',p1,p2))
fun RELSPEC (p1,p2) = Token.TOKEN (ParserData.LrTable.T 85,(
ParserData.MlyValue.VOID',p1,p2))
fun AUXUPD (p1,p2) = Token.TOKEN (ParserData.LrTable.T 86,(
ParserData.MlyValue.VOID',p1,p2))
fun GHOSTUPD (p1,p2) = Token.TOKEN (ParserData.LrTable.T 87,(
ParserData.MlyValue.VOID',p1,p2))
fun MODIFIES (p1,p2) = Token.TOKEN (ParserData.LrTable.T 88,(
ParserData.MlyValue.VOID',p1,p2))
fun CALLS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 89,(
ParserData.MlyValue.VOID',p1,p2))
fun OWNED_BY (p1,p2) = Token.TOKEN (ParserData.LrTable.T 90,(
ParserData.MlyValue.VOID',p1,p2))
fun SPEC_BEGIN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 91,(
ParserData.MlyValue.VOID',p1,p2))
fun SPEC_END (p1,p2) = Token.TOKEN (ParserData.LrTable.T 92,(
ParserData.MlyValue.VOID',p1,p2))
fun DONT_TRANSLATE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 93,(
ParserData.MlyValue.VOID',p1,p2))
fun STRING_LITERAL (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 94,(
ParserData.MlyValue.STRING_LITERAL (fn () => i),p1,p2))
fun SPEC_BLOCKEND (p1,p2) = Token.TOKEN (ParserData.LrTable.T 95,(
ParserData.MlyValue.VOID',p1,p2))
fun GCC_ATTRIBUTE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 96,(
ParserData.MlyValue.VOID',p1,p2))
fun YASM (p1,p2) = Token.TOKEN (ParserData.LrTable.T 97,(
ParserData.MlyValue.VOID',p1,p2))
fun YREGISTER (p1,p2) = Token.TOKEN (ParserData.LrTable.T 98,(
ParserData.MlyValue.VOID',p1,p2))
end
end
