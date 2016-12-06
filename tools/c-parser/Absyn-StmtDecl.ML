(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

structure StmtDeclDatatype =
struct

type expr = Expr.expr
type initializer = Expr.initializer
type 'a ctype = 'a CType.ctype
type 'a wrap = 'a RegionExtras.wrap
datatype gcc_attribute = GCC_AttribID of string
                       | GCC_AttribFn of string * expr list
                       | OWNED_BY of string

datatype fnspec = fnspec of string wrap
                | relspec of string wrap
                | fn_modifies of string list
                | didnt_translate
                | gcc_attribs of gcc_attribute list

datatype storage_class =
         SC_EXTERN | SC_STATIC | SC_AUTO | SC_REGISTER | SC_THRD_LOCAL

datatype declaration =
         VarDecl of (expr ctype *
                     string wrap *
                     storage_class list *
                     initializer option *
                     gcc_attribute list)
         (* VarDecl's bool is true if the declaration is not an extern;
            if the declaration is "genuine".
            The accompanying optional initialiser is only used to calculate the
            size of an array when a declaration like
              int a[] = {...}
            is made.
            Initialisers are translated into subsequent assignment statements
            by the parser. *)
       | StructDecl of string wrap * (expr ctype * string wrap) list
       | TypeDecl of (expr ctype * string wrap) list
       | ExtFnDecl of {rettype : expr ctype, name : string wrap,
                       params : (expr ctype * string option) list,
                       specs : fnspec list}
       | EnumDecl of string option wrap * (string wrap * expr option) list

type namedstringexp = string option * string * expr

type asmblock = {head : string,
                 mod1 : namedstringexp list,
                 mod2 : namedstringexp list,
                 mod3 : string list}
(* if mod_i is empty, then so too are all mod_j for j > i *)

datatype trappable = BreakT | ContinueT


datatype statement_node =
         Assign of expr * expr
       | AssignFnCall of expr option * expr * expr list (* lval, fn, args *)
       | Chaos of expr
       | EmbFnCall of expr * expr * expr list (* lval, fn, args *)
       | Block of block_item list
       | While of expr * string wrap option * statement
       | Trap of trappable * statement
       | Return of expr option
       | ReturnFnCall of expr * expr list
       | Break | Continue
       | IfStmt of expr * statement * statement
       | Switch of expr * (expr option list * block_item list) list
       | EmptyStmt
       | Auxupd of string
       | Ghostupd of string
       | Spec of ((string * string) * statement list * string)
       | AsmStmt of {volatilep : bool, asmblock : asmblock}
       | LocalInit of expr
and statement = Stmt of statement_node Region.Wrap.t
and block_item =
    BI_Stmt of statement
  | BI_Decl of declaration wrap

type body = block_item list wrap

datatype ext_decl =
         FnDefn of (expr ctype * string wrap) * (expr ctype * string wrap) list *
                   fnspec list (* fnspec *) * body
       | Decl of declaration wrap

end

signature STMT_DECL =
sig
  datatype gcc_attribute = datatype StmtDeclDatatype.gcc_attribute
  datatype storage_class = datatype StmtDeclDatatype.storage_class
  datatype fnspec = datatype StmtDeclDatatype.fnspec
  datatype declaration = datatype StmtDeclDatatype.declaration
  datatype trappable = datatype StmtDeclDatatype.trappable
  datatype statement_node = datatype StmtDeclDatatype.statement_node
  type statement
  type asmblock = StmtDeclDatatype.asmblock
  type namedstringexp = StmtDeclDatatype.namedstringexp
  datatype block_item = datatype StmtDeclDatatype.block_item
  datatype ext_decl = datatype StmtDeclDatatype.ext_decl

  val merge_specs : fnspec list -> fnspec list -> fnspec list
  val has_IDattribute : (string -> bool) -> fnspec list -> string option
  val all_IDattributes : fnspec list -> string Binaryset.set
  val get_owned_by : gcc_attribute list -> string option
  val fnspec2string : fnspec -> string

  val snode : statement -> statement_node
  val swrap : statement_node * SourcePos.t * SourcePos.t -> statement
  val sbogwrap : statement_node -> statement
  val sleft : statement -> SourcePos.t
  val sright : statement -> SourcePos.t

  val stmt_type : statement -> string

  val stmt_fail : statement * string -> exn

  val is_extern : storage_class list -> bool
  val is_static : storage_class list -> bool

  val sub_stmts : statement -> statement list

end

structure StmtDecl : STMT_DECL =
struct

open StmtDeclDatatype RegionExtras Expr

fun attr2string (GCC_AttribID s) = s
  | attr2string (GCC_AttribFn(s, _)) = s ^ "(...)"
  | attr2string (OWNED_BY s) = "[OWNED_BY "^s^"]"

fun has_IDattribute P fspecs = let
  val search_gccattrs = get_first
                            (fn GCC_AttribID s => if P s then SOME s else NONE
                              | _ => NONE)
  fun oneP fspec =
      case fspec of
        gcc_attribs attrs => search_gccattrs attrs
      | _ => NONE
in
  get_first oneP fspecs
end

fun all_IDattributes fspecs = let
  fun getID (GCC_AttribID s, acc) = Binaryset.add(acc,s) | getID (_,acc) = acc
  fun getGCCs (gcc_attribs attrs, acc) = List.foldl getID acc attrs
    | getGCCs (_,acc) = acc
in
  List.foldl getGCCs (Binaryset.empty String.compare) fspecs
end

fun get_owned_by gattrs =
    case gattrs of
        [] => NONE
      | OWNED_BY s :: _ => SOME s
      | _ :: rest => get_owned_by rest



val commas = String.concat o separate ","
fun fnspec2string fs =
    case fs of
      fnspec s => "fnspec: "^node s
    | fn_modifies slist => "MODIFIES: "^String.concat (separate " " slist)
    | didnt_translate => "DONT_TRANSLATE"
    | gcc_attribs attrs => "__attribute__((" ^ commas (map attr2string attrs) ^
                           "))"
    | relspec s => "relspec: "^node s


fun collapse_mod_attribs sp = let
  local
    open Binaryset
  in
  fun IL (NONE, slist) = SOME (addList(empty String.compare, slist))
    | IL (SOME s, slist) = SOME (addList(s, slist))
  end
  fun recurse (acc as (mods, attribs, specs)) sp =
      case sp of
        [] => acc
      | s :: rest => let
        in
          case s of
            fn_modifies slist => recurse (IL (mods, slist), attribs, specs) rest
          | gcc_attribs gs => recurse (mods, Library.union op= gs attribs,
                                       specs)
                                      rest
          | _ => recurse (mods, attribs, s::specs) rest
        end
  val (mods, attribs, specs) = recurse (NONE, [], []) sp
  val mods = Option.map Binaryset.listItems mods
  val mods' = case mods of NONE => [] | SOME l => [fn_modifies l]
  val attribs' = case attribs of [] => [] | _ => [gcc_attribs attribs]
in
  mods' @ attribs' @ specs
end

fun merge_specs sp1 sp2 = collapse_mod_attribs (sp1 @ sp2)


fun sleft (Stmt w) = left w
fun sright (Stmt w) = right w
fun swrap (s, l, r) = Stmt(wrap(s,l,r))
fun snode (Stmt w) = node w
fun sbogwrap s = Stmt(wrap(s,bogus,bogus))

fun stmt_type s =
    case snode s of
      Assign _ => "Assign"
    | AssignFnCall _ => "AssignFnCall"
    | EmbFnCall _ => "EmbFnCall"
    | Block _ => "Block"
    | Chaos _ => "Chaos"
    | While _ => "While"
    | Trap _ => "Trap"
    | Return _ => "Return"
    | ReturnFnCall _ => "ReturnFnCall"
    | Break => "Break"
    | Continue => "Continue"
    | IfStmt _ => "IfStmt"
    | Switch _ => "Switch"
    | EmptyStmt => "EmptyStmt"
    | Auxupd _ => "Auxupd"
    | Spec _ => "Spec"
    | AsmStmt _ => "AsmStmt"
    | LocalInit _ => "LocalInit"
    | _ => "[whoa!  Unknown stmt type]"

fun map_concat f ss = map f ss |> List.concat

fun sub_stmts s =
    case snode s of
      Block bis => map_concat bi_stmts bis
    | While (_, _, s) => [s]
    | Trap (_, s) => [s]
    | IfStmt (_, l, r) => [l, r]
    | Switch (_, sws) => map_concat (map_concat bi_stmts o snd) sws
    | Spec (_, ss, _) => ss
    | _ => []
and bi_stmts (BI_Stmt s) = sub_stmts s
  | bi_stmts _ = []

fun stmt_fail (Stmt w, msg) =
    Fail (Region.toString (Region.Wrap.region w) ^ ": " ^ msg)

val is_extern = List.exists (fn x => x = SC_EXTERN)
val is_static = List.exists (fn x => x = SC_STATIC)

end
