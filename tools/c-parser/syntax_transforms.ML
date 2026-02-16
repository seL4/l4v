(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

signature FUN_RM =
sig
  (* Statement lists. *)
  type stmt_list
  val stmt_list_of : Absyn.statement list -> stmt_list
  val of_stmt_list : stmt_list -> Absyn.statement list
  val @@ : stmt_list * stmt_list -> stmt_list
  val @> : stmt_list * Absyn.statement list -> Absyn.statement list
  val empty : stmt_list -> bool
  (* A monad for extracting function calls that are embedded in expressions. *)
  type 'rv fun_rm
  val run : 'a fun_rm -> stmt_list * 'a
  val run' : unit fun_rm -> Absyn.statement list
  val scope_pre : 'a fun_rm -> ('a -> 'b fun_rm) -> (stmt_list * 'b) fun_rm
  val scope_stmts : unit fun_rm -> Absyn.statement list fun_rm
  val scope_rv : 'a fun_rm -> 'a fun_rm
  val add_stmts : stmt_list -> unit fun_rm
  val add_stmts_fst : (stmt_list * 'a) -> 'a fun_rm
  val add_stmt : Absyn.statement -> unit fun_rm
  val next_sym : string -> int fun_rm
  val return : 'a -> 'a fun_rm
  val pass : ('a -> unit fun_rm) -> 'a -> 'a fun_rm
  val >- : 'a fun_rm * ('a -> 'b fun_rm) -> 'b fun_rm
  val <:> : 'a fun_rm * 'b fun_rm -> ('a * 'b) fun_rm
  val >> : unit fun_rm * 'b fun_rm -> 'b fun_rm
  val <$ : ('a -> 'b) * 'a fun_rm -> 'b fun_rm
  val $> : 'a fun_rm * ('a -> 'b) -> 'b fun_rm
  val mmap : ('a -> 'b fun_rm) -> 'a list -> 'b list fun_rm
end

structure FunRm :> FUN_RM =
struct

infix @@ @> >- <*> <$ $> <:> >>

fun (f >- g) (syms, stmts) = let
  val (syms', stmts', rv_f) = f (syms, stmts)
in
  g rv_f (syms', stmts')
end

fun return v (syms, stmts) = (syms, stmts, v)
fun f <*> g = f >- (fn f' => g >- return o f')
fun f <$ g = return f <*> g
fun f $> g = g <$ f
fun f <:> g = pair <$ f <*> g
fun f >> g = snd <$ (f <:> g)
fun pass f x = f x >> return x

fun mmap _ [] = return []
  | mmap f (h::t) = cons <$ f h <*> mmap f t

(* A difference list that is most likely a premature optimisation.
   The `option` allows testing for emptiness. *)
type stmt_list = (Absyn.statement list ->  Absyn.statement list) option
fun stmt_list_of xs = if null xs then NONE else SOME (fn ys => xs @ ys)
fun empty NONE = true
  | empty _ = false
fun NONE @> ys = ys
  | (SOME xs) @> ys = xs ys
fun NONE @@ ys = ys
  | xs @@ NONE = xs
  | (SOME xs) @@ (SOME ys) = SOME (xs o ys)
fun of_stmt_list xs = xs @> []

(* A state monad for extracting function calls that are embedded in expressions.
   Expressions rendered to SIMPL cannot contain SIMPL procedure calls. We therefore
   extract any function calls embedded in an expression to new statements placed just
   before whichever statement contained the expression. We replace each original function
   call with a temporary variable which takes the value returned by the extracted function.
   `fun_rm` provides support for tracking the temporary variables used, and the new
   statements emitted for the extracted function calls.
   The state consists of a bag of symbols used for temporary variables and
   a list of accumulated program statements. Since we always append statements to the tail
   of the list, we store the list of statements as a difference list. This accumulation
   of statements effectively makes this a writer monad, but it's more convenient to
   implement as a state monad. *)
type 'rv fun_rm = int Symtab.table * stmt_list -> int Symtab.table * stmt_list * 'rv

fun add_stmts new_stmts (syms, stmts) = (syms, stmts @@ new_stmts, ())
fun add_stmts_fst (stmts, rv) = add_stmts stmts >> return rv
fun add_stmt s = add_stmts (stmt_list_of [s])

fun next_sym name (syms, stmts) = let
  val i = case Symtab.lookup syms name of NONE => 1 | SOME i => i + 1
in
  (Symtab.update (name, i) syms, stmts, i)
end

fun run f = let
  (* Once we're done executing the action, we don't need the symbol table any more,
     since the temporary variables won't be referenced again. *)
  val (_, stmts, rv) = f (Symtab.empty, NONE)
in
  (stmts, rv)
end

(* When extracting function calls embedded in expressions with conditional and
   short-circuit operators, we might need to generate conditional statements.
   Procedure calls extracted from sub-expressions that are only conditionally
   evaluated in the C semantics should be scoped to the appropriate branch of
   such a conditional statement.
   The `scope` operator allows inner scopes to be embedded in outer scopes for
   this purpose. *)
fun scope_pre alloc f (outer_syms, outer_stmts) = let
  (* The `alloc` action is executed in the outer scope before `f` is executed
     in the inner scope. Any variables allocated by `alloc` remain free to be
     allocated by `f` in the inner scope, but are not free on return to the
     outer scope. This is a hack to preserve compatibility with older proofs in
     some obscure cases. It can be used to allocate variables that are to be
     assigned only at the end of the inner scope, without preventing the inner
     scope from first using those variables for its own purposes. *)
  val (outer_syms', outer_stmts', vars) = alloc (outer_syms, outer_stmts)
  (* We assume that any variables allocated in the inner scope are not live on
     return to the outer scope, so we can drop the inner scope's symbol table.
     This means that `scope` can also be useful for avoiding unnecessary variable
     allocations in unconditionally evaluated subexpressions, when it's known that
     any variables allocated by the inner scope will only be used in statements
     that will be immediately emitted by the outer scope. *)
  val (_, inner_stmts, rv) = f vars (outer_syms, NONE)
in
  (* Return the statements accumulated inside the scope, and continue with the
     symbol table and statements for the outer scope.
     It's the outer scope's responsibility to do something appropriate with the
     returned statements. *)
  (outer_syms', outer_stmts', (inner_stmts, rv))
end

val run' = of_stmt_list o #1 o run
fun scope_plain f = scope_pre (return ()) (K f)
fun scope_stmts f = scope_plain f $> of_stmt_list o #1
fun scope_rv f = scope_plain f >- add_stmts_fst

end

signature SYNTAX_TRANSFORMS =
sig
  type program = Absyn.ext_decl list
  val remove_typedefs : program -> program
  val remove_embedded_fncalls : ProgramAnalysis.csenv -> program -> program
  val remove_anonstructs : program -> program
end;


structure SyntaxTransforms : SYNTAX_TRANSFORMS =
struct

type program = Absyn.ext_decl list
open Absyn Basics

fun extend_env newbinds [] = [newbinds] (* shouldn't happen *)
  | extend_env newbinds (h::t) = (newbinds @ h) :: t

fun env_lookup(env, k) =
    case env of
      [] => NONE
    | e::es => (case assoc(e, k) of
                  NONE => env_lookup(es, k)
                | x => x)

fun update_type env (ty : Absyn.expr ctype) : Absyn.expr ctype =
    case ty of
      Ptr ty0 => Ptr (update_type env ty0)
    | Array (ty0, n) => Array(update_type env ty0,
                              Option.map (remove_expr_typedefs env) n)
    | Ident s => (case env_lookup(env, s) of
                    NONE => raise Fail ("No typedef for "^s)
                  | SOME ty => update_type env ty)
    | _ => ty
and remove_expr_typedefs env expr = let
  val ret = remove_expr_typedefs env
  val rit = remove_init_typedefs env
  val rdt = remove_designator_typedefs env
  val l = eleft expr
  val r = eright expr
  fun w en = ewrap (en, l, r)
  val updty = update_type env
  val updtyw = apnode updty
in
  case enode expr of
    BinOp(bop,e1,e2) => w(BinOp(bop, ret e1, ret e2))
  | UnOp(unop, e) => w(UnOp(unop, ret e))
  | CondExp(e1,e2,e3) => w(CondExp(ret e1, ret e2, ret e3))
  | StructDot(e,s) => w(StructDot(ret e, s))
  | ArrayDeref(e1, e2) => w(ArrayDeref(ret e1, ret e2))
  | Deref e => w(Deref (ret e))
  | Sizeof e => w(Sizeof (ret e))
  | SizeofTy ty => w(SizeofTy (updtyw ty))
  | TypeCast(ty,e) => w(TypeCast(updtyw ty, ret e))
  | EFnCall(fnnm,elist) => w(EFnCall(fnnm, map ret elist))
  | CompLiteral(ty, dis) =>
       w(CompLiteral(updty ty,
                     map (fn (ds,i) => (map rdt ds, rit i)) dis))
  | Arbitrary ty => w(Arbitrary (update_type env ty))
  | _ => expr
end
and remove_init_typedefs env i = let
  val ret = remove_expr_typedefs env
  val rit = remove_init_typedefs env
  val rdt = remove_designator_typedefs env
in
  case i of
    InitE e => InitE (ret e)
  | InitList ilist => InitList (map (fn (ds,i) => (map rdt ds, rit i)) ilist)
end
and remove_designator_typedefs env d =
    case d of
      DesignE e => DesignE (remove_expr_typedefs env e)
    | DesignFld _ => d



fun remove_decl_typedefs env d =
  case d of
    VarDecl (basety,name,is_extern,iopt,attrs) => let
    in
      (SOME (VarDecl (update_type env basety, name, is_extern,
                      Option.map (remove_init_typedefs env) iopt,
                      attrs)),
       env)
    end
  | StructDecl (sname, tys) =>
      (SOME (StructDecl (sname, map (apfst (update_type env)) tys)), env)
  | TypeDecl tys => let
      val newrhs = map (fn (ty, nm) => (node nm, update_type env ty)) tys
    in
      (NONE, extend_env newrhs env)
    end
  | ExtFnDecl {rettype, name, params, specs} => let
    in
      (SOME (ExtFnDecl{ rettype = update_type env rettype,
                        name = name,
                        params = map (apfst (update_type env)) params,
                        specs = specs}),
       env)
    end
  | EnumDecl (sw, ecs) => let
      fun ecmap (sw, eopt) = (sw, Option.map (remove_expr_typedefs env) eopt)
    in
      (SOME (EnumDecl (sw, map ecmap ecs)), env)
    end
  | StaticAssertion {condition, message} => let
    in
      (SOME (StaticAssertion { condition = (remove_expr_typedefs env) condition,
                               message = message }),
       env)
    end

val bogus = SourcePos.bogus

fun remove_stmt_typedefs env stmt = let
  val ret = remove_expr_typedefs env
  val rst = remove_stmt_typedefs env
  fun w st = swrap(st, sleft stmt, sright stmt)
in
  case snode stmt of
    Assign(e1, e2) => w(Assign(ret e1, ret e2))
  | AssignFnCall(fopt,s,args) => w(AssignFnCall(Option.map ret fopt, s,
                                                map ret args))
  | Block b => w(Block (#2 (remove_body_typedefs env b)))
  | Chaos e => w(Chaos(ret e))
  | While(g,sopt,body) => w(While(ret g, sopt, rst body))
  | Trap(tty,s) => w(Trap(tty, rst s))
  | Return eopt => w(Return (Option.map ret eopt))
  | ReturnFnCall (s,args) => w(ReturnFnCall(s,map ret args))
  | IfStmt(g,s1,s2) => w(IfStmt(ret g, rst s1, rst s2))
  | Switch(g,bilist) => let
      val g' = ret g
      fun foldthis ((eoptlist, bilist), (env,acc)) = let
        val eoptlist' = map (Option.map ret) eoptlist
        val (env', bilist') = remove_body_typedefs env bilist
      in
        (env', ((eoptlist',bilist') :: acc))
      end
      val (_, bilist') = List.foldr foldthis (env,[]) bilist
    in
      w(Switch(g',bilist'))
    end
  | EmptyStmt => stmt
  | Auxupd _ => stmt
  | Ghostupd _ => stmt
  | Spec _ => stmt
  | Break => stmt
  | Continue => stmt
  | AsmStmt _ => stmt
  | _ => raise Fail ("remove_stmt_typedefs: unhandled type - "^stmt_type stmt)
end
and remove_body_typedefs env bilist =
    case bilist of
      [] => (env, [])
    | BI_Stmt st :: rest => let
        val st' = BI_Stmt (remove_stmt_typedefs env st)
        val (env', rest') = remove_body_typedefs env rest
      in
        (env', st' :: rest')
      end
    | BI_Decl d :: rest => let
        val (dopt, env') = remove_decl_typedefs env (node d)
        val (env'', rest') = remove_body_typedefs env' rest
      in
        case dopt of
          NONE => (env'', rest')
        | SOME d' => (env'', BI_Decl (wrap(d',left d,right d)) :: rest')
      end




fun remove_typedefs p = let
  fun transform acc env p =
      case p of
        [] => List.rev acc
      | e::es => let
        in
          case e of
            Decl d => let
              val (dopt, env') = remove_decl_typedefs env (node d)
            in
              case dopt of
                NONE => transform acc env' es
              | SOME d' => transform (Decl (wrap (d',left d, right d))::acc)
                                     env' es
            end
          | FnDefn ((retty, s), params, prepost, body) => let
              val params' = map (apfst (update_type env)) params
              val retty' = update_type env retty
              val (_, body') = remove_body_typedefs env (node body)
              val wbody = wrap(body', left body, right body)
              val newfn = FnDefn((retty', s), params', prepost, wbody)
            in
              transform (newfn :: acc) env es
            end
        end
in
  transform [] [] p
end

(* set up little state-transformer monad *)
open NameGeneration

infix @> >- <:> >> <$ $>
fun x @> y = FunRm.@> (x,y)
fun f >- g = FunRm.>- (f,g)
fun f <:> g = FunRm.<:> (f,g)
fun f >> g = FunRm.>> (f,g)
fun f <$ g = FunRm.<$ (f,g)
fun f $> g = FunRm.$> (f,g)

fun ex_remove_embfncalls cse = let
  fun new_var (ty,l,r) = let
    val rtype_n = tyname ty
    fun mk_var temp_i = let
      val nm = embret_var_name (rtype_n, temp_i)
      val mvinfo = MungedVar {munge = nm, owned_by = NONE}
    in
      ewrap(Var (MString.dest nm, ref (SOME (ty, mvinfo))), l, r)
    end
  in
    FunRm.next_sym rtype_n $> mk_var
  end

  fun new_call (l,r) fn_e args = let
    open ProgramAnalysis
    val (_, (rty, _)) = fndes_callinfo cse fn_e
  in
    new_var (rty, eleft fn_e, eright fn_e)
    >- FunRm.pass (fn v => FunRm.add_stmt (swrap(EmbFnCall(v,fn_e,args), l, r)))
  end

  fun ex_remove_embfncalls e = let
    fun w e0 = ewrap(e0, eleft e, eright e)
  in
    case enode e of
      BinOp(bop,e1,e2) => let
        val scp = bop = LogOr orelse bop = LogAnd
      in
        if scp andalso eneeds_sc_protection e2 then
          guard_translate e
        else
          ex_remove_embfncalls e1 <:> ex_remove_embfncalls e2
          $> (fn (e1',e2') => w(BinOp(bop,e1',e2')))
      end
    | UnOp(uop,e) =>  ex_remove_embfncalls e $> (fn e' => w(UnOp(uop,e')))
    | CondExp (g,t,e) => let
      in
        if eneeds_sc_protection t orelse eneeds_sc_protection e
        then let
          val t_ty = ProgramAnalysis.cse_typing cse t
          val e_ty = ProgramAnalysis.cse_typing cse e
          val branch_type = unify_types(t_ty, e_ty)
          fun create_if v g' = let
            fun ex e = ex_remove_embfncalls e >- (fn e => FunRm.add_stmt (sbogwrap(Assign(v,e))))
            fun bl e = FunRm.scope_stmts (ex e) $> sbogwrap o Block o map BI_Stmt
          in
            bl t <:> bl e >- (fn (t',e') => FunRm.add_stmt (sbogwrap(IfStmt(g',t',e'))))
            >> FunRm.return v
          end
        in
          (* The variable is only used in the assignment at the end of each branch,
             so it's safe for the branches to use the same variable prior to the assignment.
             We allow this for compatibility with existing proofs. *)
          FunRm.scope_pre (new_var (branch_type, eleft g, eright g))
                          (fn v => FunRm.scope_rv (ex_remove_embfncalls g) >- create_if v)
          >- FunRm.add_stmts_fst
        end
        else
          ex_remove_embfncalls g <:> ex_remove_embfncalls t <:> ex_remove_embfncalls e
          $> (fn ((g',t'),e') => w(CondExp(g',t',e')))
      end
    | Var _ => FunRm.return e
    | Constant _ => FunRm.return e
    | StructDot (e,fld) => ex_remove_embfncalls e $> (fn e' => w(StructDot(e',fld)))
    | ArrayDeref(e1,e2) => ex_remove_embfncalls e1 <:> ex_remove_embfncalls e2 $> w o ArrayDeref
    | Deref e => ex_remove_embfncalls e $> w o Deref
    | TypeCast(ty,e) => ex_remove_embfncalls e $> (fn e' => w(TypeCast(ty,e')))
    | Sizeof _ => FunRm.return e
    | SizeofTy _ => FunRm.return e
    | CompLiteral (ty,dis) => FunRm.mmap di_rm_efncalls dis $> (fn dis' => w(CompLiteral(ty,dis')))
    | EFnCall(fn_e,args) => FunRm.mmap ex_remove_embfncalls args
                            >- new_call (eleft e, eright e) fn_e
    | Arbitrary _ => FunRm.return e
    | _ => raise Fail ("ex_remove_embfncalls: couldn't handle: " ^ expr_string e)
  end
  and i_rm_efncalls i =
      case i of
        InitE e => InitE <$ ex_remove_embfncalls e
      | InitList dis => InitList <$ FunRm.mmap di_rm_efncalls dis
  and di_rm_efncalls (d,i) = pair d <$ i_rm_efncalls i
  and linearise e v = let
    fun lin e1 e2 p = FunRm.scope_rv (linearise e1 v)
                      >> FunRm.scope_stmts (linearise e2 v) >- FunRm.add_stmt o p v
    fun pos v stmts = sbogwrap(IfStmt(v,sbogwrap(Block (map BI_Stmt stmts)),sbogwrap EmptyStmt))
    fun neg v stmts = sbogwrap(IfStmt(v,sbogwrap EmptyStmt,sbogwrap(Block (map BI_Stmt stmts))))
    fun assign v e = sbogwrap(Assign(v,ebogwrap(MKBOOL e)))
  in
    case enode e of
        BinOp(LogAnd, e1, e2) => lin e1 e2 pos
      | BinOp(LogOr, e1, e2) => lin e1 e2 neg
      | _ => ex_remove_embfncalls e >- FunRm.add_stmt o assign v
  end
  and guard_translate e =
      (* The variable is assigned at the end of each branch, and then immediately read
         in the condition for the next branch. It's otherwise unused by `linearise`,
         so it's safe for the branches to use the same variable prior to the assignment.
         We allow this for compatibility with existing proofs. *)
      FunRm.scope_pre (new_var (Signed Int, eleft e, eright e))
                      (FunRm.pass (linearise e))
      >- FunRm.add_stmts_fst
in
  ex_remove_embfncalls
end

fun decl_remove_embfncalls _ (* cse *) d = (d, [])

fun bitem_remove_embfncalls cse = let
  val decl_remove_embfncalls = decl_remove_embfncalls cse
  fun bitem_remove_embfncalls bi =
      case bi of
        BI_Decl dw => let
          val (d', sts) = decl_remove_embfncalls (node dw)
        in
          (map BI_Stmt sts @ [BI_Decl (wrap(d', left dw, right dw))])
        end
      | BI_Stmt st => map BI_Stmt (stmt_remove_embfncalls st)
  and stmt_remove_embfncalls st = let
    val ex_remove_embfncalls = ex_remove_embfncalls cse
    fun w s = swrap(s, sleft st, sright st)
    val bog_empty = swrap(EmptyStmt,bogus,bogus)
    fun mk_single [] = bog_empty
      | mk_single [st] = st
      | mk_single rest = swrap(Block(map BI_Stmt rest), sleft (hd rest),
                               sright (List.last rest))
  in
    case snode st of
      Assign(e1,e2) =>
        FunRm.run' (ex_remove_embfncalls e1 <:> ex_remove_embfncalls e2
                    >- FunRm.add_stmt o w o Assign)
    | AssignFnCall(tgt,fnm,args) =>
        (* don't need to consider tgt as parser ensures this is always a simple
           object reference (field reference or variable) *)
        FunRm.run' (FunRm.mmap ex_remove_embfncalls args
                    >- (fn args' => FunRm.add_stmt (w(AssignFnCall(tgt,fnm,args')))))
    | Block bilist =>
        [w(Block (List.concat (map bitem_remove_embfncalls bilist)))]
    | Chaos e => FunRm.run' (ex_remove_embfncalls e >- FunRm.add_stmt o w o Chaos)
    | While(g,spec,body) => let
        val (gsts, g') = FunRm.run (ex_remove_embfncalls g)
        val body' = stmt_remove_embfncalls body
      in
        if FunRm.empty gsts andalso length body' = 1 then
          [w(While(g',spec,hd body'))]
        else
          gsts @> [w(While(g', spec, swrap(Block (map BI_Stmt (body' @ FunRm.of_stmt_list gsts)),
                                          sleft body,
                                          sright body)))]
      end
    | Trap(tty, s) => let
        val s' = stmt_remove_embfncalls s
      in
        [w(Trap(tty,mk_single s'))]
      end
    | Return (SOME e) => FunRm.run' (ex_remove_embfncalls e >- FunRm.add_stmt o w o Return o SOME)
    | Return NONE => [st]
    | ReturnFnCall (fnm, args) =>
        FunRm.run' (FunRm.mmap ex_remove_embfncalls args
                    >- (fn args' => FunRm.add_stmt (w(ReturnFnCall(fnm,args')))))
    | Break => [st]
    | Continue => [st]
    | IfStmt(g,tst,est) => let
        val (gsts, g') = FunRm.run (ex_remove_embfncalls g)
        val tst' = stmt_remove_embfncalls tst
        val est' = stmt_remove_embfncalls est
      in
        gsts @> [w(IfStmt(g', mk_single tst', mk_single est'))]
      end
    | Switch(g,cases) => let
        val (gsts, g') = FunRm.run (ex_remove_embfncalls g)
        fun mapthis (labs,bis) =
            (labs, List.concat (map bitem_remove_embfncalls bis))
      in
        gsts @> [w(Switch(g', map mapthis cases))]
      end
    | EmptyStmt => [st]
    | Auxupd _ => [st]
    | Ghostupd _ => [st]
    | Spec _ => [st]
    | AsmStmt _ => [st]
    | LocalInit _ => [st]
    | _ => raise Fail ("stmt_remove_embfncalls: Couldn't handle " ^ stmt_type st)
  end
in
  bitem_remove_embfncalls
end

fun extdecl_remove_embfncalls cse e =
    case e of
      FnDefn ((retty,nm),params,spec,body) => let
        val body' = List.concat (map (bitem_remove_embfncalls cse) (node body))
      in
        FnDefn((retty,nm),params,spec,wrap(body',left body,right body))
      end
    | Decl d => let
        val (d', sts) = decl_remove_embfncalls cse d
      in
        if null sts then Decl d'
        else (!Feedback.warnf("Not handling initialisation of global \
                              \variables");
              Decl d')
      end

fun remove_embedded_fncalls cse = map (extdecl_remove_embfncalls cse)

fun tysubst th ty =
    case ty of
        StructTy s => (case Symtab.lookup th s of
                           NONE => ty
                         | SOME s' => StructTy s')
      | Ptr ty => Ptr (tysubst th ty)
      | Array (ty, sz) => Array (tysubst th ty, sz)
      | Function (retty, args) => Function (tysubst th retty,
                                            map (tysubst th) args)
      | _ => ty

fun ws th strw =
  let
    fun strf s = case Symtab.lookup th s of NONE => s | SOME s' => s'
  in
    apnode strf strw
  end

fun dsubst th d =
    case d of
        StructDecl (nmw, flds) => StructDecl (ws th nmw, map (apfst (tysubst th)) flds)
      | VarDecl(ty, nm, b, iopt, attrs) =>
          VarDecl(tysubst th ty, nm, b, iopt, attrs)
      | TypeDecl tnms => TypeDecl (map (apfst (tysubst th)) tnms)
      | _ => d

fun edsubst th ed =
    case ed of
        FnDefn _ => ed
      | Decl d => Decl (apnode (dsubst th) d)

fun calctheta (edec, acc as (i, th)) =
    case edec of
        FnDefn _ => acc
      | Decl dw =>
        (case node dw of
             StructDecl (nmw, _) =>
             let
               val oldnm = node nmw
               open NameGeneration
             in
               if String.isPrefix internalAnonStructPfx oldnm then
                 let
                   val newnm = mkAnonStructName i
                 in
                   (i + 1, Symtab.update (oldnm, newnm) th)
                 end
               else
                 acc
             end
           | _ => acc)

fun remove_anonstructs edecs =
  let
    val (_, theta) = List.foldl calctheta (1, Symtab.empty) edecs
  in
    map (edsubst theta) edecs
  end

end (* struct *)
