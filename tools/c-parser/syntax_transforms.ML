(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

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

infix >> >-
fun (f >- g) m = let
  val (m',result) = f m
in
  g result m'
end
fun (f >> g) = f >- (fn _ => g)
fun return v m = (m,v)
fun mmap f list =
    case list of
      [] => return []
    | h::t => f h >- (fn h' => mmap f t >- (fn t' => return (h'::t')))

fun new_var (ty,l,r) (embmap, calls) = let
  val rtype_n = tyname ty

  val temp_i = case Symtab.lookup embmap rtype_n of
                 NONE => 1
               | SOME i => i + 1
  val nm = embret_var_name (rtype_n, temp_i)
  val mvinfo = MungedVar{munge = nm, owned_by = NONE}
  val temp = ewrap(Var (MString.dest nm, ref (SOME (ty, mvinfo))), l, r)
  val emb' = Symtab.update (rtype_n, temp_i) embmap
in
  ((emb',calls), temp)
end


fun add_stmts stmts (embmap,sts) = ((embmap, sts @ stmts), ())
fun add_stmt st = add_stmts [st]

fun new_call cse fn_e args (l,r) = let
  open ProgramAnalysis
  val (_, (rty, _)) = fndes_callinfo cse fn_e
in
  new_var (rty, eleft fn_e, eright fn_e) >- (fn temp =>
  add_stmt (swrap(EmbFnCall(temp,fn_e,args), l, r)) >>
  return temp)
end

val bogus_empty = sbogwrap EmptyStmt

fun poscond v stmts =
    sbogwrap(IfStmt(v,sbogwrap(Block (map BI_Stmt stmts)),bogus_empty))
fun negcond v stmts =
    sbogwrap(IfStmt(v,bogus_empty,sbogwrap(Block (map BI_Stmt stmts))))
fun assign (v, e) = sbogwrap(Assign(v,ebogwrap(MKBOOL e)))



fun ex_remove_embfncalls cse e = let
  val doit = ex_remove_embfncalls cse
  fun w e0 = ewrap(e0,eleft e,eright e)
in
  case enode e of
    BinOp(bop,e1,e2) => let
      val scp = bop = LogOr orelse bop = LogAnd
    in
      if scp andalso eneeds_sc_protection e2 then
        guard_translate cse e
      else
        doit e1 >- (fn e1' =>
        doit e2 >- (fn e2' =>
        return (w(BinOp(bop,e1',e2')))))
    end
  | UnOp(uop,e) => doit e >- (fn e' => return (w(UnOp(uop, e'))))
  | CondExp (g,t,e) => let
    in
      if eneeds_sc_protection t orelse eneeds_sc_protection e then let
          val t_ty = ProgramAnalysis.cse_typing cse t
          val e_ty = ProgramAnalysis.cse_typing cse e
          val branch_type = unify_types(t_ty, e_ty)
              handle Fail _ => t_ty (* error will have already been reported
                                       in process_decls pass *)
          val sbw = sbogwrap
          val (g',gsts) = expr_remove_embfncalls cse g
          val (t',tsts) = expr_remove_embfncalls cse t
          val (e',ests) = expr_remove_embfncalls cse e
          fun create_if v = let
            val tbr = sbw(Block (map BI_Stmt (tsts @ [sbw(Assign(v,t'))])))
            val ebr = sbw(Block (map BI_Stmt (ests @ [sbw(Assign(v,e'))])))
          in
            add_stmts (gsts @ [sbw(IfStmt(g',tbr,ebr))]) >>
            return v
          end
        in
          new_var (branch_type,eleft g,eright g) >- create_if
        end
      else
        doit g >- (fn g' =>
        doit t >- (fn t' =>
        doit e >- (fn e' =>
        return (w(CondExp (g',t',e'))))))
    end
  | Var _ => return e
  | Constant _ => return e
  | StructDot (e,fld) => doit e >- (fn e' => return (w(StructDot(e',fld))))
  | ArrayDeref(e1,e2) => doit e1 >- (fn e1' =>
                         doit e2 >- (fn e2' =>
                         return (w(ArrayDeref(e1',e2')))))
  | Deref e => doit e >- return o w o Deref
  | TypeCast(ty,e) => doit e >- (fn e' => return (w(TypeCast(ty,e'))))
  | Sizeof _ => return e
  | SizeofTy _ => return e
  | CompLiteral (ty,dis) => mmap (di_rm_efncalls cse) dis >- (fn dis' =>
                            return (w(CompLiteral(ty,dis'))))
  | EFnCall(fn_e,args) => let
    in
      mmap doit args >- (fn args' =>
      new_call cse fn_e args' (eleft e, eright e) >- (fn temp =>
      return temp))
    end
  | Arbitrary _ => return e
  | _ => raise Fail ("ex_remove_embfncalls: couldn't handle: " ^ expr_string e)
end
and i_rm_efncalls cse i =
    case i of
      InitE e => ex_remove_embfncalls cse e >- return o InitE
    | InitList dis => mmap (di_rm_efncalls cse) dis >- return o InitList
and di_rm_efncalls cse (d,i) = i_rm_efncalls cse i >- (fn i' => return (d,i'))
and linearise cse v e = let
  val lin = linearise cse v
in
  case enode e of
    BinOp(LogAnd, e1, e2) => lin e1 @ [poscond v (lin e2)]
  | BinOp(LogOr, e1, e2) => lin e1 @ [negcond v (lin e2)]
  | _ => let
      val (e',sts) = expr_remove_embfncalls cse e
    in
      sts @ [assign(v,e')]
    end
end
and guard_translate cse e = let
  fun stage2 guardvar = let
  in
    add_stmts (linearise cse guardvar e) >>
    return guardvar
  end
in
  new_var (Signed Int,eleft e,eright e) >- stage2
end
and expr_remove_embfncalls cse e = let
  val ((_, sts), e') = ex_remove_embfncalls cse e (Symtab.empty, [])
in
  (e', sts)
end

fun decl_remove_embfncalls _ (*cse*) d = (d, [])

fun bitem_remove_embfncalls cse bi =
    case bi of
      BI_Decl dw => let
        val (d',sts) = decl_remove_embfncalls cse (node dw)
      in
        (map BI_Stmt sts @ [BI_Decl (wrap(d',left dw,right dw))])
      end
    | BI_Stmt st => map BI_Stmt (stmt_remove_embfncalls cse st)
and stmt_remove_embfncalls cse st = let
  val expr_remove_embfncalls = expr_remove_embfncalls cse
  val stmt_remove_embfncalls = stmt_remove_embfncalls cse
  fun w s = swrap(s,sleft st, sright st)
  val bog_empty = swrap(EmptyStmt,bogus,bogus)
  fun mk_single [] = bog_empty
    | mk_single [st] = st
    | mk_single rest = swrap(Block(map BI_Stmt rest), sleft (hd rest),
                             sright (List.last rest))
in
  case snode st of
    Assign(e1,e2) => let
      val (e1',sts1) = expr_remove_embfncalls e1
      val (e2',sts2) = expr_remove_embfncalls e2
    in
      sts1 @ sts2 @ [w(Assign(e1',e2'))]
    end
  | AssignFnCall(tgt,fnm,args) => let
      (* don't need to consider tgt as parser ensures this is always a simple
         object reference (field reference or variable) *)
      val ((_, sts), args') =
          mmap (ex_remove_embfncalls cse) args (Symtab.empty, [])
    in
      sts @ [w(AssignFnCall(tgt,fnm,args'))]
    end
  | Block bilist =>
      [w(Block (List.concat (map (bitem_remove_embfncalls cse) bilist)))]
  | Chaos e =>
    let
      val (e',sts) = expr_remove_embfncalls e
    in
      sts @ [w(Chaos e')]
    end
  | While(g,spec,body) => let
      val (g', gsts) = expr_remove_embfncalls g
      val body' = stmt_remove_embfncalls body
    in
      if null gsts andalso length body' = 1 then
        [w(While(g',spec,hd body'))]
      else
        gsts @ [w(While(g',spec, swrap(Block (map BI_Stmt (body' @ gsts)),
                                       sleft body,
                                       sright body)))]
    end
  | Trap(tty, s) => let
      val s' = stmt_remove_embfncalls s
    in
      [w(Trap(tty,mk_single s'))]
    end
  | Return (SOME e) => let
      val (e', sts) = expr_remove_embfncalls e
    in
      sts @ [w(Return(SOME e'))]
    end
  | Return NONE => [st]
  | ReturnFnCall (fnm, args) => let
      val ((_, sts), args') =
          mmap (ex_remove_embfncalls cse) args (Symtab.empty, [])
    in
      sts @ [w(ReturnFnCall(fnm,args'))]
    end
  | Break => [st]
  | Continue => [st]
  | IfStmt(g,tst,est) => let
      val (g',gsts) = expr_remove_embfncalls g
      val tst' = stmt_remove_embfncalls tst
      val est' = stmt_remove_embfncalls est
    in
      gsts @ [w(IfStmt(g',mk_single tst', mk_single est'))]
    end
  | Switch(g,cases) => let
      val (g',gsts) = expr_remove_embfncalls g
      fun mapthis (labs,bis) =
          (labs, List.concat (map (bitem_remove_embfncalls cse) bis))
    in
      gsts @ [w(Switch(g',map mapthis cases))]
    end
  | EmptyStmt => [st]
  | Auxupd _ => [st]
  | Ghostupd _ => [st]
  | Spec _ => [st]
  | AsmStmt _ => [st]
  | LocalInit _ => [st]
  | _ => raise Fail ("stmt_remove_embfncalls: Couldn't handle " ^ stmt_type st)
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
