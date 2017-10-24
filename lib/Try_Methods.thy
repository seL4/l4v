(*
 *
 * Copyright 2017, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory Try_Methods

imports Eisbach_Methods

keywords "trym" :: diag
  and "add_try_method" :: thy_decl

begin

text {*
A collection of methods that can be "tried" against subgoals (similar
to try, try0 etc). It is easy to add new methods with "add_try_method",
although the parser currently supports only single names.

Particular subgoals can be tried with "trym 1" etc. By default all
subgoals are attempted unless they are coupled to others by shared
schematic variables.
*}

ML {*
structure Try_Methods = struct

structure Methods = Theory_Data
(
  type T = Symtab.set;
  val empty = Symtab.empty;
  val extend = I;
  val merge = Symtab.merge (K true);
);

val get_methods_global = Methods.get #> Symtab.keys
val add_method = Methods.map o Symtab.insert_set

(* borrowed from try0 implementation (of course) *)
fun parse_method_name keywords =
  enclose "(" ")"
  #> Token.explode keywords Position.start
  #> filter Token.is_proper
  #> Scan.read Token.stopper Method.parse
  #> (fn SOME (Method.Source src, _) => src | _ => raise Fail "expected Source");

fun mk_method ctxt = parse_method_name (Thy_Header.get_keywords' ctxt)
  #> Method.method_cmd ctxt
  #> Method.Basic

fun get_methods ctxt = get_methods_global (Proof_Context.theory_of ctxt)
  |> map (mk_method ctxt)

fun try_one_method m ctxt n goal
    = can (Timeout.apply (Time.fromSeconds 5)
        (Goal.restrict n 1 #> Method.NO_CONTEXT_TACTIC ctxt
            (Method.evaluate_runtime m ctxt [])
            #> Seq.hd
    )) goal

fun msg m_nm n = writeln ("method " ^ m_nm ^ " succceeded on goal " ^ string_of_int n)

fun times xs ys = maps (fn x => map (pair x) ys) xs

fun independent_subgoals goal verbose = let
    fun get_vars t = Term.fold_aterms
        (fn (Var v) => Termtab.insert_set (Var v) | _ => I)
        t Termtab.empty
    val goals = Thm.prems_of goal
    val goal_vars = map get_vars goals
    val count_vars = fold (fn t1 => fn t2 => Termtab.join (K (op +))
        (Termtab.map (K (K 1)) t1, t2)) goal_vars Termtab.empty
    val indep_vars = Termtab.forall (fst #> Termtab.lookup count_vars
        #> (fn n => n = SOME 1))
    val indep = (1 upto Thm.nprems_of goal) ~~ map indep_vars goal_vars
    val _ = app (fst #> string_of_int
        #> prefix "ignoring non-independent goal " #> warning)
        (filter (fn x => verbose andalso not (snd x)) indep)
  in indep |> filter snd |> map fst end

fun try_methods opt_n ctxt goal = let
    val ms = get_methods_global (Proof_Context.theory_of ctxt)
        ~~ get_methods ctxt
    val ns = case opt_n of
        NONE => independent_subgoals goal true
      | SOME n => [n]
    fun apply ((m_nm, m), n) = if try_one_method m ctxt n goal
      then (msg m_nm n; SOME (m_nm, n)) else NONE
    val results = Par_List.map apply (times ms ns)
  in map_filter I results end

fun try_methods_command opt_n st = let
    val ctxt = #context (Proof.goal st)
        |> Try0.silence_methods false
    val goal = #goal (Proof.goal st)
  in try_methods opt_n ctxt goal; () end

val _ = Outer_Syntax.command @{command_keyword trym}
  "try methods from a library of specialised strategies"
  (Scan.option Parse.int >> (fn opt_n =>
    Toplevel.keep_proof (try_methods_command opt_n o Toplevel.proof_of)))

fun local_check_add_method nm ctxt =
    (mk_method ctxt nm; Local_Theory.background_theory (add_method nm) ctxt)

val _ = Outer_Syntax.command @{command_keyword add_try_method}
  "add a method to a library of strategies tried by trym"
  (Parse.name >> (Toplevel.local_theory NONE NONE o local_check_add_method))

end
*}

add_try_method fastforce
add_try_method blast
add_try_method metis

method auto_metis = solves \<open>auto; metis\<close>
add_try_method auto_metis

end