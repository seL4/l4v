(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory GraphLang

imports
  "CParser.TypHeapLib"
  "Lib.SplitRule"
  "CommonOps"

begin

text \<open>Note that machine states here are assumed to be countable and
are thus represented by naturals.\<close>

datatype variable =
    VarNone
  | VarWord8 word8
  | VarWord16 word16
  | VarWord32 word32
  | VarWord64 word64
  | VarMem "machine_word \<Rightarrow> word8"
  | VarDom "machine_word set"
  | VarGhostState "ghost_assertions"
  | VarHTD "heap_typ_desc"
  | VarMS "unit \<times> nat"
  | VarBool bool

text \<open>States are a mapping from names to the variable type, which is
a union of the available names.\<close>

datatype state = State "string \<Rightarrow> variable"

text \<open>Accessors for grabbing variables by name and expected type.\<close>

definition
  "var_acc nm st = (case st of State f \<Rightarrow> f nm)"

definition
  "var_word8 nm st = (case var_acc nm st of
    VarWord8 w \<Rightarrow> w | _ \<Rightarrow> 0)"

definition
  "var_word16 nm st = (case var_acc nm st of
    VarWord16 w \<Rightarrow> w | _ \<Rightarrow> 0)"

definition
  "var_word32 nm st = (case var_acc nm st of
    VarWord32 w \<Rightarrow> w | _ \<Rightarrow> 0)"

definition
  "var_word64 nm st = (case var_acc nm st of
    VarWord64 w \<Rightarrow> w | _ \<Rightarrow> 0)"

definition
  "var_ghoststate nm st = (case var_acc nm st of
    VarGhostState arr \<Rightarrow> arr | _ \<Rightarrow> (\<lambda>_. 0))"

definition
  "var_mem nm st = (case var_acc nm st of
    VarMem m \<Rightarrow> m | _ \<Rightarrow> \<lambda>_. 0)"

definition
  "var_dom nm st = (case var_acc nm st of
    VarDom d \<Rightarrow> d | _ \<Rightarrow> {})"

definition
  "var_htd nm st = (case var_acc nm st of
    VarHTD htd \<Rightarrow> htd | _ \<Rightarrow> empty_htd)"

definition
  "var_ms nm st = (case var_acc nm st of
    VarMS ms \<Rightarrow> ms | _ \<Rightarrow> ((), 0))"

definition
  "var_bool nm st = (case var_acc nm st of
    VarBool bool \<Rightarrow> bool | _ \<Rightarrow> False)"

text \<open>The variable updator.\<close>

definition
  "var_upd nm v st = (case st of State f \<Rightarrow> State (f (nm := v)))"

definition
  "default_state = State (\<lambda>_. VarNone)"

text \<open>The type of nodes.\<close>

datatype next_node =
    NextNode nat | Ret | Err

datatype node =
    Basic next_node "(string \<times> (state \<Rightarrow> variable)) list"
  | Cond next_node next_node "state \<Rightarrow> bool"
  | Call next_node string "(state \<Rightarrow> variable) list" "string list"

definition Skip where
  "Skip nn = Cond nn nn (\<lambda>x. True)"

text \<open>The type for a total graph function, including list of inputs,
  list of outputs, graph, and entry point.\<close>

datatype graph_function
  = GraphFunction "string list" "string list" "nat \<Rightarrow> node option" nat

primrec entry_point where
  "entry_point (GraphFunction inputs outputs graph ep) = ep"

primrec function_graph where
  "function_graph (GraphFunction inputs outputs graph ep) = graph"

primrec function_inputs where
  "function_inputs (GraphFunction inputs outputs graph ep) = inputs"

primrec function_outputs where
  "function_outputs (GraphFunction inputs outputs graph ep) = outputs"

text \<open>The definition of execution, including a stack to allow function calls.\<close>

definition
  save_vals :: "string list \<Rightarrow> variable list \<Rightarrow> state \<Rightarrow> state"
where
 "save_vals vars vals st = fold (\<lambda>(var, val). var_upd var val) (zip vars vals) st"

definition
  init_vars :: "string list \<Rightarrow> (state \<Rightarrow> variable) list \<Rightarrow> state \<Rightarrow> state"
where
  "init_vars vars accs st = save_vals vars (map (\<lambda>i. i st) accs) default_state"

definition
  acc_vars :: "string list \<Rightarrow> state \<Rightarrow> variable list"
where
  "acc_vars vars st = map (\<lambda>v. var_acc v st) vars"

definition
  return_vars :: "string list \<Rightarrow> string list \<Rightarrow> state \<Rightarrow> state \<Rightarrow> state"
where
  "return_vars inner outer inner_st = save_vals outer (acc_vars inner inner_st)"

definition
  upd_vars :: "(string \<times> (state \<Rightarrow> variable)) list \<Rightarrow> state \<Rightarrow> state"
where
  "upd_vars upds st = save_vals (map fst upds) (map (\<lambda>(nm, vf). vf st) upds) st"

type_synonym stack = "(next_node \<times> state \<times> string) list"

primrec
  upd_stack :: "next_node \<Rightarrow> (state \<Rightarrow> state) \<Rightarrow> stack \<Rightarrow> stack"
where
    "upd_stack nn stf (x # xs) = (nn, stf (fst (snd x)), snd (snd x)) # xs"
  | "upd_stack nn stf [] = []"

primrec
  exec_node :: "(string \<Rightarrow> graph_function option)
        \<Rightarrow> state \<Rightarrow> node \<Rightarrow> stack \<Rightarrow> stack set"
where
    "exec_node Gamma st (Basic cont upds) stack
        = {upd_stack cont (K (upd_vars upds st)) stack}"
  | "exec_node Gamma st (Cond left right cond) stack
        = {upd_stack (if cond st then left else right) id stack}"
  | "exec_node Gamma st (Call cont fname inputs outputs) stack
        = (case Gamma fname of None \<Rightarrow> {upd_stack Err id stack}
            | Some (GraphFunction inps outps graph ep)
                \<Rightarrow> {(NextNode ep, init_vars inps inputs st, fname)
                        # stack})"

primrec
  exec_node_return :: "(string \<Rightarrow> graph_function option)
        \<Rightarrow> state \<Rightarrow> node \<Rightarrow> stack \<Rightarrow> stack set"
where
    "exec_node_return _ _ (Basic _ _) stack = {}"
  | "exec_node_return _ _ (Cond _ _ _) stack = {}"
  | "exec_node_return Gamma st (Call cont fname inputs outputs) stack
        = (case Gamma fname of None \<Rightarrow> {}
            | Some (GraphFunction inps outps graph ep)
                \<Rightarrow> {upd_stack cont (return_vars outps outputs st) stack})"

text \<open>The single-step relation on graph states.\<close>

definition
  exec_graph_step :: "(string \<Rightarrow> graph_function option)
        \<Rightarrow> (stack \<times> stack) set"
where
    "exec_graph_step Gamma = {(stack, stack'). case stack of
            (NextNode nn, st, fname) # _ \<Rightarrow>
                (case Gamma fname of None \<Rightarrow> False
                    | Some (GraphFunction _ _ graph _) \<Rightarrow>
                        (case graph nn of None \<Rightarrow> stack' = upd_stack Err id stack
                            | Some node \<Rightarrow> stack' \<in> exec_node Gamma st node stack))
          | (Ret, st, _) # (NextNode nn, _, fname) # _ \<Rightarrow>
                (case Gamma fname of None \<Rightarrow> False
                    | Some (GraphFunction _ _ graph _) \<Rightarrow>
                        (case graph nn of None \<Rightarrow> stack' = upd_stack Err id (tl stack)
                            | Some node \<Rightarrow> stack' \<in> exec_node_return Gamma st node (tl stack)))
          | [] \<Rightarrow> False
          | [_] \<Rightarrow> False \<comment> \<open>note NextNode case is handled\<close>
          | _ \<Rightarrow> stack' = upd_stack Err id (tl stack)
      }"

text \<open>Multi-step relations.\<close>

definition exec_graph
where "exec_graph Gamma = rtrancl (exec_graph_step Gamma)"

definition exec_graph_n
where "exec_graph_n Gamma n = exec_graph_step Gamma ^^ n"

lemma relpow_Suc_simp2:
  "R ^^ Suc n = R O R ^^ n"
  apply safe
   apply (erule relpow_Suc_E2, blast)
  apply (blast intro: relpow_Suc_I2)
  done

lemma exec_graph_n_take_step:
  "\<lbrakk> (stack, stack') \<in> exec_graph_n GGamma n;
    \<lbrakk> n = 0; stack' = stack \<rbrakk> \<Longrightarrow> P;
    \<And>stack''. \<lbrakk> n > 0; (stack, stack'') \<in> exec_graph_step GGamma;
            (stack'', stack') \<in> exec_graph_n GGamma (n - 1) \<rbrakk>
        \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (cases n, simp_all only: exec_graph_n_def relpow_Suc_simp2)
   apply simp
  apply clarsimp
  done

lemma exec_graph_take_step:
  "\<lbrakk> ((NextNode m, gst, fname) # stack, stack') \<in> exec_graph_n GGamma n;
            GGamma fname = Some gf; function_graph gf m = Some node \<rbrakk>
    \<Longrightarrow> (n = 0 \<and> stack' = (NextNode m, gst, fname) # stack)
    \<or> (\<exists>stack''. n \<ge> 1
            \<and> stack'' \<in> exec_node GGamma gst node
                    ((NextNode m, gst, fname) # stack)
            \<and> (stack'', stack') \<in> exec_graph_n GGamma (n - 1))"
  apply (erule exec_graph_n_take_step)
   apply simp
  apply (clarsimp simp: exec_graph_step_def split: graph_function.split_asm)
  apply blast
  done

definition
  continuing :: "stack \<Rightarrow> bool"
where
  "continuing st = (case st of [] \<Rightarrow> False
    | [(NextNode _, _, _)] \<Rightarrow> True | [_] \<Rightarrow> False | _ \<Rightarrow> True)"

lemma continuing_simps[simp]:
  "\<not> continuing []"
  "continuing [(unn, st, g)] = (unn \<noteq> Ret \<and> unn \<noteq> Err)"
  "continuing ((Ret, st, g) # stk) = (stk \<noteq> [])"
  "continuing (stf # stf' # stk)"
  "continuing ((NextNode nn, st, g) # stk)"
  "continuing ((Err, st, g) # stk) = (stk \<noteq> [])"
  by (simp_all add: continuing_def split: next_node.split list.split)

lemma consume_Not_eq:
  "(\<not> P) = Q \<Longrightarrow> P = (\<not> Q)"
  by clarsimp

lemma exec_node_case_helper:
  "(stk' \<in> exec_node Gamma st node stk)
    = (case node of Basic _ _ \<Rightarrow> stk' \<in> id (exec_node Gamma) st node stk
        | _ \<Rightarrow> stk' \<in> id (exec_node Gamma) st node stk)"
  "(stk' \<in> exec_node_return Gamma st node stk)
    = (case node of Basic _ _ \<Rightarrow> stk' \<in> id (exec_node_return Gamma) st node stk
        | _ \<Rightarrow> stk' \<in> id (exec_node_return Gamma) st node stk)"
  by (simp_all split: node.split)

lemmas splits_raw = prod.split list.split option.split
    next_node.split graph_function.split node.split
lemmas splits_cooked = splits_raw[where P=Not, THEN consume_Not_eq]
    option.split[where P="\<lambda>S. x \<notin> S", THEN consume_Not_eq]
    graph_function.split[where P="\<lambda>S. x \<notin> S", THEN consume_Not_eq] for x

lemmas all_exec_graph_step_cases = exec_graph_step_def[THEN eqset_imp_iff,
    simplified, unfolded exec_node_case_helper splits_cooked, simplified,
    unfolded splits_cooked, simplified]

lemma exec_node_stack_extend:
  "continuing stack \<Longrightarrow>
    (stack' \<in> exec_node Gamma st node (stack @ xs))
        = (\<exists>stack''. stack' = stack'' @ xs
                \<and> stack'' \<in> exec_node Gamma st node stack)"
  apply (cases node, simp_all)
  apply (simp_all add: continuing_def
                split: list.split_asm prod.split_asm next_node.split_asm)
  apply (auto split: option.split graph_function.split)
  done

lemma exec_node_return_stack_extend:
  "continuing stack \<Longrightarrow>
    (stack' \<in> exec_node_return Gamma st node (stack @ xs))
        = (\<exists>stack''. stack' = stack'' @ xs
                \<and> stack'' \<in> exec_node_return Gamma st node stack)"
  apply (cases node, simp_all)
  apply (simp_all add: continuing_def
                split: list.split_asm prod.split_asm next_node.split_asm)
  apply (auto split: option.split graph_function.split)
  done

lemma exec_graph_step_stack_extend:
  "continuing stack \<Longrightarrow>
    ((stack @ xs, stack') \<in> exec_graph_step Gamma)
    = (\<exists>stack''. stack' = stack'' @ xs
        \<and> (stack, stack'') \<in> exec_graph_step Gamma)"
  using exec_node_stack_extend[where stack'=stack' and stack=stack
            and Gamma=Gamma and xs=xs]
        exec_node_return_stack_extend[where stack'=stack' and stack="tl stack"
            and Gamma=Gamma and xs=xs]
  apply (simp add: exec_graph_step_def)
  apply (cases stack, simp_all)
  apply clarsimp
  apply (case_tac a, simp_all)
    apply (clarsimp split: option.split graph_function.split)
   apply (clarsimp simp: neq_Nil_conv split: list.split)
   apply (clarsimp split: next_node.split option.split graph_function.split)
  apply (clarsimp simp: neq_Nil_conv split: list.split)
  done

lemma exec_graph_n_stack_extend:
  "continuing stack \<Longrightarrow>
    ((stack @ xs, stack') \<in> exec_graph_n Gamma n)
    = (\<exists>stack'' n'. (stack, stack'') \<in> (exec_graph_step Gamma
                \<inter> {(st, _). continuing st}) ^^ n'
        \<and> ((n' < n \<and> \<not> continuing stack''
                \<and> (stack'' @ xs, stack') \<in> exec_graph_n Gamma (n - n'))
            \<or> (stack' = stack'' @ xs \<and> n' = n)))"
  unfolding exec_graph_n_def
proof (induct n arbitrary: stack)
  case 0
  show ?case
    by auto[1]
next
  case (Suc n stack)
  show ?case
    apply (simp only: relpow_Suc_simp2)
    apply (rule iffI)
     apply (clarsimp simp: exec_graph_step_stack_extend Suc.prems)
     apply (case_tac "continuing stack''")
      apply (frule Suc.hyps, clarsimp)
      apply (rule_tac x="stack''a" in exI, rule_tac x="Suc n'" in exI)
      apply (simp only: relpow_Suc_simp2, clarsimp)
      apply (blast intro: Suc.prems)
     apply (rule_tac x="stack''" in exI, rule_tac x=1 in exI)
     apply (auto simp: Suc.prems)[1]
    apply (clarsimp)
    apply (case_tac n', simp_all only: minus_nat.diff_0 relpow_Suc_simp2)
     apply auto[1]
    apply clarsimp
    apply (rule_tac b="y @ xs" in relcompI)
     apply (simp add: exec_graph_step_stack_extend Suc.prems)
    apply (case_tac "nat = 0")
     apply auto[1]
    apply (subst Suc.hyps)
     apply (case_tac nat, simp_all only: relpow_Suc_simp2, auto)[1]
    apply auto[1]
    done
qed

definition
  "init_state fname gfun xs =
    (NextNode (entry_point gfun), save_vals (function_inputs gfun) xs default_state, fname)"

lemma exec_graph_step_nonempty:
  "\<lbrakk> (stack, stack') \<in> exec_graph_step Gamma ^^ n; stack \<noteq> [] \<rbrakk>
    \<Longrightarrow> stack' \<noteq> []"
  by (cases n, auto simp: all_exec_graph_step_cases
                   split: graph_function.split_asm)

lemma relpow_mono:
  "\<lbrakk> R \<subseteq> (S :: ('a \<times> 'a) set) \<rbrakk> \<Longrightarrow> R ^^ n \<subseteq> S ^^ n"
  by (induct n, auto)

lemma drop_eq_Cons:
  "(drop n xs = x # ys) = (\<exists>zs. length zs = n \<and> xs = zs @ x # ys)"
  apply (induct n arbitrary: xs)
   apply simp
  apply (case_tac xs, auto simp add: length_Suc_conv)
  done

lemma exec_graph_step_n_Err:
  "(((Err, st, graph) # stack, stack') \<in> exec_graph_n Gamma n)
    \<Longrightarrow> stack' = upd_stack Err id (drop n ((Err, st, graph) # stack))
        \<and> drop n ((Err, st, graph) # stack) \<noteq> []"
proof (induct n arbitrary: stack')
  case 0
  show ?case using 0
    by (auto simp add: exec_graph_n_def)
next
  case (Suc n)
  show ?case using Suc.prems
    apply (clarsimp simp: exec_graph_n_def relcomp_unfold linorder_not_le)
    apply (drule exec_graph_step_def[THEN eqset_imp_iff, THEN iffD1])
    apply (case_tac y, simp_all)
    apply (drule Suc.hyps[rotated, unfolded exec_graph_n_def])
    apply (simp only: neq_Nil_conv)
    apply (clarsimp simp: linorder_not_le drop_eq_Cons)
    apply (clarsimp split: list.split_asm)
    apply (case_tac zs, simp_all)
    done
qed

text \<open>Possibly infinite traces.\<close>

definition nat_trace_rel
  where "nat_trace_rel cont r = {tr. (\<forall>n. (tr n = None \<longrightarrow> tr (Suc n) = None)
    \<and> (tr (Suc n) \<noteq> None \<longrightarrow> (the (tr n), the (tr (Suc n))) \<in> r)
    \<and> (tr n \<noteq> None \<and> cont (the (tr n)) \<longrightarrow> tr (Suc n) \<noteq> None))}"

type_synonym trace = "(nat \<Rightarrow> stack option)"

definition
  trace_end :: "(nat \<Rightarrow> 'a option) \<Rightarrow> 'a option"
where
  "trace_end tr = (if \<exists>n. tr n = None then tr (Max (dom tr)) else None)"

lemma nat_trace_rel_Some_range:
  "tr \<in> nat_trace_rel cont r \<Longrightarrow> tr n = Some v
    \<Longrightarrow> \<forall>i \<le> n. \<exists>v'. tr i = Some v'"
  apply (induct n arbitrary: v, simp_all)
  apply (simp add: nat_trace_rel_def le_Suc_eq)
  apply (drule_tac x=n in spec, clarsimp)
  done

lemma trace_None_dom_subset:
  "tr n = None \<Longrightarrow> tr \<in> nat_trace_rel cont R
    \<Longrightarrow> dom tr \<subseteq> {..< n}"
  apply clarsimp
  apply (drule_tac n=x in nat_trace_rel_Some_range, simp+)
  apply (drule_tac x="n" in spec)
  apply simp
  done

lemma nat_trace_Max_dom_None:
  "tr \<in> nat_trace_rel cont R \<Longrightarrow> tr n \<noteq> None \<Longrightarrow> (tr (Max (dom tr)) \<noteq> None)"
  apply (rule notI)
  apply (frule(1) trace_None_dom_subset)
  apply (cases "dom tr = {}")
   apply clarsimp
  apply (drule Max_in[rotated])
   apply (simp add: finite_subset)
  apply clarsimp
  done

lemma trace_end_NoneD:
  "trace_end tr = None \<Longrightarrow> tr \<in> nat_trace_rel cont r
    \<Longrightarrow> tr = (\<lambda>_. None) \<or> (\<exists>f. tr = Some o f)"
  apply (subst disj_commute, rule disjCI)
  apply (clarsimp simp: fun_eq_iff)
  apply (simp add: trace_end_def split: if_split_asm)
   apply (metis nat_trace_Max_dom_None not_None_eq)
  apply (rule_tac x="the o tr" in exI, simp)
  done

lemma trace_end_SomeD:
  "trace_end tr = Some v \<Longrightarrow> tr \<in> nat_trace_rel cont r
    \<Longrightarrow> \<exists>n. tr n = Some v \<and> tr (Suc n) = None \<and> \<not> cont v"
  apply (clarsimp simp: trace_end_def split: if_split_asm)
  apply (rule exI, rule conjI, assumption)
  apply (case_tac "tr (Suc (Max (dom tr)))")
   apply (simp add: nat_trace_rel_def)
   apply (metis option.sel option.simps(3))
  apply (cut_tac x="Suc y" for y in Max_ge[OF finite_subset domI])
     apply (erule(1) trace_None_dom_subset[rotated])
    apply simp+
  done

definition
  exec_trace :: "(string \<Rightarrow> graph_function option) \<Rightarrow> string \<Rightarrow> trace set"
where
  "exec_trace Gamma fname
    = {trace. \<exists>gf. Gamma fname = Some gf
        \<and> (\<exists>st. trace 0 = Some [(NextNode (entry_point gf), st, fname)])
        \<and> trace \<in> nat_trace_rel continuing (exec_graph_step Gamma)}"

lemma relpow_nat_trace:
  "((s, s') \<in> r ^^ n) = (\<exists>tr \<in> nat_trace_rel (\<lambda>x. False) r. tr 0 = Some s
    \<and> tr n = Some s' \<and> tr (Suc n) = None)"
  apply (simp add: relpow_fun_conv, safe)
   apply (rule_tac x="\<lambda>x. if x < Suc n then Some (f x) else None" in bexI)
    apply simp
   apply (simp add: nat_trace_rel_def)
  apply (rule_tac x="the o tr" in exI)
  apply (frule(1) nat_trace_rel_Some_range[where n=n])
  apply (clarsimp simp: nat_trace_rel_def)
  done

text \<open>Parsing code for the graph language.\<close>

ML \<open>

structure ParseGraph = struct

exception PARSEGRAPH of string list

val debug = ref false

fun trace s = if (! debug) then writeln s else ()

fun parse_int str = if String.isPrefix "-" str
  then ~ (parse_int (unprefix "-" str))
  else case read_int (raw_explode str)
  of (n, []) => n
    | _ => raise PARSEGRAPH ["read_int:", str]

val s = @{term "s :: state"}

fun parse_n p (n :: ss) = let
    val n = parse_int n
  in funpow_yield n p ss end
  | parse_n _ [] = raise PARSEGRAPH ["parse_n: empty"]

fun mk_binT sz = Word_Lib.mk_wordT sz |> dest_Type |> snd |> hd

val ptr_size_str =
    case @{typ machine_word} of
      @{typ word32} => "32"
    | @{typ word64} => "64"

fun parse_typ ("Word" :: n :: ss) = let
    val n = parse_int n
  in (Word_Lib.mk_wordT n, ss) end
  | parse_typ ("Bool" :: ss) = (@{typ bool}, ss)
  | parse_typ ("Mem" :: ss) = (@{typ "machine_word \<Rightarrow> word8"}, ss)
  | parse_typ ("Dom" :: ss) = (@{typ "machine_word set"}, ss)
  | parse_typ ("HTD" :: ss) = (@{typ heap_typ_desc}, ss)
  | parse_typ ("PMS" :: ss) = (@{typ nat}, ss)
  | parse_typ ("UNIT" :: ss) = (@{typ unit}, ss)
  | parse_typ ("Array" :: ss) = let
    val (el_typ, ss) = parse_typ ss
    val (n, ss) = case ss of (n :: ss) => (parse_int n, ss)
        | [] => raise PARSEGRAPH ["parse_typ: array index"]
  in (Type (@{type_name array}, [el_typ, mk_binT n]), ss) end
  | parse_typ (bad as ("WordArray" :: "50" :: element_size :: ss)) =
      (if element_size = ptr_size_str
      then (@{typ "ghost_assertions"}, ss)
      else raise PARSEGRAPH ("parse_typ: bad ghost assertion codomain" :: bad))
  | parse_typ ("Struct" :: nm :: ss) = (Type (nm, []), ss)
  | parse_typ ("Ptr" :: ss) = let
    val (obj_typ, ss) = parse_typ ss
  in (Type (@{type_name ptr}, [obj_typ]), ss) end
  | parse_typ ss = raise PARSEGRAPH ("parse_typ: malformed" :: ss)

fun parse_lval ("VarUpdate" :: nm :: ss) = let
    val (_, ss) = parse_typ ss (* FIXME: check typ? *)
  in (nm, ss) end
  | parse_lval ss = raise PARSEGRAPH ("parse_lval" :: ss)

fun parse_var ss = parse_lval ("VarUpdate" :: ss)

val opers = Symtab.make [
      ("Plus", @{const_name "plus"}),
      ("Minus", @{const_name "minus"}),
      ("Times", @{const_name "times"}),
      ("Modulus", @{const_name "modulo_class.modulo"}),
      ("DividedBy", @{const_name "divide_class.divide"}),
      ("BWAnd", @{const_name "and"}),
      ("BWOr", @{const_name "or"}),
      ("BWXOR", @{const_name "xor"}),
      ("And", @{const_name "conj"}),
      ("Or", @{const_name "disj"}),
      ("Implies", @{const_name "implies"}),
      ("Equals", @{const_name "HOL.eq"}),
      ("Less", @{const_name "less"}),
      ("LessEquals", @{const_name "less_eq"}),
      ("SignedLess", @{const_name "word_sless"}),
      ("SignedLessEquals", @{const_name "word_sle"}),
      ("Not", @{const_name "Not"}),
      ("BWNot", @{const_name "not"}),
      ("WordCast", @{const_name "unsigned"}),
      ("WordCastSigned", @{const_name "signed"}),
      ("WordArrayAccess", @{const_name "fun_app"}),
      ("WordArrayUpdate", @{const_name "fun_upd"}),
      ("CountLeadingZeroes", @{const_name "bv_clz"}),
      ("CountTrailingZeroes", @{const_name "bv_ctz"}),
      ("True", @{const_name "True"}),
      ("False", @{const_name "False"}),
      ("IfThenElse", @{const_name "If"}),
      ("MemAcc", @{const_name "mem_acc"}),
      ("MemUpdate", @{const_name "mem_upd"}),
      ("MemDom", @{const_name "Set.member"}),
      ("ShiftLeft", @{const_name "bvshl"}),
      ("ShiftRight", @{const_name "bvlshr"}),
      ("SignedShiftRight", @{const_name "bvashr"}),
      ("PValid", @{const_name pvalid}),
      ("PArrayValid", @{const_name parray_valid}),
      ("PAlignValid", @{const_name palign_valid}),
      ("PGlobalValid", @{const_name pglobal_valid}),
      ("PWeakValid", @{const_name pweak_valid}),
      ("HTDUpdate", @{const_name all_htd_updates})
  ]

fun mk_acc nm typ st = (case typ of
        @{typ word8} => @{term var_word8}
      | @{typ word16} => @{term var_word16}
      | @{typ word32} => @{term var_word32}
      | @{typ word64} => @{term var_word64}
      | @{typ "machine_word \<Rightarrow> word8"} => @{term var_mem}
      | @{typ "machine_word set"} => @{term var_dom}
      | @{typ "ghost_assertions"} => @{term var_ghoststate}
      | @{typ "heap_typ_desc"} => @{term var_htd}
      | @{typ "nat"} => @{term var_ms}
      | @{typ bool} => @{term var_bool}
      | Type (@{type_name ptr}, [_]) =>
          (case @{typ "machine_word"} of
            @{typ word32} => @{term var_word32}
          | @{typ word64} => @{term var_word64})
      | _ => raise PARSEGRAPH ["mk_acc", nm, fst (dest_Type typ)])
    $ HOLogic.mk_string nm $ st

fun parse_val ("Num" :: ss) = let
    val (n, ss) = case ss of n :: ss => (n, ss)
        | [] => raise PARSEGRAPH ["parse_val: parsing num, no numeral"]
    val (typ, ss) = parse_typ ss
    val n = parse_int n
  in (HOLogic.mk_number typ n, ss) end
  | parse_val ("Op" :: nm :: ss) = let
    val const = case Symtab.lookup opers nm
      of SOME c => c
      | NONE => raise PARSEGRAPH ["parse_val: unexpected op", nm]
    val (typ, ss) = parse_typ ss
    val (args, ss) = parse_n parse_val ss
    val oper = Const (const, map fastype_of args ---> typ)
  in trace ("parsed oper " ^ nm ^ " and args");
    (list_comb (oper, args), ss) end
  | parse_val ("Var" :: nm :: ss) = let
    val (typ, ss) = parse_typ ss
  in (mk_acc nm typ s, ss) end
  | parse_val ("Type" :: ss) = let
    val (typ, ss) = parse_typ ss
  in (Logic.mk_type typ, ss) end
  | parse_val ("Symbol" :: nm :: ss) = let
    val (_, ss) = parse_typ ss
  in (TermsTypes.symbol_table $ HOLogic.mk_string nm, ss) end
  | parse_val ss = raise PARSEGRAPH ("parse_val: malformed" :: ss)

val parse_lvals = parse_n parse_lval

val parse_vars = parse_n parse_var

fun mk_var_typ T = (case T of
        @{typ word8} => @{term VarWord8}
      | @{typ word16} => @{term VarWord16}
      | @{typ word32} => @{term VarWord32}
      | @{typ word64} => @{term VarWord64}
      | Type (@{type_name word}, [Type (@{type_name signed}, [T2])])
        => let val uT = Type (@{type_name word}, [T2])
        in Abs ("t", T, mk_var_typ uT $ (Const (@{const_name unsigned}, T --> uT) $ Bound 0)) end
      | @{typ "machine_word \<Rightarrow> word8"} => @{term VarMem}
      | @{typ "ghost_assertions"} => @{term VarGhostState}
      | @{typ "machine_word set"} => @{term VarDom}
      | @{typ "heap_typ_desc"} => @{term VarHTD}
      | @{typ "unit \<times> nat"} => @{term VarMS}
      | @{typ bool} => @{term VarBool}
      | _ => raise TYPE ("mk_var_typ: unexpected var typ", [T], []))

fun mk_var_term t = betapply (mk_var_typ (fastype_of t), t)

fun parse_val_acc ss = let
    val (t, ss) = parse_val ss
  in (Term.lambda_name ("s", s) (mk_var_term t), ss) end

fun parse_cond ss = let
    val (t, ss) = parse_val ss
  in (Term.lambda_name ("s", s) t, ss) end

val parse_vals = parse_n parse_val_acc

fun mk_NextNode n = @{term NextNode} $ HOLogic.mk_number @{typ nat} n

fun parse_nn "Err" = @{term Err}
  | parse_nn "Ret" = @{term Ret}
  | parse_nn n = mk_NextNode (parse_int n)

fun parse_fun_decl ("Function" :: nm :: ss) = let
    val (xs, ss) = parse_vars ss
    val (ys, ss) = parse_vars ss
  in
    ss = [] orelse raise PARSEGRAPH ("parse_fun_decl: trailing" :: ss);
    (nm, xs, ys)
  end
  | parse_fun_decl ss = raise PARSEGRAPH ("parse_fun_decl: malformed" :: ss)

fun parse_var_and_val_acc ss = let
    val (var, ss) = parse_var ss
    val (v, ss) = parse_val_acc ss
  in (HOLogic.mk_prod (HOLogic.mk_string var, v), ss) end

val mk_stringlist = map HOLogic.mk_string #> HOLogic.mk_list @{typ string}

fun parse_node (n :: ss) = let
    val n = parse_int n
    val (t, ss) = case ss of
      "Cond" :: l :: r :: ss => let
        val l = parse_nn l
        val r = parse_nn r
        val (c, ss) = parse_cond ss
      in (@{term Cond} $ l $ r $ c, ss) end
      | "Basic" :: c :: ss => let
        val c = parse_nn c
        val (upds, ss) = parse_n parse_var_and_val_acc ss
      in (@{term Basic} $ c $ HOLogic.mk_list
            @{typ "string \<times> (state \<Rightarrow> variable)"} upds, ss) end
      | "Call" :: c :: fname :: ss => let
        val c = parse_nn c
        val (args, ss) = parse_vals ss
        val (rets, ss) = parse_vars ss
      in (@{term Call} $ c $ HOLogic.mk_string fname
            $ HOLogic.mk_list @{typ "state \<Rightarrow> variable"} args
            $ mk_stringlist rets, ss) end
      | _ => raise PARSEGRAPH ("parse_node: malformed" :: ss)
  in
    ss = [] orelse raise PARSEGRAPH ("parse_node: trailing" :: ss);
    (n, t)
  end
  | parse_node [] = raise PARSEGRAPH (["parse_node: empty"])

fun parse_fun (["Function" :: ss]) = let
    val (nm, xs, ys) = parse_fun_decl ("Function" :: ss)
  in SOME (nm, (xs, ys, NONE)) end
  | parse_fun (("Function" :: ss) :: sss) = let
    val (nm, xs, ys) = parse_fun_decl ("Function" :: ss)
    val _ = tracing ("Parsing " ^ nm)
    val (node_sss, sss) = chop_prefix
        (fn ss => not (is_prefix (op =) ["EntryPoint"] ss)) sss
    val (ep, _) = case sss of (ep :: sss) => (ep, sss)
        | [] => raise PARSEGRAPH [
        "parse_fun: EntryPoint not found"]
    val ep = case ep of [_, n] => parse_int n
        | _ => raise PARSEGRAPH (
        "parse_fun: EntryPoint line malformed" :: ep)
  in
    SOME (nm, (xs, ys, SOME (ep, map parse_node node_sss,
        Abs ("g", @{typ "nat \<Rightarrow> node option"}, @{term GraphFunction}
            $ mk_stringlist xs $ mk_stringlist ys
            $ Bound 0 $ HOLogic.mk_number @{typ nat} ep))))
  end
  | parse_fun [] = raise PARSEGRAPH ["parse_fun: empty"]
  | parse_fun (ss :: _) = (warning ("parse_fun: ignoring: "
    ^ space_implode " " ss); NONE)

fun fun_groups gp ((fs as ("Function" :: _)) :: sss) =
    (if null gp then [] else [rev gp]) @ fun_groups [fs] sss
  | fun_groups gp ([] :: sss) = fun_groups gp sss
  | fun_groups gp (ss :: sss) = fun_groups (ss :: gp) sss
  | fun_groups gp [] = [rev gp]

fun filename_relative thy name =
    Path.append (Resources.master_directory thy) (Path.explode name)
    |> File.standard_path

fun mkdir_relative thy name =
    Path.append (Resources.master_directory thy) (Path.explode name)
    |> Isabelle_System.make_directory

fun openIn_relative thy = filename_relative thy #> TextIO.openIn

fun get_funs thy file = let
    val f = openIn_relative thy file
    fun get () = case TextIO.inputLine f
      of NONE => []
      | SOME s => unsuffix "\n" s :: get ()
    val lines = get ()
      |> map (Library.space_explode " " #> filter (fn s => s <> ""))
      |> filter_out null
      |> filter_out (fn (s :: _) => String.isPrefix "#" s | _ => false)
  in fun_groups [] lines end

type funs = (string list * string list * (int * (int * term) list * term) option) Symtab.table

fun funs thy file : funs = get_funs thy file
  |> map_filter parse_fun
  |> Symtab.make

fun define_graph s nodes = let
    val nodes = sort (int_ord o apply2 fst) nodes
  in StaticFun.define_tree_and_save_thms (Binding.name s)
    (map (fst #> Int.toString #> prefix (s ^ "_")) nodes)
    (map (apfst (HOLogic.mk_number @{typ nat})) nodes)
    @{term "id :: nat => nat"} []
  end

fun define_graph_fun (funs : funs) b1 b2 nm ctxt =
        case (Symtab.lookup funs nm) of
    SOME (_, _, SOME (_, g, gf))
    => let
    val (graph_term, ctxt) = define_graph b1 g ctxt
    val (_, ctxt) = Local_Theory.define ((b2, NoSyn), ((Thm.def_binding b2, []),
        betapply (gf, graph_term))) ctxt
  in ctxt end
  | _ => error ("define_graph_fun: " ^ nm ^ " not in funs")

end

\<close>

end
