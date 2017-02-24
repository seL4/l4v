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

theory Apply_Debug
  imports Apply_Trace "~~/src/HOL/Eisbach/Eisbach_Tools"
  keywords "apply_debug" :: "prf_script" % "proof" and
    "continue" :: prf_script % "proof" and  "finish" :: prf_script % "proof"
begin

(* Small hack to keep enough available threads around to support ongoing apply_debug sessions *)
ML \<open>
val start_max_threads = Multithreading.max_threads ();
\<close>

(*FIXME: Add proper interface to match *)
context
begin

private method put_prems =
  (match premises in H:"PROP _" (multi) \<Rightarrow> \<open>insert H\<close>)

ML \<open>
fun get_match_prems ctxt =
  let

    val st = Goal.init @{cterm "PROP P"}

    fun get_wrapped () =
      let
        val ((_,st'),_) =
          Method_Closure.apply_method ctxt @{method put_prems} [] [] [] ctxt [] (ctxt, st)
          |> Seq.first_result "prems";

        val prems =
          Thm.prems_of st' |> hd |> Logic.strip_imp_prems;

      in prems end

     val match_prems = the_default [] (try get_wrapped ());

     val all_prems = Assumption.all_prems_of ctxt;

   in map_filter (fn t => find_first (fn thm => t aconv (Thm.prop_of thm)) all_prems) match_prems end

\<close>
end

ML \<open>
signature APPLY_DEBUG =
sig
type break_opts = { tags : string list, trace : (string * Position.T) option, show_running : bool }

val break : Proof.context -> string option -> tactic;
val apply_debug : break_opts -> Method.text_range -> Proof.state -> Proof.state;
val continue : int option -> (context_state -> context_state option) option -> Proof.state -> Proof.state;
val finish : Proof.state -> Proof.state;

end

structure Apply_Debug : APPLY_DEBUG =
struct
type break_opts = { tags : string list, trace : (string * Position.T) option, show_running : bool }

fun do_markup range m = Output.report [Markup.markup (Markup.properties (Position.properties_of_range range) m) ""];
fun do_markup_pos pos m = Output.report [Markup.markup (Markup.properties (Position.properties_of pos) m) ""];

type markup_queue = { cur : Position.range option, next : Position.range option, clear_cur : bool }

fun map_cur f ({cur, next, clear_cur} : markup_queue) =
  ({cur = f cur, next = next, clear_cur = clear_cur} : markup_queue)

fun map_next f ({cur, next, clear_cur} : markup_queue) =
  ({cur = cur, next = f next, clear_cur = clear_cur} : markup_queue)

fun map_clear_cur f ({cur, next, clear_cur} : markup_queue) =
  ({cur = cur, next = next, clear_cur = f clear_cur} : markup_queue)

type markup_state =
  { running : markup_queue
  }

fun map_running f ({running} : markup_state) =
  {running = f running}


structure Markup_Data = Proof_Data
(
  type T = markup_state Synchronized.var option *
    Position.range option (* latest method location *) *
    Position.range option (* latest breakpoint location *)
  fun init _ : T = (NONE, NONE, NONE)
);

val init_queue = ({cur = NONE, next = NONE, clear_cur = false}: markup_queue)
val init_markup_state = ({running = init_queue} : markup_state)

fun set_markup_state id = Markup_Data.map (@{apply 3 (1)} (K id));
fun get_markup_id ctxt = #1 (Markup_Data.get ctxt);

fun set_latest_range range = Markup_Data.map (@{apply 3 (2)} (K (SOME range)));
fun get_latest_range ctxt = #2 (Markup_Data.get ctxt);

fun set_breakpoint_range range = Markup_Data.map (@{apply 3 (3)} (K (SOME range)));
fun get_breakpoint_range ctxt = #3 (Markup_Data.get ctxt);

val clear_ranges = Markup_Data.map (@{apply 3 (3)} (K NONE) o @{apply 3 (2)} (K NONE));

fun swap_markup queue startm endm =
if is_some (#next queue) andalso #next queue = #cur queue then SOME (map_next (K NONE) queue) else
let
  fun clear_cur () =
    (case #cur queue of SOME crng =>
        do_markup crng endm
      | NONE => ())
in
  case #next queue of SOME rng =>
    (clear_cur (); do_markup rng startm; SOME ((map_cur (K (SOME rng)) o map_next (K NONE)) queue))
   | NONE => if #clear_cur queue then (clear_cur (); SOME ((map_cur (K NONE) o map_clear_cur (K false)) queue))
             else NONE
end

fun markup_worker (SOME (id : markup_state Synchronized.var)) =
let
  fun main_loop () =
    let val _ = Synchronized.guarded_access id (fn e =>
    case swap_markup (#running e) Markup.running Markup.finished of
      SOME queue' => SOME ((),map_running (fn _ => queue') e)
    | NONE => NONE)
     in main_loop () end
in main_loop () end
 | markup_worker NONE = (fn () => ())

fun set_gen get set (SOME id) rng =
  let
    val _ =
       Synchronized.guarded_access id (fn e =>
         if is_some (#next (get e)) orelse (#clear_cur (get e)) then NONE else
         if (#cur (get e)) = SOME rng then SOME ((), e)
         else (SOME ((),(set (map_next (fn _ => SOME rng)) e))))

    val _ = Synchronized.guarded_access id (fn e => if is_some (#next (get e)) then NONE else SOME ((),e))
  in () end
 | set_gen _ _ NONE _ = ()


fun clear_gen get set (SOME id) =
  Synchronized.guarded_access id (fn e =>
  if (#clear_cur (get e)) then NONE
  else (SOME ((),(set (map_clear_cur (fn _ => true)) e))))
 | clear_gen _ _ NONE = ()

val set_running = set_gen #running map_running
val clear_running = clear_gen #running map_running


fun traceify_method static_ctxt src =
let
  val range = Token.range_of src;
  val head_range = Token.range_of [hd src];
  val m = Method.method_cmd static_ctxt src;

in (fn eval_ctxt => fn facts =>
  let
    val eval_ctxt = set_latest_range head_range eval_ctxt;
    val markup_id = get_markup_id eval_ctxt;

    fun traceify seq = Seq.make (fn () =>
        let
          val _ = set_running markup_id range;
          val r = Seq.pull seq;
          val _ = clear_running markup_id;
        in Option.map (apsnd traceify) r end)

    fun tac (runtime_ctxt,thm) =
        let
          val runtime_ctxt' = set_latest_range head_range runtime_ctxt;
          val _ = set_running markup_id range;
          in traceify (m eval_ctxt facts (runtime_ctxt', thm)) end

   in tac end)
end

fun add_debug ctxt (Method.Source src) = (Method.Basic (traceify_method ctxt src))
  | add_debug ctxt (Method.Combinator (x,y,txts)) = (Method.Combinator (x,y, map (add_debug ctxt) txts))
  | add_debug _ x = x

fun st_eq (ctxt : Proof.context,st) (ctxt',st') =
  pointer_eq (ctxt,ctxt') andalso Thm.eq_thm (st,st')

type result =
  { pre_state : thm,
    post_state : thm,
    context: Proof.context}

datatype final_state = RESULT of (Proof.context * thm) | ERR of (unit -> string)

type debug_state =
  {results : result list, (* this execution, in order of appearance *)
   prev_results : thm list, (* continuations needed to get thread back to some state*)
   next_state : thm option, (* proof thread blocks waiting for this *)
   break_state : (Proof.context * thm) option, (* state of proof thread just before blocking *)
   restart : (unit -> unit) * int, (* restart function (how many previous results to keep), restart requested if non-zero *)
   final : final_state option, (* final result, maybe error *)
   trans_id : int, (* increment on every restart *)
   ignore_breaks: bool}

val init_state =
  ({results = [],
    prev_results = [],
    next_state = NONE, break_state = NONE,
    final = NONE, ignore_breaks = false, restart = (K (), ~1), trans_id = 0} : debug_state)

fun map_next_state f ({results, next_state, break_state, final, ignore_breaks, prev_results, restart, trans_id} : debug_state) =
  ({results = results, next_state = f next_state, break_state = break_state, final = final, prev_results = prev_results,
    restart = restart, ignore_breaks = ignore_breaks, trans_id = trans_id} : debug_state)

fun map_results f ({results, next_state, break_state, final, ignore_breaks, prev_results, restart, trans_id} : debug_state) =
  ({results = f results, next_state = next_state, break_state = break_state, final = final, prev_results = prev_results,
    restart = restart, ignore_breaks = ignore_breaks, trans_id = trans_id} : debug_state)

fun map_prev_results f ({results, next_state, break_state, final, ignore_breaks, prev_results, restart, trans_id} : debug_state) =
  ({results = results, next_state = next_state, break_state = break_state, final = final, prev_results = f prev_results,
    restart = restart, ignore_breaks = ignore_breaks, trans_id = trans_id} : debug_state)

fun map_ignore_breaks f ({results, next_state, break_state = break_state, final, ignore_breaks, prev_results, restart, trans_id} : debug_state) =
  ({results = results, next_state = next_state, break_state = break_state,final = final, prev_results = prev_results,
    restart = restart, ignore_breaks = f ignore_breaks, trans_id = trans_id} : debug_state)

fun map_final f ({results, next_state, break_state, final, ignore_breaks, prev_results, restart, trans_id} : debug_state) =
  ({results = results, next_state = next_state, break_state =break_state ,final = f final, prev_results = prev_results,
    restart = restart, ignore_breaks = ignore_breaks, trans_id = trans_id} : debug_state)

fun map_restart f ({results, next_state, break_state, final, ignore_breaks, prev_results, restart, trans_id} : debug_state) =
  ({results = results, next_state = next_state, break_state = break_state, final = final, prev_results = prev_results,
    restart = f restart, ignore_breaks = ignore_breaks, trans_id = trans_id} : debug_state)

fun map_break_state f ({results, next_state, break_state, final, ignore_breaks, prev_results, restart, trans_id} : debug_state) =
  ({results = results, next_state = next_state, break_state = f break_state, final = final, prev_results = prev_results,
    restart = restart, ignore_breaks = ignore_breaks, trans_id = trans_id} : debug_state)

fun map_trans_id f ({results, next_state, break_state, final, ignore_breaks, prev_results, restart, trans_id} : debug_state) =
  ({results = results, next_state = next_state, break_state = break_state, final = final, prev_results = prev_results,
    restart = restart, ignore_breaks = ignore_breaks, trans_id = f trans_id} : debug_state)

fun is_restarting ({restart,...} : debug_state) = snd restart > ~1;
fun is_finished ({final,...} : debug_state) = is_some final;

val drop_states = map_break_state (K NONE) o map_next_state (K NONE);

fun add_result ctxt pre post = map_results (cons {pre_state = pre, post_state = post, context = ctxt}) o drop_states;

fun get_trans_id (id : debug_state Synchronized.var) = #trans_id (Synchronized.value id);

fun stale_transaction_err trans_id trans_id' =
  error ("Stale transaction. Expected " ^ Int.toString trans_id ^ " but found " ^ Int.toString trans_id')

fun assert_trans_id trans_id (e : debug_state) =
  if trans_id = (#trans_id e) then ()
    else stale_transaction_err trans_id (#trans_id e)

fun guarded_access id f =
  let
    val trans_id = get_trans_id id;
  in
  Synchronized.guarded_access id
    (fn (e : debug_state) =>
     (assert_trans_id trans_id e;
       (case f e of
          NONE => NONE
         | SOME (e', g) => SOME (e', g e))))
   end

fun guarded_read id f =
  let
    val trans_id = get_trans_id id;
  in
  Synchronized.guarded_access id
    (fn (e : debug_state) =>
     (assert_trans_id trans_id e;
      (case f e of
          NONE => NONE
         | SOME e' => SOME (e', e))))
   end



(* Immediate return if there are previous results available or we are ignoring breakpoints *)

fun pop_state_no_block id ctxt pre = guarded_access id (fn e =>
  if is_finished e then error "Attempted to pop state from finished proof" else
  if (#ignore_breaks e) then SOME (SOME pre, add_result ctxt pre pre) else
  case #prev_results e of
     [] => SOME (NONE, I)
   | (st :: sts) => SOME (SOME st, add_result ctxt pre st o map_prev_results (fn _ => sts)))

fun pop_next_state id ctxt pre = guarded_access id (fn e =>
  if is_finished e then error "Attempted to pop state from finished proof" else
  if not (null (#prev_results e)) then error "Attempted to pop state when previous results exist" else
    if (#ignore_breaks e) then SOME (pre, add_result ctxt pre pre) else
    (case #next_state e of
            NONE => NONE
          | SOME st => SOME (st, add_result ctxt pre st)))

fun set_next_state id trans_id st = guarded_access id (fn e =>
  (assert_trans_id trans_id e;
   (if is_none (#next_state e) andalso is_some (#break_state e) then
     SOME ((), map_next_state (fn _ => SOME st) o map_break_state (fn _ => NONE))
   else error ("Attempted to set next state in inconsistent state" ^ (@{make_string} e)))))

fun set_break_state id st = guarded_access id (fn e =>
  if is_none (#next_state e) andalso is_none (#break_state e) then
    SOME ((), map_break_state (fn _ => SOME st))
  else error ("Attempted to set break state in inconsistent state" ^ (@{make_string} e)))

fun pop_state id ctxt pre =
  case pop_state_no_block id ctxt pre of SOME st => st
  | NONE =>
  let
    val _ = set_break_state id (ctxt, pre); (* wait for continue *)
  in pop_next_state id ctxt pre end

(* block until a breakpoint is hit or method finishes *)
fun wait_break_state id trans_id = guarded_read id
  (fn e =>
    (assert_trans_id trans_id e;
     (case (#final e) of SOME st => SOME (st, true) | NONE =>
      case (#break_state e) of SOME st => SOME (RESULT st, false)
     | NONE => NONE)));

fun debug_print (id : debug_state Synchronized.var) =
  (@{print} (Synchronized.value id));

(* Trigger a restart if an existing nth entry differs from the given one *)
fun maybe_restart id n st =
let
  val gen = guarded_read id (fn e => SOME (#trans_id e));

  val did_restart = guarded_access id (fn e =>
    if is_some (#next_state e) then NONE else
    if not (null (#prev_results e)) then NONE else
    if is_restarting e then NONE (* TODO, what to do if we're already restarting? *)
    else if length (#results e) > n then
      (SOME (true, map_restart (apsnd (fn _ => n))))
    else SOME (false, I))


  val trans_id = Synchronized.guarded_access id
    (fn e => if is_restarting e then NONE else
             if not did_restart orelse gen + 1 = #trans_id e then SOME (#trans_id e,e) else
             stale_transaction_err (gen + 1) (#trans_id e));
in trans_id end;


fun peek_all_results id = guarded_read id (fn e => SOME (#results e));

fun peek_final_result id =
  guarded_read id (fn e => #final e)

fun poke_error (RESULT st) = st
  | poke_error (ERR e) = error (e ())

fun context_state e = (#context e, #pre_state e);

fun nth_pre_result id i = guarded_read id
  (fn e =>
    if length (#results e) > i then SOME (RESULT (context_state (nth (rev (#results e)) i)), false) else
    if not (null (#prev_results e)) then NONE else
      (if length (#results e) = i then
         (case #break_state e of SOME st => SOME (RESULT st, false) | NONE => NONE) else
         (case #final e of SOME st => SOME (st, true) | NONE => NONE)))

fun set_finished_result id trans_id st =
  guarded_access id (fn e =>
  (assert_trans_id trans_id e;
   SOME ((), map_final (K (SOME st)))));

fun is_finished_result id = guarded_read id (fn e => SOME (is_finished e));

fun get_finish id =
if is_finished_result id then peek_final_result id else
  let
    val _ = guarded_access id
      (fn _ => SOME ((), (map_ignore_breaks (fn _ => true))))

  in peek_final_result id end


val no_break_opts = ({tags = [], trace = NONE, show_running = false} : break_opts)

structure Debug_Data = Proof_Data
(
  type T = debug_state Synchronized.var option  (* handle on active proof thread *) *
  int * (* continuation counter *)
  bool * (* currently interactive context *)
  break_opts * (* global break arguments *)
  string option (* latest breakpoint tag *)
  fun init _ : T = (NONE,~1, false, no_break_opts, NONE)
);

fun set_debug_ident ident = Debug_Data.map  (@{apply 5 (1)} (fn _ => SOME ident))
val get_debug_ident = #1 o Debug_Data.get;
val get_the_debug_ident = the o get_debug_ident;

fun set_break_opts opts = Debug_Data.map (@{apply 5 (4)} (fn _ => opts))
val get_break_opts = #4 o Debug_Data.get;

fun set_last_tag tags = Debug_Data.map (@{apply 5 (5)} (fn _ => tags))
val get_last_tag = #5 o Debug_Data.get;

val is_debug_ctxt = is_some o #1 o Debug_Data.get;

fun clear_debug ctxt = ctxt
 |> Debug_Data.map (fn _ => (NONE,~1,false, no_break_opts, NONE))
 |> clear_ranges


val get_continuation = #2 o Debug_Data.get;
val get_can_break = #3 o Debug_Data.get;

(* Maintain pointer equality if possible *)
fun set_continuation i ctxt = if get_continuation ctxt = i then ctxt else
  Debug_Data.map (@{apply 5 (2)} (fn _ => i)) ctxt;

fun set_can_break b ctxt = if get_can_break ctxt = b then ctxt else
  Debug_Data.map (@{apply 5 (3)} (fn _ => b)) ctxt;

fun has_break_tag (SOME tag) tags = member (op =) tags tag
  | has_break_tag NONE _ = true;

fun break ctxt tag = (fn thm =>
if not (get_can_break ctxt)
   orelse Method.detect_closure_state thm
   orelse not (has_break_tag tag (#tags (get_break_opts ctxt)))
    then Seq.single thm else
  let
    val id = get_the_debug_ident ctxt;
    val ctxt' = set_last_tag tag ctxt;

    val st' = Seq.make (fn () =>
     SOME (pop_state id ctxt' thm,Seq.empty))

  in st' end)

fun init_interactive ctxt = ctxt
  |> set_can_break false
  |> Config.put Method.closure true;

type static_info =
  {private_dyn_facts : string list, local_facts : (string * thm list) list}

structure Data = Generic_Data
(
  type T = (morphism * Proof.context * static_info) option;
  val empty: T = NONE;
  val extend = K NONE;
  fun merge data : T = NONE;
);

(* Present Eisbach/Match variable binding context as normal context elements.
   Potentially shadows existing facts/binds *)

fun dest_local s =
  let
    val ["local",s'] = Long_Name.explode s;
  in SOME s' end handle Bind => NONE

fun maybe_bind st (_,[tok]) ctxt =
  if Method.detect_closure_state st then
    let
      val target = Local_Theory.target_of ctxt
      val local_facts = Proof_Context.facts_of ctxt;
      val global_facts = map (Global_Theory.facts_of) (Context.parents_of (Proof_Context.theory_of ctxt));
      val raw_facts = Facts.dest_all (Context.Proof ctxt) true global_facts local_facts |> map fst;

      fun can_retrieve s = can (Facts.retrieve (Context.Proof ctxt) local_facts) (s, Position.none)

      val private_dyns = raw_facts |>
        (filter (fn s => Facts.is_concealed local_facts s andalso Facts.is_dynamic local_facts s
                         andalso can_retrieve (Long_Name.base_name s)
                         andalso Facts.intern local_facts (Long_Name.base_name s) = s
                         andalso not (can_retrieve s)) )

      val local_facts = Facts.dest_static true [(Proof_Context.facts_of target)] local_facts;

      val _ = Token.assign (SOME (Token.Declaration (fn phi =>
      Data.put (SOME (phi,ctxt, {private_dyn_facts = private_dyns, local_facts = local_facts}))))) tok;

   in ctxt end
  else
    let
      val SOME (Token.Declaration decl) = Token.get_value tok;
      val dummy_ctxt = decl Morphism.identity (Context.Proof ctxt);
      val SOME (phi,static_ctxt,{private_dyn_facts, local_facts}) = Data.get dummy_ctxt;

      val old_facts = Proof_Context.facts_of static_ctxt;
      val cur_priv_facts = map (fn s =>
            Facts.retrieve (Context.Proof ctxt) old_facts (Long_Name.base_name s,Position.none)) private_dyn_facts;

      val cur_local_facts =
        map (fn (s,fact) => (dest_local s, Morphism.fact phi fact)) local_facts
      |> map_filter (fn (s,fact) => case s of SOME s => SOME (s,fact) | _ => NONE)

      val old_fixes = (Variable.dest_fixes static_ctxt)

      val local_fixes =
        filter (fn (_,f) =>
          Variable.is_newly_fixed static_ctxt (Local_Theory.target_of static_ctxt) f) old_fixes
        |> map_filter (fn (n,f) => case Variable.default_type static_ctxt f of SOME typ =>
              if typ = dummyT then NONE else SOME (n, Free (f, typ))
            | NONE => NONE)

      val local_binds = (map (apsnd (Morphism.term phi)) local_fixes)

      val ctxt' = ctxt
      |> fold (fn (s,t) =>
          Variable.bind_term ((s,0),t)
          #> Variable.declare_constraints (Var ((s,0),Term.fastype_of t))) local_binds
      |> fold (fn e =>
          Proof_Context.put_thms true (Long_Name.base_name (#name e), SOME (#thms e))) cur_priv_facts
      |> fold (fn (nm,fact) =>
          Proof_Context.put_thms true (nm, SOME fact)) cur_local_facts
      |> Proof_Context.put_thms true ("match_prems", SOME (get_match_prems ctxt));

    in ctxt' end
 | maybe_bind _ _ ctxt = ctxt

val _ = Context.>> (Context.map_theory (Method.setup @{binding #}
  (Scan.lift (Scan.trace (Scan.trace (Args.$$$ "break") -- (Scan.option Parse.string))) >>
   (fn ((b,tag),toks) => fn _ => fn _ =>
    fn (ctxt,thm) =>
      (let

        val range = Token.range_of toks;
        val ctxt' = ctxt
          |> maybe_bind thm b
          |> set_breakpoint_range range;

      in Seq.make_results (Seq.map (fn thm' => (ctxt',thm')) (break ctxt' tag thm)) end))) ""))

fun map_state f state =
     let
      val (r,_) = Seq.first_result "map_state" (Proof.apply
        (Method.Basic (fn _ => fn _ => fn st =>
            Seq.make_results (Seq.single (f st))),
          Position.no_range) state)
     in r end;

fun get_state state =
let
  val {context,goal} = Proof.simple_goal state;
in (context,goal) end


fun maybe_trace (SOME (tr, pos)) (ctxt, st) =
let
  val deps = Apply_Trace.used_facts ctxt st;
  val query = if tr = "" then NONE else SOME (tr, pos);
  val pr = Apply_Trace.pretty_deps false query ctxt st deps;
in Pretty.writeln pr end
  | maybe_trace NONE (ctxt, st) = ()

val active_debug_threads = Synchronized.var "active_debug_threads" ([] : unit future list);

fun update_max_threads extra =
let
  val n_active = Synchronized.change_result active_debug_threads (fn ts =>
    let
      val ts' = List.filter (not o Future.is_finished) ts;
    in (length ts',ts') end)
  val _ = Multithreading.max_threads_update (start_max_threads + ((n_active + extra) * 3));
in () end


fun continue i_opt m_opt =
(map_state (fn (ctxt,thm) =>
      let

        val ctxt = set_can_break true ctxt

        val thm = Apply_Trace.clear_deps thm;

        val _ = if is_none (get_debug_ident ctxt) then error "Cannot continue in a non-debug state" else ();

        val id = get_the_debug_ident ctxt;

        val start_cont = get_continuation ctxt; (* how many breakpoints so far *)

        val trans_id = maybe_restart id start_cont (ctxt,thm);
          (* possibly restart if the thread has made too much progress.
             trans_id is the current number of restarts, used to avoid manipulating
             stale states *)

        val _ = nth_pre_result id start_cont; (* block until we've hit the start of this continuation *)

        fun get_final n (st as (ctxt,_))  =
         case (i_opt,m_opt) of
          (SOME i,NONE) => if i < 1 then error "Can only continue a positive number of breakpoints" else
            if n = start_cont + i then SOME st else NONE
         | (NONE, SOME m) => (m (apfst init_interactive st))
         | (_, _) => error "Invalid continue arguments"

        val ex_results = peek_all_results id |> rev;

        fun tick_up n (_,thm) =
          if n < length ex_results then error "Unexpected number of existing results"
           (*case get_final n (#pre_state (nth ex_results n)) of SOME st' => (st', false, n)
            | NONE => tick_up (n + 1) st *)
          else
          let
            val _ = if n > length ex_results then set_next_state id trans_id thm else ();
            val (n_r, b) = wait_break_state id trans_id;
            val st' = poke_error n_r;
          in if b then (st',b, n) else
            case get_final n st' of SOME st'' => (st'', false, n)
            | NONE => tick_up (n + 1) st' end

        val _ = if length ex_results < start_cont then
          (debug_print id; @{print} ("start_cont",start_cont); @{print} ("trans_id",trans_id);
            error "Unexpected number of existing results")
          else ()


        val (st',b, cont) = tick_up (start_cont + 1) (ctxt, thm)

        val st'' = if b then (Output.writeln "Final Result."; st' |> apfst clear_debug)
                   else st' |> apfst (set_continuation cont) |> apfst (init_interactive);

        (* markup for matching breakpoints to continues *)

        val sr = serial ();

        fun markup_def rng =
          (Output.report
              [Markup.markup (Markup.entity "breakpoint" ""
               |> Markup.properties (Position.entity_properties_of true sr
                    (Position.range_position rng))) ""]);

        val _ = Option.map markup_def (get_latest_range (fst st''));
        val _ = Option.map markup_def (get_breakpoint_range (fst st''));

        val _ =
          (Context_Position.report ctxt (Position.thread_data ())
             (Markup.entity "breakpoint" ""
              |> Markup.properties (Position.entity_properties_of false sr Position.none)))

        val _ = maybe_trace (#trace (get_break_opts ctxt)) st'';

      in st'' end))

fun do_apply pos rng opts m =
let
  val {tags, trace, show_running} = opts;
  val batch_mode = is_some (Position.line_of (fst rng));
  val show_running = if batch_mode then false else show_running;

  val _ = if batch_mode then () else update_max_threads 1;

in
 (fn st => map_state (fn (ctxt,thm) =>
  let
     val ident = Synchronized.var "debug_state" init_state;
     val markup_id = if show_running then SOME (Synchronized.var "markup_state" init_markup_state)
       else NONE;
     fun maybe_markup m = if show_running then do_markup rng m else ();

     val _ = if is_debug_ctxt ctxt then
      error "Cannot use apply_debug while debugging" else ();

     val m = apfst (fn f => f ctxt) m;

     val st = Proof.map_context
      (set_can_break true
       #> set_break_opts opts
       #> set_markup_state markup_id
       #> set_debug_ident ident
       #> set_continuation ~1) st
       |> map_state (apsnd Apply_Trace.clear_deps);

     fun do_cancel thread = (Future.cancel thread; Future.join_result thread; ());

     fun do_fork trans_id = Future.fork (fn () =>
       let
        val (ctxt,thm) = get_state st;

        val r = case Exn.interruptible_capture (fn st =>
        let val _ = Seq.pull (break ctxt NONE thm) in
        (case (Seq.pull o Proof.apply m) st
          of (SOME (Seq.Result st', _)) => RESULT (get_state st')
           | (SOME (Seq.Error e, _)) => ERR e
           | _ => ERR (fn _ => "No results")) end) st
           of Exn.Res (RESULT r) => RESULT r
             | Exn.Res (ERR e) => ERR e
            | Exn.Exn e => ERR (fn _ => Runtime.exn_message e)
        val _ = set_finished_result ident trans_id r;

        val _ = clear_running markup_id;

       in () end)


     val thread = do_fork 0;
     val _ = Synchronized.change ident (map_restart (fn _ => (fn () => do_cancel thread, ~1)));

     val _ = maybe_markup Markup.finished;

     val _ = Future.fork (fn () => markup_worker markup_id ());

     val st' = get_state (continue (SOME 1) NONE (Proof.map_context (set_continuation 0) st))

     val _ = maybe_markup Markup.joined;


     val main_thread = if batch_mode then Future.fork (fn () => ()) else Future.fork (fn () =>
      let

        fun restart_state gls e = e
          |> map_prev_results (fn _ => map #post_state (take gls (rev (#results e))))
          |> map_results (fn _ => [])
          |> map_final (fn _ => NONE)
          |> map_ignore_breaks (fn _ => false)
          |> map_restart (fn _ => (K (), gls))
          |> map_break_state (fn _ => NONE)
          |> map_next_state (fn _ => NONE)
          |> map_trans_id (fn i => i + 1);

        fun main_loop () =
          let
            val r = Synchronized.timed_access ident (fn _ => SOME (seconds 0.1)) (fn e as {restart,next_state,...} =>
              if is_restarting e andalso is_none next_state then
              SOME ((fst restart, #trans_id e), restart_state (snd restart) e) else NONE);
            val _ = OS.Process.sleep (seconds 0.1);
            in case r of NONE => main_loop ()
            | SOME (f,trans_id) =>
              let
                val _ = f ();
                val _ = clear_running markup_id;
                val thread = do_fork (trans_id + 1);
                val _ = Synchronized.change ident (map_restart (fn _ => (fn () => do_cancel thread, ~1)))
              in main_loop () end
           end;
       in main_loop () end);

       val _ = maybe_markup Markup.running;
       val _ = maybe_markup Markup.forked;

       val _ = Synchronized.change active_debug_threads (cons main_thread);

   in st' end) st)
end

fun apply_debug opts (m', rng)  =
  let
      val _ = Method.report (m', rng);

      val m'' = (fn ctxt => add_debug ctxt m')
      val m = (m'',rng)
      val pos = Position.thread_data ();

     in do_apply pos rng opts m end;

fun quasi_keyword x = Scan.trace (Args.$$$ x) >>
  (fn (s,[tok]) => (Position.reports [(Token.pos_of tok, Markup.quasi_keyword)]; s))

val parse_tags = (Args.parens (quasi_keyword "tags" |-- Parse.enum1 "," Parse.string));
val parse_trace = Scan.option (Args.parens (quasi_keyword "trace" |-- Scan.option (Parse.position Parse.cartouche))) >>
  (fn SOME NONE => SOME ("", Position.none) | SOME (SOME x) => SOME x | _ => NONE);

val parse_opts1 = (parse_tags -- parse_trace) >>
  (fn (tags,trace) => {tags = tags, trace = trace});

val parse_opts2 = (parse_trace -- (Scan.optional parse_tags [])) >>
  (fn (trace,tags) => {tags = tags, trace = trace});

fun mode s = Scan.optional (Args.parens (quasi_keyword s) >> (K true)) false

val parse_opts = ((parse_opts1 || parse_opts2) -- mode "show_running") >>
  (fn ({tags, trace}, show_running) => {tags = tags, trace = trace, show_running = show_running} : break_opts) ;

val _ =
  Outer_Syntax.command @{command_keyword apply_debug} "initial goal refinement step (unstructured)"
    (Scan.trace
      (parse_opts --  Method.parse) >>
      (fn ((opts, (m,_)),toks) => Toplevel.proof (apply_debug opts (m,Token.range_of toks))));

val finish = map_state (fn (ctxt,_) =>
      let
        val _ = if is_none (get_debug_ident ctxt) then error "Cannot finish in a non-debug state" else ();
        val f = get_finish (get_the_debug_ident ctxt);
      in f |> poke_error |> apfst clear_debug end)




fun continue_cmd i_opt m_opt state =
let
  val {context,...} = Proof.simple_goal state;
  val check = Method.map_source (Method.method_closure (init_interactive context))

  val m_opt' = Option.map (check o Method.check_text context o fst) m_opt;

  fun eval_method txt =
    (fn (ctxt,thm) => try (fst o Seq.first_result "method") (Method.evaluate txt ctxt [] (ctxt,thm)))

  val i_opt' = case (i_opt,m_opt) of (NONE,NONE) => SOME 1 | _ => i_opt;

in continue i_opt' (Option.map eval_method m_opt') state end

val _ =
  Outer_Syntax.command @{command_keyword continue} "step to next breakpoint"
  (Scan.option Parse.int -- Scan.option Method.parse >> (fn (i_opt,m_opt) =>
    (Toplevel.proof (continue_cmd i_opt m_opt))))

val _ =
  Outer_Syntax.command @{command_keyword finish} "finish debugging"
  (Scan.succeed (Toplevel.proof (continue NONE (SOME (fn _ => NONE)))))

end
\<close>
end
