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

ML \<open>
infix 1 CONTEXT_THEN;
infix 0 CONTEXT_THEN_ELSE;

signature CONTEXT_TACTICALS =
sig
val CONTEXT_REPEAT_DETERM_N : int -> context_tactic -> context_tactic;
val CONTEXT_REPEAT_DETERM : context_tactic -> context_tactic;
val CONTEXT_CHANGED : context_tactic -> context_tactic;
val CONTEXT_THEN : context_tactic * context_tactic -> context_tactic;
val CONTEXT_THEN_ELSE: context_tactic * (context_tactic * context_tactic) -> context_tactic;
val SOME_CONTEXT_TACTIC: (Proof.context -> tactic) -> context_tactic;
end

structure Context_Tacticals : CONTEXT_TACTICALS =
struct

fun make_tactic r = (fn st => Seq.make_results (Seq.make (fn () => r st))) : context_tactic;

fun CONTEXT_REPEAT_DETERM_N n tac =
  let
    fun drep 0 st = SOME (st, Seq.empty)
      | drep n st =
          (case Seq.pull (Seq.filter_results (tac st)) of
            NONE => SOME(st, Seq.empty)
          | SOME (st', _) => drep (n - 1) st');
  in make_tactic (drep n) end;

val CONTEXT_REPEAT_DETERM = CONTEXT_REPEAT_DETERM_N ~1;

fun CONTEXT_CHANGED tac (ctxt,st) =
  let fun diff (_, st') = not (Thm.eq_thm (st, st'));
  in Seq.make_results (Seq.filter diff (Seq.filter_results (tac (ctxt, st)))) end;

fun ((tac1 : context_tactic) CONTEXT_THEN (tac2 : context_tactic)) = (fn st =>
  Seq.maps_results tac2 (tac1 st)) : context_tactic;

fun (tac CONTEXT_THEN_ELSE (tac1, tac2)) st =
  (case Seq.pull (Seq.filter_results (tac st)) of
    NONE => tac2 st  (*failed; try tactic 2*)
  | some => Seq.maps tac1 (Seq.make (fn () => some)));  (*succeeded; use tactic 1*)

fun SOME_CONTEXT_TACTIC (tac : Proof.context -> tactic) =
  (fn (ctxt,thm) => Method.CONTEXT ctxt (tac ctxt thm)) : context_tactic

end

open Context_Tacticals;

signature APPLY_DEBUG =
sig
type break_opts = { tags : string list, trace : (string * Position.T) option }

val break : string option -> context_tactic;
val apply_debug : break_opts -> Method.text_range -> Proof.state -> Proof.state;
val continue : break_opts -> int option -> (context_state -> context_state option) option -> Proof.state -> Proof.state;
val finish : Proof.state -> Proof.state;

end

structure Apply_Debug : APPLY_DEBUG =
struct
type break_opts = { tags : string list, trace : (string * Position.T) option }

fun do_markup range m = Output.report [Markup.markup (Markup.properties (Position.properties_of_range range) m) ""];

type markup_queue = { cur : Position.range option, next : Position.range option, clear_cur : bool }

fun map_cur f ({cur, next, clear_cur} : markup_queue) =
  ({cur = f cur, next = next, clear_cur = clear_cur} : markup_queue)

fun map_next f ({cur, next, clear_cur} : markup_queue) =
  ({cur = cur, next = f next, clear_cur = clear_cur} : markup_queue)

fun map_clear_cur f ({cur, next, clear_cur} : markup_queue) =
  ({cur = cur, next = next, clear_cur = f clear_cur} : markup_queue)

type markup_state =
  { running : markup_queue,
    hilight : markup_queue
  }

fun map_running f ({running, hilight} : markup_state) =
  {running = f running, hilight = hilight}

fun map_hilight f ({running, hilight} : markup_state) =
  {running = running, hilight = f hilight}

structure Markup_Data = Proof_Data
(
  type T = markup_state Synchronized.var option *
    Position.range option (* latest method location *)
  fun init _ : T = (NONE, NONE)
);

val init_queue = ({cur = NONE, next = NONE, clear_cur = false}: markup_queue)
val init_markup_state = ({running = init_queue, hilight = init_queue} : markup_state)

fun set_markup_state id = Markup_Data.map (apfst (K (SOME id)));
fun get_markup_id ctxt = fst (Markup_Data.get ctxt);

fun set_latest_range range = Markup_Data.map (apsnd (K (SOME range)));
fun get_latest_range ctxt = snd (Markup_Data.get ctxt);

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

fun markup_worker (id : markup_state Synchronized.var) =
let
  fun main_loop () =
    let val _ = Synchronized.guarded_access id (fn e =>
    case swap_markup (#running e) Markup.running Markup.finished of
      SOME queue' => SOME ((),map_running (fn _ => queue') e)
    | NONE => case swap_markup (#hilight e) Markup.forked Markup.joined of
        SOME queue' => SOME ((), map_hilight (fn _ => queue') e)
       | NONE => NONE)
     in main_loop () end
in main_loop () end

fun set_gen get set (SOME id) rng =
  let
    val _ =
       Synchronized.guarded_access id (fn e =>
         if is_some (#next (get e)) orelse (#clear_cur (get e)) then NONE
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

val set_hilight = set_gen #hilight map_hilight
val clear_hilight = clear_gen #hilight map_hilight

val _ = Context.>>
  (Context.map_theory (Method.setup @{binding "markup"}
  (Scan.state :|-- (fn st => Scan.lift (Scan.trace (Scan.pass st Method_Closure.method_text))) >>
   (fn (text, toks) => fn ctxt => fn facts =>
   let
     val range = case (Token.get_value (hd toks)) of
     SOME (Token.Source src) => Token.range_of src
     | _ => Position.no_range
     val markup_id = get_markup_id ctxt;

     fun tac (ctxt,thm) =
      let val ctxt' = set_latest_range range ctxt in
        Method_Closure.method_evaluate text ctxt' facts (ctxt',thm)
      end

     fun traceify seq = Seq.make (fn () =>
      let
        val _ = set_running markup_id range;
        val r = Seq.pull seq;
        val _ = clear_running markup_id;
      in Option.map (apsnd traceify) r end)

   in traceify o tac end)) ""))

fun wrap_src src =
  let
    val pos = Token.range_of src |> Position.set_range;
    val tok = Token.make_string ("", pos);
    val tok' = Token.assign (SOME (Token.Source src)) tok;
  in Token.closure tok' end


fun add_debug (Method.Source src) =
      (Method.Source (Token.make_src ("Apply_Debug.markup", Position.none) [wrap_src src]))
  | add_debug (Method.Combinator (x,y,txts)) = (Method.Combinator (x,y, map add_debug txts))
  | add_debug x = x

fun st_eq (ctxt : Proof.context,st) (ctxt',st') =
  pointer_eq (ctxt,ctxt') andalso Thm.eq_thm (st,st')

type result =
  { pre_state : (Proof.context * thm),
    post_state : (Proof.context * thm) }

datatype final_state = RESULT of (Proof.context * thm) | ERR of (unit -> string)

type debug_state =
  {results : result list, (* this execution, in order of appearance *)
   prev_results : (Proof.context * thm) list, (* continuations needed to get thread back to some state*)
   next_state : (Proof.context * thm) option, (* proof thread blocks waiting for this *)
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

fun add_result pre post = map_results (cons {pre_state = pre, post_state = post}) o drop_states;

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

fun pop_state_no_block id pre = guarded_access id (fn e =>
  if is_finished e then error "Attempted to pop state from finished proof" else
  if (#ignore_breaks e) then SOME (SOME pre, add_result pre pre) else
  case #prev_results e of
     [] => SOME (NONE, I)
   | (st :: sts) => SOME (SOME st, add_result pre st o map_prev_results (fn _ => sts)))

fun pop_next_state id pre = guarded_access id (fn e =>
  if is_finished e then error "Attempted to pop state from finished proof" else
  if not (null (#prev_results e)) then error "Attempted to pop state when previous results exist" else
    if (#ignore_breaks e) then SOME (pre, add_result pre pre) else
    (case #next_state e of
            NONE => NONE
          | SOME st => SOME (st, add_result pre st)))

fun set_next_state id trans_id st = guarded_access id (fn e =>
  (assert_trans_id trans_id e;
   (if is_none (#next_state e) andalso is_some (#break_state e) then
     SOME ((), map_next_state (fn _ => SOME st) o map_break_state (fn _ => NONE))
   else error ("Attempted to set next state in inconsistent state" ^ (@{make_string} e)))))

fun set_break_state id st = guarded_access id (fn e =>
  if is_none (#next_state e) andalso is_none (#break_state e) then
    SOME ((), map_break_state (fn _ => SOME st))
  else error ("Attempted to set break state in inconsistent state" ^ (@{make_string} e)))

fun pop_state id pre =
  case pop_state_no_block id pre of SOME st => st
  | NONE =>
  let
    val _ = set_break_state id pre; (* wait for continue *)
  in pop_next_state id pre end

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
     (*(if st_eq (#post_state (nth (rev (#results e)) n)) st then SOME (false, I)
     else*) SOME (true, map_restart (apsnd (fn _ => n)))
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

fun nth_pre_result id i = guarded_read id
  (fn e =>
    if length (#results e) > i then SOME (RESULT (#pre_state (nth (rev (#results e)) i)), false) else
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


val no_break_opts = ({tags = [], trace = NONE} : break_opts)

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
val get_debug_ident = the o #1 o Debug_Data.get

fun set_break_opts opts = Debug_Data.map (@{apply 5 (4)} (fn _ => opts))
val get_break_opts = #4 o Debug_Data.get;

fun set_last_tag tags = Debug_Data.map (@{apply 5 (5)} (fn _ => tags))
val get_last_tag = #5 o Debug_Data.get;

val is_debug_ctxt = is_some o #1 o Debug_Data.get;
val clear_debug = Debug_Data.map (fn _ => (NONE,~1,false, no_break_opts, NONE));


val get_continuation = #2 o Debug_Data.get;
val get_can_break = #3 o Debug_Data.get;

(* Maintain pointer equality if possible *)
fun set_continuation i ctxt = if get_continuation ctxt = i then ctxt else
  Debug_Data.map (@{apply 5 (2)} (fn _ => i)) ctxt;

fun set_can_break b ctxt = if get_can_break ctxt = b then ctxt else
  Debug_Data.map (@{apply 5 (3)} (fn _ => b)) ctxt;

fun has_break_tag (SOME tag) tags = member (op =) tags tag
  | has_break_tag NONE _ = true;

fun break tag = (fn (ctxt,thm) =>
if not (get_can_break ctxt) orelse not (has_break_tag tag (#tags (get_break_opts ctxt)))
   orelse Method.detect_closure_state thm
    then Seq.make_results (Seq.single (ctxt,thm)) else
  let
    val id = get_debug_ident ctxt;
    val ctxt' = set_last_tag tag ctxt;

    val st' = Seq.make (fn () =>
     SOME (pop_state id (ctxt',thm),Seq.empty))

  in Seq.make_results st' end) : context_tactic

val _ = Context.>> (Context.map_theory (Method.setup @{binding break}
  (Scan.lift (Scan.option Parse.string) >> (fn tag => fn _ => fn _ => break tag)) ""))

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

val last_click = Unsynchronized.ref (NONE : Position.range option)

fun maybe_trace (SOME (tr, pos)) (ctxt, st) =
let
  val deps = Apply_Trace.used_facts ctxt st;
  val query = if tr = "" then NONE else SOME (tr, pos);
  val pr = Apply_Trace.pretty_deps false query ctxt st deps;
in Pretty.writeln pr end
  | maybe_trace NONE (ctxt, st) =
    if is_some (#trace (get_break_opts ctxt)) then
     maybe_trace (#trace (get_break_opts ctxt)) (ctxt,st)
    else ()

fun do_apply pos rng opts m =
let
  val _ = Method.report m;
  val {tags, trace} = opts;

in
 (fn st => map_state (fn (ctxt,_) =>
  let
     val ident = Synchronized.var "debug_state" init_state;
     val markup_id = Synchronized.var "markup_state" init_markup_state;
     val _ = if is_debug_ctxt ctxt then
      error "Cannot use apply_debug while debugging" else ();

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

        val r = case Exn.interruptible_capture (fn st => (case (Seq.pull o Proof.apply m) st
          of (SOME (Seq.Result st', _)) => RESULT (get_state st')
           | (SOME (Seq.Error e, _)) => ERR e
           | _ => ERR (fn _ => "No results"))) st
           of Exn.Res (RESULT r) => RESULT r
             | Exn.Res (ERR e) => ERR e
            | Exn.Exn e => ERR (fn _ => Runtime.exn_message e)
        val _ = set_finished_result ident trans_id r;

        val _ = clear_running (SOME markup_id);

       in () end)



     val thread = do_fork 0;
     val _ = Synchronized.change ident (map_restart (fn _ => (fn () => do_cancel thread, ~1)));

     val _ = do_markup rng Markup.finished;

     val _ = Future.fork (fn () => markup_worker markup_id ());

     fun do_hilight_work () =
           case !last_click of NONE => clear_hilight (SOME markup_id)
             | SOME rng => set_hilight (SOME markup_id) rng;

     val st' =
     let
       val (r,b) = wait_break_state ident 0;

       val st' = case r of ERR e =>
          (do_markup rng Markup.running; error (e ()))
        | RESULT st' => st'

       val st'' = if b then (Output.writeln "Final Result."; st' |> apfst clear_debug)
                     else st' |> apfst (set_continuation 0) |> apfst (set_can_break false)

     in st''  end

     val _ = do_markup rng Markup.joined;

     val _ = if get_continuation (fst st') < 0 then
      (do_markup rng Markup.running;do_markup rng Markup.forked; Future.fork (fn () => ())) else
      Execution.fork {name = "apply_debug_main", pos = pos, pri = ~1} (fn () =>
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
            val _ = do_hilight_work ();
            in case r of NONE => main_loop ()
            | SOME (f,trans_id) =>
              let
                val _ = f ();
                val _ = clear_running (SOME markup_id);
                val thread = do_fork (trans_id + 1);
                val _ = Synchronized.change ident (map_restart (fn _ => (fn () => do_cancel thread, ~1)))
              in main_loop () end
           end;
       in main_loop () end)

       val _ = maybe_trace trace st';

   in st' end) st)
end

fun apply_debug opts (m', rng)  =
  let
      val m'' = add_debug m'
      val m = (m'',rng)
      val pos = Position.thread_data ();

     in do_apply pos rng opts m end;

fun quasi_keyword x = Scan.trace (Args.$$$ x) >>
  (fn (s,[tok]) => (Position.reports [(Token.pos_of tok, Markup.quasi_keyword)]; s))

val parse_tags = (Args.parens (quasi_keyword "tags" |-- Parse.enum1 "," Parse.string));
val parse_trace = Scan.option (Args.parens (quasi_keyword "trace" |-- Scan.option (Parse.position Parse.cartouche))) >>
  (fn SOME NONE => SOME ("", Position.none) | SOME (SOME x) => SOME x | _ => NONE);

val parse_opts1 = (parse_tags -- parse_trace) >>
  (fn (tags,trace) => {tags = tags, trace = trace} : break_opts);

val parse_opts2 = (parse_trace -- (Scan.optional parse_tags [])) >>
  (fn (trace,tags) => {tags = tags, trace = trace} : break_opts);

val parse_opts = parse_opts1 || parse_opts2;

val _ =
  Outer_Syntax.command @{command_keyword apply_debug} "initial goal refinement step (unstructured)"
    (Scan.trace
      (parse_opts --  Method.parse) >>
      (fn ((opts, (m,_)),toks) => Toplevel.proof (apply_debug opts (m,Token.range_of toks))));

val finish = map_state (fn (ctxt,_) =>
      let
        val _ = if get_continuation ctxt < 0 then error "Cannot finish in a non-debug state" else ();
        val f = get_finish (get_debug_ident ctxt);
      in f |> poke_error |> apfst clear_debug end)


fun continue opts i_opt m_opt =
(map_state (fn (ctxt,thm) =>
      let
        val {tags, trace} = opts;
        val ctxt = set_can_break true ctxt;
        val thm = Apply_Trace.clear_deps thm;

        val _ = if get_continuation ctxt < 0 then error "Cannot continue in a non-debug state" else ();

        val id = get_debug_ident ctxt;

        val start_cont = get_continuation ctxt; (* how many breakpoints so far *)
        val trans_id = maybe_restart id start_cont (ctxt,thm);
          (* possibly restart if the thread has made too much progress.
             trans_id is the current number of restarts, used to avoid manipulating
             stale states *)

        val _ = nth_pre_result id start_cont; (* block until we've hit the start of this continuation *)

        fun get_final n (st as (ctxt,_))  =
        if not (has_break_tag (get_last_tag ctxt) (#tags (get_break_opts ctxt))
                orelse has_break_tag (get_last_tag ctxt) tags) then NONE else
         case (i_opt,m_opt) of
          (SOME i,NONE) => if i < 1 then error "Can only continue a positive number of breakpoints" else
            if n = start_cont + i then SOME st else NONE
         | (NONE, SOME m) => m st
         | (_, _) => error "Invalid continue arguments"

        val ex_results = peek_all_results id |> rev;

        fun tick_up n st =
          if n < length ex_results then error "Unexpected number of existing results"
           (*case get_final n (#pre_state (nth ex_results n)) of SOME st' => (st', false, n)
            | NONE => tick_up (n + 1) st *)
          else
          let
            val _ = if n > length ex_results then set_next_state id trans_id st else ();
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
                   else st' |> apfst (set_continuation cont) |> apfst (set_can_break false);

        val _ = maybe_trace trace st'';

      in st'' end))

fun continue_cmd opts i_opt m_opt state =
let
  val {context,...} = Proof.simple_goal state;
  val check = Method.map_source (Method.method_closure context)

  val m_opt' = Option.map (check o Method.check_text context o fst) m_opt;

  fun eval_method txt =
    (fn (ctxt,thm) => try (fst o Seq.first_result "method") (Method.evaluate txt ctxt [] (ctxt,thm)))

  val i_opt' = case (i_opt,m_opt) of (NONE,NONE) => SOME 1 | _ => i_opt;

in continue opts i_opt' (Option.map eval_method m_opt') state end

val _ =
  Outer_Syntax.command @{command_keyword continue} "step to next breakpoint"
  (parse_opts -- Scan.option Parse.int -- Scan.option Method.parse >> (fn ((opts, i_opt),m_opt) =>
    (Toplevel.proof (continue_cmd opts i_opt m_opt))))

val _ =
  Outer_Syntax.command @{command_keyword finish} "finish debugging"
  (Scan.succeed (Toplevel.proof (continue {tags = [], trace = NONE} NONE (SOME (fn _ => NONE)))))

val _ =
  Query_Operation.register {name = "print_state", pri = Task_Queue.urgent_pri}
    (fn {state = st, output_result, ...} =>
      if Toplevel.is_proof st
      then
        (last_click := get_latest_range (Proof.context_of (Toplevel.proof_of st));
        output_result (Markup.markup Markup.state (Toplevel.string_of_state st)))
      else ());

end
\<close>
end
