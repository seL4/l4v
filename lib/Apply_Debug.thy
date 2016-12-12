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
  imports Main "~~/src/HOL/Eisbach/Eisbach_Tools"
  keywords "apply_debug" :: "prf_script" % "proof" and
    "continue" :: prf_script % "proof" and  "finish" :: prf_script % "proof"
begin

ML \<open>
signature APPLY_DEBUG =
sig
val break : Method.method;
val apply_debug : Method.text_range -> Proof.state -> Proof.state;
val continue : int -> Proof.state -> Proof.state;
val finish : Proof.state -> Proof.state;

end

structure Apply_Debug : APPLY_DEBUG =
struct
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
     (if st_eq (#post_state (nth (rev (#results e)) n)) st then SOME (false, I)
     else SOME (true, map_restart (apsnd (fn _ => n))))
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

structure Debug_Data = Proof_Data
(
  type T = debug_state Synchronized.var option  (* execution id *) *
  int (* continuation counter *)
  fun init _ : T = (NONE,~1)
);

fun set_debug_ident ident = Debug_Data.map  (apfst (fn _ => SOME ident))
val get_debug_ident = the o fst o Debug_Data.get

val is_debug_ctxt = is_some o fst o Debug_Data.get;
val clear_debug = Debug_Data.map (apfst (fn _ => NONE) o apsnd (fn _ => ~1));


val get_continuation = snd o Debug_Data.get;

(* Maintain pointer equality if possible *)
fun set_continuation i ctxt = if get_continuation ctxt = i then ctxt else
  Debug_Data.map (apsnd (fn _ => i)) ctxt;

val break = (fn _ => fn (st as (ctxt,_)) =>
  let
    val id = get_debug_ident ctxt;

    val st' = Seq.make (fn () =>
     SOME (pop_state id st,Seq.empty))

  in Seq.make_results st' end) : Method.method

val _ = Context.>> (Context.map_theory (Method.setup @{binding break}
  (Scan.succeed (fn _ => break)) ""))

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

val _ = Context.>> (Context.map_theory (Sign.print_translation
 [(@{const_syntax Trueprop}, fn ctxt => (last_click := get_latest_range ctxt; (fn [x] => x)))]))


fun do_apply pos rng m =
let
  val _ = Method.report m;

in
 (fn st => map_state (fn (ctxt,_) =>
  let
     val ident = Synchronized.var "debug_state" init_state;
     val markup_id = Synchronized.var "markup_state" init_markup_state;
     val _ = if is_debug_ctxt ctxt then
      error "Cannot use apply_debug while debugging" else ();

     val st = Proof.map_context (set_markup_state markup_id o set_debug_ident ident o set_continuation ~1) st;

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
     val _ = Future.fork (fn () =>
       let
        fun do_hilight_work () =
          let
            val _ =
              case !last_click of NONE => clear_hilight (SOME markup_id)
                | SOME rng => set_hilight (SOME markup_id) rng;
            val _ = OS.Process.sleep (seconds 0.1)
          in do_hilight_work () end
        in do_hilight_work () end)



     val st' =
     let
       val (r,b) = wait_break_state ident 0;

       val st' = case r of ERR e =>
          (do_markup rng Markup.running; error (e ()))
        | RESULT st' => st'

       val st'' = if b then (Output.writeln "Final Result."; st' |> apfst clear_debug)
                     else st' |> apfst (set_continuation 0)

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
            val (f,trans_id) = Synchronized.guarded_access ident (fn e as {restart,next_state,...} =>
              if is_restarting e andalso is_none next_state then
              SOME ((fst restart, #trans_id e), restart_state (snd restart) e) else NONE);
            val _ = f ();
            val _ = clear_running (SOME markup_id);
            val thread = do_fork (trans_id + 1);
            val _ = Synchronized.change ident (map_restart (fn _ => (fn () => do_cancel thread, ~1)))
          in main_loop () end
      in main_loop () end)

   in st' end) st)
end

fun apply_debug (m', rng) =
  let
      val m'' = add_debug m'
      val m = (m'',rng)
      val pos = Position.thread_data ();
     in do_apply pos rng m end;

val _ =
  Outer_Syntax.command @{command_keyword apply_debug} "initial goal refinement step (unstructured)"
    (Method.parse >> (fn txt => Toplevel.proof (apply_debug txt)));

val finish = map_state (fn (ctxt,_) =>
      let
        val _ = if get_continuation ctxt < 0 then error "Cannot finish in a non-debug state" else ();
        val f = get_finish (get_debug_ident ctxt);
      in f |> poke_error |> apfst clear_debug end)

val _ =
  Outer_Syntax.command @{command_keyword finish} "finish debugging"
  (Scan.succeed (Toplevel.proof finish))

fun continue i =
(map_state (fn (ctxt,thm) =>
      let
        val _ = if i < 1 then error "Must continue a non-zero amount" else ();
        val _ = if get_continuation ctxt < 0 then error "Cannot continue in a non-debug state" else ();

        val id = get_debug_ident ctxt;

        val start_cont = get_continuation ctxt; (* how many breakpoints so far *)
        val trans_id = maybe_restart id start_cont (ctxt,thm);
          (* possibly restart if the thread has made too much progress.
             trans_id is the current number of restarts, used to avoid manipulating
             stale states *)

        val _ = nth_pre_result id start_cont; (* block until we've hit the start of this continuation *)

        val cont = start_cont + i; (* final number of breakpoints hit *)

        val ex_results = peek_all_results id |> rev;

        fun tick_up n st = if n = cont then (st,false) else
          let
            val _ = set_next_state id trans_id st;
            val (n_r, b) = wait_break_state id trans_id;
            val results = peek_all_results id;
            val _ = if length results = n + 1 then () else
              error ("Unexpected number of results. Expected: " ^ @{make_string } (n + 1)^ " but got " ^ @{make_string } (length results))
            val st' = poke_error n_r;
          in if b then ((st',b)) else tick_up (n + 1) st' end

        val (st',b) =
          if length ex_results > cont then
            (#pre_state (nth ex_results cont), false)
          else if length ex_results = cont then
            wait_break_state id trans_id |> apfst poke_error
          else if length ex_results = start_cont then
            tick_up (length ex_results) (ctxt, thm)
          else (debug_print id; @{print} ("start_cont",start_cont); @{print} ("trans_id",trans_id);
            error "Unexpected number of existing results")

        val st'' = if b then (Output.writeln "Final Result."; st' |> apfst clear_debug)
                   else st' |> apfst (set_continuation cont)

      in st'' end))

val _ =
  Outer_Syntax.command @{command_keyword continue} "step to next breakpoint"
  (Scan.optional Parse.int 1 >> (fn i =>
    (Toplevel.proof (continue i))))

end
\<close>

lemma
  assumes AB: "A \<Longrightarrow> B"
  assumes BA: "B \<Longrightarrow> A"
  assumes BC: "B \<Longrightarrow> C"
  assumes CB: "C \<Longrightarrow> B"
  assumes DC: "D \<Longrightarrow> C"
  assumes DE: "D \<Longrightarrow> E"
  assumes ED: "E \<Longrightarrow> D"
  assumes FE: "F \<Longrightarrow> E"
  assumes EF: "E \<Longrightarrow> F"
  shows
  "A"
  (*
  apply_debug (sleep 1, break, rule BA, sleep 1, break, rule AB, sleep n)
  continue
  continue

  apply_debug (break, tactic \<open>fn st => raise TERM ("foo",[@{term True}])\<close>)
    continue *)
  apply_debug (sleep 1, rule BA, break, sleep 1,rule BA, rule CB, break, rule DC, sleep 1, break, rule ED, sleep 1, break, rule EF)
    apply (rule AB)
    continue
      apply -
      apply -

    continue
      apply -
      apply -
    continue
    continue
  oops
  (*
  apply_debug (sleep 1, rule BA, break, sleep 1,rule BA, rule CB, break, rule DC, sleep 1, break, rule ED, sleep 1, break, rule EF)
  continue
  continue
    apply (rule ED)
    apply (rule DE)
  continue
    apply (rule FE)
  continue
  oops
    (* continue
      apply -
    continue
    continue
      apply (rule FE)
      apply (sleep 1)
    continue
    oops*)

    (*
  apply_debug (sleep 1, rule BA, break, sleep 1, rule DC, break, rule FE, break)
    apply (rule CB)
      continue
        apply (rule ED)
      continue
      finish
      finish

    oops
    (* continue
    oops
(*      apply (rule DC)
    continue

    oops
  (*
   stop
   continue
   continue

  apply -
  subgoal
  apply -
  apply_debug ((sleep 1, rule quirk) | (sleep 1, rule baz) | sleep 2)
  print_state
  ML_prf \<open>Synchronized.value rr\<close>
  ML \<open>error (Position.here_list (Synchronized.value rr)) \<close>
  done

end


(*
              (*let val n_ex =
                if length ex_results > cont then
                  let
                    val _ = @{print} "restarting.."
                    val _ = Synchronized.guarded_access id (fn e => if snd (#restart e) > 0 then NONE else
                        SOME ((), map_restart (fn (f,_) => (f, start_cont)) e));
                    val _ = Synchronized.guarded_access id (fn e => if snd (#restart e) > 0 then NONE else SOME ((),e));
                    val _ = @{print} ("ex_results_pre", peek_all_results id)
                    val _ = @{print} ("prev_results_pre", #prev_results (Synchronized.value id))
                    val st = nth_result id (start_cont);
                    val _ = @{print} ("execution starts..", st)

                  in start_cont + 1 end
                else length ex_results*)

ML \<open>
val _ =
  Outer_Syntax.command @{command_keyword done'} "done proof"
    (Scan.succeed
      (Toplevel.end_proof_deferred
        (fn defer => (@{print} "baz"; (K Proof.global_done_proof)))
          (@{print} "foo"; (K Proof.global_done_proof))));
\<close>
(*
lemma "True"

  apply (tactic \<open>fn st => (@{print} "pre_sleep"; Seq.single st)\<close>)
  apply (sleep 10)
  apply (tactic \<open>fn st => (@{print} "post_sleep"; Seq.single st)\<close>)
  apply simp
  done'*)
ML \<open>Exn.reraise\<close>
ML \<open>val e = error "foo" handle e => e\<close>
ML \<open>val e' = Exn_Properties.position e\<close>

ML \<open>Proof.pretty_state\<close>
ML \<open>Runtime.exn_messages_ids\<close>
ML \<open>Exn_Properties.get e\<close>
ML \<open>Runtime.exn_messages_ids\<close>
ML \<open>Runtime.exn_context\<close>
ML \<open> val pos = @{here}\<close>
ML \<open>Markup.markup_only\<close>
ML \<open>Output.error_message "foo"\<close>

ML \<open>
let
  val _ = Position.report pos Markup.accepted
in () end\<close>

ML \<open>t : unit Exn.result\<close>
lemma
  assumes A: "\<And>x :: 'b. PROP (P x)"
  assumes B: "\<And>x :: 'b. PROP (P x) \<Longrightarrow> PROP (P x)"
  shows
  "\<And>x :: 'b. PROP (P x) \<Longrightarrow> PROP (P x)"
  apply ( sleep 10)
  subgoal for x
    apply (rule B[where x=x])
      term x
    by -
  apply -
  apply (sleep 1)
  apply (sleep 1)
  apply (sleep 1, rule)
  apply (rule B)
  apply (rule B)

  done

lemma "PROP P \<Longrightarrow> PROP P"
  apply (sleep 5)
  done

end
(*

ML \<open>fun f a b = a ? b\<close>

ML \<open>Runtime.controlled_execution\<close>

ML \<open>Proof_Context.cert_propp\<close>
lemmas

ML \<open>Thm.biresolution\<close>
ML \<open>Drule.multi_resolves\<close>

ML \<open>
(* Pending lemmas *)
structure Data = Generic_Data
(
  type T = (Proof.context -> (local_theory -> local_theory)) list;
  val empty = [];
  val extend = I;
  fun merge data : T = uncurry append data;
);

fun collapse_pending context =
  let
    val ps = Data.get context;
    val ctxt = Context.proof_of context;
    val (exit, lthy) = Named_Target.switch NONE context;
    val context' = fold (fn f => fn lthy => f lthy) (map (fn p => p ctxt) ps) lthy |> exit;

  in Data.map (fn _ => []) context' end

\<close>
ML \<open>is_none NONE\<close>
ML \<open>
local

val long_keyword =
  Parse_Spec.includes >> K "" ||
  Parse_Spec.long_statement_keyword;

val long_statement =
  Scan.optional (Parse_Spec.opt_thm_name ":" --| Scan.ahead long_keyword) Binding.empty_atts --
  Scan.optional Parse_Spec.includes [] -- Parse_Spec.long_statement
    >> (fn ((binding, includes), (elems, concl)) => (true, binding, includes, elems, concl));

val short_statement =
  Parse_Spec.statement -- Parse_Spec.if_statement -- Parse.for_fixes
    >> (fn ((shows, assumes), fixes) =>
      (false, Binding.empty_atts, [], [Element.Fixes fixes, Element.Assumes assumes],
        Element.Shows shows));

fun wrap_shows' ctxt (nm, concls) =
  (nm, map (fn (t, ts) => (Syntax.read_term ctxt t, Syntax.read_terms ctxt ts)) concls)

fun wrap_shows (Element.Shows l) = (fn ctxt => Element.Shows (map (wrap_shows' ctxt) l))
  | wrap_shows _ = raise Fail "Unexpected";

local
val simple_asm  = (fn ((_,atts),_) => List.all (fn att => length att < 2) atts)
in
fun simple_elem (Element.Fixes _) = true
  | simple_elem (Element.Assumes l) = List.all simple_asm l
  | simple_elem (Element.Constrains _) = true
  | simple_elem (Element.Defines _) = true
  | simple_elem (Element.Notes _) = false
end

fun do_proof long binding elems concl =
  let
    val finish = (fn ctxt =>
      Specification.theorem_cmd long Thm.theoremK NONE (K I) binding [] elems concl true
      #> Proof.global_skip_proof true)
  in Proof.theorem NONE
  (fn _ => Local_Theory.background_theory
    (Context.theory_map (Data.map (fn ts => finish :: ts)))) [] end


fun theorem spec schematic descr =
  Outer_Syntax.local_theory_to_proof' spec ("state " ^ descr)
    ((long_statement || short_statement) >>
      (fn (long, binding, includes, elems, concl) =>
      (if null includes andalso (List.all simple_elem elems)
      then (fn _ => do_proof long binding elems concl) else
      (if schematic then Specification.schematic_theorem_cmd else Specification.theorem_cmd)
        long Thm.theoremK NONE (K I) binding includes elems concl)
      ));

val _ = theorem @{command_keyword lemma'} false "lemma'";

in end\<close>
lemmas
ML \<open>
Context.theory_of
\<close>

ML \<open>


\<close>

ML \<open>Parse.propp\<close>

ML \<open>Outer_Syntax.local_theory_to_proof' @{command_keyword lemma'} "lemma'"\<close>

syntax
  "_bazz" :: "idt => bool"  ("_!&" [70] 61)

parse_translation \<open>[(@{syntax_const "_bazz"},fn ctxt =>
  fn ts => (OS.Process.sleep (seconds 0.1);@{print} "foo"; hd ts))]\<close>

lemma'   baz:
  assumes P:False
  shows
  "foo!&"
  done


lemma' baz2:
  assumes P:False
  shows
  "foo!&"
  done

ML \<open>Data.get (Context.Theory @{theory})\<close>

ML \<open> Context.>> collapse_pending\<close>

thm baz

ML \<open>Named_Target.switch\<close>

lemma' baz[simp]: "([1,2] ! 3) = undefined (1 :: nat)"
  apply sleep
  apply (simp add: nth_def)


lemma "([] ! 1) = ([] ! 2)"


lemma foo
  apply rule
  oops

ML \<open>Named_Theorems.declare\<close>

named_theorems baz

method_setup add_named_theorem =
  \<open>Attrib.thms >> (fn [thm'] => (fn thms' => fn ctxt =>
    (fn (context,thm) => Seq.single (
    Context.proof_map (Named_Theorems.add_thm "Scratch.baz" thm') context , thm)
    |> Seq.make_results)))\<close>

ML \<open>Method.assumption\<close>

schematic_goal "?P"
  subgoal

lemma assumes P:"P"
  shows  "P"
  thm baz

  subgoal
    apply (add_named_theorem P)
  thm baz
  using P
  apply (use in \<open>rule method_facts\<close>)
  done
  thm baz
done

thm baz

lemma P
  apply (rule baz)



end
