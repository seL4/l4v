(*
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory Time_Methods_Cmd imports
  Main
begin

(* See Time_Methods_Cmd_Test for documentation *)

ML \<open>
structure Time_Methods = struct
  (* Work around Isabelle running every apply method on a dummy proof state *)
  fun skip_dummy_state (method: Method.method) : Method.method =
    fn facts => fn (ctxt, st) =>
      case Thm.prop_of st of
          Const ("Pure.prop", _) $ (Const ("Pure.term", _) $ Const ("Pure.dummy_pattern", _)) =>
            Seq.succeed (Seq.Result (ctxt, st))
        | _ => method facts (ctxt, st);

  (* ML interface. Takes a list of (possibly-named) methods, then calls the supplied
   * callback with the method index (starting from 1), supplied name and timing.
   * Also returns the list of timings at the end. *)
  fun time_methods
        (no_check: bool)
        (skip_fail: bool)
        (callback: (int * string option -> Timing.timing -> unit))
        (maybe_named_methods: (string option * Method.method) list)
        (* like Method.method but also returns timing list *)
        : thm list -> context_state -> (Timing.timing list * context_state Seq.result Seq.seq)
    = fn facts => fn (ctxt, st) => let
        fun run method =
              Timing.timing (fn () =>
                case method facts (ctxt, st) |> Seq.pull of
                  (* Peek at first result, then put it back *)
                    NONE => (NONE, Seq.empty)
                  | SOME (r as Seq.Result (_, st'), rs) => (SOME st', Seq.cons r rs)
                  | SOME (r as Seq.Error _, rs) => (NONE, Seq.cons r rs)
              ) ()

        val results = tag_list 1 maybe_named_methods
              |> map (fn (idx1, (maybe_name, method)) =>
                  let val (time, (st', results)) = run method
                      val _ =
                        if Option.isSome st' orelse not skip_fail
                        then callback (idx1, maybe_name) time
                        else ()
                      val name = Option.getOpt (maybe_name, "[method " ^ string_of_int idx1 ^ "]")
                  in {name = name, state = st', results = results, time = time} end)

        val canonical_result = hd results
        val other_results = tl results
        val return_val = (map #time results, #results canonical_result)
        fun show_state NONE = @{thm FalseE[where P="METHOD_FAILED"]}
          | show_state (SOME st) = st
      in
        if no_check then return_val else
        (* Compare the proof states that we peeked at *)
        case other_results
              |> filter (fn result =>
                    (* It's tempting to use aconv, etc., here instead of (<>), but
                     * minute differences such as bound names in Pure.all can
                     * break a proof script later on. *)
                    Option.map Thm.full_prop_of (#state result) <>
                    Option.map Thm.full_prop_of (#state canonical_result)) of
            [] => return_val
          | (bad_result::_) =>
              raise THM ("methods \"" ^ #name canonical_result ^
                         "\" and \"" ^ #name bad_result ^ "\" have different results",
                         1, map (show_state o #state) [canonical_result, bad_result])
      end
end
\<close>

method_setup time_methods = \<open>
let
  fun scan_flag name = Scan.lift (Scan.optional (Args.parens (Parse.reserved name) >> K true) false)
  val parse_no_check = scan_flag "no_check"
  val parse_skip_fail = scan_flag "skip_fail"
  val parse_maybe_name = Scan.option (Scan.lift (Parse.liberal_name --| Parse.$$$ ":"))
  fun auto_name (idx1, maybe_name) =
        Option.getOpt (maybe_name, "[method " ^ string_of_int idx1 ^ "]")
in
  parse_no_check -- parse_skip_fail --
  Scan.repeat1 (parse_maybe_name -- Method.text_closure) >>
  (fn ((no_check, skip_fail), maybe_named_methods_text) => fn ctxt =>
      let
        val max_length = tag_list 1 (map fst maybe_named_methods_text)
                         |> map (String.size o auto_name)
                         |> (fn ls => fold (curry Int.max) ls 0)
        fun pad_name s =
           let val pad_length = max_length + String.size ": " - String.size s
           in s ^ replicate_string pad_length " " end
        fun timing_callback id time = warning (pad_name (auto_name id ^ ": ") ^ Timing.message time)
        val maybe_named_methods = maybe_named_methods_text
              |> map (apsnd (fn method_text => Method.evaluate method_text ctxt))
        val timed_method = Time_Methods.time_methods no_check skip_fail timing_callback maybe_named_methods
        fun method_discard_times facts st = snd (timed_method facts st)
      in
        method_discard_times
        |> Time_Methods.skip_dummy_state
      end)
end
\<close> "Compare running time of several methods on the current proof state"

end
