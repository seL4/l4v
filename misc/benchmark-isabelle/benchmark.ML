(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Simple benchmarking framework for determining the speed of ML operations
 * in Isabelle.
 *
 * We benchmark functions of the form "unit -> 'a" (i.e., we pass in a unit
 * type, throw away the result, and time how long this takes). For each
 * function that we benchmark we first:
 *
 *   1. Estimate how many times we could run it in a second;
 *
 *   2. Run it enough times so that it runs for approximately
 *      SECONDS_PER_RUN seconds.
 *
 *   3. Measure how long step (2) actually took, and divide out
 *      by the number of iterations we performed.
 *
 *   4. Repeat this process NUM_SAMPLES times.
 *
 * This gives us a reasonable measurement of the function's time.
 *
 * 2011 David Greenaway
 *)
signature BENCHMARK =
sig
  val benchmark : string -> (unit -> 'a) -> string
  val benchmark_set : string -> ('a -> 'b) -> ('a -> int) -> 'a list -> string list
  val category : string -> unit
end

structure Benchmark : BENCHMARK =
struct

val NUM_SAMPLES = 5;
val SECONDS_PER_RUN = 3.0;

(* Perform the given action 'n' times. *)
fun perform 0 _ = ()
  | perform (n : int) (f : unit -> 'a) = (f () ; perform (n - 1) f)

(* Repeat the given action 'n' times, returning the results as a list. *)
fun iterate 0 _ = []
  | iterate (n : int) (f : unit -> 'a) = (f () :: iterate (n - 1) f)

(* Time how long it takes to run the given function 'n' times. *)
fun simple_benchmark (n : int) (f : unit -> 'a) =
  let
    val start = Timing.start ();
    val _ = perform n f;
    val finish = Timing.result start;
  in
    {
      wall = #elapsed finish |> Time.toReal,
      gc = #gc finish |> Time.toReal,
      cpu = #cpu finish |> Time.toReal
    }
  end

(* Guess how many times this function could run in 1 second. *)
fun guess_iterations_per_second (f : unit -> 'a) =
  let
    fun do_guess n =
      let
        val t = simple_benchmark n f;
        val time = #wall t
        val num_per_second = if time > 0.0 then floor (real n / time) else 0
      in
        if time > 0.05 then num_per_second else do_guess (n * 2)
      end
  in
    do_guess 1
  end

(* Simple statistical functions. *)

fun sum [] = 0.0
  | sum (x::xs) = x + sum xs

fun avg x = (sum x / real (length x))

fun variance x =
  let
    val a = avg x
  in
    avg (map (fn n => (n - a) * (n - a)) x)
  end

fun stddev x = Math.sqrt (variance x)

(* Benchmark the given function 'num_samples' times. *)
fun benchmark_raw num_samples (f : unit -> 'a) =
  let
    (* Determine number of samples needed to run for SECONDS_PER_RUN. *)
    val iterations_needed = (floor (real (guess_iterations_per_second f) * SECONDS_PER_RUN)) + 1;

    (* Grab the samples. *)
    val samples =
      iterate (num_samples + 1) (fn _ => simple_benchmark iterations_needed f)
        (* Throw away the first result; it may be bogus due to caching,
         * dynamic compilation, etc. *)
        |> tl
  in
    {
      time        = avg    (map (fn x => (#cpu x) / real iterations_needed) samples),
      time_stddev = stddev (map (fn x => (#cpu x) / real iterations_needed) samples),
      results     = (map (fn x => (#cpu x) / real iterations_needed) samples)
    }
  end

(* High-level benchmark function. *)
fun benchmark name f =
  let
    (* Get the benchmark results. *)
    val results = benchmark_raw NUM_SAMPLES f;

    (* Pretty print string. What I would give for a sprintf() function. *)
    val S = Real.fmt (StringCvt.FIX (SOME 1));
    val P = StringCvt.padLeft #" ";
    val R = StringCvt.padRight #" ";
    val dev_percent = (#time_stddev results) / (#time results);
    val cpu_string = (S (#time results * 1000000.0)) ^  " us"
    val dev_percent_str = S (dev_percent * 100.0)
    val result_string =
      (R 32 name) ^ ": "
      ^ (P 12 cpu_string)
      ^ " (sd " ^ P 5 dev_percent_str ^ "%,"
      ^ " " ^ P 11 (S (1.0 /(#time results))) ^ " op/s)"

    (* Print to output for parsing scripts to use. *)
    val _ = tracing ("result:: " ^ result_string)
  in
    result_string
  end

(* Export a category marker. *)
fun category name = tracing ("category:: " ^ name)

(* Run a benchmark on a series of inputs. *)
fun benchmark_set name f measure items =
  map (fn t => benchmark (name ^ " (" ^ (Int.fmt StringCvt.DEC (measure t)) ^ ")") (fn _ => f t)) items;


end

