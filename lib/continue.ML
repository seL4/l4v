(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(* Hack to make isabelle sessions continue building after encountering
   tactic failures. Provides an alternative version of use_thy and use
   to those from pure_setup.ML or ThyInfo.
*)

structure ContinueOnFailure = struct

val thynames = Unsynchronized.ref ([] : string list);

val _ = ThyInfo.add_hook
  (K (fn thyname => (thynames := thyname :: (! thynames))));

fun scan_transs_depths [] _ = []
  | scan_transs_depths (t :: ts) s =
      Toplevel.level s :: scan_transs_depths ts (Toplevel.command t s)

fun dict_of_props props
    = "{" ^ commas (map (fn (a, b) => a ^ " = " ^ b) props) ^ "}";

val long_site_of = dict_of_props o Position.properties_of o Toplevel.pos_of; 

fun apply_transs [] s = s
  | apply_transs ((t, n) :: ts) s
    = apply_transs ts (Toplevel.command t s)
        handle Interrupt => raise Interrupt
          | _ => let
    val i = find_index (fn (_, n') => n' < n) ts;
    val ts' = Library.drop (i, ts);
    val t' = fst (hd ts');
  in
    tracing ("use_thy_continue: skipping from " ^ Toplevel.str_of t
      ^ " resuming at " ^ Toplevel.str_of t');
    tracing ("  (" ^ long_site_of t ^ " - " ^ long_site_of t' ^ ")");
    s |> Toplevel.command (IsarCmd.skip_proof Toplevel.empty)
      |> apply_transs (Library.drop (i, ts))
  end 

fun set_flags () = let in
    quick_and_dirty := true;
    Toplevel.skip_proofs := false;
    Goal.parallel_proofs := 0;
    Multithreading.max_threads := 1;
    ()
  end;

fun use_thy_continue thyname = let
    val _ = set_flags ();
    val path = Path.explode thyname;
    val base = Path.base path |> Path.implode;
    val text = File.read (Path.append (Path.dir path) (ThyLoad.thy_path base));
    val transs = OuterSyntax.parse (Position.file base) text;
    val _ = Toplevel.skip_proofs := true;
    val depths = scan_transs_depths transs Toplevel.toplevel;
    val _ = Toplevel.skip_proofs := false;
  in
    apply_transs
      ((transs ~~ depths) @ [(Toplevel.commit_exit Position.none, 0)])
      Toplevel.toplevel;
    ()
  end;

fun get_thy_absname thyname
  = Path.append (ThyInfo.master_directory thyname)
      (Path.basic thyname) |> Path.implode;

fun use_continue mlfile
  = (set_flags (); thynames := []; ThyInfo.use mlfile)
  handle Interrupt => raise Interrupt
    | _ => let
    fun trace_loading s = tracing ("use_continue: reloading " ^ s);
  in
    tracing "use_continue: got exn, checking for partially-loaded thys";
    (! thynames)
      |> filter_out (Option.isSome o ThyInfo.lookup_theory)
      |> map (use_thy_continue o tap trace_loading o get_thy_absname)
    ;
    tracing "use_continue: loaded all partially-loaded thys";
    use_continue mlfile
  end;

end

