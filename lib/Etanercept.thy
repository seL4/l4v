(*
 * Copyright 2015, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Etanercept (* FIXME: broken, untested *)
imports
  "$L4V_ARCH/WordSetup"
  "ml-helpers/TermPatternAntiquote"
keywords
  "word_refute" :: diag
begin

text {*
  This theory implements a tool for refuting word propositions. It works by constructing a C program
  that exhaustively explores the state space of your proposition.

  Usage:
    Run the "word_refute" command in a proof. The proof goal should involve only word
    and boolean expressions.
  Options:
    These are config options which can be set using "declare" or "using".
    - word_refute_debug        enable verbose debugging output
    - word_refute_timeout      timeout, in seconds

  It is currently a work in progress and has the following known issues:
   - Temporary files are just left for Isabelle to clean up when it exits. Should we be attempting
     to remove these ourselves?
   - The exploration strategy is completely naive, which simplifies the code, but sometimes leads to
     a failure to find trivial counter-examples.
   - There's no support for HOL binders like \<forall> and \<exists>. These could be supported relatively easily
     with GNU statement expressions, but I'm unsure if it's worth it.
   - We currently only support 8-, 16-, 32-, and 64-bit words. It would be straightforward to
     support other non-standard widths if required.

  The tool is named after etanercept, an ill-advised treatment for primary progressive aphasia, a
  condition who's symptoms include an inability to find the right words for things. Amusingly the
  word "etanercept" is also quite hard to remember.
*}

ML {*
  signature ETANERCEPT =
  sig
  end;

  structure Etanercept : ETANERCEPT =
  struct

  (* Toggle this to enable debugging output. *)
  val config_debug = let
    val (config, setup) = Attrib.config_bool (Binding.name "word_refute_debug") (K false)
  in
    Context.>>(Context.map_theory setup);
    config
  end

  (* Timeout, in seconds. *)
  val config_timeout = let
    val (config, setup) = Attrib.config_real (Binding.name "word_refute_timeout") (K 60.0)
  in
    Context.>>(Context.map_theory setup);
    config
  end

  (* C compiler options. Rationale:
   *   -O3: search for counterexamples faster
   *   -fwrapv: match HOL-Word semantics for signed overflow
   *)
  val config_cflags = "-O3 -fwrapv"

  fun debug_log ctxt str = if Config.get ctxt config_debug then tracing str else ()

  (* XXX: Clagged from metis *)
  fun dropWhile p =
    let
      fun f [] = []
        | f (l as x :: xs) = if p x then f xs else l
    in
      f
    end

  (* Exponentiation. *)
  fun exp _    0 = 1
    | exp base n = if n mod 2 = 0 then exp (base*base) (n div 2) else base * exp base (n - 1)

  (* Strip whitespace from the end of a string. *)
  fun rstrip s =
    s
    |> String.explode
    |> List.rev
    |> dropWhile Char.isSpace
    |> List.rev
    |> String.implode

  (* Generate a string that's safe to put in a C string. In particular, we escape backslashes and
   * remove trailing underscores. The latter is not for string safety, but because focusing leads to
   * a variable named, e.g. "x__", that originated from a meta-bound "x". Stripping these
   * underscores makes the counter-example output clearer to the user.
   *)
  fun safe_name s =
    s
    |> String.explode
    |> map (fn c => if c = #"\\" then "\\\\" else String.implode [c])
    |> List.rev
    |> dropWhile (fn c => c = "_")
    |> List.rev
    |> String.concat

  (* Find a C compiler. Prefer Clang. *)
  fun cc () =
    let
      val (clang, r1) = Isabelle_System.bash_output "which clang";
      val (gcc, r2) = Isabelle_System.bash_output "which gcc"
    in
      if r1 = 0 then SOME (rstrip clang ^ " -Wno-tautological-compare") else
      if r2 = 0 then SOME (rstrip gcc) else
      NONE
    end

  (* Compile a C program. *)
  fun compile ctxt file =
    case cc () of
        SOME compiler =>
          let
            val serial = serial_string ();
            val tmp = File.shell_path (File.tmp_path (Path.explode ("etanercept" ^ serial ^ ".exe")));
            val cmd = compiler ^ " " ^ config_cflags ^ " -o " ^ tmp ^ " " ^ file
            val _ = debug_log ctxt ("Compiling: " ^ cmd)
            val (_, ret) = Isabelle_System.bash_output cmd
          in
            if ret = 0
              then tmp
              else error "Etanercept: failed to compile generated program (BUG)"
          end
      | NONE => error "Etanercept: no available C compiler"

  (* Mapping between Isabelle and C variables. *)
  fun var_index (vs, sz) v =
        case Termtab.lookup vs v of
            NONE => ((Termtab.update_new (v, sz) vs, sz+1), sz)
          | SOME n => ((vs, sz), n)
  val empty_var_index = (Termtab.empty, 0)

  (* The C symbol for the nth variable. *)
  fun to_var n = "v" ^ Int.toString n
  (* Create variable list from mapping *)
  val var_index_list =
        fst #> Termtab.dest
        #> sort (int_ord o apply2 snd)
        #> map (apsnd to_var)

  fun name_of (Free (name, _)) = safe_name name
    | name_of t = raise TERM ("Etanercept: unexpected variable (BUG)", [t])


  (* Types that we know about. *)
  type IntInfo = { isa_type: typ,
                   c_type:   string,
                   c_min:    string,
                   c_max:    string,
                   c_printf: string
                 }
  val type_info : IntInfo Typtab.table =
    [
      { isa_type = @{typ "8 word"},
        c_type = "uint8_t",
        c_min = "((uint8_t)0)",
        c_max = "UINT8_MAX",
        c_printf = "PRIu8"
      },
      { isa_type = @{typ "16 word"},
        c_type = "uint16_t",
        c_min = "((uint16_t)0)",
        c_max = "UINT16_MAX",
        c_printf = "PRIu16"
      },
      { isa_type = @{typ "32 word"},
        c_type = "uint32_t",
        c_min = "((uint32_t)0)",
        c_max = "UINT32_MAX",
        c_printf = "PRIu32"
      },
      { isa_type = @{typ "64 word"},
        c_type = "uint64_t",
        c_min = "((uint64_t)0)",
        c_max = "UINT64_MAX",
        c_printf = "PRIu64"
      },
      { isa_type = @{typ "nat"},
        c_type = "uintmax_t",
        c_min = "((uintmax_t)0)",
        c_max = "UINTMAX_MAX",
        c_printf = "PRIuMAX"
      },

      { isa_type = @{typ "8 signed word"},
        c_type = "int8_t",
        c_min = "INT8_MIN",
        c_max = "INT8_MAX",
        c_printf = "PRId8"
      },
      { isa_type = @{typ "16 signed word"},
        c_type = "int16_t",
        c_min = "INT16_MIN",
        c_max = "INT16_MAX",
        c_printf = "PRId16"
      },
      { isa_type = @{typ "32 signed word"},
        c_type = "int32_t",
        c_min = "INT32_MIN",
        c_max = "INT32_MAX",
        c_printf = "PRId32"
      },
      { isa_type = @{typ "64 signed word"},
        c_type = "int64_t",
        c_min = "INT64_MIN",
        c_max = "INT64_MAX",
        c_printf = "PRId64"
      },
      { isa_type = @{typ "int"},
        c_type = "intmax_t",
        c_min = "INTMAX_MIN",
        c_max = "INTMAX_MAX",
        c_printf = "PRIdMAX"
      }
    ] |> (fn infos => Typtab.make (map (fn info => (#isa_type info, info)) infos))

  fun lookup_info f expect_success t =
    let val severity = if expect_success then " (BUG)" else ""
    in case t of
           Free (_, ty) => (case Typtab.lookup type_info ty of
                                SOME info => f info
                             | NONE => raise TYPE ("etanercept: unsupported type" ^ severity, [ty], [t]))
         | _ => raise TERM ("Etanercept: unsupported term" ^ severity, [t]) end

  val min_of = lookup_info #c_min true
  val max_of = lookup_info #c_max true
  val type_of = lookup_info #c_type true
  val format_of = lookup_info #c_printf true

  fun cast_to _ (Type ("fun", [from, to])) =
        (case try (lookup_info #c_type false) (Free ("_", to)) of
             SOME c_type => c_type
           | NONE => raise TYPE ("Etanercept: unsupported ucast/scast result type", [to], []))
    | cast_to _ T = raise TYPE ("Etanercept: strange ucast/scast type (BUG)", [T], [])

  (* A printf format string for printing the variables. *)
  fun format_string vs =
    var_index_list vs
    |> map (fn (var, c_var) => "\" " ^ name_of var ^ " = %\" " ^ format_of var ^ " \"\\n\" ")
    |> String.concat

  (* The variables as a list of arguments to be passed to a C function. *)
  fun as_args vs =
    var_index_list vs
    |> map (fn (var, c_var) => ", " ^ c_var)
    |> String.concat

  (* Initialisation for the variables. *)
  fun loop_header vs =
    var_index_list vs
    |> map (fn (var, c_var) =>
              type_of var ^ " " ^ c_var ^ ";\n" ^
              "for (" ^ c_var ^ " = " ^ min_of var ^ "; ; " ^ c_var ^ "++) {\n")
    |> String.concat

  (* Per-variable loop termination. *)
  fun loop_footer vs =
    var_index_list vs
    |> rev
    |> map (fn (var, c_var) =>
              "if (" ^ c_var ^ " == " ^ max_of var ^ ") { break; }\n}\n")
    |> String.concat

  (* Translate an Isabelle term into the equivalent C expression, collecting discovered variables
   * along the way.
   *)
  fun translate state vs t =
    let
      val tr = translate state
      fun bin_op op1 op2 =
        let val (vs', s1) = tr vs op1;
            val (vs'', s2) = tr vs' op2
          in (vs'', s1, s2)
        end
    in
      case t of
          @{term "Trueprop"} $ t' => tr vs t'
        | @{term "True"} => (vs, "true")
        | @{term "False"} => (vs, "false")
        | @{term_pat "?a = ?b"} =>
            let val (vs', s1, s2) = bin_op a b
              in (vs', "(" ^ s1 ^ " == " ^ s2 ^ ")")
            end
        | @{term_pat "\<not> ?a"} =>
            let val (vs', s) = tr vs a
              in (vs', "(!" ^ s ^ ")")
            end
        | @{term_pat "?a < ?b"} =>
            let val (vs', s1, s2) = bin_op a b
              in (vs', "(" ^ s1 ^ " < " ^ s2 ^ ")")
            end
        | @{term_pat "?a \<le> ?b"} =>
            let val (vs', s1, s2) = bin_op a b
              in (vs', "(" ^ s1 ^ " <= " ^ s2 ^ ")")
            end
        | @{term_pat "?a + ?b"} =>
            let val (vs', s1, s2) = bin_op a b
              in (vs', "(" ^ s1 ^ " + " ^ s2 ^ ")")
            end
        | @{term_pat "?a - ?b"} =>
            let val (vs', s1, s2) = bin_op a b
              in (vs', "(" ^ s1 ^ " - " ^ s2 ^ ")")
            end
        | @{term_pat "?a * ?b"} =>
            let val (vs', s1, s2) = bin_op a b
              in (vs', "(" ^ s1 ^ " * " ^ s2 ^ ")")
            end
        | @{term_pat "- ?a"} =>
            let val (vs', s) = tr vs a
              in (vs', "(-" ^ s ^ ")")
            end
        | @{term_pat "?a div ?b"} =>
            let val (vs', s1, s2) = bin_op a b
              in (vs', "(" ^ s2 ^ " == 0 ? 0 : (" ^ s1 ^ " / " ^ s2 ^ "))")
            end
        | @{term_pat "?a mod ?b"} =>
            let val (vs', s1, s2) = bin_op a b
              in (vs', "(" ^ s2 ^ " == 0 ? " ^ s1 ^ " : (" ^ s1 ^ " % " ^ s2 ^ "))")
            end
        | @{term_pat "?a \<longrightarrow> ?b"} =>
            let val (vs', s1, s2) = bin_op a b
              in (vs', "((!" ^ s1 ^ ") || (" ^ s2 ^ "))")
            end
        | @{term_pat "shiftl ?a ?b"} =>
            let val (vs', s1, s2) = bin_op a b
              in (vs', "(" ^ s1 ^ " << " ^ s2 ^ ")")
            end
        | @{term_pat "shiftr ?a ?b"} =>
            let val (vs', s1, s2) = bin_op a b
              in (vs', "(" ^ s1 ^ " >> " ^ s2 ^ ")")
            end
        | @{term_pat "?a && ?b"} =>
            let val (vs', s1, s2) = bin_op a b
              in (vs', "(" ^ s1 ^ " & " ^ s2 ^ ")")
            end
        | @{term_pat "?a || ?b"} =>
            let val (vs', s1, s2) = bin_op a b
              in (vs', "(" ^ s1 ^ " | " ^ s2 ^ ")")
            end
        | @{term_pat "?a xor ?b"} =>
            let val (vs', s1, s2) = bin_op a b
              in (vs', "(" ^ s1 ^ " ^ " ^ s2 ^ ")")
            end
        | @{term_pat "NOT ?a"} =>
            let val (vs', s) = tr vs a
              in (vs', "(~" ^ s ^ ")")
            end
        | @{term_pat "test_bit ?a ?b"} =>
            let val (vs', s1, s2) = bin_op a b
              in (vs', "(" ^ s1 ^ " ^ & (1ULL << " ^ s2 ^ "))")
            end
        | @{term_pat "lsb ?a"} =>
            let val (vs', s) = tr vs a
              in (vs', "(" ^ s ^ " & 1)")
            end
        | Const (@{const_name Word.ucast}, typ) $ a =>
            let val (vs', s) = tr vs a
              in (vs', "((" ^ cast_to state typ ^ ")" ^ s ^ ")")
            end
        | Const (@{const_name Word.scast}, typ) $ a =>
            let val (vs', s) = tr vs a
              in (vs', "((" ^ cast_to state typ ^ ")" ^ s ^ ")")
            end
        | Free (name, T) =>
            if Typtab.defined type_info T
              then let val (vs', n) = var_index vs t
                     in (vs', to_var n)
                   end
              else (case T of Type ("Word.word", _) =>
                                   raise TYPE ("unsupported word width of variable " ^ name, [T], [])
                            | _ => raise TYPE ("unsupported type of variable " ^ name, [T], []))
        | @{term_pat "?a \<and> ?b"} =>
            let val (vs', s1, s2) = bin_op a b
              in (vs', "(" ^ s1 ^ " && " ^ s2 ^ ")")
            end
        | @{term_pat "?a \<or> ?b"} => 
            let val (vs', s1, s2) = bin_op a b
              in (vs', "(" ^ s1 ^ " || " ^ s2 ^ ")")
            end
        | @{term_pat "0"} => (vs, "(0)")
        | @{term_pat "1"} => (vs, "(1)")
        | @{term_pat "Suc ?a"} =>
            let val (vs', s) = tr vs a
              in (vs', "(1 + " ^ s ^ ")")
            end
        | @{term_pat "numeral ?a"} =>
            let val a' = HOLogic.dest_num a
                val suffix = if a' > exp 2 32 - 1 then "ull" else ""
              in (vs, "(" ^ string_of_int a' ^ suffix ^ ")")
            end
        | _ => raise TERM ("unsupported subterm ", [t])
    end

  (* Construct a C program to match the current goal state. *)
  fun make_program st =
    let
      val state = Toplevel.proof_of st;
      val {goal = g, ...} = Proof.raw_goal state;
      val (_, g') = Subgoal.focus (Proof.context_of state) 1 g
      val (gi, _) = Logic.goal_params (Thm.prop_of g') 1
      val (vars, expr) = translate state empty_var_index gi
    in
      "#include <inttypes.h>\n" ^
      "#include <limits.h>\n" ^
      "#include <stdbool.h>\n" ^ 
      "#include <stdint.h>\n" ^
      "#include <stdio.h>\n" ^
      "int main(void) {\n" ^
      loop_header vars ^
      "if (!" ^ expr ^ ") {\n" ^
      "printf(\"Found counter-example:\\n\"" ^ format_string vars ^ as_args vars ^ ");\n" ^
      "return 0;\n" ^
      "}\n" ^
      loop_footer vars ^
      "return -1;\n" ^
      "}"
    end

  (* Try to refute the current goal by using a C program to find a counter example. *)
  fun refute st =
        let
          val ctxt = Proof.context_of (Toplevel.proof_of st);
          val program = make_program st;
          val serial = serial_string ();
          val tmp = File.tmp_path (Path.explode ("etanercept" ^ serial ^ ".c"));
          val _ = File.write tmp program;
          val aout = compile ctxt (File.shell_path tmp);
          val _ = debug_log ctxt
                    ("Program:\n" ^ program ^ "\nWritten to: " ^ File.shell_path tmp ^ "\nCompiled to: " ^ aout)
          val (msg, ret) = TimeLimit.timeLimit (Config.get ctxt config_timeout |> Time.fromReal)
                             Isabelle_System.bash_output aout
        in
          (if ret = 0
             then msg
             else "Etanercept found no counter example")
          |> writeln
        end
        handle TimeLimit.TimeOut =>
          warning "Etanercept: timed out"

  (* Install the command itself. *)
  val _ = Outer_Syntax.command @{command_keyword word_refute}
            "Construct a C program to find counter-examples to word propositions"
              (Scan.succeed [] >> (fn _ => Toplevel.keep_proof refute))

  end
*}


text {* Basic examples *}
lemma "True \<and> False"
  word_refute
  oops

lemma "(x::32 word) = 0"
  word_refute

  using [[word_refute_debug]]
  word_refute
  oops

word_refute -- "requires a proof state"

text {* Can deal with top-level quantified vars *}
lemma "\<And>x. (x::32 word) \<noteq> y\<^sub>1 \<and> y \<ge> x"
  word_refute
  oops

lemma "(x::8 word) = y"
  word_refute
  oops

lemma "(x::64 word) < y"
  word_refute
  oops

lemma "\<And>(x::32 word) y. x = y"
  word_refute
  oops

text {* Previously, this example would give us a tautological comparison warning from Clang. *}
lemma "y = y \<and> (x::32 word) << y = x"
  word_refute
  oops

text {* Also works for nats (approximated with uint64) *}
lemma "(x :: nat) = 0"
  word_refute
  oops

text {* Example that partially demonstrates Etanercept's utility. *}
lemma "(x::8 word) > y \<or> x < y + y + y + y"
  (* quickcheck cannot handle this *)
    (* quickcheck *)
  (* quickcheck[random] takes a little while *)
    quickcheck[random]
  (* Etanercept immediately finds the trivial counterexample *)
    word_refute
  oops

text {* Example that demonstrates one of Etanercept's weaknesses. *}
lemma "(x::32 word) div y = x"
  (* The naive exploration strategy means we wait for Etanercept to try every value of y before
   * moving x beyond 0.
   *)
  word_refute
  oops

text {*
  This is an interesting example that, due to Etanercept's exploration strategy, *should* be out of
  its reach with a reasonable time out. Instead, the C compiler folds the entire loop into immediate
  discovery of a counter-example.
*}
lemma "(x::64 word) \<ge> y \<and> x \<ge> y + y"
  word_refute
  oops

text {* Various cases that test our handling of numeric literals. *}
lemma "(x::32 word) && 45 = 0"
  word_refute
  oops
lemma "(x::32 word) < 45"
  word_refute
  oops
lemma "(x::32 word) < 0"
  word_refute
  oops
lemma "(x::32 word) < 1"
  word_refute
  oops
lemma "(x::32 word) < 0x45"
  word_refute
  oops

text {* Test something non-trivial that we shouldn't be able to refute. *}
lemma "(x::32 word) && 1 = 1 \<and> x && (~~ 1) = 0 \<longrightarrow> x = 1"
  word_refute
  apply word_bitwise
  done
lemma "(x::32 signed word) && 1 = 1 \<and> x && (~~ 1) = 0 \<longrightarrow> x = 1"
  word_refute
  apply word_bitwise_signed
  done

text {* Test that division by zero is correctly modelled with Isabelle's semantics. *}
lemma "(x::64 word) div 0 = 0"
  word_refute
  by (simp add: word_arith_nat_defs(6))

text {* Test we can handle large literals. *}
lemma "0xdeadbeeffacecafe > 0xdeadbeeffacade00 + (x::64 word)"
  word_refute
  oops

text {* Test some casting operations. *}
lemma "(ucast::32 signed word \<Rightarrow> 32 word) (x::32 signed word) = (y::32 word)"
  word_refute
  oops
lemma "ucast (x::32 word) = (y:: 8 word)"
  word_refute
  oops
lemma "ucast (x::32 word) = (y::32 word)"
  word_refute
  oops
lemma "scast (x::32 signed word) = (y::8 word)"
  word_refute
  oops

text {* Try some things we shouldn't be able to refute. *}
lemma "(x::64 word) >> 0 = x"
  word_refute
  by simp
lemma "(x::64 word) >> 1 = x div 2"
  word_refute
  apply simp
  apply (rule shiftr_div_2n_w[where n=1, simplified])
  apply (simp add:word_size)
  done
lemma "(x::64 word) << 1 = x * 2"
  word_refute
  apply (subst shiftl_t2n)
  apply simp
  done

text {* Test that our compiler setup permits signed overflow *}
lemma "(x :: 32 signed word) < x + 1"
  word_refute -- "should find INT_MAX"
  oops

text {* C translation pitfalls *}
lemma "(ucast (x * y :: 16 word) :: 32 signed word) \<ge> 0"
  text {* A naive translation fails due to semantic mismatch *}
  word_refute
  by simp


text {* Unsupported constructs *}
lemma "(x :: 1 word) = 0" -- "bad word size"
  (* word_refute *)
  oops

end
