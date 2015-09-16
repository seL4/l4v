
AutoCorres
==========

AutoCorres is a tool that assists reasoning about C programs
in [Isabelle/HOL][1]. In particular, it uses Norrish's
[C-to-Isabelle parser][2] to parse C into Isabelle, and then
abstracts the result to produce a result that is (hopefully)
more pleasant to reason about.

  [1]: http://www.cl.cam.ac.uk/research/hvg/Isabelle/
  [2]: http://ssrg.nicta.com.au/software/TS/c-parser/


Quickstart
----------

To use AutoCorres, you need to (i) run the C parser, and then (ii) run
AutoCorres. For example, assume you want to parse a file `myfile.c`
containing a function `foo`. Start by creating an Isabelle theory file
`Example.thy` as follows:

    theory Example
    imports AutoCorres
    begin

    (* Run the C-to-Isabelle parser. *)
    install_C_file "myfile.c"

    (* Run autocorres. *)
    autocorres "myfile.c"

    (* Enter the locale where all the theories reside. *)
    context myfile begin

    (* Show the output of the C parser. *)
    thm foo_body_def

    (* Show the output of AutoCorres. *)
    thm foo'_def

    end

    end

Each function `foo` in your input file will have a definition in
Isabelle/HOL with the name `foo'`.

You can perform some basic reasoning using the Hoare framework and
associated tools developed by NICTA and distributed with AutoCorres.

Options
-------

AutoCorres supports a variety of options, which are used as follows:

    autocorres [option, key=val, list=a b c d] "file.c"

The options are:

  * `unsigned_word_abs = FUNC_NAMES`: Use _word abstraction_
    on unsigned integers in the given functions.

  * `no_signed_word_abs = FUNC_NAMES`: Disable signed
    _word abstraction_ on the given list of functions.

  * `skip_word_abs`: Completely disable _word abstraction_.

  * `ts_rules = RULES`: Enable _type strengthening_ to the
    following types. Possible types include `pure` (pure
    functional), `option` (option monad without state), `gets` (option
    monad with state) and `nondet` (non-deterministic state monad).

  * `ts_force RULE_NAME = FUNC_NAMES`: Force the given
    functions to be type-strengthened to the given type,
    even if a "better" type could otherwise be used.
    See `tests/examples/type_strengthen_tricks.thy`.

  * `no_heap_abs = FUNC_NAMES`: Disable _heap abstraction_
    on the given list of functions.

  * `force_heap_abs = FUNC_NAMES`: Attempt _heap abstraction_
    on the given list of functions, even if AutoCorres' heuristics
    believes that they cannot be lifted.

  * `heap_abs_syntax`: Enable experimental heap abstraction
    syntactic sugar.

Name compatibility options:

  * `lifted_globals_field_prefix="foo"`, `lifted_globals_field_suffix="foo"`:
    Override generated names for global variables during heap abstraction.
    The default is `f` -> `f_''` (i.e. prefix="", suffix="_''").

  * `function_name_prefix="foo"`, `function_name_suffix="foo"`:
    Override generated names for abstracted functions.
    The default is `f` -> `f'` (i.e. prefix="", suffix="'").

Less common options (mainly for debugging):

  * `keep_going`: Attempt to ignore certain non-critical
    errors.

  * `scope`: Only parse the given functions and their
    callees, up to depth `scope_depth`.

  * `trace_heap_lift = FUNC_NAMES`: Trace the _heap abstraction_
    process for each of the given functions. The traces
    are stored in the Isabelle theory and can be quite large.
    See `tests/examples/TraceDemo.thy`.

  * `trace_word_abs = FUNC_NAMES`: As above, but traces
    _word abstraction_.

  * `trace_opt`: As above, but traces internal simplification
    phases (for all functions).

  * `no_opt`: Disable some optimisation passes that simplify
    the AutoCorres output.

  * `gen_word_heaps`: Force _heap abstraction_ to create
    abstract heaps for standard `word` types
    (`word8`, `word16`, `word32`, `word64`) even if they
    are not needed.

An example of invoking AutoCorres with _all_ of the options
is as follows:

    autocorres [
        unsigned_word_abs = f g h,
        no_signed_word_abs = i j k,
        skip_word_abs,  (* mutually exclusive with previous rules *)
        ts_rules = pure nondet,
        ts_force nondet = l m n,
        no_heap_abs = a b,
        force_heap_abs = c d,
        heap_abs_syntax,
        keep_going,
        scope = o p q,
        scope_depth = 5,
        trace_heap_lift = c d,
        trace_word_abs = f h i,
        no_opt,
        gen_word_heaps,
        lifted_globals_name_prefix="my_global_",
        lifted_globals_name_suffix="",
        function_name_prefix="my_func_",
        function_name_suffix=""
        ] "filename.c"

Examples
--------

Some basic examples are in the `tests/examples` directory.

Many of these examples are quick-and-dirty proofs, and should not
necessary be considered the best style.

None-the-less, some of the examples available are, in approximate
increasing level of difficulty:

  * `Simple.thy`: Proofs of some simple functions, including
    `max` and `gcd`.

  * `Swap.thy`: Proof of a simple `swap` function.

  * `MultByAdd.thy`: Proof of a function that carries out
    multiplication using addition.

  * `Factorial.thy`: Proof of a factorial function, using
    several different methods.

  * `FibProof.thy`: Proof of the Fibonacci function, using
    several different methods.

  * `ListRev.thy`: Proof of a function that carries out an
    in-place linked list reversal.

  * `IsPrime.thy`: Proof of a function that determines if
    the input number is prime.

  * `MemCpy.thy`: Proof of a C `memcpy` implementation.

  * `MemSet.thy`: Proof of a C `memset` implementation.

  * `Quicksort.thy`: Proof of a simple QuickSort
    implementation on an array of `int`s.

  * `BinarySearch.thy`: Proof of a function that determines
    if a sorted input array of `unsigned int` contains the
    given `unsigned int`.

  * `SchorrWaite.thy`: Proof a C implementation of the
    Schorr-Waite algorithm, using Mehta and Nipkow's
    high-level proof.


Papers
------

AutoCorres is an ongoing research project. Papers related to the project
are:

  * David Greenaway, June Andronick, and Gerwin Klein.
    [_"Bridging the gap: Automatic verified abstraction of C."_][3]
    In Interactive Theorem Proving, pp. 99-115. Springer
    Berlin Heidelberg, 2012.

  * David Greenaway, Japheth Lim, June Andronick, and Gerwin Klein.
    [_"Don't sweat the small stuff: formal verification of C code without the pain."_][4]
    In Proceedings of the 35th ACM SIGPLAN Conference on
    Programming Language Design and Implementation, p. 45.
    ACM, 2014.

  [3]: http://www.ssrg.nicta.com.au/publications/papers/Greenaway_AK_12.pdf
  [4]: http://www.nicta.com.au/pub?doc=7629

