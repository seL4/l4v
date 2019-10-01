(*
 * Copyright 2019, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

\<comment>\<open>
  The C parser emits long names for all local variables, as well as some
  abbreviations to shorten common ones. However, the Record library tactic
  @{ML Record.split_simp_tac} uses the long names to name the bound variables
  it generates.

  For example, say our goal looks like this:

  "\<Gamma> \<turnstile> \<lbrace> \<acute>x = 3 \<rbrace> \<acute>x :== 2 * \<acute>x \<lbrace> \<acute>x = 6 \<rbrace>"

  Pretty early on, @{method vcg} produces the expected
  verification condition:

  "\<And>state. x_' state = 3 \<Longrightarrow> 2 * x_' state = 6"

  Notice that the Simpl access \<open>\<acute>x\<close> has been desugared to
  a normal record access \<open>x_' state\<close>.  Next, @{method vcg} uses
  @{ML Record.split_simp_tac} to convert those record accesses into
  meta-variables:

  "\<And>x___int. x___int = 3 \<Longrightarrow> 2 * x___int = 6"

  Since the record *definitions* don't use the short-name alias, neither do
  the generated variable names.

  The `Shorten_Names` structure contains utilities for finding and restoring
  short names in the current bound variables.
\<close>
signature SHORTEN_NAMES =
sig
  \<comment>\<open>
    `find_short_name ctxt (long_name, typ)` looks in `ctxt` for a short name
    that corresponds to `long_name`, where `long_name` is a C parser munged
    variable name.

    Prints a warning if the found constant doesn't correspond
    to a field of type `typ` (we don't treat this as an error because there
    are some adventurous proofs that somehow use long names for an associated
    `errtyp`).
  \<close>
  val find_short_name: Proof.context -> (string * typ) -> string option;

  \<comment>\<open>
    `shorten_names_tac` is a tactic to restore short names for bound
    variables that have a long C parser name. For each bound
    variable which looks like a long C-parser name, we look for the expected
    short-name abbreviation, and if it exists we rename the bound variable
    accordingly.

    `shorten_names_tac` tries to respect the "normal" manner in which Isabelle
    mangles bound variables to avoid collisions. For example, if a tactic would
    make the goal look like @{term "\<And>x___int x___int. P"}, after renaming
    it would look like @{term "\<And>x xa. P"}.
  \<close>
  val shorten_names_tac: Proof.context -> int -> tactic;
  val shorten_names: (Proof.context -> Method.method) context_parser;

  \<comment>\<open>
    `shorten_names_preserve_new_tac` is like `shorten_names_preserve_new`, except
    it tries to preserve 'newer' (innermost) variable names and instead rename
    outer variables to avoid collisions. For example, if a tactic would make the
    goal look like @{term "\<And>x___int x___int. P"}, after renaming it would look like
    @{term "\<And>xa x. P"}.

    This tactic exists for use by tactics like `ctac` and `csymbr`, which expect
    any new bound variables they introduce to have a particular name.
  \<close>
  val shorten_names_preserve_new_tac: Proof.context -> int -> tactic;
  val shorten_names_preserve_new: (Proof.context -> Method.method) context_parser;
end;

structure Shorten_Names: SHORTEN_NAMES =
struct

fun find_short_name ctxt (long_name, typ) =
    let
      fun short_name () =
          let
            (* If we see a bound variable name like `x___int`, we do the
               following:
                 - Parse the term `myvars.x_'`, which is the alias (if any)
                   that the C parser would have defined for `myvars.x___int'`.
                 - If the abbreviation parses to a constant, check that the
                   constant name would indeed convert to `x___int`.
                 - The bound variable `x___int` will have some type `c_int`,
                   and the discovered constant *should* have some type
                   `record_scheme => c_int`, so we check that the codomain of
                   the constant is indeed `c_int`. *)
            val short_name = StringExtras.split "___" long_name |> hd;
            val abbreviation =
                (HoarePackage.varname short_name) |>
                Long_Name.qualify NameGeneration.local_rcd_name
            val candidate = try (Syntax.read_term ctxt) abbreviation
            fun check (Const (c_name, c_typ)) =
                let
                  val c_name = Long_Name.base_name c_name
                  val c_typ = try (Term.dest_funT #> snd) c_typ
                  fun warn_typ () =
                      if c_typ = SOME typ
                      then ()
                      else warning ("Found short name '" ^ short_name ^ "' for '" ^ long_name ^
                                   "', but with unexpected type (wanted " ^
                                   (@{make_string} typ) ^ ", but found " ^
                                   (@{make_string} c_typ) ^ ")")
                in
                  if c_name = HoarePackage.varname long_name
                  then (warn_typ (); SOME short_name)
                  else NONE
                end
              | check _ = raise Match
          in
            Option.mapPartial check candidate
          end
    in
      (* Only try and find short names for C parser long names, since
         `short_name` is an expensive exception-catching function. *)
      if String.isSubstring "___" long_name
      then short_name ()
      else NONE
    end;

local
  fun rename_one (old, new) =
      let
        val old = Abs (old, dummyT, Term.dummy);
        val new = Abs (new, dummyT, Term.dummy);
      in
        Thm.rename_boundvars old new
      end;
in
  fun shorten_names_tac ctxt = CSUBGOAL (fn (cgoal, _) =>
      let
        val goal = Thm.term_of cgoal;
        val params = Logic.strip_params goal;
        val renames = params |>
            map_filter (fn (long_name, typ) =>
              find_short_name ctxt (long_name, typ) |> Option.map (pair long_name))
        val rename = fold rename_one renames
        val rename_tac = rename #> Seq.single
      in
        TRY rename_tac
      end)
end

val shorten_names =
    Scan.succeed (shorten_names_tac #> Method.SIMPLE_METHOD');

local
  \<comment>\<open>
    Normally, if a method adds new colliding variable names, the new variable
    gets adjusted to avoid the collision. As an example, if you started with
    bound variables `x y` and introduced a new bound variable also called `x`,
    the result would be `x y xa`.

    Other tactics, like `csymbr`, *force* the new variable to have a particular
    name. If you call `csymbr` three times and each time it adds a variable
    called `x`, the result is `xa xb x`.

    We can replicate this behaviour by using @{method rename_tac}. `renames`
    identifies the suffix of the current param list which we should rename
    (leaving the prefix to be adjusted in the event of collisions).

    For example, if our current variables are `x x___int y z___unsigned`, and
    both long names can be shortened, `renames` will return

    `["x", "y", "z"]`

    And the resulting variables will be

    `xa x y z`.
  \<close>
  fun prepend x xs = x :: xs;
  fun renames_collect ctxt (nm, typ) (names: string list option) =
      case find_short_name ctxt (nm, typ) of
        NONE => Option.map (prepend nm) names
      | SOME short_name => SOME (names |> the_default [] |> prepend short_name);
  fun renames ctxt params =
      fold (renames_collect ctxt) params NONE |> the_default [] |> rev;

in
  fun shorten_names_preserve_new_tac ctxt = CSUBGOAL (fn (cgoal, i) =>
      let
        val goal = Thm.term_of cgoal;
        val params = Logic.strip_params goal;
        val renames = renames ctxt params;
      in
        Tactic.rename_tac renames i |> TRY
      end)
end

val shorten_names_preserve_new =
    Scan.succeed (shorten_names_preserve_new_tac #> Method.SIMPLE_METHOD');

end
