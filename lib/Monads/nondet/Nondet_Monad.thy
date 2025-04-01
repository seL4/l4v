(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
   Nondeterministic state and error monads with failure in Isabelle.
*)

chapter "Nondeterministic State Monad with Failure"

theory Nondet_Monad
  imports
    Fun_Pred_Syntax
    Monad_Lib
begin

text \<open>
  \label{c:monads}

  State monads are used extensively in the seL4 specification. They are defined below.\<close>

section "The Monad"

record 'c monad_state_record =
  env :: 'c

type_synonym ('c, 's) monad_state = "('c, 's) monad_state_record_scheme"

type_synonym ('c, 's) mpred = "('c, 's) monad_state \<Rightarrow> bool"

abbreviation monad_state :: "'c \<Rightarrow> 's \<Rightarrow> ('c, 's) monad_state" where
  "monad_state c \<equiv> \<lambda>s. \<lparr> env = c, \<dots> = s \<rparr>"

abbreviation mstate :: "('c, 's) monad_state \<Rightarrow> 's" where
  "mstate \<equiv> monad_state_record.more"

abbreviation with_env_of :: "('c, 's) monad_state \<Rightarrow> 't \<Rightarrow> ('c, 't) monad_state" where
  "with_env_of s \<equiv> monad_state (env s)"

definition map_state :: "('s \<Rightarrow> 't) \<Rightarrow> ('c, 's) monad_state \<Rightarrow> ('c, 't) monad_state"
  where
  "map_state f \<equiv> \<lambda>s. with_env_of s (f (mstate s))"

definition const_env ::
  "(('c, 's) monad_state \<Rightarrow> ('d, 't) monad_state) \<Rightarrow> ('c, 's) monad_state \<Rightarrow> ('c, 't) monad_state"
  where
  "const_env f \<equiv> \<lambda>s. with_env_of s (mstate (f s))"

definition is_const_env :: "(('c, 's) monad_state \<Rightarrow> ('c, 't) monad_state) \<Rightarrow> bool"
  where
  "is_const_env f \<equiv> \<forall>s. env (f s) = env s"

text \<open>
  The basic type of the nondeterministic state monad with failure is
  very similar to the normal state monad. Instead of a pair consisting
  of result @{typ 'a} and new state @{typ 's}, we return a set of these
  pairs coupled with a failure flag. Each element in the set is a potential
  result of the computation. The flag is @{const True} if there is an
  execution path in the computation that may have failed. Conversely, if
  the flag is @{const False}, none of the computations resulting in the
  returned set has failed. The monad also takes as input an environment
  state @{typ 'c}, which is constant throughout the execution.\<close>
type_synonym ('c, 's, 'a) nondet_monad = "('c, 's) monad_state \<Rightarrow> ('a \<times> 's) set \<times> bool"

text \<open>
  Print the type @{typ "('c, 's, 'a) nondet_monad"} instead of its unwieldy expansion.
  Needs an AST translation in code, because it needs to check that the state variable
  @{typ 's} occurs twice. This comparison is not guaranteed to always work as expected
  (AST instances might have different decoration), but it does seem to work here.\<close>
print_ast_translation \<open>
  let
    fun monad_tr _ [Ast.Appl [Ast.Constant @{type_syntax monad_state}, env, st],
                    Ast.Appl [Ast.Constant @{type_syntax prod},
                          Ast.Appl [Ast.Constant @{type_syntax set},
                            Ast.Appl [Ast.Constant @{type_syntax prod}, rv, st']],
                          Ast.Constant @{type_syntax bool}]] =
      if st = st'
      then Ast.Appl [Ast.Constant @{type_syntax "nondet_monad"}, env, st, rv]
      else raise Match
  in [(@{type_syntax "fun"}, monad_tr)] end
\<close>

text \<open>
  The definition of fundamental monad functions @{text return} and
  @{text bind}. The monad function @{text "return x"} does not change
  the  state, does not fail, and returns @{text "x"}.\<close>
definition return :: "'a \<Rightarrow> ('c,'s,'a) nondet_monad" where
  "return a \<equiv> \<lambda>s. ({(a, mstate s)},False)"

text \<open>
  The monad function @{text "bind f g"}, also written @{text "f >>= g"},
  is the execution of @{term f} followed by the execution of @{text g}.
  The function @{text g} takes the result value \emph{and} the result
  state of @{text f} as parameter. The definition says that the result of
  the combined operation is the union of the set of sets that is created
  by @{text g} applied to the result sets of @{text f}. The combined
  operation may have failed, if @{text f} may have failed or @{text g} may
  have failed on any of the results of @{text f}. The environment passed to
  @{text g} is the same as the one passed to @{term f}.\<close>
definition bind ::
  "('c, 's, 'a) nondet_monad \<Rightarrow> ('a \<Rightarrow> ('c, 's, 'b) nondet_monad) \<Rightarrow> ('c, 's, 'b) nondet_monad"
  (infixl ">>=" 60)
  where
  "bind f g \<equiv> \<lambda>s. (\<Union>(fst ` case_prod g ` apsnd (with_env_of s) ` fst (f s)),
                   True \<in> snd ` case_prod g ` apsnd (with_env_of s) ` fst (f s) \<or> snd (f s))"

text \<open>Sometimes it is convenient to write @{text bind} in reverse order.\<close>
abbreviation (input) bind_rev ::
  "('a \<Rightarrow> ('c, 's, 'b) nondet_monad) \<Rightarrow> ('c, 's, 'a) nondet_monad \<Rightarrow> ('c, 's, 'b) nondet_monad"
  (infixl "=<<" 60)
  where
  "g =<< f \<equiv> f >>= g"

text \<open>
  The basic accessor functions of the state monad. @{text get} returns
  the current state as result, does not fail, and does not change the state.
  @{text ask} returns the constant part of the state as result, does not
  change the state and does not fail. @{text "put s"} returns nothing
  (@{typ unit}), changes the current state to @{text s} and does not fail.

  We choose to return the full state of the monad in @{text get}, including the
  constant part, because we later want @{text gets} to return the same kind of
  state that Hoare logic predicates expect, and those will need access to the
  full state. This means, @{text modify} and @{text put} should both also take
  the full state as their argument (ignoring the constant part of their
  argument), to keep the standard @{text get}/@{text put} laws intact. This
  integrates well with how @{text gets} and @{text modify} are intended to be
  used with a record type state -- the standard record update and access
  will expect the full state type, not only the variable part of the state.\<close>
definition get :: "('c,'s, ('c,'s) monad_state) nondet_monad" where
  "get \<equiv> \<lambda>s. ({(s, mstate s)}, False)"

definition ask :: "('c,'s,'c) nondet_monad" where
  "ask \<equiv> \<lambda>s. ({(env s, mstate s)}, False)"

definition put :: "('c,'s) monad_state \<Rightarrow> ('c, 's, unit) nondet_monad" where
  "put s \<equiv> \<lambda>_. ({((), mstate s)}, False)"

subsection "Nondeterminism"

text \<open>
  Basic nondeterministic functions. @{text "select A"} chooses an element
  of the set @{text A}, does not change the state, and does not fail
  (even if the set is empty). @{text "f \<sqinter> g"} executes @{text f} or
  executes @{text g}. It returns the union of results of @{text f} and
  @{text g}, and may have failed if either may have failed.\<close>
definition select :: "'a set \<Rightarrow> ('c, 's, 'a) nondet_monad" where
  "select A \<equiv> \<lambda>s. (A \<times> {mstate s}, False)"

definition alternative ::
  "('c, 's, 'a) nondet_monad \<Rightarrow> ('c, 's, 'a) nondet_monad \<Rightarrow> ('c, 's, 'a) nondet_monad" (infixl "\<sqinter>" 20)
  where
  "f \<sqinter> g \<equiv> \<lambda>s. (fst (f s) \<union> fst (g s), snd (f s) \<or> snd (g s))"

text \<open>
  A variant of @{text select} that takes a pair. The first component is a set
  as in normal @{text select}, the second component indicates whether the
  execution failed. This is useful to lift monads between different state
  spaces.\<close>
definition select_f :: "'a set \<times> bool  \<Rightarrow> ('c, 's, 'a) nondet_monad" where
  "select_f S \<equiv> \<lambda>s. (fst S \<times> {mstate s}, snd S)"

text \<open>
  @{text state_select} takes a relationship between states, and outputs
  nondeterministically a state related to the input state. Fails if no such
  state exists.\<close>
definition state_select ::
  "(('c,'s) monad_state \<times> ('c,'s) monad_state) set \<Rightarrow> ('c, 's, unit) nondet_monad" where
  "state_select r \<equiv> \<lambda>s. ((\<lambda>x. ((), mstate x)) ` {s'. (s, s') \<in> r}, \<not> (\<exists>s'. (s, s') \<in> r))"

subsection "Failure"

text \<open>
  The monad function that always fails. Returns an empty set of results and sets the failure flag.\<close>
definition fail :: "('c, 's, 'a) nondet_monad" where
  "fail \<equiv> \<lambda>s. ({}, True)"

text \<open>Assertions: fail if the property @{text P} is not true\<close>
definition assert :: "bool \<Rightarrow> ('c, 's, unit) nondet_monad" where
  "assert P \<equiv> if P then return () else fail"

text \<open>Fail if the value is @{const None}, return result @{text v} for @{term "Some v"}\<close>
definition assert_opt :: "'a option \<Rightarrow> ('c, 's, 'a) nondet_monad" where
  "assert_opt v \<equiv> case v of None \<Rightarrow> fail | Some v \<Rightarrow> return v"

text \<open>An assertion that also can introspect the current state.\<close>
definition state_assert :: "('c,'s) mpred \<Rightarrow> ('c, 's, unit) nondet_monad" where
  "state_assert P \<equiv> get >>= (\<lambda>s. assert (P s))"

subsection "Generic functions on top of the state monad"

text \<open>Apply a function to the current state and return the result without changing the state.\<close>
definition gets :: "(('c,'s) monad_state \<Rightarrow> 'a) \<Rightarrow> ('c, 's, 'a) nondet_monad" where
  "gets f \<equiv> get >>= (\<lambda>s. return (f s))"

text \<open>Apply a function to the constant state and return the result without changing the state.\<close>
definition asks :: "('c \<Rightarrow> 'a) \<Rightarrow> ('c, 's, 'a) nondet_monad" where
  "asks f \<equiv> ask >>= (\<lambda>s. return (f s))"

text \<open>Modify the current state using the function passed in.\<close>
definition modify ::
  "(('c, 's) monad_state \<Rightarrow> ('c, 's) monad_state) \<Rightarrow> ('c, 's, unit) nondet_monad"
  where
  "modify f \<equiv> get >>= (\<lambda>s. put (f s))"

lemma simpler_gets_def:
  "gets f = (\<lambda>s. ({(f s, mstate s)}, False))"
  by (simp add: gets_def return_def bind_def get_def)

lemma simpler_modify_def:
  "modify f = (\<lambda>s. ({((), mstate (f s))}, False))"
  by (simp add: modify_def bind_def get_def put_def)

text \<open>Execute the given monad when the condition is true, return @{text "()"} otherwise.\<close>
definition "when" :: "bool \<Rightarrow> ('c, 's, unit) nondet_monad \<Rightarrow> ('c, 's, unit) nondet_monad" where
  "when P m \<equiv> if P then m else return ()"

text \<open>Execute the given monad unless the condition is true, return @{text "()"} otherwise.\<close>
definition unless :: "bool \<Rightarrow> ('c, 's, unit) nondet_monad \<Rightarrow> ('c, 's, unit) nondet_monad" where
  "unless P m \<equiv> when (\<not>P) m"

text \<open>
  Perform a test on the current state, performing the left monad if
  the result is true or the right monad if the result is false. \<close>
definition condition ::
  "('c,'s) mpred \<Rightarrow> ('c, 's, 'r) nondet_monad \<Rightarrow> ('c, 's, 'r) nondet_monad \<Rightarrow> ('c, 's, 'r) nondet_monad"
  where
  "condition P L R \<equiv> \<lambda>s. if P s then L s else R s"

notation (output)
  condition  ("(condition (_)//  (_)//  (_))" [1000,1000,1000] 1000)

text \<open>
  Apply an option valued function to the current state, fail if it returns @{const None},
  return @{text v} if it returns @{term "Some v"}.\<close>
definition gets_the :: "(('c,'s) monad_state \<Rightarrow> 'a option) \<Rightarrow> ('c, 's, 'a) nondet_monad" where
  "gets_the f \<equiv> gets f >>= assert_opt"

text \<open>
  Get a map (such as a heap) from the current state and apply an argument to the map.
  Fail if the map returns @{const None}, otherwise return the value.\<close>
definition gets_map ::
  "(('c,'s) monad_state \<Rightarrow> 'a \<Rightarrow> 'b option) \<Rightarrow> 'a \<Rightarrow> ('c, 's, 'b) nondet_monad"
  where
  "gets_map f p \<equiv> gets f >>= (\<lambda>m. assert_opt (m p))"


subsection \<open>The Monad Laws\<close>

text \<open>An alternative definition of @{term bind}, sometimes more convenient.\<close>
lemma bind_def':
  "(f >>= g) \<equiv>
       \<lambda>s. ({(r'', s''). \<exists>(r', s') \<in> fst (f s). (r'', s'') \<in> fst (g r' (with_env_of s s')) },
                     snd (f s) \<or> (\<exists>(r', s') \<in> fst (f s). snd (g r' (with_env_of s s'))))"
  by (rule eq_reflection)
     (auto simp add: bind_def split_def Let_def)

lemma with_env_of_mstate[simp]:
  "with_env_of s (mstate s) = s"
  by (cases s, auto)

text \<open>Each monad satisfies at least the following three laws.\<close>

text \<open>@{term return} is absorbed at the left of a @{term bind}, applying the return value directly:\<close>
lemma return_bind[simp]:
  "(return x >>= f) = f x"
  by (simp add: return_def bind_def)

text \<open>@{term return} is absorbed on the right of a @{term bind}\<close>
lemma bind_return[simp]:
  "(m >>= return) = m"
  by (simp add: bind_def return_def split_def)

text \<open>@{term bind} is associative\<close>
lemma bind_assoc:
  fixes m :: "('c, 's, 'a) nondet_monad"
  fixes f :: "'a \<Rightarrow> ('c, 's, 'b) nondet_monad"
  fixes g :: "'b \<Rightarrow> ('c, 's, 'd) nondet_monad"
  shows "(m >>= f) >>= g  =  m >>= (\<lambda>x. f x >>= g)"
  unfolding bind_def Let_def split_def
  by (auto intro: rev_image_eqI)


section \<open>Adding Exceptions\<close>

text \<open>
  The type @{typ "('c,'s,'a) nondet_monad"} gives us nondeterminism and
  failure. We now extend this monad with exceptional return values
  that abort normal execution, but can be handled explicitly.
  We use the sum type to indicate exceptions.

  In @{typ "('c, 's, 'e + 'a) nondet_monad"}, @{typ "'s"} is the state,
  @{typ 'e} is an exception, and @{typ 'a} is a normal return value.

  This new type itself forms a monad again. Since type classes in
  Isabelle are not powerful enough to express the class of monads,
  we provide new names for the @{term return} and @{term bind} functions
  in this monad. We call them @{text returnOk} (for normal return values)
  and @{text bindE} (for composition). We also define @{text throwError}
  to return an exceptional value.\<close>
definition returnOk :: "'a \<Rightarrow> ('c, 's, 'e + 'a) nondet_monad" where
  "returnOk \<equiv> return o Inr"

definition throwError :: "'e \<Rightarrow> ('c, 's, 'e + 'a) nondet_monad" where
  "throwError \<equiv> return o Inl"

text \<open>
  Lifting a function over the exception type: if the input is an
  exception, return that exception; otherwise continue execution.\<close>
definition lift :: "('a \<Rightarrow> ('c, 's, 'e + 'b) nondet_monad) \<Rightarrow> 'e +'a \<Rightarrow> ('c, 's, 'e + 'b) nondet_monad" where
  "lift f v \<equiv> case v of Inl e \<Rightarrow> throwError e | Inr v' \<Rightarrow> f v'"

text \<open>
  The definition of @{term bind} in the exception monad (new
  name @{text bindE}): the same as normal @{term bind}, but
  the right-hand side is skipped if the left-hand side
  produced an exception.\<close>
definition bindE ::
  "('c, 's, 'e + 'a) nondet_monad \<Rightarrow> ('a \<Rightarrow> ('c, 's, 'e + 'b) nondet_monad) \<Rightarrow> ('c, 's, 'e + 'b) nondet_monad"
  (infixl ">>=E" 60) where
  "f >>=E g \<equiv> f >>= lift g"

text \<open>
  Lifting a normal nondeterministic monad into the
  exception monad is achieved by always returning its
  result as normal result and never throwing an exception.\<close>
definition liftE :: "('c,'s,'a) nondet_monad \<Rightarrow> ('c, 's, 'e+'a) nondet_monad" where
  "liftE f \<equiv> f >>= (\<lambda>r. return (Inr r))"

text \<open>
  Since the underlying type and @{text return} function changed,
  we need new definitions for when and unless:\<close>
definition whenE :: "bool \<Rightarrow> ('c, 's, 'e + unit) nondet_monad \<Rightarrow> ('c, 's, 'e + unit) nondet_monad" where
  "whenE P f \<equiv> if P then f else returnOk ()"

definition unlessE :: "bool \<Rightarrow> ('c, 's, 'e + unit) nondet_monad \<Rightarrow> ('c, 's, 'e + unit) nondet_monad" where
  "unlessE P f \<equiv> if P then returnOk () else f"

text \<open>
  Throwing an exception when the parameter is @{term None}, otherwise
  returning @{term "v"} for @{term "Some v"}.\<close>
definition throw_opt :: "'e \<Rightarrow> 'a option \<Rightarrow> ('c, 's, 'e + 'a) nondet_monad" where
  "throw_opt ex x \<equiv> case x of None \<Rightarrow> throwError ex | Some v \<Rightarrow> returnOk v"

text \<open>
  Failure in the exception monad is redefined in the same way
  as @{const whenE} and @{const unlessE}, with @{term returnOk}
  instead of @{term return}.\<close>
definition assertE :: "bool \<Rightarrow> ('c, 's, 'e + unit) nondet_monad" where
  "assertE P \<equiv> if P then returnOk () else fail"


subsection "Monad Laws for the Exception Monad"

text \<open>More direct definition of @{const liftE}:\<close>
lemma liftE_def2:
  "liftE f = (\<lambda>s. ((\<lambda>(v,s'). (Inr v, s')) ` fst (f s), snd (f s)))"
  by (auto simp: liftE_def return_def split_def bind_def)

text \<open>Left @{const returnOk} absorbtion over @{term bindE}:\<close>
lemma returnOk_bindE[simp]: "(returnOk x >>=E f) = f x"
  unfolding bindE_def returnOk_def
  by (clarsimp simp: lift_def)

lemma lift_return[simp]:
  "lift (return \<circ> Inr) = return"
  by (auto simp: lift_def throwError_def split: sum.splits)

text \<open>Right @{const returnOk} absorbtion over @{term bindE}:\<close>
lemma bindE_returnOk[simp]:
  "(m >>=E returnOk) = m"
  by (simp add: bindE_def returnOk_def)

text \<open>Associativity of @{const bindE}:\<close>
lemma bindE_assoc:
  "(m >>=E f) >>=E g = m >>=E (\<lambda>x. f x >>=E g)"
  unfolding bindE_def
  by (fastforce simp: bind_assoc lift_def throwError_def
                split: sum.splits
                intro: arg_cong[where f="\<lambda>x. m >>= x"])

text \<open>@{const returnOk} could also be defined via @{const liftE}:\<close>
lemma returnOk_liftE:
  "returnOk x = liftE (return x)"
  by (simp add: liftE_def returnOk_def)

text \<open>Execution after throwing an exception is skipped:\<close>
lemma throwError_bindE[simp]:
  "(throwError E >>=E f) = throwError E"
  by (simp add: bindE_def bind_def throwError_def lift_def return_def)


section "Syntax"

text \<open>This section defines traditional Haskell-like do-syntax
  for the state monad in Isabelle.\<close>

subsection "Syntax for the Nondeterministic State Monad"

text \<open>
  We use @{text K_bind} to syntactically indicate the case where the return argument
  of the left side of a @{term bind} is ignored\<close>
definition K_bind :: "'a \<Rightarrow> 'b \<Rightarrow> 'a" where
  K_bind_def[iff]: "K_bind \<equiv> \<lambda>x y. x"

nonterminal
  dobinds and dobind and nobind

syntax
  "_dobind"    :: "[pttrn, 'a] => dobind"             ("(_ <-/ _)" 10)
  ""           :: "dobind => dobinds"                 ("_")
  "_nobind"    :: "'a => dobind"                      ("_")
  "_dobinds"   :: "[dobind, dobinds] => dobinds"      ("(_);//(_)")

  "_do"        :: "[dobinds, 'a] => 'a"               ("(do ((_);//(_))//od)" 100)
syntax (xsymbols)
  "_dobind"    :: "[pttrn, 'a] => dobind"             ("(_ \<leftarrow>/ _)" 10)

translations
  "_do (_dobinds b bs) e"  == "_do b (_do bs e)"
  "_do (_nobind b) e"      == "b >>= (CONST K_bind e)"
  "do x <- a; e od"        == "a >>= (\<lambda>x. e)"

text \<open>Syntax examples:\<close>
lemma "do x \<leftarrow> return 1;
          return (2::nat);
          return x
       od =
       return 1 >>=
       (\<lambda>x. return (2::nat) >>=
            K_bind (return x))"
  by (rule refl)

lemma "do x \<leftarrow> return 1;
          return 2;
          return x
       od = return 1"
  by simp

subsection "Syntax for the Exception Monad"

text \<open>
  Since the exception monad is a different type, we need to distinguish it in the syntax
  if we want to avoid ambiguous terms. We use @{text doE}/@{text odE} for this, but can
  re-use most of the productions from @{text do}/@{text od} above. \<close>
syntax
  "_doE" :: "[dobinds, 'a] => 'a"  ("(doE ((_);//(_))//odE)" 100)

translations
  "_doE (_dobinds b bs) e"  == "_doE b (_doE bs e)"
  "_doE (_nobind b) e"      == "b >>=E (CONST K_bind e)"
  "doE x <- a; e odE"       == "a >>=E (\<lambda>x. e)"

text \<open>Syntax examples:\<close>
lemma "doE x \<leftarrow> returnOk 1;
           returnOk (2::nat);
           returnOk x
       odE =
       returnOk 1 >>=E
       (\<lambda>x. returnOk (2::nat) >>=E
            K_bind (returnOk x))"
  by (rule refl)

lemma "doE x \<leftarrow> returnOk 1;
           returnOk 2;
           returnOk x
       odE = returnOk 1"
  by simp


section "Library of additional Monadic Functions and Combinators"

text \<open>Lifting a normal function into the monad type:\<close>
definition liftM :: "('a \<Rightarrow> 'b) \<Rightarrow> ('c, 's, 'a) nondet_monad \<Rightarrow> ('c, 's, 'b) nondet_monad" where
  "liftM f m \<equiv> do x \<leftarrow> m; return (f x) od"

text \<open>The same for the exception monad:\<close>
definition liftME :: "('a \<Rightarrow> 'b) \<Rightarrow> ('c, 's, 'e+'a) nondet_monad \<Rightarrow> ('c, 's, 'e+'b) nondet_monad" where
  "liftME f m \<equiv> doE x \<leftarrow> m; returnOk (f x) odE"

text \<open>Execute @{term f} for @{term "Some x"}, otherwise do nothing.\<close>
definition maybeM :: "('a \<Rightarrow> ('c, 's, unit) nondet_monad) \<Rightarrow> 'a option \<Rightarrow> ('c, 's, unit) nondet_monad" where
  "maybeM f y \<equiv> case y of Some x \<Rightarrow> f x | None \<Rightarrow> return ()"

text \<open>Run a sequence of monads from left to right, ignoring return values.\<close>
definition sequence_x :: "('c, 's, 'a) nondet_monad list \<Rightarrow> ('c, 's, unit) nondet_monad" where
  "sequence_x xs \<equiv> foldr (\<lambda>x y. x >>= (\<lambda>_. y)) xs (return ())"

text \<open>
  Map a monadic function over a list by applying it to each element
  of the list from left to right, ignoring return values.\<close>
definition mapM_x :: "('a \<Rightarrow> ('c, 's, 'b) nondet_monad) \<Rightarrow> 'a list \<Rightarrow> ('c, 's, unit) nondet_monad" where
  "mapM_x f xs \<equiv> sequence_x (map f xs)"

text \<open>
  Map a monadic function with two parameters over two lists,
  going through both lists simultaneously, left to right, ignoring
  return values.\<close>
definition zipWithM_x ::
  "('a \<Rightarrow> 'b \<Rightarrow> ('r,'s,'c) nondet_monad) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> ('r, 's, unit) nondet_monad"
  where
  "zipWithM_x f xs ys \<equiv> sequence_x (zipWith f xs ys)"

text \<open>
  The same three functions as above, but returning a list of
  return values instead of @{text unit}\<close>
definition sequence :: "('c, 's, 'a) nondet_monad list \<Rightarrow> ('c, 's, 'a list) nondet_monad" where
  "sequence xs \<equiv> let mcons = (\<lambda>p q. p >>= (\<lambda>x. q >>= (\<lambda>y. return (x#y))))
                 in foldr mcons xs (return [])"

definition mapM :: "('a \<Rightarrow> ('c, 's,'b) nondet_monad) \<Rightarrow> 'a list \<Rightarrow> ('c, 's, 'b list) nondet_monad" where
  "mapM f xs \<equiv> sequence (map f xs)"

definition zipWithM ::
  "('a \<Rightarrow> 'b \<Rightarrow> ('r,'s,'c) nondet_monad) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> ('r, 's, 'c list) nondet_monad"
  where
  "zipWithM f xs ys \<equiv> sequence (zipWith f xs ys)"

definition foldM ::
  "('b \<Rightarrow> 'a \<Rightarrow> ('r, 's, 'a) nondet_monad) \<Rightarrow> 'b list \<Rightarrow> 'a \<Rightarrow> ('r, 's, 'a) nondet_monad"
  where
  "foldM m xs a \<equiv> foldr (\<lambda>p q. q >>= m p) xs (return a) "

definition foldME ::
  "('b \<Rightarrow> 'a \<Rightarrow> ('c, 's, ('e + 'b)) nondet_monad) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> ('c, 's, ('e + 'b)) nondet_monad"
  where
  "foldME m a xs \<equiv> foldr (\<lambda>p q. q >>=E swp m p) xs (returnOk a)"

text \<open>
  The sequence and map functions above for the exception monad, with and without
  lists of return value\<close>
definition sequenceE_x :: "('c, 's, 'e+'a) nondet_monad list \<Rightarrow> ('c, 's, 'e+unit) nondet_monad" where
  "sequenceE_x xs \<equiv> foldr (\<lambda>x y. doE _ <- x; y odE) xs (returnOk ())"

definition mapME_x :: "('a \<Rightarrow> ('c, 's,'e+'b) nondet_monad) \<Rightarrow> 'a list \<Rightarrow> ('c, 's,'e+unit) nondet_monad" where
  "mapME_x f xs \<equiv> sequenceE_x (map f xs)"

definition sequenceE :: "('c, 's, 'e+'a) nondet_monad list \<Rightarrow> ('c, 's, 'e+'a list) nondet_monad" where
  "sequenceE xs \<equiv> let mcons = (\<lambda>p q. p >>=E (\<lambda>x. q >>=E (\<lambda>y. returnOk (x#y))))
                   in foldr mcons xs (returnOk [])"

definition mapME ::
  "('a \<Rightarrow> ('c,'s,'e+'b) nondet_monad) \<Rightarrow> 'a list \<Rightarrow> ('c,'s,'e+'b list) nondet_monad"
  where
  "mapME f xs \<equiv> sequenceE (map f xs)"

text \<open>Filtering a list using a monadic function as predicate:\<close>
primrec filterM :: "('a \<Rightarrow> ('c,'s, bool) nondet_monad) \<Rightarrow> 'a list \<Rightarrow> ('c, 's, 'a list) nondet_monad" where
  "filterM P []       = return []"
| "filterM P (x # xs) = do
     b  <- P x;
     ys <- filterM P xs;
     return (if b then (x # ys) else ys)
   od"

text \<open>An alternative definition of @{term state_select}\<close>
lemma state_select_def2:
  "state_select r \<equiv> (do
    s \<leftarrow> get;
    S \<leftarrow> return {s'. (s, s') \<in> r};
    assert (S \<noteq> {});
    s' \<leftarrow> select S;
    put s'
  od)"
  apply (clarsimp simp add: state_select_def get_def return_def assert_def fail_def select_def
                            put_def bind_def fun_eq_iff
                    intro!: eq_reflection)
  apply fastforce
  done


section "Catching and Handling Exceptions"

text \<open>
  Turning an exception monad into a normal state monad
  by catching and handling any potential exceptions:\<close>
definition catch ::
  "('c, 's, 'e + 'a) nondet_monad \<Rightarrow> ('e \<Rightarrow> ('c, 's, 'a) nondet_monad) \<Rightarrow> ('c, 's, 'a) nondet_monad"
  (infix "<catch>" 10) where
  "f <catch> handler \<equiv>
     do x \<leftarrow> f;
        case x of
          Inr b \<Rightarrow> return b
        | Inl e \<Rightarrow> handler e
     od"

text \<open>
  Handling exceptions, but staying in the exception monad.
  The handler may throw a type of exceptions different from
  the left side.\<close>
definition handleE' ::
  "('c, 's, 'e1 + 'a) nondet_monad \<Rightarrow> ('e1 \<Rightarrow> ('c, 's, 'e2 + 'a) nondet_monad) \<Rightarrow> ('c, 's, 'e2 + 'a) nondet_monad"
  (infix "<handle2>" 10) where
  "f <handle2> handler \<equiv>
   do
      v \<leftarrow> f;
      case v of
        Inl e \<Rightarrow> handler e
      | Inr v' \<Rightarrow> return (Inr v')
   od"

text \<open>
  A type restriction of the above that is used more commonly in
  practice: the exception handler (potentially) throws an exception
  of the same type as the left-hand side.\<close>
definition handleE ::
  "('c, 's, 'x + 'a) nondet_monad \<Rightarrow> ('x \<Rightarrow> ('c, 's, 'x + 'a) nondet_monad) \<Rightarrow> ('c, 's, 'x + 'a) nondet_monad"
  (infix "<handle>" 10) where
  "handleE \<equiv> handleE'"

text \<open>
  Handling exceptions, and additionally providing a continuation
  if the left-hand side throws no exception:\<close>
definition handle_elseE ::
  "('c, 's, 'e + 'a) nondet_monad \<Rightarrow> ('e \<Rightarrow> ('c, 's, 'ee + 'b) nondet_monad) \<Rightarrow>
   ('a \<Rightarrow> ('c, 's, 'ee + 'b) nondet_monad) \<Rightarrow> ('c, 's, 'ee + 'b) nondet_monad" ("_ <handle> _ <else> _" 10)
  where
  "f <handle> handler <else> continue \<equiv>
   do v \<leftarrow> f;
      case v of Inl e  \<Rightarrow> handler e
              | Inr v' \<Rightarrow> continue v'
   od"

subsection "Loops"

text \<open>
  Loops are handled using the following inductive predicate;
  non-termination is represented using the failure flag of the
  monad.\<close>
inductive_set whileLoop_results ::
  "('r \<Rightarrow> ('c,'s) mpred) \<Rightarrow> ('r \<Rightarrow> ('c, 's, 'r) nondet_monad) \<Rightarrow> 'c \<Rightarrow>
   ((('r \<times> 's) option) \<times> (('r \<times> 's) option)) set"
  for C B c where
    "\<lbrakk> \<not> C r (monad_state c s) \<rbrakk> \<Longrightarrow> (Some (r, s), Some (r, s)) \<in> whileLoop_results C B c"
  | "\<lbrakk> C  r (monad_state c s); snd (B r (monad_state c s)) \<rbrakk>
     \<Longrightarrow> (Some (r, s), None) \<in> whileLoop_results C B c"
  | "\<lbrakk> C r (monad_state c s); (r', s') \<in> fst (B r (monad_state c s));
       (Some (r', s'), z) \<in> whileLoop_results C B c \<rbrakk>
     \<Longrightarrow> (Some (r, s), z) \<in> whileLoop_results C B c"

inductive_cases whileLoop_results_cases_valid: "(Some x, Some y) \<in> whileLoop_results C B c"
inductive_cases whileLoop_results_cases_fail: "(Some x, None) \<in> whileLoop_results C B c"
inductive_simps whileLoop_results_simps: "(Some x, y) \<in> whileLoop_results C B c"
inductive_simps whileLoop_results_simps_valid: "(Some x, Some y) \<in> whileLoop_results C B c"
inductive_simps whileLoop_results_simps_start_fail[simp]: "(None, x) \<in> whileLoop_results C B c"

inductive whileLoop_terminates ::
  "('r \<Rightarrow> ('c,'s) mpred) \<Rightarrow> ('r \<Rightarrow> ('c, 's, 'r) nondet_monad) \<Rightarrow> 'c \<Rightarrow> 'r \<Rightarrow> 's \<Rightarrow> bool"
  for C B c where
    "\<not> C r (monad_state c s) \<Longrightarrow> whileLoop_terminates C B c r s"
  | "\<lbrakk> C r (monad_state c s);
       \<forall>(r', s') \<in> fst (B r (monad_state c s)). whileLoop_terminates C B c r' s' \<rbrakk>
     \<Longrightarrow> whileLoop_terminates C B c r s"

inductive_cases whileLoop_terminates_cases: "whileLoop_terminates C B c r s"
inductive_simps whileLoop_terminates_simps: "whileLoop_terminates C B c r s"

definition whileLoop ::
  "('a \<Rightarrow> ('c,'s) mpred) \<Rightarrow> ('a \<Rightarrow> ('c, 's, 'a) nondet_monad) \<Rightarrow> 'a \<Rightarrow> ('c, 's, 'a) nondet_monad"
  where
  "whileLoop C B \<equiv> \<lambda>r s.
     ({(r',s'). (Some (r, mstate s), Some (r', s')) \<in> whileLoop_results C B (env s)},
      (Some (r, mstate s), None) \<in> whileLoop_results C B (env s) \<or>
      \<not>whileLoop_terminates C B (env s) r (mstate s))"

notation (output)
  whileLoop  ("(whileLoop (_)//  (_))" [1000, 1000] 1000)

definition whileLoopE ::
  "('r \<Rightarrow> ('c,'s) mpred) \<Rightarrow> ('r \<Rightarrow> ('c, 's, 'e + 'r) nondet_monad) \<Rightarrow>
   'r \<Rightarrow> ('c, 's, 'e + 'r) nondet_monad"
  where
  "whileLoopE C body \<equiv>
     \<lambda>r. whileLoop (\<lambda>r s. (case r of Inr v \<Rightarrow> C v s | _ \<Rightarrow> False)) (lift body) (Inr r)"

notation (output)
  whileLoopE  ("(whileLoopE (_)//  (_))" [1000, 1000] 1000)


section "Combinators that have conditions with side effects"

definition notM :: "('c, 's, bool) nondet_monad \<Rightarrow> ('c, 's, bool) nondet_monad" where
  "notM m = do c \<leftarrow> m; return (\<not> c) od"

definition whileM ::
  "('c, 's, bool) nondet_monad \<Rightarrow> ('c, 's, 'a) nondet_monad \<Rightarrow> ('c, 's, unit) nondet_monad"
  where
  "whileM C B \<equiv> do
    c \<leftarrow> C;
    whileLoop (\<lambda>c s. c) (\<lambda>_. do B; C od) c;
    return ()
  od"

definition ifM ::
  "('c, 's, bool) nondet_monad \<Rightarrow> ('c, 's, 'a) nondet_monad \<Rightarrow> ('c, 's, 'a) nondet_monad \<Rightarrow> ('c, 's, 'a) nondet_monad"
  where
  "ifM test t f = do
    c \<leftarrow> test;
    if c then t else f
   od"

definition ifME ::
  "('c, 's, 'a + bool) nondet_monad \<Rightarrow> ('c, 's, 'a + 'b) nondet_monad \<Rightarrow> ('c, 's, 'a + 'b) nondet_monad
   \<Rightarrow> ('c, 's, 'a + 'b) nondet_monad"
  where
  "ifME test t f = doE
    c \<leftarrow> test;
    if c then t else f
   odE"

definition whenM ::
  "('c, 's, bool) nondet_monad \<Rightarrow> ('c, 's, unit) nondet_monad \<Rightarrow> ('c, 's, unit) nondet_monad"
  where
  "whenM t m = ifM t m (return ())"

definition orM ::
  "('c, 's, bool) nondet_monad \<Rightarrow> ('c, 's, bool) nondet_monad \<Rightarrow> ('c, 's, bool) nondet_monad"
  where
  "orM a b = ifM a (return True) b"

definition andM ::
  "('c, 's, bool) nondet_monad \<Rightarrow> ('c, 's, bool) nondet_monad \<Rightarrow> ('c, 's, bool) nondet_monad"
  where
  "andM a b = ifM a b (return False)"

end
