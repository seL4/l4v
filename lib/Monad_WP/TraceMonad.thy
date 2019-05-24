(*
 * Copyright 2017, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)
theory TraceMonad
imports
  "../Lib"
  "Strengthen"
begin

text \<open>
The ``Interference Trace Monad''. This nondeterministic monad
records the state at every interference point, permitting
nondeterministic interference by the environment at interference
points.

The trace set initially includes all possible environment behaviours.
Trace steps are tagged as environment or self actions, and can then
be constrained to a smaller set where the environment acts according
to a rely constraint (i.e. rely-guarantee reasoning), or to set the
environment actions to be the self actions of another program (parallel
composition).
\<close>

section "The Trace Monad"

text \<open>Trace monad identifier. Me corresponds to the current thread running and Env to the environment.\<close>
datatype tmid = Me | Env

text \<open>Results associated with traces. Traces may correspond to incomplete, failed, or completed executions.\<close>
datatype ('s, 'a) tmres = Failed | Incomplete | Result "('a \<times> 's)"

abbreviation
  map_tmres_rv :: "('a \<Rightarrow> 'b) \<Rightarrow> ('s, 'a) tmres \<Rightarrow> ('s, 'b) tmres"
where
  "map_tmres_rv f \<equiv> map_tmres id f"

section "The Monad"

text \<open> tmonad returns a set of non-deterministic  computations, including
  a trace as a list of "thread identifier" \<times> state, and an optional
  pair result, state when the computation did not fail. \<close>
type_synonym ('s, 'a) tmonad = "'s \<Rightarrow> ((tmid \<times> 's) list \<times> ('s, 'a) tmres) set"

text \<open>Returns monad results, ignoring failures and traces.\<close>
definition
  mres :: "((tmid \<times> 's) list \<times> ('s, 'a) tmres) set \<Rightarrow> ('a \<times> 's) set"
where
  "mres r = Result -` (snd ` r)"

text \<open>
  The definition of fundamental monad functions @{text return} and
  @{text bind}. The monad function @{text "return x"} does not change
  the  state, does not fail, and returns @{text "x"}.
\<close>
definition
  return :: "'a \<Rightarrow> ('s,'a) tmonad"
where
  "return a \<equiv> \<lambda>s. ({([], Result (a, s))})"

text \<open>
  The monad function @{text "bind f g"}, also written @{text "f >>= g"},
  is the execution of @{term f} followed by the execution of @{text g}.
  The function @{text g} takes the result value \emph{and} the result
  state of @{text f} as parameter. The definition says that the result of
  the combined operation is the union of the set of sets that is created
  by @{text g} applied to the result sets of @{text f}. The combined
  operation may have failed, if @{text f} may have failed or @{text g} may
  have failed on any of the results of @{text f}.
\<close>

abbreviation (input)
  fst_upd :: "('a \<Rightarrow> 'c) \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'c \<times> 'b"
where
  "fst_upd f \<equiv> \<lambda>(a,b). (f a, b)"

abbreviation (input)
  snd_upd :: "('b \<Rightarrow> 'c) \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'c"
where
  "snd_upd f \<equiv> \<lambda>(a,b). (a, f b)"

definition
  bind :: "('s, 'a) tmonad \<Rightarrow> ('a \<Rightarrow> ('s, 'b) tmonad) \<Rightarrow>
           ('s, 'b) tmonad" (infixl ">>=" 60)
where
  "bind f g \<equiv> \<lambda>s. \<Union>(xs, r) \<in> (f s). case r of Failed \<Rightarrow> {(xs, Failed)}
    | Incomplete \<Rightarrow> {(xs, Incomplete)}
    | Result (rv, s) \<Rightarrow> fst_upd (\<lambda>ys. ys @ xs) ` g rv s"

text \<open>Sometimes it is convenient to write @{text bind} in reverse order.\<close>
abbreviation(input)
  bind_rev :: "('c \<Rightarrow> ('a, 'b) tmonad) \<Rightarrow> ('a, 'c) tmonad \<Rightarrow>
               ('a, 'b) tmonad" (infixl "=<<" 60)
where
  "g =<< f \<equiv> f >>= g"

text \<open>
  The basic accessor functions of the state monad. @{text get} returns
  the current state as result, does not fail, and does not change the state.
  @{text "put s"} returns nothing (@{typ unit}), changes the current state
  to @{text s} and does not fail.
\<close>
definition
  get :: "('s,'s) tmonad"
where
  "get \<equiv> \<lambda>s. {([], Result (s, s))}"

definition
  put :: "'s \<Rightarrow> ('s, unit) tmonad"
where
  "put s \<equiv> \<lambda>st. {([], Result ((), s))}"

definition
  put_trace_elem :: "(tmid \<times> 's) \<Rightarrow> ('s, unit) tmonad"
where
  "put_trace_elem x = (\<lambda>s. {([], Incomplete), ([x], Result ((), s))})"

primrec
  put_trace :: "(tmid \<times> 's) list \<Rightarrow> ('s, unit) tmonad"
where
    "put_trace [] = return ()"
  | "put_trace (x # xs) = (put_trace xs >>= (\<lambda>_. put_trace_elem x))"

subsection "Nondeterminism"

text \<open>
  Basic nondeterministic functions. @{text "select A"} chooses an element
  of the set @{text A}, does not change the state, and does not fail
  (even if the set is empty). @{text "f OR g"} executes @{text f} or
  executes @{text g}. It retuns the union of results of @{text f} and
  @{text g}, and may have failed if either may have failed.
\<close>
definition
  select :: "'a set \<Rightarrow> ('s, 'a) tmonad"
where
  (* Should we have Failed when A = {} ? *)
  "select A \<equiv> \<lambda>s. (Pair [] ` Result ` (A \<times> {s}))"

definition
  alternative :: "('s,'a) tmonad \<Rightarrow> ('s,'a) tmonad \<Rightarrow>
                  ('s,'a) tmonad"
  (infixl "OR" 20)
where
  "f OR g \<equiv> \<lambda>s. (f s \<union> g s)"

text \<open> Alternative notation for @{text OR} \<close>
notation (xsymbols)  alternative (infixl "\<sqinter>" 20)


text \<open> The @{text selet_f} function was left out here until we figure
  out what variant we actually need.
\<close>

subsection "Failure"

text \<open> The monad function that always fails. Returns an empty set of
results and sets the failure flag. \<close>
definition
  fail :: "('s, 'a) tmonad"
where
 "fail \<equiv> \<lambda>s. {([], Failed)}"

text \<open> Assertions: fail if the property @{text P} is not true \<close>
definition
  assert :: "bool \<Rightarrow> ('a, unit) tmonad"
where
 "assert P \<equiv> if P then return () else fail"

text \<open> Fail if the value is @{const None},
  return result @{text v} for @{term "Some v"} \<close>
definition
  assert_opt :: "'a option \<Rightarrow> ('b, 'a) tmonad"
where
 "assert_opt v \<equiv> case v of None \<Rightarrow> fail | Some v \<Rightarrow> return v"

text \<open> An assertion that also can introspect the current state. \<close>

definition
  state_assert :: "('s \<Rightarrow> bool) \<Rightarrow> ('s, unit) tmonad"
where
  "state_assert P \<equiv> get >>= (\<lambda>s. assert (P s))"

subsection "Generic functions on top of the state monad"

text \<open> Apply a function to the current state and return the result
without changing the state. \<close>
definition
  gets :: "('s \<Rightarrow> 'a) \<Rightarrow> ('s, 'a) tmonad"
where
 "gets f \<equiv> get >>= (\<lambda>s. return (f s))"

text \<open> Modify the current state using the function passed in. \<close>
definition
  modify :: "('s \<Rightarrow> 's) \<Rightarrow> ('s, unit) tmonad"
where
  "modify f \<equiv> get >>= (\<lambda>s. put (f s))"

lemma simpler_gets_def: "gets f = (\<lambda>s. {([], Result ((f s), s))})"
 by (simp add: fun_eq_iff gets_def return_def bind_def get_def split_def)

lemma simpler_modify_def:
  "modify f = (\<lambda>s. {([], Result ((),(f s)))})"
  by (simp add: fun_eq_iff modify_def bind_def get_def put_def split_def)

text \<open> Execute the given monad when the condition is true,
  return @{text "()"} otherwise. \<close>
definition
  "when" :: "bool \<Rightarrow> ('s, unit) tmonad \<Rightarrow>
           ('s, unit) tmonad"
where
  "when P m \<equiv> if P then m else return ()"

text \<open> Execute the given monad unless the condition is true,
  return @{text "()"} otherwise. \<close>
definition
  unless :: "bool \<Rightarrow> ('s, unit) tmonad \<Rightarrow>
            ('s, unit) tmonad"
where
  "unless P m \<equiv> when (\<not>P) m"

text \<open>
  Perform a test on the current state, performing the left monad if
  the result is true or the right monad if the result is false.
\<close>
definition
  condition :: "('s \<Rightarrow> bool) \<Rightarrow> ('s, 'r) tmonad \<Rightarrow> ('s, 'r) tmonad \<Rightarrow> ('s, 'r) tmonad"
where
  "condition P L R \<equiv> \<lambda>s. if (P s) then (L s) else (R s)"

notation (output)
  condition  ("(condition (_)//  (_)//  (_))" [1000,1000,1000] 1000)

text \<open>
Apply an option valued function to the current state, fail
if it returns @{const None}, return @{text v} if it returns
@{term "Some v"}.
\<close>
definition
  gets_the :: "('s \<Rightarrow> 'a option) \<Rightarrow> ('s, 'a) tmonad"
where
  "gets_the f \<equiv> gets f >>= assert_opt"


subsection \<open> The Monad Laws \<close>

text \<open>An alternative definition of bind, sometimes more convenient.\<close>
lemma bind_def2:
  "bind f g \<equiv> (\<lambda>s. ((\<lambda>xs. (xs, Failed)) ` {xs. (xs, Failed) \<in> f s})
    \<union> ((\<lambda>xs. (xs, Incomplete)) ` {xs. (xs, Incomplete) \<in> f s})
    \<union> (\<Union>(xs, rv, s) \<in> {(xs, rv, s'). (xs, Result (rv, s')) \<in> f s}. fst_upd (\<lambda>ys. ys @ xs) ` g rv s))"
  apply (clarsimp simp add: bind_def fun_eq_iff
                            Un_Union_image split_def
                    intro!: eq_reflection)
  apply (auto split: tmres.splits elim!:rev_bexI[where A="f x" for x])
  apply (fastforce intro: image_eqI[rotated])
  done

lemma elem_bindE:
  "(tr, res) \<in> bind f (\<lambda>x. g x) s
    \<Longrightarrow> ((res = Incomplete | res = Failed) \<Longrightarrow> (tr, map_tmres undefined undefined res) \<in> f s \<Longrightarrow> P)
    \<Longrightarrow> (\<And>tr' tr'' x s'. (tr', Result (x, s')) \<in> f s \<Longrightarrow> (tr'', res) \<in> g x s'
        \<Longrightarrow> tr = tr'' @ tr' \<Longrightarrow> P)
    \<Longrightarrow> P"
  by (auto simp: bind_def2)

text \<open> Each monad satisfies at least the following three laws. \<close>

text \<open> @{term return} is absorbed at the left of a @{term bind},
  applying the return value directly: \<close>

declare map_option.identity[simp]

lemma return_bind [simp]: "(return x >>= f) = f x"
  by (auto simp add: return_def bind_def split_def split:if_splits)

text \<open> @{term return} is absorbed on the right of a @{term bind} \<close>
lemma bind_return [simp]: "(m >>= return) = m"
  by (auto simp add: fun_eq_iff bind_def return_def
           split: tmres.splits)

text \<open> @{term bind} is associative \<close>
lemma bind_assoc:
  fixes m :: "('a,'b) tmonad"
  fixes f :: "'b \<Rightarrow> ('a,'c) tmonad"
  fixes g :: "'c \<Rightarrow> ('a,'d) tmonad"
  shows "(m >>= f) >>= g  =  m >>= (\<lambda>x. f x >>= g)"
  apply (unfold bind_def Let_def split_def)
  apply (rule ext)
  apply clarsimp
  apply (rule SUP_cong[OF refl], clarsimp)
  apply (split tmres.split; intro conjI impI; clarsimp)
  apply (simp add: image_Union)
  apply (rule SUP_cong[OF refl], clarsimp)
  apply (split tmres.split; intro conjI impI; clarsimp)
  apply (simp add: image_image)
  done

section \<open> Adding Exceptions \<close>

text \<open>
  The type @{typ "('s,'a) tmonad"} gives us nondeterminism and
  failure. We now extend this monad with exceptional return values
  that abort normal execution, but can be handled explicitly.
  We use the sum type to indicate exceptions.

  In @{typ "('s, 'e + 'a) tmonad"}, @{typ "'s"} is the state,
  @{typ 'e} is an exception, and @{typ 'a} is a normal return value.

  This new type itself forms a monad again. Since type classes in
  Isabelle are not powerful enough to express the class of monads,
  we provide new names for the @{term return} and @{term bind} functions
  in this monad. We call them @{text returnOk} (for normal return values)
  and @{text bindE} (for composition). We also define @{text throwError}
  to return an exceptional value.
\<close>
definition
  returnOk :: "'a \<Rightarrow> ('s, 'e + 'a) tmonad"
where
  "returnOk \<equiv> return o Inr"

definition
  throwError :: "'e \<Rightarrow> ('s, 'e + 'a) tmonad"
where
  "throwError \<equiv> return o Inl"

text \<open>
  Lifting a function over the exception type: if the input is an
  exception, return that exception; otherwise continue execution.
\<close>
definition
  lift :: "('a \<Rightarrow> ('s, 'e + 'b) tmonad) \<Rightarrow>
           'e +'a \<Rightarrow> ('s, 'e + 'b) tmonad"
where
  "lift f v \<equiv> case v of Inl e \<Rightarrow> throwError e
                      | Inr v' \<Rightarrow> f v'"

text \<open>
  The definition of @{term bind} in the exception monad (new
  name @{text bindE}): the same as normal @{term bind}, but
  the right-hand side is skipped if the left-hand side
  produced an exception.
\<close>
definition
  bindE :: "('s, 'e + 'a) tmonad \<Rightarrow>
            ('a \<Rightarrow> ('s, 'e + 'b) tmonad) \<Rightarrow>
            ('s, 'e + 'b) tmonad"  (infixl ">>=E" 60)
where
  "bindE f g \<equiv> bind f (lift g)"


text \<open>
  Lifting a normal nondeterministic monad into the
  exception monad is achieved by always returning its
  result as normal result and never throwing an exception.
\<close>
definition
  liftE :: "('s,'a) tmonad \<Rightarrow> ('s, 'e+'a) tmonad"
where
  "liftE f \<equiv> f >>= (\<lambda>r. return (Inr r))"


text \<open>
  Since the underlying type and @{text return} function changed,
  we need new definitions for when and unless:
\<close>
definition
  whenE :: "bool \<Rightarrow> ('s, 'e + unit) tmonad \<Rightarrow>
            ('s, 'e + unit) tmonad"
where
  "whenE P f \<equiv> if P then f else returnOk ()"

definition
  unlessE :: "bool \<Rightarrow> ('s, 'e + unit) tmonad \<Rightarrow>
            ('s, 'e + unit) tmonad"
where
  "unlessE P f \<equiv> if P then returnOk () else f"


text \<open>
  Throwing an exception when the parameter is @{term None}, otherwise
  returning @{term "v"} for @{term "Some v"}.
\<close>
definition
  throw_opt :: "'e \<Rightarrow> 'a option \<Rightarrow> ('s, 'e + 'a) tmonad"
where
  "throw_opt ex x \<equiv>
    case x of None \<Rightarrow> throwError ex | Some v \<Rightarrow> returnOk v"


text \<open>
  Failure in the exception monad is redefined in the same way
  as @{const whenE} and @{const unlessE}, with @{term returnOk}
  instead of @{term return}.
\<close>
definition
  assertE :: "bool \<Rightarrow> ('a, 'e + unit) tmonad"
where
  "assertE P \<equiv> if P then returnOk () else fail"

subsection "Monad Laws for the Exception Monad"

text \<open> More direct definition of @{const liftE}: \<close>
lemma liftE_def2:
  "liftE f = (\<lambda>s. snd_upd (map_tmres_rv Inr) ` (f s))"
  apply (clarsimp simp: fun_eq_iff liftE_def return_def split_def bind_def image_def)
  apply (rule set_eqI)
  apply (rule iffI)
  apply clarsimp
   apply (erule rev_bexI[where A="f s" for s])
   apply (clarsimp split: tmres.splits)
  apply clarsimp
  apply (rule exI)
  apply (rule conjI)
   apply (erule rev_bexI[where A="f s" for s])
   apply (rule refl)
  apply (clarsimp split: tmres.splits)
  done

text \<open> Left @{const returnOk} absorbtion over @{term bindE}: \<close>
lemma returnOk_bindE [simp]: "(returnOk x >>=E f) = f x"
  apply (unfold bindE_def returnOk_def)
  apply (clarsimp simp: lift_def)
  done

lemma lift_return [simp]:
  "lift (return \<circ> Inr) = return"
  by (simp add: fun_eq_iff lift_def throwError_def split: sum.splits)

text \<open> Right @{const returnOk} absorbtion over @{term bindE}: \<close>
lemma bindE_returnOk [simp]: "(m >>=E returnOk) = m"
  by (simp add: bindE_def returnOk_def)

text \<open> Associativity of @{const bindE}: \<close>
lemma bindE_assoc:
  "(m >>=E f) >>=E g = m >>=E (\<lambda>x. f x >>=E g)"
  apply (simp add: bindE_def bind_assoc)
  apply (rule arg_cong [where f="\<lambda>x. m >>= x"])
  apply (rule ext)
  apply (case_tac x, simp_all add: lift_def throwError_def)
  done

text \<open> @{const returnOk} could also be defined via @{const liftE}: \<close>
lemma returnOk_liftE:
  "returnOk x = liftE (return x)"
  by (simp add: liftE_def returnOk_def)

text \<open> Execution after throwing an exception is skipped: \<close>
lemma throwError_bindE [simp]:
  "(throwError E >>=E f) = throwError E"
  by (simp add: fun_eq_iff bindE_def bind_def throwError_def lift_def return_def split_def)


section "Syntax"

text \<open> This section defines traditional Haskell-like do-syntax
  for the state monad in Isabelle. \<close>

subsection "Syntax for the Nondeterministic State Monad"

text \<open> We use @{text K_bind} to syntactically indicate the
  case where the return argument of the left side of a @{term bind}
  is ignored \<close>
definition
  K_bind_def [iff]: "K_bind \<equiv> \<lambda>x y. x"

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

text \<open> Syntax examples: \<close>
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

subsection "Interference command"

text \<open>Interference commands must be inserted in between actions that can be interfered with commands
running in other threads. \<close>

definition
  last_st_tr :: "(tmid * 's) list \<Rightarrow> 's \<Rightarrow> 's"
where
  "last_st_tr tr s0 = (hd (map snd tr @ [s0]))"

definition
  env_steps :: "('s,unit) tmonad"
where
  "env_steps \<equiv>
  do
    s \<leftarrow> get;
    \<comment> \<open>Add unfiltered environment events to the trace\<close>
    xs \<leftarrow> select UNIV;
    tr \<leftarrow> return (map (Pair Env) xs);
    put_trace tr;
    \<comment> \<open>Pick the last event of the trace as the final state\<close>
    put (last_st_tr tr s)
  od"

definition
  commit_step :: "('s, unit) tmonad"
where
  "commit_step \<equiv>
  do
    s \<leftarrow> get;
    put_trace [(Me,s)]
  od"

definition
  interference :: "('s,unit) tmonad"
where
  "interference \<equiv>
  do
    commit_step;
    env_steps
  od"

subsection "Syntax for the Exception Monad"

text \<open>
  Since the exception monad is a different type, we
  need to syntactically distinguish it in the syntax.
  We use @{text doE}/@{text odE} for this, but can re-use
  most of the productions from @{text do}/@{text od}
  above.
\<close>

syntax
  "_doE" :: "[dobinds, 'a] => 'a"  ("(doE ((_);//(_))//odE)" 100)

translations
  "_doE (_dobinds b bs) e"  == "_doE b (_doE bs e)"
  "_doE (_nobind b) e"      == "b >>=E (CONST K_bind e)"
  "doE x <- a; e odE"       == "a >>=E (\<lambda>x. e)"

text \<open> Syntax examples: \<close>
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


text \<open> Lifting a normal function into the monad type: \<close>
definition
  liftM :: "('a \<Rightarrow> 'b) \<Rightarrow> ('s,'a) tmonad \<Rightarrow> ('s, 'b) tmonad"
where
  "liftM f m \<equiv> do x \<leftarrow> m; return (f x) od"

text \<open> The same for the exception monad: \<close>
definition
  liftME :: "('a \<Rightarrow> 'b) \<Rightarrow> ('s,'e+'a) tmonad \<Rightarrow> ('s,'e+'b) tmonad"
where
  "liftME f m \<equiv> doE x \<leftarrow> m; returnOk (f x) odE"

text \<open> Run a sequence of monads from left to right, ignoring return values. \<close>
definition
  sequence_x :: "('s, 'a) tmonad list \<Rightarrow> ('s, unit) tmonad"
where
  "sequence_x xs \<equiv> foldr (\<lambda>x y. x >>= (\<lambda>_. y)) xs (return ())"

text \<open>
  Map a monadic function over a list by applying it to each element
  of the list from left to right, ignoring return values.
\<close>
definition
  mapM_x :: "('a \<Rightarrow> ('s,'b) tmonad) \<Rightarrow> 'a list \<Rightarrow> ('s, unit) tmonad"
where
  "mapM_x f xs \<equiv> sequence_x (map f xs)"

text \<open>
  Map a monadic function with two parameters over two lists,
  going through both lists simultaneously, left to right, ignoring
  return values.
\<close>
definition
  zipWithM_x :: "('a \<Rightarrow> 'b \<Rightarrow> ('s,'c) tmonad) \<Rightarrow>
                 'a list \<Rightarrow> 'b list \<Rightarrow> ('s, unit) tmonad"
where
  "zipWithM_x f xs ys \<equiv> sequence_x (zipWith f xs ys)"


text \<open> The same three functions as above, but returning a list of
return values instead of @{text unit} \<close>
definition
  sequence :: "('s, 'a) tmonad list \<Rightarrow> ('s, 'a list) tmonad"
where
  "sequence xs \<equiv> let mcons = (\<lambda>p q. p >>= (\<lambda>x. q >>= (\<lambda>y. return (x#y))))
                 in foldr mcons xs (return [])"

definition
  mapM :: "('a \<Rightarrow> ('s,'b) tmonad) \<Rightarrow> 'a list \<Rightarrow> ('s, 'b list) tmonad"
where
  "mapM f xs \<equiv> sequence (map f xs)"

definition
  zipWithM :: "('a \<Rightarrow> 'b \<Rightarrow> ('s,'c) tmonad) \<Rightarrow>
                 'a list \<Rightarrow> 'b list \<Rightarrow> ('s, 'c list) tmonad"
where
  "zipWithM f xs ys \<equiv> sequence (zipWith f xs ys)"

definition
  foldM :: "('b \<Rightarrow> 'a \<Rightarrow> ('s, 'a) tmonad) \<Rightarrow> 'b list \<Rightarrow> 'a \<Rightarrow> ('s, 'a) tmonad"
where
  "foldM m xs a \<equiv> foldr (\<lambda>p q. q >>= m p) xs (return a) "

definition
  foldME ::"('b \<Rightarrow> 'a \<Rightarrow> ('s,('e + 'b)) tmonad) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> ('s, ('e + 'b)) tmonad"
where "foldME m a xs \<equiv> foldr (\<lambda>p q. q >>=E swp m p) xs (returnOk a)"

text \<open> The sequence and map functions above for the exception monad,
with and without lists of return value \<close>
definition
  sequenceE_x :: "('s, 'e+'a) tmonad list \<Rightarrow> ('s, 'e+unit) tmonad"
where
  "sequenceE_x xs \<equiv> foldr (\<lambda>x y. doE _ <- x; y odE) xs (returnOk ())"

definition
  mapME_x :: "('a \<Rightarrow> ('s,'e+'b) tmonad) \<Rightarrow> 'a list \<Rightarrow>
              ('s,'e+unit) tmonad"
where
  "mapME_x f xs \<equiv> sequenceE_x (map f xs)"

definition
  sequenceE :: "('s, 'e+'a) tmonad list \<Rightarrow> ('s, 'e+'a list) tmonad"
where
  "sequenceE xs \<equiv> let mcons = (\<lambda>p q. p >>=E (\<lambda>x. q >>=E (\<lambda>y. returnOk (x#y))))
                 in foldr mcons xs (returnOk [])"

definition
  mapME :: "('a \<Rightarrow> ('s,'e+'b) tmonad) \<Rightarrow> 'a list \<Rightarrow>
              ('s,'e+'b list) tmonad"
where
  "mapME f xs \<equiv> sequenceE (map f xs)"


text \<open> Filtering a list using a monadic function as predicate: \<close>
primrec
  filterM :: "('a \<Rightarrow> ('s, bool) tmonad) \<Rightarrow> 'a list \<Rightarrow> ('s, 'a list) tmonad"
where
  "filterM P []       = return []"
| "filterM P (x # xs) = do
     b  <- P x;
     ys <- filterM P xs;
     return (if b then (x # ys) else ys)
   od"

text \<open> @{text select_state} takes a relationship between
  states, and outputs nondeterministically a state
  related to the input state. \<close>

definition
  state_select :: "('s \<times> 's) set \<Rightarrow> ('s, unit) tmonad"
where
  "state_select r \<equiv> (do
    s \<leftarrow> get;
    S \<leftarrow> return {s'. (s, s') \<in> r};
    assert (S \<noteq> {});
    s' \<leftarrow> select S;
    put s'
  od)"
section "Catching and Handling Exceptions"

text \<open>
  Turning an exception monad into a normal state monad
  by catching and handling any potential exceptions:
\<close>
definition
  catch :: "('s, 'e + 'a) tmonad \<Rightarrow>
            ('e \<Rightarrow> ('s, 'a) tmonad) \<Rightarrow>
            ('s, 'a) tmonad" (infix "<catch>" 10)
where
  "f <catch> handler \<equiv>
     do x \<leftarrow> f;
        case x of
          Inr b \<Rightarrow> return b
        | Inl e \<Rightarrow> handler e
     od"

text \<open>
  Handling exceptions, but staying in the exception monad.
  The handler may throw a type of exceptions different from
  the left side.
\<close>
definition
  handleE' :: "('s, 'e1 + 'a) tmonad \<Rightarrow>
               ('e1 \<Rightarrow> ('s, 'e2 + 'a) tmonad) \<Rightarrow>
               ('s, 'e2 + 'a) tmonad" (infix "<handle2>" 10)
where
  "f <handle2> handler \<equiv>
   do
      v \<leftarrow> f;
      case v of
        Inl e \<Rightarrow> handler e
      | Inr v' \<Rightarrow> return (Inr v')
   od"

text \<open>
  A type restriction of the above that is used more commonly in
  practice: the exception handle (potentially) throws exception
  of the same type as the left-hand side.
\<close>
definition
  handleE :: "('s, 'x + 'a) tmonad \<Rightarrow>
              ('x \<Rightarrow> ('s, 'x + 'a) tmonad) \<Rightarrow>
              ('s, 'x + 'a) tmonad" (infix "<handle>" 10)
where
  "handleE \<equiv> handleE'"


text \<open>
  Handling exceptions, and additionally providing a continuation
  if the left-hand side throws no exception:
\<close>
definition
  handle_elseE :: "('s, 'e + 'a) tmonad \<Rightarrow>
                   ('e \<Rightarrow> ('s, 'ee + 'b) tmonad) \<Rightarrow>
                   ('a \<Rightarrow> ('s, 'ee + 'b) tmonad) \<Rightarrow>
                   ('s, 'ee + 'b) tmonad"
  ("_ <handle> _ <else> _" 10)
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
  monad.
\<close>
inductive_set
  whileLoop_results :: "('r \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('r \<Rightarrow> ('s, 'r) tmonad) \<Rightarrow> (('r \<times> 's) \<times> ((tmid \<times> 's) list \<times> ('s, 'r) tmres)) set"
  for C B
where
    "\<lbrakk> \<not> C r s \<rbrakk> \<Longrightarrow> ((r, s), ([], Result (r, s))) \<in> whileLoop_results C B"
  | "\<lbrakk> C r s; (ts, Failed) \<in> B r s \<rbrakk> \<Longrightarrow> ((r, s), (ts, Failed)) \<in> whileLoop_results C B"
  | "\<lbrakk> C r s; (ts, Incomplete) \<in> B r s \<rbrakk> \<Longrightarrow> ((r, s), (ts, Incomplete)) \<in> whileLoop_results C B"
  | "\<lbrakk> C r s; (ts, Result (r', s')) \<in> B r s; ((r', s'), (ts',z)) \<in> whileLoop_results C B  \<rbrakk>
       \<Longrightarrow> ((r, s), (ts'@ts,z)) \<in> whileLoop_results C B"

inductive_cases whileLoop_results_cases_result_end: "((x,y), ([],Result r)) \<in> whileLoop_results C B"
inductive_cases whileLoop_results_cases_fail: "((x,y), (ts, Failed)) \<in> whileLoop_results C B"
inductive_cases whileLoop_results_cases_incomplete: "((x,y), (ts, Incomplete)) \<in> whileLoop_results C B"

inductive_simps whileLoop_results_simps_valid: "((x,y), ([], Result z)) \<in> whileLoop_results C B"

inductive
  whileLoop_terminates :: "('r \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('r \<Rightarrow> ('s, 'r) tmonad) \<Rightarrow> 'r \<Rightarrow> 's \<Rightarrow> bool"
  for C B
where
    "\<not> C r s \<Longrightarrow> whileLoop_terminates C B r s"
  | "\<lbrakk> C r s; \<forall>(r', s') \<in> Result -` snd ` (B r s). whileLoop_terminates C B r' s' \<rbrakk>
        \<Longrightarrow> whileLoop_terminates C B r s"


inductive_cases whileLoop_terminates_cases: "whileLoop_terminates C B r s"
inductive_simps whileLoop_terminates_simps: "whileLoop_terminates C B r s"

definition
  whileLoop :: "('r \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('r \<Rightarrow> ('s, 'r) tmonad) \<Rightarrow> 'r \<Rightarrow> ('s, 'r) tmonad"
where
  "whileLoop C B \<equiv> (\<lambda>r s. {(ts, res). ((r,s), ts,res) \<in> whileLoop_results C B})"

notation (output)
  whileLoop  ("(whileLoop (_)//  (_))" [1000, 1000] 1000)

definition
  whileLoopT :: "('r \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('r \<Rightarrow> ('s, 'r) tmonad) \<Rightarrow> 'r \<Rightarrow> ('s, 'r) tmonad"
where
  "whileLoopT C B \<equiv> (\<lambda>r s. {(ts, res). ((r,s), ts,res) \<in> whileLoop_results C B
                                         \<and> whileLoop_terminates C B r s})"

notation (output)
  whileLoopT  ("(whileLoopT (_)//  (_))" [1000, 1000] 1000)

definition
  whileLoopE :: "('r \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('r \<Rightarrow> ('s, 'e + 'r) tmonad)
      \<Rightarrow> 'r \<Rightarrow> ('s, ('e + 'r)) tmonad"
where
  "whileLoopE C body \<equiv>
      \<lambda>r. whileLoop (\<lambda>r s. (case r of Inr v \<Rightarrow> C v s | _ \<Rightarrow> False)) (lift body) (Inr r)"

notation (output)
  whileLoopE  ("(whileLoopE (_)//  (_))" [1000, 1000] 1000)

subsection "Await command"

text \<open> @{term "Await c f"} blocks the execution until the @{term "c"} is true,
      and atomically executes @{term "f"}.
\<close>

definition
  Await :: "('s \<Rightarrow> bool) \<Rightarrow> ('s,unit) tmonad"
where
  "Await c \<equiv>
  do
    s \<leftarrow> get;
    \<comment> \<open>Add unfiltered environment events, with the last one
       satisfying the `c' state predicate\<close>
    xs \<leftarrow> select {xs. c (last_st_tr (map (Pair Env) xs) s)};
    tr \<leftarrow> return (map (Pair Env) xs);
    put_trace tr;
    \<comment> \<open>Pick the last event of the trace\<close>
    put (last_st_tr tr s)
  od"

section "Hoare Logic"

subsection "Validity"

text \<open> This section defines a Hoare logic for partial correctness for
  the nondeterministic state monad as well as the exception monad.
  The logic talks only about the behaviour part of the monad and ignores
  the failure flag.

  The logic is defined semantically. Rules work directly on the
  validity predicate.

  In the nondeterministic state monad, validity is a triple of precondition,
  monad, and postcondition. The precondition is a function from state to
  bool (a state predicate), the postcondition is a function from return value
  to state to bool. A triple is valid if for all states that satisfy the
  precondition, all result values and result states that are returned by
  the monad satisfy the postcondition. Note that if the computation returns
  the empty set, the triple is trivially valid. This means @{term "assert P"}
  does not require us to prove that @{term P} holds, but rather allows us
  to assume @{term P}! Proving non-failure is done via separate predicate and
  calculus (see below).
\<close>


definition
  valid :: "('s \<Rightarrow> bool) \<Rightarrow> ('s,'a) tmonad \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
  ("\<lbrace>_\<rbrace>/ _ /\<lbrace>_\<rbrace>")
where
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<equiv> \<forall>s. P s \<longrightarrow> (\<forall>(r,s') \<in> mres (f s). Q r s')"

text \<open>
  We often reason about invariant predicates. The following provides shorthand syntax
  that avoids repeating potentially long predicates.
\<close>
abbreviation (input)
  invariant :: "('s,'a) tmonad \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> bool" ("_ \<lbrace>_\<rbrace>" [59,0] 60)
where
  "invariant f P \<equiv> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. P\<rbrace>"

text \<open>rg_pred type: Rely-Guaranty predicates (state before => state after => bool)\<close>
type_synonym 's rg_pred = "'s \<Rightarrow> 's \<Rightarrow> bool"


text \<open>
  Validity for the exception monad is similar and build on the standard
  validity above. Instead of one postcondition, we have two: one for
  normal and one for exceptional results.
\<close>
definition
  validE :: "('s \<Rightarrow> bool) \<Rightarrow> ('s, 'a + 'b) tmonad \<Rightarrow>
             ('b \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
             ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
("\<lbrace>_\<rbrace>/ _ /(\<lbrace>_\<rbrace>,/ \<lbrace>_\<rbrace>)" )
where
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<equiv> \<lbrace>P\<rbrace> f \<lbrace> \<lambda>v s. case v of Inr r \<Rightarrow> Q r s | Inl e \<Rightarrow> E e s \<rbrace>"
(*
text \<open> Validity for exception monad with interferences. Not as easy to phrase
 as we need to  \<close>
definition
  validIE :: "('s, 'a + 'b) tmonad \<Rightarrow>
             's rg_pred \<Rightarrow>
             's rg_pred \<Rightarrow> 's rg_pred \<Rightarrow>
             ('b \<Rightarrow> 's rg_pred) \<Rightarrow>
             ('a \<Rightarrow> 's rg_pred) \<Rightarrow> bool"
 ("_ //PRE _//RELY _//GUAR _//POST _//EXC _" [59,0,0,0,0,0] 60)
where
  "validIE f P R G Q E \<equiv> f SAT [P,R,G,\<lambda>v. case v of Inr r \<Rightarrow> Q r | Inl e \<Rightarrow> E e]"

abbreviation (input)
  validIEsat :: "('s, 'a + 'b) tmonad \<Rightarrow>
             's rg_pred \<Rightarrow>
             's rg_pred \<Rightarrow> 's rg_pred \<Rightarrow>
             ('b \<Rightarrow> 's rg_pred) \<Rightarrow>
             ('a \<Rightarrow> 's rg_pred) \<Rightarrow> bool"
  ("_ //SAT [_, _, _, _, _]" [59,0,0,0,0,0] 60)
  where
  "validIEsat f P R G Q E \<equiv> validIE f P R G Q E"
 *)
text \<open>
  The following two instantiations are convenient to separate reasoning
  for exceptional and normal case.
\<close>
definition
  validE_R :: "('s \<Rightarrow> bool) \<Rightarrow> ('s, 'e + 'a) tmonad \<Rightarrow>
               ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
   ("\<lbrace>_\<rbrace>/ _ /\<lbrace>_\<rbrace>, -")
where
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,- \<equiv> validE P f Q (\<lambda>x y. True)"

definition
  validE_E :: "('s \<Rightarrow> bool) \<Rightarrow>  ('s, 'e + 'a) tmonad \<Rightarrow>
               ('e \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
   ("\<lbrace>_\<rbrace>/ _ /-, \<lbrace>_\<rbrace>")
where
  "\<lbrace>P\<rbrace> f -,\<lbrace>Q\<rbrace> \<equiv> validE P f (\<lambda>x y. True) Q"


text \<open> Abbreviations for trivial preconditions: \<close>
abbreviation(input)
  top :: "'a \<Rightarrow> bool" ("\<top>")
where
  "\<top> \<equiv> \<lambda>_. True"

abbreviation(input)
  bottom :: "'a \<Rightarrow> bool" ("\<bottom>")
where
  "\<bottom> \<equiv> \<lambda>_. False"

text \<open> Abbreviations for trivial postconditions (taking two arguments): \<close>
abbreviation(input)
  toptop :: "'a \<Rightarrow> 'b \<Rightarrow> bool" ("\<top>\<top>")
where
  "\<top>\<top> \<equiv> \<lambda>_ _. True"

abbreviation(input)
  toptoptop :: "'a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool" ("\<top>\<top>\<top>")
where
  "\<top>\<top>\<top> \<equiv> \<lambda>_ _ _. True"

abbreviation(input)
  botbot :: "'a \<Rightarrow> 'b \<Rightarrow> bool" ("\<bottom>\<bottom>")
where
  "\<bottom>\<bottom> \<equiv> \<lambda>_ _. False"

abbreviation(input)
  botbotbot :: "'a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool" ("\<bottom>\<bottom>\<bottom>")
where
  "\<bottom>\<bottom>\<bottom> \<equiv> \<lambda>_ _ _. False"

text \<open>
  Lifting @{text "\<and>"} and @{text "\<or>"} over two arguments.
  Lifting @{text "\<and>"} and @{text "\<or>"} over one argument is already
  defined (written @{text "and"} and @{text "or"}).
\<close>
definition
  bipred_conj :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)"
  (infixl "And" 96)
where
  "bipred_conj P Q \<equiv> \<lambda>x y. P x y \<and> Q x y"

definition
  bipred_disj :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)"
  (infixl "Or" 91)
where
  "bipred_disj P Q \<equiv> \<lambda>x y. P x y \<or> Q x y"

subsection "Determinism"

text \<open> A monad of type @{text tmonad} is deterministic iff it
returns an empty trace, exactly one state and result and does not fail \<close>
definition
  det :: "('a,'s) tmonad \<Rightarrow> bool"
where
  "det f \<equiv> \<forall>s. \<exists>r. f s = {([], Result r)}"

text \<open> A deterministic @{text tmonad} can be turned
  into a normal state monad: \<close>
definition
  the_run_state :: "('s,'a) tmonad \<Rightarrow> 's \<Rightarrow> 'a \<times> 's"
where
  "the_run_state M \<equiv> \<lambda>s. THE s'. mres (M s) = {s'}"


subsection "Non-Failure"

text \<open>
  We can formulate non-failure separately from validity.
\<close>
definition
  no_fail :: "('s \<Rightarrow> bool) \<Rightarrow> ('s,'a) tmonad \<Rightarrow> bool"
where
  "no_fail P m \<equiv> \<forall>s. P s \<longrightarrow> Failed \<notin> snd ` (m s)"

text \<open>
  It is often desired to prove non-failure and a Hoare triple
  simultaneously, as the reasoning is often similar. The following
  definitions allow such reasoning to take place.
\<close>

definition
  validNF ::"('s \<Rightarrow> bool) \<Rightarrow> ('s,'a) tmonad \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
      ("\<lbrace>_\<rbrace>/ _ /\<lbrace>_\<rbrace>!")
where
  "validNF P f Q \<equiv> valid P f Q \<and> no_fail P f"

definition
  validE_NF :: "('s \<Rightarrow> bool) \<Rightarrow> ('s, 'a + 'b) tmonad \<Rightarrow>
             ('b \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
             ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
  ("\<lbrace>_\<rbrace>/ _ /(\<lbrace>_\<rbrace>,/ \<lbrace>_\<rbrace>!)")
where
  "validE_NF P f Q E \<equiv> validE P f Q E \<and> no_fail P f"

lemma validE_NF_alt_def:
  "\<lbrace> P \<rbrace> B \<lbrace> Q \<rbrace>,\<lbrace> E \<rbrace>! = \<lbrace> P \<rbrace> B \<lbrace> \<lambda>v s. case v of Inl e \<Rightarrow> E e s | Inr r \<Rightarrow> Q r s \<rbrace>!"
  by (clarsimp simp: validE_NF_def validE_def validNF_def)

(* text \<open>
  Usually, well-formed monads constructed from the primitives
  above will have the following property: if they return an
  empty set of results, they will have the failure flag set.
\<close>
definition
  empty_fail :: "('s,'a) tmonad \<Rightarrow> bool"
where
  "empty_fail m \<equiv> \<forall>s. fst (m s) = {} \<longrightarrow> snd (m s)"

text \<open>
  Useful in forcing otherwise unknown executions to have
  the @{const empty_fail} property.
\<close>
definition
  mk_ef :: "'a set \<times> bool \<Rightarrow> 'a set \<times> bool"
where
  "mk_ef S \<equiv> (fst S, fst S = {} \<or> snd S)"
 *)
section "Basic exception reasoning"

text \<open>
  The following predicates @{text no_throw} and @{text no_return} allow
  reasoning that functions in the exception monad either do
  no throw an exception or never return normally.
\<close>

definition "no_throw P A \<equiv> \<lbrace> P \<rbrace> A \<lbrace> \<lambda>_ _. True \<rbrace>,\<lbrace> \<lambda>_ _. False \<rbrace>"

definition "no_return P A \<equiv> \<lbrace> P \<rbrace> A \<lbrace>\<lambda>_ _. False\<rbrace>,\<lbrace>\<lambda>_ _. True \<rbrace>"

section "Trace monad Parallel"

definition
  parallel :: "('s,'a) tmonad \<Rightarrow> ('s,'a) tmonad \<Rightarrow> ('s,'a) tmonad"
where
  "parallel f g = (\<lambda>s. {(xs, rv). \<exists>f_steps. length f_steps = length xs
    \<and> (map (\<lambda>(f_step, (id, s)). (if f_step then id else Env, s)) (zip f_steps xs), rv) \<in> f s
    \<and> (map (\<lambda>(f_step, (id, s)). (if f_step then Env else id, s)) (zip f_steps xs), rv) \<in> g s})"

abbreviation(input)
  "parallel_mrg \<equiv> ((\<lambda>((idn, s), (idn', _)). (if idn = Env then idn' else idn, s)))"

lemma parallel_def2:
  "parallel f g = (\<lambda>s. {(xs, rv). \<exists>ys zs. (ys, rv) \<in> f s \<and> (zs, rv) \<in> g s
    \<and> list_all2 (\<lambda>y z. (fst y = Env \<or> fst z = Env) \<and> snd y = snd z) ys zs
    \<and> xs = map parallel_mrg (zip ys zs)})"
  apply (simp add: parallel_def fun_eq_iff set_eq_iff)
  apply safe
   apply (rule exI, rule conjI, assumption)+
   apply (simp add: list_all2_conv_all_nth list_eq_iff_nth_eq split_def prod_eq_iff)
   apply clarsimp
  apply (rule_tac x="map (((\<noteq>) Env) o fst) ys" in exI)
  apply (simp add: zip_map1 o_def split_def)
  apply (strengthen subst[where P="\<lambda>xs. (xs, v) \<in> S" for v S, mk_strg I _ E])
  apply (clarsimp simp: list_all2_conv_all_nth list_eq_iff_nth_eq
                        split_def prod_eq_iff
             split del: if_split cong: if_cong)
  apply auto
  done

lemma parallel_def3:
  "parallel f g = (\<lambda>s. (\<lambda>(ys, zs, rv). (map parallel_mrg (zip ys zs), rv))
    ` {(ys, zs, rv). (ys, rv) \<in> f s \<and> (zs, rv) \<in> g s
    \<and> list_all2 (\<lambda>y z. (fst y = Env \<or> fst z = Env) \<and> snd y = snd z) ys zs})"
  by (simp add: parallel_def2, rule ext, auto simp: image_def)

primrec
  trace_steps :: "(tmid \<times> 's) list \<Rightarrow> 's \<Rightarrow> (tmid \<times> 's \<times> 's) set"
where
  "trace_steps (elem # trace) s0 = {(fst elem, s0, snd elem)} \<union> trace_steps trace (snd elem)"
| "trace_steps [] s0 = {}"

lemma trace_steps_nth:
  "trace_steps xs s0 = (\<lambda>i. (fst (xs ! i), (if i = 0 then s0 else snd (xs ! (i - 1))), snd (xs ! i))) ` {..< length xs}"
proof (induct xs arbitrary: s0)
  case Nil
  show ?case by simp
next
  case (Cons a xs)
  show ?case
    apply (simp add: lessThan_Suc_eq_insert_0 Cons image_image nth_Cons')
    apply (intro arg_cong2[where f=insert] refl image_cong)
    apply simp
    done
qed

definition
  rely_cond :: "'s rg_pred \<Rightarrow> 's \<Rightarrow> (tmid \<times> 's) list \<Rightarrow> bool"
where
  "rely_cond R s0s tr = (\<forall>(ident, s0, s) \<in> trace_steps (rev tr) s0s. ident = Env \<longrightarrow> R s0 s)"

definition
  guar_cond :: "'s rg_pred \<Rightarrow> 's \<Rightarrow> (tmid \<times> 's) list \<Rightarrow> bool"
where
  "guar_cond G s0s tr = (\<forall>(ident, s0, s) \<in> trace_steps (rev tr) s0s. ident = Me \<longrightarrow> G s0 s)"

lemma rg_empty_conds[simp]:
  "rely_cond R s0s []"
  "guar_cond G s0s []"
  by (simp_all add: rely_cond_def guar_cond_def)

definition
  rely :: "('s, 'a) tmonad \<Rightarrow> 's rg_pred \<Rightarrow> 's \<Rightarrow> ('s, 'a) tmonad"
where
  "rely f R s0s \<equiv> (\<lambda>s. f s \<inter> ({tr. rely_cond R s0s tr} \<times> UNIV))"

definition
  prefix_closed :: "('s, 'a) tmonad \<Rightarrow> bool"
where
  "prefix_closed f = (\<forall>s. \<forall>x xs. (x # xs) \<in> fst ` f s \<longrightarrow> (xs, Incomplete) \<in> f s)"

definition
  validI :: "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's rg_pred \<Rightarrow> ('s,'a) tmonad
    \<Rightarrow> 's rg_pred \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
  ("(\<lbrace>_\<rbrace>,/ \<lbrace>_\<rbrace>)/ _ /(\<lbrace>_\<rbrace>,/ \<lbrace>_\<rbrace>)")
where
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace> \<equiv> prefix_closed f \<and> (\<forall>s0 s. P s0 s
    \<longrightarrow> (\<forall>tr res. (tr, res) \<in> (rely f R s0 s) \<longrightarrow> guar_cond G s0 tr
        \<and> (\<forall>rv s'. res = Result (rv, s') \<longrightarrow> Q rv (last_st_tr tr s0) s')))"

lemma in_rely:
  "\<lbrakk> (tr, res) \<in> f s; rely_cond R s0s tr \<rbrakk> \<Longrightarrow> (tr, res) \<in> rely f R s0s s"
  by (simp add: rely_def)

lemmas validI_D = validI_def[THEN meta_eq_to_obj_eq, THEN iffD1,
    THEN conjunct2, rule_format, OF _ _ in_rely]
lemmas validI_GD = validI_D[THEN conjunct1]
lemmas validI_rvD = validI_D[THEN conjunct2, rule_format, rotated -1, OF refl]
lemmas validI_prefix_closed = validI_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct1]
lemmas validI_prefix_closed_T = validI_prefix_closed[where P="\<lambda>_ _. False" and R="\<lambda>_ _. False"
    and G="\<lambda>_ _. True" and Q="\<lambda>_ _ _. True"]

lemmas prefix_closedD1 = prefix_closed_def[THEN iffD1, rule_format]

lemma in_fst_snd_image_eq:
  "x \<in> fst ` S = (\<exists>y. (x, y) \<in> S)"
  "y \<in> snd ` S = (\<exists>x. (x, y) \<in> S)"
  by (auto elim: image_eqI[rotated])

lemma in_fst_snd_image:
  "(x, y) \<in> S \<Longrightarrow> x \<in> fst ` S"
  "(x, y) \<in> S \<Longrightarrow> y \<in> snd ` S"
  by (auto simp: in_fst_snd_image_eq)

lemmas prefix_closedD = prefix_closedD1[OF _ in_fst_snd_image(1)]

end
