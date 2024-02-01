(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

chapter "Interference Trace Monad"

theory Trace_Monad
  imports
    Fun_Pred_Syntax
    Monad_Lib
    Strengthen
begin

text \<open>
  The ``Interference Trace Monad''. This nondeterministic monad
  records the state at every interference point, permitting
  nondeterministic interference by the environment at these points.

  The trace set initially includes all possible environment behaviours.
  Trace steps are tagged as environment or self actions, and can then
  be constrained to a smaller set where the environment acts according
  to a rely constraint (i.e. rely-guarantee reasoning), or to set the
  environment actions to be the self actions of another program (parallel
  composition).\<close>

section "The Trace Monad"

text \<open>Trace monad identifier. Me corresponds to the current thread running and Env to the environment.\<close>
datatype tmid = Me | Env

text \<open>
  Results associated with traces. Traces may correspond to incomplete, failed, or completed executions.\<close>
datatype ('s, 'a) tmres = Failed | Incomplete | Result "('a \<times> 's)"

abbreviation map_tmres_rv :: "('a \<Rightarrow> 'b) \<Rightarrow> ('s, 'a) tmres \<Rightarrow> ('s, 'b) tmres" where
  "map_tmres_rv f \<equiv> map_tmres id f"

text \<open>
  tmonad returns a set of non-deterministic computations, including
  a trace as a list of @{text "thread identifier \<times> state"}, and an optional
  pair of result and state when the computation did not fail.\<close>
type_synonym ('s, 'a) tmonad = "'s \<Rightarrow> ((tmid \<times> 's) list \<times> ('s, 'a) tmres) set"

text \<open>
  Print the type @{typ "('s,'a) tmonad"} instead of its unwieldy expansion.
  Needs an AST translation in code, because it needs to check that the state variable
  @{typ 's} occurs three times. This comparison is not guaranteed to always work as expected
  (AST instances might have different decoration), but it does seem to work here.\<close>
print_ast_translation \<open>
  let
    fun tmonad_tr _ [t1, Ast.Appl [Ast.Constant @{type_syntax set},
                          Ast.Appl [Ast.Constant @{type_syntax prod},
                            Ast.Appl [Ast.Constant @{type_syntax list},
                              Ast.Appl [Ast.Constant @{type_syntax prod},
                                Ast.Constant @{type_syntax tmid}, t2]],
                            Ast.Appl [Ast.Constant @{type_syntax tmres}, t3, t4]]]] =
      if t1 = t2 andalso t1 = t3
      then Ast.Appl [Ast.Constant @{type_syntax "tmonad"}, t1, t4]
      else raise Match
  in [(@{type_syntax "fun"}, tmonad_tr)] end\<close>


text \<open>Returns monad results, ignoring failures and traces.\<close>
definition mres :: "((tmid \<times> 's) list \<times> ('s, 'a) tmres) set \<Rightarrow> ('a \<times> 's) set" where
  "mres r = Result -` (snd ` r)"

text \<open>True if the monad has a computation resulting in Failed.\<close>
definition failed :: "((tmid \<times> 's) list \<times> ('s, 'a) tmres) set \<Rightarrow> bool" where
  "failed r \<equiv> Failed \<in> snd ` r"

lemma failed_simps[simp]:
  "failed {(x, y)} = (y = Failed)"
  "failed (r \<union> r') = (failed r \<or> failed r')"
  "\<not> failed {}"
  by (auto simp: failed_def)


text \<open>
  The definition of fundamental monad functions @{text return} and
  @{text bind}. The monad function @{text "return x"} does not change
  the  state, does not fail, and returns @{text "x"}.\<close>
definition return :: "'a \<Rightarrow> ('s,'a) tmonad" where
  "return a \<equiv> \<lambda>s. ({([], Result (a, s))})"

text \<open>
  The monad function @{text "bind f g"}, also written @{text "f >>= g"},
  is the execution of @{term f} followed by the execution of @{text g}.
  The function @{text g} takes the result value \emph{and} the result
  state of @{text f} as parameter. The definition says that the result of
  the combined operation is the union of the set of sets that is created
  by @{text g} applied to the result sets of @{text f}. The combined
  operation may have failed, if @{text f} may have failed or @{text g} may
  have failed on any of the results of @{text f}.\<close>
abbreviation (input) fst_upd :: "('a \<Rightarrow> 'c) \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'c \<times> 'b" where
  "fst_upd f \<equiv> \<lambda>(a,b). (f a, b)"

abbreviation (input) snd_upd :: "('b \<Rightarrow> 'c) \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'c" where
  "snd_upd f \<equiv> \<lambda>(a,b). (a, f b)"

definition bind ::
  "('s, 'a) tmonad \<Rightarrow> ('a \<Rightarrow> ('s, 'b) tmonad) \<Rightarrow> ('s, 'b) tmonad" (infixl ">>=" 60)
  where
  "bind f g \<equiv> \<lambda>s. \<Union>(xs, r) \<in> (f s). case r of Failed \<Rightarrow> {(xs, Failed)}
    | Incomplete \<Rightarrow> {(xs, Incomplete)}
    | Result (rv, s) \<Rightarrow> fst_upd (\<lambda>ys. ys @ xs) ` g rv s"

text \<open>Sometimes it is convenient to write @{text bind} in reverse order.\<close>
abbreviation (input) bind_rev ::
  "('c \<Rightarrow> ('a, 'b) tmonad) \<Rightarrow> ('a, 'c) tmonad \<Rightarrow> ('a, 'b) tmonad" (infixl "=<<" 60)
  where
  "g =<< f \<equiv> f >>= g"

text \<open>
  The basic accessor functions of the state monad. @{text get} returns the
  current state as result, does not change the state, and does not add to the
  trace. @{text "put s"} returns nothing (@{typ unit}), changes the current
  state to @{text s}, and does not add to the trace. @{text "put_trace xs"}
  returns nothing (@{typ unit}), does not change the state, and adds @{text xs}
  to the trace.\<close>
definition get :: "('s,'s) tmonad" where
  "get \<equiv> \<lambda>s. {([], Result (s, s))}"

definition put :: "'s \<Rightarrow> ('s, unit) tmonad" where
  "put s \<equiv> \<lambda>_. {([], Result ((), s))}"

definition put_trace_elem :: "(tmid \<times> 's) \<Rightarrow> ('s, unit) tmonad" where
  "put_trace_elem x = (\<lambda>s. {([], Incomplete), ([x], Result ((), s))})"

primrec put_trace :: "(tmid \<times> 's) list \<Rightarrow> ('s, unit) tmonad" where
    "put_trace [] = return ()"
  | "put_trace (x # xs) = (put_trace xs >>= (\<lambda>_. put_trace_elem x))"


subsection "Nondeterminism"

text \<open>
  Basic nondeterministic functions. @{text "select A"} chooses an element
  of the set @{text A} as the result, does not change the state, does not add
  to the trace, and does not fail (even if the set is empty). @{text "f \<sqinter> g"}
  executes @{text f} or executes @{text g}. It returns the union of results and
  traces of @{text f} and @{text g}.\<close>
definition select :: "'a set \<Rightarrow> ('s, 'a) tmonad" where
  "select A \<equiv> \<lambda>s. (Pair [] ` Result ` (A \<times> {s}))"

definition alternative ::
  "('s,'a) tmonad \<Rightarrow> ('s,'a) tmonad \<Rightarrow> ('s,'a) tmonad" (infixl "\<sqinter>" 20)
  where
  "f \<sqinter> g \<equiv> \<lambda>s. (f s \<union> g s)"

text \<open>
  FIXME: The @{text select_f} function was left out here until we figure
  out what variant we actually need.\<close>

definition
  "default_elem dflt A \<equiv> if A = {} then {dflt} else A"

text \<open>
  @{text state_select} takes a relationship between states, and outputs
  nondeterministically a state related to the input state. Fails if no such
  state exists.\<close>
definition state_select :: "('s \<times> 's) set \<Rightarrow> ('s, unit) tmonad" where
  "state_select r \<equiv>
     \<lambda>s. (Pair [] ` default_elem Failed (Result ` (\<lambda>x. ((), x)) ` {s'. (s, s') \<in> r}))"


subsection "Failure"

text \<open>
  The monad function that always fails. Returns an empty trace with a Failed result.\<close>
definition fail :: "('s, 'a) tmonad" where
  "fail \<equiv> \<lambda>s. {([], Failed)}"

text \<open>Assertions: fail if the property @{text P} is not true\<close>
definition assert :: "bool \<Rightarrow> ('a, unit) tmonad" where
  "assert P \<equiv> if P then return () else fail"

text \<open>Fail if the value is @{const None}, return result @{text v} for @{term "Some v"}\<close>
definition assert_opt :: "'a option \<Rightarrow> ('b, 'a) tmonad" where
  "assert_opt v \<equiv> case v of None \<Rightarrow> fail | Some v \<Rightarrow> return v"

text \<open>An assertion that also can introspect the current state.\<close>
definition state_assert :: "('s \<Rightarrow> bool) \<Rightarrow> ('s, unit) tmonad" where
  "state_assert P \<equiv> get >>= (\<lambda>s. assert (P s))"

subsection "Generic functions on top of the state monad"

text \<open>Apply a function to the current state and return the result without changing the state.\<close>
definition gets :: "('s \<Rightarrow> 'a) \<Rightarrow> ('s, 'a) tmonad" where
  "gets f \<equiv> get >>= (\<lambda>s. return (f s))"

text \<open>Modify the current state using the function passed in.\<close>
definition modify :: "('s \<Rightarrow> 's) \<Rightarrow> ('s, unit) tmonad" where
  "modify f \<equiv> get >>= (\<lambda>s. put (f s))"

lemma simpler_gets_def:
  "gets f = (\<lambda>s. {([], Result ((f s), s))})"
  by (simp add: gets_def return_def bind_def get_def)

lemma simpler_modify_def:
  "modify f = (\<lambda>s. {([], Result ((),(f s)))})"
  by (simp add: modify_def bind_def get_def put_def)

text \<open>Execute the given monad when the condition is true, return @{text "()"} otherwise.\<close>
definition "when" :: "bool \<Rightarrow> ('s, unit) tmonad \<Rightarrow> ('s, unit) tmonad" where
  "when P m \<equiv> if P then m else return ()"

text \<open>Execute the given monad unless the condition is true, return @{text "()"} otherwise.\<close>
definition unless :: "bool \<Rightarrow> ('s, unit) tmonad \<Rightarrow> ('s, unit) tmonad" where
  "unless P m \<equiv> when (\<not>P) m"

text \<open>
  Perform a test on the current state, performing the left monad if
  the result is true or the right monad if the result is false.\<close>
definition condition ::
  "('s \<Rightarrow> bool) \<Rightarrow> ('s, 'r) tmonad \<Rightarrow> ('s, 'r) tmonad \<Rightarrow> ('s, 'r) tmonad"
  where
  "condition P L R \<equiv> \<lambda>s. if (P s) then (L s) else (R s)"

notation (output)
  condition  ("(condition (_)//  (_)//  (_))" [1000,1000,1000] 1000)

text \<open>
  Apply an option valued function to the current state, fail if it returns @{const None},
  return @{text v} if it returns @{term "Some v"}.\<close>
definition gets_the :: "('s \<Rightarrow> 'a option) \<Rightarrow> ('s, 'a) tmonad" where
  "gets_the f \<equiv> gets f >>= assert_opt"

text \<open>
  Get a map (such as a heap) from the current state and apply an argument to the map.
  Fail if the map returns @{const None}, otherwise return the value.\<close>
definition gets_map :: "('s \<Rightarrow> 'a \<Rightarrow> 'b option) \<Rightarrow> 'a \<Rightarrow> ('s, 'b) tmonad" where
  "gets_map f p \<equiv> gets f >>= (\<lambda>m. assert_opt (m p))"


subsection \<open>The Monad Laws\<close>

text \<open>An alternative definition of @{term bind}, sometimes more convenient.\<close>
lemma bind_def':
  "bind f g \<equiv>
     \<lambda>s. ((\<lambda>xs. (xs, Failed)) ` {xs. (xs, Failed) \<in> f s})
         \<union> ((\<lambda>xs. (xs, Incomplete)) ` {xs. (xs, Incomplete) \<in> f s})
         \<union> (\<Union>(xs, rv, s) \<in> {(xs, rv, s'). (xs, Result (rv, s')) \<in> f s}. fst_upd (\<lambda>ys. ys @ xs) ` g rv s)"
  apply (clarsimp simp add: bind_def fun_eq_iff
                            Un_Union_image split_def
                    intro!: eq_reflection)
  apply (fastforce split: tmres.splits elim!: rev_bexI[where A="f x" for x]
                   intro: image_eqI[rotated])
  done

lemma elem_bindE:
  "\<lbrakk>(tr, res) \<in> bind f g s;
    \<lbrakk>res = Incomplete \<or> res = Failed; (tr, map_tmres undefined undefined res) \<in> f s\<rbrakk> \<Longrightarrow> P;
    \<And>tr' tr'' x s'. \<lbrakk>(tr', Result (x, s')) \<in> f s; (tr'', res) \<in> g x s'; tr = tr'' @ tr'\<rbrakk> \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by (auto simp: bind_def')

text \<open>Each monad satisfies at least the following three laws.\<close>

\<comment> \<open>FIXME: is this necessary? If it is, move it\<close>
declare map_option.identity[simp]

text \<open>@{term return} is absorbed at the left of a @{term bind}, applying the return value directly:\<close>
lemma return_bind[simp]:
  "(return x >>= f) = f x"
  by (simp add: return_def bind_def)

text \<open>@{term return} is absorbed on the right of a @{term bind}\<close>
lemma bind_return[simp]:
  "(m >>= return) = m"
  by (auto simp: fun_eq_iff bind_def return_def
           split: tmres.splits)

text \<open>@{term bind} is associative\<close>
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


section \<open>Adding Exceptions\<close>

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
  to return an exceptional value.\<close>
definition returnOk :: "'a \<Rightarrow> ('s, 'e + 'a) tmonad" where
  "returnOk \<equiv> return o Inr"

definition throwError :: "'e \<Rightarrow> ('s, 'e + 'a) tmonad" where
  "throwError \<equiv> return o Inl"

text \<open>
  Lifting a function over the exception type: if the input is an
  exception, return that exception; otherwise continue execution.\<close>
definition lift :: "('a \<Rightarrow> ('s, 'e + 'b) tmonad) \<Rightarrow> 'e +'a \<Rightarrow> ('s, 'e + 'b) tmonad" where
  "lift f v \<equiv> case v of Inl e \<Rightarrow> throwError e | Inr v' \<Rightarrow> f v'"

text \<open>
  The definition of @{term bind} in the exception monad (new
  name @{text bindE}): the same as normal @{term bind}, but
  the right-hand side is skipped if the left-hand side
  produced an exception.\<close>
definition bindE ::
  "('s, 'e + 'a) tmonad \<Rightarrow> ('a \<Rightarrow> ('s, 'e + 'b) tmonad) \<Rightarrow> ('s, 'e + 'b) tmonad" (infixl ">>=E" 60)
  where
  "f >>=E g \<equiv> f >>= lift g"

text \<open>
  Lifting a normal nondeterministic monad into the
  exception monad is achieved by always returning its
  result as normal result and never throwing an exception.\<close>
definition liftE :: "('s,'a) tmonad \<Rightarrow> ('s, 'e+'a) tmonad" where
  "liftE f \<equiv> f >>= (\<lambda>r. return (Inr r))"

text \<open>
  Since the underlying type and @{text return} function changed,
  we need new definitions for when and unless:\<close>
definition whenE :: "bool \<Rightarrow> ('s, 'e + unit) tmonad \<Rightarrow> ('s, 'e + unit) tmonad" where
  "whenE P f \<equiv> if P then f else returnOk ()"

definition unlessE :: "bool \<Rightarrow> ('s, 'e + unit) tmonad \<Rightarrow> ('s, 'e + unit) tmonad" where
  "unlessE P f \<equiv> if P then returnOk () else f"

text \<open>
  Throwing an exception when the parameter is @{term None}, otherwise
  returning @{term "v"} for @{term "Some v"}.\<close>
definition throw_opt :: "'e \<Rightarrow> 'a option \<Rightarrow> ('s, 'e + 'a) tmonad" where
  "throw_opt ex x \<equiv> case x of None \<Rightarrow> throwError ex | Some v \<Rightarrow> returnOk v"

text \<open>
  Failure in the exception monad is redefined in the same way
  as @{const whenE} and @{const unlessE}, with @{term returnOk}
  instead of @{term return}.\<close>
definition assertE :: "bool \<Rightarrow> ('a, 'e + unit) tmonad" where
  "assertE P \<equiv> if P then returnOk () else fail"


subsection "Monad Laws for the Exception Monad"

text \<open>More direct definition of @{const liftE}:\<close>
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

subsection "Syntax for the Interference Trace Monad"

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


subsection "Interference command"

text \<open>
  Interference commands must be inserted in between actions that can be interfered with by
  commands running in other threads.\<close>

definition last_st_tr :: "(tmid * 's) list \<Rightarrow> 's \<Rightarrow> 's" where
  "last_st_tr tr s0 \<equiv> hd (map snd tr @ [s0])"

lemma last_st_tr_simps[simp]:
  "last_st_tr [] s = s"
  "last_st_tr (x # xs) s = snd x"
  "last_st_tr (tr @ tr') s = last_st_tr tr (last_st_tr tr' s)"
  by (simp add: last_st_tr_def hd_append)+

text \<open>Nondeterministically add all possible environment events to the trace.\<close>
definition env_steps :: "('s,unit) tmonad" where
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

text \<open>Add the current state to the trace, tagged as a self action.\<close>
definition commit_step :: "('s,unit) tmonad" where
  "commit_step \<equiv>
   do
     s \<leftarrow> get;
     put_trace [(Me,s)]
   od"

text \<open>
  Record the action taken by the current thread since the last interference point and
  then add unfiltered environment events.\<close>
definition interference :: "('s,unit) tmonad" where
  "interference \<equiv>
   do
     commit_step;
     env_steps
   od"


section "Library of additional Monadic Functions and Combinators"

text \<open>Lifting a normal function into the monad type:\<close>
definition liftM :: "('a \<Rightarrow> 'b) \<Rightarrow> ('s,'a) tmonad \<Rightarrow> ('s, 'b) tmonad" where
  "liftM f m \<equiv> do x \<leftarrow> m; return (f x) od"

text \<open>The same for the exception monad:\<close>
definition liftME :: "('a \<Rightarrow> 'b) \<Rightarrow> ('s,'e+'a) tmonad \<Rightarrow> ('s,'e+'b) tmonad" where
  "liftME f m \<equiv> doE x \<leftarrow> m; returnOk (f x) odE"

text \<open>Execute @{term f} for @{term "Some x"}, otherwise do nothing.\<close>
definition maybeM :: "('a \<Rightarrow> ('s, unit) tmonad) \<Rightarrow> 'a option \<Rightarrow> ('s, unit) tmonad" where
  "maybeM f y \<equiv> case y of Some x \<Rightarrow> f x | None \<Rightarrow> return ()"

text \<open>Run a sequence of monads from left to right, ignoring return values.\<close>
definition sequence_x :: "('s, 'a) tmonad list \<Rightarrow> ('s, unit) tmonad" where
  "sequence_x xs \<equiv> foldr (\<lambda>x y. x >>= (\<lambda>_. y)) xs (return ())"

text \<open>
  Map a monadic function over a list by applying it to each element
  of the list from left to right, ignoring return values.\<close>
definition mapM_x :: "('a \<Rightarrow> ('s,'b) tmonad) \<Rightarrow> 'a list \<Rightarrow> ('s, unit) tmonad" where
  "mapM_x f xs \<equiv> sequence_x (map f xs)"

text \<open>
  Map a monadic function with two parameters over two lists,
  going through both lists simultaneously, left to right, ignoring
  return values.\<close>
definition zipWithM_x ::
  "('a \<Rightarrow> 'b \<Rightarrow> ('s,'c) tmonad) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> ('s, unit) tmonad"
  where
  "zipWithM_x f xs ys \<equiv> sequence_x (zipWith f xs ys)"

text \<open>
  The same three functions as above, but returning a list of
  return values instead of @{text unit}\<close>
definition sequence :: "('s, 'a) tmonad list \<Rightarrow> ('s, 'a list) tmonad" where
  "sequence xs \<equiv> let mcons = (\<lambda>p q. p >>= (\<lambda>x. q >>= (\<lambda>y. return (x#y))))
                 in foldr mcons xs (return [])"

definition mapM :: "('a \<Rightarrow> ('s,'b) tmonad) \<Rightarrow> 'a list \<Rightarrow> ('s, 'b list) tmonad" where
  "mapM f xs \<equiv> sequence (map f xs)"

definition zipWithM ::
  "('a \<Rightarrow> 'b \<Rightarrow> ('s,'c) tmonad) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> ('s, 'c list) tmonad"
  where
  "zipWithM f xs ys \<equiv> sequence (zipWith f xs ys)"

definition foldM :: "('b \<Rightarrow> 'a \<Rightarrow> ('s, 'a) tmonad) \<Rightarrow> 'b list \<Rightarrow> 'a \<Rightarrow> ('s, 'a) tmonad" where
  "foldM m xs a \<equiv> foldr (\<lambda>p q. q >>= m p) xs (return a) "

definition foldME ::
  "('b \<Rightarrow> 'a \<Rightarrow> ('s,('e + 'b)) tmonad) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> ('s, ('e + 'b)) tmonad"
  where
  "foldME m a xs \<equiv> foldr (\<lambda>p q. q >>=E swp m p) xs (returnOk a)"

text \<open>
  The sequence and map functions above for the exception monad, with and without
  lists of return value\<close>
definition sequenceE_x :: "('s, 'e+'a) tmonad list \<Rightarrow> ('s, 'e+unit) tmonad" where
  "sequenceE_x xs \<equiv> foldr (\<lambda>x y. doE _ <- x; y odE) xs (returnOk ())"

definition mapME_x :: "('a \<Rightarrow> ('s,'e+'b) tmonad) \<Rightarrow> 'a list \<Rightarrow> ('s,'e+unit) tmonad" where
  "mapME_x f xs \<equiv> sequenceE_x (map f xs)"

definition sequenceE :: "('s, 'e+'a) tmonad list \<Rightarrow> ('s, 'e+'a list) tmonad" where
  "sequenceE xs \<equiv> let mcons = (\<lambda>p q. p >>=E (\<lambda>x. q >>=E (\<lambda>y. returnOk (x#y))))
                   in foldr mcons xs (returnOk [])"

definition mapME :: "('a \<Rightarrow> ('s,'e+'b) tmonad) \<Rightarrow> 'a list \<Rightarrow> ('s,'e+'b list) tmonad" where
  "mapME f xs \<equiv> sequenceE (map f xs)"

text \<open>Filtering a list using a monadic function as predicate:\<close>
primrec filterM :: "('a \<Rightarrow> ('s, bool) tmonad) \<Rightarrow> 'a list \<Rightarrow> ('s, 'a list) tmonad" where
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
                            put_def bind_def fun_eq_iff default_elem_def
                    intro!: eq_reflection)
  apply fastforce
  done


section "Catching and Handling Exceptions"

text \<open>
  Turning an exception monad into a normal state monad
  by catching and handling any potential exceptions:\<close>
definition catch ::
  "('s, 'e + 'a) tmonad \<Rightarrow> ('e \<Rightarrow> ('s, 'a) tmonad) \<Rightarrow> ('s, 'a) tmonad" (infix "<catch>" 10)
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
  the left side.\<close>
definition handleE' ::
  "('s, 'e1 + 'a) tmonad \<Rightarrow> ('e1 \<Rightarrow> ('s, 'e2 + 'a) tmonad) \<Rightarrow> ('s, 'e2 + 'a) tmonad"
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
  practice: the exception handle (potentially) throws exception
  of the same type as the left-hand side.\<close>
definition handleE ::
  "('s, 'x + 'a) tmonad \<Rightarrow> ('x \<Rightarrow> ('s, 'x + 'a) tmonad) \<Rightarrow> ('s, 'x + 'a) tmonad" (infix "<handle>" 10)
  where
  "handleE \<equiv> handleE'"

text \<open>
  Handling exceptions, and additionally providing a continuation
  if the left-hand side throws no exception:\<close>
definition handle_elseE ::
  "('s, 'e + 'a) tmonad \<Rightarrow> ('e \<Rightarrow> ('s, 'ee + 'b) tmonad) \<Rightarrow> ('a \<Rightarrow> ('s, 'ee + 'b) tmonad) \<Rightarrow>
   ('s, 'ee + 'b) tmonad" ("_ <handle> _ <else> _" 10)
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
FIXME: update comment about non-termination\<close>

inductive_set whileLoop_results ::
  "('r \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('r \<Rightarrow> ('s, 'r) tmonad) \<Rightarrow> (('r \<times> 's) \<times> ((tmid \<times> 's) list \<times> ('s, 'r) tmres)) set"
  for C B where
    "\<lbrakk> \<not> C r s \<rbrakk> \<Longrightarrow> ((r, s), ([], Result (r, s))) \<in> whileLoop_results C B"
  | "\<lbrakk> C r s; (ts, Failed) \<in> B r s \<rbrakk> \<Longrightarrow> ((r, s), (ts, Failed)) \<in> whileLoop_results C B"
  | "\<lbrakk> C r s; (ts, Incomplete) \<in> B r s \<rbrakk> \<Longrightarrow> ((r, s), (ts, Incomplete)) \<in> whileLoop_results C B"
  | "\<lbrakk> C r s; (ts, Result (r', s')) \<in> B r s; ((r', s'), (ts',z)) \<in> whileLoop_results C B; ts''=ts'@ts \<rbrakk>
       \<Longrightarrow> ((r, s), (ts'',z)) \<in> whileLoop_results C B"

\<comment> \<open>FIXME: there are fewer lemmas here than in NonDetMonad and I don't understand this well enough
  to know whether this is correct or not.\<close>
inductive_cases whileLoop_results_cases_result_end: "((x,y), ([],Result r)) \<in> whileLoop_results C B"
inductive_cases whileLoop_results_cases_fail: "((x,y), (ts, Failed)) \<in> whileLoop_results C B"
inductive_cases whileLoop_results_cases_incomplete: "((x,y), (ts, Incomplete)) \<in> whileLoop_results C B"

inductive_simps whileLoop_results_simps_valid: "((x,y), ([], Result z)) \<in> whileLoop_results C B"

inductive whileLoop_terminates ::
  "('r \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('r \<Rightarrow> ('s, 'r) tmonad) \<Rightarrow> 'r \<Rightarrow> 's \<Rightarrow> bool"
  for C B where
    "\<not> C r s \<Longrightarrow> whileLoop_terminates C B r s"
  | "\<lbrakk> C r s; \<forall>(r', s') \<in> Result -` snd ` (B r s). whileLoop_terminates C B r' s' \<rbrakk>
        \<Longrightarrow> whileLoop_terminates C B r s"

inductive_cases whileLoop_terminates_cases: "whileLoop_terminates C B r s"
inductive_simps whileLoop_terminates_simps: "whileLoop_terminates C B r s"

definition whileLoop ::
  "('r \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('r \<Rightarrow> ('s, 'r) tmonad) \<Rightarrow> 'r \<Rightarrow> ('s, 'r) tmonad"
  where
  "whileLoop C B \<equiv> (\<lambda>r s. {(ts, res). ((r,s), ts,res) \<in> whileLoop_results C B})"

notation (output)
  whileLoop  ("(whileLoop (_)//  (_))" [1000, 1000] 1000)

\<comment> \<open>FIXME: why does this differ to @{text Nondet_Monad}?\<close>
definition whileLoopT ::
  "('r \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('r \<Rightarrow> ('s, 'r) tmonad) \<Rightarrow> 'r \<Rightarrow> ('s, 'r) tmonad"
  where
  "whileLoopT C B \<equiv> (\<lambda>r s. {(ts, res). ((r,s), ts,res) \<in> whileLoop_results C B
                                         \<and> whileLoop_terminates C B r s})"

notation (output)
  whileLoopT  ("(whileLoopT (_)//  (_))" [1000, 1000] 1000)

definition whileLoopE ::
  "('r \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('r \<Rightarrow> ('s, 'e + 'r) tmonad) \<Rightarrow> 'r \<Rightarrow> ('s, ('e + 'r)) tmonad"
  where
  "whileLoopE C body \<equiv>
      \<lambda>r. whileLoop (\<lambda>r s. (case r of Inr v \<Rightarrow> C v s | _ \<Rightarrow> False)) (lift body) (Inr r)"

notation (output)
  whileLoopE  ("(whileLoopE (_)//  (_))" [1000, 1000] 1000)


section "Combinators that have conditions with side effects"

definition notM :: "('s, bool) tmonad \<Rightarrow> ('s, bool) tmonad" where
  "notM m = do c \<leftarrow> m; return (\<not> c) od"

definition whileM :: "('s, bool) tmonad \<Rightarrow> ('s, 'a) tmonad \<Rightarrow> ('s, unit) tmonad" where
  "whileM C B \<equiv> do
    c \<leftarrow> C;
    whileLoop (\<lambda>c s. c) (\<lambda>_. do B; C od) c;
    return ()
  od"

definition ifM :: "('s, bool) tmonad \<Rightarrow> ('s, 'a) tmonad \<Rightarrow> ('s, 'a) tmonad \<Rightarrow> ('s, 'a) tmonad" where
  "ifM test t f = do
    c \<leftarrow> test;
    if c then t else f
   od"

definition ifME ::
  "('a, 'b + bool) tmonad \<Rightarrow> ('a, 'b + 'c) tmonad \<Rightarrow> ('a, 'b + 'c) tmonad \<Rightarrow> ('a, 'b + 'c) tmonad"
  where
  "ifME test t f = doE
    c \<leftarrow> test;
    if c then t else f
   odE"

definition whenM :: "('s, bool) tmonad \<Rightarrow> ('s, unit) tmonad \<Rightarrow> ('s, unit) tmonad" where
  "whenM t m = ifM t m (return ())"

definition orM :: "('s, bool) tmonad \<Rightarrow> ('s, bool) tmonad \<Rightarrow> ('s, bool) tmonad" where
  "orM a b = ifM a (return True) b"

definition andM :: "('s, bool) tmonad \<Rightarrow> ('s, bool) tmonad \<Rightarrow> ('s, bool) tmonad" where
  "andM a b = ifM a b (return False)"


section "Await command"

text \<open>@{term "Await c f"} blocks the execution until @{term "c"} is true,
      and then atomically executes @{term "f"}.\<close>
definition Await :: "('s \<Rightarrow> bool) \<Rightarrow> ('s,unit) tmonad" where
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


section "Parallel combinator"

definition parallel :: "('s,'a) tmonad \<Rightarrow> ('s,'a) tmonad \<Rightarrow> ('s,'a) tmonad" where
  "parallel f g = (\<lambda>s. {(xs, rv). \<exists>f_steps. length f_steps = length xs
    \<and> (map (\<lambda>(f_step, (id, s)). (if f_step then id else Env, s)) (zip f_steps xs), rv) \<in> f s
    \<and> (map (\<lambda>(f_step, (id, s)). (if f_step then Env else id, s)) (zip f_steps xs), rv) \<in> g s})"

abbreviation(input)
  "parallel_mrg \<equiv> \<lambda>((idn, s), (idn', _)). (if idn = Env then idn' else idn, s)"

lemma parallel_def2:
  "parallel f g = (\<lambda>s. {(xs, rv). \<exists>ys zs. (ys, rv) \<in> f s \<and> (zs, rv) \<in> g s
    \<and> list_all2 (\<lambda>y z. (fst y = Env \<or> fst z = Env) \<and> snd y = snd z) ys zs
    \<and> xs = map parallel_mrg (zip ys zs)})"
  apply (simp add: parallel_def fun_eq_iff set_eq_iff)
  apply safe
   apply (rule exI, rule conjI, assumption)+
   apply (simp add: list_all2_conv_all_nth list_eq_iff_nth_eq split_def prod_eq_iff)
   apply clarsimp
  apply (rename_tac ys zs)
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

end
