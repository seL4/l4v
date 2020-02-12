(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(*
  The state and error monads in Isabelle,
*)

chapter "Monads"

theory StateMonad (* FIXME: untested/unused *)
imports Lib
begin

type_synonym ('s,'a) state_monad = "'s \<Rightarrow> 'a \<times> 's"

definition
  runState :: "('s,'a) state_monad \<Rightarrow> 's \<Rightarrow> 'a \<times> 's"
where
  "runState \<equiv> id"

definition
  "return a \<equiv> \<lambda>s. (a,s)"

definition
  bind :: "('s, 'a) state_monad \<Rightarrow> ('a \<Rightarrow> ('s, 'b) state_monad) \<Rightarrow>
           ('s, 'b) state_monad" (infixl ">>=" 60)
where
  "bind f g \<equiv> (\<lambda>s. let (v,s') = f s in (g v) s')"

definition
  "bind' f g \<equiv> bind f (\<lambda>_. g)"

declare bind'_def [iff]


definition
  "get \<equiv> \<lambda>s. (s,s)"

definition
  "put s \<equiv> \<lambda>_. ((),s)"

definition
  "gets f \<equiv> get >>= (\<lambda>s. return $ f s)"

definition
  "modify f \<equiv> get >>= (\<lambda>s. put $ f s)"

definition
  "when p s \<equiv> if p then s else return ()"

definition
  "unless p s \<equiv> when (\<not>p) s"


text \<open>The monad laws:\<close>

lemma return_bind [simp]: "(return x >>= f) = f x"
  by (simp add: return_def bind_def runState_def)

lemma bind_return [simp]: "(m >>= return) = m"
  unfolding bind_def return_def runState_def
  by (simp add: Let_def split_def)

lemma bind_assoc:
  fixes m :: "('s,'a) state_monad"
  fixes f :: "'a \<Rightarrow> ('s,'b) state_monad"
  fixes g :: "'b \<Rightarrow> ('s,'c) state_monad"
  shows "(m >>= f) >>= g  =  m >>= (\<lambda>x. f x >>= g)"
  unfolding bind_def
  by (clarsimp simp add: Let_def split_def)


text \<open>An errorT state\_monad (returnOk=return, bindE=bind):\<close>

definition
  "returnOk \<equiv> return o Inr"

definition
  "throwError \<equiv> return o Inl"

definition
  "Ok \<equiv> Inr"

definition
  lift :: "('a \<Rightarrow> ('s, 'e + 'b) state_monad) \<Rightarrow> 'e+'a \<Rightarrow> ('s, 'e + 'b) state_monad"
where
  "lift f v \<equiv> case v of Inl e \<Rightarrow> throwError e | Inr v' \<Rightarrow> f v'"

definition
  lift2 :: "('c \<Rightarrow> ('a, 'b + 'e + 'd) state_monad) \<Rightarrow> 'b+'e+'c \<Rightarrow> ('a, 'b+'e+'d) state_monad"
where
  "lift2 f v \<equiv> case v of
                 Inl e \<Rightarrow> throwError e
               | Inr v'' \<Rightarrow> (case v'' of Inl e' \<Rightarrow> return $ Inr $ Inl e' | Inr v' \<Rightarrow> f v')"

(* This is used if you are just trying to throwError by itself *)
definition
  raise :: "'a \<Rightarrow> 's \<Rightarrow> ('a + unit) \<times> 's"
where
  "raise \<equiv> return \<circ> Inl"

definition
  bindE :: "('s, 'e + 'a) state_monad \<Rightarrow> ('a \<Rightarrow> ('s, 'e + 'b) state_monad) \<Rightarrow>
            ('s, 'e + 'b) state_monad"  (infixl ">>=E" 60)
where
  "bindE f g \<equiv> bind f (lift g)"


definition
  "bindE' f g \<equiv> bindE f (\<lambda>_. g)"

definition
  liftE :: "('s,'a) state_monad \<Rightarrow> ('s, 'e+'a) state_monad" where
  "liftE f \<equiv> \<lambda>s. let (v,s') = f s in (Inr v, s')"

definition
  "whenE P f \<equiv> if P then f else returnOk ()"

definition
  "unlessE P f \<equiv> if P then returnOk () else f"

definition
  "throw_opt ex x \<equiv> case x of None \<Rightarrow> throwError ex | Some v \<Rightarrow> returnOk v"

definition
  "bindEE f g \<equiv> bind f (lift2 g)"
definition
  "bindEE' f g \<equiv> bindEE f (\<lambda>_. g)"

definition
  "modifyE \<equiv> (liftE \<circ> modify)"
definition
  "getsE x \<equiv> liftE $ gets x"

syntax
  bindEE :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixl ">>=EE" 60)

declare
  bindE'_def [iff]
  bindEE_def [iff]
  bindEE'_def [iff]

lemma returnOk_bindE [simp]: "(returnOk x >>=E f) = f x"
  unfolding bindE_def return_def returnOk_def
  by (clarsimp simp: lift_def bind_def)

lemma lift_return [simp]:
  "lift (return \<circ> Inr) = return"
  by (auto simp: lift_def throwError_def split: sum.splits)

lemma bindE_returnOk [simp]: "(m >>=E returnOk) = m"
  by (simp add: bindE_def returnOk_def)

 lemma bindE_assoc:
  shows "(m >>=E f) >>=E g  =  m >>=E (\<lambda>x. f x >>=E g)"
  by (auto simp: Let_def bindE_def bind_def lift_def split_def runState_def throwError_def return_def
           split: sum.splits)

lemma throwError_bindE [simp]:
  "throwError E >>=E f = throwError E"
  by (simp add: bindE_def bind_def throwError_def lift_def return_def)


subsection "Syntax for state monad"


nonterminal
  dobinds and dobind and nobind

syntax
  "_dobind"    :: "[pttrn, 'a] => dobind"             ("(_ <-/ _)" 10)
  ""           :: "dobind => dobinds"                 ("_")
  "_nobind"    :: "'a => dobind"                      ("_")
  "_dobinds"   :: "[dobind, dobinds] => dobinds"      ("(_);//(_)")

  "_do"        :: "[dobinds, 'a] => 'a"               ("(do (_);//   (_)//od)" 100)
syntax (xsymbols)
  "_dobind"    :: "[pttrn, 'a] => dobind"             ("(_ \<leftarrow>/ _)" 10)


translations
  "_do (_dobinds b bs) e"  == "_do b (_do bs e)"
  "_do (_nobind b) e"      == "CONST bind' b e"
  "do x <- a; e od"        == "a >>= (\<lambda>x. e)"

lemma "do x \<leftarrow> return 1; return 2; return x od = return 1"
  by simp


subsection "Syntax for errorT state monad"


syntax
  "_doE" :: "[dobinds, 'a] => 'a"  ("(doE (_);//    (_)//odE)" 100)

translations
  "_doE (_dobinds b bs) e"  == "_doE b (_doE bs e)"
  "_doE (_nobind b) e"      == "CONST bindE' b e"
  "doE x <- a; e odE"       == "a >>=E (\<lambda>x. e)"


subsection "Syntax for errorT errorT state monad"

syntax
  "_doEE" :: "[dobinds, 'a] => 'a" ("(doEE (_);//     (_)//odEE)" 100)

translations
  "_doEE (_dobinds b bs) e"  == "_doEE b (_doEE bs e)"
  "_doEE (_nobind b) e"      == "CONST bindEE' b e"
  "doEE x <- a; e odEE"      == "a >>=EE (\<lambda>x. e)"

primrec
  inc_forloop :: "nat \<Rightarrow> 'g::{plus,one} \<Rightarrow> ('g \<Rightarrow> ('a, 'b + unit) state_monad) \<Rightarrow>
                  ('a, 'b + unit) state_monad"
where
  "inc_forloop 0 current body = returnOk ()"
| "inc_forloop (Suc left) current body = doE body current ; inc_forloop left (current+1) body odE"

primrec
  do_times :: "nat \<Rightarrow> ('a, 'b + unit) state_monad \<Rightarrow> ('a, 'b + unit) state_monad \<Rightarrow>
              ('a, 'b + unit) state_monad"
where
  "do_times 0 body increment = returnOk ()"
| "do_times (Suc left) body increment = doE body ; increment ; do_times left body increment odE"

definition
  function_update :: "'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)" where
  "function_update index modifier f \<equiv>
   \<lambda>x. if x = index then modifier (f x) else (f x)"

lemma "doE x \<leftarrow> returnOk 1; returnOk 2; returnOk x odE = returnOk 1"
  by simp

term "doEE x \<leftarrow> returnOk $ Ok 1; returnOk $ Ok 2; returnOk $ Ok x odEE"

definition
  "skip \<equiv> returnOk $ Ok ()"

definition
  "liftM f m \<equiv> do x \<leftarrow> m; return (f x) od"
definition
  "liftME f m \<equiv> doE x \<leftarrow> m; returnOk (f x) odE"

definition
  "sequence_x xs \<equiv> foldr (\<lambda>x y. x >>= (\<lambda>_. y)) xs (return ())"

definition
  "zipWithM_x f xs ys \<equiv> sequence_x (zipWith f xs ys)"
definition
  "mapM_x f xs \<equiv> sequence_x (map f xs)"

definition
  "sequence xs \<equiv> let mcons = (\<lambda>p q. p >>= (\<lambda>x. q >>= (\<lambda>y. return (x#y))))
                 in foldr mcons xs (return [])"

definition
  "mapM f xs \<equiv> sequence (map f xs)"

definition
  "sequenceE_x xs \<equiv> foldr (\<lambda>x y. doE uu <- x; y odE) xs (returnOk ())"
definition
  "mapME_x f xs \<equiv> sequenceE_x (map f xs)"

definition
  "sequenceEE_x xs \<equiv> foldr bindEE' xs (skip)"
definition
  "mapMEE_x f xs \<equiv> sequenceEE_x (map f xs)"

definition
  catch :: "('s, 'a + 'b) state_monad \<Rightarrow> ('a \<Rightarrow> ('s, 'b) state_monad) \<Rightarrow> ('s, 'b) state_monad"
where
  "catch f handler \<equiv> do x \<leftarrow> f;
                        case x of
                            Inr b \<Rightarrow> return b
                          | Inl e \<Rightarrow> handler e
                      od"

definition
  handleE :: "('s, 'x + 'a) state_monad \<Rightarrow>
              ('x \<Rightarrow> ('s, 'x + 'a) state_monad) \<Rightarrow>
              ('s, 'x + 'a) state_monad" (infix "<handle>" 11) where
  "f <handle> handler \<equiv>
   do v \<leftarrow> f; case v of Inl e \<Rightarrow> handler e | Inr v' \<Rightarrow> return v od"

definition
  handle_elseE :: "('s, 'x + 'a) state_monad \<Rightarrow>
                   ('x \<Rightarrow> ('s, 'x + 'a) state_monad) \<Rightarrow>
                   ('a \<Rightarrow> ('s, 'x + 'a) state_monad) \<Rightarrow>
                   ('s, 'x + 'a) state_monad" ("_ <handle> _ <else> _" 10)
where
  "f <handle> handler <else> continue \<equiv>
    do v \<leftarrow> f;
       case v of Inl e \<Rightarrow> handler e
               | Inr v \<Rightarrow> continue v
    od"

definition
  isSkip :: "('s, 'a) state_monad \<Rightarrow> bool" where
  "isSkip m \<equiv> \<forall>s. \<exists>r. m s = (r,s)"

lemma isSkip_bindI: "\<lbrakk> isSkip f; \<And>x. isSkip (g x) \<rbrakk> \<Longrightarrow> isSkip (f >>= g)"
  apply (clarsimp simp: isSkip_def bind_def Let_def)
  apply (erule_tac x=s in allE)
  apply clarsimp
  done

lemma isSkip_return [simp,intro!]:
  "isSkip (return x)"
  by (simp add: isSkip_def return_def)

lemma isSkip_gets [simp,intro!]:
  "isSkip (gets x)"
  by (simp add: isSkip_def gets_def get_def bind_def return_def)

lemma isSkip_liftE [iff]: "isSkip (liftE f) = isSkip f"
  apply (simp add: isSkip_def liftE_def Let_def split_def)
  apply rule
   apply clarsimp
   apply (case_tac "f s")
   apply (erule_tac x = s in allE)
   apply simp
  apply clarsimp
  apply (case_tac "f s")
  apply (erule_tac x = s in allE)
  apply simp
  done

lemma isSkip_liftI [simp, intro!]:
  "\<lbrakk> \<And>y. x = Inr y \<Longrightarrow> isSkip (f y) \<rbrakk> \<Longrightarrow> isSkip (lift f x)"
  by (simp add: lift_def throwError_def return_def isSkip_def split: sum.splits)

lemma isSkip_Error [iff]:
  "isSkip (throwError x)"
  by (simp add: throwError_def)

lemma isSkip_returnOk [iff]:
  "isSkip (returnOk x)"
  by (simp add: returnOk_def)

lemma isSkip_throw_opt [iff]:
  "isSkip (throw_opt e x)"
  by (simp add: throw_opt_def split: option.splits)

lemma nested_bind [simp]:
  "do x <- do y <- f; return (g y) od; h x od =
   do y <- f; h (g y) od"
  apply (clarsimp simp add: bind_def)
  apply (rule ext)
  apply (clarsimp simp add: Let_def split_def runState_def return_def)
  done

lemma skip_bind:
  "isSkip s \<Longrightarrow> do _ \<leftarrow> s; g od = g"
  apply (clarsimp simp add: bind_def)
  apply (rule ext)
  apply (clarsimp simp add: isSkip_def Let_def)
  apply (erule_tac x=sa in allE)
  apply clarsimp
  done

lemma bind_eqI:
  "\<lbrakk> f = f'; \<And>x. g x = g' x \<rbrakk> \<Longrightarrow> f >>= g = f' >>= g'"
  by (simp add: bind_def)

lemma bind_cong [fundef_cong]:
  "\<lbrakk> f = f'; \<And>v s s'. f' s = (v, s') \<Longrightarrow> g v s' = g' v s' \<rbrakk> \<Longrightarrow> f >>= g = f' >>= g'"
  by (simp add: bind_def Let_def split_def)

lemma bind'_cong [fundef_cong]:
  "\<lbrakk> f = f'; \<And>v s s'. f' s = (v, s') \<Longrightarrow> g s' = g' s' \<rbrakk> \<Longrightarrow> bind' f g = bind' f' g'"
  by (auto intro: bind_cong)

lemma bindE_cong[fundef_cong]:
  "\<lbrakk> M = M' ; \<And>v s s'. M' s = (Inr v, s') \<Longrightarrow> N v s' = N' v s' \<rbrakk> \<Longrightarrow> bindE M N = bindE M' N'"
  apply (simp add: bindE_def)
  apply (rule bind_cong)
   apply (rule refl)
  apply (unfold lift_def)
  apply (case_tac v, simp_all)
  done

lemma bindE'_cong[fundef_cong]:
  "\<lbrakk> M = M' ; \<And>v s s'. M' s = (Inr v, s') \<Longrightarrow> N s' = N' s' \<rbrakk> \<Longrightarrow> bindE' M N = bindE' M' N'"
  by (auto intro: bindE_cong)

definition
  valid :: "('s \<Rightarrow> bool) \<Rightarrow> ('s,'a) state_monad \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool" ("\<lbrace>_\<rbrace> _ \<lbrace>_\<rbrace>") where
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<equiv> \<forall>s. P s \<longrightarrow> split Q (f s)"

definition
  validE :: "('s \<Rightarrow> bool) \<Rightarrow> ('s, 'a + 'b) state_monad \<Rightarrow> ('b \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
             ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool" ("\<lbrace>_\<rbrace> _ \<lbrace>_\<rbrace>, \<lbrace>_\<rbrace>") where
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>R\<rbrace> \<equiv> \<forall>s. P s \<longrightarrow> split (\<lambda>r s. case r of Inr b \<Rightarrow> Q b s
                                                  | Inl a \<Rightarrow> R a s) (f s)"

lemma validE_def2:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>R\<rbrace> \<equiv> \<lbrace>P\<rbrace> f \<lbrace> \<lambda>r s. case r of Inr b \<Rightarrow> Q b s | Inl a \<Rightarrow> R a s \<rbrace>"
  by (unfold valid_def validE_def)

(* FIXME: modernize *)
syntax top :: "'a \<Rightarrow> bool" ("\<top>")
       bottom :: "'a \<Rightarrow> bool" ("\<bottom>")

translations
  "\<top>" == "\<lambda>_. CONST True"
  "\<bottom>" == "\<lambda>_. CONST False"

definition
  bipred_conj :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)" (infixl "And" 96)
where
  "bipred_conj P Q \<equiv> \<lambda>x y. P x y \<and> Q x y"

definition
  bipred_disj :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)" (infixl "Or" 91)
where
  "bipred_disj P Q \<equiv> \<lambda>x y. P x y \<or> Q x y"

definition
  bipred_neg :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)" ("Not _") where
  "bipred_neg P \<equiv> \<lambda>x y. \<not> P x y"

syntax toptop :: "'a \<Rightarrow> 'b \<Rightarrow> bool" ("\<top>\<top>")
       botbot :: "'a \<Rightarrow> 'b \<Rightarrow> bool" ("\<bottom>\<bottom>")

translations "\<top>\<top>" == "\<lambda>_ _. CONST True"
             "\<bottom>\<bottom>" == "\<lambda>_ _. CONST False"

definition
  pred_lift_exact :: "('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)" ("\<guillemotleft>_,_\<guillemotright>") where
  "pred_lift_exact P Q \<equiv> \<lambda>x y. P x \<and> Q y"

lemma pred_lift_taut[simp]: "\<guillemotleft>\<top>,\<top>\<guillemotright> = \<top>\<top>"
  by (simp add:pred_lift_exact_def)

lemma pred_lift_cont_l[simp]: "\<guillemotleft>\<bottom>,x\<guillemotright> = \<bottom>\<bottom>"
  by (simp add:pred_lift_exact_def)

lemma pred_lift_cont_r[simp]: "\<guillemotleft>x,\<bottom>\<guillemotright> = \<bottom>\<bottom>"
  by (simp add:pred_lift_exact_def)

lemma pred_liftI[intro!]: "\<lbrakk> P x; Q y \<rbrakk> \<Longrightarrow> \<guillemotleft>P,Q\<guillemotright> x y"
  by (simp add:pred_lift_exact_def)

lemma pred_exact_split:
  "\<guillemotleft>P,Q\<guillemotright> = (\<guillemotleft>P,\<top>\<guillemotright> And \<guillemotleft>\<top>,Q\<guillemotright>)"
  by (simp add:pred_lift_exact_def bipred_conj_def)

lemma pred_andE[elim!]: "\<lbrakk> (A and B) x; \<lbrakk> A x; B x \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by (simp add:pred_conj_def)

lemma pred_andI[intro!]: "\<lbrakk> A x; B x \<rbrakk> \<Longrightarrow> (A and B) x"
  by (simp add:pred_conj_def)

lemma bipred_conj_app[simp]: "(P And Q) x = (P x and Q x)"
  by (simp add:pred_conj_def bipred_conj_def)

lemma bipred_disj_app[simp]: "(P Or Q) x = (P x or Q x)"
  by (simp add:pred_disj_def bipred_disj_def)

lemma pred_conj_app[simp]: "(P and Q) x = (P x \<and> Q x)"
  by (simp add:pred_conj_def)

lemma pred_disj_app[simp]: "(P or Q) x = (P x \<or> Q x)"
  by (simp add:pred_disj_def)

lemma pred_notnotD[simp]: "(not not P) = P"
  by (simp add:pred_neg_def)

lemma bipred_notnotD[simp]: "(Not Not P) = P"
  by (simp add:bipred_neg_def)

lemma pred_lift_add[simp]: "\<guillemotleft>P,Q\<guillemotright> x = ((\<lambda>s. P x) and Q)"
  by (simp add:pred_lift_exact_def pred_conj_def)

lemma pred_and_true[simp]: "(P and \<top>) = P"
  by (simp add:pred_conj_def)

lemma pred_and_true_var[simp]: "(\<top> and P) = P"
  by (simp add:pred_conj_def)

lemma pred_and_false[simp]: "(P and \<bottom>) = \<bottom>"
  by (simp add:pred_conj_def)

lemma pred_and_false_var[simp]: "(\<bottom> and P) = \<bottom>"
  by (simp add:pred_conj_def)

lemma seq':
  "\<lbrakk> \<lbrace>A\<rbrace> f \<lbrace>B\<rbrace>;
     \<forall>x. P x \<longrightarrow> \<lbrace>C\<rbrace> g x \<lbrace>D\<rbrace>;
     \<forall>x s. B x s \<longrightarrow> P x \<and> C s \<rbrakk> \<Longrightarrow>
   \<lbrace>A\<rbrace> do x \<leftarrow> f; g x od \<lbrace>D\<rbrace>"
  apply (clarsimp simp: valid_def runState_def bind_def Let_def split_def)
  apply (case_tac "f s")
  apply fastforce
  done


lemma seq:
  assumes "\<lbrace>A\<rbrace> f \<lbrace>B\<rbrace>"
  assumes "\<And>x. P x \<Longrightarrow> \<lbrace>C\<rbrace> g x \<lbrace>D\<rbrace>"
  assumes "\<And>x s. B x s \<Longrightarrow> P x \<and> C s"
  shows "\<lbrace>A\<rbrace> do x \<leftarrow> f; g x od \<lbrace>D\<rbrace>"
  using assms by (blast intro: seq')

lemma seq_invar_nobind:
  assumes f_valid: "\<lbrace>A\<rbrace> f \<lbrace>\<guillemotleft>\<top>,A\<guillemotright>\<rbrace>"
  assumes g_valid: "\<And>x. \<lbrace>A\<rbrace> g x \<lbrace>\<guillemotleft>\<top>,A\<guillemotright>\<rbrace>"
  shows "\<lbrace>A\<rbrace> do x \<leftarrow> f; g x od \<lbrace>\<guillemotleft>\<top>,A\<guillemotright>\<rbrace>"
  apply(rule_tac B="\<guillemotleft>\<top>,A\<guillemotright>" and C="A" and P="\<top>" in seq)
    apply(insert f_valid g_valid)
    apply(simp_all add:pred_lift_exact_def)
  done

lemma seq_invar_bind:
  assumes f_valid: "\<lbrace>A\<rbrace> f \<lbrace>\<guillemotleft>B,A\<guillemotright>\<rbrace>"
  assumes g_valid: "\<And>x. P x \<Longrightarrow> \<lbrace>A\<rbrace> g x \<lbrace>\<guillemotleft>\<top>,A\<guillemotright>\<rbrace>"
  assumes bind: "\<And>x. B x \<Longrightarrow> P x"
  shows "\<lbrace>A\<rbrace> do x \<leftarrow> f; g x od \<lbrace>\<guillemotleft>\<top>,A\<guillemotright>\<rbrace>"
  apply(rule_tac B="\<guillemotleft>B,A\<guillemotright>" and C="A" and P="P" in seq)
    apply(insert f_valid g_valid bind)
    apply(simp_all add: pred_lift_exact_def)
  done

lemma seq_noimp:
  assumes f_valid: "\<lbrace>A\<rbrace> f \<lbrace>\<guillemotleft>C,B\<guillemotright>\<rbrace>"
  assumes g_valid: "\<And>x. C x \<Longrightarrow> \<lbrace>B\<rbrace> g x \<lbrace>D\<rbrace>"
  shows "\<lbrace>A\<rbrace> do x \<leftarrow> f; g x od \<lbrace>D\<rbrace>"
  apply(rule_tac B="\<guillemotleft>C,B\<guillemotright>" and C="B" and P="C" in seq)
    apply(insert f_valid g_valid, simp_all add:pred_lift_exact_def)
  done

lemma seq_ext':
  "\<lbrakk> \<lbrace>A\<rbrace> f \<lbrace>B\<rbrace>; \<forall>x. \<lbrace>B x\<rbrace> g x \<lbrace>C\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>A\<rbrace> do x \<leftarrow> f; g x od \<lbrace>C\<rbrace>"
  by (clarsimp simp: valid_def runState_def bind_def Let_def split_def)

lemma seq_ext:
  assumes "\<lbrace>A\<rbrace> f \<lbrace>B\<rbrace>" "\<And>x. \<lbrace>B x\<rbrace> g x \<lbrace>C\<rbrace>"
  shows "\<lbrace>A\<rbrace> do x \<leftarrow> f; g x od \<lbrace>C\<rbrace>"
  using assms by (blast intro: seq_ext')

lemma seqE':
  "\<lbrakk> \<lbrace>A\<rbrace> f \<lbrace>B\<rbrace>,\<lbrace>E\<rbrace>;
     \<forall>x. \<lbrace>B x\<rbrace> g x \<lbrace>C\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace>A\<rbrace> doE x \<leftarrow> f; g x odE \<lbrace>C\<rbrace>,\<lbrace>E\<rbrace>"
  apply(simp add: bindE_def lift_def bind_def Let_def split_def)
  apply(clarsimp simp: validE_def)
  apply(rename_tac s r x)
  apply(case_tac "fst (f s)"; case_tac r; fastforce simp:throwError_def return_def)
  done

lemma seqE:
  assumes "\<lbrace>A\<rbrace> f \<lbrace>B\<rbrace>,\<lbrace>E\<rbrace>" "\<And>x. \<lbrace>B x\<rbrace> g x \<lbrace>C\<rbrace>,\<lbrace>E\<rbrace>"
  shows "\<lbrace>A\<rbrace> doE x \<leftarrow> f; g x odE \<lbrace>C\<rbrace>,\<lbrace>E\<rbrace>"
  using assms by(blast intro: seqE')

lemma get_sp:
  "\<lbrace>P\<rbrace> get \<lbrace>\<lambda>a s. s = a \<and> P s\<rbrace>"
  by (simp add:get_def valid_def)

lemma put_sp:
  "\<lbrace>\<top>\<rbrace> put a \<lbrace>\<lambda>_ s. s = a\<rbrace>"
  by (simp add:put_def valid_def)

lemma return_sp:
  "\<lbrace>P\<rbrace> return a \<lbrace>\<lambda>b s. b = a \<and> P s\<rbrace>"
  by (simp add:return_def valid_def)

lemma hoare_post_conj [intro!]:
  "\<lbrakk> \<lbrace> P \<rbrace> a \<lbrace> Q \<rbrace>; \<lbrace> P \<rbrace> a \<lbrace> R \<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace> P \<rbrace> a \<lbrace> Q And R \<rbrace>"
  by (simp add:valid_def split_def bipred_conj_def)

lemma hoare_pre_disj [intro!]:
  "\<lbrakk> \<lbrace> P \<rbrace> a \<lbrace> R \<rbrace>; \<lbrace> Q \<rbrace> a \<lbrace> R \<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace> P or Q \<rbrace> a \<lbrace> R \<rbrace>"
  by (simp add:valid_def pred_disj_def)

lemma hoare_post_taut [iff]: "\<lbrace> P \<rbrace> a \<lbrace> \<top>\<top> \<rbrace>"
  by (simp add:valid_def)

lemma hoare_pre_cont [iff]: "\<lbrace> \<bottom> \<rbrace> a \<lbrace> P \<rbrace>"
  by (simp add:valid_def)

lemma hoare_return [intro!]: "\<And>x. P x \<Longrightarrow> \<lbrace> Q \<rbrace> return x \<lbrace> \<guillemotleft>P,Q\<guillemotright> \<rbrace>"
  by (simp add:valid_def return_def pred_lift_exact_def)

lemma hoare_return_drop [iff]: "\<lbrace> Q \<rbrace> return x \<lbrace> \<guillemotleft>\<top>,Q\<guillemotright> \<rbrace>"
  by (simp add:valid_def return_def pred_lift_exact_def)

lemma hoare_return_drop_var [iff]: "\<lbrace> Q \<rbrace> return x \<lbrace> \<lambda>r. Q \<rbrace>"
  by (simp add:valid_def return_def pred_lift_exact_def)

lemma hoare_return_only [intro!]: "\<And>x. P x \<Longrightarrow> \<lbrace> Q \<rbrace> return x \<lbrace> \<guillemotleft>P,\<top>\<guillemotright> \<rbrace>"
  by (simp add:valid_def return_def pred_lift_exact_def)

lemma hoare_get [iff]: "\<lbrace> P \<rbrace> get \<lbrace> \<guillemotleft>P,P\<guillemotright> \<rbrace>"
  by (simp add:valid_def get_def pred_lift_exact_def)

lemma hoare_gets [intro!]: "\<lbrakk> \<And>s. P s \<Longrightarrow> Q (f s) s \<rbrakk> \<Longrightarrow> \<lbrace> P \<rbrace> gets f \<lbrace> Q \<rbrace>"
  by (simp add:valid_def gets_def get_def bind_def return_def)

lemma hoare_modify [iff]: "\<lbrace> P o f \<rbrace> modify f \<lbrace> \<guillemotleft>\<top>,P\<guillemotright> \<rbrace>"
  by (simp add:valid_def modify_def pred_lift_exact_def put_def bind_def get_def)

lemma hoare_modifyE [intro!]: "\<lbrakk> \<And>s. P s \<Longrightarrow> Q (f s) \<rbrakk> \<Longrightarrow> \<lbrace> P \<rbrace> modify f \<lbrace> \<guillemotleft>\<top>,Q\<guillemotright> \<rbrace>"
  by (simp add:valid_def modify_def pred_lift_exact_def put_def bind_def get_def)

lemma hoare_modifyE_var [intro!]: "\<lbrakk> \<And>s. P s \<Longrightarrow> Q (f s) \<rbrakk> \<Longrightarrow> \<lbrace> P \<rbrace> modify f \<lbrace> \<lambda>r s. Q s \<rbrace>"
  by (simp add:valid_def modify_def pred_lift_exact_def put_def bind_def get_def)

lemma hoare_put [intro!]: "P x \<Longrightarrow> \<lbrace> Q \<rbrace> put x \<lbrace> \<guillemotleft>\<top>,P\<guillemotright>\<rbrace>"
  by (simp add:valid_def put_def pred_lift_exact_def)

lemma hoare_if [intro!]:
  "\<lbrakk> P \<Longrightarrow> \<lbrace> Q \<rbrace> a \<lbrace> R \<rbrace>; \<not> P \<Longrightarrow> \<lbrace> Q \<rbrace> b \<lbrace> R \<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace> Q \<rbrace> if P then a else b \<lbrace> R \<rbrace>"
  by (simp add:valid_def)

lemma hoare_when [intro!]:
  "\<lbrakk> \<lbrakk> P \<rbrakk> \<Longrightarrow> \<lbrace> Q \<rbrace> a \<lbrace> \<guillemotleft>\<top>,R\<guillemotright> \<rbrace>; \<And>s. \<lbrakk> \<not> P; Q s \<rbrakk> \<Longrightarrow> R s \<rbrakk> \<Longrightarrow>
   \<lbrace> Q \<rbrace> when P a \<lbrace> \<guillemotleft>\<top>,R\<guillemotright> \<rbrace>"
  by (simp add:valid_def when_def split_def return_def pred_lift_exact_def)

lemma hoare_unless [intro!]:
  "\<lbrakk> \<And>s. \<lbrakk> P; Q s \<rbrakk> \<Longrightarrow> R s; \<lbrakk> \<not> P \<rbrakk> \<Longrightarrow> \<lbrace> Q \<rbrace> a \<lbrace> \<guillemotleft>\<top>,R\<guillemotright> \<rbrace> \<rbrakk> \<Longrightarrow>
   \<lbrace> Q \<rbrace> unless P a \<lbrace> \<guillemotleft>\<top>,R\<guillemotright> \<rbrace>"
  by (simp add:valid_def unless_def split_def when_def return_def pred_lift_exact_def)

lemma hoare_pre_subst: "\<lbrakk> A = B; \<lbrace>A\<rbrace> a \<lbrace>C\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>B\<rbrace> a \<lbrace>C\<rbrace>"
  by (clarsimp simp:valid_def split_def)

lemma hoare_post_subst: "\<lbrakk> B = C; \<lbrace>A\<rbrace> a \<lbrace>B\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>A\<rbrace> a \<lbrace>C\<rbrace>"
  by (clarsimp simp:valid_def split_def)

lemma hoare_pre_tautI: "\<lbrakk> \<lbrace>A and P\<rbrace> a \<lbrace>B\<rbrace>; \<lbrace>A and not P\<rbrace> a \<lbrace>B\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>A\<rbrace> a \<lbrace>B\<rbrace>"
  by (clarsimp simp:valid_def split_def pred_conj_def pred_neg_def, blast)

lemma hoare_return_var[intro!]: "\<lbrakk> \<And>x. P x \<Longrightarrow> Q x \<rbrakk> \<Longrightarrow> (\<And>x. P x \<Longrightarrow> \<lbrace>R\<rbrace> return x \<lbrace>\<guillemotleft>Q,R\<guillemotright>\<rbrace>)"
  by (rule hoare_return)

lemma hoare_return_drop_imp[intro!]: "\<lbrakk> \<And>s. P s \<Longrightarrow> Q s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> return x \<lbrace>\<guillemotleft>\<top>,Q\<guillemotright>\<rbrace>"
 by (simp add:valid_def return_def)

lemmas hoare_case_option_inference = option.exhaust

lemma hoare_pre_imp: "\<lbrakk> \<lbrace>Q\<rbrace> a \<lbrace>R\<rbrace>; \<And>s. P s \<Longrightarrow> Q s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> a \<lbrace>R\<rbrace>"
  by (simp add:valid_def)

lemma hoare_post_imp: "\<lbrakk> \<lbrace>P\<rbrace> a \<lbrace>Q\<rbrace>; \<And>r s. Q r s \<Longrightarrow> R r s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> a \<lbrace>R\<rbrace>"
  by (simp add:valid_def split_def)

lemma hoare_post_impE:
  "\<lbrakk> \<lbrace>P\<rbrace> a \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>; \<And>r s. Q r s \<Longrightarrow> R r s; \<And>e s. E e s \<Longrightarrow> F e s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> a \<lbrace>R\<rbrace>,\<lbrace>F\<rbrace>"
  apply(clarsimp simp: validE_def)
  apply(rename_tac s r x)
  apply(case_tac r; fastforce)
  done

lemma "isSkip f \<Longrightarrow> \<lbrace> P \<rbrace> f \<lbrace> \<guillemotleft>\<top>,P\<guillemotright> \<rbrace>"
  apply (clarsimp simp: valid_def split_def isSkip_def)
  apply (rename_tac s)
  apply (case_tac "f s")
  apply (erule_tac x=s in allE)
  apply auto
  done

end
