(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory fncall
imports "CParser.CTranslation"
begin

declare sep_conj_ac [simp add]

primrec
  fac :: "nat \<Rightarrow> nat"
where
  "fac 0 = 1"
| "fac (Suc n) = (Suc n) * fac n"

ML \<open>

val ast = IsarInstall.get_Csyntax @{theory} "fncall.c"

\<close>

external_file "fncall.c"
install_C_file "fncall.c"

context fncall
begin


thm "\<Gamma>_def"
thm has_bogus_spec_'proc_def
thm has_bogus_spec_impl
thm f_impl
thm g_impl
thm h_impl
thm i_impl
thm calls_bogus_impl
thm f_body_def
thm g_body_def
thm fact_body_def

thm fact_'proc_def

thm has_bogus_spec_modifies
thm g_modifies
thm f_modifies
thm fact_modifies

term "f_body"
term "\<Gamma>"
term "fact_body"
term "f_'proc"

end

print_locale fncall_global_addresses

print_locale g_modifies
thm g_modifies_def

print_locale f_spec
thm f_spec_def

lemma (in g_modifies)
  shows "\<Gamma> \<turnstile> \<lbrace> \<acute>t_hrs = t \<rbrace> \<acute>ret__int :== PROC g() \<lbrace> \<acute>t_hrs = t \<rbrace>"
apply (hoare_rule HoarePartial.ProcRec1)
apply (vcg spec=modifies)
done


lemma (in fncall_global_addresses) f_impl_result:
  "\<Gamma> f_'proc = Some f_body"
  apply (rule f_impl)
  done

(* Check that printed procedure call syntax does not contain internal _'proc
   suffix, and that printed output is legal input and alpha-convertible to original.
   Also check that this holds for procedure names that are Const from the C parser
   as well as Free from Simpl locale parameters. *)
context fncall_global_addresses
begin

ML \<open>
local
  val ctxt = @{context};
  fun round_trip must_contain s =
    let
      val t = Syntax.read_term ctxt s;
      val s' = Pretty.pure_string_of (Syntax.pretty_term ctxt t);
      val _ = @{assert} (not (String.isSubstring "_'proc" s'));
      val _ = @{assert} (String.isSubstring must_contain s');
      val t' = Syntax.read_term ctxt s';
    in @{assert} (t aconv t') end;
in
val _ = round_trip "CALL f(\<acute>n)"
  "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret__int :== CALL f(\<acute>n) \<lbrace> \<acute>ret__int = 1 \<rbrace>";
val _ = round_trip "CALL g()"
  "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret__int :== CALL g() \<lbrace> \<acute>ret__int = 257 \<rbrace>";
val _ = round_trip "PROC f(\<acute>n)"
  "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret__int :== PROC f(\<acute>n) \<lbrace> \<acute>ret__int = 1 \<rbrace>";
val _ = round_trip "PROC g()"
  "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> Call g_'proc \<lbrace> \<acute>ret__int = 257 \<rbrace>";
end
\<close>

end

lemma (in fncall_global_addresses) g_spec:
  shows
  "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret__int :== PROC g() \<lbrace> \<acute>ret__int = 257 \<rbrace>"
  apply vcg
  done

lemma (in fncall_global_addresses) foo:
  shows
   "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret__int :== PROC f(n) \<lbrace> \<acute>ret__int = 1 \<rbrace>"
apply vcg
apply (simp )
done

lemma (in f_spec) foo :
shows
  "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret__int :== CALL f(\<acute>n) \<lbrace> \<acute>ret__int = 1 \<rbrace>"

apply vcg
done

lemma (in fncall_global_addresses) bar:
shows "\<Gamma> \<turnstile> \<lbrace> 1\<le> \<acute>n & \<acute>n \<le> 12 \<rbrace> \<acute>ret__int :== CALL fact(\<acute>n) \<lbrace> \<acute>ret__int = of_nat (fac (unat \<acute>n)) \<rbrace>"
apply vcg
apply unat_arith
oops

lemma (in fncall_global_addresses) baz:
shows "\<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> \<lbrace> \<acute>t_hrs = t \<rbrace> \<acute>ret__int :== PROC i() \<lbrace> \<acute>t_hrs = t \<rbrace>"
apply (hoare_rule HoarePartial.ProcRec1)
apply (vcg spec=modifies)
done

locale ih = i_modifies + h_modifies
lemma (in ih) qux:
shows "\<forall>t. \<Gamma> \<turnstile> \<lbrace>\<acute>t_hrs = t\<rbrace> \<acute>ret__int :== CALL i() \<lbrace> t = \<acute>t_hrs \<rbrace>"
apply vcg
oops

locale ff = f_spec + f_modifies
(* this lemma is bogus, because f does actually modify the globals *)
lemma (in ff) bogus1:
shows "\<forall>t. \<Gamma> \<turnstile> \<lbrace> \<acute>t_hrs = t \<rbrace> \<acute>ret__int :== CALL f(\<acute>n) \<lbrace> t = \<acute>t_hrs \<rbrace>"
apply vcg
apply simp
done

lemma (in has_bogus_spec_spec) bogus2:
shows "\<Gamma> \<turnstile> \<lbrace> \<acute>n = 42 \<rbrace> \<acute>ret__int :== CALL has_bogus_spec() \<lbrace> \<acute>ret__int = 4 \<rbrace>"
apply vcg
done

lemma (in fncall_global_addresses) toldyou:
shows "\<Gamma> \<turnstile> \<lbrace> \<acute>n = 42 \<rbrace> \<acute>ret__int :== CALL has_bogus_spec() \<lbrace> \<acute>ret__int = 3 \<rbrace>"
apply vcg
done

lemma (in has_bogus_spec_spec) bogus3:
shows "\<Gamma> \<turnstile> \<lbrace> \<acute>n = 42 \<rbrace> \<acute>ret__int :== CALL calls_bogus() \<lbrace> \<acute>ret__int = 4 \<rbrace>"
apply vcg
done

end
