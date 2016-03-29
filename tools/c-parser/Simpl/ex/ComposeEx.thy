(*
    Author:      Norbert Schirmer
    Maintainer:  Norbert Schirmer, norbert.schirmer at web de
    License:     LGPL
*)

(*  Title:      ComposeEx.thy
    Author:     Norbert Schirmer, TU Muenchen

Copyright (C) 2006-2008 Norbert Schirmer 
Some rights reserved, TU Muenchen

This library is free software; you can redistribute it and/or modify
it under the terms of the GNU Lesser General Public License as
published by the Free Software Foundation; either version 2.1 of the
License, or (at your option) any later version.

This library is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307
USA
*)
theory ComposeEx imports Compose "../Vcg" "../HeapList" begin


record globals_list = 
  next_' :: "ref \<Rightarrow> ref"

record state_list = "globals_list state" +
  p_'    :: "ref"
  sl_q_'    :: "ref"
  r_'    :: "ref"


procedures Rev(p|sl_q) =
      "\<acute>sl_q :== Null;;
       WHILE \<acute>p \<noteq> Null 
       DO
         \<acute>r :== \<acute>p;; \<lbrace>\<acute>p \<noteq> Null\<rbrace>\<longmapsto> \<acute>p :== \<acute>p\<rightarrow>\<acute>next;;
         \<lbrace>\<acute>r \<noteq> Null\<rbrace>\<longmapsto> \<acute>r\<rightarrow>\<acute>next :== \<acute>sl_q;; \<acute>sl_q :== \<acute>r
       OD"
print_theorems



lemma (in Rev_impl) 
 Rev_modifies:
  "\<forall>\<sigma>. \<Gamma>\<turnstile>\<^bsub>/UNIV \<^esub>{\<sigma>} \<acute>sl_q :== PROC Rev(\<acute>p) {t. t may_only_modify_globals \<sigma> in [next]}"
apply (hoare_rule HoarePartial.ProcNoRec1)
apply (vcg spec=modifies)
done

lemma (in Rev_impl) shows
 Rev_spec: 
  "\<forall>Ps. \<Gamma>\<turnstile> \<lbrace>List \<acute>p \<acute>next Ps\<rbrace> \<acute>sl_q :== PROC Rev(\<acute>p) \<lbrace>List \<acute>sl_q \<acute>next (rev Ps)\<rbrace>"
apply (hoare_rule HoarePartial.ProcNoRec1)
apply (hoare_rule anno =
       "\<acute>sl_q :== Null;;
       WHILE \<acute>p \<noteq> Null INV \<lbrace>\<exists>Ps' Qs'. List \<acute>p \<acute>next Ps' \<and> List \<acute>sl_q \<acute>next Qs' \<and>
                             set Ps' \<inter> set Qs' = {} \<and>
                             rev Ps' @ Qs' = rev Ps\<rbrace>
        DO
         \<acute>r :== \<acute>p;; \<lbrace>\<acute>p \<noteq> Null\<rbrace>\<longmapsto>\<acute>p :== \<acute>p\<rightarrow>\<acute>next;;
         \<lbrace>\<acute>r \<noteq> Null\<rbrace>\<longmapsto> \<acute>r\<rightarrow>\<acute>next :== \<acute>sl_q;; \<acute>sl_q :== \<acute>r
       OD" in HoarePartial.annotateI)
apply vcg 
apply   clarsimp
apply  fastforce
apply clarsimp
done

declare [[names_unique = false]]

record globals = 
  strnext_'   :: "ref \<Rightarrow> ref"
  chr_'    :: "ref \<Rightarrow> char"

  qnext_' :: "ref \<Rightarrow> ref"  
  cont_'   :: "ref \<Rightarrow> int"
record state = "globals state" +
  str_'  :: "ref"
  queue_':: "ref" 
  q_'    :: "ref"
  r_'    :: "ref"


definition project_globals_str:: "globals \<Rightarrow> globals_list"
  where "project_globals_str g = \<lparr>next_' = strnext_' g\<rparr>"

definition project_str:: "state \<Rightarrow> state_list"
where
"project_str s =
  \<lparr>globals = project_globals_str (globals s),
   state_list.p_' = str_' s, sl_q_' = q_' s, state_list.r_' = r_' s\<rparr>"

definition inject_globals_str:: 
  "globals \<Rightarrow> globals_list \<Rightarrow> globals"
where
  "inject_globals_str G g =
   G\<lparr>strnext_' := next_' g\<rparr>"

definition "inject_str"::"state \<Rightarrow> state_list \<Rightarrow> state" where
"inject_str S s = S\<lparr>globals := inject_globals_str (globals S) (globals s),
                str_' := state_list.p_' s, q_' := sl_q_' s,
                r_' := state_list.r_' s\<rparr>"

lemma globals_inject_project_str_commutes: 
  "inject_globals_str G (project_globals_str G) = G"
  by (simp add: inject_globals_str_def project_globals_str_def)

lemma inject_project_str_commutes: "inject_str S (project_str S) = S"
  by (simp add: inject_str_def project_str_def globals_inject_project_str_commutes)

lemma globals_project_inject_str_commutes: 
  "project_globals_str (inject_globals_str G g) = g"
  by (simp add: inject_globals_str_def project_globals_str_def)

lemma project_inject_str_commutes: "project_str (inject_str S s) = s"
  by (simp add: inject_str_def project_str_def globals_project_inject_str_commutes)

lemma globals_inject_str_last: 
  "inject_globals_str (inject_globals_str G g) g' = inject_globals_str G g'"
  by (simp add: inject_globals_str_def)

lemma inject_str_last: 
  "inject_str (inject_str S s) s' = inject_str S s'"
  by (simp add: inject_str_def globals_inject_str_last)

definition
  "lift\<^sub>e = (\<lambda>\<Gamma> p. map_option (lift\<^sub>c project_str inject_str) (\<Gamma> p))"
print_locale lift_state_space
interpretation ex: lift_state_space project_str inject_str
  "xstate_map project_str" lift\<^sub>e "lift\<^sub>c project_str inject_str"
  "lift\<^sub>f project_str inject_str" "lift\<^sub>s project_str"
  "lift\<^sub>r project_str inject_str"
  apply -
  apply       (rule lift_state_space.intro)
  apply       (rule project_inject_str_commutes)
  apply      simp
  apply     simp
  apply    (simp add: lift\<^sub>e_def)
  apply   simp
  apply  simp
  apply simp
  done

interpretation ex: lift_state_space_ext project_str inject_str
  "xstate_map project_str" lift\<^sub>e "lift\<^sub>c project_str inject_str"
  "lift\<^sub>f project_str inject_str" "lift\<^sub>s project_str"
  "lift\<^sub>r project_str inject_str"

(*  project_str "inject_str" _ lift\<^sub>e *)
apply -
apply intro_locales [1]
  apply (rule lift_state_space_ext_axioms.intro)
  apply  (rule inject_project_str_commutes) 
  apply (rule inject_str_last)
apply (simp_all add: lift\<^sub>e_def)
  done

(*
  apply (intro_locales)
  apply (rule lift_state_space_ext_axioms.intro)
  apply  (rule inject_project_str_commutes) 
  apply (rule inject_str_last)
  done
*)

(*
declare lift_set_def [simp] project_def [simp] project_globals_def [simp]
*)
lemmas Rev_lift_spec = ex.lift_hoarep' [OF Rev_impl.Rev_spec,simplified lift\<^sub>s_def
 project_str_def project_globals_str_def,simplified, of _ "''Rev''"]
print_theorems


definition "\<N> p' p = (if p=''Rev'' then p' else '''')"


procedures RevStr(str|q) = "rename (\<N> RevStr_'proc)
                (lift\<^sub>c project_str inject_str (Rev_body.Rev_body))"


lemmas Rev_lift_spec' = 
  Rev_lift_spec [of "[''Rev''\<mapsto>Rev_body.Rev_body]" ,
     simplified Rev_impl_def Rev_clique_def,simplified]
thm Rev_lift_spec'


lemma Rev_lift_spec'':
  "\<forall>Ps. lift\<^sub>e [''Rev'' \<mapsto> Rev_body.Rev_body]
       \<turnstile> \<lbrace>List \<acute>str \<acute>strnext Ps\<rbrace> Call ''Rev'' \<lbrace>List \<acute>q \<acute>strnext (rev Ps)\<rbrace>"
  by (rule Rev_lift_spec')

lemma (in RevStr_impl) \<N>_ok: 
"\<forall>p bdy. (lift\<^sub>e [''Rev'' \<mapsto> Rev_body.Rev_body]) p = Some bdy \<longrightarrow> 
     \<Gamma> (\<N> RevStr_'proc p) = Some (rename (\<N> RevStr_'proc) bdy)"
apply (insert RevStr_impl)
apply (auto simp add: RevStr_body_def lift\<^sub>e_def \<N>_def)
done

context RevStr_impl
begin
 thm hoare_to_hoare_rename'[OF _ Rev_lift_spec'', OF \<N>_ok,
  simplified \<N>_def, simplified ]
end

lemmas (in RevStr_impl) RevStr_spec =
  hoare_to_hoare_rename' [OF _ Rev_lift_spec'', OF \<N>_ok,
  simplified \<N>_def, simplified ]


lemma (in RevStr_impl) RevStr_spec': 
"\<forall>Ps. \<Gamma>\<turnstile> \<lbrace>List \<acute>str \<acute>strnext Ps\<rbrace> \<acute>q :== PROC RevStr(\<acute>str) 
          \<lbrace>List \<acute>q \<acute>strnext (rev Ps)\<rbrace>"
  by (rule RevStr_spec)

lemmas Rev_modifies' =
  Rev_impl.Rev_modifies [of "[''Rev''\<mapsto>Rev_body.Rev_body]", simplified Rev_impl_def,
   simplified]
thm Rev_modifies'

context RevStr_impl
begin
lemmas RevStr_modifies' =
  hoare_to_hoare_rename' [OF _ ex.hoare_lift_modifies' [OF Rev_modifies'],
         OF \<N>_ok, of "''Rev''", simplified \<N>_def Rev_clique_def,simplified]
end


lemma (in RevStr_impl) RevStr_modifies:
"\<forall>\<sigma>. \<Gamma>\<turnstile>\<^bsub>/UNIV \<^esub>{\<sigma>} \<acute>str :== PROC RevStr(\<acute>str) 
  {t. t may_only_modify_globals \<sigma> in [strnext]}"
apply (rule allI)
apply (rule HoarePartialProps.ConseqMGT [OF RevStr_modifies'])
apply (clarsimp simp add: 
  lift\<^sub>s_def mex_def meq_def
  project_str_def inject_str_def project_globals_str_def inject_globals_str_def)
apply blast
done

end

