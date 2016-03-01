(*
    Author:      Norbert Schirmer
    Maintainer:  Norbert Schirmer, norbert.schirmer at web de
    License:     LGPL
*)

(*  Title:      Language.thy
    Author:     Norbert Schirmer, TU Muenchen

Copyright (C) 2004-2008 Norbert Schirmer 
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

section {* The Simpl Syntax *}

theory Language imports "~~/src/HOL/Library/Old_Recdef" begin

subsection {* The Core Language *}

text {* We use a shallow embedding of boolean expressions as well as assertions
as sets of states. 
*}

type_synonym 's bexp = "'s set"
type_synonym 's assn = "'s set"

datatype (dead 's, 'p, 'f) com =
    Skip
  | Basic "'s \<Rightarrow> 's"
  | Spec "('s \<times> 's) set"
  | Seq "('s ,'p, 'f) com" "('s,'p, 'f) com"    
  | Cond "'s bexp" "('s,'p,'f) com"  "('s,'p,'f) com"
  | While "'s bexp" "('s,'p,'f) com"
  | Call "'p" 
  | DynCom "'s \<Rightarrow> ('s,'p,'f) com" 
  | Guard "'f" "'s bexp" "('s,'p,'f) com" 
  | Throw
  | Catch "('s,'p,'f) com" "('s,'p,'f) com"






subsection {* Derived Language Constructs *}

definition
  raise:: "('s \<Rightarrow> 's) \<Rightarrow> ('s,'p,'f) com" where
  "raise f = Seq (Basic f) Throw"

definition
  condCatch:: "('s,'p,'f) com \<Rightarrow> 's bexp \<Rightarrow> ('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com" where
  "condCatch c\<^sub>1 b c\<^sub>2 = Catch c\<^sub>1 (Cond b c\<^sub>2 Throw)"

definition
  bind:: "('s \<Rightarrow> 'v) \<Rightarrow> ('v \<Rightarrow> ('s,'p,'f) com) \<Rightarrow> ('s,'p,'f) com" where
  "bind e c = DynCom (\<lambda>s. c (e s))"

definition
  bseq:: "('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com" where
  "bseq = Seq"
 
definition
  block:: "['s\<Rightarrow>'s,('s,'p,'f) com,'s\<Rightarrow>'s\<Rightarrow>'s,'s\<Rightarrow>'s\<Rightarrow>('s,'p,'f) com]\<Rightarrow>('s,'p,'f) com"
where
  "block init bdy return c =
    DynCom (\<lambda>s. (Seq (Catch (Seq (Basic init) bdy) (Seq (Basic (return s)) Throw)) 
                            (DynCom (\<lambda>t. Seq (Basic (return s)) (c s t))))
                        )" 

definition
  call:: "('s\<Rightarrow>'s) \<Rightarrow> 'p \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 's)\<Rightarrow>('s\<Rightarrow>'s\<Rightarrow>('s,'p,'f) com)\<Rightarrow>('s,'p,'f)com" where
  "call init p return c = block init (Call p) return c"

definition
  dynCall:: "('s \<Rightarrow> 's) \<Rightarrow> ('s \<Rightarrow> 'p) \<Rightarrow> 
             ('s \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> ('s,'p,'f) com) \<Rightarrow> ('s,'p,'f) com" where
  "dynCall init p return c = DynCom (\<lambda>s. call init (p s) return c)"

definition
  fcall:: "('s\<Rightarrow>'s) \<Rightarrow> 'p \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 's)\<Rightarrow>('s \<Rightarrow> 'v) \<Rightarrow> ('v\<Rightarrow>('s,'p,'f) com)
            \<Rightarrow>('s,'p,'f)com" where
  "fcall init p return result c = call init p return (\<lambda>s t. c (result t))"

definition
  lem:: "'x \<Rightarrow> ('s,'p,'f)com \<Rightarrow>('s,'p,'f)com" where
  "lem x c = c"

primrec switch:: "('s \<Rightarrow> 'v) \<Rightarrow> ('v set \<times> ('s,'p,'f) com) list \<Rightarrow> ('s,'p,'f) com" 
where
"switch v [] = Skip" |
"switch v (Vc#vs) = Cond {s. v s \<in> fst Vc} (snd Vc) (switch v vs)"

definition guaranteeStrip:: "'f \<Rightarrow> 's set \<Rightarrow> ('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com"
  where "guaranteeStrip f g c = Guard f g c"

definition guaranteeStripPair:: "'f \<Rightarrow> 's set \<Rightarrow> ('f \<times> 's set)"
  where "guaranteeStripPair f g = (f,g)"

primrec guards:: "('f \<times> 's set ) list \<Rightarrow> ('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com"
where
"guards [] c = c" |
"guards (g#gs) c = Guard (fst g) (snd g) (guards gs c)"

definition
  while::  "('f \<times> 's set) list \<Rightarrow> 's bexp \<Rightarrow> ('s,'p,'f) com \<Rightarrow> ('s, 'p, 'f) com"
where
  "while gs b c = guards gs (While b (Seq c (guards gs Skip)))"

definition
  whileAnno:: 
  "'s bexp \<Rightarrow> 's assn \<Rightarrow> ('s \<times> 's) assn \<Rightarrow> ('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com" where
  "whileAnno b I V c = While b c"

definition
  whileAnnoG:: 
  "('f \<times> 's set) list \<Rightarrow> 's bexp \<Rightarrow> 's assn \<Rightarrow> ('s \<times> 's) assn \<Rightarrow> 
     ('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com" where
  "whileAnnoG gs b I V c = while gs b c"
 
definition
  specAnno::  "('a \<Rightarrow> 's assn) \<Rightarrow> ('a \<Rightarrow> ('s,'p,'f) com) \<Rightarrow> 
                         ('a \<Rightarrow> 's assn) \<Rightarrow> ('a \<Rightarrow> 's assn) \<Rightarrow> ('s,'p,'f) com"
  where "specAnno P c Q A = (c undefined)"

definition
  whileAnnoFix:: 
  "'s bexp \<Rightarrow> ('a \<Rightarrow> 's assn) \<Rightarrow> ('a \<Rightarrow> ('s \<times> 's) assn) \<Rightarrow> ('a \<Rightarrow> ('s,'p,'f) com) \<Rightarrow> 
     ('s,'p,'f) com" where
  "whileAnnoFix b I V c = While b (c undefined)"

definition
  whileAnnoGFix:: 
  "('f \<times> 's set) list \<Rightarrow> 's bexp \<Rightarrow> ('a \<Rightarrow> 's assn) \<Rightarrow> ('a \<Rightarrow> ('s \<times> 's) assn) \<Rightarrow> 
     ('a \<Rightarrow> ('s,'p,'f) com) \<Rightarrow> ('s,'p,'f) com" where
  "whileAnnoGFix gs b I V c = while gs b (c undefined)"

definition if_rel::"('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> ('s \<times> 's) set" 
  where "if_rel b f g h = {(s,t). if b s then t = f s else t = g s \<or> t = h s}"

lemma fst_guaranteeStripPair: "fst (guaranteeStripPair f g) = f"
  by (simp add: guaranteeStripPair_def)

lemma snd_guaranteeStripPair: "snd (guaranteeStripPair f g) = g"
  by (simp add: guaranteeStripPair_def)


subsection {* Operations on Simpl-Syntax *}


subsubsection {* Normalisation of Sequential Composition: @{text "sequence"}, @{text "flatten"} and @{text "normalize"} *}

primrec flatten:: "('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com list" 
where
"flatten Skip = [Skip]" |
"flatten (Basic f) = [Basic f]" |
"flatten (Spec r) = [Spec r]" |
"flatten (Seq c\<^sub>1 c\<^sub>2)  = flatten c\<^sub>1 @ flatten c\<^sub>2" |
"flatten (Cond b c\<^sub>1 c\<^sub>2) = [Cond b c\<^sub>1 c\<^sub>2]" |
"flatten (While b c) = [While b c]" |
"flatten (Call p) = [Call p]" |
"flatten (DynCom c) = [DynCom c]" |
"flatten (Guard f g c) = [Guard f g c]" |
"flatten Throw = [Throw]" |
"flatten (Catch c\<^sub>1 c\<^sub>2) = [Catch c\<^sub>1 c\<^sub>2]"

primrec sequence:: "(('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com) \<Rightarrow> 
                      ('s,'p,'f) com list \<Rightarrow> ('s,'p,'f) com"
where
"sequence seq [] = Skip" |
"sequence seq (c#cs) = (case cs of [] \<Rightarrow> c
                        | _ \<Rightarrow> seq c (sequence seq cs))" 


primrec normalize:: "('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com"
where
"normalize Skip = Skip" |
"normalize (Basic f) = Basic f" |
"normalize (Spec r) = Spec r" |
"normalize (Seq c\<^sub>1 c\<^sub>2)  = sequence Seq
                            ((flatten (normalize c\<^sub>1)) @ (flatten (normalize c\<^sub>2)))" |
"normalize (Cond b c\<^sub>1 c\<^sub>2) = Cond b (normalize c\<^sub>1) (normalize c\<^sub>2)" |
"normalize (While b c) = While b (normalize c)" |
"normalize (Call p) = Call p" |
"normalize (DynCom c) = DynCom (\<lambda>s. (normalize (c s)))" |
"normalize (Guard f g c) = Guard f g (normalize c)" |
"normalize Throw = Throw" |
"normalize (Catch c\<^sub>1 c\<^sub>2) = Catch (normalize c\<^sub>1) (normalize c\<^sub>2)"


lemma flatten_nonEmpty: "flatten c \<noteq> []"
  by (induct c) simp_all

lemma flatten_single: "\<forall>c \<in> set (flatten c'). flatten c = [c]"
apply (induct c')
apply           simp
apply          simp
apply         simp
apply        (simp (no_asm_use) )
apply        blast
apply       (simp (no_asm_use) )
apply      (simp (no_asm_use) )
apply     simp
apply    (simp (no_asm_use))
apply   (simp (no_asm_use))
apply  simp
apply (simp (no_asm_use))
done


lemma flatten_sequence_id: 
  "\<lbrakk>cs\<noteq>[];\<forall>c \<in> set cs. flatten c = [c]\<rbrakk> \<Longrightarrow> flatten (sequence Seq cs) = cs"
  apply (induct cs)
  apply  simp
  apply (case_tac cs)
  apply  simp
  apply auto
  done


lemma flatten_app:
  "flatten (sequence Seq (flatten c1 @ flatten c2)) = flatten c1 @ flatten c2"
  apply (rule flatten_sequence_id)
  apply (simp add: flatten_nonEmpty)
  apply (simp)
  apply (insert flatten_single)
  apply blast
  done


  
lemma flatten_sequence_flatten: "flatten (sequence Seq (flatten c)) = flatten c"
  apply (induct c)
  apply (auto simp add: flatten_app)
  done

lemma sequence_flatten_normalize: "sequence Seq (flatten (normalize c)) = normalize c"
apply (induct c)
apply (auto simp add:  flatten_app)
done


lemma flatten_normalize: "\<And>x xs. flatten (normalize c) = x#xs 
       \<Longrightarrow> (case xs of [] \<Rightarrow> normalize c = x 
              | (x'#xs') \<Rightarrow> normalize c= Seq x (sequence Seq xs))"
proof (induct c)
  case (Seq c1 c2)
  have "flatten (normalize (Seq c1 c2)) = x # xs" by fact
  hence "flatten (sequence Seq (flatten (normalize c1) @ flatten (normalize c2))) = 
          x#xs"
    by simp
  hence x_xs: "flatten (normalize c1) @ flatten (normalize c2) = x # xs" 
    by (simp add: flatten_app)
  show ?case
  proof (cases "flatten (normalize c1)")
    case Nil
    with flatten_nonEmpty show ?thesis by auto
  next
    case (Cons x1 xs1)
    note Cons_x1_xs1 = this
    with x_xs obtain 
      x_x1: "x=x1" and xs_rest: "xs=xs1@flatten (normalize c2)"
      by auto
    show ?thesis
    proof (cases xs1)
      case Nil
      from Seq.hyps (1) [OF Cons_x1_xs1] Nil
      have "normalize c1 = x1"
        by simp
      with Cons_x1_xs1 Nil x_x1 xs_rest show ?thesis
        apply (cases "flatten (normalize c2)")
        apply (fastforce simp add: flatten_nonEmpty)
        apply simp
        done
    next
      case Cons
      from Seq.hyps (1) [OF Cons_x1_xs1] Cons
      have "normalize c1 = Seq x1 (sequence Seq xs1)"
        by simp
      with Cons_x1_xs1 Nil x_x1 xs_rest show ?thesis
        apply (cases "flatten (normalize c2)")
        apply (fastforce simp add: flatten_nonEmpty)
        apply (simp split: list.splits)
        done
    qed
  qed
qed (auto)

lemma flatten_raise [simp]: "flatten (raise f) = [Basic f, Throw]"
  by (simp add: raise_def)

lemma flatten_condCatch [simp]: "flatten (condCatch c1 b c2) = [condCatch c1 b c2]"
  by (simp add: condCatch_def)

lemma flatten_bind [simp]: "flatten (bind e c) = [bind e c]"
  by (simp add: bind_def)

lemma flatten_bseq [simp]: "flatten (bseq c1 c2) = flatten c1 @ flatten c2"
  by (simp add: bseq_def)

lemma flatten_block [simp]:
  "flatten (block init bdy return result) = [block init bdy return result]"
  by (simp add: block_def)

lemma flatten_call [simp]: "flatten (call init p return result) = [call init p return result]"
  by (simp add: call_def)

lemma flatten_dynCall [simp]: "flatten (dynCall init p return result) = [dynCall init p return result]"
  by (simp add: dynCall_def)

lemma flatten_fcall [simp]: "flatten (fcall init p return result c) = [fcall init p return result c]"
  by (simp add: fcall_def)

lemma flatten_switch [simp]: "flatten (switch v Vcs) = [switch v Vcs]"
  by (cases Vcs) auto

lemma flatten_guaranteeStrip [simp]: 
  "flatten (guaranteeStrip f g c) = [guaranteeStrip f g c]"
  by (simp add: guaranteeStrip_def)

lemma flatten_while [simp]: "flatten (while gs b c) = [while gs b c]"
  apply (simp add: while_def)
  apply (induct gs)
  apply  auto
  done

lemma flatten_whileAnno [simp]: 
  "flatten (whileAnno b I V c) = [whileAnno b I V c]"
  by (simp add: whileAnno_def)

lemma flatten_whileAnnoG [simp]: 
  "flatten (whileAnnoG gs b I V c) = [whileAnnoG gs b I V c]"
  by (simp add: whileAnnoG_def)

lemma flatten_specAnno [simp]:
  "flatten (specAnno P c Q A) = flatten (c undefined)"
  by (simp add: specAnno_def)

lemmas flatten_simps = flatten.simps flatten_raise flatten_condCatch flatten_bind
  flatten_block flatten_call flatten_dynCall flatten_fcall flatten_switch
  flatten_guaranteeStrip
  flatten_while flatten_whileAnno flatten_whileAnnoG flatten_specAnno

lemma normalize_raise [simp]:
 "normalize (raise f) = raise f"
  by (simp add: raise_def)

lemma normalize_condCatch [simp]:
 "normalize (condCatch c1 b c2) = condCatch (normalize c1) b (normalize c2)"
  by (simp add: condCatch_def)

lemma normalize_bind [simp]:
 "normalize (bind e c) = bind e (\<lambda>v. normalize (c v))"
  by (simp add: bind_def)

lemma normalize_bseq [simp]:
 "normalize (bseq c1 c2) = sequence bseq
                            ((flatten (normalize c1)) @ (flatten (normalize c2)))"
  by (simp add: bseq_def)

lemma normalize_block [simp]: "normalize (block init bdy return c) = 
                         block init (normalize bdy) return (\<lambda>s t. normalize (c s t))"
  apply (simp add: block_def)
  apply (rule ext)
  apply (simp)
  apply (cases "flatten (normalize bdy)")
  apply  (simp add: flatten_nonEmpty)
  apply (rule conjI)
  apply  simp
  apply  (drule flatten_normalize)
  apply  (case_tac list)
  apply   simp
  apply  simp
  apply (rule ext)
  apply (case_tac "flatten (normalize (c s sa))")
  apply  (simp add: flatten_nonEmpty)
  apply  simp
  apply (thin_tac "flatten (normalize bdy) = P" for P)
  apply (drule flatten_normalize)
  apply (case_tac lista)
  apply  simp
  apply simp
  done

lemma normalize_call [simp]: 
  "normalize (call init p return c) = call init p return (\<lambda>i t. normalize (c i t))"
  by (simp add: call_def)

lemma normalize_dynCall [simp]:
  "normalize (dynCall init p return c) = 
    dynCall init p return (\<lambda>s t. normalize (c s t))" 
  by (simp add: dynCall_def)

lemma normalize_fcall [simp]:
  "normalize (fcall init p return result c) = 
    fcall init p return result (\<lambda>v. normalize (c v))"
  by (simp add: fcall_def)

lemma normalize_switch [simp]:
  "normalize (switch v Vcs) = switch v (map (\<lambda>(V,c). (V,normalize c)) Vcs)"
apply (induct Vcs)
apply auto
done

lemma normalize_guaranteeStrip [simp]:
  "normalize (guaranteeStrip f g c) = guaranteeStrip f g (normalize c)"
  by (simp add: guaranteeStrip_def)

lemma normalize_guards [simp]:
  "normalize (guards gs c) = guards gs (normalize c)"
  by (induct gs) auto

text {* Sequencial composition with guards in the body is not preserved by
        normalize *}
lemma normalize_while [simp]:
  "normalize (while gs b c) = guards gs
      (While b (sequence Seq (flatten (normalize c) @ flatten (guards gs Skip))))" 
  by (simp add: while_def)

lemma normalize_whileAnno [simp]:
  "normalize (whileAnno b I V c) = whileAnno b I V (normalize c)"
  by (simp add: whileAnno_def)

lemma normalize_whileAnnoG [simp]:
  "normalize (whileAnnoG gs b I V c) = guards gs
      (While b (sequence Seq (flatten (normalize c) @ flatten (guards gs Skip))))" 
  by (simp add: whileAnnoG_def)

lemma normalize_specAnno [simp]:
  "normalize (specAnno P c Q A) = specAnno P (\<lambda>s. normalize (c undefined)) Q A"
  by (simp add: specAnno_def)

lemmas normalize_simps = 
  normalize.simps normalize_raise normalize_condCatch normalize_bind
  normalize_block normalize_call normalize_dynCall normalize_fcall normalize_switch
  normalize_guaranteeStrip normalize_guards 
  normalize_while normalize_whileAnno normalize_whileAnnoG normalize_specAnno


subsubsection {* Stripping Guards: @{text "strip_guards"} *}

primrec strip_guards:: "'f set \<Rightarrow> ('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com"
where
"strip_guards F Skip = Skip" |
"strip_guards F (Basic f) = Basic f" |
"strip_guards F (Spec r) = Spec r" |
"strip_guards F (Seq c\<^sub>1 c\<^sub>2)  = (Seq (strip_guards F c\<^sub>1) (strip_guards F c\<^sub>2))" |
"strip_guards F (Cond b c\<^sub>1 c\<^sub>2) = Cond b (strip_guards F c\<^sub>1) (strip_guards F c\<^sub>2)" |
"strip_guards F (While b c) = While b (strip_guards F c)" |
"strip_guards F (Call p) = Call p" |
"strip_guards F (DynCom c) = DynCom (\<lambda>s. (strip_guards F (c s)))" |
"strip_guards F (Guard f g c) = (if f \<in> F then strip_guards F c
                                  else Guard f g (strip_guards F c))" |
"strip_guards F Throw = Throw" |
"strip_guards F (Catch c\<^sub>1 c\<^sub>2) = Catch (strip_guards F c\<^sub>1) (strip_guards F c\<^sub>2)"

definition strip:: "'f set \<Rightarrow> 
                   ('p \<Rightarrow> ('s,'p,'f) com option) \<Rightarrow> ('p \<Rightarrow> ('s,'p,'f) com option)"
  where "strip F \<Gamma> = (\<lambda>p. map_option (strip_guards F) (\<Gamma> p))"


lemma strip_simp [simp]: "(strip F \<Gamma>) p = map_option (strip_guards F) (\<Gamma> p)"
  by (simp add: strip_def)

lemma dom_strip: "dom (strip F \<Gamma>) = dom \<Gamma>"
  by (auto)

lemma strip_guards_idem: "strip_guards F (strip_guards F c) = strip_guards F c"
  by (induct c) auto

lemma strip_idem: "strip F (strip F \<Gamma>) = strip F \<Gamma>"
  apply (rule ext)
  apply (case_tac "\<Gamma> x")
  apply (auto simp add: strip_guards_idem strip_def)
  done

lemma strip_guards_raise [simp]:
  "strip_guards F (raise f) = raise f"
  by (simp add: raise_def)

lemma strip_guards_condCatch [simp]:
  "strip_guards F (condCatch c1 b c2) = 
    condCatch (strip_guards F c1) b (strip_guards F c2)"
  by (simp add: condCatch_def)

lemma strip_guards_bind [simp]:
  "strip_guards F (bind e c) = bind e (\<lambda>v. strip_guards F (c v))"
  by (simp add: bind_def)

lemma strip_guards_bseq [simp]:
  "strip_guards F (bseq c1 c2) = bseq (strip_guards F c1) (strip_guards F c2)"
  by (simp add: bseq_def)

lemma strip_guards_block [simp]:
  "strip_guards F (block init bdy return c) =
    block init (strip_guards F bdy) return (\<lambda>s t. strip_guards F (c s t))"
  by (simp add: block_def)

lemma strip_guards_call [simp]:
  "strip_guards F (call init p return c) =
     call init p return (\<lambda>s t. strip_guards F (c s t))"
  by (simp add: call_def)

lemma strip_guards_dynCall [simp]:
  "strip_guards F (dynCall init p return c) =
     dynCall init p return (\<lambda>s t. strip_guards F (c s t))"
  by (simp add: dynCall_def)

lemma strip_guards_fcall [simp]:
  "strip_guards F (fcall init p return result c) =
     fcall init p return result (\<lambda>v. strip_guards F (c v))"
  by (simp add: fcall_def)

lemma strip_guards_switch [simp]:
  "strip_guards F (switch v Vc) =
    switch v (map (\<lambda>(V,c). (V,strip_guards F c)) Vc)"
  by (induct Vc) auto

lemma strip_guards_guaranteeStrip [simp]:
  "strip_guards F (guaranteeStrip f g c) = 
    (if f \<in> F then strip_guards F c 
     else guaranteeStrip f g (strip_guards F c))"
  by (simp add: guaranteeStrip_def)

lemma guaranteeStripPair_split_conv [simp]: "case_prod c (guaranteeStripPair f g) = c f g"
  by (simp add: guaranteeStripPair_def)

lemma strip_guards_guards [simp]: "strip_guards F (guards gs c) =
        guards (filter (\<lambda>(f,g). f \<notin> F) gs) (strip_guards F c)"
  by (induct gs) auto

lemma strip_guards_while [simp]:
 "strip_guards F (while gs b  c) = 
     while (filter (\<lambda>(f,g). f \<notin> F) gs) b (strip_guards F c)"
  by (simp add: while_def)

lemma strip_guards_whileAnno [simp]:
 "strip_guards F (whileAnno b I V c) = whileAnno b I V (strip_guards F c)"
  by (simp add: whileAnno_def  while_def)

lemma strip_guards_whileAnnoG [simp]:
 "strip_guards F (whileAnnoG gs b I V c) = 
     whileAnnoG (filter (\<lambda>(f,g). f \<notin> F) gs) b I V (strip_guards F c)"
  by (simp add: whileAnnoG_def)

lemma strip_guards_specAnno [simp]:
  "strip_guards F (specAnno P c Q A) = 
    specAnno P (\<lambda>s. strip_guards F (c undefined)) Q A"
  by (simp add: specAnno_def)

lemmas strip_guards_simps = strip_guards.simps strip_guards_raise 
  strip_guards_condCatch strip_guards_bind strip_guards_bseq strip_guards_block
  strip_guards_dynCall strip_guards_fcall strip_guards_switch 
  strip_guards_guaranteeStrip guaranteeStripPair_split_conv strip_guards_guards
  strip_guards_while strip_guards_whileAnno strip_guards_whileAnnoG
  strip_guards_specAnno

subsubsection {* Marking Guards: @{text "mark_guards"} *}

primrec mark_guards:: "'f \<Rightarrow> ('s,'p,'g) com \<Rightarrow> ('s,'p,'f) com"
where
"mark_guards f Skip = Skip" |
"mark_guards f (Basic g) = Basic g" |
"mark_guards f (Spec r) = Spec r" |
"mark_guards f (Seq c\<^sub>1 c\<^sub>2)  = (Seq (mark_guards f c\<^sub>1) (mark_guards f c\<^sub>2))" |
"mark_guards f (Cond b c\<^sub>1 c\<^sub>2) = Cond b (mark_guards f c\<^sub>1) (mark_guards f c\<^sub>2)" |
"mark_guards f (While b c) = While b (mark_guards f c)" |
"mark_guards f (Call p) = Call p" |
"mark_guards f (DynCom c) = DynCom (\<lambda>s. (mark_guards f (c s)))" |
"mark_guards f (Guard f' g c) = Guard f g (mark_guards f c)" |
"mark_guards f Throw = Throw" |
"mark_guards f (Catch c\<^sub>1 c\<^sub>2) = Catch (mark_guards f c\<^sub>1) (mark_guards f c\<^sub>2)"

lemma mark_guards_raise: "mark_guards f (raise g) = raise g"
  by (simp add: raise_def)

lemma mark_guards_condCatch [simp]:
  "mark_guards f (condCatch c1 b c2) = 
    condCatch (mark_guards f c1) b (mark_guards f c2)"
  by (simp add: condCatch_def)

lemma mark_guards_bind [simp]:
  "mark_guards f (bind e c) = bind e (\<lambda>v. mark_guards f (c v))"
  by (simp add: bind_def)

lemma mark_guards_bseq [simp]:
  "mark_guards f (bseq c1 c2) = bseq (mark_guards f c1) (mark_guards f c2)"
  by (simp add: bseq_def)

lemma mark_guards_block [simp]:
  "mark_guards f (block init bdy return c) =
    block init (mark_guards f bdy) return (\<lambda>s t. mark_guards f (c s t))"
  by (simp add: block_def)

lemma mark_guards_call [simp]:
  "mark_guards f (call init p return c) =
     call init p return (\<lambda>s t. mark_guards f (c s t))"
  by (simp add: call_def)

lemma mark_guards_dynCall [simp]:
  "mark_guards f (dynCall init p return c) =
     dynCall init p return (\<lambda>s t. mark_guards f (c s t))"
  by (simp add: dynCall_def)

lemma mark_guards_fcall [simp]:
  "mark_guards f (fcall init p return result c) =
     fcall init p return result (\<lambda>v. mark_guards f (c v))"
  by (simp add: fcall_def)

lemma mark_guards_switch [simp]: 
  "mark_guards f (switch v vs) = 
     switch v (map (\<lambda>(V,c). (V,mark_guards f c)) vs)"
  by (induct vs) auto

lemma mark_guards_guaranteeStrip [simp]:
  "mark_guards f (guaranteeStrip f' g c) = guaranteeStrip f g (mark_guards f c)"
  by (simp add: guaranteeStrip_def)

lemma mark_guards_guards [simp]: 
  "mark_guards f (guards gs c) = guards (map (\<lambda>(f',g). (f,g)) gs) (mark_guards f c)"
  by (induct gs) auto

lemma mark_guards_while [simp]:
 "mark_guards f (while gs b c) = 
    while (map (\<lambda>(f',g). (f,g)) gs) b (mark_guards f c)"
  by (simp add: while_def) 

lemma mark_guards_whileAnno [simp]:
 "mark_guards f (whileAnno b I V c) = whileAnno b I V (mark_guards f c)"
  by (simp add: whileAnno_def while_def)

lemma mark_guards_whileAnnoG [simp]:
 "mark_guards f (whileAnnoG gs b I V c) = 
    whileAnnoG (map (\<lambda>(f',g). (f,g)) gs) b I V (mark_guards f c)"
  by (simp add: whileAnno_def whileAnnoG_def while_def) 

lemma mark_guards_specAnno [simp]:
  "mark_guards f (specAnno P c Q A) = 
    specAnno P (\<lambda>s. mark_guards f (c undefined)) Q A"
  by (simp add: specAnno_def)

lemmas mark_guards_simps = mark_guards.simps mark_guards_raise 
  mark_guards_condCatch mark_guards_bind mark_guards_bseq mark_guards_block
  mark_guards_dynCall mark_guards_fcall mark_guards_switch 
  mark_guards_guaranteeStrip guaranteeStripPair_split_conv mark_guards_guards
  mark_guards_while mark_guards_whileAnno mark_guards_whileAnnoG
  mark_guards_specAnno

definition is_Guard:: "('s,'p,'f) com \<Rightarrow> bool"
  where "is_Guard c = (case c of Guard f g c' \<Rightarrow> True | _ \<Rightarrow> False)"
lemma is_Guard_basic_simps [simp]:
 "is_Guard Skip = False"
 "is_Guard (Basic f) = False"
 "is_Guard (Spec r) = False"
 "is_Guard (Seq c1 c2) = False"
 "is_Guard (Cond b c1 c2) = False"
 "is_Guard (While b c) = False"
 "is_Guard (Call p) = False"
 "is_Guard (DynCom C) = False"
 "is_Guard (Guard F g c) = True"
 "is_Guard (Throw) = False"
 "is_Guard (Catch c1 c2) = False"
 "is_Guard (raise f) = False"
 "is_Guard (condCatch c1 b c2) = False"
 "is_Guard (bind e cv) = False"
 "is_Guard (bseq c1 c2) = False"
 "is_Guard (block init bdy return cont) = False"
 "is_Guard (call init p return cont) = False"
 "is_Guard (dynCall init P return cont) = False"
 "is_Guard (fcall init p return result cont') = False"
 "is_Guard (whileAnno b I V c) = False"
 "is_Guard (guaranteeStrip F g c) = True"
  by (auto simp add: is_Guard_def raise_def condCatch_def bind_def bseq_def
          block_def call_def dynCall_def fcall_def whileAnno_def guaranteeStrip_def)


lemma is_Guard_switch [simp]:
 "is_Guard (switch v Vc) = False"
  by (induct Vc) auto

lemmas is_Guard_simps = is_Guard_basic_simps is_Guard_switch

primrec dest_Guard:: "('s,'p,'f) com \<Rightarrow> ('f \<times> 's set \<times> ('s,'p,'f) com)"
  where "dest_Guard (Guard f g c) = (f,g,c)"

lemma dest_Guard_guaranteeStrip [simp]: "dest_Guard (guaranteeStrip f g c) = (f,g,c)"
  by (simp add: guaranteeStrip_def)

lemmas dest_Guard_simps = dest_Guard.simps dest_Guard_guaranteeStrip

subsubsection {* Merging Guards: @{text merge_guards}*}

primrec merge_guards:: "('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com"
where
"merge_guards Skip = Skip" |
"merge_guards (Basic g) = Basic g" |
"merge_guards (Spec r) = Spec r" |
"merge_guards (Seq c\<^sub>1 c\<^sub>2)  = (Seq (merge_guards c\<^sub>1) (merge_guards c\<^sub>2))" |
"merge_guards (Cond b c\<^sub>1 c\<^sub>2) = Cond b (merge_guards c\<^sub>1) (merge_guards c\<^sub>2)" |
"merge_guards (While b c) = While b (merge_guards c)" |
"merge_guards (Call p) = Call p" |
"merge_guards (DynCom c) = DynCom (\<lambda>s. (merge_guards (c s)))" |
(*"merge_guards (Guard f g c) = 
    (case (merge_guards c) of
      Guard f' g' c' \<Rightarrow> if f=f' then Guard f (g \<inter> g') c' 
                        else Guard f g (Guard f' g' c')
     | _ \<Rightarrow>  Guard f g (merge_guards c))"*)
(* the following version works better with derived language constructs *)
"merge_guards (Guard f g c) = 
    (let c' = (merge_guards c)
     in if is_Guard c' 
        then let (f',g',c'') = dest_Guard c' 
             in if f=f' then Guard f (g \<inter> g') c'' 
                        else Guard f g (Guard f' g' c'')
        else Guard f g c')" |
"merge_guards Throw = Throw" |
"merge_guards (Catch c\<^sub>1 c\<^sub>2) = Catch (merge_guards c\<^sub>1) (merge_guards c\<^sub>2)"

lemma merge_guards_res_Skip: "merge_guards c = Skip \<Longrightarrow> c = Skip"
  by (cases c) (auto split: com.splits split_if_asm simp add: is_Guard_def Let_def)

lemma merge_guards_res_Basic: "merge_guards c = Basic f \<Longrightarrow> c = Basic f"
  by (cases c) (auto split: com.splits split_if_asm simp add: is_Guard_def Let_def)

lemma merge_guards_res_Spec: "merge_guards c = Spec r \<Longrightarrow> c = Spec r"
  by (cases c) (auto split: com.splits split_if_asm simp add: is_Guard_def Let_def)

lemma merge_guards_res_Seq: "merge_guards c = Seq c1 c2 \<Longrightarrow> 
    \<exists>c1' c2'. c = Seq c1' c2' \<and> merge_guards c1' = c1 \<and> merge_guards c2' = c2"
  by (cases c) (auto split: com.splits split_if_asm simp add: is_Guard_def Let_def)

lemma merge_guards_res_Cond: "merge_guards c = Cond b c1 c2 \<Longrightarrow> 
    \<exists>c1' c2'. c = Cond b c1' c2' \<and> merge_guards c1' = c1 \<and> merge_guards c2' = c2"
  by (cases c) (auto split: com.splits split_if_asm simp add: is_Guard_def Let_def)

lemma merge_guards_res_While: "merge_guards c = While b c' \<Longrightarrow> 
    \<exists>c''. c = While b c''  \<and> merge_guards c'' = c'"
  by (cases c) (auto split: com.splits split_if_asm simp add: is_Guard_def Let_def)

lemma merge_guards_res_Call: "merge_guards c = Call p \<Longrightarrow> c = Call p"
  by (cases c) (auto split: com.splits split_if_asm simp add: is_Guard_def Let_def)

lemma merge_guards_res_DynCom: "merge_guards c = DynCom c' \<Longrightarrow> 
    \<exists>c''. c = DynCom c''  \<and> (\<lambda>s. (merge_guards (c'' s))) = c'"
  by (cases c) (auto split: com.splits split_if_asm simp add: is_Guard_def Let_def)

lemma merge_guards_res_Throw: "merge_guards c = Throw \<Longrightarrow> c = Throw"
  by (cases c) (auto split: com.splits split_if_asm simp add: is_Guard_def Let_def)

lemma merge_guards_res_Catch: "merge_guards c = Catch c1 c2 \<Longrightarrow> 
    \<exists>c1' c2'. c = Catch c1' c2' \<and> merge_guards c1' = c1 \<and> merge_guards c2' = c2"
  by (cases c) (auto split: com.splits split_if_asm simp add: is_Guard_def Let_def)

lemma merge_guards_res_Guard: 
 "merge_guards c = Guard f g c' \<Longrightarrow> \<exists>c'' f' g'. c = Guard f' g' c''"
  by (cases c) (auto split: com.splits split_if_asm simp add: is_Guard_def Let_def)

lemmas merge_guards_res_simps = merge_guards_res_Skip merge_guards_res_Basic 
 merge_guards_res_Spec merge_guards_res_Seq merge_guards_res_Cond 
 merge_guards_res_While merge_guards_res_Call
 merge_guards_res_DynCom merge_guards_res_Throw merge_guards_res_Catch 
 merge_guards_res_Guard 

lemma merge_guards_raise: "merge_guards (raise g) = raise g"
  by (simp add: raise_def)

lemma merge_guards_condCatch [simp]:
  "merge_guards (condCatch c1 b c2) = 
    condCatch (merge_guards c1) b (merge_guards c2)"
  by (simp add: condCatch_def)

lemma merge_guards_bind [simp]:
  "merge_guards (bind e c) = bind e (\<lambda>v. merge_guards (c v))"
  by (simp add: bind_def)

lemma merge_guards_bseq [simp]:
  "merge_guards (bseq c1 c2) = bseq (merge_guards c1) (merge_guards c2)"
  by (simp add: bseq_def)

lemma merge_guards_block [simp]:
  "merge_guards (block init bdy return c) =
    block init (merge_guards bdy) return (\<lambda>s t. merge_guards (c s t))"
  by (simp add: block_def)

lemma merge_guards_call [simp]:
  "merge_guards (call init p return c) =
     call init p return (\<lambda>s t. merge_guards (c s t))"
  by (simp add: call_def)

lemma merge_guards_dynCall [simp]:
  "merge_guards (dynCall init p return c) =
     dynCall init p return (\<lambda>s t. merge_guards (c s t))"
  by (simp add: dynCall_def)

lemma merge_guards_fcall [simp]:
  "merge_guards (fcall init p return result c) =
     fcall init p return result (\<lambda>v. merge_guards (c v))"
  by (simp add: fcall_def)

lemma merge_guards_switch [simp]: 
  "merge_guards (switch v vs) = 
     switch v (map (\<lambda>(V,c). (V,merge_guards c)) vs)"
  by (induct vs) auto

lemma merge_guards_guaranteeStrip [simp]: 
  "merge_guards (guaranteeStrip f g c) = 
    (let c' = (merge_guards c)
     in if is_Guard c' 
        then let (f',g',c') = dest_Guard c' 
             in if f=f' then Guard f (g \<inter> g') c' 
                        else Guard f g (Guard f' g' c')
        else Guard f g c')"
  by (simp add: guaranteeStrip_def)

lemma merge_guards_whileAnno [simp]:
 "merge_guards (whileAnno b I V c) = whileAnno b I V (merge_guards c)"
  by (simp add: whileAnno_def while_def)

lemma merge_guards_specAnno [simp]:
  "merge_guards (specAnno P c Q A) = 
    specAnno P (\<lambda>s. merge_guards (c undefined)) Q A"
  by (simp add: specAnno_def)

text {* @{term "merge_guards"} for guard-lists as in @{const guards}, @{const while}
 and @{const whileAnnoG} may have funny effects since the guard-list has to
 be merged with the body statement too.*}

lemmas merge_guards_simps = merge_guards.simps merge_guards_raise 
  merge_guards_condCatch merge_guards_bind merge_guards_bseq merge_guards_block
  merge_guards_dynCall merge_guards_fcall merge_guards_switch 
  merge_guards_guaranteeStrip merge_guards_whileAnno merge_guards_specAnno

primrec noguards:: "('s,'p,'f) com \<Rightarrow> bool"
where
"noguards Skip = True" |
"noguards (Basic f) = True" |
"noguards (Spec r ) = True" |
"noguards (Seq c\<^sub>1 c\<^sub>2)  = (noguards c\<^sub>1 \<and> noguards c\<^sub>2)" |
"noguards (Cond b c\<^sub>1 c\<^sub>2) = (noguards c\<^sub>1 \<and> noguards c\<^sub>2)" |
"noguards (While b c) = (noguards c)" |
"noguards (Call p) = True" |
"noguards (DynCom c) = (\<forall>s. noguards (c s))" |
"noguards (Guard f g c) = False" |
"noguards Throw = True" |
"noguards (Catch c\<^sub>1 c\<^sub>2) = (noguards c\<^sub>1 \<and> noguards c\<^sub>2)"

lemma noguards_strip_guards: "noguards (strip_guards UNIV c)"
  by (induct c) auto

primrec nothrows:: "('s,'p,'f) com \<Rightarrow> bool"
where
"nothrows Skip = True" |
"nothrows (Basic f) = True" |
"nothrows (Spec r) = True" |
"nothrows (Seq c\<^sub>1 c\<^sub>2)  = (nothrows c\<^sub>1 \<and> nothrows c\<^sub>2)" |
"nothrows (Cond b c\<^sub>1 c\<^sub>2) = (nothrows c\<^sub>1 \<and> nothrows c\<^sub>2)" |
"nothrows (While b c) = nothrows c" |
"nothrows (Call p) = True" |
"nothrows (DynCom c) = (\<forall>s. nothrows (c s))" |
"nothrows (Guard f g c) = nothrows c" |
"nothrows Throw = False" |
"nothrows (Catch c\<^sub>1 c\<^sub>2) = (nothrows c\<^sub>1 \<and> nothrows c\<^sub>2)"

subsubsection {* Intersecting Guards: @{text "c\<^sub>1 \<inter>\<^sub>g c\<^sub>2"}*}

inductive_set com_rel ::"(('s,'p,'f) com \<times> ('s,'p,'f) com) set"
where
  "(c1, Seq c1 c2) \<in> com_rel"
| "(c2, Seq c1 c2) \<in> com_rel"
| "(c1, Cond b c1 c2) \<in> com_rel"
| "(c2, Cond b c1 c2) \<in> com_rel"
| "(c, While b c) \<in> com_rel"
| "(c x, DynCom c) \<in> com_rel"
| "(c, Guard f g c) \<in> com_rel"
| "(c1, Catch c1 c2) \<in> com_rel"
| "(c2, Catch c1 c2) \<in> com_rel"

inductive_cases com_rel_elim_cases:
 "(c, Skip) \<in> com_rel"
 "(c, Basic f) \<in> com_rel"
 "(c, Spec r) \<in> com_rel"
 "(c, Seq c1 c2) \<in> com_rel"
 "(c, Cond b c1 c2) \<in> com_rel"
 "(c, While b c1) \<in> com_rel"
 "(c, Call p) \<in> com_rel"
 "(c, DynCom c1) \<in> com_rel"
 "(c, Guard f g c1) \<in> com_rel"
 "(c, Throw) \<in> com_rel"
 "(c, Catch c1 c2) \<in> com_rel"

lemma wf_com_rel: "wf com_rel"
apply (rule wfUNIVI)
apply (induct_tac x)
apply           (erule allE, erule mp, (rule allI impI)+, erule com_rel_elim_cases)
apply          (erule allE, erule mp, (rule allI impI)+, erule com_rel_elim_cases)
apply         (erule allE, erule mp, (rule allI impI)+, erule com_rel_elim_cases)
apply        (erule allE, erule mp, (rule allI impI)+, erule com_rel_elim_cases,
               simp,simp)
apply       (erule allE, erule mp, (rule allI impI)+, erule com_rel_elim_cases,
              simp,simp)
apply      (erule allE, erule mp, (rule allI impI)+, erule com_rel_elim_cases,simp)
apply     (erule allE, erule mp, (rule allI impI)+, erule com_rel_elim_cases)
apply    (erule allE, erule mp, (rule allI impI)+, erule com_rel_elim_cases,simp)
apply   (erule allE, erule mp, (rule allI impI)+, erule com_rel_elim_cases,simp)
apply  (erule allE, erule mp, (rule allI impI)+, erule com_rel_elim_cases)
apply (erule allE, erule mp, (rule allI impI)+, erule com_rel_elim_cases,simp,simp)
done

consts inter_guards:: "('s,'p,'f) com \<times> ('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com option"

abbreviation 
  inter_guards_syntax :: "('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com option"
           ("_ \<inter>\<^sub>g _" [20,20] 19)
  where "c \<inter>\<^sub>g d == inter_guards (c,d)" 

recdef inter_guards "inv_image com_rel fst" 
"(Skip \<inter>\<^sub>g Skip) = Some Skip"

"(Basic f1 \<inter>\<^sub>g Basic f2) = (if (f1=f2) then Some (Basic f1) else None)"
"(Spec r1 \<inter>\<^sub>g Spec r2) = (if (r1=r2) then Some (Spec r1) else None)"
"(Seq a1 a2 \<inter>\<^sub>g Seq b1 b2) = 
   (case (a1 \<inter>\<^sub>g b1) of
      None \<Rightarrow> None
    | Some c1 \<Rightarrow> (case (a2 \<inter>\<^sub>g b2) of
                    None \<Rightarrow> None
                  | Some c2 \<Rightarrow> Some (Seq c1 c2)))"

"(Cond cnd1 t1 e1 \<inter>\<^sub>g Cond cnd2 t2 e2) = 
   (if (cnd1=cnd2) 
    then (case (t1 \<inter>\<^sub>g t2) of 
            None \<Rightarrow> None
          | Some t \<Rightarrow> (case (e1 \<inter>\<^sub>g e2) of
                         None \<Rightarrow> None
                       | Some e \<Rightarrow> Some (Cond cnd1 t e)))
    else None)"

"(While cnd1 c1 \<inter>\<^sub>g While cnd2 c2) = 
    (if (cnd1=cnd2 )
     then (case (c1 \<inter>\<^sub>g c2) of
             None \<Rightarrow> None
           | Some c \<Rightarrow> Some (While cnd1 c))
     else None)"

"(Call p1 \<inter>\<^sub>g Call p2) = 
   (if p1 = p2
    then Some (Call p1)
    else None)"

"(DynCom P1 \<inter>\<^sub>g DynCom P2) = 
   (if (\<forall>s. ((P1 s) \<inter>\<^sub>g (P2 s)) \<noteq> None)
   then Some (DynCom (\<lambda>s.  the ((P1 s) \<inter>\<^sub>g (P2 s))))
   else None)"

"(Guard m1 g1 c1 \<inter>\<^sub>g Guard m2 g2 c2) = 
   (if m1=m2 then
       (case (c1 \<inter>\<^sub>g c2) of
          None \<Rightarrow> None
        | Some c \<Rightarrow> Some (Guard m1 (g1 \<inter> g2) c))
    else None)"

"(Throw \<inter>\<^sub>g Throw) = Some Throw"
"(Catch a1 a2 \<inter>\<^sub>g Catch b1 b2) = 
   (case (a1 \<inter>\<^sub>g b1) of
      None \<Rightarrow> None
    | Some c1 \<Rightarrow> (case (a2 \<inter>\<^sub>g b2) of
                    None \<Rightarrow> None
                  | Some c2 \<Rightarrow> Some (Catch c1 c2)))" 
"(c \<inter>\<^sub>g d) = None"

(hints cong add: option.case_cong if_cong  
       recdef_wf: wf_com_rel simp: com_rel.intros)

lemma inter_guards_strip_eq:
  "\<And>c. (c1 \<inter>\<^sub>g c2) = Some c  \<Longrightarrow> 
    (strip_guards UNIV c = strip_guards UNIV c1) \<and> 
    (strip_guards UNIV c = strip_guards UNIV c2)"
apply (induct c1 c2 rule: inter_guards.induct) 
prefer 8 
apply (simp split: split_if_asm)
apply hypsubst
apply simp
apply (rule ext)
apply (erule_tac x=s in allE, erule exE)
apply (erule_tac x=s in allE)
apply fastforce
apply (fastforce split: option.splits split_if_asm)+
done

lemma inter_guards_sym: "\<And>c. (c1 \<inter>\<^sub>g c2) = Some c \<Longrightarrow> (c2 \<inter>\<^sub>g c1) = Some c"
apply (induct c1 c2 rule: inter_guards.induct)
apply (simp_all)
prefer 7
apply (simp split: split_if_asm add: not_None_eq)
apply (rule conjI)
apply  (clarsimp)
apply  (rule ext)
apply  (erule_tac x=s in allE)+
apply  fastforce
apply fastforce
apply (fastforce split: option.splits split_if_asm)+
done


lemma inter_guards_Skip: "(Skip \<inter>\<^sub>g c2) = Some c = (c2=Skip \<and> c=Skip)"
  by (cases c2) auto

lemma inter_guards_Basic: 
  "((Basic f) \<inter>\<^sub>g c2) = Some c = (c2=Basic f \<and> c=Basic f)"
  by (cases c2) auto

lemma inter_guards_Spec: 
  "((Spec r) \<inter>\<^sub>g c2) = Some c = (c2=Spec r \<and> c=Spec r)"
  by (cases c2) auto

lemma inter_guards_Seq: 
  "(Seq a1 a2 \<inter>\<^sub>g c2) = Some c = 
     (\<exists>b1 b2 d1 d2. c2=Seq b1 b2 \<and> (a1 \<inter>\<^sub>g b1) = Some d1 \<and> 
        (a2 \<inter>\<^sub>g b2) = Some d2 \<and> c=Seq d1 d2)"
  by (cases c2) (auto split: option.splits)

lemma inter_guards_Cond:
  "(Cond cnd t1 e1 \<inter>\<^sub>g c2) = Some c =
     (\<exists>t2 e2 t e. c2=Cond cnd t2 e2 \<and> (t1 \<inter>\<^sub>g t2) = Some t \<and> 
        (e1 \<inter>\<^sub>g e2) = Some e \<and> c=Cond cnd t e)"  
  by (cases c2) (auto split: option.splits)

lemma inter_guards_While:
 "(While cnd bdy1 \<inter>\<^sub>g c2) = Some c =
     (\<exists>bdy2 bdy. c2 =While cnd bdy2 \<and> (bdy1 \<inter>\<^sub>g bdy2) = Some bdy \<and>
       c=While cnd bdy)"
  by (cases c2) (auto split: option.splits split_if_asm)

lemma inter_guards_Call:
  "(Call p \<inter>\<^sub>g c2) = Some c =
     (c2=Call p \<and> c=Call p)"
  by (cases c2) (auto split: split_if_asm)

lemma inter_guards_DynCom:
  "(DynCom f1 \<inter>\<^sub>g c2) = Some c =
     (\<exists>f2. c2=DynCom f2 \<and> (\<forall>s. ((f1 s) \<inter>\<^sub>g (f2 s)) \<noteq> None) \<and>
      c=DynCom (\<lambda>s. the ((f1 s) \<inter>\<^sub>g (f2 s))))"
  by (cases c2) (auto split: split_if_asm)


lemma inter_guards_Guard:
  "(Guard f g1 bdy1 \<inter>\<^sub>g c2) = Some c =
     (\<exists>g2 bdy2 bdy. c2=Guard f g2 bdy2 \<and> (bdy1 \<inter>\<^sub>g bdy2) = Some bdy \<and>
       c=Guard f (g1 \<inter> g2) bdy)" 
  by (cases c2) (auto split: option.splits)

lemma inter_guards_Throw:
  "(Throw \<inter>\<^sub>g c2) = Some c = (c2=Throw \<and> c=Throw)"
  by (cases c2) auto

lemma inter_guards_Catch:
  "(Catch a1 a2 \<inter>\<^sub>g c2) = Some c = 
     (\<exists>b1 b2 d1 d2. c2=Catch b1 b2 \<and> (a1 \<inter>\<^sub>g b1) = Some d1 \<and> 
        (a2 \<inter>\<^sub>g b2) = Some d2 \<and> c=Catch d1 d2)"
  by (cases c2) (auto split: option.splits)


lemmas inter_guards_simps = inter_guards_Skip inter_guards_Basic inter_guards_Spec
  inter_guards_Seq inter_guards_Cond inter_guards_While inter_guards_Call
  inter_guards_DynCom inter_guards_Guard inter_guards_Throw 
  inter_guards_Catch

subsubsection {* Subset on Guards: @{text "c\<^sub>1 \<subseteq>\<^sub>g c\<^sub>2"} *} 


consts subseteq_guards:: "('s,'p,'f) com \<times> ('s,'p,'f) com \<Rightarrow> bool"

abbreviation
  subseteq_guards_syntax :: "('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com \<Rightarrow> bool"
           ("_ \<subseteq>\<^sub>g _" [20,20] 19)
  where "c \<subseteq>\<^sub>g d == subseteq_guards (c,d)"


recdef subseteq_guards "inv_image com_rel snd" 
"(Skip \<subseteq>\<^sub>g Skip) = True"
"(Basic f1 \<subseteq>\<^sub>g Basic f2) = (f1=f2)"
"(Spec r1 \<subseteq>\<^sub>g Spec r2) = (r1=r2)"
"(Seq a1 a2 \<subseteq>\<^sub>g Seq b1 b2) = ((a1 \<subseteq>\<^sub>g b1) \<and> (a2 \<subseteq>\<^sub>g b2))"
"(Cond cnd1 t1 e1 \<subseteq>\<^sub>g Cond cnd2 t2 e2) = ((cnd1=cnd2) \<and> (t1 \<subseteq>\<^sub>g t2) \<and> (e1 \<subseteq>\<^sub>g e2))"
"(While cnd1 c1 \<subseteq>\<^sub>g While cnd2 c2) = ((cnd1=cnd2) \<and> (c1 \<subseteq>\<^sub>g c2))"
"(Call p1 \<subseteq>\<^sub>g Call p2) = (p1 = p2)"
"(DynCom P1 \<subseteq>\<^sub>g DynCom P2) = (\<forall>s. ((P1 s) \<subseteq>\<^sub>g (P2 s)))"
"(Guard m1 g1 c1 \<subseteq>\<^sub>g Guard m2 g2 c2) = 
    ((m1=m2 \<and> g1=g2 \<and> (c1 \<subseteq>\<^sub>g c2)) \<or> (Guard m1 g1 c1 \<subseteq>\<^sub>g c2))"
"(c1 \<subseteq>\<^sub>g Guard m2 g2 c2) = (c1 \<subseteq>\<^sub>g c2)"

"(Throw \<subseteq>\<^sub>g Throw) = True"
"(Catch a1 a2 \<subseteq>\<^sub>g Catch b1 b2) = ((a1 \<subseteq>\<^sub>g b1) \<and> (a2 \<subseteq>\<^sub>g b2))" 
"(c \<subseteq>\<^sub>g d) = False"

(hints cong add: if_cong  
       recdef_wf: wf_com_rel simp: com_rel.intros)

lemma subseteq_guards_Skip:
 "c \<subseteq>\<^sub>g Skip \<Longrightarrow> c = Skip"
  by (cases c) (auto)

lemma subseteq_guards_Basic:
 "c \<subseteq>\<^sub>g Basic f \<Longrightarrow> c = Basic f"
  by (cases c) (auto)

lemma subseteq_guards_Spec:
 "c \<subseteq>\<^sub>g Spec r \<Longrightarrow> c = Spec r"
  by (cases c) (auto)

lemma subseteq_guards_Seq:
  "c \<subseteq>\<^sub>g Seq c1 c2 \<Longrightarrow> \<exists>c1' c2'. c=Seq c1' c2' \<and> (c1' \<subseteq>\<^sub>g c1) \<and> (c2' \<subseteq>\<^sub>g c2)"
  by (cases c) (auto)

lemma subseteq_guards_Cond:
  "c \<subseteq>\<^sub>g Cond b c1 c2 \<Longrightarrow> \<exists>c1' c2'. c=Cond b c1' c2' \<and> (c1' \<subseteq>\<^sub>g c1) \<and> (c2' \<subseteq>\<^sub>g c2)"
  by (cases c) (auto)

lemma subseteq_guards_While:
  "c \<subseteq>\<^sub>g While b c' \<Longrightarrow> \<exists>c''. c=While b c'' \<and> (c'' \<subseteq>\<^sub>g c')"
  by (cases c) (auto)

lemma subseteq_guards_Call:
 "c \<subseteq>\<^sub>g Call p \<Longrightarrow> c = Call p"
  by (cases c) (auto)

lemma subseteq_guards_DynCom:
  "c \<subseteq>\<^sub>g DynCom C \<Longrightarrow> \<exists>C'. c=DynCom C' \<and> (\<forall>s. C' s \<subseteq>\<^sub>g C s)"
  by (cases c) (auto)

lemma subseteq_guards_Guard:
  "c \<subseteq>\<^sub>g Guard f g c'  \<Longrightarrow> 
     (c \<subseteq>\<^sub>g c') \<or> (\<exists>c''. c=Guard f g c'' \<and> (c'' \<subseteq>\<^sub>g c'))"
  by (cases c) (auto split: split_if_asm)

lemma subseteq_guards_Throw:
 "c \<subseteq>\<^sub>g Throw \<Longrightarrow> c = Throw"
  by (cases c) (auto)

lemma subseteq_guards_Catch:
  "c \<subseteq>\<^sub>g Catch c1 c2 \<Longrightarrow> \<exists>c1' c2'. c=Catch c1' c2' \<and> (c1' \<subseteq>\<^sub>g c1) \<and> (c2' \<subseteq>\<^sub>g c2)"
  by (cases c) (auto)

lemmas subseteq_guardsD = subseteq_guards_Skip subseteq_guards_Basic
 subseteq_guards_Spec subseteq_guards_Seq subseteq_guards_Cond subseteq_guards_While
 subseteq_guards_Call subseteq_guards_DynCom subseteq_guards_Guard
 subseteq_guards_Throw subseteq_guards_Catch 

lemma subseteq_guards_Guard': 
  "Guard f b c \<subseteq>\<^sub>g d \<Longrightarrow> \<exists>f' b' c'. d=Guard f' b' c'"
apply (cases d)
apply auto
done

lemma subseteq_guards_refl: "c \<subseteq>\<^sub>g c"
  by (induct c) auto

(* Antisymmetry and transitivity should hold as well\<dots> *)

end
