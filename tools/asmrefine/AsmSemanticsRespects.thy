(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory AsmSemanticsRespects

imports "GlobalsSwap"

begin

definition
  asm_semantics_protects_globs
    :: "('g \<Rightarrow> heap_raw_state) \<Rightarrow> ((heap_raw_state \<Rightarrow> heap_raw_state) \<Rightarrow> 'g \<Rightarrow> 'g)
    \<Rightarrow> ('g \<Rightarrow> 'a)
    \<Rightarrow> (string \<Rightarrow> addr) \<Rightarrow> ('g global_data list)
    \<Rightarrow> bool"
where
  "asm_semantics_protects_globs mem memu ms symtab xs
    \<equiv> (let sw = globals_swap mem memu symtab xs
        in (\<forall>v v' s m' ms' specname. (v', m', ms')
            \<in> asm_semantics specname v
                (hrs_mem (mem (sw s)), ms s)
           \<longrightarrow> const_globals_in_memory symtab xs
                (hrs_mem (mem (sw (sw s))))
           \<longrightarrow> const_globals_in_memory symtab xs
                (hrs_mem (mem (sw (memu (hrs_mem_update (\<lambda>_. m')) (sw s)))))))"

abbreviation(input)
  asm_ops_are_swap
    :: "('g \<Rightarrow> heap_raw_state) \<Rightarrow> ((heap_raw_state \<Rightarrow> heap_raw_state) \<Rightarrow> 'g \<Rightarrow> 'g)
    \<Rightarrow> ('g \<Rightarrow> 'a) \<Rightarrow> (('a \<Rightarrow> 'a) \<Rightarrow> 'g \<Rightarrow> 'g)
    \<Rightarrow> (string \<Rightarrow> addr) \<Rightarrow> ('g \<Rightarrow> 'b) \<Rightarrow> ('g global_data list)
    \<Rightarrow> bool"
where
  "asm_ops_are_swap mem memu ms msu symtab gdata xs
    \<equiv> (let sw = globals_swap mem memu symtab xs
      in (\<forall>s. asm_fetch s = (hrs_mem (mem (sw s)), ms (sw s)))
        \<and> (\<forall>v s. asm_store gdata v s = sw (msu (\<lambda>_. snd v)
            (memu (hrs_mem_update (\<lambda>_. fst v)) (sw s))))
        \<and> asm_semantics_protects_globs mem memu ms symtab xs)"

lemma asm_semantics_protects_globs_revD[OF refl]:
  "sw = globals_swap mem memu symtab xs
    \<Longrightarrow> (v', m', ms')
            \<in> asm_semantics specname v
                (hrs_mem (mem (sw s)), ms s)
    \<Longrightarrow> asm_semantics_protects_globs mem memu ms symtab xs
            \<longrightarrow> const_globals_in_memory symtab xs
                (hrs_mem (mem (sw (sw s))))
            \<longrightarrow> const_globals_in_memory symtab xs
                (hrs_mem (mem (sw (memu (hrs_mem_update (\<lambda>_. m')) (sw s)))))"
  apply (simp add: asm_semantics_protects_globs_def Let_def)
  apply blast
  done

end
