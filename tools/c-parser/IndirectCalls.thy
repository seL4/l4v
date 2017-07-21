(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory IndirectCalls

imports
  "PrettyProgs"

begin

definition
  lookup_proc :: "(string \<Rightarrow> 'proc_addr) \<Rightarrow> ('proc_id \<rightharpoonup> string)
    \<Rightarrow> 'proc_addr \<Rightarrow> 'proc_id"
where
  "lookup_proc symtab naming x
    = (THE pid. naming pid \<noteq> None \<and> symtab (the (naming pid)) = x)"

definition
  lookup_proc_safe :: "(string \<Rightarrow> 'proc_addr) \<Rightarrow> ('proc_id \<rightharpoonup> string)
    \<Rightarrow> 'proc_addr \<Rightarrow> bool"
where
  "lookup_proc_safe symtab naming x
    = (card {pid. naming pid \<noteq> None \<and> symtab (the (naming pid)) = x} = 1)"

definition
  procs_consistent :: "(string \<Rightarrow> 'proc_addr) \<Rightarrow> ('proc_nm \<rightharpoonup> string)
    \<Rightarrow> bool"
where
  "procs_consistent symtab naming
    = (finite (dom naming)
        \<and> (\<forall>x y nm nm'. naming x = Some nm \<and> naming y = Some nm'
            \<and> symtab nm = symtab nm'
                \<longrightarrow> x = y))"

lemma procs_consistent_eq:
  "\<lbrakk> naming proc = Some nm; procs_consistent symtab naming; addr = symtab nm \<rbrakk>
    \<Longrightarrow> lookup_proc symtab naming addr = proc"
  apply (clarsimp simp: procs_consistent_def lookup_proc_def)
  apply (rule the_equality)
   apply clarsimp
  apply clarsimp
  done

lemma procs_consistent_safe:
  "\<lbrakk> naming proc = Some nm; procs_consistent symtab naming; addr = symtab nm \<rbrakk>
    \<Longrightarrow> lookup_proc_safe symtab naming addr"
  apply (clarsimp simp: procs_consistent_def lookup_proc_safe_def)
  apply (rule trans, rule arg_cong[where f=card and y="{proc}"])
   apply auto
  done

lemma hoare_indirect_call_procs_consistent:
  "\<lbrakk> naming proc = Some nm;
        \<Gamma> \<turnstile> P (call initf proc ret c) Q, A \<rbrakk>
    \<Longrightarrow> \<Gamma> \<turnstile> ({s. procs_consistent symtab naming \<and> x_fn s = symtab nm} \<inter> P)
            (dynCall initf (\<lambda>s. lookup_proc symtab naming (x_fn s))
                    ret c) Q, A"
  apply (rule hoare_complete, drule hoare_sound)
  apply (clarsimp simp: cvalid_def HoarePartialDef.valid_def)
  apply (erule exec_dynCall_Normal_elim)
  apply (simp add: procs_consistent_eq)
  apply blast
  done

end

