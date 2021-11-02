(*
 * Copyright 2021, UNSW (ABN 57 195 873 179),
 * Copyright 2021, The University of Melbourne (ABN 84 002 705 224).
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory TimeProtection
imports "Word_Lib.WordSetup"
begin

(* or something *)
type_synonym address = "machine_word"



(*
     cache(s)
     time
     other_state
     regs
*)

(*
  FLUSHABLE
  everything changes it somehow
  it affects everything

  PARTITIONABLE
  address \<Rightarrow> time

  the cache touch fn, given some 'a'


cache impact fn
inputs:
  - address
  - fch
  - pch
outputs:
  - new fch
  - new pch
  - time taken
*)



\<comment> \<open> flushable (fch) and partitionable (pch) caches\<close>
typedecl fch_cachedness
typedecl pch_cachedness
type_synonym fch = "address \<Rightarrow> fch_cachedness"
type_synonym pch = "address \<Rightarrow> pch_cachedness"

type_synonym time = nat

typedecl regs
typedecl other_state


record state =
  fch :: fch \<comment> \<open> flushable cache\<close>
  pch :: pch \<comment> \<open> partitionable cache \<close>
  tm :: time
  regs :: regs
  other_state :: other_state




type_synonym cache_impact = "address \<Rightarrow> fch \<Rightarrow> pch \<Rightarrow> fch \<times> pch"

axiomatization collision_set :: "address \<Rightarrow> address set"

axiomatization read_impact :: cache_impact
  where pch_partitioned_read: "a2 \<notin> collision_set a1 \<Longrightarrow> p a2 = snd (read_impact a1 f p) a2"

axiomatization write_impact :: cache_impact
  where pch_partitioned_write: "a2 \<notin> collision_set a1 \<Longrightarrow> p a2 = snd (write_impact a1 f p) a2"

axiomatization read_cycles  :: "fch_cachedness \<Rightarrow> pch_cachedness \<Rightarrow> time"
axiomatization write_cycles :: "fch_cachedness \<Rightarrow> pch_cachedness \<Rightarrow> time"

axiomatization do_read :: "address \<Rightarrow> other_state \<Rightarrow> regs \<Rightarrow> regs"
axiomatization do_write :: "address \<Rightarrow> other_state \<Rightarrow> regs \<Rightarrow> other_state"

axiomatization store_time :: "time \<Rightarrow> regs \<Rightarrow> regs"

axiomatization padding_regs_impact :: "time \<Rightarrow> regs \<Rightarrow> regs"

axiomatization empty_fch :: fch
axiomatization fch_flush_cycles :: "fch \<Rightarrow> time" \<comment> \<open>could this be dependent on anything else?\<close>

axiomatization do_pch_flush :: "pch \<Rightarrow> address set \<Rightarrow> pch"
\<comment> \<open> this will probably need some restriction about its relationship with collision_set\<close>

axiomatization pch_flush_cycles :: "pch \<Rightarrow> address set \<Rightarrow> time" \<comment> \<open>could this be dependent on anything else?\<close>


(*

  KSHARED
  - some concrete set of addresses that spans various colours
  - kernel steps may access these addresses - therefore there are time flows through pch
  - we make the pch of all these addresses deterministic at domain-switch
  - we may say that kshared includes all of the collision sets within itself




  UWR u (CURRENTLY RUNNNING)
  - all of fch
  - pch (for addresses in colour(u))
    - user transitions: only above
    - kernel transitions: also addresses in kshared
  - tm 
  - all of regs
  - other_state (according to external UWR u)

  UWR u (NOT RUNNNING)
  - none of fch
  - pch (for addresses in colour(u))
    - user transitions: only above
    - kernel transitions: also addresses in kshared
  - none of tm
  - none of regs
  - other_state (according to external UWR u)


  every step maintains external UWR u

*)

(*
 - if we have some types of step:
   - kentry
   - kexit 
   - etc

 - 

 - for any step, touched_addresses is only in the current domain

*)



(*
  read process:
  - time step from read_time
  - impact using read_impact
*)

(* now we make some basic isntructions, which contain addresses etc *)
datatype instr = IRead address
               | IWrite address
               | IRegs "regs \<Rightarrow> regs"
               | IFlushL1
               | IFlushL2 "address set"
               | IReadTime
               | IPadToTime time


primrec
  instr_step :: "instr \<Rightarrow> state \<Rightarrow> state" where
 "instr_step (IRead a) s = (let (f2, p2) = read_impact a (fch s) (pch s) in
      s\<lparr>fch := f2,
        pch := p2,
        tm  := tm s + read_cycles (fch s a) (pch s a),
        regs := do_read a (other_state s) (regs s)\<rparr>)"
  | "instr_step (IWrite a) s = (let (f2, p2) = write_impact a (fch s) (pch s) in
      s\<lparr>fch := f2,
        pch := p2,
        tm  := tm s + write_cycles (fch s a) (pch s a),
        other_state := do_write a (other_state s) (regs s)\<rparr>)"
  | "instr_step (IRegs m) s =
      s\<lparr>regs := m (regs s),
        tm := tm s + 1 \<rparr>" \<comment> \<open>we increment by the smallest possible amount - different instruction
                            lengths can be encoded with strings of consecutive IRegs intructions.\<close>
  | "instr_step IReadTime s =
      s\<lparr>regs := store_time (tm s) (regs s),
        tm := tm s + 1\<rparr>"
  | "instr_step (IPadToTime t) s =     \<comment> \<open>TODO: is it possible that this changes anything other than regs? what about going backwards?\<close>
      s\<lparr>regs := padding_regs_impact t (regs s),
        tm := t\<rparr>"
  | "instr_step IFlushL1 s =
      s\<lparr>fch := empty_fch,
        tm := tm s + fch_flush_cycles (fch s)\<rparr>"
  | "instr_step (IFlushL2 as) s =
      s\<lparr>pch := do_pch_flush (pch s) as,
        tm := tm s + pch_flush_cycles (pch s) as\<rparr>"


(*
definition
  instr_step :: "instr \<Rightarrow> state \<Rightarrow> state" where
 "instr_step i s \<equiv> case i of
    IRead a \<Rightarrow> let (f2, p2) = read_impact a (fch s) (pch s) in
      s\<lparr>fch := f2,
        pch := p2,
        tm  := tm s + read_cycles (fch s a) (pch s a),
        regs := do_read a (other_state s) (regs s)\<rparr>
  | IWrite a \<Rightarrow> let (f2, p2) = write_impact a (fch s) (pch s) in
      s\<lparr>fch := f2,
        pch := p2,
        tm  := tm s + write_cycles (fch s a) (pch s a),
        other_state := do_write a (other_state s) (regs s)\<rparr>
  | IRegs m \<Rightarrow>
      s\<lparr>regs := m (regs s),
        tm := tm s + 1 \<rparr> \<comment> \<open>we increment by the smallest possible amount - different instruction
                            lengths can be encoded with strings of consecutive IRegs intructions.\<close>
  | IReadTime \<Rightarrow>
      s\<lparr>regs := store_time (tm s) (regs s),
        tm := tm s + 1\<rparr>
  | IPadToTime t \<Rightarrow>     \<comment> \<open>TODO: is it possible that this changes anything other than regs? what about going backwards?\<close>
      s\<lparr>regs := padding_regs_impact t (regs s),
        tm := t\<rparr>
  | IFlushL1 \<Rightarrow>
      s\<lparr>fch := empty_fch,
        tm := tm s + fch_flush_cycles (fch s)\<rparr>
  | IFlushL2 as \<Rightarrow>
      s\<lparr>pch := do_pch_flush (pch s) as,
        tm := tm s + pch_flush_cycles (pch s) as\<rparr>"
*)

type_synonym program = "instr list"

primrec instr_multistep :: "program \<Rightarrow> state \<Rightarrow> state" where
  "instr_multistep [] s = s"
| "instr_multistep (i#is) s = instr_multistep is (instr_step i s)"





definition
  instrs_obeying_ta :: "address set \<Rightarrow> instr set" where
 "instrs_obeying_ta ta \<equiv> {i. case i of
                            IRead a  \<Rightarrow> a \<in> ta
                          | IWrite a \<Rightarrow> a \<in> ta
                          | _        \<Rightarrow> True }"



(* these are the programs that could have created this ta *)
definition
  programs_obeying_ta :: "address set \<Rightarrow> program set" where
 "programs_obeying_ta ta \<equiv> {p. list_all (\<lambda>i. i \<in> instrs_obeying_ta ta) p}"


(*

  s  -->  t
          
  |       ||||
  v       vvvv
          
  s'      t'


*)








end