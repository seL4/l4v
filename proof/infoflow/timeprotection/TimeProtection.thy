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
type_synonym 'fch_cachedness fch = "address \<Rightarrow> 'fch_cachedness"
type_synonym 'pch_cachedness pch = "address \<Rightarrow> 'pch_cachedness"
type_synonym ('fch,'pch) cache_impact = "address \<Rightarrow> 'fch \<Rightarrow> 'pch \<Rightarrow> 'fch \<times> 'pch"

type_synonym time = nat

typedecl regs
typedecl other_state
typedecl domain
typedecl colour

record ('fch,'pch) state =
  fch :: 'fch \<comment> \<open> flushable cache\<close>
  pch :: 'pch \<comment> \<open> partitionable cache \<close>
  tm :: time
  regs :: regs
  other_state :: other_state



locale time_protection =
  fixes collision_set :: "address \<Rightarrow> address set"

  fixes read_impact :: "('fch_cachedness fch, 'pch_cachedness pch) cache_impact"
  assumes pch_partitioned_read: "a2 \<notin> collision_set a1 \<Longrightarrow> p a2 = snd (read_impact a1 f p) a2"

  fixes write_impact :: "('fch_cachedness fch, 'pch_cachedness pch) cache_impact"
  assumes pch_partitioned_write: "a2 \<notin> collision_set a1 \<Longrightarrow> p a2 = snd (write_impact a1 f p) a2"

  fixes read_cycles  :: "'fch_cachedness \<Rightarrow> 'pch_cachedness \<Rightarrow> time"
  fixes write_cycles :: "'fch_cachedness \<Rightarrow> 'pch_cachedness \<Rightarrow> time"

  fixes do_read :: "address \<Rightarrow> other_state \<Rightarrow> regs \<Rightarrow> regs"
  fixes do_write :: "address \<Rightarrow> other_state \<Rightarrow> regs \<Rightarrow> other_state"

  fixes store_time :: "time \<Rightarrow> regs \<Rightarrow> regs"

  fixes padding_regs_impact :: "time \<Rightarrow> regs \<Rightarrow> regs"

  fixes empty_fch :: "'fch_cachedness fch"
  fixes fch_flush_cycles :: "'fch_cachedness fch \<Rightarrow> time" \<comment> \<open>could this be dependent on anything else?\<close>

  fixes do_pch_flush :: "'pch_cachedness pch \<Rightarrow> address set \<Rightarrow> 'pch_cachedness pch"
  \<comment> \<open> this will probably need some restriction about its relationship with collision_set\<close>

  fixes addr_domain :: "address \<Rightarrow> domain" \<comment> \<open>for each address, this is the security domain\<close>
  fixes addr_colour :: "address \<Rightarrow> colour" \<comment> \<open>for each address, this is the cache colour\<close>
  fixes colour_domain :: "colour \<Rightarrow> domain"
  assumes colours_not_shared: "colour_domain c1 \<noteq> colour_domain c2 \<Longrightarrow> c1 \<noteq> c2"
  assumes addr_domain_valid: "addr_domain a = colour_domain (addr_colour a)" \<comment> \<open>do we assert this here
  or just put it in the type so it has to be asserted before instantiation? or assert it differently
  later?\<close>
  fixes current_domain :: "other_state \<Rightarrow> domain"

  fixes external_uwr :: "domain \<Rightarrow> (other_state \<times> other_state) set"
  assumes external_uwr_same_domain: "(s1, s2) \<in> external_uwr d \<Longrightarrow> current_domain s1 = current_domain s2"
\<comment> \<open>we will probably needs lots more info about this external uwr later on\<close>

  fixes pch_flush_cycles :: "'pch_cachedness pch \<Rightarrow> address set \<Rightarrow> time" \<comment> \<open>could this be dependent on anything else?\<close>
begin

definition current_domain' where "current_domain' s = current_domain (other_state s)"

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

definition pch_same_for_domain :: "domain \<Rightarrow> 'pch_cachedness pch \<Rightarrow> 'pch_cachedness pch \<Rightarrow> bool"
  where
 "pch_same_for_domain d p1 p2 \<equiv> \<forall> a. addr_domain a = d \<longrightarrow> p1 a = p2 a"

definition uwr_running :: "domain \<Rightarrow>
  (('fch_cachedness fch, 'pch_cachedness pch) state \<times>
   ('fch_cachedness fch, 'pch_cachedness pch) state) set"
  where
  "uwr_running d \<equiv> {(s1, s2). fch s1 = fch s2
                            \<and> pch_same_for_domain d (pch s1) (pch s2)
                            \<and> tm s1 = tm s2
                            \<and> regs s1 = regs s2
                            \<and> (other_state s1, other_state s2) \<in> external_uwr d }"
\<comment> \<open>how do we know we have the same program?\<close>


definition uwr_notrunning :: "domain \<Rightarrow>
  (('fch_cachedness fch, 'pch_cachedness pch) state \<times>
   ('fch_cachedness fch, 'pch_cachedness pch) state) set"
  where
  "uwr_notrunning d \<equiv> {(s1, s2). pch_same_for_domain d (pch s1) (pch s2)
                               \<and> (other_state s1, other_state s2) \<in> external_uwr d }"
\<comment> \<open>external uwr needs to be held in the right conditions as an axiom\<close>

definition uwr :: "domain \<Rightarrow>
  (('fch_cachedness fch, 'pch_cachedness pch) state \<times>
   ('fch_cachedness fch, 'pch_cachedness pch) state) set"
  where
  "uwr d \<equiv> {(s1, s2). if (current_domain' s1 = d)
                      then (s1, s2) \<in> uwr_running d
                      else (s1, s2) \<in> uwr_notrunning d }"

(* notes about confidentiality properties with this model:
   
  for some step (let's say the user step for example), for a step of the NOT CURRENTLY RUNNING
  domain d:
  - we have two programs derived from touched_addresses - may not be the same touched_addresses (? ? ?)
    - we may not have concrete touched_addresses-es - we may overapprox this to the whole currently running domain
  - these touched_addresses does NOT contain any addresses from d
  - initial states s and t hold uwr_notrunning
  - we execute both programs
  - new state s' and t' hold uwr_notrunning
  - this will rely on infoflow properties of external_uwr

  ...and for a step of the CURRENTLY RUNNING domain d:
  - we have two programs derived from the same touched_addresses
    - these have to be the same program (so we need to know that the choice depends on stuff in
      other_state in the external uwr)
  - that touched_addresses ONLY contains addresses in d
  - initial states s and t hold uwr_running
  - we execute the program on both states
  - new states s' and t' hold uwr_running
  - this will rely on infoflow properties of external_uwr
  
  


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
  instr_step :: "instr \<Rightarrow>
    ('fch_cachedness fch, 'pch_cachedness pch) state \<Rightarrow>
    ('fch_cachedness fch, 'pch_cachedness pch) state" where
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

primrec instr_multistep :: "program \<Rightarrow>
  ('fch_cachedness fch, 'pch_cachedness pch) state \<Rightarrow>
  ('fch_cachedness fch, 'pch_cachedness pch) state" where
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
end