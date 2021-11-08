(*
 * Copyright 2021, UNSW (ABN 57 195 873 179),
 * Copyright 2021, The University of Melbourne (ABN 84 002 705 224).
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory TimeProtection
imports "Word_Lib.WordSetup"
  InfoFlow.Noninterference_Base
  Lib.Eisbach_Methods
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
type_synonym 'fch fch_impact = "address \<Rightarrow> 'fch \<Rightarrow> 'fch"
type_synonym ('fch,'pch) pch_impact = "address \<Rightarrow> 'fch \<Rightarrow> 'pch \<Rightarrow> 'pch"

type_synonym time = nat

typedecl regs
typedecl other_state
typedecl colour

typedecl userdomain
datatype domain = Sched | User userdomain

record ('fch_cachedness,'pch_cachedness) state =
  fch :: "'fch_cachedness fch" \<comment> \<open> flushable cache\<close>
  pch :: "'pch_cachedness pch" \<comment> \<open> partitionable cache \<close>
  tm :: time
  regs :: regs
  other_state :: other_state



locale time_protection_system = unwinding_system A s0 current_domain external_uwr policy out Sched
  for A :: "('a,other_state,unit) data_type"
  and s0 :: "other_state"
  and current_domain :: "unit \<Rightarrow> other_state \<Rightarrow> domain"
  and external_uwr :: "domain \<Rightarrow> (other_state \<times> other_state) set"
  and policy :: "(domain \<times> domain) set"
  and out :: "domain \<Rightarrow> other_state \<Rightarrow> 'p" +

  (* "(a, b) \<in> collides_in_pch" = "a may cause b to be evicted from or loaded to the pch" *)
  fixes collides_in_pch :: "address rel"
  assumes collides_with_equiv: "equiv UNIV collides_in_pch"

  fixes fch_read_impact :: "'fch_cachedness fch fch_impact"
  fixes pch_read_impact :: "('fch_cachedness fch, 'pch_cachedness pch) pch_impact"
  assumes pch_partitioned_read: "(a1, a2) \<notin> collides_in_pch \<Longrightarrow> p a2 = (pch_read_impact a1 f p) a2"
  (* if a2 can be impacted by a read from a1,
     we require that this impact depends only on the prior state of the fch
     and the prior cachedness of the rest of their collision set in the pch *)
  assumes pch_collision_read: "(a1, a2) \<in> collides_in_pch \<Longrightarrow>
    \<forall>a3. (a2, a3) \<in> collides_in_pch \<longrightarrow> pchs a3 = pcht a3 \<Longrightarrow>
    \<comment> \<open>This might be stronger than is met by hardware that just promises
        a 'random' replacement algorithm. Essentially we are requiring that
        any such 'randomness' cannot be influenced by the prior cachedness of
        addresses outside the collision set in question. \<close>
    (pch_read_impact a1 f pchs) a2 = (pch_read_impact a1 f pcht) a2"

  fixes fch_write_impact :: "'fch_cachedness fch fch_impact"
  fixes pch_write_impact :: "('fch_cachedness fch, 'pch_cachedness pch) pch_impact"
  assumes pch_partitioned_write: "(a1, a2) \<notin> collides_in_pch \<Longrightarrow> p a2 = (pch_write_impact a1 f p) a2"
  assumes pch_collision_write: "(a1, a2) \<in> collides_in_pch \<Longrightarrow>
    \<forall>a3. (a2, a3) \<in> collides_in_pch \<longrightarrow> pchs a3 = pcht a3 \<Longrightarrow>
    \<comment> \<open>The same strong requirement placing limits on the 'randomness'
        of the cache replacement algorithm as for @{term pch_collision_read}\<close>
    (pch_write_impact a1 f pchs) a2 = (pch_write_impact a1 f pcht) a2"

  fixes read_cycles  :: "'fch_cachedness \<Rightarrow> 'pch_cachedness \<Rightarrow> time"
  fixes write_cycles :: "'fch_cachedness \<Rightarrow> 'pch_cachedness \<Rightarrow> time"

  fixes do_read :: "address \<Rightarrow> other_state \<Rightarrow> regs \<Rightarrow> regs"
  fixes do_write :: "address \<Rightarrow> other_state \<Rightarrow> regs \<Rightarrow> other_state"

  fixes store_time :: "time \<Rightarrow> regs \<Rightarrow> regs"

  fixes initial_regs :: "regs"
  fixes padding_regs_impact :: "time \<Rightarrow> regs \<Rightarrow> regs"

  fixes empty_fch :: "'fch_cachedness fch"
  fixes fch_flush_cycles :: "'fch_cachedness fch \<Rightarrow> time" \<comment> \<open>could this be dependent on anything else?\<close>

  fixes initial_pch :: "'pch_cachedness pch"
  fixes do_pch_flush :: "'pch_cachedness pch \<Rightarrow> address set \<Rightarrow> 'pch_cachedness pch"
  \<comment> \<open> this will probably need some restriction about its relationship with collision_set\<close>

  fixes addr_domain :: "address \<Rightarrow> domain" \<comment> \<open>for each address, this is the security domain\<close>
  fixes addr_colour :: "address \<Rightarrow> colour" \<comment> \<open>for each address, this is the cache colour\<close>
  fixes colour_userdomain :: "colour \<Rightarrow> userdomain"
  assumes colours_not_shared: "colour_userdomain c1 \<noteq> colour_userdomain c2 \<Longrightarrow> c1 \<noteq> c2"
  assumes no_cross_colour_collisions:
    "(a1, a2) \<in> collides_in_pch \<Longrightarrow> addr_colour a1 = addr_colour a2"
  assumes addr_domain_valid: "addr_domain a = Sched
                            \<or> addr_domain a = User (colour_userdomain (addr_colour a))"
\<comment> \<open>do we assert this here
  or just put it in the type so it has to be asserted before instantiation? or assert it differently
  later?\<close>

  (* The parent locale requires current_domain to be equated by Sched uwr, which confidentiality_u
     then treats as specifying public information; assuming that it is instead equated by every
     domain's uwr arguably simplifies things without changing the strength of the property.
       Without this assumption, I expect we'll need to add the Sched uwr explicitly to the
     pre-equivalence of many lemmas; it may also be a bit harder to prove that our uwr is an
     equivalence relation without it. It may be reasonable to keep this if it holds (or can
     reasonably be made to hold) for the seL4 infoflow theory's unwinding relation. -robs. *)
  assumes external_uwr_same_domain:
    "(s1, s2) \<in> external_uwr d \<Longrightarrow> current_domain () s1 = current_domain () s2"
\<comment> \<open>we will probably needs lots more info about this external uwr\<close>

  
  
  assumes do_write_maintains_external_uwr_out:
    "addr_domain a \<noteq> d \<and> addr_domain a \<noteq> Sched \<Longrightarrow>
     (s, do_write a s r) \<in> external_uwr d"
  
  (*NOTE: we can only invoke this if we have already equalised the "regs" fields *)
  assumes do_write_maintains_external_uwr_in:
    "addr_domain a = d \<or> addr_domain a = Sched \<Longrightarrow>
     (s, t) \<in> external_uwr d \<Longrightarrow>
     (do_write a s r, do_write a t r) \<in> external_uwr d"


  fixes pch_flush_cycles :: "'pch_cachedness pch \<Rightarrow> address set \<Rightarrow> time" \<comment> \<open>could this be dependent on anything else?\<close>

  fixes touched_addrs :: "other_state \<Rightarrow> address set"
  assumes touched_addrs_inv:
    "reachable s \<Longrightarrow>
     touched_addrs s \<subseteq> {a. addr_domain a = (current_domain () s)} \<union> kernel_shared_precise"
  assumes external_uwr_same_touched_addrs:
    "(s1, s2) \<in> external_uwr d \<Longrightarrow> current_domain () s1 = d\<Longrightarrow> touched_addrs s1 = touched_addrs s2"
begin

definition all_addrs_of :: "domain \<Rightarrow> address set" where
  "all_addrs_of d = {a. addr_domain a = d}"

abbreviation current_domain' :: "('fch_cachedness,'pch_cachedness) state \<Rightarrow> domain" where
  "current_domain' s \<equiv> current_domain () (other_state s)"

abbreviation touched_addrs' :: "('fch_cachedness,'pch_cachedness) state \<Rightarrow> address set" where
  "touched_addrs' s \<equiv> touched_addrs (other_state s)"

lemma touched_addrs_inv':
  "reachable (other_state s) \<Longrightarrow>
   touched_addrs' s \<subseteq> all_addrs_of (current_domain' s) \<union> kernel_shared_precise"
  using touched_addrs_inv unfolding all_addrs_of_def
  by simp

abbreviation collision_set :: "address \<Rightarrow> address set" where
  "collision_set a \<equiv> {b. (a, b) \<in> collides_in_pch}"

lemma collision_set_contains_itself: "a \<in> collision_set a"
  using collides_with_equiv
  by (clarsimp simp:equiv_def refl_on_def)

\<comment> \<open> the addresses in kernel shared memory (which for now is everything in the sched domain)\<close>
definition kernel_shared_precise :: "address set" where
  "kernel_shared_precise \<equiv> {a. addr_domain a = Sched}"

\<comment> \<open> the kernel shared memory, including cache colliding addresses \<close>
definition kernel_shared_expanded :: "address set" where
  "kernel_shared_expanded \<equiv> {a. \<exists> z \<in> kernel_shared_precise. a \<in> collision_set z}"



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

definition pch_same_for_domain_and_shared :: "domain \<Rightarrow> 'pch_cachedness pch \<Rightarrow> 'pch_cachedness pch \<Rightarrow> bool"
  where
 "pch_same_for_domain_and_shared d p1 p2 \<equiv> \<forall> a. addr_domain a = d \<or> a \<in> kernel_shared_expanded \<longrightarrow> p1 a = p2 a"

definition pch_same_for_domain_except_shared :: "domain \<Rightarrow> 'pch_cachedness pch \<Rightarrow> 'pch_cachedness pch \<Rightarrow> bool"
  where
 "pch_same_for_domain_except_shared d p1 p2 \<equiv> \<forall> a. addr_domain a = d \<and> a \<notin> kernel_shared_expanded \<longrightarrow> p1 a = p2 a"

definition uwr_running :: "domain \<Rightarrow>
  (('fch_cachedness,'pch_cachedness) state \<times> ('fch_cachedness,'pch_cachedness) state) set"
  where
  "uwr_running d \<equiv> {(s1, s2). fch s1 = fch s2
                            \<and> pch_same_for_domain_and_shared d (pch s1) (pch s2)
                            \<and> tm s1 = tm s2
                            \<and> regs s1 = regs s2
                            \<and> (other_state s1, other_state s2) \<in> external_uwr d }"
\<comment> \<open>how do we know we have the same program?\<close>


definition uwr_notrunning :: "domain \<Rightarrow>
  (('fch_cachedness,'pch_cachedness) state \<times> ('fch_cachedness,'pch_cachedness) state) set"
  where
  "uwr_notrunning d \<equiv> {(s1, s2). pch_same_for_domain_except_shared d (pch s1) (pch s2)
                               \<and> (other_state s1, other_state s2) \<in> external_uwr d }"
\<comment> \<open>external uwr needs to be held in the right conditions as an axiom\<close>

definition uwr :: "domain \<Rightarrow>
  (('fch_cachedness,'pch_cachedness) state \<times> ('fch_cachedness,'pch_cachedness) state) set"
  where
  "uwr d \<equiv> {(s1, s2). if (current_domain' s1 = d)
                      then (s1, s2) \<in> uwr_running d
                      else (s1, s2) \<in> uwr_notrunning d }"

lemma uwr_to_external:
  "(s, t) \<in> uwr d \<Longrightarrow> (other_state s, other_state t) \<in> external_uwr d"
  by (clarsimp simp:uwr_def uwr_running_def uwr_notrunning_def split:if_splits)

lemma uwr_same_domain:
  "(s, t) \<in> uwr d \<Longrightarrow> current_domain' s = current_domain' t"
  by (force dest:uwr_to_external external_uwr_same_domain)

lemma uwr_same_touched_addrs:
  "(s, t) \<in> uwr d \<Longrightarrow> current_domain' s = d \<Longrightarrow> touched_addrs' s = touched_addrs' t"
  by (force dest:uwr_to_external external_uwr_same_touched_addrs)

lemma extended_uwr_equiv_rel:
  "equiv UNIV (uwr u)"
  using uwr_equiv_rel
  apply(erule_tac x=u in meta_allE)
  apply(clarsimp simp:equiv_def)
  apply(rule conjI)
   apply(clarsimp simp:uwr_def refl_on_def uwr_running_def uwr_notrunning_def)
   apply(force simp:pch_same_for_domain_and_shared_def pch_same_for_domain_except_shared_def)
  apply(rule conjI)
   apply(clarsimp simp:sym_def)
   apply(frule uwr_same_domain)
   apply(erule_tac x="other_state x" in allE)
   apply(erule_tac x="other_state y" in allE)
   apply(clarsimp simp:uwr_def split:if_splits)
    apply(force simp:uwr_running_def pch_same_for_domain_and_shared_def)
   apply(force simp:uwr_notrunning_def pch_same_for_domain_except_shared_def)
  apply(clarsimp simp:trans_def)
  apply(frule_tac s=x in uwr_same_domain)
  apply(frule_tac s=y in uwr_same_domain)
  apply(erule_tac x="other_state x" in allE)
  apply(erule_tac x="other_state y" in allE)
  apply(erule impE)
   apply(force simp:uwr_to_external)
  apply(erule_tac x="other_state z" in allE)
  apply(erule impE)
   apply(force simp:uwr_to_external)
  apply(clarsimp simp:uwr_def split:if_splits)
   apply(force simp:uwr_running_def pch_same_for_domain_and_shared_def)
  apply(force simp:uwr_notrunning_def pch_same_for_domain_except_shared_def)
  done

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
    ('fch_cachedness, 'pch_cachedness) state \<Rightarrow>
    ('fch_cachedness, 'pch_cachedness) state" where
 "instr_step (IRead a) s =
      s\<lparr>fch := fch_read_impact a (fch s),
        pch := pch_read_impact a (fch s) (pch s),
        tm  := tm s + read_cycles (fch s a) (pch s a),
        regs := do_read a (other_state s) (regs s)\<rparr>"
  | "instr_step (IWrite a) s =
      s\<lparr>fch := fch_write_impact a (fch s),
        pch := pch_write_impact a (fch s) (pch s),
        tm  := tm s + write_cycles (fch s a) (pch s a),
        other_state := do_write a (other_state s) (regs s)\<rparr>"
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
  ('fch_cachedness, 'pch_cachedness) state \<Rightarrow>
  ('fch_cachedness, 'pch_cachedness) state" where
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


lemma hd_instr_obeying_ta [dest]:
  "a # p \<in> programs_obeying_ta ta \<Longrightarrow> a \<in> instrs_obeying_ta ta"
  by (force simp:programs_obeying_ta_def)

(*

  s  -->  t
          
  |       ||||
  v       vvvv
          
  s'      t'


*)

lemma d_running_step:
  assumes
    "i \<in> instrs_obeying_ta ta"
    "ta \<subseteq> all_addrs_of d \<union> kernel_shared_precise"
    "(s, t) \<in> uwr d"
    "current_domain' s = d"
    "s' = instr_step i s"
    "t' = instr_step i t"
    "current_domain' s' = d"
  shows
    "(s', t') \<in> uwr d"
  proof (cases i)
    case (IRead a)
    thus ?thesis using assms
      apply(clarsimp simp:uwr_def uwr_running_def)
      apply(clarsimp simp:instrs_obeying_ta_def)
      (* First obtain that `a` belongs to the current domain or shared memory (i.e. Sched) *)
      apply(clarsimp simp:all_addrs_of_def)
      apply(erule_tac c=a in subsetCE)
       apply force
      apply clarsimp
      apply(rule conjI)
       (* equivalence on part of pch *)
       apply(clarsimp simp:pch_same_for_domain_and_shared_def kernel_shared_expanded_def)
       apply(rename_tac a')
       apply(case_tac "a' \<in> collision_set a")
        (* for colliding addresses *)
        apply clarsimp
        apply(rule conjI)
         apply clarsimp
         apply(rule pch_collision_read)
          apply force
         using no_cross_colour_collisions
         apply(metis (mono_tags, lifting) addr_domain_valid collision_set_contains_itself kernel_shared_precise_def mem_Collect_eq)
        apply clarsimp
        apply(rule pch_collision_read)
         apply force
        apply clarsimp
        apply(erule_tac x=a3 in allE)
        apply clarsimp
        apply(erule_tac x=z in ballE)
         using collides_with_equiv
         apply(clarsimp simp:equiv_def)
         apply(solves\<open>meson trans_def\<close>)
        apply force
       apply clarsimp
       (* for non-colliding addresses *)
       using pch_partitioned_read
       apply force
      apply(rule conjI)
       (* equivalence of read cycles *)
       apply(erule disjE)
        apply(force simp:pch_same_for_domain_and_shared_def)
       apply(clarsimp simp:pch_same_for_domain_and_shared_def kernel_shared_expanded_def)
       using collision_set_contains_itself
       apply fastforce
      (* equivalence of what ends up in the registers from other_state *)
      (* TODO: we need a property that says the external_uwr will give us
         equivalence of what's read from addresses belonging to that domain. *)
      sorry
  next
    case (IWrite a)
    (* NB: Reasoning is mostly identical to that for IRead -robs. *)
    thus ?thesis using assms
      apply(clarsimp simp:uwr_def uwr_running_def)
      apply(clarsimp simp:instrs_obeying_ta_def)
      (* First obtain that `a` belongs to the current domain or shared memory (i.e. Sched) *)
      apply(clarsimp simp:all_addrs_of_def)
      apply(erule_tac c=a in subsetCE)
       apply force
      apply clarsimp
      apply(rule conjI)
       (* equivalence on part of pch *)
       apply(clarsimp simp:pch_same_for_domain_and_shared_def kernel_shared_expanded_def)
       apply(rename_tac a')
       apply(case_tac "a' \<in> collision_set a")
        (* for colliding addresses *)
        apply clarsimp
        apply(rule conjI)
         apply clarsimp
         apply(rule pch_collision_write)
          apply force
         using no_cross_colour_collisions
         apply(metis (mono_tags, lifting) addr_domain_valid collision_set_contains_itself kernel_shared_precise_def mem_Collect_eq)
        apply clarsimp
        apply(rule pch_collision_write)
         apply force
        apply clarsimp
        apply(erule_tac x=a3 in allE)
        apply clarsimp
        apply(erule_tac x=z in ballE)
         using collides_with_equiv
         apply(clarsimp simp:equiv_def)
         apply(solves\<open>meson trans_def\<close>)
        apply force
       apply clarsimp
       (* for non-colliding addresses *)
       using pch_partitioned_write
       apply force
      apply(rule conjI)
       (* equivalence of write cycles *)
       apply(erule disjE)
        apply(force simp:pch_same_for_domain_and_shared_def)
       apply(clarsimp simp:pch_same_for_domain_and_shared_def kernel_shared_expanded_def)
       using collision_set_contains_itself
       apply fastforce
      (* equivalence of the written impact on other_state *)
      using do_write_maintains_external_uwr_in kernel_shared_precise_def
      by blast
  next
    case (IRegs x3)
    thus ?thesis using assms by (force simp:uwr_def uwr_running_def)
  next
    case IFlushL1
    thus ?thesis using assms by (force simp:uwr_def uwr_running_def)
  next
    case (IFlushL2 x5)
    then show ?thesis sorry (* TODO *)
  next
    case IReadTime
    thus ?thesis using assms by (force simp:uwr_def uwr_running_def)
  next
    case (IPadToTime x7)
    thus ?thesis using assms by (force simp:uwr_def uwr_running_def)
  qed

(* d running \<rightarrow> d running *)
lemma d_running: "\<lbrakk>
   \<comment> \<open>Note: The \<open>programs_obeying_ta_preserve_uwr\<close> lemma that uses this should extract whatever
     we'll need here from its guards that s and t are reachable. We can't have these reachability
     guards here because it will mess up the induction proof (won't hold for intermediate states).\<close>
   \<comment> \<open>we have two programs derived from the same touched_addresses -
     these have to be the same program (so we need to know that the choice depends on stuff in
     other_state in the external uwr)\<close>
   p \<in> programs_obeying_ta ta;
   \<comment> \<open>that touched_addresses ONLY contains addresses in d\<close>
   ta \<subseteq> all_addrs_of d \<union> kernel_shared_precise;
   \<comment> \<open>initial states s and t hold uwr_running\<close>
   (s, t) \<in> uwr d;
   current_domain' s = d;
   \<comment> \<open>NB: external_uwr should give us current_domain' t = d\<close>
   \<comment> \<open>we execute the program on both states\<close>
   s' = instr_multistep p s;
   t' = instr_multistep p t;
   current_domain' s' = d
   \<comment> \<open>NB: external_uwr should oblige us to prove current_domain' t' = d\<close>
   \<rbrakk> \<Longrightarrow>
   \<comment> \<open>new states s' and t' hold uwr_running\<close>
   (s', t') \<in> uwr d"
  apply(induct p arbitrary:s t)
   apply force
  apply clarsimp
  apply(erule_tac x="instr_step a s" in meta_allE)
  apply(erule_tac x="instr_step a t" in meta_allE)
  apply clarsimp
  apply(erule meta_impE)
   apply(force simp:programs_obeying_ta_def)
  apply(prop_tac "current_domain' (instr_step a s) = current_domain' s")
   (* FIXME: We need a guard strong enough to say "there's no change to dom by any instr
      of this program" enforced depending on which step of the automaton we're in. *)
   defer
  apply(erule meta_impE)
   apply(force dest:d_running_step)
  apply force
  sorry

(*FIXME: This is a draft *)
(* d running \<rightarrow> d not running *)
lemma context_switch_from_d: "\<lbrakk>
   p \<in> programs_obeying_ta ta;
   ta \<subseteq> all_addrs_of d \<union> kernel_shared_precise;
   (s, t) \<in> uwr d;
   current_domain' s = d;
   \<comment> \<open>NB: external_uwr should give us current_domain' t = d\<close>
   s' = instr_multistep p s;
   t' = instr_multistep p t;
   current_domain' s' \<noteq> d
   \<comment> \<open>NB: external_uwr should oblige us to prove current_domain' t' \<noteq> d\<close>
   \<rbrakk> \<Longrightarrow>
   (s', t') \<in> uwr d"
  sorry

(* d not running \<rightarrow> d not running *)
lemma d_not_running: "\<lbrakk>
   \<comment> \<open>we have two programs derived from touched_addresses - may not be the same touched_addresses\<close>
   p\<^sub>s \<in> programs_obeying_ta ta\<^sub>s;
   p\<^sub>t \<in> programs_obeying_ta ta\<^sub>t;
   \<comment> \<open>we may not have concrete touched_addresses -
     we may overapprox this to the whole currently running domain.
     NB: I think it's enough just to require it not contain any of d's addresses. -robs.\<close>
   \<comment> \<open>these touched_addresses does NOT contain any addresses from d\<close>
   ta\<^sub>s \<inter> all_addrs_of d \<subseteq> kernel_shared_precise;
   ta\<^sub>t \<inter> all_addrs_of d \<subseteq> kernel_shared_precise;
   \<comment> \<open>initial states s and t hold uwr_notrunning\<close>
   (s, t) \<in> uwr d;
   current_domain' s \<noteq> d;
   \<comment> \<open>NB: external_uwr should give us current_domain' t \<noteq> d\<close>
   \<comment> \<open>we execute both programs\<close>
   s' = instr_multistep p\<^sub>s s;
   t' = instr_multistep p\<^sub>t t;
   current_domain' s' \<noteq> d
   \<comment> \<open>NB: external_uwr should oblige us to prove current_domain' t' \<noteq> d\<close>
   \<rbrakk> \<Longrightarrow>
   \<comment> \<open>new state s' and t' hold uwr_notrunning\<close>
   (s', t') \<in> uwr d"
  apply(clarsimp simp:uwr_def)
  sorry

(* d not running \<rightarrow> d running *)
lemma context_switch_to_d: "\<lbrakk>
   p\<^sub>s \<in> programs_obeying_ta ta\<^sub>s;
   p\<^sub>t \<in> programs_obeying_ta ta\<^sub>t;
   ta\<^sub>s \<inter> all_addrs_of d \<subseteq> kernel_shared_precise;
   ta\<^sub>t \<inter> all_addrs_of d \<subseteq> kernel_shared_precise;
   (s, t) \<in> uwr d;
   current_domain' s \<noteq> d;
   \<comment> \<open>external_uwr should give us current_domain' t \<noteq> d\<close>
   s' = instr_multistep (p\<^sub>s @ [IFlushL1, IPadToTime detTime]) s;
   t' = instr_multistep (p\<^sub>t @ [IFlushL1, IPadToTime detTime]) t;
   current_domain' s' = d
   \<comment> \<open>external_uwr should oblige us to prove current_domain' t' = d\<close>
   \<rbrakk> \<Longrightarrow>
   (s', t') \<in> uwr d"
  sorry

lemma programs_obeying_ta_preserve_uwr: "\<lbrakk>
   reachable (other_state s);
   reachable (other_state t);
   p\<^sub>s \<in> programs_obeying_ta (touched_addrs' s);
   p\<^sub>t \<in> programs_obeying_ta (touched_addrs' t);
   (s, t) \<in> uwr d;
   s' = instr_multistep p\<^sub>s s;
   t' = instr_multistep p\<^sub>t t
   \<rbrakk> \<Longrightarrow>
   (s', t') \<in> uwr d"
  apply(frule uwr_same_domain)
  apply(case_tac "current_domain' s = d")
   apply clarsimp
   apply(case_tac "current_domain' s' = d")
    apply(rule d_running)
          apply force
         using touched_addrs_inv'
         apply force
        apply force
       apply force
      apply force
     apply(frule uwr_same_touched_addrs)
      apply force
     apply(prop_tac "p\<^sub>s = p\<^sub>t")
      (* FIXME: Here's something we need - essentially, that we *can* expect the program
         (that is, the "multistep" implementation) to be known to the currently running domain.
         How best to require/obtain this? -robs. *)
      defer
     apply force
    apply force
   (* FIXME: The lemma is too broad. We should make it about the context switch and assert
      there is (1) a designated step in the automaton that does it, and (2) a much more
      constrained set of instr_multistep programs that implement it. -robs.
   apply(rule context_switch_from_d)
         apply force
        using touched_addrs_inv' apply force
       apply force
      apply force
     apply force
    defer
   apply force
   *)
   defer
  apply(case_tac "current_domain' s' = d")
   (* FIXME: Broken for similar reasons as context_switch_from_d
   apply(rule context_switch_to_d)
           apply force
          using touched_addrs_inv' apply force
         defer
        defer
       apply force
      apply force
     defer
    defer
   apply force
   *)
  apply clarsimp
  apply(rule d_not_running[where s=s and t=t and p\<^sub>s=p\<^sub>s and p\<^sub>t=p\<^sub>t and
        ta\<^sub>s="touched_addrs' s" and ta\<^sub>t="touched_addrs' t"])
          apply force
         apply force
        (* using touched_addrs_inv' *)
        defer (* FIXME: Think more about these two. -robs. *)
       defer
      apply force
     apply force
    apply force
   apply force
  (* FIXME: We need a fact from the automaton - for example, that we're definitely
     not on a context switch step. (But is that enough? Can't this case also be
     covering a context switch step between two other domains?) -robs. *)
  defer
  sorry

definition A_extended_Step :: "unit \<Rightarrow>
  (('fch_cachedness,'pch_cachedness)state \<times> ('fch_cachedness,'pch_cachedness)state) set"
  where
  "A_extended_Step \<equiv> \<lambda>_. {(s, s').
     \<comment> \<open>Initial attempt. FIXME: The fact the 2nd conjunct might reject executions that were fine
        in the original automaton is what might be making enabledness tricky. -robs.\<close>
     (other_state s') \<in> execution A (other_state s) [()] \<and>
     (\<exists>p \<in> programs_obeying_ta (touched_addrs (other_state s)). s' = instr_multistep p s)}"

definition A_extended ::
  "(('fch_cachedness,'pch_cachedness)state,('fch_cachedness,'pch_cachedness)state,unit) data_type"
  where
  "A_extended = \<lparr> Init = \<lambda>s. {s}, Fin = id, Step = A_extended_Step \<rparr>"

definition A_extended_state :: "other_state \<Rightarrow> ('fch_cachedness,'pch_cachedness)state" where
  "A_extended_state s =
     \<lparr> fch = empty_fch, pch = initial_pch, tm = 0, regs = initial_regs, other_state = s \<rparr>"

(* XXX: Annoying, surely some helpers for this already exist; come back to this later -robs. *)
lemma bad_lemma:
  "\<lbrakk>\<comment> \<open>system.reachable A_extended (A_extended_state s0) s;\<close>
   x \<in> execution A_extended s as\<rbrakk>
   \<Longrightarrow> (s, x) \<in> Run (system.Step A_extended) as"
  apply(induct as arbitrary:s)
   apply(force simp:execution_def steps_def A_extended_def)
  apply(clarsimp simp:execution_def A_extended_def)
  sorry

interpretation tpni: unwinding_system A_extended "A_extended_state s0" "\<lambda>_. current_domain'" uwr
  policy "\<lambda>d s. out d (other_state s)" Sched
  (* Note: The 3 enabledness/reachability requirements are probably broken. -robs. *)
  apply unfold_locales
        (* enabled_system.enabled *)
        using enabled
        apply(clarsimp simp:A_extended_def)
        (* FIXME *)
        defer
       (* Step_system.reachable_s0 *)
       apply(clarsimp simp:A_extended_state_def A_extended_def A_extended_Step_def)
       apply(clarsimp simp:system.reachable_def execution_def)
       apply(metis (no_types, lifting) foldl_Nil singletonI steps_def)
      (* Step_system.execution_Run *)
      (* using execution_Run *)
      apply(rule set_eqI)
      apply clarsimp
      apply(rule iffI)
       (* XXX: Not sure the best way to do these proofs -robs. *)
       apply(force simp:bad_lemma)
      (* FIXME *)
      defer
     (* noninterference_policy.uwr_equiv_rel *)
     using extended_uwr_equiv_rel apply blast
    (* noninterference_policy.schedIncludesCurrentDom *)
    using uwr_same_domain apply blast
   (* noninterference_policy.schedFlowsToAll *)
   using schedFlowsToAll apply blast
  (* noninterference_policy.schedNotGlobalChannel *)
  using schedNotGlobalChannel apply blast
  sorry

lemma to_original_step:
  "(x, y) \<in> tpni.Step () \<Longrightarrow>
   (other_state x, other_state y) \<in> Step ()"
  by (clarsimp simp:tpni.Step_def system.Step_def execution_def
      A_extended_def A_extended_Step_def steps_def)

lemma to_original_run:
  "(s, s') \<in> Run tpni.Step as \<Longrightarrow>
   (other_state s, other_state s') \<in> Run local.Step as"
  apply(induct as arbitrary:s)
   apply(force simp:A_extended_state_def)
  apply clarsimp
  apply(erule_tac x=y in meta_allE)
  apply clarsimp
  apply(subgoal_tac "(other_state x, other_state y) \<in> Step ()")
   apply blast
  using to_original_step by blast

lemma to_original_run':
  "(A_extended_state s, s') \<in> Run tpni.Step as \<Longrightarrow>
   (s, other_state s') \<in> Run local.Step as"
  apply(clarsimp simp:A_extended_state_def)
  using to_original_run by force

lemma to_original_reachability:
  "tpni.reachable s \<Longrightarrow> reachable (other_state s)"
  apply(rule Run_reachable)
  apply(drule tpni.reachable_Run)
  apply clarsimp
  apply(rule_tac x=as in exI)
  using to_original_run' by blast

theorem extended_confidentiality_u:
  "confidentiality_u \<Longrightarrow> tpni.confidentiality_u"
  apply(clarsimp simp:confidentiality_u_def tpni.confidentiality_u_def)
  apply(erule_tac x=u in allE)
  apply(erule_tac x="other_state s" in allE)
  apply(erule_tac x="other_state t" in allE)
  apply(prop_tac "reachable (other_state s) \<and> reachable (other_state t)")
   using to_original_reachability apply force
  apply(prop_tac "uwr2 (other_state s) Sched (other_state t)")
   using uwr_to_external apply blast
  apply(prop_tac "((current_domain () (other_state s), u) \<in> policy) \<longrightarrow>
        uwr2 (other_state s) (current_domain () (other_state s)) (other_state t)")
   using uwr_to_external apply blast
  apply(prop_tac "uwr2 (other_state s) u (other_state t)")
   using uwr_to_external apply blast
  apply clarsimp
  apply(erule_tac x="other_state s'" in allE)
  apply(erule_tac x="other_state t'" in allE)
  apply(frule_tac x=s in to_original_step)
  apply(frule_tac x=t in to_original_step)
  apply clarsimp
  (* The reachability assumptions just unfold into something messy - get rid of them. -robs. *)
  apply(thin_tac "tpni.reachable x" for x)+
  apply(clarsimp simp:tpni.Step_def system.Step_def A_extended_def execution_def A_extended_Step_def steps_def)
  (* What we now expect is to invoke some versions of d_running, d_notrunning etc.
     These case split on whether `u` is the currently running domain, but maybe we'll
     need to adjust their guards to adapt them further to the automata... -robs. *)
  apply(rename_tac u s t x xa p\<^sub>s xb xc p\<^sub>t)
  apply(rule_tac s=s and t=t and p\<^sub>s=p\<^sub>s and p\<^sub>t=p\<^sub>t in programs_obeying_ta_preserve_uwr, force+)
  done

end
end