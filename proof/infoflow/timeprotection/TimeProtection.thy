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



locale time_protection =
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

  fixes padding_regs_impact :: "time \<Rightarrow> regs \<Rightarrow> regs"

  fixes empty_fch :: "'fch_cachedness fch"
  fixes fch_flush_cycles :: "'fch_cachedness fch \<Rightarrow> time" \<comment> \<open>could this be dependent on anything else?\<close>

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
  fixes current_domain :: "other_state \<Rightarrow> domain"

  fixes external_uwr :: "domain \<Rightarrow> (other_state \<times> other_state) set"
  assumes external_uwr_same_domain: "(s1, s2) \<in> external_uwr d \<Longrightarrow> current_domain s1 = current_domain s2"
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
begin

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


(*

  s  -->  t
          
  |       ||||
  v       vvvv
          
  s'      t'


*)

definition all_addrs_of :: "domain \<Rightarrow> address set" where
  "all_addrs_of d = {a. addr_domain a = d}"

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
  apply(induct p)
   apply force
  using d_running_step
  (* TODO *)
  oops

(*FIXME: This is a draft *)
(* d running \<rightarrow> d not running *)
lemma context_switch_from_d:
  "\<lbrakk>p \<in> programs_obeying_ta ta;
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
  oops

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
  oops

(* d not running \<rightarrow> d running *)
lemma context_switch_to_d:
  "\<lbrakk>p\<^sub>s \<in> programs_obeying_ta ta\<^sub>s;
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
  oops

end
end