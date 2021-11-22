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

datatype 'userdomain domain = Sched | User 'userdomain

record ('fch,'pch,'regs,'other_state) state =
  fch :: "'fch" \<comment> \<open> flushable cache\<close>
  pch :: "'pch" \<comment> \<open> partitionable cache \<close>
  tm :: time
  regs :: 'regs
  other_state :: 'other_state


locale time_protection =
  (* "(a, b) \<in> collides_in_pch" = "a may cause b to be evicted from or loaded to the pch" *)
  fixes collides_in_pch :: "address rel"
  assumes collides_with_equiv: "equiv UNIV collides_in_pch"

  fixes fch_lookup :: "'fch \<Rightarrow> 'fch_cachedness fch"
  fixes pch_lookup :: "'pch \<Rightarrow> 'pch_cachedness pch"

  fixes fch_read_impact :: "'fch fch_impact"
  fixes pch_read_impact :: "('fch, 'pch) pch_impact"

  assumes pch_partitioned_read:
    "(a1, a2) \<notin> collides_in_pch \<Longrightarrow> pch_lookup p a2 = pch_lookup (pch_read_impact a1 f p) a2"
  (* if a2 can be impacted by a read from a1,
     we require that this impact depends only on the prior state of the fch
     and the prior cachedness of the rest of their collision set in the pch *)
  assumes pch_collision_read: "(a1, a2) \<in> collides_in_pch \<Longrightarrow>
    \<forall>a3. (a2, a3) \<in> collides_in_pch \<longrightarrow> pch_lookup pchs a3 = pch_lookup pcht a3 \<Longrightarrow>
    \<comment> \<open>This might be stronger than is met by hardware that just promises
        a 'random' replacement algorithm. Essentially we are requiring that
        any such 'randomness' cannot be influenced by the prior cachedness of
        addresses outside the collision set in question. \<close>
    pch_lookup (pch_read_impact a1 f pchs) a2 = pch_lookup (pch_read_impact a1 f pcht) a2"

  fixes fch_write_impact :: "'fch fch_impact"
  fixes pch_write_impact :: "('fch, 'pch) pch_impact"
  assumes pch_partitioned_write:
    "(a1, a2) \<notin> collides_in_pch \<Longrightarrow> pch_lookup p a2 = pch_lookup (pch_write_impact a1 f p) a2"

  assumes pch_collision_write: "(a1, a2) \<in> collides_in_pch \<Longrightarrow>
    \<forall>a3. (a2, a3) \<in> collides_in_pch \<longrightarrow> pch_lookup pchs a3 = pch_lookup pcht a3 \<Longrightarrow>
    \<comment> \<open>The same strong requirement placing limits on the 'randomness'
        of the cache replacement algorithm as for @{term pch_collision_read}\<close>
    pch_lookup (pch_write_impact a1 f pchs) a2 = pch_lookup (pch_write_impact a1 f pcht) a2"

  fixes read_cycles  :: "'fch_cachedness \<Rightarrow> 'pch_cachedness \<Rightarrow> time"
  fixes write_cycles :: "'fch_cachedness \<Rightarrow> 'pch_cachedness \<Rightarrow> time"

  fixes do_read :: "address \<Rightarrow> 'other_state \<Rightarrow> 'regs \<Rightarrow> 'regs"
  fixes do_write :: "address \<Rightarrow> 'other_state \<Rightarrow> 'regs \<Rightarrow> 'other_state"

  fixes store_time :: "time \<Rightarrow> 'regs \<Rightarrow> 'regs"

  fixes padding_regs_impact :: "time \<Rightarrow> 'regs \<Rightarrow> 'regs"

  fixes empty_fch :: "'fch"
  fixes fch_flush_cycles :: "'fch \<Rightarrow> time" \<comment> \<open>could this be dependent on anything else?\<close>

  fixes do_pch_flush :: "'pch \<Rightarrow> address set \<Rightarrow> 'pch"
  fixes pch_flush_cycles :: "'pch \<Rightarrow> address set \<Rightarrow> time" \<comment> \<open>could this be dependent on anything else?\<close>

  assumes pch_partitioned_flush:
   "(\<forall>a'\<in>as. (a, a') \<notin> collides_in_pch) \<Longrightarrow> pch_lookup (do_pch_flush p as) a = pch_lookup p a"
  assumes pch_collision_flush:
    "\<exists>a1\<in>as. (a, a1) \<in> collides_in_pch \<Longrightarrow>
    \<forall>a1. (\<exists>a2\<in>as. (a1, a2) \<in> collides_in_pch) \<longrightarrow> pch_lookup pchs a1 = pch_lookup pcht a1 \<Longrightarrow>
    pch_lookup (do_pch_flush pchs as) a = pch_lookup (do_pch_flush pcht as) a"
  assumes pch_flush_cycles_localised:
    "\<forall>a1. (\<exists>a2\<in>as. (a1, a2) \<in> collides_in_pch) \<longrightarrow> pch_lookup pchs a1 = pch_lookup pcht a1 \<Longrightarrow>
    pch_flush_cycles pchs as = pch_flush_cycles pcht as"

  fixes addr_domain :: "address \<Rightarrow> 'userdomain domain" \<comment> \<open>for each address, this is the security domain\<close>
  fixes addr_colour :: "address \<Rightarrow> 'colour" \<comment> \<open>for each address, this is the cache colour\<close>
  fixes colour_userdomain :: "'colour \<Rightarrow> 'userdomain"
  assumes colours_not_shared: "colour_userdomain c1 \<noteq> colour_userdomain c2 \<Longrightarrow> c1 \<noteq> c2"
  assumes no_cross_colour_collisions:
    "(a1, a2) \<in> collides_in_pch \<Longrightarrow> addr_colour a1 = addr_colour a2"
  assumes addr_domain_valid: "addr_domain a = Sched
                            \<or> addr_domain a = User (colour_userdomain (addr_colour a))"
\<comment> \<open>do we assert this here
  or just put it in the type so it has to be asserted before instantiation? or assert it differently
  later?\<close>


  fixes current_domain :: "'other_state \<Rightarrow> 'userdomain domain"
  fixes external_uwr :: "'userdomain domain \<Rightarrow> ('other_state \<times> 'other_state) set"
  assumes external_uwr_equiv_rel:
    "equiv UNIV (external_uwr d)"
  (* The parent locale requires current_domain to be equated by Sched uwr, which confidentiality_u
     then treats as specifying public information; assuming that it is instead equated by every
     domain's uwr arguably simplifies things without changing the strength of the property.
       Without this assumption, I expect we'll need to add the Sched uwr explicitly to the
     pre-equivalence of many lemmas; it may also be a bit harder to prove that our uwr is an
     equivalence relation without it. It may be reasonable to keep this if it holds (or can
     reasonably be made to hold) for the seL4 infoflow theory's unwinding relation. -robs. *)
  assumes external_uwr_same_domain:
    "(s1, s2) \<in> external_uwr d \<Longrightarrow> current_domain s1 = current_domain s2"
\<comment> \<open>we will probably needs lots more info about this external uwr\<close>

  
  
  assumes do_write_maintains_external_uwr_out:
    "addr_domain a \<noteq> d \<and> addr_domain a \<noteq> Sched \<Longrightarrow>
     (s, do_write a s r) \<in> external_uwr d"
  
  (*NOTE: we can only invoke this if we have already equalised the "regs" fields *)
  assumes do_write_maintains_external_uwr_in:
    "addr_domain a = d \<or> addr_domain a = Sched \<Longrightarrow>
     (s, t) \<in> external_uwr d \<Longrightarrow>
     (do_write a s r, do_write a t r) \<in> external_uwr d"

  assumes do_write_outside_kernelshared_same_domain:
    "addr_domain a \<noteq> Sched \<Longrightarrow>
     current_domain (do_write a s r) = current_domain s"

  (* do_read depends only on things bound in its external uwr *)
  assumes do_read_from_external_uwr_domain:
    "\<lbrakk>(s, t) \<in> external_uwr d;
     addr_domain a = d \<rbrakk> \<Longrightarrow>
     do_read a s r = do_read a t r"

  (* do_read of kernel_shared depends only on things bound in any external uwr *)
  assumes do_read_from_external_uwr_sched:
    "\<lbrakk>(s, t) \<in> external_uwr d;
     addr_domain a = Sched \<rbrakk> \<Longrightarrow>
     do_read a s r = do_read a t r"

  fixes touched_addrs :: "'other_state \<Rightarrow> address set"
  assumes external_uwr_same_touched_addrs:
    "(s1, s2) \<in> external_uwr d \<Longrightarrow> current_domain s1 = d\<Longrightarrow> touched_addrs s1 = touched_addrs s2"

  (* We expect this to be true for, say, seL4's KSched \<rightarrow> KExit step. -robs. *)
  fixes can_domain_switch :: "'other_state \<Rightarrow> bool"
  assumes can_domain_switch_public:
    "(s1, s2) \<in> external_uwr d \<Longrightarrow> can_domain_switch s1 = can_domain_switch s2"
begin

definition all_addrs_of :: "'userdomain domain \<Rightarrow> address set" where
  "all_addrs_of d = {a. addr_domain a = d}"

abbreviation current_domain' :: "('fch,'pch,'regs,'other_state)state \<Rightarrow> 'userdomain domain"
  where
  "current_domain' s \<equiv> current_domain (other_state s)"

abbreviation collision_set :: "address \<Rightarrow> address set" where
  "collision_set a \<equiv> {b. (a, b) \<in> collides_in_pch}"

lemma collision_set_contains_itself: "a \<in> collision_set a"
  using collides_with_equiv
  by (clarsimp simp:equiv_def refl_on_def)

lemma external_uwr_refl [simp]:
  "(s, s) \<in> external_uwr d"
  using external_uwr_equiv_rel
  by (clarsimp simp: equiv_def refl_on_def)

lemma collision_sym [simp]:
  "(a, b) \<in> collides_in_pch \<Longrightarrow>
  (b, a) \<in> collides_in_pch"
  by (meson collides_with_equiv equiv_def symE)

\<comment> \<open> the addresses in kernel shared memory (which for now is everything in the sched domain)\<close>
definition kernel_shared_precise :: "address set" where
  "kernel_shared_precise \<equiv> {a. addr_domain a = Sched}"

\<comment> \<open> the kernel shared memory, including cache colliding addresses \<close>
definition kernel_shared_expanded :: "address set" where
  "kernel_shared_expanded \<equiv> {a. \<exists> z \<in> kernel_shared_precise. a \<in> collision_set z}"

\<comment> \<open> a full collision set contains all of its own collisions \<close>
definition full_collision_set :: "address set \<Rightarrow> bool" where
  "full_collision_set S \<equiv> \<forall>a1\<in>S. \<forall>a2. (a1, a2) \<in> collides_in_pch \<longrightarrow> a2 \<in> S"

lemma collision_set_full_collision_set:
  "full_collision_set (collision_set a)"
  apply (clarsimp simp: full_collision_set_def)
  apply (meson collides_with_equiv equiv_def trans_def)
  done

lemma kernel_shared_expanded_full_collision_set:
  "full_collision_set kernel_shared_expanded"
  apply (clarsimp simp: kernel_shared_expanded_def full_collision_set_def)
  apply (meson collides_with_equiv equiv_def trans_def)
  done

lemma collision_in_full_collision_set:
  "full_collision_set S \<Longrightarrow>
  (a1, a2) \<in> collides_in_pch \<Longrightarrow>
  a1 \<notin> S \<Longrightarrow>
  a2 \<notin> S"
  apply (clarsimp simp: full_collision_set_def)
  done

abbreviation touched_addrs' ::
  "('fch,'pch,'regs,'other_state)state \<Rightarrow> address set"
  where
  "touched_addrs' s \<equiv> touched_addrs (other_state s)"

(*FIXME: Move these? These seem more of an IF framework thing. -Scott B *)
\<comment> \<open> the invariant that touched_addresses is always sensible for its current domain \<close>
definition touched_addrs_inv :: "'other_state \<Rightarrow> bool" where
  "touched_addrs_inv s \<equiv>
     touched_addrs s \<subseteq> all_addrs_of (current_domain s) \<union> kernel_shared_precise"

abbreviation touched_addrs_inv' :: "('fch,'pch,'regs,'other_state)state \<Rightarrow> bool" where
  "touched_addrs_inv' s \<equiv> touched_addrs_inv (other_state s)"

definition pch_same_for_domain ::
  "'userdomain domain \<Rightarrow> 'pch \<Rightarrow> 'pch \<Rightarrow> bool"
  where
 "pch_same_for_domain d p1 p2 \<equiv> \<forall> a. addr_domain a = d \<longrightarrow> pch_lookup p1 a = pch_lookup p2 a"

definition pch_same_for_domain_and_shared ::
  "'userdomain domain \<Rightarrow> 'pch \<Rightarrow> 'pch \<Rightarrow> bool"
  where
 "pch_same_for_domain_and_shared d p1 p2 \<equiv>
    \<forall> a. addr_domain a = d \<or> a \<in> kernel_shared_expanded \<longrightarrow> pch_lookup p1 a = pch_lookup p2 a"

definition pch_same_for_domain_except_shared ::
  "'userdomain domain \<Rightarrow> 'pch \<Rightarrow> 'pch \<Rightarrow> bool"
  where
 "pch_same_for_domain_except_shared d p1 p2 \<equiv>
    \<forall> a. addr_domain a = d \<and> a \<notin> kernel_shared_expanded \<longrightarrow> pch_lookup p1 a = pch_lookup p2 a"

definition uwr_running ::
  "'userdomain domain \<Rightarrow> ('fch,'pch,'regs,'other_state)state rel"
  where
  "uwr_running d \<equiv> {(s1, s2). fch s1 = fch s2
                            \<and> pch_same_for_domain_and_shared d (pch s1) (pch s2)
                            \<and> tm s1 = tm s2
                            \<and> regs s1 = regs s2
                            \<and> (other_state s1, other_state s2) \<in> external_uwr d }"
\<comment> \<open>how do we know we have the same program?\<close>


definition uwr_notrunning ::
  "'userdomain domain \<Rightarrow> ('fch,'pch,'regs,'other_state)state rel"
  where
  "uwr_notrunning d \<equiv> {(s1, s2). pch_same_for_domain_except_shared d (pch s1) (pch s2)
                               \<and> (other_state s1, other_state s2) \<in> external_uwr d }"
\<comment> \<open>external uwr needs to be held in the right conditions as an axiom\<close>

definition uwr ::
  "'userdomain domain \<Rightarrow> ('fch,'pch,'regs,'other_state)state rel"
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
  using external_uwr_equiv_rel
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

lemma uwr_refl [simp]:
  "(s, s) \<in> uwr d"
  using extended_uwr_equiv_rel
  by (clarsimp simp: equiv_def refl_on_def)

lemma uwr_trans:
  "(a, b) \<in> uwr d \<Longrightarrow>
  (b, c) \<in> uwr d \<Longrightarrow>
  (a, c) \<in> uwr d"
  using extended_uwr_equiv_rel
  apply (clarsimp simp: equiv_def)
  by (meson trans_def)

lemma uwr_sym:
  "((a, b) \<in> uwr d) = ((b, a) \<in> uwr d)"
  using extended_uwr_equiv_rel
  apply (clarsimp simp: equiv_def sym_def)
  apply blast
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






(* now we make some basic isntructions, which contain addresses etc *)
datatype 'r instr = IRead address          \<comment> \<open>read from some address into regs\<close>
                  | IWrite address         \<comment> \<open>write to some address from regs\<close>
                  | IRegs "'r \<Rightarrow> 'r"       \<comment> \<open>modify the regs somehow\<close>
                  | IFlushL1               \<comment> \<open>flush the entire L1 cache(s)\<close>
                  | IFlushL2 "address set" \<comment> \<open>flush some part L2 cache(s)\<close>
                  | IReadTime              \<comment> \<open>read the time into some regs\<close>
                  | IPadToTime time        \<comment> \<open>pad the time up to some point\<close>

primrec
  instr_step :: "'regs instr \<Rightarrow>
    ('fch,'pch,'regs,'other_state)state \<Rightarrow>
    ('fch,'pch,'regs,'other_state)state" where
 "instr_step (IRead a) s =
      s\<lparr>fch := fch_read_impact a (fch s),
        pch := pch_read_impact a (fch s) (pch s),
        tm  := tm s + read_cycles (fch_lookup (fch s) a) (pch_lookup (pch s) a),
        regs := do_read a (other_state s) (regs s)\<rparr>"
  | "instr_step (IWrite a) s =
      s\<lparr>fch := fch_write_impact a (fch s),
        pch := pch_write_impact a (fch s) (pch s),
        tm  := tm s + write_cycles (fch_lookup (fch s) a) (pch_lookup (pch s) a),
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


type_synonym 'r program = "'r instr list"

primrec instr_multistep :: "'regs program \<Rightarrow>
  ('fch,'pch,'regs,'other_state)state \<Rightarrow>
  ('fch,'pch,'regs,'other_state)state" where
  "instr_multistep [] s = s"
| "instr_multistep (i#is) s = instr_multistep is (instr_step i s)"

definition
  instrs_obeying_ta :: "address set \<Rightarrow> 'regs instr set" where
 "instrs_obeying_ta ta \<equiv> {i. case i of
                            IRead a  \<Rightarrow> a \<in> ta
                          | IWrite a \<Rightarrow> a \<in> ta
                          | IFlushL2 as \<Rightarrow> as \<subseteq> ta
                          | _        \<Rightarrow> True }"

(* "safe" instructions. for now this just means they don't write to kernel shared memory *)
definition
  instrs_safe :: "'regs instr set" where
 "instrs_safe \<equiv> {i. case i of
                    IWrite a \<Rightarrow> a \<notin> kernel_shared_precise
                  | _ \<Rightarrow> True}"

(* these are the programs that could have created this ta *)
definition
  programs_obeying_ta :: "address set \<Rightarrow> 'regs program set" where
 "programs_obeying_ta ta \<equiv> {p. list_all (\<lambda>i. i \<in> instrs_obeying_ta ta) p}"


definition
  programs_safe :: "'regs program set" where
 "programs_safe \<equiv> {p. list_all (\<lambda>i. i \<in> instrs_safe) p}"


lemma hd_instr_obeying_ta [dest]:
  "a # p \<in> programs_obeying_ta ta \<Longrightarrow> a \<in> instrs_obeying_ta ta"
  by (force simp:programs_obeying_ta_def)



(* trying to replace this with instrs_safe

(* this program never changes the current domain *)
primrec program_no_domainswitch :: "'regs program \<Rightarrow> bool" where
  "program_no_domainswitch [] = True" |
  "program_no_domainswitch (i#is) =
     ((\<forall> s. current_domain' s = current_domain' (instr_step i s)) \<and> program_no_domainswitch is)"



definition
  programs_no_domainswitch :: "'regs program set" where
  "programs_no_domainswitch \<equiv> {p. program_no_domainswitch p}"

*)

lemma safe_no_domainswitch:
  "i \<in> instrs_safe \<Longrightarrow>
  current_domain' s = current_domain' (instr_step i s)"
  apply (cases i; clarsimp simp: instrs_safe_def)
  apply (clarsimp simp: kernel_shared_precise_def do_write_outside_kernelshared_same_domain)
  done

lemma no_domainswitch_inv:
  "p \<in> programs_safe \<Longrightarrow> current_domain' s = current_domain' (instr_multistep p s)"
  apply(induct p arbitrary:s)
   apply force
  using safe_no_domainswitch
  by (metis (full_types) instr_multistep.simps(2) list_all_simps(1) mem_Collect_eq programs_safe_def)

definition is_secure_nondomainswitch ::
  "'regs program \<Rightarrow> ('fch,'pch,'regs,'other_state)state \<Rightarrow> bool"
  where
  "is_secure_nondomainswitch p s \<equiv>
      \<comment> \<open>Oblige the original system not to reach any system-step that would require either
          (1) straying out of touched_addresses or (2) switching domains to implement.\<close>
      p \<in> (programs_obeying_ta (touched_addrs (other_state s))) \<inter> programs_safe"

definition has_secure_nondomainswitch :: "('fch,'pch,'regs,'other_state)state \<Rightarrow>
  ('fch,'pch,'regs,'other_state)state \<Rightarrow> bool"
  where
  "has_secure_nondomainswitch s s' \<equiv>
     \<comment> \<open>The original definition.\<close>
     \<exists>p. s' = instr_multistep p s \<and> is_secure_nondomainswitch p s \<and>
       \<comment> \<open>Assume the currently running domain's uwr ensures the program stays deterministic.
             Actually, as discussed with Toby, we should add machinery to capture that the program
           might become nondeterministic after the current domain reads from outside
           `touched_addresses + kernel_shared_memory`, assuming pessimistically it might branch
           on some secret data it read -- thus, forcing ourselves to prove that won't happen before
           or during a non-domainswitch step. We should then remove the lines below.\<close>
       (\<forall>t q. (s, t) \<in> uwr (current_domain' s) \<and> is_secure_nondomainswitch q t \<longrightarrow> p = q)"


lemma collides_with_set_or_doesnt:
  "\<lbrakk>\<forall>a'\<in>as. (a, a') \<notin> collides_in_pch \<Longrightarrow> P;
    \<exists>a'\<in>as. (a, a') \<in> collides_in_pch \<Longrightarrow> P \<rbrakk> \<Longrightarrow>
  P"
  by blast


lemma diff_domain_no_collision:
  "\<lbrakk>a \<notin> kernel_shared_expanded;
  addr_domain a' \<noteq> addr_domain a;
  (a, a') \<in> collides_in_pch\<rbrakk> \<Longrightarrow>
  False"
  apply (frule(1) collision_in_full_collision_set [OF kernel_shared_expanded_full_collision_set])
  apply (metis (mono_tags, lifting) addr_domain_valid collision_set_contains_itself
               kernel_shared_expanded_def kernel_shared_precise_def mem_Collect_eq
               no_cross_colour_collisions)
  done



lemma in_inter_empty:
  "\<lbrakk>x \<in> S1;              
  S1 \<inter> S2 = {} \<rbrakk> \<Longrightarrow>
  x \<notin> S2"
  by blast

lemma in_sub_inter_empty:
  "\<lbrakk>x \<in> S1;
  S1 \<subseteq> S2;
  S2 \<inter> S3 = {} \<rbrakk> \<Longrightarrow>
  x \<notin> S3"
  by blast

lemma in_sub_union:
  "\<lbrakk>x \<in> S1;
  S1 \<subseteq> S2;
  S2 \<subseteq> S3 \<union> S4\<rbrakk> \<Longrightarrow>
  x \<in> S3 \<or> x \<in> S4"
  by blast

(* this helps avoid/reverse some unhelpful clarsimp behaviour *)
lemma and_or_specific:
  "(\<And>x. (P x \<or> Q x \<Longrightarrow> R x)) \<Longrightarrow>
   \<forall>a. (P a \<longrightarrow> R a) \<and> (Q a \<longrightarrow> R a)"
  apply blast
  done

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
      apply (erule disjE)
       (* equivalence of what is read from external state, from external uwr *)
       apply (erule(1) do_read_from_external_uwr_domain)
      (* equivalence of what is read from kernel shared memory *)
      apply (erule do_read_from_external_uwr_sched)
      apply (clarsimp simp: kernel_shared_precise_def)
      done
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
    case (IFlushL2 fa)
    then show ?thesis using assms
      apply (clarsimp simp: uwr_def uwr_running_def pch_same_for_domain_and_shared_def
                            instrs_obeying_ta_def)
      apply (thin_tac "s' = _", thin_tac "t' = _") (* messy and not needed *)
      apply (subgoal_tac "\<forall>a1. (\<exists>a2\<in>fa. (a1, a2) \<in> collides_in_pch) \<longrightarrow> pch_lookup (pch s) a1 = pch_lookup (pch t) a1")
       defer
        apply clarsimp
        apply (drule_tac x=a1 in spec)
        apply clarsimp
        apply (drule(2) in_sub_union)
        apply (metis (mono_tags, lifting) all_addrs_of_def collision_in_full_collision_set
                     diff_domain_no_collision kernel_shared_expanded_def
                     kernel_shared_expanded_full_collision_set kernel_shared_precise_def
                     mem_Collect_eq)
      apply (intro conjI)
       (* pch flush affects are partitioned or deterministic on collision *)
       apply (rule and_or_specific)
       apply (rename_tac a)
       apply (rule_tac a=a and as=fa in collides_with_set_or_doesnt)
        (* a has no collision with fa *)
        apply (frule pch_partitioned_flush [where p = "pch s"])
        apply (frule pch_partitioned_flush [where p = "pch t"])
        apply (clarsimp, blast)
       (* a collides with fa *)
       apply (erule(1) pch_collision_flush)
      (* pch flush cycles depend only on equiv state *)
      apply (erule pch_flush_cycles_localised)
      done
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
   p \<in> programs_safe;
   \<comment> \<open>that touched_addresses ONLY contains addresses in d\<close>
   ta \<subseteq> all_addrs_of d \<union> kernel_shared_precise;
   \<comment> \<open>initial states s and t hold uwr_running\<close>
   (s, t) \<in> uwr d;
   current_domain' s = d;
   \<comment> \<open>NB: external_uwr should give us current_domain' t = d\<close>
   \<comment> \<open>we execute the program on both states\<close>
   s' = instr_multistep p s;
   t' = instr_multistep p t
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
  apply(erule meta_impE)
   apply (clarsimp simp: programs_safe_def)
  apply (subgoal_tac "current_domain' (instr_step a s) = d")
   apply (erule meta_impE)
    apply(fastforce dest:d_running_step) 
   apply force
  using safe_no_domainswitch
  apply (metis list_all_simps(1) mem_Collect_eq programs_safe_def)
  done

(*FIXME: This is a draft *)
(* d running \<rightarrow> d not running *)
lemma context_switch_from_d: "\<lbrakk>
   p \<in> programs_obeying_ta ta;
   ta \<inter> all_addrs_of d = {};
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




lemma d_not_running_step:
  assumes
  "i \<in> instrs_obeying_ta ta"
  "i \<in> instrs_safe"
  "ta \<inter> all_addrs_of d = {}"
  "current_domain' s \<noteq> d"
  "s' = instr_step i s"
  shows
  "(s, s') \<in> uwr d"
  proof (cases i)
    case (IRead x1)
    then show ?thesis using assms
      apply (clarsimp simp: uwr_def uwr_notrunning_def pch_same_for_domain_except_shared_def
                            instrs_obeying_ta_def)
      (* show that the instruction hasn't affected our visible part of pch *)
      apply (drule(1) in_inter_empty)
      apply (clarsimp simp: all_addrs_of_def)
      apply (rule pch_partitioned_read, clarsimp)
      apply (erule(1) diff_domain_no_collision, simp)
      done
  next
    case (IWrite x2)
    then show ?thesis using assms
      apply (clarsimp simp: uwr_def uwr_notrunning_def pch_same_for_domain_except_shared_def
                            instrs_obeying_ta_def)
      apply (thin_tac "s' = _")
      apply (drule(1) in_inter_empty)
      apply (intro conjI)
       apply (clarsimp simp: all_addrs_of_def)
       apply (rule pch_partitioned_write, clarsimp)
       apply (erule(1) diff_domain_no_collision, simp)
      apply (rule do_write_maintains_external_uwr_out)
      apply (clarsimp simp: all_addrs_of_def)
      apply (clarsimp simp: instrs_safe_def kernel_shared_precise_def)
      done
  next
    case (IRegs x3)
    then show ?thesis using assms
      by (clarsimp simp: uwr_def uwr_notrunning_def pch_same_for_domain_except_shared_def)
  next
    case IFlushL1
    then show ?thesis using assms
      by (clarsimp simp: uwr_def uwr_notrunning_def pch_same_for_domain_except_shared_def)
  next
    case (IFlushL2 x5)
    then show ?thesis using assms
      apply (clarsimp simp: uwr_def uwr_notrunning_def pch_same_for_domain_except_shared_def
                            instrs_obeying_ta_def)
      apply (rule sym, rule pch_partitioned_flush, clarsimp)
      apply (drule(2) in_sub_inter_empty)
      apply (thin_tac "s' = _") (* just clearing junk *)
      apply (clarsimp simp: all_addrs_of_def)
      apply (erule(2) diff_domain_no_collision)
      done
  next
    case IReadTime
    then show ?thesis using assms
      by (clarsimp simp: uwr_def uwr_notrunning_def pch_same_for_domain_except_shared_def)
  next
    case (IPadToTime x7)
    then show ?thesis using assms
      by (clarsimp simp: uwr_def uwr_notrunning_def pch_same_for_domain_except_shared_def)
qed



lemma programs_obeying_ta_head_and_rest:
  "h # r \<in> programs_obeying_ta ta \<Longrightarrow>
   h \<in> instrs_obeying_ta ta \<and> r \<in> programs_obeying_ta ta"
  apply (clarsimp simp: programs_obeying_ta_def)
  done

lemma programs_safe_head_and_rest:
  "h # r \<in> programs_safe \<Longrightarrow>
   h \<in> instrs_safe \<and> r \<in> programs_safe"
  apply (clarsimp simp: programs_safe_def)
  done                          

lemma d_not_running_integrity_uwr:
  "\<lbrakk>p \<in> programs_obeying_ta ta;
  p \<in> programs_safe; 
  current_domain' s \<noteq> d;
  ta \<inter> all_addrs_of d = {} \<rbrakk> \<Longrightarrow>
  (s, instr_multistep p s) \<in> uwr d"
  apply (induct p arbitrary: s; clarsimp)
  apply (drule programs_obeying_ta_head_and_rest, clarsimp)
  apply (drule programs_safe_head_and_rest, clarsimp)
  apply (subgoal_tac "current_domain' (instr_step a s) \<noteq> d")
   defer
   using safe_no_domainswitch
   apply blast
  apply (drule_tac x="instr_step a s" in meta_spec)
  apply (rule_tac b="instr_step a s" in uwr_trans)
   defer
   apply assumption 
  (* now we are down to the single step *)
  apply (erule_tac i=a and ta=ta in d_not_running_step; simp)
  done

(* d not running \<rightarrow> d not running *)
lemma d_not_running: "\<lbrakk>
   \<comment> \<open>we have two programs derived from touched_addresses - may not be the same touched_addresses\<close>
   p\<^sub>s \<in> programs_obeying_ta ta\<^sub>s;
   p\<^sub>t \<in> programs_obeying_ta ta\<^sub>t;   
   p\<^sub>s \<in> programs_safe;
   p\<^sub>t \<in> programs_safe;
   \<comment> \<open>we may not have concrete touched_addresses -
     we may overapprox this to the whole currently running domain.
     NB: I think it's enough just to require it not contain any of d's addresses. -robs.\<close>
   \<comment> \<open>these touched_addresses does NOT contain any addresses from d\<close>
   ta\<^sub>s \<inter> all_addrs_of d = {};
   ta\<^sub>t \<inter> all_addrs_of d = {};
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
  apply clarsimp
  apply (subgoal_tac "current_domain' t \<noteq> d")
   apply (drule(3) d_not_running_integrity_uwr [where s=s])
   apply (drule(3) d_not_running_integrity_uwr [where s=t])
  apply (rule uwr_trans, subst uwr_sym, assumption)
   apply (rule uwr_trans, assumption, assumption)
  using uwr_same_domain apply blast
  done
  
  

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
  oops

lemma programs_obeying_ta_preserve_uwr: "\<lbrakk>
   \<not> can_domain_switch (other_state s);
   \<not> can_domain_switch (other_state t);
   touched_addrs_inv' s;
   touched_addrs_inv' t;
   is_secure_nondomainswitch p\<^sub>s s;
   is_secure_nondomainswitch p\<^sub>t t;
   (s, t) \<in> uwr d;
   current_domain' s = d \<longrightarrow> p\<^sub>s = p\<^sub>t;
   s' = instr_multistep p\<^sub>s s;
   t' = instr_multistep p\<^sub>t t
   \<rbrakk> \<Longrightarrow>
   (s', t') \<in> uwr d"
  apply(clarsimp simp:is_secure_nondomainswitch_def)
  apply(frule uwr_same_domain)
  apply(case_tac "current_domain' s = d")
   apply clarsimp
   apply(prop_tac "current_domain' s' = d")
    apply(metis no_domainswitch_inv)
   apply(rule d_running)
        apply force
       apply force
      apply(force simp:touched_addrs_inv_def)
     apply force
    apply force
   apply force
  apply(frule uwr_same_touched_addrs)
    apply force
   apply force
  apply(prop_tac "current_domain' s' \<noteq> d")
   apply(metis no_domainswitch_inv)
  apply clarsimp
  apply(rule d_not_running[where s=s and t=t and p\<^sub>s=p\<^sub>s and p\<^sub>t=p\<^sub>t and
        ta\<^sub>s="touched_addrs' s" and ta\<^sub>t="touched_addrs' t"])
            apply force
           apply force
          apply force
         apply force
        (* using touched_addrs_inv' *)
        defer (* FIXME: Think more about these two. -robs. *)
       defer
      apply force
     apply force
    apply force
   apply force
  apply force
  sorry

end

locale time_protection_system =
  unwinding_system A s0 "\<lambda>_. current_domain" external_uwr policy out Sched +
  time_protection collides_in_pch fch_lookup pch_lookup
    fch_read_impact pch_read_impact fch_write_impact pch_write_impact
    read_cycles write_cycles do_read do_write store_time padding_regs_impact
    empty_fch fch_flush_cycles do_pch_flush pch_flush_cycles addr_domain addr_colour colour_userdomain
    current_domain external_uwr  touched_addrs can_domain_switch
  for A :: "('a,'other_state,unit) data_type"
  and s0 :: "'other_state"
  and current_domain :: "'other_state \<Rightarrow> 'userdomain domain"
  and external_uwr :: "'userdomain domain \<Rightarrow> ('other_state \<times> 'other_state) set"
  and policy :: "('userdomain domain \<times> 'userdomain domain) set"
  and out :: "'userdomain domain \<Rightarrow> 'other_state \<Rightarrow> 'p"
  and collides_in_pch :: "address rel"
  and fch_lookup :: "'fch \<Rightarrow> 'fch_cachedness fch"
  and pch_lookup :: "'pch \<Rightarrow> 'pch_cachedness pch"
  and fch_read_impact :: "'fch fch_impact"
  and pch_read_impact :: "('fch, 'pch) pch_impact"
  and fch_write_impact :: "'fch fch_impact"
  and pch_write_impact :: "('fch, 'pch) pch_impact"
  and read_cycles  :: "'fch_cachedness \<Rightarrow> 'pch_cachedness \<Rightarrow> time"
  and write_cycles :: "'fch_cachedness \<Rightarrow> 'pch_cachedness \<Rightarrow> time"
  and do_read :: "address \<Rightarrow> 'other_state \<Rightarrow> 'regs \<Rightarrow> 'regs"
  and do_write :: "address \<Rightarrow> 'other_state \<Rightarrow> 'regs \<Rightarrow> 'other_state"
  and store_time :: "time \<Rightarrow> 'regs \<Rightarrow> 'regs"
  and padding_regs_impact :: "time \<Rightarrow> 'regs \<Rightarrow> 'regs"
  and empty_fch :: "'fch"
  and fch_flush_cycles :: "'fch \<Rightarrow> time"
  and do_pch_flush :: "'pch \<Rightarrow> address set \<Rightarrow> 'pch"
  and pch_flush_cycles :: "'pch \<Rightarrow> address set \<Rightarrow> time"
  and addr_domain :: "address \<Rightarrow> 'userdomain domain"
  and addr_colour :: "address \<Rightarrow> 'colour"
  and colour_userdomain :: "'colour \<Rightarrow> 'userdomain"
  and touched_addrs :: "'other_state \<Rightarrow> address set"
  and can_domain_switch :: "'other_state \<Rightarrow> bool" +
  fixes initial_regs :: "'regs"
  fixes initial_pch :: "'pch"
  assumes touched_addrs_inv:
    "reachable s \<Longrightarrow> touched_addrs_inv s"

begin

definition has_secure_domainswitch :: "('fch,'pch,'regs,'other_state)state \<Rightarrow>
  ('fch,'pch,'regs,'other_state)state \<Rightarrow> bool"
  where
  "has_secure_domainswitch s s' \<equiv>
     \<comment> \<open>Oblige the instantiator to ensure that in all possible reachable situations where the
         uwr holds there exists a domain-switch implementation pair that would preserve it.\<close>
     \<forall>d t t'. reachable (other_state t) \<and>
       (s, t) \<in> uwr d \<and> \<comment> \<open>The \<open>uwr\<close> should give us \<open>can_domain_switch (other_state t)\<close>.\<close>
       (other_state t, other_state t') \<in> Step () \<longrightarrow>
        (\<exists> p q.
           s' = instr_multistep p s \<and>
           t' = instr_multistep q t \<and>
           (s', t') \<in> uwr d)"

definition has_secure_implementation :: "('fch,'pch,'regs,'other_state)state \<Rightarrow>
  ('fch,'pch,'regs,'other_state)state \<Rightarrow> bool"
  where
  "has_secure_implementation s s' \<equiv>
     if can_domain_switch (other_state s)
       then has_secure_domainswitch s s'
       else has_secure_nondomainswitch s s'"

end

locale securely_implementable =
  time_protection_system A s0 current_domain external_uwr policy out
  collides_in_pch fch_lookup pch_lookup
  fch_read_impact pch_read_impact fch_write_impact pch_write_impact
  read_cycles write_cycles do_read do_write store_time padding_regs_impact
  empty_fch fch_flush_cycles do_pch_flush pch_flush_cycles addr_domain addr_colour colour_userdomain
  touched_addrs can_domain_switch initial_regs initial_pch

  for A :: "('a,'other_state,unit) data_type"
  and s0 :: "'other_state"
  and current_domain :: "'other_state \<Rightarrow> 'userdomain domain"
  and external_uwr :: "'userdomain domain \<Rightarrow> ('other_state \<times> 'other_state) set"
  and policy :: "('userdomain domain \<times> 'userdomain domain) set"
  and out :: "'userdomain domain \<Rightarrow> 'other_state \<Rightarrow> 'p"
  and collides_in_pch :: "address rel"
  and fch_lookup :: "'fch \<Rightarrow> 'fch_cachedness fch"
  and pch_lookup :: "'pch \<Rightarrow> 'pch_cachedness pch"
  and fch_read_impact :: "'fch fch_impact"
  and pch_read_impact :: "('fch, 'pch) pch_impact"
  and fch_write_impact :: "'fch fch_impact"
  and pch_write_impact :: "('fch, 'pch) pch_impact"
  and read_cycles  :: "'fch_cachedness \<Rightarrow> 'pch_cachedness \<Rightarrow> time"
  and write_cycles :: "'fch_cachedness \<Rightarrow> 'pch_cachedness \<Rightarrow> time"
  and do_read :: "address \<Rightarrow> 'other_state \<Rightarrow> 'regs \<Rightarrow> 'regs"
  and do_write :: "address \<Rightarrow> 'other_state \<Rightarrow> 'regs \<Rightarrow> 'other_state"
  and store_time :: "time \<Rightarrow> 'regs \<Rightarrow> 'regs"
  and padding_regs_impact :: "time \<Rightarrow> 'regs \<Rightarrow> 'regs"
  and empty_fch :: "'fch"
  and fch_flush_cycles :: "'fch \<Rightarrow> time"
  and do_pch_flush :: "'pch \<Rightarrow> address set \<Rightarrow> 'pch"
  and pch_flush_cycles :: "'pch \<Rightarrow> address set \<Rightarrow> time"
  and addr_domain :: "address \<Rightarrow> 'userdomain domain"
  and addr_colour :: "address \<Rightarrow> 'colour"
  and colour_userdomain :: "'colour \<Rightarrow> 'userdomain"
  and touched_addrs :: "'other_state \<Rightarrow> address set"
  and can_domain_switch :: "'other_state \<Rightarrow> bool"
  and initial_regs :: "'regs"
  and initial_pch :: "'pch" +
  assumes reachable_steps_have_secure_implementation_specific:
    "(\<And> s s'.
       reachable (other_state s) \<Longrightarrow>
       (other_state s, other_state s') \<in> Step () \<Longrightarrow>
       has_secure_implementation s s')"
begin

lemma reachable_steps_have_secure_implementation_nonspecific:
  "(\<And> s os'.
     reachable (other_state s) \<Longrightarrow>
     (other_state s, os') \<in> Step () \<Longrightarrow>
     \<exists>s'. os' = other_state s' \<and> has_secure_implementation s s')"
  using reachable_steps_have_secure_implementation_specific
  by (metis state.select_convs(5))

definition A_extended_Step :: "unit \<Rightarrow>
  ('fch,'pch,'regs,'other_state)state rel"
  where
  "A_extended_Step \<equiv> \<lambda>_. {(s, s').
     (other_state s, other_state s') \<in> Step () \<and>
     has_secure_implementation s s'}"

definition A_extended ::
  "(('fch,'pch,'regs,'other_state)state,
    ('fch,'pch,'regs,'other_state)state,unit) data_type"
  where
  "A_extended = \<lparr> Init = \<lambda>s. {s}, Fin = id, Step = A_extended_Step \<rparr>"

definition A_extended_state ::
  "'other_state \<Rightarrow> ('fch,'pch,'regs,'other_state)state"
  where
  "A_extended_state s =
     \<lparr> fch = empty_fch, pch = initial_pch, tm = 0, regs = initial_regs, other_state = s \<rparr>"

(* This is now redundant with the Init_inv_Fin_system interpretation below, but I'll commit this
   at least once in case we change something and are left only with Init_Fin_system. -robs. *)
interpretation tpni: Init_Fin_system A_extended "A_extended_state s0"
  apply unfold_locales
     (* Init_Fin_system.reachable_s0 *)
     apply(clarsimp simp:A_extended_state_def A_extended_def A_extended_Step_def)
     apply(clarsimp simp:system.reachable_def execution_def)
     apply(metis (no_types, lifting) foldl_Nil singletonI steps_def)
    (* Init_Fin_system.Fin_Init *)
    apply(force simp:A_extended_def)
   (* Init_Fin_system.Init_Fin *)
   apply(force simp:A_extended_def)
  (* Init_Fin_system.obs_det_or_no_abs *)
  apply(rule disjI2)
  apply(force simp:system.no_abs_def A_extended_def)
  done

interpretation tpni: Init_inv_Fin_system A_extended "A_extended_state s0"
  apply unfold_locales
    (* Init_Fin_system.Fin_Init_s0 *)
    apply(force simp:A_extended_state_def A_extended_def)
   (* Init_Fin_system.Init_inv_Fin *)
   apply(force simp:A_extended_def)
  (* Init_Fin_system.Fin_inj *)
  apply(force simp:A_extended_def)
  done

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

lemma to_extended_step_enabledness:
 "\<lbrakk>reachable (other_state s);
   \<exists>s'. (other_state s, other_state (s'::('fch,'pch,'regs,'other_state)state)) \<in> Step ()
  \<rbrakk> \<Longrightarrow> \<exists>s'. (s, s') \<in> system.Step A_extended ()"
  apply clarsimp
  apply(frule_tac os'="other_state s'" in reachable_steps_have_secure_implementation_nonspecific)
   apply force
  apply clarsimp
  apply(rename_tac s' s'')
  apply(rule_tac x=s'' in exI)
  by (clarsimp simp:system.Step_def execution_def A_extended_def A_extended_Step_def steps_def)

lemma to_some_extended_step:
 "\<lbrakk>reachable (other_state s);
   (other_state s, os') \<in> Step ()
  \<rbrakk> \<Longrightarrow> \<exists>s'. os' = other_state s' \<and> (s, s') \<in> system.Step A_extended ()"
  apply(frule_tac os'="os'" in reachable_steps_have_secure_implementation_nonspecific)
   apply force
  apply clarsimp
  apply(rule_tac x=s' in exI)
  apply(rule conjI)
   apply force
  unfolding tpni.Step_def (* Warning: This unfold has to happen first for some reason -robs. *)
  apply(force simp:execution_def A_extended_def A_extended_Step_def steps_def)
  done

lemma to_specific_extended_step:
 "\<lbrakk>reachable (other_state s);
   (other_state s, other_state s') \<in> Step ()
  \<rbrakk> \<Longrightarrow> (s, s') \<in> system.Step A_extended ()"
  apply(frule_tac s'=s' in reachable_steps_have_secure_implementation_specific)
   apply force
  unfolding tpni.Step_def (* Warning: This unfold has to happen first for some reason -robs. *)
  apply(force simp:execution_def A_extended_def A_extended_Step_def steps_def)
  done

lemma to_extended_execution_enabledness:
 "\<lbrakk>tpni.reachable s;
   reachable (other_state s);
   \<exists>os'. os' \<in> execution A (other_state s) js \<comment> \<open>enabledness of original system at (other_state s)\<close>\<rbrakk>
  \<Longrightarrow> \<exists>s'. s' \<in> execution A_extended s js" \<comment> \<open>enabledness of extended system at s\<close>
  apply(induct js arbitrary:s)
   apply(force simp:execution_def steps_def A_extended_def)
  apply clarsimp
  apply(rename_tac js s os')
  (* We need s' to be an extension of os'. But we also need it to be
     a state we arrive at after one tpni.Step from s. *)
  apply(frule_tac as="() # js" in execution_Run)
  apply clarsimp
  apply(rename_tac js s os'' os')
  apply(frule_tac os'="os''" in reachable_steps_have_secure_implementation_nonspecific)
   apply force
  apply clarsimp
  apply(rename_tac js s os' s'')
  apply(erule_tac x=s'' in meta_allE)
  apply(erule meta_impE)
   apply(rule_tac a="()" in tpni.reachable_Step)
    apply force
   unfolding tpni.Step_def (* For some reason this can't just be in the simps on the next line. *)
   apply(force simp:execution_def A_extended_def A_extended_Step_def steps_def)
  apply(erule meta_impE)
   using reachable_Step apply force
  apply(erule meta_impE)
   using reachable_Step reachable_enabled apply force
  apply clarsimp
  apply(rename_tac js s os' s'' s')
  apply(frule_tac s'=s'' in to_specific_extended_step)
   apply force
  apply(prop_tac "tpni.reachable s''")
   using tpni.reachable_Step apply blast
  apply(prop_tac "tpni.reachable s'")
   using tpni.reachable_execution apply blast
  apply(rule_tac x=s' in exI)
  apply(drule_tac as="() # js" in tpni.execution_Run)
  apply clarsimp
  using tpni.execution_Run by auto

interpretation tpni: unwinding_system A_extended "A_extended_state s0" "\<lambda>_. current_domain'" uwr
  policy "\<lambda>d s. out d (other_state s)" Sched
  apply unfold_locales
      (* enabled_system.enabled *)
      apply(prop_tac "reachable (other_state s)")
       apply(simp only:system.reachable_def[symmetric])
       apply(force dest:to_original_reachability)
      apply(simp only:tpni.reachable_def[symmetric])
      apply(frule_tac js=js in enabled[simplified reachable_def[symmetric]])
      using to_extended_execution_enabledness apply blast
     (* noninterference_policy.uwr_equiv_rel *)
     using extended_uwr_equiv_rel apply blast
    (* noninterference_policy.schedIncludesCurrentDom *)
    using uwr_same_domain apply blast
   (* noninterference_policy.schedFlowsToAll *)
   using schedFlowsToAll apply blast
  (* noninterference_policy.schedNotGlobalChannel *)
  using schedNotGlobalChannel apply blast
  done

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
  apply(prop_tac "((current_domain (other_state s), u) \<in> policy) \<longrightarrow>
        uwr2 (other_state s) (current_domain (other_state s)) (other_state t)")
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
  apply(frule can_domain_switch_public)
  apply(clarsimp simp:has_secure_implementation_def split:if_splits)
   apply(clarsimp simp:has_secure_domainswitch_def)
   apply(metis enabled_Step to_some_extended_step tpni.uwr_sym tpni.uwr_trans)
   (* Note: Another proof. Are the use of these lemmas by these metis proofs suspicious? -robs.
   apply(metis enabled_Step reachable_steps_have_secure_implementation_nonspecific tpni.uwr_sym tpni.uwr_trans) *)
  apply(clarsimp simp:has_secure_nondomainswitch_def)
  apply(rename_tac u s t s_priv' s_priv t_priv' t_priv p\<^sub>t p\<^sub>s)
  apply(erule_tac x=t in allE)
  apply(erule_tac x=p\<^sub>t in allE)
  apply clarsimp
  apply(rule programs_obeying_ta_preserve_uwr, simp_all)
   apply(force simp:touched_addrs_inv)
  apply(force simp:touched_addrs_inv)
  done

theorem extended_Nonleakage:
  "Nonleakage_gen \<Longrightarrow> tpni.Nonleakage_gen"
  using Nonleakage_gen_confidentiality_u extended_confidentiality_u tpni.Nonleakage_gen
  by blast

end
end