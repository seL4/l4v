(*
 * Copyright 2021, UNSW (ABN 57 195 873 179),
 * Copyright 2021, The University of Melbourne (ABN 84 002 705 224).
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory TimeProtection
imports "Word_Lib.WordSetup"
  InfoFlow.Noninterference_Base_Refinement
  "Lib.Apply_Trace_Cmd"
begin

(* questions:
  - do we want to support a writeback `fch`?
    - We know how we'd implement it, we dont think it would be heaps more work. we just need
      to know if it's needed.
*)

datatype vaddr = VAddr machine_word
type_synonym paddr = machine_word

type_synonym vpaddr = "vaddr \<times> paddr"

\<comment> \<open> flushable (fch) and partitionable (pch) caches\<close>
type_synonym 'fch_cachedness fch = "vaddr \<Rightarrow> 'fch_cachedness"
type_synonym 'pch_cachedness pch = "paddr \<Rightarrow> 'pch_cachedness"
type_synonym 'fch fch_impact = "vaddr \<Rightarrow> 'fch \<Rightarrow> 'fch"
(* Note: This `pch_impact` version only supports a writethrough `fch`. *)
type_synonym 'pch pch_impact = "paddr \<Rightarrow> 'pch \<Rightarrow> 'pch"
(* FIXME: If we want to support a writeback `fch`, we'll need to use a type signature like this
  instead. This is because when a read or write evicts a dirty `fch` entry, that dirty bit (and value)
  will need to be propagated to the corresponding `pch` entry. -robs.
type_synonym ('fch,'pch) pch_impact = "vaddr \<Rightarrow> 'fch \<Rightarrow> 'pch \<Rightarrow> 'pch" *)

type_synonym time = nat

record ('fch,'pch) state =
  fch :: "'fch" \<comment> \<open> flushable cache\<close>
  pch :: "'pch" \<comment> \<open> partitionable cache \<close>
  tm :: time

locale time_protection_hardware =
  fixes gentypes :: "('fch \<times> 'fch_cachedness \<times> 'pch \<times> 'pch_cachedness \<times> 'domain \<times> 'colour) itself"
  fixes Sched :: "'domain"

  \<comment> \<open>flushable cache\<close>
  fixes fch_lookup :: "'fch \<Rightarrow> 'fch_cachedness fch"
  fixes fch_read_impact :: "'fch fch_impact"
  fixes fch_write_impact :: "'fch fch_impact"
  fixes empty_fch :: "'fch"
  fixes fch_flush_cycles :: "'fch \<Rightarrow> time" (*FIXME: should this be dependent on anything else? *)
  fixes fch_flush_WCET :: "time"
  assumes fch_flush_cycles_obeys_WCET:
    "\<forall> fch. fch_flush_cycles fch \<le> fch_flush_WCET"


  \<comment> \<open>partitionable cache\<close>
  fixes pch_lookup :: "'pch \<Rightarrow> 'pch_cachedness pch"
  fixes pch_read_impact :: "'pch pch_impact"
  fixes pch_write_impact :: "'pch pch_impact"
  fixes do_pch_flush :: "'pch \<Rightarrow> paddr set \<Rightarrow> 'pch"
  fixes pch_flush_cycles :: "'pch \<Rightarrow> paddr set \<Rightarrow> time" \<comment> \<open>could this be dependent on anything else?\<close>
  fixes pch_flush_WCET :: "paddr set \<Rightarrow> time"
  assumes pch_flush_cycles_obeys_WCET:
    "\<forall> pch. pch_flush_cycles pch as \<le> pch_flush_WCET as"
  (* "a coll b" = "a may cause b to be evicted from or loaded into the pch" *)
  fixes collides_in_pch :: "paddr \<Rightarrow> paddr \<Rightarrow> bool" (infix "coll" 50)
  (* collides_in_pch isn't a relation, but it is kind of an equivalence *)
  assumes collides_with_equiv: "equiv UNIV {(x, y). x coll y}" (*FIXME: should do_pch_flush also affect the fch? *)
  (* pch_read_impact only impacts colliding addresses *)
  assumes pch_partitioned_read:
    "\<not>a coll b \<Longrightarrow> pch_lookup p b = pch_lookup (pch_read_impact a p) b"
  (* if `b` can be impacted by a read from `a`,
     we require that this impact depends only on the prior state of the fch
     and the prior cachedness of the rest of their collision set in the pch *)
  assumes pch_collision_read: "\<And>a b pchs pcht.
    a coll b \<Longrightarrow>
    \<forall>c. a coll c \<longrightarrow> pch_lookup pchs c = pch_lookup pcht c \<Longrightarrow>
    \<comment> \<open>This might be stronger than is met by hardware that just promises
        a 'random' replacement algorithm. Essentially we are requiring that
        any such 'randomness' cannot be influenced by the prior cachedness of
        addresses outside the collision set in question. \<close>
    pchs' = pch_read_impact a pchs \<Longrightarrow>
    pcht' = pch_read_impact a pcht \<Longrightarrow>
    pch_lookup pchs' b = pch_lookup pcht' b"
  (* pch_write_impact only impacts colliding addresses *)
  assumes pch_partitioned_write:
    "\<not>a coll b \<Longrightarrow> pch_lookup p b = pch_lookup (pch_write_impact a p) b"
  (* similar to pch_collision_read *)
  assumes pch_collision_write: "\<And>a b pchs pcht.
    a coll b \<Longrightarrow>
    \<forall>c. a coll c \<longrightarrow> pch_lookup pchs c = pch_lookup pcht c \<Longrightarrow>
    \<comment> \<open>The same strong requirement placing limits on the 'randomness'
        of the cache replacement algorithm as for @{term pch_collision_read}\<close>
    pchs' = pch_write_impact a pchs \<Longrightarrow>
    pcht' = pch_write_impact a pcht \<Longrightarrow>
    pch_lookup pchs' b = pch_lookup pcht' b"
  (* pch flush only affects addresses that collide with the set *)
  assumes pch_partitioned_flush:
   "(\<forall>a'\<in>as. \<not> a coll a') \<Longrightarrow> pch_lookup (do_pch_flush p as) a = pch_lookup p a"
  assumes pch_collision_flush:
    "\<exists>a1\<in>as. a coll a1 \<Longrightarrow>
    pch_lookup (do_pch_flush pchs as) a = pch_lookup (do_pch_flush pcht as) a"
  (* if all colliding addresses to @{term as} are the same, then the flush will take the same amount of time *)
  assumes pch_flush_cycles_localised:
    "\<forall>a1. (\<exists>a2\<in>as. a1 coll a2) \<longrightarrow> pch_lookup pchs a1 = pch_lookup pcht a1 \<Longrightarrow>
    pch_flush_cycles pchs as = pch_flush_cycles pcht as"

  
  \<comment> \<open>the time taken to do reads and writes\<close>
  fixes read_cycles  :: "'fch_cachedness \<Rightarrow> 'pch_cachedness \<Rightarrow> time"
  fixes write_cycles :: "'fch_cachedness \<Rightarrow> 'pch_cachedness \<Rightarrow> time"
  
  
  \<comment> \<open>domains / colours / collisions\<close>
  fixes addr_domain :: "paddr \<Rightarrow> 'domain"
  fixes addr_colour :: "paddr \<Rightarrow> 'colour"
  fixes colour_userdomain :: "'colour \<Rightarrow> 'domain"
  assumes colour_not_Sched:
    "colour_userdomain c \<noteq> Sched"
  assumes no_cross_colour_collisions:
    "a1 coll a2 \<Longrightarrow> addr_colour a1 = addr_colour a2"
  (* every physical address either belongs to the scheduler or is correctly coloured *)
  assumes addr_domain_valid: "addr_domain a = Sched
                            \<or> addr_domain a = colour_userdomain (addr_colour a)"
begin

corollary colours_not_shared:
  "colour_userdomain c1 \<noteq> colour_userdomain c2 \<Longrightarrow> c1 \<noteq> c2"
  by blast

abbreviation collision_set :: "paddr \<Rightarrow> paddr set" where
  "collision_set a \<equiv> {b. a coll b}"

lemma collision_set_contains_itself: "a \<in> collision_set a"
  using collides_with_equiv
  by (clarsimp simp:equiv_def refl_on_def)

lemma collision_collect:
  "a coll b = ((a, b) \<in> (Collect (case_prod collides_in_pch)))"
  by simp

lemma collision_sym [simp]:
  "a coll b \<Longrightarrow> b coll a"
  using collision_collect
  by (meson collides_with_equiv equiv_def symE)

\<comment> \<open> the addresses in kernel shared memory (which for now is everything in the sched domain)\<close>
definition kernel_shared_precise :: "paddr set" where
  "kernel_shared_precise \<equiv> {a. addr_domain a = Sched}"

\<comment> \<open> the kernel shared memory, including cache colliding addresses \<close>
definition kernel_shared_expanded :: "paddr set" where
  "kernel_shared_expanded \<equiv> {a. \<exists> z \<in> kernel_shared_precise. a \<in> collision_set z}"

\<comment> \<open> a full collision set contains all of its own collisions \<close>
definition full_collision_set :: "paddr set \<Rightarrow> bool" where
  "full_collision_set S \<equiv> \<forall>a1\<in>S. \<forall>a2. a1 coll a2 \<longrightarrow> a2 \<in> S"

lemma collision_set_full_collision_set:
  "full_collision_set (collision_set a)"
  apply (clarsimp simp: full_collision_set_def)
  using collision_collect
  apply (meson collides_with_equiv equiv_def trans_def)
  done

lemma kernel_shared_expanded_full_collision_set:
  "full_collision_set kernel_shared_expanded"
  apply (clarsimp simp: kernel_shared_expanded_def full_collision_set_def)
  using collision_collect
  apply (meson collides_with_equiv equiv_def trans_def)
  done

\<comment> \<open> in a full collision set S, if two addresses collide and one is not in the set, the other
     is also not in the set. \<close>
lemma collision_in_full_collision_set:
  "full_collision_set S \<Longrightarrow>
  a1 coll a2 \<Longrightarrow>
  a1 \<notin> S \<Longrightarrow>
  a2 \<notin> S"
  apply (clarsimp simp: full_collision_set_def)
  done

definition pch_same_for_domain ::
  "'domain \<Rightarrow> 'pch \<Rightarrow> 'pch \<Rightarrow> bool"
  where
 "pch_same_for_domain d p1 p2 \<equiv> \<forall> a. addr_domain a = d \<longrightarrow> pch_lookup p1 a = pch_lookup p2 a"

definition pch_same_for_domain_and_shared ::
  "'domain \<Rightarrow> 'pch \<Rightarrow> 'pch \<Rightarrow> bool"
  where
 "pch_same_for_domain_and_shared d p1 p2 \<equiv>
    \<forall> a. addr_domain a = d \<or> a \<in> kernel_shared_expanded \<longrightarrow> pch_lookup p1 a = pch_lookup p2 a"

definition pch_same_for_domain_except_shared ::
  "'domain \<Rightarrow> 'pch \<Rightarrow> 'pch \<Rightarrow> bool"
  where
 "pch_same_for_domain_except_shared d p1 p2 \<equiv>
    \<forall> a. addr_domain a = d \<and> a \<notin> kernel_shared_expanded \<longrightarrow> pch_lookup p1 a = pch_lookup p2 a"

(* the different ways our trace can interact with microarch state *)
datatype trace_unit = IRead vpaddr           \<comment> \<open>read from some address\<close>
                    | IWrite vpaddr          \<comment> \<open>write to some address\<close>
                    | IFlushL1               \<comment> \<open>flush the entire L1 cache(s)\<close>
                    | IFlushL2 "paddr set"   \<comment> \<open>flush some part L2 cache(s)\<close>
                    | IPadToTime time        \<comment> \<open>pad the time up to some point, if that time is in the future\<close>

primrec
  trace_step :: "trace_unit \<Rightarrow>
    ('fch,'pch)state \<Rightarrow>
    ('fch,'pch)state" where
 "trace_step (IRead a) s =
      s\<lparr>fch := fch_read_impact (fst a) (fch s),
        pch := pch_read_impact (snd a) (pch s),
        tm  := tm s + read_cycles (fch_lookup (fch s) (fst a)) (pch_lookup (pch s) (snd a))\<rparr>"
  | "trace_step (IWrite a) s =
      s\<lparr>fch := fch_write_impact (fst a) (fch s),
        pch := pch_write_impact (snd a) (pch s),
        tm  := tm s + write_cycles (fch_lookup (fch s) (fst a)) (pch_lookup (pch s) (snd a))\<rparr>"
  | "trace_step (IPadToTime t) s =
      s\<lparr>tm := max (tm s) t\<rparr>" \<comment> \<open>will not step backwards\<close>
  | "trace_step IFlushL1 s =
      s\<lparr>fch := empty_fch,
        tm := tm s + fch_flush_cycles (fch s)\<rparr>"
  | "trace_step (IFlushL2 as) s =
      s\<lparr>pch := do_pch_flush (pch s) as,
        tm := tm s + pch_flush_cycles (pch s) as\<rparr>"

type_synonym trace = "trace_unit list"

primrec trace_multistep :: "trace \<Rightarrow>
  ('fch,'pch)state \<Rightarrow>
  ('fch,'pch)state" where
  "trace_multistep [] s = s"
| "trace_multistep (i#is) s = trace_multistep is (trace_step i s)"

definition
  trace_units_obeying_set :: "vpaddr set \<Rightarrow> trace_unit set" where
 "trace_units_obeying_set vps \<equiv> {i. case i of
                                 IRead a  \<Rightarrow> a \<in> vps
                               | IWrite a \<Rightarrow> a \<in> vps
                               | IFlushL2 as \<Rightarrow> as \<subseteq> snd ` vps
                               | _        \<Rightarrow> True }"

(* these are the programs that could have created this ta *)
definition
  traces_obeying_set :: "vpaddr set \<Rightarrow> trace set" where
 "traces_obeying_set vps \<equiv> {p. list_all (\<lambda>i. i \<in> trace_units_obeying_set vps) p}"

lemma hd_trace_obeying_set [dest]:
  "a # p \<in> traces_obeying_set ta \<Longrightarrow> a \<in> trace_units_obeying_set ta \<and> p \<in> traces_obeying_set ta"
  by (force simp:traces_obeying_set_def)

definition
  WCET_bounded_traces :: "time \<Rightarrow> ('fch,'pch)state \<Rightarrow> trace set" where
 "WCET_bounded_traces wc s \<equiv> {p. tm (trace_multistep p s) \<le> tm s + wc}"

definition
  WCET_bounded_traces_universal :: "time \<Rightarrow> trace set" where
 "WCET_bounded_traces_universal wc \<equiv> {p. \<forall> s. tm (trace_multistep p s) \<le> tm s + wc}"

lemma trace_step_time_forward:
  "tm (trace_step i s) \<ge> tm s"
  apply (cases i; clarsimp)
  done

lemma trace_multistep_time_forward:
  "tm (trace_multistep p s) \<ge> tm s"
  apply (induction p arbitrary: s; clarsimp)
  apply (drule_tac x="trace_step a s" in meta_spec)
  using order_trans trace_step_time_forward apply blast
  done

lemma collides_with_set_or_doesnt:
  "\<lbrakk>\<forall>a'\<in>as. \<not> a coll a' \<Longrightarrow> P;
    \<exists>a'\<in>as. a coll a' \<Longrightarrow> P \<rbrakk> \<Longrightarrow>
    P"
  by blast

lemma diff_domain_no_collision:
  "\<lbrakk>a \<notin> kernel_shared_expanded;
  addr_domain a' \<noteq> addr_domain a;
  a coll a'\<rbrakk> \<Longrightarrow>
  False"
  apply (frule(1) collision_in_full_collision_set [OF kernel_shared_expanded_full_collision_set])
  apply (metis (mono_tags, lifting) kernel_shared_expanded_def kernel_shared_precise_def
    mem_Collect_eq time_protection_hardware.addr_domain_valid collision_set_contains_itself
    no_cross_colour_collisions time_protection_hardware_axioms)
  done

(* general set helpers *)

lemma in_image_union:
  "\<lbrakk>x \<in> S;
  f ` S \<subseteq> A \<union> B \<rbrakk> \<Longrightarrow>
  f x \<in> A \<or> f x \<in> B"
  apply blast
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

lemma and_or_specific':
  "((P \<or> Q \<Longrightarrow> R)) \<Longrightarrow>
   (P \<longrightarrow> R) \<and> (Q \<longrightarrow> R)"
  apply simp
  done

end


locale trace_selector =
  fixes gentypes :: "('state \<times> 'domain \<times> 'trace \<times> 'touchedaddresses) itself"
  fixes current_domain :: "'state \<Rightarrow> 'domain"
  fixes uwr :: "'domain \<Rightarrow> ('state \<times> 'state) set"
  fixes sched_domain :: "'domain"
  fixes default_trace :: "'trace"
  fixes trace_will_be_uwr_determined :: "'state \<Rightarrow> bool"
  fixes trace_will_be_public_determined :: "'state \<Rightarrow> bool"
  fixes select_trace :: "('state \<Rightarrow> 'touchedaddresses \<Rightarrow> 'trace set) \<Rightarrow> 'state \<Rightarrow> 'touchedaddresses \<Rightarrow> 'trace"
  assumes trace_from_set:
    "default_trace \<in> tfn s ta \<Longrightarrow> select_trace tfn s ta \<in> tfn s ta"
  assumes select_trace_uwr_determined:
    "trace_will_be_uwr_determined s \<Longrightarrow>
    (s, t) \<in> uwr (current_domain s) \<Longrightarrow>
    select_trace tfn s ta = select_trace tfn t ta"
  assumes select_trace_public_determined:
    "trace_will_be_public_determined s \<Longrightarrow>
    (s, t) \<in> uwr sched_domain \<Longrightarrow>
    select_trace tfn t ta = select_trace tfn s ta" 
  begin
corollary trace_from_superset: "default_trace \<in> tfn s ta \<Longrightarrow> q \<supseteq> tfn s ta \<Longrightarrow> select_trace tfn s ta \<in> q"
  by (simp add: in_mono trace_from_set)
end




locale time_protection_hardware_uwr =
  time_protection_hardware gentypes Sched fch_lookup fch_read_impact fch_write_impact empty_fch
    fch_flush_cycles fch_flush_WCET pch_lookup pch_read_impact pch_write_impact do_pch_flush
    pch_flush_cycles pch_flush_WCET collides_in_pch read_cycles write_cycles addr_domain
    addr_colour colour_userdomain
  for gentypes :: "('fch \<times> 'fch_cachedness \<times> 'pch \<times> 'pch_cachedness \<times> 'domain \<times> 'colour) itself"
  and Sched :: "'domain"
  and fch_lookup :: "'fch \<Rightarrow> 'fch_cachedness fch"
  and fch_read_impact :: "'fch fch_impact"
  and fch_write_impact :: "'fch fch_impact"
  and empty_fch :: "'fch"
  and fch_flush_cycles :: "'fch \<Rightarrow> time"
  and fch_flush_WCET :: "time"
  and pch_lookup :: "'pch \<Rightarrow> 'pch_cachedness pch"
  and pch_read_impact :: "'pch pch_impact"
  and pch_write_impact :: "'pch pch_impact"
  and do_pch_flush :: "'pch \<Rightarrow> paddr set \<Rightarrow> 'pch"
  and pch_flush_cycles :: "'pch \<Rightarrow> paddr set \<Rightarrow> time"
  and pch_flush_WCET :: "paddr set \<Rightarrow> time"
  and collides_in_pch :: "paddr \<Rightarrow> paddr \<Rightarrow> bool" (infix "coll" 50)
  and read_cycles  :: "'fch_cachedness \<Rightarrow> 'pch_cachedness \<Rightarrow> time"
  and write_cycles :: "'fch_cachedness \<Rightarrow> 'pch_cachedness \<Rightarrow> time"
  and addr_domain :: "paddr \<Rightarrow> 'domain"
  and addr_colour :: "paddr \<Rightarrow> 'colour"
  and colour_userdomain :: "'colour \<Rightarrow> 'domain" +
  fixes current_domain :: "'other_state \<Rightarrow> 'domain"
  fixes external_uwr :: "'domain \<Rightarrow> ('other_state \<times> 'other_state) set"
  fixes next_latest_domainswitch_start :: "time \<Rightarrow> time"
  assumes external_uwr_same_domain:
    "(s1, s2) \<in> external_uwr Sched \<Longrightarrow> current_domain s2 = current_domain s1"
  assumes external_uwr_equiv_rel:
    "equiv UNIV (external_uwr d)"

begin

abbreviation nlds where "nlds \<equiv> next_latest_domainswitch_start"

definition uwr_running where
  "uwr_running d \<equiv> {(s1, s2). fch s1 = fch s2
                            \<and> pch_same_for_domain_and_shared d (pch s1) (pch s2)
                            \<and> tm s1 = tm s2 }"

definition uwr_notrunning ::
  "'domain \<Rightarrow> ('fch,'pch)state rel"
  where
  "uwr_notrunning d \<equiv> {(s1, s2). pch_same_for_domain_except_shared d (pch s1) (pch s2)
                               \<and> nlds (tm s1) = nlds (tm s2) }"

definition uwr ::
  "'domain \<Rightarrow> ('other_state \<times> ('fch,'pch)state) rel"
  where
  "uwr d \<equiv> {((os1, s1), (os2, s2)). (os1, os2) \<in> external_uwr d
                    \<and> current_domain os2 = current_domain os1
                    \<and> (if (current_domain os1 = d)
                      then (s1, s2) \<in> uwr_running d
                      else (s1, s2) \<in> uwr_notrunning d ) }"

lemma uwr_external_uwr:
  "((so, s), (to, t)) \<in> uwr d \<Longrightarrow>
  (so, to) \<in> external_uwr d"
  apply (clarsimp simp: uwr_def)
  done

lemma external_uwr_refl [simp]:
  "(s, s) \<in> external_uwr d"
  using external_uwr_equiv_rel
  by (clarsimp simp: equiv_def refl_on_def)

lemma uwr_refl [simp]:
  "(s, s) \<in> uwr d"
  apply (clarsimp simp:uwr_def)
  apply (clarsimp simp: uwr_running_def pch_same_for_domain_and_shared_def)
  apply (clarsimp simp:uwr_notrunning_def pch_same_for_domain_except_shared_def)
  done

lemma uwr_sym':
  "((a, b) \<in> uwr d) \<Longrightarrow> ((b, a) \<in> uwr d)"
  apply (clarsimp simp: uwr_def)
  apply (case_tac "current_domain os2 = d"; clarsimp)
   apply (intro conjI, meson equiv_def external_uwr_equiv_rel symE)
   apply (clarsimp simp:uwr_running_def pch_same_for_domain_and_shared_def)
  apply (intro conjI, meson equiv_def external_uwr_equiv_rel symE)
  apply (clarsimp simp: uwr_notrunning_def pch_same_for_domain_except_shared_def)
  done

lemma uwr_trans:
  "(a, b) \<in> uwr d \<Longrightarrow>
  (b, c) \<in> uwr d \<Longrightarrow>
  (a, c) \<in> uwr d"
  apply (clarsimp simp: uwr_def)
  apply (case_tac "current_domain x = d"; clarsimp)
   apply (intro conjI, meson equiv_def external_uwr_equiv_rel transE)
   apply (clarsimp simp:uwr_running_def pch_same_for_domain_and_shared_def)
  apply (intro conjI, meson equiv_def external_uwr_equiv_rel transE)
  apply (clarsimp simp: uwr_notrunning_def pch_same_for_domain_except_shared_def)
  done

lemma uwr_equiv_rel:
  "equiv UNIV (uwr u)"
  apply(clarsimp simp:equiv_def)
  apply(intro conjI)
    \<comment> \<open>refl\<close>
    apply (clarsimp simp: refl_on_def)
   \<comment> \<open>sym\<close>
   apply (clarsimp simp:sym_def, erule uwr_sym')
  \<comment> \<open>trans\<close>
  apply (clarsimp simp:trans_def, erule uwr_trans, simp)
  done

end

(* a step transition can be split four ways:
  - oldclean - a step only accessing the old domain's memory
  - dirty - a publicly-deterministic step accessing both new and old domains
  - gadget - only the time protection mechanisms
  - newclean - a step only accessing the new domain's memory
 *)
definition can_split_four_ways :: "('s \<Rightarrow> bool) \<Rightarrow> ('s \<times> 's) set \<Rightarrow> ('s \<times> 's) set \<Rightarrow> ('s \<times> 's) set \<Rightarrow>
                                   ('s \<times> 's) set \<Rightarrow> ('s \<times> 's) set \<Rightarrow> bool" where
  "can_split_four_ways P step oldclean dirty gadget newclean \<equiv> \<forall> s1 s5. (P s1 \<longrightarrow> (s1, s5) \<in> step \<longrightarrow>
  (\<exists> s2 s3 s4. (s1, s2) \<in> oldclean \<and> (s2, s3) \<in> dirty \<and> (s3, s4) \<in> gadget \<and> (s4, s5) \<in> newclean))"

locale time_protection_system =
  ab: unwinding_system A s0 "\<lambda>_. current_domain" external_uwr policy out Sched +
  tp?: time_protection_hardware_uwr
    "TYPE('fch \<times> 'fch_cachedness \<times> 'pch \<times> 'pch_cachedness \<times> 'domain \<times> 'colour)" +
  ts?: trace_selector
    "TYPE(('other_state \<times> ('fch,'pch) state) \<times> 'domain \<times> trace \<times> vpaddr set)"
    "current_domain \<circ> fst"
    tp.uwr Sched "[]"
    "step_is_uwr_determined \<circ> fst"
    "step_is_publicly_determined \<circ> fst"
  for A :: "('other_state,'other_state,unit) data_type"
  and s0 :: "'other_state"
  
  and policy :: "('domain \<times> 'domain) set"
  and out :: "'domain \<Rightarrow> 'other_state \<Rightarrow> 'p"
  
  and step_is_publicly_determined :: "'other_state \<Rightarrow> bool"
  and step_is_uwr_determined :: "'other_state \<Rightarrow> bool"
  
+

  fixes touched_addrs :: "'other_state \<Rightarrow> vpaddr set"

  fixes all_paddrs_of :: "'domain \<Rightarrow> paddr set"
  defines "all_paddrs_of d \<equiv> {a. addr_domain a = d}"

  \<comment> \<open> TA inv stuff\<close>
  (* the invariant that touched_addresses is always sensible for its current domain *)
  fixes touched_addrs_inv :: "'other_state \<Rightarrow> bool"
  defines "touched_addrs_inv s \<equiv>
       snd ` touched_addrs s \<subseteq> all_paddrs_of (current_domain s) \<union> kernel_shared_precise"

  fixes touched_addrs_dirty_inv :: "'domain \<Rightarrow> 'domain \<Rightarrow> 'other_state \<Rightarrow> bool"
  defines "touched_addrs_dirty_inv u u' s \<equiv>
       touched_addrs s \<subseteq> {(v, p) | v p. p \<in> (all_paddrs_of u \<union> all_paddrs_of u' \<union> kernel_shared_precise)}"

  \<comment> \<open>external uwr stuff\<close>  
  (* We expect this to be true for, say, seL4's KSched \<rightarrow> KExit step. -robs. *)
  fixes will_domain_switch :: "'other_state \<Rightarrow> bool"
  assumes will_domain_switch_public:
    "(os, ot) \<in> external_uwr d \<Longrightarrow> will_domain_switch ot = will_domain_switch os"

  \<comment> \<open>domain scheduling stuff\<close>
  assumes next_latest_domainswitch_start_in_future:
    "\<And> t. t < next_latest_domainswitch_start t"
  assumes next_latest_domainswitch_start_flatsteps:
    "\<And> t t'. t' \<ge> t \<Longrightarrow>
       t' < next_latest_domainswitch_start t \<Longrightarrow>
       next_latest_domainswitch_start t' = next_latest_domainswitch_start t"
  fixes domainswitch_start_delay_WCT :: "time"
  fixes dirty_step_WCET :: "time"

  fixes initial_pch :: "'pch"
  fixes get_next_domain :: "'other_state \<Rightarrow> 'domain"
  assumes get_next_domain_public:
    "(s, t) \<in> external_uwr Sched \<Longrightarrow>
     get_next_domain t = get_next_domain s"

  assumes reachable_touched_addrs_inv:
    "ab.reachable s \<Longrightarrow> touched_addrs_inv s"

  assumes simple_steps:
    "(s, s') \<in> ab.Step () \<Longrightarrow>
      (\<not>will_domain_switch s \<and> current_domain s' = current_domain s \<and> step_is_uwr_determined s)
    \<or> (will_domain_switch s \<and> current_domain s' = get_next_domain s)"


  (* note: these ask for 'other_state instead of 'other_state because of the inner/outer
    state thing in the noninterference framework *)
  fixes ds_substep_oldclean :: "('other_state \<times> 'other_state) set"
  fixes ds_substep_dirty :: "('other_state \<times> 'other_state) set"
  fixes ds_substep_gadget :: "('other_state \<times> 'other_state) set"
  fixes ds_substep_newclean :: "('other_state \<times> 'other_state) set"

  (* step_is_uwr_determimed tells us that touched_addrs will be determined.
    the steps that we need this for are non-ds big steps, oldclean and newclean *)
  assumes external_uwr_same_touched_addrs:
    "(s, t) \<in> external_uwr d \<Longrightarrow>
    current_domain s = d \<Longrightarrow>
    step_is_uwr_determined s \<Longrightarrow>
    (step = ab.Step () \<and> \<not>will_domain_switch s)
    \<or> step = ds_substep_oldclean \<or> step = ds_substep_newclean \<Longrightarrow>
    (s, s') \<in> step \<Longrightarrow>
    (t, t') \<in> step \<Longrightarrow>
    touched_addrs t' = touched_addrs s'"


  (* we only need the dirty step to be publicly determined *)
  assumes external_uwr_public_same_touched_addrs:
    "(s, t) \<in> external_uwr Sched \<Longrightarrow>
    step_is_publicly_determined s \<Longrightarrow>
    (s, s') \<in> ds_substep_dirty \<Longrightarrow>
    (t, t') \<in> ds_substep_dirty \<Longrightarrow>
    touched_addrs t' = touched_addrs s'"

  assumes fourways: "can_split_four_ways
    will_domain_switch
    (ab.Step ())
    ds_substep_oldclean
    ds_substep_dirty
    ds_substep_gadget
    ds_substep_newclean"

  (* marking that a step only performs the time protection gadget *)
  fixes step_is_only_timeprotection_gadget :: "'other_state \<Rightarrow> 'other_state \<Rightarrow> bool"

  (*
    RELATED QUESTION:
      let's take a look at "ab.Step ()" and see what kind of step it's taking.
      This needs to be steps of the right size that are appropriate for us.

    PROBLEM:
      we need to know that the TA set is the same at certain intermediary
      points within a domainswitch transition.

    CONTEXT:
      we have predicates step_is_uwr_determined etc that the interpreter defines.
      the external uwr is definitely defined at the initial state before domainswitch,
      but the interpreter might not have uwr info part-way through.

    SOLUTION ONE:
      we have substeps A \<rightarrow> a' \<rightarrow> a'' \<rightarrow> B.
      we ask for UWR at point A to define that the transition from a' to a'' will produce
      the same TA set. This makes the interface simpler (not assuming any uwr knowledge for
      midpoints) but could make the interpreter's proofs more difficult as uwr isn't asked
      for at the natural place.

    SOLUTION TWO:
      we have substeps A \<rightarrow> a' \<rightarrow> a'' \<rightarrow> B.
      we ask for UWR at point a' to define that the transition from a' to a'' will produce
      the same TA set. This makes the assumptions requested by the locale a little more
      verbose, and also requires the interpreter to provide the fact that their uwr is
      maintained by each of the substeps. However, this represents a more natural application
      of the uwr and the `step_is_uwr_determined` etc predicates.
  *)

  (* should we also ask that touched_addrs is clean after the gadget? that might not be
    strictly true though. *)

  assumes fourways_properties:
    "\<lbrakk>(s1, s5) \<in> ab.Step ();
    ab.reachable s1;
    will_domain_switch s1;
    (s1, s2) \<in> ds_substep_oldclean;
    (s2, s3) \<in> ds_substep_dirty;
    (s3, s4) \<in> ds_substep_gadget;
    (s4, s5) \<in> ds_substep_newclean\<rbrakk> \<Longrightarrow>
      step_is_uwr_determined s1
    \<and> touched_addrs_inv s2
    \<and> step_is_publicly_determined s2
    \<and> touched_addrs_dirty_inv (current_domain s) (get_next_domain s) s3
    \<and> step_is_only_timeprotection_gadget s3 s4
    \<and> step_is_uwr_determined s4"

begin

definition
  time_bounded_traces :: "('fch,'pch) state \<Rightarrow> trace set" where
 "time_bounded_traces s \<equiv> {p. tm (trace_multistep p s) < nlds (tm s)}"

definition select_user_trace :: "('other_state \<times> ('fch,'pch) state) \<Rightarrow> vpaddr set \<Rightarrow> trace" where
  "select_user_trace os_s ta \<equiv>
    select_trace (\<lambda>(os, s) ta. traces_obeying_set ta \<inter> time_bounded_traces s) os_s ta"

definition select_public_trace :: "('other_state \<times> ('fch,'pch) state) \<Rightarrow> time \<Rightarrow> vpaddr set \<Rightarrow> trace" where
  "select_public_trace os_s wcet ta \<equiv> 
    select_trace (\<lambda>(os, s) ta. traces_obeying_set ta \<inter> WCET_bounded_traces wcet s) os_s ta"

definition pad_time :: "time \<Rightarrow> time" where
  "pad_time t \<equiv> t + dirty_step_WCET + fch_flush_WCET + pch_flush_WCET kernel_shared_precise"

definition
  gadget_trace where
  "gadget_trace t = [IFlushL1, IFlushL2 kernel_shared_precise, IPadToTime (pad_time t)]"

definition maStep :: "unit \<Rightarrow>
  (('other_state\<times>('fch, 'pch)state) \<times> ('other_state\<times>('fch, 'pch)state)) set"
  where
  "maStep _ \<equiv> {((os, s), (os', s')) | os os' s s' osa osb osc sa sb sc p p_oldclean p_dirty p_gadget p_newclean.
              (os, os') \<in> ab.Step () \<and>
               ((\<not>will_domain_switch os
                 \<and> p = select_user_trace (os, s) (touched_addrs os')
                 \<and> s' = trace_multistep p s )
               \<or> (will_domain_switch os
                 \<comment> \<open>we have intermediate external states\<close>
                 \<and> (os, osa) \<in> ds_substep_oldclean
                 \<and> (osa, osb) \<in> ds_substep_dirty
                 \<and> (osb, osc) \<in> ds_substep_gadget
                 \<comment> \<open>we select traces for each substep\<close>
                 \<and> p_oldclean = select_user_trace (os, s) (touched_addrs osa)
                 \<and> p_dirty = select_public_trace (osa, sa) dirty_step_WCET (touched_addrs osb)
                 \<and> p_gadget = gadget_trace (nlds (tm s))
                 \<and> p_newclean = select_user_trace (osc, sc) (touched_addrs os')
                 \<comment> \<open>we figure out microarch states for the intermediate states\<close>
                 \<and> sa = trace_multistep p_oldclean s
                 \<and> sb = trace_multistep p_dirty sa
                 \<and> sc = trace_multistep p_gadget sb
                 \<and> s' = trace_multistep p_newclean sc )
              )}"

definition maA :: "(('other_state\<times>('fch, 'pch)state), ('other_state\<times>('fch, 'pch)state), unit) data_type" where
  "maA \<equiv> \<lparr> Init = \<lambda>s. {s}, Fin = id, Step = maStep \<rparr>"

(* instead of A_extended_state *)
definition mas0 :: "'other_state\<times>('fch, 'pch)state" where
  "mas0 \<equiv> (s0, \<lparr> fch=empty_fch, pch=initial_pch, tm=0 \<rparr>)"

interpretation ma?:Init_inv_Fin_system maA mas0
  apply unfold_locales
    (* Init_Fin_system.Fin_Init_s0 *)
    apply(force simp:maA_def mas0_def)
   (* Init_Fin_system.Init_inv_Fin *)
   apply(force simp:maA_def)
  (* Init_Fin_system.Fin_inj *)
  apply(force simp:maA_def)
  done

lemma ma_to_ab_step:
  "((os, s), (os', s')) \<in> ma.Step () \<Longrightarrow>
   (os, os') \<in> ab.Step ()"
  apply (clarsimp simp: ma.Step_def execution_def maA_def system.Step_def steps_def maStep_def)
  done

lemma ma_to_ab_run:
  "((os, s), (os', s')) \<in> Run ma.Step as \<Longrightarrow>
   (os, os') \<in> Run ab.Step as"
  apply(induct as arbitrary:s os, solves \<open>simp\<close>)
  apply clarsimp
  apply(erule_tac x=ba in meta_allE)
  apply(erule_tac x=aa in meta_allE)
  apply (drule ma_to_ab_step)
  apply clarsimp
  by blast

lemma ma_to_ab_reachable:
  "ma.reachable (os, s) \<Longrightarrow> ab.reachable os"
  apply(rule ab.Run_reachable)
  apply(drule ma.reachable_Run, clarsimp)
  apply(rule_tac x=as in exI)
  apply (clarsimp simp:mas0_def)
  using ma_to_ab_run apply blast
  done

lemma ma_to_ab_reachable':
  "ma.reachable s \<Longrightarrow> ab.reachable (fst s)"
  apply (cases s, clarsimp simp:ma_to_ab_reachable)
  done

lemma ma_single_step_enabled:
  "ab.reachable os \<Longrightarrow>
   \<exists>s' os'. ((os, s), os', s') \<in> {(s, s'). s' \<in> steps maStep {s} [()]} \<and> ab.reachable os'"
  apply (clarsimp simp: steps_def maStep_def)
  apply (frule ab.enabled_Step, clarsimp)
  apply (frule ab.reachable_Step, simp)
  apply (metis (mono_tags, opaque_lifting) can_split_four_ways_def fourways)
  done

lemma ma_execution_enabledness:
  "ab.reachable os \<Longrightarrow>
   ma.reachable (os, s) \<Longrightarrow>
   \<exists>s' os'. (os', s') \<in> execution maA (os, s) js"
  apply (subst ma.execution_Run [OF _], simp)
  apply (thin_tac "ma.reachable _")
  apply (induct js arbitrary:os s)
   apply (clarsimp simp: execution_def steps_def maA_def)
  apply clarsimp
  apply (clarsimp simp:ma.Step_def execution_def maA_def maStep_def system.Step_def)
  apply (simp only:maA_def [symmetric])
  using ma_single_step_enabled apply (meson relcomp.relcompI)
  done

(* note: we're given an 'out' in time_protection_system, and here we just adjust it to look at
   the other_state part of the new ma state *)
interpretation ma: unwinding_system maA mas0 "\<lambda>_ s. current_domain (fst s)" uwr policy "\<lambda>d s. out d (fst s)" Sched
  apply unfold_locales
      (* enabled_system.enabled *)
      apply(simp only:system.reachable_def[symmetric])
      apply (frule ma_to_ab_reachable')
      apply (simp only:ab.reachable_def)
      apply (frule_tac js=js in ab.enabled)
      apply (frule ma_to_ab_reachable')
      using ma_execution_enabledness apply fastforce 
     (* noninterference_policy.uwr_equiv_rel *)
     using uwr_equiv_rel apply blast
    (* noninterference_policy.schedIncludesCurrentDom *)
    using external_uwr_same_domain uwr_external_uwr apply fastforce
   (* noninterference_policy.schedFlowsToAll *)
   using ab.schedFlowsToAll apply blast
  (* noninterference_policy.schedNotGlobalChannel *)
  using ab.schedNotGlobalChannel apply blast
  done



abbreviation
  trace_units_obeying_ta :: "'other_state \<Rightarrow> trace_unit set" where
 "trace_units_obeying_ta os \<equiv> trace_units_obeying_set (touched_addrs os)"

abbreviation
  traces_obeying_ta :: "'other_state \<Rightarrow> trace set" where
 "traces_obeying_ta os \<equiv> traces_obeying_set (touched_addrs os)"

lemma hd_time_bounded_traces:
  "h # r \<in> time_bounded_traces s \<Longrightarrow>
  tm (trace_step h s) < nlds (tm s) \<and> r \<in> time_bounded_traces (trace_step h s)"
  apply (intro conjI)
   apply (clarsimp simp:time_bounded_traces_def)
   apply (meson order_le_less_trans trace_multistep_time_forward)
  apply (smt (verit, ccfv_threshold) mem_Collect_eq next_latest_domainswitch_start_flatsteps
    order_le_less_trans time_bounded_traces_def trace_multistep.simps(2) trace_multistep_time_forward
    trace_step_time_forward)
  done

lemma in_touched_addrs_expand:
  "a \<in> touched_addrs os \<Longrightarrow>
  touched_addrs_inv os \<Longrightarrow>
  snd a \<in> all_paddrs_of (current_domain os) \<or> snd a \<in> kernel_shared_precise"
  apply (clarsimp simp:touched_addrs_inv_def)
  apply blast
  done

lemma d_running_step:
  assumes
    "i \<in> trace_units_obeying_ta os'"
    "touched_addrs_inv os'"
    "((os, s), (ot, t)) \<in> uwr d"
    "(os', ot') \<in> external_uwr d"
    "current_domain os = d"
    "s' = trace_step i s"
    "t' = trace_step i t"
    (* the only thing we care about output other_state is that the domain hasn't changed *)
    "current_domain os' = current_domain os"
    "current_domain ot' = current_domain ot"
  shows
    "((os', s'), (ot', t')) \<in> uwr d"
  proof (cases i)
    case (IRead a)
    thus ?thesis using assms
      apply (clarsimp simp: uwr_def uwr_running_def trace_units_obeying_set_def)
      apply (thin_tac "s' = _", thin_tac "t' = _")
      apply (intro conjI)
       (* pch *)
       apply (clarsimp simp: pch_same_for_domain_and_shared_def)
       apply (rule and_or_specific')
       apply (case_tac "snd a coll aa")
        (* colliding addresses *)
        apply (rule pch_collision_read [where pchs="pch s" and pcht="pch t" and a="snd a"]; clarsimp)
        apply (metis collision_in_full_collision_set collision_sym diff_domain_no_collision kernel_shared_expanded_full_collision_set)
       (* non-colliding addresses *)
       apply (metis pch_partitioned_read)
      (* time *)
      apply (metis (mono_tags, lifting) all_paddrs_of_def collision_set_contains_itself in_touched_addrs_expand kernel_shared_expanded_def mem_Collect_eq pch_same_for_domain_and_shared_def)
      done
  next
    case (IWrite a)
    thus ?thesis using assms
      apply (clarsimp simp: uwr_def uwr_running_def trace_units_obeying_set_def)
      apply (thin_tac "s' = _", thin_tac "t' = _")
      apply (intro conjI)
       (* pch *)
       apply (clarsimp simp: pch_same_for_domain_and_shared_def)
       apply (rule and_or_specific')
       apply (case_tac "snd a coll aa")
        (* colliding addresses *)
        apply (rule pch_collision_write [where pchs="pch s" and pcht="pch t" and a="snd a"]; clarsimp)
        apply (metis collision_in_full_collision_set collision_sym diff_domain_no_collision kernel_shared_expanded_full_collision_set)        
       (* non-colliding addresses *)
       apply (metis pch_partitioned_write)
      (* time *)
      apply (metis (mono_tags, lifting) all_paddrs_of_def collision_set_contains_itself in_touched_addrs_expand kernel_shared_expanded_def mem_Collect_eq pch_same_for_domain_and_shared_def)
      done
  next
    case IFlushL1
    thus ?thesis using assms by (force simp:uwr_def uwr_running_def)
  next
    case (IFlushL2 fa)
    then show ?thesis using assms
      apply (clarsimp simp: uwr_def uwr_running_def pch_same_for_domain_and_shared_def
                            trace_units_obeying_set_def)
      apply (thin_tac "s' = _", thin_tac "t' = _") (* messy and not needed *)
      apply (prop_tac "\<forall>a1. (\<exists>a2\<in>fa. a1 coll a2) \<longrightarrow> pch_lookup (pch s) a1 = pch_lookup (pch t) a1")
       apply (smt all_paddrs_of_def collision_sym diff_domain_no_collision in_sub_union kernel_shared_expanded_def mem_Collect_eq touched_addrs_inv_def)
      apply (intro conjI)
       apply clarsimp
       apply (rule and_or_specific')
       apply (rule_tac a=a and as=fa in collides_with_set_or_doesnt)
        (* a has no collision with fa *)
        apply (frule pch_partitioned_flush [where p = "pch s"])
        apply (frule pch_partitioned_flush [where p = "pch t"])
        apply (clarsimp, blast)
       (* a collides with fa *)       
       apply (erule pch_collision_flush)
      (* pch flush cycles depend only on equiv state *)
      apply (erule pch_flush_cycles_localised)
      done
  next
    case (IPadToTime x7)
    thus ?thesis using assms by (force simp:uwr_def uwr_running_def)
  qed

(* d running \<rightarrow> d running *)
lemma d_running: "\<lbrakk>
   p \<in> traces_obeying_ta os';
   touched_addrs_inv os';
   \<comment> \<open>initial states s and t hold uwr\<close>
   ((os, s), (ot, t)) \<in> uwr d;
   \<comment> \<open>external states hold external uwr\<close>
   (os', ot') \<in> external_uwr Sched;
   (os', ot') \<in> external_uwr d;
   \<comment> \<open>NB: external_uwr should give us current_domain' t = d\<close>
   current_domain os = d;
   \<comment> \<open>we execute the program on both states\<close>
   s' = trace_multistep p s;
   t' = trace_multistep p t;
   \<comment> \<open>the external state's domain hasn't changed\<close>
   current_domain os' = current_domain os
   \<rbrakk> \<Longrightarrow>
   \<comment> \<open>new states s' and t' hold uwr\<close>
   ((os', s'), (ot', t')) \<in> uwr d"
  apply (frule external_uwr_same_domain)
  apply(induct p arbitrary:s t os ot)
   apply (solves \<open>clarsimp simp:uwr_def\<close>)
  apply clarsimp
  apply(erule_tac x="trace_step a s" in meta_allE)
  apply(erule_tac x="trace_step a t" in meta_allE)
  apply(erule_tac x="os'" in meta_allE)
  apply(erule_tac x="ot'" in meta_allE)
  apply(erule meta_impE)
   apply blast
  apply(erule meta_impE)
   apply (frule hd_trace_obeying_set, clarsimp)
   apply (erule(3) d_running_step; simp)
   apply (simp add:uwr_def)
  apply simp
  done

\<comment> \<open>we prove this via an integrity step\<close>
lemma d_not_running_step:
  assumes
  "i \<in> trace_units_obeying_ta os'"
  "touched_addrs_inv os'"
  "current_domain os \<noteq> d"
  "s' = trace_step i s"
  "current_domain os' = current_domain os"
  shows
  "((os, s), (os, s'\<lparr>tm:=tm s\<rparr>)) \<in> uwr d"
  proof (cases i)
    case (IRead a)
    then show ?thesis using assms
      apply (clarsimp simp: uwr_def uwr_notrunning_def trace_units_obeying_set_def)
      apply (thin_tac "s' = _")
      apply (clarsimp simp:pch_same_for_domain_except_shared_def)
      apply (rule pch_partitioned_read)
      apply (clarsimp simp: touched_addrs_inv_def)
      apply (drule(1) in_image_union)
      apply (erule disjE)
       apply (clarsimp simp: all_paddrs_of_def)
       apply (metis collision_sym diff_domain_no_collision)
      using kernel_shared_expanded_def apply blast
      done
  next
    case (IWrite x2)
    then show ?thesis using assms
      apply (clarsimp simp: uwr_def uwr_notrunning_def trace_units_obeying_set_def)
      apply (thin_tac "s' = _")
      apply (clarsimp simp:pch_same_for_domain_except_shared_def)
      apply (rule pch_partitioned_write)
      apply (clarsimp simp: touched_addrs_inv_def)
      apply (drule(1) in_image_union)
      apply (erule disjE)
       apply (clarsimp simp: all_paddrs_of_def)
       apply (metis collision_sym diff_domain_no_collision)
      using kernel_shared_expanded_def apply blast
      done
  next
    case IFlushL1
    then show ?thesis using assms
      by (clarsimp simp: uwr_def uwr_notrunning_def pch_same_for_domain_except_shared_def)
  next
    case (IFlushL2 x5)
    then show ?thesis using assms
      apply (clarsimp simp: uwr_def uwr_notrunning_def pch_same_for_domain_except_shared_def
                            trace_units_obeying_set_def)
      apply (rule sym, rule pch_partitioned_flush, clarsimp)
      apply(clarsimp simp:touched_addrs_inv_def all_paddrs_of_def)
      (* Adapted from Isar proof found by Sledgehammer -robs. *)
      apply(prop_tac "addr_domain a' = d")
       using diff_domain_no_collision
       apply blast
      apply(prop_tac "a \<in> kernel_shared_precise")
       apply(force simp:kernel_shared_precise_def)
      using collision_set_contains_itself kernel_shared_expanded_def
      apply blast
      done
  next
    case (IPadToTime x7)
    then show ?thesis using assms
      by (clarsimp simp: uwr_def uwr_notrunning_def pch_same_for_domain_except_shared_def)
qed

lemma d_not_running_integrity_uwr:
  "\<lbrakk>p \<in> traces_obeying_ta os';
  p \<in> time_bounded_traces s;
  touched_addrs_inv os';
  current_domain os \<noteq> d;
  current_domain os' = current_domain os
  \<rbrakk> \<Longrightarrow>
  ((os, s), (os, trace_multistep p s)) \<in> uwr d"
  apply (induct p arbitrary: s; clarsimp)
  apply (drule hd_trace_obeying_set, clarsimp)
  apply (drule_tac s'="trace_step a s" in d_not_running_step, simp+)
  apply (drule hd_time_bounded_traces, clarsimp)
  apply (drule_tac x="trace_step a s" in meta_spec, clarsimp)
  apply (subgoal_tac "((os, s), os, trace_step a s) \<in> uwr d")
   using uwr_trans apply blast
  apply (thin_tac "((os, trace_step a s), os,
         trace_multistep p (trace_step a s))
        \<in> uwr d")
  apply (clarsimp simp:uwr_def uwr_notrunning_def)
  apply (subst eq_sym_conv)
  apply (rule next_latest_domainswitch_start_flatsteps)
   apply (rule trace_step_time_forward)
  apply clarsimp
  done

(* d not running \<rightarrow> d not running *)
lemma d_not_running: "\<lbrakk>
   \<comment> \<open>we have two programs derived from touched_addresses - may not be the same touched_addresses\<close>
   ps \<in> traces_obeying_ta os';
   pt \<in> traces_obeying_ta ot';
   ps \<in> time_bounded_traces s;
   pt \<in> time_bounded_traces t;
   \<comment> \<open>these touched_addresses does NOT contain any addresses from d\<close>
   current_domain os \<noteq> d;
   current_domain os' = current_domain os;
   touched_addrs_inv os';
   touched_addrs_inv ot';
   \<comment> \<open>initial states s and t hold uwr\<close>
   ((os, s), (ot, t)) \<in> uwr d;
   (os', ot') \<in> external_uwr Sched;
   (os', ot') \<in> external_uwr d;
   \<comment> \<open>we execute both programs\<close>
   s' = trace_multistep ps s;
   t' = trace_multistep pt t
   \<rbrakk> \<Longrightarrow>
   \<comment> \<open>new state s' and t' hold uwr_notrunning\<close>
   ((os', s'), (ot', t')) \<in> uwr d"
  apply (frule external_uwr_same_domain)
  apply (drule(4) d_not_running_integrity_uwr [where s=s and os=os])
  apply (drule(2) d_not_running_integrity_uwr [where s=t and os=ot and d=d])
    using uwr_def apply fastforce
   using uwr_def apply force
  apply (prop_tac "((os, trace_multistep ps s), ot, trace_multistep pt t) \<in> uwr d")
   apply (rule uwr_trans, rule uwr_sym', assumption)
   apply (rule uwr_trans, assumption, assumption)
  apply (simp add:uwr_def)
  done


(*
 a 'dirty step' touching addresses from both U and U'.
 we know that U is the current domain.
 (U' is the "next" domain)

 we show uwr preservation according to D.

 There are a number of cases to consider:
 - D = U. Therefore, D is the current domain.     [dirty_step_from_d]
 - D \<noteq> U, but D = U' (d is not current_domain)    [dirty_step_to_d]
 - D \<noteq> U and D \<noteq> U' (d is not current_domain)     [dirty_step_unrelated]

*)

lemma dirty_step_from_d:
  assumes
    "i \<in> trace_units_obeying_set {(va, pa) | va pa. pa \<in> (all_paddrs_of u \<union> all_paddrs_of u' \<union> kernel_shared_precise)}"
    "d = u"
    "((os, s), (ot, t\<lparr>tm:=tm s\<rparr>)) \<in> uwr d"
    "s' = trace_step i s"
    "t' = trace_step i t"
    "current_domain os = u"
  shows
    "((os, s'), (ot, t'\<lparr>tm:=tm s'\<rparr>)) \<in> uwr d"
  proof (cases i)
  case (IRead a)
  then show ?thesis using assms
    apply (clarsimp simp: uwr_def uwr_running_def)
    apply (thin_tac "s' = _", thin_tac "t' = _")
    apply (clarsimp simp: pch_same_for_domain_and_shared_def)
    apply (smt collision_in_full_collision_set diff_domain_no_collision full_collision_set_def kernel_shared_expanded_full_collision_set pch_collision_read pch_partitioned_read)
    done
next
  case (IWrite a)
  then show ?thesis using assms
    apply (clarsimp simp: uwr_def uwr_running_def)
    apply (thin_tac "s' = _", thin_tac "t' = _")
    apply (clarsimp simp: pch_same_for_domain_and_shared_def)
    apply (smt collision_in_full_collision_set diff_domain_no_collision full_collision_set_def kernel_shared_expanded_full_collision_set pch_collision_write pch_partitioned_write)
    done
next
  case IFlushL1
  then show ?thesis using assms
    by (clarsimp simp: uwr_def uwr_running_def)
next
  case (IFlushL2 pas)
  then show ?thesis using assms
    apply (clarsimp simp: uwr_def uwr_running_def)
    apply (clarsimp simp: pch_same_for_domain_and_shared_def)
    (* for now let's only consider the cases where this program might
       flush L2 within kernel_shared_expanded. We can probably prove this without that
       restriction, but would probably need to change some locale assumptions for that. *)
    apply (prop_tac "pas = kernel_shared_precise")
     subgoal sorry
    apply (metis pch_collision_flush pch_partitioned_flush)
    done
next
  case (IPadToTime x5)
  then show ?thesis using assms
  apply (clarsimp simp: uwr_def uwr_running_def)
  done
qed

lemma dirty_step_to_d:
  assumes
    "i \<in> trace_units_obeying_set {(va, pa) | va pa. pa \<in> (all_paddrs_of u \<union> all_paddrs_of u' \<union> kernel_shared_precise)}"
    "d = u' \<and> d \<noteq> u"
    "((os, s), (ot, t\<lparr>tm:=tm s\<rparr>)) \<in> uwr d"
    "s' = trace_step i s"
    "t' = trace_step i t"
    "current_domain os = u"
  shows
    "((os, s'), (ot, t'\<lparr>tm:=tm s'\<rparr>)) \<in> uwr d"
  proof (cases i)
  case (IRead a)
  then show ?thesis using assms
    apply (clarsimp simp: uwr_def uwr_notrunning_def)
    apply (thin_tac "s' = _", thin_tac "t' = _")
    apply (clarsimp simp: pch_same_for_domain_except_shared_def)
    apply (smt collision_in_full_collision_set diff_domain_no_collision full_collision_set_def kernel_shared_expanded_full_collision_set pch_collision_read pch_partitioned_read)
    done
next
  case (IWrite a)
  then show ?thesis using assms
    apply (clarsimp simp: uwr_def uwr_notrunning_def)
    apply (thin_tac "s' = _", thin_tac "t' = _")
    apply (clarsimp simp: pch_same_for_domain_except_shared_def)
    apply (smt collision_in_full_collision_set diff_domain_no_collision full_collision_set_def kernel_shared_expanded_full_collision_set pch_collision_write pch_partitioned_write)
    done
next
  case IFlushL1
  then show ?thesis using assms
    by (clarsimp simp: uwr_def uwr_notrunning_def)
next
  case (IFlushL2 pas)
  then show ?thesis using assms
    apply (clarsimp simp: uwr_def uwr_notrunning_def)
    apply (clarsimp simp: pch_same_for_domain_except_shared_def)
    (* for now let's only consider the cases where this program might
       flush L2 within kernel_shared_expanded. We can probably prove this without that
       restriction, but would probably need to change some locale assumptions for that. *)
    apply (prop_tac "pas \<subseteq> kernel_shared_expanded")
     subgoal sorry
    apply (smt collision_in_full_collision_set in_mono kernel_shared_expanded_full_collision_set pch_collision_flush pch_partitioned_flush)
    done
next
  case (IPadToTime x5)
  then show ?thesis using assms
  apply (clarsimp simp: uwr_def uwr_notrunning_def)
  done
qed

lemma dirty_step_unrelated:
  assumes
    "i \<in> trace_units_obeying_set {(va, pa) | va pa. pa \<in> (all_paddrs_of u \<union> all_paddrs_of u' \<union> kernel_shared_precise)}"
    "d \<noteq> u \<and> d \<noteq> u'"
    "((os, s), (ot, t\<lparr>tm:=tm s\<rparr>)) \<in> uwr d"
    "s' = trace_step i s"
    "t' = trace_step i t"
    "current_domain os = u"
  shows
    "((os, s'), (ot, t'\<lparr>tm:=tm s'\<rparr>)) \<in> uwr d"
  proof (cases i)
  case (IRead a)
  then show ?thesis using assms
    apply (clarsimp simp: uwr_def uwr_notrunning_def)
    apply (thin_tac "s' = _", thin_tac "t' = _")
    apply (clarsimp simp: pch_same_for_domain_except_shared_def)
    apply (smt collision_in_full_collision_set diff_domain_no_collision full_collision_set_def kernel_shared_expanded_full_collision_set pch_collision_read pch_partitioned_read)
    done
next
  case (IWrite a)
  then show ?thesis using assms
    apply (clarsimp simp: uwr_def uwr_notrunning_def)
    apply (thin_tac "s' = _", thin_tac "t' = _")
    apply (clarsimp simp: pch_same_for_domain_except_shared_def)
    apply (smt collision_in_full_collision_set diff_domain_no_collision full_collision_set_def kernel_shared_expanded_full_collision_set pch_collision_write pch_partitioned_write)
    done
next
  case IFlushL1
  then show ?thesis using assms
    by (clarsimp simp: uwr_def uwr_notrunning_def)
next
  case (IFlushL2 pas)
  then show ?thesis using assms
    apply (clarsimp simp: uwr_def uwr_notrunning_def)
    apply (clarsimp simp: pch_same_for_domain_except_shared_def)
    (* for now let's only consider the cases where this program might
       flush L2 within kernel_shared_expanded. We can probably prove this without that
       restriction, but would probably need to change some locale assumptions for that. *)
    apply (prop_tac "pas \<subseteq> kernel_shared_expanded")
     subgoal sorry
    apply (smt collision_in_full_collision_set in_mono kernel_shared_expanded_full_collision_set pch_collision_flush pch_partitioned_flush)
    done
next
  case (IPadToTime x5)
  then show ?thesis using assms
  apply (clarsimp simp: uwr_def uwr_notrunning_def)
  done
qed

lemma dirty_multistep_aux: "\<lbrakk>
   p \<in> traces_obeying_set {(va, pa) | va pa.
           pa \<in> (all_paddrs_of u \<union> all_paddrs_of u' \<union> kernel_shared_precise)};
   current_domain os = u;
   d = u \<or> (d = u' \<and> d \<noteq> u) \<or> (d \<noteq> u \<and> d \<noteq> u');
   \<comment> \<open>initial states s and t hold uwr (apart from time)\<close>
   ((os, s), (ot, t\<lparr>tm:=tm s\<rparr>)) \<in> uwr d;
   \<comment> \<open>we execute both programs\<close>
   s' = trace_multistep p s;
   t' = trace_multistep p t
   \<rbrakk> \<Longrightarrow>
   \<comment> \<open>new state s' and t' hold uwr_notrunning\<close>
   ((os, s'), (ot, t'\<lparr>tm:=tm s'\<rparr>)) \<in> uwr d"
  apply(induct p arbitrary:s t os ot)
   apply (solves \<open>clarsimp simp:uwr_def uwr_running_def\<close>)
  apply clarsimp
  apply (drule hd_trace_obeying_set, clarsimp)
  apply(erule_tac x="trace_step a s" in meta_allE)
  apply(erule_tac x="trace_step a t" in meta_allE)
  apply clarsimp
  apply(erule_tac x="os" in meta_allE)
  apply(erule_tac x="ot" in meta_allE)
  apply clarsimp
  apply(erule meta_impE)
   apply (erule disjE)
    apply (rule dirty_step_from_d; simp)
   apply (erule disjE)
    apply (rule dirty_step_to_d; simp)
    apply clarsimp
    apply(rule dirty_step_unrelated; simp)
   apply simp
  apply simp
  done

lemma dirty_multistep: "\<lbrakk>
   p \<in> traces_obeying_set {(va, pa) | va pa.
           pa \<in> (all_paddrs_of u \<union> all_paddrs_of u' \<union> kernel_shared_precise)};
   current_domain os = u;
   d = u \<or> (d = u' \<and> d \<noteq> u) \<or> (d \<noteq> u \<and> d \<noteq> u');
   \<comment> \<open>initial states s and t hold uwr (apart from time)\<close>
   ((os, s), (ot, t)) \<in> uwr d;
   \<comment> \<open>we execute both programs\<close>
   s' = trace_multistep p s;
   t' = trace_multistep p t
   \<rbrakk> \<Longrightarrow>
   \<comment> \<open>new state s' and t' hold uwr_notrunning\<close>
   ((os, s'), (ot, t'\<lparr>tm:=tm s'\<rparr>)) \<in> uwr d"
  apply (erule dirty_multistep_aux; simp?)
  apply (cases "current_domain os = d"; clarsimp simp:uwr_def uwr_running_def uwr_notrunning_def)
  done

lemma dirty_multistep_times: "\<lbrakk>
   p \<in> WCET_bounded_traces_universal dirty_step_WCET;
   \<comment> \<open>initial states s and t hold uwr (apart from time)\<close>
   ((os, s), (ot, t)) \<in> uwr d;
   \<comment> \<open>we execute both programs\<close>
   s' = trace_multistep p s;
   t' = trace_multistep p t
   \<rbrakk> \<Longrightarrow>
   tm s' < nlds (tm s) + dirty_step_WCET \<and> tm t' < nlds (tm s) + dirty_step_WCET"
  apply (prop_tac "nlds (tm t) = nlds (tm s)")
   apply (cases "current_domain os = d"; clarsimp simp: uwr_def uwr_running_def uwr_notrunning_def)
  apply (clarsimp simp: WCET_bounded_traces_def)
  apply (smt (verit, ccfv_threshold) WCET_bounded_traces_universal_def add.commute
    add_mono_thms_linordered_field(2) mem_Collect_eq next_latest_domainswitch_start_in_future
    order_le_less_trans)
  done

lemma in_precise_in_expanded:
  "a \<in> kernel_shared_precise \<Longrightarrow> a \<in> kernel_shared_expanded"
  using collision_set_contains_itself kernel_shared_expanded_def apply blast
  done

lemma pch_after_L2_flush_and:
  "((os, s), ot, t\<lparr>tm := tm s\<rparr>) \<in> uwr d \<Longrightarrow>
  pch_same_for_domain_and_shared d
    (do_pch_flush (pch s) kernel_shared_precise)
    (do_pch_flush (pch t) kernel_shared_precise)"
  apply (clarsimp simp: pch_same_for_domain_and_shared_def)
  apply (clarsimp simp: uwr_def)
  apply (rule and_or_specific')
  apply (cases "current_domain os = d"; clarsimp)
   apply (clarsimp simp: uwr_running_def pch_same_for_domain_and_shared_def)
   apply (smt collision_in_full_collision_set in_precise_in_expanded kernel_shared_expanded_full_collision_set pch_collision_flush pch_partitioned_flush)
   apply (clarsimp simp: uwr_notrunning_def pch_same_for_domain_except_shared_def)
   apply (smt collision_sym kernel_shared_expanded_def mem_Collect_eq pch_collision_flush pch_partitioned_flush)
  done

lemma pch_after_L2_flush_except:
  "((os, s), ot, t\<lparr>tm := tm s\<rparr>) \<in> uwr d \<Longrightarrow>
  pch_same_for_domain_except_shared d
    (do_pch_flush (pch s) kernel_shared_precise)
    (do_pch_flush (pch t) kernel_shared_precise)"
  apply (clarsimp simp: pch_same_for_domain_except_shared_def)
  apply (clarsimp simp: uwr_def)
  apply (cases "current_domain os = d"; clarsimp)
   apply (clarsimp simp: uwr_running_def pch_same_for_domain_and_shared_def)
   apply (smt collision_in_full_collision_set in_precise_in_expanded kernel_shared_expanded_full_collision_set pch_collision_flush pch_partitioned_flush)
   apply (clarsimp simp: uwr_notrunning_def pch_same_for_domain_except_shared_def)
   apply (smt collision_sym kernel_shared_expanded_def mem_Collect_eq pch_collision_flush pch_partitioned_flush)
  done

lemma gadget_multistep: "\<lbrakk>
   \<comment> \<open>initial states s and t hold uwr (apart from time)\<close>
   ((os, s), (ot, t\<lparr>tm:=tm s\<rparr>)) \<in> uwr d;
   p = gadget_trace ndst_a;
   current_domain os = u;
   tm s \<le> ndst_a + dirty_step_WCET;
   tm t \<le> ndst_a + dirty_step_WCET;
   \<comment> \<open>we execute both programs\<close>
   s' = trace_multistep p s;
   t' = trace_multistep p t;
   \<comment> \<open>output states hold external uwr\<close>
   (os', ot') \<in> external_uwr Sched;
   (os', ot') \<in> external_uwr d
   \<rbrakk> \<Longrightarrow>
    ((os', s'), (ot', t')) \<in> uwr d"
  apply (frule external_uwr_same_domain)
  apply (clarsimp simp:gadget_trace_def)
  apply (thin_tac "t' = _", thin_tac "s' = _")
  apply (subst uwr_def, clarsimp)
  apply (intro conjI; clarsimp)
   apply (clarsimp simp: uwr_running_def)
   apply (intro conjI)
    apply (erule pch_after_L2_flush_and)
   apply (simp add: pad_time_def add_mono_thms_linordered_semiring(1) fch_flush_cycles_obeys_WCET
                    max_def pch_flush_cycles_obeys_WCET)
  apply (clarsimp simp: uwr_notrunning_def)
  apply (intro conjI)
   apply (erule pch_after_L2_flush_except)
  apply (simp add: pad_time_def add_mono_thms_linordered_semiring(1) fch_flush_cycles_obeys_WCET
                   max_def pch_flush_cycles_obeys_WCET)
  done

(*meowmeow here ^^*)


(* not currently used? *)
lemma uwr_same_nlds:
  "((os, s), (ot, t)) \<in> uwr d \<Longrightarrow>
   nlds (tm t) = nlds (tm s)"
  apply (case_tac "current_domain os = d")
  apply (clarsimp simp:uwr_def uwr_running_def uwr_notrunning_def)+
  done

lemma empty_in_traces_obeying_ta [simp]:
  "[] \<in> traces_obeying_ta os'"
  by (simp add: traces_obeying_set_def)

lemma empty_in_time_bounded_traces [simp]:
  "[] \<in> time_bounded_traces t"
  by (simp add: next_latest_domainswitch_start_in_future time_bounded_traces_def)

lemma user_trace_from_ta:
  "select_user_trace oss (touched_addrs os') \<in> traces_obeying_ta os'"
  apply (cases oss; clarsimp simp: select_user_trace_def)
  apply (rule ts.trace_from_superset; clarsimp)
  done

lemma user_trace_from_time_bounded:
  "select_user_trace (os, s) ta \<in> time_bounded_traces s"
  apply (clarsimp simp:select_user_trace_def)
  apply (rule ts.trace_from_superset; clarsimp)
  apply (clarsimp simp:traces_obeying_set_def)
  done

lemma ma_confidentiality_u_ta:
  "\<lbrakk>\<not>will_domain_switch os;
  touched_addrs_inv os';
  touched_addrs_inv ot';
  ab.reachable os;
  ma.uwr2 (os, s) u (ot, t);
  ab.uwr2 os' Sched ot';
  ab.uwr2 os' u ot';
  ((os, s), os', s') \<in> maStep ();
  ((ot, t), ot', t') \<in> maStep ()\<rbrakk>
  \<Longrightarrow> ma.uwr2 (os', s') u (ot', t')"
  apply (frule uwr_external_uwr)
  apply (frule will_domain_switch_public [where os=os])
  apply (clarsimp simp:maStep_def)
  apply (thin_tac "s' = _", thin_tac "t' = _")

  (* show that the domain hasn't changed *)
  apply (frule simple_steps [where s=os]; clarsimp)
  apply (frule simple_steps [where s=ot]; clarsimp)

  (* show that the programs obey the TAs *)
  apply (prop_tac "select_user_trace (os, s) (touched_addrs os') \<in> traces_obeying_ta os'
                 \<and> select_user_trace (ot, t) (touched_addrs ot') \<in> traces_obeying_ta ot'")
   apply (intro conjI; rule user_trace_from_ta)
  apply clarsimp

  apply (case_tac "current_domain os = u")
   (* u is executing *)
   apply (prop_tac "touched_addrs ot' = touched_addrs os'")
    subgoal sorry
    apply clarsimp
(*    apply (rule external_uwr_same_touched_addrs [where s=os and t=ot]; simp add:step_or_substep_def)
   apply clarsimp *)
   apply (prop_tac "select_user_trace (ot, t) (touched_addrs os')
                  = select_user_trace (os, s) (touched_addrs os')")
    apply (subst eq_sym_conv)
    apply (clarsimp simp: select_user_trace_def)
    apply (rule ts.select_trace_uwr_determined; simp)
   apply clarsimp

   apply (rule d_running [where os=os and ot=ot and s=s and t=t]; simp)
  
  (* u is not executing *)
  apply (rule d_not_running [where os=os and ot=ot]; simp?)
   apply (rule user_trace_from_time_bounded)+
  done

lemma trace_multistep_fold:
  "trace_multistep pb (trace_multistep pa s) = trace_multistep (pa @ pb) s"
  apply (induct pa arbitrary: pb s; clarsimp)
  done

lemma public_trace_obeys_wcet:
  "tm (trace_multistep (select_public_trace (os, s) wcet ta) s) < nlds (tm s) + wcet"
  apply (prop_tac "select_public_trace (os, s) wcet ta \<in> _")
   apply (clarsimp simp: select_public_trace_def)
   apply (rule ts.trace_from_set)
   apply (simp add: WCET_bounded_traces_def traces_obeying_set_def)
  apply clarsimp
  apply (metis WCET_bounded_traces_def add_le_cancel_left add_mono_thms_linordered_field(3)
    le_iff_add mem_Collect_eq next_latest_domainswitch_start_in_future trace_multistep_time_forward)
  done

lemma traces_obeying_set_subset:
  "S1 \<subseteq> S2 \<Longrightarrow>
  traces_obeying_set S1 \<subseteq> traces_obeying_set S2"
  apply (clarsimp simp:traces_obeying_set_def list_all_def)
  apply (drule_tac x=i in bspec, assumption)
  apply (clarsimp simp:trace_units_obeying_set_def)
  apply (case_tac i; clarsimp)
    apply blast
   apply blast
  apply blast
  done

lemma ta_dirty_inv_applied:
  "touched_addrs_dirty_inv u u' os' \<Longrightarrow>
   select_public_trace (os, s) wcet (touched_addrs os')
   \<in> traces_obeying_set {(va, pa).
       pa \<in> all_paddrs_of u \<or>
       pa \<in> all_paddrs_of u' \<or>
       pa \<in> kernel_shared_precise}"
  apply (smt Collect_cong Int_Collect Un_iff WCET_bounded_traces_def case_prodE case_prod_conv
    dual_order.trans empty_in_traces_obeying_ta inf.cobounded1 le_iff_add select_public_trace_def
    touched_addrs_dirty_inv_def trace_multistep.simps(1) traces_obeying_set_subset
    ts.trace_from_superset)
  done
   
lemma ma_confidentiality_u_ds:
  "\<lbrakk>will_domain_switch os;
  ma.uwr2 (os, s) Sched (ot, t);
  ma.uwr2 (os, s) u (ot, t);
  ab.uwr2 os' Sched ot';
  ab.uwr2 os' u ot';
  ab.reachable os;
  ((os, s), os', s') \<in> maStep ();
  ((ot, t), ot', t') \<in> maStep ()\<rbrakk>
  \<Longrightarrow> ma.uwr2 (os', s') u (ot', t')"
  apply (frule uwr_external_uwr)

  apply (prop_tac "will_domain_switch ot")
   using will_domain_switch_public apply fastforce

  apply (clarsimp simp:maStep_def)
  apply (thin_tac "s' = _", thin_tac "t' = _")
  apply (rename_tac osa osa' osb osb' osc osc')
  (* show that the ending domain has changed (but is the same) *)
  apply (frule simple_steps [where s=os]; clarsimp)
  apply (frule simple_steps [where s=ot]; clarsimp)
  apply (frule get_next_domain_public; clarsimp)

  (* show that the TAs are the same *)  
  apply (prop_tac "touched_addrs osa' = touched_addrs osa")
   apply (rule external_uwr_same_touched_addrs [where d=u])
        apply assumption
       apply simp
   thm external_uwr_same_touched_addrs
   term big_step_ADT_A_if

  apply (prop_tac "touched_addrs osma = touched_addrs osm")
   apply (rule external_uwr_public_same_touched_addrs [where s=os and t=ot])
      apply assumption+

  (* show that the traces are the same *)
  apply (prop_tac "select_public_trace (ot, t) dirty_step_WCET (touched_addrs osm) = 
                   select_public_trace (os, s) dirty_step_WCET (touched_addrs osm)")
   apply (clarsimp simp:select_public_trace_def)
   apply (rule ts.select_trace_public_determined, simp+)
  apply (prop_tac " ((os, _), (ot, _\<lparr>tm:=tm _\<rparr>)) \<in> uwr u")
   apply (rule dirty_multistep [where p="(select_public_trace (ot, t) dirty_step_WCET
           (touched_addrs _))"
          and u="current_domain os" and u'="get_next_domain os"]; (rule refl)?)
  sorry (*
     apply (drule middle_step_holds_dirty_ta; simp)
     apply (rule ta_dirty_inv_applied, simp)
    apply blast
   apply assumption

  apply (drule gadget_multistep [where p="gadget_trace (nlds (tm s))" and os'=os' and ot'=ot'])
          apply (rule refl)
         apply (rule refl)
        apply (metis nat_less_le public_trace_obeys_wcet)
       apply (metis nat_less_le public_trace_obeys_wcet uwr_same_nlds)
      apply (rule refl)
     apply (rule refl)
    apply assumption
   apply assumption
  apply (clarsimp simp: trace_multistep_fold)
  apply (simp add: uwr_same_nlds)
  done *)

theorem ma_confidentiality_u:
  "ab.confidentiality_u \<Longrightarrow> ma.confidentiality_u"
  apply(clarsimp simp:ma.confidentiality_u_def)
  apply (rename_tac u os s ot t os' s' ot' t')

  apply (prop_tac "ab.uwr2 os' u ot'")
   apply (simp only:ab.confidentiality_u_def)
   apply (meson ma_to_ab_reachable ma_to_ab_step uwr_external_uwr)
  
  apply (prop_tac "ab.uwr2 os' Sched ot'")
   apply (simp only:ab.confidentiality_u_def)
   apply (metis ma.schedNotGlobalChannel ma_to_ab_reachable ma_to_ab_step uwr_external_uwr)

  apply (frule_tac s="(os, s)" in ma.reachable_Step, assumption)
  apply (frule_tac s="(ot, t)" in ma.reachable_Step, assumption)

  apply (frule_tac os=os' in ma_to_ab_reachable)
  apply (frule_tac os=ot' in ma_to_ab_reachable)
  apply (frule_tac s=os' in reachable_touched_addrs_inv)
  apply (frule_tac s=ot' in reachable_touched_addrs_inv)
  
  apply (thin_tac "_ \<longrightarrow> _")

  (* let's get this all in terms of maStep *)
  apply (clarsimp simp:ma.Step_def execution_def steps_def maA_def system.Step_def)
  apply (simp only:maA_def [symmetric])

  apply (case_tac "will_domain_switch os")
   defer
  sorry (*
   apply (erule ma_confidentiality_u_ta; simp)

  apply (rule ma_confidentiality_u_ds; simp?)
   apply (rule ma_to_ab_reachable, assumption)
  apply (metis ab.enabled_Step domainswitch_step_splittable fst_conv insert_iff
    ma_to_ab_reachable')
  done *)

theorem extended_Nonleakage:
  "ab.Nonleakage_gen \<Longrightarrow> ma.Nonleakage_gen"
  using ab.Nonleakage_gen_equiv_confidentiality_u ma.Nonleakage_gen
    ma_confidentiality_u apply blast
  done

end
end