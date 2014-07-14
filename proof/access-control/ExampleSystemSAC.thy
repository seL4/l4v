(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory ExampleSystem
imports
  Access
  "../drefine/StateTranslation_D"
  sac_dump_simplified
begin

text {* 

This file tries to define an example system using the access control
definitions. The aim is a sanity check of the AC definitions, in
particular that the function state_objs_to_policy does not connect everything
to everything.


The example system is inspired by the SAC system. 

The aim is to be able to prove 

  pas_refined A S0

where A is the label graph defining the AC policy for the SAC and S0
is the initial state of the SAC after booting.

This shows in particular that the aag extracted from S0 (by
state_objs_to_policy) is included in the policy graph A.

*}




text{* ----- SIMPLIFIED SAC POLICY  ------*}



text {* We first define an example static policy SACPAS with a
simplified SAC system, where the Router (Linux) is running, connected
to one mapped frame of NicB. And we also have one frame in NicA, and
the aim would be to show that it cannot be changed by the Router.
*}

datatype SACLabels = 
    NicA | NicB | NicC | NicD
  | Router
  | RouterManager |  SacController | EndPoint
  | ASID 

text{* FIXME: the ASID is just added to be able to prove the
wellformed predicate, but it is not used yet.
*}

text{* Defining some references. *}

definition
  tcb_router :: word32 where
  "tcb_router = 0x1000"
definition
  cnode_router :: word32 where
  "cnode_router = 0x2000"
definition
  frame_nicA :: word32 where
  "frame_nicA = 0x3000"
definition
  frame_nicB :: word32 where
  "frame_nicB = 0x4000"
definition
  frame_nicC :: word32 where
  "frame_nicC = 0x5000"
definition
  frame_nicD :: word32 where
  "frame_nicD = 0x6000"
definition
  tcb_rm :: word32 where
  "tcb_rm = 0x7000"
definition
  cnode_rm :: word32 where
  "cnode_rm = 0x8000"
definition
  tcb_sacc :: word32 where
  "tcb_sacc = 0x9000"
definition
  cnode_sacc :: word32 where
  "cnode_sacc = 0x10000"
definition
  ep :: word32 where
  "ep = 0x11000"

lemmas sac_id_defs = 
  tcb_router_def cnode_router_def 
   frame_nicA_def frame_nicB_def 
   frame_nicC_def frame_nicD_def
   tcb_rm_def cnode_rm_def 
   tcb_sacc_def cnode_sacc_def 
   ep_def

text {* Mapping the references to the labels *}

definition SACAgentMap :: "SACLabels agent_map" where 
  "SACAgentMap \<equiv> 
      (\<lambda>_. undefined)
      ( tcb_router :=Router  ,
        cnode_router := Router, 
        frame_nicA := NicA ,
        frame_nicB := NicB ,
        frame_nicC := NicC ,
        frame_nicD := NicD  ,
        tcb_rm := RouterManager,  
        cnode_rm := RouterManager,  
        tcb_sacc := SacController , 
        cnode_sacc := SacController,  
        ep := EndPoint) "

text {* Defining the authority between labels. 

Here we have the intuitive authority we want, plus all the needed
authority to have a wellformed graph. So we define
complete_AgentAuthGraph to add these 'extra' authorities (at least all
the ones not depending on the current label). These are:

  . self-authority (each label needs all the authorities to itself).
  . if Control edge is present between 2 labels then we add all
    authorities between them
  . Control authority is transitive: we add an Control edge
    between 2 labels if we can connect them via Control
    edges. Actually we add all authorities because of the second clause.
  
*}


definition complete_AgentAuthGraph :: "'a AgentAuthGraph \<Rightarrow> 'a AgentAuthGraph" where 
  "complete_AgentAuthGraph g \<equiv> 
     g \<union> {(y,a,y) | a y. True} 
       \<union> {(x,a,y) | x a y. (x,Control,y) \<in> g }
       \<union> {(x,a,y)|x a y. \<exists> z. (x,Control,z) \<in> g \<and> (z, Control,y) \<in> g} " 


text {* try to automate the proof of wellformed *}

lemma complete_AgentAuthGraph_is_wellformed:
  " (\<forall>y. (curl, Control, y) \<in> g \<longrightarrow> curl = y) \<Longrightarrow>
    policy_wellformed (complete_AgentAuthGraph g) curl"

(*
  apply (clarsimp simp: policy_wellformed_def complete_AgentAuthGraph_def) 
  apply (intro allI impI conjI) 
   apply (elim exE conjE)
   apply (frule_tac R="curl=z" in allE)
    apply (erule impE, assumption+)
   apply simp
*)

  apply (unfold policy_wellformed_def complete_AgentAuthGraph_def) 
  apply (rule conjI)
   apply clarsimp 
   apply (frule_tac R="curl=z" in allE)
    apply (erule impE, assumption+)
   apply simp
  apply (rule conjI)
   apply clarsimp
  apply (rule conjI)
   apply simp

  apply (intro allI impI conjI)
  apply clarsimp
(*  apply (elim disjE)
   apply clarsimp+*)  (* need to come back to this one *)
sorry


text {* Now the graph for the SAC contains only 2 edges (Router can
read from and write to NicB), plus the self-authorities *}

text {* FIXME: Auth.Read and Auth.Write have been removed because not
used yet. I used them here for the example so I've just replaced a
Read by a Receive and a Write by a Send with a "fixme" comment *}


definition SACAgentAuthGraph_aux ::
"SACLabels AgentAuthGraph" where
  "SACAgentAuthGraph_aux \<equiv>
  { (Router, Auth.Receive (*fixme: Auth.Read *),  NicB), (Router, Auth.Send (*fixme: Auth.Write *), NicB),
    (Router, Auth.Receive (*fixme: Auth.Read *),  NicD), (Router, Auth.Send (*fixme: Auth.Write *), NicD),

    (SacController, Auth.Receive (*fixme: Auth.Read *),  NicC), (SacController, Auth.Send (*fixme: Auth.Write *), NicC),
    (SacController, Send,  EndPoint), 
  
    (RouterManager, Receive, EndPoint),
    (RouterManager, Control, Router), 
    (RouterManager, Control, NicA), 
    (RouterManager, Control, NicB),
    (RouterManager, Control, NicD)
 }"


definition SACAgentAuthGraph :: "SACLabels AgentAuthGraph" where
  "SACAgentAuthGraph = complete_AgentAuthGraph SACAgentAuthGraph_aux"

text {* Sanity check of complete_AgentAuthGraph *}
definition SACAgentAuthGraph2 :: "SACLabels AgentAuthGraph" where
  "SACAgentAuthGraph2 \<equiv> 
  { (Router, Auth.Receive (*fixme: Auth.Read *),  NicB), (Router, Auth.Send (*fixme: Auth.Write *), NicB),
    (Router, Auth.Receive (*fixme: Auth.Read *),  NicD), (Router, Auth.Send (*fixme: Auth.Write *), NicD),
    (SacController, Auth.Receive (*fixme: Auth.Read *),  NicC), (SacController, Auth.Send (*fixme: Auth.Write *), NicC),
    (SacController, Send,  EndPoint), 
  
    (RouterManager, Receive, EndPoint),
    (RouterManager, Control, Router),
    (RouterManager, Control, NicA),
    (RouterManager, Control, NicB),
    (RouterManager, Control, NicD),

    (Router, Control, Router), 
    (Router, Auth.Receive (*fixme: Auth.Read *), Router),     
    (Router, Auth.Send (*fixme: Auth.Write *), Router) , 
    (Router, Receive, Router) , 
    (Router, Send, Router),

    (NicA, Control, NicA),     
    (NicA, Auth.Receive (*fixme: Auth.Read *), NicA),     
    (NicA, Auth.Send (*fixme: Auth.Write *), NicA) , 
    (NicA, Receive, NicA) , 
    (NicA, Send, NicA),

    (NicB, Control, NicB),     
    (NicB, Auth.Receive (*fixme: Auth.Read *), NicB),     
    (NicB, Auth.Send (*fixme: Auth.Write *), NicB) , 
    (NicB, Receive, NicB) , 
    (NicB, Send, NicB),

    (NicC, Control, NicC),     
    (NicC, Auth.Receive (*fixme: Auth.Read *), NicC),     
    (NicC, Auth.Send (*fixme: Auth.Write *), NicC) , 
    (NicC, Receive, NicC) , 
    (NicC, Send, NicC),

    (NicD, Control, NicD),     
    (NicD, Auth.Receive (*fixme: Auth.Read *), NicD),     
    (NicD, Auth.Send (*fixme: Auth.Write *), NicD) , 
    (NicD, Receive, NicD) , 
    (NicD, Send, NicD),

    (ASID, Control, ASID),     
    (ASID, Auth.Receive (*fixme: Auth.Read *), ASID),     
    (ASID, Auth.Send (*fixme: Auth.Write *), ASID) , 
    (ASID, Receive, ASID) , 
    (ASID, Send, ASID) , 

    (RouterManager, Send, RouterManager),
    (RouterManager, Control, RouterManager),     
    (RouterManager, Auth.Receive (*fixme: Auth.Read *), RouterManager),     
    (RouterManager, Auth.Send (*fixme: Auth.Write *), RouterManager) , 
    (RouterManager, Receive, RouterManager) , 
    (RouterManager, Send, RouterManager),

    (EndPoint, Control, EndPoint),     
    (EndPoint, Auth.Receive (*fixme: Auth.Read *), EndPoint),     
    (EndPoint, Auth.Send (*fixme: Auth.Write *), EndPoint) , 
    (EndPoint, Receive, EndPoint) , 
    (EndPoint, Send, EndPoint),

    (SacController, Control, SacController),     
    (SacController, Auth.Receive (*fixme: Auth.Read *), SacController),     
    (SacController, Auth.Send (*fixme: Auth.Write *), SacController) , 
    (SacController, Receive, SacController) , 
    (SacController, Send, SacController),

    (RouterManager, Auth.Receive (*fixme: Auth.Read *), Router), (RouterManager, Auth.Send (*fixme: Auth.Write *), Router),
    (RouterManager, Send, Router), (RouterManager, Receive, Router),
    (RouterManager, Auth.Receive (*fixme: Auth.Read *), NicA), (RouterManager, Auth.Send (*fixme: Auth.Write *), NicA),
    (RouterManager, Send, NicA), (RouterManager, Receive, NicA),
    (RouterManager, Auth.Receive (*fixme: Auth.Read *), NicB), (RouterManager, Auth.Send (*fixme: Auth.Write *), NicB),
    (RouterManager, Send, NicB), (RouterManager, Receive, NicB),
    (RouterManager, Auth.Receive (*fixme: Auth.Read *), NicD), (RouterManager, Auth.Send (*fixme: Auth.Write *), NicD),
    (RouterManager, Send, NicD), (RouterManager, Receive, NicD)

    }"

lemma "SACAgentAuthGraph2 = complete_AgentAuthGraph SACAgentAuthGraph_aux"
  apply (simp add: complete_AgentAuthGraph_def SACAgentAuthGraph_aux_def SACAgentAuthGraph2_def)
  apply (rule equalityI)
   apply simp
  apply (rule subsetI) 
  apply (erule insertE, simp)+
  apply (erule UnE)
   apply simp
   apply (elim disjE)
    apply (elim exE)
    apply clarify
    apply (case_tac y, simp_all)(*
     apply ((case_tac ab, simp_all)+)[9]
   apply clarify
   apply (case_tac y, simp_all)
    apply ((case_tac ab, simp_all)+)[4]
  apply (elim exE) 
  apply clarify
  apply (case_tac y, simp_all)
done *) sorry (*need to come back to this later *)


text {* Definition of the PAS for the SAC *}

definition
  sacasid :: word8 where
  "sacasid = 0x100"

definition SACASIDMap :: "SACLabels agent_asid_map" where
  "SACASIDMap asid \<equiv> if asid=sacasid then ASID else undefined"

definition SACPAS :: "SACLabels PAS" where
  "SACPAS \<equiv> \<lparr> pasObjectAbs = SACAgentMap, pasASIDAbs = SACASIDMap, 
              pasPolicy = SACAgentAuthGraph, pasSubject = Router \<rparr>"


text {* proof that the SACPAS is wellformed *}

lemma SACPAS_wellformed: "pas_wellformed SACPAS"
 apply (clarsimp simp: SACPAS_def policy_wellformed_def SACAgentAuthGraph_def)
 apply (intro allI conjI impI) 
    apply (simp add: complete_AgentAuthGraph_def SACAgentAuthGraph_aux_def) 
   apply (simp add: complete_AgentAuthGraph_def SACAgentAuthGraph_aux_def)
  apply (simp add: complete_AgentAuthGraph_def SACAgentAuthGraph_aux_def)
  apply clarsimp
 apply (simp add: complete_AgentAuthGraph_def SACAgentAuthGraph_aux_def)
 apply (case_tac x, simp_all)
  apply (case_tac y, simp_all)+
done


text{* some sanity checks for is_subject, aag_has_auth_to and aag_cap_auth *}

lemma "is_subject SACPAS tcb_router" 
  by (simp add: SACPAS_def SACAgentMap_def sac_id_defs) 
lemma "is_subject SACPAS cnode_router" 
  by (simp add: SACPAS_def SACAgentMap_def sac_id_defs) 

lemma "aag_has_auth_to SACPAS Auth.Send (*fixme: Auth.Write *) frame_nicB"
 by (simp add: SACPAS_def SACAgentMap_def SACAgentAuthGraph_def sac_id_defs
                  complete_AgentAuthGraph_def SACAgentAuthGraph_aux_def)

lemma "\<not> (aag_has_auth_to SACPAS Auth.Send (*fixme: Auth.Write *) frame_nicA)"
 by (simp add: SACPAS_def SACAgentMap_def SACAgentAuthGraph_def sac_id_defs
                  complete_AgentAuthGraph_def SACAgentAuthGraph_aux_def)


lemma "aag_cap_auth SACPAS Router (Structures_A.ArchObjectCap 
       (ARM_Structs_A.PageCap frame_nicB {AllowRead} ARMSmallPage None))"
 apply (simp add: SACPAS_def SACAgentMap_def SACAgentAuthGraph_def sac_id_defs
                  complete_AgentAuthGraph_def SACAgentAuthGraph_aux_def
                  cap_auth_conferred_def) 
oops (* authority  conferred by an page cap is still to be defined (undefined) *)


text {* proof that if we have integrity between s and s', then the
values of the frames of NicA are unchanged. This means that whenever
the router is executing between s and s', it can't have changed the
frames for NicA *}

lemma SAC_integrity_frame_nicA: 
   "\<lbrakk> (integrity SACPAS {frame_nicA} s s');
      (kheap s frame_nicA) = Some (Structures_A.ArchObj p);  
      (kheap s' frame_nicA) = Some (Structures_A.ArchObj p')\<rbrakk> \<Longrightarrow>
      p=p' "
  apply (unfold integrity_def)
  apply (clarsimp simp: SACPAS_def SACAgentMap_def sac_id_defs SACAgentAuthGraph_def SACAgentAuthGraph_aux_def
                        complete_AgentAuthGraph_def)
  apply (elim integrity_obj.cases, simp_all)
done



lemma SAC_integrity_ep:
   "\<lbrakk> (integrity SACPAS {ep} s s');
      (kheap s ep) = Some (Structures_A.Endpoint p);  
      (kheap s' ep) = Some (Structures_A.Endpoint p')\<rbrakk> \<Longrightarrow>
      p=p' "
  apply (unfold integrity_def)
  apply (clarsimp simp: SACPAS_def SACAgentMap_def sac_id_defs SACAgentAuthGraph_def SACAgentAuthGraph_aux_def
                        complete_AgentAuthGraph_def)
  apply (elim integrity_obj.cases, simp_all)
done


definition SACPAS2 :: "SACLabels PAS" where
  "SACPAS2 \<equiv> \<lparr> pasObjectAbs = SACAgentMap, pasASIDAbs = SACASIDMap, 
              pasPolicy = SACAgentAuthGraph, pasSubject = SacController \<rparr>"


lemma SAC_integrity_ep:
   "\<lbrakk> (integrity SACPAS2 {ep} s s');
      (kheap s ep) = Some (Structures_A.Endpoint p);  
      (kheap s' ep) = Some (Structures_A.Endpoint p')\<rbrakk> \<Longrightarrow>
      p=p' "
  apply (unfold integrity_def)
  apply (clarsimp simp: SACPAS2_def SACAgentMap_def sac_id_defs SACAgentAuthGraph_def SACAgentAuthGraph_aux_def
                        complete_AgentAuthGraph_def)
  apply (elim integrity_obj.cases, simp_all)
oops

text {* all these proofs are trivial for now, because integrity is still underdefined 

Discussion with Simon: we're more interested in checking state_objs_to_policy

*}



text {*=================================================================*}


text {* defining an initial state *}

text {* we want to use the dump from the SAC example, but this is at
the capDL level, so we want to extract a state at the abstract
level. So we define the inverse of the transform function (with having
'undefined' wherever the information is not in the capDL -or we don't
need it for the state_objs_to_policy function).

The state_objs_to_policy function only needs the heap and the cdt.

*}


definition 
  transform_inv_tcb :: "cdl_tcb \<Rightarrow> Structures_A.kernel_object"
where 
  "transform_inv_tcb = undefined"


definition
  transform_inv_cap :: "cdl_cap \<Rightarrow> Structures_A.cap"
where
  "transform_inv_cap = undefined"


(* Convert a bool list of the given size into a nat. *)
definition
  bl_to_nat :: "bool list \<Rightarrow> nat"
where
  "bl_to_nat b \<equiv>
    number_of (bl_to_bin b)"



lemma " nat_to_bl n sz = Some b  \<Longrightarrow> bl_to_nat b = n"
  apply (simp add: nat_to_bl_def bl_to_nat_def)
  apply (cases "2 ^ n \<le> sz", clarsimp+)
  apply (simp add: bin_bl_bin[simplified])
sorry



definition
  transform_inv_cnode :: "cdl_cnode \<Rightarrow> Structures_A.kernel_object"
where
  "transform_inv_cnode = undefined"
(*  "transform_cnode_contents c \<equiv> \<lambda>n. option_map transform_inv_cap (option_map_join c (nat_to_bl (ct_bits c) n))" *)



definition
  transform_inv_page_table:: "cdl_page_table\<Rightarrow> (word8 \<Rightarrow> ARM_Structs_A.pte)"
where
  "transform_inv_page_table = undefined"

definition
  transform_inv_page_directory:: "cdl_page_directory\<Rightarrow> (12 word \<Rightarrow> ARM_Structs_A.pde)"
where 
  "transform_inv_page_directory = undefined"

definition 
  size_for_pageBits :: "nat \<Rightarrow> vmpage_size"
where
  "size_for_pageBits n \<equiv>
     if n=12 then ARMSmallPage else
     if n=16 then ARMLargePage else
     if n=20 then ARMSection else
     if n=24 then ARMSuperSection else undefined"


definition
  transform_inv_object :: "cdl_object \<Rightarrow>  Structures_A.kernel_object"
  where
  "transform_inv_object obj \<equiv> case obj of
            Endpoint \<Rightarrow> (Structures_A.Endpoint undefined)
          | AsyncEndpoint \<Rightarrow> (Structures_A.AsyncEndpoint undefined)
          | Tcb t \<Rightarrow> transform_inv_tcb t
          | CNode c \<Rightarrow> transform_inv_cnode c 
          | Untyped \<Rightarrow> undefined
          | AsidPool \<Rightarrow> (Structures_A.ArchObj (ARM_Structs_A.ASIDPool undefined))
          | PageTable pt \<Rightarrow> (Structures_A.ArchObj (ARM_Structs_A.PageTable (transform_inv_page_table pt)))
          | PageDirectory pd \<Rightarrow> (Structures_A.ArchObj (ARM_Structs_A.PageDirectory (transform_inv_page_directory pd)))
          | Frame f \<Rightarrow> (Structures_A.ArchObj (ARM_Structs_A.DataPage (size_for_pageBits (cdl_frame_size_bits f ))))
          | IrqSlot i \<Rightarrow> undefined"


definition 
  transform_inv_kheap :: "cdl_state \<Rightarrow> kheap "
where 
  "transform_inv_kheap s = (\<lambda> ptr. 
      option_map  (transform_inv_object) (cdl_objects s (Standard ptr))) "


definition
  transform_inv :: "cdl_state \<Rightarrow> state"
where
  "transform_inv s \<equiv> \<lparr>
    kheap = transform_inv_kheap s,
    cdt = undefined,
    is_original_cap = undefined,
    cur_thread = undefined,
    idle_thread = undefined,
    machine_state = undefined,
    interrupt_irq_node = undefined,
    interrupt_states = undefined,
    arch_state = undefined
    \<rparr>"

(* somes guesses on what we actually need in the state *)
lemma "s= transform_inv state \<Longrightarrow> a = state_objs_to_policy s"
  apply (unfold transform_inv_def) 
  apply (unfold transform_inv_kheap_def) 
  apply (unfold Option.map_def)
  apply (unfold transform_inv_object_def)

  apply (unfold state_def) 
  apply simp
  apply (unfold objects_def) apply simp
oops

text {*


TODO: finish defining this function *} 



text {*=================================================================*}


text {* defining the full SAC initial state and policy *}


datatype SACFullLabels = 
    NicA | NicB | NicC | NicD
  | RouterManager |  SacController | Timer
  | EndPointCRM | AsyncEndPointTC | AsyncEndPointTRM
  | ASID
  | IO  (* Fixme: IOports and devices - need to be removed because it's arm *)
  | IRQ  (* Fixme: this is for empty cnodes in irq, not sure what I'm supposed to do with them *)

definition SACFullAgentMap :: "SACFullLabels agent_map" where 
  "SACFullAgentMap \<equiv> (\<lambda>_. undefined) 
     (0    := AsyncEndPointTC,
      1    := AsyncEndPointTRM,
      2    := ASID,           (* Timer's ASID - fixme: do we need one label per asid? *)
      3    := ASID,           (* RM's asid *)
      4    := ASID,           (* SAC_C's asid *)
      5    := SacController,  (* SAC_C's cspace *)
      6    := SacController,  (* SAC_C's cspace *)
      7    := RouterManager,  (* RM's cspace *)
      8    := Timer,          (* Timer's cspace *)
      9    := EndPointCRM,
      10   := NicC,
      43   := NicA,
      107  := NicB ,
      171  := NicD ,
      280  := RouterManager,  (* R's vspace - Fixme: do I need to put it in a new label R? *)
      287  := RouterManager,  (* RM's vspace *)
      288  := RouterManager,  (* RM's vspace *)
      301  := Timer,          (* Timer's vspace *)
      302  := Timer,          (* Timer's vspace *)
      1448 := RouterManager,  (* R's vspace - Fixme: do I need to put it in a new label R? *)
      1455 := SacController,  (* SAC-C's vspace *)
      1612 := SacController,  (* SAC-C's vspace *)
      1613 := RouterManager,  (* R's vspace - Fixme: do I need to put it in a new label R? *)
      2223 := SacController,  (* SAC-C's vspace *)
      2332 := SacController,  (* SAC-C's vspace *)
      3053 := IO, 
      3054 := IO,
      3055 := IO,
      3056 := IO,
      3057 := IO,
      3058 := IRQ,
      3063 := SacController,  (* SAC-C's vspace *)
      3064 := RouterManager,  (* R's vspace - Fixme: do I need to put it in a new label R? *)
      3065 := RouterManager,  (* RM's vspace *)
      3066 := Timer,          (* Timer's vspace *)
      3067 := SacController,  (* SAC-C's vspace *)
      3068 := RouterManager,  (* RM's vspace *)
      3069 := Timer,          (* Timer's vspace *)
      3070 := SacController,  (* SAC-C's vspace *)
      3071 := SacController,  (* SAC-C's vspace *)
      3072 := SacController,  (* SAC-C's vspace *)
      3073 := RouterManager,  (* RM's vspace *)
      3074 := RouterManager,  (* R's vspace - Fixme: do I need to put it in a new label R? *)
      3075 := RouterManager,  (* R's vspace - Fixme: do I need to put it in a new label R? *)
      3076 := RouterManager,  (* R's vspace - Fixme: do I need to put it in a new label R? *)
      3077 := RouterManager,  (* RM's vspace *)
      3078 := Timer,          (* Timer's vspace *)
      3079 := SacController,  (* SAC-C's tcb *)
      3080 := RouterManager,  (* RM's tcb *)
      3081 := Timer,          (* Timer's tcb*)
      3123 := Timer,          (* Timer's untyped*)
      3124 := RouterManager,  (* RM's untyped *)
      3151 := SacController   (* SAC-C's untyped *)
)"


definition SACFullAgentAuthGraph_aux :: "SACFullLabels AgentAuthGraph" where
  "SACFullAgentAuthGraph_aux \<equiv>
  { (SacController, Auth.Receive (*fixme: Auth.Read *),  NicC), 
    (SacController, Auth.Send (*fixme: Auth.Write *), NicC),
    (SacController, Auth.Send, EndPointCRM),
    (SacController, Auth.Receive, AsyncEndPointTC),  (* fixeme: IO?? *)
  
    (RouterManager, Auth.Receive (*fixme: Auth.Read *), NicA), 
    (RouterManager, Auth.Send (*fixme: Auth.Write *), NicA),
    (RouterManager, Auth.Receive (*fixme: Auth.Read *), NicB), 
    (RouterManager, Auth.Send (*fixme: Auth.Write *), NicB),
    (RouterManager, Auth.Receive (*fixme: Auth.Read *), NicD), 
    (RouterManager, Auth.Send (*fixme: Auth.Write *), NicD),  (*fixme: also Send/receive to Nics? *)
    (RouterManager, Auth.Receive, EndPointCRM), 
    (RouterManager, Auth.Receive, AsyncEndPointTRM),  (* fixeme: IO?? *)

    (Timer, Auth.Send, AsyncEndPointTRM),
    (Timer, Auth.Send, AsyncEndPointTC)

 }"


definition SACFullAgentAuthGraph :: "SACFullLabels AgentAuthGraph" where
  "SACFullAgentAuthGraph = complete_AgentAuthGraph SACFullAgentAuthGraph_aux"


definition SACFullASIDMap :: "SACFullLabels agent_asid_map" where
  "SACFullASIDMap \<equiv> (\<lambda>_. undefined) 
     (2 := ASID, 3 := ASID, 4 := ASID )"


definition SACFullPAS :: "SACFullLabels PAS" where
  "SACFullPAS \<equiv> \<lparr> pasObjectAbs = SACFullAgentMap, pasASIDAbs = SACFullASIDMap, 
              pasPolicy = SACFullAgentAuthGraph, pasSubject = SacController \<rparr>"



lemma SACFullPAS_wellformed: "pas_wellformed SACFullPAS"
 apply (clarsimp simp: SACFullPAS_def policy_wellformed_def SACFullAgentAuthGraph_def)
 apply (intro allI conjI impI) 
    apply (simp add: complete_AgentAuthGraph_def SACFullAgentAuthGraph_aux_def) +
done

 
lemma SACFull_pas_refined: "pas_refined SACFullPAS (transform_inv state)"
  apply (clarsimp simp: pas_refined_def)
  apply (rule conjI, simp add: SACFullPAS_wellformed)
  apply (rule conjI)
   apply (clarsimp simp: auth_graph_map_def SACFullPAS_def)
   apply (clarsimp simp: state_objs_to_policy_def) 

(* I really need 
     . (caps_of_state (transform_inv state))
     . (state_refs_of (transform_inv state)) 
     . (cdt (transform_inv state))
     . (state_vrefs (transform_inv state)) 

I should try on smaller example
*)
sorry


text {*=================================================================*}


text {* defining a very dummy example *}

datatype MinSysLabels = 
    L0 | L1

definition MinSysAgentMap :: "MinSysLabels agent_map" where 
  "MinSysAgentMap \<equiv> (\<lambda>_. undefined) 
     (0    := L0,
      1    := L1)"


definition cnode0 :: cnode_contents where
 "cnode0 \<equiv> [[True]  \<mapsto> Structures_A.EndpointCap (0::obj_ref) (0:: machine_word) {AllowSend},
            [False] \<mapsto> Structures_A.NullCap ]"

definition kh0 :: kheap where
 "kh0 \<equiv> [ 0 \<mapsto> Structures_A.Endpoint (Structures_A.RecvEP []) , 
          1 \<mapsto> Structures_A.CNode cnode0 ]"

definition s0 :: state where
"s0 \<equiv>  \<lparr>
    kheap = kh0,
    cdt = empty,
    is_original_cap = undefined,
    cur_thread = undefined,
    idle_thread = undefined,
    machine_state = undefined,
    interrupt_irq_node = undefined,
    interrupt_states = undefined,
    arch_state = undefined
    \<rparr>"



definition MinSysAgentAuthGraph_aux :: "MinSysLabels AgentAuthGraph" where
  "MinSysAgentAuthGraph_aux \<equiv>
  { (L1, Auth.Send, L0) }"

definition MinSysAgentAuthGraph:: "MinSysLabels AgentAuthGraph" where
  "MinSysAgentAuthGraph \<equiv> complete_AgentAuthGraph MinSysAgentAuthGraph_aux"


definition MinSysPAS :: "MinSysLabels PAS" where
  "MinSysPAS \<equiv> \<lparr> pasObjectAbs = MinSysAgentMap, pasASIDAbs = undefined, 
              pasPolicy = MinSysAgentAuthGraph, pasSubject = L1 \<rparr>"

lemma cnode0_well_formed: "well_formed_cnode cnode0"
 apply (clarsimp simp: cnode0_def well_formed_cnode_def well_formed_cnode_n_def)
 apply (rule_tac x=1 in exI) 
 apply (rule set_eqI)
 apply clarsimp
 apply (rule iffI)
  apply (erule disjE, simp_all) [1]
 apply (case_tac x, simp, clarsimp)
done


lemma s0_caps_of_state : "caps_of_state s0 = 
       [((1::obj_ref,[True]))  \<mapsto> Structures_A.EndpointCap (0::obj_ref) (0:: machine_word) {AllowWrite},
        ((1::obj_ref,[False])) \<mapsto> Structures_A.NullCap ]"
  apply (insert cnode0_well_formed)
  apply (simp add: caps_of_state_cte_wp_at cte_wp_at_cases s0_def kh0_def cnode0_def)
  apply (rule ext, clarsimp simp add: cte_wp_at_cases)
done 

lemma s0_state_refs_of: "state_refs_of s0 objrf = {}"
 by (simp add: state_refs_of_def s0_def kh0_def)

lemma s0_state_vrefs: "state_vrefs s0 objrf = {}"
 by (simp add: state_vrefs_def s0_def kh0_def vs_refs_no_global_pts_def)

lemma MinSys_wellformed: "pas_wellformed MinSysPAS"
 apply (clarsimp simp: MinSysPAS_def policy_wellformed_def MinSysAgentAuthGraph_def)
 apply (clarsimp simp: MinSysAgentAuthGraph_aux_def complete_AgentAuthGraph_def)
done

lemma "pas_refined MinSysPAS s0"
  apply (clarsimp simp: pas_refined_def)
  apply (intro conjI)
    apply (simp add: MinSys_wellformed)
   apply (clarsimp simp: auth_graph_map_def MinSysPAS_def)
   apply (clarsimp simp: state_objs_to_policy_def state_bits_to_policy_def)
   apply (erule state_bits_to_policyp.cases, simp_all, clarsimp)
        apply (clarsimp simp: s0_caps_of_state)
        apply (case_tac "a=1 \<and> b=[False]", clarsimp+)
        apply (case_tac "a=1 \<and> b=[True]", clarsimp)
         apply (clarsimp simp:cap_auth_conferred_def cap_rights_to_auth_def)
         apply (clarsimp simp: MinSysAgentMap_def MinSysAgentAuthGraph_def)
         apply (clarsimp simp: MinSysAgentAuthGraph_aux_def complete_AgentAuthGraph_def)
        apply clarsimp
       apply clarsimp
       apply (clarsimp simp: s0_caps_of_state)
       apply (case_tac "a=1 \<and> b=[False]", clarsimp+)
       apply (case_tac "a=1 \<and> b=[True]", clarsimp+)
      apply (simp add: s0_state_refs_of)
     apply (simp add: s0_def)
    apply (simp add: s0_state_vrefs)+
  apply (simp add: s0_caps_of_state)
  apply (rule subsetI, clarsimp)
  apply (erule Access.state_asids_to_policy_aux.cases)
   apply (clarsimp simp:  MinSysPAS_def MinSysAgentAuthGraph_def
                          MinSysAgentAuthGraph_aux_def complete_AgentAuthGraph_def
                          MinSysAgentMap_def)
   apply (case_tac "ab=1 \<and> ba = [False]", clarsimp+)
   apply (case_tac "ab=1 \<and> ba = [True]", clarsimp+)
  apply (case_tac "ab=1 \<and> ba = [False]", clarsimp+)
  apply (case_tac "ab=1 \<and> ba = [True]", clarsimp+)
done


     

(* then I could try to link the abstract state to an equivalent
cdl_state, to better understand how transform_inv should be defined *)




text {*=================================================================*}

text {* manual small SAC state at abstract level *}



text {* SAC-C's CSpace *}

definition the_nat_to_bl :: "nat \<Rightarrow> nat \<Rightarrow> bool list" where
 "the_nat_to_bl sz n \<equiv> the (nat_to_bl sz n)"

definition the_nat_to_bl_10  :: "nat \<Rightarrow> bool list"where
 "the_nat_to_bl_10 n \<equiv> the_nat_to_bl 10 n"


definition asid3063 :: machine_word where
"asid3063 \<equiv> 1<<asid_low_bits" 

definition asid3065 :: machine_word where
"asid3065 \<equiv> 2<<asid_low_bits" 

lemma "asid_high_bits_of asid3065 \<noteq> asid_high_bits_of asid3063"
apply (simp add: asid3063_def asid_high_bits_of_def asid3065_def asid_low_bits_def)
done


definition caps6 :: Structures_A.cnode_contents where
"caps6 \<equiv> 
   (Retype_A.empty_cnode 10)
         ( (the_nat_to_bl_10 1)   \<mapsto> Structures_A.ThreadCap 3079, 
           (the_nat_to_bl_10 2)   \<mapsto> Structures_A.CNodeCap 6 undefined undefined, 
           (the_nat_to_bl_10 3)   \<mapsto> Structures_A.ArchObjectCap (ARM_Structs_A.PageDirectoryCap 3063 (Some asid3063)),
           (the_nat_to_bl_10 318) \<mapsto> Structures_A.EndpointCap  9 0 {AllowSend} )"

definition obj6 :: kernel_object where
"obj6 \<equiv> Structures_A.CNode caps6"

text {* RM's Cspace *}

definition caps7 :: Structures_A.cnode_contents where
"caps7 \<equiv> 
   (Retype_A.empty_cnode 10)
         ( (the_nat_to_bl_10 1)   \<mapsto> Structures_A.ThreadCap 3080, 
           (the_nat_to_bl_10 2)   \<mapsto> Structures_A.CNodeCap 7 undefined undefined,
           (the_nat_to_bl_10 3)   \<mapsto> Structures_A.ArchObjectCap (ARM_Structs_A.PageDirectoryCap 3065 (Some asid3065)),
           (the_nat_to_bl_10 318) \<mapsto> Structures_A.EndpointCap  9 0 {AllowRecv}) "

definition obj7 :: kernel_object where
"obj7 \<equiv> Structures_A.CNode caps7"


text {* endpoint between SAC-C and RM *}

definition obj9 :: kernel_object where
"obj9 \<equiv> Structures_A.Endpoint Structures_A.IdleEP"


text {* SAC-C's VSpace (PageDirectory)*}

definition pt3072 :: "word8 \<Rightarrow> ARM_Structs_A.pte " where
"pt3072 \<equiv> (\<lambda>_. ARM_Structs_A.InvalidPTE)( 0 := ARM_Structs_A.SmallPagePTE undefined undefined undefined)"

definition obj3072 :: kernel_object where
"obj3072 \<equiv> Structures_A.ArchObj (ARM_Structs_A.PageTable pt3072)"


definition pd3063 :: "12 word \<Rightarrow> ARM_Structs_A.pde " where
"pd3063 \<equiv> (\<lambda>_. ARM_Structs_A.InvalidPDE)
             ( 0 := ARM_Structs_A.PageTablePDE (Platform.addrFromPPtr 3072) undefined undefined )"
(* used addrFromPPtr because proof gives me ptrFromAddr.. need to check if it's right *)



definition obj3063 :: kernel_object where
"obj3063 \<equiv> Structures_A.ArchObj (ARM_Structs_A.PageDirectory pd3063)"


text {* RM's VSpace (PageDirectory)*}


definition pt3077 :: "word8 \<Rightarrow> ARM_Structs_A.pte " where
"pt3077 \<equiv> (\<lambda>_. ARM_Structs_A.InvalidPTE)( 0 := ARM_Structs_A.SmallPagePTE undefined undefined undefined)"

definition obj3077 :: kernel_object where
"obj3077 \<equiv> Structures_A.ArchObj (ARM_Structs_A.PageTable pt3077)"


definition pd3065 :: "12 word \<Rightarrow> ARM_Structs_A.pde " where
"pd3065 \<equiv> (\<lambda>_. ARM_Structs_A.InvalidPDE)
        (0 := ARM_Structs_A.PageTablePDE  (Platform.addrFromPPtr 3077) undefined undefined )" 
(* used addrFromPPtr because proof gives me ptrFromAddr.. need to check if it's right *)

definition obj3065 :: kernel_object where
"obj3065 \<equiv> Structures_A.ArchObj (ARM_Structs_A.PageDirectory pd3065)"


text {* SAC-C's tcb *}

definition dummycap :: Structures_A.cap
where "dummycap \<equiv> Structures_A.NullCap"  
(* TODO: fixme - used for replycap callercap and ipcframecap - I need to check what these should be *)

definition obj3079 :: kernel_object where
"obj3079 \<equiv> Structures_A.TCB \<lparr> 
              tcb_ctable        = Structures_A.CNodeCap 6 undefined undefined ,
              tcb_vtable        = Structures_A.ArchObjectCap (ARM_Structs_A.PageDirectoryCap 3063 (Some asid3063)),
              tcb_reply         = dummycap,
              tcb_caller        = dummycap,
              tcb_ipcframe      = dummycap,
              tcb_state         = Structures_A.Running,    (* I don't think we need the rest *)
              tcb_fault_handler = undefined, 
              tcb_ipc_buffer    = undefined,
              tcb_context       = undefined,
              tcb_fault         = undefined \<rparr>"

text {* RM's tcb *}

definition obj3080 :: kernel_object where
"obj3080 \<equiv> Structures_A.TCB \<lparr> 
              tcb_ctable        = Structures_A.CNodeCap 7 undefined undefined ,
              tcb_vtable        = Structures_A.ArchObjectCap (ARM_Structs_A.PageDirectoryCap 3065 (Some asid3065)),
              tcb_reply         = dummycap,
              tcb_caller        = dummycap,
              tcb_ipcframe      = dummycap,
              tcb_state         = Structures_A.BlockedOnReceive 9 True,   (* I don't think we need the rest *)
              tcb_fault_handler = undefined, 
              tcb_ipc_buffer    = undefined,
              tcb_context       = undefined,
              tcb_fault         = undefined \<rparr>"

(* the boolean in BlockedOnReceive is True if the object can receive but not send.
but Tom says it only matters if the sender can grant - which is not the case of the SAC-C - I think *)

definition kh1 :: kheap where 
 "kh1 \<equiv> [ 6 \<mapsto> obj6,
          7 \<mapsto> obj7,
          9 \<mapsto> obj9,
          3063 \<mapsto> obj3063,
          3065 \<mapsto> obj3065,
          3072 \<mapsto> obj3072,
          3077 \<mapsto> obj3077,
          3079 \<mapsto> obj3079,
          3080 \<mapsto> obj3080 ]"

lemmas kh1_obj_def = 
  obj6_def obj7_def obj9_def obj3063_def obj3065_def 
  obj3072_def obj3077_def obj3079_def obj3080_def 



definition s1 :: state where
"s1 \<equiv>  \<lparr>
    kheap = kh1,
    cdt = empty,
    is_original_cap = undefined,
    cur_thread = undefined,
    idle_thread = undefined,
    machine_state = undefined,
    interrupt_irq_node = undefined,
    interrupt_states = undefined,
    arch_state = undefined
    \<rparr>"




datatype SysLabels = 
    SacC | RM |Ep9

definition SysAgentMap :: "SysLabels agent_map" where 
  "SysAgentMap \<equiv> (\<lambda>_. undefined) 
     (6 := SacC,
      7 := RM,
      9 := Ep9,
      3063 := SacC,
      3065 := RM,
      3072 := SacC, 
      3077 := RM,
      3079 := SacC,
      3080 := RM )"


definition SysAgentAuthGraph_aux :: "SysLabels AgentAuthGraph" where
  "SysAgentAuthGraph_aux \<equiv>
  { (SacC, Auth.Send, Ep9), (RM, Auth.Receive, Ep9) }"

definition SysAgentAuthGraph:: "SysLabels AgentAuthGraph" where
  "SysAgentAuthGraph \<equiv> complete_AgentAuthGraph SysAgentAuthGraph_aux"


definition SysASIDMap :: "SysLabels agent_asid_map" where 
  "SysASIDMap \<equiv>  (\<lambda>_. undefined) 
     ((asid_high_bits_of asid3063) := SacC,
      (asid_high_bits_of asid3065) := RM )"

definition SysPAS :: "SysLabels PAS" where
  "SysPAS \<equiv> \<lparr> pasObjectAbs = SysAgentMap, pasASIDAbs = SysASIDMap, 
              pasPolicy = SysAgentAuthGraph, pasSubject = SacC \<rparr>"




lemma caps7_well_formed: "well_formed_cnode caps7"
 apply (clarsimp simp: caps7_def well_formed_cnode_def well_formed_cnode_n_def) 
 apply (clarsimp simp: the_nat_to_bl_10_def the_nat_to_bl_def nat_to_bl_def)
 apply (clarsimp simp: Retype_A.empty_cnode_def dom_def)
 apply (rule_tac x=10 in exI)
 apply (rule set_eqI, clarsimp)
 apply (rule iffI)
  apply (elim disjE, insert len_bin_to_bl, simp_all)[1] 
 apply clarsimp
done

lemma caps6_well_formed: "well_formed_cnode caps6"
 apply (clarsimp simp: caps6_def well_formed_cnode_def well_formed_cnode_n_def) 
 apply (clarsimp simp: the_nat_to_bl_10_def the_nat_to_bl_def nat_to_bl_def)
 apply (clarsimp simp: Retype_A.empty_cnode_def dom_def)
 apply (rule_tac x=10 in exI)
 apply (rule set_eqI, clarsimp)
 apply (rule iffI)
  apply (elim disjE, insert len_bin_to_bl, simp_all)[1] 
 apply clarsimp
done


lemma tcb_cnode_index_nat_to_bl:
  "n<10 \<Longrightarrow> the_nat_to_bl_10 n \<noteq> tcb_cnode_index n"
  by (clarsimp simp: the_nat_to_bl_10_def the_nat_to_bl_def tcb_cnode_index_def
                        nat_to_bl_def to_bl_def bin_to_bl_aux_def)

lemma s1_caps_of_state : 
  "caps_of_state s1 p = Some cap \<Longrightarrow>
     cap = Structures_A.NullCap \<or>
     (p,cap) \<in>  
       { ((6::obj_ref,(the_nat_to_bl_10 1)),  Structures_A.ThreadCap 3079),
         ((6::obj_ref,(the_nat_to_bl_10 2)),  Structures_A.CNodeCap 6 undefined undefined),
         ((6::obj_ref,(the_nat_to_bl_10 3)),  Structures_A.ArchObjectCap (ARM_Structs_A.PageDirectoryCap 3063 (Some asid3063))), 
         ((6::obj_ref,(the_nat_to_bl_10 318)),Structures_A.EndpointCap  9 0 {AllowSend}),
         ((7::obj_ref,(the_nat_to_bl_10 1)),  Structures_A.ThreadCap 3080), 
         ((7::obj_ref,(the_nat_to_bl_10 2)),  Structures_A.CNodeCap 7 undefined undefined),
         ((7::obj_ref,(the_nat_to_bl_10 3)),  Structures_A.ArchObjectCap (ARM_Structs_A.PageDirectoryCap 3065 (Some asid3065))), 
         ((7::obj_ref,(the_nat_to_bl_10 318)),Structures_A.EndpointCap  9 0 {AllowRecv}) ,
         ((3079::obj_ref, (tcb_cnode_index 0)), Structures_A.CNodeCap 6 undefined undefined ),
         ((3079::obj_ref, (tcb_cnode_index 1)), Structures_A.ArchObjectCap (ARM_Structs_A.PageDirectoryCap 3063 (Some asid3063))),
         ((3079::obj_ref, (tcb_cnode_index 2)), dummycap),
         ((3079::obj_ref, (tcb_cnode_index 3)), dummycap),
         ((3079::obj_ref, (tcb_cnode_index 4)), dummycap),
         ((3080::obj_ref, (tcb_cnode_index 0)), Structures_A.CNodeCap 7 undefined undefined ),
         ((3080::obj_ref, (tcb_cnode_index 1)), Structures_A.ArchObjectCap (ARM_Structs_A.PageDirectoryCap 3065 (Some asid3065))),
         ((3080::obj_ref, (tcb_cnode_index 2)), dummycap),
         ((3080::obj_ref, (tcb_cnode_index 3)), dummycap),
         ((3080::obj_ref, (tcb_cnode_index 4)), dummycap)} "
  apply (insert caps7_well_formed)
  apply (insert caps6_well_formed) 
  apply (simp add: caps_of_state_cte_wp_at cte_wp_at_cases s1_def kh1_def kh1_obj_def)
  apply (case_tac p, clarsimp)
  apply (clarsimp split: if_splits)
     apply (clarsimp simp: cte_wp_at_cases tcb_cap_cases_def split: split_if_asm)+ 
   apply (clarsimp simp: caps7_def split: if_splits)
  apply (clarsimp simp: caps6_def cte_wp_at_cases  split: if_splits)
done


  

lemma Sys_wellformed: "pas_wellformed SysPAS"
 apply (clarsimp simp: SysPAS_def policy_wellformed_def SysAgentAuthGraph_def)
 apply (clarsimp simp: SysAgentAuthGraph_aux_def complete_AgentAuthGraph_def)
done



lemma "pas_refined SysPAS s1"
  apply (clarsimp simp: pas_refined_def)
  apply (intro conjI)
    apply (simp add: Sys_wellformed)
   apply (clarsimp simp: auth_graph_map_def SysPAS_def
                         state_objs_to_policy_def state_bits_to_policy_def)
   apply (erule state_bits_to_policyp.cases, simp_all, clarsimp)
        apply (drule s1_caps_of_state, clarsimp)
        apply (elim disjE, 
               (clarsimp simp: cap_auth_conferred_def SysAgentMap_def SysAgentAuthGraph_def
                                complete_AgentAuthGraph_def SysAgentAuthGraph_aux_def
                                cap_rights_to_auth_def
                                dummycap_def)+) [1]
       apply (drule s1_caps_of_state, clarsimp)
       apply (elim disjE, (clarsimp simp: dummycap_def)+)
      apply (clarsimp simp: state_refs_of_def s1_def kh1_def kh1_obj_def split: if_splits)
      apply (clarsimp simp: SysAgentMap_def)
      (* oops - if thread_state is blocked on receive, the uathority should be undefined! *)
      defer
     apply (simp add: s1_def) (* this is OK because cdt is empty..*)

    apply ((clarsimp simp: state_vrefs_def vs_refs_no_global_pts_def s1_def kh1_def kh1_obj_def split: if_splits,
           ((clarsimp split: if_splits 
                     simp: pd3065_def pd3063_def graph_of_def pde_ref_def
                           SysAgentMap_def SysAgentAuthGraph_def
                           complete_AgentAuthGraph_def SysAgentAuthGraph_aux_def)+)[2])+)[2] (*long*)

  apply (rule subsetI, clarsimp)
  apply (erule state_asids_to_policy_aux.cases)
   apply clarsimp
   apply (((drule s1_caps_of_state, clarsimp,
          elim disjE, (clarsimp simp: SysPAS_def SysASIDMap_def SysAgentMap_def SysAgentAuthGraph_def SysAgentAuthGraph_aux_def complete_AgentAuthGraph_def
                      asid3065_def asid3063_def asid_high_bits_of_def asid_low_bits_def dummycap_def)+) [1]) +)[2] (*long*)
sorry




end
