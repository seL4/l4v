(*
 * Copyright 2018, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory Policy_CAMKES_CDL imports
  "CamkesAdlSpec.Types_CAMKES"
  "CamkesAdlSpec.Library_CAMKES"
  "Access.Access"
begin

text \<open>Defining suitable access policies from CAmkES compositions.\<close>

abbreviation "edge_subject \<equiv> fst"
abbreviation "edge_auth \<equiv> fst o snd"
abbreviation "edge_object \<equiv> snd o snd"

type_synonym label = string


section \<open>Generic policy definitions\<close>
text {*
  Access rights entailed by a given CAmkES component system. We assign
  each component and connector its own label, which is just its name
  in the CAmkES assembly.
*}
definition
  policy_of :: "assembly \<Rightarrow> label auth_graph"
where
  "policy_of spec \<equiv>
     (* Every label has every authority over itself. *)
     {edge. edge_subject edge \<in> fst ` set (components (composition spec)) \<and>
            edge_subject edge = edge_object edge} \<union>

     (* Senders on seL4RPC connections. *)
     {edge. \<exists>from. from \<in> fst ` set (components (composition spec)) \<and>
                   (\<exists>conn \<in> set (connections (composition spec)).
                      from \<in> set (from_components (snd conn)) \<and>
                      conn_type (snd conn) = seL4RPC \<and>
                      edge_object edge = fst conn) \<and>
                    edge_subject edge = from \<and>
                    edge_auth edge \<in> {Receive, Reset, SyncSend}} \<union>

     (* Receivers on seL4RPC connections. *)
     {edge. \<exists>to. to \<in> fst ` set (components (composition spec)) \<and>
                 (\<exists>conn \<in> set (connections (composition spec)).
                    to \<in> set (to_components (snd conn)) \<and>
                    conn_type (snd conn) = seL4RPC \<and>
                    edge_object edge = fst conn) \<and>
                  edge_subject edge = to \<and>
                  edge_auth edge \<in> {Receive, Reset, SyncSend}} \<union>

     (* Senders on seL4Asynch connections. *)
     {edge. \<exists>from. from \<in> fst ` set (components (composition spec)) \<and>
                   (\<exists>conn \<in> set (connections (composition spec)).
                      from \<in> set (from_components (snd conn)) \<and>
                      conn_type (snd conn) = seL4Asynch \<and>
                      edge_object edge = fst conn) \<and>
                    edge_subject edge = from \<and>
                    edge_auth edge \<in> {Notify, Reset}} \<union>

     (* Receivers on seL4Asynch connections. *)
     {edge. \<exists>to. to \<in> fst ` set (components (composition spec)) \<and>
                 (\<exists>conn \<in> set (connections (composition spec)).
                    to \<in> set (to_components (snd conn)) \<and>
                    conn_type (snd conn) = seL4Asynch \<and>
                    edge_object edge = fst conn) \<and>
                  edge_subject edge = to \<and>
                  edge_auth edge \<in> {Receive, Reset}} \<union>

     (* Senders and recievers on dataports.
        Here, we always assume both sides have Read and Write because
        most of the dataport implementations use in-line signalling. *)
     {edge. \<exists>from. from \<in> fst ` set (components (composition spec)) \<and>
                   (\<exists>conn \<in> set (connections (composition spec)).
                      from \<in> set (from_components (snd conn)) \<and>
                      conn_type (snd conn) = seL4SharedData \<and>
                      edge_object edge = fst conn) \<and>
                    edge_subject edge = from \<and>
                    edge_auth edge \<in> {Read, Write}} \<union>

     {edge. \<exists>to. to \<in> fst ` set (components (composition spec)) \<and>
                 (\<exists>conn \<in> set (connections (composition spec)).
                    to \<in> set (to_components (snd conn)) \<and>
                    conn_type (snd conn) = seL4SharedData \<and>
                    edge_object edge = fst conn) \<and>
                  edge_subject edge = to \<and>
                  edge_auth edge \<in> {Read, Write}}"

end