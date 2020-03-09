(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Policy_CAMKES_CDL imports
  "CamkesAdlSpec.Types_CAMKES"
  "CamkesAdlSpec.Library_CAMKES"
  "Access.Access"
begin

text \<open>Defining suitable access policies from CAmkES compositions.\<close>

type_synonym label = string


section \<open>Generic policy definitions\<close>
text \<open>
  Access rights entailed by a given CAmkES component system.

  We assign each component and connector its own label, which is just
  its name in the CAmkES assembly.

  @{typ connector}s already declare the access rights that they provide,
  so this is merely a convenience function that puts them all together.
\<close>
definition
  policy_of :: "assembly \<Rightarrow> label auth_graph"
where
  "policy_of spec \<equiv>
     let component_groups = get_group_label (composition spec) `
                            fst ` set (components (composition spec))
     in
     \<comment> \<open>First, some global assumptions.\<close>

     \<comment> \<open>Every component has every authority over itself.\<close>
     {(subj, auth, obj).
           subj \<in> component_groups \<and>
           subj = obj
     } \<union>

     \<comment> \<open>FIXME: @{const policy_wellformed} makes DeleteDerived too transitive.
         For now, we relax it even further and say that reply caps from any component
         can end up in any other component. (Jira VER-1030)\<close>
     {(subj, auth, obj).
           subj \<in> component_groups \<and>
           obj \<in> component_groups \<and>
           subj \<noteq> obj \<and>
           auth = DeleteDerived
     } \<union>

    \<comment> \<open>Now, just read out the rights implied by each connector.\<close>
    {(subj, auth, obj).
           \<exists>conn \<in> snd ` set (connections (composition spec)).
             subj \<in> get_group_label (composition spec) `fst ` set (conn_from conn) \<and>
             obj  \<in> get_group_label (composition spec) `fst ` set (conn_to conn) \<and>
             auth \<in> access_from_to (connector_access (conn_type conn))
    } \<union>
    {(subj, auth, obj).
           \<exists>conn \<in> snd ` set (connections (composition spec)).
             subj \<in> get_group_label (composition spec) `fst ` set (conn_to conn) \<and>
             obj  \<in> get_group_label (composition spec) `fst ` set (conn_from conn) \<and>
             auth \<in> access_to_from (connector_access (conn_type conn))
    } \<union>
    {(subj, auth, obj).
           \<exists>conn \<in> snd ` set (connections (composition spec)).
             subj \<in> fst ` set (conn_from conn) \<and>
             obj \<in> fst ` set (conn_from conn) \<and>
             subj \<noteq> obj \<and>
             auth \<in> access_from_from (connector_access (conn_type conn))
    } \<union>
    {(subj, auth, obj).
           \<exists>conn \<in> snd ` set (connections (composition spec)).
             subj \<in> fst ` set (conn_to conn) \<and>
             obj \<in> fst ` set (conn_to conn) \<and>
             subj \<noteq> obj \<and>
             auth \<in> access_to_to (connector_access (conn_type conn))
    } \<union>
    {(subj, auth, obj).
           \<exists>(conn_name, conn) \<in> set (connections (composition spec)).
             subj \<in> get_group_label (composition spec) `fst ` set (conn_from conn) \<and>
             obj = get_group_label (composition spec) conn_name \<and>
             auth \<in> access_from_conn (connector_access (conn_type conn))
    } \<union>
    {(subj, auth, obj).
           \<exists>(conn_name, conn) \<in> set (connections (composition spec)).
             subj \<in> get_group_label (composition spec) `fst ` set (conn_to conn) \<and>
             obj = get_group_label (composition spec) conn_name \<and>
             auth \<in> access_to_conn (connector_access (conn_type conn))
    } \<union>
    (\<lambda>(subj, auth, obj). (get_group_label (composition spec) subj, auth,
                          get_group_label (composition spec) obj)) `
      policy_extra spec"

end