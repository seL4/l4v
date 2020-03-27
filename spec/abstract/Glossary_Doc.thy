(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Glossary. Documentation only.



This file is a running glossary of technical nouns used in
documenting the abstract model.

The entries should be listed alphabetically.
Each has three details:
   1. a short name, e.g. cnode
   2. a long name, e.g. capability node
   3. a reference to the section where it is first discussed.

The long name (2) should only be used when the term is first
discussed, i.e. at (3).
It should be followed by the short name (1) in parantheses and a
label command of the form: \label{glos:<shortname>}.
That label should be used to generate the reference (3).

e.g. A \emph{capability node} (cnode)\label{glos:cnode} is a ...

A fourth optional argument can give additional information of one
or more of the following types:
   - names that should not be used.
   - a list of historical terms that mean the same thing.
*)

chapter "Glossary"

(*<*)

theory Glossary_Doc
imports "Syscall_A"
begin

(*>*)
text \<open>
\newcommand{\glossaryentry}[4][\null]
    {\begin{list}{\null}{\setlength{\leftmargin}{0pt}
                         \setlength{\rightmargin}{0pt}
                         \setlength{\labelwidth}{0pt}
                         \setlength{\itemindent}{0pt}
                         \setlength{\topsep}{1.0em}}
     \item  \parbox[t]{.18\textwidth}{\raggedright{\bf #2}}%
            \hfill\parbox[t]{.75\textwidth}{\raggedright{#3}}%
            \hfill\parbox[t]{.05\textwidth}{\raggedright{%\autoref{#4}
}}%
     \ifx#1\null\relax\else%
        \item\nopagebreak\hfill
             \begin{minipage}[t]{.775\textwidth}{\it #1}\end{minipage}
     \fi
     \end{list}}

\glossaryentry
  {ntfn, Notification}
  {A \emph{notification} object. A kernel object in seL4 consisting
  of a set of binary semaphores, used for sending (signalling)
  notifications to other threads.}
  {glos:ntfn}

\glossaryentry
  {asid, asid pool}
  {Address Space Identifier. ASIDs are associated with page
  directories (PDs) and define the virtual address space of a
  thread. Multiple threads may be in the same address space.
  Since ARM hardware supports only 255 different ASIDs, seL4 on ARM
  supports the concept of virtual ASIDs that are mapped to hardware ASIDS
  managed in a two-level structure. The user manages only the second
  level of this structure: the asid pool. An asid pool can be seen as
  a set of virtual ASIDs that can be connected to and disconnected from
  page directories.}
  {}


\glossaryentry
  {badge}
  {A badge is a piece of extra information stored in an endpoint
  capability. It can be used by applications to identify caps
  previously handed out to clients.}
  {glos:badge}

\glossaryentry
  {cap, capability}
  {The main access control concept in seL4. A capability conceptually
  is a reference to a kernel object together with a set of access
  rights. Most seL4 capabilities store additional bits of
  information. Some of this additional information may be
  exposed to the user, but the bulk of it is kernel-internal
  book-keeping information. Capabilities are stored in CNodes and
  TCBs.}
  {glos:cap}

\glossaryentry
  {cdt}
  {Capability Derivation Tree. A kernel-internal data structure that
  tracks the child/parent relationship between capabilities. Capabilities
  to new objects are children of the Untyped capability the object was
  created from. Capabilities can also be copied; in this case the user may
  specify if the operation should produce children or siblings of
  the source capability. The revoke operation will delete all children
  of the invoked capability.}
  {}

\glossaryentry
  {cnode}
  {Capability Node. Kernel-controlled storage that holds capabilities.
   Capability nodes can be created in different sizes and be shared
   between CSpaces. CNodes can be pointed to by capabilities themselves.}
  {glos:cnode}

\glossaryentry
  {cspace}
  {A directed graph of CNodes. The CSpace of a thread defines the set
  of capabilities it has access to. The root of the graph is the CNode
  capability in the CSpace slot of the thread. The edges of the graph
  are the CNode capabilities residing in the CNodes spanned by this root.}
  {glos:cspace}

\glossaryentry
  {cptr}
  {Capability Pointer. A user-level reference to a capability,
  relative to a specified root CNode or the thread's CSpace root. In
  this specification, a user-level capability pointer is a sequence of
  bits that define a path in the CSpace graph that should end in a
  capability slot. The kernel resolves user-level capability pointers
  into capability slot pointers (cslot\_ptr).}
  {glos:cptr}

\glossaryentry
  {cslot\_ptr}
  {Capability Slot Pointer. A kernel-internal reference to a capability. It
  identifies the kernel object the capability resides in as well as
  the location (slot) of the capability inside this object. }
  {glos:cptr}

\glossaryentry
  {ep}
  {Endpoint. Without further qualifier refers to a synchronous
  communications (IPC) endpoint in seL4.}
  {glos:ep}

\glossaryentry
  {guard}
  {Guard of a CNode capability. From the user's perspetive the CSpace
  of a thread is organised as a guardedage table. The kernel will
  resolve user capability pointers into internal capability slot pointers.
  The guard of one link/edge in the CSpace graph defines a sequence of bits
  that will be stripped from the user-level capability pointer before
  resolving resumes at the next CNode.}
  {}

\glossaryentry
  {ipc}
  {Inter Process Communication. In seL4: sending short synchronous messages
  between threads. To communicate via IPC in seL4, the
  receiver listens at an endpoint object and the sender sends to the
  same endpoint object. There is a separate mechanism for
  notifications between threads.}
  {}

\glossaryentry
  {kheap}
  {Kernel Heap. This is not an actual C heap in the sense that it
  supports malloc and free. Rather, it is the kernel virtual memory
  view of physical memory in the machine. }
  {}

\glossaryentry
  {pd}
  {Page Directory. The first level of an ARM virtual memory page
  table. A page directory can be seen as an array of page directory
  entries (PDEs).}
  {}

\glossaryentry
  {pde}
  {Page Directory Entry. One entry in the page directory. It either
  is invalid, contains a translation to a frame, or a translation to
  a second level page table.}
  {}

\glossaryentry
  {pt}
  {Page Table. The second level of an ARM virtual memory page
  table. It can be seen as an array of page table entries.}
  {}

\glossaryentry
  {pte}
  {Page Table Entry. One entry of a second level ARM page table. It is
  either invalid or contains a translation to a frame.}
  {}

\glossaryentry
  {replycap}
  {Reply Capability. Reply capabilities are created automatically
  in the receiver of a Call IPC. The reply capability points back
  to the sender of the call and can be used to send a reply efficiently
  without having to explicitly set up a return channel. Reply capabilities
  can be invoked only once. Internally, reply capabilities are created
  as copies of so-called Master Reply Capabilities that are always
  present in the master reply slot of the sender's TCB.}
  {}

\glossaryentry
  {tcb}
  {Thread Control Block. The kernel object that stores management data
  for threads, such as the thread's CSpace, VSpace, thread state, or user
  registers.}
  {}

\glossaryentry
  {thread}
  {The CPU execution abstraction of seL4.}
  {}

\glossaryentry
  {vm}
  {Virtual Memory. The concept of translating virutal memory addresses
  to physical frames. SeL4 uses the MMU (Memory Management Unit) to
  provide controlled virtual memory mechanisms to the user, to protect
  kernel data and code from users, and to enforce separation between
  users (if set up correctly). }
  {}

\glossaryentry
  {vspace}
  {In analogy to CSpace, the virtual memory space of a thread. In the
  ARM case, the VSpace of a thread is defined by its top-level page
  directory and that page directory's ASID.}
  {}

\glossaryentry
  {zombie}
  {Zombie Capability. This capability is not accessible to the
  user. It stores continuation information for the preemtable
  capability delete operation.}
  {}
\<close>

(*<*)
end
(*>*)
