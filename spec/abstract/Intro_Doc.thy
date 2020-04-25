(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Documentation file, introduction to the abstract specification.
*)

chapter "Introduction"

(*<*)
theory Intro_Doc
imports Main
begin
(*>*)
text \<open>

The seL4 microkernel is an operating system kernel designed to be a
secure, safe, and reliable foundation for systems in a wide variety of
application domains. As a microkernel, seL4 provides a minimal number of
services to applications. This small number of services directly
translates to a small implementation of approximately $8700$ lines of C code,
which has allowed the kernel to be formally proven in the Isabelle/HOL
theorem prover to adhere to a formal specification.

This document gives the text version of the formal Isabelle/HOL
specification used in this proof. The document starts by giving a brief
overview of the seL4 microkernel design, followed by text generated from
the Isabelle/HOL definitions.

This document is not a user manual to seL4, nor is it intended to
be read as such. Instead, it is a precise reference to the
behaviour of the seL4 kernel.

Further information on the models and verification techniques
can be found in previous publications~\cite{Boyton_09,Cock_08,Cock_KS_08,Derrin_EKCC_06,Elkaduwe_GE_07,Elkaduwe_GE_08,Elphinstone_KDRH_07,Heiser_EKKP_07,Klein_09,Klein_DE_09,Klein_EHACDEEKNSTW_09,Klein_EHACDEEKNSTW_10,Tuch_08,Tuch_09,Tuch_KH_05,Tuch_KN_07,Tuch_Klein_05,Tuch:phd,Winwood_KSACN_09}.


\section{The seL4 Microkernel}

The seL4 microkernel is a small operating system kernel of the L4
family. SeL4 provides a minimal number of services to applications, such
as abstractions for virtual address spaces, threads, inter-process
communication (IPC).

SeL4 uses a capability-based access-control model. All memory, devices,
and microkernel-provided services require an associated
\emph{capability} (access right) to utilise them
\cite{Dennis_VanHorn_66}. The set of capabilities an application
possesses determines what resources that application can directly
access. SeL4 enforces this access control by using the hardware's memory
management unit (MMU) to ensure that userspace applications only have
access to memory they possess capabilities to.

\autoref{fig:sample} shows a representative seL4-based system. It
depicts the microkernel executing on top of the hardware as the only
software running in privileged mode of the processor. The first
application to execute is the supervisor OS. The supervisor OS (also
termed a \emph{booter} for simple scenarios) is responsible for
initialising, configuring and delegating authority to the specific
system layered on top.

\begin{figure}[tb]
  \centering
  \includegraphics[width=6cm]{imgs/seL4-background_01}
  \caption{Sample seL4 based system}
  \label{fig:sample}
\end{figure}

In \autoref{fig:sample}, the example system set up by the supervisor consists
of an instance of Linux on the left, and several instances of trusted or
sensitive applications on the right. The group of applications on the left and
the group on the right are unable to directly communicate or interfere with
each other without explicit involvement of the supervisor (and the
microkernel) --- a barrier is thus created between the untrusted left and the
trusted right, as indicated in the figure. The supervisor has a
kernel-provided mechanism to determine the relationship between applications
and the presence or absence of any such barriers.

\subsection{Kernel Services}
\label{s:kernel_services}

A limited number of service primitives are provided by the
microkernel; more complex services may be implemented as applications
on top of these primitives. In this way, the functionality of the
system can be extended without increasing the code and complexity in
privileged mode, while still supporting a potentially wide number of
services for varied application domains.

The basic services the microkernel provides are as follows:
\begin{description}
\item[Threads] are an abstraction of CPU execution that support running
  software;
\item[Address Spaces] are virtual memory spaces that each contain an
  application. Applications are limited to accessing memory in their
  address space;
\item[Interprocess Communication] (IPC) via \emph{endpoints} allows
threads to communicate using message passing;
\item[Device Primitives] allow device drivers to be implemented as unprivileged
  applications.  The kernel exports hardware device interrupts
  via IPC messages; and
\item[Capability Spaces] store capabilities (i.e., access rights) to kernel services along
with their book-keeping information.
\end{description}

All kernel services are accessed using kernel-provided system calls
that \emph{invoke} a capability;
the semantics of the system call depends upon the type of the
capability invoked.  For example, invoking the \meth{Call} system call on a
thread control block (TCB) with certain arguments will suspend the
target thread, while invoking \meth{Call} on an endpoint will result
in a message being sent.  In general, the message sent to a capability
will have an entry indicating the desired operation, along with any
arguments.

The kernel provides to clients the following system calls:
\begin{description}
\item[\meth{Send}] delivers the system call arguments to the target object
and allows the application to continue. If the
target object is unable to receive and/or process the arguments
immediately, the sending application will be blocked until the arguments
can be delivered.

\item[\meth{NBSend}] performs non-blocking send in a similar fashion
to \meth{Send} except that if the object is unable to receive the
arguments immediately, the message is silently dropped.

\item[\meth{Call}] is a \meth{Send} that blocks the application until the
object provides a response, or the receiving application replies. In
the case of delivery to an application (via an \obj{Endpoint}), an
additional capability is added to the arguments and delivered to the
receiver to give it the right to respond to the sender.

\item[\meth{Recv}] is used by an application to block until the target
object is ready.

\item[\meth{Reply}] is used to respond to a \meth{Call}, using the
capability generated by the \meth{Call} operation.

\item[\meth{ReplyRecv}] is a combination of \meth{Reply} and
\meth{Recv}. It exists for efficiency reasons: the common case of
replying to a request and waiting for the next can be performed in a
single kernel system call instead of two.
\end{description}

\subsection{Capability-based Access Control}
\label{s:sel4_cap_access_control}


The seL4 microkernel provides a capability-based access control model.
Access control governs all kernel services; in order to perform any
system call, an application must invoke a capability in its possession
that has sufficient access rights for the requested service.  With
this, the system can be configured to isolate software components from
each other, and also to enable authorised controlled communication
between components by selectively granting specific communication
capabilities.  This enables software component isolation with a high
degree of assurance, as only those operations explicitly authorised by
capability possession are permitted.

A capability is an unforgeable token that references a specific kernel
object (such as a thread control block) and carries access
rights that control what operations may be performed when it is invoked.
Conceptually, a capability resides in an application's
\emph{capability space}; an address in this space refers to a
\emph{slot} which may or may not contain a capability.  An application
may refer to a capability --- to request a kernel service, for example
--- using the address of the slot holding that capability.  The seL4
capability model is an instance of a \emph{segregated} (or
\emph{partitioned}) capability
model, where capabilities are managed by the kernel.

Capability spaces are implemented as a directed graph of kernel-managed
\emph{capability nodes} (\obj{CNode}s).  A \obj{CNode} is a table of
slots, where each slot may contain further \obj{CNode} capabilities.
An address in a capability space is then the concatenation of the
indices of the \obj{CNode} capabilities forming the path to the
destination slot; we discuss \obj{CNode} objects further in
\autoref{s:cnode_obj}.

Capabilities can be copied and moved within capability spaces, and
also sent via IPC. This allows creation of applications with specific
access rights, the delegation of authority to another application, and
passing to an application authority to a newly created (or selected)
kernel service. Furthermore, capabilities can be \emph{minted} to
create a derived capability with a subset of the rights of the
original capability (never with more rights). A newly minted
capability can be used for partial delegation of authority.

Capabilities can also be revoked in their entirety to withdraw
authority. Revocation includes any capabilities that may have
been derived from the original capabilities. The propagation of
capabilities through the system is controlled by a
\emph{take-grant}-based model~\cite{Elkaduwe_GE_07}.

\subsection{Kernel Objects}
\label{s:sel4_internals}

In this section we give a brief overview of the kernel implemented
objects that can be invoked by applications. The interface to these
objects forms the interface to the kernel itself. The creation and use
of the high-level kernel services is achieved by the creation,
manipulation, and combination of these kernel objects.

\subsubsection{\obj{CNodes}}
\label{s:cnode_obj}

As mentioned in the previous section, capabilities in seL4 are stored
in kernel objects called \obj{CNodes}. A \obj{CNode} has a fixed
number of slots, always a power of two, determined when the
\obj{CNode} is created. Slots can be empty or contain a capability.

\begin{figure}[htb]
  \centering
  \includegraphics[height=5cm]{imgs/sel4objects_01.pdf}
  \caption{\obj{CNodes} forming a \obj{CSpace}}
  \label{fig:cnode}
\end{figure}


\obj{CNodes} have the following operations:
\begin{description}
\item[\meth{Mint}] creates a new capability in a specified \obj{CNode} slot
from an existing capability.  The newly created capability may have fewer rights than the original.
\item[\meth{Copy}] is similar to \meth{Mint}, but the newly created capability
  has the same rights as the original.
\item[\meth{Move}] moves a capability between two specified capability slots.
\item[\meth{Mutate}] is an atomic combination of \meth{Move} and
  \meth{Mint}. It is a performance optimisation.
\item[\meth{Rotate}] moves two capabilities between three specified
  capability slots. It is essentially two \meth{Move} operations: one
  from the second specified slot to the first, and one from the third
  to the second. The first and third specified slots may be the same,
  in which case the capability in it is swapped with the capability in
  the second slot. The operation is atomic; either both or neither capabilities
  are moved.
\item[\meth{Delete}] removes a capability from the specified slot.
\item[\meth{Revoke}] is equivalent to calling \meth{Delete} on each
  derived child of the specified capability. It has no effect on the
  capability itself.
\item[\meth{SaveCaller}] moves a kernel-generated reply capability of the
  current thread from the special \obj{TCB} slot it was created in, into
  the designated \obj{CSpace} slot.
\item[\meth{Recycle}] is equivalent to \meth{Revoke}, except that it
  also resets most aspects of the object to its initial state.
\end{description}

\subsubsection{IPC Endpoints and Notifications}

The seL4 microkernel supports \emph{synchronous} IPC (\obj{EP}) endpoints,
used to facilitate
interprocess communication between threads. Capabilities to endpoints
can be restricted to be send-only or receive-only. They can also
specify whether capabilities can be passed through the endpoint.

Endpoints allow both data and capabilities to be
transferred between threads, depending on the rights on the endpoint
capability.  Sending a message will block the sender until the message
has been received; similarly, a waiting thread will be blocked until a
message is available (but see \meth{NBSend} above).

When only notification of an event is required, notification objects can
be used. These have the following invocations:
%
\begin{description}
\item[\meth{Notify}] simply sets the given set of semaphore bits in the
notification object.
Multiple \meth{Notify} system calls without an intervening \meth{Recv}
result in the bits being ``or-ed'' with any bits already set. As such,
\meth{Notify} is always non-blocking, and has no indication of whether
a receiver has received the notification.
\end{description}
%
Additionally, the \meth{Recv} system call may be used with an
notification object, allowing the calling thread to retrieve all set
bits from the notification object. By default, if no \meth{Notify}
operations have taken place since the last \meth{Recv} call, the
calling thread will block until the next \meth{Notify} takes place.
There is also a non-blocking (polling) variant of this invocaction.

\subsubsection{\obj{TCB}}

The \emph{thread control block} (\obj{TCB}) object represents a thread
of execution in seL4. Threads are the unit of execution that is
scheduled, blocked, unblocked, etc., depending on the applications
interaction with other threads.

As illustrated in
\autoref{fig:sel4_internals}, a thread needs both a \obj{CSpace} and a
\obj{VSpace} in which to execute to form an application (plus some
additional information not represented here). The \obj{CSpace}
provides the capabilities (authority) required to manipulated kernel
objects, in order to send messages to another application for example. The
\obj{VSpace} provides the virtual memory environment required to
contain the code and data of the application. A \obj{CSpace} is
associated with a thread by installing a capability to the root
\obj{CNode} of a \obj{CSpace} into the \obj{TCB}. Likewise, a
\obj{VSpace} is associated with a thread by installing a capability to
a \obj{Page Directory} (described shortly) into the \obj{TCB}. Note that multiple threads
can share the same \obj{CSpace} and \obj{VSpace}.

\begin{figure}[htb]
  \centering
  \includegraphics[width=0.8\textwidth]{imgs/sel4_internals_01}
  \caption{Internal representation of an application in seL4}
  \label{fig:sel4_internals}
\end{figure}

The TCB object has the following methods:

\begin{description}
\item[\meth{CopyRegisters}] is used for copying the state of a
  thread. The method is given an additional capability argument, which
  must refer to a \obj{TCB} that will be used as the source of the
  transfer; the invoked thread is the destination. The caller may
  select which of several subsets of the register context will be
  transferred between the threads. The operation may also suspend the
  source thread, and resume the destination thread.

  Two subsets of the context that might be copied (if indicated by the
  caller) include: firstly, the parts of the register state that are used or preserved
  by system calls, including the instruction and stack pointers, and
  the argument and message registers; and secondly, the
  remaining integer registers. Other subsets are architecture-defined,
  and typically include coprocessor registers such as the floating
  point registers.  Note that many integer registers are modified or
  destroyed by system calls, so it is not generally useful to use
  \meth{CopyRegisters} to copy integer registers to or from the
  current thread.
\item[\meth{ReadRegisters}] is a variant of \meth{CopyRegisters} for
  which the destination is the calling thread. It uses the message
  registers to transfer the two subsets of the integer registers; the
  message format has the more commonly transferred instruction
  pointer, stack pointer and argument registers at the start, and will
  be truncated at the caller's request if the other registers are not
  required.
\item[\meth{WriteRegisters}] is a variant of \meth{CopyRegisters} for
  which the source is the calling thread. It uses the message
  registers to transfer the integer registers, in the same order used
  by \meth{ReadRegisters}. It may be truncated if the later registers
  are not required; an explicit length argument is given to allow
  error detection when the message is inadvertently truncated by a
  missing IPC buffer.
\item[\meth{SetPriority}] configures the thread's scheduling
  parameters. In the current version of seL4, this is simply a
  priority for the round-robin scheduler.
\item[\meth{SetIPCBuffer}] configures the thread's local storage,
  particularly the IPC buffer used for sending parts of the message
  payload that don't fit in hardware registers.
\item[\meth{SetSpace}] configures the thread's virtual memory and
  capability address spaces. It sets the roots of the trees (or other
  architecture-specific page table structures) that represent the two
  address spaces, and also nominates the \obj{Endpoint} that the kernel uses
  to notify the thread's pager\footnote{A \emph{pager} is a term for a
    thread that manages the \obj{VSpace} of another application. For
    example, Linux would be called the pager of its applications.} of
  faults and exceptions.
\item[\meth{Configure}] is a batched version of the three
  configuration system calls: \meth{SetPriority}, \meth{SetIPCBuffer},
  and \meth{SetSpace}. \meth{Configure} is simply a performance
  optimisation.
\item[\meth{Suspend}] makes a thread inactive. The thread will not
  be scheduled again until a \meth{Resume} operation is performed on
  it.  A \meth{CopyRegisters} or \meth{ReadRegisters} operation may
  optionally include a \meth{Suspend} operation on the source thread.
\item[\meth{Resume}] resumes execution of a thread that is
  inactive or waiting for a kernel operation to complete. If the
  invoked thread is waiting for a kernel operation, \meth{Resume} will
  modify the thread's state so that it will attempt to perform the
  faulting or aborted operation again. \meth{Resume}-ing a thread that
  is already ready has no effect. \meth{Resume}-ing a thread that is
  in the waiting phase of a \meth{Call} operation may cause the
  sending phase to be performed again, even if it has previously
  succeeded.

  A \meth{CopyRegisters} or \meth{WriteRegisters} operation may
  optionally include a \meth{Resume} operation on the destination
  thread.
\end{description}

\subsubsection{Virtual Memory}

A virtual address space in seL4 is called a \obj{VSpace}. In a similar
way to \obj{CSpaces}, a \obj{VSpace} is composed of objects provided
by the microkernel. Unlike \obj{CSpaces}, these objects for managing
virtual memory largely directly correspond to those of the hardware,
that is, a page directory pointing to page tables, which in turn map
physical frames.  The kernel also includes \obj{ASID Pool} and
\obj{ASID Control} objects for tracking the status of address spaces.

\autoref{fig:vspace} illustrates a \obj{VSpace} with the requisite
components required to implement a virtual address space.

\begin{figure}[htb]
  \centering
   \includegraphics[height=5cm]{imgs/sel4objects_05.pdf}
  \caption{Virtual Memory in seL4.}
  \label{fig:vspace}
\end{figure}

These \obj{VSpace}-related objects are sufficient to implement the
hardware data structures required to create, manipulate, and destroy
virtual memory address spaces. It should be noted that, as usual, the
manipulator of a virtual memory space needs the appropriate
capabilities to the required objects.

\paragraph{\obj{Page Directory}}

The \obj{Page Directory} (PD) is the top-level page table of the ARM
two-level page table structure. It has a hardware defined format, but
conceptually contains 1024 page directory entries (PDE), which are one
of a pointer to a page table, a 4 megabyte \obj{Page}, or an invalid
entry . The \obj{Page Directory} has no methods itself, but it is used
as an argument to several other virtual memory related object calls.

\paragraph{\obj{Page Table}} The \obj{Page Table} object forms the
second level of the ARM page table. It contains 1024 slots, each of which
contains a page table entry (PTE). A page table entry contains either an
invalid entry, or a pointer to a 4 kilobyte \obj{Page}.

\obj{Page Table} objects possess only a single method:
\begin{description}
\item[\meth{Map}] takes a \obj{Page Directory}
  capability as an argument, and installs a reference to the invoked
  \obj{Page Table} to a specified slot in the \obj{Page
    Directory}.
\end{description}

\paragraph{\obj{Page}}

A \obj{Page} object is a region of physical memory that is used to
implement virtual memory pages in a virtual address space. The
\obj{Page} object has the following methods:
\begin{description}
\item[\meth{Map}] takes a
  \obj{Page Directory} or a \obj{Page Table} capability as an argument
  and installs a PDE or PTE referring to the \obj{Page} in the
  specified location, respectively. In addition, \meth{Map} has a
  remapping mode which is used to change the access permissions on an
  existing mapping.
\item[\meth{Unmap}] removes an existing mapping.
\end{description}

\paragraph{\obj{ASID Control}}

For internal kernel book-keeping purposes, there is a fixed maximum
number of applications the system can support.  In order to manage
this limited resource, the microkernel provides an \obj{ASID Control}
capability. The \obj{ASID Control} capability is used to generate a
capability that authorises the use of a subset of available address
space identifiers. This newly created capability is called an
\obj{ASID Pool}. \obj{ASID Control} only has a single method:
\begin{description}
\item[\meth{MakePool}] together with a capability to
\obj{Untyped Memory} (described shortly) as argument creates an \obj{ASID Pool}.
\end{description}

\paragraph{\obj{ASID Pool}}

An \obj{ASID Pool} confers the right to create a subset of the available
maximum applications. For a \obj{VSpace} to be usable by an application, it
must be assigned to an ASID. This is done using a capability to an
\obj{ASID Pool}. The \obj{ASID Pool} object has a single method:
\begin{description}
\item[\meth{Assign}] assigns an ASID to the \obj{VSpace}
  associated with the \obj{Page Directory} passed in as an argument.
\end{description}

\subsubsection{Interrupt Objects}

Device driver applications need the ability to receive and acknowledge
interrupts from hardware devices.

A capability to \obj{IRQControl} has the ability to create a new
capability to manage a specific interrupt source associated with a
specific device. The new capability is then delegated to a device
driver to access an interrupt source. \obj{IRQControl} has one method:
\begin{description}
\item[\meth{Get}] creates an \obj{IRQHandler} capability for the
  specified interrupt source.
\end{description}

An \obj{IRQHandler} object is used by driver application to handle
interrupts for the device it manages. It has three methods:
\begin{description}
\item[\meth{SetEndpoint}] specifies the \obj{NTFN} that a
  \meth{Notify} should be sent to when an interrupt occurs. The driver
  application usually \meth{Recv}-s on this endpoint for interrupts to
  process.
\item[\meth{Ack}] informs the kernel that the userspace driver has finished
  processing the interrupt and the microkernel can send further pending
  or new interrupts to the application.
\item[\meth{Clear}] de-registers the \obj{NTFN} from the
  \obj{IRQHandler} object.
\end{description}

\subsubsection{\obj{Untyped Memory}}

The \obj{Untyped Memory} object is the foundation of memory allocation
in the seL4 kernel.  Untyped memory capabilities have a single method:
\begin{description}
 \item[\meth{Retype}] creates a number of new kernel objects.  If this
method succeeds, it returns capabilities to the newly-created objects.
\end{description}

In particular, untyped memory objects can be divided into a group of
smaller untyped memory objects.  We discuss memory management in
general in the following section.

\subsection{Kernel Memory Allocation}
\label{sec:kernmemalloc}

The seL4 microkernel has no internal memory allocator: all kernel
objects must be explicitly created from application controlled memory
regions via \obj{Untyped Memory} capabilities.  Applications must have
explicit authority to memory (via \obj{Untyped Memory} capabilities)
in order to create other services, and services consume no extra
memory once created (other than the amount of untyped memory from
which they were originally created). The mechanisms can be used to
precisely control the specific amount of physical memory available to
applications, including being able to enforce isolation of physical
memory access between applications or a device.  Thus, there are no
arbitrary resource limits in the kernel apart from those dictated by
the hardware\footnote{The treatment of virtual ASIDs imposes a fixed
number of address spaces, but this limitation is to be removed in
future versions of seL4.}, and so many denial-of-service attacks via
resource exhaustion are obviated.

At boot time, seL4 pre-allocates all the memory required for the
kernel itself, including the code, data, and stack sections (seL4 is a
single kernel-stack operating system). The remainder of the memory is
given to the first task in the form of capabilities to \obj{Untyped
Memory}, and some additional capabilities to kernel objects that were
required to bootstrap the supervisor task.  These objects can then be
split into smaller untyped memory regions or other kernel objects
using the \meth{Retype} method; the created objects are termed
\emph{children} of the original untyped memory object.

See \autoref{fig:alloc2} for an
example.

\begin{figure}[htb]
  \centering
   \includegraphics[width=7cm]{imgs/seL4-background_03}
  \caption{Memory layout at boot time}
  \label{fig:alloc2}
\end{figure}

\begin{figure}[htb]
  \centering
  \includegraphics[width=7cm]{imgs/seL4-background_04}
  \caption{Memory layout after supervisor creates kernel services.}
  \label{fig:alloc-sup}
\end{figure}

The user-level application that creates an object using \meth{Retype}
receives full authority over the resulting object. It can then
delegate all or part of the authority it possesses over this object to
one or more of its clients.  This is done by selectively granting each
client a capability to the kernel object, thereby allowing the client
to obtain kernel services by invoking the object.

For obvious security reasons, kernel data must be protected from user
access.  The seL4 kernel prevents such access by using two mechanisms.
First, the above allocation policy guarantees that typed objects never
overlap.  Second, the kernel ensures that each physical frame mapped
by the MMU at a user-accessible address corresponds to a
\obj{Page} object (described above); \obj{Page} objects contain no kernel
data, so direct
user access to kernel data is not possible. All other kernel objects
are only indirectly manipulated via their corresponding capabilities.

\subsubsection{Re-using Memory}
\label{s:memRevoke}

The model described thus far is sufficient for applications to
allocate kernel objects, distribute authority among client
applications, and obtain various kernel services provided by these
objects.  This alone is sufficient for a simple static system
configuration.

The seL4 kernel also allows memory re-use.  Reusing a region of memory
is sound only when there are no dangling references (e.g.\
capabilities) left to the objects implemented by that memory.  The
kernel tracks \emph{capability derivations}, that is, the children
generated by various \obj{CNode} methods (\meth{Retype}, \meth{Mint},
\meth{Copy}, and \meth{Mutate}).  Whenever a user requests that the
kernel create new objects in an untyped memory region, the kernel uses
this information to check that there are no children in the region,
and thus no live capability references.

The tree structure so generated is termed the \emph{capability
derivation tree} (CDT)\footnote{Although we model the CDT as a
separate data structure, it is implemented as part of the CNode object
and so requires no additional kernel meta-data.}.  For example, when a
user creates new kernel objects by retyping untyped memory, the newly
created capabilities would be inserted into the CDT as children of the
untyped memory capability.

Finally, recall that the \meth{Revoke} operation destroys all
capabilities derived from the argument capability.  Revoking the last
capability to a kernel object is easily detectable, and triggers the
\emph{destroy} operation on the now unreferenced object. Destroy
simply deactivates the object if it was active, and cleans up any
in-kernel dependencies between it and other objects.

By calling \meth{Revoke} on the original
capability to an untyped memory object, the user removes all of the
untyped memory object's children --- that is, all capabilities pointing to
objects in the untyped memory region.
Thus, after this operation there are no valid references
to any object within the untyped region, and the region may be
safely retyped and reused.

\section{Summary}
\label{s:backsum}

This chapter has given an overview of the seL4 microkernel. The
following chapters are generated from the formal Isabelle/HOL
definitions that comprise the formal specification of the seL4 kernel
on the ARM11 architecture. The specification does not cover any other
architectures or platforms.

The order of definitions in this document is as processed by
Isabelle/HOL: bottom up. All concepts are defined before first used.
This means the first chapters mainly introduce basic data types and
structures while the top-level kernel entry point is defined in the
last chapter (\autoref{c:syscall}). The following section shows
the dependency graph between the theory modules in this specification.
We assume a familiarity with Isabelle syntax; see Nipkow et
al.~\cite{LNCS2283} for an introduction. In addition to the standard
Isabelle/HOL notation, we sometimes write @{text "f $ x"} for
@{text "(f x)"} and use monadic do-notation extensively. The latter
is defined in \autoref{c:monads}.

\section{Theory Dependencies}

\centerline{\includegraphics[height=0.8\textheight]{session_graph}}

\<close>
(*<*)
end
(*>*)
