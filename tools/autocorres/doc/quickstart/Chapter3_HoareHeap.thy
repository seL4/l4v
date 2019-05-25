(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(*<*)
theory Chapter3_HoareHeap
imports "AutoCorres.AutoCorres"
begin

external_file "swap.c"
(*>*)

subsection \<open>\texttt{swap}\<close>

text \<open>

  Here, we use AutoCorres to verify a C program that reads and writes to the heap.
  Our C function, \texttt{swap}, swaps two words in memory:

\lstinputlisting[language=C, firstline=15]{../../swap.c}

  Again, we translate the program using the C parser and AutoCorres.
\<close>

install_C_file "swap.c"
autocorres [heap_abs_syntax, ts_rules = nondet] "swap.c"
(*<*)
context swap begin
(*>*)

text \<open>
  Most heap operations in C programs consist of accessing a pointer.
  AutoCorres abstracts the global C heap by creating one heap for
  each type. (In our simple \texttt{swap} example, it creates only
  a @{typ word32} heap.) This makes verification easier as long as
  the program does not access the same memory as two different types.

  There are other operations that are relevant to program verification,
  such as changing the type that occupies a given region of memory.
  AutoCorres will not abstract any functions that use these operations,
  so verifying them will be more complicated (but still possible).
\<close>

text \<open>
  The C parser expresses \texttt{swap} like this:
\<close>

thm swap_body_def
text \<open>@{thm [display] swap_body_def}\<close>

text \<open>
  AutoCorres abstracts the function to this:
\<close>

thm swap'_def
text \<open>@{thm [display] swap'_def }\<close>

text \<open>
  There are some things to note:

  The function contains guards (assertions) that the pointers
  \texttt{a} and \texttt{b} are valid. We need to prove that
  these guards never fail when verifying \texttt{swap}.
  Conversely, when verifying any function that calls
  \texttt{swap}, we need to show that the arguments are
  valid pointers.

  We saw a monadic program in the previous section, but here
  the monad is actually being used to carry the program heap.
\<close>

(* FIXME: something about heap syntax here. *)

text \<open>
  Now we prove that \texttt{swap} is correct. We use @{term x}
  and @{term y} to ``remember'' the initial values so that we can
  talk about them in the postcondition.
\<close>
lemma "\<lbrace> \<lambda>s. is_valid_w32 s a \<and> s[a] = x \<and> is_valid_w32 s b \<and> s[b] = y \<rbrace>
         swap' a b
       \<lbrace> \<lambda>_ s. s[a] = y \<and> s[b] = x \<rbrace>!"
  apply (unfold swap'_def)
  apply wp
  apply clarsimp
  txt \<open>
    The C parser and AutoCorres both model the C heap using functions,
    which takes a pointer to some object in memory. Heap updates are
    modelled using the functional update @{term fun_upd}:

      @{thm [display] fun_upd_def}

    To reason about functional updates, we use the rule fun\_upd\_apply.
\<close>
  apply (simp add: fun_upd_apply)
  done

text \<open>
  Note that we have ``only'' proved that the function swaps its
  arguments. We have not proved that it does \emph{not} change
  any other state. This is a typical \emph{frame problem} with
  pointer reasoning. We can prove a more complete specification
  of \texttt{swap}:
\<close>
lemma "(\<And>x y s. P (s[a := x][b := y]) = P s) \<Longrightarrow>
       \<lbrace> \<lambda>s. is_valid_w32 s a \<and> s[a] = x \<and> is_valid_w32 s b \<and> s[b] = y \<and> P s \<rbrace>
         swap' a b
       \<lbrace> \<lambda>_ s. s[a] = y \<and> s[b] = x \<and> P s \<rbrace>!"
  apply (unfold swap'_def)
  apply wp
  apply (clarsimp simp: fun_upd_apply)
  done

text \<open>
  In other words, if predicate @{term P} does not depend on the
  inputs to \texttt{swap}, it will continue to hold.

  \emph{Separation logic} provides a more structured approach
  to this problem.
\<close>

(*<*)
end
end
(*>*)
