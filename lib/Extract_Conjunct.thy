(*
 * Copyright 2017, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory Extract_Conjunct
imports
  "Main"
  "Eisbach_Methods"
begin

section \<open>Extracting conjuncts in the conclusion\<close>

text \<open>
Methods for extracting a conjunct from a nest of conjuncts in the conclusion
of a goal, typically by pattern matching.

When faced with a conclusion which is a big conjunction, it is often the case
that a small number of conjuncts require special attention, while the rest can
be solved easily by @{method clarsimp}, @{method auto} or similar. However,
sometimes the method that would solve the bulk of the conjuncts would put some
of the conjuncts into a more difficult or unsolvable state.

The higher-order methods defined here provide an efficient way to select a
conjunct requiring special treatment, so that it can be dealt with first. Once
all such conjuncts have been removed, the remaining conjuncts can all be solved
together by some automated method.

Each method takes an inner method as an argument, and selects the leftmost
conjunct for which that inner method succeeds. The methods differ according to
what they do with the selected conjunct. See below for more information and
some simple examples.
\<close>

context begin

subsection \<open>Focused conjunct with context\<close>

text \<open>
We define a predicate which allows us to identify a particular sub-tree and its
context within a nest of conjunctions. We express this sub-tree-with-context using
a function which reconstructs the original nest of conjunctions. The context
consists of a list of parent contexts, where each parent context consists of a
sibling sub-tree, and a tag indicating whether the focused sub-tree is on the left
or right. Rebuilding the original tree works from the focused sub-tree up towards
the root of the original structure. This sub-tree-with-context is sometimes known
as a zipper.
\<close>

private fun focus_conj :: "bool \<Rightarrow> bool list \<Rightarrow> bool" where
  "focus_conj current [] = current"
| "focus_conj current (sibling # parents) = focus_conj (current \<and> sibling) parents"

private definition "focus \<equiv> focus_conj"

private definition "tag t P \<equiv> P"
private lemmas focus_defs = focus_def tag_def

private abbreviation "left \<equiv> tag Left"
private abbreviation "right \<equiv> tag Right"

private lemma focus_example:
  "focus C [right B, left D, left E, right A] \<longleftrightarrow> A \<and> ((B \<and> C) \<and> D) \<and> E"
  unfolding focus_defs by auto

subsection \<open>Moving the focus\<close>

text \<open>
We now prove some rules which allow us to switch between focused and unfocused
structures, and to move the focus around. Some versions of these rules carry an
extra conjunct @{term E} outside the structure. Once we find the conjunct we want,
this @{term E} allows to keep track of it while we reassemble the rest of the
original structure.

First, we have rules for going between focused and unfocused structures.
\<close>

private lemma focus_top_iff: "E \<and> focus P [] \<longleftrightarrow> E \<and> P"
  unfolding focus_def by simp

private lemmas to_focus = focus_top_iff[where E=True, simplified, THEN iffD1]
private lemmas from_focusE = focus_top_iff[THEN iffD2]
private lemmas from_focus = from_focusE[where E=True, simplified]

text \<open>
Next, we have rules for moving the focus to and from the left conjunct.
\<close>

private lemma focus_left_iff: "E \<and> focus L (left R # P) \<longleftrightarrow> E \<and> focus (L \<and> R) P"
  unfolding focus_defs by simp

private lemmas focus_left = focus_left_iff[where E=True, simplified, THEN iffD1]
private lemmas unfocusE_left = focus_left_iff[THEN iffD2]
private lemmas unfocus_left = unfocusE_left[where E=True, simplified]

text \<open>
Next, we have rules for moving the focus to and from the right conjunct.
\<close>

private lemma focus_right_iff: "E \<and> focus R (right L # P) \<longleftrightarrow> E \<and> focus (L \<and> R) P"
  unfolding focus_defs using conj_commute by simp

private lemmas focus_right = focus_right_iff[where E=True, simplified, THEN iffD1]
private lemmas unfocusE_right = focus_right_iff[THEN iffD2]
private lemmas unfocus_right = unfocusE_right[where E=True, simplified]

text \<open>
Finally, we have rules for extracting the current focus. The sibling of the
extracted focus becomes the new focus of the remaining structure.
\<close>

private lemma extract_focus_iff: "focus C (tag t S # P) \<longleftrightarrow> (C \<and> focus S P)"
  unfolding focus_defs by (induct P arbitrary: S) auto

private lemmas extract_focus = extract_focus_iff[THEN iffD2]

subsection \<open>Primitive methods for navigating a conjunction\<close>

text \<open>
Using these rules as transitions, we implement a machine which navigates a tree
of conjunctions, searching from left to right for a conjunct for which a given
method will succeed. Once a matching conjunct is found, it is extracted, and the
remaining conjuncts are reassembled.
\<close>

text \<open>From the current focus, move to the leftmost sub-conjunct.\<close>
private method focus_leftmost = (intro focus_left)?

text \<open>Find the furthest ancestor for which the current focus is still on the right.\<close>
private method unfocus_rightmost = (intro unfocus_right)?

text \<open>Move to the immediate-right sibling.\<close>
private method focus_right_sibling = (rule unfocus_left, rule focus_right)

text \<open>Move to the next conjunct in right-to-left ordering.\<close>
private method focus_next_conjunct = (unfocus_rightmost, focus_right_sibling, focus_leftmost)

text \<open>Search from current focus toward the right until we find a matching conjunct.\<close>
private method find_match methods m = (rule extract_focus, m | focus_next_conjunct, find_match m)

text \<open>Search within nest of conjuncts, leaving remaining structure focused.\<close>
private method extract_match methods m = (rule to_focus, focus_leftmost, find_match m)

text \<open>Move all the way out of focus, keeping track of any extracted conjunct.\<close>
private method unfocusE = ((intro unfocusE_right unfocusE_left)?, rule from_focusE)
private method unfocus = ((intro unfocus_right unfocus_left)?, rule from_focus)

subsection \<open>Methods for selecting the leftmost matching conjunct\<close>

text \<open>
See the introduction at the top of this theory for motivation, and below for
some simple examples.
\<close>

text \<open>
Assuming the conclusion of the goal is a nest of conjunctions, method
@{text lift_conjunct} finds the leftmost conjunct for which the given method
succeeds, and moves it to the front of the conjunction in the goal.
\<close>
method lift_conjunct methods m = (extract_match \<open>succeeds \<open>rule conjI, m\<close>\<close>, unfocusE)

text \<open>
Method @{text extract_conjunct} finds the leftmost conjunct for which the
given method succeeds, and splits it into a fresh subgoal, leaving the remaining
conjuncts untouched in the second subgoal. It is equivalent to @{method lift_conjunct}
followed by @{method rule} @{thm conjI}.
\<close>
method extract_conjunct methods m = (extract_match \<open>rule conjI, succeeds m\<close>; unfocus?)

text \<open>
Method @{text apply_conjunct} finds the leftmost conjunct for which the given
method succeeds, leaving any subgoals created by the application of that method,
and a subgoal containing the remaining conjuncts untouched. It is equivalent to
@{method extract_conjunct} followed by the given method, but more efficient.
\<close>
method apply_conjunct methods m = (extract_match \<open>rule conjI, m\<close>; unfocus?)

subsection \<open>Examples\<close>

text \<open>
Given an inner method based on @{method match}, which only succeeds on the desired
conjunct @{term C}, @{method lift_conjunct} moves the conjunct @{term C} to the
front. The body of the @{method match} here is irrelevant, since @{method lift_conjunct}
always discards the effect of the method it is given.
\<close>
lemma "\<lbrakk> A; B; \<lbrakk> A; B; D; E \<rbrakk> \<Longrightarrow> C; D; E \<rbrakk> \<Longrightarrow> A \<and> ((B \<and> C) \<and> D) \<and> E"
  apply (lift_conjunct \<open>match conclusion in C \<Rightarrow> \<open>-\<close>\<close>)
  -- \<open>@{term C} as been moved to the front of the conclusion.\<close>
  apply (match conclusion in \<open>C \<and> A \<and> (B \<and> D) \<and> E\<close> \<Rightarrow> \<open>-\<close>)
  oops

text \<open>
Method @{method extract_conjunct} works similarly, but peels of the matched conjunct
as a separate subgoal. As for @{method lift_conjunct}, the effect of the given method
is discarded, so the body of the @{method match} is irrelevant.
\<close>
lemma "\<lbrakk> A; B; \<lbrakk> A; B; D; E \<rbrakk> \<Longrightarrow> C; D; E \<rbrakk> \<Longrightarrow> A \<and> ((B \<and> C) \<and> D) \<and> E"
  apply (extract_conjunct \<open>match conclusion in C \<Rightarrow> \<open>-\<close>\<close>)
  -- \<open>@{method extract_conjunct} gives us the matched conjunct @{term C} as a separate subgoal.\<close>
   apply (match conclusion in C \<Rightarrow> \<open>-\<close>)
   apply blast
  -- \<open>The other subgoal contains the remaining conjuncts untouched.\<close>
  apply (match conclusion in \<open>A \<and> (B \<and> D) \<and> E\<close> \<Rightarrow> \<open>-\<close>)
  oops

text \<open>
Method @{method apply_conjunct} goes one step further, and applies the given method
to the extracted subgoal.
\<close>
lemma "\<lbrakk> A; B; \<lbrakk> A; B; D; E \<rbrakk> \<Longrightarrow> C; D; E \<rbrakk> \<Longrightarrow> A \<and> ((B \<and> C) \<and> D) \<and> E"
  apply (apply_conjunct \<open>match conclusion in C \<Rightarrow> \<open>match premises in H: _ \<Rightarrow> \<open>rule H\<close>\<close>\<close>)
  -- \<open>We get four subgoals from applying the given method to the matched conjunct @{term C}.\<close>
      apply (match premises in H: A \<Rightarrow> \<open>rule H\<close>)
     apply (match premises in H: B \<Rightarrow> \<open>rule H\<close>)
    apply (match premises in H: D \<Rightarrow> \<open>rule H\<close>)
   apply (match premises in H: E \<Rightarrow> \<open>rule H\<close>)
  -- \<open>The last subgoal contains the remaining conjuncts untouched.\<close>
  apply (match conclusion in \<open>A \<and> (B \<and> D) \<and> E\<close> \<Rightarrow> \<open>-\<close>)
  oops

end

end
