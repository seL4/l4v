(*
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

chapter "SchedContexts"

theory SchedContext_H

imports
  SchedContextDecls_H
  TCBDecls_H
  ThreadDecls_H
  NotificationDecls_H
  ReplyDecls_H
  VSpace_H

begin

context begin interpretation Arch .
requalify_consts
  kernelWCET_ticks
  kernelWCET_us
  ticks_to_us
  max_ticks_to_us
  getCurrentTime
end

#INCLUDE_HASKELL SEL4/Object/SchedContext.lhs bodies_only ONLY scheduleUsed mergeRefill canMergeRefill

fun
  refillsMergePrefix :: "refill list \<Rightarrow> refill list"
where
  "refillsMergePrefix [] = []"
| "refillsMergePrefix [r] = [r]"
| "refillsMergePrefix (r1 # r2 # rs) =
     (if canMergeRefill r1 r2
      then refillsMergePrefix (mergeRefill r1 r2 # rs)
      else r1 # r2 # rs)"

fun
  minBudgetMerge :: "bool \<Rightarrow> refill list \<Rightarrow> refill list"
where
  "minBudgetMerge _ [] = []"
| "minBudgetMerge _ [r] = [r]"
| "minBudgetMerge full (r0#r1#rs) = (if (rAmount r0 < minBudget \<or> full)
     then minBudgetMerge False (r1\<lparr> rAmount := rAmount r1 + rAmount r0 \<rparr> # rs)
     else (r0#r1#rs))"

function
  refillsBudgetCheck :: "ticks \<Rightarrow> ticks \<Rightarrow> refill list \<Rightarrow> ticks \<times> refill list"
where
  "refillsBudgetCheck period usage [] = (usage, [])"
| "refillsBudgetCheck period usage (r#rs) = (if rAmount r \<le> usage \<and> 0 < rAmount r
     then refillsBudgetCheck period (usage - rAmount r)
                                         (scheduleUsed rs (r\<lparr>rTime := rTime r + period\<rparr>))
     else (usage, r#rs))"
  by pat_completeness auto

#INCLUDE_HASKELL SEL4/Object/SchedContext.lhs bodies_only NOT scheduleUsed mergeRefill canMergeRefill refillsMergePrefix minBudgetMerge refillsBudgetCheck

end
