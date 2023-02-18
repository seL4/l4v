(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2022, UNSW (ABN 57 195 873 197)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory SchedContext_C
imports Schedule_C
begin

context kernel_m begin

lemma refill_new_ccorres:
  "ccorres dc xfdc
     invs'
     (\<lbrace>\<acute>sc = Ptr scPtr\<rbrace>
      \<inter> \<lbrace>\<acute>max_refills = of_nat maxRefills\<rbrace>
      \<inter> \<lbrace>\<acute>budget = budget\<rbrace>
      \<inter> \<lbrace>\<acute>period = period\<rbrace>) []
     (refillNew scPtr maxRefills budget period) (Call refill_new_'proc)"
sorry (* FIXME RT: refill_new_ccorres *)

lemma refill_update_ccorres:
  "ccorres dc xfdc
     invs'
     (\<lbrace>\<acute>sc = Ptr scPtr\<rbrace>
      \<inter> \<lbrace>\<acute>new_period = newPeriod\<rbrace>
      \<inter> \<lbrace>\<acute>new_budget = newBudget\<rbrace>
      \<inter> \<lbrace>\<acute>new_max_refills = of_nat newMaxRefills\<rbrace>) []
     (refillUpdate scPtr newPeriod newBudget newMaxRefills) (Call refill_update_'proc)"
sorry (* FIXME RT: refill_update_ccorres *)

lemma decodeSchedContext_UnbindObject_ccorres:
  "ccorres dc xfdc
     invs' \<lbrace>\<acute>sc = Ptr scPtr\<rbrace> []
     (decodeSchedContext_UnbindObject scPtr excaps) (Call decodeSchedContext_UnbindObject_'proc)"
sorry (* FIXME RT: decodeSchedContext_UnbindObject_ccorres *)

lemma decodeSchedContext_Bind_ccorres:
  "ccorres dc xfdc
     invs' \<lbrace>\<acute>sc = Ptr scPtr\<rbrace> []
     (decodeSchedContext_Bind scPtr excaps) (Call decodeSchedContext_Bind_'proc)"
sorry (* FIXME RT: decodeSchedContext_Bind_ccorres *)

lemma setConsumed_ccorres:
  "ccorres dc xfdc
     invs' \<lbrace>\<acute>sc = Ptr scPtr\<rbrace> []
     (setConsumed scPtr buffer) (Call setConsumed_'proc)"
sorry (* FIXME RT: setConsumed_ccorres *)

lemma decodeSchedContext_YieldTo_ccorres:
  "ccorres dc xfdc
     invs' \<lbrace>\<acute>sc = Ptr scPtr\<rbrace> []
     (decodeSchedContext_YieldTo scPtr buffer) (Call decodeSchedContext_YieldTo_'proc)"
sorry (* FIXME RT: decodeSchedContext_YieldTo_ccorres *)

lemma decodeSchedContextInvocation_ccorres:
  "ccorres dc xfdc
     invs' \<lbrace>\<acute>sc = Ptr scPtr\<rbrace> []
     (decodeSchedContextInvocation label scPtr excaps buffer)
     (Call decodeSchedContextInvocation_'proc)"
sorry (* FIXME RT: decodeSchedContextInvocation_ccorres *)

lemma schedContext_updateConsumed_ccorres:
  "ccorres dc xfdc
     invs' \<lbrace>\<acute>sc = Ptr scPtr\<rbrace> []
     (schedContextUpdateConsumed scPtr)
     (Call schedContext_updateConsumed_'proc)"
sorry (* FIXME RT: schedContext_updateConsumed_ccorres *)

lemma schedContext_cancelYieldTo_ccorres:
  "ccorres dc xfdc
     invs' \<lbrace>\<acute>tcb = tcb_ptr_to_ctcb_ptr tptr\<rbrace> []
     (schedContextCancelYieldTo tptr)
     (Call schedContext_cancelYieldTo_'proc)"
sorry (* FIXME RT: schedContext_cancelYieldTo_ccorres *)

lemma invokeSchedControl_ConfigureFlags_ccorres:
  "ccorres dc xfdc
     invs' UNIV []
     (invokeSchedControlConfigureFlags iv)
     (Call invokeSchedControl_ConfigureFlags_'proc)"
sorry (* FIXME RT: invokeSchedControl_ConfigureFlags_ccorres *)

end

end
