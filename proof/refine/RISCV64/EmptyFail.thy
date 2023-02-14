(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory EmptyFail
imports Bits_R
begin

(* Collect empty_fail lemmas here. naming convention is emtpy_fail_NAME.
   Unless there is a good reason, they should all be [intro!, wp, simp] *)

lemma empty_fail_fun_app[intro!]:
  "empty_fail (f x) \<Longrightarrow> empty_fail (f $ x)"
  by simp

lemma empty_fail_alignCheck [intro!, wp, simp]:
  "empty_fail (alignCheck a b)"
  unfolding alignCheck_def by wpsimp

lemma empty_fail_magnitudeCheck [intro!, wp, simp]:
  "empty_fail (magnitudeCheck a b c)"
  unfolding magnitudeCheck_def by wpsimp

lemma empty_fail_loadObject_default [intro!, wp, simp]:
  shows "empty_fail (gets_the $ loadObject_default x b c d)" by wpsimp

lemma empty_fail_threadGet [intro!, wp, simp]:
  "empty_fail (threadGet f p)"
  by (wpsimp simp: threadGet_def)

lemma empty_fail_getCTE [intro!, wp, simp]:
  "empty_fail (getCTE slot)"
  by (wpsimp simp: getCTE_def getObject_def)

lemma empty_fail_updateObject_cte [intro!, wp, simp]:
  "empty_fail (updateObject (v :: cte) ko a b c)"
  by (fastforce simp: updateObject_cte typeError_def unless_def split: kernel_object.splits )

lemma empty_fail_setCTE [intro!, wp, simp]:
  "empty_fail (setCTE p cte)"
  unfolding setCTE_def
  by (fastforce simp: setObject_def split_def)

lemma empty_fail_updateCap [intro!, wp, simp]:
  "empty_fail (updateCap p f)"
  unfolding updateCap_def by auto

lemma empty_fail_updateMDB [intro!, wp, simp]:
  "empty_fail (updateMDB a b)"
  unfolding updateMDB_def Let_def by auto

lemma empty_fail_getSlotCap [intro!, wp, simp]:
  "empty_fail (getSlotCap a)"
  unfolding getSlotCap_def by fastforce

context begin interpretation Arch . (*FIXME: arch_split*)

lemma empty_fail_getObject:
  "empty_fail (getObject x :: 'a :: pspace_storable kernel)"
  apply (wpsimp simp: getObject_def split_def)
  done

lemma empty_fail_getObject_tcb [intro!, wp, simp]:
  shows "empty_fail (getObject x :: tcb kernel)"
  by (wpsimp wp: empty_fail_getObject)

lemma empty_fail_updateTrackedFreeIndex [intro!, wp, simp]:
  shows "empty_fail (updateTrackedFreeIndex p idx)"
  by (fastforce simp add: updateTrackedFreeIndex_def)

lemma empty_fail_updateNewFreeIndex [intro!, wp, simp]:
  shows "empty_fail (updateNewFreeIndex p)"
  apply (simp add: updateNewFreeIndex_def)
  apply safe
  apply (simp split: capability.split)
  done

lemma empty_fail_insertNewCap [intro!, wp, simp]:
  "empty_fail (insertNewCap p p' cap)"
  unfolding insertNewCap_def by fastforce

lemma empty_fail_getIRQSlot [intro!, wp, simp]:
  "empty_fail (getIRQSlot irq)"
  by (fastforce simp: getIRQSlot_def getInterruptState_def locateSlot_conv)

lemma empty_fail_getObject_ntfn [intro!, wp, simp]:
  "empty_fail (getObject p :: Structures_H.notification kernel)"
  by (wpsimp wp: empty_fail_getObject)

lemma empty_fail_getNotification [intro!, wp, simp]:
  "empty_fail (getNotification ep)"
  by (simp add: getNotification_def)

lemma empty_fail_lookupIPCBuffer [intro!, wp, simp]:
  "empty_fail (lookupIPCBuffer a b)"
  by (clarsimp simp: lookupIPCBuffer_def Let_def getThreadBufferSlot_def locateSlot_conv
              split: capability.splits arch_capability.splits | wp | wpc | safe)+

lemma empty_fail_updateObject_default [intro!, wp, simp]:
  "empty_fail (updateObject_default v ko a b c)"
  by (wpsimp simp: updateObject_default_def)

lemma empty_fail_threadSet [intro!, wp, simp]:
  "empty_fail (threadSet f p)"
  by (wpsimp simp: threadSet_def setObject_def)

lemma empty_fail_getThreadState[iff]:
  "empty_fail (getThreadState t)"
  by (simp add: getThreadState_def)

declare empty_fail_stateAssert [wp]
declare setRegister_empty_fail [intro!, simp]

lemma empty_fail_getSchedulerAction [intro!, wp, simp]:
  "empty_fail getSchedulerAction"
  by (simp add: getSchedulerAction_def getObject_def split_def)

lemma empty_fail_scheduleSwitchThreadFastfail [intro!, wp, simp]:
  "empty_fail (scheduleSwitchThreadFastfail a b c d)"
  by (simp add: scheduleSwitchThreadFastfail_def split: if_splits)

lemma empty_fail_curDomain [intro!, wp, simp]:
  "empty_fail curDomain"
  by (simp add: curDomain_def)

end
end
