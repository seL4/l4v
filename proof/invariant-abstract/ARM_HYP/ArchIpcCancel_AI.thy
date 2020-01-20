(*
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

theory ArchIpcCancel_AI
imports "../IpcCancel_AI"
begin

context Arch begin global_naming ARM_HYP

named_theorems IpcCancel_AI_asms

crunches arch_post_cap_deletion
  for typ_at[wp, IpcCancel_AI_asms]: "\<lambda>s. P (typ_at T p s)"
  and idle_thread[wp, IpcCancel_AI_asms]: "\<lambda>s. P (idle_thread s)"

end

interpretation IpcCancel_AI?: IpcCancel_AI
  proof goal_cases
  interpret Arch .
  case 1 show ?case
  by (intro_locales; (unfold_locales; fact IpcCancel_AI_asms)?)
  qed


end
