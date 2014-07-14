(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

if OS.Process.getEnv "SKIP_REFINE_PROOFS" = SOME "1" then
  with_skip_proofs_use_thys ["Refine_C"]
else
  use_thy "Refine_C";


