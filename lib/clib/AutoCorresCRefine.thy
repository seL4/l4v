(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory AutoCorresCRefine

imports Ctac "../../tools/autocorres/LegacyAutoCorres"

begin

context kernel begin

ML {* val ckernel_fn_info = (FunctionInfo.init_fn_info @{context} "c/kernel_all.c_pp") *}
ML {* val ckernel_prog_info = ProgramInfo.get_prog_info @{context} "c/kernel_all.c_pp" *}

end

method_setup autocorres_legacy
    = {* AutoCorresLegacy.method ckernel_prog_info ckernel_fn_info
        @{term "globals :: globals myvars \<Rightarrow> _"} *}

end
