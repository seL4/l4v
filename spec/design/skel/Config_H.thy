(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Config_H
imports Types_H Kernel_Config
begin

#INCLUDE_HASKELL SEL4/Config.lhs NOT numDomains

end
