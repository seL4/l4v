(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Config_H
imports Types_H
begin

#INCLUDE_HASKELL SEL4/Config.lhs NOT numDomains timeSlice resetChunkBits retypeFanOutLimit

end
