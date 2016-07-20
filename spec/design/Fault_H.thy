(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file Fault_H.thy *)
(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(*
	 The fault datatype. 
*)

chapter "Fault Structures"

theory Fault_H
imports "$L4V_ARCH/ArchFault_H"
begin

context begin interpretation Arch .

requalify_types
  arch_fault
end

datatype lookup_failure =
    MissingCapability nat
  | DepthMismatch nat nat
  | InvalidRoot
  | GuardMismatch nat machine_word nat

primrec
  depthMismatchBitsLeft :: "lookup_failure \<Rightarrow> nat"
where
  "depthMismatchBitsLeft (DepthMismatch v0 v1) = v0"

primrec
  guardMismatchBitsLeft :: "lookup_failure \<Rightarrow> nat"
where
  "guardMismatchBitsLeft (GuardMismatch v0 v1 v2) = v0"

primrec
  guardMismatchGuardFound :: "lookup_failure \<Rightarrow> machine_word"
where
  "guardMismatchGuardFound (GuardMismatch v0 v1 v2) = v1"

primrec
  guardMismatchGuardSize :: "lookup_failure \<Rightarrow> nat"
where
  "guardMismatchGuardSize (GuardMismatch v0 v1 v2) = v2"

primrec
  missingCapBitsLeft :: "lookup_failure \<Rightarrow> nat"
where
  "missingCapBitsLeft (MissingCapability v0) = v0"

primrec
  depthMismatchBitsFound :: "lookup_failure \<Rightarrow> nat"
where
  "depthMismatchBitsFound (DepthMismatch v0 v1) = v1"

primrec
  depthMismatchBitsLeft_update :: "(nat \<Rightarrow> nat) \<Rightarrow> lookup_failure \<Rightarrow> lookup_failure"
where
  "depthMismatchBitsLeft_update f (DepthMismatch v0 v1) = DepthMismatch (f v0) v1"

primrec
  guardMismatchBitsLeft_update :: "(nat \<Rightarrow> nat) \<Rightarrow> lookup_failure \<Rightarrow> lookup_failure"
where
  "guardMismatchBitsLeft_update f (GuardMismatch v0 v1 v2) = GuardMismatch (f v0) v1 v2"

primrec
  guardMismatchGuardFound_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> lookup_failure \<Rightarrow> lookup_failure"
where
  "guardMismatchGuardFound_update f (GuardMismatch v0 v1 v2) = GuardMismatch v0 (f v1) v2"

primrec
  guardMismatchGuardSize_update :: "(nat \<Rightarrow> nat) \<Rightarrow> lookup_failure \<Rightarrow> lookup_failure"
where
  "guardMismatchGuardSize_update f (GuardMismatch v0 v1 v2) = GuardMismatch v0 v1 (f v2)"

primrec
  missingCapBitsLeft_update :: "(nat \<Rightarrow> nat) \<Rightarrow> lookup_failure \<Rightarrow> lookup_failure"
where
  "missingCapBitsLeft_update f (MissingCapability v0) = MissingCapability (f v0)"

primrec
  depthMismatchBitsFound_update :: "(nat \<Rightarrow> nat) \<Rightarrow> lookup_failure \<Rightarrow> lookup_failure"
where
  "depthMismatchBitsFound_update f (DepthMismatch v0 v1) = DepthMismatch v0 (f v1)"

abbreviation (input)
  MissingCapability_trans :: "(nat) \<Rightarrow> lookup_failure" ("MissingCapability'_ \<lparr> missingCapBitsLeft= _ \<rparr>")
where
  "MissingCapability_ \<lparr> missingCapBitsLeft= v0 \<rparr> == MissingCapability v0"

abbreviation (input)
  DepthMismatch_trans :: "(nat) \<Rightarrow> (nat) \<Rightarrow> lookup_failure" ("DepthMismatch'_ \<lparr> depthMismatchBitsLeft= _, depthMismatchBitsFound= _ \<rparr>")
where
  "DepthMismatch_ \<lparr> depthMismatchBitsLeft= v0, depthMismatchBitsFound= v1 \<rparr> == DepthMismatch v0 v1"

abbreviation (input)
  GuardMismatch_trans :: "(nat) \<Rightarrow> (machine_word) \<Rightarrow> (nat) \<Rightarrow> lookup_failure" ("GuardMismatch'_ \<lparr> guardMismatchBitsLeft= _, guardMismatchGuardFound= _, guardMismatchGuardSize= _ \<rparr>")
where
  "GuardMismatch_ \<lparr> guardMismatchBitsLeft= v0, guardMismatchGuardFound= v1, guardMismatchGuardSize= v2 \<rparr> == GuardMismatch v0 v1 v2"

definition
  isMissingCapability :: "lookup_failure \<Rightarrow> bool"
where
 "isMissingCapability v \<equiv> case v of
    MissingCapability v0 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isDepthMismatch :: "lookup_failure \<Rightarrow> bool"
where
 "isDepthMismatch v \<equiv> case v of
    DepthMismatch v0 v1 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isInvalidRoot :: "lookup_failure \<Rightarrow> bool"
where
 "isInvalidRoot v \<equiv> case v of
    InvalidRoot \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isGuardMismatch :: "lookup_failure \<Rightarrow> bool"
where
 "isGuardMismatch v \<equiv> case v of
    GuardMismatch v0 v1 v2 \<Rightarrow> True
  | _ \<Rightarrow> False"

datatype fault =
    UserException machine_word machine_word
  | CapFault cptr bool lookup_failure
  | UnknownSyscallException machine_word
  | ArchFault arch_fault

primrec
  userExceptionErrorCode :: "fault \<Rightarrow> machine_word"
where
  "userExceptionErrorCode (UserException v0 v1) = v1"

primrec
  capFaultInReceivePhase :: "fault \<Rightarrow> bool"
where
  "capFaultInReceivePhase (CapFault v0 v1 v2) = v1"

primrec
  capFaultFailure :: "fault \<Rightarrow> lookup_failure"
where
  "capFaultFailure (CapFault v0 v1 v2) = v2"

primrec
  archFault :: "fault \<Rightarrow> arch_fault"
where
  "archFault (ArchFault v0) = v0"

primrec
  capFaultAddress :: "fault \<Rightarrow> cptr"
where
  "capFaultAddress (CapFault v0 v1 v2) = v0"

primrec
  userExceptionNumber :: "fault \<Rightarrow> machine_word"
where
  "userExceptionNumber (UserException v0 v1) = v0"

primrec
  unknownSyscallNumber :: "fault \<Rightarrow> machine_word"
where
  "unknownSyscallNumber (UnknownSyscallException v0) = v0"

primrec
  userExceptionErrorCode_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> fault \<Rightarrow> fault"
where
  "userExceptionErrorCode_update f (UserException v0 v1) = UserException v0 (f v1)"

primrec
  capFaultInReceivePhase_update :: "(bool \<Rightarrow> bool) \<Rightarrow> fault \<Rightarrow> fault"
where
  "capFaultInReceivePhase_update f (CapFault v0 v1 v2) = CapFault v0 (f v1) v2"

primrec
  capFaultFailure_update :: "(lookup_failure \<Rightarrow> lookup_failure) \<Rightarrow> fault \<Rightarrow> fault"
where
  "capFaultFailure_update f (CapFault v0 v1 v2) = CapFault v0 v1 (f v2)"

primrec
  archFault_update :: "(arch_fault \<Rightarrow> arch_fault) \<Rightarrow> fault \<Rightarrow> fault"
where
  "archFault_update f (ArchFault v0) = ArchFault (f v0)"

primrec
  capFaultAddress_update :: "(cptr \<Rightarrow> cptr) \<Rightarrow> fault \<Rightarrow> fault"
where
  "capFaultAddress_update f (CapFault v0 v1 v2) = CapFault (f v0) v1 v2"

primrec
  userExceptionNumber_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> fault \<Rightarrow> fault"
where
  "userExceptionNumber_update f (UserException v0 v1) = UserException (f v0) v1"

primrec
  unknownSyscallNumber_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> fault \<Rightarrow> fault"
where
  "unknownSyscallNumber_update f (UnknownSyscallException v0) = UnknownSyscallException (f v0)"

abbreviation (input)
  UserException_trans :: "(machine_word) \<Rightarrow> (machine_word) \<Rightarrow> fault" ("UserException'_ \<lparr> userExceptionNumber= _, userExceptionErrorCode= _ \<rparr>")
where
  "UserException_ \<lparr> userExceptionNumber= v0, userExceptionErrorCode= v1 \<rparr> == UserException v0 v1"

abbreviation (input)
  CapFault_trans :: "(cptr) \<Rightarrow> (bool) \<Rightarrow> (lookup_failure) \<Rightarrow> fault" ("CapFault'_ \<lparr> capFaultAddress= _, capFaultInReceivePhase= _, capFaultFailure= _ \<rparr>")
where
  "CapFault_ \<lparr> capFaultAddress= v0, capFaultInReceivePhase= v1, capFaultFailure= v2 \<rparr> == CapFault v0 v1 v2"

abbreviation (input)
  UnknownSyscallException_trans :: "(machine_word) \<Rightarrow> fault" ("UnknownSyscallException'_ \<lparr> unknownSyscallNumber= _ \<rparr>")
where
  "UnknownSyscallException_ \<lparr> unknownSyscallNumber= v0 \<rparr> == UnknownSyscallException v0"

abbreviation (input)
  ArchFault_trans :: "(arch_fault) \<Rightarrow> fault" ("ArchFault'_ \<lparr> archFault= _ \<rparr>")
where
  "ArchFault_ \<lparr> archFault= v0 \<rparr> == ArchFault v0"

definition
  isUserException :: "fault \<Rightarrow> bool"
where
 "isUserException v \<equiv> case v of
    UserException v0 v1 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isCapFault :: "fault \<Rightarrow> bool"
where
 "isCapFault v \<equiv> case v of
    CapFault v0 v1 v2 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isUnknownSyscallException :: "fault \<Rightarrow> bool"
where
 "isUnknownSyscallException v \<equiv> case v of
    UnknownSyscallException v0 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isArchFault :: "fault \<Rightarrow> bool"
where
 "isArchFault v \<equiv> case v of
    ArchFault v0 \<Rightarrow> True
  | _ \<Rightarrow> False"

datatype init_failure =
    IFailure

datatype syscall_error =
    IllegalOperation
  | InvalidArgument nat
  | TruncatedMessage
  | DeleteFirst
  | RangeError machine_word machine_word
  | FailedLookup bool lookup_failure
  | InvalidCapability nat
  | RevokeFirst
  | NotEnoughMemory machine_word
  | AlignmentError

primrec
  failedLookupDescription :: "syscall_error \<Rightarrow> lookup_failure"
where
  "failedLookupDescription (FailedLookup v0 v1) = v1"

primrec
  invalidCapNumber :: "syscall_error \<Rightarrow> nat"
where
  "invalidCapNumber (InvalidCapability v0) = v0"

primrec
  invalidArgumentNumber :: "syscall_error \<Rightarrow> nat"
where
  "invalidArgumentNumber (InvalidArgument v0) = v0"

primrec
  rangeErrorMax :: "syscall_error \<Rightarrow> machine_word"
where
  "rangeErrorMax (RangeError v0 v1) = v1"

primrec
  rangeErrorMin :: "syscall_error \<Rightarrow> machine_word"
where
  "rangeErrorMin (RangeError v0 v1) = v0"

primrec
  memoryLeft :: "syscall_error \<Rightarrow> machine_word"
where
  "memoryLeft (NotEnoughMemory v0) = v0"

primrec
  failedLookupWasSource :: "syscall_error \<Rightarrow> bool"
where
  "failedLookupWasSource (FailedLookup v0 v1) = v0"

primrec
  failedLookupDescription_update :: "(lookup_failure \<Rightarrow> lookup_failure) \<Rightarrow> syscall_error \<Rightarrow> syscall_error"
where
  "failedLookupDescription_update f (FailedLookup v0 v1) = FailedLookup v0 (f v1)"

primrec
  invalidCapNumber_update :: "(nat \<Rightarrow> nat) \<Rightarrow> syscall_error \<Rightarrow> syscall_error"
where
  "invalidCapNumber_update f (InvalidCapability v0) = InvalidCapability (f v0)"

primrec
  invalidArgumentNumber_update :: "(nat \<Rightarrow> nat) \<Rightarrow> syscall_error \<Rightarrow> syscall_error"
where
  "invalidArgumentNumber_update f (InvalidArgument v0) = InvalidArgument (f v0)"

primrec
  rangeErrorMax_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> syscall_error \<Rightarrow> syscall_error"
where
  "rangeErrorMax_update f (RangeError v0 v1) = RangeError v0 (f v1)"

primrec
  rangeErrorMin_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> syscall_error \<Rightarrow> syscall_error"
where
  "rangeErrorMin_update f (RangeError v0 v1) = RangeError (f v0) v1"

primrec
  memoryLeft_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> syscall_error \<Rightarrow> syscall_error"
where
  "memoryLeft_update f (NotEnoughMemory v0) = NotEnoughMemory (f v0)"

primrec
  failedLookupWasSource_update :: "(bool \<Rightarrow> bool) \<Rightarrow> syscall_error \<Rightarrow> syscall_error"
where
  "failedLookupWasSource_update f (FailedLookup v0 v1) = FailedLookup (f v0) v1"

abbreviation (input)
  InvalidArgument_trans :: "(nat) \<Rightarrow> syscall_error" ("InvalidArgument'_ \<lparr> invalidArgumentNumber= _ \<rparr>")
where
  "InvalidArgument_ \<lparr> invalidArgumentNumber= v0 \<rparr> == InvalidArgument v0"

abbreviation (input)
  RangeError_trans :: "(machine_word) \<Rightarrow> (machine_word) \<Rightarrow> syscall_error" ("RangeError'_ \<lparr> rangeErrorMin= _, rangeErrorMax= _ \<rparr>")
where
  "RangeError_ \<lparr> rangeErrorMin= v0, rangeErrorMax= v1 \<rparr> == RangeError v0 v1"

abbreviation (input)
  FailedLookup_trans :: "(bool) \<Rightarrow> (lookup_failure) \<Rightarrow> syscall_error" ("FailedLookup'_ \<lparr> failedLookupWasSource= _, failedLookupDescription= _ \<rparr>")
where
  "FailedLookup_ \<lparr> failedLookupWasSource= v0, failedLookupDescription= v1 \<rparr> == FailedLookup v0 v1"

abbreviation (input)
  InvalidCapability_trans :: "(nat) \<Rightarrow> syscall_error" ("InvalidCapability'_ \<lparr> invalidCapNumber= _ \<rparr>")
where
  "InvalidCapability_ \<lparr> invalidCapNumber= v0 \<rparr> == InvalidCapability v0"

abbreviation (input)
  NotEnoughMemory_trans :: "(machine_word) \<Rightarrow> syscall_error" ("NotEnoughMemory'_ \<lparr> memoryLeft= _ \<rparr>")
where
  "NotEnoughMemory_ \<lparr> memoryLeft= v0 \<rparr> == NotEnoughMemory v0"

definition
  isIllegalOperation :: "syscall_error \<Rightarrow> bool"
where
 "isIllegalOperation v \<equiv> case v of
    IllegalOperation \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isInvalidArgument :: "syscall_error \<Rightarrow> bool"
where
 "isInvalidArgument v \<equiv> case v of
    InvalidArgument v0 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isTruncatedMessage :: "syscall_error \<Rightarrow> bool"
where
 "isTruncatedMessage v \<equiv> case v of
    TruncatedMessage \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isDeleteFirst :: "syscall_error \<Rightarrow> bool"
where
 "isDeleteFirst v \<equiv> case v of
    DeleteFirst \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isRangeError :: "syscall_error \<Rightarrow> bool"
where
 "isRangeError v \<equiv> case v of
    RangeError v0 v1 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isFailedLookup :: "syscall_error \<Rightarrow> bool"
where
 "isFailedLookup v \<equiv> case v of
    FailedLookup v0 v1 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isInvalidCapability :: "syscall_error \<Rightarrow> bool"
where
 "isInvalidCapability v \<equiv> case v of
    InvalidCapability v0 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isRevokeFirst :: "syscall_error \<Rightarrow> bool"
where
 "isRevokeFirst v \<equiv> case v of
    RevokeFirst \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isNotEnoughMemory :: "syscall_error \<Rightarrow> bool"
where
 "isNotEnoughMemory v \<equiv> case v of
    NotEnoughMemory v0 \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isAlignmentError :: "syscall_error \<Rightarrow> bool"
where
 "isAlignmentError v \<equiv> case v of
    AlignmentError \<Rightarrow> True
  | _ \<Rightarrow> False"

consts'
msgFromSyscallError :: "syscall_error \<Rightarrow> (machine_word * machine_word list)"

consts'
msgFromLookupFailure :: "lookup_failure \<Rightarrow> machine_word list"

defs msgFromSyscallError_def:
"msgFromSyscallError x0\<equiv> (case x0 of
    (InvalidArgument n) \<Rightarrow>    (1, [fromIntegral n])
  | (InvalidCapability n) \<Rightarrow>    (2, [fromIntegral n])
  | IllegalOperation \<Rightarrow>    (3, [])
  | (RangeError minV maxV) \<Rightarrow>    (4, [minV, maxV])
  | AlignmentError \<Rightarrow>    (5, [])
  | (FailedLookup s lf) \<Rightarrow>   
    (6, (fromIntegral $ fromEnum s)#(msgFromLookupFailure lf))
  | TruncatedMessage \<Rightarrow>    (7, [])
  | DeleteFirst \<Rightarrow>    (8, [])
  | RevokeFirst \<Rightarrow>    (9, [])
  | (NotEnoughMemory n) \<Rightarrow>    (10, [n])
  )"

defs msgFromLookupFailure_def:
"msgFromLookupFailure x0\<equiv> (case x0 of
    InvalidRoot \<Rightarrow>    [1]
  | (MissingCapability bl) \<Rightarrow>    [2, fromIntegral bl]
  | (DepthMismatch bl bf) \<Rightarrow>   
    [3, fromIntegral bl, fromIntegral bf]
  | (GuardMismatch bl g gs) \<Rightarrow>   
    [4, fromIntegral bl, g, fromIntegral gs]
  )"


end
