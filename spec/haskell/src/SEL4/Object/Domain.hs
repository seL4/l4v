--
-- Copyright 2026, Proofcraft Pty Ltd
-- Copyright 2014, General Dynamics C4 Systems
--
-- SPDX-License-Identifier: GPL-2.0-only
--

-- This module contains domain scheduler invocation operations and decoding

{-# LANGUAGE CPP #-}

module SEL4.Object.Domain (
        decodeDomainInvocation, invokeDomain
    ) where

import Prelude hiding (Word)
import SEL4.Config (numDomains)
import SEL4.API.Types
import SEL4.API.Failures
import SEL4.API.Invocation
import SEL4.API.InvocationLabels
import SEL4.Machine
import SEL4.Model
import SEL4.Object.Structures
import {-# SOURCE #-} SEL4.Kernel.Thread

import qualified SEL4.Object.Domain.TARGET as Arch


-- Performing Domain Invocations

domainSet :: PPtr TCB -> Domain -> Kernel ()
domainSet thread domain = do
    Arch.prepareSetDomain thread domain
    setDomain thread domain

-- does not exist in Prelude; this definition lines up with Isabelle list_update
listUpdate :: [a] -> Int -> a -> [a]
listUpdate []     i v = []
listUpdate (x:xs) i v = if i == 0 then v:xs else x:listUpdate xs (i - 1) v

domainScheduleConfigure :: Int -> Domain -> DomainDuration -> Kernel ()
domainScheduleConfigure index domain duration =
    modify (\s -> s { ksDomSchedule = listUpdate (ksDomSchedule s) index (domain, duration) })

domainSetStart start = do
    modify (\s -> s { ksDomScheduleStart = start })
    modify (\s -> s { ksDomainTime = 0 })
    rescheduleRequired

invokeDomain :: DomainInvocation -> Kernel ()
invokeDomain (InvokeDomainSet thread domain) =
    domainSet thread domain
invokeDomain (InvokeDomainScheduleConfigure index domain duration) =
    domainScheduleConfigure index domain duration
invokeDomain (InvokeDomainScheduleSetStart start) =
    domainSetStart start


-- Decoding Domain Invocations

decodeDomainSet :: [Word] -> [(Capability, PPtr CTE)] -> KernelF SyscallError DomainInvocation
decodeDomainSet args extraCaps = do
    domain <- case args of
        (x:_) -> do
                     when (fromIntegral x >= numDomains) $
                         throw InvalidArgument { invalidArgumentNumber = 0 }
                     return $ fromIntegral x
        _ -> throw TruncatedMessage
    when (null extraCaps) $ throw TruncatedMessage
    case fst (head extraCaps) of
        ThreadCap { capTCBPtr = ptr } -> return $ InvokeDomainSet ptr domain
        _ -> throw InvalidArgument { invalidArgumentNumber = 1 }

decodeDomainConfigure :: [Word] -> [(Capability, PPtr CTE)] -> KernelF SyscallError DomainInvocation
decodeDomainConfigure args extraCaps = do
    when (length args < 2 + timeArgLen) $ throw TruncatedMessage
    index <- return $ fromIntegral $ args !! 0
    domain <- return $ args !! 1
    duration <- return $ parseTimeArg 2 args
    sched <- withoutFailure $ gets ksDomSchedule
    when (index >= length sched) $ throw $ RangeError 0 (fromIntegral (length sched - 1))
    when (fromIntegral domain >= numDomains)  $ throw $ RangeError 0 (fromIntegral (numDomains - 1))
    when (duration > maxDomainDuration) $ throw $ InvalidArgument 2
    when (duration == 0 && domain /= 0) $ throw $ InvalidArgument 1
    start <- withoutFailure $ gets ksDomScheduleStart
    when (index == start && duration == 0) $ throw $ InvalidArgument 2
    return $ InvokeDomainScheduleConfigure index (fromIntegral domain) duration

decodeDomainSetStart :: [Word] -> [(Capability, PPtr CTE)] -> KernelF SyscallError DomainInvocation
decodeDomainSetStart args extraCaps = do
    when (length args == 0) $ throw TruncatedMessage
    index <- return $ fromIntegral $ args !! 0
    sched <- withoutFailure $ gets ksDomSchedule
    when (index >= length sched) $ throw $ RangeError 0 (fromIntegral (length sched - 1))
    when (sched !! index == domainEndMarker) $ throw $ InvalidArgument 0
    return $ InvokeDomainScheduleSetStart index

decodeDomainInvocation :: Word -> [Word] -> [(Capability, PPtr CTE)] ->
        KernelF SyscallError DomainInvocation
decodeDomainInvocation label args extraCaps = do
    case genInvocationType label of
        DomainSetSet -> decodeDomainSet args extraCaps
        DomainScheduleConfigure -> decodeDomainConfigure args extraCaps
        DomainScheduleSetStart -> decodeDomainSetStart args extraCaps
        _ -> throw IllegalOperation
