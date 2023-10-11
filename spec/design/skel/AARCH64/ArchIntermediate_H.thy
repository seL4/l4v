(*
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2022, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Intermediate"

theory ArchIntermediate_H
imports Intermediate_H
begin

context Arch begin
context begin

private abbreviation (input)
  "createNewFrameCaps regionBase numObjects dev gSize pSize \<equiv>
    let Data = (if dev then KOUserDataDevice else KOUserData) in
    (do addrs \<leftarrow> createObjects regionBase numObjects Data gSize;
        modify (\<lambda>ks. ks \<lparr> gsUserPages := (\<lambda> addr.
          if addr `~elem~` map fromPPtr addrs then Just pSize
          else gsUserPages ks addr)\<rparr>);
        return $ map (\<lambda>n. FrameCap  (PPtr (fromPPtr n)) VMReadWrite pSize dev Nothing) addrs
     od)"

private abbreviation (input)
  "createNewTableCaps regionBase numObjects ptType objectProto cap initialiseMappings \<equiv> (do
      tableBits \<leftarrow> return (ptBits ptType);
      tableSize \<leftarrow> return (tableBits - objBits objectProto);
      addrs \<leftarrow> createObjects regionBase numObjects (injectKO objectProto) tableSize;
      pts \<leftarrow> return (map (PPtr \<circ> fromPPtr) addrs);
      modify (\<lambda>ks. ks \<lparr>ksArchState :=
                         ksArchState ks \<lparr>gsPTTypes := (\<lambda>addr.
                                           if addr `~elem~` map fromPPtr addrs then Just ptType
                                           else gsPTTypes (ksArchState ks) addr)\<rparr>\<rparr>);
      initialiseMappings pts;
      return $ map (\<lambda>pt. cap pt Nothing) pts
    od)"

defs Arch_createNewCaps_def:
"Arch_createNewCaps t regionBase numObjects userSize dev \<equiv>
    let pointerCast = PPtr \<circ> fromPPtr
    in (case t of
          APIObjectType apiObject \<Rightarrow> haskell_fail []
        | SmallPageObject \<Rightarrow>
            createNewFrameCaps regionBase numObjects dev 0 ARMSmallPage
        | LargePageObject \<Rightarrow>
            createNewFrameCaps regionBase numObjects dev (ptTranslationBits NormalPT_T) ARMLargePage
        | HugePageObject \<Rightarrow>
            createNewFrameCaps regionBase numObjects dev (2 * ptTranslationBits NormalPT_T) ARMHugePage
        | VSpaceObject \<Rightarrow>
            createNewTableCaps regionBase numObjects VSRootPT_T (makeObject::pte)
              (\<lambda>base addr. PageTableCap base VSRootPT_T addr)
              (\<lambda>pts. return ())
        | PageTableObject \<Rightarrow>
            createNewTableCaps regionBase numObjects NormalPT_T (makeObject::pte)
              (\<lambda>base addr. PageTableCap base NormalPT_T addr)
              (\<lambda>pts. return ())
        | VCPUObject \<Rightarrow> (do
            addrs \<leftarrow> createObjects regionBase numObjects (injectKO (makeObject :: vcpu)) 0;
            return $ map (\<lambda> addr. VCPUCap addr) addrs
            od)
        )"

end
end

end
