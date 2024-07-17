(*
 * Copyright 2014, General Dynamics C4 Systems
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
  "createNewPageCaps regionBase numObjects dev gSize pSize \<equiv>
    let Data = (if dev then KOUserDataDevice else KOUserData) in
    (do addrs \<leftarrow> createObjects regionBase numObjects Data gSize;
        modify (\<lambda>ks. ks \<lparr> gsUserPages := (\<lambda> addr.
          if addr `~elem~` map fromPPtr addrs then Just pSize
          else gsUserPages ks addr)\<rparr>);
        when (\<not>dev) $
          mapM_x (\<lambda>addr. doMachineOp $
                            cleanCacheRange_RAM addr
                                                (addr + mask (pageBitsForSize pSize))
                                                (addrFromPPtr addr)) addrs;
        return $ map (\<lambda>n. PageCap dev (PPtr (fromPPtr n)) VMReadWrite pSize Nothing) addrs
     od)"

private abbreviation (input)
  "createNewTableCaps regionBase numObjects tableBits objectProto cap initialiseMappings \<equiv> (do
      tableSize \<leftarrow> return (tableBits - objBits objectProto);
      addrs \<leftarrow> createObjects regionBase numObjects (injectKO objectProto) tableSize;
      pts \<leftarrow> return (map (PPtr \<circ> fromPPtr) addrs);
      initialiseMappings pts;
      mapM_x (\<lambda>addr. doMachineOp $
                       cleanCacheRange_PoU addr (addr + mask tableBits) (addrFromPPtr addr)) addrs;
      return $ map (\<lambda>pt. cap pt Nothing) pts
    od)"

defs Arch_createNewCaps_def:
"Arch_createNewCaps t regionBase numObjects userSize dev \<equiv>
    let pointerCast = PPtr \<circ> fromPPtr
    in (case t of
          APIObjectType apiObject \<Rightarrow> haskell_fail []
        | SmallPageObject \<Rightarrow>
            createNewPageCaps regionBase numObjects dev 0 ARMSmallPage
        | LargePageObject \<Rightarrow>
            createNewPageCaps regionBase numObjects dev 4 ARMLargePage
        | SectionObject \<Rightarrow>
            createNewPageCaps regionBase numObjects dev 9 ARMSection
        | SuperSectionObject \<Rightarrow>
            createNewPageCaps regionBase numObjects dev 13 ARMSuperSection
        | PageTableObject \<Rightarrow>
            createNewTableCaps regionBase numObjects ptBits (makeObject::pte) PageTableCap
              (\<lambda>pts. return ())
        | PageDirectoryObject \<Rightarrow>
            createNewTableCaps regionBase numObjects pdBits (makeObject::pde) PageDirectoryCap
              (\<lambda>pds. do objSize \<leftarrow> return (((1::nat) `~shiftL~` pdBits));
                        mapM_x copyGlobalMappings pds
                     od)
        | VCPUObject \<Rightarrow> (do
            addrs \<leftarrow> createObjects regionBase numObjects (injectKO (makeObject :: vcpu)) 0;
            return $ map (\<lambda>addr. VCPUCap addr) addrs
            od)
        )"

end
end

end
