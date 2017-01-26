(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Intermediate"

theory ArchIntermediate_H
imports "../Intermediate_H"
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
        return $ map (\<lambda>n. PageCap dev (PPtr (fromPPtr n)) VMReadWrite pSize Nothing) addrs
     od)"

private abbreviation (input)
  "createNewTableCaps regionBase numObjects tableBits objectProto cap initialiseMappings \<equiv> (do
      tableSize \<leftarrow> return (tableBits - objBits objectProto);
      addrs \<leftarrow> createObjects regionBase numObjects (injectKO objectProto) tableSize;
      pts \<leftarrow> return (map (PPtr \<circ> fromPPtr) addrs);
      initialiseMappings pts;
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
            createNewPageCaps regionBase numObjects dev 8 ARMSection
        | SuperSectionObject \<Rightarrow>
            createNewPageCaps regionBase numObjects dev 12 ARMSuperSection
        | PageTableObject \<Rightarrow>
            createNewTableCaps regionBase numObjects ptBits (makeObject::pte) PageTableCap
              (\<lambda>pts. return ())
        | PageDirectoryObject \<Rightarrow>
            createNewTableCaps regionBase numObjects pdBits (makeObject::pde) PageDirectoryCap
              (\<lambda>pds. do objSize \<leftarrow> return (((1::nat) `~shiftL~` pdBits));
                        mapM_x copyGlobalMappings pds;
                        doMachineOp $ mapM_x (\<lambda>x. cleanCacheRange_PoU x
                                                    (x + (fromIntegral objSize) - 1)
                                                    (addrFromPPtr x)) pds
                     od)
        )"

end
end

end
