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
        return $ map (\<lambda>n. PageCap (PPtr (fromPPtr n)) VMReadWrite VMNoMap pSize dev Nothing) addrs
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
            createNewPageCaps regionBase numObjects dev 0 X64SmallPage
        | LargePageObject \<Rightarrow>
            createNewPageCaps regionBase numObjects dev ptTranslationBits X64LargePage
        | HugePageObject \<Rightarrow>
            createNewPageCaps regionBase numObjects dev (ptTranslationBits + ptTranslationBits) X64HugePage
        | PageTableObject \<Rightarrow>
            createNewTableCaps regionBase numObjects ptBits (makeObject::pte) PageTableCap
              (\<lambda>pts. return ())
        | PageDirectoryObject \<Rightarrow>
            createNewTableCaps regionBase numObjects pdBits (makeObject::pde) PageDirectoryCap
              (\<lambda>pts. return ())
        | PDPointerTableObject \<Rightarrow>
            createNewTableCaps regionBase numObjects pdptBits (makeObject::pdpte) PDPointerTableCap
              (\<lambda>pts. return ())
        | PML4Object \<Rightarrow>
            createNewTableCaps regionBase numObjects pml4Bits (makeObject::pml4e) PML4Cap
              (\<lambda>pms. mapM_x copyGlobalMappings pms)
        )"

end
end

end
