(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory parse_struct
imports "../CTranslation"
begin

install_C_file "parse_struct.c"

(* mem_type instances proved automatically.  If you remove the additional
   theorems from the simp add: list below, you see that the LHS of the goal
   turns into sizeof TYPE(struct1), demonstrating that the mem_type's axiom
   "len" is applied.  Thus, struct1 is really a mem_type. *)

lemma
  "length bs = size_of TYPE(struct1_C) \<Longrightarrow> length (to_bytes (x::struct1_C) bs) = 12"
  by (simp)

print_locale parse_struct_global_addresses

thm allinclusive_C_typ_tag

thm parse_struct_global_addresses.mkall_body_def

(* fold congruences proved in creation of these records help us
   by reducing the doubling of syntax on the lhs *)
lemma "s \<lparr> c1_C := c1_C s + 2 \<rparr> = c1_C_update (\<lambda>x. x + 2) s"
  apply (simp cong: charpair_C_fold_congs)
  done

end
