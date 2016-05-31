(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

structure MString :> sig
  eqtype t
  val mk : string -> t
  val dest : t -> string
  val destPP : t -> string
  val compare : t * t -> order
end = struct
  type t = string
  fun mk s = s
  fun dest s = s
  fun destPP s = "MV(" ^ s ^ ")"
  val compare = String.compare
end
structure MSymTab = Table(struct
  type key = MString.t
  val ord = inv_img_cmp MString.dest String.compare
end)

structure CNameTab = Table
  (struct type key = {varname : MString.t,
                      fnname : string option}
          fun ord ({varname = vn1, fnname = fn1},
                   {varname = vn2, fnname = fn2}) =
              pair_compare (option_compare String.compare,
                            MString.compare)
                           ((fn1, vn1), (fn2, vn2))
   end)

datatype more_info = MungedVar of {munge : MString.t, owned_by : string option}
                   | EnumC
                   | FunctionName
