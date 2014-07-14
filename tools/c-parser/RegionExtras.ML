(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

signature REGION_EXTRAS =
sig
  type 'a wrap
  val bogus : SourcePos.t
  val wrap : 'a * SourcePos.t * SourcePos.t -> 'a wrap
  val bogwrap : 'a -> 'a wrap
  val left : 'a wrap -> SourcePos.t
  val right : 'a wrap -> SourcePos.t
  val node : 'a wrap -> 'a
  val apnode : ('a -> 'b) -> 'a wrap -> 'b wrap
end

structure RegionExtras =
struct

val bogus = SourcePos.bogus
type 'a wrap = 'a Region.Wrap.t
fun wrap (x,l,r) = Region.Wrap.makeRegion'(x,l,r)
fun bogwrap x = wrap(x,bogus,bogus)
fun left w =
    valOf (Region.left (Region.Wrap.region w)) handle Option => bogus
fun right w =
    valOf (Region.right (Region.Wrap.region w))
    handle Option => bogus
val node = Region.Wrap.node

fun apnode f x_w = let
  val x = node x_w
in
  wrap (f x, left x_w, right x_w)
end

end (* struct *)
