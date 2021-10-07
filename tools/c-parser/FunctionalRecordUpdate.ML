(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* See http://mlton.org/FunctionalRecordUpdate *)
structure FunctionalRecordUpdate =
struct
local
  fun  f1 (f,z) x =   f (z x)
  fun  f2 (f,z) x =  f1 (f x, z)
  fun  f3 (f,z) x =  f2 (f x, z)
  fun  f4 (f,z) x =  f3 (f x, z)
  fun  f5 (f,z) x =  f4 (f x, z)
  fun  f6 (f,z) x =  f5 (f x, z)
  fun  f7 (f,z) x =  f6 (f x, z)
  fun  f8 (f,z) x =  f7 (f x, z)
  fun  f9 (f,z) x =  f8 (f x, z)
  fun f10 (f,z) x =  f9 (f x, z)
  fun f11 (f,z) x = f10 (f x, z)
  fun f12 (f,z) x = f11 (f x, z)
  fun f13 (f,z) x = f12 (f x, z)
  fun f14 (f,z) x = f13 (f x, z)
  fun f15 (f,z) x = f14 (f x, z)
  fun f16 (f,z) x = f15 (f x, z)
  fun f17 (f,z) x = f16 (f x, z)
  fun f18 (f,z) x = f17 (f x, z)
  fun f19 (f,z) x = f18 (f x, z)
  fun f20 (f,z) x = f19 (f x, z)
  fun f21 (f,z) x = f20 (f x, z)
  fun f22 (f,z) x = f21 (f x, z)
  fun f23 (f,z) x = f22 (f x, z)
  fun f24 (f,z) x = f23 (f x, z)
  fun f25 (f,z) x = f24 (f x, z)
  fun f26 (f,z) x = f25 (f x, z)

  fun  c0 from =  from
  fun  c1 from =  c0 (from  f1)
  fun  c2 from =  c1 (from  f2)
  fun  c3 from =  c2 (from  f3)
  fun  c4 from =  c3 (from  f4)
  fun  c5 from =  c4 (from  f5)
  fun  c6 from =  c5 (from  f6)
  fun  c7 from =  c6 (from  f7)
  fun  c8 from =  c7 (from  f8)
  fun  c9 from =  c8 (from  f9)
  fun c10 from =  c9 (from f10)
  fun c11 from = c10 (from f11)
  fun c12 from = c11 (from f12)
  fun c13 from = c12 (from f13)
  fun c14 from = c13 (from f14)
  fun c15 from = c14 (from f15)
  fun c16 from = c15 (from f16)
  fun c17 from = c16 (from f17)
  fun c18 from = c17 (from f18)
  fun c19 from = c18 (from f19)
  fun c20 from = c19 (from f20)
  fun c21 from = c20 (from f21)
  fun c22 from = c21 (from f22)
  fun c23 from = c22 (from f23)
  fun c24 from = c23 (from f24)
  fun c25 from = c24 (from f25)
  fun c26 from = c25 (from f26)
in

(* see http://mlton.org/Fold *)
structure Fold =
struct
  fun fold (a,f) g = g (a,f)
  fun step0 h (a,f) =  fold (h a, f)
  fun step1 h (a,f) b = fold (h (b,a), f)
  fun step2 h (a,f) b c = fold (h (b,c,a), f)
end

fun makeUpdate cX (from, from', to) record =
    let
      fun ops () = cX from'
      fun vars f = to f record
    in
      Fold.fold ((vars, ops), fn (vars, _) => vars from)
    end

fun  makeUpdate0 z = makeUpdate  c0 z
fun  makeUpdate1 z = makeUpdate  c1 z
fun  makeUpdate2 z = makeUpdate  c2 z
fun  makeUpdate3 z = makeUpdate  c3 z
fun  makeUpdate4 z = makeUpdate  c4 z
fun  makeUpdate5 z = makeUpdate  c5 z
fun  makeUpdate6 z = makeUpdate  c6 z
fun  makeUpdate7 z = makeUpdate  c7 z
fun  makeUpdate8 z = makeUpdate  c8 z
fun  makeUpdate9 z = makeUpdate  c9 z
fun makeUpdate10 z = makeUpdate c10 z
fun makeUpdate11 z = makeUpdate c11 z
fun makeUpdate12 z = makeUpdate c12 z
fun makeUpdate13 z = makeUpdate c13 z
fun makeUpdate14 z = makeUpdate c14 z
fun makeUpdate15 z = makeUpdate c15 z
fun makeUpdate16 z = makeUpdate c16 z
fun makeUpdate17 z = makeUpdate c17 z
fun makeUpdate18 z = makeUpdate c18 z
fun makeUpdate19 z = makeUpdate c19 z
fun makeUpdate20 z = makeUpdate c20 z
fun makeUpdate21 z = makeUpdate c21 z
fun makeUpdate22 z = makeUpdate c22 z
fun makeUpdate23 z = makeUpdate c23 z
fun makeUpdate24 z = makeUpdate c24 z
fun makeUpdate25 z = makeUpdate c25 z
fun makeUpdate26 z = makeUpdate c26 z

fun $$ (a,f) = f a

fun U s v z =
    Fold.step0 (fn (vars,ops) =>
                   (fn out => vars (s (ops()) (out,fn _ => v)),ops))
               z
end (* local *)

end (* struct *)
