(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(* this is an -*- sml -*- file *)
structure RecursiveRecordPP =
struct

(* a chunk of RecordPackage.ML ripped violently free of its shackles *)


(* this much handles pretty-printing record field updates *)
val updateN = Record.updateN

fun gen_field_upds_tr' mark sfx (tm as Const (name_field, _) $ k $ u) =
  let val t = (case k of (Abs (_,_,(Abs (_,_,t)$Bound 0)))
                  => if null (loose_bnos t) then t else raise Match
               | Abs (_,_,t) => if null (loose_bnos t) then t else raise Match
               | _ => raise Match)
  in
    (case try (unsuffix sfx) name_field of
      SOME name =>
        apfst (cons (Syntax.const mark $ Syntax.free name $ t)) (gen_field_upds_tr' mark sfx u)
     | NONE => ([], tm))
  end
  | gen_field_upds_tr' _ _ tm = ([], tm);

fun record_update_tr' _ tm =
  let val (ts, u) = gen_field_upds_tr' "_update" updateN tm in
    if null ts then raise Match
    else Syntax.const "_record_update" $ u $
          foldr1 (fn (v, w) => Syntax.const "_updates" $ v $ w) (rev ts)
  end;

fun gen_field_tr' sfx tr' name =
  let val name_sfx = suffix sfx name
  in (name_sfx, fn ctxt => fn [t, u] => tr' ctxt (Syntax.const name_sfx $ t $ u) | _ => raise Match) end;

fun print_translation names =
  map (gen_field_tr' updateN record_update_tr') names;


fun install_translations
      {record_name = _, fields : {fldname : string, fldty : typ} list} thy =
let
  val field_tr's = print_translation (map #fldname fields)
in
  Sign.print_translation field_tr's thy
end

end;
