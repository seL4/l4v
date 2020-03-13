(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

signature PROOF_COUNT =
sig

  datatype lemmaT = Lemma of string | Declare of string

  datatype transactionT = Start | Qed | Declaration | Qed_Global | Unknown

  type count_report = (((transactionT * string) * string list * (Position.range)) list Symtab.table)

  val get_size_report : unit -> count_report

  val compute_sizes : count_report -> (lemmaT * Position.range) Symtab.table

end

structure Proof_Count : PROOF_COUNT =
struct

datatype transactionT = Start | Qed | Declaration | Qed_Global | Unknown

type count_report = (((transactionT * string) * string list * (Position.range)) list Symtab.table)

val transactions = Synchronized.var "hooked" (Symtab.empty : ((transactionT * string) * string list * (Position.range)) list Symtab.table)

fun get_transactionT k =
    if Keyword.is_theory_goal k orelse Keyword.is_proof_goal k then Start
    else if Keyword.is_qed k then Qed
    else if Keyword.is_qed_global k then Qed_Global
    else if member (op =) (Keyword.command_tags k) "thy_decl" orelse k = "lemmas" then Declaration
    else Unknown

fun needs_hook k = case get_transactionT k of Unknown => false
                 | _ => if k = "lemmas" orelse k = "by" then false else true

(*We explicitly ignore the "real" fact names because this is not what's given in the dependency analysis.*)
(*The "name" tag in the thm is what is picked up by the kernel for creating the proof_bodies*)
fun add_new_lemmas thy thy' beg fin trans =
let
  val file = Position.file_of beg
                       |> the_default ""
  val prev_facts = Global_Theory.facts_of thy;
  val facts = Global_Theory.facts_of thy';
  val nms = (Facts.dest_static false [prev_facts] facts);
  val realnms = map (fn (_,thms) => filter Thm.has_name_hint thms |> map Thm.get_name_hint) nms |> flat
in
  Synchronized.change transactions (Symtab.map_default (file,[]) (cons ((get_transactionT trans,trans),realnms,(beg,fin)))) end


val _ =
  Outer_Syntax.command @{command_keyword "by"} "terminal backward proof"
    ((fn toks =>
    let
      val (beg,fin) = (Token.pos_of (hd toks),Token.pos_of (List.last toks))
      val file = Position.file_of beg |> the_default ""
      val _ = Synchronized.change transactions (Symtab.map_default (file,[]) (cons ((Qed,"by"),[],(beg,fin))))
    in
      (Method.parse -- Scan.option Method.parse >> Isar_Cmd.terminal_proof) toks
    end))

fun wrap_lthy' ttyp parser toks =
  let
    val (flthy,toks') = parser toks
  in
   ((fn b => fn lthy => let
      val (beg,fin) = (Token.pos_of (hd toks),Token.pos_of (List.last toks))
      val lthy' = flthy b lthy
      val _ = add_new_lemmas (Proof_Context.theory_of lthy) (Proof_Context.theory_of lthy') beg fin ttyp
   in
      lthy' end),toks') end

fun theorems kind =
  Parse_Spec.name_facts -- Parse.for_fixes
    >> (fn (facts, fixes) => #2 oo Specification.theorems_cmd kind facts fixes);

val _ =
  Outer_Syntax.local_theory' @{command_keyword "lemmas"} "define lemmas" (wrap_lthy' "lemmas" (theorems Thm.lemmaK));

fun get_size_report () = Synchronized.value transactions

(* Move to library? *)
fun bracket_list leftbr rightbr superbr l =
let
  fun err () = error ("Mismatched parenthesis: " ^ Position.here @{here})

  fun bracket_list_aux stack pairs extras [] =
      if null stack then (rev pairs,rev extras) else err ()

  |  bracket_list_aux stack pairs extras (x :: l) =
    if leftbr x then bracket_list_aux (x :: stack) pairs extras l
    else if rightbr x then
    case stack of
      (s :: stack') => bracket_list_aux stack' ((s,x) :: pairs) extras l
      | _ => err ()
    else if superbr x then bracket_list_aux [] ((List.last stack,x) :: pairs) extras l
    else bracket_list_aux stack pairs (x :: extras) l
in
  bracket_list_aux [] [] [] l
end

fun merge_duplicates ord merge =
let
  fun merge_duplicates_aux (a :: b :: l) =
  (case (ord (a,b)) of
      EQUAL => merge_duplicates_aux ((merge a b) :: l)
    | GREATER => error "Merging duplicates requires sorted list"
    | _ => a :: (merge_duplicates_aux (b :: l)))

    | merge_duplicates_aux x = x
in
  merge_duplicates_aux
end


fun to_tuple pos = (Position.line_of pos, Position.offset_of pos)

fun pos_ord (pos1,pos2) = (prod_ord (option_ord int_ord) (option_ord int_ord)) (to_tuple pos1,to_tuple pos2)

datatype lemmaT = Lemma of string | Declare of string


fun compute_sizes (transactions) =
  let

    fun trans_less (Start,Qed) = true
       | trans_less (Start,Declaration) = true
       | trans_less (Qed,Declaration) = true
       | trans_less (Start,Qed_Global) = true
       | trans_less (Qed_Global,Declaration) = true
       | trans_less _ = false

    fun do_prod (((trans,_),_,(st1,_)),((trans',_),_,(st2,_))) = ((st1,trans),(st2,trans'))

    val ord = (prod_ord pos_ord (make_ord trans_less)) o do_prod

    fun proc_entry (_,trans) =
      let
        val _ = map (fn  ((Unknown,_),_,_) =>
                  error "Unexpected Unknown transaction in count report"
                | _ => ()) trans

        val sorted_transactions = sort ord trans
        |> merge_duplicates ord (fn (t,nms,s) => fn (_,nms',_) => (t,merge (op =) (nms,nms'),s))

        val (paired,singles) = bracket_list
            (fn ((t,_),_,_) => t = Start)
            (fn ((t,_),_,_) => t = Qed)
            (fn ((t,_),_,_) => t = Qed_Global)
            sorted_transactions

        fun fix_range ((x,xs,(st1,_)),(_,ys,(_,fin2))) = (x,xs @ ys,(st1,fin2))
      in
        (map fix_range paired) @ singles end

      fun translate_trans t nm = case t of Start => Lemma nm
                                      | Declaration => Declare nm
                                      | _ => error "Unexpected transaction type"
  in
    fold (append o proc_entry) (Symtab.dest transactions) []
    |> map (fn (t,facts,range) => map (rpair (t,range)) facts)
    |> flat
    |> Symtab.make_list
    |> Symtab.map (fn _ => fn k => find_first (fn (_,(p,p')) => Option.isSome (Position.line_of p) andalso Option.isSome (Position.line_of p')) k |> the_default (hd k))
    |> Symtab.delete_safe ""
    |> Symtab.map (fn _ => fn ((t,nm),range) => (translate_trans t nm,range))
end

(*FIXME: Redundant?*)
val _ = Toplevel.add_hook (fn trans => fn state => fn state' =>
        if needs_hook (Toplevel.name_of trans) then
          (let
            val pos = Toplevel.pos_of trans
            val name = Toplevel.name_of trans

            val thy = Toplevel.theory_of state
            val thy' = Toplevel.theory_of state'

          in
            add_new_lemmas thy thy' pos pos name end)
        else ())


end
