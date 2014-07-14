(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory ProofCount
imports Main
begin

ML {*
signature PROOF_COUNT =
sig
  datatype transaction = Lemma | Done | Lemmas | Crunch | Other | Unknown
  
  val get_size_report : unit -> (transaction * string list * (Position.range)) list Symtab.table
  val compute_sizes : (transaction * string list * Position.range) list Symtab.table ->
    (transaction * Position.range) Symtab.table
  
end

structure Proof_Count : PROOF_COUNT =
struct

datatype transaction = Lemma | Done | Lemmas | Crunch | Other | Unknown

val transactions = Synchronized.var "hooked" (Symtab.empty : ((transaction * string list * Position.range) list) Symtab.table)


val lemmaTs = ["lemma","theorem","schematic_lemma","corollary","schematic_theorem"]
val doneTs = ["done","qed","sorry",".","..","oops"] (* Note oops should result in no facts added, but brackets the lemma*)
val otherTs = ["termination","instance","instantiation"]
val tops = lemmaTs @ doneTs @ otherTs @ ["crunch"]



fun get_trans nm = if member (op =) lemmaTs nm then Lemma
                         else if member (op =) doneTs nm then Done
                         else if member (op =) otherTs nm then Other
                         else case nm of "crunch" => Crunch | _ => error "Unknown transaction type"

(*We explicitly ignore the "real" fact names because this is not what's given in the dependency analysis.*)
(*The "name" tag in the thm is what is picked up by the kernel for creating the proof_bodies*)
fun add_new_lemmas thy thy' beg fin trans =
let
  val file = Position.file_of beg
                       |> the_default ""
  val prev_facts = Global_Theory.facts_of thy;
  val facts = Global_Theory.facts_of thy';
  val nms = (Facts.dest_static [prev_facts] facts);
  val realnms = map (fn (_,thms) => filter Thm.has_name_hint thms |> map Thm.get_name_hint) nms |> flat
in
  Synchronized.change transactions (Symtab.map_default (file,[]) (cons (trans,realnms,(beg,fin)))) end
  

fun setup_hook () = 
Toplevel.add_hook (fn trans => fn state => fn state' => 
        if member (op =) tops (Toplevel.name_of trans) then
          (let
            val pos = Toplevel.pos_of trans
            val name = Toplevel.name_of trans

            val thy = Toplevel.theory_of state
            val thy' = Toplevel.theory_of state'

          in
            add_new_lemmas thy thy' pos pos (get_trans name) end)
        else ());


fun theorems kind toks =
 (Parse_Spec.name_facts -- Parse.for_fixes
    >> (fn (facts, fixes) => (fn b => fn lthy => 
    let 
      val (_,lthy') = Specification.theorems_cmd kind facts fixes b lthy
      val beg = Token.position_of (hd toks)
      val fin = Token.position_of (List.last toks)
    in
      (add_new_lemmas (Proof_Context.theory_of lthy) (Proof_Context.theory_of lthy') beg fin Lemmas;lthy') end))) toks;

val _ =
  Outer_Syntax.local_theory' @{command_spec "lemmas"} "define lemmas" (theorems Thm.lemmaK);



val _ =
  Outer_Syntax.command @{command_spec "by"} "terminal backward proof"
    ((fn toks => 
    let
      val (beg,fin) = (Token.position_of (hd toks),Token.position_of (List.last toks))
      val file = Position.file_of beg |> the_default ""
      val _ = Synchronized.change transactions (Symtab.map_default (file,[]) (cons (Done,[],(beg,fin))))
    in
      (Method.parse -- Scan.option Method.parse >> Isar_Cmd.terminal_proof) toks
    end))
   
fun get_size_report () = Synchronized.value transactions


fun compute_sizes transactions =
  let
  
    fun line_of (pos,_) = the_default ~1 (Position.line_of pos)
    
    fun trans_less (Lemma,Done) = true
       | trans_less _ = false

    val ord = prod_ord int_ord (make_ord trans_less)

    fun do_prod ((trans,_,pos),(trans',_,pos')) = ((line_of pos,trans),(line_of pos',trans'))
 
    fun last_done ((Done,nms,(_,pos)) :: (Lemma,_,_) :: _) = (nms,pos)
      | last_done ((Done,nms,(_,pos)) :: (Lemmas,_,_) :: _) = (nms,pos)
      | last_done ((Done,nms,(_,pos)) :: (Crunch,_,_) :: _) = (nms,pos)
      | last_done ((Done,nms,(_,pos)) :: (Other,_,_) :: _) = (nms,pos)
      | last_done [(Done,nms,(_,pos))] = (nms,pos)
      | last_done (_ :: rest) = last_done rest
      | last_done _ = ([],(Position.none))
       


    fun proc_trans ((Lemma,nms,(pos,_)) :: trans') lemmas =
      let
        val (nms',next_done) = last_done trans'
      in
        (proc_trans trans' ((nms @ nms',(Lemma,(pos,next_done))) :: lemmas)) end
      | proc_trans ((Done,_,_) :: trans') lemmas = proc_trans trans' lemmas
      | proc_trans ((trans_type,nms,pos) :: trans') lemmas = proc_trans trans' ((nms,(trans_type,pos)) :: lemmas)
      | proc_trans [] lemmas = lemmas
        
        
    fun proc_entry (_,trans) =
      let
        val sorted_transactions = sort (ord o do_prod) trans
        val entry = proc_trans sorted_transactions []
      in                                                      
        entry end        
  in
    fold (append o proc_entry) (Symtab.dest transactions) []
    |> map (fn (t,b) => map (rpair b) t)
    |> flat
    |> Symtab.make_list
    |> Symtab.map (fn _ => fn k => find_first (fn (_,(p,p')) => Option.isSome (Position.line_of p) andalso Option.isSome (Position.line_of p')) k |> the_default (hd k)) end
    |> Symtab.delete_safe ""

val _ = setup_hook ()
   

end

*}


end
