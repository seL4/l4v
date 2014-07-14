(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

structure CcorresUnderlying =
struct

(* Finds a subterm matching p and returns it and it's arguments, otherwise NONE *)
fun find_subterm (p : term -> bool)
		 (tm : term) : (term * term list) option = let
    fun find_subterm' (args : term list) (tm : term) =
	if p tm then SOME (tm, args)
	else case tm of
		 Abs (n, tp, tm') => find_subterm' [] tm'
	       | tm' $ tm''       => 
		 (case find_subterm' (tm'' :: args) tm' of
		     SOME x       => SOME x
		   | NONE         => find_subterm' [] tm'')
	       | _                => NONE (* this would have been picked up in 
                                              the 'if p tm then ...' *)		  
in
    find_subterm' [] tm
end

val cul_prefix = "ccorres_underlying"
val cul_fullname = fst (dest_Const @{term "ccorres_underlying"})

(* Extract the names and types of sr and gamma in thm *)
fun is_cul x = is_Const x andalso fst (dest_Const x) = cul_fullname

val thm_to_cul = find_subterm is_cul o Thm.prop_of

structure cul_rules = GenericDataFun
(struct
    val name = "HOL/cul/rules"
    type T = thm list
    val empty = []
    val extend = I
    fun merge _ = Thm.merge_thms;
    fun print context rules =
        Pretty.writeln (Pretty.big_list "correspondence underlying rules:"
        (map (ProofContext.pretty_thm (Context.proof_of context)) rules));
end);

exception NO_CCORRES
val cul_add = Thm.declaration_attribute 
                    (fn thm => if isSome (thm_to_cul thm) then
				   (cul_rules.map (Thm.add_thm thm))
			       else raise NO_CCORRES);

val cul_del = Thm.declaration_attribute 
                    (fn thm =>                      
                        (cul_rules.map (Thm.del_thm thm))); 
  
val setup = 
  Attrib.add_attributes
            [("cul_standard", Attrib.add_del_args cul_add cul_del, 
              "underlying correspondence rules")];
	    
local structure P = ProofContext in

fun instantiate_one_ccorres 
	(lthy  : local_theory)
	(sr    : cterm)
	(gamma : cterm)
	(thm   : thm) : thm = let

    (* This should be checked in cul_add *)
    val (SOME (_, (Var (sr_nm, sr_tp)) :: (Var (gamma_nm, gamma_tp)) :: _))
      = thm_to_cul thm 

    (* sr has type (a x b) set, while gamma has type (b, ...) so it is sufficient to 
       destroy sr's type. Yuck, though *)
    val thy         = P.theory_of lthy
    fun dest_set tp = 
	case tp of
	    (Type ("set", [Type ("*", [a, b])])) => (a, b)
	  | _ => raise Bind
		   
    val sr_tp'      = typ_of (ctyp_of_term sr)
    val gamma_tp'   = typ_of (ctyp_of_term gamma)
    val (a, b)      = dest_set (typ_of (ctyp_of_term sr))
    val (a', b')    = dest_set sr_tp
    val gamma'      = cterm_of thy (Var (gamma_nm, gamma_tp'))
    val sr'         = cterm_of thy (Var (sr_nm, sr_tp'))
    fun mkinst a' a = if is_TVar a' then [(ctyp_of thy a', ctyp_of thy a)] else []
    val instT       = mkinst a' a @ mkinst b' b
in
    Thm.instantiate (instT, [(sr', sr), (gamma', gamma)]) thm
end;
	
exception NOT_PREFIX
(* Specialises corres for a particular gamma and sr *)

fun specialise_ccorres_lemmas (locale : string)
			       (prefix : string)
			       (srn     : string)
			       (gamman  : string)
			       (thy   : theory) : theory = let
(*
    val _    = tracing ("instantiate_ccorres: " ^ locale ^ " " ^ prefix ^ " " ^ dname ^ " " ^ gamma ^ " " ^ sr)
 *)
    val lthy = TheoryTarget.context locale thy
    val thms = cul_rules.get (Context.Proof lthy)
    val read_term = P.read_term_abbrev lthy
    val cert = cterm_of (P.theory_of lthy) o P.cert_term lthy

    val sr       = read_term srn
    val gamma    = read_term gamman
    val rhs      = Syntax.check_term lthy (Const (cul_fullname, dummyT) $ sr $ gamma )

    val sr_c     = cert sr
    val gamma_c  = cert gamma		  

    val ((_, (_, def)), lthy') 
      = LocalTheory.define Thm.definitionK ((prefix, NoSyn), (("", []), rhs)) lthy
    (* Not sure why I need to do this ... *)
    val lthy'' = LocalTheory.restore lthy'
    val def'   = Morphism.thm (P.export_morphism lthy' lthy'') def

    fun trace s x = let val _ = tracing s in x end

    fun specialise (thm, l) = let
	val thm' = instantiate_one_ccorres l sr_c gamma_c thm
					   |> LocalDefs.fold l [def']
	val name = NameSpace.base (Thm.get_name thm)
	val name' = if String.isPrefix cul_prefix name
		    then prefix ^ (String.extract (name, size cul_prefix, NONE))
		    else raise NOT_PREFIX
    in
	snd (LocalTheory.note "specialise" ((name', []), [thm']) l) |> 
	trace ("Defined theorem: " ^ name')
    end handle NOT_PREFIX => 
	       (let 
		    val _ = tracing ("Warning: ignoring theorem (Pfx) " ^ Thm.get_name thm)
		in 
		    l
		end)
	     | Bind => 
		      (let 
			   val _ = tracing ("Warning: ignoring theorem (Bind) " ^ Thm.get_name thm)
		       in 
			   l
		       end);	

    val lthy'' = foldl specialise lthy'' thms
in
    P.theory_of (LocalTheory.exit (LocalTheory.restore lthy''))
end;

end;

local structure P = OuterParse and K = OuterKeyword in

val instant_command =
    OuterSyntax.command 
        "instantiate_ccorres" 
        "Instantiate ccorres lemmas for a particular theory.  Arguments are (all strings): locale name, desired theorem prefix, the state relation, and gamma"
        K.thy_decl
        (P.name -- P.name -- P.name -- P.name 
		>> (fn (((locale, prefix), sr), gamma) => 
		       Toplevel.theory (specialise_ccorres_lemmas locale prefix sr gamma)))

end;  
end
								   
