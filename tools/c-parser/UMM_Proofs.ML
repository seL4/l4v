(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(* FIXME: all this should work on Proof.context or local_thy, not theory *)
signature UMM_PROOFS =
sig
  type T

  val umm_empty_state : T
  val umm_finalise : T -> theory -> theory

  val umm_struct_calculation :
      ((string * (string * typ * int Absyn.ctype) list) * T * theory) ->
      T * theory

  val umm_array_calculation : typ -> int -> T -> theory -> T * theory

end

structure UMM_Proof_Theorems = Theory_Data (
      type T = thm list Symtab.table;
      val empty = Symtab.empty
      val extend = I
      val merge = Symtab.join (fn _ => fn (lhs, rhs) =>
        sort_distinct Thm.thm_ord (lhs @ rhs))
    )

structure UMM_Proofs : UMM_PROOFS =
struct

(* Add a list of theorems to our theory data. *)
fun add_data_thms thms thy =
  UMM_Proof_Theorems.map (
    fold (fn (k,v) => Symtab.map_default (k, []) (fn a => v @ a)) thms) thy

open TermsTypes NameGeneration UMM_TermsTypes

type T = {
     starttime     : Time.time,
     fg_thms       : thm list,
     typ_info_thms : thm list,
     td_names_thms : thm list,
     typ_name_thms : thm list,
     upd_lift_thms : thm list,
     upd_other_thms : thm list,
     size_align_thms : thm list,
     fl_Some_thms    : thm list,
     fl_ti_thms    : thm list,
     records_done  : string Binaryset.set,
     arrayeltypes_done : typ Binaryset.set,
     structsize_done  : string Binaryset.set, (* name of struct type *)
     szclass_done : (string * string) Binaryset.set
                    (* name of struct type coupled with sizeclass *)
};

val umm_empty_state =
    {starttime = Time.now (),
     fg_thms = [],
     typ_info_thms = [],
     td_names_thms = [],
     typ_name_thms = [],
     upd_lift_thms = [],
     upd_other_thms = [],
     size_align_thms = [],
     fl_Some_thms = [],
     fl_ti_thms = [],
     records_done = Binaryset.empty String.compare,
     arrayeltypes_done = Binaryset.empty typ_ord,
     structsize_done = Binaryset.empty String.compare,
     szclass_done = Binaryset.empty (pair_compare(String.compare, String.compare))};

(* Should these be prefixed by e.g. parser_ ?  They can be added to the simpset somewhere else *)
fun umm_finalise st thy = let
    val thms = [(("fg_cons_simps", #fg_thms st), []), (* alread in ss *)
                (("typ_info_simps", #typ_info_thms st), []),
                (("td_names_simps", #td_names_thms st), []), (* alread in ss *)
                (("typ_name_simps", #typ_name_thms st), [Simplifier.simp_add]),
                (("upd_lift_simps", #upd_lift_thms st),  [(* Simplifier.simp_add *)]),
                (("upd_other_simps", #upd_other_thms st), [(* Simplifier.simp_add *)]),
                (("size_align_simps", #size_align_thms st), []), (* already in ss *)
                (("fl_Some_simps", #fl_Some_thms st), []), (* These should be intro simps *)
                (("fl_ti_simps", #fl_ti_thms st), [Simplifier.simp_add])
               ]

    fun mapthis ((nm,thms),attrs) = ((Binding.name nm, thms), attrs)
    val (_, thy) = Global_Theory.add_thmss (map mapthis thms) thy

    (* Record the theorems in the theory data. *)
    val thy = add_data_thms (map fst thms) thy
in
    thy
end;

fun add_st_thms fgs tis tds tns uts uos sas fls fltis
             {starttime, fg_thms, typ_info_thms, td_names_thms, typ_name_thms,
              upd_lift_thms, upd_other_thms, size_align_thms, fl_Some_thms,
              fl_ti_thms, records_done, arrayeltypes_done, structsize_done,
              szclass_done} =
    { starttime = starttime,
      fg_thms = fgs @ fg_thms,
      typ_info_thms = tis @ typ_info_thms,
      td_names_thms = tds @ td_names_thms,
      typ_name_thms = tns @ typ_name_thms,
      upd_lift_thms = uts @ upd_lift_thms,
      upd_other_thms = uos @ upd_other_thms,
      size_align_thms = sas @ size_align_thms,
      fl_Some_thms = fls @ fl_Some_thms,
      fl_ti_thms = fltis @ fl_ti_thms,
      records_done = records_done,
      arrayeltypes_done = arrayeltypes_done,
      structsize_done = structsize_done,
      szclass_done = szclass_done
    }

fun add_record_done nm {starttime, fg_thms, typ_info_thms, td_names_thms,
                        typ_name_thms, upd_lift_thms, upd_other_thms,
                        size_align_thms, fl_Some_thms, fl_ti_thms,
                        records_done, arrayeltypes_done, structsize_done,
                        szclass_done} =
    {starttime = starttime,
     fg_thms = fg_thms,
     typ_info_thms = typ_info_thms,
     td_names_thms = td_names_thms,
     typ_name_thms = typ_name_thms,
     upd_lift_thms = upd_lift_thms,
     upd_other_thms = upd_other_thms,
     size_align_thms = size_align_thms,
     fl_Some_thms = fl_Some_thms,
     fl_ti_thms = fl_ti_thms,
     records_done = Binaryset.add(records_done, nm),
     arrayeltypes_done = arrayeltypes_done,
     structsize_done = structsize_done,
     szclass_done = szclass_done}

fun add_array_done i {starttime, fg_thms, typ_info_thms, td_names_thms,
                      typ_name_thms, upd_lift_thms, upd_other_thms,
                      size_align_thms, fl_Some_thms, fl_ti_thms,
                      records_done, arrayeltypes_done, structsize_done,
                      szclass_done} =
    {starttime = starttime,
     fg_thms = fg_thms,
     typ_info_thms = typ_info_thms,
     td_names_thms = td_names_thms,
     typ_name_thms = typ_name_thms,
     upd_lift_thms = upd_lift_thms,
     upd_other_thms = upd_other_thms,
     size_align_thms = size_align_thms,
     fl_Some_thms = fl_Some_thms,
     fl_ti_thms = fl_ti_thms,
     records_done = records_done,
     arrayeltypes_done = Binaryset.add(arrayeltypes_done, i),
     structsize_done = structsize_done,
     szclass_done = szclass_done}

fun add_structsize_done i {starttime, fg_thms, typ_info_thms, td_names_thms,
                        typ_name_thms, upd_lift_thms, upd_other_thms,
                        size_align_thms, fl_Some_thms, fl_ti_thms,
                        records_done, arrayeltypes_done, structsize_done,
                        szclass_done} =
    {starttime = starttime,
     fg_thms = fg_thms,
     typ_info_thms = typ_info_thms,
     td_names_thms = td_names_thms,
     typ_name_thms = typ_name_thms,
     upd_lift_thms = upd_lift_thms,
     upd_other_thms = upd_other_thms,
     size_align_thms = size_align_thms,
     fl_Some_thms = fl_Some_thms,
     fl_ti_thms = fl_ti_thms,
     records_done = records_done,
     arrayeltypes_done = arrayeltypes_done,
     structsize_done = Binaryset.add(structsize_done, i),
     szclass_done = szclass_done}

fun add_szclass_done i {starttime, fg_thms, typ_info_thms, td_names_thms,
                        typ_name_thms, upd_lift_thms, upd_other_thms,
                        size_align_thms, fl_Some_thms, fl_ti_thms,
                        records_done, arrayeltypes_done, structsize_done,
                        szclass_done} =
    {starttime = starttime,
     fg_thms = fg_thms,
     typ_info_thms = typ_info_thms,
     td_names_thms = td_names_thms,
     typ_name_thms = typ_name_thms,
     upd_lift_thms = upd_lift_thms,
     upd_other_thms = upd_other_thms,
     size_align_thms = size_align_thms,
     fl_Some_thms = fl_Some_thms,
     fl_ti_thms = fl_ti_thms,
     records_done = records_done,
     arrayeltypes_done = arrayeltypes_done,
     structsize_done = structsize_done,
     szclass_done = Binaryset.add(szclass_done, i)}

fun phase st recname s =
    let
        val tm = (Time.now ()) - (#starttime st)
    in
        Feedback.informStr (2, "PHASE " ^ s ^ " " ^ recname ^ " " ^
                        LargeInt.toString (Time.toMilliseconds tm))
    end

val size_td_simps_arr =
    @{thms "size_td_simps"} @
    [@{thm "typ_info_array"}, @{thm "array_tag_def"},
     @{thm "align_td_array_tag"}]

val size_td_simps_arr_fl =
    @{thms "size_td_simps"} @
    [@{thm "size_td_array"}, @{thm "align_td_array"}, @{thm "max_def"}]

fun umm_mem_type recname recty typtag_thm tag_def_thm thy = let
  val _ = Feedback.informStr (0, "Proving UMM inversion for type "^recname^"... ")
  val ctxt0 = thy2ctxt thy
  val mem_type_instance_t =
      Logic.mk_of_class(recty, "CTypesDefs.mem_type")

  (* typ_tag TYPE('a struct_scheme) = struct_tag_def *)
  val t_def_thms = [typtag_thm, tag_def_thm, @{thm "align_of_def"},
                    @{thm "size_of_def"}]
  val t_def_step = ALLGOALS (asm_full_simp_tac (ctxt0 addsimps t_def_thms))

  (* wf_desc *)
  val wf_desc_Is = ctxt0 addIs [@{thm "wf_desc_final_pad"},
                                @{thm "wf_desc_ti_typ_pad_combine"}]
  val wf_desc_step = force_tac wf_desc_Is 1

  (* wf_size_desc *)
  val wf_size_desc_Is =
      ctxt0 addIs
      [@{thm "wf_size_desc_ti_typ_pad_combine"}, @{thm "wf_size_desc_final_pad"}]
  val wf_size_desc_step = force_tac wf_size_desc_Is 1

  (* wf_lf *)
  infix addsimps'
  fun op addsimps' (ctxt, thms) =
      Context.proof_map (Simplifier.map_ss (fn ss => ss addsimps thms)) ctxt
  val wf_lf_Is =
      ctxt0
        addIs [@{thm "wf_lf_final_pad"}, @{thm "wf_lf_ti_typ_pad_combine"},
               @{thm "wf_desc_final_pad"}, @{thm "wf_desc_ti_typ_pad_combine"},
               @{thm "g_ind_ti_typ_pad_combine"}, @{thm "f_ind_ti_typ_pad_combine"},
               @{thm "fa_ind_ti_typ_pad_combine"}]
        addsimps' [@{thm "comp_def"}]
  val wf_lf_step = force_tac wf_lf_Is 1

  (* At Raf's request - important if screwed *)
  fun dprint_tac s = if !Feedback.verbosity_level > 2 then print_tac ctxt0 s
                     else all_tac

  (* fu_eq_mask *)
  val fu_eq_mask_step = auto_tac ctxt0 THEN
      resolve_tac ctxt0 [@{thm "fu_eq_mask"}] 1 THEN
      dprint_tac "fu_eq_mask [v-2]" THEN
      assume_tac ctxt0 1 THEN
      dprint_tac "fu_eq_mask [v-1]" THEN
      asm_full_simp_tac (ctxt0 addsimps (size_td_simps_arr)) 1 THEN
      dprint_tac "fu_eq_mask [v0]" THEN
      resolve_tac ctxt0 [@{thm "fu_eq_mask_final_pad"}] 1 THEN
      REPEAT (resolve_tac ctxt0 [@{thm "fu_eq_mask_ti_typ_pad_combine"}] 1) THEN
      asm_full_simp_tac (ctxt0 addsimps [
          @{thm "fu_eq_mask_empty_typ_info"}, @{thm "there_is_only_one"}]) 1 THEN
      dprint_tac "fu_eq_mask [v1]" THEN
      REPEAT (dprint_tac "forcing" THEN
              force_tac (ctxt0 addSIs [@{thm "fc_ti_typ_pad_combine"}]
                               addsimps' [@{thm "there_is_only_one"}, @{thm "fg_cons_def"}, @{thm "comp_def"}, @{thm "fu_eq_mask_empty_typ_info"},
                                          @{thm "upd_local_def"}]) 1) THEN
      dprint_tac "fu_eq_mask [v2]"

  val align_dvd_size_step =
      asm_full_simp_tac
          (ctxt0 addsimps [
             @{thm "align_of_def"}, @{thm "size_of_def"}]) 1

  val align_field_step =
      asm_full_simp_tac
          (ctxt0 addsimps [
             @{thm "align_td_array_tag"}, @{thm "align_field_final_pad"},
             @{thm "align_field_ti_typ_pad_combine"},
             @{thm "typ_info_array"}, @{thm "array_tag_def"}]) 1

  val size_lt_step =
      asm_full_simp_tac
          (ctxt0 addsimps
           (size_td_simps_arr @
            [@{thm "addr_card"}, @{thm "align_of_def"},
             @{thm "size_of_def"}, @{thm "align_of_final_pad"}])) 1

  val is_mem_type_thm =
      Goal.prove_future ctxt0 [] [] mem_type_instance_t
       (fn _ => DETERM ((
                Class.intro_classes_tac ctxt0 [] THEN
                dprint_tac "t_def" THEN
                t_def_step THEN
                dprint_tac "wf_desc" THEN
                wf_desc_step THEN
                dprint_tac "wf_size_desc" THEN
                wf_size_desc_step) THEN
                dprint_tac "wf_lf" THEN
                wf_lf_step THEN
                dprint_tac "fu_eq_mask" THEN
                fu_eq_mask_step THEN
                dprint_tac "align_dvd_size" THEN
                align_dvd_size_step THEN
                dprint_tac "align_field" THEN
                align_field_step THEN
                dprint_tac "size_lt" THEN
                size_lt_step))
in
    Axclass.add_arity is_mem_type_thm thy
end;

val packed_type_simps = @{thms "packed_type_intro_simps"}

fun umm_packed_type recname recty typtag_thm tag_def_thm fgthms thy = let
  val _ = Feedback.informStr (0, "Proving UMM packed type for type "^recname^"... ")
  val ctxt0 = thy2ctxt thy
  val packed_type_instance_t =
      Logic.mk_of_class (recty, "PackedTypes.packed_type")
  val packed_type_instance_ct = Thm.cterm_of ctxt0 packed_type_instance_t

  val pt_ss = (ctxt0 addsimps ([typtag_thm, tag_def_thm] @ packed_type_simps @ fgthms))

  (* Try to solve. If we fail, we catch the exception and ignore. *)
  val is_packed_type_thm =
      Goal.prove_internal ctxt0 [] packed_type_instance_ct
       (fn _ => DETERM ((
                ((fn _ => Class.intro_classes_tac ctxt0 []) THEN_ALL_NEW (asm_simp_tac pt_ss)) 1)))
in
    Axclass.add_arity is_packed_type_thm thy
end handle THM _ => (Feedback.informStr (0, "Failed to prove UMM packed type for type "^recname); thy)

exception AlreadyDone
fun calculate_record_size recname (st, thy) ths ty =
  if Binaryset.member(#structsize_done st, recname) then (st, thy)
  else let
      val ctxt = thy2ctxt thy
      val tysize_th =
          Simplifier.rewrite
              ((thy2ctxt thy) addsimps
                          ((@{thm "size_of_def"} :: @{thm "typ_info_array"} ::
                            @{thm "array_tag_def"} :: @{thm "TWO"} ::
                            @{thms "size_td_simps"} @ ths)))
              (Thm.cterm_of ctxt (mk_sizeof (mk_TYPE ty)))
      val _ = let
        val ctxt = thy2ctxt thy
        val size_t = Thm.term_of (Thm.rhs_of tysize_th)
      in
        (* check that it simplifies to a number *)
        numb_to_int size_t
        handle e as TERM _ =>
               (Feedback.informStr (0, "Can't get good computation of size of type " ^
                         recname ^ " (got this RHS: "^
                         Syntax.string_of_term ctxt size_t ^ ")");
                raise e)
      end
      val (thm, thy) = Global_Theory.add_thm ((Binding.name(recname^"_size"),tysize_th),
                                            [Simplifier.simp_add])
                                           thy
      val thy = add_data_thms [("size_simps", [thm])] thy
    in
      (add_structsize_done recname st, thy)
    end

fun umm_struct_calculation ((recname, flds), st, thy) = let
  val _ = not (Binaryset.member (#records_done st, recname)) orelse
          (Feedback.informStr (0, "UMM Proof for "^recname^" already done");
           raise AlreadyDone)

  (* useful stuff for what is to come *)
  val fullrecname = Sign.intern_type thy recname
  val recty = Type(fullrecname, [])

  val phase = phase st recname
  fun trac s = Feedback.informStr (1, recname ^ ": " ^ s)

  val _ = phase "START"

  (* the tag definition for the new type *)
  fun gen_tag_pad flds tag =
      case flds of
        [] => error ("Record ("^recname^") with no fields??")
      | [(fldnm, ty, _)] => mk_tag_pad_tm recty ty fldnm thy $ tag
      | (fldnm, ty, _)::rest =>
          gen_tag_pad rest (mk_tag_pad_tm recty ty fldnm thy $ tag)
  val tag_rhs =
      final_pad_tm recty $ gen_tag_pad flds (empty_tag_tm recty recname)
  val tag_nm = recname^"_tag"
  val thy = prim_mk_defn tag_nm tag_rhs thy
      handle ERROR s => error ("Defining "^tag_nm^" as\n  "^
                               Syntax.string_of_term_global thy tag_rhs ^
                               "\nfailed with message: "^s)
  val tag_tm = Const(Sign.intern_const thy tag_nm, mk_tag_type recty)
  val tag_def_thm = Global_Theory.get_thm thy (tag_nm ^ "_def")
  val _ = phase "MADE TAG DEFN"

  (* the typ_name_itself definition *)
  val typnameitself_lhs =
      Const(@{const_name "typ_name_itself"}, mk_itself_type recty -->
          typ_name_ty) $ Free("x", mk_itself_type recty)
  val typnameitself_rhs = mk_string recname
  val typnameitself_triple =
      ((Binding.name (recname ^ "_typ_name_itself"),
        mk_defeqn(typnameitself_lhs, typnameitself_rhs)),
       [Simplifier.simp_add])

  (* the typ_tag definition *)
  val typtag_lhs = mk_typ_info_tm recty $ Free("x", mk_itself_type recty)
  val typtag_rhs = tag_tm
  val typtag_triple =
      ((Binding.name (recname ^ "_typ_tag"),
        mk_defeqn(typtag_lhs, typtag_rhs)),
       [])

  val typ_info_TYPE = mk_typ_info_of recty

  (* make the definitions *)
  val (typnameitself_thm, typtag_thm, thy) =
      case Global_Theory.add_defs true
                                  [typnameitself_triple, typtag_triple] thy
       of
          ([x,y], thy) => (x,y,thy)
        | _ => raise Fail "UMM_Proofs: Bind error"
  val thy = add_data_thms [("typ_name_itself", [typnameitself_thm])] thy

  val _ = phase "MEMTYPE"
  (* Add the mem_type instance *)
  val thy = umm_mem_type recname recty typtag_thm tag_def_thm thy

  val _ = phase "SIZE"
  val _ = trac "About to size/align..."

  val size_td_thm =
      Simplifier.asm_full_rewrite
          ((thy2ctxt thy) addsimps (size_td_simps_arr @ [tag_def_thm, typtag_thm]))
          (Thm.cterm_of (thy2ctxt thy) (mk_sizetd typ_info_TYPE))
  val (st,thy) = calculate_record_size recname (st,thy) [size_td_thm] recty


  val _ = phase "ALIGN"
  val _ = trac "About to size/align 1..."

  val align_td_thm =
      Simplifier.asm_full_rewrite
          ((thy2ctxt thy) addsimps (size_td_simps_arr
                                    @ [tag_def_thm, typtag_thm, @{thm "align_of_def"}]))
          (Thm.cterm_of (thy2ctxt thy) (mk_aligntd typ_info_TYPE))

  val (recthms,thy) =
      Global_Theory.add_thms [((Binding.name(recname^"_size_of"),size_td_thm),[]),
                              ((Binding.name(recname^"_align_of"),align_td_thm),[])]
                             thy

  val (typtag_thm, thy) =
      Global_Theory.add_thms [((Binding.name(recname ^ "_typ_info"), typtag_thm),[])]
                             thy |> apfst hd

  val _ = phase "TYPNAME"
  val _ = trac "About to type typ_name ..."
  val typ_name_thm =
      Simplifier.asm_full_rewrite
          ((thy2ctxt thy) addsimps [tag_def_thm, typtag_thm])
          (Thm.cterm_of (thy2ctxt thy) (mk_typ_name_of recty))
  val (typ_name_thm, thy) =
      Global_Theory.add_thms [((Binding.name(recname ^ "_typ_name"), typ_name_thm),
                               [Simplifier.simp_add])]
                             thy

  val _ = phase "FL"
  val _ = trac "About to type/field fl..."

  val flthms = let
    val fl_simps = size_td_simps_arr_fl @ @{thms "fl_simps"} @
      [tag_def_thm, typtag_thm]
    fun fl_thm f = ((Binding.name(recname^"_"^(#1 f) ^"_fl"), Drule.export_without_context (
      Simplifier.asm_full_rewrite ((thy2ctxt thy) addsimps fl_simps)
      (Thm.cterm_of (thy2ctxt thy) (mk_field_lookup (recty,#1 f))))),[])
  in
    map fl_thm flds
  end;

  val (flthms,thy) = Global_Theory.add_thms flthms thy
  val thy = add_data_thms [("fl_simps", flthms)] thy

  val _ = phase "FG"
  val _ = trac "About to fg..."
  val fgthms = let
    fun fg_thm f = Goal.prove_future (thy2ctxt thy) [] []
      (mk_prop (mk_fg_cons_tm recty (#2 f) (#1 f) thy))
      (fn _ => asm_full_simp_tac
          ((thy2ctxt thy) addsimps [@{thm "fg_cons_def"}, @{thm comp_def}]) 1)
  in
    map fg_thm flds
  end;

  val _ = phase "PACKEDTYPE"
  val thy = umm_packed_type recname recty typtag_thm tag_def_thm fgthms thy

  val _ = phase "FLSOME"
  val _ = trac "About to type/field fl_Some ..."
  val fl_Some_thms = let
      fun fl_thm' (fl, (name, _, _)) = let
          val concl_lhs = mk_field_lookup_nofs (recty, name)
          val thm =
              Simplifier.asm_full_rewrite ((thy2ctxt thy) addsimps [fl])
                                          (Thm.cterm_of (thy2ctxt thy) concl_lhs) |>
                                          Drule.export_without_context
      in
          ((Binding.name(recname^ "_" ^ name ^ "_fl_Some"), thm), [])
      end
  in
      map fl_thm' (flthms ~~ flds)
  end
  val (fl_Some_thms, thy) = Global_Theory.add_thms fl_Some_thms thy

  val _ = phase "FLTI"
  val _ = trac "About to type/field fl_ti ..."
  val fl_ti_thms = let
      val rl = @{thm "field_lookup_field_ti"}

      fun fl_thm' (fl_Some, (name, _, _)) = let
          val thm = rl OF [fl_Some]
      in
          ((Binding.name(recname^ "_" ^ name ^ "_fl_ti"), thm), [])
      end
  in
      map fl_thm' (fl_Some_thms ~~ flds)
  end
  val (fl_ti_thms, thy) = Global_Theory.add_thms fl_ti_thms thy

  val upd_lift_thms = []
  val upd_lift_other_thms = []

  val _ = phase "NAMES"
  val _ = trac "About to td_names ..."
  val td_names_name = recname ^ "_td_names";
  val td_names_thm =
      Simplifier.asm_full_rewrite
          ((thy2ctxt thy) addsimps
                      [tag_def_thm, typtag_thm,
                       @{thm "pad_typ_name_def"}, @{thm "insert_commute"},
                       @{thm "nat_to_bin_string.simps"}])
          (Thm.cterm_of (thy2ctxt thy) (mk_td_names typtag_lhs)) |> Drule.export_without_context

  (* Declare the td_names (typ_info_t ..) = ... and add it to the simpset *)
  val (td_names_thm, thy) =
      Global_Theory.add_thms [((Binding.name td_names_name, td_names_thm),
                               [Simplifier.simp_add])]
                             thy

  val thy =
      thy |> Context.theory_map
               (Simplifier.map_ss
                    (fn ss => ss addsimps (recthms @ flthms @ fgthms)))
  val _ = phase "END"
  val _ = trac "done"
in
  (st |> add_st_thms fgthms [typtag_thm] td_names_thm typ_name_thm
                     upd_lift_thms upd_lift_other_thms recthms
                     fl_Some_thms fl_ti_thms
      |> add_record_done recname,
   thy)
end handle TYPE (s, tps, ts) => let
             val _ = Feedback.informStr (0, "EXN: " ^ s)
           in
             raise (TYPE (s, tps, ts))
           end
         | AlreadyDone => (st,thy)


fun prove_type_in_szclass (st, thy) ty szclass =  let
  val tyname = Syntax.string_of_typ (thy2ctxt thy) ty
in
  if Binaryset.member(#szclass_done st, (tyname, szclass)) then (st, thy)
  else let
      fun tac thy _ =
          Class.intro_classes_tac(thy2ctxt thy) [] THEN asm_full_simp_tac (thy2ctxt thy) 1

      val instance_t = Logic.mk_of_class(ty, szclass)
      val instance_thm =
          Goal.prove_future (thy2ctxt thy) [] [] instance_t (tac thy)
      val thy = Axclass.add_arity instance_thm thy
      val st = add_szclass_done (tyname, szclass) st
    in
      Output.state("Proved "^tyname^" :: "^szclass);
      (st, thy)
    end
end


  (* prove that the new type is an instance of the class finite *)
  (* prove that the new type is an instance of the class array_max_count *)
fun umm_array_calculation el_ty n st thy = let
  val _ = Feedback.informStr (0, "Proving that an array of "^Int.toString n^" "^
                   Syntax.string_of_typ (thy2ctxt thy) el_ty ^" is a mem_type")

  (* Unlike in the struct case, we don't need to establish the new type as
     a c_type, because the array operator has already been declared to do this
     by the
        instance array :: (type,finite) c_type ..
     line in ArraysMemInstance.thy.

     So we can get straight onto showing that the array type is in mem_type.
     This is done exploiting the fact that we have the following instance
     in our context already

        instance array :: (array_outer_max_size, array_max_count) mem_type

     Thanks to the neat instance declarations in ArchArraysMemInstance.thy
     (all those classes with names lt<n>), the array_max_count for
     the array size will be handled automatically by type-checking.

     This means that we just need to do one independent instance proofs,
     for el_ty :: array_outer_max_size

     Even that may be done automatically, for certain element types.  For
     example all the word types have this happen through

       instance word :: (len8) array_outer_max_size
       instance word_length8 :: len8
       instance word_length16 :: len8
       instance word_length32 :: len8
       instance word_length64 :: len8

     Structures can't be done this way, so those need to get done by hand.

     Arrays get to use the

       instance array :: (array_inner_max_size, array_max_count) array_outer_max_size

     information.

  *)
in
  if Binaryset.member(#arrayeltypes_done st, el_ty) then (st, thy)
  else let
      fun ex() = error ("Can't compute an element size class for " ^
                        Syntax.string_of_typ (thy2ctxt thy) el_ty)
      val (tyname, args) = case el_ty of Type p => p | _ => ex()
      val (st,thy) =
          case args of
            [] => (* will be a record type *)
                  prove_type_in_szclass (st, thy) el_ty "ArchArraysMemInstance.array_outer_max_size"
          | [_] => (* can compute sizes for words and ptrs *)
            if tyname = @{type_name "Word.word"} then (st, thy)
            else if tyname = @{type_name "CTypesBase.ptr"} then (st, thy)
            else ex()
          | [a,_] => let
              val _ = tyname = @{type_name "array"} orelse
                      error "Binary type operator is not array."
              (* a is an element type and must be in array_inner_max_size *)
              val (atyname, aargs) = case a of Type p => p
                                             | _ => error "Array eltype is not Type"
            in
              case aargs of
                [] => prove_type_in_szclass (st,thy) a "ArchArraysMemInstance.array_inner_max_size"
              | [_] => if atyname = @{type_name "word"} orelse
                           atyname = @{type_name "ptr"}
                        then (st, thy)
                        else error ("Unary operator type "^atyname^" not word or ptr")
              | _ => ex()
            end
          | _ => ex()
    in
      (add_array_done el_ty st, thy)
    end
end

end; (* struct *)
