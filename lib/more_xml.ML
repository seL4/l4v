(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(* Poor man's extension to Isabelle's poverty-striken XML library. *)


(* Encoding strings to XML. *)

fun xml_list name attr value =
    XML.Elem ((name, attr), value);

fun xml_node name value =
    xml_list name [] [XML.Text value]

fun xml_attrib_node name attribs value =
    xml_list name attribs [XML.Text value]

(* Decoding XML. Poor error handling, sorry. *)

fun xml_unwrap_node root =
  case root of
    XML.Text _ => error ("Could not unwrap element.")
  | XML.Elem (_, x) => x

fun xml_unwrap_attributes root =
  case root of
    XML.Text _ => error ("Could not unwrap element.")
  | XML.Elem ((_, x), _) => x

fun xml_get_text root =
  case (xml_unwrap_node root) of
    [XML.Text x] => x
  | _ => error ("Expected a single node with a single text element.")

fun xml_node_name root =
  case root of
    XML.Text _ => error ("Expected node, but got string.")
  | XML.Elem ((x,_), _) => x

fun xml_get_child name root =
  (xml_unwrap_node root)
  |> filter (fn n => xml_node_name n = name)

fun xml_get_attrib name root =
  (xml_unwrap_attributes root)
  |> map_filter (fn (n, v) => if n = name then SOME v else NONE)
  |> hd

