(*  ID:         $Id: Importer.hs 632 2008-02-27 06:02:00Z rittweil $
    Author:     Florian Haftmann, TU Muenchen

Decorate importer adaption table with current Isabelle syntax.
*)

signature MK_ADAPT =
sig
  val run: theory -> string -> string -> unit;
end;

structure MkAdapt : MK_ADAPT =
struct

fun run thy src_loc dst_loc =
  let
    val src = File.read (Path.explode src_loc);
    val _ = writeln ("Reading from " ^ src_loc);
    val dsts = ["-- THIS IS A GENERATED FILE - DO NOT EDIT!",
      "-- $Id$", ""];
    val _ = File.write (Path.explode dst_loc) (cat_lines dsts);
    val _ = writeln ("Written to " ^ dst_loc);
  in () end;

end;
