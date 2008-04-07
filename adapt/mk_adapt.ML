(*  ID:         $Id: Importer.hs 632 2008-02-27 06:02:00Z rittweil $
    Author:     Florian Haftmann, TU Muenchen

Decorate importer adaption table with current Isabelle syntax.
*)

signature MK_ADAPT =
sig
  val run: string -> string -> unit;
end;

structure MkAdapt : MK_ADAPT =
struct

fun run src_loc dst_loc =
  let
    val _ = writeln ("Reading from " ^ src_loc);
    val _ = writeln ("Writing to" ^ dst_loc);
  in () end;

end;
