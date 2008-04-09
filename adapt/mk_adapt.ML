(*  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Decorate importer adaption table with current Isabelle syntax.
*)

signature MK_ADAPT =
sig
  val run: theory -> string -> string -> unit;
end;

structure MkAdapt : MK_ADAPT =
struct

(* concrete output syntax *)

fun mk_typentry thy (hs, raw_isa) =
  let
    val isa = Sign.intern_type thy raw_isa;
    val s = "(Haskell " ^ quote hs ^ " Type " ^ quote hs ^ ", Isabelle "
      ^ quote isa ^ " Type " ^ quote isa ^ ")";
  in s end;

fun mk_constentry thy (hs, raw_isa) =
  let
    val isa = Sign.intern_const thy raw_isa;
    val syn = ();
    fun string_of_syn () = "Function";
    val syn' = string_of_syn syn;
    val typ = Logic.unvarifyT (Sign.the_const_type thy isa);
    val typ' = Sign.string_of_typ thy typ;
    val s = "(Haskell " ^ quote hs ^ " " ^ syn' ^ " " ^ quote typ' ^ ", Isabelle "
      ^ quote isa ^ " " ^ syn' ^ " " ^ quote typ' ^ ")";
  in s end;


(* concrete input syntax *)

structure T = OuterLex;
structure P = OuterParse;

val typesN = "types";
val constsN = "consts";

val adapt_lexicon = Scan.make_lexicon (map Symbol.explode [typesN, constsN]);

fun types thy = Scan.optional (P.$$$ typesN |--
  Scan.repeat1 (P.name -- P.name >> mk_typentry thy)) [];
fun consts thy = Scan.optional (P.$$$ constsN |--
  Scan.repeat1 (P.name -- P.name >> mk_constentry thy)) [];

fun adapt thy = types thy -- consts thy >> (op @ #> space_implode ",\n" #> enclose "[" "]");

fun convert thy pos = Source.of_string
  #> Symbol.source false
  #> T.source NONE (fn () => (adapt_lexicon, Scan.empty_lexicon)) pos
  #> T.source_proper
  #> Source.source T.stopper (Scan.single (Scan.error (P.!!! (adapt thy)))) NONE
  #> Source.get_single
  #> (fn SOME (dst, _) => dst | _ => error ("Unexpected end of input" ^ Position.str_of pos))

fun run thy src_loc dst_loc =
  let
    val _ = writeln ("Reading from " ^ src_loc);
    val src = File.read (Path.explode src_loc);
    val dsts = ["-- THIS IS A GENERATED FILE - DO NOT EDIT!",
      "-- $" ^ "Id" ^ "$", "", convert thy (Position.file src_loc) src];
    val _ = File.write (Path.explode dst_loc) (cat_lines dsts);
    val _ = writeln ("Written to " ^ dst_loc);
  in () end;

(*

fun read pos src =
  let val res =
    src
    |> Symbol.source false
    |> T.source NONE (fn () => (header_lexicon, Scan.empty_lexicon)) pos
    |> T.source_proper
    |> Source.source T.stopper (Scan.single (Scan.error (P.!!! header))) NONE
    |> Source.get_single;
  in
    (case res of SOME (x, _) => x
    | NONE => error ("Unexpected end of input" ^ Position.str_of pos))
  end;

fun load_thy dir name pos text time =
  let
    val toks = text_src
      |> Symbol.source false
      |> T.source NONE (K (get_lexicons ())) pos
      |> Source.exhausted;
    val trs = toks
      |> toplevel_source false false NONE (K (get_parser ()))
      |> Source.exhaust;
  in () end;
*)

end;
