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

(* used constant symbols *)

fun used_constants thy = []
  |> Symtab.fold (fn (c, (_, NONE)) => cons c | _ => I)
       ((snd o #constants o Consts.dest o #consts o Sign.rep_sg) thy)
  |> map (Sign.extern_const thy)
  |> filter_out NameSpace.is_qualified;


(* concrete output syntax *)

fun mk_typentry thy (hs, raw_isa) =
  let
    val isa = Sign.intern_type thy raw_isa;
    val s = "(Haskell " ^ quote hs ^ " Type, Isabelle "
      ^ quote isa ^ " Type)";
  in s end;

fun mk_constentry thy (hs, raw_isa) =
  let
    val isa = Sign.intern_const thy raw_isa;
    val syn = Syntax.guess_infix (Sign.syn_of thy) (Sign.const_syntax_name thy isa);
    fun string_of_syn NONE = (isa, "Function")
      | string_of_syn (SOME (InfixName (s, j))) =
          (s, enclose "(" ")" ("InfixOp NoneAssoc " ^ string_of_int j))
      | string_of_syn (SOME (InfixlName (s, j))) = 
          (s, enclose "(" ")" ("InfixOp LeftAssoc " ^ string_of_int j))
      | string_of_syn (SOME (InfixrName (s, j))) = 
          (s, enclose "(" ")" ("InfixOp RightAssoc " ^ string_of_int j))
    val (sym, syn') = string_of_syn syn;
    val s = "(Haskell " ^ quote hs ^ " " ^ syn' ^ ", Isabelle "
      ^ quote sym ^ " " ^ syn' ^ ")";
  in s end;


(* concrete input syntax *)

structure T = OuterLex;
structure P = OuterParse;

val typesN = "types";
val constsN = "consts";

val adapt_lexicon = Scan.make_lexicon (map Symbol.explode [typesN, constsN]);

fun types thy = P.$$$ typesN |--
  Scan.repeat1 (P.name -- P.name >> mk_typentry thy);
fun consts thy = P.$$$ constsN |--
  Scan.repeat1 (P.name -- P.name >> mk_constentry thy);

fun adapt thy = (types thy @@@ Scan.optional (consts thy) []
  || consts thy) >> (space_implode ",\n  " #> enclose "[" "]");

fun convert thy pos = Source.of_string
  #> Symbol.source false
  #> T.source NONE (fn () => (adapt_lexicon, Scan.empty_lexicon)) pos
  #> T.source_proper
  #> Source.source T.stopper (Scan.single (Scan.error (P.!!! (adapt thy)))) NONE
  #> Source.exhaust
  #> (fn [dst] => dst | _ => error ("Extra input " ^ Position.str_of pos))


(* glueing it together *)

fun run thy src_loc dst_loc =
  let
    val _ = writeln ("Reading from " ^ src_loc);
    val src = File.read (Path.explode src_loc);
    val dst_path = Path.explode dst_loc;
    val modl_name = (Path.implode o fst o Path.split_ext o Path.base) dst_path;
    val adaptions = convert thy (Position.file src_loc) src;
    val const_names = Pretty.enum "," "[" "]"
      (map (Pretty.str o quote) (used_constants thy));
    val thy_names = Pretty.enum "," "[" "]"
      (map (Pretty.str o quote) (ThyInfo.get_names ()));
    val dsts = ["-- THIS IS A GENERATED FILE - DO NOT EDIT!",
      "-- $" ^ "Id" ^ "$", "",
      "module Importer." ^ modl_name ^ " where", "",
      "import Importer.AdaptTable", "",
      "rawAdaptionTable = " ^ adaptions, "",
      "usedConstNames = " ^ Pretty.string_of const_names, "",
      "usedThyNames = " ^ Pretty.string_of thy_names, ""];
    val _ = File.write dst_path (cat_lines dsts);
    val _ = writeln ("Written to " ^ dst_loc);
  in () end;

end;
