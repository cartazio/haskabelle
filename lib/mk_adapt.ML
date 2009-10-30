(*  Author:  Florian Haftmann, TU Muenchen

Decorate importer adaption table with current Isabelle syntax.
*)

signature MK_ADAPT =
sig
  val run: theory -> string -> string -> unit;
end;

structure Mk_Adapt : MK_ADAPT =
struct

(* used constant symbols *)

fun used_constants thy = []
  |> Symtab.fold (fn (c, (_, NONE)) => cons c | _ => I)
       ((snd o #constants o Consts.dest o #consts o Sign.rep_sg) thy)
  |> map (Sign.extern_const thy)
  |> filter_out Long_Name.is_qualified;


(* concrete output syntax *)

fun mk_classentry _ (((hs, isa), super), params) =
  let
    val s_super = enclose "[" "]" (commas_quote super);
    val s_params = enclose "[" "]" (commas (map (fn (n, t) => "(" ^ quote n ^ ", " ^ quote t ^ ")") params));
    val s_entry = "(Class (RawClassInfo { superclasses = " ^ s_super ^ ", classVar = \"a\", methods = "
      ^ s_params ^ " }))";
    val s = "(Haskell " ^ quote hs ^ " " ^ s_entry ^ ", Isabelle " ^ quote isa ^ " " ^ s_entry ^ ")";
  in s end;

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
      | string_of_syn _ = raise Match;
    val (sym, syn') = string_of_syn syn;
    val s = "(Haskell " ^ quote hs ^ " Function, Isabelle "
      ^ quote sym ^ " " ^ syn' ^ ")";
  in s end;


(* concrete input syntax *)

structure T = OuterLex;
structure P = OuterParse;

val classesN = "classes";
val superclassN = "superclass";
val parameterN = "parameter";
val typesN = "types";
val constsN = "consts";

val adapt_lexicon = Scan.make_lexicon (map Symbol.explode
  [classesN, superclassN, parameterN, typesN, constsN]);

fun classes thy = P.$$$ classesN |--
  Scan.repeat1 (P.name -- P.name
    -- Scan.optional (Scan.repeat1 (P.$$$ superclassN |-- P.name)) []
    -- Scan.optional (Scan.repeat1 (P.$$$ parameterN |-- P.name -- P.string)) []
    >> mk_classentry thy);
fun types thy = P.$$$ typesN |--
  Scan.repeat1 (P.name -- P.name >> mk_typentry thy);
fun consts thy = P.$$$ constsN |--
  Scan.repeat1 (P.name -- P.name >> mk_constentry thy);

fun adapt thy = (
     classes thy @@@ Scan.optional (types thy) [] @@@ Scan.optional (consts thy) []
  || types thy @@@ Scan.optional (consts thy) []
  || consts thy) >> (space_implode ",\n  " #> enclose "[" "]");

fun convert thy pos = Source.of_string
  #> Symbol.source { do_recover = false }
  #> T.source { do_recover = NONE } (fn () => (adapt_lexicon, Scan.empty_lexicon)) pos
  #> T.source_proper
  #> Source.source T.stopper (Scan.single (Scan.error (P.!!! (adapt thy)))) NONE
  #> Source.exhaust
  #> (fn [dst] => dst | _ => error ("Extra input " ^ Position.str_of pos))


(* glueing it together *)

val prep_string =
  translate_string (fn "\\" => "\\\\" | s => s)
  #> quote
  #> Pretty.str;

fun main thy src_loc dst_loc =
  let
    val _ = writeln ("Reading from " ^ src_loc);
    val src = File.read (Path.explode src_loc);
    val dst_path = Path.explode dst_loc;
    val modl_name = (Path.implode o fst o Path.split_ext o Path.base) dst_path;
    val adaptions = convert thy (Position.file src_loc) src;
    val enumerate_sorted = sort string_ord #> map prep_string #> map single
      #> separate [Pretty.str ",", Pretty.fbrk] #> flat #> Pretty.enclose "[" "]";
    val keywords = enumerate_sorted (OuterKeyword.dest_commands () @ OuterKeyword.dest_keywords ());
    val const_names = enumerate_sorted (used_constants thy);
    val thy_names = enumerate_sorted (ThyInfo.get_names ());
    val dsts = ["-- THIS IS A GENERATED FILE - DO NOT EDIT!",
      "-- Haskell syntax is only superficial.",
      "",
      "module " ^ modl_name ^ " where", "",
      "raw_adaption_table = " ^ adaptions, "",
      "reserved_keywords = " ^ Pretty.string_of keywords, "",
      "used_const_names = " ^ Pretty.string_of const_names, "",
      "used_thy_names = " ^ Pretty.string_of thy_names, ""];
    val _ = File.write dst_path (cat_lines dsts);
    val _ = writeln ("Written to " ^ dst_loc);
  in () end;

fun run thy src_loc dst_loc = main thy src_loc dst_loc
  handle ERROR e => (writeln ("ERROR: " ^ e); OS.Process.exit OS.Process.failure);

end;
