(*  Author:  Florian Haftmann, TU Muenchen

Decorate Haskabelle adaptation table with current Isabelle syntax.
*)

signature MK_ADAPT =
sig
  val run: string -> string -> string -> unit
end;

structure Mk_Adapt : MK_ADAPT =
struct

(* used constant symbols *)

fun used_constants thy = []
  |> Symtab.fold (fn (c, (_, NONE)) => cons c | _ => I)
       ((snd o #constants o Consts.dest o Sign.consts_of) thy)
  |> map (Proof_Context.extern_const (Proof_Context.init_global thy))
  |> filter_out Long_Name.is_qualified;


(* concrete output syntax *)

fun assert_class thy class = Sign.certify_class thy class
  handle TYPE _ => error ("Not a class: " ^ quote class);
fun assert_type thy tyco = if Symtab.defined ((snd o #types o Type.rep_tsig o Sign.tsig_of) thy) tyco
  then tyco else error ("Not a type constructor: " ^ quote tyco);
fun assert_const thy const = if Symtab.defined ((snd o #constants o Consts.dest o Sign.consts_of) thy) const
  then const else error ("Not a constant: " ^ quote const);
  
fun check_class thy = assert_class thy o Sign.intern_class thy;
fun check_type thy = assert_type thy o Sign.intern_type thy;
fun check_const thy = assert_const thy o Sign.intern_const thy;

fun mk_classentry thy (((hs, raw_isa), raw_super), params) =
  let
    val isa = check_class thy raw_isa;
    val super = map (check_class thy) raw_super;
    val s_super = enclose "[" "]" (commas_quote super);
    val s_params = enclose "[" "]" (commas (map (fn (n, t) => "(" ^ quote n ^ ", " ^ quote t ^ ")") params));
    val s_entry = "(Class (RawClassInfo { superclasses = " ^ s_super ^ ", classVar = \"a\", methods = "
      ^ s_params ^ " }))";
    val s = "(Haskell " ^ quote hs ^ " " ^ s_entry ^ ", Isabelle " ^ quote isa ^ " " ^ s_entry ^ ")";
  in s end;

fun mk_typentry thy (hs, raw_isa) =
  let
    val isa = check_type thy raw_isa;
    val s = "(Haskell " ^ quote hs ^ " Type, Isabelle "
      ^ quote isa ^ " Type)";
  in s end;

fun mk_constentry thy (hs, raw_isa) =
  let
    val isa = check_const thy raw_isa;
    val syn = Syntax.guess_infix (Sign.syn_of thy) (Lexicon.mark_const isa);
    fun string_of_syn NONE = (isa, "Function")
      | string_of_syn (SOME (Infix (s, j))) =
          (s, enclose "(" ")" ("InfixOp NoneAssoc " ^ string_of_int j))
      | string_of_syn (SOME (Infixl (s, j))) = 
          (s, enclose "(" ")" ("InfixOp LeftAssoc " ^ string_of_int j))
      | string_of_syn (SOME (Infixr (s, j))) = 
          (s, enclose "(" ")" ("InfixOp RightAssoc " ^ string_of_int j))
      | string_of_syn _ = raise Match;
    val (sym, syn') = string_of_syn syn;
    val s = "(Haskell " ^ quote hs ^ " Function, Isabelle "
      ^ quote sym ^ " " ^ syn' ^ ")";
  in s end;


(* concrete input syntax *)

val classesN = "classes";
val superclassN = "superclass";
val parameterN = "parameter";
val typesN = "types";
val constsN = "consts";

val adapt_lexicon = Scan.make_lexicon (map Symbol.explode
  [classesN, superclassN, parameterN, typesN, constsN]);

fun classes thy = Parse.$$$ classesN |--
  Scan.repeat1 (Parse.name -- Parse.name
    -- Scan.optional (Scan.repeat1 (Parse.$$$ superclassN |-- Parse.name)) []
    -- Scan.optional (Scan.repeat1 (Parse.$$$ parameterN |-- Parse.name -- Parse.string)) []
    >> mk_classentry thy);
fun types thy = Parse.$$$ typesN |--
  Scan.repeat1 (Parse.name -- Parse.name >> mk_typentry thy);
fun consts thy = Parse.$$$ constsN |--
  Scan.repeat1 (Parse.name -- Parse.name >> mk_constentry thy);

fun adapt thy = (
     classes thy @@@ Scan.optional (types thy) [] @@@ Scan.optional (consts thy) []
  || types thy @@@ Scan.optional (consts thy) []
  || consts thy) >> (space_implode ",\n  " #> enclose "[" "]");

fun convert thy pos = Source.of_string
  #> Symbol.source
  #> Token.source { do_recover = NONE } (fn () => (adapt_lexicon, Scan.empty_lexicon)) pos
  #> Token.source_proper
  #> Source.source Token.stopper (Scan.single (Scan.error (Parse.!!! (adapt thy)))) NONE
  #> Source.exhaust
  #> (fn [dst] => dst | _ => error ("Extra input " ^ Position.here pos))


(* glueing it together *)

val prep_string =
  translate_string (fn "\\" => "\\\\" | s => s)
  #> quote
  #> Pretty.str;

fun run thy_name src_loc dst_loc =
  let
    val thy = Thy_Info.get_theory thy_name;
    val _ = writeln ("Reading from " ^ src_loc);
    val src = File.read (Path.explode src_loc);
    val dst_path = Path.explode dst_loc;
    val modl_name = (Path.implode o fst o Path.split_ext o Path.base) dst_path;
    val adaptions = convert thy (Position.file src_loc) src;
    val enumerate_sorted = sort string_ord #> map prep_string #> map single
      #> separate [Pretty.str ",", Pretty.fbrk] #> flat #> Pretty.enclose "[" "]";
    val keywords = enumerate_sorted (op @ (Keyword.dest ()));
    val const_names = enumerate_sorted (used_constants thy);
    val thy_names = enumerate_sorted (Thy_Info.get_names ());
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

end;
