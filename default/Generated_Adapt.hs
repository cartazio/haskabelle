-- THIS IS A GENERATED FILE - DO NOT EDIT!
-- Haskell syntax is only superficial.

module Generated_Adapt where

raw_adaption_table = [(Haskell "Prelude.Eq" (Class (RawClassInfo { superclasses = [], classVar = "a", methods = [("Prelude.(==)", "a -> a -> bool"), ("Prelude.(/=)", "a -> a -> bool")] })), Isabelle "Prelude.eq" (Class (RawClassInfo { superclasses = [], classVar = "a", methods = [("Prelude.(==)", "a -> a -> bool"), ("Prelude.(/=)", "a -> a -> bool")] }))),
  (Haskell "Prelude.Ord" (Class (RawClassInfo { superclasses = [], classVar = "a", methods = [("Prelude.(<=)", "a -> a -> bool"), ("Prelude.(<)", "a -> a -> bool")] })), Isabelle "Prelude.ord" (Class (RawClassInfo { superclasses = [], classVar = "a", methods = [("Prelude.(<=)", "a -> a -> bool"), ("Prelude.(<)", "a -> a -> bool")] }))),
  (Haskell "Prelude.Show" (Class (RawClassInfo { superclasses = [], classVar = "a", methods = [("Prelude.show", "a -> String")] })), Isabelle "Prelude.print" (Class (RawClassInfo { superclasses = [], classVar = "a", methods = [("Prelude.show", "a -> String")] }))),
  (Haskell "Prelude.Num" (Class (RawClassInfo { superclasses = [], classVar = "a", methods = [] })), Isabelle "Prelude.num" (Class (RawClassInfo { superclasses = [], classVar = "a", methods = [] }))),
  (Haskell "Prelude.Bool" Type, Isabelle "HOL.bool" Type),
  (Haskell "Prelude.UnitTyCon" Type, Isabelle "Product_Type.unit" Type),
  (Haskell "Prelude.PairTyCon" Type, Isabelle "Product_Type.prod" Type),
  (Haskell "Prelude.ListTyCon" Type, Isabelle "List.list" Type),
  (Haskell "Prelude.Maybe" Type, Isabelle "Option.option" Type),
  (Haskell "Prelude.Char" Type, Isabelle "String.char" Type),
  (Haskell "Prelude.String" Type, Isabelle "String.string" Type),
  (Haskell "Prelude.Int" Type, Isabelle "Int.int" Type),
  (Haskell "Prelude.Integer" Type, Isabelle "Int.int" Type),
  (Haskell "Prelude.True" Function, Isabelle "HOL.True" Function),
  (Haskell "Prelude.False" Function, Isabelle "HOL.False" Function),
  (Haskell "Prelude.not" Function, Isabelle "HOL.Not" Function),
  (Haskell "Prelude.(&&)" Function, Isabelle "&" (InfixOp RightAssoc 35)),
  (Haskell "Prelude.(||)" Function, Isabelle "|" (InfixOp RightAssoc 30)),
  (Haskell "Prelude._|_" Function, Isabelle "HOL.undefined" Function),
  (Haskell "Prelude.error" Function, Isabelle "Prelude.error" Function),
  (Haskell "Prelude.($)" Function, Isabelle "$" (InfixOp RightAssoc 60)),
  (Haskell "Prelude.const" Function, Isabelle "Prelude.const" Function),
  (Haskell "Prelude.id" Function, Isabelle "Fun.id" Function),
  (Haskell "Prelude.(.)" Function, Isabelle "o" (InfixOp LeftAssoc 55)),
  (Haskell "Prelude.curry" Function, Isabelle "Prelude.curry" Function),
  (Haskell "Prelude.uncurry" Function, Isabelle "Prelude.uncurry" Function),
  (Haskell "Prelude.(==)" Function, Isabelle "Prelude.eq_class.eq" Function),
  (Haskell "Prelude.(/=)" Function, Isabelle "Prelude.eq_class.not_eq" Function),
  (Haskell "Prelude.(())" Function, Isabelle "Product_Type.Unity" Function),
  (Haskell "Prelude.PairDataCon" Function, Isabelle "Product_Type.Pair" Function),
  (Haskell "Prelude.fst" Function, Isabelle "Product_Type.fst" Function),
  (Haskell "Prelude.snd" Function, Isabelle "Product_Type.snd" Function),
  (Haskell "Prelude.([])" Function, Isabelle "List.list.Nil" Function),
  (Haskell "Prelude.(:)" Function, Isabelle "#" (InfixOp RightAssoc 65)),
  (Haskell "Prelude.null" Function, Isabelle "Prelude.null" Function),
  (Haskell "Prelude.head" Function, Isabelle "List.hd" Function),
  (Haskell "Prelude.tail" Function, Isabelle "List.tl" Function),
  (Haskell "Prelude.map" Function, Isabelle "List.map" Function),
  (Haskell "Prelude.filter" Function, Isabelle "List.filter" Function),
  (Haskell "Prelude.(++)" Function, Isabelle "@" (InfixOp RightAssoc 65)),
  (Haskell "Prelude.concat" Function, Isabelle "List.concat" Function),
  (Haskell "Prelude.reverse" Function, Isabelle "List.rev" Function),
  (Haskell "Prelude.elem" Function, Isabelle "Prelude.member" Function),
  (Haskell "Prelude.notElem" Function, Isabelle "Prelude.not_member" Function),
  (Haskell "Prelude.replicate" Function, Isabelle "Prelude.replicate" Function),
  (Haskell "Prelude.(!!)" Function, Isabelle "Prelude.nth" Function),
  (Haskell "Prelude.length" Function, Isabelle "Prelude.length" Function),
  (Haskell "Prelude.any" Function, Isabelle "List.list_ex" Function),
  (Haskell "Prelude.all" Function, Isabelle "List.list_all" Function),
  (Haskell "Prelude.zip" Function, Isabelle "List.zip" Function),
  (Haskell "Prelude.foldl" Function, Isabelle "List.foldl" Function),
  (Haskell "Prelude.foldr" Function, Isabelle "List.foldr" Function),
  (Haskell "Prelude.Nothing" Function, Isabelle "Option.option.None" Function),
  (Haskell "Prelude.Just" Function, Isabelle "Option.option.Some" Function),
  (Haskell "Prelude.maybe" Function, Isabelle "Prelude.maybe" Function),
  (Haskell "Prelude.show" Function, Isabelle "Prelude.print_class.print" Function),
  (Haskell "Prelude.(+)" Function, Isabelle "+" (InfixOp LeftAssoc 65)),
  (Haskell "Prelude.(*)" Function, Isabelle "*" (InfixOp LeftAssoc 70)),
  (Haskell "Prelude.negate" Function, Isabelle "Groups.uminus_class.uminus" Function),
  (Haskell "Prelude.(-)" Function, Isabelle "-" (InfixOp LeftAssoc 65)),
  (Haskell "Prelude.(<)" Function, Isabelle "<" (InfixOp NoneAssoc 50)),
  (Haskell "Prelude.(<=)" Function, Isabelle "<=" (InfixOp NoneAssoc 50)),
  (Haskell "Prelude.(>)" Function, Isabelle ">" (InfixOp NoneAssoc 50)),
  (Haskell "Prelude.(>=)" Function, Isabelle ">=" (InfixOp NoneAssoc 50)),
  (Haskell "Prelude.abs" Function, Isabelle "Groups.abs_class.abs" Function),
  (Haskell "Prelude.sgn" Function, Isabelle "Groups.sgn_class.sgn" Function),
  (Haskell "Prelude.fromInteger" Function, Isabelle "Int.ring_1_class.of_int" Function),
  (Haskell "Prelude.divMod" Function, Isabelle "Divides.divmod_int" Function),
  (Haskell "Prelude.min" Function, Isabelle "Orderings.ord_class.min" Function),
  (Haskell "Prelude.max" Function, Isabelle "Orderings.ord_class.max" Function)]

reserved_keywords = ["!",
  "!!",
  "%",
  "(",
  ")",
  "+",
  ",",
  "--",
  ".",
  "..",
  "/",
  ":",
  "::",
  ";",
  "<",
  "<=",
  "=",
  "==",
  "=>",
  "?",
  "Isabelle.command",
  "ML",
  "ML_command",
  "ML_prf",
  "ML_val",
  "ProofGeneral.inform_file_processed",
  "ProofGeneral.inform_file_retracted",
  "ProofGeneral.kill_proof",
  "ProofGeneral.pr",
  "ProofGeneral.process_pgip",
  "ProofGeneral.restart",
  "ProofGeneral.undo",
  "[",
  "\\<equiv>",
  "\\<leftharpoondown>",
  "\\<rightharpoonup>",
  "\\<rightleftharpoons>",
  "\\<subseteq>",
  "]",
  "abbreviation",
  "advanced",
  "also",
  "and",
  "apply",
  "apply_end",
  "arities",
  "assume",
  "assumes",
  "attach",
  "attribute_setup",
  "ax_specification",
  "axiomatization",
  "axioms",
  "back",
  "begin",
  "binder",
  "by",
  "by",
  "cannot_undo",
  "case",
  "cd",
  "chapter",
  "checking",
  "class",
  "class_deps",
  "classes",
  "classrel",
  "code_abort",
  "code_class",
  "code_const",
  "code_datatype",
  "code_deps",
  "code_include",
  "code_instance",
  "code_library",
  "code_module",
  "code_modulename",
  "code_monad",
  "code_pred",
  "code_reflect",
  "code_reserved",
  "code_thms",
  "code_type",
  "coinductive",
  "coinductive_set",
  "commit",
  "congs",
  "constrains",
  "consts",
  "consts_code",
  "contains",
  "context",
  "corollary",
  "datatype",
  "datatypes",
  "declaration",
  "declare",
  "def",
  "default_sort",
  "defer",
  "defer_recdef",
  "defines",
  "definition",
  "defs",
  "disable_pr",
  "display_drafts",
  "done",
  "enable_pr",
  "end",
  "example_proof",
  "exit",
  "export_code",
  "extract",
  "extract_type",
  "file",
  "finalconsts",
  "finally",
  "find_consts",
  "find_theorems",
  "fix",
  "fixes",
  "for",
  "from",
  "full_prf",
  "fun",
  "function",
  "functions",
  "guess",
  "have",
  "header",
  "help",
  "hence",
  "hide_class",
  "hide_const",
  "hide_fact",
  "hide_type",
  "hints",
  "identifier",
  "if",
  "imports",
  "in",
  "inductive",
  "inductive_cases",
  "inductive_set",
  "inductive_simps",
  "infix",
  "infixl",
  "infixr",
  "init_toplevel",
  "instance",
  "instantiation",
  "interpret",
  "interpretation",
  "is",
  "judgment",
  "kill",
  "kill_thy",
  "lemma",
  "lemmas",
  "let",
  "linear_undo",
  "local_setup",
  "locale",
  "method_setup",
  "module_name",
  "monos",
  "moreover",
  "morphisms",
  "next",
  "nitpick",
  "nitpick_params",
  "no_notation",
  "no_syntax",
  "no_translations",
  "no_type_notation",
  "nonterminals",
  "notation",
  "note",
  "notes",
  "obtain",
  "obtains",
  "oops",
  "open",
  "oracle",
  "output",
  "overloaded",
  "overloading",
  "parse_ast_translation",
  "parse_translation",
  "permissive",
  "pervasive",
  "pr",
  "prefer",
  "presume",
  "pretty_setmargin",
  "prf",
  "primrec",
  "print_abbrevs",
  "print_antiquotations",
  "print_ast_translation",
  "print_attributes",
  "print_binds",
  "print_cases",
  "print_claset",
  "print_classes",
  "print_codeproc",
  "print_codesetup",
  "print_commands",
  "print_configs",
  "print_context",
  "print_drafts",
  "print_facts",
  "print_induct_rules",
  "print_interps",
  "print_locale",
  "print_locales",
  "print_methods",
  "print_orders",
  "print_quotconsts",
  "print_quotients",
  "print_quotmaps",
  "print_rules",
  "print_simpset",
  "print_statement",
  "print_syntax",
  "print_theorems",
  "print_theory",
  "print_trans_rules",
  "print_translation",
  "proof",
  "prop",
  "pwd",
  "qed",
  "quickcheck",
  "quickcheck_params",
  "quit",
  "quotient_definition",
  "quotient_type",
  "realizability",
  "realizers",
  "recdef",
  "recdef_tc",
  "record",
  "refute",
  "refute_params",
  "remove_thy",
  "rep_datatype",
  "schematic_corollary",
  "schematic_lemma",
  "schematic_theorem",
  "sect",
  "section",
  "setup",
  "show",
  "shows",
  "simproc_setup",
  "sledgehammer",
  "sledgehammer_params",
  "smt_status",
  "sorry",
  "specification",
  "structure",
  "subclass",
  "sublocale",
  "subsect",
  "subsection",
  "subsubsect",
  "subsubsection",
  "syntax",
  "term",
  "termination",
  "text",
  "text_raw",
  "then",
  "theorem",
  "theorems",
  "theory",
  "thm",
  "thm_deps",
  "thus",
  "thy_deps",
  "translations",
  "try",
  "txt",
  "txt_raw",
  "typ",
  "type_notation",
  "typed_print_translation",
  "typedecl",
  "typedef",
  "types",
  "types_code",
  "ultimately",
  "unchecked",
  "undo",
  "undos_proof",
  "unfolding",
  "unused_thms",
  "use",
  "use_thy",
  "uses",
  "using",
  "value",
  "values",
  "welcome",
  "where",
  "with",
  "write",
  "{",
  "|",
  "}"]

used_const_names = ["==",
  "==>",
  "Abs_Integ",
  "Abs_Nat",
  "Abs_Node",
  "Abs_char",
  "Abs_fin_fun",
  "Abs_fun_box",
  "Abs_lazy_sequence",
  "Abs_list",
  "Abs_nibble",
  "Abs_option",
  "Abs_pair_box",
  "Abs_pattern",
  "Abs_pred",
  "Abs_prod",
  "Abs_seq",
  "Abs_sum",
  "Abs_sumbool",
  "Abs_term",
  "Abs_tuple_isomorphism",
  "Abs_typerep",
  "Abs_unit",
  "Abs_word",
  "All",
  "Babs",
  "Ball",
  "Bex",
  "Bex1_rel",
  "Char",
  "Collect",
  "Cons",
  "Domain",
  "DomainP",
  "Eps",
  "Ex",
  "Ex1",
  "False",
  "Field",
  "Greatest",
  "GreatestM",
  "INFI",
  "Id",
  "Id_on",
  "If",
  "Image",
  "In0",
  "In1",
  "Inf",
  "Inf_class",
  "Inf_fin",
  "Inl",
  "Inl_Rep",
  "Inr",
  "Inr_Rep",
  "Integ",
  "Ints",
  "Least",
  "LeastM",
  "Left",
  "Let",
  "ListMem",
  "Max",
  "Min",
  "Nat",
  "Nats",
  "Nibble0",
  "Nibble1",
  "Nibble2",
  "Nibble3",
  "Nibble4",
  "Nibble5",
  "Nibble6",
  "Nibble7",
  "Nibble8",
  "Nibble9",
  "NibbleA",
  "NibbleB",
  "NibbleC",
  "NibbleD",
  "NibbleE",
  "NibbleF",
  "Nil",
  "None",
  "Not",
  "Pair",
  "Pair_Rep",
  "Plus",
  "Pow",
  "Powp",
  "Push_Node",
  "Quot_True",
  "Quotient",
  "Random_graph",
  "Random_rel",
  "Random_sumC",
  "Range",
  "RangeP",
  "Rep_Integ",
  "Rep_Nat",
  "Rep_Node",
  "Rep_char",
  "Rep_fin_fun",
  "Rep_fun_box",
  "Rep_lazy_sequence",
  "Rep_list",
  "Rep_nibble",
  "Rep_option",
  "Rep_pair_box",
  "Rep_pattern",
  "Rep_pred",
  "Rep_prod",
  "Rep_seq",
  "Rep_sum",
  "Rep_sumbool",
  "Rep_term",
  "Rep_tuple_isomorphism",
  "Rep_typerep",
  "Rep_unit",
  "Rep_word",
  "Respects",
  "Right",
  "STR",
  "SUPR",
  "Scons",
  "Sigma",
  "Some",
  "Suc",
  "Suc_Rep",
  "Suc_code_numeral",
  "Sup",
  "Sup_class",
  "Sup_fin",
  "THE_default",
  "TYPE",
  "The",
  "True",
  "Trueprop",
  "Unity",
  "Zero_Rep",
  "ab_group_add_class",
  "ab_semigroup_add_class",
  "ab_semigroup_idem_mult_class",
  "ab_semigroup_mult_class",
  "abel_semigroup",
  "abel_semigroup_axioms",
  "abs",
  "abs_class",
  "abs_if_class",
  "acc",
  "accp",
  "acyclic",
  "adjust",
  "adm_wf",
  "all",
  "anamorph",
  "anamorph_graph",
  "anamorph_rel",
  "anamorph_sumC",
  "antisym",
  "apfst",
  "append",
  "apsnd",
  "atLeast",
  "atLeastAtMost",
  "atLeastLessThan",
  "atMost",
  "bij_betw",
  "bool_case",
  "bool_rec",
  "bool_rec_set",
  "bool_size",
  "boolean_algebra_class",
  "bot",
  "bot_class",
  "bounded_lattice_bot_class",
  "bounded_lattice_class",
  "bounded_lattice_top_class",
  "butlast",
  "cancel_ab_semigroup_add_class",
  "cancel_comm_monoid_add_class",
  "cancel_semigroup_add_class",
  "card",
  "char_case",
  "char_rec",
  "char_rec_set",
  "char_rep_set",
  "char_size",
  "chars",
  "code_numeral_case",
  "code_numeral_rec",
  "code_numeral_rec_set",
  "code_numeral_size",
  "comm_monoid",
  "comm_monoid_add_class",
  "comm_monoid_axioms",
  "comm_monoid_big",
  "comm_monoid_big_axioms",
  "comm_monoid_mult_class",
  "comm_ring_1_class",
  "comm_ring_class",
  "comm_semiring_0_cancel_class",
  "comm_semiring_0_class",
  "comm_semiring_1_cancel_class",
  "comm_semiring_1_cancel_crossproduct_class",
  "comm_semiring_1_class",
  "comm_semiring_class",
  "comp",
  "complete_lattice_class",
  "compow",
  "concat",
  "congruent",
  "congruent2",
  "conj",
  "contained",
  "converse",
  "conversep",
  "cut",
  "default",
  "default_class",
  "dense_linorder_class",
  "disj",
  "distinct",
  "distrib_lattice_class",
  "div",
  "div_class",
  "div_mod_code_numeral",
  "divide",
  "division_ring_class",
  "division_ring_inverse_zero_class",
  "divmod_int",
  "divmod_int_rel",
  "divmod_nat",
  "divmod_nat_rel",
  "dom",
  "dprod",
  "drop",
  "dropWhile",
  "dsum",
  "dummy_pattern",
  "dvd",
  "dvd_class",
  "embed_list",
  "eq",
  "eq_class",
  "equal_class",
  "equiv",
  "equivp",
  "error",
  "eval_graph",
  "eval_rel",
  "eval_sumC",
  "explode",
  "fcomp",
  "field_class",
  "field_inverse_zero_class",
  "filter",
  "fin_fun_case",
  "fin_fun_rec",
  "fin_fun_rec_set",
  "fin_fun_rep_set",
  "fin_fun_size",
  "finite",
  "finite_class",
  "finite_psubset",
  "fold",
  "fold1",
  "fold1Set",
  "fold_graph",
  "fold_image",
  "folding",
  "folding_idem",
  "folding_idem_axioms",
  "folding_image",
  "folding_image_axioms",
  "folding_image_idem",
  "folding_image_idem_axioms",
  "folding_image_simple",
  "folding_image_simple_axioms",
  "folding_image_simple_idem",
  "folding_image_simple_idem_axioms",
  "folding_one",
  "folding_one_axioms",
  "folding_one_idem",
  "folding_one_idem_axioms",
  "foldl",
  "foldr",
  "fst",
  "fun_box_case",
  "fun_box_rec",
  "fun_box_rec_set",
  "fun_box_rep_set",
  "fun_box_size",
  "fun_left_comm",
  "fun_left_comm_idem",
  "fun_left_comm_idem_axioms",
  "fun_map",
  "fun_rel",
  "fun_upd",
  "gfp",
  "greaterThan",
  "greaterThanAtMost",
  "greaterThanLessThan",
  "group_add_class",
  "hb_bind",
  "hb_flat",
  "hb_if_seq",
  "hb_map",
  "hb_not_seq",
  "hb_single",
  "hd",
  "hit_bound",
  "id",
  "idom_class",
  "image",
  "implies",
  "in_rel",
  "inf",
  "inj_on",
  "insert",
  "insort_insert",
  "insort_key",
  "int_ge_less_than",
  "int_ge_less_than2",
  "intrel",
  "inv_image",
  "inv_imagep",
  "inv_into",
  "inverse",
  "inverse_class",
  "irrefl",
  "is_measure",
  "is_nat",
  "isomorphic_tuple",
  "iszero",
  "iter'_graph",
  "iter'_rel",
  "iter'_sumC",
  "iter_graph",
  "iter_rel",
  "iter_sumC",
  "iterate_graph",
  "iterate_rel",
  "iterate_sumC",
  "last",
  "lattice_class",
  "lazy_sequence_case",
  "lazy_sequence_rec",
  "lazy_sequence_rec_set",
  "lazy_sequence_rep_set",
  "lazy_sequence_size",
  "lenlex",
  "less",
  "lessThan",
  "less_eq",
  "less_than",
  "lex",
  "lex_prod",
  "lexn",
  "lexord",
  "lfp",
  "linorder_class",
  "linordered_ab_group_add_class",
  "linordered_ab_semigroup_add_class",
  "linordered_cancel_ab_semigroup_add_class",
  "linordered_comm_semiring_strict_class",
  "linordered_field_class",
  "linordered_field_inverse_zero_class",
  "linordered_idom_class",
  "linordered_ring_class",
  "linordered_ring_strict_class",
  "linordered_semidom_class",
  "linordered_semiring_1_class",
  "linordered_semiring_1_strict_class",
  "linordered_semiring_class",
  "linordered_semiring_strict_class",
  "list_all",
  "list_all2",
  "list_case",
  "list_ex",
  "list_rec",
  "list_rec_set",
  "list_rep_set",
  "list_size",
  "list_update",
  "listrel",
  "listrelp",
  "lists",
  "listset",
  "listsp",
  "listsum",
  "log_graph",
  "log_rel",
  "log_sumC",
  "map",
  "map_add",
  "map_comp",
  "map_le",
  "map_of",
  "map_seq_graph",
  "map_seq_rel",
  "map_seq_sumC",
  "map_upds",
  "max",
  "max_ext",
  "max_extp",
  "max_strict",
  "max_weak",
  "measure",
  "measures",
  "member",
  "min",
  "min_ext",
  "min_strict",
  "min_weak",
  "minus",
  "minus_class",
  "mlex_prod",
  "mod",
  "mono",
  "monoid",
  "monoid_add_class",
  "monoid_axioms",
  "monoid_mult_class",
  "mult_zero_class",
  "mutual_random_auxtyperep",
  "nat",
  "nat_case",
  "nat_gcd_graph",
  "nat_gcd_rel",
  "nat_gcd_sumC",
  "nat_list",
  "nat_of_aux",
  "nat_rec",
  "nat_rec_set",
  "nat_set",
  "nat_size",
  "ndepth",
  "neg",
  "negDivAlg",
  "negDivAlg_graph",
  "negDivAlg_rel",
  "negDivAlg_sumC",
  "negateSnd",
  "nibble_case",
  "nibble_pair_of_char",
  "nibble_rec",
  "nibble_rec_set",
  "nibble_rep_set",
  "nibble_size",
  "no_zero_divisors_class",
  "norm_frac_graph",
  "norm_frac_rel",
  "norm_frac_sumC",
  "not_eq",
  "ntrunc",
  "num_class",
  "number_class",
  "number_of",
  "number_ring_class",
  "of_int",
  "of_nat",
  "of_nat_aux",
  "one_class",
  "option_case",
  "option_rec",
  "option_rec_set",
  "option_rep_set",
  "option_size",
  "order_class",
  "ordered_ab_group_add_abs_class",
  "ordered_ab_group_add_class",
  "ordered_ab_semigroup_add_class",
  "ordered_ab_semigroup_add_imp_le_class",
  "ordered_cancel_ab_semigroup_add_class",
  "ordered_cancel_comm_semiring_class",
  "ordered_cancel_semiring_class",
  "ordered_comm_monoid_add_class",
  "ordered_comm_ring_class",
  "ordered_comm_semiring_class",
  "ordered_ring_abs_class",
  "ordered_ring_class",
  "ordered_semiring_class",
  "override_on",
  "pair_box_case",
  "pair_box_rec",
  "pair_box_rec_set",
  "pair_box_rep_set",
  "pair_box_size",
  "pair_leq",
  "pair_less",
  "part_equivp",
  "partition",
  "pattern_case",
  "pattern_rec",
  "pattern_rec_set",
  "pattern_rep_set",
  "pattern_size",
  "pdivmod",
  "plus",
  "plus_class",
  "posDivAlg",
  "posDivAlg_graph",
  "posDivAlg_rel",
  "posDivAlg_sumC",
  "power",
  "power_class",
  "pred_case",
  "pred_comp",
  "pred_nat",
  "pred_rec",
  "pred_rec_set",
  "pred_rep_set",
  "pred_size",
  "preorder_class",
  "print",
  "print_class",
  "prod",
  "prod_case",
  "prod_fun",
  "prod_rec",
  "prod_rec_set",
  "prod_size",
  "prop",
  "quot_type",
  "quotient",
  "ran",
  "random_aux_code_numeral",
  "random_aux_fin_fun",
  "random_aux_fun_box",
  "random_aux_lazy_sequence",
  "random_aux_list",
  "random_aux_nibble",
  "random_aux_option",
  "random_aux_pair_box",
  "random_aux_pattern",
  "random_aux_pred",
  "random_aux_prod",
  "random_aux_seq",
  "random_aux_sum",
  "random_aux_sumbool",
  "random_aux_term",
  "random_aux_tuple_isomorphism",
  "random_aux_typerep",
  "random_aux_typerep_list",
  "random_aux_unit",
  "random_aux_word",
  "random_class",
  "reduction_pair",
  "refl_on",
  "reflp",
  "rel_comp",
  "remdups",
  "remove1",
  "removeAll",
  "restrict_map",
  "return_list",
  "rev",
  "ring_1_class",
  "ring_1_no_zero_divisors_class",
  "ring_char_0_class",
  "ring_class",
  "ring_div_class",
  "ring_no_zero_divisors_class",
  "rotate",
  "rotate1",
  "rp_inv_image",
  "rtrancl",
  "rtranclp",
  "same_fst",
  "scomp",
  "semigroup",
  "semigroup_add_class",
  "semigroup_mult_class",
  "semilattice",
  "semilattice_axioms",
  "semilattice_big",
  "semilattice_big_axioms",
  "semilattice_inf_class",
  "semilattice_sup_class",
  "semiring_0_cancel_class",
  "semiring_0_class",
  "semiring_1_cancel_class",
  "semiring_1_class",
  "semiring_char_0_class",
  "semiring_class",
  "semiring_div_class",
  "separate",
  "seq_case",
  "seq_rec",
  "seq_rec_set",
  "seq_rep_set",
  "seq_size",
  "set",
  "set_Cons",
  "setprod",
  "setsum",
  "sgn",
  "sgn_class",
  "sgn_if_class",
  "simp_implies",
  "single_valued",
  "size",
  "size_class",
  "snd",
  "sort_key",
  "sorted",
  "sorted_list_of_set",
  "splice",
  "strict_mono",
  "sublist",
  "subtract_code_numeral",
  "sum",
  "sum_case",
  "sum_rec",
  "sum_rec_set",
  "sum_size",
  "sumbool_case",
  "sumbool_rec",
  "sumbool_rec_set",
  "sumbool_rep_set",
  "sumbool_size",
  "sup",
  "surj_on",
  "sym",
  "symp",
  "take",
  "takeWhile",
  "term_case",
  "term_of_class",
  "term_rec",
  "term_rec_set",
  "term_rep_set",
  "term_size",
  "the",
  "the_default",
  "the_elem",
  "the_inv_into",
  "times",
  "times_class",
  "tl",
  "top",
  "top_class",
  "total_on",
  "trancl",
  "tranclp",
  "trans",
  "transfer_morphism",
  "transp",
  "transpose",
  "transpose_graph",
  "transpose_rel",
  "transpose_sumC",
  "tsub",
  "tuple_isomorphism_case",
  "tuple_isomorphism_rec",
  "tuple_isomorphism_rec_set",
  "tuple_isomorphism_rep_set",
  "tuple_isomorphism_size",
  "type_class",
  "type_definition",
  "typerep_Rep_1",
  "typerep_case",
  "typerep_class",
  "typerep_of",
  "typerep_rec_1",
  "typerep_rec_2",
  "typerep_rec_set",
  "typerep_rec_set_1",
  "typerep_rec_set_2",
  "typerep_rep_set",
  "typerep_rep_set_1",
  "typerep_rep_set_2",
  "typerep_size",
  "uminus",
  "uminus_class",
  "uncurry",
  "undefined",
  "unit",
  "unit_case",
  "unit_rec",
  "unit_rec_set",
  "unit_size",
  "uprod",
  "upt",
  "upto",
  "upto_graph",
  "upto_rel",
  "upto_sumC",
  "usum",
  "vimage",
  "wellorder_class",
  "wf",
  "wfP",
  "wfrec",
  "wfrec_rel",
  "word_case",
  "word_rec",
  "word_rec_set",
  "word_rep_set",
  "word_size",
  "yield",
  "yieldn",
  "zero_class",
  "zero_neq_one_class",
  "zip"]

used_thy_names = ["ATP",
  "Archimedean_Field",
  "Big_Operators",
  "Code_Evaluation",
  "Code_Generator",
  "Code_Numeral",
  "Complete_Lattice",
  "Complex",
  "Complex_Main",
  "DSequence",
  "Datatype",
  "Deriv",
  "Divides",
  "Equiv_Relations",
  "Extraction",
  "Fact",
  "Fields",
  "Finite_Set",
  "Fun",
  "FunDef",
  "GCD",
  "Groebner_Basis",
  "Groups",
  "HOL",
  "Hilbert_Choice",
  "Inductive",
  "Int",
  "Lattices",
  "Lazy_Sequence",
  "Lim",
  "Limits",
  "List",
  "Ln",
  "Log",
  "Lubs",
  "MacLaurin",
  "Main",
  "Map",
  "Meson",
  "Metis",
  "Nat",
  "Nat_Numeral",
  "Nat_Transfer",
  "New_DSequence",
  "New_Random_Sequence",
  "Nitpick",
  "NthRoot",
  "Numeral_Simprocs",
  "Option",
  "Orderings",
  "Parity",
  "Plain",
  "Power",
  "Predicate",
  "Predicate_Compile",
  "Prelude",
  "Presburger",
  "Product_Type",
  "Pure",
  "Quickcheck",
  "Quotient",
  "RComplete",
  "Random",
  "Random_Sequence",
  "Rat",
  "Real",
  "RealDef",
  "RealVector",
  "Recdef",
  "Record",
  "Refute",
  "Relation",
  "Rings",
  "SAT",
  "SEQ",
  "SMT",
  "Semiring_Normalization",
  "Series",
  "Set",
  "SetInterval",
  "Sledgehammer",
  "String",
  "Sum_Type",
  "SupInf",
  "Taylor",
  "Transcendental",
  "Transitive_Closure",
  "Typedef",
  "Typerep",
  "Wellfounded"]
