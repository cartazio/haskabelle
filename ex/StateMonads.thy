theory StateMonads
imports Main
begin

types 'a StateM = "int => ('a * int)"

constdefs
  return :: "'a => 'a StateM"
  "return a == % s. (a,s)"

  bind :: "'a StateM => ('a => 'b StateM) => 'b StateM"
          (infixl ">>=" 60)
  "bind f g == %s. let (r, s') = f s in g r s'"

constdefs
  get :: "int StateM"
  "get == %s. (s,s)"

  put :: "int => unit StateM"
  "put s == %_. ((),s)"

nonterminals
  dobinds dobind nobind

syntax
  "dobind"  :: "pttrn => 'a => dobind"             ("(_ <-/ _)" 10)
  ""        :: "dobind => dobinds"                 ("_")
  "nobind"  :: "'a => dobind"                      ("_")
  "dobinds" :: "dobind => dobinds => dobinds"      ("(_);//(_)")
  "_do_"     :: "dobinds => 'a => 'a"               ("(do (_);//   (_)//od)" 100)  
syntax (xsymbols)
  "dobind"  :: "pttrn => 'a => dobind"             ("(_ \<leftarrow>/ _)" 10)

translations
  "_do_ (dobinds b bs) e" == "_do_ b (_do_ bs e)"
  "_do_ (nobind b) e"     == "b >>= (%_.e)"
  "do x <- b; e od"       == "b >>= (%x. e)"  


types 'a ErrorM = "(string + 'a) StateM"

constdefs
  returnE :: "'a => 'a ErrorM"
  "returnE == return o Inr"

  bindE :: "'a ErrorM =>  ('a => 'b ErrorM) => 'b ErrorM"
           (infixl ">>=E" 60)
  "bindE f g == bind f (%r. case r of
	                    Inl e => return (Inl e)
	                  | Inr v => g v)"

constdefs
  "throwError == return o Inl"

constdefs
  lift :: "'a StateM => 'a ErrorM"
  "lift f == %s. let (v,s') = f s in (Inr v, s')"

  whenE :: "bool => unit ErrorM => unit ErrorM"
  "whenE b m == if b then m else returnE () "

syntax
  "_doE_" :: "dobinds => 'a => 'a"  ("(doE (_);//    (_)//odE)" 100)
  
translations
  "_doE_ (dobinds b bs) e" == "_doE_ b (_doE_ bs e )"
  "_doE_ (nobind b) e "    == "b >>=E (%_. e)"
  "doE x <- b; e odE"      == "b >>=E (%x. e)"
end