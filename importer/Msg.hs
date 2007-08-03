
module Importer.Msg where

quote :: Show a => a -> String
quote x = "`" ++ (show x) ++ "'"

assoc_mismatch op1 assoc1 op2 assoc2
    = let { op1' = quote op1; assoc1' = quote assoc1; } in
      let { op2' = quote op2; assoc2' = quote assoc2; } in
      "Associativity mismatch: " ++ op1' ++ " has " ++ assoc1' ++ 
      ", whereas " ++ op2' ++ " has " ++ assoc2' ++ "."

missing_infix_decl name
    = "Missing infix declaration for " ++ (quote name) ++
      ", assuming left associativity and a fixity of 9."

missing_fun_sig name
    = "Missing function signature for " ++ (quote name) ++ ". (FIXME)"