{-  ID:         $Id$
    Author:     Tobias C. Rittweiler, TU Muenchen

Messages.
-}

module Importer.Msg where

import List (intersperse)
import Maybe (fromMaybe)

import Importer.Utilities.Hsk (srcloc2string, module2FilePath, namesFromHsDecl)
import Importer.Utilities.Misc (prettyShow', prettyHsx)


spacify x = x ++ " "
linify  x = x ++ "\n\n"

quote :: Show a => a -> String
quote x = "`" ++ (show x) ++ "'"

printEnv env = "Global environment looked like:\n"
               ++ prettyShow' "globalenv" env

assoc_mismatch op1 assoc1 op2 assoc2
    = let { op1' = quote op1; assoc1' = quote assoc1; } in
      let { op2' = quote op2; assoc2' = quote assoc2; } in
      "Associativity mismatch: " ++ op1' ++ " has " ++ assoc1' ++ 
      ", whereas " ++ op2' ++ " has " ++ assoc2' ++ "."

missing_infix_decl name env
    = "Missing infix declaration for " ++ (quote name) ++
      ", assuming left associativity and a fixity of 9.\n\n"
      ++ printEnv env

missing_fun_sig name env
    = "Missing function signature for " ++ (quote name) ++ ". (FIXME)\n\n"
      ++ printEnv env

failed_import importloc m errormsg
    = srcloc2string importloc ++ ": "
      ++ "While trying to import " ++ quote (module2FilePath m)
      ++ ", the following error occured:\n" ++ errormsg

failed_parsing loc msg
    = srcloc2string loc ++ ": " ++ msg

cycle_in_dependency_graph moduleNs
    = "Dependency graph is not a DAG. In particular, a cycle was found between\n"
      ++ "the following modules: " ++ concatMap (spacify . quote) moduleNs

free_vars_found loc freeVariableNames
    = srcloc2string loc ++ ": " ++ "Closures disallowed. The following variables occur free: "
      ++ concatMap (spacify . quote . prettyHsx) freeVariableNames

identifier_collision_in_lookup curModule qname foundIdentifiers
    = "Ambiguous occurences found for " ++ quote qname ++ "\n"
      ++ "while trying to look it up in " ++ quote curModule ++ ":\n\n" 
      ++ concatMap (linify . prettyShow' (show qname)) foundIdentifiers

ambiguous_decl_definitions decls
    = "Ambiguous definitions between\n" ++ concatMap (linify . prettyShow' "decl") decls

duplicate_import ms
    = "Duplicate in imported modules: " ++ show ms