
module Importer.Adapt (adaptGlobalEnv, adaptIsaUnit) where

-- import List (lookupBy, concatMap)
-- import Maybe (fromJust, fromMaybe)

import qualified Data.Map as Map

import qualified Importer.LexEnv as Env
import Importer.ConversionUnit
import Importer.Utilities.Misc (lookupBy, wordsBy, assert)
-- import Importer.Utilities.Hsk (string2HsName)

import Importer.Mapping (AdaptionTable(..))

import qualified Importer.IsaSyntax as Isa
import Language.Haskell.Hsx

adaptGlobalEnv :: Env.GlobalE -> AdaptionTable -> Env.GlobalE
adaptGlobalEnv globalEnv (AdaptionTable mappings)
    = Env.mapGlobalEnv maybeAdaptIdentifier globalEnv
    where maybeAdaptIdentifier :: Env.Identifier -> Maybe Env.Identifier
          maybeAdaptIdentifier identifier 
              = lookupBy check identifier mappings
              where check id1 id2
                        -- We make sure that the identifier that shall be adapted,
                        -- hasn't changed in the GlobalE.
                        = let n1 = Env.identifier2name id1 
                              n2 = Env.identifier2name id2
                          in if n1 == n2 then assert (id1 == identifier) True
                                         else False

shadow :: [Isa.Name] -> (Isa.Term -> Isa.Term) -> (Isa.Term -> Isa.Term)
shadow boundNs translator  
    = \term -> if or (map (`elem` boundNs) $ extractNames term) 
               then term else translator term


makeTranslator :: Env.GlobalE -> AdaptionTable -> (Isa.Theory -> (Isa.Term -> Isa.Term))
makeTranslator globalEnv (AdaptionTable adaptionTable) thy
    = \term -> case term of
                     Isa.Var n -> case Env.lookup (Env.fromIsa thy) (Env.fromIsa n) globalEnv of
                                    Just id@(Env.Variable _)    -> Isa.Var $ Env.toIsa (Env.identifier2name id)
                                    Just id@(Env.Function _)    -> Isa.Var $ Env.toIsa (Env.identifier2name id)
                                    Just id@(Env.InfixOp _ _ _) -> Isa.Var $ Env.toIsa (Env.identifier2name id)
                                    _ -> Isa.Var n
                     etc   -> etc

adaptIsaUnit :: Env.GlobalE -> AdaptionTable -> ConversionUnit -> ConversionUnit
adaptIsaUnit globalEnv adaptionTable (IsaUnit thycmds adaptedGlobalEnv)
    = let translator = makeTranslator adaptedGlobalEnv adaptionTable
      in (flip IsaUnit adaptedGlobalEnv) 
          $ map (\(Isa.TheoryCmd thy cmds) 
                     -> Isa.TheoryCmd thy (map (adapt (translator thy)) cmds))
                thycmds
         

class Adapt a where
    adapt  :: (Isa.Term -> Isa.Term) -> a -> a

instance Adapt Isa.Cmd where
    adapt translator (Isa.Block cmds)           = Isa.Block $ map (adapt translator) cmds
    adapt translator (Isa.TheoryCmd thy cmds)   = Isa.TheoryCmd thy $ map (adapt translator) cmds
    adapt translator c@(Isa.DatatypeCmd _ _)    = c
    adapt translator c@(Isa.RecordCmd _ _)      = c
    adapt translator c@(Isa.TypesCmd _)         = c
    adapt translator c@(Isa.InfixDeclCmd _ _ _) = c
    adapt translator c@(Isa.Comment _)          = c
    adapt translator (Isa.FunCmd funNs types defs)
        = Isa.FunCmd funNs types
            $ map (\(funN, pats, body)
                       -> assert (funN `elem` funNs)
                            $ let boundNs = funNs ++ concatMap extractNames pats
                              in (funN, pats, adapt (shadow boundNs translator) body))
                  defs
    adapt translator (Isa.DefinitionCmd name typ (pat, term))
        = Isa.DefinitionCmd name typ (pat, adapt (shadow (extractNames pat) translator) term)

instance Adapt Isa.Term where
    adapt translator (Isa.Literal lit)     = Isa.Literal lit
    adapt translator t@(Isa.Var _)         = translator t
    adapt translator t@(Isa.RecConstr _ _) = translator t
    adapt translator t@(Isa.RecUpdate _ _) = translator t
    adapt translator (Isa.App t1 t2)       = Isa.App (adapt translator t1) (adapt translator t2)
    adapt translator (Isa.Parenthesized t) = Isa.Parenthesized (adapt translator t)

    adapt translator (Isa.Lambda boundNs body)
        = Isa.Lambda boundNs $ adapt (shadow boundNs translator) body

    adapt translator (Isa.If c t e)    = Isa.If c' t' e'
        where c' = adapt translator c
              t' = adapt translator t
              e' = adapt translator e

    adapt translator (Isa.Let bindings body)
        = let boundNs = concatMap (extractNames . fst) bindings
          in Isa.Let (map (\(pat, term) -> (pat, adapt translator term)) bindings)
                 (adapt (shadow boundNs translator) body)

    adapt translator (Isa.Case term patterns)
        = Isa.Case (adapt translator term)
            $ map (\(pat, body) -> (pat, adapt (shadow (extractNames pat) translator) body))
                  patterns

extractNames :: Isa.Term -> [Isa.Name]
extractNames (Isa.Var n)                   = [n]
extractNames (Isa.App t1 t2)               = extractNames t1 ++ extractNames t2
extractNames (Isa.RecConstr name patterns) = [name] ++ map fst patterns
extractNames etc = []

