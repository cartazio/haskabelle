
module Importer.Adapt (convertAndAdapt_GlobalEnv, adaptIsaUnit) where

import List (lookup, concatMap)
import Maybe (fromJust, fromMaybe)

import qualified Data.Map as Map

import Importer.LexEnv
import Importer.ConversionUnit
import Importer.Utilities.Misc (wordsBy, assert)
import Importer.Utilities.Hsk (string2HsName)

import Importer.Mapping (AdaptionTable(..))
import Importer.Convert.Trivia (convert_trivia)

import qualified Importer.IsaSyntax as Isa
import Language.Haskell.Hsx

-- adaptionTable = [(UnQual (HsIdent "append"), UnQual (HsSymbol "@"))]



-- adaptHskUnit :: ConversionUnit -> ConversionUnit
-- adaptHskUnit (HskUnit hsmods) = HskUnit (map adapt hsmods)

-- adapt :: HsModule -> HsModule
-- adapt (HsModule loc modul exports imports decls)
--     = HsModule loc modul exports imports (map (renameFreeVars adaptionTable) decls)

convertAndAdapt_GlobalEnv :: GlobalE -> AdaptionTable -> GlobalE
convertAndAdapt_GlobalEnv (HskGlobalEnv globalmap) (AdaptionTable adaptionTable)
    = IsaGlobalEnv 
        $ Map.map convertModuleEnv (Map.mapKeys convert_trivia globalmap) 
    where 
          convertModuleEnv :: ModuleE -> ModuleE
          convertModuleEnv (HskModuleEnv m _ _ lexenv)
              = IsaTheoryEnv (convert_trivia m) (convertLexEnv lexenv)

          convertLexEnv :: LexE -> LexE
          convertLexEnv (HskLexEnv lexmap)
              = IsaLexEnv 
                  $ let lexmap' = Map.map (\id -> fromMaybe (convertHskIdentifier id) 
                                                            (maybeAdaptIdentifier id)) 
                                          lexmap
                    in Map.mapKeys (\name -> isaIdentifier2name (fromJust $ Map.lookup name lexmap')) 
                                   lexmap'
                                    

          maybeAdaptIdentifier :: HskIdentifier -> Maybe IsaIdentifier
          maybeAdaptIdentifier hskidentifier 
              = case List.lookup (identifier $ extractLexInfo hskidentifier) adaptionTable' of
                  Just (hskId, isaId) -> assert (hskId == hskidentifier) $ Just isaId
                  Nothing -> Nothing
              where adaptionTable' 
                        = map (\(hskId, isaId) 
                                   -> (identifier $ extractLexInfo hskId, (hskId, isaId))) 
                              adaptionTable

convertHskLexInfo :: HskLexInfo -> IsaLexInfo
convertHskLexInfo (HskLexInfo { identifier = i, typeOf = t, moduleOf = m })
    = IsaLexInfo { _identifier = convert_trivia i,
                   _typeOf     = convert_trivia (fromJust t),
                   _theoryOf   = convert_trivia m }

convertHskIdentifier :: HskIdentifier -> IsaIdentifier
convertHskIdentifier (HskVariable lexinfo)     = IsaVariable (convertHskLexInfo lexinfo)
convertHskIdentifier (HskFunction lexinfo)     = IsaFunction (convertHskLexInfo lexinfo)
convertHskIdentifier (HskInfixOp  lexinfo a p) 
    = IsaInfixOp  (convertHskLexInfo lexinfo) (convert_trivia a) p


shadow :: [Isa.Name] -> (Isa.Term -> Isa.Term) -> (Isa.Term -> Isa.Term)
shadow boundNs translator  
    = \term -> if or (map (`elem` boundNs) $ extractNames term) 
               then term else translator term


makeTranslator :: GlobalE -> AdaptionTable -> (Isa.Theory -> (Isa.Term -> Isa.Term))
makeTranslator globalEnv@(HskGlobalEnv _) (AdaptionTable adaptionTable) thy
    = \term -> case term of
                     Isa.Var n -> case lookupName thy n of
                                    Just id@(IsaVariable _)    -> Isa.Var $ isaIdentifier2name id
                                    Just id@(IsaFunction _)    -> Isa.Var $ isaIdentifier2name id
                                    Just id@(IsaInfixOp i _ _) -> Isa.Var $ isaIdentifier2name id
                                    _ -> Isa.Var n
                     etc   -> etc
      where lookupName :: Isa.Theory -> Isa.Name -> Maybe IsaIdentifier
            lookupName (Isa.Theory thyN) name
                = case Importer.LexEnv.lookup (Module thyN) (toHsQName name) globalEnv of
                    Just hskidentifier -> List.lookup hskidentifier adaptionTable
                    Nothing            -> Nothing

            toHsQName :: Isa.Name -> HsQName
            toHsQName (Isa.QName (Isa.Theory thyN) n) = Qual (Module thyN) (string2HsName n)
            toHsQName (Isa.Name n)                    = UnQual (string2HsName n)

adaptIsaUnit :: GlobalE -> AdaptionTable -> ConversionUnit -> ConversionUnit
adaptIsaUnit globalEnv adaptionTable (IsaUnit thycmds isaGlobalEnv)
    = let translator = makeTranslator globalEnv adaptionTable
      in (flip IsaUnit isaGlobalEnv) 
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