{-  ID:         $Id$
    Author:     Tobias C. Rittweiler, TU Muenchen
-}

module Importer.Adapt (adaptGlobalEnv, adaptIsaUnit) where

import Maybe (fromJust, fromMaybe)

import Control.Monad.State

import qualified Data.Map as Map
import Data.Generics.Biplate (transformBi)

import qualified Importer.LexEnv as Env
import Importer.ConversionUnit
import Importer.Utilities.Misc

import Importer.Mapping (AdaptionTable(..))

import qualified Importer.IsaSyntax as Isa
import Language.Haskell.Hsx

adaptGlobalEnv :: Env.GlobalE -> AdaptionTable -> Env.GlobalE
adaptGlobalEnv env tbl
    = Env.mapGlobalEnv (\n -> case adapt_whole_identifier tbl n of 
                                         Just new_id -> Just new_id
                                         Nothing     -> adapt_type_in_identifier env tbl n)
                  env


adapt_whole_identifier :: AdaptionTable -> Env.EnvName -> Maybe Env.Identifier
adapt_whole_identifier (AdaptionTable mappings) name
    = lookupBy (\n1 id2 -> n1 == Env.identifier2name id2) name mappings

adapt_type_in_identifier :: Env.GlobalE -> AdaptionTable -> Env.EnvName -> Maybe Env.Identifier
adapt_type_in_identifier globalEnv tbl n@(Env.EnvQualName mID _)
    = do let old_id       = Env.lookup_orLose mID n globalEnv
         let old_lexinfo  = Env.lexInfoOf old_id
         let old_type     = fromJust (Env.typeOf old_lexinfo)
         new_type <- transformEnvType tbl (qualifier (Env.moduleOf old_lexinfo)) old_type
         return $ Env.updateIdentifier old_id (old_lexinfo {Env.typeOf = Just new_type})
    where qualifier mID n
              = Env.identifier2name (Env.lookup_orLose mID n globalEnv) -- Kludge.

transformEnvType :: AdaptionTable -> (Env.EnvName -> Env.EnvName) -> Env.EnvType -> Maybe Env.EnvType
transformEnvType (AdaptionTable mappings) qualify typ
    = let type_renams  = filter (Env.isType . fst) mappings
          type_renams' = assert (all (Env.isType . snd) type_renams) 
                           $ map (\(t1,t2) -> (Env.identifier2name t1, Env.identifier2name t2)) 
                                 type_renams
      in case runState (transform type_renams' typ) False of
           (_, False)       -> Nothing
           (new_type, True) -> Just new_type
    where 
      transform :: [(Env.EnvName, Env.EnvName)] -> Env.EnvType -> State Bool Env.EnvType
      transform alist typ
          = let transl n =
                    case lookup (qualify n) alist of
                      Nothing -> return n
                      Just n' -> do put True; return n'
                in case typ of 
                     Env.EnvTyVar n     -> transl n >>= (return . Env.EnvTyVar)
                     Env.EnvTyCon n ts  -> do n'  <- transl n
                                              ts' <- mapM (transform alist) ts
                                              return (Env.EnvTyCon n' ts')
                     Env.EnvTyFun t1 t2 -> do t1' <- transform alist t1
                                              t2' <- transform alist t2
                                              return (Env.EnvTyFun t1' t2')
                     Env.EnvTyTuple ts  -> do ts' <- mapM (transform alist) ts
                                              return (Env.EnvTyTuple ts')

shadow :: [Isa.Name] -> (Isa.Term -> Isa.Term) -> (Isa.Term -> Isa.Term)
shadow boundNs translator  
    = \term -> if or (map (`elem` boundNs) $ extractNames term) 
               then term else translator term

makeTranslator :: Env.GlobalE -> AdaptionTable -> (Isa.Theory -> (Isa.Term -> Isa.Term))
makeTranslator globalEnv adaptionTable thy
    = \term -> case term of
                 Isa.Var n 
                     | Just id    <- Env.lookup (Env.fromIsa thy) (Env.fromIsa n) globalEnv,
                       Just newId <- adapt_whole_identifier adaptionTable (Env.identifier2name id)
                     -> Isa.Var $ Env.toIsa (Env.identifier2name newId)
                 etc -> etc


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

