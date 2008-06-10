{-  ID:         $Id$
    Author:     Tobias C. Rittweiler, TU Muenchen
-}

module Importer.Adapt (adaptGlobalEnv, adaptIsaUnit) where

import Maybe (fromJust, fromMaybe, isJust)
import List (partition)

import Control.Monad.State
import qualified Data.Map as Map
import Data.Generics.Biplate (transformBi)

import qualified Importer.LexEnv as Env
import Importer.ConversionUnit
import Importer.Utilities.Misc

import Importer.Mapping (AdaptionTable(..))

import qualified Importer.IsaSyntax as Isa
import Language.Haskell.Hsx


data AdptState = AdptState { oldGlobalEnv     :: Env.GlobalE,
                             adaptedGlobalEnv :: Env.GlobalE,
                             adaptionTable    :: AdaptionTable,
                             currentModuleID  :: Maybe Env.ModuleID
                           }

type AdaptM v = State AdptState v

query :: (AdptState -> x) -> AdaptM x
query slot = do s <- get; return (slot s)

set :: (AdptState -> AdptState) -> AdaptM ()
set update = do s <- get; put (update s); return ()

shadow :: [Env.EnvName] -> AdaptM ()
shadow names
    = set (\state 
               -> let (AdaptionTable mappings) = adaptionTable state 
                      -- Functions (especially data constructors, like []) can't
                      -- be locally bound, so we must not shadow them.
                      (fun_mappings, rest_mappings)
                          = partition (\(id,_) -> Env.isInfixOp id || Env.isFunction id ) 
                              mappings
                  in state { adaptionTable 
                                 = AdaptionTable $ 
                                     fun_mappings ++
                                     filter ((`notElem` names) . Env.identifier2name . fst) 
                                        rest_mappings
                           })
   
-- shadowing [a, b, c] $ body
--   with appropriate a, b, c.      
--
-- Inside `body', do not adapt names `a', `b', and `c'.
--
shadowing :: [Isa.Name] -> AdaptM v -> AdaptM v
shadowing names body
    = do old_tbl <- query adaptionTable
         shadow (map Env.fromIsa names)
         r <- body
         set (\state -> state { adaptionTable = old_tbl })
         return r

-- nested_binding [(a, computeA), (b, computeB), (c, computeC)] $
--  \([a', b', c']) -> body
--
--     with appropriate a, b, c 
-- and with a', b', c' being the results of computeA, computeB, computeC.
--
-- LET like binding construct: while computing `computeB', `a' is shadowed,
-- while computing `computeC', `a' and `b' are shadowed, and so on.
--
-- Inside `body', the identifiers `a', `b' and `c' won't be adapted..
-- 
nested_binding :: [([Isa.Name], AdaptM b)] -> ([b] -> AdaptM v) -> AdaptM v
nested_binding [] continuation = continuation []
nested_binding bindings continuation
    = do old_tbl <- query adaptionTable
         rs      <- foldM (\result (ns,thunk) -> let ns' = map Env.fromIsa ns in
                                                 do shadow ns' ; t <- thunk
                                                    return (result ++ [t])) 
                    [] bindings
         r       <- continuation rs
         set (\state -> state { adaptionTable = old_tbl })
         return r
                         

runAdaption :: Env.GlobalE -> Env.GlobalE -> AdaptionTable -> AdaptM v -> v
runAdaption oldEnv newEnv tbl state 
    = evalState state (AdptState { oldGlobalEnv     = oldEnv,
                                   adaptedGlobalEnv = newEnv,
                                   adaptionTable    = tbl,
                                   currentModuleID  = Nothing 
                                 })

adaptGlobalEnv :: Env.GlobalE -> AdaptionTable -> Env.GlobalE
adaptGlobalEnv env tbl
    = let r = Env.updateGlobalEnv 
               (\n -> case translateName tbl n of 
                        Just new_id -> Just new_id
                        Nothing     -> adapt_type_in_identifier env tbl n)
               env
      in r -- trace (prettyShow' "adaptionTable" tbl) r

translateName :: AdaptionTable -> Env.EnvName -> Maybe Env.Identifier
translateName (AdaptionTable mappings) name
    = lookupBy (\n1 id2 -> n1 == Env.identifier2name id2) name mappings

translateIdentifier :: AdaptionTable -> Env.Identifier -> Env.Identifier
translateIdentifier tbl id
    = case translateName tbl (Env.identifier2name id) of
        Nothing     -> id
        Just new_id -> new_id

adapt_type_in_identifier :: Env.GlobalE -> AdaptionTable -> Env.EnvName -> Maybe Env.Identifier
adapt_type_in_identifier globalEnv tbl n@(Env.EnvQualName mID _)
    = do let old_id       = Env.lookup_orLose mID n globalEnv
         let old_lexinfo  = Env.lexInfoOf old_id
         let old_type     = Env.typeOf old_lexinfo
         new_type <- translateEnvType tbl (qualifier (Env.moduleOf old_lexinfo)) old_type
         return $ Env.updateIdentifier old_id (old_lexinfo {Env.typeOf = new_type})
    where qualifier mID n
              = case Env.lookup mID n globalEnv of
                  Nothing -> Env.qualifyEnvName mID n
                  Just id -> Env.identifier2name id 

translateEnvType :: AdaptionTable -> (Env.EnvName -> Env.EnvName) -> Env.EnvType -> Maybe Env.EnvType
translateEnvType (AdaptionTable mappings) qualify typ
    = let type_renams  = filter (Env.isType . fst) mappings
          type_renams' = assert (all (Env.isType . snd) type_renams) 
                           $ map (\(t1,t2) -> (Env.identifier2name t1, Env.identifier2name t2)) 
                                 type_renams
      in case runState (translate type_renams' typ) False of
           (_, False)       -> Nothing        -- no match found in AdaptionTable. 
           (new_type, True) -> Just new_type
    where 
      translate :: [(Env.EnvName, Env.EnvName)] -> Env.EnvType -> State Bool Env.EnvType
      translate alist typ
          = let transl n = case lookup (qualify n) alist of
                             Nothing -> return n
                             Just n' -> do put True; return n'
                in case typ of 
                     Env.EnvTyNone      -> return Env.EnvTyNone
                     Env.EnvTyVar n     -> transl n >>= (return . Env.EnvTyVar)
                     Env.EnvTyCon n ts  -> do n'  <- transl n
                                              ts' <- mapM (translate alist) ts
                                              return (Env.EnvTyCon n' ts')
                     Env.EnvTyFun t1 t2 -> do t1' <- translate alist t1
                                              t2' <- translate alist t2
                                              return (Env.EnvTyFun t1' t2')
                     Env.EnvTyTuple ts  -> do ts' <- mapM (translate alist) ts
                                              return (Env.EnvTyTuple ts')

adaptEnvName :: Env.EnvName -> AdaptM Env.EnvName
adaptEnvName n 
    = do Just mID <- query currentModuleID
         tbl      <- query adaptionTable
         oldEnv   <- query oldGlobalEnv
         newEnv   <- query adaptedGlobalEnv
         case Env.lookup mID n oldEnv of
           Nothing -> return n
           Just id -> let new_id       = translateIdentifier tbl id
                          new_id_name  = Env.identifier2name new_id
                      in assert (isJust (Env.lookup mID new_id_name newEnv))
                           $ return new_id_name

adaptEnvType :: Env.EnvType -> AdaptM Env.EnvType
adaptEnvType t
    = do Just mID <- query currentModuleID
         tbl      <- query adaptionTable
         oldEnv   <- query oldGlobalEnv
         let qualify n
              = case Env.lookup mID n oldEnv of
                  Nothing -> Env.qualifyEnvName mID n
                  Just id -> Env.identifier2name id 
         return (fromMaybe t (translateEnvType tbl qualify t))

adaptName :: Isa.Name -> AdaptM Isa.Name
adaptName n = do n' <- adaptEnvName (Env.fromIsa n); return (Env.toIsa n')

adaptType :: Isa.Type -> AdaptM Isa.Type
adaptType t = do t' <- adaptEnvType (Env.fromIsa t); return (Env.toIsa t')


adaptIsaUnit :: Env.GlobalE -> AdaptionTable -> ConversionUnit -> ConversionUnit
adaptIsaUnit globalEnv adaptionTable (IsaUnit thycmds adaptedGlobalEnv)
    = let run thunk = runAdaption globalEnv adaptedGlobalEnv adaptionTable thunk
          thycmds'  = run (mapM adapt thycmds)
      in IsaUnit thycmds' adaptedGlobalEnv


not_implemented x = error ("Adaption not implemented yet for\n  " ++ prettyShow' "thing" x) 

class Adapt a where
    adapt  :: a -> AdaptM a

instance Adapt Isa.Cmd where
    adapt (Isa.Block cmds)       
        = mapM adapt cmds >>= (return . Isa.Block)

    adapt (Isa.TheoryCmd thy cmds)   
        = do old_mID <- query currentModuleID
             set (setModuleID $ Just (Env.fromIsa thy))
             cmds'   <- mapM adapt cmds
             set (setModuleID old_mID)
             return (Isa.TheoryCmd thy cmds')
        where setModuleID v state
                  = state { currentModuleID = v }

    adapt c@(Isa.RecordCmd _ _)      = not_implemented c
    adapt c@(Isa.TypesCmd _)         = not_implemented c
    adapt c@(Isa.InfixDeclCmd _ _ _) = not_implemented c
    adapt c@(Isa.Comment _)          = return c

    adapt (Isa.DatatypeCmd sig@(Isa.TypeSpec tyvarNs tycoN) constrs)    
        = shadowing (tycoN:tyvarNs) $
            do constrs' <- mapM adpt constrs
               return (Isa.DatatypeCmd sig constrs')
        where adpt (Isa.Constructor name types)
                  = do types' <- mapM adaptType types
                       return (Isa.Constructor name types')
                           
    adapt (Isa.FunCmd funNs typesigs defs)
        = do typesigs' <- mapM adapt typesigs
             shadowing funNs $
               do defs' <- mapM (\(funN, pats, body)
                                     -> assert (funN `elem` funNs) $
                                        do pats' <- mapM adapt pats
                                           shadowing (concatMap extractNames pats') $
                                             do body' <- adapt body ; return (funN, pats', body'))
                                defs
                  return (Isa.FunCmd funNs typesigs' defs')

    adapt (Isa.DefinitionCmd name typesig (pat, term))
        = do typesig' <- adapt typesig
             shadowing (extractNames pat) $
               do term' <- adapt term ; return (Isa.DefinitionCmd name typesig' (pat, term'))

instance Adapt Isa.TypeSpec where
    adapt (Isa.TypeSpec tyvarNs tycoN)
        = do (Isa.TyCon tycoN' tyvars') <- adaptType (Isa.TyCon tycoN (map Isa.TyVar tyvarNs))
             return $ Isa.TypeSpec (map (\(Isa.TyVar n) -> n) tyvars') tycoN'

instance Adapt Isa.TypeSig where
    adapt (Isa.TypeSig n t)
        = do t' <- adaptType t ; return (Isa.TypeSig n t')

instance Adapt Isa.Term where
    adapt (Isa.Literal lit)     = return (Isa.Literal lit)
    adapt (Isa.Var n)           = adaptName n >>= (return . Isa.Var)
    adapt (Isa.Parenthesized t) = adapt t     >>= (return . Isa.Parenthesized)
    adapt t@(Isa.RecConstr _ _) = not_implemented t
    adapt t@(Isa.RecUpdate _ _) = not_implemented t

    adapt (Isa.App t1 t2)       = do t1' <- adapt t1 ; t2' <- adapt t2
                                     return (Isa.App t1' t2')

    adapt (Isa.If c t e)        = do c' <- adapt c ; t' <- adapt t ; e' <- adapt e
                                     return (Isa.If c' t' e')

    adapt (Isa.Lambda boundNs body)
        = shadowing boundNs $
            adapt body >>= (return . Isa.Lambda boundNs)

    adapt (Isa.Let bindings body)
        = nested_binding (map (\(p,t) -> (extractNames p, adapt t)) bindings) $
            \terms' -> do body' <- adapt body
                          let pats = map fst bindings
                          return (Isa.Let (zip pats terms') body')

    adapt (Isa.Case term patterns)
        = do term'     <- adapt term
             patterns' <- mapM (\(pat, body) 
                                    -> do pat' <- adapt pat
                                          shadowing (extractNames pat') $
                                            do body' <- adapt body
                                               return (pat', body'))
                               patterns
             return (Isa.Case term' patterns')

extractNames :: Isa.Term -> [Isa.Name]
extractNames (Isa.Var n)                   = [n]
extractNames (Isa.App t1 t2)               = extractNames t1 ++ extractNames t2
extractNames (Isa.RecConstr name patterns) = [name] ++ map fst patterns
extractNames etc = []

